/*
 * Copyright (C) 1996-2026 The Squid Software Foundation and contributors
 *
 * Squid software is distributed under GPLv2+ license and includes
 * contributions from numerous individuals and organizations.
 * Please see the COPYING and CONTRIBUTORS files for details.
 */

/* DEBUG: section 28    Access Control */

#include "squid.h"
#include "acl/Checklist.h"
#include "acl/DomainData.h"
#include "acl/SplayInserter.h"
#include "anyp/Uri.h"
#include "base/Assure.h"
#include "cache_cf.h"
#include "ConfigParser.h"
#include "debug/Stream.h"
#include "util.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <new>
#include <vector>
#if HAVE_SYS_MMAN_H
#include <sys/mman.h>
#endif

template<class T>
inline void
xRefFree(T &thing)
{
    xfree (thing);
}

ACLDomainData::~ACLDomainData()
{
    domains.destroy(xRefFree);
}

template<class T>
inline int
splaystrcasecmp (T&l, T&r)
{
    return strcasecmp ((char *)l,(char *)r);
}

template<class T>
inline int
splaystrcmp (T&l, T&r)
{
    return strcmp ((char *)l,(char *)r);
}

/* general compare functions, these are used for tree search algorithms
 * so they return <0, 0 or >0 */

/* compare a host and a domain */

static int
aclHostDomainCompare( char *const &a, char * const &b)
{
    const char *h = static_cast<const char *>(a);
    const char *d = static_cast<const char *>(b);
    return matchDomainName(h, d);
}

bool
ACLDomainData::match(char const *host)
{
    if (!host)
        return false;

    debugs(28, 3, "aclMatchDomainList: checking '" << host << "'");

    char *h = const_cast<char *>(host);
    const auto result = domains.find(h, aclHostDomainCompare);

    debugs(28, 3, "aclMatchDomainList: '" << host << "' " << (result ? "found" : "NOT found"));

    return (result != nullptr);
}

struct AclDomainDataDumpVisitor {
    SBufList contents;
    void operator() (char * const & node_data) {
        contents.push_back(SBuf(node_data));
    }
};

SBufList
ACLDomainData::dump() const
{
    AclDomainDataDumpVisitor visitor;
    domains.visit(visitor);
    return visitor.contents;
}

template <>
int
Acl::SplayInserter<char*>::Compare(const Value &a, const Value &b)
{
    // If X represents a set of matching domain names (e.g., .example.com), then
    // matchDomainName(X, Y) uses a single domain name from X by removing the
    // leading dot (e.g., example.com). We call that name "the root of X". If X
    // is a single domain name, then its root is X itself. Since domain sets
    // cannot have _partial_ overlaps (unlike IP or integer ranges), testing
    // roots is enough to detect duplicates and establish correct set order.

    if (matchDomainName(b, a)) {
        // Set A does not contain B's root. If set B contains A's root, then the
        // call below will return 0, signaling duplicates. Otherwise, A and B
        // have no common values, and the call below will correctly order the
        // two sets, mimicking the order used by the Splay comparison function
        // in match().
        return matchDomainName(a, b);
    } else {
        // Signal duplicates because set A contains B's root (at least).
        return 0;
    }
}

template <>
bool
Acl::SplayInserter<char*>::IsSubset(const Value &a, const Value &b)
{
    // A value that starts with a dot matches a set of the corresponding domain
    // names. Other values are individual domain names that match themselves.
    // \sa matchDomainName()

    if (*a == '.' && *b == '.') {
        // A and B are overlapping sets. More characters imply a smaller set.
        return strlen(a) >= strlen(b);
    }

    if (*a != '.' && *b != '.') {
        // A and B are identical individual domain names
        return true;
    }

    // Either A or B is a set. The other one is a domain name inside that set.
    // That domain name may use fewer or more characters (e.g., both example.com
    // and x.example.com domains belong to the same .example.com set), so we
    // cannot use a strlen()-based test here.
    return *b == '.';
}

template <>
Acl::SplayInserter<char*>::Value
Acl::SplayInserter<char*>::MakeCombinedValue(const Value &, const Value &)
{
    Assure(!"domain name sets cannot partially overlap");
    return nullptr; // unreachable code
}

template <>
void
Acl::SplayInserter<char*>::DestroyValue(Value v)
{
    xfree(v);
}

namespace {

/// A std::allocator replacement for large, short-lived parsing buffers. Where
/// possible, gets memory directly from the OS so that deallocation returns it
/// to the OS. A malloc(3) heap may keep such memory resident after parsing,
/// growing every Squid process by the size of the largest domain ACL.
template <class T>
class ScratchAllocator
{
public:
    using value_type = T;

    ScratchAllocator() = default;
    template <class U> ScratchAllocator(const ScratchAllocator<U> &) {}

    T *allocate(const size_t n) {
#if HAVE_SYS_MMAN_H && defined(MAP_ANONYMOUS)
        const auto p = mmap(nullptr, n * sizeof(T), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (p == MAP_FAILED)
            throw std::bad_alloc();
        return static_cast<T *>(p);
#else
        return std::allocator<T>().allocate(n);
#endif
    }

    void deallocate(T * const p, const size_t n) {
#if HAVE_SYS_MMAN_H && defined(MAP_ANONYMOUS)
        munmap(p, n * sizeof(T));
#else
        std::allocator<T>().deallocate(p, n);
#endif
    }

    template <class U> bool operator ==(const ScratchAllocator<U> &) const { return true; }
    template <class U> bool operator !=(const ScratchAllocator<U> &) const { return false; }
};

template <class T>
using ScratchVector = std::vector<T, ScratchAllocator<T> >;

/// A parsed domain ACL value prepared for bulk loading by DomainBulkLoader.
class BulkDomain
{
public:
    char *value = nullptr; ///< the lowercased ACL value
    /// The first KeyPrefixLength sorting key bytes, as a big-endian number
    /// padded with zeros. Comparing these numbers orders most values without
    /// reaching into DomainBulkLoader::keys, speeding up sorting several times.
    uint64_t keyPrefix = 0;
    size_t keyOffset = 0; ///< where our sorting key starts in DomainBulkLoader::keys
    size_t keyLength = 0; ///< the number of bytes in our sorting key
    size_t position = 0; ///< configuration order (for "earlier" in warnings)
    bool isSet = false; ///< whether the value starts with a dot (i.e. covers subdomains)
};

/// Builds a domain Splay tree from many values at once: Sorts values using keys
/// that order them the way matchDomainName() does, drops values covered by
/// other values, and builds a balanced tree from the remaining sorted values.
/// Inserting large domain lists one value at a time costs O(log n) splaying
/// matchDomainName() calls per value and dominates reconfiguration time.
class DomainBulkLoader
{
public:
    /// remembers a lowercased ACL value (in configuration order)
    void add(char *value);

    /// Whether loadInto() orders and deduplicates added values exactly like
    /// Acl::SplayInserter::Merge() does. Values like "." or "..example.com"
    /// make matchDomainName() an inconsistent comparison function, so Merge()
    /// results for lists with them depend on value order.
    bool canLoad() const { return allSupported; }

    /// moves added values into the given empty tree
    /// \prec canLoad()
    void loadInto(Splay<char *> &);

    /// added values, in configuration order, starting with the given position
    std::vector<char *> valuesFrom(size_t position) const;

private:
    static bool Supported(const char *value);
    static void ReportIgnored(const BulkDomain &ignored, const BulkDomain &kept);

    const char *keyOf(const BulkDomain &d) const { return keys.data() + d.keyOffset; }
    bool sameKey(const BulkDomain &, const BulkDomain &) const;
    bool covers(const BulkDomain &set, const BulkDomain &) const;
    bool less(const BulkDomain &, const BulkDomain &) const;

    ScratchVector<BulkDomain> domains;

    /// Sorting keys of all domains, back to back. A key is the value without
    /// its leading dot, reversed, with dots replaced by KeyDot. Byte-wise key
    /// comparison then orders values just like matchDomainName() compares
    /// their characters: from the end, treating dots as smaller than other
    /// characters, and treating the value that runs out first as smaller.
    ScratchVector<char> keys;

    /// whether all added values are Supported()
    bool allSupported = true;
};

/// replaces '.' in sorting keys; sorts before all Supported() value bytes
const char KeyDot = '\x01';

/// the number of sorting key bytes in BulkDomain::keyPrefix
const size_t KeyPrefixLength = sizeof(BulkDomain::keyPrefix);

/// Accepts plain domain names and single-dot sets of them that consist of
/// bytes ordered the same way by xtolower() and keys.
bool
DomainBulkLoader::Supported(const char *value)
{
    if (*value == '.')
        ++value;
    if (!*value || *value == '.')
        return false;
    for (auto p = value; *p; ++p) {
        const auto c = static_cast<unsigned char>(*p);
        if (c <= ' ' || c >= 0x7F || (c >= 'A' && c <= 'Z'))
            return false;
    }
    return true;
}

void
DomainBulkLoader::add(char * const value)
{
    allSupported = allSupported && Supported(value);

    BulkDomain d;
    d.value = value;
    d.isSet = (*value == '.');
    d.position = domains.size();
    d.keyOffset = keys.size();
    const auto root = value + (d.isSet ? 1 : 0);
    d.keyLength = strlen(root);
    keys.resize(d.keyOffset + d.keyLength);
    auto key = keys.data() + d.keyOffset;
    for (auto p = root + d.keyLength; p > root;) {
        const auto c = *--p;
        *key++ = (c == '.' ? KeyDot : c);
    }
    // Keys have no zero bytes, so zero padding orders a shorter key before
    // the longer keys that it is a prefix of, just like memcmp() below does.
    for (size_t i = 0; i < KeyPrefixLength; ++i)
        d.keyPrefix = (d.keyPrefix << 8) | (i < d.keyLength ? static_cast<unsigned char>(keyOf(d)[i]) : 0);
    domains.push_back(d);
}

std::vector<char *>
DomainBulkLoader::valuesFrom(const size_t position) const
{
    std::vector<char *> values;
    for (auto i = position; i < domains.size(); ++i)
        values.push_back(domains[i].value);
    return values;
}

bool
DomainBulkLoader::sameKey(const BulkDomain &a, const BulkDomain &b) const
{
    return a.keyPrefix == b.keyPrefix && a.keyLength == b.keyLength &&
           memcmp(keyOf(a), keyOf(b), a.keyLength) == 0;
}

/// whether the given set matches all names matched by the given value
bool
DomainBulkLoader::covers(const BulkDomain &set, const BulkDomain &d) const
{
    if (!set.isSet)
        return false;
    if (sameKey(set, d))
        return true; // .example.com covers .example.com and example.com
    // .example.com covers sub.example.com and .sub.example.com
    return d.keyLength > set.keyLength &&
           memcmp(keyOf(set), keyOf(d), set.keyLength) == 0 &&
           keyOf(d)[set.keyLength] == KeyDot;
}

/// Orders by keys. Among values with the same key, puts a set before the name
/// it covers and an earlier duplicate before the later one.
bool
DomainBulkLoader::less(const BulkDomain &a, const BulkDomain &b) const
{
    if (a.keyPrefix != b.keyPrefix)
        return a.keyPrefix < b.keyPrefix;
    const auto commonLength = std::min(a.keyLength, b.keyLength);
    if (commonLength > KeyPrefixLength) {
        const auto skip = KeyPrefixLength; // these key bytes are equal
        if (const auto diff = memcmp(keyOf(a) + skip, keyOf(b) + skip, commonLength - skip))
            return diff < 0;
    }
    if (a.keyLength != b.keyLength)
        return a.keyLength < b.keyLength;
    if (a.isSet != b.isSet)
        return a.isSet;
    return a.position < b.position;
}

/// reports a dropped value using Acl::SplayInserter::Merge() wording
void
DomainBulkLoader::ReportIgnored(const BulkDomain &ignored, const BulkDomain &kept)
{
    if (ignored.position > kept.position) {
        debugs(28, DBG_PARSE_NOTE(DBG_IMPORTANT), "WARNING: Ignoring " << ignored.value << " because it is already covered by " << kept.value <<
               Debug::Extra << "advice: Remove value " << ignored.value << " from the ACL");
    } else {
        debugs(28, DBG_PARSE_NOTE(DBG_IMPORTANT), "WARNING: Ignoring earlier " << ignored.value << " because it is covered by " << kept.value <<
               Debug::Extra << "advice: Remove value " << ignored.value << " from the ACL");
    }
}

void
DomainBulkLoader::loadInto(Splay<char *> &tree)
{
    Assure(allSupported);

    std::sort(domains.begin(), domains.end(), [this](const BulkDomain &a, const BulkDomain &b) {
        return less(a, b);
    });

    // In key order, every value covered by a set immediately follows that set
    // (or another value covered by that set), and duplicates are adjacent.
    ScratchVector<char *> kept;
    kept.reserve(domains.size());
    const BulkDomain *lastKept = nullptr;
    const BulkDomain *lastSet = nullptr;
    for (const auto &d: domains) {
        const BulkDomain *coveringValue = nullptr;
        if (lastSet && covers(*lastSet, d))
            coveringValue = lastSet;
        else if (lastKept && sameKey(*lastKept, d))
            coveringValue = lastKept;

        if (coveringValue) {
            ReportIgnored(d, *coveringValue);
            xfree(d.value);
            continue;
        }

        kept.push_back(d.value);
        lastKept = &d;
        if (d.isSet)
            lastSet = &d;
    }
    ScratchVector<BulkDomain>().swap(domains);
    ScratchVector<char>().swap(keys);

    tree.assignSorted(kept);
}

} // namespace

void
ACLDomainData::parse()
{
    DomainBulkLoader loader;

    // values loaded by earlier "acl" lines with this ACL name
    size_t earlierValues = 0;
    auto collector = [&](char * const &value) {
        loader.add(value);
        ++earlierValues;
    };
    domains.visit(collector);

    while (char *t = ConfigParser::strtokFile()) {
        Tolower(t);
        loader.add(xstrdup(t));
    }

    if (!loader.canLoad()) {
        // preserve Merge() results that may depend on value order
        for (auto value: loader.valuesFrom(earlierValues))
            Acl::SplayInserter<char*>::Merge(domains, std::move(value));
        return;
    }

    domains.destroy([](char *&) {}); // the loader now owns earlier values
    loader.loadInto(domains);
}

bool
ACLDomainData::empty() const
{
    return domains.empty();
}

