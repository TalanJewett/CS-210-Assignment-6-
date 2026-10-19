// main.cpp - CS 210 Assignment 06: Passwords and Hash Tables
// Author: Talan Jewett
//
// Build:  g++ -std=c++17 -O2 -Wall -Wextra main.cpp -o a06
// Run:    ./a06          authentication demo (default)
//         ./a06 test     unit / edge-case / randomized tests on all strategies
//         ./a06 bench    probe-count and timing comparison of the strategies
//
// The user records live in a hand-written hash table (no std::unordered_map).
// Four collision strategies are implemented behind one interface; separate
// chaining (class HashTable) is the one chosen for the authentication demo.

#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <vector>

// ============================================================================
// Hash function and index helpers
// ============================================================================

// demoHash is the course-provided educational hash (FNV-1a style, 64-bit),
// used exactly as given. (Its offset basis is one digit shorter than the
// standard FNV-1a constant 14695981039346656037; it still mixes well.)
// It is fast and well-distributed for hash-table indexing, but it is NOT a
// password-hashing function: it is designed to be fast, which is exactly what
// an attacker guessing passwords wants. See the write-up for details.


inline uint64_t demoHash(const std::string& s) {
    uint64_t h = 1469598103934665603ULL;
    for (unsigned char c : s) {
        h = (h ^ c) * 1099511628211ULL;
    }
    return h;
}

// Smallest power of two >= n (minimum 2). Power-of-two capacities let us use a
// bit mask instead of '%' and guarantee that quadratic (triangular) probing and
// double hashing with an odd step visit every slot.
inline std::size_t roundUpPow2(std::size_t n) {
    std::size_t p = 2;
    while (p < n) p <<= 1;
    return p;
}

// Map a 64-bit hash to a bucket. XOR-folding the upper 32 bits into the lower
// 32 bits means the high bits of the hash still influence the bucket when we
// mask with a small capacity.
inline std::size_t homeIndex(uint64_t h, std::size_t capacity) {
    return static_cast<std::size_t>(h ^ (h >> 32)) & (capacity - 1);
}

// Second hash for double hashing. Multiplying by a large odd constant
// (Fibonacci hashing) decorrelates the step from the home index; forcing the
// result odd makes it coprime with a power-of-two capacity.
inline std::size_t secondaryStep(uint64_t h) {
    return static_cast<std::size_t>((h * 0x9E3779B97F4A7C15ULL) >> 33) | 1u;
}

inline std::string toHex(uint64_t v) {
    char buf[17];
    std::snprintf(buf, sizeof buf, "%016llx", static_cast<unsigned long long>(v));
    return std::string(buf);
}

// ============================================================================
// User record
// ============================================================================

// One stored account. The plaintext password is never stored: only the
// per-user salt and demoHash(salt + password + pepper).
struct UserRecord {
    std::string username;
    std::string salt;           // 16 hex characters, unique per user
    uint64_t passwordHash = 0;  // demoHash(salt + password + pepper)
};

// ============================================================================
// Common table interface + instrumentation
// ============================================================================

// Common interface for every collision strategy, so the auth service, tests
// and benchmark can run the exact same code against each implementation.



// Instrumentation used by the benchmark to compare strategies.
struct ProbeStats {
    uint64_t lookups = 0;   // number of find() calls
    uint64_t probes = 0;    // slots / chain nodes examined across those calls
    uint64_t rehashes = 0;  // number of resize/rehash events
    double avgProbes() const { return lookups ? static_cast<double>(probes) / lookups : 0.0; }
};

// Called whenever a table rehashes: (strategy, oldCapacity, newCapacity, entriesMoved)
using RehashListener =
    std::function<void(const std::string&, std::size_t, std::size_t, std::size_t)>;

class UserTable {
public:
    virtual ~UserTable() = default;

    // Returns true if the key was new, false if an existing record was replaced.
    virtual bool insert(const std::string& username, const UserRecord& record) = 0;
    // Returns nullptr if the key is absent.
    virtual const UserRecord* find(const std::string& username) const = 0;
    // Returns true if a record was removed.
    virtual bool remove(const std::string& username) = 0;
    // Live entries / capacity.
    virtual double loadFactor() const = 0;
    virtual std::size_t size() const = 0;
    virtual std::size_t capacity() const = 0;
    virtual std::string strategyName() const = 0;

    void setRehashListener(RehashListener listener) { listener_ = std::move(listener); }
    const ProbeStats& stats() const { return stats_; }
    void resetProbeStats() const { stats_.lookups = 0; stats_.probes = 0; }

protected:
    void notifyRehash(std::size_t oldCap, std::size_t newCap) {
        ++stats_.rehashes;
        if (listener_) listener_(strategyName(), oldCap, newCap, size());
    }

    mutable ProbeStats stats_;  // mutable: find() is const but still counts probes
    RehashListener listener_;
};

// ============================================================================
// HashTable: SEPARATE CHAINING (chosen strategy)
// ============================================================================

// HashTable: separate chaining. This is the strategy I chose for the final
// authentication demo (see the write-up for the benchmark that justifies it).
//
// Layout: a power-of-two array of buckets; each bucket is a singly linked list
// of heap-allocated nodes. Each node caches its full 64-bit hash, so rehashing
// never recomputes demoHash and most mismatches are rejected without a string
// comparison.



class HashTable : public UserTable {
public:
    explicit HashTable(std::size_t initialCapacity = 8, double maxLoad = 0.75)
        : buckets_(roundUpPow2(initialCapacity)), maxLoad_(maxLoad) {}

    ~HashTable() override { clear(); }
    HashTable(const HashTable&) = delete;
    HashTable& operator=(const HashTable&) = delete;

    bool insert(const std::string& username, const UserRecord& record) override {
        const uint64_t h = demoHash(username);
        // Update in place if the key already exists.
        for (Node* n = buckets_[homeIndex(h, buckets_.size())].get(); n; n = n->next.get()) {
            if (n->hash == h && n->key == username) {
                n->value = record;
                return false;
            }
        }
        // Grow before adding if this insert would exceed the max load factor.
        if (static_cast<double>(size_ + 1) / buckets_.size() > maxLoad_) {
            rehash(buckets_.size() * 2);
        }
        auto node = std::make_unique<Node>();
        node->hash = h;
        node->key = username;
        node->value = record;
        std::unique_ptr<Node>& head = buckets_[homeIndex(h, buckets_.size())];
        node->next = std::move(head);  // push-front: O(1)
        head = std::move(node);
        ++size_;
        return true;
    }

    const UserRecord* find(const std::string& username) const override {
        const uint64_t h = demoHash(username);
        ++stats_.lookups;
        std::size_t visited = 0;
        for (const Node* n = buckets_[homeIndex(h, buckets_.size())].get(); n; n = n->next.get()) {
            ++visited;
            if (n->hash == h && n->key == username) {
                stats_.probes += visited;
                return &n->value;
            }
        }
        stats_.probes += visited ? visited : 1;  // inspecting an empty bucket costs one probe
        return nullptr;
    }

    bool remove(const std::string& username) override {
        const uint64_t h = demoHash(username);
        std::unique_ptr<Node>* link = &buckets_[homeIndex(h, buckets_.size())];
        while (*link) {
            if ((*link)->hash == h && (*link)->key == username) {
                *link = std::move((*link)->next);  // unlink; old node is freed
                --size_;
                return true;
            }
            link = &(*link)->next;
        }
        return false;
    }

    double loadFactor() const override {
        return static_cast<double>(size_) / buckets_.size();
    }
    std::size_t size() const override { return size_; }
    std::size_t capacity() const override { return buckets_.size(); }
    std::string strategyName() const override { return "separate chaining"; }

    // ---- Inspection helpers used by the demo to visualise collisions ----
    std::vector<std::string> bucketKeys(std::size_t bucket) const {
        std::vector<std::string> keys;
        for (const Node* n = buckets_[bucket].get(); n; n = n->next.get()) keys.push_back(n->key);
        return keys;
    }
    std::size_t longestChain() const {
        std::size_t best = 0;
        for (std::size_t b = 0; b < buckets_.size(); ++b) {
            std::size_t len = 0;
            for (const Node* n = buckets_[b].get(); n; n = n->next.get()) ++len;
            if (len > best) best = len;
        }
        return best;
    }

private:
    struct Node {
        uint64_t hash = 0;
        std::string key;
        UserRecord value;
        std::unique_ptr<Node> next;
    };

    // Relink every node into a new bucket array. Nodes are moved, not copied,
    // so pointers returned by find() stay valid across a rehash.
    void rehash(std::size_t newCapacity) {
        std::vector<std::unique_ptr<Node>> fresh(newCapacity);
        for (auto& head : buckets_) {
            while (head) {
                std::unique_ptr<Node> n = std::move(head);
                head = std::move(n->next);
                std::unique_ptr<Node>& dest = fresh[homeIndex(n->hash, newCapacity)];
                n->next = std::move(dest);
                dest = std::move(n);
            }
        }
        const std::size_t oldCapacity = buckets_.size();
        buckets_.swap(fresh);
        notifyRehash(oldCapacity, newCapacity);
    }

    // Iterative teardown so a very long chain can't overflow the stack through
    // recursive unique_ptr destructors.
    void clear() {
        for (auto& head : buckets_) {
            while (head) head = std::move(head->next);
        }
        size_ = 0;
    }

    std::vector<std::unique_ptr<Node>> buckets_;
    std::size_t size_ = 0;
    double maxLoad_;
};

// ============================================================================
// Open addressing: linear, quadratic, double hashing
// ============================================================================

// Open addressing: every entry lives directly in the slot array. On a
// collision we probe a sequence of other slots. Three probe sequences:
//
//   Linear     : home + i                 (mod capacity)
//   Quadratic  : home + i(i+1)/2          (triangular numbers; with a
//                                          power-of-two capacity this visits
//                                          every slot exactly once)
//   DoubleHash : home + i * step(h)       (step is odd, so it is coprime with
//                                          a power-of-two capacity)
//
// Deletion uses tombstones: a removed slot is marked Deleted rather than
// Empty, because an Empty slot would cut the probe chain and hide keys stored
// further along it. Tombstones are reused by later inserts and flushed by
// rehashing.



enum class ProbeMode { Linear, Quadratic, DoubleHash };

class OpenAddressingTable : public UserTable {
public:
    explicit OpenAddressingTable(ProbeMode mode, std::size_t initialCapacity = 8,
                                 double maxLoad = 0.5)
        : slots_(roundUpPow2(initialCapacity)), maxLoad_(maxLoad), mode_(mode) {}

    bool insert(const std::string& username, const UserRecord& record) override {
        const uint64_t h = demoHash(username);
        const std::size_t existing = locate(h, username, /*countProbes=*/false);
        if (existing != npos) {
            slots_[existing].value = record;
            return false;
        }
        // Tombstones lengthen probe sequences just like live entries, so they
        // count toward the resize threshold.
        if (static_cast<double>(size_ + tombstones_ + 1) / slots_.size() > maxLoad_) {
            // If live entries alone are past half the threshold, grow.
            // Otherwise the table is mostly tombstones: rebuild at the same size.
            const bool grow = static_cast<double>(size_ + 1) / slots_.size() > maxLoad_ / 2;
            rehash(grow ? slots_.size() * 2 : slots_.size());
        }
        place(h, username, record);
        ++size_;
        return true;
    }

    const UserRecord* find(const std::string& username) const override {
        ++stats_.lookups;
        const std::size_t idx = locate(demoHash(username), username, /*countProbes=*/true);
        return idx == npos ? nullptr : &slots_[idx].value;
    }

    bool remove(const std::string& username) override {
        const std::size_t idx = locate(demoHash(username), username, /*countProbes=*/false);
        if (idx == npos) return false;
        Slot& s = slots_[idx];
        s.state = State::Deleted;  // tombstone keeps the probe chain intact
        s.key.clear();
        s.value = UserRecord{};
        --size_;
        ++tombstones_;
        return true;
    }

    double loadFactor() const override {
        return static_cast<double>(size_) / slots_.size();
    }
    std::size_t size() const override { return size_; }
    std::size_t capacity() const override { return slots_.size(); }
    std::size_t tombstones() const { return tombstones_; }

    std::string strategyName() const override {
        switch (mode_) {
            case ProbeMode::Linear: return "linear probing";
            case ProbeMode::Quadratic: return "quadratic probing";
            case ProbeMode::DoubleHash: return "double hashing";
        }
        return "open addressing";
    }

private:
    enum class State : uint8_t { Empty, Occupied, Deleted };
    struct Slot {
        State state = State::Empty;
        uint64_t hash = 0;
        std::string key;
        UserRecord value;
    };
    static constexpr std::size_t npos = static_cast<std::size_t>(-1);

    // i-th slot in the probe sequence for hash h.
    std::size_t probeAt(uint64_t h, std::size_t i, std::size_t cap) const {
        const std::size_t mask = cap - 1;
        const std::size_t home = homeIndex(h, cap);
        switch (mode_) {
            case ProbeMode::Linear: return (home + i) & mask;
            case ProbeMode::Quadratic: return (home + i * (i + 1) / 2) & mask;
            case ProbeMode::DoubleHash: return (home + i * secondaryStep(h)) & mask;
        }
        return home;
    }

    // Index of the slot holding key, or npos. Stops at the first Empty slot.
    std::size_t locate(uint64_t h, const std::string& key, bool countProbes) const {
        const std::size_t cap = slots_.size();
        for (std::size_t i = 0; i < cap; ++i) {
            const std::size_t idx = probeAt(h, i, cap);
            if (countProbes) ++stats_.probes;
            const Slot& s = slots_[idx];
            if (s.state == State::Empty) return npos;
            if (s.state == State::Occupied && s.hash == h && s.key == key) return idx;
        }
        return npos;
    }

    // Put a key known to be absent into the first Empty or Deleted slot.
    void place(uint64_t h, const std::string& key, const UserRecord& record) {
        const std::size_t cap = slots_.size();
        for (std::size_t i = 0; i < cap; ++i) {
            Slot& s = slots_[probeAt(h, i, cap)];
            if (s.state != State::Occupied) {
                if (s.state == State::Deleted) --tombstones_;
                s.state = State::Occupied;
                s.hash = h;
                s.key = key;
                s.value = record;
                return;
            }
        }
        // Unreachable while maxLoad < 1: a free slot always exists.
    }

    void rehash(std::size_t newCapacity) {
        std::vector<Slot> old(newCapacity);
        old.swap(slots_);  // slots_ is now an empty array of the new size
        tombstones_ = 0;
        for (Slot& s : old) {
            if (s.state == State::Occupied) place(s.hash, s.key, s.value);
        }
        notifyRehash(old.size(), newCapacity);
    }

    std::vector<Slot> slots_;
    std::size_t size_ = 0;
    std::size_t tombstones_ = 0;
    double maxLoad_;
    ProbeMode mode_;
};

// ============================================================================
// Strategy factory
// ============================================================================

enum class Strategy { SeparateChaining, LinearProbing, QuadraticProbing, DoubleHashing };

constexpr Strategy kAllStrategies[] = {Strategy::SeparateChaining, Strategy::LinearProbing,
                                       Strategy::QuadraticProbing, Strategy::DoubleHashing};

// Default max load factors: chaining tolerates high load gracefully;
// open addressing degrades quickly past ~0.5-0.7, so it resizes earlier.
inline double defaultMaxLoad(Strategy s) {
    return s == Strategy::SeparateChaining ? 0.75 : 0.5;
}

// maxLoad <= 0 means "use the default for this strategy".
inline std::unique_ptr<UserTable> makeTable(Strategy s, std::size_t initialCapacity = 8,
                                            double maxLoad = 0.0) {
    if (maxLoad <= 0.0) maxLoad = defaultMaxLoad(s);
    switch (s) {
        case Strategy::SeparateChaining:
            return std::make_unique<HashTable>(initialCapacity, maxLoad);
        case Strategy::LinearProbing:
            return std::make_unique<OpenAddressingTable>(ProbeMode::Linear, initialCapacity, maxLoad);
        case Strategy::QuadraticProbing:
            return std::make_unique<OpenAddressingTable>(ProbeMode::Quadratic, initialCapacity, maxLoad);
        case Strategy::DoubleHashing:
            return std::make_unique<OpenAddressingTable>(ProbeMode::DoubleHash, initialCapacity, maxLoad);
    }
    return nullptr;
}

// ============================================================================
// Authentication service
// ============================================================================

enum class LoginResult { Success, WrongPassword, UnknownUser };

const char* loginResultName(LoginResult r);

class AuthService {
public:
    // The table is injected so the same login code runs on every strategy.
    // saltSeed makes the demo output reproducible for the write-up; a real
    // system would draw salts from a cryptographically secure source.
    AuthService(std::unique_ptr<UserTable> table, uint64_t saltSeed);

    // Returns false (and changes nothing) if the username is already taken.
    bool registerUser(const std::string& username, const std::string& password);
    LoginResult login(const std::string& username, const std::string& password) const;
    bool removeUser(const std::string& username);

    const UserTable& table() const { return *users_; }

    // demoHash(salt + password + pepper)
    static uint64_t hashPassword(const std::string& salt, const std::string& password);

private:
    std::string makeSalt();

    std::unique_ptr<UserTable> users_;
    std::mt19937_64 rng_;
};

// ============================================================================
// Authentication service implementation
// ============================================================================

namespace {
// The pepper is a secret shared by every account and kept OUT of the user
// table. If the table leaks but the pepper does not, stored hashes cannot be
// checked offline. In production it would come from a secrets manager or
// environment variable, never source code; it is hard-coded here for the demo.
const std::string kPepper = "CS210-pepper-v1";
}  // namespace

const char* loginResultName(LoginResult r) {
    switch (r) {
        case LoginResult::Success: return "SUCCESS";
        case LoginResult::WrongPassword: return "WRONG PASSWORD";
        case LoginResult::UnknownUser: return "UNKNOWN USER";
    }
    return "?";
}

AuthService::AuthService(std::unique_ptr<UserTable> table, uint64_t saltSeed)
    : users_(std::move(table)), rng_(saltSeed) {}

uint64_t AuthService::hashPassword(const std::string& salt, const std::string& password) {
    return demoHash(salt + password + kPepper);
}

std::string AuthService::makeSalt() {
    return toHex(rng_());  // 64 random bits -> 16 hex chars
}

bool AuthService::registerUser(const std::string& username, const std::string& password) {
    if (users_->find(username) != nullptr) return false;
    UserRecord rec;
    rec.username = username;
    rec.salt = makeSalt();
    rec.passwordHash = hashPassword(rec.salt, password);
    users_->insert(username, rec);
    return true;
}

LoginResult AuthService::login(const std::string& username, const std::string& password) const {
    const UserRecord* rec = users_->find(username);  // expected O(1)
    if (rec == nullptr) return LoginResult::UnknownUser;
    // Recompute with the stored salt and compare. (Real systems also use a
    // constant-time comparison; one 64-bit compare is already branch-free.)
    return hashPassword(rec->salt, password) == rec->passwordHash ? LoginResult::Success
                                                                  : LoginResult::WrongPassword;
}

bool AuthService::removeUser(const std::string& username) {
    return users_->remove(username);
}

// ============================================================================
// DEMO MODE (default): authentication walkthrough
// ============================================================================

namespace demo {

// Demonstrates: registration of salted+peppered users, successful login,
// failed password, unknown user, removal, rehash events, visible collisions,
// and the same flow running on all four collision strategies.


namespace {

int g_pass = 0;
int g_fail = 0;

void check(bool ok, const std::string& what) {
    std::cout << (ok ? "    [PASS] " : "    [FAIL] ") << what << '\n';
    (ok ? g_pass : g_fail)++;
}

void section(const std::string& title) {
    std::cout << "\n=== " << title << " ===\n";
}

void attempt(const AuthService& auth, const std::string& user, const std::string& pw,
             LoginResult expected) {
    const LoginResult r = auth.login(user, pw);
    std::cout << "  login(\"" << user << "\", \"" << pw << "\") -> " << loginResultName(r) << '\n';
    check(r == expected, std::string("expected ") + loginResultName(expected));
}

void printTableState(const UserTable& t) {
    std::cout << "    size=" << t.size() << " capacity=" << t.capacity() << " load="
              << std::fixed << std::setprecision(3) << t.loadFactor() << '\n';
}

void printBuckets(const HashTable& t) {
    for (std::size_t b = 0; b < t.capacity(); ++b) {
        const auto keys = t.bucketKeys(b);
        std::cout << "    [" << std::setw(2) << b << "] ";
        if (keys.empty()) std::cout << "(empty)";
        for (std::size_t i = 0; i < keys.size(); ++i) std::cout << (i ? " -> " : "") << keys[i];
        if (keys.size() > 1) std::cout << "   <-- collision, chain length " << keys.size();
        std::cout << '\n';
    }
}

struct DemoUser {
    std::string name;
    std::string password;
};

const std::vector<DemoUser> kUsers = {
    {"alice", "Wonderland#42"}, {"bob", "b0bcat!"},       {"carmen", "SanDiego2026"},
    {"dmitri", "Tchaikovsky1840"}, {"eunji", "kimchi&rice"}, {"farah", "desertRose7"},
    {"gabe", "hunter2"},        {"hiro", "hunter2"},  // same password on purpose
};

constexpr uint64_t kSaltSeed = 210;

}  // namespace

int runDemo() {
    std::cout << "CS 210 Assignment 06 - Passwords and Hash Tables (Talan Jewett)\n";

    auto chained = std::make_unique<HashTable>(4, 0.75);
    HashTable* table = chained.get();  // non-owning view for bucket printing
    table->setRehashListener([](const std::string& s, std::size_t oldCap, std::size_t newCap,
                                std::size_t moved) {
        std::cout << "  [REHASH] " << s << ": " << oldCap << " -> " << newCap << " buckets ("
                  << moved << " entries relinked)\n";
    });
    AuthService auth(std::move(chained), kSaltSeed);

    // ------------------------------------------------------------------
    section("1. Register 8 users (separate chaining, start capacity 4, max load 0.75)");
    for (const auto& u : kUsers) {
        auth.registerUser(u.name, u.password);
        const UserRecord* r = table->find(u.name);
        std::cout << "  + " << std::left << std::setw(7) << u.name << std::right
                  << " salt=" << r->salt << "  hash=" << toHex(r->passwordHash)
                  << "  load=" << std::fixed << std::setprecision(3) << table->loadFactor()
                  << " (" << table->size() << "/" << table->capacity() << ")\n";
    }
    check(table->size() == 8, "8 users stored");
    check(table->stats().rehashes == 2, "two automatic rehash events (4->8, 8->16)");
    check(table->loadFactor() <= 0.75, "load factor stays <= 0.75");
    check(!auth.registerUser("alice", "different"), "duplicate username is rejected");

    // ------------------------------------------------------------------
    section("2. Bucket layout (collisions handled by chaining)");
    printBuckets(*table);
    std::cout << "    longest chain = " << table->longestChain() << '\n';

    // ------------------------------------------------------------------
    section("3. Salt demonstration: gabe and hiro share the password \"hunter2\"");
    const UserRecord* g = table->find("gabe");
    const UserRecord* h = table->find("hiro");
    std::cout << "  gabe: salt=" << g->salt << " hash=" << toHex(g->passwordHash) << '\n';
    std::cout << "  hiro: salt=" << h->salt << " hash=" << toHex(h->passwordHash) << '\n';
    check(g->salt != h->salt, "salts differ");
    check(g->passwordHash != h->passwordHash, "same password -> different stored hashes");
    check(AuthService::hashPassword(g->salt, "hunter2") == g->passwordHash,
          "hash recomputes from stored salt + password + pepper");

    // ------------------------------------------------------------------
    section("4. Login flow");
    attempt(auth, "alice", "Wonderland#42", LoginResult::Success);
    attempt(auth, "carmen", "SanDiego2026", LoginResult::Success);
    attempt(auth, "alice", "wonderland#42", LoginResult::WrongPassword);  // case differs
    attempt(auth, "dmitri", "", LoginResult::WrongPassword);
    attempt(auth, "gabe", "hunter3", LoginResult::WrongPassword);
    attempt(auth, "mallory", "Wonderland#42", LoginResult::UnknownUser);
    attempt(auth, "Alice", "Wonderland#42", LoginResult::UnknownUser);  // keys are case-sensitive

    // ------------------------------------------------------------------
    section("5. Removal");
    check(auth.removeUser("bob"), "remove(\"bob\") returns true");
    attempt(auth, "bob", "b0bcat!", LoginResult::UnknownUser);
    check(!auth.removeUser("bob"), "removing bob again returns false");
    check(table->find("bob") == nullptr, "find(\"bob\") returns nullptr");
    check(table->size() == 7, "size is now 7");
    attempt(auth, "eunji", "kimchi&rice", LoginResult::Success);  // neighbours unaffected
    printTableState(*table);

    // ------------------------------------------------------------------
    section("6. Rehash event: add users until load would exceed 0.75");
    const std::size_t before = table->capacity();
    for (int i = 1; i <= 6; ++i) {
        const std::string name = "student" + std::to_string(i);
        auth.registerUser(name, "pw" + std::to_string(i));
        std::cout << "  + " << name << "  load=" << std::fixed << std::setprecision(3)
                  << table->loadFactor() << " (" << table->size() << "/" << table->capacity()
                  << ")\n";
    }
    check(table->capacity() == before * 2, "capacity doubled from 16 to 32");
    check(table->stats().rehashes == 3, "third rehash event recorded");
    bool allOk = true;
    for (const auto& u : kUsers) {
        if (u.name == "bob") continue;
        allOk = allOk && auth.login(u.name, u.password) == LoginResult::Success;
    }
    check(allOk, "every original user still logs in after the rehash");
    attempt(auth, "student6", "pw6", LoginResult::Success);

    // ------------------------------------------------------------------
    section("7. Same workflow on all four collision strategies");
    std::cout << "  " << std::left << std::setw(20) << "strategy" << std::right << std::setw(6)
              << "size" << std::setw(6) << "cap" << std::setw(8) << "load" << std::setw(10)
              << "rehashes" << std::setw(12) << "avg probes" << "  logins\n";
    for (Strategy s : kAllStrategies) {
        AuthService a(makeTable(s, 4), kSaltSeed);
        for (const auto& u : kUsers) a.registerUser(u.name, u.password);
        a.removeUser("bob");
        for (int i = 1; i <= 6; ++i) a.registerUser("student" + std::to_string(i), "pw" + std::to_string(i));
        a.table().resetProbeStats();
        bool ok = a.login("bob", "b0bcat!") == LoginResult::UnknownUser &&
                  a.login("alice", "nope") == LoginResult::WrongPassword;
        for (const auto& u : kUsers)
            if (u.name != "bob") ok = ok && a.login(u.name, u.password) == LoginResult::Success;
        const UserTable& t = a.table();
        std::cout << "  " << std::left << std::setw(20) << t.strategyName() << std::right
                  << std::setw(6) << t.size() << std::setw(6) << t.capacity() << std::setw(8)
                  << std::setprecision(3) << t.loadFactor() << std::setw(10)
                  << t.stats().rehashes << std::setw(12) << std::setprecision(2)
                  << t.stats().avgProbes() << "  " << (ok ? "all correct" : "MISMATCH") << '\n';
        check(ok, t.strategyName() + ": success / wrong password / unknown user all correct");
    }

    std::cout << "\nSummary: " << g_pass << " checks passed, " << g_fail << " failed\n";
    return g_fail == 0 ? 0 : 1;
}

}  // namespace demo

// ============================================================================
// TEST MODE: unit, edge-case and randomized tests
// ============================================================================

namespace tests {

// Every table test runs against all four strategies. std::map is used ONLY as
// a reference oracle in the randomized test; it never stores user records.


namespace {

int g_pass = 0;
int g_fail = 0;

#define EXPECT(cond)                                                                  \
    do {                                                                              \
        if (cond) {                                                                   \
            ++g_pass;                                                                 \
        } else {                                                                      \
            ++g_fail;                                                                 \
            std::cout << "    FAIL line " << __LINE__ << ": " #cond << '\n';          \
        }                                                                             \
    } while (0)

UserRecord rec(const std::string& user, uint64_t h = 0) {
    UserRecord r;
    r.username = user;
    r.salt = "salt";
    r.passwordHash = h;
    return r;
}

bool isPow2(std::size_t n) { return n && !(n & (n - 1)); }

void testHashFunction() {
    // Regression values for the course-provided demoHash. Note: its offset
    // basis (1469598103934665603) is one digit shorter than standard FNV-1a's
    // (14695981039346656037), so outputs differ from published FNV-1a vectors.
    // I use the function exactly as provided.
    EXPECT(demoHash("") == 1469598103934665603ULL);
    EXPECT(demoHash("a") == 0x44bd8ad473cd9906ULL);
    EXPECT(demoHash("foobar") == 0x88fad7c0a8ff07f2ULL);
    EXPECT(demoHash("alice") == demoHash("alice"));  // deterministic
    EXPECT(demoHash("alice") != demoHash("Alice"));
}

void testBasics(Strategy s) {
    auto t = makeTable(s, 8);
    EXPECT(t->size() == 0);
    EXPECT(t->loadFactor() == 0.0);
    EXPECT(t->find("ghost") == nullptr);
    EXPECT(!t->remove("ghost"));

    EXPECT(t->insert("alice", rec("alice", 1)));
    EXPECT(!t->insert("alice", rec("alice", 2)));  // duplicate key -> update, not a new entry
    EXPECT(t->size() == 1);
    const UserRecord* r = t->find("alice");
    EXPECT(r != nullptr && r->passwordHash == 2);

    EXPECT(t->insert("bob", rec("bob", 3)));
    EXPECT(std::fabs(t->loadFactor() - 2.0 / t->capacity()) < 1e-12);

    EXPECT(t->remove("alice"));
    EXPECT(t->find("alice") == nullptr);
    EXPECT(!t->remove("alice"));
    EXPECT(t->size() == 1);
    EXPECT(t->find("bob") != nullptr);

    EXPECT(t->insert("", rec("", 9)));  // empty string is a legal key
    EXPECT(t->find("") != nullptr && t->find("")->passwordHash == 9);
}

void testResize(Strategy s) {
    auto t = makeTable(s, 2);
    const double maxLoad = defaultMaxLoad(s);
    bool loadOk = true;
    for (int i = 0; i < 5000; ++i) {
        t->insert("user" + std::to_string(i), rec("u", static_cast<uint64_t>(i)));
        loadOk = loadOk && t->loadFactor() <= maxLoad;
    }
    EXPECT(loadOk);
    EXPECT(t->size() == 5000);
    EXPECT(isPow2(t->capacity()));
    EXPECT(t->stats().rehashes >= 10);
    bool allFound = true;
    for (int i = 0; i < 5000; ++i) {
        const UserRecord* r = t->find("user" + std::to_string(i));
        allFound = allFound && r && r->passwordHash == static_cast<uint64_t>(i);
    }
    EXPECT(allFound);
}

void testForcedCollisions(Strategy s) {
    const std::size_t cap = 16;
    // Very high max load for chaining so the table never resizes in this test.
    auto t = makeTable(s, cap, s == Strategy::SeparateChaining ? 100.0 : 0.95);
    std::vector<std::string> keys;  // six keys that all hash to bucket 3
    for (int i = 0; keys.size() < 6; ++i) {
        const std::string k = "k" + std::to_string(i);
        if (homeIndex(demoHash(k), cap) == 3) keys.push_back(k);
    }
    for (const auto& k : keys) t->insert(k, rec(k));
    EXPECT(t->capacity() == cap);
    bool allFound = true;
    for (const auto& k : keys) allFound = allFound && t->find(k) != nullptr;
    EXPECT(allFound);

    // Removing from the middle of a collision cluster must not hide later keys
    // (this is what tombstones are for in open addressing).
    EXPECT(t->remove(keys[2]));
    EXPECT(t->find(keys[2]) == nullptr);
    bool othersFound = true;
    for (std::size_t i = 0; i < keys.size(); ++i)
        if (i != 2) othersFound = othersFound && t->find(keys[i]) != nullptr;
    EXPECT(othersFound);
    EXPECT(t->insert(keys[2], rec(keys[2])));  // reinsert (reuses tombstone)
    EXPECT(t->find(keys[2]) != nullptr);
    EXPECT(t->size() == keys.size());
}

void testTombstoneChurn(Strategy s) {
    // Insert/remove cycles must not grow the table forever or loop infinitely.
    auto t = makeTable(s, 8);
    t->insert("keepA", rec("keepA"));
    t->insert("keepB", rec("keepB"));
    for (int i = 0; i < 20000; ++i) {
        const std::string k = "tmp" + std::to_string(i);
        t->insert(k, rec(k));
        t->remove(k);
    }
    EXPECT(t->size() == 2);
    EXPECT(t->capacity() <= 16);
    EXPECT(t->find("keepA") != nullptr && t->find("keepB") != nullptr);
}

void testRandomizedAgainstReference(Strategy s) {
    auto t = makeTable(s, 4);
    std::map<std::string, uint64_t> ref;  // oracle only
    std::mt19937 rng(42);
    std::uniform_int_distribution<int> keyDist(0, 1999), opDist(0, 2);
    bool consistent = true;
    for (int step = 0; step < 50000; ++step) {
        const std::string k = "key" + std::to_string(keyDist(rng));
        const uint64_t v = static_cast<uint64_t>(step);
        switch (opDist(rng)) {
            case 0: {
                const bool isNew = ref.find(k) == ref.end();
                consistent = consistent && t->insert(k, rec(k, v)) == isNew;
                ref[k] = v;
                break;
            }
            case 1:
                consistent = consistent && t->remove(k) == (ref.erase(k) == 1);
                break;
            default: {
                const UserRecord* r = t->find(k);
                auto it = ref.find(k);
                consistent = consistent && (it == ref.end() ? r == nullptr
                                                            : r && r->passwordHash == it->second);
            }
        }
    }
    EXPECT(consistent);
    EXPECT(t->size() == ref.size());
    bool finalMatch = true;
    for (const auto& kv : ref) {
        const UserRecord* r = t->find(kv.first);
        finalMatch = finalMatch && r && r->passwordHash == kv.second;
    }
    EXPECT(finalMatch);
}

void testAuth(Strategy s) {
    AuthService auth(makeTable(s, 2), 7);
    const std::vector<std::pair<std::string, std::string>> users = {
        {"ana", "pa55"}, {"ben", "secret"}, {"cy", "secret"}, {"dee", "x"}, {"eli", "!@#$"}};
    for (const auto& u : users) EXPECT(auth.registerUser(u.first, u.second));
    EXPECT(!auth.registerUser("ana", "other"));
    EXPECT(auth.table().size() == 5);
    for (const auto& u : users) EXPECT(auth.login(u.first, u.second) == LoginResult::Success);
    EXPECT(auth.login("ana", "PA55") == LoginResult::WrongPassword);
    EXPECT(auth.login("ana", "") == LoginResult::WrongPassword);
    EXPECT(auth.login("zed", "pa55") == LoginResult::UnknownUser);
    EXPECT(auth.login("", "") == LoginResult::UnknownUser);
    const UserRecord* b = auth.table().find("ben");
    const UserRecord* c = auth.table().find("cy");
    EXPECT(b->salt.size() == 16 && b->salt != c->salt);
    EXPECT(b->passwordHash != c->passwordHash);  // same password, different salts
    EXPECT(auth.removeUser("ben"));
    EXPECT(auth.login("ben", "secret") == LoginResult::UnknownUser);
    EXPECT(auth.login("cy", "secret") == LoginResult::Success);
}

void runGroup(const std::string& name, void (*fn)(Strategy)) {
    for (Strategy s : kAllStrategies) {
        const int failBefore = g_fail;
        fn(s);
        std::cout << "  " << (g_fail == failBefore ? "ok  " : "FAIL") << "  " << name << " ["
                  << makeTable(s)->strategyName() << "]\n";
    }
}

}  // namespace

int runTests() {
    std::cout << "Running hash table tests\n";
    testHashFunction();
    std::cout << "  " << (g_fail ? "FAIL" : "ok  ") << "  demoHash reference values\n";
    runGroup("insert/find/remove/loadFactor basics", testBasics);
    runGroup("automatic resize keeps all keys (5000 inserts)", testResize);
    runGroup("forced collisions + removal mid-cluster", testForcedCollisions);
    runGroup("tombstone churn (20000 insert/remove cycles)", testTombstoneChurn);
    runGroup("50000 random ops vs reference map", testRandomizedAgainstReference);
    runGroup("auth: register/login/remove", testAuth);
    std::cout << "\n" << g_pass << " assertions passed, " << g_fail << " failed\n";
    return g_fail == 0 ? 0 : 1;
}

}  // namespace tests

// ============================================================================
// BENCH MODE: compare the four collision strategies
// ============================================================================

namespace bench {

// Part A: average probes per lookup at fixed load factors (no resizing).
// Part B: wall-clock time for a realistic workload with automatic resizing
//         and a delete-heavy phase.


namespace {

UserRecord rec(const std::string& u) {
    UserRecord r;
    r.username = u;
    return r;
}

std::vector<std::string> makeKeys(const std::string& prefix, std::size_t n) {
    std::vector<std::string> v;
    v.reserve(n);
    for (std::size_t i = 0; i < n; ++i) v.push_back(prefix + std::to_string(i));
    return v;
}

double msSince(std::chrono::steady_clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
}

}  // namespace

int runBench() {
    const std::size_t cap = 1u << 16;  // 65,536 slots
    const auto hitKeys = makeKeys("user", cap);
    const auto missKeys = makeKeys("miss", cap);

    std::cout << "Part A: average probes per lookup, capacity " << cap << ", no resizing\n";
    std::cout << std::left << std::setw(20) << "strategy" << std::right;
    const double loads[] = {0.25, 0.50, 0.75, 0.90};
    for (double a : loads) std::cout << "   hit@" << std::fixed << std::setprecision(2) << a << "  miss@" << a;
    std::cout << '\n';

    for (Strategy s : kAllStrategies) {
        std::cout << std::left << std::setw(20) << makeTable(s)->strategyName() << std::right;
        for (double a : loads) {
            auto t = makeTable(s, cap, 0.99);
            const std::size_t n = static_cast<std::size_t>(a * cap);
            for (std::size_t i = 0; i < n; ++i) t->insert(hitKeys[i], rec(hitKeys[i]));
            t->resetProbeStats();
            for (std::size_t i = 0; i < n; ++i) t->find(hitKeys[i]);
            const double hit = t->stats().avgProbes();
            t->resetProbeStats();
            for (std::size_t i = 0; i < n; ++i) t->find(missKeys[i]);
            const double miss = t->stats().avgProbes();
            std::cout << std::setprecision(2) << std::setw(10) << hit << std::setw(11) << miss;
        }
        std::cout << '\n';
    }

    const std::size_t N = 200000;
    const auto keys = makeKeys("member", N);
    const auto more = makeKeys("newbie", N / 2);
    const auto misses = makeKeys("nobody", N);
    std::cout << "\nPart B: " << N << " users, default max load, start capacity 8 (ms, best of 3)\n";
    std::cout << std::left << std::setw(20) << "strategy" << std::right << std::setw(10) << "insert"
              << std::setw(10) << "find hit" << std::setw(11) << "find miss" << std::setw(13)
              << "remove 50%" << std::setw(13) << "re-insert" << std::setw(10) << "cap"
              << std::setw(10) << "rehashes" << '\n';
    for (Strategy s : kAllStrategies) {
        double best[5] = {1e18, 1e18, 1e18, 1e18, 1e18};
        std::size_t finalCap = 0;
        uint64_t rehashes = 0;
        for (int rep = 0; rep < 3; ++rep) {
            auto t = makeTable(s, 8);
            double ms[5];
            auto t0 = std::chrono::steady_clock::now();
            for (const auto& k : keys) t->insert(k, rec(k));
            ms[0] = msSince(t0);
            t0 = std::chrono::steady_clock::now();
            for (const auto& k : keys) t->find(k);
            ms[1] = msSince(t0);
            t0 = std::chrono::steady_clock::now();
            for (const auto& k : misses) t->find(k);
            ms[2] = msSince(t0);
            t0 = std::chrono::steady_clock::now();
            for (std::size_t i = 0; i < N; i += 2) t->remove(keys[i]);
            ms[3] = msSince(t0);
            t0 = std::chrono::steady_clock::now();
            for (const auto& k : more) t->insert(k, rec(k));
            ms[4] = msSince(t0);
            for (int i = 0; i < 5; ++i) best[i] = ms[i] < best[i] ? ms[i] : best[i];
            finalCap = t->capacity();
            rehashes = t->stats().rehashes;
        }
        std::cout << std::left << std::setw(20) << makeTable(s)->strategyName() << std::right
                  << std::setprecision(1) << std::setw(10) << best[0] << std::setw(10) << best[1]
                  << std::setw(11) << best[2] << std::setw(13) << best[3] << std::setw(13)
                  << best[4] << std::setw(10) << finalCap << std::setw(10) << rehashes << '\n';
    }
    return 0;
}

}  // namespace bench

// ============================================================================
// Entry point
// ============================================================================

int main(int argc, char* argv[]) {
    const std::string mode = argc > 1 ? argv[1] : "demo";
    if (mode == "demo") return demo::runDemo();
    if (mode == "test") return tests::runTests();
    if (mode == "bench") return bench::runBench();
    std::cerr << "usage: " << argv[0] << " [demo|test|bench]\n";
    return 2;
}
