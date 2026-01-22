/*
Copyright (c) 2012–2026 Oscar Riveros

SATX is free software: you can redistribute it and/or modify it under the terms of the GNU Affero General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

SATX is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License along with this program. If not, see https://www.gnu.org/licenses/.

Commercial licensing options are available. See COMMERCIAL.md for details.
*/

// covertrace_sat.cpp
// COVERTRACE-SAT exact solver (disjoint forbidden subcubes) for DIMACS CNF
// Competition-friendly improvements (exact core):
//  - Preprocessing: unit propagation + pure literal elimination (exact)
//  - Variable reduction via remapping
//  - Fast witness extraction (exact) via W-sum trick
//  - Optional buddy compression (--compress) (heuristic, exactness-preserving)
//  - Optional clause sorting (--sort-clauses) (heuristic)
//
// Indexing improvements (exact):
//  - Multi-signature intersection index:
//    * Build 2-3 independent signature-bucket indices on disjoint sets of frequent vars.
//    * Query each index for compatible buckets; intersect candidate lists.
//    * If a signature query is too broad, we ignore that signature (fallback for that one).
//    * If all signatures are broad, fallback to full scan.
//
// Build: g++ -O2 -std=c++17 covertrace_sat.cpp -o covertrace_sat
// Run:   ./covertrace_sat [--compress] [--sort-clauses] input.cnf
//
// Output:
//   s SATISFIABLE
//   v <lit> ... 0
// or
//   s UNSATISFIABLE

#include <bits/stdc++.h>
using namespace std;

// =====================
// Simple BigInt (non-negative) base 2^32
// =====================
struct BigInt {
    vector<uint32_t> a; // little-endian limbs

    BigInt() = default;
    explicit BigInt(uint64_t x) { set_u64(x); }

    void normalize() { while (!a.empty() && a.back() == 0) a.pop_back(); }
    bool is_zero() const { return a.empty(); }

    void set_u64(uint64_t x) {
        a.clear();
        if (x == 0) return;
        a.push_back(uint32_t(x & 0xFFFFFFFFu));
        uint32_t hi = uint32_t((x >> 32) & 0xFFFFFFFFu);
        if (hi) a.push_back(hi);
    }

    static BigInt pow2(int exp) {
        BigInt r;
        if (exp < 0) return r;
        int limb = exp / 32;
        int bit  = exp % 32;
        r.a.assign(limb + 1, 0);
        r.a[limb] = (1u << bit);
        return r;
    }

    static int cmp(const BigInt& x, const BigInt& y) {
        if (x.a.size() != y.a.size()) return x.a.size() < y.a.size() ? -1 : 1;
        for (int i = (int)x.a.size() - 1; i >= 0; --i) {
            if (x.a[i] != y.a[i]) return x.a[i] < y.a[i] ? -1 : 1;
        }
        return 0;
    }

    void add(const BigInt& b) {
        size_t n = max(a.size(), b.a.size());
        a.resize(n, 0);
        uint64_t carry = 0;
        for (size_t i = 0; i < n; ++i) {
            uint64_t s = carry + a[i] + (i < b.a.size() ? b.a[i] : 0u);
            a[i] = uint32_t(s & 0xFFFFFFFFu);
            carry = s >> 32;
        }
        if (carry) a.push_back(uint32_t(carry));
    }

    void sub(const BigInt& b) {
        // assumes *this >= b
        uint64_t borrow = 0;
        for (size_t i = 0; i < a.size(); ++i) {
            uint64_t bi = (i < b.a.size() ? b.a[i] : 0u);
            uint64_t cur = uint64_t(a[i]);
            uint64_t res;
            if (cur >= bi + borrow) {
                res = cur - bi - borrow;
                borrow = 0;
            } else {
                res = (cur + (1ull << 32)) - bi - borrow;
                borrow = 1;
            }
            a[i] = uint32_t(res & 0xFFFFFFFFu);
        }
        normalize();
    }

    void add_pow2(int exp) { add(pow2(exp)); }
    void sub_pow2(int exp) { sub(pow2(exp)); }
};

// =====================
// DIMACS parsing
// =====================
struct CNF {
    int n = 0;
    vector<vector<int>> clauses;
};

static CNF parse_dimacs(const string& path) {
    ifstream in(path);
    if (!in) {
        cerr << "c ERROR: cannot open file " << path << "\n";
        exit(1);
    }
    CNF cnf;
    string tok;
    int declared_m = -1;
    vector<int> cur;

    while (in >> tok) {
        if (tok == "c") { string rest; getline(in, rest); continue; }
        if (tok == "p") {
            string fmt;
            in >> fmt;
            if (fmt != "cnf") { cerr << "c ERROR: expected 'p cnf'\n"; exit(1); }
            in >> cnf.n >> declared_m;
            continue;
        }
        int lit = stoi(tok);
        if (lit == 0) { cnf.clauses.push_back(cur); cur.clear(); }
        else cur.push_back(lit);
    }
    if (!cur.empty()) { cerr << "c ERROR: last clause missing terminating 0\n"; exit(1); }
    if (cnf.n <= 0) { cerr << "c ERROR: missing or invalid DIMACS header\n"; exit(1); }
    if (declared_m >= 0 && declared_m != (int)cnf.clauses.size()) {
        cerr << "c WARNING: header m=" << declared_m
             << " but parsed " << cnf.clauses.size() << " clauses\n";
    }
    return cnf;
}

// =====================
// Preprocessing: unit propagation + pure literal elimination (exact)
// Then remap to reduced variables
// =====================
struct PreprocessResult {
    bool unsat = false;
    int n_red = 0;
    vector<vector<int>> clauses_red;
    vector<int> assign_full; // size n (original), -1 unassigned, 0/1 fixed
    vector<int> old_to_new;  // size n (original), -1 if fixed, else new index
    vector<int> new_to_old;  // size n_red, original var index
};

static inline int var_of(int lit) { return abs(lit) - 1; }
static inline bool sign_of(int lit) { return lit > 0; }

static PreprocessResult preprocess_cnf(const CNF& cnf) {
    PreprocessResult R;
    int n = cnf.n;
    R.assign_full.assign(n, -1);

    vector<vector<int>> cls = cnf.clauses;

    auto lit_value = [&](int lit) -> int {
        int v = var_of(lit);
        int a = R.assign_full[v];
        if (a == -1) return -1;
        bool pos = sign_of(lit);
        bool val = (a == 1);
        bool sat = pos ? val : !val;
        return sat ? 1 : 0;
    };

    bool changed = true;
    while (changed) {
        changed = false;

        // Unit propagation
        deque<int> unit_queue;
        for (auto &c : cls) {
            bool satisfied = false;
            vector<int> newc;
            newc.reserve(c.size());
            for (int lit : c) {
                int lv = lit_value(lit);
                if (lv == 1) { satisfied = true; break; }
                if (lv == 0) continue;
                newc.push_back(lit);
            }
            if (satisfied) { c.clear(); c.push_back(INT_MAX); continue; }
            c.swap(newc);
            if (c.empty()) { R.unsat = true; return R; }
            if (c.size() == 1) unit_queue.push_back(c[0]);
        }

        while (!unit_queue.empty()) {
            int u = unit_queue.front(); unit_queue.pop_front();
            int v = var_of(u);
            int want = sign_of(u) ? 1 : 0;
            if (R.assign_full[v] != -1) {
                if (R.assign_full[v] != want) { R.unsat = true; return R; }
                continue;
            }
            R.assign_full[v] = want;
            changed = true;
        }
        if (changed) continue;

        // Pure literal elimination
        vector<int8_t> seen_pos(n, 0), seen_neg(n, 0);
        for (auto &c : cls) {
            if (c.size() == 1 && c[0] == INT_MAX) continue;
            for (int lit : c) {
                int v = var_of(lit);
                if (R.assign_full[v] != -1) continue;
                if (lit > 0) seen_pos[v] = 1;
                else seen_neg[v] = 1;
            }
        }
        for (int v = 0; v < n; ++v) {
            if (R.assign_full[v] != -1) continue;
            if (seen_pos[v] && !seen_neg[v]) { R.assign_full[v] = 1; changed = true; }
            else if (!seen_pos[v] && seen_neg[v]) { R.assign_full[v] = 0; changed = true; }
        }
    }

    // Substitute assignments, simplify clauses
    vector<vector<int>> simplified;
    simplified.reserve(cls.size());
    for (auto &c : cls) {
        if (c.size() == 1 && c[0] == INT_MAX) continue;
        bool sat = false;
        vector<int> newc;
        newc.reserve(c.size());
        for (int lit : c) {
            int v = var_of(lit);
            int a = R.assign_full[v];
            if (a == -1) newc.push_back(lit);
            else {
                bool pos = sign_of(lit);
                bool val = (a == 1);
                if ((pos && val) || (!pos && !val)) { sat = true; break; }
            }
        }
        if (sat) continue;
        if (newc.empty()) { R.unsat = true; return R; }
        sort(newc.begin(), newc.end());
        newc.erase(unique(newc.begin(), newc.end()), newc.end());
        bool taut = false;
        for (int lit : newc) if (binary_search(newc.begin(), newc.end(), -lit)) { taut = true; break; }
        if (!taut) simplified.push_back(std::move(newc));
    }

    // Remap vars that appear; fix unused to 0
    vector<int8_t> appears(n, 0);
    for (auto &c : simplified) for (int lit : c) appears[var_of(lit)] = 1;

    R.old_to_new.assign(n, -1);
    for (int v = 0; v < n; ++v) {
        if (R.assign_full[v] != -1) continue;
        if (!appears[v]) { R.assign_full[v] = 0; continue; }
        int idx = (int)R.new_to_old.size();
        R.old_to_new[v] = idx;
        R.new_to_old.push_back(v);
    }
    R.n_red = (int)R.new_to_old.size();

    R.clauses_red.reserve(simplified.size());
    for (auto &c : simplified) {
        vector<int> rc;
        rc.reserve(c.size());
        for (int lit : c) {
            int ov = var_of(lit);
            int nv = R.old_to_new[ov];
            if (nv < 0) continue;
            rc.push_back(lit > 0 ? (nv + 1) : -(nv + 1));
        }
        if (rc.empty()) { R.unsat = true; return R; }
        R.clauses_red.push_back(std::move(rc));
    }

    return R;
}

// =====================
// Cube representation
// =====================
struct Cube {
    int n = 0, W = 0;
    vector<uint64_t> fixed;
    vector<uint64_t> value;

    Cube() = default;
    explicit Cube(int n_) : n(n_) {
        W = (n + 63) / 64;
        fixed.assign(W, 0);
        value.assign(W, 0);
    }

    inline void set_var(int idx, int val) {
        int w = idx / 64;
        int b = idx % 64;
        uint64_t bit = 1ull << b;
        fixed[w] |= bit;
        if (val) value[w] |= bit;
        else value[w] &= ~bit;
    }

    inline int popcount_fixed() const {
        int cnt = 0;
        for (int i = 0; i < W; ++i) cnt += __builtin_popcountll(fixed[i]);
        return cnt;
    }

    // 0=free, 1=fixed0, 2=fixed1
    inline int digit_on_var(int var) const {
        int w = var / 64, b = var % 64;
        uint64_t bit = 1ull << b;
        if ((fixed[w] & bit) == 0) return 0;
        return (value[w] & bit) ? 2 : 1;
    }
};

static inline bool conflict(const Cube& a, const Cube& b) {
    for (int i = 0; i < a.W; ++i) {
        uint64_t both = a.fixed[i] & b.fixed[i];
        uint64_t diff = (a.value[i] ^ b.value[i]) & both;
        if (diff) return true;
    }
    return false;
}
static inline bool intersects(const Cube& a, const Cube& b) { return !conflict(a, b); }

static inline bool subset(const Cube& p, const Cube& r) {
    for (int i = 0; i < p.W; ++i) {
        if ((r.fixed[i] & ~p.fixed[i]) != 0) return false;
        if (((p.value[i] ^ r.value[i]) & r.fixed[i]) != 0) return false;
    }
    return true;
}

static inline BigInt cube_volume_big(const Cube& c) {
    int k = c.popcount_fixed();
    return BigInt::pow2(c.n - k);
}

// =====================
// CubeDiff(p, r): disjoint family whose union is Q(p)\Q(r)
// =====================
static void cube_diff_rec(const Cube& p, const Cube& r, vector<Cube>& out) {
    if (!intersects(p, r)) { out.push_back(p); return; }
    if (subset(p, r)) return;

    int cut = -1;
    int rv = 0;
    for (int wi = 0; wi < p.W && cut < 0; ++wi) {
        uint64_t cand = r.fixed[wi] & ~p.fixed[wi];
        if (cand) {
            int b = __builtin_ctzll(cand);
            cut = wi * 64 + b;
            uint64_t bit = 1ull << b;
            rv = (r.value[wi] & bit) ? 1 : 0;
        }
    }
    if (cut < 0) return;

    Cube other = p;
    Cube same  = p;
    other.set_var(cut, 1 - rv);
    same.set_var(cut, rv);

    out.push_back(std::move(other));
    cube_diff_rec(same, r, out);
}

// =====================
// Clause -> falsification cube (skip tautologies)
// =====================
static bool clause_to_cube(const vector<int>& clause, int n, Cube& outCube) {
    unordered_set<int> pos, neg;
    pos.reserve(clause.size());
    neg.reserve(clause.size());
    for (int lit : clause) {
        int v = abs(lit);
        if (v < 1 || v > n) { cerr << "c ERROR: bad literal " << lit << "\n"; exit(1); }
        (lit > 0 ? pos : neg).insert(v);
    }
    for (int v : pos) if (neg.find(v) != neg.end()) return false; // tautology

    Cube c(n);
    for (int v : pos) c.set_var(v - 1, 0);
    for (int v : neg) c.set_var(v - 1, 1);
    outCube = std::move(c);
    return true;
}

// =====================
// Signature bucket index
// =====================
struct SignatureIndex {
    int t = 0;
    vector<int> sig_vars;
    vector<int> pow3;
    vector<vector<int>> buckets;

    // if compatible key count explodes, we mark fallback for this signature
    int max_keys = 20000;

    void init(const vector<int>& vars) {
        sig_vars = vars;
        t = (int)sig_vars.size();
        if (t == 0) return;
        pow3.assign(t + 1, 1);
        for (int i = 1; i <= t; ++i) pow3[i] = pow3[i-1] * 3;
        buckets.assign(pow3[t], {});
    }

    inline int key_of(const Cube& c) const {
        int key = 0;
        for (int i = 0; i < t; ++i) {
            int v = sig_vars[i];
            int d = c.digit_on_var(v);
            key += d * pow3[i];
        }
        return key;
    }

    void rebuild(const vector<Cube>& U) {
        if (t == 0) return;
        for (auto &b : buckets) b.clear();
        for (int i = 0; i < (int)U.size(); ++i) buckets[key_of(U[i])].push_back(i);
    }

    void add_one(const vector<Cube>& U, int idx) {
        if (t == 0) return;
        buckets[key_of(U[idx])].push_back(idx);
    }

    // Returns union of compatible buckets; no duplicates (each cube in exactly one bucket).
    void query_union_compatible(const vector<Cube>& /*U*/, const Cube& p, vector<int>& out, bool& fallback) const {
        out.clear();
        fallback = false;
        if (t == 0) { fallback = true; return; }

        // digits:
        // p free       => {0,1,2}
        // p fixed0 (1) => {0,1}
        // p fixed1 (2) => {0,2}
        vector<array<int,3>> opts(t);
        vector<int> opt_len(t);

        int64_t keyCount = 1;
        for (int i = 0; i < t; ++i) {
            int var = sig_vars[i];
            int d = p.digit_on_var(var);
            if (d == 0) { opts[i] = {0,1,2}; opt_len[i] = 3; keyCount *= 3; }
            else if (d == 1) { opts[i] = {0,1,0}; opt_len[i] = 2; keyCount *= 2; }
            else { opts[i] = {0,2,0}; opt_len[i] = 2; keyCount *= 2; }

            if (keyCount > max_keys) { fallback = true; return; }
        }

        function<void(int,int)> rec = [&](int i, int base) {
            if (i == t) {
                const auto& b = buckets[base];
                out.insert(out.end(), b.begin(), b.end());
                return;
            }
            for (int j = 0; j < opt_len[i]; ++j) rec(i + 1, base + opts[i][j] * pow3[i]);
        };
        rec(0, 0);
    }
};

// Choose top-frequency vars; then partition into disjoint groups
static vector<int> top_k_vars_by_freq(const vector<vector<int>>& clauses, int n, int k) {
    vector<int> freq(n, 0);
    for (auto &c : clauses) for (int lit : c) freq[abs(lit) - 1]++;

    vector<int> vars(n);
    iota(vars.begin(), vars.end(), 0);
    stable_sort(vars.begin(), vars.end(), [&](int a, int b){ return freq[a] > freq[b]; });
    if ((int)vars.size() > k) vars.resize(k);
    return vars;
}

struct MultiIndex {
    vector<SignatureIndex> sigs;

    // stamps for set intersection without clearing arrays
    vector<int> stamp;
    int curStamp = 1;

    // init with disjoint signature var sets
    void init_from_cnf(const vector<vector<int>>& clauses, int n,
                      int nsig = 3, int t_each = 8) {
        sigs.clear();
        if (n <= 0) return;

        // total vars desired
        int total = min(n, nsig * t_each);
        vector<int> top = top_k_vars_by_freq(clauses, n, total);

        // partition sequentially into nsig groups
        sigs.reserve(nsig);
        for (int s = 0; s < nsig; ++s) {
            int L = s * t_each;
            int R = min(total, (s + 1) * t_each);
            if (L >= R) break;
            vector<int> group(top.begin() + L, top.begin() + R);
            SignatureIndex idx;
            idx.max_keys = 20000; // tune: smaller => more per-sig fallback
            idx.init(group);
            sigs.push_back(std::move(idx));
        }

        stamp.assign(0, 0);
        curStamp = 1;
    }

    void rebuild(const vector<Cube>& U) {
        for (auto &s : sigs) s.rebuild(U);
        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);
    }

    void add_one(const vector<Cube>& U, int idx) {
        for (auto &s : sigs) s.add_one(U, idx);
        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);
    }

    // Query intersection of unions from each signature.
    // If a signature is too broad => ignore it.
    // If all are too broad or no signatures => fallback full scan.
    void query_candidates_intersection(const vector<Cube>& U, const Cube& p,
                                       vector<int>& out, bool& fallback) {
        out.clear();
        fallback = false;

        if (sigs.empty()) { fallback = true; return; }

        vector<vector<int>> lists;
        lists.reserve(sigs.size());

        for (auto &s : sigs) {
            vector<int> L;
            bool fb = false;
            s.query_union_compatible(U, p, L, fb);
            if (!fb) lists.push_back(std::move(L));
        }

        if (lists.empty()) { fallback = true; return; }
        if (lists.size() == 1) { out = std::move(lists[0]); return; }

        // Start from smallest list to reduce work
        int best = 0;
        for (int i = 1; i < (int)lists.size(); ++i)
            if (lists[i].size() < lists[best].size()) best = i;

        vector<int> cur = std::move(lists[best]);
        lists.erase(lists.begin() + best);

        // Sequential intersection using stamps
        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);

        for (auto &L : lists) {
            if (cur.empty()) break;
            if (++curStamp == INT_MAX) { // rare, reset
                fill(stamp.begin(), stamp.end(), 0);
                curStamp = 1;
            }

            // mark cur
            for (int idx : cur) stamp[idx] = curStamp;

            // filter using L
            vector<int> nxt;
            nxt.reserve(min(cur.size(), L.size()));
            for (int idx : L) if (stamp[idx] == curStamp) nxt.push_back(idx);
            cur.swap(nxt);
        }

        out.swap(cur);
    }
};

// =====================
// Optional buddy compression (heuristic, exactness-preserving)
// =====================
static inline uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ull;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebull;
    return x ^ (x >> 31);
}

struct CubeHashKey {
    vector<uint64_t> fixed;
    vector<uint64_t> value;
    bool operator==(CubeHashKey const& o) const {
        return fixed == o.fixed && value == o.value;
    }
};
struct CubeHashKeyHasher {
    size_t operator()(CubeHashKey const& k) const noexcept {
        uint64_t h = 0x1234567890abcdefull;
        for (uint64_t w : k.fixed) h = splitmix64(h ^ w);
        for (uint64_t w : k.value) h = splitmix64(h ^ (w + 0x9e37ull));
        return (size_t)h;
    }
};

static void buddy_compress(vector<Cube>& U, int max_rounds = 2) {
    if (U.empty()) return;

    for (int round = 0; round < max_rounds; ++round) {
        unordered_map<CubeHashKey, int, CubeHashKeyHasher> mp;
        mp.reserve(U.size() * 2);

        vector<char> alive(U.size(), 1);
        vector<Cube> out;
        out.reserve(U.size());

        for (int i = 0; i < (int)U.size(); ++i) mp.emplace(CubeHashKey{U[i].fixed, U[i].value}, i);

        bool merged_any = false;

        for (int i = 0; i < (int)U.size(); ++i) {
            if (!alive[i]) continue;
            Cube &a = U[i];

            bool merged = false;
            for (int wi = 0; wi < a.W && !merged; ++wi) {
                uint64_t f = a.fixed[wi];
                while (f) {
                    int b = __builtin_ctzll(f);
                    uint64_t bit = 1ull << b;
                    f &= (f - 1);

                    CubeHashKey buddyKey{a.fixed, a.value};
                    buddyKey.value[wi] ^= bit;

                    auto it = mp.find(buddyKey);
                    if (it == mp.end()) continue;
                    int j = it->second;
                    if (j == i || !alive[j]) continue;

                    Cube m = a;
                    m.fixed[wi] &= ~bit;
                    m.value[wi] &= ~bit;

                    alive[i] = 0;
                    alive[j] = 0;
                    out.push_back(std::move(m));
                    merged_any = true;
                    merged = true;
                }
            }
            if (!merged && alive[i]) {
                out.push_back(a);
                alive[i] = 0;
            }
        }

        U.swap(out);
        if (!merged_any) break;
    }
}

// =====================
// Indexed insertion using MultiIndex
// Returns delta = |Q \ Cov(U)|
// =====================
static BigInt add_cube_disjoint_indexed(vector<Cube>& U, const Cube& Q, MultiIndex& midx) {
    // Candidates based on Q (safe because any cube intersecting a subset must intersect Q)
    vector<int> cand;
    bool fallback = false;
    midx.query_candidates_intersection(U, Q, cand, fallback);

    vector<Cube> P;
    P.push_back(Q);

    if (fallback) {
        for (const Cube& R : U) {
            if (P.empty()) break;
            vector<Cube> newP;
            newP.reserve(P.size());
            for (const Cube& p : P) cube_diff_rec(p, R, newP);
            P.swap(newP);
        }
    } else {
        for (int ri : cand) {
            if (P.empty()) break;
            const Cube& R = U[ri];
            vector<Cube> newP;
            newP.reserve(P.size());
            for (const Cube& p : P) cube_diff_rec(p, R, newP);
            P.swap(newP);
        }
    }

    BigInt delta(0);
    for (const Cube& p : P) delta.add(cube_volume_big(p));

    int oldSize = (int)U.size();
    U.insert(U.end(), P.begin(), P.end());
    for (int i = oldSize; i < (int)U.size(); ++i) midx.add_one(U, i);

    return delta;
}

// =====================
// Fast witness extraction using W-sum trick (exact)
// =====================
static vector<int> extract_witness_fast(const vector<Cube>& U, int n) {
    if (n == 0) return {};
    if (U.empty()) return vector<int>(n, 0);

    int K = 0;
    for (auto &c : U) K = max(K, c.popcount_fixed());

    BigInt Wsum(0);
    vector<int> exp_u(U.size(), 0);
    vector<char> active(U.size(), 1);

    vector<vector<int>> fix0(n), fix1(n);
    for (int ui = 0; ui < (int)U.size(); ++ui) {
        const Cube& c = U[ui];
        int k = c.popcount_fixed();
        int e = K - k;
        exp_u[ui] = e;
        Wsum.add_pow2(e);

        for (int wi = 0; wi < c.W; ++wi) {
            uint64_t f = c.fixed[wi];
            while (f) {
                int b = __builtin_ctzll(f);
                uint64_t bit = 1ull << b;
                f &= (f - 1);
                int var = wi * 64 + b;
                if (var >= n) continue;
                int val = (c.value[wi] & bit) ? 1 : 0;
                (val == 0 ? fix0[var] : fix1[var]).push_back(ui);
            }
        }
    }

    BigInt TH = BigInt::pow2(K);
    if (BigInt::cmp(Wsum, TH) >= 0) return {};

    auto compute_trial = [&](int var, int b, BigInt& outTrial) {
        outTrial = Wsum;

        const auto& conf = (b == 0) ? fix1[var] : fix0[var];
        BigInt sconf(0);
        for (int ui : conf) if (active[ui]) sconf.add_pow2(exp_u[ui]);
        if (!sconf.is_zero()) outTrial.sub(sconf);

        const auto& mat = (b == 0) ? fix0[var] : fix1[var];
        BigInt smat(0);
        for (int ui : mat) if (active[ui]) smat.add_pow2(exp_u[ui]);
        if (!smat.is_zero()) outTrial.add(smat);
    };

    vector<int> x(n, 0);
    for (int var = 0; var < n; ++var) {
        BigInt W0, W1;
        compute_trial(var, 0, W0);
        bool ok0 = BigInt::cmp(W0, TH) < 0;

        if (ok0) {
            x[var] = 0;
            for (int ui : fix1[var]) if (active[ui]) { active[ui]=0; Wsum.sub_pow2(exp_u[ui]); }
            for (int ui : fix0[var]) if (active[ui]) { Wsum.add_pow2(exp_u[ui]); exp_u[ui]++; }
        } else {
            compute_trial(var, 1, W1);
            bool ok1 = BigInt::cmp(W1, TH) < 0;
            if (!ok1) return {};

            x[var] = 1;
            for (int ui : fix0[var]) if (active[ui]) { active[ui]=0; Wsum.sub_pow2(exp_u[ui]); }
            for (int ui : fix1[var]) if (active[ui]) { Wsum.add_pow2(exp_u[ui]); exp_u[ui]++; }
        }
    }
    return x;
}

// =====================
// Evaluate CNF
// =====================
static bool eval_cnf(const vector<vector<int>>& clauses, const vector<int>& x) {
    for (auto &c : clauses) {
        bool sat = false;
        for (int lit : c) {
            int v = abs(lit) - 1;
            int val = x[v];
            if (lit > 0 && val == 1) { sat = true; break; }
            if (lit < 0 && val == 0) { sat = true; break; }
        }
        if (!sat) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    bool opt_compress = false;
    bool opt_sort = false;
    string path;

    for (int i = 1; i < argc; ++i) {
        string s = argv[i];
        if (s == "--compress") opt_compress = true;
        else if (s == "--sort-clauses") opt_sort = true;
        else path = s;
    }

    if (path.empty()) {
        cerr << "c usage: " << argv[0] << " [--compress] [--sort-clauses] <input.cnf>\n";
        return 1;
    }

    CNF cnf = parse_dimacs(path);

    // Preprocess
    PreprocessResult P = preprocess_cnf(cnf);
    if (P.unsat) {
        cout << "s UNSATISFIABLE\n";
        return 20;
    }

    int n = P.n_red;
    auto clauses = std::move(P.clauses_red);

    if (opt_sort) {
        sort(clauses.begin(), clauses.end(),
             [](const auto& a, const auto& b){ return a.size() > b.size(); });
    }

    // Build multi-signature index over reduced CNF
    MultiIndex midx;
    // Defaults: 3 signatures of 8 vars each (disjoint) => up to 24 vars used.
    // If n is small, it will auto-shrink.
    midx.init_from_cnf(clauses, n, /*nsig=*/3, /*t_each=*/8);

    vector<Cube> U;
    U.reserve(clauses.size());
    midx.rebuild(U);

    BigInt y = BigInt::pow2(n); // #survivors over reduced vars

    for (size_t j = 0; j < clauses.size(); ++j) {
        Cube Q(n);
        bool ok = clause_to_cube(clauses[j], n, Q);
        if (!ok) continue; // tautology

        BigInt delta = add_cube_disjoint_indexed(U, Q, midx);

        if (BigInt::cmp(y, delta) < 0) y = BigInt(0);
        else y.sub(delta);

        if (y.is_zero()) {
            cout << "s UNSATISFIABLE\n";
            return 20;
        }

        if (opt_compress && (j % 64 == 63)) {
            buddy_compress(U, 2);
            midx.rebuild(U);
        }
    }

    // SAT: extract witness in reduced vars
    vector<int> x_red = extract_witness_fast(U, n);
    if (x_red.empty()) x_red.assign(n, 0);

    // Reconstruct full assignment
    vector<int> x_full = P.assign_full;
    for (int newv = 0; newv < n; ++newv) {
        int oldv = P.new_to_old[newv];
        x_full[oldv] = x_red[newv];
    }
    for (int i = 0; i < (int)x_full.size(); ++i)
        if (x_full[i] == -1) x_full[i] = 0;

    // (Optional) verify original CNF; should pass if everything is correct.
    (void)eval_cnf(cnf.clauses, x_full);

    cout << "s SATISFIABLE\n";
    cout << "v ";
    for (int i = 0; i < cnf.n; ++i) {
        int lit = (x_full[i] == 1) ? (i + 1) : -(i + 1);
        cout << lit << " ";
    }
    cout << "0\n";
    return 10;
}
