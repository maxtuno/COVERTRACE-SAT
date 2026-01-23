/*
Copyright (c) 2012–2026 Oscar Riveros

SATX is free software: you can redistribute it and/or modify it under the terms of the GNU Affero General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

SATX is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License along with this program. If not, see https://www.gnu.org/licenses/.

Commercial licensing options are available. See COMMERCIAL.md for details.
*/

// covertrace_sat_hybrid_interleaved.cpp
// Hybrid SAT solver: CDCL (standard heuristics) + interleaved CoverTrace UNSAT detector.
//
// Features (CDCL):
//  - 2-watched literals propagation
//  - 1-UIP conflict analysis and backjumping
//  - VSIDS variable activity + decay
//  - Phase saving
//  - Luby restarts
//  - LBD scoring (Glucose-style) + learned DB reduction
//  - Final model verification (never prints SAT with invalid assignment)
//
// Features (Interleaving):
//  - While CDCL runs, we continuously feed a filtered stream of *entailed clauses*
//    (learned clauses with low LBD / small size, plus optionally original clauses) into CoverTrace.
//  - If CoverTrace proves coverage of {0,1}^n, we can conclude UNSAT early.
//  - Optional: CoverTrace witness (when y>0) is used to set CDCL phase preferences.
//
// Build:
//   g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat_hybrid_interleaved.cpp -o covertrace_sat
//
// Run:
//   ./covertrace_sat --interleaved --ct-seed-original test.cnf
//   ./covertrace_sat --cdcl test.cnf
//   ./covertrace_sat --covertrace test.cnf
//
#include <bits/stdc++.h>
using namespace std;

// ============================================================
// DIMACS parser + model check
// ============================================================
struct CNF {
    int n = 0;
    vector<vector<int>> clauses; // each clause: DIMACS lits, no trailing 0
};

static CNF parse_dimacs(const string& path) {
    CNF cnf;
    ifstream in(path);
    if (!in) {
        cerr << "c ERROR: cannot open " << path << "\n";
        exit(1);
    }
    string tok;
    vector<int> cur;
    while (in >> tok) {
        if (tok.empty()) continue;
        if (tok[0] == 'c') { string rest; getline(in, rest); continue; }
        if (tok[0] == 'p') {
            string fmt; int m;
            in >> fmt >> cnf.n >> m;
            cnf.clauses.reserve((size_t)m);
            continue;
        }
        int lit = stoi(tok);
        if (lit == 0) {
            if (!cur.empty()) {
                cnf.clauses.push_back(cur);
            }
            cur.clear();
        } else {
            cur.push_back(lit);
        }
    }
    if (!cur.empty()) cnf.clauses.push_back(cur);
    sort(cnf.clauses.begin(), cnf.clauses.end(),  [] (auto &c1, auto &c2) { return c1.size() < c2.size(); });    
    return cnf;
}

static inline bool eval_clause(const vector<int>& c, const vector<int>& x01) {
    for (int lit : c) {
        int v = abs(lit) - 1;
        int val = x01[v];
        if (lit > 0) { if (val == 1) return true; }
        else { if (val == 0) return true; }
    }
    return false;
}

static bool eval_cnf(const CNF& cnf, const vector<int>& x01, int* first_bad = nullptr) {
    for (int i = 0; i < (int)cnf.clauses.size(); ++i) {
        if (!eval_clause(cnf.clauses[i], x01)) {
            if (first_bad) *first_bad = i;
            return false;
        }
    }
    return true;
}

// ============================================================
// BigInt (non-negative) base 2^32  -- operations needed by CoverTrace
// ============================================================
struct BigInt {
    vector<uint32_t> a; // little-endian limbs

    BigInt() = default;
    explicit BigInt(uint64_t x) { set_u64(x); }

    void normalize() { while (!a.empty() && a.back() == 0) a.pop_back(); }
    bool is_zero() const { return a.empty(); }

    void set_u64(uint64_t x) {
        a.clear();
        if (x == 0) return;
        a.push_back((uint32_t)(x & 0xFFFFFFFFu));
        uint32_t hi = (uint32_t)((x >> 32) & 0xFFFFFFFFu);
        if (hi) a.push_back(hi);
    }

    static BigInt pow2(int exp) {
        BigInt r;
        if (exp < 0) return r;
        int limb = exp / 32;
        int bit = exp % 32;
        r.a.assign((size_t)limb + 1, 0);
        r.a[(size_t)limb] = (1u << bit);
        return r;
    }

    static int cmp(const BigInt& x, const BigInt& y) {
        if (x.a.size() != y.a.size()) return x.a.size() < y.a.size() ? -1 : 1;
        for (int i = (int)x.a.size() - 1; i >= 0; --i) {
            if (x.a[(size_t)i] != y.a[(size_t)i]) return x.a[(size_t)i] < y.a[(size_t)i] ? -1 : 1;
        }
        return 0;
    }

    void add(const BigInt& b) {
        size_t n = max(a.size(), b.a.size());
        a.resize(n, 0);
        uint64_t carry = 0;
        for (size_t i = 0; i < n; ++i) {
            uint64_t s = (uint64_t)a[i] + (i < b.a.size() ? (uint64_t)b.a[i] : 0ull) + carry;
            a[i] = (uint32_t)(s & 0xFFFFFFFFu);
            carry = s >> 32;
        }
        if (carry) a.push_back((uint32_t)carry);
    }

    void sub(const BigInt& b) {
        // assumes *this >= b
        uint64_t borrow = 0;
        for (size_t i = 0; i < a.size(); ++i) {
            uint64_t bi = (i < b.a.size() ? b.a[i] : 0ull);
            uint64_t cur = (uint64_t)a[i];
            uint64_t need = bi + borrow;
            if (cur >= need) { a[i] = (uint32_t)(cur - need); borrow = 0; }
            else { a[i] = (uint32_t)((cur + (1ull << 32)) - need); borrow = 1; }
        }
        normalize();
    }

    // In-place add/sub of 2^exp (critical for speed)
    void add_pow2(int exp) {
        if (exp < 0) return;
        size_t limb = (size_t)(exp / 32);
        uint32_t bit = 1u << (exp % 32);
        if (a.size() <= limb) a.resize(limb + 1, 0);
        uint64_t s = (uint64_t)a[limb] + (uint64_t)bit;
        a[limb] = (uint32_t)(s & 0xFFFFFFFFu);
        uint64_t carry = s >> 32;
        for (size_t i = limb + 1; carry; ++i) {
            if (a.size() <= i) a.push_back(0);
            uint64_t t = (uint64_t)a[i] + carry;
            a[i] = (uint32_t)(t & 0xFFFFFFFFu);
            carry = t >> 32;
        }
    }

    void sub_pow2(int exp) {
        if (exp < 0) return;
        size_t limb = (size_t)(exp / 32);
        uint32_t bit = 1u << (exp % 32);
        // assumes *this >= 2^exp
        uint64_t cur = (uint64_t)a[limb];
        if (cur >= bit) {
            a[limb] = (uint32_t)(cur - bit);
        } else {
            a[limb] = (uint32_t)((cur + (1ull << 32)) - bit);
            for (size_t i = limb + 1;; ++i) {
                if (a[i] != 0) { a[i]--; break; }
                a[i] = 0xFFFFFFFFu;
            }
        }
        normalize();
    }
};

// ============================================================
// CoverTrace: disjoint forbidden subcubes + multi-signature index
// (based on your covertrace_sat_fast.cpp pieces, trimmed to essentials)
// ============================================================
struct Cube {
    int n = 0;
    int W = 0;
    vector<uint64_t> fixed; // bit=1 => var fixed
    vector<uint64_t> value; // bit => value for fixed vars

    Cube() = default;
    explicit Cube(int nvars) : n(nvars) {
        W = (n + 63) / 64;
        fixed.assign(W, 0);
        value.assign(W, 0);
    }

    inline void set_var(int v, int val01) {
        int wi = v >> 6;
        int bi = v & 63;
        uint64_t m = 1ull << bi;
        fixed[wi] |= m;
        if (val01) value[wi] |= m;
        else value[wi] &= ~m;
    }

    inline int popcount_fixed() const {
        int c = 0;
        for (uint64_t w : fixed) c += __builtin_popcountll(w);
        return c;
    }

    // digit in {0=free, 1=fixed0, 2=fixed1}
    inline int digit_on_var(int v) const {
        int wi = v >> 6;
        int bi = v & 63;
        uint64_t m = 1ull << bi;
        if ((fixed[wi] & m) == 0) return 0;
        return (value[wi] & m) ? 2 : 1;
    }
};

static inline bool intersects(const Cube& a, const Cube& b) {
    // conflict if some var fixed in both with different values
    for (int i = 0; i < a.W; ++i) {
        uint64_t both = a.fixed[i] & b.fixed[i];
        if (!both) continue;
        uint64_t diff = (a.value[i] ^ b.value[i]) & both;
        if (diff) return false;
    }
    return true;
}

static inline bool subset(const Cube& a, const Cube& b) {
    // a ⊆ b iff every fixed var in b is also fixed in a with same value?
    // Actually cube defines set of assignments satisfying its fixed constraints.
    // a ⊆ b means: b's constraints are weaker or equal. So every fixed var in b must be fixed in a with same value.
    for (int i = 0; i < a.W; ++i) {
        uint64_t fb = b.fixed[i];
        uint64_t missing = fb & ~a.fixed[i];
        if (missing) return false;
        uint64_t diff = (a.value[i] ^ b.value[i]) & fb;
        if (diff) return false;
    }
    return true;
}

static void cube_diff_rec(const Cube& p_in, const Cube& r, vector<Cube>& out) {
    Cube p = p_in;
    if (!intersects(p, r)) { out.push_back(std::move(p)); return; }
    if (subset(p, r)) return;

    while (true) {
        int cut = -1;
        int rv = 0;
        for (int wi = 0; wi < p.W && cut < 0; ++wi) {
            uint64_t cand = r.fixed[wi] & ~p.fixed[wi];
            if (cand) {
                int b = __builtin_ctzll(cand);
                cut = wi * 64 + b;
                rv = (r.value[wi] & (1ull << b)) ? 1 : 0;
            }
        }
        if (cut < 0) return;

        Cube other = p;
        other.set_var(cut, 1 - rv);
        out.push_back(std::move(other));

        p.set_var(cut, rv);
        if (subset(p, r)) return;
    }
}

static bool clause_to_cube(const vector<int>& clause, int n, Cube& outCube) {
    // falsification cube of clause; skip tautologies
    vector<int> lits = clause;
    for (int lit : lits) {
        int v = abs(lit);
        if (v < 1 || v > n) {
            cerr << "c ERROR: bad literal " << lit << "\n";
            exit(1);
        }
    }
    sort(lits.begin(), lits.end(), [](int a, int b) {
        int va = abs(a), vb = abs(b);
        if (va != vb) return va < vb;
        return a < b;
    });

    Cube c(n);
    for (size_t i = 0; i < lits.size();) {
        int v = abs(lits[i]);
        bool has_neg = false, has_pos = false;
        while (i < lits.size() && abs(lits[i]) == v) {
            if (lits[i] > 0) has_pos = true;
            else has_neg = true;
            ++i;
        }
        if (has_pos && has_neg) return false; // tautology
        if (has_pos) c.set_var(v - 1, 0);
        else if (has_neg) c.set_var(v - 1, 1);
    }

    outCube = std::move(c);
    return true;
}

struct SignatureIndex {
    int t = 0;
    vector<int> sig_vars;
    vector<int> pow3;
    vector<vector<int>> buckets;
    int max_keys = 20000;

    void init(const vector<int>& vars) {
        sig_vars = vars;
        t = (int)sig_vars.size();
        if (t == 0) return;
        pow3.assign(t + 1, 1);
        for (int i = 1; i <= t; ++i) pow3[i] = pow3[i - 1] * 3;
        buckets.assign((size_t)pow3[t], {});
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
        for (auto& b : buckets) b.clear();
        for (int i = 0; i < (int)U.size(); ++i) buckets[(size_t)key_of(U[i])].push_back(i);
    }

    void add_one(const vector<Cube>& U, int idx) {
        if (t == 0) return;
        buckets[(size_t)key_of(U[(size_t)idx])].push_back(idx);
    }

    void query_union_compatible(const Cube& p, vector<int>& out, bool& fallback) const {
        out.clear();
        fallback = false;
        if (t == 0) { fallback = true; return; }

        vector<array<int,3>> opts((size_t)t);
        vector<int> opt_len((size_t)t);

        long long keyCount = 1;
        for (int i = 0; i < t; ++i) {
            int var = sig_vars[i];
            int d = p.digit_on_var(var);
            if (d == 0) { opts[(size_t)i] = {0, 1, 2}; opt_len[(size_t)i] = 3; keyCount *= 3; }
            else if (d == 1) { opts[(size_t)i] = {0, 1, 0}; opt_len[(size_t)i] = 2; keyCount *= 2; }
            else { opts[(size_t)i] = {0, 2, 0}; opt_len[(size_t)i] = 2; keyCount *= 2; }
            if (keyCount > max_keys) { fallback = true; return; }
        }

        function<void(int,int)> rec = [&](int i, int base) {
            if (i == t) {
                const auto& b = buckets[(size_t)base];
                out.insert(out.end(), b.begin(), b.end());
                return;
            }
            for (int j = 0; j < opt_len[(size_t)i]; ++j) rec(i + 1, base + opts[(size_t)i][(size_t)j] * pow3[(size_t)i]);
        };
        rec(0, 0);
    }
};

static vector<int> top_k_vars_by_freq(const vector<vector<int>>& clauses, int n, int k) {
    vector<int> freq((size_t)n, 0);
    for (auto& c : clauses) for (int lit : c) freq[(size_t)(abs(lit) - 1)]++;
    vector<int> vars((size_t)n);
    iota(vars.begin(), vars.end(), 0);
    stable_sort(vars.begin(), vars.end(), [&](int a, int b){ return freq[(size_t)a] > freq[(size_t)b]; });
    if ((int)vars.size() > k) vars.resize((size_t)k);
    return vars;
}

struct MultiIndex {
    vector<SignatureIndex> sigs;
    vector<int> stamp;
    int curStamp = 1;

    void init_from_cnf(const vector<vector<int>>& clauses, int n, int nsig = 3, int t_each = 8) {
        sigs.clear();
        if (n <= 0) return;
        int total = min(n, nsig * t_each);
        vector<int> top = top_k_vars_by_freq(clauses, n, total);
        sigs.reserve((size_t)nsig);
        for (int s = 0; s < nsig; ++s) {
            int L = s * t_each;
            int R = min(total, (s + 1) * t_each);
            if (L >= R) break;
            vector<int> group(top.begin() + L, top.begin() + R);
            SignatureIndex idx;
            idx.max_keys = 20000;
            idx.init(group);
            sigs.push_back(std::move(idx));
        }
        stamp.clear();
        curStamp = 1;
    }

    void rebuild(const vector<Cube>& U) {
        for (auto& s : sigs) s.rebuild(U);
        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);
    }

    void add_one(const vector<Cube>& U, int idx) {
        for (auto& s : sigs) s.add_one(U, idx);
        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);
    }

    void query_candidates_intersection(const vector<Cube>& U, const Cube& p, vector<int>& out, bool& fallback) {
        out.clear();
        fallback = false;
        if (sigs.empty()) { fallback = true; return; }

        vector<vector<int>> lists;
        lists.reserve(sigs.size());
        for (auto& s : sigs) {
            vector<int> L;
            bool fb = false;
            s.query_union_compatible(p, L, fb);
            if (!fb) lists.push_back(std::move(L));
        }
        if (lists.empty()) { fallback = true; return; }
        if (lists.size() == 1) { out = std::move(lists[0]); return; }

        int best = 0;
        for (int i = 1; i < (int)lists.size(); ++i) if (lists[(size_t)i].size() < lists[(size_t)best].size()) best = i;
        vector<int> cur = std::move(lists[(size_t)best]);
        lists.erase(lists.begin() + best);

        if ((int)stamp.size() < (int)U.size()) stamp.resize(U.size(), 0);

        for (auto& L : lists) {
            if (cur.empty()) break;
            if (++curStamp == INT_MAX) { fill(stamp.begin(), stamp.end(), 0); curStamp = 1; }
            for (int idx : cur) stamp[(size_t)idx] = curStamp;
            vector<int> nxt;
            nxt.reserve(min(cur.size(), L.size()));
            for (int idx : L) if (stamp[(size_t)idx] == curStamp) nxt.push_back(idx);
            cur.swap(nxt);
        }
        out.swap(cur);
    }
};

static BigInt add_cube_disjoint_indexed(vector<Cube>& U, const Cube& Q, MultiIndex& midx) {
    vector<int> cand;
    bool fallback = false;
    midx.query_candidates_intersection(U, Q, cand, fallback);

    if (!fallback) {
        size_t wr = 0;
        for (int ri : cand) {
            if (intersects(U[(size_t)ri], Q)) cand[wr++] = ri;
        }
        cand.resize(wr);
        for (int ri : cand) {
            if (subset(Q, U[(size_t)ri])) return BigInt(0);
        }
    }

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
            const Cube& R = U[(size_t)ri];
            vector<Cube> newP;
            newP.reserve(P.size());
            for (const Cube& p : P) cube_diff_rec(p, R, newP);
            P.swap(newP);
        }
    }

    BigInt delta(0);
    for (const Cube& p : P) delta.add_pow2(p.n - p.popcount_fixed());

    int oldSize = (int)U.size();
    U.insert(U.end(), P.begin(), P.end());
    for (int i = oldSize; i < (int)U.size(); ++i) midx.add_one(U, i);

    return delta;
}

static vector<int> extract_witness_fast(const vector<Cube>& U, int n) {
    if (n == 0) return {};
    if (U.empty()) return vector<int>((size_t)n, 0);

    int K = 0;
    for (const auto& c : U) K = max(K, c.popcount_fixed());

    BigInt Wsum(0);
    vector<int> exp_u(U.size(), 0);
    vector<char> active(U.size(), 1);

    vector<vector<int>> fix0((size_t)n), fix1((size_t)n);
    for (int ui = 0; ui < (int)U.size(); ++ui) {
        const Cube& c = U[(size_t)ui];
        int k = c.popcount_fixed();
        int e = K - k;
        exp_u[(size_t)ui] = e;
        Wsum.add_pow2(e);

        for (int wi = 0; wi < c.W; ++wi) {
            uint64_t f = c.fixed[(size_t)wi];
            while (f) {
                int b = __builtin_ctzll(f);
                uint64_t bit = 1ull << b;
                f &= (f - 1);
                int var = wi * 64 + b;
                if (var >= n) continue;
                int val = (c.value[(size_t)wi] & bit) ? 1 : 0;
                (val == 0 ? fix0[(size_t)var] : fix1[(size_t)var]).push_back(ui);
            }
        }
    }

    BigInt TH = BigInt::pow2(K);
    if (BigInt::cmp(Wsum, TH) >= 0) return {};

    auto compute_trial = [&](int var, int b, BigInt& outTrial) {
        outTrial = Wsum;

        const auto& conf = (b == 0) ? fix1[(size_t)var] : fix0[(size_t)var];
        BigInt sconf(0);
        for (int ui : conf) if (active[(size_t)ui]) sconf.add_pow2(exp_u[(size_t)ui]);
        if (!sconf.is_zero()) outTrial.sub(sconf);

        const auto& mat = (b == 0) ? fix0[(size_t)var] : fix1[(size_t)var];
        BigInt smat(0);
        for (int ui : mat) if (active[(size_t)ui]) smat.add_pow2(exp_u[(size_t)ui]);
        if (!smat.is_zero()) outTrial.add(smat);
    };

    vector<int> x((size_t)n, 0);
    for (int var = 0; var < n; ++var) {
        BigInt W0, W1;
        compute_trial(var, 0, W0);
        bool ok0 = BigInt::cmp(W0, TH) < 0;
        if (ok0) {
            x[(size_t)var] = 0;
            for (int ui : fix1[(size_t)var]) if (active[(size_t)ui]) { active[(size_t)ui]=0; Wsum.sub_pow2(exp_u[(size_t)ui]); }
            for (int ui : fix0[(size_t)var]) if (active[(size_t)ui]) { Wsum.add_pow2(exp_u[(size_t)ui]); exp_u[(size_t)ui]++; }
        } else {
            compute_trial(var, 1, W1);
            bool ok1 = BigInt::cmp(W1, TH) < 0;
            if (!ok1) return {};
            x[(size_t)var] = 1;
            for (int ui : fix0[(size_t)var]) if (active[(size_t)ui]) { active[(size_t)ui]=0; Wsum.sub_pow2(exp_u[(size_t)ui]); }
            for (int ui : fix1[(size_t)var]) if (active[(size_t)ui]) { Wsum.add_pow2(exp_u[(size_t)ui]); exp_u[(size_t)ui]++; }
        }
    }

    return x;
}

struct CoverTrace {
    int n = 0;
    vector<Cube> U;  // disjoint forbidden cubes
    BigInt y;        // remaining measure
    MultiIndex midx;

    explicit CoverTrace(int nvars, const vector<vector<int>>& cnf_clauses)
        : n(nvars), y(BigInt::pow2(nvars)) {
        midx.init_from_cnf(cnf_clauses, nvars);
        midx.rebuild(U);
    }

    // feed a DIMACS clause; returns true if UNSAT proven (y==0)
    bool feed_clause(const vector<int>& clause) {
        Cube Q;
        if (!clause_to_cube(clause, n, Q)) return false; // tautology
        BigInt delta = add_cube_disjoint_indexed(U, Q, midx);
        if (!delta.is_zero()) {
            if (BigInt::cmp(y, delta) >= 0) y.sub(delta);
            else y.set_u64(0);
        }
        return y.is_zero();
    }

    bool is_unsat() const { return y.is_zero(); }

    // produce a candidate assignment avoiding current forbidden cubes (if any exists)
    vector<int> witness01() const {
        if (is_unsat()) return {};
        return extract_witness_fast(U, n);
    }
};

// ============================================================
// CDCL Solver (MiniSat-like core)
// ============================================================
using Lit = int;
static inline int var(Lit p) { return p >> 1; }
static inline int sign(Lit p) { return p & 1; }
static inline Lit mkLit(int v, int s) { return (v << 1) | (s & 1); }
static inline Lit neg(Lit p) { return p ^ 1; }

struct Watcher { int cref; Lit blocker; };

struct Clause {
    vector<Lit> lits;
    bool learnt = false;
    bool deleted = false;
    int lbd = 0;
    float activity = 0.0f;
};

struct VarOrder {
    vector<int> heap;       // vars
    vector<int> pos;        // pos[var] or -1
    vector<double>* act = nullptr;

    explicit VarOrder(int n = 0, vector<double>* a = nullptr) { init(n, a); }

    void init(int n, vector<double>* a) {
        act = a;
        heap.clear(); heap.reserve((size_t)n);
        pos.assign((size_t)n, -1);
    }

    bool inHeap(int v) const { return pos[(size_t)v] >= 0; }

    bool better(int v, int u) const {
        return (*act)[(size_t)v] > (*act)[(size_t)u];
    }

    void siftUp(int i) {
        while (i > 0) {
            int p = (i - 1) >> 1;
            if (!better(heap[(size_t)i], heap[(size_t)p])) break;
            swap(heap[(size_t)i], heap[(size_t)p]);
            pos[(size_t)heap[(size_t)i]] = i;
            pos[(size_t)heap[(size_t)p]] = p;
            i = p;
        }
    }

    void siftDown(int i) {
        int n = (int)heap.size();
        while (true) {
            int l = (i << 1) + 1;
            int r = l + 1;
            int best = i;
            if (l < n && better(heap[(size_t)l], heap[(size_t)best])) best = l;
            if (r < n && better(heap[(size_t)r], heap[(size_t)best])) best = r;
            if (best == i) break;
            swap(heap[(size_t)i], heap[(size_t)best]);
            pos[(size_t)heap[(size_t)i]] = i;
            pos[(size_t)heap[(size_t)best]] = best;
            i = best;
        }
    }

    void insert(int v) {
        if (inHeap(v)) return;
        pos[(size_t)v] = (int)heap.size();
        heap.push_back(v);
        siftUp((int)heap.size() - 1);
    }

    int removeMax() {
        if (heap.empty()) return -1;
        int v = heap[0];
        int last = heap.back();
        heap.pop_back();
        pos[(size_t)v] = -1;
        if (!heap.empty()) {
            heap[0] = last;
            pos[(size_t)last] = 0;
            siftDown(0);
        }
        return v;
    }

    void update(int v) {
        int i = pos[(size_t)v];
        if (i < 0) return;
        siftUp(i);
        siftDown(i);
    }
};

struct CDCLSolver {
    int n = 0;

    vector<Clause> clauses;           // original + learned
    vector<vector<Watcher>> watches;  // size 2*n; indexed by literal p that becomes TRUE

    vector<int8_t> assigns; // -1 false, 0 undef, 1 true
    vector<int> level;
    vector<int> reason;     // clause index or -1

    vector<Lit> trail;
    vector<int> trail_lim;
    int qhead = 0;

    // heuristics
    vector<double> var_act;
    double var_inc = 1.0;
    double var_decay = 0.95;

    vector<uint8_t> polarity; // preferred value for var (1 => true)

    vector<int> learnt_ids;
    float cla_inc = 1.0f;
    float cla_decay = 0.999f;

    VarOrder order;

    // interleaving hooks
    CoverTrace* ct = nullptr;
    const CNF* orig_cnf = nullptr;
    bool ct_seed_original = false;
    int ct_every = 2000;
    int ct_batch = 256;
    int ct_lbd_max = 6;
    int ct_maxlen = 12;
    int ct_witness_phase_every = 5000; // use witness to set phases
    size_t ct_maxU = 400000;

    deque<int> ct_queue; // clause indices to feed
    int next_orig_clause = 0;

    // stats
    long long conflicts = 0;
    long long decisions = 0;
    long long propagations = 0;

    bool debug = false;

    explicit CDCLSolver(int nvars) : n(nvars) {
        watches.assign((size_t)(2*n), {});
        assigns.assign((size_t)n, 0);
        level.assign((size_t)n, 0);
        reason.assign((size_t)n, -1);
        var_act.assign((size_t)n, 0.0);
        polarity.assign((size_t)n, 1);
        order.init(n, &var_act);
        for (int v = 0; v < n; ++v) order.insert(v);
    }

    inline int valueLit(Lit p) const {
        int v = var(p);
        int8_t a = assigns[(size_t)v];
        if (a == 0) return 0;
        // literal is true if var value != sign
        bool var_true = (a == 1);
        bool lit_true = (var_true != (bool)sign(p));
        return lit_true ? 1 : -1;
    }

    inline int decisionLevel() const { return (int)trail_lim.size(); }

    void newDecisionLevel() { trail_lim.push_back((int)trail.size()); }

    bool enqueue(Lit p, int from) {
        int v = var(p);
        int8_t need = sign(p) ? -1 : 1;
        int8_t cur = assigns[(size_t)v];
        if (cur != 0) return cur == need;
        assigns[(size_t)v] = need;
        level[(size_t)v] = decisionLevel();
        reason[(size_t)v] = from;
        polarity[(size_t)v] = (need == 1) ? 1 : 0; // phase saving
        trail.push_back(p);
        return true;
    }

    void cancelUntil(int lvl) {
        if (decisionLevel() <= lvl) return;
        // trail_lim[i] stores the trail index where decision level (i+1) starts.
        // To backtrack to level `lvl`, keep assignments up to the start of level (lvl+1).
        // For lvl==0, keep root-level assignments (trail indices < trail_lim[0]) if any.
        int lim = 0;
        if (lvl == 0) {
            if (!trail_lim.empty()) lim = trail_lim[0];
        } else {
            lim = trail_lim[(size_t)lvl];
        }
        for (int i = (int)trail.size() - 1; i >= lim; --i) {
            int v = var(trail[(size_t)i]);
            assigns[(size_t)v] = 0;
            reason[(size_t)v] = -1;
            level[(size_t)v] = 0;
            order.insert(v);
        }
        trail.resize((size_t)lim);
        trail_lim.resize((size_t)lvl);
        qhead = min(qhead, (int)trail.size());
    }

    static inline int litToDimacs(Lit p) {
        int v = var(p) + 1;
        return sign(p) ? -v : v;
    }

    void dump_clause(int ci, ostream& os = cerr) const {
        if (ci < 0 || ci >= (int)clauses.size()) {
            os << "c clause[" << ci << "] <invalid>\n";
            return;
        }
        const Clause& c = clauses[(size_t)ci];
        os << "c clause[" << ci << "]" << (c.deleted ? " (deleted)" : "") << " :";
        for (Lit p : c.lits) os << ' ' << litToDimacs(p);
        os << " 0\n";
    }

    void dump_trail(ostream& os = cerr) const {
        os << "c trail size=" << trail.size() << " qhead=" << qhead
           << " dl=" << decisionLevel() << "\n";
        for (size_t i = 0; i < trail.size(); ++i) {
            Lit p = trail[i];
            int v = var(p);
            os << "c  #" << i
               << " lit=" << litToDimacs(p)
               << " lvl=" << level[(size_t)v]
               << " reason=" << reason[(size_t)v]
               << "\n";
        }
    }

    bool clause_falsified(int ci) const {
        if (ci < 0 || ci >= (int)clauses.size()) return false;
        const Clause& c = clauses[(size_t)ci];
        if (c.deleted) return false;
        for (Lit p : c.lits) {
            int v = valueLit(p);
            if (v != -1) return false;
        }
        return true;
    }

    void attachClause(int ci) {
        Clause& c = clauses[(size_t)ci];
        if (c.deleted) return;
        if (c.lits.size() == 1) {
            // Watch unit as usual: store under neg(l) so it is processed when l becomes false.
            watches[(size_t)neg(c.lits[0])].push_back({ci, c.lits[0]});
        } else {
            // MiniSat scheme: store watchers under neg(watched)
            watches[(size_t)neg(c.lits[0])].push_back({ci, c.lits[1]});
            watches[(size_t)neg(c.lits[1])].push_back({ci, c.lits[0]});
        }
    }

    void varBump(int v) {
        var_act[(size_t)v] += var_inc;
        if (var_act[(size_t)v] > 1e100) {
            for (double& x : var_act) x *= 1e-100;
            var_inc *= 1e-100;
        }
        order.update(v);
    }

    void varDecay() { var_inc *= (1.0 / var_decay); }

    void claBump(int ci) {
        Clause& c = clauses[(size_t)ci];
        c.activity += cla_inc;
        if (c.activity > 1e20f) {
            for (int id : learnt_ids) if (!clauses[(size_t)id].deleted) clauses[(size_t)id].activity *= 1e-20f;
            cla_inc *= 1e-20f;
        }
    }

    void claDecay() { cla_inc *= (1.0f / cla_decay); }

    static int compute_lbd(const vector<Lit>& lits, const vector<int>& level) {
        vector<int> ls;
        ls.reserve(lits.size());
        for (Lit p : lits) {
            int lv = level[(size_t)var(p)];
            if (lv > 0) ls.push_back(lv);
        }
        sort(ls.begin(), ls.end());
        ls.erase(unique(ls.begin(), ls.end()), ls.end());
        return (int)ls.size();
    }

    // propagate; returns conflict clause index or -1
    int propagate() {
        while (qhead < (int)trail.size()) {
            Lit p = trail[(size_t)qhead++];
            auto& ws = watches[(size_t)p];
            int i = 0, j = 0;
            propagations++;

            while (i < (int)ws.size()) {
                Watcher w = ws[(size_t)i++];
                int ci = w.cref;
                if (ci < 0 || ci >= (int)clauses.size()) continue;
                Clause& c = clauses[(size_t)ci];
                if (c.deleted) continue;

                // if blocker literal is true, clause satisfied
                if (valueLit(w.blocker) == 1) {
                    ws[(size_t)j++] = w;
                    continue;
                }

                // Find the false literal (the watched one whose negation is p)
                Lit false_lit = neg(p);

                // ensure c.lits[0] is false_lit
                if (c.lits.size() == 1) {
                    // unit clause violated if its lit is false
                    if (valueLit(c.lits[0]) == -1) {
                        // keep remaining watches
                        ws[(size_t)j++] = w;
                        while (i < (int)ws.size()) ws[(size_t)j++] = ws[(size_t)i++];
                        ws.resize((size_t)j);
                        return ci;
                    }
                    ws[(size_t)j++] = w;
                    continue;
                }

                if (c.lits[0] != false_lit) {
                    // swap if second matches
                    if (c.lits[1] == false_lit) swap(c.lits[0], c.lits[1]);
                    else {
                        // stale watch (should be rare). Keep it safe.
                        ws[(size_t)j++] = w;
                        continue;
                    }
                }

                Lit other = c.lits[1];
                if (valueLit(other) == 1) {
                    ws[(size_t)j++] = {ci, other};
                    continue;
                }

                // search new watch
                bool found = false;
                for (size_t k = 2; k < c.lits.size(); ++k) {
                    Lit q = c.lits[k];
                    if (valueLit(q) != -1) {
                        // move watch from false_lit to q
                        c.lits[0] = q;
                        c.lits[k] = false_lit;
                        watches[(size_t)neg(q)].push_back({ci, other});
                        found = true;
                        break;
                    }
                }
                if (found) continue;

                // no replacement => unit or conflict
                ws[(size_t)j++] = {ci, other};
                if (valueLit(other) == -1) {
                    while (i < (int)ws.size()) ws[(size_t)j++] = ws[(size_t)i++];
                    ws.resize((size_t)j);
#ifndef NDEBUG
                    if (!clause_falsified(ci)) {
                        cerr << "c ASSERT: conflict clause not falsified (propagate)\n";
                        dump_clause(ci);
                        dump_trail();
                        assert(false);
                    }
#endif
                    return ci;
                }
                if (!enqueue(other, ci)) {
                    while (i < (int)ws.size()) ws[(size_t)j++] = ws[(size_t)i++];
                    ws.resize((size_t)j);
#ifndef NDEBUG
                    if (!clause_falsified(ci)) {
                        cerr << "c ASSERT: conflict clause not falsified (enqueue)\n";
                        dump_clause(ci);
                        dump_trail();
                        assert(false);
                    }
#endif
                    return ci;
                }
            }
            ws.resize((size_t)j);
        }
        return -1;
    }

    // add clause from internal lits; returns false if contradiction at level 0.
    // If out_ci is provided, it will be set to the new clause index, or -1 if the clause was ignored
    // (tautology / already satisfied) or handled as a unit at level 0.
    bool addClauseInternal(vector<Lit> lits, bool learnt = false, int lbd = 0, int* out_ci = nullptr) {
        if (out_ci) *out_ci = -1;
        if (lits.empty()) return false;

        // Learned clauses rely on lits[0] being the asserting literal (used for enqueue and as a watched lit).
        // Keep track of it through simplification/reordering.
        Lit asserting = -1;
        if (learnt) asserting = lits[0];

        sort(lits.begin(), lits.end());
        lits.erase(unique(lits.begin(), lits.end()), lits.end());
        for (Lit p : lits) {
            if (binary_search(lits.begin(), lits.end(), neg(p))) return true; // tautology
        }

        if (decisionLevel() == 0) {
            vector<Lit> tmp;
            tmp.reserve(lits.size());
            for (Lit p : lits) {
                int v = valueLit(p);
                if (v == 1) return true;
                if (v == 0) tmp.push_back(p);
            }
            lits.swap(tmp);
            if (lits.empty()) return false;
            if (lits.size() == 1) {
                if (!enqueue(lits[0], -1)) return false;
                int confl = propagate();
                return confl == -1;
            }
        }

        if (learnt && lits.size() > 1) {
            // Ensure asserting literal is at position 0 (do this before attachClause uses lits[0]/lits[1]).
            auto it = find(lits.begin(), lits.end(), asserting);
            if (it != lits.end()) swap(lits[0], *it);

            // For better propagation, put the highest decision-level literal (excluding the asserting one) at pos 1.
            size_t best = 1;
            int best_lv = level[(size_t)var(lits[1])];
            for (size_t i = 2; i < lits.size(); ++i) {
                int lv = level[(size_t)var(lits[i])];
                if (lv > best_lv) { best_lv = lv; best = i; }
            }
            swap(lits[1], lits[best]);
        }

        Clause c;
        c.lits = std::move(lits);
        c.learnt = learnt;
        c.lbd = lbd;
        int ci = (int)clauses.size();
        clauses.push_back(std::move(c));
        attachClause(ci);
        if (learnt) learnt_ids.push_back(ci);
        if (out_ci) *out_ci = ci;
        return true;
    }

    bool addClauseDimacs(const vector<int>& dimacs, bool learnt = false, int lbd = 0) {
        vector<Lit> lits;
        lits.reserve(dimacs.size());
        for (int x : dimacs) {
            int v = abs(x);
            if (v < 1 || v > n) {
                cerr << "c ERROR: literal out of range in clause\n";
                exit(1);
            }
            int vv = v - 1;
            bool negs = (x < 0);
            lits.push_back(mkLit(vv, negs ? 1 : 0));
        }
        return addClauseInternal(std::move(lits), learnt, lbd);
    }

    // conflict analysis: 1-UIP
    void analyze(int confl, vector<Lit>& out_learnt, int& out_btlevel, int& out_lbd) {
        out_learnt.clear();
        out_learnt.push_back(-1);

        vector<uint8_t> seen((size_t)n, 0);
        int pathC = 0;
        Lit p = -1;
        int idx = (int)trail.size() - 1;

        auto bumpClauseVars = [&](int ci, Lit skip) {
            Clause& c = clauses[(size_t)ci];
            if (c.learnt) claBump(ci);
            for (Lit q : c.lits) {
                if (q == skip) continue;
                int v = var(q);
                if (!seen[(size_t)v] && level[(size_t)v] > 0) {
                    seen[(size_t)v] = 1;
                    varBump(v);
                    if (level[(size_t)v] == decisionLevel()) pathC++;
                    else out_learnt.push_back(q);
                }
            }
        };

        bumpClauseVars(confl, -1);

        while (true) {
            // select last assigned seen var
            while (idx >= 0) {
                Lit q = trail[(size_t)idx--];
                if (seen[(size_t)var(q)]) { p = q; break; }
            }
            int vp = var(p);
            seen[(size_t)vp] = 0;
            pathC--;
            int r = reason[(size_t)vp];
            if (pathC <= 0) {
                out_learnt[0] = neg(p);
                break;
            }
            if (r != -1) bumpClauseVars(r, p);
            // if r == -1 (decision), loop continues and will break when pathC hits 0
        }

        out_btlevel = 0;
        for (size_t i = 1; i < out_learnt.size(); ++i) out_btlevel = max(out_btlevel, level[(size_t)var(out_learnt[i])]);
        out_lbd = compute_lbd(out_learnt, level);
    }

    bool locked(int ci) const {
        const Clause& c = clauses[(size_t)ci];
        if (c.deleted || c.lits.empty()) return false;
        // A clause is locked if it is currently the reason for any assigned variable.
        // Do not assume the implied literal is stored at a fixed position.
        for (Lit p : c.lits) {
            int v = var(p);
            if (reason[(size_t)v] == ci) return true;
        }
        return false;
    }

    void reduceDB() {
        // keep binaries + locked + low lbd
        vector<int> cand;
        cand.reserve(learnt_ids.size());
        for (int ci : learnt_ids) {
            Clause& c = clauses[(size_t)ci];
            if (c.deleted) continue;
            if (c.lits.size() <= 2) continue;
            if (locked(ci)) continue;
            cand.push_back(ci);
        }
        if (cand.size() < 500) return;

        sort(cand.begin(), cand.end(), [&](int a, int b) {
            const Clause& A = clauses[(size_t)a];
            const Clause& B = clauses[(size_t)b];
            if (A.lbd != B.lbd) return A.lbd > B.lbd; // delete higher lbd first
            return A.activity < B.activity;          // and low activity
        });

        size_t to_del = cand.size() / 2;
        for (size_t i = 0; i < to_del; ++i) {
            Clause& c = clauses[(size_t)cand[i]];
            c.deleted = true;
            // Release memory aggressively (we never physically compact clause indices).
            vector<Lit>().swap(c.lits);
        }
    }

    Lit pickBranchLit() {
        int v;
        while ((v = order.removeMax()) != -1) {
            if (assigns[(size_t)v] == 0) {
                decisions++;
                bool pref_true = polarity[(size_t)v] != 0;
                return mkLit(v, pref_true ? 0 : 1);
            }
        }
        return -1;
    }

    // Luby sequence (1,1,2,1,1,2,4,...)
    static long long luby(long long y, int x) {
        int size = 1;
        int seq = 0;
        while (size < x + 1) { seq++; size = 2 * size + 1; }
        while (size - 1 != x) { size = (size - 1) >> 1; seq--; x = x % size; }
        long long res = 1;
        for (int i = 0; i < seq; ++i) res *= y;
        return res;
    }

    bool covertrace_tick() {
        if (!ct || !orig_cnf) return false;
        if (ct->U.size() > ct_maxU) return false;

        int fed = 0;

        // seed original clauses gradually
        if (ct_seed_original) {
            while (fed < ct_batch / 2 && next_orig_clause < (int)orig_cnf->clauses.size()) {
                if (ct->feed_clause(orig_cnf->clauses[(size_t)next_orig_clause++])) return true;
                if (ct->U.size() > ct_maxU) return false;
                fed++;
            }
        }

        // feed learned clauses from queue
        while (fed < ct_batch && !ct_queue.empty()) {
            int ci = ct_queue.front();
            ct_queue.pop_front();
            if (ci < 0 || ci >= (int)clauses.size()) continue;
            const Clause& c = clauses[(size_t)ci];
            if (c.deleted) continue;

            // convert to DIMACS lits to feed CoverTrace
            vector<int> dim;
            dim.reserve(c.lits.size());
            for (Lit p : c.lits) {
                int v = var(p) + 1;
                int dlit = sign(p) ? -v : v;
                dim.push_back(dlit);
            }

            if (ct->feed_clause(dim)) return true;
            if (ct->U.size() > ct_maxU) return false;
            fed++;
        }

        // feed witness -> phases
        if (ct_witness_phase_every > 0 && (conflicts % ct_witness_phase_every == 0) && !ct->is_unsat()) {
            vector<int> w = ct->witness01();
            if ((int)w.size() == n) {
                for (int v = 0; v < n; ++v) polarity[(size_t)v] = (uint8_t)(w[(size_t)v] ? 1 : 0);
            }
        }

        return false;
    }

    // Solve; returns pair(sat, model01)
    pair<bool, vector<int>> solve(const CNF& cnf_verify) {
        orig_cnf = &cnf_verify;

        long long restart_inc = 100;
        int luby_idx = 1;
        long long next_restart = restart_inc * luby(2, luby_idx);
        long long next_reduce = 2000;

        for (;;) {
            int confl = propagate();
            if (confl != -1) {
                conflicts++;
                if (decisionLevel() == 0) {
                    if (debug) {
                        cerr << "c UNSAT at level 0, confl=" << confl << "\n";
                        dump_clause(confl);
                        dump_trail();
                    }
                    return {false, {}};
                }

                vector<Lit> learnt;
                int bt = 0;
                int lbd = 0;
                analyze(confl, learnt, bt, lbd);

                // activity decay
                varDecay();
                claDecay();

                cancelUntil(bt);

#ifndef NDEBUG
                if (!learnt.empty()) {
                    if (valueLit(learnt[0]) != 0) {
                        cerr << "c ASSERT: asserting literal not unassigned after backtrack\n";
                        dump_trail();
                        cerr << "c learnt:";
                        for (Lit p : learnt) cerr << ' ' << litToDimacs(p);
                        cerr << " 0\n";
                        assert(false);
                    }
                    for (size_t i = 1; i < learnt.size(); ++i) {
                        if (valueLit(learnt[i]) != -1) {
                            cerr << "c ASSERT: learnt clause not unit after backtrack\n";
                            dump_trail();
                            cerr << "c learnt:";
                            for (Lit p : learnt) cerr << ' ' << litToDimacs(p);
                            cerr << " 0\n";
                            assert(false);
                        }
                    }
                }
#endif

                // add learnt clause
                if (learnt.size() == 1) {
                    if (!enqueue(learnt[0], -1)) return {false, {}};
                } else {
                    // put asserting literal at position 0
                    // ensure learnt[0] is asserting; already set in analyze
                    int ci = -1;
                    bool ok = addClauseInternal(learnt, true, lbd, &ci);
                    if (!ok) return {false, {}};
                    if (ci != -1) {
                        // enqueue asserting literal with reason
                        if (!enqueue(clauses[(size_t)ci].lits[0], ci)) return {false, {}};

                        // queue to CoverTrace if good
                        if (ct && lbd <= ct_lbd_max && (int)clauses[(size_t)ci].lits.size() <= ct_maxlen) {
                            ct_queue.push_back(ci);
                        }
                    }
                }

                // interleaving
                if (ct && (conflicts % ct_every == 0)) {
                    if (covertrace_tick()) {
                        return {false, {}}; // UNSAT proven by CoverTrace
                    }
                }

                // restarts
                if (conflicts >= next_restart) {
                    cancelUntil(0);
                    luby_idx++;
                    next_restart = conflicts + restart_inc * luby(2, luby_idx);
                }

                // reduce db
                if (conflicts >= next_reduce) {
                    reduceDB();
                    next_reduce = conflicts + 2000;
                }

                continue;
            }

            // no conflict
            Lit next = pickBranchLit();
            if (next == -1) {
                // SAT candidate; build model (unassigned => 0) and verify
                vector<int> model01((size_t)n, 0);
                for (int v = 0; v < n; ++v) {
                    int8_t a = assigns[(size_t)v];
                    model01[(size_t)v] = (a == 1) ? 1 : 0;
                }

                int bad = -1;
                if (!eval_cnf(cnf_verify, model01, &bad)) {
                    // This should never happen in a correct CDCL; but we refuse to claim SAT.
                    // Convert the falsified clause into a conflict by forcing search to continue.
                    // Strategy: add that falsified clause again (no-op) and backtrack/restart.
                    cerr << "c WARNING: SAT candidate fails verification at clause " << bad << ". Continuing search.\n";
                    cancelUntil(0);
                    // Make phases follow the current (wrong) model to escape; flip a bit
                    if (n > 0) polarity[(size_t)(bad % n)] ^= 1;
                    continue;
                }

                return {true, model01};
            }

            newDecisionLevel();
            if (!enqueue(next, -1)) {
                // should not happen
                cancelUntil(0);
            }
        }
    }
};

// ============================================================
// CLI / main
// ============================================================
enum Mode { MODE_INTERLEAVED, MODE_CDCL, MODE_COVERTRACE };

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    Mode mode = MODE_INTERLEAVED;
    bool ct_seed_original = false;
    int ct_every = 64;
    int ct_batch = 16;
    int ct_lbd = 2;
    int ct_maxlen = 4;
    int ct_witness_phase_every = 32;
    size_t ct_maxu = 8;

    string path;
    for (int i = 1; i < argc; ++i) {
        string s = argv[i];
        if (s == "--interleaved" || s == "--interleave") mode = MODE_INTERLEAVED;
        else if (s == "--cdcl" || s == "--cdcl-only") mode = MODE_CDCL;
        else if (s == "--covertrace" || s == "--ct-only") mode = MODE_COVERTRACE;
        else if (s == "--ct-seed-original") ct_seed_original = true;
        else if (s == "--ct-every" && i + 1 < argc) ct_every = atoi(argv[++i]);
        else if (s == "--ct-batch" && i + 1 < argc) ct_batch = atoi(argv[++i]);
        else if (s == "--ct-lbd" && i + 1 < argc) ct_lbd = atoi(argv[++i]);
        else if (s == "--ct-maxlen" && i + 1 < argc) ct_maxlen = atoi(argv[++i]);
        else if (s == "--ct-maxu" && i + 1 < argc) ct_maxu = (size_t)atoll(argv[++i]);
        else if (s == "--ct-witness-phase-every" && i + 1 < argc) ct_witness_phase_every = atoi(argv[++i]);
        else path = s;
    }

    if (path.empty()) {
        cerr << "c usage: " << argv[0]
             << " [--interleaved|--cdcl|--covertrace] [ct options] <input.cnf>\n";
        return 1;
    }

    CNF cnf = parse_dimacs(path);

    // CoverTrace-only mode can only prove UNSAT (or give up). If it doesn't reach y==0, we fall back to CDCL.
    unique_ptr<CoverTrace> ct_ptr;

    if (mode == MODE_COVERTRACE) {
        CoverTrace ct(cnf.n, cnf.clauses);
        for (const auto& c : cnf.clauses) {
            if (ct.feed_clause(c)) {
                cout << "s UNSATISFIABLE\n";
                return 20;
            }
            if (ct.U.size() > ct_maxu) {
                cerr << "c CoverTrace U too large (" << ct.U.size() << "); switching to CDCL.\n";
                break;
            }
        }
        mode = MODE_INTERLEAVED;
        ct_seed_original = true;
    }

    if (mode == MODE_INTERLEAVED) {
        ct_ptr = make_unique<CoverTrace>(cnf.n, cnf.clauses);
    }

    CDCLSolver solver(cnf.n);
    solver.ct = ct_ptr.get();
    solver.ct_seed_original = ct_seed_original;
    solver.ct_every = ct_every;
    solver.ct_batch = ct_batch;
    solver.ct_lbd_max = ct_lbd;
    solver.ct_maxlen = ct_maxlen;
    solver.ct_witness_phase_every = ct_witness_phase_every;
    solver.ct_maxU = ct_maxu;

    // Add original clauses to CDCL (exact)
    for (const auto& c : cnf.clauses) {
        if (!solver.addClauseDimacs(c, false, 0)) {
            cout << "s UNSATISFIABLE\n";
            return 20;
        }
    }

    auto [sat, model01] = solver.solve(cnf);

    if (sat) {
        cout << "s SATISFIABLE\n";
        cout << "v ";
        for (int v = 0; v < cnf.n; ++v) {
            int lit = model01[(size_t)v] ? (v + 1) : -(v + 1);
            cout << lit << ' ';
        }
        cout << "0\n";
        return 10;
    }

    // If interleaved, CoverTrace may have proven UNSAT even if CDCL returns UNSAT.
    cout << "s UNSATISFIABLE\n";
    return 20;
}





