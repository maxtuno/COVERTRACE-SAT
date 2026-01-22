/*
Copyright (c) 2012–2026 Oscar Riveros

SATX is free software: you can redistribute it and/or modify it under the terms of the GNU Affero General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

SATX is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License along with this program. If not, see https://www.gnu.org/licenses/.

Commercial licensing options are available. See COMMERCIAL.md for details.
*/

// covertrace_sat.cpp
// Hybrid SAT solver: CDCL (standard heuristics) + interleaved CoverTrace UNSAT detector.
//
// Soundness: the solver verifies any SAT candidate model before printing SAT.
//
// Build:
//   g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat.cpp -o covertrace_sat
//
// Run:
//   ./covertrace_sat [options] input.cnf
//
// Options:
//   --cdcl            : CDCL only
//   --covertrace      : CoverTrace only (exact, may blow up)
//   --interleaved     : CDCL + interleaved CoverTrace (default)
//
// Interleaved CoverTrace options:
//   --ct-seed-original        : feed original clauses into CoverTrace queue too
//   --ct-every <conflicts>    : run a CoverTrace tick every N CDCL conflicts (default 2000)
//   --ct-batch <k>            : how many clauses to feed per tick (default 128)
//   --ct-lbd <L>              : only feed learned clauses with LBD <= L (default 6)
//   --ct-maxlen <K>           : only feed clauses of length <= K (default 12)
//   --ct-maxu <U>             : pause CoverTrace if |U| exceeds U (default 300000)
//
// Output is DIMACS-style:
//   s SATISFIABLE / s UNSATISFIABLE
//   v <lits...> 0  (only for SAT)

#include <bits/stdc++.h>
using namespace std;

// ------------------------------------------------------------
// DIMACS parsing
// ------------------------------------------------------------
struct CNF {
    int nvars = 0;
    vector<vector<int>> clauses; // DIMACS literals
};

static CNF parse_dimacs(const string& path) {
    ifstream in(path);
    if (!in) {
        cerr << "c ERROR: cannot open " << path << "\n";
        exit(1);
    }
    CNF cnf;
    string tok;
    int n = 0, m = 0;
    while (in >> tok) {
        if (tok == "c") {
            string line;
            getline(in, line);
            continue;
        }
        if (tok == "p") {
            string fmt;
            in >> fmt >> n >> m;
            cnf.nvars = n;
            cnf.clauses.reserve(m);
            continue;
        }
        // first literal of a clause
        int lit = stoi(tok);
        vector<int> clause;
        clause.reserve(8);
        while (lit != 0) {
            clause.push_back(lit);
            in >> lit;
        }
        cnf.clauses.push_back(std::move(clause));
    }
    return cnf;
}

static bool eval_cnf(const vector<vector<int>>& clauses, const vector<int>& assign01 /*size nvars, 0/1*/) {
    for (const auto& c : clauses) {
        bool sat = false;
        for (int x : c) {
            int v = abs(x) - 1;
            bool val = assign01[v] != 0;
            bool lit_true = (x > 0) ? val : !val;
            if (lit_true) { sat = true; break; }
        }
        if (!sat) return false;
    }
    return true;
}

// ------------------------------------------------------------
// Simple BigInt base 2^32 (non-negative only) - only operations we need.
// ------------------------------------------------------------
struct BigInt {
    vector<uint32_t> a; // little-endian limbs

    void normalize() {
        while (!a.empty() && a.back() == 0) a.pop_back();
    }
    bool is_zero() const { return a.empty(); }

    static BigInt pow2(int exp) {
        BigInt r;
        if (exp < 0) return r;
        size_t limb = (size_t)(exp / 32);
        int bit = exp % 32;
        r.a.assign(limb + 1, 0);
        r.a[limb] = (1u << bit);
        return r;
    }

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

    // assumes *this >= b
    void sub(const BigInt& b) {
        uint64_t borrow = 0;
        size_t n = a.size();
        for (size_t i = 0; i < n; ++i) {
            uint64_t bi = (i < b.a.size() ? b.a[i] : 0u);
            uint64_t cur = (uint64_t)a[i];
            uint64_t need = bi + borrow;
            if (cur >= need) {
                a[i] = (uint32_t)(cur - need);
                borrow = 0;
            } else {
                a[i] = (uint32_t)((cur + (1ull<<32)) - need);
                borrow = 1;
            }
        }
        normalize();
    }
};

// ------------------------------------------------------------
// CoverTrace: disjoint forbidden cubes (exact UNSAT detector)
// ------------------------------------------------------------
struct Cube {
    int n = 0;
    int W = 0;
    vector<uint64_t> fixed; // 1 if var fixed
    vector<uint64_t> value; // value where fixed=1

    Cube() = default;
    explicit Cube(int n_) : n(n_), W((n_ + 63) / 64), fixed(W, 0), value(W, 0) {}

    inline void set_var(int v, int val01) {
        int wi = v >> 6;
        int bi = v & 63;
        uint64_t m = 1ull << bi;
        fixed[wi] |= m;
        if (val01) value[wi] |= m;
        else value[wi] &= ~m;
    }

    inline int popcount_fixed() const {
        int s = 0;
        for (uint64_t x : fixed) s += __builtin_popcountll(x);
        return s;
    }
};

static inline bool intersects(const Cube& a, const Cube& b) {
    for (int i = 0; i < a.W; ++i) {
        uint64_t both = a.fixed[i] & b.fixed[i];
        uint64_t diff = (a.value[i] ^ b.value[i]) & both;
        if (diff) return false;
    }
    return true;
}

// a subset b : all assignments satisfying a also satisfy b
static inline bool subset(const Cube& a, const Cube& b) {
    // b's fixed bits must be subset of a's fixed, with matching values
    for (int i = 0; i < a.W; ++i) {
        uint64_t bf = b.fixed[i];
        if (bf & ~a.fixed[i]) return false;
        if (((a.value[i] ^ b.value[i]) & bf) != 0) return false;
    }
    return true;
}

// p \ r -> disjoint cubes appended to out
static void cube_diff(const Cube& p_in, const Cube& r, vector<Cube>& out) {
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
                cut = wi*64 + b;
                rv = (r.value[wi] >> b) & 1;
            }
        }
        if (cut < 0) return; // should not happen if subset check above is correct

        Cube other = p;
        other.set_var(cut, 1 - rv);
        out.push_back(std::move(other));

        p.set_var(cut, rv);
        if (subset(p, r)) return;
    }
}

static bool clause_to_cube(const vector<int>& clause_dimacs, int n, Cube& out) {
    // A clause is falsified when all literals are false.
    // (x) false => x=0; (~x) false => x=1
    vector<int> lits = clause_dimacs;
    sort(lits.begin(), lits.end(), [](int a, int b) {
        int va = abs(a), vb = abs(b);
        if (va != vb) return va < vb;
        return a < b;
    });

    Cube c(n);
    for (size_t i = 0; i < lits.size();) {
        int v = abs(lits[i]);
        bool has_pos = false, has_neg = false;
        while (i < lits.size() && abs(lits[i]) == v) {
            if (lits[i] > 0) has_pos = true; else has_neg = true;
            ++i;
        }
        if (has_pos && has_neg) return false; // tautology
        if (has_pos) c.set_var(v - 1, 0);
        else if (has_neg) c.set_var(v - 1, 1);
    }
    out = std::move(c);
    return true;
}

struct CoverTrace {
    int n = 0;
    vector<Cube> U;      // disjoint cubes
    BigInt y;            // remaining uncovered assignments count

    explicit CoverTrace(int n_) : n(n_), y(BigInt::pow2(n_)) {
        U.reserve(1024);
    }

    BigInt add_cube_disjoint(const Cube& Q) {
        vector<Cube> P;
        P.reserve(32);
        P.push_back(Q);

        // Early filter: if any R covers Q => delta 0
        for (const Cube& R : U) {
            if (!intersects(Q, R)) continue;
            if (subset(Q, R)) return BigInt{}; // 0
        }

        vector<Cube> tmp;
        for (const Cube& R : U) {
            if (P.empty()) break;
            if (!intersects(Q, R)) continue;

            tmp.clear();
            tmp.reserve(P.size()*2);
            for (const Cube& p : P) {
                if (!intersects(p, R)) tmp.push_back(p);
                else cube_diff(p, R, tmp);
            }
            P.swap(tmp);
        }

        BigInt delta;
        for (const Cube& p : P) {
            U.push_back(p);
            delta.add_pow2(n - p.popcount_fixed());
        }
        return delta;
    }

    // returns true if UNSAT proven (y==0)
    bool feed_clause(const vector<int>& clause_dimacs) {
        Cube Q(n);
        if (!clause_to_cube(clause_dimacs, n, Q)) return false;
        BigInt delta = add_cube_disjoint(Q);
        if (!delta.is_zero()) {
            // y -= delta, saturating at 0 (shouldn't go negative if math is correct)
            // we assume y >= delta because delta is new uncovered volume
            y.sub(delta);
        }
        return y.is_zero();
    }
};

// ------------------------------------------------------------
// CDCL core
// ------------------------------------------------------------
static inline int luby(int y, int x) {
    // Luby sequence as in MiniSat (1,1,2,1,1,2,4,...)
    int size = 1;
    int seq = 0;
    while (size < x + 1) {
        seq++;
        size = 2*size + 1;
    }
    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }
    return 1 << seq;
}

enum class SolveStatus { SAT, UNSAT, UNKNOWN };

struct SolveOut {
    SolveStatus status = SolveStatus::UNKNOWN;
    vector<int> model01;
};

struct Clause {
    vector<int> lits; // internal literal ids
    bool learnt = false;
    bool deleted = false;
    int lbd = 0;
    double activity = 0.0;
};

struct Watch {
    int cref;
    int blocker;
};

struct CDCL {
    int n = 0;
    vector<Clause> cs;
    vector<vector<Watch>> watches; // size 2*n
    vector<int8_t> assigns;        // -1 false, 0 undef, 1 true
    vector<int> level;
    vector<int> reason;            // cref or -1
    vector<int> trail;
    vector<int> trail_lim;
    int qhead = 0;

    // heuristics
    vector<double> var_act;
    vector<uint8_t> phase;    // 0/1
    double var_inc = 1.0;
    double var_decay = 0.95;

    // learned clause management
    vector<int> learnts;
    double cla_inc = 1.0;
    double cla_decay = 0.999;

    // interleaving
    CoverTrace* ct = nullptr;
    bool ct_seed_original = false;
    int ct_every = 2000;
    int ct_batch = 128;
    int ct_lbd_max = 6;
    int ct_len_max = 12;
    int ct_max_u = 300000;
    deque<int> ct_queue; // clause indices (cs)

    // stats
    long long conflicts = 0;
    long long propagations = 0;
    long long decisions = 0;

    explicit CDCL(int nvars) : n(nvars) {
        watches.assign(2*n, {});
        assigns.assign(n, 0);
        level.assign(n, 0);
        reason.assign(n, -1);
        var_act.assign(n, 0.0);
        phase.assign(n, 1);
    }

    inline int toLitDimacs(int x) const {
        int v = abs(x) - 1;
        return (v << 1) ^ (x < 0);
    }
    inline int var(int lit) const { return lit >> 1; }
    inline int neg(int lit) const { return lit ^ 1; }

    inline int litValue(int lit) const {
        int v = var(lit);
        int8_t a = assigns[v];
        if (a == 0) return 0;
        bool val = (a == 1);
        bool sign = (lit & 1);
        bool truth = (val != sign);
        return truth ? 1 : -1;
    }

    int decisionLevel() const { return (int)trail_lim.size(); }

    void newDecisionLevel() { trail_lim.push_back((int)trail.size()); }

    bool enqueue(int lit, int from) {
        int v = var(lit);
        int8_t a = assigns[v];
        int8_t need = (lit & 1) ? -1 : 1;
        if (a != 0) return a == need;
        assigns[v] = need;
        level[v] = decisionLevel();
        reason[v] = from;
        phase[v] = (need == 1) ? 1 : 0; // phase saving
        trail.push_back(lit);
        return true;
    }

    void cancelUntil(int lvl) {
        if (decisionLevel() <= lvl) return;
        int lim = (lvl == 0) ? 0 : trail_lim[lvl];
        for (int i = (int)trail.size() - 1; i >= lim; --i) {
            int v = var(trail[i]);
            assigns[v] = 0;
            reason[v] = -1;
            level[v] = 0;
        }
        trail.resize(lim);
        trail_lim.resize(lvl);
        qhead = min(qhead, (int)trail.size());
    }

    void varBump(int v) {
        var_act[v] += var_inc;
        if (var_act[v] > 1e100) {
            // rescale
            for (double &x : var_act) x *= 1e-100;
            var_inc *= 1e-100;
        }
    }

    void varDecay() { var_inc *= (1.0 / var_decay); }

    void claBump(int ci) {
        cs[ci].activity += cla_inc;
        if (cs[ci].activity > 1e20) {
            for (int id : learnts) if (!cs[id].deleted) cs[id].activity *= 1e-20;
            cla_inc *= 1e-20;
        }
    }
    void claDecay() { cla_inc *= (1.0 / cla_decay); }

    void attachClause(int ci) {
        Clause& c = cs[ci];
        if (c.deleted) return;
        if (c.lits.size() == 1) {
            // store under the falsified literal (¬l) because propagate processes watches[false_lit]
            watches[neg(c.lits[0])].push_back({ci, c.lits[0]});
        } else {
            // ensure first two watched are at positions 0 and 1
            watches[neg(c.lits[0])].push_back({ci, c.lits[1]});
            watches[neg(c.lits[1])].push_back({ci, c.lits[0]});
        }
    }

    void rebuildWatches() {
        watches.assign(2*n, {});
        for (int i = 0; i < (int)cs.size(); ++i) {
            if (cs[i].deleted) continue;
            if (cs[i].lits.empty()) continue;
            if (cs[i].lits.size() == 1) {
                watches[neg(cs[i].lits[0])].push_back({i, cs[i].lits[0]});
            } else {
                // normalize watched literals
                // pick two non-false lits if possible
                int w0 = 0, w1 = 1;
                // simple: keep first two; propagate will fix
                watches[neg(cs[i].lits[w0])].push_back({i, cs[i].lits[w1]});
                watches[neg(cs[i].lits[w1])].push_back({i, cs[i].lits[w0]});
            }
        }
    }

    // Add a clause from DIMACS literals (public interface).
    // Returns false if contradiction detected at level 0.
    bool addClauseDimacs(const vector<int>& dimacs, bool learnt=false, int lbd=0) {
        vector<int> lits;
        lits.reserve(dimacs.size());
        for (int x : dimacs) {
            if (x == 0) continue;
            int l = toLitDimacs(x);
            lits.push_back(l);
        }
        return addClauseInternal(lits, learnt, lbd);
    }

    bool addClauseInternal(vector<int>& lits, bool learnt=false, int lbd=0) {
        if (lits.empty()) return false;

        // remove duplicates/tautologies
        sort(lits.begin(), lits.end());
        lits.erase(unique(lits.begin(), lits.end()), lits.end());
        for (int l : lits) {
            if (binary_search(lits.begin(), lits.end(), neg(l))) return true; // tautology -> ignore
        }

        // simplify using current assignment at level 0 only
        if (decisionLevel() == 0) {
            vector<int> tmp;
            tmp.reserve(lits.size());
            for (int l : lits) {
                int v = litValue(l);
                if (v == 1) return true; // already satisfied
                if (v == 0) tmp.push_back(l);
            }
            lits.swap(tmp);
            if (lits.empty()) return false; // empty after simplification -> conflict
            if (lits.size() == 1) {
                if (!enqueue(lits[0], -1)) return false;
                int confl;
                if (!propagate(confl)) return false;
                return true;
            }
        }

        Clause c;
        c.lits = std::move(lits);
        c.learnt = learnt;
        c.lbd = lbd;
        int ci = (int)cs.size();
        cs.push_back(std::move(c));
        if (cs[ci].learnt) learnts.push_back(ci);
        attachClause(ci);

        // if unit, enqueue now (might be beyond level 0 for learnts; handled in addLearnt)
        return true;
    }

    // Propagation. Returns false on conflict and outputs conflict clause index in confl.
    bool propagate(int& confl) {
        confl = -1;
        while (qhead < (int)trail.size()) {
            int p = trail[qhead++]; // lit set true
            // We store watches under the negation of the watched literal (MiniSat scheme).
            // When p becomes true, the watched literal ¬p became false, so we process watches[p].
            int false_lit = neg(p);
            auto& ws = watches[p];
            int i = 0, j = 0;
            propagations++;

            while (i < (int)ws.size()) {
                Watch w = ws[i++];
                int ci = w.cref;
                if (ci < 0 || ci >= (int)cs.size()) continue;
                Clause& c = cs[ci];
                if (c.deleted) continue;

                // quick satisfied check via blocker
                if (litValue(w.blocker) == 1) {
                    ws[j++] = w;
                    continue;
                }

                // ensure c.lits[0] is false_lit (the watched lit that became false)
                if (c.lits.size() == 1) {
                    // unit clause watched directly: if it becomes false -> conflict
                    if (litValue(c.lits[0]) == -1) {
                        confl = ci;
                        // keep remaining watches
                        ws[j++] = w;
                        while (i < (int)ws.size()) ws[j++] = ws[i++];
                        ws.resize(j);
                        return false;
                    } else {
                        ws[j++] = w;
                        continue;
                    }
                }

                int l0 = c.lits[0];
                int l1 = c.lits[1];
                if (l0 != false_lit) {
                    // swap watchers in clause
                    if (l1 == false_lit) swap(c.lits[0], c.lits[1]);
                    else {
                        // false_lit might not be in first two due to rebuild; try to find and swap into position 0
                        // (rare; maintains soundness)
                        for (size_t k = 2; k < c.lits.size(); ++k) {
                            if (c.lits[k] == false_lit) { swap(c.lits[0], c.lits[k]); break; }
                        }
                        if (c.lits[0] != false_lit) {
                            // can't locate; keep watch entry and continue safely
                            ws[j++] = w;
                            continue;
                        }
                    }
                    l0 = c.lits[0]; l1 = c.lits[1];
                }

                int other = l1;
                if (litValue(other) == 1) {
                    ws[j++] = {ci, other};
                    continue;
                }

                // find new watch
                bool found = false;
                for (size_t k = 2; k < c.lits.size(); ++k) {
                    int lk = c.lits[k];
                    if (litValue(lk) != -1) {
                        // move watch from false_lit to lk
                        c.lits[0] = lk;
                        c.lits[k] = false_lit;
                        watches[neg(lk)].push_back({ci, other});
                        found = true;
                        break;
                    }
                }

                if (found) continue;

                // clause is unit or conflict under current assignment
                ws[j++] = {ci, other};
                if (litValue(other) == -1) {
                    confl = ci;
                    while (i < (int)ws.size()) ws[j++] = ws[i++];
                    ws.resize(j);
                    return false;
                } else {
                    if (!enqueue(other, ci)) {
                        confl = ci;
                        while (i < (int)ws.size()) ws[j++] = ws[i++];
                        ws.resize(j);
                        return false;
                    }
                }
            }
            ws.resize(j);
        }
        return true;
    }

    int pickBranchLit() {
        int best = -1;
        double best_act = -1.0;
        for (int v = 0; v < n; ++v) {
            if (assigns[v] != 0) continue;
            double a = var_act[v];
            if (a > best_act) { best_act = a; best = v; }
        }
        if (best == -1) return -1;
        decisions++;
        // phase saving
        int lit = (best << 1) ^ (phase[best] ? 0 : 1);
        return lit;
    }

    int computeLBD(const vector<int>& clause) {
        // distinct decision levels among literals (excluding level 0)
        static vector<int> seen_levels;
        seen_levels.clear();
        seen_levels.reserve(clause.size());
        for (int lit : clause) {
            int v = var(lit);
            int lv = level[v];
            if (lv == 0) continue;
            seen_levels.push_back(lv);
        }
        sort(seen_levels.begin(), seen_levels.end());
        seen_levels.erase(unique(seen_levels.begin(), seen_levels.end()), seen_levels.end());
        return (int)seen_levels.size();
    }

    void analyze(int confl, vector<int>& out_learnt, int& out_bt, int& out_lbd) {
        out_learnt.clear();
        out_learnt.push_back(-1); // placeholder for asserting lit

        vector<uint8_t> seen(n, 0);
        vector<int> to_clear;
        to_clear.reserve(64);

        int pathC = 0;
        int p = -1;
        int idx = (int)trail.size() - 1;

        Clause* cptr = &cs[confl];
        claBump(confl);

        // Resolve until first UIP
        while (true) {
            Clause& c = *cptr;
            for (int q : c.lits) {
                int v = var(q);
                if (!seen[v] && level[v] > 0) {
                    seen[v] = 1;
                    to_clear.push_back(v);
                    varBump(v);
                    if (level[v] == decisionLevel()) pathC++;
                    else out_learnt.push_back(q);
                }
            }

            // pick next seen variable from trail (latest assignment)
            while (idx >= 0) {
                int t = trail[idx--];
                if (seen[var(t)]) { p = t; break; }
            }
            if (p == -1) {
                // Should not happen in a sound CDCL; fall back to avoid UB.
                break;
            }

            int pv = var(p);
            seen[pv] = 0; // do not visit again
            pathC--;

            if (pathC <= 0) break;

            int r = reason[pv];
            if (r >= 0) cptr = &cs[r];
            else {
                // Decision variable reached earlier than expected; safe fallback.
                break;
            }
        }

        out_learnt[0] = neg(p);

        // Backtrack level: max level among other literals
        out_bt = 0;
        for (size_t i = 1; i < out_learnt.size(); ++i) {
            out_bt = max(out_bt, level[var(out_learnt[i])]);
        }

        out_lbd = computeLBD(out_learnt);

        for (int v : to_clear) seen[v] = 0;
    }

    bool locked(int ci) const {
        const Clause& c = cs[ci];
        if (c.deleted || c.lits.empty()) return false;
        // A clause is locked if it is the reason for some assigned var.
        // This check is cheap and sufficient.
        for (int lit : c.lits) {
            int v = var(lit);
            if (reason[v] == ci) return true;
        }
        return false;
    }

    void reduceDB() {
        // keep binaries, keep low LBD, keep locked
        vector<int> cand;
        cand.reserve(learnts.size());
        for (int ci : learnts) {
            if (cs[ci].deleted) continue;
            if (cs[ci].lits.size() <= 2) continue;
            if (locked(ci)) continue;
            cand.push_back(ci);
        }
        if (cand.empty()) return;

        sort(cand.begin(), cand.end(), [&](int a, int b) {
            if (cs[a].lbd != cs[b].lbd) return cs[a].lbd < cs[b].lbd;
            return cs[a].activity > cs[b].activity;
        });

        size_t remove_cnt = cand.size() / 2;
        for (size_t i = 0; i < remove_cnt; ++i) {
            int ci = cand[i];
            cs[ci].deleted = true; // lazy delete
        }
    }

    // covertrace tick: feed queued clauses
    bool covertrace_tick() {
        if (!ct) return false;
        if ((int)ct->U.size() > ct_max_u) return false;

        int k = 0;
        while (!ct_queue.empty() && k < ct_batch) {
            int ci = ct_queue.front();
            ct_queue.pop_front();
            if (ci < 0 || ci >= (int)cs.size()) continue;
            Clause& c = cs[ci];
            if (c.deleted) continue;

            // Convert internal lits to DIMACS lits
            vector<int> dim;
            dim.reserve(c.lits.size());
            for (int l : c.lits) {
                int v = var(l) + 1;
                bool is_neg = (l & 1);
                dim.push_back(is_neg ? -v : v);
            }
            if (ct->feed_clause(dim)) return true; // UNSAT proven
            k++;
        }
        return false;
    }

    // Solve. Returns {sat, model01} where model01 size n with 0/1 values.
    SolveOut solve(const vector<vector<int>>& orig_dimacs) {
        // enqueue original clauses to covertrace if requested
        if (ct && ct_seed_original) {
            for (int i = 0; i < (int)cs.size(); ++i) {
                if (!cs[i].deleted && !cs[i].learnt) ct_queue.push_back(i);
            }
        }

        // initial propagate at level 0
        int confl;
        if (!propagate(confl)) return {SolveStatus::UNSAT, {}};

        // Restart policy
        int restart_inc = 100;
        int luby_idx = 1;
        long long next_restart = (long long)restart_inc * luby(2, luby_idx);

        long long next_reduce = 2000;

        int sat_guard_rebuilds = 0;

        while (true) {
            int confl;
            if (!propagate(confl)) {
                conflicts++;

                if (decisionLevel() == 0) return {SolveStatus::UNSAT, {}};

                // analyze conflict
                vector<int> learnt;
                int bt, lbd;
                analyze(confl, learnt, bt, lbd);

                // decay/bump
                varDecay();
                claDecay();
                claBump(confl);

                cancelUntil(bt);

                // add learnt clause
                // place asserting lit at front, then choose second lit with highest level for better propagation
                if (learnt.size() > 1) {
                    int max_i = 1;
                    int max_lv = level[var(learnt[1])];
                    for (size_t i = 2; i < learnt.size(); ++i) {
                        int lv = level[var(learnt[i])];
                        if (lv > max_lv) { max_lv = lv; max_i = (int)i; }
                    }
                    swap(learnt[1], learnt[max_i]);
                }

                int ci = (int)cs.size();
                {
                    Clause c;
                    c.lits = learnt;
                    c.learnt = true;
                    c.lbd = lbd;
                    c.activity = 0.0;
                    cs.push_back(std::move(c));
                    learnts.push_back(ci);
                    attachClause(ci);
                }

                if (ct && lbd <= ct_lbd_max && (int)learnt.size() <= ct_len_max) {
                    ct_queue.push_back(ci);
                }

                // enqueue asserting lit
                if (!enqueue(cs[ci].lits[0], ci)) {
                    return {SolveStatus::UNSAT, {}};
                }

                // periodic covertrace tick
                if (ct && conflicts % ct_every == 0) {
                    if (covertrace_tick()) return {SolveStatus::UNSAT, {}}; // UNSAT
                }

                // restarts (Luby)
                if (conflicts >= next_restart) {
                    cancelUntil(0);
                    luby_idx++;
                    next_restart = conflicts + (long long)restart_inc * luby(2, luby_idx);
                }

                // reduce DB
                if (conflicts >= next_reduce) {
                    reduceDB();
                    next_reduce = conflicts + 2000;
                }

                continue;
            }

            // no conflict
            int next = pickBranchLit();
            if (next == -1) {
                // SAT candidate: build model and verify
                vector<int> model01(n, 0);
                for (int v = 0; v < n; ++v) {
                    int8_t a = assigns[v];
                    model01[v] = (a == 1) ? 1 : 0;
                }
                if (eval_cnf(orig_dimacs, model01)) {
                    return {SolveStatus::SAT, model01};
                }

                // guard: if verification fails, we never claim SAT
                sat_guard_rebuilds++;
                cerr << "c WARNING: model failed verification. Rebuilding watches and continuing (guard).\n";
                if (sat_guard_rebuilds > 3) {
                    cerr << "c ERROR: repeated invalid SAT candidates; aborting as UNKNOWN.\n";
                    // safer than claiming SAT; but keep UNSAT correctness:
                    // if covertrace already proved UNSAT, we'd have returned earlier.
                    return {SolveStatus::UNKNOWN, {}};
                }
                rebuildWatches();
                cancelUntil(0);
                continue;
            }

            newDecisionLevel();
            if (!enqueue(next, -1)) {
                // should not happen
                cancelUntil(0);
            }
        }
    }
};

// ------------------------------------------------------------
// Main / glue
// ------------------------------------------------------------
enum Mode { MODE_INTERLEAVED, MODE_CDCL, MODE_COVERTRACE };

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    Mode mode = MODE_INTERLEAVED;
    bool ct_seed_original = false;
    int ct_every = 2000;
    int ct_batch = 128;
    int ct_lbd = 6;
    int ct_maxlen = 12;
    int ct_maxu = 300000;

    string path;
    for (int i = 1; i < argc; ++i) {
        string s = argv[i];
        if (s == "--interleaved") mode = MODE_INTERLEAVED;
        else if (s == "--cdcl") mode = MODE_CDCL;
        else if (s == "--covertrace") mode = MODE_COVERTRACE;
        else if (s == "--ct-seed-original") ct_seed_original = true;
        else if (s == "--ct-every" && i + 1 < argc) ct_every = atoi(argv[++i]);
        else if (s == "--ct-batch" && i + 1 < argc) ct_batch = atoi(argv[++i]);
        else if (s == "--ct-lbd" && i + 1 < argc) ct_lbd = atoi(argv[++i]);
        else if (s == "--ct-maxlen" && i + 1 < argc) ct_maxlen = atoi(argv[++i]);
        else if (s == "--ct-maxu" && i + 1 < argc) ct_maxu = atoi(argv[++i]);
        else path = s;
    }

    if (path.empty()) {
        cerr << "c usage: " << argv[0] << " [--interleaved|--cdcl|--covertrace] [ct options] <input.cnf>\n";
        return 1;
    }

    CNF cnf = parse_dimacs(path);

    if (mode == MODE_COVERTRACE) {
        CoverTrace ct(cnf.nvars);
        for (const auto& c : cnf.clauses) {
            if (ct.feed_clause(c)) {
                cout << "s UNSATISFIABLE\n";
                return 20;
            }
            if ((int)ct.U.size() > ct_maxu) {
                cerr << "c CoverTrace U too large; stopping early.\n";
                break;
            }
        }
        // If CoverTrace didn't prove UNSAT, we can't conclude SAT (needs witness extraction).
        // Use CDCL to finish.
        mode = MODE_INTERLEAVED;
        ct_seed_original = true;
        // continue below
    }

    unique_ptr<CoverTrace> ct_ptr;
    if (mode == MODE_INTERLEAVED) {
        ct_ptr = make_unique<CoverTrace>(cnf.nvars);
    }

    CDCL solver(cnf.nvars);
    if (ct_ptr) {
        solver.ct = ct_ptr.get();
        solver.ct_seed_original = ct_seed_original;
        solver.ct_every = ct_every;
        solver.ct_batch = ct_batch;
        solver.ct_lbd_max = ct_lbd;
        solver.ct_len_max = ct_maxlen;
        solver.ct_max_u = ct_maxu;
    }

    // Add original clauses
    for (const auto& c : cnf.clauses) {
        if (!solver.addClauseDimacs(c, false, 0)) {
            cout << "s UNSATISFIABLE\n";
            return 20;
        }
    }

    SolveOut out = solver.solve(cnf.clauses);

    if (out.status == SolveStatus::SAT) {
        const auto& model01 = out.model01;
        cout << "s SATISFIABLE\n";
        cout << "v ";
        for (int v = 0; v < cnf.nvars; ++v) {
            int lit = model01[v] ? (v + 1) : -(v + 1);
            cout << lit << " ";
        }
        cout << "0\n";
        return 10;
    } else if (out.status == SolveStatus::UNSAT) {
        cout << "s UNSATISFIABLE\n";
        return 20;
    } else {
        cout << "s UNKNOWN\n";
        return 0;
    }
}
