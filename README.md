# COVERTRACE-SAT

I’m sharing my new paper, “COVERTRACE-SAT as Disjoint-Subcube Knowledge Compilation.” It reframes CNF-SAT/#SAT geometrically: clauses forbid axis-aligned subcubes of the Boolean hypercube, and we maintain an exact disjoint cover (DSOP-style) so model counting becomes additive and witness extraction is constructive. The paper formalizes correctness, analyzes fragmentation as the central complexity driver, proves explicit exponential worst-case lower bounds for disjoint subcube covers, and discusses the conditional consequence that uniform polynomial-size disjoint-cover compilation would imply #SAT ∈ P and collapse PH. Code is included for reproducibility and benchmarking.

[COVERTRACE-SAT as Disjoint Subcube Knowledge Compilation](https://www.academia.edu/147768691/COVERTRACE_SAT_as_Disjoint_Subcube_Knowledge_Compilation_Worst_Case_Fragmentation_Conditional_PH_Collapse_and_Connections_to_Geometric_Complexity_Theory)


### Hybrid SAT solver: CDCL (standard heuristics) + interleaved CoverTrace UNSAT detector.

#### Features (CDCL):
      - 2-watched literals propagation
      - 1-UIP conflict analysis and backjumping
      - VSIDS variable activity + decay
      - Phase saving
      - Luby restarts
      - LBD scoring (Glucose-style) + learned DB reduction
      - Final model verification (never prints SAT with invalid assignment)

#### Features (Interleaving):
      - While CDCL runs, we continuously feed a filtered stream of *entailed clauses* (learned clauses with low LBD / small size, plus optionally original clauses) into CoverTrace.
      - If CoverTrace proves coverage of {0,1}^n, we can conclude UNSAT early.
      - Optional: CoverTrace witness (when y>0) is used to set CDCL phase preferences.

#### Build:
    g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat_hybrid_interleaved.cpp -o covertrace_sat

#### Run:
    ./covertrace_sat --interleaved --ct-seed-original test.cnf
    ./covertrace_sat --cdcl test.cnf
    ./covertrace_sat --covertrace test.cnf






