# COVERTRACE-SAT

I’m sharing my new paper, “COVERTRACE-SAT as Disjoint-Subcube Knowledge Compilation.” It reframes CNF-SAT/#SAT geometrically: clauses forbid axis-aligned subcubes of the Boolean hypercube, and we maintain an exact disjoint cover (DSOP-style) so model counting becomes additive and witness extraction is constructive. The paper formalizes correctness, analyzes fragmentation as the central complexity driver, proves explicit exponential worst-case lower bounds for disjoint subcube covers, and discusses the conditional consequence that uniform polynomial-size disjoint-cover compilation would imply #SAT ∈ P and collapse PH. Code is included for reproducibility and benchmarking.

[COVERTRACE-SAT as Disjoint Subcube Knowledge Compilation](https://www.academia.edu/147768691/COVERTRACE_SAT_as_Disjoint_Subcube_Knowledge_Compilation_Worst_Case_Fragmentation_Conditional_PH_Collapse_and_Connections_to_Geometric_Complexity_Theory)


## Hybrid SAT solver: CDCL (standard heuristics) + interleaved CoverTrace UNSAT detector.
Soundness: the solver verifies any SAT candidate model before printing SAT.

### Build:

    g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat.cpp -o covertrace_sat

### Run:

    ./covertrace_sat [options] input.cnf

### Options:
    
    --cdcl            : CDCL only
    --covertrace      : CoverTrace only (exact, may blow up)
    --interleaved     : CDCL + interleaved CoverTrace (default)

### Interleaved CoverTrace options:

    --ct-seed-original        : feed original clauses into CoverTrace queue too
    --ct-every <conflicts>    : run a CoverTrace tick every N CDCL conflicts (default 2000)
    --ct-batch <k>            : how many clauses to feed per tick (default 128)
    --ct-lbd <L>              : only feed learned clauses with LBD <= L (default 6)
    --ct-maxlen <K>           : only feed clauses of length <= K (default 12)
    --ct-maxu <U>             : pause CoverTrace if |U| exceeds U (default 300000)

### Output is DIMACS-style:

    s SATISFIABLE / s UNSATISFIABLE
    v <lits...> 0  (only for SAT)



