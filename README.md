# COVERTRACE-SAT

I’m sharing my new paper, “COVERTRACE-SAT as Disjoint-Subcube Knowledge Compilation.” It reframes CNF-SAT/#SAT geometrically: clauses forbid axis-aligned subcubes of the Boolean hypercube, and we maintain an exact disjoint cover (DSOP-style) so model counting becomes additive and witness extraction is constructive. The paper formalizes correctness, analyzes fragmentation as the central complexity driver, proves explicit exponential worst-case lower bounds for disjoint subcube covers, and discusses the conditional consequence that uniform polynomial-size disjoint-cover compilation would imply #SAT ∈ P and collapse PH. Code is included for reproducibility and benchmarking.

[COVERTRACE-SAT as Disjoint Subcube Knowledge Compilation](https://www.academia.edu/147768691/COVERTRACE_SAT_as_Disjoint_Subcube_Knowledge_Compilation_Worst_Case_Fragmentation_Conditional_PH_Collapse_and_Connections_to_Geometric_Complexity_Theory)


Compile

    g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat.cpp -o covertrace_sat

Pure CoverTrace:

    ./covertrace_sat --covertrace input.cnf

Pure CDCL:

    ./covertrace_sat --cdcl input.cnf

Hybrid (default): Start with CoverTrace and switch to CDCL if it becomes costly:

    ./covertrace_sat --hybrid input.cnf

Switch to CDCL if |U| exceeds a certain size:

    ./covertrace_sat --hybrid --switch-u 300000 input.cnf

Switch to CDCL if CoverTrace takes more than X ms:

    ./covertrace_sat --hybrid --switch-ms 5000 input.cnf
  
All-In:

    ./covertrace_sat --hybrid --compress --sort-clauses --switch-u 300000 --switch-ms 5000 input.cnf


