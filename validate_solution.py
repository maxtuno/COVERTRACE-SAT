import argparse
from typing import Dict, List, Tuple

Literal = Tuple[int, int]    
CNFClause = List[Literal]


def parse_dimacs_cnf(path: str) -> Tuple[List[List[int]], int]:
    clauses: List[List[int]] = []
    num_vars = 0
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                if len(parts) >= 4:
                    num_vars = int(parts[2])
                continue
            lits = [int(x) for x in line.split() if x != "0"]
            if lits:
                clauses.append(lits)
    return clauses, num_vars


def parse_bool_model(path: str) -> Dict[int, bool]:
    """Parse solver model: integers separated by spaces/newlines; ignore c/s/v prefixes; stop at 0 if present."""
    model: Dict[int, bool] = {}
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(("c", "s")):
                continue
            if line.startswith("v"):
                line = line[1:].strip()
            for tok in line.split():
                if tok == "0":
                    break
                lit = int(tok)
                var = abs(lit)
                model[var] = lit > 0
    return model


# ----------------- Checkers -----------------
def check_gcnf(clauses: List[CNFClause], assign: Dict[int, int]) -> Tuple[bool, List[int]]:
    """Return (ok, unsat_clause_indices)."""
    unsat = []
    for idx, clause in enumerate(clauses):
        sat = False
        for var, val in clause:
            a = assign.get(var, None)
            if a is None:
                continue
            if a == val:
                sat = True
                break
        if not sat:
            unsat.append(idx)
    return len(unsat) == 0, unsat


def check_cnf(cnf: List[List[int]], model: Dict[int, bool]) -> Tuple[bool, List[int]]:
    unsat = []
    for idx, clause in enumerate(cnf):
        sat = False
        for lit in clause:
            val = model.get(abs(lit), False)
            if (lit > 0 and val) or (lit < 0 and not val):
                sat = True
                break
        if not sat:
            unsat.append(idx)
    return len(unsat) == 0, unsat


def decode_model_to_assign(model: Dict[int, bool], mapping: Dict[int, Tuple[int, int]]) -> Dict[int, int]:
    """Given boolean model and mapping vid->(var,val), return assign[var]=val (last true wins)."""
    assign: Dict[int, int] = {}
    for vid, (var, val) in mapping.items():
        if model.get(vid, False):
            assign[var] = val
    return assign


def main() -> None:
    ap = argparse.ArgumentParser(description="Valida soluciones para GCNF o CNF (reducido).")
    ap.add_argument("--cnf", help="Archivo DIMACS CNF (salida de gcnf_to_cnf).")
    ap.add_argument("--assign", help="Modelo booleano (salida SAT solver).")
    args = ap.parse_args()

    if args.assign and args.cnf:
        cnf, _ = parse_dimacs_cnf(args.cnf)
        model = parse_bool_model(args.assign)
        ok_cnf, bad_cnf = check_cnf(cnf, model)
        print(f"CNF: {'SAT' if ok_cnf else 'NO SAT'}, clausulas malas: {bad_cnf}")
    else:
        ap.error("Usa --cnf instance.cnf --assign assign.txt")


if __name__ == "__main__":
    main()
