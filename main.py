import random
import time
import tracemalloc
from itertools import combinations
from typing import List, Set, Dict, Tuple, Optional
from copy import deepcopy

Clause = Set[int]
Formula = List[Clause]
Assignment = Dict[int, bool]

# ------------------ UTILITARE ------------------
def generate_random_cnf(n_vars: int, n_clauses: int, clause_len: int = 3) -> Formula:
    formula = []
    seen_clauses = set()
    redundant_count = 0
    attempts = 0
    max_attempts = n_clauses * 10

    while len(formula) < n_clauses and attempts < max_attempts:
        clause = set()
        while len(clause) < clause_len:
            var = random.randint(1, n_vars)
            lit = var * random.choice([-1, 1])
            clause.add(lit)

        if any(-lit in clause for lit in clause):
            redundant_count += 1
            attempts += 1
            continue

        frozen = frozenset(clause)
        if frozen in seen_clauses:
            redundant_count += 1
            attempts += 1
            continue

        formula.append(clause)
        seen_clauses.add(frozen)
        attempts += 1

    print(f"Formula generată cu {len(formula)} clauze unice (eliminate {redundant_count} redundante)")
    return formula

def simplify_formula(formula: Formula, literal: int) -> Optional[Formula]:
    new_formula = []
    for clause in formula:
        if literal in clause:
            continue
        new_clause = clause - {-literal}
        if not new_clause:
            return None
        new_formula.append(new_clause)
    return new_formula

# ------------------ ALGORITMUL DE REZOLUȚIE ------------------
def resolution_solver(formula: Formula) -> Tuple[bool, Dict[str, int]]:
    stats = {'decisions': 0, 'backtracks': 0}
    clauses = {frozenset(c) for c in formula}
    new_clauses = set()

    while True:
        derived = set()
        for ci, cj in combinations(clauses, 2):
            for lit in ci:
                if -lit in cj:
                    resolvent = (ci | cj) - {lit, -lit}
                    if not resolvent:
                        return False, stats
                    derived.add(frozenset(resolvent))

        if not derived:
            return True, stats

        if derived.issubset(clauses):
            return True, stats

        stats['decisions'] += len(derived)
        clauses.update(derived)

# ------------------ ALGORITMUL DP ------------------
#    def dp_solver(formula: Formula) -> Tuple[bool, Dict[str, int]]:
#        stats = {'decisions': 0, 'backtracks': 0}
#        if not formula:
#            return True, stats
#
#        variables = {abs(lit) for clause in formula for lit in clause}
#        for var in sorted(variables, key=lambda x: -sum(x in clause or -x in clause for clause in formula)):
#            stats['decisions'] += 1
#
#            pos = [c for c in formula if var in c]
#            neg = [c for c in formula if -var in c]
#            other = [c for c in formula if var not in c and -var not in c]
#
#            new_clauses = []
#            for p in pos:
#                for n in neg:
#                    resolvent = (p | n) - {var, -var}
#                    if not resolvent:
#                        return False, stats
#                    new_clauses.append(resolvent)
#
#           formula = other + new_clauses
#
#        return True, stats

# ------------------ ALGORITMUL DP OPTIMIZAT ------------------
def dp_solver_optimized(formula: Formula) -> Tuple[bool, Dict[str, int]]:
    stats = {'decisions': 0, 'backtracks': 0}
    assignment = {}

    def unit_propagate(formula: Formula, assignment: Assignment) -> Optional[Formula]:
        changed = True
        while changed:
            changed = False
            unit_clauses = [c for c in formula if len(c) == 1]
            for clause in unit_clauses:
                lit = next(iter(clause))
                var = abs(lit)
                val = lit > 0
                if var in assignment:
                    if assignment[var] != val:
                        return None
                    continue
                assignment[var] = val
                formula = simplify_formula(formula, lit)
                if formula is None:
                    return None
                changed = True
        return formula

    def pure_literal_elimination(formula: Formula, assignment: Assignment) -> Optional[Formula]:
        literal_count = {}
        for clause in formula:
            for lit in clause:
                literal_count[lit] = literal_count.get(lit, 0) + 1

        pures = {lit for lit in literal_count if -lit not in literal_count}
        for lit in pures:
            var = abs(lit)
            if var not in assignment:
                assignment[var] = (lit > 0)
                formula = simplify_formula(formula, lit)
                if formula is None:
                    return None
        return formula

    formula = unit_propagate(formula, assignment)
    if formula is None:
        stats['backtracks'] += 1
        return False, stats
    if not formula:
        return True, stats

    formula = pure_literal_elimination(formula, assignment)
    if formula is None:
        stats['backtracks'] += 1
        return False, stats
    if not formula:
        return True, stats

    variables = {abs(lit) for clause in formula for lit in clause}
    for var in sorted(variables, key=lambda x: -sum(x in clause or -x in clause for clause in formula)):
        stats['decisions'] += 1

        pos = [c for c in formula if var in c]
        neg = [c for c in formula if -var in c]
        other = [c for c in formula if var not in c and -var not in c]

        new_clauses = []
        for p in pos:
            for n in neg:
                resolvent = (p | n) - {var, -var}
                if not resolvent:
                    return False, stats
                new_clauses.append(resolvent)

        formula = other + new_clauses

        formula = unit_propagate(formula, assignment)
        if formula is None:
            stats['backtracks'] += 1
            return False, stats
        if not formula:
            return True, stats

        formula = pure_literal_elimination(formula, assignment)
        if formula is None:
            stats['backtracks'] += 1
            return False, stats
        if not formula:
            return True, stats

    return True, stats

# ------------------ ALGORITMUL DPLL ------------------
class DPLLSolver:
    def __init__(self):
        self.stats = {'decisions': 0, 'propagations': 0, 'backtracks': 0}

    def unit_propagate(self, formula: Formula, assignment: Assignment) -> Tuple[Optional[Formula], Optional[Assignment]]:
        changed = True
        while changed:
            changed = False
            for clause in formula:
                if len(clause) == 1:
                    lit = next(iter(clause))
                    var = abs(lit)
                    if var not in assignment:
                        self.stats['propagations'] += 1
                        assignment[var] = (lit > 0)
                        formula = simplify_formula(formula, lit)
                        if formula is None:
                            return None, None
                        changed = True
                        break
        return formula, assignment

    def pure_literal_elimination(self, formula: Formula, assignment: Assignment) -> Tuple[Optional[Formula], Optional[Assignment]]:
        literal_counts = {}
        for clause in formula:
            for lit in clause:
                literal_counts[lit] = literal_counts.get(lit, 0) + 1

        for lit, count in literal_counts.items():
            if -lit not in literal_counts:
                var = abs(lit)
                if var not in assignment:
                    assignment[var] = (lit > 0)
                    formula = simplify_formula(formula, lit)
                    if formula is None:
                        return None, None
        return formula, assignment

    def solve(self, formula: Formula, assignment: Optional[Assignment] = None) -> bool:
        if assignment is None:
            assignment = {}

        formula, assignment = self.unit_propagate(formula, assignment)
        if formula is None:
            self.stats['backtracks'] += 1
            return False
        if not formula:
            return True

        formula, assignment = self.pure_literal_elimination(formula, assignment)
        if formula is None:
            self.stats['backtracks'] += 1
            return False
        if not formula:
            return True

        var = self.choose_variable(formula, assignment)
        self.stats['decisions'] += 1

        new_assignment = assignment.copy()
        new_assignment[var] = True
        new_formula = simplify_formula(deepcopy(formula), var)
        if new_formula is not None and self.solve(new_formula, new_assignment):
            return True

        new_assignment = assignment.copy()
        new_assignment[var] = False
        new_formula = simplify_formula(deepcopy(formula), -var)
        if new_formula is not None and self.solve(new_formula, new_assignment):
            return True

        self.stats['backtracks'] += 1
        return False

    def choose_variable(self, formula: Formula, assignment: Assignment) -> int:
        for clause in formula:
            for lit in clause:
                var = abs(lit)
                if var not in assignment:
                    return var
        return 1

class DPLLRandom(DPLLSolver):
    def choose_variable(self, formula: Formula, assignment: Assignment) -> int:
        unassigned = [abs(lit) for clause in formula for lit in clause if abs(lit) not in assignment]
        return random.choice(unassigned) if unassigned else 1

class DPLLMOMS(DPLLSolver):
    def choose_variable(self, formula: Formula, assignment: Assignment) -> int:
        min_len = min(len(c) for c in formula)
        freq = {}
        for clause in formula:
            if len(clause) == min_len:
                for lit in clause:
                    var = abs(lit)
                    if var not in assignment:
                        freq[var] = freq.get(var, 0) + 1
        return max(freq.items(), key=lambda x: x[1])[0] if freq else super().choose_variable(formula, assignment)

class DPLLVSIDS(DPLLSolver):
    def __init__(self):
        super().__init__()
        self.vsids_scores = {}
        self.decay_factor = 0.95

    def choose_variable(self, formula: Formula, assignment: Assignment) -> int:
        for clause in formula:
            for lit in clause:
                var = abs(lit)
                if var not in assignment:
                    self.vsids_scores[var] = self.vsids_scores.get(var, 0) + 1

        for var in self.vsids_scores:
            self.vsids_scores[var] *= self.decay_factor

        return max(self.vsids_scores.items(), key=lambda x: x[1])[0] if self.vsids_scores else super().choose_variable(formula, assignment)

# ------------------ EXPERIMENT ------------------

def _run_solver(solver, formula):
    result = solver.solve(formula)
    return result, solver.stats

def print_results_table(results, n_vars):
    print("\nREZULTATE COMPARATIVE")
    print("-" * 100)
    print(f"{'Algoritm':<15} | {'Clauze':<6} | {'Vars':<6} | {'SAT':<5} | {'Timp (s)':<10} | {'Memorie (KB)':<12} | {'Decizii':<8} | {'Backtracks'}")
    print("-" * 100)

    for name, data in results.items():
        for i in range(len(data['time'])):
            sat_status = "SAT" if data['sat'][i] else "UNSAT"
            print(f"{name:<15} | {data['clauses'][i]:<6} | {n_vars:<6} | {sat_status:<5} | {data['time'][i]:<10.4f} | {data['memory'][i]:<12.1f} | {data['decisions'][i]:<8} | {data['backtracks'][i]}")

    print("\nDistribuție SAT/UNSAT pentru fiecare algoritm:")
    for name, data in results.items():
        total = len(data['sat'])
        sat_count = sum(data['sat'])
        unsat_count = total - sat_count
        print(f"  {name}: {sat_count}/{total} SAT ({sat_count/total*100:.1f}%), {unsat_count}/{total*100:.1f}% UNSAT")


def save_results_to_file(results, filename="C:\\Users\\NumeUtilizator\\Downloads\\results.txt"):
    with open(filename, "a", encoding="utf-8") as f:  
        f.write("\nREZULTATE COMPARATIVE\n")
        f.write("-" * 100 + "\n")
        f.write(f"{'Algoritm':<15} | {'Variabile':<10} | {'Clauze':<6} | {'SAT':<5} | {'Timp (s)':<10} | {'Memorie (KB)':<12} | {'Decizii':<8} | {'Backtracks'}\n")
        f.write("-" * 100 + "\n")

        for name, data in results.items():
            for i in range(len(data['time'])):
                sat_status = "SAT" if data['sat'][i] else "UNSAT"
                f.write(f"{name:<15} | {data['vars'][i]:<10} | {data['clauses'][i]:<6} | {sat_status:<5} | {data['time'][i]:<10.4f} | {data['memory'][i]:<12.1f} | {data['decisions'][i]:<8} | {data['backtracks'][i]}\n")

        f.write("\nDistribuție SAT/UNSAT pentru fiecare algoritm:\n")
        for name, data in results.items():
            total = len(data['sat'])
            sat_count = sum(data['sat'])
            unsat_count = total - sat_count
            f.write(f"  {name}: {sat_count}/{total} SAT ({sat_count/total*100:.1f}%), {unsat_count}/{total*100:.1f}% UNSAT\n")

def run_experiment():
    n_vars = int(input("Introduceti numarul de variabile (n_vars): "))
    
    clause_counts = list(range(2, 28, 4))

    strategies = {
        'Rezolutie': resolution_solver,
        #'DP': dp_solver,
        'DP-Optimizat': dp_solver_optimized,
        'DPLL-First': lambda f: _run_solver(DPLLSolver(), f),
        'DPLL-Random': lambda f: _run_solver(DPLLRandom(), f),
        'DPLL-MOMS': lambda f: _run_solver(DPLLMOMS(), f),
        'DPLL-VSIDS': lambda f: _run_solver(DPLLVSIDS(), f)
    }

    results = {
        name: {'time': [], 'memory': [], 'clauses': [], 'vars': [], 'decisions': [], 'backtracks': [], 'sat': []}
        for name in strategies
    }

    for n_clauses in clause_counts:
        print(f"\nProcesez {n_clauses} clauze...")
        formula = generate_random_cnf(n_vars, n_clauses)

        for name, solver in strategies.items():
            if name == "Rezolutie" and n_clauses > 8:
                print(f"  Rulez {name}... Omit din cauza limitării (clauze > 8)")
                continue

            print(f"  Rulez {name} cu {n_vars} variabile și {n_clauses} clauze...", end=' ', flush=True)
            f = deepcopy(formula)

            tracemalloc.start()
            start_time = time.perf_counter()

            try:
                result, stats = solver(f)
                elapsed = time.perf_counter() - start_time
                _, peak_mem = tracemalloc.get_traced_memory()

                results[name]['time'].append(elapsed)
                results[name]['memory'].append(peak_mem / 1024)
                results[name]['clauses'].append(n_clauses)
                results[name]['vars'].append(n_vars)  # Adăugăm numărul de variabile
                results[name]['decisions'].append(stats.get('decisions', 0))
                results[name]['backtracks'].append(stats.get('backtracks', 0))
                results[name]['sat'].append(result)

                print(f"Done ({elapsed:.2f}s) — {'SAT' if result else 'UNSAT'}")
            except Exception as e:
                print(f"Eroare la {name}: {str(e)}")
            finally:
                tracemalloc.stop()

    # După finalizarea experimentului, salvăm rezultatele într-un fișier
    save_results_to_file(results)

    return results

if __name__ == "__main__":
    import time
    random.seed(time.time())
    print("Începe experimentul...")
    results = run_experiment()
    print("Experiment completat cu succes!")
