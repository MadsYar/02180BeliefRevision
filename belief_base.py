import re
from itertools import combinations
from typing import Iterator 


from sympy import And, Or, S, Implies, sympify, to_cnf, Not

# Used to register Implies so that sympy can process formulas like "p → q"
LOCAL_DICT = {"Implies": Implies}


class Belief:
    def __init__(self, belief_str: str, priority: int):
        self.sentence = sympify(self.to_sympy_format(belief_str), evaluate=False, locals=LOCAL_DICT)
        self.priority = priority
        self.cnf = to_cnf(self.sentence, simplify=True)

    def __repr__(self) -> str:
        return f"{self.sentence} ({self.priority})"

    @staticmethod
    def to_sympy_format(formula: str) -> str:
        # Trim, normalize, and replace logical symbols with Pythonic
        formula = formula.strip()
        formula = formula.replace('→', '>>').replace('->', '>>').replace('implies', '>>')
        formula = formula.replace('¬', '~').replace('!', '~')
        formula = formula.replace('V', '|').replace('v', '|').replace('∨', '|').replace('or', '|')
        formula = formula.replace('∧', '&').replace('and', '&')
        formula = re.sub(r'\s*>>\s*', '>>', formula)
        formula = re.sub(r'(\w+|\([^()]*\))>>(\w+|\([^()]*\))', r'Implies(\1,\2)', formula)
        return formula


class BeliefBase:
    def __init__(self):
        self.beliefs: list[Belief] = []

    def add(self, belief: Belief):
        self.beliefs.append(belief)

    def remove(self, belief: Belief):
        self.beliefs.remove(belief)

    def __len__(self) -> int:
        return len(self.beliefs)

    def __iter__(self) -> Iterator[Belief]:
        return iter(sorted(self.beliefs, key=lambda b: b.priority))

    def __repr__(self) -> str:
        return "\n".join(str(b) for b in self)

    @staticmethod
    def _get_clauses(expr):
        clauses = []
        if expr == True or expr == S.true:
            return []
        if expr == False or expr == S.false:
            return [frozenset()]
        if expr.func == And:
            for arg in expr.args:
                clauses.extend(BeliefBase._get_clauses(arg))
        elif expr.func == Or:
            lits = set()
            for arg in expr.args:
                lits.add(arg)
            clauses.append(frozenset(lits))
        else:
            clauses.append(frozenset([expr]))
        return clauses

    @staticmethod
    def _resolve_clause(c1, c2):
        resolved_clauses = set()
        for lit1 in c1:
            for lit2 in c2:
                if (lit1 == Not(lit2)) or (lit2 == Not(lit1)):
                    new_clause = (c1.union(c2)) - {lit1, lit2}
                    resolved_clauses.add(frozenset(new_clause))
        return resolved_clauses

    @staticmethod
    def _resolution(clauses):
        clauses = list(map(frozenset, clauses))
        new = set()
        while True:
            for ci, cj in combinations(clauses, 2):
                resolved_clauses = BeliefBase._resolve_clause(ci, cj)
                if frozenset() in resolved_clauses:
                    return True
                new = new.union(resolved_clauses)
            if new.issubset(set(clauses)):
                return False
            clauses = list(set(clauses) | new)
            new = set()

    # --- Belief Revision Methods (Entailment, Contraction, Expansion) ---

    def entails(self, query: Belief) -> bool:
        neg_query = to_cnf(Not(query.sentence), simplify=True)
        clauses = []
        for b in self.beliefs:
            clauses.extend(BeliefBase._get_clauses(b.cnf))
        clauses.extend(BeliefBase._get_clauses(neg_query))
        return BeliefBase._resolution(clauses)

    def contract(self, target: Belief):
        while self.entails(target):
            removed = False
            # Try removing beliefs one by one, according to their priority.
            for b in self:
                temp_base = BeliefBase()
                temp_base.beliefs = self.beliefs.copy()
                temp_base.remove(b)
                if not temp_base.entails(target):
                    self.remove(b)
                    removed = True
                    break
            if not removed:
                break

    def expand(self, belief: Belief):
        self.add(belief)
