import re
from itertools import combinations

from sympy import And, Or, S, Implies, sympify, to_cnf, Not

# Used to store Implies so that sympy can process formulas like "p → q"
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
        """
        Parse and replacing characters in string, so it can encapsulate as a sympy object.
        :param formula: Raw proportional logic string.
        :return: A proportional logical string compatible with sympy.
        """

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
        self.beliefs: set[Belief] = set()

    def __len__(self) -> int:
        return len(self.beliefs)

    def __iter__(self) -> iter(list[Belief]):
        return iter(sorted(self.beliefs, key=lambda b: b.priority))

    def __repr__(self) -> str:
        return "\n".join(str(b) for b in self)

    def remove(self, belief: Belief):
        self.beliefs.remove(belief)

    @staticmethod
    def _get_clauses(expr) -> list:
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
        """
        Here is where we check if the first clause and the second clause as the same symbol literal, but one is a "not" of
        the literal. Then generate the new clause.
        :param c1: First clause
        :param c2: Second clause
        :return: The newly generated clause without the literal.
        """
        resolved_clauses = set()
        for lit1 in c1:  # Literals in the first clause
            for lit2 in c2:  # Literals in the second clause
                if (lit1 == Not(lit2)) or (lit2 == Not(lit1)):  # Eg. lit1 = P, lit2 = ~P, or vice versa
                    new_clause = (c1.union(c2)) - {lit1, lit2}
                    resolved_clauses.add(frozenset(new_clause))
        return resolved_clauses

    @staticmethod
    def _resolution(clauses) -> bool:
        """
        Iterate with two clauses at a time, check whether the first clause has a literal symbol, and the second clause
        has a ~literal symbol, then we generate a new clause with everything from the first and second clause
        except the literal and ~literal.

        This happens until no new clauses are generated.
        :param clauses: A set of clauses
        :return:
        """
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

    def entails(self, query: Belief) -> bool:
        """
        1. Convert the belief into CNF
        2. Place all the CNF clauses into a set of clauses
        3. Call _resolution()
        :param query: A belief to check entitlement on
        :return: whether the new sentence can be entailed.
        """
        # Belief class does to_cnf() in __init__ but, we need to convert CNF of ~(belief)
        neg_query = to_cnf(Not(query.sentence), simplify=True)
        clauses = []  # list of lists
        for b in self.beliefs:
            clauses.extend(BeliefBase._get_clauses(b.cnf))
        clauses.extend(BeliefBase._get_clauses(neg_query))
        return BeliefBase._resolution(clauses)

    def contract(self, target: Belief):
        """
        Remove belief from the belief base under the condition we can't entail belief.
        :param target: A belief to remove from the belief base
        :return:
        """
        while self.entails(target):
            removed = False
            # Removing beliefs one by one based on their priority.
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

    def expand(self, *belief: Belief):
        """
        Just the union between current belief base and new belief
        :param belief: A new belief to be added
        """
        self.beliefs = self.beliefs.union(belief)
