import re
from itertools import combinations
from typing import Iterator
import sympy
from sympy import And, Or, S, Implies, sympify, Not

# Used to register Implies so that sympy can process formulas like "p → q"
LOCAL_DICT = {"Implies": Implies}


# Manually implementing CNF conversion like the assignment asks for
def eliminate_implications(formula):
    if formula == True or formula == False:
        return formula

    if formula.func == Implies:
        return Or(Not(eliminate_implications(formula.args[0])),
                  eliminate_implications(formula.args[1]))

    elif formula.func in (And, Or):
        return formula.func(*[eliminate_implications(arg) for arg in formula.args])

    elif formula.func == Not:
        return Not(eliminate_implications(formula.args[0]))

    else:
        return formula


def negation_normal_form(formula):
    if formula == True or formula == False:
        return formula

    if formula.func == Not:
        arg = formula.args[0]
        if arg.func == Not:
            return negation_normal_form(arg.args[0])

        elif arg.func == And:
            return Or(*[negation_normal_form(Not(sub_arg)) for sub_arg in arg.args])

        elif arg.func == Or:
            return And(*[negation_normal_form(Not(sub_arg)) for sub_arg in arg.args])

        else:
            return Not(arg)

    elif formula.func in (And, Or):
        return formula.func(*[negation_normal_form(arg) for arg in formula.args])

    else:
        return formula  # Atomic formula or True/False


def distribute_disjunctions(formula):
    if formula == True or formula == False:
        return formula

    if formula.func == Or:
        for i, arg in enumerate(formula.args):
            if arg.func == And:
                other_args = list(formula.args)
                other_args.pop(i)

                if other_args:
                    other_disj = distribute_disjunctions(Or(*other_args))
                    distributed = And(*[distribute_disjunctions(Or(other_disj, conj_arg))
                                        for conj_arg in arg.args])

                else:
                    distributed = distribute_disjunctions(arg)

                return distributed

        return Or(*[distribute_disjunctions(arg) for arg in formula.args])

    elif formula.func == And:
        return And(*[distribute_disjunctions(arg) for arg in formula.args])

    else:
        return formula


def flatten_formulas(formula):
    if formula == True or formula == False:
        return formula

    if formula.func in (And, Or):
        args = []

        for arg in formula.args:
            flattened_arg = flatten_formulas(arg)

            if flattened_arg.func == formula.func:
                args.extend(flattened_arg.args)

            else:
                args.append(flattened_arg)

        return formula.func(*args)

    elif formula.func == Not:
        return Not(flatten_formulas(formula.args[0]))

    else:
        return formula


def cnf(formula):
    formula = eliminate_implications(formula)

    formula = negation_normal_form(formula)

    formula = distribute_disjunctions(formula)

    formula = flatten_formulas(formula)

    return formula


# This is where we implement the Belief Base and its methods

class Belief:
    def __init__(self, belief_str: str, priority: int):
        if belief_str.strip() == "False":
            self.sentence = S.false
        elif belief_str.strip() == "True":
            self.sentence = S.true
        else:
            self.sentence = sympify(self.to_sympy_format(belief_str), evaluate=False, locals=LOCAL_DICT)

        self.priority = priority
        self.cnf = cnf(self.sentence)

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

    def __iter__(self) -> Iterator[Belief]:
        return iter(sorted(self.beliefs, key=lambda b: b.priority))

    def __repr__(self) -> str:
        return "\n".join(str(b) for b in self)

    def remove(self, belief: Belief):
        self.beliefs.remove(belief)

    @staticmethod
    def _get_clauses(expr: sympy.Basic) -> list:
        """
        A list of clauses generated from the logical expression. Each clause is a frozenset. An empty list is 
        returned if the expression is logically True, and a list with one empty frozenset is returned 
        if the expression is logically False.

        :param expr: A sympy logical expression
        :return: A list of clauses from the logic. 
        """
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
        neg_query = cnf(Not(query.sentence))
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
