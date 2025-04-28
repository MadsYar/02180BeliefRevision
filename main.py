from belief_base import BeliefBase, Belief


def test_success_postulate():
    print("Success Postulate")
    bb = BeliefBase()
    bb.expand(Belief("p", 1))
    bb.expand(Belief("Implies(p,q)", 2))

    # The base explicitly entails 'p' (since 'p' is in the base)
    print("Before contraction, does belief base entail 'p'? :", bb.entails(Belief("p", 1)))

    # Contract by the belief 'p'
    bb.contract(Belief("p", 1))
    result = bb.entails(Belief("p", 1))
    print("After contraction, does belief base entail 'p'? :", result)

    print("Resulting Belief Base:")
    print(bb, "\n")


def test_inclusion_postulate():
    print("Testing Inclusion Postulate")
    bb = BeliefBase()
    bb.expand(Belief("p", 1))
    bb.expand(Belief("Implies(p,q)", 2))
    bb.contract(Belief("p", 1))

    print("Resulting Belief Base:")
    print(bb, "\n")


def test_vacuity_postulate():
    print("Testing Vacuity Postulate")
    bb = BeliefBase()
    bb.expand(Belief("p", 1))
    bb.expand(Belief("Implies(p,q)", 2))
    # The base does not entail 'r'
    if not bb.entails(Belief("r", 1)):
        print("Precondition met: Base does not entail 'r'.")
    else:
        print("Error: Base should not entail 'r'.")

    # Record the current state of the base
    print("Resulting Belief Base:")
    print(bb, "\n")


def test_consistency_postulate():
    print("Testing Consistency Postulate")
    bb = BeliefBase()
    bb.expand(Belief("p", 1))
    bb.expand(Belief("q", 2))
    # Before contraction, ensure that the base is consistent (does not entail False)
    if not bb.entails(Belief("False", 1)):
        print("Belief base is consistent before contraction.")
    else:
        print("Error: Base is inconsistent before contraction.")

    bb.contract(Belief("p", 1))
    print("Resulting Belief Base:")
    print(bb, "\n")

def test_extensionality_postulate():
    print("\nTesting Extensionality Postulate")
    # Create two identical belief bases
    bb1 = BeliefBase()
    bb1.add(Belief("p", 1))
    bb1.add(Belief("Implies(p, q)", 2))

    bb2 = BeliefBase()
    bb2.add(Belief("p", 1))
    bb2.add(Belief("Implies(p, q)", 2))

    # Contract bb1 by p
    bb1.contract(Belief("p", 1))
    # Contract bb2 by ~~p (double negation of p)
    bb2.contract(Belief("Not(Not(p))", 1))

    print("Resulting Belief Base after contracting by p:")
    for belief in bb1.beliefs:
        print(belief)

    print("\nResulting Belief Base after contracting by ~~p:")
    for belief in bb2.beliefs:
        print(belief)

    same = set(str(b) for b in bb1.beliefs) == set(str(b) for b in bb2.beliefs)
    print("\nAre the two belief bases the same?:", same)


def main():
    test_success_postulate()
    test_inclusion_postulate()
    test_vacuity_postulate()
    test_consistency_postulate()
    test_extensionality_postulate()


if __name__ == "__main__":
    main()
