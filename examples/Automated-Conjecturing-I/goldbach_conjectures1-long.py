'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py'
and 'numbertheory.py' is loaded.
'''

def automatedSearch(objects, invariants, mainInvariant, universe, upperBound=True, steps=10, verbose=False, operators=None):
    if verbose:
        print("Starting with these objects:")
        for i in objects:
            print(" {}".format(i))
        print("")
        print("Available invariants:")
        for pos, invariant in enumerate(invariants):
            if type(invariant) == tuple:
                name, _ = invariant
            elif hasattr(invariant, '__name__'):
                name = invariant.__name__
            else:
                name = 'invariant_{}'.format(pos)
            if pos + 1 == mainInvariant:
                print(" * {}".format(name))
            else:
                print("   {}".format(name))
        print("")
    for step in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound, operators=operators)
        if verbose:
            print("Found the following conjectures:")
            for c in l:
                print(" {}".format(c))
            print("")
        noCounterExample = True
        for i in universe:
            if any([not c.evaluate(Integer(i)) for c in l]):
                print "Step {}: Adding {}".format(step+1, i)
                objects.append(i)
                universe.remove(i)
                noCounterExample = False
                break
        if noCounterExample:
            print "No counterexample found"
            break
    return l

objects = [Integer(4)]
universe = [Integer(n) for n in range(4, 1000001, 2)]

for n in objects:
    universe.remove(n)

mainInvariant = invariants.index(goldbach)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = automatedSearch(objects, invariants, mainInvariant, universe, steps=200, verbose=True, upperBound=False, operators=operators)

print("The conjectures are stored in the variable conjectures.")
