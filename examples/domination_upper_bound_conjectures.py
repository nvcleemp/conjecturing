'''
This file assumes that the conjecturing spkg and nauty spkg is installed and that 'conjecturing.py' and
'graphtheory.py' are loaded.
'''

def automatedGraphSearch(objects, invariants, minimumVertices, maximumVertices, upperBound=True, steps=10, mainInvariant=1, verbose=False):
    if verbose:
        print("Starting with these objects:")
        for g in objects:
            print("    {}: {}".format(g, g.graph6_string()))
        print()
        print("Available invariants:")
        for pos, invariant in enumerate(invariants):
            if type(invariant) == tuple:
                name, _ = invariant
            elif hasattr(invariant, '__name__'):
                name = invariant.__name__
            else:
                name = 'invariant_{}'.format(pos)
            if pos + 1 == mainInvariant:
                print(" *  {}".format(name))
            else:
                print("    {}".format(name))
        print()
    for _ in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound)
        if verbose:
            print("Found the following conjectures:")
            for c in l:
                print("    {}".format(c))
            print()
        noCounterExample = True
        for i in range(minimumVertices, maximumVertices+1):
            if verbose:
                print("Looking for counterexamples with {} {}".format(i, "vertex" if i==1 else "vertices"))
            for g in graphs.nauty_geng('-c {}'.format(i)):
                if any([not c.evaluate(g) for c in l]):
                    print "Adding {}: {}".format(g, g.graph6_string())
                    objects.append(g)
                    noCounterExample = False
                    break
            if not noCounterExample: break
        if noCounterExample:
            print "No counterexample found"
            break
    return l

objects = [graphs.CompleteGraph(3)]

knownUpperBounds = [matching_number, annihilation_number, fractional_alpha, lovasz_theta, cvetkovic]
for bound in knownUpperBounds:
    invariants.remove(bound)
mainInvariant = invariants.index(dominationNumber) + 1

conjectures = automatedGraphSearch(objects, invariants, 3, 10, mainInvariant=mainInvariant, steps=100, verbose=True)

print("The conjectures are stored in the variable conjectures.")
