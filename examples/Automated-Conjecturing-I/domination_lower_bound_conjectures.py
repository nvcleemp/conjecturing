'''
This file assumes that the conjecturing spkg and nauty spkg is installed and that 'conjecturing.py' and
'graphtheory.py' are loaded.
'''

def automatedGraphSearch(objects, invariants, minimumVertices, maximumVertices, upperBound=True, steps=10, mainInvariant=1, operators=None):
    for _ in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound, operators=operators)
        noCounterExample = True
        for i in range(minimumVertices, maximumVertices+1):
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

mainInvariant = invariants.index(dominationNumber)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = automatedGraphSearch(objects, invariants, 3, 10, mainInvariant=mainInvariant, steps=100, upperBound=False, operators=operators)

print("The conjectures are stored in the variable conjectures.")
