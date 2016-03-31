'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py' and
'matrixtheory.py' are loaded.
'''

def automatedGraphSearch(objects, invariants, minimumSize, maximumSize, upperBound=True, steps=10, mainInvariant=1, verbose=False, operators=None):
    if verbose:
        print("Starting with these objects:")
        for m in objects:
            print("    {}".format(m.rows()))
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
                print(" *  {}".format(name))
            else:
                print("    {}".format(name))
        print("")
    for _ in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound, operators=operators)
        if verbose:
            print("Found the following conjectures:")
            for c in l:
                print("    {}".format(c))
            print("")
        noCounterExample = True
        for i in range(minimumSize, maximumSize+1):
            if verbose:
                print("Looking for counterexamples of size {}".format(i))
            for m in generateSymmetricMatrices(i):
                try:
                    if any([not c.evaluate(m) for c in l]):
                        print("Adding {}".format(m.rows()))
                        objects.append(m)
                        noCounterExample = False
                        break
                except OverflowError:
                    print("OverflowError: skipping {}".format(m.rows()))
                    continue
                except:
                    print("Error while checking {}".format(m.rows()))
                    raise
            if not noCounterExample: break
        if noCounterExample:
            print("No counterexample found")
            break
    if not noCounterExample:
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound, operators=operators)
        if verbose:
            print("Found the following conjectures:")
            for c in l:
                print("    {}".format(c))
            print("")
    return l

def inverseTriangularNumber(t):
    n = int(sqrt(2*t))
    assert n*(n+1)==2*t, "Not a triangular number: {}".format(t)
    return n


def symmetricMatrixFromList(l):
    n = inverseTriangularNumber(len(l))
    m = [None] * n
    end = 0
    for i in range(n):
        start = end
        end += n - i
        m[i] = [m[j][i] for j in range(i)] + l[start:end]
    return matrix(m)

def int2base21(i, length):
    if not i: return [0] * int(length)
    l = []
    while i:
        l.append(i%21)
        i//=21
    l += [0]* (int(length)-len(l))
    return l

def generateSymmetricMatrices(size):
    length = ((size+1)*size/2)
    count = 21**length
    i = 0
    while i < count:
        yield symmetricMatrixFromList([n-10 for n in int2base21(i, length)])
        i+=1

objects = [matrix([[1,1],[1,1]]), matrix([[-1,1,1],[1,-1,1],[1,1,-1]])]

mainInvariant = invariants.index(determinant)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = automatedGraphSearch(objects, invariants, 2, 4, steps=100, verbose=True, mainInvariant=mainInvariant, operators=operators)

print("The conjectures are stored in the variable conjectures.")
