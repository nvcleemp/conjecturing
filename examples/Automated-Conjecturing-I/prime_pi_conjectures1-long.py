'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py' is loaded.
'''

def digits10(n):
    return len(n.digits(10))

def digits2(n):
    return len(n.digits(2))

def count_divisors(n):
    return len(divisors(n))

def count_prime_divisors(n):
    return len(factor(n))

def count_quadratic_residues(n):
    return len(quadratic_residues(n))

def number(n):
    return n

def automatedSearch(objects, invariants, universe, upperBound=True, steps=10, mainInvariant=0, operators=None):
    for _ in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound, operators=operators)
        noCounterExample = True
        for i in universe:
            if any([not c.evaluate(Integer(i)) for c in l]):
                print "Adding {}".format(i)
                objects.append(i)
                universe.remove(i)
                noCounterExample = False
                break
        if noCounterExample:
            print "No counterexample found"
            break
    return l

invariants = [('prime_pi',prime_pi), ('euler_phi', euler_phi), number, digits10, digits2, ('sigma', sigma), count_divisors, next_prime, previous_prime, count_quadratic_residues]

objects = [Integer(n) for n in [5, 12, 30, 50]]
universe = [Integer(n) for n in range(3, 1000001)]

for n in objects:
    universe.remove(n)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = automatedSearch(objects, invariants, universe, steps=210, operators=operators)

print("The conjectures are stored in the variable conjectures.")
