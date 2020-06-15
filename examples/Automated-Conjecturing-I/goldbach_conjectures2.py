'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py'
and 'numbertheory.py' is loaded.
'''

objects = [Integer(n) for n in [4, 6, 8, 12, 38, 32, 68]]

invariants.remove(digits10)
mainInvariant = invariants.index(goldbach)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = conjecture(objects, invariants, mainInvariant, upperBound=False, operators=operators)

print("The conjectures are stored in the variable conjectures.")
