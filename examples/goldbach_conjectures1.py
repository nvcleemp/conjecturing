'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py'
and 'numbertheory.py' is loaded.
'''

objects = [Integer(4), Integer(12)]

mainInvariant = invariants.index(goldbach)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = conjecture(objects, invariants, mainInvariant, upperBound=False, operators=operators)

print("The conjectures are stored in the variable conjectures.")
