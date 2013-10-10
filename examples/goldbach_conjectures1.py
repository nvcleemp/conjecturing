'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py'
and 'numbertheory.py' is loaded.
'''

objects = [Integer(4), Integer(12)]

mainInvariant = invariants.index(goldbach) + 1

conjectures = conjecture(objects, invariants, mainInvariant, upperBound=False)

print("The conjectures are stored in the variable conjectures.")
