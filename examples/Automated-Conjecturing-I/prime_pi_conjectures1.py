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

invariants = [('prime_pi',prime_pi), ('euler_phi', euler_phi), number, digits10, digits2, ('sigma', sigma), count_divisors, next_prime, previous_prime, count_quadratic_residues]

_objects = [5, 12, 30, 50, 7, 16, 24, 48, 17, 3, 8, 6, 11, 19, 23, 29, 31, 32, 41, 43, 46, 47, 53, 59, 61, 64, 66, 54, 45, 58, 60, 62, 67, 71, 73, 78, 79, 80, 63, 82, 83, 89, 97, 98, 99, 100, 101, 102, 84, 90, 103, 104, 105, 106, 107, 108, 109, 13, 111, 112, 113, 114, 115, 117, 127, 120, 135, 137, 138, 139, 144, 149, 151, 157, 160, 163, 167, 173, 174, 175, 176, 179, 168, 178, 180, 181, 191, 184, 192, 193, 194, 197, 198, 199, 77, 204, 208, 210, 211, 216, 223, 224, 227, 229, 233, 239, 240, 241, 247, 251, 272, 277, 278, 281, 271, 283, 288, 313, 317, 331, 337, 347, 349, 352, 353, 358, 359, 360, 367, 368, 373, 379, 383, 389, 397, 400, 401, 408, 409, 414, 419, 420, 421, 424, 431, 426, 432, 328, 376, 385, 433, 439]
objects = [Integer(n) for n in _objects]

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = conjecture(objects, invariants, 0, operators=operators)

print("The conjectures are stored in the variable conjectures.")
