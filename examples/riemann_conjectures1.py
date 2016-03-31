'''
This file assumes that the conjecturing spkg is installed and that 'conjecturing.py'
and 'numbertheory.py' is loaded.
'''

def riemann(x):
    return abs(prime_pi(x)-li(x)+li(2))

invariants = [riemann] + invariants

objects = [3, 10, 16, 28, 27, 29, 36, 37, 11, 13, 17, 18, 30, 31, 5, 35, 4, 12, 32, 34, 38, 39, 40, 41, 46, 42, 49, 50, 51, 52, 53, 54, 57, 58, 59, 60, 62, 63, 64, 65, 66, 70, 72, 78, 71, 61, 79, 80, 81, 88, 89, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 121, 122, 123, 124, 125, 110, 114, 115, 117, 126, 127, 128, 129, 130, 131, 113, 134, 135, 136, 137, 139, 144, 145, 146, 147, 148, 149, 151, 161, 102, 138, 162, 166, 174, 175, 176, 177, 178, 179, 180, 182, 187, 189, 9, 190, 191, 169, 192, 193, 195, 197, 198, 200, 208, 210, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 6, 229, 228, 239, 241, 243, 251, 256, 288, 290, 305, 306, 307, 252, 254, 329, 330, 331, 336, 337, 343, 344, 345, 346, 347, 348, 349, 304, 360, 375, 400, 416, 418, 419, 420, 430, 432, 435, 438, 439, 442, 443, 444, 537, 538, 429, 539, 540, 541, 545, 551, 553, 529, 554, 555, 556, 557, 560, 562, 561, 567, 569, 568, 570, 571, 314, 576, 617, 625, 648, 665, 667]
objects = [Integer(n) for n in objects]

invariants.remove(('li', li))
invariants.remove(('prime_pi', prime_pi))
invariants.remove(goldbach) #only for even numbers

mainInvariant = invariants.index(riemann)

operators = { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
    '+', '*', 'max', 'min', '-', '/', '^'}

conjectures = conjecture(objects, invariants, mainInvariant, upperBound=True, operators=operators)

print("The conjectures are stored in the variable conjectures.")
