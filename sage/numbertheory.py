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

def goldbach(x):
    assert x%2==0, "This function only works for even numbers"
    count = 0
    l = prime_range(2, x/2+1)
    s = set(prime_range(x/2, x-1))
    for i in l:
        if x-i in s:
            count+=1
    return count

def mertens(x):
    #see [Crandall - Pomerance, 2005], p.36

    #The list comprehension code causes MemoryErrors when x is very large
    #return sum([moebius(n) for n in range(1, floor(x+1))])

    #The for loop code causes MemoryErrors when x is very large
    #m = 0
    #for n in range(1, floor(x+1)):
    #    m += moebius(n)
    #return m

    m, n = 0, 1
    while n <= floor(x):
        m += moebius(n)
        n += 1
    return m

def reciprocal_prime_sum(x):
    return sum(1/p for p in prime_range(2, x+1))

def max_prime_divisor(x):
    return max(p for p,_ in factor(x))

def prime_product(x):
    prod = 1
    for p in prime_range(2, x+1):
        prod *= p
    return prod

invariants = [goldbach, 
              ('prime_pi',prime_pi),
              ('euler_phi', euler_phi),
              number,
              digits10,
              digits2,
              ('sigma', sigma),
              count_divisors,
              next_prime,
              previous_prime,
              count_quadratic_residues,
              mertens,
              ('li', li),
              ('zeta', zeta),
              reciprocal_prime_sum,
              max_prime_divisor,
              prime_product]

def automatedSearch(objects, invariants, universe, upperBound=True, steps=10, mainInvariant=1):
    for _ in range(steps):
        l = conjecture(objects, invariants, mainInvariant, upperBound=upperBound)
        print(l)
        noCounterExample = True
        for i in universe:
            if any([not c.evaluate(Integer(i)) for c in l]):
                print("Adding {}".format(i))
                objects.append(i)
                universe.remove(i)
                noCounterExample = False
                break
        if noCounterExample:
            print("No counterexample found")
            break
    return l

