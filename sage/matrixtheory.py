
def determinant(m):
    return m.determinant()

def nullity(m):
    return m.nullity()

def rank(m):
    return m.rank()

def trace(m):
    return m.trace()

def nrows(m):
    return m.nrows()

def permanent(m):
    return m.permanent()

def maximum_eigenvalue(m):
    return max(m.eigenvalues())

def minimum_eigenvalue(m):
    return min(m.eigenvalues())

def average_eigenvalue(m):
    evs = m.eigenvalues()
    return sum(evs)/len(evs)

def number_of_distinct_eigenvalues(m):
    return len(set(m.eigenvalues()))

def spectral_radius(m):
    return max(abs(e) for e in m.eigenvalues())

def frobenius_norm(m):
    return sqrt(sum(e*e for e in m.list()))

def l2_norm(m):
    return sqrt(sum(abs(e) for e in m.list()))

def l_inf_norm(m):
    return max(abs(e) for e in m.list())

invariants = [determinant, nullity, rank, trace, nrows, permanent,
              maximum_eigenvalue, minimum_eigenvalue, average_eigenvalue,
              number_of_distinct_eigenvalues, spectral_radius,
              frobenius_norm, l2_norm, l_inf_norm]

