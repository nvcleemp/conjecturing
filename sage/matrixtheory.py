
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
    return float(max(m.eigenvalues()))

def minimum_eigenvalue(m):
    return float(min(m.eigenvalues()))

def average_eigenvalue(m):
    evs = m.eigenvalues()
    return float(sum(evs)/len(evs))

def number_of_distinct_eigenvalues(m):
    return len(set(m.eigenvalues()))

def spectral_radius(m):
    return float(max(abs(e) for e in m.eigenvalues()))

def frobenius_norm(m):
    return sqrt(sum(e*e for e in m.list()))

def l2_norm(m):
    return sqrt(sum(abs(e) for e in m.list()))

def l_inf_norm(m):
    return max(abs(e) for e in m.list())

def max_column_sum(m):
    return max(sum(c) for c in m.columns())

def ratio_min_max_absolute_eigenvalues(m):
    aevs = [abs(ev) for ev in m.eigenvalues()]
    return float(max(aevs)/min(aevs))

def separator(m):
    sevs = sorted(m.eigenvalues())
    return float(sevs[-1] - sevs[-2])


invariants = [determinant, nullity, rank, trace, nrows, permanent,
              maximum_eigenvalue, minimum_eigenvalue, average_eigenvalue,
              number_of_distinct_eigenvalues, spectral_radius,
              frobenius_norm, l2_norm, l_inf_norm, max_column_sum,
              ratio_min_max_absolute_eigenvalues, separator]

