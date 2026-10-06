"""Exact check of the note's Lemma 6.1 (local blocks) and D_2 = -3^10*5 (sympy, rational arithmetic)."""
from sympy import symbols, Rational as Q, residue, Matrix, factorint, simplify
w = symbols('w')
def Lam(j, f):
    S0 = sum((Q(m, 3) - w) ** -3 for m in (1, 2) if m <= j)
    S1 = sum((Q(m, 3) - w) ** -3 for m in (1, 2) if m > j)
    Om = 1 / (w ** 4 * (w - 1) ** 4)
    r0 = residue(f * S0 * Om, w, 0) if S0 != 0 else 0
    r1 = residue(f * S1 * Om, w, 1) if S1 != 0 else 0
    return simplify(r0 - r1)
for j in (0, 1, 2):
    G = Matrix(4, 4, lambda a, b: Lam(j, w ** (a + b)))
    d = G.det()
    print('j', j, 'det', d, factorint(d.p), factorint(d.q))
x = w - Q(1, 2)
mu = {t: Lam(1, x ** t) for t in range(8)}
print('even moments', [mu[t] for t in (0, 2, 4, 6)])
D2 = Matrix([[mu[1], mu[3]], [mu[3], mu[5]]]).det()
print('D2', D2, D2 == -3 ** 10 * 5)
