"""Independent exact check of the note's Theorem 6.2 (strict dominance, c = q pair design) for p=3, q=4, d=1.
Written from the note's Lemma 2.2 only.  L(x^m) = sum_k sum_{a<=3} c_{k,a} C(m,a)(-k)^{m-a},
c_{k,a} = -sum_{i=1}^{4-a} i H_k[4-i-a] (I_{i+1} + S_k(i+1)), with I_2 dropped (its total coefficient is
-sum_k r_{k,1} = 0), I_3 = I_5 = 0, I_4 = 4*3^5*X.  Then Delta_K(X) = det[L(x^{i+j})]_{i,j<K}, K = 4(3n+1-l).
Claim: v_l([X^0]) = -28 * #pairs and v_l([X^i]) > v_l([X^0]) for i >= 1.
usage: python check_nv.py n l"""
import sys, math
from fractions import Fraction as Fr
import flint
n, l = int(sys.argv[1]), int(sys.argv[2])
R = 3 * n // 2; Ks = list(range(-R, R + 1))
assert l > R and l >= 7 and 3 * (l - R) <= l and all(l % r for r in range(2, int(l ** .5) + 1))
def vp(x, pr):
    x = Fr(x)
    if x == 0: return None
    a, b, v = x.numerator, x.denominator, 0
    while a % pr == 0: a //= pr; v += 1
    while b % pr == 0: b //= pr; v -= 1
    return v
def H(k):   # [u^b] u^4 W(-k+u) = prod_{m != k} (m-k+u)^-4, b < 4
    s = [Fr(1), Fr(0), Fr(0), Fr(0)]
    for m in Ks:
        if m == k: continue
        c = Fr(m - k); ser = [Fr(math.comb(3 + j, j) * (-1) ** j) / c ** (4 + j) for j in range(4)]
        s = [sum(s[i] * ser[j - i] for i in range(j + 1)) for j in range(4)]
    return s
def S(k, M):
    if k == 0: return Fr(0)
    tot = sum(Fr(1, mm ** (M + 1)) for mm in range(1, 3 * abs(k)) if mm % 3)
    return -M * 3 ** (M + 1) * tot if k > 0 else M * (-1) ** (M + 1) * 3 ** (M + 1) * tot
# c_{k,a} = beta + X alpha
beta, alpha = {}, {}
for k in Ks:
    h = H(k)
    for a in range(4):
        b_, al = Fr(0), Fr(0)
        for i in range(1, 5 - a):
            M = i + 1
            b_ += -i * h[4 - i - a] * S(k, M)
            if M == 4: al += -i * h[4 - i - a] * 4 * 3 ** 5
        beta[k, a], alpha[k, a] = b_, al
K = 4 * (3 * n + 1 - l)
def mom(m, tab):
    return sum(tab[k, a] * math.comb(m, a) * (-k) ** (m - a) for k in Ks for a in range(4) if a <= m)
B = [mom(m, beta) for m in range(2 * K - 1)]; A = [mom(m, alpha) for m in range(2 * K - 1)]
# interpolate Delta(X) at X = 0..K
pts = list(range(K + 1)); vals = []
for X in pts:
    Mx = flint.fmpq_mat(K, K, [flint.fmpq((B[i + j] + X * A[i + j]).numerator, (B[i + j] + X * A[i + j]).denominator) for i in range(K) for j in range(K)])
    vals.append(Fr(int(Mx.det().p), int(Mx.det().q)))
# Lagrange -> coefficients via exact Newton/Vandermonde solve
V = flint.fmpq_mat(K + 1, K + 1, [x ** e for x in pts for e in range(K + 1)])
y = flint.fmpq_mat(K + 1, 1, [flint.fmpq(v.numerator, v.denominator) for v in vals])
coef = V.solve(y)
cs = [Fr(int(coef[e, 0].p), int(coef[e, 0].q)) for e in range(K + 1)]
v = [vp(c, l) for c in cs]
pairs = 3 * n + 1 - l
print(f'n={n} l={l} K={K} pairs={pairs}  v_l([X^0])={v[0]}  expected {-28 * pairs}')
print('  v_l of X^i coefficients:', v)
ok = v[0] == -28 * pairs and all(x is None or x > v[0] for x in v[1:])
print('  VERDICT:', 'PASS' if ok else 'FAIL')
