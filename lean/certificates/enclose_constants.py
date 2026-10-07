"""Rigorous enclosure of the constants in the zeta_3(5) budget, in exact rational arithmetic.
log 2, log 3, log 5: atanh series with explicit tail bounds. Euler gamma: Euler-Maclaurin with N = 1024 and
remainder 0 <= gamma - A_N <= 1/(132 N^10). Proves c(6) < 71.075041 and the margin > 7.93.
usage: python enclose_constants.py cert_c_p3_q4_d1_a1.5_k6.0.json"""
from fractions import Fraction as Q

import json, sys

def add(a, b):
    return a[0] + b[0], a[1] + b[1]

def neg(a):
    return -a[1], -a[0]

def sub(a, b):
    return add(a, neg(b))

def scale(c, a):
    vals = (c*a[0], c*a[1])
    return min(vals), max(vals)

def div(a, b):
    assert b[0] > 0
    vals = [x/y for x in a for y in b]
    return min(vals), max(vals)

def point(x):
    return Q(x), Q(x)

def log_interval(x, terms=200):
    t = Q(x-1, x+1)
    s = 2*sum(t**(2*j+1)/Q(2*j+1) for j in range(terms))
    tail = 2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
    return s, s+tail

def fixed(z, digits=35):
    sign = "-" if z < 0 else ""
    z = abs(z)
    return sign + str(z//10**digits) + "." + str(z%10**digits).zfill(digits)

def show(name, a, digits=35):
    lo = a[0]*10**digits
    hi = a[1]*10**digits
    flo = lo.numerator//lo.denominator
    cei = -((-hi.numerator)//hi.denominator)
    print(name, "[", fixed(flo, digits), ",", fixed(cei, digits), "]")

C = json.load(open(sys.argv[1]))
assert (C["p"], C["q"], C["d"]) == (3, 4, 1)
assert Q(C["a"]) == Q(3, 2) and Q(C["kappa"]) == 6
subs = [s for cell in C["cells"] for s in cell["subcells"]]
assert len(C["cells"]) == 120 and len(subs) == 2880
assert all(Q(s["lam"]) >= 0 for s in subs)
step = sum((Q(s["b"])-Q(s["a"]))*Q(s["h"]) for s in subs)
assert step == Q(C["step"])
assert step < Q(196761611117789, 10**12)

l2, l3, l5 = (log_interval(x) for x in (2, 3, 5))
l20 = add(scale(2, l2), l5)
N = 1024
H = sum(Q(1, k) for k in range(1, N+1))
correction = -Q(1, 2*N) + Q(1, 12*N**2) - Q(1, 120*N**4)
correction += Q(1, 252*N**6) - Q(1, 240*N**8)
A = sub(point(H+correction), scale(10, l2))
gamma = A[0], A[1]+Q(1, 132*N**10)

Fbits = div(sub(point(54), scale(36, l3)), l2)
lhs = div(scale(63, l3), l2)
negative = neg(add(add(gamma, scale(Q(1, 2), l3)), l20))
numerator = add(scale(36, negative), point(step+Q(18, 20)+Q(2, 400)))
cbits = div(numerator, l2)
margin = sub(sub(lhs, Fbits), cbits)
rounded_margin = sub(lhs, point(Q("20.846883")+Q("71.075041")))

assert Fbits[1] < Q("20.846883")
assert cbits[1] < Q("71.075041")
assert margin[0] > Q("7.93")
assert rounded_margin[0] > Q("7.93")
for name, val in [
    ("step", point(step)), ("Fdagger", Fbits), ("63log2(3)", lhs),
    ("c_certificate", cbits), ("margin", margin),
    ("margin_with_paper_ceilings", rounded_margin)
]:
    show(name, val)
print("PASS: exact rational enclosures prove all printed ceilings and the margin.")
