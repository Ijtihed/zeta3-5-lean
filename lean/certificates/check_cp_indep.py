"""INDEPENDENT checker for p-adic denominator certificates cert_c_p*_q*_d*_a*_k*.json (certify_p.py).

Written from the specification in the zeta_2(7) paper, Section 8 (leaf bound, V_c, circle model, Lemma
'Cells', weak duality, assembly), transposed to the p-adic unit-integral family (A=0, nodes [-a,b],
hs iff |y| >= u/p, Mertens constant -gamma - ln p/(p-1)).  It imports NOTHING from the generator
(no genc/genq/genm/pbudget/certify_p): leaf bound by brute force over (R, pi), V_c by an explicit DP,
circle types by direct arc enumeration, the cell events re-derived from the four critical points, and
the constants bounded with mpmath at 50 digits.

Checks (every failure increments `issues`; the verdict is PASS only if issues == 0):
  C1 cells tile [eps, U_end] contiguously; U_end >= max(N, p a, p b) (beyond it T^+ = 0 at lambda = 0);
  C2 every event u (two critical points coincide mod u) in (eps, U_end) is a cell endpoint;
  C3 at 3 exact interior points of every cell the type set equals the certificate's and every measure
     equals m0 + m1 u  (two points determine an affine map, the third is a check);
  C4 every V table equals the recomputed V_c;
  C5 subcells tile each cell; every h >= 0 and h >= g(lambda, u) at both subcell endpoints (affine in u);
  C6 the step sum re-adds exactly; c is re-assembled with outward-rounded constants.
usage: python check_cp_indep.py cert.json [--eps 1/20] [--tamper KIND]   (tamper = negative control)
"""
import sys, json, itertools, math
FASTEST = '--fastest' in sys.argv  # exact: vbar has slope 0/1 in a (audited for the 2-adic analogue, headline/audit_W1_leaf.py),
                                   # so the leaf value is maximised at R = {0..s-1} with the reversed pairing
from fractions import Fraction as F
from functools import lru_cache

sys.set_int_max_str_digits(0)


def main(fn, eps=F(1, 20), tamper=None):
    C = json.load(open(fn))
    p, q, d = C['p'], C['q'], C['d']
    a = b = F(C['a']); kap = F(C['kappa']); N = a + b
    cells = C['cells']
    issues = 0; notes = []

    def bad(msg):
        nonlocal issues
        issues += 1
        if len(notes) < 12: notes.append(msg)

    # ---------- negative-control tampering (the checker must catch each of these)
    if tamper == 'h':            # lower one height by 1/1000
        s = cells[len(cells) // 2]['subcells'][3]; s['h'] = str(F(s['h']) - F(1, 1000))
    elif tamper == 'V':          # raise nothing, lower one V entry (makes the table too optimistic)
        cells[5]['types'][0]['V'][7] -= 1
    elif tamper == 'meas':
        t = cells[40]['types'][0]; t['m1'] = str(F(t['m1']) + F(1, 100))
    elif tamper == 'cell':       # merge two cells (hides an event)
        c0, c1 = cells[60], cells[61]
        if c0['types'] == c1['types']:
            pass
        c0['b'] = c1['b']; c0['subcells'] = c0['subcells'] + c1['subcells']; del cells[61]
    elif tamper == 'hs2':        # wrong model: pretend hs threshold is u/2 (checker uses it => mismatch)
        pass

    thr_div = 2 if tamper == 'hs2' else p

    # ---------- leaf bound (paper Sec. 8, with q, d general; alpha part for every surviving index)
    surv = [i for i in range(2, q + 1) if (i + d + 1) % 2 == 1]
    vals = [i + d + 1 for i in surv]
    if vals != C['values']: bad(f'surviving values {vals} != {C["values"]}')

    def vbar(o, mu, hs, al):
        D = q * o
        cand = [-D - (q - i - al) * mu - (i + d + 1) * hs for i in range(1, q - al + 1)]
        cand += [-D - (q - i0 - al) * mu for i0 in surv if al <= q - i0]
        return min(cand)

    @lru_cache(maxsize=None)
    def fplus(o, mu, hs, s):
        if s == 0: return 0
        best = None
        for R in ([tuple(range(s))] if FASTEST else itertools.combinations(range(q), s)):
            ell = sum(R) - s * (s - 1) // 2
            for pi in ([tuple(reversed(range(s)))] if FASTEST else itertools.permutations(range(s))):
                if any(R[t] + pi[t] > q - 1 for t in range(s)): continue
                v = sum(-vbar(o, mu, hs, R[t] + pi[t]) for t in range(s)) + ell * (1 if o > 0 else 0)
                best = v if best is None else max(best, v)
        return max(best, 0)

    @lru_cache(maxsize=None)
    def Vc(typ):             # typ: sorted tuple of (o, z, mu, hs)
        # W[S] = max over s_k (0..q), sum s_k = S, of sum (f+(k,s_k) + s_k^2);  V = W - S^2
        W = {0: 0}
        for (o, z, mu, hs) in typ:
            assert z == 0
            nw = {}
            for S0, w0 in W.items():
                for s in range(q + 1):
                    val = w0 + fplus(o, mu, hs, s) + s * s
                    if S0 + s not in nw or val > nw[S0 + s]: nw[S0 + s] = val
            W = nw
        return tuple(W[S] - S * S for S in range(len(W)))

    # ---------- circle model by direct arc enumeration
    def types_at(u):
        crit = sorted({(-a) % u, b % u, (u / thr_div) % u, (-u / thr_div) % u})
        pts = crit + [crit[0] + u]
        out = {}
        for x0, x1 in zip(pts, pts[1:]):
            if x1 == x0: continue
            x = (x0 + x1) / 2
            j = math.floor((-a - x) / u)
            while x + j * u < -a: j += 1
            ys = []
            while x + j * u <= b:
                ys.append(x + j * u); j += 1
            if not ys: continue
            o = len(ys) - 1; mu = 1 if o > 0 else 0
            typ = tuple(sorted((o, 0, mu, 1 if abs(y) >= u / thr_div else 0) for y in ys))
            out[typ] = out.get(typ, 0) + (x1 - x0)
        return out

    # ---------- C1 tiling
    ends = [F(c['a']) for c in cells] + [F(cells[-1]['b'])]
    if ends[0] != eps: bad(f'first cell starts at {ends[0]} != eps')
    for c, c2 in zip(cells, cells[1:]):
        if F(c['b']) != F(c2['a']): bad('cells not contiguous at ' + c['b'])
    U_end = ends[-1]
    if U_end < max(N, p * a, p * b): bad(f'U_end {U_end} too small')
    # beyond U_end: single nodes, hs = 0 -> V = 0, T^+ <= 0 at lambda = 0
    ubig = U_end + 1
    tb = types_at(ubig)
    if set(tb) != {((0, 0, 0, 0),)} or any(v != 0 for v in Vc(((0, 0, 0, 0),))): bad('tail u > U_end not trivial')

    # ---------- C2 events
    ev = set()
    jmax = int(4 * p * max(a, b, 1) / eps) + 10
    for j in range(1, jmax): ev.add(N / j)
    for D in (a, b):
        for j in range(0, jmax):
            for sg in (1, -1):
                den = F(j) + F(sg, thr_div)          # D = u (j + sg/p)
                if den > 0: ev.add(D / den)
    # 2u/p in uZ impossible for p >= 3; for the u/2 model it is always true (no event)
    endset = set(ends)
    miss = sorted(e for e in ev if eps < e < U_end and e not in endset)
    for e in miss[:5]: bad(f'event u={e} ({float(e):.6f}) is not a cell endpoint')
    if miss: notes.append(f'{len(miss)} events missing in total')

    # ---------- C3-C5
    step = F(0)
    for ci, c in enumerate(cells):
        lo, hi = F(c['a']), F(c['b'])
        ctypes = {}
        for t in c['types']:
            key = tuple(sorted(tuple(x) for x in t['nodes']))
            ctypes[key] = (F(t['m0']), F(t['m1']), t['V'])
        for fr in (F(1, 7), F(1, 2), F(5, 6)):
            u = lo + fr * (hi - lo)
            tm = types_at(u)
            if set(tm) != set(ctypes):
                bad(f'cell {ci}: type set differs at u={float(u):.5f}'); continue
            for k, (m0, m1, _) in ctypes.items():
                if m0 + m1 * u != tm[k]: bad(f'cell {ci}: measure mismatch at u={float(u):.5f}')
        for k, (_, _, V) in ctypes.items():
            if tuple(V) != Vc(k): bad(f'cell {ci}: V table differs')
        subs = c['subcells']
        if F(subs[0]['a']) != lo or F(subs[-1]['b']) != hi: bad(f'cell {ci}: subcells do not cover')
        for s1, s2 in zip(subs, subs[1:]):
            if F(s1['b']) != F(s2['a']): bad(f'cell {ci}: subcells not contiguous')
        psi_cache = {}
        for sub in subs:
            ua, ub, lam, h = F(sub['a']), F(sub['b']), F(sub['lam']), F(sub['h'])
            if ub <= ua: bad(f'cell {ci}: empty subcell')
            ps = {k: max(v - lam * S for S, v in enumerate(Vc(k))) for k in ctypes}
            g = max(lam * kap + sum((m0 + m1 * u) * ps[k] for k, (m0, m1, _) in ctypes.items()) for u in (ua, ub))
            if h < g: bad(f'cell {ci}: h < g by {float(g - h):.3g}')
            if h < 0: bad(f'cell {ci}: h < 0')
            step += (ub - ua) * h
    if step != F(C['step']): bad('step sum differs from certificate')

    # ---------- C6 constants (outward rounding verified at 50 digits)
    import mpmath as mp
    mp.mp.dps = 50
    Etrue = -mp.euler - mp.log(p) / (p - 1)
    E_hi = F(math.ceil(Etrue * 10**9), 10**9)             # >= true value
    assert mp.mpf(E_hi.numerator) / E_hi.denominator >= Etrue
    lninv = mp.log(1 / (mp.mpf(eps.numerator) / eps.denominator))
    lninv_lo = F(math.floor(lninv * 10**9), 10**9)
    ln2_lo = F(math.floor(mp.log(2) * 10**9), 10**9); ln2_hi = ln2_lo + F(1, 10**9)
    lead = kap * (q * N - kap)
    if lead < 0: bad('negative leading coefficient')
    num = lead * (E_hi - lninv_lo) + step + (d + 2) * kap * eps + F(q * q, 8) * eps ** 2
    cu = num / ln2_lo if num >= 0 else num / ln2_hi
    print(f'{fn}: p={p} q={q} d={d} a={a} kappa={kap} cells={len(cells)} events_in_range={sum(1 for e in ev if eps < e < U_end)}')
    print(f'  issues={issues}  step_equal={step == F(C["step"])}  c <= {float(cu):.6f}  (certificate: {C["c_upper"]:.6f})')
    for n_ in notes: print('   !', n_)
    print('  VERDICT:', 'PASS' if issues == 0 else 'FAIL')
    return issues, cu


if __name__ == '__main__':
    args = sys.argv[1:]
    tamper = None; eps = F(1, 20)
    if '--tamper' in args:
        i = args.index('--tamper'); tamper = args[i + 1]; del args[i:i + 2]
    if '--eps' in args:
        i = args.index('--eps'); eps = F(args[i + 1]); del args[i:i + 2]
    bad = 0
    for fn in [a for a in args if a != '--fastest']:
        bad += main(fn, eps, tamper)[0]
    sys.exit(1 if bad else 0)
