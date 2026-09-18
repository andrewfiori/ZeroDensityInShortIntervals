#!/usr/bin/env python3
r"""
INDEPENDENT mpmath re-evaluation (2026-09-05) of the eight compact-window hypothesis fields in
`ZerosInShortIntervals/Background/BackgroundZetaBounds.lean` --
`InterpolationCertificates.interpolated_bound_1a_hcompact`, `_1b_hcompact`, `_1c_hcompact` and
`Hcompact2Certificates.hcompact2_four`, `_five`, `_six`, `_seven`, `_tail` -- written directly
from the Lean statements rather than from any existing Sage script, so that a transcription error
in one would show up in the other (an earlier attempt to split cases (1a)/(1b)/(1c) into boxes
plus a uniform tail produced tables that were wrong for case (1a), for the reason recorded in
`BackgroundZetaBounds.lean`: sigma-endpoint evaluation cannot see that the two widths sum to 1):

   interpolated_bound_1a_hcompact   interpG 66.7 1.546 (27/164) (1/14) (4e),  alpha=(p+1,0,0), beta=(1,q,1), |t| <= 4e+1
   interpolated_bound_1b_hcompact   interpG 0.611 1.546 (1/6) (1/14) 16,     alpha=(p+1,0,1), beta=(1,q,1), |t| <= 3
   interpolated_bound_1c_hcompact   interpG1c 1.546 0.470795 4.04972 (1/14) (4e), alpha=(p+1,1,0,0) p=1/6, beta=(1,0,q,1), |t| <= 4e+1
   hcompact2_four .. _seven, _tail  Hcompact2Claim k: interpG 1.546 1.546 (1/(2^k-2)) (1/(2^(k+1)-2)) e,
                                    alpha=(p+1,0,1), beta=(1,q,1), sigma in [1-k/(2^k-2), 1-(k+1)/(2^(k+1)-2)], |t| <= 3

with (PhragmenLindelofSetup.lean)
   interpG A B p q Q  = [ linG (A^(1/(p+1))) 0,  linGRefl ((B/A^(1/(p+1)))^(1/q)) 1,  GPL Q ]
   interpG1c B c d q Q = [ linG 1 0,  G1shift Q c d,  linGRefl (B^(1/q)) 1,  GPL Q ]
   linG C Q s = C (Q+s),  linGRefl C Q s = C (Q-s),  GPL Q s = (log(Q+s)+log(Q+2-s))/2,
   G1shift Q c d s = c GPL Q (s+1) + d,
and the claim, for every t in the range and sigma in [a,b],
   |(s-1) zeta(s)|  <  prod_i ( inf_{tau in [a,b]} |G_i(tau+it)| )^( alpha_i (b-sigma)/(b-a) + beta_i (sigma-a)/(b-a) ).

WHAT IS COMPUTED.  For each case, the POINTWISE ratio LHS/RHS on a grid (sigma: 25 points,
t: step 0.05 on [0,T0]; both sides are conjugation-invariant so t >= 0 suffices), with the
tau-infimum of |GPL| found by a fine tau-grid plus golden refinement (the linear G's have
endpoint infima).  The worst ratio must be < 1.  Then, for the DECOUPLED split the Lean route
needs (sup_box LHS vs inf_box RHS), the worst U/L over boxes of several sizes is reported --
including a sigma-cut for (1b), which the docstring says is required.  For `hcompact2_tail` the
k-trend of the worst ratio is printed for k = 8..16 together with the k-uniform lower bound on
RHS used by `indep_arb_hcompact.sage`.

This is floating point evidence (25-30 digits); `indep_arb_hcompact.sage` is the certified
version.  Run with:  python3 Code/indep_mpmath_hcompact.py
"""
import mpmath as mp

mp.mp.dps = 25
E = mp.e


def GPL(Q, s):
    return (mp.log(Q + s) + mp.log(Q + 2 - s)) / 2


def inf_tau_abs(f, a, b, n=60):
    """inf over tau in [a,b] of |f(tau)| by grid + golden refinement (f smooth, unimodal here)."""
    best = None
    bi = 0
    for i in range(n + 1):
        tau = a + (b - a) * i / n
        v = abs(f(tau))
        if best is None or v < best:
            best, bi = v, i
    lo = a + (b - a) * max(bi - 1, 0) / n
    hi = a + (b - a) * min(bi + 1, n) / n
    gr = (mp.sqrt(5) - 1) / 2
    x1 = hi - gr * (hi - lo)
    x2 = lo + gr * (hi - lo)
    f1, f2 = abs(f(x1)), abs(f(x2))
    for _ in range(40):
        if f1 < f2:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - gr * (hi - lo)
            f1 = abs(f(x1))
        else:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + gr * (hi - lo)
            f2 = abs(f(x2))
    return min(best, f1, f2)


class Case:
    def __init__(self, name, a, b, T0, Gs, alpha, beta):
        self.name, self.a, self.b, self.T0 = name, mp.mpf(a), mp.mpf(b), mp.mpf(T0)
        self.Gs, self.alpha, self.beta = Gs, alpha, beta

    def infs(self, t):
        """inf_{tau in [a,b]} |G_i(tau + i t)| for each i."""
        out = []
        for kind, G in self.Gs:
            if kind == "linG":      # |C (Q + tau + it)|, Q>=0: increasing in tau -> tau = a
                out.append(abs(G(mp.mpc(self.a, t))))
            elif kind == "linGRefl":  # |C (Q - tau - it)| with Q - tau > 0 on [a,b]: decreasing -> tau = b
                out.append(abs(G(mp.mpc(self.b, t))))
            else:
                out.append(inf_tau_abs(lambda tau: G(mp.mpc(tau, t)), self.a, self.b))
        return out

    def rhs(self, sig, t, infs=None):
        if infs is None:
            infs = self.infs(t)
        wa = (self.b - sig) / (self.b - self.a)
        wb = (sig - self.a) / (self.b - self.a)
        val = mp.mpf(1)
        for i, m in enumerate(infs):
            val *= m ** (self.alpha[i] * wa + self.beta[i] * wb)
        return val

    @staticmethod
    def lhs(sig, t):
        s = mp.mpc(sig, t)
        return abs((s - 1) * mp.zeta(s))


def interpG(A, B, p, q, Q):
    A, B, p, q, Q = map(mp.mpf, (A, B, p, q, Q))
    C0 = A ** (1 / (p + 1))
    C1 = (B / C0) ** (1 / q)
    return [("linG", lambda s: C0 * s), ("linGRefl", lambda s: C1 * (1 - s)), ("GPL", lambda s: GPL(Q, s))]


def interpG1c(B, c, d, q, Q):
    B, c, d, q, Q = map(mp.mpf, (B, c, d, q, Q))
    return [("linG", lambda s: s), ("G1shift", lambda s: c * GPL(Q, s + 1) + d),
            ("linGRefl", lambda s: (B ** (1 / q)) * (1 - s)), ("GPL", lambda s: GPL(Q, s))]


def sigma_k(k):
    return 1 - mp.mpf(k) / (2 ** k - 2)


def make_cases():
    cases = []
    p, q = mp.mpf(27) / 164, mp.mpf(1) / 14
    cases.append(Case("1a", mp.mpf(1) / 2, mp.mpf(5) / 7, 4 * E + 1, interpG(mp.mpf('66.7'), mp.mpf('1.546'), p, q, 4 * E),
                      [p + 1, 0, 0], [1, q, 1]))
    p = mp.mpf(1) / 6
    cases.append(Case("1b", mp.mpf(1) / 2, mp.mpf(5) / 7, 3, interpG(mp.mpf('0.611'), mp.mpf('1.546'), p, q, 16),
                      [p + 1, 0, 1], [1, q, 1]))
    cases.append(Case("1c", mp.mpf(1) / 2, mp.mpf(5) / 7, 4 * E + 1,
                      interpG1c(mp.mpf('1.546'), mp.mpf('0.470795'), mp.mpf('4.04972'), q, 4 * E),
                      [p + 1, 1, 0, 0], [1, 0, q, 1]))
    for k in range(4, 17):
        a, b = sigma_k(k), sigma_k(k + 1)
        pk, qk = 1 / (mp.mpf(2) ** k - 2), 1 / (mp.mpf(2) ** (k + 1) - 2)
        cases.append(Case(f"2:k={k}", a, b, 3, interpG(mp.mpf('1.546'), mp.mpf('1.546'), pk, qk, E),
                          [pk + 1, 0, 1], [1, qk, 1]))
    return cases


def pointwise(case, nsig=24, dt=mp.mpf('0.05')):
    worst = (mp.mpf(0), None)
    t = mp.mpf(0)
    while t <= case.T0 + mp.mpf('1e-12'):
        infs = case.infs(t)
        for i in range(nsig + 1):
            sig = case.a + (case.b - case.a) * i / nsig
            r = case.lhs(sig, t) / case.rhs(sig, t, infs)
            if r > worst[0]:
                worst = (r, (sig, t))
        t += dt
    # also the exact end point T0
    infs = case.infs(case.T0)
    for i in range(nsig + 1):
        sig = case.a + (case.b - case.a) * i / nsig
        r = case.lhs(sig, case.T0) / case.rhs(sig, case.T0, infs)
        if r > worst[0]:
            worst = (r, (sig, case.T0))
    return worst


def decoupled(case, tw, nsigcut, nsig=12, nt=8):
    """worst over boxes (sigma-cut into nsigcut pieces, t-width tw) of sup_box LHS / inf_box RHS.
    RHS inf over the box: log RHS is affine in sigma, so the sigma-inf is at a box endpoint; over t a grid."""
    worst = (mp.mpf(0), None)
    t0 = mp.mpf(0)
    while t0 < case.T0:
        t1 = min(t0 + tw, case.T0)
        for j in range(nsigcut):
            s0 = case.a + (case.b - case.a) * j / nsigcut
            s1 = case.a + (case.b - case.a) * (j + 1) / nsigcut
            U = mp.mpf(0)
            L = None
            for it in range(nt + 1):
                t = t0 + (t1 - t0) * it / nt
                infs = case.infs(t)
                for ends in (s0, s1):
                    v = case.rhs(ends, t, infs)
                    L = v if L is None else min(L, v)
                for isg in range(nsig + 1):
                    sig = s0 + (s1 - s0) * isg / nsig
                    U = max(U, case.lhs(sig, t))
            r = U / L
            if r > worst[0]:
                worst = (r, (s0, s1, t0, t1, U, L))
        t0 = t1
    return worst


if __name__ == "__main__":
    cases = make_cases()
    print("=" * 96)
    print("POINTWISE: worst LHS/RHS over sigma in [a,b] (25 pts) x t in [0,T0] (step 0.05); must be < 1")
    print("=" * 96)
    pw = {}
    for c in cases:
        w = pointwise(c)
        pw[c.name] = w
        print(f"  {c.name:8s} a={mp.nstr(c.a,7):>10} b={mp.nstr(c.b,7):>10} T0={mp.nstr(c.T0,6):>8}:  "
              f"worst ratio {mp.nstr(w[0], 8)} at sigma={mp.nstr(w[1][0],6)}, t={mp.nstr(w[1][1],6)}   "
              f"{'OK' if w[0] < 1 else 'FAIL <-- CHECK'}")

    print()
    print("=" * 96)
    print("DECOUPLED SPLIT (sup_box LHS / inf_box RHS): what box sizes make the Lean route work?")
    print("=" * 96)
    for name in ("1a", "1b", "1c", "2:k=4", "2:k=5", "2:k=6", "2:k=7"):
        c = next(x for x in cases if x.name == name)
        for tw, ns in [(4, 1), (2, 1), (1, 1), (mp.mpf(1) / 2, 1), (mp.mpf(1) / 2, 2), (mp.mpf(1) / 4, 4), (mp.mpf(1) / 8, 8)]:
            if tw > c.T0:
                continue
            w = decoupled(c, mp.mpf(tw), ns)
            s0, s1, t0, t1, U, L = w[1]
            print(f"  {name:6s} t-width {mp.nstr(tw,4):>5}, sigma cut {ns}: worst U/L = {mp.nstr(w[0], 6)}"
                  f"  (box sigma [{mp.nstr(s0,4)},{mp.nstr(s1,4)}], t [{mp.nstr(t0,4)},{mp.nstr(t1,4)}]: sup LHS {mp.nstr(U,6)} vs inf RHS {mp.nstr(L,6)})"
                  f"  {'works' if w[0] < 1 else 'fails'}")
        print()

    print("=" * 96)
    print("hcompact2_tail: k-trend and the k-uniform RHS lower bound (as used by indep_arb_hcompact.sage)")
    print("=" * 96)
    A = mp.mpf('1.546')
    p8 = 1 / (mp.mpf(2) ** 8 - 2)
    q8 = 1 / (mp.mpf(2) ** 9 - 2)
    s8, s9 = sigma_k(8), sigma_k(9)
    term1_low = (1 - s9) ** q8
    print(f"  sigma_8 = {mp.nstr(s8, 8)},  sigma_9 = {mp.nstr(s9, 8)},  p_8 = {mp.nstr(p8, 8)},  q_8 = {mp.nstr(q8, 8)}")
    print(f"  (1-sigma_9)^q_8 = {mp.nstr(term1_low, 8)}  (lower bound for the linGRefl factor, all k>=8)")

    def R_low(sig_dummy, t):
        base = A ** (1 / (1 + p8)) * mp.sqrt(s8 ** 2 + t ** 2)
        t0 = min(base, base ** (1 + p8))
        gpl = inf_tau_abs(lambda tau: GPL(E, mp.mpc(tau, t)), s8, mp.mpf(1))
        return t0 * term1_low * gpl

    worst_unif = (mp.mpf(0), None)
    t = mp.mpf(0)
    while t <= 3 + mp.mpf('1e-12'):
        rl = R_low(None, t)
        for i in range(0, 33):
            sig = s8 + (1 - s8) * i / 32
            if sig == 1 and t == 0:
                lhs = mp.mpf(1)
            else:
                lhs = Case.lhs(sig, t)
            r = lhs / rl
            if r > worst_unif[0]:
                worst_unif = (r, (sig, t))
        t += mp.mpf('0.05')
    print(f"  UNIFORM: sup_{{sigma in [sigma_8,1]}} LHS / R_low(t) over t in [0,3] = {mp.nstr(worst_unif[0], 6)}"
          f" at sigma={mp.nstr(worst_unif[1][0],6)}, t={mp.nstr(worst_unif[1][1],4)}   {'OK: tail k>=8 follows' if worst_unif[0] < 1 else 'FAIL'}")
    print("  per-k pointwise worst ratios (from above):")
    for k in range(8, 17):
        w = pw[f"2:k={k}"]
        print(f"     k={k:2d}: {mp.nstr(w[0], 8)}")
    print()
    print("Done.")
