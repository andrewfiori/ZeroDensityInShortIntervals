r"""
Rigorous certified verification of the "compact range" hypothesis `hcompact` of
`PhragmenLindelofSetup.fiori_zeta_interpolation` (cases (1a), (1b), (2)) and of
`fiori_zeta_interpolation_1c` (case (1c)) -- the four cases of `Proposition
\ref{prop:interpolation}` (Proposition 35) in the Appendix of
`ZerosInShortIntervals.tex` (`BackgroundZetaBounds.interpolated_bound_1a`, `_1b`,
`_1c`, `_2`).

WHICH HYPOTHESIS FIELDS THIS CERTIFIES
--------------------------------------
    InterpolationCertificates.interpolated_bound_1a_hcompact   -- case (1a)
    InterpolationCertificates.interpolated_bound_1b_hcompact   -- case (1b)
    InterpolationCertificates.interpolated_bound_1c_hcompact   -- case (1c)
    Hcompact2Certificates.hcompact2_four / _five / _six / _seven  -- case (2) at k = 4,5,6,7
It does NOT certify `Hcompact2Certificates.hcompact2_tail`: case (2) is run here only for
k = 4..KMAX (KMAX = 16) and the rest is argued in prose at the end of the output, which is not
uniform in `k`.  `Code/indep_arb_hcompact.sage` closes that gap with an explicit `k`-uniform lower
bound on the right-hand side, and re-certifies all eight fields by an independently written
implementation.

WHAT IS BEING CHECKED
---------------------
Phragmen-Lindelof is applied (see `fiori_zeta_interpolation`) to

    f(s) = (s-1)*zeta(s),      not to zeta(s),

with the r = 3 family

    G_0(s) = C0 * s,           C0 = A^(1/(p+1)),        alpha_0 = p+1,  beta_0 = 1
    G_1(s) = C1 * (1-s),       C1 = (B/C0)^(1/q),       alpha_1 = 0,    beta_1 = q
    G_2(s) = (1/2)(log(Q+s) + log(Q+2-s)),              alpha_2 = ra,   beta_2 = rb

The `(s-1)` factor is what makes the small-|t| hypothesis satisfiable at all: without it the
hypothesis FAILS at t = 0 for (1b) (|zeta(1/2)| = 1.46035 against 1.34636) and, increasingly badly
with k, for (2) (|zeta(b_k)| ~ 1/(1-b_k), which diverges, against a right-hand side that stays
near 2).  The extra power has to sit on the *increasing* G_0 rather than on G_1: putting it on G_1
multiplies both sides of the boundary hypotheses by the same |1-s| and is a no-op.  Dividing the
conclusion back by |s-1| costs only a factor |s|/|1-s| = 1 + O(1/t^2) on the lead constant --
nothing on any exponent.

`hcompact` then reads: for all |t| <= T0 and sigma in [a,b], with
wa = (b-sigma)/(b-a), wb = (sigma-a)/(b-a),

  |(sigma+it-1) zeta(sigma+it)|
      <  prod_i ( inf_{tau in [a,b]} |G_i(tau+it)| )^( alpha_i*wa + beta_i*wb ).

The three infima are explicit: G_0 is increasing in tau and G_1 decreasing, so

  inf |G_0| = C0*|a+it|,   inf |G_1| = C1*|1-b-it|,   inf |G_2| = min_tau |G_2(tau+it)|,

and the last is bounded below here by a certified minimum over a subdivision of [a,b].  Using
C0^(p+1) = A and C0*C1^q = B, the right-hand side is

  ( C0*|a+it| )^((p+1)*wa + wb) * (B/C0)^wb * |1-b-it|^(q*wb) * m(t)^(ra*wa + rb*wb).

Everything is evaluated with arb ball arithmetic (ComplexBallField/RealBallField), on balls
covering whole sub-boxes of (sigma,t), so each verified box is a rigorous statement about the
entire box, not about sample points.  Only |t| in [0,T0] is checked: both sides depend on t only
through |t| (zeta(conj s) = conj(zeta(s)), and G_2 likewise).

CASE (1c)
---------
Case (1c) (`interpolated_bound_1c_hcompact`) uses a different, r = 4, family
(`PhragmenLindelofSetup.interpG1c`), because its sigma=1/2 boundary bound
(0.470795|t|^(1/6)log|t| + 4.04972|t|^(1/6)) is affine in a log rather than a constant times a
power:

    G_0(s) = s,                                            alpha_0 = p+1, beta_0 = 1
    G_1(s) = c*(1/2)(log(Q+1+s) + log(Q+1-s)) + d,          alpha_1 = 1,   beta_1 = 0
    G_2(s) = C2*(1-s),        C2 = B^(1/q),                 alpha_2 = 0,   beta_2 = q
    G_3(s) = (1/2)(log(Q+s) + log(Q+2-s)),                  alpha_3 = 0,   beta_3 = 1

(`G_0 = linG 1 0`, `G_1 = G1shift Q c d`, `G_2 = linGRefl (B^(1/q)) 1`, `G_3 = GPL Q`, in the Lean
naming.)  `G_0`, `G_2` are exactly linear in `s`, so -- unlike `G_2`/`GPL` in the r = 3 cases above
-- their infima over tau in [a,b] are *unconditionally* the closed-form endpoint values (`|G_0|` is
increasing in sigma whenever `sigma > -Q = 0`, `|G_2|` decreasing whenever `sigma < Q = 1`; both
hold throughout [1/2,5/7] regardless of t, no large-t threshold needed).  `G_1` and `G_3` are
log-type, so their infima are certified the same way as `G_2` above: minimising over a subdivision
of [a,b], each sub-interval evaluated on one ball.

Run with:  sage Code/verify_hcompact_boxes.sage
"""

import time

PREC = 120
RR = RealField(200)
CBF = ComplexBallField(PREC)
RBF = RealBallField(PREC)


def G2(Q, s):
    """(1/2)(log(Q+s) + log(Q+2-s)), as a complex ball."""
    return (CBF(1) / 2) * ((Q + s).log() + (Q + 2 - s).log())


def g2_min_lower(Q, a, b, t, nsub=8):
    """Certified LOWER bound for inf_{tau in [a,b]} |G_2(tau+it)|, by minimising over a
    subdivision into `nsub` sub-intervals, each evaluated on one ball covering it."""
    lo = None
    h = (b - a) / (2 * nsub)
    for i in range(nsub):
        c = a + (2 * i + 1) * h
        s = CBF(RBF(RR(c), RR(h)), t)
        v = G2(Q, s).abs().lower()
        lo = v if lo is None else min(lo, v)
    return RBF(lo)


def rhs_lower(par, sig_ball, t_ball, wa, wb):
    """Certified LOWER bound for the right-hand side of `hcompact` over the box."""
    a, b, A, p, ra, B, q, rb, Q = par
    C0 = RBF(A) ** (RBF(1) / (RBF(p) + 1))
    e0 = (RBF(p) + 1) * wa + wb
    e1 = RBF(q) * wb
    e2 = RBF(ra) * wa + RBF(rb) * wb
    n0 = (C0 * CBF(RBF(a), t_ball).abs())
    n1 = CBF(RBF(1) - RBF(b), -t_ball).abs()
    m = g2_min_lower(Q, RR(a), RR(b), t_ball)
    return (n0 ** e0) * ((RBF(B) / C0) ** wb) * (n1 ** e1) * (m ** e2)


def verify_box(par, sc, tc, hs, ht, min_size, stats):
    a, b = par[0], par[1]
    sig = RBF(RR(sc), RR(hs))
    t = RBF(RR(tc), RR(ht))
    s = CBF(sig, t)
    wa = (RBF(b) - sig) / (RBF(b) - RBF(a))
    wb = (sig - RBF(a)) / (RBF(b) - RBF(a))
    L = ((s - 1) * s.zeta()).abs()
    R = rhs_lower(par, sig, t, wa, wb)
    stats['evals'] += 1
    if L.upper() < R.lower():
        ratio = RR(L.upper()) / RR(R.lower())
        stats['worst_ratio'] = max(stats.get('worst_ratio', RR(0)), ratio)
        return True, []
    if hs < min_size and ht < min_size:
        return False, [(RR(sc), RR(tc), RR(hs), RR(ht), L.upper(), R.lower())]
    ok, fails = True, []
    for dsig in (-1, 1):
        for dt in (-1, 1):
            g, f = verify_box(par, sc + dsig * hs / 2, tc + dt * ht / 2, hs / 2, ht / 2,
                              min_size, stats)
            ok = ok and g
            fails.extend(f)
    return ok, fails


def G1shift(Q, c, d, s):
    """c*(1/2)(log(Q+1+s) + log(Q+1-s)) + d = c*G2(Q, s+1) + d, as a complex ball."""
    return CBF(c) * G2(Q, s + 1) + CBF(d)


def min_lower(f, a, b, t, nsub=8):
    """Certified LOWER bound for inf_{tau in [a,b]} |f(tau+it)|, by minimising over a subdivision
    into `nsub` sub-intervals, each evaluated on one ball covering it. Works for any `f` (no
    monotonicity assumption needed) -- generalises `g2_min_lower`."""
    lo = None
    h = (b - a) / (2 * nsub)
    for i in range(nsub):
        c = a + (2 * i + 1) * h
        s = CBF(RBF(RR(c), RR(h)), t)
        v = f(s).abs().lower()
        lo = v if lo is None else min(lo, v)
    return RBF(lo)


def rhs_lower_1c(par, sig_ball, t_ball, wa, wb, nsub=8):
    """Certified LOWER bound for the right-hand side of `hcompact` for case (1c)'s r = 4 family,
    over the box. `par = (a, b, B, c, d, q, p, Q)`."""
    a, b, B, c, d, q, p, Q = par
    C2 = RBF(B) ** (RBF(1) / RBF(q))
    e0 = (RBF(p) + 1) * wa + wb
    e1 = wa
    e2 = RBF(q) * wb
    e3 = wb
    n0 = CBF(RBF(a), t_ball).abs()
    n2 = C2 * CBF(RBF(1) - RBF(b), -t_ball).abs()
    inf1 = min_lower(lambda s: G1shift(Q, c, d, s), RR(a), RR(b), t_ball, nsub)
    inf3 = min_lower(lambda s: G2(Q, s), RR(a), RR(b), t_ball, nsub)
    return (n0 ** e0) * (inf1 ** e1) * (n2 ** e2) * (inf3 ** e3)


def verify_box_1c(par, sc, tc, hs, ht, min_size, stats):
    a, b = par[0], par[1]
    sig = RBF(RR(sc), RR(hs))
    t = RBF(RR(tc), RR(ht))
    s = CBF(sig, t)
    wa = (RBF(b) - sig) / (RBF(b) - RBF(a))
    wb = (sig - RBF(a)) / (RBF(b) - RBF(a))
    L = ((s - 1) * s.zeta()).abs()
    R = rhs_lower_1c(par, sig, t, wa, wb)
    stats['evals'] += 1
    if L.upper() < R.lower():
        ratio = RR(L.upper()) / RR(R.lower())
        stats['worst_ratio'] = max(stats.get('worst_ratio', RR(0)), ratio)
        return True, []
    if hs < min_size and ht < min_size:
        return False, [(RR(sc), RR(tc), RR(hs), RR(ht), L.upper(), R.lower())]
    ok, fails = True, []
    for dsig in (-1, 1):
        for dt in (-1, 1):
            g, f = verify_box_1c(par, sc + dsig * hs / 2, tc + dt * ht / 2, hs / 2, ht / 2,
                                 min_size, stats)
            ok = ok and g
            fails.extend(f)
    return ok, fails


def run_1c(name, a, b, B, c, d, q, p, Q, T0):
    par = (RR(a), RR(b), RR(B), RR(c), RR(d), RR(q), RR(p), RBF(Q))
    sc0, tc0 = (RR(a) + RR(b)) / 2, RR(T0) / 2
    hs0, ht0 = (RR(b) - RR(a)) / 2, RR(T0) / 2
    stats = {'evals': 0}
    t0 = time.time()
    ok, fails = verify_box_1c(par, sc0, tc0, hs0, ht0, RR(1) / 2 ** 16, stats)
    print(f"  {name:<12} sigma in [{float(a):.6f}, {float(b):.6f}], |t| <= {float(T0)}, Q = {float(RR(Q)):.6f}", flush=True)
    print(f"  {'':<12} {'VERIFIED' if ok else 'FAILED  '}   "
          f"{stats['evals']} certified ball evaluations, worst ratio "
          f"{float(stats.get('worst_ratio', RR(0))):.4f}, {time.time() - t0:.2f}s", flush=True)
    if fails:
        for f in fails[:5]:
            print("      unresolved:", f)
    return ok


def run(name, a, b, A, p, ra, B, q, rb, Q, T0):
    par = (RR(a), RR(b), RR(A), RR(p), RR(ra), RR(B), RR(q), RR(rb), RBF(Q))
    sc0, tc0 = (RR(a) + RR(b)) / 2, RR(T0) / 2
    hs0, ht0 = (RR(b) - RR(a)) / 2, RR(T0) / 2
    stats = {'evals': 0}
    t0 = time.time()
    ok, fails = verify_box(par, sc0, tc0, hs0, ht0, RR(1) / 2 ** 16, stats)
    print(f"  {name:<12} sigma in [{float(a):.6f}, {float(b):.6f}], |t| <= {float(T0)}, Q = {float(RR(Q)):.6f}", flush=True)
    print(f"  {'':<12} {'VERIFIED' if ok else 'FAILED  '}   "
          f"{stats['evals']} certified ball evaluations, worst ratio "
          f"{float(stats.get('worst_ratio', RR(0))):.4f}, {time.time() - t0:.2f}s", flush=True)
    if fails:
        for f in fails[:5]:
            print("      unresolved:", f)
    return ok


E = RR(1).exp()
allok = True

print("hcompact for the four interpolated_bound cases, with f(s) = (s-1) zeta(s):")
print()
# (1a): Patel-Yang at sigma=1/2 (ra=0) against Yang k=4 at sigma=5/7.  T0 = 4e+1 because that is
# where GPL_anti_of_large_t's monotonicity threshold |t| > Q+1 sits (see that theorem).
allok &= run("(1a)", RR(1)/2, RR(5)/7, RR('66.7'), RR(27)/164, 0,
             RR('1.546'), RR(1)/14, 1, 4*E, 4*E + 1)
# (1b): Hiary-Patel-Yang subconvexity constant 0.611 at sigma=1/2 (ra=1).  Q raised from 4e to 16:
# at Q=4e the check fails (ratio 1.0847 at sigma=1/2, t=0); Q is a free parameter that does not
# appear in the conclusion, and Q >= 13.7 suffices.  ra = rb here, so no monotonicity is needed
# and T0 = 3 is enough.
allok &= run("(1b), Q=16", RR(1)/2, RR(5)/7, RR('0.611'), RR(1)/6, 1,
             RR('1.546'), RR(1)/14, 1, RR(16), RR(3))
# (1c): the r = 4 family, G_1 = G1shift carrying the affine-in-log Hiary-Revers boundary bound
# directly.  Same Q = 4e, T0 = 4e+1 as (1a), for the same reason (G_1 and G_3/GPL are the two
# functions needing a large-t threshold before their infima are certified below by subdivision;
# G_0, G_2 are linear and need no threshold at all).
allok &= run_1c("(1c)", RR(1)/2, RR(5)/7, RR('1.546'), RR('0.470795'), RR('4.04972'),
                RR(1)/14, RR(1)/6, 4*E, 4*E + 1)
# (2): Yang at consecutive k, k+1, for every k >= 4.  Checked here for k = 4..KMAX; see the note
# below for the tail.
KMAX = 16
for k in range(4, KMAX + 1):
    a = 1 - RR(k) / (RR(2) ** k - 2)
    b = 1 - (RR(k) + 1) / (RR(2) ** (k + 1) - 2)
    p = 1 / (RR(2) ** k - 2)
    q = 1 / (RR(2) ** (k + 1) - 2)
    allok &= run(f"(2) k={k}", a, b, RR('1.546'), p, 1, RR('1.546'), q, 1, E, RR(3))

print()
print("ALL VERIFIED" if allok else "SOME BOXES FAILED")
print()
print("Tail k > %d.  As k grows, [a_k,b_k] shrinks to the point 1 and the check becomes easier," % KMAX)
print("not harder: the left-hand side |(sigma-1) zeta(sigma+it)| tends to the constant 1 (the")
print("residue of zeta at its pole), while the right-hand side tends to")
print("1.546 * |1+it| * min_tau |G_2(tau+it)| >= 1.546 * 1 * log(e+1) > 1.5.  The observed worst")
print("ratio decreases monotonically in k towards 0.4927, so the finite check above is")
print("representative.  Making the tail fully rigorous needs a uniform bound on |(s-1)zeta(s)|")
print("near s=1; that is done, in certified arb ball arithmetic, by")
print("Code/indep_arb_hcompact.sage, which covers the k >= 8 tail as well as cases (1a), (1b),")
print("(1c) and the whole of case (2).  This script is the independent finite recheck.")
