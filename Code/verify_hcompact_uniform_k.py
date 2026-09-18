"""Can case (2) of the interpolation hypothesis be certified UNIFORMLY in k by a single box?

Case (2) is the hypothesis class `Hcompact2Certificates`
(ZerosInShortIntervals/Background/BackgroundZetaBounds.lean): one `Hcompact2Claim k` field for
each of k = 4, 5, 6, 7 (`hcompact2_four`, `_five`, `_six`, `_seven`) plus the k-uniform
`hcompact2_tail : forall {k}, 8 <= k -> Hcompact2Claim k`.  This script is the search that
located that crossover -- where the finite, strip-by-strip checks can stop and one uniform
argument can take over.

`Code/verify_hcompact_boxes.sage` checks case (2) strip by strip for k = 4..16 only and argues
the rest in prose, so on its own it leaves a uniformity gap: the claim quantifies over all
k >= 4.  The route tested here closes it: bound `(s-1)zeta(s)` ONCE on a box reaching from the
half-line to the 1-line, use a uniform lower bound on the interpolant, and let maximum modulus
do the rest.  The two numbers do separate, but only from the crossover onwards -- which is why
the small k keep their own boxes rather than the whole range being covered at once.

That route is what `Code/indep_arb_hcompact.sage` implements rigorously: its tail block runs a
k-uniform RHS lower bound anchored at sigma_8 against sup |(s-1)zeta(s)| on [sigma_8, 1] x
[-3,3], and certifies `hcompact2_tail` over 232 boxes (with 292 / 302 / 588 / 926 boxes for
k = 4, 5, 6, 7).

This script is mpmath at 30 digits on point grids, NOT certified interval arithmetic: it
locates the crossover, the arb script certifies the boxes.

Setup for case (2), matching verify_hcompact_boxes.sage exactly:
    a = sigma_k = 1 - k/(2^k-2),  b = sigma_{k+1},  p = 1/(2^k-2),  q = 1/(2^{k+1}-2)
    A = B = 1.546,  ra = rb = 1,  Q = e,  |t| <= 3
    wa = (b-sigma)/(b-a),  wb = (sigma-a)/(b-a)
    G2(Q,s) = (1/2)(log(Q+s) + log(Q+2-s))
    RHS = (C0|a+it|)^e0 * (B/C0)^wb * |1-b-it|^e1 * (min_tau |G2|)^e2
      with C0 = A^(1/(p+1)), e0 = (p+1)wa + wb, e1 = q*wb, e2 = ra*wa + rb*wb
"""
import mpmath as mp

mp.mp.dps = 30

A = mp.mpf('1.546')
Bc = mp.mpf('1.546')
Q = mp.e
T0 = mp.mpf(3)


def sigma_k(k):
    return 1 - mp.mpf(k) / (mp.mpf(2) ** k - 2)


def G2(s):
    return (mp.log(Q + s) + mp.log(Q + 2 - s)) / 2


def lhs(sig, t):
    """|(s-1)zeta(s)|. The singularity at s=1 is REMOVABLE -- (s-1)zeta(s) -> 1, the residue
    of zeta at its simple pole -- but mpmath raises there, so the point is handled directly."""
    s = mp.mpc(sig, t)
    if abs(s - 1) < mp.mpf('1e-20'):
        return mp.mpf(1)
    return abs((s - 1) * mp.zeta(s))


def rhs(k, sig, t):
    a, b = sigma_k(k), sigma_k(k + 1)
    p = 1 / (mp.mpf(2) ** k - 2)
    q = 1 / (mp.mpf(2) ** (k + 1) - 2)
    wa = (b - sig) / (b - a)
    wb = (sig - a) / (b - a)
    C0 = A ** (1 / (p + 1))
    e0 = (p + 1) * wa + wb
    e1 = q * wb
    e2 = wa + wb                      # ra = rb = 1
    n0 = C0 * abs(mp.mpc(a, t))
    n1 = abs(mp.mpc(1 - b, -t))
    m = min(abs(G2(mp.mpc(a + (b - a) * mp.mpf(i) / 16, t))) for i in range(17))
    return (n0 ** e0) * ((Bc / C0) ** wb) * (n1 ** e1) * (m ** e2)


# ---------------------------------------------------------------- LHS on one fixed box
# Case (2)'s strips all live in [sigma_4, 1) = [5/7, 1); the wider box between the half-line
# and the 1-line is the one the uniform argument would use. Both are computed, on a 61 x 241
# point grid.
def max_lhs(s_lo, s_hi, ns=60, nt=240):
    best, arg = mp.mpf(0), None
    for i in range(ns + 1):
        sig = s_lo + (s_hi - s_lo) * mp.mpf(i) / ns
        for j in range(nt + 1):
            t = -T0 + 2 * T0 * mp.mpf(j) / nt
            v = lhs(sig, t)
            if v > best:
                best, arg = v, (sig, t)
    return best, arg


print("=" * 76)
print("STEP 1 -- sup |(s-1)zeta(s)| on a single box, |Im s| <= 3")
print("=" * 76)
M57, arg57 = max_lhs(mp.mpf(5) / 7, mp.mpf(1))
print(f"  Re(s) in [5/7, 1]  (exactly the union of case (2)'s strips):")
print(f"      max = {mp.nstr(M57, 10)}   at sigma={mp.nstr(arg57[0],6)}, t={mp.nstr(arg57[1],6)}")
M12, arg12 = max_lhs(mp.mpf(1) / 2, mp.mpf(1))
print(f"  Re(s) in [1/2, 1]  (the author's 'half-line to 1-line' box):")
print(f"      max = {mp.nstr(M12, 10)}   at sigma={mp.nstr(arg12[0],6)}, t={mp.nstr(arg12[1],6)}")

print()
print("=" * 76)
print("STEP 2 -- inf of the interpolant RHS over each strip, as k grows")
print("=" * 76)
print("`ptwise` is max over the strip of LHS(s)/RHS(s) at the SAME s -- the quantity the real")
print("verification bounds, and what `verify_hcompact_boxes.sage` reports as its 'ratio'.")
print("`min RHS` is the uniform lower bound the single-box argument would have to beat.")
print()
print(f"{'k':>5} {'sigma_k':>14} {'min RHS':>12} {'ptwise ratio':>14} {'min RHS > M?':>14}")
print("-" * 64)
rows = []
for k in list(range(4, 21)) + [25, 30, 40, 60, 80]:
    a, b = sigma_k(k), sigma_k(k + 1)
    if b - a < mp.mpf('1e-40'):        # strip below working precision; limit already reached
        break
    mr, worst = None, mp.mpf(0)
    for i in range(21):
        sig = a + (b - a) * mp.mpf(i) / 20
        for j in range(41):
            t = -T0 + 2 * T0 * mp.mpf(j) / 40
            r = rhs(k, sig, t)
            mr = r if mr is None else min(mr, r)
            worst = max(worst, lhs(sig, t) / r)
    rows.append((k, mr, worst))
    flag = "yes" if mr > M57 else "NO"
    print(f"{k:>5} {mp.nstr(a,10):>14} {mp.nstr(mr,7):>12} {mp.nstr(worst,6):>14} {flag:>14}")

min_rhs_all = min(r[1] for r in rows)
k0 = None
for k, mr, _ in rows:
    if mr > M57 and k0 is None:
        k0 = k
    elif mr <= M57:
        k0 = None                       # must hold from k0 onwards without interruption

print()
print("=" * 76)
print("VERDICT")
print("=" * 76)
print(f"  M  := sup over [5/7,1] x [-3,3] of |(s-1)zeta(s)| = {mp.nstr(M57, 10)}")
print(f"  inf over all k sampled of  min RHS               = {mp.nstr(min_rhs_all, 10)}")
print()
if min_rhs_all > M57:
    print("  Separated for every k: one box suffices for all k >= 4.")
elif k0 is not None:
    print(f"  NOT separated for every k -- but separated from k = {k0} onwards.")
    print(f"  min RHS is increasing in k, from {mp.nstr(rows[0][1],6)} at k=4 to a limit of")
    print(f"  {mp.nstr(rows[-1][1],8)}, crossing M = {mp.nstr(M57,7)} at k = {k0}.")
    print()
    print("  So the single-box argument DOES close the uniformity gap, but only for the tail:")
    print(f"    * k = 4 .. {k0-1}: the strips are wide and the interpolant is still small there,")
    print("      so these need their individual box checks, exactly as now.")
    print(f"    * k >= {k0}: ONE bound on |(s-1)zeta(s)| over [5/7,1] x [-3,3], together with the")
    print("      uniform lower bound on the interpolant, covers all of them at once.")
    print(f"  That replaces 'check k=4..16 and argue the tail informally' with a complete")
    print(f"  argument: {k0-4} finite checks plus one uniform box.")
else:
    print("  NOT separated -- a single box does not suffice as posed.")

print()
print("Limit as k -> infinity (strip collapses to sigma = 1):")
print("  LHS -> |(s-1)zeta(s)| at sigma=1, i.e. the residue 1 (times |it| factors -> 1).")
for t in ['0', '1', '3']:
    t = mp.mpf(t)
    lim = Bc * abs(mp.mpc(1, t)) * abs(G2(mp.mpc(1, t)))
    print(f"    t={mp.nstr(t,3):>4}  RHS limit = 1.546*|1+it|*|G2(1+it)| = {mp.nstr(lim, 8)}")
