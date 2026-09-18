#!/usr/bin/env python3
"""
INDEPENDENT re-derivation of the decoupled-split constants behind the hypothesis field
`InterpolationCertificates.interpolated_bound_1a_hcompact`
(ZerosInShortIntervals/Background/BackgroundZetaBounds.lean), written from the Lean
definitions directly.

Why this exists
---------------
The certificate proper is `Code/indep_arb_hcompact.sage`, which discharges case (1a) in arb
ball arithmetic over 125 boxes; `Code/indep_mpmath_hcompact.py` rechecks all the cases
pointwise.  Ball arithmetic evaluated on a whole box can over-inflate and report a worst-case
ratio that no point of the box attains, so a ratio close to 1 there is not on its own evidence
that the claim is nearly tight -- it may be an artifact of the enclosure.  This script is a
deliberately different implementation of case (1a) alone: mpmath on a point grid, with the
G-family transcribed from the Lean definitions rather than copied from any Sage script, so
that agreement is real corroboration and disagreement is informative.  Its second half asks a
question the certifying scripts do not: how coarse a t-partition the DECOUPLED comparison
(sup LHS over a box against inf RHS over the same box) still survives.

Definitions, transcribed from Background/PhragmenLindelofSetup.lean
-------------------------------------------------------------------
  linG C Q s      = C * (Q + s)
  linGRefl C Q s  = C * (Q - s)
  GPL Q s         = (1/2)*(log(Q + s) + log(Q + 2 - s))
  interpG A B p q Q =
      ![ linG (A^(1/(p+1))) 0, linGRefl ((B / A^(1/(p+1)))^(1/q)) 1, GPL Q ]
  interpalpha p ra = ![p + 1, 0, ra]      interpbeta q rb = ![1, q, rb]

Case (1a): A=66.7, B=1.546, p=27/164, q=1/14, Q=4e, ra=0, rb=1, on
sigma in [1/2, 5/7], |t| <= 4e+1 = 11.873.  The scan below covers t in [0,12], a superset.

KEY STRUCTURAL FACT (verified below): log RHS is AFFINE in sigma, because every
base depends on t alone and every exponent is affine in sigma.  So the
sigma-infimum of the RHS is always at an endpoint -- no interior search needed.
At sigma = 5/7 the product telescopes:
    RHS(5/7, t) = B * inf|s| * (inf|1-s|)^(1/14) * inf|GPL|
since C0 * (B/C0)^(q * 1/q) = B.

NOTE ON RIGOUR: fine-grid evaluation at 121 sigma-samples and 481 t-samples, not certified
interval arithmetic.  It can corroborate or contradict a published constant; it cannot
certify one.
"""

from mpmath import mp, mpf, mpc, zeta, log, exp, fabs

mp.dps = 30

A, B = mpf('66.7'), mpf('1.546')
p, q = mpf(27) / mpf(164), mpf(1) / mpf(14)
Q = 4 * exp(1)

SIG_LO, SIG_HI = mpf(1) / mpf(2), mpf(5) / mpf(7)
WIDTH = SIG_HI - SIG_LO

C0 = A ** (1 / (p + 1))
C1 = (B / C0) ** (1 / q)
ALPHA = [p + 1, mpf(0), mpf(0)]
BETA = [mpf(1), q, mpf(1)]


def G(i, s):
    if i == 0:
        return C0 * s
    if i == 1:
        return C1 * (1 - s)
    return (log(Q + s) + log(Q + 2 - s)) / 2


def exponent(i, sigma):
    wa = (SIG_HI - sigma) / WIDTH
    wb = (sigma - SIG_LO) / WIDTH
    return ALPHA[i] * wa + BETA[i] * wb


NS, NT_PER_UNIT = 120, 40


def profile(t):
    """(sup_sigma LHS, min over sigma-endpoints of RHS) at fixed t."""
    bases = []
    for i in range(3):
        best = None
        for k in range(NS + 1):
            tau = SIG_LO + WIDTH * mpf(k) / NS
            v = fabs(G(i, mpc(tau, t)))
            if best is None or v < best:
                best = v
        bases.append(best)
    sup_l = mpf(0)
    for k in range(NS + 1):
        sigma = SIG_LO + WIDTH * mpf(k) / NS
        v = fabs((mpc(sigma, t) - 1) * zeta(mpc(sigma, t)))
        if v > sup_l:
            sup_l = v
    lr = []
    for sigma in (SIG_LO, SIG_HI):
        lr.append(sum(exponent(i, sigma) * log(bases[i]) for i in range(3)))
    return sup_l, exp(min(lr))


T_MAX = mpf(12)
N = int(T_MAX * NT_PER_UNIT)
print("Sampling t in [0,12] ...")
grid = []
for j in range(N + 1):
    t = T_MAX * mpf(j) / N
    u, r = profile(t)
    grid.append((t, u, r))

print()
print("Pointwise check (does the CLAIM itself hold at every sampled t?):")
bad = [(t, u, r) for (t, u, r) in grid if u >= r]
if not bad:
    worst = max(grid, key=lambda z: z[1] / z[2])
    print(f"  YES at every sampled t. Worst pointwise ratio "
          f"{mp.nstr(worst[1] / worst[2], 6)} at t = {mp.nstr(worst[0], 6)}")
else:
    print(f"  NO -- fails at {len(bad)} sampled t, first at t = {mp.nstr(bad[0][0], 6)}")

print()
print("Now: how coarse a t-partition still lets the DECOUPLED split work?")
print("(decoupling compares sup LHS over a box against inf RHS over the same box)")
print()
for width in [mpf(4), mpf(2), mpf(1), mpf('0.5'), mpf('0.25')]:
    nb = int(T_MAX / width)
    ok, worst_ratio, worst_box = True, mpf(0), None
    for b in range(nb):
        lo, hi = width * b, width * (b + 1)
        cell = [(t, u, r) for (t, u, r) in grid if lo <= t <= hi]
        U = max(u for (_, u, _) in cell)
        L = min(r for (_, _, r) in cell)
        ratio = U / L
        if ratio > worst_ratio:
            worst_ratio, worst_box = ratio, (lo, hi, U, L)
        if U >= L:
            ok = False
    lo, hi, U, L = worst_box
    print(f"  width {mp.nstr(width, 4):>6}: {nb:>3} boxes, worst U/L = "
          f"{mp.nstr(worst_ratio, 6):>9} on [{mp.nstr(lo, 4)},{mp.nstr(hi, 4)}]  "
          f"(U={mp.nstr(U, 6)}, L={mp.nstr(L, 6)})  {'OK' if ok else 'FAILS'}")

print()
print("Reference values at the endpoints, for cross-checking against the")
print("Sage script's table:")
for t0 in [mpf(0), mpf(4), mpf(8)]:
    u, r = profile(t0)
    print(f"  t = {int(t0):>2}:  sup LHS = {mp.nstr(u, 8):>12}   RHS_min = {mp.nstr(r, 8):>12}")
print()
print("t -> -t needs no separate scan: |(s-1)zeta(s)| and every |G_i| are")
print("invariant under conjugation.")
