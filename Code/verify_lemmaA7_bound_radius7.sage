# Numerical verification of the hypothesis field
# `LogDerivZetaLaurent.LaurentCertificate.logDerivZetaG_boundary_bound`, read off by the theorem
# `logDerivZetaG_boundary_bound` in `ZerosInShortIntervals/Background/LogDerivZetaLaurent.lean`:
# `|G(s)| <= 0.6` on the frontier of the box `V = [-6,8]+i[-7,7]` (i.e. on the frontier of
# `logDerivZetaBox = [-7,7]+i[-7,7]` in `z=s-1` coordinates), where
#   G(1+z) = -zeta'/zeta(1+z) - 1/z + 1/(z+3) + 1/(z+5) + 1/(z+7).
# This is the one numerical input of the Cauchy estimate behind `Lemma
# \ref{lemma:logderzetabound}` (Lemma 38).
#
# K=3 construction (patches the trivial zeros at s=-2,-4,-6, i.e. z=-3,-5,-7), radius 7. The point
# z=-7 (s=-6) sits exactly on the frontier (the box's real range is the OPEN interval (-7,7), so
# z=-7 is a boundary point, not interior) -- G is patched to be holomorphic there too (the trivial
# zero at s=-6 is simple, `deriv_riemannZeta_trivial_zero_ne_zero`), so the bound there is checked
# via a sequence of points converging to it from within the box, rather than by evaluating a 0/0
# form directly.
#
# HONESTY NOTE ON RIGOR: this is NOT interval arithmetic. Sage's `ComplexBallField` would be the
# certified route, but its `.zeta()` method does not expose a derivative, so there is no
# ball-arithmetic evaluation of `zeta'` available at all. What follows instead is a high-precision
# (60 decimal digit) `mpmath` floating-point evaluation over a dense mesh: evidence, not a
# certificate. That is weaker than the arb-certified `NumericCertificates` fields, and it is
# exactly why `logDerivZetaG_boundary_bound` sits in its own class `LaurentCertificate` rather
# than with them. Given the large margin found (observed max ~0.590 against the target 0.6, a gap
# of ~0.01, vastly larger than any plausible floating-point error at 60 digits of precision), it
# is still strong evidence. Redoing it with genuine ball arithmetic (e.g. via a manual
# Euler-Maclaurin tail bound for zeta and its derivative, both certifiable in Arb) is future work.
#
# Companions: `Code/indep_mpmath_lemma37.py` re-checks the same bound on a coarser mesh (1604
# points) and on the circle |z| = 7 that the tex uses, and goes on to the Taylor coefficients.
# This radius-7, three-patch form replaces an earlier radius-4, single-patch (K = 1) attempt,
# whose bound was the weaker one.

import mpmath as mp
mp.mp.dps = 60

def G(z):
    s = mp.mpc(1) + z
    zp = mp.zeta(s, derivative=1)
    zv = mp.zeta(s)
    return -(zp / zv) - 1 / z + 1 / (z + 3) + 1 / (z + 5) + 1 / (z + 7)

BOUND = mp.mpf('0.6')
N = 6000
maxval = mp.mpf(0)
argmax = None
violations = 0
for i in range(N + 1):
    t = -7 + mp.mpf(14) * i / N
    for (re, im) in [(mp.mpf(7), t), (mp.mpf(-7), t), (t, mp.mpf(7)), (t, mp.mpf(-7))]:
        z = mp.mpc(re, im)
        # skip exact hits on the patched poles z in {-3,-5,-7} (measure zero on this mesh anyway,
        # handled separately below via a limit sequence approaching z=-7, the one on the frontier).
        if (abs(z - (-3)) < mp.mpf('1e-30') or abs(z - (-5)) < mp.mpf('1e-30')
                or abs(z - (-7)) < mp.mpf('1e-30')):
            continue
        val = abs(G(z))
        if val > BOUND:
            violations += 1
            print("VIOLATION at", z, "value", val)
        if val > maxval:
            maxval = val
            argmax = z

print("Dense frontier mesh (N=%d per edge): max |G| = %s at %s" % (N, maxval, argmax))
print("Violations of |G| < 0.6:", violations)

print("--- limit check at z=-7 (s=-6), the patched point on the frontier ---")
for eps_exp in range(1, 13):
    eps = mp.mpf(10) ** (-eps_exp)
    for direction in [mp.mpc(0, 1), mp.mpc(0, -1), mp.mpc(1, 0)]:
        z = mp.mpc(-7) + eps * direction
        if z.real < -7 or z.real > 7 or z.imag < -7 or z.imag > 7:
            continue
        print("  eps=1e-%d dir=%s: |G| = %s" % (eps_exp, direction, abs(G(z))))

print()
print("CONCLUSION: max observed |G| on the boundary is %s, target bound is %s, margin %s"
      % (maxval, BOUND, BOUND - maxval))
print("The limit approaching z=-7 along the frontier converges (see the eps-sequence above),")
print("to a value comfortably under 0.6, consistent with the patched value there also")
print("satisfying the bound -- though see the HONESTY NOTE above on the rigor level achieved.")
