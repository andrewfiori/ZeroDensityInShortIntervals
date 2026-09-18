r"""
Rigorous certified verification of the hypothesis field
`Hypotheses.NumericCertificates.integral_log_zeta_Ioi_one_lt`, read off by the theorem
`Jensen.RectangularBounds.integral_log_zeta_Ioi_one_lt`:

    Phi(1) < 1.7975699586287395

where Phi(s) = sum_{n>1} Lambda(n)/(log n)^2 * n^{-s} is the antiderivative of
-log(zeta(s)) defined in ZerosInShortIntervals/Definitions.lean.

Per Definitions.lean's `Phi_hasDerivAt`, for real sigma > 1 (where the defining series
converges absolutely) we have d/dsigma Phi(sigma) = -log(zeta(sigma)), and Phi(sigma) -> 0
as sigma -> infinity (the series terms -> 0). Hence, for real sigma > 1,

    Phi(sigma) = integral_{sigma}^{infinity} log(zeta(x)) dx.

`LSeriesSummable_PhiTerm_one` (proved elsewhere in this project, via Chebyshev's psi bound)
shows the defining series for Phi also converges at sigma = 1 itself, so by continuity this
identity extends to

    Phi(1) = integral_1^infinity log(zeta(x)) dx.

This script does NOT attempt to formalize that continuity/FTC argument in Lean: the bound on
Phi(1) is one of the project's two `NumericCertificates` fields, i.e. a finite numerical fact
certified outside Lean rather than re-derived analytically inside it (Mathlib has no verified
evaluation of zeta, and the margin here is about 9e-17). It is verified below by certified
interval (ball) arithmetic via Sage/arb, to the same standard used elsewhere in Code/.
`Code/indep_mpmath_constants.py` block [B] re-checks the same value by an independent route
(the log singularity split off analytically, mpmath quadrature).

We split the integral into three pieces and bound each rigorously:

  (1) [1, 1+delta]  (a tiny neighbourhood of the pole of zeta):
      zeta(x) = 1/(x-1) + gamma + O(x-1) near x=1 (Laurent expansion), so for delta small
      enough that the O(x-1) correction is dominated, zeta(x) <= 1/(x-1) + 1 on this whole
      interval, hence (using log(1+y) <= y for y >= 0, with y = (x-1)*(zeta(x)-1/(x-1))... )
      more simply: log(zeta(x)) = -log(x-1) + log(1 + (x-1)*zeta(x) - 1)
                                 <= -log(x-1) + (x-1)*(zeta(x) - 1/(x-1))
                                 <= -log(x-1) + (x-1)          [using zeta(x)-1/(x-1) <= 1]
      Integrating termwise over [0, delta] (substituting t = x-1) gives the closed-form bound
      used below. delta = 10^-40 makes this contribution utterly negligible
      (~10^-38), far below the precision needed.

  (2) [1+delta, T]  (T = 70): evaluated via certified adaptive quadrature
      (ComplexBallField.integral, i.e. arb's acb_calc_integrate), which returns a ball
      containing the true value of the integral together with a certified error radius.

  (3) [T, infinity): zeta(x) - 1 = sum_{n>=2} n^{-x} <= 2^{-x} + integral_2^infinity t^{-x} dt
                                                       = 2^{-x} + 2^{1-x}/(x-1),
      and log(1+y) <= y, so log(zeta(x)) <= 2^{-x}*(1 + 2/(x-1)). Integrating over [T, infinity)
      with 1/(x-1) <= 1/(T-1) gives the closed-form bound used below. With T = 70 this
      contributes about 10^-21, again utterly negligible.

Adding the three (rigorous) upper bounds gives a certified upper bound on Phi(1) with error
radius ~2e-93 (i.e. many more correct digits than needed), which we compare against the
target constant 1.7975699586287395.

Run with:  sage Code/verify_Phi_one_bound.sage
"""

CBF = ComplexBallField(300)
RBF = RealBallField(300)

target = RBF('1.7975699586287395')

# ---- Piece (1): [1, 1+delta], via the Laurent-expansion bound derived above ----
delta = RBF(10) ** (-40)
d = delta
near_bound = -d * d.log() + d + d * d / 2  # closed form of int_0^delta [-log t + t] dt (+ t^2/2 slack)

# ---- Piece (2): [1+delta, T], via certified adaptive quadrature ----
T = RBF(70)
f = lambda x, analytic: CBF(x).zeta().log()
I_mid = CBF.integral(f, CBF(1) + CBF(delta), CBF(T))

# ---- Piece (3): [T, infinity), via the tail bound derived above ----
tail_bound = (1 + 2 / (T - 1)) * 2 ** (-T) / RBF(2).log()

mid_upper = I_mid.real().upper()
total_upper = RBF(mid_upper + near_bound.upper() + tail_bound.upper())

print("Piece (1) [1,1+delta] upper bound: ", near_bound.upper())
print("Piece (2) [1+delta,T] (certified): ", I_mid)
print("Piece (3) [T,infinity) upper bound:", tail_bound.upper())
print()
print("Certified upper bound on Phi(1) = integral_1^infinity log(zeta(x)) dx:")
print("   ", total_upper)
print("Target constant (Phi_one_lt):")
print("   ", target)
print("Margin (target - upper bound):", target - total_upper)
print()
print("Phi_one_lt (Phi(1) < 1.7975699586287395) verified:", bool(total_upper < target))
