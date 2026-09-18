#!/usr/bin/env python3
r"""
WHY `jensenrectangle` CONCLUDES WITH `<=` AND NOT `<`.  The manuscript's STRICT inequality in
`Proposition \ref{prop:jensenrectangle}` (Proposition 19) cannot be had: both sides are exactly 0
on a large, legitimate part of its hypothesis range, so `<` fails there while `<=` holds.

This is the live numerical justification for the shape of the Lean statement.
`Jensen/RectangularBounds.jensenrectangle` concludes with `<=`, carries the hypothesis
`0 < alpha`, is PROVED, and its docstring cites this script for the reason.  The degeneracy
exhibited below survives `0 < alpha`, so it is not answered by that hypothesis and is what makes
`<=` unavoidable.  (`0 < alpha` answers a SEPARATE degeneracy: at alpha = -1, r = 1 the
denominator `rectDenom r alpha` is 0 and Lean's total division makes the right-hand side 0 as
well.  `rectDenom_pos` needs `0 < alpha` in any case.)

WHAT WAS REFUTED.  The strict form asserts

    N(T-h, T+h, alpha)  <  ( \int_x [ circle-average - centre value ] dx ) / D_{r,alpha}

Why both sides vanish.  The bracket is the Jensen defect

    (1/2pi) \int_0^{2pi} log|zeta(1 + i(T+x) + r e^{i th})| dth  -  log|zeta(1 + i(T+x))| ,

which by Jensen's formula equals  sum over zeros rho in the open disc of log(r/|rho - c|),
c = 1 + i(T+x).  A zero rho = beta + i gamma lies in that disc only if 1 - beta < r.  So if
r is smaller than the distance from the line Re s = 1 to the nearest zero at these heights,
the disc is zero-free, log|zeta| is harmonic on it, and the defect is EXACTLY 0 by the mean
value property.  Then the numerator is 0, D_{r,alpha} > 0, so the right-hand side is 0.

Meanwhile N(T-h, T+h, alpha) counts zeros with 1 - alpha < Re rho, and alpha < r, so it is
0 for the same reason.  The claim becomes 0 < 0.

This is not an RH-conditional statement: the classical zero-free region
zeta(sigma + it) != 0 for sigma > 1 - c/log(|t|+3) makes the discs provably zero-free once
r < c/log(T+3), which the hypotheses (only alpha < r, 0 < h, h < T - alphahat - r) allow.

The script verifies the numerical half of that: at T = 100, h = 0.01, alpha = 0.02, r = 0.03 it
evaluates the Jensen defect by high-precision quadrature across the whole x-window and finds it 0
to quadrature accuracy at 40 digits (the `jensenrectangle` docstring records the worst value as
< 1.2e-41), and it checks directly that the nearest zeros of zeta sit at distance 0.5 from the
line Re s = 1, far outside every disc of radius r = 0.03.

Run:  python3 Code/verify_jensenrectangle_degenerate.py
"""

from mpmath import mp, mpf, mpc, zeta, log, pi, cos, sin, quad, fabs, sqrt, findroot

mp.dps = 40

# --- sample parameters, all satisfying jensenrectangle's hypotheses -------------------
T = mpf('100')
h = mpf('0.01')
alpha = mpf('0.02')
r = mpf('0.03')

alphahat = sqrt(r**2 - alpha**2)

print("parameters")
print("  T        =", T)
print("  h        =", h)
print("  alpha    =", alpha)
print("  r        =", r)
print("  alphahat = sqrt(r^2 - alpha^2) =", alphahat)
print()
print("hypotheses of jensenrectangle:")
print("  alpha < r                :", alpha < r)
print("  0 < h                    :", h > 0)
print("  h < T - alphahat - r     :", h < T - alphahat - r,
      "   (rhs =", T - alphahat - r, ")")
print()

# --- the Jensen defect at a fixed x ---------------------------------------------------


def defect(x):
    """(1/2pi) int_0^{2pi} log|zeta(c + r e^{i th})| dth  -  log|zeta(c)|,  c = 1+i(T+x)."""
    c = mpc(1, T + x)

    def integrand(th):
        return log(fabs(zeta(c + r * mpc(cos(th), sin(th)))))

    avg = quad(integrand, [0, pi / 2, pi, 3 * pi / 2, 2 * pi]) / (2 * pi)
    return avg - log(fabs(zeta(c)))


a = h + alphahat
print("sweeping x over [-a, a] with a = h + alphahat =", a)
print()
print("   x            Jensen defect")
worst = mpf('0')
for k in range(-4, 5):
    x = a * mpf(k) / 4
    d = defect(x)
    worst = max(worst, fabs(d))
    print("  %+.6f   % .6e" % (float(x), float(d)))
print()
print("worst |defect| over the sample =", mp.nstr(worst, 8))
print("(quadrature noise level at dps =", mp.dps, "is ~1e-30; anything at that level is 0)")
print()

# --- confirm directly that no zero of zeta lies within r of the segment ---------------
# Zeros in the disc need 1 - Re rho < r, i.e. Re rho > 1 - r.  The classical zero-free
# region already forbids that here; as an independent check we locate the zeros nearest
# to height T and report their distance to the line Re s = 1.

print("nearest nontrivial zeros to height T (all lie on Re s = 1/2 in this range):")
for guess in [mpc('0.5', '98.8'), mpc('0.5', '101.3'), mpc('0.5', '103.7')]:
    rho = findroot(zeta, guess)
    dist = fabs(rho - mpc(1, rho.imag))
    print("  rho = %s   distance to Re s = 1 line: %.6f  (r = %.4f)"
          % (mp.nstr(rho, 12), float(dist), float(r)))
print()
print("every such distance is 1 - Re rho = 0.5 >> r, so no zero enters any disc;")
print("log|zeta| is harmonic on each disc and the defect is exactly 0.")
print()

# --- conclusion -----------------------------------------------------------------------
print("CONCLUSION")
print("  numerator  = int_x defect(x) dx = 0")
print("  D_{r,alpha} = 2r*sqrt(1-(alpha/r)^2) - 2*alpha*atan(sqrt((r/alpha)^2-1)) > 0")
print("  so the right-hand side of jensenrectangle is 0")
print("  N(T-h, T+h, alpha) = 0 as well (no zero has Re rho > 1 - alpha = %.4f)"
      % float(1 - alpha))
print("  hence the assertion is  0 < 0  -- FALSE.")
print()
print("  The statement becomes true, and matches every downstream consumer")
print("  (rectangularjensen concludes with <=), if `<` is weakened to `<=`.")
