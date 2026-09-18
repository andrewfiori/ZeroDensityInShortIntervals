#!/usr/bin/env python3
r"""
EXPLORATORY REGIME ANALYSIS -- NOT a current certificate for anything in Lean.

Question asked: does the very-large-h regime (h > t, far past the tex's h = t^{2/3} case
boundary) give an easy resolution of `Corollary \ref{cor:main-jensen}` (Corollary 4) and
`Corollary \ref{cor:main-littlewood}` (Corollary 5)?

Answer: no.  The h > t^{2/3} branch was dropped instead.  Both corollaries are now stated on
t^{2/3} > h > h_0 and are PROVED --
`MainCorollary.mainPositiveProportionCorollary_jensen`/`_littlewood` -- so no Lean statement
depends on anything below.  This script is kept only as the record of how far the large-h regime
is from closing, and of the Lsym idea that was tried there.

The Corollaries bound   N(t-h,t+h,alpha) / (N(t+h)-N(t-h))  <  C_2  (~1/2).

For large h the numerator is controlled by the classical zero-density input the
tex's own sketch uses,
    N(t-h,t+h,alpha)  <<  (t+h)^{(8/3)alpha} log(t+h)^3,
(implied constant taken as 1, as in the theorem-side table), while the
denominator GROWS with h.  So the ratio improves as h grows.  The question is
WHERE it first drops below 1/2, and whether h > t is the relevant threshold.

Denominator, three variants:
  L      (h < t^{2/3}):  ((1/pi)log(t/2pi) - (1-log2)h^2/(pi t^2))h - .194 log t - 9.908
         -- the sharp (1-log2)/pi coefficient, matching `MainCorollary.Lbound`.
  Ltilde (h >= t^{2/3}): (h/2pi)log(t/2pi) - 0.097 log(t(t+h)) - 9.908
         -- the tex's separate bound above the case boundary, where Bellotti-Wong can no longer
         be applied at the lower endpoint t-h.
  Lsym   (h > t): once h > t the window (t-h, t+h) dips below the real axis, so the zero count
         in it is N(t+h) + N(h-t) rather than N(t+h) - N(t-h); this variant uses
         M(x) = (x/2pi)log(x/(2 pi e)) with the Bellotti-Wong tail applied at both ends.

Method: mpmath at 30 decimal digits, tabulation plus bisection.  Indicative, not ball arithmetic.
"""

from mpmath import mp, mpf, log, pi, exp, nstr

mp.dps = 30

T0 = 3 * mpf(10) ** 12
ALPHAS = [mpf(1) / 6, mpf(1) / 7, mpf(1) / 9]


def density(alpha, t, h):
    x = t + h
    return x ** (mpf(8) / 3 * alpha) * log(x) ** 3


def L(h, t):
    return ((log(t / (2 * pi)) / pi - (1 - log(2)) * h ** 2 / (pi * t ** 2)) * h
            - mpf('0.194') * log(t) - mpf('9.908'))


def Ltilde(h, t):
    return (h / (2 * pi)) * log(t / (2 * pi)) - mpf('0.097') * log(t * (t + h)) - mpf('9.908')


def M(x):
    return (x / (2 * pi)) * log(x / (2 * pi * exp(1)))


def Lsym(h, t):
    """h > t: the interval dips below the axis, so the zero count is
    N(t+h) + N(h-t), not N(t+h). Bellotti-Wong tail applied at both ends."""
    return M(t + h) + M(h - t) - mpf('0.097') * log((t + h) * (h - t)) - 2 * mpf('4.954')


t = T0
print(f"t = 3e12,  t^(2/3) = {nstr(t ** (mpf(2) / 3), 8)},  t = {nstr(t, 8)}")
print()
print("ratio = [density bound] / [denominator];  need < 1/2")
print()

for alpha in ALPHAS:
    print(f"alpha = 1/{int(1/alpha + mpf('0.5'))}")
    print(f"    {'h':>16} {'h/t^(2/3)':>12} {'denominator':>16} {'ratio':>14}  verdict")
    for mult, lab in [(1, "t^(2/3)"), (2, ""), (5, ""), (10, ""), (20, ""),
                      (50, ""), (100, "")]:
        h = mult * t ** (mpf(2) / 3)
        den = Ltilde(h, t) if h >= t ** (mpf(2) / 3) else L(h, t)
        r = density(alpha, t, h) / den
        print(f"    {nstr(h, 8):>16} {mult:>12} {nstr(den, 8):>16} {nstr(r, 8):>14}"
              f"  {'OK' if r < mpf(1)/2 else 'fails'}   {lab}")
    # now the h > t regime, both with and without the author's improvement
    for mult, lab in [(1, "h = t"), (2, "h = 2t"), (10, "h = 10t")]:
        h = mult * t
        base = Ltilde(h, t)
        sym = Lsym(h, t) if h > t else base
        rb = density(alpha, t, h) / base
        rs = density(alpha, t, h) / sym
        print(f"    {nstr(h, 8):>16} {'':>12} {nstr(base, 8):>16} {nstr(rb, 8):>14}"
              f"  {'OK' if rb < mpf(1)/2 else 'fails'}   {lab}"
              + (f"   [with N(h-t): ratio {nstr(rs, 6)}, denom x{nstr(sym/base, 4)}]"
                 if mult > 1 else ""))
    print()

print("Where does the ratio first drop below 1/2?  (bisection in h, using Ltilde)")
for alpha in ALPHAS:
    lo, hi = t ** (mpf(2) / 3), 100 * t
    if density(alpha, t, hi) / Ltilde(hi, t) >= mpf(1) / 2:
        print(f"    alpha = 1/{int(1/alpha + mpf('0.5'))}: still fails at h = 100t")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if density(alpha, t, mid) / Ltilde(mid, t) < mpf(1) / 2:
            hi = mid
        else:
            lo = mid
    print(f"    alpha = 1/{int(1/alpha + mpf('0.5'))}: h* = {nstr(hi, 8)}"
          f"  = {nstr(hi / t ** (mpf(2)/3), 6)} * t^(2/3)"
          f"  = {nstr(hi / t, 6)} * t")
