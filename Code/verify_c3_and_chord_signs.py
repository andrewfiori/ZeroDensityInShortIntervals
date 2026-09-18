#!/usr/bin/env python3
"""Sign checks for the constants feeding `MainCorollary.C2Jensen_antitone_*` /
`C2Littlewood_antitone_*`.

The two antitonicity halves reduce (see `MainCorollary.C2Jensen_eq_affine`) to sign facts
about the affine-over-affine numerator coefficients

    P(t) = (2/D)(c1 + c2 loglog t/log t + c3/log t)                       (Jensen)
    Q(t) = alphaHat*P(t) + pi*B4/log t + 3.35 pi/(D t^{1/3} log t)
    P(t) = 2A1 + 2 pi A2 loglog t/log t + 2 pi A3/log t                   (Littlewood)
    Q(t) = 2A4 + 2 pi A5 loglog t/log t + pi A6/log t + (tiny)

so this script tests, over the admissible ranges:

  (1)  0 <= c3 r            for 0 < r < 1                 -> feeds `B3 >= 0`
  (2)  0 <= v_k             for all k                     -> feeds `A1 >= 0`
  (3)  log 0.611 <= v''_k   for all k                     -> the chord lower bound that makes
                                                              `2 pi A2 loglog t + 2 pi A3` positive
  (4)  the Littlewood combination  loglog t + chord''  >= 0  at log t > 20
  (5)  x -> (A2 log x + A3)/x decreasing for x > 20 (the `t`-antitonicity of the A2/A3 pair)

Everything here is elementary (no zeta / no Phi), so plain Python suffices.  The Phi/c5/c4
positivity facts are recorded in the Lean docstrings instead; they are sign-obvious
(`Phi(s) = sum_{n>=2} Lambda(n)/(log n)^2 n^{-s} > 0` for real `s >= 1`, and
`log|zeta(1+x)| > 0` for `x > 0`) but need Mathlib-level work.

Nothing here certifies a hypothesis-class field.  `ConstantSigns.c3_nonneg` is proved in Lean,
as are the `Jensen.JensenScaleConstants` sign facts behind (2) and (3), so this is an
independent re-check.  The method is deliberately cheap and is NOT certified: binary64 floats
throughout, a 1e-4 grid in r for (1) (about 10^4 radii), the `c3` series truncated at
jmax = 120 terms past K = Kidx r, and k swept only over -60 <= k <= 60 in (2), (3) and (4).
The exact-rational re-check of the same `c3_nonneg` argument is
`Code/verify_c3_tangent_route.py`.

Run:  python3 Code/verify_c3_and_chord_signs.py
"""

import math

LOG1546 = math.log(1.546)
LOG0611 = math.log(0.611)


def sigma(k):
    """`JensenScaleConstants.sigma`."""
    if k >= 0:
        return 1.0 - (k + 3.0) / (2.0 ** (k + 3) - 2.0)
    return ((-k) + 3.0) / (2.0 ** (-k + 3) - 2.0)


def vCoeff(k):
    """`JensenScaleConstants.vCoeff`."""
    if k >= 0:
        return 1.0 / (2.0 ** (k + 3) - 2.0)
    return sigma(-k) - 0.5 + 1.0 / (2.0 ** (-k + 3) - 2.0)


def vCoeffPP(k):
    """`JensenScaleConstants.vCoeffPP`."""
    if k > 0:
        return LOG1546
    if k == 0:
        return LOG0611
    return LOG1546 + (sigma(k) - 0.5) * math.log(math.pi)


def slope_intercept(v, k):
    """`(mCoeff k, bCoeff k)` for the coefficient family `v`.

    For `v = vCoeffPP` and `k >= 1` the two endpoint values coincide (`v''` is constant
    `log 1.546` past `k = 0`), so the slope is exactly `0`; taking that branch explicitly
    avoids a `0/0` once `sigma k` and `sigma (k+1)` collide in binary64."""
    s0, s1 = sigma(k), sigma(k + 1)
    if s0 == s1:
        assert v(k) == v(k + 1), "coincident sigma with distinct v"
        return 0.0, v(k)
    m = (v(k) - v(k + 1)) / (s0 - s1)
    return m, v(k) - m * s0


def chord(v, k, x):
    """Value at `x` of the chord through `(sigma k, v k)` and `(sigma (k+1), v (k+1))`,
    i.e. `mCoeff k * x + bCoeff k` for the corresponding `v`."""
    m, b = slope_intercept(v, k)
    return m * x + b


def theta(k, r):
    return math.asin(min(1.0, max(-1.0, (1.0 - sigma(k)) / r)))


def Kidx(r):
    """Least `k` with `1 - sigma k <= r`."""
    k = -60
    while 1.0 - sigma(k) > r:
        k += 1
        if k > 60:
            raise ValueError("no admissible index")
    return k


def c3(r, jmax=120):
    """`JensenScaleConstants.c3`, boundary term plus the (rapidly telescoping) tail."""
    K = Kidx(r)
    mK1, bK1 = slope_intercept(vCoeffPP, K - 1)
    total = (mK1 + bK1) * (math.pi / 2 - theta(K, r)) - mK1 * r * math.cos(theta(K, r))
    for j in range(jmax):
        k = K + j
        m, b = slope_intercept(vCoeffPP, k)
        total += (m + b) * (theta(k, r) - theta(k + 1, r))
        total += m * r * (math.cos(theta(k, r)) - math.cos(theta(k + 1, r)))
    return total


def main():
    print("=" * 72)
    print("(1)  c3 r >= 0  for 0 < r < 1")
    print("=" * 72)
    worst_r, worst = None, float("inf")
    r = 1e-4
    while r < 0.99999:
        val = c3(r)
        if val < worst:
            worst, worst_r = val, r
        r += 1e-4
    print(f"  min over r in (0,1) on a 1e-4 grid:  c3({worst_r:.4f}) = {worst:.8f}")
    print(f"  verdict: {'HOLDS' if worst >= 0 else '*** FAILS ***'}")
    for rr in (0.05, 0.1, 0.2, 1.0 / 3, 0.4, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8, 0.9, 0.95):
        print(f"    c3({rr:.4f}) = {c3(rr): .8f}   K = {Kidx(rr)}")

    print()
    print("=" * 72)
    print("(2)  v_k >= 0  for all k   (=> A1 >= 0, since A1 is a chord of v)")
    print("=" * 72)
    vmin = min(vCoeff(k) for k in range(-60, 61))
    print(f"  min over -60 <= k <= 60:  {vmin:.10f}   (limit as k -> -inf is 1/2)")
    print(f"  verdict: {'HOLDS' if vmin >= 0 else '*** FAILS ***'}")

    print()
    print("=" * 72)
    print("(3)  v''_k >= log 0.611  for all k  (v''_0 = log 0.611 attains it)")
    print("=" * 72)
    vals = [(k, vCoeffPP(k)) for k in range(-60, 61)]
    kmin, vppmin = min(vals, key=lambda p: p[1])
    print(f"  min over -60 <= k <= 60: v''({kmin}) = {vppmin:.10f}")
    print(f"  log 0.611 = {LOG0611:.10f}")
    print(f"  k -> -inf limit: log 1.546 - (1/2) log pi = "
          f"{LOG1546 - 0.5 * math.log(math.pi):.10f}")
    print(f"  verdict: {'HOLDS' if vppmin >= LOG0611 - 1e-15 else '*** FAILS ***'}")
    print("  NOTE: v''_k is genuinely NEGATIVE at k = 0 and for k << 0, so the Littlewood")
    print("        A3 term is NOT termwise nonnegative -- see (4).")

    print()
    print("=" * 72)
    print("(4)  A3 can be negative; the A2/A3 combination is still positive at log t > 20")
    print("=" * 72)
    print("  A3 = chord''(1-r) / (2 pi (r-alpha)), A2 = 1 / (2 pi (r-alpha)) (since v'_k == 1).")
    print("  So 2 pi A2 loglog t + 2 pi A3 = (loglog t + chord''(1-r)) / (r-alpha).")
    worst_chord = float("inf")
    for k in range(-40, 40):
        # the chord is affine, so its minimum over the segment is at an endpoint
        worst_chord = min(worst_chord, vCoeffPP(k), vCoeffPP(k + 1))
    print(f"  min chord'' value over every chord segment: {worst_chord:.10f}")
    print(f"  loglog t at t = 10^12: {math.log(math.log(10.0 ** 12)):.10f}")
    print(f"  loglog t + min chord'' = "
          f"{math.log(math.log(10.0 ** 12)) + worst_chord:.10f}")
    print(f"  verdict: {'HOLDS' if math.log(math.log(10.0**12)) + worst_chord > 0 else '*** FAILS ***'}")

    print()
    print("=" * 72)
    print("(5)  x -> (A2 log x + A3)/x is decreasing for x = log t > 20")
    print("=" * 72)
    print("  d/dx [(a log x + b)/x] = (a - a log x - b)/x^2 < 0  iff  a(log x - 1) > -b,")
    print("  and with a = 1, b = chord''(1-r) (after clearing 1/(2 pi (r-alpha))):")
    print(f"    log 20 - 1 = {math.log(20.0) - 1:.10f}  >  -min chord'' = {-worst_chord:.10f}")
    print(f"  verdict: {'HOLDS' if math.log(20.0) - 1 > -worst_chord else '*** FAILS ***'}")
    print("  (log t > 20 at t > 10^12 by `twenty_lt_log`, so log(log t) - 1 > log 20 - 1.)")


if __name__ == "__main__":
    main()
