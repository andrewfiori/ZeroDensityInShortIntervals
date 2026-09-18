#!/usr/bin/env python3
r"""Would raising the large-h threshold from t^{2/3} to t^{3/4} let zero density close case (i)?

EXPLORATORY REGIME ANALYSIS -- NOT a current certificate.  The threshold was not raised: the
h > t^{2/3} branch was dropped altogether.  `Theorem \ref{thm:main-jensen}` (Theorem 2),
`Theorem \ref{thm:main-littlewood}` (Theorem 3) and Corollaries
`\ref{cor:main-jensen}`/`\ref{cor:main-littlewood}` (Corollaries 4 and 5) are stated on
h <= t^{2/3} (resp. t^{2/3} > h > h_0) and PROVED there.  Nothing in Lean depends on the numbers
below.

Background.  The tex's earlier proof sketch for Theorem 2 splits at h = t^{2/3}.  Case (i),
h > t^{2/3}, is disposed of by "standard zero-density estimates":

    Nrect(t-h,t+h,alpha) <= [Farzanfard Cor 4.50]  <  U_J(alpha,r,h,t).

`verify_kln_large_h_case.py` showed the middle inequality FAILS at h = t^{2/3}, t = 3e12 near the
top of the alpha range (factor 20.8 off at alpha=1/7).

Why raising the threshold helps: U_J is essentially LINEAR in h, while the zero-density bound
depends on t+h ~ t and is nearly constant in h over this range.  So the larger the threshold, the
easier case (i) becomes.  Going from t^{2/3} to t^{3/4} multiplies U_J's leading part by about
t^{1/12}, which at t = 3e12 is a factor of ~11.

This script asks, for a general threshold exponent theta (h = t^theta):
  (A) at theta = 2/3, 0.7, 3/4, 0.8: does case (i) hold at the floor t = 3e12, and from what t?
  (B) what is the SMALLEST theta that closes case (i) at t = 3e12, per alpha?
  (C) how wide is the leftover gap t^{2/3} < h < t^theta that would then need separate treatment?

Farzanfard Cor 4.50 needs T2 >= 3e12; we also keep t - h >= 3e12.

Pure-Python (mpmath only); no Sage required.  mpmath at 40 decimal digits, tabulation plus
bisection -- indicative, not ball arithmetic.
"""
import mpmath as mp

mp.mp.dps = 40

C_U = mp.mpf('12.45321')     # Farzanfard Cor 4.50 leading constant
C_V = mp.mpf('3.869')        # Farzanfard Cor 4.50 secondary constant
H0 = 3 * mp.mpf(10) ** 12    # Platt-Trudgian height = Cor 4.50's T2 floor

# alpha, r, B1, B2, B3, B4, alphahat_r --- tex Table \ref{tab:rectangularjensen} (Table 5)
TABLE = [
    (mp.mpf(1) / 7, '0.5647100', '0.2457053', '0.3900919', '1.450119', '6.518765', '0.5463417'),
    (mp.mpf(1) / 8, '0.5185446', '0.2294753', '0.4239720', '1.514935', '6.977388', '0.5032529'),
    (mp.mpf(1) / 9, '0.5030821', '0.2172051', '0.4340594', '1.446353', '6.922300', '0.4906586'),
    (mp.mpf(1) / 10, '0.4821212', '0.2079206', '0.4778655', '1.331336', '7.058488', '0.4716364'),
    (mp.mpf(1) / 16, '0.2909922', '0.1663861', '1.250289', '0.5551999', '12.302409', '0.2842010'),
]


def zero_density_rhs(alpha, T2):
    L = mp.log(T2)
    return C_U * T2 ** (mp.mpf(8) / 3 * alpha) * L ** (3 + 2 * alpha) + C_V * L ** 2


def UJ(ahat, B1, B2, B3, B4, h, t):
    L = mp.log(t)
    return (2 * h + 2 * ahat) * (B1 / mp.pi * L + B2 * mp.log(L) + B3) + B4


def holds(alpha, ahat, B1, B2, B3, B4, t, theta):
    h = t ** mp.mpf(theta)
    if t - h < H0:
        return None                      # Cor 4.50 not applicable
    return zero_density_rhs(alpha, t + h) < UJ(ahat, B1, B2, B3, B4, h, t)


def ratio(alpha, ahat, B1, B2, B3, B4, t, theta):
    h = t ** mp.mpf(theta)
    return zero_density_rhs(alpha, t + h) / UJ(ahat, B1, B2, B3, B4, h, t)


def main():
    thetas = [mp.mpf(2) / 3, mp.mpf('0.7'), mp.mpf(3) / 4, mp.mpf('0.8')]

    print("=" * 92)
    print("(A) ratio  [zero-density bound] / U_J  at the floor t = 3e12.  Need < 1.")
    print("=" * 92)
    print(f"{'alpha':>8} " + " ".join(f"{'theta=' + mp.nstr(th, 4):>16}" for th in thetas))
    for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
        B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
        cells = []
        for th in thetas:
            rr = ratio(alpha, ahat, B1, B2, B3, B4, H0, th)
            cells.append(f"{mp.nstr(rr, 5):>11}{'  OK' if rr < 1 else '  no'}")
        print(f"{mp.nstr(alpha, 5):>8} " + " ".join(cells))

    print()
    print("=" * 92)
    print("(B) smallest threshold exponent theta that closes case (i) AT t = 3e12")
    print("=" * 92)
    for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
        B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
        lo, hi = mp.mpf('0.5'), mp.mpf('1.0')
        if ratio(alpha, ahat, B1, B2, B3, B4, H0, hi) >= 1:
            print(f"  alpha={mp.nstr(alpha, 6):>10}:  fails even at theta = 1 (h = t)")
            continue
        for _ in range(200):
            mid = (lo + hi) / 2
            if ratio(alpha, ahat, B1, B2, B3, B4, H0, mid) < 1:
                hi = mid
            else:
                lo = mid
        h_at = H0 ** hi
        print(f"  alpha={mp.nstr(alpha, 6):>10}:  theta >= {mp.nstr(hi, 6):>9}   "
              f"(h >= {mp.nstr(h_at, 6)} = 10^{float(mp.log(h_at, 10)):.2f})")

    print()
    print("=" * 92)
    print("(C) crossover t, theta = 3/4 versus theta = 2/3")
    print("=" * 92)

    def crossover(alpha, ahat, B1, B2, B3, B4, theta):
        def ok(texp):
            return ratio(alpha, ahat, B1, B2, B3, B4, mp.mpf(10) ** texp, theta) < 1
        lo, hi = 12.48, 100000.0
        if ok(lo):
            return None                       # already holds at the floor
        if not ok(hi):
            return mp.inf
        for _ in range(200):
            mid = (lo + hi) / 2
            if ok(mid):
                hi = mid
            else:
                lo = mid
        return hi

    def fmt(c):
        if c is None:
            return "floor (3e12)"
        if c == mp.inf:
            return "never"
        return f"10^{c:.2f}"

    print(f"{'alpha':>10} {'theta=2/3':>16} {'theta=3/4':>16}")
    for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
        B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
        c23 = crossover(alpha, ahat, B1, B2, B3, B4, mp.mpf(2) / 3)
        c34 = crossover(alpha, ahat, B1, B2, B3, B4, mp.mpf(3) / 4)
        print(f"{mp.nstr(alpha, 6):>10} {fmt(c23):>16} {fmt(c34):>16}")
    print()
    print("  Asymptotically the condition is just theta > (8/3)alpha (log powers are lower")
    print("  order), so theta=2/3 suffices for every alpha < 1/4 once t is large enough.")
    print("  The whole difficulty is at the FLOOR t = 3e12, where the constants and the")
    print("  (log t)^{3+2alpha} factor dominate.  Raising theta buys a factor t^{theta-2/3}.")

    print()
    print("=" * 92)
    print("(D) how wide is the leftover gap  t^{2/3} < h < t^{3/4} ?")
    print("=" * 92)
    for texp in [12.48, 13, 15, 20, 50]:
        t = mp.mpf(10) ** texp
        h1, h2 = t ** (mp.mpf(2) / 3), t ** (mp.mpf(3) / 4)
        print(f"  t=10^{texp:<6}  t^(2/3)=10^{float(mp.log(h1,10)):.2f}   "
              f"t^(3/4)=10^{float(mp.log(h2,10)):.2f}   width = 10^{float(mp.log(h2/h1,10)):.2f} "
              f"= t^{float(texp/12/texp*12/12):.4f}... (t^(1/12))")
    print("  the gap is a factor t^{1/12} wide -- at the floor that is only ~11x,")
    print("  but it grows with t, so it is a genuine region, not a boundary case.")


if __name__ == "__main__":
    main()
