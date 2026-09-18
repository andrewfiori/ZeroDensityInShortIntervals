r"""Does the tex's `h > t^{2/3}` sketch survive explicit constants?

EXPLORATORY REGIME ANALYSIS -- NOT a current certificate.  Answer: no, and the branch was dropped
rather than repaired.  `Theorem \ref{thm:main-jensen}` (Theorem 2),
`Theorem \ref{thm:main-littlewood}` (Theorem 3), `Corollary \ref{cor:main-jensen}` (Corollary 4)
and `Corollary \ref{cor:main-littlewood}` (Corollary 5) are all stated on `h <= t^{2/3}` (resp.
`t^{2/3} > h > h_0`) and are PROVED there.  This script is the numerical record of WHY the branch
was dropped, and is cited as such by the Lean docstrings of
`MainTheorem.Nrect_le_zero_density_bound` and of
`MainCorollary.mainPositiveProportionCorollary_jensen`/`_littlewood` (which point at Parts 3a and
3b below) -- so its part numbering is load-bearing and should not be changed.

The remark after Theorem 2 disposes of the case `h > t^{2/3}`, `t > 10^12` by

    N(t-h,t+h,alpha) << (t+h)^{(8/3)alpha} log(t+h)^3 << U_J(alpha,r,h,10^12) < U_J(alpha,r,h,t)

with the `<<` justified by "standard zero-density estimates", citing Kadiri-Lumley-Ng. The
details are deliberately omitted. This script substitutes an EXPLICIT zero-density bound and
checks whether the middle inequality actually holds.

Explicit input: Farzanfard, "Explicit zero density for the Riemann zeta function", MSc thesis,
University of Lethbridge (2025), Corollary 4.50 --- an INTERVAL bound, which is what is needed
here (KLN's own Theorem 1.1 bounds N(sigma,T), a count from height 0):

    N(sigma, T1, T2) <= 12.45321 * T2^{(8/3)(1-sigma)} * (log T2)^{5-2 sigma}
                        + 3.869 * (log T2)^2                    for T2 >= 3e12, sigma in [0.75,1]

In this project's convention `Nrect T1 T2 alpha` counts zeros with `Re rho > 1 - alpha`, i.e.
sigma = 1 - alpha, so with `alpha in [0, 0.25]` the bound reads

    Nrect(T1,T2,alpha) <= 12.45321 * T2^{(8/3)alpha} * (log T2)^{3+2 alpha} + 3.869 (log T2)^2.

Compared against, from `Theorem \ref{thm:main-jensen}` (Theorem 2),

    U_J(alpha,r,h,t) = (2h + 2 alphahat_r)(B1/pi log t + B2 loglog t + B3) + B4.

`B1..B4` and `alphahat_r` are the paper's own optimised values, Table
`\ref{tab:rectangularjensen}` (Table 5).

Method: mpmath at 40 decimal digits, tabulation plus bisection.  Indicative, not ball arithmetic.
"""
import mpmath as mp

mp.mp.dps = 40

C_U = mp.mpf('12.45321')     # Farzanfard Cor 4.50 leading constant
C_V = mp.mpf('3.869')        # Farzanfard Cor 4.50 secondary constant
H0 = 3 * mp.mpf(10) ** 12    # Platt-Trudgian verification height = Cor 4.50's T2 floor

# alpha, r, B1, B2, B3, B4, alphahat_r  --- tex Table \ref{tab:rectangularjensen} (Table 5)
TABLE = [
    (mp.mpf(1) / 7, '0.5647100', '0.2457053', '0.3900919', '1.450119', '6.518765', '0.5463417'),
    (mp.mpf(1) / 8, '0.5185446', '0.2294753', '0.4239720', '1.514935', '6.977388', '0.5032529'),
    (mp.mpf(1) / 9, '0.5030821', '0.2172051', '0.4340594', '1.446353', '6.922300', '0.4906586'),
    (mp.mpf(1) / 10, '0.4821212', '0.2079206', '0.4778655', '1.331336', '7.058488', '0.4716364'),
    (mp.mpf(1) / 16, '0.2909922', '0.1663861', '1.250289', '0.5551999', '12.302409', '0.2842010'),
    (mp.mpf(1) / 64, '0.09924636', '0.1023306', '3.292282', '1.434352', '33.994587', '0.09800867'),
    (mp.mpf(1) / 1024, '0.01014060', '0.05652525', '28.889451', '12.586295',
     '309.383987', '0.01009347'),
]


def zero_density_rhs(alpha, T2):
    """Farzanfard Cor 4.50, in this project's `alpha = 1 - sigma` convention."""
    L = mp.log(T2)
    return C_U * T2 ** (mp.mpf(8) / 3 * alpha) * L ** (3 + 2 * alpha) + C_V * L ** 2


def UJ(alpha, ahat, B1, B2, B3, B4, h, t):
    L = mp.log(t)
    return (2 * h + 2 * ahat) * (B1 / mp.pi * L + B2 * mp.log(L) + B3) + B4


print("=" * 88)
print("Is  zero-density bound  <  U_J  ?   at the SMALLEST admissible h, i.e. h = t^{2/3}")
print("(the tex's own comparison uses U_J at t=10^12, which is smaller still, so this is")
print(" already the generous reading)")
print("=" * 88)
print(f"{'alpha':>9} {'t':>10} {'h=t^(2/3)':>13} {'density bd':>14} {'U_J':>14} {'ratio':>10}  ok?")
worst = {}
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
    for texp in [12.5, 13, 14, 16, 20, 30, 50, 100, 200, 500]:
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        if t - h < H0:          # Cor 4.50 needs T2 >= 3e12; t-h >= H0 keeps T1 admissible too
            continue
        lhs = zero_density_rhs(alpha, t + h)
        rhs = UJ(alpha, ahat, B1, B2, B3, B4, h, t)
        ratio = lhs / rhs
        ok = lhs < rhs
        worst.setdefault(alpha, []).append((texp, ratio, ok))
        print(f"{mp.nstr(alpha,5):>9} {'1e%g' % texp:>10} {mp.nstr(h,6):>13} "
              f"{mp.nstr(lhs,6):>14} {mp.nstr(rhs,6):>14} {mp.nstr(ratio,5):>10}  "
              f"{'YES' if ok else 'NO'}")

print()
print("=" * 88)
print("Crossover: smallest t (at h = t^{2/3}) where the sketch's inequality starts to hold")
print("=" * 88)
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))

    def holds(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return zero_density_rhs(alpha, t + h) < UJ(alpha, ahat, B1, B2, B3, B4, h, t)

    lo, hi = 12.5, 100000.0
    if not holds(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from about t = 10^{hi:.1f} upward")

print()
print("=" * 88)
print("At fixed t = 3e12, how large must h be for the inequality to hold?")
print("=" * 88)
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
    t = H0

    def holds_h(hexp):
        h = mp.mpf(10) ** hexp
        return zero_density_rhs(alpha, t + h) < UJ(alpha, ahat, B1, B2, B3, B4, h, t)

    lo, hi = 8.0, 100000.0
    if not holds_h(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at h = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_h(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  needs h >~ 10^{hi:.2f}   "
          f"(t^(2/3) = 10^{float(mp.log(t ** (mp.mpf(2)/3), 10)):.2f})")


# ==============================================================================================
# PART 2 --- the Littlewood mechanism (`\ref{thm:main-littlewood}`, Theorem 3), same case,
# against U_L
# ==============================================================================================
# alpha, r, A1..A6 --- tex Table \ref{tab:littlewoodshort} (Table 7). The table's largest alpha
# is 1/6; the Littlewood mechanism itself needs only alpha < 1/2
# (`MainTheoremTight.mainLittlewoodTight`), and for that wider range the paper tabulates nothing.
TABLE_L = [
    (mp.mpf(1) / 6, '0.5000000', '0.2469513', '0', '2.005451', '0.2201801', '1.948504',
     '10.269668'),
    (mp.mpf(1) / 7, '0.5000000', '0.2304879', '0', '1.871754', '0.2055015', '1.818604',
     '9.585023'),
    (mp.mpf(1) / 8, '0.5000000', '0.2195122', '0', '1.782623', '0.1957157', '1.732003',
     '9.128594'),
    (mp.mpf(1) / 9, '0.2857143', '0.2045455', '0.9115238', '0.3971245', '0.1059233',
     '2.454546', '12.040681'),
    (mp.mpf(1) / 10, '0.2857143', '0.1923077', '0.8569882', '0.3733649', '0.09958597',
     '2.307693', '11.320299'),
    (mp.mpf(1) / 16, '0.2857143', '0.1600000', '0.7130142', '0.3106396', '0.08285553',
     '1.920001', '9.418489'),
    (mp.mpf(1) / 64, '0.09677420', '0.09937889', '1.961264', '0.8544655', '0.01794826',
     '1.788820', '14.441878'),
    (mp.mpf(1) / 1024, '0.009784736', '0.05554351', '18.069007', '7.872142', '0.001042787',
     '1.666306', '73.905261'),
]


def UL(A1, A2, A3, A4, A5, A6, h, t):
    r"""`U_L(alpha,r,h,t)`, `Theorem \ref{thm:main-littlewood}` (Theorem 3)
    (`MainTheorem.ULittlewood`, defined in `ZerosInShortIntervals/MainTerms.lean`)."""
    L = mp.log(t)
    return ((2 * A1 * h + 2 * A4) / mp.pi * L
            + (2 * A2 * h + 2 * A5) * mp.log(L)
            + 2 * A3 * h + A6)


print()
print("=" * 88)
print("PART 2 --- Littlewood (Theorem 2): zero-density bound  <  U_L ?   at h = t^{2/3}")
print("=" * 88)
print(f"{'alpha':>11} {'t':>9} {'density bd':>14} {'U_L':>14} {'ratio':>11}  ok?")
for (alpha, r, A1, A2, A3, A4, A5, A6) in TABLE_L:
    A1, A2, A3, A4, A5, A6 = map(mp.mpf, (A1, A2, A3, A4, A5, A6))
    for texp in [12.5, 13, 16, 20, 30, 100]:
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        if t - h < H0:
            continue
        lhs = zero_density_rhs(alpha, t + h)
        rhs = UL(A1, A2, A3, A4, A5, A6, h, t)
        print(f"{mp.nstr(alpha,5):>11} {'1e%g' % texp:>9} {mp.nstr(lhs,6):>14} "
              f"{mp.nstr(rhs,6):>14} {mp.nstr(lhs/rhs,5):>11}  {'YES' if lhs < rhs else 'NO'}")

print()
print("Littlewood crossover: smallest t (at h = t^{2/3}) where the sketch holds")
for (alpha, r, A1, A2, A3, A4, A5, A6) in TABLE_L:
    A1, A2, A3, A4, A5, A6 = map(mp.mpf, (A1, A2, A3, A4, A5, A6))

    def holds_L(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return zero_density_rhs(alpha, t + h) < UL(A1, A2, A3, A4, A5, A6, h, t)

    lo, hi = 12.5, 100000.0
    if not holds_L(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_L(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from about t = 10^{hi:.1f} upward")


# ==============================================================================================
# PART 3 --- the two corollaries (`\ref{cor:main-jensen}`/`\ref{cor:main-littlewood}`,
# Corollaries 4 and 5), via C_2
# ==============================================================================================
# The corollaries bound  Nrect/(N(t+h)-N(t-h))  by C_2(alpha,r,h_0,t_0). In the h > t^{2/3} case
# the numerator is bounded by the zero-density estimate and the denominator below by L(h,t).
# Since C_2 is DECREASING in both h_0 and t_0 and the corollary has h > h_0, t > t_0, it is
# sufficient to check the ratio against C_2 evaluated at the SAME (h,t): then
#     ratio(h,t) < C_2(h,t) <= C_2(h_0,t_0).
# NOTE ON CONSTANTS. `Lbound` and `C2denom` below implement the earlier `-h^2/(4t^2)` allowance
# (and its `-pi/(4 t^{2/3} log t)` image in the C_2 denominator), NOT the sharp
# `-(1-log2)h^2/(pi t^2)` that the tex and `MainCorollary.Lbound` now carry. The two differ by a
# factor 2.5595 on a term that is utterly negligible here (see `verify_Lht_sharp_constant.py`),
# so the conclusions below are unaffected; the code is left as it was run.
def Lbound(h, t):
    r"""`L(h,t)`, the lower bound on `N(t+h) - N(t-h)` displayed just above
    `Corollary \ref{cor:main-jensen}` (Corollary 4), in its pre-sharpening `-h^2/(4t^2)` form."""
    return ((mp.log(t / (2 * mp.pi)) / mp.pi - h ** 2 / (4 * t ** 2)) * h
            - mp.mpf('0.194') * mp.log(t) - mp.mpf('9.908'))


def rectDenom(r, alpha):
    return 2 * r * mp.sqrt(1 - (alpha / r) ** 2) - 2 * alpha * mp.atan(mp.sqrt((r / alpha) ** 2 - 1))


def C2denom(h, t):
    L = mp.log(t)
    return (1 - mp.log(2 * mp.pi) / L - mp.pi / (4 * t ** (mp.mpf(2) / 3) * L)
            - mp.mpf('0.194') * mp.pi / h - mp.mpf('9.908') * mp.pi / (h * L))


def C2J(alpha, r, ahat, B1, B2, B3, B4, h, t):
    L = mp.log(t)
    D = rectDenom(r, alpha)
    num = ((2 + 2 * ahat / h) * (B1 + mp.pi * B2 * mp.log(L) / L + mp.pi * B3 / L)
           + mp.pi * B4 / (h * L)
           + mp.mpf('3.35') * mp.pi / (D * h * t ** (mp.mpf(1) / 3) * L))
    return num / C2denom(h, t)


def C2L(alpha, r, A1, A2, A3, A4, A5, A6, h, t):
    L = mp.log(t)
    num = (2 * A1 + 2 * A4 / h
           + mp.pi * (2 * A2 + 2 * A5 / h) * mp.log(L) / L
           + 2 * mp.pi * A3 / L + mp.pi * A6 / (h * L)
           + mp.pi / ((r - alpha) * h * t * L) * (mp.mpf('0.335') + mp.mpf('0.51') / L))
    return num / C2denom(h, t)


print()
print("=" * 88)
print("PART 3a --- Corollary 3 (Jensen): density bound / L(h,t)  <  C_2^J ?   at h = t^{2/3}")
print("=" * 88)
print(f"{'alpha':>11} {'t':>9} {'ratio':>13} {'C_2^J':>12} {'margin':>11}  ok?")
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    r = mp.mpf(r)
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
    for texp in [12.5, 13, 16, 20, 30]:
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        if t - h < H0:
            continue
        ratio = zero_density_rhs(alpha, t + h) / Lbound(h, t)
        c2 = C2J(alpha, r, ahat, B1, B2, B3, B4, h, t)
        print(f"{mp.nstr(alpha,5):>11} {'1e%g' % texp:>9} {mp.nstr(ratio,6):>13} "
              f"{mp.nstr(c2,6):>12} {mp.nstr(ratio/c2,5):>11}  {'YES' if ratio < c2 else 'NO'}")

print()
print("Corollary 3 crossover: smallest t (at h = t^{2/3}) where ratio < C_2^J(h,t)")
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    r = mp.mpf(r)
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))

    def holds_c(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return (zero_density_rhs(alpha, t + h) / Lbound(h, t)
                < C2J(alpha, r, ahat, B1, B2, B3, B4, h, t))

    lo, hi = 12.5, 100000.0
    if not holds_c(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_c(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from about t = 10^{hi:.1f} upward")

print()
print("=" * 88)
print("PART 3b --- Corollary 4 (Littlewood): density bound / L(h,t)  <  C_2^L ?")
print("=" * 88)
print(f"{'alpha':>11} {'t':>9} {'ratio':>13} {'C_2^L':>12} {'margin':>11}  ok?")
for (alpha, r, A1, A2, A3, A4, A5, A6) in TABLE_L:
    r = mp.mpf(r)
    A1, A2, A3, A4, A5, A6 = map(mp.mpf, (A1, A2, A3, A4, A5, A6))
    for texp in [12.5, 13, 16, 20, 30]:
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        if t - h < H0:
            continue
        ratio = zero_density_rhs(alpha, t + h) / Lbound(h, t)
        c2 = C2L(alpha, r, A1, A2, A3, A4, A5, A6, h, t)
        print(f"{mp.nstr(alpha,5):>11} {'1e%g' % texp:>9} {mp.nstr(ratio,6):>13} "
              f"{mp.nstr(c2,6):>12} {mp.nstr(ratio/c2,5):>11}  {'YES' if ratio < c2 else 'NO'}")

print()
print("Corollary 4 crossover: smallest t (at h = t^{2/3}) where ratio < C_2^L(h,t)")
for (alpha, r, A1, A2, A3, A4, A5, A6) in TABLE_L:
    r = mp.mpf(r)
    A1, A2, A3, A4, A5, A6 = map(mp.mpf, (A1, A2, A3, A4, A5, A6))

    def holds_cl(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return (zero_density_rhs(alpha, t + h) / Lbound(h, t)
                < C2L(alpha, r, A1, A2, A3, A4, A5, A6, h, t))

    lo, hi = 12.5, 100000.0
    if not holds_cl(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_cl(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from about t = 10^{hi:.1f} upward")


# ==============================================================================================
# PART 3c --- does a SMALL h_0 rescue the corollaries?
# ==============================================================================================
# Above, the ratio was compared against `C_2` at the same `(h,t)`, which makes the corollary
# comparison ALGEBRAICALLY EQUIVALENT to the theorem's (since C_2 = U/L after normalising, the
# `L` cancels) --- hence the identical crossovers. But the corollary only needs
# `ratio < C_2(h_0,t_0)`, and `C_2` blows up as `h_0` approaches `h0Threshold(t_0)`, where its
# denominator vanishes. So a small `h_0` can rescue the case even where the theorem's own
# comparison fails.
def h0_threshold(t0):
    L = mp.log(t0)
    return ((97 * mp.pi / 500) * (1 + mp.mpf(4954) / (97 * L))
            / (1 - mp.pi / (4 * t0 ** (mp.mpf(2) / 3) * L) - mp.log(2 * mp.pi) / L))


print()
print("=" * 88)
print("PART 3c --- Corollary 3 at t_0 = 3e12: largest h_0 for which case (i) still closes")
print("=" * 88)
t0 = H0
h_case = t0 ** (mp.mpf(2) / 3)
print(f"  h0Threshold(t_0) = {mp.nstr(h0_threshold(t0), 8)},   "
      f"t_0^(2/3) = {mp.nstr(h_case, 8)}")
print(f"{'alpha':>11} {'ratio at h=t^2/3':>18} {'max h_0 that works':>20}")
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    r = mp.mpf(r)
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
    ratio = zero_density_rhs(alpha, t0 + h_case) / Lbound(h_case, t0)
    lo, hi = h0_threshold(t0) * mp.mpf('1.000001'), h_case
    if C2J(alpha, r, ahat, B1, B2, B3, B4, hi, t0) > ratio:
        print(f"{mp.nstr(alpha,5):>11} {mp.nstr(ratio,6):>18} "
              f"{'all h_0 up to t^(2/3)':>20}")
        continue
    if C2J(alpha, r, ahat, B1, B2, B3, B4, lo, t0) <= ratio:
        print(f"{mp.nstr(alpha,5):>11} {mp.nstr(ratio,6):>18} {'none':>20}")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if C2J(alpha, r, ahat, B1, B2, B3, B4, mid, t0) > ratio:
            lo = mid
        else:
            hi = mid
    print(f"{mp.nstr(alpha,5):>11} {mp.nstr(ratio,6):>18} {mp.nstr(lo,8):>20}")


# ==============================================================================================
# PART 4 --- the TIGHTER zero-density input
# ==============================================================================================
# Corollary 4.50 is doubly lossy for this application:
#
#  (L1) Its `U = 12.45321` and `V = 3.869` are the MAXIMA over the whole range sigma in [0.75,1]
#       (U at the top end, V at the bottom). Table A.1 of the thesis gives U and V per sigma, and
#       in our range they are roughly half of 12.45.
#
#  (L2) It quotes equation (4.160), which is (4.159) weakened by log(1+y) <= y. The sharper
#       (4.159) is
#           N(sigma,T1,T2) <= (T2-T1)(log T2) log(1 + Y/(T2-T1)) + V (log T2)^2,
#           Y = U T2^{(8/3)alpha} (log T2)^{2+2 alpha},
#       whose leading term is LINEAR in the interval length T2-T1 = 2h --- the same shape as
#       U_J's own `2h` factor --- rather than h-independent. For a short interval that is a real
#       gain whenever Y/(2h) is not small.
#
# Table A.1 (T0 = H0 = 3e12, sub-convexity version, k=2, eta ~ 0.20341): sigma, U, V.
TABLE_A1 = [
    (0.750, '3.436480', '3.868940'), (0.760, '3.637080', '3.790960'),
    (0.770, '3.848100', '3.712980'), (0.780, '4.069980', '3.635000'),
    (0.790, '4.303130', '3.557020'), (0.800, '4.547990', '3.479040'),
    (0.810, '4.804980', '3.401060'), (0.820, '5.074550', '3.323090'),
    (0.830, '5.357110', '3.245110'), (0.840, '5.653090', '3.167130'),
    (0.850, '5.962890', '3.089150'), (0.860, '6.286900', '3.011170'),
    (0.870, '6.625510', '2.933190'), (0.880, '6.979070', '2.855210'),
    (0.890, '7.347900', '2.777240'), (0.900, '7.732300', '2.699260'),
    (0.910, '8.132490', '2.621280'), (0.920, '8.548700', '2.543300'),
    (0.930, '8.981040', '2.465320'), (0.940, '9.429580', '2.387340'),
    (0.950, '9.894320', '2.309360'), (0.960, '10.375150', '2.231390'),
    (0.970, '10.871850', '2.153410'), (0.980, '11.384100', '2.075430'),
    (0.990, '11.911420', '1.997450'),
]


def UV_at(alpha):
    """`U`, `V` of Theorem 4.46 at `sigma = 1 - alpha`, interpolated in Table A.1.

    Above `sigma = 0.99` the table stops; Corollary 4.50's own `U = 12.45321` is the
    `sigma -> 1` value, so we clamp there rather than extrapolate.
    """
    s = float(1 - alpha)
    if s >= 0.99:
        f = min((s - 0.99) / 0.01, 1.0)
        u0, v0 = mp.mpf('11.911420'), mp.mpf('1.997450')
        return u0 + f * (C_U - u0), v0 + f * (mp.mpf('1.9195') - v0)
    for i in range(len(TABLE_A1) - 1):
        s0, u0, v0 = TABLE_A1[i]
        s1, u1, v1 = TABLE_A1[i + 1]
        if s0 <= s <= s1:
            w = (s - s0) / (s1 - s0)
            return (mp.mpf(u0) + w * (mp.mpf(u1) - mp.mpf(u0)),
                    mp.mpf(v0) + w * (mp.mpf(v1) - mp.mpf(v0)))
    return C_U, C_V           # sigma < 0.75: outside the table, fall back to Cor 4.50


def zero_density_tight(alpha, length, T2):
    """Theorem 4.46 equation (4.159), with per-sigma `U`,`V` --- both levers applied.

    `length` is `T2 - T1`, passed in directly: computing it as `(t+h)-(t-h)` loses all
    precision once `t` dwarfs `h`, which it does at the top of the scan range.
    """
    U, V = UV_at(alpha)
    L = mp.log(T2)
    Y = U * T2 ** (mp.mpf(8) / 3 * alpha) * L ** (2 + 2 * alpha)
    return length * L * mp.log(1 + Y / length) + V * L ** 2


print()
print("=" * 88)
print("PART 4 --- the TIGHTER input: per-sigma U,V (Table A.1) AND eq (4.159) not (4.160)")
print("=" * 88)
print(f"{'alpha':>10} {'U(Cor4.50)':>11} {'U(per-sigma)':>13} {'old ratio':>11} "
      f"{'new ratio':>11} {'gain':>7}  ok?")
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
    t = H0
    h = t ** (mp.mpf(2) / 3)
    U, V = UV_at(alpha)
    old = zero_density_rhs(alpha, t + h)
    new = zero_density_tight(alpha, 2 * h, t + h)
    uj = UJ(alpha, ahat, B1, B2, B3, B4, h, t)
    print(f"{mp.nstr(alpha,5):>10} {mp.nstr(C_U,6):>11} {mp.nstr(U,6):>13} "
          f"{mp.nstr(old/uj,5):>11} {mp.nstr(new/uj,5):>11} "
          f"{mp.nstr(old/new,4):>7}  {'YES' if new < uj else 'NO'}")

print()
print("Jensen crossover with the TIGHT input (h = t^{2/3}):")
for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
    B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))

    def holds_tight(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return (zero_density_tight(alpha, 2 * h, t + h)
                < UJ(alpha, ahat, B1, B2, B3, B4, h, t))

    lo, hi = 12.5, 100000.0
    if not holds_tight(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_tight(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from t = 10^{hi:.1f}   "
          f"(was 10^18.8 / 10^15.2 / 10^12.5 with Cor 4.50)")

print()
print("Littlewood crossover with the TIGHT input (h = t^{2/3}):")
for (alpha, r, A1, A2, A3, A4, A5, A6) in TABLE_L:
    A1, A2, A3, A4, A5, A6 = map(mp.mpf, (A1, A2, A3, A4, A5, A6))

    def holds_tight_L(texp):
        t = mp.mpf(10) ** texp
        h = t ** (mp.mpf(2) / 3)
        return (zero_density_tight(alpha, 2 * h, t + h)
                < UL(A1, A2, A3, A4, A5, A6, h, t))

    lo, hi = 12.5, 100000.0
    if not holds_tight_L(hi):
        print(f"  alpha={mp.nstr(alpha,6):>10}:  fails even at t = 10^100000")
        continue
    for _ in range(200):
        mid = (lo + hi) / 2
        if holds_tight_L(mid):
            hi = mid
        else:
            lo = mid
    print(f"  alpha={mp.nstr(alpha,6):>10}:  holds from t = 10^{hi:.1f}")
