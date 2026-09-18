r"""
Rigorous(-ish) reproduction of Table \ref{tab:littlewoodshort} (Table 7) in
`ZerosInShortIntervals.tex` (the alpha/r/A_{1..6,alpha,r}/r-alpha table attached to
Theorem \ref{thm:littlewoodshort} (Theorem 32)).

**No Lean target.** The table is printed in the paper; no hypothesis-class field depends on it,
and nothing here is a certificate. What it pins down are the *values* of
`Littlewood.LittlewoodShort`'s `A1 .. A6` at the paper's optimal `r`, hence of `c1,c2,c3`
(`Jensen.JensenScaleConstants`) and `c4` (`Jensen.JensenBounds`) that feed them.

This is a cleaned-up, self-contained extraction of the working computation in the exploratory
notebook `Zero Density Short Intervals.ipynb` (cells 0, 1, 2, 8, 10 — the "Table A_R" block),
which has since been removed from `Code/` and is recoverable from git history only,
restructured to name each function after the matching Lean definition in
`ZerosInShortIntervals/Jensen/JensenScaleConstants.lean` / `ZerosInShortIntervals/Littlewood/*.lean`, so
the correspondence between this script, the tex, and the Lean formalization is explicit. It does
NOT copy the notebook's printed numbers -- every value here is recomputed from the definitions in
Theorem \ref{thm:littlewoodshort} (Theorem 32) and Proposition \ref{prop:jensen-easy}
(Proposition 8).

**Which `k = 0` chord triple.** As in the paper's tables, `vCoeff`/`vCoeffP`/`vCoeffPP` below carry
Remark \ref{rem:altcoefficients} (Remark 7)'s triple `(27/164, 0, log 66.7)`, i.e. Lean's
`Jensen/JensenScaleConstantsAlt.lean` (`vCoeffAlt`, `vCoeffPAlt`, `vCoeffPPAlt`), NOT
`JensenScaleConstants`'s main-text `(1/6, 1, log 0.611)`. See the "KNOWN DISCREPANCY" note at the
top of `JensenScaleConstants.lean` and `Code/verify_v0_triple_vs_tables.py`.

Rigor level: the `zeta`/`zeta'` evaluations and the `c1,c2,c3,c4` sums/integrals are done in
`ComplexBallField(200)` (certified ball arithmetic -- same as the original notebook), so those
carry a certified error radius. The purely rational/algebraic pieces (`sigma`, `mCoeff`, `bCoeff`,
`find_k`, the optimal-`r` search of `find_optimal_Ar`) are exact rationals; `eta` (root of
`1+eta+log(eta)=0`) is Newton-refined in `RealField(1000)` -- not literally ball-certified, but
carried at 1000 bits, i.e. error far below the 7-significant-figure table -- and its residual is
printed and asserted below `2^-180`. The final rounding (`roundup_to`) drops to Sage's default
`RR = RealField(53)`, which is still far more than the 7 printed digits need. This matches the
table's own stated "mostly rigorous" provenance -- it is not full
certified-interval-image-of-a-box verification the way `Code/verify_hcompact_boxes.sage` is (that
would need certified handling of the infinite tail sums and of `find_k`'s bisection, which is a
larger undertaking left as a follow-up).

Run with:  sage Code/verify_littlewoodshort_table.sage
"""

N = 1000
R = ComplexBallField(200)

# ---------------------------------------------------------------------------------------------
# `sigma`, `vCoeff`, `vCoeffP`, `vCoeffPP`, `mCoeff`, `bCoeff` -- `JensenScaleConstants.lean`,
# with the `k = 0` values of `JensenScaleConstantsAlt.lean`.
# ---------------------------------------------------------------------------------------------


def sigma(k):
    if k == infinity:
        return 1
    elif k == -infinity:
        return 0
    elif k == 0:
        return QQ(1) / 2
    elif k > 0:
        return 1 - (k + 3) / (2 ** (k + 3) - 2)
    else:
        return (-k + 3) / (2 ** (-k + 3) - 2)


def find_k(sig, Nn=N):
    r"""`k` with `sigma(k) <= sig < sigma(k+1)` (bisection on the monotone `sigma`)."""
    upper, lower = Nn, -Nn
    vupper, vlower = sigma(upper), sigma(lower)
    if sig > vupper:
        return infinity
    if sig < vlower:
        return -infinity
    while upper - lower > 1:
        mid = (upper + lower) // 2
        vmid = sigma(mid)
        if sig < vmid:
            upper, vupper = mid, vmid
        elif sig > vmid:
            lower, vlower = mid, vmid
        else:
            return mid
    return lower


def vCoeff(k):
    # `k = 0` uses Remark \ref{rem:altcoefficients} (Remark 7), which follows the `v_k` definitions
    # after \eqref{eq:sigmak}: `v_0 = 27/164`, not `1/6` -- Lean's
    # `JensenScaleConstantsAlt.vCoeffAlt`, and what `JensenScaleConstants.lean`'s "KNOWN
    # DISCREPANCY" note records the paper's *tables* as using.
    if k == infinity:
        return 0
    elif k == -infinity:
        return QQ(1) / 2
    elif k == 0:
        return QQ(27) / 164
    elif k > 0:
        return 1 / (2 ** (k + 3) - 2)
    else:
        return QQ(1) / 2 - sigma(k) + 1 / (2 ** (-k + 3) - 2)


def vCoeffP(k):
    return 0 if k == 0 else 1


def vCoeffPP(k):
    if k == 0:
        return log(R(667) / 10)  # log(66.7) = `vCoeffPPAlt 0`, the variant matching v_0 = 27/164
    elif k > 0:
        return log(R(1546) / 1000)
    else:
        return log(R(1546) / 1000) + (sigma(k) - QQ(1) / 2) * log(R(pi))


# CONVENTION (do not change without changing every evaluation site below):
# matches `eq:mk`/`eq:mkp`/`eq:mkpp` in the tex and `JensenScaleConstants.lean`'s
# `mCoeff`/`bCoeff` EXACTLY -- note the NEGATIVE denominator `sigma(k) - sigma(k+1)`.
# The chord is `mCoeff(k)*sigma + bCoeff(k)`, evaluated at `sigma` itself (NOT at `1-sigma`);
# it interpolates `(sigma_k, v_k) -> (sigma_{k+1}, v_{k+1})`.
def mCoeff(k):
    if k in (infinity, -infinity):
        return 0
    return (vCoeff(k) - vCoeff(k + 1)) / (sigma(k) - sigma(k + 1))


def mCoeffP(k):
    if k in (infinity, -infinity):
        return 0
    return (vCoeffP(k) - vCoeffP(k + 1)) / (sigma(k) - sigma(k + 1))


def mCoeffPP(k):
    if k in (infinity, -infinity):
        return 0
    return (vCoeffPP(k) - vCoeffPP(k + 1)) / (sigma(k) - sigma(k + 1))


def bCoeff(k):
    return vCoeff(k) - mCoeff(k) * sigma(k)


def bCoeffP(k):
    return vCoeffP(k) - mCoeffP(k) * sigma(k)


def bCoeffPP(k):
    return vCoeffPP(k) - mCoeffPP(k) * sigma(k)


# ---------------------------------------------------------------------------------------------
# `c1(r), c2(r), c3(r)` -- the rapidly-convergent sum of `JensenScaleConstants.lean` -- and
# `c4(r)` -- the `zeta'/zeta` integral of `JensenBounds.lean`'s `c4` -- both via ball
# arithmetic, following `coef`/`c4r` in the notebook.
# ---------------------------------------------------------------------------------------------


def coef(r):
    r"""Returns `[r, c1(r), c2(r), c3(r)]`, summing the boundary term plus the tail from
    `k = find_k(1-r)+1` up to `k = N` (the terms decay geometrically in `k`, so truncating at
    `N = 1000` is far beyond the ~7-significant-figure precision the table prints)."""
    k = find_k(1 - r) + 1
    if k < -N:
        k = -N
    C1 = C2 = C3 = R(0)
    thetak = R(pi / 2)
    thetakp1 = (arcsin(R((1 - sigma(k)) / r))).real()
    while k < N:
        # `(m_k + b_k)*dtheta + m_k*r*dcos` -- exactly the sum printed in the tex after
        # \eqref{eq:thetak}, in the tex/Lean chord convention fixed above.
        cosdiff = cos(thetak) - cos(thetakp1)
        thetadiff = thetak - thetakp1
        C1 += r * cosdiff * mCoeff(k - 1) + thetadiff * (mCoeff(k - 1) + bCoeff(k - 1))
        C2 += r * cosdiff * mCoeffP(k - 1) + thetadiff * (mCoeffP(k - 1) + bCoeffP(k - 1))
        C3 += r * cosdiff * mCoeffPP(k - 1) + thetadiff * (mCoeffPP(k - 1) + bCoeffPP(k - 1))
        thetak = thetakp1
        k += 1
        thetakp1 = arcsin(R((1 - sigma(k)) / r)).real()
    return [r, R(C1), R(C2), R(C3)]


def integrable_logderzetaarcsin(rr, u, analytic):
    if analytic and u.real() > 1 and u.imag().contains_zero():
        return CBF(NaN)
    return -rr * zetaderiv(1, 1 + rr * u) / zeta(1 + rr * u) * arcsin(u)


def c4r(r):
    r"""`c4(r) = (1/2) log zeta(1+r) - (r/pi) int_0^1 (zeta'/zeta)(1+ru) arcsin(u) du`, matching
    `JensenBounds.lean`'s `c4` (Proposition \ref{prop:integraloutside}, Proposition 15),
    integrated by certified ball quadrature (the `1/2^100` inner cutoff
    absorbs the integrable singularity of `zeta'/zeta` at `u=0`, bounded there by `arcsin(u) < 2u`,
    same as the notebook's `c4r`)."""
    val1 = R(log(zeta(1 + r)) / 2)
    val2 = (
        R.integral(lambda z, a: integrable_logderzetaarcsin(r, z, a), 1 / 2 ** 100, 1)
        + 1 / 2 ** 99
    ).real() / R(pi)
    return val1 + val2


# ---------------------------------------------------------------------------------------------
# `eta` -- Definitions.lean's `eta`, the root of `1 + eta + log(eta) = 0` -- Newton-refined.
# ---------------------------------------------------------------------------------------------

RR1000 = RealField(1000)
_x = RR1000(0.3)
_f(t) = 1 + t + log(t)
_df = _f.derivative()
for _ in range(20):
    _x = _x - _f(_x) / _df(_x)
eta = R(_x)
eta_residual = (1 + eta + log(eta)).real()
print("eta =", RR(_x), " residual of 1+eta+log(eta) at eta:", eta_residual)
assert eta_residual.abs().upper() < RR(2) ** (-180), \
    "eta failed to converge to the required precision"


# ---------------------------------------------------------------------------------------------
# `Phi(z) = int_z^oo log(zeta(x)) dx`, appearing in `A6` -- ported as-is
# from the notebook (cells 0/1): a certified tail via `R.integral` out to `x=1000`, plus a
# certified-from-10^6-onward prime-power-sum bound for the piece beyond `x=1000`.
# ---------------------------------------------------------------------------------------------


def prime_power_heap_iterator(limit):
    from heapq import heappush, heappop, heapify

    pq = []
    max_k = ceil(log(limit) / log(2))
    for k in range(1, max_k + 1):
        it = (p ** k for p in primes(ceil(limit ** (1 / k))) if p ** k <= limit)
        try:
            first_val = next(it)
            pq.append((first_val, it, k))
        except StopIteration:
            break
    heapify(pq)
    while pq:
        val, it, k = heappop(pq)
        yield val
        try:
            nxt = next(it)
            heappush(pq, (nxt, it, k))
        except StopIteration:
            pass


def Phi_approx(X, z):
    sumval = 0
    r = z - 1
    for n in prime_power_heap_iterator(X):
        pp = is_prime_power(n, get_data=True)
        if pp[1] > 0:
            sumval += R(1 / pp[1] / log(n) / n ** (1 + r))
    if X >= 10 ** 10:
        epsilon = 64 * 10 ** (-7)
    elif X >= 10 ** 9:
        epsilon = 198 * 10 ** (-7)
    elif X >= 10 ** 8:
        epsilon = 738 * 10 ** (-7)
    elif X >= 10 ** 7:
        epsilon = 2231 * 10 ** (-7)
    elif X >= 10 ** 6:
        epsilon = 6932 * 10 ** (-7)
    else:
        X = 10 ** 4
        epsilon = 8759 * 10 ** (-6)
    if r == 0:
        tail = R((1 / log(X) + 1 / log(X) ** 2) * (1 + epsilon))
    else:
        tail = R(
            (r ** 2 * gamma_inc(-2, R(r) * R(log(X))) + r * gamma_inc(-1, R(r) * R(log(X))))
            * (r + 1)
            * (1 + epsilon)
        )
    return (sumval + tail).real()


def integrable_logzeta(z, analytic):
    if analytic and z.real() < 0 and z.imag().contains_zero():
        return CBF(NaN)
    return log(zeta(z))


def Phi(z):
    if z == 1:
        val1 = R.integral(integrable_logzeta, z + 1 / 2 ** 100, 1000)
        val2 = R(-(1 / 2 ** 100) * (log(1 / 2 ** 100) - 1))
    else:
        val1 = R.integral(integrable_logzeta, z, 1000)
        val2 = 0
    val3 = Phi_approx(10 ** 6, 1000)
    return val1 + val2 + val3


# ---------------------------------------------------------------------------------------------
# `A1 .. A6`, `r/alpha` -- `Littlewood/LittlewoodShort.lean`'s `A1 .. A6` (Theorem
# \ref{thm:littlewoodshort}, Theorem 32), at the optimal `r` --
# following `find_optimal_Ar` in the notebook: `r = 1 - sigma(k)` for the least `k` past which the
# ratio `v_{k+1}/(1-sigma(k+1)-alpha)` stops decreasing.
# ---------------------------------------------------------------------------------------------


def find_optimal_Ar(alpha):
    k = -1000
    while (
        alpha < (1 - sigma(k + 1))
        and (vCoeff(k + 1) / (1 - sigma(k + 1) - alpha) < vCoeff(k) / (1 - sigma(k) - alpha))
    ):
        k = k + 1
    r = 1 - sigma(k)
    # `A1..A3` have denominator `2(r-alpha)` -- the extra `/2` is written out on each line below --
    # while `A4..A6` have denominator `(r-alpha)` alone. That asymmetry is in the tex and in Lean.
    # `A1 = (m_k(1-r)+b_k)/(2(r-alpha))` collapses to `vCoeff(k)/(2(r-alpha))` here because
    # `r = 1-sigma(k)` is a chord endpoint: `1-r = sigma(k)`, so `m_k*sigma(k)+b_k = v_k` exactly
    # and the slope never has to be evaluated. Likewise for `A2`, `A3`.
    weight = r - alpha
    A1 = vCoeff(k) / weight / 2
    A2 = vCoeffP(k) / pi / weight / 2
    A3 = vCoeffPP(k) / pi / weight / 2
    cr = coef(r)
    c4 = c4r(r)
    A4 = r * cr[1] / weight
    A5 = r * (cr[2] / pi + 1) / weight
    A6 = (
        r * (cr[3] / pi + c4 + log(R(29388) / 1000) + ((1 + eta) * log(zeta(1 + eta * r))) / pi)
        + Phi(1 + eta * r) / pi
    ) / weight
    return [alpha, r, A1, A2, A3, A4, A5, A6, r / alpha]


def roundup_to(v, ndig):
    r"""Round `v` UP to `ndig` significant decimal digits -- matching the tex's stated "rounded
    up" convention (and the notebook's `roundup_s`), returned as a Sage `RR = RealField(53)` value
    for easy printing/comparison."""
    v = RR(v)
    if v == 0:
        return RR(0)
    d = ceil(log(v) / log(10))
    if d < 1:
        scaled = ceil(v * 10 ** (1 + 7 - d)) / 10 ** (1 + 7 - d)
    else:
        scaled = ceil(v * 10 ** 7) / 10 ** 7
    return RR(scaled)


# ---------------------------------------------------------------------------------------------
# The table itself: Table \ref{tab:littlewoodshort} (Table 7) of
# `ZerosInShortIntervals.tex`, columns
# `alpha, r, A1, A2, A3, A4, A5, A6, r/alpha` -- 7 significant figures, rounded up.
# ---------------------------------------------------------------------------------------------

TABLE_ALPHA = [
    QQ(1) / 6, QQ(1) / 7, QQ(1) / 8, QQ(1) / 9, QQ(1) / 10, QQ(1) / 11, QQ(1) / 12, QQ(1) / 13,
    QQ(1) / 14, QQ(1) / 15, QQ(1) / 16, QQ(1) / 32, QQ(1) / 64, QQ(1) / 128, QQ(1) / 256,
    QQ(1) / 512, QQ(1) / 1024, QQ(1) / 2048,
]

# tex row: [r, A1, A2, A3, A4, A5, A6, r/alpha]  (alpha itself is exact, printed as "1/n")
TEX_TABLE = {
    QQ(1) / 6: [0.5000000, 0.2469513, 0, 2.005451, 0.2201801, 1.948504, 10.269668, 3.000000],
    QQ(1) / 7: [0.5000000, 0.2304879, 0, 1.871754, 0.2055015, 1.818604, 9.585023, 3.500000],
    QQ(1) / 8: [0.5000000, 0.2195122, 0, 1.782623, 0.1957157, 1.732003, 9.128594, 4.000000],
    QQ(1) / 9: [0.2857143, 0.2045455, 0.9115238, 0.3971245, 0.1059233, 2.454546, 12.040681,
                2.571429],
    QQ(1) / 10: [0.2857143, 0.1923077, 0.8569882, 0.3733649, 0.09958597, 2.307693, 11.320299,
                 2.857143],
    QQ(1) / 11: [0.2857143, 0.1833334, 0.8169954, 0.3559412, 0.09493862, 2.200000, 10.792018,
                 3.142858],
    QQ(1) / 12: [0.2857143, 0.1764706, 0.7864127, 0.3426172, 0.09138477, 2.117648, 10.388039,
                 3.428572],
    QQ(1) / 13: [0.2857143, 0.1710527, 0.7622685, 0.3320983, 0.08857910, 2.052632, 10.069108,
                 3.714286],
    QQ(1) / 14: [0.2857143, 0.1666667, 0.7427231, 0.3235829, 0.08630784, 2.000000, 9.810926,
                 4.000000],
    QQ(1) / 15: [0.2857143, 0.1630435, 0.7265770, 0.3165485, 0.08443158, 1.956522, 9.597645,
                 4.285715],
    QQ(1) / 16: [0.2857143, 0.1600000, 0.7130142, 0.3106396, 0.08285553, 1.920001, 9.418489,
                 4.571429],
    QQ(1) / 32: [0.1666667, 0.1230770, 1.175299, 0.5120433, 0.03779972, 1.846154, 11.325849,
                 5.333334],
    QQ(1) / 64: [0.09677420, 0.09937889, 1.961264, 0.8544655, 0.01794826, 1.788820, 14.441878,
                 6.193549],
    QQ(1) / 128: [0.05555556, 0.08311689, 3.333573, 1.452341, 0.008701209, 1.745455, 19.713406,
                  7.111112],
    QQ(1) / 256: [0.03149607, 0.07134895, 5.768613, 2.513217, 0.004266277, 1.712375, 28.844815,
                  8.062993],
    QQ(1) / 512: [0.01764706, 0.06246950, 10.141176, 4.418216, 0.002105235, 1.686677, 44.972432,
                  9.035295],
    QQ(1) / 1024: [0.009784736, 0.05554351, 18.069007, 7.872142, 0.001042787, 1.666306, 73.905261,
                   10.019570],
    QQ(1) / 2048: [0.005376345, 0.04999512, 32.559922, 14.185413, 5.177350e-4, 1.649839,
                   126.451532, 11.010753],
}

COLS = ["r", "A1", "A2", "A3", "A4", "A5", "A6", "r/alpha"]

print("\n=== Reproducing Table tab:littlewoodshort ===\n")
worst_rel_gap = 0
for alpha in TABLE_ALPHA:
    computed = find_optimal_Ar(alpha)  # [alpha, r, A1, A2, A3, A4, A5, A6, r/alpha]
    printed = TEX_TABLE[alpha]
    print(f"alpha = 1/{QQ(1)/alpha} :")
    for name, comp, want in zip(COLS, computed[1:], printed):
        comp_r = RR(comp)
        rounded = roundup_to(comp_r, 7)
        gap = abs(RR(want) - rounded) / max(abs(RR(want)), 1e-30)
        worst_rel_gap = max(worst_rel_gap, gap)
        flag = "" if gap < 1e-5 else "   <-- MISMATCH"
        print(f"    {name:8s} computed={comp_r:.10g}  roundup7={rounded:.10g}"
              f"  tex={want:.10g}{flag}")
    print()

print(f"Worst relative gap between our rounded-up value and the tex's printed value:"
      f" {worst_rel_gap:.3e}")
print("(Expected to be tiny -- both this script and the tex value trace back to the same"
      " ball-arithmetic computation in the notebook; a large gap would flag either a genuine"
      " numeric error in the tex or a divergence in how this script ported the definitions.)")
