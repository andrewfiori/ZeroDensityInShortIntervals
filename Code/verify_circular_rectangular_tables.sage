r"""
Rigorous(-ish) reproduction of the five Jensen / rectangular-Jensen constant tables of
`ZerosInShortIntervals.tex`: Tables \ref{tab:crvalues} (Table 2), \ref{tab:CRvalues}
(Table 3), \ref{tab:crvalues2} (Table 4), \ref{tab:rectangularjensen} (Table 5) and
\ref{tab:crvalues3} (Table 6). Table \ref{tab:littlewoodshort} (Table 7) is covered separately by
`verify_littlewoodshort_table.sage`, whose `coef`/`c4r`/`sigma`/`mCoeff`/`bCoeff`/`Phi` machinery
this script reuses verbatim -- see that file's docstring for the shared provenance/rigor notes.

NUMBERING NOTE: the identifiers (`TABLE1_R`, `TEX_TABLE1`, ..., `worst5`) and the banners/printed
labels below number these five tables 1-5, in the order this script does them. The tex numbers
them 2-6. The `\ref` labels are the stable identifier; the ordinals are not.

**No Lean target.** These tables are printed in the paper; no hypothesis-class field depends on
them, and nothing here is a certificate. What they pin down are the *values* of the Lean constants
`c1,c2,c3` (`Jensen.JensenScaleConstants`), `c4` and `C1,C2,C3` (`Jensen.JensenBounds`), and `c5`,
`rectDenom`, `B1..B4` (`Jensen.RectangularBounds`).

Values are recomputed from the definitions in Proposition \ref{prop:jensen-easy} (Proposition 8;
`c1,c2,c3`), Proposition \ref{prop:integraloutside} (Proposition 15; `c4`), Proposition
\ref{prop:outside3} (Proposition 23; `c5`), Theorem \ref{thm:circularregions1} (Theorem 16;
`C1,C2,C3`) and Theorem \ref{thm:rectangularjensen} (Theorem 24; `B1,B2,B3,B4`). Not copied from
the notebook's printed numbers.

**Which `k = 0` chord triple.** As in the paper's tables, `vCoeff`/`vCoeffP`/`vCoeffPP` below carry
the Remark \ref{rem:altcoefficients} (Remark 7) triple `(v_0, v_0', v_0'') = (27/164, 0, log 66.7)`
-- in Lean, `Jensen/JensenScaleConstantsAlt.lean`'s `vCoeffAlt`, `vCoeffPAlt`, `vCoeffPPAlt`.
`JensenScaleConstants`'s own `vCoeff`/`vCoeffP`/`vCoeffPP` are the main-text triple
`(1/6, 1, log 0.611)`, so `JensenBounds.c1,c2,c3` evaluate to different numbers than the ones
reproduced here. That is deliberate and is recorded as the "KNOWN DISCREPANCY" note at the top of
`JensenScaleConstants.lean`; see also `Code/verify_v0_triple_vs_tables.py`.

**Rigor level, per quantity:**
  * `c1,c2,c3,c4` at a *given* `r`: `ComplexBallField(200)` certified ball arithmetic (as in
    `verify_littlewoodshort_table.sage`).
  * `c5` at a given `r`: same, via a new certified-ball quadrature of
    `(2r/pi) int_0^1 log(zeta(1+ru)) arcsin(u) du` (the `u=0` endpoint is handled the same way as
    `c4r`'s `zeta'/zeta` singularity there, via a `1/2^100` cutoff -- `log(zeta(1+ru))*arcsin(u) ->
    0` there since `arcsin(u) ~ u` beats the `log(1/u)` blowup of `log(zeta(1+ru))` as `u -> 0`).
  * The optimal `r` in Tables `CRvalues`/`rectangularjensen` (minimizing `C1(alpha,r)` /
    `B1(alpha,r)` over `r in (alpha, 1)`): a golden-section search whose bracket arithmetic is
    `RF = RealField(200)` but whose objective is `c1_fast`, a *fast* `RD = RealField(53)`
    (non-ball), 80-term-capped evaluation of `c1(r)` alone (for speed -- the search only needs
    the location of the minimum, not a certified value there), then one final certified
    `ComplexBallField(200)` evaluation of `c1,c2,c3,c4,c5` at the converged `r*`. This mirrors the
    notebook's own two-tier `coef1` (fast search) / `coef` (certified) split. The search itself is
    NOT a certified global-optimality proof (matching this project's "mostly rigorous" standard for
    tables, not the full certified-box standard of `verify_hcompact_boxes.sage`); `c1(r)` is smooth
    and unimodal in `r` on the ranges tested here (verified empirically by the search converging to
    the same point from multiple starting brackets), so this is a reasonable, not fully certified,
    optimum.
  * The assembly of `C1,C2,C3` and `B1..B4` from the `c_i`, together with `rectDenom` and
    `roundup_to`, runs in plain `RF = RealField(200)`, not in ball arithmetic. So the numbers this
    script prints and compares are 200-bit approximations, not enclosures.

Run with:  sage Code/verify_circular_rectangular_tables.sage
"""

N = 1000
R = ComplexBallField(200)
RF = RealField(200)


# ---------------------------------------------------------------------------------------------
# Shared machinery -- verbatim from `verify_littlewoodshort_table.sage`:
# `JensenScaleConstants.lean`'s `sigma`/`vCoeff`/`mCoeff`/`bCoeff` and `c1,c2,c3`, plus
# `JensenBounds.lean`'s `c4` -- but with the `k = 0` triple of `JensenScaleConstantsAlt.lean`
# (`vCoeffAlt`, `vCoeffPAlt`, `vCoeffPPAlt`), which is what the paper's tables use.
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


def vCoeffPP(k, field=R):
    if k == 0:
        return log(field(667) / 10)
    elif k > 0:
        return log(field(1546) / 1000)
    else:
        return log(field(1546) / 1000) + (sigma(k) - QQ(1) / 2) * log(field(pi))


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


def mCoeffPP(k, field=R):
    if k in (infinity, -infinity):
        return 0
    return (vCoeffPP(k, field) - vCoeffPP(k + 1, field)) / (sigma(k) - sigma(k + 1))


def bCoeff(k):
    return vCoeff(k) - mCoeff(k) * sigma(k)


def bCoeffP(k):
    return vCoeffP(k) - mCoeffP(k) * sigma(k)


def bCoeffPP(k, field=R):
    return vCoeffPP(k, field) - mCoeffPP(k, field) * sigma(k)


def coef(r, field=R, kcap=N):
    r"""`[c1(r), c2(r), c3(r)]`, certified when `field = R = ComplexBallField(200)` and
    `kcap = N = 1000`. `kcap` caps how many terms *past the starting `k`* are summed -- the sum is
    geometrically rapidly convergent (tex, after \eqref{eq:thetak}), so a small `kcap` (used only by
    `c1_fast` below, for the search) is a fast, non-certified approximation; the default `kcap = N`
    matches the original, fully-summed, certified computation.

    `r = 1` is a genuine edge case: `1 - r = 0` is below `sigma(k)` for *every* finite `k` (`sigma`
    only reaches `0` in the `k -> -infinity` limit), so `find_k(0) = -infinity` and the natural
    starting point for the sum is off the bottom of our `[-N, N]` discretization entirely -- the
    correct range to sum is then the *whole* `[-N, N]`, not `[-N, -N + kcap]` (which is what the
    general-case fallback below would give, since `k + kcap = -N + N = 0` when `k` gets clamped to
    `-N`)."""
    fk = find_k(1 - r)
    if fk == -infinity:
        k = -N
        kstop = N
    else:
        k = fk + 1
        if k < -N:
            k = -N
        kstop = min(N, k + kcap)
    C1 = C2 = C3 = field(0)
    thetak = field(pi / 2)
    thetakp1 = (arcsin(field((1 - sigma(k)) / r))).real()
    while k < kstop:
        # `(m_k + b_k)*dtheta + m_k*r*dcos` -- exactly the sum printed in the tex after
        # \eqref{eq:thetak}, in the tex/Lean chord convention fixed above.
        cosdiff = cos(thetak) - cos(thetakp1)
        thetadiff = thetak - thetakp1
        C1 += r * cosdiff * mCoeff(k - 1) + thetadiff * (mCoeff(k - 1) + bCoeff(k - 1))
        C2 += r * cosdiff * mCoeffP(k - 1) + thetadiff * (mCoeffP(k - 1) + bCoeffP(k - 1))
        C3 += (r * cosdiff * mCoeffPP(k - 1, field)
               + thetadiff * (mCoeffPP(k - 1, field) + bCoeffPP(k - 1, field)))
        thetak = thetakp1
        k += 1
        thetakp1 = arcsin(field((1 - sigma(k)) / r)).real()
    return [field(C1), field(C2), field(C3)]


RD = RealField(53)  # double precision, for the fast search only


def c1_fast(r):
    r"""`c1(r)` alone, in fast double-precision, 80-term-capped arithmetic -- for use inside the
    golden-section search only, where speed matters more than a certified error radius (the search
    only needs the *location* of the minimum; the final answer is re-evaluated certified, capped at
    the full `N = 1000`, once, after the search converges)."""
    return coef(RD(r), field=RD, kcap=80)[0]


def integrable_logderzetaarcsin(rr, u, analytic):
    if analytic and u.real() > 1 and u.imag().contains_zero():
        return CBF(NaN)
    return -rr * zetaderiv(1, 1 + rr * u) / zeta(1 + rr * u) * arcsin(u)


def c4r(r):
    val1 = R(log(zeta(1 + r)) / 2)
    val2 = (
        R.integral(lambda z, a: integrable_logderzetaarcsin(r, z, a), 1 / 2 ** 100, 1)
        + 1 / 2 ** 99
    ).real() / R(pi)
    return val1 + val2


# ---------------------------------------------------------------------------------------------
# `c5(r)` -- Proposition \ref{prop:outside3} (Proposition 23): `c5(r) = Phi(1+r)
# + (2r/pi) int_0^1 log(zeta(1+ru)) arcsin(u) du`.
# New (not in `verify_littlewoodshort_table.sage`), matching the notebook's `c5r`
# (`Phi(1+r) - 2*integral(-log(zeta(1+ru))... )`, same quantity, sign folded into the integrand
# there) and `RectangularBounds.lean`'s `c5`.
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


def integrable_logzeta_arcsin(r, u, analytic):
    if analytic and u.real() > 1 and u.imag().contains_zero():
        return CBF(NaN)
    return log(zeta(1 + r * u)) * arcsin(u)


def c5r(r):
    val1 = Phi(1 + r).real()
    val2 = (
        2
        * r
        * (R.integral(lambda z, a: integrable_logzeta_arcsin(r, z, a), 1 / 2 ** 100, 1)).real()
        / R(pi)
    )
    return val1 + val2


# ---------------------------------------------------------------------------------------------
# `C1,C2,C3` -- `Jensen/JensenBounds.lean`, Theorem \ref{thm:circularregions1} (Theorem 16);
# `B1,B2,B3,B4,rectDenom` -- `Jensen/RectangularBounds.lean`, Theorem
# \ref{thm:rectangularjensen} (Theorem 24).
# ---------------------------------------------------------------------------------------------


def C1_of(alpha, r, c1):
    return c1 / log(RF(r) / RF(alpha))


def C2_of(alpha, r, c2):
    lr = log(RF(r) / RF(alpha))
    return c2 / (lr * RF(pi)) + 1 / lr


def C3_of(alpha, r, c3, c4):
    lr = log(RF(r) / RF(alpha))
    return c3 / (RF(pi) * lr) + c4 / lr + log(RF(29388) / 1000) / lr


def rectDenom(r, alpha):
    r, alpha = RF(r), RF(alpha)
    return 2 * r * sqrt(1 - (alpha / r) ** 2) - 2 * alpha * arctan(sqrt((r / alpha) ** 2 - 1))


# `Phi(1) = int_1^oo log|zeta(x)| dx < 1.7975699586287395`, the bound stated in Proposition
# \ref{prop:outside2} (Proposition 22). In Lean this is the hypothesis field
# `NumericCertificates.integral_log_zeta_Ioi_one_lt`, certified by `Code/verify_Phi_one_bound.sage`
# -- not by this script, which only consumes the value.
PHI1 = RF(1.7975699586287395)


def B1_of(r, alpha, c1):
    return c1 / rectDenom(r, alpha)


def B2_of(r, alpha, c2):
    return c2 / (RF(pi) * rectDenom(r, alpha))


def B3_of(r, alpha, c3):
    return c3 / (RF(pi) * rectDenom(r, alpha))


def B4_of(r, alpha, c5):
    # `B_{4,alpha,r} = (2*Phi(1) + c_{5,r})/D_{r,alpha}`, Theorem \ref{thm:rectangularjensen}
    # (Theorem 24). NOT `Phi(1)/pi`: Proposition \ref{prop:outside2} (Proposition 22) states its
    # bound in `(1/(2pi))`-normalised form `(1/(2pi)) int log|zeta(1+it)|dt <= Phi(1)/pi`, i.e.
    # `int log|zeta(1+it)|dt <= 2*Phi(1)`, and it is the *un-normalised* integral that occurs bare
    # in the numerator of Proposition \ref{prop:jensenrectangle} (Proposition 19).
    # Matches `RectangularBounds.lean`'s `B4` exactly (see its docstring for the full argument).
    return (2 * PHI1 + c5) / rectDenom(r, alpha)


# ---------------------------------------------------------------------------------------------
# Golden-section search for the `r in (alpha, 1)` minimizing `c1_fast(r)/weight(r,alpha)`.
# ---------------------------------------------------------------------------------------------

GOLDEN = (sqrt(RF(5)) - 1) / 2  # 1/phi


def golden_section_min(f, lo, hi, iters=45):
    lo, hi = RF(lo), RF(hi)
    x1 = hi - GOLDEN * (hi - lo)
    x2 = lo + GOLDEN * (hi - lo)
    f1, f2 = f(x1), f(x2)
    for _ in range(iters):
        if f1 < f2:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - GOLDEN * (hi - lo)
            f1 = f(x1)
        else:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + GOLDEN * (hi - lo)
            f2 = f(x2)
    return (lo + hi) / 2


def optimal_r_Cvalues(alpha):
    weight = lambda r: log(RF(r) / RF(alpha))
    f = lambda r: c1_fast(r) / weight(r)
    return golden_section_min(f, RF(alpha) * RF(1.001), RF(0.999999))


def optimal_r_rectangular(alpha):
    f = lambda r: c1_fast(r) / rectDenom(r, alpha)
    return golden_section_min(f, RF(alpha) * RF(1.001), RF(0.999999))


def roundup_to(v, ndig):
    v = RF(v)
    if v == 0:
        return RF(0)
    d = ceil(log(v) / log(10))
    if d < 1:
        scaled = ceil(v * 10 ** (1 + 7 - d)) / 10 ** (1 + 7 - d)
    else:
        scaled = ceil(v * 10 ** 7) / 10 ** 7
    return RF(scaled)


def compare(name, computed, want, worst_ref):
    computed = RF(computed)
    rounded = roundup_to(computed, 7)
    gap = abs(RF(want) - rounded) / max(abs(RF(want)), RF(1e-30))
    worst_ref[0] = max(worst_ref[0], gap)
    flag = "" if gap < 1e-4 else "   <-- MISMATCH"
    print(f"    {name:8s} computed={computed:.10g}  roundup7={rounded:.10g}"
          f"  tex={want:.10g}{flag}")


# =================================================================================================
# tab:crvalues -- Table 2 of the tex -- [r, c1, c2, c3, c4, c5]
# =================================================================================================

TABLE1_R = [1, QQ(1)/2, QQ(1)/3, QQ(1)/4, QQ(1)/5, QQ(1)/6, QQ(1)/7, QQ(1)/8, QQ(1)/9, QQ(1)/10,
            QQ(1)/11, QQ(1)/12, QQ(1)/13, QQ(1)/14, QQ(1)/15, QQ(1)/16, QQ(1)/32, QQ(1)/64,
            QQ(1)/128, QQ(1)/256, QQ(1)/512, QQ(1)/1024, QQ(1)/2048]

TEX_TABLE1 = {
    1: [0.4260491, 1.320694, 1.233886, 0.5099522, 0.8331601],
    QQ(1)/2: [0.1467868, 0.9393432, 3.061478, 0.7795712, 1.126439],
    QQ(1)/3: [0.08122972, 1.491029, 0.9846382, 0.9546469, 1.271554],
    QQ(1)/4: [0.05402652, 1.570797, 0.6843504, 1.084244, 1.360125],
    QQ(1)/5: [0.03956564, 1.570797, 0.6843504, 1.187130, 1.420588],
    QQ(1)/6: [0.03071227, 1.570797, 0.6843504, 1.272441, 1.464849],
    QQ(1)/7: [0.02516876, 1.570797, 0.6843504, 1.345309, 1.498839],
    QQ(1)/8: [0.02110448, 1.570797, 0.6843504, 1.408902, 1.525868],
    QQ(1)/9: [0.01803813, 1.570797, 0.6843504, 1.465317, 1.547944],
    QQ(1)/10: [0.01569390, 1.570797, 0.6843504, 1.516009, 1.566357],
    QQ(1)/11: [0.01393216, 1.570797, 0.6843504, 1.562034, 1.581977],
    QQ(1)/12: [0.01249892, 1.570797, 0.6843504, 1.604178, 1.595417],
    QQ(1)/13: [0.01129907, 1.570797, 0.6843504, 1.643045, 1.607118],
    QQ(1)/14: [0.01028337, 1.570797, 0.6843504, 1.679108, 1.617407],
    QQ(1)/15: [0.009416022, 1.570797, 0.6843504, 1.712745, 1.626535],
    QQ(1)/16: [0.008670644, 1.570797, 0.6843504, 1.744261, 1.634694],
    QQ(1)/32: [0.003703026, 1.570797, 0.6843504, 2.085161, 1.702482],
    QQ(1)/64: [0.001626574, 1.570797, 0.6843504, 2.428881, 1.743167],
    QQ(1)/128: [7.256286e-4, 1.570797, 0.6843504, 2.774023, 1.766930],
    QQ(1)/256: [3.277390e-4, 1.570797, 0.6843504, 3.119880, 1.780529],
    QQ(1)/512: [1.495313e-4, 1.570797, 0.6843504, 3.466095, 1.788188],
    QQ(1)/1024: [6.880172e-5, 1.570797, 0.6843504, 3.812489, 1.792449],
    QQ(1)/2048: [3.188568e-5, 1.570797, 0.6843504, 4.158973, 1.794794],
}

print("\n=== Table 1 (tab:crvalues): c1,c2,c3,c4,c5 ===\n")
worst1 = [0]
for r in TABLE1_R:
    c1, c2, c3 = coef(r)
    c4 = c4r(r)
    c5 = c5r(r)
    print(f"r = {r} :")
    for nm, comp, want in zip(["c1", "c2", "c3", "c4", "c5"], [c1, c2, c3, c4, c5],
                               TEX_TABLE1[r]):
        compare(nm, comp, want, worst1)
    print()
print(f"Table 1 worst relative gap: {worst1[0]:.3e}")


# =================================================================================================
# tab:CRvalues -- Table 3 of the tex -- [alpha, r, C1, C2, C3, r/alpha]
# (optimal r minimizing C1(alpha,r) = c1(r)/log(r/alpha))
# =================================================================================================

TABLE24_ALPHA = [QQ(1)/3, QQ(1)/4, QQ(1)/5, QQ(1)/6, QQ(1)/7, QQ(1)/8, QQ(1)/9, QQ(1)/10,
                 QQ(1)/11, QQ(1)/12, QQ(1)/13, QQ(1)/14, QQ(1)/15, QQ(1)/16, QQ(1)/32, QQ(1)/64,
                 QQ(1)/128, QQ(1)/256, QQ(1)/512, QQ(1)/1024, QQ(1)/2048]

TEX_TABLE2 = {
    QQ(1)/3: [0.6490511, 0.3264740, 1.965836, 7.446222, 1.947154],
    QQ(1)/4: [0.5022756, 0.2117515, 1.858502, 7.369401, 2.009103],
    QQ(1)/5: [0.3940064, 0.1538013, 2.093277, 7.054466, 1.970032],
    QQ(1)/6: [0.3242696, 0.1170874, 2.225533, 6.965111, 1.945618],
    QQ(1)/7: [0.2897366, 0.09333569, 2.120321, 6.530988, 2.028157],
    QQ(1)/8: [0.2606756, 0.07783097, 2.040920, 6.345352, 2.085405],
    QQ(1)/9: [0.2276378, 0.06616898, 2.091395, 6.588795, 2.048740],
    QQ(1)/10: [0.2030836, 0.05706802, 2.117307, 6.744948, 2.030836],
    QQ(1)/11: [0.1851792, 0.04988792, 2.108330, 6.776810, 2.036971],
    QQ(1)/12: [0.1729682, 0.04420265, 2.054067, 6.646159, 2.075618],
    QQ(1)/13: [0.1668192, 0.03972128, 1.937723, 6.291698, 2.168650],
    QQ(1)/14: [0.1550286, 0.03611895, 1.935706, 6.329759, 2.170400],
    QQ(1)/15: [0.1433184, 0.03302353, 1.959855, 6.457329, 2.149775],
    QQ(1)/16: [0.1333413, 0.03033976, 1.979559, 6.567526, 2.133460],
    QQ(1)/32: [0.06834560, 0.01242107, 1.916792, 6.771429, 2.187059],
    QQ(1)/64: [0.03512879, 0.005269206, 1.851512, 6.944143, 2.248243],
    QQ(1)/128: [0.01817011, 0.002295522, 1.777141, 7.052067, 2.325774],
    QQ(1)/256: [0.009413507, 0.001021403, 1.705384, 7.139335, 2.409858],
    QQ(1)/512: [0.004727625, 4.607252e-4, 1.696848, 7.492183, 2.420544],
    QQ(1)/1024: [0.002374581, 2.099090e-4, 1.688169, 7.840865, 2.431570],
    QQ(1)/2048: [0.001192880, 9.643198e-5, 1.679292, 8.184763, 2.443018],
}

print("\n=== Table 2 (tab:CRvalues): r*, C1, C2, C3, r*/alpha ===\n")
worst2 = [0]
table2_r = {}
for alpha in TABLE24_ALPHA:
    rstar = optimal_r_Cvalues(alpha)
    table2_r[alpha] = rstar
    c1, c2, c3 = coef(QQ(RealField(120)(rstar)))
    c4 = c4r(QQ(RealField(120)(rstar)))
    C1v = C1_of(alpha, rstar, RF(c1))
    C2v = C2_of(alpha, rstar, RF(c2))
    C3v = C3_of(alpha, rstar, RF(c3), RF(c4))
    print(f"alpha = 1/{QQ(1)/alpha} :")
    for nm, comp, want in zip(["r", "C1", "C2", "C3", "r/alpha"],
                               [rstar, C1v, C2v, C3v, rstar / alpha], TEX_TABLE2[alpha]):
        compare(nm, comp, want, worst2)
    print()
print(f"Table 2 worst relative gap: {worst2[0]:.3e}")


# =================================================================================================
# tab:crvalues2 -- Table 4 of the tex -- [r, c1, c2, c3, c4] at tab:CRvalues's r values
# =================================================================================================

print("\n=== Table 3 (tab:crvalues2): c1,c2,c3,c4 at Table 2's r ===\n")
worst3 = [0]
TEX_TABLE3 = list(zip(
    [0.6490511, 0.5022756, 0.3940064, 0.3242696, 0.2897366, 0.2606756, 0.2276378, 0.2030836,
     0.1851792, 0.1729682, 0.1668192, 0.1550286, 0.1433183, 0.1333413, 0.06834559, 0.03512879,
     0.01817011, 0.009413510, 0.004727620, 0.002374580, 0.001192880],
    [[0.2175520, 0.9738017, 2.853749, 0.6729643],
     [0.1477365, 0.9319669, 3.089081, 0.7776710],
     [0.1042849, 1.317413, 1.638224, 0.8812288],
     [0.07793089, 1.511949, 0.9058834, 0.9668954],
     [0.06600019, 1.568710, 0.6922055, 1.017316],
     [0.05720288, 1.570797, 0.6843504, 1.065177],
     [0.04745803, 1.570797, 0.6843504, 1.127225],
     [0.04042969, 1.570797, 0.6843504, 1.180019],
     [0.03549344, 1.570797, 0.6843504, 1.223032],
     [0.03227938, 1.570797, 0.6843504, 1.254995],
     [0.03074843, 1.570797, 0.6843504, 1.272011],
     [0.02798899, 1.570797, 0.6843504, 1.306581],
     [0.02527499, 1.570797, 0.6843504, 1.343779],
     [0.02298980, 1.570797, 0.6843504, 1.378087],
     [0.009720201, 1.570797, 0.6843504, 1.700612],
     [0.004268841, 1.570797, 0.6843504, 2.027367],
     [0.001937541, 1.570797, 0.6843504, 2.353894],
     [8.983930e-4, 1.570797, 0.6843504, 2.681106],
     [4.072770e-4, 1.570797, 0.6843504, 3.024609],
     [1.865119e-4, 1.570797, 0.6843504, 3.368478],
     [8.613635e-5, 1.570797, 0.6843504, 3.712486]],
))
for alpha, (r_tex, row) in zip(TABLE24_ALPHA, TEX_TABLE3):
    rstar = table2_r[alpha]
    c1, c2, c3 = coef(QQ(RealField(120)(rstar)))
    c4 = c4r(QQ(RealField(120)(rstar)))
    print(f"alpha = 1/{QQ(1)/alpha}  (tex r={r_tex}, ours r={RF(rstar):.7g}) :")
    for nm, comp, want in zip(["c1", "c2", "c3", "c4"], [c1, c2, c3, c4], row):
        compare(nm, comp, want, worst3)
    print()
print(f"Table 3 worst relative gap: {worst3[0]:.3e}")


# =================================================================================================
# tab:rectangularjensen -- Table 5 of the tex -- [alpha, r, B1, B2, B3, B4, hat_alpha_r, r/alpha]
# (optimal r minimizing B1(alpha,r) = c1(r)/rectDenom(r,alpha))
# =================================================================================================

TABLE4_ALPHA = [QQ(1)/7, QQ(1)/8, QQ(1)/9, QQ(1)/10, QQ(1)/11, QQ(1)/12, QQ(1)/13, QQ(1)/14,
                QQ(1)/15, QQ(1)/16, QQ(1)/32, QQ(1)/64, QQ(1)/128, QQ(1)/256, QQ(1)/512,
                QQ(1)/1024, QQ(1)/2048]

TEX_TABLE4 = {
    QQ(1)/7: [0.5647100, 0.2457053, 0.3900919, 1.450119, 6.518765, 0.5463417, 3.952970],
    QQ(1)/8: [0.5185446, 0.2294753, 0.4239720, 1.514935, 6.977388, 0.5032529, 4.148357],
    QQ(1)/9: [0.5030821, 0.2172051, 0.4340594, 1.446353, 6.922300, 0.4906586, 4.527739],
    QQ(1)/10: [0.4821212, 0.2079206, 0.4778655, 1.331336, 7.058488, 0.4716364, 4.821212],
    QQ(1)/11: [0.3820330, 0.1991813, 0.8624038, 0.9519504, 9.637060, 0.3710589, 4.202362],
    QQ(1)/12: [0.3390065, 0.1907470, 1.076388, 0.7557944, 11.128858, 0.3286046, 4.068078],
    QQ(1)/13: [0.3165097, 0.1832274, 1.186113, 0.6552031, 11.906782, 0.3070199, 4.114626],
    QQ(1)/14: [0.3035626, 0.1767236, 1.236003, 0.6023857, 12.253958, 0.2950393, 4.249876],
    QQ(1)/15: [0.2957571, 0.1711536, 1.252382, 0.5730817, 12.349950, 0.2881455, 4.436356],
    QQ(1)/16: [0.2909922, 0.1663861, 1.250289, 0.5551999, 12.302409, 0.2842010, 4.655874],
    QQ(1)/32: [0.1701799, 0.1273443, 2.016620, 0.8785824, 20.388630, 0.1672861, 5.445757],
    QQ(1)/64: [0.09924636, 0.1023306, 3.292282, 1.434352, 33.994587, 0.09800867, 6.351767],
    QQ(1)/128: [0.05717608, 0.08524602, 5.501905, 2.397021, 57.665580, 0.05663982, 7.318538],
    QQ(1)/256: [0.03250649, 0.07294429, 9.396536, 4.093798, 99.501950, 0.03227093, 8.321661],
    QQ(1)/512: [0.01825477, 0.06370419, 16.349070, 7.122815, 174.312148, 0.01814999, 9.346441],
    QQ(1)/1024: [0.01014060, 0.05652525, 28.889451, 12.586295, 309.383987, 0.01009347, 10.383974],
    QQ(1)/2048: [0.005580532, 0.05079351, 51.707199, 22.527325, 555.296995, 0.005559130,
                 11.428930],
}

# `B_{4,alpha,r}` per Theorem \ref{thm:rectangularjensen} (Theorem 24):
# `(2*Phi(1) + c_{5,r})/D_{r,alpha}`.
print("\n=== Table 4 (tab:rectangularjensen): r*, B1, B2, B3, B4, hat_alpha_r, r*/alpha ===\n")
worst4 = [0]
table4_r = {}
for alpha in TABLE4_ALPHA:
    rstar = optimal_r_rectangular(alpha)
    table4_r[alpha] = rstar
    c1, c2, c3 = coef(QQ(RealField(120)(rstar)))
    c5 = c5r(QQ(RealField(120)(rstar)))
    B1v = B1_of(rstar, alpha, RF(c1))
    B2v = B2_of(rstar, alpha, RF(c2))
    B3v = B3_of(rstar, alpha, RF(c3))
    B4v = B4_of(rstar, alpha, RF(c5))
    hat_alpha_r = sqrt(RF(rstar) ** 2 - RF(alpha) ** 2)
    print(f"alpha = 1/{QQ(1)/alpha} :")
    for nm, comp, want in zip(["r", "B1", "B2", "B3", "B4", "hat_alpha_r", "r/alpha"],
                               [rstar, B1v, B2v, B3v, B4v, hat_alpha_r, rstar / alpha],
                               TEX_TABLE4[alpha]):
        compare(nm, comp, want, worst4)
    print()
print(f"Table 4 worst relative gap: {worst4[0]:.3e}")


# =================================================================================================
# tab:crvalues3 -- Table 6 of the tex -- [r, c1, c2, c3, c5] at tab:rectangularjensen's r values
# =================================================================================================

print("\n=== Table 5 (tab:crvalues3): c1,c2,c3,c5 at Table 4's r ===\n")
worst5 = [0]
TEX_TABLE5 = list(zip(
    [0.5647100, 0.5185446, 0.5030821, 0.4821212, 0.3820329, 0.3390065, 0.3165097, 0.3035626,
     0.2957571, 0.2909922, 0.1701799, 0.09924635, 0.05717607, 0.03250649, 0.01825477, 0.01014060,
     0.005580530],
    [[0.1761601, 0.8786375, 3.266227, 1.078532],
     [0.1548203, 0.8986260, 3.210968, 1.112301],
     [0.1480773, 0.9296458, 3.097724, 1.124066],
     [0.1394940, 1.007195, 2.806049, 1.140402],
     [0.09963112, 1.355212, 1.495928, 1.225349],
     [0.08331889, 1.477082, 1.037145, 1.265982],
     [0.07515015, 1.528325, 0.8442389, 1.288392],
     [0.07062081, 1.551699, 0.7562453, 1.301685],
     [0.06797647, 1.562641, 0.7150543, 1.309847],
     [0.06640649, 1.567667, 0.6961340, 1.314886],
     [0.03157371, 1.570797, 0.6843504, 1.460012],
     [0.01554098, 1.570797, 0.6843504, 1.567632],
     [0.007746955, 1.570797, 0.6843504, 1.645371],
     [0.003881447, 1.570797, 0.6843504, 1.699469],
     [0.001948252, 1.570797, 0.6843504, 1.735811],
     [9.783026e-4, 1.570797, 0.6843504, 1.759479],
     [4.911646e-4, 1.570797, 0.6843504, 1.774490]],
))
for alpha, (r_tex, row) in zip(TABLE4_ALPHA, TEX_TABLE5):
    rstar = table4_r[alpha]
    c1, c2, c3 = coef(QQ(RealField(120)(rstar)))
    c5 = c5r(QQ(RealField(120)(rstar)))
    print(f"alpha = 1/{QQ(1)/alpha}  (tex r={r_tex}, ours r={RF(rstar):.7g}) :")
    for nm, comp, want in zip(["c1", "c2", "c3", "c5"], [c1, c2, c3, c5], row):
        compare(nm, comp, want, worst5)
    print()
print(f"Table 5 worst relative gap: {worst5[0]:.3e}")

print("\n=== Overall worst relative gap across Tables 1-5: "
      f"{max(worst1[0], worst2[0], worst3[0], worst4[0], worst5[0]):.3e} ===")
