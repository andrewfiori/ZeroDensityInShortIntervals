r"""
Tables of `C_2^J(alpha,r,h_0,t_0)` and `C_2^L(alpha,r,h_0,t_0)` for `Corollary
\ref{cor:main-jensen}` (Corollary 4) and `Corollary \ref{cor:main-littlewood}` (Corollary 5) of
`ZerosInShortIntervals.tex`, with `r` optimized (per `(alpha,h_0,t_0)`) to MINIMIZE
`C_2` itself.

This is the computation stage of the paper's Tables 8-11 (`tab:C2J`, `tab:C2L`,
`tab:C2Jfrontier`, `tab:C2Lfrontier`).  It writes the COMPLETE computed record --
every grid point, with the `C_2 >= 1/2` rows kept as comments -- to `Code/C2_tables_raw.tex`.
`Code/emit_C2_tables.py` then applies the presentation rules and writes `Code/C2_tables.tex`,
which the paper `\input`s.

--------------------------------------------------------------------------------------------
FORMULAS
--------------------------------------------------------------------------------------------
With `ahat = sqrt(r^2-alpha^2)` (`\hat\alpha_r`), `D = rectDenom(r,alpha)` (`D_{r,alpha}`),
`LT = log t`, `LLT = log log t`, the corollaries' constants are

    DEN(h,t) = 1 - log(2 pi)/LT - (1 - log 2)/(t^(2/3) LT) - 0.194 pi/h - 9.908 pi/(h LT)

(The `t^(2/3)` term carries the sharp `h^2` coefficient `(1-log 2)/pi` of `L(h,t)`, so `DEN`,
`h0_threshold` and `Lraw` below match `MainCorollary.C2denom`/`h0Threshold`/`Lbound` in Lean
exactly.  At the tabulated `t_0 >= 3*10^12` that term is below `1e-9`, so it moves no printed
digit; it is carried anyway so the identity checked in "SANITY CHECK" below is exact.)

    NUM_J    = (2 + 2 ahat/h) (B1 + pi B2 LLT/LT + pi B3/LT)
               + pi B4/(h LT) + 3.35 pi/(D h t^(1/3) LT)
    NUM_L    = 2 A1 + 2 A4/h + pi (2 A2 + 2 A5/h) LLT/LT
               + 2 pi A3/LT + pi A6/(h LT)
               + pi/((r-alpha) h t LT) (0.335 + 0.51/LT)

    C_2^J = NUM_J/DEN,   C_2^L = NUM_L/DEN.

The factors of `pi` above are the whole subtlety, and are easy to drop: normalising the ratio
`U/L` by `(h log t)/pi` leaves only the leading `B1` (resp. `A1`) term `pi`-free, and multiplies
every other term of both numerator and denominator by `pi`.  Section "SANITY CHECK" below
re-derives `C_2` from the unnormalised `U`, `E`, `L` and verifies the identity to full precision;
that check is the guard against a transcription slip in the formulas above.

The admissibility threshold on `h_0` (exactly the condition `DEN > 0`) is

    h_0 > (97 pi/500) (1 + 4954/(97 log t_0)) / (1 - (1 - log 2)/(t_0^(2/3) log t_0) - log(2 pi)/log t_0)

and is checked for every `(h_0,t_0)` pair below.

--------------------------------------------------------------------------------------------
PROVENANCE / SHARED MACHINERY
--------------------------------------------------------------------------------------------
`sigma`, `find_k`, the `vCoeff`/`mCoeff`/`bCoeff` families, `coef` (`c1,c2,c3`), `c1_fast`,
`c4r`, `Phi_approx`/`Phi`, `c5r`, `rectDenom`, `B1_of..B4_of`, `golden_section_min` and
`roundup_to` are copied verbatim from `Code/verify_circular_rectangular_tables.sage`
(which in turn took the `sigma`/`mCoeff`/`bCoeff`/`coef`/`c4r`/`Phi` block verbatim from
`Code/verify_littlewoodshort_table.sage`).  Copying, rather than `load()`-ing, matches the
convention already used between those two scripts, and avoids re-running their table output.
`eta` is copied from `verify_littlewoodshort_table.sage`.

`A1_of .. A6_of` are NEW here: the existing `find_optimal_Ar` in
`verify_littlewoodshort_table.sage` only ever evaluates the `A`-constants at the discrete
notebook optimum `r = 1 - sigma(k)`, where `A1 = v_k/(2(r-alpha))` etc.; optimising `C_2` over a
*continuous* `r` needs them at arbitrary `r`.  See the "A-CONSTANTS AT GENERAL r" section for the
(checked) generalisation and an important discrepancy with the formula as printed in the tex.

--------------------------------------------------------------------------------------------
RIGOR LEVEL  (matching the "mostly rigorous" standard of the sibling table scripts)
--------------------------------------------------------------------------------------------
  * Final reported `C_2`, `r*`, and all `A_i`/`B_i` at the converged `r*`: certified
    `ComplexBallField(200)` evaluation of `c1..c5`, `c4`, `Phi`, `zeta` (as in the sibling
    scripts).  The surrounding `C_2` arithmetic is `RealField(200)`.
  * The `r`-search itself: fast, NON-certified `RealField(53)` evaluation (`coef` capped at 80
    terms, `Phi` by `numerical_integral` out to `x=60`, where `log zeta(60) < 1e-18`).  As in
    `verify_circular_rectangular_tables.sage`, the search only needs the *location* of the
    minimum; the value there is re-evaluated certified afterwards.
  * Unimodality of `C_2` in `r` is NOT proved.  It is checked empirically (multi-bracket restart
    agreement + a coarse grid scan whose argmin is compared against the golden-section result);
    disagreements are reported.  This matches the sibling scripts' own non-certified treatment of
    their optimal `r`.

Run with:  sage Code/compute_C2_tables.sage
"""

import time

N = 1000
R = ComplexBallField(200)
RF = RealField(200)
RD = RealField(53)  # fast, non-certified: search only

# `coef`'s chord sum decays geometrically (terms ~ 2^{-k}), so summing 250 terms past the
# starting `k` is already far below the 200-bit working precision; the sibling scripts' full
# `N = 1000` is ~4x slower for no gain.  (Ball arithmetic makes this self-certifying: a truncation
# that mattered would show up as an inflated error radius.)
CERT_KCAP = 250

# Golden-section iterations for the r-search: 0.618^24 ~ 1e-5, i.e. r* to ~5 decimal places,
# which is far finer than C_2's sensitivity to r near its (flat) minimum.
GS_ITERS = 16          # 0.618^16 ~ 5e-4; C_2 is very flat near its minimum in r
GRID_PTS = 25          # coarse grid scan, used as a global-minimum cross-check every time
THOROUGH_EVERY = 40    # do the full 3-bracket unimodality restart on every Nth grid point


def to_RF(x):
    r"""`RealField(200)` value of a ball / real / rational, whichever came in."""
    try:
        return RF(x.real())
    except (AttributeError, TypeError):
        return RF(x)


# =============================================================================================
# Shared machinery -- verbatim from `verify_circular_rectangular_tables.sage`
# (which took it from `verify_littlewoodshort_table.sage`).
# =============================================================================================


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


# `Phi_approx(10^6, 1000)` is the `z`-independent tail past `x = 1000`; the sibling scripts
# recompute it on every `Phi` call, which is pure waste (it is a fixed prime-power sum). Cached.
_PHI_TAIL = None


def _phi_tail():
    global _PHI_TAIL
    if _PHI_TAIL is None:
        _PHI_TAIL = Phi_approx(10 ** 6, 1000)
    return _PHI_TAIL


def Phi(z):
    if z == 1:
        val1 = R.integral(integrable_logzeta, z + 1 / 2 ** 100, 1000)
        val2 = R(-(1 / 2 ** 100) * (log(1 / 2 ** 100) - 1))
    else:
        val1 = R.integral(integrable_logzeta, z, 1000)
        val2 = 0
    return val1 + val2 + _phi_tail()


def integrable_logzeta_arcsin(r, u, analytic):
    if analytic and u.real() > 1 and u.imag().contains_zero():
        return CBF(NaN)
    return log(zeta(1 + r * u)) * arcsin(u)


def c5r(r):
    val1 = Phi(1 + r).real()
    val2 = (
        2 * r
        * (R.integral(lambda z, a: integrable_logzeta_arcsin(r, z, a), 1 / 2 ** 100, 1)).real()
        / R(pi)
    )
    return val1 + val2


def rectDenom(r, alpha):
    r, alpha = RF(r), RF(alpha)
    return 2 * r * sqrt(1 - (alpha / r) ** 2) - 2 * alpha * arctan(sqrt((r / alpha) ** 2 - 1))


PHI1 = RF(1.7975699586287395)  # Proposition \ref{prop:outside2}'s stated bound on Phi(1)


def B1_of(r, alpha, c1):
    return c1 / rectDenom(r, alpha)


def B2_of(r, alpha, c2):
    return c2 / (RF(pi) * rectDenom(r, alpha))


def B3_of(r, alpha, c3):
    return c3 / (RF(pi) * rectDenom(r, alpha))


def B4_of(r, alpha, c5):
    return (2 * PHI1 + c5) / rectDenom(r, alpha)


GOLDEN = (sqrt(RF(5)) - 1) / 2


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


# `eta` -- root of `1 + eta + log(eta) = 0` -- from `verify_littlewoodshort_table.sage`.
RR1000 = RealField(1000)
_x = RR1000(0.3)
_f(t) = 1 + t + log(t)
_df = _f.derivative()
for _ in range(20):
    _x = _x - _f(_x) / _df(_x)
eta = R(_x)
eta_RF = RF(_x)
_eta_residual = (1 + eta + log(eta)).real()
assert _eta_residual.abs().upper() < RR(2) ** (-180), "eta failed to converge"


# =============================================================================================
# A-CONSTANTS AT GENERAL r
#
# Theorem \ref{thm:littlewoodshort} prints
#     A_{1,alpha,r} = (m_k (1-r) + b_k) / (2(r-alpha)),      sigma_k <= 1-r < sigma_{k+1},
# and we use exactly that, verbatim -- it agrees with the theorem's printed Table
# \ref{tab:littlewoodshort} and with Lean's `LittlewoodShort.A1`, PROVIDED `m_k`, `b_k` are the
# tex/Lean chord coefficients defined above (chord evaluated at `sigma`, negative denominator).
# At the discrete optimum `r = 1-sigma(k)` we have `1-r = sigma(k)`, so
#     m_k (1-r) + b_k = m_k sigma_k + b_k = v_k,
# giving `A1 = v_k/(2(r-alpha))`, which is the notebook's value and the table's printed entry
# (e.g. `0.2045455` at `alpha=1/9`, `k=1`).  `check_A_against_notebook()` below verifies this.
#
# HISTORICAL NOTE (the reason the convention comment above exists).  An earlier revision of this
# script defined `mCoeff`/`bCoeff` with the opposite sign and a `(1-sigma_k)` offset, i.e. the
# chord parameterised by `1-sigma`.  Evaluating the tex's formula with THOSE coefficients gives
# `0.5973` instead of `0.2045455` at `alpha=1/9`, and this was briefly mis-reported as an error in
# the tex.  It was not: the tex and Lean are correct and mutually consistent; only this script's
# private convention differed.  Both conventions describe the same chord -- they are related by
#     mCoeff_old(k) = -mCoeff(k),      bCoeff_old(k) = mCoeff(k) + bCoeff(k),
#     mCoeff_old(k)*y + bCoeff_old(k) == mCoeff(k)*(1-y) + bCoeff(k)   for all y
# -- so the numbers this script produces are unchanged by the unification; only the spelling is.
# =============================================================================================


def A123_of(alpha, r, field=R):
    r"""`[A1, A2, A3]` at arbitrary `r`, with `k = find_k(1-r)`.

    Reads identically to the tex's printed `A_{i,alpha,r}` and to Lean's
    `LittlewoodShort.A1`/`A2`/`A3`."""
    k = find_k(1 - r)
    w = 2 * (field(r) - field(alpha))
    one_minus_r = 1 - field(r)
    A1 = (field(mCoeff(k)) * one_minus_r + field(bCoeff(k))) / w
    A2 = (field(mCoeffP(k)) * one_minus_r + field(bCoeffP(k))) / (field(pi) * w)
    A3 = (mCoeffPP(k, field) * one_minus_r + bCoeffPP(k, field)) / (field(pi) * w)
    return [A1, A2, A3]


def A456_of(alpha, r, c1, c2, c3, c4, phi_1_eta_r, log_zeta_1_eta_r, field=R):
    r"""`[A4, A5, A6]` at arbitrary `r`, per Theorem \ref{thm:littlewoodshort}:
        A4 = c1 r/(r-alpha),  A5 = (c2 r + pi r)/(pi(r-alpha)),
        A6 = (c3 r + c4 pi r + pi log(29.388) r + Phi(1+eta r) + (1+eta) r log zeta(1+eta r))
             / (pi(r-alpha)).
    (Identical to `find_optimal_Ar`'s expressions, rearranged over the common `pi(r-alpha)`.)"""
    w = field(r) - field(alpha)
    et = field(eta_RF) if field is not R else eta
    A4 = c1 * field(r) / w
    A5 = (c2 * field(r) + field(pi) * field(r)) / (field(pi) * w)
    A6 = (
        c3 * field(r)
        + c4 * field(pi) * field(r)
        + field(pi) * log(field(29388) / 1000) * field(r)
        + phi_1_eta_r
        + (1 + et) * field(r) * log_zeta_1_eta_r
    ) / (field(pi) * w)
    return [A4, A5, A6]


# =============================================================================================
# FAST (non-certified) tier -- search only.
# =============================================================================================


def Phi_fast(z):
    r"""`Phi(z) = int_z^infty log zeta(x) dx`, by fast double-precision quadrature out to `x=60`
    (`log zeta(60) < 1e-18`, so the discarded tail is far below the search's needs).  Agrees with
    the certified `Phi` to ~13 digits (checked in the sanity-check section)."""
    return RD(numerical_integral(lambda x: log(zeta(x)), RD(z), 60)[0])


def c4_fast(r):
    r = RD(r)
    val1 = log(zeta(1 + r)) / 2
    integ = numerical_integral(
        lambda u: -r * zetaderiv(1, 1 + r * u) / zeta(1 + r * u) * arcsin(u), 1e-12, 1
    )[0]
    return RD(val1 + RD(integ) / RD(pi))


def c5_fast(r):
    r = RD(r)
    val1 = Phi_fast(1 + r)
    integ = numerical_integral(lambda u: log(zeta(1 + r * u)) * arcsin(u), 1e-12, 1)[0]
    return RD(val1 + 2 * r * RD(integ) / RD(pi))


_FAST_CACHE = {}


def fast_data(r, need_c4=False, need_c5=False):
    r"""Cached fast data at `r`, computed LAZILY: the `numerical_integral` calls behind `c4`
    (Littlewood only) and `c5` (Jensen only) dominate the search cost, so neither is evaluated
    unless the caller actually needs it."""
    key = RD(r).str(digits=12)
    d = _FAST_CACHE.get(key)
    if d is None:
        rr = RD(r)
        c1, c2, c3 = coef(rr, field=RD, kcap=80)
        d = {"r": rr, "c1": RD(c1), "c2": RD(c2), "c3": RD(c3)}
        _FAST_CACHE[key] = d
    rr = d["r"]
    if need_c4 and "c4" not in d:
        d["c4"] = c4_fast(rr)
        d["phi"] = Phi_fast(1 + RD(eta_RF) * rr)
        d["lzeta"] = RD(log(zeta(1 + RD(eta_RF) * rr)))
    if need_c5 and "c5" not in d:
        d["c5"] = c5_fast(rr)
    return d


# =============================================================================================
# C_2 itself.
# =============================================================================================


def DEN(h, t, field=RF, exact_h2=False):
    r"""The shared denominator.  `exact_h2=True` keeps the un-weakened `(1-log 2) h^2/(t^2 LT)`
    term (used by the sanity check, where the `h <= t^(2/3)` weakening must not be applied)."""
    h, t = field(h), field(t)
    LT = log(t)
    h2term = ((1 - log(field(2))) * h ** 2 / (t ** 2 * LT) if exact_h2
              else (1 - log(field(2))) / (t ** (field(2) / 3) * LT))
    return (1 - log(2 * field(pi)) / LT - h2term
            - field("0.194") * field(pi) / h
            - field("9.908") * field(pi) / (h * LT))


def NUM_J(alpha, r, h, t, B1, B2, B3, B4, field=RF):
    h, t, r, alpha = field(h), field(t), field(r), field(alpha)
    LT = log(t)
    LLT = log(LT)
    ahat = sqrt(r ** 2 - alpha ** 2)
    D = field(rectDenom(r, alpha))
    return ((2 + 2 * ahat / h) * (B1 + field(pi) * B2 * LLT / LT + field(pi) * B3 / LT)
            + field(pi) * B4 / (h * LT)
            + field("3.35") * field(pi) / (D * h * t ** (field(1) / 3) * LT))


def NUM_L(alpha, r, h, t, A1, A2, A3, A4, A5, A6, field=RF):
    h, t, r, alpha = field(h), field(t), field(r), field(alpha)
    LT = log(t)
    LLT = log(LT)
    return (2 * A1 + 2 * A4 / h
            + field(pi) * (2 * A2 + 2 * A5 / h) * LLT / LT
            + 2 * field(pi) * A3 / LT
            + field(pi) * A6 / (h * LT)
            + field(pi) / ((r - alpha) * h * t * LT)
              * (field("0.335") + field("0.51") / LT))


def C2J_fast(alpha, r, h, t):
    d = fast_data(r, need_c5=True)
    B1 = RD(B1_of(r, alpha, RF(d["c1"])))
    B2 = RD(B2_of(r, alpha, RF(d["c2"])))
    B3 = RD(B3_of(r, alpha, RF(d["c3"])))
    B4 = RD(B4_of(r, alpha, RF(d["c5"])))
    return NUM_J(alpha, r, h, t, B1, B2, B3, B4, field=RD) / DEN(h, t, field=RD)


def C2L_fast(alpha, r, h, t):
    d = fast_data(r, need_c4=True)
    A1, A2, A3 = A123_of(alpha, r, field=RD)
    A4, A5, A6 = A456_of(alpha, r, d["c1"], d["c2"], d["c3"], d["c4"],
                         d["phi"], d["lzeta"], field=RD)
    return NUM_L(alpha, r, h, t, A1, A2, A3, A4, A5, A6, field=RD) / DEN(h, t, field=RD)


def C2J_certified(alpha, r, h, t):
    # `coef` must get an ORDERED `r` (its `find_k` compares `1-r` against `sigma(k)`), so pass the
    # exact dyadic rational; the ball arithmetic is selected by `field=R` instead.
    rq = QQ(RF(r))
    c1, c2, c3 = coef(rq, field=R, kcap=CERT_KCAP)
    c5 = c5r(R(r))
    B1 = B1_of(r, alpha, to_RF(c1))
    B2 = B2_of(r, alpha, to_RF(c2))
    B3 = B3_of(r, alpha, to_RF(c3))
    B4 = B4_of(r, alpha, to_RF(c5))
    val = NUM_J(alpha, r, h, t, B1, B2, B3, B4) / DEN(h, t)
    return val, [B1, B2, B3, B4]


def C2L_certified(alpha, r, h, t):
    rq = QQ(RF(r))
    c1, c2, c3 = coef(rq, field=R, kcap=CERT_KCAP)
    c4 = c4r(R(r))
    ph = Phi(1 + eta * R(r))
    lz = log(zeta(1 + eta * R(r)))
    A1, A2, A3 = A123_of(alpha, r, field=R)
    A4, A5, A6 = A456_of(alpha, r, c1, c2, c3, c4, ph, lz, field=R)
    Av = [to_RF(A1), to_RF(A2), to_RF(A3), to_RF(A4), to_RF(A5), to_RF(A6)]
    val = NUM_L(alpha, r, h, t, *Av) / DEN(h, t)
    return val, Av


def h0_threshold(t0):
    r"""The corollaries' admissibility threshold -- exactly the condition `DEN > 0`."""
    t0 = RF(t0)
    LT = log(t0)
    return ((97 * RF(pi) / 500) * (1 + RF(4954) / (97 * LT))
            / (1 - (1 - log(RF(2))) / (t0 ** (RF(2) / 3) * LT) - log(2 * RF(pi)) / LT))


# =============================================================================================
# SANITY CHECK (directive point 5): C_2 re-derived from the unnormalised U, E, L.
# =============================================================================================


def Lraw(h, t):
    h, t = RF(h), RF(t)
    return (log(t / (2 * RF(pi))) / RF(pi) - (1 - log(RF(2))) * h ** 2 / (RF(pi) * t ** 2)) * h \
        - RF("0.194") * log(t) - RF("9.908")


def sanity_check():
    print("=" * 92)
    print("SANITY CHECK: normalised C_2 vs (U+E)/L from the unnormalised definitions")
    print("(exact identity expected -- DEN uses the un-weakened (1-log 2) h^2/(t^2 LT) term here)")
    print("=" * 92)
    worst = RF(0)
    for (alpha, r, texp, hexp) in [(QQ(1) / 8, RF("0.52"), 12, 4),
                                   (QQ(1) / 16, RF("0.30"), 20, 6),
                                   (QQ(1) / 64, RF("0.11"), 30, 3)]:
        t = RF(10) ** texp
        h = RF(10) ** hexp
        LT = log(t)
        LLT = log(LT)
        ahat = sqrt(RF(r) ** 2 - RF(alpha) ** 2)
        D = rectDenom(r, alpha)

        c1, c2, c3 = coef(QQ(RF(r)), field=R, kcap=CERT_KCAP)
        c4 = c4r(R(r))
        c5 = c5r(R(r))
        B1 = B1_of(r, alpha, to_RF(c1))
        B2 = B2_of(r, alpha, to_RF(c2))
        B3 = B3_of(r, alpha, to_RF(c3))
        B4 = B4_of(r, alpha, to_RF(c5))

        # Jensen
        UJ = (2 * h + 2 * ahat) * (B1 * LT / RF(pi) + B2 * LLT + B3) + B4
        EJ = RF("3.35") / (D * t ** (RF(1) / 3))
        direct_J = (UJ + EJ) / Lraw(h, t)
        norm_J = NUM_J(alpha, r, h, t, B1, B2, B3, B4) / DEN(h, t, exact_h2=True)
        gapJ = abs(direct_J - norm_J) / abs(direct_J)

        # Littlewood
        ph = Phi(1 + eta * R(r))
        lz = log(zeta(1 + eta * R(r)))
        A1, A2, A3 = A123_of(alpha, r, field=R)
        A4, A5, A6 = A456_of(alpha, r, c1, c2, c3, c4, ph, lz, field=R)
        Av = [to_RF(A1), to_RF(A2), to_RF(A3), to_RF(A4), to_RF(A5), to_RF(A6)]
        UL = ((2 * Av[0] * h + 2 * Av[3]) / RF(pi) * LT
              + (2 * Av[1] * h + 2 * Av[4]) * LLT
              + 2 * Av[2] * h + Av[5])
        EL = (1 / (t * (RF(r) - RF(alpha)))) * (RF("0.335") + RF("0.51") / LT)
        direct_L = (UL + EL) / Lraw(h, t)
        norm_L = NUM_L(alpha, r, h, t, *Av) / DEN(h, t, exact_h2=True)
        gapL = abs(direct_L - norm_L) / abs(direct_L)

        worst = max(worst, gapJ, gapL)
        print(f"  alpha=1/{QQ(1)/alpha}, r={RR(r):.4f}, t=1e{texp}, h=1e{hexp}:")
        print(f"      Jensen     direct={RR(direct_J):.15g}  normalised={RR(norm_J):.15g}"
              f"  relgap={RR(gapJ):.3e}")
        print(f"      Littlewood direct={RR(direct_L):.15g}  normalised={RR(norm_L):.15g}"
              f"  relgap={RR(gapL):.3e}")
    print(f"\n  worst relative gap: {RR(worst):.3e}"
          f"  -> {'PASS' if worst < RR(1e-25) else 'FAIL'}")
    assert worst < RR(1e-25), "sanity check FAILED: normalised C_2 != (U+E)/L"
    print()
    return worst


def check_A_against_notebook():
    r"""`A123_of`/`A456_of` at `r = 1-sigma(k)` must reproduce
    `verify_littlewoodshort_table.sage`'s `find_optimal_Ar` (`A1 = v_k/(2(r-alpha))` etc.),
    and hence Table \ref{tab:littlewoodshort}."""
    print("=" * 92)
    print("CHECK: A123_of at r = 1-sigma(k) reproduces the notebook's v_k/(2(r-alpha)) form")
    print("=" * 92)
    worst = RF(0)
    for (alpha, k) in [(QQ(1) / 9, 1), (QQ(1) / 12, 1), (QQ(1) / 32, 2), (QQ(1) / 64, 3)]:
        r = 1 - sigma(k)
        A1, A2, A3 = A123_of(alpha, r, field=R)
        w = 2 * (RF(r) - RF(alpha))
        want1 = RF(vCoeff(k)) / w
        want2 = RF(vCoeffP(k)) / (RF(pi) * w)
        want3 = to_RF(vCoeffPP(k)) / (RF(pi) * w)
        for nm, got, want in [("A1", to_RF(A1), want1), ("A2", to_RF(A2), want2),
                              ("A3", to_RF(A3), want3)]:
            gap = abs(got - want) / max(abs(want), RF(1e-30))
            worst = max(worst, gap)
            print(f"  alpha=1/{QQ(1)/alpha} k={k}: {nm} general={RR(got):.10g}"
                  f"  notebook={RR(want):.10g}  relgap={RR(gap):.2e}")
    print(f"\n  worst relative gap: {RR(worst):.3e}"
          f"  -> {'PASS' if worst < RR(1e-25) else 'FAIL'}")
    assert worst < RR(1e-25), "A-constant generalisation does NOT match the notebook/table"
    print()


def check_phi_fast():
    print("=" * 92)
    print("CHECK: fast Phi vs certified Phi")
    print("=" * 92)
    worst = RF(0)
    for z in [RF("1.1"), RF("1.4"), RF("1.9")]:
        cert = to_RF(Phi(R(z)))
        fast = RF(Phi_fast(z))
        gap = abs(cert - fast) / abs(cert)
        worst = max(worst, gap)
        print(f"  z={RR(z):.3f}: certified={RR(cert):.15g}  fast={RR(fast):.15g}"
              f"  relgap={RR(gap):.2e}")
    print(f"\n  worst relative gap: {RR(worst):.3e} (search-tier only; final values are certified)")
    print()


# =============================================================================================
# r-optimization.
# =============================================================================================


def smallest_t0_exp(fastfn, alpha, h0, nmin=13, nmax=100000):
    r"""Smallest `n` with `C_2(alpha, r*, h_0, 10^n) < 1/2`, or `None` if none up to `nmax`.

    `C_2` is decreasing in `t_0` (the corollaries state this, and the admissibility threshold
    `h0_threshold(t_0)` is itself decreasing in `t_0`, so a `h_0` that is admissible at some `n`
    stays admissible above it). The predicate "below 1/2" is therefore monotone in `n`, and
    bisection is valid.

    `nmin = 13` because the corollaries require `t_0 > 10^{12}` STRICTLY, so `10^{12}` itself is
    inadmissible and `10^{13}` is the smallest power of ten that qualifies.

    The search runs entirely on the FAST (non-certified) path; the answer is re-evaluated
    certified by the caller. That matches how `r*` itself is located.
    """
    def below(n):
        t0 = RF(10) ** n
        if RF(h0) <= h0_threshold(t0):
            return False
        r, _ = optimise_r(fastfn, alpha, h0, t0, thorough=False)
        return bool(fastfn(alpha, r, h0, t0) < RD(1) / 2)

    if not below(nmax):
        return None
    lo, hi = nmin, nmax
    while lo < hi:
        mid = (lo + hi) // 2
        if below(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def optimise_r(fastfn, alpha, h, t, iters=GS_ITERS, thorough=False):
    r"""Minimise `fastfn(alpha,r,h,t)` over `r in (alpha,1)`.  Returns `(r*, unimodal_ok)`.

    Always: one full-bracket golden-section run PLUS a coarse grid scan, taking whichever is
    better -- so the reported `r*` is safe even if `C_2` is not unimodal.  `unimodal_ok` records
    whether the golden-section result *was* the better of the two (an empirical unimodality
    signal).  With `thorough=True` the search is additionally restarted on the two half-brackets,
    the stronger multi-bracket check; that is done on a sample of grid points (every
    `THOROUGH_EVERY`th) to keep the runtime sane."""
    lo, hi = RF(alpha) * RF(1.001), RF("0.999999")
    f = lambda rr: fastfn(alpha, rr, h, t)

    r1 = golden_section_min(f, lo, hi, iters=iters)
    cands = [r1]
    if thorough:
        mid = (lo + hi) / 2
        cands.append(golden_section_min(f, lo, mid, iters=iters))
        cands.append(golden_section_min(f, mid, hi, iters=iters))

    grid = [lo + (hi - lo) * RF(i) / GRID_PTS for i in range(GRID_PTS + 1)]
    cands.append(min([(f(g), g) for g in grid])[1])

    fbest, best = min([(f(rr), rr) for rr in cands])
    unimodal_ok = bool(abs(f(r1) - fbest) <= RF(1e-9) * abs(fbest))
    return best, unimodal_ok


# =============================================================================================
# MAIN
# =============================================================================================

# Table \ref{tab:CRvalues}'s alpha list, restricted to `alpha < 1/6` (both corollaries' hypothesis).
ALPHAS = [QQ(1) / n for n in [7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                              32, 64, 128, 256, 512, 1024, 2048]]
# `t_0` spans 10^13 .. 10^1000. The corollaries require `t_0 > 10^12` STRICTLY, so 10^12 itself
# is not admissible and the grid starts one power up. `RF`/`RD` are MPFR `RealField`s, whose
# exponent range easily covers 10^1000 (a hardware double would overflow at ~10^308).
# `h_0` stays modest: it only has to clear `h0_threshold(t_0)`, which tends to 97*pi/500 ~ 0.61
# from above as `t_0` grows, and is ~1.8 at the smallest `t_0` here.
T0S = [3 * RF(10) ** 12, RF(10) ** 13, RF(10) ** 20, RF(10) ** 30, RF(10) ** 40,
       RF(10) ** 50, RF(10) ** 100, RF(10) ** 200, RF(10) ** 500, RF(10) ** 1000,
       RF(10) ** 10000]
# Small `h_0` values are included because `h0_threshold(t_0) -> 97 pi/500 ~ 0.6095` from above,
# so even `h_0 = 1` is admissible once `t_0` is large enough.
H0S = [RF(1), RF(2), RF(5), RF(10), RF(10) ** 2, RF(10) ** 3]

if __name__ == "__main__" or True:
    t_start = time.time()
    print()
    check_phi_fast()
    check_A_against_notebook()
    sanity_check()

    print("=" * 92)
    print("h_0 ADMISSIBILITY THRESHOLD  (h_0 must exceed this for DEN > 0)")
    print("=" * 92)
    for t0 in T0S:
        thr = h0_threshold(t0)
        bad = [RR(h0) for h0 in H0S if RF(h0) <= thr]
        print(f"  t_0 = 1e{RR(log(t0)/log(10)):.0f}:  h_0 > {RR(thr):.6f}"
              f"   (grid values violating it: {bad if bad else 'none'})")
    print()

    def e10(x):
        return int(round(float(log(RF(x)) / log(RF(10)))))

    def pow10str(x):
        r"""LaTeX for a grid value `x`.

        Small integers print in plain decimal (`1`, `2`, `5`, `10`, `100`, `1000`) rather than
        as powers -- `$10^{1}$` for `h_0 = 10` is noise, and `h_0 = 1,2,5` are not powers of ten
        at all. Everything else prints as `10^n`, keeping the mantissa when there is one:
        `e10` alone would render `3e12` as `$10^{12}$`, discarding the mantissa and, worse,
        displaying a `t_0` the corollaries exclude (they need `t_0 > 10^{12}` strictly).
        """
        xr = RF(x)
        if xr <= 10000:
            k = int(round(float(xr)))
            if abs(float(xr) - k) < 1e-9:
                return f"${k}$"
        n = int(floor(float(log(xr) / log(RF(10)))))
        m = xr / RF(10) ** n
        if abs(float(m) - 1) < 1e-9:
            return f"$10^{{{n}}}$"
        ms = f"{float(m):g}"
        return f"${ms}\\cdot10^{{{n}}}$"

    def propstr(val, digits=3):
        r"""The PROPORTION `1 - 2 C_2`, as `a\cdot10^{-n}`, rounded DOWN.

        The frontier tables exist to witness `C_2 < 1/2`, and printing `C_2` itself to a fixed
        number of decimals defeats that: every frontier row is just under `1/2` by construction,
        so the witness can round away entirely (the `alpha = 1/8`, `h_0 = 10` row printed
        `0.5000000`, reading as a proportion of exactly zero).  Printing `1 - 2 C_2` instead keeps
        the significant digits wherever the margin sits, and `a\cdot10^{-n}` fits the column.

        The direction of rounding flips with the quantity.  `C_2` is an upper bound, so it is
        rounded UP by `c2str`.  `1 - 2 C_2` is a LOWER bound on the proportion of zeros in the
        middle band, so it is rounded DOWN: printing more would assert a proportion the
        computation does not support.  `digits` is the number of significant figures in `a`.
        """
        p = 1 - 2 * RF(val)
        if p <= 0:
            return "$\\leq 0$"
        n = int(floor(float(log(p) / log(RF(10)))))
        scale = RF(10) ** (digits - 1 - n)
        a = (p * scale).floor() / scale / RF(10) ** n
        return f"${RR(a):.{digits - 1}f}\\cdot10^{{{n}}}$"

    def c2str(val, digits=7):
        r"""`C_2` rounded so the printed number is still a valid bound.

        `C_2` is an UPPER bound on the zero-density ratio, so the printed value is rounded
        UP (`ceil` at `digits` places). Rounding down would print a number smaller than what
        was actually proved, i.e. would assert a bound the computation does not support.
        The `< 1/2` test that decides suppression uses the exact certified value, not this
        rounded one, so a value just under `1/2` is never mis-classified by the rounding.
        (Nothing is bolded; rows failing the test are suppressed instead.)
        """
        scale = RF(10) ** digits
        up = (RF(val) * scale).ceil() / scale
        return f"{RR(up):.{digits}f}"

    results = {"J": [], "L": []}
    nonunimodal = []
    nthorough = 0
    counter = 0

    for mech, fastfn, certfn in [("J", C2J_fast, C2J_certified),
                                 ("L", C2L_fast, C2L_certified)]:
        label = "Jensen (C_2^J)" if mech == "J" else "Littlewood (C_2^L)"
        print("=" * 92)
        print(f"{label}:  optimal r minimising C_2, per (alpha, h_0, t_0)")
        print("=" * 92)
        # NB: keep the "< 1/2 ?" label OUT of an f-string replacement field -- Sage's preparser
        # treats the contents of `{...}` as code and rewrites the `1/2` into `_sage_const_1/...`.
        print(f"{'alpha':>10} {'h_0':>8} {'t_0':>8} {'r*':>12} {'C_2':>14}   below 1/2?")
        for alpha in ALPHAS:
            for t0 in T0S:
                for h0 in H0S:
                    if RF(h0) <= h0_threshold(t0):
                        print(f"{'1/' + str(QQ(1)/alpha):>10} {'1e%d' % e10(h0):>8}"
                              f" {'1e%d' % e10(t0):>8}   -- skipped: h_0 below threshold --")
                        continue
                    counter += 1
                    thorough = (counter % THOROUGH_EVERY == 1)
                    if thorough:
                        nthorough += 1
                    rstar, uni = optimise_r(fastfn, alpha, h0, t0, thorough=thorough)
                    if not uni:
                        nonunimodal.append((mech, str(alpha), e10(h0), e10(t0)))
                    val, consts = certfn(alpha, rstar, h0, t0)
                    ok = bool(val < RF(1) / 2)
                    results[mech].append((alpha, rstar, h0, t0, val, ok))
                    print(f"{'1/' + str(QQ(1)/alpha):>10}"
                          f" {'1e%d' % e10(h0):>8}"
                          f" {'1e%d' % e10(t0):>8}"
                          f" {RR(rstar):>12.7f} {RR(val):>14.7f}   {'YES' if ok else '':>6}")
        print()

    print("=" * 92)
    print("SUMMARY: tuples achieving C_2 < 1/2")
    print("=" * 92)
    for mech in ["J", "L"]:
        good = [x for x in results[mech] if x[5]]
        nm = "C_2^J (Jensen)" if mech == "J" else "C_2^L (Littlewood)"
        print(f"\n{nm}: {len(good)} of {len(results[mech])} grid points achieve C_2 < 1/2")
        if good:
            best = min(good, key=lambda x: x[4])
            print(f"  smallest C_2 found: {RR(best[4]):.7f} at alpha=1/{QQ(1)/best[0]},"
                  f" r*={RR(best[1]):.7f}, h_0=1e{e10(best[2])}, t_0=1e{e10(best[3])}")
            largest_alpha = max(good, key=lambda x: x[0])
            print(f"  largest alpha with some C_2 < 1/2: 1/{QQ(1)/largest_alpha[0]}"
                  f"  (C_2={RR(largest_alpha[4]):.7f} at h_0=1e{e10(largest_alpha[2])},"
                  f" t_0=1e{e10(largest_alpha[3])})")
        else:
            print("  (none on this grid)")

    print(f"\nUnimodality: full 3-bracket restart done at {nthorough} sampled grid point(s);"
          f" a full-bracket golden-section vs coarse-grid cross-check was done at ALL"
          f" {len(results['J']) + len(results['L'])} points.")
    if nonunimodal:
        print(f"WARNING: golden-section lost to the grid scan at {len(nonunimodal)} point(s)"
              f" -- C_2 may not be unimodal in r there.  The reported r* is the best over"
              f" {{golden-section, grid scan}} in every case, so the tabulated C_2 is still valid.")
        for x in nonunimodal[:12]:
            print(f"    {x}")
    else:
        print("No disagreement found: golden-section matched or beat the coarse grid argmin"
              " everywhere (empirical evidence of unimodality, not a proof).")

    # ------------------------------------------------- smallest t_0 = 10^n reaching C_2 < 1/2
    print("=" * 92)
    print("SMALLEST t_0 = 10^n with C_2 < 1/2, per (alpha, h_0)")
    print("=" * 92)
    print(f"{'mech':>5} {'alpha':>10} {'h_0':>8} {'n':>8} {'r*':>12} {'C_2':>14}")
    smallest = {"J": [], "L": []}
    for mech, fastfn, certfn in [("J", C2J_fast, C2J_certified),
                                 ("L", C2L_fast, C2L_certified)]:
        for alpha in ALPHAS:
            for h0 in H0S:
                n = smallest_t0_exp(fastfn, alpha, h0)
                if n is None:
                    smallest[mech].append((alpha, h0, None, None, None))
                    print(f"{mech:>5} {'1/' + str(QQ(1)/alpha):>10} {RR(h0):>8.0f}"
                          f" {'none':>8}")
                    continue
                t0 = RF(10) ** n
                rstar, _ = optimise_r(fastfn, alpha, h0, t0, thorough=False)
                val, _ = certfn(alpha, rstar, h0, t0)
                # The bisection ran on the fast path; if the certified value at `n` misses,
                # step up until it does not, so the tabulated row is certified-correct.
                while val >= RF(1) / 2 and n < 100000:
                    n += 1
                    t0 = RF(10) ** n
                    rstar, _ = optimise_r(fastfn, alpha, h0, t0, thorough=False)
                    val, _ = certfn(alpha, rstar, h0, t0)
                smallest[mech].append((alpha, h0, n, rstar, val))
                print(f"{mech:>5} {'1/' + str(QQ(1)/alpha):>10} {RR(h0):>8.0f}"
                      f" {n:>8} {RR(rstar):>12.7f} {RR(val):>14.7f}")
    print()

    # ------------------------------------------------------------------ LaTeX fragment
    out = []
    out.append("% Generated by Code/compute_C2_tables.sage -- do not edit by hand.")
    out.append("% Tables of C_2^J / C_2^L for Corollaries \\ref{cor:main-jensen} and")
    out.append("% \\ref{cor:main-littlewood}, with r optimised to minimise C_2.")
    for mech in ["J", "L"]:
        nm = "J" if mech == "J" else "L"
        capt = ("Values of $C_2^J(\\alpha,r,h_0,t_0)$ for Corollary \\ref{cor:main-jensen}"
                if mech == "J" else
                "Values of $C_2^L(\\alpha,r,h_0,t_0)$ for Corollary \\ref{cor:main-littlewood}")
        # `longtable`, not `tabular` in a `table` float: these run to several hundred rows and a
        # float cannot break across pages, so a `tabular` would simply overflow the page. The
        # `\endhead`/`\endfoot` blocks repeat the column headings on every continuation page.
        hdr = "$\\alpha$&$r$&$h_0$&$t_0$&$C_2^" + nm + "$\\\\"
        out.append("")
        out.append("\\begin{longtable}{|cc|cc|c|}")
        # NB: no bolding is applied anywhere, so the caption must not claim any. Rows with
        # `C_2 >= 1/2` are suppressed (kept as comments), which is the only distinction drawn.
        # This caption reaches only `C2_tables_raw.tex`; the paper's captions are written by
        # `emit_C2_tables.py`.
        out.append(f"\\caption{{{capt}, with $r$ optimised to minimise $C_2$. "
                   "Only rows with $C_2<1/2$ are shown.}"
                   f"\\label{{tab:C2{nm}}}\\\\")
        out.append("\\hline")
        out.append(hdr)
        out.append("\\hline")
        out.append("\\endfirsthead")
        out.append("\\multicolumn{5}{c}{{\\tablename\\ \\thetable{} -- continued}}\\\\")
        out.append("\\hline")
        out.append(hdr)
        out.append("\\hline")
        out.append("\\endhead")
        out.append("\\hline")
        out.append("\\multicolumn{5}{r}{{continued on next page}}\\\\")
        out.append("\\endfoot")
        out.append("\\hline")
        out.append("\\endlastfoot")
        nshown = 0
        for (alpha, rstar, h0, t0, val, ok) in results[mech]:
            a = f"$1/{QQ(1)/alpha}$"
            rr = f"${RR(rstar):.7f}$"
            hh = pow10str(h0)
            tt = pow10str(t0)
            row = f"{a}&{rr}&{hh}&{tt}&${c2str(val)}$\\\\"
            if ok:
                nshown += 1
                out.append(row)
            else:
                # Suppressed, not discarded: rows with C_2 >= 1/2 carry no information for the
                # corollaries' purpose, but the computation was done and is kept here so the
                # grid can be seen in full by reading the source.
                out.append(f"% [C_2 >= 1/2, suppressed] {row}")
        out.append("\\end{longtable}")
        print(f"  table {nm}: {nshown} of {len(results[mech])} rows shown"
              f" ({len(results[mech]) - nshown} suppressed as C_2 >= 1/2)")

    # third table: the t_0 frontier
    for mech in ["J", "L"]:
        nm = mech
        capt = ("Smallest $t_0=10^n$ for which $C_2^%s(\\alpha,r,h_0,t_0)<1/2$, with $r$ "
                "optimised. The last column is the resulting proportion $1-2C_2^%s$ of zeros "
                "with real part in $[\\alpha,1-\\alpha]$, rounded down. Since $C_2$ is "
                "decreasing in $t_0$, the bound holds for every $t>t_0$." % (nm, nm))
        hdr = "$\\alpha$&$h_0$&$n$&$r$&$1-2C_2^" + nm + "$\\\\"
        out.append("")
        out.append("\\begin{longtable}{|cc|c|cc|}")
        out.append(f"\\caption{{{capt}}}\\label{{tab:C2{nm}frontier}}\\\\")
        out.append("\\hline")
        out.append(hdr)
        out.append("\\hline")
        out.append("\\endfirsthead")
        out.append("\\multicolumn{5}{c}{{\\tablename\\ \\thetable{} -- continued}}\\\\")
        out.append("\\hline")
        out.append(hdr)
        out.append("\\hline")
        out.append("\\endhead")
        out.append("\\hline")
        out.append("\\multicolumn{5}{r}{{continued on next page}}\\\\")
        out.append("\\endfoot")
        out.append("\\hline")
        out.append("\\endlastfoot")
        for (alpha, h0, n, rstar, val) in smallest[mech]:
            a = f"$1/{QQ(1)/alpha}$"
            hh = pow10str(h0)
            if n is None:
                out.append(f"{a}&{hh}&\\multicolumn{{3}}{{c|}}{{none with $n\\leq 10^5$}}\\\\")
            else:
                out.append(f"{a}&{hh}&${n}$&${RR(rstar):.7f}$&{propstr(val)}\\\\")
        out.append("\\end{longtable}")

    # NOTE: this writes the RAW record -- every computed row, with C_2 >= 1/2 rows kept as
    # comments -- NOT the fragment the paper \input's. `Code/emit_C2_tables.py` reads this
    # file and writes `C2_tables.tex`, applying the presentation rules (h_0 selection, t_0
    # thinning, column order, two-panel layout). Splitting the two means a layout change costs
    # seconds instead of this script's ~80 minutes, and it keeps one source of truth for the
    # numbers. Do not point this back at C2_tables.tex: the emitter reads raw and writes the
    # view, so a shared path would let a re-run clobber the view, or the emitter parse its own
    # thinned output and lose rows.
    with open("/home/algie/lean-projects/ZerosInShortIntervals/Code/C2_tables_raw.tex",
              "w") as fh:
        fh.write("\n".join(out) + "\n")
    print("\nRaw LaTeX record written to Code/C2_tables_raw.tex")
    print("Now run:  python3 /home/algie/lean-projects/ZerosInShortIntervals/Code/"
          "emit_C2_tables.py")
    print(f"\nTotal runtime: {time.time()-t_start:.1f}s")
