#!/usr/bin/env python3
r"""
Does the LOG form of Farzanfard's zero-density bound close the `h > t^{2/3}` branch of
`Theorem \ref{thm:main-jensen}` (Theorem 2) and `Theorem \ref{thm:main-littlewood}` (Theorem 3)
(`MainTheorem.mainJensen` / `mainLittlewood`)?

EXPLORATORY REGIME ANALYSIS -- NOT a current certificate.  Answer: it helps but does not close
the branch, and the branch was dropped rather than repaired.  Theorems 2 and 3 and Corollaries
`\ref{cor:main-jensen}`/`\ref{cor:main-littlewood}` (Corollaries 4 and 5) are stated on
`h <= t^{2/3}` (resp. `t^{2/3} > h > h_0`) and are PROVED there; no Lean statement depends on
anything below.

INPUT.  Farzanfard, "Explicit zero density for the Riemann zeta function", MSc thesis, U. of
Lethbridge (2025), Theorem 4.46 / Remark 4.47 eq. (4.165) (read from the PDF in References/):

    N(sigma,T1,T2) <= (T2-T1) log T2 * log( 1 + U T2^{(8/3)(1-sigma)} (log T2)^{4-2 sigma} / (T2-T1) )
                      + V (log T2)^2,                       T1 > H0 = 3e12,  T2 > T0 = 3e12,

with U = U(sigma), V = V(sigma) from Table A.1 (sigma = 0.75, 0.76, ..., 0.99).  Corollary 4.50 is
(4.165) after `log(1+y) <= y` AND after replacing U, V by their maxima over sigma in [0.75,1]
(U = 12.45321 at sigma -> 1, V = 3.869 at sigma = 0.75); that is the form recorded by the
hypothesis-class field `LiteratureInputs.farzanfard_zero_density_interval`, exposed as the
theorem `ExternalFacts.farzanfard_zero_density_interval` and used by
`MainTheorem.Nrect_le_zero_density_bound` (which is retained only for a possible future extension
to `h > t^{2/3}`; nothing consumes it).

WHY THE LOG FORM MIGHT HELP.  With L := T2-T1 = 2h the (4.165) bound is
    2h log T2 * log(1 + Y/(2h)) + V (log T2)^2,   Y := U T2^{(8/3)alpha} (log T2)^{2+2alpha},
i.e. O(h log t) -- the SAME shape as U_J = (2h+2ahat)(B1/pi log t + ...) + B4 and
U_L = (2A1 h + 2A4)/pi log t + ... .  Its ratio to U_J is asymptotically
    pi * log(1 + Y/(2h)) / B1,
so it beats the main term exactly when Y/(2h) is small, i.e. for h large compared with Y.  The
(4.166)/(4.160) form replaces log(1+Y/(2h)) by Y/(2h) and is only good when Y/(2h) << 1.

THREE READINGS OF THE HYPOTHESIS T1 > H0.  In the application T1 = t-h with h > t^{2/3}, so T1
may be below H0 = 3e12 (or negative).  Since below height 3e12 every zero is on the critical line
(`LiteratureInputs.platt_trudgian_verified_below`),
N(sigma, t-h, t+h) = N(sigma, max(t-h, H0), t+h) for sigma > 1/2,
and the (4.165) right-hand side is INCREASING in L = T2-T1 (d/dL [L log(1+Y/L)] = log(1+Y/L) -
Y/(L+Y) > 0), so using L = 2h is always valid once T2 = t+h > T0.  If t+h <= T0 the count is 0.

PER-SIGMA CONSTANTS, CONSERVATIVELY.  Theorem 4.46 holds at each sigma with its own U(sigma),
V(sigma); Table A.1 tabulates them at sigma = 0.75(0.01)0.99 and the thesis (proof of Cor 4.50)
states that on each sub-interval U is maximal at the right end and V at the left end.  For a
sigma = 1 - alpha between rows we therefore use U from the row just ABOVE and V from the row just
BELOW.  (The author could run the thesis code at sigma = 5/6, 6/7, ... for exact values.)

WHAT IS REPORTED, for alpha = 1/6, 1/7, 1/8, 1/9, 1/10, 1/16, 1/64 with the paper's own tabulated
B_i (Table `\ref{tab:rectangularjensen}`, Table 5) and A_i (Table `\ref{tab:littlewoodshort}`,
Table 7):
  [A] ratio (4.165)/U at h = t^{2/3}, t = 3e12 ... 1e30  (uniform U,V and per-sigma), vs the
      (4.166) ratio, to show the gain;
  [B] monotonicity in h at fixed t (the ratio should DEcrease in h, so h = t^{2/3} is the worst case);
  [C] the crossover t* at h = t^{2/3} (smallest t from which the branch closes for ALL h >= t^{2/3});
  [D] the smallest exponent theta such that at t0 = 3e12 the branch closes for all h >= t^theta,
      i.e. where the case boundary would have to be moved to.  Moving it is not free: the tight
      collapses `MainTheoremTight.jensenTight_collapse`/`littlewoodTight_collapse` carry an error
      matched to h ~ t^{2/3} (RHS 3.34/t^{1/3}) and would have to be re-proved at the weaker
      exponent -- see `verify_four_region_split.py`.
For alpha = 1/6 the Jensen row is not in Table `\ref{tab:rectangularjensen}` (Table 5) (vacuous
for the paper's purpose); its B_i are recovered from the r = 0.5647100 row's c_i (Table
`\ref{tab:crvalues3}`, Table 6) via B_i = c_i / D(r, 1/6), as in
`Code/verify_alpha_sixth_B_values.py`.

Method: mpmath at 30 decimal digits, tabulation plus bisection.  Indicative, not ball arithmetic.

Run with:  python3 Code/indep_mpmath_zero_density_4165.py
"""
import mpmath as mp

mp.mp.dps = 30
H0 = 3 * mp.mpf(10) ** 12
U_UNIF, V_UNIF = mp.mpf('12.45321'), mp.mpf('3.869')
PHI1 = mp.mpf('1.7975699586287395')

# Table A.1 (T0 = H0 = 3e12): sigma, U, V
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


def UV_conservative(alpha):
    """U from the first tabulated sigma >= 1-alpha (U increasing), V from the last tabulated
    sigma <= 1-alpha (V decreasing); above 0.99 fall back to Cor 4.50's uniform values."""
    s = float(1 - alpha)
    U = None
    for (sg, u, v) in TABLE_A1:
        if sg >= s - 1e-12:
            U = mp.mpf(u)
            break
    if U is None:
        U = U_UNIF
    V = V_UNIF
    for (sg, u, v) in TABLE_A1:
        if sg <= s + 1e-12:
            V = mp.mpf(v)
    return U, V


def bound_log(alpha, h, t, U, V):
    """(4.165) with L = 2h, T2 = t + h."""
    T2 = t + h
    L2 = mp.log(T2)
    Y = U * T2 ** (mp.mpf(8) / 3 * alpha) * L2 ** (2 + 2 * alpha)
    return 2 * h * L2 * mp.log(1 + Y / (2 * h)) + V * L2 ** 2


def bound_lin(alpha, h, t, U, V):
    """(4.166) = Cor 4.50 shape, T2 = t + h."""
    T2 = t + h
    L2 = mp.log(T2)
    return U * T2 ** (mp.mpf(8) / 3 * alpha) * L2 ** (3 + 2 * alpha) + V * L2 ** 2


def rectDenom(r, a):
    return 2 * r * mp.sqrt(1 - (a / r) ** 2) - 2 * a * mp.atan(mp.sqrt((r / a) ** 2 - 1))


# Jensen rows: alpha -> (r, B1, B2, B3, B4, ahat)   [tex Table \ref{tab:rectangularjensen}, Table 5]
TABLE_J = {
    7: ('0.5647100', '0.2457053', '0.3900919', '1.450119', '6.518765', '0.5463417'),
    8: ('0.5185446', '0.2294753', '0.4239720', '1.514935', '6.977388', '0.5032529'),
    9: ('0.5030821', '0.2172051', '0.4340594', '1.446353', '6.922300', '0.4906586'),
    10: ('0.4821212', '0.2079206', '0.4778655', '1.331336', '7.058488', '0.4716364'),
    16: ('0.2909922', '0.1663861', '1.250289', '0.5551999', '12.302409', '0.2842010'),
    64: ('0.09924636', '0.1023306', '3.292282', '1.434352', '33.994587', '0.09800867'),
}
# alpha = 1/6: recover from the c_i of tex Table \ref{tab:crvalues3} (Table 6) at r = 0.5647100
_r6 = mp.mpf('0.5647100')
_c1, _c2, _c3, _c5 = map(mp.mpf, ('0.1761601', '0.8786375', '3.266227', '1.078532'))
_D6 = rectDenom(_r6, mp.mpf(1) / 6)
TABLE_J[6] = (str(_r6), mp.nstr(_c1 / _D6, 10), mp.nstr(_c2 / (mp.pi * _D6), 10),
              mp.nstr(_c3 / (mp.pi * _D6), 10), mp.nstr((2 * PHI1 + _c5) / _D6, 10),
              mp.nstr(mp.sqrt(_r6 ** 2 - (mp.mpf(1) / 6) ** 2), 10))

# Littlewood rows: alpha -> (r, A1..A6)   [tex Table \ref{tab:littlewoodshort}, Table 7]
TABLE_L = {
    6: ('0.5000000', '0.2469513', '0', '2.005451', '0.2201801', '1.948504', '10.269668'),
    7: ('0.5000000', '0.2304879', '0', '1.871754', '0.2055015', '1.818604', '9.585023'),
    8: ('0.5000000', '0.2195122', '0', '1.782623', '0.1957157', '1.732003', '9.128594'),
    9: ('0.2857143', '0.2045455', '0.9115238', '0.3971245', '0.1059233', '2.454546', '12.040681'),
    10: ('0.2857143', '0.1923077', '0.8569882', '0.3733649', '0.09958597', '2.307693', '11.320299'),
    16: ('0.2857143', '0.1600000', '0.7130142', '0.3106396', '0.08285553', '1.920001', '9.418489'),
    64: ('0.09677420', '0.09937889', '1.961264', '0.8544655', '0.01794826', '1.788820', '14.441878'),
}


def UJ(n, h, t):
    r, B1, B2, B3, B4, ahat = map(mp.mpf, TABLE_J[n])
    L = mp.log(t)
    return (2 * h + 2 * ahat) * (B1 / mp.pi * L + B2 * mp.log(L) + B3) + B4


def UL(n, h, t):
    r, A1, A2, A3, A4, A5, A6 = map(mp.mpf, TABLE_L[n])
    L = mp.log(t)
    return (2 * A1 * h + 2 * A4) / mp.pi * L + (2 * A2 * h + 2 * A5) * mp.log(L) + 2 * A3 * h + A6


ALPHAS = [6, 7, 8, 9, 10, 16, 64]


def ratio(mech, n, h, t, per_sigma, logform=True):
    alpha = mp.mpf(1) / n
    U, V = UV_conservative(alpha) if per_sigma else (U_UNIF, V_UNIF)
    b = bound_log(alpha, h, t, U, V) if logform else bound_lin(alpha, h, t, U, V)
    return b / (UJ(n, h, t) if mech == 'J' else UL(n, h, t))


print("=" * 100)
print("[A] ratio  zero-density bound / U  at h = t^(2/3)   ('lin' = Cor 4.50 form, 'log' = (4.165); 'ps' = per-sigma U,V)")
print("=" * 100)
for mech in ('J', 'L'):
    print(f"--- {'Jensen (U_J)' if mech == 'J' else 'Littlewood (U_L)'}")
    print(f"{'alpha':>6} {'t':>7} {'lin,unif':>10} {'log,unif':>10} {'log,ps':>10}   U(ps),V(ps)")
    for n in ALPHAS:
        alpha = mp.mpf(1) / n
        U, V = UV_conservative(alpha)
        for texp in (12.477, 13, 15, 20, 30):
            t = mp.mpf(10) ** texp
            h = t ** (mp.mpf(2) / 3)
            r1 = ratio(mech, n, h, t, False, logform=False)
            r2 = ratio(mech, n, h, t, False, logform=True)
            r3 = ratio(mech, n, h, t, True, logform=True)
            print(f"{'1/' + str(n):>6} {'1e%g' % texp:>7} {mp.nstr(r1, 5):>10} {mp.nstr(r2, 5):>10} {mp.nstr(r3, 5):>10}"
                  f"   {mp.nstr(U, 5)}, {mp.nstr(V, 5)}")
        print()

print("=" * 100)
print("[B] monotonicity in h at t = 3e12: ratio (log form, per-sigma) at h = t^(2/3) * {1, 3, 10, 100, 1e4, 1e6}")
print("=" * 100)
t = H0
for mech in ('J', 'L'):
    print(f"--- {mech}")
    for n in ALPHAS:
        h0 = t ** (mp.mpf(2) / 3)
        vals = [ratio(mech, n, h0 * m, t, True) for m in (1, 3, 10, 100, 10 ** 4, 10 ** 6)]
        print(f"  alpha=1/{n:<3} " + "  ".join(f"{mp.nstr(v, 5):>9}" for v in vals)
              + ("   decreasing" if all(vals[i] >= vals[i + 1] for i in range(len(vals) - 1)) else "   NOT monotone"))
    print()

print("=" * 100)
print("[C] crossover t*: smallest t with ratio <= 1 at h = t^(2/3) (then for all h >= t^(2/3) by [B])")
print("=" * 100)
print(f"{'alpha':>6} {'mech':>4} {'lin,unif':>12} {'log,unif':>12} {'log,ps':>12}")
for n in ALPHAS:
    for mech in ('J', 'L'):
        out = []
        for (ps, lf) in ((False, False), (False, True), (True, True)):
            def holds(texp):
                tt = mp.mpf(10) ** texp
                return ratio(mech, n, tt ** (mp.mpf(2) / 3), tt, ps, lf) <= 1
            lo, hi = 12.477, 100000.0
            if not holds(hi):
                out.append("  never<1e5")
                continue
            if holds(lo):
                out.append("  <=3e12")
                continue
            for _ in range(200):
                mid = (lo + hi) / 2
                if holds(mid):
                    hi = mid
                else:
                    lo = mid
            out.append(f"10^{hi:.1f}")
        print(f"{'1/' + str(n):>6} {mech:>4} {out[0]:>12} {out[1]:>12} {out[2]:>12}")

print()
print("=" * 100)
print("[D] case boundary: smallest theta with ratio <= 1 at h = t^theta for t = 3e12 (log form), and whether it")
print("    stays <= 1 at h = t^theta for t = 1e13, 1e20, 1e100 (so the branch would close for all t > 3e12, h >= t^theta)")
print("=" * 100)
print(f"{'alpha':>6} {'mech':>4} {'theta(unif)':>12} {'theta(ps)':>10}   check at larger t (ps)")
for n in ALPHAS:
    for mech in ('J', 'L'):
        res = []
        for ps in (False, True):
            def holds_th(th):
                tt = H0
                return ratio(mech, n, tt ** th, tt, ps) <= 1
            if not holds_th(mp.mpf(1)):
                res.append(None)
                continue
            lo, hi = mp.mpf(2) / 3, mp.mpf(1)
            if holds_th(lo):
                res.append(lo)
                continue
            for _ in range(60):
                mid = (lo + hi) / 2
                if holds_th(mid):
                    hi = mid
                else:
                    lo = mid
            res.append(hi)
        th = res[1]
        chk = ""
        if th is not None:
            chk = "  ".join(f"1e{e}:{'ok' if ratio(mech, n, (mp.mpf(10) ** e) ** th, mp.mpf(10) ** e, True) <= 1 else 'FAIL'}"
                           for e in (13, 20, 100))
        print(f"{'1/' + str(n):>6} {mech:>4} {('none (h=t fails)' if res[0] is None else mp.nstr(res[0], 5)):>12}"
              f" {('none' if th is None else mp.nstr(th, 5)):>10}   {chk}")
print()
print("Reading: 'theta = 0.66667' means the existing h > t^(2/3) boundary already closes at t = 3e12;")
print("a larger theta is the boundary the tight collapse (Theorems 23/31, h <= t^theta) would have to be")
print("re-proved at (SorriesAndAxioms 1.5 discusses theta = 4/5 at the current constants).")
