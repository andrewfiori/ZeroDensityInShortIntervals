#!/usr/bin/env python3
"""Recover B_{i,alpha,r} at alpha near 1/6, the rows Table \\ref{tab:rectangularjensen} (Table 5)
suppresses.

**No Lean target.**  Nothing here certifies a hypothesis-class field.  It is an exploratory
recovery of suppressed table rows, plus one numeric comparison against the literature bound the
project imports as `LiteratureInputs.farzanfard_zero_density_interval`.

WHY THE TABLE STOPS AT 1/7.  `verify_alpha_max_sixth.sage` shows, in exact rational arithmetic,
that alpha = 1/6 is where the argument stops: min_r A1(1/6,r) = 1/4 exactly (at r = 1/2 =
sigma(0)), so 4*A1 = 1 and the two-sided proportion of zeros outside [alpha,1-alpha] is exactly
1 -- the statement says nothing.  One-sided, the coefficient is 2*A1 = 1/2.  So rows at and near
1/6 were computed but suppressed: their final value is >= 1/2 and the row carries no information.
`alpha < 1/6` is the paper's own hypothesis (Corollary \\ref{cor:simpmain}, Corollary 1), proved in
Lean as `PositiveProportion.positiveProportion_of_lt_sixth`.

That does NOT mean the B_i blow up.  At r = 1/2, alpha = 1/6 the denominator
D_{r,alpha} = rectDenom(1/2, 1/6) is finite and positive, so the constants are perfectly
well-defined; the result is merely vacuous.  Which means the `h >> t^{2/3}` zero-density
comparison -- the remark following Theorem \\ref{thm:main-jensen} (Theorem 2), which observes that
in that regime the claim follows from a classical zero-density estimate instead -- IS computable
at alpha -> 1/6, and that is what the second half of this script does.

METHOD.  `verify_circular_rectangular_tables.sage` defines
    B1 = c1(r)/D(r,alpha),  B2 = c2(r)/(pi D),  B3 = c3(r)/(pi D),  B4 = (2 Phi(1) + c5(r))/D,
so the c_i depend ONLY on r.  Each published row therefore determines c_i(r) at that row's r:
    c1(r) = B1_row * D(r, alpha_row),   etc.
Re-dividing by D(r, 1/6) gives the B_i at alpha = 1/6 for that same r.  Sweeping the published
r values and taking the r that MINIMISES B1 approximates the paper's own optimisation (the paper
picks r to minimise C1 = B1).  Minimising B1 is also the HARDEST case for the zero-density
comparison, since U_J grows with B1 -- so this is the conservative choice.

CAVEAT: this recovers c_i only at the finitely many r values the table publishes, so the
optimum found is over that grid, not over all r.  A true optimum would need the c_i as functions
of r, which lives in `verify_circular_rectangular_tables.sage`.

Pure-Python (mpmath only); no Sage required.  Everything runs at 30 decimal digits in plain
mpmath floating point -- no interval arithmetic, so the ratios printed are indicative, not
certified.
"""
import mpmath as mp

mp.mp.dps = 30

# `C_U`, `C_V` are the two constants of the classical short-interval zero-density bound the project
# imports, `LiteratureInputs.farzanfard_zero_density_interval`:
#   Nrect T1 T2 alpha <= 12.45321 * T2^(8 alpha/3) * (log T2)^(3+2 alpha) + 3.869 * (log T2)^2
# for alpha in [0,1/4] and 3*10^12 <= T1 <= T2.  `H0 = 3*10^12` is that floor (Platt-Trudgian's
# verified height).  `PHI1` is the bound of Proposition \ref{prop:outside2} (Proposition 22),
# in Lean the field `NumericCertificates.integral_log_zeta_Ioi_one_lt`, certified by
# `Code/verify_Phi_one_bound.sage`.  All four are consumed here, none is checked here.
C_U = mp.mpf('12.45321')
C_V = mp.mpf('3.869')
H0 = 3 * mp.mpf(10) ** 12
PHI1 = mp.mpf('1.7975699586287395')

# alpha, r, B1, B2, B3, B4  --- tex Table \ref{tab:rectangularjensen} (Table 5), verbatim
ROWS = [
    (mp.mpf(1) / 7, '0.5647100', '0.2457053', '0.3900919', '1.450119', '6.518765'),
    (mp.mpf(1) / 8, '0.5185446', '0.2294753', '0.4239720', '1.514935', '6.977388'),
    (mp.mpf(1) / 9, '0.5030821', '0.2172051', '0.4340594', '1.446353', '6.922300'),
    (mp.mpf(1) / 10, '0.4821212', '0.2079206', '0.4778655', '1.331336', '7.058488'),
    (mp.mpf(1) / 11, '0.3820330', '0.1991813', '0.8624038', '0.9519504', '9.637060'),
    (mp.mpf(1) / 12, '0.3390065', '0.1907470', '1.076388', '0.7557944', '11.128858'),
]


def rectDenom(r, alpha):
    return 2 * r * mp.sqrt(1 - (alpha / r) ** 2) - 2 * alpha * mp.atan(
        mp.sqrt((r / alpha) ** 2 - 1))


def hatAlpha(r, alpha):
    return mp.sqrt(r ** 2 - alpha ** 2)


def recover_c(alpha_row, r, B1, B2, B3, B4):
    """Invert the B_i definitions to get the r-only constants."""
    D = rectDenom(r, alpha_row)
    return (B1 * D, B2 * mp.pi * D, B3 * mp.pi * D, B4 * D - 2 * PHI1)


def B_at(alpha, r, c1, c2, c3, c5):
    D = rectDenom(r, alpha)
    if D <= 0:
        return None
    return (c1 / D, c2 / (mp.pi * D), c3 / (mp.pi * D), (2 * PHI1 + c5) / D)


def zero_density_rhs(alpha, T2):
    L = mp.log(T2)
    return C_U * T2 ** (mp.mpf(8) / 3 * alpha) * L ** (3 + 2 * alpha) + C_V * L ** 2


def UJ(ahat, B1, B2, B3, B4, h, t):
    L = mp.log(t)
    return (2 * h + 2 * ahat) * (B1 / mp.pi * L + B2 * mp.log(L) + B3) + B4


def main():
    print("=" * 92)
    print("Recovered r-only constants c_i(r) from each published row")
    print("=" * 92)
    cs = []
    for (a_row, r, B1, B2, B3, B4) in ROWS:
        r, B1, B2, B3, B4 = map(mp.mpf, (r, B1, B2, B3, B4))
        c1, c2, c3, c5 = recover_c(a_row, r, B1, B2, B3, B4)
        cs.append((r, c1, c2, c3, c5))
        print(f"  r={mp.nstr(r, 7):>10} (from alpha={mp.nstr(a_row, 5):>8}): "
              f"c1={mp.nstr(c1, 6):>9} c2={mp.nstr(c2, 6):>9} "
              f"c3={mp.nstr(c3, 6):>9} c5={mp.nstr(c5, 6):>9}")

    for alpha_name, alpha in [('1/6.5', mp.mpf(1) / mp.mpf('6.5')), ('1/6.2', mp.mpf(1) / mp.mpf('6.2')),
                              ('1/6.05', mp.mpf(1) / mp.mpf('6.05')), ('1/6', mp.mpf(1) / 6)]:
        print()
        print("=" * 92)
        print(f"alpha = {alpha_name} = {mp.nstr(alpha, 8)}")
        print("=" * 92)
        best = None
        for (r, c1, c2, c3, c5) in cs:
            if r <= alpha:
                continue
            got = B_at(alpha, r, c1, c2, c3, c5)
            if got is None:
                continue
            B1, B2, B3, B4 = got
            if best is None or B1 < best[1]:
                best = (r, B1, B2, B3, B4)
        if best is None:
            print("  no admissible r on the published grid")
            continue
        r, B1, B2, B3, B4 = best
        ahat = hatAlpha(r, alpha)
        print(f"  best published r = {mp.nstr(r, 7)}   D = {mp.nstr(rectDenom(r, alpha), 7)}")
        print(f"  B1={mp.nstr(B1, 7)}  B2={mp.nstr(B2, 7)}  B3={mp.nstr(B3, 7)}  "
              f"B4={mp.nstr(B4, 7)}  ahat={mp.nstr(ahat, 7)}")
        print(f"  one-sided proportion coefficient 2*B1 = {mp.nstr(2 * B1, 7)}"
              f"   ({'>= 1/2 -- VACUOUS, hence suppressed' if 2 * B1 >= mp.mpf('0.5') else '< 1/2'})")
        print()
        print("  case (i) ratio [density]/U_J at the floor t = 3e12:")
        for nm, th in [('2/3', mp.mpf(2) / 3), ('3/4', mp.mpf(3) / 4),
                       ('4/5', mp.mpf(4) / 5), ('6/7', mp.mpf(6) / 7)]:
            h = H0 ** th
            rr = zero_density_rhs(alpha, H0 + h) / UJ(ahat, B1, B2, B3, B4, h, H0)
            print(f"    h=t^{nm:<4}  ratio = {mp.nstr(rr, 6):>10}  "
                  f"{'OK' if rr < 1 else 'no'}")


if __name__ == "__main__":
    main()
