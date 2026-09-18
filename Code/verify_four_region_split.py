#!/usr/bin/env python3
r"""Four-region split for `Theorem \ref{thm:main-jensen}` (Theorem 2): h<t^{2/3},
t^{2/3}<h<t^{3/4}, t^{3/4}<h<t^{4/5}, t^{4/5}<h.

EXPLORATORY REGIME ANALYSIS -- NOT a current certificate for anything in Lean.  The h > t^{2/3}
branch was dropped rather than covered: Theorem 2, Theorem 3 and Corollaries 4 and 5 are all
stated on h <= t^{2/3} (resp. t^{2/3} > h > h_0) and are PROVED there.  What follows is the record
of what a finer split would and would not have bought.

Which regions close with EXISTING machinery, and which need new work?

Two mechanisms are available.

(1) THE TIGHT MECHANISM (`MainTheoremTight.mainJensenTight`, proved).
    Its `h`-dependence sits entirely in `jensenTight_collapse`, which asserts

      5(h+ahat)/(3(t-h-ahat-1)) + [two lower-order terms]
        <  3.34/t^{1/3} + 4.01/t^{4/3} + 291/(t^{4/3} log t).

    The leading behaviour is  5h/(3t) < 3.34/t^{1/3}, i.e. h < (3*3.34/5) t^{2/3} = 2.004 t^{2/3}.
    So the RHS exponent t^{-1/3} is MATCHED to h ~ t^{2/3}: the tight mechanism does NOT extend
    to t^{3/4} at its current constants.  Extending it to h < t^theta needs the error term
    restated as ~ (5/3) t^{-(1-theta)}.  That is a change of statement, not a free extension.

(2) ZERO DENSITY (`MainTheorem.Nrect_le_zero_density_bound`, proved from the hypothesis-class
    field `LiteratureInputs.farzanfard_zero_density_interval`; it is retained in the development
    only for a possible future extension to h > t^{2/3}, nothing consumes it).
    U_J is ~linear in h and the density bound is ~constant in h, so within a region
    t^a < h < t^b the binding case is the LOWER endpoint h = t^a.

This script tabulates, for each region and each alpha, whether mechanism (2) covers it at the
floor t = 3e12, and what error constant mechanism (1) would need to reach up to each boundary.

Pure-Python (mpmath only); no Sage required.
"""
import mpmath as mp

mp.mp.dps = 40

C_U = mp.mpf('12.45321')
C_V = mp.mpf('3.869')
H0 = 3 * mp.mpf(10) ** 12

# alpha, r, B1, B2, B3, B4, alphahat_r --- tex Table \ref{tab:rectangularjensen} (Table 5)
TABLE = [
    (mp.mpf(1) / 7, '0.5647100', '0.2457053', '0.3900919', '1.450119', '6.518765', '0.5463417'),
    (mp.mpf(1) / 8, '0.5185446', '0.2294753', '0.4239720', '1.514935', '6.977388', '0.5032529'),
    (mp.mpf(1) / 9, '0.5030821', '0.2172051', '0.4340594', '1.446353', '6.922300', '0.4906586'),
    (mp.mpf(1) / 10, '0.4821212', '0.2079206', '0.4778655', '1.331336', '7.058488', '0.4716364'),
    (mp.mpf(1) / 16, '0.2909922', '0.1663861', '1.250289', '0.5551999', '12.302409', '0.2842010'),
]

BOUNDARIES = [('2/3', mp.mpf(2) / 3), ('3/4', mp.mpf(3) / 4), ('4/5', mp.mpf(4) / 5)]


def zero_density_rhs(alpha, T2):
    L = mp.log(T2)
    return C_U * T2 ** (mp.mpf(8) / 3 * alpha) * L ** (3 + 2 * alpha) + C_V * L ** 2


def UJ(ahat, B1, B2, B3, B4, h, t):
    L = mp.log(t)
    return (2 * h + 2 * ahat) * (B1 / mp.pi * L + B2 * mp.log(L) + B3) + B4


def ratio(alpha, ahat, B1, B2, B3, B4, t, theta):
    h = t ** mp.mpf(theta)
    return zero_density_rhs(alpha, t + h) / UJ(ahat, B1, B2, B3, B4, h, t)


def tight_lhs(h, t, ahat):
    """jensenTight_collapse's left side, exactly."""
    d = t - h - ahat - 1
    return (5 * (h + ahat) / (3 * d)
            + 2 * (h + ahat) / d ** 2
            + 1158 * (h + ahat) / (8 * d ** 2 * mp.log(d)))


def main():
    print("=" * 94)
    print("(1) ZERO DENSITY: ratio [density bound]/U_J at each region's LOWER endpoint,")
    print("    evaluated at the floor t = 3e12.  Need < 1 for the region to be covered.")
    print("=" * 94)
    print(f"{'alpha':>8}  " + "  ".join(f"{'h=t^' + nm:>14}" for nm, _ in BOUNDARIES))
    for (alpha, r, B1, B2, B3, B4, ahat) in TABLE:
        B1, B2, B3, B4, ahat = map(mp.mpf, (B1, B2, B3, B4, ahat))
        cells = []
        for nm, th in BOUNDARIES:
            rr = ratio(alpha, ahat, B1, B2, B3, B4, H0, th)
            cells.append(f"{mp.nstr(rr, 5):>9}{'  OK' if rr < 1 else '  no'}")
        print(f"{mp.nstr(alpha, 5):>8}  " + "  ".join(cells))
    print()
    print("  Region 2 (t^{2/3}<h<t^{3/4}) is covered iff the t^{2/3} column is OK.")
    print("  Region 3 (t^{3/4}<h<t^{4/5}) iff the t^{3/4} column is OK.")
    print("  Region 4 (h>t^{4/5})         iff the t^{4/5} column is OK.")

    print()
    print("=" * 94)
    print("(2) TIGHT MECHANISM: what error constant would jensenTight_collapse need to reach")
    print("    up to h = t^theta?  (its current RHS is 3.34/t^{1/3}, matched to theta=2/3)")
    print("=" * 94)
    ahat_max = mp.mpf(1)          # hatAlpha < 1 always (hatAlpha_lt_one)
    for nm, th in BOUNDARIES:
        print(f"  theta = {nm}:")
        worst = mp.mpf(0)
        for texp in [12.48, 13, 15, 20, 50, 200]:
            t = mp.mpf(10) ** texp
            h = t ** th
            lhs = tight_lhs(h, t, ahat_max)
            # express as C / t^{1-theta}
            C = lhs * t ** (1 - th)
            worst = max(worst, C)
            print(f"      t=10^{texp:<6}  LHS = {mp.nstr(lhs, 6):>12}"
                  f"   = {mp.nstr(C, 6):>9} / t^{mp.nstr(1 - th, 4)}")
        print(f"    -> needs RHS constant >= {mp.nstr(worst, 6)} at exponent t^-{mp.nstr(1-th,4)}"
              f"   (current: 3.34 at t^-0.3333)")
        print()

    print("=" * 94)
    print("(3) THE CONSEQUENCE")
    print("=" * 94)
    print("  A four-way split does NOT by itself help: within each region the zero-density")
    print("  case is decided by the region's LOWER endpoint, so regions 2 and 3 inherit")
    print("  exactly the t^{2/3} and t^{3/4} columns above.  Extra boundaries buy nothing")
    print("  unless a DIFFERENT mechanism covers the middle regions.")
    print()
    print("  The productive split is TWO regions, not four:")
    print("      h < t^{4/5}   -- tight mechanism, error restated as ~3.34/t^{1/5}")
    print("      h > t^{4/5}   -- zero density (covers alpha <= 1/7 at the floor)")
    print("  This closes alpha = 1/7 at t > 3e12, which neither t^{2/3} nor t^{3/4} does.")
    print("  Cost: jensenTight_collapse and littlewoodTight_collapse must be reproved with")
    print("  the weaker error exponent, and E_Jensen / the C_2 tables pick up t^{1/5}")
    print("  where they currently have t^{1/3}.")


if __name__ == "__main__":
    main()
