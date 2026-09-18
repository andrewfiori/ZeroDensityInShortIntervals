r"""Compute the alpha = 1/6 row of Table \ref{tab:rectangularjensen} (Table 5), properly optimised
over r.

**No Lean target.**  This script neither certifies a hypothesis-class field nor checks a theorem:
it recovers a row the paper computes and then suppresses, so that the suppression can be seen to
be a choice about informativeness rather than about definedness.

WHY THE ROW IS MISSING.  `verify_alpha_max_sixth.sage` shows, in exact rational arithmetic, that
alpha = 1/6 is where the argument stops: min_r A1(1/6,r) = 1/4 exactly, so the one-sided
proportion coefficient 2*A1 equals 1/2 and the statement says nothing.  Rows at alpha >= 1/6 were
therefore computed and then suppressed.  The constants themselves are perfectly finite there --
the result is vacuous, not undefined -- so the row can be restored with the vacuous entries
marked.

`alpha < 1/6` is the paper's own hypothesis (Corollary \ref{cor:simpmain}, Corollary 1), and Lean
proves the corresponding statements outright: `PositiveProportion.positiveProportion_of_lt_sixth`
and `positiveProportion_littlewood_half` assume nothing beyond `0 < alpha < 1/6`.  Per
`PositiveProportion.lean`'s own module docstring, the threshold is sharp at the endpoint: at
alpha = 1/6, r = 1/2 gives limiting constant exactly 0 and no other r does better.

This script reuses `verify_circular_rectangular_tables.sage`'s machinery (`optimal_r_rectangular`,
`coef`, `c5r`, `rectDenom`, `roundup_to`) so the numbers are produced exactly the way the
published rows were, rather than reconstructed on a grid.

RIGOR.  Only `coef` and `c5r` are ball-certified (`ComplexBallField(200)`); `optimal_r_rectangular`
runs its golden-section search on a `RealField(53)` objective, and `rectDenom`/`roundup_to` are
plain `RealField(200)`.  Moreover the `B_i` below are built from `c.mid()`, i.e. the ball
MIDPOINTS, discarding the radii -- so the rows printed here are approximations, not enclosures.
The script's own conclusion (is 2*B1 >= 1/2?) is a yes/no comparison, and the printed 2*B1 values
are what it rests on; read them as approximations.

Run with:  sage Code/compute_alpha_sixth_row.sage
"""

load("Code/verify_circular_rectangular_tables.sage")

print("\n\n" + "=" * 92)
print("ALPHA = 1/6 ROW (and neighbours), optimised over r exactly as the published rows are")
print("=" * 92)

PHI1_local = RF(1.7975699586287395)

NEW_ALPHA = [QQ(1) / 6, QQ(2) / 13, QQ(1) / 7]   # 1/7 is a published row: a self-check

print(f"{'alpha':>8} {'r*':>12} {'B1':>12} {'B2':>12} {'B3':>12} {'B4':>12} "
      f"{'ahat':>12} {'r*/alpha':>10} {'2*B1':>10}")

results = {}
for alpha in NEW_ALPHA:
    rstar = optimal_r_rectangular(alpha)
    c = coef(R(rstar))
    c1, c2, c3 = c[0], c[1], c[2]
    c5 = c5r(R(rstar))
    D = rectDenom(RF(rstar), RF(alpha))
    B1 = RF(c1.mid()) / D
    B2 = RF(c2.mid()) / (RF(pi) * D)
    B3 = RF(c3.mid()) / (RF(pi) * D)
    B4 = (2 * PHI1_local + RF(c5.mid())) / D
    ahat = sqrt(RF(rstar) ** 2 - RF(alpha) ** 2)
    results[alpha] = (rstar, B1, B2, B3, B4, ahat)
    print(f"{str(alpha):>8} {roundup_to(rstar,7):>12} {roundup_to(B1,7):>12} "
          f"{roundup_to(B2,7):>12} {roundup_to(B3,7):>12} {roundup_to(B4,7):>12} "
          f"{roundup_to(ahat,7):>12} {roundup_to(rstar/RF(alpha),7):>10} "
          f"{RF(2*B1):>10.7f}")

print()
print("SUPPRESSION TEST.  The Jensen mechanism's one-sided proportion coefficient is 2*B1;")
print("the row carries information only when 2*B1 < 1/2.")
for alpha in NEW_ALPHA:
    B1 = results[alpha][1]
    v = RF(2 * B1)
    print(f"  alpha={str(alpha):>6}:  2*B1 = {v:.7f}   "
          f"{'>= 1/2  -> VACUOUS, suppress' if v >= RF(0.5) else '< 1/2  -> informative'}")

print()
print("Cross-check against the certified Littlewood threshold: verify_alpha_max_sixth.sage")
print("gives min_r A1(1/6,r) = 1/4 EXACTLY, i.e. 2*A1 = 1/2 exactly at alpha = 1/6.  The paper")
print("takes whichever mechanism is smaller, so alpha = 1/6 sits exactly on the boundary.")
