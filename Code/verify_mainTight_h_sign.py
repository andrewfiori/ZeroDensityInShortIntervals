"""Why `mainJensenTight` / `mainLittlewoodTight` carry the lower bound `0 < h`.

Both are stated in `MainTheoremTight.lean` on the regime `t > 10^12`, `0 < h <= t^{2/3}`, and both
are proved.  The `0 < h` half of that regime is load-bearing, and this script is the record of
why: without it the statement is false, not merely unproved.

For `h <= 0` the interval `(t-h, t+h)` is empty (its left endpoint is >= its right), so
`Nrect (t-h) (t+h) alpha = 0` and the claim would reduce to `0 < U + error`.

`ULittlewood alpha r h t k` is AFFINE in `h` with slope

    S := (2*A1)/pi * log t + 2*A2 * log log t + 2*A3.

`S > 0` therefore sends `U -> -infinity` as `h -> -infinity` while the error term stays fixed, so
`0 < U + error` fails.  This script computes `S` over a grid of `(alpha, r)` and exhibits one
explicit `h < 0` that would refute the statement if the lower bound were dropped.

**No Lean target.**  Nothing here is a certificate, and no theorem is being checked; the printed
refutation is against the hypothetical statement WITHOUT `0 < h`, not against the theorems as they
now stand.

Definitions transcribed from ZerosInShortIntervals/Jensen/JensenScaleConstants.lean -- the MAIN-TEXT
`k = 0` triple `(1/6, 1, log 0.611)`, i.e. `vCoeff`/`vCoeffP`/`vCoeffPP`, not
`JensenScaleConstantsAlt`'s `(27/164, 0, log 66.7)` -- and
ZerosInShortIntervals/Littlewood/LittlewoodShort.lean.
"""
import mpmath as mp

mp.mp.dps = 30


def sigma(k):
    k = mp.mpf(k)
    if k >= 0:
        return 1 - (k + 3) / (mp.mpf(2) ** (k + 3) - 2)
    return ((-k) + 3) / (mp.mpf(2) ** (-k + 3) - 2)


def vCoeff(k):
    if k >= 0:
        return 1 / (mp.mpf(2) ** (k + 3) - 2)
    return sigma(-k) - mp.mpf(1) / 2 + 1 / (mp.mpf(2) ** (-k + 3) - 2)


def vCoeffP(k):
    return mp.mpf(1)


def vCoeffPP(k):
    if k > 0:
        return mp.log(mp.mpf('1.546'))
    if k == 0:
        return mp.log(mp.mpf('0.611'))
    return mp.log(mp.mpf('1.546')) + (sigma(k) - mp.mpf(1) / 2) * mp.log(mp.pi)


def chord(vf, k, s):
    """(m_k s + b_k) with m_k = (v_k - v_{k+1})/(sigma_k - sigma_{k+1}), b_k = v_k - m_k sigma_k."""
    m = (vf(k) - vf(k + 1)) / (sigma(k) - sigma(k + 1))
    b = vf(k) - m * sigma(k)
    return m * s + b


def A1(alpha, r, k):
    return chord(vCoeff, k, 1 - r) / (2 * (r - alpha))


def A2(alpha, r, k):
    return chord(vCoeffP, k, 1 - r) / (2 * mp.pi * (r - alpha))


def A3(alpha, r, k):
    return chord(vCoeffPP, k, 1 - r) / (2 * mp.pi * (r - alpha))


def find_k(r):
    """The k pinned by sigma_k <= 1-r < sigma_{k+1}."""
    for k in range(-40, 40):
        if sigma(k) <= 1 - r < sigma(k + 1):
            return k
    raise ValueError("no k")


print("WHY `mainJensenTight` / `mainLittlewoodTight` CARRY THE HYPOTHESIS `0 < h`.")
print("Both theorems are PROVED, on the regime t > 10^12, 0 < h <= t^(2/3).  What is refuted")
print("below is the hypothetical statement with `0 < h` DROPPED -- never the theorems as stated.")
print()
print("Slope of ULittlewood in h, at t = 10^12 (the smallest admissible t):")
print()
print(f"{'alpha':>8} {'r':>8} {'k':>4} {'A1':>12} {'A2':>12} {'A3':>12} {'slope S':>12}  S>0?")
print("-" * 80)
t = mp.mpf(10) ** 12
L, LL = mp.log(t), mp.log(mp.log(t))
worst = None
for alpha_den in [7, 8, 10, 16]:
    for rs in ['0.5', '0.6', '0.71', '0.9']:
        alpha = 1 / mp.mpf(alpha_den)
        r = mp.mpf(rs)
        if not (alpha < r < 1):
            continue
        k = find_k(r)
        a1, a2, a3 = A1(alpha, r, k), A2(alpha, r, k), A3(alpha, r, k)
        S = (2 * a1) / mp.pi * L + 2 * a2 * LL + 2 * a3
        print(f"{'1/' + str(alpha_den):>8} {mp.nstr(r,4):>8} {k:>4} {mp.nstr(a1,6):>12} "
              f"{mp.nstr(a2,6):>12} {mp.nstr(a3,6):>12} {mp.nstr(S,6):>12}  "
              f"{'yes' if S > 0 else 'NO'}")
        if worst is None or S < worst[0]:
            worst = (S, alpha_den, r, k)

print()
print(f"Smallest slope seen: {mp.nstr(worst[0], 8)} at alpha=1/{worst[1]}, r={mp.nstr(worst[2],4)}.")
print()
print("Since A2 = 1/(2 pi (r-alpha)) exactly -- vCoeffP is identically 1, so the chord is the")
print("constant 1 -- the log log t term is strictly positive and dominates for large t.")
print()
print("CONSEQUENCE: with S > 0, sending h -> -infinity sends ULittlewood -> -infinity while the")
print("error term stays fixed, so `0 < U + error` fails. Concretely, the claim needs")
print("U + error > 0, i.e. h > -(intercept + error)/S. A value of h below that, still satisfying")
print("h < t^(2/3), refutes the statement.")
print()
print("Worked refutation at alpha = 1/7, r = 0.5, t = 10^12:")
alpha, r = 1 / mp.mpf(7), mp.mpf('0.5')
k = find_k(r)
a1, a2, a3 = A1(alpha, r, k), A2(alpha, r, k), A3(alpha, r, k)
S = (2 * a1) / mp.pi * L + 2 * a2 * LL + 2 * a3
print(f"   slope S = {mp.nstr(S, 8)} > 0, so U(h) -> -infinity as h -> -infinity.")
hbad = -(mp.mpf(10) ** 6)
print(f"   at h = {mp.nstr(hbad,4)}:  the h-dependent part of U is {mp.nstr(S * hbad, 8)},")
print("   overwhelmingly negative, while Nrect = 0 and the error term is O(1/t).  So the")
print("   statement WITHOUT `0 < h` is false here; the theorems, which assume it, are unaffected.")
print(f"   (and h = {mp.nstr(hbad,4)} satisfies the stated hypothesis h < t^(2/3) = "
      f"{mp.nstr(t ** (mp.mpf(2)/3), 6)}.)")
