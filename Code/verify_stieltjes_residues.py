"""Check the exact closing arithmetic for the two gamma_1 consumers in Jensen/JensenBounds.

Those are `stieltjes_combo_pos` (0 < gamma^2 + 2 gamma_1) and `stieltjes_combo_bound`
(exp(2/3)(gamma^2 + 2 gamma_1)/8 <= (pi-2) gamma / (2 pi)).  Each reduces to a finite numeric
residue about `Definitions.stieltjesSeq` / `Definitions.stieltjesSeqMid`.  This script confirms
(a) each residue is true with margin, and (b) each residue really does close its consumer using
ONLY facts available in this Mathlib:

    1/2 < gamma < 2/3          one_half_lt_eulerMascheroniConstant, ..._lt_two_thirds
    3.14 < pi < 3.15           Real.pi_gt_d2, Real.pi_lt_d2
    0.6931471803 < log 2 < 0.6931471808   Real.log_two_gt_d9, Real.log_two_lt_d9
    log x <= x - 1             Real.log_le_sub_one_of_pos

The first block is the route Lean takes for `stieltjes_combo_pos`:
`Definitions.neg_one_eighth_lt_stieltjesSeqMid_five` and
`Definitions.neg_one_eighth_lt_stieltjesConstant1` give gamma_1 > -1/8 from stieltjesSeqMid 5
using exactly the cheap log 3 / log 5 bounds checked here.

The `stieltjesSeq m <= U` candidates in the second block are only what `stieltjes_combo_bound`
needs, which is weak.  Anywhere a sharp upper bound on gamma_1 is wanted -- notably
`Background/LogDerivZetaLaurent.stieltjesConstant1_upper_bound` (gamma_1 <= -0.0724, feeding
`stieltjes_combo_upper_bound`) -- Lean uses the Euler-Maclaurin bracket
`Definitions.stieltjesSeqHi` at m = 16 instead, which is far stronger than any of these and
costs only the logarithms of 2, 3, 5, 7, 11, 13.
"""
import mpmath as mp

mp.mp.dps = 40

LOG2_LO = mp.mpf('0.6931471803')
LOG2_HI = mp.mpf('0.6931471808')
PI_LO = mp.mpf('3.14')


def a(m):
    return mp.fsum(mp.log(k) / k for k in range(1, m + 1)) - mp.log(m) ** 2 / 2


def mid(m):
    return a(m) - mp.log(m) / m / 2


print("=" * 72)
print("stieltjes_combo_pos :  0 < gamma^2 + 2*gamma_1")
print("=" * 72)
# Worst case gamma -> 1/2, so it suffices that  2*gamma_1 > -1/4,  i.e. gamma_1 > -1/8.
print(f"  needs   gamma_1 > -1/8 = -0.125")
print(f"  bracket stieltjesSeqMid 5 = {mp.nstr(mid(5), 10)}   margin {mp.nstr(mid(5)+mp.mpf(1)/8, 6)}")

# Now: can we PROVE  -1/8 < stieltjesSeqMid 5  from the cheap log bounds?
# stieltjesSeqMid 5 = log2 + log3/3 + log5/10 - (log5)^2/2      (log4/4 = log2/2)
exact = mp.log(2) + mp.log(3) / 3 + mp.log(5) / 10 - mp.log(5) ** 2 / 2
print(f"\n  identity check: log2 + log3/3 + log5/10 - (log5)^2/2 = {mp.nstr(exact, 10)}")
assert abs(exact - mid(5)) < mp.mpf('1e-30'), "identity for stieltjesSeqMid 5 is wrong"
print("  identity matches stieltjesSeqMid 5  [OK]")

# log 3 >= log 2 + 1/3      (log(2/3) <= 2/3 - 1  =>  log(3/2) >= 1/3)
log3_lo = LOG2_LO + mp.mpf(1) / 3
# log 5 <= 2 log 2 + 1/8 + 1/9   (5/4 = (9/8)(10/9); log t <= t-1 on each factor)
log5_hi = 2 * LOG2_HI + mp.mpf(1) / 8 + mp.mpf(1) / 9
print(f"\n  cheap bounds:  log3 > {mp.nstr(log3_lo,10)} (true {mp.nstr(mp.log(3),10)})")
print(f"                 log5 < {mp.nstr(log5_hi,10)} (true {mp.nstr(mp.log(5),10)})")

# c/10 - c^2/2 is decreasing for c > 1/10, so the upper bound on log5 is the worst case.
lower = LOG2_LO + log3_lo / 3 + log5_hi / 10 - log5_hi ** 2 / 2
print(f"\n  => stieltjesSeqMid 5 > {mp.nstr(lower, 10)}")
print(f"     vs required          -0.125          "
      f"{'PROVES IT, margin ' + mp.nstr(lower + mp.mpf(1)/8, 6) if lower > -mp.mpf(1)/8 else 'FAILS'}")

print()
print("=" * 72)
print("stieltjes_combo_bound :  exp(2/3)(g^2+2g1)/8 <= (pi-2) g /(2 pi)")
print("=" * 72)
# Use exp(2/3) < 2  (cheap: 2/3 < log 2) and (pi-2)/(2pi) = 1/2 - 1/pi >= 1/2 - 1/3.14.
rhs_coeff = mp.mpf(1) / 2 - 1 / PI_LO
print(f"  exp(2/3) = {mp.nstr(mp.exp(mp.mpf(2)/3), 8)} < 2   (since 2/3 < log 2 = {mp.nstr(mp.log(2),8)})")
print(f"  (pi-2)/(2pi) = 1/2 - 1/pi >= 1/2 - 1/3.14 = {mp.nstr(rhs_coeff, 10)}")
# Suffices: 2*(g^2 + 2U)/8 <= rhs_coeff * g   for all g in [1/2, 2/3], i.e.
#           g^2 - 4*rhs_coeff*g + 2U <= 0.  Concave-up, so worst at an endpoint.
print("\n  suffices:  g^2 - 4*(pi-2)/(2pi)*g + 2U <= 0 for g in [1/2, 2/3];")
print("  the quadratic is convex, so it is worst at an endpoint:")
for g in [mp.mpf(1) / 2, mp.mpf(2) / 3]:
    umax = -(g ** 2 - 4 * rhs_coeff * g) / 2
    print(f"     g = {mp.nstr(g,6):>10}  =>  U <= {mp.nstr(umax, 8)}")
umax = min(-(g ** 2 - 4 * rhs_coeff * g) / 2 for g in [mp.mpf(1) / 2, mp.mpf(2) / 3])
print(f"  binding requirement:  gamma_1 <= U with U <= {mp.nstr(umax, 8)}")

print("\n  candidate residues  stieltjesSeq m <= U:")
for m, U in [(15, mp.mpf(1) / 50), (20, mp.mpf(1) / 100), (20, mp.mpf(1) / 200),
             (25, mp.mpf(1) / 200)]:
    ok_res = a(m) <= U
    ok_close = U <= umax
    print(f"     m={m:<3} U=1/{int(1/U):<4} a_m={mp.nstr(a(m),8):>12}  "
          f"residue {'true' if ok_res else 'FALSE'} (margin {mp.nstr(U-a(m),4)}), "
          f"closes {'yes' if ok_close else 'NO'} (margin {mp.nstr(umax-U,4)})")
