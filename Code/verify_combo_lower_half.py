"""Certify the LOWER half of stieltjes_combo_numeric_bounds:  0.15 <= gamma^2 + 2 gamma_1.

That is the proved theorem `Background/LogDerivZetaLaurent.stieltjes_combo_lower_bound`; this
script is the exact-rational certification of its closing arithmetic.  It does NOT use floating
point for the certificate: every bound it chains is an exact `Fraction`, and every inequality it
checks is an exact rational comparison.  mpmath is used only to print the true values for
orientation.

The chain mirrors, step for step, what the Lean proof does:

  gamma   >= eulerMascheroniSeq 31 = harmonic 31 - log 32 = harmonic 31 - 5 log 2
              (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant, Real.log_two_lt_d9)
  gamma_1 >= stieltjesSeqMid 5 = log 2 + (log 3)/3 + (log 5)/10 - (log 5)^2/2
              (Definitions.stieltjesSeqMid_le_stieltjesConstant1 at m = 5,
               Definitions.stieltjesSeqMid_five_eq)

with log 3 and log 5 obtained from log 2 plus a Taylor bound on log(1 - x):

  Real.abs_log_sub_add_sum_range_le :
      |(sum_{i<n} x^(i+1)/(i+1)) + log (1 - x)| <= |x|^(n+1) / (1 - |x|)

  log 3 = log 2 + log (3/2)   via x = -1/2,  n = 12   (error <= (1/2)^12)
  log 5 = 2 log 2 + log (5/4) via x = -1/4,  n = 6    (error <= (4/3)(1/4)^7)

The previously-reported route (gamma >= harmonic 20 - log 21 with log 21 <= 3.05029, from a
`log t <= t - 1` telescoping) is ALSO evaluated below, and is shown to NOT close: the residual
margin is negative once the only proved lower bound for gamma_1 (-1/8) is used, and is razor thin
even against the exact value of stieltjesSeqMid 5.
"""

from fractions import Fraction as F

import mpmath as mp

mp.mp.dps = 40

TRUE_GAMMA = mp.euler
TRUE_GAMMA1 = mp.mpf('-0.0728158454836767248605863758749013191377')
TRUE_COMBO = TRUE_GAMMA ** 2 + 2 * TRUE_GAMMA1

# Mathlib: Real.log_two_gt_d9 / Real.log_two_lt_d9
LOG2_LO = F('0.6931471803')
LOG2_HI = F('0.6931471808')


def harmonic(n):
    return sum((F(1, k) for k in range(1, n + 1)), F(0))


def taylor_log_bounds(x, n):
    """Certified (lo, hi) for log(1 - x) from Real.abs_log_sub_add_sum_range_le."""
    assert abs(x) < 1
    s = sum((x ** (i + 1) / F(i + 1) for i in range(n)), F(0))
    err = abs(x) ** (n + 1) / (1 - abs(x))
    return (-s - err, -s + err)


print(f"true gamma            = {mp.nstr(TRUE_GAMMA, 15)}")
print(f"true gamma_1          = {mp.nstr(TRUE_GAMMA1, 15)}")
print(f"true gamma^2+2gamma_1 = {mp.nstr(TRUE_COMBO, 15)}   (target >= 0.15)")
print(f"  slack above 0.15    = {mp.nstr(TRUE_COMBO - mp.mpf('0.15'), 6)}\n")

# ---------------------------------------------------------------- log 3, log 5

lo32, hi32 = taylor_log_bounds(F(-1, 2), 12)
lo54, hi54 = taylor_log_bounds(F(-1, 4), 6)
print("Taylor brackets (exact rationals, printed as floats):")
print(f"  log(3/2) in [{float(lo32):.10f}, {float(hi32):.10f}]  true {float(mp.log(1.5)):.10f}")
print(f"  log(5/4) in [{float(lo54):.10f}, {float(hi54):.10f}]  true {float(mp.log(1.25)):.10f}")

LOG3_LO_TARGET = F('1.098')      # the constant `log_three_lower_bound` states
LOG5_HI_TARGET = F('1.61')       # the constant `log_five_upper_bound` states

log3_lo = LOG2_LO + lo32
log5_hi = 2 * LOG2_HI + hi54
print(f"  => log 3 >= {float(log3_lo):.10f}; stating {float(LOG3_LO_TARGET)}  "
      f"OK={log3_lo >= LOG3_LO_TARGET}")
print(f"  => log 5 <= {float(log5_hi):.10f}; stating {float(LOG5_HI_TARGET)}  "
      f"OK={log5_hi <= LOG5_HI_TARGET}\n")

# ------------------------------------------------- gamma_1 >= stieltjesSeqMid 5
# stieltjesSeqMid 5 = log 2 + (log 3)/3 + (log 5)/10 - (log 5)^2/2.
# c |-> c/10 - c^2/2 is decreasing for c >= 1/10, so c <= LOG5_HI_TARGET is the worst case.
c = LOG5_HI_TARGET
mid5_lo = LOG2_LO + LOG3_LO_TARGET / 3 + c / 10 - c ** 2 / 2
mid5_true = (mp.log(2) + mp.log(3) / 3 + mp.log(5) / 10 - mp.log(5) ** 2 / 2)
G1_LO_TARGET = F('-0.076')        # the constant `stieltjesConstant1_lower_bound` states
print(f"stieltjesSeqMid 5 >= {float(mid5_lo):.10f}   true {float(mid5_true):.10f}")
print(f"  stating gamma_1 >= {float(G1_LO_TARGET)}   OK={mid5_lo >= G1_LO_TARGET}\n")

# ------------------------------------------------------------ gamma from n = 31
# n = 31 is chosen so that n + 1 = 32 is a power of two: log 32 = 5 log 2 exactly, so the only
# transcendental input is Mathlib's nine-digit log 2 and no bound on log 21 is needed at all.
H31 = harmonic(31)
gamma_lo = H31 - 5 * LOG2_HI              # log 32 = 5 log 2
GAMMA_LO_TARGET = F('0.5615')             # the constant `eulerMascheroniConstant_lower_bound` states
print(f"harmonic 31 = {H31}  = {float(H31):.10f}")
true_seq31 = mp.mpf(H31.numerator) / H31.denominator - mp.log(32)
print(f"eulerMascheroniSeq 31 >= {float(gamma_lo):.10f}   true seq {float(true_seq31):.10f}")
print(f"  stating gamma >= {float(GAMMA_LO_TARGET)}   OK={gamma_lo >= GAMMA_LO_TARGET}\n")

# ------------------------------------------------------------------- the close
combo_lo = GAMMA_LO_TARGET ** 2 + 2 * G1_LO_TARGET
print(f"CLOSING: gamma^2 + 2 gamma_1 >= {GAMMA_LO_TARGET}^2 + 2*({G1_LO_TARGET})"
      f" = {float(combo_lo):.10f}")
print(f"  >= 0.15 ?  {combo_lo >= F('0.15')}    margin = {float(combo_lo - F('0.15')):.10f}\n")

# ---------------------------------------------- the previously reported route
print("=" * 74)
print("Cross-check of the reported 'one bound away' route (n = 20, log 21 <= 3.05029):")
H20 = harmonic(20)
for name, C in [("claimed 3.05029", F('3.05029')),
                ("telescoping 17/16..21/20", sum((F(1, k) for k in range(16, 21)), F(0))
                 + 4 * LOG2_HI)]:
    g = H20 - C
    print(f"  log 21 <= {name}: -> gamma >= {float(g):.8f}, gamma^2 >= {float(g ** 2):.8f}")
    for g1name, g1 in [("proved -1/8", F(-1, 8)),
                       ("exact stieltjesSeqMid 5", F(mp.nstr(mid5_true, 20)))]:
        v = g ** 2 + 2 * g1
        print(f"      with gamma_1 >= {g1name:<24s}: {float(v):.8f}  "
              f"{'OK' if v >= F('0.15') else 'FAILS'} (margin {float(v - F('0.15')):+.6f})")
print()

# -------------------- cost of the UPPER half by the CRUDE bracket, for the record
# This block prices a route the Lean did NOT take.  With the crude upper bracket
# gamma_1 <= stieltjesSeq m (error (log m)/(2m)) the 0.0125 slack forces m ~ 800 and
# n ~ 140-200, i.e. certified bounds on the logarithms of all 139 primes below 800.
# `Background/LogDerivZetaLaurent.stieltjes_combo_upper_bound` is instead proved from the
# Euler-Maclaurin bracket `Definitions.stieltjesSeqHi` (error O((log m)/m^3)) at m = 16, via
# `stieltjesConstant1_upper_bound` (gamma_1 <= -0.0724) and `eulerMascheroniConstant_upper_bound`
# (gamma <= 0.5851 at n = 64), needing only log 2, 3, 5, 7, 11, 13.  So what follows is the cost
# of the rejected alternative, not of the implemented proof; the "(still a sorry)" wording in the
# printed output below is stale.
print("=" * 74)
print("Cost of the UPPER half  gamma^2 + 2 gamma_1 <= 0.20  (still a sorry):")
print("  gamma  <= eulerMascheroniSeq' n = harmonic n - log n")
print("  gamma_1 <= stieltjesSeq m       = sum_{k<=m} (log k)/k - (log m)^2/2")


def em_hi(n):
    return mp.mpf(harmonic(n).numerator) / harmonic(n).denominator - mp.log(n)


def g1_hi(m):
    return mp.fsum(mp.log(k) / k for k in range(1, m + 1)) - mp.log(m) ** 2 / 2


def primes_below(x):
    return sum(1 for k in range(2, x + 1)
               if all(k % d for d in range(2, int(k ** 0.5) + 1)))


for m in [400, 800, 1600, 3200]:
    n = None
    for cand in range(10, 4001):
        if em_hi(cand) ** 2 + 2 * g1_hi(m) <= mp.mpf('0.20'):
            n = cand
            break
    print(f"  m = {m:5d}  (pi(m) = {primes_below(m):3d} logarithms)  needs n >= "
          f"{n if n else '> 4000'}")
print("  -> the cheapest balanced point is around n = 140-200, m = 800, i.e. the logs of the")
print("     139 primes below 800; slack against the true value is only 0.0125.")
print()
print("Conclusion: the reported route does not close.  With the only proved gamma_1 bound")
print("(-1/8) it misses by ~0.09; even with the exact value of stieltjesSeqMid 5 the margin")
print("against log 21 <= 3.05029 is essentially zero.  The fix is TWO-sided: a sharper")
print("gamma_1 lower bound (better log 3 / log 5) AND a sharper gamma lower bound; taking")
print("n = 31 makes log 32 = 5 log 2 so no log-21 bound is needed at all.")
