"""Is the antitone step 2*a_{n+1} <= a_n actually STRICT for n >= 2?

Independent exact-rational check of the arithmetic inside the proved theorem
`Background/LogDerivZetaLaurent.logDerivZetaCoeff_two_mul_succ_lt`, whose non-strict companion
is `logDerivZetaCoeff_two_mul_succ_le`.  Strictness is needed because claim 2 of
Lemma \\ref{lemma:logderzetabound} (Lemma 38) asserts `<` while Mathlib's alternating-series
lemmas only deliver `<=`; the gap is closed by one strictly decreasing tail step.

Claim 1 (`logDerivZetaCoeff_bound`) gives |a_n - M_n| <= 0.6 * 7^{-n} with
M_n = 3^{-n-1} + 5^{-n-1} + 7^{-n-1}.  Writing n = m+2 and A = 3^{-m}, B = 5^{-m}, C = 7^{-m}
(so 0 < C <= B <= A):

    a_{m+3} <= A/81  + B/625 + C/2401 + 0.6*C/343       (upper)
    a_{m+2} >= A/27  + B/125 + C/343  - 0.6*C/49        (lower)

so  a_{m+2} - 2*a_{m+3}  >=  (1/27 - 2/81)A + (1/125 - 2/625)B
                             + (1/343 - 0.6/49 - 2/2401 - 1.2/343)C
                          =  (1/81)A + (3/625)B - (164/12005)C.

This script checks that combination is strictly positive using only C <= A, C <= B, C > 0 --
exactly the facts (i3, i5, hw) the non-strict Lean proof already has in context.  Every
quantity below is an exact `Fraction`; the floats are printed for readability only.

Strictness is genuinely unavailable at n = 0, 1: there claim 1's 0.6*7^{-n} error term swamps
the margin, and the Lean falls back on the exact values a_0 = gamma (`logDerivZetaCoeff_zero`)
and a_1 = gamma^2 + 2*gamma_1 (`logDerivZetaCoeff_one`).  Claim 2 only ever needs the strict
step at indices >= 2.
"""
from fractions import Fraction as F

cA = F(1, 27) - F(2, 81)
cB = F(1, 125) - F(2, 625)
cC = F(1, 343) - F(6, 10) / 49 - F(2, 2401) - (F(12, 10)) / 343

print(f"coefficient of A : {cA}  = {float(cA):.8f}")
print(f"coefficient of B : {cB}  = {float(cB):.8f}")
print(f"coefficient of C : {cC}  = {float(cC):.8f}")
print()
print("cC is negative, so bound A >= C and B >= C from below:")
worst = cA + cB + cC
print(f"   cA + cB + cC = {worst} = {float(worst):.8f}")
print(f"   strictly positive: {worst > 0}")
print()
print("So a_{m+2} - 2 a_{m+3} >= (cA + cB + cC) * C > 0 for every m >= 0,")
print("i.e. 2*a_{n+1} < a_n strictly for every n >= 2, from claim 1 alone.")
print()
print("Direct sanity check with the true M_n values (no error term), a few n:")
print(f"{'n':>4} {'M_n':>14} {'2*M_{n+1}':>14} {'margin':>14}")
for n in range(2, 9):
    Mn = F(1, 3 ** (n + 1)) + F(1, 5 ** (n + 1)) + F(1, 7 ** (n + 1))
    Mn1 = F(1, 3 ** (n + 2)) + F(1, 5 ** (n + 2)) + F(1, 7 ** (n + 2))
    print(f"{n:>4} {float(Mn):>14.8f} {float(2*Mn1):>14.8f} {float(Mn - 2*Mn1):>14.8f}")
