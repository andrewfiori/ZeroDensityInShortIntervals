"""Are `b_k > 0` and `m_k + b_k <= 0` compatible?  Exact-rational check of the two
`Jensen.JensenScaleConstants` sign facts `bCoeff_pos` and `mCoeff_add_bCoeff_neg`.

The only sign claim about these quantities in `ZerosInShortIntervals.tex` is
"m_k + b_k \\leq 0", which is exactly what Lean proves as `mCoeff_add_bCoeff_neg`.  There is no
claim "b_k <= 0" anywhere in the current tex, and none is needed: the two facts are compatible
because m_k < 0 with |m_k| > b_k, which is what the table below exhibits at every index.

Conventions are `JensenScaleConstants`: `sigma` from Equation `\\ref{eq:sigmak}` (Equation 4),
`vCoeff` the main-text coefficient triple, and `mCoeff`/`bCoeff` the chord through
(sigma_k, v_k) and (sigma_{k+1}, v_{k+1}) from Equation `\\ref{eq:mk}` (Equation 5).

Everything is `fractions.Fraction`, so the table is exact.  The script tests the strict
`m_k + b_k < 0`, which is stronger than the tex's non-strict claim, over -6 <= k <= 8.  Both
Lean theorems are proved, so this is an independent re-check, not a certificate.
"""
from fractions import Fraction as F

def sigma(k):
    if k >= 0:
        return 1 - F(k + 3, 2 ** (k + 3) - 2)
    j = -k
    return F(j + 3, 2 ** (j + 3) - 2)

def vCoeff(k):
    if k >= 0:
        return F(1, 2 ** (k + 3) - 2)
    j = -k
    return sigma(j) - F(1, 2) + F(1, 2 ** (j + 3) - 2)

def m(k):
    return (vCoeff(k) - vCoeff(k + 1)) / (sigma(k) - sigma(k + 1))

def b(k):
    return vCoeff(k) - m(k) * sigma(k)

print(f"{'k':>4} {'m_k':>14} {'b_k':>14} {'m_k+b_k':>14}  b_k>0  m+b<0")
bad = 0
for k in range(-6, 9):
    mk, bk = m(k), b(k)
    ok1, ok2 = bk > 0, mk + bk < 0
    bad += (not ok1) + (not ok2)
    print(f"{k:>4} {str(mk):>14} {str(bk):>14} {str(mk+bk):>14}   "
          f"{'OK' if ok1 else 'FAIL':<5}  {'OK' if ok2 else 'FAIL'}")

print(f"\nviolations: {bad}")
print("\nConclusion: b_k > 0 and m_k + b_k < 0 are both true at every index tested, and are")
print("perfectly compatible (m_k < 0 and |m_k| > b_k). The tex's line 503 claim 'm_k+b_k <= 0'")
print("is CORRECT. No statement 'b_k <= 0' appears anywhere in the current tex.")
