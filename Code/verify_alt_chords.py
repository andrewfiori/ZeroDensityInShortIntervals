"""Exact-rational check of `Jensen.JensenScaleConstantsAlt`'s closed-form chord constants.

Conventions (tex Equation `\\ref{eq:sigmak}` (Equation 4), Equation `\\ref{eq:mk}` (Equation 5)):
    sigma k  = 1 - (k+3)/(2^(k+3)-2)          for k >= 0
    sigma k  = ((-k)+3)/(2^(-k+3)-2)          for k <  0
    vCoeff k = 1/(2^(k+3)-2)                  for k >= 0   [main text]
    vCoeff k = sigma(-k) - 1/2 + 1/(2^(-k+3)-2)  for k < 0
    m_k = (v_k - v_{k+1})/(sigma_k - sigma_{k+1});  b_k = v_k - m_k*sigma_k
Alt family: the triple of `Remark \\ref{rem:altcoefficients}` (Remark 7), namely
v_0 = 27/164, v_0' = 0, v_0'' = log 66.7 (the Patel-Yang sub-Weyl bound).  Only the v and v'
members are exercised here: v_0'' is transcendental, so it has no place in an exact check.

Thirteen closed forms are compared against the values the Lean definitions give, followed by the
two mirror-chord identities used in the k = -1 branch of `zeta_piecewise_bound_alt`.  All
arithmetic is `fractions.Fraction`, so every comparison is exact; the Lean side is proved, so
this is an independent re-check and not a certificate of any hypothesis-class field.
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

def vAlt(k):
    return F(27, 164) if k == 0 else vCoeff(k)

def vPAlt(k):
    return F(0) if k == 0 else F(1)

def m(v, k):
    return (v(k) - v(k + 1)) / (sigma(k) - sigma(k + 1))

def b(v, k):
    return v(k) - m(v, k) * sigma(k)

checks = [
    ("sigma 0",            sigma(0),        F(1, 2)),
    ("sigma 1",            sigma(1),        F(5, 7)),
    ("sigma (-1)",         sigma(-1),       F(2, 7)),
    ("vCoeff 1",           vCoeff(1),       F(1, 14)),
    ("vCoeff (-1)",        vCoeff(-1),      F(2, 7)),
    ("mCoeffAlt 0",        m(vAlt, 0),      -F(107, 246)),
    ("bCoeffAlt 0",        b(vAlt, 0),      F(47, 123)),
    ("mCoeffPAlt 0",       m(vPAlt, 0),     F(14, 3)),
    ("bCoeffPAlt 0",       b(vPAlt, 0),     -F(7, 3)),
    ("mCoeffAlt (-1)",     m(vAlt, -1),     -F(139, 246)),
    ("bCoeffAlt (-1)",     b(vAlt, -1),     F(55, 123)),
    ("mCoeffPAlt (-1)",    m(vPAlt, -1),    -F(14, 3)),
    ("bCoeffPAlt (-1)",    b(vPAlt, -1),    F(7, 3)),
]

print(f"{'quantity':<20} {'computed':>16} {'Lean claims':>16}   ok")
bad = 0
for name, got, want in checks:
    ok = got == want
    bad += (not ok)
    print(f"{name:<20} {str(got):>16} {str(want):>16}   {'OK' if ok else 'MISMATCH'}")

# The mirror-chord identity used in the k = -1 branch of zeta_piecewise_bound_alt:
#   mAlt(-1)*s + bAlt(-1) = (mAlt(0)*(1-s) + bAlt(0)) + (1/2 - s)
print("\nmirror chord identity  mAlt(-1)s + bAlt(-1) == mAlt(0)(1-s) + bAlt(0) + (1/2-s):")
for s in [F(2, 7), F(1, 3), F(2, 5), F(1, 2)]:
    lhs = m(vAlt, -1) * s + b(vAlt, -1)
    rhs = (m(vAlt, 0) * (1 - s) + b(vAlt, 0)) + (F(1, 2) - s)
    ok = lhs == rhs
    bad += (not ok)
    print(f"  s={str(s):>5}: {str(lhs):>14} vs {str(rhs):>14}  {'OK' if ok else 'MISMATCH'}")

print("\nmirror chord identity (log log):  mPAlt(-1)s + bPAlt(-1) == mPAlt(0)(1-s) + bPAlt(0):")
for s in [F(2, 7), F(1, 3), F(1, 2)]:
    lhs = m(vPAlt, -1) * s + b(vPAlt, -1)
    rhs = m(vPAlt, 0) * (1 - s) + b(vPAlt, 0)
    ok = lhs == rhs
    bad += (not ok)
    print(f"  s={str(s):>5}: {str(lhs):>14} vs {str(rhs):>14}  {'OK' if ok else 'MISMATCH'}")

print("\nFAILURES:", bad)
