"""Which v_0 convention reproduces the tex's own c_{1,1/2} = 0.1480612309?

That number is quoted in an unlabelled remark just after Proposition \\ref{prop:jensen-easy}
(Proposition 8), and it differs from the c1 = 0.1467868 printed in Table \\ref{tab:crvalues}
(Table 2) for the same r = 1/2 -- so the two cannot both come from the same triple.

MAIN TEXT (what `JensenScaleConstants.vCoeff` implements): v_0 = 1/(2^3-2) = 1/6
REMARK \\ref{rem:altcoefficients} (Remark 7) -- what `JensenScaleConstantsAlt.vCoeffAlt` and the
Sage table scripts implement:                              v_0 = 27/164

c1 depends only on v (not v', v''), so this isolates the question.  The narrow companion of
`verify_v0_triple_vs_tables.py`, which runs the same comparison for all three of c1, c2, c3
against the table row; see that file for the full statement of the discrepancy.

sigma/v/m/b are exact rationals; only arcsin/cos go to floating point (40 digits of mpmath).

**No Lean target.**  A diagnostic; it certifies nothing.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, cos, pi
mp.dps = 40

def sigma(k):
    if k >= 0:
        return 1 - F(k + 3, 2 ** (k + 3) - 2)
    return F(-k + 3, 2 ** (-k + 3) - 2)

def make_v(v0):
    def v(k):
        if k == 0:
            return F(v0)
        if k > 0:
            return F(1, 2 ** (k + 3) - 2)
        return sigma(-k) - F(1, 2) + F(1, 2 ** (-k + 3) - 2)
    return v

def m_b(v, k):
    m = (v(k) - v(k + 1)) / (sigma(k) - sigma(k + 1))
    b = v(k) - m * sigma(k)
    return m, b

def theta(k, r):
    x = (1 - sigma(k)) / r
    if x > 1:
        return None
    return asin(mpf(x.numerator) / mpf(x.denominator))

def c1(r, v, KMAX=120):
    K = None
    for k in range(-KMAX, KMAX):
        if r >= 1 - sigma(k):
            K = k
            break
    assert K is not None
    thK = theta(K, r)
    mK1, bK1 = m_b(v, K - 1)
    rr = mpf(r.numerator) / mpf(r.denominator)
    tot = (mpf((mK1 + bK1).numerator) / mpf((mK1 + bK1).denominator)) * (pi / 2 - thK) \
        - (mpf(mK1.numerator) / mpf(mK1.denominator)) * rr * cos(thK)
    for k in range(K, KMAX):
        tk, tk1 = theta(k, r), theta(k + 1, r)
        if tk is None or tk1 is None:
            break
        mk, bk = m_b(v, k)
        mkf = mpf(mk.numerator) / mpf(mk.denominator)
        mbf = mpf((mk + bk).numerator) / mpf((mk + bk).denominator)
        tot += mbf * (tk - tk1) + mkf * rr * (cos(tk) - cos(tk1))
    return tot

target = mpf('0.1480612309')
r = F(1, 2)
print(f"tex Remark (line 346) states  c_{{1,1/2}} = {target}\n")
for label, v0 in [("MAIN TEXT v_0 = 1/6    (Lean's vCoeff)", F(1, 6)),
                  ("REMARK    v_0 = 27/164 (sage's vCoeff)", F(27, 164))]:
    val = c1(r, make_v(v0))
    print(f"{label}:  c1(1/2) = {mp.nstr(val, 12)}   diff = {mp.nstr(val - target, 6)}")
