"""Which (v_0, v_0', v_0'') triple reproduces the tex's Table \\ref{tab:crvalues} (Table 2)
at r = 1/2?

Table \\ref{tab:crvalues} (Table 2), r=1/2 row:  c1=0.1467868  c2=0.9393432  c3=3.061478
An unlabelled remark just after Proposition \\ref{prop:jensen-easy} (Proposition 8) separately
quotes c_{1,1/2} = 0.1480612309.  Since c1 is determined by the triple alone, that value and the
table's 0.1467868 at the same r = 1/2 cannot both come from the same triple; the script says which
is which.

MAIN TEXT (Lean's JensenScaleConstants.vCoeff/vCoeffP/vCoeffPP):
    v_0 = 1/6,     v_0' = 1, v_0'' = log(0.611)
REMARK \\ref{rem:altcoefficients} (Remark 7); Lean's JensenScaleConstantsAlt.vCoeffAlt /
vCoeffPAlt / vCoeffPPAlt; and what the Sage table scripts implement:
    v_0 = 27/164,  v_0' = 0, v_0'' = log(66.7)

THE FINDING, still live: the paper's tables are computed with the REMARK triple, while
`Jensen/JensenBounds.lean`'s c1, c2, c3 -- and everything built on them (C1..C3, B1..B4,
A1..A6) -- use the main-text one, so the Lean constants are not the numbers printed in the paper.
That is recorded as the "KNOWN DISCREPANCY" note at the top of `JensenScaleConstants.lean`.  Lean
carries BOTH families: `Jensen/JensenScaleConstantsAlt.lean` defines the Remark's triple and
proves `zeta_piecewise_bound_alt`, discharging the Remark's "also admissible" claim, so the two
rest on the same inputs.  Which is canonical remains an author decision.

**No Lean target.**  A diagnostic that says which triple a given printed number came from; it
certifies nothing and checks no theorem.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, cos, pi, log
mp.dps = 40

def sigma(k):
    if k >= 0:
        return 1 - F(k + 3, 2 ** (k + 3) - 2)
    return F(-k + 3, 2 ** (-k + 3) - 2)

def fl(x):
    return mpf(x.numerator) / mpf(x.denominator) if isinstance(x, F) else mpf(x)

def theta(k, r):
    x = (1 - sigma(k)) / r
    if x > 1:
        return None
    return asin(fl(x))

def generic_c(r, vfun, KMAX=120):
    """c_{i,r} for a coefficient family vfun(k) (returns mpf)."""
    K = next(k for k in range(-KMAX, KMAX) if r >= 1 - sigma(k))
    def m_b(k):
        m = (vfun(k) - vfun(k + 1)) / (fl(sigma(k)) - fl(sigma(k + 1)))
        b = vfun(k) - m * fl(sigma(k))
        return m, b
    rr, thK = fl(r), theta(K, r)
    mK1, bK1 = m_b(K - 1)
    tot = (mK1 + bK1) * (pi / 2 - thK) - mK1 * rr * cos(thK)
    for k in range(K, KMAX):
        tk, tk1 = theta(k, r), theta(k + 1, r)
        if tk is None or tk1 is None:
            break
        mk, bk = m_b(k)
        tot += (mk + bk) * (tk - tk1) + mk * rr * (cos(tk) - cos(tk1))
    return tot

def make(v0, v0p, v0pp):
    def v(k):
        if k == 0: return fl(F(v0)) if not isinstance(v0, str) else mpf(v0)
        if k > 0:  return fl(F(1, 2 ** (k + 3) - 2))
        return fl(sigma(-k) - F(1, 2) + F(1, 2 ** (-k + 3) - 2))
    def vp(k):
        return mpf(v0p) if k == 0 else mpf(1)
    def vpp(k):
        if k > 0:  return log(mpf('1.546'))
        if k == 0: return v0pp
        return log(mpf('1.546')) + (fl(sigma(k)) - mpf('0.5')) * log(pi)
    return v, vp, vpp

r = F(1, 2)
tbl = dict(c1=mpf('0.1467868'), c2=mpf('0.9393432'), c3=mpf('3.061478'))
print(f"Table 1 (r=1/2):  c1={tbl['c1']}  c2={tbl['c2']}  c3={tbl['c3']}")
print(f"tex line 346 separately quotes c_1 = 0.1480612309\n")

for label, (v0, v0p, v0pp) in [
    ("MAIN TEXT / LEAN  (1/6, 1, log 0.611)", (F(1, 6), 1, log(mpf('0.611')))),
    ("REMARK    / SAGE  (27/164, 0, log 66.7)", (F(27, 164), 0, log(mpf('66.7')))),
]:
    v, vp, vpp = make(v0, v0p, v0pp)
    got = dict(c1=generic_c(r, v), c2=generic_c(r, vp), c3=generic_c(r, vpp))
    print(label)
    for nm in ("c1", "c2", "c3"):
        d = got[nm] - tbl[nm]
        flag = "MATCH" if abs(d) < mpf('1e-6') else "     "
        print(f"   {nm} = {mp.nstr(got[nm], 10):<16} table={tbl[nm]}  diff={mp.nstr(d, 5):<14}{flag}")
    print()
