#!/usr/bin/env python3
r"""
INDEPENDENT mpmath spot-check of the paper's tables against the Lean DEFINITIONS of the constants,
recomputed from scratch with mpmath quadrature.  The point of the file is the independence: it
shares no code with the Sage table scripts -- no arb, and no reuse of their
`coef`/`c4r`/`c5r`/`Phi` machinery -- so a transcription error common to those would show up here.

**No Lean target.** Nothing here certifies a hypothesis-class field; it is a second, disjoint
implementation of the constants the paper tabulates.

Tables in `ZerosInShortIntervals.tex` use the "alternate" chord triple
(v_0, v_0', v_0'') = (27/164, 0, log 66.7) of Remark \ref{rem:altcoefficients} (Remark 7), which is
Lean's `JensenScaleConstantsAlt` (`vCoeffAlt`, `vCoeffPAlt`, `vCoeffPPAlt`); the main-text triple
(1/6, 1, log 0.611) is Lean's `vCoeff`/`vCoeffP`/`vCoeffPP` (JensenScaleConstants).  Both are
computed, and the table is compared against the Alt values.

Checked rows (all rounded UP to 7 significant figures in the tex):
  \ref{tab:crvalues} (Table 2)  r = 1/2 : c1=0.1467868 c2=0.9393432 c3=3.061478 c4=0.7795712 c5=1.126439
  \ref{tab:littlewoodshort} (Table 7)  alpha = 1/8, r = 1/2 : A1=0.2195122 A2=0 A3=1.782623 A4=0.1957157 A5=1.732003 A6=9.128594 (k=0)
  \ref{tab:rectangularjensen} (Table 5) alpha = 1/7, r = 0.5647100 : B1=0.2457053 B2=0.3900919 B3=1.450119 B4=6.518765, ahat=0.5463417
  C2 tables (Code/C2_tables_raw.tex -> Code/C2_tables.tex, the paper's Tables 8-11):
      Littlewood alpha=1/7, r=0.5000553, h0=100, t0=10^200: C2^L=0.4981758;
      Jensen     alpha=1/16, r=0.5264389, h0=100, t0=10^100: C2^J=0.4579894.

NUMBERING NOTE: the numbers in the banners below are the paper's current ones, read from its
`.aux` -- `tab:crvalues` is Table 2, `tab:rectangularjensen` Table 5, `tab:crvalues3` Table 6,
`tab:littlewoodshort` Table 7, and the four C_2 tables are Tables 8-11.  The `\ref` labels are
the stable identifier; re-read the `.aux` if a front-matter environment is ever inserted.

Lean definitions used (JensenScaleConstants / JensenBounds / RectangularBounds / LittlewoodShort / MainCorollary):
  c1 r = (m_{K-1}+b_{K-1})(pi/2 - theta_K) - m_{K-1} r cos theta_K
         + sum_{j>=0} [ (m_{K+j}+b_{K+j})(theta_{K+j} - theta_{K+j+1}) + m_{K+j} r (cos theta_{K+j} - cos theta_{K+j+1}) ]
       with theta_k = arcsin((1-sigma_k)/r), K = Kidx r = min{k : 1 - sigma_k <= r};  c2, c3 likewise with primed data
  c4 r = (1/2) log zeta(1+r) - (r/pi) int_0^1 Re(zeta'/zeta)(1+ru) arcsin u du
  c5 r = Phi(1+r) + (2r/pi) int_0^1 log zeta(1+ru) arcsin u du,   Phi(s) = int_s^oo log zeta(x) dx  (real s>1)
  A1 = (m_k(1-r)+b_k)/(2(r-alpha)), A2 = (m_k'(1-r)+b_k')/(2 pi (r-alpha)), A3 = (m_k''(1-r)+b_k'')/(2 pi (r-alpha)),
  A4 = c1 r/(r-alpha), A5 = (c2 r + pi r)/(pi(r-alpha)),
  A6 = (c3 r + c4 pi r + pi log(29.388) r + Phi(1+eta r) + (1+eta) r log zeta(1+eta r))/(pi (r-alpha)),  1+eta+log eta = 0
  rectDenom r a = 2 r sqrt(1-(a/r)^2) - 2 a arctan(sqrt((r/a)^2-1)),  B1 = c1/D, B2 = c2/(pi D), B3 = c3/(pi D), B4 = (2 Phi(1) + c5)/D
  C2denom, C2Jensen, C2Littlewood as in MainCorollary.lean (see indep_mpmath_constants.py [I]).

Run with:  python3 Code/indep_mpmath_tables_spotcheck.py
"""
import mpmath as mp
from fractions import Fraction as F

mp.mp.dps = 50


def q(x):
    return mp.mpf(x.numerator) / mp.mpf(x.denominator) if isinstance(x, F) else mp.mpf(x)


def sigma(k):
    if k >= 0:
        return 1 - F(k + 3, 2 ** (k + 3) - 2)
    return F(-k + 3, 2 ** (-k + 3) - 2)


def make_family(alt):
    LOG1546 = mp.log(mp.mpf('1.546'))

    def v(k):
        if k == 0:
            return q(F(27, 164)) if alt else q(F(1, 6))
        if k > 0:
            return q(F(1, 2 ** (k + 3) - 2))
        return q(sigma(-k) - F(1, 2) + F(1, 2 ** (-k + 3) - 2))

    def vp(k):
        if k == 0:
            return mp.mpf(0) if alt else mp.mpf(1)
        return mp.mpf(1)

    def vpp(k):
        if k > 0:
            return LOG1546
        if k == 0:
            return mp.log(mp.mpf('66.7')) if alt else mp.log(mp.mpf('0.611'))
        return LOG1546 + (q(sigma(k)) - mp.mpf(1) / 2) * mp.log(mp.pi)

    def mb(vf, k):
        m = (vf(k) - vf(k + 1)) / (q(sigma(k)) - q(sigma(k + 1)))
        b = vf(k) - m * q(sigma(k))
        return m, b
    return v, vp, vpp, mb


def Kidx(r):
    k = -200
    while not (1 - q(sigma(k)) <= r):
        k += 1
    return k


def theta(k, r):
    x = (1 - q(sigma(k))) / r
    return mp.asin(min(x, mp.mpf(1)))


def c_generic(r, vf, mb, KMAX=200):
    K = Kidx(r)
    m, b = mb(vf, K - 1)
    thK = theta(K, r)
    tot = (m + b) * (mp.pi / 2 - thK) - m * r * mp.cos(thK)
    for j in range(0, KMAX):
        k = K + j
        if q(sigma(k)) == q(sigma(k + 1)):
            break          # breakpoints coincide at working precision: every later term is 0
        m, b = mb(vf, k)
        t0, t1 = theta(k, r), theta(k + 1, r)
        tot += (m + b) * (t0 - t1) + m * r * (mp.cos(t0) - mp.cos(t1))
    return tot


def c4(r):
    val = mp.log(mp.zeta(1 + r)) / 2

    def f(u):
        # (zeta'/zeta)(1+x) = -1/x - gamma + O(x); times arcsin u ~ u: the integrand tends to -1/r at u = 0.
        # For u below 1e-20 the point 1 + r u rounds to 1 (pole), so use the two-term Laurent form there.
        if u < mp.mpf('1e-20'):
            return (-1 / (r * u) - mp.euler) * mp.asin(u) if u > 0 else -1 / r
        return (mp.zeta(1 + r * u, 1, 1) / mp.zeta(1 + r * u)).real * mp.asin(u)
    integ = mp.quad(f, [0, mp.mpf('0.001'), mp.mpf('0.1'), 1])
    return val - r / mp.pi * integ


def Phi(s):
    return mp.quad(lambda x: mp.log(mp.zeta(x)), [s, s + 1, s + 3, s + 10, s + 40, mp.inf])


def c5(r):
    def f(u):
        # log zeta(1+x) = -log x + gamma x + O(x^2); times arcsin u -> 0 at u = 0.  Below 1e-20 the
        # point 1 + r u rounds to 1 (pole), so use the Laurent form there.
        if u < mp.mpf('1e-20'):
            return (-mp.log(r * u) + mp.euler * r * u) * mp.asin(u) if u > 0 else mp.mpf(0)
        return mp.log(mp.zeta(1 + r * u)) * mp.asin(u)
    integ = mp.quad(f, [0, mp.mpf('0.001'), mp.mpf('0.1'), 1])
    return Phi(1 + r) + 2 * r / mp.pi * integ


def rectDenom(r, a):
    return 2 * r * mp.sqrt(1 - (a / r) ** 2) - 2 * a * mp.atan(mp.sqrt((r / a) ** 2 - 1))


def roundup7(v):
    if v == 0:
        return mp.mpf(0)
    d = int(mp.ceil(mp.log10(abs(v))))
    sc = mp.mpf(10) ** (7 - d)
    return mp.ceil(v * sc) / sc


def cmp(name, val, tex):
    ru = roundup7(val)
    tex = mp.mpf(tex)
    gap = abs(ru - tex) / max(abs(tex), mp.mpf('1e-30'))
    flag = "OK" if gap < mp.mpf('2e-6') else "MISMATCH <-- CHECK"
    print(f"    {name:6s} computed={mp.nstr(val, 12):>18}  roundup7={mp.nstr(ru, 9):>12}  tex={mp.nstr(tex, 9):>12}  {flag}")
    return gap


eta = mp.findroot(lambda e: 1 + e + mp.log(e), mp.mpf('0.28'))
PHI1 = Phi(mp.mpf(1) + mp.mpf('1e-40'))  # Phi(1) via the split of indep_mpmath_constants [B]
# recompute Phi(1) properly (log singularity at 1):
PHI1 = 1 + mp.quad(lambda x: mp.log((x - 1) * mp.zeta(x)) if x != 1 else mp.mpf(0), [1, 1.25, 1.5, 2]) \
    + mp.quad(lambda x: mp.log(mp.zeta(x)), [2, 4, 8, 16, 32, mp.inf])
print(f"eta = {mp.nstr(eta, 20)}   Phi(1) = {mp.nstr(PHI1, 20)}")

vA, vpA, vppA, mbA = make_family(alt=True)
vM, vpM, vppM, mbM = make_family(alt=False)

print()
print("=" * 90)
print("Table 2 (tab:crvalues), r = 1/2  [tex uses the Alt triple]")
print("=" * 90)
r = mp.mpf(1) / 2
c1A, c2A, c3A = c_generic(r, vA, mbA), c_generic(r, vpA, mbA), c_generic(r, vppA, mbA)
c1M, c2M, c3M = c_generic(r, vM, mbM), c_generic(r, vpM, mbM), c_generic(r, vppM, mbM)
c4v, c5v = c4(r), c5(r)
print("  Alt triple (table's):")
cmp("c1", c1A, '0.1467868'); cmp("c2", c2A, '0.9393432'); cmp("c3", c3A, '3.061478')
cmp("c4", c4v, '0.7795712'); cmp("c5", c5v, '1.126439')
print(f"  Main-text triple (Lean's c1/c2/c3): c1={mp.nstr(c1M, 10)}  c2={mp.nstr(c2M, 10)} (= pi/2? {mp.nstr(c2M - mp.pi/2, 3)})  c3={mp.nstr(c3M, 10)}")
print(f"  Lean docstring quotes c_{{3,1/2}} = 0.0982 under the main-text triple: {'OK' if abs(c3M - mp.mpf('0.0982')) < 1e-4 else 'CHECK'}")

print()
print("=" * 90)
print("Table 7 (tab:littlewoodshort), alpha = 1/8, r = 1/2 (k = 0)  [Alt triple]")
print("=" * 90)
alpha = mp.mpf(1) / 8
k = 0
mk, bk = mbA(vA, k); mkp, bkp = mbA(vpA, k); mkpp, bkpp = mbA(vppA, k)
A1 = (mk * (1 - r) + bk) / (2 * (r - alpha))
A2 = (mkp * (1 - r) + bkp) / (2 * mp.pi * (r - alpha))
A3 = (mkpp * (1 - r) + bkpp) / (2 * mp.pi * (r - alpha))
A4 = c1A * r / (r - alpha)
A5 = (c2A * r + mp.pi * r) / (mp.pi * (r - alpha))
A6 = (c3A * r + c4v * mp.pi * r + mp.pi * mp.log(mp.mpf('29.388')) * r + Phi(1 + eta * r)
      + (1 + eta) * r * mp.log(mp.zeta(1 + eta * r))) / (mp.pi * (r - alpha))
cmp("A1", A1, '0.2195122'); cmp("A2", A2, '0'); cmp("A3", A3, '1.782623')
cmp("A4", A4, '0.1957157'); cmp("A5", A5, '1.732003'); cmp("A6", A6, '9.128594')
mkM, bkM = mbM(vM, 0)
print(f"  Lean's main-text A1 at the same point: {mp.nstr((mkM*(1-r)+bkM)/(2*(r-alpha)), 10)}  (= v_0/(2(r-alpha)) = (1/6)/(3/4) = 0.2222)")

print()
print("=" * 90)
print("Table 5 (tab:rectangularjensen), alpha = 1/7, r = 0.5647100  [Alt triple]")
print("=" * 90)
alpha = mp.mpf(1) / 7
r = mp.mpf('0.5647100')
D = rectDenom(r, alpha)
c1A, c2A, c3A = c_generic(r, vA, mbA), c_generic(r, vpA, mbA), c_generic(r, vppA, mbA)
c5v = c5(r)
cmp("B1", c1A / D, '0.2457053'); cmp("B2", c2A / (mp.pi * D), '0.3900919')
cmp("B3", c3A / (mp.pi * D), '1.450119'); cmp("B4", (2 * PHI1 + c5v) / D, '6.518765')
cmp("ahat", mp.sqrt(r ** 2 - alpha ** 2), '0.5463417')
print(f"  (Table 6 row: c1={mp.nstr(c1A,8)} c2={mp.nstr(c2A,8)} c3={mp.nstr(c3A,8)} c5={mp.nstr(c5v,8)}; tex 0.1761601, 0.8786375, 3.266227, 1.078532)")


def C2denom(h, t):
    L = mp.log(t)
    return (1 - mp.log(2 * mp.pi) / L - (1 - mp.log(2)) / (t ** (mp.mpf(2) / 3) * L)
            - mp.mpf('0.194') * mp.pi / h - mp.mpf('9.908') * mp.pi / (h * L))


print()
print("=" * 90)
print("C2 tables (Code/C2_tables_raw.tex -> paper Tables 8-11)  [Alt triple, as compute_C2_tables.sage]")
print("=" * 90)
# Littlewood row: alpha=1/7, r=0.5000553, h0=100, t0=10^200 -> 0.4981758
alpha = mp.mpf(1) / 7
r = mp.mpf('0.5000553')
h, t = mp.mpf(100), mp.mpf(10) ** 200
k = 0 if q(sigma(0)) <= 1 - r < q(sigma(1)) else -1
mk, bk = mbA(vA, k); mkp, bkp = mbA(vpA, k); mkpp, bkpp = mbA(vppA, k)
c1A, c2A, c3A = c_generic(r, vA, mbA), c_generic(r, vpA, mbA), c_generic(r, vppA, mbA)
c4v = c4(r)
A1 = (mk * (1 - r) + bk) / (2 * (r - alpha)); A2 = (mkp * (1 - r) + bkp) / (2 * mp.pi * (r - alpha))
A3 = (mkpp * (1 - r) + bkpp) / (2 * mp.pi * (r - alpha)); A4 = c1A * r / (r - alpha)
A5 = (c2A * r + mp.pi * r) / (mp.pi * (r - alpha))
A6 = (c3A * r + c4v * mp.pi * r + mp.pi * mp.log(mp.mpf('29.388')) * r + Phi(1 + eta * r)
      + (1 + eta) * r * mp.log(mp.zeta(1 + eta * r))) / (mp.pi * (r - alpha))
L = mp.log(t)
numL = (2 * A1 + 2 * A4 / h + mp.pi * (2 * A2 + 2 * A5 / h) * mp.log(L) / L + 2 * mp.pi * A3 / L
        + mp.pi * A6 / (h * L) + mp.pi / ((r - alpha) * h * t * L) * (mp.mpf('0.335') + mp.mpf('0.51') / L))
C2L = numL / C2denom(h, t)
print(f"  Littlewood alpha=1/7 r={r} h0=100 t0=1e200 (chord k={k}):")
cmp("C2L", C2L, '0.4981758')
# Jensen row: alpha=1/16, r=0.5264389, h0=100, t0=10^100 -> 0.4579894
alpha = mp.mpf(1) / 16
r = mp.mpf('0.5264389')
h, t = mp.mpf(100), mp.mpf(10) ** 100
D = rectDenom(r, alpha)
c1A, c2A, c3A = c_generic(r, vA, mbA), c_generic(r, vpA, mbA), c_generic(r, vppA, mbA)
c5v = c5(r)
B1, B2, B3, B4 = c1A / D, c2A / (mp.pi * D), c3A / (mp.pi * D), (2 * PHI1 + c5v) / D
ahat = mp.sqrt(r ** 2 - alpha ** 2)
L = mp.log(t)
numJ = ((2 + 2 * ahat / h) * (B1 + mp.pi * B2 * mp.log(L) / L + mp.pi * B3 / L) + mp.pi * B4 / (h * L)
        + mp.mpf('3.35') * mp.pi / (D * h * t ** (mp.mpf(1) / 3) * L))
C2J = numJ / C2denom(h, t)
print(f"  Jensen alpha=1/16 r={r} h0=100 t0=1e100:")
cmp("C2J", C2J, '0.4579894')
print()
print("=" * 90)
print("c3_nonneg (ConstantSigns.lean): min over r in (0,1) of c3(r) in Lean's MAIN-TEXT triple (1/6, 1, log 0.611)")
print("=" * 90)
mp.mp.dps = 30
best = None
for i in range(1, 1000):
    r = mp.mpf(i) / 1000
    v = c_generic(r, vppM, mbM)
    if best is None or v < best[0]:
        best = (v, r)
# refine around the grid minimum
lo, hi = best[1] - mp.mpf('0.001'), best[1] + mp.mpf('0.001')
for i in range(0, 201):
    r = lo + (hi - lo) * i / 200
    if 0 < r < 1:
        v = c_generic(r, vppM, mbM)
        if v < best[0]:
            best = (v, r)
print(f"  min c3(r) = {mp.nstr(best[0], 10)} at r = {mp.nstr(best[1], 8)}   (verify_c3_and_chord_signs.py: 0.0165 at 0.5776)"
      f"   {'>= 0 OK' if best[0] >= 0 else 'NEGATIVE <-- CHECK'}")
# c3 is piecewise-smooth in r with kinks at the breakpoints r = 1 - sigma_k; the minimum sits inside the k=0 chord
c3_half = c_generic(mp.mpf(1) / 2, vppM, mbM)
c3_bp = c_generic(1 - q(sigma(-1)), vppM, mbM)
print(f"  c3(1/2) = {mp.nstr(c3_half, 8)},  c3(1-sigma_(-1)) = c3({mp.nstr(1 - q(sigma(-1)), 6)}) = {mp.nstr(c3_bp, 8)}")
print(f"  (Alt triple for comparison: min over the same grid = "
      f"{mp.nstr(min(c_generic(mp.mpf(i)/1000, vppA, mbA) for i in range(1, 1000)), 8)})")
print()
print("NOTE: C2denom here uses the Lean/tex constant (1-log 2)/(t^(2/3) log t), and so does")
print("      compute_C2_tables.sage, so this is an independent recomputation of the same formula.")
print("Done.")
