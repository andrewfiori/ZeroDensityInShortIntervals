#!/usr/bin/env python3
r"""
INDEPENDENT mpmath check (2026-09-05) of the numeric content of `Lemma
\ref{lemma:logderzetabound}` (Lemma 38; the file name records an earlier numbering, when the same
lemma was Lemma 37) as formalized in
`ZerosInShortIntervals/Background/LogDerivZetaLaurent.lean`.

  G(z) := logDerivZetaG(1+z) = -(zetaReg'/zetaReg)(1+z) + 1/(z+3) + 1/(z+5) + 1/(z+7)
        = -zeta'/zeta(1+z) - 1/z + 1/(z+3) + 1/(z+5) + 1/(z+7)          (z != 0, -3, -5, -7)

Block [A] is the project's certificate for the hypothesis field
`LaurentCertificate.logDerivZetaG_boundary_bound`; everything after it checks statements the Lean
now proves outright from that one input.  It is high-precision floating point, not ball
arithmetic: arb has no `zeta'`, which is why this field is kept apart from the arb-certified
`NumericCertificates`.  `Code/verify_lemmaA7_bound_radius7.sage` runs the same boundary scan on a
much denser mesh (6000 points per edge).

  [A] `LaurentCertificate.logDerivZetaG_boundary_bound`: |G(z)| <= 0.6 on the frontier of the
      SQUARE logDerivZetaBox = (-7,7) x (-7,7)  (NB: the tex says the circle |z| = 7; the Lean box
      is the square, whose boundary contains the removable point z = -7).  Both the square's
      boundary and the circle are scanned; near z = -7 the removable singularity is handled by
      evaluating -zeta'/zeta(s) + 1/(s+6) through its limit (zeta has a simple zero at s = -6).
  [B] `logDerivZetaCoeff n`, `logDerivZetaCoeff_bound` (claim 1): a_n = (-1)^{n+1} Re g_n + 3^{-n-1}+5^{-n-1}+7^{-n-1},
      g_n = G^{(n)}(0)/n!  computed by a Cauchy integral on |z| = 3 (trapezoid rule, exponentially accurate);
      check |a_n - (3^{-n-1}+5^{-n-1}+7^{-n-1})| <= 0.6 * 7^{-n}  for n = 1..60.
  [C] `logDerivZetaCoeff_zero` (a_0 = gamma), `logDerivZetaCoeff_one` (a_1 = gamma^2 + 2 gamma_1).
  [D] `hasSum_logDerivZetaCoeff` and `hasSum_logDerivZetaCoeff_integrated`: for x in (0,2],
        sum_n (-1)^n a_n x^n            = 1/x + zeta'/zeta(1+x),
        sum_n (-1)^n a_n x^{n+1}/(n+1)  = log|zeta(1+x)| + log x.
  [E] the tex's positivity / monotonicity remarks used for claim 2: a_n > 0, and a_n 2^n decreasing for n >= 2
      (`logDerivZetaCoeff_pos`, `logDerivZetaCoeff_two_mul_succ_le`).
  [F] the formula of `Remark \ref{lemma:logderzetabound-remark}` (Remark 39),
      a_n = -(1/n!) lim_m ( sum_{k<=m} Lambda(k) (log k)^n / k - (log m)^{n+1}/(n+1) ),
      checked at n = 0,1,2 with m up to 2e5 (slowly convergent; consistency to ~1e-3 is all one expects).

Run with:  python3 Code/indep_mpmath_lemma37.py
"""
import mpmath as mp

mp.mp.dps = 40
PASS = "PASS"
FAIL = "FAIL  <-- CHECK"


def verdict(ok):
    return PASS if ok else FAIL


def neg_logderiv_zeta(s):
    return -mp.zeta(s, 1, 1) / mp.zeta(s)


def G(z):
    z = mp.mpc(z)
    s = 1 + z
    # remove the trivial-zero poles by a limit when very close to s = -2, -4, -6
    for k in (2, 4, 6):
        if abs(s + k) < mp.mpf('1e-12'):
            # -zeta'/zeta(s) + 1/(s+k) is analytic; evaluate by symmetric average at tiny offsets
            h = mp.mpf('1e-8')
            v1 = neg_logderiv_zeta(s + h) + 1 / (s + h + k)
            v2 = neg_logderiv_zeta(s - h) + 1 / (s - h + k)
            core = (v1 + v2) / 2
            others = sum(1 / (s + j) for j in (2, 4, 6) if j != k)
            return core - 1 / (s - 1) + others
    return neg_logderiv_zeta(s) - 1 / (s - 1) + 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6)


# ------------------------------------------------------------------------------------------
print("=" * 90)
print("[A] logDerivZetaG_boundary_bound: |G(z)| <= 0.6 on the boundary of the square [-7,7]^2 (and on |z|=7)")
print("=" * 90)
mp.mp.dps = 30
N = 400
worst_sq = (mp.mpf(0), None)
pts = []
for i in range(N + 1):
    u = -7 + 14 * mp.mpf(i) / N
    pts += [mp.mpc(u, 7), mp.mpc(u, -7), mp.mpc(7, u), mp.mpc(-7, u)]
for z in pts:
    v = abs(G(z))
    if v > worst_sq[0]:
        worst_sq = (v, z)
print(f"  square boundary, {len(pts)} points: max |G| = {mp.nstr(worst_sq[0], 10)} at z = {mp.nstr(worst_sq[1], 6)}"
      f"   <= 0.6 : {verdict(worst_sq[0] <= mp.mpf('0.6'))}")
# refine near the worst point
zc = worst_sq[1]
best = worst_sq[0]
for i in range(-50, 51):
    if abs(zc.imag) == 7:
        z = mp.mpc(zc.real + mp.mpf(i) / 1000, zc.imag)
    else:
        z = mp.mpc(zc.real, zc.imag + mp.mpf(i) / 1000)
    if abs(z.real) <= 7 and abs(z.imag) <= 7:
        best = max(best, abs(G(z)))
print(f"  refined local max near there: {mp.nstr(best, 10)}")
print(f"  |G(-7)| (removable point on the frontier, via limit) = {mp.nstr(abs(G(mp.mpc(-7, 0))), 10)}")
worst_ci = (mp.mpf(0), None)
for i in range(N):
    th = 2 * mp.pi * i / N
    z = 7 * mp.expj(th)
    v = abs(G(z))
    if v > worst_ci[0]:
        worst_ci = (v, z)
print(f"  circle |z|=7, {N} points: max |G| = {mp.nstr(worst_ci[0], 10)} at z = {mp.nstr(worst_ci[1], 6)}"
      f"   <= 0.6 : {verdict(worst_ci[0] <= mp.mpf('0.6'))}")
print("  (tex: 'on the boundary |z|=7'; Lean: the square -- max modulus makes the square bound the stronger statement)")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[B] Taylor coefficients of G at 0 by Cauchy integral on |z|=3; claim 1 bound 0.6*7^-n")
print("=" * 90)
mp.mp.dps = 40
M = 512
R = mp.mpf(3)
# sample at half-integer angles so no node lands on z = -3 (s = -2, a removable point of G whose
# finite-difference limit would otherwise pollute the high coefficients)
THETAS = [2 * mp.pi * (j + mp.mpf(1) / 2) / M for j in range(M)]
vals = [G(R * mp.expj(th)) for th in THETAS]


def g_coeff(n):
    # g_n = (1/2 pi i) oint G(z)/z^{n+1} dz = (1/M) sum G(R e^{i th_j}) R^{-n} e^{-i n th_j}
    return mp.fsum(vals[j] * mp.expj(-n * THETAS[j]) for j in range(M)) / (M * R ** n)


def a_coeff(n):
    gn = g_coeff(n)
    return ((-1) ** (n + 1)) * gn.real + mp.mpf(3) ** (-n - 1) + mp.mpf(5) ** (-n - 1) + mp.mpf(7) ** (-n - 1)


a = [a_coeff(n) for n in range(0, 61)]
im_max = max(abs(g_coeff(n).imag) for n in range(0, 10))
print(f"  max |Im g_n| (n<10) = {mp.nstr(im_max, 3)}  (should be ~0: real coefficients)")
okB = True
worst_ratio = mp.mpf(0)
for n in range(1, 61):
    main = mp.mpf(3) ** (-n - 1) + mp.mpf(5) ** (-n - 1) + mp.mpf(7) ** (-n - 1)
    dev = abs(a[n] - main)
    ratio = dev / (mp.mpf('0.6') * mp.mpf(7) ** (-n))
    worst_ratio = max(worst_ratio, ratio)
    okB = okB and ratio <= 1
    if n <= 8 or n % 10 == 0:
        print(f"  n={n:2d}: a_n = {mp.nstr(a[n], 15):>22}  |a_n - main| / (0.6*7^-n) = {mp.nstr(ratio, 6)}")
print(f"  claim 1 holds for n=1..60 : {verdict(okB)}   (worst ratio {mp.nstr(worst_ratio, 6)}; "
      f"the G^(n)(0)/n! decay like 7^-n * 0.59, so the bound is sharp in the exponent)")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[C] a_0 = gamma,  a_1 = gamma^2 + 2 gamma_1")
print("=" * 90)
print(f"  a_0 = {mp.nstr(a[0], 25)}   gamma = {mp.nstr(mp.euler, 25)}   {verdict(abs(a[0]-mp.euler) < mp.mpf('1e-25'))}"
      f"  |diff|={mp.nstr(abs(a[0]-mp.euler), 3)}")
c1 = mp.euler ** 2 + 2 * mp.stieltjes(1)
print(f"  a_1 = {mp.nstr(a[1], 25)}   gamma^2+2gamma_1 = {mp.nstr(c1, 25)}   {verdict(abs(a[1]-c1) < mp.mpf('1e-25'))}"
      f"  |diff|={mp.nstr(abs(a[1]-c1), 3)}")
# a_n via Stieltjes constants: -zeta'/zeta(1+z) = 1/z + ... ; the general relation is not linear,
# so only a_0, a_1 are checked in closed form.

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[D] hasSum_logDerivZetaCoeff / _integrated at x in {0.5, 1, 2}")
print("=" * 90)
okD = True
for x in (mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)):
    S1 = mp.fsum(((-1) ** n) * a[n] * x ** n for n in range(0, 61))
    T1 = 1 / x + (mp.zeta(1 + x, 1, 1) / mp.zeta(1 + x))
    S2 = mp.fsum(((-1) ** n) * a[n] * x ** (n + 1) / (n + 1) for n in range(0, 61))
    T2 = mp.log(abs(mp.zeta(1 + x))) + mp.log(x)
    tail = abs(a[60]) * x ** 60 / (1 - x / 7)   # geometric tail estimate, a_n ~ 0.6*7^-n
    d1, d2 = abs(S1 - T1), abs(S2 - T2)
    okD = okD and d1 < 10 * tail + mp.mpf('1e-15') and d2 < 10 * tail + mp.mpf('1e-15')
    print(f"  x={mp.nstr(x,3)}: sum (-1)^n a_n x^n = {mp.nstr(S1, 18)} vs 1/x + zeta'/zeta(1+x) = {mp.nstr(T1, 18)}  |diff|={mp.nstr(d1, 3)}")
    print(f"         sum (-1)^n a_n x^(n+1)/(n+1) = {mp.nstr(S2, 18)} vs log zeta(1+x) + log x = {mp.nstr(T2, 18)}  |diff|={mp.nstr(d2, 3)}"
          f"  (truncation ~{mp.nstr(tail, 2)})")
print(f"  both HasSum statements consistent (to truncation) : {verdict(okD)}")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[E] a_n > 0 for all n <= 60; a_n 2^n decreasing for n >= 2 (tex claim 2 mechanics)")
print("=" * 90)
pos = all(a[n] > 0 for n in range(0, 61))
dec = all(a[n + 1] * 2 ** (n + 1) <= a[n] * 2 ** n for n in range(2, 60))
print(f"  a_n > 0 : {verdict(pos)}     a_n 2^n decreasing from n=2 : {verdict(dec)}")
print(f"  a_1*2 = {mp.nstr(2*a[1], 8)}, a_2*4 = {mp.nstr(4*a[2], 8)}, a_3*8 = {mp.nstr(8*a[3], 8)}  "
      f"(a_1 2 > a_2 4 ? {2*a[1] > 4*a[2]})")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[F] Remark 38: a_n = -(1/n!) lim_m ( sum_{k<=m} Lambda(k)(log k)^n/k - (log m)^{n+1}/(n+1) )")
print("=" * 90)
mp.mp.dps = 20
import math
Mmax = 200000
# sieve for Lambda via smallest prime factor
spf = list(range(Mmax + 1))
for i in range(2, int(Mmax ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, Mmax + 1, i):
            if spf[j] == j:
                spf[j] = i
lam = [0.0] * (Mmax + 1)
for k in range(2, Mmax + 1):
    p = spf[k]
    m = k
    while m % p == 0:
        m //= p
    if m == 1:
        lam[k] = math.log(p)
for n in (0, 1, 2):
    acc = 0.0
    checkpoints = {20000, 50000, 100000, 200000}
    vals_at = []
    for k in range(2, Mmax + 1):
        if lam[k]:
            acc += lam[k] * (math.log(k) ** n) / k
        if k in checkpoints:
            reg = acc - math.log(k) ** (n + 1) / (n + 1)
            vals_at.append((k, -reg / math.factorial(n)))
    print(f"  n={n}: a_n (Cauchy) = {mp.nstr(a[n], 12)};  Remark-38 partial limits: " +
          ", ".join(f"m={k}: {v:.6f}" for k, v in vals_at))
print("  (the regularised prime sum converges like (log m)^n (psi(m)-m)/m, oscillatory: n=0,1 agree to ~1e-3,")
print("   n=2 is not testable at m=2e5; this block is a consistency check of the Remark's SIGN convention, not a proof)")
print()
print("Done.")
