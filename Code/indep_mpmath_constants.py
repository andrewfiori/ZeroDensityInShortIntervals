#!/usr/bin/env python3
r"""
INDEPENDENT mpmath re-verification (2026-09-05) of the closed numeric facts this development does
not prove inside Lean, together with several it does, computed from scratch -- NOT by re-running
or porting the Sage/arb scripts, but by a different route wherever one exists (closed forms,
direct quadrature with singularity splitting, direct series summation), so that a transcription
error shared by the tex, the Lean docstring and the arb script would show up.

Everything here is high-precision floating point (mpmath, 40-60 digits), i.e. *evidence*, not a
certificate. Where a Sage script gives certified balls, this script is the independent cross-check
of those balls; where it uses mpmath too, this is a second implementation.

Each block names its Lean target and prints PASS/FAIL against the constant that appears in the
Lean statement. Two blocks certify a hypothesis-class field; the rest check declarations the Lean
now proves outright, or internal consistency of definitions. Blocks:

  [A] certifies `Hypotheses.NumericCertificates.ehalf_bound` (theorem
      `Jensen.JensenBounds.Ehalf_bound`)     3e*Ehalf/(2pi) < 1.1343755
      -- the arb certificate is `Code/verify_Ehalf_bound.sage`
  [B] certifies `Hypotheses.NumericCertificates.integral_log_zeta_Ioi_one_lt` (theorem
      `Jensen.RectangularBounds.integral_log_zeta_Ioi_one_lt`)  int_1^oo log zeta < 1.7975699586287395
      -- the arb certificate is `Code/verify_Phi_one_bound.sage`
  [C] proved theorems `Background.LogDerivZetaLaurent.stieltjes_combo_upper_bound`/`_lower_bound`
      0.15 <= gamma^2+2gamma_1 <= 0.20
  [D] the Euler-Maclaurin-free bracket `Definitions.stieltjesSeq`: stieltjesSeq 20 <= 1/100 (and
      the m=15 remark).  The wrapper this once supported is gone -- the live upper bracket for
      gamma_1 is `LogDerivZetaLaurent.stieltjesConstant1_upper_bound` (gamma_1 <= -0.0724), got
      from `Definitions.stieltjesSeqHi` at m = 16 -- so this block is now a standalone check that
      the crude bracket behaves as described.
  [E] proved theorems `Background.BackgroundZetaBounds.argGamma_analytic` / `argGamma`, whose
      stated error term is 0.21/t^3.  Reports sup residual*t^3 on a grid against several
      envelopes: the slack 2, the tex's older 0.043 (numerically true but NOT derivable from
      Brent's remainder bound), and 1/20.
  [F] proved theorem `Background.BackgroundZetaBounds.argGamma_taylor_residue`
      pure-real residual*t^3 <= 1
  [G] proved theorem `Background.BackgroundZetaBounds.abs_arctan_sub_self_le_cube_div_three`
  [H] -Re(zeta'/zeta)(1+z) < 1/z for z > 0.  The all-`z` form has no Lean counterpart: it was
      deleted with its unused consumers, because every call site needs only z <= 2, where
      `LogDerivZetaLaurent.neg_logDeriv_zeta_lt_one_div` (Lemma 38's claim 2) proves it.  The grid
      below is evidence for the general statement, not a certificate of anything.
  [I] `MainCorollary.h0Threshold`, `C2denom`, `Lbound` -- internal consistency (h0Threshold is the root
      of C2denom; Lbound >= (h log t/pi)*C2denom for h <= t^{2/3})
  [J] the hypothesis field `ExternalFacts.BrentStirlingInputs.shifted_remainder_bound` (theorem
      `brent_stirling_shifted_remainder_bound`)  ||R2hat(z)||*||z||^3 <= 1/100 on the box
      Re z in [-1,1], Im z in [5, 1e4]  (the Re z < 0 extension the field takes beyond Brent's H*)

Run with:  python3 Code/indep_mpmath_constants.py
"""
import mpmath as mp

mp.mp.dps = 50
PASS = "PASS"
FAIL = "FAIL  <-- CHECK"


def verdict(ok):
    return PASS if ok else FAIL


# ------------------------------------------------------------------------------------------
# [A] Ehalf = int_0^{pi/2} cos(theta)^{3/2} dtheta.  Independent routes:
#     (i) Beta function:  (1/2) B(5/4, 1/2) = Gamma(5/4)Gamma(1/2)/(2 Gamma(7/4));
#     (ii) direct tanh-sinh quadrature (mpmath handles the algebraic endpoint singularity);
#     (iii) the classical form Gamma(1/4)^2/(6 sqrt(2 pi)) quoted in the Lean docstring.
# ------------------------------------------------------------------------------------------
print("=" * 90)
print("[A] Ehalf_bound :  3*e*Ehalf/(2*pi) < 1.1343755")
print("=" * 90)
E_beta = mp.gamma(mp.mpf(5) / 4) * mp.gamma(mp.mpf(1) / 2) / (2 * mp.gamma(mp.mpf(7) / 4))
E_quad = mp.quad(lambda th: mp.cos(th) ** mp.mpf(1.5), [0, mp.pi / 4, mp.pi / 2])
E_closed = mp.gamma(mp.mpf(1) / 4) ** 2 / (6 * mp.sqrt(2 * mp.pi))
print(f"  Ehalf via Beta     = {mp.nstr(E_beta, 30)}")
print(f"  Ehalf via quad     = {mp.nstr(E_quad, 30)}")
print(f"  Ehalf via Gamma(1/4)^2/(6 sqrt(2pi)) = {mp.nstr(E_closed, 30)}")
print(f"  |Beta - quad|      = {mp.nstr(abs(E_beta - E_quad), 5)}   "
      f"|Beta - closed| = {mp.nstr(abs(E_beta - E_closed), 5)}")
val_A = 3 * mp.e * E_beta / (2 * mp.pi)
print(f"  3e*Ehalf/(2pi)     = {mp.nstr(val_A, 25)}")
print(f"  margin to 1.1343755 = {mp.nstr(mp.mpf('1.1343755') - val_A, 6)}   "
      f"{verdict(val_A < mp.mpf('1.1343755'))}")
print(f"  (tex's printed 1.134375 as a strict upper bound: "
      f"{verdict(val_A < mp.mpf('1.134375'))} -- expected FAIL, the tex writes '~', see docstring)")

# ------------------------------------------------------------------------------------------
# [B] Phi(1) = int_1^oo log zeta(x) dx.  Independent route: split off the log singularity at
#     x = 1 analytically.  Write log zeta(x) = -log(x-1) + log((x-1) zeta(x)); the second factor
#     is analytic and bounded near 1 ((x-1)zeta(x) -> 1).  Then
#        int_1^2 log zeta = int_1^2 -log(x-1) dx + int_1^2 log((x-1)zeta(x)) dx = 1 + smooth,
#     and the tail int_2^oo log zeta(x) dx is computed with the substitution to an infinite
#     interval (mpmath quad on [2, inf]; log zeta(x) ~ 2^{-x} so this converges fast).
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[B] integral_log_zeta_Ioi_one_lt :  int_1^oo log|zeta(x)| dx < 1.7975699586287395")
print("=" * 90)


def log_reg(x):
    # log((x-1)*zeta(x)), removable at x=1 (value 0 there)
    if x == 1:
        return mp.mpf(0)
    return mp.log((x - 1) * mp.zeta(x))


I_sing = mp.mpf(1)                      # int_1^2 -log(x-1) dx = 1 exactly
I_reg = mp.quad(log_reg, [1, mp.mpf('1.25'), mp.mpf('1.5'), 2])
I_tail = mp.quad(lambda x: mp.log(mp.zeta(x)), [2, 4, 8, 16, 32, 64, mp.inf])
Phi1 = I_sing + I_reg + I_tail
bound_B = mp.mpf('1.7975699586287395')
print(f"  int_1^2 -log(x-1)         = 1 (exact)")
print(f"  int_1^2 log((x-1)zeta(x)) = {mp.nstr(I_reg, 30)}")
print(f"  int_2^oo log zeta(x)      = {mp.nstr(I_tail, 30)}")
print(f"  Phi(1)                    = {mp.nstr(Phi1, 30)}")
print(f"  Lean/tex bound            = {mp.nstr(bound_B, 30)}")
print(f"  margin (bound - Phi(1))   = {mp.nstr(bound_B - Phi1, 6)}   {verdict(Phi1 < bound_B)}")
# cross-check against the prime-power series Phi(1) = sum_{n>=2} Lambda(n)/(log n)^2 / n at
# a large cutoff plus the Sage script's own tail formula is NOT used here -- the point is
# independence.  Instead cross-check via a second quadrature with a different split point.
I_reg2 = mp.quad(log_reg, [1, mp.mpf('1.1'), mp.mpf('1.7'), 3])
I_tail2 = mp.quad(lambda x: mp.log(mp.zeta(x)), [3, 6, 12, 24, 48, mp.inf])
Phi1b = mp.log(2) + I_reg2 + I_tail2     # int_1^3 -log(x-1) dx = 2 log 2 - 2 + 2 ... careful
# int_1^3 -log(x-1) dx = -[ (x-1)log(x-1) - (x-1) ]_1^3 = -(2 log 2 - 2) = 2 - 2 log 2
Phi1b = (2 - 2 * mp.log(2)) + I_reg2 + I_tail2
print(f"  second split (at x=3)     = {mp.nstr(Phi1b, 30)}   |diff| = {mp.nstr(abs(Phi1 - Phi1b), 5)}")

# ------------------------------------------------------------------------------------------
# [C] gamma^2 + 2 gamma_1 with mpmath's own euler and stieltjes(1)
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[C] stieltjes_combo_{lower,upper}_bound :  0.15 <= gamma^2 + 2*gamma_1 <= 0.20")
print("=" * 90)
g = mp.euler
g1 = mp.stieltjes(1)
combo = g ** 2 + 2 * g1
print(f"  gamma   = {mp.nstr(g, 30)}")
print(f"  gamma_1 = {mp.nstr(g1, 30)}")
print(f"  gamma^2 + 2 gamma_1 = {mp.nstr(combo, 30)}")
print(f"  0.15 <= combo : {verdict(combo >= mp.mpf('0.15'))}    combo <= 0.20 : {verdict(combo <= mp.mpf('0.20'))}")
print(f"  slack above: {mp.nstr(mp.mpf('0.20') - combo, 6)}   slack below: {mp.nstr(combo - mp.mpf('0.15'), 6)}")

# ------------------------------------------------------------------------------------------
# [D] stieltjesSeq m = sum_{k=1}^m log k / k - (log m)^2/2   (Definitions.stieltjesSeq).  This is
#     the crude upper bracket for gamma_1; reaching gamma_1 <= -0.0724 through it would need
#     m ~ 800.  The development instead uses the Euler-Maclaurin bracket Definitions.stieltjesSeqHi
#     at m = 16, so what is checked here is the crude sequence's own behaviour.
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[D] stieltjesSeq 20 <= 1/100 -- the crude sequence's own behaviour.  No Lean declaration")
print("    states this; the development brackets gamma_1 with Definitions.stieltjesSeqHi at")
print("    m = 16 instead (stieltjesConstant1_le_stieltjesSeqHi).")
print("=" * 90)


def stieltjesSeq(m):
    return mp.fsum(mp.log(k) / k for k in range(1, m + 1)) - mp.log(m) ** 2 / 2


for m in (15, 20, 50, 100, 400, 800):
    v = stieltjesSeq(m)
    print(f"  stieltjesSeq({m:4d}) = {mp.nstr(v, 20)}    (minus gamma_1: {mp.nstr(v - g1, 8)})")
s20 = stieltjesSeq(20)
print(f"  stieltjesSeq 20 <= 1/100 : {verdict(s20 <= mp.mpf(1) / 100)}   margin {mp.nstr(mp.mpf(1)/100 - s20, 8)}")
print(f"  stieltjesSeq 15 <= 1/50  : {verdict(stieltjesSeq(15) <= mp.mpf(1) / 50)}  (docstring remark)")
# the upper bracket  gamma_1 <= stieltjesSeq m  (Definitions.stieltjesConstant1_le_stieltjesSeq)
print(f"  bracket gamma_1 <= stieltjesSeq 20 : {verdict(g1 <= s20)}")

# ------------------------------------------------------------------------------------------
# [E] `Lemma \ref{lemma:argGamma}` (Lemma 37) / argGamma_analytic.  mpmath's loggamma IS the
#     analytic branch (continuous in the right half plane), i.e. exactly `logGammaAnalytic`.
#     Residual
#        R(d,t) = Im lg(1/2 + it/2) - Im lg(1/2 + d/2 + it/2) - ( -d pi/4 + d^2/(4t) ).
#     Lean proves |R| <= 0.21/t^3 -- the constant Brent's shifted remainder bound actually yields
#     (0.16) plus the sharp Taylor residual (0.045).  An earlier tex printed 0.043/t^3, which is
#     numerically true (the true sup is ~0.0422) but is not derivable from the cited remainder
#     bound.  Report sup |R| t^3 over d in [-1/2, 1], t in [10, 2000] against those envelopes.
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[E] argGamma / argGamma_analytic : |Im lgG(1/2+it/2) - Im lgG(1/2+d/2+it/2) + d pi/4 - d^2/(4t)| * t^3")
print("=" * 90)
mp.mp.dps = 40


def residual_E(d, t):
    d = mp.mpf(d)
    t = mp.mpf(t)
    a = mp.loggamma(mp.mpc(mp.mpf(1) / 2, t / 2)).imag
    b = mp.loggamma(mp.mpc(mp.mpf(1) / 2 + d / 2, t / 2)).imag
    return a - b - (-d * mp.pi / 4 + d ** 2 / (4 * t))


worst = (mp.mpf(0), None, None)
for t in [10, 10.5, 11, 12, 14, 17, 20, 25, 30, 40, 60, 100, 200, 500, 1000, 2000]:
    for i in range(0, 31):
        d = mp.mpf(-1) / 2 + mp.mpf(3) / 2 * i / 30
        v = abs(residual_E(d, t)) * mp.mpf(t) ** 3
        if v > worst[0]:
            worst = (v, d, t)
print(f"  sup |R| t^3 on grid = {mp.nstr(worst[0], 10)}  at delta={mp.nstr(worst[1], 6)}, t={worst[2]}")
# refine around the worst point in delta at t = 10 (the sup is approached as t -> 10+, delta -> 1)
best = worst[0]
for i in range(0, 201):
    d = mp.mpf(1) - mp.mpf(i) / 400          # delta in [0.5, 1]
    for t in (10, mp.mpf('10.0001'), 10.01, 10.1):
        v = abs(residual_E(d, t)) * mp.mpf(t) ** 3
        best = max(best, v)
print(f"  refined sup |R| t^3 (delta in [1/2,1], t near 10) = {mp.nstr(best, 10)}")
print(f"  <= 2      (Lean argGamma):        {verdict(best <= 2)}")
print(f"  <= 0.043  (tex Lemma 36 as stated): {verdict(best <= mp.mpf('0.043'))}")
print(f"  <= 1/20   (verify_argGamma.py's remark): {verdict(best <= mp.mpf(1) / 20)}")
# The pieces: leading Taylor part  -d^4/(24 t^3) + d^2/(12 t^3)  (max 1/24 = 0.041667 at d=1)
print(f"  leading-order prediction at delta=1: (1/12 - 1/24) = {mp.nstr(mp.mpf(1)/24, 8)};"
      f" Brent-remainder difference contributes the rest")
# What is provable from the Brent inputs as stated: Taylor residue (<= 1/t^3 as stated in Lean,
# true value 0.0417/t^3) plus 2 * (1/100) * 8 / t^3 = 0.16/t^3 for the two shifted remainders
print(f"  provable from Lean axioms with sharp Taylor part: 0.0417 + 0.16 = 0.2017 (so 0.21/t^3 would be"
      f" provable; 0.043 is NOT derivable from the axiomatized Brent bound 1/100)")

# ------------------------------------------------------------------------------------------
# [F] argGamma_taylor_residue: pure real inequality, |d| <= 1, t > 10
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[F] argGamma_taylor_residue : |d/2 arctan(d/t) - t/4 log(1+d^2/t^2) - d^2/(4t) + d^2/(12 t (d^2+t^2))| <= 1/t^3")
print("=" * 90)


def taylor_res(d, t):
    d = mp.mpf(d)
    t = mp.mpf(t)
    return abs(d / 2 * mp.atan(d / t) - t / 4 * mp.log(1 + d ** 2 / t ** 2) - d ** 2 / (4 * t)
               + d ** 2 / (12 * t * (d ** 2 + t ** 2)))


worstF = mp.mpf(0)
for t in [10, 10.001, 10.1, 11, 15, 20, 50, 100, 1000]:
    for i in range(-40, 41):
        d = mp.mpf(i) / 40
        worstF = max(worstF, taylor_res(d, t) * mp.mpf(t) ** 3)
print(f"  sup residual * t^3 over grid = {mp.nstr(worstF, 10)}   <= 1 : {verdict(worstF <= 1)}")
print(f"  (leading order  |d^2/12 - d^4/24| <= 1/24 = 0.041667; a Lean proof via the two Taylor bounds"
      f" gets 1/6 + 1/4 + 1/12 = 1/2 <= 1)")

# ------------------------------------------------------------------------------------------
# [G] |arctan x - x| <= |x|^3/3 on |x| <= 1
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[G] abs_arctan_sub_self_le_cube_div_three")
print("=" * 90)
worstG = mp.mpf(0)
for i in range(1, 1001):
    x = mp.mpf(i) / 1000
    worstG = max(worstG, abs(mp.atan(x) - x) / (x ** 3 / 3))
print(f"  sup |arctan x - x| / (|x|^3/3) on (0,1] = {mp.nstr(worstG, 10)}  <= 1 : {verdict(worstG <= 1)}"
      f"   (odd function, so |x| <= 1 covered)")

# ------------------------------------------------------------------------------------------
# [H] -Re(zeta'/zeta)(1+z) < 1/z for z > 0
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[H] -zeta'/zeta(1+z) < 1/z,  z > 0 -- a standing inequality about the Dirichlet series.")
print("    No Lean declaration states it in this form; Definitions carries the two facts the")
print("    development actually uses, neg_logDeriv_zeta_re_pos and neg_logDeriv_zeta_re_antitone.")
print("=" * 90)
min_gap = None
for z in [mp.mpf('1e-6'), mp.mpf('1e-3'), 0.01, 0.1, 0.5, 1, 2, 5, 10, 20, 50, 100]:
    z = mp.mpf(z)
    s = 1 + z
    val = -mp.zeta(s, 1, 1) / mp.zeta(s)
    gap = 1 / z - val
    min_gap = gap if min_gap is None else min(min_gap, gap)
    print(f"  z={mp.nstr(z, 6):>8}:  -zeta'/zeta(1+z) = {mp.nstr(val, 12):>18}   1/z - that = {mp.nstr(gap, 10)}")
print(f"  gap -> gamma = {mp.nstr(mp.euler, 10)} as z -> 0;  minimum gap on grid {mp.nstr(min_gap, 8)} > 0 : "
      f"{verdict(min_gap > 0)}")

# ------------------------------------------------------------------------------------------
# [I] MainCorollary: h0Threshold is the root of C2denom(h, t0) in h; Lbound vs C2denom
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[I] MainCorollary.h0Threshold / C2denom / Lbound consistency")
print("=" * 90)


def C2denom(h, t):
    L = mp.log(t)
    return (1 - mp.log(2 * mp.pi) / L - (1 - mp.log(2)) / (t ** (mp.mpf(2) / 3) * L)
            - mp.mpf('0.194') * mp.pi / h - mp.mpf('9.908') * mp.pi / (h * L))


def h0Threshold(t0):
    L = mp.log(t0)
    return ((97 * mp.pi / 500) * (1 + mp.mpf(4954) / (97 * L))
            / (1 - (1 - mp.log(2)) / (t0 ** (mp.mpf(2) / 3) * L) - mp.log(2 * mp.pi) / L))


def Lbound(h, t):
    return ((mp.log(t / (2 * mp.pi)) / mp.pi - (1 - mp.log(2)) * h ** 2 / (mp.pi * t ** 2)) * h
            - mp.mpf('0.194') * mp.log(t) - mp.mpf('9.908'))


okI = True
for t0 in [mp.mpf(10) ** 12, 3 * mp.mpf(10) ** 12, mp.mpf(10) ** 20, mp.mpf(10) ** 100]:
    h0 = h0Threshold(t0)
    root_res = C2denom(h0, t0)
    okI = okI and abs(root_res) < mp.mpf('1e-30')
    print(f"  t0=1e{mp.nstr(mp.log10(t0), 5)}: h0Threshold = {mp.nstr(h0, 10)},  C2denom(h0,t0) = {mp.nstr(root_res, 3)}")
print(f"  h0Threshold is the exact root of C2denom in h : {verdict(okI)}")
print(f"  (Lean docstring: 'about 1.86 at t0 = 10^12')")
# Lbound(h,t) >= (h log t/pi) * C2denom(h,t)  for h <= t^{2/3}  (the single weakening h^2/t^2 <= t^{-2/3})
okL = True
for t in [mp.mpf(10) ** 12, mp.mpf(10) ** 13, mp.mpf(10) ** 30]:
    for h in [2, 10, 100, 1000, t ** (mp.mpf(2) / 3) / 2, t ** (mp.mpf(2) / 3)]:
        h = mp.mpf(h)
        lhs = Lbound(h, t)
        rhs = h * mp.log(t) / mp.pi * C2denom(h, t)
        okL = okL and lhs >= rhs - mp.mpf('1e-25') * abs(lhs)
print(f"  Lbound(h,t) >= (h log t/pi) C2denom(h,t) for h <= t^(2/3) on grid : {verdict(okL)}")
# and equality at h = t^{2/3} exactly
t = mp.mpf(10) ** 12
h = t ** (mp.mpf(2) / 3)
print(f"  at h = t^(2/3): Lbound - (h log t/pi) C2denom = {mp.nstr(Lbound(h, t) - h*mp.log(t)/mp.pi*C2denom(h, t), 3)} (should be ~0)")

# ------------------------------------------------------------------------------------------
# [J] Brent shifted remainder R2hat(z) = lgG(z+1/2) - (z log z - z + log(2pi)/2 - 1/(24z)),
#     ||R2hat|| * ||z||^3 <= 1/100 for Im z > 5, |Re z| <= 1
#     (hypothesis field ExternalFacts.BrentStirlingInputs.shifted_remainder_bound, read off by the
#      theorem brent_stirling_shifted_remainder_bound)
# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("[J] brent_stirling_shifted_remainder_bound : ||R2hat(z)|| ||z||^3 <= 1/100 on Re z in [-1,1], Im z in [5,1e4]")
print("=" * 90)


def R2hat(z):
    return mp.loggamma(z + mp.mpf(1) / 2) - (z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z))


worstJ = (mp.mpf(0), None)
for y in [5, 5.001, 5.5, 6, 8, 10, 20, 50, 100, 1000, 10000]:
    for i in range(-20, 21):
        x = mp.mpf(i) / 20
        z = mp.mpc(x, y)
        v = abs(R2hat(z)) * abs(z) ** 3
        if v > worstJ[0]:
            worstJ = (v, z)
print(f"  sup ||R2hat|| ||z||^3 on grid = {mp.nstr(worstJ[0], 10)} at z = {mp.nstr(worstJ[1], 8)}")
print(f"  <= 1/100 : {verdict(worstJ[0] <= mp.mpf(1)/100)}     (Brent's next term 7/2880 = {mp.nstr(mp.mpf(7)/2880, 8)})")
print()
print("Done.")
