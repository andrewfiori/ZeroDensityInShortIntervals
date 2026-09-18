#!/usr/bin/env python3
r"""
INDEPENDENT mpmath check of the five Stirling / functional-equation residual bounds of
`Lemma \ref{lem:zetalessthanhalf}` (Lemma 36) in
`ZerosInShortIntervals/Background/BackgroundZetaBounds.lean`:

  `zetalessthanhalf_upper`        sigma in [0,1/2],  t>10 :  |D(sigma,t)|                     <= 1/(2 t^2)
  `zetalessthanhalf_upper_tight`  sigma in [0,1/2],  t>10 :  |D(sigma,t) - Dcoeff(sigma)/t^2| <= 1.21/t^3
  `zetalessthanhalf_lower`        sigma in [-1,0],   t>10 :  |D(sigma,t)|                     <= 4/t^2
  `zetalessthanhalf_lower_tight`  sigma in [-1,0],   t>10 :  |D(sigma,t) - Dcoeff(sigma)/t^2| <= 7.88/t^3
  `gamma_cos_estimate_lower`      sigma in [-1,0],   t>10 :  |E(sigma,t)|                     <= 4/t^2

All five are PROVED in Lean, and this is a sampled mpmath sweep at 40 digits rather than ball
arithmetic, so what follows is an independent numeric check and not a certificate of any
hypothesis-class field.  The two `_tight` thresholds tested here, 1.21 and 7.88, are the tex's
OLD constants; the Lean proofs and the corrected tex give the much sharper 0.06 and 1.4 (from
`gamma_cos_estimate_upper_tight` / `_lower_tight`).  Clearing 1.21/7.88 is therefore weaker than
the statements as they now stand -- but the suprema this script measures, about 1.2e-4 and 0.025,
are comfortably inside 0.06 and 1.4 as well.

where, with s = sigma + it,

  D(sigma,t) = log|zeta(s)| - log|zeta(1-s+2it)|  ...  precisely, in the Lean spelling,
             = log|zeta(sigma+it)| - ( log|zeta(1-sigma+it)| + (1/2-sigma) log|t/2| + (sigma-1/2) log pi ),
  Dcoeff(sigma) = sigma (2 sigma - 1)(1 - sigma)/12            (`Dcoeff`; `Dcoeff2 := Dcoeff`),
  E(sigma,t)  = log 2 - (1-sigma) log(2pi) + log|Gamma(1-sigma-it)| + log|cos(pi(1-sigma-it)/2)|
                - ( (1/2-sigma) log|t/2| + (sigma-1/2) log pi ).

and the tex (`Lemma \ref{lem:zetalessthanhalf}`, Lemma 36) stated the collapsed forms with
constants `(7 sqrt7/108 + 1.21/t)/t^2` and `(7/3 + 7.88/t)/t^2`, which the corrected tex and the
Lean theorems `zetalessthanhalf_upper_collapsed` / `_lower_collapsed` sharpen to
`(sqrt3/216 + 0.06/t)/t^2` and `(1/2 + 1.4/t)/t^2`.

TWO INDEPENDENT ROUTES for D.  (i) Directly from mpmath's zeta at both points (this checks the
transcription of the functional equation in the Lean statement -- signs of the log|t/2| and
log pi terms included).  (ii) zeta-free, from the functional equation
zeta(s) = chi(s) zeta(1-s), chi(s) = 2^s pi^{s-1} sin(pi s/2) Gamma(1-s): since zeta(1-s) and
zeta(1-sigma+it) = conj(zeta(1-s)) have the same modulus,
     D(sigma,t) = log|chi(s)| - (1/2-sigma) log(t/2) - (sigma-1/2) log pi,
which is smooth (no zeta zeros) and is what the residual "really is".  Route (i) is used on a
grid that keeps away from zeta zeros; route (ii) gives the supremum.

The output reports, for each statement, the supremum over the (sigma,t) grid of |residual| * t^2
(or * t^3), compared with the constant in the table above, and the true asymptotic constant.  The
grid is 18 ordinates t from 10 to 1e5, crossed with 21 abscissae sigma = i/40 on [0,1/2] and 41
abscissae sigma = -i/40 on [-1,0].

Run with:  python3 Code/indep_mpmath_zeta_functional_eq.py
"""
import mpmath as mp

mp.mp.dps = 40
PASS = "PASS"
FAIL = "FAIL  <-- CHECK"


def verdict(ok):
    return PASS if ok else FAIL


def Dcoeff(sig):
    sig = mp.mpf(sig)
    return sig * (2 * sig - 1) * (1 - sig) / 12


def D_zeta(sig, t):
    s = mp.mpc(sig, t)
    s1 = mp.mpc(1 - sig, t)
    return (mp.log(abs(mp.zeta(s))) - (mp.log(abs(mp.zeta(s1))) + (mp.mpf(1) / 2 - sig) * mp.log(abs(t / 2))
                                          + (sig - mp.mpf(1) / 2) * mp.log(mp.pi)))


def logabs_chi(sig, t):
    s = mp.mpc(sig, t)
    # log|chi(s)| with chi(s) = 2^s pi^(s-1) sin(pi s/2) Gamma(1-s); use loggamma for size
    return (sig * mp.log(2) + (sig - 1) * mp.log(mp.pi) + mp.log(abs(mp.sin(mp.pi * s / 2)))
            + mp.re(mp.loggamma(1 - s)))


def D_chi(sig, t):
    sig = mp.mpf(sig)
    t = mp.mpf(t)
    return logabs_chi(sig, t) - (mp.mpf(1) / 2 - sig) * mp.log(t / 2) - (sig - mp.mpf(1) / 2) * mp.log(mp.pi)


def E_gamma_cos(sig, t):
    sig = mp.mpf(sig)
    t = mp.mpf(t)
    w = mp.mpc(1 - sig, -t)
    return (mp.log(2) - (1 - sig) * mp.log(2 * mp.pi) + mp.re(mp.loggamma(w))
            + mp.log(abs(mp.cos(mp.pi * w / 2)))
            - ((mp.mpf(1) / 2 - sig) * mp.log(t / 2) + (sig - mp.mpf(1) / 2) * mp.log(mp.pi)))


# ------------------------------------------------------------------------------------------
print("=" * 90)
print("Route (i) vs route (ii): D from zeta directly and D from chi agree?  (transcription check)")
print("=" * 90)
worst_diff = mp.mpf(0)
for sig in [0, 0.1, 0.25, 0.5, -0.3, -1]:
    for t in [10.5, 13.7, 20.3, 50.1, 101.3]:
        a = D_zeta(mp.mpf(sig), mp.mpf(t))
        b = D_chi(sig, t)
        worst_diff = max(worst_diff, abs(a - b))
print(f"  max |D_zeta - D_chi| over sample = {mp.nstr(worst_diff, 5)}   {verdict(worst_diff < mp.mpf('1e-25'))}")
print("  (so the Lean statement's log|t/2|, log pi terms and signs are the functional equation's)")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("sigma in [0,1/2]: zetalessthanhalf_upper (1/(2t^2)) and _upper_tight (Dcoeff/t^2 + 1.21/t^3)")
print("=" * 90)
TS = [10, 10.01, 10.5, 11, 12, 14, 17, 20, 25, 30, 40, 60, 100, 200, 500, 1000, 1e4, 1e5]
SIG_UP = [mp.mpf(i) / 40 for i in range(0, 21)]           # 0 .. 1/2
sup_simple = (mp.mpf(0), None)
sup_tight = (mp.mpf(0), None)
for t in TS:
    t = mp.mpf(t)
    for sig in SIG_UP:
        d = D_chi(sig, t)
        v1 = abs(d) * t ** 2
        v2 = abs(d - Dcoeff(sig) / t ** 2) * t ** 3
        if v1 > sup_simple[0]:
            sup_simple = (v1, (sig, t))
        if v2 > sup_tight[0]:
            sup_tight = (v2, (sig, t))
print(f"  sup |D| t^2         = {mp.nstr(sup_simple[0], 8)} at (sigma,t)=({mp.nstr(sup_simple[1][0],4)},{mp.nstr(sup_simple[1][1],6)})"
      f"   Lean 1/2 : {verdict(sup_simple[0] <= mp.mpf(1)/2)}   tex 7sqrt7/108={mp.nstr(7*mp.sqrt(7)/108, 6)} (+1.21/t)")
print(f"  sup |D - Dcoeff/t^2| t^3 = {mp.nstr(sup_tight[0], 8)} at (sigma,t)=({mp.nstr(sup_tight[1][0],4)},{mp.nstr(sup_tight[1][1],6)})"
      f"   Lean/tex 1.21 : {verdict(sup_tight[0] <= mp.mpf('1.21'))}")
print(f"  max |Dcoeff| on [0,1/2] = {mp.nstr(max(abs(Dcoeff(s)) for s in SIG_UP), 6)}  (the true 1/t^2 coefficient)")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("sigma in [-1,0]: zetalessthanhalf_lower (4/t^2), _lower_tight (Dcoeff/t^2 + 7.88/t^3), gamma_cos_estimate_lower (4/t^2)")
print("=" * 90)
SIG_LO = [-mp.mpf(i) / 40 for i in range(0, 41)]          # 0 .. -1
sup_lo = (mp.mpf(0), None)
sup_lo_t = (mp.mpf(0), None)
sup_E = (mp.mpf(0), None)
sup_DE = mp.mpf(0)
for t in TS:
    t = mp.mpf(t)
    for sig in SIG_LO:
        d = D_chi(sig, t)
        e = E_gamma_cos(sig, t)
        v1 = abs(d) * t ** 2
        v2 = abs(d - Dcoeff(sig) / t ** 2) * t ** 3
        v3 = abs(e) * t ** 2
        sup_DE = max(sup_DE, abs(d - e))
        if v1 > sup_lo[0]:
            sup_lo = (v1, (sig, t))
        if v2 > sup_lo_t[0]:
            sup_lo_t = (v2, (sig, t))
        if v3 > sup_E[0]:
            sup_E = (v3, (sig, t))
print(f"  sup |D| t^2         = {mp.nstr(sup_lo[0], 8)} at ({mp.nstr(sup_lo[1][0],4)},{mp.nstr(sup_lo[1][1],6)})"
      f"   Lean 4 : {verdict(sup_lo[0] <= 4)}    tex 7/3 (+7.88/t)")
print(f"  sup |D - Dcoeff/t^2| t^3 = {mp.nstr(sup_lo_t[0], 8)} at ({mp.nstr(sup_lo_t[1][0],4)},{mp.nstr(sup_lo_t[1][1],6)})"
      f"   Lean/tex 7.88 : {verdict(sup_lo_t[0] <= mp.mpf('7.88'))}")
print(f"  max |Dcoeff| on [-1,0] = {mp.nstr(max(abs(Dcoeff(s)) for s in SIG_LO), 6)}  (= |Dcoeff(-1)| = 1/2)")
print(f"  gamma_cos_estimate_lower: sup |E| t^2 = {mp.nstr(sup_E[0], 8)}   Lean 4 : {verdict(sup_E[0] <= 4)}")
print(f"  |D - E| (E is exactly D rewritten via the functional equation) max = {mp.nstr(sup_DE, 5)}"
      f"   {verdict(sup_DE < mp.mpf('1e-25'))}")

# ------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("Dcoeff: the true t^-2 coefficient?  Check t^2 * D(sigma,t) -> Dcoeff(sigma) as t -> oo")
print("=" * 90)
okD = True
for sig in [0.1, 0.3, 0.5, -0.4, -1]:
    lim = D_chi(sig, mp.mpf(10) ** 6) * mp.mpf(10) ** 12
    okD = okD and abs(lim - Dcoeff(sig)) < mp.mpf('1e-4')
    print(f"  sigma={sig:>5}: t^2 D at t=1e6 = {mp.nstr(lim, 10)}   Dcoeff = {mp.nstr(Dcoeff(sig), 10)}")
print(f"  Dcoeff(sigma) = sigma(2sigma-1)(1-sigma)/12 is the exact 1/t^2 coefficient : {verdict(okD)}")
print("  (verify_Dcoeff_corrected.py reached the same conclusion; this is an independent recomputation)")
print()
print("Done.")
