#!/usr/bin/env python3
r"""
`Lemma \ref{lem:zetalessthanhalf}` (Lemma 36) and `Lemma \ref{lemma:argGamma}` (Lemma 37): the
formulas in the tex proofs, the exact `1/t²` coefficient, and the constants that the proofs
actually establish (2026-09-05; requested by the author).  The file name records an earlier
numbering, when these were Lemmas 35 and 36.

Both lemmas are PROVED in Lean (`zetalessthanhalf_upper`/`_lower` with their `_tight` and
`_collapsed` variants, from the single Stirling application `gamma_cos_estimate_general`; and
`argGamma`/`argGamma_analytic`).  Nothing here certifies a hypothesis field: this script is where
the constants those proofs print were derived and checked, and where the tex's original displays
were found to be wrong.

PART A -- the displayed formulas of the `\ref{lem:zetalessthanhalf}` proof, checked
  symbolically/numerically.
  With z_a = a + it/2, Brent's expansion  logΓ(z) = (z-1/2)log z - z + (1/2)log 2π + B₂/(2z) + R₂(z)
  gives, for the DIFFERENCE logΓ(z_a) - logΓ(z_b):
    * the "-z" terms contribute  -z_a + z_b = (b - a)          (tex had "-(b-a)");
    * 1/(a+it/2) = (a-it/2)/(a²+t²/4)                            (tex had a²-t²/4);
    * Re[(z_a - 1/2) log z_a] = (a-1/2)(log(t/2) + ½log(1+4a²/t²)) + (t/2)(arctan(2a/t) - π/2),
      so the real part of the difference is
        (a-b)log(t/2) + (a-1/2)/2·log(1+4a²/t²) - (b-1/2)/2·log(1+4b²/t²)
        + (t/2)(arctan(2a/t) - arctan(2b/t)) + (b-a) + B₂a/(2(a²+t²/4)) - B₂b/(2(b²+t²/4)) + Re(R₂(z_a)-R₂(z_b))
      (tex: no ½ on the logs, "-(t/2)(arctan - arctan)", "-(b-a)", and a²-t²/4);
    * expanding, the 1/t² coefficient is  P(a) - P(b),  P(a) := a(2a-1)(a-1)/3
      (the (a-b) from the arctan cancels the +(b-a)); the tex's "O*(8(a³-b³)/t³)" is really the
      order-1/t² arctan term -4(a³-b³)/(3t²).
  These identities are verified below to 30 digits with mpmath (R₂ computed exactly as
  loggamma minus the expansion), and the OLD formulas are shown to fail.
PART B -- with a = (1-σ)/2, b = σ/2 (tex's choice for 0 ≤ σ ≤ 1/2):  P(a) - P(b) = σ(2σ-1)(1-σ)/12 =: D(σ),
  the coefficient Lean calls `Dcoeff σ`; the same D(σ) results on [-1,0].  sup|D| = √3/216 on
  [0,1/2] (at σ = (3-√3)/6) and 1/2 on [-1,0] (at σ = -1).
PART C -- the residual  E(σ,t) := log|ζ(σ+it)| - log|ζ(1-σ+it)| - (1/2-σ)log(t/2) - (σ-1/2)log π
  (computed ζ-free via the functional equation), its true supremum·t², and the true (E - D/t²)·t³.
PART D -- the constants the PROOF gives (Brent's remainder bound (1+√(2π))|B₄|/(12|z|³) plus
  explicit Taylor remainders, t > 10):
    * asymmetric route (as in Lean `gamma_cos_estimate_general`: Stirling once, at z = 1-σ-it,
      |z| ≥ t): |E - D/t²| ≤ ((1/2-σ)(1-σ)⁴/4 + (1-σ)⁵/5 + (1-σ)³/12 + 1/100)/t⁴ + (1+√(2π))/(360t³)
      → 0.06/t³ on [0,1/2] and 1.4/t³ on [-1,0], hence  |E| ≤ (√3/216 + 0.06/t)/t²  and
      |E| ≤ (1/2 + 1.4/t)/t²  -- the constants now in the tex and proved in Lean;
    * the tex's symmetric route (two Gammas at |z| ≈ t/2) pays 2·8·(1+√(2π))/(360t³) ≈ 0.156/t³ for
      the remainders alone, so it cannot beat ≈ 0.17/t³ on [0,1/2].
PART E -- `\ref{lemma:argGamma}`: the same bookkeeping for Im, giving
  -δπ/4 + δ²/(4t) + (δ²/12 - δ⁴/24)/t³ + ...;
  the explicit part is at most 0.045/t³ (proved in Lean `argGamma_taylor_residue`), the two
  remainders at most 2·(1/100)·8/t³ = 0.16/t³ (the hypothesis field
  `BrentStirlingInputs.shifted_remainder_bound`) or 2(1+√(2π))/(45 t³) = 0.156/t³
  (Brent's constant), total 0.21/t³ = the constant now in the tex and Lean; the true supremum is
  0.0422/t³, so 0.043 was numerically right but not derivable from the cited remainder bound.

Run with:  python3 Code/indep_mpmath_lemma35_constants.py
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 40
B2 = mp.mpf(1) / 6
B4 = -mp.mpf(1) / 30


def R2(z):
    """Brent's remainder at k=2, computed exactly: lgΓ(z) - [(z-1/2)log z - z + log(2π)/2 + B₂/(2z)]."""
    return mp.loggamma(z) - ((z - mp.mpf(1) / 2) * mp.log(z) - z + mp.log(2 * mp.pi) / 2 + B2 / (2 * z))


print("=" * 92)
print("PART A: the real-part display of the Lemma 35 proof (corrected vs tex)")
print("=" * 92)
worst_new, worst_old = mp.mpf(0), mp.mpf(0)
for (a, b, t) in [(0.25, 0.1, 10), (0.5, 0, 12.5), (0.375, 0.125, 30), (1, 0.75, 10), (0.6, 0.9, 100)]:
    a, b, t = mp.mpf(a), mp.mpf(b), mp.mpf(t)
    za, zb = mp.mpc(a, t / 2), mp.mpc(b, t / 2)
    lhs = mp.re(mp.loggamma(za) - mp.loggamma(zb))
    rem = mp.re(R2(za) - R2(zb))
    new = ((a - b) * mp.log(t / 2) + (a - mp.mpf(1) / 2) / 2 * mp.log(1 + 4 * a ** 2 / t ** 2)
           - (b - mp.mpf(1) / 2) / 2 * mp.log(1 + 4 * b ** 2 / t ** 2)
           + t / 2 * (mp.atan(2 * a / t) - mp.atan(2 * b / t)) + (b - a)
           + B2 * a / (2 * (a ** 2 + t ** 2 / 4)) - B2 * b / (2 * (b ** 2 + t ** 2 / 4)) + rem)
    old = ((a - b) * mp.log(t / 2) + (a - mp.mpf(1) / 2) * mp.log(1 + 4 * a ** 2 / t ** 2)
           - (b - mp.mpf(1) / 2) * mp.log(1 + 4 * b ** 2 / t ** 2)
           - t / 2 * (mp.atan(2 * a / t) - mp.atan(2 * b / t)) - (b - a)
           + B2 * a / (2 * (a ** 2 - t ** 2 / 4)) - B2 * b / (2 * (b ** 2 - t ** 2 / 4)) + rem)
    worst_new = max(worst_new, abs(lhs - new))
    worst_old = max(worst_old, abs(lhs - old))
    print(f"  a={mp.nstr(a,4)} b={mp.nstr(b,4)} t={mp.nstr(t,5)}: |lhs - corrected| = {mp.nstr(abs(lhs-new), 3)}"
          f"   |lhs - tex display| = {mp.nstr(abs(lhs-old), 3)}")
print(f"  corrected display: exact to {mp.nstr(worst_new, 3)};  tex display: off by up to {mp.nstr(worst_old, 3)}")

print()
print("=" * 92)
print("PART B: the 1/t^2 coefficient (sympy)")
print("=" * 92)
a, b, s, t = sp.symbols('a b sigma t', positive=True)
u = sp.symbols('u')
# expand the corrected real part in 1/t (without the R2 terms) to order t^-2
expr = ((a - sp.Rational(1, 2)) / 2 * sp.log(1 + 4 * a ** 2 / t ** 2)
        - (b - sp.Rational(1, 2)) / 2 * sp.log(1 + 4 * b ** 2 / t ** 2)
        + t / 2 * (sp.atan(2 * a / t) - sp.atan(2 * b / t)) + (b - a)
        + sp.Rational(1, 6) * a / (2 * (a ** 2 + t ** 2 / 4)) - sp.Rational(1, 6) * b / (2 * (b ** 2 + t ** 2 / 4)))
ser = sp.series(expr.subs(t, 1 / u), u, 0, 4).removeO()
c2 = sp.simplify(ser.coeff(u, 2))
c0 = sp.simplify(ser.coeff(u, 0))
c1 = sp.simplify(ser.coeff(u, 1))
P = lambda x: x * (2 * x - 1) * (x - 1) / 3
print(f"  order t^0 coefficient (must vanish): {c0};  order t^-1: {c1}")
print(f"  order t^-2 coefficient: {sp.factor(c2)}")
print(f"  equals P(a) - P(b) with P(x) = x(2x-1)(x-1)/3 ? {sp.simplify(c2 - (P(a) - P(b))) == 0}")
Dsig = sp.factor((P(a) - P(b)).subs({a: (1 - s) / 2, b: s / 2}))
print(f"  with a=(1-sigma)/2, b=sigma/2:  D(sigma) = {Dsig}   (= sigma(2sigma-1)(1-sigma)/12 ? "
      f"{sp.simplify(Dsig - s*(2*s-1)*(1-s)/12) == 0})")
Dfun = s * (2 * s - 1) * (1 - s) / 12
crit = sp.solve(sp.diff(Dfun, s), s)
print(f"  critical points of D: {crit};  D there: {[sp.nsimplify(Dfun.subs(s, c)) for c in crit]}")
print(f"  sup|D| on [0,1/2] = sqrt(3)/216 = {sp.N(sp.sqrt(3)/216, 12)};  sup|D| on [-1,0] = |D(-1)| = {abs(Dfun.subs(s, -1))}")

print()
print("=" * 92)
print("PART C: true residual (zeta-free, via chi(s) = 2^s pi^(s-1) sin(pi s/2) Gamma(1-s))")
print("=" * 92)


def E_res(sig, tt):
    sig, tt = mp.mpf(sig), mp.mpf(tt)
    z = mp.mpc(sig, tt)
    logchi = sig * mp.log(2) + (sig - 1) * mp.log(mp.pi) + mp.log(abs(mp.sin(mp.pi * z / 2))) + mp.re(mp.loggamma(1 - z))
    return logchi - (mp.mpf(1) / 2 - sig) * mp.log(tt / 2) - (sig - mp.mpf(1) / 2) * mp.log(mp.pi)


def Dc(sig):
    sig = mp.mpf(sig)
    return sig * (2 * sig - 1) * (1 - sig) / 12


for (lo, hi, name) in [(0, 0.5, "[0,1/2]"), (-1, 0, "[-1,0]")]:
    s2, s3 = mp.mpf(0), mp.mpf(0)
    for i in range(0, 41):
        sig = lo + (hi - lo) * mp.mpf(i) / 40
        for tt in [10, 10.5, 12, 15, 20, 30, 50, 100, 1000, 1e5]:
            e = E_res(sig, tt)
            s2 = max(s2, abs(e) * mp.mpf(tt) ** 2)
            s3 = max(s3, abs(e - Dc(sig) / mp.mpf(tt) ** 2) * mp.mpf(tt) ** 3)
    print(f"  sigma in {name}: sup |E| t^2 = {mp.nstr(s2, 6)},  sup |E - D/t^2| t^3 = {mp.nstr(s3, 6)}")

print()
print("=" * 92)
print("PART D: constants the proof establishes for t > 10 (Brent remainder + explicit Taylor remainders)")
print("=" * 92)
sq = mp.sqrt(2 * mp.pi)
brent1 = (1 + sq) / 360            # one Stirling remainder at |z| >= t   (asymmetric route)
brent2 = 2 * 8 * (1 + sq) / 360    # two remainders at |z| >= t/2         (symmetric tex route)
print(f"  (1+sqrt(2 pi))/360 = {mp.nstr(brent1, 6)} per t^3 (asymmetric, Lean route);"
      f"  16(1+sqrt(2 pi))/360 = {mp.nstr(brent2, 6)} per t^3 (symmetric tex route)")


def taylor_num(sig):
    x = 1 - mp.mpf(sig)
    return (mp.mpf(1) / 2 - mp.mpf(sig)) * x ** 4 / 4 + x ** 5 / 5 + x ** 3 / 12 + mp.mpf(1) / 100


for (lo, hi, name, stated) in [(0, 0.5, "[0,1/2]", 0.06), (-1, 0, "[-1,0]", 1.4)]:
    tn = max(taylor_num(lo + (hi - lo) * mp.mpf(i) / 400) for i in range(401))
    c3 = tn / 10 + brent1
    print(f"  sigma in {name}: Taylor numerator <= {mp.nstr(tn, 5)} (-> /t^4 <= {mp.nstr(tn/10, 5)}/t^3 at t>10),"
          f" total 1/t^3 constant {mp.nstr(c3, 5)} <= stated {stated}: {'OK' if c3 <= stated else 'FAIL'}")
print(f"  collapsed forms: |E| <= (sqrt(3)/216 + 0.06/t)/t^2 on [0,1/2];  |E| <= (1/2 + 1.4/t)/t^2 on [-1,0]")
print(f"  (tex had (7 sqrt7/108 + 1.21/t)/t^2 = ({mp.nstr(7*mp.sqrt(7)/108, 5)} + 1.21/t)/t^2 and (7/3 + 7.88/t)/t^2,"
      f" computed from an incorrect 1/t^2 polynomial)")

print()
print("=" * 92)
print("PART E: Lemma 36 -- residual of the arg difference, and what is provable")
print("=" * 92)


def argres(d, tt):
    d, tt = mp.mpf(d), mp.mpf(tt)
    a = mp.loggamma(mp.mpc(mp.mpf(1) / 2, tt / 2)).imag
    b = mp.loggamma(mp.mpc(mp.mpf(1) / 2 + d / 2, tt / 2)).imag
    return a - b - (-d * mp.pi / 4 + d ** 2 / (4 * tt))


sup = mp.mpf(0)
for i in range(0, 61):
    d = -mp.mpf(1) / 2 + mp.mpf(3) / 2 * i / 60
    for tt in [10, 10.01, 10.5, 12, 15, 20, 50, 100, 1000]:
        sup = max(sup, abs(argres(d, tt)) * mp.mpf(tt) ** 3)
print(f"  true sup |residual| t^3 = {mp.nstr(sup, 6)} (tex's 0.043 was numerically valid)")
print(f"  explicit part: (delta^2/12 - delta^4/24)/t^3 + O(1/t^5) <= 0.045/t^3 (Lean: argGamma_taylor_residue);")
print(f"  two shifted remainders: 2*(1/100)*8 = 0.16 (Lean axiom) or 2(1+sqrt(2 pi))/45 = {mp.nstr(2*(1+sq)/45, 5)} (Brent);")
print(f"  total 0.045 + 0.16 = 0.205 <= 0.21: the constant now in the tex and proved in Lean (argGamma).")
# the B2 term of the Im display, corrected:  Im[B2/(2 z_a) - B2/(2 z_b)] = (4 B2/t^3)(a^2-b^2)/((1+4a^2/t^2)(1+4b^2/t^2))
ok = True
for (a_, b_, t_) in [(0.5, 0.75, 10), (0.5, 0.25, 30), (0.5, 1.0, 100)]:
    a_, b_, t_ = mp.mpf(a_), mp.mpf(b_), mp.mpf(t_)
    lhs = mp.im(B2 / (2 * mp.mpc(a_, t_ / 2)) - B2 / (2 * mp.mpc(b_, t_ / 2)))
    rhs = 4 * B2 / t_ ** 3 * (a_ ** 2 - b_ ** 2) / ((1 + 4 * a_ ** 2 / t_ ** 2) * (1 + 4 * b_ ** 2 / t_ ** 2))
    ok = ok and abs(lhs - rhs) < mp.mpf('1e-30')
print(f"  corrected B_2 term of the Im display, (4B_2/t^3)(a^2-b^2)/((1+4a^2/t^2)(1+4b^2/t^2)): exact? {ok}")
print()
print("Done.")
