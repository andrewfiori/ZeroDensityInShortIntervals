"""Is the tex's 2N+1 indexing in claim 2 of `Lemma \\ref{lemma:logderzetabound}` (Lemma 38)
really WEAKER than the Lean's 2N-1?

-zeta'/zeta(1+z) = 1/z + sum_{n>=0} (-1)^{n+1} a_n z^n.
Partial sums   S_m(x) = 1/x + sum_{n=0}^{m} (-1)^{n+1} a_n x^n,  with S_{-1} = 1/x.

tex  claim 2:  S_{2N}   <  L  <  S_{2N+1}
Lean claim 2:  S_{2N}   <  L  <  S_{2N-1}

Both are valid iff odd-index partial sums lie above L and even ones below. The question is
which UPPER bound is tighter: S_{2N+1} or S_{2N-1}?  The last block asks the companion
question of whether the tex's own "any N >= 0" admits N = 0, where the tex's upper bound is
S_1 and the Lean's is the empty sum S_{-1} = 1/x.

Method: mpmath at 40 digits.  The Taylor coefficients a_n are obtained by numerical Cauchy
integration on |z| = 1/2 up to n = 8, so they are quadrature values and nothing here is
certified; a_0 and a_1 are cross-checked against gamma and gamma^2 + 2 gamma_1, which Lean
proves exactly (`logDerivZetaCoeff_zero`, `logDerivZetaCoeff_one`).

This script certifies nothing; it only compares two indexings.  All three claims of Lemma 38
are proved in Lean as `LogDerivZetaLaurent.logderzetabound` (with the N = 1 upper bound
extracted as `neg_logDeriv_zeta_bound_of_claim_two`), resting on the single hypothesis field
`LaurentCertificate.logDerivZetaG_boundary_bound` -- and that field is certified by other
scripts, `Code/indep_mpmath_lemma37.py` and `Code/verify_lemmaA7_bound_radius7.sage`, not by
this one.
"""
import mpmath as mp

mp.mp.dps = 40

def g(z):
    """-zeta'/zeta(1+z) - 1/z, analytic at 0."""
    if abs(z) < mp.mpf('1e-25'):
        return -mp.euler
    s = 1 + z
    return -mp.zeta(s, derivative=1) / mp.zeta(s) - 1 / z

# Taylor coefficients of g at 0 via Cauchy integral on |z| = 1/2
R = mp.mpf('0.5')
NMAX = 8
c = []
for n in range(NMAX + 1):
    val = mp.quad(lambda t: g(R * mp.expj(t)) * mp.expj(-n * t), [0, 2 * mp.pi]) / (2 * mp.pi * R**n)
    c.append(val.real)
a = [(-1)**(n + 1) * c[n] for n in range(NMAX + 1)]

print("Laurent coefficients a_n of -zeta'/zeta(1+z):")
for n in range(5):
    print(f"  a_{n} = {mp.nstr(a[n], 15)}")
print(f"\n  gamma            = {mp.nstr(mp.euler, 15)}   (should equal a_0)")
g1 = mp.mpf('-0.0728158454836767248605863758749013191377363383343')
print(f"  gamma^2+2gamma_1 = {mp.nstr(mp.euler**2 + 2*g1, 15)}   (should equal a_1)")
print(f"  a_0/a_1          = {mp.nstr(a[0]/a[1], 10)}  <- if > 2, S_1 < 1/x on all of (0,2]")

def S(m, x):
    """Partial sum S_m; m = -1 gives the empty sum, i.e. 1/x."""
    tot = 1 / x
    for n in range(0, m + 1):
        tot += (-1)**(n + 1) * a[n] * x**n
    return tot

def L(x):
    return -mp.zeta(1 + x, derivative=1) / mp.zeta(1 + x)

print("\n" + "=" * 78)
print("Claim 2 upper bounds, N = 0 and N = 1.  Tighter = smaller (both must exceed L).")
print("=" * 78)
print(f"{'x':>6} {'L(x)':>16} {'tex S_2N+1':>16} {'Lean S_2N-1':>16}  {'tighter':>10}")
for N in (0, 1):
    print(f"-- N = {N} --")
    for x in ['0.01', '0.1', '0.5', '1.0', '2.0']:
        x = mp.mpf(x)
        lv, tex_u, lean_u = L(x), S(2*N + 1, x), S(2*N - 1, x)
        ok = "tex" if tex_u < lean_u else "Lean"
        valid = "" if (lv < tex_u and lv < lean_u) else "   <-- A BOUND FAILS"
        print(f"{mp.nstr(x,4):>6} {mp.nstr(lv,12):>16} {mp.nstr(tex_u,12):>16} "
              f"{mp.nstr(lean_u,12):>16}  {ok:>10}{valid}")

print("\n" + "=" * 78)
print("Does the tex admit N = 0?  The tex reads 'for any x in [0,2] and any N >= 0'.")
print("At N=0 the tex's upper bound is S_1 and the Lean's is S_-1 = 1/x.")
print("=" * 78)
for x in ['0.01', '0.5', '2.0']:
    x = mp.mpf(x)
    print(f"  x={mp.nstr(x,4):>5}   S_1 = {mp.nstr(S(1,x),12):>14}   "
          f"1/x = {mp.nstr(1/x,12):>14}   S_1 < 1/x: {S(1,x) < 1/x}")
