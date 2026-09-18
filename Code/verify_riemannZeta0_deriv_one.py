#!/usr/bin/env python3
"""
Independent numeric check of the proved theorem
`Background/LogDerivZetaLaurent.hasDerivAt_riemannZeta₀_one`:

    (riemannZeta₀)'(1) = -gamma_1

where `riemannZeta₀ s = zeta(s) - 1/(s-1)` is Mathlib's pole-free part of zeta
(`riemannZeta₀_one : riemannZeta₀ 1 = eulerMascheroniConstant`), and gamma_1 is
the first Stieltjes constant.

Three independent handles on gamma_1 are compared:
  (a) mpmath's built-in `stieltjes(1)`
  (b) the LIMIT FORMULA that `Definitions.stieltjesConstant1` uses as its
      DEFINITION:  gamma_1 = lim_m [ sum_{k<=m} log(k)/k - log(m)^2/2 ]
  (c) a numerical derivative of zeta(s) - 1/(s-1) at s = 1

(a) vs (b) is the bridge the theorem supplies: it is what connects the repo's
limit-formula definition of gamma_1 to gamma_1's role as a Laurent coefficient.
(c) confirms the derivative reading.

Also reports gamma^2 + 2*gamma_1, the combination the development actually
consumes (it is the `a_1` coefficient of -zeta'/zeta at 1, exactly
`Background/LogDerivZetaLaurent.logDerivZetaCoeff_one`).

Fine-grid / finite-difference evidence, not certified interval arithmetic: it can
corroborate or contradict the Lean statement, it does not certify it.
"""

from mpmath import mp, mpf, mpc, zeta, log, euler, stieltjes, diff, nstr

mp.dps = 40

g0 = +euler
g1 = stieltjes(1)

print("gamma   =", nstr(g0, 30))
print("gamma_1 =", nstr(g1, 30))
print()

# (b) the limit formula that DEFINES `Definitions.stieltjesConstant1`
print("(b) limit formula  sum_{k<=m} log k / k  -  (log m)^2 / 2")
run = mpf(0)
prev = None
for m in range(1, 200001):
    run += log(m) / m
    if m in (10, 100, 1000, 10000, 100000, 200000):
        val = run - log(m) ** 2 / 2
        print(f"      m = {m:>7}:  {nstr(val, 20)}   (error {nstr(val - g1, 6)})")
        prev = val
print(f"      mpmath stieltjes(1) = {nstr(g1, 20)}")
print()

# (c) the derivative reading: (zeta(s) - 1/(s-1))' at s = 1
def zeta0(s):
    s = mpc(s)
    if abs(s - 1) < mpf(10) ** (-mp.dps + 5):
        return mpc(g0)
    return zeta(s) - 1 / (s - 1)

print("(c) numerical derivative of  zeta(s) - 1/(s-1)  at s = 1")
for h in ['1e-3', '1e-4', '1e-5', '1e-6']:
    hh = mpf(h)
    d = (zeta0(1 + hh) - zeta0(1 - hh)) / (2 * hh)
    print(f"      h = {h:>6}:  {nstr(d.real, 20)}   vs  -gamma_1 = {nstr(-g1, 20)}"
          f"   (diff {nstr(d.real + g1, 6)})")
print()

# also check the value at 1 itself, which Mathlib already proves
print("      zeta0(1) via limit =", nstr(zeta0(1 + mpf('1e-12')).real, 20),
      " vs gamma =", nstr(g0, 20))
print()

combo = g0 ** 2 + 2 * g1
print("The combination the development consumes:")
print("      gamma^2 + 2*gamma_1 =", nstr(combo, 30))
print("      -2*gamma_1          =", nstr(-2 * g1, 30))
print()
print("Sanity: a_1 is the coefficient in  -zeta'/zeta(1+z) = 1/z + sum (-1)^{n+1} a_n z^n.")
print("Series-free cross-check of a_1 by numerical differentiation of -zeta'/zeta:")


def negLogDeriv(z):
    s = mpc(1) + z
    return -(diff(zeta, s) / zeta(s))


# -zeta'/zeta(1+z) - 1/z  =  a_0 - a_1 z + ...   (n=0 term is +a_0, n=1 is -a_1)
# so a_1 = -d/dz [ -zeta'/zeta(1+z) - 1/z ] at z = 0
def f(z):
    return negLogDeriv(z) - 1 / z


for h in ['1e-3', '1e-4']:
    hh = mpf(h)
    d = (f(mpc(hh)) - f(mpc(-hh))) / (2 * hh)
    print(f"      h = {h:>6}:  a_1 ~ {nstr(-d.real, 20)}   vs  gamma^2+2gamma_1 = "
          f"{nstr(combo, 20)}   (diff {nstr(-d.real - combo, 6)})")
