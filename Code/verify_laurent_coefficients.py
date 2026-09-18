"""Compute the Laurent coefficients a_n of -zeta'/zeta(1+z) - 1/z = sum (-1)^(n+1) a_n z^n.

Independent numeric check (mpmath, 40 digits) of facts that
ZerosInShortIntervals/Background/LogDerivZetaLaurent.lean now PROVES outright, for
Lemma \\ref{lemma:logderzetabound} (Lemma 38):

  * a_0 = gamma (Euler-Mascheroni) to 40 digits -- the exact identity
    `logDerivZetaCoeff_zero`, and a strong end-to-end check that the sign convention and the
    whole G-construction in the Lean file are right.
  * a_1 = gamma^2 + 2*gamma_1 (true value 0.187546232840365224597...) --
    `logDerivZetaCoeff_one`.  The table below prints a_1 to 12 places; the contour is computed
    at 40.
  * claim 1, |a_n - (3^{-n-1}+5^{-n-1}+7^{-n-1})| <= 0.6*7^{-n} for n >= 1 --
    `logDerivZetaCoeff_bound`.
  * a_n > 0 for 1 <= n <= 15 -- `logDerivZetaCoeff_pos`.
  * a_n * 2^n antitone for 0 <= n <= 15 -- `logDerivZetaCoeff_antitone`, via
    `logDerivZetaCoeff_two_mul_succ_le_all`.

It also shows explicitly WHERE claim 1's crude bound runs out: the bound decides positivity at
every n >= 1, but decides the antitone step only from n >= 2 -- the sharpness recorded in
`logDerivZetaCoeff_two_mul_succ_le`'s docstring.  The Lean closes the two remaining steps
without any further numeric input of this kind: n = 0 -> 1 from the exact identity a_0 = gamma,
and n = 1 -> 2 from the certified bracket 0.15 <= a_1 <= 0.20
(`logDerivZetaCoeff_one_bounds`, resting on `stieltjes_combo_numeric_bounds`).

Fine-grid contour evaluation, not certified interval arithmetic.


Convention matches ZerosInShortIntervals/Background/LogDerivZetaLaurent.lean and
verify_lemmaA7_bound_radius7.sage:
    G(z) = -zeta'/zeta(1+z) - 1/z + 1/(z+3) + 1/(z+5) + 1/(z+7)
and  f(z) := -zeta'/zeta(1+z) - 1/z = sum_{n>=0} b_n z^n  with  b_n = (-1)^(n+1) a_n.

f is analytic in |z| < 3 (nearest singularity: the trivial zero s=-2, i.e. z=-3; the
lowest nontrivial zero sits at |z| ~ 14.13).  We recover b_n by a Cauchy contour integral
on |z| = r with r = 1, sampled at M equally spaced points (trapezoid rule = exact up to
aliasing error ~ b_{n+M} r^M, utterly negligible here since b_m ~ 3^{-m} and r = 1).
"""
import mpmath as mp

mp.mp.dps = 40

R = mp.mpf(1)      # contour radius
M = 128            # sample points
NMAX = 15


def f(z):
    s = mp.mpc(1) + z
    return -(mp.zeta(s, derivative=1) / mp.zeta(s)) - 1 / z


print("sampling f on |z| = %s at %d points ..." % (R, M))
samples = []
for k in range(M):
    theta = 2 * mp.pi * k / M
    samples.append(f(R * mp.exp(1j * theta)))

b = []
for n in range(NMAX + 1):
    acc = mp.mpc(0)
    for k in range(M):
        theta = 2 * mp.pi * k / M
        acc += samples[k] * mp.exp(-1j * n * theta)
    b.append(acc / M / (R ** n))

# a_n = (-1)^(n+1) b_n
a = [((-1) ** (n + 1)) * b[n] for n in range(NMAX + 1)]

print()
print("Check imaginary parts are ~0 (Schwarz reflection => real coefficients):")
print("  max |Im a_n| =", max(abs(mp.im(x)) for x in a))
print()

a = [mp.re(x) for x in a]

print("a_0 =", a[0], "   (gamma =", mp.euler, ")")
print("  a_0 - gamma =", a[0] - mp.euler)
print()


def S(n):
    return mp.mpf(3) ** (-n - 1) + mp.mpf(5) ** (-n - 1) + mp.mpf(7) ** (-n - 1)


print("%-3s %-24s %-24s %-14s %-14s" % ("n", "a_n", "S_n", "a_n - S_n", "0.6*7^-n"))
for n in range(NMAX + 1):
    err = a[n] - S(n)
    print("%-3d %-24s %-24s %-14s %-14s" % (
        n, mp.nstr(a[n], 12), mp.nstr(S(n), 12), mp.nstr(err, 6),
        mp.nstr(mp.mpf('0.6') * mp.mpf(7) ** (-n), 6)))

print()
print("(i)  a_0 > 0 :", a[0] > 0)
print("(ii) a_n > 0 for 1<=n<=%d :" % NMAX, all(a[n] > 0 for n in range(1, NMAX + 1)))
print("     claim-1 bound alone forces a_n >= S_n - 0.6*7^-n; is that > 0?")
for n in range(1, 8):
    lo = S(n) - mp.mpf('0.6') * mp.mpf(7) ** (-n)
    print("       n=%d: S_n - 0.6*7^-n = %s  (>0: %s)" % (n, mp.nstr(lo, 8), lo > 0))

print()
print("(iii) is a_n * 2^n antitone (a_{n+1}*2 <= a_n)?   [x=2, the hardest endpoint]")
for n in range(0, NMAX):
    lhs = 2 * a[n + 1]
    rhs = a[n]
    print("       n=%d -> %d:  2*a_{n+1} = %s   a_n = %s   holds: %s" % (
        n, n + 1, mp.nstr(lhs, 10), mp.nstr(rhs, 10), lhs <= rhs))

print()
print("      does the CRUDE claim-1 bound alone give it?  need 2*(S_{n+1}+0.6*7^-(n+1)) <= S_n - 0.6*7^-n")
for n in range(1, 8):
    lhs = 2 * (S(n + 1) + mp.mpf('0.6') * mp.mpf(7) ** (-n - 1))
    rhs = S(n) - mp.mpf('0.6') * mp.mpf(7) ** (-n)
    print("       n=%d: lhs=%s rhs=%s  crude-bound-suffices: %s" % (
        n, mp.nstr(lhs, 8), mp.nstr(rhs, 8), lhs <= rhs))
