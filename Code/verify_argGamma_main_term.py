#!/usr/bin/env python3
"""
Check the correction to the main term of `Lemma \\ref{lemma:argGamma}` (Lemma 37).

tex as first written:  arg G(1/2+it/2) - arg G(1/2+d/2+it/2)
                         =  (-d/2 - d^2)/t + O*(2/t^3)
correct:               same difference
                         =  -d*pi/4 + (d^2/4)/t + O*(0.043/t^3)

The -d*pi/4 is exactly the (a-b)*pi/2 term with a=1/4, b=1/4+d/2, which the tex's
proof drops when taking imaginary parts.  The error is a CONSTANT, not a rate: as
t -> oo the true difference tends to -d*pi/4 while the claimed term tends to 0,
so no choice of the O*-constant can rescue the original statement.

The corrected main term is what Lean proves, as `argGamma_analytic` in
`ZerosInShortIntervals/Background/BackgroundZetaBounds.lean`.  The 0.043/t^3 above is
the corrected tex's constant, essentially the observed supremum (0.04218, at
d = 1, t = 10) of the whole residual; Lean's proved constant is the weaker
0.21/t^3, because Brent's stated remainder bound cannot reach 0.043.  So this
script is an independent numeric check of a proved theorem, not a certificate of
any hypothesis-class field.

Uses mpmath `loggamma` at 30 digits -- the ANALYTIC log-Gamma, which does not
wrap -- so this isolates the main-term question from the separate branch
question.  The second half then shows why the branch question really is separate:
the principal-argument difference wraps by 2*pi on a set of t of density
|difference|/(2 pi), which is why the Lean statement is about `logGammaAnalytic`
and not about `Complex.arg`.

Grids: d in {1, 0.5, -0.5} at t in {100, 1000, 10000}, then t = 1e6 for the
limit; the branch scan is d = 0.05 at five t near 10.
"""

from mpmath import mp, mpf, mpc, loggamma, gamma, arg, pi, nstr, fabs

mp.dps = 30


def analytic_diff(d, t):
    z1 = mpc(mpf(1) / 2, t / 2)
    z2 = mpc(mpf(1) / 2 + d / 2, t / 2)
    return (loggamma(z1) - loggamma(z2)).imag


def tex_claim(d, t):
    return (-d / 2 - d ** 2) / t


def corrected(d, t):
    return -d * pi / 4 + (d ** 2 / 4) / t


print("ANALYTIC difference (no wrapping) vs the two candidate main terms")
print()
for d in ['1', '0.5', '-0.5']:
    dd = mpf(d)
    print(f"delta = {d}")
    print(f"{'t':>8} {'true (analytic)':>20} {'tex claim':>16} {'corrected':>16} "
          f"{'|true-corr|*t^3':>18}")
    for t in ['100', '1000', '10000']:
        tt = mpf(t)
        tr = analytic_diff(dd, tt)
        print(f"{t:>8} {nstr(tr, 12):>20} {nstr(tex_claim(dd, tt), 8):>16} "
              f"{nstr(corrected(dd, tt), 8):>16} "
              f"{nstr(fabs(tr - corrected(dd, tt)) * tt ** 3, 6):>18}")
    print()

print("The tex's error is a CONSTANT, not a rate: as t -> oo the true difference")
print("tends to -delta*pi/4 while the claimed term tends to 0.")
print()
for d in ['1', '0.5']:
    dd = mpf(d)
    tt = mpf('1e6')
    print(f"  delta={d}: true -> {nstr(analytic_diff(dd, tt), 10)}, "
          f"-delta*pi/4 = {nstr(-dd * pi / 4, 10)}, tex claim -> "
          f"{nstr(tex_claim(dd, tt), 6)}")

print()
print("=" * 72)
print("Now the SEPARATE branch question: does the 2*pi wrap cancel in the")
print("difference, since both points are at the same height t?")
print()
print("Answer: only when no branch cut falls BETWEEN the two points.  The")
print("individual values Im log G ~ (t/2)log(t/2) are huge and wrap at different")
print("t for the two points, so the principal-arg difference jumps by 2*pi on a")
print("set of t of density ~ |analytic difference| / (2*pi).")
print()
d = mpf('0.05')
print(f"delta = {d}, scanning t near a crossing:")
print(f"{'t':>10} {'analytic diff':>18} {'principal arg diff':>20} {'wrapped?':>10}")
for t in ['10.00', '10.04', '10.06', '10.08', '10.20']:
    tt = mpf(t)
    z1 = mpc(mpf(1) / 2, tt / 2)
    z2 = mpc(mpf(1) / 2 + d / 2, tt / 2)
    an = (loggamma(z1) - loggamma(z2)).imag
    pr = arg(gamma(z1)) - arg(gamma(z2))
    wrapped = fabs(pr - an) > 1
    print(f"{t:>10} {nstr(an, 8):>18} {nstr(pr, 8):>20} {str(wrapped):>10}")
print()
print(f"predicted density of wrapped t ~ |diff|/(2pi) = "
      f"{nstr(fabs(-d * pi / 4) / (2 * pi), 4)}  (i.e. delta/8)")
