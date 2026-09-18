#!/usr/bin/env python3
"""Numerical audit of Lemma \\ref{lemma:argGamma} (Lemma 37) and of the shifted
Brent-Stirling expansion that its proof needs.

Everything below is mpmath at 40 digits on sampled grids -- no ball arithmetic --
so the numbers are evidence, not certificates.

Lean now proves the lemma outright, on the analytic branch `logGammaAnalytic`
rather than on `Complex.arg`: `argGamma_im_diff` (the exact Im-difference
identity), `argGamma_taylor_residue` and `_sharp` (the pure-real Taylor residue),
and `argGamma_analytic` (the assembled `-d*pi/4 + d^2/(4t) + O*(0.21/t^3)`), all
in `ZerosInShortIntervals/Background/BackgroundZetaBounds.lean`.  Sections (A)-(F)
and (H) are therefore independent numeric checks of proved theorems.  The one
exception is section (G), which is numeric evidence for the hypothesis field
`BrentStirlingInputs.shifted_remainder_bound`.

Sections, and what each answers.

(A)/(B)  Is the tex's *analytic* claim true?  With arg = Im log Gamma taken on
     the continuous branch (loggamma, not the principal argument),

         Im logGamma(1/2 + i t/2) - Im logGamma(1/2 + d/2 + i t/2)
             - (-d/2 - d^2)/t          =?  O*(2/t^3)

     tabulated at d in {-1/2,-1/4,1/4,1/2,1} and t in {10.5,20,100,1000,10000}.
     It is not: the tex's main term is wrong by a CONSTANT.  The correct main
     term, tabulated alongside, is  -d*pi/4 + (d^2/4)/t + O(1/t^3).

(B2) The tex's own displayed imaginary part term by term, at a = 1/4 (the value
     its proof takes) and a = 1/2 (the value its statement needs).  The dropped
     (a-b)pi/2 contribution is exactly the -d*pi/4 above.

(C)  Is the claim true for the PRINCIPAL argument, `Complex.arg`, range
     (-pi, pi]?  No: arg Gamma(1/2+it/2) grows like (t/2)log(t/2) and wraps at
     different t for the two points, so the principal difference jumps by 2*pi on
     a set of t of positive density.  That is why the Lean statement is about
     `logGammaAnalytic`.  Scan at d = 0.05 over t in [10.01, 40) in steps of
     0.01, then refined in steps of 0.002 around the worst t.

(D)  Sanity check of the shifted Stirling expansion

         logGamma(z + 1/2) = z log z - z + (1/2) log(2 pi) - 1/(24 z) + R3(z),
         |R3(z)| decaying like |z|^{-3},

     The expansion itself is definitional once R3 is DEFINED as the truncation
     error of `BrentStirlingInputs.shifted_expansion` (Brent Eq. (3.4) at k = 2);
     what has content is R3's size, so this reports |R3| and |R3|*|z|^3 at ten
     sample z, against the next classical term 7/(2880 z^3).

(E)  Why the unshifted expansion cannot be stated with
     `Complex.log (Complex.Gamma z)`: with the principal log on the left, R2 is
     forced to be a nonzero multiple of 2*pi*i, while
     `BrentStirlingInputs.remainder_bound` says it is of size ~1e-5.  The same
     residual on the continuous branch is tiny.  This is the reason
     `logGammaAnalytic` exists.

(F)  The corrected statement swept: d in [-1/2, 1] in steps of 0.05, t from
     10.0001 to 400 geometrically (ratio 1.15).  Reports max |residual|*t^3, and
     the closed form d^2/12 - d^4/24 of the 1/t^3 coefficient, whose maximum over
     |d| <= 1 is 1/24 = 0.041667.

(G)  `BrentStirlingInputs.shifted_remainder_bound`:
     ||R3(z)|| <= (1/100)/||z||^3 for |Re z| <= 1, Im z > 5.  Swept over
     Re z in [-1, 1] in steps of 0.05 and Im z from 5.0001 to 1e5 geometrically
     (ratio 1.3), then at the two points argGamma actually uses at t just above 10.

(H)  The two ingredients of `argGamma_analytic`, checked directly:
     (H1) the exact identity of `argGamma_im_diff` -- at dps 40 anything ~1e-35
          is exact;
     (H2) `argGamma_taylor_residue`, |E(d,t)| <= 1/t^3 for |d| <= 1, t > 10,
          swept in d by 0.02 and in t geometrically (ratio 1.1) up to 1e5;
     (H3) the assembled residual over d in [-1/2, 1] on that same t sweep,
          measured against the tex's constant 2/t^3.  Lean proves 0.21/t^3.

Run:  python3 Code/verify_argGamma.py
"""

import mpmath as mp

mp.mp.dps = 40


def imloggamma(a, t):
    """Im log Gamma(a + i t/2) on the continuous (loggamma) branch."""
    return mp.im(mp.loggamma(mp.mpf(a) + 1j * mp.mpf(t) / 2))


def claimed(d, t):
    return (-mp.mpf(d) / 2 - mp.mpf(d) ** 2) / mp.mpf(t)


def predicted(d, t):
    """-d*pi/4 + (d^2/4)/t"""
    d = mp.mpf(d)
    t = mp.mpf(t)
    return -d * mp.pi / 4 + (d ** 2 / 4) / t


print("=" * 78)
print("(A)/(B)  continuous branch:  D(d,t) = Im logG(1/2+it/2) - Im logG(1/2+d/2+it/2)")
print("=" * 78)
print(f"{'d':>6} {'t':>10} {'D':>18} {'claimed':>14} {'|D-claimed|':>14} "
      f"{'predicted':>14} {'|D-pred|*t^3':>14}")
for d in [-0.5, -0.25, 0.25, 0.5, 1.0]:
    for t in [10.5, 20, 100, 1000, 10000]:
        D = imloggamma(0.5, t) - imloggamma(0.5 + d / 2, t)
        c = claimed(d, t)
        p = predicted(d, t)
        print(f"{d:>6} {t:>10} {mp.nstr(D, 12):>18} {mp.nstr(c, 8):>14} "
              f"{mp.nstr(abs(D - c), 8):>14} {mp.nstr(p, 8):>14} "
              f"{mp.nstr(abs(D - p) * mp.mpf(t) ** 3, 8):>14}")
    print()

print("=> if column |D-claimed| does not go to 0 (and beat 2/t^3), the tex")
print("   statement of Lemma 36 is FALSE on the continuous branch.")
print("   2/t^3 at t=10.5 is", mp.nstr(2 / mp.mpf(10.5) ** 3, 8),
      "; at t=100 is", mp.nstr(2 / mp.mpf(100) ** 3, 8))
print()

print("=" * 78)
print("(B2)  the tex's own displayed imaginary part, term by term, at a=1/4")
print("=" * 78)
# tex proof takes a = 1/4, b = 1/4 + d/2 (i.e. Gamma(s/2) on the critical line).
# Full correct imaginary part of Brent (2.1) difference:
#   (a-1/2)(pi/2 - arctan(2a/t)) + (t/4)log(1+4a^2/t^2)  -  [same with b]
for (a0, name) in [(0.25, "a=1/4  (tex proof)"), (0.5, "a=1/2  (lemma statement)")]:
    print(name)
    for d in [-0.5, 0.5, 1.0]:
        t = mp.mpf(1000)
        a = mp.mpf(a0)
        b = mp.mpf(a0) + mp.mpf(d) / 2
        exact = imloggamma(a, t) - imloggamma(b, t)
        const = (a - b) * mp.pi / 2
        oneovert = (a * (1 - a) - b * (1 - b)) / t
        print(f"   d={d:>5}  exact={mp.nstr(exact, 12):>16}  "
              f"const=(a-b)pi/2={mp.nstr(const, 10):>12}  "
              f"1/t term={mp.nstr(oneovert, 10):>12}  "
              f"residual*t^3={mp.nstr((exact - const - oneovert) * t ** 3, 8)}")
    print()

print("=" * 78)
print("(C)  principal branch: Complex.arg, range (-pi, pi]")
print("=" * 78)
print("arg Gamma(1/2+it/2) principal, for a few t -- it wraps many times:")
for t in [10.5, 12, 20, 50]:
    z = mp.gamma(mp.mpf(0.5) + 1j * mp.mpf(t) / 2)
    print(f"   t={t:>6}  Im logGamma = {mp.nstr(imloggamma(0.5, t), 10):>14}"
          f"   principal arg = {mp.nstr(mp.arg(z), 10):>14}")
print()
print("search for t > 10 where the principal-arg difference jumps by ~2pi")
print("(the true continuous difference is tiny, so a jump refutes the Lean form):")


def principal_diff(d, t):
    z0 = mp.gamma(mp.mpf(0.5) + 1j * mp.mpf(t) / 2)
    z1 = mp.gamma(mp.mpf(0.5) + mp.mpf(d) / 2 + 1j * mp.mpf(t) / 2)
    return mp.arg(z0) - mp.arg(z1)


# For fixed small d, scan t and record the worst |principal_diff - claimed|.
worst = None
d = mp.mpf("0.05")
t = mp.mpf("10.01")
while t < 40:
    v = principal_diff(d, t) - claimed(d, t)
    if worst is None or abs(v) > abs(worst[1]):
        worst = (t, v)
    t += mp.mpf("0.01")
print(f"   d=0.05, t in [10.01,40): worst |principal_diff - claimed| = "
      f"{mp.nstr(abs(worst[1]), 10)} at t={mp.nstr(worst[0], 10)}")
print(f"   bound claimed there: 2/t^3 = {mp.nstr(2 / worst[0] ** 3, 8)}")
print()
print("   refined near that t:")
t = worst[0] - mp.mpf("0.01")
while t < worst[0] + mp.mpf("0.01"):
    v = principal_diff(d, t)
    print(f"      t={mp.nstr(t, 12):>16}  principal diff = {mp.nstr(v, 10):>16}"
          f"   continuous diff = "
          f"{mp.nstr(imloggamma(0.5, t) - imloggamma(0.5 + d / 2, t), 10)}")
    t += mp.mpf("0.002")
print()

print("=" * 78)
print("(D)  shifted Stirling:  logGamma(z+1/2) = z log z - z + (1/2)log(2pi)")
print("                        - 1/(24 z) + R3(z)")
print("=" * 78)
print(f"{'z':>26} {'|R3(z)|':>16} {'|R3| * |z|^3':>16}")
for z in [mp.mpf(1), mp.mpf(2), mp.mpf(10), mp.mpf(100),
          mp.mpf(1) + 5j, mp.mpf("0.25") + 5j, mp.mpf("0.25") + 500j,
          mp.mpf("0.01") + 50j, 1j * mp.mpf(5), 1j * mp.mpf(500)]:
    z = mp.mpmathify(z)
    lhs = mp.loggamma(z + mp.mpf(1) / 2)
    rhs = z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z)
    R3 = lhs - rhs
    print(f"{mp.nstr(z, 8):>26} {mp.nstr(abs(R3), 8):>16} "
          f"{mp.nstr(abs(R3) * abs(z) ** 3, 8):>16}")
print()
print("classical next term is  +7/(2880 z^3)  (k=2 term of the shifted series)")
print("7/2880 =", mp.nstr(mp.mpf(7) / 2880, 8))
print()

print("=" * 78)
print("(E)  Is ExternalFacts.brent_stirling_expansion + _remainder_bound consistent?")
print("=" * 78)
print("Lean's `Complex.log` is the PRINCIPAL branch, so")
print("   (Complex.log (Complex.Gamma z)).im = Complex.arg (Gamma z) in (-pi, pi],")
print("while the RHS (z-1/2)log z - z + (1/2)log(2pi) + B2/(2z) has im ~ (t/2)log(t/2).")
print("So R2(z) forced by the expansion is ~ 2 pi i k, but the bound says it is tiny.")
print()
B2 = mp.mpf(1) / 6
B4 = -mp.mpf(1) / 30
print(f"{'z':>20} {'|R2| forced (principal)':>26} {'bound |(1+s2pi)B4/(12z^3)|':>28}")
for t in [10.5, 20, 100, 1000]:
    z = mp.mpf("0.5") + 1j * mp.mpf(t) / 2
    lhs = mp.log(mp.gamma(z))            # principal Complex.log of Gamma z
    rhs = (z - mp.mpf("0.5")) * mp.log(z) - z + mp.log(2 * mp.pi) / 2 + B2 / (2 * z)
    R2 = lhs - rhs
    bnd = abs((1 + mp.sqrt(2 * mp.pi)) * B4 / (12 * z ** 3))
    print(f"{mp.nstr(z, 8):>20} {mp.nstr(abs(R2), 10):>26} {mp.nstr(bnd, 10):>28}")
print()
print("(compare: with the CONTINUOUS branch loggamma the same residual is tiny)")
for t in [10.5, 100]:
    z = mp.mpf("0.5") + 1j * mp.mpf(t) / 2
    lhs = mp.loggamma(z)
    rhs = (z - mp.mpf("0.5")) * mp.log(z) - z + mp.log(2 * mp.pi) / 2 + B2 / (2 * z)
    print(f"   z={mp.nstr(z, 8):>16}  |R2 continuous| = {mp.nstr(abs(lhs - rhs), 10)}")
print()

print("=" * 78)
print("(F)  the CORRECTED Lemma 36:  D(d,t) = -d*pi/4 + (d^2/4)/t + O*(C/t^3)")
print("     sweep d in [-1/2,1], t in (10, 400]; report max |residual| * t^3")
print("=" * 78)
worstF = (0, 0, mp.mpf(0))
d = mp.mpf("-0.5")
while d <= mp.mpf("1.0") + mp.mpf("1e-9"):
    t = mp.mpf("10.0001")
    while t <= 400:
        D = imloggamma(0.5, t) - imloggamma(0.5 + d / 2, t)
        r = abs(D - predicted(d, t)) * t ** 3
        if r > worstF[2]:
            worstF = (d, t, r)
        t = t * mp.mpf("1.15")
    d += mp.mpf("0.05")
print(f"   max |residual|*t^3 = {mp.nstr(worstF[2], 10)}  at d={mp.nstr(worstF[0], 6)}, "
      f"t={mp.nstr(worstF[1], 8)}")
print("   => the corrected statement holds with the paper's own constant 2 to spare")
print("      (and even with constant 1/20).")
print()
print("   asymptotic check of the 1/t^3 coefficient, at t=10^4:")
for d in [-0.5, 0.5, 1.0]:
    t = mp.mpf(10000)
    D = imloggamma(0.5, t) - imloggamma(0.5 + mp.mpf(d) / 2, t)
    print(f"      d={d:>5}  (D - predicted)*t^3 = "
          f"{mp.nstr((D - predicted(d, t)) * t ** 3, 10)}")
print()
print("   closed form of that 1/t^3 coefficient: d^2/12 - d^4/24")
for d in [-0.5, 0.5, 1.0]:
    d = mp.mpf(d)
    print(f"      d={mp.nstr(d, 4):>5}  d^2/12 - d^4/24 = "
          f"{mp.nstr(d ** 2 / 12 - d ** 4 / 24, 10)}")
print("   max over |d| <= 1 is 1/24 =", mp.nstr(mp.mpf(1) / 24, 8))
print()

print("=" * 78)
print("(G)  remainder bound for the AXIOM's domain: |Re z| <= 1, Im z > 5")
print("     claim to axiomatize:  ||R3(z)|| <= (1/100)/||z||^3")
print("=" * 78)
worstG = (None, mp.mpf(0))
u = mp.mpf(-1)
while u <= mp.mpf(1) + mp.mpf("1e-9"):
    y = mp.mpf("5.0001")
    while y <= 100000:
        z = u + 1j * y
        R3 = mp.loggamma(z + mp.mpf(1) / 2) - (
            z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z))
        r = abs(R3) * abs(z) ** 3
        if r > worstG[1]:
            worstG = (z, r)
        y = y * mp.mpf("1.3")
    u += mp.mpf("0.05")
print(f"   max ||R3(z)|| * ||z||^3 = {mp.nstr(worstG[1], 10)}  at z = "
      f"{mp.nstr(worstG[0], 8)}")
print("   axiom constant 1/100 = 0.01, so the axiom has a factor",
      mp.nstr(mp.mpf("0.01") / worstG[1], 6), "of margin.")
print()
print("   the two points actually used, at t just above 10:")
for d in [-0.5, 0.0, 1.0]:
    t = mp.mpf("10.0001")
    for z in [1j * t / 2, mp.mpf(d) / 2 + 1j * t / 2]:
        R3 = mp.loggamma(z + mp.mpf(1) / 2) - (
            z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z))
        print(f"      d={d:>5}  z={mp.nstr(z, 8):>18}  ||R3||={mp.nstr(abs(R3), 8):>14}"
              f"   (1/100)/||z||^3 = {mp.nstr(mp.mpf('0.01') / abs(z) ** 3, 8)}")
print()


def R3(z):
    """R3(z) = logGamma(z+1/2) - (z log z - z + (1/2)log 2pi - 1/(24 z))."""
    return mp.loggamma(z + mp.mpf(1) / 2) - (
        z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z))


print("=" * 78)
print("(H)  EXACT check of the two Lean `sorry`s that argGamma_analytic rests on")
print("=" * 78)
print("(H1) argGamma_im_diff -- an EXACT identity, must hold to machine precision:")
print("     im logGA(1/2+it/2) - im logGA(1/2+d/2+it/2)")
print("       = -d*pi/4 + (d/2)arctan(d/t) - (t/4)log(1+d^2/t^2) + d^2/(12 t (d^2+t^2))")
print("         + im R3(it/2) - im R3(d/2+it/2)")
print()
print(f"{'d':>7} {'t':>10} {'LHS - RHS (should be 0)':>28}")
worstH1 = mp.mpf(0)
for d in [-0.5, -0.25, 0.0, 0.25, 0.5, 1.0, 0.7]:
    for t in [10.0001, 10.5, 37, 1000]:
        d_ = mp.mpf(d)
        t_ = mp.mpf(t)
        z0 = 1j * t_ / 2
        z1 = d_ / 2 + 1j * t_ / 2
        lhs = mp.im(mp.loggamma(mp.mpf(1) / 2 + 1j * t_ / 2)) - mp.im(
            mp.loggamma(mp.mpf(1) / 2 + d_ / 2 + 1j * t_ / 2))
        rhs = (-d_ * mp.pi / 4 + d_ / 2 * mp.atan(d_ / t_)
               - t_ / 4 * mp.log(1 + d_ ** 2 / t_ ** 2)
               + d_ ** 2 / (12 * t_ * (d_ ** 2 + t_ ** 2))
               + mp.im(R3(z0)) - mp.im(R3(z1)))
        diff = abs(lhs - rhs)
        if diff > worstH1:
            worstH1 = diff
        print(f"{d:>7} {t:>10} {mp.nstr(diff, 8):>28}")
print(f"   worst = {mp.nstr(worstH1, 8)}   (mp.dps = {mp.mp.dps}; anything ~1e-35 is exact)")
print()

print("(H2) argGamma_taylor_residue -- claim  |E(d,t)| <= 1/t^3  for |d|<=1, t>10, where")
print("     E = (d/2)arctan(d/t) - (t/4)log(1+d^2/t^2) - d^2/(4t) + d^2/(12 t (d^2+t^2))")
worstH2 = (None, None, mp.mpf(0))
d = mp.mpf(-1)
while d <= mp.mpf(1) + mp.mpf("1e-9"):
    t = mp.mpf("10.0001")
    while t <= 100000:
        E = (d / 2 * mp.atan(d / t) - t / 4 * mp.log(1 + d ** 2 / t ** 2)
             - d ** 2 / (4 * t) + d ** 2 / (12 * t * (d ** 2 + t ** 2)))
        r = abs(E) * t ** 3
        if r > worstH2[2]:
            worstH2 = (d, t, r)
        t = t * mp.mpf("1.1")
    d += mp.mpf("0.02")
print(f"   max |E| * t^3 = {mp.nstr(worstH2[2], 10)}  at d={mp.nstr(worstH2[0], 6)}, "
      f"t={mp.nstr(worstH2[1], 8)}")
print("   claim needs <= 1.  (hand chain gives 1/6 + 1/4 + 1/12 = 1/2)")
print()
print("(H3) the assembled bound of argGamma_analytic, |...| <= 2/t^3, measured directly:")
worstH3 = (None, None, mp.mpf(0))
d = mp.mpf("-0.5")
while d <= mp.mpf(1) + mp.mpf("1e-9"):
    t = mp.mpf("10.0001")
    while t <= 100000:
        D = imloggamma(0.5, t) - imloggamma(0.5 + d / 2, t)
        r = abs(D - (-d * mp.pi / 4 + d ** 2 / (4 * t))) * t ** 3
        if r > worstH3[2]:
            worstH3 = (d, t, r)
        t = t * mp.mpf("1.1")
    d += mp.mpf("0.02")
print(f"   max |residual| * t^3 = {mp.nstr(worstH3[2], 10)}  at d={mp.nstr(worstH3[0], 6)}, "
      f"t={mp.nstr(worstH3[1], 8)}   (claim needs <= 2)")

