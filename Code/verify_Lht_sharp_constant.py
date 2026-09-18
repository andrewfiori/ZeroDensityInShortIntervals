#!/usr/bin/env python3
"""
Independent numeric check of the sharp `(1 - log 2) h^2/(pi t^2)` term of L(h,t).

NOT a certificate.  The coefficient is PROVED in Lean: `MainCorollary.Lbound` carries it,
`MainCorollary.Lbound_le_N_sub_N` justifies it through `ExternalFacts.bellotti_wong_Lbound_le`,
which derives it from Bellotti-Wong Corollary 1.3 (the hypothesis-class field
`LiteratureInputs.bellotti_wong_cor_1_3`) via the power-series inequality
`Common.RealLogBounds.two_mul_sub_bwPhi_le`.  The tex carries the same coefficient.  What follows
re-derives the constant numerically, two ways, and shows it is sharp.

With lambda = h/t, the estimate L needs is
    M(t+h) - M(t-h) >= (h/pi) log(t/2pi) - C * h * lambda^2
and the exact M-difference gives
    M(t+h) - M(t-h) = (h/pi) log(t/2pi) + (t/2pi) * INT(lambda),
    INT(lambda) := int_0^lambda log(1-v^2) dv.
So the requirement is  -(t/2pi) INT(lambda) <= C h lambda^2, i.e.
    -INT(lambda) <= 2 pi C lambda^3.

The sharp C is therefore  C* = sup_lambda [ -INT(lambda) / (2 pi lambda^3) ].

Two independent evaluations of -INT:
  (a) the closed form proved in Lean as `Common.RealLogBounds.integral_log_one_sub_sq`,
      INT(a) = log(1+a) - log(1-a) + a log(1-a^2) - 2a
      (cross-checked below against `mp.quad`)
  (b) the series  -INT(lambda) = sum_{k>=1} lambda^(2k+1) / (k(2k+1))

At lambda -> 1 both give  -INT(1) = 2 - 2 log 2 = 0.6137056...,
since sum_{k>=1} 1/(k(2k+1)) = 2(1 - log 2).
Hence C* = (2 - 2 log 2)/(2 pi) = (1 - log 2)/pi = 0.09767428...,  a factor 2.5595 smaller than
the 1/4 the tex allowed before the sharpening.

Method: mpmath at 30 decimal digits.  Indicative, not ball arithmetic; the identification of C*
is exact.
"""

from mpmath import mp, mpf, log, pi, quad, nstr

mp.dps = 30


def INT_closed(a):
    return log(1 + a) - log(1 - a) + a * log(1 - a ** 2) - 2 * a


def INT_quad(a):
    return quad(lambda v: log(1 - v ** 2), [0, a])


# `C_tex` is the OLD 1/4 allowance, kept here only so the improvement factor can be printed.
# Both the tex and `MainCorollary.Lbound` now carry `C_sharp`, so the print labels below that read
# "tex uses C = 1/4" and "with C = 1/4" are out of date; they are left as the script's own
# printed evidence for the size of the sharpening.
C_sharp = (1 - log(2)) / pi
C_tex = mpf(1) / 4

print("Sharp constant")
print(f"  C* = (1 - log 2)/pi = {nstr(C_sharp, 20)}")
print(f"  tex uses C  = 1/4   = {nstr(C_tex, 20)}")
print(f"  improvement factor  = {nstr(C_tex / C_sharp, 8)}")
print()

print("Is  -INT(lambda) / (2 pi lambda^3)  increasing in lambda (so the sup is at 1)?")
print(f"{'lambda':>10} {'closed form':>18} {'quadrature':>18} {'ratio to 2pi l^3':>20}")
prev = None
mono = True
for k in range(1, 20):
    lam = mpf(k) / 20
    a = INT_closed(lam)
    b = INT_quad(lam)
    assert abs(a - b) < mpf(10) ** (-20), (lam, a, b)
    r = -a / (2 * pi * lam ** 3)
    if prev is not None and r < prev:
        mono = False
    prev = r
    print(f"{nstr(lam, 4):>10} {nstr(-a, 12):>18} {nstr(-b, 12):>18} {nstr(r, 12):>20}")
print()
print("monotone increasing:", mono)
print(f"limit as lambda -> 1: {nstr(C_sharp, 20)}   (= (2-2log2)/(2pi))")
print()

print("Closed form and series agree at lambda -> 1:")
s = sum(mpf(1) / (k * (2 * k + 1)) for k in range(1, 200000))
print(f"  sum_(k>=1) 1/(k(2k+1))  = {nstr(s, 12)}  (partial)")
print(f"  2(1 - log 2)            = {nstr(2 * (1 - log(2)), 12)}")
print(f"  -INT(0.999999)          = {nstr(-INT_closed(mpf('0.999999')), 12)}")
print()

print("Sanity: does the SHARP bound still hold at the operative lambda?")
print("(h < t^(2/3), t > 10^12  =>  lambda < 10^-4)")
for lam in ['1e-4', '1e-6', '0.5', '0.9', '0.999']:
    ll = mpf(lam)
    lhs = -INT_closed(ll)
    rhs = 2 * pi * C_sharp * ll ** 3
    print(f"  lambda = {lam:>7}: -INT = {nstr(lhs, 10):>16} <= {nstr(rhs, 10):>16}"
          f"  {'OK' if lhs <= rhs else 'FAIL'}")
print()
print("How much does the sharpening matter in the operative range?")
lam = mpf('1e-4')
t = mpf(10) ** 12
main = log(t / (2 * pi)) / pi
print(f"  at lambda=1e-4: subtracted term / main term")
print(f"    with C = 1/4      : {nstr(C_tex * lam ** 2 / main, 6)}")
print(f"    with C = (1-ln2)/pi: {nstr(C_sharp * lam ** 2 / main, 6)}")
print("  i.e. both utterly negligible there; the sharpening matters only for")
print("  lambda of order 1, which the h < t^(2/3) hypothesis excludes.")
