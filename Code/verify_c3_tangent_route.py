#!/usr/bin/env python3
"""Exact-rational re-check of every numeric step in the Lean proof of
`ConstantSigns.c3_nonneg` (`ZerosInShortIntervals/ConstantSigns.lean`).

That theorem is proved, so this is an independent re-check and not a certificate of any
hypothesis-class field.

The Lean proof puts `c3 r` into closed form on each regime of K = Kidx r and then uses

  * c3G0 convex on [1/2, 5/7] and above its tangent at r_1 = 1/sqrt 3,
  * c3G1 decreasing on [2/7, 1/2] with c3G1(1/2) = c3G0(1/2),
  * c3F concave on [5/7, 1] with c3F(5/7) = c3G0(5/7) and c3F(1) >= 0.03.

Section [A] checks, in exact rational arithmetic (fractions.Fraction), that the interval
bounds used in Lean imply the stated conclusions with the stated slack:

  c3L_bounds       0.435669 <= L  = log 1.546 <= 0.435672
  c3L0_bounds     -0.49266  <= L0 = log 0.611 <= -0.492657
  logPi_bounds     1.14472  <= lp = log pi    <= 1.14474
  c3m0_bounds      4.33218  <= m0 = (14/3)(L - L0) <= 4.33222
  pi                3.141592 <  pi <  3.141593                      (Real.pi_gt_d6 / pi_lt_d6)
  arcA_27_r1_le    arcsin(2 sqrt3 / 7) <= pi/6 - 0.0059
  sqrt bounds      sqrt(1/12), sqrt(37/147), sqrt(37/49), sqrt(24/49), sqrt(3/4), sqrt(45/49)
  c3G0_r1_ge       c3G0(r_1) >= 0.0163
  c3G0'_r1_bounds  -0.006 <= c3G0'(r_1) <= 0.006
  c3G0_lower       c3G0 >= 0.012 on [1/2, 5/7]
  c3F_one_ge       c3F(1) >= 0.03  (with arcsin(5/7) <= 0.8, arcsin(2/7) <= 0.2945)

Section [B] checks with mpmath (30 digits, sampled points -- so [B] on its own is evidence
rather than a certificate) that the interval bounds themselves are true, that the closed forms
agree with the series definition of `JensenScaleConstants.c3` at five sample radii, and reports
the true values (c3G0(r_1) = 0.0164999, min c3 = 0.016499 at r = 0.57762, c3F(1) = 0.0601864).

Run:  python3 Code/verify_c3_tangent_route.py
"""
from fractions import Fraction as Fr

ok = True


def check(name, cond):
    global ok
    print(f"  [{'OK' if cond else 'FAIL'}] {name}")
    ok = ok and cond


def F(*args):
    return Fr(*args)


print("[A] exact rational implications of the Lean interval bounds")
L_lo, L_hi = F('0.435669'), F('0.435672')
L0_lo, L0_hi = F('-0.49266'), F('-0.492657')
lp_lo, lp_hi = F('1.14472'), F('1.14474')
pi_lo, pi_hi = F('3.141592'), F('3.141593')
m0_lo, m0_hi = F(14, 3) * (L_lo - L0_hi), F(14, 3) * (L_hi - L0_lo)
check("c3m0_bounds: 4.33218 <= m0 <= 4.33222", F('4.33218') <= m0_lo and m0_hi <= F('4.33222'))
m0_lo, m0_hi = F('4.33218'), F('4.33222')

# square-root bounds by squaring
check("sqrt(1/12) in [0.288675, 0.288676]", F('0.288675') ** 2 <= F(1, 12) <= F('0.288676') ** 2)
check("sqrt(37/147) in [0.50169, 0.5017]", F('0.50169') ** 2 <= F(37, 147) <= F('0.5017') ** 2)
check("sqrt(37/49) in [0.868966, 0.868967]", F('0.868966') ** 2 <= F(37, 49) <= F('0.868967') ** 2)
check("sqrt(24/49) <= 0.69986", F(24, 49) <= F('0.69986') ** 2)
check("sqrt(3/4) >= 0.866025", F('0.866025') ** 2 <= F(3, 4))
check("sqrt(45/49) <= 0.95832", F(45, 49) <= F('0.95832') ** 2)
check("sqrt 3 in [1.7320508, 1.7320509]", F('1.7320508') ** 2 <= 3 <= F('1.7320509') ** 2)
check("r_1 = sqrt(1/3) in [0.57735, 0.57736]", F('0.57735') ** 2 <= F(1, 3) <= F('0.57736') ** 2)

# arcA_27_r1_le: 2 sqrt3/7 <= (1 - d^2/2)/2 - (sqrt3/2) d with d = 0.0059, sqrt3 <= 1.7320509
d = F('0.0059')
s3_hi = F('1.7320509')
check("arcsin(2 sqrt3/7) <= pi/6 - 0.0059 (via sin(pi/6 - d) lower polynomial)",
      2 * s3_hi / 7 <= (1 - d * d / 2) / 2 - s3_hi / 2 * d)

# arcsin(5/7) <= 0.8 and arcsin(2/7) <= 0.2945 via sin x > x - x^3/6
check("sin 0.8 > 5/7 via x - x^3/6", F('0.8') - F('0.8') ** 3 / 6 >= F(5, 7))
check("sin 0.2945 > 2/7 via x - x^3/6", F('0.2945') - F('0.2945') ** 3 / 6 >= F(2, 7))

# c3G0(r_1) = pi (L0/9 + 7L/18 + lp/12) + (4/3)(L0 - L) th1 + (2 m0 - lp) sqrt(1/12) - m0 sqrt(37/147)
combo_lo = L0_lo / 9 + 7 * L_lo / 18 + lp_lo / 12
check("log combination >= 0.21008", combo_lo >= F('0.21008'))
t1 = pi_lo * F('0.21008')
coef_lo = F(4, 3) * (L0_lo - L_hi)          # <= (4/3)(L0 - L) < 0
check("(4/3)(L0 - L) >= -1.237776", coef_lo >= F('-1.237776'))
th1_hi = pi_hi / 6 - d
t2 = F('-1.237776') * th1_hi
B_lo = 2 * m0_lo - lp_hi
check("2 m0 - lp >= 7.51962", B_lo >= F('7.51962'))
t3 = F('7.51962') * F('0.288675')
t4 = -m0_hi * F('0.5017')
G0r1_lo = t1 + t2 + t3 + t4
print(f"      c3G0(r_1) chain lower bound = {float(G0r1_lo):.7f}")
check("c3G0_r1_ge: >= 0.0163", G0r1_lo >= F('0.0163'))

# c3G0'(r_1) = (2 m0 - lp)/2 - m0 sqrt(37/49)
dG_lo = (2 * m0_lo - lp_hi) / 2 - m0_hi * F('0.868967')
dG_hi = (2 * m0_hi - lp_lo) / 2 - m0_lo * F('0.868966')
print(f"      c3G0'(r_1) in [{float(dG_lo):.6f}, {float(dG_hi):.6f}]")
check("c3G0'_r1_bounds: |c3G0'(r_1)| <= 0.006", dG_lo >= F('-0.006') and dG_hi <= F('0.006'))

# c3G0_lower: c3G0 x >= c3G0(r_1) + c3G0'(r_1)(x - r_1), x in [1/2, 5/7], r_1 in [0.57735, 0.57736]
worst = min(F('0.0163') - F('0.006') * (F(5, 7) - F('0.57735')),
            F('0.0163') - F('0.006') * (F('0.57736') - F(1, 2)))
print(f"      tangent-line worst case on [1/2, 5/7] = {float(worst):.6f}")
check("c3G0_lower: >= 0.012", worst >= F('0.012'))

# c3F(1) = (L + lp/2) pi/2 + (10/3)(L0 - L) th_{-1} + (m0 - lp/2) pi/6 + (4/3)(L0 - L) th_1
#          - m0 sqrt(24/49) + (2 m0 - lp) sqrt(3/4) - m0 sqrt(45/49)
check("L + lp/2 >= 1.008029", L_lo + lp_lo / 2 >= F('1.008029'))
check("m0 - lp/2 >= 3.75981", m0_lo - lp_hi / 2 >= F('3.75981'))
u1 = F('1.008029') * pi_lo / 2
u2 = F(10, 3) * (L0_lo - L_hi) * F('0.8')
u3 = F('3.75981') * pi_lo / 6
u4 = F(4, 3) * (L0_lo - L_hi) * F('0.2945')
u5 = -m0_hi * F('0.69986')
u6 = F('7.51962') * F('0.866025')
u7 = -m0_hi * F('0.95832')
F1_lo = u1 + u2 + u3 + u4 + u5 + u6 + u7
print(f"      c3F(1) chain lower bound = {float(F1_lo):.6f}")
check("c3F_one_ge: >= 0.03", F1_lo >= F('0.03'))

# second-derivative coefficient inequalities
check("c3G0'' >= 0 needs m0 (2/7)^2 <= (2 m0 - lp)(1/2)^2 (i.e. 82 m0 >= 49 lp)",
      m0_hi * F(4, 49) <= (2 * m0_lo - lp_hi) / 4)
check("c3F'' <= 0 needs (2 m0 - lp)/4 <= m0 (5/7)^2 (i.e. 49(2 m0 - lp) <= 100 m0)",
      (2 * m0_hi - lp_lo) / 4 <= m0_lo * F(25, 49))

print()
print("[B] mpmath: truth of the interval bounds and agreement of the closed forms with c3")
try:
    from mpmath import mp, mpf, log, pi, asin, sqrt, cos
    mp.dps = 30
    L = log(mpf('1.546')); L0 = log(mpf('0.611')); lp = log(pi)
    check("log 1.546 in [0.435669, 0.435672]", mpf(str(L_lo)) <= L <= mpf(str(L_hi)))
    check("log 0.611 in [-0.49266, -0.492657]", mpf(str(L0_lo)) <= L0 <= mpf(str(L0_hi)))
    check("log pi in [1.14472, 1.14474]", mpf(str(lp_lo)) <= lp <= mpf(str(lp_hi)))
    check("arcsin(2 sqrt3/7) <= pi/6 - 0.0059", asin(2 * sqrt(3) / 7) <= pi / 6 - mpf('0.0059'))
    check("arcsin(5/7) <= 0.8", asin(mpf(5) / 7) <= mpf('0.8'))
    check("arcsin(2/7) <= 0.2945", asin(mpf(2) / 7) <= mpf('0.2945'))
    m0 = mpf(14) / 3 * (L - L0); b0 = L0 - m0 / 2; mm1 = lp - m0; bm1 = L0 - mm1 / 2

    def blk(m, b, a, r):
        return (m + b) * asin(a / r) + m * sqrt(r * r - a * a)

    def G1(r):
        return (m0 + b0) * pi / 2 - blk(m0, b0, mpf(2) / 7, r) + blk(0, L, mpf(2) / 7, r)

    def G0(r):
        return ((mm1 + bm1) * pi / 2 - blk(mm1, bm1, mpf(1) / 2, r) + blk(m0, b0, mpf(1) / 2, r)
                - blk(m0, b0, mpf(2) / 7, r) + blk(0, L, mpf(2) / 7, r))

    def Fc(r):
        return ((lp + (L - lp / 2)) * pi / 2 - blk(lp, L - lp / 2, mpf(5) / 7, r)
                + blk(mm1, bm1, mpf(5) / 7, r) - blk(mm1, bm1, mpf(1) / 2, r)
                + blk(m0, b0, mpf(1) / 2, r) - blk(m0, b0, mpf(2) / 7, r) + blk(0, L, mpf(2) / 7, r))

    # the series definition (JensenScaleConstants.c3), summed to k = 60
    def sigma(k):
        if k >= 0:
            return 1 - mpf(k + 3) / (2 ** (k + 3) - 2)
        return mpf(-k + 3) / (2 ** (-k + 3) - 2)

    def vpp(k):
        if k > 0:
            return L
        if k == 0:
            return L0
        return L + (sigma(k) - mpf(1) / 2) * lp

    def mpp(k):
        return (vpp(k) - vpp(k + 1)) / (sigma(k) - sigma(k + 1))

    def bpp(k):
        return vpp(k) - mpp(k) * sigma(k)

    def th(k, r):
        return asin((1 - sigma(k)) / r)

    def c3(r):
        K = -60
        while 1 - sigma(K) > r:
            K += 1
        tot = (mpp(K - 1) + bpp(K - 1)) * (pi / 2 - th(K, r)) - mpp(K - 1) * r * cos(th(K, r))
        for k in range(K, 60):
            tot += ((mpp(k) + bpp(k)) * (th(k, r) - th(k + 1, r))
                    + mpp(k) * r * (cos(th(k, r)) - cos(th(k + 1, r))))
        # exact tail: for k >= 60 the summand is L (theta_k - theta_{k+1}), telescoping to L theta_60
        tot += L * th(60, r)
        return tot

    for r, f, name in [(mpf('0.2'), lambda r: L * pi / 2, "L pi/2"), (mpf('0.4'), G1, "c3G1"),
                       (mpf('0.6'), G0, "c3G0"), (mpf('0.8'), Fc, "c3F"), (mpf('0.95'), Fc, "c3F")]:
        check(f"c3({r}) = {name}({r}) to 1e-25", abs(c3(r) - f(r)) < mpf('1e-25'))
    r1 = 1 / sqrt(3)
    print(f"      c3G0(r_1) = {G0(r1)}   c3F(1) = {Fc(mpf(1))}   c3G0(1/2) = {G0(mpf(1)/2)}")
    print(f"      c3G0'(r_1) = {(2*m0 - lp)/2 - m0*sqrt(37)/7}")
    from mpmath import findroot, diff
    rs = findroot(lambda r: diff(G0, r), mpf('0.58'))
    print(f"      min c3 = c3G0({rs}) = {G0(rs)}")
except ImportError:
    print("  (mpmath not available; section [B] skipped)")

print()
print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
