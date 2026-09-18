#!/usr/bin/env python3
r"""
An explicit counterexample to the printed right-hand side of `Lemma \ref{lem:integralofarg}`
(Lemma 28), and a check of the corrected form.

(The filename records an earlier numbering, in which this was Lemma 27; the paper has since
gained a Corollary 1 and a Table 1 at the front, moving every theorem-like number up by one.)

No Lean target of its own: the corrected statement is PROVED as
`Littlewood.ArgIntegrals.integralofarg`, in a file that declares no hypothesis-class binder.
This script is the live record of WHY the statement had to be corrected.

`Lemma \ref{lem:integralofarg}` (Lemma 28) of `ZerosInShortIntervals.tex` was printed as

    | int_{s1}^{s0} Delta arg f(x+iT)|_{s1}^{u} du |
        <  C_{c,s0,s1} * int_0^{c-s0} pi (n_{F_N}(u) + 1/2) / (N u) du .        (tex, as printed)

Two things were wrong with that right-hand side, and this script checks both by
an explicit example.

 (1) With the `+1/2` INSIDE the integrand, int_0^{c-s0} (1/2)/(N u) du diverges,
     so the printed bound is +infinity (vacuous).  The proof's own display has the
     constant OUTSIDE: (pi/N)(1/2 + int_0^{c-s0} n(u)/u du).

 (2) Even outside, `1/2` is dimensionally wrong: the left side and
     sum (Re rho - s0) scale like a LENGTH, a bare 1/2 does not.  The step-function
     bound the proof invokes is |Delta arg f(u)| <= (pi/N)(k(u) + 1), where k(u) is
     the number of zeros of Re f(x+iT)^N between u and s1; its integral over
     [s0, s1] is (pi/N)( sum_rho (Re rho - s0) + (s1 - s0) ).  So the additive
     term must be (s1 - s0), not 1/2 -- and it cannot be omitted altogether.

Example: f(s) = exp(s^2), which satisfies f(conj s) = conj f(s).  Then
   arg f(u+iT) = Im (u+iT)^2 = 2uT  (a continuous argument),
   Re f(u+iT)^N = exp(N(u^2-T^2)) cos(2NuT),
   F_N(w)       = exp(N((w+c)^2 - T^2)) cos(2NT(w+c)),
whose zeros are all REAL: w + c = (2m+1) pi / (4NT).

With T = 0.01, N = 1, s0 = 100, s1 = 200, c = 160 (so c > (s0+s1)/2 = 150):
   zeros of F_1 at w = (2m+1)*25*pi - 160  ->  -81.46, 75.62, 232.70, ...
   none in the disc |w| <= c - s0 = 60, hence n_{F_1}(u) = 0 on [0, 60].
So every candidate right-hand side without an additive length term is 0, the
tex's `1/2` version is pi/2 = 1.5708, while the left side is
   | int_{200}^{100} 2T(u - 200) du | = T (s1-s0)^2 = 100.
The corrected bound (pi/N)((s1-s0) + C*0) = 100 pi = 314.16 holds.

This is the example behind the corrected Lean statement of `integralofarg`
(`ZerosInShortIntervals/Littlewood/ArgIntegrals.lean`) and behind the matching correction in the tex.

Method: mpmath at 30 decimal digits; the example is exact and closed-form, the grid sup for
C_{c,s0,s1} (100000 points) is only used to show that the constant stays under c - s0.
"""
from mpmath import mp, mpf, pi, quad, exp, cos, mpc, findroot, log

mp.dps = 30

T = mpf('0.01')
N = 1
s0, s1, c = mpf(100), mpf(200), mpf(160)
R = c - s0

assert c > (s0 + s1) / 2

# left-hand side: | int_{s1}^{s0} (arg f(u+iT) - arg f(s1+iT)) du |, arg f(u+iT) = 2uT
def darg(u):
    return 2 * u * T - 2 * s1 * T

lhs = abs(quad(darg, [s1, s0]))
print("LHS = |int_{s1}^{s0} Delta arg| =", lhs, "   (exact: T (s1-s0)^2 =", T * (s1 - s0) ** 2, ")")

# zeros of F_1(w) = exp((w+c)^2 - T^2) cos(2T(w+c)) : w = (2m+1) pi/(4T) - c, all real
zeros = [(2 * m + 1) * pi / (4 * T) - c for m in range(-3, 6)]
print("real zeros of F_1 near the disc (w-plane):", [mp.nstr(z, 8) for z in zeros])
inside = [z for z in zeros if abs(z) <= R]
print("zeros with |w| <= c - s0 =", R, ":", inside)
assert not inside, "unexpected zero inside the disc"

# sanity: F_1 has no non-real zeros -- exp never vanishes and cos(2T(w+c)) = 0 forces
# 2T(w+c) = (2m+1) pi/2, i.e. w real.  Spot-check |F_1| on the boundary circle.
def F1(w):
    return exp((w + c) ** 2 - T ** 2) * cos(2 * T * (w + c))
mn = min(abs(F1(R * exp(mpc(0, 1) * th))) for th in [mpf(k) / 200 * 2 * pi for k in range(200)])
print("min |F_1| on |w| = c - s0 (200 sample points):", mp.nstr(mn, 6), "(> 0)")

# C_{c,s0,s1} = sup_{s in [s0,s1]\{c}} (s - s0)/(log(c-s0) - log|s-c|)
def ratio(s):
    return (s - s0) / (log(c - s0) - log(abs(s - c)))
grid = [s0 + (s1 - s0) * mpf(k) / 100000 for k in range(1, 100000) if abs(s0 + (s1 - s0) * mpf(k) / 100000 - c) > mpf('1e-9')]
C = max(ratio(s) for s in grid)
print("C_{c,s0,s1} (grid sup) =", mp.nstr(C, 8), "   <= c - s0 =", R)

# candidate right-hand sides
n_integral = mpf(0)  # n_{F_1} == 0 on [0, R]
rhs_no_constant = C * pi / N * n_integral
rhs_tex_half_outside = pi / N * (mpf(1) / 2 + C * n_integral)
rhs_corrected = pi / N * ((s1 - s0) + C * n_integral)
print("RHS with no additive term          =", rhs_no_constant, "  -> LHS <= RHS ?", lhs <= rhs_no_constant)
print("RHS with tex's 1/2 (outside)       =", mp.nstr(rhs_tex_half_outside, 8), "  -> LHS <= RHS ?", lhs <= rhs_tex_half_outside)
print("RHS with (s1 - s0) [corrected]     =", mp.nstr(rhs_corrected, 8), "  -> LHS <= RHS ?", lhs <= rhs_corrected)
print("tex's printed RHS (1/2 inside the 1/u integral): int_0^R (1/2)/u du diverges -> +oo (vacuous)")

# the pointwise step-function bound behind the corrected constant:
# |Delta arg f(u)| <= (pi/N) (k(u) + 1) with k(u) = 0 here; check sup |Delta arg| < pi.
# The author's suggested pointwise form (pi/N)(k(u) + 1/2) fails at k = 0: with no sign
# change of Re f^N the value f^N merely stays in one open half-plane, and its argument can
# move by anything below pi.  Here it moves by 2 > pi/2.
sup_darg = max(abs(darg(s0 + (s1 - s0) * mpf(k) / 1000)) for k in range(1001))
print("sup_u |Delta arg f(u)| =", mp.nstr(sup_darg, 6), "  <  (pi/N)(0+1) =", mp.nstr(pi / N, 6), "->", sup_darg < pi / N)
print("                        ", mp.nstr(sup_darg, 6), " <= (pi/N)(0+1/2) =", mp.nstr(pi / (2 * N), 6), "->", sup_darg <= pi / (2 * N), "  (pointwise '+1/2' fails)")
