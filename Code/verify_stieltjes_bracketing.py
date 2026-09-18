"""The mean-value bracketing that reduces a gamma_1 bound to a finite numeric check.

Independent numeric check, not a certificate.  The gamma_1 statements it feeds are
`Background/LogDerivZetaLaurent.stieltjes_combo_lower_bound` and `stieltjes_combo_upper_bound`
(via `stieltjesConstant1_lower_bound` / `stieltjesConstant1_upper_bound`), both proved, and
`Jensen/JensenBounds.stieltjes_combo_pos` (proved) and `stieltjes_combo_bound`.

`Definitions.stieltjesConstant1` is `limUnder atTop a` with

    a_m = sum_{k=1}^{m} (log k)/k  -  (log m)^2 / 2.

Writing f(x) = (log x)/x, note (log x)^2/2 is an antiderivative of f, so by the mean value
theorem there is xi in (m-1, m) with

    (log m)^2/2 - (log (m-1))^2/2 = f(xi).

`Real.log_div_self_antitoneOn` says f is antitone on [e, infinity), so for m-1 >= 3 > e,

    f(m) <= f(xi) <= f(m-1).

Hence, with b_m := a_m - f(m),

    a_m - a_{m-1} = f(m) - f(xi) <= 0            (a is antitone)
    b_m - b_{m-1} = f(m-1) - f(xi) >= 0          (b is monotone)
    a_m - b_m     = f(m) -> 0

so a decreases to gamma_1, b increases to gamma_1, and for every m >= 3

    b_m <= gamma_1 <= a_m.

That converts each `stieltjes_combo_*` statement into an inequality about a FINITE sum of logs.
This script finds the smallest m that suffices for each.

Here a_m is `Definitions.stieltjesSeq m`.  The Lean uses two sharper brackets than the plain
b_m below: `Definitions.stieltjesSeqMid m` = a_m - (log m)/(2m) (trapezoid, half the gap) as
the lower one, and `Definitions.stieltjesSeqHi m` (Euler-Maclaurin, error O((log m)/m^3)) as
the upper one.  With those, `stieltjesConstant1_lower_bound` (gamma_1 >= -0.076) closes at
m = 5 and `stieltjesConstant1_upper_bound` (gamma_1 <= -0.0724) at m = 16, needing only the
logarithms of 2, 3, 5, 7, 11, 13.
"""
import mpmath as mp

mp.mp.dps = 40

GAMMA = mp.euler
GAMMA1 = mp.mpf('-0.0728158454836767248605863758749013191377')


def a(m):
    return mp.fsum(mp.log(k) / k for k in range(1, m + 1)) - mp.log(m) ** 2 / 2


def b(m):
    return a(m) - mp.log(m) / m


print("Sanity: the bracketing really does hold, and the gap is f(m) = log m / m.")
print(f"{'m':>5} {'b_m':>16} {'gamma_1':>16} {'a_m':>16} {'gap':>12} {'ok?':>5}")
for m in [3, 5, 10, 20, 40, 100]:
    lo, hi = b(m), a(m)
    ok = lo <= GAMMA1 <= hi
    print(f"{m:>5} {mp.nstr(lo,10):>16} {mp.nstr(GAMMA1,10):>16} {mp.nstr(hi,10):>16} "
          f"{mp.nstr(hi-lo,6):>12} {'yes' if ok else 'NO':>5}")

# ---------------------------------------------------------------- stieltjes_combo_bound
# exp(2/3)*(g^2 + 2 g1)/8 <= (pi-2) g /(2 pi),  i.e.  2 g1 <= g*(c - g)  with
c = 4 * (mp.pi - 2) / (mp.pi * mp.exp(mp.mpf(2) / 3))
print()
print("stieltjes_combo_bound reduces to  2*gamma_1 <= gamma*(c - gamma)  with")
print(f"   c = 4(pi-2)/(pi e^(2/3)) = {mp.nstr(c, 12)}")
# g*(c-g) is concave, so on [1/2, 2/3] its min is at an endpoint.
lo_end = mp.mpf(1) / 2 * (c - mp.mpf(1) / 2)
hi_end = mp.mpf(2) / 3 * (c - mp.mpf(2) / 3)
worst = min(lo_end, hi_end)
print(f"   gamma in (1/2, 2/3) [Mathlib]; g(c-g) is concave so min is at an endpoint:")
print(f"     at 1/2: {mp.nstr(lo_end, 8)}     at 2/3: {mp.nstr(hi_end, 8)}")
print(f"   => suffices:  gamma_1 <= {mp.nstr(worst/2, 8)}")
need_up = worst / 2
for m in [10, 15, 16, 20, 30]:
    print(f"     a_{m:<3} = {mp.nstr(a(m),8):>12}   {'SUFFICES' if a(m) <= need_up else 'no'}")

# ---------------------------------------------------------------- stieltjes_combo_pos
print()
print("stieltjes_combo_pos reduces to  2*gamma_1 > -gamma^2, worst at gamma = 1/2:")
need_lo = -mp.mpf(1) / 8
print(f"   => suffices:  gamma_1 > -1/8 = {mp.nstr(need_lo, 8)}")
for m in [20, 30, 40, 50, 60]:
    print(f"     b_{m:<3} = {mp.nstr(b(m),8):>12}   {'SUFFICES' if b(m) > need_lo else 'no'}")

print()
print("A sharper lower bound on gamma would relax the second requirement a lot:")
for gl in ['0.5', '0.55', '0.57']:
    gl = mp.mpf(gl)
    print(f"   gamma > {mp.nstr(gl,4)}  =>  need gamma_1 > {mp.nstr(-gl**2/2, 8)}"
          f"   (b_20 = {mp.nstr(b(20),8)} {'suffices' if b(20) > -gl**2/2 else 'does not'})")
