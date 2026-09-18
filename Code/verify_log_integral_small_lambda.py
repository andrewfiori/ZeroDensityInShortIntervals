"""A cheap provable route to  int_0^lambda -log(1-v^2) dv <= pi lambda^3 / 2.

NO LEAN TARGET; this route was not taken.  The inequality above is the `C = 1/4` form of the
allowance that L(h,t) needs: the requirement is int_0^lambda -log(1-v^2) dv <= 2 pi C lambda^3,
and 2 pi (1/4) = pi/2.  Lean instead proves the SHARP constant C = (1-log 2)/pi, which
`MainCorollary.Lbound` carries, from the power series of (1+x)log(1+x) - (1-x)log(1-x) in
`Common.RealLogBounds.two_mul_sub_bwPhi_le` (numerics: `Code/verify_Lht_sharp_constant.py`).
What follows is kept as the record of the cheap alternative and of how much slack it has.

The general-lambda statement is true but its worst ratio (0.391, as lambda -> 1) needs the
antiderivative of log(1-v^2). For the application lambda = h/t is TINY, so a crude pointwise
bound suffices and needs only `Real.log_le_sub_one_of_pos`, which Mathlib has.

Pointwise, for 0 <= v <= lambda < 1:

    -log(1 - v^2) = log(1/(1-v^2)) <= 1/(1-v^2) - 1 = v^2/(1-v^2) <= v^2/(1-lambda^2)

using log x <= x - 1 at x = 1/(1-v^2). Integrating,

    int_0^lambda -log(1-v^2) dv  <=  lambda^3 / (3(1-lambda^2)),

so the target holds as soon as

    lambda^3/(3(1-lambda^2)) <= pi lambda^3/2   <=>   2 <= 3 pi (1 - lambda^2)
                                                <=>   lambda^2 <= 1 - 2/(3 pi).

Method: mpmath at 25 decimal digits, tabulation against `mp.quad`.  Indicative, not ball
arithmetic; the derivation above is exact.
"""
import mpmath as mp

mp.mp.dps = 25

thresh = mp.sqrt(1 - 2 / (3 * mp.pi))
print(f"crude route valid for lambda <= sqrt(1 - 2/(3pi)) = {mp.nstr(thresh, 10)}")
print()

print("In the application lambda = h/t with h < t^(2/3) and t > 10^12, so")
for t in ['1e12', '1e13', '1e20']:
    t = mp.mpf(t)
    lam = t ** (mp.mpf(2) / 3) / t
    print(f"   t = {mp.nstr(t,4):>8}   h = t^(2/3)  =>  lambda = t^(-1/3) = {mp.nstr(lam, 6)}")
print(f"   ... all far below the threshold {mp.nstr(thresh,6)}, and below 1/1000.")
print()

print("Pointwise bound and the resulting integral bound:")
print(f"{'lambda':>10} {'exact int':>16} {'crude bound':>16} {'target pi l^3/2':>17} {'ok?':>5}")
print("-" * 70)
for lam in ['1e-4', '1e-3', '0.01', '0.1', '0.5', '0.8', '0.887', '0.89']:
    lam = mp.mpf(lam)
    exact = mp.quad(lambda v: -mp.log(1 - v**2), [0, lam])
    crude = lam**3 / (3 * (1 - lam**2))
    target = mp.pi * lam**3 / 2
    ok = "yes" if crude <= target else "NO"
    print(f"{mp.nstr(lam,5):>10} {mp.nstr(exact,8):>16} {mp.nstr(crude,8):>16} "
          f"{mp.nstr(target,8):>17} {ok:>5}")

print()
print("Margin at the sizes that actually occur (lambda = 1e-4):")
lam = mp.mpf('1e-4')
crude = lam**3 / (3 * (1 - lam**2))
target = mp.pi * lam**3 / 2
print(f"   crude bound / target = {mp.nstr(crude/target, 8)}   (i.e. ~{mp.nstr(target/crude,6)}x of room)")
print()
print("So on lambda <= 1/1000 the inequality is not delicate at all: the crude bound")
print("already gives a factor of about 4.7 of slack, and needs only log x <= x - 1.")
