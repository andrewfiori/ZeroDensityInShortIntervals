"""Independent numeric check of the collapse behind the proved theorem
`MainTheoremTight.mainLittlewoodTight`.

No hypothesis-class field is certified here.  `mainLittlewoodTight` is proved in Lean, on the
regime `t > 10^12`, `0 < h <= t^{2/3}`; what this script does is evaluate, over a sweep of that
regime, the single arithmetic inequality the Lean proof reduces to, so that a mistranscribed
constant in the six-term bound would show up as a ratio above 1.  The six constants below are the
ones listed in `MainTheoremTight.lean`'s own module docstring.

`LittlewoodShort.littlewoodshort_tight` gives, for `13 < t-h`, `0 < h < t`, `0 < alpha < r`:

    Nrect(t-h, t+h, alpha) < ULittlewood(alpha,r,h,t,k) + Etight/(r-alpha)

with (writing E(r,tau) = arcErr_tight r tau)

    Etight = 2h/(pi (t-h)^2) + 1158 h/(8 pi (t-h)^2 log(t-h))
             + (r/4)(E(r,t+h) + E(r,t-h)),

    E(r,tau) = (2/3)(r/(tau-r)) + (r/(tau-r))/(log tau - r/(tau-r))
               + 2/(tau-r)^2 + 1158/(8 (tau-r)^2 log(tau-r)).

`mainLittlewoodTight` asserts the six-term bound

    Etight/(r-alpha) <= (1/(t(r-alpha))) * B,
    B := 0.334 + 0.502/log t + 1.001/t + 72.48/(t log t)
         + 0.64/t^(1/3) + 46.3/(t^(1/3) log t).

The `1/(r-alpha)` cancels, so the claim is `t * Etight <= B` under `t > 10^12`, `0 < h <= t^(2/3)`
(the Lean regime is non-strict in `h`; the sweep below samples `h` up to `0.999999*t^(2/3)`).
This script checks that, and the term-by-term correspondence behind it.

The un-collapsed input, `littlewoodshort_tight`, is the `t > 10^12`, `h < t^{2/3}` simplification
stated inside Theorem \\ref{thm:littlewoodshort} (Theorem 32).
"""
import mpmath as mp

mp.mp.dps = 40


def arcErr_tight(r, tau):
    d = tau - r
    return ((mp.mpf(2) / 3) * (r / d)
            + (r / d) / (mp.log(tau) - r / d)
            + 2 / d**2
            + mp.mpf(1158) / (8 * d**2 * mp.log(d)))


def Etight(r, h, t):
    d = t - h
    return (2 * h / (mp.pi * d**2)
            + mp.mpf(1158) * h / (8 * mp.pi * d**2 * mp.log(d))
            + (r / 4) * (arcErr_tight(r, t + h) + arcErr_tight(r, t - h)))


def B(t):
    L = mp.log(t)
    return (mp.mpf('0.334') + mp.mpf('0.502') / L + mp.mpf('1.001') / t
            + mp.mpf('72.48') / (t * L)
            + mp.mpf('0.64') / t ** (mp.mpf(1) / 3)
            + mp.mpf('46.3') / (t ** (mp.mpf(1) / 3) * L))


print("Claim: t * Etight(r,h,t) <= B(t)  for t > 10^12, 0 < h < t^(2/3), 0 < r < 1.")
print()
print(f"{'t':>10} {'r':>7} {'h':>14} {'t*Etight':>16} {'B(t)':>16} {'ratio':>9}  ok?")
print("-" * 78)
worst = mp.mpf(0)
worst_at = None
for texp in [12, 13, 15, 20, 30]:
    t = mp.mpf(10) ** texp
    hmax = t ** (mp.mpf(2) / 3)
    for r in ['0.05', '0.5', '0.9', '0.999']:
        r = mp.mpf(r)
        for hf in ['1e-9', '0.5', '0.999999']:
            h = mp.mpf(hf) * hmax
            lhs = t * Etight(r, h, t)
            rhs = B(t)
            ratio = lhs / rhs
            if ratio > worst:
                worst, worst_at = ratio, (texp, r, h / hmax)
            if texp in (12, 30) and hf in ('1e-9', '0.999999'):
                print(f"1e{texp:<8} {mp.nstr(r,4):>7} {mp.nstr(h,6):>14} "
                      f"{mp.nstr(lhs,9):>16} {mp.nstr(rhs,9):>16} "
                      f"{mp.nstr(ratio,5):>9}  {'yes' if ratio <= 1 else 'NO'}")

print()
print(f"worst ratio over the whole sweep: {mp.nstr(worst, 8)} "
      f"(at t=1e{worst_at[0]}, r={mp.nstr(worst_at[1],4)}, h/t^(2/3)={mp.nstr(worst_at[2],4)})")
print("  -> holds" if worst <= 1 else "  -> FAILS")

print()
print("Term-by-term correspondence at the binding corner (r -> 1, h -> t^(2/3)):")
print("  (r/4)*2*(2/3)(r/(tau-r))          ~ r^2/(3t)        vs  0.334/t      (1/3 = 0.3333)")
print("  (r/4)*2*(r/(tau-r))/(log tau...)  ~ r^2/(2 t log t) vs  0.502/(t log t)  (1/2)")
print("  (r/4)*2*2/(tau-r)^2               ~ r/t^2           vs  1.001/t^2")
print("  (r/4)*2*1158/(8(tau-r)^2 log)     ~ 72.375 r/(t^2 log t) vs 72.48/(t^2 log t)")
print("  2h/(pi(t-h)^2)                    ~ 2/(pi t^(4/3))  vs  0.64/t^(4/3)   (2/pi = 0.6366)")
print("  1158h/(8pi(t-h)^2 log)            ~ 46.07/(t^(4/3) log t) vs 46.3/(t^(4/3) log t)")
print()
print("Every printed constant strictly exceeds its limiting value, so the bound has room at")
print("the corner; the sweep above confirms it holds throughout, not just in the limit.")
