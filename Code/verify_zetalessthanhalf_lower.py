"""Verify the asymptotic expansion behind `zetalessthanhalf_lower` / `_lower_tight`
(`Lemma \\ref{lem:zetalessthanhalf}`, Lemma 36, second case).

Both Lean statements are proved, and this is mpmath at 40 digits on a sampled grid rather
than ball arithmetic, so what follows is an independent numeric check and not a certificate
of any hypothesis-class field.

The Mathlib-native route (already proved as `log_norm_zeta_functional_eq`) gives, with
z := (1-sigma) - i t and u := 1-sigma,

    log|zeta(sigma+it)| - log|zeta(1-sigma+it)|
      = log 2 - u log(2pi) + log|Gamma(z)| + log|cos(pi z / 2)|.

Two closed forms feed into that:

  (A)  |cos(a - b i)|^2 = cosh(b)^2 - sin(a)^2   exactly,  a = pi u / 2, b = pi t / 2.
  (B)  Brent:  log Gamma(z) = (z-1/2) log z - z + (1/2) log(2pi) + B2/(2z) + R(z),  B2 = 1/6.

Expanding (A) and (B) in 1/t, the main terms cancel against the target
(1/2-sigma) log|t/2| + (sigma-1/2) log|pi|, leaving a 1/t^2 coefficient which this
script measures against two candidates:

    D_pred(sigma) = (-2 sigma^3 + 3 sigma^2 - sigma)/12      <- derived here
    Dcoeff2(sigma) = -(6 sigma^3 + 6 sigma^2 + 25 sigma + 11)/6   <- the SUPERSEDED polynomial

D_pred is the correct coefficient: it is exactly sigma(2 sigma - 1)(1 - sigma)/12, which is
what Lean's `Dcoeff` is, and `Dcoeff2` is now defined to be `Dcoeff`.  The second candidate
above, kept here under its old name, is the polynomial the Lean statement used to carry; it
agrees with the true one only at sigma = -1/2.  STEP 1 is the measurement that exposed it:
E(sigma,t)*t^2 settles on D_pred and goes nowhere near Dcoeff2.

STEP 3 checks the 4/t^2 of `zetalessthanhalf_lower` over sigma in {0, -0.2, -0.5, -0.8, -1}
and t in {10.5, 11, 20, 100, 1000}; the worst ratio |E|/(4/t^2) on that grid is about 0.125,
the true supremum of |E|*t^2 being 1/2, approached as sigma -> -1, t -> oo.
"""
import mpmath as mp

mp.mp.dps = 40


def E(sigma, t):
    """The quantity `zetalessthanhalf_lower` bounds in absolute value."""
    s = mp.mpc(sigma, t)
    s2 = mp.mpc(1 - sigma, t)
    return (mp.log(abs(mp.zeta(s)))
            - (mp.log(abs(mp.zeta(s2)))
               + (mp.mpf(1) / 2 - sigma) * mp.log(abs(t / 2))
               + (sigma - mp.mpf(1) / 2) * mp.log(abs(mp.pi))))


def D_pred(sigma):
    return (-2 * sigma**3 + 3 * sigma**2 - sigma) / 12


def Dcoeff2(sigma):
    return -(6 * sigma**3 + 6 * sigma**2 + 25 * sigma + 11) / 6


print("STEP 1 -- is the 1/t^2 coefficient D_pred, or the superseded polynomial?")
print("Measuring E(sigma,t) * t^2 as t grows.  D_pred is what Lean's `Dcoeff` (and hence")
print("today's `Dcoeff2`) computes; the `superseded` column is the polynomial the Lean")
print("statement used to carry, shown here only to see the measurement reject it.")
print()
hdr = f"{'sigma':>7} {'t':>8} {'E*t^2':>16} {'D_pred':>14} {'superseded':>14}"
print(hdr)
print("-" * len(hdr))
for sigma in ['0', '-0.25', '-0.5', '-1']:
    sg = mp.mpf(sigma)
    for t in ['100', '1000', '10000']:
        tt = mp.mpf(t)
        val = E(sg, tt) * tt**2
        print(f"{mp.nstr(sg,4):>7} {mp.nstr(tt,5):>8} {mp.nstr(val,10):>16} "
              f"{mp.nstr(D_pred(sg),8):>14} {mp.nstr(Dcoeff2(sg),8):>14}")
    print()

print("STEP 2 -- exact cos identity |cos(a-bi)|^2 = cosh(b)^2 - sin(a)^2")
for sigma in ['0', '-0.5', '-1']:
    for t in ['11', '50']:
        sg, tt = mp.mpf(sigma), mp.mpf(t)
        a = mp.pi * (1 - sg) / 2
        b = mp.pi * tt / 2
        lhs = abs(mp.cos(mp.mpc(a, -b)))**2
        rhs = mp.cosh(b)**2 - mp.sin(a)**2
        print(f"   sigma={mp.nstr(sg,4):>5} t={mp.nstr(tt,4):>4}  "
              f"rel err = {mp.nstr(abs(lhs-rhs)/abs(rhs), 6)}")

print()
print("STEP 3 -- does the claimed bound 4/t^2 hold on the stated range?")
print(f"{'sigma':>7} {'t':>8} {'|E|':>16} {'4/t^2':>16} {'holds?':>8}")
print("-" * 58)
worst = mp.mpf(0)
for sigma in ['0', '-0.2', '-0.5', '-0.8', '-1']:
    for t in ['10.5', '11', '20', '100', '1000']:
        sg, tt = mp.mpf(sigma), mp.mpf(t)
        v, bound = abs(E(sg, tt)), 4 / tt**2
        worst = max(worst, v / bound)
        print(f"{mp.nstr(sg,4):>7} {mp.nstr(tt,5):>8} {mp.nstr(v,10):>16} "
              f"{mp.nstr(bound,10):>16} {'yes' if v <= bound else 'NO':>8}")
print()
print(f"worst ratio |E| / (4/t^2) = {mp.nstr(worst, 8)}")
