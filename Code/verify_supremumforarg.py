r"""Independent numeric check of the claims of `Lemma \ref{lem:supremumforarg}` (Lemma 29), with
the numerator sigma - sigma_0.

Not a certificate: the claims are PROVED in Lean, as
`Littlewood.ArgIntegrals.supremumforarg_left`/`_right`/`_full`, and that file declares no
hypothesis-class binder, so nothing there depends on the numbers below.

The numerator is sigma - sigma_0 throughout.  Claim 3 was PRINTED in the tex with
sigma - sigma_1; that was a typo, and both the tex and the Lean now carry sigma - sigma_0 -- see
`Code/verify_supremumforarg_numerator.py` for the evidence.

Claim 1 : sup_{sigma in [sigma0, c)} (sigma-sigma0)/(log(c-sigma0)-log(c-sigma))  <=  c-sigma0
Claim 3 : same ratio over [sigma0,sigma1]\{c}, given sigma1-c <= eta*(c-sigma0)

What the tabulations below show:
  (a) the bound is approached as sigma -> sigma0+ (the ratio tends to c-sigma0 there), so `<=`
      is correct and a strict `<` would be false;
  (b) the right-hand piece (c,sigma1] does stay under c-sigma0 under the eta hypothesis, with
      equality exactly at the endpoint sigma = sigma1 when that hypothesis is tight.

Method: mpmath at 30 decimal digits on 2000- and 4000-point grids.  Indicative, not ball
arithmetic.
"""
import mpmath as mp

mp.mp.dps = 30

# eta: unique root in (0,1) of 1 + eta + log eta = 0
eta = mp.findroot(lambda e: 1 + e + mp.log(e), mp.mpf('0.278'))
print(f"eta = {mp.nstr(eta, 20)}   check 1+eta+log(eta) = {mp.nstr(1+eta+mp.log(eta), 5)}")
print(f"-log(eta) = {mp.nstr(-mp.log(eta), 20)}   1+eta = {mp.nstr(1+eta, 20)}   equal: "
      f"{mp.almosteq(-mp.log(eta), 1+eta)}")

def ratio(sigma, sigma0, c):
    d = mp.log(c - sigma0) - mp.log(abs(sigma - c))
    if d == 0:
        return mp.mpf(0)          # Lean's 0/0 = 0 convention at sigma = sigma0
    return (sigma - sigma0) / d

print("\n" + "=" * 74)
print("(a) LEFT PIECE  [sigma0, c):  sup should EQUAL c-sigma0, approached as sigma->sigma0+")
print("=" * 74)
sigma0, c = mp.mpf(0), mp.mpf(1)          # c - sigma0 = 1
print(f"  target c-sigma0 = {mp.nstr(c-sigma0, 10)}")
for e in ['1e-2', '1e-4', '1e-6', '1e-10', '1e-14']:
    s = sigma0 + mp.mpf(e)
    print(f"    sigma = sigma0 + {e:<7}  ratio = {mp.nstr(ratio(s, sigma0, c), 18)}")
mx = max(ratio(sigma0 + mp.mpf(k)/2000 * (c-sigma0), sigma0, c) for k in range(0, 2000))
print(f"  max over a 2000-point grid of [sigma0,c) = {mp.nstr(mx, 18)}")
print(f"  => strict '<' is FALSE, '<=' is correct: {mx <= c - sigma0}")

print("\n" + "=" * 74)
print("(b) RIGHT PIECE  (c, sigma1]  with sigma1 - c = eta*(c-sigma0)  (hypothesis tight)")
print("=" * 74)
sigma1 = c + eta * (c - sigma0)
print(f"  sigma1 = {mp.nstr(sigma1, 15)},  c-sigma0 = {mp.nstr(c-sigma0, 10)}")
worst = mp.mpf(0)
for k in range(1, 2001):
    s = c + mp.mpf(k)/2000 * (sigma1 - c)
    worst = max(worst, ratio(s, sigma0, c))
print(f"  max over (c,sigma1] = {mp.nstr(worst, 18)}   <= c-sigma0: {worst <= c - sigma0}")
print(f"  value at the endpoint sigma1 = {mp.nstr(ratio(sigma1, sigma0, c), 18)}")
print("  (endpoint value should equal c-sigma0 exactly when the eta hypothesis is tight)")

print("\n" + "=" * 74)
print("(c) A few non-tight configurations, both pieces, random-ish")
print("=" * 74)
for (s0, cc, frac) in [(mp.mpf('-3'), mp.mpf('0.5'), mp.mpf('0.3')),
                       (mp.mpf('0.2'), mp.mpf('2.0'), mp.mpf('1.0')),
                       (mp.mpf('-1'), mp.mpf('0.25'), mp.mpf('0.7'))]:
    s1 = cc + frac * eta * (cc - s0)
    m = mp.mpf(0)
    for k in range(0, 4001):
        s = s0 + mp.mpf(k)/4000 * (s1 - s0)
        if abs(s - cc) < mp.mpf('1e-12'):
            continue
        m = max(m, ratio(s, s0, cc))
    ok = m <= cc - s0
    print(f"  sigma0={mp.nstr(s0,4):>6} c={mp.nstr(cc,4):>5} sigma1={mp.nstr(s1,6):>8}  "
          f"max={mp.nstr(m,14):>18}  c-sigma0={mp.nstr(cc-s0,10):>12}  holds: {ok}")
