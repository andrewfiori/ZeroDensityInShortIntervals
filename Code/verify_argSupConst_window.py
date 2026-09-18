r"""Which condition on `c - sigma_0` makes `argSupConst`'s spurious `sigma = c` value harmless?

No Lean target: this is the tabulation that `Littlewood.ArgIntegrals.argSupConst`'s docstring
cites to justify puncturing that definition's domain at `sigma = c` rather than taking the tex's
closed `[sigma_0, sigma_1]`.  `argSupConst_le_of_le` -- `Lemma \ref{lem:supremumforarg}`
(Lemma 29) in the form `Lemma \ref{lem:integralofarg}` (Lemma 28) consumes it -- is PROVED, and
deliberately free of any hypothesis-class binder, so nothing below is a certificate for it.

At `sigma = c` Lean's total `Real.log` gives `log|sigma-c| = log 0 = 0`, so the ratio
`(sigma-sigma_0)/(log(c-sigma_0) - log|sigma-c|)` evaluates there to

    V(d) = d / log(d),        d := c - sigma_0 > 0,

instead of its true limit 0. The bound being sought is `<= d`. So the question is exactly:
for which `d` is `V(d) <= d`?

Method: mpmath at 30 decimal digits; the answer below is read off an exact one-line argument
(`V(d) > d` iff `0 < log d < 1`), the table only illustrates it.
"""
import mpmath as mp

mp.mp.dps = 30


def V(d):
    d = mp.mpf(d)
    if d == 1:
        return mp.inf   # log 1 = 0; Lean's x/0 = 0, handled separately below
    return d / mp.log(d)


print(f"{'d = c-sigma_0':>14} {'V(d) = d/log d':>18} {'d':>12}   exceeds d?")
print("-" * 62)
for d in ['0.1', '0.5', '0.9', '1.1', '1.5', '2.0', '2.5', '2.71', '2.72', '3.0', '5.0', '10.0']:
    d = mp.mpf(d)
    v = V(d)
    bad = v > d
    print(f"{mp.nstr(d,4):>14} {mp.nstr(v,10):>18} {mp.nstr(d,6):>12}   {'YES  <-- BAD' if bad else 'no'}")

print()
print("V(d) > d  <=>  1/log(d) > 1  <=>  0 < log(d) < 1  <=>  1 < d < e.")
print(f"e = {mp.nstr(mp.e, 12)}")
print()
print("So the failure window is the OPEN INTERVAL (1, e):")
print("  * d <= 1  : log d <= 0, so V(d) <= 0 < d.  SAFE (d = 1 gives Lean's x/0 = 0).")
print("  * d >= e  : log d >= 1, so V(d) <= d.      SAFE")
print("  * 1<d<e   : 0 < log d < 1, so V(d) > d.    FAILS")
print()
print("Therefore `c - sigma_0 < e` does NOT rescue the bound -- it CONTAINS the whole")
print("failure window. The conditions that do work are `c - sigma_0 <= 1` or")
print("`c - sigma_0 >= e`. The intended application has c = 1 and sigma_0 in (0,1),")
print("hence d < 1, which is the first (and by far the more natural) of these.")

# The overshoot is unbounded as d -> 1+, so there is no "small margin" reading of the
# window: the spurious value blows up there.
print()
print("The overshoot is UNBOUNDED as d -> 1+, since log d -> 0:")
for d in ['1.5', '1.1', '1.01', '1.001']:
    d = mp.mpf(d)
    print(f"    d = {mp.nstr(d,5):>7}   V(d) = {mp.nstr(V(d),10):>14}   V(d)/d = {mp.nstr(V(d)/d,8)}")
