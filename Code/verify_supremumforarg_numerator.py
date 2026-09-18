r"""The numerator of claim 3 of `Lemma \ref{lem:supremumforarg}` (Lemma 29): a typo, and its
correction.

The lemma bounds C_{c,s0,s1} := sup_{s in [s0,s1]} (s-s0)/(log(c-s0)-log|s-c|), the constant that
`Lemma \ref{lem:integralofarg}` (Lemma 28) carries as a factor (Lean:
`Littlewood.ArgIntegrals.argSupConst`):
  claim 1: sup_{s in [s0,c]}   (s-s0)/(...)  <= c-s0
  claim 2: sup_{s in [c,s1]}   (s-s0)/(...)  <= (s1-s0)/(log(c-s0)-log|s1-c|)
  claim 3: if s1-c <= eta(c-s0),  sup_{s in [s0,s1]} (s-s0)/(...)  <= c-s0

LIVE FINDING.  Claim 3 was PRINTED with the numerator (s-s1).  That is a typo for (s-s0), and
this script is the evidence:

  * with (s-s1) the numerator is <= 0 throughout [s0,s1], so the supremum is <= 0 and claim 3,
    while trivially true, bounds NOTHING about C_{c,s0,s1} -- which is the whole point of the
    lemma;
  * with (s-s0) the supremum is exactly c-s0 (approached as s -> s0+), so claim 3 is tight and
    non-trivial;
  * the tex's own proof of claim 3 computes
    (s1-s0)/(log(c-s0)-log(s1-c)) <= (1+eta)(c-s0)/(-log eta) = c-s0, which is the (s-s0)
    numerator evaluated at s = s1.  So the PROOF is for (s-s0) as well.

Both documents now carry (s-s0): the tex is corrected, and the Lean statements
`Littlewood.ArgIntegrals.supremumforarg_left` and `supremumforarg_full` are PROVED with that
numerator (as is `argSupConst`'s definition).  So this is a record of a resolved discrepancy, not
a certificate for anything.

Method: mpmath at 30 decimal digits, supremum over a 200000-point grid.  Indicative, not ball
arithmetic.
"""
from mpmath import mp, mpf, log, findroot
mp.dps = 30

# eta: unique root of 1 + eta + log(eta) = 0
eta = findroot(lambda e: 1 + e + log(e), mpf('0.278'))
print(f"eta = {eta}\n")

def ratio(s, s0, s1, c, num):
    den = log(c - s0) - log(abs(s - c))
    n = (s - s0) if num == "s-s0" else (s - s1)
    if den == 0:
        return mpf(0)
    return n / den

def sup_over(s0, s1, c, num, lo, hi, skip_c=True, M=200000):
    best = mpf('-inf')
    arg = None
    for i in range(1, M):
        s = lo + (hi - lo) * mpf(i) / M
        if skip_c and abs(s - c) < mpf(10)**-12:
            continue
        v = ratio(s, s0, s1, c, num)
        if v > best:
            best, arg = v, s
    return best, arg

print("=" * 78)
print("Case: s0=0, c=1 (so c-s0=1), s1 = c + eta*(c-s0) = boundary of the eta-hypothesis")
s0, c = mpf(0), mpf(1)
s1 = c + eta * (c - s0)
print(f"s0={s0}, c={c}, s1={s1}, c-s0={c-s0}\n")

for num in ("s-s0", "s-s1"):
    b1, a1 = sup_over(s0, s1, c, num, s0, c)
    b3, a3 = sup_over(s0, s1, c, num, s0, s1)
    print(f"numerator ({num}):")
    print(f"   claim-1 domain [s0,c) : sup = {mp.nstr(b1,12):>16}   (tex claim 1 bound c-s0 = {c-s0})")
    print(f"   claim-3 domain [s0,s1]: sup = {mp.nstr(b3,12):>16}   (tex claim 3 bound c-s0 = {c-s0})")
    print()

print("=" * 78)
print("Interpretation:")
print("  With (s-s0): sup -> c-s0 exactly (approached as s->s0+), so both claims are TIGHT")
print("               and genuinely bound C_{c,s0,s1}.  Non-trivial.")
print("  With (s-s1): numerator <= 0 throughout [s0,s1], so sup <= 0 and the claim is")
print("               TRIVIALLY true but bounds NOTHING about C_{c,s0,s1}.")
print()
print("tex's own proof of claim 3 computes (s1-s0)/(log(c-s0)-log(s1-c)) <= (1+eta)(c-s0)/(-log eta)")
lhs = (s1 - s0) / (log(c - s0) - log(s1 - c))
rhs = (1 + eta) * (c - s0) / (-log(eta))
print(f"   (s1-s0)/(log(c-s0)-log(s1-c)) = {mp.nstr(lhs,12)}")
print(f"   (1+eta)(c-s0)/(-log eta)      = {mp.nstr(rhs,12)}   [= c-s0 = {c-s0} by eta's defn]")
print("   -> that is the numerator (s-s0) evaluated at s=s1.  So the PROOF is for (s-s0).")
