"""How sharp must gamma and gamma_1 be to prove 0.15 <= gamma^2 + 2 gamma_1 <= 0.20?

A feasibility study; no current Lean target, because the question is settled.  Both halves of
`Background/LogDerivZetaLaurent.stieltjes_combo_numeric_bounds` are proved --
`stieltjes_combo_lower_bound` and `stieltjes_combo_upper_bound` -- and the upper half is proved
by a route this script does not cost: the Euler-Maclaurin bracket `Definitions.stieltjesSeqHi`
(error O((log m)/m^3)), which closes at m = 16 on the logarithms of 2, 3, 5, 7, 11, 13 alone.

What is quantified below is the cost using only the two CRUDER enclosures,

  gamma   in (eulerMascheroniSeq n, eulerMascheroniSeq' n),  width = log((n+1)/n) ~ 1/n
  gamma_1 in (stieltjesSeqMid m, stieltjesSeq m),            width = (log m)/(2m)

so the (n, m) it reports are the price of the route that was rejected -- retained because that
price is exactly what made the sharper bracket worth building.  The obstacle was never a missing
Stieltjes constant in Mathlib (`Definitions` supplies a proved two-sided bracket); it was
precision, and the crude bracket's 1/m-type error is what costs so much of it.

NOTE: several of the printed labels below still describe the pre-2026-09-08 state (e.g. the
"best proved now" line quoting gamma_1 <= 1/100, and the "BOTH halves fail" verdict).  The
proved bounds are now gamma_1 <= -0.0724 and gamma in [0.5615, 0.5851].
"""
import mpmath as mp

mp.mp.dps = 40

GAMMA = mp.euler
GAMMA1 = mp.mpf('-0.0728158454836767248605863758749013191377')
TRUE = GAMMA ** 2 + 2 * GAMMA1


def em_lo(n):          # eulerMascheroniSeq n = harmonic n - log(n+1)
    return mp.fsum(mp.mpf(1) / k for k in range(1, n + 1)) - mp.log(n + 1)


def em_hi(n):          # eulerMascheroniSeq' n = harmonic n - log n
    return mp.fsum(mp.mpf(1) / k for k in range(1, n + 1)) - mp.log(n)


def g1_hi(m):          # stieltjesSeq m
    return mp.fsum(mp.log(k) / k for k in range(1, m + 1)) - mp.log(m) ** 2 / 2


def g1_lo(m):          # stieltjesSeqMid m
    return g1_hi(m) - mp.log(m) / m / 2


print(f"true gamma^2 + 2 gamma_1 = {mp.nstr(TRUE, 12)}")
print(f"  slack below 0.20 : {mp.nstr(mp.mpf('0.20') - TRUE, 6)}")
print(f"  slack above 0.15 : {mp.nstr(TRUE - mp.mpf('0.15'), 6)}")
print()

print("Current inputs (Mathlib gamma at n=6, our gamma_1 bracket at m=5 / m=20):")
print(f"  gamma in (1/2, 2/3):  gamma^2 in ({mp.nstr(mp.mpf(0.25),6)}, {mp.nstr(mp.mpf(4)/9,6)})")
print(f"  best proved now: gamma_1 >= {mp.nstr(g1_lo(5),8)} (m=5), gamma_1 <= 1/100")
worst_hi = (mp.mpf(2) / 3) ** 2 + 2 * mp.mpf(1) / 100
worst_lo = mp.mpf(0.25) + 2 * g1_lo(5)
print(f"  => provable now:  {mp.nstr(worst_lo,8)} <= g^2+2g1 <= {mp.nstr(worst_hi,8)}")
print(f"     needed:        0.15 <= ... <= 0.20   -> BOTH halves fail\n")

print("Smallest n (gamma) and m (gamma_1) that would suffice, searched jointly:")
for label, target in [("upper 0.20", 'hi'), ("lower 0.15", 'lo')]:
    best = None
    for n in [6, 10, 20, 50, 100, 200, 400, 800, 1600, 3200]:
        for m in [5, 20, 50, 100, 200, 400, 800, 1600, 3200, 6400]:
            if target == 'hi':
                ok = em_hi(n) ** 2 + 2 * g1_hi(m) <= mp.mpf('0.20')
            else:
                ok = em_lo(n) ** 2 + 2 * g1_lo(m) >= mp.mpf('0.15')
            if ok:
                if best is None or n + m < best[0] + best[1]:
                    best = (n, m)
    print(f"  {label}: smallest tried (n, m) = {best}")

print()
print("Cost reading: harmonic n is an exact rational (norm_num territory) but n terms;")
print("stieltjesSeq m needs the logs of all primes <= m.")
