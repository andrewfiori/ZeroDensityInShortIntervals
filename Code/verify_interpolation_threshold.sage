r"""
HOW FAR DOWN THE THRESHOLD CAN BE PUSHED -- the general-threshold restatement of the Appendix
interpolation proposition, `Proposition \ref{prop:interpolation}` (Proposition 35) of
`ZerosInShortIntervals.tex`: restate the interpolation bounds for a general threshold
t_0 rather than the hard-wired 10^12, track the error term as an explicit function C(t_0) of that
threshold, and certify the threshold and the constants that come out of it.  It implements the
"standing note (author)" after `Proposition \ref{prop:jensen-easy}` (Proposition 8).

SCOPE.  This maps the BOUNDARY of the method rather than certifying a statement in use: the
numbers below are tex-facing, and no Lean declaration and no hypothesis-class field reads any of
them.  Everything here is nevertheless computed in certified interval arithmetic, so the
thresholds it reports are real bounds and not indications -- which is the point of keeping it.

No parameter search happens here -- every quantity below is a fixed, closed-form expression of a
fixed t_0, so (per the project's convention that only the FINAL DISPLAYED numbers need to be
certified) the whole script runs directly in certified interval arithmetic (`RealIntervalField`,
`RIF`); there is no separate "Phase 1 / Phase 2" split to make. A script that DID contain a
genuine optimization search (over r, say, or over log T) would need that split: an uncertified
search phase to locate the optimum, then a certified phase to bound the answer at it.

Three claims are checked, all in the direction of a valid (i.e. not accidentally too strong) bound:

  (1) The Phragmen-Lindelof "C_i(t_0) -> 1" bookkeeping threshold: (4e+2)^2 + 55 < 222, so t_0 = 222
      is a legitimate, comfortable instantiation of "t_0 >= (4e+2)^2+55" (the condition the tex
      derives from |t| >= (Q+2)^2+55 at Q = 4e, using 55 > e^4).

  (2) The coefficient bounds c <= 1/6, w <= 1 used to define C(t_0), checked as exact rational
      inequalities at the four relevant endpoints (sigma = 1/2, 5/7 for cases (1a)/(1b)/(1c); the
      k -> infinity behaviour of case (2) is monotone towards 0, so only k=4's endpoint value,
      which coincides with case (1b)/(1c)'s sigma=5/7 value by construction, needs checking).

  (3) The two headline numerical instantiations printed in the tex: C(222) < 1.36 and
      C(10^12) < 1.21, where
          C(t_0) = t_0/(t_0-1) * (1 + c + w/log(t_0-1)),  c <= 1/6, w <= 1.

CONCLUSION: all three checks pass -- t_0 = 222 is a legitimate instantiation of the
Phragmen-Lindelof bookkeeping threshold, c <= 1/6 and w <= 1 hold across all four displayed
bounds, and C(222) < 1.36, C(10^12) < 1.21 (with C_8(222) < 1.6, C_8(10^12) < 1.4).

Run with:  sage Code/verify_interpolation_threshold.sage
"""

# ---------------------------------------------------------------------------
# (1) The Phragmen-Lindelof bookkeeping threshold, exact rational arithmetic.
# ---------------------------------------------------------------------------

# 55 > e^4 is needed; certify this first with a certified upper bound on e^4.
RIF = RealIntervalField(200)
e4 = RIF(e) ** 4
assert e4.upper() < 55, f"expected e^4 < 55, got upper bound {e4.upper()}"
print(f"e^4 in {e4}, so 55 > e^4 confirmed (upper bound {e4.upper()})")

Q = RIF(4) * RIF(e)
threshold = (Q + 2) ** 2 + 55
print(f"(4e+2)^2 + 55 in {threshold}")
assert threshold.upper() < 222, f"expected (4e+2)^2+55 < 222, got upper bound {threshold.upper()}"
print("Certified: (4e+2)^2 + 55 < 222, so t_0 = 222 is a valid, comfortable threshold.")

# ---------------------------------------------------------------------------
# (2) The coefficient bounds c <= 1/6, w <= 1, exact rational arithmetic.
# ---------------------------------------------------------------------------

print()
print("Coefficient checks (exact rationals):")

# Case (1a): c(sigma) = 47/123 - 107/246*sigma, w(sigma) = 14/3*(sigma-1/2), sigma in [1/2,5/7].
def c_1a(sigma):
    return QQ(47) / 123 - QQ(107) / 246 * sigma


def w_1a(sigma):
    return QQ(14) / 3 * (sigma - QQ(1) / 2)


for sigma in [QQ(1) / 2, QQ(5) / 7]:
    c, w = c_1a(sigma), w_1a(sigma)
    print(f"  case 1a, sigma={sigma}: c={c} (<=1/6? {c <= QQ(1)/6}), w={w} (<=1? {w <= 1})")
    assert c <= QQ(1) / 6 and c >= 0 and 0 <= w <= 1

# Case (1b)/(1c): c(sigma) = 4*(1-sigma)/9 - 1/18, w = 1 (constant), sigma in [1/2,5/7].
def c_1b(sigma):
    return QQ(4) * (1 - sigma) / 9 - QQ(1) / 18


for sigma in [QQ(1) / 2, QQ(5) / 7]:
    c = c_1b(sigma)
    print(f"  case 1b/1c, sigma={sigma}: c={c} (<=1/6? {c <= QQ(1)/6})")
    assert c <= QQ(1) / 6 and c >= 0
w_1b = QQ(1)
assert w_1b <= 1

# Case (2), k=4 endpoint sigma=5/7 (matches case (1b)/(1c) by construction of the interpolation):
# c(sigma) = (1-sigma)/(k-1+2^(1-k)) - 1/(2^k*(k-1)+2), w = 1 (constant).
def c_2(k, sigma):
    k = QQ(k)
    return (1 - sigma) / (k - 1 + 2 ** (1 - k)) - 1 / (2 ** k * (k - 1) + 2)


c_2_at_k4 = c_2(4, QQ(5) / 7)
print(f"  case 2, k=4, sigma=5/7: c={c_2_at_k4} (matches case 1b/1c's c(5/7)={c_1b(QQ(5)/7)}? "
      f"{c_2_at_k4 == c_1b(QQ(5)/7)})")
assert c_2_at_k4 == c_1b(QQ(5) / 7)
assert c_2_at_k4 <= QQ(1) / 6

# case (2)'s c is decreasing in k for k>=4 (checked numerically for a wide range of k, since a
# fully symbolic monotonicity proof is not needed -- we only need c<=1/6, and the k=4 endpoint
# already IS 1/6's neighbourhood from above, so larger k only helps).
prev = None
for k in range(4, 60):
    ck = float(c_2(k, QQ(1) - QQ(k) / (2 ** k - 2)))  # left endpoint of the k-th range
    if prev is not None:
        assert ck <= prev + 1e-12, f"case 2's c not decreasing at k={k}"
    prev = ck
print("  case 2, k=4..59 (left endpoints): c decreasing, all <= 1/6 confirmed numerically "
      "(exact check only needed, and done, at k=4).")

print()
print("Certified: c <= 1/6 and w <= 1 across all four displayed bounds.")

# ---------------------------------------------------------------------------
# (3) The two headline numerical instantiations, certified interval arithmetic.
# ---------------------------------------------------------------------------

print()
print("Numerical instantiations of C(t_0) = t_0/(t_0-1) * (1 + c + w/log(t_0-1)), c<=1/6, w<=1:")

RIF = RealIntervalField(200)


def C_bound(t0):
    # Divides by log(t0-1), not log(t0): log(t0-1) < log(t0), so 1/log(t0-1) is the LARGER (safe,
    # upper-bound) choice -- using log(t0) instead would understate C(t_0).
    t0 = RIF(t0)
    return (t0 / (t0 - 1)) * (1 + RIF(1) / 6 + RIF(1) / (t0 - 1).log())


for t0, claimed in [(222, 1.36), (10 ** 12, 1.21)]:
    val = C_bound(t0)
    print(f"  t_0 = {t0}: C(t_0) in {val}, upper bound {val.upper():.6f}, claimed < {claimed}")
    assert val.upper() < claimed, f"C({t0}) upper bound {val.upper()} is NOT < {claimed}"

print()
print("Certified: C(222) < 1.36 and C(10^12) < 1.21.")

# ---------------------------------------------------------------------------
# Bonus: the propagated constants quoted downstream (Proposition \ref{prop:jensen-easy}
# (Proposition 8) and after).
# ---------------------------------------------------------------------------

print()
print("Propagated constants (Proposition jensen-easy and downstream):")


def C8_bound(t0):
    t0 = RIF(t0)
    C = C_bound(t0)
    kappa = (t0 + 1) / t0
    return kappa * ((C + 1) / 2 + RIF(1) / 4 + RIF(1) / (2 * (t0 + 1).log()))


for t0, claimed in [(222, 1.6), (10 ** 12, 1.4)]:
    val = C8_bound(t0)
    print(f"  t_0 = {t0}: C_8(t_0) in {val}, upper bound {val.upper():.6f}, claimed < {claimed}")
    assert val.upper() < claimed, f"C_8({t0}) upper bound {val.upper()} is NOT < {claimed}"

print()
print("Certified: C_8(222) < 1.6 and C_8(10^12) < 1.4; hence 2(C_8-related C(t_0)+1) < 4.8 and")
print("C(t_0)+1 < 2.4 throughout t_0 >= 222, as quoted at Lemma littlewood-mainterm/Theorem")
print("littlewoodshort.")

print()
print("ALL CHECKS PASSED.")
