r"""
INDEPENDENT CERTIFIED (arb / Sage ComplexBallField) verification of the eight compact-window
hypothesis fields of `ZerosInShortIntervals/Background/BackgroundZetaBounds.lean` (2026-09-05):

    InterpolationCertificates.interpolated_bound_1a_hcompact   -- case (1a) below
    InterpolationCertificates.interpolated_bound_1b_hcompact   -- case (1b)
    InterpolationCertificates.interpolated_bound_1c_hcompact   -- case (1c)
    Hcompact2Certificates.hcompact2_four / _five / _six / _seven  -- cases k = 4,5,6,7
    Hcompact2Certificates.hcompact2_tail                       -- the k >= 8 TAIL below

Each is the `hcompact` hypothesis of Fiori's Phragmen-Lindelof interpolation, `Proposition
\ref{prop:interpolation}` (Proposition 35), on a compact window of `t`.  Certified interval
arithmetic for `zeta` does not exist inside Lean, which is why these are hypotheses rather than
proofs.  The run recorded in those classes' docstrings prints `ALL CERTIFIED` with 125 / 264 / 137
boxes for (1a)/(1b)/(1c), 292 / 302 / 588 / 926 for k = 4..7, and 232 for the tail.

Written from the Lean statements (see `indep_mpmath_hcompact.py` for the transcription and for
the floating-point picture), NOT from `verify_hcompact_boxes.sage`: the point is a second
implementation from the statement, so that a transcription error in the first would show up.  `hcompact2_tail` is the
substantive addition -- `verify_hcompact_boxes.sage` checks case (2) only at the finitely many
`k = 4..16` and argues the rest in prose, which left a real uniformity-in-`k` gap.

METHOD (rigorous).  For a box  sigma in [s0,s1], t in [t0,t1]  (t >= 0 suffices: both sides of
the inequality are conjugation invariant):

  * LHS upper bound:  |(s-1) zeta(s)| enclosed over s = (ball over [s0,s1]) + i (ball over [t0,t1]) by a
    second-order Taylor expansion about the box centre with the `zeta''` remainder evaluated on the
    whole box (`f_enclosure` below), then `.abs().upper()`.  (Arb's zeta applied directly to the box
    ball is valid but hopelessly loose -- radius 0.08 on a box of radius 0.004 -- so a first attempt
    with it could not certify (1b) at any depth; the Taylor form is exact to O(radius^2).)
  * RHS lower bound:  log RHS(sigma,t) is AFFINE in sigma for fixed t (the tau-infima do not depend
    on sigma, the exponents alpha_i w_a + beta_i w_b do, linearly), so its infimum over sigma in
    [s0,s1] is attained at s0 or s1.  Each of the two is evaluated with sigma EXACT and t a ball;
    the tau-infimum of |G_i(tau + it)| over tau in [a,b] is bounded below by
       - the exact endpoint value for the linear G's (|C(Q+tau+it)| increasing in tau for Q>=0,
         |C(Q-tau-it)| decreasing for Q-tau>0 -- both proved in PhragmenLindelofSetup), and
       - for GPL / G1shift, the minimum over a tau-partition of [a,b] of the ball lower bound of
         |G(tau_ball + i t_ball)|  (a valid lower bound for every tau in [a,b] and every t in the t-ball).
    The product of lower bounds raised to the (nonnegative) exponents is a lower bound; `.lower()`.
  * The box PASSES if  LHS.upper() < RHS_lower.  Otherwise it is bisected (in t, and in sigma when the
    sigma-width is the larger relative size) down to a depth limit.

If every box of a case passes, the Lean statement of that case is certified (modulo arb).

CASES: (1a), (1b), (1c), hcompact2 k = 4,5,6,7, and the TAIL k >= 8 via the k-uniform lower bound
       RHS_k(sigma,t) >= R_low(t) := min(base, base^(1+p_8)) * (1-sigma_9)^(q_8) * inf_{tau in [sigma_8,1]} |GPL_e(tau+it)|,
         base = 1.546^(1/(1+p_8)) sqrt(sigma_8^2 + t^2),
       valid for all k >= 8 and sigma in [sigma_k, sigma_{k+1}] (derivation in the docstring of the
       tail block below), against  sup_{sigma in [sigma_8, 1]} |(s-1)zeta(s)|.  Near s = 1 arb cannot
       evaluate (s-1)zeta(s) on a ball containing 1, so for boxes within |s-1| <= 1/4 the bound
       |(s-1)zeta(s) - 1| <= |s-1| * M,  M := max_{|w-1| = 1/4} |zeta(w) - 1/(w-1)|  (maximum modulus of
       the entire function zeta(w) - 1/(w-1)) is used, with M itself certified by balls on the circle.

Run with:  sage Code/indep_arb_hcompact.sage
"""
import time

PREC = 100
CB = ComplexBallField(PREC)
RB = RealBallField(PREC)
E_RB = RB(1).exp()


def ball(lo, hi):
    lo, hi = RB(lo), RB(hi)
    return RB(lo.union(hi))


def GPL(Q, s):
    return (CB(Q + s).log() + CB(Q + 2 - s).log()) / 2


def f_enclosure(sball, tball):
    r"""Rigorous enclosure of f(s) = (s-1) zeta(s) over the box s = sball + i tball, by a
    second-order Taylor expansion about the box centre m:
        f(s) = f(m) + f'(m)(s-m) + (s-m)^2 * int_0^1 (1-u) f''(m+u(s-m)) du,
    and the integral lies in (1/2) * hull(f''(box)).  Arb's plain `zeta` on a ball of radius 0.004
    returns a radius ~0.08 (checked), far too loose for the 5% margin of case (1b); this form is
    exact to O(radius^2)."""
    m = CB(RB(sball.mid()), RB(tball.mid()))
    S = CB(sball, tball)
    fm = (m - 1) * m.zeta()
    f1m = m.zeta() + (m - 1) * zetaderiv(1, m)
    f2S = 2 * zetaderiv(1, S) + (S - 1) * zetaderiv(2, S)
    d = S - m
    return fm + f1m * d + f2S * d * d / 2


class Case:
    def __init__(self, name, a, b, T0, Gs, alpha, beta):
        self.name, self.a, self.b, self.T0 = name, a, b, T0
        self.Gs, self.alpha, self.beta = Gs, alpha, beta   # Gs: list of (kind, function on CB)

    def inf_lower(self, tball, ntau=8):
        out = []
        for kind, G in self.Gs:
            if kind == "linG":
                out.append(G(CB(RB(self.a), tball)).abs().lower())
            elif kind == "linGRefl":
                out.append(G(CB(RB(self.b), tball)).abs().lower())
            else:
                best = None
                for j in range(ntau):
                    tau = ball(self.a + (self.b - self.a) * j / ntau, self.a + (self.b - self.a) * (j + 1) / ntau)
                    v = G(CB(tau, tball)).abs().lower()
                    best = v if best is None else min(best, v)
                out.append(best)
        return out

    def rhs_lower(self, sig, tball, infs):
        # sig exact rational; exponents exact rationals or RB
        wa = (self.b - sig) / (self.b - self.a)
        wb = (sig - self.a) / (self.b - self.a)
        val = RB(1)
        for i, m in enumerate(infs):
            ex = RB(self.alpha[i] * wa + self.beta[i] * wb)
            val *= RB(m) ** ex
        return val.lower()

    def lhs_upper(self, sball, tball):
        return f_enclosure(sball, tball).abs().upper()

    def check_box(self, s0, s1, t0, t1, depth, stats, maxdepth=14):
        stats["boxes"] += 1
        tball = ball(t0, t1)
        infs = self.inf_lower(tball)
        L = min(self.rhs_lower(s0, tball, infs), self.rhs_lower(s1, tball, infs))
        U = self.lhs_upper(ball(s0, s1), tball)
        if U < L:
            stats["worst"] = max(stats["worst"], RR(U) / RR(L))
            return True
        if depth >= maxdepth:
            stats["failed"].append((s0, s1, t0, t1, RR(U), RR(L)))
            return False
        # bisect the relatively wider side
        ok = True
        if (s1 - s0) / (self.b - self.a) > (t1 - t0) / max(self.T0, 1):
            sm = (s0 + s1) / 2
            ok &= self.check_box(s0, sm, t0, t1, depth + 1, stats, maxdepth)
            ok &= self.check_box(sm, s1, t0, t1, depth + 1, stats, maxdepth)
        else:
            tm = (t0 + t1) / 2
            ok &= self.check_box(s0, s1, t0, tm, depth + 1, stats, maxdepth)
            ok &= self.check_box(s0, s1, tm, t1, depth + 1, stats, maxdepth)
        return ok

    def run(self, nt0=None):
        stats = {"boxes": 0, "worst": RR(0), "failed": []}
        t_start = time.time()
        # initial t-partition of [0,T0] into pieces of width ~1/8, sigma whole
        T0 = self.T0
        n = nt0 or int(ceil(RR(T0) * 8))
        ok = True
        for i in range(n):
            t0 = T0 * i / n
            t1 = T0 * (i + 1) / n
            ok &= self.check_box(self.a, self.b, t0, t1, 0, stats)
        el = time.time() - t_start
        print(f"  {self.name:8s}: {'CERTIFIED' if ok else 'FAILED'}  boxes={stats['boxes']:5d}  "
              f"worst certified U/L={stats['worst']:.4f}  ({el:.1f}s)")
        for f in stats["failed"][:5]:
            print(f"      unresolved box sigma[{RR(f[0]):.4f},{RR(f[1]):.4f}] t[{RR(f[2]):.4f},{RR(f[3]):.4f}]: U={f[4]:.4f} L={f[5]:.4f}")
        return ok


def interpG(A, B, p, q, Q):
    A, B = RB(A), RB(B)
    C0 = A ** (RB(1) / (p + 1))
    C1 = (B / C0) ** (RB(1) / q)
    return [("linG", lambda s: CB(C0) * s), ("linGRefl", lambda s: CB(C1) * (1 - s)),
            ("GPL", lambda s: GPL(Q, s))]


def interpG1c(B, c, d, q, Q):
    B, c, d = RB(B), RB(c), RB(d)
    C2 = B ** (RB(1) / q)
    return [("linG", lambda s: s), ("G1shift", lambda s: CB(c) * GPL(Q, s + 1) + CB(d)),
            ("linGRefl", lambda s: CB(C2) * (1 - s)), ("GPL", lambda s: GPL(Q, s))]


def sigma_k(k):
    return 1 - QQ(k) / (2 ** k - 2)


print("=" * 90)
print("Certified box checks (arb, prec 100 bits). t >= 0 only (conjugation symmetry).")
print("=" * 90)
T0_big = 4 * E_RB + 1
p, q = QQ(27) / 164, QQ(1) / 14
results = {}
results["1a"] = Case("1a", QQ(1) / 2, QQ(5) / 7, T0_big, interpG(RB("66.7"), RB("1.546"), p, q, 4 * E_RB),
                     [p + 1, 0, 0], [1, q, 1]).run()
p = QQ(1) / 6
results["1b"] = Case("1b", QQ(1) / 2, QQ(5) / 7, RB(3), interpG(RB("0.611"), RB("1.546"), p, q, RB(16)),
                     [p + 1, 0, 1], [1, q, 1]).run()
results["1c"] = Case("1c", QQ(1) / 2, QQ(5) / 7, T0_big,
                     interpG1c(RB("1.546"), RB("0.470795"), RB("4.04972"), q, 4 * E_RB),
                     [p + 1, 1, 0, 0], [1, 0, q, 1]).run()
for k in range(4, 8):
    a, b = sigma_k(k), sigma_k(k + 1)
    pk, qk = QQ(1) / (2 ** k - 2), QQ(1) / (2 ** (k + 1) - 2)
    results[f"k={k}"] = Case(f"2:k={k}", a, b, RB(3), interpG(RB("1.546"), RB("1.546"), pk, qk, E_RB),
                             [pk + 1, 0, 1], [1, qk, 1]).run()

# --------------------------------------------------------------------------------------------
# TAIL k >= 8.
#
# RHS_k(sigma,t) = (A^(1/(p+1)) sqrt(a^2+t^2))^(1 + p w_a) * ((A^(p/(p+1)))^(1/q) sqrt((1-b)^2+t^2))^(q w_b) * inf_tau |GPL_e|
#   with a = sigma_k, b = sigma_{k+1}, p = 1/(2^k-2), q = 1/(2^{k+1}-2), A = 1.546, w_a + w_b = 1, w_a,w_b in [0,1].
#   * factor 0: base_k := A^(1/(p+1)) sqrt(a^2+t^2) >= base_low := A^(1/(1+p_8)) sqrt(sigma_8^2+t^2) for k>=8
#     (p decreasing in k, a = sigma_k increasing); exponent in [1, 1+p] subset [1, 1+p_8];
#     so factor0 >= min(base_low, base_low^(1+p_8)).
#   * factor 1: (A^(p/(p+1)))^(w_b) >= 1 and ((1-b)^2+t^2)^(q w_b/2) >= min(1, (1-b)^q) = (1-b_k)^(q_k) >= (1-sigma_9)^(q_8)
#     (q_k |log(1-b_k)| is decreasing in k: check printed below for k = 8..40).
#   * factor 2: inf over tau in [sigma_k, sigma_{k+1}] subset [sigma_8, 1] >= inf over [sigma_8, 1].
# LHS: sup over sigma in [sigma_8, 1] of |(s-1) zeta(s)|.
# --------------------------------------------------------------------------------------------
print()
print("=" * 90)
print("TAIL k >= 8 (hcompact2_tail): k-uniform lower bound on RHS vs sup over sigma in [sigma_8, 1] of LHS")
print("=" * 90)
A = RB("1.546")
s8, s9 = sigma_k(8), sigma_k(9)
p8, q8 = QQ(1) / (2 ** 8 - 2), QQ(1) / (2 ** 9 - 2)
mono_ok = True
prev = None
for k in range(8, 41):
    bk = sigma_k(k + 1)
    qk = QQ(1) / (2 ** (k + 1) - 2)
    val = RR(qk) * abs(RR(log(RR(1 - bk))))
    if prev is not None and val > prev:
        mono_ok = False
    prev = val
print(f"  q_k |log(1-sigma_(k+1))| decreasing for k=8..40: {mono_ok}   -> (1-sigma_(k+1))^q_k >= (1-sigma_9)^q_8 = {RR((1-s9)**q8):.6f}")
term1_low = RB(1 - s9) ** RB(q8)

# M = max_{|w-1| = 1/4} |zeta(w) - 1/(w-1)| certified on arcs
M = RR(0)
NARC = 64
for j in range(NARC):
    th = ball(2 * RB.pi() * j / NARC, 2 * RB.pi() * (j + 1) / NARC)
    w = CB(1) + CB(RB(1) / 4) * CB(th.cos(), th.sin())
    v = (w.zeta() - 1 / (w - 1)).abs().upper()
    M = max(M, RR(v))
M = RB(M)
print(f"  M = max_(|w-1|=1/4) |zeta(w) - 1/(w-1)| <= {RR(M.upper()):.6f}  (true value ~ gamma + ... )")


def tail_R_low(tball):
    base = A ** (RB(1) / (1 + p8)) * (RB(s8) ** 2 + tball ** 2).sqrt()
    f0 = RB(min(base.lower(), (base ** RB(1 + p8)).lower()))
    best = None
    for j in range(16):
        tau = ball(s8 + (1 - s8) * j / 16, s8 + (1 - s8) * (j + 1) / 16)
        v = GPL(E_RB, CB(tau, tball)).abs().lower()
        best = v if best is None else min(best, v)
    return (f0 * term1_low * RB(best)).lower()


def tail_lhs_upper(s0, s1, t0, t1):
    sball, tball = ball(s0, s1), ball(t0, t1)
    # if the box is within |s-1| <= 1/4 use the Laurent bound (arb cannot enclose zeta on a ball containing 1).
    # `rad` is computed from the exact rational corners, rounded up (a ball sqrt of a ball touching 0 is NaN).
    rad = RealField(PREC, rnd='RNDU')(max((1 - s0) ** 2, (1 - s1) ** 2) + max(t0 ** 2, t1 ** 2)).sqrt()
    if rad <= RR(1) / 4:
        return (RB(1) + RB(rad) * M).upper()
    return f_enclosure(sball, tball).abs().upper()


def tail_check(s0, s1, t0, t1, depth, stats, maxdepth=12):
    stats["boxes"] += 1
    L = tail_R_low(ball(t0, t1))
    U = tail_lhs_upper(s0, s1, t0, t1)
    if U < L:
        stats["worst"] = max(stats["worst"], RR(U) / RR(L))
        return True
    if depth >= maxdepth:
        stats["failed"].append((s0, s1, t0, t1, RR(U), RR(L)))
        return False
    ok = True
    if (s1 - s0) / (1 - s8) > (t1 - t0) / 3:
        sm = (s0 + s1) / 2
        ok &= tail_check(s0, sm, t0, t1, depth + 1, stats, maxdepth)
        ok &= tail_check(sm, s1, t0, t1, depth + 1, stats, maxdepth)
    else:
        tm = (t0 + t1) / 2
        ok &= tail_check(s0, s1, t0, tm, depth + 1, stats, maxdepth)
        ok &= tail_check(s0, s1, tm, t1, depth + 1, stats, maxdepth)
    return ok


stats = {"boxes": 0, "worst": RR(0), "failed": []}
t_start = time.time()
ok = True
for i in range(12):
    ok &= tail_check(s8, QQ(1), QQ(i) / 4, QQ(i + 1) / 4, 0, stats)
print(f"  TAIL k>=8: {'CERTIFIED' if ok else 'FAILED'}  boxes={stats['boxes']}  worst U/L={stats['worst']:.4f}  ({time.time()-t_start:.1f}s)")
for f in stats["failed"][:5]:
    print(f"      unresolved box sigma[{RR(f[0]):.4f},{RR(f[1]):.4f}] t[{RR(f[2]):.4f},{RR(f[3]):.4f}]: U={f[4]:.4f} L={f[5]:.4f}")
results["tail"] = ok

print()
print("=" * 90)
print("SUMMARY")
print("=" * 90)
for k, v in results.items():
    print(f"  {k:6s}: {'CERTIFIED' if v else 'NOT certified'}")
print("ALL CERTIFIED" if all(results.values()) else "SOME CASES NOT CERTIFIED -- see above")
