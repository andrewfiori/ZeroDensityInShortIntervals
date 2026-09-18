#!/usr/bin/env python3
"""Can `logderzetabound`'s claims be extended past x = 2 by a monotonicity argument?

Exploratory; no Lean target.  Nothing in the development needs the extension -- this records
what it would and would not buy, and which routes to it fail, so that they are not retried.

Background.  `logderzetabound_claim_two`/`_three` (Background/LogDerivZetaLaurent.lean) are
proved on `0 < x <= 2`; the ceiling comes from `logDerivZetaCoeff_antitone`, i.e. from the
alternating-series machinery, not from anything about zeta.  Claim 2's N = 1 upper bound is
consumed as `neg_logDeriv_zeta_bound_of_claim_two`, which is the truncated Laurent estimate
-zeta'/zeta(1+z) < 1/z - gamma + (gamma^2+2*gamma_1)z used by
Proposition \\ref{prop:integraloutside} (Proposition 15) -- and used there only on (0,2].

Proposal under test: LHS(x) = -Re(zeta'/zeta)(1+x) is decreasing in x; if the RHS is increasing
past x = 2, truth at x = 2 extends to all x > 2.

This script checks (i) whether the RHS really is increasing at 2, (ii) whether the conclusion
survives anyway via a better route, (iii) whether the same works for the other three
inequalities in claims 2 and 3, and (iv) the N = 0 form of claim 3's upper bound,
log(zeta(1+ru)) <= -log(ru) + gamma*ru, which the tex cites inside the proof of
Proposition \\ref{prop:outside3} (Proposition 23).

READ (i) CAREFULLY: it REFUTES the monotonicity premise rather than supporting it.  The N=1
RHS is still *decreasing* at x = 2 (RHS'(2) = -0.0625) and only turns at x* = 1/sqrt(c) =
2.3091.  The conclusion nonetheless holds, by (ii), which needs no monotonicity of the RHS at
all -- only the AM-GM floor  1/x + c*x >= 2*sqrt(c).

Pure-Python (mpmath only); no Sage required.
"""

from mpmath import mp, mpf, zeta, euler, log, sqrt, exp, taylor, diff, findroot

mp.dps = 30

GAMMA = +euler


def stieltjes(n):
    return mp.stieltjes(n)


def LHS(x):
    """-zeta'(1+x)/zeta(1+x), real for real x > 0."""
    s = 1 + mpf(x)
    return -diff(zeta, s) / zeta(s)


def coeffs(N=6):
    """a_n with  -zeta'/zeta(1+z) = 1/z + sum_n (-1)^{n+1} a_n z^n."""
    g = lambda z: -diff(zeta, 1 + z) / zeta(1 + z) - 1 / z
    t = taylor(g, 0, N, method='quad', radius=mpf('0.3'))
    return [((-1) ** (n + 1)) * t[n] for n in range(N + 1)]


def main():
    a = coeffs(4)
    a0, a1, a2 = a[0], a[1], a[2]
    print("== coefficients ==")
    print("  a0            = %s   (gamma = %s)" % (mp.nstr(a0, 18), mp.nstr(GAMMA, 18)))
    print("  a1            = %s   (gamma^2+2*gamma_1 = %s)"
          % (mp.nstr(a1, 18), mp.nstr(GAMMA ** 2 + 2 * stieltjes(1), 18)))
    print("  a2            = %s" % mp.nstr(a2, 18))

    c = GAMMA ** 2 + 2 * stieltjes(1)
    print()
    print("== (i) is the N=1 RHS  1/x - gamma + c*x  increasing at x = 2? ==")
    print("  c = gamma^2 + 2*gamma_1 = %s" % mp.nstr(c, 18))
    zstar = 1 / sqrt(c)
    print("  RHS'(x) = -1/x^2 + c  vanishes at x* = 1/sqrt(c) = %s" % mp.nstr(zstar, 18))
    print("  RHS'(2) = %s   -> %s at x = 2"
          % (mp.nstr(-1 / mpf(4) + c, 12),
             "INCREASING" if -1 / mpf(4) + c > 0 else "still DECREASING"))
    print("  So the premise is false: the RHS turns at x* = %s > 2." % mp.nstr(zstar, 8))

    print()
    print("== (ii) the conclusion survives anyway, via AM-GM instead of monotonicity ==")
    rhs_min = 2 * sqrt(c) - GAMMA
    print("  1/x + c*x >= 2*sqrt(c) for ALL x > 0, so  RHS(x) >= 2*sqrt(c) - gamma = %s"
          % mp.nstr(rhs_min, 18))
    print("  (attained at x = x*, value RHS(x*) = %s -- agrees)"
          % mp.nstr(1 / zstar - GAMMA + c * zstar, 18))
    L2 = LHS(2)
    print("  LHS(2) = -zeta'(3)/zeta(3) = %s" % mp.nstr(L2, 18))
    print("  LHS is decreasing (termwise: sum Lambda(n) n^{-(1+x)}), so for x >= 2")
    print("      LHS(x) <= LHS(2) = %s  <  %s = min RHS" % (mp.nstr(L2, 12), mp.nstr(rhs_min, 12)))
    print("  margin = %s" % mp.nstr(rhs_min - L2, 12))
    print("  VERDICT: %s" % ("extends to all x > 2" if L2 < rhs_min else "FAILS"))

    print()
    print("  smallest x0 for which this closes (LHS(x0) < min RHS):")
    x0 = findroot(lambda x: LHS(x) - rhs_min, mpf('1.5'))
    print("    LHS(x) = min RHS at x = %s, so any x0 >= that works; x0 = 2 has room."
          % mp.nstr(x0, 12))

    print()
    print("== (iii) the other three inequalities at N = 1 ==")
    # claim 2 lower:  1/x - a0 + a1 x - a2 x^2  <  LHS
    lo2 = lambda x: 1 / x - a0 + a1 * x - a2 * x ** 2
    # claim 3 lower:  -log x + a0 x - (a1/2) x^2      <  log zeta(1+x)
    lo3 = lambda x: -log(x) + a0 * x - a1 / 2 * x ** 2
    # claim 3 upper:  log zeta(1+x) <  -log x + a0 x - (a1/2) x^2 + (a2/3) x^3
    up3 = lambda x: -log(x) + a0 * x - a1 / 2 * x ** 2 + a2 / 3 * x ** 3
    logz = lambda x: log(zeta(1 + x))

    print("  claim 2 LOWER bound  (need RHS_lo < LHS):")
    for x in ['2', '2.2', '2.5', '3', '4']:
        x = mpf(x)
        print("    x=%-4s  bound=%-14s LHS=%-14s  %s"
              % (mp.nstr(x, 4), mp.nstr(lo2(x), 10), mp.nstr(LHS(x), 10),
                 "ok" if lo2(x) < LHS(x) else "FAILS"))
    print("    -> bound is DECREASING past 2 (same direction as LHS): no free ride.")
    print("       It does go negative (LHS > 0 always) at x = %s, so only the"
          % mp.nstr(findroot(lo2, mpf('2.5')), 8))
    print("       finite window [2, that] needs real work.")

    print()
    print("  claim 3 LOWER bound  (need bound < log zeta(1+x)):")
    for x in ['2', '2.5', '3', '4']:
        x = mpf(x)
        print("    x=%-4s  bound=%-14s logz=%-14s  %s"
              % (mp.nstr(x, 4), mp.nstr(lo3(x), 10), mp.nstr(logz(x), 10),
                 "ok" if lo3(x) < logz(x) else "FAILS"))
    print("    -> bound -> -infty, log zeta -> 0+. Extends, but again only after a")
    print("       finite window; it is already negative at x = %s."
          % mp.nstr(findroot(lo3, mpf('2.5')), 8))

    print()
    print("  claim 3 UPPER bound  (need log zeta(1+x) < bound):")
    for x in ['2', '2.5', '3', '4', '6']:
        x = mpf(x)
        print("    x=%-4s  logz=%-14s bound=%-14s  %s"
              % (mp.nstr(x, 4), mp.nstr(logz(x), 10), mp.nstr(up3(x), 10),
                 "ok" if logz(x) < up3(x) else "FAILS"))
    print("    -> bound -> +infty (a2/3 x^3), log zeta -> 0+. Needs a global min of a")
    print("       cubic-plus-log, not a two-term AM-GM: doable but not free.")

    print()
    print("== (iv) claim 3 UPPER at N = 0 -- the form tex Prop 22 actually cites ==")
    print("   tex line 776:  log(zeta(1+ru)) <= -log(ru) + gamma*ru")
    up3_0 = lambda x: -log(x) + a0 * x
    # min of -log x + gamma x is at x = 1/gamma, value 1 + log(gamma)
    xmin = 1 / a0
    floor = 1 + log(a0)
    print("   min of -log x + gamma*x at x = 1/gamma = %s, value 1+log(gamma) = %s"
          % (mp.nstr(xmin, 12), mp.nstr(floor, 18)))
    print("   check against direct evaluation: %s" % mp.nstr(up3_0(xmin), 18))
    print("   log zeta(1+2) = %s   (decreasing in x)" % mp.nstr(logz(2), 18))
    print("   margin = %s" % mp.nstr(floor - logz(2), 12))
    print("   VERDICT: %s"
          % ("extends to all x >= 2 by the SAME global-floor argument"
             if logz(2) < floor else "FAILS"))
    for x in ['2', '3', '5', '10']:
        x = mpf(x)
        print("     x=%-4s  logz=%-14s bound=%-14s  %s"
              % (mp.nstr(x, 4), mp.nstr(logz(x), 10), mp.nstr(up3_0(x), 10),
                 "ok" if logz(x) < up3_0(x) else "FAILS"))


if __name__ == "__main__":
    main()
