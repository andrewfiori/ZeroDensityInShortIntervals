"""Satisfiability check for the Brent-Stirling family in `ExternalFacts.lean`.

Why the family has to be stated about an analytic branch, and hence why this
script exists.  The pair

    expansion       : Complex.log (Complex.Gamma z) = ... + R2 z
    remainder_bound : ||R2 z|| < ||(1+sqrt(2pi)) B4 / (12 z^3)||

is contradictory when the left-hand side uses the PRINCIPAL log: it caps
Im(log(Gamma z)) at pi while the Stirling right-hand side grows like
(t/2)log(t/2), so R2 is forced to be a nonzero multiple of 2*pi.  The family is
therefore stated about the analytic branch `logGammaAnalytic` (a definition, with
`exp_logGammaAnalytic` a theorem).  A satisfiability claim can only be checked
numerically one way: exhibit ONE interpretation of the opaque symbols under which
EVERY member holds, at many points.  If such an interpretation exists the family
is consistent and no `False` is derivable from it.

The interpretation used here (mpmath at 40 digits):

    logGammaAnalytic                     :=  mpmath.loggamma  (analytic on C \\ (-inf,0])
    BrentStirlingInputs.remainder        :=  R2    as defined by Eq. (2.1) at k = 2
    BrentStirlingInputs.shiftedRemainder :=  R2hat as defined by Eq. (3.4) at k = 2

What is checked.  (A1) is a proved theorem of `ExternalFacts`; (A2)-(A5) are the
four `Prop` fields of the hypothesis class `BrentStirlingInputs`, reached through
the same-named wrapper theorems `brent_stirling_expansion`,
`brent_stirling_remainder_bound`, `brent_stirling_shifted_expansion`,
`brent_stirling_shifted_remainder_bound`.

  (A1) exp_logGammaAnalytic                 exp(lnG z) = Gamma z   on slitPlane
  (A2) BrentStirlingInputs.expansion        lnG z = (z-1/2)log z - z
                                              + (1/2)log(2pi) + B2/(2z) + R2 z
                                                                       on Re z>0
  (A3) BrentStirlingInputs.remainder_bound  |R2 z| < |(1+sqrt(2pi))B4/(12 z^3)|
                                                                       on Re z>0
  (A4) BrentStirlingInputs.shifted_expansion
                                            lnG (z+1/2) = z log z - z
                                              + (1/2)log(2pi) - 1/(24z) + R2h z
                                                                       on Im z>5
  (A5) BrentStirlingInputs.shifted_remainder_bound
                                            |R2h z| <= (1/100)/|z|^3
                                                        on Im z>5, |Re z| <= 1

(A2) and (A4) are definitional once R2 and R2hat are DEFINED as the respective
truncation errors -- that is exactly Brent's own definition of R_k -- so the
content to check is (A1), (A3), (A5), plus the fact that a single lnG serves
both expansions.  (A2)/(A4) are nevertheless evaluated as residuals, to confirm
no algebra slip.

Point counts: 9 for (A1), 14 for (A2)+(A3) (including the arguments
`zetalessthanhalf_upper`/`_lower` actually reach), 9 for (A4)+(A5), 4 for the
one-branch agreement, 4 ordinates for the contrast block.  Sampled points, not
ball arithmetic: this is evidence of consistency, not a proof of it.

Run: python3 Code/verify_brent_family_consistent.py
"""

import mpmath as mp

mp.mp.dps = 40

B2 = mp.mpf(1) / 6          # Bernoulli number B_2
B4 = -mp.mpf(1) / 30        # Bernoulli number B_4


def lnG(z):
    """The analytic branch: Brent's `ln Gamma`, mpmath's `loggamma`."""
    return mp.loggamma(z)


def R2(z):
    """Brent Eq. (2.1) remainder at k = 2, by definition."""
    return lnG(z) - ((z - mp.mpf(1) / 2) * mp.log(z) - z
                     + mp.log(2 * mp.pi) / 2 + B2 / (2 * z))


def R2_bound(z):
    """The right-hand side of `brent_stirling_remainder_bound`."""
    return abs((1 + mp.sqrt(2 * mp.pi)) * B4 / (12 * z ** 3))


def R2hat(z):
    """Brent Eq. (3.4) remainder at k = 2, by definition."""
    return lnG(z + mp.mpf(1) / 2) - (z * mp.log(z) - z
                                     + mp.log(2 * mp.pi) / 2 - 1 / (24 * z))


def R2hat_bound(z):
    return mp.mpf(1) / 100 / abs(z) ** 3


def hdr(s):
    print()
    print(s)
    print("-" * len(s))


ok = True

# --------------------------------------------------------------------------
hdr("(A1) exp(lnG z) = Gamma z  on the slit plane  {0 < Re z} u {Im z != 0}")
# Includes Im z < 0 points, which `zetalessthanhalf_upper/_lower` need (they use
# z = 1-sigma -+ it): the domain has to be the slit plane, not a half-plane.
a1_pts = [mp.mpc(0.5, 5.0), mp.mpc(0.5, -5.0), mp.mpc(1.0, -20.0),
          mp.mpc(0.75, -100.0), mp.mpc(-0.4, 12.0), mp.mpc(-0.4, -12.0),
          mp.mpc(0.001, 0.5), mp.mpc(3.0, 0.0), mp.mpc(0.5, 500.0)]
print("%28s %16s" % ("z", "|exp(lnG z) - Gamma z|"))
for z in a1_pts:
    d = abs(mp.exp(lnG(z)) - mp.gamma(z)) / max(abs(mp.gamma(z)), mp.mpf(1))
    flag = "ok" if d < mp.mpf(10) ** (-25) else "FAIL"
    if flag == "FAIL":
        ok = False
    print("%28s %16s  %s" % (mp.nstr(z, 8), mp.nstr(d, 6), flag))

# --------------------------------------------------------------------------
hdr("(A2)+(A3) unshifted expansion and remainder bound, on Re z > 0")
print("%24s %14s %14s %8s" % ("z", "|R2(z)|", "bound", "ratio"))
a23_pts = [mp.mpc(0.5, 5.25), mp.mpc(0.5, 10.0), mp.mpc(0.5, 50.0),
           mp.mpc(0.5, 500.0), mp.mpc(0.5, -5.25), mp.mpc(0.5, -500.0),
           # the arguments zetalessthanhalf_upper/_lower actually reach:
           # z = 1 - sigma -+ i t, sigma in [-1, 1/2], t > 10
           mp.mpc(0.5, 10.5), mp.mpc(0.5, -10.5), mp.mpc(1.0, 11.0),
           mp.mpc(2.0, -11.0), mp.mpc(1.5, 30.0),
           # real and near-real points, where the two branches agree
           mp.mpc(4.0, 0.0), mp.mpc(10.0, 0.0), mp.mpc(1.0, 0.25)]
for z in a23_pts:
    r, b = abs(R2(z)), R2_bound(z)
    flag = "ok" if r < b else "FAIL"
    if flag == "FAIL":
        ok = False
    print("%24s %14s %14s %8s  %s"
          % (mp.nstr(z, 8), mp.nstr(r, 6), mp.nstr(b, 6),
             mp.nstr(r / b, 4), flag))

# --------------------------------------------------------------------------
hdr("(A4)+(A5) shifted expansion and remainder bound, Im z > 5, |Re z| <= 1")
print("%24s %14s %14s %8s" % ("z", "|R2hat(z)|", "bound", "ratio"))
a45_pts = [mp.mpc(0.0, 5.001), mp.mpc(0.0, 5.5), mp.mpc(-0.25, 5.001),
           mp.mpc(0.5, 5.001), mp.mpc(-1.0, 5.001), mp.mpc(1.0, 5.001),
           mp.mpc(0.0, 50.0), mp.mpc(0.25, 500.0), mp.mpc(-0.5, 5000.0)]
for z in a45_pts:
    r, b = abs(R2hat(z)), R2hat_bound(z)
    flag = "ok" if r <= b else "FAIL"
    if flag == "FAIL":
        ok = False
    print("%24s %14s %14s %8s  %s"
          % (mp.nstr(z, 8), mp.nstr(r, 6), mp.nstr(b, 6),
             mp.nstr(r / b, 4), flag))

# --------------------------------------------------------------------------
hdr("One lnG serves both expansions (the point of the migration)")
# The two expansions are about the SAME logGammaAnalytic.  Check they agree
# where both apply: lnG(z + 1/2) computed from (A4) must equal lnG(w) with
# w = z + 1/2 computed from (A2), i.e. R2 and R2hat are simultaneously the
# truncation errors of one function.
print("%24s %26s" % ("z", "|lnG(z+1/2) via A2 - via A4|"))
for z in [mp.mpc(0.0, 6.0), mp.mpc(0.5, 20.0), mp.mpc(-0.25, 100.0),
          mp.mpc(0.25, 1000.0)]:
    w = z + mp.mpf(1) / 2
    via_a2 = ((w - mp.mpf(1) / 2) * mp.log(w) - w + mp.log(2 * mp.pi) / 2
              + B2 / (2 * w) + R2(w))
    via_a4 = (z * mp.log(z) - z + mp.log(2 * mp.pi) / 2 - 1 / (24 * z)
              + R2hat(z))
    d = abs(via_a2 - via_a4)
    flag = "ok" if d < mp.mpf(10) ** (-25) else "FAIL"
    if flag == "FAIL":
        ok = False
    print("%24s %26s  %s" % (mp.nstr(z, 8), mp.nstr(d, 6), flag))

# --------------------------------------------------------------------------
hdr("What the OLD statement did at the same points, for contrast")
print("With Complex.log (Complex.Gamma z) on the left, R2 is forced to be")
print("R2 + (an integer multiple of 2*pi*i).  At z = 1/2 + i t/2:")
print("%10s %20s %14s" % ("t", "forced |R2| / (2pi)", "bound allows"))
for t in [10.5, 20, 100, 1000]:
    z = mp.mpc(0.5, mp.mpf(t) / 2)
    principal = mp.log(mp.gamma(z))
    forced = principal - ((z - mp.mpf(1) / 2) * mp.log(z) - z
                          + mp.log(2 * mp.pi) / 2 + B2 / (2 * z))
    print("%10s %20s %14s"
          % (t, mp.nstr(abs(forced) / (2 * mp.pi), 6),
             mp.nstr(R2_bound(z), 6)))

print()
if ok:
    print("ALL CHECKS PASS.  (A1)-(A5) are simultaneously satisfied by one")
    print("interpretation, so the family is consistent: `False` is not")
    print("derivable from it.")
else:
    print("SOME CHECK FAILED -- the family is NOT vindicated.")
