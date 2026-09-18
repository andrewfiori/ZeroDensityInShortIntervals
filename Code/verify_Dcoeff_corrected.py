#!/usr/bin/env python3
"""
Check the corrected 1/t^2 coefficient  D(s) = s(2s-1)(1-s)/12  of
`Lemma \\ref{lem:zetalessthanhalf}` (Lemma 36), in

  log|zeta(s+it)| = log|zeta(1-s+it)| + (1/2-s)log|t/2| + (s-1/2)log(pi)
                    + D(s)/t^2 + residual.

D is the polynomial Lean now calls `Dcoeff` (with `Dcoeff2 := Dcoeff`).  This
file's `Dcoeff_old` and `Dcoeff2_old` are the two SUPERSEDED polynomials the Lean
statements used to carry; they are kept here only so that the test which exposed
them can still be run, and they are not what Lean means by `Dcoeff` today.

Method: mpmath at 30 digits on sampled points -- evidence, not a certificate.
The Lean statements are proved outright (`gamma_cos_estimate_general`,
`zetalessthanhalf_upper_tight`, `_lower_tight`, `_collapsed`), so this is an
independent recomputation of their constants, not a hypothesis-class certificate.

Three things are checked:
  (A) sup|D| on [0,1/2] and on [-1,0] -- endpoints plus the two roots of D' --
      against the tex's OLD constants 7*sqrt(7)/108 and 7/3, which were derived
      from the superseded polynomials and must remain valid majorants for the
      true D, or the tex changes too.  (They do remain valid; the corrected tex
      and the Lean proof have since sharpened them to sqrt(3)/216 and 1/2.)
  (B) that D really is the 1/t^2 coefficient, i.e. residual*t^3 stays bounded
      rather than growing --- the exact test that exposed the old Dcoeff2, whose
      residual*t^3 grows linearly instead of settling;
  (C) the residual constants 1.21 (upper range) and 7.88 (lower range).  These
      too are the tex's OLD 1/t^3 constants; Lean now proves the sharper 0.06 and
      1.4, so clearing 1.21/7.88 is necessary but not sufficient for the current
      statements -- the measured sups are far inside both pairs.

(B) and (C) run over s in {0, 0.1, 0.25, 0.4, 0.5} and s in {-1, -0.75, -0.5,
-0.25, 0}, each at t in {100, 1000, 10000}.

D is a SINGLE polynomial valid on both s-ranges: the derivation never uses the
sign of s, which is why one definition can replace both Dcoeff and Dcoeff2.
"""

from mpmath import mp, mpf, mpc, zeta, log, pi, sqrt, fabs, findroot, nstr

mp.dps = 30


def D(s):
    return s * (2 * s - 1) * (1 - s) / 12


def Dcoeff_old(s):
    return -((2 * s - 1) * (3 * s ** 2 - 3 * s - 1)) / 6


def Dcoeff2_old(s):
    return -(6 * s ** 3 + 6 * s ** 2 + 25 * s + 11) / 6


# ---------------------------------------------------------------- (A) sup |D|
print("(A) sup |D| against the tex's constants")
crit = [(3 - sqrt(3)) / 6, (3 + sqrt(3)) / 6]     # D'(s) = 0
for name, lo, hi, texconst, texname in [
        ("[0,1/2]  (upper)", mpf(0), mpf(1) / 2, 7 * sqrt(7) / 108, "7*sqrt(7)/108"),
        ("[-1,0]   (lower)", mpf(-1), mpf(0), mpf(7) / 3, "7/3")]:
    pts = [lo, hi] + [c for c in crit if lo <= c <= hi]
    suD = max(fabs(D(p)) for p in pts)
    suOld = max(fabs(Dcoeff_old(p) if lo >= 0 else Dcoeff2_old(p)) for p in pts)
    print(f"  {name}: sup|D_true| = {nstr(suD, 8):>14}   "
          f"sup|D_old| = {nstr(suOld, 8):>14}   tex {texname} = {nstr(texconst, 8)}")
    print(f"      tex constant still a valid majorant for D_true: "
          f"{'YES' if suD <= texconst else 'NO -- TEX MUST CHANGE'}")
print()

# ------------------------------------------------- (B)/(C) residual behaviour
def residual(s, t):
    z1 = zeta(mpc(s, t))
    z2 = zeta(mpc(1 - s, t))
    if z1 == 0 or z2 == 0:
        return None
    lhs = log(fabs(z1))
    rhs = (log(fabs(z2)) + (mpf(1) / 2 - s) * log(fabs(t / 2))
           + (s - mpf(1) / 2) * log(pi) + D(s) / t ** 2)
    return lhs - rhs


print("(B)/(C) residual * t^3  -- bounded means D is the right coefficient")
for label, svals, claimed in [
        ("upper  s in [0,1/2]", ['0', '0.1', '0.25', '0.4', '0.5'], mpf('1.21')),
        ("lower  s in [-1,0] ", ['-1', '-0.75', '-0.5', '-0.25', '0'], mpf('7.88'))]:
    print(f"  {label}   (tex claims residual*t^3 <= {claimed})")
    print(f"    {'s':>7} " + "".join(f"{'t=' + t:>16}" for t in
                                     ['100', '1000', '10000']))
    worst = mpf(0)
    for s in svals:
        ss = mpf(s)
        row = f"    {s:>7} "
        for t in ['100', '1000', '10000']:
            tt = mpf(t)
            r = residual(ss, tt)
            if r is None:
                row += f"{'zero':>16}"
                continue
            v = fabs(r) * tt ** 3
            worst = max(worst, v)
            row += f"{nstr(v, 8):>16}"
        print(row)
    print(f"    worst residual*t^3 over this grid: {nstr(worst, 8)}   "
          f"{'within' if worst <= claimed else 'EXCEEDS'} the claimed {claimed}")
    print()

print("Contrast -- the SAME test with the old polynomials, which is how the")
print("defect was found (residual*t^3 grows linearly instead of settling):")
for s in ['0', '-1']:
    ss = mpf(s)
    old = Dcoeff_old if ss >= 0 else Dcoeff2_old
    print(f"    s = {s:>3}:", end="")
    for t in ['100', '1000', '10000']:
        tt = mpf(t)
        z1, z2 = zeta(mpc(ss, tt)), zeta(mpc(1 - ss, tt))
        lhs = log(fabs(z1))
        rhs = (log(fabs(z2)) + (mpf(1) / 2 - ss) * log(fabs(tt / 2))
               + (ss - mpf(1) / 2) * log(pi) + old(ss) / tt ** 2)
        print(f"  t={t}: {nstr(fabs(lhs - rhs) * tt ** 3, 6):>12}", end="")
    print()
