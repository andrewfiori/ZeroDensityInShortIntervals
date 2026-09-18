#!/usr/bin/env python3
r"""The worked example of section 2 of `ZerosInShortIntervals.tex`: the dominant
coefficient at `alpha = 1/8`, `r = 1/2`, and the two-sided proportion it gives.

WHAT IT COMPUTES.  The tex's section 2 illustrates the Jensen mechanism at `alpha = 1/8` with the
circle radius `r = 1/2`, printing the dominant term of the zero count as `(X/pi) h log|t|` and then
the proportion of zeros with real part in `[alpha, 1-alpha]` that follows from it.  Both numbers
are recomputed here from the paper's own definitions:

    X = 2 c_{1,r} / D_{r,alpha},        D_{r,alpha} = 2 r sqrt(1-(alpha/r)^2)
                                                      - 2 alpha arctan(sqrt((r/alpha)^2-1))

and, since `N(t+h) - N(t-h)` is asymptotically `(h/pi) log|t|`, the one-sided proportion tends to
`X` and the two-sided proportion in the middle band to `1 - 2X`.

WHICH COEFFICIENT TRIPLE.  `c_{1,r}` depends on the `k = 0` anchor, and the paper offers two
admissible choices.  Remark \ref{rem:altcoefficients} (Remark 7) fixes
`(v_0, v_0', v_0'') = (27/164, 0, log 66.7)` and says its values are used in all displayed tables,
so that is what is used here; the main text's `(1/6, 1, log 0.611)` is computed alongside for
comparison, and is what the Lean formalizes.  The two agree for `k >= 1`, so they differ only where
the circle reaches the `k = 0` chord, which at `r = 1/2` it does exactly.

The printed coefficient is an upper bound, so it is rounded UP; the printed percentage is a lower
bound, so it is rounded DOWN.

Run:  python3 Code/verify_section2_worked_example.py
"""

from mpmath import mp, mpf, sqrt, atan, asin, cos, pi, log, floor, ceil

mp.dps = 40

ALPHA = mpf(1) / 8
R = mpf(1) / 2


def sigma(k):
    k = int(k)
    if k >= 0:
        return 1 - (mpf(k) + 3) / (2 ** (k + 3) - 2)
    j = -k
    return (mpf(j) + 3) / (2 ** (j + 3) - 2)


def vCoeff(k, v0):
    k = int(k)
    if k == 0:
        return v0
    if k > 0:
        return mpf(1) / (2 ** (k + 3) - 2)
    j = -k
    return sigma(j) - mpf(1) / 2 + mpf(1) / (2 ** (j + 3) - 2)


def mCoeff(k, v0):
    return (vCoeff(k, v0) - vCoeff(k + 1, v0)) / (sigma(k) - sigma(k + 1))


def bCoeff(k, v0):
    return vCoeff(k, v0) - mCoeff(k, v0) * sigma(k)


def Kidx(r):
    """Smallest k with 1 - sigma(k) <= r; 1 - sigma is strictly decreasing in k."""
    k = -60
    while 1 - sigma(k) > r:
        k += 1
    return k


def theta(k, r):
    val = (1 - sigma(k)) / r
    val = min(mpf(1), max(mpf(-1), val))
    return asin(val)


def c1(r, v0, N=200):
    """The circular average of the leading chord majorant, as defined before Proposition 8."""
    K = Kidx(r)
    thK = theta(K, r)
    s = (mCoeff(K - 1, v0) + bCoeff(K - 1, v0)) * (pi / 2 - thK)
    s -= mCoeff(K - 1, v0) * r * cos(thK)
    for j in range(N):
        k = K + j
        if sigma(k + 1) == sigma(k):
            break
        tk, tk1 = theta(k, r), theta(k + 1, r)
        s += (mCoeff(k, v0) + bCoeff(k, v0)) * (tk - tk1)
        s += mCoeff(k, v0) * r * (cos(tk) - cos(tk1))
    return s


def rectDenom(r, alpha):
    return 2 * r * sqrt(1 - (alpha / r) ** 2) - 2 * alpha * atan(sqrt((r / alpha) ** 2 - 1))


def report(name, v0):
    c = c1(R, v0)
    D = rectDenom(R, ALPHA)
    X = 2 * c / D
    prop = 1 - 2 * X
    print("  %-18s c_{1,1/2} = %s" % (name, mp.nstr(c, 12)))
    print("  %-18s X = 2c/D  = %s   (round UP:   %s)"
          % ("", mp.nstr(X, 12), mp.nstr(ceil(X * 10 ** 5) / mpf(10 ** 5), 8)))
    print("  %-18s 1 - 2X    = %s   (round DOWN: %s%%)"
          % ("", mp.nstr(prop, 12), mp.nstr(floor(prop * 10 ** 4) / mpf(100), 6)))
    print()
    return c, X, prop


if __name__ == "__main__":
    print("alpha = 1/8, r = 1/2")
    print("D_{1/2,1/8} =", mp.nstr(rectDenom(R, ALPHA), 12))
    print()
    report("Remark 7 triple", mpf(27) / 164)
    report("main-text triple", mpf(1) / 6)
    print("The tex's section 2 prints the coefficient and the percentage for the")
    print("Remark 7 triple, matching Table 2 and every other displayed table.")
