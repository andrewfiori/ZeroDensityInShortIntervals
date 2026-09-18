#!/usr/bin/env python3
"""Independent numeric check of the closed form and monotonicity behind step (iii) of
`RectangularBounds.jensenrectangle`.

Nothing here is a certificate: `RectangularBounds.rectDenom` is a Lean definition and
`RectangularBounds.rectDenom_le_window` a proved theorem, and no hypothesis-class field is
involved.
It is an independent evaluation of statements the formalization already establishes, kept because
the closed form is the one place where a sign or a factor of two would silently change every
`B_{i,alpha,r}`.

Step (iii) of Proposition \\ref{prop:jensenrectangle} (Proposition 19) says: a zero
`rho = beta + i*gamma` lying in the disc of radius `r` about `1 + i(T+x)`, with
`1 - beta = b <= alpha`, contributes at least `rectDenom r alpha` to the integrated Jensen defect.
The contribution is

    W(r,b) := int_{-c}^{c} [ log r - (1/2) log(b^2 + y^2) ] dy,      c = sqrt(r^2 - b^2)

(the `y`-range being exactly where `b^2 + y^2 <= r^2`, i.e. where the zero is inside the disc).

This script checks the three facts the Lean statements assert:

  (A)  W(r,b) = 2*sqrt(r^2-b^2) - 2*b*arctan(sqrt(r^2-b^2)/b)
  (B)  rectDenom r b = 2*r*sqrt(1-(b/r)^2) - 2*b*arctan(sqrt((r/b)^2-1))  equals that same value
  (C)  d/db W(r,b) = -2*arctan(sqrt(r^2-b^2)/b)  < 0,  so W is strictly antitone in b.

NOTE on (C): it is *not* what the Lean proof uses, and is kept here only as a cross-check.
Antitonicity of W compares each zero's own disc-chord window, and for b <= alpha that window
is the *wider* one -- wider than the fixed [-hatAlpha, hatAlpha] that Proposition
\\ref{prop:jensenrectangle} (Proposition 19) actually integrates over, so step (ii) cannot supply
it.  Over the fixed window the comparison is pointwise (log is monotone), which is how
`rectDenom_le_window` proves it.  Only checks (A) at b = alpha and (B) are load-bearing.

Pure-Python (mpmath only); no Sage required.  40 decimal digits of plain floating point, not
interval arithmetic: the residuals printed are evidence, not enclosures.
"""

from mpmath import mp, mpf, sqrt, atan, log, quad, diff

mp.dps = 40


def W_quad(r, b):
    """The defining integral, by quadrature."""
    c = sqrt(r ** 2 - b ** 2)
    return quad(lambda y: log(r) - log(b ** 2 + y ** 2) / 2, [-c, 0, c])


def W_closed(r, b):
    """The claimed closed form."""
    c = sqrt(r ** 2 - b ** 2)
    return 2 * c - 2 * b * atan(c / b)


def rectDenom(r, a):
    """The Lean/tex definition of `rectDenom`, verbatim."""
    return 2 * r * sqrt(1 - (a / r) ** 2) - 2 * a * atan(sqrt((r / a) ** 2 - 1))


def main():
    cases = [(mpf(rr), mpf(bb))
             for rr in ["0.25", "0.5", "1", "2", "7.5"]
             for bb in ["0.001", "0.01", "0.05", "1/6", "0.2"]]

    print("== (A) quadrature vs closed form,  (B) closed form vs rectDenom ==")
    worstA = mpf(0)
    worstB = mpf(0)
    for r, b in cases:
        if b >= r:
            continue
        wq, wc, rd = W_quad(r, b), W_closed(r, b), rectDenom(r, b)
        dA, dB = abs(wq - wc), abs(wc - rd)
        worstA, worstB = max(worstA, dA), max(worstB, dB)
        print("  r=%-6s b=%-8s  W=%s   |A|=%.2e  |B|=%.2e"
              % (mp.nstr(r, 4), mp.nstr(b, 4), mp.nstr(wc, 20), float(dA), float(dB)))
    print("  worst (A) residual: %.3e" % float(worstA))
    print("  worst (B) residual: %.3e" % float(worstB))

    print()
    print("== (C) derivative in b equals -2*arctan(sqrt(r^2-b^2)/b), and is negative ==")
    worstC = mpf(0)
    for r, b in cases:
        if b >= r:
            continue
        num = diff(lambda t: W_closed(r, t), b)
        claim = -2 * atan(sqrt(r ** 2 - b ** 2) / b)
        dC = abs(num - claim)
        worstC = max(worstC, dC)
        assert claim < 0, (r, b)
        print("  r=%-6s b=%-8s  dW/db=%s   |C|=%.2e"
              % (mp.nstr(r, 4), mp.nstr(b, 4), mp.nstr(claim, 20), float(dC)))
    print("  worst (C) residual: %.3e" % float(worstC))

    print()
    print("== antitonicity in b (the form actually used: b <= alpha ==> W(r,b) >= W(r,alpha)) ==")
    ok = True
    for r in [mpf("0.25"), mpf(1), mpf("7.5")]:
        prev = None
        n = 400
        for i in range(1, n):
            b = r * mpf(i) / n
            cur = W_closed(r, b)
            if prev is not None and not (cur < prev):
                ok = False
                print("  FAIL at r=%s b=%s" % (mp.nstr(r, 4), mp.nstr(b, 6)))
            prev = cur
    print("  strictly decreasing on a 400-point grid of (0,r): %s" % ("OK" if ok else "FAIL"))

    print()
    print("== endpoint sanity: W(r,b) -> 2r as b -> 0+, and -> 0 as b -> r- ==")
    for r in [mpf("0.25"), mpf(1), mpf("7.5")]:
        print("  r=%-6s W(r,1e-30)=%s  (2r=%s)   W(r,r(1-1e-20))=%.3e"
              % (mp.nstr(r, 4), mp.nstr(W_closed(r, mpf("1e-30")), 15),
                 mp.nstr(2 * r, 15), float(W_closed(r, r * (1 - mpf("1e-20"))))))


if __name__ == "__main__":
    main()
