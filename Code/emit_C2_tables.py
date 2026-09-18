#!/usr/bin/env python3
"""
Re-emit Tables 8-11 (the C_2 tables) with the presentation rules requested by
the author, WITHOUT recomputing.  `compute_C2_tables.sage` takes ~80 minutes;
layout changes should not cost that.

DATA SOURCE
    Code/C2_tables_data.json                 if present (preferred), else
    Code/C2_tables_raw.tex                   parsed directly.
The raw .tex is a complete record: rows with C_2 >= 1/2 are suppressed as
comments rather than discarded, so every computed row is recoverable from it.
The output is Code/C2_tables.tex, which the paper `\input`s.

PRESENTATION RULES
  1. Drop every h_0 = 1000 row, in all four tables.
  2. Per alpha, keep only two h_0 values: the SMALLEST h_0 that achieves
     C_2 < 1/2, and h_0 = 100.  (If those coincide, one column of rows.)
     C_2 is decreasing in h_0, so the smallest successful h_0 is the threshold
     and h_0 = 100 shows the comfortable case.
  3. Thin the t_0 grid to the informative values (see KEEP_T0).
  4. Tables 10-11 (the frontier tables): move `r` next to `alpha`, matching
     Tables 8-9.
  5. Tables 10-11: drop the "none with n <= 10^5" rows entirely.
  6. All four: two-panel layout, so two segments of the table sit side by side
     on one page.  Font reduced to \\footnotesize to make room.
  7. Each table is a floating `table` holding one `tabular`, not a `longtable`:
     a tabular is a single box, so no table can break across pages.  The tallest
     of the four (about 46 two-panel rows) is about 500pt at \\footnotesize,
     inside amsart's 606pt text height; `[p]` puts each on its own float page.
  8. Captions say exactly which rows appear: per alpha, h_0 = 100 and -- only
     when it is smaller -- the smallest h_0 in {1,2,5,10} that succeeds; so an
     alpha may have one or two h_0 blocks, not always two.

Writes Code/C2_tables.tex.
"""

import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
TEX = os.path.join(HERE, "C2_tables.tex")          # output, \input by the paper
RAW = os.path.join(HERE, "C2_tables_raw.tex")      # input: the COMPLETE record
JSON_CACHE = os.path.join(HERE, "C2_tables_data.json")

# NOTE: input and output are deliberately different files. This script both reads
# computed rows and writes a reduced view of them; if it read its own output, a
# second run would parse the already-thinned table and silently discard rows.
# `C2_tables_raw.tex` keeps every computed row and must not be edited by hand.

# t_0 values kept.  The floor 3*10^12 is the smallest admissible value; 10^13
# shows the immediate neighbourhood; the rest give a geometric spread out to the
# asymptotic regime.  10^40, 10^200 and 10^500 are dropped as visually redundant
# with their neighbours.
KEEP_T0 = [
    r"3\cdot10^{12}", "10^{13}", "10^{20}", "10^{30}",
    "10^{50}", "10^{100}", "10^{1000}", "10^{10000}",
]
T0_ORDER = {s: i for i, s in enumerate(KEEP_T0)}

DROP_H0 = {1000}
ALWAYS_H0 = 100


def _strip_math(s):
    s = s.strip()
    if s.startswith("$") and s.endswith("$"):
        s = s[1:-1]
    return s


def _h0_to_int(s):
    """`$100$` -> 100, `$10^{2}$` -> 100."""
    s = _strip_math(s)
    m = re.fullmatch(r"10\^\{(\d+)\}", s)
    if m:
        return 10 ** int(m.group(1))
    return int(s)


def _alpha_den(s):
    """`$1/7$` -> 7."""
    return int(_strip_math(s).split("/")[1])


def parse_tex(path):
    """Recover every computed row from the generated .tex."""
    with open(path, encoding="utf-8") as fh:
        text = fh.read()

    values = {"J": [], "L": []}
    frontier = {"J": [], "L": []}

    blocks = text.split("\\begin{longtable}")
    for blk in blocks[1:]:
        mlab = re.search(r"\\label\{tab:C2(J|L)(frontier)?\}", blk)
        if not mlab:
            continue
        mech, is_front = mlab.group(1), bool(mlab.group(2))
        for line in blk.splitlines():
            raw = line.strip()
            suppressed = False
            if raw.startswith("% [C_2 >= 1/2, suppressed]"):
                raw = raw[len("% [C_2 >= 1/2, suppressed]"):].strip()
                suppressed = True
            if not raw.startswith("$1/") or not raw.endswith("\\\\"):
                continue
            body = raw[:-2]
            cells = body.split("&")
            if is_front:
                if len(cells) != 5 or "multicolumn" in body:
                    continue           # rule 5: the "none" rows are dropped
                a, h0, n, r, c2 = cells
                frontier[mech].append({
                    "alpha_den": _alpha_den(a), "h0": _h0_to_int(h0),
                    "n": _strip_math(n), "r": _strip_math(r),
                    "c2": _strip_math(c2),
                })
            else:
                if len(cells) != 5:
                    continue
                a, r, h0, t0, c2 = cells
                values[mech].append({
                    "alpha_den": _alpha_den(a), "r": _strip_math(r),
                    "h0": _h0_to_int(h0), "t0": _strip_math(t0),
                    "c2": _strip_math(c2), "ok": not suppressed,
                })
    return values, frontier


def load_data():
    if os.path.exists(JSON_CACHE):
        with open(JSON_CACHE, encoding="utf-8") as fh:
            d = json.load(fh)
        return d["values"], d["frontier"]
    if not os.path.exists(RAW):
        raise SystemExit(
            f"No data source. Expected {JSON_CACHE} or {RAW}.\n"
            "The raw file is the complete computed record; recreate it by "
            "re-running compute_C2_tables.sage (~80 min).")
    return parse_tex(RAW)


def chosen_h0(rows, ok_key):
    """Per alpha: {smallest h_0 meeting `ok_key`} union {100}, minus DROP_H0."""
    out = {}
    alphas = sorted({r["alpha_den"] for r in rows})
    for a in alphas:
        mine = [r for r in rows if r["alpha_den"] == a and r["h0"] not in DROP_H0]
        good = sorted({r["h0"] for r in mine if ok_key(r)})
        keep = {ALWAYS_H0}
        if good:
            keep.add(good[0])
        out[a] = keep
    return out


def two_panel(rows, ncell, colspec, header, caption, label):
    """Emit a floating `table` (one `tabular`, so it cannot break across pages)
    whose rows are laid out in two side-by-side panels."""
    n = len(rows)
    half = (n + 1) // 2
    left, right = rows[:half], rows[half:]
    blank = "&".join([""] * ncell)

    hdr2 = header + "&" + header + "\\\\"
    out = []
    out.append("")
    out.append("\\begin{table}[p]")
    out.append("\\centering\\footnotesize")
    out.append("\\setlength{\\tabcolsep}{3pt}")
    out.append(f"\\caption{{{caption}}}\\label{{{label}}}")
    out.append("\\begin{tabular}{" + colspec + "}")
    out.append("\\hline")
    out.append(hdr2)
    out.append("\\hline")
    for i in range(half):
        l = left[i]
        r = right[i] if i < len(right) else None
        out.append(l + "&" + (r if r is not None else blank) + "\\\\")
    out.append("\\hline")
    out.append("\\end{tabular}")
    out.append("\\end{table}")
    return out


def main():
    values, frontier = load_data()
    out = ["% Generated by Code/emit_C2_tables.py -- do not edit by hand.",
           "% Layout only; the numbers come from compute_C2_tables.sage.",
           "% Presentation rules are documented at the top of emit_C2_tables.py."]

    # ------------------------------------------- Tables 8, 9 (tab:C2J, tab:C2L)
    for mech in ["J", "L"]:
        rows = values[mech]
        keep = chosen_h0(rows, lambda r: r["ok"])
        sel = [r for r in rows
               if r["h0"] in keep[r["alpha_den"]]
               and r["t0"] in T0_ORDER
               and r["ok"]]
        sel.sort(key=lambda r: (r["alpha_den"], r["h0"], T0_ORDER[r["t0"]]))
        cells = [f"$1/{r['alpha_den']}$&${r['r']}$&${r['h0']}$&${r['t0']}$&${r['c2']}$"
                 for r in sel]
        corol = "cor:main-jensen" if mech == "J" else "cor:main-littlewood"
        cap = (f"Values of $C_2^{mech}(\\alpha,r,h_0,t_0)$ for Corollary "
               f"\\ref{{{corol}}}, with $r$ chosen to minimise $C_2^{mech}$, at selected "
               f"$t_0$; only entries with $C_2^{mech}<1/2$ are shown. For each $\\alpha$ the "
               f"rows are for $h_0=100$ and, when a smaller value succeeds, for the smallest "
               f"$h_0\\in\\{{1,2,5,10\\}}$ with $C_2^{mech}<1/2$ at some tabulated $t_0$.")
        out += two_panel(
            cells, 5, "|cc|cc|c||cc|cc|c|",
            f"$\\alpha$&$r$&$h_0$&$t_0$&$C_2^{mech}$", cap, f"tab:C2{mech}")

    # --------------- Tables 10, 11 (tab:C2Jfrontier, tab:C2Lfrontier)
    for mech in ["J", "L"]:
        rows = frontier[mech]
        keep = chosen_h0(rows, lambda r: True)   # every surviving row has C_2 < 1/2
        sel = [r for r in rows if r["h0"] in keep[r["alpha_den"]]]
        sel.sort(key=lambda r: (r["alpha_den"], r["h0"]))
        # rule 4: r moved next to alpha
        cells = [f"$1/{r['alpha_den']}$&${r['r']}$&${r['h0']}$&${r['n']}$&${r['c2']}$"
                 for r in sel]
        cap = (f"Smallest $n$ with $C_2^{mech}(\\alpha,r,h_0,10^n)<1/2$, with $r$ chosen to "
               f"minimise $C_2^{mech}$. The last column is the resulting proportion "
               f"$1-2C_2^{mech}$ of zeros with real part in $[\\alpha,1-\\alpha]$, rounded down; "
               f"since $C_2^{mech}$ is decreasing in $t_0$, it is a lower bound for every "
               f"$t_0\\geq 10^n$. For each $\\alpha$ the rows are for $h_0=100$ and, when it "
               f"exists, for the smallest $h_0\\in\\{{1,2,5,10\\}}$ with such an $n\\leq 10^5$.")
        out += two_panel(
            cells, 5, "|cc|c|cc||cc|c|cc|",
            f"$\\alpha$&$r$&$h_0$&$n$&$1-2C_2^{mech}$", cap, f"tab:C2{mech}frontier")

    with open(TEX, "w", encoding="utf-8") as fh:
        fh.write("\n".join(out) + "\n")

    print(f"wrote {TEX}")
    for mech in ["J", "L"]:
        tot = len(values[mech])
        print(f"  table C2{mech}:         {tot} computed rows -> "
              f"{sum(1 for r in values[mech] if r['ok'])} passing, "
              f"{len([1 for r in values[mech] if r['ok'] and r['t0'] in T0_ORDER])} after t_0 thinning")
    for mech in ["J", "L"]:
        print(f"  table C2{mech}frontier: {len(frontier[mech])} rows with a finite n")


if __name__ == "__main__":
    main()
