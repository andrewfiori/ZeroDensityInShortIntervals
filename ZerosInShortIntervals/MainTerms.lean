/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodShort

/-! # The main and error terms of Theorems `\ref{thm:main-jensen}`/`\ref{thm:main-littlewood}`

The five definitions the two headline theorems of the introduction of
`ZerosInShortIntervals.tex` are stated with: the `α`-threshold `1/6`
(`alphaBoundTodo`), the main terms `U_J` (`UJensen`) and `U_L` (`ULittlewood`), and the collapsed
`O^*` errors (`EJensen`, `ELittlewood`).

**Why a separate file.** `MainTheorem.mainJensen`/`mainLittlewood` are proved from the sharper
regime forms `MainTheoremTight.mainJensenTight`/`mainLittlewoodTight` (for `t > 10^12`), which are
themselves stated in terms of `UJensen`/`ULittlewood`. The definitions therefore have to sit
upstream of both files: `MainTheoremTight` imports this file, and `MainTheorem` imports
`MainTheoremTight`. There are no namespaces here, so the informal prefix `MainTheorem.UJensen`
used elsewhere in the project's docstrings names these same declarations. -/

/-- **The threshold on `α` for the Jensen mechanism, `1/6`**, the hypothesis carried by
`Theorem \ref{thm:main-jensen}` (Theorem 2).

### Summary of Proof
A definition, `1/6`. Its significance: `1/6` is where the `t, h → ∞` asymptotic proportion of
zeros with `Re ρ ∈ [α, 1-α]` first becomes non-positive, via `LittlewoodShort.A1` at radius
`r = 1/2`, where the evaluation point `1 - r = 1/2` is exactly `σ_0`, so the chord index of
`ULittlewood` is pinned at `k = 0`. Certified exactly (no floating point) in
`Code/verify_alpha_max_sixth.sage`.

### Lean Notes
Despite the name this is **not** a placeholder: `1/6` is exactly the threshold the tex states, for
`Theorem \ref{thm:main-littlewood}` (Theorem 3) as well as for Theorem 2. The regime forms in
`MainTheoremTight` carry weaker hypotheses on `α`, so of the headline results only `mainJensen`
consumes this definition.

### References
tex: the hypothesis `α < 1/6` of `\ref{thm:main-jensen}` (Theorem 2) and
`\ref{thm:main-littlewood}` (Theorem 3).

### Dependencies
**Depends on:** none.
**Used by:** `MainTheorem.mainJensen`, `AllHypotheses.mainJensen'`,
`HalvingConvention.mainJensenHalf`, `MainCorollary.mainPositiveProportionCorollary_jensen`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`. -/
noncomputable def alphaBoundTodo : ℝ := 1 / 6

/-- **`U_J(α,r,h,t)`, the Jensen-mechanism main term of `\ref{thm:main-jensen}` (Theorem 2):**
`(2h + 2α̂_r)(B₁/π·log t + B₂·log log t + B₃) + B₄`.

### Summary of Proof
A definition, transcribed verbatim from the `U_J` display inside Theorem 2, with
`α̂_r = hatAlpha r α` and `B₁,…,B₄` exactly the `B_{i,α,r}` of
`Theorem \ref{thm:rectangularjensen}` (Theorem 24), i.e. `RectangularBounds.B1`–`B4`.

### Lean Notes
The `O^*` error is kept **outside** this definition, matching the tex, which writes the bound as
`U_J(α,r,h,t) + O^*(…)`. That separation is what lets `EJensen` and
`MainTheoremTight.mainJensenTight` supply two different error terms against the same main term.

### References
tex: `\ref{thm:main-jensen}` (Theorem 2), the `U_J` display; the `B_{i,α,r}` are from
`\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `hatAlpha`, `B1`, `B2`, `B3`, `B4`.
**Used by:** `mainJensen`, `MainCorollary.Ubound_jensen`,
`MainTheoremTight.mainJensenTight`. -/
noncomputable def UJensen (α r h t : ℝ) : ℝ :=
  (2 * h + 2 * hatAlpha r α) *
      (B1 α r / Real.pi * Real.log t + B2 α r * Real.log (Real.log t) + B3 α r)
    + B4 α r

/-- **`U_L(α,r,h,t)`, the Littlewood-mechanism main term of `\ref{thm:main-littlewood}`
(Theorem 3):** `(2A₁h + 2A₄)/π·log t + (2A₂h + 2A₅)·log log t + 2A₃h + A₆`.

### Summary of Proof
A definition, transcribed from the `U_L` display inside Theorem 3, with `A₁,…,A₆` exactly the
`A_{i,α,r}` of `Theorem \ref{thm:littlewoodshort}` (Theorem 32), i.e. `LittlewoodShort.A1`–`A6`.

### Lean Notes
As with `UJensen`, the `O^*` error is kept outside. The index `k` is an explicit argument here
because `A1`, `A2`, `A3` depend on the chord index pinned by `σ_k ≤ 1-r < σ_{k+1}`; the tex
leaves that dependence implicit in its `A_{i,α,r}` notation.

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3), the `U_L` display; the `A_{i,α,r}` are from
`\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** `A1`, `A2`, `A3`, `A4`, `A5`, `A6`.
**Used by:** `MainTheorem.ULittlewood_add_ELittlewood_pos`, `HalvingConvention.ULittlewood_avg`,
`MainCorollary.Ubound_littlewood`, `MainCorollary.Ubound_littlewood_eq_num_mul`,
`MainTheorem.mainLittlewood`, `AllHypotheses.mainLittlewood'`,
`HalvingConvention.mainLittlewoodHalf`, `MainTheoremTight.mainLittlewoodTight`. -/
noncomputable def ULittlewood (α r h t : ℝ) (k : ℤ) : ℝ :=
  (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log t
    + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log t)
    + 2 * A3 α r k * h + A6 α r

/-- **The Jensen-mechanism `O^*` error of `\ref{thm:main-jensen}` (Theorem 2):**
`3.35 / (D_{r,α}·t^{1/3})`, with `D_{r,α} = rectDenom r α`.

### Summary of Proof
A definition, the fully collapsed single-term form printed in Theorem 2. It comes from the
three-term `t > 10^12`, `h < t^{2/3}` simplification stated inside
`Theorem \ref{thm:rectangularjensen}` (Theorem 24),
`(1/D_{r,α})(3.34/t^{1/3} + 4.01/t^{4/3} + 291/(t^{4/3}log t))`, by absorbing the two `t^{-4/3}`
terms into the leading constant (`3.34 → 3.35`).

### Lean Notes
The sharper three-term form is stated separately as `MainTheoremTight.mainJensenTight`. Note the
decay is only `t^{-1/3}`, not `t^{-1}`: every term of Theorem 24's error carries a factor
`(h + α̂_r)` in its numerator, and `h` may be as large as `t^{2/3}`.

### References
tex: `\ref{thm:main-jensen}` (Theorem 2); collapsed from the `t > 10^12`, `h < t^{2/3}`
simplification stated inside `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `rectDenom`.
**Used by:** `MainTheorem.UJensen_add_EJensen_pos`, `MainCorollary.Ubound_jensen`,
`MainCorollary.Ubound_jensen_div_Lbound_le_C2Jensen`, `MainCorollary.Ubound_jensen_eq_num_mul`,
`MainTheorem.mainJensen`, `AllHypotheses.mainJensen'`, `HalvingConvention.mainJensenHalf`. -/
noncomputable def EJensen (α r t : ℝ) : ℝ :=
  3.35 / (rectDenom r α * t ^ ((1 : ℝ) / 3))

/-- **The Littlewood-mechanism `O^*` error of `\ref{thm:main-littlewood}` (Theorem 3):**
`(1/(t(r-α)))·(0.335 + 0.51/log t)`.

### Summary of Proof
A definition, the two-term collapsed form printed in Theorem 3, obtained from the six-term
`t > 10^12`, `h < t^{2/3}` simplification stated inside `Theorem \ref{thm:littlewoodshort}`
(Theorem 32), namely `(1/(t(r-α)))` times
`(0.334 + 0.502/log t + 1.001/t + 72.48/(t log t) + 0.64/t^{1/3} + 46.3/(t^{1/3}log t))`,
by absorbing the four smaller terms using `t ≥ 10^12`.

### Lean Notes
The sharper six-term form is stated separately as `MainTheoremTight.mainLittlewoodTight`. Unlike
the Jensen error this genuinely decays like `t^{-1}`, because Theorem 32's arc-integral error
term carries no factor of `h`.

The six-term form is the one printed inside Theorem 32; the two-term collapse transcribed here is
printed in Theorem 3, and appears in Theorem 32's own statement only as a commented-out
alternative. The two are consistent — the two-term form majorises the six-term one for
`t ≥ 10^12`.

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3); collapsed from the `t > 10^12`, `h < t^{2/3}`
simplification stated inside `\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** none.
**Used by:** `MainTheorem.ULittlewood_add_ELittlewood_pos`, `MainCorollary.Ubound_littlewood`,
`MainCorollary.Ubound_littlewood_eq_num_mul`, `MainTheorem.mainLittlewood`,
`AllHypotheses.mainLittlewood'`, `HalvingConvention.mainLittlewoodHalf`. -/
noncomputable def ELittlewood (α r t : ℝ) : ℝ :=
  (1 / (t * (r - α))) * (0.335 + 0.51 / Real.log t)
