/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodShort
import ZerosInShortIntervals.MainTheorem

/-! # `L`, `h₀`, `C₂`: the Jensen/Littlewood corollary machinery

This file formalizes Corollaries `\ref{cor:main-jensen}` (**Corollary 4**, tex lines 207–225) and
`\ref{cor:main-littlewood}` (**Corollary 5**, tex lines 227–241) of
`ZerosInShortIntervals.tex`, together with the `L(h,t)` lower bound (tex line 203) and
the `h₀` admissibility threshold (tex lines 209, 229) they rest on.

**`C₂` is the tex's own quantity.** `C2Jensen`/`C2Littlewood` are the tex's `C_2^J`/`C_2^L`, i.e.
the *ratio bound itself*,
`Nrect(t-h,t+h,α)/(N(t+h) - N(t-h)) < C_2^{J or L}(α,r,h₀,t₀)`,
and the corollaries below are stated in the tex's `<` direction. The interesting regime is
therefore `C₂ < 1/2`, which is what makes Corollary 1's proportion `1 - 2C₂` positive.

**Where the `π`'s come from.** Normalising the ratio `U/L` by `(h·log t)/π` leaves the
`B_{1,α,r}` (resp. `A_{1,α,r}`) term `π`-free but multiplies *every* other term, in both
numerator and denominator, by `π`. Likewise the `h²` term of `L(h,t)`, divided by `(h log t)/π`,
is at most `(1-log 2)/(t^{2/3} log t)` using `h ≤ t^{2/3}`; and `h₀`'s threshold — which is
exactly the condition making the denominator positive — carries the same `π`. Lean and tex agree
term for term.

**Scope.** `Ubound_jensen`/`Ubound_littlewood` are the *full* upper bounds on `Nrect`, i.e.
`MainTerms.UJensen + EJensen` and `ULittlewood + ELittlewood`, so that `C₂ = Ubound/Lbound` after
normalization; the underlying `U` and error pieces live in `MainTerms`, where the tex states them.

**Monotonicity infrastructure.** Two sections below — "Generic monotonicity infrastructure" and
the two "…numerator in affine form" sections — carry the machinery for Corollaries 4 and 5's
"decreasing in both `h₀` and `t₀`" claim. The key rearrangement is
`C₂(α,r,h,t) = (P(t)·h + Q(t))/(S(t)·h - W(t))` (`C2Jensen_eq_affine`,
`C2Littlewood_eq_affine`), after which the `h`-half is `affine_div_affine_antitoneOn` and the
`t`-half is `div_antitoneOn_of_antitoneOn_of_monotoneOn` over `P`, `Q` antitone and `S·h - W`
monotone; the `loglog t/log t` monotonicity inside `P` and `Q` is
`log_affine_div_self_antitoneOn`.

**That decomposition also settles the sign of the headline constant.**
`ZerosInShortIntervals/PositiveProportion.lean` uses `C2Littlewood_eq_affine` to show
`C₂ᴸ → 2A₁` as `h, t → ∞`, and hence that `1 - 2C₂ᴸ` of Corollary `\ref{cor:simpmain}`
(Corollary 1) is **positive** for every `α ∈ (0, 1/6)`, with the radius `r = 1/2` supplied rather
than assumed. The `C₂` tables of the tex's Section 4 give the numerical *values* of the constant,
not its sign.

**The sign facts about the paper's constants** that this machinery consumes — `B1_nonneg`–
`B4_nonneg`, `A1_nonneg`, `A2_eq`/`A2_nonneg`, `A4_nonneg`–`A6_nonneg`, their ingredients
`c3_nonneg`, `c4_nonneg`, `two_Phi_one_add_c5_nonneg`, and `neg_A2_le_A3` (which replaces the
*false* `0 ≤ A₃`, via the `v''` lower bound `log_point_six_one_one_le_vCoeffPP` and its chord
form) — live in `ZerosInShortIntervals.ConstantSigns`, because
`MainTheorem.mainJensen`/`mainLittlewood` need them as well (for `t ≤ 10^12` the count is zero and
those theorems reduce to the positivity of `U + O^*`). This file sees them through its import of
`MainTheorem`. All are proved; the numerical backing for the `c₃` and chord signs is
`Code/verify_c3_tangent_route.py` and `Code/verify_c3_and_chord_signs.py`. -/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **The lower bound `L(h,t)` on `N(t+h) - N(t-h)`**, stated just above
`Corollary \ref{cor:main-jensen}` (Corollary 4):
`L(h,t) := (log(t/2π)/π - (1-log 2)h²/(πt²))·h - 0.194·log t - 9.908`.

### Summary of Proof
A definition. Its derivation in the tex: with `M(t) := (t/2π)·log(t/2πe)`, `M'(t) =
log(t/2π)/(2π)`, so `M(t+h) - M(t-h) = (h/π)log(t/2π) + (t/2π)∫₀^λ log(1-v²)dv` with `λ = h/t`,
and the subtracted `(1-log 2)h³/(πt²)` is a valid — indeed sharp — allowance for that integral
(see the Lean Notes). The additive tail `-0.194 log t - 9.908` comes from
`|N(t) - M(t)| < 0.097 log t + 4.954` (`\cite[Cor.~1.3]{BellottiWong2026}`) applied at both `t+h`
and `t-h`, using `log(t+h) + log(t-h) = log(t² - h²) < 2 log t`.

### Lean Notes
Shared between both mechanisms — it bounds the *total* zero count in the window and is unrelated
to which mechanism bounds `Nrect`. Carrying the true `h`-cubic term rather than a worst-cased
constant is what makes `C₂`'s denominator carry a `t^{2/3}`-decaying term rather than an `h`-free
one.

**The coefficient is `(1-log2)/π`, and it is sharp.** A subtracted `C·h·λ²` (`λ = h/t`) is
admissible exactly when `∫₀^λ -log(1-v²)dv ≤ 2πC·λ³`, from the identity
`M(t+h)-M(t-h) = (h/π)log(t/2π) + (t/2π)∫₀^λ log(1-v²)dv`. Since
`(∫₀^λ -log(1-v²))/λ³` is monotone increasing with limit `2-2log2`, the sharp constant is
`(2-2log2)/(2π) = (1-log2)/π = 0.0976742860`.
The closed form is `Common.RealLogBounds.integral_log_one_sub_sq`.

**Two things that trip people here.** First, the sharp constant makes the estimate valid on all of
`0 < λ < 1`, so this term needs no `h` restriction — but `L` still does, at the *left* endpoint:
Bellotti–Wong is applied at `t ± h` and needs `t - h ≥ 1`, which is why the tex splits at
`h = t^{2/3}` and supplies a separate `L̃` above it (tex line 205). Second, the `π` bookkeeping:
this coefficient is `(1-log2)/π` *here*, but `C₂`'s denominator is `L·π/(h log t)`, so the `π`
cancels and the term appears there as `(1-log2)/(t^{2/3} log t)` — not
`(1-log2)/(π t^{2/3} log t)`.

### References
tex: the `L(h,t)` display immediately preceding `\ref{cor:main-jensen}` (Corollary 4), tex line
203. External: Bellotti–Wong, `\cite[Cor.~1.3]{BellottiWong2026}`.

### Dependencies
**Depends on:** none.
**Used by:** `Lbound_le_N_sub_N`, `C2denom_mul_le_Lbound`,
`Ubound_jensen_div_Lbound_le_C2Jensen`, `Ubound_littlewood_div_Lbound_le_C2Littlewood`, both
corollaries below, and `HalvingConvention.continuous_Lbound_h`/`Lbound_le_Nhalf_one`. -/
noncomputable def Lbound (h t : ℝ) : ℝ :=
  (Real.log (t / (2 * Real.pi)) / Real.pi
      - (1 - Real.log 2) * h ^ 2 / (Real.pi * t ^ 2)) * h
    - (0.194 : ℝ) * Real.log t - 9.908

/-- **`L(h,t)` really does bound the zero count below:** `L(h,t) ≤ N(t+h) - N(t-h)`.

### Summary of Proof
Immediate from `ExternalFacts.bellotti_wong_Lbound_le`, which is this statement with `Lbound`
unfolded; that is a theorem derived from the cited Bellotti–Wong Corollary 1.3 (the
`LiteratureInputs` field `bellotti_wong_cor_1_3`) via the power-series inequality
`Common.RealLogBounds.two_mul_sub_bwPhi_le`.

### Lean Notes
The `ExternalFacts` statement is written with the formula spelled out because `Lbound` is defined
in this file, which is downstream of `ExternalFacts`. This is the version to cite.

This is what connects `Lbound` to `N`, and so the step both corollaries need to pass from
Theorem 2 / Theorem 3's bound on `Nrect` to a bound on the *ratio*.

### References
tex: the `L(h,t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex lines 200–205.
External: Bellotti–Wong, `\cite[Cor. 1.3]{BellottiWong2026}`.

### Dependencies
**Depends on:** `Lbound`, `N`, `ExternalFacts.bellotti_wong_Lbound_le`.
**Used by:** `mainPositiveProportionCorollary_jensen`,
`mainPositiveProportionCorollary_littlewood`, `HalvingConvention.Lbound_le_Nhalf_one`. -/
theorem Lbound_le_N_sub_N {h t : ℝ} (hh : 0 < h) (ht : 1 ≤ t - h) :
    Lbound h t ≤ ((N (t + h) : ℝ) - (N (t - h) : ℝ)) :=
  bellotti_wong_Lbound_le hh ht

/-- **The full Jensen-mechanism upper bound on `Nrect (t-h) (t+h) α`**, i.e. the entire
right-hand side of `Theorem \ref{thm:main-jensen}` (Theorem 2):
`U_J(α,r,h,t) + O^*(3.35/(D_{r,α} t^{1/3}))`.

### Summary of Proof
A definition, `UJensen + EJensen`. Bundling main term and error together is what makes
`C₂ = Ubound/Lbound` after normalisation.

### References
tex: the right-hand side of `\ref{thm:main-jensen}` (Theorem 2), tex line 159.

### Dependencies
**Depends on:** `UJensen`, `EJensen`.
**Used by:** `Ubound_jensen_eq_num_mul`, `Ubound_jensen_div_Lbound_le_C2Jensen`,
`mainPositiveProportionCorollary_jensen`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`. -/
noncomputable def Ubound_jensen (α r h t : ℝ) : ℝ :=
  UJensen α r h t + EJensen α r t

/-- **The full Littlewood-mechanism upper bound on `Nrect (t-h) (t+h) α`**, i.e. the entire
right-hand side of `Theorem \ref{thm:main-littlewood}` (Theorem 3):
`U_L(α,r,h,t) + O^*((1/(t(r-α)))(0.335 + 0.51/log t))`.

### Summary of Proof
A definition, `ULittlewood + ELittlewood`.

### Lean Notes
The error term carries the factor `1/(r-α)` inside `ELittlewood`: every term that
`\ref{eq:simplelittlewoodzerodensity}` (Equation 14) bounds `Nrect` by sits inside a bracket
divided by `r-α` as a whole, and `r-α` has no lower bound.

### References
tex: the right-hand side of `\ref{thm:main-littlewood}` (Theorem 3), tex line 185.

### Dependencies
**Depends on:** `ULittlewood`, `ELittlewood`.
**Used by:** `Ubound_littlewood_eq_num_mul`, `Ubound_littlewood_div_Lbound_le_C2Littlewood`,
`mainPositiveProportionCorollary_littlewood`,
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`. -/
noncomputable def Ubound_littlewood (α r h t : ℝ) (k : ℤ) : ℝ :=
  ULittlewood α r h t k + ELittlewood α r t

/-- **The common denominator of `C_2^J` and `C_2^L`**, after normalising `U/L` by `(h·log t)/π`:
`1 - log(2π)/log t - (1-log 2)/(t^{2/3} log t) - 0.194π/h - 9.908π/(h log t)`.

### Summary of Proof
A definition. It is `L(h,t)` divided by `(h log t)/π`, with the single weakening
`(1-log 2)h²/(πt²) ≤ (1-log 2)/(πt^{2/3})` (valid for `h ≤ t^{2/3}`) applied to make the result
`h`-free in that term.

### Lean Notes
Its positivity is exactly what `h > h0Threshold t₀` guarantees — see `h0Threshold`, which is
obtained by solving `C2denom > 0` for `h`.

### References
tex: the shared denominator of the `C_2^J` display in `\ref{cor:main-jensen}` (Corollary 4, tex
line 214) and the `C_2^L` display in `\ref{cor:main-littlewood}` (Corollary 5, tex line 234).

### Dependencies
**Depends on:** none.
**Used by:** `C2Jensen`, `C2Littlewood`, `C2denom_mul_eq_affine`, `C2denom_mul_le_Lbound`,
`C2denom_pos_of_h0Threshold_lt`, `Ubound_jensen_div_Lbound_le_C2Jensen`,
`Ubound_littlewood_div_Lbound_le_C2Littlewood`. -/
noncomputable def C2denom (h t : ℝ) : ℝ :=
  1 - Real.log (2 * Real.pi) / Real.log t
    - (1 - Real.log 2) / (t ^ ((2 : ℝ) / 3) * Real.log t)
    - 0.194 * Real.pi / h
    - 9.908 * Real.pi / (h * Real.log t)

/-- **`C_2^J(α,r,h,t)` from `Corollary \ref{cor:main-jensen}` (Corollary 4):**
`[(2 + 2α̂_r/h)(B₁ + πB₂·loglog t/log t + πB₃/log t) + πB₄/(h log t)
  + 3.35π/(D_{r,α}·h·t^{1/3}·log t)] / C2denom h t`.

### Summary of Proof
A definition: the normalised ratio `U_J/L`, obtained by dividing numerator and denominator of
`Ubound_jensen / Lbound` by `(h·log t)/π`. That normalisation leaves the `B_{1,α,r}` term `π`-free
but multiplies every other term, in both numerator and denominator, by `π`.

### Lean Notes
Numerator and denominator match the tex's display at tex lines 213–215 term for term, `π`'s
included. The `π`'s are what the `(h·log t)/π` normalisation puts there: only the `B_{1,α,r}`
term escapes one.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the `C_2^J` display at tex lines 213–215. The
`B_{i,α,r}` are from `\ref{thm:rectangularjensen}` (Theorem 24).

**Independent numeric check.**
`Code/indep_mpmath_tables_spotcheck.py` recomputes this expression from scratch with mpmath
(no arb, none of the Sage table machinery) at `α = 1/16`, `r = 0.5264389`, `h₀ = 100`,
`t₀ = 10¹⁰⁰` and reproduces the `C₂ᴶ = 0.4579894` row of `Code/C2_tables_raw.tex` to all 7
printed digits.

### Dependencies
**Depends on:** `B1`, `B2`, `B3`, `B4`, `hatAlpha`, `rectDenom`, `C2denom`.
**Used by:** `C2Jensen_eq_affine`, `C2Jensen_antitone_h`, `C2Jensen_antitone_t`,
`C2Jensen_antitone`, `Ubound_jensen_div_Lbound_le_C2Jensen`,
`mainPositiveProportionCorollary_jensen`, `HalvingConvention.CsimpJensen`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`. -/
noncomputable def C2Jensen (α r h t : ℝ) : ℝ :=
  ((2 + 2 * hatAlpha r α / h) *
        (B1 α r + Real.pi * B2 α r * Real.log (Real.log t) / Real.log t
          + Real.pi * B3 α r / Real.log t)
      + Real.pi * B4 α r / (h * Real.log t)
      + 3.35 * Real.pi / (rectDenom r α * h * t ^ ((1 : ℝ) / 3) * Real.log t))
    / C2denom h t

/-- **`C_2^L(α,r,h,t)` from `Corollary \ref{cor:main-littlewood}` (Corollary 5):**
`[2A₁ + 2A₄/h + π(2A₂ + 2A₅/h)·loglog t/log t + 2πA₃/log t + πA₆/(h log t)
  + π/((r-α)·h·t·log t)·(0.335 + 0.51/log t)] / C2denom h t`.

### Summary of Proof
A definition: the normalised ratio `U_L/L`, by the same division by `(h·log t)/π` as `C2Jensen`.
The `A_{1,α,r}` term is left `π`-free; every other term acquires a `π`.

### Lean Notes
Matches the tex's display at tex lines 233–235 term for term. As with `C2Jensen` the `π`'s are
what the `(h·log t)/π` normalisation puts there; here only the `A_{1,α,r}` term escapes one.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the `C_2^L` display at tex lines 233–235. The
`A_{i,α,r}` are from `\ref{thm:littlewoodshort}` (Theorem 32).

**Independent numeric check.**
`Code/indep_mpmath_tables_spotcheck.py` recomputes this expression from scratch with mpmath at
`α = 1/7`, `r = 0.5000553` (chord `k = -1`), `h₀ = 100`, `t₀ = 10²⁰⁰` and reproduces the
`C₂ᴸ = 0.4981758` row of `Code/C2_tables_raw.tex` to all 7 printed digits.

### Dependencies
**Depends on:** `A1`, `A2`, `A3`, `A4`, `A5`, `A6`, `C2denom`.
**Used by:** `C2Littlewood_eq_affine`, `C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`,
`C2Littlewood_antitone`, `Ubound_littlewood_div_Lbound_le_C2Littlewood`,
`mainPositiveProportionCorollary_littlewood`, `HalvingConvention.CsimpLittlewood`,
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`,
`PositiveProportion.tendsto_C2Littlewood_h`, `PositiveProportion.exists_C2Littlewood_lt_half`. -/
noncomputable def C2Littlewood (α r h t : ℝ) (k : ℤ) : ℝ :=
  (2 * A1 α r k + 2 * A4 α r / h
      + Real.pi * (2 * A2 α r k + 2 * A5 α r / h) * Real.log (Real.log t) / Real.log t
      + 2 * Real.pi * A3 α r k / Real.log t
      + Real.pi * A6 α r / (h * Real.log t)
      + Real.pi / ((r - α) * h * t * Real.log t) * (0.335 + 0.51 / Real.log t))
    / C2denom h t

/-- **The admissibility threshold on `h₀` shared by both corollaries:**
`h₀ > (97π/500)·(1 + 4954/(97 log t₀)) / (1 - (1-log 2)/(t₀^{2/3} log t₀) - log(2π)/log t₀)`.

### Summary of Proof
A definition. It is *exactly* the condition making `C2denom h₀ t₀ > 0`, obtained by clearing `h₀`
from that expression and solving — which is what the corollaries' proofs need in order to divide
by the denominator. The tex states only that "the lower bound on `h₀` precisely ensures this
condition is met".

### Lean Notes
Numerically small — about `1.86` at `t₀ = 10^12`, decreasing in `t₀` — so not a restrictive
hypothesis in practice, but it must be checked rather than assumed.

### References
tex: the `h_0` display in both `\ref{cor:main-jensen}` (Corollary 4, tex line 209) and
`\ref{cor:main-littlewood}` (Corollary 5, tex line 229); the two are identical.

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [I]: `C2denom (h0Threshold t₀) t₀ = 0` to `10⁻⁴¹` at
`t₀ = 10¹², 3·10¹², 10²⁰, 10¹⁰⁰` (values `1.8597, 1.8086, 1.3388, 0.7506`), and
`Lbound h t ≥ (h log t/π)·C2denom h t` for `h ≤ t^{2/3}` with equality at `h = t^{2/3}`.

### Dependencies
**Depends on:** none.
**Used by:** `h0Threshold_eq_div`, `h0Threshold_pos`, `h0Threshold_antitone`,
`C2denom_pos_of_h0Threshold_lt`, the four `C2Jensen`/`C2Littlewood` antitonicity statements and
their conjunctions, both corollaries below and every statement of `HalvingConvention` built on
them, and the `(h₀, t₀)` existentials of `PositiveProportion`. -/
noncomputable def h0Threshold (t0 : ℝ) : ℝ :=
  (97 * Real.pi / 500) * ((1 + 4954 / (97 * Real.log t0)) /
    (1 - (1 - Real.log 2) / (t0 ^ ((2 : ℝ) / 3) * Real.log t0)
      - Real.log (2 * Real.pi) / Real.log t0))

/-! ### `C2denom` as an affine function of `h`: the `S`/`W` split

`C2denom h t` is affine in `1/h`, so `C2denom h t · h = S(t)·h - W(t)` where `S` collects the
`h`-free part of the bracket and `W` the `1/h`-coefficient. Both `C₂`'s antitonicity halves run
through this split: the `h`-half because `affine_div_affine_antitoneOn` wants exactly that shape,
the `t`-half because `S·h - W` is visibly monotone in `t` while `C2denom` itself is not written
in a monotone-looking way. `h0Threshold` is precisely `W/S`. -/

/-- **The `h`-free part of `C2denom`:** `S(t) = 1 - log(2π)/log t - (1-log 2)/(t^{2/3} log t)`.

### Summary of Proof
A definition, the bracket of `C2denom` with its two `1/h` terms removed.

### Lean Notes
Named so that `C2denom h t · h = S(t)·h - W(t)` (`C2denom_mul_eq_affine`) exposes the
affine-in-`h` shape both antitonicity halves need, and so that `S(t) → 1` can be stated on its
own (`PositiveProportion.tendsto_C2denomS`). Would sit naturally in `Definitions.lean` beside
`affine_div_affine_strictAntiOn` if that file ever grows a `C₂` section.

### References
tex: the shared denominator of the `C_2` displays in `\ref{cor:main-jensen}` (Corollary 4, tex
line 214) and `\ref{cor:main-littlewood}` (Corollary 5, tex line 234).

### Dependencies
**Depends on:** none.
**Used by:** `C2denom_mul_eq_affine`, `C2denomS_pos`, `C2denomS_le`, `h0Threshold_eq_div`,
`C2denomAff_monotoneOn`, `C2Jensen_eq_affine`, `C2Littlewood_eq_affine`,
`PositiveProportion.tendsto_C2denomS`,
`PositiveProportion.tendsto_C2LittlewoodP_div_C2denomS`,
`PositiveProportion.tendsto_C2Littlewood_h`. -/
noncomputable def C2denomS (t : ℝ) : ℝ :=
  1 - Real.log (2 * Real.pi) / Real.log t - (1 - Real.log 2) / (t ^ ((2 : ℝ) / 3) * Real.log t)

/-- **The `1/h`-coefficient of `C2denom`:** `W(t) = 0.194π + 9.908π/log t`.

### Summary of Proof
A definition, the two `1/h` terms of `C2denom` with the `1/h` factored out.

### Lean Notes
Strictly positive for every `t` with `log t > 0`, which is what makes the `r < 0` hypothesis of
`affine_div_affine_strictAntiOn` (here `-W < 0`) free.

### References
tex: as `C2denomS`.

### Dependencies
**Depends on:** none.
**Used by:** `C2denom_mul_eq_affine`, `C2denomW_pos`, `C2denomW_le`, `h0Threshold_eq_div`,
`C2denomAff_monotoneOn`, `C2Jensen_eq_affine`, `C2Littlewood_eq_affine`,
`PositiveProportion.tendsto_C2Littlewood_h`. -/
noncomputable def C2denomW (t : ℝ) : ℝ :=
  0.194 * Real.pi + 9.908 * Real.pi / Real.log t

/-- **`C2denom` cleared of its `1/h`'s:** `C2denom h t · h = S(t)·h - W(t)` for `h ≠ 0`.

### Summary of Proof
Multiply out. The two `1/h` terms of `C2denom` become the `h`-free `-W(t)`; everything else keeps
its factor `h`.

### Lean Notes
`log t ≠ 0` is not mathematically needed — with `log t = 0` both sides degenerate to `h - 0.194π`
via `x/0 = 0` — but `field_simp` wants it, and every call site has `log t > 20`.

### References
tex: no separate statement; this is the rearrangement the `h_0` display of
`\ref{cor:main-jensen}` (Corollary 4, tex line 209) performs implicitly.

### Dependencies
**Depends on:** `C2denom`, `C2denomS`, `C2denomW`.
**Used by:** `C2denom_pos_of_h0Threshold_lt`, `C2Jensen_eq_affine`, `C2Littlewood_eq_affine`,
`C2Jensen_antitone_h`, `C2Jensen_antitone_t`, `C2Littlewood_antitone_h`,
`C2Littlewood_antitone_t`. -/
theorem C2denom_mul_eq_affine (h t : ℝ) (hh : h ≠ 0) (hlog : Real.log t ≠ 0) :
    C2denom h t * h = C2denomS t * h - C2denomW t := by
  unfold C2denom C2denomS C2denomW
  field_simp
  ring

/-- **`log(2π) < 2.08`.**

### Summary of Proof
`2π ≤ 8` from `Real.pi_le_four`, then `log 8 = 3 log 2 < 3 · 0.6931472 = 2.0794…`.

### References
No tex counterpart — a numeric bound used to make `C2denomS` visibly positive.

### Dependencies
**Depends on:** `Real.pi_le_four`, `Real.log_two_lt_d9`.
**Used by:** `C2denomS_pos`. -/
theorem log_two_pi_lt_two_point_zero_eight : Real.log (2 * Real.pi) < 2.08 := by
  have h8 : (2:ℝ) * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hlt := Real.log_le_log (by positivity : (0:ℝ) < 2 * Real.pi) h8
  have h83 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [Real.log_two_lt_d9]

/-- **`0 < S(t)` for `t > 10^12`**, i.e. `C2denom`'s `h`-free bracket is positive.

### Summary of Proof
`twenty_lt_log` gives `log t > 20` and `t^{2/3} ≥ 1` (all that is needed; in fact `t^{2/3} > 10^8`),
so `log(2π)/log t < 2.08/20 = 0.104` and `(1-log 2)/(t^{2/3}log t) < 1/20 = 0.05`, leaving
`S ≥ 1 - 0.104 - 0.05 > 0`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the sentence justifying the `h_0` lower bound, tex
line 224.

### Dependencies
**Depends on:** `C2denomS`, `twenty_lt_log`, `log_two_pi_lt_two_point_zero_eight`.
**Used by:** `h0Threshold_pos`, `C2denom_pos_of_h0Threshold_lt`, `h0Threshold_antitone`,
`C2Jensen_antitone_h`, `C2Littlewood_antitone_h`,
`PositiveProportion.exists_C2Littlewood_lt_half`. -/
theorem C2denomS_pos {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 < C2denomS t := by
  have ht1 : (1:ℝ) < t := by nlinarith [ht]
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogpos : (0:ℝ) < Real.log t := by linarith
  have hrpow : (1:ℝ) ≤ t ^ ((2:ℝ)/3) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) ht1.le
      (by norm_num : (0:ℝ) ≤ (2:ℝ)/3)
    rwa [Real.one_rpow] at h
  have hb1 : Real.log (2 * Real.pi) / Real.log t ≤ 0.104 := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [log_two_pi_lt_two_point_zero_eight]
  -- `(1 - log 2) < 1`, and `t^{2/3} log t ≥ 20`, so this term is well under `0.05`.
  have hb2 : (1 - Real.log 2) / (t ^ ((2:ℝ)/3) * Real.log t) ≤ 0.05 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2),
      mul_le_mul_of_nonneg_right hrpow hlogpos.le]
  unfold C2denomS
  linarith

/-- **`0 < W(t)` for `t > 10^12`.**

### Summary of Proof
`W = 0.194π + 9.908π/log t` with `log t > 20 > 0`; `positivity`.

### References
tex: as `C2denomS_pos`.

### Dependencies
**Depends on:** `C2denomW`, `twenty_lt_log`.
**Used by:** `h0Threshold_pos`, `C2Jensen_antitone_h`, `C2Littlewood_antitone_h`. -/
theorem C2denomW_pos {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 < C2denomW t := by
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogpos : (0:ℝ) < Real.log t := by linarith
  unfold C2denomW
  positivity

/-- **`h0Threshold t = W(t)/S(t)`** for `t > 10^12` — the threshold really is the ratio.

### Summary of Proof
`(97π/500)(1 + 4954/(97 log t))` is `W(t) = 0.194π + 9.908π/log t` rearranged, since
`97/500 = 0.194` and `4954/500 = 9.908`; and `h0Threshold`'s denominator is `S(t)` written with
its two subtracted terms in the opposite order, so the two are reconciled by `ring` rather than
syntactically.

### References
tex: the `h_0` display in `\ref{cor:main-jensen}` (Corollary 4, tex line 209).

### Dependencies
**Depends on:** `h0Threshold`, `C2denomS`, `C2denomW`, `twenty_lt_log`.
**Used by:** `h0Threshold_pos`, `h0Threshold_antitone`, `C2denom_pos_of_h0Threshold_lt`. -/
theorem h0Threshold_eq_div {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    h0Threshold t = C2denomW t / C2denomS t := by
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogne : Real.log t ≠ 0 := by linarith
  have hWeq : 97 * Real.pi / 500 * (1 + 4954 / (97 * Real.log t)) = C2denomW t := by
    unfold C2denomW; field_simp; ring
  unfold h0Threshold C2denomS
  rw [← mul_div_assoc, hWeq]
  congr 1
  ring

/-- **`0 < h0Threshold t` for `t > 10^12`.**

### Summary of Proof
`h0Threshold t = W(t)/S(t)` with both `W` and `S` positive.

### Lean Notes
Exported separately because every use of the affine reduction needs `h ≠ 0` on the domain
`h > h0Threshold t₀`, and this is where `0 < h` comes from.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the `h_0` display, tex line 209.

### Dependencies
**Depends on:** `h0Threshold_eq_div`, `C2denomS_pos`, `C2denomW_pos`.
**Used by:** `C2denom_pos_of_h0Threshold_lt`, `C2Jensen_antitone_h`, `C2Jensen_antitone_t`,
`C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`, both corollaries below, and in
`HalvingConvention` the two `mainPositiveProportionCorollary_*_half`, `Nhalf_one_pos` and the two
`simpleProportionCorollary_*_prose`. -/
theorem h0Threshold_pos {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 < h0Threshold t := by
  rw [h0Threshold_eq_div ht]
  exact div_pos (C2denomW_pos ht) (C2denomS_pos ht)

/-- **`h0Threshold` is exactly the positivity threshold for `C2denom`.** For `t₀ > 10^12` and
`h > h0Threshold t₀`, the common denominator of `C_2^J`/`C_2^L` is positive. (Verified numerically:
at `h = h0Threshold t₀` the denominator is `0` to machine precision, and positive above it.)

### Summary of Proof
Corollary 4 asserts only that "the lower bound on `h₀` precisely ensures this condition is met".
The derivation is routine: `C2denom h t > 0` is linear in `1/h`, so solving
`1 - log(2π)/log t - (1-log 2)/(t^{2/3}log t) > (0.194π + 9.908π/log t)/h` for `h` gives exactly
`h0Threshold t`.

### Lean Notes
`h0Threshold` is *exactly* `W/S`, where
`S = C2denomS t = 1 - log(2π)/log t - (1-log 2)/(t^{2/3}log t)` is the bracket and
`W = C2denomW t = 0.194π + 9.908π/log t` is the `1/h`-coefficient: the
`(97π/500)(1 + 4954/(97 log t))` of its definition is `W` rearranged, since `97/500 = 0.194` and
`4954/500 = 9.908`. That identification is `h0Threshold_eq_div`.

Given it, the proof is three lines: `h > W/S` and `S > 0` give `W < S·h`, hence
`C2denom h t · h = S·h - W > 0` by `C2denom_mul_eq_affine`, and dividing by `h > 0`
(`h0Threshold_pos`) finishes. The numeric work (`log(2π) < 2.08`, `S > 0`) and the `W/S`
identification are the standalone `log_two_pi_lt_two_point_zero_eight`, `C2denomS_pos`,
`C2denomW_pos` and `h0Threshold_eq_div`, because the antitonicity halves need all four
independently.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the sentence justifying the `h_0` lower bound, tex
line 224.

### Dependencies
**Depends on:** `C2denom`, `h0Threshold`, `h0Threshold_eq_div`, `h0Threshold_pos`,
`C2denomS_pos`, `C2denom_mul_eq_affine`, `twenty_lt_log`.
**Used by:** `C2Jensen_antitone_h`, `C2Jensen_antitone_t`, `C2Littlewood_antitone_h`,
`C2Littlewood_antitone_t`; and it is the `hden` hypothesis consumed by
`Ubound_jensen_div_Lbound_le_C2Jensen`, `Ubound_littlewood_div_Lbound_le_C2Littlewood`, both
corollaries below, and `HalvingConvention`'s two half-counted forms and `Nhalf_one_pos`. -/
theorem C2denom_pos_of_h0Threshold_lt {h t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hh : h0Threshold t < h) : 0 < C2denom h t := by
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogne : Real.log t ≠ 0 := by linarith
  have hS := C2denomS_pos ht
  have hhpos : (0:ℝ) < h := (h0Threshold_pos ht).trans hh
  rw [h0Threshold_eq_div ht, div_lt_iff₀ hS] at hh
  have hprod : (0:ℝ) < C2denom h t * h := by
    rw [C2denom_mul_eq_affine h t (ne_of_gt hhpos) hlogne]
    nlinarith [hh]
  nlinarith [hprod, hhpos]

/-- **The normalisation weakening, isolated:** `C2denom h t · (h·log t/π) ≤ L(h,t)`.

### Summary of Proof
`C2denom` is `L(h,t)` divided by `K := (h·log t)/π`, with the single weakening
`c·h²/t² ≤ c/t^{2/3}`, `c := (1-log 2)/π`. Multiplying back by `K` therefore returns `L(h,t)` up
to exactly that one term. Concretely the identity is

    C2denom h t · K = L(h,t) + c·h³/t² - c·h/t^{2/3},

so the claim reduces to `h³/t² ≤ h/t^{2/3}`, i.e. (for `h > 0`) `h² · t^{2/3} ≤ t²`, which is
`h ≤ t^{2/3}` squared. Equality holds exactly at `h = t^{2/3}`.

### Lean Notes
Stated separately from the ratio lemmas because it is **unconditional in `α` and `r`** — it
involves neither — and is the only inequality in either of them; everything else there is an
identity. The constants are checked in `Code/indep_mpmath_constants.py`, block [I]: the gap
`L - C2denom·K = c(h/t^{2/3} - h³/t²)` is `0` at `h = t^{2/3}` and at most `c·2/(3√3) ≈ 0.038`
throughout.

### References
tex: the `C_2` denominator display in `\ref{cor:main-jensen}` (Corollary 4, tex line 214),
against the `L(h,t)` display at tex line 203.

### Dependencies
**Depends on:** `C2denom`, `Lbound`, `twenty_lt_log`.
**Used by:** `Ubound_jensen_div_Lbound_le_C2Jensen`,
`Ubound_littlewood_div_Lbound_le_C2Littlewood`, both corollaries below, and in
`HalvingConvention` the two `mainPositiveProportionCorollary_*_half` and `Nhalf_one_pos`. -/
theorem C2denom_mul_le_Lbound {h t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    C2denom h t * (h * Real.log t / Real.pi) ≤ Lbound h t := by
  have ht0 : (0:ℝ) < t := by nlinarith [ht]
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogpos : (0:ℝ) < Real.log t := by linarith
  have hpi := Real.pi_pos
  have h23pos : (0:ℝ) < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
  have hlogdiv : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div (ne_of_gt ht0) (by positivity)
  -- the single inequality: `h³/t² ≤ h/t^{2/3}`, i.e. `h² t^{2/3} ≤ t²`
  have hpow : (t ^ ((2:ℝ)/3)) ^ (2:ℕ) * t ^ ((2:ℝ)/3) = t ^ (2:ℕ) := by
    rw [← Real.rpow_natCast (t ^ ((2:ℝ)/3)) 2, ← Real.rpow_mul ht0.le,
      ← Real.rpow_add ht0, ← Real.rpow_natCast t 2]
    norm_num
  have hsq : h ^ 2 * t ^ ((2:ℝ)/3) ≤ t ^ 2 := by
    have h1 : h ^ 2 ≤ (t ^ ((2:ℝ)/3)) ^ (2:ℕ) := by nlinarith [hh, hh0]
    nlinarith [h1, h23pos, hpow]
  have hkey : h ^ 3 / t ^ 2 ≤ h / t ^ ((2:ℝ)/3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hh0]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hcoef : (0:ℝ) ≤ (1 - Real.log 2) / Real.pi := div_nonneg (by linarith) hpi.le
  -- `Lbound`'s coefficient `(1-log2)/π` and `C2denom`'s `(1-log2)` differ by exactly the `π` of
  -- the normalisation, so the residual is that shared factor times `h³/t² - h/t^{2/3}`.
  have hid : C2denom h t * (h * Real.log t / Real.pi)
      = Lbound h t
        + (1 - Real.log 2) / Real.pi * (h ^ 3 / t ^ 2 - h / t ^ ((2:ℝ)/3)) := by
    unfold C2denom Lbound
    rw [hlogdiv]
    field_simp
    ring
  rw [hid]
  nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hkey)]

/-- **The arithmetic shape of both ratio lemmas**, over free variables:
if `0 ≤ N`, `0 < D`, `0 < L` and `D·K ≤ L`, then `N·K/L ≤ N/D`.

### Summary of Proof
Cross-multiplying against the two positive denominators, the claim is `N·K·D ≤ N·L`, which is
`D·K ≤ L` scaled by `N ≥ 0`.

### Lean Notes
Isolated over free variables, following the `LittlewoodShort.Dcombo_bound` pattern, so that the
`ring`-level work runs in a small context rather than inside the full `C₂` expressions.

**`0 ≤ N` is not decoration.** With `N < 0` the scaling reverses and the conclusion is false
whenever `D·K < L` strictly, which is why the two ratio lemmas below carry `0 ≤ Ubound_*` as a
hypothesis.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `Ubound_jensen_div_Lbound_le_C2Jensen`,
`Ubound_littlewood_div_Lbound_le_C2Littlewood`. -/
theorem div_mul_le_div_of_denom_le {N K D L : ℝ} (hN : 0 ≤ N) (hD : 0 < D) (hL : 0 < L)
    (hDK : D * K ≤ L) : N * K / L ≤ N / D := by
  rw [div_le_div_iff₀ hL hD]
  nlinarith [mul_le_mul_of_nonneg_left hDK hN]

/-- **The exact normalisation identity for the Jensen mechanism:**
`U_J + E_J = (C₂ᴶ's numerator) · (h·log t/π)`.

### Summary of Proof
Dividing `Ubound_jensen` by `K := (h·log t)/π` is what produces `C2Jensen`'s numerator, term by
term: the `B₁` term loses its `1/π` and its `log t`, the `B₂` and `B₃` terms each gain a `π` and
a `1/log t`, `B₄` gains `π/(h log t)`, and `E_J = 3.35/(D_{r,α}t^{1/3})` becomes
`3.35π/(D_{r,α}·h·t^{1/3}·log t)`. This states the identity in the cleared form.

### Lean Notes
An identity, not an inequality — the whole `≤` in the ratio lemma comes from the *denominator*
(`C2denom_mul_le_Lbound`), never from the numerator.

`rectDenom r α ≠ 0` is needed only to clear denominators. When `rectDenom r α = 0` every `B_i`
and `E_J` is Lean-zero (each has `rectDenom` in a denominator), so both sides vanish and the
identity still holds; the ratio lemmas below dispatch that case separately.

The identity was checked numerically to `2·10⁻³¹` relative error. The corrected `C_2` formulas
themselves, with certified final digits, are produced by `Code/compute_C2_tables.sage`, whose
header also records why the earlier printed forms were systematically missing factors of `π`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the normalisation step of its proof, tex lines
221–222.

### Dependencies
**Depends on:** `Ubound_jensen`, `UJensen`, `EJensen`, `B1`, `B2`, `B3`, `B4`, `hatAlpha`,
`rectDenom`.
**Used by:** `Ubound_jensen_div_Lbound_le_C2Jensen`. -/
theorem Ubound_jensen_eq_num_mul {α r h t : ℝ} (hh0 : h ≠ 0)
    (hlogne : Real.log t ≠ 0) (ht0 : 0 < t) (hD : rectDenom r α ≠ 0) :
    Ubound_jensen α r h t
      = ((2 + 2 * hatAlpha r α / h) *
            (B1 α r + Real.pi * B2 α r * Real.log (Real.log t) / Real.log t
              + Real.pi * B3 α r / Real.log t)
          + Real.pi * B4 α r / (h * Real.log t)
          + 3.35 * Real.pi / (rectDenom r α * h * t ^ ((1 : ℝ) / 3) * Real.log t))
        * (h * Real.log t / Real.pi) := by
  have ht13 : (0:ℝ) < t ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
  have hpi := Real.pi_pos
  unfold Ubound_jensen UJensen EJensen B1 B2 B3 B4
  field_simp
  try ring

/-- **`C2Jensen` bounds the normalised ratio.** For `h ≤ t^{2/3}` and a positive denominator,
`Ubound_jensen α r h t / Lbound h t ≤ C2Jensen α r h t`.

### Summary of Proof
The algebraic heart of `Corollary \ref{cor:main-jensen}` (Corollary 4) — the step the tex
introduces with "By inspection we have" (tex line 220). Dividing numerator and denominator of
`U_J/L` by `(h·log t)/π` gives `C2Jensen` *exactly*, apart from the single weakening
`(1-log 2)h²/(t² log t) ≤ (1-log 2)/(t^{2/3} log t)`, which uses `h ≤ t^{2/3}` (so equality holds
at `h = t^{2/3}`).

### Lean Notes
**Two hypotheses here are not in the tex, and both are genuinely needed rather than artefacts.**

`0 < h` — without it the normalisation constant `K = (h log t)/π` is not positive and the whole
division argument reverses. The tex never states it because `h` is a half-window width; every
intended use has `h > h₀ > 0`.

`0 ≤ Ubound_jensen α r h t` — the scaling step `div_mul_le_div_of_denom_le` needs the numerator
non-negative, and with `N < 0` its conclusion is false whenever `D·K < L` strictly. It is carried
as a hypothesis rather than derived, so that this lemma stays purely algebraic in `α`, `r`, `h`,
`t`; call sites get it from the count being non-negative, as
`mainPositiveProportionCorollary_jensen` does via `Nrect_nonneg` and
`MainTheorem.mainJensen`. It is also available directly from signs: `B1 = c1/D`, `B2 = c2/(πD)`,
`B3 = c3/(πD)`, `B4 = (2Φ(1)+c5)/D` with `D = rectDenom r α > 0`
(`RectangularBounds.rectDenom_pos`), plus `2h + 2α̂_r > 0`, `log t > 0` and `loglog t > 0` at
`t > 10^12`, and all four numerators non-negative (`ConstantSigns.c1_nonneg`, `c2_nonneg`,
`c3_nonneg`, `two_Phi_one_add_c5_nonneg`).

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the displayed `U_J/L` inequality in its proof, tex
lines 221–222.

### Dependencies
**Depends on:** `Ubound_jensen_eq_num_mul`, `div_mul_le_div_of_denom_le`, `C2denom_mul_le_Lbound`,
`twenty_lt_log`.
**Used by:** `mainPositiveProportionCorollary_jensen`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`. -/
theorem Ubound_jensen_div_Lbound_le_C2Jensen {α r h t : ℝ}
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) (hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hden : 0 < C2denom h t) (hL : 0 < Lbound h t)
    (hUnonneg : 0 ≤ Ubound_jensen α r h t) :
    Ubound_jensen α r h t / Lbound h t ≤ C2Jensen α r h t := by
  have ht0 : (0:ℝ) < t := by nlinarith [ht]
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogne : Real.log t ≠ 0 := by linarith
  rcases eq_or_ne (rectDenom r α) 0 with hD | hD
  · -- Degenerate: every `B_i` and `E_J` carries `rectDenom` in a denominator, so both sides are
    -- Lean-zero and the claim is `0 ≤ 0`.
    simp [Ubound_jensen, UJensen, EJensen, C2Jensen, B1, B2, B3, B4, hD]
  · have hK : (0:ℝ) < h * Real.log t / Real.pi := by
      have := Real.pi_pos
      positivity
    rw [Ubound_jensen_eq_num_mul (ne_of_gt hh0) hlogne ht0 hD] at hUnonneg ⊢
    exact div_mul_le_div_of_denom_le ((mul_nonneg_iff_of_pos_right hK).mp hUnonneg) hden hL
      (C2denom_mul_le_Lbound ht hh0 hh)

/-- **The exact normalisation identity for the Littlewood mechanism:**
`U_L + E_L = (C₂ᴸ's numerator) · (h·log t/π)`.

### Summary of Proof
The Littlewood counterpart of `Ubound_jensen_eq_num_mul`, by the same division by
`K := (h·log t)/π`: the `A₁`/`A₄` terms lose their `1/π` and `log t`, the `A₂`/`A₅` and `A₃`/`A₆`
terms each gain a `π` and a `1/log t`, and `E_L = (1/(t(r-α)))(0.335 + 0.51/log t)` becomes
`π/((r-α)·h·t·log t)·(0.335 + 0.51/log t)`.

### Lean Notes
An identity, as in the Jensen case — the `≤` of the ratio lemma comes entirely from the
denominator. `r - α ≠ 0` is needed only to clear `E_L`'s denominator; when `r = α` both sides
are Lean-zero in that term.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), whose proof (tex line 240) defers to
`\ref{cor:main-jensen}` (Corollary 4).

### Dependencies
**Depends on:** `Ubound_littlewood`, `ULittlewood`, `ELittlewood`, `A1`, `A2`, `A3`, `A4`, `A5`,
`A6`.
**Used by:** `Ubound_littlewood_div_Lbound_le_C2Littlewood`. -/
theorem Ubound_littlewood_eq_num_mul {α r h t : ℝ} {k : ℤ} (hh0 : h ≠ 0)
    (hlogne : Real.log t ≠ 0) (ht0 : 0 < t) (hrα : r - α ≠ 0) :
    Ubound_littlewood α r h t k
      = (2 * A1 α r k + 2 * A4 α r / h
          + Real.pi * (2 * A2 α r k + 2 * A5 α r / h) * Real.log (Real.log t) / Real.log t
          + 2 * Real.pi * A3 α r k / Real.log t
          + Real.pi * A6 α r / (h * Real.log t)
          + Real.pi / ((r - α) * h * t * Real.log t) * (0.335 + 0.51 / Real.log t))
        * (h * Real.log t / Real.pi) := by
  have hpi := Real.pi_pos
  unfold Ubound_littlewood ULittlewood ELittlewood
  field_simp
  try ring

/-- **The Littlewood analogue of `Ubound_jensen_div_Lbound_le_C2Jensen`**: the algebraic heart of
`Corollary \ref{cor:main-littlewood}` (Corollary 5).
`Ubound_littlewood α r h t k / Lbound h t ≤ C2Littlewood α r h t k`.

### Summary of Proof
Same normalisation by `(h·log t)/π` as the Jensen version, same single `h ≤ t^{2/3}` weakening in
the denominator, same exactness — numerically verified to `1.000000` at `h = t^{2/3}`. The tex's
proof of Corollary 5 reads in full: "The proof is the same as the above."

### Lean Notes
Three hypotheses beyond the tex's, for the reasons given at length in
`Ubound_jensen_div_Lbound_le_C2Jensen`'s Lean Notes: `0 < h` (else the normalisation constant is
not positive), `α < r` (needed only to clear `E_L`'s `1/(r-α)`; the Jensen version instead
case-splits on `rectDenom r α = 0`), and `0 ≤ Ubound_littlewood` for the scaling step.

**The non-negativity is harder to supply directly here than on the Jensen side.** `A1`, `A2`,
`A3` are chord values `(m_k(1-r)+b_k)/(2(r-α))` and its `'`/`''` analogues, so their signs come
from the chord machinery of `JensenScaleConstants` rather than from a `c_i ≥ 0` fact; `A6`
additionally carries `Φ(1+ηr)` and `log‖ζ(1+ηr)‖`, the latter of unrestricted sign in general.
The route callers take instead is through `MainTheorem.mainLittlewood`: the count it bounds is
non-negative, so `0 ≤ Ubound_littlewood` follows by `le_trans`, which is what
`mainPositiveProportionCorollary_littlewood` does.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), whose proof (tex line 240) defers to
`\ref{cor:main-jensen}` (Corollary 4).

### Dependencies
**Depends on:** `Ubound_littlewood_eq_num_mul`, `div_mul_le_div_of_denom_le`,
`C2denom_mul_le_Lbound`, `twenty_lt_log`.
**Used by:** `mainPositiveProportionCorollary_littlewood`,
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`. -/
theorem Ubound_littlewood_div_Lbound_le_C2Littlewood {α r h t : ℝ} {k : ℤ}
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) (hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hrαlt : α < r) (hden : 0 < C2denom h t) (hL : 0 < Lbound h t)
    (hUnonneg : 0 ≤ Ubound_littlewood α r h t k) :
    Ubound_littlewood α r h t k / Lbound h t ≤ C2Littlewood α r h t k := by
  have ht0 : (0:ℝ) < t := by nlinarith [ht]
  have hlog : (20:ℝ) < Real.log t := twenty_lt_log ht
  have hlogne : Real.log t ≠ 0 := by linarith
  have hrα : r - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrαlt)
  have hK : (0:ℝ) < h * Real.log t / Real.pi := by
    have := Real.pi_pos
    positivity
  rw [Ubound_littlewood_eq_num_mul (ne_of_gt hh0) hlogne ht0 hrα] at hUnonneg ⊢
  exact div_mul_le_div_of_denom_le ((mul_nonneg_iff_of_pos_right hK).mp hUnonneg) hden hL
    (C2denom_mul_le_Lbound ht hh0 hh)

/-! ## Generic monotonicity infrastructure

Everything in this section is free of `ζ`, of the `A_i`/`B_i`, and of the tex; it is the
elementary analysis that the four antitonicity halves are assembled from. All of it is proved.

Three shapes recur, and each gets one lemma:

* `(p·h + q)/(s·h - w)` decreasing in `h` — the `h`-halves (`affine_div_affine_antitoneOn`);
* `f/g` with `f` antitone non-negative and `g` monotone positive — the `t`-halves
  (`div_antitoneOn_of_antitoneOn_of_monotoneOn`);
* `(a·loglog t + b)/log t` decreasing in `t` — every `t`-dependent numerator term
  (`loglog_affine_div_log_antitoneOn`).

The third is the one with real content. It is **not** termwise: `b` may be negative (it is
`2πA₃` on the Littlewood side, and `A₃` genuinely changes sign — see
`Code/verify_c3_and_chord_signs.py`, part (3)), so `b/log t` alone is *increasing*. The trick
is the exact rewrite

    (a·log x + b)/x  =  (a/e)·(log(x/e)/(x/e))  +  (a + b)/x,

which splits it into Mathlib's `Real.log_div_self_antitoneOn` (valid from `x/e ≥ e`, i.e.
`x ≥ e²`, and `log t > 20 > e²`) plus a term needing only `a + b ≥ 0`. That is why the
side condition throughout is `0 ≤ a` **and** `0 ≤ a + b`, not `0 ≤ b`. -/

/-- **Affine over affine is decreasing**, in the non-strict form the corollaries need:
`(p·h + q)/(s·h - w)` is `AntitoneOn` on `{h | 0 < s·h - w}` when `0 ≤ p`, `0 ≤ q`, `0 < s`,
`0 ≤ w`.

### Summary of Proof
Cross-multiplying across the two positive denominators, the difference collapses to
`(b - a)·(p·w + q·s) ≥ 0`.

### Lean Notes
`Definitions.affine_div_affine_strictAntiOn` is the strict version, but it asks for `0 < p` and
`r < 0` strictly. `0 < p` is exactly what the `B_i`/`A_i` cannot supply — `c1_nonneg` and
`c2_nonneg` are `≤`, not `<` — so this weakening is what makes the `h`-halves go through.
`AntitoneOn` is also all the corollaries want. Should migrate to `Definitions.lean` next to
`affine_div_affine_strictAntiOn`.

Note the sign convention differs: the strict lemma writes the denominator `s·h + r` with `r < 0`,
this one writes `s·h - w` with `0 ≤ w`, to match `C2denom_mul_eq_affine`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `C2Jensen_antitone_h`, `C2Littlewood_antitone_h`. -/
theorem affine_div_affine_antitoneOn {p q s w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 < s)
    (hw : 0 ≤ w) :
    AntitoneOn (fun h : ℝ => (p * h + q) / (s * h - w)) {h : ℝ | 0 < s * h - w} := by
  intro a ha b hb hab
  replace ha : (0:ℝ) < s * a - w := ha
  replace hb : (0:ℝ) < s * b - w := hb
  simp only
  rw [div_le_div_iff₀ hb ha]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (mul_nonneg hp hw),
    mul_nonneg (sub_nonneg.mpr hab) (mul_nonneg hq hs.le)]

/-- **A decreasing non-negative numerator over an increasing positive denominator is
decreasing.**

### Summary of Proof
For `a ≤ b` in the set, cross-multiplying gives `f b · g a ≤ f a · g b`, which is
`g b·(f a - f b) + f b·(g b - g a) ≥ 0`.

### Lean Notes
This is the sentence `C2Jensen_antitone_t`'s Summary of Proof appeals to ("A decreasing
non-negative numerator over an increasing positive denominator is decreasing"), as a lemma.
Non-negativity of `f` is essential: with `f < 0` the conclusion reverses.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `C2Jensen_antitone_t`, `C2Littlewood_antitone_t`. -/
theorem div_antitoneOn_of_antitoneOn_of_monotoneOn {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AntitoneOn f s) (hfnn : ∀ x ∈ s, 0 ≤ f x) (hg : MonotoneOn g s)
    (hgpos : ∀ x ∈ s, 0 < g x) :
    AntitoneOn (fun x => f x / g x) s := by
  intro a ha b hb hab
  simp only
  rw [div_le_div_iff₀ (hgpos b hb) (hgpos a ha)]
  nlinarith [hf ha hb hab, hg ha hb hab, hfnn b hb, hgpos a ha, hgpos b hb]

/-- **`a/b = a·c/(b·c)` for `c ≠ 0`**, including when `b = 0`.

### Summary of Proof
If `b = 0` both sides are Lean-zero; otherwise `field_simp`.

### Lean Notes
Stated to move `C2Jensen`/`C2Littlewood` from `num/C2denom` to `(num·h)/(C2denom·h)` without
having to know the sign of `C2denom` first. Mathlib's `mul_div_mul_right` does the same job but
its argument order has drifted between versions.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `C2Jensen_eq_affine`, `C2Littlewood_eq_affine`. -/
theorem div_eq_mul_div_mul_right {a b c : ℝ} (hc : c ≠ 0) : a / b = a * c / (b * c) := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  · field_simp

/-- **`(a·log x + b)/x` is decreasing for `x ≥ e²`**, given `0 ≤ a` and `0 ≤ a + b`.

### Summary of Proof
Exact rewrite `(a log x + b)/x = (a/e)·(log(x/e)/(x/e)) + (a+b)/x`. The first summand is
`a/e ≥ 0` times `Real.log_div_self_antitoneOn` evaluated at `x/e ≥ e` (which is `x ≥ e²`); the
second is a non-negative constant over an increasing positive `x`.

### Lean Notes
`0 ≤ b` is *not* assumed, and must not be: the Littlewood instance has `b = 2πA₃` with `A₃` of
either sign. What is needed is `a + b ≥ 0`, i.e. the value of the affine function at `x = e`.

### References
No tex counterpart. External: `Real.log_div_self_antitoneOn` (Mathlib,
`Analysis/SpecialFunctions/Log/Monotone.lean`).

### Dependencies
**Depends on:** `Real.log_div_self_antitoneOn`.
**Used by:** `loglog_affine_div_log_antitoneOn`. -/
theorem log_affine_div_self_antitoneOn {a b : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + b) :
    AntitoneOn (fun x : ℝ => (a * Real.log x + b) / x) (Set.Ici (Real.exp 1 * Real.exp 1)) := by
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  intro x hx y hy hxy
  replace hx : Real.exp 1 * Real.exp 1 ≤ x := hx
  replace hy : Real.exp 1 * Real.exp 1 ≤ y := hy
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (by positivity) hx
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le (by positivity) hy
  have key : ∀ z : ℝ, 0 < z →
      (a * Real.log z + b) / z
        = a / Real.exp 1 * (Real.log (z / Real.exp 1) / (z / Real.exp 1)) + (a + b) / z := by
    intro z hz
    rw [Real.log_div (ne_of_gt hz) (Real.exp_ne_zero 1), Real.log_exp]
    field_simp
    ring
  simp only
  rw [key x hx0, key y hy0]
  have hxe : Real.exp 1 ≤ x / Real.exp 1 := by rw [le_div_iff₀ he]; linarith
  have hye : Real.exp 1 ≤ y / Real.exp 1 := by rw [le_div_iff₀ he]; linarith
  have hxye : x / Real.exp 1 ≤ y / Real.exp 1 := by gcongr
  have hstep : Real.log (y / Real.exp 1) / (y / Real.exp 1)
      ≤ Real.log (x / Real.exp 1) / (x / Real.exp 1) :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hxe) (Set.mem_Ici.mpr hye) hxye
  have h1 : a / Real.exp 1 * (Real.log (y / Real.exp 1) / (y / Real.exp 1))
      ≤ a / Real.exp 1 * (Real.log (x / Real.exp 1) / (x / Real.exp 1)) := by
    have : (0:ℝ) ≤ a / Real.exp 1 := by positivity
    exact mul_le_mul_of_nonneg_left hstep this
  have h2 : (a + b) / y ≤ (a + b) / x := by gcongr
  linarith

/-- **`(a·loglog t + b)/log t` is decreasing in `t` on `Ici t₀` for `t₀ > 10^12`**, given
`0 ≤ a` and `0 ≤ a + b`.

### Summary of Proof
`log` is monotone and `log t > 20 > e² ≈ 7.39` on the range (`twenty_lt_log`), so this is
`log_affine_div_self_antitoneOn` composed with `Real.log`.

### Lean Notes
Stated on `Set.Ici t₀` rather than `Set.Ioi t₀` because the `t`-halves also have to compare a
point of `Ioi t₀` against `t₀` itself, to transport `0 < C2denom h t₀` outwards.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_affine_div_self_antitoneOn`, `twenty_lt_log`, `Real.exp_one_lt_d9`.
**Used by:** `C2JensenP_antitoneOn`, `C2LittlewoodP_antitoneOn`, `C2LittlewoodQ_antitoneOn`.
(`C2JensenQ_antitoneOn` does not use it: its `B₄` term is handled by `gcongr` and its error term
by `const_div_mul_rpow_mul_log_le`.) -/
theorem loglog_affine_div_log_antitoneOn {a b t0 : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + b)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    AntitoneOn (fun t : ℝ => (a * Real.log (Real.log t) + b) / Real.log t) (Set.Ici t0) := by
  intro x hx y hy hxy
  replace hx : t0 ≤ x := hx
  replace hy : t0 ≤ y := hy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := lt_of_lt_of_le ht0 hx
  have hyg : (10:ℝ) ^ (12:ℕ) < y := lt_of_lt_of_le ht0 hy
  have hlx := twenty_lt_log hxg
  have hly := twenty_lt_log hyg
  have hx0 : (0:ℝ) < x := by nlinarith [hxg]
  have hmono : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have he2 : Real.exp 1 * Real.exp 1 ≤ Real.log x := by
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  exact log_affine_div_self_antitoneOn ha hab (Set.mem_Ici.mpr he2)
    (Set.mem_Ici.mpr (he2.trans hmono)) hmono

/-- **`(a·loglog t + b)/log t ≥ 0` for `t > 10^12`**, given `0 ≤ a` and `0 ≤ a + b`.

### Summary of Proof
`log t > 20 > e`, so `loglog t > 1`; hence `a·loglog t + b ≥ a + b ≥ 0`, over `log t > 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log`, `Real.exp_one_lt_d9`.
**Used by:** `C2JensenP_nonneg`, `C2LittlewoodP_nonneg`, `C2LittlewoodQ_nonneg`.
(`C2JensenQ_nonneg` does not use it: its non-`P` terms are `positivity` and
`const_div_mul_rpow_mul_log_nonneg`.) -/
theorem loglog_affine_div_log_nonneg {a b t : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + b)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 ≤ (a * Real.log (Real.log t) + b) / Real.log t := by
  have hlog := twenty_lt_log ht
  have hone : (1:ℝ) ≤ Real.log (Real.log t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    nlinarith [Real.exp_one_lt_d9]
  exact div_nonneg (by nlinarith) (by linarith)

/-- **`c/(d·t^e·log t)` is decreasing in `t`**, for `0 ≤ c`, `0 < d`, `0 ≤ e` and `t > 10^12`.

### Summary of Proof
`t ↦ t^e` and `t ↦ log t` are both monotone and positive on the range, so the denominator
increases; `gcongr`.

### Lean Notes
Covers both the `(1-log 2)/(t^{2/3} log t)` term of `C2denomS` (at `d = 1`) and the
`3.35π/(D_{r,α} t^{1/3} log t)` term of `C₂ᴶ`'s numerator.

### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log`.
**Used by:** `C2denomS_le`, `C2JensenQ_antitoneOn`. -/
theorem const_div_mul_rpow_mul_log_le {c d e a b : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (he : 0 ≤ e)
    (ha : (10 : ℝ) ^ (12 : ℕ) < a) (hab : a ≤ b) :
    c / (d * b ^ e * Real.log b) ≤ c / (d * a ^ e * Real.log a) := by
  have ha0 : (0:ℝ) < a := by nlinarith [ha]
  have hla := twenty_lt_log ha
  have hlb := twenty_lt_log (lt_of_lt_of_le ha hab)
  have hmono : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hrpow : a ^ e ≤ b ^ e := Real.rpow_le_rpow ha0.le hab he
  have hapow : (0:ℝ) < a ^ e := Real.rpow_pos_of_pos ha0 e
  have hbpow : (0:ℝ) < b ^ e := Real.rpow_pos_of_pos (by linarith) e
  have hlapos : (0:ℝ) < Real.log a := by linarith
  gcongr

/-- **`0 ≤ c/(d·t^e·log t)` for `0 ≤ c`, `0 < d` and `t > 10^12`.**

### Summary of Proof
`positivity`, once `log t > 20 > 0` and `t^e > 0` are in context.

### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log`.
**Used by:** `C2JensenQ_nonneg`. -/
theorem const_div_mul_rpow_mul_log_nonneg {c d e t : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 ≤ c / (d * t ^ e * Real.log t) := by
  have ht0 : (0:ℝ) < t := by nlinarith [ht]
  have hlog := twenty_lt_log ht
  have hpow : (0:ℝ) < t ^ e := Real.rpow_pos_of_pos ht0 e
  positivity

/-- **`C2denomS` is increasing in `t`** on `t > 10^12`.

### Summary of Proof
Both subtracted terms shrink: `log(2π)/log t` because `log(2π) > 0` and `log t` increases, and
`(1-log 2)/(t^{2/3}log t)` by `const_div_mul_rpow_mul_log_le` at `d = 1`.

### References
tex: implicit in `\ref{cor:main-jensen}` (Corollary 4)'s "decreasing in `t_0`" claim (tex line
216) — the denominator's growth is half of why the ratio falls.

### Dependencies
**Depends on:** `C2denomS`, `const_div_mul_rpow_mul_log_le`, `twenty_lt_log`.
**Used by:** `C2denomAff_monotoneOn`, `h0Threshold_antitone`. -/
theorem C2denomS_le {a b : ℝ} (ha : (10 : ℝ) ^ (12 : ℕ) < a) (hab : a ≤ b) :
    C2denomS a ≤ C2denomS b := by
  have ha0 : (0:ℝ) < a := by nlinarith [ha]
  have hla := twenty_lt_log ha
  have hlb := twenty_lt_log (lt_of_lt_of_le ha hab)
  have hmono : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlog2pi : (0:ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlapos : (0:ℝ) < Real.log a := by linarith
  have h1 : Real.log (2 * Real.pi) / Real.log b ≤ Real.log (2 * Real.pi) / Real.log a := by
    gcongr
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  -- the same helper at `d = 1`; `simpa` strips the resulting `1 * _`
  have h2 : (1 - Real.log 2) / (b ^ ((2:ℝ)/3) * Real.log b)
      ≤ (1 - Real.log 2) / (a ^ ((2:ℝ)/3) * Real.log a) := by
    have := const_div_mul_rpow_mul_log_le (c := 1 - Real.log 2) (d := 1) (e := (2:ℝ)/3)
      (by linarith) one_pos (by norm_num) ha hab
    simpa using this
  unfold C2denomS
  linarith

/-- **`C2denomW` is decreasing in `t`** on `t > 10^12`.

### Summary of Proof
`W = 0.194π + 9.908π/log t` and `log t` increases through positive values.

### References
tex: as `C2denomS_le`.

### Dependencies
**Depends on:** `C2denomW`, `twenty_lt_log`.
**Used by:** `C2denomAff_monotoneOn`, `h0Threshold_antitone`. -/
theorem C2denomW_le {a b : ℝ} (ha : (10 : ℝ) ^ (12 : ℕ) < a) (hab : a ≤ b) :
    C2denomW b ≤ C2denomW a := by
  have ha0 : (0:ℝ) < a := by nlinarith [ha]
  have hla := twenty_lt_log ha
  have hlb := twenty_lt_log (lt_of_lt_of_le ha hab)
  have hmono : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlapos : (0:ℝ) < Real.log a := by linarith
  have h1 : 9.908 * Real.pi / Real.log b ≤ 9.908 * Real.pi / Real.log a := by
    gcongr
  unfold C2denomW
  linarith

/-- **The cleared denominator `S(t)·h - W(t)` is increasing in `t`**, for fixed `h > 0`.

### Summary of Proof
`S` increases (`C2denomS_le`) and is multiplied by the positive constant `h`; `W` decreases
(`C2denomW_le`) and is subtracted.

### Lean Notes
On `Set.Ici t₀`, not `Ioi t₀`, so that the `t`-halves can transport positivity from `t₀` itself
outwards — see `C2Jensen_antitone_t`. Positivity is then carried along this monotonicity rather
than by re-deriving `0 < C2denom h t` at each `t`, which would need `h > h0Threshold t` there.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "denominator increases" half of the
`t`-monotonicity claim (tex line 223).

### Dependencies
**Depends on:** `C2denomS_le`, `C2denomW_le`.
**Used by:** `C2Jensen_antitone_t`, `C2Littlewood_antitone_t`. -/
theorem C2denomAff_monotoneOn {h t0 : ℝ} (hh : 0 < h) (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    MonotoneOn (fun t => C2denomS t * h - C2denomW t) (Set.Ici t0) := by
  intro x hx y hy hxy
  replace hx : t0 ≤ x := hx
  have hxg : (10:ℝ) ^ (12:ℕ) < x := lt_of_lt_of_le ht0 hx
  have hS := C2denomS_le hxg hxy
  have hW := C2denomW_le hxg hxy
  simp only
  nlinarith [hS, hW, hh]

/-! ## The Jensen numerator in affine form

Multiplying `C2Jensen`'s numerator and denominator by `h` puts it in the shape

    C₂ᴶ(α,r,h,t) = (P(t)·h + Q(t)) / (S(t)·h - W(t)),

with `P = C2JensenP` and `Q = C2JensenQ` below. Both antitonicity halves then reduce to sign and
monotonicity facts about `P` and `Q` alone. -/

/-- **The `h`-coefficient of `C₂ᴶ`'s cleared numerator:**
`P(t) = 2(B₁ + πB₂·loglog t/log t + πB₃/log t)`.

### Summary of Proof
A definition. It is `C2Jensen`'s numerator times `h`, keeping only the terms that survive with a
factor `h` — i.e. the `2·(bracket)` coming from the `2` in `(2 + 2α̂_r/h)`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the `C_2^J` numerator at tex lines 213–214; the
`B_{i,α,r}` are from `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B1`, `B2`, `B3`.
**Used by:** `C2JensenQ`, `C2JensenP_eq`, `C2Jensen_num_mul`, `C2Jensen_eq_affine`,
`C2JensenP_nonneg`, `C2JensenP_antitoneOn`. -/
noncomputable def C2JensenP (α r t : ℝ) : ℝ :=
  2 * (B1 α r + Real.pi * B2 α r * Real.log (Real.log t) / Real.log t
        + Real.pi * B3 α r / Real.log t)

/-- **The `h`-free part of `C₂ᴶ`'s cleared numerator:**
`Q(t) = α̂_r·P(t) + πB₄/log t + 3.35π/(D_{r,α} t^{1/3} log t)`.

### Summary of Proof
A definition. The `2α̂_r/h` of `(2 + 2α̂_r/h)` contributes `2α̂_r·(bracket) = α̂_r·P(t)` once
multiplied by `h`; the `B₄` and error terms each lose their `1/h`.

### References
tex: as `C2JensenP`.

### Dependencies
**Depends on:** `C2JensenP`, `B4`, `hatAlpha`, `rectDenom`.
**Used by:** `C2JensenQ_antitoneOn`, `C2JensenQ_nonneg`, `C2Jensen_antitone_h`,
`C2Jensen_antitone_t`, `C2Jensen_eq_affine`, `C2Jensen_num_mul`. -/
noncomputable def C2JensenQ (α r t : ℝ) : ℝ :=
  hatAlpha r α * C2JensenP α r t + Real.pi * B4 α r / Real.log t
    + 3.35 * Real.pi / (rectDenom r α * t ^ ((1 : ℝ) / 3) * Real.log t)

/-- **`P` over a common `log t`:** `P(t) = 2B₁ + (2πB₂·loglog t + 2πB₃)/log t`.

### Summary of Proof
`field_simp`; the two `1/log t` terms are collected.

### Lean Notes
This is the form `loglog_affine_div_log_antitoneOn` and `loglog_affine_div_log_nonneg` consume,
with `a = 2πB₂` and `b = 2πB₃`.

### References
No tex counterpart — bookkeeping.

### Dependencies
**Depends on:** `C2JensenP`.
**Used by:** `C2JensenP_nonneg`, `C2JensenP_antitoneOn`. -/
theorem C2JensenP_eq {α r t : ℝ} (hlog : Real.log t ≠ 0) :
    C2JensenP α r t
      = 2 * B1 α r
        + (2 * Real.pi * B2 α r * Real.log (Real.log t) + 2 * Real.pi * B3 α r) / Real.log t := by
  unfold C2JensenP
  field_simp
  ring

/-- **`0 ≤ P(t)` for `t > 10^12` and `0 < α < r < 1`.**

### Summary of Proof
`2B₁ ≥ 0` plus `loglog_affine_div_log_nonneg` at `a = 2πB₂ ≥ 0`, `b = 2πB₃ ≥ 0`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4).

### Dependencies
**Depends on:** `C2JensenP_eq`, `B1_nonneg`, `B2_nonneg`, `B3_nonneg`,
`loglog_affine_div_log_nonneg`, `twenty_lt_log`.
**Used by:** `C2JensenQ_nonneg`, `C2Jensen_antitone_h`, `C2Jensen_antitone_t`. -/
theorem C2JensenP_nonneg {α r t : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 ≤ C2JensenP α r t := by
  have hlog := twenty_lt_log ht
  have hb1 := B1_nonneg hα hαr hr1
  have hb2 := B2_nonneg hα hαr
  have hb3 := B3_nonneg hα hαr hr1
  have ha : (0:ℝ) ≤ 2 * Real.pi * B2 α r := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * B2 α r + 2 * Real.pi * B3 α r := by positivity
  have := loglog_affine_div_log_nonneg ha hab ht
  rw [C2JensenP_eq (by linarith : Real.log t ≠ 0)]
  linarith

/-- **`0 ≤ Q(t)` for `t > 10^12` and `0 < α < r < 1`.**

### Summary of Proof
`α̂_r = √(r²-α²) ≥ 0` times `C2JensenP_nonneg`, plus `πB₄/log t ≥ 0` and the error term
`3.35π/(D_{r,α}t^{1/3}log t) ≥ 0` by `const_div_mul_rpow_mul_log_nonneg`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4).

### Dependencies
**Depends on:** `C2JensenP_nonneg`, `B4_nonneg`, `const_div_mul_rpow_mul_log_nonneg`,
`hatAlpha`, `rectDenom_pos`, `twenty_lt_log`.
**Used by:** `C2Jensen_antitone_h`, `C2Jensen_antitone_t`. -/
theorem C2JensenQ_nonneg {α r t : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 ≤ C2JensenQ α r t := by
  have hlog := twenty_lt_log ht
  have hP := C2JensenP_nonneg hα hαr hr1 ht
  have hb4 := B4_nonneg hα hαr hr1
  have hâ : (0:ℝ) ≤ hatAlpha r α := Real.sqrt_nonneg _
  have h1 : (0:ℝ) ≤ Real.pi * B4 α r / Real.log t := by
    apply div_nonneg (by positivity) (by linarith)
  have h2 : (0:ℝ) ≤ 3.35 * Real.pi / (rectDenom r α * t ^ ((1:ℝ)/3) * Real.log t) :=
    const_div_mul_rpow_mul_log_nonneg (by positivity) (rectDenom_pos hα hαr) ht
  unfold C2JensenQ
  have := mul_nonneg hâ hP
  linarith

/-- **`P` is decreasing in `t`** on `Ici t₀` for `t₀ > 10^12` and `0 < α < r < 1`.

### Summary of Proof
`P(t) = 2B₁ + (2πB₂·loglog t + 2πB₃)/log t`; the constant `2B₁` is `t`-free and the rest is
`loglog_affine_div_log_antitoneOn` at `a = 2πB₂ ≥ 0`, `b = 2πB₃ ≥ 0`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "decreasing in `t_0`" claim.

### Dependencies
**Depends on:** `C2JensenP_eq`, `B2_nonneg`, `B3_nonneg`, `loglog_affine_div_log_antitoneOn`,
`twenty_lt_log`.
**Used by:** `C2JensenQ_antitoneOn`, `C2Jensen_antitone_t`. -/
theorem C2JensenP_antitoneOn {α r t0 : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    AntitoneOn (fun t => C2JensenP α r t) (Set.Ici t0) := by
  have hb2 := B2_nonneg hα hαr
  have hb3 := B3_nonneg hα hαr hr1
  have ha : (0:ℝ) ≤ 2 * Real.pi * B2 α r := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * B2 α r + 2 * Real.pi * B3 α r := by positivity
  intro x hx y hy hxy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := lt_of_lt_of_le ht0 hx
  have hyg : (10:ℝ) ^ (12:ℕ) < y := lt_of_lt_of_le ht0 hy
  have hlx := twenty_lt_log hxg
  have hly := twenty_lt_log hyg
  have hstep := loglog_affine_div_log_antitoneOn ha hab ht0 hx hy hxy
  simp only
  rw [C2JensenP_eq (by linarith : Real.log x ≠ 0),
    C2JensenP_eq (by linarith : Real.log y ≠ 0)]
  simp only at hstep
  linarith

/-- **`Q` is decreasing in `t`** on `Ici t₀` for `t₀ > 10^12` and `0 < α < r < 1`.

### Summary of Proof
Three antitone summands: `α̂_r·P(t)` (non-negative multiple of `C2JensenP_antitoneOn`),
`πB₄/log t` (non-negative constant over an increasing `log t`), and the error term by
`const_div_mul_rpow_mul_log_le`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "decreasing in `t_0`" claim.

### Dependencies
**Depends on:** `C2JensenP_antitoneOn`, `B4_nonneg`, `const_div_mul_rpow_mul_log_le`,
`hatAlpha`, `rectDenom_pos`, `twenty_lt_log`.
**Used by:** `C2Jensen_antitone_t`. -/
theorem C2JensenQ_antitoneOn {α r t0 : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    AntitoneOn (fun t => C2JensenQ α r t) (Set.Ici t0) := by
  have hb4 := B4_nonneg hα hαr hr1
  have hâ : (0:ℝ) ≤ hatAlpha r α := Real.sqrt_nonneg _
  intro x hx y hy hxy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := lt_of_lt_of_le ht0 hx
  have hlx := twenty_lt_log hxg
  have hly := twenty_lt_log (lt_of_lt_of_le ht0 hy)
  have hx0 : (0:ℝ) < x := by nlinarith [hxg]
  have hmono : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hP := C2JensenP_antitoneOn hα hαr hr1 ht0 hx hy hxy
  have h1 : hatAlpha r α * C2JensenP α r y ≤ hatAlpha r α * C2JensenP α r x :=
    mul_le_mul_of_nonneg_left hP hâ
  have hlxpos : (0:ℝ) < Real.log x := by linarith
  have h2 : Real.pi * B4 α r / Real.log y ≤ Real.pi * B4 α r / Real.log x := by
    gcongr
  have h3 : 3.35 * Real.pi / (rectDenom r α * y ^ ((1:ℝ)/3) * Real.log y)
      ≤ 3.35 * Real.pi / (rectDenom r α * x ^ ((1:ℝ)/3) * Real.log x) :=
    const_div_mul_rpow_mul_log_le (by positivity) (rectDenom_pos hα hαr) (by norm_num) hxg hxy
  simp only
  unfold C2JensenQ
  linarith

/-- **`C₂ᴶ`'s numerator, cleared of `1/h`:** `numerator · h = P(t)·h + Q(t)`.

### Summary of Proof
`field_simp` after unfolding `P` and `Q`: `(2 + 2α̂_r/h)·(bracket)·h = 2(bracket)h + 2α̂_r(bracket)`
and the two `1/h` terms lose their `h`.

### Lean Notes
`rectDenom r α ≠ 0`, `0 < t` and `log t ≠ 0` are needed only so `field_simp` may clear the
denominators; the identity is true regardless, by Lean's `x/0 = 0`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the `C_2^J` display at tex lines 213–215.

### Dependencies
**Depends on:** `C2JensenP`, `C2JensenQ`, `B1`, `B2`, `B3`, `B4`, `hatAlpha`, `rectDenom`.
**Used by:** `C2Jensen_eq_affine`. -/
theorem C2Jensen_num_mul {α r h t : ℝ} (hh : h ≠ 0) (hlog : Real.log t ≠ 0) (ht : 0 < t)
    (hD : rectDenom r α ≠ 0) :
    ((2 + 2 * hatAlpha r α / h) *
          (B1 α r + Real.pi * B2 α r * Real.log (Real.log t) / Real.log t
            + Real.pi * B3 α r / Real.log t)
        + Real.pi * B4 α r / (h * Real.log t)
        + 3.35 * Real.pi / (rectDenom r α * h * t ^ ((1 : ℝ) / 3) * Real.log t)) * h
      = C2JensenP α r t * h + C2JensenQ α r t := by
  have ht13 : t ^ ((1:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold C2JensenQ C2JensenP
  field_simp
  ring

/-- **`C₂ᴶ` in affine-over-affine form:**
`C₂ᴶ(α,r,h,t) = (P(t)·h + Q(t))/(S(t)·h - W(t))`.

### Summary of Proof
Multiply numerator and denominator by `h` (`div_eq_mul_div_mul_right`), then apply
`C2Jensen_num_mul` above and `C2denom_mul_eq_affine` below.

### Lean Notes
Exact, with no inequality anywhere. Both antitonicity halves rewrite through it.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the `C_2^J` display at tex lines 213–215 together
with the `h_0` display at tex line 209.

### Dependencies
**Depends on:** `C2Jensen`, `C2Jensen_num_mul`, `C2denom_mul_eq_affine`,
`div_eq_mul_div_mul_right`.
**Used by:** `C2Jensen_antitone_h`, `C2Jensen_antitone_t`. -/
theorem C2Jensen_eq_affine {α r h t : ℝ} (hh : h ≠ 0) (hlog : Real.log t ≠ 0) (ht : 0 < t)
    (hD : rectDenom r α ≠ 0) :
    C2Jensen α r h t
      = (C2JensenP α r t * h + C2JensenQ α r t) / (C2denomS t * h - C2denomW t) := by
  rw [← C2denom_mul_eq_affine h t hh hlog, ← C2Jensen_num_mul hh hlog ht hD]
  unfold C2Jensen
  exact div_eq_mul_div_mul_right hh

/-- **`C₂ᴶ` is decreasing in `h`** — the first half of `C2Jensen_antitone`.

### Summary of Proof
Clearing the `1/h`'s puts `C₂ᴶ` in the affine-over-affine shape
`C₂ᴶ(h) = (P·h + Q)/(S·h - W)` with

    P = 2(B₁ + πB₂ loglog t/log t + πB₃/log t),
    Q = 2α̂_r·(that bracket) + πB₄/log t + 3.35π/(D_{r,α} t^{1/3} log t),
    S = 1 - log(2π)/log t - (1-log 2)/(t^{2/3} log t),   W = 0.194π + 9.908π/log t,

and `affine_div_affine_antitoneOn` gives exactly this, on the domain `{h | 0 < S·h - W}` — which
is `h > W/S = h0Threshold t₀`, the set named here. Domain membership comes from
`C2denom_pos_of_h0Threshold_lt` transported through `C2denom_mul_eq_affine`; the required
`0 ≤ W` is free, since `W` carries the constant `0.194π`.

### Lean Notes
**Hypotheses `0 < α`, `α < r`, `r < 1` are not decoration.**
Without them the statement is *false*: `rectDenom r α` can be negative (e.g. `α = 1`, `r = -2`
gives `D ≈ -5.56`), which flips the signs of every `B_i` and turns `C₂ᴶ` into an increasing
function of `h`. They are the tex's own hypotheses on Corollary 4 (`r > α > 0`) together with the
`r < 1` that `\ref{thm:main-jensen}` (Theorem 2, `MainTheorem.mainJensen`) already carries.

The lemma applied is `affine_div_affine_antitoneOn`, not
`Definitions.affine_div_affine_strictAntiOn`: the latter needs `0 < P` strictly, whereas
`c1_nonneg`/`c2_nonneg` only give `≤`. `AntitoneOn` is all the corollary needs.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "decreasing in `h_0`" half of its claim, tex
lines 216 and 223.

### Dependencies
**Depends on:** `C2Jensen_eq_affine`, `affine_div_affine_antitoneOn`, `C2JensenP_nonneg`,
`C2JensenQ_nonneg`, `C2denomS_pos`, `C2denomW_pos`, `C2denom_pos_of_h0Threshold_lt`,
`C2denom_mul_eq_affine`, `h0Threshold_pos`, `rectDenom_pos`, `twenty_lt_log`.
**Used by:** `C2Jensen_antitone`. -/
theorem C2Jensen_antitone_h (α r : ℝ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) :
    AntitoneOn (fun h => C2Jensen α r h t0) (Set.Ioi (h0Threshold t0)) := by
  have ht0pos : (0:ℝ) < t0 := by nlinarith [ht0]
  have hlog := twenty_lt_log ht0
  have hlogne : Real.log t0 ≠ 0 := by linarith
  have hDne : rectDenom r α ≠ 0 := ne_of_gt (rectDenom_pos hα hαr)
  have hP := C2JensenP_nonneg hα hαr hr1 ht0
  have hQ := C2JensenQ_nonneg hα hαr hr1 ht0
  have hmain := affine_div_affine_antitoneOn hP hQ (C2denomS_pos ht0) (C2denomW_pos ht0).le
  intro a ha b hb hab
  have ha' : h0Threshold t0 < a := ha
  have hb' : h0Threshold t0 < b := hb
  have hapos : (0:ℝ) < a := (h0Threshold_pos ht0).trans ha'
  have hbpos : (0:ℝ) < b := (h0Threshold_pos ht0).trans hb'
  have hda : (0:ℝ) < C2denomS t0 * a - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine a t0 (ne_of_gt hapos) hlogne]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 ha') hapos
  have hdb : (0:ℝ) < C2denomS t0 * b - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine b t0 (ne_of_gt hbpos) hlogne]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 hb') hbpos
  simp only
  rw [C2Jensen_eq_affine (ne_of_gt hapos) hlogne ht0pos hDne,
    C2Jensen_eq_affine (ne_of_gt hbpos) hlogne ht0pos hDne]
  exact hmain hda hdb hab

/-- **`C₂ᴶ` is decreasing in `t`** — the second half of `C2Jensen_antitone`.

### Summary of Proof
The numerator's `t`-dependence is through `loglog t/log t`, `1/log t` and `1/(t^{1/3}log t)`, all
decreasing on this range, while the denominator `C2denom` increases towards `1`. A decreasing
non-negative numerator over an increasing positive denominator is decreasing.

The assembly is `div_antitoneOn_of_antitoneOn_of_monotoneOn` with numerator `P(t)·h + Q(t)`
(antitone by `C2JensenP_antitoneOn`/`C2JensenQ_antitoneOn`, non-negative by the corresponding
`_nonneg` lemmas) over denominator `S(t)·h - W(t)` (monotone by `C2denomAff_monotoneOn`).

### Lean Notes
Same three hypotheses beyond the tex as `C2Jensen_antitone_h`, for the same reason.

**Stated on the closed `Ici t₀`**, so that `mainPositiveProportionCorollary_jensen` can compare
`C₂` at its height `t` with `C₂` at the threshold `t₀` itself; every ingredient
(`C2denomAff_monotoneOn`, the `P`/`Q` antitonicity and non-negativity) lives on `Ici t₀`.

**Why the `loglog t/log t` term needs care.** It is only *eventually* decreasing (it rises up to
`t = e^e ≈ 15.15`), and Mathlib's nearest lemma is `Real.log_div_self_antitoneOn` — `log x / x`
antitone on `Ici (exp 1)`. Composing that with `Real.log` supplies the threshold, since
`log t > 20 > e` at `t > 10^12`. What it does *not* give on its own is the whole numerator,
because the `1/log t` terms sit beside it; the identity

    (a·log x + b)/x = (a/e)·(log(x/e)/(x/e)) + (a+b)/x

is what reduces the pair to that one Mathlib lemma, and is `log_affine_div_self_antitoneOn`.
It needs only `0 ≤ a` and `0 ≤ a + b` — deliberately not `0 ≤ b`, since the Littlewood analogue
has `b` of either sign.

**Positivity of the denominator away from `t₀`** is obtained by transporting
`0 < C2denom h t₀ · h` outwards along `C2denomAff_monotoneOn`, rather than by re-deriving it at
each `t`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "decreasing in `t_0`" half of its claim, tex
lines 216 and 223.

### Dependencies
**Depends on:** `C2Jensen_eq_affine`, `div_antitoneOn_of_antitoneOn_of_monotoneOn`,
`C2JensenP_antitoneOn`, `C2JensenQ_antitoneOn`, `C2JensenP_nonneg`, `C2JensenQ_nonneg`,
`C2denomAff_monotoneOn`, `C2denom_pos_of_h0Threshold_lt`, `C2denom_mul_eq_affine`,
`h0Threshold_pos`, `rectDenom_pos`, `twenty_lt_log`.
**Used by:** `C2Jensen_antitone`. -/
theorem C2Jensen_antitone_t (α r : ℝ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) :
    ∀ h, h0Threshold t0 < h → AntitoneOn (fun t => C2Jensen α r h t) (Set.Ici t0) := by
  intro h hh
  have hhpos : (0:ℝ) < h := (h0Threshold_pos ht0).trans hh
  have hlog0 := twenty_lt_log ht0
  have hlogne0 : Real.log t0 ≠ 0 := by linarith
  have hDne : rectDenom r α ≠ 0 := ne_of_gt (rectDenom_pos hα hαr)
  -- the denominator is positive on `Ici t₀`, by transport from `t₀` itself
  have hd0 : (0:ℝ) < C2denomS t0 * h - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine h t0 (ne_of_gt hhpos) hlogne0]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 hh) hhpos
  have hmonoAff := C2denomAff_monotoneOn hhpos ht0
  have hdpos : ∀ t ∈ Set.Ici t0, 0 < C2denomS t * h - C2denomW t := by
    intro t htm
    have htm' : t0 ≤ t := htm
    have := hmonoAff (Set.mem_Ici.mpr (le_refl t0)) htm htm'
    simp only at this
    linarith
  -- the numerator is antitone and non-negative on `Ici t₀`
  have hnum : AntitoneOn (fun t => C2JensenP α r t * h + C2JensenQ α r t) (Set.Ici t0) := by
    intro x hx y hy hxy
    have hxi : x ∈ Set.Ici t0 := hx
    have hyi : y ∈ Set.Ici t0 := hy
    have hPa := C2JensenP_antitoneOn hα hαr hr1 ht0 hxi hyi hxy
    have hQa := C2JensenQ_antitoneOn hα hαr hr1 ht0 hxi hyi hxy
    simp only at hPa hQa ⊢
    nlinarith [hPa, hQa, hhpos]
  have hnumnn : ∀ t ∈ Set.Ici t0, 0 ≤ C2JensenP α r t * h + C2JensenQ α r t := by
    intro t htm
    have htg : (10:ℝ) ^ (12:ℕ) < t := ht0.trans_le htm
    have hPn := C2JensenP_nonneg hα hαr hr1 htg
    have hQn := C2JensenQ_nonneg hα hαr hr1 htg
    nlinarith [hPn, hQn, hhpos]
  have hmain := div_antitoneOn_of_antitoneOn_of_monotoneOn hnum hnumnn hmonoAff hdpos
  intro x hx y hy hxy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := ht0.trans_le hx
  have hyg : (10:ℝ) ^ (12:ℕ) < y := ht0.trans_le hy
  have hx0 : (0:ℝ) < x := by nlinarith [hxg]
  have hy0 : (0:ℝ) < y := by nlinarith [hyg]
  have hlx : Real.log x ≠ 0 := by linarith [twenty_lt_log hxg]
  have hly : Real.log y ≠ 0 := by linarith [twenty_lt_log hyg]
  simp only
  rw [C2Jensen_eq_affine (ne_of_gt hhpos) hlx hx0 hDne,
    C2Jensen_eq_affine (ne_of_gt hhpos) hly hy0 hDne]
  exact hmain hx hy hxy

/-- **`C2Jensen` is decreasing in both `h` and `t`**, as Corollary `\ref{cor:main-jensen}` claims
("is decreasing in both `h₀` and `t₀` for any fixed `α` and `r`"). This is what lets the corollary
evaluate `C₂` at the *thresholds* `h₀, t₀` and have it bound the ratio for all larger `h, t`.

### Summary of Proof
The tex asserts it by inspection: "the right hand side is clearly decreasing in both `h` and `t`
provided the denominator is positive." This monotonicity is what lets the corollary evaluate `C₂`
at the *thresholds* `h₀, t₀` and have it bound the ratio for all larger `h, t`.

### Lean Notes
**Split into its two halves**, `C2Jensen_antitone_h` and `C2Jensen_antitone_t`; this theorem is
their conjunction. Note the two halves live on different sets: `Ioi (h0Threshold t₀)` in `h`, and
the closed `Ici t₀` in `t` so that the threshold height itself is admissible.

**`0 < α`, `α < r`, `r < 1` are hypotheses**, matching the tex's `r > α > 0` on Corollary 4
and the `r < 1` of `\ref{thm:main-jensen}` (Theorem 2). Without them the claim is false — see
`C2Jensen_antitone_h`'s Lean Notes.

The positivity side condition that both halves need, `C2denom > 0` on the domain, is
`C2denom_pos_of_h0Threshold_lt`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), the "is decreasing in both `h_0` and `t_0`" clause
(tex line 216) and the corresponding sentence in its proof (tex line 223).

### Dependencies
**Depends on:** `C2Jensen_antitone_h`, `C2Jensen_antitone_t`.
**Used by:** `mainPositiveProportionCorollary_jensen`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`. -/
theorem C2Jensen_antitone (α r : ℝ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) :
    AntitoneOn (fun h => C2Jensen α r h t0) (Set.Ioi (h0Threshold t0)) ∧
      ∀ h, h0Threshold t0 < h → AntitoneOn (fun t => C2Jensen α r h t) (Set.Ici t0) :=
  ⟨C2Jensen_antitone_h α r ht0 hα hαr hr1, C2Jensen_antitone_t α r ht0 hα hαr hr1⟩

/-! ## The Littlewood numerator in affine form

Exactly as on the Jensen side, `C₂ᴸ(α,r,h,t) = (P(t)·h + Q(t))/(S(t)·h - W(t))` with `S`, `W`
shared. The sign facts are harder here, and one of them is *false termwise*: `A₃` is a chord of
`v''`, which dips to `log(0.611) < 0` at `k = 0`, so `2πA₃/log t` on its own is **increasing** in
`t`. What holds is `A₂ + A₃ ≥ 0` (`neg_A2_le_A3`), which is exactly the hypothesis
`0 ≤ a + b` of `loglog_affine_div_log_antitoneOn`. See
`Code/verify_c3_and_chord_signs.py`, parts (3)–(5). -/

/-- **The `h`-coefficient of `C₂ᴸ`'s cleared numerator:**
`P(t) = 2A₁ + 2πA₂·loglog t/log t + 2πA₃/log t`.

### Summary of Proof
A definition; `C2Littlewood`'s numerator times `h`, keeping the terms with a surviving `h`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the `C_2^L` numerator at tex lines 233–235; the
`A_{i,α,r}` are from `\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** `A1`, `A2`, `A3`.
**Used by:** `C2LittlewoodP_eq`, `C2Littlewood_num_mul`, `C2Littlewood_eq_affine`,
`C2LittlewoodP_nonneg`, `C2LittlewoodP_antitoneOn`, `PositiveProportion.tendsto_C2LittlewoodP`,
`PositiveProportion.tendsto_C2LittlewoodP_div_C2denomS`,
`PositiveProportion.tendsto_C2Littlewood_h`. -/
noncomputable def C2LittlewoodP (α r t : ℝ) (k : ℤ) : ℝ :=
  2 * A1 α r k + 2 * Real.pi * A2 α r k * Real.log (Real.log t) / Real.log t
    + 2 * Real.pi * A3 α r k / Real.log t

/-- **The `h`-free part of `C₂ᴸ`'s cleared numerator:**
`Q(t) = 2A₄ + 2πA₅·loglog t/log t + πA₆/log t + π(0.335 + 0.51/log t)/((r-α)·t·log t)`.

### Summary of Proof
A definition. Independent of the chord index `k`, since `A₄`, `A₅`, `A₆` are.

### References
tex: as `C2LittlewoodP`.

### Dependencies
**Depends on:** `A4`, `A5`, `A6`.
**Used by:** `C2LittlewoodQ_antitoneOn`, `C2LittlewoodQ_eq`, `C2LittlewoodQ_nonneg`,
`C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`, `C2Littlewood_eq_affine`,
`C2Littlewood_num_mul`, `PositiveProportion.tendsto_C2Littlewood_h`. -/
noncomputable def C2LittlewoodQ (α r t : ℝ) : ℝ :=
  2 * A4 α r + 2 * Real.pi * A5 α r * Real.log (Real.log t) / Real.log t
    + Real.pi * A6 α r / Real.log t
    + Real.pi / ((r - α) * t * Real.log t) * (0.335 + 0.51 / Real.log t)

/-- **`P` over a common `log t`:** `P(t) = 2A₁ + (2πA₂·loglog t + 2πA₃)/log t`.

### Summary of Proof
`field_simp`.

### References
No tex counterpart — bookkeeping.

### Dependencies
**Depends on:** `C2LittlewoodP`.
**Used by:** `C2LittlewoodP_nonneg`, `C2LittlewoodP_antitoneOn`. -/
theorem C2LittlewoodP_eq {α r t : ℝ} {k : ℤ} (hlog : Real.log t ≠ 0) :
    C2LittlewoodP α r t k
      = 2 * A1 α r k
        + (2 * Real.pi * A2 α r k * Real.log (Real.log t) + 2 * Real.pi * A3 α r k)
            / Real.log t := by
  unfold C2LittlewoodP
  field_simp
  ring

/-- **`Q` over a common `log t`, error term aside:**
`Q(t) = 2A₄ + (2πA₅·loglog t + πA₆)/log t + (error)`.

### Summary of Proof
`field_simp`, leaving the `1/(t log t)` error term untouched.

### References
No tex counterpart — bookkeeping.

### Dependencies
**Depends on:** `C2LittlewoodQ`.
**Used by:** `C2LittlewoodQ_nonneg`, `C2LittlewoodQ_antitoneOn`. -/
theorem C2LittlewoodQ_eq {α r t : ℝ} (_hlog : Real.log t ≠ 0) :
    C2LittlewoodQ α r t
      = 2 * A4 α r
        + (2 * Real.pi * A5 α r * Real.log (Real.log t) + Real.pi * A6 α r) / Real.log t
        + Real.pi / ((r - α) * t * Real.log t) * (0.335 + 0.51 / Real.log t) := by
  unfold C2LittlewoodQ
  rw [add_div]
  ring_nf

/-- **The Littlewood error term is decreasing in `t`:**
`π/(d·t·log t)·(0.335 + 0.51/log t)` falls as `t` grows, for `d > 0` and `t > 10^12`.

### Summary of Proof
Both factors are non-negative and decreasing: `1/(t log t)` because `t` and `log t` both grow,
and `0.335 + 0.51/log t` because `log t` grows. `gcongr`.

### References
tex: the `O^*` term of `\ref{thm:main-littlewood}` (Theorem 3), tex line 185, after the
`(h log t)/π` normalisation.

### Dependencies
**Depends on:** `twenty_lt_log`.
**Used by:** `C2LittlewoodQ_antitoneOn`. -/
theorem littlewoodErr_le {d a b : ℝ} (hd : 0 < d) (ha : (10 : ℝ) ^ (12 : ℕ) < a) (hab : a ≤ b) :
    Real.pi / (d * b * Real.log b) * (0.335 + 0.51 / Real.log b)
      ≤ Real.pi / (d * a * Real.log a) * (0.335 + 0.51 / Real.log a) := by
  have ha0 : (0:ℝ) < a := by nlinarith [ha]
  have hb0 : (0:ℝ) < b := by linarith
  have hla := twenty_lt_log ha
  have hlb := twenty_lt_log (lt_of_lt_of_le ha hab)
  have hlapos : (0:ℝ) < Real.log a := by linarith
  have hlbpos : (0:ℝ) < Real.log b := by linarith
  have hmono : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hdena : (0:ℝ) < d * a * Real.log a := mul_pos (mul_pos hd ha0) hlapos
  have hdenb : (0:ℝ) < d * b * Real.log b := mul_pos (mul_pos hd hb0) hlbpos
  gcongr

/-- **The Littlewood error term is non-negative** for `α < r` and `t > 10^12`.

### Summary of Proof
`π > 0`, `(r-α)·t·log t > 0`, and `0.335 + 0.51/log t > 0`.

### References
tex: as `littlewoodErr_le`.

### Dependencies
**Depends on:** `twenty_lt_log`.
**Used by:** `C2LittlewoodQ_nonneg`. -/
theorem littlewoodErr_nonneg {α r t : ℝ} (hαr : α < r) (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    0 ≤ Real.pi / ((r - α) * t * Real.log t) * (0.335 + 0.51 / Real.log t) := by
  have ht0 : (0:ℝ) < t := by nlinarith [ht]
  have hlog := twenty_lt_log ht
  have hden : (0:ℝ) < (r - α) * t * Real.log t :=
    mul_pos (mul_pos (by linarith) ht0) (by linarith)
  have hfac : (0:ℝ) ≤ 0.335 + 0.51 / Real.log t :=
    by have : (0:ℝ) ≤ 0.51 / Real.log t := div_nonneg (by norm_num) (by linarith)
       linarith
  exact mul_nonneg (div_nonneg Real.pi_pos.le hden.le) hfac

/-- **`0 ≤ P(t)`** for `t > 10^12`, `0 < α < r < 1` and the pinned chord index.

### Summary of Proof
`2A₁ ≥ 0` (`A1_nonneg`) plus `loglog_affine_div_log_nonneg` at `a = 2πA₂ ≥ 0` and
`a + b = 2π(A₂ + A₃) ≥ 0` (`neg_A2_le_A3`).

### Lean Notes
`b = 2πA₃` alone may be negative; this is the place where the `a + b ≥ 0` form of the hypothesis
earns its keep.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `C2LittlewoodP_eq`, `A1_nonneg`, `A2_nonneg`, `neg_A2_le_A3`,
`loglog_affine_div_log_nonneg`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`. -/
theorem C2LittlewoodP_nonneg {α r t : ℝ} {k : ℤ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r ≤ sigma (k + 1)) (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    0 ≤ C2LittlewoodP α r t k := by
  have hlog := twenty_lt_log ht
  have h1 := A1_nonneg hαr hk hk'
  have h2 := A2_nonneg (k := k) hαr
  have h3 := neg_A2_le_A3 hα hαr hr1 hk hk'
  have ha : (0:ℝ) ≤ 2 * Real.pi * A2 α r k := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * A2 α r k + 2 * Real.pi * A3 α r k := by
    nlinarith [Real.pi_pos, h3]
  have := loglog_affine_div_log_nonneg ha hab ht
  rw [C2LittlewoodP_eq (by linarith : Real.log t ≠ 0)]
  linarith

/-- **`0 ≤ Q(t)`** for `t > 10^12` and `0 < α < r < 1`.

### Summary of Proof
`2A₄ ≥ 0` (`A4_nonneg`), then `loglog_affine_div_log_nonneg` at `a = 2πA₅ ≥ 0`, `b = πA₆ ≥ 0`,
then `littlewoodErr_nonneg`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `C2LittlewoodQ_eq`, `A4_nonneg`, `A5_nonneg`, `A6_nonneg`,
`loglog_affine_div_log_nonneg`, `littlewoodErr_nonneg`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`. -/
theorem C2LittlewoodQ_nonneg {α r t : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) : 0 ≤ C2LittlewoodQ α r t := by
  have hlog := twenty_lt_log ht
  have h4 := A4_nonneg (hα.trans hαr) hr1 hαr
  have h5 := A5_nonneg (hα.trans hαr) hαr
  have h6 := A6_nonneg hα hαr hr1
  have ha : (0:ℝ) ≤ 2 * Real.pi * A5 α r := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * A5 α r + Real.pi * A6 α r := by positivity
  have hmid := loglog_affine_div_log_nonneg ha hab ht
  have herr := littlewoodErr_nonneg (t := t) hαr ht
  rw [C2LittlewoodQ_eq (by linarith : Real.log t ≠ 0)]
  linarith

/-- **`P` is decreasing in `t`** on `Ici t₀`, for `t₀ > 10^12`, `0 < α < r < 1` and the pinned
chord index.

### Summary of Proof
`P(t) = 2A₁ + (2πA₂·loglog t + 2πA₃)/log t` with `2A₁` constant in `t`, then
`loglog_affine_div_log_antitoneOn` at `a = 2πA₂ ≥ 0`, `a + b = 2π(A₂+A₃) ≥ 0`.

### Lean Notes
The `t`-monotonicity here is genuine content rather than a termwise observation, and the argument
that supplies it is the `(a log x + b)/x` split of `log_affine_div_self_antitoneOn`, not a
derivative computation — `2πA₃/log t` alone is increasing when `A₃ < 0`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the "decreasing in `t_0`" claim.

### Dependencies
**Depends on:** `C2LittlewoodP_eq`, `A2_nonneg`, `neg_A2_le_A3`,
`loglog_affine_div_log_antitoneOn`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone_t`. -/
theorem C2LittlewoodP_antitoneOn {α r t0 : ℝ} {k : ℤ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r ≤ sigma (k + 1)) (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    AntitoneOn (fun t => C2LittlewoodP α r t k) (Set.Ici t0) := by
  have h2 := A2_nonneg (k := k) hαr
  have h3 := neg_A2_le_A3 hα hαr hr1 hk hk'
  have ha : (0:ℝ) ≤ 2 * Real.pi * A2 α r k := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * A2 α r k + 2 * Real.pi * A3 α r k := by
    nlinarith [Real.pi_pos, h3]
  intro x hx y hy hxy
  have hlx := twenty_lt_log (lt_of_lt_of_le ht0 hx)
  have hly := twenty_lt_log (lt_of_lt_of_le ht0 hy)
  have hstep := loglog_affine_div_log_antitoneOn ha hab ht0 hx hy hxy
  simp only
  rw [C2LittlewoodP_eq (k := k) (by linarith : Real.log x ≠ 0),
    C2LittlewoodP_eq (k := k) (by linarith : Real.log y ≠ 0)]
  simp only at hstep
  linarith

/-- **`Q` is decreasing in `t`** on `Ici t₀`, for `t₀ > 10^12` and `0 < α < r < 1`.

### Summary of Proof
`2A₄` is constant, the `loglog` block is `loglog_affine_div_log_antitoneOn` at `a = 2πA₅ ≥ 0`,
`b = πA₆ ≥ 0`, and the error term is `littlewoodErr_le`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the "decreasing in `t_0`" claim.

### Dependencies
**Depends on:** `C2LittlewoodQ_eq`, `A5_nonneg`, `A6_nonneg`,
`loglog_affine_div_log_antitoneOn`, `littlewoodErr_le`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone_t`. -/
theorem C2LittlewoodQ_antitoneOn {α r t0 : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) :
    AntitoneOn (fun t => C2LittlewoodQ α r t) (Set.Ici t0) := by
  have h5 := A5_nonneg (hα.trans hαr) hαr
  have h6 := A6_nonneg hα hαr hr1
  have ha : (0:ℝ) ≤ 2 * Real.pi * A5 α r := by positivity
  have hab : (0:ℝ) ≤ 2 * Real.pi * A5 α r + Real.pi * A6 α r := by positivity
  intro x hx y hy hxy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := lt_of_lt_of_le ht0 hx
  have hlx := twenty_lt_log hxg
  have hly := twenty_lt_log (lt_of_lt_of_le ht0 hy)
  have hstep := loglog_affine_div_log_antitoneOn ha hab ht0 hx hy hxy
  have herr := littlewoodErr_le (d := r - α) (by linarith) hxg hxy
  simp only
  rw [C2LittlewoodQ_eq (by linarith : Real.log x ≠ 0),
    C2LittlewoodQ_eq (by linarith : Real.log y ≠ 0)]
  simp only at hstep
  linarith

/-- **`C₂ᴸ`'s numerator, cleared of `1/h`:** `numerator · h = P(t)·h + Q(t)`.

### Summary of Proof
`field_simp` after unfolding `P` and `Q`.

### Lean Notes
`α ≠ r`, `t ≠ 0` and `log t ≠ 0` are needed only to clear denominators.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the `C_2^L` display at tex lines 233–235.

### Dependencies
**Depends on:** `C2LittlewoodP`, `C2LittlewoodQ`, `A1`, `A2`, `A3`, `A4`, `A5`, `A6`.
**Used by:** `C2Littlewood_eq_affine`. -/
theorem C2Littlewood_num_mul {α r h t : ℝ} {k : ℤ} (hh : h ≠ 0) (hlog : Real.log t ≠ 0)
    (ht : t ≠ 0) (hrα : r - α ≠ 0) :
    (2 * A1 α r k + 2 * A4 α r / h
        + Real.pi * (2 * A2 α r k + 2 * A5 α r / h) * Real.log (Real.log t) / Real.log t
        + 2 * Real.pi * A3 α r k / Real.log t
        + Real.pi * A6 α r / (h * Real.log t)
        + Real.pi / ((r - α) * h * t * Real.log t) * (0.335 + 0.51 / Real.log t)) * h
      = C2LittlewoodP α r t k * h + C2LittlewoodQ α r t := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold C2LittlewoodP C2LittlewoodQ
  field_simp
  ring

/-- **`C₂ᴸ` in affine-over-affine form:**
`C₂ᴸ(α,r,h,t,k) = (P(t)·h + Q(t))/(S(t)·h - W(t))`.

### Summary of Proof
As `C2Jensen_eq_affine`: multiply through by `h` and apply `C2Littlewood_num_mul` and
`C2denom_mul_eq_affine`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), tex lines 233–235 with the `h_0` display at tex
line 229.

### Dependencies
**Depends on:** `C2Littlewood`, `C2Littlewood_num_mul`, `C2denom_mul_eq_affine`,
`div_eq_mul_div_mul_right`.
**Used by:** `C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`,
`PositiveProportion.tendsto_C2Littlewood_h` — which uses it for a purpose beyond monotonicity, to
read off `C₂ᴸ → P(t)/S(t)` as `h → ∞` and hence the positivity of Corollary 1's constant. -/
theorem C2Littlewood_eq_affine {α r h t : ℝ} {k : ℤ} (hh : h ≠ 0) (hlog : Real.log t ≠ 0)
    (ht : t ≠ 0) (hrα : r - α ≠ 0) :
    C2Littlewood α r h t k
      = (C2LittlewoodP α r t k * h + C2LittlewoodQ α r t) / (C2denomS t * h - C2denomW t) := by
  rw [← C2denom_mul_eq_affine h t hh hlog, ← C2Littlewood_num_mul hh hlog ht hrα]
  unfold C2Littlewood
  exact div_eq_mul_div_mul_right hh

/-- **`C₂ᴸ` is decreasing in `h`** — the first half of `C2Littlewood_antitone`.

### Summary of Proof
As `C2Jensen_antitone_h`: clearing the `1/h`'s gives the affine-over-affine shape
`(P·h + Q)/(S·h - W)` with `P = 2A₁ + 2πA₂ loglog t/log t + 2πA₃/log t`,
`Q = 2A₄ + 2πA₅ loglog t/log t + πA₆/log t + π(0.335 + 0.51/log t)/((r-α)t log t)`, and the same
`S`, `W` as the Jensen case (the denominator `C2denom` is shared). Then
`affine_div_affine_antitoneOn` applies on `h > W/S = h0Threshold t₀`.

### Lean Notes
**Five hypotheses beyond the tex's display.** `0 < α`, `α < r`, `r < 1` for the same reason as on
the Jensen side (without them the `A_i` signs are unconstrained and the claim is false), plus the
chord-index conditions `σ_k ≤ 1-r` and `1-r ≤ σ_{k+1}` (the latter non-strict here, where the
corollary states `<`). The chord conditions are the `hk`/`hk'` that
`mainPositiveProportionCorollary_littlewood` already carries: without pinning `k`, `A₁` and `A₃`
are values of unrelated chords and nothing constrains their sign.

**The sign inputs.** `A₁`, `A₂`, `A₄`, `A₅` are non-negative (`A1_nonneg` via
`chord_vCoeff_nonneg`, `A2_nonneg` via `A2_eq`, `A4_nonneg` via `c1_nonneg`, `A5_nonneg` via
`c2_nonneg`); `A6_nonneg` additionally needs `1 ≤ ‖ζ(σ)‖` for real `σ > 1`, `0 ≤ c_{4,r}`,
`0 ≤ Φ(σ).re` and `c3_nonneg`. For `A₃` there is no sign: `0 ≤ A₃` is **false** (`A₃` is a chord
of `v''`, which dips to `log(0.611) < 0` at `k = 0`), and what holds is `-A₂ ≤ A₃`
(`neg_A2_le_A3`), i.e. the chord value is at least `-1`. Checked numerically in
`Code/verify_c3_and_chord_signs.py`, part (3). `A₂ = 1/(2π(r-α)) > 0` for every `k` (`A2_eq`,
`vCoeffP` being identically `1`), and it is precisely that `A₂ loglog t` term which keeps `P`
non-negative where `A₃` is negative.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the "decreasing in `h_0`" half of its claim, tex
line 236.

### Dependencies
**Depends on:** `C2Littlewood_eq_affine`, `affine_div_affine_antitoneOn`, `C2LittlewoodP_nonneg`,
`C2LittlewoodQ_nonneg`, `C2denomS_pos`, `C2denomW_pos`, `C2denom_pos_of_h0Threshold_lt`,
`C2denom_mul_eq_affine`, `h0Threshold_pos`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone`. -/
theorem C2Littlewood_antitone_h (α r : ℝ) (k : ℤ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r ≤ sigma (k + 1)) :
    AntitoneOn (fun h => C2Littlewood α r h t0 k) (Set.Ioi (h0Threshold t0)) := by
  have ht0pos : (0:ℝ) < t0 := by nlinarith [ht0]
  have hlog := twenty_lt_log ht0
  have hlogne : Real.log t0 ≠ 0 := by linarith
  have hrαne : r - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hαr)
  have hP := C2LittlewoodP_nonneg hα hαr hr1 hk hk' ht0
  have hQ := C2LittlewoodQ_nonneg hα hαr hr1 ht0
  have hmain := affine_div_affine_antitoneOn hP hQ (C2denomS_pos ht0) (C2denomW_pos ht0).le
  intro a ha b hb hab
  have ha' : h0Threshold t0 < a := ha
  have hb' : h0Threshold t0 < b := hb
  have hapos : (0:ℝ) < a := (h0Threshold_pos ht0).trans ha'
  have hbpos : (0:ℝ) < b := (h0Threshold_pos ht0).trans hb'
  have hda : (0:ℝ) < C2denomS t0 * a - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine a t0 (ne_of_gt hapos) hlogne]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 ha') hapos
  have hdb : (0:ℝ) < C2denomS t0 * b - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine b t0 (ne_of_gt hbpos) hlogne]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 hb') hbpos
  simp only
  rw [C2Littlewood_eq_affine (ne_of_gt hapos) hlogne (ne_of_gt ht0pos) hrαne,
    C2Littlewood_eq_affine (ne_of_gt hbpos) hlogne (ne_of_gt ht0pos) hrαne]
  exact hmain hda hdb hab

/-- **`C₂ᴸ` is decreasing in `t`** — the second half of `C2Littlewood_antitone`.

### Summary of Proof
As `C2Jensen_antitone_t`: numerator decreasing in `t` through `loglog t/log t`, `1/log t` and
`1/(t log t)`, denominator increasing towards `1`.

### Lean Notes
Same five hypotheses beyond the tex's display as `C2Littlewood_antitone_h`.

**Stated on the closed `Ici t₀`**, as `C2Jensen_antitone_t`, so that
`mainPositiveProportionCorollary_littlewood` can compare `C₂` at its height `t` with `C₂` at the
threshold `t₀` itself.

**The numerator is not termwise antitone here**, unlike the Jensen side. `A₃` can be negative, so
`2πA₃/log t` is *increasing* in `t`. What is antitone is the pair
`(2πA₂·loglog t + 2πA₃)/log t` taken together, via `log_affine_div_self_antitoneOn`, whose
hypothesis is `0 ≤ a` and `0 ≤ a + b` — here `A₂ ≥ 0` and `A₂ + A₃ ≥ 0`. Concretely
`A₂ + A₃ = (1 + m''_k(1-r) + b''_k)/(2π(r-α))` and the chord of `v''` is bounded below by
`log(0.611) ≈ -0.49 > -1`. See `Code/verify_c3_and_chord_signs.py`, parts (3)–(5).

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the "decreasing in `t_0`" half of its claim, tex
line 236.

### Dependencies
**Depends on:** `C2Littlewood_eq_affine`, `div_antitoneOn_of_antitoneOn_of_monotoneOn`,
`C2LittlewoodP_antitoneOn`, `C2LittlewoodQ_antitoneOn`, `C2LittlewoodP_nonneg`,
`C2LittlewoodQ_nonneg`, `C2denomAff_monotoneOn`, `C2denom_pos_of_h0Threshold_lt`,
`C2denom_mul_eq_affine`, `h0Threshold_pos`, `twenty_lt_log`.
**Used by:** `C2Littlewood_antitone`. -/
theorem C2Littlewood_antitone_t (α r : ℝ) (k : ℤ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r ≤ sigma (k + 1)) :
    ∀ h, h0Threshold t0 < h → AntitoneOn (fun t => C2Littlewood α r h t k) (Set.Ici t0) := by
  intro h hh
  have hhpos : (0:ℝ) < h := (h0Threshold_pos ht0).trans hh
  have hlog0 := twenty_lt_log ht0
  have hlogne0 : Real.log t0 ≠ 0 := by linarith
  have hrαne : r - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hαr)
  have hd0 : (0:ℝ) < C2denomS t0 * h - C2denomW t0 := by
    rw [← C2denom_mul_eq_affine h t0 (ne_of_gt hhpos) hlogne0]
    exact mul_pos (C2denom_pos_of_h0Threshold_lt ht0 hh) hhpos
  have hmonoAff := C2denomAff_monotoneOn hhpos ht0
  have hdpos : ∀ t ∈ Set.Ici t0, 0 < C2denomS t * h - C2denomW t := by
    intro t htm
    have htm' : t0 ≤ t := htm
    have := hmonoAff (Set.mem_Ici.mpr (le_refl t0)) htm htm'
    simp only at this
    linarith
  have hnum :
      AntitoneOn (fun t => C2LittlewoodP α r t k * h + C2LittlewoodQ α r t) (Set.Ici t0) := by
    intro x hx y hy hxy
    have hxi : x ∈ Set.Ici t0 := hx
    have hyi : y ∈ Set.Ici t0 := hy
    have hPa := C2LittlewoodP_antitoneOn hα hαr hr1 hk hk' ht0 hxi hyi hxy
    have hQa := C2LittlewoodQ_antitoneOn hα hαr hr1 ht0 hxi hyi hxy
    simp only at hPa hQa ⊢
    nlinarith [hPa, hQa, hhpos]
  have hnumnn : ∀ t ∈ Set.Ici t0, 0 ≤ C2LittlewoodP α r t k * h + C2LittlewoodQ α r t := by
    intro t htm
    have htg : (10:ℝ) ^ (12:ℕ) < t := ht0.trans_le htm
    have hPn := C2LittlewoodP_nonneg hα hαr hr1 hk hk' htg
    have hQn := C2LittlewoodQ_nonneg hα hαr hr1 htg
    nlinarith [hPn, hQn, hhpos]
  have hmain := div_antitoneOn_of_antitoneOn_of_monotoneOn hnum hnumnn hmonoAff hdpos
  intro x hx y hy hxy
  have hxg : (10:ℝ) ^ (12:ℕ) < x := ht0.trans_le hx
  have hyg : (10:ℝ) ^ (12:ℕ) < y := ht0.trans_le hy
  have hx0 : (0:ℝ) < x := by nlinarith [hxg]
  have hy0 : (0:ℝ) < y := by nlinarith [hyg]
  have hlx : Real.log x ≠ 0 := by linarith [twenty_lt_log hxg]
  have hly : Real.log y ≠ 0 := by linarith [twenty_lt_log hyg]
  simp only
  rw [C2Littlewood_eq_affine (ne_of_gt hhpos) hlx (ne_of_gt hx0) hrαne,
    C2Littlewood_eq_affine (ne_of_gt hhpos) hly (ne_of_gt hy0) hrαne]
  exact hmain hx hy hxy

/-- **The Littlewood analogue of `C2Jensen_antitone`**, for `Corollary \ref{cor:main-littlewood}`
(Corollary 5)'s "is decreasing in both `h₀` and `t₀`" claim.

### Summary of Proof
As for `C2Jensen_antitone`: the tex asserts monotonicity by inspection, the numerator being
decreasing in `h` and `t` while the denominator increases, given positivity of the latter.

### Lean Notes
**Split into `C2Littlewood_antitone_h` and `C2Littlewood_antitone_t`**, as on the Jensen side;
this theorem is their conjunction, the `h`-half on `Ioi (h0Threshold t₀)` and the `t`-half on the
closed `Ici t₀`.

**Five hypotheses beyond the tex's display**: `0 < α`, `α < r`, `r < 1` and the chord-index pair
`σ_k ≤ 1-r ≤ σ_{k+1}` (non-strict on the right here, where the corollary states `<`), all of
which `mainPositiveProportionCorollary_littlewood` supplies. Without them the claim is false.

The sign side conditions are harder on this side than on the Jensen one: `A₁`, `A₂`, `A₄`, `A₅`
are non-negative outright, `A₆` needs `1 ≤ ‖ζ(σ)‖` for real `σ > 1`, and `A₃` has no sign at all
— the usable statement is `-A₂ ≤ A₃`. See `C2Littlewood_antitone_h`'s Lean Notes.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), the "is decreasing in both `h_0` and `t_0`"
clause, tex line 236.

### Dependencies
**Depends on:** `C2Littlewood_antitone_h`, `C2Littlewood_antitone_t`.
**Used by:** `mainPositiveProportionCorollary_littlewood`,
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`. -/
theorem C2Littlewood_antitone (α r : ℝ) (k : ℤ) {t0 : ℝ} (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0)
    (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r ≤ sigma (k + 1)) :
    AntitoneOn (fun h => C2Littlewood α r h t0 k) (Set.Ioi (h0Threshold t0)) ∧
      ∀ h, h0Threshold t0 < h → AntitoneOn (fun t => C2Littlewood α r h t k) (Set.Ici t0) :=
  ⟨C2Littlewood_antitone_h α r k ht0 hα hαr hr1 hk hk',
    C2Littlewood_antitone_t α r k ht0 hα hαr hr1 hk hk'⟩

/-- **`h0Threshold` is decreasing in `t`**: `h0Threshold t = W(t)/S(t)` with `W` decreasing and `S`
increasing and positive for `t > 10^12`.

### Summary of Proof
`h0Threshold_eq_div` at both points, then `C2denomW_le`, `C2denomS_le`, `C2denomS_pos` and
`div_le_div₀`.

### Lean Notes
Needed by the corollaries: their `h₀` clears the threshold at `t₀`, while positivity of the
denominator at the larger height `t` (`C2denom_pos_of_h0Threshold_lt`) needs `h0Threshold t < h`.

### References
tex: the `h₀` threshold display of `\ref{cor:main-jensen}` (Corollary 4), tex line 209.

### Dependencies
**Depends on:** `h0Threshold_eq_div`, `C2denomW_le`, `C2denomS_le`, `C2denomS_pos`,
`twenty_lt_log`.
**Used by:** `mainPositiveProportionCorollary_jensen`,
`mainPositiveProportionCorollary_littlewood`, and in `HalvingConvention` their half-counted forms
together with `simpleProportionCorollary_*_mul` and `simpleProportionCorollary_*_prose`. -/
theorem h0Threshold_antitone {a b : ℝ} (ha : (10 : ℝ) ^ (12 : ℕ) < a) (hab : a ≤ b) :
    h0Threshold b ≤ h0Threshold a := by
  have hb : (10 : ℝ) ^ (12 : ℕ) < b := lt_of_lt_of_le ha hab
  rw [h0Threshold_eq_div ha, h0Threshold_eq_div hb]
  have hla : (0 : ℝ) < Real.log a := by linarith [twenty_lt_log ha]
  have hWa : 0 ≤ C2denomW a := by
    unfold C2denomW
    have hpi := Real.pi_pos
    have h1 : (0 : ℝ) ≤ 0.194 * Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 9.908 * Real.pi / Real.log a := div_nonneg (by positivity) hla.le
    linarith
  exact div_le_div₀ hWa (C2denomW_le ha hab) (C2denomS_pos ha) (C2denomS_le ha hab)

/-- **Corollary `\ref{cor:main-jensen}` (Jensen).** For `r > α > 0` with `α < 1/6` (and `r < 1`,
as in Theorem 2), `t₀ > 10^12` and `h₀` above the admissibility threshold, for all `t > t₀` and
`t^{2/3} > h > h₀`: `Nrect(t-h,t+h,α) / (N(t+h) - N(t-h)) < C_2^J(α,r,h₀,t₀)`.

### Summary of Proof
The tex's proof, in three steps:

1. `Nrect/(N(t+h)-N(t-h)) < U_J(α,r,h,t)/L(h,t)`: `Theorem \ref{thm:main-jensen}` (Theorem 2,
   `mainJensen`) bounds the numerator, `Lbound_le_N_sub_N` (Bellotti–Wong) bounds the
   denominator below by `L(h,t)`, which is positive by `C2denom_mul_le_Lbound` once
   `C2denom h t > 0` (`C2denom_pos_of_h0Threshold_lt`);
2. `U_J/L ≤ C_2^J(α,r,h,t)` by the normalisation `Ubound_jensen_div_Lbound_le_C2Jensen`;
3. `C_2^J(α,r,h,t) ≤ C_2^J(α,r,h₀,t) ≤ C_2^J(α,r,h₀,t₀)` by `C2Jensen_antitone` — first in `h` at
   the height `t`, then in `t` at the width `h₀`.

### Lean Notes
**`hht : h < t^{2/3}`** is the tex's own range ("for all `t > t₀` and `t^{2/3} > h > h₀`") and is
required: the `h > t^{2/3}` regime is not covered, exactly as it is not covered by Theorem 2, and
the classical zero-density route to it fails numerically at these thresholds
(`Code/verify_kln_large_h_case.py`, Part 3a). `MainTheorem.Nrect_le_zero_density_bound` records
what that route does give.

Side conditions: `h0Threshold t < h` at the height `t` is `h0Threshold_antitone` (the threshold
decreases in `t`); `1 ≤ t-h` follows from `h < t^{2/3} ≤ t/10000` (`rpow_two_thirds_le_div`);
`e ≤ t` from `t > 10^12`. `C₂` is evaluated at the *thresholds* `h₀,t₀`, not at `h,t` — that is
what `C2Jensen_antitone` is for, and why the corollary can quote a single number; its `t`-half is
stated on `Ici t₀` so that `t₀` itself is admissible.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), tex lines 207–225. Consumes `\ref{thm:main-jensen}`
(Theorem 2) and the `L(h,t)` bound at tex line 203.

### Dependencies
**Depends on:** `C2Jensen`, `h0Threshold`, `h0Threshold_antitone`, `h0Threshold_pos`, `Nrect`,
`N`, `mainJensen`, `Ubound_jensen`, `Lbound`, `Lbound_le_N_sub_N`,
`C2denom_pos_of_h0Threshold_lt`, `C2denom_mul_le_Lbound`, `Ubound_jensen_div_Lbound_le_C2Jensen`,
`C2Jensen_antitone`, `rpow_two_thirds_le_div`, `twenty_lt_log`.
**Used by:** none — this is a headline result. -/
theorem mainPositiveProportionCorollary_jensen {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    (Nrect (t - h) (t + h) α : ℝ) / (N (t + h) - N (t - h)) < C2Jensen α r h0 t0 := by
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have h12 : ((10 : ℝ) ^ (12 : ℕ)) = 1000000000000 := by norm_num
  have ht12' : (1000000000000 : ℝ) < t := by rw [← h12]; exact ht12
  have hthr0 : h0Threshold t ≤ h0Threshold t0 := h0Threshold_antitone ht0 ht.le
  have hthr : h0Threshold t < h := lt_of_le_of_lt hthr0 (hh0.trans hh)
  have hhpos : 0 < h := (h0Threshold_pos ht12).trans hthr
  have hh23 : h ≤ t ^ ((2 : ℝ) / 3) := hht.le
  have hth1 : 1 ≤ t - h := by
    have := rpow_two_thirds_le_div ht12
    linarith
  have hte : Real.exp 1 ≤ t := by
    have := Real.exp_one_lt_d9
    linarith
  -- Theorem 2
  have hmain : (Nrect (t - h) (t + h) α : ℝ) < Ubound_jensen α r h t :=
    mainJensen hα0 hrα hr1 (by unfold alphaBoundTodo; exact hα) hte hhpos.le hh23
  -- the denominator is positive and bounds `N(t+h) - N(t-h)` below
  have hden : 0 < C2denom h t := C2denom_pos_of_h0Threshold_lt ht12 hthr
  have hlog : (20 : ℝ) < Real.log t := twenty_lt_log ht12
  have hK : 0 < h * Real.log t / Real.pi := div_pos (mul_pos hhpos (by linarith)) Real.pi_pos
  have hL : 0 < Lbound h t :=
    lt_of_lt_of_le (mul_pos hden hK) (C2denom_mul_le_Lbound ht12 hhpos hh23)
  have hNsub : Lbound h t ≤ (N (t + h) : ℝ) - N (t - h) := Lbound_le_N_sub_N hhpos hth1
  have hN0 : (0 : ℝ) ≤ (Nrect (t - h) (t + h) α : ℝ) := by
    exact_mod_cast Nrect_nonneg (by linarith : (0 : ℝ) < t - h)
  have hUnn : 0 ≤ Ubound_jensen α r h t := le_trans hN0 hmain.le
  -- the chain
  calc (Nrect (t - h) (t + h) α : ℝ) / (N (t + h) - N (t - h))
      ≤ (Nrect (t - h) (t + h) α : ℝ) / Lbound h t := div_le_div_of_nonneg_left hN0 hL hNsub
    _ < Ubound_jensen α r h t / Lbound h t := div_lt_div_of_pos_right hmain hL
    _ ≤ C2Jensen α r h t := Ubound_jensen_div_Lbound_le_C2Jensen ht12 hhpos hh23 hden hL hUnn
    _ ≤ C2Jensen α r h0 t :=
        (C2Jensen_antitone α r ht12 hα0 hrα hr1).1 (Set.mem_Ioi.mpr (lt_of_le_of_lt hthr0 hh0))
          (Set.mem_Ioi.mpr hthr) hh.le
    _ ≤ C2Jensen α r h0 t0 :=
        (C2Jensen_antitone α r ht0 hα0 hrα hr1).2 h0 hh0 (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr ht.le) ht.le

/-- **Corollary `\ref{cor:main-littlewood}` (Littlewood).** Same shape as
`mainPositiveProportionCorollary_jensen`, with `C_2^L` in place of `C_2^J`: for `r > α > 0`
with `α < 1/6`, the chord index `k` with `σ_k ≤ 1-r < σ_{k+1}`, `t₀ > 10^12` and `h₀` above the
admissibility threshold, for all `t > t₀` and `t^{2/3} > h > h₀`,
`Nrect(t-h,t+h,α) / (N(t+h) - N(t-h)) < C_2^L(α,r,h₀,t₀)`.

### Summary of Proof
The tex's proof reads in full: "The proof is the same as the above" — i.e. exactly
`mainPositiveProportionCorollary_jensen`'s three-step chain (Theorem 3 and the `L` bound, then
the normalisation `Ubound_littlewood_div_Lbound_le_C2Littlewood`, then `C2Littlewood_antitone`),
with `U_L`/`C_2^L` in place of `U_J`/`C_2^J`.

### Lean Notes
**`hht : h < t^{2/3}`** is the tex's own range, as in the Jensen corollary; the `h > t^{2/3}`
regime is the worst of the four results numerically
(`Code/verify_kln_large_h_case.py`, Part 3b) and is not claimed. `r < 1` is not assumed but
follows from `hk` (`sigma_pos`).

**`hzf_p`/`hzf_m`** are inherited from `MainTheorem.mainLittlewood` (Theorem 3): no zero of `ζ`
on the two horizontal edges `Im s = t ± h`, `Re s ∈ [1-r, 1+ηr]`, which is the tex's first
`arg ζ` case. The half-counted form with no edge hypothesis is
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`. No hypothesis on `arg ζ` is
needed: `argZeta` is the tex's constructed branch (`LittlewoodMethod.argZetaDef`).

The tex states this corollary with `α < 1/6`, and so does its underlying
`Theorem \ref{thm:main-littlewood}` (Theorem 3); that is reproduced faithfully here. The
Littlewood mechanism itself needs no bound on `α` beyond `α < r`
(`MainTheoremTight.mainLittlewoodTight` asks only `α < 1/2`). `e^e ≤ t` is supplied from
`t > 10^12` via `e^e < e^3 < 27`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), tex lines 227–241. Consumes
`\ref{thm:main-littlewood}` (Theorem 3) and the `L(h,t)` bound at tex line 203.

### Dependencies
**Depends on:** `C2Littlewood`, `h0Threshold`, `h0Threshold_antitone`, `h0Threshold_pos`, `Nrect`,
`N`, `sigma`, `sigma_pos`, `argZeta`, `eta`, `mainLittlewood`, `Ubound_littlewood`, `Lbound`,
`Lbound_le_N_sub_N`, `C2denom_pos_of_h0Threshold_lt`, `C2denom_mul_le_Lbound`,
`Ubound_littlewood_div_Lbound_le_C2Littlewood`, `C2Littlewood_antitone`, `rpow_two_thirds_le_div`,
`twenty_lt_log`.
**Used by:** none — this is a headline result. -/
theorem mainPositiveProportionCorollary_littlewood {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t - h) * Complex.I) ≠ 0) :
    (Nrect (t - h) (t + h) α : ℝ) / (N (t + h) - N (t - h)) < C2Littlewood α r h0 t0 k := by
  have hr1 : r < 1 := by linarith [sigma_pos k, hk]
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have h12 : ((10 : ℝ) ^ (12 : ℕ)) = 1000000000000 := by norm_num
  have ht12' : (1000000000000 : ℝ) < t := by rw [← h12]; exact ht12
  have hthr0 : h0Threshold t ≤ h0Threshold t0 := h0Threshold_antitone ht0 ht.le
  have hthr : h0Threshold t < h := lt_of_le_of_lt hthr0 (hh0.trans hh)
  have hhpos : 0 < h := (h0Threshold_pos ht12).trans hthr
  have hh23 : h ≤ t ^ ((2 : ℝ) / 3) := hht.le
  have hth1 : 1 ≤ t - h := by
    have := rpow_two_thirds_le_div ht12
    linarith
  have htee : Real.exp (Real.exp 1) ≤ t := by
    have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he1
    have h27 : Real.exp 3 < 27 := by
      have := pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
      rw [Real.exp_one_pow] at this
      norm_num at this
      linarith
    linarith
  -- Theorem 3
  have hmain : (Nrect (t - h) (t + h) α : ℝ) < Ubound_littlewood α r h t k :=
    mainLittlewood hα0 hrα hα hk hk' htee hhpos.le hh23 hzf_p hzf_m
  -- the denominator is positive and bounds `N(t+h) - N(t-h)` below
  have hden : 0 < C2denom h t := C2denom_pos_of_h0Threshold_lt ht12 hthr
  have hlog : (20 : ℝ) < Real.log t := twenty_lt_log ht12
  have hK : 0 < h * Real.log t / Real.pi := div_pos (mul_pos hhpos (by linarith)) Real.pi_pos
  have hL : 0 < Lbound h t :=
    lt_of_lt_of_le (mul_pos hden hK) (C2denom_mul_le_Lbound ht12 hhpos hh23)
  have hNsub : Lbound h t ≤ (N (t + h) : ℝ) - N (t - h) := Lbound_le_N_sub_N hhpos hth1
  have hN0 : (0 : ℝ) ≤ (Nrect (t - h) (t + h) α : ℝ) := by
    exact_mod_cast Nrect_nonneg (by linarith : (0 : ℝ) < t - h)
  have hUnn : 0 ≤ Ubound_littlewood α r h t k := le_trans hN0 hmain.le
  -- the chain
  calc (Nrect (t - h) (t + h) α : ℝ) / (N (t + h) - N (t - h))
      ≤ (Nrect (t - h) (t + h) α : ℝ) / Lbound h t := div_le_div_of_nonneg_left hN0 hL hNsub
    _ < Ubound_littlewood α r h t k / Lbound h t := div_lt_div_of_pos_right hmain hL
    _ ≤ C2Littlewood α r h t k :=
        Ubound_littlewood_div_Lbound_le_C2Littlewood ht12 hhpos hh23 hrα hden hL hUnn
    _ ≤ C2Littlewood α r h0 t k :=
        (C2Littlewood_antitone α r k ht12 hα0 hrα hr1 hk hk'.le).1
          (Set.mem_Ioi.mpr (lt_of_le_of_lt hthr0 hh0)) (Set.mem_Ioi.mpr hthr) hh.le
    _ ≤ C2Littlewood α r h0 t0 k :=
        (C2Littlewood_antitone α r k ht0 hα0 hrα hr1 hk hk'.le).2 h0 hh0 (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr ht.le) ht.le
