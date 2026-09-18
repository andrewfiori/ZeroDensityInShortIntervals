/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib

/-! # Core definitions for "Zero Density Theorems for Short Intervals"

This file collects the basic definitions from `ZerosInShortIntervals.tex`
(A. Fiori, *Zero Density Theorems for Short Intervals*) that are used throughout the
`ZerosInShortIntervals` development. No hypothesis-class section variable is declared here, so every
statement in this file is unconditional.

We count zeros of `riemannZeta` with multiplicity using the divisor `MeromorphicOn.divisor` from
`Mathlib.Analysis.Meromorphic.Divisor` (the same object that drives Mathlib's Jensen's formula,
`Mathlib.Analysis.Complex.JensenFormula`). For a set `U` on which `riemannZeta` is (automatically)
meromorphic, `∑ᶠ u, MeromorphicOn.divisor riemannZeta U u` is the number of zeros of `ζ` in `U`
counted with multiplicity, offset by the order of any pole of `ζ` lying in `U`. The only pole is
`s = 1`, whose imaginary part is `0`, so every region below that carries a positive lower bound on
`Im s` is pole-free and the sum is a genuine zero count (`Nrect_nonneg`, `NlineRe_nonneg`).
`Ncirc`, by contrast, is defined for an arbitrary closed ball and so carries no such guarantee by
construction.

### Zero-counting functions
- `N T`: the number of zeros `ρ` of `ζ` with `0 < Im ρ ≤ T`.
- `Ncirc s α`: the number of zeros `ρ` of `ζ` with `|ρ - s| ≤ α`, i.e. `N(s,α)` in the source.
- `Nrect T₁ T₂ α`: the number of zeros `ρ` of `ζ` with `T₁ < Im ρ ≤ T₂` and `Re ρ > 1 - α` — the
  half-open window, top edge included and bottom edge excluded, in which the whole development
  and the registry submission are stated.
- `NlineRe T α`: the zeros on the single horizontal line `Im ρ = T` with `Re ρ > 1 - α`.
- `Nhalf T₁ T₂ α`: the source's own `N(T₁,T₂,α)`, which counts a zero on either horizontal edge
  of the closed window `T₁ ≤ Im ρ ≤ T₂` with half its multiplicity.
- `zetaOrd u`: the order of vanishing of `ζ` at `u`, the pointwise summand behind all of these.

### Other recurring quantities
- `Phi`: the function `Φ(s) = ∑_{n>1} Λ(n)/(log n)² n^{-s}` of Equation `\ref{eq:phis}`
  (Equation 12), an antiderivative of `-log ζ(s)`.
- `hatAlpha`: `α̂_r = √(r² - α²)` from Equation `\ref{eq:hatalpha}` (Equation 10).
- `eta`: the constant `η ∈ (0,1)` solving `1 + η + log η = 0` from Equation `\ref{eq:eta}`
  (Equation 15).
- `stieltjesConstant1`: the first Stieltjes constant `γ₁`, together with the convergence proof and
  the explicit two-sided bracketing that make numerical claims about it provable.
-/

open scoped ArithmeticFunction

/-- **`N T` is the number of zeros `ρ` of `ζ` (with multiplicity) satisfying `0 < Im ρ ≤ T`.**

### Summary of Proof
A definition: the sum of the divisor of `ζ` over the half-strip `{0 < Im s ≤ T}`. This is `N(T)`
in the introduction of the source.

### References
tex: the definition of `N(T)` in the introduction (page 1).

### Dependencies
**Depends on:** none.
**Used by:** `Hypotheses.LiteratureInputs.bellotti_wong_cor_1_3`,
`ExternalFacts.bellotti_wong_cor_1_3`, `MainCorollary.Lbound_le_N_sub_N`, and
`HalvingConvention.N_sub_N_eq_Nrect_one`. -/
noncomputable def N (T : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.im ∧ s.im ≤ T} u

/-- **`Ncirc s α` is the number of zeros `ρ` of `ζ` (with multiplicity) satisfying `|ρ - s| ≤ α`.**

### Summary of Proof
A definition: the sum of the divisor of `ζ` over `Metric.closedBall s α`, the *closed* disc of
radius `α` about `s`. This is `N(s,α)` in the introduction of the source.

### References
tex: the definition of `N(s,α)` in the introduction (page 1).

### Dependencies
**Depends on:** none.
**Used by:** `Ncirc_nonneg`, `circularregions1`, `circularregions1_tight`, `circularregions2`,
`jensenbound`, `log_norm_le_jensenCircleAvg`. -/
noncomputable def Ncirc (s : ℂ) (α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u

/-- **`Nrect T₁ T₂ α` is the number of zeros `ρ` of `ζ` (with multiplicity) satisfying
`T₁ < Im ρ ≤ T₂` and `Re ρ > 1 - α`.**

### Summary of Proof
A definition: the sum of the divisor of `ζ` over the half-open window `{T₁ < Im s ≤ T₂}` cut by
the open half-plane `{Re s > 1 - α}`. The window is half-open on purpose — the top edge counts in
full, the bottom edge not at all — which makes `Nrect` additive in the height range
(`Nrect_add_split`). This is the unhalved variant of the source's `N(T₁,T₂,α)`; the source's own
half-multiplicity convention for edge zeros is `Nhalf`, and the two agree whenever both edges are
zero-free (`Nhalf_eq_Nrect_of_forall_ne_zero`). Every statement of the development and of the
registry submission is phrased with `Nrect`.

### References
tex: the definition of `N(T₁,T₂,α)` in the introduction (page 1).

### Dependencies
**Depends on:** none.
**Used by:** `Nrect_mono`, `Nrect_nonneg`, `Nhalf`, `Nrect_add_split`, `two_mul_Nhalf_eq`,
`Nsigma`, `jensenrectangle`, `littlewoodshort`,
`littlewoodshort_tight`, `mainJensen`, `mainJensenTight`, `mainLittlewood`, `mainLittlewoodTight`,
`mainPositiveProportionCorollary_jensen`, `mainPositiveProportionCorollary_littlewood`,
`rectangularjensen`, `rectangularjensen_tight`, `simplelittlewoodzerodensity`. -/
noncomputable def Nrect (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} u

/-- **Shared helper for `Nrect_divisor_support_finite`/`Nrect_mono`/`Nrect_nonneg`.** `ζ` is
analytic on any half-strip `{T₁ < Im s ≤ T₂, γ < Re s}` with `T₁ > 0`, since such a strip never
contains `ζ`'s only pole `s = 1` (which has `Im = 0`).

### Summary of Proof
`ζ` is analytic everywhere except its simple pole at `s = 1`. The half-strip
`{T₁ < Im s ≤ T₂, γ < Re s}` with `0 < T₁` has every point of positive imaginary part, so
it excludes `1` (which is real); hence `ζ` is analytic on a neighbourhood of the whole
region. Shared by `Nrect_divisor_support_finite`, `Nrect_mono` and `Nrect_nonneg`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `Nrect_divisor_support_finite`, `Nrect_mono`, `Nrect_nonneg`. -/
theorem analyticOnNhd_riemannZeta_rect {T1 T2 γ : ℝ} (hT1 : 0 < T1) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ γ < s.re} := by
  apply analyticOn_riemannZeta.mono
  intro x hx hx1
  have hx1' : x = (1 : ℂ) := hx1
  subst hx1'
  have h := hx.1
  rw [Complex.one_im] at h
  linarith

/-- **Helper for `Nrect_mono`.** The divisor of `ζ` on the half-strip `{T₁ < Im s ≤ T₂, γ < Re s}`
has finite support, even though the strip itself is unbounded (`Re s` ranges over `(γ,∞)`).

### Summary of Proof
Every zero of `ζ` in the strip must in fact satisfy `Re s ≤ 1`
(`riemannZeta_ne_zero_of_one_lt_re`), so the (a priori unbounded) strip's zero set coincides with
that of the *compact* rectangle `{γ ≤ Re s ≤ 1, T₁ ≤ Im s ≤ T₂}`, which is finite by Mathlib's
`IsCompact.inter_riemannZetaZeros_finite`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `analyticOnNhd_riemannZeta_rect`.
**Used by:** `Nrect_add_split`, `Nrect_mono`, `HalvingConvention.N_sub_N_eq_Nrect_one`. -/
theorem Nrect_divisor_support_finite {T1 T2 γ : ℝ} (hT1 : 0 < T1) :
    (Function.support (fun u => MeromorphicOn.divisor riemannZeta
      {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ γ < s.re} u)).Finite := by
  set U : Set ℂ := {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ γ < s.re} with hU_def
  set K : Set ℂ := Set.Icc γ 1 ×ℂ Set.Icc T1 T2 with hK_def
  have hKcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  have hanalytic : AnalyticOnNhd ℂ riemannZeta U := analyticOnNhd_riemannZeta_rect hT1
  have hsub : Function.support (fun u => MeromorphicOn.divisor riemannZeta U u)
      ⊆ K ∩ riemannZetaZeros := by
    intro u hu
    simp only [Function.mem_support] at hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic huU] at hu
    have hzero : riemannZeta u = 0 := by
      by_contra hne
      rw [(hanalytic u huU).analyticOrderAt_eq_zero.mpr hne] at hu
      simp at hu
    have hre1 : u.re ≤ 1 := by
      by_contra hgt
      exact riemannZeta_ne_zero_of_one_lt_re (not_le.mp hgt) hzero
    exact ⟨Complex.mem_reProdIm.mpr ⟨⟨huU.2.2.le, hre1⟩, huU.1.le, huU.2.1⟩, hzero⟩
  exact (hKcompact.inter_riemannZetaZeros_finite).subset hsub

/-- **`Nrect T₁ T₂` is monotone nondecreasing in `α`.**

### Summary of Proof
As `α` grows the threshold `1-α` shrinks, widening the region `{Re s > 1-α}` that `Nrect` counts,
so at least as many zeros fall inside it. Formally the divisor sum is over a larger set, and every
summand is nonnegative because `0 < T₁` keeps `ζ`'s pole at `1` (which has `Im = 0`) out of the
region — `analyticOnNhd_riemannZeta_rect` — while
`Nrect_divisor_support_finite` makes the sum finite.

### References
tex: no direct counterpart; it supports the counting conventions behind Equation
`\ref{eq:zerodensityintegral}` (Equation 13).

### Dependencies
**Depends on:** `Nrect`, `Nrect_divisor_support_finite`, `analyticOnNhd_riemannZeta_rect`.
**Used by:** `LittlewoodIdentity.littlewood_identity_argZetaDef`,
`LittlewoodIdentity.simplelittlewoodzerodensity`. -/
theorem Nrect_mono {T1 T2 α β : ℝ} (hT1 : 0 < T1) (hαβ : α ≤ β) :
    Nrect T1 T2 α ≤ Nrect T1 T2 β := by
  have hsub : {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - α < s.re}
      ⊆ {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - β < s.re} :=
    fun s hs => ⟨hs.1, hs.2.1, lt_of_le_of_lt (by linarith) hs.2.2⟩
  have hanalytic :
      ∀ γ : ℝ, AnalyticOnNhd ℂ riemannZeta {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ γ < s.re} :=
    fun γ => analyticOnNhd_riemannZeta_rect hT1
  refine finsum_le_finsum' (Nrect_divisor_support_finite hT1) (Nrect_divisor_support_finite hT1)
    fun u => ?_
  by_cases huα : u ∈ {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - α < s.re}
  · have huβ : u ∈ {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - β < s.re} := hsub huα
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hanalytic (1 - α)) huα,
      MeromorphicOn.AnalyticOnNhd.divisor_apply (hanalytic (1 - β)) huβ]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huα]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hanalytic (1 - β)) u

/-- **`Nrect T₁ T₂ γ` is nonnegative whenever `0 < T₁`** (which again excludes `ζ`'s pole from the
region, so the value is a genuine zero *count*, with no pole order to subtract).

### Summary of Proof
`Nrect` is a sum of divisor orders over a region on which `ζ` is analytic — the `0 < T₁`
hypothesis excludes the pole, via `analyticOnNhd_riemannZeta_rect`. On an analytic
function every divisor order is a genuine zero multiplicity, hence nonnegative, so the
sum is too: there is no pole order to cancel against.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Nrect`, `analyticOnNhd_riemannZeta_rect`.
**Used by:** `HalvingConvention.Nhalf_nonneg`, `HalvingConvention.Nrect_inner_le_Nhalf`,
`MainCorollary.mainPositiveProportionCorollary_jensen`,
`MainCorollary.mainPositiveProportionCorollary_littlewood`,
`LittlewoodIdentity.simplelittlewoodzerodensity`. -/
theorem Nrect_nonneg {T1 T2 γ : ℝ} (hT1 : 0 < T1) : 0 ≤ Nrect T1 T2 γ :=
  finsum_nonneg fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (analyticOnNhd_riemannZeta_rect hT1) u

/-! ### The halving convention: zeros on the horizontal edges

The tex (page 1) counts a zero **on** the boundary of the window `T₁ ≤ Im ρ ≤ T₂` with half its
multiplicity.  `Nrect` counts `T₁ < Im ρ ≤ T₂` without halving; the two agree exactly when no zero
lies on either horizontal edge, which is what every Littlewood-side statement assumes through
`hzf_p`/`hzf_m`.  This section supplies the
half-counted count `Nhalf` and the one identity that turns each main theorem into its
half-counted form (`HalvingConvention.lean`):

  `2 · Nhalf T₁ T₂ α = Nrect (T₁-ε) (T₂+ε) α + Nrect (T₁+ε) (T₂-ε) α`

for every `ε > 0` smaller than the gap between `T₁`, `T₂` and the nearest other zero ordinate
(`two_mul_Nhalf_eq`; the gap exists by `exists_gap_ordinates`, since a compact rectangle holds
finitely many zeros).  The outer window counts every edge zero fully, the inner one not at all,
and the main theorems apply to both because the right-hand sides `U_J`, `U_L` are affine in `h`.
Everything rests on writing `Nrect` as a finite sum of the pointwise order `zetaOrd` over a
region (`divisor_riemannZeta_eq_ite`) so that windows can be split (`Nrect_add_split`) and
zero-free strips dropped (`Nrect_eq_zero_of_forall_ne_zero`, `Nrect_eq_NlineRe_of_forall_ne_zero`).
-/

/-- **The order of vanishing of `ζ` at `u`, as an integer**: `0` where `ζ` does not vanish, and
also `0` at the pole `s = 1`.

### Summary of Proof
A definition, `((analyticOrderAt ζ u).map (↑)).untop₀` — exactly the value Mathlib's
`MeromorphicOn.AnalyticOnNhd.divisor_apply` assigns to the divisor at a point of analyticity,
which is what makes `divisor_riemannZeta_eq_ite` hold on the nose.

### Lean Notes
`analyticOrderAt` lands in `ℕ∞` and `untop₀` sends its top element to `0`. Both degenerate
branches are harmless here. The order is `⊤` only when the function vanishes identically near
`u`, which `ζ` never does, so `untop₀` costs nothing. At the pole `u = 1` the order is not `⊤`
but `0`: by `analyticOrderAt_eq_zero` the order vanishes as soon as the function fails to be
analytic at the point. So `zetaOrd 1 = 0`, and no pole order is ever subtracted from a count.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `divisor_riemannZeta_eq_ite`, `zetaOrd_nonneg`, `zetaOrd_eq_zero_of_ne_zero`. -/
noncomputable def zetaOrd (u : ℂ) : ℤ :=
  ((analyticOrderAt riemannZeta u).map ((↑) : ℕ → ℤ)).untop₀

/-- **`0 ≤ zetaOrd u`.**

### Summary of Proof
Case split on the analytic order (`⊤` gives `0`, `n` gives `n ≥ 0`).

### Dependencies
**Depends on:** `zetaOrd`.
**Used by:** none yet (the divisor form `MeromorphicOn.AnalyticOnNhd.divisor_nonneg` is used
instead). -/
theorem zetaOrd_nonneg (u : ℂ) : 0 ≤ zetaOrd u := by
  unfold zetaOrd
  cases h : analyticOrderAt riemannZeta u with
  | top => simp
  | coe n => simp

/-- **`zetaOrd u = 0` where `ζ u ≠ 0`.**

### Summary of Proof
`analyticOrderAt_eq_zero` (the order is `0` iff `f` is not analytic or `f u ≠ 0`).

### Dependencies
**Depends on:** `zetaOrd`.
**Used by:** `NlineRe_eq_zero_of_forall_ne_zero`, `Nrect_eq_NlineRe_of_forall_ne_zero`,
`Nrect_eq_zero_of_forall_ne_zero`, `HalvingConvention.N_divisor_support_finite`,
`Reflection.NlineRe_one_eq_add`, `Reflection.Nrect_one_eq_add`,
`HalvingConvention.zetaOrd_eq_zero_of_im_pos_of_re_nonpos`. -/
theorem zetaOrd_eq_zero_of_ne_zero {u : ℂ} (hu : riemannZeta u ≠ 0) : zetaOrd u = 0 := by
  unfold zetaOrd
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hu)]
  simp

open Classical in
/-- **The divisor of `ζ` on a region of analyticity is the indicator of the region times
`zetaOrd`.**

### Summary of Proof
`MeromorphicOn.AnalyticOnNhd.divisor_apply` inside the region,
`Function.locallyFinsuppWithin.apply_eq_zero_of_notMem` outside.

### Lean Notes
This is the form in which all the counting identities below are proved: two `finsum`s of
divisors over different regions are compared pointwise through their indicators.

### Dependencies
**Depends on:** `zetaOrd`.
**Used by:** `Nrect_add_split`, `Nrect_eq_zero_of_forall_ne_zero`,
`Nrect_eq_NlineRe_of_forall_ne_zero`, `NlineRe_eq_zero_of_forall_ne_zero`. -/
theorem divisor_riemannZeta_eq_ite {U : Set ℂ} (hU : AnalyticOnNhd ℂ riemannZeta U) (u : ℂ) :
    MeromorphicOn.divisor riemannZeta U u = if u ∈ U then zetaOrd u else 0 := by
  by_cases hu : u ∈ U
  · rw [ite_eq_left hu, MeromorphicOn.AnalyticOnNhd.divisor_apply hU hu]; rfl
  · rw [ite_eq_right hu]; exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

/-- **`ζ` is analytic on any set of points with positive imaginary part** (the pole `s = 1` is
real).

### Summary of Proof
As `analyticOnNhd_riemannZeta_rect`: `analyticOn_riemannZeta.mono`, the only excluded point being
`1`, whose imaginary part is `0`.

### Dependencies
**Depends on:** none.
**Used by:** `analyticOnNhd_riemannZeta_line`, `HalvingConvention.N_divisor_support_finite`,
`HalvingConvention.N_sub_N_eq_Nrect_one`, `Reflection.analyticOnNhd_riemannZeta_lineLeft`,
`Reflection.analyticOnNhd_riemannZeta_lineMid`, `Reflection.analyticOnNhd_riemannZeta_rectLeft`,
`Reflection.analyticOnNhd_riemannZeta_rectMid`. -/
theorem analyticOnNhd_riemannZeta_of_im_pos {U : Set ℂ} (hU : ∀ s ∈ U, 0 < s.im) :
    AnalyticOnNhd ℂ riemannZeta U := by
  apply analyticOn_riemannZeta.mono
  intro x hx hx1
  have hx1' : x = (1 : ℂ) := hx1
  subst hx1'
  have := hU 1 hx
  rw [Complex.one_im] at this
  linarith

/-- **`NlineRe T α` is the number of zeros `ρ` of `ζ` (with multiplicity) ON the horizontal line
`Im ρ = T` with `Re ρ > 1 - α`.**

### Summary of Proof
Definition, with the same divisor as `Nrect`.

### References
tex: page 1, the half-multiplicity convention for boundary zeros.

### Dependencies
**Depends on:** none.
**Used by:** `Nhalf`, `Nrect_eq_NlineRe_of_forall_ne_zero`, `NlineRe_eq_zero_of_forall_ne_zero`,
`NlineRe_nonneg`. -/
noncomputable def NlineRe (T α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ 1 - α < s.re} u

/-- **`Nhalf T₁ T₂ α` is the tex's `N(T₁,T₂,α)`: zeros with `T₁ ≤ Im ρ ≤ T₂`, `Re ρ > 1 - α`,
with multiplicity, those on the two edges counting with half their multiplicity.**

### Summary of Proof
Definition: `Nrect T₁ T₂ α - NlineRe T₂ α / 2 + NlineRe T₁ α / 2` (the interior zeros plus half of
each edge; `Nrect` already contains the top edge fully and the bottom edge not at all).  It is
real-valued (half-integers).

### Lean Notes
Equal to `Nrect` when both edges are zero-free (`Nhalf_eq_Nrect_of_forall_ne_zero`), which is the
situation of every `hzf_p`/`hzf_m`-carrying statement in the project.

### References
tex: page 1, the counting convention; `\ref{thm:main-jensen}` (Theorem 2),
`\ref{thm:main-littlewood}` (Theorem 3).

### Dependencies
**Depends on:** `Nrect`, `NlineRe`.
**Used by:** `two_mul_Nhalf_eq`, `Nhalf_eq_Nrect_of_forall_ne_zero`,
`HalvingConvention.mainJensenHalf`, `HalvingConvention.mainLittlewoodHalf`. -/
noncomputable def Nhalf (T₁ T₂ α : ℝ) : ℝ :=
  (Nrect T₁ T₂ α : ℝ) - (NlineRe T₂ α : ℝ) / 2 + (NlineRe T₁ α : ℝ) / 2

/-- **`ζ` is analytic on the half-line `{Im s = T, γ < Re s}` for `T > 0`.**

### Summary of Proof
`analyticOnNhd_riemannZeta_of_im_pos`.

### Dependencies
**Depends on:** `analyticOnNhd_riemannZeta_of_im_pos`.
**Used by:** `NlineRe_eq_zero_of_forall_ne_zero`, `NlineRe_nonneg`,
`Nrect_eq_NlineRe_of_forall_ne_zero`, `Reflection.NlineReLeft_eq_NlineRe`,
`Reflection.NlineRe_one_eq_add`. -/
theorem analyticOnNhd_riemannZeta_line {T γ : ℝ} (hT : 0 < T) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.im = T ∧ γ < s.re} :=
  analyticOnNhd_riemannZeta_of_im_pos (fun s hs => by rw [hs.1]; exact hT)

/-- **Additivity of `Nrect` over a split of the imaginary range:**
`Nrect T₁ T₃ α = Nrect T₁ T₂ α + Nrect T₂ T₃ α` for `0 < T₁ ≤ T₂ ≤ T₃`.

### Summary of Proof
`finsum_add_distrib` (both supports are finite, `Nrect_divisor_support_finite`) and a pointwise
case analysis on `Im u` through `divisor_riemannZeta_eq_ite`: the strip `(T₁, T₃]` is the disjoint
union of `(T₁, T₂]` and `(T₂, T₃]`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Nrect`, `Nrect_divisor_support_finite`, `analyticOnNhd_riemannZeta_rect`,
`divisor_riemannZeta_eq_ite`.
**Used by:** `two_mul_Nhalf_eq`, `HalvingConvention.Nrect_inner_le_Nhalf`. -/
theorem Nrect_add_split {T1 T2 T3 α : ℝ} (hT1 : 0 < T1) (h12 : T1 ≤ T2) (h23 : T2 ≤ T3) :
    Nrect T1 T3 α = Nrect T1 T2 α + Nrect T2 T3 α := by
  have hT2 : 0 < T2 := lt_of_lt_of_le hT1 h12
  unfold Nrect
  rw [← finsum_add_distrib (Nrect_divisor_support_finite (T2 := T2) (γ := 1 - α) hT1)
    (Nrect_divisor_support_finite (T1 := T2) (T2 := T3) (γ := 1 - α) hT2)]
  apply finsum_congr
  intro u
  rw [divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_rect (T2 := T3) (γ := 1 - α) hT1),
    divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_rect (T2 := T2) (γ := 1 - α) hT1),
    divisor_riemannZeta_eq_ite
      (analyticOnNhd_riemannZeta_rect (T1 := T2) (T2 := T3) (γ := 1 - α) hT2)]
  simp only [Set.mem_ofPred_eq]
  by_cases hre : 1 - α < u.re
  · by_cases hlo : T1 < u.im
    · by_cases hmid : u.im ≤ T2
      · have h3 : u.im ≤ T3 := hmid.trans h23
        have hn : ¬ T2 < u.im := not_lt.mpr hmid
        simp [hre, hlo, hmid, h3, hn]
      · by_cases hhi : u.im ≤ T3
        · have : T2 < u.im := not_le.mp hmid
          simp [hre, hlo, hmid, hhi, this]
        · simp [hre, hlo, hmid, hhi]
    · have : ¬ T2 < u.im := fun h => hlo (lt_of_le_of_lt h12 h)
      simp [hlo, this]
  · simp [hre]

/-- **`Nrect T₁ T₂ α = 0` when the strip `T₁ < Im s ≤ T₂`, `Re s > 1 - α` is zero-free.**

### Summary of Proof
Every term of the `finsum` vanishes: `divisor_riemannZeta_eq_ite` and `zetaOrd_eq_zero_of_ne_zero`.

### Dependencies
**Depends on:** `Nrect`, `divisor_riemannZeta_eq_ite`, `zetaOrd_eq_zero_of_ne_zero`,
`analyticOnNhd_riemannZeta_rect`.
**Used by:** `two_mul_Nhalf_eq`. -/
theorem Nrect_eq_zero_of_forall_ne_zero {T1 T2 α : ℝ} (hT1 : 0 < T1)
    (hzf : ∀ s : ℂ, T1 < s.im → s.im ≤ T2 → 1 - α < s.re → riemannZeta s ≠ 0) :
    Nrect T1 T2 α = 0 := by
  unfold Nrect
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  rw [divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_rect (T2 := T2) (γ := 1 - α) hT1)]
  split_ifs with hu
  · exact zetaOrd_eq_zero_of_ne_zero (hzf u hu.1 hu.2.1 hu.2.2)
  · rfl

/-- **A strip `(T-ε, T]` whose open part is zero-free counts exactly the zeros on its top edge:**
`Nrect (T-ε) T α = NlineRe T α`.

### Summary of Proof
Pointwise through `divisor_riemannZeta_eq_ite`: on the line `Im u = T` both indicators agree; on
the open strip the order is `0` (`zetaOrd_eq_zero_of_ne_zero`); elsewhere both sides vanish.

### Dependencies
**Depends on:** `Nrect`, `NlineRe`, `divisor_riemannZeta_eq_ite`, `zetaOrd_eq_zero_of_ne_zero`,
`analyticOnNhd_riemannZeta_rect`, `analyticOnNhd_riemannZeta_line`.
**Used by:** `two_mul_Nhalf_eq`. -/
theorem Nrect_eq_NlineRe_of_forall_ne_zero {T ε α : ℝ} (hT : 0 < T - ε) (hε : 0 < ε)
    (hzf : ∀ s : ℂ, T - ε < s.im → s.im < T → 1 - α < s.re → riemannZeta s ≠ 0) :
    Nrect (T - ε) T α = NlineRe T α := by
  have hT0 : 0 < T := by linarith
  unfold Nrect NlineRe
  apply finsum_congr
  intro u
  rw [divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_rect (T2 := T) (γ := 1 - α) hT),
    divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_line (γ := 1 - α) hT0)]
  simp only [Set.mem_ofPred_eq]
  by_cases hre : 1 - α < u.re
  · by_cases heq : u.im = T
    · simp [heq, hre, hε]
    · have hne : ¬ (u.im = T ∧ 1 - α < u.re) := fun h => heq h.1
      rw [ite_eq_right hne]
      split_ifs with hu
      · exact zetaOrd_eq_zero_of_ne_zero (hzf u hu.1 (lt_of_le_of_ne hu.2.1 heq) hre)
      · rfl
  · simp [hre]

/-- **`NlineRe T α = 0` when the edge `Im s = T`, `Re s > 1 - α` is zero-free** — the form in which
the project's `hzf_p`/`hzf_m` hypotheses are stated.

### Summary of Proof
Pointwise: a point of the line is `↑(Re u) + ↑T · I` (`Complex.re_add_im`), where `ζ ≠ 0` by
hypothesis, so `zetaOrd` vanishes.

### Dependencies
**Depends on:** `NlineRe`, `divisor_riemannZeta_eq_ite`, `zetaOrd_eq_zero_of_ne_zero`,
`analyticOnNhd_riemannZeta_line`.
**Used by:** `Nhalf_eq_Nrect_of_forall_ne_zero`. -/
theorem NlineRe_eq_zero_of_forall_ne_zero {T α : ℝ} (hT : 0 < T)
    (hzf : ∀ x : ℝ, 1 - α < x → riemannZeta (x + T * Complex.I) ≠ 0) : NlineRe T α = 0 := by
  unfold NlineRe
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  rw [divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_line (γ := 1 - α) hT)]
  split_ifs with hu
  · apply zetaOrd_eq_zero_of_ne_zero
    have : u = (u.re : ℂ) + (T : ℂ) * Complex.I := by
      rw [← hu.1]; exact (Complex.re_add_im u).symm
    rw [this]; exact hzf u.re hu.2
  · rfl

/-- **`0 ≤ NlineRe T α` for `T > 0`.**

### Summary of Proof
As `Nrect_nonneg`: a sum of divisor orders of an analytic function.

### Dependencies
**Depends on:** `NlineRe`, `analyticOnNhd_riemannZeta_line`.
**Used by:** none yet. -/
theorem NlineRe_nonneg {T α : ℝ} (hT : 0 < T) : 0 ≤ NlineRe T α :=
  finsum_nonneg fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (analyticOnNhd_riemannZeta_line (γ := 1 - α) hT) u

/-- **The zero ordinates are isolated:** for every height `T` and abscissa `γ` there is `ε₀ > 0`
such that every zero `ρ` of `ζ` with `Re ρ ≥ γ` and `|Im ρ - T| < ε₀` lies exactly on `Im ρ = T`.

### Summary of Proof
The zeros in the compact rectangle `[γ, 1] × [T-1, T+1]` are finitely many
(`IsCompact.inter_riemannZetaZeros_finite`; every zero has `Re ρ ≤ 1` by
`riemannZeta_ne_zero_of_one_le_re`).  Their ordinates other than `T` form a finite, hence closed,
set not containing `T`, so some ball about `T` misses it (`Metric.isOpen_iff` on the complement);
take `ε₀ = min` of that radius and `1`.

### Lean Notes
Stated with `γ ≤ Re ρ` (closed) so that the same `ε₀` serves both the counting sets
`Re > 1 - α` of `Nrect` and the closed edge segments `[1 - r, 1 + ηr]` of the `hzf_*` hypotheses
(take `γ = 1 - r ≤ 1 - α`).

### References
tex: no direct counterpart; this is what makes the `ε → 0` limit of the remark following Equation
`\ref{eq:zerodensityintegral}` (Equation 13) — the definition of `arg f` on a horizontal line
through a zero, compatible with the halving convention — available at every height.

### Dependencies
**Depends on:** none.
**Used by:** `HalvingConvention.exists_window_eps`. -/
theorem exists_gap_ordinates (T γ : ℝ) :
    ∃ ε0 > 0, ∀ s : ℂ, riemannZeta s = 0 → γ ≤ s.re → |s.im - T| < ε0 → s.im = T := by
  set K : Set ℂ := Set.Icc γ 1 ×ℂ Set.Icc (T - 1) (T + 1) with hK
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  have hfin : (K ∩ riemannZetaZeros).Finite := hKc.inter_riemannZetaZeros_finite
  set F : Set ℝ := ((fun s : ℂ => s.im) '' (K ∩ riemannZetaZeros)) \ {T} with hF
  have hFfin : F.Finite := (hfin.image _).sdiff
  have hFclosed : IsClosed F := hFfin.isClosed
  have hTnot : T ∈ Fᶜ := fun h => h.2 rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hFclosed.isOpen_compl T hTnot
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro s hs hre him
  have him1 : |s.im - T| < 1 := lt_of_lt_of_le him (min_le_right _ _)
  have himδ : |s.im - T| < δ := lt_of_lt_of_le him (min_le_left _ _)
  have hre1 : s.re ≤ 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_le.mp h).le hs
  have hsK : s ∈ K := by
    rw [hK, Complex.mem_reProdIm]
    refine ⟨⟨hre, hre1⟩, ?_⟩
    rw [abs_lt] at him1
    exact ⟨by linarith, by linarith⟩
  have hmem : s.im ∈ (fun s : ℂ => s.im) '' (K ∩ riemannZetaZeros) :=
    ⟨s, ⟨hsK, mem_riemannZetaZeros.mpr hs⟩, rfl⟩
  by_contra hne
  have hF' : s.im ∈ F := ⟨hmem, hne⟩
  have : s.im ∈ Metric.ball T δ := by rw [Metric.mem_ball, Real.dist_eq]; exact himδ
  exact hball this hF'

/-- **The halving identity:** for `ε > 0` below the gap to the nearest other zero ordinate at
both edges, `2 · Nhalf T₁ T₂ α = Nrect (T₁-ε) (T₂+ε) α + Nrect (T₁+ε) (T₂-ε) α`.

### Summary of Proof
Split the outer window as `(T₁-ε, T₁] ∪ (T₁, T₂] ∪ (T₂, T₂+ε]` and the inner one out of
`(T₁, T₂] = (T₁, T₁+ε] ∪ (T₁+ε, T₂-ε] ∪ (T₂-ε, T₂]` (`Nrect_add_split`).  By the gap hypotheses
the strips `(T₁-ε, T₁]` and `(T₂-ε, T₂]` count exactly the edge zeros
(`Nrect_eq_NlineRe_of_forall_ne_zero`) and the strips `(T₁, T₁+ε]`, `(T₂, T₂+ε]` count nothing
(`Nrect_eq_zero_of_forall_ne_zero`).  So the outer window is `NlineRe T₁ + Nrect T₁ T₂` and the
inner one `Nrect T₁ T₂ - NlineRe T₂`; their sum is `2 · Nhalf` by definition.

### Lean Notes
The gap hypotheses are taken non-strict (`|Im s - Tᵢ| ≤ ε`) because the outer strips are
half-open at distance exactly `ε`; `HalvingConvention.exists_window_eps` supplies them with room
to spare (`ε` at most half the gap radius).

### References
tex: page 1 convention and the remark after Equation 13.

### Dependencies
**Depends on:** `Nhalf`, `Nrect_add_split`, `Nrect_eq_NlineRe_of_forall_ne_zero`,
`Nrect_eq_zero_of_forall_ne_zero`.
**Used by:** `HalvingConvention.Nhalf_nonneg`, `HalvingConvention.Nrect_inner_le_Nhalf`,
`HalvingConvention.littlewoodshortHalf`, `HalvingConvention.mainJensenHalf`,
`HalvingConvention.mainLittlewoodHalf`. -/
theorem two_mul_Nhalf_eq {T1 T2 α ε : ℝ} (hε : 0 < ε) (hT1 : 0 < T1 - ε) (h12 : T1 + ε ≤ T2 - ε)
    (hgap1 : ∀ s : ℂ, riemannZeta s = 0 → 1 - α < s.re → |s.im - T1| ≤ ε → s.im = T1)
    (hgap2 : ∀ s : ℂ, riemannZeta s = 0 → 1 - α < s.re → |s.im - T2| ≤ ε → s.im = T2) :
    2 * Nhalf T1 T2 α
      = (Nrect (T1 - ε) (T2 + ε) α : ℝ) + (Nrect (T1 + ε) (T2 - ε) α : ℝ) := by
  have hT1' : 0 < T1 := by linarith
  have hT2 : 0 < T2 := by linarith
  have o1 : Nrect (T1 - ε) (T2 + ε) α = Nrect (T1 - ε) T1 α + Nrect T1 (T2 + ε) α :=
    Nrect_add_split hT1 (by linarith) (by linarith)
  have o2 : Nrect T1 (T2 + ε) α = Nrect T1 T2 α + Nrect T2 (T2 + ε) α :=
    Nrect_add_split hT1' (by linarith) (by linarith)
  have o3 : Nrect (T1 - ε) T1 α = NlineRe T1 α := by
    apply Nrect_eq_NlineRe_of_forall_ne_zero hT1 hε
    intro s h1 h2 hre hz
    have := hgap1 s hz hre (by rw [abs_le]; constructor <;> linarith)
    linarith
  have o4 : Nrect T2 (T2 + ε) α = 0 := by
    apply Nrect_eq_zero_of_forall_ne_zero hT2
    intro s h1 h2 hre hz
    have := hgap2 s hz hre (by rw [abs_le]; constructor <;> linarith)
    linarith
  have i1 : Nrect T1 T2 α = Nrect T1 (T1 + ε) α + Nrect (T1 + ε) T2 α :=
    Nrect_add_split hT1' (by linarith) (by linarith)
  have i2 : Nrect (T1 + ε) T2 α = Nrect (T1 + ε) (T2 - ε) α + Nrect (T2 - ε) T2 α :=
    Nrect_add_split (by linarith) h12 (by linarith)
  have i3 : Nrect T1 (T1 + ε) α = 0 := by
    apply Nrect_eq_zero_of_forall_ne_zero hT1'
    intro s h1 h2 hre hz
    have := hgap1 s hz hre (by rw [abs_le]; constructor <;> linarith)
    linarith
  have i4 : Nrect (T2 - ε) T2 α = NlineRe T2 α := by
    apply Nrect_eq_NlineRe_of_forall_ne_zero (by linarith) hε
    intro s h1 h2 hre hz
    have := hgap2 s hz hre (by rw [abs_le]; constructor <;> linarith)
    linarith
  have hout : Nrect (T1 - ε) (T2 + ε) α = NlineRe T1 α + Nrect T1 T2 α := by
    rw [o1, o2, o3, o4]; ring
  have hin : Nrect (T1 + ε) (T2 - ε) α = Nrect T1 T2 α - NlineRe T2 α := by
    have := i1
    rw [i2, i3, i4] at this
    linarith
  unfold Nhalf
  rw [hout, hin]
  push_cast
  ring

/-- **With zero-free edges the two conventions agree:** `Nhalf T₁ T₂ α = Nrect T₁ T₂ α`.

### Summary of Proof
Both `NlineRe` terms vanish (`NlineRe_eq_zero_of_forall_ne_zero`).

### Lean Notes
This is the precise sense in which every `hzf_p`/`hzf_m`-carrying theorem of the project is
already a statement about the tex's half-counted `N(T₁,T₂,α)`.

### Dependencies
**Depends on:** `Nhalf`, `NlineRe_eq_zero_of_forall_ne_zero`.
**Used by:** documentation. -/
theorem Nhalf_eq_Nrect_of_forall_ne_zero {T1 T2 α : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2)
    (h1 : ∀ x : ℝ, 1 - α < x → riemannZeta (x + T1 * Complex.I) ≠ 0)
    (h2 : ∀ x : ℝ, 1 - α < x → riemannZeta (x + T2 * Complex.I) ≠ 0) :
    Nhalf T1 T2 α = Nrect T1 T2 α := by
  unfold Nhalf
  rw [NlineRe_eq_zero_of_forall_ne_zero hT1 h1, NlineRe_eq_zero_of_forall_ne_zero hT2 h2]
  simp

/-- **The function `Φ(s) = ∑_{n>1} Λ(n)/(log n)² n^{-s}` of Equation `\ref{eq:phis}`
(Equation 12), an antiderivative of `-log ζ(s)`.**

### Summary of Proof
A definition, transcribed from Equation 12. **Note the sign**: it is an antiderivative of
`-log ζ(s)`, not of `log ζ(s)`, because `d/ds n^{-s} = -log(n) n^{-s}` contributes a minus, so
term-by-term differentiation gives `Φ'(s) = -∑_{n>1} Λ(n)/log(n)·n^{-s}`. That is exactly what
`Phi_hasDerivAt` proves, the tex records the same sign at Equation 12, and everything downstream
consumes the negated form consistently.

### References
tex: Equation `\ref{eq:phis}` (Equation 12), inside `\ref{prop:outside2}` (Proposition 22).

### Dependencies
**Depends on:** none.
**Used by:** `A6`, `B4`, `Phi_continuousOn_closedHalfPlane`, `Phi_eq_LSeries`,
`Phi_eq_LSeries_funext`, `Phi_hasDerivAt`, `Phi_im_hasDerivAt`, `Phi_norm_le`, `Phi_one_lt`,
`Phi_re_antitoneOn`, `c5`, `littlewood_outerlog`, `littlewood_outerlog_le`,
`littlewood_outerlog_of_one_lt`, `littlewoodshort`, `littlewoodshort_tight`, `outside2`,
`outside2_le`, `outside2_of_one_lt`, `outside3_lt`, `rectangularjensen`, `rectangularjensen_tight`.
-/
noncomputable def Phi (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n ≤ 1 then 0 else
    (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) ^ 2 / (n : ℂ) ^ s

/-- **`Phi` as a coefficient function, for hooking into Mathlib's `LSeries` API (differentiability,
abscissa of convergence).**

### Summary of Proof
A definition: `Φ`'s coefficient function, `n ↦ Λ(n)/(log n)²` for `n > 1` and `0`
otherwise. Phrasing `Φ` as an `LSeries` of this lets Mathlib's API supply
differentiability and the abscissa of convergence rather than reproving them by hand.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `LSeriesSummable_PhiTerm_one`, `PhiTerm_abscissaOfAbsConv_le_one`, `PhiTerm_eq_ofReal`,
`PhiTerm_norm_le_two`, `PhiTerm_term_re`, `Phi_continuousOn_closedHalfPlane`, `Phi_eq_LSeries`,
`Phi_eq_LSeries_funext`, `Phi_hasDerivAt`, `Phi_norm_le`, `Phi_re_antitoneOn`,
`logMul_PhiTerm_eq_GTerm`. -/
noncomputable def PhiTerm : ℕ → ℂ :=
  fun n => if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) ^ 2

/-- **Bridge from the hand-rolled `Phi` to Mathlib's `LSeries` API.** `Phi` is defined directly as a
`tsum`; this identifies it with `LSeries PhiTerm`, unlocking Mathlib's differentiability and
abscissa-of-convergence machinery.

### Summary of Proof
Proved termwise: away from `n = 0, 1` the two summands are
definitionally equal, and at `n = 0, 1` both vanish (`PhiTerm` by its `if n ≤ 1` guard,
`LSeries.term` by its own `n = 0` case). No source counterpart — the tex uses the series informally.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `PhiTerm`.
**Used by:** `Phi_eq_LSeries_funext`, `Phi_norm_le`, `Phi_re_antitoneOn`,
`RectangularBounds.Phi_re_le_two_rpow`, `RectangularBounds.Phi_re_nonneg`. -/
theorem Phi_eq_LSeries (s : ℂ) : Phi s = LSeries PhiTerm s := by
  refine tsum_congr fun n => ?_
  simp only [LSeries.term, PhiTerm]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n ≤ 1
    · interval_cases n <;> simp_all
    · simp [h0, h1]

/-- **Uniform bound `‖PhiTerm n‖ ≤ 2`**, the input to `PhiTerm_abscissaOfAbsConv_le_one`.

### Summary of Proof
For `n ≥ 2`, `PhiTerm n = Λ(n)/(log n)²` with `Λ(n) ≤ log n` (`vonMangoldt_le_log`), so the ratio
is at most `1/log n ≤ 1/log 2 < 2`; for `n ≤ 1` the term is `0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `PhiTerm`.
**Used by:** `PhiTerm_abscissaOfAbsConv_le_one`. -/
theorem PhiTerm_norm_le_two {n : ℕ} : ‖PhiTerm n‖ ≤ 2 := by
  simp only [PhiTerm]
  by_cases h1 : n ≤ 1
  · simp [h1]
  · rw [not_le] at h1
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast h1)
    rw [ite_eq_right (by omega), norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogpos,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
    have hle : (ArithmeticFunction.vonMangoldt n) ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h1)
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9]

/-- **`PhiTerm`'s Dirichlet series converges absolutely for `Re s > 1`.**

### Summary of Proof
Immediate from the uniform bound `‖PhiTerm n‖ ≤ 2 = 2·n^{1-1}` (`PhiTerm_norm_le_two`) via
Mathlib's `LSeriesSummable_of_le_const_mul_rpow`.

### Lean Notes
This is what makes `Φ` differentiable on the open half plane, hence what `Phi_hasDerivAt` rests
on. The tex takes the convergence for granted.

### References
No tex counterpart.

### Dependencies
**Depends on:** `PhiTerm`, `PhiTerm_norm_le_two`.
**Used by:** `Phi_hasDerivAt`, `Phi_norm_le`, `Phi_re_antitoneOn`,
`RectangularBounds.LSeriesSummable_PhiTerm_of_one_le`. -/
theorem PhiTerm_abscissaOfAbsConv_le_one : LSeries.abscissaOfAbsConv PhiTerm ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1) (by exact_mod_cast hy)
  refine ⟨2, fun n _ => ?_⟩
  have h1 : ((n : ℝ)) ^ ((1 : ℝ) - 1) = 1 := by norm_num
  rw [h1, mul_one]
  exact PhiTerm_norm_le_two

/-- **Function-level (`funext`) restatement of `Phi_eq_LSeries`, for rewriting `Phi` as a whole
rather than pointwise.**

### Summary of Proof
`funext` applied to the pointwise identity `Phi_eq_LSeries`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `PhiTerm`, `Phi_eq_LSeries`.
**Used by:** `Phi_continuousOn_closedHalfPlane`, `Phi_hasDerivAt`. -/
theorem Phi_eq_LSeries_funext : Phi = LSeries PhiTerm := funext Phi_eq_LSeries

/-- **`G(s) := ∑_{n>1} Λ(n)/log(n) · n^{-s}`, the (negative of the) derivative of `Φ` (see
`Phi_hasDerivAt`); agrees with a branch of `log ζ(s)` for `Re s > 1` in the sense that
`exp(G(s)) = ζ(s)` (see `GTerm_LSeries_exp_eq_riemannZeta`), which is all that is needed to
recover `Re(G(s)) = log‖ζ(s)‖` without worrying about which branch of `Complex.log` is meant.**

### Summary of Proof
A definition, `n ↦ Λ(n)/log(n)` for `n > 1`. Its `LSeries` is `G(s) = ∑_{n>1} Λ(n)/log(n)·n^{-s}`,
which is `-Φ'` (see `Phi_hasDerivAt`) and agrees with a branch of `log ζ(s)` for
`Re s > 1`. Working with `G` rather than `Complex.log ∘ ζ` avoids having to track a branch
cut anywhere in the development.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GTerm_LSeries_exp_eq_riemannZeta`, `GTerm_LSeries_im_eq_zero`,
`GTerm_LSeries_re_eq_log_norm`, `GTerm_abscissaOfAbsConv_le_one`, `GTerm_eq_ofReal`,
`GTerm_norm_le_one`, `GTerm_term_im_eq_zero`, `GTerm_term_re`, `GTerm_term_two`, `G_hasDerivAt`,
`G_norm_le`, `Phi_hasDerivAt`, `Phi_im_hasDerivAt`, `argZeta_abs_le`, `argZeta_eq_im_G`,
`logMul_GTerm_eq_vonMangoldt`, `logMul_PhiTerm_eq_GTerm`, `log_zeta_norm_antitoneOn`,
`log_zeta_norm_pos`, `log_zeta_norm_strictAntiOn`. -/
noncomputable def GTerm : ℕ → ℂ :=
  fun n => if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)

/-- **Uniform bound `‖GTerm n‖ ≤ 1`**, the `GTerm` analogue of `PhiTerm_norm_le_two`.

### Summary of Proof
For `n ≥ 2`, `GTerm n = Λ(n)/log n ≤ 1` since `Λ(n) ≤ log n` (`vonMangoldt_le_log`); for `n ≤ 1`
the term is `0`. This is the input to `GTerm_abscissaOfAbsConv_le_one`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`.
**Used by:** `GTerm_abscissaOfAbsConv_le_one`. -/
theorem GTerm_norm_le_one {n : ℕ} : ‖GTerm n‖ ≤ 1 := by
  simp only [GTerm]
  by_cases h1 : n ≤ 1
  · simp [h1]
  · rw [not_le] at h1
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast h1)
    rw [ite_eq_right (by omega), norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hlogpos, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg),
      div_le_one hlogpos]
    exact ArithmeticFunction.vonMangoldt_le_log

/-- **`GTerm`'s Dirichlet series converges absolutely for `Re s > 1`.**

### Summary of Proof
From the uniform bound `‖GTerm n‖ ≤ 1` (`GTerm_norm_le_one`), via Mathlib's
`LSeriesSummable_of_le_const_mul_rpow`.

### Lean Notes
Since `LSeries GTerm` is the branch of `log ζ` used throughout this development
(`GTerm_LSeries_exp_eq_riemannZeta`), this is the convergence fact underlying every `log ζ`
manipulation on the half plane.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_norm_le_one`.
**Used by:** `GTerm_LSeries_im_eq_zero`, `G_hasDerivAt`, `G_norm_le`, `log_zeta_norm_antitoneOn`,
`log_zeta_norm_pos`, `log_zeta_norm_strictAntiOn`, `RectangularBounds.abs_log_zeta_norm_le`. -/
theorem GTerm_abscissaOfAbsConv_le_one : LSeries.abscissaOfAbsConv GTerm ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1) (by exact_mod_cast hy)
  refine ⟨1, fun n _ => ?_⟩
  have h1 : ((n : ℝ)) ^ ((1 : ℝ) - 1) = 1 := by norm_num
  rw [h1, mul_one]
  exact GTerm_norm_le_one

/-- **Term-level identity behind `Φ' = -log ζ`:** `LSeries.logMul PhiTerm = GTerm`.

### Summary of Proof
Mathlib differentiates a Dirichlet series by multiplying its coefficients by `-log n`
(`LSeries.logMul`); applying that to `PhiTerm` produces exactly `GTerm`, since
`(Λ(n)/(log n)²)·log n = Λ(n)/log n`. Proved termwise, the `n ≤ 1` cases being `0 = 0`.

### Lean Notes
Feeding this into `LSeries_hasDerivAt` is precisely how `Phi_hasDerivAt` is proved. The tex
asserts the antiderivative relation without proof.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `PhiTerm`.
**Used by:** `Phi_hasDerivAt`. -/
theorem logMul_PhiTerm_eq_GTerm : LSeries.logMul PhiTerm = GTerm := by
  funext n
  simp only [LSeries.logMul, PhiTerm, GTerm]
  by_cases h1 : n ≤ 1
  · simp [h1]
  · rw [not_le] at h1
    have hcl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (Nat.cast_nonneg n)]
    have hlogne : (Real.log n : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact (Real.log_pos (by exact_mod_cast h1)).ne'
    rw [ite_eq_right (by omega), ite_eq_right (by omega), hcl]
    field_simp

/-- **Term-level identity behind `G' = ζ'/ζ`:** `LSeries.logMul GTerm = Λ`.

### Summary of Proof
Multiplying `GTerm`'s coefficients by `log n` gives `Λ(n)` itself, since
`(Λ(n)/log n)·log n = Λ(n)`. The `n ≤ 1` cases are handled separately (`Λ(1) = 0`).

### Lean Notes
Combined with Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` this yields
`G_hasDerivAt`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`.
**Used by:** `G_hasDerivAt`. -/
theorem logMul_GTerm_eq_vonMangoldt :
    LSeries.logMul GTerm = fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  simp only [LSeries.logMul, GTerm]
  by_cases h1 : n ≤ 1
  · interval_cases n
    · simp
    · simp [ArithmeticFunction.vonMangoldt_apply_one]
  · rw [not_le] at h1
    have hcl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (Nat.cast_nonneg n)]
    have hlogne : (Real.log n : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact (Real.log_pos (by exact_mod_cast h1)).ne'
    rw [ite_eq_right (by omega), hcl]
    field_simp

/-- **The main structural fact about `Phi`.** For `Re s > 1`, `Φ'(s) = -G(s)`, where
`G(s) = LSeries GTerm s`.

### Summary of Proof
Rewrite `Phi` as `LSeries PhiTerm` (`Phi_eq_LSeries_funext`), apply Mathlib's
`LSeries_hasDerivAt` — legitimate because `PhiTerm_abscissaOfAbsConv_le_one` puts the abscissa of
absolute convergence below `Re s` — and identify the differentiated coefficients with `GTerm` by
`logMul_PhiTerm_eq_GTerm`.

### Lean Notes
Combined with `GTerm_LSeries_exp_eq_riemannZeta` below (`exp(G(s)) = ζ(s)`), this gives
`Φ'(s) = -log ζ(s)` in the sense that matters (real parts).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `Phi`, `PhiTerm`, `PhiTerm_abscissaOfAbsConv_le_one`,
`Phi_eq_LSeries_funext`, `logMul_PhiTerm_eq_GTerm`.
**Used by:** `Phi_im_hasDerivAt`, `RectangularBounds.Phi_re_hasDerivAt`. -/
theorem Phi_hasDerivAt {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt Phi (-LSeries GTerm s) s := by
  rw [Phi_eq_LSeries_funext]
  have hasc : LSeries.abscissaOfAbsConv PhiTerm < (s.re : EReal) :=
    lt_of_le_of_lt PhiTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hs)
  have h := LSeries_hasDerivAt hasc
  rwa [logMul_PhiTerm_eq_GTerm] at h

/-- **For `Re s > 1`, `G'(s) = ζ'(s)/ζ(s)`.**

### Summary of Proof
Differentiating a Dirichlet series multiplies its coefficients by `-log n`, so `G'` is the
`LSeries` of `n ↦ -log(n)·Λ(n)/log(n) = -Λ(n)` — that identification is
`logMul_GTerm_eq_vonMangoldt`. Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` then
names that series as `ζ'/ζ`. The whole step runs on Mathlib's `LSeries` differentiability API,
with `GTerm_abscissaOfAbsConv_le_one` supplying the convergence side condition.

### References
No tex counterpart — the tex differentiates `Φ`/`G` informally.

### Dependencies
**Depends on:** `GTerm`, `GTerm_abscissaOfAbsConv_le_one`, `logMul_GTerm_eq_vonMangoldt`.
**Used by:** `LittlewoodMethod.hasDerivAt_G_line`, `LittlewoodIdentity.hasDerivAt_G_vertical`,
`LogDerivZetaLaurent.hasSum_logDerivZetaCoeff_integrated`. -/
theorem G_hasDerivAt {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries GTerm) (deriv riemannZeta s / riemannZeta s) s := by
  have hasc : LSeries.abscissaOfAbsConv GTerm < (s.re : EReal) :=
    lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hs)
  have h := LSeries_hasDerivAt hasc
  rw [logMul_GTerm_eq_vonMangoldt,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  simpa [neg_div] using h

/-- **`exp(G(s)) = ζ(s)` for `Re s > 1`, where `G(s) := LSeries GTerm s`.** This is what makes
`G` "a branch of `log ζ`" in the only sense the development needs, and it avoids ever having to
discuss which branch of `Complex.log` is meant (no branch-cut ambiguity: `Complex.exp` is
single-valued, unlike `Complex.log`).

### Summary of Proof
Mathlib has this, as `riemannZeta_eq_exp_LSeries`
(`Mathlib.NumberTheory.EulerProduct.DirichletLSeries`): `exp (LSeries (fun n ↦ Λ n / log n) s) =
ζ(s)` for `Re s > 1`, proved there via the Euler product. `GTerm` agrees with `fun n ↦ Λ n / log n`
pointwise: for `n > 1` this is definitional, and at `n = 0, 1` both sides are `0` (`GTerm` by its
`if n ≤ 1` clause; the Mathlib side because `Λ 0 = Λ 1 = 0` and `Real.log 0 = Real.log 1 = 0`, so
`0 / 0 = 0` by Lean's junk-value convention for division).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`.
**Used by:** `GTerm_LSeries_re_eq_log_norm`, `LittlewoodMethod.exp_logZetaLine_line`,
`LittlewoodIdentity.exp_logZetaLine_line'`. -/
theorem GTerm_LSeries_exp_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries GTerm s) = riemannZeta s := by
  rw [← riemannZeta_eq_exp_LSeries hs]
  congr 1
  refine congrArg (LSeries · s) (funext fun n => ?_)
  simp only [GTerm]
  by_cases h1 : n ≤ 1
  · interval_cases n <;> simp
  · rw [ite_eq_right h1]

/-- **The real payoff of the two facts above: for `Re s > 1`, `Re(G(s)) = log‖ζ(s)‖`, with no
reference to `Complex.log` or its branch at all.**

### Summary of Proof
Combine the two preceding facts: `exp(G(s)) = ζ(s)` identifies `G` with a logarithm of
`ζ`, and taking real parts of that identity gives `Re(G(s)) = log‖ζ(s)‖`, since
`‖exp w‖ = exp (Re w)`. The point is that the conclusion mentions no `Complex.log` and so
no branch choice at all.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_exp_eq_riemannZeta`.
**Used by:** `Phi_im_hasDerivAt`, `log_zeta_norm_antitoneOn`, `log_zeta_norm_pos`,
`log_zeta_norm_strictAntiOn`, `RectangularBounds.Phi_re_hasDerivAt`,
`RectangularBounds.abs_log_zeta_norm_le`, `LittlewoodMethod.argZeta_abs_le`,
`LogDerivZetaLaurent.hasSum_logDerivZetaCoeff_integrated`. -/
theorem GTerm_LSeries_re_eq_log_norm {s : ℂ} (hs : 1 < s.re) :
    (LSeries GTerm s).re = Real.log ‖riemannZeta s‖ := by
  have h := GTerm_LSeries_exp_eq_riemannZeta hs
  have hnorm : ‖riemannZeta s‖ = Real.exp (LSeries GTerm s).re := by
    rw [← h, Complex.norm_exp]
  rw [hnorm, Real.log_exp]

/-- **`PhiTerm n` is a real number viewed in `ℂ` — every ingredient (`Λ(n)`, `log n`) is real.**

### Summary of Proof
Unfold `PhiTerm` and split on `n ≤ 1`; in both branches the value is a coercion of an explicitly
real expression, so `push_cast`/`ring` closes it.

### Lean Notes
Used to push `Complex.re` through `PhiTerm`'s Dirichlet terms in `PhiTerm_term_re` and
`Phi_norm_le`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `PhiTerm`.
**Used by:** `PhiTerm_term_re`, `Phi_norm_le`. -/
theorem PhiTerm_eq_ofReal (n : ℕ) :
    PhiTerm n = ((if n ≤ 1 then 0 else
      (ArithmeticFunction.vonMangoldt n) / (Real.log n) ^ 2 : ℝ) : ℂ) := by
  simp only [PhiTerm]
  split_ifs <;> push_cast <;> ring

/-- **Domination bound**: `Φ` (viewed at `w`) is dominated in norm by its value at the real point
`Re w`, since `PhiTerm` has nonnegative-real terms.

### Summary of Proof
Termwise: `‖term PhiTerm w n‖ = Re(term PhiTerm (Re w) n)` because the coefficient is a
nonnegative real (`PhiTerm_eq_ofReal`) and `‖n^{-w}‖ = n^{-Re w}`. Summing and pulling `Re`
through the `tsum` (`Complex.re_tsum`, legitimate by `PhiTerm_abscissaOfAbsConv_le_one`) gives the
bound from the triangle inequality for `tsum`s.

### Lean Notes
Used to bound `Φ` along vertical lines by its value on the real axis, in
`RectangularBounds.outside2_of_one_lt` and `LittlewoodMethod.littlewood_outerlog_of_one_lt`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `PhiTerm`, `PhiTerm_abscissaOfAbsConv_le_one`, `PhiTerm_eq_ofReal`,
`Phi_eq_LSeries`.
**Used by:** `RectangularBounds.abs_integral_log_zeta_vertical_le`,
`LittlewoodMethod.littlewood_outerlog_of_one_lt`. -/
theorem Phi_norm_le {w : ℂ} (hw : 1 < w.re) : ‖Phi w‖ ≤ (Phi (w.re : ℂ)).re := by
  have hsum : LSeriesSummable PhiTerm (w.re : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt PhiTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hw))
  have hterm_eq : ∀ n : ℕ, ‖LSeries.term PhiTerm w n‖ = (LSeries.term PhiTerm (w.re : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hpow : (n : ℂ) ^ (w.re : ℂ) = (((n : ℝ) ^ w.re : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (Nat.cast_nonneg n) w.re).symm
      have hxnn : (0 : ℝ) ≤
          if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n) / (Real.log n) ^ 2 := by
        split_ifs <;> positivity
      simp only [LSeries.term, ite_eq_right hn, PhiTerm_eq_ofReal]
      rw [hpow, ← Complex.ofReal_div, Complex.ofReal_re, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hxnn]
  have hsumnorm : Summable (fun n => ‖LSeries.term PhiTerm w n‖) := by
    simpa only [hterm_eq] using (Complex.hasSum_re hsum.hasSum).summable
  calc ‖Phi w‖ = ‖LSeries PhiTerm w‖ := by rw [Phi_eq_LSeries]
    _ ≤ ∑' n, ‖LSeries.term PhiTerm w n‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' n, (LSeries.term PhiTerm (w.re : ℂ) n).re := tsum_congr hterm_eq
    _ = (∑' n, LSeries.term PhiTerm (w.re : ℂ) n).re := (Complex.re_tsum hsum).symm
    _ = (LSeries PhiTerm (w.re : ℂ)).re := rfl
    _ = (Phi (w.re : ℂ)).re := by rw [Phi_eq_LSeries]

/-- **`ζ` is meromorphic at every point of `ℂ`**, including its pole at `s = 1`.

### Summary of Proof
Read off from
`riemannZeta_eq_mul_completedRiemannZeta₀`,
`ζ(s) = (sΛ₀(s) - 1 - s/(1-s)) / (2π^{-s/2}Γ(s/2+1))`: the numerator is entire apart from the
explicitly meromorphic `s/(1-s)`, and the denominator is a product of an entire factor with the
(meromorphic) `Γ`. Mathlib does not record this, though it does have `Meromorphic.Gamma`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `JensenBounds.intervalIntegrable_log_zeta_circle`,
`JensenBounds.intervalIntegrable_log_zeta_circle_reflect`,
`JensenBounds.intervalIntegrable_log_zeta_circle_shift`,
`JensenBounds.intervalIntegrable_log_zeta_cos`,
`ZetaCircleFcr.intervalIntegrable_log_zeta_real_axis`,
`RectangularBounds.intervalIntegrable_logzeta_line`,
`RectangularBounds.logzeta_arcsin_integrable_ofReal`, `JensenBounds.prop_Richert`. -/
theorem meromorphicAt_riemannZeta (z : ℂ) : MeromorphicAt riemannZeta z := by
  have hEq : riemannZeta = fun s : ℂ => (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
      (2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) :=
    funext riemannZeta_eq_mul_completedRiemannZeta₀
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcpow : AnalyticAt ℂ (fun s : ℂ => ((Real.pi : ℂ)) ^ (-s / 2)) z := by
    have hrw : (fun s : ℂ => ((Real.pi : ℂ)) ^ (-s / 2))
        = fun s : ℂ => Complex.exp (Complex.log ((Real.pi : ℂ)) * (-s / 2)) :=
      funext fun s => Complex.cpow_def_of_ne_zero hpi _
    rw [hrw]
    exact Differentiable.analyticAt (by fun_prop) z
  have hgam : MeromorphicAt (fun s : ℂ => Complex.Gamma (s / 2 + 1)) z :=
    (Meromorphic.Gamma (z / 2 + 1)).comp_analyticAt
      (g := fun s : ℂ => s / 2 + 1) (x := z) (by fun_prop)
  rw [hEq]
  apply MeromorphicAt.div
  · apply MeromorphicAt.sub
    · apply MeromorphicAt.sub
      · exact (AnalyticAt.mul analyticAt_id
          (differentiable_completedZeta₀.analyticAt z)).meromorphicAt
      · exact analyticAt_const.meromorphicAt
    · exact (analyticAt_id.meromorphicAt).div
        ((analyticAt_const.sub analyticAt_id).meromorphicAt)
  · exact ((analyticAt_const.mul hcpow).meromorphicAt).mul hgam

/-- **`‖ζ(s)‖ ≤ ζ(Re s)` for `Re s > 1`** — the Dirichlet-series domination used as the pointwise
step of `Proposition \ref{prop:integraloutside}` ("`log|ζ(1+it+re^{iθ})| < log(ζ(1+r cos θ))`").

### Summary of Proof
Same nonnegative-coefficient `tsum` argument as `Phi_norm_le`, applied to `ζ`'s own series.

Note this is `≤`, not the source's `<`: strictness needs a non-degeneracy argument (no cancellation
in `∑ n^{-s}`, which for `Im s ≠ 0` follows from linear independence of `{log p}` over `ℚ`), which
is a genuinely separate fact.

### References
tex: `\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `FcrZeta_inside_pointwise`, `integraloutside_bound`. -/
theorem zeta_norm_le_zeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta ((s.re : ℝ) : ℂ)‖ := by
  have hsre : (1:ℝ) < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hsumR : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (((s.re : ℝ) : ℂ))) :=
    Complex.summable_one_div_nat_cpow.mpr (by simpa using hs)
  have hterm : ∀ n : ℕ, ‖1 / (n : ℂ) ^ s‖ = (1 / (n : ℂ) ^ (((s.re : ℝ) : ℂ))).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hsne : s ≠ 0 := by
        intro h; rw [h] at hs; simp at hs; linarith
      have hsne' : ((s.re : ℝ) : ℂ) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      simp only [Nat.cast_zero, Complex.zero_cpow hsne, Complex.zero_cpow hsne']
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hpow : (n : ℂ) ^ (((s.re : ℝ) : ℂ)) = (((n : ℝ) ^ s.re : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (Nat.cast_nonneg n) s.re).symm
      rw [hpow, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos,
        ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsumnorm : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ s‖) := by
    simpa only [hterm] using (Complex.hasSum_re hsumR.hasSum).summable
  calc ‖riemannZeta s‖ = ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ := by rw [zeta_eq_tsum_one_div_nat_cpow hs]
    _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' n : ℕ, (1 / (n : ℂ) ^ (((s.re : ℝ) : ℂ))).re := tsum_congr hterm
    _ = (∑' n : ℕ, 1 / (n : ℂ) ^ (((s.re : ℝ) : ℂ))).re := (Complex.re_tsum hsumR).symm
    _ = (riemannZeta ((s.re : ℝ) : ℂ)).re := by rw [zeta_eq_tsum_one_div_nat_cpow hsre]
    _ ≤ ‖riemannZeta ((s.re : ℝ) : ℂ)‖ := Complex.re_le_norm _

/-! ### `log‖ζ(σ)‖` is antitone on the real axis right of `1`

The source uses "monotonicity of `ζ` on the real axis" as a pointwise step in
`Proposition \ref{prop:integraloutside}` and `Proposition \ref{prop:outside3}`. It follows from
the same nonnegative-Dirichlet-coefficient structure that gives `Phi_norm_le`: for real `σ > 1`,
`log‖ζ(σ)‖ = (LSeries GTerm σ).re = ∑ₙ (Λ(n)/log n)·n^{-σ}`, a sum of nonnegative terms each
antitone in `σ`. -/

/-- **`GTerm` is real-valued**: `GTerm n = ((Λ(n)/log n : ℝ) : ℂ)` for `n ≥ 2`, and `0` for
`n ≤ 1`.

### Summary of Proof
Unfold `GTerm` and split on `n ≤ 1`. In the nontrivial branch both `Λ(n)` and `log n` are
coercions of reals, so `push_cast`/`ring` closes it.

### Lean Notes
Bookkeeping the source never states. `GTerm` is *defined* with complex-valued `Λ(n)` and
`Complex.log n`; this identifies it with the coercion of an explicitly real expression, which is
what makes every later "sum of nonnegative reals" argument available (the source simply treats
`∑ Λ(n)/(log n) n^{-σ}` as a real series and moves on).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`.
**Used by:** `GTerm_term_im_eq_zero`, `GTerm_term_re`, `G_norm_le`,
`RectangularBounds.abs_log_zeta_norm_le`. -/
theorem GTerm_eq_ofReal (n : ℕ) :
    GTerm n = ((if n ≤ 1 then 0 else
      (ArithmeticFunction.vonMangoldt n) / (Real.log n) : ℝ) : ℂ) := by
  simp only [GTerm]
  split_ifs <;> push_cast <;> ring

/-- **Real part of `GTerm`'s Dirichlet term at a real point:**
`Re(term GTerm σ n) = (Λ(n)/log n)/n^σ` for real `σ`.

### Summary of Proof
The `n = 0` term is `0` by definition of `LSeries.term`. For `n ≠ 0`, rewrite `(n : ℂ) ^ (σ : ℂ)`
as the coercion of the real power `(n : ℝ) ^ σ` (`Complex.ofReal_cpow`) and use `GTerm_eq_ofReal`;
the whole term is then a coercion of a real, and `.re` is `Complex.ofReal_re`.

### Lean Notes
The `GTerm` companion of `PhiTerm_term_re`, and the workhorse behind every
nonnegative-coefficient argument in this section (`log_zeta_norm_antitoneOn`,
`log_zeta_norm_pos`, `log_zeta_norm_strictAntiOn`, `G_norm_le`): once each term is exhibited as a
nonnegative real, monotonicity and positivity of the sum follow termwise.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_eq_ofReal`.
**Used by:** `GTerm_term_two`, `G_norm_le`, `log_zeta_norm_antitoneOn`, `log_zeta_norm_pos`,
`log_zeta_norm_strictAntiOn`. -/
theorem GTerm_term_re (n : ℕ) (σ : ℝ) :
    (LSeries.term GTerm (σ : ℂ) n).re
      = (if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n) / (Real.log n) : ℝ)
          / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    simp only [LSeries.term, ite_eq_right hn, GTerm_eq_ofReal, hpow, ← Complex.ofReal_div,
      Complex.ofReal_re]

/-- **`log‖ζ(σ)‖` is antitone on `(1,∞)`.**

### Summary of Proof
By `GTerm_LSeries_re_eq_log_norm`, `log‖ζ(σ)‖ = Re(G(σ))`, and `G` is a Dirichlet series
with nonnegative coefficients `Λ(n)/log n ≥ 0`. Each term `n^{-σ}` is antitone in `σ`, so
the sum is antitone on `(1,∞)` where it converges absolutely.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `GTerm_abscissaOfAbsConv_le_one`,
`GTerm_term_re`.
**Used by:** `integral_logzeta_arcsin_gt`. -/
theorem log_zeta_norm_antitoneOn :
    AntitoneOn (fun σ : ℝ => Real.log ‖riemannZeta (σ : ℂ)‖) (Set.Ioi 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hare : (1:ℝ) < ((a : ℂ)).re := by simpa using ha
  have hbre : (1:ℝ) < ((b : ℂ)).re := by simpa using hb
  have hsa : LSeriesSummable GTerm (a : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast ha))
  have hsb : LSeriesSummable GTerm (b : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hb))
  simp only
  rw [← GTerm_LSeries_re_eq_log_norm hare, ← GTerm_LSeries_re_eq_log_norm hbre]
  change (∑' n, LSeries.term GTerm (b:ℂ) n).re ≤ (∑' n, LSeries.term GTerm (a:ℂ) n).re
  rw [Complex.re_tsum hsa, Complex.re_tsum hsb]
  refine Summable.tsum_mono ((Complex.hasSum_re hsb.hasSum).summable)
    ((Complex.hasSum_re hsa.hasSum).summable) ?_
  intro n
  simp only
  rw [GTerm_term_re, GTerm_term_re]
  rcases le_or_gt n 1 with hn | hn
  · simp [hn]
  · have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hnum : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n) / (Real.log n) := by
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      exact Real.log_nonneg (by linarith)
    rw [ite_eq_right (by omega : ¬ n ≤ 1)]
    apply div_le_div_of_nonneg_left hnum
    · exact Real.rpow_pos_of_pos (by linarith) a
    · exact Real.rpow_le_rpow_of_exponent_le (by linarith) hab

/-- **The `n = 2` term of `G`'s series is exactly `1/2^σ`**, since `Λ(2) = log 2` cancels the
`log 2` denominator.

### Summary of Proof
`GTerm_term_re` at `n = 2`, then `vonMangoldt_apply_prime` for `Λ(2) = log 2` and `div_self`
(`log 2 ≠ 0`).

### Lean Notes
Isolating one strictly positive term is what upgrades the nonnegativity arguments to strict
statements — used by `log_zeta_norm_pos` and `log_zeta_norm_strictAntiOn`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_term_re`.
**Used by:** `log_zeta_norm_pos`, `log_zeta_norm_strictAntiOn`. -/
theorem GTerm_term_two (σ : ℝ) :
    (LSeries.term GTerm (σ : ℂ) 2).re = 1 / (2 : ℝ) ^ σ := by
  rw [GTerm_term_re]
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  rw [h2, ite_eq_right (by omega : ¬ (2:ℕ) ≤ 1)]
  push_cast
  rw [div_self (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2)))]

/-- **`log‖ζ(σ)‖ > 0` for real `σ > 1`**, i.e. `‖ζ(σ)‖ > 1` there.

### Summary of Proof
Via `GTerm_LSeries_re_eq_log_norm`, `log‖ζ(σ)‖` is the sum of the nonnegative reals
`(Λ(n)/log n)·n^{-σ}` (`GTerm_term_re`); the `n = 2` term alone is `2^{-σ} > 0`
(`GTerm_term_two`), so the total is strictly positive.

Supplies the source's implicit "`log ζ` is positive to the right of `1`" step in
`Proposition \ref{prop:integraloutside}` (Proposition 15) and
`Proposition \ref{prop:outside3}` (Proposition 23), which the tex uses without comment.

### References
tex: `\ref{prop:integraloutside}` (Proposition 15), `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `GTerm_abscissaOfAbsConv_le_one`,
`GTerm_term_re`, `GTerm_term_two`.
**Used by:** `ConstantSigns.A6_nonneg`, `ZetaCircleFcr.FcrZeta_inside_pointwise`,
`RectangularBounds.Phi_one_re_eq_integral`, `ConstantSigns.c4_nonneg`,
`JensenBounds.integraloutside_bound`, `RectangularBounds.logzeta_integrableOn_Ioi_one`,
`ConstantSigns.two_Phi_one_add_c5_nonneg`. -/
theorem log_zeta_norm_pos {σ : ℝ} (hσ : 1 < σ) : 0 < Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hre : (1:ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hs : LSeriesSummable GTerm (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hσ))
  rw [← GTerm_LSeries_re_eq_log_norm hre]
  change 0 < (∑' n, LSeries.term GTerm (σ:ℂ) n).re
  rw [Complex.re_tsum hs]
  have hnn : ∀ n : ℕ, 0 ≤ (LSeries.term GTerm (σ:ℂ) n).re := by
    intro n
    rw [GTerm_term_re]
    rcases le_or_gt n 1 with hn | hn
    · simp [hn]
    · rw [ite_eq_right (by omega : ¬ n ≤ 1)]
      apply div_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.log_nonneg (by exact_mod_cast hn.le)))
      positivity
  have hle := Summable.le_tsum ((Complex.hasSum_re hs.hasSum).summable) 2 (fun j _ => hnn j)
  have h2pos : (0:ℝ) < (LSeries.term GTerm (σ:ℂ) 2).re := by
    rw [GTerm_term_two]; positivity
  linarith

/-- **Each term of `GTerm`'s Dirichlet series, evaluated at a *real* point, is itself real
(`GTerm n` is real, and `n^σ` for real `σ` is a nonnegative real cast) — so its imaginary part
vanishes.**

### Summary of Proof
Same rewriting as `GTerm_term_re`, of which this is the imaginary-part companion: the `n = 0`
term is `0`, and for `n ≠ 0` the term is a coercion of a real, so `Complex.ofReal_im` applies.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_eq_ofReal`.
**Used by:** `GTerm_LSeries_im_eq_zero`. -/
theorem GTerm_term_im_eq_zero (n : ℕ) (σ : ℝ) : (LSeries.term GTerm (σ : ℂ) n).im = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    simp only [LSeries.term, ite_eq_right hn, GTerm_eq_ofReal, hpow, ← Complex.ofReal_div,
      Complex.ofReal_im]

/-- **`G := LSeries GTerm` is real on the real axis** (`σ > 1`).

### Summary of Proof
Every term is real (`GTerm_term_im_eq_zero`); pull `Complex.im` through the `tsum`
(`Complex.im_tsum`, legitimate by `GTerm_abscissaOfAbsConv_le_one`) and sum zeros.

### Lean Notes
Needed for `argZeta_eq_im_G`'s base case.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_abscissaOfAbsConv_le_one`, `GTerm_term_im_eq_zero`.
**Used by:** none. -/
theorem GTerm_LSeries_im_eq_zero {σ : ℝ} (hσ : 1 < σ) : (LSeries GTerm (σ : ℂ)).im = 0 := by
  have hs : LSeriesSummable GTerm (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hσ))
  change (∑' n, LSeries.term GTerm (σ:ℂ) n).im = 0
  rw [Complex.im_tsum hs]
  simp only [GTerm_term_im_eq_zero, tsum_zero]

/-- **Domination bound for `G`**, the `GTerm`-analogue of `Phi_norm_le`: `G` (viewed at `w`) is
dominated in norm by its value at the real point `Re w`, since `GTerm` has nonnegative-real
coefficients.

### Summary of Proof
Termwise, exactly as in `Phi_norm_le`: `‖term GTerm w n‖ = Re(term GTerm (Re w) n)` by
`GTerm_eq_ofReal` and `GTerm_term_re`, then the triangle inequality for `tsum`s and
`Complex.re_tsum`.

### Lean Notes
Used to bound `arg ζ` by `log ζ(Re s)` in `LittlewoodMethod.argZeta_abs_le`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_abscissaOfAbsConv_le_one`, `GTerm_eq_ofReal`, `GTerm_term_re`.
**Used by:** `argZeta_abs_le`. -/
theorem G_norm_le {w : ℂ} (hw : 1 < w.re) : ‖LSeries GTerm w‖ ≤ (LSeries GTerm (w.re : ℂ)).re := by
  have hsum : LSeriesSummable GTerm (w.re : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hw))
  have hterm_eq : ∀ n : ℕ, ‖LSeries.term GTerm w n‖ = (LSeries.term GTerm (w.re : ℂ) n).re := by
    intro n
    rw [GTerm_term_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term, ite_eq_right hn, GTerm_eq_ofReal, norm_div,
        Complex.norm_natCast_cpow_of_pos hnpos, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by
          split_ifs with h
          · rfl
          · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.log_nonneg (by exact_mod_cast (not_le.mp h).le)))]
  have hsumnorm : Summable (fun n => ‖LSeries.term GTerm w n‖) := by
    simpa only [hterm_eq] using (Complex.hasSum_re hsum.hasSum).summable
  calc ‖LSeries GTerm w‖ = ‖∑' n, LSeries.term GTerm w n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term GTerm w n‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' n, (LSeries.term GTerm (w.re : ℂ) n).re := tsum_congr hterm_eq
    _ = (∑' n, LSeries.term GTerm (w.re : ℂ) n).re := (Complex.re_tsum hsum).symm
    _ = (LSeries GTerm (w.re : ℂ)).re := rfl

/-- **Strict form of `log_zeta_norm_antitoneOn`:** `σ ↦ log‖ζ(σ)‖` is *strictly* decreasing on
`(1,∞)`.**

### Summary of Proof
Same termwise argument, but using `Summable.tsum_lt_tsum` at the index `n = 2`, where
`GTerm_term_two` gives the strictly decreasing term `2^{-σ}`. Strictness is what
`integral_logzeta_arcsin_gt` needs (a strict integral inequality cannot be obtained from an
antitone bound alone).

This makes precise the source's informal appeal to monotonicity of `ζ` on the real axis in
`Proposition \ref{prop:integraloutside}` (Proposition 15) and
`Proposition \ref{prop:outside3}` (Proposition 23).

### References
tex: `\ref{prop:integraloutside}` (Proposition 15), `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `GTerm_abscissaOfAbsConv_le_one`,
`GTerm_term_re`, `GTerm_term_two`.
**Used by:** `integral_logzeta_arcsin_gt`. -/
theorem log_zeta_norm_strictAntiOn :
    StrictAntiOn (fun σ : ℝ => Real.log ‖riemannZeta (σ : ℂ)‖) (Set.Ioi 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hare : (1:ℝ) < ((a : ℂ)).re := by simpa using ha
  have hbre : (1:ℝ) < ((b : ℂ)).re := by simpa using hb
  have hsa : LSeriesSummable GTerm (a : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast ha))
  have hsb : LSeriesSummable GTerm (b : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hb))
  simp only
  rw [← GTerm_LSeries_re_eq_log_norm hare, ← GTerm_LSeries_re_eq_log_norm hbre]
  change (∑' n, LSeries.term GTerm (b:ℂ) n).re < (∑' n, LSeries.term GTerm (a:ℂ) n).re
  rw [Complex.re_tsum hsa, Complex.re_tsum hsb]
  refine Summable.tsum_lt_tsum (i := 2) ?_ ?_ ((Complex.hasSum_re hsb.hasSum).summable)
    ((Complex.hasSum_re hsa.hasSum).summable)
  · intro n
    simp only
    rw [GTerm_term_re, GTerm_term_re]
    rcases le_or_gt n 1 with hn | hn
    · simp [hn]
    · have hnum : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n) / (Real.log n) :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.log_nonneg (by exact_mod_cast hn.le))
      rw [ite_eq_right (by omega : ¬ n ≤ 1)]
      apply div_le_div_of_nonneg_left hnum
      · exact Real.rpow_pos_of_pos (by positivity) a
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hab.le
  · rw [GTerm_term_two, GTerm_term_two]
    apply div_lt_div_of_pos_left one_pos
    · exact Real.rpow_pos_of_pos (by norm_num) a
    · exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hab

/-- **Real part of `PhiTerm`'s Dirichlet term at a real point:**
`Re(term PhiTerm σ n) = (Λ(n)/(log n)²)/n^σ`.

### Summary of Proof
As `GTerm_term_re`: the `n = 0` term is `0`, and for `n ≠ 0` rewriting `(n : ℂ) ^ (σ : ℂ)` as the
coercion of `(n : ℝ) ^ σ` (`Complex.ofReal_cpow`) with `PhiTerm_eq_ofReal` makes the term a
coercion of a real.

### Lean Notes
Used by `Phi_re_antitoneOn` to run the same termwise monotonicity argument for `Φ` itself.

### References
No tex counterpart.

### Dependencies
**Depends on:** `PhiTerm`, `PhiTerm_eq_ofReal`.
**Used by:** `Phi_re_antitoneOn`, `RectangularBounds.Phi_re_le_two_rpow`,
`RectangularBounds.Phi_re_nonneg`. -/
theorem PhiTerm_term_re (n : ℕ) (σ : ℝ) :
    (LSeries.term PhiTerm (σ : ℂ) n).re
      = (if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n) / (Real.log n) ^ 2 : ℝ)
          / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    simp only [LSeries.term, ite_eq_right hn, PhiTerm_eq_ofReal, hpow, ← Complex.ofReal_div,
      Complex.ofReal_re]

/-! ### `-ζ'/ζ` is positive on the real axis right of `1`

The source uses "`ζ'(1+ru)/ζ(1+ru) < 0`" as a step in `Proposition \ref{prop:integraloutside}` and
`Proposition \ref{prop:outside3}`. Same nonnegative-Dirichlet-coefficient argument as
`log_zeta_norm_pos`, now with von Mangoldt's `Λ` in place of `GTerm`. -/

/-- **Real part of von Mangoldt's Dirichlet term at a real point:** `Re(term Λ σ n) = Λ(n)/n^σ`
for real `σ`.**

### Summary of Proof
The `n = 0` term is `0` by definition of `LSeries.term`. For `n ≠ 0`, rewrite
`(n : ℂ) ^ (σ : ℂ)` as the coercion of the real power `(n : ℝ) ^ σ` (`Complex.ofReal_cpow`,
valid since `n ≥ 0`), after which the whole term is a coercion of a real and taking `.re` is
`Complex.ofReal_re`.

### Lean Notes
The source writes `∑ Λ(n) n^{-σ}` as a real series without comment. This is the `Λ` analogue of
`GTerm_term_re`/`PhiTerm_term_re`, and is the step that lets `neg_logDeriv_zeta_re_pos` exhibit
`-ζ'/ζ(σ)` as a sum of *nonnegative reals*, which is how the source's "`ζ'(1+ru)/ζ(1+ru) < 0`"
step in `Proposition \ref{prop:integraloutside}` (Proposition 15) and
`Proposition \ref{prop:outside3}` (Proposition 23) is discharged.

### References
tex: `\ref{prop:integraloutside}` (Proposition 15), `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** none.
**Used by:** `neg_logDeriv_zeta_re_antitone`, `neg_logDeriv_zeta_re_pos`. -/
theorem vonMangoldt_term_re (n : ℕ) (σ : ℝ) :
    (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    simp only [LSeries.term, ite_eq_right hn, hpow, ← Complex.ofReal_div, Complex.ofReal_re]

/-- **`-ζ'/ζ(σ) > 0` for real `σ > 1` — the source's "`ζ'/ζ(1+ru) < 0`" step.**

### Summary of Proof
For real `σ > 1`, `-ζ'/ζ(σ) = ∑_{n≥2} Λ(n) n^{-σ}` is a sum of nonnegative reals with at
least one strictly positive term (`n = 2`), hence strictly positive. The real-part
bookkeeping is `vonMangoldt_term_re`. This discharges the source's step
"`ζ'(1+ru)/ζ(1+ru) < 0`", used in `\ref{prop:integraloutside}` (Proposition 15) and
`\ref{prop:outside3}` (Proposition 23).

### References
tex: `\ref{prop:integraloutside}` (Proposition 15), `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `vonMangoldt_term_re`.
**Used by:** `JensenBounds.c4IntegrandBound_abs_le`, `ConstantSigns.c4_nonneg`,
`JensenBounds.integraloutside_bound_secondary`. -/
theorem neg_logDeriv_zeta_re_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re := by
  have hre : (1:ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hs : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  rw [neg_div', ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre]
  change 0 < (∑' n, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ:ℂ) n).re
  rw [Complex.re_tsum hs]
  have hnn : ∀ n : ℕ,
      0 ≤ (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ:ℂ) n).re := by
    intro n
    rw [vonMangoldt_term_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have hle := Summable.le_tsum ((Complex.hasSum_re hs.hasSum).summable) 2 (fun j _ => hnn j)
  have h2pos :
      (0:ℝ) < (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ:ℂ) 2).re := by
    rw [vonMangoldt_term_re, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  linarith

/-- **`σ ↦ -Re(ζ'/ζ)(σ)` is antitone on `(1,∞)`.**

### Summary of Proof
Same route as `neg_logDeriv_zeta_re_pos` above, which this mirrors term for term. On `Re s > 1`,
`-ζ'(s)/ζ(s)` is the L-series of the von Mangoldt function
(`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`), summable there
(`ArithmeticFunction.LSeriesSummable_vonMangoldt`). Taking real parts through the `tsum`
(`Complex.re_tsum`) and using `vonMangoldt_term_re`, the value is `∑ₙ Λ(n)/n^σ`. Every term is
antitone in `σ` — `Λ(n) ≥ 0` and `n^σ` is monotone in `σ` for `n ≥ 1` — so `tsum_le_tsum`
finishes.

### Lean Notes
Note this comes from the **Dirichlet series**, not from the Laurent expansion at `s = 1`; in
particular it is independent of the `LaurentCertificate` class and of everything built on it.

The `n = 0` term is `0` on both sides by `LSeries.term`'s own convention, so the termwise
comparison holds for every `n` with no case split beyond what `vonMangoldt_term_re` already does.

It is used only where the fact that the function decreases matters, never a rate:
`JensenBounds.c4IntegrandBound_abs_le` bounds the integrand away from the pole, where the
`(0, 2]` range of `LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two` does not reach, and
the same monotonicity underlies the AM–GM argument recorded there for extending
`logderzetabound` past `x = 2`.

### References
No tex counterpart — used implicitly wherever the source says the estimate is worst near the
pole.

### Dependencies
**Depends on:** `vonMangoldt_term_re`.
**Used by:** `JensenBounds.c4IntegrandBound_abs_le`. -/
theorem neg_logDeriv_zeta_re_antitone {σ₁ σ₂ : ℝ} (hσ₁ : 1 < σ₁) (hle : σ₁ ≤ σ₂) :
    (-(deriv riemannZeta (σ₂ : ℂ) / riemannZeta (σ₂ : ℂ))).re
      ≤ (-(deriv riemannZeta (σ₁ : ℂ) / riemannZeta (σ₁ : ℂ))).re := by
  have hσ₂ : (1 : ℝ) < σ₂ := lt_of_lt_of_le hσ₁ hle
  have hre₁ : (1:ℝ) < ((σ₁ : ℂ)).re := by simpa using hσ₁
  have hre₂ : (1:ℝ) < ((σ₂ : ℂ)).re := by simpa using hσ₂
  have hs₁ : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ₁ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hre₁
  have hs₂ : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ₂ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hre₂
  rw [neg_div', neg_div',
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre₂,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre₁]
  change (∑' n, LSeries.term _ (σ₂:ℂ) n).re ≤ (∑' n, LSeries.term _ (σ₁:ℂ) n).re
  rw [Complex.re_tsum hs₂, Complex.re_tsum hs₁]
  refine (Complex.hasSum_re hs₂.hasSum).summable.tsum_le_tsum ?_
    (Complex.hasSum_re hs₁.hasSum).summable
  intro n
  rw [vonMangoldt_term_re, vonMangoldt_term_re]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hn1 : (1:ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hpow : ((n : ℝ)) ^ σ₁ ≤ ((n : ℝ)) ^ σ₂ := Real.rpow_le_rpow_of_exponent_le hn1 hle
    have hp1 : (0:ℝ) < ((n : ℝ)) ^ σ₁ := Real.rpow_pos_of_pos (by linarith) _
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hp1 hpow

/-- **Real-variable form of `Phi_hasDerivAt`.** For `σ > 1`, the real function `x ↦ Im(Φ(σ+xi))`
has derivative `-log‖ζ(σ+ti)‖` at every real `t`.

### Summary of Proof
Compose `Phi_hasDerivAt` with the affine map `w ↦ σ + wI` (chain rule), multiply by `-I` — which
turns the imaginary part into a real part — restrict to real arguments
(`HasDerivAt.real_of_complex`), and read the resulting real part off with
`GTerm_LSeries_re_eq_log_norm`.

### Lean Notes
This is the fact that runs the FTC argument in `RectangularBounds.outside2_of_one_lt` and
`LittlewoodMethod.littlewood_outerlog_of_one_lt`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `Phi`, `Phi_hasDerivAt`.
**Used by:** `RectangularBounds.integral_log_zeta_vertical_eq`,
`LittlewoodMethod.littlewood_outerlog_of_one_lt`. -/
theorem Phi_im_hasDerivAt {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (Phi ((σ : ℂ) + x * Complex.I)).im)
      (-Real.log ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖) t := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hsre : 1 < s.re := by simp [hs_def, hσ]
  have haffine : HasDerivAt (fun w : ℂ => (σ : ℂ) + w * Complex.I) Complex.I (t : ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => w * Complex.I) Complex.I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const Complex.I
    simpa using h1.const_add (σ : ℂ)
  have hcomp0 : HasDerivAt (Phi ∘ (fun w : ℂ => (σ : ℂ) + w * Complex.I))
      (-LSeries GTerm s * Complex.I) (t : ℂ) :=
    (Phi_hasDerivAt hsre).comp (t : ℂ) haffine
  have hcomp : HasDerivAt (fun w : ℂ => Phi ((σ : ℂ) + w * Complex.I))
      (-LSeries GTerm s * Complex.I) (t : ℂ) := hcomp0
  have hmul : HasDerivAt (fun w : ℂ => -Complex.I * Phi ((σ : ℂ) + w * Complex.I))
      (-Complex.I * (-LSeries GTerm s * Complex.I)) (t : ℂ) :=
    hcomp.const_mul (-Complex.I)
  have hval : -Complex.I * (-LSeries GTerm s * Complex.I) = -LSeries GTerm s := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have heq : -Complex.I * (-LSeries GTerm s * Complex.I) = LSeries GTerm s * Complex.I ^ 2 := by
      ring
    rw [heq, hI2]; ring
  rw [hval] at hmul
  have hreal := hmul.real_of_complex
  have hre_eq : ∀ x : ℝ, (-Complex.I * Phi ((σ : ℂ) + (x : ℂ) * Complex.I)).re
      = (Phi ((σ : ℂ) + (x : ℂ) * Complex.I)).im := fun x => by
    generalize Phi ((σ : ℂ) + (x : ℂ) * Complex.I) = z
    simp [Complex.mul_re]
  simp only [hre_eq] at hreal
  rwa [Complex.neg_re, GTerm_LSeries_re_eq_log_norm hsre] at hreal

/-! ### `Φ(1)` is well-defined: reducing convergence to Chebyshev's `ψ`-bound

`Phi` is a `tsum`, so `Phi 1` is only the "real" value of `∑ Λ(n)/(n(log n)²)` if that series is
actually (absolutely) summable — otherwise Lean's junk convention silently gives `Phi 1 = 0`, which
would make `RectangularBounds.outside2`/`LittlewoodMethod.littlewood_outerlog` state something
false. The crude bound `Λ(n) ≤ log n` alone is not enough (it only gives the *divergent* comparison
series `∑ 1/(n log n)`); genuine cancellation from `Λ` vanishing off the prime powers is needed.

This is exactly what a Chebyshev-type bound on `ψ(x) = ∑_{n≤x} Λ(n)` provides — and **Mathlib
already has one**, so the whole argument stays inside Mathlib:
`Chebyshev.psi_le_const_mul_self : ψ x ≤ (log 4 + 4) * x`. Combined with Abel summation
(`Mathlib.NumberTheory.AbelSummation.summable_mul_of_bigO_atTop'`), this gives summability directly:
writing `n ↦ Λ(n)/(n(log n)²)` (for `n ≥ 2`) as `f(n) * c(n)` with `c(n) := Λ(n)`, `f(t) := 1/(t
(log t)²)`, Abel's formula bounds the partial sums via `ψ`, and the remaining "boundary" integral
`∫ ψ(t) · |f'(t)| dt` converges because `f' = O(1/(t(log t)²))` and `∫ dt/(t(log t)²)` has the
explicit antiderivative `-1/log t → 0`. -/

/-- **The antiderivative used to certify integrability of `1/((t+1)(log(t+1))²)` at `+∞`: its
derivative is exactly that function, for every `t` with `0 < t` (so `t+1 > 1` and
`log(t+1) ≠ 0`).**

### Summary of Proof
Direct differentiation: `d/dt (-1/log(t+1)) = 1/((t+1)(log(t+1))²)` by the chain rule,
valid wherever `log(t+1) ≠ 0`, i.e. for `t > 0`. Having the antiderivative in closed form
is what certifies integrability of that function at `+∞`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrableOn_Ioi_one_recip_log_add_one`. -/
theorem hasDerivAt_neg_inv_log_add_one {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => -(Real.log (x + 1))⁻¹)
      (1 / ((t + 1) * Real.log (t + 1) ^ 2)) t := by
  have h1 : HasDerivAt (fun x : ℝ => x + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h3 : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (t + 1)) t :=
    h1.log (show (t : ℝ) + 1 ≠ 0 by linarith)
  have hlogne : Real.log (t + 1) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro h; linarith)
  have h4 := h3.inv hlogne
  have h5 := h4.neg
  have heq : -(-(1 / (t + 1)) / Real.log (t + 1) ^ 2) = 1 / ((t + 1) * Real.log (t + 1) ^ 2) := by
    field_simp
  rwa [heq] at h5

/-- **`1/((t+1)(log(t+1))²)` is integrable on `(1,∞)`** — the analytic fact underlying convergence
of `∑ Λ(n)/(n(log n)²)`, supplied as `hg₂` in the Abel-summation argument below.

### Summary of Proof
Directly from `hasDerivAt_neg_inv_log_add_one` and Mathlib's improper-integral FTC lemma
`integrableOn_Ioi_deriv_of_nonneg'`: the integrand is nonnegative on `(1,∞)` and the
antiderivative `-1/log(t+1)` tends to `0` at `+∞`. No Chebyshev input is needed here — that
enters through the *partial sums* bounds `h_bdd`/`hg₁` below, not through integrability of `f`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_neg_inv_log_add_one`.
**Used by:** `LSeriesSummable_PhiTerm_one`. -/
theorem integrableOn_Ioi_one_recip_log_add_one :
    MeasureTheory.IntegrableOn (fun t : ℝ => 1 / ((t + 1) * Real.log (t + 1) ^ 2))
      (Set.Ioi (1 : ℝ)) := by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (g := fun x : ℝ => -(Real.log (x + 1))⁻¹)
    (fun x hx => hasDerivAt_neg_inv_log_add_one (by simp only [Set.mem_Ici] at hx; linarith))
  · intro x hx
    simp only [Set.mem_Ioi] at hx
    positivity
  · have hlog : Filter.Tendsto (fun x : ℝ => Real.log (x + 1)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        Filter.tendsto_id)
    have := hlog.inv_tendsto_atTop
    simpa using this.neg

/-- **The derivative of `1/((t+1)(log(t+1))²)` itself (needed for `hf_int`/`hg₁` in the
Abel-summation argument below, as opposed to `hasDerivAt_neg_inv_log_add_one`, which is the
derivative of its *antiderivative*).**

### Summary of Proof
The derivative of `1/((t+1)(log(t+1))²)` itself, by the product and chain rules. Needed as
`hf_int`/`hg₁` in the Abel-summation argument below — a different requirement from
`hasDerivAt_neg_inv_log_add_one`, which supplies the antiderivative rather than the
derivative.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `LSeriesSummable_PhiTerm_one`, `PhiTerm_deriv_norm_mul_partialSum_isBigO`,
`hasDerivAt_two_add_div_mul_log_add_one_sq`. -/
theorem hasDerivAt_recip_mul_log_add_one_sq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => 1 / ((x + 1) * Real.log (x + 1) ^ 2))
      (-(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) / ((t + 1) * Real.log (t + 1) ^ 2) ^ 2)
      t := by
  have h1 : HasDerivAt (fun x : ℝ => x + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h3 : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (t + 1)) t :=
    h1.log (show (t : ℝ) + 1 ≠ 0 by linarith)
  have h3sq0 : HasDerivAt (fun x : ℝ => Real.log (x + 1) * Real.log (x + 1))
      (1 / (t + 1) * Real.log (t + 1) + Real.log (t + 1) * (1 / (t + 1))) t := h3.mul h3
  have hlogne : Real.log (t + 1) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro h; linarith)
  have htne : (t : ℝ) + 1 ≠ 0 := by linarith
  have hphi : HasDerivAt (fun x : ℝ => (x + 1) * (Real.log (x + 1) * Real.log (x + 1)))
      (1 * (Real.log (t + 1) * Real.log (t + 1)) +
        (t + 1) * (1 / (t + 1) * Real.log (t + 1) + Real.log (t + 1) * (1 / (t + 1)))) t :=
    h1.mul h3sq0
  have hphine : (t + 1) * (Real.log (t + 1) * Real.log (t + 1)) ≠ 0 :=
    mul_ne_zero htne (mul_ne_zero hlogne hlogne)
  have h4 := hphi.inv hphine
  have hfun : (fun x : ℝ => 1 / ((x + 1) * Real.log (x + 1) ^ 2))
      = (fun x : ℝ => (x + 1) * (Real.log (x + 1) * Real.log (x + 1)))⁻¹ := by
    funext x
    rw [Pi.inv_apply, ← sq, one_div]
  rw [hfun]
  have heq : -(1 * (Real.log (t + 1) * Real.log (t + 1)) +
        (t + 1) * (1 / (t + 1) * Real.log (t + 1) + Real.log (t + 1) * (1 / (t + 1)))) /
        ((t + 1) * (Real.log (t + 1) * Real.log (t + 1))) ^ 2
      = -(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) / ((t + 1) * Real.log (t + 1) ^ 2) ^ 2 := by
    field_simp
    ring
  rw [heq] at h4
  exact h4

/-- **`1/((t+1)(log(t+1))²)` is positive for `t > 0`.**

### Summary of Proof
For `t > 0` we have `t + 1 > 1`, so `log(t+1) > 0` and its square is positive; a quotient
of positives is positive. `positivity` discharges it once those two facts are in scope.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `LSeriesSummable_PhiTerm_one`, `PhiTerm_deriv_norm_mul_partialSum_isBigO`,
`PhiTerm_f_mul_partialSum_bddAbove`. -/
theorem recip_mul_log_add_one_sq_pos {t : ℝ} (ht : 0 < t) :
    0 < 1 / ((t + 1) * Real.log (t + 1) ^ 2) := by
  apply div_pos one_pos
  apply mul_pos (by linarith)
  apply sq_pos_of_ne_zero
  exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro h; linarith)

/-- **Chebyshev's bound controls the partial sums of `Λ` shifted by one.** For every `n : ℕ`,
`∑_{k=1}^n Λ(k+1) ≤ (log 4 + 4)(n+2)`.

### Summary of Proof
Reindex the shifted sum as a sum over `Finset.Icc 0 (n+1)`, which is `ψ(n+1)`
(`Chebyshev.psi_eq_sum_Icc`), then apply `Chebyshev.psi_le_const_mul_self` and enlarge `n+1` to
`n+2`.

### Lean Notes
This is the one place `Chebyshev.psi_le_const_mul_self` (Mathlib's explicit Chebyshev bound
`ψ(x) ≤ (log 4 + 4)x`) enters the summability argument below.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `PhiTerm_deriv_norm_mul_partialSum_isBigO`, `PhiTerm_f_mul_partialSum_bddAbove`. -/
theorem sum_vonMangoldt_succ_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖
      ≤ (Real.log 4 + 4) * (n + 2) := by
  have h1 : ∑ k ∈ Finset.Icc 1 n, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖
      = ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ) :=
    Finset.sum_congr rfl fun k _ => abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
  rw [h1]
  calc ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ)
      = ∑ x ∈ (Finset.Icc 1 n).image (· + 1), (ArithmeticFunction.vonMangoldt x : ℝ) :=
        (Finset.sum_image fun a _ b _ h => by omega).symm
    _ ≤ ∑ x ∈ Finset.Icc 0 (n + 1), (ArithmeticFunction.vonMangoldt x : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_image, Finset.mem_Icc] at hx
          obtain ⟨k, ⟨_, hk2⟩, rfl⟩ := hx
          simp only [Finset.mem_Icc]; omega
        · exact fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi (n + 1) := by
        rw [Chebyshev.psi_eq_sum_Icc,
          show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    _ ≤ (Real.log 4 + 4) * (n + 1) := Chebyshev.psi_le_const_mul_self (by positivity)
    _ ≤ (Real.log 4 + 4) * (n + 2) := by
        have : (0:ℝ) ≤ Real.log 4 + 4 := by
          have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
          linarith
        nlinarith

/-- **The derivative of the auxiliary ratio `g(t) := (t+2)/((t+1)(log(t+1))²)`**, whose value at
`t = n` bounds `f(n) * ∑_{k=1}^n Λ(k+1)` via `sum_vonMangoldt_succ_le`.

### Summary of Proof
Product rule applied to `(t+2) · 1/((t+1)(log(t+1))²)`, the second factor differentiated by
`hasDerivAt_recip_mul_log_add_one_sq`; `field_simp`/`ring` puts the result in the stated closed
form `-(log(t+1) + 2(t+2))/((t+1)²(log(t+1))³)`.

### Lean Notes
The sign is immediate from that closed form: for `t > 0` one has `log(t+1) > 0`, so numerator and
denominator are both positive and the derivative is negative throughout `(0,∞)` — `g` decreases
on the whole ray, with no case split and no numerics. `PhiTerm_f_mul_partialSum_bddAbove` uses
this only on `[1,∞)`, where it maximises `g` at `t = 1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_recip_mul_log_add_one_sq`.
**Used by:** `PhiTerm_f_mul_partialSum_bddAbove`. -/
theorem hasDerivAt_two_add_div_mul_log_add_one_sq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x + 2) / ((x + 1) * Real.log (x + 1) ^ 2))
      (-(Real.log (t + 1) + 2 * (t + 2)) / ((t + 1) ^ 2 * Real.log (t + 1) ^ 3)) t := by
  have hu : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have hf := hasDerivAt_recip_mul_log_add_one_sq ht
  have hg : HasDerivAt (fun x : ℝ => (x + 2) * (1 / ((x + 1) * Real.log (x + 1) ^ 2)))
      (1 * (1 / ((t + 1) * Real.log (t + 1) ^ 2)) +
        (t + 2) * (-(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) /
          ((t + 1) * Real.log (t + 1) ^ 2) ^ 2)) t :=
    hu.mul hf
  have hlogne : Real.log (t + 1) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro h; linarith)
  have htne : (t : ℝ) + 1 ≠ 0 := by linarith
  have hfun : (fun x : ℝ => (x + 2) * (1 / ((x + 1) * Real.log (x + 1) ^ 2)))
      = (fun x : ℝ => (x + 2) / ((x + 1) * Real.log (x + 1) ^ 2)) := by
    funext x; ring
  have heq : 1 * (1 / ((t + 1) * Real.log (t + 1) ^ 2)) +
      (t + 2) * (-(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) /
        ((t + 1) * Real.log (t + 1) ^ 2) ^ 2)
      = -(Real.log (t + 1) + 2 * (t + 2)) / ((t + 1) ^ 2 * Real.log (t + 1) ^ 3) := by
    field_simp
    ring
  rw [hfun, heq] at hg
  exact hg

/-- **General affine-quotient monotonicity.** For `p > 0`, `q ≥ 0`, `s > 0` and `r < 0`, the
function `h ↦ (p·h+q)/(s·h+r)` is strictly decreasing on `{h | 0 < s·h+r}`.

### Summary of Proof
Cross-multiplication, not differentiation. For `a < b` in the domain both denominators are
positive, so `div_lt_div_iff₀` reduces the claim to
`(pb+q)(sa+r) < (pa+q)(sb+r)`, whose difference collapses to `(b-a)(pr - qs)`. Then `b-a > 0`,
while `p > 0` with `r < 0` gives `pr < 0` and `q ≥ 0` with `s > 0` gives `qs ≥ 0`, so the second
factor is strictly negative and the product is negative.

That is the same sign computation the derivative would produce — `pr - qs` is the numerator of
`d/dh (ph+q)/(sh+r)` — reached without needing `strictAntiOn_of_deriv_neg`, the convexity of the
domain, or any `HasDerivAt.div` plumbing.

### Lean Notes
**The hypothesis is `r < 0`, not `r ≤ 0`, and that matters: with `r ≤ 0` the statement is
FALSE.** The numerator `pr - qs` vanishes exactly when `r = 0` and `q = 0` (given `p, s > 0`),
and there the function is constant, not strictly decreasing. `0 < q` would serve equally well as
the repair; `r < 0` is chosen because it is what the intended application supplies — see below.
**This is exactly the shape the corollaries need, and the strengthened hypothesis is free
there.** Writing `C_2 = NUM/DEN` as a function of `h`, both parts are affine in `1/h`:

    NUM = P + Q/h,   DEN = S - W/h,   so   C_2 = (P h + Q)/(S h - W)

with `P = 2(B₁ + πB₂ loglog t/log t + πB₃/log t)`,
`Q = 2α̂_r·(that same bracket) + πB₄/log t + 3.35π/(D_{r,α} t^{1/3} log t)`,
`S = 1 - log(2π)/log t - (1-log 2)/(t^{2/3} log t)` and `W = 0.194π + 9.908π/log t`.

So `r := -W`, and `W > 0` strictly — it has the constant term `0.194π` — hence `r < 0` always
holds in the application. The domain `{h | 0 < s·h + r}` is then `h > W/S`, which is precisely
the corollaries' admissibility threshold on `h_0` (the condition `DEN > 0`).

**Nothing in the project calls this lemma.** The `h`-monotonicity halves of
`MainCorollary.C2Jensen_antitone`/`C2Littlewood_antitone`, which support the "decreasing in both
`h₀` and `t₀`" claims of Corollaries `\ref{cor:main-jensen}` (Corollary 4) and
`\ref{cor:main-littlewood}` (Corollary 5), run instead through the non-strict
`MainCorollary.affine_div_affine_antitoneOn`, whose `≤` conclusion is what those statements need.
This strict variant is kept because the algebra above shows it is the right tool for the same
rearrangement whenever strictness is wanted.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** none.
**Used by:** none. -/
theorem affine_div_affine_strictAntiOn {p q s r : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hs : 0 < s)
    (hr : r < 0) :
    StrictAntiOn (fun h : ℝ => (p * h + q) / (s * h + r)) {h : ℝ | 0 < s * h + r} := by
  intro a ha b hb hab
  -- membership in `{h | 0 < s*h + r}` is definitional
  replace ha : (0:ℝ) < s * a + r := ha
  replace hb : (0:ℝ) < s * b + r := hb
  simp only
  rw [div_lt_div_iff₀ hb ha]
  -- Cross-multiplying, the difference collapses to `(b-a)(pr - qs)`, and `pr < 0 ≤ qs`.
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hab) (mul_neg_of_pos_of_neg hp hr),
    mul_nonneg (sub_pos.mpr hab).le (mul_nonneg hq hs.le)]

/-- **Reduction lemma** for the `h_bdd` hypothesis of `summable_mul_of_bigO_atTop'`: the
comparison weight `f(n) := 1/((n+1)(log(n+1))²)` times the partial sum of shifted von Mangoldt
values `∑_{k=1}^n Λ(k+1)` is globally bounded, uniformly in `n : ℕ`.

### Summary of Proof
Follows from
`sum_vonMangoldt_succ_le` (a Chebyshev bound valid for *all* `n`) combined with
`hasDerivAt_two_add_div_mul_log_add_one_sq`, which shows the resulting ratio
`(n+2)/((n+1)(log(n+1))²)` is (for `n ≥ 1`) decreasing in `n`, hence maximized at `n=1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_two_add_div_mul_log_add_one_sq`, `recip_mul_log_add_one_sq_pos`,
`sum_vonMangoldt_succ_le`.
**Used by:** `LSeriesSummable_PhiTerm_one`. -/
theorem PhiTerm_f_mul_partialSum_bddAbove :
    ∃ C : ℝ, ∀ n : ℕ,
      ‖(1:ℝ) / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2)‖ *
        ∑ k ∈ Finset.Icc 1 n, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖ ≤ C := by
  refine ⟨(Real.log 4 + 4) * (3 / (2 * Real.log 2 ^ 2)), fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    norm_num
    positivity
  · have hnormf : ‖(1:ℝ) / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2)‖
        = 1 / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2) :=
      abs_of_pos (recip_mul_log_add_one_sq_pos (by positivity))
    rw [hnormf]
    have hg_anti : AntitoneOn (fun t : ℝ => (t + 2) / ((t + 1) * Real.log (t + 1) ^ 2))
        (Set.Ici (1 : ℝ)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
      · have hden : ContinuousOn (fun t : ℝ => (t + 1) * Real.log (t + 1) ^ 2)
            (Set.Ici (1 : ℝ)) := by
          apply ContinuousOn.mul (by fun_prop)
          apply ContinuousOn.pow
          apply ContinuousOn.log (by fun_prop)
          intro t ht
          have : (0:ℝ) < t + 1 := by linarith [Set.mem_Ici.mp ht]
          exact this.ne'
        apply ContinuousOn.div (by fun_prop) hden
        intro t ht
        exact (mul_pos (by linarith [Set.mem_Ici.mp ht] : (0:ℝ) < t + 1)
          (sq_pos_of_ne_zero (Real.log_ne_zero_of_pos_of_ne_one
            (by linarith [Set.mem_Ici.mp ht]) (by intro h; linarith [Set.mem_Ici.mp ht, h])))).ne'
      · intro t ht
        rw [interior_Ici] at ht
        exact (hasDerivAt_two_add_div_mul_log_add_one_sq
          (by linarith [Set.mem_Ioi.mp ht])).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hasDerivAt_two_add_div_mul_log_add_one_sq (by linarith [Set.mem_Ioi.mp ht])).deriv]
        have h1 : (0:ℝ) < t + 1 := by linarith [Set.mem_Ioi.mp ht]
        have h2 : 0 < Real.log (t + 1) :=
          Real.log_pos (by linarith [Set.mem_Ioi.mp ht])
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
    have hle : (n + 2 : ℝ) / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2)
        ≤ (3 : ℝ) / (2 * Real.log 2 ^ 2) := by
      have hthis := hg_anti (Set.mem_Ici.mpr (le_refl (1:ℝ)))
        (Set.mem_Ici.mpr (show (1:ℝ) ≤ (n:ℝ) by exact_mod_cast hnpos))
        (show (1:ℝ) ≤ (n:ℝ) by exact_mod_cast hnpos)
      norm_num at hthis
      convert hthis using 2
    calc 1 / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2)
          * ∑ k ∈ Finset.Icc 1 n, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖
        ≤ 1 / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2) * ((Real.log 4 + 4) * (n + 2)) := by
          apply mul_le_mul_of_nonneg_left (sum_vonMangoldt_succ_le n)
          exact le_of_lt (recip_mul_log_add_one_sq_pos (by positivity))
      _ = (Real.log 4 + 4) * ((n + 2) / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1) ^ 2)) := by ring
      _ ≤ (Real.log 4 + 4) * (3 / (2 * Real.log 2 ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hle
          have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
          linarith

/-- **Reduction lemma** for the `hg₁` hypothesis of `summable_mul_of_bigO_atTop'`, with comparison
function `g = f` (chosen so that `hg₂` reduces to `integrableOn_Ioi_one_recip_log_add_one`):
`deriv ‖f‖` weighted by the partial sum of shifted von Mangoldt values is `O(f)` at `+∞`.

### Summary of Proof
Proved by
an explicit eventual bound at `t ≥ 7`: writing `L := log(t+1)`, `|deriv f(t)| = (L+2)/((t+1)²L³)`
(from `hasDerivAt_recip_mul_log_add_one_sq`, dividing through by `L`) and the partial sum is
`≤ (log4+4)(t+2)` (`sum_vonMangoldt_succ_le`), so the product is `≤ 4(log4+4)·f(t)` once `L ≥ 2`
(true for `t+1 ≥ 8 > e²`) — the algebra reduces to `2(t+2) ≤ L(3t+2)`, immediate from `L ≥ 2` and
`t ≥ 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_recip_mul_log_add_one_sq`, `recip_mul_log_add_one_sq_pos`,
`sum_vonMangoldt_succ_le`.
**Used by:** `LSeriesSummable_PhiTerm_one`. -/
theorem PhiTerm_deriv_norm_mul_partialSum_isBigO :
    (fun t : ℝ => deriv (fun x : ℝ => ‖(1:ℝ) / ((x + 1) * Real.log (x + 1) ^ 2)‖) t *
        ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖)
      =O[Filter.atTop] (fun t : ℝ => (1:ℝ) / ((t + 1) * Real.log (t + 1) ^ 2)) := by
  apply Asymptotics.IsBigO.of_bound (4 * (Real.log 4 + 4))
  filter_upwards [Filter.eventually_ge_atTop (8 : ℝ)] with t ht
  have ht0 : (0:ℝ) < t := by linarith
  have ht1pos : (0:ℝ) < t + 1 := by linarith
  set L := Real.log (t + 1) with hL_def
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hL2 : 2 ≤ L := by
    have hexp2 : Real.exp 2 < 8 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    have h8 : (8:ℝ) < t + 1 := by linarith
    have hlt := Real.log_lt_log (Real.exp_pos 2) (hexp2.trans h8)
    rw [Real.log_exp] at hlt
    rw [hL_def]; linarith [hlt]
  have hderiv_eq : deriv (fun x : ℝ => ‖(1:ℝ) / ((x + 1) * Real.log (x + 1) ^ 2)‖) t
      = deriv (fun x : ℝ => (1:ℝ) / ((x + 1) * Real.log (x + 1) ^ 2)) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds ht0] with x hx
    exact abs_of_pos (recip_mul_log_add_one_sq_pos hx)
  rw [hderiv_eq, (hasDerivAt_recip_mul_log_add_one_sq ht0).deriv]
  have hsum_le : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖)
      ≤ (Real.log 4 + 4) * (t + 2) := by
    calc ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖
        ≤ (Real.log 4 + 4) * (⌊t⌋₊ + 2) := sum_vonMangoldt_succ_le ⌊t⌋₊
      _ ≤ (Real.log 4 + 4) * (t + 2) := by
          have hlog4 : (0:ℝ) ≤ Real.log 4 + 4 := by
            have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
          have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
          nlinarith
  have hsum_nonneg :
      (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_pos (recip_mul_log_add_one_sq_pos ht0), abs_of_nonneg hsum_nonneg]
  have hnum_nonpos : -(L ^ 2 + 2 * L) ≤ 0 := by nlinarith [sq_nonneg L, hLpos.le]
  have hderivabs : |(-(L ^ 2 + 2 * L) / ((t + 1) * L ^ 2) ^ 2)|
      = (L + 2) / ((t + 1) ^ 2 * L ^ 3) := by
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum_nonpos (by positivity))]
    field_simp
  rw [hderivabs]
  have hlog4 : (0:ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  rw [div_mul_eq_mul_div, mul_one_div,
    div_le_div_iff₀ (by positivity : (0:ℝ) < (t + 1) ^ 2 * L ^ 3)
      (by positivity : (0:ℝ) < (t + 1) * L ^ 2)]
  have hbase : (L + 2) * (t + 2) ≤ 4 * (t + 1) * L := by nlinarith [hL2, ht0.le]
  have hkey : (L + 2) * (Real.log 4 + 4) * (t + 2) ≤ 4 * (Real.log 4 + 4) * (t + 1) * L := by
    nlinarith [mul_le_mul_of_nonneg_left hbase hlog4]
  have hstep : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖) * (L + 2)
      ≤ (Real.log 4 + 4) * (t + 2) * (L + 2) :=
    mul_le_mul_of_nonneg_right hsum_le (by linarith)
  have hfinal :
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖) * (L + 2) *
          ((t + 1) * L ^ 2)
        ≤ 4 * (Real.log 4 + 4) * (t + 1) * L * ((t + 1) * L ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖(ArithmeticFunction.vonMangoldt (k + 1) : ℝ)‖) * (L + 2)
        ≤ (Real.log 4 + 4) * (t + 2) * (L + 2) := hstep
      _ = (L + 2) * (Real.log 4 + 4) * (t + 2) := by ring
      _ ≤ 4 * (Real.log 4 + 4) * (t + 1) * L := hkey
  nlinarith [hfinal]

/-- **`PhiTerm` is summable at `s=1`**, hence `Phi 1` is genuinely the value of the convergent
series `∑ Λ(n)/(n(log n)²)`, not a `tsum` junk value.

### Summary of Proof
Combines Mathlib's Chebyshev bound `Chebyshev.psi_le_const_mul_self` with Abel's summation
formula (`Mathlib.NumberTheory.AbelSummation.summable_mul_of_bigO_atTop'`), whose four
hypotheses are supplied by the reduction lemmas above:
`PhiTerm_f_mul_partialSum_bddAbove` for `h_bdd`, `PhiTerm_deriv_norm_mul_partialSum_isBigO` for
`hg₁`, and `integrableOn_Ioi_one_recip_log_add_one` for `hg₂`. A Chebyshev bound suffices — no
PNT-strength input is used.

### Lean Notes
This is what makes the target `(Phi 1).re` of `RectangularBounds.outside2` and
`LittlewoodMethod.littlewood_outerlog` well-defined rather than a `tsum` junk value.

### References
No tex counterpart.

### Dependencies
**Depends on:** `PhiTerm`, `PhiTerm_deriv_norm_mul_partialSum_isBigO`,
`PhiTerm_f_mul_partialSum_bddAbove`, `hasDerivAt_recip_mul_log_add_one_sq`,
`integrableOn_Ioi_one_recip_log_add_one`, `recip_mul_log_add_one_sq_pos`.
**Used by:** `Phi_continuousOn_closedHalfPlane`, `Phi_re_antitoneOn`,
`RectangularBounds.LSeriesSummable_PhiTerm_of_one_le`. -/
theorem LSeriesSummable_PhiTerm_one : LSeriesSummable PhiTerm 1 := by
  set f : ℝ → ℝ := fun t => 1 / ((t + 1) * Real.log (t + 1) ^ 2) with hf_def
  set c : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) with hc_def
  have hnormf : ∀ t : ℝ, 0 < t → ‖f t‖ = f t :=
    fun t ht => abs_of_pos (recip_mul_log_add_one_sq_pos ht)
  have hnormc : ∀ n : ℕ, ‖c n‖ = c n :=
    fun _ => abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hderiv_eq : ∀ t : ℝ, 0 < t → deriv f t =
      -(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) / ((t + 1) * Real.log (t + 1) ^ 2) ^ 2 :=
    fun t ht => (hasDerivAt_recip_mul_log_add_one_sq ht).deriv
  have hderiv_normf_eq : ∀ t : ℝ, 0 < t → deriv (fun x => ‖f x‖) t = deriv f t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds ht] with x hx using hnormf x hx
  have hcont : ContinuousOn (deriv (fun x => ‖f x‖)) (Set.Ici (1 : ℝ)) := by
    apply ContinuousOn.congr (f := fun t =>
      -(Real.log (t + 1) ^ 2 + 2 * Real.log (t + 1)) / ((t + 1) * Real.log (t + 1) ^ 2) ^ 2)
    · intro t ht
      simp only [Set.mem_Ici] at ht
      have h1 : (0:ℝ) < t + 1 := by linarith
      have h2 : Real.log (t + 1) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro h; linarith)
      fun_prop (disch := first | positivity | assumption)
    · intro t ht
      simp only [Set.mem_Ici] at ht
      exact (hderiv_normf_eq t (by linarith)).trans (hderiv_eq t (by linarith))
  have key : Summable (fun n : ℕ => f n * c n) := by
    apply summable_mul_of_bigO_atTop' (f := f) (c := c)
    · intro t ht
      have ht' : (0:ℝ) < t := by simp only [Set.mem_Ici] at ht; linarith
      have heqf : (fun x : ℝ => ‖f x‖) =ᶠ[nhds t] f := by
        filter_upwards [eventually_gt_nhds ht'] with x hx using hnormf x hx
      exact ((hasDerivAt_recip_mul_log_add_one_sq ht').differentiableAt).congr_of_eventuallyEq
        heqf
    · exact hcont.locallyIntegrableOn measurableSet_Ici
    · obtain ⟨C, hC⟩ := PhiTerm_f_mul_partialSum_bddAbove
      refine Asymptotics.isBigO_one_nat_atTop_iff.mpr ⟨C, fun n => ?_⟩
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _))]
      exact hC n
    · exact PhiTerm_deriv_norm_mul_partialSum_isBigO
    · exact ⟨Set.Ioi (1 : ℝ), Filter.Ioi_mem_atTop 1, integrableOn_Ioi_one_recip_log_add_one⟩
  change Summable (LSeries.term PhiTerm 1)
  rw [← summable_nat_add_iff (f := LSeries.term PhiTerm 1) 1]
  apply (Complex.summable_ofReal.mpr key).congr
  intro n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  simp only [Nat.succ_eq_add_one]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : (ArithmeticFunction.vonMangoldt (0 + 1) : ℝ) = 0 := by
      norm_num [ArithmeticFunction.vonMangoldt_apply_one]
    simp only [hf_def, hc_def, this, mul_zero, Complex.ofReal_zero]
    norm_num [PhiTerm]
  · have hgt : ¬ ((n : ℕ) + 1 ≤ 1) := by omega
    have hlogpos : 0 < Real.log ((n:ℝ) + 1) := Real.log_pos (by
      have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
      linarith)
    simp only [hf_def, hc_def, PhiTerm, ite_eq_right hgt]
    push_cast
    rw [Complex.cpow_one]
    have hlogne : (Real.log ((n:ℝ) + 1) : ℂ) ≠ 0 := by
      exact_mod_cast hlogpos.ne'
    have hnne : ((n:ℂ) + 1) ≠ 0 := by
      have : (0:ℝ) < (n:ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    field_simp

/-- **`Re Φ(σ)` is antitone on `[1,∞)` (nonnegative coefficients, each term antitone).**

### Summary of Proof
`Re Φ(σ)` is a Dirichlet series with nonnegative coefficients `Λ(n)/(log n)² ≥ 0`, and
each term `n^{-σ}` is antitone in `σ`. A sum of antitone nonnegative terms is antitone, on
`[1,∞)` where the series converges.

### References
No tex counterpart.

### Dependencies
**Depends on:** `LSeriesSummable_PhiTerm_one`, `Phi`, `PhiTerm`, `PhiTerm_abscissaOfAbsConv_le_one`,
`PhiTerm_term_re`, `Phi_eq_LSeries`.
**Used by:** none. -/
theorem Phi_re_antitoneOn : AntitoneOn (fun σ : ℝ => (Phi (σ : ℂ)).re) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hsa : LSeriesSummable PhiTerm (a : ℂ) := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h]; exact_mod_cast LSeriesSummable_PhiTerm_one
    · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
        (lt_of_le_of_lt PhiTerm_abscissaOfAbsConv_le_one (by exact_mod_cast h))
  have hsb : LSeriesSummable PhiTerm (b : ℂ) := by
    rcases eq_or_lt_of_le hb with h | h
    · rw [← h]; exact_mod_cast LSeriesSummable_PhiTerm_one
    · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
        (lt_of_le_of_lt PhiTerm_abscissaOfAbsConv_le_one (by exact_mod_cast h))
  simp only [Phi_eq_LSeries]
  change (∑' n, LSeries.term PhiTerm (b:ℂ) n).re ≤ (∑' n, LSeries.term PhiTerm (a:ℂ) n).re
  rw [Complex.re_tsum hsa, Complex.re_tsum hsb]
  refine Summable.tsum_mono ((Complex.hasSum_re hsb.hasSum).summable)
    ((Complex.hasSum_re hsa.hasSum).summable) ?_
  intro n
  simp only
  rw [PhiTerm_term_re, PhiTerm_term_re]
  rcases le_or_gt n 1 with hn | hn
  · simp [hn]
  · have hnum : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n) / (Real.log n) ^ 2 := by
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg; positivity
    rw [ite_eq_right (by omega : ¬ n ≤ 1)]
    apply div_le_div_of_nonneg_left hnum
    · exact Real.rpow_pos_of_pos (by positivity) a
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hab

/-- **`Phi` is continuous on the closed half-plane `Re s ≥ 1`.**

### Summary of Proof
The key extra mileage from
`LSeriesSummable_PhiTerm_one`: since `ℂ` is finite-dimensional over `ℝ`, that `Summable`-in-the-
unconditional sense fact upgrades to *absolute* summability of `‖LSeries.term PhiTerm 1 n‖`
(`summable_norm_iff`), which dominates `‖LSeries.term PhiTerm w n‖` uniformly for every `w` with
`1 ≤ w.re` (since `n^{w.re} ≥ n^1` there), giving continuity of the whole series via Mathlib's
Weierstrass-M-test-style `continuousOn_tsum`.

### Lean Notes
This is what carries the `ε→0⁺` limiting arguments of `RectangularBounds.outside2_le` and
`LittlewoodMethod.littlewood_outerlog_le` from the open half-plane forms
`outside2_of_one_lt`/`littlewood_outerlog_of_one_lt` down to the boundary line `Re s = 1`.

### References
No tex counterpart — the tex uses continuity of `Φ` up to `Re s = 1` without remark.

### Dependencies
**Depends on:** `LSeriesSummable_PhiTerm_one`, `Phi`, `PhiTerm`, `Phi_eq_LSeries_funext`.
**Used by:** `RectangularBounds.Phi_re_continuousOn`, `LittlewoodMethod.littlewood_outerlog_le`,
`RectangularBounds.outside2_le`, `RectangularBounds.phi_slice_continuousOn`. -/
theorem Phi_continuousOn_closedHalfPlane : ContinuousOn Phi {s : ℂ | 1 ≤ s.re} := by
  rw [Phi_eq_LSeries_funext]
  have hu : Summable (fun n : ℕ => ‖LSeries.term PhiTerm 1 n‖) :=
    summable_norm_iff.mpr LSeriesSummable_PhiTerm_one
  refine continuousOn_tsum (fun n => ?_) hu (fun n w hw => ?_)
  · rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term] using continuousOn_const
    · simp only [LSeries.term_of_ne_zero hn]
      apply ContinuousOn.div continuousOn_const
      · exact (continuous_id.const_cpow
          (Or.inl (show (n : ℂ) ≠ 0 by exact_mod_cast hn))).continuousOn
      · intro w _
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hw1 : (1:ℝ) ≤ w.re := hw
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hn1 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnbase : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hmono : (n:ℝ) ^ ((1:ℂ).re) ≤ (n:ℝ) ^ w.re :=
        Real.rpow_le_rpow_of_exponent_le hnbase (by rw [Complex.one_re]; exact hw1)
      exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hn1 _) hmono

/-- **`α̂_r = √(r² - α²)`, from Equation `\ref{eq:hatalpha}` (Equation 10).**

### Summary of Proof
A definition, transcribed from Equation 10.

### Lean Notes
The formula is only meaningful for `α ≤ r`. `Real.sqrt` extends it to all `α, r` by sending
negative arguments to `0`; that junk branch is never reached, since every call site
(`RectangularBounds.lean`, `LittlewoodShort.lean`) carries `α ≤ r`.

### References
tex: Equation `\ref{eq:hatalpha}` (Equation 10).

### Dependencies
**Depends on:** none.
**Used by:** `C2Jensen`, `UJensen`, `jensenrectangle`, `outside2`, `outside2_le`, `outside3`,
`rectangularjensen`, `rectangularjensen_tight`. -/
noncomputable def hatAlpha (r α : ℝ) : ℝ := Real.sqrt (r ^ 2 - α ^ 2)

/-- **Existence and uniqueness of the constant `η ∈ (0,1)` solving `1 + η + log η = 0`, from
Equation `\ref{eq:eta}` (Equation 15).** Numerically `η ≈ 0.27846454276…`.

### Summary of Proof
`x ↦ 1 + x + log x` is strictly monotone on `(0,∞)` (`Real.strictMonoOn_log` plus the increasing
linear part) and continuous on `[1/100, 1]`. At `1/100` it is `1 + 1/100 - log 100 ≤ 0`, using
`log 100 > 2` from `Real.exp_one_lt_d9`; at `1` it is `2 > 0`. The intermediate value theorem
(`intermediate_value_Icc`) supplies a root `c`, which lies in the *open* interval since the value
at `1` is not `0`; uniqueness is injectivity of a strictly monotone function.

### Lean Notes
Unconditional: this file declares no hypothesis-class section variable, so the statement and its
proof depend on nothing beyond Mathlib and the three standard axioms.

### References
tex: Equation `\ref{eq:eta}` (Equation 15).

### Dependencies
**Depends on:** none.
**Used by:** `eta`, `eta_eq`, `eta_mem_Ioo`, `Solution.eta_eq_of_spec`. -/
theorem exists_unique_eta : ∃! η : ℝ, η ∈ Set.Ioo (0 : ℝ) 1 ∧ 1 + η + Real.log η = 0 := by
  have hmono : StrictMonoOn (fun x : ℝ => 1 + x + Real.log x) (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have := Real.strictMonoOn_log hx hy hxy
    dsimp only
    linarith
  have hexp2 : Real.exp 2 < 100 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  have hlog100 : (2 : ℝ) < Real.log 100 := by
    have h := Real.log_lt_log (Real.exp_pos 2) hexp2
    rwa [Real.log_exp] at h
  have hcont : ContinuousOn (fun x : ℝ => 1 + x + Real.log x) (Set.Icc (1 / 100 : ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ => 1 + x) (Set.Icc (1 / 100 : ℝ) 1) :=
      (continuous_const.add continuous_id).continuousOn
    have h2 : ContinuousOn Real.log (Set.Icc (1 / 100 : ℝ) 1) :=
      Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le (by norm_num) hx.1).ne'
    exact h1.add h2
  have hlog_frac : Real.log (1 / 100 : ℝ) = -Real.log 100 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have hg_a : (fun x : ℝ => 1 + x + Real.log x) (1 / 100) ≤ 0 := by
    dsimp only; rw [hlog_frac]; linarith
  have hg1_eq : (fun x : ℝ => 1 + x + Real.log x) (1 : ℝ) = 2 := by
    dsimp only; rw [Real.log_one]; ring
  have hg_b : (0 : ℝ) ≤ (fun x : ℝ => 1 + x + Real.log x) (1 : ℝ) := by rw [hg1_eq]; norm_num
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 100 : ℝ) ≤ 1) hcont ⟨hg_a, hg_b⟩
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) hc_mem.1
  have hc_lt_one : c < 1 := by
    rcases hc_mem.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, hg1_eq] at hc_eq; norm_num at hc_eq
  refine ⟨c, ⟨⟨hc_pos, hc_lt_one⟩, hc_eq⟩, ?_⟩
  rintro y ⟨⟨hy0, _⟩, hy_eq⟩
  exact hmono.injOn hy0 hc_pos (hy_eq.trans hc_eq.symm)

/-- **The constant `η ∈ (0,1)` solving `1 + η + log η = 0`, from Equation `\ref{eq:eta}`
(Equation 15).** Numerically `η ≈ 0.27846454276…`.

### Summary of Proof
A definition: the witness `exists_unique_eta.exists.choose`. It is therefore opaque, and
`eta_mem_Ioo`/`eta_eq` are the complete interface to it.

### Lean Notes
Unconditional, like everything in this file. Used in `Lemma \ref{lem:supremumforarg}` (Lemma 29)
and `Theorem \ref{thm:littlewoodshort}` (Theorem 32).

### References
tex: Equation `\ref{eq:eta}` (Equation 15); used in `\ref{lem:supremumforarg}` (Lemma 29) and
`\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** `exists_unique_eta`.
**Used by:** `A6`, `arg_integrals`, `deltaArg_bound_finite_N`, `eta_eq`, `eta_mem_Ioo`,
`littlewoodshort`, `littlewoodshort_tight`, `supremumforarg_full`. -/
noncomputable def eta : ℝ := exists_unique_eta.exists.choose

/-- **`η ∈ (0,1)`, extracted from `exists_unique_eta`.**

### Summary of Proof
The first component of `exists_unique_eta.exists.choose_spec`.

### Lean Notes
Together with `eta_eq` this is the full characterisation of the constant `η` of Equation
`\ref{eq:eta}` (Equation 15) that downstream files consume; `eta` itself is opaque (defined by
`choose`), so these two lemmas are the only way to reason about it. Both are unconditional.

### References
tex: `\ref{eq:eta}` (Equation 15).

### Dependencies
**Depends on:** `eta`, `exists_unique_eta`.
**Used by:** `ConstantSigns.A6_nonneg`, `ArgIntegrals.argRatio_le_of_gt`,
`ArgIntegrals.deltaArg_bound_finite_N`, `Solution.eta_eq_of_spec`,
`LittlewoodShort.littlewoodshort`, `LittlewoodShort.littlewoodshort_tight`. -/
theorem eta_mem_Ioo : eta ∈ Set.Ioo (0 : ℝ) 1 := exists_unique_eta.exists.choose_spec.1

/-- **The defining equation `1 + η + log η = 0` of Equation `\ref{eq:eta}` (Equation 15),
extracted from `exists_unique_eta`.**

### Summary of Proof
The second component of `exists_unique_eta.exists.choose_spec`.

### Lean Notes
Together with `eta_mem_Ioo` this is the complete interface to the opaque constant `eta`
(numerically `η ≈ 0.27846454276…`). Both are unconditional.

### References
tex: `\ref{eq:eta}` (Equation 15).

### Dependencies
**Depends on:** `eta`, `exists_unique_eta`.
**Used by:** `Littlewood.ArgIntegrals.arg_integrals`, and the Palomar `Solution.lean`, where it
discharges the characterisation the Challenge quantifies `η` under. -/
theorem eta_eq : 1 + eta + Real.log eta = 0 := exists_unique_eta.exists.choose_spec.2

/-- **The first Stieltjes constant `γ₁`**, appearing (together with the Euler–Mascheroni constant
`γ`, which is Mathlib's `eulerMascheroniConstant`) in the Laurent expansion of `ζ` at `s = 1`,
`ζ(s) = 1/(s-1) + ∑_{n≥0} ((-1)^n/n!) γ_n (s-1)^n`.

### Summary of Proof
A definition. Mathlib does not define the Stieltjes constants, so we mirror its construction of
`eulerMascheroniConstant` (`Mathlib.NumberTheory.Harmonic.EulerMascheroni`) directly from the
standard limit formula `γ₁ = lim_{m→∞} (∑_{k=1}^m (log k)/k - (log m)²/2)`.

### Lean Notes
`Filter.limUnder` of a divergent sequence is unspecified, so on its own this definition would be
a junk value. `tendsto_stieltjesSeq` supplies the missing convergence, and the bracketing
sequences below pin the value down numerically.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `c4_lt_of_le_exp_two_thirds`, `integraloutside_bound_secondary`,
`logDerivZetaCoeff_one`, `hasDerivAt_riemannZeta₀_one`, `neg_logDeriv_zeta_bound_of_claim_two`,
`stieltjes_combo_bound`, `stieltjes_combo_numeric_bounds`, `stieltjes_combo_pos`. -/
noncomputable def stieltjesConstant1 : ℝ :=
  Filter.limUnder Filter.atTop
    (fun m : ℕ => (∑ k ∈ Finset.range (m + 1), if k = 0 then 0 else Real.log k / k)
      - (Real.log m) ^ 2 / 2)

/-! ### Convergence of the limit defining `γ₁`, and a two-sided bracketing

`stieltjesConstant1` is a `Filter.limUnder`, so if the underlying sequence failed to converge it
would be a *junk value* and every numerical claim about it would be unprovable (or false).  This
section supplies the missing convergence proof together with an explicit two-sided bracketing

  `stieltjesSeqLow m ≤ γ₁ ≤ stieltjesSeq m`  for every `m ≥ 3`,

which reduces numerical claims about `γ₁` to finite computations with logarithms.

The argument is the standard sum-versus-integral comparison, in exactly the form Mathlib uses for
`Real.eulerMascheroniConstant` (`Mathlib.NumberTheory.Harmonic.EulerMascheroni`): a monotone and
an antitone sequence whose difference tends to `0`.  Writing `f x = (log x)/x`, the function
`(log x)²/2` is an antiderivative of `f`, so

  `stieltjesSeq m = ∑_{k=1}^m f k - ∫_1^m f`,

and each increment `stieltjesSeq (n+1) - stieltjesSeq n = f (n+1) - ∫_n^{n+1} f` is controlled by
the antitonicity of `f` on `[e, ∞)` (`Real.log_div_self_antitoneOn`).
-/

/-- **The sequence whose limit defines `stieltjesConstant1`.**

### Summary of Proof
A definition; the body is character-for-character the one inside `stieltjesConstant1`, so that
`stieltjesConstant1_eq_limUnder` holds by `rfl`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjesConstant1_eq_limUnder`, `stieltjesSeqLow`, `stieltjesSeq_succ_sub`,
`antitone_stieltjesSeq_shift`, `tendsto_stieltjesSeq`, `stieltjesConstant1_le_stieltjesSeq`. -/
noncomputable def stieltjesSeq (m : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (m + 1), if k = 0 then 0 else Real.log k / k) - (Real.log m) ^ 2 / 2

/-- **The lower bracketing sequence `stieltjesSeq m - (log m)/m`.**

### Summary of Proof
A definition.  The subtracted term `(log m)/m` is exactly the crude bound on the tail
`γ₁ - stieltjesSeq m`, obtained by telescoping `∑_{j>m} (f j - f (j-1)) = -f m`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq`.
**Used by:** `exists_tendsto_stieltjesSeq`, `monotone_stieltjesSeqLow_shift`,
`stieltjesSeqLow_le_stieltjesConstant1`, `stieltjesSeqLow_le_stieltjesSeq`,
`stieltjesSeqLow_le_succ`. -/
noncomputable def stieltjesSeqLow (m : ℕ) : ℝ := stieltjesSeq m - Real.log m / m

/-- **`stieltjesConstant1` is the `limUnder` of `stieltjesSeq`.**

### Summary of Proof
True by `rfl`: `stieltjesSeq` was given the same body as the lambda inside `stieltjesConstant1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesConstant1`, `stieltjesSeq`.
**Used by:** `tendsto_stieltjesSeq`. -/
theorem stieltjesConstant1_eq_limUnder :
    stieltjesConstant1 = Filter.limUnder Filter.atTop stieltjesSeq := rfl

/-- **`(log ·)²/2` is an antiderivative of `(log ·)/·` away from `0`.**

### Summary of Proof
Chain rule: `Real.hasDerivAt_log` gives `log' x = x⁻¹`, so `((log x)²)' = 2 (log x) x⁻¹`, and
dividing by `2` gives `(log x)/x`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_div_id`. -/
theorem hasDerivAt_log_sq_div_two {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log x / x) x := by
  have h : HasDerivAt (fun t : ℝ => Real.log t ^ 2) ((2 : ℕ) * Real.log x ^ (2 - 1) * x⁻¹) x :=
    (Real.hasDerivAt_log hx).pow 2
  have h2 := h.div_const 2
  have hval : ((2 : ℕ) : ℝ) * Real.log x ^ (2 - 1) * x⁻¹ / 2 = Real.log x / x := by
    push_cast
    rw [pow_one]
    field_simp
  rwa [hval] at h2

/-- **`(log ·)/·` is interval-integrable on any interval avoiding `0`.**

### Summary of Proof
It is continuous there: `Real.continuousAt_log` away from `0`, divided by the identity, which is
nonzero on the interval because both endpoints are positive.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_div_id`, `log_div_id_integral_step`, `log_div_id_tangent_step`,
`log_div_id_trapezoid`. -/
theorem intervalIntegrable_log_div_id {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => Real.log x / x) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hx0 : 0 < x := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
  exact ContinuousAt.continuousWithinAt
    ((Real.continuousAt_log hx0.ne').div continuousAt_id hx0.ne')

/-- **`∫_a^b (log x)/x dx = (log b)²/2 - (log a)²/2` for positive endpoints.**

### Summary of Proof
`intervalIntegral.integral_eq_sub_of_hasDerivAt` with the antiderivative
`hasDerivAt_log_sq_div_two`, valid at every point of `[[a,b]]` because both endpoints are
positive.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_log_sq_div_two`, `intervalIntegrable_log_div_id`.
**Used by:** `log_div_id_integral_step`, `log_div_id_tangent_step`, `log_div_id_trapezoid`. -/
theorem integral_log_div_id {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, Real.log x / x) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  have key : (∫ x in a..b, Real.log x / x)
      = (fun t : ℝ => Real.log t ^ 2 / 2) b - (fun t : ℝ => Real.log t ^ 2 / 2) a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Real.log t ^ 2 / 2) (fun x hx => ?_)
      (intervalIntegrable_log_div_id ha hb)
    have hx0 : 0 < x := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
      · rw [Set.uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
    exact hasDerivAt_log_sq_div_two hx0.ne'
  simpa using key

/-- **`Real.exp 1 ≤ 3`.**

### Summary of Proof
`Real.exp_one_lt_d9` gives `e < 2.7182818286 < 3`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjesSeq_succ_le`, `stieltjesSeqLow_le_succ`. -/
theorem exp_one_le_three : Real.exp 1 ≤ 3 :=
  le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))

/-- **The one-step sandwich `f (x+1) ≤ ∫_x^{x+1} f ≤ f x` for `f = (log ·)/·` and `x ≥ e`.**

### Summary of Proof
`Real.log_div_self_antitoneOn` says `f` is antitone on `[e, ∞)`, so on `[x, x+1]` the value of `f`
lies between the two endpoint values `f (x+1)` and `f x`.  Integrating those two constants over an
interval of length `1` gives the two bounds, and `integral_log_div_id` evaluates the middle term
as `(log (x+1))²/2 - (log x)²/2`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `integral_log_div_id`, `intervalIntegrable_log_div_id`.
**Used by:** `stieltjesSeq_succ_le`, `stieltjesSeqLow_le_succ`. -/
theorem log_div_id_integral_step {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.log (x + 1) / (x + 1) ≤ Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2 ∧
      Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2 ≤ Real.log x / x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxle : x ≤ x + 1 := by linarith
  have hmem : x ∈ Set.Ici (Real.exp 1) := hx
  have hmem1 : x + 1 ∈ Set.Ici (Real.exp 1) := le_trans hx hxle
  have hint : (∫ t in x..(x + 1), Real.log t / t)
      = Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2 := integral_log_div_id hx0 hx1
  constructor
  · rw [← hint]
    have hle : ∀ t ∈ Set.Icc x (x + 1), Real.log (x + 1) / (x + 1) ≤ Real.log t / t := by
      intro t ht
      exact Real.log_div_self_antitoneOn (le_trans hx ht.1) hmem1 ht.2
    calc Real.log (x + 1) / (x + 1)
        = ∫ _t in x..(x + 1), Real.log (x + 1) / (x + 1) := by simp
      _ ≤ ∫ t in x..(x + 1), Real.log t / t :=
          intervalIntegral.integral_mono_on hxle intervalIntegrable_const
            (intervalIntegrable_log_div_id hx0 hx1) hle
  · rw [← hint]
    have hle : ∀ t ∈ Set.Icc x (x + 1), Real.log t / t ≤ Real.log x / x := by
      intro t ht
      exact Real.log_div_self_antitoneOn hmem (le_trans hx ht.1) ht.1
    calc (∫ t in x..(x + 1), Real.log t / t)
        ≤ ∫ _t in x..(x + 1), Real.log x / x :=
          intervalIntegral.integral_mono_on hxle
            (intervalIntegrable_log_div_id hx0 hx1) intervalIntegrable_const hle
      _ = Real.log x / x := by simp

/-- **The increment of `stieltjesSeq`.**

### Summary of Proof
`Finset.sum_range_succ` peels off the `k = n+1` term of the defining sum; the `if k = 0` guard is
discharged because `n + 1 ≠ 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq`.
**Used by:** `stieltjesSeqHi_succ_le`, `stieltjesSeqLow_le_succ`, `stieltjesSeqMid_le_succ`,
`stieltjesSeq_succ_le`, `LogDerivZetaLaurent.sum_zetaTermD_one`. -/
theorem stieltjesSeq_succ_sub (n : ℕ) :
    stieltjesSeq (n + 1) - stieltjesSeq n
      = Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)
        - (Real.log ((n : ℝ) + 1) ^ 2 / 2 - Real.log (n : ℝ) ^ 2 / 2) := by
  have h0 : ¬ (n + 1 = 0) := Nat.succ_ne_zero n
  simp only [stieltjesSeq, Finset.sum_range_succ, ite_eq_right h0]
  push_cast
  ring

/-- **`stieltjesSeq` decreases from index `3` on.**

### Summary of Proof
By `stieltjesSeq_succ_sub` the increment is `f (n+1) - ∫_n^{n+1} f`, which is `≤ 0` by the first
half of `log_div_id_integral_step` (applicable since `n ≥ 3 ≥ e`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq_succ_sub`, `log_div_id_integral_step`, `exp_one_le_three`.
**Used by:** `antitone_stieltjesSeq_shift`. -/
theorem stieltjesSeq_succ_le {n : ℕ} (hn : 3 ≤ n) : stieltjesSeq (n + 1) ≤ stieltjesSeq n := by
  have hxn : Real.exp 1 ≤ (n : ℝ) :=
    exp_one_le_three.trans (by exact_mod_cast Nat.cast_le.mpr hn)
  have h := (log_div_id_integral_step hxn).1
  have := stieltjesSeq_succ_sub n
  linarith

/-- **`stieltjesSeqLow` increases from index `3` on.**

### Summary of Proof
`stieltjesSeqLow (n+1) - stieltjesSeqLow n = f n - ∫_n^{n+1} f`, which is `≥ 0` by the second half
of `log_div_id_integral_step`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq_succ_sub`, `log_div_id_integral_step`, `exp_one_le_three`.
**Used by:** `monotone_stieltjesSeqLow_shift`. -/
theorem stieltjesSeqLow_le_succ {n : ℕ} (hn : 3 ≤ n) :
    stieltjesSeqLow n ≤ stieltjesSeqLow (n + 1) := by
  have hxn : Real.exp 1 ≤ (n : ℝ) :=
    exp_one_le_three.trans (by exact_mod_cast Nat.cast_le.mpr hn)
  have h := (log_div_id_integral_step hxn).2
  have hsub := stieltjesSeq_succ_sub n
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [stieltjesSeqLow]
  rw [← hcast]
  linarith

/-- **The lower bracketing sequence never exceeds the upper one.**

### Summary of Proof
Their difference is `(log m)/m`, which is `≥ 0` for every natural `m` (for `m = 0` it is `0/0 = 0`
by Lean's junk convention, and for `m ≥ 1` both `log m ≥ 0` and `m > 0`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq`, `stieltjesSeqLow`.
**Used by:** `exists_tendsto_stieltjesSeq`. -/
theorem stieltjesSeqLow_le_stieltjesSeq (m : ℕ) : stieltjesSeqLow m ≤ stieltjesSeq m := by
  rw [stieltjesSeqLow, sub_le_self_iff]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (by positivity)

/-- **`stieltjesSeq`, shifted to start at index `3`, is antitone.**

### Summary of Proof
`antitone_nat_of_succ_le` applied to `stieltjesSeq_succ_le`, which is available from index `3` on.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq_succ_le`.
**Used by:** `exists_tendsto_stieltjesSeq`, `stieltjesConstant1_le_stieltjesSeq`. -/
theorem antitone_stieltjesSeq_shift : Antitone (fun k : ℕ => stieltjesSeq (k + 3)) :=
  antitone_nat_of_succ_le fun k => by
    simpa [show k + 1 + 3 = k + 3 + 1 from by omega] using
      stieltjesSeq_succ_le (n := k + 3) (by omega)

/-- **`stieltjesSeqLow`, shifted to start at index `3`, is monotone.**

### Summary of Proof
`monotone_nat_of_le_succ` applied to `stieltjesSeqLow_le_succ`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqLow_le_succ`.
**Used by:** `exists_tendsto_stieltjesSeq`, `stieltjesSeqLow_le_stieltjesConstant1`. -/
theorem monotone_stieltjesSeqLow_shift : Monotone (fun k : ℕ => stieltjesSeqLow (k + 3)) :=
  monotone_nat_of_le_succ fun k => by
    simpa [show k + 1 + 3 = k + 3 + 1 from by omega] using
      stieltjesSeqLow_le_succ (n := k + 3) (by omega)

/-- **`(log x)/x → 0` as `x → ∞`.**

### Summary of Proof
`Real.isLittleO_log_id_atTop` says `log =o[atTop] id`; `Asymptotics.IsLittleO.tendsto_div_nhds_zero`
converts that into the statement about the quotient.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjesSeqMid_le_stieltjesConstant1`, `tendsto_log_div_nat_shift`,
`tendsto_stieltjesSeqHi_shift`. -/
theorem tendsto_log_div_id_atTop :
    Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- **The gap between the two bracketing sequences tends to `0`.**

### Summary of Proof
Composition of `tendsto_log_div_id_atTop` with `k ↦ (k : ℝ) + 3`, which tends to `atTop`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `tendsto_log_div_id_atTop`.
**Used by:** `exists_tendsto_stieltjesSeq`, `stieltjesSeqLow_le_stieltjesConstant1`. -/
theorem tendsto_log_div_nat_shift :
    Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 3) / ((k : ℝ) + 3)) Filter.atTop (nhds 0) :=
  tendsto_log_div_id_atTop.comp
    (Filter.tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)

/-- **The sequence defining `γ₁` converges.**

### Summary of Proof
Mirrors Mathlib's treatment of `Real.eulerMascheroniConstant`.  From index `3` on,
`stieltjesSeqLow` is monotone (`monotone_stieltjesSeqLow_shift`) and bounded above by
`stieltjesSeq 3`, because `stieltjesSeqLow m ≤ stieltjesSeq m ≤ stieltjesSeq 3`.  Hence it
converges to its supremum (`tendsto_atTop_ciSup`).  Since
`stieltjesSeq m = stieltjesSeqLow m + (log m)/m` and the gap tends to `0`
(`tendsto_log_div_nat_shift`), the shifted `stieltjesSeq` converges to the same limit, and
`Filter.tendsto_add_atTop_iff_nat` removes the shift.

### Lean Notes
This is what makes `stieltjesConstant1` more than a junk value: `Filter.limUnder` of a divergent
sequence is unspecified, so without this lemma no numerical statement about `γ₁` is provable.

### References
No tex counterpart.

### Dependencies
**Depends on:** `monotone_stieltjesSeqLow_shift`, `antitone_stieltjesSeq_shift`,
`stieltjesSeqLow_le_stieltjesSeq`, `tendsto_log_div_nat_shift`.
**Used by:** `tendsto_stieltjesSeq`. -/
theorem exists_tendsto_stieltjesSeq :
    ∃ L : ℝ, Filter.Tendsto stieltjesSeq Filter.atTop (nhds L) := by
  have hbdd : BddAbove (Set.range fun k : ℕ => stieltjesSeqLow (k + 3)) := by
    refine ⟨stieltjesSeq 3, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (stieltjesSeqLow_le_stieltjesSeq (k + 3)).trans
      (antitone_stieltjesSeq_shift (Nat.zero_le k))
  have hB := tendsto_atTop_ciSup monotone_stieltjesSeqLow_shift hbdd
  refine ⟨⨆ k : ℕ, stieltjesSeqLow (k + 3), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 3]
  have hsum := hB.add tendsto_log_div_nat_shift
  rw [add_zero] at hsum
  refine hsum.congr fun k => ?_
  simp only [stieltjesSeqLow]
  push_cast
  ring

/-- **`stieltjesSeq` converges to `stieltjesConstant1`.**

### Summary of Proof
`exists_tendsto_stieltjesSeq` supplies a limit `L`; `Filter.Tendsto.limUnder_eq` identifies
`limUnder atTop stieltjesSeq`, which is `stieltjesConstant1` by definition, with `L`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `exists_tendsto_stieltjesSeq`, `stieltjesConstant1_eq_limUnder`.
**Used by:** `stieltjesConstant1_le_stieltjesSeq`, `stieltjesSeqLow_le_stieltjesConstant1`,
`stieltjesSeqMid_le_stieltjesConstant1`, `tendsto_stieltjesSeqHi_shift`,
`LogDerivZetaLaurent.hasSum_zetaTermD_one`. -/
theorem tendsto_stieltjesSeq :
    Filter.Tendsto stieltjesSeq Filter.atTop (nhds stieltjesConstant1) := by
  obtain ⟨L, hL⟩ := exists_tendsto_stieltjesSeq
  rw [stieltjesConstant1_eq_limUnder, hL.limUnder_eq]
  exact hL

/-- **Upper bracket: `γ₁ ≤ stieltjesSeq m` for every `m ≥ 3`.**

### Summary of Proof
The shifted sequence is antitone and converges to `γ₁`, so it stays above its limit
(`Antitone.le_of_tendsto`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `antitone_stieltjesSeq_shift`, `tendsto_stieltjesSeq`.
**Used by:** the numerical residues bounding `γ₁` from above. -/
theorem stieltjesConstant1_le_stieltjesSeq {m : ℕ} (hm : 3 ≤ m) :
    stieltjesConstant1 ≤ stieltjesSeq m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  exact antitone_stieltjesSeq_shift.le_of_tendsto
    ((Filter.tendsto_add_atTop_iff_nat 3).mpr tendsto_stieltjesSeq) j

/-- **Lower bracket: `stieltjesSeqLow m ≤ γ₁` for every `m ≥ 3`.**

### Summary of Proof
The shifted `stieltjesSeqLow` is monotone and converges to `γ₁` — it differs from `stieltjesSeq`
by `(log m)/m`, which tends to `0` — so it stays below its limit (`Monotone.ge_of_tendsto`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `monotone_stieltjesSeqLow_shift`, `tendsto_stieltjesSeq`,
`tendsto_log_div_nat_shift`.
**Used by:** the numerical residues bounding `γ₁` from below. -/
theorem stieltjesSeqLow_le_stieltjesConstant1 {m : ℕ} (hm : 3 ≤ m) :
    stieltjesSeqLow m ≤ stieltjesConstant1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hlow : Filter.Tendsto (fun k : ℕ => stieltjesSeqLow (k + 3)) Filter.atTop
      (nhds stieltjesConstant1) := by
    have hsub := ((Filter.tendsto_add_atTop_iff_nat 3).mpr tendsto_stieltjesSeq).sub
      tendsto_log_div_nat_shift
    rw [sub_zero] at hsub
    refine hsub.congr fun k => ?_
    simp only [stieltjesSeqLow]
    push_cast
    ring
  exact monotone_stieltjesSeqLow_shift.ge_of_tendsto hlow j

/-! ### Sharpening the lower bracket: the trapezoid refinement

The bracket above has gap `(log m)/m`, which overestimates the true error `γ₁ - stieltjesSeq m` by
a factor of `2`.  Replacing the rectangle bound `∫_n^{n+1} f ≤ f n` by the trapezoid bound
`∫_n^{n+1} f ≤ (f n + f (n+1))/2` — valid because `f x = (log x)/x` is *convex* on `[5, ∞)`, its
second derivative being `(2 log x - 3)/x³` — halves the gap, giving

  `stieltjesSeq m - (log m)/(2m) ≤ γ₁`  for every `m ≥ 5`.

The gain is decisive in practice: the crude bracket needs `m = 40` to certify `γ₁ > -1/8`, while
the refined one already does it at `m = 5`, where the sum involves only `log 2`, `log 3`
and `log 5`.
-/

/-- **`(log ·)/·` has derivative `(1 - log x)/x²`.**

### Summary of Proof
Quotient rule on `log x / x`, using `Real.hasDerivAt_log`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `convexOn_log_div_id`, `log_div_id_tangent_step`. -/
theorem hasDerivAt_log_div_id {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t / t) ((1 - Real.log x) / x ^ 2) x := by
  have h := (Real.hasDerivAt_log hx.ne').div (hasDerivAt_id' x) hx.ne'
  have heq : (x⁻¹ * x - Real.log x * 1) / x ^ 2 = (1 - Real.log x) / x ^ 2 := by
    rw [inv_mul_cancel₀ hx.ne', mul_one]
  rwa [heq] at h

/-- **`(1 - log ·)/·²` has derivative `(2 log x - 3)/x³`.**

### Summary of Proof
Quotient rule again.  This is the second derivative of `(log ·)/·`, and its sign is what makes
that function convex beyond `e^{3/2}`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `monotoneOn_deriv_log_div_id`. -/
theorem hasDerivAt_one_sub_log_div_sq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (1 - Real.log t) / t ^ 2) ((2 * Real.log x - 3) / x ^ 3) x := by
  have hx' : x ≠ 0 := hx.ne'
  have hnum : HasDerivAt (fun t : ℝ => 1 - Real.log t) (-x⁻¹) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx')
    rwa [zero_sub] at h
  have hden : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (((2 : ℕ) : ℝ) * x ^ (2 - 1)) x :=
      hasDerivAt_pow 2 x
    have heq : ((2 : ℕ) : ℝ) * x ^ (2 - 1) = 2 * x := by norm_num
    rwa [heq] at h
  have h := hnum.div hden (pow_ne_zero 2 hx')
  have heq : (-x⁻¹ * x ^ 2 - (1 - Real.log x) * (2 * x)) / (x ^ 2) ^ 2
      = (2 * Real.log x - 3) / x ^ 3 := by
    field_simp
    ring
  rwa [heq] at h

/-- **`3/2 < log 5`**, equivalently `e^{3/2} < 5`.

### Summary of Proof
`log 5 = 2 log 2 + log (5/4)`.  Mathlib's `Real.log_two_gt_d9` gives `2 log 2 > 1.38629`, and
`Real.log_le_sub_one_of_pos` at `4/5` gives `log (5/4) ≥ 1/5`.  The sum exceeds `3/2`.

### Lean Notes
This is the exact threshold for convexity of `(log ·)/·`: the second derivative
`(2 log x - 3)/x³` is nonnegative precisely when `log x ≥ 3/2`.  The true value of `e^{3/2}` is
`4.4816890703…`, so `5` clears it with room.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `monotoneOn_deriv_log_div_id`. -/
theorem three_halves_lt_log_five : (3 : ℝ) / 2 < Real.log 5 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h54 : (1 : ℝ) / 5 ≤ Real.log (5 / 4) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    rw [show (4 : ℝ) / 5 = ((5 : ℝ) / 4)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hsplit : Real.log 5 = Real.log 4 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  rw [hsplit, h4]
  linarith

/-- **The derivative of `(log ·)/·` is monotone on `[5, ∞)`.**

### Summary of Proof
`monotoneOn_of_deriv_nonneg` applied to `(1 - log x)/x²`, whose derivative
`(2 log x - 3)/x³` is nonnegative there because `log x ≥ log 5 > 3/2`
(`three_halves_lt_log_five`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_one_sub_log_div_sq`, `three_halves_lt_log_five`.
**Used by:** `convexOn_log_div_id`, `log_div_id_tangent_step`. -/
theorem monotoneOn_deriv_log_div_id :
    MonotoneOn (fun x : ℝ => (1 - Real.log x) / x ^ 2) (Set.Ici 5) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 5) ?_ ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    exact ((hasDerivAt_one_sub_log_div_sq hx0).continuousAt).continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by norm_num) hx
    exact ((hasDerivAt_one_sub_log_div_sq hx0).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by norm_num) hx
    rw [(hasDerivAt_one_sub_log_div_sq hx0).deriv]
    have hlog : (3 : ℝ) / 2 < Real.log x :=
      three_halves_lt_log_five.trans_le (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact div_nonneg (by linarith) (by positivity)

/-- **`(log ·)/·` is convex on `[5, ∞)`.**

### Summary of Proof
`MonotoneOn.convexOn_of_deriv`: the function is continuous and differentiable there, and its
derivative — computed by `hasDerivAt_log_div_id` to be `(1 - log x)/x²` — is monotone by
`monotoneOn_deriv_log_div_id`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_log_div_id`, `monotoneOn_deriv_log_div_id`.
**Used by:** `log_div_id_trapezoid`. -/
theorem convexOn_log_div_id : ConvexOn ℝ (Set.Ici 5) (fun x : ℝ => Real.log x / x) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 5) ?_ ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    exact ((hasDerivAt_log_div_id hx0).continuousAt).continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by norm_num) hx
    exact ((hasDerivAt_log_div_id hx0).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    have hEq : Set.EqOn (fun x : ℝ => (1 - Real.log x) / x ^ 2)
        (deriv fun x : ℝ => Real.log x / x) (Set.Ioi 5) := fun x hx =>
      ((hasDerivAt_log_div_id (lt_trans (by norm_num) hx)).deriv).symm
    exact (monotoneOn_deriv_log_div_id.mono Set.Ioi_subset_Ici_self).congr hEq

/-- **The trapezoid bound `∫_x^{x+1} f ≤ (f x + f (x+1))/2` for `f = (log ·)/·` and `x ≥ 5`.**

### Summary of Proof
Convexity (`convexOn_log_div_id`) puts the graph of `f` below its chord on `[x, x+1]`; integrating
that pointwise inequality and evaluating the integral of the (affine) chord — whose antiderivative
is written out explicitly — gives the trapezoid value `(f x + f (x+1))/2`.  The left-hand side is
evaluated by `integral_log_div_id`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `convexOn_log_div_id`, `integral_log_div_id`, `intervalIntegrable_log_div_id`.
**Used by:** `stieltjesSeqMid_le_succ`. -/
theorem log_div_id_trapezoid {x : ℝ} (hx : 5 ≤ x) :
    Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2
      ≤ (Real.log x / x + Real.log (x + 1) / (x + 1)) / 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxle : x ≤ x + 1 := by linarith
  have hint := integral_log_div_id hx0 hx1
  rw [← hint]
  have hchord : ∀ t ∈ Set.Icc x (x + 1),
      Real.log t / t
        ≤ (Real.log x / x) * (x + 1 - t) + (Real.log (x + 1) / (x + 1)) * (t - x) := by
    intro t ht
    have h := convexOn_log_div_id.2 (show x ∈ Set.Ici (5 : ℝ) from hx)
      (show x + 1 ∈ Set.Ici (5 : ℝ) from le_trans hx hxle)
      (show (0 : ℝ) ≤ x + 1 - t by linarith [ht.2])
      (show (0 : ℝ) ≤ t - x by linarith [ht.1]) (by ring)
    have hpt : (x + 1 - t) • x + (t - x) • (x + 1) = t := by
      simp only [smul_eq_mul]; ring
    rw [hpt] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hcont : Continuous fun t : ℝ =>
      (Real.log x / x) * (x + 1 - t) + (Real.log (x + 1) / (x + 1)) * (t - x) := by fun_prop
  calc (∫ t in x..(x + 1), Real.log t / t)
      ≤ ∫ t in x..(x + 1),
          ((Real.log x / x) * (x + 1 - t) + (Real.log (x + 1) / (x + 1)) * (t - x)) :=
        intervalIntegral.integral_mono_on hxle (intervalIntegrable_log_div_id hx0 hx1)
          (hcont.intervalIntegrable _ _) hchord
    _ = (Real.log x / x + Real.log (x + 1) / (x + 1)) / 2 := by
        have hF : ∀ t : ℝ, HasDerivAt
            (fun s : ℝ => (Real.log x / x) * ((x + 1) * s - s ^ 2 / 2)
              + (Real.log (x + 1) / (x + 1)) * (s ^ 2 / 2 - x * s))
            ((Real.log x / x) * (x + 1 - t)
              + (Real.log (x + 1) / (x + 1)) * (t - x)) t := by
          intro t
          have h1 : HasDerivAt (fun s : ℝ => (x + 1) * s - s ^ 2 / 2) (x + 1 - t) t := by
            have h : HasDerivAt (fun s : ℝ => (x + 1) * s - s ^ 2 / 2)
                ((x + 1) * 1 - ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2) t :=
              ((hasDerivAt_id' t).const_mul (x + 1)).sub ((hasDerivAt_pow 2 t).div_const 2)
            have heq : (x + 1) * 1 - ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = x + 1 - t := by norm_num
            rwa [heq] at h
          have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 - x * s) (t - x) t := by
            have h : HasDerivAt (fun s : ℝ => s ^ 2 / 2 - x * s)
                (((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 - x * 1) t :=
              ((hasDerivAt_pow 2 t).div_const 2).sub ((hasDerivAt_id' t).const_mul x)
            have heq : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 - x * 1 = t - x := by norm_num
            rwa [heq] at h
          exact (h1.const_mul _).add (h2.const_mul _)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
          (hcont.intervalIntegrable _ _)]
        ring

/-- **The refined lower bracketing sequence `stieltjesSeq m - (log m)/(2m)`.**

### Summary of Proof
A definition.  Written as `... / m / 2` rather than `... / (2 * m)` so that `linarith` sees the
same atom `(log m)/m` that appears in `stieltjesSeq_succ_sub`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeq`.
**Used by:** `stieltjesSeqMid_le_succ`, `stieltjesSeqMid_le_stieltjesConstant1`. -/
noncomputable def stieltjesSeqMid (m : ℕ) : ℝ := stieltjesSeq m - Real.log m / m / 2

/-- **`stieltjesSeqMid` increases from index `5` on.**

### Summary of Proof
`stieltjesSeqMid (n+1) - stieltjesSeqMid n = (f n + f (n+1))/2 - ∫_n^{n+1} f`, which is `≥ 0` by
`log_div_id_trapezoid`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_div_id_trapezoid`, `stieltjesSeq_succ_sub`.
**Used by:** `monotone_stieltjesSeqMid_shift`. -/
theorem stieltjesSeqMid_le_succ {n : ℕ} (hn : 5 ≤ n) :
    stieltjesSeqMid n ≤ stieltjesSeqMid (n + 1) := by
  have hxn : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := log_div_id_trapezoid hxn
  have hsub := stieltjesSeq_succ_sub n
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [stieltjesSeqMid]
  rw [← hcast]
  linarith

/-- **`stieltjesSeqMid`, shifted to start at index `5`, is monotone.**

### Summary of Proof
`monotone_nat_of_le_succ` applied to `stieltjesSeqMid_le_succ`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqMid_le_succ`.
**Used by:** `stieltjesSeqMid_le_stieltjesConstant1`. -/
theorem monotone_stieltjesSeqMid_shift : Monotone (fun k : ℕ => stieltjesSeqMid (k + 5)) :=
  monotone_nat_of_le_succ fun k => by
    simpa [show k + 1 + 5 = k + 5 + 1 from by omega] using
      stieltjesSeqMid_le_succ (n := k + 5) (by omega)

/-- **Refined lower bracket: `stieltjesSeq m - (log m)/(2m) ≤ γ₁` for every `m ≥ 5`.**

### Summary of Proof
The shifted `stieltjesSeqMid` is monotone (`monotone_stieltjesSeqMid_shift`) and converges to `γ₁`,
since it differs from `stieltjesSeq` by `(log m)/(2m) → 0`; so it stays below its limit.

### Lean Notes
This is twice as sharp as `stieltjesSeqLow_le_stieltjesConstant1`, and that is what makes the
numerical residues cheap: at `m = 5` the value is `-0.07485…`, already comfortably above the
`-1/8` needed for `Jensen.JensenBounds.stieltjes_combo_pos`, whereas the crude bracket does not
reach `-1/8` until `m = 40`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `monotone_stieltjesSeqMid_shift`, `tendsto_stieltjesSeq`,
`tendsto_log_div_id_atTop`.
**Used by:** the numerical residues bounding `γ₁` from below. -/
theorem stieltjesSeqMid_le_stieltjesConstant1 {m : ℕ} (hm : 5 ≤ m) :
    stieltjesSeqMid m ≤ stieltjesConstant1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  have hmid : Filter.Tendsto (fun k : ℕ => stieltjesSeqMid (k + 5)) Filter.atTop
      (nhds stieltjesConstant1) := by
    have hlog : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 5) / ((k : ℝ) + 5) / 2)
        Filter.atTop (nhds 0) := by
      have h := (tendsto_log_div_id_atTop.comp
        (Filter.tendsto_atTop_add_const_right _ 5 tendsto_natCast_atTop_atTop)).div_const 2
      simpa using h
    have hsub := ((Filter.tendsto_add_atTop_iff_nat 5).mpr tendsto_stieltjesSeq).sub hlog
    rw [sub_zero] at hsub
    refine hsub.congr fun k => ?_
    simp only [stieltjesSeqMid]
    push_cast
    ring
  exact monotone_stieltjesSeqMid_shift.ge_of_tendsto hmid j

/-! ### The Euler–Maclaurin upper bracket

The trapezoid bracket `stieltjesSeqMid m ≤ γ₁` is sharp from *below* (error `≈ (log m)/(12 m²)`),
but the only upper bracket so far, `γ₁ ≤ stieltjesSeq m`, has error `≈ (log m)/(2m)`, which forces
`m ≈ 800` for the numeric claim `γ² + 2γ₁ ≤ 0.20` (`Background.LogDerivZetaLaurent`).  The next
Euler–Maclaurin term repairs this.  For `f(x) = (log x)/x`, convex on `[e^{3/2}, ∞) ⊇ [5, ∞)`
(`convexOn_log_div_id`, `monotoneOn_deriv_log_div_id`), the tangent lines at the two endpoints
lie *below* `f` on `[m, m+1]`, so integrating the tangent at `m` over `[m, m+½]` and the tangent
at `m+1` over `[m+½, m+1]` gives

  `∫_m^{m+1} f ≥ (f(m) + f(m+1))/2 + (f'(m) - f'(m+1))/8`,

i.e. the trapezoid *over*estimates the integral by at most `(f'(m+1) - f'(m))/8` — note that
`f' = (1 - log x)/x²` is negative and increasing here, so the correction is positive.  Summing,
`stieltjesSeqHi m := stieltjesSeqMid m - f'(m)/8` is **antitone** from `m = 5`, with the same
limit `γ₁`, whence `γ₁ ≤ stieltjesSeqHi m`.  Its error is `O((log m)/m³)`; at `m = 16` it is
`0.00009`, against `0.087` for `stieltjesSeq 16`.  (The genuine Euler–Maclaurin constant is
`1/12`, not `1/8`; the tangent-line argument gives up a factor `3/2` in exchange for needing only
convexity, and `1/8` is ample.)
-/

/-- **Integral of an affine function**:
`∫_a^b (c + d (t - e)) dt = c (b - a) + d ((b² - a²)/2 - e (b - a))`.

### Summary of Proof
Split the sum, pull out the constant, and use Mathlib's `integral_id` and
`intervalIntegral.integral_const`; `ring` finishes.

### Lean Notes
Stated in exactly the shape produced by the tangent-line bounds of `log_div_id_tangent_step`,
so that a single `rw` followed by `ring` evaluates each of the two half-interval integrals there.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_div_id_tangent_step`. -/
theorem integral_affine_aux (c d e a b : ℝ) :
    ∫ t in a..b, (c + d * (t - e)) = c * (b - a) + d * ((b ^ 2 - a ^ 2) / 2 - e * (b - a)) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun t : ℝ => d * (t - e)) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun t : ℝ => d * (t - e)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- **One Euler–Maclaurin step for `f(x) = (log x)/x`, `x ≥ 5`:**
`(f(x) + f(x+1))/2 - ∫_x^{x+1} f ≤ (f'(x+1) - f'(x))/8`, with `f' = (1 - log x)/x²`.

### Summary of Proof
By the mean value theorem (`exists_hasDerivAt_eq_slope`) and the monotonicity of `f'` on
`[5, ∞)` (`monotoneOn_deriv_log_div_id`), the tangent line at `x` lies below `f` on `[x, x+1]`
(`htan1`) and so does the tangent line at `x+1` (`htan2`).  Split `∫_x^{x+1} f` at `x + ½`
(`intervalIntegral.integral_add_adjacent_intervals`), bound each half from below by the
corresponding tangent line (`intervalIntegral.integral_mono_on`), and evaluate the two affine
integrals with `integral_affine_aux`: they are `f(x)/2 + f'(x)/8` and `f(x+1)/2 - f'(x+1)/8`.
The exact value of the integral is `integral_log_div_id`; `linarith` assembles the result.

### Lean Notes
`f` and `f'` are introduced with `set` so that the MVT and monotonicity lemmas apply verbatim;
the four `rfl` unfoldings at the end return to the explicit statement.  The `x ≥ 5` hypothesis is
used only through `monotoneOn_deriv_log_div_id` (whose threshold `5 > e^{3/2} = 4.48…` is the
convexity threshold of `f`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_log_div_id`, `monotoneOn_deriv_log_div_id`, `integral_log_div_id`,
`intervalIntegrable_log_div_id`, `integral_affine_aux`.
**Used by:** `stieltjesSeqHi_succ_le`. -/
theorem log_div_id_tangent_step {x : ℝ} (hx : 5 ≤ x) :
    (Real.log x / x + Real.log (x + 1) / (x + 1)) / 2
        - (Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2)
      ≤ ((1 - Real.log (x + 1)) / (x + 1) ^ 2 - (1 - Real.log x) / x ^ 2) / 8 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  set f : ℝ → ℝ := fun t => Real.log t / t with hf
  set f' : ℝ → ℝ := fun t => (1 - Real.log t) / t ^ 2 with hf'
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t := fun t ht => hasDerivAt_log_div_id ht
  have hcont : ∀ a b : ℝ, 0 < a → ContinuousOn f (Set.Icc a b) := by
    intro a b ha t ht
    exact (hderiv t (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  have htan1 : ∀ t ∈ Set.Icc x (x + 1), f x + f' x * (t - x) ≤ f t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; simp
    · obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' h (hcont x t hx0)
        (fun y hy => hderiv y (by linarith [hy.1]))
      have hmono : f' x ≤ f' ξ :=
        monotoneOn_deriv_log_div_id (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (by linarith [hξ.1]))
          hξ.1.le
      have htx : 0 < t - x := by linarith
      have heq : f t - f x = f' ξ * (t - x) := by rw [hξ', div_mul_cancel₀ _ htx.ne']
      have := mul_le_mul_of_nonneg_right hmono htx.le
      linarith
  have htan2 : ∀ t ∈ Set.Icc x (x + 1), f (x + 1) + f' (x + 1) * (t - (x + 1)) ≤ f t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; simp
    · obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' h
        (hcont t (x + 1) (by linarith [ht.1]))
        (fun y hy => hderiv y (by linarith [hy.1, ht.1]))
      have hmono : f' ξ ≤ f' (x + 1) :=
        monotoneOn_deriv_log_div_id (Set.mem_Ici.mpr (by linarith [hξ.1, ht.1]))
          (Set.mem_Ici.mpr (by linarith)) hξ.2.le
      have htx : 0 < x + 1 - t := by linarith
      have heq : f (x + 1) - f t = f' ξ * (x + 1 - t) := by rw [hξ', div_mul_cancel₀ _ htx.ne']
      have := mul_le_mul_of_nonneg_right hmono htx.le
      linarith
  have hint : ∫ t in x..(x + 1), f t = Real.log (x + 1) ^ 2 / 2 - Real.log x ^ 2 / 2 :=
    integral_log_div_id hx0 hx1
  have hi1 : IntervalIntegrable f MeasureTheory.volume x (x + 1 / 2) :=
    intervalIntegrable_log_div_id hx0 (by linarith)
  have hi2 : IntervalIntegrable f MeasureTheory.volume (x + 1 / 2) (x + 1) :=
    intervalIntegrable_log_div_id (by linarith) hx1
  have hsplit : ∫ t in x..(x + 1), f t
      = (∫ t in x..(x + 1 / 2), f t) + ∫ t in (x + 1 / 2)..(x + 1), f t :=
    (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hI1 : ∫ t in x..(x + 1 / 2), (f x + f' x * (t - x)) ≤ ∫ t in x..(x + 1 / 2), f t := by
    apply intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun t : ℝ => f x + f' x * (t - x)).intervalIntegrable _ _) hi1
    intro t ht
    exact htan1 t ⟨ht.1, by linarith [ht.2]⟩
  have hI2 : ∫ t in (x + 1 / 2)..(x + 1), (f (x + 1) + f' (x + 1) * (t - (x + 1)))
      ≤ ∫ t in (x + 1 / 2)..(x + 1), f t := by
    apply intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop :
          Continuous fun t : ℝ => f (x + 1) + f' (x + 1) * (t - (x + 1))).intervalIntegrable
        _ _) hi2
    intro t ht
    exact htan2 t ⟨by linarith [ht.1], ht.2⟩
  have hA1 : ∫ t in x..(x + 1 / 2), (f x + f' x * (t - x)) = f x / 2 + f' x / 8 := by
    rw [integral_affine_aux]; ring
  have hA2 : ∫ t in (x + 1 / 2)..(x + 1), (f (x + 1) + f' (x + 1) * (t - (x + 1)))
      = f (x + 1) / 2 - f' (x + 1) / 8 := by
    rw [integral_affine_aux]; ring
  have hfx : f x = Real.log x / x := rfl
  have hfx1 : f (x + 1) = Real.log (x + 1) / (x + 1) := rfl
  have hf'x : f' x = (1 - Real.log x) / x ^ 2 := rfl
  have hf'x1 : f' (x + 1) = (1 - Real.log (x + 1)) / (x + 1) ^ 2 := rfl
  rw [← hfx, ← hfx1, ← hf'x, ← hf'x1]
  linarith [hint, hsplit, hI1, hI2, hA1, hA2]

/-- **The Euler–Maclaurin upper bracket** `stieltjesSeqHi m = stieltjesSeqMid m - f'(m)/8`, where
`f'(m) = (1 - log m)/m²` is the derivative of `(log x)/x` at `m`.

### Summary of Proof
Definition.  Since `f'(m) < 0` for `m ≥ 3`, this lies *above* `stieltjesSeqMid m`; it decreases
to `γ₁` from `m = 5` (`antitone_stieltjesSeqHi_shift`, `tendsto_stieltjesSeqHi_shift`), so it is
an upper bracket (`stieltjesConstant1_le_stieltjesSeqHi`), with error `O((log m)/m³)`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqMid`.
**Used by:** `antitone_stieltjesSeqHi_shift`, `stieltjesConstant1_le_stieltjesSeqHi`,
`stieltjesSeqHi_succ_le`, `tendsto_stieltjesSeqHi_shift`,
`LogDerivZetaLaurent.stieltjesConstant1_upper_bound`,
`LogDerivZetaLaurent.stieltjesSeqHi_sixteen_eq`. -/
noncomputable def stieltjesSeqHi (m : ℕ) : ℝ :=
  stieltjesSeqMid m - (1 - Real.log m) / (8 * (m : ℝ) ^ 2)

/-- **One step: `stieltjesSeqHi (n+1) ≤ stieltjesSeqHi n` for `n ≥ 5`.**

### Summary of Proof
Unfold: the difference `stieltjesSeqHi (n+1) - stieltjesSeqHi n` equals
`(f(n) + f(n+1))/2 - ∫_n^{n+1} f - (f'(n+1) - f'(n))/8` (by `stieltjesSeq_succ_sub` for the
increment of `stieltjesSeq` and `integral_log_div_id` for the integral), which
`log_div_id_tangent_step` shows is `≤ 0`.

### Lean Notes
The two rewrites `e1`, `e2` put `(1 - log t)/(8 t²)` into the shape `((1 - log t)/t²)/8` of the
tangent-step lemma; `ring` cannot do this on its own because the inverse of a product is atomic to
it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_div_id_tangent_step`, `stieltjesSeq_succ_sub`.
**Used by:** `antitone_stieltjesSeqHi_shift`. -/
theorem stieltjesSeqHi_succ_le {n : ℕ} (hn : 5 ≤ n) :
    stieltjesSeqHi (n + 1) ≤ stieltjesSeqHi n := by
  have hxn : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := log_div_id_tangent_step hxn
  have hsub := stieltjesSeq_succ_sub n
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  simp only [stieltjesSeqHi, stieltjesSeqMid]
  push_cast
  have e1 : ((1 : ℝ) - Real.log ((n : ℝ) + 1)) / (8 * ((n : ℝ) + 1) ^ 2)
      = ((1 - Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2) / 8 := by
    rw [div_div, mul_comm]
  have e2 : ((1 : ℝ) - Real.log (n : ℝ)) / (8 * (n : ℝ) ^ 2)
      = ((1 - Real.log (n : ℝ)) / (n : ℝ) ^ 2) / 8 := by
    rw [div_div, mul_comm]
  rw [e1, e2]
  linarith [h, hsub]

/-- **`k ↦ stieltjesSeqHi (k + 5)` is antitone.**

### Summary of Proof
`antitone_nat_of_succ_le` from `stieltjesSeqHi_succ_le`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqHi_succ_le`.
**Used by:** `stieltjesConstant1_le_stieltjesSeqHi`. -/
theorem antitone_stieltjesSeqHi_shift : Antitone (fun k : ℕ => stieltjesSeqHi (k + 5)) :=
  antitone_nat_of_succ_le fun k => by
    simpa [show k + 1 + 5 = k + 5 + 1 from by omega] using
      stieltjesSeqHi_succ_le (n := k + 5) (by omega)

/-- **`stieltjesSeqHi (k + 5) → γ₁`.**

### Summary of Proof
`stieltjesSeqHi` differs from `stieltjesSeq` by `(log m)/(2m) + (1 - log m)/(8m²)`, and both
pieces tend to `0`: the first by `tendsto_log_div_id_atTop`, the second as the product
`(1/m - (log m)/m) · (1/m) / 8` of null sequences.  Then `tendsto_stieltjesSeq`.

### Lean Notes
The proof of the `stieltjesSeqMid` limit is repeated inline (as `hmid`) rather than extracted,
since `stieltjesSeqMid_le_stieltjesConstant1` also keeps it inline; both are six lines.

### References
No tex counterpart.

### Dependencies
**Depends on:** `tendsto_stieltjesSeq`, `tendsto_log_div_id_atTop`.
**Used by:** `stieltjesConstant1_le_stieltjesSeqHi`. -/
theorem tendsto_stieltjesSeqHi_shift :
    Filter.Tendsto (fun k : ℕ => stieltjesSeqHi (k + 5)) Filter.atTop
      (nhds stieltjesConstant1) := by
  have hmid : Filter.Tendsto (fun k : ℕ => stieltjesSeqMid (k + 5)) Filter.atTop
      (nhds stieltjesConstant1) := by
    have hlog : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 5) / ((k : ℝ) + 5) / 2)
        Filter.atTop (nhds 0) := by
      have h := (tendsto_log_div_id_atTop.comp
        (Filter.tendsto_atTop_add_const_right _ 5 tendsto_natCast_atTop_atTop)).div_const 2
      simpa using h
    have hsub := ((Filter.tendsto_add_atTop_iff_nat 5).mpr tendsto_stieltjesSeq).sub hlog
    rw [sub_zero] at hsub
    refine hsub.congr fun k => ?_
    simp only [stieltjesSeqMid]
    push_cast
    ring
  have hcorr : Filter.Tendsto (fun k : ℕ => (1 - Real.log ((k : ℝ) + 5)) / (8 * ((k : ℝ) + 5) ^ 2))
      Filter.atTop (nhds 0) := by
    have hbig : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 5) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 5 tendsto_natCast_atTop_atTop
    have h1 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 5)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hbig
    have h2 : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 5) / ((k : ℝ) + 5))
        Filter.atTop (nhds 0) :=
      tendsto_log_div_id_atTop.comp hbig
    have h3 := ((h1.sub h2).mul h1).div_const 8
    simp only [sub_zero, zero_mul, zero_div] at h3
    refine h3.congr fun k => ?_
    have : (0 : ℝ) < (k : ℝ) + 5 := by positivity
    field_simp
  have := hmid.sub hcorr
  rw [sub_zero] at this
  refine this.congr fun k => ?_
  simp only [stieltjesSeqHi]
  push_cast
  ring

/-- **Refined upper bracket: `γ₁ ≤ stieltjesSeq m - (log m)/(2m) - (1 - log m)/(8m²)` for every
`m ≥ 5`.**

### Summary of Proof
The shifted `stieltjesSeqHi` is antitone (`antitone_stieltjesSeqHi_shift`) and converges to `γ₁`
(`tendsto_stieltjesSeqHi_shift`), so it stays above its limit.

### Lean Notes
Use this in place of `stieltjesConstant1_le_stieltjesSeq` (error `(log m)/(2m)`) wherever
precision matters: at `m = 16` the gap `stieltjesSeqHi 16 - γ₁` is `0.000089`, so the numeric
claim `γ² + 2γ₁ ≤ 0.20` of `Background.LogDerivZetaLaurent.stieltjes_combo_upper_bound` needs
only the logarithms of the six primes `≤ 16`, where the coarser bracket would need `m ≈ 800` and
139 primes.

### References
No tex counterpart.

### Dependencies
**Depends on:** `antitone_stieltjesSeqHi_shift`, `tendsto_stieltjesSeqHi_shift`.
**Used by:** `Background.LogDerivZetaLaurent.stieltjesConstant1_upper_bound`. -/
theorem stieltjesConstant1_le_stieltjesSeqHi {m : ℕ} (hm : 5 ≤ m) :
    stieltjesConstant1 ≤ stieltjesSeqHi m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  exact antitone_stieltjesSeqHi_shift.le_of_tendsto tendsto_stieltjesSeqHi_shift j

/-! ### Numerical consequences

Everything about `γ₁` now reduces to finite sums of logarithms: `stieltjesSeqMid m ≤ γ₁ ≤
stieltjesSeqHi m` for `m ≥ 5`, with the two brackets `O((log m)/m²)` and `O((log m)/m³)` from
`γ₁`.  The lower numeric residue is proved here; the upper one, which needs the logarithms of the
primes up to `13`, is in `Background.LogDerivZetaLaurent`.
-/

/-- **`stieltjesSeqMid 5 = log 2 + (log 3)/3 + (log 5)/10 - (log 5)²/2`.**

### Summary of Proof
Expand the five-term sum.  The `k = 1` term vanishes (`log 1 = 0`) and the `k = 4` term is
`(log 4)/4 = (2 log 2)/4 = (log 2)/2`, which combines with the `k = 2` term `(log 2)/2` to give
`log 2`.  The `k = 5` term `(log 5)/5` combines with the subtracted `(log 5)/(2·5)` to give
`(log 5)/10`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqMid`, `stieltjesSeq`.
**Used by:** `neg_one_eighth_lt_stieltjesSeqMid_five`,
`Background.LogDerivZetaLaurent.stieltjesConstant1_lower_bound`. -/
theorem stieltjesSeqMid_five_eq :
    stieltjesSeqMid 5
      = Real.log 2 + Real.log 3 / 3 + Real.log 5 / 10 - Real.log 5 ^ 2 / 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  simp only [stieltjesSeqMid, stieltjesSeq, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [h4]
  ring

/-- **`-1/8 < γ₁`.**

### Summary of Proof
A finite computation: the value of `stieltjesSeqMid 5` is `-0.07485012896…`.  Writing it via
`stieltjesSeqMid_five_eq` as
`log 2 + (log 3)/3 + (log 5)/10 - (log 5)²/2`, three cheap bounds suffice:

* `log 2 > 0.6931471803` (`Real.log_two_gt_d9`) and `log 2 < 0.6931471808`
  (`Real.log_two_lt_d9`);
* `log 3 ≥ log 2 + 1/3`, from `Real.log_le_sub_one_of_pos` at `2/3`;
* `log 5 ≤ 2 log 2 + 1/8 + 1/9 < 1.6225`, from the factorisation `5 = 4·(9/8)·(10/9)` and
  `Real.log_le_sub_one_of_pos` at `9/8` and at `10/9`.

Since `c ↦ c/10 - c²/2` is decreasing for `c ≥ 1/10`, the upper bound on `log 5` is the worst
case, and the three bounds give `stieltjesSeqMid 5 > -0.11855`, comfortably above `-1/8`.

### Lean Notes
The margin is `0.0064`, which is why the crude `log 5 ≤ 2 log 2 + 1/4` (from a single application
of `log x ≤ x - 1` at `5/4`) is *not* enough: it only yields `> -0.1486`.  Splitting `5/4` as
`(9/8)(10/9)` is what buys the margin.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesSeqMid_five_eq`.
**Used by:** `neg_one_eighth_lt_stieltjesConstant1`, and through it
`Jensen.JensenBounds.stieltjes_combo_pos`. -/
theorem neg_one_eighth_lt_stieltjesSeqMid_five : -(1 / 8 : ℝ) < stieltjesSeqMid 5 := by
  rw [stieltjesSeqMid_five_eq]
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 2 + 1 / 3 ≤ Real.log 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    linarith
  have h98 : Real.log (9 / 8) ≤ 1 / 8 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
    linarith
  have h109 : Real.log (10 / 9) ≤ 1 / 9 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
    linarith
  have hsplit : Real.log 5 = Real.log 4 + Real.log (9 / 8) + Real.log (10 / 9) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hc : Real.log 5 ≤ 1.6225 := by
    rw [hsplit, h4]
    linarith
  have hcnn : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hcnn (sub_nonneg.2 hc), h2lo, h3]

/-- **`-1/8 < γ₁`**, in terms of `stieltjesConstant1` itself.

### Summary of Proof
`neg_one_eighth_lt_stieltjesSeqMid_five` combined with the refined lower bracket
`stieltjesSeqMid_le_stieltjesConstant1` at `m = 5`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `neg_one_eighth_lt_stieltjesSeqMid_five`, `stieltjesSeqMid_le_stieltjesConstant1`.
**Used by:** `JensenBounds.c4IntegrandBound_abs_le`, `JensenBounds.stieltjes_combo_pos`. -/
theorem neg_one_eighth_lt_stieltjesConstant1 : -(1 / 8 : ℝ) < stieltjesConstant1 :=
  neg_one_eighth_lt_stieltjesSeqMid_five.trans_le
    (stieltjesSeqMid_le_stieltjesConstant1 (by norm_num))

