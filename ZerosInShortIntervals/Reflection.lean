/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Background.LogDerivZetaLaurent

/-! # The reflection `ρ ↦ 1 - conj ρ` and the factor of two in the proportion statements

Every proportion statement in the paper reads the count `2N(T₁,T₂,α)` as "the zeros of the window
that are NOT in the strip `α ≤ Re ρ ≤ 1-α`", i.e. it asserts

  #{ρ : T₁ < Im ρ ≤ T₂, Re ρ < α}  =  #{ρ : T₁ < Im ρ ≤ T₂, Re ρ > 1-α}  =  N(T₁,T₂,α)

with multiplicity.  The tex leaves this implicit; it is the content of this file.

The map is `refl ρ = 1 - conj ρ`.  It is an involution of `ℂ`, it fixes `Im` (because conjugation
negates it and `1 - ·` negates it again) and it reflects `Re` about `1/2`, so it carries the left
edge strip of a window onto the right edge strip of the *same* window.  What has to be proved is
that it preserves the order of vanishing, and that is the author's observation: the functional
equation

  `ζ (1-s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)`      (`riemannZeta_one_sub`)

has a multiplier (`zetaFE`) that is analytic and **nonvanishing** off the real axis — `Γ` has no
zeros at all, `(2π)^{-s}` is an exponential, and the zeros of `cos(πs/2)` are the odd integers,
all real — so `ζ(1-s)` and `ζ(s)` vanish to the same order there.  Conjugation preserves the order
for the usual Schwarz-reflection reason (`riemannZeta_conj`, plus the fact that `conj ∘ g ∘ conj`
is analytic wherever `g` is).

Contents:
* `analyticOrderAt_conj_comp`, `zetaOrd_conj` — the conjugation half;
* `zetaFE`, `zetaFE_ne_zero`, `analyticAt_zetaFE`, `zetaOrd_one_sub` — the functional-equation half;
* `zetaOrd_reflect` — the two combined;
* `NrectLeft`, `NrectLeft_eq_Nrect` and `NlineReLeft`, `NlineReLeft_eq_NlineRe` — the counting
  consequence, for the rectangle and for a horizontal line.

The three-way split of a window into left edge, middle and right edge, and the restatement of
Corollary `\ref{cor:simpmain}` (Corollary 1) that it licenses, are in `HalvingConvention.lean`,
which is where the half-counting convention lives. -/

open Complex Filter Topology

set_option linter.unusedSectionVars false

/-! ### Conjugation -/

/-- **`conj ∘ f ∘ conj` is analytic at `s` whenever `f` is analytic at `conj s`.**

### Summary of Proof
`f` is differentiable on a neighbourhood of `conj s` (`AnalyticAt.eventually_analyticAt`), so
`conj ∘ f ∘ conj` is differentiable on the conjugate neighbourhood by
`differentiableAt_conj_conj_iff`, and `DifferentiableOn.analyticAt` upgrades that to analyticity.

### Lean Notes
Stated for the literal composition `⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)`, which is the shape
`differentiableAt_conj_conj_iff` is stated in.

### References
No tex counterpart; the tex does not prove the reflection step.

### Dependencies
**Depends on:** none.
**Used by:** `analyticOrderAt_conj_comp`. -/
theorem analyticAt_conj_comp {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) s)) :
    AnalyticAt ℂ (⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)) s := by
  have hmem : {y : ℂ | DifferentiableAt ℂ f y} ∈ 𝓝 ((starRingEnd ℂ) s) := by
    filter_upwards [hf.eventually_analyticAt] with y hy using hy.differentiableAt
  have hpre : (⇑(starRingEnd ℂ) ⁻¹' {y : ℂ | DifferentiableAt ℂ f y}) ∈ 𝓝 s :=
    (Complex.continuous_conj.tendsto s) hmem
  exact DifferentiableOn.analyticAt (s := ⇑(starRingEnd ℂ) ⁻¹' {y | DifferentiableAt ℂ f y})
    (fun z hz => (differentiableAt_conj_conj_iff.mpr hz).differentiableWithinAt) hpre

/-- **The order of vanishing is carried along by conjugation:**
`analyticOrderAt (conj ∘ f ∘ conj) s = analyticOrderAt f (conj s)`.

### Summary of Proof
Case on the order at `conj s`.  If it is `⊤`, `f` vanishes on a neighbourhood of `conj s`, hence
`conj ∘ f ∘ conj` vanishes on a neighbourhood of `s` (push the eventual statement through the
continuous map `conj`).  If it is `n : ℕ`, write `f z = (z - conj s)^n • g z` near `conj s` with
`g` analytic and `g (conj s) ≠ 0` (`AnalyticAt.analyticOrderAt_eq_natCast`); then
`conj ∘ g ∘ conj` is the corresponding factor at `s`, since conjugating
`f (conj z) = (conj z - conj s)^n • g (conj z)` gives
`conj (f (conj z)) = (z - s)^n • conj (g (conj z))`.

### Lean Notes
No analyticity hypothesis is needed in the `⊤` branch, but one is needed in the `n` branch (order
`0` does not imply analyticity: `analyticOrderAt_eq_zero` also holds when `f` is not analytic at
the point).  Since the only application is to `ζ`, the hypothesis is simply assumed.

### Dependencies
**Depends on:** `analyticAt_conj_comp`.
**Used by:** `zetaOrd_conj`. -/
theorem analyticOrderAt_conj_comp {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) s)) :
    analyticOrderAt (⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)) s
      = analyticOrderAt f ((starRingEnd ℂ) s) := by
  have hconj : AnalyticAt ℂ (⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)) s := analyticAt_conj_comp hf
  have htend : Tendsto (⇑(starRingEnd ℂ)) (𝓝 s) (𝓝 ((starRingEnd ℂ) s)) :=
    Complex.continuous_conj.tendsto s
  cases h : analyticOrderAt f ((starRingEnd ℂ) s) with
  | top =>
    rw [analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [htend.eventually h] with z hz
    simp [Function.comp_def, hz]
  | coe n =>
    obtain ⟨g, hg_an, hg_ne, hgeq⟩ := hf.analyticOrderAt_eq_natCast.mp h
    refine hconj.analyticOrderAt_eq_natCast.mpr
      ⟨⇑(starRingEnd ℂ) ∘ g ∘ ⇑(starRingEnd ℂ), analyticAt_conj_comp hg_an, ?_, ?_⟩
    · simpa [Function.comp_def] using hg_ne
    · filter_upwards [htend.eventually hgeq] with z hz
      simp only [Function.comp_apply, hz, smul_eq_mul, map_mul, map_pow, map_sub,
        Complex.conj_conj]

/-- **`ζ` vanishes to the same order at `conj s` as at `s`.**

### Summary of Proof
`riemannZeta_conj` says `ζ (conj z) = conj (ζ z)`, so `conj ∘ ζ ∘ conj = ζ` as functions; apply
`analyticOrderAt_conj_comp` at `conj s` and rewrite.

### Lean Notes
The hypothesis is only `s ≠ 1`, needed so that `ζ` is analytic at `s` (and hence at `conj s`).

### Dependencies
**Depends on:** `analyticOrderAt_conj_comp`, `Definitions.zetaOrd`.
**Used by:** `zetaOrd_reflect`. -/
theorem zetaOrd_conj {s : ℂ} (hs : s ≠ 1) : zetaOrd ((starRingEnd ℂ) s) = zetaOrd s := by
  have han : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  have key : analyticOrderAt (⇑(starRingEnd ℂ) ∘ riemannZeta ∘ ⇑(starRingEnd ℂ))
      ((starRingEnd ℂ) s) = analyticOrderAt riemannZeta s := by
    have := analyticOrderAt_conj_comp (f := riemannZeta) (s := (starRingEnd ℂ) s)
      (by simpa using han)
    simpa using this
  have hfun : (⇑(starRingEnd ℂ) ∘ riemannZeta ∘ ⇑(starRingEnd ℂ)) = riemannZeta := by
    funext z
    simp [Function.comp_def, riemannZeta_conj]
  rw [hfun] at key
  unfold zetaOrd
  rw [key]

/-! ### The functional equation -/

/-- **The multiplier of the functional equation:** `2 (2π)^{-s} Γ(s) cos(πs/2)`, so that
`ζ(1-s) = zetaFE s · ζ(s)` (`riemannZeta_one_sub`).

### Summary of Proof
A definition.

### References
tex: the functional equation is used implicitly wherever the paper doubles `N(T₁,T₂,α)`.

### Dependencies
**Depends on:** none.
**Used by:** `zetaFE_ne_zero`, `differentiableAt_zetaFE`, `analyticAt_zetaFE`,
`zetaOrd_one_sub`. -/
noncomputable def zetaFE (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

/-- **A point off the real axis is not a non-positive integer.**

### Summary of Proof
`(-(m : ℂ)).im = 0`.

### Dependencies
**Depends on:** none.
**Used by:** `zetaFE_ne_zero`, `differentiableAt_zetaFE`, `zetaOrd_one_sub`. -/
theorem ne_neg_natCast_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : ∀ m : ℕ, s ≠ -(m : ℂ) := by
  intro m h
  rw [h] at hs
  simp at hs

/-- **The functional-equation multiplier is nonvanishing off the real axis.**

### Summary of Proof
Four factors.  `2 ≠ 0`; `(2π)^{-s} ≠ 0` because the base is nonzero (`Complex.cpow_ne_zero_iff`);
`Γ(s) ≠ 0` always, given that `s` is not a non-positive integer (`Complex.Gamma_ne_zero`); and
`cos(πs/2) ≠ 0` because `Complex.cos_ne_zero_iff` puts its zeros at `(2k+1)π/2`, which are real,
while `πs/2` has imaginary part `π·Im(s)/2 ≠ 0`.

### Lean Notes
This is the whole content of the reflection step, and the reason it is "immediate": the
multiplier never vanishes where the nontrivial zeros live.

### References
tex: no counterpart; the doubling is asserted without proof.

### Dependencies
**Depends on:** `zetaFE`, `ne_neg_natCast_of_im_ne_zero`.
**Used by:** `zetaOrd_one_sub`. -/
theorem zetaFE_ne_zero {s : ℂ} (hs : s.im ≠ 0) : zetaFE s ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  have h2 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (ne_neg_natCast_of_im_ne_zero hs)
  have h3 : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have him := congrArg Complex.im hk
    simp only [div_ofNat_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, add_re, mul_re,
      re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero, sub_zero, one_re, add_im, one_im,
      zero_div, div_eq_zero_iff, mul_eq_zero, Real.pi_ne_zero, false_or, OfNat.ofNat_ne_zero,
      or_false] at him
    exact hs him
  simp only [zetaFE, ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨two_ne_zero, h1⟩, h2⟩, h3⟩

/-- **The multiplier is differentiable off the real axis.**

### Summary of Proof
`DifferentiableAt.const_cpow` for `(2π)^{-s}`, `Complex.differentiableAt_Gamma` (whose hypothesis
is again that `s` is not a non-positive integer), and `Complex.differentiable_cos` composed with
an affine map.

### Dependencies
**Depends on:** `zetaFE`, `ne_neg_natCast_of_im_ne_zero`.
**Used by:** `analyticAt_zetaFE`. -/
theorem differentiableAt_zetaFE {s : ℂ} (hs : s.im ≠ 0) : DifferentiableAt ℂ zetaFE s := by
  have hc : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    DifferentiableAt.const_cpow differentiable_neg.differentiableAt
      (Or.inl (by simp [Real.pi_ne_zero]))
  have hg : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (ne_neg_natCast_of_im_ne_zero hs)
  have hk : DifferentiableAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s :=
    (Complex.differentiable_cos _).comp s (by fun_prop)
  exact (((differentiableAt_const _).mul hc).mul hg).mul hk

/-- **The open half-planes off the real axis.**

### Summary of Proof
Preimage of the open set `{0}ᶜ` under the continuous map `Im`.

### Dependencies
**Depends on:** none.
**Used by:** `analyticAt_zetaFE`, `zetaOrd_one_sub`. -/
theorem isOpen_im_ne_zero : IsOpen {z : ℂ | z.im ≠ 0} :=
  isOpen_compl_singleton.preimage Complex.continuous_im

/-- **The multiplier is analytic off the real axis.**

### Summary of Proof
`differentiableAt_zetaFE` on the open set `{Im ≠ 0}`, then `DifferentiableOn.analyticAt`.

### Dependencies
**Depends on:** `differentiableAt_zetaFE`, `isOpen_im_ne_zero`.
**Used by:** `zetaOrd_one_sub`. -/
theorem analyticAt_zetaFE {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ zetaFE s :=
  DifferentiableOn.analyticAt (s := {z : ℂ | z.im ≠ 0})
    (fun _ hz => (differentiableAt_zetaFE hz).differentiableWithinAt)
    (isOpen_im_ne_zero.mem_nhds hs)

/-- **`ζ` vanishes to the same order at `1 - s` as at `s`, off the real axis.**

### Summary of Proof
`analyticOrderAt_comp_of_deriv_ne_zero` for the affine substitution `z ↦ 1 - z` (whose derivative
is `-1`) turns the order at `1 - s` into the order of `ζ ∘ (1 - ·)` at `s`.  On the open set
`{Im ≠ 0}` the functional equation gives `ζ ∘ (1 - ·) = zetaFE · ζ` (every point there is neither
a non-positive integer nor `1`), so `analyticOrderAt_congr` applies; then `analyticOrderAt_mul`
splits the product and `zetaFE`'s order is `0` because it does not vanish.

### Lean Notes
This is where the author's "immediate from non-vanishing of the other factors" is discharged.

### References
tex: implicit in every `2N(t-h,t+h,α)`.

### Dependencies
**Depends on:** `zetaFE`, `zetaFE_ne_zero`, `analyticAt_zetaFE`, `isOpen_im_ne_zero`,
`ne_neg_natCast_of_im_ne_zero`, `Definitions.zetaOrd`.
**Used by:** `zetaOrd_reflect`. -/
theorem zetaOrd_one_sub {s : ℂ} (hs : s.im ≠ 0) : zetaOrd (1 - s) = zetaOrd s := by
  have hs1 : s ≠ 1 := fun h => hs (by rw [h]; simp)
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) s := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) s ≠ 0 := by simp
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hg hg'
  have heq : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[𝓝 s] (zetaFE * riemannZeta) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
    simp only [Function.comp_apply, Pi.mul_apply, zetaFE]
    exact riemannZeta_one_sub (ne_neg_natCast_of_im_ne_zero hz) (fun h => hz (by rw [h]; simp))
  unfold zetaOrd
  rw [← hcomp, analyticOrderAt_congr heq, analyticOrderAt_mul (analyticAt_zetaFE hs) hζ,
    analyticOrderAt_eq_zero.mpr (Or.inr (zetaFE_ne_zero hs)), zero_add]

/-- **The reflection `ρ ↦ 1 - conj ρ` preserves the order of vanishing of `ζ` off the real axis.**

### Summary of Proof
`zetaOrd_one_sub` at `conj s` (whose imaginary part is `-Im s ≠ 0`), then `zetaOrd_conj`.

### Lean Notes
The map fixes the imaginary part — `(1 - conj s).im = s.im` — and sends `Re` to `1 - Re`, so it
carries `{Re < α}` onto `{Re > 1-α}` within one and the same horizontal window.  That is the
factor of two.

### References
tex: implicit in every `2N(t-h,t+h,α)`.

### Dependencies
**Depends on:** `zetaOrd_one_sub`, `zetaOrd_conj`.
**Used by:** `NrectLeft_eq_Nrect`, `NlineReLeft_eq_NlineRe`. -/
theorem zetaOrd_reflect {s : ℂ} (hs : s.im ≠ 0) :
    zetaOrd (1 - (starRingEnd ℂ) s) = zetaOrd s := by
  have hcs : ((starRingEnd ℂ) s).im ≠ 0 := by simpa using hs
  have hs1 : s ≠ 1 := fun h => hs (by rw [h]; simp)
  rw [zetaOrd_one_sub hcs, zetaOrd_conj hs1]

/-! ### The counting consequence -/

/-- **The reflection as a permutation of `ℂ`:** `ρ ↦ 1 - conj ρ`.

### Summary of Proof
An involution: `1 - conj (1 - conj z) = 1 - (1 - z) = z`.

### Lean Notes
Packaged as an `Equiv` so that `finsum_comp_equiv` can reindex the counting `finsum`s along it.

### Dependencies
**Depends on:** none.
**Used by:** `NlineReLeft_eq_NlineRe`, `NrectLeft_eq_Nrect`, `reflectEquiv_apply`. -/
def reflectEquiv : ℂ ≃ ℂ :=
  Function.Involutive.toPerm (fun z => 1 - (starRingEnd ℂ) z) (by intro z; simp)

@[simp] theorem reflectEquiv_apply (z : ℂ) : reflectEquiv z = 1 - (starRingEnd ℂ) z := rfl

/-- **`NrectLeft T₁ T₂ α` counts the zeros of the window on the LEFT edge strip `Re ρ < α`**, with
multiplicity — the mirror image of `Definitions.Nrect`.

### Summary of Proof
A definition, with the same divisor as `Nrect`.

### References
tex: the zeros the paper's `2N(T₁,T₂,α)` counts alongside `N(T₁,T₂,α)`.

### Dependencies
**Depends on:** none.
**Used by:** `NrectLeft_eq_Nrect`, `NrectMid_eq`, `Nrect_one_eq_add`. -/
noncomputable def NrectLeft (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} u

/-- **`ζ` is analytic on the left edge strip of a window at positive height.**

### Summary of Proof
`analyticOnNhd_riemannZeta_of_im_pos`; every point has `Im > T₁ > 0`, so the pole at `1` is
excluded.

### Dependencies
**Depends on:** `Definitions.analyticOnNhd_riemannZeta_of_im_pos`.
**Used by:** `NrectLeft_eq_Nrect`, `Nrect_one_eq_add`. -/
theorem analyticOnNhd_riemannZeta_rectLeft {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} :=
  analyticOnNhd_riemannZeta_of_im_pos (fun _ hs => hT₁.trans hs.1)

/-- **The factor of two: `NrectLeft T₁ T₂ α = Nrect T₁ T₂ α` for `T₁ > 0`.**

### Summary of Proof
Reindex the `Nrect` sum along `reflectEquiv` (`finsum_comp_equiv`) and compare pointwise.  Writing
both divisors through `divisor_riemannZeta_eq_ite`, membership matches because
`(1 - conj u).im = u.im` and `(1 - conj u).re = 1 - u.re`, so `1 - α < 1 - u.re ↔ u.re < α`; and
the two orders agree by `zetaOrd_reflect`, whose hypothesis `Im u ≠ 0` holds on the window because
`T₁ > 0`.

### Lean Notes
Both `if`-branches are handled at once: off the left strip both indicators are `0`, and on it
`Im u > T₁ > 0`.

### References
tex: the step the paper leaves implicit when it writes the count of zeros outside
`[α, 1-α]` as `2N(T₁,T₂,α)`.

### Dependencies
**Depends on:** `NrectLeft`, `Definitions.Nrect`, `zetaOrd_reflect`, `reflectEquiv`,
`Definitions.divisor_riemannZeta_eq_ite`, `analyticOnNhd_riemannZeta_rectLeft`,
`Definitions.analyticOnNhd_riemannZeta_rect`.
**Used by:** `HalvingConvention.NrectMid_eq`. -/
theorem NrectLeft_eq_Nrect {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) :
    NrectLeft T₁ T₂ α = Nrect T₁ T₂ α := by
  have hL := analyticOnNhd_riemannZeta_rectLeft (T₂ := T₂) (α := α) hT₁
  have hR := analyticOnNhd_riemannZeta_rect (T2 := T₂) (γ := 1 - α) hT₁
  unfold NrectLeft Nrect
  rw [← finsum_comp_equiv reflectEquiv
    (f := fun u => MeromorphicOn.divisor riemannZeta
      {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} u)]
  refine finsum_congr fun u => ?_
  rw [divisor_riemannZeta_eq_ite hL, divisor_riemannZeta_eq_ite hR]
  have him : (reflectEquiv u).im = u.im := by simp
  have hre : (reflectEquiv u).re = 1 - u.re := by simp
  by_cases hu : u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α}
  · have hmem : (reflectEquiv u) ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} := by
      refine ⟨by rw [him]; exact hu.1, by rw [him]; exact hu.2.1, ?_⟩
      rw [hre]; linarith [hu.2.2]
    have hzero : u.im ≠ 0 := ne_of_gt (hT₁.trans hu.1)
    rw [ite_eq_left hu, ite_eq_left hmem, reflectEquiv_apply, zetaOrd_reflect hzero]
  · have hmem : (reflectEquiv u) ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} := by
      intro h
      exact hu ⟨by rw [← him]; exact h.1, by rw [← him]; exact h.2.1, by
        have := h.2.2; rw [hre] at this; linarith⟩
    rw [ite_eq_right hu, ite_eq_right hmem]

/-- **`NlineReLeft T α` counts the zeros ON the horizontal line `Im ρ = T` with `Re ρ < α`.**

### Summary of Proof
A definition, the left-edge mirror of `Definitions.NlineRe`.

### References
tex: page 1, the half-multiplicity convention for boundary zeros, on the left edge strip.

### Dependencies
**Depends on:** none.
**Used by:** `NlineReLeft_eq_NlineRe`, `NlineReMid_eq`, `NlineRe_one_eq_add`. -/
noncomputable def NlineReLeft (T α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ s.re < α} u

/-- **`ζ` is analytic on the left half of a horizontal line at positive height.**

### Summary of Proof
`analyticOnNhd_riemannZeta_of_im_pos`.

### Dependencies
**Depends on:** `Definitions.analyticOnNhd_riemannZeta_of_im_pos`.
**Used by:** `NlineReLeft_eq_NlineRe`, `NlineRe_one_eq_add`. -/
theorem analyticOnNhd_riemannZeta_lineLeft {T α : ℝ} (hT : 0 < T) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.im = T ∧ s.re < α} :=
  analyticOnNhd_riemannZeta_of_im_pos (fun _ hs => by rw [hs.1]; exact hT)

/-- **The factor of two on an edge: `NlineReLeft T α = NlineRe T α` for `T > 0`.**

### Summary of Proof
`NrectLeft_eq_Nrect`'s argument verbatim; the reflection fixes `Im`, so it preserves the line
`Im ρ = T`.

### References
tex: page 1, the half-multiplicity convention.

### Dependencies
**Depends on:** `NlineReLeft`, `Definitions.NlineRe`, `zetaOrd_reflect`, `reflectEquiv`,
`Definitions.divisor_riemannZeta_eq_ite`, `analyticOnNhd_riemannZeta_lineLeft`,
`Definitions.analyticOnNhd_riemannZeta_line`.
**Used by:** `NlineReMid_eq`. -/
theorem NlineReLeft_eq_NlineRe {T α : ℝ} (hT : 0 < T) :
    NlineReLeft T α = NlineRe T α := by
  have hL := analyticOnNhd_riemannZeta_lineLeft (α := α) hT
  have hR := analyticOnNhd_riemannZeta_line (γ := 1 - α) hT
  unfold NlineReLeft NlineRe
  rw [← finsum_comp_equiv reflectEquiv
    (f := fun u => MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ 1 - α < s.re} u)]
  refine finsum_congr fun u => ?_
  rw [divisor_riemannZeta_eq_ite hL, divisor_riemannZeta_eq_ite hR]
  have him : (reflectEquiv u).im = u.im := by simp
  have hre : (reflectEquiv u).re = 1 - u.re := by simp
  by_cases hu : u ∈ {s : ℂ | s.im = T ∧ s.re < α}
  · have hmem : (reflectEquiv u) ∈ {s : ℂ | s.im = T ∧ 1 - α < s.re} := by
      refine ⟨by rw [him]; exact hu.1, by rw [hre]; linarith [hu.2]⟩
    have hzero : u.im ≠ 0 := by rw [hu.1]; exact ne_of_gt hT
    rw [ite_eq_left hu, ite_eq_left hmem, reflectEquiv_apply, zetaOrd_reflect hzero]
  · have hmem : (reflectEquiv u) ∉ {s : ℂ | s.im = T ∧ 1 - α < s.re} := by
      intro h
      exact hu ⟨by rw [← him]; exact h.1, by have := h.2; rw [hre] at this; linarith⟩
    rw [ite_eq_right hu, ite_eq_right hmem]

/-! ### Splitting a window into left edge, middle and right edge

Everything above this point is unconditional: the order-of-vanishing results and the
edge-strip identities use nothing but Mathlib.  From here on the arguments need to know that a
zero with non-positive real part is a trivial zero, which `LogDerivZetaLaurent` derives from a
literature input, so the statements below carry the hypothesis classes of
`ZerosInShortIntervals/Hypotheses.lean`. -/

variable [LiteratureInputs] [BrentStirlingInputs]

/-- **Support finiteness for the divisor of `ζ` on any region inside a horizontal strip at
positive height.**

### Summary of Proof
`Nrect_divisor_support_finite`'s argument, with the real part pinned from both sides for a zero:
`riemannZeta_ne_zero_of_one_lt_re` gives `Re ρ ≤ 1`, and `riemannZeta_eq_zero_of_re_nonpos` gives
`0 < Re ρ` (a zero with `Re ≤ 0` is a trivial zero, which is real, and the strip has `Im > 0`).
So the support lies in the compact box `[0,1] × [T₁,T₂]` intersected with the zero set, which is
finite by `IsCompact.inter_riemannZetaZeros_finite`.

### Lean Notes
Stated for an arbitrary `U` inside the strip so that the left edge strip, the middle strip and the
horizontal lines all reuse it; `Definitions.Nrect_divisor_support_finite` is the special case its
own box `[γ,1] × [T₁,T₂]` covers.

### Dependencies
**Depends on:** `Background.LogDerivZetaLaurent.riemannZeta_eq_zero_of_re_nonpos`.
**Used by:** `NlineRe_one_eq_add`, `Nrect_one_eq_add`. -/
theorem divisor_support_finite_of_subset_strip {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) {U : Set ℂ}
    (hU : U ⊆ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂}) (hUan : AnalyticOnNhd ℂ riemannZeta U) :
    (Function.support (fun u => MeromorphicOn.divisor riemannZeta U u)).Finite := by
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc T₁ T₂) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  refine (hKcompact.inter_riemannZetaZeros_finite).subset fun u hu => ?_
  simp only [Function.mem_support] at hu
  have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain hu
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hUan huU] at hu
  have hzero : riemannZeta u = 0 := by
    by_contra hne
    rw [(hUan u huU).analyticOrderAt_eq_zero.mpr hne] at hu
    simp at hu
  have hstrip := hU huU
  have hre1 : u.re ≤ 1 := by
    by_contra hgt
    exact riemannZeta_ne_zero_of_one_lt_re (not_le.mp hgt) hzero
  have hre0 : 0 ≤ u.re := by
    by_contra hlt
    obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos (le_of_not_ge hlt) hzero
    have : u.im = 0 := by rw [hn]; simp
    have := hstrip.1
    linarith
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨hre0, hre1⟩, hstrip.1.le, hstrip.2⟩, hzero⟩

/-- **`NrectMid T₁ T₂ α` counts the zeros of the window with `α ≤ Re ρ ≤ 1-α`**, with
multiplicity — the quantity the paper's proportion statements are really about.

### Summary of Proof
A definition, with the same divisor as `Nrect`.

### References
tex: the numerator of `\ref{cor:simpmain}` (Corollary 1) read as the tex's prose reads it.

### Dependencies
**Depends on:** none.
**Used by:** `NrectMid_eq`, `Nrect_one_eq_add`, `HalvingConvention.NhalfMid`,
`HalvingConvention.NhalfMid_eq`. -/
noncomputable def NrectMid (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u

/-- **`ζ` is analytic on the middle strip of a window at positive height.**

### Dependencies
**Depends on:** `Definitions.analyticOnNhd_riemannZeta_of_im_pos`.
**Used by:** `Nrect_one_eq_add`. -/
theorem analyticOnNhd_riemannZeta_rectMid {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
  analyticOnNhd_riemannZeta_of_im_pos (fun _ hs => hT₁.trans hs.1)

/-- **A window splits into its two edge strips and its middle:**
`Nrect T₁ T₂ 1 = NrectLeft T₁ T₂ α + NrectMid T₁ T₂ α + Nrect T₁ T₂ α`.

### Summary of Proof
Pointwise through `divisor_riemannZeta_eq_ite`, with `finsum_add_distrib` twice (supports are
finite by `divisor_support_finite_of_subset_strip`).  For `u` in the window exactly one of
`Re u < α`, `α ≤ Re u ≤ 1-α`, `1-α < Re u` holds, and `Nrect _ _ 1`'s region is `0 < Re u`; the
two readings differ only where `Re u ≤ 0`, and there `zetaOrd u = 0` because a zero with
non-positive real part is a trivial zero and hence real.

### Lean Notes
`α ≤ 1/2` is what makes the three cases exclusive and exhaustive (`α ≤ 1 - α`); `0 < α` is what
puts the middle strip inside `0 < Re`.

### References
tex: the implicit decomposition behind "the proportion of zeros with `Re ρ ∈ [α,1-α]`".

### Dependencies
**Depends on:** `NrectLeft`, `NrectMid`, `Definitions.Nrect`,
`divisor_support_finite_of_subset_strip`, `Definitions.divisor_riemannZeta_eq_ite`,
`Background.LogDerivZetaLaurent.riemannZeta_eq_zero_of_re_nonpos`.
**Used by:** `NrectMid_eq`. -/
theorem Nrect_one_eq_add {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    Nrect T₁ T₂ 1 = NrectLeft T₁ T₂ α + NrectMid T₁ T₂ α + Nrect T₁ T₂ α := by
  have hAll := analyticOnNhd_riemannZeta_rect (T1 := T₁) (T2 := T₂) (γ := 1 - 1) hT₁
  have hLeft := analyticOnNhd_riemannZeta_rectLeft (T₂ := T₂) (α := α) hT₁
  have hMid := analyticOnNhd_riemannZeta_rectMid (T₂ := T₂) (α := α) hT₁
  have hRight := analyticOnNhd_riemannZeta_rect (T1 := T₁) (T2 := T₂) (γ := 1 - α) hT₁
  have hfL := divisor_support_finite_of_subset_strip (T₂ := T₂) hT₁
    (U := {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α}) (fun s hs => ⟨hs.1, hs.2.1⟩) hLeft
  have hfM := divisor_support_finite_of_subset_strip (T₂ := T₂) hT₁
    (U := {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α})
    (fun s hs => ⟨hs.1, hs.2.1⟩) hMid
  have hfR := divisor_support_finite_of_subset_strip (T₂ := T₂) hT₁
    (U := {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re}) (fun s hs => ⟨hs.1, hs.2.1⟩) hRight
  have hfLM : (Function.support (fun u => MeromorphicOn.divisor riemannZeta
      {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} u + MeromorphicOn.divisor riemannZeta
      {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u)).Finite :=
    (hfL.union hfM).subset (Function.support_add _ _)
  unfold Nrect NrectLeft NrectMid
  rw [← finsum_add_distrib hfL hfM, ← finsum_add_distrib hfLM hfR]
  refine finsum_congr fun u => ?_
  rw [divisor_riemannZeta_eq_ite hAll u, divisor_riemannZeta_eq_ite hLeft u,
    divisor_riemannZeta_eq_ite hMid u, divisor_riemannZeta_eq_ite hRight u]
  by_cases hw1 : T₁ < u.im
  · by_cases hw2 : u.im ≤ T₂
    · have hzneg : u.re ≤ 0 → zetaOrd u = 0 := by
        intro hre
        apply zetaOrd_eq_zero_of_ne_zero
        intro hz
        obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos hre hz
        have him : u.im = 0 := by rw [hn]; simp
        linarith
      rcases lt_or_ge u.re α with hlt | hge
      · have hL : u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} := ⟨hw1, hw2, hlt⟩
        have hM : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
          fun h => absurd h.2.2.1 (not_le.mpr hlt)
        have hR : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} :=
          fun h => absurd h.2.2 (not_lt.mpr (by linarith))
        rw [ite_eq_left hL, ite_eq_right hM, ite_eq_right hR]
        rcases lt_or_ge 0 u.re with h0 | h0
        · rw [ite_eq_left (show u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - 1 < s.re} from
            ⟨hw1, hw2, by linarith⟩)]
          ring
        · rw [ite_eq_right (show u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - 1 < s.re} from
            fun h => absurd h.2.2 (not_lt.mpr (by linarith))), hzneg h0]
          ring
      · rcases le_or_gt u.re (1 - α) with hle | hgt
        · have hL : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} :=
            fun h => absurd h.2.2 (not_lt.mpr hge)
          have hM : u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
            ⟨hw1, hw2, hge, hle⟩
          have hR : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} :=
            fun h => absurd h.2.2 (not_lt.mpr hle)
          rw [ite_eq_right hL, ite_eq_left hM, ite_eq_right hR,
            ite_eq_left (show u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - 1 < s.re} from
              ⟨hw1, hw2, by linarith⟩)]
          ring
        · have hL : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ s.re < α} :=
            fun h => absurd h.2.2 (not_lt.mpr hge)
          have hM : u ∉ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
            fun h => absurd h.2.2.2 (not_le.mpr hgt)
          have hR : u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} := ⟨hw1, hw2, hgt⟩
          rw [ite_eq_right hL, ite_eq_right hM, ite_eq_left hR,
            ite_eq_left (show u ∈ {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - 1 < s.re} from
              ⟨hw1, hw2, by linarith⟩)]
          ring
    · rw [ite_eq_right (fun h => hw2 h.2.1), ite_eq_right (fun h => hw2 h.2.1),
        ite_eq_right (fun h => hw2 h.2.1), ite_eq_right (fun h => hw2 h.2.1)]
      ring
  · rw [ite_eq_right (fun h => hw1 h.1), ite_eq_right (fun h => hw1 h.1),
      ite_eq_right (fun h => hw1 h.1), ite_eq_right (fun h => hw1 h.1)]
    ring

/-- **The middle count of a window is the total minus twice the edge count:**
`NrectMid T₁ T₂ α = Nrect T₁ T₂ 1 - 2 · Nrect T₁ T₂ α`.

### Summary of Proof
`Nrect_one_eq_add` and `NrectLeft_eq_Nrect`.

### Lean Notes
**This is the factor of two of the paper's proportion statements, proved.**  Everything the tex
writes as `1 - 2N(t-h,t+h,α)/(N(t+h)-N(t-h))` is now literally the proportion of the window's
zeros whose real part lies in `[α, 1-α]`.

### References
tex: `\ref{cor:simpmain}` (Corollary 1).

### Dependencies
**Depends on:** `Nrect_one_eq_add`, `NrectLeft_eq_Nrect`.
**Used by:** `HalvingConvention.NhalfMid_eq`. -/
theorem NrectMid_eq {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    NrectMid T₁ T₂ α = Nrect T₁ T₂ 1 - 2 * Nrect T₁ T₂ α := by
  have h := Nrect_one_eq_add (T₂ := T₂) hT₁ hα hα2
  rw [NrectLeft_eq_Nrect hT₁] at h
  omega

/-- **`NlineReMid T α` counts the zeros ON the line `Im ρ = T` with `α ≤ Re ρ ≤ 1-α`.**

### Summary of Proof
A definition, the middle-strip analogue of `Definitions.NlineRe`.

### References
tex: page 1, the half-multiplicity convention, on the middle strip.

### Dependencies
**Depends on:** none.
**Used by:** `NlineReMid_eq`, `NlineRe_one_eq_add`, `HalvingConvention.NhalfMid`,
`HalvingConvention.NhalfMid_eq`. -/
noncomputable def NlineReMid (T α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u

/-- **`ζ` is analytic on the middle strip of a horizontal line at positive height.**

### Dependencies
**Depends on:** `Definitions.analyticOnNhd_riemannZeta_of_im_pos`.
**Used by:** `NlineRe_one_eq_add`. -/
theorem analyticOnNhd_riemannZeta_lineMid {T α : ℝ} (hT : 0 < T) :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
  analyticOnNhd_riemannZeta_of_im_pos (fun _ hs => by rw [hs.1]; exact hT)

/-- **A horizontal line splits into its two edge strips and its middle:**
`NlineRe T 1 = NlineReLeft T α + NlineReMid T α + NlineRe T α`.

### Summary of Proof
`Nrect_one_eq_add`'s argument verbatim, with the strip `T/2 < Im ≤ T` supplying the finiteness
hypothesis of `divisor_support_finite_of_subset_strip`.

### Dependencies
**Depends on:** `NlineReLeft`, `NlineReMid`, `Definitions.NlineRe`,
`divisor_support_finite_of_subset_strip`, `Definitions.divisor_riemannZeta_eq_ite`,
`Background.LogDerivZetaLaurent.riemannZeta_eq_zero_of_re_nonpos`.
**Used by:** `NlineReMid_eq`. -/
theorem NlineRe_one_eq_add {T α : ℝ} (hT : 0 < T) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    NlineRe T 1 = NlineReLeft T α + NlineReMid T α + NlineRe T α := by
  have hAll := analyticOnNhd_riemannZeta_line (T := T) (γ := 1 - 1) hT
  have hLeft := analyticOnNhd_riemannZeta_lineLeft (α := α) hT
  have hMid := analyticOnNhd_riemannZeta_lineMid (α := α) hT
  have hRight := analyticOnNhd_riemannZeta_line (T := T) (γ := 1 - α) hT
  have hT2 : T / 2 < T := by linarith
  have hfL := divisor_support_finite_of_subset_strip (T₁ := T / 2) (T₂ := T) (by linarith)
    (U := {s : ℂ | s.im = T ∧ s.re < α}) (fun s hs => ⟨by rw [hs.1]; exact hT2, hs.1.le⟩) hLeft
  have hfM := divisor_support_finite_of_subset_strip (T₁ := T / 2) (T₂ := T) (by linarith)
    (U := {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α})
    (fun s hs => ⟨by rw [hs.1]; exact hT2, hs.1.le⟩) hMid
  have hfR := divisor_support_finite_of_subset_strip (T₁ := T / 2) (T₂ := T) (by linarith)
    (U := {s : ℂ | s.im = T ∧ 1 - α < s.re}) (fun s hs => ⟨by rw [hs.1]; exact hT2, hs.1.le⟩)
    hRight
  have hfLM : (Function.support (fun u => MeromorphicOn.divisor riemannZeta
      {s : ℂ | s.im = T ∧ s.re < α} u + MeromorphicOn.divisor riemannZeta
      {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u)).Finite :=
    (hfL.union hfM).subset (Function.support_add _ _)
  unfold NlineRe NlineReLeft NlineReMid
  rw [← finsum_add_distrib hfL hfM, ← finsum_add_distrib hfLM hfR]
  refine finsum_congr fun u => ?_
  rw [divisor_riemannZeta_eq_ite hAll u, divisor_riemannZeta_eq_ite hLeft u,
    divisor_riemannZeta_eq_ite hMid u, divisor_riemannZeta_eq_ite hRight u]
  by_cases hw : u.im = T
  · have hzneg : u.re ≤ 0 → zetaOrd u = 0 := by
      intro hre
      apply zetaOrd_eq_zero_of_ne_zero
      intro hz
      obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos hre hz
      have him : u.im = 0 := by rw [hn]; simp
      rw [hw] at him
      linarith
    rcases lt_or_ge u.re α with hlt | hge
    · have hL : u ∈ {s : ℂ | s.im = T ∧ s.re < α} := ⟨hw, hlt⟩
      have hM : u ∉ {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
        fun h => absurd h.2.1 (not_le.mpr hlt)
      have hR : u ∉ {s : ℂ | s.im = T ∧ 1 - α < s.re} :=
        fun h => absurd h.2 (not_lt.mpr (by linarith))
      rw [ite_eq_left hL, ite_eq_right hM, ite_eq_right hR]
      rcases lt_or_ge 0 u.re with h0 | h0
      · rw [ite_eq_left (show u ∈ {s : ℂ | s.im = T ∧ 1 - 1 < s.re} from ⟨hw, by linarith⟩)]
        ring
      · rw [ite_eq_right (show u ∉ {s : ℂ | s.im = T ∧ 1 - 1 < s.re} from
          fun h => absurd h.2 (not_lt.mpr (by linarith))), hzneg h0]
        ring
    · rcases le_or_gt u.re (1 - α) with hle | hgt
      · have hL : u ∉ {s : ℂ | s.im = T ∧ s.re < α} := fun h => absurd h.2 (not_lt.mpr hge)
        have hM : u ∈ {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} := ⟨hw, hge, hle⟩
        have hR : u ∉ {s : ℂ | s.im = T ∧ 1 - α < s.re} := fun h => absurd h.2 (not_lt.mpr hle)
        rw [ite_eq_right hL, ite_eq_left hM, ite_eq_right hR,
          ite_eq_left (show u ∈ {s : ℂ | s.im = T ∧ 1 - 1 < s.re} from ⟨hw, by linarith⟩)]
        ring
      · have hL : u ∉ {s : ℂ | s.im = T ∧ s.re < α} := fun h => absurd h.2 (not_lt.mpr hge)
        have hM : u ∉ {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} :=
          fun h => absurd h.2.2 (not_le.mpr hgt)
        have hR : u ∈ {s : ℂ | s.im = T ∧ 1 - α < s.re} := ⟨hw, hgt⟩
        rw [ite_eq_right hL, ite_eq_right hM, ite_eq_left hR,
          ite_eq_left (show u ∈ {s : ℂ | s.im = T ∧ 1 - 1 < s.re} from ⟨hw, by linarith⟩)]
        ring
  · rw [ite_eq_right (fun h => hw h.1), ite_eq_right (fun h => hw h.1),
      ite_eq_right (fun h => hw h.1), ite_eq_right (fun h => hw h.1)]
    ring

/-- **The middle count of a horizontal line is the total minus twice the edge count:**
`NlineReMid T α = NlineRe T 1 - 2 · NlineRe T α`.

### Summary of Proof
`NlineRe_one_eq_add` and `NlineReLeft_eq_NlineRe`.

### References
tex: page 1, the half-multiplicity convention.

### Dependencies
**Depends on:** `NlineRe_one_eq_add`, `NlineReLeft_eq_NlineRe`.
**Used by:** `HalvingConvention.NhalfMid_eq`. -/
theorem NlineReMid_eq {T α : ℝ} (hT : 0 < T) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    NlineReMid T α = NlineRe T 1 - 2 * NlineRe T α := by
  have h := NlineRe_one_eq_add hT hα hα2
  rw [NlineReLeft_eq_NlineRe hT] at h
  omega
