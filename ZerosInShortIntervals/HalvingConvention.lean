/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.MainTheorem
import ZerosInShortIntervals.MainCorollary
import ZerosInShortIntervals.Reflection

/-! # The halving convention: Theorems 2, 3, 32 and Corollaries 1, 4, 5 for the tex's `N(T₁,T₂,α)`

The tex counts zeros on the horizontal edges of the window `[t-h, t+h]` with **half** their
multiplicity (page 1), and after Equation 13 defines `arg ζ` on a line through a zero as the
average of its two one-sided limits, so that Equation 13 still holds.  The Lean statements count
`T₁ < Im ρ ≤ T₂` (`Nrect`) and, on the Littlewood side, assume the two edges zero-free
(`hzf_p`/`hzf_m`); the two conventions agree exactly in that case
(`Definitions.Nhalf_eq_Nrect_of_forall_ne_zero`).

This file gives every headline statement its half-counted form, with **no** edge hypothesis, by a
single mechanism: for `ε > 0` below the gap to the nearest other zero ordinate,

  `2 · Nhalf (t-h) (t+h) α = Nrect (t-h-ε) (t+h+ε) α + Nrect (t-h+ε) (t+h-ε) α`

(`Definitions.two_mul_Nhalf_eq`).  Both shifted windows have zero-free edges, so the existing
theorem applies to each with half-widths `h ± ε`, and because the main terms `U_J`, `U_L` are
**affine in `h`** the two right-hand sides average back to the value at `h` exactly:
`Nhalf < U(h) + E` with the tex's strict inequality and no limit argument
(`mainJensenHalf`, `mainLittlewoodHalf`, `mainPositiveProportionCorollary_*_half`).  Theorem 32's
right-hand side is not affine in `h` (its error term has `h/(T-h)`), so its half-counted form
`littlewoodshortHalf` is obtained with `≤` by letting `ε → 0⁺`.

The corollaries are half-counted in numerator **and** denominator: the denominator is
`Nhalf (t-h) (t+h) 1`, the tex's `N(t+h) - N(t-h)` for all nontrivial zeros (`Re ρ > 0`) with the
edge convention.  The Bellotti–Wong lower bound `Lbound h t` still applies to it: the *inner*
window `N(t+h-ε) - N(t-h+ε)` is at most the half count and is bounded below by `Lbound (h-ε) t`
for every small `ε`, so `ε → 0⁺` gives
`Lbound h t ≤ Nhalf (t-h) (t+h) 1` (`Lbound_le_Nhalf_one`); no change to `Lbound` or to the `C₂`
tables is needed.  (`N_sub_N_eq_Nrect_one` identifies Lean's `N(T₂) - N(T₁)` with
`Nrect T₁ T₂ 1`, using that a zero with positive imaginary part has `0 < Re ρ < 1`.)

One deliberate limitation, recorded in the docstrings: the half-counted Theorems 2 and 3 need
`h < t^{2/3}` (strict) rather than the tex's `h ≤ t^{2/3}`, since the outer window has half-width
`h + ε`.  Equation 13 itself in half-counted form (with the averaged `arg`) is not attempted; it
is not needed for any of the results above.

The file also carries the introduction's headline Corollary `\ref{cor:simpmain}` (Corollary 1),
`simpleProportionCorollary_jensen`/`_littlewood`: dividing `\ref{cor:main-jensen}` and
`\ref{cor:main-littlewood}` through gives
`1 - 2·Nhalf(t-h,t+h,α)/Nhalf(t-h,t+h,1) > 1 - 2C₂`, which is the corollary's displayed
inequality.  Reading the left-hand side as "the proportion of zeros with `Re ρ ∈ [α,1-α]`" needs
the reflection `ρ ↦ 1 - conj ρ` to be a multiplicity-preserving involution of the zero set; that
is proved in `Reflection.lean`, so the `_prose` forms below state the corollary in the tex's own
words rather than only in its displayed one.

What this file does **not** settle is the sign of the constant.  Everything here proves
`proportion > C` for an `h₀` and a `t₀` the caller supplies, whatever the sign of `C`.  That the
constant is positive, and that admissible `h₀`, `t₀` exist at all, is `PositiveProportion.lean`. -/

open Filter Topology

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced.  The headline results are
restated with the single bundled class in `ZerosInShortIntervals/AllHypotheses.lean`. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **`Nhalf T T α = 0`.**

### Summary of Proof
`Nrect_self` and the two equal `NlineRe` halves cancel.

### Dependencies
**Depends on:** `Definitions.Nhalf`, `MainTheorem.Nrect_self`.
**Used by:** `Nhalf_nonneg`, `mainJensenHalf`, `mainLittlewoodHalf`. -/
theorem Nhalf_self (T α : ℝ) : Nhalf T T α = 0 := by
  unfold Nhalf; rw [Nrect_self]; ring

/-- **A common `ε` for both edges of the window `[t-h, t+h]`**, below half the gap radius of
`Definitions.exists_gap_ordinates` at each edge and below the caps `h/2`, `b`, `(t-h)/2`.

### Summary of Proof
Two applications of `exists_gap_ordinates` and a `min`.

### Lean Notes
The gap conclusion is stated with `≤ ε` (non-strict), which is what `two_mul_Nhalf_eq` and the
edge lemma `edge_zero_free_of_gap` consume; it holds because `ε` is at most half the radius.
The cap `b` is the room left for the outer window (`t^{2/3} - h` in Theorems 2–3,
`(T - h - 10^{12})/2` in Theorem 32).

### Dependencies
**Depends on:** `Definitions.exists_gap_ordinates`.
**Used by:** `Lbound_le_Nhalf_one`, `Nhalf_nonneg`, `littlewoodshortHalf`, `mainJensenHalf`,
`mainLittlewoodHalf`. -/
theorem exists_window_eps (t h γ b : ℝ) (hth : 0 < t - h) (hh : 0 < h) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ h / 2 ∧ ε ≤ b ∧ ε ≤ (t - h) / 2 ∧
      (∀ s : ℂ, riemannZeta s = 0 → γ ≤ s.re → |s.im - (t - h)| ≤ ε → s.im = t - h) ∧
      (∀ s : ℂ, riemannZeta s = 0 → γ ≤ s.re → |s.im - (t + h)| ≤ ε → s.im = t + h) := by
  obtain ⟨ε1, hε1, hg1⟩ := exists_gap_ordinates (t - h) γ
  obtain ⟨ε2, hε2, hg2⟩ := exists_gap_ordinates (t + h) γ
  refine ⟨min (ε1 / 2) (min (ε2 / 2) (min (h / 2) (min b ((t - h) / 2)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  · intro s hs hre him
    exact hg1 s hs hre (lt_of_le_of_lt him (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  · intro s hs hre him
    exact hg2 s hs hre (lt_of_le_of_lt him
      (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)))

/-- **`0 ≤ Nhalf T₁ T₂ α` for `0 < T₁ ≤ T₂`.**

### Summary of Proof
`T₁ = T₂` is `Nhalf_self`; otherwise `two_mul_Nhalf_eq` writes `2 · Nhalf` as a sum of two
`Nrect`s, each nonnegative (`Nrect_nonneg`).

### Dependencies
**Depends on:** `Nhalf_self`, `exists_window_eps`, `Definitions.two_mul_Nhalf_eq`,
`Definitions.Nrect_nonneg`.
**Used by:** `mainPositiveProportionCorollary_jensen_half`,
`mainPositiveProportionCorollary_littlewood_half`. -/
theorem Nhalf_nonneg {T1 T2 α : ℝ} (hT1 : 0 < T1) (h12 : T1 ≤ T2) : 0 ≤ Nhalf T1 T2 α := by
  rcases h12.eq_or_lt with heq | hlt
  · subst heq; rw [Nhalf_self]
  · set t := (T1 + T2) / 2 with ht
    set h := (T2 - T1) / 2 with hh
    have hT1' : T1 = t - h := by rw [ht, hh]; ring
    have hT2' : T2 = t + h := by rw [ht, hh]; ring
    have hh0 : 0 < h := by rw [hh]; linarith
    obtain ⟨ε, hε, hεh, -, hεt, hg1, hg2⟩ :=
      exists_window_eps t h (1 - α) 1 (by rw [← hT1']; exact hT1) hh0 one_pos
    rw [hT1', hT2']
    have h2 := two_mul_Nhalf_eq (T1 := t - h) (T2 := t + h) (α := α) hε (by linarith) (by linarith)
      (fun s hs hre him => hg1 s hs hre.le him) (fun s hs hre him => hg2 s hs hre.le him)
    have hA : (0 : ℝ) ≤ Nrect (t - h - ε) (t + h + ε) α := by
      exact_mod_cast Nrect_nonneg (by linarith : (0 : ℝ) < t - h - ε)
    have hB : (0 : ℝ) ≤ Nrect (t - h + ε) (t + h - ε) α := by
      exact_mod_cast Nrect_nonneg (by linarith : (0 : ℝ) < t - h + ε)
    linarith

/-- **`U_J` is affine in `h`:** `U_J(h+ε) + U_J(h-ε) = 2 U_J(h)`.

### Summary of Proof
`ring` on the definition `(2h + 2α̂)(⋯) + B₄`.

### Dependencies
**Depends on:** `MainTerms.UJensen`.
**Used by:** `mainJensenHalf`. -/
theorem UJensen_avg (α r h ε t : ℝ) :
    UJensen α r (h + ε) t + UJensen α r (h - ε) t = 2 * UJensen α r h t := by
  unfold UJensen; ring

/-- **`U_L` is affine in `h`:** `U_L(h+ε) + U_L(h-ε) = 2 U_L(h)`.

### Summary of Proof
`ring` on the definition.

### Dependencies
**Depends on:** `MainTerms.ULittlewood`.
**Used by:** `mainLittlewoodHalf`. -/
theorem ULittlewood_avg (α r h ε t : ℝ) (k : ℤ) :
    ULittlewood α r (h + ε) t k + ULittlewood α r (h - ε) t k = 2 * ULittlewood α r h t k := by
  unfold ULittlewood; ring

/-- **Theorem `\ref{thm:main-jensen}` (Theorem 2) in the tex's half-counting convention:**
`Nhalf (t-h) (t+h) α < U_J(α,r,h,t) + E_J`, for `0 < α < r < 1`, `α < 1/6`, `t ≥ e`,
`0 ≤ h < t^{2/3}`.

### Summary of Proof
`h = 0` is `Nhalf_self` and the positivity of the right-hand side.  For `h > 0` pick `ε` by
`exists_window_eps` (with room `t^{2/3} - h`), write `2 · Nhalf` as the outer plus inner window
count (`two_mul_Nhalf_eq`), apply `mainJensen` to both windows (half-widths `h ± ε`, both in
`[0, t^{2/3}]`) and average: `U_J(h+ε) + U_J(h-ε) = 2 U_J(h)` (`UJensen_avg`), so the strict
inequality survives without any limit.

### Lean Notes
The one loss against the tex is the endpoint `h = t^{2/3}`: the outer window has half-width
`h + ε > t^{2/3}`, outside `mainJensen`'s range.  Theorem 2 as stated needs no edge hypothesis to
begin with; this version only changes the count.  Inherits exactly the `sorry`s and axioms of
`mainJensen` (`#print axioms`, 2026-09-08).

### References
tex: `\ref{thm:main-jensen}` (Theorem 2) with the page-1 counting convention.

### Dependencies
**Depends on:** `MainTheorem.mainJensen`, `MainTheorem.UJensen_add_EJensen_pos`,
`MainTheorem.rpow_two_thirds_lt_self`, `exists_window_eps`, `Definitions.two_mul_Nhalf_eq`,
`UJensen_avg`, `Nhalf_self`.
**Used by:** `mainPositiveProportionCorollary_jensen_half`. -/
theorem mainJensenHalf {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (hα : α < alphaBoundTodo) (ht : Real.exp 1 ≤ t) (hh0 : 0 ≤ h)
    (hh : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α < UJensen α r h t + EJensen α r t := by
  have hpos := UJensen_add_EJensen_pos hα0 hαr hr1 ht hh0
  rcases hh0.eq_or_lt with h0 | hhpos
  · subst h0
    rw [sub_zero, add_zero, Nhalf_self]
    exact hpos
  · have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have ht1 : (1 : ℝ) < t := by linarith
    have hth : 0 < t - h := by linarith [rpow_two_thirds_lt_self ht1]
    obtain ⟨ε, hε, hεh, hεb, hεt, hg1, hg2⟩ :=
      exists_window_eps t h (1 - α) (t ^ ((2 : ℝ) / 3) - h) hth hhpos (by linarith)
    have h2 := two_mul_Nhalf_eq (T1 := t - h) (T2 := t + h) (α := α) hε (by linarith) (by linarith)
      (fun s hs hre him => hg1 s hs hre.le him) (fun s hs hre him => hg2 s hs hre.le him)
    have hout := mainJensen hα0 hαr hr1 hα ht (by linarith : 0 ≤ h + ε)
      (by linarith : h + ε ≤ t ^ ((2 : ℝ) / 3))
    have hin := mainJensen hα0 hαr hr1 hα ht (by linarith : 0 ≤ h - ε)
      (by linarith : h - ε ≤ t ^ ((2 : ℝ) / 3))
    rw [show t - (h + ε) = t - h - ε by ring, show t + (h + ε) = t + h + ε by ring] at hout
    rw [show t - (h - ε) = t - h + ε by ring, show t + (h - ε) = t + h - ε by ring] at hin
    have havg := UJensen_avg α r h ε t
    linarith

/-- **The shifted edges are zero-free:** if no zero with `Re ≥ γ` has ordinate within `ε` of `T`
other than `T` itself, then the lines `Im = T ± ε` carry no zero with `Re ≥ γ`.

### Summary of Proof
A zero on `Im = T + δ` (`δ = ±ε`) has `|Im - T| = ε ≤ ε`, so by the gap hypothesis its ordinate
is `T`, i.e. `δ = 0`, contradicting `ε > 0`.

### Lean Notes
Stated with the height as a single real cast `((T + δ : ℝ) : ℂ)`, so that after substituting
`T = t ± h` the hypothesis shapes `x + (t + (h ± ε)) * I` of `mainLittlewood`/`littlewoodshort`
are reached by one `ring` rewrite inside the cast and `push_cast`.

### Dependencies
**Depends on:** none.
**Used by:** `mainLittlewoodHalf`, `littlewoodshortHalf`. -/
theorem edge_zero_free_of_gap {ε γ : ℝ} (hε : 0 < ε) (T : ℝ)
    (hg : ∀ s : ℂ, riemannZeta s = 0 → γ ≤ s.re → |s.im - T| ≤ ε → s.im = T) (δ : ℝ)
    (hδ : δ = ε ∨ δ = -ε) :
    ∀ x ∈ Set.Ici γ, riemannZeta (x + ((T + δ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  intro x hx hz
  have hre' : ((x : ℂ) + ((T + δ : ℝ) : ℂ) * Complex.I).re = x := by simp
  have him' : ((x : ℂ) + ((T + δ : ℝ) : ℂ) * Complex.I).im = T + δ := by simp
  have h := hg _ hz (by rw [hre']; exact hx) (by
    rw [him']
    rcases hδ with h | h <;> rw [h] <;> simp [abs_of_pos hε])
  rw [him'] at h
  rcases hδ with h' | h' <;> rw [h'] at h <;> linarith

/-- **Theorem `\ref{thm:main-littlewood}` (Theorem 3) in the tex's half-counting convention, with
NO zero-free-edge hypothesis:** `Nhalf (t-h) (t+h) α < U_L(α,r,h,t,k) + E_L`, for `r > α > 0`,
`α < 1/6`, `σ_k ≤ 1-r < σ_{k+1}`, `t ≥ e^e`, `0 ≤ h < t^{2/3}`.

### Summary of Proof
As `mainJensenHalf`, with the gap taken at abscissa `γ = 1 - r` so that it also covers the closed
edge segments `[1-r, 1+ηr]`: `edge_zero_free_of_gap` turns it into the `hzf_p`/`hzf_m`
hypotheses of `mainLittlewood` for both shifted windows, whose bounds average by
`ULittlewood_avg`.

### Lean Notes
This removes `hzf_p`/`hzf_m` entirely: whether or not a zero sits on an edge, the half-counted
statement holds (with an edge zero, `Nhalf` is smaller than `Nrect` by half the top-edge
multiplicity and larger by half the bottom-edge one — the tex's convention exactly).  Same
endpoint loss `h < t^{2/3}` as `mainJensenHalf`.  Inherits the `sorry`s and axioms of
`mainLittlewood` and nothing else (`#print axioms`, 2026-09-08).

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3) with the page-1 counting convention.

### Dependencies
**Depends on:** `MainTheorem.mainLittlewood`, `MainTheorem.ULittlewood_add_ELittlewood_pos`,
`MainTheorem.rpow_two_thirds_lt_self`, `exists_window_eps`, `Definitions.two_mul_Nhalf_eq`,
`edge_zero_free_of_gap`, `ULittlewood_avg`, `Nhalf_self`.
**Used by:** `mainPositiveProportionCorollary_littlewood_half`. -/
theorem mainLittlewoodHalf {α r h t : ℝ} {k : ℤ} (hα0 : 0 < α) (hrα : α < r) (hα16 : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : Real.exp (Real.exp 1) ≤ t) (hh0 : 0 ≤ h) (hh : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α < ULittlewood α r h t k + ELittlewood α r t := by
  have hpos := ULittlewood_add_ELittlewood_pos (k := k) hα0 hrα hk hk' ht hh0
  rcases hh0.eq_or_lt with h0 | hhpos
  · subst h0
    rw [sub_zero, add_zero, Nhalf_self]
    exact hpos
  · have hee : (1 : ℝ) < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hee ht
    have hth : 0 < t - h := by linarith [rpow_two_thirds_lt_self ht1]
    obtain ⟨ε, hε, hεh, hεb, hεt, hg1, hg2⟩ :=
      exists_window_eps t h (1 - r) (t ^ ((2 : ℝ) / 3) - h) hth hhpos (by linarith)
    have h2 := two_mul_Nhalf_eq (T1 := t - h) (T2 := t + h) (α := α) hε (by linarith) (by linarith)
      (fun s hs hre him => hg1 s hs (by linarith) him)
      (fun s hs hre him => hg2 s hs (by linarith) him)
    have hzf_pp := edge_zero_free_of_gap hε (t + h) hg2 ε (Or.inl rfl)
    have hzf_pm := edge_zero_free_of_gap hε (t + h) hg2 (-ε) (Or.inr rfl)
    have hzf_mp := edge_zero_free_of_gap hε (t - h) hg1 ε (Or.inl rfl)
    have hzf_mm := edge_zero_free_of_gap hε (t - h) hg1 (-ε) (Or.inr rfl)
    have hout := mainLittlewood hα0 hrα hα16 hk hk' ht (by linarith : 0 ≤ h + ε)
      (by linarith : h + ε ≤ t ^ ((2 : ℝ) / 3))
      (fun x hx => by
        have := hzf_pp x (Set.mem_Ici.mpr hx.1)
        rw [show (t + h + ε : ℝ) = t + (h + ε) by ring] at this; push_cast at this ⊢; exact this)
      (fun x hx => by
        have := hzf_mm x (Set.mem_Ici.mpr hx.1)
        rw [show (t - h + -ε : ℝ) = t - (h + ε) by ring] at this; push_cast at this ⊢; exact this)
    have hin := mainLittlewood hα0 hrα hα16 hk hk' ht (by linarith : 0 ≤ h - ε)
      (by linarith : h - ε ≤ t ^ ((2 : ℝ) / 3))
      (fun x hx => by
        have := hzf_pm x (Set.mem_Ici.mpr hx.1)
        rw [show (t + h + -ε : ℝ) = t + (h - ε) by ring] at this; push_cast at this ⊢; exact this)
      (fun x hx => by
        have := hzf_mp x (Set.mem_Ici.mpr hx.1)
        rw [show (t - h + ε : ℝ) = t - (h - ε) by ring] at this; push_cast at this ⊢; exact this)
    rw [show t - (h + ε) = t - h - ε by ring, show t + (h + ε) = t + h + ε by ring] at hout
    rw [show t - (h - ε) = t - h + ε by ring, show t + (h - ε) = t + h - ε by ring] at hin
    have havg := ULittlewood_avg α r h ε t k
    linarith

/-- **The right-hand side of `littlewoodshort` (Theorem 32) as a function of the half-width `h`.**

### Summary of Proof
Definition; it is affine in `h` except for the error term `4h/(π(T-h))`, which is why the
half-counted Theorem 32 needs a limit rather than the exact averaging of `UJensen_avg`.

### Dependencies
**Depends on:** `LittlewoodShort.A1`–`A6`.
**Used by:** `continuousAt_littlewoodshortRHS`, `littlewoodshortHalf`. -/
noncomputable def littlewoodshortRHS (T r α : ℝ) (k : ℤ) (h : ℝ) : ℝ :=
  (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
    + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
    + 2 * A3 α r k * h + A6 α r
    + (4 * h / (Real.pi * (T - h)) + 2) / (r - α)

/-- **`littlewoodshortRHS` is continuous in `h` for `h < T`.**

### Summary of Proof
`fun_prop`, the only side condition being `π(T-h) ≠ 0`.

### Dependencies
**Depends on:** `littlewoodshortRHS`.
**Used by:** `littlewoodshortHalf`. -/
theorem continuousAt_littlewoodshortRHS {T r α : ℝ} (k : ℤ) {h : ℝ} (hh : h < T) :
    ContinuousAt (littlewoodshortRHS T r α k) h := by
  have hne : Real.pi * (T - h) ≠ 0 := mul_ne_zero Real.pi_pos.ne' (sub_pos.mpr hh).ne'
  unfold littlewoodshortRHS
  fun_prop (disch := assumption)

/-- **Theorem `\ref{thm:littlewoodshort}` (Theorem 32) in the half-counting convention, with NO
zero-free-edge hypothesis and `≤` in place of `<`.**

### Summary of Proof
For every `0 < ε ≤ ε₀` (`exists_window_eps`, with room `(T - h - 10^{12})/2` so that the outer
window still has `T - h - ε > 10^{12}`) the two shifted windows satisfy `littlewoodshort`, whose
edge hypotheses come from `edge_zero_free_of_gap`; `two_mul_Nhalf_eq` gives
`2 · Nhalf < R(h+ε) + R(h-ε)` with `R = littlewoodshortRHS`.  `R` is continuous at `h`
(`continuousAt_littlewoodshortRHS`), so `R(h+ε) + R(h-ε) → 2R(h)` as `ε → 0⁺`
(`ge_of_tendsto` on `𝓝[>] 0`), whence `2 · Nhalf ≤ 2 R(h)`.

### Lean Notes
Strictness is lost only because of the non-affine error term `4h/(π(T-h))`; the two
`ULittlewood`-level statements keep `<`.  A strict version would follow from the (true) convexity
of `h ↦ 4h/(π(T-h))` only in the wrong direction, so `≤` is the honest statement here.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32) with the page-1 counting convention.

### Dependencies
**Depends on:** `LittlewoodShort.littlewoodshort`, `exists_window_eps`,
`Definitions.two_mul_Nhalf_eq`, `edge_zero_free_of_gap`, `littlewoodshortRHS`,
`continuousAt_littlewoodshortRHS`.
**Used by:** none (statement-level counterpart of Theorem 32). -/
theorem littlewoodshortHalf {T h r α : ℝ} {k : ℤ} (hT : (10 : ℝ) ^ (12 : ℕ) < T - h) (hh0 : 0 < h)
    (hh : h < T) (hα : 0 < α) (hrα : α < r) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r < sigma (k + 1)) :
    Nhalf (T - h) (T + h) α
      ≤ (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
        + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
        + 2 * A3 α r k * h + A6 α r
        + (4 * h / (Real.pi * (T - h)) + 2) / (r - α) := by
  have h1e12 : (0 : ℝ) < (10 : ℝ) ^ (12 : ℕ) := by norm_num
  have hth : 0 < T - h := by linarith
  obtain ⟨ε0, hε0, hε0h, hε0b, hε0t, hg1, hg2⟩ :=
    exists_window_eps T h (1 - r) ((T - h - 10 ^ (12 : ℕ)) / 2) hth hh0 (by linarith)
  -- the two-window bound for every 0 < ε ≤ ε0
  have hbound : ∀ ε, 0 < ε → ε ≤ ε0 →
      2 * Nhalf (T - h) (T + h) α
        < littlewoodshortRHS T r α k (h + ε) + littlewoodshortRHS T r α k (h - ε) := by
    intro ε hε hεε0
    have hg1' : ∀ s : ℂ, riemannZeta s = 0 → 1 - r ≤ s.re → |s.im - (T - h)| ≤ ε →
        s.im = T - h :=
      fun s hs hre him => hg1 s hs hre (him.trans hεε0)
    have hg2' : ∀ s : ℂ, riemannZeta s = 0 → 1 - r ≤ s.re → |s.im - (T + h)| ≤ ε →
        s.im = T + h :=
      fun s hs hre him => hg2 s hs hre (him.trans hεε0)
    have h2 := two_mul_Nhalf_eq (T1 := T - h) (T2 := T + h) (α := α) hε (by linarith) (by linarith)
      (fun s hs hre him => hg1' s hs (by linarith) him)
      (fun s hs hre him => hg2' s hs (by linarith) him)
    have hzf_pp := edge_zero_free_of_gap hε (T + h) hg2' ε (Or.inl rfl)
    have hzf_pm := edge_zero_free_of_gap hε (T + h) hg2' (-ε) (Or.inr rfl)
    have hzf_mp := edge_zero_free_of_gap hε (T - h) hg1' ε (Or.inl rfl)
    have hzf_mm := edge_zero_free_of_gap hε (T - h) hg1' (-ε) (Or.inr rfl)
    have hout := littlewoodshort (T := T) (h := h + ε) (r := r) (α := α) (k := k)
      (by linarith) (by linarith) (by linarith) hα hrα hk hk'
      (fun x hx => by
        have := hzf_pp x (Set.mem_Ici.mpr hx.1)
        rw [show (T + h + ε : ℝ) = T + (h + ε) by ring] at this; push_cast at this ⊢; exact this)
      (fun x hx => by
        have := hzf_mm x (Set.mem_Ici.mpr hx.1)
        rw [show (T - h + -ε : ℝ) = T - (h + ε) by ring] at this; push_cast at this ⊢; exact this)
    have hin := littlewoodshort (T := T) (h := h - ε) (r := r) (α := α) (k := k)
      (by linarith) (by linarith) (by linarith) hα hrα hk hk'
      (fun x hx => by
        have := hzf_pm x (Set.mem_Ici.mpr hx.1)
        rw [show (T + h + -ε : ℝ) = T + (h - ε) by ring] at this; push_cast at this ⊢; exact this)
      (fun x hx => by
        have := hzf_mp x (Set.mem_Ici.mpr hx.1)
        rw [show (T - h + ε : ℝ) = T - (h - ε) by ring] at this; push_cast at this ⊢; exact this)
    rw [show T - (h + ε) = T - h - ε by ring, show T + (h + ε) = T + h + ε by ring] at hout
    rw [show T - (h - ε) = T - h + ε by ring, show T + (h - ε) = T + h - ε by ring] at hin
    unfold littlewoodshortRHS
    rw [show T - (h + ε) = T - h - ε by ring, show T - (h - ε) = T - h + ε by ring]
    linarith
  -- pass to the limit ε → 0⁺
  have hcont := continuousAt_littlewoodshortRHS (T := T) (r := r) (α := α) k hh
  have hlim : Tendsto (fun ε : ℝ => littlewoodshortRHS T r α k (h + ε)
      + littlewoodshortRHS T r α k (h - ε)) (𝓝[>] 0) (𝓝 (2 * littlewoodshortRHS T r α k h)) := by
    have hp : Tendsto (fun ε : ℝ => h + ε) (𝓝[>] 0) (𝓝 h) := by
      have : Tendsto (fun ε : ℝ => h + ε) (𝓝 0) (𝓝 (h + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hm : Tendsto (fun ε : ℝ => h - ε) (𝓝[>] 0) (𝓝 h) := by
      have : Tendsto (fun ε : ℝ => h - ε) (𝓝 0) (𝓝 (h - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := (hcont.tendsto.comp hp).add (hcont.tendsto.comp hm)
    rw [show littlewoodshortRHS T r α k h + littlewoodshortRHS T r α k h
        = 2 * littlewoodshortRHS T r α k h by ring] at this
    exact this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * Nhalf (T - h) (T + h) α
      ≤ littlewoodshortRHS T r α k (h + ε) + littlewoodshortRHS T r α k (h - ε) := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with ε hε
    exact (hbound ε hε.1 hε.2.le).le
  have := ge_of_tendsto hlim hev
  unfold littlewoodshortRHS at this
  linarith

/-- **A zero of `ζ` with positive imaginary part has positive real part** (in the form
`zetaOrd u = 0` when `Im u > 0`, `Re u ≤ 0`).

### Summary of Proof
`LogDerivZetaLaurent.riemannZeta_eq_zero_of_re_nonpos`: a zero with `Re ≤ 0` is a trivial zero
`-2(n+1)`, whose imaginary part is `0`.

### Dependencies
**Depends on:** `Definitions.zetaOrd_eq_zero_of_ne_zero`,
`LogDerivZetaLaurent.riemannZeta_eq_zero_of_re_nonpos`.
**Used by:** `N_divisor_support_finite`, `N_sub_N_eq_Nrect_one`. -/
theorem zetaOrd_eq_zero_of_im_pos_of_re_nonpos {u : ℂ} (hu : 0 < u.im) (hre : u.re ≤ 0) :
    zetaOrd u = 0 := by
  apply zetaOrd_eq_zero_of_ne_zero
  intro hz
  obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos hre hz
  have : u.im = 0 := by rw [hn]; simp
  linarith

/-- **The divisor defining `N T` has finite support.**

### Summary of Proof
A point of the support is a zero with `0 < Im ≤ T`, hence with `0 ≤ Re ≤ 1`
(`zetaOrd_eq_zero_of_im_pos_of_re_nonpos`, `riemannZeta_ne_zero_of_one_le_re`), i.e. in the
compact rectangle `[0,1] × [0,T]`, which holds finitely many zeros
(`IsCompact.inter_riemannZetaZeros_finite`).

### Dependencies
**Depends on:** `Definitions.N`, `Definitions.divisor_riemannZeta_eq_ite`,
`zetaOrd_eq_zero_of_im_pos_of_re_nonpos`.
**Used by:** `N_sub_N_eq_Nrect_one`. -/
theorem N_divisor_support_finite (T : ℝ) :
    (Function.support (fun u => MeromorphicOn.divisor riemannZeta
      {s : ℂ | 0 < s.im ∧ s.im ≤ T} u)).Finite := by
  set K : Set ℂ := Set.Icc 0 1 ×ℂ Set.Icc 0 T with hK
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  refine (hKc.inter_riemannZetaZeros_finite).subset ?_
  intro u hu
  rw [Function.mem_support,
    divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_of_im_pos fun s hs => hs.1)] at hu
  split_ifs at hu with hmem
  · have hz : riemannZeta u = 0 := by
      by_contra h; exact hu (zetaOrd_eq_zero_of_ne_zero h)
    have hre1 : u.re ≤ 1 := by
      by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_le.mp h).le hz
    have hre0 : 0 ≤ u.re := by
      by_contra h
      exact hu (zetaOrd_eq_zero_of_im_pos_of_re_nonpos hmem.1 (not_le.mp h).le)
    refine ⟨?_, mem_riemannZetaZeros.mpr hz⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨hre0, hre1⟩, ⟨hmem.1.le, hmem.2⟩⟩
  · exact absurd rfl hu

/-- **`N T₂ - N T₁ = Nrect T₁ T₂ 1` for `0 < T₁ ≤ T₂`:** Lean's `N` differences are the `α = 1`
rectangle counts, because every zero with positive imaginary part has `0 < Re ρ`.

### Summary of Proof
Pointwise through `divisor_riemannZeta_eq_ite` and `finsum_add_distrib`, as `Nrect_add_split`; the
only new case is a point of the strip with `Re ≤ 0`, where `zetaOrd` vanishes
(`zetaOrd_eq_zero_of_im_pos_of_re_nonpos`).

### Dependencies
**Depends on:** `Definitions.N`, `Definitions.Nrect`, `N_divisor_support_finite`,
`Definitions.Nrect_divisor_support_finite`, `Definitions.divisor_riemannZeta_eq_ite`,
`zetaOrd_eq_zero_of_im_pos_of_re_nonpos`.
**Used by:** `Lbound_le_Nhalf_one`. -/
theorem N_sub_N_eq_Nrect_one {T1 T2 : ℝ} (hT1 : 0 < T1) (h12 : T1 ≤ T2) :
    N T2 - N T1 = Nrect T1 T2 1 := by
  unfold N Nrect
  rw [sub_eq_iff_eq_add, ← finsum_add_distrib
    (Nrect_divisor_support_finite (T2 := T2) (γ := 1 - 1) hT1) (N_divisor_support_finite T1)]
  apply finsum_congr
  intro u
  rw [divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_of_im_pos fun s hs => hs.1),
    divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_rect (T2 := T2) (γ := 1 - 1) hT1),
    divisor_riemannZeta_eq_ite (analyticOnNhd_riemannZeta_of_im_pos fun s hs => hs.1)]
  simp only [Set.mem_ofPred_eq, sub_self]
  by_cases him : 0 < u.im
  · by_cases h1 : u.im ≤ T1
    · have h2 : u.im ≤ T2 := h1.trans h12
      have hn : ¬ T1 < u.im := not_lt.mpr h1
      simp [him, h1, h2, hn]
    · have hlt : T1 < u.im := not_le.mp h1
      by_cases h2 : u.im ≤ T2
      · by_cases hre : 0 < u.re
        · simp [him, h1, h2, hlt, hre]
        · have := zetaOrd_eq_zero_of_im_pos_of_re_nonpos him (not_lt.mp hre)
          simp [him, h1, h2, hlt, hre, this]
      · simp [him, h1, h2]
  · have : ¬ T1 < u.im := fun h => him (hT1.trans h)
    simp [him, this]

/-- **The inner window counts at most the half count:**
`Nrect (T₁+ε) (T₂-ε) α ≤ Nhalf T₁ T₂ α` under the gap hypotheses of `two_mul_Nhalf_eq`.

### Summary of Proof
`2·Nhalf = outer + inner` and `inner ≤ outer` (the outer window contains the inner one,
`Nrect_add_split` and `Nrect_nonneg`).

### Dependencies
**Depends on:** `Definitions.two_mul_Nhalf_eq`, `Definitions.Nrect_add_split`,
`Definitions.Nrect_nonneg`.
**Used by:** `Lbound_le_Nhalf_one`. -/
theorem Nrect_inner_le_Nhalf {T1 T2 α ε : ℝ} (hε : 0 < ε) (hT1 : 0 < T1 - ε)
    (h12 : T1 + ε ≤ T2 - ε)
    (hgap1 : ∀ s : ℂ, riemannZeta s = 0 → 1 - α < s.re → |s.im - T1| ≤ ε → s.im = T1)
    (hgap2 : ∀ s : ℂ, riemannZeta s = 0 → 1 - α < s.re → |s.im - T2| ≤ ε → s.im = T2) :
    (Nrect (T1 + ε) (T2 - ε) α : ℝ) ≤ Nhalf T1 T2 α := by
  have h2 := two_mul_Nhalf_eq hε hT1 h12 hgap1 hgap2
  have hout : (Nrect (T1 + ε) (T2 - ε) α : ℝ) ≤ Nrect (T1 - ε) (T2 + ε) α := by
    have e1 : Nrect (T1 - ε) (T2 + ε) α
        = Nrect (T1 - ε) (T1 + ε) α + Nrect (T1 + ε) (T2 + ε) α :=
      Nrect_add_split hT1 (by linarith) (by linarith)
    have e2 : Nrect (T1 + ε) (T2 + ε) α
        = Nrect (T1 + ε) (T2 - ε) α + Nrect (T2 - ε) (T2 + ε) α :=
      Nrect_add_split (by linarith) h12 (by linarith)
    have n1 := Nrect_nonneg (T2 := T1 + ε) (γ := α) hT1
    have n2 := Nrect_nonneg (T1 := T2 - ε) (T2 := T2 + ε) (γ := α) (by linarith)
    have : Nrect (T1 + ε) (T2 - ε) α ≤ Nrect (T1 - ε) (T2 + ε) α := by rw [e1, e2]; linarith
    exact_mod_cast this
  linarith

/-- **`Lbound h t` is continuous in `h`.**

### Summary of Proof
`fun_prop` (a polynomial in `h`).

### Dependencies
**Depends on:** `MainCorollary.Lbound`.
**Used by:** `Lbound_le_Nhalf_one`. -/
theorem continuous_Lbound_h (t : ℝ) : Continuous (fun h : ℝ => Lbound h t) := by
  unfold Lbound
  fun_prop

/-- **The Bellotti–Wong lower bound holds for the half-counted denominator:**
`Lbound h t ≤ Nhalf (t-h) (t+h) 1` for `0 < h`, `1 ≤ t - h`.

### Summary of Proof
The author's argument (2026-09-08): for every small `ε > 0` the inner window
`N(t+h-ε) - N(t-h+ε) = Nrect (t-h+ε) (t+h-ε) 1` (`N_sub_N_eq_Nrect_one`) is at most the half
count (`Nrect_inner_le_Nhalf`) and at least `Lbound (h-ε) t` (`Lbound_le_N_sub_N`); `Lbound` is
continuous in `h`, so `ε → 0⁺` (`le_of_tendsto`) gives the claim.

### Lean Notes
This is what makes the half-counted Corollaries 4–5 free: the denominator's lower bound needs no
new constant, contrary to the first version of this file's module docstring.

### References
External: Bellotti–Wong, Cor. 1.3, through `MainCorollary.Lbound_le_N_sub_N`.

### Dependencies
**Depends on:** `exists_window_eps`, `Nrect_inner_le_Nhalf`, `N_sub_N_eq_Nrect_one`,
`MainCorollary.Lbound_le_N_sub_N`, `continuous_Lbound_h`.
**Used by:** `Nhalf_one_pos`, `mainPositiveProportionCorollary_jensen_half`,
`mainPositiveProportionCorollary_littlewood_half`. -/
theorem Lbound_le_Nhalf_one {h t : ℝ} (hh : 0 < h) (ht : 1 ≤ t - h) :
    Lbound h t ≤ Nhalf (t - h) (t + h) 1 := by
  obtain ⟨ε0, hε0, hε0h, -, hε0t, hg1, hg2⟩ :=
    exists_window_eps t h 0 1 (by linarith) hh one_pos
  have hbound : ∀ ε, 0 < ε → ε ≤ ε0 → Lbound (h - ε) t ≤ Nhalf (t - h) (t + h) 1 := by
    intro ε hε hεε0
    have hg1' : ∀ s : ℂ, riemannZeta s = 0 → 1 - 1 < s.re → |s.im - (t - h)| ≤ ε →
        s.im = t - h :=
      fun s hs hre him => hg1 s hs (by linarith) (him.trans hεε0)
    have hg2' : ∀ s : ℂ, riemannZeta s = 0 → 1 - 1 < s.re → |s.im - (t + h)| ≤ ε →
        s.im = t + h :=
      fun s hs hre him => hg2 s hs (by linarith) (him.trans hεε0)
    have hin := Nrect_inner_le_Nhalf (T1 := t - h) (T2 := t + h) (α := 1) hε (by linarith)
      (by linarith) hg1' hg2'
    have hN : N (t + h - ε) - N (t - h + ε) = Nrect (t - h + ε) (t + h - ε) 1 :=
      N_sub_N_eq_Nrect_one (by linarith) (by linarith)
    have hL := Lbound_le_N_sub_N (h := h - ε) (t := t) (by linarith) (by linarith)
    rw [show t + (h - ε) = t + h - ε by ring, show t - (h - ε) = t - h + ε by ring] at hL
    have hcast : ((N (t + h - ε) : ℝ) - N (t - h + ε))
        = (Nrect (t - h + ε) (t + h - ε) 1 : ℝ) := by
      exact_mod_cast hN
    linarith
  have hlim : Tendsto (fun ε : ℝ => Lbound (h - ε) t) (𝓝[>] 0) (𝓝 (Lbound h t)) := by
    have hc : Tendsto (fun ε : ℝ => h - ε) (𝓝 0) (𝓝 (h - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at hc
    exact ((continuous_Lbound_h t).tendsto h).comp (hc.mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Lbound (h - ε) t ≤ Nhalf (t - h) (t + h) 1 := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with ε hε
    exact hbound ε hε.1 hε.2.le
  exact le_of_tendsto hlim hev

/-- **Corollary `\ref{cor:main-jensen}` (Jensen) in the half-counting convention:**
`Nhalf(t-h,t+h,α) / Nhalf(t-h,t+h,1) < C_2^J(α,r,h₀,t₀)`, both counts with the page-1 edge
convention.

### Summary of Proof
`mainPositiveProportionCorollary_jensen`'s chain verbatim, with `mainJensenHalf` in place of
`mainJensen` (the corollary already has `h < t^{2/3}`), `Nhalf_nonneg` for the numerator's sign,
and `Lbound_le_Nhalf_one` in place of `Lbound_le_N_sub_N` for the denominator.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4) with the page-1 counting convention.

### Dependencies
**Depends on:** `mainJensenHalf`, `Nhalf_nonneg`, `Lbound_le_Nhalf_one`, and the `MainCorollary`
chain (`h0Threshold_antitone`, `h0Threshold_pos`, `rpow_two_thirds_le_div`,
`C2denom_pos_of_h0Threshold_lt`, `twenty_lt_log`, `C2denom_mul_le_Lbound`,
`Ubound_jensen_div_Lbound_le_C2Jensen`, `C2Jensen_antitone`).
**Used by:** `simpleProportionCorollary_jensen`, `Solution.edge_proportion_jensen`,
`AllHypotheses.mainPositiveProportionCorollary_jensen_half'`. -/
theorem mainPositiveProportionCorollary_jensen_half {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Jensen α r h0 t0 := by
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
  have hmain : Nhalf (t - h) (t + h) α < Ubound_jensen α r h t :=
    mainJensenHalf hα0 hrα hr1 (by unfold alphaBoundTodo; exact hα) hte hhpos.le hht
  have hden : 0 < C2denom h t := C2denom_pos_of_h0Threshold_lt ht12 hthr
  have hlog : (20 : ℝ) < Real.log t := twenty_lt_log ht12
  have hK : 0 < h * Real.log t / Real.pi := div_pos (mul_pos hhpos (by linarith)) Real.pi_pos
  have hL : 0 < Lbound h t :=
    lt_of_lt_of_le (mul_pos hden hK) (C2denom_mul_le_Lbound ht12 hhpos hh23)
  have hNsub : Lbound h t ≤ Nhalf (t - h) (t + h) 1 := Lbound_le_Nhalf_one hhpos hth1
  have hN0 : (0 : ℝ) ≤ Nhalf (t - h) (t + h) α := Nhalf_nonneg (by linarith) (by linarith)
  have hUnn : 0 ≤ Ubound_jensen α r h t := le_trans hN0 hmain.le
  calc Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
      ≤ Nhalf (t - h) (t + h) α / Lbound h t := div_le_div_of_nonneg_left hN0 hL hNsub
    _ < Ubound_jensen α r h t / Lbound h t := div_lt_div_of_pos_right hmain hL
    _ ≤ C2Jensen α r h t := Ubound_jensen_div_Lbound_le_C2Jensen ht12 hhpos hh23 hden hL hUnn
    _ ≤ C2Jensen α r h0 t :=
        (C2Jensen_antitone α r ht12 hα0 hrα hr1).1 (Set.mem_Ioi.mpr (lt_of_le_of_lt hthr0 hh0))
          (Set.mem_Ioi.mpr hthr) hh.le
    _ ≤ C2Jensen α r h0 t0 :=
        (C2Jensen_antitone α r ht0 hα0 hrα hr1).2 h0 hh0 (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr ht.le) ht.le

/-- **Corollary `\ref{cor:main-littlewood}` (Littlewood) in the half-counting convention, with NO
zero-free-edge hypothesis:** `Nhalf(t-h,t+h,α) / Nhalf(t-h,t+h,1) < C_2^L(α,r,h₀,t₀,k)`.

### Summary of Proof
`mainPositiveProportionCorollary_littlewood`'s chain verbatim, with `mainLittlewoodHalf` in place
of `mainLittlewood` — which is what removes `hzf_p`/`hzf_m` from the statement — `Nhalf_nonneg`,
and `Lbound_le_Nhalf_one` for the half-counted denominator.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5) with the page-1 counting convention.

### Dependencies
**Depends on:** `mainLittlewoodHalf`, `Nhalf_nonneg`, `Lbound_le_Nhalf_one`, and the
`MainCorollary` chain (`h0Threshold_antitone`, `h0Threshold_pos`, `rpow_two_thirds_le_div`,
`C2denom_pos_of_h0Threshold_lt`, `twenty_lt_log`, `C2denom_mul_le_Lbound`,
`Ubound_littlewood_div_Lbound_le_C2Littlewood`, `C2Littlewood_antitone`).
**Used by:** `simpleProportionCorollary_littlewood`, `Solution.edge_proportion_littlewood`,
`AllHypotheses.mainPositiveProportionCorollary_littlewood_half'`. -/
theorem mainPositiveProportionCorollary_littlewood_half {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Littlewood α r h0 t0 k := by
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
  have hmain : Nhalf (t - h) (t + h) α < Ubound_littlewood α r h t k :=
    mainLittlewoodHalf hα0 hrα hα hk hk' htee hhpos.le hht
  have hden : 0 < C2denom h t := C2denom_pos_of_h0Threshold_lt ht12 hthr
  have hlog : (20 : ℝ) < Real.log t := twenty_lt_log ht12
  have hK : 0 < h * Real.log t / Real.pi := div_pos (mul_pos hhpos (by linarith)) Real.pi_pos
  have hL : 0 < Lbound h t :=
    lt_of_lt_of_le (mul_pos hden hK) (C2denom_mul_le_Lbound ht12 hhpos hh23)
  have hNsub : Lbound h t ≤ Nhalf (t - h) (t + h) 1 := Lbound_le_Nhalf_one hhpos hth1
  have hN0 : (0 : ℝ) ≤ Nhalf (t - h) (t + h) α := Nhalf_nonneg (by linarith) (by linarith)
  have hUnn : 0 ≤ Ubound_littlewood α r h t k := le_trans hN0 hmain.le
  calc Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
      ≤ Nhalf (t - h) (t + h) α / Lbound h t := div_le_div_of_nonneg_left hN0 hL hNsub
    _ < Ubound_littlewood α r h t k / Lbound h t := div_lt_div_of_pos_right hmain hL
    _ ≤ C2Littlewood α r h t k :=
        Ubound_littlewood_div_Lbound_le_C2Littlewood ht12 hhpos hh23 hrα hden hL hUnn
    _ ≤ C2Littlewood α r h0 t k :=
        (C2Littlewood_antitone α r k ht12 hα0 hrα hr1 hk hk'.le).1
          (Set.mem_Ioi.mpr (lt_of_le_of_lt hthr0 hh0)) (Set.mem_Ioi.mpr hthr) hh.le
    _ ≤ C2Littlewood α r h0 t0 k :=
        (C2Littlewood_antitone α r k ht0 hα0 hrα hr1 hk hk'.le).2 h0 hh0 (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr ht.le) ht.le

/-- **`C_{α,h₀,t₀}` for the Jensen mechanism:** `1 - 2·C₂ᴶ(α,r,h₀,t₀)`, the proportion bound of
Corollary `\ref{cor:simpmain}` (Corollary 1).

### Summary of Proof
A definition.  The zeros of the window that are *not* counted by `2·N(t-h,t+h,α)` are exactly
those with `α ≤ Re ρ ≤ 1-α`, so dividing the window's zero count into the two edge strips and the
middle turns Corollary `\ref{cor:main-jensen}`'s `C₂ᴶ` into the proportion `1 - 2C₂ᴶ`.

### Lean Notes
Positive exactly when `C₂ᴶ(α,r,h₀,t₀) < 1/2`, which is what Table `\ref{tab:C2J}` (Table 8)
tabulates; the definition itself carries no positivity.

### References
tex: `\ref{cor:simpmain}` (Corollary 1) and Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `MainCorollary.C2Jensen`.
**Used by:** `simpleProportionCorollary_jensen`, `simpleProportionCorollary_jensen_mul`,
`simpleProportionCorollary_jensen_prose`, `AllHypotheses.simpleProportionCorollary_jensen_prose'`.
-/
noncomputable def CsimpJensen (α r h0 t0 : ℝ) : ℝ := 1 - 2 * C2Jensen α r h0 t0

/-- **`C_{α,h₀,t₀}` for the Littlewood mechanism:** `1 - 2·C₂ᴸ(α,r,h₀,t₀,k)`.

### Summary of Proof
A definition; see `CsimpJensen`.

### Lean Notes
Positive exactly when `C₂ᴸ(α,r,h₀,t₀,k) < 1/2`, tabulated in Table `\ref{tab:C2L}` (Table 9).
On every row of Table `\ref{table:chat}` (Table 1) but one this is the larger of the two
mechanisms' constants.

### References
tex: `\ref{cor:simpmain}` (Corollary 1) and Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `MainCorollary.C2Littlewood`.
**Used by:** `simpleProportionCorollary_littlewood`. -/
noncomputable def CsimpLittlewood (α r h0 t0 : ℝ) (k : ℤ) : ℝ := 1 - 2 * C2Littlewood α r h0 t0 k

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Jensen mechanism:**
`1 - 2·Nhalf(t-h,t+h,α) / Nhalf(t-h,t+h,1) > C_{α,h₀,t₀}`, both counts with the tex's page-1 edge
convention.

### Summary of Proof
Immediate from `mainPositiveProportionCorollary_jensen_half`: if `x/y < C₂` then
`1 - 2x/y > 1 - 2C₂`.  `mul_div_assoc` puts `2 * x / y` into the shape `2 * (x / y)` that
`linarith` needs.

### Lean Notes
**The statement is the tex's displayed inequality, not its prose.**  The tex reads the left-hand
side as "the proportion of zeros `ρ` with `Im ρ ∈ [t-h,t+h]` for which `Re ρ ∈ [α,1-α]`".  That
reading needs one further step, not formalized here and not proved in the tex either: the zeros of
the window with `Re ρ < α` are as many as those with `Re ρ > 1-α`, because `ρ ↦ 1 - conj ρ` is a
multiplicity-preserving involution of the zero set that fixes `Im` and reflects `Re` about `1/2`.
Mathlib has both ingredients (`riemannZeta_conj` and `riemannZeta_one_sub`, whose multiplier is
zero-free and finite off the real axis), but transporting `analyticOrderAt` — and hence
`MeromorphicOn.divisor`, on which `Nrect` is built — along that involution is a genuine piece of
work rather than a rewriting step.  Until it is done, "`1 - 2N/(N(t+h)-N(t-h))`" is a proved lower
bound for a quantity the reader, not Lean, identifies with the proportion.

### Obstacles
None for the inequality as stated.  The reflection step above is the only gap between this theorem
and the corollary's prose; it is the same gap the tex leaves implicit.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), via `\ref{cor:main-jensen}` (Corollary 4).
Table `\ref{table:chat}` (Table 1) tabulates `CsimpJensen`/`CsimpLittlewood` at fifteen
`(α,h₀,t₀)` triples.

### Dependencies
**Depends on:** `mainPositiveProportionCorollary_jensen_half`, `CsimpJensen`.
**Used by:** `simpleProportionCorollary_jensen_mul`. -/
theorem simpleProportionCorollary_jensen {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    1 - 2 * Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpJensen α r h0 t0 := by
  have hmain :=
    mainPositiveProportionCorollary_jensen_half hα0 hrα hr1 hα ht0 hh0 hh ht hht
  unfold CsimpJensen
  rw [mul_div_assoc]
  linarith

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Littlewood mechanism:**
`1 - 2·Nhalf(t-h,t+h,α) / Nhalf(t-h,t+h,1) > C_{α,h₀,t₀}`, with no zero-free-edge hypothesis.

### Summary of Proof
`simpleProportionCorollary_jensen`'s two lines with
`mainPositiveProportionCorollary_littlewood_half` in place of the Jensen corollary.

### Lean Notes
See `simpleProportionCorollary_jensen` for the one step separating this inequality from the
corollary's prose reading.  This is the mechanism that supplies fourteen of the fifteen rows of
Table `\ref{table:chat}` (Table 1), including the abstract's `α = 1/16`, `h₀ = 100`, `t₀ = 10^100`
example: `C₂ᴸ = 0.4312874…`, hence a proportion of at least `0.1374`.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), via `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `mainPositiveProportionCorollary_littlewood_half`, `CsimpLittlewood`.
**Used by:** `simpleProportionCorollary_littlewood_mul`. -/
theorem simpleProportionCorollary_littlewood {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    1 - 2 * Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpLittlewood α r h0 t0 k := by
  have hmain :=
    mainPositiveProportionCorollary_littlewood_half hα0 hrα hα hk hk' ht0 hh0 hh ht hht
  unfold CsimpLittlewood
  rw [mul_div_assoc]
  linarith

/-- **The half-counted window is non-empty: `0 < Nhalf (t-h) (t+h) 1`.**

### Summary of Proof
The chain already inside `mainPositiveProportionCorollary_jensen_half`, isolated: `Lbound h t` is
positive (`C2denom_pos_of_h0Threshold_lt`, `twenty_lt_log`, `C2denom_mul_le_Lbound`) and bounds
the half count from below (`Lbound_le_Nhalf_one`).

### Lean Notes
Isolated so that `simpleProportionCorollary_jensen_mul`/`_littlewood_mul` can be read without
reconstructing why the denominator of the ratio form is non-zero.

### References
tex: the denominator `N(t+h) - N(t-h)` of `\ref{cor:simpmain}` (Corollary 1),
`\ref{cor:main-jensen}` (Corollary 4) and `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `h0Threshold_pos`, `rpow_two_thirds_le_div`, `C2denom_pos_of_h0Threshold_lt`,
`twenty_lt_log`, `C2denom_mul_le_Lbound`, `Lbound_le_Nhalf_one`.
**Used by:** `simpleProportionCorollary_jensen_mul`, `simpleProportionCorollary_jensen_prose`,
`simpleProportionCorollary_littlewood_mul`, `simpleProportionCorollary_littlewood_prose`. -/
theorem Nhalf_one_pos {h t : ℝ} (ht12 : (10 : ℝ) ^ (12 : ℕ) < t)
    (hthr : h0Threshold t < h) (hh23 : h ≤ t ^ ((2 : ℝ) / 3)) :
    0 < Nhalf (t - h) (t + h) 1 := by
  have hhpos : 0 < h := (h0Threshold_pos ht12).trans hthr
  have hth1 : 1 ≤ t - h := by
    have := rpow_two_thirds_le_div ht12
    linarith
  have hden : 0 < C2denom h t := C2denom_pos_of_h0Threshold_lt ht12 hthr
  have hlog : (20 : ℝ) < Real.log t := twenty_lt_log ht12
  have hK : 0 < h * Real.log t / Real.pi := div_pos (mul_pos hhpos (by linarith)) Real.pi_pos
  have hL : 0 < Lbound h t :=
    lt_of_lt_of_le (mul_pos hden hK) (C2denom_mul_le_Lbound ht12 hhpos hh23)
  exact lt_of_lt_of_le hL (Lbound_le_Nhalf_one hhpos hth1)

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Jensen mechanism, division-free:**
`Nhalf(t-h,t+h,1) - 2·Nhalf(t-h,t+h,α) > C_{α,h₀,t₀} · Nhalf(t-h,t+h,1)`.

### Summary of Proof
`simpleProportionCorollary_jensen` multiplied through by the denominator, which is positive by
`Nhalf_one_pos`.

### Lean Notes
The same content as `simpleProportionCorollary_jensen` in the shape the tex's display would take
after clearing denominators.  Preferred when the statement has to be audited on its own: the ratio
form is only meaningful once the reader knows `Nhalf (t-h) (t+h) 1 ≠ 0`, and here the count and the
bound sit on the same side of a single multiplication.  The left-hand side is the number of zeros
of the window outside the two edge strips — under the reflection step recorded in
`simpleProportionCorollary_jensen`'s Lean Notes, the zeros with `α ≤ Re ρ ≤ 1-α`.

### References
tex: `\ref{cor:simpmain}` (Corollary 1).

### Dependencies
**Depends on:** `simpleProportionCorollary_jensen`, `Nhalf_one_pos`.
**Used by:** `simpleProportionCorollary_jensen_prose`. -/
theorem simpleProportionCorollary_jensen_mul {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) 1 - 2 * Nhalf (t - h) (t + h) α
      > CsimpJensen α r h0 t0 * Nhalf (t - h) (t + h) 1 := by
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have hthr : h0Threshold t < h :=
    lt_of_le_of_lt (h0Threshold_antitone ht0 ht.le) (hh0.trans hh)
  have hpos : 0 < Nhalf (t - h) (t + h) 1 := Nhalf_one_pos ht12 hthr hht.le
  have hratio := simpleProportionCorollary_jensen hα0 hrα hr1 hα ht0 hh0 hh ht hht
  have hne : Nhalf (t - h) (t + h) 1 ≠ 0 := hpos.ne'
  have hmul := mul_lt_mul_of_pos_right hratio hpos
  have hkey : (1 - 2 * Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1)
      * Nhalf (t - h) (t + h) 1 = Nhalf (t - h) (t + h) 1 - 2 * Nhalf (t - h) (t + h) α := by
    field_simp
  rw [hkey] at hmul
  linarith

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Littlewood mechanism, division-free.**

### Summary of Proof
`simpleProportionCorollary_jensen_mul`'s four lines with the Littlewood ratio bound.

### Lean Notes
See `simpleProportionCorollary_jensen_mul`.  This is the form to put in front of a reader who has
not been told that the denominator is non-zero.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), via `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `simpleProportionCorollary_littlewood`, `Nhalf_one_pos`.
**Used by:** `simpleProportionCorollary_littlewood_prose`. -/
theorem simpleProportionCorollary_littlewood_mul {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) 1 - 2 * Nhalf (t - h) (t + h) α
      > CsimpLittlewood α r h0 t0 k * Nhalf (t - h) (t + h) 1 := by
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have hthr : h0Threshold t < h :=
    lt_of_le_of_lt (h0Threshold_antitone ht0 ht.le) (hh0.trans hh)
  have hpos : 0 < Nhalf (t - h) (t + h) 1 := Nhalf_one_pos ht12 hthr hht.le
  have hratio := simpleProportionCorollary_littlewood hα0 hrα hα hk hk' ht0 hh0 hh ht hht
  have hne : Nhalf (t - h) (t + h) 1 ≠ 0 := hpos.ne'
  have hmul := mul_lt_mul_of_pos_right hratio hpos
  have hkey : (1 - 2 * Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1)
      * Nhalf (t - h) (t + h) 1 = Nhalf (t - h) (t + h) 1 - 2 * Nhalf (t - h) (t + h) α := by
    field_simp
  rw [hkey] at hmul
  linarith

/-! ### Corollary 1 in the form the tex's prose states it

`Reflection.lean` proves that `ρ ↦ 1 - conj ρ` preserves the order of vanishing of `ζ` off the
real axis, hence that a window's left edge strip and right edge strip carry equally many zeros.
That turns the tex's `1 - 2N(t-h,t+h,α)/(N(t+h)-N(t-h))` into the honest proportion of the
window's zeros whose real part lies in `[α, 1-α]`. -/

/-- **`NhalfMid T₁ T₂ α` is the tex's count of the window's zeros with `α ≤ Re ρ ≤ 1-α`**, edges
counted with half their multiplicity.

### Summary of Proof
`Definitions.Nhalf`'s definition with `Reflection.NrectMid`/`Reflection.NlineReMid` in place of
`Nrect`/`NlineRe`.

### References
tex: the numerator of `\ref{cor:simpmain}` (Corollary 1) as its prose describes it.

### Dependencies
**Depends on:** `Reflection.NrectMid`, `Reflection.NlineReMid`.
**Used by:** `NhalfMid_eq`, `simpleProportionCorollary_jensen_prose`,
`simpleProportionCorollary_littlewood_prose`. -/
noncomputable def NhalfMid (T₁ T₂ α : ℝ) : ℝ :=
  (NrectMid T₁ T₂ α : ℝ) - (NlineReMid T₂ α : ℝ) / 2 + (NlineReMid T₁ α : ℝ) / 2

/-- **The half-counted middle is the half-counted total minus twice the half-counted edge:**
`NhalfMid T₁ T₂ α = Nhalf T₁ T₂ 1 - 2 · Nhalf T₁ T₂ α`.

### Summary of Proof
`Reflection.NrectMid_eq` on the rectangle and `Reflection.NlineReMid_eq` on each of the two edges,
then arithmetic.

### Lean Notes
This is the identity the tex uses without comment.  Note it needs `α ≤ 1/2`, which `α < 1/6`
supplies, and positive heights, which the window `[t-h, t+h]` has.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), page 1 counting convention.

### Dependencies
**Depends on:** `NhalfMid`, `Definitions.Nhalf`, `Reflection.NrectMid_eq`,
`Reflection.NlineReMid_eq`.
**Used by:** `simpleProportionCorollary_jensen_prose`,
`simpleProportionCorollary_littlewood_prose`. -/
theorem NhalfMid_eq {T₁ T₂ α : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    NhalfMid T₁ T₂ α = Nhalf T₁ T₂ 1 - 2 * Nhalf T₁ T₂ α := by
  unfold NhalfMid Nhalf
  rw [NrectMid_eq hT₁ hα hα2, NlineReMid_eq hT₂ hα hα2, NlineReMid_eq hT₁ hα hα2]
  push_cast
  ring

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Jensen mechanism, in the tex's own words:**
the proportion of the window's zeros whose real part lies in `[α, 1-α]` exceeds `C_{α,h₀,t₀}`.

### Summary of Proof
`NhalfMid_eq` rewrites the numerator as `Nhalf(…,1) - 2·Nhalf(…,α)`, and then this is
`simpleProportionCorollary_jensen_mul` divided by the positive `Nhalf(…,1)`.

### Lean Notes
**This is the statement the tex's prose makes**, as opposed to `simpleProportionCorollary_jensen`,
which is the statement its displayed formula makes.  The two are separated by the reflection
`ρ ↦ 1 - conj ρ`, proved in `Reflection.lean` since 2026-09-11; before that this form was not
available.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), via `\ref{cor:main-jensen}` (Corollary 4).

### Dependencies
**Depends on:** `NhalfMid_eq`, `simpleProportionCorollary_jensen_mul`, `Nhalf_one_pos`.
**Used by:** `AllHypotheses.simpleProportionCorollary_jensen_prose'`. -/
theorem simpleProportionCorollary_jensen_prose {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpJensen α r h0 t0 := by
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have hthr : h0Threshold t < h :=
    lt_of_le_of_lt (h0Threshold_antitone ht0 ht.le) (hh0.trans hh)
  have hhpos : 0 < h := (h0Threshold_pos ht12).trans hthr
  have hth1 : 1 ≤ t - h := by
    have := rpow_two_thirds_le_div ht12
    linarith
  have hpos : 0 < Nhalf (t - h) (t + h) 1 := Nhalf_one_pos ht12 hthr hht.le
  rw [NhalfMid_eq (by linarith) (by linarith) hα0 (by linarith)]
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  have := simpleProportionCorollary_jensen_mul hα0 hrα hr1 hα ht0 hh0 hh ht hht
  linarith

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Littlewood mechanism, in the tex's own words.**

### Summary of Proof
`simpleProportionCorollary_jensen_prose`'s proof with the Littlewood bound.

### Lean Notes
This is the form that supplies Table `\ref{table:chat}` (Table 1): for `α = 1/16`, `h₀ = 100`,
`t₀ = 10^100` it says that at least a `0.1374` fraction of the zeros with imaginary part within
`h` of `t` have real part in `[1/16, 15/16]`, which is the abstract's "at least 13%".

### References
tex: `\ref{cor:simpmain}` (Corollary 1), via `\ref{cor:main-littlewood}` (Corollary 5).

### Dependencies
**Depends on:** `NhalfMid_eq`, `simpleProportionCorollary_littlewood_mul`, `Nhalf_one_pos`.
**Used by:** `AllHypotheses.simpleProportionCorollary_littlewood_prose'`, and through it the
Palomar `Solution.lean`. -/
theorem simpleProportionCorollary_littlewood_prose {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpLittlewood α r h0 t0 k := by
  have ht12 : (10 : ℝ) ^ (12 : ℕ) < t := ht0.trans ht
  have hthr : h0Threshold t < h :=
    lt_of_le_of_lt (h0Threshold_antitone ht0 ht.le) (hh0.trans hh)
  have hhpos : 0 < h := (h0Threshold_pos ht12).trans hthr
  have hth1 : 1 ≤ t - h := by
    have := rpow_two_thirds_le_div ht12
    linarith
  have hpos : 0 < Nhalf (t - h) (t + h) 1 := Nhalf_one_pos ht12 hthr hht.le
  rw [NhalfMid_eq (by linarith) (by linarith) hα0 (by linarith)]
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  have := simpleProportionCorollary_littlewood_mul hα0 hrα hα hk hk' ht0 hh0 hh ht hht
  linarith
