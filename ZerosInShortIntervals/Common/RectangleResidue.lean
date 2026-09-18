/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib

/-! # The residue theorem on a rectangle

Generic complex analysis, no `ζ`: the counterclockwise boundary integral `rectInt a b c d f` of
`f` over the rectangle `[a,b] × [c,d]`, the value `2πi` of `rectInt` for `1/(s - p)` with `p`
inside (`rectInt_inv_sub`, by four explicit logarithmic antiderivatives), and the **residue
theorem** `rectInt_eq_two_pi_I_mul_sum`: for `f` holomorphic on the closed rectangle except at
finitely many interior points `p`, near each of which `f - res p / (s - p)` stays bounded,
`rectInt a b c d f = 2πi Σ res p`. The proof is by induction on the set of poles, removing one pole
at a time with Mathlib's removable-singularity theorem
(`differentiableOn_update_limUnder_of_bddAbove`) and finishing with Cauchy–Goursat for rectangles
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).

The consumer is Littlewood's zero-counting identity, Equation `\ref{eq:zerodensityintegral}`
(Equation 13), in `ZerosInShortIntervals.Littlewood.LittlewoodIdentity`, where these lemmas are
applied to `ζ'/ζ` on the rectangles `[σ, σ1] × [T1, T2]`. The mathematics is textbook
(`\cite[§9.9]{Titchmarsh1986}` uses exactly this residue step, his (9.9.2)). -/


open Complex MeasureTheory intervalIntegral Set

/-- **The counterclockwise boundary integral of `f` over the rectangle `[a,b] × [c,d]`:**
bottom edge `∫_a^b f(x+ic) dx`, minus top edge, plus `i∫_c^d f(b+iy) dy` (right edge), minus
`i∫_c^d f(a+iy) dy` (left edge) — the combination Mathlib's Cauchy–Goursat theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` is stated for.

### References
`\cite[§9.9]{Titchmarsh1986}`, the contour integral "round the rectangle in the positive
direction"; Farzanfard, Lemma 2.2, (2.5).

### Dependencies
**Depends on:** none.
**Used by:** everything in this file; `LittlewoodIdentity.left_edge_identity`. -/
noncomputable def rectInt (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I))
    + I * (∫ y in c..d, f (b + y * I)) - I * ∫ y in c..d, f (a + y * I)

/-- **The closed rectangle `[a,b] × [c,d] ⊆ ℂ`** (`Icc a b ×ℂ Icc c d`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** the Cauchy and residue theorems below; `LittlewoodIdentity.zetaZerosIn`. -/
def rectC (a b c d : ℝ) : Set ℂ := Icc a b ×ℂ Icc c d

/-- **The open rectangle `(a,b) × (c,d) ⊆ ℂ`** (`Ioo a b ×ℂ Ioo c d`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `inRectO_mem_rectO`, `isOpen_rectO`, `rectInt_eq_two_pi_I_mul_sum`,
`rectInt_eq_zero_of_continuousOn_of_differentiableOn`, `rectO_subset_rectC`. -/
def rectO (a b c d : ℝ) : Set ℂ := Ioo a b ×ℂ Ioo c d

/-- **Cauchy–Goursat on a rectangle:** `rectInt a b c d f = 0` for `f` holomorphic on the closed
rectangle. Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, with the
corners `a + ci`, `b + di` unpacked.

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectInt`, `rectC`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum` (base case). -/
theorem rectInt_eq_zero_of_differentiableOn {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (rectC a b c d)) : rectInt a b c d f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (a + c * I) (b + d * I)
    (by
      have e1 : ((a : ℂ) + c * I).re = a := by simp
      have e2 : ((b : ℂ) + d * I).re = b := by simp
      have e3 : ((a : ℂ) + c * I).im = c := by simp
      have e4 : ((b : ℂ) + d * I).im = d := by simp
      rw [e1, e2, e3, e4, uIcc_of_le hab, uIcc_of_le hcd]
      exact hf)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at h
  unfold rectInt
  exact h

/-- **Cauchy–Goursat on a rectangle, continuous-boundary form:** `rectInt a b c d f = 0` for `f`
continuous on the closed rectangle and holomorphic on the open one
(`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectInt`, `rectC`, `rectO`.
**Used by:** none yet. -/
theorem rectInt_eq_zero_of_continuousOn_of_differentiableOn {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) {f : ℂ → ℂ} (hc : ContinuousOn f (rectC a b c d))
    (hf : DifferentiableOn ℂ f (rectO a b c d)) : rectInt a b c d f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    (a + c * I) (b + d * I)
    (by
      have e1 : ((a : ℂ) + c * I).re = a := by simp
      have e2 : ((b : ℂ) + d * I).re = b := by simp
      have e3 : ((a : ℂ) + c * I).im = c := by simp
      have e4 : ((b : ℂ) + d * I).im = d := by simp
      rw [e1, e2, e3, e4, uIcc_of_le hab, uIcc_of_le hcd]
      exact hc)
    (by
      have e1 : ((a : ℂ) + c * I).re = a := by simp
      have e2 : ((b : ℂ) + d * I).re = b := by simp
      have e3 : ((a : ℂ) + c * I).im = c := by simp
      have e4 : ((b : ℂ) + d * I).im = d := by simp
      rw [e1, e2, e3, e4, min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
      exact hf)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at h
  unfold rectInt
  exact h

/-- **`p` lies strictly inside the rectangle `[a,b] × [c,d]`.**

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `inRectO_mem_rectC`, `inRectO_mem_rectO`, `not_inRectO_of_mem_rectB`,
`rectInt_eq_two_pi_I_mul_sum`, `rectInt_inv_sub`, `LittlewoodIdentity.left_edge_identity`,
`LittlewoodIdentity.zetaZerosIn_inRectO`. -/
def InRectO (a b c d : ℝ) (p : ℂ) : Prop := a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d

/-- **Antiderivative of `1/(s−p)` along a horizontal edge:** `x ↦ log(x + it − p)` has derivative
`(x + it − p)⁻¹` where `x + it − p` is in the slit plane (`Complex.hasStrictDerivAt_log`,
`HasDerivAt.comp_ofReal`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_inv_sub`. -/
theorem hasDerivAt_log_line_re {p : ℂ} {t x : ℝ} (hmem : (x : ℂ) + t * I - p ∈ slitPlane) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + t * I - p)) (((x : ℂ) + t * I - p)⁻¹) x := by
  have h1 : HasDerivAt (fun w : ℂ => w + t * I - p) 1 (x : ℂ) :=
    ((hasDerivAt_id _).add_const _).sub_const _
  have h2 := (Complex.hasStrictDerivAt_log hmem).hasDerivAt.comp (x : ℂ) h1
  rw [mul_one] at h2
  exact h2.comp_ofReal

/-- **Antiderivative of `i/(s−p)` along a vertical edge:** `y ↦ log(s + iy − p)` has derivative
`(s + iy − p)⁻¹ · i` where `s + iy − p` is in the slit plane.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_inv_sub` (right edge). -/
theorem hasDerivAt_log_line_im {p : ℂ} {s y : ℝ} (hmem : (s : ℂ) + y * I - p ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log ((s : ℂ) + t * I - p))
      (((s : ℂ) + y * I - p)⁻¹ * I) y := by
  have h1 : HasDerivAt (fun w : ℂ => (s : ℂ) + w * I - p) I (y : ℂ) := by
    have := ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (s : ℂ)
    simpa using this.sub_const p
  have h2 := (Complex.hasStrictDerivAt_log hmem).hasDerivAt.comp (y : ℂ) h1
  exact h2.comp_ofReal

/-- **Antiderivative of `i/(s−p)` along a vertical edge to the *left* of `p`:**
`y ↦ log(p − (s + iy))` has derivative `i · (s + iy − p)⁻¹` where `p − (s+iy)` is in the slit
plane — the branch `log(p − ·)` is needed because `s + iy − p` itself crosses the negative real
axis on the left edge.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_inv_sub` (left edge). -/
theorem hasDerivAt_log_line_im_neg {p : ℂ} {s y : ℝ} (hmem : p - ((s : ℂ) + y * I) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (p - ((s : ℂ) + t * I)))
      (I * ((s : ℂ) + y * I - p)⁻¹) y := by
  have h1 : HasDerivAt (fun w : ℂ => p - ((s : ℂ) + w * I)) (-I) (y : ℂ) := by
    have := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (s : ℂ)).const_sub p
    simpa using this
  have h2 := (Complex.hasStrictDerivAt_log hmem).hasDerivAt.comp (y : ℂ) h1
  refine h2.comp_ofReal.congr_deriv ?_
  have hne : p - ((s : ℂ) + y * I) ≠ 0 := slitPlane_ne_zero hmem
  have hne' : (s : ℂ) + y * I - p ≠ 0 := by
    intro h; apply hne; linear_combination -h
  field_simp
  ring

/-- **`x ↦ (x + it − p)⁻¹` is continuous on a horizontal edge not through `p`.**

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_inv_sub`. -/
theorem continuousOn_inv_sub_line_re {p : ℂ} {t a b : ℝ} (ht : t ≠ p.im) :
    ContinuousOn (fun x : ℝ => ((x : ℂ) + t * I - p)⁻¹) (uIcc a b) := by
  apply Continuous.continuousOn
  apply Continuous.inv₀ (by fun_prop)
  intro x h
  have := congrArg Complex.im h
  simp at this
  exact ht (by linarith)

/-- **`y ↦ (s + iy − p)⁻¹` is continuous on a vertical edge not through `p`.**

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_inv_sub`. -/
theorem continuousOn_inv_sub_line_im {p : ℂ} {s c d : ℝ} (hs : s ≠ p.re) :
    ContinuousOn (fun y : ℝ => ((s : ℂ) + y * I - p)⁻¹) (uIcc c d) := by
  apply Continuous.continuousOn
  apply Continuous.inv₀ (by fun_prop)
  intro y h
  have := congrArg Complex.re h
  simp at this
  exact hs (by linarith)

/-- **`∮_{∂R} ds/(s − p) = 2πi` for `p` inside the rectangle.**

### Summary of Proof
Each edge is evaluated by the fundamental theorem of calculus with an explicit logarithmic
antiderivative: `log(s − p)` on the bottom, top and right edges (where `s − p` stays in the slit
plane, having constant nonzero imaginary part resp. positive real part), and `log(p − s)` on the
left edge (where `p − s` has positive real part). The eight boundary values collapse to
`log w2 − log w1 − log(−w2) + log(−w1)` with `w1 = a + ic − p` (third quadrant), `w2 = a + id − p`
(second quadrant), and `log(−w) = log w ∓ iπ` according to the sign of `Im w`
(`Complex.arg_neg_eq_arg_sub_pi_of_im_pos`, `Complex.arg_neg_eq_arg_add_pi_of_im_neg`) gives `2πi`.

### References
Standard; `\cite[§9.9]{Titchmarsh1986}` (9.9.2) uses it implicitly.

### Dependencies
**Depends on:** `rectInt`, `InRectO`, `hasDerivAt_log_line_re`, `hasDerivAt_log_line_im`,
`hasDerivAt_log_line_im_neg`, `continuousOn_inv_sub_line_re`, `continuousOn_inv_sub_line_im`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectInt_inv_sub {a b c d : ℝ} {p : ℂ} (hp : InRectO a b c d p) :
    rectInt a b c d (fun s => (s - p)⁻¹) = 2 * Real.pi * I := by
  obtain ⟨hpa, hpb, hpc, hpd⟩ := hp
  -- bottom edge
  have hbot : ∫ x in a..b, ((x : ℂ) + c * I - p)⁻¹
      = Complex.log ((b : ℂ) + c * I - p) - Complex.log ((a : ℂ) + c * I - p) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      apply hasDerivAt_log_line_re
      rw [mem_slitPlane_iff]; right; simp; linarith
    · exact (continuousOn_inv_sub_line_re (by linarith)).intervalIntegrable
  -- top edge
  have htop : ∫ x in a..b, ((x : ℂ) + d * I - p)⁻¹
      = Complex.log ((b : ℂ) + d * I - p) - Complex.log ((a : ℂ) + d * I - p) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      apply hasDerivAt_log_line_re
      rw [mem_slitPlane_iff]; right; simp; linarith
    · exact (continuousOn_inv_sub_line_re (by linarith)).intervalIntegrable
  -- right edge
  have hright : ∫ y in c..d, ((b : ℂ) + y * I - p)⁻¹ * I
      = Complex.log ((b : ℂ) + d * I - p) - Complex.log ((b : ℂ) + c * I - p) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro y _
      apply hasDerivAt_log_line_im
      rw [mem_slitPlane_iff]; left; simp; linarith
    · exact ((continuousOn_inv_sub_line_im (by linarith)).mul continuousOn_const).intervalIntegrable
  -- left edge
  have hleft : ∫ y in c..d, I * ((a : ℂ) + y * I - p)⁻¹
      = Complex.log (p - ((a : ℂ) + d * I)) - Complex.log (p - ((a : ℂ) + c * I)) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro y _
      apply hasDerivAt_log_line_im_neg
      rw [mem_slitPlane_iff]; left; simp; linarith
    · exact (continuousOn_const.mul (continuousOn_inv_sub_line_im (by linarith))).intervalIntegrable
  have hr : I * ∫ y in c..d, ((b : ℂ) + y * I - p)⁻¹
      = Complex.log ((b : ℂ) + d * I - p) - Complex.log ((b : ℂ) + c * I - p) := by
    rw [← hright, ← intervalIntegral.integral_const_mul]
    congr 1; funext y; ring
  have hl : I * ∫ y in c..d, ((a : ℂ) + y * I - p)⁻¹
      = Complex.log (p - ((a : ℂ) + d * I)) - Complex.log (p - ((a : ℂ) + c * I)) := by
    rw [← hleft, ← intervalIntegral.integral_const_mul]
  unfold rectInt
  simp only
  rw [hbot, htop, hr, hl]
  -- the four logarithms: `w1 = a + ci - p` (third quadrant), `w2 = a + di - p` (second quadrant)
  set w1 : ℂ := (a : ℂ) + c * I - p with hw1
  set w2 : ℂ := (a : ℂ) + d * I - p with hw2
  have hn1 : p - ((a : ℂ) + c * I) = -w1 := by rw [hw1]; ring
  have hn2 : p - ((a : ℂ) + d * I) = -w2 := by rw [hw2]; ring
  rw [hn1, hn2]
  have hw1im : w1.im < 0 := by rw [hw1]; simp; linarith
  have hw2im : 0 < w2.im := by rw [hw2]; simp; linarith
  have hlog1 : Complex.log (-w1) = Complex.log w1 + Real.pi * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp only [Complex.log_im, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero]
      exact Complex.arg_neg_eq_arg_add_pi_of_im_neg hw1im
  have hlog2 : Complex.log (-w2) = Complex.log w2 - Real.pi * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp only [Complex.log_im, sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero]
      exact Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw2im
  rw [hlog1, hlog2]
  ring

/-! ### Linearity of `rectInt` on the boundary -/

/-- **The boundary of the rectangle `[a,b] × [c,d]`**, as the union of its four edges (images of
`uIcc a b` resp. `uIcc c d`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectInt_add`, `rectInt_congr`, `rectB_subset_rectC`, `not_inRectO_of_mem_rectB`,
`rectInt_eq_two_pi_I_mul_sum`. -/
def rectB (a b c d : ℝ) : Set ℂ :=
  ((fun x : ℝ => (x : ℂ) + c * I) '' uIcc a b) ∪ ((fun x : ℝ => (x : ℂ) + d * I) '' uIcc a b)
    ∪ ((fun y : ℝ => (b : ℂ) + y * I) '' uIcc c d) ∪ ((fun y : ℝ => (a : ℂ) + y * I) '' uIcc c d)

/-- **`rectInt` is additive** for functions continuous on the boundary (each edge integrand is then
interval-integrable).

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectInt`, `rectB`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectInt_add {a b c d : ℝ} {f g : ℂ → ℂ} (hf : ContinuousOn f (rectB a b c d))
    (hg : ContinuousOn g (rectB a b c d)) :
    rectInt a b c d (fun s => f s + g s) = rectInt a b c d f + rectInt a b c d g := by
  have hcont : ∀ h : ℂ → ℂ, ContinuousOn h (rectB a b c d) →
      IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + c * I)) volume a b ∧
      IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + d * I)) volume a b ∧
      IntervalIntegrable (fun y : ℝ => h ((b : ℂ) + y * I)) volume c d ∧
      IntervalIntegrable (fun y : ℝ => h ((a : ℂ) + y * I)) volume c d := by
    intro h hh
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable
    · exact hh.comp (by fun_prop) (fun x hx => by
        unfold rectB; left; left; left; exact ⟨x, hx, rfl⟩)
    · exact hh.comp (by fun_prop) (fun x hx => by
        unfold rectB; left; left; right; exact ⟨x, hx, rfl⟩)
    · exact hh.comp (by fun_prop) (fun y hy => by
        unfold rectB; left; right; exact ⟨y, hy, rfl⟩)
    · exact hh.comp (by fun_prop) (fun y hy => by
        unfold rectB; right; exact ⟨y, hy, rfl⟩)
  obtain ⟨f1, f2, f3, f4⟩ := hcont f hf
  obtain ⟨g1, g2, g3, g4⟩ := hcont g hg
  unfold rectInt
  simp only
  rw [integral_add f1 g1, integral_add f2 g2, integral_add f3 g3, integral_add f4 g4]
  ring

/-- **`rectInt` commutes with scalar multiplication.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectInt`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectInt_const_mul (a b c d : ℝ) (r : ℂ) (f : ℂ → ℂ) :
    rectInt a b c d (fun s => r * f s) = r * rectInt a b c d f := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- **`rectInt` only sees the boundary values.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectInt`, `rectB`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectInt_congr {a b c d : ℝ} {f g : ℂ → ℂ} (h : EqOn f g (rectB a b c d)) :
    rectInt a b c d f = rectInt a b c d g := by
  unfold rectInt
  have e1 : ∫ x in a..b, f ((x : ℂ) + c * I) = ∫ x in a..b, g ((x : ℂ) + c * I) :=
    integral_congr fun x hx => h (by unfold rectB; left; left; left; exact ⟨x, hx, rfl⟩)
  have e2 : ∫ x in a..b, f ((x : ℂ) + d * I) = ∫ x in a..b, g ((x : ℂ) + d * I) :=
    integral_congr fun x hx => h (by unfold rectB; left; left; right; exact ⟨x, hx, rfl⟩)
  have e3 : ∫ y in c..d, f ((b : ℂ) + y * I) = ∫ y in c..d, g ((b : ℂ) + y * I) :=
    integral_congr fun y hy => h (by unfold rectB; left; right; exact ⟨y, hy, rfl⟩)
  have e4 : ∫ y in c..d, f ((a : ℂ) + y * I) = ∫ y in c..d, g ((a : ℂ) + y * I) :=
    integral_congr fun y hy => h (by unfold rectB; right; exact ⟨y, hy, rfl⟩)
  rw [e1, e2, e3, e4]

/-- **The boundary lies in the closed rectangle.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectB`, `rectC`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectB_subset_rectC {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    rectB a b c d ⊆ rectC a b c d := by
  intro s hs
  unfold rectB at hs
  rw [uIcc_of_le hab, uIcc_of_le hcd] at hs
  unfold rectC
  rw [mem_reProdIm]
  rcases hs with ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
  · simpa using ⟨hx, hcd⟩
  · simpa using ⟨hx, hcd⟩
  · simpa using ⟨hab, hy⟩
  · simpa using ⟨hab, hy⟩

/-- **A boundary point is not an interior point.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectB`, `InRectO`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem not_inRectO_of_mem_rectB {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {s : ℂ}
    (hs : s ∈ rectB a b c d) : ¬ InRectO a b c d s := by
  unfold rectB at hs
  rw [uIcc_of_le hab, uIcc_of_le hcd] at hs
  unfold InRectO
  rcases hs with ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩ <;> simp

/-- **An interior point lies in the closed rectangle.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `InRectO`, `rectC`.
**Used by:** none yet. -/
theorem inRectO_mem_rectC {a b c d : ℝ} {p : ℂ} (hp : InRectO a b c d p) : p ∈ rectC a b c d := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold rectC; rw [mem_reProdIm]; exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩

/-- **An interior point lies in the open rectangle.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `InRectO`, `rectO`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem inRectO_mem_rectO {a b c d : ℝ} {p : ℂ} (hp : InRectO a b c d p) : p ∈ rectO a b c d := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold rectO; rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- **The open rectangle is open** (`IsOpen.reProdIm`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectO`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem isOpen_rectO (a b c d : ℝ) : IsOpen (rectO a b c d) := isOpen_Ioo.reProdIm isOpen_Ioo

/-- **The open rectangle lies in the closed one.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectO`, `rectC`.
**Used by:** `rectInt_eq_two_pi_I_mul_sum`. -/
theorem rectO_subset_rectC (a b c d : ℝ) : rectO a b c d ⊆ rectC a b c d := by
  intro s hs
  unfold rectO rectC at *
  rw [mem_reProdIm] at *
  exact ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩

/-! ### The residue theorem on a rectangle, for finitely many poles -/

/-- **The residue theorem on a rectangle.** If `f` is holomorphic on the closed rectangle except
at finitely many interior points `p ∈ P`, near each of which `f − res p / (s − p)` stays bounded,
then `rectInt a b c d f = 2πi Σ_{p ∈ P} res p`.

### Summary of Proof
Induction on `P`. For `P = ∅` this is Cauchy–Goursat (`rectInt_eq_zero_of_differentiableOn`).
For `insert p P'`, let `g := f − res p/(s − p)`; its singularity at `p` is removable
(`differentiableOn_update_limUnder_of_bddAbove`, Mathlib's removable-singularity theorem, on a
small ball around `p` avoiding `P'`), so the patched `f₁ := update g p (lim g)` is holomorphic on
the closed rectangle minus `P'` and satisfies the boundedness hypothesis at each `q ∈ P'` (the
extra term `res p/(s − p)` is bounded near `q ≠ p`). By induction `rectInt f₁ = 2πi Σ_{P'} res`;
on the boundary `f = f₁ + res p·(s − p)⁻¹`, so `rectInt_add`, `rectInt_const_mul`, `rectInt_congr`
and `rectInt_inv_sub` give the extra `2πi·res p`.

### Lean Notes
The boundedness hypothesis is the form in which residues are available for `ζ'/ζ`
(`LittlewoodIdentity.zeta_logDeriv_sub_bounded`); no meromorphy API is needed. The universally
quantified `f` in the statement is what makes the induction go through (the induction step
changes the function).

### References
`\cite[§9.9]{Titchmarsh1986}`, the residue step (9.9.2); Farzanfard, Lemma 2.2, (2.7).

### Dependencies
**Depends on:** `rectInt`, `rectC`, `rectO`, `InRectO`, `rectB`,
`rectInt_eq_zero_of_differentiableOn`, `rectInt_inv_sub`, `rectInt_add`, `rectInt_const_mul`,
`rectInt_congr`, `rectB_subset_rectC`, `not_inRectO_of_mem_rectB`, `inRectO_mem_rectO`,
`isOpen_rectO`, `rectO_subset_rectC`.
**Used by:** `LittlewoodIdentity.left_edge_identity`. -/
theorem rectInt_eq_two_pi_I_mul_sum {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (P : Finset ℂ) (res : ℂ → ℂ) (hP : ∀ p ∈ P, InRectO a b c d p) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (rectC a b c d \ (P : Set ℂ)) →
    (∀ p ∈ P, ∃ r > 0, ∃ M : ℝ, ∀ z ∈ Metric.ball p r \ {p}, ‖f z - res p / (z - p)‖ ≤ M) →
    rectInt a b c d f = 2 * Real.pi * I * ∑ p ∈ P, res p := by
  induction P using Finset.induction_on with
  | empty =>
    intro f hf _
    simp only [Finset.coe_empty, Set.sdiff_empty, Finset.sum_empty, mul_zero] at hf ⊢
    exact rectInt_eq_zero_of_differentiableOn hab.le hcd.le hf
  | insert p P' hpP' ih =>
    intro f hf hres
    have hp : InRectO a b c d p := hP p (Finset.mem_insert_self p P')
    have hP' : ∀ q ∈ P', InRectO a b c d q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    -- the function with the pole at `p` removed
    set g : ℂ → ℂ := fun s => f s - res p / (s - p) with hg
    set f₁ : ℂ → ℂ := Function.update g p (Filter.limUnder (nhdsWithin p {p}ᶜ) g) with hf₁
    -- a small ball around `p` inside the open rectangle, avoiding `P'`, inside the `hres` ball
    obtain ⟨r0, hr0, M, hM⟩ := hres p (Finset.mem_insert_self p P')
    have hopen : rectO a b c d \ (P' : Set ℂ) ∈ nhds p := by
      apply IsOpen.mem_nhds
      · exact (isOpen_rectO a b c d).sdiff (Finset.finite_toSet P').isClosed
      · exact ⟨inRectO_mem_rectO hp, by simpa using hpP'⟩
    obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp hopen
    set r := min r0 r1 with hr
    have hrpos : 0 < r := lt_min hr0 hr1
    have hball : Metric.ball p r ⊆ rectO a b c d \ (P' : Set ℂ) :=
      (Metric.ball_subset_ball (min_le_right _ _)).trans hball1
    have hballr0 : Metric.ball p r ⊆ Metric.ball p r0 := Metric.ball_subset_ball (min_le_left _ _)
    -- `g` is differentiable off `P`, and on the punctured ball
    have hg_diff : DifferentiableOn ℂ g (rectC a b c d \ ((insert p P' : Finset ℂ) : Set ℂ)) := by
      intro s hs
      have hsp : s ≠ p := by
        intro h; apply hs.2; rw [h]; exact Finset.mem_coe.mpr (Finset.mem_insert_self p P')
      exact (hf s hs).sub ((differentiableWithinAt_const _).div
        ((differentiableWithinAt_id).sub_const _) (sub_ne_zero.mpr hsp))
    have hg_ball : DifferentiableOn ℂ g (Metric.ball p r \ {p}) := by
      intro s hs
      have hs' : s ∈ rectC a b c d \ ((insert p P' : Finset ℂ) : Set ℂ) := by
        have h1 := hball hs.1
        refine ⟨rectO_subset_rectC _ _ _ _ h1.1, ?_⟩
        intro h2
        rw [Finset.coe_insert] at h2
        rcases h2 with h2 | h2
        · exact hs.2 h2
        · exact h1.2 h2
      exact (hg_diff s hs').mono (by
        intro z hz
        have h1 := hball hz.1
        refine ⟨rectO_subset_rectC _ _ _ _ h1.1, ?_⟩
        intro h2
        rw [Finset.coe_insert] at h2
        rcases h2 with h2 | h2
        · exact hz.2 h2
        · exact h1.2 h2)
    have hg_bdd : BddAbove (norm ∘ g '' (Metric.ball p r \ {p})) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hM z ⟨hballr0 hz.1, hz.2⟩
    have hf₁_ball : DifferentiableOn ℂ f₁ (Metric.ball p r) :=
      differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds p hrpos) hg_ball hg_bdd
    -- `f₁` is differentiable on the closed rectangle minus `P'`
    have hf₁_diff : DifferentiableOn ℂ f₁ (rectC a b c d \ (P' : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · subst hsp
        exact (hf₁_ball.differentiableAt (Metric.ball_mem_nhds s hrpos)).differentiableWithinAt
      · have hs' : s ∈ rectC a b c d \ ((insert p P' : Finset ℂ) : Set ℂ) := by
          refine ⟨hs.1, ?_⟩
          intro h
          rw [Finset.coe_insert] at h
          rcases h with h | h
          · exact hsp h
          · exact hs.2 h
        have hgs := hg_diff s hs'
        have hmem : rectC a b c d \ ((insert p P' : Finset ℂ) : Set ℂ)
            ∈ nhdsWithin s (rectC a b c d \ (P' : Set ℂ)) := by
          apply mem_nhdsWithin.mpr
          refine ⟨{p}ᶜ, isOpen_compl_singleton, hsp, ?_⟩
          intro z hz
          refine ⟨hz.2.1, ?_⟩
          intro h
          rw [Finset.coe_insert] at h
          rcases h with h | h
          · exact hz.1 h
          · exact hz.2.2 h
        have hgs' := hgs.mono_of_mem_nhdsWithin hmem
        apply hgs'.congr_of_eventuallyEq
        · have : {p}ᶜ ∈ nhdsWithin s (rectC a b c d \ (P' : Set ℂ)) :=
            mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
          filter_upwards [this] with z hz
          exact Function.update_of_ne hz _ _
        · exact Function.update_of_ne hsp _ _
    -- residue bounds for `f₁` at the remaining poles
    have hres' : ∀ q ∈ P', ∃ r > 0, ∃ M : ℝ,
        ∀ z ∈ Metric.ball q r \ {q}, ‖f₁ z - res q / (z - q)‖ ≤ M := by
      intro q hq
      obtain ⟨rq, hrq, Mq, hMq⟩ := hres q (Finset.mem_insert_of_mem hq)
      have hqp : q ≠ p := by intro h; apply hpP'; rw [← h]; exact hq
      have hdpos : 0 < dist q p := dist_pos.mpr hqp
      refine ⟨min rq (dist q p / 2), lt_min hrq (by linarith), Mq + ‖res p‖ / (dist q p / 2), ?_⟩
      intro z hz
      have hz1 : z ∈ Metric.ball q rq := Metric.ball_subset_ball (min_le_left _ _) hz.1
      have hz2 : dist z q < dist q p / 2 :=
        lt_of_lt_of_le (Metric.mem_ball.mp hz.1) (min_le_right _ _)
      have hzp : z ≠ p := by
        intro h; subst h
        have := dist_comm z q ▸ hz2
        linarith [dist_comm q z]
      have hzp' : dist q p / 2 ≤ dist z p := by
        have := dist_triangle q z p
        rw [dist_comm q z] at this
        linarith
      have hf₁z : f₁ z = g z := Function.update_of_ne hzp _ _
      rw [hf₁z, hg]
      simp only
      have e : f z - res p / (z - p) - res q / (z - q)
          = (f z - res q / (z - q)) - res p / (z - p) := by ring
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add (hMq z ⟨hz1, hz.2⟩) ?_)
      rw [norm_div]
      have hzp0 : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
      rw [div_le_div_iff₀ hzp0 (by linarith)]
      have : dist z p = ‖z - p‖ := dist_eq_norm z p
      nlinarith [norm_nonneg (res p)]
    have ih' := ih hP' f₁ hf₁_diff hres'
    -- relate `rectInt f` to `rectInt f₁`
    have hcontf : ContinuousOn f (rectB a b c d) := by
      apply hf.continuousOn.mono
      intro s hs
      refine ⟨rectB_subset_rectC hab.le hcd.le hs, ?_⟩
      intro h
      exact not_inRectO_of_mem_rectB hab.le hcd.le hs (hP s (Finset.mem_coe.mp h))
    have hcontf₁ : ContinuousOn f₁ (rectB a b c d) := by
      apply hf₁_diff.continuousOn.mono
      intro s hs
      refine ⟨rectB_subset_rectC hab.le hcd.le hs, ?_⟩
      intro h
      exact not_inRectO_of_mem_rectB hab.le hcd.le hs (hP' s (Finset.mem_coe.mp h))
    have hcontinv : ContinuousOn (fun s => res p * (s - p)⁻¹) (rectB a b c d) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const))
      intro s hs
      apply sub_ne_zero.mpr
      intro h; subst h
      exact not_inRectO_of_mem_rectB hab.le hcd.le hs hp
    have hsplit : rectInt a b c d f
        = rectInt a b c d f₁ + res p * rectInt a b c d (fun s => (s - p)⁻¹) := by
      rw [← rectInt_const_mul, ← rectInt_add hcontf₁ hcontinv]
      apply rectInt_congr
      intro s hs
      have hsp : s ≠ p := by
        intro h; subst h; exact not_inRectO_of_mem_rectB hab.le hcd.le hs hp
      simp only [hf₁, Function.update_of_ne hsp, hg]
      field_simp
      ring
    rw [hsplit, ih', rectInt_inv_sub hp, Finset.sum_insert hpP']
    ring
