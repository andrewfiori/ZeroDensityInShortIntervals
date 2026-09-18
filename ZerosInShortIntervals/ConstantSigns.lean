/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodShort

/-! # Sign facts about the constants `B_{i,α,r}` and `A_{i,α,r}`

Non-negativity of the coefficients of `U_J` (`B1`–`B4`, via `c1_nonneg`, `c2_nonneg`,
`c3_nonneg`, `two_Phi_one_add_c5_nonneg`) and of `U_L` (`A1`, `A2`, `A4`, `A5`, `A6`, via
`chord_vCoeff_nonneg`, `c4_nonneg`, `c3_nonneg`), together with the lower bound `-A₂ ≤ A₃`
(`neg_A2_le_A3`), which stands in for the sign of `A₃` — that one genuinely can be negative, so
`0 ≤ A₃` is false.

**Why they live together.** `ZerosInShortIntervals.MainCorollary` uses them to make the ratios `C₂`
of Corollaries `\ref{cor:main-jensen}` and `\ref{cor:main-littlewood}` (Corollaries 4 and 5)
non-negative and monotone. `MainTheorem.mainJensen`/`mainLittlewood` (Theorems 2 and 3) need them
too: for `t ≤ 10^12` the count `Nrect (t-h) (t+h) α` vanishes (Platt–Trudgian, via
`MainTheorem.Nrect_eq_zero_of_le_H0`), so there the theorems reduce to the positivity of their
right-hand sides `U + O^*`, which is exactly these sign facts plus `log log t ≥ 0` (Jensen) resp.
`log log t ≥ 1` (Littlewood, because only `-A₂ ≤ A₃` is available). This file sits below both.

Each lemma's docstring says where it *belongs* (`JensenScaleConstants.lean`,
`RectangularBounds.lean`, `JensenBounds.lean`, `LittlewoodShort.lean`); those are the eventual
destinations. `c3_nonneg` is proved by the closed-form/tangent-line development that opens this
file (margin `0.0165` against terms of size `1`, so the analysis has to be near-sharp on
`[1/2, 5/7]`). -/

/-! ## `0 ≤ c_{3,r}`: closed forms per chord regime and a tangent-line argument

`c_{3,r} = ∫_0^{π/2} A''(1 - r sin φ) dφ`, where `A''` is the piecewise-linear interpolant — in
the sense of Equation `\ref{eq:mkpp}` (Equation 7) — of the double-primed data `v''_k` from the
display following Equation `\ref{eq:sigmak}` (Equation 4), at the abscissae `σ_k`.
In Lean `c3` is the series of `JensenScaleConstants.c3`, indexed from `K = Kidx r`.  The data are

* `v''_k = log 1.546 =: L` for `k ≥ 1`, so `A'' ≡ L` on `[5/7, 1]`;
* `v''_0 = log 0.611 =: L₀ < 0`, so `A''` dips to `L₀` at `σ_0 = 1/2` along the two chords
  `m_0 σ + b_0` on `[1/2, 5/7]` and `m_{-1} σ + b_{-1}` on `[2/7, 1/2]`;
* `v''_k = L + (σ_k - 1/2) log π` for `k ≤ -1`, which is *linear* in `σ_k`, so every chord with
  `k ≤ -2` is the same line `log π · σ + (L - (log π)/2)` on `[0, 2/7]`.

With `a_k := 1 - σ_k` (`a_{-1} = 5/7`, `a_0 = 1/2`, `a_1 = 2/7`), `θ_a(r) := arcsin(a/r)` and
`u_a(r) := √(r² - a²) = r cos θ_a(r)`, each chord contributes a block
`(m + b)·θ_a(r) + m·u_a(r)` (`chordBlock`), and `c3 r` has four closed forms:

| regime | `Kidx r` | `c3 r` |
|---|---|---|
| `r < 2/7` | `≥ 2` | `L π/2` |
| `2/7 ≤ r < 1/2` | `1` | `c3G1 r` |
| `1/2 ≤ r < 5/7` | `0` | `c3G0 r` (the tight one: minimum `0.016499` at `r = 0.57762`) |
| `5/7 ≤ r < 1` | `≤ -1` | `c3F r` (uniform in `K`, by telescoping the identical linear chords) |

The three functions agree at the regime boundaries (`c3G1 (1/2) = c3G0 (1/2)`,
`c3F (5/7) = c3G0 (5/7)`), so everything reduces to `c3G0` on `[1/2, 5/7]` plus `c3F 1 ≈ 0.0602`:

* `c3G1' = -m_0 cos θ_{a_1} ≤ 0`, so `c3G1 ≥ c3G1 (1/2) = c3G0 (1/2)` on `[2/7, 1/2]`;
* `c3G0' = (m_0 - m_{-1}) cos θ_{a_0} - m_0 cos θ_{a_1}` and `c3G0'' ≥ 0`, so `c3G0` is convex and
  lies above its tangent at `r₁ = 1/√3` (where `θ_{a_0} = π/3` exactly, `cos θ_{a_1} = √37/7`):
  `c3G0 r₁ = 0.016500`, `|c3G0' r₁| = 0.0047 ≤ 0.006`, whence `c3G0 ≥ 0.012` on `[1/2, 5/7]`;
* `c3F' = -m_0 cos θ_{a_{-1}} + (m_0 - m_{-1}) cos θ_{a_0} - m_0 cos θ_{a_1}` and `c3F'' ≤ 0`, so
  `c3F` is concave and `c3F ≥ min (c3F (5/7), c3F 1) = min (c3G0 (5/7), 0.0602) ≥ 0.012`.

The derivative formulas simplify because consecutive chords agree at their common abscissa; the
second-derivative signs need only `u_{a}` decreasing in `a` and the two crude coefficient
inequalities `82 m_0 ≥ 49 log π`, `49 (m_0 - m_{-1}) ≤ 100 m_0`.  The only transcendental inputs are
`log 1.546`, `log 0.611`, `log π` to five–six decimals (`Real.abs_log_sub_add_sum_range_le`),
`π` to six (`Real.pi_gt_d6`), and one-sided `arcsin` bounds from `sin x > x - x³/6` and
`cos x ≥ 1 - x²/2`.  Every numeric step is re-checked in exact rational arithmetic by
`Code/verify_c3_tangent_route.py`.
-/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **`L = log 1.546`**, the constant chord value for `k ≥ 1` (`vCoeffPP k` for `k > 0`).

### Summary of Proof
Definition; `0.435669 ≤ L ≤ 0.435672` is `c3L_bounds`.

### References
tex: the `v''_k` display following Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** none.
**Used by:** `c3m0`, `c3G1`, `c3G0`, `c3F`, `c3L_bounds`. -/
noncomputable def c3L : ℝ := Real.log 1.546

/-- **`L₀ = log 0.611`**, the negative chord value at `σ_0 = 1/2` (`vCoeffPP 0`).

### Summary of Proof
Definition; `-0.49266 ≤ L₀ ≤ -0.492657` is `c3L0_bounds`.

### References
tex: the `v''_k` display following Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** none.
**Used by:** `c3m0`, `c3b0`, `c3bNeg1`, `c3L0_bounds`. -/
noncomputable def c3L0 : ℝ := Real.log 0.611

/-- **`log π`**, the slope of the linear chord data `v''_k = L + (σ_k - 1/2) log π` for `k ≤ -1`.

### Summary of Proof
Definition; `1.14472 ≤ log π ≤ 1.14474` is `logPi_bounds`.

### References
tex: the `v''_k` display following Equation `\ref{eq:sigmak}` (Equation 4), whose `k < 0` case
reads `v''_k = log(1.546) + (σ_k - 1/2)log|π|`.

### Dependencies
**Depends on:** none.
**Used by:** `c3mNeg1`, `c3F`, `logPi_bounds`, `mCoeffPP_of_le_neg_two`. -/
noncomputable def logPi : ℝ := Real.log Real.pi

/-- **`m_0 = (14/3)(L - L₀)`**, the slope of the `k = 0` chord (`mCoeffPP 0`, see
`mCoeffPP_zero_eq`).

### Summary of Proof
`(v''_0 - v''_1)/(σ_0 - σ_1) = (L₀ - L)/(1/2 - 5/7)`.  Numerically `4.33220`.

### Dependencies
**Depends on:** `c3L`, `c3L0`.
**Used by:** `c3b0`, `c3mNeg1`, `c3G1`, `c3G0`, `c3F`, `c3m0_bounds`. -/
noncomputable def c3m0 : ℝ := 14 / 3 * (c3L - c3L0)

/-- **`b_0 = L₀ - m_0/2`**, the intercept of the `k = 0` chord (`bCoeffPP 0`).

### Summary of Proof
`v''_0 - m_0 σ_0`.

### Dependencies
**Depends on:** `c3L0`, `c3m0`.
**Used by:** `c3G1`, `c3G0`, `c3F`. -/
noncomputable def c3b0 : ℝ := c3L0 - c3m0 / 2

/-- **`m_{-1} = log π - m_0`**, the slope of the `k = -1` chord (`mCoeffPP (-1)`).

### Summary of Proof
`(v''_{-1} - v''_0)/(σ_{-1} - σ_0) = (L - (3/14) log π - L₀)/(-3/14) = log π - m_0`.  Numerically
`-3.18747`.

### Dependencies
**Depends on:** `logPi`, `c3m0`.
**Used by:** `c3bNeg1`, `c3G0`, `c3F`. -/
noncomputable def c3mNeg1 : ℝ := logPi - c3m0

/-- **`b_{-1} = L₀ - m_{-1}/2`**, the intercept of the `k = -1` chord (`bCoeffPP (-1)`).

### Summary of Proof
`v''_{-1} - m_{-1} σ_{-1}`, rewritten through the common value `L₀` at `σ_0 = 1/2`.

### Dependencies
**Depends on:** `c3L0`, `c3mNeg1`.
**Used by:** `c3G0`, `c3F`. -/
noncomputable def c3bNeg1 : ℝ := c3L0 - c3mNeg1 / 2

/-- **`1.09861 ≤ log 3 ≤ 1.09862`.**

### Summary of Proof
`log 3 = log 2 + log (3/2)`, `Real.log_two_gt_d9`/`lt_d9`, and `Real.abs_log_sub_add_sum_range_le`
at `x = -1/2` with `20` terms (error `2⁻²⁰`).

### References
Mathlib: `Real.abs_log_sub_add_sum_range_le`.

### Dependencies
**Depends on:** none.
**Used by:** `logPi_bounds`. -/
theorem log_three_two_sided : (1.09861 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.09862 := by
  have habs : |(-(1 / 2) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 20
  rw [abs_le] at h
  have hx : (1 : ℝ) - -(1 / 2) = 3 / 2 := by norm_num
  rw [hx] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  rw [hsplit]
  constructor <;> linarith [h.1, h.2]

/-- **`0.435669 ≤ log 1.546 ≤ 0.435672`.**

### Summary of Proof
`log 1.546 = log 2 + log (773/1000)` and `Real.abs_log_sub_add_sum_range_le` at `x = 227/1000` with
`9` terms (error `0.227¹⁰/0.773 = 4.7·10⁻⁷`).  True value `0.4356709…`.

### Dependencies
**Depends on:** `c3L`.
**Used by:** `c3F_one_ge`, `c3G0_r1_ge`, `c3m0_bounds`. -/
theorem c3L_bounds : (0.435669 : ℝ) ≤ c3L ∧ c3L ≤ 0.435672 := by
  have habs : |(227 / 1000 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 9
  rw [abs_le] at h
  have hx : (1 : ℝ) - 227 / 1000 = 773 / 1000 := by norm_num
  rw [hx] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : c3L = Real.log 2 + Real.log (773 / 1000) := by
    unfold c3L
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  rw [hsplit]
  constructor <;> linarith [h.1, h.2]

/-- **`-0.49266 ≤ log 0.611 ≤ -0.492657`.**

### Summary of Proof
`Real.abs_log_sub_add_sum_range_le` at `x = 389/1000` with `16` terms (error
`0.389¹⁷/0.611 = 1.8·10⁻⁷`).  True value `-0.4926583…`.

### Dependencies
**Depends on:** `c3L0`.
**Used by:** `c3m0_bounds`, `c3G0_r1_ge`, `c3F_one_ge`. -/
theorem c3L0_bounds : (-0.49266 : ℝ) ≤ c3L0 ∧ c3L0 ≤ -0.492657 := by
  have habs : |(389 / 1000 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 16
  rw [abs_le] at h
  have hx : (1 : ℝ) - 389 / 1000 = 611 / 1000 := by norm_num
  rw [hx] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : c3L0 = Real.log (611 / 1000) := by
    unfold c3L0; norm_num
  rw [hsplit]
  constructor <;> linarith [h.1, h.2]

/-- **`1.14472 ≤ log π ≤ 1.14474`.**

### Summary of Proof
`Real.pi_gt_d6`/`pi_lt_d6` bracket `π` between `3.141592` and `3.141593`; `log` is monotone; each
endpoint is `log 3 + log (1 + x)` with `|x| < 0.0472`, handled by `log_three_two_sided` and
`Real.abs_log_sub_add_sum_range_le` with `6` terms.  True value `1.1447299…`.

### Dependencies
**Depends on:** `logPi`, `log_three_two_sided`.
**Used by:** `c3B_pos`, `c3F''_nonpos`, `c3F_one_ge`, `c3G0''_nonneg`, `c3G0'_r1_bounds`,
`c3G0_r1_ge`. -/
theorem logPi_bounds : (1.14472 : ℝ) ≤ logPi ∧ logPi ≤ 1.14474 := by
  have hpi1 : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6; norm_num at h ⊢; linarith
  have hpi2 : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6; norm_num at h ⊢; linarith
  have hl1 : Real.log (392699 / 125000) ≤ logPi := Real.log_le_log (by norm_num) hpi1
  have hl2 : logPi ≤ Real.log (3141593 / 1000000) := Real.log_le_log Real.pi_pos hpi2
  have habs1 : |(-(141592 / 3000000) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h1 := Real.abs_log_sub_add_sum_range_le habs1 6
  rw [abs_le] at h1
  have hx1 : (1 : ℝ) - -(141592 / 3000000) = 392699 / 375000 := by norm_num
  rw [hx1] at h1
  norm_num [Finset.sum_range_succ] at h1
  have habs2 : |(-(141593 / 3000000) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h2 := Real.abs_log_sub_add_sum_range_le habs2 6
  rw [abs_le] at h2
  have hx2 : (1 : ℝ) - -(141593 / 3000000) = 3141593 / 3000000 := by norm_num
  rw [hx2] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hs1 : Real.log (392699 / 125000) = Real.log 3 + Real.log (392699 / 375000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.log (3141593 / 1000000) = Real.log 3 + Real.log (3141593 / 3000000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h3 := log_three_two_sided
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **`4.33218 ≤ m_0 ≤ 4.33222`.**

### Summary of Proof
`m_0 = (14/3)(L - L₀)` with `c3L_bounds`, `c3L0_bounds`.

### Dependencies
**Depends on:** `c3m0`, `c3L_bounds`, `c3L0_bounds`.
**Used by:** `c3m0_pos`, `c3B_pos`, `c3G0''_nonneg`, `c3F''_nonpos`, `c3G0_r1_ge`,
`c3G0'_r1_bounds`, `c3F_one_ge`. -/
theorem c3m0_bounds : (4.33218 : ℝ) ≤ c3m0 ∧ c3m0 ≤ 4.33222 := by
  have := c3L_bounds; have := c3L0_bounds
  unfold c3m0; constructor <;> linarith

/-- **`0 < m_0`.**

### Summary of Proof
From `c3m0_bounds`.

### Dependencies
**Depends on:** `c3m0_bounds`.
**Used by:** `c3G1'_nonpos`, `c3G0''_nonneg`, `c3F''_nonpos`. -/
theorem c3m0_pos : 0 < c3m0 := by linarith [c3m0_bounds.1]

/-- **`0 < m_0 - m_{-1} = 2 m_0 - log π`**, the slope jump at `σ_0 = 1/2`.

### Summary of Proof
From `c3m0_bounds` and `logPi_bounds`.

### Dependencies
**Depends on:** `c3mNeg1`, `c3m0_bounds`, `logPi_bounds`.
**Used by:** `c3G0''_nonneg`, `c3F''_nonpos`. -/
theorem c3B_pos : 0 < c3m0 - c3mNeg1 := by
  unfold c3mNeg1; linarith [c3m0_bounds.1, logPi_bounds.2]

/-- **`θ_a(r) = arcsin (a/r)`**, the angle at which the arc `1 - r sin φ` meets the line `1 - a`.

### Summary of Proof
Definition; `theta k r = arcA (1 - sigma k) r` definitionally (`theta_eq_arcA`).

### Dependencies
**Depends on:** none.
**Used by:** `chordBlock`, `hasDerivAt_arcA`, `continuousOn_arcA`, `theta_eq_arcA`. -/
noncomputable def arcA (a r : ℝ) : ℝ := Real.arcsin (a / r)

/-- **`u_a(r) = √(r² - a²) = r cos θ_a(r)`.**

### Summary of Proof
Definition; the identity with `r cos θ_a(r)` is `cos_theta_eq_rootA`.

### Dependencies
**Depends on:** none.
**Used by:** `chordBlock`, `ratioA`, `hasDerivAt_rootA`, `rootA_pos`, `rootA_sq`, `rootA_anti`. -/
noncomputable def rootA (a r : ℝ) : ℝ := Real.sqrt (r ^ 2 - a ^ 2)

/-- **`cos θ_a(r) = u_a(r)/r`**, the quantity that appears in every first derivative below.

### Summary of Proof
Definition.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `c3G1'`, `c3G0'`, `c3F'`, `hasDerivAt_ratioA`, `ratioA_eq`. -/
noncomputable def ratioA (a r : ℝ) : ℝ := rootA a r / r

/-- **One chord's contribution** `(m + b) θ_a(r) + m u_a(r)` to the arc integral: since
`u_a(r) = r cos θ_a(r)`, this is the primitive `θ ↦ (m + b) θ + m r cos θ` of the chord integrand
`m (1 - r sin θ) + b`, evaluated at `θ = θ_a(r)`.

### Summary of Proof
Definition.  `c3G1`, `c3G0`, `c3F` are signed sums of blocks, one per chord crossed, obtained by
evaluating `∫_0^{π/2} A''(1 - r sin θ) dθ` piecewise.

### Dependencies
**Depends on:** `arcA`, `rootA`.
**Used by:** `c3G1`, `c3G0`, `c3F`, `hasDerivAt_chordBlock`, `continuousOn_chordBlock`. -/
noncomputable def chordBlock (m b a r : ℝ) : ℝ := (m + b) * arcA a r + m * rootA a r

/-- **`0 < u_a(r)` for `0 ≤ a < r`.**

### Summary of Proof
`Real.sqrt_pos` and `r² - a² > 0`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** the derivative lemmas below. -/
theorem rootA_pos {a r : ℝ} (ha : 0 ≤ a) (har : a < r) : 0 < rootA a r := by
  unfold rootA; apply Real.sqrt_pos.mpr; nlinarith

/-- **`0 ≤ u_a(r)`.**

### Summary of Proof
`Real.sqrt_nonneg`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `c3G1'_nonpos`. -/
theorem rootA_nonneg (a r : ℝ) : 0 ≤ rootA a r := Real.sqrt_nonneg _

/-- **`u_a(r)² = r² - a²` for `0 ≤ a ≤ r`.**

### Summary of Proof
`Real.sq_sqrt`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `ratioA_eq`, `hasDerivAt_ratioA`. -/
theorem rootA_sq {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) : rootA a r ^ 2 = r ^ 2 - a ^ 2 := by
  unfold rootA; rw [Real.sq_sqrt]; nlinarith

/-- **`u_a` is antitone in `a` on `[0, ∞)`**: `a ≤ a'` gives `u_{a'}(r) ≤ u_a(r)`.

### Summary of Proof
`Real.sqrt_le_sqrt` and `a² ≤ a'²`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `c3G0''_nonneg`, `c3F''_nonpos`. -/
theorem rootA_anti {a a' r : ℝ} (h : a ≤ a') (ha : 0 ≤ a) : rootA a' r ≤ rootA a r := by
  unfold rootA; apply Real.sqrt_le_sqrt; nlinarith

/-- **`d/dr arcsin (a/r) = -a/(r u_a(r))`** for `0 < a < r`.

### Summary of Proof
Chain rule: `Real.hasDerivAt_arcsin` at `a/r ∈ (0,1)` composed with `d/dr (a/r) = -a/r²`; then
`√(1 - a²/r²) = u_a(r)/r` (`Real.sqrt_div'`, `Real.sqrt_sq`).

### Dependencies
**Depends on:** `arcA`, `rootA_pos`.
**Used by:** `hasDerivAt_chordBlock`. -/
theorem hasDerivAt_arcA {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HasDerivAt (fun r => arcA a r) (-a / (r * rootA a r)) r := by
  have hr : 0 < r := ha.trans har
  have hu := rootA_pos ha.le har
  have h1 : HasDerivAt (fun r : ℝ => a / r) (a * -(r ^ 2)⁻¹) r := by
    simpa only [div_eq_mul_inv] using (hasDerivAt_inv hr.ne').const_mul a
  have hlt : a / r < 1 := by rw [div_lt_one hr]; exact har
  have hgt : -1 < a / r := by have : 0 < a / r := div_pos ha hr; linarith
  have hderiv : HasDerivAt (fun r => arcA a r)
      (1 / Real.sqrt (1 - (a / r) ^ 2) * (a * -(r ^ 2)⁻¹)) r :=
    (Real.hasDerivAt_arcsin hgt.ne' hlt.ne).comp r h1
  refine hderiv.congr_deriv ?_
  have hsq : Real.sqrt (1 - (a / r) ^ 2) = rootA a r / r := by
    rw [show (1 : ℝ) - (a / r) ^ 2 = (r ^ 2 - a ^ 2) / r ^ 2 by field_simp,
      Real.sqrt_div' _ (sq_nonneg r), Real.sqrt_sq hr.le]
    rfl
  rw [hsq]
  field_simp

/-- **`d/dr √(r² - a²) = r/u_a(r)`** for `0 ≤ a < r`.

### Summary of Proof
`HasDerivAt.sqrt` applied to `r² - a²`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `hasDerivAt_chordBlock`, `hasDerivAt_ratioA`. -/
theorem hasDerivAt_rootA {a r : ℝ} (ha : 0 ≤ a) (har : a < r) :
    HasDerivAt (fun r => rootA a r) (r / rootA a r) r := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 - a ^ 2) (2 * r) r := by
    have := (hasDerivAt_pow 2 r).sub_const (a ^ 2)
    simpa using this
  have := h1.sqrt hpos.ne'
  refine this.congr_deriv ?_
  unfold rootA
  have hu : 0 < Real.sqrt (r ^ 2 - a ^ 2) := Real.sqrt_pos.mpr hpos
  field_simp

/-- **Derivative of a chord block**: `d/dr [(m+b) θ_a + m u_a] = (m r² - (m+b) a)/(r u_a)`.

### Summary of Proof
`hasDerivAt_arcA` and `hasDerivAt_rootA`, then `field_simp; ring`.

### Lean Notes
When two blocks with the same `a` and chords agreeing at `σ = 1 - a` are subtracted, the
`(m+b) a` terms combine to `(m - m') a²` and the difference of derivatives is
`(m - m') u_a/r = (m - m') cos θ_a`.  That is how `c3G1'`, `c3G0'`, `c3F'` arise.

### Dependencies
**Depends on:** `hasDerivAt_arcA`, `hasDerivAt_rootA`, `rootA_pos`.
**Used by:** `hasDerivAt_c3G1`, `hasDerivAt_c3G0`, `hasDerivAt_c3F`. -/
theorem hasDerivAt_chordBlock {m b a r : ℝ} (ha : 0 < a) (har : a < r) :
    HasDerivAt (fun r => chordBlock m b a r) ((m * r ^ 2 - (m + b) * a) / (r * rootA a r)) r := by
  have h := ((hasDerivAt_arcA ha har).const_mul (m + b)).add
    ((hasDerivAt_rootA ha.le har).const_mul m)
  have hr : 0 < r := ha.trans har
  have hu := rootA_pos ha.le har
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **`cos θ_a(r) = (r² - a²)/(r u_a(r))`**, the form in which the first derivatives are matched.

### Summary of Proof
`u_a/r = u_a²/(r u_a)` and `rootA_sq`.

### Dependencies
**Depends on:** `ratioA`, `rootA_sq`, `rootA_pos`.
**Used by:** `hasDerivAt_c3G1`, `hasDerivAt_c3G0`, `hasDerivAt_c3F`. -/
theorem ratioA_eq {a r : ℝ} (ha : 0 ≤ a) (har : a < r) :
    ratioA a r = (r ^ 2 - a ^ 2) / (r * rootA a r) := by
  have hu := rootA_pos ha har
  have hr : 0 < r := lt_of_le_of_lt ha har
  unfold ratioA
  rw [← rootA_sq ha har.le]
  field_simp

/-- **`d/dr cos θ_a(r) = a²/(r² u_a(r))`** for `0 < a < r`.

### Summary of Proof
Quotient rule on `u_a(r)/r` with `hasDerivAt_rootA`, then `u_a² = r² - a²`.

### Dependencies
**Depends on:** `ratioA`, `hasDerivAt_rootA`, `rootA_sq`.
**Used by:** `hasDerivAt_c3G0'`, `hasDerivAt_c3F'`. -/
theorem hasDerivAt_ratioA {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HasDerivAt (fun r => ratioA a r) (a ^ 2 / (r ^ 2 * rootA a r)) r := by
  have hr : 0 < r := ha.trans har
  have hu := rootA_pos ha.le har
  have h := (hasDerivAt_rootA ha.le har).div (hasDerivAt_id r) hr.ne'
  refine h.congr_deriv ?_
  have hsq := rootA_sq ha.le har.le
  have ha2 : a ^ 2 = r ^ 2 - rootA a r ^ 2 := by linarith
  rw [ha2]
  simp only [id]
  field_simp

/-- **`arcA a` is continuous away from `r = 0`.**

### Summary of Proof
`Real.continuous_arcsin` composed with `r ↦ a/r`.

### Dependencies
**Depends on:** `arcA`.
**Used by:** `continuousOn_chordBlock`. -/
theorem continuousOn_arcA (a : ℝ) {s : Set ℝ} (hs : ∀ r ∈ s, r ≠ 0) :
    ContinuousOn (fun r => arcA a r) s := by
  apply Real.continuous_arcsin.comp_continuousOn
  exact continuousOn_const.div continuousOn_id hs

/-- **`rootA a` is continuous.**

### Summary of Proof
`fun_prop`.

### Dependencies
**Depends on:** `rootA`.
**Used by:** `continuousOn_chordBlock`. -/
theorem continuous_rootA (a : ℝ) : Continuous (fun r => rootA a r) := by
  unfold rootA; fun_prop

/-- **A chord block is continuous away from `r = 0`.**

### Summary of Proof
`continuousOn_arcA`, `continuous_rootA`.

### Dependencies
**Depends on:** `chordBlock`, `continuousOn_arcA`, `continuous_rootA`.
**Used by:** `continuousOn_c3G1`, `continuousOn_c3G0`, `continuousOn_c3F`. -/
theorem continuousOn_chordBlock (m b a : ℝ) {s : Set ℝ} (hs : ∀ r ∈ s, r ≠ 0) :
    ContinuousOn (fun r => chordBlock m b a r) s := by
  unfold chordBlock
  exact (continuousOn_const.mul (continuousOn_arcA a hs)).add
    (continuousOn_const.mul (continuous_rootA a).continuousOn)

/-- **Tangent-line lower bound for a function with monotone derivative**: if `f'` is monotone on
`(a, b)` then `f x ≥ f x₀ + f' x₀ (x - x₀)` for `x₀ ∈ (a, b)`, `x ∈ [a, b]`.

### Summary of Proof
Mean value theorem (`exists_hasDerivAt_eq_slope`) on `[x, x₀]` or `[x₀, x]`: the slope is `f' ξ`
with `ξ` between `x` and `x₀`, and monotonicity compares `f' ξ` with `f' x₀` in the right
direction on either side.

### Lean Notes
Stated with `HasDerivAt` hypotheses rather than `ConvexOn`, so that no `deriv` bookkeeping is
needed; `f'` need only be monotone on the *open* interval.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0_lower`. -/
theorem tangent_le_of_monotone_deriv {f f' : ℝ → ℝ} {a b x₀ x : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hmono : MonotoneOn f' (Set.Ioo a b))
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx : x ∈ Set.Icc a b) :
    f x₀ + f' x₀ * (x - x₀) ≤ f x := by
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (hcont.mono (Set.Icc_subset_Icc hx.1 hx₀.2.le))
      (fun y hy => hderiv y ⟨lt_of_le_of_lt hx.1 hy.1, hy.2.trans hx₀.2⟩)
    have hle : f' ξ ≤ f' x₀ := hmono ⟨lt_of_le_of_lt hx.1 hξ.1, hξ.2.trans hx₀.2⟩ hx₀ hξ.2.le
    have hpos : 0 < x₀ - x := by linarith
    have heq : f x₀ - f x = f' ξ * (x₀ - x) := by rw [hξ', div_mul_cancel₀ _ hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_right hle hpos.le]
  · subst heq; simp
  · obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (hcont.mono (Set.Icc_subset_Icc hx₀.1.le hx.2))
      (fun y hy => hderiv y ⟨hx₀.1.trans hy.1, lt_of_lt_of_le hy.2 hx.2⟩)
    have hle : f' x₀ ≤ f' ξ := hmono hx₀ ⟨hx₀.1.trans hξ.1, lt_of_lt_of_le hξ.2 hx.2⟩ hξ.1.le
    have hpos : 0 < x - x₀ := by linarith
    have heq : f x - f x₀ = f' ξ * (x - x₀) := by rw [hξ', div_mul_cancel₀ _ hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_right hle hpos.le]

/-- **A function with antitone derivative is at least the smaller endpoint value**:
`min (f a) (f b) ≤ f x` on `[a, b]`.

### Summary of Proof
Two mean value theorems, on `[a, x]` and `[x, b]`, give slopes `f' ξ ≥ f' η`; if `f' ξ ≥ 0` then
`f x ≥ f a`, otherwise `f' η < 0` and `f x > f b`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `c3F_lower`. -/
theorem min_le_of_antitone_deriv {f f' : ℝ → ℝ} {a b x : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hanti : AntitoneOn f' (Set.Ioo a b))
    (hx : x ∈ Set.Icc a b) : min (f a) (f b) ≤ f x := by
  rcases eq_or_lt_of_le hx.1 with h1 | h1
  · rw [← h1]; exact min_le_left _ _
  rcases eq_or_lt_of_le hx.2 with h2 | h2
  · rw [h2]; exact min_le_right _ _
  obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' h1
    (hcont.mono (Set.Icc_subset_Icc le_rfl hx.2)) (fun y hy => hderiv y ⟨hy.1, hy.2.trans h2⟩)
  obtain ⟨η, hη, hη'⟩ := exists_hasDerivAt_eq_slope f f' h2
    (hcont.mono (Set.Icc_subset_Icc hx.1 le_rfl)) (fun y hy => hderiv y ⟨h1.trans hy.1, hy.2⟩)
  have hle : f' η ≤ f' ξ :=
    hanti ⟨hξ.1, hξ.2.trans h2⟩ ⟨h1.trans hη.1, hη.2⟩ (hξ.2.trans hη.1).le
  have e1 : f x - f a = f' ξ * (x - a) := by rw [hξ', div_mul_cancel₀ _ (by linarith)]
  have e2 : f b - f x = f' η * (b - x) := by rw [hη', div_mul_cancel₀ _ (by linarith)]
  rcases le_or_gt 0 (f' ξ) with h | h
  · refine (min_le_left _ _).trans ?_; nlinarith
  · refine (min_le_right _ _).trans ?_; nlinarith

/-- **A function with nonpositive derivative is at least its right endpoint value.**

### Summary of Proof
Mean value theorem on `[x, b]`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `c3G1_lower`. -/
theorem right_le_of_nonpos_deriv {f f' : ℝ → ℝ} {a b x : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hneg : ∀ y ∈ Set.Ioo a b, f' y ≤ 0)
    (hx : x ∈ Set.Icc a b) : f b ≤ f x := by
  rcases eq_or_lt_of_le hx.2 with h2 | h2
  · rw [h2]
  obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f f' h2
    (hcont.mono (Set.Icc_subset_Icc hx.1 le_rfl))
    (fun y hy => hderiv y ⟨lt_of_le_of_lt hx.1 hy.1, hy.2⟩)
  have e : f b - f x = f' ξ * (b - x) := by rw [hξ', div_mul_cancel₀ _ (by linarith)]
  have := hneg ξ ⟨lt_of_le_of_lt hx.1 hξ.1, hξ.2⟩
  nlinarith

/-- **Monotone on an open interval from a nonnegative derivative** (`HasDerivAt` form).

### Summary of Proof
Mathlib's `monotoneOn_of_hasDerivWithinAt_nonneg` on `D = Ioo a b`, whose interior is itself.

### References
Mathlib: `monotoneOn_of_hasDerivWithinAt_nonneg`.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0_lower`. -/
theorem monotoneOn_Ioo_of_hasDerivAt {g g' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt g (g' y) y)
    (hnn : ∀ y ∈ Set.Ioo a b, 0 ≤ g' y) : MonotoneOn g (Set.Ioo a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b)
  · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun y hy => (hderiv y hy).hasDerivWithinAt
  · rw [interior_Ioo]; exact hnn

/-- **Antitone on an open interval from a nonpositive derivative** (`HasDerivAt` form).

### Summary of Proof
Mathlib's `antitoneOn_of_hasDerivWithinAt_nonpos` on `D = Ioo a b`.

### References
Mathlib: `antitoneOn_of_hasDerivWithinAt_nonpos`.

### Dependencies
**Depends on:** none.
**Used by:** `c3F_lower`. -/
theorem antitoneOn_Ioo_of_hasDerivAt {g g' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt g (g' y) y)
    (hnp : ∀ y ∈ Set.Ioo a b, g' y ≤ 0) : AntitoneOn g (Set.Ioo a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo a b)
  · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun y hy => (hderiv y hy).hasDerivWithinAt
  · rw [interior_Ioo]; exact hnp

/-- **`c_{3,r}` for `2/7 ≤ r ≤ 1/2` (`Kidx r = 1`)**:
`(m_0 + b_0)(π/2 - θ_{2/7}) - m_0 u_{2/7} + L θ_{2/7}`.

### Summary of Proof
Definition; equals `c3 r` on the regime by `c3_eq_c3G1`.  The `k = 0` chord covers
`φ ∈ [θ_{2/7}, π/2]` and the constant `L` covers `[0, θ_{2/7}]`.

### Dependencies
**Depends on:** `chordBlock`, `c3m0`, `c3b0`, `c3L`.
**Used by:** `c3_eq_c3G1`, `hasDerivAt_c3G1`, `c3G1_lower`. -/
noncomputable def c3G1 (r : ℝ) : ℝ :=
  (c3m0 + c3b0) * (Real.pi / 2) - chordBlock c3m0 c3b0 (2 / 7) r + chordBlock 0 c3L (2 / 7) r

/-- **`c_{3,r}` for `1/2 ≤ r ≤ 5/7` (`Kidx r = 0`)**: the `k = -1` chord on `[θ_{1/2}, π/2]`, the
`k = 0` chord on `[θ_{2/7}, θ_{1/2}]`, and `L` on `[0, θ_{2/7}]`.

### Summary of Proof
Definition; equals `c3 r` on the regime by `c3_eq_c3G0`.  This is the regime containing the
global minimum `0.016499` at `r = 0.57762`.

### Dependencies
**Depends on:** `chordBlock`, `c3m0`, `c3b0`, `c3mNeg1`, `c3bNeg1`, `c3L`.
**Used by:** `c3_eq_c3G0`, `hasDerivAt_c3G0`, `c3G0_lower`, `c3G1_half_eq`, `c3F_57_eq`. -/
noncomputable def c3G0 (r : ℝ) : ℝ :=
  (c3mNeg1 + c3bNeg1) * (Real.pi / 2) - chordBlock c3mNeg1 c3bNeg1 (1 / 2) r
    + chordBlock c3m0 c3b0 (1 / 2) r - chordBlock c3m0 c3b0 (2 / 7) r + chordBlock 0 c3L (2 / 7) r

/-- **`c_{3,r}` for `5/7 ≤ r ≤ 1` (`Kidx r ≤ -1`)**: the linear chord `log π · σ + (L - log π/2)`
on `[θ_{5/7}, π/2]`, then the `k = -1`, `k = 0` chords and `L` as in `c3G0`.

### Summary of Proof
Definition; equals `c3 r` on the regime by `c3_eq_c3F`, uniformly in `Kidx r ≤ -1`, because all
chords with `k ≤ -2` are the same line and their blocks telescope.

### Dependencies
**Depends on:** `chordBlock`, `logPi`, `c3L`, `c3m0`, `c3b0`, `c3mNeg1`, `c3bNeg1`.
**Used by:** `c3_eq_c3F`, `hasDerivAt_c3F`, `c3F_lower`, `c3F_57_eq`, `c3F_one_eq`. -/
noncomputable def c3F (r : ℝ) : ℝ :=
  (logPi + (c3L - logPi / 2)) * (Real.pi / 2) - chordBlock logPi (c3L - logPi / 2) (5 / 7) r
    + chordBlock c3mNeg1 c3bNeg1 (5 / 7) r - chordBlock c3mNeg1 c3bNeg1 (1 / 2) r
    + chordBlock c3m0 c3b0 (1 / 2) r - chordBlock c3m0 c3b0 (2 / 7) r + chordBlock 0 c3L (2 / 7) r

/-- **`c3G1' r = -m_0 cos θ_{2/7}(r)`.**

### Summary of Proof
Definition of the derivative; `hasDerivAt_c3G1` proves it is one.

### Dependencies
**Depends on:** `ratioA`, `c3m0`.
**Used by:** `c3G1'_nonpos`, `c3G1_lower`, `hasDerivAt_c3G1`. -/
noncomputable def c3G1' (r : ℝ) : ℝ := -c3m0 * ratioA (2 / 7) r

/-- **`c3G0' r = (m_0 - m_{-1}) cos θ_{1/2}(r) - m_0 cos θ_{2/7}(r)`.**

### Summary of Proof
Definition; `hasDerivAt_c3G0`.  It vanishes at `r* = 0.57762`, the minimiser of `c_3`.

### Dependencies
**Depends on:** `ratioA`, `c3m0`, `c3mNeg1`.
**Used by:** `hasDerivAt_c3G0`, `hasDerivAt_c3G0'`, `c3G0'_r1_bounds`, `c3G0_lower`. -/
noncomputable def c3G0' (r : ℝ) : ℝ := (c3m0 - c3mNeg1) * ratioA (1 / 2) r - c3m0 * ratioA (2 / 7) r

/-- **`c3F' r = -m_0 cos θ_{5/7}(r) + (m_0 - m_{-1}) cos θ_{1/2}(r) - m_0 cos θ_{2/7}(r)`.**

### Summary of Proof
Definition; `hasDerivAt_c3F`.  The first coefficient is `m_{-1} - log π = -m_0`.

### Dependencies
**Depends on:** `ratioA`, `c3m0`, `c3mNeg1`.
**Used by:** `hasDerivAt_c3F`, `hasDerivAt_c3F'`, `c3F_lower`. -/
noncomputable def c3F' (r : ℝ) : ℝ :=
  -c3m0 * ratioA (5 / 7) r + (c3m0 - c3mNeg1) * ratioA (1 / 2) r - c3m0 * ratioA (2 / 7) r

/-- **`c3G0'' r = (m_0 - m_{-1}) (1/2)²/(r² u_{1/2}) - m_0 (2/7)²/(r² u_{2/7})`.**

### Summary of Proof
Definition; `hasDerivAt_c3G0'`, and `c3G0''_nonneg` gives the convexity of `c3G0`.

### Dependencies
**Depends on:** `rootA`, `c3m0`, `c3mNeg1`.
**Used by:** `c3G0''_nonneg`, `c3G0_lower`, `hasDerivAt_c3G0'`. -/
noncomputable def c3G0'' (r : ℝ) : ℝ :=
  (c3m0 - c3mNeg1) * ((1 / 2) ^ 2 / (r ^ 2 * rootA (1 / 2) r))
    - c3m0 * ((2 / 7) ^ 2 / (r ^ 2 * rootA (2 / 7) r))

/-- **`c3F'' r`**, the derivative of `c3F'`; `c3F''_nonpos` gives the concavity of `c3F`.

### Summary of Proof
Definition; `hasDerivAt_c3F'`.

### Dependencies
**Depends on:** `rootA`, `c3m0`, `c3mNeg1`.
**Used by:** `c3F''_nonpos`, `c3F_lower`, `hasDerivAt_c3F'`. -/
noncomputable def c3F'' (r : ℝ) : ℝ :=
  -c3m0 * ((5 / 7) ^ 2 / (r ^ 2 * rootA (5 / 7) r))
    + (c3m0 - c3mNeg1) * ((1 / 2) ^ 2 / (r ^ 2 * rootA (1 / 2) r))
    - c3m0 * ((2 / 7) ^ 2 / (r ^ 2 * rootA (2 / 7) r))

/-- **`c3G1` has derivative `c3G1'` for `r > 2/7`.**

### Summary of Proof
`hasDerivAt_chordBlock` twice; the two `a = 2/7` blocks combine because the `k = 0` chord takes the
value `L` at `σ_1 = 5/7`, i.e. `(5/7) m_0 + b_0 = L`, which is a ring identity once `c3m0`, `c3b0`
are unfolded.

### Dependencies
**Depends on:** `c3G1`, `c3G1'`, `hasDerivAt_chordBlock`, `ratioA_eq`.
**Used by:** `c3G1_lower`. -/
theorem hasDerivAt_c3G1 {y : ℝ} (hy : 2 / 7 < y) : HasDerivAt c3G1 (c3G1' y) y := by
  have h1 := hasDerivAt_chordBlock (m := c3m0) (b := c3b0) (a := 2 / 7) (r := y) (by norm_num) hy
  have h2 := hasDerivAt_chordBlock (m := 0) (b := c3L) (a := 2 / 7) (r := y) (by norm_num) hy
  have h := ((hasDerivAt_const y ((c3m0 + c3b0) * (Real.pi / 2))).sub h1).add h2
  refine h.congr_deriv ?_
  have hu := rootA_pos (a := 2 / 7) (r := y) (by norm_num) hy
  have hy0 : 0 < y := by linarith
  rw [c3G1', ratioA_eq (by norm_num) hy]
  unfold c3b0 c3m0
  field_simp
  ring

/-- **`c3G0` has derivative `c3G0'` for `r > 1/2`.**

### Summary of Proof
`hasDerivAt_chordBlock` four times; the blocks at `a = 1/2` combine through the common value `L₀`
of the `k = -1` and `k = 0` chords at `σ_0`, those at `a = 2/7` as in `hasDerivAt_c3G1`.

### Dependencies
**Depends on:** `c3G0`, `c3G0'`, `hasDerivAt_chordBlock`, `ratioA_eq`.
**Used by:** `c3G0_lower`. -/
theorem hasDerivAt_c3G0 {y : ℝ} (hy : 1 / 2 < y) : HasDerivAt c3G0 (c3G0' y) y := by
  have hy' : 2 / 7 < y := by linarith
  have h1 := hasDerivAt_chordBlock (m := c3mNeg1) (b := c3bNeg1) (a := 1 / 2) (r := y)
    (by norm_num) hy
  have h2 := hasDerivAt_chordBlock (m := c3m0) (b := c3b0) (a := 1 / 2) (r := y) (by norm_num) hy
  have h3 := hasDerivAt_chordBlock (m := c3m0) (b := c3b0) (a := 2 / 7) (r := y) (by norm_num) hy'
  have h4 := hasDerivAt_chordBlock (m := 0) (b := c3L) (a := 2 / 7) (r := y) (by norm_num) hy'
  have h := ((((hasDerivAt_const y ((c3mNeg1 + c3bNeg1) * (Real.pi / 2))).sub h1).add h2).sub
    h3).add h4
  refine h.congr_deriv ?_
  have hu0 := rootA_pos (a := 1 / 2) (r := y) (by norm_num) hy
  have hu1 := rootA_pos (a := 2 / 7) (r := y) (by norm_num) hy'
  have hy0 : 0 < y := by linarith
  rw [c3G0', ratioA_eq (by norm_num) hy, ratioA_eq (by norm_num) hy']
  unfold c3bNeg1 c3mNeg1 c3b0 c3m0
  field_simp
  ring

/-- **`c3F` has derivative `c3F'` for `r > 5/7`.**

### Summary of Proof
`hasDerivAt_chordBlock` six times; the two `a = 5/7` blocks combine through the common value
`v''_{-1} = L - (3/14) log π` of the linear chord and the `k = -1` chord at `σ_{-1} = 2/7`.

### Dependencies
**Depends on:** `c3F`, `c3F'`, `hasDerivAt_chordBlock`, `ratioA_eq`.
**Used by:** `c3F_lower`. -/
theorem hasDerivAt_c3F {y : ℝ} (hy : 5 / 7 < y) : HasDerivAt c3F (c3F' y) y := by
  have hy' : 1 / 2 < y := by linarith
  have hy'' : 2 / 7 < y := by linarith
  have h0 := hasDerivAt_chordBlock (m := logPi) (b := c3L - logPi / 2) (a := 5 / 7) (r := y)
    (by norm_num) hy
  have h1 := hasDerivAt_chordBlock (m := c3mNeg1) (b := c3bNeg1) (a := 5 / 7) (r := y)
    (by norm_num) hy
  have h2 := hasDerivAt_chordBlock (m := c3mNeg1) (b := c3bNeg1) (a := 1 / 2) (r := y)
    (by norm_num) hy'
  have h3 := hasDerivAt_chordBlock (m := c3m0) (b := c3b0) (a := 1 / 2) (r := y) (by norm_num) hy'
  have h4 := hasDerivAt_chordBlock (m := c3m0) (b := c3b0) (a := 2 / 7) (r := y) (by norm_num) hy''
  have h5 := hasDerivAt_chordBlock (m := 0) (b := c3L) (a := 2 / 7) (r := y) (by norm_num) hy''
  have h := ((((((hasDerivAt_const y ((logPi + (c3L - logPi / 2)) * (Real.pi / 2))).sub h0).add
    h1).sub h2).add h3).sub h4).add h5
  refine h.congr_deriv ?_
  have hum := rootA_pos (a := 5 / 7) (r := y) (by norm_num) hy
  have hu0 := rootA_pos (a := 1 / 2) (r := y) (by norm_num) hy'
  have hu1 := rootA_pos (a := 2 / 7) (r := y) (by norm_num) hy''
  have hy0 : 0 < y := by linarith
  rw [c3F', ratioA_eq (by norm_num) hy, ratioA_eq (by norm_num) hy', ratioA_eq (by norm_num) hy'']
  unfold c3bNeg1 c3mNeg1 c3b0 c3m0
  field_simp
  ring

/-- **`c3G0'` has derivative `c3G0''` for `r > 1/2`.**

### Summary of Proof
`hasDerivAt_ratioA` twice.

### Dependencies
**Depends on:** `c3G0'`, `c3G0''`, `hasDerivAt_ratioA`.
**Used by:** `c3G0_lower`. -/
theorem hasDerivAt_c3G0' {y : ℝ} (hy : 1 / 2 < y) : HasDerivAt c3G0' (c3G0'' y) y := by
  have hy' : 2 / 7 < y := by linarith
  have h1 := (hasDerivAt_ratioA (a := 1 / 2) (r := y) (by norm_num) hy).const_mul (c3m0 - c3mNeg1)
  have h2 := (hasDerivAt_ratioA (a := 2 / 7) (r := y) (by norm_num) hy').const_mul c3m0
  exact h1.sub h2

/-- **`c3F'` has derivative `c3F''` for `r > 5/7`.**

### Summary of Proof
`hasDerivAt_ratioA` three times.

### Dependencies
**Depends on:** `c3F'`, `c3F''`, `hasDerivAt_ratioA`.
**Used by:** `c3F_lower`. -/
theorem hasDerivAt_c3F' {y : ℝ} (hy : 5 / 7 < y) : HasDerivAt c3F' (c3F'' y) y := by
  have hy' : 1 / 2 < y := by linarith
  have hy'' : 2 / 7 < y := by linarith
  have h0 := (hasDerivAt_ratioA (a := 5 / 7) (r := y) (by norm_num) hy).const_mul (-c3m0)
  have h1 := (hasDerivAt_ratioA (a := 1 / 2) (r := y) (by norm_num) hy').const_mul (c3m0 - c3mNeg1)
  have h2 := (hasDerivAt_ratioA (a := 2 / 7) (r := y) (by norm_num) hy'').const_mul c3m0
  exact (h0.add h1).sub h2

/-- **`c3G1' ≤ 0` for `r > 2/7`**: `c3G1` is decreasing on `[2/7, 1/2]`.

### Summary of Proof
`m_0 > 0` and `cos θ ≥ 0`.

### Dependencies
**Depends on:** `c3G1'`, `c3m0_pos`, `rootA_nonneg`.
**Used by:** `c3G1_lower`. -/
theorem c3G1'_nonpos {y : ℝ} (hy : 2 / 7 < y) : c3G1' y ≤ 0 := by
  unfold c3G1' ratioA
  have hy0 : 0 < y := by linarith
  have := c3m0_pos
  have : 0 ≤ rootA (2 / 7) y / y := div_nonneg (rootA_nonneg _ _) hy0.le
  nlinarith

/-- **`c3G0'' ≥ 0` for `r > 1/2`**: `c3G0` is convex on `[1/2, 5/7]`.

### Summary of Proof
`(m_0 - m_{-1})/4 ≥ 4 m_0/49` (i.e. `82 m_0 ≥ 49 log π`, crude) and `u_{1/2} ≤ u_{2/7}`, so the
positive term dominates the negative one.

### Dependencies
**Depends on:** `c3G0''`, `rootA_pos`, `rootA_anti`, `c3B_pos`, `c3m0_pos`, `c3m0_bounds`,
`logPi_bounds`.
**Used by:** `c3G0_lower`. -/
theorem c3G0''_nonneg {y : ℝ} (hy : 1 / 2 < y) : 0 ≤ c3G0'' y := by
  have hy' : 2 / 7 < y := by linarith
  have hu0 := rootA_pos (a := 1 / 2) (r := y) (by norm_num) hy
  have hu1 := rootA_pos (a := 2 / 7) (r := y) (by norm_num) hy'
  have hle : rootA (1 / 2) y ≤ rootA (2 / 7) y := rootA_anti (by norm_num) (by norm_num)
  have hy0 : 0 < y := by linarith
  have hB := c3B_pos
  have hm := c3m0_pos
  have hcoef : c3m0 * (2 / 7) ^ 2 ≤ (c3m0 - c3mNeg1) * (1 / 2) ^ 2 := by
    unfold c3mNeg1; nlinarith [c3m0_bounds.1, logPi_bounds.2]
  unfold c3G0''
  rw [sub_nonneg]
  calc c3m0 * ((2 / 7) ^ 2 / (y ^ 2 * rootA (2 / 7) y))
      = (c3m0 * (2 / 7) ^ 2) / (y ^ 2 * rootA (2 / 7) y) := by ring
    _ ≤ (c3m0 * (2 / 7) ^ 2) / (y ^ 2 * rootA (1 / 2) y) := by gcongr
    _ ≤ ((c3m0 - c3mNeg1) * (1 / 2) ^ 2) / (y ^ 2 * rootA (1 / 2) y) := by gcongr
    _ = (c3m0 - c3mNeg1) * ((1 / 2) ^ 2 / (y ^ 2 * rootA (1 / 2) y)) := by ring

/-- **`c3F'' ≤ 0` for `r > 5/7`**: `c3F` is concave on `[5/7, 1]`.

### Summary of Proof
`(m_0 - m_{-1})/4 ≤ (25/49) m_0` (i.e. `49 (2 m_0 - log π) ≤ 100 m_0`, crude) and
`u_{5/7} ≤ u_{1/2}`, so the negative `a = 5/7` term dominates the positive `a = 1/2` term; the
`a = 2/7` term is negative outright.

### Dependencies
**Depends on:** `c3F''`, `rootA_pos`, `rootA_anti`, `c3B_pos`, `c3m0_pos`, `c3m0_bounds`,
`logPi_bounds`.
**Used by:** `c3F_lower`. -/
theorem c3F''_nonpos {y : ℝ} (hy : 5 / 7 < y) : c3F'' y ≤ 0 := by
  have hy' : 1 / 2 < y := by linarith
  have hy'' : 2 / 7 < y := by linarith
  have hum := rootA_pos (a := 5 / 7) (r := y) (by norm_num) hy
  have hu0 := rootA_pos (a := 1 / 2) (r := y) (by norm_num) hy'
  have hu1 := rootA_pos (a := 2 / 7) (r := y) (by norm_num) hy''
  have hle : rootA (5 / 7) y ≤ rootA (1 / 2) y := rootA_anti (by norm_num) (by norm_num)
  have hy0 : 0 < y := by linarith
  have hB := c3B_pos
  have hm := c3m0_pos
  have hcoef : (c3m0 - c3mNeg1) * (1 / 2) ^ 2 ≤ c3m0 * (5 / 7) ^ 2 := by
    unfold c3mNeg1; nlinarith [c3m0_bounds.1, logPi_bounds.1]
  have hthird : 0 ≤ c3m0 * ((2 / 7) ^ 2 / (y ^ 2 * rootA (2 / 7) y)) := by positivity
  have hmain : (c3m0 - c3mNeg1) * ((1 / 2) ^ 2 / (y ^ 2 * rootA (1 / 2) y))
      ≤ c3m0 * ((5 / 7) ^ 2 / (y ^ 2 * rootA (5 / 7) y)) := by
    calc (c3m0 - c3mNeg1) * ((1 / 2) ^ 2 / (y ^ 2 * rootA (1 / 2) y))
        = ((c3m0 - c3mNeg1) * (1 / 2) ^ 2) / (y ^ 2 * rootA (1 / 2) y) := by ring
      _ ≤ (c3m0 * (5 / 7) ^ 2) / (y ^ 2 * rootA (1 / 2) y) := by gcongr
      _ ≤ (c3m0 * (5 / 7) ^ 2) / (y ^ 2 * rootA (5 / 7) y) := by gcongr
      _ = c3m0 * ((5 / 7) ^ 2 / (y ^ 2 * rootA (5 / 7) y)) := by ring
  unfold c3F''
  linarith

/-- **`c3G1` is continuous on `[2/7, 1/2]`.**

### Summary of Proof
`continuousOn_chordBlock`; the interval avoids `r = 0`.

### Dependencies
**Depends on:** `c3G1`, `continuousOn_chordBlock`.
**Used by:** `c3G1_lower`. -/
theorem continuousOn_c3G1 : ContinuousOn c3G1 (Set.Icc (2 / 7) (1 / 2)) := by
  have hs : ∀ r ∈ Set.Icc (2 / 7 : ℝ) (1 / 2), r ≠ 0 := fun r hr => by
    have := hr.1; positivity
  unfold c3G1
  exact ((continuousOn_const.sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs))

/-- **`c3G0` is continuous on `[1/2, 5/7]`.**

### Summary of Proof
`continuousOn_chordBlock`.

### Dependencies
**Depends on:** `c3G0`, `continuousOn_chordBlock`.
**Used by:** `c3G0_lower`. -/
theorem continuousOn_c3G0 : ContinuousOn c3G0 (Set.Icc (1 / 2) (5 / 7)) := by
  have hs : ∀ r ∈ Set.Icc (1 / 2 : ℝ) (5 / 7), r ≠ 0 := fun r hr => by
    have := hr.1; positivity
  unfold c3G0
  exact ((((continuousOn_const.sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs)).sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs))

/-- **`c3F` is continuous on `[5/7, 1]`.**

### Summary of Proof
`continuousOn_chordBlock`.

### Dependencies
**Depends on:** `c3F`, `continuousOn_chordBlock`.
**Used by:** `c3F_lower`. -/
theorem continuousOn_c3F : ContinuousOn c3F (Set.Icc (5 / 7) 1) := by
  have hs : ∀ r ∈ Set.Icc (5 / 7 : ℝ) 1, r ≠ 0 := fun r hr => by
    have := hr.1; positivity
  unfold c3F
  exact ((((((continuousOn_const.sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs)).sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs)).sub (continuousOn_chordBlock _ _ _ hs)).add
    (continuousOn_chordBlock _ _ _ hs))

/-- **The tangent point `r₁ = 1/√3 = 0.57735`**, chosen so that `θ_{1/2}(r₁) = π/3` exactly and
`cos θ_{2/7}(r₁) = √37/7`; it lies `0.00027` below the true minimiser `r* = 0.57762` of `c_3`.

### Summary of Proof
Definition.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0_r1_ge`, `c3G0'_r1_bounds`, `c3G0_lower`. -/
noncomputable def c3r1 : ℝ := Real.sqrt (1 / 3)

/-- **`r₁² = 1/3`.**

### Summary of Proof
`Real.sq_sqrt`.

### Dependencies
**Depends on:** `c3r1`.
**Used by:** `rootA_half_r1`, `rootA_27_r1`. -/
theorem c3r1_sq : c3r1 ^ 2 = 1 / 3 := by unfold c3r1; rw [Real.sq_sqrt]; norm_num

/-- **`r₁ = (√3)⁻¹`.**

### Summary of Proof
`Real.sqrt_inv`.

### Dependencies
**Depends on:** `c3r1`.
**Used by:** `arcA_half_r1`, `arcA_27_r1_le`. -/
theorem c3r1_eq : c3r1 = (Real.sqrt 3)⁻¹ := by unfold c3r1; rw [one_div, Real.sqrt_inv]

/-- **`0.57735 ≤ r₁ ≤ 0.57736`.**

### Summary of Proof
`Real.le_sqrt`, `Real.sqrt_le_left` against `1/3`.

### Dependencies
**Depends on:** `c3r1`.
**Used by:** `c3G0_lower`. -/
theorem c3r1_bounds : (0.57735 : ℝ) ≤ c3r1 ∧ c3r1 ≤ 0.57736 := by
  unfold c3r1
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **`1.7320508 ≤ √3 ≤ 1.7320509`.**

### Summary of Proof
Squaring.

### Dependencies
**Depends on:** none.
**Used by:** `arcA_27_r1_le`. -/
theorem sqrt_three_bounds : (1.7320508 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.7320509 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **`θ_{1/2}(r₁) = π/3`.**

### Summary of Proof
`(1/2)/r₁ = √3/2 = sin (π/3)` and `Real.arcsin_sin`.

### Dependencies
**Depends on:** `arcA`, `c3r1_eq`.
**Used by:** `c3G0_r1_eq`. -/
theorem arcA_half_r1 : arcA (1 / 2) c3r1 = Real.pi / 3 := by
  unfold arcA
  rw [c3r1_eq]
  have hs : 0 < Real.sqrt 3 := by positivity
  have : (1 / 2 : ℝ) / (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 2 := by field_simp
  rw [this, ← Real.sin_pi_div_three]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- **`u_{1/2}(r₁) = √(1/12)`.**

### Summary of Proof
`r₁² - 1/4 = 1/12`.

### Dependencies
**Depends on:** `rootA`, `c3r1_sq`.
**Used by:** `c3G0_r1_eq`, `ratioA_half_r1`. -/
theorem rootA_half_r1 : rootA (1 / 2) c3r1 = Real.sqrt (1 / 12) := by
  unfold rootA; rw [c3r1_sq]; norm_num

/-- **`u_{2/7}(r₁) = √(37/147)`.**

### Summary of Proof
`r₁² - 4/49 = 37/147`.

### Dependencies
**Depends on:** `rootA`, `c3r1_sq`.
**Used by:** `c3G0_r1_eq`, `ratioA_27_r1`. -/
theorem rootA_27_r1 : rootA (2 / 7) c3r1 = Real.sqrt (37 / 147) := by
  unfold rootA; rw [c3r1_sq]; norm_num

/-- **`cos θ_{1/2}(r₁) = 1/2`.**

### Summary of Proof
`√(1/12)/√(1/3) = √(1/4)`.

### Dependencies
**Depends on:** `ratioA`, `rootA_half_r1`, `c3r1`.
**Used by:** `c3G0'_r1_bounds`. -/
theorem ratioA_half_r1 : ratioA (1 / 2) c3r1 = 1 / 2 := by
  unfold ratioA
  rw [rootA_half_r1]
  unfold c3r1
  rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  rw [show (1 / 12 : ℝ) / (1 / 3) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **`cos θ_{2/7}(r₁) = √(37/49)`.**

### Summary of Proof
`√(37/147)/√(1/3) = √(37/49)`.

### Dependencies
**Depends on:** `ratioA`, `rootA_27_r1`, `c3r1`.
**Used by:** `c3G0'_r1_bounds`. -/
theorem ratioA_27_r1 : ratioA (2 / 7) c3r1 = Real.sqrt (37 / 49) := by
  unfold ratioA
  rw [rootA_27_r1]
  unfold c3r1
  rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num

/-- **`θ_{2/7}(r₁) = arcsin (2√3/7) ≤ π/6 - 0.0059`** (true value `π/6 - 0.005912`).

### Summary of Proof
`Real.arcsin_le_iff_le_sin` reduces to `2√3/7 ≤ sin (π/6 - δ) = (cos δ)/2 - (√3/2) sin δ` with
`δ = 0.0059`; `cos δ ≥ 1 - δ²/2` (`Real.one_sub_sq_div_two_le_cos`) and `sin δ ≤ δ`
(`Real.sin_le`) give `≥ 0.4948817`, against `2√3/7 ≤ 0.4948717` from `sqrt_three_bounds`.

### Lean Notes
Only an upper bound on this angle is needed, since its coefficient `L - (m_0 + b_0)` in
`c3G0 r₁` is negative.

### Dependencies
**Depends on:** `arcA`, `c3r1_eq`, `sqrt_three_bounds`.
**Used by:** `c3G0_r1_ge`. -/
theorem arcA_27_r1_le : arcA (2 / 7) c3r1 ≤ Real.pi / 6 - 0.0059 := by
  have hs3 := sqrt_three_bounds
  have hs : 0 < Real.sqrt 3 := by positivity
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  unfold arcA
  rw [c3r1_eq]
  have hx : (2 / 7 : ℝ) / (Real.sqrt 3)⁻¹ = 2 * Real.sqrt 3 / 7 := by field_simp
  rw [hx]
  rw [Real.arcsin_le_iff_le_sin ⟨by nlinarith, by nlinarith⟩ ⟨by linarith, by linarith⟩]
  rw [Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 0.0059)
  have hsn := Real.sin_le (x := 0.0059) (by norm_num)
  have := mul_le_mul_of_nonneg_left hsn (Real.sqrt_nonneg 3)
  nlinarith

/-- **`0.288675 ≤ √(1/12) ≤ 0.288676`.**

### Summary of Proof
Squaring.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0_r1_ge`. -/
theorem sqrt_one_twelfth_bounds :
    (0.288675 : ℝ) ≤ Real.sqrt (1 / 12) ∧ Real.sqrt (1 / 12) ≤ 0.288676 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **`0.50169 ≤ √(37/147) ≤ 0.5017`.**

### Summary of Proof
Squaring.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0_r1_ge`. -/
theorem sqrt_37_147_bounds :
    (0.50169 : ℝ) ≤ Real.sqrt (37 / 147) ∧ Real.sqrt (37 / 147) ≤ 0.5017 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **`0.868966 ≤ √(37/49) ≤ 0.868967`.**

### Summary of Proof
Squaring.

### Dependencies
**Depends on:** none.
**Used by:** `c3G0'_r1_bounds`. -/
theorem sqrt_37_49_bounds :
    (0.868966 : ℝ) ≤ Real.sqrt (37 / 49) ∧ Real.sqrt (37 / 49) ≤ 0.868967 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **`c3G0 r₁` in closed form**:
`π (L₀/9 + 7L/18 + log π/12) + (4/3)(L₀ - L) θ_{2/7}(r₁) + (2m_0 - log π) √(1/12) - m_0 √(37/147)`.

### Summary of Proof
Unfold the blocks at `r₁`, substitute `θ_{1/2}(r₁) = π/3`, `u_{1/2}(r₁) = √(1/12)`,
`u_{2/7}(r₁) = √(37/147)`, and `ring` with the constants unfolded.

### Dependencies
**Depends on:** `c3G0`, `arcA_half_r1`, `rootA_half_r1`, `rootA_27_r1`.
**Used by:** `c3G0_r1_ge`. -/
theorem c3G0_r1_eq :
    c3G0 c3r1 = Real.pi * (c3L0 / 9 + 7 * c3L / 18 + logPi / 12)
      + 4 / 3 * (c3L0 - c3L) * arcA (2 / 7) c3r1
      + (2 * c3m0 - logPi) * Real.sqrt (1 / 12) - c3m0 * Real.sqrt (37 / 147) := by
  unfold c3G0 chordBlock
  rw [arcA_half_r1, rootA_half_r1, rootA_27_r1]
  unfold c3bNeg1 c3mNeg1 c3b0 c3m0
  ring

/-- **`c3G0 r₁ ≥ 0.0163`** (true value `0.0164999`).

### Summary of Proof
Each of the four terms of `c3G0_r1_eq` is bounded below from the interval bounds on `L`, `L₀`,
`log π`, `π`, `√(1/12)`, `√(37/147)` and the upper bound on `θ_{2/7}(r₁)`:
`0.659985 - 0.640795 + 2.170727 - 2.173475 = 0.016442`.

### Lean Notes
The margin `1.4·10⁻⁴` is genuine but small; `Code/verify_c3_tangent_route.py` recomputes this
chain in exact rational arithmetic.  Loosening any input bound by `10⁻⁴` would break it.

### Dependencies
**Depends on:** `c3G0_r1_eq`, `c3L_bounds`, `c3L0_bounds`, `logPi_bounds`, `c3m0_bounds`,
`arcA_27_r1_le`, `sqrt_one_twelfth_bounds`, `sqrt_37_147_bounds`.
**Used by:** `c3G0_lower`. -/
theorem c3G0_r1_ge : (0.0163 : ℝ) ≤ c3G0 c3r1 := by
  rw [c3G0_r1_eq]
  have hL := c3L_bounds
  have h0 := c3L0_bounds
  have hP := logPi_bounds
  have hm := c3m0_bounds
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hth := arcA_27_r1_le
  have hs1 := sqrt_one_twelfth_bounds
  have hs2 := sqrt_37_147_bounds
  have t1 : (3.141592 : ℝ) * 0.21008 ≤ Real.pi * (c3L0 / 9 + 7 * c3L / 18 + logPi / 12) := by
    apply mul_le_mul hpi.le (by linarith) (by norm_num) Real.pi_pos.le
  have t2 : (4 / 3 * (c3L0 - c3L)) * (Real.pi / 6 - 0.0059)
      ≤ 4 / 3 * (c3L0 - c3L) * arcA (2 / 7) c3r1 := by
    apply mul_le_mul_of_nonpos_left hth (by linarith)
  have t2a : (-1.237776 : ℝ) * (Real.pi / 6 - 0.0059)
      ≤ (4 / 3 * (c3L0 - c3L)) * (Real.pi / 6 - 0.0059) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have t2b : (-1.237776 : ℝ) * (3.141593 / 6 - 0.0059) ≤ (-1.237776 : ℝ) * (Real.pi / 6 - 0.0059) :=
    mul_le_mul_of_nonpos_left (by linarith) (by norm_num)
  have t3 : (7.51962 : ℝ) * 0.288675 ≤ (2 * c3m0 - logPi) * Real.sqrt (1 / 12) := by
    apply mul_le_mul (by linarith) hs1.1 (by norm_num) (by linarith)
  have t4 : c3m0 * Real.sqrt (37 / 147) ≤ (4.33222 : ℝ) * 0.5017 := by
    apply mul_le_mul hm.2 hs2.2 (Real.sqrt_nonneg _) (by norm_num)
  linarith

/-- **`|c3G0' r₁| ≤ 0.006`** (true value `-0.0047`).

### Summary of Proof
`c3G0' r₁ = (m_0 - m_{-1})/2 - m_0 √(37/49)` by `ratioA_half_r1`, `ratioA_27_r1`; interval bounds.

### Dependencies
**Depends on:** `c3G0'`, `ratioA_half_r1`, `ratioA_27_r1`, `c3m0_bounds`, `logPi_bounds`,
`sqrt_37_49_bounds`.
**Used by:** `c3G0_lower`. -/
theorem c3G0'_r1_bounds : (-0.006 : ℝ) ≤ c3G0' c3r1 ∧ c3G0' c3r1 ≤ 0.006 := by
  unfold c3G0'
  rw [ratioA_half_r1, ratioA_27_r1]
  have hm := c3m0_bounds
  have hP := logPi_bounds
  have hs := sqrt_37_49_bounds
  have t1 : c3m0 * Real.sqrt (37 / 49) ≤ (4.33222 : ℝ) * 0.868967 :=
    mul_le_mul hm.2 hs.2 (Real.sqrt_nonneg _) (by norm_num)
  have t2 : (4.33218 : ℝ) * 0.868966 ≤ c3m0 * Real.sqrt (37 / 49) :=
    mul_le_mul hm.1 hs.1 (by norm_num) (by linarith)
  unfold c3mNeg1
  constructor <;> linarith

/-- **`c3G0 ≥ 0.012` on `[1/2, 5/7]`.**

### Summary of Proof
`c3G0'` is monotone on `(1/2, 5/7)` (`monotoneOn_Ioo_of_hasDerivAt` with `c3G0''_nonneg`), so
`tangent_le_of_monotone_deriv` at `r₁` gives `c3G0 x ≥ c3G0 r₁ + c3G0' r₁ (x - r₁)
≥ 0.0163 - 0.006 · 0.14 > 0.012`, since `x - r₁ ∈ [-0.08, 0.14]` on the regime.

### Lean Notes
This single tangent line covers the whole regime, including its endpoints `1/2` and `5/7`, which
is what makes the other two regimes cheap (`c3G1_lower`, `c3F_lower`).

### Dependencies
**Depends on:** `continuousOn_c3G0`, `hasDerivAt_c3G0`, `hasDerivAt_c3G0'`, `c3G0''_nonneg`,
`c3G0_r1_ge`, `c3G0'_r1_bounds`, `c3r1_bounds`, `tangent_le_of_monotone_deriv`,
`monotoneOn_Ioo_of_hasDerivAt`.
**Used by:** `c3_nonneg`, `c3G1_lower`, `c3F_lower`. -/
theorem c3G0_lower {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) : (0.012 : ℝ) ≤ c3G0 x := by
  have hr1 := c3r1_bounds
  have hr1mem : c3r1 ∈ Set.Ioo (1 / 2 : ℝ) (5 / 7) := ⟨by linarith, by linarith⟩
  have hmono : MonotoneOn c3G0' (Set.Ioo (1 / 2 : ℝ) (5 / 7)) :=
    monotoneOn_Ioo_of_hasDerivAt (fun y hy => hasDerivAt_c3G0' hy.1)
      (fun y hy => c3G0''_nonneg hy.1)
  have h := tangent_le_of_monotone_deriv continuousOn_c3G0 (fun y hy => hasDerivAt_c3G0 hy.1)
    hmono hr1mem hx
  have hv := c3G0_r1_ge
  have hd := c3G0'_r1_bounds
  have hx1 := hx.1
  have hx2 := hx.2
  nlinarith [mul_nonneg (sub_nonneg.2 hd.2) (sub_nonneg.2 (show x - c3r1 ≤ 0.14 by linarith)),
    mul_nonneg (sub_nonneg.2 hd.2) (sub_nonneg.2 (show -0.08 ≤ x - c3r1 by linarith)),
    mul_nonneg (sub_nonneg.2 hd.1) (sub_nonneg.2 (show x - c3r1 ≤ 0.14 by linarith)),
    mul_nonneg (sub_nonneg.2 hd.1) (sub_nonneg.2 (show -0.08 ≤ x - c3r1 by linarith))]

/-- **`c3G1 (1/2) = c3G0 (1/2)`**: the closed forms agree at the regime boundary.

### Summary of Proof
At `r = 1/2`, `θ_{1/2} = arcsin 1 = π/2` and `u_{1/2} = 0`, so the `k = -1` block of `c3G0`
cancels its boundary term.

### Dependencies
**Depends on:** `c3G1`, `c3G0`.
**Used by:** `c3G1_lower`. -/
theorem c3G1_half_eq : c3G1 (1 / 2) = c3G0 (1 / 2) := by
  unfold c3G1 c3G0 chordBlock
  have h1 : arcA (1 / 2) (1 / 2) = Real.pi / 2 := by
    unfold arcA; rw [div_self (by norm_num), Real.arcsin_one]
  have h2 : rootA (1 / 2) (1 / 2) = 0 := by unfold rootA; norm_num
  rw [h1, h2]
  ring

/-- **`c3F (5/7) = c3G0 (5/7)`**: the closed forms agree at the regime boundary.

### Summary of Proof
At `r = 5/7`, `θ_{5/7} = π/2` and `u_{5/7} = 0`.

### Dependencies
**Depends on:** `c3F`, `c3G0`.
**Used by:** `c3F_lower`. -/
theorem c3F_57_eq : c3F (5 / 7) = c3G0 (5 / 7) := by
  unfold c3F c3G0 chordBlock
  have h1 : arcA (5 / 7) (5 / 7) = Real.pi / 2 := by
    unfold arcA; rw [div_self (by norm_num), Real.arcsin_one]
  have h2 : rootA (5 / 7) (5 / 7) = 0 := by unfold rootA; norm_num
  rw [h1, h2]
  ring

/-- **`arcsin (5/7) ≤ 0.8`** (true value `0.79560`).

### Summary of Proof
`Real.arcsin_le_iff_le_sin` and `sin 0.8 > 0.8 - 0.8³/6 = 0.71467 > 5/7`
(`Real.sin_gt_sub_cube`).

### Dependencies
**Depends on:** none.
**Used by:** `c3F_one_ge`. -/
theorem arcsin_five_sevenths_le : Real.arcsin (5 / 7) ≤ 0.8 := by
  have hpi := Real.pi_gt_d2
  rw [Real.arcsin_le_iff_le_sin ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩]
  have := Real.sin_gt_sub_cube (x := 0.8) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **`arcsin (2/7) ≤ 0.2945`** (true value `0.28975`).

### Summary of Proof
As `arcsin_five_sevenths_le`: `0.2945 - 0.2945³/6 = 0.29024 > 2/7`.

### Dependencies
**Depends on:** none.
**Used by:** `c3F_one_ge`. -/
theorem arcsin_two_sevenths_le : Real.arcsin (2 / 7) ≤ 0.2945 := by
  have hpi := Real.pi_gt_d2
  rw [Real.arcsin_le_iff_le_sin ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩]
  have := Real.sin_gt_sub_cube (x := 0.2945) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **`c3F 1` in closed form**, with `θ_{1/2}(1) = π/6`, `u_{5/7}(1) = √(24/49)`,
`u_{1/2}(1) = √(3/4)`, `u_{2/7}(1) = √(45/49)`.

### Summary of Proof
Unfold and `ring`, after `Real.arcsin_sin` at `π/6`.

### Dependencies
**Depends on:** `c3F`.
**Used by:** `c3F_one_ge`. -/
theorem c3F_one_eq :
    c3F 1 = (c3L + logPi / 2) * (Real.pi / 2) + 10 / 3 * (c3L0 - c3L) * Real.arcsin (5 / 7)
      + (c3m0 - logPi / 2) * (Real.pi / 6) + 4 / 3 * (c3L0 - c3L) * Real.arcsin (2 / 7)
      - c3m0 * Real.sqrt (24 / 49) + (2 * c3m0 - logPi) * Real.sqrt (3 / 4)
      - c3m0 * Real.sqrt (45 / 49) := by
  unfold c3F chordBlock
  have h1 : arcA (1 / 2) 1 = Real.pi / 6 := by
    unfold arcA
    rw [div_one, ← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : arcA (5 / 7) 1 = Real.arcsin (5 / 7) := by unfold arcA; rw [div_one]
  have h3 : arcA (2 / 7) 1 = Real.arcsin (2 / 7) := by unfold arcA; rw [div_one]
  have h4 : rootA (5 / 7) 1 = Real.sqrt (24 / 49) := by unfold rootA; norm_num
  have h5 : rootA (1 / 2) 1 = Real.sqrt (3 / 4) := by unfold rootA; norm_num
  have h6 : rootA (2 / 7) 1 = Real.sqrt (45 / 49) := by unfold rootA; norm_num
  rw [h1, h2, h3, h4, h5, h6]
  unfold c3bNeg1 c3mNeg1 c3b0 c3m0
  ring

/-- **`c3F 1 ≥ 0.03`** (true value `0.060186`; with the crude `arcsin` bounds the chain gives
`0.04034`).

### Summary of Proof
Seven termwise bounds on `c3F_one_eq`, using the upper bounds `arcsin (5/7) ≤ 0.8`,
`arcsin (2/7) ≤ 0.2945` (both coefficients are negative), and the square-root bounds by squaring.

### Dependencies
**Depends on:** `c3F_one_eq`, `c3L_bounds`, `c3L0_bounds`, `logPi_bounds`, `c3m0_bounds`,
`arcsin_five_sevenths_le`, `arcsin_two_sevenths_le`.
**Used by:** `c3F_lower`. -/
theorem c3F_one_ge : (0.03 : ℝ) ≤ c3F 1 := by
  rw [c3F_one_eq]
  have hL := c3L_bounds
  have h0 := c3L0_bounds
  have hP := logPi_bounds
  have hm := c3m0_bounds
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have ha1 := arcsin_five_sevenths_le
  have ha2 := arcsin_two_sevenths_le
  have ha1' : 0 ≤ Real.arcsin (5 / 7) := Real.arcsin_nonneg.mpr (by norm_num)
  have ha2' : 0 ≤ Real.arcsin (2 / 7) := Real.arcsin_nonneg.mpr (by norm_num)
  have hs1 : Real.sqrt (24 / 49) ≤ 0.69986 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2 : (0.866025 : ℝ) ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs3 : Real.sqrt (45 / 49) ≤ 0.95832 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have t1 : (1.008029 : ℝ) * (3.141592 / 2) ≤ (c3L + logPi / 2) * (Real.pi / 2) := by
    apply mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have t2 : (10 / 3 * (c3L0 - c3L)) * 0.8 ≤ 10 / 3 * (c3L0 - c3L) * Real.arcsin (5 / 7) :=
    mul_le_mul_of_nonpos_left ha1 (by linarith)
  have t3 : (3.75981 : ℝ) * (3.141592 / 6) ≤ (c3m0 - logPi / 2) * (Real.pi / 6) := by
    apply mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have t4 : (4 / 3 * (c3L0 - c3L)) * 0.2945 ≤ 4 / 3 * (c3L0 - c3L) * Real.arcsin (2 / 7) :=
    mul_le_mul_of_nonpos_left ha2 (by linarith)
  have t5 : c3m0 * Real.sqrt (24 / 49) ≤ (4.33222 : ℝ) * 0.69986 :=
    mul_le_mul hm.2 hs1 (Real.sqrt_nonneg _) (by norm_num)
  have t6 : (7.51962 : ℝ) * 0.866025 ≤ (2 * c3m0 - logPi) * Real.sqrt (3 / 4) := by
    apply mul_le_mul (by linarith) hs2 (by norm_num) (by linarith)
  have t7 : c3m0 * Real.sqrt (45 / 49) ≤ (4.33222 : ℝ) * 0.95832 :=
    mul_le_mul hm.2 hs3 (Real.sqrt_nonneg _) (by norm_num)
  linarith

/-- **`c3G1 ≥ 0.012` on `[2/7, 1/2]`.**

### Summary of Proof
`c3G1` is decreasing (`c3G1'_nonpos`, `right_le_of_nonpos_deriv`), so it is at least
`c3G1 (1/2) = c3G0 (1/2) ≥ 0.012` (`c3G1_half_eq`, `c3G0_lower`).

### Dependencies
**Depends on:** `continuousOn_c3G1`, `hasDerivAt_c3G1`, `c3G1'_nonpos`, `c3G1_half_eq`,
`c3G0_lower`, `right_le_of_nonpos_deriv`.
**Used by:** `c3_nonneg`. -/
theorem c3G1_lower {x : ℝ} (hx : x ∈ Set.Icc (2 / 7 : ℝ) (1 / 2)) : (0.012 : ℝ) ≤ c3G1 x := by
  have h := right_le_of_nonpos_deriv continuousOn_c3G1 (fun y hy => hasDerivAt_c3G1 hy.1)
    (fun y hy => c3G1'_nonpos hy.1) hx
  have := c3G0_lower (x := 1 / 2) ⟨le_rfl, by norm_num⟩
  rw [c3G1_half_eq] at h
  linarith

/-- **`c3F ≥ 0.012` on `[5/7, 1]`.**

### Summary of Proof
`c3F` is concave (`c3F''_nonpos`, `antitoneOn_Ioo_of_hasDerivAt`), so by `min_le_of_antitone_deriv`
it is at least `min (c3F (5/7)) (c3F 1) = min (c3G0 (5/7)) (c3F 1) ≥ min 0.012 0.03`.

### Dependencies
**Depends on:** `continuousOn_c3F`, `hasDerivAt_c3F`, `hasDerivAt_c3F'`, `c3F''_nonpos`,
`c3F_57_eq`, `c3G0_lower`, `c3F_one_ge`, `min_le_of_antitone_deriv`,
`antitoneOn_Ioo_of_hasDerivAt`.
**Used by:** `c3_nonneg`. -/
theorem c3F_lower {x : ℝ} (hx : x ∈ Set.Icc (5 / 7 : ℝ) 1) : (0.012 : ℝ) ≤ c3F x := by
  have hanti : AntitoneOn c3F' (Set.Ioo (5 / 7 : ℝ) 1) :=
    antitoneOn_Ioo_of_hasDerivAt (fun y hy => hasDerivAt_c3F' hy.1) (fun y hy => c3F''_nonpos hy.1)
  have h := min_le_of_antitone_deriv continuousOn_c3F (fun y hy => hasDerivAt_c3F hy.1) hanti hx
  have h1 := c3G0_lower (x := 5 / 7) ⟨by norm_num, le_rfl⟩
  have h2 := c3F_one_ge
  rw [c3F_57_eq] at h
  have : (0.012 : ℝ) ≤ min (c3G0 (5 / 7)) (c3F 1) := le_min h1 (by linarith)
  linarith

/-- **`σ_0 = 1/2`.**

### Summary of Proof
`norm_num [sigma]`.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `bCoeffPP_zero_eq`, `c3_eq_c3F`, `c3_eq_c3G0`, `c3_nonneg`, `mCoeffPP_neg_one_eq`,
`mCoeffPP_zero_eq`. -/
theorem sigma_zero_eq : sigma 0 = 1 / 2 := by norm_num [sigma]

/-- **`σ_1 = 5/7`.**

### Summary of Proof
`norm_num [sigma]`.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `mCoeffPP_zero_eq`, `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`, `c3_nonneg`. -/
theorem sigma_one_eq : sigma 1 = 5 / 7 := by norm_num [sigma]

/-- **`σ_{-1} = 2/7`.**

### Summary of Proof
`norm_num [sigma]`.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `mCoeffPP_neg_one_eq`, `bCoeffPP_neg_one_eq`, `c3_eq_c3F`, `c3_nonneg`. -/
theorem sigma_neg_one_eq : sigma (-1) = 2 / 7 := by norm_num [sigma]

/-- **`mCoeffPP 0 = m_0`.**

### Summary of Proof
Unfold; `(L₀ - L)/(1/2 - 5/7) = (14/3)(L - L₀)`.

### Dependencies
**Depends on:** `mCoeffPP`, `vCoeffPP`, `sigma_zero_eq`, `sigma_one_eq`, `c3m0`.
**Used by:** `bCoeffPP_zero_eq`, `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem mCoeffPP_zero_eq : mCoeffPP 0 = c3m0 := by
  unfold mCoeffPP vCoeffPP c3m0 c3L c3L0
  rw [show (0 : ℤ) + 1 = 1 by norm_num, sigma_zero_eq, sigma_one_eq]
  simp only [lt_self_iff_false, ite_false, ite_true, zero_lt_one]
  ring

/-- **`bCoeffPP 0 = b_0`.**

### Summary of Proof
Unfold; `L₀ - m_0/2`.

### Dependencies
**Depends on:** `bCoeffPP`, `mCoeffPP_zero_eq`, `sigma_zero_eq`, `c3b0`.
**Used by:** `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem bCoeffPP_zero_eq : bCoeffPP 0 = c3b0 := by
  unfold bCoeffPP c3b0
  rw [mCoeffPP_zero_eq, sigma_zero_eq]
  unfold vCoeffPP c3L0
  simp only [lt_self_iff_false, ite_false, ite_true]
  ring

/-- **`mCoeffPP (-1) = m_{-1}`.**

### Summary of Proof
Unfold; `(L + (2/7 - 1/2) log π - L₀)/(2/7 - 1/2) = log π - m_0`.

### Dependencies
**Depends on:** `mCoeffPP`, `vCoeffPP`, `sigma_neg_one_eq`, `sigma_zero_eq`, `c3mNeg1`.
**Used by:** `bCoeffPP_neg_one_eq`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem mCoeffPP_neg_one_eq : mCoeffPP (-1) = c3mNeg1 := by
  unfold mCoeffPP vCoeffPP c3mNeg1 c3m0 c3L c3L0 logPi
  rw [sigma_neg_one_eq, show (-1 : ℤ) + 1 = 0 by norm_num, sigma_zero_eq]
  simp only [lt_self_iff_false, ite_false, ite_true,
    show ¬ ((0 : ℤ) < -1) by norm_num, show (-1 : ℤ) ≠ 0 by norm_num]
  ring

/-- **`bCoeffPP (-1) = b_{-1}`.**

### Summary of Proof
Unfold; `v''_{-1} - m_{-1} (2/7) = L₀ - m_{-1}/2` by continuity of the two chords at `σ_0`.

### Dependencies
**Depends on:** `bCoeffPP`, `mCoeffPP_neg_one_eq`, `sigma_neg_one_eq`, `c3bNeg1`.
**Used by:** `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem bCoeffPP_neg_one_eq : bCoeffPP (-1) = c3bNeg1 := by
  unfold bCoeffPP c3bNeg1
  rw [mCoeffPP_neg_one_eq, sigma_neg_one_eq]
  unfold vCoeffPP c3mNeg1 c3m0 c3L c3L0 logPi
  simp only [show ¬ ((0 : ℤ) < -1) by norm_num, show (-1 : ℤ) ≠ 0 by norm_num, ite_false]
  rw [sigma_neg_one_eq]
  ring

/-- **`mCoeffPP k = log π` for `k ≤ -2`**: all the far chords have the same slope.

### Summary of Proof
Both `v''_k` and `v''_{k+1}` are on the negative branch `L + (σ - 1/2) log π`, so the difference
quotient is `log π` (`sigma_lt_succ` for the nonzero denominator).

### Dependencies
**Depends on:** `mCoeffPP`, `vCoeffPP`, `sigma_lt_succ`, `logPi`.
**Used by:** `bCoeffPP_of_le_neg_two`, `c3_eq_c3F`. -/
theorem mCoeffPP_of_le_neg_two {k : ℤ} (hk : k ≤ -2) : mCoeffPP k = logPi := by
  unfold mCoeffPP vCoeffPP logPi
  have h1 : ¬ (0 < k) := by omega
  have h2 : k ≠ 0 := by omega
  have h3 : ¬ (0 < k + 1) := by omega
  have h4 : k + 1 ≠ 0 := by omega
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
  have hne : sigma k - sigma (k + 1) ≠ 0 := by linarith [sigma_lt_succ k]
  field_simp
  ring

/-- **`bCoeffPP k = L - (log π)/2` for `k ≤ -2`**: all the far chords have the same intercept.

### Summary of Proof
`v''_k - log π · σ_k = L - (log π)/2`.

### Dependencies
**Depends on:** `bCoeffPP`, `mCoeffPP_of_le_neg_two`, `c3L`, `logPi`.
**Used by:** `c3_eq_c3F`. -/
theorem bCoeffPP_of_le_neg_two {k : ℤ} (hk : k ≤ -2) : bCoeffPP k = c3L - logPi / 2 := by
  unfold bCoeffPP
  rw [mCoeffPP_of_le_neg_two hk]
  unfold vCoeffPP c3L logPi
  have h1 : ¬ (0 < k) := by omega
  have h2 : k ≠ 0 := by omega
  rw [ite_eq_right h1, ite_eq_right h2]
  ring

/-- **`cos θ_{k,r} = u_{1 - σ_k}(r)/r`** for `r > 0`.

### Summary of Proof
`Real.cos_arcsin` and `√(1 - a²/r²) = √(r² - a²)/r` (`Real.sqrt_div'`, `Real.sqrt_sq`); no
hypothesis `1 - σ_k ≤ r` is needed, since both sides vanish otherwise.

### Dependencies
**Depends on:** `theta`, `rootA`.
**Used by:** `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem cos_theta_eq_rootA {k : ℤ} {r : ℝ} (hr : 0 < r) :
    Real.cos (theta k r) = rootA (1 - sigma k) r / r := by
  unfold theta rootA
  rw [Real.cos_arcsin]
  have : (1 : ℝ) - ((1 - sigma k) / r) ^ 2 = (r ^ 2 - (1 - sigma k) ^ 2) / r ^ 2 := by
    field_simp
  rw [this, Real.sqrt_div' _ (sq_nonneg r), Real.sqrt_sq hr.le]

/-- **`theta k r = arcA (1 - σ_k) r`**, definitionally.

### Summary of Proof
`rfl`.

### Dependencies
**Depends on:** `theta`, `arcA`.
**Used by:** `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem theta_eq_arcA (k : ℤ) (r : ℝ) : theta k r = arcA (1 - sigma k) r := rfl

/-- **`Kidx r ≤ K` whenever `1 - σ_K ≤ r`.**

### Summary of Proof
`csInf_le` with `Kidx_set_bddBelow`.

### Dependencies
**Depends on:** `Kidx`, `Kidx_set_bddBelow`.
**Used by:** `Kidx_eq_of`, `c3_nonneg`. -/
theorem Kidx_le_of_le {K : ℤ} {r : ℝ} (hr1 : r < 1) (h : 1 - sigma K ≤ r) : Kidx r ≤ K :=
  csInf_le (Kidx_set_bddBelow hr1) h

/-- **`K ≤ Kidx r` whenever `r < 1 - σ_{K-1}`.**

### Summary of Proof
If `Kidx r ≤ K - 1` then `σ_{Kidx r} ≤ σ_{K-1}` (`sigma_strictMono`), contradicting
`1 - σ_{Kidx r} ≤ r` (`Kidx_mem`).

### Dependencies
**Depends on:** `Kidx_mem`, `sigma_strictMono`.
**Used by:** `Kidx_eq_of`, `c3_nonneg`. -/
theorem le_Kidx_of_lt {K : ℤ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (h : r < 1 - sigma (K - 1)) :
    K ≤ Kidx r := by
  by_contra hcon
  have hmono : sigma (Kidx r) ≤ sigma (K - 1) := sigma_strictMono.monotone (by omega)
  have := Kidx_mem hr hr1
  linarith

/-- **`Kidx r = K` iff `1 - σ_K ≤ r < 1 - σ_{K-1}`** (the forward direction).

### Summary of Proof
`Kidx_le_of_le` and `le_Kidx_of_lt`.

### Dependencies
**Depends on:** `Kidx_le_of_le`, `le_Kidx_of_lt`.
**Used by:** `c3_nonneg`. -/
theorem Kidx_eq_of {K : ℤ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (h1 : 1 - sigma K ≤ r)
    (h2 : r < 1 - sigma (K - 1)) : Kidx r = K :=
  le_antisymm (Kidx_le_of_le hr1 h1) (le_Kidx_of_lt hr hr1 h2)

/-- **The `c3` series split after `N` terms**: for `Kidx r + N ≥ 1` the tail is
`log 1.546 · θ_{K+N}`, because every chord with index `≥ 1` has `m'' = 0`, `b'' = log 1.546` and the
angle differences telescope (`hasSum_theta_diff`).

### Summary of Proof
`Summable.sum_add_tsum_nat_add` on `c3_summable`; the shifted summand is
`log 1.546 · (θ_{K+N+j} - θ_{K+N+j+1})` by `mCoeffPP_eq_zero_of_pos`, `bCoeffPP_eq_of_pos`.

### Dependencies
**Depends on:** `c3`, `c3_summable`, `hasSum_theta_diff`, `mCoeffPP_eq_zero_of_pos`,
`bCoeffPP_eq_of_pos`.
**Used by:** `c3_eq_of_two_le_Kidx`, `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`. -/
theorem c3_eq_finite_split {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : 0 < Kidx r + N) :
    c3 r = (mCoeffPP (Kidx r - 1) + bCoeffPP (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
      - mCoeffPP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
      + ∑ j ∈ Finset.range N,
          ((mCoeffPP (Kidx r + j) + bCoeffPP (Kidx r + j))
              * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
            + mCoeffPP (Kidx r + j) * r
                * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
      + Real.log 1.546 * theta (Kidx r + N) r := by
  unfold c3
  rw [← (c3_summable hr).sum_add_tsum_nat_add N, ← add_assoc]
  congr 1
  have h := (hasSum_theta_diff (Kidx r + N) hr).mul_left (Real.log 1.546)
  rw [← h.tsum_eq]
  congr 1
  funext j
  have hpos : 0 < Kidx r + ((j + N : ℕ) : ℤ) := by push_cast; omega
  rw [mCoeffPP_eq_zero_of_pos hpos, bCoeffPP_eq_of_pos hpos,
    show Kidx r + ((j + N : ℕ) : ℤ) = Kidx r + N + (j : ℤ) by push_cast; ring]
  ring

/-- **Telescoping of `M` identical linear chords**:
`Σ_{j<M} [A (θ_{K+j} - θ_{K+j+1}) + B (cos θ_{K+j} - cos θ_{K+j+1})]
= A (θ_K - θ_{K+M}) + B (cos θ_K - cos θ_{K+M})`.

### Summary of Proof
Induction on `M`, as `sum_range_theta_telescope`.

### Dependencies
**Depends on:** `theta`.
**Used by:** `c3_eq_c3F`. -/
theorem theta_cos_telescope (K : ℤ) (r A B : ℝ) (M : ℕ) :
    ∑ j ∈ Finset.range M,
        (A * (theta (K + j) r - theta (K + j + 1) r)
          + B * (Real.cos (theta (K + j) r) - Real.cos (theta (K + j + 1) r)))
      = A * (theta K r - theta (K + M) r)
        + B * (Real.cos (theta K r) - Real.cos (theta (K + M) r)) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (K + (m : ℤ) + 1) = K + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; ring

/-- **`c3 r = log 1.546 · π/2` when `Kidx r ≥ 2`** (i.e. `r < 2/7`).

### Summary of Proof
`c3_eq_finite_split` with `N = 0`; the boundary chord `Kidx r - 1 ≥ 1` has `m'' = 0`,
`b'' = log 1.546`, so `c3 r = L (π/2 - θ_K) + L θ_K`.

### Dependencies
**Depends on:** `c3_eq_finite_split`, `mCoeffPP_eq_zero_of_pos`, `bCoeffPP_eq_of_pos`.
**Used by:** `c3_nonneg`. -/
theorem c3_eq_of_two_le_Kidx {r : ℝ} (hr : 0 < r) (hK : 2 ≤ Kidx r) :
    c3 r = Real.log 1.546 * (Real.pi / 2) := by
  rw [c3_eq_finite_split hr 0 (by omega)]
  simp only [Finset.sum_range_zero, Nat.cast_zero, add_zero]
  rw [mCoeffPP_eq_zero_of_pos (by omega), bCoeffPP_eq_of_pos (by omega)]
  ring

/-- **`c3 r = c3G1 r` when `Kidx r = 1`** (i.e. `2/7 ≤ r < 1/2`).

### Summary of Proof
`c3_eq_finite_split` with `N = 0`; the boundary chord is `k = 0`, and `r cos θ_1 = u_{2/7}(r)`.

### Dependencies
**Depends on:** `c3_eq_finite_split`, `mCoeffPP_zero_eq`, `bCoeffPP_zero_eq`,
`cos_theta_eq_rootA`, `theta_eq_arcA`, `sigma_one_eq`, `c3G1`.
**Used by:** `c3_nonneg`. -/
theorem c3_eq_c3G1 {r : ℝ} (hr : 0 < r) (hK : Kidx r = 1) : c3 r = c3G1 r := by
  rw [c3_eq_finite_split hr 0 (by omega)]
  simp only [Finset.sum_range_zero, Nat.cast_zero, add_zero]
  rw [hK, show (1 : ℤ) - 1 = 0 by norm_num, mCoeffPP_zero_eq, bCoeffPP_zero_eq,
    cos_theta_eq_rootA hr, theta_eq_arcA, sigma_one_eq]
  unfold c3G1 chordBlock c3L
  field_simp
  ring_nf

/-- **`c3 r = c3G0 r` when `Kidx r = 0`** (i.e. `1/2 ≤ r < 5/7`).

### Summary of Proof
`c3_eq_finite_split` with `N = 1`: boundary chord `k = -1`, one series term `k = 0`, tail
`L θ_1`.

### Dependencies
**Depends on:** `c3_eq_finite_split`, `mCoeffPP_zero_eq`, `bCoeffPP_zero_eq`,
`mCoeffPP_neg_one_eq`, `bCoeffPP_neg_one_eq`, `cos_theta_eq_rootA`, `theta_eq_arcA`,
`sigma_zero_eq`, `sigma_one_eq`, `c3G0`.
**Used by:** `c3_nonneg`. -/
theorem c3_eq_c3G0 {r : ℝ} (hr : 0 < r) (hK : Kidx r = 0) : c3 r = c3G0 r := by
  rw [c3_eq_finite_split hr 1 (by omega)]
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one]
  rw [hK, show (0 : ℤ) - 1 = -1 by norm_num, zero_add, mCoeffPP_zero_eq, bCoeffPP_zero_eq,
    mCoeffPP_neg_one_eq, bCoeffPP_neg_one_eq, cos_theta_eq_rootA hr, cos_theta_eq_rootA hr,
    theta_eq_arcA, theta_eq_arcA, sigma_one_eq, sigma_zero_eq]
  unfold c3G0 chordBlock c3L
  field_simp
  ring_nf

/-- **`c3 r = c3F r` when `Kidx r ≤ -1`** (i.e. `5/7 ≤ r < 1`), uniformly in `Kidx r`.

### Summary of Proof
Write `Kidx r = -1 - M` and split after `M + 2` terms (`c3_eq_finite_split`).  The first `M`
terms are identical linear chords (`mCoeffPP_of_le_neg_two`, `bCoeffPP_of_le_neg_two`) and
telescope (`theta_cos_telescope`) against the boundary term into
`(L + log π/2)(π/2 - θ_{-1}) - log π · r cos θ_{-1}`; the last two terms are the `k = -1`, `k = 0`
chords and the tail is `L θ_1`.

### Lean Notes
After the index rewrites `Kidx r + M = -1`, `Kidx r + (M+1) = 0`, `Kidx r + (M+2) = 1` the
indices `-1 + 1` and `0 + 1` must be normalised by hand before `cos_theta_eq_rootA` and
`theta_eq_arcA` fire on them.

### Dependencies
**Depends on:** `c3_eq_finite_split`, `theta_cos_telescope`, `mCoeffPP_of_le_neg_two`,
`bCoeffPP_of_le_neg_two`, `mCoeffPP_zero_eq`, `bCoeffPP_zero_eq`, `mCoeffPP_neg_one_eq`,
`bCoeffPP_neg_one_eq`, `cos_theta_eq_rootA`, `theta_eq_arcA`, `sigma_neg_one_eq`,
`sigma_zero_eq`, `sigma_one_eq`, `c3F`.
**Used by:** `c3_nonneg`. -/
theorem c3_eq_c3F {r : ℝ} (hr : 0 < r) (hK : Kidx r ≤ -1) : c3 r = c3F r := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Kidx r = -1 - M := ⟨(-1 - Kidx r).toNat, by omega⟩
  rw [c3_eq_finite_split hr (M + 2) (by omega)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hlin : ∀ j ∈ Finset.range M,
      ((mCoeffPP (Kidx r + j) + bCoeffPP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffPP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
      = ((logPi + (c3L - logPi / 2)) * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + (logPi * r)
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mCoeffPP_of_le_neg_two (by omega), bCoeffPP_of_le_neg_two (by omega)]
  rw [Finset.sum_congr rfl hlin, theta_cos_telescope]
  rw [mCoeffPP_of_le_neg_two (by omega), bCoeffPP_of_le_neg_two (by omega)]
  rw [show Kidx r + (M : ℤ) = -1 by omega, show Kidx r + ((M + 1 : ℕ) : ℤ) = 0 by push_cast; omega,
    show Kidx r + ((M + 2 : ℕ) : ℤ) = 1 by push_cast; omega,
    show (-1 : ℤ) + 1 = 0 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num]
  rw [mCoeffPP_zero_eq, bCoeffPP_zero_eq, mCoeffPP_neg_one_eq, bCoeffPP_neg_one_eq]
  rw [cos_theta_eq_rootA hr, cos_theta_eq_rootA hr, cos_theta_eq_rootA hr, cos_theta_eq_rootA hr,
    theta_eq_arcA (-1), theta_eq_arcA 0, theta_eq_arcA 1, sigma_neg_one_eq, sigma_zero_eq,
    sigma_one_eq]
  unfold c3F chordBlock c3L
  field_simp
  ring_nf

/-- **`0 ≤ c_{3,r}` for `0 < r < 1`.**

### Summary of Proof
`c_{3,r}` is the constant-term analogue of `c_{1,r}` and `c_{2,r}`, built from the double-primed
chord data `v''_k` of Equation `\ref{eq:mkpp}` (Equation 7).  Unlike `c_1` and `c_2` it is **not**
termwise non-negative: `v''_0 = log(0.611) < 0`.  The proof is by regimes of `K = Kidx r`
(`Kidx_eq_of`, `Kidx_le_of_le`, `le_Kidx_of_lt` with `σ_{-1}, σ_0, σ_1 = 2/7, 1/2, 5/7`):

* `r < 2/7`: `c3 r = log 1.546 · π/2 > 0` (`c3_eq_of_two_le_Kidx`);
* `2/7 ≤ r < 1/2`: `c3 r = c3G1 r ≥ 0.012` (`c3_eq_c3G1`, `c3G1_lower`);
* `1/2 ≤ r < 5/7`: `c3 r = c3G0 r ≥ 0.012` (`c3_eq_c3G0`, `c3G0_lower` — the tangent line at
  `r₁ = 1/√3` under the convex `c3G0`);
* `5/7 ≤ r < 1`: `c3 r = c3F r ≥ 0.012` (`c3_eq_c3F`, `c3F_lower` — concavity and the endpoint
  values `c3G0 (5/7)`, `c3F 1 ≥ 0.03`).

See the section header above for the design.  The proved lower bound `0.012` is `73%` of the true
minimum `0.016499` (at `r = 0.57762`, inside the `k = 0` regime).

### Lean Notes
The termwise strategy of `c1_nonneg`/`c2_nonneg` is not available: `c3`'s terms are not
individually non-negative, the `j = 0` term being about `-0.17` at `r = 1/2`.  A first-derivative
sign analysis of `c3G0`, `c3F` on a dozen subintervals with monotone envelopes would also work,
but is much longer; the tangent-line/concavity route needs the second derivatives, and those are
one `HasDerivAt` each with crude signs.  Its numerics reduce to one point (`r₁ = 1/√3`, chosen to
make `θ_{1/2}(r₁) = π/3` exact) plus `c3F 1`.

### References
tex: the `c_{3,r}` display after Equation `\ref{eq:thetak}` (Equation 8); the `v''_k` display
following Equation `\ref{eq:sigmak}` (Equation 4).  Numerics: `Code/verify_c3_tangent_route.py`
(exact rational re-check of every bound used here) and, independently,
`Code/indep_mpmath_tables_spotcheck.py` (`min c_{3,r} = 0.016499` at `r = 0.57762`,
`c_{3,1/2} = 0.098154`).

### Dependencies
**Depends on:** `c3_eq_of_two_le_Kidx`, `c3_eq_c3G1`, `c3_eq_c3G0`, `c3_eq_c3F`, `c3G1_lower`,
`c3G0_lower`, `c3F_lower`, `Kidx_eq_of`, `Kidx_le_of_le`, `le_Kidx_of_lt`.
**Used by:** `B3_nonneg`, `A6_nonneg`. -/
theorem c3_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 ≤ c3 r := by
  rcases lt_or_ge r (2 / 7) with h27 | h27
  · have hK : 2 ≤ Kidx r := le_Kidx_of_lt hr hr1 (by
      rw [show (2 : ℤ) - 1 = 1 by norm_num, sigma_one_eq]; linarith)
    rw [c3_eq_of_two_le_Kidx hr hK]
    have : 0 < Real.log 1.546 := Real.log_pos (by norm_num)
    positivity
  rcases lt_or_ge r (1 / 2) with h12 | h12
  · have hK : Kidx r = 1 := Kidx_eq_of hr hr1 (by rw [sigma_one_eq]; linarith)
      (by rw [show (1 : ℤ) - 1 = 0 by norm_num, sigma_zero_eq]; linarith)
    rw [c3_eq_c3G1 hr hK]
    linarith [c3G1_lower ⟨h27, h12.le⟩]
  rcases lt_or_ge r (5 / 7) with h57 | h57
  · have hK : Kidx r = 0 := Kidx_eq_of hr hr1 (by rw [sigma_zero_eq]; linarith)
      (by rw [show (0 : ℤ) - 1 = -1 by norm_num, sigma_neg_one_eq]; linarith)
    rw [c3_eq_c3G0 hr hK]
    linarith [c3G0_lower ⟨h12, h57.le⟩]
  · have hK : Kidx r ≤ -1 := Kidx_le_of_le hr1 (by rw [sigma_neg_one_eq]; linarith)
    rw [c3_eq_c3F hr hK]
    linarith [c3F_lower ⟨h57, hr1.le⟩]

/-- **`0 ≤ 2Φ(1) + c_{5,r}` for `0 < r < 1`** — the numerator of `B_{4,α,r}`.

### Summary of Proof
Both summands are separately non-negative, for elementary reasons:
* `Φ(s) = Σ_{n≥2} Λ(n)/(log n)²·n^{-s}` has every term `≥ 0` at real `s ≥ 1`, so `Φ(1).re ≥ 0`;
* `c_{5,r} = Φ(1+r).re + (2r/π)∫_0^1 log‖ζ(1+ru)‖·arcsin u du`, and for `u ∈ (0,1]` we have
  `1 + ru > 1`, where `ζ` exceeds `1` on the real axis, so `log‖ζ(1+ru)‖ > 0` and `arcsin u ≥ 0`;
  the integral is therefore non-negative, as is `Φ(1+r).re`.

### Lean Notes
The two inputs are `RectangularBounds.Phi_re_nonneg` (`0 ≤ (Φ σ).re` for real `σ ≥ 1`, used at
`σ = 1` and `σ = 1 + r`) and `Definitions.log_zeta_norm_pos` (`0 < log‖ζ(σ)‖` for real `σ > 1`),
the latter applied pointwise to the integrand on `(0,1]`; at `u = 0` the factor `arcsin 0 = 0`
kills the product outright, so `intervalIntegral.integral_nonneg` applies with no a.e. argument
and no integrability hypothesis. The casts `((1 + r·u : ℝ) : ℂ) = 1 + r·u` are discharged by
`push_cast`. Belongs in `RectangularBounds.lean` next to `B4`.

### References
tex: `\ref{thm:rectangularjensen}` (Theorem 24) for `B_{4,α,r}`, `\ref{prop:outside2}`
(Proposition 22) for the `2Φ(1)` normalisation, and the `c_{5,r}` display in
`\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `Phi`, `c5`, `RectangularBounds.Phi_re_nonneg`,
`Definitions.log_zeta_norm_pos`.
**Used by:** `B4_nonneg`. -/
theorem two_Phi_one_add_c5_nonneg {r : ℝ} (hr : 0 < r) (_hr1 : r < 1) :
    0 ≤ 2 * (Phi 1).re + c5 r := by
  have hPhi1 : 0 ≤ (Phi 1).re := by
    have := Phi_re_nonneg (σ := 1) le_rfl
    simpa using this
  have hPhi : 0 ≤ (Phi (1 + r : ℂ)).re := by
    have hcast : ((1 + r : ℝ) : ℂ) = (1 + r : ℂ) := by push_cast; ring
    have := Phi_re_nonneg (σ := 1 + r) (by linarith)
    rwa [hcast] at this
  have hint : 0 ≤ ∫ u in (0:ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro u hu
    obtain ⟨hu0, _⟩ := hu
    rcases eq_or_lt_of_le hu0 with h0 | hpos
    · subst h0; simp
    · apply mul_nonneg
      · have hcast : ((1 + r * u : ℝ) : ℂ) = (1 + r * u : ℂ) := by push_cast; ring
        have := log_zeta_norm_pos (σ := 1 + r * u) (by nlinarith)
        rw [hcast] at this
        exact this.le
      · exact Real.arcsin_nonneg.mpr hu0
  have hcoef : 0 ≤ 2 * r / Real.pi := by positivity
  unfold c5
  nlinarith [mul_nonneg hcoef hint]

/-- **`0 ≤ B_{1,α,r}` for `0 < α < r < 1`.**

### Summary of Proof
`B₁ = c_{1,r}/D_{r,α}` with `c1_nonneg` and `rectDenom_pos`.

### References
tex: `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B1`, `c1_nonneg`, `rectDenom_pos`.
**Used by:** `MainCorollary.C2JensenP_nonneg`, `MainTheorem.UJensen_add_EJensen_pos`. -/
theorem B1_nonneg {α r : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) : 0 ≤ B1 α r :=
  div_nonneg (c1_nonneg (hα.trans hαr) hr1) (rectDenom_pos hα hαr).le

/-- **`0 ≤ B_{2,α,r}` for `0 < α < r`.**

### Summary of Proof
`B₂ = c_{2,r}/(π D_{r,α})` with `c2_nonneg` and `rectDenom_pos`.

### References
tex: `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B2`, `c2_nonneg`, `rectDenom_pos`.
**Used by:** `MainCorollary.C2JensenP_antitoneOn`, `MainCorollary.C2JensenP_nonneg`,
`MainTheorem.UJensen_add_EJensen_pos`. -/
theorem B2_nonneg {α r : ℝ} (hα : 0 < α) (hαr : α < r) : 0 ≤ B2 α r :=
  div_nonneg (c2_nonneg (hα.trans hαr))
    (mul_pos Real.pi_pos (rectDenom_pos hα hαr)).le

/-- **`0 ≤ B_{3,α,r}` for `0 < α < r < 1`.**

### Summary of Proof
`B₃ = c_{3,r}/(π D_{r,α})` with `c3_nonneg` and `rectDenom_pos`.

### References
tex: `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B3`, `c3_nonneg`, `rectDenom_pos`.
**Used by:** `MainCorollary.C2JensenP_antitoneOn`, `MainCorollary.C2JensenP_nonneg`,
`MainTheorem.UJensen_add_EJensen_pos`. -/
theorem B3_nonneg {α r : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) : 0 ≤ B3 α r :=
  div_nonneg (c3_nonneg (hα.trans hαr) hr1)
    (mul_pos Real.pi_pos (rectDenom_pos hα hαr)).le

/-- **`0 ≤ B_{4,α,r}` for `0 < α < r < 1`.**

### Summary of Proof
`B₄ = (2Φ(1) + c_{5,r})/D_{r,α}` with `two_Phi_one_add_c5_nonneg` (above) and `rectDenom_pos`.

### References
tex: `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B4`, `two_Phi_one_add_c5_nonneg`, `rectDenom_pos`.
**Used by:** `MainCorollary.C2JensenQ_antitoneOn`, `MainCorollary.C2JensenQ_nonneg`,
`MainTheorem.UJensen_add_EJensen_pos`. -/
theorem B4_nonneg {α r : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) : 0 ≤ B4 α r :=
  div_nonneg (two_Phi_one_add_c5_nonneg (hα.trans hαr) hr1) (rectDenom_pos hα hαr).le

/-- **`0 ≤ A_{1,α,r}`** when `α < r` and the chord index `k` is the one pinned by
`σ_k ≤ 1-r ≤ σ_{k+1}`.

### Summary of Proof
`A₁ = (m_k(1-r) + b_k)/(2(r-α))`, and `m_k σ + b_k` is the chord interpolating `v_k` and
`v_{k+1}`, both non-negative (`vCoeff_nonneg`); `chord_vCoeff_nonneg` packages exactly that.

### Lean Notes
The chord-index hypotheses are the same `hk`/`hk'` that
`mainPositiveProportionCorollary_littlewood` already carries — without them `k` is arbitrary and
`A₁` is unconstrained.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{1,α,r}` display; Equation
`\ref{eq:mk}` (Equation 5) for the chord.

### Dependencies
**Depends on:** `A1`, `chord_vCoeff_nonneg`.
**Used by:** `MainCorollary.C2LittlewoodP_nonneg`, `MainTheorem.ULittlewood_add_ELittlewood_pos`.
-/
theorem A1_nonneg {α r : ℝ} {k : ℤ} (hαr : α < r) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r ≤ sigma (k + 1)) : 0 ≤ A1 α r k :=
  div_nonneg (chord_vCoeff_nonneg hk hk') (by linarith)

/-- **`A_{2,α,r} = 1/(2π(r-α))`, for every `k`.**

### Summary of Proof
`v'_k ≡ 1` (`vCoeffP`), so every slope `m'_k` vanishes and every intercept `b'_k` is `1`; the
chord is the constant `1` and `A₂ = 1/(2π(r-α))`.

### Lean Notes
Since `vCoeffP` is identically `1`, `A₂` is never zero (for `α < r`), and it is precisely the
`loglog t` term that rescues `P > 0` when `A₃ < 0`. The paper's Table `\ref{tab:littlewoodshort}`
(Table 7) does list `A₂ = 0` in its `r = 1/2` rows: there `1 - r = σ_0`, so the chord returns
`v₀'` itself, and the table is computed with `Remark \ref{rem:altcoefficients}` (Remark 7)'s
`v₀' = 0` rather than the main text's `1` — see `JensenScaleConstants`'s module docstring.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{2,α,r}` display; Equation `\ref{eq:mkp}`
(Equation 6).

### Dependencies
**Depends on:** `A2`, `mCoeffP`, `bCoeffP`, `vCoeffP`.
**Used by:** `A2_nonneg`, `neg_A2_le_A3`. -/
theorem A2_eq {α r : ℝ} {k : ℤ} : A2 α r k = 1 / (2 * Real.pi * (r - α)) := by
  have hm : mCoeffP k = 0 := by simp [mCoeffP, vCoeffP]
  have hb : bCoeffP k = 1 := by simp [bCoeffP, vCoeffP, mCoeffP]
  unfold A2
  rw [hm, hb]
  norm_num

/-- **`0 ≤ A_{2,α,r}` for `α < r`.**

### Summary of Proof
`A2_eq` plus positivity of `2π(r-α)`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** `A2_eq`.
**Used by:** `MainCorollary.C2LittlewoodP_antitoneOn`, `MainCorollary.C2LittlewoodP_nonneg`,
`MainTheorem.ULittlewood_add_ELittlewood_pos`. -/
theorem A2_nonneg {α r : ℝ} {k : ℤ} (hαr : α < r) : 0 ≤ A2 α r k := by
  rw [A2_eq]
  exact div_nonneg zero_le_one (by nlinarith [Real.pi_pos])

/-- **`0 ≤ A_{4,α,r}` for `0 < r < 1` and `α < r`.**

### Summary of Proof
`A₄ = c_{1,r}·r/(r-α)` with `c1_nonneg`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{4,α,r}` display.

### Dependencies
**Depends on:** `A4`, `c1_nonneg`.
**Used by:** `MainCorollary.C2LittlewoodQ_nonneg`, `MainTheorem.ULittlewood_add_ELittlewood_pos`.
-/
theorem A4_nonneg {α r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hαr : α < r) : 0 ≤ A4 α r :=
  div_nonneg (mul_nonneg (c1_nonneg hr hr1) hr.le) (by linarith)

/-- **`0 ≤ A_{5,α,r}` for `0 < r` and `α < r`.**

### Summary of Proof
`A₅ = (c_{2,r}r + πr)/(π(r-α))`; `c2_nonneg` makes the first summand non-negative and `πr > 0`
the second.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{5,α,r}` display.

### Dependencies
**Depends on:** `A5`, `c2_nonneg`.
**Used by:** `MainCorollary.C2LittlewoodQ_antitoneOn`, `MainCorollary.C2LittlewoodQ_nonneg`,
`MainTheorem.ULittlewood_add_ELittlewood_pos`. -/
theorem A5_nonneg {α r : ℝ} (hr : 0 < r) (hαr : α < r) : 0 ≤ A5 α r :=
  div_nonneg (by nlinarith [c2_nonneg hr, Real.pi_pos])
    (by nlinarith [Real.pi_pos])

/-- **`0 ≤ c_{4,r}` for `0 < r`** — Proposition `\ref{prop:integraloutside}` (Proposition 15)'s
circle constant for the integral outside the critical strip is non-negative.

### Summary of Proof
`c_{4,r} = (1/2)log‖ζ(1+r)‖ - (r/π)∫_0^1 Re(ζ'/ζ)(1+ru)·arcsin u du`. On the real axis right of
`1` we have `‖ζ‖ > 1` (`Definitions.log_zeta_norm_pos`), so the first term is positive, and
`Re(ζ'/ζ)(1+x) = -Σ Λ(n)n^{-1-x} < 0` (`Definitions.neg_logDeriv_zeta_re_pos`) while
`arcsin u ≥ 0`, so the integrand is non-positive on `(0,1]` (and `0` at `u = 0`, where
`arcsin 0 = 0`); the subtracted integral is therefore non-positive.

### Lean Notes
The `c₄` ingredient of `A6_nonneg`. The integral sign is obtained from
`intervalIntegral.integral_nonneg` applied to the negated integrand, with no integrability
hypothesis. Belongs in `JensenBounds.lean` next to `c4`.

### References
tex: `\ref{prop:integraloutside}` (Proposition 15), the `c_{4,r}` display; the sign is not stated
there.

### Dependencies
**Depends on:** `c4`, `Definitions.log_zeta_norm_pos`, `Definitions.neg_logDeriv_zeta_re_pos`.
**Used by:** `A6_nonneg`. -/
theorem c4_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ c4 r := by
  have hlog : 0 < Real.log ‖riemannZeta (1 + r : ℂ)‖ := by
    have hcast : ((1 + r : ℝ) : ℂ) = (1 + r : ℂ) := by push_cast; ring
    have := log_zeta_norm_pos (σ := 1 + r) (by linarith)
    rwa [hcast] at this
  have hint : (∫ u in (0:ℝ)..1,
      (deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re
        * Real.arcsin u) ≤ 0 := by
    have hneg : 0 ≤ ∫ u in (0:ℝ)..1,
        -((deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re
            * Real.arcsin u) := by
      apply intervalIntegral.integral_nonneg zero_le_one
      intro u hu
      obtain ⟨hu0, _⟩ := hu
      rcases eq_or_lt_of_le hu0 with h0 | hpos
      · subst h0; simp
      · have hcast : ((1 + r * u : ℝ) : ℂ) = (1 + r * u : ℂ) := by push_cast; ring
        have h := neg_logDeriv_zeta_re_pos (σ := 1 + r * u) (by nlinarith)
        rw [hcast, Complex.neg_re] at h
        have harc := Real.arcsin_nonneg.mpr hu0
        nlinarith
    rw [intervalIntegral.integral_neg] at hneg
    linarith
  have hpi := Real.pi_pos
  have hcoef : 0 ≤ r / Real.pi := by positivity
  unfold c4
  nlinarith [mul_nonneg hcoef (neg_nonneg.mpr hint)]

/-- **`0 ≤ A_{6,α,r}` for `0 < α < r < 1`.**

### Summary of Proof
Every one of `A₆`'s five contributions is non-negative for `0 < r < 1`:
* `c_{3,r}·r ≥ 0` by `c3_nonneg`;
* `c_{4,r}·πr ≥ 0` — `c_{4,r} = (1/2)log‖ζ(1+r)‖ - (r/π)∫_0^1 Re(ζ'/ζ)(1+ru)·arcsin u du`, and on
  the real axis right of `1` we have `‖ζ‖ > 1` (so the first term is positive) while
  `Re(ζ'/ζ)(1+x) = -Σ Λ(n)n^{-1-x} < 0` (so the subtracted integral is negative);
* `π log(29.388)·r > 0`;
* `Φ(1+ηr).re ≥ 0`, as in `two_Phi_one_add_c5_nonneg`;
* `(1+η)r·log‖ζ(1+ηr)‖ ≥ 0`, again because `‖ζ(σ)‖ > 1` for real `σ > 1` and `η > 0`
  (`eta_mem_Ioo`).

### Lean Notes
Assembles four sign facts: `c3_nonneg` (above), `c4_nonneg`, `RectangularBounds.Phi_re_nonneg` at
`σ = 1 + ηr ≥ 1`, and `Definitions.log_zeta_norm_pos` at `σ = 1 + ηr > 1` (with `η > 0` from
`Definitions.eta_mem_Ioo`), plus `log 29.388 > 0`. Belongs in `LittlewoodShort.lean` next to `A6`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{6,α,r}` display;
`\ref{lemma:littlewood-outerlog}` (Lemma 26) and Equation `\ref{eq:eta}` (Equation 15).
External: Leong, arXiv:2405.04869, for the `log 29.388`.

### Dependencies
**Depends on:** `A6`, `c3_nonneg`, `c4_nonneg`, `RectangularBounds.Phi_re_nonneg`,
`Definitions.log_zeta_norm_pos`, `Definitions.eta_mem_Ioo`.
**Used by:** `MainCorollary.C2LittlewoodQ_antitoneOn`, `MainCorollary.C2LittlewoodQ_nonneg`,
`MainTheorem.ULittlewood_add_ELittlewood_pos`. -/
theorem A6_nonneg {α r : ℝ} (hα : 0 < α) (hαr : α < r) (hr1 : r < 1) : 0 ≤ A6 α r := by
  have hr : 0 < r := hα.trans hαr
  have heta := eta_mem_Ioo
  have hηr : 0 < eta * r := mul_pos heta.1 hr
  have hc3 := c3_nonneg hr hr1
  have hc4 := c4_nonneg hr
  have hlog2 : 0 < Real.log 29.388 := Real.log_pos (by norm_num)
  have hPhi : 0 ≤ (Phi (1 + eta * r : ℂ)).re := by
    have hcast : ((1 + eta * r : ℝ) : ℂ) = (1 + eta * r : ℂ) := by push_cast; ring
    have := Phi_re_nonneg (σ := 1 + eta * r) (by linarith)
    rwa [hcast] at this
  have hlogz : 0 < Real.log ‖riemannZeta (1 + eta * r : ℂ)‖ := by
    have hcast : ((1 + eta * r : ℝ) : ℂ) = (1 + eta * r : ℂ) := by push_cast; ring
    have := log_zeta_norm_pos (σ := 1 + eta * r) (by linarith)
    rwa [hcast] at this
  have hpi := Real.pi_pos
  have hden : 0 < Real.pi * (r - α) := mul_pos hpi (by linarith)
  unfold A6
  apply div_nonneg _ hden.le
  have h1 : 0 ≤ c3 r * r := mul_nonneg hc3 hr.le
  have h2 : 0 ≤ c4 r * Real.pi * r := mul_nonneg (mul_nonneg hc4 hpi.le) hr.le
  have h3 : 0 ≤ Real.pi * Real.log 29.388 * r := mul_nonneg (mul_nonneg hpi.le hlog2.le) hr.le
  have h4 : 0 ≤ (1 + eta) * r * Real.log ‖riemannZeta (1 + eta * r : ℂ)‖ :=
    mul_nonneg (mul_nonneg (by linarith [heta.1]) hr.le) hlogz.le
  linarith

/-- **`log 0.611 ≤ log 1.546 - (log π)/2`** — the numeric inequality behind the `k < 0` branch of
`log_point_six_one_one_le_vCoeffPP`.

### Summary of Proof
Exponentiating, the claim is `0.611²·π ≤ 1.546²`, i.e. `0.3733·π ≤ 2.3901`, i.e. `π ≤ 6.40`;
`Real.pi_le_four` is far more than enough. The margin is comfortable: the true values are
`-0.4927` against `0.4358 - 0.5724 = -0.1367`.

### References
No tex counterpart — supports the `v''_k` lower bound.

### Dependencies
**Depends on:** `Real.pi_le_four`.
**Used by:** `log_point_six_one_one_le_vCoeffPP`. -/
theorem log_611_le_log_1546_sub_log_pi_div_two :
    Real.log 0.611 ≤ Real.log 1.546 - Real.log Real.pi / 2 := by
  have hπ := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have h1 : (0.611:ℝ) ^ 2 * Real.pi ≤ (1.546:ℝ) ^ 2 := by nlinarith
  have h2 : Real.log ((0.611:ℝ) ^ 2 * Real.pi) ≤ Real.log ((1.546:ℝ) ^ 2) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (ne_of_gt hπ0), Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

/-- **`log 0.611 ≤ v''_k` for every `k`** — the constant-term coefficients are bounded below by
their value at `k = 0`.

### Summary of Proof
Three cases, matching `vCoeffPP`'s two `if`s:
* `k > 0`: `v''_k = log 1.546 > log 0.611`;
* `k = 0`: equality;
* `k < 0`: `v''_k = log 1.546 + (σ_k - 1/2)log π` with `σ_k > 0` (`sigma_pos`) and `log π > 0`,
  so `v''_k > log 1.546 - (log π)/2 ≥ log 0.611` by
  `log_611_le_log_1546_sub_log_pi_div_two`.

### Lean Notes
The bound is **attained** at `k = 0`, so it cannot be improved. This is exactly the reason
`0 ≤ c3 r` is not termwise and `0 ≤ A₃` is false: `v''` dips below zero at the single index
`k = 0`, and (mildly) again as `k → -∞`, where the limit is `log 1.546 - (log π)/2 ≈ -0.1367`.
Confirmed numerically in `Code/verify_c3_and_chord_signs.py`, part (3).

**Belongs in `JensenScaleConstants.lean` next to `vCoeff_nonneg`.**

### References
tex: the `v''_k` display following Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `vCoeffPP`, `sigma_pos`, `log_611_le_log_1546_sub_log_pi_div_two`.
**Used by:** `log_point_six_one_one_le_chord_vCoeffPP`. -/
theorem log_point_six_one_one_le_vCoeffPP (k : ℤ) : Real.log 0.611 ≤ vCoeffPP k := by
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  unfold vCoeffPP
  split_ifs with h1 h2
  · exact Real.log_le_log (by norm_num) (by norm_num)
  · exact le_refl _
  · have hσ := sigma_pos k
    have hprod : 0 < sigma k * Real.log Real.pi := mul_pos hσ hlogpi
    have hexp : (sigma k - 1 / 2) * Real.log Real.pi
        = sigma k * Real.log Real.pi - Real.log Real.pi / 2 := by ring
    rw [hexp]
    linarith [log_611_le_log_1546_sub_log_pi_div_two]

/-- **A chord of `v''` stays above `log 0.611`**: for `σ_k ≤ σ ≤ σ_{k+1}`,
`log 0.611 ≤ m''_k σ + b''_k`.

### Summary of Proof
Writing `l = (σ - σ_k)/(σ_{k+1} - σ_k) ∈ [0,1]`, the chord value is the convex combination
`(1-l)v''_k + l·v''_{k+1}`, and both endpoints are `≥ log 0.611`
(`log_point_six_one_one_le_vCoeffPP`).

### Lean Notes
This is `chord_vCoeff_nonneg`'s argument with the bound `0` replaced by `log 0.611` and `vCoeff`
by `vCoeffPP`. A `chord_ge_of_endpoints_ge` generalisation in `JensenScaleConstants` would
subsume both; that is the right place for this lemma to end up.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `mCoeffPP`, `bCoeffPP`, `sigma_lt_succ`, `log_point_six_one_one_le_vCoeffPP`.
**Used by:** `neg_A2_le_A3`. -/
theorem log_point_six_one_one_le_chord_vCoeffPP {k : ℤ} {σ : ℝ} (hσ : sigma k ≤ σ)
    (hσ' : σ ≤ sigma (k + 1)) : Real.log 0.611 ≤ mCoeffPP k * σ + bCoeffPP k := by
  have hlt := sigma_lt_succ k
  have hd : (0:ℝ) < sigma (k + 1) - sigma k := by linarith
  have hne : sigma k - sigma (k + 1) ≠ 0 := by intro hc; linarith
  set l : ℝ := (σ - sigma k) / (sigma (k + 1) - sigma k) with hl_def
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
  have hl1 : l ≤ 1 := by rw [hl_def, div_le_one hd]; linarith
  have hkey : mCoeffPP k * σ + bCoeffPP k = (1 - l) * vCoeffPP k + l * vCoeffPP (k + 1) := by
    rw [hl_def]
    simp only [bCoeffPP, mCoeffPP]
    field_simp
    ring
  rw [hkey]
  have hvk := log_point_six_one_one_le_vCoeffPP k
  have hvk1 := log_point_six_one_one_le_vCoeffPP (k + 1)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - l)
      (by linarith : (0:ℝ) ≤ vCoeffPP k - Real.log 0.611),
    mul_nonneg hl0 (by linarith : (0:ℝ) ≤ vCoeffPP (k + 1) - Real.log 0.611)]

/-- **`-1 ≤ log 0.611`**, since `0.611 > e^{-1} = 0.3679`.

### Summary of Proof
`exp(-1)·exp 1 = 1` and `exp 1 > 2.718` (`Real.exp_one_gt_d9`) give `exp(-1) < 0.368 < 0.611`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Real.exp_one_gt_d9`.
**Used by:** `neg_A2_le_A3`. -/
theorem neg_one_le_log_point_six_one_one : (-1 : ℝ) ≤ Real.log 0.611 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 0.611)]
  have hexp : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos (-1), hexp]

/-- **`-A_{2,α,r} ≤ A_{3,α,r}`** — the sign fact that stands in for `0 ≤ A₃`, which is false.

### Summary of Proof
`A₂ = 1/(2π(r-α))` and `A₃ = (m''_k(1-r) + b''_k)/(2π(r-α))`, so with `α < r` the claim is
`-1 ≤ m''_k(1-r) + b''_k`: the chord of `v''` at `1-r` is at least `-1`. That holds because
`v''` itself is bounded below by `log(0.611) ≈ -0.4927` — its minimum, attained at `k = 0` — and
a chord of two values `≥ log(0.611)` stays `≥ log(0.611) > -1`. (For `k < 0`,
`v''_k = log(1.546) + (σ_k - 1/2)log π` with `σ_k ∈ (0, 1/2)`, so
`v''_k > log(1.546) - (log π)/2 ≈ -0.1367`; for `k > 0`, `v''_k = log(1.546) > 0`.)

### Lean Notes
It rests on two chord facts proved above: `log_point_six_one_one_le_vCoeffPP` (the `v''` lower
bound, attained at `k = 0`) and `log_point_six_one_one_le_chord_vCoeffPP` (convex combination).
Both **belong in `JensenScaleConstants.lean`** next to `vCoeff_nonneg`/`chord_vCoeff_nonneg` and
should be migrated; a `chord_ge_of_endpoints_ge` generalisation there would subsume both this and
`A1_nonneg`.

The slack is large — `log 0.611 ≈ -0.4927` against the needed `-1` — so the numeric step
(`neg_one_le_log_point_six_one_one`) is comfortable. Numerically confirmed by
`Code/verify_c3_and_chord_signs.py`, part (3): the minimum of `v''` over `|k| ≤ 60` is
exactly `log 0.611`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{2,α,r}` and `A_{3,α,r}` displays;
Equations `\ref{eq:mkp}`, `\ref{eq:mkpp}` (Equations 6, 7).

### Dependencies
**Depends on:** `A2_eq`, `A3`, `log_point_six_one_one_le_chord_vCoeffPP`,
`neg_one_le_log_point_six_one_one`.
**Used by:** `MainCorollary.C2LittlewoodP_antitoneOn`, `MainCorollary.C2LittlewoodP_nonneg`,
`MainTheorem.ULittlewood_add_ELittlewood_pos`. -/
theorem neg_A2_le_A3 {α r : ℝ} {k : ℤ} (_hα : 0 < α) (hαr : α < r) (_hr1 : r < 1)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r ≤ sigma (k + 1)) : -A2 α r k ≤ A3 α r k := by
  have hD : (0:ℝ) < 2 * Real.pi * (r - α) := by nlinarith [Real.pi_pos]
  have hchord := log_point_six_one_one_le_chord_vCoeffPP hk hk'
  have hN : (-1:ℝ) ≤ mCoeffPP k * (1 - r) + bCoeffPP k := by
    linarith [neg_one_le_log_point_six_one_one]
  rw [A2_eq]
  unfold A3
  rw [show -(1 / (2 * Real.pi * (r - α))) = (-1 : ℝ) / (2 * Real.pi * (r - α)) by ring]
  gcongr
