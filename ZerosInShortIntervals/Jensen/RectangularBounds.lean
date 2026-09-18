/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Hypotheses
import ZerosInShortIntervals.Jensen.JensenScaleConstants
import ZerosInShortIntervals.Jensen.JensenBounds
import ZerosInShortIntervals.Littlewood.LittlewoodMethod
import ZerosInShortIntervals.Background.LogDerivZetaLaurent

/-! # Rectangular regions (`\S \ref{sec:rectangularjensen}`, Section 2)

This file formalizes Section 2, "Rectangular intervals", of
`ZerosInShortIntervals.tex`, which bounds `N(T-h,T+h,α)` by integrating the circular
Jensen bounds of `ZerosInShortIntervals.Jensen.JensenBounds` along a vertical segment.
-/

open scoped ComplexOrder

/- The unproved inputs used below enter through the hypothesis classes: `LiteratureInputs` and
`NumericCertificates` from `ZerosInShortIntervals/Hypotheses.lean`, `BrentStirlingInputs` from
`Background/ExternalFacts.lean`, `LaurentCertificate` from
`Background/LogDerivZetaLaurent.lean`, and
`InterpolationCertificates`/`Hcompact2Certificates` from `Background/BackgroundZetaBounds.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [NumericCertificates] [LaurentCertificate]
  [InterpolationCertificates] [Hcompact2Certificates]

/-- **`D_{r,α} = 2r√(1-(α/r)²) - 2α arctan(√((r/α)²-1))`, the denominator of Proposition
`\ref{prop:jensenrectangle}` (Proposition 19) and of every `B_{i,α,r}` of Theorem
`\ref{thm:rectangularjensen}` (Theorem 24).**

### Summary of Proof
A definition. It is the area-like normalising factor produced by the Jensen argument on a
rectangle: the chord of the circle of radius `r` cut off at abscissa `α`, minus the
angular correction. Every `B_{i,α,r}` divides by it, and it is positive throughout the
range of interest (`rectDenom_pos`), which the source uses without remark.

### References
tex: Proposition `\ref{prop:jensenrectangle}` (Proposition 19), Theorem
`\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** none.
**Used by:** `B1`, `B2`, `B3`, `B4`, `C2Jensen`, `C2JensenQ`, `C2Jensen_num_mul`, `EJensen`,
`Ubound_jensen_eq_num_mul`, `jensenrectangle`, `mainJensenTight`, `rectDenom_eq_sqrt_form`,
`rectDenom_le_window`, `rectDenom_pos`, `rectangularjensen`, `rectangularjensen_tight`,
`window_integral_ge_rectDenom`. -/
noncomputable def rectDenom (r α : ℝ) : ℝ :=
  2 * r * Real.sqrt (1 - (α / r) ^ 2) - 2 * α * Real.arctan (Real.sqrt ((r / α) ^ 2 - 1))

/-! ### Positivity of `rectDenom`, and the window integral

`rectDenom r α = 2r√(1-(α/r)²) - 2α arctan(√((r/α)²-1))` is `2α(u - arctan u)` with
`u = √((r/α)²-1) = α̂_r/α`, hence positive whenever `0 < α < r` — the source does not remark on
this, but every use divides by it. -/

/-- **`arctan x < x` for `x > 0` (from `Real.lt_tan` at `y = arctan x`).**

### Summary of Proof
From `Real.lt_tan` applied at `y = arctan x`: since `tan (arctan x) = x` and `tan y > y`
for `y ∈ (0, π/2)`, we get `arctan x < x` for `x > 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `rectDenom_pos`. -/
theorem arctan_lt_self {x : ℝ} (hx : 0 < x) : Real.arctan x < x := by
  have h1 : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  have h2 : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have := Real.lt_tan h1 h2
  rwa [Real.tan_arctan] at this

/-- **`0 < rectDenom r α` for `0 < α < r`.**

### Summary of Proof
Both terms simplify through `√(r²-α²) = α̂_r`: writing `u = √((r/α)²-1) = α̂_r/α` gives
`rectDenom r α = 2αu - 2α arctan u = 2α(u - arctan u)`, positive because `arctan u < u` for
`u > 0` (`arctan_lt_self`). The source does not remark on this, but every use of Proposition
`\ref{prop:jensenrectangle}` (Proposition 19) divides by it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arctan_lt_self`, `rectDenom`.
**Used by:** `jensenrectangle`, `rectangularjensen`, `rectangularjensen_tight`; and downstream
`ConstantSigns.B1_nonneg`–`B4_nonneg`, `MainTheorem.UJensen_add_EJensen_pos`/`mainJensen`,
`MainTheoremTight.mainJensenTight`, and in `MainCorollary` `C2JensenQ_nonneg`,
`C2JensenQ_antitoneOn`, `C2Jensen_antitone_h`, `C2Jensen_antitone_t`. -/
theorem rectDenom_pos {r α : ℝ} (hα : 0 < α) (hrα : α < r) : 0 < rectDenom r α := by
  have hr : 0 < r := hα.trans hrα
  have hra : 1 < (r/α)^2 := by
    have h : 1 < r/α := (one_lt_div hα).mpr hrα
    nlinarith
  set u : ℝ := Real.sqrt ((r/α)^2 - 1) with hu_def
  have hu : 0 < u := Real.sqrt_pos.mpr (by linarith)
  have e1 : r * Real.sqrt (1 - (α/r)^2) = Real.sqrt (r^2 - α^2) := by
    rw [show r^2 - α^2 = r^2 * (1 - (α/r)^2) by field_simp,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have e2 : α * u = Real.sqrt (r^2 - α^2) := by
    rw [hu_def, show r^2 - α^2 = α^2 * ((r/α)^2 - 1) by field_simp,
      Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
  rw [rectDenom, ← hu_def]
  have h3 := arctan_lt_self hu
  nlinarith [e1, e2]

/-! ### Step (iii) of `jensenrectangle`: the per-zero window integral

A zero `ρ = β + iγ` at distance `b = 1 - β` from the line `Re s = 1` sits inside the disc of
radius `r` about `1 + i(T+x)` exactly when `b² + (γ - T - x)² ≤ r²`, i.e. for `x` in an interval
of half-width `√(r² - b²)` about `γ - T`. Over that interval its contribution to the integrated
Jensen defect is

  `W(r,b) := ∫_{-√(r²-b²)}^{√(r²-b²)} (log r - ½ log (b² + y²)) dy`,

and Proposition `\ref{prop:jensenrectangle}` (Proposition 19) asserts `W(r,b) ≥ rectDenom r α`
whenever `b ≤ α`. The three lemmas below separate that assertion into (a) an algebraic identity,
(b) one integral evaluation, and (c) one monotonicity fact, and then assemble them. All three are
verified numerically to 40 digits in `Code/verify_rectDenom_window.py`, where (a) holds to the
last bit.
-/

/-- **`rectDenom` in `√(r²-α²)` form: `rectDenom r α = 2√(r²-α²) - 2α arctan(√(r²-α²)/α)`.**

### Summary of Proof
Pure algebra on the two square roots, reusing the rewrites inside `rectDenom_pos`:
`r√(1-(α/r)²) = √(r²-α²)` (pull `r²` out of the root) and `√((r/α)²-1) = √(r²-α²)/α`
(pull `α²` out). Verified exactly — residual `0` at 40 digits — in
`Code/verify_rectDenom_window.py`, check (B).

This is the shape in which `rectDenom` actually arises from the per-zero integral
(`integral_log_disc_chord_eq`), so having it as a rewrite avoids re-deriving the roots at
every use.

### References
tex: Proposition `\ref{prop:jensenrectangle}` (Proposition 19); `D_{r,α}` is the denominator
there.

### Dependencies
**Depends on:** `rectDenom`.
**Used by:** `rectDenom_le_window`. -/
theorem rectDenom_eq_sqrt_form {r α : ℝ} (hα : 0 < α) (hrα : α < r) :
    rectDenom r α
      = 2 * Real.sqrt (r ^ 2 - α ^ 2)
          - 2 * α * Real.arctan (Real.sqrt (r ^ 2 - α ^ 2) / α) := by
  have hr : 0 < r := hα.trans hrα
  have hra : 1 < (r / α) ^ 2 := by
    have h : 1 < r / α := (one_lt_div hα).mpr hrα
    nlinarith
  have e1 : r * Real.sqrt (1 - (α / r) ^ 2) = Real.sqrt (r ^ 2 - α ^ 2) := by
    rw [show r ^ 2 - α ^ 2 = r ^ 2 * (1 - (α / r) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have e2 : Real.sqrt ((r / α) ^ 2 - 1) = Real.sqrt (r ^ 2 - α ^ 2) / α := by
    rw [show r ^ 2 - α ^ 2 = α ^ 2 * ((r / α) ^ 2 - 1) by field_simp,
      Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    field_simp
  rw [rectDenom, e2, ← e1]
  ring

/-- **The per-zero window integral in closed form:
`∫_{-c}^{c} (log r - ½ log(b² + y²)) dy = 2c - 2b arctan(c/b)` for `c = √(r²-b²)`.**

### Summary of Proof
An antiderivative of `log(b² + y²)` is `y log(b² + y²) - 2y + 2b arctan(y/b)`. Since the
integrand is even, the integral over `[-c,c]` is twice the integral over `[0,c]`, and using
`b² + c² = r²` the `log` terms cancel against `∫_{-c}^{c} log r dy = 2c log r`:

  `2c log r - ½(4c log r - 4c + 4b arctan(c/b)) = 2c - 2b arctan(c/b)`.

There is no improper endpoint: `b > 0` keeps `b² + y² ≥ b² > 0` throughout, so the integrand is
continuous on the closed interval and Lean's junk value `log 0 = 0` never arises.

Verified to 40 digits against adaptive quadrature in `Code/verify_rectDenom_window.py`,
check (A) (worst residual `1.8×10⁻⁴⁰`).

### Lean Notes
Proved by `intervalIntegral.integral_eq_sub_of_hasDerivAt` with the antiderivative
`F y = y log r - ½(y log(b²+y²) - 2y + 2b arctan(y/b))`, whose `HasDerivAt` holds on **all** of
`uIcc (-c) c` (not merely the open interval), because `b² + y² ≥ b² > 0` throughout — so the
plain FTC lemma suffices and the `..._of_tendsto` variant is not needed. The derivative of the
bracket is `log(b²+y²) + 2y²/(b²+y²) - 2 + 2b²/(b²+y²)`, and the three non-`log` terms cancel
because `2y² + 2b² = 2(b²+y²)`; `field_simp; ring` closes that after rewriting
`1 + (y/b)² = (b²+y²)/b²` (needed to clear `arctan`'s derivative denominator).

At the endpoints, `b² + (±c)² = r²` and `log(r²) = 2 log r` make the `2c log r` terms cancel,
leaving `2c - 2b arctan(c/b)`; `Real.arctan_neg` supplies the odd symmetry at `-c`.

### References
tex: the displayed evaluation inside the proof of Proposition `\ref{prop:jensenrectangle}`
(Proposition 19) — "a closed form for `∫ log r - ½log(α²+t²) dt`, evaluated via `arctan`".

### Dependencies
**Depends on:** none.
**Used by:** `rectDenom_le_window`. -/
theorem integral_log_disc_chord_eq {r b : ℝ} (hb : 0 < b) (hbr : b < r) :
    (∫ y in (-Real.sqrt (r ^ 2 - b ^ 2))..(Real.sqrt (r ^ 2 - b ^ 2)),
        (Real.log r - (1 / 2) * Real.log (b ^ 2 + y ^ 2)))
      = 2 * Real.sqrt (r ^ 2 - b ^ 2)
          - 2 * b * Real.arctan (Real.sqrt (r ^ 2 - b ^ 2) / b) := by
  have hr : 0 < r := hb.trans hbr
  have hbne : b ≠ 0 := ne_of_gt hb
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have hpos : ∀ y : ℝ, (0 : ℝ) < b ^ 2 + y ^ 2 := fun y => by nlinarith [sq_nonneg y]
  set c : ℝ := Real.sqrt (r ^ 2 - b ^ 2) with hc_def
  have hcsq : c ^ 2 = r ^ 2 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  set G : ℝ → ℝ := fun y => Real.log r - 1 / 2 * Real.log (b ^ 2 + y ^ 2) with hG_def
  set F : ℝ → ℝ := fun y =>
    y * Real.log r
      - 1 / 2 * (y * Real.log (b ^ 2 + y ^ 2) - 2 * y + 2 * b * Real.arctan (y / b)) with hF_def
  have hderiv : ∀ y ∈ Set.uIcc (-c) c, HasDerivAt F (G y) y := by
    intro y _
    have hne : (b ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (hpos y)
    have d1 : HasDerivAt (fun y : ℝ => y * Real.log r) (Real.log r) y := by
      simpa using (hasDerivAt_id y).mul_const (Real.log r)
    have dq : HasDerivAt (fun y : ℝ => b ^ 2 + y ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (b ^ 2)
    have dlog : HasDerivAt (fun y : ℝ => Real.log (b ^ 2 + y ^ 2))
        (2 * y / (b ^ 2 + y ^ 2)) y := dq.log hne
    have darc : HasDerivAt (fun y : ℝ => Real.arctan (y / b))
        (1 / (1 + (y / b) ^ 2) * (1 / b)) y := by
      have h1 : HasDerivAt (fun y : ℝ => y / b) (1 / b) y := by
        simpa using (hasDerivAt_id y).div_const b
      exact (Real.hasDerivAt_arctan (y / b)).comp y h1
    have e1 : HasDerivAt (fun y : ℝ => y * Real.log (b ^ 2 + y ^ 2))
        (1 * Real.log (b ^ 2 + y ^ 2) + y * (2 * y / (b ^ 2 + y ^ 2))) y :=
      (hasDerivAt_id y).mul dlog
    have e2 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
      simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
    have e3 : HasDerivAt (fun y : ℝ => 2 * b * Real.arctan (y / b))
        (2 * b * (1 / (1 + (y / b) ^ 2) * (1 / b))) y := darc.const_mul (2 * b)
    have dinner := (e1.sub e2).add e3
    have dF := d1.sub (dinner.const_mul (1 / 2 : ℝ))
    rw [hF_def]
    refine dF.congr_deriv ?_
    rw [hG_def]
    simp only
    rw [show (1 : ℝ) + (y / b) ^ 2 = (b ^ 2 + y ^ 2) / b ^ 2 by field_simp]
    field_simp
    ring
  have hcont : ContinuousOn G (Set.uIcc (-c) c) := by
    rw [hG_def]
    refine continuousOn_const.sub (continuousOn_const.mul (ContinuousOn.log ?_ ?_))
    · exact continuousOn_const.add (continuous_pow 2).continuousOn
    · intro y _; exact ne_of_gt (hpos y)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hFTC, hF_def]
  simp only
  have hsum : b ^ 2 + c ^ 2 = r ^ 2 := by rw [hcsq]; ring
  have hlog2 : Real.log (b ^ 2 + c ^ 2) = 2 * Real.log r := by
    rw [hsum, show (r : ℝ) ^ 2 = r ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hnegsq : b ^ 2 + (-c) ^ 2 = b ^ 2 + c ^ 2 := by ring
  have harc : Real.arctan (-c / b) = -Real.arctan (c / b) := by
    rw [show (-c) / b = -(c / b) by ring, Real.arctan_neg]
  rw [hnegsq, hlog2, harc]
  ring

/-! **A monotonicity fact deliberately *not* stated as a lemma.** One naturally reaches for:
`b ↦ 2√(r²-b²) - 2b arctan(√(r²-b²)/b)` is strictly antitone on `(0,r)`, so a zero closer to the
line than `α` contributes more than one at distance exactly `α`. It is true, with a clean proof:
writing `c(b) = √(r²-b²)` (so `c' = -b/c`) and `g(b) = 2c - 2b arctan(c/b)`,

  `d/db arctan(c/b) = (1/(1+(c/b)²))·(c'b - c)/b² = (c'b - c)/(b²+c²) = (c'b - c)/r² = -1/c`,

whence `g'(b) = 2c' - 2 arctan(c/b) + 2b/c = -2b/c - 2 arctan(c/b) + 2b/c = -2 arctan(c/b) < 0`
— the derivative is exactly minus twice the arctan already in `g`. (Verified to 40 digits,
residual `0`, as check (C) of `Code/verify_rectDenom_window.py`.)

But it is the wrong tool here, and stating it would have been a trap. It compares the integrals
over the two zeros' *own* disc-chords, and for `b ≤ α` the chord `[-√(r²-b²), √(r²-b²)]` is the
**wider** interval — wider than the `[-α̂_r, α̂_r]` window that `jensenrectangle` actually
integrates over. Step (ii) cannot supply that extra range. Over the fixed window the comparison
is instead pointwise and elementary (`log` is monotone), which is how `rectDenom_le_window` below
proves it, needing only the `b = α` instance of `integral_log_disc_chord_eq`. -/

/-- **Step (iii) of `jensenrectangle`: a zero at distance `b ≤ α` from the line contributes at
least `rectDenom r α`.**

### Summary of Proof
The window here is the **fixed** one `[-α̂_r, α̂_r]` that `jensenrectangle` actually integrates
over, *not* the zero's own disc-chord `[-√(r²-b²), √(r²-b²)]` — which for `b ≤ α` is the wider
interval, and so is not available to step (ii). Over a fixed window the monotonicity is
pointwise and elementary: `b² + y² ≤ α² + y²` with both sides positive, so
`-½log(b²+y²) ≥ -½log(α²+y²)`, and `intervalIntegral.integral_mono_on` integrates it. The
resulting lower bound `∫_{-α̂}^{α̂}(log r - ½log(α²+y²))dy` is exactly
`integral_log_disc_chord_eq` at `b := α`, since `hatAlpha r α = √(r²-α²)` definitionally, and
that closed form is `rectDenom r α` by `rectDenom_eq_sqrt_form`.

So the antitonicity of `b ↦ 2√(r²-b²) - 2b arctan(√(r²-b²)/b)` discussed in the section comment
above (never stated as a lemma) is **not** needed for this: only the `b = α` instance of
`integral_log_disc_chord_eq` is on the critical path.

This is the *uniform* lower bound that step (ii) of `jensenrectangle` needs — uniform in the
zero, depending only on `r` and `α` — which is precisely what makes the interchange with the sum
over zeros useful.

### References
tex: Proposition `\ref{prop:jensenrectangle}` (Proposition 19).

### Dependencies
**Depends on:** `hatAlpha`, `integral_log_disc_chord_eq`, `rectDenom`, `rectDenom_eq_sqrt_form`.
**Used by:** `window_integral_ge_rectDenom` (step (iii) of `jensenrectangle`). -/
theorem rectDenom_le_window {r α b : ℝ} (hb : 0 < b) (hbα : b ≤ α) (hαr : α < r) :
    rectDenom r α
      ≤ ∫ y in (-hatAlpha r α)..(hatAlpha r α),
          (Real.log r - (1 / 2) * Real.log (b ^ 2 + y ^ 2)) := by
  have hα : 0 < α := lt_of_lt_of_le hb hbα
  have hr : 0 < r := hα.trans hαr
  have hAeq : hatAlpha r α = Real.sqrt (r ^ 2 - α ^ 2) := rfl
  -- continuity of `y ↦ log r - ½ log (c² + y²)` for any `c > 0`, on any interval
  have hcont : ∀ c : ℝ, 0 < c → ContinuousOn
      (fun y : ℝ => Real.log r - (1 / 2) * Real.log (c ^ 2 + y ^ 2))
      (Set.uIcc (-Real.sqrt (r ^ 2 - α ^ 2)) (Real.sqrt (r ^ 2 - α ^ 2))) := by
    intro c hc
    refine continuousOn_const.sub (continuousOn_const.mul (ContinuousOn.log ?_ ?_))
    · exact continuousOn_const.add ((continuous_pow 2).continuousOn)
    · intro y _
      have hc2 : 0 < c ^ 2 := pow_pos hc 2
      exact ne_of_gt (by nlinarith [sq_nonneg y])
  -- the `b = α` instance of the closed form *is* `rectDenom r α`
  have hbase : rectDenom r α
      = ∫ y in (-Real.sqrt (r ^ 2 - α ^ 2))..(Real.sqrt (r ^ 2 - α ^ 2)),
          (Real.log r - (1 / 2) * Real.log (α ^ 2 + y ^ 2)) :=
    (rectDenom_eq_sqrt_form hα hαr).trans (integral_log_disc_chord_eq hα hαr).symm
  rw [hAeq, hbase]
  refine intervalIntegral.integral_mono_on
    (neg_le_self (Real.sqrt_nonneg _))
    ((hcont α hα).intervalIntegrable) ((hcont b hb).intervalIntegrable) ?_
  intro y _
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have h1 : (0 : ℝ) < b ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  have h2 : b ^ 2 + y ^ 2 ≤ α ^ 2 + y ^ 2 := by nlinarith
  linarith [Real.log_le_log h1 h2]

/-- **The window integral of Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s bound.** For
`A, B ≥ 0`, `0 < a` and `T - a > 1`,
`∫_{T-a}^{T+a}(A log t + B log log t + C + 3/t)dt ≤ 2a(A log T + B log log T + C) + 6a/(T-a)`.

### Summary of Proof
Integrate term by term over the symmetric window `[T-a, T+a]`. Concavity of `log` and of
`log ∘ log` kills the first-order error there (`LittlewoodMethod.integral_log_le_window`,
`integral_loglog_le_window` — this is where `0 ≤ A` and `0 ≤ B` are needed, since concavity
points the right way only for nonnegative coefficients), and the constant integrates exactly to
`2aC`. The whole error budget goes to the `3/t` tail, which evaluates to `3 log((T+a)/(T-a))` and
is bounded via `log x ≤ x - 1` by `3·(2a/(T-a)) = 6a/(T-a)`.

### References
tex: Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `integral_log_le_window`, `integral_loglog_le_window`.
**Used by:** `rectangularjensen`. -/
theorem integral_window_bound {T a A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hTa : 1 < T - a) :
    (∫ t in (T-a)..(T+a), (A * Real.log t + B * Real.log (Real.log t) + C + 3/t))
      ≤ 2*a*(A * Real.log T + B * Real.log (Real.log T) + C) + 6*a/(T-a) := by
  have hpi := Real.pi_pos
  have hT0 : (0:ℝ) < T - a := by linarith
  have hTp : (0:ℝ) < T + a := by linarith
  have hab : T - a ≤ T + a := by linarith
  have hcont : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.uIcc (T-a) (T+a)) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.log
    · apply ContinuousOn.log continuousOn_id
      intro t ht; simp only [id_eq]; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hi1 : IntervalIntegrable (fun t : ℝ => A * Real.log t) MeasureTheory.volume (T-a) (T+a) :=
    intervalIntegral.intervalIntegrable_log'.const_mul _
  have hi2 : IntervalIntegrable (fun t : ℝ => B * Real.log (Real.log t))
      MeasureTheory.volume (T-a) (T+a) := (hcont.intervalIntegrable).const_mul _
  have hi4 : IntervalIntegrable (fun t : ℝ => 3/t) MeasureTheory.volume (T-a) (T+a) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  rw [intervalIntegral.integral_add (((hi1.add hi2).add intervalIntegrable_const)) hi4,
    intervalIntegral.integral_add (hi1.add hi2) intervalIntegrable_const,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  have h1 := integral_log_le_window (T := T) (h := a) ha.le hT0
  have h2 := integral_loglog_le_window (T := T) (h := a) ha.le hTa
  have h4 : (∫ t in (T-a)..(T+a), 3/t)
      = 3 * (Real.log (T+a) - Real.log (T-a)) := by
    have heq : (fun t : ℝ => 3/t) = fun t : ℝ => (3:ℝ) * t⁻¹ := by
      funext t; field_simp
    rw [heq, intervalIntegral.integral_const_mul, integral_inv_of_pos hT0 hTp,
      Real.log_div (ne_of_gt hTp) (ne_of_gt hT0)]
  have hlog : Real.log (T+a) - Real.log (T-a) ≤ 2*a/(T-a) := by
    have h := Real.log_le_sub_one_of_pos (x := (T+a)/(T-a)) (by positivity)
    rw [Real.log_div (ne_of_gt hTp) (ne_of_gt hT0)] at h
    have he : (T+a)/(T-a) - 1 = 2*a/(T-a) := by field_simp; ring
    linarith [he ▸ h]
  have hlogpi : 3 * (Real.log (T+a) - Real.log (T-a)) ≤ 6*a/(T-a) := by
    have he : (3:ℝ) * (2*a/(T-a)) = 6*a/(T-a) := by ring
    linarith [he ▸ (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 3))]
  rw [h4]
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB, hlogpi]

/-- **The window integral of `JensenBounds.jensen_easy_tight`'s bound.** For `A, B ≥ 0` and
`2 < T - a`, `∫_{T-a}^{T+a}(A log t + B log log t + C + (5/(6(t-1)) + 1/(t-1)² +
1158/(16(t-1)²log(t-1))))dt ≤ 2a(A log T + B log log T + C) + (5a/(3(T-a-1)) + 2a/(T-a-1)² +
1158a/(8(T-a-1)²log(T-a-1)))`: as in `integral_window_bound`, concavity kills the `log`/`log log`
first-order error, and the whole budget goes to the tail.**

### Summary of Proof
The `5/(6(t-1))` piece is bounded exactly
as `integral_window_bound`'s `3/t` piece was (`log((T+a-1)/(T-a-1)) ≤ 2a/(T-a-1)`, shifted by `-1`
via `intervalIntegral.integral_comp_sub_right`); the remaining `1/(t-1)² + 1158/(16(t-1)²log(t-1))`
is exactly half of `LittlewoodMethod.integral_tight_tail_lt_window`'s integrand evaluated at `t-1`,
so that lemma (applied at `T-1`) is reused directly rather than redone.

### References
No tex counterpart.

### Dependencies
**Depends on:** `integral_log_le_window`, `integral_loglog_le_window`,
`integral_tight_tail_lt_window`.
**Used by:** `rectangularjensen_tight`. -/
theorem integral_window_bound_tight {T a A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hTa : (2 : ℝ) < T - a) :
    (∫ t in (T-a)..(T+a), (A * Real.log t + B * Real.log (Real.log t) + C
        + (5 / (6 * (t - 1)) + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1))))))
      ≤ 2 * a * (A * Real.log T + B * Real.log (Real.log T) + C)
        + (5 * a / (3 * (T - a - 1))
            + (2 * a / (T - a - 1) ^ 2
                + 1158 * a / (8 * (T - a - 1) ^ 2 * Real.log (T - a - 1)))) := by
  have hpi := Real.pi_pos
  have hT0 : (0:ℝ) < T - a := by linarith
  have hTp : (0:ℝ) < T + a := by linarith
  have hab : T - a ≤ T + a := by linarith
  have hTa1 : (1:ℝ) < T - a - 1 := by linarith
  have hTp1 : (0:ℝ) < T + a - 1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.uIcc (T-a) (T+a)) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.log
    · apply ContinuousOn.log continuousOn_id
      intro t ht; simp only [id_eq]; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hi1 : IntervalIntegrable (fun t : ℝ => A * Real.log t) MeasureTheory.volume (T-a) (T+a) :=
    intervalIntegral.intervalIntegrable_log'.const_mul _
  have hi2 : IntervalIntegrable (fun t : ℝ => B * Real.log (Real.log t))
      MeasureTheory.volume (T-a) (T+a) := (hcont.intervalIntegrable).const_mul _
  have hiPa : IntervalIntegrable (fun t : ℝ => (5:ℝ) / (6 * (t - 1)))
      MeasureTheory.volume (T-a) (T+a) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    have : (0:ℝ) < t - 1 := by linarith [ht.1]
    positivity
  have hiPbc : IntervalIntegrable
      (fun t : ℝ => (1:ℝ) / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1)))
      MeasureTheory.volume (T-a) (T+a) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.add
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      have : (0:ℝ) < t - 1 := by linarith [ht.1]
      positivity
    · apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.mul (by fun_prop)
        apply ContinuousOn.log (by fun_prop)
        intro t ht; exact ne_of_gt (by linarith [ht.1] : (0:ℝ) < t - 1)
      · intro t ht
        have h1 : (1:ℝ) < t - 1 := by linarith [ht.1]
        have h2 : (0:ℝ) < Real.log (t - 1) := Real.log_pos h1
        positivity
  rw [intervalIntegral.integral_add ((hi1.add hi2).add intervalIntegrable_const)
      (hiPa.add hiPbc),
    intervalIntegral.integral_add (hi1.add hi2) intervalIntegrable_const,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,
    intervalIntegral.integral_add hiPa hiPbc]
  have h1 := integral_log_le_window (T := T) (h := a) ha.le hT0
  have h2 := integral_loglog_le_window (T := T) (h := a) ha.le (by linarith : (1:ℝ) < T - a)
  -- piece Pa: shift by `-1` and reuse `integral_inv_of_pos`.
  have hPaShift : (∫ t in (T-a)..(T+a), (5:ℝ) / (6 * (t - 1)))
      = ∫ x in (T-a-1)..(T+a-1), (5:ℝ) / (6 * x) :=
    intervalIntegral.integral_comp_sub_right (f := fun x : ℝ => (5:ℝ) / (6 * x)) 1
  have hPaVal : (∫ x in (T-a-1)..(T+a-1), (5:ℝ) / (6 * x))
      = (5/6) * Real.log ((T+a-1)/(T-a-1)) := by
    have heq : (fun x : ℝ => (5:ℝ) / (6 * x)) = fun x : ℝ => (5/6:ℝ) * x⁻¹ := by
      funext x; ring
    rw [heq, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by linarith : (0:ℝ) < T - a - 1) hTp1]
  have hboundPa : (∫ t in (T-a)..(T+a), (5:ℝ) / (6 * (t - 1))) ≤ 5 * a / (3 * (T - a - 1)) := by
    rw [hPaShift, hPaVal]
    have hlog : Real.log ((T+a-1)/(T-a-1)) ≤ 2 * a / (T - a - 1) := by
      have h := Real.log_le_sub_one_of_pos (x := (T+a-1)/(T-a-1)) (by positivity)
      have he : (T+a-1)/(T-a-1) - 1 = 2 * a / (T - a - 1) := by field_simp; ring
      linarith [he ▸ h]
    have hne : (T - a - 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have he2 : (5/6:ℝ) * (2 * a / (T - a - 1)) = 5 * a / (3 * (T - a - 1)) := by
      field_simp; ring
    linarith [he2 ▸ (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 5/6))]
  -- piece Pb+Pc: shift by `-1` and reuse `LittlewoodMethod.integral_tight_tail_lt_window`
  -- (exactly half its integrand, evaluated at `T - 1`).
  have hPbcShift : (∫ t in (T-a)..(T+a),
        ((1:ℝ) / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1))))
      = ∫ x in (T-a-1)..(T+a-1), ((1:ℝ) / x ^ 2 + 1158 / (16 * x ^ 2 * Real.log x)) :=
    intervalIntegral.integral_comp_sub_right
      (f := fun x : ℝ => (1:ℝ) / x ^ 2 + 1158 / (16 * x ^ 2 * Real.log x)) 1
  have hboundPbc : (∫ t in (T-a)..(T+a),
        ((1:ℝ) / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1))))
      ≤ 2 * a / (T - a - 1) ^ 2 + 1158 * a / (8 * (T - a - 1) ^ 2 * Real.log (T - a - 1)) := by
    rw [hPbcShift]
    have hhalf : (fun x : ℝ => (1:ℝ) / x ^ 2 + 1158 / (16 * x ^ 2 * Real.log x))
        = fun x : ℝ => (1/2:ℝ) * (2 / x ^ 2 + 1158 / (8 * x ^ 2 * Real.log x)) := by
      funext x; ring
    rw [hhalf, intervalIntegral.integral_const_mul]
    have htail := integral_tight_tail_lt_window (T := T - 1) (h := a) ha
      (show (1:ℝ) < T - 1 - a by linarith)
    have e1 : T - 1 - a = T - a - 1 := by ring
    have e2 : T - 1 + a = T + a - 1 := by ring
    rw [e1, e2] at htail
    have hd0 : (T - a - 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hlog0 : Real.log (T - a - 1) ≠ 0 := ne_of_gt (Real.log_pos hTa1)
    have hEqRHS : (4 * a / (T - a - 1) ^ 2
          + 1158 * a / (4 * (T - a - 1) ^ 2 * Real.log (T - a - 1)))
        = 2 * (2 * a / (T - a - 1) ^ 2
            + 1158 * a / (8 * (T - a - 1) ^ 2 * Real.log (T - a - 1))) := by
      field_simp; ring
    rw [hEqRHS] at htail
    linarith [htail]
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB,
    hboundPa, hboundPbc]

/-! ### Steps (i) and (ii) of `jensenrectangle`: Jensen's formula and the finite sum over zeros

Mathlib's `AnalyticOnNhd.circleAverage_log_norm` is Jensen's formula for an analytic function on a
closed disc with `f(centre) ≠ 0`. Applied to `ζ` on the disc of radius `r` about `1 + i(T+x)`
(which avoids the pole since `|T+x| > r`, and whose centre is not a zero since `Re = 1`), it
writes the Jensen defect as `∑ᶠ u, divisor ζ (closedBall c r) u · log(r/‖c-u‖)`. The lemmas
below turn that `finsum` into a sum over one **fixed finite set** — the zeros of `ζ` in a compact
rectangle `K` containing every disc of the sweep, finite by
`IsCompact.inter_riemannZetaZeros_finite` — with each zero weighted by `max 0 (log(r/‖c-u‖))`.
That makes the exchange of `∫dx` with the sum a finite-sum identity
(`intervalIntegral.integral_finsetSum`), so no Fubini/Tonelli argument is needed, and zeros on a
boundary circle contribute `log 1 = 0` on either reading, so the tex's halving convention never
has to be threaded through. -/

/-- **Jensen's formula for `ζ` on a disc avoiding the pole**, centred at a non-zero of `ζ`:
`(1/2π)∫₀^{2π} log‖ζ(c + re^{iθ})‖dθ - log‖ζ(c)‖
  = ∑ᶠ u, divisor ζ (closedBall c r) u · log(r/‖c-u‖)`.

### Summary of Proof
`AnalyticOnNhd.circleAverage_log_norm` for `ζ` on `closedBall c |r| ⊆ {1}ᶜ`
(`analyticOn_riemannZeta`), unfolding `Real.circleAverage` and `circleMap`.

### References
tex: Equation `\ref{eq:jensen}` (Equation 1), the Jensen identity behind Proposition
`\ref{prop:jensenrectangle}` (Proposition 19).

### Dependencies
**Depends on:** none (Mathlib's Jensen formula).
**Used by:** `jensenrectangle`. -/
theorem jensen_defect_zeta {c : ℂ} {r : ℝ} (hr : 0 < r) (hc1 : r < ‖c - 1‖)
    (hc0 : riemannZeta c ≠ 0) :
    (1 / (2 * Real.pi)) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖riemannZeta (c + r * Complex.exp (θ * Complex.I))‖)
      - Real.log ‖riemannZeta c‖
    = ∑ᶠ u, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c r) u : ℤ) : ℝ)
        * Real.log (r * ‖c - u‖⁻¹) := by
  have hrabs : |r| = r := abs_of_pos hr
  have hsub : Metric.closedBall c |r| ⊆ ({1} : Set ℂ)ᶜ := by
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    subst h1
    rw [Metric.mem_closedBall, dist_eq_norm, hrabs] at hz
    have : ‖c - 1‖ = ‖(1 : ℂ) - c‖ := by rw [norm_sub_rev]
    linarith
  have han : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c |r|) :=
    analyticOn_riemannZeta.mono hsub
  have hJ := AnalyticOnNhd.circleAverage_log_norm (f := riemannZeta) hr.ne' han hc0
  unfold Real.circleAverage at hJ
  simp only [circleMap, smul_eq_mul] at hJ
  rw [hrabs] at hJ
  have e : (1 / (2 * Real.pi)) = (2 * Real.pi)⁻¹ := one_div _
  rw [e]
  linarith [hJ]

/-- **The multiplicity of `ζ` at a point `≠ 1` is nonnegative**, as the untopped meromorphic
order.

### Summary of Proof
`ζ` is analytic at `u ≠ 1`, so `meromorphicOrderAt ζ u` is the cast of an `analyticOrderAt`
(`AnalyticAt.meromorphicOrderAt_eq`), whose `untop₀` is a natural number or `0`.

### References
No tex counterpart — this is the multiplicity in the tex's "number of zeros, with multiplicity".

### Dependencies
**Depends on:** none.
**Used by:** `jensenrectangle`. -/
theorem zeta_order_untop_nonneg {u : ℂ} (hu : u ≠ 1) :
    (0 : ℤ) ≤ (meromorphicOrderAt riemannZeta u).untop₀ := by
  have han : AnalyticAt ℂ riemannZeta u := analyticOn_riemannZeta u hu
  rw [han.meromorphicOrderAt_eq]
  induction (analyticOrderAt riemannZeta u) using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- **The multiplicity vanishes where `ζ` does not.**

### Summary of Proof
`analyticOrderAt_eq_zero` at a point where `ζ ≠ 0`, transported through
`AnalyticAt.meromorphicOrderAt_eq`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `jensen_sum_eq_finset_sum`, `jensenrectangle`. -/
theorem zeta_order_untop_eq_zero {u : ℂ} (hu : u ≠ 1) (h0 : riemannZeta u ≠ 0) :
    (meromorphicOrderAt riemannZeta u).untop₀ = 0 := by
  have han : AnalyticAt ℂ riemannZeta u := analyticOn_riemannZeta u hu
  rw [han.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h0)]
  simp

/-- **Zeros of `ζ` have real part `< 1`.**

### Summary of Proof
`riemannZeta_ne_zero_of_one_le_re`, contrapositive.

### References
No tex counterpart (used tacitly: the tex's `N(T₁,T₂,α)` counts zeros with `1-α < Re ρ`, and
they all have `Re ρ < 1`).

### Dependencies
**Depends on:** none.
**Used by:** `jensenrectangle`. -/
theorem zeta_zero_re_lt_one {u : ℂ} (hu : riemannZeta u = 0) : u.re < 1 :=
  lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hu)

/-- **The Jensen sum over a disc as a sum over a fixed finite set of zeros.** For a disc
`closedBall c r ⊆ K` (`K` compact, `1 ∉ K`) about a non-zero `c` of `ζ`,
`∑ᶠ u, divisor ζ (closedBall c r) u · log(r/‖c-u‖) = ∑_{u ∈ Z_K} m_u · max 0 (log(r/‖c-u‖))`,
where `Z_K` is the (finite) set of zeros of `ζ` in `K` and `m_u` the multiplicity.

### Summary of Proof
`finsum_eq_finsetSum_of_support_subset`: the support of the divisor lies in the disc, hence in
`Z_K`. Termwise, for `u ∈ Z_K`: inside the disc the divisor is `m_u` (`MeromorphicOn.divisor_apply`)
and `log(r/‖c-u‖) ≥ 0`, so the `max` is the log itself; outside it the divisor is `0` and
`log(r/‖c-u‖) < 0`, so the `max` is `0`. A zero on the boundary circle contributes
`log 1 = 0` either way.

### Lean Notes
This is what replaces the tex's Fubini step: the same finite set `Z_K` serves every disc of the
sweep in `jensenrectangle`, so the `x`-integral of the Jensen defect is an integral of a *finite*
sum, and `intervalIntegral.integral_finsetSum` exchanges it with no measure theory beyond
continuity of each summand.

### References
tex: Equation `\ref{eq:jensen}` (Equation 1) as used in Proposition
`\ref{prop:jensenrectangle}` (Proposition 19).

### Dependencies
**Depends on:** `zeta_order_untop_eq_zero`.
**Used by:** `jensenrectangle`. -/
theorem jensen_sum_eq_finset_sum {K : Set ℂ} (hK : IsCompact K) (h1K : (1 : ℂ) ∉ K)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hsub : Metric.closedBall c r ⊆ K) (hc0 : riemannZeta c ≠ 0) :
    ∑ᶠ u, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c r) u : ℤ) : ℝ)
        * Real.log (r * ‖c - u‖⁻¹)
      = ∑ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
          (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ)
            * max 0 (Real.log (r * ‖c - u‖⁻¹)) := by
  have han : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c r) := by
    apply analyticOn_riemannZeta.mono
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    exact h1K (h1 ▸ hsub hz)
  have hmer : MeromorphicOn riemannZeta (Metric.closedBall c r) := han.meromorphicOn
  rw [finsum_eq_finsetSum_of_support_subset]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨huK, hu0⟩ := hu
    rw [mem_riemannZetaZeros] at hu0
    have hcu : c ≠ u := fun h => hc0 (h ▸ hu0)
    have hnorm : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcu)
    by_cases hball : u ∈ Metric.closedBall c r
    · rw [MeromorphicOn.divisor_apply hmer hball]
      have hle : ‖c - u‖ ≤ r := by
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hball; exact hball
      have h1le : 1 ≤ r * ‖c - u‖⁻¹ := by
        rw [le_mul_inv_iff₀ hnorm, one_mul]; exact hle
      rw [max_eq_right (Real.log_nonneg h1le)]
    · rw [MeromorphicOn.divisor_def]
      simp only [hball, and_false, ite_false]
      have hgt : r < ‖c - u‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] at hball; exact hball
      have hlt : r * ‖c - u‖⁻¹ < 1 := by
        rw [mul_inv_lt_iff₀ hnorm, one_mul]; exact hgt
      rw [max_eq_left (Real.log_nonpos (by positivity) hlt.le)]
      simp
  · intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset]
    have hdiv : MeromorphicOn.divisor riemannZeta (Metric.closedBall c r) u ≠ 0 := by
      intro h; apply hu; simp [h]
    have hball : u ∈ Metric.closedBall c r := by
      by_contra hb
      apply hdiv
      rw [MeromorphicOn.divisor_def]
      simp only [hb, and_false, ite_false]
    refine ⟨hsub hball, ?_⟩
    rw [mem_riemannZetaZeros]
    by_contra hne
    apply hdiv
    rw [MeromorphicOn.divisor_apply hmer hball]
    exact zeta_order_untop_eq_zero (fun h => h1K (h ▸ hsub hball)) hne

/-- **The centre `1 + (T+x)i` is at positive distance from any point with `Re < 1`.**

### Summary of Proof
`|Re| ≤ ‖·‖` (`Complex.abs_re_le_norm`) with real part `1 - Re u > 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeroWeight_continuous`. -/
theorem norm_center_sub_pos {u : ℂ} (hu : u.re < 1) (T x : ℝ) :
    0 < ‖(1 + (T + x) * Complex.I : ℂ) - u‖ := by
  have hre : ((1 + (T + x) * Complex.I : ℂ) - u).re = 1 - u.re := by simp
  have := Complex.abs_re_le_norm ((1 + (T + x) * Complex.I : ℂ) - u)
  rw [hre] at this
  have h1 : 0 < 1 - u.re := by linarith
  calc (0:ℝ) < 1 - u.re := h1
    _ ≤ |1 - u.re| := le_abs_self _
    _ ≤ _ := this

/-- **Continuity in `x` of the per-zero weight `max 0 (log(r/‖(1 + (T+x)i) - u‖))`** for a
point `u` with `Re u < 1`.

### Summary of Proof
Composition of continuous maps; `Continuous.inv₀` and `Continuous.log` need the norm and the
ratio nonzero, which `norm_center_sub_pos` and `r > 0` give.

### References
No tex counterpart — supplies the integrability the exchange of sum and integral needs.

### Dependencies
**Depends on:** `norm_center_sub_pos`.
**Used by:** `window_integral_ge_rectDenom`, `jensenrectangle`. -/
theorem zeroWeight_continuous {u : ℂ} (hu : u.re < 1) {r : ℝ} (hr : 0 < r) (T : ℝ) :
    Continuous (fun x : ℝ =>
      max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹))) := by
  have hn : Continuous (fun x : ℝ => ‖(1 + (T + x) * Complex.I : ℂ) - u‖) := by fun_prop
  have hne : ∀ x : ℝ, ‖(1 + (T + x) * Complex.I : ℂ) - u‖ ≠ 0 :=
    fun x => (norm_center_sub_pos hu T x).ne'
  refine continuous_const.max (Continuous.log (continuous_const.mul (hn.inv₀ hne)) ?_)
  intro x
  exact mul_ne_zero hr.ne' (inv_ne_zero (hne x))

/-- **`‖(1 + (T+x)i) - u‖ = √((1-Re u)² + (x-(Im u-T))²)`.**

### Summary of Proof
`Complex.norm_eq_sqrt_sq_add_sq` and the real/imaginary parts of the difference.

### References
tex: the distance `|ρ - (1+i(T+x))|` in the proof of Proposition `\ref{prop:jensenrectangle}`
(Proposition 19).

### Dependencies
**Depends on:** none.
**Used by:** `window_integral_ge_rectDenom`. -/
theorem norm_center_sub_eq (u : ℂ) (T x : ℝ) :
    ‖(1 + (T + x) * Complex.I : ℂ) - u‖
      = Real.sqrt ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp
  ring

/-- **Step (iii) of `jensenrectangle`, per zero.** A zero `u` of `ζ` counted by
`Nrect (T-h) (T+h) α` — so `1-α < Re u < 1` and `T-h < Im u ≤ T+h` — contributes at least
`rectDenom r α` to the integrated Jensen defect over the window `x ∈ [-h-α̂_r, h+α̂_r]`:
`rectDenom r α ≤ ∫_{-h-α̂}^{h+α̂} max 0 (log(r/‖(1+(T+x)i) - u‖)) dx`.

### Summary of Proof
Shrink the window to the zero's own `[x₀-α̂, x₀+α̂]`, `x₀ = Im u - T ∈ (-h, h]`
(`intervalIntegral.integral_mono_interval`, the integrand being `≥ 0`). There
`(1-Re u)² + (x-x₀)² ≤ α² + α̂² = r²`, so the weight is `log r - ½log((1-Re u)² + (x-x₀)²)` with
no `max` (`norm_center_sub_eq`); translate by `x₀` (`intervalIntegral.integral_comp_sub_right`)
and apply `rectDenom_le_window` with `b = 1 - Re u ∈ (0, α]`.

### References
tex: the per-zero evaluation in the proof of Proposition `\ref{prop:jensenrectangle}`
(Proposition 19).

### Dependencies
**Depends on:** `hatAlpha`, `rectDenom`, `rectDenom_le_window`, `zeroWeight_continuous`,
`norm_center_sub_eq`.
**Used by:** `jensenrectangle`. -/
theorem window_integral_ge_rectDenom {T h r α : ℝ} (hα : 0 < α) (hrα : α < r)
    {u : ℂ} (hre : 1 - α < u.re) (hre1 : u.re < 1) (him1 : T - h < u.im) (him2 : u.im ≤ T + h) :
    rectDenom r α ≤ ∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
        max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)) := by
  have hr : 0 < r := hα.trans hrα
  have hA0 : 0 ≤ hatAlpha r α := Real.sqrt_nonneg _
  have hA2 : hatAlpha r α ^ 2 = r ^ 2 - α ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb : 0 < 1 - u.re := by linarith
  have hbα : 1 - u.re ≤ α := by linarith
  have hcont := zeroWeight_continuous hre1 hr T
  -- step 1: shrink the window to the zero's own `[x₀-α̂, x₀+α̂]`
  have h1 : (∫ x in (u.im - T - hatAlpha r α)..(u.im - T + hatAlpha r α),
        max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)))
      ≤ ∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
        max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)) := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun x => le_max_left _ _)
    · exact hcont.intervalIntegrable _ _
  -- step 2: on that window the positive part is the log itself
  have h2 : (∫ x in (u.im - T - hatAlpha r α)..(u.im - T + hatAlpha r α),
        max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)))
      = ∫ x in (u.im - T - hatAlpha r α)..(u.im - T + hatAlpha r α),
        (Real.log r - (1 / 2) * Real.log ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hsq : (x - (u.im - T)) ^ 2 ≤ hatAlpha r α ^ 2 := by
      apply sq_le_sq' <;> linarith
    have hpos : 0 < (1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2 := by positivity
    have hle : (1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2 ≤ r ^ 2 := by nlinarith
    have hsqrt_le : Real.sqrt ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2) ≤ r := by
      calc Real.sqrt ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2) ≤ Real.sqrt (r ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = r := Real.sqrt_sq hr.le
    have hsqrt_pos : 0 < Real.sqrt ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2) :=
      Real.sqrt_pos.mpr hpos
    dsimp only
    rw [norm_center_sub_eq u T x]
    have h1le : 1 ≤ r * (Real.sqrt ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2))⁻¹ := by
      rw [le_mul_inv_iff₀ hsqrt_pos, one_mul]; exact hsqrt_le
    rw [max_eq_right (Real.log_nonneg h1le), Real.log_mul hr.ne' (inv_ne_zero hsqrt_pos.ne'),
      Real.log_inv, Real.log_sqrt hpos.le]
    ring
  -- step 3: translate to the symmetric window `[-α̂, α̂]`
  have h3 : (∫ x in (u.im - T - hatAlpha r α)..(u.im - T + hatAlpha r α),
        (Real.log r - (1 / 2) * Real.log ((1 - u.re) ^ 2 + (x - (u.im - T)) ^ 2)))
      = ∫ y in (-hatAlpha r α)..(hatAlpha r α),
        (Real.log r - (1 / 2) * Real.log ((1 - u.re) ^ 2 + y ^ 2)) := by
    have := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => Real.log r - (1 / 2) * Real.log ((1 - u.re) ^ 2 + y ^ 2))
      (a := u.im - T - hatAlpha r α) (b := u.im - T + hatAlpha r α) (u.im - T)
    have e1 : u.im - T - hatAlpha r α - (u.im - T) = -hatAlpha r α := by ring
    have e2 : u.im - T + hatAlpha r α - (u.im - T) = hatAlpha r α := by ring
    rw [e1, e2] at this
    exact this
  have h4 := rectDenom_le_window hb hbα hrα
  linarith [h1, h2, h3, h4]

set_option maxHeartbeats 300000 in
-- the assembly carries a `Finset`-indexed family of interval integrals through `integral_congr`,
-- `integral_finsetSum` and a termwise comparison; elaboration exceeds the default budget
/-- **Proposition `\ref{prop:jensenrectangle}` (Proposition 19).** For `r > α > 0` and
`T - α̂_r - r > h > 0`,
`N(T-h,T+h,α) ≤` the integral of the Jensen defect
`(1/(2π))∫_0^{2π} log|ζ(1+i(T+x)+re^{iθ})|dθ - log|ζ(1+i(T+x))|` over `x ∈ [-h-α̂_r, h+α̂_r]`,
divided by `rectDenom r α`. (The manuscript's `<` is false — see Lean Notes.)**

### Summary of Proof
Integrate Equation `\ref{eq:jensen}` (Equation 1) over `x` in the stated range and exchange the
integral with the sum over zeros. Each zero `ρ` with `1 - Re ρ < α` and `Im ρ ∈ (T-h, T+h]`
contributes at least `rectDenom r α` — a closed form for `∫ log(r) - (1/2)log(α²+t²) dt`,
evaluated via `arctan`. Dividing through by that common lower bound gives the claimed count.

### Lean Notes
**Three steps.** (i) Jensen's formula for `ζ` on each disc,
`jensen_defect_zeta` (Mathlib's `AnalyticOnNhd.circleAverage_log_norm`; the disc avoids the pole
because `|T+x| ≥ T-h-α̂ > r`, and the centre is not a zero because `Re = 1`). (ii) The exchange
of `∫dx` with the sum over zeros: `jensen_sum_eq_finset_sum` rewrites every disc's Jensen sum as
a sum over the *same* finite set `Z_K` of zeros of `ζ` in the compact rectangle
`K = [1-r, 1+r] × [T-h-α̂-r, T+h+α̂+r]` (`IsCompact.inter_riemannZetaZeros_finite`), weighted by
`m_u · max 0 (log(r/‖c(x)-u‖))`, so `intervalIntegral.integral_finsetSum` does the exchange with
no Fubini argument; `Nrect (T-h) (T+h) α` is the sum of the same `m_u` over the `u ∈ Z_K` lying
in the strip (`MeromorphicOn.divisor_apply` on both sets gives the same
`(meromorphicOrderAt ζ u).untop₀`). (iii) Each counted zero contributes at least `rectDenom r α`
(`window_integral_ge_rectDenom`, resting on `rectDenom_le_window`, `rectDenom_eq_sqrt_form` and
`integral_log_disc_chord_eq`, all checked to 40 digits in `Code/verify_rectDenom_window.py`),
every other zero contributes `≥ 0`, and `rectDenom_pos` divides through.

**Boundary zeros.** A zero on a boundary circle `‖u - c(x)‖ = r` has weight `log 1 = 0` whether or
not the divisor counts it, so the tex's halving convention after Equation
`\ref{eq:zerodensityintegral}` (Equation 13) never has to be threaded through here.

**Stated with `≤`; the manuscript's `<` is FALSE.** With `<` the statement would be not merely
unproved but refutable, in *two independent ways*.

*Junk value (which `hα : 0 < α` rules out).* Take `α = -1, r = 1, h = 1, T = 3`. Every other
hypothesis holds (`α < r`, `0 < h`, and `α̂_r = √(1-1) = 0` so `h < T - α̂_r - r = 2`),
but `rectDenom 1 (-1) = 2√(1-1) + 2 arctan(√(1-1)) = 0`, so the right-hand side is
`numerator / 0 = 0` by Lean's total division; and `Nrect 2 4 (-1)` counts zeros with `Re ρ > 2`,
of which there are none. So `0 < 0`. That is why `hα : 0 < α` is a hypothesis — `rectDenom_pos`
needs it anyway, and both callers already have it in scope.

*Analytic (survives `0 < α`, and is why `≤` is unavoidable).* The numerator is the Jensen defect
`(1/2π)∮log|ζ| - log|ζ(centre)|`, which by Jensen's formula equals `∑_ρ log(r/|ρ-c|)` over the
zeros `ρ` in the disc of radius `r` about `c = 1+i(T+x)`. A zero `ρ = β+iγ` enters that disc only
if `1 - β < r`. So whenever `r` is below the distance from the line `Re s = 1` to the nearest
zero at these heights, every disc is zero-free, `log|ζ|` is harmonic on it, and the defect is
**exactly `0`** by the mean value property — making the whole right-hand side `0`. And
`Nrect (T-h) (T+h) α` counts zeros with `1 - α < Re ρ`, so with `α < r` it is `0` for the same
reason. The assertion becomes `0 < 0`.

This needs no unproved hypothesis: the classical zero-free region
`ζ(σ+it) ≠ 0` for `σ > 1 - c/log(|t|+3)` makes the discs provably zero-free as soon as
`r < c/log(T+3)`, which `hrα`, `hh` and `hTh` freely allow (they impose no lower bound on `r`).
Verified numerically at `T = 100, h = 0.01, α = 0.02, r = 0.03` in
`Code/verify_jensenrectangle_degenerate.py`, where the defect comes out `< 1.2×10⁻⁴¹`
(quadrature noise at 40 digits) across the whole `x`-window.

`≤` costs nothing downstream: both consumers, `rectangularjensen` and `rectangularjensen_tight`,
conclude with `≤`. `outside2`, `outside3` and `JensenBounds.integraloutside_bound` likewise state
`≤` in place of the manuscript's unjustified `<`; the difference is that here the `<` is
refutable rather than just unjustified.

### References
tex: Proposition `\ref{prop:jensenrectangle}` (Proposition 19); rests on Equation
`\ref{eq:jensen}` (Equation 1) and the `α̂_r` of Equation `\ref{eq:hatalpha}` (Equation 10).

### Dependencies
**Depends on:** `Nrect`, `hatAlpha`, `rectDenom`, `rectDenom_pos`, `jensen_defect_zeta`,
`jensen_sum_eq_finset_sum`, `window_integral_ge_rectDenom`, `zeroWeight_continuous`,
`zeta_order_untop_nonneg`, `zeta_order_untop_eq_zero`, `zeta_zero_re_lt_one`,
`Definitions.analyticOnNhd_riemannZeta_rect`.
**Used by:** `rectangularjensen`, `rectangularjensen_tight`. -/
theorem jensenrectangle {T h r α : ℝ} (hα : 0 < α) (hrα : α < r) (hh : 0 < h)
    (hTh : h < T - hatAlpha r α - r) :
    (Nrect (T - h) (T + h) α : ℝ)
      ≤ (∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
            ((1 / (2 * Real.pi)) *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
              - Real.log ‖riemannZeta (1 + (T + x) * Complex.I)‖))
        / rectDenom r α := by
  have hr : 0 < r := hα.trans hrα
  have hA0 : 0 ≤ hatAlpha r α := Real.sqrt_nonneg _
  have hD := rectDenom_pos hα hrα
  have hTh0 : 0 < T - h := by linarith
  rw [le_div_iff₀ hD]
  -- the compact rectangle containing every disc of the sweep
  have hK : IsCompact (Set.Icc (1 - r) (1 + r) ×ℂ
      Set.Icc (T - h - hatAlpha r α - r) (T + h + hatAlpha r α + r)) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  have h1K : (1 : ℂ) ∉ Set.Icc (1 - r) (1 + r) ×ℂ
      Set.Icc (T - h - hatAlpha r α - r) (T + h + hatAlpha r α + r) := by
    intro hmem
    rw [Complex.mem_reProdIm] at hmem
    have := hmem.2.1
    rw [Complex.one_im] at this
    linarith
  -- every zero in the rectangle is a genuine zero with `Re < 1`, `≠ 1`
  have hZmem : ∀ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
      riemannZeta u = 0 ∧ u ≠ 1 ∧ u.re < 1 := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨huK, hu0⟩ := hu
    rw [mem_riemannZetaZeros] at hu0
    exact ⟨hu0, fun h => h1K (h ▸ huK), zeta_zero_re_lt_one hu0⟩
  have hm_nonneg : ∀ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
      (0 : ℝ) ≤ (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ) := by
    intro u hu
    exact_mod_cast zeta_order_untop_nonneg (hZmem u hu).2.1
  -- pointwise identity of the integrand: Jensen, then the finite-sum form
  have hpt : Set.EqOn
      (fun x : ℝ => (1 / (2 * Real.pi)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
        - Real.log ‖riemannZeta (1 + (T + x) * Complex.I)‖)
      (fun x : ℝ => ∑ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
          (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ)
            * max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)))
      (Set.uIcc (-h - hatAlpha r α) (h + hatAlpha r α)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hc1 : r < ‖(1 + (T + x) * Complex.I : ℂ) - 1‖ := by
      have e : (1 + (T + x) * Complex.I : ℂ) - 1 = ((T + x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have hc0 : riemannZeta (1 + (T + x) * Complex.I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp
    have hsub : Metric.closedBall (1 + (T + x) * Complex.I : ℂ) r ⊆
        Set.Icc (1 - r) (1 + r) ×ℂ
          Set.Icc (T - h - hatAlpha r α - r) (T + h + hatAlpha r α + r) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - (1 + (T + x) * Complex.I))
      have him := Complex.abs_im_le_norm (z - (1 + (T + x) * Complex.I))
      have ere : (z - (1 + (T + x) * Complex.I)).re = z.re - 1 := by simp
      have eim : (z - (1 + (T + x) * Complex.I)).im = z.im - (T + x) := by simp
      rw [ere] at hre
      rw [eim] at him
      have hre' := abs_le.mp (hre.trans hz)
      have him' := abs_le.mp (him.trans hz)
      rw [Complex.mem_reProdIm]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    dsimp only
    rw [jensen_defect_zeta hr hc1 hc0, jensen_sum_eq_finset_sum hK h1K hr hsub hc0]
  rw [intervalIntegral.integral_congr hpt]
  -- exchange the finite sum with the `x`-integral
  have hsum : (∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
        ∑ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
          (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ)
            * max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)))
      = ∑ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
          (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ)
            * ∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
                max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)) := by
    refine (intervalIntegral.integral_finsetSum
      (f := fun u x => (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ)
        * max 0 (Real.log (r * ‖(1 + (T + x) * Complex.I : ℂ) - u‖⁻¹)))
      (fun u hu => (continuous_const.mul
        (zeroWeight_continuous (hZmem u hu).2.2 hr T)).intervalIntegrable _ _)).trans ?_
    apply Finset.sum_congr rfl
    intro u _
    exact intervalIntegral.integral_const_mul _ _
  rw [hsum]
  -- `Nrect` as a sum over the same finite set
  have hS_mer : MeromorphicOn riemannZeta
      {s : ℂ | T - h < s.im ∧ s.im ≤ T + h ∧ 1 - α < s.re} :=
    (analyticOnNhd_riemannZeta_rect hTh0).meromorphicOn
  have hN : (Nrect (T - h) (T + h) α : ℝ)
      = ∑ u ∈ (hK.inter_riemannZetaZeros_finite).toFinset,
          (if (T - h < u.im ∧ u.im ≤ T + h ∧ 1 - α < u.re)
            then (((meromorphicOrderAt riemannZeta u).untop₀ : ℤ) : ℝ) else 0) := by
    unfold Nrect
    rw [finsum_eq_finsetSum_of_support_subset _ (s := (hK.inter_riemannZetaZeros_finite).toFinset)]
    · push_cast
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hS : T - h < u.im ∧ u.im ≤ T + h ∧ 1 - α < u.re
      · rw [MeromorphicOn.divisor_apply hS_mer hS]
        simp only [hS, and_self, ite_true]
      · rw [MeromorphicOn.divisor_def]
        simp only [Set.mem_ofPred_eq, hS, and_false, ite_false, Int.cast_zero]
    · intro u hu
      rw [Function.mem_support] at hu
      rw [Set.Finite.coe_toFinset]
      have huS : T - h < u.im ∧ u.im ≤ T + h ∧ 1 - α < u.re := by
        by_contra hS
        apply hu
        rw [MeromorphicOn.divisor_def]
        simp only [Set.mem_ofPred_eq, hS, and_false, ite_false]
      have hu1 : u ≠ 1 := by
        intro h
        rw [h, Complex.one_im] at huS
        linarith [huS.1]
      have hu0 : riemannZeta u = 0 := by
        by_contra hne
        apply hu
        rw [MeromorphicOn.divisor_apply hS_mer huS]
        exact zeta_order_untop_eq_zero hu1 hne
      refine ⟨?_, hu0⟩
      rw [Complex.mem_reProdIm]
      have hre1 := zeta_zero_re_lt_one hu0
      exact ⟨⟨by linarith [huS.2.2], by linarith⟩, ⟨by linarith [huS.1], by linarith [huS.2.1]⟩⟩
  rw [hN, Finset.sum_mul]
  -- termwise: counted zeros give `≥ rectDenom`, the others `≥ 0`
  apply Finset.sum_le_sum
  intro u hu
  obtain ⟨hu0, hu1, hre1⟩ := hZmem u hu
  split_ifs with hS
  · exact mul_le_mul_of_nonneg_left
      (window_integral_ge_rectDenom hα hrα hS.2.2 hre1 hS.1 hS.2.1) (hm_nonneg u hu)
  · rw [zero_mul]
    exact mul_nonneg (hm_nonneg u hu)
      (intervalIntegral.integral_nonneg (by linarith) (fun x _ => le_max_left _ _))

/-- **The `Φ`-FTC identity on a vertical segment:** for `σ > 1`,
`∫_{T-h'}^{T+h'} log‖ζ(σ+it)‖ dt = Φ(σ+i(T-h')).im - Φ(σ+i(T+h')).im`.

### Summary of Proof
`Definitions.Phi_im_hasDerivAt` says `t ↦ Φ(σ+it).im` is an antiderivative of `-log‖ζ(σ+it)‖`
along the vertical line `Re s = σ`. Since `σ > 1` keeps the whole segment off `ζ`'s pole and
zero set, the integrand is continuous there, so the plain
`intervalIntegral.integral_eq_sub_of_hasDerivAt` applies and the integral telescopes.

### Lean Notes
Stated as an *identity* rather than the bound `abs_integral_log_zeta_vertical_le` derives from
it, because `outside3_inner_abs_intervalIntegrable` needs the closed form: it is what exhibits the
inner `x`-integral of `outside3` as a **continuous** function of `θ`, which is how that
integrability is proved.

### References
No tex counterpart. It is the `σ`-fixed core shared by Proposition `\ref{prop:outside2}`
(Proposition 22) and Proposition `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `Phi`, `Phi_im_hasDerivAt`.
**Used by:** `abs_integral_log_zeta_vertical_le`, `outside3_theta_slice_eq`. -/
theorem integral_log_zeta_vertical_eq {σ T h' : ℝ} (hσ : 1 < σ) :
    (∫ t in (T - h')..(T + h'), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      = (Phi ((σ : ℂ) + ((T - h' : ℝ) : ℂ) * Complex.I)).im
        - (Phi ((σ : ℂ) + ((T + h' : ℝ) : ℂ) * Complex.I)).im := by
  have hne : ∀ x : ℝ, (σ : ℂ) + (x : ℂ) * Complex.I ≠ 1 := by
    intro x heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have haffine_cont : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hzcont : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + t * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (differentiableAt_riemannZeta (hne t)).continuousAt
      haffine_cont.continuousAt
  have hnz : ∀ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≠ 0 := fun t =>
    norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))
  have hlogcont : Continuous (fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖) :=
    hzcont.norm.log hnz
  have hderiv : ∀ x ∈ Set.uIcc (T - h') (T + h'),
      HasDerivAt (fun x : ℝ => (Phi ((σ : ℂ) + x * Complex.I)).im)
        (-Real.log ‖riemannZeta ((σ : ℂ) + x * Complex.I)‖) x :=
    fun x _ => Phi_im_hasDerivAt hσ x
  have hint : IntervalIntegrable (fun x : ℝ => -Real.log ‖riemannZeta ((σ : ℂ) + x * Complex.I)‖)
      MeasureTheory.volume (T - h') (T + h') := hlogcont.neg.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hFTC
  linarith [hFTC]

/-- **The `Φ`-FTC bound on a vertical segment, in absolute value:** for `σ > 1`,
`|∫_{T-h'}^{T+h'} log‖ζ(σ+it)‖ dt| ≤ 2·Φ(σ).re`.

### Summary of Proof
`Φ` is an antiderivative of `-log ζ` along the vertical line (`Phi_im_hasDerivAt`), so the
integral telescopes to `Φ(σ+i(T-h')).im - Φ(σ+i(T+h')).im`. Each of those is bounded in absolute
value by `Φ(σ).re`, since `|Im w| ≤ ‖w‖` and `Phi_norm_le` gives `‖Φ(w)‖ ≤ Φ(Re w).re`. The
triangle inequality then gives `2·Φ(σ).re`.

### Lean Notes
This is the two-sided strengthening of `outside2_of_one_lt`, which states only the upper half and
is derived from it. The two-sided form is what `outside3` needs, since
that proposition bounds an **absolute value** of the `x`-integral: the triangle inequality there
controls `|Im(Φ(a) - Φ(b))|` rather than one sign of it.

The telescoping step itself is factored out as `integral_log_zeta_vertical_eq` above, since
`outside3_inner_abs_intervalIntegrable` needs the *identity* and not just the bound; what is left
here is only the two `|Im Φ| ≤ Φ(σ).re` estimates.

Restricted to `σ > 1` strictly, so no boundary or `ε` argument is needed; the extension to
`σ = 1` is `outside2_le`'s job.

### References
No tex counterpart. It is the `σ`-fixed core shared by Proposition `\ref{prop:outside2}`
(Proposition 22) and Proposition `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `Phi`, `Phi_norm_le`, `integral_log_zeta_vertical_eq`.
**Used by:** `outside2_of_one_lt`, `outside3_theta_slice_le`. -/
theorem abs_integral_log_zeta_vertical_le {σ T h' : ℝ} (hσ : 1 < σ) :
    |∫ t in (T - h')..(T + h'), Real.log ‖riemannZeta (σ + t * Complex.I)‖|
      ≤ 2 * (Phi σ).re := by
  have hbound : ∀ x : ℝ, |(Phi ((σ : ℂ) + x * Complex.I)).im| ≤ (Phi σ).re := by
    intro x
    have h1 : |(Phi ((σ : ℂ) + x * Complex.I)).im| ≤ ‖Phi ((σ : ℂ) + x * Complex.I)‖ :=
      Complex.abs_im_le_norm _
    have h2 : ‖Phi ((σ : ℂ) + x * Complex.I)‖ ≤ (Phi (((σ : ℂ) + x * Complex.I).re : ℂ)).re :=
      Phi_norm_le (by simpa using hσ)
    have h3 : (((σ : ℂ) + x * Complex.I).re : ℂ) = (σ : ℂ) := by simp
    rw [h3] at h2
    linarith
  rw [integral_log_zeta_vertical_eq hσ]
  have hb1 := hbound (T - h')
  have hb2 := hbound (T + h')
  push_cast at hb1 hb2 ⊢
  rw [abs_le] at hb1 hb2 ⊢
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- **`outside2`'s statement for `σ > 1` strictly** (no boundary/`ε` issues, mirroring
`LittlewoodMethod.littlewood_outerlog_of_one_lt`'s proof exactly but non-negated: swapping which
of `Im Φ(σ+i(T±h'))` is subtracted from which gives the *non-negated* direction of the same
triangle-inequality bound).**

### Summary of Proof
Mirrors `LittlewoodMethod.littlewood_outerlog_of_one_lt`'s proof exactly, but on a
*vertical* segment rather than a horizontal one: `Φ` is an antiderivative of `-log ζ`
(`Phi_im_hasDerivAt`), so the integral telescopes to a difference of `Φ` values, and
`Phi_norm_le` bounds those. Restricted to `σ > 1` strictly, so no boundary or `ε`
argument is needed.

### Lean Notes
This is the upper half of `abs_integral_log_zeta_vertical_le`, which carries the same argument in
two-sided form; the proof below is just that lemma's `≤` direction rescaled by `1/(2π)`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `abs_integral_log_zeta_vertical_le`.
**Used by:** `outside2_le`. -/
theorem outside2_of_one_lt {σ T h' : ℝ} (hσ : 1 < σ) :
    (1 / (2 * Real.pi)) * ∫ t in (T - h')..(T + h'), Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (Phi σ).re / Real.pi := by
  have hcore := (abs_le.mp (abs_integral_log_zeta_vertical_le (σ := σ) (T := T) (h' := h') hσ)).2
  rw [show (Phi σ).re / Real.pi = (1 / (2 * Real.pi)) * (2 * (Phi σ).re) by field_simp]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

/-- **`outside2`'s content, with `≤` instead of `<`, extended to `σ = 1`.**

### Summary of Proof
Take `outside2_of_one_lt`, which is valid for every `σ > 1`, and pass to the limit `ε → 0⁺`. Two
continuity facts make the limit legitimate: continuity of the integral in `σ` at `σ = 1` from the
right — via `intervalIntegral.continuousWithinAt_of_dominated_interval`, using that `ζ` is
holomorphic and non-vanishing (`riemannZeta_ne_zero_of_one_le_re`) on a neighbourhood of the
compact rectangle `[1,2] × [T-h', T+h']`, which stays clear of `ζ`'s pole since `T - h' > 0` —
and continuity of `Phi` at `σ = 1` (`Definitions.Phi_continuousOn_closedHalfPlane`).

### Lean Notes
Carries the extra hypothesis `0 ≤ h` purely so that `T - h' ≤ T + h'`, i.e. so the integration
bounds are in the expected order; harmless, since `h` is always a half-width in the source. This
is exactly `outside2` itself — see that theorem's docstring for the `≤`/`0 ≤ h` discussion.

### References
tex: Proposition `\ref{prop:outside2}` (Proposition 22).

### Dependencies
**Depends on:** `Phi`, `Phi_continuousOn_closedHalfPlane`, `hatAlpha`, `outside2_of_one_lt`.
**Used by:** `outside2`. -/
theorem outside2_le {T h r α : ℝ} (hh : 0 ≤ h) (hTh : h + hatAlpha r α < T) :
    (1 / (2 * Real.pi)) *
        ∫ t in (T - h - hatAlpha r α)..(T + h + hatAlpha r α),
          Real.log ‖riemannZeta (1 + t * Complex.I)‖
      ≤ (Phi 1).re / Real.pi := by
  set h' : ℝ := h + hatAlpha r α with hh'_def
  have hTh' : (0:ℝ) < T - h' := by linarith
  have hh'0 : (0:ℝ) ≤ h' := by
    rw [hh'_def]; have := Real.sqrt_nonneg (r ^ 2 - α ^ 2); unfold hatAlpha; linarith
  have hle : T - h' ≤ T + h' := by linarith
  have heq1 : T - h - hatAlpha r α = T - h' := by rw [hh'_def]; ring
  have heq2 : T + h + hatAlpha r α = T + h' := by rw [hh'_def]; ring
  rw [heq1, heq2]
  set F : ℝ → ℝ := fun σ => (1 / (2 * Real.pi)) *
      ∫ t in (T - h')..(T + h'), Real.log ‖riemannZeta (σ + t * Complex.I)‖ with hF_def
  -- Joint continuity + a uniform bound of the integrand on `[1,2] × [T-h',T+h']`.
  have hcontpt : ∀ p : ℝ × ℝ, 1 ≤ p.1 → T - h' ≤ p.2 → p.2 ≤ T + h' →
      ContinuousAt (fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I)) p := by
    intro p hp1 hp2 hp3
    have hne : (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
        Complex.ofReal_re, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
      linarith
    have haff : ContinuousAt (fun q : ℝ × ℝ => (q.1:ℂ) + (q.2:ℂ) * Complex.I) p := by fun_prop
    have hcomp := ContinuousAt.comp
      (f := fun q : ℝ × ℝ => (q.1:ℂ) + (q.2:ℂ) * Complex.I) (x := p)
      (differentiableAt_riemannZeta hne).continuousAt haff
    exact hcomp
  -- Single-variable slices of `hcontpt`, fixing one coordinate.
  have hcontpt1 : ∀ σ t : ℝ, 1 ≤ σ → T - h' ≤ t → t ≤ T + h' →
      ContinuousAt (fun s : ℝ => riemannZeta ((σ:ℂ) + (s:ℂ) * Complex.I)) t := by
    intro σ t h1 h2 h3
    have hinj : ContinuousAt (fun s : ℝ => ((σ, s) : ℝ × ℝ)) t :=
      continuousAt_const.prodMk continuousAt_id
    have hcomp := ContinuousAt.comp
      (g := fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I))
      (f := fun s : ℝ => ((σ, s) : ℝ × ℝ)) (x := t)
      (hcontpt (σ, t) h1 h2 h3) hinj
    exact hcomp
  have hcontpt2 : ∀ σ t : ℝ, 1 ≤ σ → T - h' ≤ t → t ≤ T + h' →
      ContinuousAt (fun s : ℝ => riemannZeta ((s:ℂ) + (t:ℂ) * Complex.I)) σ := by
    intro σ t h1 h2 h3
    have hinj : ContinuousAt (fun s : ℝ => ((s, t) : ℝ × ℝ)) σ :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp := ContinuousAt.comp
      (g := fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I))
      (f := fun s : ℝ => ((s, t) : ℝ × ℝ)) (x := σ)
      (hcontpt (σ, t) h1 h2 h3) hinj
    exact hcomp
  have hjointcont : ContinuousOn (fun p : ℝ × ℝ => Real.log ‖riemannZeta (p.1 + p.2 * Complex.I)‖)
      (Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h') (T + h')) := by
    apply ContinuousOn.log
    · intro p hp
      simp only [Set.mem_prod, Set.mem_Icc] at hp
      exact (hcontpt p hp.1.1 hp.2.1 hp.2.2).continuousWithinAt.norm
    · intro p hp
      simp only [Set.mem_prod, Set.mem_Icc] at hp
      exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hp.1.1))
  have hcompact : IsCompact (Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h') (T + h')) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hjointcont.norm
  have hCbound : ∀ p ∈ Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h') (T + h'),
      ‖Real.log ‖riemannZeta (p.1 + p.2 * Complex.I)‖‖ ≤ C :=
    fun p hp => hC (Set.mem_image_of_mem _ hp)
  have hs_mem : Set.Icc (1:ℝ) 2 ∈ nhdsWithin (1:ℝ) (Set.Ici 1) := by
    apply Filter.mem_of_superset
      (inter_mem_nhdsWithin (Set.Ici 1) (isOpen_Iio.mem_nhds (show (1:ℝ) < 2 by norm_num)))
    intro x hx
    exact ⟨hx.1, le_of_lt hx.2⟩
  -- Continuity (from the right) of the bare integral in `σ` at `σ = 1`.
  have hIntCont : ContinuousWithinAt
      (fun σ : ℝ => ∫ t in (T - h')..(T + h'), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      (Set.Ici 1) 1 := by
    have hmeas : ∀ σ : ℝ, 1 ≤ σ →
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => Real.log ‖riemannZeta (σ + t * Complex.I)‖)
          (MeasureTheory.volume.restrict (Set.uIoc (T - h') (T + h'))) := by
      intro σ hσ
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      apply ContinuousOn.mono _ Set.uIoc_subset_uIcc
      rw [Set.uIcc_of_le hle]
      intro t ht
      exact ((hcontpt1 σ t hσ ht.1 ht.2).continuousWithinAt).norm.log
        (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hσ)))
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun (σ t : ℝ) => Real.log ‖riemannZeta (σ + t * Complex.I)‖) (bound := fun _ => C)
    · filter_upwards [hs_mem] with σ hσ using hmeas σ hσ.1
    · filter_upwards [hs_mem] with σ hσ
      apply MeasureTheory.ae_of_all
      intro t htmem
      have ht' : t ∈ Set.Icc (T - h') (T + h') := by
        rw [← Set.uIcc_of_le hle]; exact Set.uIoc_subset_uIcc htmem
      rw [Real.norm_eq_abs]
      exact hCbound (σ, t) ⟨hσ, ht'⟩
    · exact intervalIntegrable_const
    · apply MeasureTheory.ae_of_all
      intro t ht
      have ht' : t ∈ Set.Icc (T - h') (T + h') := by
        rw [← Set.uIcc_of_le hle]; exact Set.uIoc_subset_uIcc ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.log
      · exact (hcontpt2 1 t le_rfl ht'.1 ht'.2).norm
      · exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simp))
  have hFcont : ContinuousWithinAt F (Set.Ici 1) 1 := by
    rw [hF_def]; exact hIntCont.const_mul _
  have hFcont' : Filter.Tendsto F (nhdsWithin 1 (Set.Ici 1)) (nhds (F 1)) := hFcont
  have hGcont : Filter.Tendsto (fun σ : ℝ => (Phi (σ:ℂ)).re / Real.pi)
      (nhdsWithin 1 (Set.Ici 1)) (nhds ((Phi 1).re / Real.pi)) := by
    have hmapsto : Set.MapsTo (fun σ : ℝ => (σ:ℂ)) (Set.Ici (1:ℝ)) {s : ℂ | 1 ≤ s.re} :=
      fun x hx => by simpa using hx
    have hcompPhi : ContinuousOn (fun σ : ℝ => Phi (σ:ℂ)) (Set.Ici 1) :=
      Phi_continuousOn_closedHalfPlane.comp Complex.continuous_ofReal.continuousOn hmapsto
    have h1mem : (1:ℝ) ∈ Set.Ici (1:ℝ) := Set.mem_Ici.mpr le_rfl
    have h0 := (hcompPhi 1 h1mem).tendsto
    have h2 := (Complex.continuous_re.tendsto (Phi (1:ℂ))).comp h0
    simpa [Function.comp] using h2.div_const Real.pi
  have hle_eventually : ∀ᶠ σ in nhdsWithin (1:ℝ) (Set.Ioi 1),
      F σ ≤ (Phi (σ:ℂ)).re / Real.pi := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ using outside2_of_one_lt hσ
  have hmono : (nhdsWithin (1:ℝ) (Set.Ioi 1)) ≤ nhdsWithin (1:ℝ) (Set.Ici 1) :=
    nhdsWithin_mono 1 Set.Ioi_subset_Ici_self
  exact le_of_tendsto_of_tendsto (hFcont'.mono_left hmono) (hGcont.mono_left hmono) hle_eventually

/-- **Proposition `\ref{prop:outside2}` (Proposition 22).** For `0 ≤ h` and `T > h + α̂_r`,
`(1/(2π)) ∫_{T-h-α̂_r}^{T+h+α̂_r} log|ζ(1+it)| dt ≤ Φ(1)/π`, where `Φ(1) < 1.7975699586287395`,
matching `ZerosInShortIntervals.tex` exactly (integration limits, `0 ≤ h`
hypothesis, and `≤` in place of the manuscript's unjustified `<`).**

### Summary of Proof
The source's proof derives this bound from `|Im Φ(s)| ≤ ‖Φ(s)‖ ≤ Φ(Re s).re`
(`Phi_norm_le`/`Complex.abs_im_le_norm`, both genuine triangle-inequality facts giving `≤`, not
`<`) applied at the two integration endpoints — promoting this to `<` would need a separate
non-degeneracy step (ruling out the triangle-inequality bound being exactly tight at both
endpoints simultaneously), not attempted here since Theorem `\ref{thm:rectangularjensen}`
(Theorem 24), the assembly this feeds, is itself stated with `≤` (as are `jensen_easy` and
`outside3`, which feed the same assembly). This theorem literally *is* `outside2_le` above, kept
as a separate name since it is Proposition `\ref{prop:outside2}` (Proposition 22) in the source.

### References
tex: Proposition `\ref{prop:outside2}` (Proposition 22).

### Dependencies
**Depends on:** `Phi`, `hatAlpha`, `outside2_le`.
**Used by:** none. -/
theorem outside2 {T h r α : ℝ} (hh : 0 ≤ h) (hTh : h + hatAlpha r α < T) :
    (1 / (2 * Real.pi)) *
        ∫ t in (T - h - hatAlpha r α)..(T + h + hatAlpha r α),
          Real.log ‖riemannZeta (1 + t * Complex.I)‖
      ≤ (Phi 1).re / Real.pi :=
  outside2_le hh hTh

/-! ### `Φ` restricted to the real axis

Six facts about `σ ↦ Φ(σ).re` for real `σ`, all specialisations of results in `Definitions.lean`
but not stated there. The first two are the *horizontal-ray* companions of
`Definitions.Phi_im_hasDerivAt` (which handles vertical lines), and are what every remaining
`Φ`-integral in this file runs on: `phi_cos_integral_eq_c5` uses both, and
`Phi_one_re_eq_integral` uses them together with `Phi_re_tendsto_atTop`.

**Migration note.** All six declarations in this section — `Phi_re_hasDerivAt`,
`Phi_re_continuousOn`, `LSeriesSummable_PhiTerm_of_one_le`, `Phi_re_nonneg`, `Phi_re_le_two_rpow`
and `Phi_re_tendsto_atTop` — are general-purpose statements about `Definitions.Phi` with nothing
rectangle-specific about them; they belong in `ZerosInShortIntervals/Definitions.lean` next to
`Phi_im_hasDerivAt`, `Phi_re_antitoneOn` and `Phi_continuousOn_closedHalfPlane`, and should be
migrated there when that file is next touched. -/

/-- **`Φ' = -log ζ` along the real axis:** for real `σ > 1`,
`(d/dσ) Φ(σ).re = -log‖ζ(σ)‖`.

### Summary of Proof
The horizontal-ray twin of `Definitions.Phi_im_hasDerivAt`, and strictly simpler: restrict
`Phi_hasDerivAt` (which gives `Φ'(s) = -G(s)` for `Re s > 1`) to the real axis with
`HasDerivAt.real_of_complex`, then rewrite the resulting `(-G(σ)).re` as `-log‖ζ(σ)‖` using
`Definitions.GTerm_LSeries_re_eq_log_norm`. No rotation by `-i` is needed — that step exists in
`Phi_im_hasDerivAt` only to convert a vertical direction into a real one.

### Lean Notes
Stated with the derivative evaluated at the *same* `σ` as the point, so it composes directly with
an inner function via `HasDerivAt.comp` (see `phi_cos_re_hasDerivAt`).

### References
No tex counterpart. `Φ` is Equation `\ref{eq:phis}` (Equation 12); the tex differentiates it
informally.

### Dependencies
**Depends on:** `GTerm_LSeries_re_eq_log_norm`, `Phi`, `Phi_hasDerivAt`.
**Used by:** `Phi_one_re_eq_integral`, `logzeta_integrableOn_Ioi_one`, `phi_cos_re_hasDerivAt`. -/
theorem Phi_re_hasDerivAt {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fun x : ℝ => (Phi (x : ℂ)).re) (-Real.log ‖riemannZeta (σ : ℂ)‖) σ := by
  have hsre : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hreal := (Phi_hasDerivAt hsre).real_of_complex
  rwa [Complex.neg_re, GTerm_LSeries_re_eq_log_norm hsre] at hreal

/-- **`σ ↦ Φ(σ).re` is continuous on `[1, ∞)`,** boundary point `σ = 1` included.

### Summary of Proof
`Definitions.Phi_continuousOn_closedHalfPlane` gives `ContinuousOn Phi {s | 1 ≤ s.re}`; compose
with the (continuous) real-to-complex coercion, which maps `[1,∞)` into that half-plane, and then
with `Complex.re`. Including `σ = 1` is exactly the content of `LSeriesSummable_PhiTerm_one`,
which is what makes `Φ(1)` a genuine value rather than a `tsum` junk value.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_continuousOn_closedHalfPlane`.
**Used by:** `Phi_one_re_eq_integral`, `logzeta_integrableOn_Ioi_one`, `phi_cos_re_continuousOn`.
-/
theorem Phi_re_continuousOn : ContinuousOn (fun σ : ℝ => (Phi (σ : ℂ)).re) (Set.Ici (1 : ℝ)) := by
  have hmapsto : Set.MapsTo (fun σ : ℝ => (σ : ℂ)) (Set.Ici (1 : ℝ)) {s : ℂ | 1 ≤ s.re} :=
    fun x hx => by simpa using hx
  have hcompPhi : ContinuousOn (fun σ : ℝ => Phi (σ : ℂ)) (Set.Ici 1) :=
    Phi_continuousOn_closedHalfPlane.comp Complex.continuous_ofReal.continuousOn hmapsto
  exact Complex.continuous_re.comp_continuousOn hcompPhi

/-- **`Φ`'s defining Dirichlet series converges for every real `σ ≥ 1`.**

### Summary of Proof
For `σ > 1` this is `LSeriesSummable_of_abscissaOfAbsConv_lt_re` together with
`Definitions.PhiTerm_abscissaOfAbsConv_le_one`; the boundary case `σ = 1` is exactly
`Definitions.LSeriesSummable_PhiTerm_one`, the Chebyshev-`ψ` bound. The same two-case split
appears inside `Definitions.Phi_re_antitoneOn`; it is factored out here because three lemmas below
need it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `LSeriesSummable_PhiTerm_one`, `PhiTerm`, `PhiTerm_abscissaOfAbsConv_le_one`.
**Used by:** `Phi_re_nonneg`, `Phi_re_le_two_rpow`. -/
theorem LSeriesSummable_PhiTerm_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) :
    LSeriesSummable PhiTerm ((σ : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hσ with h | h
  · rw [← h]; exact_mod_cast LSeriesSummable_PhiTerm_one
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt PhiTerm_abscissaOfAbsConv_le_one (by exact_mod_cast h))

/-- **`Φ(σ).re ≥ 0` for real `σ ≥ 1`.**

### Summary of Proof
Termwise: `Φ`'s coefficients are `Λ(n)/(log n)² ≥ 0` and the weights `n^{-σ}` are positive, so
every term of `Re Φ(σ) = ∑ Λ(n)/((log n)²n^σ)` is nonnegative. `Complex.re_tsum` moves the real
part inside the sum (legitimate by `LSeriesSummable_PhiTerm_of_one_le`) and `tsum_nonneg`
finishes.

### References
No tex counterpart.

### Dependencies
**Depends on:** `LSeriesSummable_PhiTerm_of_one_le`, `Phi`, `PhiTerm`, `PhiTerm_term_re`,
`Phi_eq_LSeries`.
**Used by:** `Phi_re_tendsto_atTop`, `ConstantSigns.two_Phi_one_add_c5_nonneg`,
`ConstantSigns.A6_nonneg`. -/
theorem Phi_re_nonneg {σ : ℝ} (hσ : 1 ≤ σ) : 0 ≤ (Phi ((σ : ℝ) : ℂ)).re := by
  rw [Phi_eq_LSeries]
  change (0 : ℝ) ≤ (∑' n : ℕ, LSeries.term PhiTerm ((σ : ℝ) : ℂ) n).re
  rw [Complex.re_tsum (LSeriesSummable_PhiTerm_of_one_le hσ)]
  refine tsum_nonneg (fun n => ?_)
  rw [PhiTerm_term_re]
  rcases le_or_gt n 1 with hn | hn
  · simp [hn]
  · rw [ite_eq_right (by omega : ¬ n ≤ 1)]
    apply div_nonneg
    · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg; positivity
    · positivity

/-- **`Φ(σ).re ≤ 2^{1-σ}·Φ(1).re` for real `σ ≥ 1`:** the geometric decay that forces
`Φ(σ) → 0`.

### Summary of Proof
Compare the two Dirichlet series term by term. `Φ`'s coefficients vanish for `n ≤ 1`, so every
surviving term has `n ≥ 2`; there
`n^{-σ} = n^{-1}·n^{1-σ} ≤ n^{-1}·2^{1-σ}`, because `1 - σ ≤ 0` makes `x ↦ x^{1-σ}` antitone
(`Real.rpow_le_rpow_of_nonpos`) and `n ≥ 2`. Multiplying by the nonnegative coefficient and
summing (`Summable.tsum_mono`, with `tsum_mul_left` pulling the constant out) gives the claim.

### Lean Notes
The "no constant term" fact — `PhiTerm n = 0` for `n ≤ 1` — is what the argument really turns on:
it is why the whole series, not just its tail, decays like `2^{1-σ}`. Without it the `n = 1` term
would be `σ`-independent and the bound would be false.

### References
No tex counterpart.

### Dependencies
**Depends on:** `LSeriesSummable_PhiTerm_of_one_le`, `Phi`, `PhiTerm`, `PhiTerm_term_re`,
`Phi_eq_LSeries`.
**Used by:** `Phi_re_tendsto_atTop`. -/
theorem Phi_re_le_two_rpow {σ : ℝ} (hσ : 1 ≤ σ) :
    (Phi ((σ : ℝ) : ℂ)).re ≤ (2 : ℝ) ^ (1 - σ) * (Phi 1).re := by
  have hs1 : LSeriesSummable PhiTerm ((1 : ℝ) : ℂ) := LSeriesSummable_PhiTerm_of_one_le le_rfl
  have hsσ : LSeriesSummable PhiTerm ((σ : ℝ) : ℂ) := LSeriesSummable_PhiTerm_of_one_le hσ
  have hone : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  have e1 : (Phi ((σ : ℝ) : ℂ)).re = ∑' n : ℕ, (LSeries.term PhiTerm ((σ : ℝ) : ℂ) n).re := by
    rw [Phi_eq_LSeries]
    change (∑' n : ℕ, LSeries.term PhiTerm ((σ : ℝ) : ℂ) n).re = _
    exact Complex.re_tsum hsσ
  have e2 : (Phi (1 : ℂ)).re = ∑' n : ℕ, (LSeries.term PhiTerm ((1 : ℝ) : ℂ) n).re := by
    rw [← hone, Phi_eq_LSeries]
    change (∑' n : ℕ, LSeries.term PhiTerm ((1 : ℝ) : ℂ) n).re = _
    exact Complex.re_tsum hs1
  rw [e1, e2, ← tsum_mul_left]
  refine Summable.tsum_mono ((Complex.hasSum_re hsσ.hasSum).summable)
    (((Complex.hasSum_re hs1.hasSum).summable).mul_left _) (fun n => ?_)
  simp only
  rw [PhiTerm_term_re, PhiTerm_term_re]
  rcases le_or_gt n 1 with hn | hn
  · simp [hn]
  · rw [ite_eq_right (by omega : ¬ n ≤ 1), Real.rpow_one]
    set c : ℝ := (ArithmeticFunction.vonMangoldt n) / (Real.log n) ^ 2 with hc
    have hc0 : 0 ≤ c := by
      rw [hc]; apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg; positivity
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hkey : (n : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)
    have hrs : (n : ℝ) ^ (1 - σ) = (n : ℝ) / (n : ℝ) ^ σ := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
    rw [hrs] at hkey
    have hcn : (0 : ℝ) ≤ c / (n : ℝ) := div_nonneg hc0 hnpos.le
    have hmul := mul_le_mul_of_nonneg_left hkey hcn
    calc c / (n : ℝ) ^ σ = c / (n : ℝ) * ((n : ℝ) / (n : ℝ) ^ σ) := by field_simp
      _ ≤ c / (n : ℝ) * (2 : ℝ) ^ (1 - σ) := hmul
      _ = (2 : ℝ) ^ (1 - σ) * (c / (n : ℝ)) := by ring

/-- **`Φ(σ).re → 0` as `σ → +∞` along the real axis.**

### Summary of Proof
Squeeze between `0` (`Phi_re_nonneg`) and `2^{1-σ}·Φ(1).re` (`Phi_re_le_two_rpow`), both valid
eventually (namely for `σ ≥ 1`), and the upper bound tends to `0` because `1 - σ → -∞` and
`2^· → 0` at `-∞` (`tendsto_rpow_atBot_of_base_gt_one`).

### Lean Notes
This is the limit that makes the improper integral `∫_1^∞ log ζ` converge to `Φ(1)`, and the
input `Phi_one_re_eq_integral` needs at the `+∞` endpoint.

### References
No tex counterpart — the tex takes `Φ(σ) → 0` for granted.

### Dependencies
**Depends on:** `Phi`, `Phi_re_le_two_rpow`, `Phi_re_nonneg`.
**Used by:** `Phi_one_re_eq_integral`, `logzeta_integrableOn_Ioi_one`. -/
theorem Phi_re_tendsto_atTop :
    Filter.Tendsto (fun σ : ℝ => (Phi ((σ : ℝ) : ℂ)).re) Filter.atTop (nhds 0) := by
  have hsub : Filter.Tendsto (fun σ : ℝ => 1 - σ) Filter.atTop Filter.atBot := by
    rw [Filter.tendsto_atBot]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (1 - b)] with σ hσ
    linarith
  have h2 : Filter.Tendsto (fun σ : ℝ => (2 : ℝ) ^ (1 - σ)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp hsub
  have h3 : Filter.Tendsto (fun σ : ℝ => (2 : ℝ) ^ (1 - σ) * (Phi 1).re)
      Filter.atTop (nhds 0) := by
    simpa using h2.mul_const ((Phi 1).re)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with σ hσ using Phi_re_nonneg hσ
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with σ hσ using Phi_re_le_two_rpow hσ

/-! ### `Φ(1)`: the analytic identity and the certified numeric bound

`Phi_one_lt` is split into two independent halves, so that neither mentions `Phi`'s
Dirichlet-series definition and the numeric constant in the same breath.

* The *analytic* half, `Phi_one_re_eq_integral`, identifies `Φ(1)` with an improper real integral,
  using only the `Φ`-real-axis lemmas of the previous section; `logzeta_integrableOn_Ioi_one`
  separately certifies that the integral converges, so the numeric half is not vacuously
  satisfiable.
* The *numeric* half, `integral_log_zeta_Ioi_one_lt`, is a bound on that explicit integral. It is
  not proved in Lean: it reads the class field
  `Hypotheses.NumericCertificates.integral_log_zeta_Ioi_one_lt`.
-/

/-- **Analytic half of `Phi_one_lt`: `Φ(1) = ∫_1^∞ log ζ(x) dx`.**

### Summary of Proof
`Φ` is an antiderivative of `−log ζ` along horizontal rays as well as vertical lines
(`Phi_re_hasDerivAt`), and `Φ(σ) → 0` as `σ → ∞` (`Phi_re_tendsto_atTop`, by the geometric
majorant `2^{1-σ}Φ(1)`). So for `1 < X`,
`Φ(1) − Φ(X) = ∫_1^X log ζ(x) dx`, and letting `X → ∞` gives the claim.
`Φ(1)` itself is well defined by `Definitions.LSeriesSummable_PhiTerm_one`, and
`Phi_continuousOn_closedHalfPlane` gives continuity up to the boundary `σ = 1`.

For real `x > 1` the value `ζ(x)` is real and `> 1`, so `log ‖ζ(x)‖ = log ζ(x) > 0`; the norm is
used here only to match the form of the other `Φ`-integrals in this file.

### Lean Notes
Applied to `g(σ) := -Φ(σ).re`, whose derivative `g' = log‖ζ‖` is **nonnegative** on `(1,∞)`
(`Definitions.log_zeta_norm_pos`). That sign is what makes
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` the right FTC lemma: it *derives*
integrability of `g'` on `(1,∞)` from monotonicity plus the limit at `+∞`, rather than demanding
it as a hypothesis. So no majorant like `log(1/(x−1))` has to be produced near the pole.
(`logzeta_integrableOn_Ioi_one` below records the integrability separately, since the statement
of this theorem does not expose it.)

The three inputs are `Phi_re_continuousOn` (left endpoint), `Phi_re_hasDerivAt` (the
horizontal-ray derivative) and `Phi_re_tendsto_atTop` (the limit at `+∞`).

### References
tex: `Φ` is Equation `\ref{eq:phis}` (Equation 12); the identity is the unnumbered display in the
proof of Proposition `\ref{prop:outside2}` (Proposition 22).

### Dependencies
**Depends on:** `Phi`, `Phi_re_continuousOn`, `Phi_re_hasDerivAt`, `Phi_re_tendsto_atTop`,
`log_zeta_norm_pos`.
**Used by:** `Phi_one_lt`. -/
theorem Phi_one_re_eq_integral :
    (Phi 1).re = ∫ x in Set.Ioi (1 : ℝ), Real.log ‖riemannZeta (x : ℂ)‖ := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re) (Set.Ici 1) 1 :=
    (Phi_re_continuousOn 1 (Set.mem_Ici.mpr le_rfl)).neg
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re)
        (Real.log ‖riemannZeta ((x : ℝ) : ℂ)‖) x := by
    intro x hx
    exact ((Phi_re_hasDerivAt (Set.mem_Ioi.mp hx)).neg).congr_deriv (by ring)
  have hpos : ∀ x ∈ Set.Ioi (1 : ℝ), (0 : ℝ) ≤ Real.log ‖riemannZeta ((x : ℝ) : ℂ)‖ :=
    fun x hx => (log_zeta_norm_pos (Set.mem_Ioi.mp hx)).le
  have hlim : Filter.Tendsto (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re) Filter.atTop (nhds 0) := by
    simpa using Phi_re_tendsto_atTop.neg
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  norm_num

/-- **`log‖ζ‖` really is Bochner integrable on `(1, ∞)`.**

### Summary of Proof
Same four inputs as `Phi_one_re_eq_integral`, fed to
`MeasureTheory.integrableOn_Ioi_deriv_of_nonneg` instead of its integral-evaluating companion: a
nonnegative derivative whose antiderivative has a finite limit at `+∞` is automatically
integrable.

### Lean Notes
Stated separately because `Phi_one_re_eq_integral` asserts only an equality of values, and Lean's
`∫` returns `0` for a non-integrable function — so that equality alone would not rule out the
degenerate reading. With this lemma in hand the pair
`Phi_one_re_eq_integral`/`integral_log_zeta_Ioi_one_lt` has no junk-value escape hatch: the
integral in both is a genuine convergent integral. See "No junk-value escape hatch" in
`integral_log_zeta_Ioi_one_lt`'s docstring.

### References
No tex counterpart — the tex writes the improper integral without comment on convergence.

### Dependencies
**Depends on:** `Phi`, `Phi_re_continuousOn`, `Phi_re_hasDerivAt`, `Phi_re_tendsto_atTop`,
`log_zeta_norm_pos`.
**Used by:** none — it certifies the meaningfulness of `integral_log_zeta_Ioi_one_lt`. -/
theorem logzeta_integrableOn_Ioi_one :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℝ) : ℂ)‖)
      (Set.Ioi (1 : ℝ)) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re) (Set.Ici 1) 1 :=
    (Phi_re_continuousOn 1 (Set.mem_Ici.mpr le_rfl)).neg
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re)
        (Real.log ‖riemannZeta ((x : ℝ) : ℂ)‖) x := by
    intro x hx
    exact ((Phi_re_hasDerivAt (Set.mem_Ioi.mp hx)).neg).congr_deriv (by ring)
  have hpos : ∀ x ∈ Set.Ioi (1 : ℝ), (0 : ℝ) ≤ Real.log ‖riemannZeta ((x : ℝ) : ℂ)‖ :=
    fun x hx => (log_zeta_norm_pos (Set.mem_Ioi.mp hx)).le
  have hlim : Filter.Tendsto (fun x : ℝ => -(Phi ((x : ℝ) : ℂ)).re) Filter.atTop (nhds 0) := by
    simpa using Phi_re_tendsto_atTop.neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim

/-- **Numerical half of `Phi_one_lt`: `∫_1^∞ log ζ(x) dx < 1.7975699586287395`.**

**A hypothesis, not a Lean proof**: the body reads the class field
`Hypotheses.NumericCertificates.integral_log_zeta_Ioi_one_lt`. The source justifies it "from an
explicit rigorous computation of the defining integral".

### Summary of Proof
`NumericCertificates.integral_log_zeta_Ioi_one_lt`. Outside Lean the integral is bounded by
certified ball arithmetic (splitting off a `[1,1+δ]` near-pole piece and a `[T,∞)` tail, both
bounded in closed form, with the bulk `[1+δ,T]` evaluated by arb's certified adaptive quadrature)
in `Code/verify_Phi_one_bound.sage`, giving an upper bound `1.79756995862873940793…` with error
radius `~2×10⁻⁹³` — margin `~9.2×10⁻¹⁷` below the stated constant.

The statement does not mention `Phi`: it is a self-contained bound on an explicit real integral
of `log ‖ζ‖` along the real axis, which is what the Sage script certifies.

### Lean Notes
Mathlib has no verified evaluation of `ζ`, and the margin is `~9.2×10⁻¹⁷`, so a Lean-side
reproduction would have to carry ~20 digits; that is why this is a certificate field rather than
a proof.

**No junk-value escape hatch.** Taken alone this statement would be *vacuously true* if
`log ‖ζ(·)‖` were not Bochner integrable on `(1,∞)`: Lean's `∫` returns `0` then, and
`0 < 1.797…`. `logzeta_integrableOn_Ioi_one` above closes that by proving the integrand genuinely
integrable on `(1,∞)`, and `Phi_one_re_eq_integral` identifies the integral's value with
`(Phi 1).re`. The three should be read together.

### References
tex: `Φ(1) < 1.7975699586287395` is the "Moreover" clause of Proposition `\ref{prop:outside2}`
(Proposition 22).

**Independent numeric check.** `Code/indep_mpmath_constants.py` block [B] evaluates the integral
by a different route from the Sage script — the logarithmic singularity at `x = 1` is split off
analytically (`∫_1^2 -log(x-1) dx = 1`, plus the smooth `log((x-1)ζ(x))`), the tail by quadrature
to `∞` — and gets `Φ(1) = 1.79756995862873940793…`, a margin of `9.2×10⁻¹⁷` below the stated
bound (two different split points agree to 50 digits).

### Dependencies
**Depends on:** `Hypotheses.NumericCertificates.integral_log_zeta_Ioi_one_lt`.
**Used by:** `Phi_one_lt`. -/
theorem integral_log_zeta_Ioi_one_lt :
    (∫ x in Set.Ioi (1 : ℝ), Real.log ‖riemannZeta (x : ℂ)‖) < 1.7975699586287395 :=
  NumericCertificates.integral_log_zeta_Ioi_one_lt

/-- **`Φ(1) < 1.7975699586287395`, the "Moreover" clause of Proposition
`\ref{prop:outside2}` (Proposition 22).** Conditional on `NumericCertificates`, through
`integral_log_zeta_Ioi_one_lt`.

### Summary of Proof
Immediate from the two halves: the analytic identity `Phi_one_re_eq_integral` and the certificate
field `integral_log_zeta_Ioi_one_lt`.

### References
tex: `Φ(1) < 1.7975699586287395` is the "Moreover" clause of Proposition `\ref{prop:outside2}`
(Proposition 22); `Φ` is Equation `\ref{eq:phis}` (Equation 12).

### Dependencies
**Depends on:** `Phi`, `Phi_one_re_eq_integral`, `integral_log_zeta_Ioi_one_lt`.
**Used by:** none. -/
theorem Phi_one_lt : (Phi 1).re < 1.7975699586287395 := by
  rw [Phi_one_re_eq_integral]
  exact integral_log_zeta_Ioi_one_lt

/-- **`c_{5,r}` from Proposition `\ref{prop:outside3}` (Proposition 23):
`c_{5,r} = Φ(1+r) + (2r/π) ∫_0^1 log ζ(1+ru) arcsin(u) du`.**

### Summary of Proof
A definition, transcribing the source's `c_{5,r}` verbatim. The `+` in front of the integral is
the sign Lean-checks in `phi_cos_integral_eq_c5`; the integral converges because
`log ζ(1+ru)·arcsin u` has only a logarithmic singularity at `u = 0`, where `1+ru` meets `ζ`'s
pole (`logzeta_arcsin_integrable`).

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `Phi`.
**Used by:** `B4`, `outside3`, `outside3_lt`, `phi_cos_integral_eq_c5`, `rectangularjensen`,
`rectangularjensen_tight`, `ConstantSigns.two_Phi_one_add_c5_nonneg`. -/
noncomputable def c5 (r : ℝ) : ℝ :=
  (Phi (1 + r : ℂ)).re
    + (2 * r / Real.pi) * ∫ u in (0 : ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u

/-! ### Proposition `\ref{prop:outside3}` (Proposition 23): the shape of the statement

`outside3` is stated below, after the pieces it is assembled from: for `0 < r`, `0 ≤ h` and
`T > h + α̂_r`,
`|∫_{-h-α̂_r}^{h+α̂_r} (1/(2π)) ∫_{-π/2}^{π/2} log|ζ(1+i(T+x)+re^{iθ})| dθ dx| ≤ c_{5,r}`.
Three features of that statement are recorded here rather than in the source.

### Summary of Proof
**Why `≤` and not `<`.** The source's proof exchanges the order of integration and then bounds
`Re(Φ(a)-Φ(b))` by `2·Φ(1+r cos θ).re` — the `Phi_norm_le` triangle-inequality mechanism of
`outside2_of_one_lt`, which is genuinely `≤`. Upgrading to `<` would need a separate
non-degeneracy argument, which the source does not give and nothing downstream needs: Theorem
`\ref{thm:rectangularjensen}` (Theorem 24), the only consumer, is itself stated with `≤`.

**Why an absolute value.** The triangle inequality bounds `|Im(Φ(a) - Φ(b))|` rather than one
sign of it. `rectangularjensen` needs the *positive* direction, where `jensenrectangle`'s
numerator carries the inside-strip half-circle average with a `+`; `outside2_of_one_lt` and
`LittlewoodMethod.littlewood_outerlog_of_one_lt` are the two signs of that same argument.

**Why the sign in `c5` is `+`.** In the integration by parts of step 3 below, `Φ`'s real-axis
derivative is `Φ'(σ) = -log ζ(σ)` (`Phi_re_hasDerivAt`, so `Φ` is decreasing on `(1,∞)`, matching
the termwise decrease of its defining series), and the inner map `θ ↦ 1 + r cos θ` has derivative
`-r sin θ`; the two minus signs cancel (`phi_cos_re_hasDerivAt`). The same cancellation appears in
`JensenBounds.integraloutside_bound`'s structurally analogous IBP, which reproduces `c4 r`'s
closed form sign-for-sign. `phi_cos_integral_eq_c5` checks it in Lean.

See `outside3_lt` below for the explicit closed-form bound built from `c5`, proved via a *direct*
upper bound on `log ζ(1+ru)` rather than a second integration by parts (see that theorem's
docstring for why that route is taken, and for the resulting closed form).

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23).
-/

/-! ### `outside3` in full: the three steps

Writing `a := h + α̂_r` and `A` for the double integral, the chain is

1.  at each fixed `θ ∈ (-π/2, π/2)` the inner `x`-integral is a vertical `Φ`-FTC integral, so
    `|∫_{-a}^{a} log‖ζ(1+i(T+x)+re^{iθ})‖ dx| ≤ 2·Φ(1+r cos θ).re`
    — `outside3_theta_slice_le`, from `abs_integral_log_zeta_vertical_le`;
2.  Fubini plus `|∫| ≤ ∫|·|` plus (1) give `|A| ≤ (1/π)∫_{-π/2}^{π/2} Φ(1+r cos θ).re dθ`
    — `outside3_fubini_bound`. Its two side conditions are the substance: the exchange itself
    (`outside3_fubini_swap`, resting on the joint integrability `outside3_integrableOn_rect`)
    and the `θ`-integrability of the inner integral
    (`outside3_inner_abs_intervalIntegrable`);
3.  that `θ`-integral equals `c_{5,r}` — `phi_cos_integral_eq_c5`, by integration by parts in `θ`
    (`phi_cos_integral_quarter`) followed by the substitution `u = cos θ`
    (`integral_sin_mul_logzeta_comp_cos`). This is also what **Lean-checks the `+` sign** in
    `c5`, as the section comment above explains.

Both places where the integrand's blow-up at `θ = ±π/2` had to be faced are handled the same way:
the offending `θ`-values form a **null set**, so the identity or continuity that fails there is
simply not needed. In step 2 that is `Ioo` versus `Ioc` inside `outside3_integrableOn_rect`, and
`integral_mono_on_of_le_Ioo` in `outside3_fubini_bound`; in
`outside3_inner_abs_intervalIntegrable` it is the same `Ioo`/`Ioc` move again.

**Why `outside3` carries `0 < r` and `0 ≤ h`, which the source does not state.** Steps 1–3 all
need `0 < r`, to keep `1 + r cos θ > 1` off `ζ`'s pole and to make `Φ(1+r)` — hence `c5 r` —
converge at all: without it, `r < 0` would compare against a `c5 r` built from a divergent
series, i.e. a Lean junk value. And `0 ≤ h` is not implied by `T > h + α̂_r`. Both callers
(`rectangularjensen`, `rectangularjensen_tight`) have `0 < α < r` and `0 < h` in scope, so
nothing downstream is constrained by them. The tex is unaffected: `r > 0` is standing throughout
Section `\ref{sec:rectangularjensen}` (Section 2). -/

/-- **The `θ`-slice of `outside3` as a vertical-segment integral.** For every `T, a, r, θ`,
`∫_{-a}^{a} log‖ζ(1+i(T+x)+re^{iθ})‖ dx = ∫_{d-a}^{d+a} log‖ζ((1+r cos θ)+it)‖ dt`, where
`d = T + r sin θ`.

### Summary of Proof
The point `1 + i(T+x) + re^{iθ}` has real part `1 + r cos θ` and imaginary part `T + x + r sin θ`,
so at fixed `θ` the inner integral *is* a vertical-segment integral on the line
`Re s = 1 + r cos θ`, centred at height `d = T + r sin θ` with half-width `a`. The translation
`x ↦ d + x` is `intervalIntegral.integral_comp_add_left`.

### Lean Notes
A pure change of variable: **no hypotheses at all**, in particular neither `0 < r` nor
`cos θ > 0`. Those are needed only by the vertical-line lemmas this feeds, and keeping them out
here is what lets both `outside3_theta_slice_le` and `outside3_theta_slice_eq` be one-liners on
top of it rather than repeating the translation.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), the inner `x`-integral of its proof.

### Dependencies
**Depends on:** none.
**Used by:** `outside3_theta_slice_le`, `outside3_theta_slice_eq`. -/
theorem outside3_slice_translate (T a r θ : ℝ) :
    (∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      = ∫ t in (T + r * Real.sin θ - a)..(T + r * Real.sin θ + a),
          Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set σ : ℝ := 1 + r * Real.cos θ with hσ_def
  set d : ℝ := T + r * Real.sin θ with hd_def
  -- the integrand is `f (d + x)` for the vertical-line function `f`
  have hpt : ∀ x : ℝ,
      (1 : ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        = (σ : ℂ) + ((d + x : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hσ_def, hd_def]
    push_cast
    ring
  have hrw : (fun x : ℝ =>
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      = fun x : ℝ => (fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
          (d + x) := by
    funext x
    simp only
    rw [hpt x]
  rw [hrw, intervalIntegral.integral_comp_add_left
    (f := fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) d]
  have hbounds : d + -a = d - a := by ring
  rw [hbounds]

/-- **The `θ`-slice of `outside3`:** at fixed `θ` with `cos θ > 0`, the inner `x`-integral is
bounded by `2·Φ(1+r cos θ).re`.

### Summary of Proof
`outside3_slice_translate` turns the inner integral into a vertical-segment integral on the line
`Re s = 1 + r cos θ`, which is exactly the shape `abs_integral_log_zeta_vertical_le` bounds.

`cos θ > 0` and `0 < r` put `1 + r cos θ > 1`, which is that lemma's hypothesis: the whole
half-disc `Re > 1` stays clear of `ζ`'s pole, which is why this slice needs no `ε`-argument.

### Lean Notes
This is step (1) of the reduction described above. It is stated over a free half-width `a` rather
than `h + α̂_r`, so the `Fubini` step can use it uniformly in `θ`.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), the inner `x`-integral of its proof.

### Dependencies
**Depends on:** `Phi`, `abs_integral_log_zeta_vertical_le`, `outside3_slice_translate`.
**Used by:** `outside3_fubini_bound`. -/
theorem outside3_theta_slice_le {T a r θ : ℝ} (hr : 0 < r) (hcos : 0 < Real.cos θ) :
    |∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|
      ≤ 2 * (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
  have hσ : (1 : ℝ) < 1 + r * Real.cos θ := by nlinarith
  rw [outside3_slice_translate T a r θ]
  exact abs_integral_log_zeta_vertical_le
    (σ := 1 + r * Real.cos θ) (T := T + r * Real.sin θ) (h' := a) hσ

/-- **The `θ`-slice of `outside3` in closed form:** at fixed `θ` with `cos θ > 0`, the inner
`x`-integral equals `Φ(σ + i(d-a)).im - Φ(σ + i(d+a)).im`, with `σ = 1 + r cos θ` and
`d = T + r sin θ`.

### Summary of Proof
`outside3_slice_translate` followed by `integral_log_zeta_vertical_eq`.

### Lean Notes
The sharpening of `outside3_theta_slice_le` from a bound to an identity, and the reason it exists:
the right-hand side is manifestly **continuous in `θ` on the closed interval `[-π/2, π/2]`** (by
`Phi_continuousOn_closedHalfPlane`, since `Re = 1 + r cos θ ≥ 1` there), whereas the left-hand
side is an integral whose `θ`-regularity is not otherwise apparent. That is what proves
`outside3_inner_abs_intervalIntegrable`, and the endpoints `θ = ±π/2` — where this identity is
*not* claimed, `cos θ` being `0` there — are a null set, so they do not obstruct integrability.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), the inner `x`-integral of its proof.

### Dependencies
**Depends on:** `Phi`, `integral_log_zeta_vertical_eq`, `outside3_slice_translate`.
**Used by:** `outside3_inner_abs_intervalIntegrable`. -/
theorem outside3_theta_slice_eq {T a r θ : ℝ} (hr : 0 < r) (hcos : 0 < Real.cos θ) :
    (∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      = (Phi (((1 + r * Real.cos θ : ℝ) : ℂ)
            + ((T + r * Real.sin θ - a : ℝ) : ℂ) * Complex.I)).im
        - (Phi (((1 + r * Real.cos θ : ℝ) : ℂ)
            + ((T + r * Real.sin θ + a : ℝ) : ℂ) * Complex.I)).im := by
  have hσ : (1 : ℝ) < 1 + r * Real.cos θ := by nlinarith
  rw [outside3_slice_translate T a r θ]
  exact integral_log_zeta_vertical_eq
    (σ := 1 + r * Real.cos θ) (T := T + r * Real.sin θ) (h' := a) hσ

/-- **`θ ↦ Φ(1+r cos θ).re` is continuous on `[-π/2, π/2]`,** endpoints included.

### Summary of Proof
On `[-π/2, π/2]` one has `cos θ ≥ 0`, so `1 + r cos θ ≥ 1` for `r > 0`; compose
`Phi_re_continuousOn` with `θ ↦ 1 + r cos θ`. The endpoints `θ = ±π/2` are the delicate ones —
there `1 + r cos θ = 1` sits exactly on `ζ`'s pole — and they are covered precisely because
`Phi_re_continuousOn` reaches the boundary `σ = 1`.

### Lean Notes
This one lemma does four separate jobs: in `outside3_fubini_bound` it supplies the integrability
of the `Φ`-majorant on the closed `θ`-interval, and in `phi_cos_integral_quarter` it supplies the
integrability of the `Φ` summand of the integration-by-parts identity, **both** endpoint limits of
that identity, and (in `phi_cos_integral_eq_c5`) the integrability needed to split the
`[-π/2, π/2]` integral at `θ = 0` for the evenness step.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_re_continuousOn`.
**Used by:** `outside3_fubini_bound`, `phi_cos_integral_quarter`, `phi_cos_integral_eq_c5`. -/
theorem phi_cos_re_continuousOn {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hmaps : Set.MapsTo (fun θ : ℝ => 1 + r * Real.cos θ)
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) (Set.Ici (1 : ℝ)) := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩
    simp only [Set.mem_Ici]
    nlinarith
  exact Phi_re_continuousOn.comp (by fun_prop) hmaps

/-- **`θ ↦ Φ((1+r cos θ) + i·b(θ)).im` is continuous on `[-π/2, π/2]`** for any continuous real
`b`.

### Summary of Proof
On `[-π/2, π/2]` one has `cos θ ≥ 0`, so the point `(1+r cos θ) + i b(θ)` has real part `≥ 1` and
lies in the closed half-plane where `Definitions.Phi_continuousOn_closedHalfPlane` gives
continuity of `Φ`. Compose with the (continuous) parametrisation and with `Complex.im`.

### Lean Notes
Stated for an arbitrary continuous `b` so that the two instances needed by
`outside3_inner_abs_intervalIntegrable` — `b(θ) = T + r sin θ ∓ a` — are the *same* lemma. The
endpoints `θ = ±π/2` are included: that is the whole point, and it works only because `Φ`
converges at `σ = 1` (`Definitions.LSeriesSummable_PhiTerm_one`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_continuousOn_closedHalfPlane`.
**Used by:** `outside3_inner_abs_intervalIntegrable`. -/
theorem phi_slice_continuousOn {r : ℝ} (hr : 0 < r) {b : ℝ → ℝ} (hb : Continuous b) :
    ContinuousOn
      (fun θ : ℝ => (Phi (((1 + r * Real.cos θ : ℝ) : ℂ) + ((b θ : ℝ) : ℂ) * Complex.I)).im)
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hmaps : Set.MapsTo
      (fun θ : ℝ => ((1 + r * Real.cos θ : ℝ) : ℂ) + ((b θ : ℝ) : ℂ) * Complex.I)
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) {z : ℂ | 1 ≤ z.re} := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩
    have hre : (1 : ℝ)
        ≤ (((1 + r * Real.cos θ : ℝ) : ℂ) + ((b θ : ℝ) : ℂ) * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      nlinarith
    exact hre
  have hcont : ContinuousOn
      (fun θ : ℝ => Phi (((1 + r * Real.cos θ : ℝ) : ℂ) + ((b θ : ℝ) : ℂ) * Complex.I))
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    Phi_continuousOn_closedHalfPlane.comp (by fun_prop) hmaps
  exact Complex.continuous_im.comp_continuousOn hcont

/-- **The inner `x`-integral of `outside3` is interval integrable in `θ` (in absolute value).**

### Summary of Proof
By `outside3_theta_slice_eq`, on the *open* interval `(-π/2, π/2)` — where `cos θ > 0` — the
function `θ ↦ |∫_{-a}^{a} log‖ζ(1+i(T+x)+re^{iθ})‖ dx|` coincides with
`J(θ) := |Φ(σ(θ)+i(d(θ)-a)).im - Φ(σ(θ)+i(d(θ)+a)).im|`, `σ(θ) = 1+r cos θ`,
`d(θ) = T+r sin θ`. And `J` is continuous on the **closed** interval `[-π/2, π/2]`
(`phi_slice_continuousOn`), hence integrable there. Since `(-π/2, π/2)` and `(-π/2, π/2]` differ
by a null set, integrability transfers.

### Lean Notes
One of the two integrability side conditions of `outside3_fubini_bound`. The point is that the
slice identity is needed only *almost everywhere*: the two endpoints `θ = ±π/2`, where it
genuinely fails to be available (there `1 + r cos θ = 1`, on `ζ`'s pole, and `Phi_im_hasDerivAt`
has no `σ = 1` version), form a null set and are discarded by passing from `Ioc` to `Ioo`.

### References
No tex counterpart — the tex does not remark on this integrability.

### Dependencies
**Depends on:** `Phi`, `outside3_theta_slice_eq`, `phi_slice_continuousOn`.
**Used by:** `outside3_fubini_bound`. -/
theorem outside3_inner_abs_intervalIntegrable {T a r : ℝ} (hr : 0 < r) :
    IntervalIntegrable
      (fun θ : ℝ => |∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  have hhalf : (-Real.pi / 2 : ℝ) ≤ Real.pi / 2 := by linarith
  set J : ℝ → ℝ := fun θ =>
    |(Phi (((1 + r * Real.cos θ : ℝ) : ℂ)
        + ((T + r * Real.sin θ - a : ℝ) : ℂ) * Complex.I)).im
      - (Phi (((1 + r * Real.cos θ : ℝ) : ℂ)
        + ((T + r * Real.sin θ + a : ℝ) : ℂ) * Complex.I)).im| with hJ_def
  have hJcont : ContinuousOn J (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
    rw [hJ_def]
    exact ((phi_slice_continuousOn hr
        (b := fun θ : ℝ => T + r * Real.sin θ - a) (by fun_prop)).sub
      (phi_slice_continuousOn hr
        (b := fun θ : ℝ => T + r * Real.sin θ + a) (by fun_prop))).abs
  have hJIcc : MeasureTheory.IntegrableOn J (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    hJcont.integrableOn_Icc
  have hsubIoo : Set.Ioo (-Real.pi / 2) (Real.pi / 2)
      ⊆ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], le_of_lt hx.2⟩
  have hJIoo : MeasureTheory.IntegrableOn J (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :=
    hJIcc.mono_set hsubIoo
  have heqOn : Set.EqOn J
      (fun θ : ℝ => |∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|)
      (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    simp only [hJ_def]
    rw [outside3_theta_slice_eq (T := T) (a := a) hr hcos]
  have hIoo := hJIoo.congr_fun heqOn measurableSet_Ioo
  have hIoc := hIoo.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc).symm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
  exact hIoc

/-- **`|log‖ζ(s)‖| ≤ log ζ(Re s)` for `Re s > 1`** — the two-sided Dirichlet-series domination.

### Summary of Proof
`Definitions.GTerm_LSeries_re_eq_log_norm` identifies `log‖ζ(s)‖` with `Re G(s)`, where
`G(s) = ∑ Λ(n)/(log n)·n^{-s}` has **nonnegative** coefficients. Hence
`|Re G(s)| ≤ ‖G(s)‖ ≤ ∑ ‖term‖ = ∑ Λ(n)/(log n)·n^{-Re s} = Re G(Re s) = log ζ(Re s)`.
Exactly the argument of `Definitions.Phi_norm_le`, with `GTerm` in place of `PhiTerm`.

### Lean Notes
This is the two-sided companion of `Definitions.zeta_norm_le_zeta_re`, which gives only
`‖ζ(s)‖ ≤ ζ(Re s)` (i.e. the upper half). The lower half — `‖ζ(s)‖ ≥ 1/ζ(Re s)` — is what makes
this a *majorant* for `|log‖ζ‖|` rather than a one-sided bound, and it is what
`outside3_integrableOn_rect` needs: an integrable dominating function, not an upper bound.

**Migration note.** This is a general fact about `ζ` with nothing rectangle-specific about it; it
belongs in `ZerosInShortIntervals/Definitions.lean` beside `zeta_norm_le_zeta_re` and `Phi_norm_le`,
and should be migrated there when that file is next touched.

### References
No tex counterpart — the tex uses only the one-sided bound, in Proposition
`\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `GTerm_abscissaOfAbsConv_le_one`,
`GTerm_eq_ofReal`.
**Used by:** `outside3_integrableOn_rect`. -/
theorem abs_log_zeta_norm_le {w : ℂ} (hw : 1 < w.re) :
    |Real.log ‖riemannZeta w‖| ≤ Real.log ‖riemannZeta ((w.re : ℝ) : ℂ)‖ := by
  have hwre : (1 : ℝ) < ((w.re : ℝ) : ℂ).re := by simpa using hw
  have hsum : LSeriesSummable GTerm ((w.re : ℝ) : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt GTerm_abscissaOfAbsConv_le_one (by exact_mod_cast hw))
  have hterm_eq : ∀ n : ℕ,
      ‖LSeries.term GTerm w n‖ = (LSeries.term GTerm ((w.re : ℝ) : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hpow : (n : ℂ) ^ ((w.re : ℝ) : ℂ) = (((n : ℝ) ^ w.re : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (Nat.cast_nonneg n) w.re).symm
      have hxnn : (0 : ℝ) ≤
          if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt n) / (Real.log n) := by
        split_ifs with h
        · exact le_refl 0
        · have h1 : (1 : ℕ) ≤ n := by omega
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.log_nonneg (by exact_mod_cast h1))
      simp only [LSeries.term, ite_eq_right hn, GTerm_eq_ofReal]
      rw [hpow, ← Complex.ofReal_div, Complex.ofReal_re, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hxnn]
  have hsumnorm : Summable (fun n => ‖LSeries.term GTerm w n‖) := by
    simpa only [hterm_eq] using (Complex.hasSum_re hsum.hasSum).summable
  have hchain : ‖LSeries GTerm w‖ ≤ (LSeries GTerm ((w.re : ℝ) : ℂ)).re := by
    calc ‖LSeries GTerm w‖ ≤ ∑' n, ‖LSeries.term GTerm w n‖ := norm_tsum_le_tsum_norm hsumnorm
      _ = ∑' n, (LSeries.term GTerm ((w.re : ℝ) : ℂ) n).re := tsum_congr hterm_eq
      _ = (∑' n, LSeries.term GTerm ((w.re : ℝ) : ℂ) n).re := (Complex.re_tsum hsum).symm
      _ = (LSeries GTerm ((w.re : ℝ) : ℂ)).re := rfl
  rw [← GTerm_LSeries_re_eq_log_norm hw, ← GTerm_LSeries_re_eq_log_norm hwre]
  have habs := abs_le.mp (Complex.abs_re_le_norm (LSeries GTerm w))
  rw [abs_le]
  constructor <;> linarith [habs.1, habs.2, hchain]

/-- **`Re(1 + i(T+x) + re^{iθ}) = 1 + r cos θ`.**

### Summary of Proof
`Complex.exp_mul_I` expands `e^{iθ}` as `cos θ + i sin θ`; the `i(T+x)` term is purely imaginary,
so only `1` and `r cos θ` survive in the real part.

### Lean Notes
Trivial, but stated because both `outside3_integrableOn_rect`'s continuity argument and its
majorant bound need it, and inlining it twice would obscure them.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `outside3_integrableOn_rect`. -/
theorem circle_point_re (T r x θ : ℝ) :
    ((1 : ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = 1 + r * Real.cos θ := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  ring

/-- **Interval integrability of `θ ↦ log‖ζ(1+r cos θ)‖`,** in the real-coercion form.

### Summary of Proof
`JensenBounds.intervalIntegrable_log_zeta_cos` states exactly this with the argument written as
`(1 : ℂ) + r·Complex.cos θ`; `Complex.ofReal_cos` reconciles the two spellings.

### Lean Notes
The singularity at `cos θ = 0`, where `1 + r cos θ` sits on `ζ`'s pole, is only logarithmic, which
is why the interval integral exists across it; that is `intervalIntegrable_log_zeta_cos`'s content,
via `MeromorphicOn.intervalIntegrable_log_norm`. This lemma is what makes the majorant of
`outside3_integrableOn_rect` integrable in `θ` right up to the endpoints `±π/2`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `intervalIntegrable_log_zeta_cos`.
**Used by:** `integral_sin_mul_logzeta_comp_cos`, `outside3_integrableOn_rect`,
`phi_cos_integral_quarter`. -/
theorem logzeta_cos_intervalIntegrable_ofReal {r a b : ℝ} : IntervalIntegrable
    (fun θ : ℝ => Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖)
    MeasureTheory.volume a b := by
  have h : IntervalIntegrable
      (fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (r : ℂ) * Complex.cos (θ : ℂ))‖)
      MeasureTheory.volume a b := intervalIntegrable_log_zeta_cos
  have heq : (fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (r : ℂ) * Complex.cos (θ : ℂ))‖)
      = fun θ : ℝ => Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖ := by
    funext θ; rw [← Complex.ofReal_cos]; norm_num
  rwa [heq] at h

/-- **Joint integrability of `(x,θ) ↦ log‖ζ(1+i(T+x)+re^{iθ})‖` on the rectangle.** This is
Fubini's hypothesis for `outside3_fubini_swap`, and the only real content of that step.

### Summary of Proof
Two ingredients, both uniform in `x`.

*Measurability.* On `Ioc(-a,a) ×ˢ Ioo(-π/2,π/2)` the point `1+i(T+x)+re^{iθ}` has real part
`1 + r cos θ > 1` (`circle_point_re`, `cos θ > 0`), so it avoids both `ζ`'s pole at `1` and its
zeros, and the integrand is **continuous** there. `ContinuousOn.aestronglyMeasurable` then gives
a.e.-strong-measurability.

*Domination.* `abs_log_zeta_norm_le` bounds `|log‖ζ(s)‖|` by `log ζ(Re s) = log ζ(1 + r cos θ)`,
which does not involve `x` at all. That majorant is integrable in `θ`
(`logzeta_cos_intervalIntegrable_ofReal` — the singularity at `θ = ±π/2` is logarithmic) and
constant in `x`, so `Integrable.mul_prod` against the constant `1` on the bounded `x`-interval
makes it integrable on the rectangle. `Integrable.mono'` concludes.

Finally the `θ`-interval is enlarged from `Ioo` back to the `Ioc` that
`intervalIntegral_intervalIntegral_swap` asks for; the two differ by `Ioc(-a,a) × {π/2}`, of
product measure `(finite)·0 = 0`.

### Lean Notes
The whole point of using `Ioo` for `θ` in the middle of the proof is that `cos θ > 0` there, which
is what keeps the integrand continuous; at `θ = π/2` (which `Ioc` contains) the point sits exactly
on `ζ`'s pole. Since that is a single `θ`-value, it is a null set of the rectangle and can simply
be added back at the end.

The majorant being **independent of `x`** is what makes this easy: the two-dimensional
integrability question collapses to the one-dimensional one already solved for
`logzeta_cos_intervalIntegrable_ofReal`.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23); the tex exchanges the order of
integration without remarking on convergence.

### Dependencies
**Depends on:** `abs_log_zeta_norm_le`, `circle_point_re`,
`logzeta_cos_intervalIntegrable_ofReal`.
**Used by:** `outside3_fubini_swap`. -/
theorem outside3_integrableOn_rect {T a r : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn
      (Function.uncurry fun x θ : ℝ =>
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      (Set.uIoc (-a) a ×ˢ Set.uIoc (-Real.pi / 2) (Real.pi / 2)) := by
  have hpi := Real.pi_pos
  have hna : (-a : ℝ) ≤ a := by linarith
  have hhalf : (-Real.pi / 2 : ℝ) ≤ Real.pi / 2 := by linarith
  rw [Set.uIoc_of_le hna, Set.uIoc_of_le hhalf]
  set M : ℝ → ℝ := fun θ => Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖ with hM
  -- on the rectangle with `θ` in the OPEN interval the point stays off `ζ`'s pole
  have hkey : ∀ p : ℝ × ℝ, p ∈ Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2) →
      1 < ((1 : ℂ) + ((T : ℂ) + (p.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)).re := by
    intro p hp
    have hcos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1], hp.2.2⟩
    rw [circle_point_re T r p.1 p.2]
    nlinarith
  have hcont : ContinuousOn
      (Function.uncurry fun x θ : ℝ =>
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    intro p hp
    have hgre := hkey p hp
    have hne : (1 : ℂ) + ((T : ℂ) + (p.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) ≠ 1 := by
      intro h
      rw [h] at hgre
      simp only [Complex.one_re] at hgre
      linarith
    have hgc : ContinuousAt (fun q : ℝ × ℝ => (1 : ℂ) + ((T : ℂ) + (q.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)) p := by fun_prop
    have hzc : ContinuousAt (fun q : ℝ × ℝ => riemannZeta ((1 : ℂ) + ((T : ℂ) + (q.1 : ℂ))
        * Complex.I + (r : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))) p :=
      ContinuousAt.comp (g := riemannZeta) (x := p)
        (differentiableAt_riemannZeta hne).continuousAt hgc
    exact ((hzc.norm).log
      (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hgre))).continuousWithinAt
  have hmeasS : MeasurableSet (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  -- the majorant, integrable in `θ` and constant in `x`
  have hMB : MeasureTheory.IntegrableOn M (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    have h := logzeta_cos_intervalIntegrable_ofReal (r := r)
      (a := (-Real.pi / 2 : ℝ)) (b := (Real.pi / 2 : ℝ))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at h
    exact h.mono_set Set.Ioo_subset_Ioc_self
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (-a) a) :=
    continuous_const.integrableOn_Ioc
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => M p.2)
      (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    have h := hone.mul_prod hMB
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod] at h
    have h2 : MeasureTheory.Integrable (fun z : ℝ × ℝ => M z.2)
        (MeasureTheory.volume.restrict
          (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2))) := by
      simpa using h
    exact h2
  have hdom : MeasureTheory.IntegrableOn
      (Function.uncurry fun x θ : ℝ =>
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    refine hprod.mono' (hcont.aestronglyMeasurable hmeasS) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hmeasS (fun p hp => ?_)
    have h := abs_log_zeta_norm_le (hkey p hp)
    rw [circle_point_re T r p.1 p.2] at h
    simpa [Function.uncurry, Real.norm_eq_abs, hM] using h
  -- put the endpoint `θ = π/2` back: it is a null slice of the rectangle
  have hnull : MeasureTheory.volume
      ((Set.univ : Set ℝ) ×ˢ ({Real.pi / 2} : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have hst : (Set.Ioc (-a) a ×ˢ Set.Ioc (-Real.pi / 2) (Real.pi / 2))
      =ᵐ[MeasureTheory.volume] (Set.Ioc (-a) a ×ˢ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine MeasureTheory.measure_mono_null ?_ hnull
      intro p hp
      obtain ⟨hmem, hnmem⟩ := hp
      have h1 : p.1 ∈ Set.Ioc (-a) a := hmem.1
      have h2 : p.2 ∈ Set.Ioc (-Real.pi / 2) (Real.pi / 2) := hmem.2
      have h3 : p.2 ∉ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := fun hc => hnmem ⟨h1, hc⟩
      have h4 : p.2 = Real.pi / 2 := by
        rcases lt_or_eq_of_le h2.2 with hlt | heq
        · exact absurd ⟨h2.1, hlt⟩ h3
        · exact heq
      exact ⟨Set.mem_univ _, h4⟩
    · refine MeasureTheory.measure_mono_null (t := (∅ : Set (ℝ × ℝ))) ?_
        MeasureTheory.measure_empty
      rintro p ⟨⟨h1, h2⟩, hn⟩
      exact hn ⟨h1, Set.Ioo_subset_Ioc_self h2⟩
  exact hdom.congr_set_ae hst

/-- **The Fubini exchange behind step 1 of `outside3`.**
`∫_{-a}^{a} ∫_{-π/2}^{π/2} log‖ζ(1+i(T+x)+re^{iθ})‖ dθ dx
 = ∫_{-π/2}^{π/2} ∫_{-a}^{a} log‖ζ(1+i(T+x)+re^{iθ})‖ dx dθ`.

### Summary of Proof
Fubini on the rectangle `[-a,a] × [-π/2,π/2]`, via
`MeasureTheory.intervalIntegral_intervalIntegral_swap`, whose only hypothesis is joint
integrability of the uncurried integrand on `uIoc(-a,a) ×ˢ uIoc(-π/2,π/2)` —
`outside3_integrableOn_rect`.

### Lean Notes
Mathlib's `intervalIntegral_intervalIntegral_swap` states exactly this shape (both integrals
interval integrals), so no rewriting between `intervalIntegral` and set integrals over `Ioc` is
needed; all the work sits in the integrability hypothesis.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), step 1 of its proof ("exchange the order
of integration").

### Dependencies
**Depends on:** `outside3_integrableOn_rect`.
**Used by:** `outside3_fubini_bound`. -/
theorem outside3_fubini_swap {T a r : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    (∫ x in (-a)..a, ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖)
      = ∫ θ in (-Real.pi / 2)..(Real.pi / 2), ∫ x in (-a)..a,
          Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖ :=
  MeasureTheory.intervalIntegral_intervalIntegral_swap (outside3_integrableOn_rect hr ha)

/-- **Step 2 of `outside3`'s reduction:** the Fubini swap, together with the triangle inequality
and the slice bound, giving `|A| ≤ (1/π)∫_{-π/2}^{π/2} Φ(1+r cos θ).re dθ`.

### Summary of Proof
Exchange the order of integration to put the `θ`-integral outside, then
`|∫ f| ≤ ∫ |f|` on the `θ`-integral, then apply `outside3_theta_slice_le` pointwise in `θ`. The
factor is `(1/(2π))·2 = 1/π`.

### Lean Notes
The step is assembled here from four facts:

* `outside3_fubini_swap` — the exchange itself, and the only place joint integrability on the
  rectangle is needed (`outside3_integrableOn_rect`);
* `intervalIntegral.abs_integral_le_integral_abs` for the triangle step (no side conditions);
* `intervalIntegral.integral_mono_on_of_le_Ioo` for the pointwise bound. The *open*-interval form
  is essential, not a convenience: `outside3_theta_slice_le` requires `cos θ > 0`, which fails at
  `θ = ±π/2` — exactly the two endpoints that form excludes;
* its two integrability side conditions, `outside3_inner_abs_intervalIntegrable` (via the closed
  form `outside3_theta_slice_eq`) and the continuity of the `Φ`-majorant on the closed interval
  (`phi_cos_re_continuousOn`).

The final arithmetic is `(1/(2π))·(2·X) = (1/π)·X`, with the constant pulled out of the
`x`-integral by `intervalIntegral.integral_const_mul` and out of the absolute value by
`abs_of_pos`.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), steps 1–2 of its proof.

### Dependencies
**Depends on:** `Phi`, `outside3_fubini_swap`, `outside3_inner_abs_intervalIntegrable`,
`outside3_theta_slice_le`, `phi_cos_re_continuousOn`.
**Used by:** `outside3`. -/
theorem outside3_fubini_bound {T a r : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    |∫ x in (-a)..a,
        (1 / (2 * Real.pi)) *
          ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|
      ≤ (1 / Real.pi) *
          ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
  have hpi := Real.pi_pos
  have hhalf : (-Real.pi / 2 : ℝ) ≤ Real.pi / 2 := by linarith
  have hc2pi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  -- integrability of the majorant `θ ↦ 2 · Φ(1+r cos θ).re`
  have hmaj : IntervalIntegrable
      (fun θ : ℝ => 2 * (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hhalf]
    refine continuousOn_const.mul ((phi_cos_re_continuousOn hr).mono ?_)
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  -- triangle inequality in `θ`, then the slice bound pointwise on the open interval
  have h1 : |∫ θ in (-Real.pi / 2)..(Real.pi / 2), ∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|
      ≤ ∫ θ in (-Real.pi / 2)..(Real.pi / 2), |∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖| :=
    intervalIntegral.abs_integral_le_integral_abs hhalf
  have h2 : (∫ θ in (-Real.pi / 2)..(Real.pi / 2), |∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|)
      ≤ ∫ θ in (-Real.pi / 2)..(Real.pi / 2), 2 * (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hhalf
      (outside3_inner_abs_intervalIntegrable hr) hmaj (fun θ hθ => ?_)
    exact outside3_theta_slice_le hr (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have h3 : (∫ θ in (-Real.pi / 2)..(Real.pi / 2), 2 * (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      = 2 * ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re :=
    intervalIntegral.integral_const_mul 2 _
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos hc2pi,
    outside3_fubini_swap hr ha]
  have hchain : |∫ θ in (-Real.pi / 2)..(Real.pi / 2), ∫ x in (-a)..a,
        Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|
      ≤ 2 * ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
    rw [← h3]; exact h1.trans h2
  have hscaled := mul_le_mul_of_nonneg_left hchain hc2pi.le
  have hfin : 1 / (2 * Real.pi) *
      (2 * ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      = 1 / Real.pi * ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
          (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
    field_simp
  linarith [hfin ▸ hscaled]

/-! ### Ingredients for step 3 (`phi_cos_integral_eq_c5`)

Small lemmas feeding the integration by parts that identifies the
`θ`-integral of `Φ(1+r cos θ).re` with `c_{5,r}`. (Two more that this step uses,
`phi_cos_re_continuousOn` and `logzeta_cos_intervalIntegrable_ofReal`, are stated earlier,
because step 2 needs them too.) They follow the route of
`JensenBounds.integral_log_zeta_cos_quarter_eq_c4` — the structurally identical statement with
`log ζ` in place of `Φ` — namely IBP **in `θ` first**, substitution `u = cos θ` **afterwards**.

A coercion convention: everything here writes the argument of `ζ` as `((1 + r·x : ℝ) : ℂ)`,
because that is the form `Phi_re_hasDerivAt` produces, whereas `c5` writes `(1 + r*x : ℂ)`. The
two agree by `push_cast`, reconciled once at the end of `phi_cos_integral_eq_c5` (the same
bookkeeping the `c4` proof does). -/

/-- **Interval integrability of `u ↦ log‖ζ(1+ru)‖·arcsin u`,** in the real-coercion form.

### Summary of Proof
`u ↦ ζ(1+ru)` is real-meromorphic (`Definitions.meromorphicAt_riemannZeta` composed with an
affine map), so `MeromorphicOn.intervalIntegrable_log_norm` applies: the `log‖ζ(1+ru)‖` factor
blows up like `-log(ru)` at the pole `u = 0`, but only logarithmically, hence integrably. The
`arcsin` factor is bounded and continuous.

### Lean Notes
This is the cast-normalised twin of `logzeta_arcsin_integrable` below, which is now derived from
it; it is stated first because `integral_sin_mul_logzeta_comp_cos` (above `c5`'s consumers) needs
this form.

### References
No tex counterpart.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `integral_sin_mul_logzeta_comp_cos`, `logzeta_arcsin_integrable`. -/
theorem logzeta_arcsin_integrable_ofReal (r a b : ℝ) : IntervalIntegrable
    (fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
    MeasureTheory.volume a b := by
  have hmero : MeromorphicOn (fun u : ℝ => riemannZeta ((1 : ℂ) + (r : ℂ) * (u : ℂ)))
      (Set.uIcc a b) := by
    intro t _
    have hinner : AnalyticAt ℝ (fun u : ℝ => (1 : ℂ) + (r : ℂ) * (u : ℂ)) t := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul analyticAt_const
      exact Complex.ofRealCLM.analyticAt t
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  have h := hmero.intervalIntegrable_log_norm.mul_continuousOn Real.continuous_arcsin.continuousOn
  have heq : (fun u : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (r : ℂ) * (u : ℂ))‖ * Real.arcsin u)
      = fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u := by
    funext u; norm_num
  rwa [heq] at h

/-- **`(d/dθ) Φ(1+r cos θ).re = r·sin θ·log‖ζ(1+r cos θ)‖`,** wherever `cos θ > 0`.

### Summary of Proof
Chain rule: `Phi_re_hasDerivAt` at `σ = 1 + r cos θ > 1` gives outer derivative
`-log‖ζ(1+r cos θ)‖`, and `θ ↦ 1 + r cos θ` has derivative `-r sin θ`. The two minus signs
cancel, which is why the `arcsin`-weighted term in `c5` carries a **`+`**.

### Lean Notes
The hypothesis is `cos θ > 0` rather than `θ ∈ (-π/2, π/2)`: it is exactly what keeps
`1 + r cos θ` strictly off `ζ`'s pole, and it is what fails at `θ = ±π/2`. That failure is why
`phi_cos_integral_quarter` must use the `..._of_tendsto` form of the FTC, which asks for
`HasDerivAt` only on the open interval.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_re_hasDerivAt`.
**Used by:** `phi_cos_integral_quarter`. -/
theorem phi_cos_re_hasDerivAt {r θ : ℝ} (hr : 0 < r) (hcos : 0 < Real.cos θ) :
    HasDerivAt (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      (r * Real.sin θ * Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖) θ := by
  have hσ : (1 : ℝ) < 1 + r * Real.cos θ := by nlinarith
  have h1 := Phi_re_hasDerivAt hσ
  have h2 : HasDerivAt (fun θ : ℝ => 1 + r * Real.cos θ) (r * -Real.sin θ) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul r).const_add (1 : ℝ)
  have h3 := h1.comp θ h2
  refine h3.congr_deriv ?_
  ring

/-- **The substitution `u = cos θ`:**
`∫_0^{π/2} sin θ·log‖ζ(1+r cos θ)‖·arcsin(cos θ) dθ = ∫_0^1 log‖ζ(1+ru)‖·arcsin u du`.

### Summary of Proof
`intervalIntegral.integral_deriv_smul_comp'''` with `f = cos`, `f' = -sin`, and
`g u = log‖ζ(1+ru)‖·arcsin u`. Since `cos 0 = 1` and `cos(π/2) = 0`, the substituted bounds come
out reversed, which `intervalIntegral.integral_symm` and the sign of `f'` undo together.

### Lean Notes
The exact analogue of `JensenBounds.integral_sin_mul_comp_cos`, which does the same substitution
with `(ζ'/ζ)(1+ru)` in place of `log‖ζ(1+ru)‖, and its proof is followed step for step.

The choice of `integral_deriv_smul_comp'''` (rather than the simpler
`integral_comp_smul_deriv`) is forced and worth recording: `g` is **not** continuous at `u = 0`,
where `1 + ru` hits `ζ`'s pole. That lemma asks for continuity of `g` only on the image of the
**open** interval — here `(0,1]` — and mere *integrability* on the closed image `[0,1]`, which
`logzeta_arcsin_integrable_ofReal` supplies. So no limit argument at the singular endpoint is
needed; contrast the `c4` analogue, where the singular endpoint had to be handled in the
integration by parts instead.

### References
No tex counterpart — the tex performs this substitution in one line.

### Dependencies
**Depends on:** `logzeta_arcsin_integrable_ofReal`, `logzeta_cos_intervalIntegrable_ofReal`.
**Used by:** `phi_cos_integral_quarter`. -/
theorem integral_sin_mul_logzeta_comp_cos {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
          * Real.arcsin (Real.cos θ)))
      = ∫ u in (0 : ℝ)..1, Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have huIcc : Set.uIcc (0 : ℝ) (Real.pi / 2) = Set.Icc 0 (Real.pi / 2) := Set.uIcc_of_le hle
  have himg_cl : Real.cos '' Set.uIcc (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [huIcc] at hθ
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩, Real.cos_le_one θ⟩
  have himg_op : Real.cos '' Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2))
      ⊆ Set.Ioc (0 : ℝ) 1 := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [min_eq_left hle, max_eq_right hle] at hθ
    exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩, Real.cos_le_one θ⟩
  have hGcont : ContinuousOn
      (fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
      (Set.Ioc (0 : ℝ) 1) := by
    refine ContinuousOn.mul (ContinuousOn.log ?_ ?_) Real.continuous_arcsin.continuousOn
    · intro u hu
      have hσ : (1 : ℝ) < 1 + r * u := by nlinarith [hu.1]
      have hne : ((1 + r * u : ℝ) : ℂ) ≠ 1 := by
        intro hc
        have hre := congrArg Complex.re hc
        simp only [Complex.ofReal_re, Complex.one_re] at hre
        linarith
      have hc : ContinuousAt (fun u : ℝ => riemannZeta ((1 + r * u : ℝ) : ℂ)) u :=
        ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => ((1 + r * u : ℝ) : ℂ)) (x := u)
          (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
      exact hc.continuousWithinAt.norm
    · intro u hu
      have hσ : (1 : ℝ) < 1 + r * u := by nlinarith [hu.1]
      exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))
  have hIcc : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
      (Set.Icc (0 : ℝ) 1) := by
    have h := logzeta_arcsin_integrable_ofReal r 0 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    exact h.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc).symm
  have hprodneg : IntervalIntegrable
      (fun θ : ℝ => -Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
        * Real.arcsin (Real.cos θ))) MeasureTheory.volume 0 (Real.pi / 2) :=
    (logzeta_cos_intervalIntegrable_ofReal.mul_continuousOn
        (g := fun θ : ℝ => Real.arcsin (Real.cos θ)) (by fun_prop)).continuousOn_mul
      (g := fun θ : ℝ => -Real.sin θ) (by fun_prop)
  have hsub := intervalIntegral.integral_deriv_smul_comp'''
    (f := Real.cos) (f' := fun θ => -Real.sin θ)
    (g := fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
    (a := (0 : ℝ)) (b := Real.pi / 2)
    Real.continuous_cos.continuousOn
    (fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt)
    (hGcont.mono himg_op)
    (hIcc.mono_set himg_cl)
    (by
      rw [huIcc]
      have h0 := hprodneg
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at h0
      have h := h0.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc).symm
      refine h.congr_fun ?_ measurableSet_Icc
      intro θ _
      simp only [Function.comp, smul_eq_mul])
  rw [Real.cos_zero, Real.cos_pi_div_two] at hsub
  simp only [Function.comp, smul_eq_mul] at hsub
  rw [intervalIntegral.integral_symm (0 : ℝ) 1] at hsub
  have hneg : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      -Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
        * Real.arcsin (Real.cos θ)))
      = -∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
          * Real.arcsin (Real.cos θ)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun θ _ => by ring)
  rw [hneg] at hsub
  linarith [hsub]

/-- **The quarter-period integration by parts:**
`∫_0^{π/2} Φ(1+r cos θ).re dθ = (π/2)·Φ(1+r).re + r·∫_0^1 log‖ζ(1+ru)‖·arcsin u du`.

### Summary of Proof
Integrate by parts with the antiderivative of `1` taken to be `θ - π/2` — chosen because it
**vanishes at `θ = π/2`**, the endpoint where `1 + r cos θ` meets `ζ`'s pole. Writing
`f(θ) := Φ(1+r cos θ).re` and `P(θ) := f(θ)·(θ - π/2)`, `phi_cos_re_hasDerivAt` gives

    P'(θ) = r·sin θ·log‖ζ(1+r cos θ)‖·(θ - π/2) + f(θ),

and `arcsin(cos θ) = π/2 - θ` on `[0, π/2]` (`JensenBounds.arcsin_cos_eq`) turns the first
summand into `-r·sin θ·log‖ζ(1+r cos θ)‖·arcsin(cos θ)`. The two endpoint limits are
`P(0) = -(π/2)·Φ(1+r).re` and `P(π/2) = 0`, both immediate from `phi_cos_re_continuousOn`, so
`∫_0^{π/2} P' = (π/2)·Φ(1+r).re`. Substituting `u = cos θ`
(`integral_sin_mul_logzeta_comp_cos`) on the remaining term gives the claim.

### Lean Notes
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` is used rather than the plain FTC:
`phi_cos_re_hasDerivAt` holds only on the **open** interval, since at `θ = π/2` the outer
derivative `Phi_re_hasDerivAt` would be asked for at `σ = 1`, where it fails. That lemma takes
both endpoint values as `nhdsWithin` limits, so no `[ε, π/2 - ε]` exhaustion is needed.

**Easier than the `c4` analogue, and worth saying why.** In
`JensenBounds.integral_log_zeta_cos_quarter_eq_c4` the boundary term needed
`log ζ(1+x)·arcsin x → 0` as `x → 0⁺`, a pole-times-zero limit requiring
`tendsto_riemannZeta_sub_one_div`. Here the corresponding factor is `Φ(1+r cos θ)`, which is
**bounded**: `Φ` converges at `σ = 1` (`Definitions.LSeriesSummable_PhiTerm_one`) and is
continuous up to it (`Phi_continuousOn_closedHalfPlane`), so the boundary term vanishes simply
because `θ - π/2 → 0` against a bounded factor. No pole cancellation is involved.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), step 3 of its proof.

### Dependencies
**Depends on:** `Phi`, `arcsin_cos_eq`, `integral_sin_mul_logzeta_comp_cos`,
`logzeta_cos_intervalIntegrable_ofReal`, `phi_cos_re_continuousOn`, `phi_cos_re_hasDerivAt`.
**Used by:** `phi_cos_integral_eq_c5`. -/
theorem phi_cos_integral_quarter {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      = Real.pi / 2 * (Phi ((1 + r : ℝ) : ℂ)).re
        + r * ∫ u in (0 : ℝ)..1,
            Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u := by
  have hpi := Real.pi_pos
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re * (θ - Real.pi / 2))
        (-(r * (Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
              * Real.arcsin (Real.cos θ))))
          + (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re) θ := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have h1 := phi_cos_re_hasDerivAt hr hcos
    have h2 := (hasDerivAt_id θ).sub_const (Real.pi / 2)
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have harc : Real.arcsin (Real.cos θ) = Real.pi / 2 - θ :=
      arcsin_cos_eq hθ.1.le (by linarith [hθ.2])
    rw [harc]
    simp only [id_eq]
    ring
  have hfint : IntervalIntegrable (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hhalf.le]
    exact (phi_cos_re_continuousOn hr).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hsq : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
        * Real.arcsin (Real.cos θ))) MeasureTheory.volume 0 (Real.pi / 2) :=
    (logzeta_cos_intervalIntegrable_ofReal.mul_continuousOn
        (g := fun θ : ℝ => Real.arcsin (Real.cos θ)) (by fun_prop)).continuousOn_mul
      (g := fun θ : ℝ => Real.sin θ) (by fun_prop)
  have hnegint : IntervalIntegrable
      (fun θ : ℝ => -(r * (Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
          * Real.arcsin (Real.cos θ))))) MeasureTheory.volume 0 (Real.pi / 2) :=
    (hsq.const_mul r).neg
  have hint : IntervalIntegrable
      (fun θ : ℝ => -(r * (Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
            * Real.arcsin (Real.cos θ))))
        + (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re) MeasureTheory.volume 0 (Real.pi / 2) :=
    hnegint.add hfint
  have hmem0 : Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
  have hmemhi : Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    apply Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Iio (Real.pi / 2))
      (isOpen_Ioi.mem_nhds (show -(Real.pi / 2) < Real.pi / 2 by linarith)))
    rintro x ⟨hx1, hx2⟩
    exact ⟨le_of_lt hx2, le_of_lt hx1⟩
  have ha : Filter.Tendsto
      (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re * (θ - Real.pi / 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds ((Phi ((1 + r * Real.cos 0 : ℝ) : ℂ)).re * (0 - Real.pi / 2))) := by
    have hc := (phi_cos_re_continuousOn hr) 0 ⟨by linarith, by linarith⟩
    have h1 := hc.mono_left (nhdsWithin_le_iff.mpr hmem0)
    have h2 : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 - Real.pi / 2)) :=
      ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    exact h1.mul h2
  have hb : Filter.Tendsto
      (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re * (θ - Real.pi / 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc := (phi_cos_re_continuousOn hr) (Real.pi / 2) ⟨by linarith, le_rfl⟩
    have h1 := hc.mono_left (nhdsWithin_le_iff.mpr hmemhi)
    have h2 : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hcont : Continuous (fun θ : ℝ => θ - Real.pi / 2) := by fun_prop
      have h : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.pi / 2 - Real.pi / 2)) :=
        (hcont.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
      simpa using h
    simpa using h1.mul h2
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hhalf hderiv hint ha hb
  have hval : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      -(r * (Real.sin θ * (Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖
        * Real.arcsin (Real.cos θ)))))
      = -(r * ∫ u in (0 : ℝ)..1,
          Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      integral_sin_mul_logzeta_comp_cos hr]
  rw [intervalIntegral.integral_add hnegint hfint, hval] at heq
  have hcos0 : ((1 + r * Real.cos 0 : ℝ) : ℂ) = ((1 + r : ℝ) : ℂ) := by norm_num
  rw [hcos0] at heq
  linear_combination heq

/-- **Step 3 of `outside3`'s reduction:** the `θ`-integral of `Φ(1+r cos θ).re` is exactly
`c_{5,r}`.

### Summary of Proof
Integrate by parts in `θ`, taking the antiderivative of `1` to be `θ - π/2` — chosen because it
**vanishes at `θ = π/2`**, where `cos θ = 0`. With `f(θ) := Φ(1+r cos θ).re`,

    ∫_0^{π/2} f = [f·(θ-π/2)]_0^{π/2} - ∫_0^{π/2} f'(θ)(θ-π/2) dθ = (π/2)Φ(1+r).re + …

and `f'(θ) = -r·log‖ζ(1+r cos θ)‖·(-sin θ)` since `Φ' = -log ζ` on the real axis. Using
`arcsin(cos θ) = π/2 - θ` on `[0,π/2]` and then the substitution `u = cos θ`, the remaining term
is `r∫_0^1 log‖ζ(1+ru)‖·arcsin u du`. Multiplying by `2/π` (the `-π/2..π/2` integral is twice the
`0..π/2` one, `cos` being even) gives exactly
`Φ(1+r).re + (2r/π)∫_0^1 log‖ζ(1+ru)‖ arcsin u du = c5 r`.

This is the Lean check of the **`+` sign** in `c5`, independent of the paper derivation sketched
in the section comment above `outside3_theta_slice_le`.

### Lean Notes
The whole integration by parts is `phi_cos_integral_quarter`; what is left here is the evenness
reduction and the coercion bookkeeping. Evenness: `intervalIntegral.integral_comp_neg` together
with `Real.cos_neg` identifies `∫_{-π/2}^0` with `∫_0^{π/2}`, and
`intervalIntegral.integral_add_adjacent_intervals` glues them (integrability of both halves from
`phi_cos_re_continuousOn`). Coercions: the helper lemmas write `ζ`'s argument as
`((1 + r·x : ℝ) : ℂ)` while `c5` writes `(1 + r*x : ℂ)`; the two are reconciled by `push_cast`
here, at the end, exactly as `JensenBounds.integral_log_zeta_cos_quarter_eq_c4` does.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), steps 3–4 of its proof; `c_{5,r}` is
defined there.

### Dependencies
**Depends on:** `Phi`, `c5`, `phi_cos_integral_quarter`, `phi_cos_re_continuousOn`.
**Used by:** `outside3`. -/
theorem phi_cos_integral_eq_c5 {r : ℝ} (hr : 0 < r) :
    (1 / Real.pi) *
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re
      = c5 r := by
  have hpi := Real.pi_pos
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith
  have hlow : (-Real.pi / 2 : ℝ) = -(Real.pi / 2) := by ring
  have hintA : IntervalIntegrable (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      MeasureTheory.volume (-(Real.pi / 2)) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact (phi_cos_re_continuousOn hr).mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  have hintB : IntervalIntegrable (fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hhalf.le]
    exact (phi_cos_re_continuousOn hr).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hrefl : (∫ θ in (-(Real.pi / 2))..(0 : ℝ), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
    simp only [Real.cos_neg, neg_zero] at h
    exact h.symm
  have hsplit : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re)
      = 2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (Phi ((1 + r * Real.cos θ : ℝ) : ℂ)).re := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hintA hintB, hrefl]
    ring
  have hfeq : (fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
      = fun u : ℝ => Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u := by
    funext u; norm_num
  have hc1 : ((1 + r : ℝ) : ℂ) = (1 + r : ℂ) := by push_cast; ring
  rw [hlow, hsplit, phi_cos_integral_quarter hr, hfeq, hc1, c5]
  field_simp

/-- **Proposition `\ref{prop:outside3}` (Proposition 23)**, main bound: for `0 < r`, `0 ≤ h` and
`T > h + α̂_r`,
`|∫_{-h-α̂_r}^{h+α̂_r} (1/(2π)) ∫_{-π/2}^{π/2} log|ζ(1+i(T+x)+re^{iθ})| dθ dx| ≤ c_{5,r}`.**

Proved, under the file's hypothesis-class binders — a conditional statement in form, though the
proof below reaches nothing but Mathlib and `Definitions`. The reasons for the `≤`, the absolute
value and the `+` in `c5` are in the section comment above `outside3_theta_slice_le`; this is the
assembly.

### Summary of Proof
`outside3_fubini_bound` (steps 1–2: Fubini, then the slice bound `outside3_theta_slice_le`)
followed by `phi_cos_integral_eq_c5` (steps 3–4: the IBP in `θ` and the `u = cos θ`
substitution).

### Lean Notes
The `0 < r` and `0 ≤ h` hypotheses are not in the source; see the section comment above for why
they are needed. `T > h + α̂_r` is retained (as `_hTh`) because it is the tex's hypothesis and
callers pass it, but the bound as proved does not use it: the `Φ`-FTC route bounds the inner
integral by `2·Φ(1+r cos θ).re` independently of where the window sits, which is exactly the
crudeness `outside2_of_one_lt` also has.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23).

### Dependencies
**Depends on:** `c5`, `hatAlpha`, `outside3_fubini_bound`, `phi_cos_integral_eq_c5`.
**Used by:** `rectangularjensen`, `rectangularjensen_tight`. -/
theorem outside3 {T h r α : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (_hTh : h + hatAlpha r α < T) :
    |∫ x in (-h - hatAlpha r α)..(h + hatAlpha r α),
        (1 / (2 * Real.pi)) *
          ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            Real.log ‖riemannZeta (1 + (T + x) * Complex.I + r * Complex.exp (θ * Complex.I))‖|
      ≤ c5 r := by
  have ha : (0 : ℝ) ≤ h + hatAlpha r α := by
    have : (0 : ℝ) ≤ hatAlpha r α := Real.sqrt_nonneg _
    linarith
  have hneg : -h - hatAlpha r α = -(h + hatAlpha r α) := by ring
  rw [hneg]
  rw [← phi_cos_integral_eq_c5 hr]
  exact outside3_fubini_bound (T := T) (a := h + hatAlpha r α) hr ha

/-- **Interval integrability of `u ↦ log‖ζ(1+ru)‖·arcsin u`, the integrand of `c5`.**

### Summary of Proof
The `log‖ζ(1+ru)‖` factor blows up like `-log(ru)` at `u=0` (where `1+ru` hits `ζ`'s pole), but
logarithmically, hence integrably: `u ↦ ζ(1+ru)` is real-meromorphic
(`Definitions.meromorphicAt_riemannZeta` composed with an affine map), so
`MeromorphicOn.intervalIntegrable_log_norm` applies, and `arcsin` is a bounded continuous factor.

### Lean Notes
That argument lives in `logzeta_arcsin_integrable_ofReal` above, which states the same fact with
`ζ`'s argument written as `((1 + r·u : ℝ) : ℂ)` (the form the `Φ` machinery produces). This is
its cast-normalised restatement in `c5`'s own spelling `(1 + r*u : ℂ)`, obtained by a
`funext`/`push_cast` rewrite; the two functions are pointwise equal.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logzeta_arcsin_integrable_ofReal`.
**Used by:** `integral_logzeta_arcsin_gt`, `outside3_lt`. -/
theorem logzeta_arcsin_integrable (r a b : ℝ) : IntervalIntegrable
    (fun u : ℝ => Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u)
    MeasureTheory.volume a b := by
  have h := logzeta_arcsin_integrable_ofReal r a b
  have heq : (fun u : ℝ => Real.log ‖riemannZeta ((1 + r * u : ℝ) : ℂ)‖ * Real.arcsin u)
      = fun u : ℝ => Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u := by
    funext u; norm_num
  rwa [heq] at h

/-- **A strict lower bound for `c5`'s integral:**
`∫₀¹ log‖ζ(1+ru)‖·arcsin u du > (π/2 - 1)·log‖ζ(1+r)‖`.

### Summary of Proof
The non-strict form is immediate from `Definitions.log_zeta_norm_antitoneOn`
(`log‖ζ(1+ru)‖ ≥ log‖ζ(1+r)‖` for `u ≤ 1`) together with
`JensenBounds.integral_arcsin_zero_one` (`∫₀¹ arcsin = π/2 - 1`). Strictness — which is what the
source's `<` needs, and which it gets by "dropping a manifestly-negative remainder" — comes from
splitting at `u = 1/2` and using the *strict* antitonicity
`Definitions.log_zeta_norm_strictAntiOn` on the lower half: the gain is
`(log‖ζ(1+r/2)‖ - log‖ζ(1+r)‖)·∫₀^{1/2} arcsin > 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `integral_arcsin_zero_one`, `log_zeta_norm_antitoneOn`,
`log_zeta_norm_strictAntiOn`, `logzeta_arcsin_integrable`.
**Used by:** none — `outside3_lt` reaches its closed form through the direct pointwise bound
`logzeta_le_linear` instead, so this is off the critical path. -/
theorem integral_logzeta_arcsin_gt {r : ℝ} (hr : 0 < r) :
    (Real.pi / 2 - 1) * Real.log ‖riemannZeta (1 + r : ℂ)‖
      < ∫ u in (0 : ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u := by
  set L : ℝ := Real.log ‖riemannZeta (1 + r : ℂ)‖ with hL
  set L₂ : ℝ := Real.log ‖riemannZeta (1 + r / 2 : ℂ)‖ with hL2
  have hLlt : L < L₂ := by
    rw [hL, hL2]
    have h := log_zeta_norm_strictAntiOn (a := 1 + r / 2) (b := 1 + r)
      (by simp; linarith) (by simp; linarith) (by linarith)
    simp only at h
    push_cast at h ⊢; exact h
  -- pointwise bounds on the two halves
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, L * Real.arcsin x
      ≤ Real.log ‖riemannZeta (1 + r * x : ℂ)‖ * Real.arcsin x := by
    intro x hx
    have harc : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.2 hx.1
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]; simp
    · refine mul_le_mul_of_nonneg_right ?_ harc
      have h := log_zeta_norm_antitoneOn (a := 1 + r * x) (b := 1 + r)
        (by simp only [Set.mem_Ioi, lt_add_iff_pos_right]; positivity)
        (by simp; linarith) (by nlinarith [hx.2])
      simp only at h
      rw [hL]; push_cast at h ⊢; exact h
  have hpt2 : ∀ x ∈ Set.Icc (0:ℝ) (1/2), L₂ * Real.arcsin x
      ≤ Real.log ‖riemannZeta (1 + r * x : ℂ)‖ * Real.arcsin x := by
    intro x hx
    have harc : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.2 hx.1
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]; simp
    · refine mul_le_mul_of_nonneg_right ?_ harc
      have h := log_zeta_norm_antitoneOn (a := 1 + r * x) (b := 1 + r / 2)
        (by simp only [Set.mem_Ioi, lt_add_iff_pos_right]; positivity)
        (by simp; linarith) (by nlinarith [hx.2])
      simp only at h
      rw [hL2]; push_cast at h ⊢; exact h
  -- split the integral at `1/2` and compare each half against its constant lower bound
  have hint01 := logzeta_arcsin_integrable r 0 1
  have hintA := logzeta_arcsin_integrable r 0 (1/2)
  have hintB := logzeta_arcsin_integrable r (1/2) 1
  have hsplit : (∫ u in (0:ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u)
      = (∫ u in (0:ℝ)..(1/2), Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u)
        + ∫ u in (1/2:ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u :=
    (intervalIntegral.integral_add_adjacent_intervals hintA hintB).symm
  have harcA : IntervalIntegrable Real.arcsin MeasureTheory.volume 0 (1/2) :=
    Real.continuous_arcsin.intervalIntegrable _ _
  have harcB : IntervalIntegrable Real.arcsin MeasureTheory.volume (1/2) 1 :=
    Real.continuous_arcsin.intervalIntegrable _ _
  set A : ℝ := ∫ u in (0:ℝ)..(1/2), Real.arcsin u with hA
  set B : ℝ := ∫ u in (1/2:ℝ)..1, Real.arcsin u with hB
  have hAB : A + B = Real.pi / 2 - 1 := by
    rw [hA, hB, intervalIntegral.integral_add_adjacent_intervals harcA harcB]
    exact integral_arcsin_zero_one
  have hApos : 0 < A := by
    rw [hA]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on harcA ?_ (by norm_num)
    intro x hx
    exact Real.arcsin_pos.2 hx.1
  -- lower bound on each half
  have hlowA : L₂ * A ≤ ∫ u in (0:ℝ)..(1/2), Real.log ‖riemannZeta (1 + r * u : ℂ)‖
      * Real.arcsin u := by
    rw [hA, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((harcA.const_mul L₂)) hintA ?_
    intro x hx
    exact hpt2 x (by simpa using hx)
  have hlowB : L * B ≤ ∫ u in (1/2:ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖
      * Real.arcsin u := by
    rw [hB, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((harcB.const_mul L)) hintB ?_
    intro x hx
    refine hpt x ⟨by linarith [hx.1], hx.2⟩
  have hgap : L * A < L₂ * A := mul_lt_mul_of_pos_right hLlt hApos
  have hkey : (Real.pi / 2 - 1) * L = L * A + L * B := by rw [← hAB]; ring
  rw [hsplit, hkey]
  linarith

/-! ### The closed-form bound on `c5` (via a direct upper bound on `log ζ`)

**Follows the source's own proof of `c5`'s "Moreover" bound.** Write
`Q(r) := ∫₀¹ log ζ(1+ru)·arcsin(u) du`, so that `c5 r = Φ(1+r).re + (2r/π)Q(r)`. Lemma
`\ref{lemma:logderzetabound}` (Lemma 38), claim 3 at `N = 0`, gives the pointwise bound
`log ζ(1+x) ≤ -log x + γx` on `0 < x ≤ 2` (`logzeta_le_linear` below). Taking `x := ru` with
`u ∈ (0,1]`, multiplying by `arcsin(u) ≥ 0` and integrating over `[0,1]`:

`Q(r) ≤ -(π/2-1)·log r - ∫₀¹ log(u)·arcsin(u) du + γr·∫₀¹ u·arcsin(u) du`.

All three integrals are elementary and exact, with no `ζ` in sight:
`∫₀¹ arcsin(u) du = π/2 - 1` (`JensenBounds.integral_arcsin_zero_one`),
`∫₀¹ u·arcsin(u) du = π/8` (`JensenBounds.integral_mul_arcsin_zero_one`), and
`∫₀¹ log(u)·arcsin(u) du = 2 - π/2 - log 2` (`integral_log_mul_arcsin` below, proved via one
further IBP against `arcsinAntideriv`, whose own boundary/singularity handling reuses the exact
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` technique Mathlib itself uses for
`∫ log`). Scaling by `2r/π` gives

`c5 r ≤ Φ(1+r).re + r·(-4/π + 1 + (γ/4)r - log r + (2/π)log(2r))`,

which is `outside3_lt`, matching the tex's "Moreover" clause exactly.

**Alternative: integrating by parts a second time, not used.** `Q(r)` can also be reached by a
second IBP — expressing it via `∫(ζ'/ζ)(1+ru).re·g(u)du` for `g := arcsinAntideriv`, then bounding
that with `-ζ'/ζ(1+w) < 1/w` — but this needs an IBP-with-limit-at-a-removable-singularity
argument that is genuinely more delicate, and, unless carried through to the same exact bound,
tends to leave a *worse* constant (e.g. `r/4 = 0.25r` from the crude step `g(u) ≤ (π/4)u²`, against
`(π+2log2-4)/π ≈ 0.168r` above). The direct route the source uses gets to the exact bound without
that detour.

**Would a sharper `ζ'/ζ` bound help further? Not implemented — the gain is too small to justify
the dependency.** Swapping `-ζ'/ζ(1+w) < 1/w` for
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`'s sharper `< 1/w - γ + (γ²+2γ₁)w` in
the same integration
adds two correction terms to `Q(r)`:
`-γr·∫₀¹(1-u)arcsin(u)du + (γ²+2γ₁)(r²/2)·∫₀¹(1-u²)arcsin(u)du`. Both extra integrals are elementary
and exact: `∫₀¹(1-u)arcsin(u)du = 3π/8-1 ≈ 0.178` and `∫₀¹(1-u²)arcsin(u)du = π/3-7/9 ≈ 0.269`. With
`γ ≈ 0.5772`, `γ₁ ≈ -0.0728` (so `γ²+2γ₁ ≈ 0.1875`), the correction to `c5 r` (after the same `2r/π`
scaling) is `≈ -0.0654r² + 0.0161r³` — an `O(r²)` refinement of the `O(r)` term above, vanishing
faster as `r → 0` and at most `≈ -0.049` at `r = 1` (the largest `r` any caller uses, per
`rectangularjensen`'s `hr1 : r < 1`) against the `≈ 0.168r` leading correction — a further ≈29%
shrink of that one term, not of `c5 r` as a whole. Both routes rest on Lemma 38's numeric input
`logDerivZetaG_boundary_bound`, a field of `LogDerivZetaLaurent.LaurentCertificate`, so the
sharper one buys no independence; the extra machinery is not worth a
sub-30%-of-a-lower-order-term gain. -/

/-- **`g(u) := u·arcsin(u) + √(1-u²) - 1`, the antiderivative of `arcsin` vanishing at `0`
(`g' = arcsin`, `arcsinAntideriv_hasDerivAt`), used to integrate by parts a second time in
`integral_log_mul_arcsin`.**

### Summary of Proof
A definition, `g(u) := u·arcsin(u) + √(1-u²) - 1`. It is the antiderivative of `arcsin`
normalised to vanish at `0`; `arcsinAntideriv_hasDerivAt` proves `g' = arcsin`. Having it
in closed form is what lets the `c_{5,r}` integral be done by parts.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `arcsinAntideriv_eq_integral`, `arcsinAntideriv_hasDerivAt`, `arcsinAntideriv_le`,
`arcsinAntideriv_nonneg`, `arcsinAntideriv_one`, `div_arcsinAntideriv_eq`,
`integral_log_mul_arcsin`, `logu_arcsinAntideriv_tendsto`. -/
noncomputable def arcsinAntideriv (x : ℝ) : ℝ := x * Real.arcsin x + Real.sqrt (1 - x ^ 2) - 1

/-- **`g' = arcsin` on `(-1,1)`, where `g = arcsinAntideriv`.**

### Summary of Proof
Differentiating `g(x) = x·arcsin x + √(1-x²) - 1` termwise: the product rule on `x·arcsin x` gives
`arcsin x + x/√(1-x²)`, and `√(1-x²)` contributes `-x/√(1-x²)`, so the two `x/√(1-x²)` terms cancel
and only `arcsin x` survives. The endpoints `±1` are genuinely excluded — `arcsin` is not
differentiable there.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`.
**Used by:** `arcsinAntideriv_eq_integral`, `integral_log_mul_arcsin`. -/
theorem arcsinAntideriv_hasDerivAt {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt arcsinAntideriv (Real.arcsin u) u := by
  have hne1 : u ≠ -1 := ne_of_gt hu.1
  have hne2 : u ≠ 1 := ne_of_lt hu.2
  have hpos : (0:ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have h1 : HasDerivAt (fun x : ℝ => x * Real.arcsin x)
      (1 * Real.arcsin u + u * (1 / Real.sqrt (1 - u ^ 2))) u := by
    have ha : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - u ^ 2)) u :=
      Real.hasDerivAt_arcsin hne1 hne2
    exact (hasDerivAt_id u).mul ha
  have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (-u / Real.sqrt (1 - u ^ 2)) u := by
    have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by simpa using (hasDerivAt_pow 2 u)
    have hd : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * u)) u := by
      have := hp2.const_sub (1:ℝ); simpa using this
    have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u hd
    refine hcomp.congr_deriv ?_
    field_simp
  have h3 := (h1.add h2).sub_const (1:ℝ)
  have hfun : (fun x : ℝ => ((fun x => x * Real.arcsin x) + fun x => Real.sqrt (1 - x ^ 2)) x - 1)
      = arcsinAntideriv := rfl
  rw [hfun] at h3
  refine h3.congr_deriv ?_
  field_simp
  ring

/-- **`g(x) = ∫₀ˣ arcsin t dt` for `x ∈ [0,1)`:** `g = arcsinAntideriv` really is *the*
antiderivative of `arcsin` vanishing at `0`.

### Summary of Proof
Immediate from `arcsinAntideriv_hasDerivAt` and `g(0) = 0` via the FTC. Used to
derive the sign and size bounds (`arcsinAntideriv_nonneg`, `arcsinAntideriv_le`) by comparing
integrands rather than manipulating the closed form.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`, `arcsinAntideriv_hasDerivAt`.
**Used by:** `arcsinAntideriv_le`, `arcsinAntideriv_nonneg`. -/
theorem arcsinAntideriv_eq_integral {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) :
    arcsinAntideriv x = ∫ t in (0:ℝ)..x, Real.arcsin t := by
  have hzero : arcsinAntideriv 0 = 0 := by simp [arcsinAntideriv]
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) x, HasDerivAt arcsinAntideriv (Real.arcsin t) t := fun t ht =>
    arcsinAntideriv_hasDerivAt ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
  have hint : IntervalIntegrable Real.arcsin MeasureTheory.volume 0 x :=
    Real.continuous_arcsin.intervalIntegrable _ _
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by rwa [Set.uIcc_of_le hx.1] at ht)) hint
  rw [heq, hzero, sub_zero]

/-- **`g(1) = π/2 - 1`, by direct evaluation (`arcsin 1 = π/2`, `√(1-1) = 0`).**

### Summary of Proof
`simp [arcsinAntideriv, Real.arcsin_one]`. The value is the total integral `∫₀¹ arcsin`, and is
what `arcsinAntideriv_nonneg` and `arcsinAntideriv_le` need at the excluded endpoint `x = 1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`.
**Used by:** `arcsinAntideriv_le`, `arcsinAntideriv_nonneg`. -/
theorem arcsinAntideriv_one : arcsinAntideriv 1 = Real.pi / 2 - 1 := by
  simp [arcsinAntideriv, Real.arcsin_one]

/-- **`g ≥ 0` on `[0,1]`.**

### Summary of Proof
On `[0,1)` this is `arcsinAntideriv_eq_integral` plus nonnegativity of
`arcsin` on `[0,1]`; the endpoint `x = 1` is handled separately via `arcsinAntideriv_one`
(`π/2 - 1 > 0` since `π > 3`). It is the lower half of the squeeze in
`logu_arcsinAntideriv_tendsto`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`, `arcsinAntideriv_eq_integral`, `arcsinAntideriv_one`.
**Used by:** `logu_arcsinAntideriv_tendsto`. -/
theorem arcsinAntideriv_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ arcsinAntideriv x := by
  rcases eq_or_lt_of_le hx.2 with heq | hlt
  · subst heq; rw [arcsinAntideriv_one]; linarith [Real.pi_gt_three]
  · rw [arcsinAntideriv_eq_integral ⟨hx.1, hlt⟩]
    exact intervalIntegral.integral_nonneg hx.1 fun t ht => Real.arcsin_nonneg.2 ht.1

/-- **`g(x) ≤ (π/4)x²` on `[0,1]`, the upper half of the squeeze in
`logu_arcsinAntideriv_tendsto`.**

### Summary of Proof
By comparing integrands: `arcsin t ≤ (π/2)t` on `[0,1]` (concavity, `arcsin_le_half_pi_mul`),
and integrating gives `(π/4)x²`. The endpoint `x = 1` is again separate, where the claim is
`π/2 - 1 ≤ π/4`, i.e. `π ≤ 4`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`, `arcsinAntideriv_eq_integral`, `arcsinAntideriv_one`,
`arcsin_le_half_pi_mul`.
**Used by:** `logu_arcsinAntideriv_tendsto`. -/
theorem arcsinAntideriv_le {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    arcsinAntideriv x ≤ (Real.pi / 4) * x ^ 2 := by
  rcases eq_or_lt_of_le hx.2 with heq | hlt
  · subst heq; rw [arcsinAntideriv_one]; nlinarith [Real.pi_le_four]
  · rw [arcsinAntideriv_eq_integral ⟨hx.1, hlt⟩]
    have hbound : (Real.pi / 4) * x ^ 2 = ∫ t in (0:ℝ)..x, (Real.pi / 2) * t := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    rw [hbound]
    refine intervalIntegral.integral_mono_on hx.1
      (Real.continuous_arcsin.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _) fun t ht => ?_
    exact arcsin_le_half_pi_mul ⟨ht.1, by linarith [ht.2, hlt.le]⟩

/-- **The real derivative of `log‖ζ(1+ru)‖` along the segment `u > 0`.** Built exactly like
`Phi_im_hasDerivAt`, but along a *horizontal* (real) line rather than a vertical one, and via
`Complex.log` (needing `ζ(1+ru) ∈ Complex.slitPlane`, immediate from `riemannZeta_pos_of_one_lt`
since `ζ(1+ru)` is then a *positive real*) rather than the `LSeries GTerm` route
`Phi_hasDerivAt` uses.**

### Summary of Proof
Built exactly like `Phi_im_hasDerivAt`, but along a *horizontal* (real) line rather than a
vertical one: `log‖ζ(1+ru)‖` is the real part of `log ζ` there, and differentiating the
composite gives `r · Re(ζ'/ζ(1+ru))`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** none — kept as the FTC ingredient for `log ζ` along the real axis, the shape any
further sharpening of the `c5` bound would need. -/
theorem logzeta_real_hasDerivAt (r u : ℝ) (hru : 0 < r * u) :
    HasDerivAt (fun w : ℝ => Real.log ‖riemannZeta ((1 + r * w : ℝ) : ℂ)‖)
      (r * (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) / riemannZeta ((1 + r * u : ℝ) : ℂ)).re) u := by
  have hσ : (1:ℝ) < 1 + r * u := by linarith
  have hpos : 0 < riemannZeta ((1 + r * u : ℝ) : ℂ) := riemannZeta_pos_of_one_lt hσ
  have hslit : riemannZeta ((1 + r * u : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Or.inl (Complex.pos_iff.mp hpos).1
  have haffine : HasDerivAt (fun w : ℂ => (1:ℂ) + (r:ℂ) * w) (r:ℂ) ((u:ℝ):ℂ) := by
    simpa using (hasDerivAt_id ((u:ℝ):ℂ)).const_mul (r:ℂ) |>.const_add (1:ℂ)
  have heval : (fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ) = ((1 + r * u : ℝ) : ℂ) := by
    push_cast; ring
  have hζdiff :
      HasDerivAt riemannZeta
        (deriv riemannZeta ((fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ)))
        ((fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ)) := by
    rw [heval]
    exact (differentiableAt_riemannZeta (by exact_mod_cast ne_of_gt hσ)).hasDerivAt
  have hcomp0 := hζdiff.comp ((u:ℝ):ℂ) haffine
  rw [heval] at hcomp0
  have hcomp : HasDerivAt (fun w : ℂ => riemannZeta ((1:ℂ) + (r:ℂ) * w))
      (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) * r) ((u:ℝ):ℂ) := hcomp0
  have hslit' : riemannZeta ((fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ)) ∈ Complex.slitPlane := by
    rw [heval]; exact hslit
  have hlograw : HasDerivAt Complex.log (riemannZeta ((fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ)))⁻¹
      (riemannZeta ((fun w : ℂ => (1:ℂ) + (r:ℂ) * w) ((u:ℝ):ℂ))) := Complex.hasDerivAt_log hslit'
  have hlog0 := hlograw.comp ((u:ℝ):ℂ) hcomp
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (riemannZeta ((1:ℂ) + (r:ℂ) * w)))
      ((riemannZeta ((1 + r * u : ℝ) : ℂ))⁻¹ * (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) * r))
      ((u:ℝ):ℂ) := by
    have hcomp_eq : (Complex.log ∘ fun w : ℂ => riemannZeta ((1:ℂ) + (r:ℂ) * w))
        = fun w : ℂ => Complex.log (riemannZeta ((1:ℂ) + (r:ℂ) * w)) := rfl
    rw [hcomp_eq, heval] at hlog0
    exact hlog0
  have hre := hlog.real_of_complex
  have heq2 : ∀ w : ℝ, (Complex.log (riemannZeta ((1:ℂ) + (r:ℂ) * (w:ℂ)))).re
      = Real.log ‖riemannZeta ((1 + r * w : ℝ) : ℂ)‖ := by
    intro w; rw [Complex.log_re]; congr 2; push_cast; ring
  simp only [heq2] at hre
  convert hre using 1
  rw [div_eq_inv_mul,
    show (riemannZeta ((1 + r * u : ℝ) : ℂ))⁻¹ * (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) * (r:ℂ))
      = (r:ℂ) * ((riemannZeta ((1 + r * u : ℝ) : ℂ))⁻¹ * deriv riemannZeta ((1 + r * u : ℝ) : ℂ))
      by ring,
    Complex.re_ofReal_mul]

/-- **`x² log x → 0` as `x → 0⁺`.**

### Summary of Proof
Obtained from Mathlib's `tendsto_log_div_rpow_nhdsGT_zero` at exponent `-2`, rewriting
`log x / x^{-2}` as `x² log x`. This is the quantitative input that makes the `u = 0` endpoint of
`integral_log_mul_arcsin` harmless — the `log u` singularity is killed by the `O(u²)` vanishing
of `arcsinAntideriv`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `logu_arcsinAntideriv_tendsto`. -/
theorem eps_sq_mul_log_tendsto :
    Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.log x)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
  have h := tendsto_log_div_rpow_nhdsGT_zero (r := (-2:ℝ)) (by norm_num)
  have heq : ∀ᶠ (x:ℝ) in nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ)),
      Real.log x / x ^ (-2:ℝ) = x ^ 2 * Real.log x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Set.mem_Ioi] at hx
    rw [Real.rpow_neg hx.le, Real.rpow_two]; field_simp
  exact h.congr' heq

/-- **`sqrtAntideriv u := √(1-u²) - log(1+√(1-u²))`, an antiderivative of `-u/(1+√(1-u²))`
(`sqrtAntideriv_hasDerivAt`) — equivalently, for `u ≠ 0`, of `(√(1-u²)-1)/u`
(`sqrtAntideriv_identity`).**

### Summary of Proof
A definition. It is the antiderivative used by `integral_sqrt_sub_one_div` to evaluate
`∫₀¹ (√(1-u²)-1)/u du`, which is in turn the second half of `integral_log_mul_arcsin`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_sqrt_sub_one_div`, `sqrtAntideriv_continuous`, `sqrtAntideriv_hasDerivAt`,
`sqrtAntideriv_one`, `sqrtAntideriv_zero`. -/
noncomputable def sqrtAntideriv (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2) - Real.log (1 + Real.sqrt (1 - x ^ 2))

/-- **`sqrtAntideriv' (u) = -u/(1+√(1-u²))` on `(-1,1)`.**

### Summary of Proof
Chain rule on both summands of `√(1-u²) - log(1+√(1-u²))`: each contributes a multiple of
`-u/√(1-u²)`, and combining over the common denominator collapses to the stated form (the
`√(1-u²)` in the denominator cancels).

### References
No tex counterpart.

### Dependencies
**Depends on:** `sqrtAntideriv`.
**Used by:** `integral_sqrt_sub_one_div`. -/
theorem sqrtAntideriv_hasDerivAt {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt sqrtAntideriv (-u / (1 + Real.sqrt (1 - u ^ 2))) u := by
  have hpos : (0:ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hsq : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (-u / Real.sqrt (1 - u ^ 2)) u := by
    have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by simpa using (hasDerivAt_pow 2 u)
    have hd : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * u)) u := by
      have := hp2.const_sub (1:ℝ); simpa using this
    have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u hd
    refine hcomp.congr_deriv ?_
    field_simp
  have hlogarg : (1:ℝ) + Real.sqrt (1 - u ^ 2) ≠ 0 := by positivity
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + Real.sqrt (1 - x ^ 2)))
      ((1 + Real.sqrt (1 - u ^ 2))⁻¹ * (-u / Real.sqrt (1 - u ^ 2))) u := by
    have hinner : HasDerivAt (fun x : ℝ => 1 + Real.sqrt (1 - x ^ 2))
        (-u / Real.sqrt (1 - u ^ 2)) u := hsq.const_add 1
    exact (Real.hasDerivAt_log hlogarg).comp u hinner
  have h3 := hsq.sub hlog
  refine h3.congr_deriv ?_
  have hne : Real.sqrt (1 - u ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp
  ring

/-- **The algebraic identity `-u/(1+√(1-u²)) = (√(1-u²)-1)/u` on `[0,1]` — rationalising the
denominator, using `(√(1-u²))² = 1-u²`.**

### Summary of Proof
`field_simp` and `nlinarith` on `(√(1-u²))² = 1-u²`. It converts `sqrtAntideriv`'s derivative
into the form that actually appears in `integral_sqrt_sub_one_div`'s integrand. At `u = 0` both
sides are `0` under Lean's `x/0 = 0` convention, so the identity holds on the closed interval.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_mul_arcsin`, `integral_sqrt_sub_one_div`. -/
theorem sqrtAntideriv_identity {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    -u / (1 + Real.sqrt (1 - u ^ 2)) = (Real.sqrt (1 - u ^ 2) - 1) / u := by
  rcases eq_or_lt_of_le hu.1 with heq | hpos
  · simp [← heq]
  · have hnn : (0:ℝ) ≤ 1 - u ^ 2 := by nlinarith [hu.2]
    have hsq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt hnn
    have hden : (1:ℝ) + Real.sqrt (1 - u ^ 2) ≠ 0 := by positivity
    field_simp
    nlinarith [hsq]

/-- **`sqrtAntideriv 0 = 1 - log 2`, by direct evaluation (`√1 = 1`, `log(1+1) = log 2`).**

### Summary of Proof
`simp` on the definition. This is one of the two boundary values in
`integral_sqrt_sub_one_div`, and the origin of the `log 2` appearing in
`integral_log_mul_arcsin`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `sqrtAntideriv`.
**Used by:** `integral_sqrt_sub_one_div`. -/
theorem sqrtAntideriv_zero : sqrtAntideriv 0 = 1 - Real.log 2 := by
  have h2 : (1:ℝ) + 1 = 2 := by norm_num
  simp [sqrtAntideriv, h2]

/-- **`sqrtAntideriv 1 = 0`, by direct evaluation (`√0 = 0`, `log 1 = 0`).**

### Summary of Proof
`simp` on the definition. This is the other boundary value in `integral_sqrt_sub_one_div`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `sqrtAntideriv`.
**Used by:** `integral_sqrt_sub_one_div`. -/
theorem sqrtAntideriv_one : sqrtAntideriv 1 = 0 := by simp [sqrtAntideriv]

/-- **`sqrtAntideriv` is continuous on all of `ℝ`** — note `1 + √(1-x²) ≥ 1 > 0` always (`√` of a
negative argument being `0`), so the logarithm is never evaluated at a bad point, even outside
`[-1,1]`.

### Summary of Proof
`fun_prop` on the two summands, with `positivity` for the logarithm's argument. Continuity *at
the endpoints* — where the derivative fails to exist — is exactly the hypothesis
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` needs in
`integral_sqrt_sub_one_div`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `sqrtAntideriv`.
**Used by:** `integral_sqrt_sub_one_div`. -/
theorem sqrtAntideriv_continuous : Continuous sqrtAntideriv := by
  have h1 : Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2)) := by fun_prop
  exact h1.sub (Continuous.log (by fun_prop) fun x => by positivity)

/-- **`∫₀¹ (√(1-u²)-1)/u du = log 2 - 1`, via `sqrtAntideriv` (no singularity: the integrand extends
continuously to `0` at `u = 0`, and `sqrtAntideriv` — though not differentiable at the *right*
endpoint `u = 1`, where `arcsin`-type functions never are — is continuous there, which is all
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` needs).**

### Summary of Proof
Via `sqrtAntideriv`. There is no singularity to handle: the integrand `(√(1-u²)-1)/u`
extends continuously to `0` at `u = 0`, and `sqrtAntideriv` is its antiderivative, so the
fundamental theorem of calculus applies directly and evaluates to `log 2 - 1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `sqrtAntideriv`, `sqrtAntideriv_continuous`, `sqrtAntideriv_hasDerivAt`,
`sqrtAntideriv_identity`, `sqrtAntideriv_one`, `sqrtAntideriv_zero`.
**Used by:** `integral_log_mul_arcsin`. -/
theorem integral_sqrt_sub_one_div :
    (∫ u in (0:ℝ)..1, (Real.sqrt (1 - u ^ 2) - 1) / u) = Real.log 2 - 1 := by
  have hderiv : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt sqrtAntideriv
      ((Real.sqrt (1 - u ^ 2) - 1) / u) u := by
    intro u hu
    have h := sqrtAntideriv_hasDerivAt (⟨by linarith [hu.1], hu.2⟩ : u ∈ Set.Ioo (-1:ℝ) 1)
    rwa [sqrtAntideriv_identity ⟨hu.1.le, hu.2.le⟩] at h
  have hcont : ContinuousOn (fun u : ℝ => (Real.sqrt (1 - u ^ 2) - 1) / u) (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.congr (f := fun u => -u / (1 + Real.sqrt (1 - u ^ 2)))
    · fun_prop (disch := intro x hx; positivity)
    · intro u hu; exact (sqrtAntideriv_identity hu).symm
  have hint :
      IntervalIntegrable (fun u : ℝ => (Real.sqrt (1 - u ^ 2) - 1) / u) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have ha :
      Filter.Tendsto sqrtAntideriv (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds (sqrtAntideriv 0)) :=
    (sqrtAntideriv_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb :
      Filter.Tendsto sqrtAntideriv (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds (sqrtAntideriv 1)) :=
    (sqrtAntideriv_continuous.tendsto 1).mono_left nhdsWithin_le_nhds
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ) < 1) hderiv hint ha hb
  rw [heq, sqrtAntideriv_one, sqrtAntideriv_zero]
  ring

/-- **Pointwise, unconditionally (including at `u = 0`, where both sides are `0` by Lean's `x/0 = 0`
convention): `g(u)/u = arcsin u + (√(1-u²)-1)/u`.**

### Summary of Proof
Direct algebra from the definition of `g`, valid pointwise and unconditionally. At `u = 0`
both sides are `0` — the left by Lean's `x/0 = 0` convention, the right because
`arcsin 0 = 0` and the second term is `0/0`. So no side condition is needed.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`.
**Used by:** `integral_log_mul_arcsin`. -/
theorem div_arcsinAntideriv_eq (u : ℝ) :
    arcsinAntideriv u / u = Real.arcsin u + (Real.sqrt (1 - u ^ 2) - 1) / u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [arcsinAntideriv]
  · unfold arcsinAntideriv; field_simp; ring

/-- **`g(u)·log(u) → 0` as `u → 0⁺`, via the squeeze `(π/4)u²log(u) ≤ g(u)·log(u) ≤ 0` (using
`arcsinAntideriv_le`/`_nonneg` and `eps_sq_mul_log_tendsto`).**

### Summary of Proof
A squeeze: `(π/4)u²log(u) ≤ g(u)·log(u) ≤ 0` on `(0,1)`, using `arcsinAntideriv_le` and
`arcsinAntideriv_nonneg` for the bounds on `g`, and `eps_sq_mul_log_tendsto` for
`u²log(u) → 0`. Both bounding sequences tend to `0`, so the middle does too.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`, `arcsinAntideriv_le`, `arcsinAntideriv_nonneg`,
`eps_sq_mul_log_tendsto`.
**Used by:** `integral_log_mul_arcsin`. -/
theorem logu_arcsinAntideriv_tendsto :
    Filter.Tendsto (fun u : ℝ => Real.log u * arcsinAntideriv u)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
  have hbound : Filter.Tendsto (fun u : ℝ => (Real.pi / 4) * (u ^ 2 * Real.log u))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
    simpa using eps_sq_mul_log_tendsto.const_mul (Real.pi / 4)
  have hu1 : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ)) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbound tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin, hu1] with u hu hu1'
    rw [Set.mem_Ioi] at hu; rw [Set.mem_Iio] at hu1'
    have hple : arcsinAntideriv u ≤ (Real.pi / 4) * u ^ 2 := arcsinAntideriv_le ⟨hu.le, hu1'.le⟩
    have hlogneg : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1'.le
    nlinarith [mul_le_mul_of_nonpos_left hple hlogneg]
  · filter_upwards [self_mem_nhdsWithin, hu1] with u hu hu1'
    rw [Set.mem_Ioi] at hu; rw [Set.mem_Iio] at hu1'
    have hlogneg : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1'.le
    have hpnn : 0 ≤ arcsinAntideriv u := arcsinAntideriv_nonneg ⟨hu.le, hu1'.le⟩
    exact mul_nonpos_of_nonpos_of_nonneg hlogneg hpnn

/-- **The elementary integral behind the direct log-ζ route.**
`∫₀¹ log(u)·arcsin(u) du = 2 - π/2 - log 2`, via one further integration by parts against
`arcsinAntideriv` (`g`): `∫₀¹ log(u)·arcsin(u) du = -∫₀¹ (1/u)·g(u) du` (the boundary term
`log(u)·g(u)` vanishes at both ends: at `u=1` since `log 1 = 0`, at `u=0` via
`logu_arcsinAntideriv_tendsto`), and `(1/u)·g(u) = arcsin(u) + (√(1-u²)-1)/u`
(`div_arcsinAntideriv_eq`) integrates to `(π/2-1) + (log 2 - 1)` via `integral_arcsin_zero_one` and
`integral_sqrt_sub_one_div`.**

### Summary of Proof
One further integration by parts, against `arcsinAntideriv`: the boundary term vanishes by
`logu_arcsinAntideriv_tendsto` at `0` and by `g(1)·log 1 = 0` at `1`, leaving
`-∫₀¹ g(u)/u du`, which `div_arcsinAntideriv_eq` splits into `∫arcsin` and
`integral_sqrt_sub_one_div`. Evaluating gives `2 - π/2 - log 2`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcsinAntideriv`, `arcsinAntideriv_hasDerivAt`, `div_arcsinAntideriv_eq`,
`integral_arcsin_zero_one`, `integral_sqrt_sub_one_div`, `logu_arcsinAntideriv_tendsto`,
`sqrtAntideriv_identity`.
**Used by:** `outside3_lt`. -/
theorem integral_log_mul_arcsin :
    (∫ u in (0:ℝ)..1, Real.log u * Real.arcsin u) = 2 - Real.pi / 2 - Real.log 2 := by
  have hderiv : ∀ u ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.log u * arcsinAntideriv u)
        (Real.log u * Real.arcsin u + (1 / u) * arcsinAntideriv u) u := by
    intro u hu
    have h1 : HasDerivAt Real.log (1 / u) u := by
      simpa using Real.hasDerivAt_log (ne_of_gt hu.1)
    have h2 : HasDerivAt arcsinAntideriv (Real.arcsin u) u :=
      arcsinAntideriv_hasDerivAt ⟨by linarith [hu.1], hu.2⟩
    refine (h1.mul h2).congr_deriv ?_
    ring
  have heqfun : ∀ u : ℝ, (1 / u) * arcsinAntideriv u
      = Real.arcsin u + (Real.sqrt (1 - u ^ 2) - 1) / u := by
    intro u; rw [one_div, ← div_eq_inv_mul]; exact div_arcsinAntideriv_eq u
  have hcont2 : ContinuousOn (fun u : ℝ => (Real.sqrt (1 - u ^ 2) - 1) / u) (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.congr (f := fun u => -u / (1 + Real.sqrt (1 - u ^ 2)))
    · fun_prop (disch := intro x hx; positivity)
    · intro u hu; exact (sqrtAntideriv_identity hu).symm
  have hint1 :
      IntervalIntegrable (fun u : ℝ => Real.log u * Real.arcsin u) MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn Real.continuous_arcsin.continuousOn
  have hint2 :
      IntervalIntegrable (fun u : ℝ => (1 / u) * arcsinAntideriv u) MeasureTheory.volume 0 1 := by
    simp_rw [heqfun]
    exact (Real.continuous_arcsin.intervalIntegrable _ _).add
      (hcont2.intervalIntegrable_of_Icc (by norm_num))
  have hint := hint1.add hint2
  have ha : Filter.Tendsto (fun u : ℝ => Real.log u * arcsinAntideriv u)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := logu_arcsinAntideriv_tendsto
  have hb : Filter.Tendsto (fun u : ℝ => Real.log u * arcsinAntideriv u)
      (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds 0) := by
    have hcontp : ContinuousAt arcsinAntideriv 1 := by
      have hc : Continuous arcsinAntideriv := by unfold arcsinAntideriv; fun_prop
      exact hc.continuousAt
    have hcontl : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    have hc : ContinuousAt (fun u : ℝ => Real.log u * arcsinAntideriv u) 1 := hcontl.mul hcontp
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
    simpa [Real.log_one] using this
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ) < 1) hderiv hint ha hb
  have hsplit : (∫ u in (0:ℝ)..1, Real.log u * Real.arcsin u + (1 / u) * arcsinAntideriv u)
      = (∫ u in (0:ℝ)..1, Real.log u * Real.arcsin u)
        + ∫ u in (0:ℝ)..1, (1/u) * arcsinAntideriv u :=
    intervalIntegral.integral_add hint1 hint2
  rw [hsplit] at heq
  have hval2 : (∫ u in (0:ℝ)..1, (1/u) * arcsinAntideriv u)
      = (Real.pi / 2 - 1) + (Real.log 2 - 1) := by
    simp_rw [heqfun]
    rw [intervalIntegral.integral_add (Real.continuous_arcsin.intervalIntegrable _ _)
      (hcont2.intervalIntegrable_of_Icc (by norm_num)),
      integral_arcsin_zero_one, integral_sqrt_sub_one_div]
  rw [hval2] at heq
  linarith [heq]

/-- **The pointwise bound `log ζ(1+x) ≤ -log(x) + γx`**, `0 < x ≤ 2`, cited by
`ZerosInShortIntervals.tex`'s proof of Proposition `\ref{prop:outside3}`
(Proposition 23)'s "Moreover" clause as a consequence of Lemma `\ref{lemma:logderzetabound}`
(Lemma 38, `Background.LogDerivZetaLaurent.logderzetabound`).**

### Summary of Proof
The tex derives this from Lemma `\ref{lemma:logderzetabound}` (Lemma 38), and that is what the
Lean does — but at `N = 0`, not the `N = 1` the tex's phrasing suggests. Claim 3's upper bound at
`N = 0` has a *single* summand, `a₀x`, so it reads `log‖ζ(1+x)‖ < -log x + a₀x` directly; with
`a₀ = γ` (`logDerivZetaCoeff_zero`) that is the statement, and the strict `<` gives the `≤` for
free.

### Lean Notes
Taking `N = 0` avoids the side condition the `N = 1` route needs. At `N = 1` the bound carries
trailing terms `-(a₁/2)x² + (a₂/3)x³`, and one must check they are `≤ 0` on `0 < x ≤ 2` (true,
via `a₂x ≤ a₁` from antitonicity, but extra work). The `N = 0` instance is available because
`logderzetabound` is stated in the `2N-1` index convention, where `N = 0` leaves the shorter sum
empty rather than requiring truncated natural subtraction.

`logderzetabound`'s claims need `0 < x`, which this statement carries: at `x = 0` the `-log x`
term is Lean's junk value and the bound fails.

Upstream, claim 3 rests on Lemma 38's numeric input `logDerivZetaG_boundary_bound`, a field of
`LogDerivZetaLaurent.LaurentCertificate`, so this theorem is conditional on that class.

### References
tex: cited in the proof of Proposition `\ref{prop:outside3}` (Proposition 23)'s "Moreover"
clause, as a consequence of Lemma `\ref{lemma:logderzetabound}` (Lemma 38).

### Dependencies
**Depends on:** `Background.LogDerivZetaLaurent.logderzetabound_claim_three`,
`Background.LogDerivZetaLaurent.logDerivZetaCoeff_zero`.
**Used by:** `outside3_lt`. -/
theorem logzeta_le_linear {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    Real.log ‖riemannZeta (1 + x : ℂ)‖ ≤ -Real.log x + Real.eulerMascheroniConstant * x := by
  have h := (logderzetabound_claim_three hx0 hx2 0).2
  norm_num [logDerivZetaCoeff_zero] at h
  linarith

/-- **Proposition `\ref{prop:outside3}` (Proposition 23), secondary explicit bound ("Moreover"
clause)**, matching `ZerosInShortIntervals.tex` — via the direct pointwise bound
`logzeta_le_linear`, itself citing Lemma `\ref{lemma:logderzetabound}` (Lemma 38), so this is
conditional on `LogDerivZetaLaurent.LaurentCertificate`.

### Summary of Proof
Bound the integrand of `c5`'s integral pointwise by `logzeta_le_linear` at `x = ru`, then
integrate. The tex's own intermediate bracket is
`∫₀¹ log ζ(1+ru)·arcsin(u) du ≤ -2 + π/2 + γπr/8 - (π/2)log r + log(2r)`,
which the three exact integrals `JensenBounds.integral_arcsin_zero_one` (`= π/2-1`),
`JensenBounds.integral_mul_arcsin_zero_one` (`= π/8`) and this file's `integral_log_mul_arcsin`
(`= 2-π/2-log2`) reproduce. Scaling by `2r/π` term by term — `(2r/π)(-2) = -4r/π`,
`(2r/π)(π/2) = r` (**coefficient `+1`**), `(2r/π)(γπr/8) = γr²/4`,
`(2r/π)(-(π/2)log r) = -r·log r`, `(2r/π)log(2r)` unchanged — sums to
`r·(-4/π + 1 + (γ/4)r - log r + (2/π)log(2r))`, the constant printed in the tex.

**Hypothesis note.** The tex's Moreover clause assumes only `r > 0`; this theorem additionally
assumes `r ≤ 2`, inherited from `logzeta_le_linear`'s `x ≤ 2` (itself from `logderzetabound`'s
`x ∈ (0,2]` range), applied at `x = r·u` with `u ∈ (0,1]`. Nothing uses this bound yet, and any
consumer would come through `rectangularjensen`, whose `hr1 : r < 1` already implies it.

### References
tex: Proposition `\ref{prop:outside3}` (Proposition 23), Lemma `\ref{lemma:logderzetabound}`
(Lemma 38).

### Dependencies
**Depends on:** `Phi`, `c5`, `integral_arcsin_zero_one`, `integral_log_mul_arcsin`,
`integral_mul_arcsin_zero_one`, `logzeta_arcsin_integrable`, `logzeta_le_linear`.
**Used by:** none. -/
theorem outside3_lt {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 2) :
    c5 r ≤ (Phi (1 + r : ℂ)).re
        + r * (-4 / Real.pi + 1 + Real.eulerMascheroniConstant / 4 * r
            - Real.log r + 2 / Real.pi * Real.log (2 * r)) := by
  have hpi := Real.pi_pos
  rw [c5]
  have hpt : ∀ u ∈ Set.Ioc (0:ℝ) 1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u
      ≤ (-Real.log (r * u) + Real.eulerMascheroniConstant * (r * u)) * Real.arcsin u := by
    intro u hu
    have hzu : 0 < r * u := mul_pos hr0 hu.1
    have hzu2 : r * u ≤ 2 := by nlinarith [hu.2, hr2]
    have h := logzeta_le_linear hzu hzu2
    push_cast at h
    exact mul_le_mul_of_nonneg_right h (Real.arcsin_nonneg.2 hu.1.le)
  have hint1 : IntervalIntegrable
      (fun u : ℝ => Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u)
      MeasureTheory.volume 0 1 :=
    logzeta_arcsin_integrable r 0 1
  set g : ℝ → ℝ := fun u => -Real.log r * Real.arcsin u
      + (-(Real.log u * Real.arcsin u) + Real.eulerMascheroniConstant * r * (u * Real.arcsin u))
    with hg_def
  -- `Set.Ioc 0 1` already excludes `u = 0` by construction, so this is a genuine pointwise
  -- equality on that set (no measure-zero exclusion needed, unlike `hae` below which must range
  -- over the endpoint-inclusive `Icc` to match `integral_mono_ae_restrict`'s expected shape).
  have hpteq : ∀ u ∈ Set.Ioc (0:ℝ) 1,
      (-Real.log (r * u) + Real.eulerMascheroniConstant * (r * u)) * Real.arcsin u = g u := by
    intro u hu
    rw [hg_def, Real.log_mul hr0.ne' hu.1.ne']
    ring
  have hA : IntervalIntegrable (fun u : ℝ => -Real.log r * Real.arcsin u)
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
  have hB : IntervalIntegrable (fun u : ℝ => -(Real.log u * Real.arcsin u))
      MeasureTheory.volume 0 1 :=
    (intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      Real.continuous_arcsin.continuousOn).neg
  have hC : IntervalIntegrable (fun u : ℝ => Real.eulerMascheroniConstant * r * (u * Real.arcsin u))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
  have hBC : IntervalIntegrable
      (fun u : ℝ => -(Real.log u * Real.arcsin u)
        + Real.eulerMascheroniConstant * r * (u * Real.arcsin u))
      MeasureTheory.volume 0 1 := hB.add hC
  have hintg : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    rw [hg_def]; exact hA.add hBC
  have hint2 : IntervalIntegrable
      (fun u : ℝ => (-Real.log (r * u) + Real.eulerMascheroniConstant * (r * u)) * Real.arcsin u)
      MeasureTheory.volume 0 1 := by
    apply hintg.congr_ae
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    have huIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)
    rw [huIoc]
    exact Filter.Eventually.of_forall fun u hu => (hpteq u hu).symm
  have hae : (fun u : ℝ => Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun u : ℝ =>
        (-Real.log (r * u) + Real.eulerMascheroniConstant * (r * u)) * Real.arcsin u) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 (MeasureTheory.measure_singleton (0:ℝ))]
      with u hu hmem
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    exact hpt u ⟨lt_of_le_of_ne hmem.1 (Ne.symm hu), hmem.2⟩
  have hmono := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ) ≤ 1) hint1 hint2 hae
  have hgval : (∫ u in (0:ℝ)..1, g u)
      = -Real.log r * (Real.pi / 2 - 1) - (2 - Real.pi / 2 - Real.log 2)
        + Real.eulerMascheroniConstant * r * (Real.pi / 8) := by
    rw [hg_def, intervalIntegral.integral_add hA hBC,
      intervalIntegral.integral_const_mul, integral_arcsin_zero_one,
      intervalIntegral.integral_add hB hC,
      intervalIntegral.integral_neg, integral_log_mul_arcsin,
      intervalIntegral.integral_const_mul, integral_mul_arcsin_zero_one]
    ring
  have hval : (∫ u in (0:ℝ)..1,
        (-Real.log (r * u) + Real.eulerMascheroniConstant * (r * u)) * Real.arcsin u)
      = -Real.log r * (Real.pi / 2 - 1) - (2 - Real.pi / 2 - Real.log 2)
        + Real.eulerMascheroniConstant * r * (Real.pi / 8) := by
    rw [intervalIntegral.integral_congr_ae (by
      have huIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)
      rw [huIoc]
      exact Filter.Eventually.of_forall hpteq)]
    exact hgval
  rw [hval] at hmono
  have hcoef : (2 * r / Real.pi) *
      (-Real.log r * (Real.pi / 2 - 1) - (2 - Real.pi / 2 - Real.log 2)
        + Real.eulerMascheroniConstant * r * (Real.pi / 8))
      = r * (-4 / Real.pi + 1 + Real.eulerMascheroniConstant / 4 * r
          - Real.log r + 2 / Real.pi * Real.log (2 * r)) := by
    have hlog2r : Real.log (2 * r) = Real.log 2 + Real.log r := Real.log_mul (by norm_num) hr0.ne'
    rw [hlog2r]; field_simp; ring
  have hfinal := mul_le_mul_of_nonneg_left hmono (show (0:ℝ) ≤ 2 * r / Real.pi by positivity)
  rw [hcoef] at hfinal
  linarith [hfinal]

/-- **`B_{1,α,r}` from Theorem `\ref{thm:rectangularjensen}` (Theorem 24).**

### Summary of Proof
A definition, transcribing the tex's `B_{1,α,r} = c_{1,r}/D_{r,α}` verbatim. It is the
`log|t|` coefficient of the Jensen-mechanism main term.

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `c1`, `rectDenom`.
**Used by:** `C2Jensen`, `C2JensenP`, `UJensen`, `rectangularjensen`, `rectangularjensen_tight`,
`ConstantSigns.B1_nonneg`. -/
noncomputable def B1 (α r : ℝ) : ℝ := c1 r / rectDenom r α

/-- **`B_{2,α,r}` from Theorem `\ref{thm:rectangularjensen}` (Theorem 24).**

### Summary of Proof
A definition, transcribing the tex's `B_{2,α,r} = c_{2,r}/(π D_{r,α})` verbatim. It is
the `log log|t|` coefficient.

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `c2`, `rectDenom`.
**Used by:** `C2Jensen`, `C2JensenP`, `UJensen`, `rectangularjensen`, `rectangularjensen_tight`,
`ConstantSigns.B2_nonneg`. -/
noncomputable def B2 (α r : ℝ) : ℝ := c2 r / (Real.pi * rectDenom r α)

/-- **`B_{3,α,r}` from Theorem `\ref{thm:rectangularjensen}` (Theorem 24).**

### Summary of Proof
A definition, transcribing the tex's `B_{3,α,r} = c_{3,r}/(π D_{r,α})` verbatim. It is
the constant-term coefficient.

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `c3`, `rectDenom`.
**Used by:** `C2Jensen`, `C2JensenP`, `UJensen`, `rectangularjensen`, `rectangularjensen_tight`,
`ConstantSigns.B3_nonneg`. -/
noncomputable def B3 (α r : ℝ) : ℝ := c3 r / (Real.pi * rectDenom r α)

/-- **`B_{4,α,r} = (2Φ(1)+c_{5,r})/D_{r,α}` from Theorem `\ref{thm:rectangularjensen}`
(Theorem 24), matching `ZerosInShortIntervals.tex`.**

### Summary of Proof
**Why the factor is `2Φ(1)` and not `Φ(1)/π`.** Proposition `\ref{prop:outside2}`
(Proposition 22) is stated in the `(1/(2π))`-normalised form
`(1/(2π))∫_{T-h-α̂}^{T+h+α̂} log|ζ(1+it)|dt ≤ Φ(1)/π`, i.e. `∫ log|ζ(1+it)|dt ≤ 2Φ(1)` — and it is
the *un-normalised* integral that occurs in `jensenrectangle`'s numerator, since Jensen's formula
carries `1/(2π)` on the circle average only. Numerically `Φ(1)/π = 0.5722…` against
`2Φ(1) = 3.5951…`; at `α = 1/8`, `r = 0.5185446` that is the difference between
`(0.57217 + 1.11230)/0.674683 = 2.496751` and `(3.5951 + 1.1123)/0.674683 = 6.9772`. `B_4` is a
pure constant — it multiplies neither `h` nor `log|T|` — so the choice affects only the additive
constant, not any asymptotic conclusion.

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24), Proposition `\ref{prop:outside2}`
(Proposition 22).

**Independent numeric check.** `Code/indep_mpmath_tables_spotcheck.py` recomputes `B1`–`B4` and
`α̂_r` from these definitions with plain mpmath at `α = 1/7`, `r = 0.5647100` (alternative chord
triple) and reproduces the Table `\ref{tab:rectangularjensen}` (Table 5) row
`0.2457053, 0.3900919, 1.450119, 6.518765, 0.5463417` to 7 digits (`B4` to `1.5×10⁻⁷` relative,
the difference being the tex's use of the rounded-up `Φ(1)` bound). The `c5` here is the same
script's `c_{5,1/2} = 1.126439` (Table `\ref{tab:crvalues}`, Table 2) recomputed by `quad`.

### Dependencies
**Depends on:** `Phi`, `c5`, `rectDenom`.
**Used by:** `C2Jensen`, `C2JensenQ`, `UJensen`, `rectangularjensen`, `rectangularjensen_tight`,
`ConstantSigns.B4_nonneg`. -/
noncomputable def B4 (α r : ℝ) : ℝ := (2 * (Phi 1).re + c5 r) / rectDenom r α

/-! ### Splitting the circle average in `x`

`rectangularjensen` bounds the three parts of `jensenrectangle`'s numerator separately — the
outside-strip half-circle by `JensenBounds.jensen_easy`, the inside-strip half by `outside3`, and
`-log|ζ(1+i(T+x))|` by `LittlewoodMethod.littlewood_outerlog` — so the numerator has to be split
as a sum of three `x`-integrals, which needs each of them to be interval integrable in `x`. That
is `intervalIntegrable_arcAvg` below; the substantive input is Jensen's formula, which is what
supplies the *lower* bound (`log‖ζ‖` is unbounded below on an arc through a zero). -/



/-- **Interval integrability of `x ↦ log‖ζ(1 + i(T+x))‖`: the composite is real-meromorphic, so
`MeromorphicOn.intervalIntegrable_log_norm` applies (the pole `s = 1` is never hit, and even if it
were, `log‖·‖` of a meromorphic function is integrable regardless).**

### Summary of Proof
The composite `x ↦ ζ(1 + i(T+x))` is real-meromorphic, so Mathlib's
`MeromorphicOn.intervalIntegrable_log_norm` applies: the log of the norm of a meromorphic
function is interval-integrable, its logarithmic singularities being integrable.

### References
No tex counterpart.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `intervalIntegrable_arcAvg`, `rectangularjensen`, `rectangularjensen_tight`. -/
theorem intervalIntegrable_logzeta_line (T c d : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
      MeasureTheory.volume c d := by
  have hmero : MeromorphicOn
      (fun x : ℝ => riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)) (Set.uIcc c d) := by
    intro u _
    have hinner : AnalyticAt ℝ (fun x : ℝ => (1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I) u := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul _ analyticAt_const
      exact AnalyticAt.add analyticAt_const (Complex.ofRealCLM.analyticAt u)
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **`ζ` is measurable: it is continuous off the single point `s = 1`
(`measurable_of_continuousOn_compl_singleton`).**

### Summary of Proof
`ζ` is continuous off the single point `s = 1`, and a function continuous on the
complement of a singleton is measurable — `measurable_of_continuousOn_compl_singleton`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `stronglyMeasurable_arcAvg`. -/
theorem measurable_riemannZeta : Measurable riemannZeta :=
  measurable_of_continuousOn_compl_singleton (1:ℂ)
    (fun _ hs => (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt)

/-- **Strong measurability in `x` of the arc average
`x ↦ ∫_p^q log‖ζ(1+i(T+x)+re^{iθ})‖ dθ`, a side condition for splitting `jensenrectangle`'s
numerator into separately-integrable pieces.**

### Summary of Proof
The two-variable integrand is strongly measurable
(`measurable_riemannZeta` composed with a continuous map, then `norm` and `log`), and
`StronglyMeasurable.integral_prod_right'` integrates out `θ`; the interval integral is expanded as
the difference of the two `Ioc` restrictions. No source counterpart — the tex exchanges these
integrals without comment.

### References
No tex counterpart.

### Dependencies
**Depends on:** `measurable_riemannZeta`.
**Used by:** `intervalIntegrable_arcAvg`. -/
theorem stronglyMeasurable_arcAvg (T r p q : ℝ) :
    MeasureTheory.StronglyMeasurable (fun x : ℝ => ∫ θ in p..q,
      Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
  have hg : Continuous (fun z : ℝ × ℝ => (1:ℂ) + ((T : ℂ) + (z.1 : ℂ)) * Complex.I
      + (r : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I)) := by fun_prop
  have hm : MeasureTheory.StronglyMeasurable (fun z : ℝ × ℝ => Real.log ‖riemannZeta ((1:ℂ)
      + ((T : ℂ) + (z.1 : ℂ)) * Complex.I + (r : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I))‖) :=
    (Real.measurable_log.comp ((measurable_riemannZeta.comp hg.measurable).norm)).stronglyMeasurable
  simp only [intervalIntegral]
  exact (hm.integral_prod_right' (ν := MeasureTheory.volume.restrict (Set.Ioc p q))).sub
    (hm.integral_prod_right' (ν := MeasureTheory.volume.restrict (Set.Ioc q p)))

/-- **The centre of the circle never meets `ζ`'s pole when `r + 1 ≤ |T+x|`.**

### Summary of Proof
If `r + 1 ≤ |T+x|` then the circle's centre `1 + i(T+x)` has imaginary part of modulus at
least `r+1 > 0`, while `ζ`'s pole sits at `1`, which is real. So the two cannot coincide,
and the circle of radius `r` about that centre stays clear of the pole.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `annulus_bound`. -/
theorem circle_ne_one {T r x θ : ℝ} (hr : 0 < r) (hx : r + 1 ≤ |T + x|) :
    (1:ℂ) + ((T:ℂ) + (x:ℂ)) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I) ≠ 1 := by
  intro hc
  have h0 : ((T:ℂ) + (x:ℂ)) * Complex.I = -((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) := by
    linear_combination hc
  have h1 : ‖((T:ℂ) + (x:ℂ)) * Complex.I‖ = |T + x| := by
    rw [show ((T:ℂ)+(x:ℂ)) = ((T + x : ℝ):ℂ) by push_cast; ring, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖-((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ = r := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp]
    simp
  rw [h0, h2] at h1
  linarith

/-- **Uniform bound for `‖ζ‖` on the compact annulus swept by the circles.**

### Summary of Proof
The circles sweep a compact annulus avoiding the pole, `ζ` is continuous there, and a
continuous function on a compact set is bounded — so a uniform bound for `‖ζ‖` exists.

### References
No tex counterpart.

### Dependencies
**Depends on:** `circle_ne_one`.
**Used by:** `intervalIntegrable_arcAvg`. -/
theorem annulus_bound {T r c d : ℝ} (hr : 0 < r)
    (hT : ∀ x ∈ Set.uIcc c d, r + 1 ≤ |T + x|) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ Set.uIcc c d, ∀ θ ∈ Set.uIcc (-Real.pi/2) (3*Real.pi/2),
      ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ M := by
  have hK : IsCompact (Set.uIcc c d ×ˢ Set.uIcc (-Real.pi/2) (3*Real.pi/2)) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hcont : ContinuousOn
      (fun z : ℝ × ℝ => riemannZeta ((1:ℂ) + ((T : ℂ) + (z.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I)))
      (Set.uIcc c d ×ˢ Set.uIcc (-Real.pi/2) (3*Real.pi/2)) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    have hne := circle_ne_one (T := T) (r := r) (x := z.1) (θ := z.2) hr
      (hT z.1 (Set.mem_prod.mp hz).1)
    have hz1 : ContinuousAt riemannZeta ((1:ℂ) + ((T : ℂ) + (z.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I)) :=
      (differentiableAt_riemannZeta hne).continuousAt
    exact ContinuousAt.comp (g := riemannZeta)
      (f := fun w : ℝ × ℝ => (1:ℂ) + ((T : ℂ) + (w.1 : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((w.2 : ℂ) * Complex.I)) hz1 (by fun_prop)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, le_max_right _ _, fun x hx θ hθ => ?_⟩
  exact le_trans (hC (x, θ) (Set.mk_mem_prod hx hθ)) (le_max_left _ _)

/-- **Interval integrability, in `x`, of the arc integral
`x ↦ ∫_p^q log‖ζ(1 + i(T+x) + re^{iθ})‖ dθ`** — the one measure-theoretic fact
`rectangularjensen` needs in order to split `jensenrectangle`'s numerator into three
`x`-integrals and bound each separately.**

### Summary of Proof
**Hypotheses.** The arc must sit inside `[-π/2, 3π/2]` (the range over which `jensenCircleAvg` is
taken) and the circle must stay away from `ζ`'s pole, `r + 1 ≤ |T+x|`; both hold at every call
site, where `r < 1` and the window satisfies `T - h - α̂_r > 13`, so `T + x > r + 1` throughout.

Two-sided control is what makes this work, and the two sides are quite different. *Above*,
`‖ζ‖ ≤ M` on the compact annulus swept out (`annulus_bound`), so the arc integral is at most
`(q-p)·log M`. *Below*, no elementary bound exists — `log‖ζ‖ → -∞` at every zero on the arc — and
the bound comes from **Jensen's formula**: `log_norm_le_jensenCircleAvg` gives
`(1/2π)∫_{-π/2}^{3π/2} log‖ζ‖ ≥ log‖ζ(1+i(T+x))‖`, and the two flanking arcs contribute at most
`2π log M`, so the arc integral is at least `2π log‖ζ(1+i(T+x))‖ - 2π log M`. Both bounds are
dominated by `2π log M + 2π|log‖ζ(1+i(T+x))‖|`, which is interval integrable in `x`
(`intervalIntegrable_logzeta_line`). Measurability is `stronglyMeasurable_arcAvg`, from
`MeasureTheory.StronglyMeasurable.integral_prod_right'` and `measurable_riemannZeta`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `annulus_bound`, `intervalIntegrable_log_zeta_circle`,
`intervalIntegrable_logzeta_line`, `jensenCircleAvg`, `log_norm_le_jensenCircleAvg`,
`stronglyMeasurable_arcAvg`.
**Used by:** `rectangularjensen`, `rectangularjensen_tight`. -/
theorem intervalIntegrable_arcAvg {T r p q c d : ℝ} (hr : 0 < r)
    (hp : -Real.pi/2 ≤ p) (hpq : p ≤ q) (hq : q ≤ 3*Real.pi/2)
    (hT : ∀ x ∈ Set.uIcc c d, r + 1 ≤ |T + x|) :
    IntervalIntegrable (fun x : ℝ => ∫ θ in p..q,
      Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) MeasureTheory.volume c d := by
  obtain ⟨M, hM1, hM⟩ := annulus_bound hr hT
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hpi := Real.pi_pos
  have huI : Set.uIcc (-Real.pi/2) (3*Real.pi/2) = Set.Icc (-Real.pi/2) (3*Real.pi/2) :=
    Set.uIcc_of_le (by linarith)
  -- pointwise: `Z x θ ≤ log M` on the whole arc
  have hZle : ∀ x ∈ Set.uIcc c d, ∀ θ ∈ Set.Icc (-Real.pi/2) (3*Real.pi/2),
      Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ Real.log M := by
    intro x hx θ hθ
    rcases eq_or_lt_of_le (norm_nonneg (riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) with h0 | h0
    · rw [← h0, Real.log_zero]; exact hlogM
    · exact Real.log_le_log h0 (hM x hx θ (by rw [huI]; exact hθ))
  have hbd : ∀ x ∈ Set.uIcc c d,
      |∫ θ in p..q, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
        + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖|
      ≤ 2*Real.pi*Real.log M
        + 2*Real.pi*|Real.log ‖riemannZeta ((1:ℂ) + ((T:ℂ)+(x:ℂ))*Complex.I)‖| := by
    intro x hx
    set s : ℂ := (1:ℂ) + ((T:ℂ)+(x:ℂ))*Complex.I with hs_def
    have hii : ∀ u v : ℝ, IntervalIntegrable
        (fun θ : ℝ => Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        MeasureTheory.volume u v := fun u v => intervalIntegrable_log_zeta_circle s r u v
    have hZle' : ∀ θ ∈ Set.Icc (-Real.pi/2) (3*Real.pi/2),
        Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ ≤ Real.log M :=
      fun θ hθ => hZle x hx θ hθ
    -- Jensen at the centre
    have hTx : r + 1 ≤ |T + x| := hT x hx
    have hball : (1:ℂ) ∉ Metric.closedBall s r := by
      simp only [Metric.mem_closedBall, Complex.dist_eq, not_le, hs_def]
      have he : (1:ℂ) - ((1:ℂ) + ((T:ℂ)+(x:ℂ))*Complex.I) = -(((T + x : ℝ):ℂ) * Complex.I) := by
        push_cast; ring
      rw [he, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hζs : riemannZeta s ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      rw [hs_def]; simp
    have hJ := log_norm_le_jensenCircleAvg hr hball hζs
    have hfull : (∫ θ in (-Real.pi/2)..(3*Real.pi/2),
        Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        = 2*Real.pi * jensenCircleAvg s r := by
      rw [jensenCircleAvg, ← mul_assoc,
        show 2*Real.pi * (1/(2*Real.pi)) = 1 by field_simp, one_mul]
    -- split the full arc at `p` and `q`
    have hsp := intervalIntegral.integral_add_adjacent_intervals (a := -Real.pi/2) (b := p)
      (c := q) (hii _ _) (hii _ _)
    have hsq := intervalIntegral.integral_add_adjacent_intervals (a := -Real.pi/2) (b := q)
      (c := 3*Real.pi/2) (hii _ _) (hii _ _)
    -- the two flanking pieces are at most `logM` times their lengths
    have hflank1 : (∫ θ in (-Real.pi/2)..p,
        Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        ≤ (p - (-Real.pi/2)) * Real.log M := by
      have := intervalIntegral.integral_mono_on (a := -Real.pi/2) (b := p) hp (hii _ _)
        intervalIntegrable_const (fun θ hθ => hZle' θ ⟨hθ.1, by linarith [hθ.2]⟩)
      simpa using this
    have hflank2 : (∫ θ in q..(3*Real.pi/2),
        Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        ≤ (3*Real.pi/2 - q) * Real.log M := by
      have := intervalIntegral.integral_mono_on (a := q) (b := 3*Real.pi/2) hq (hii _ _)
        intervalIntegrable_const (fun θ hθ => hZle' θ ⟨by linarith [hθ.1], hθ.2⟩)
      simpa using this
    have hmid : (∫ θ in p..q,
        Real.log ‖riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        ≤ (q - p) * Real.log M := by
      have := intervalIntegral.integral_mono_on (a := p) (b := q) hpq (hii _ _)
        intervalIntegrable_const (fun θ hθ => hZle' θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
      simpa using this
    have habs : |Real.log ‖riemannZeta s‖| ≥ Real.log ‖riemannZeta s‖ := le_abs_self _
    have habs' : -|Real.log ‖riemannZeta s‖| ≤ Real.log ‖riemannZeta s‖ := neg_abs_le _
    rw [abs_le]
    constructor <;> nlinarith [hsp, hsq, hfull, hJ, hflank1, hflank2, hmid, hlogM, hpi,
      habs, habs']
  -- integrability from measurability + domination
  have hGi : IntervalIntegrable (fun x : ℝ => 2*Real.pi*Real.log M
      + 2*Real.pi*|Real.log ‖riemannZeta ((1:ℂ) + ((T:ℂ)+(x:ℂ))*Complex.I)‖|)
      MeasureTheory.volume c d := by
    exact intervalIntegrable_const.add (((intervalIntegrable_logzeta_line T c d).abs).const_mul _)
  have hmeas := stronglyMeasurable_arcAvg T r p q
  constructor
  · refine MeasureTheory.Integrable.mono' (hGi.1) hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact hbd x (Set.mem_uIcc_of_le (le_of_lt hx.1) hx.2)
  · refine MeasureTheory.Integrable.mono' (hGi.2) hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact hbd x (Set.mem_uIcc_of_ge (le_of_lt hx.1) hx.2)

/-- **The full-circle average splits into the outside-strip half `[π/2, 3π/2]` (bounded by
`JensenBounds.jensen_easy`) and the inside-strip half `[-π/2, π/2]` (bounded by `outside3`), using
`2π`-periodicity of `θ ↦ log‖ζ(s + re^{iθ})‖` to move `[0,2π]` to `[-π/2,3π/2]`.**

### Summary of Proof
`Function.Periodic.intervalIntegral_add_eq` moves `[0, 2π]` to `[-π/2, 3π/2]`, and
`intervalIntegral.integral_add_adjacent_intervals` splits that at `π/2` into the outside-strip
half `[π/2, 3π/2]`, which `rectangularjensen` bounds by `JensenBounds.jensen_easy`, and the
inside-strip half `[-π/2, π/2]`, which it bounds by `outside3`. Integrability of each arc is
`JensenBounds.intervalIntegrable_log_zeta_circle`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `intervalIntegrable_log_zeta_circle`.
**Used by:** `rectangularjensen`, `rectangularjensen_tight`. -/
theorem circle_full_split (T r x : ℝ) :
    (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
          + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
      = (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
          + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
        + (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
            Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
          + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
  have hper : Function.Periodic (fun θ : ℝ =>
      Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
          + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) (2 * Real.pi) := by
    intro θ
    have hexp : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by push_cast; ring
    simp only
    rw [hexp, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h := hper.intervalIntegral_add_eq (-Real.pi/2) 0
  have h1 : (-Real.pi / 2 : ℝ) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  have h2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
  rw [h1, h2] at h
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := -Real.pi/2) (b := Real.pi/2) (c := 3*Real.pi/2)
    (f := fun θ : ℝ => Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
          + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
    (intervalIntegrable_log_zeta_circle ((1:ℂ) + ((T:ℂ) + (x:ℂ)) * Complex.I) r _ _)
    (intervalIntegrable_log_zeta_circle ((1:ℂ) + ((T:ℂ) + (x:ℂ)) * Complex.I) r _ _)
  rw [← h, ← mul_add, ← hadj]
  ring

/-- **Theorem `\ref{thm:rectangularjensen}` (Theorem 24).** For `0 < α ≤ 1`, `α < r < 1`, `h > 0`
and `T - h - α̂_r > 10^{12} + 1`,
`N(T-h,T+h,α) ≤ (2h+2α̂_r)((B₁/π) log|T| + B₂ log log|T| + B₃) + B₄ + (6h+6α̂_r)/((T-h-α̂_r)·D)`,
`D = rectDenom r α`.**

### Summary of Proof
**Follows the source's own three-step recipe**, assembling three paper-level results —
`jensenrectangle`, `JensenBounds.jensen_easy` and `outside3` — plus the measure-theoretic side
condition `intervalIntegrable_arcAvg`. The numerator
of `jensenrectangle` is split at `θ = ±π/2` (`circle_full_split`) into
* the **outside-strip half**, bounded at each `x` by `jensen_easy` at `t = T+x` and then integrated
  over the window: the concavity of `log` and `log log` (`LittlewoodMethod.integral_log_le_window`,
  `integral_loglog_le_window`, packaged as `integral_window_bound`) makes the first-order error
  vanish, leaving `2(h+α̂_r)·(c₁/π·log T + c₂/π·log log T + c₃/π)` plus the `3/t` tail. This is
  where `JensenScaleConstants.c1_nonneg`/`c2_nonneg` are needed — concavity points the right way
  only for nonnegative coefficients.
* the **inside-strip half**, bounded by `outside3` in its `|·|` form, of which only the positive
  direction is used here (`le_abs_self`), giving `c₅,r`;
* the term `-∫ log|ζ(1+i(T+x))|dx`, bounded by
  `LittlewoodMethod.littlewood_outerlog` at `σ = 1`, giving `2Φ(1)`.

**Two points where this "simple" version (kept for comparison, as with `jensen_easy` vs
`jensen_easy_tight`) differs from the manuscript's printed statement** —
`rectangularjensen_tight` below matches `ZerosInShortIntervals.tex`'s own further
tightened `C8`-based error term directly.
1. `B_{4,α,r}` is `(2Φ(1) + c₅,r)/D`, not `(Φ(1)/π + c₅,r)/D` — a factor of `2π`; see `B4`.
2. The error term here is `(6h+6α̂_r)/((T-h-α̂_r)·D)`, cruder than the printed
   `O^*((4h+4)/T)`. Two separate reasons: `jensen_easy`'s own error is `3/t`, not `2/(πt)` (see
   there), which turns the `4a/π` into `6a`; and the `1/D` cannot be dropped — the two would agree
   only when `(T-h-α̂_r)·D ≥ T`, i.e. essentially `D ≥ 1`, which fails throughout Table
   `\ref{tab:rectangularjensen}` (Table 5) (`D = 0.675` at `α = 1/8`, `D ≈ 0.0097` at
   `α = 1/2048`). Since `B₄` and the error are both additive constants, no asymptotic conclusion
   changes.

Hypotheses beyond the source's: `0 < α` (needed for `rectDenom > 0`, `rectDenom_pos`), `r < 1`
and `10^{12} + 1 < T - h - α̂_r` (both needed by `jensen_easy`, applied at every `t = T+x` in the
window; `r < 1` rather than `r ≤ 1` because `c1_nonneg` needs `Kidx r` to be well defined).

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24), Table `\ref{tab:rectangularjensen}`
(Table 5).

### Dependencies
**Depends on:** `B1`, `B2`, `B3`, `B4`, `Nrect`, `Phi`, `c1`, `c1_nonneg`, `c2`, `c2_nonneg`, `c3`,
`c5`, `circle_full_split`, `hatAlpha`, `integral_window_bound`, `intervalIntegrable_arcAvg`,
`intervalIntegrable_logzeta_line`, `jensen_easy`, `jensenrectangle`, `littlewood_outerlog`,
`outside3`, `rectDenom`, `rectDenom_pos`.
**Used by:** none. -/
theorem rectangularjensen {T h α r : ℝ} (hα0 : 0 < α) (_hα : α ≤ 1) (hrα : α < r) (hr1 : r < 1)
    (hh : 0 < h) (hT : (10:ℝ)^(12:ℕ) + 1 < T - h - hatAlpha r α) :
    (Nrect (T - h) (T + h) α : ℝ)
      ≤ (2 * h + 2 * hatAlpha r α) *
            (B1 α r / Real.pi * Real.log |T| + B2 α r * Real.log (Real.log |T|) + B3 α r)
          + B4 α r
          + (6 * h + 6 * hatAlpha r α)
              / ((T - h - hatAlpha r α) * rectDenom r α) := by
  have hpi := Real.pi_pos
  have hr0 : 0 < r := hα0.trans hrα
  set A : ℝ := hatAlpha r α with hA_def
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set a : ℝ := h + A with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hbig : (1:ℝ) < 10 ^ (10:ℕ) := by norm_num
  have hTa : (1:ℝ) < T - a := by rw [ha_def]; linarith
  have hTa10 : (10:ℝ)^(10:ℕ) < T - a := by rw [ha_def]; linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hD : 0 < rectDenom r α := rectDenom_pos hα0 hrα
  have hneg : -h - A = -a := by rw [ha_def]; ring
  have haA : h + A = a := ha_def.symm
  have hc1 : 0 ≤ c1 r := c1_nonneg hr0 hr1
  have hc2 : 0 ≤ c2 r := c2_nonneg hr0
  have hjr := jensenrectangle (T := T) (h := h) (r := r) (α := α) hα0 hrα hh (by
    rw [← hA_def]; linarith)
  -- integrability of the three pieces
  have harc : ∀ x ∈ Set.uIcc (-a) a, r + 1 ≤ |T + x| := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [abs_of_pos (by linarith [hx.1] : (0:ℝ) < T + x)]
    linarith [hx.1]
  have hOi : IntervalIntegrable (fun x : ℝ =>
        (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) MeasureTheory.volume (-a) a :=
    (intervalIntegrable_arcAvg hr0 (by linarith) (by linarith) le_rfl harc).const_mul _
  have hIi : IntervalIntegrable (fun x : ℝ =>
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) MeasureTheory.volume (-a) a :=
    (intervalIntegrable_arcAvg hr0 le_rfl (by linarith) (by linarith) harc).const_mul _
  have hLi : IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
      MeasureTheory.volume (-a) a :=
    intervalIntegrable_logzeta_line T _ _
  -- split the numerator
  have hEq : (∫ x in (-a)..a, ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
        - Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖))
      = (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        + (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        - (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖) := by
    rw [← intervalIntegral.integral_add hOi hIi,
      ← intervalIntegral.integral_sub (hOi.add hIi) hLi]
    refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
    rw [circle_full_split]
  -- **P1: the outside-strip half**, via `jensen_easy` and the concavity window bound.
  have hgcont : ContinuousOn (fun x : ℝ =>
        c1 r / Real.pi * Real.log (T + x) + c2 r / Real.pi * Real.log (Real.log (T + x))
        + c3 r / Real.pi + 3 / (T + x)) (Set.uIcc (-a) a) := by
    rw [Set.uIcc_of_le (by linarith)]
    have hposx : ∀ x ∈ Set.Icc (-a) a, (1:ℝ) < T + x := by
      intro x hx; linarith [hx.1]
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_
    · exact continuousOn_const.mul
        (ContinuousOn.log (by fun_prop) (fun x hx => ne_of_gt (by linarith [hposx x hx])))
    · exact continuousOn_const.mul (ContinuousOn.log
        (ContinuousOn.log (by fun_prop) (fun x hx => ne_of_gt (by linarith [hposx x hx])))
        (fun x hx => ne_of_gt (Real.log_pos (hposx x hx))))
    · exact continuousOn_const
    · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)
      have := hposx x hx
      positivity
  have hP1 : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
      ≤ 2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
        + 6*a/(T-a) := by
    have hmono : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        ≤ ∫ x in (-a)..a, c1 r / Real.pi * Real.log (T + x)
            + c2 r / Real.pi * Real.log (Real.log (T + x))
        + c3 r / Real.pi + 3 / (T + x) := by
      refine intervalIntegral.integral_mono_on (by linarith) hOi hgcont.intervalIntegrable ?_
      intro x hx
      have hje := jensen_easy (r := r) (t := T + x) hr0 hr1 (by linarith [hx.1])
      have hcast : ((T + x : ℝ) : ℂ) = (T:ℂ) + (x:ℂ) := by push_cast; ring
      rw [hcast] at hje
      exact hje
    have hcv : (∫ x in (-a)..a, c1 r / Real.pi * Real.log (T + x)
          + c2 r / Real.pi * Real.log (Real.log (T + x))
        + c3 r / Real.pi + 3 / (T + x))
        = ∫ t in (T-a)..(T+a), c1 r / Real.pi * Real.log (t)
            + c2 r / Real.pi * Real.log (Real.log (t))
        + c3 r / Real.pi + 3 / (t) := by
      have hc := intervalIntegral.integral_comp_add_left (a := -a) (b := a)
        (fun t : ℝ => c1 r / Real.pi * Real.log (t) + c2 r / Real.pi * Real.log (Real.log (t))
        + c3 r / Real.pi + 3 / (t)) T
      have hTneg : T + -a = T - a := by ring
      rw [hTneg] at hc
      simpa using hc
    rw [hcv] at hmono
    have hw := integral_window_bound (T := T) (a := a) (A := c1 r/Real.pi) (B := c2 r/Real.pi)
      (C := c3 r/Real.pi) (by positivity) (by positivity) ha0 hTa
    linarith [hmono, hw]
  -- **P2: the inside-strip half**, via `outside3`.
  have hP2 : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) ≤ c5 r := by
    have hos := outside3 (T := T) (h := h) (r := r) (α := α) hr0 hh.le
      (by rw [← hA_def]; linarith)
    rw [← hA_def, hneg, haA] at hos
    exact le_trans (le_abs_self _) hos
  -- **P3: the `-log|ζ(1+it)|` term**, via `littlewood_outerlog`.
  have hP3 :
      -(∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
        ≤ 2 * (Phi 1).re := by
    have hcv : (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
        = ∫ t in (T-a)..(T+a), Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖ := by
      have hc := intervalIntegral.integral_comp_add_left (a := -a) (b := a)
        (fun t : ℝ => Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖) T
      have hTneg : T + -a = T - a := by ring
      rw [hTneg] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
      push_cast
      ring_nf
    have hlw := littlewood_outerlog (σ := 1) (T := T) (h := a) ha0.le (by linarith) le_rfl
    have hcast : ∀ t : ℝ, Real.log ‖riemannZeta (((1:ℝ):ℂ) + (t:ℂ) * Complex.I)‖
        = Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖ := by
      intro t; norm_num
    simp only [hcast] at hlw
    have hphi : Phi ((1:ℝ):ℂ) = Phi (1:ℂ) := by norm_num
    rw [hphi] at hlw
    rw [hcv]
    have h2 := mul_le_mul_of_nonneg_left hlw (show (0:ℝ) ≤ 2*Real.pi by linarith)
    have e1 : ∀ X : ℝ, 2*Real.pi * -(1 / (2 * Real.pi) * X) = -X := by
      intro X; field_simp
    have e2 : 2*Real.pi * ((Phi 1).re / Real.pi) = 2 * (Phi 1).re := by
      field_simp
    rw [e1, e2] at h2
    exact h2
  -- assemble
  rw [← hA_def, hneg, haA, hEq] at hjr
  have hnum : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        + (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        - (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
      ≤ 2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
        + 6*a/(T-a) + c5 r + 2*(Phi 1).re := by
    linarith [hP1, hP2, hP3]
  have hTsub : T - h - A = T - a := by rw [ha_def]; ring
  have h2hA : 2*h + 2*A = 2*a := by rw [ha_def]; ring
  have h4hA : 6*h + 6*A = 6*a := by rw [ha_def]; ring
  rw [h2hA, h4hA, hTsub, hTabs]
  clear_value a A
  have hTane : T - a ≠ 0 := by intro hc; linarith
  have hfin : (2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
      + 6*a/(T-a) + c5 r + 2*(Phi 1).re) / rectDenom r α
      = 2*a * (B1 α r / Real.pi * Real.log T + B2 α r * Real.log (Real.log T) + B3 α r)
        + B4 α r + 6*a/((T-a)*rectDenom r α) := by
    rw [B1, B2, B3, B4]
    field_simp
    ring
  refine le_trans hjr ?_
  rw [← hfin]
  gcongr

/-- **Theorem `\ref{thm:rectangularjensen}` (Theorem 24), tight version.** Carries forward the
tightened
`O(1/t²)` error of `JensenBounds.jensen_easy_tight` (in place of `rectangularjensen` above's
`jensen_easy`), via `integral_window_bound_tight` (in place of `integral_window_bound`), with the
matching threshold `13 < T - h - α̂_r`.**

### Summary of Proof
The proof is otherwise identical to `rectangularjensen`'s:
same three-step split (`circle_full_split` at `θ = ±π/2`, `outside3` for the inside strip,
`littlewood_outerlog` for the `-log|ζ(1+it)|` term), only the outside-strip piece P1 changes.

Hypothesis `0 < h` is inherited from `jensenrectangle` and is *not* implied by
`13 < T - h - α̂_r` alone — `h` could be very negative while keeping `T` large. The likely true
minimal hypothesis, following this file's own `outside2`/`outside2_le` precedent (`0 < h → 0 ≤ h`,
since `h` is a half-width and `Nrect` is vacuously `0` for `h ≤ 0`), would be `0 ≤ h`; weakening
to that would additionally need `0 ≤ c3 r`, `0 ≤ c5 r`, `0 ≤ (Phi 1).re` (none established in
this codebase) for the `h = 0` edge case, and is not done here since `jensenrectangle` requires
`0 < h` regardless.

### References
tex: Theorem `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `B1`, `B2`, `B3`, `B4`, `Nrect`, `Phi`, `c1`, `c1_nonneg`, `c2`, `c2_nonneg`, `c3`,
`c5`, `circle_full_split`, `hatAlpha`, `integral_window_bound_tight`, `intervalIntegrable_arcAvg`,
`intervalIntegrable_logzeta_line`, `jensen_easy_tight`, `jensenrectangle`, `littlewood_outerlog`,
`outside3`, `rectDenom`, `rectDenom_pos`.
**Used by:** `MainTheoremTight.mainJensenTight`, which is the `t > 10^12`, `0 < h ≤ t^{2/3}`
regime form that `MainTheorem.mainJensen` (Theorem 2) consumes. -/
theorem rectangularjensen_tight {T h α r : ℝ} (hα0 : 0 < α) (_hα : α ≤ 1) (hrα : α < r)
    (hr1 : r < 1) (hh : 0 < h) (hT : (13 : ℝ) < T - h - hatAlpha r α) :
    (Nrect (T - h) (T + h) α : ℝ)
      ≤ (2 * h + 2 * hatAlpha r α) *
            (B1 α r / Real.pi * Real.log |T| + B2 α r * Real.log (Real.log |T|) + B3 α r)
          + B4 α r
          + (5 * (h + hatAlpha r α) / (3 * (T - h - hatAlpha r α - 1))
              + (2 * (h + hatAlpha r α) / (T - h - hatAlpha r α - 1) ^ 2
                  + 1158 * (h + hatAlpha r α)
                      / (8 * (T - h - hatAlpha r α - 1) ^ 2
                          * Real.log (T - h - hatAlpha r α - 1))))
              / rectDenom r α := by
  have hpi := Real.pi_pos
  have hr0 : 0 < r := hα0.trans hrα
  set A : ℝ := hatAlpha r α with hA_def
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set a : ℝ := h + A with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hTa : (13:ℝ) < T - a := by rw [ha_def]; linarith
  have hTa2 : (2:ℝ) < T - a := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hD : 0 < rectDenom r α := rectDenom_pos hα0 hrα
  have hneg : -h - A = -a := by rw [ha_def]; ring
  have haA : h + A = a := ha_def.symm
  have hc1 : 0 ≤ c1 r := c1_nonneg hr0 hr1
  have hc2 : 0 ≤ c2 r := c2_nonneg hr0
  have hjr := jensenrectangle (T := T) (h := h) (r := r) (α := α) hα0 hrα hh (by
    rw [← hA_def]; linarith)
  -- integrability of the three pieces (threshold-independent, verbatim from `rectangularjensen`)
  have harc : ∀ x ∈ Set.uIcc (-a) a, r + 1 ≤ |T + x| := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [abs_of_pos (by linarith [hx.1] : (0:ℝ) < T + x)]
    linarith [hx.1]
  have hOi : IntervalIntegrable (fun x : ℝ =>
        (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) MeasureTheory.volume (-a) a :=
    (intervalIntegrable_arcAvg hr0 (by linarith) (by linarith) le_rfl harc).const_mul _
  have hIi : IntervalIntegrable (fun x : ℝ =>
        (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) MeasureTheory.volume (-a) a :=
    (intervalIntegrable_arcAvg hr0 le_rfl (by linarith) (by linarith) harc).const_mul _
  have hLi : IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
      MeasureTheory.volume (-a) a :=
    intervalIntegrable_logzeta_line T _ _
  -- split the numerator
  have hEq : (∫ x in (-a)..a, ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
        - Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖))
      = (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        + (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        - (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖) := by
    rw [← intervalIntegral.integral_add hOi hIi,
      ← intervalIntegral.integral_sub (hOi.add hIi) hLi]
    refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
    rw [circle_full_split]
  -- **P1: the outside-strip half**, via `jensen_easy_tight` and the tight window bound.
  have hgcont : ContinuousOn (fun x : ℝ =>
        c1 r / Real.pi * Real.log (T + x) + c2 r / Real.pi * Real.log (Real.log (T + x))
        + c3 r / Real.pi
        + (5 / (6 * (T + x - 1))
            + (1 / (T + x - 1) ^ 2 + 1158 / (16 * (T + x - 1) ^ 2 * Real.log (T + x - 1)))))
      (Set.uIcc (-a) a) := by
    rw [Set.uIcc_of_le (by linarith)]
    have hposx : ∀ x ∈ Set.Icc (-a) a, (13:ℝ) < T + x := by
      intro x hx; linarith [hx.1]
    have hposx1 : ∀ x ∈ Set.Icc (-a) a, (1:ℝ) < T + x - 1 := by
      intro x hx; linarith [hposx x hx]
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_
    · exact continuousOn_const.mul
        (ContinuousOn.log (by fun_prop) (fun x hx => ne_of_gt (by linarith [hposx x hx])))
    · exact continuousOn_const.mul (ContinuousOn.log
        (ContinuousOn.log (by fun_prop) (fun x hx => ne_of_gt (by linarith [hposx x hx])))
        (fun x hx => ne_of_gt (Real.log_pos (by linarith [hposx x hx] : (1:ℝ) < T + x))))
    · exact continuousOn_const
    · refine ContinuousOn.add ?_ (ContinuousOn.add ?_ ?_)
      · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)
        have := hposx1 x hx
        exact ne_of_gt (by linarith : (0:ℝ) < 6 * (T + x - 1))
      · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)
        have := hposx1 x hx
        positivity
      · refine ContinuousOn.div continuousOn_const ?_ (fun x hx => ?_)
        · apply ContinuousOn.mul (by fun_prop)
          apply ContinuousOn.log (by fun_prop)
          intro x hx; exact ne_of_gt (by linarith [hposx1 x hx] : (0:ℝ) < T + x - 1)
        · have h1 := hposx1 x hx
          have h2 : (0:ℝ) < Real.log (T + x - 1) := Real.log_pos h1
          positivity
  have hP1 : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
      ≤ 2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
        + (5*a/(3*(T-a-1)) + (2*a/(T-a-1)^2 + 1158*a/(8*(T-a-1)^2*Real.log (T-a-1)))) := by
    have hmono : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        ≤ ∫ x in (-a)..a, c1 r / Real.pi * Real.log (T + x)
            + c2 r / Real.pi * Real.log (Real.log (T + x)) + c3 r / Real.pi
        + (5 / (6 * (T + x - 1))
            + (1 / (T + x - 1) ^ 2 + 1158 / (16 * (T + x - 1) ^ 2 * Real.log (T + x - 1)))) := by
      refine intervalIntegral.integral_mono_on (by linarith) hOi hgcont.intervalIntegrable ?_
      intro x hx
      have hje := jensen_easy_tight (r := r) (t := T + x) hr0 hr1
        (by linarith [hx.1] : (13:ℝ) < T + x)
      have hcast : ((T + x : ℝ) : ℂ) = (T:ℂ) + (x:ℂ) := by push_cast; ring
      rw [hcast] at hje
      exact hje
    have hcv : (∫ x in (-a)..a, c1 r / Real.pi * Real.log (T + x)
          + c2 r / Real.pi * Real.log (Real.log (T + x)) + c3 r / Real.pi
        + (5 / (6 * (T + x - 1))
            + (1 / (T + x - 1) ^ 2 + 1158 / (16 * (T + x - 1) ^ 2 * Real.log (T + x - 1)))))
        = ∫ t in (T-a)..(T+a), c1 r / Real.pi * Real.log (t)
            + c2 r / Real.pi * Real.log (Real.log (t)) + c3 r / Real.pi
        + (5 / (6 * (t - 1))
            + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1)))) := by
      have hc := intervalIntegral.integral_comp_add_left (a := -a) (b := a)
        (fun t : ℝ => c1 r / Real.pi * Real.log (t) + c2 r / Real.pi * Real.log (Real.log (t))
          + c3 r / Real.pi
        + (5 / (6 * (t - 1))
            + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1))))) T
      have hTneg : T + -a = T - a := by ring
      rw [hTneg] at hc
      simpa using hc
    rw [hcv] at hmono
    have hw := integral_window_bound_tight (T := T) (a := a) (A := c1 r/Real.pi)
      (B := c2 r/Real.pi) (C := c3 r/Real.pi) (by positivity) (by positivity) ha0 hTa2
    linarith [hmono, hw]
  -- **P2: the inside-strip half**, via `outside3` (verbatim from `rectangularjensen`).
  have hP2 : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) ≤ c5 r := by
    have hos := outside3 (T := T) (h := h) (r := r) (α := α) hr0 hh.le
      (by rw [← hA_def]; linarith)
    rw [← hA_def, hneg, haA] at hos
    exact le_trans (le_abs_self _) hos
  -- **P3: the `-log|ζ(1+it)|` term**, via `littlewood_outerlog` (verbatim).
  have hP3 :
      -(∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
        ≤ 2 * (Phi 1).re := by
    have hcv : (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
        = ∫ t in (T-a)..(T+a), Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖ := by
      have hc := intervalIntegral.integral_comp_add_left (a := -a) (b := a)
        (fun t : ℝ => Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖) T
      have hTneg : T + -a = T - a := by ring
      rw [hTneg] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
      push_cast
      ring_nf
    have hlw := littlewood_outerlog (σ := 1) (T := T) (h := a) ha0.le (by linarith) le_rfl
    have hcast : ∀ t : ℝ, Real.log ‖riemannZeta (((1:ℝ):ℂ) + (t:ℂ) * Complex.I)‖
        = Real.log ‖riemannZeta ((1:ℂ) + (t:ℂ) * Complex.I)‖ := by
      intro t; norm_num
    simp only [hcast] at hlw
    have hphi : Phi ((1:ℝ):ℂ) = Phi (1:ℂ) := by norm_num
    rw [hphi] at hlw
    rw [hcv]
    have h2 := mul_le_mul_of_nonneg_left hlw (show (0:ℝ) ≤ 2*Real.pi by linarith)
    have e1 : ∀ X : ℝ, 2*Real.pi * -(1 / (2 * Real.pi) * X) = -X := by
      intro X; field_simp
    have e2 : 2*Real.pi * ((Phi 1).re / Real.pi) = 2 * (Phi 1).re := by
      field_simp
    rw [e1, e2] at h2
    exact h2
  -- assemble
  rw [← hA_def, hneg, haA, hEq] at hjr
  have hnum : (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        + (∫ x in (-a)..a, (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I
            + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖))
        - (∫ x in (-a)..a, Real.log ‖riemannZeta ((1:ℂ) + ((T : ℂ) + (x : ℂ)) * Complex.I)‖)
      ≤ 2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
        + (5*a/(3*(T-a-1)) + (2*a/(T-a-1)^2 + 1158*a/(8*(T-a-1)^2*Real.log (T-a-1))))
        + c5 r + 2*(Phi 1).re := by
    linarith [hP1, hP2, hP3]
  have hTsub : T - h - A = T - a := by rw [ha_def]; ring
  have h2hA : 2*h + 2*A = 2*a := by rw [ha_def]; ring
  rw [h2hA, hTsub, hTabs]
  clear_value a A
  have hTane : (T - a - 1 : ℝ) ≠ 0 := by intro hc; linarith
  have hlogne : Real.log (T - a - 1) ≠ 0 := ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < T-a-1))
  have hDne : rectDenom r α ≠ 0 := ne_of_gt hD
  have hfin : (2*a*(c1 r/Real.pi*Real.log T + c2 r/Real.pi*Real.log (Real.log T) + c3 r/Real.pi)
      + (5*a/(3*(T-a-1)) + (2*a/(T-a-1)^2 + 1158*a/(8*(T-a-1)^2*Real.log (T-a-1))))
      + c5 r + 2*(Phi 1).re) / rectDenom r α
      = 2*a * (B1 α r / Real.pi * Real.log T + B2 α r * Real.log (Real.log T) + B3 α r)
        + B4 α r
        + (5*a/(3*(T-a-1)) + (2*a/(T-a-1)^2 + 1158*a/(8*(T-a-1)^2*Real.log (T-a-1))))
            / rectDenom r α := by
    rw [B1, B2, B3, B4]
    field_simp
    ring
  refine le_trans hjr ?_
  rw [← hfin]
  gcongr
