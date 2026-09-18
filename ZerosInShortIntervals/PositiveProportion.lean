/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import ZerosInShortIntervals.HalvingConvention

/-! # Corollary `\ref{cor:simpmain}` (Corollary 1) in the tex's own existential form

The tex states Corollary 1 as "**for `h₀` and `t₀` sufficiently large**, and for all `t > t₀` and
`t^{2/3} > h > h₀` ... `> C_{α,h₀,t₀}`", and calls `C` a *positive* constant.  Everything in
`HalvingConvention` proves the inequality for `h₀` and `t₀` that the caller supplies and says
nothing about the sign of `C`, so on its own it is compatible with `C < 0` and asserts nothing.
This file supplies the two missing halves: the existence of admissible `h₀`, `t₀`, and the
positivity of the constant there.

**No interval arithmetic is involved**, which is the point.  `C₂ᴸ` is a quotient whose every term
except the leading `2A₁` carries a factor `1/h`, `1/log t` or `log log t / log t`, and whose
denominator tends to `1`.  So

  `C₂ᴸ(α, r, h, t, k) → 2·A₁(α, r, k)` as `h, t → ∞`,

and nothing has to be *bounded* for that: `A₂`–`A₆` are built from `c₁`–`c₄`, `Φ` and `log‖ζ‖`,
whose values this development never pins down, but they are real numbers, and a real number over
`h` tends to `0`.  What is left is the single inequality `4A₁ < 1`, and `A₁` is a ratio of
explicit rationals once `α`, `r` and `k` are fixed, so `norm_num` decides it.

The limit is taken in two steps rather than jointly, which is what makes it short.  The affine
identity `C₂ᴸ = (P(t)·h + Q(t))/(S(t)·h - W(t))` of `MainCorollary.C2Littlewood_eq_affine` gives
`C₂ᴸ → P(t)/S(t)` as `h → ∞` at fixed `t`; then `P(t)/S(t) → 2A₁` as `t → ∞`.  Two single-variable
limits suffice because only *one* admissible pair `(h₀, t₀)` is needed.

**And the side condition can be discharged once and for all.**  Take `r = 1/2`.  The chord index
`k = 0` has `σ₀ = 1/2` exactly, so `1-r` lands on a chord endpoint, the interpolation collapses,
and the numerator of `A₁` is `v₀ = 1/6` whatever the slope.  Then

  `4·A₁(α, 1/2, 0) = (1/3)/(1/2 - α) < 1  ⟺  α < 1/6`,

which is the paper's own hypothesis on `α`.  So `positiveProportion_littlewood_half` and
`positiveProportion_of_lt_sixth` assume nothing beyond `0 < α < 1/6`: the witness `r = 1/2` is
supplied, not assumed.  The parametrised `positiveProportion_littlewood` is kept because other `r`
give **larger** constants (at `α = 1/16`, `r = 1/5` gives a limiting `9/25 ≈ 0.36` against
`r = 1/2`'s `5/21 ≈ 0.238`), and `positiveProportion_littlewood_sixteenth` is that instance.

`r = 1/2` is also sharp at the endpoint: at `α = 1/6` it gives limiting constant exactly `0`, and
no other `r` does better there, so the paper's strict `α < 1/6` is not an artefact of the method.
-/

open Filter Topology

/-! ### Three limits, none of which depends on a hypothesis class -/

/-- **`log (log t) / log t → 0`.**

### Summary of Proof
`Real.log =o[atTop] id` gives `log u / u → 0`; compose with `log t → ∞`.

### Lean Notes
Stated for `Real.log (Real.log t)` rather than for a general composite because that is the only
shape the constants use.

### References
No tex counterpart; the tex treats the `log log t / log t` terms as visibly negligible.

### Dependencies
**Depends on:** `Real.isLittleO_log_id_atTop`, `Real.tendsto_log_atTop`.
**Used by:** `tendsto_C2LittlewoodP`. -/
theorem tendsto_loglog_div_log :
    Tendsto (fun t : ℝ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp Real.tendsto_log_atTop

/-- **`1 / log t → 0`.**

### Summary of Proof
`log t → ∞`, so its inverse tends to `0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Real.tendsto_log_atTop`, `Filter.Tendsto.inv_tendsto_atTop`.
**Used by:** `tendsto_C2LittlewoodP`, `tendsto_C2denomS`. -/
theorem tendsto_one_div_log :
    Tendsto (fun t : ℝ => 1 / Real.log t) atTop (𝓝 0) := by
  simp only [one_div]
  exact Real.tendsto_log_atTop.inv_tendsto_atTop

/-- **`1 / (t^{2/3} · log t) → 0`.**

### Summary of Proof
`t^{2/3} → ∞` and `log t → ∞`, so the product does, so its inverse tends to `0`.

### References
No tex counterpart; this is the shape of `C2denomS`'s second correction.

### Dependencies
**Depends on:** `tendsto_rpow_atTop`, `Real.tendsto_log_atTop`,
`Filter.Tendsto.atTop_mul_atTop₀`.
**Used by:** `tendsto_C2denomS`. -/
theorem tendsto_one_div_rpow_mul_log :
    Tendsto (fun t : ℝ => 1 / (t ^ ((2 : ℝ) / 3) * Real.log t)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t ^ ((2 : ℝ) / 3) * Real.log t) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ (tendsto_rpow_atTop (by norm_num)) Real.tendsto_log_atTop
  simp only [one_div]
  exact h.inv_tendsto_atTop

/-! ### The `t → ∞` limit of the constant -/

/-- **`P(t) → 2A₁` as `t → ∞`**, where `P` is the `h`-coefficient of `C₂ᴸ`'s cleared numerator.

### Summary of Proof
`P(t) = 2A₁ + (2πA₂)·(log log t / log t) + (2πA₃)·(1/log t)`; both correction factors tend to `0`
and `A₂`, `A₃` do not depend on `t`.

### Lean Notes
The `ring`-normalised rewrite is needed because the definition writes `2πA₂ · log log t / log t`,
which parses as `(2πA₂ · log log t) / log t`, not as a product with the quotient.

**Nothing about the size of `A₂` or `A₃` is used**, only that they are constants in `t`.  That is
what keeps this file free of the numeric certificates.

### References
tex: the `t → ∞` behaviour of `C_2^L` that `Corollary \ref{cor:simpmain}` (Corollary 1) appeals to
when it says "for `h₀` and `t₀` sufficiently large".

### Dependencies
**Depends on:** `MainCorollary.C2LittlewoodP`, `tendsto_loglog_div_log`, `tendsto_one_div_log`.
**Used by:** `tendsto_C2LittlewoodP_div_C2denomS`. -/
theorem tendsto_C2LittlewoodP (α r : ℝ) (k : ℤ) :
    Tendsto (fun t : ℝ => C2LittlewoodP α r t k) atTop (𝓝 (2 * A1 α r k)) := by
  have key : ∀ t : ℝ, C2LittlewoodP α r t k
      = 2 * A1 α r k + 2 * Real.pi * A2 α r k * (Real.log (Real.log t) / Real.log t)
        + 2 * Real.pi * A3 α r k * (1 / Real.log t) := by
    intro t; unfold C2LittlewoodP; ring
  simp only [key]
  have h := ((tendsto_const_nhds (x := 2 * A1 α r k) (f := (atTop : Filter ℝ))).add
    ((tendsto_const_nhds (x := 2 * Real.pi * A2 α r k)).mul tendsto_loglog_div_log)).add
      ((tendsto_const_nhds (x := 2 * Real.pi * A3 α r k)).mul tendsto_one_div_log)
  have hval : 2 * A1 α r k + 2 * Real.pi * A2 α r k * 0 + 2 * Real.pi * A3 α r k * 0
      = 2 * A1 α r k := by ring
  rw [hval] at h
  exact h

/-- **`S(t) → 1` as `t → ∞`**, where `S` is the `h`-coefficient of `C2denom`'s cleared form.

### Summary of Proof
`S(t) = 1 - log(2π)·(1/log t) - (1-log 2)·(1/(t^{2/3} log t))`, and both corrections tend to `0`.

### References
tex: the denominator of `C_2` is the Riemann–von Mangoldt count, which is asymptotically the whole
main term.

### Dependencies
**Depends on:** `MainCorollary.C2denomS`, `tendsto_one_div_log`, `tendsto_one_div_rpow_mul_log`.
**Used by:** `tendsto_C2LittlewoodP_div_C2denomS`. -/
theorem tendsto_C2denomS : Tendsto C2denomS atTop (𝓝 1) := by
  have key : ∀ t : ℝ, C2denomS t
      = 1 - Real.log (2 * Real.pi) * (1 / Real.log t)
        - (1 - Real.log 2) * (1 / (t ^ ((2 : ℝ) / 3) * Real.log t)) := by
    intro t; unfold C2denomS; ring
  rw [funext key]
  have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub
    ((tendsto_const_nhds (x := Real.log (2 * Real.pi))).mul tendsto_one_div_log)).sub
      ((tendsto_const_nhds (x := 1 - Real.log 2)).mul tendsto_one_div_rpow_mul_log)
  have hval : (1 : ℝ) - Real.log (2 * Real.pi) * 0 - (1 - Real.log 2) * 0 = 1 := by ring
  rw [hval] at h
  exact h

/-- **`P(t)/S(t) → 2A₁` as `t → ∞`.**

### Summary of Proof
Quotient of the two limits above; the denominator's limit `1` is nonzero.

### References
tex: this is the number `Corollary \ref{cor:simpmain}` (Corollary 1) calls `C_2^L` in the limit of
large `h₀`, `t₀`.

### Dependencies
**Depends on:** `tendsto_C2LittlewoodP`, `tendsto_C2denomS`.
**Used by:** `exists_C2Littlewood_lt_half`. -/
theorem tendsto_C2LittlewoodP_div_C2denomS (α r : ℝ) (k : ℤ) :
    Tendsto (fun t : ℝ => C2LittlewoodP α r t k / C2denomS t) atTop (𝓝 (2 * A1 α r k)) := by
  have h := (tendsto_C2LittlewoodP α r k).div tendsto_C2denomS one_ne_zero
  rw [div_one] at h
  exact h

section

/- From here on the statements use `MainCorollary`'s algebra (`C2Littlewood_eq_affine`,
`C2denomS_pos`), which carries the development's hypothesis binders, so the section variables are
opened here rather than at the top of the file: the three analytic limits above stay
unconditional. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-! ### The `h → ∞` limit at fixed `t`, and an admissible pair -/

/-- **At fixed `t`, `C₂ᴸ(·, t) → P(t)/S(t)` as `h → ∞`.**

### Summary of Proof
`C2Littlewood_eq_affine` writes `C₂ᴸ = (P·h + Q)/(S·h - W)`.  Dividing numerator and denominator
by `h` gives `(P + Q/h)/(S - W/h)`, which tends to `P/S` because `1/h → 0` and `S ≠ 0`.

### Lean Notes
The rewrite is only used once `h` is large enough that `S·h - W ≠ 0`, which is why the identity is
established `∀ᶠ h in atTop` rather than pointwise: `eventually_gt_atTop (W/S)` supplies it, using
`0 < S`.

### References
tex: the `h₀ → ∞` half of "for `h₀` and `t₀` sufficiently large".

### Dependencies
**Depends on:** `MainCorollary.C2Littlewood_eq_affine`, `tendsto_inv_atTop_zero`.
**Used by:** `exists_C2Littlewood_lt_half`. -/
theorem tendsto_C2Littlewood_h {α r t : ℝ} {k : ℤ}
    (hlog : Real.log t ≠ 0) (ht : t ≠ 0) (hrα : r - α ≠ 0) (hS : 0 < C2denomS t) :
    Tendsto (fun h : ℝ => C2Littlewood α r h t k) atTop
      (𝓝 (C2LittlewoodP α r t k / C2denomS t)) := by
  have key : ∀ᶠ h : ℝ in atTop, C2Littlewood α r h t k
      = (C2LittlewoodP α r t k + C2LittlewoodQ α r t * (1 / h))
        / (C2denomS t - C2denomW t * (1 / h)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (C2denomW t / C2denomS t)] with h hh hh2
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hlt := (div_lt_iff₀ hS).mp hh2
    have hdpos : 0 < C2denomS t * h - C2denomW t := by nlinarith
    have hd : C2denomS t * h - C2denomW t ≠ 0 := ne_of_gt hdpos
    have hP : C2LittlewoodP α r t k + C2LittlewoodQ α r t * (1 / h)
        = (C2LittlewoodP α r t k * h + C2LittlewoodQ α r t) / h := by
      field_simp
    have hSh : C2denomS t - C2denomW t * (1 / h)
        = (C2denomS t * h - C2denomW t) / h := by
      field_simp
    have cancel : ((C2LittlewoodP α r t k * h + C2LittlewoodQ α r t) / h)
        / ((C2denomS t * h - C2denomW t) / h)
        = (C2LittlewoodP α r t k * h + C2LittlewoodQ α r t)
          / (C2denomS t * h - C2denomW t) := by
      field_simp
    rw [C2Littlewood_eq_affine hh0 hlog ht hrα, hP, hSh, cancel]
  rw [tendsto_congr' key]
  have hinv : Tendsto (fun h : ℝ => 1 / h) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero
  have hnum : Tendsto (fun h : ℝ => C2LittlewoodP α r t k + C2LittlewoodQ α r t * (1 / h))
      atTop (𝓝 (C2LittlewoodP α r t k)) := by
    have h := (tendsto_const_nhds (x := C2LittlewoodP α r t k) (f := (atTop : Filter ℝ))).add
      ((tendsto_const_nhds (x := C2LittlewoodQ α r t)).mul hinv)
    have hval : C2LittlewoodP α r t k + C2LittlewoodQ α r t * 0
        = C2LittlewoodP α r t k := by ring
    rw [hval] at h
    exact h
  have hden : Tendsto (fun h : ℝ => C2denomS t - C2denomW t * (1 / h))
      atTop (𝓝 (C2denomS t)) := by
    have h := (tendsto_const_nhds (x := C2denomS t) (f := (atTop : Filter ℝ))).sub
      ((tendsto_const_nhds (x := C2denomW t)).mul hinv)
    have hval : C2denomS t - C2denomW t * 0 = C2denomS t := by ring
    rw [hval] at h
    exact h
  exact hnum.div hden (ne_of_gt hS)

/-- **If `4A₁ < 1` then some admissible `(h₀, t₀)` has `C₂ᴸ < 1/2`.**

### Summary of Proof
Two steps.  `P(t)/S(t) → 2A₁ < 1/2`, so some `t₀ > 10^12` has `P(t₀)/S(t₀) < 1/2`.  At that `t₀`,
`C₂ᴸ(h, t₀) → P(t₀)/S(t₀) < 1/2` as `h → ∞`, so some `h₀ > h0Threshold t₀` has
`C₂ᴸ(h₀, t₀) < 1/2`.

### Lean Notes
`10^12 < t₀` is folded into the first eventuality and `h0Threshold t₀ < h₀` into the second; both
are eventually true along `atTop`, so neither costs more than an `eventually_gt_atTop`.

The hypothesis reads `4 * A1 α r k < 1` rather than `A1 α r k < 1/4` because that is the form
`norm_num` meets at an instantiation, `A₁` being a quotient.

### References
tex: "for `h₀` and `t₀` sufficiently large" in `Corollary \ref{cor:simpmain}` (Corollary 1), and
Table `\ref{tab:C2Lfrontier}` (Table 11), which exhibits such pairs numerically.

### Dependencies
**Depends on:** `tendsto_C2LittlewoodP_div_C2denomS`, `tendsto_C2Littlewood_h`,
`MainCorollary.C2denomS_pos`.
**Used by:** `positiveProportion_littlewood`. -/
theorem exists_C2Littlewood_lt_half {α r : ℝ} {k : ℤ} (hrα : α < r)
    (hA1 : 4 * A1 α r k < 1) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      C2Littlewood α r h0 t0 k < 1 / 2 := by
  have hlim : (2 : ℝ) * A1 α r k < 1 / 2 := by linarith
  obtain ⟨t0, ht0big, ht0⟩ :
      ∃ t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ C2LittlewoodP α r t0 k / C2denomS t0 < 1 / 2 :=
    ((eventually_gt_atTop ((10 : ℝ) ^ (12 : ℕ))).and
      (Filter.Tendsto.eventually_lt_const hlim
        (tendsto_C2LittlewoodP_div_C2denomS α r k))).exists
  have ht1 : (1 : ℝ) < t0 := by nlinarith [ht0big]
  have hlog : Real.log t0 ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have htne : t0 ≠ 0 := by positivity
  have hSpos : 0 < C2denomS t0 := C2denomS_pos ht0big
  obtain ⟨h0, hh0, hC⟩ :
      ∃ h0 : ℝ, h0Threshold t0 < h0 ∧ C2Littlewood α r h0 t0 k < 1 / 2 :=
    ((eventually_gt_atTop (h0Threshold t0)).and
      (Filter.Tendsto.eventually_lt_const ht0
        (tendsto_C2Littlewood_h hlog htne (sub_ne_zero_of_ne (ne_of_gt hrα)) hSpos))).exists
  exact ⟨h0, t0, ht0big, hh0, hC⟩

/-! ### Corollary 1 with its positivity claim -/

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), exactly as the tex states it.**

For `h₀` and `t₀` sufficiently large, and for all `t > t₀` and `t^{2/3} > h > h₀`, the proportion
of the zeros with imaginary part within `h` of `t` whose real part lies in `[α, 1-α]` exceeds a
**positive** constant.

### Summary of Proof
`exists_C2Littlewood_lt_half` produces an admissible pair with `C₂ᴸ < 1/2`, which is exactly
`0 < 1 - 2C₂ᴸ = C`; `simpleProportionCorollary_littlewood_prose` supplies the inequality at that
pair.

### Lean Notes
This is the first statement in the development that asserts the constant is positive.  Everything
in `HalvingConvention` proves `proportion > C` for a caller-supplied `(h₀, t₀)` and is silent
about the sign of `C`.

The hypothesis `4A₁ < 1` is not vacuous: see `positiveProportion_littlewood_sixteenth`.  Nor is it
free — at `α = 1/16` the limiting constant `1 - 4A₁` is about `0.36` at `r = 1/5` but essentially
`0` at `r = 9/10`, so the choice of `r` carries real weight.

### References
tex: `Corollary \ref{cor:simpmain}` (Corollary 1), including its "for `h₀` and `t₀` sufficiently
large" and its description of `C_{α,h₀,t₀}` as an explicitly computable **positive** constant.

### Dependencies
**Depends on:** `exists_C2Littlewood_lt_half`,
`HalvingConvention.simpleProportionCorollary_littlewood_prose`,
`HalvingConvention.CsimpLittlewood`.
**Used by:** the Palomar `Challenge`/`Solution` pair. -/
theorem positiveProportion_littlewood {α r : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (hA1 : 4 * A1 α r k < 1) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood α r h0 t0 k ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood α r h0 t0 k := by
  obtain ⟨h0, t0, ht0, hh0, hC⟩ := exists_C2Littlewood_lt_half hrα hA1
  refine ⟨h0, t0, ht0, hh0, ?_, ?_⟩
  · unfold CsimpLittlewood
    linarith
  · intro t h ht hh hht
    exact simpleProportionCorollary_littlewood_prose hα0 hrα hα hk hk' ht0 hh0 hh ht hht

/-- **The hypothesis `4A₁ < 1` is satisfiable:** `α = 1/16`, `r = 1/5`, `k = 1`.

### Summary of Proof
`σ₁ = 5/7 ≤ 4/5 < 5/6 = σ₂`, so `k = 1` is the admissible chord index for `r = 1/5`.  There
`v₁ = 1/14`, `v₂ = 1/30`, so `m₁ = -8/25` and `b₁ = 3/10`, the majorant at `1-r = 4/5` is
`11/250`, and `A₁ = (11/250)/(2(1/5 - 1/16)) = 4/25`.  Hence `4A₁ = 16/25 < 1`.

### Lean Notes
Everything here is exact rational arithmetic: `σ_k` and `v_k` are explicit rationals, so `norm_num`
decides the chord inequalities and the value of `A₁` after unfolding.  **No numeric certificate and
no interval arithmetic is used**, which is the whole point of routing positivity through the limit
rather than through an evaluation of `C₂ᴸ`.

The limiting constant at these parameters is `1 - 4A₁ = 9/25 = 0.36`.  That is the limit, not the
constant this theorem produces: the `(h₀, t₀)` it produces is whatever the limit argument reaches
first, and the constant there is merely positive.  The tables give `0.3484` at `α = 1/16`,
`h₀ = 100`, `t₀ = 10^10000`, consistent with approaching `0.36` from below.

### References
tex: the `α = 1/16` rows of Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `positiveProportion_littlewood`, `JensenScaleConstants.sigma`,
`JensenScaleConstants.vCoeff`, `Littlewood.LittlewoodShort.A1`.
**Used by:** `AllHypotheses.simpleProportionCorollary_littlewood_sixteenth'`, and through it
the Palomar `Solution.lean`.  It also shows the hypothesis is not vacuous. -/
theorem positiveProportion_littlewood_sixteenth :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood (1 / 16) (1 / 5) h0 t0 1 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) (1 / 16) / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood (1 / 16) (1 / 5) h0 t0 1 := by
  have h11 : (1 : ℤ) + 1 = 2 := by norm_num
  have hs1 : sigma 1 = 5 / 7 := by norm_num [sigma]
  have hs2 : sigma 2 = 5 / 6 := by norm_num [sigma]
  have hv1 : vCoeff 1 = 1 / 14 := by norm_num [vCoeff]
  have hv2 : vCoeff 2 = 1 / 30 := by norm_num [vCoeff]
  have hm : mCoeff 1 = -(8 / 25) := by
    rw [mCoeff, h11, hv1, hv2, hs1, hs2]; norm_num
  have hb : bCoeff 1 = 3 / 10 := by
    rw [bCoeff, hv1, hm, hs1]; norm_num
  refine positiveProportion_littlewood (by norm_num) (by norm_num) (by norm_num)
    (by rw [hs1]; norm_num) (by rw [h11, hs2]; norm_num) ?_
  rw [A1, hm, hb]
  norm_num

end

/-! ### `r = 1/2` works for every admissible `α`, so no hypothesis is needed at all

The chord index `k = 0` has `σ₀ = 1/2` exactly, so at `r = 1/2` the point `1-r` where the majorant
is evaluated **is** a chord endpoint and the interpolation collapses: whatever the slope `m₀`, the
numerator of `A₁` is `m₀(1-r) + b₀ = m₀·½ + (v₀ - m₀·σ₀) = v₀ = 1/6`.  So

  `4·A₁(α, 1/2, 0) = (1/3)/(1/2 - α)`,

which is `< 1` exactly when `α < 1/6`.  That is the paper's own hypothesis on `α`, so the choice
`r = 1/2` can simply be supplied and the side condition disappears.  It is also sharp: at
`α = 1/6` the expression equals `1`, the limiting constant is `0`, and no other `r` does better
there — which is presumably why `1/6` is the threshold in the first place.
-/

/-- **`4A₁(α, 1/2, 0) < 1` for every `α < 1/6`.**

### Summary of Proof
`σ₀ = 1/2`, so `b₀ = v₀ - m₀/2` and the numerator of `A₁` is `m₀(1 - 1/2) + b₀ = v₀ = 1/6`,
independently of the slope.  Then `4A₁ = (1/3)/(1/2 - α) < 1` iff `1/3 < 1/2 - α` iff `α < 1/6`.

### Lean Notes
The slope `m₀` never has to be computed.  That is the whole content of choosing `r = 1/2`: the
evaluation point lands on a chord endpoint, so the piecewise-linear majorant takes its tabulated
value there and the interpolation drops out.

Exact rational arithmetic throughout; no numeric certificate is involved.

### References
tex: the hypothesis `0 < α < 1/6` of `Corollary \ref{cor:simpmain}` (Corollary 1), and
`MainTerms.alphaBoundTodo`.

### Dependencies
**Depends on:** `Littlewood.LittlewoodShort.A1`, `JensenScaleConstants.bCoeff`,
`JensenScaleConstants.sigma`, `JensenScaleConstants.vCoeff`.
**Used by:** `positiveProportion_littlewood_half`. -/
theorem four_mul_A1_half_lt_one {α : ℝ} (hα : α < 1 / 6) : 4 * A1 α (1 / 2) 0 < 1 := by
  have hs0 : sigma 0 = 1 / 2 := by norm_num [sigma]
  have hv0 : vCoeff 0 = 1 / 6 := by norm_num [vCoeff]
  have hnum : mCoeff 0 * (1 - 1 / 2) + bCoeff 0 = 1 / 6 := by
    rw [bCoeff, hv0, hs0]; ring
  have hpos : (0 : ℝ) < 1 / 2 - α := by linarith
  have hrw : 4 * ((1 / 6 : ℝ) / (2 * (1 / 2 - α))) = (1 / 3) / (1 / 2 - α) := by
    field_simp
    ring
  rw [A1, hnum, hrw, div_lt_one hpos]
  linarith

section

/- As above: the two statements below reach the development's hypotheses through
`positiveProportion_littlewood`, so the section variables are reopened here.  The arithmetic
lemma above stays unconditional. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1) with no side condition**, for every `α` in the
paper's own range `0 < α < 1/6`.

For such an `α` there exist `h₀` and `t₀`, admissible in the sense that `t₀ > 10^12` and
`h0Threshold t₀ < h₀`, at which the constant `C = 1 - 2C₂ᴸ(α, 1/2, h₀, t₀, 0)` is **positive**,
and for every `t > t₀` and every `h` with `h₀ < h < t^{2/3}` the proportion of the window's zeros
with real part in `[α, 1-α]` exceeds `C`.

### Summary of Proof
`positiveProportion_littlewood` at `r = 1/2`, `k = 0`.  Its five side conditions are discharged by
`four_mul_A1_half_lt_one` and by `σ₀ = 1/2 ≤ 1/2 < 5/7 = σ₁`.

### Lean Notes
This supersedes the version with a `4A₁ < 1` hypothesis: the witness is supplied rather than
assumed, so the statement's hypotheses are exactly the paper's.  The parametrised
`positiveProportion_littlewood` is kept because other `r` give **larger** constants — at
`α = 1/16`, `r = 1/5` gives a limiting `9/25 = 0.36` against `r = 1/2`'s `1 - 16/21 = 5/21 ≈ 0.238`
— so `r = 1/2` is the choice that always works, not the best one.

Sharpness: at `α = 1/6` this construction gives limiting constant exactly `0`, and a survey of
other `r` at `α = 1/6` gives no positive value either, so the paper's strict `α < 1/6` is not an
artefact of the method.

### References
tex: `Corollary \ref{cor:simpmain}` (Corollary 1), whose hypothesis is exactly `0 < α < 1/6`.

### Dependencies
**Depends on:** `positiveProportion_littlewood`, `four_mul_A1_half_lt_one`.
**Used by:** `positiveProportion_of_lt_sixth`, and the Palomar `Challenge`/`Solution` pair. -/
theorem positiveProportion_littlewood_half {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood α (1 / 2) h0 t0 0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood α (1 / 2) h0 t0 0 :=
  positiveProportion_littlewood hα0 (by linarith) hα
    (by norm_num [sigma]) (by norm_num [sigma]) (four_mul_A1_half_lt_one hα)

/-- **The tex's sentence, formalised: "bounded below by an explicitly computable positive
constant".**

### Summary of Proof
`positiveProportion_littlewood_half`, with the constant existentially quantified.

### Lean Notes
The constant is existential here only in the statement; the witness is
`CsimpLittlewood α (1/2) h₀ t₀ 0`, which is explicit, and
`positiveProportion_littlewood_half` names it.  This form exists because it is what the tex's
prose literally says, and because it is the shape a reader wants to see: `∃ C > 0`.

### References
tex: `Corollary \ref{cor:simpmain}` (Corollary 1), first sentence.

### Dependencies
**Depends on:** `positiveProportion_littlewood_half`.
**Used by:** `AllHypotheses.positiveProportion_of_lt_sixth'`, and through it the Palomar
`Solution.lean`. -/
theorem positiveProportion_of_lt_sixth {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ C h0 t0 : ℝ, 0 < C ∧ (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > C := by
  obtain ⟨h0, t0, ht0, hh0, hCpos, hbound⟩ := positiveProportion_littlewood_half hα0 hα
  exact ⟨CsimpLittlewood α (1 / 2) h0 t0 0, h0, t0, hCpos, ht0, hh0, hbound⟩

end
