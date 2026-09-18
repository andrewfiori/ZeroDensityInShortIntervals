/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib

/-! # Small reusable numeric `Real.log` bounds

Three small numeric facts (`2 < log x` for `8 < x`, `1 < log x` for `3 ≤ x`, and `4 ≤ log x` for
`55 ≤ x`), each needed at several call sites that would otherwise re-derive `Real.exp 2 < 8`,
`Real.exp 1 < 3` or `Real.exp 4 < 55` from `Real.exp_one_lt_d9` inline. They are collected here so
that the derivation happens once; each theorem's `Used by` lists its call sites.

Also here: the elementary analysis behind Bellotti–Wong's lower bound `L(h,t)` on
`N(t+h) − N(t−h)` — the power series of `φ(x) = (1+x)log(1+x) − (1−x)log(1−x)`
(`hasSum_two_mul_sub_bwPhi`), the sharp inequality `2x − φ(x) ≤ 2(1−log 2)x³` on `[0,1)`
(`two_mul_sub_bwPhi_le`), the resulting bound on `M(t+h) − M(t−h)` for the Riemann–von Mangoldt
main term `M` (`bwM_sub_ge`), and the assembly `bw_Lbound_of_cor` that
`ExternalFacts.bellotti_wong_Lbound_le` applies to the cited Corollary 1.3.

Two integral facts about `log(1 − v²)` sit here too: the crude estimate
`integral_neg_log_one_sub_sq_le` and the exact antiderivative
`hasDerivAt_log_one_sub_sq_antideriv` / `integral_log_one_sub_sq`. They belong to the same
`L(h,t)` circle of ideas but are not on the route the assembly above takes, which needs no
integral at all; see their own docstrings. -/

/-- **Lower bound `2 < log x` for `x > 8`.**

### Summary of Proof
Bound `exp 2` away from `8`, then apply strict monotonicity of `log`. Writing
`exp 2 = exp 1 * exp 1` and feeding Mathlib's decimal bound `Real.exp_one_lt_d9`
(`exp 1 < 2.7182818286`) to `nlinarith` gives `exp 2 < 8 < x`; then
`Real.log_lt_log` and `Real.log_exp` turn that into `2 = log (exp 2) < log x`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `arcErr_tight_crude_lt_three`, `jensen_easy`, `jensen_easy_tight`,
`littlewoodshort`, `littlewoodshort_tight`. -/
theorem two_lt_log_of_gt_eight {x : ℝ} (hx : 8 < x) : 2 < Real.log x := by
  have he : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlt := Real.log_lt_log (Real.exp_pos 2) (show Real.exp 2 < x by linarith)
  rwa [Real.log_exp] at hlt

/-- **Lower bound `1 < log x` for `x ≥ 3`.**

### Summary of Proof
`Real.exp_one_lt_d9` gives `exp 1 < 2.7182818286 < 3 ≤ x`, so strict monotonicity of `log`
yields `1 = log (exp 1) < log x`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem one_lt_log_of_ge_three {x : ℝ} (hx : 3 ≤ x) : 1 < Real.log x := by
  have he : Real.exp 1 < x := by have := Real.exp_one_lt_d9; linarith
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log x := Real.log_lt_log (Real.exp_pos 1) he

/-- **Lower bound `4 ≤ log x` for `x ≥ 55`.**

### Summary of Proof
Same shape as the two above, one power higher. Write `exp 4 = (exp 1)^4`, bound the base by
`Real.exp_one_lt_d9` and raise to the fourth with `gcongr`, giving
`exp 4 < 2.7182818286^4 < 55 ≤ x`. Then `Real.le_log_iff_exp_le` converts the goal `4 ≤ log x`
into `exp 4 ≤ x`, which follows.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
theorem four_le_log_of_ge_fiftyfive {x : ℝ} (hx : 55 ≤ x) : 4 ≤ Real.log x := by
  have hx0 : (0:ℝ) < x := by linarith
  have hexp4 : Real.exp 4 < 55 := by
    have h := Real.exp_one_lt_d9
    have he : Real.exp 4 = (Real.exp 1) ^ (4:ℕ) := by rw [Real.exp_one_pow]; norm_num
    rw [he]
    calc (Real.exp 1) ^ (4:ℕ) < (2.7182818286:ℝ) ^ (4:ℕ) := by gcongr
      _ < 55 := by norm_num
  rw [Real.le_log_iff_exp_le hx0]
  linarith

/-- **`∫_0^λ -log(1-v²) dv ≤ πλ³/2` for `0 ≤ λ ≤ 1/1000`.**

### Summary of Proof
Pointwise, `log x ≤ x-1` at `x = 1/(1-v²)` gives `-log(1-v²) ≤ v²/(1-v²)`, and on `[0,λ]` the
denominator is at least `1-λ²`, so the integrand is bounded by `v²/(1-λ²)`. Integrating,
`∫_0^λ ≤ λ³/(3(1-λ²))`, and the target follows from `2 ≤ 3π(1-λ²)`, i.e. `λ² ≤ 1 - 2/(3π)`.

### Lean Notes
**An integral route from Bellotti–Wong's Cor. 1.3 to the `L(h,t)` bound.** With
`M(T) = (T/2π)log(T/2πe)` and `λ = h/t`,

    M(t+h) - M(t-h) = (h/π)log(t/2π) + (1/2π)∫_0^h log(1 - u²/t²) du,

so a simplified main term `(h/π)log(t/2π) - C h³/t²` is a valid lower bound exactly when the
corresponding integral inequality holds (after `u = tv`). Bellotti–Wong itself supplies only the
additive tail `-0.194 log t - 9.908`; this is the separate step from the exact `M`-difference to
`L(h,t)`. `ExternalFacts.bellotti_wong_Lbound_le` takes that step by the power-series route
instead (`two_mul_sub_bwPhi_le`, `bwM_sub_ge`, `bw_Lbound_of_cor` below), which needs no integral
and yields the sharp constant, so nothing calls this lemma.

**The `λ ≤ 1/1000` restriction is what makes it cheap.** The statement is true for all `λ < 1` —
the true worst ratio is `(2-2log 2)/(π/2) = 0.391`, attained only as `λ → 1` — but proving that
needs the antiderivative of `log(1-v²)`, which is available here as
`hasDerivAt_log_one_sub_sq_antideriv` / `integral_log_one_sub_sq` below. The crude bound above is
valid up to `λ ≤ √(1-2/(3π)) = 0.8876`, and in the application
`λ = h/t ≤ t^{-1/3} ≤ 10⁻⁴` (from `h < t^{2/3}`, `t > 10¹²`), leaving a factor of `4.7` of room.
Tabulated in `Code/verify_log_integral_small_lambda.py`; `Code/verify_Lht_sharp_constant.py`
checks the whole reduction, with the sharp `h²`-coefficient `(1-log 2)/π` that the tex and Lean
carry. The two steps are independent: Bellotti–Wong supplies only the additive tail
`-0.194 log t - 9.908`, and this integral inequality is what licenses replacing the exact
`M`-difference by the tex's simpler main term.

### References
tex: the `L(h,t)` display preceding `\ref{cor:main-jensen}` (Corollary 4), tex line 203.

### Dependencies
**Depends on:** none.
**Used by:** none — `ExternalFacts.bellotti_wong_Lbound_le` reaches the same conclusion, with the
sharp constant, through `bw_Lbound_of_cor`. -/
theorem integral_neg_log_one_sub_sq_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 1000) :
    (∫ v in (0:ℝ)..lam, -Real.log (1 - v ^ 2)) ≤ Real.pi * lam ^ 3 / 2 := by
  have hlam1 : lam < 1 := by linarith
  have hden : (0:ℝ) < 1 - lam ^ 2 := by nlinarith
  have hpt : ∀ v ∈ Set.Icc (0:ℝ) lam, -Real.log (1 - v ^ 2) ≤ v ^ 2 / (1 - lam ^ 2) := by
    intro v hv
    obtain ⟨hv0, hvl⟩ := hv
    have hv1 : (0:ℝ) < 1 - v ^ 2 := by nlinarith
    -- `log x ≤ x - 1` at `x = 1/(1-v²)`
    have hlog := Real.log_le_sub_one_of_pos (x := 1 / (1 - v ^ 2)) (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hv1), Real.log_one] at hlog
    have heq : 1 / (1 - v ^ 2) - 1 = v ^ 2 / (1 - v ^ 2) := by
      field_simp [hv1.ne']
      ring
    rw [heq] at hlog
    have hmono : v ^ 2 / (1 - v ^ 2) ≤ v ^ 2 / (1 - lam ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hden (by nlinarith)
    linarith
  have hcont : ContinuousOn (fun v : ℝ => -Real.log (1 - v ^ 2)) (Set.uIcc 0 lam) := by
    apply ContinuousOn.neg
    apply ContinuousOn.log (by fun_prop)
    intro v hv
    rw [Set.uIcc_of_le h0] at hv
    have : (0:ℝ) < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    linarith
  have hint1 : IntervalIntegrable (fun v : ℝ => -Real.log (1 - v ^ 2))
      MeasureTheory.volume 0 lam := hcont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun v : ℝ => v ^ 2 / (1 - lam ^ 2))
      MeasureTheory.volume 0 lam := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on h0 hint1 hint2 hpt
  have hval : (∫ v in (0:ℝ)..lam, v ^ 2 / (1 - lam ^ 2)) = lam ^ 3 / (3 * (1 - lam ^ 2)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    field_simp
    ring
  rw [hval] at hle
  refine hle.trans ?_
  have hlamsq : lam ^ 2 ≤ 1 / 1000000 := by nlinarith
  have hcube : (0:ℝ) ≤ lam ^ 3 := pow_nonneg h0 3
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
  -- `π·3·(1-λ²) ≥ 9(1-10⁻⁶) ≥ 2`, then multiply through by `λ³ ≥ 0`
  have hfac : (2:ℝ) ≤ Real.pi * (3 * (1 - lam ^ 2)) := by
    nlinarith [Real.pi_gt_three,
      mul_nonneg (by linarith [Real.pi_gt_three] : (0:ℝ) ≤ Real.pi - 3)
        (by linarith : (0:ℝ) ≤ 1 - lam ^ 2)]
  calc lam ^ 3 * 2 ≤ lam ^ 3 * (Real.pi * (3 * (1 - lam ^ 2))) :=
        mul_le_mul_of_nonneg_left hfac hcube
    _ = Real.pi * lam ^ 3 * (3 * (1 - lam ^ 2)) := by ring

/-- **The closed-form antiderivative of `log (1 - x²)` on `(-1, 1)`.**

`∫ log(1-x²) dx = log((1+x)/(1-x)) + x·log(1-x²) - 2x`, stated here as a difference of logs
rather than via `artanh`, since `2 artanh x = log((1+x)/(1-x))` and Mathlib's `artanh` is not
needed for anything else here.

### Summary of Proof
Differentiate. The three pieces contribute `2/(1-x²)`, `log(1-x²) - 2x²/(1-x²)` and `-2`, and
`2/(1-x²) - 2x²/(1-x²) = 2` cancels the `-2` exactly, leaving `log(1-x²)`.

### Lean Notes
**Do not assemble this with `convert`.** `HasDerivAt.add`/`.sub` build the *pointwise* function
`((f - g) + h) - k` rather than a lambda, and `convert` then tries to unify
`Semiring.toModule` with `RCLike.toInnerProductSpaceReal.toModule` and leaves unsolvable instance
goals. Stating `key` with its expected type up front makes the two forms unify definitionally.
Likewise `simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)` rewrites `fun y => 1 + y`
into `(fun _ => 1) + id` and hits the same mismatch — use `HasDerivAt.const_add`/`.const_sub`.

### References
Supplied by the author, 2026-09-05. No tex counterpart; it supports the `L(h,t)` derivation
discussed under `integral_neg_log_one_sub_sq_le` above.

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_one_sub_sq`. -/
theorem hasDerivAt_log_one_sub_sq_antideriv {x : ℝ} (hx : |x| < 1) :
    HasDerivAt
      (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) + y * Real.log (1 - y ^ 2) - 2 * y)
      (Real.log (1 - x ^ 2)) x := by
  rw [abs_lt] at hx
  obtain ⟨h1, h2⟩ := hx
  have hp : (0 : ℝ) < 1 + x := by linarith
  have hm : (0 : ℝ) < 1 - x := by linarith
  have hsq : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hne1 : (1 + x) ≠ 0 := ne_of_gt hp
  have hne2 : (1 - x) ≠ 0 := ne_of_gt hm
  have hne3 : (1 - x ^ 2) ≠ 0 := ne_of_gt hsq
  have e1 : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) x := (hasDerivAt_id x).const_add 1
  have e2 : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id x).const_sub 1
  have e3a : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x ^ 1)) x :=
    (hasDerivAt_pow 2 x).const_sub 1
  rw [pow_one] at e3a
  have d1 := e1.log hne1
  have d2 := e2.log hne2
  have d3 := e3a.log hne3
  have d4 : HasDerivAt (fun y : ℝ => y * Real.log (1 - y ^ 2))
      (1 * Real.log (1 - x ^ 2) + x * (-(2 * x) / (1 - x ^ 2))) x :=
    (hasDerivAt_id x).mul d3
  have d5a : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1 : ℝ) x := (hasDerivAt_id x).const_mul 2
  rw [mul_one] at d5a
  have key : HasDerivAt
      (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) + y * Real.log (1 - y ^ 2) - 2 * y)
      (1 / (1 + x) - -1 / (1 - x) + (1 * Real.log (1 - x ^ 2) + x * (-(2 * x) / (1 - x ^ 2))) - 2)
      x := ((d1.sub d2).add d4).sub d5a
  have hval : 1 / (1 + x) - -1 / (1 - x)
      + (1 * Real.log (1 - x ^ 2) + x * (-(2 * x) / (1 - x ^ 2))) - 2
      = Real.log (1 - x ^ 2) := by
    field_simp
    ring
  rwa [hval] at key

/-- **The exact value of `∫₀^a log(1-x²) dx` for `0 ≤ a < 1`.**

`∫₀^a log(1-x²) dx = log(1+a) - log(1-a) + a·log(1-a²) - 2a`.

### Summary of Proof
Fundamental theorem of calculus against `hasDerivAt_log_one_sub_sq_antideriv`, whose value at `0`
is `0`. Integrability is the continuity of `log(1-x²)` on `[0,a]`, where `1-x² ≥ 1-a² > 0`.

### Lean Notes
**The sharp companion to `integral_neg_log_one_sub_sq_le` above.** That lemma's `λ ≤ 1/1000`
hypothesis and its factor-of-`4.7` slack are both consequences of its crude `log x ≤ x-1` route;
with this identity the `L(h,t)` main term is an equality rather than a majorant, and holds for
every `0 ≤ a < 1` rather than only small `a`.

### References
Supplied by the author, 2026-09-05.

### Dependencies
**Depends on:** `hasDerivAt_log_one_sub_sq_antideriv`.
**Used by:** none — the Bellotti–Wong step it addresses is done by the power-series route
(`two_mul_sub_bwPhi_le`, below), which needs no integral. -/
theorem integral_log_one_sub_sq {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    (∫ x in (0 : ℝ)..a, Real.log (1 - x ^ 2))
      = Real.log (1 + a) - Real.log (1 - a) + a * Real.log (1 - a ^ 2) - 2 * a := by
  have h : ∀ x ∈ Set.uIcc (0 : ℝ) a, HasDerivAt
      (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) + y * Real.log (1 - y ^ 2) - 2 * y)
      (Real.log (1 - x ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    exact hasDerivAt_log_one_sub_sq_antideriv
      (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h]
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    nlinarith [hx.1, hx.2]

/-! ## The elementary inequality behind Bellotti–Wong's `L(h,t)`

`M(T) = (T/2π) log(T/(2πe))` is the main term of the Riemann–von Mangoldt formula. With
`λ = h/t`, `M(t+h) − M(t−h) = (h/π)(log t − log 2π) − h/π + (t/2π) φ(λ)` where
`φ(λ) = (1+λ)log(1+λ) − (1−λ)log(1−λ)`, and the tex's lower bound
`M(t+h) − M(t−h) ≥ (log(t/2π)/π)h − (1−log 2)h³/(πt²)` is equivalent to
`2λ − φ(λ) ≤ 2(1−log 2)λ³`. That inequality is sharp at both ends of `(0,1)`, so a derivative
argument is delicate; instead `2λ − φ(λ) = Σ_{k≥1} λ^{2k+1}/(k(2k+1))` (from the power series of
`log(1±λ)`) is compared termwise with `λ³ Σ 1/(k(2k+1))`, and the constant is bounded by the
`λ → 1⁻` limit of the same identity. -/

/-- `φ(x) = (1+x) log(1+x) − (1−x) log(1−x)`.

### Summary of Proof
A definition.

### References
The tex's `L(h,t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex line 203, whose
derivation from Bellotti–Wong reduces to an inequality for this function.

### Dependencies
**Depends on:** none.
**Used by:** `hasSum_two_mul_sub_bwPhi`, `bw_const_partial_le`, `two_mul_sub_bwPhi_le`,
`bwM_sub_ge`. -/
noncomputable def bwPhi (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - (1 - x) * Real.log (1 - x)

/-- **The power series `2x − φ(x) = Σ_{k≥0} x^{2k+3}/((k+1)(2k+3))` for `|x| < 1`.**

### Summary of Proof
`log(1+x) − log(1−x) = Σ 2x^{2k+1}/(2k+1)` (`Real.hasSum_log_sub_log_of_abs_lt_one`; the `k = 0`
term is `2x`, removed with `hasSum_nat_add_iff'`) and
`log(1+x) + log(1−x) = log(1−x²) = −Σ (x²)^{k+1}/(k+1)` (`Real.hasSum_pow_div_log_of_abs_lt_one` at
`x²`). Since `φ(x) = (log(1+x) − log(1−x)) + x(log(1+x) + log(1−x))`, subtracting the two series
gives the termwise coefficient `1/(k+1) − 2/(2k+3) = 1/((k+1)(2k+3))` at `x^{2k+3}`.

### References
No tex counterpart (the tex asserts the resulting inequality "by inspection").

### Dependencies
**Depends on:** `bwPhi`.
**Used by:** `bw_const_partial_le`, `two_mul_sub_bwPhi_le`. -/
theorem hasSum_two_mul_sub_bwPhi {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3))) (2 * x - bwPhi x) := by
  have hx1 : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hx2 : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hC := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have hC' := (hasSum_nat_add_iff' 1).mpr hC
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, div_one, pow_one,
    mul_one] at hC'
  have hx2' : |x ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) hx (by norm_num)
  have hD := Real.hasSum_pow_div_log_of_abs_lt_one hx2'
  have hlog : Real.log (1 - x ^ 2) = Real.log (1 + x) + Real.log (1 - x) := by
    rw [← Real.log_mul hx1.ne' hx2.ne']
    congr 1
    ring
  rw [hlog] at hD
  have hD' : HasSum (fun k : ℕ => x ^ (2 * k + 3) / ((k : ℝ) + 1))
      (-(x * (Real.log (1 + x) + Real.log (1 - x)))) := by
    have := hD.mul_left x
    have hfun : (fun k : ℕ => x ^ (2 * k + 3) / ((k : ℝ) + 1))
        = fun i : ℕ => x * ((x ^ 2) ^ (i + 1) / ((i : ℝ) + 1)) := by
      funext k
      rw [← pow_mul]
      ring
    have hval : -(x * (Real.log (1 + x) + Real.log (1 - x)))
        = x * -(Real.log (1 + x) + Real.log (1 - x)) := by ring
    rw [hfun, hval]
    exact this
  have := hD'.sub hC'
  have hfun2 : (fun k : ℕ => x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3)))
      = fun k : ℕ => x ^ (2 * k + 3) / ((k : ℝ) + 1)
          - 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ) + 1)) * x ^ (2 * (k + 1) + 1) := by
    funext k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : (2 * ((k : ℝ) + 1) + 1) ≠ 0 := by positivity
    have hk3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hval2 : 2 * x - bwPhi x
      = -(x * (Real.log (1 + x) + Real.log (1 - x)))
        - (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
    unfold bwPhi
    ring
  rw [hfun2, hval2]
  exact this

/-- **Partial sums of `Σ 1/((k+1)(2k+3))` are at most `2(1 − log 2)`.**

### Summary of Proof
For `0 ≤ x < 1` the partial sum of `Σ x^{2k+3}/((k+1)(2k+3))` is at most the full sum
`2x − φ(x)` (`hasSum_two_mul_sub_bwPhi`, `sum_le_hasSum`). Let `x → 1⁻`: the partial sum tends to
the partial sum of the constant series (a polynomial in `x`), and `2x − φ(x) → 2 − 2 log 2` since
`(1+x)log(1+x) → 2 log 2` and `(1−x)log(1−x) → 0` (`Real.continuous_mul_log` at `0`);
`le_of_tendsto_of_tendsto` along `𝓝[<] 1`.

### Lean Notes
The full sum `Σ_{k≥1} 1/(k(2k+1))` equals `2(1 − log 2)` (the alternating harmonic series), but
only `≤` is needed and the limit argument avoids evaluating `log 2` as a series.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bwPhi`, `hasSum_two_mul_sub_bwPhi`.
**Used by:** `bw_const_summable`, `bw_const_tsum_le`. -/
theorem bw_const_partial_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3)) ≤ 2 * (1 - Real.log 2) := by
  have hpart : ∀ x : ℝ, 0 ≤ x → x < 1 →
      ∑ k ∈ Finset.range K, x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3)) ≤ 2 * x - bwPhi x := by
    intro x hx0 hx1
    have hs := hasSum_two_mul_sub_bwPhi (by rw [abs_of_nonneg hx0]; exact hx1)
    exact sum_le_hasSum (Finset.range K) (fun k _ => by positivity) hs
  have h1 : Filter.Tendsto
      (fun x : ℝ => ∑ k ∈ Finset.range K, x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (∑ k ∈ Finset.range K, (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3)))) := by
    have hc : Continuous
        (fun x : ℝ => ∑ k ∈ Finset.range K, x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3))) := by
      fun_prop
    have := hc.tendsto 1
    simp only [one_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun x : ℝ => 2 * x - bwPhi x) (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (2 * (1 - Real.log 2))) := by
    have hA : Filter.Tendsto (fun x : ℝ => (1 + x) * Real.log (1 + x)) (nhds 1)
        (nhds (2 * Real.log 2)) := by
      have hca : ContinuousAt (fun x : ℝ => (1 + x) * Real.log (1 + x)) 1 := by
        apply ContinuousAt.mul (by fun_prop)
        exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
      have h := hca.tendsto
      norm_num at h
      exact h
    have hB : Filter.Tendsto (fun x : ℝ => (1 - x) * Real.log (1 - x)) (nhds 1) (nhds 0) := by
      have hc : Continuous (fun y : ℝ => y * Real.log y) := Real.continuous_mul_log
      have hsub : Filter.Tendsto (fun x : ℝ => 1 - x) (nhds (1 : ℝ)) (nhds ((1 : ℝ) - 1)) :=
        tendsto_const_nhds.sub Filter.tendsto_id
      have := (hc.tendsto 0).comp (by simpa using hsub)
      simp only [zero_mul] at this
      exact this
    have h2x : Filter.Tendsto (fun x : ℝ => 2 * x) (nhds (1 : ℝ)) (nhds (2 * 1)) :=
      tendsto_const_nhds.mul Filter.tendsto_id
    have := (h2x.sub (hA.sub hB)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    unfold bwPhi
    rw [show (2 : ℝ) * (1 - Real.log 2) = 2 * 1 - (2 * Real.log 2 - 0) by ring]
    exact this
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  exact hpart x hx.1.le hx.2

/-- **`Σ 1/((k+1)(2k+3))` is summable** (bounded partial sums of a nonnegative series).

### Summary of Proof
`summable_of_sum_range_le` with `bw_const_partial_le`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bw_const_partial_le`.
**Used by:** `two_mul_sub_bwPhi_le`. -/
theorem bw_const_summable : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3))) :=
  summable_of_sum_range_le (fun k => by positivity) bw_const_partial_le

/-- **`Σ_{k≥0} 1/((k+1)(2k+3)) ≤ 2(1 − log 2)`.**

### Summary of Proof
`Real.tsum_le_of_sum_range_le` with `bw_const_partial_le`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bw_const_partial_le`.
**Used by:** `two_mul_sub_bwPhi_le`. -/
theorem bw_const_tsum_le :
    ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3)) ≤ 2 * (1 - Real.log 2) :=
  Real.tsum_le_of_sum_range_le (fun k => by positivity) bw_const_partial_le

/-- **The key inequality `2x − φ(x) ≤ 2(1 − log 2) x³` on `[0, 1)`.** Sharp at both ends
(equality in the limits `x → 0` to third order and `x → 1⁻`).

### Summary of Proof
Termwise: `x^{2k+3} ≤ x³` for `0 ≤ x < 1`, so the series `hasSum_two_mul_sub_bwPhi` is bounded by
`x³ Σ 1/((k+1)(2k+3))` (`hasSum_le`), and the constant is at most `2(1 − log 2)`
(`bw_const_tsum_le`).

### References
The tex's `L(h,t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex line 203: this is the
inequality that makes its `(1−log 2)h²/(πt²)` term valid (the sharp constant, see
`ExternalFacts.bellotti_wong_Lbound_le`).

### Dependencies
**Depends on:** `bwPhi`, `hasSum_two_mul_sub_bwPhi`, `bw_const_summable`, `bw_const_tsum_le`.
**Used by:** `bwM_sub_ge`. -/
theorem two_mul_sub_bwPhi_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * x - bwPhi x ≤ 2 * (1 - Real.log 2) * x ^ 3 := by
  have hs := hasSum_two_mul_sub_bwPhi (by rw [abs_of_nonneg hx0]; exact hx1)
  have hs2 : HasSum (fun k : ℕ => x ^ 3 * (1 / (((k : ℝ) + 1) * (2 * k + 3))))
      (x ^ 3 * ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3))) :=
    bw_const_summable.hasSum.mul_left (x ^ 3)
  have hterm : ∀ k : ℕ, x ^ (2 * k + 3) / (((k : ℝ) + 1) * (2 * k + 3))
      ≤ x ^ 3 * (1 / (((k : ℝ) + 1) * (2 * k + 3))) := by
    intro k
    have hpow : x ^ (2 * k + 3) ≤ x ^ 3 := pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have hden : (0 : ℝ) < ((k : ℝ) + 1) * (2 * k + 3) := by positivity
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hpow hden.le
  have hle := hasSum_le hterm hs hs2
  calc 2 * x - bwPhi x ≤ x ^ 3 * ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + 1) * (2 * k + 3)) := hle
    _ ≤ x ^ 3 * (2 * (1 - Real.log 2)) :=
        mul_le_mul_of_nonneg_left bw_const_tsum_le (by positivity)
    _ = 2 * (1 - Real.log 2) * x ^ 3 := by ring

/-- **`M(T) := (T/2π) log(T/(2πe))`**, the main term of the Riemann–von Mangoldt formula.

### Summary of Proof
A definition.

### References
The `N(t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex line 201;
Bellotti–Wong, `\cite[Cor. 1.3]{BellottiWong2026}`.

### Dependencies
**Depends on:** none.
**Used by:** `bwM_sub_ge`, `bw_Lbound_of_cor`, `Hypotheses.LiteratureInputs.bellotti_wong_cor_1_3`
and the theorem `ExternalFacts.bellotti_wong_cor_1_3` that reads it,
`ExternalFacts.bellotti_wong_Lbound_le`. -/
noncomputable def bwM (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

/-- **`M(t+h) − M(t−h) ≥ (log(t/2π)/π − (1−log 2)h²/(πt²))·h` for `0 < h < t`.**

### Summary of Proof
With `λ = h/t`, `t ± h = t(1 ± λ)` and `log(T/(2πe)) = log T − log 2π − 1`, the difference is
`(h/π)(log t − log 2π) − h/π + (t/2π) φ(λ)`, and the target minus this is
`(t/2π)(2(1−log 2)λ³ − (2λ − φ(λ))) ≥ 0` by `two_mul_sub_bwPhi_le` (`field_simp; ring` for the
identity, after substituting `h = tλ`).

### References
The tex's `L(h,t)` display above `\ref{cor:main-jensen}` (Corollary 4), tex line 203.

### Dependencies
**Depends on:** `bwM`, `bwPhi`, `two_mul_sub_bwPhi_le`.
**Used by:** `bw_Lbound_of_cor`. -/
theorem bwM_sub_ge {h t : ℝ} (hh : 0 < h) (hht : h < t) :
    (Real.log (t / (2 * Real.pi)) / Real.pi - (1 - Real.log 2) * h ^ 2 / (Real.pi * t ^ 2)) * h
      ≤ bwM (t + h) - bwM (t - h) := by
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_pos
  set l := h / t with hl
  have hl0 : 0 < l := div_pos hh ht0
  have hl1 : l < 1 := (div_lt_one ht0).mpr hht
  have hl0' : (0 : ℝ) < 1 + l := by linarith
  have hl1' : (0 : ℝ) < 1 - l := by linarith
  have hkey := two_mul_sub_bwPhi_le hl0.le hl1
  have hh' : h = t * l := by rw [hl]; field_simp
  have e1 : Real.log ((t + h) / (2 * Real.pi * Real.exp 1))
      = Real.log t + Real.log (1 + l) - Real.log (2 * Real.pi) - 1 := by
    have ht1 : t + h = t * (1 + l) := by rw [hl]; field_simp
    rw [ht1, Real.log_div (mul_pos ht0 hl0').ne' (by positivity), Real.log_mul ht0.ne' hl0'.ne',
      Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have e2 : Real.log ((t - h) / (2 * Real.pi * Real.exp 1))
      = Real.log t + Real.log (1 - l) - Real.log (2 * Real.pi) - 1 := by
    have ht1 : t - h = t * (1 - l) := by rw [hl]; field_simp
    rw [ht1, Real.log_div (mul_pos ht0 hl1').ne' (by positivity), Real.log_mul ht0.ne' hl1'.ne',
      Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have e3 : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div ht0.ne' (by positivity)
  have hdiff : (bwM (t + h) - bwM (t - h))
      - (Real.log (t / (2 * Real.pi)) / Real.pi
          - (1 - Real.log 2) * h ^ 2 / (Real.pi * t ^ 2)) * h
      = (t / (2 * Real.pi)) * (2 * (1 - Real.log 2) * l ^ 3 - (2 * l - bwPhi l)) := by
    unfold bwM bwPhi
    rw [e1, e2, e3, hh']
    field_simp
    ring
  have hnonneg : 0 ≤ (t / (2 * Real.pi)) * (2 * (1 - Real.log 2) * l ^ 3 - (2 * l - bwPhi l)) :=
    mul_nonneg (by positivity) (by linarith [hkey])
  linarith [hdiff, hnonneg]

/-- **From `|Nf(T) − M(T)| ≤ 0.097 log T + 4.954` (`T ≥ 1`) to the lower bound `L(h,t)`:**
`(log(t/2π)/π − (1−log 2)h²/(πt²))h − 0.194 log t − 9.908 ≤ Nf(t+h) − Nf(t−h)` for `0 < h`,
`1 ≤ t − h`. Stated for an arbitrary counting function `Nf`, to be applied to the project's `N`
with Bellotti–Wong's Corollary 1.3.

### Summary of Proof
The hypothesis at `T = t+h` and `T = t−h` gives
`Nf(t+h) − Nf(t−h) ≥ M(t+h) − M(t−h) − 0.097(log(t+h) + log(t−h)) − 9.908`;
`log(t+h) + log(t−h) = log(t²−h²) ≤ 2 log t`; and `bwM_sub_ge` bounds `M(t+h) − M(t−h)`.

### References
Bellotti–Wong, `\cite[Cor. 1.3]{BellottiWong2026}`; the tex's `L(h,t)` display above
`\ref{cor:main-jensen}` (Corollary 4), tex line 203.

### Dependencies
**Depends on:** `bwM`, `bwM_sub_ge`.
**Used by:** `ExternalFacts.bellotti_wong_Lbound_le`. -/
theorem bw_Lbound_of_cor {Nf : ℝ → ℝ}
    (hBW : ∀ T : ℝ, 1 ≤ T → |Nf T - bwM T| ≤ 0.097 * Real.log T + 4.954)
    {h t : ℝ} (hh : 0 < h) (ht : 1 ≤ t - h) :
    (Real.log (t / (2 * Real.pi)) / Real.pi - (1 - Real.log 2) * h ^ 2 / (Real.pi * t ^ 2)) * h
        - (0.194 : ℝ) * Real.log t - 9.908 ≤ Nf (t + h) - Nf (t - h) := by
  have hht : h < t := by linarith
  have ht0 : 0 < t := by linarith
  have h1 := abs_le.mp (hBW (t + h) (by linarith))
  have h2 := abs_le.mp (hBW (t - h) ht)
  have hlogsum : Real.log (t + h) + Real.log (t - h) ≤ 2 * Real.log t := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    have hle : (t + h) * (t - h) ≤ t * t := by nlinarith
    calc Real.log ((t + h) * (t - h)) ≤ Real.log (t * t) :=
          Real.log_le_log (by nlinarith) hle
      _ = 2 * Real.log t := by rw [Real.log_mul ht0.ne' ht0.ne']; ring
  have hM := bwM_sub_ge hh hht
  linarith [h1.1, h1.2, h2.1, h2.2, hlogsum, hM]
