/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodShort
import ZerosInShortIntervals.Background.ExternalFacts
import ZerosInShortIntervals.MainTerms
import ZerosInShortIntervals.ConstantSigns
import ZerosInShortIntervals.MainTheoremTight

/-! # Theorems `\ref{thm:main-jensen}` (Theorem 2) and `\ref{thm:main-littlewood}` (Theorem 3)

This file states **and proves** the two headline, mechanism-specific theorems of the introduction
of `ZerosInShortIntervals.tex` — `thm:main-jensen` (Theorem 2, Jensen mechanism, tex
lines 157–166) and `thm:main-littlewood` (Theorem 3, Littlewood mechanism, tex lines 183–193) — in
the tex's own form: `0 < α < r` (`r < 1` for Jensen), `α < 1/6`, `t^{2/3} ≥ h ≥ 0`, and the
`log log t` thresholds `t ≥ e` resp. `t ≥ e^e`, with the collapsed `O^*` errors
`EJensen`/`ELittlewood`. The main and error terms themselves (`UJensen`, `ULittlewood`, `EJensen`,
`ELittlewood`, `alphaBoundTodo`) are defined in `ZerosInShortIntervals.MainTerms`, upstream of
`MainTheoremTight`, whose regime forms `mainJensenTight`/`mainLittlewoodTight` the proofs below
consume.

**Two cases.** Under `h ≤ t^{2/3}` the tex's shift case `t - h < H₀ < t + h` is vacuous:
`t ≤ 10^12` forces `t + h ≤ 10^12 + 10^8 < H₀ = 3·10^12`, and for `t > 10^12` Theorems 24/32 apply
directly (their own thresholds are `13 < t - h - α̂_r` resp. `13 < t - h`, far below `H₀`). So the
proofs here have exactly two cases:

* `t > 10^12` — `MainTheoremTight.mainJensenTight` / `mainLittlewoodTight` (for `h > 0`), plus the
  numerical collapse of their sharper brackets to `EJensen`/`ELittlewood`
  (`jensen_error_collapse`, `littlewood_error_collapse`); for `h = 0` the window is empty
  (`Nrect_self`);
* `t ≤ 10^12` — the window lies below Platt–Trudgian's height, so the count is *zero*
  (`Nrect_eq_zero_of_le_H0`, from the `LiteratureInputs` field
  `platt_trudgian_verified_below`), and the claim is the positivity of `U + O^*`
  (`UJensen_add_EJensen_pos`, `ULittlewood_add_ELittlewood_pos`, from the sign facts in
  `ZerosInShortIntervals.ConstantSigns`).

**The `h > t^{2/3}` regime is outside both theorems**, as it is in the tex, which carries it only
as a remark with a sketch (tex lines 176–180). That sketch does not close with the available
explicit zero-density input at the stated threshold; `Nrect_le_zero_density_bound` below records
the half of it that does go through, and what the other half would need.

**Why the thresholds `t ≥ e` and `t ≥ e^e`**, which are the tex's own (tex lines 158, 184): they
are not slack. `U_J` and `U_L` contain `log log t`, whose coefficients `(2h + 2α̂_r)B₂` resp.
`2A₂h + 2A₅` are strictly positive for the paper's constants, so as `t → 1⁺` the right-hand side
tends to `-∞` while the count is `0`; the inequality fails for `t` slightly above `1`. What the
proofs need is `log log t ≥ 0`, i.e. `t ≥ e`, for Theorem 2 (`ht : Real.exp 1 ≤ t`), and
`log log t ≥ 1`, i.e. `t ≥ e^e ≈ 15.2`, for Theorem 3 (`ht : Real.exp (Real.exp 1) ≤ t`) — the
extra notch because the sign of `A₃` is not available (it is genuinely negative for some chords),
only `-A₂ ≤ A₃` (`ConstantSigns.neg_A2_le_A3`), so the `h`-terms `2h(A₂ log log t + A₃)` are
controlled only once `log log t ≥ 1`. Both thresholds are irrelevant to every use (`t > 10^12`).

**`arg ζ` in `mainLittlewood`.** `argZeta` is the tex's constructed branch
(`LittlewoodMethod.argZetaDef`), so no polar-form hypothesis is needed. The tex fixes `arg ζ` in
two cases: when a horizontal edge `Im s = t ± h`, `Re s ∈ [1-r, 1+ηr]` carries no zero of `ζ`,
`arg ζ` is its *defined* continuous variation from `Re s > 1`
(`zeta_eq_norm_mul_exp_argZetaDef` is exactly the polar form); when the edge passes through a
zero, the tex uses the halving convention. This file assumes the first case, which is what the
zero-free-edge hypotheses `hzf_p`/`hzf_m` record; the half-counted form carrying no edge
hypothesis at all is `HalvingConvention.mainLittlewoodHalf`, obtained there by an `ε`-shift
rather than by the averaged `arg`. Theorem 2 needs nothing of the kind — the Jensen route never
sees `arg ζ`.

**`log t` versus `log |t|`.** The tex writes `\log(t)`, `\log\log(t)` in these two theorems, while
the underlying `thm:rectangularjensen`/`thm:littlewoodshort` write `\log|t|`; the two agree for
`t > 0`, which every hypothesis here guarantees. -/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **The zero-density input to the tex's `h ≫ t^{2/3}` remark after Theorem 2, in the
`(t-h, t+h)` geometry.** For `α ∈ [0,1/4]`, `0 ≤ h` and
`t - h ≥ 3×10¹²`,
`N(t-h,t+h,α) ≤ 12.45321·(t+h)^{(8/3)α}(log(t+h))^{3+2α} + 3.869(log(t+h))²`.

### Summary of Proof
An instance of `Background.ExternalFacts.farzanfard_zero_density_interval` at `T₁ = t-h`,
`T₂ = t+h`. The only content is that `t - h ≤ t + h` when `0 ≤ h`.

### Lean Notes
This is the half of the tex's sketch that goes through. **The other half does not.** The
tex (the remark after `\ref{thm:main-jensen}`, tex lines 176–180) continues

    N(t-h,t+h,α) << (t+h)^{(8/3)α}log(t+h)³ << U_J(α,r,h,10¹²) < U_J(α,r,h,t)

and remarks that "since `α < 1/6` and `h > 10⁸` the coefficient `log(h)³/h^{1-4α}` shrinks faster
as `α → 0` than `B_{1,α,r}` can". That mechanism is real — for small `α` the comparison is
comfortable — but **it is not uniform over `α < 1/6` at the stated threshold `t > 10¹²`.**
Substituting the explicit constants above and the paper's own optimised `B_{i,α,r}` from Table
`\ref{tab:rectangularjensen}` (Table 5) (`Code/verify_kln_large_h_case.py`), at the smallest
admissible `h = t^{2/3}`:

| `α` | with Cor 4.50 | with the **tightened** input |
|---|---|---|
| `1/7` | fails `20.8×`; holds from `t ≳ 10^18.8` | fails `5.9×`; holds from `t ≳ 10^17.3` |
| `1/8` | fails `4.7×`; holds from `t ≳ 10^15.2` | fails `2.1×`; holds from `t ≳ 10^14.0` |
| `1/9` | — | **holds at `t > 10¹²`** |
| `1/10` and below | holds at `t > 10¹²` | holds at `t > 10¹²` |

The **tightened** column applies both improvements available in the source (see
`ExternalFacts.farzanfard_zero_density_interval`'s docstring): per-`σ` constants from the
thesis's Table A.1 instead of Corollary 4.50's maxima over `σ ∈ [0.75,1]`, and its equation
(4.159) instead of the `log(1+y) ≤ y` weakening (4.160) that the corollary quotes. Worth a factor
of `3.5` at `α = 1/7`. It is a real gain and it **still does not close the branch**: coverage at
`t > 10¹²` moves only from `α ≤ 1/10` to `α ≤ 1/9`.

Two further avenues were checked and yield nothing. `h = t^{2/3}` really is the binding `h` once
the `t`-dependence is kept on both sides: at fixed `t` the ratio decreases in `h` (`Y` is flat in
`h` for `h < t` while the denominator grows like `2h`), and along `h = t^{2/3}` it decreases in
`t` because `(8/3)α < 2/3`. And `U_J`'s `(2h + 2α̂_r)` factor offers no slack — `α̂_r ≈ 0.55`
against `2h ≈ 4×10⁸`.

So closing Theorem 2 for all `α < 1/6` needs something beyond this source: a genuinely sharper
zero-density estimate, a raised `t`-threshold in case (i) with `α ∈ (1/9, 1/6)`, `t ∈ (10¹²,
10^17.3)` absorbed by another case, or a revision of the argument. Recorded rather than papered
over.

### References
tex: the `h ≫ t^{2/3}` remark after `\ref{thm:main-jensen}` (Theorem 2), tex lines 176–180;
`\ref{thm:main-littlewood}` (Theorem 3)'s proof defers to Theorem 2's. External: Farzanfard, MSc
thesis, Corollary 4.50, via `ExternalFacts.farzanfard_zero_density_interval`.

### Dependencies
**Depends on:** `Nrect`, `ExternalFacts.farzanfard_zero_density_interval`.
**Used by:** none. `mainJensen` and `mainLittlewood` assume `h ≤ t^{2/3}`, so the regime this
lemma addresses lies outside both theorems; the lemma and its table record why the tex carries
that regime only as a remark with a sketch (tex lines 176–180). -/
theorem Nrect_le_zero_density_bound {α h t : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hh : 0 ≤ h) (hth : 3 * 10 ^ (12 : ℕ) ≤ t - h) :
    (Nrect (t - h) (t + h) α : ℝ)
      ≤ 12.45321 * (t + h) ^ ((8 : ℝ) / 3 * α) * Real.log (t + h) ^ (3 + 2 * α)
        + 3.869 * Real.log (t + h) ^ (2 : ℕ) :=
  farzanfard_zero_density_interval hα hth (by linarith)

/-! ### The count vanishes below Platt–Trudgian's height, and on an empty window -/

/-- **`N(T₁,T₂,α) = 0` whenever `0 < T₁`, `T₂ ≤ H₀ = 3·10^12` and `α < 1/2`.**

### Summary of Proof
Every zero `ρ` counted by `Nrect T₁ T₂ α` has `0 < T₁ < Im ρ ≤ T₂ ≤ H₀`, so
`Background.ExternalFacts.platt_trudgian_verified_below` puts it on the critical line,
`Re ρ = 1/2`; but it also has `Re ρ > 1 - α > 1/2`. So `ζ` has no zero in the region at all, every
divisor order is `0` (`analyticOrderAt_eq_zero`, `ζ` being analytic there by
`Definitions.analyticOnNhd_riemannZeta_rect`), and the `finsum` vanishes.

### Lean Notes
This is the "truly trivial" case `t + h < H₀` of the tex's proofs of Theorems 2 and 3.
The hypothesis `0 < T₁` keeps `ζ`'s pole out of the region (as in `Nrect_nonneg`) and is also
what the `LiteratureInputs` field's `0 < Im ρ` needs; the consumers have `T₁ = t - h > 0` from
`h ≤ t^{2/3} < t`.

### References
tex: the `t + h < H₀` case in the proof of `\ref{thm:main-jensen}` (Theorem 2), tex line 170.
External: Platt–Trudgian, `\cite{PlattTrudgian2021}`.

### Dependencies
**Depends on:** `Nrect`, `analyticOnNhd_riemannZeta_rect`,
`ExternalFacts.platt_trudgian_verified_below`.
**Used by:** `mainJensen`, `mainLittlewood`. -/
theorem Nrect_eq_zero_of_le_H0 {T1 T2 α : ℝ} (hT1 : 0 < T1) (hT2 : T2 ≤ 3 * 10 ^ (12 : ℕ))
    (hα : α < 1 / 2) : Nrect T1 T2 α = 0 := by
  unfold Nrect
  have hanalytic := analyticOnNhd_riemannZeta_rect (T2 := T2) (γ := 1 - α) hT1
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  by_cases hu : u ∈ {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - α < s.re}
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hu]
    have hne : riemannZeta u ≠ 0 := by
      intro h0
      have hre := platt_trudgian_verified_below u (by linarith [hu.1]) (le_trans hu.2.1 hT2) h0
      have := hu.2.2
      linarith
    rw [(hanalytic u hu).analyticOrderAt_eq_zero.mpr hne]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

/-- **`N(T,T,α) = 0`: an empty window counts nothing.** The region `{T < Im s ≤ T}` is empty, so
every divisor value is `0` by `apply_eq_zero_of_notMem`. This is the `h = 0` endpoint of the tex's
`t^{2/3} ≥ h ≥ 0`, where both Theorems 2 and 3 reduce to the positivity of their right-hand sides.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Nrect`.
**Used by:** `mainJensen`, `mainLittlewood`, `HalvingConvention.Nhalf_self`. -/
theorem Nrect_self (T α : ℝ) : Nrect T T α = 0 := by
  unfold Nrect
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  apply Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
  intro hu
  exact absurd hu.2.1 (not_le.mpr hu.1)

/-! ### Two `rpow` facts for the window `h ≤ t^{2/3}` -/

/-- **`t^{2/3} ≤ 10^8` for `0 ≤ t ≤ 10^12`** — so a window `h ≤ t^{2/3}` around any `t ≤ 10^12`
stays below `H₀ = 3·10^12`, which is why the tex's shift case `t - h < H₀ < t + h` never occurs
once `h ≤ t^{2/3}`. `Real.rpow_le_rpow` plus `(10^12)^{2/3} = 10^8` (`Real.rpow_mul`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `mainJensen`, `mainLittlewood`. -/
theorem rpow_two_thirds_le_ten_pow_eight {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (10 : ℝ) ^ (12 : ℕ)) :
    t ^ ((2 : ℝ) / 3) ≤ (10 : ℝ) ^ (8 : ℕ) := by
  have h108 : ((10 : ℝ) ^ (12 : ℕ)) ^ ((2 : ℝ) / 3) = (10 : ℝ) ^ (8 : ℕ) := by
    rw [← Real.rpow_natCast (10 : ℝ) 12, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← h108]
  exact Real.rpow_le_rpow ht0 ht (by norm_num)

/-- **`t^{2/3} < t` for `t > 1`** — so `h ≤ t^{2/3}` gives `t - h > 0`, the positivity of the
window's lower edge that `Nrect_eq_zero_of_le_H0` and `Nrect_nonneg` need.
`Real.rpow_lt_rpow_of_exponent_lt` with exponents `2/3 < 1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `mainJensen`, `mainLittlewood`, `HalvingConvention.mainJensenHalf`,
`HalvingConvention.mainLittlewoodHalf`. -/
theorem rpow_two_thirds_lt_self {t : ℝ} (ht : 1 < t) : t ^ ((2 : ℝ) / 3) < t := by
  have := Real.rpow_lt_rpow_of_exponent_lt ht (by norm_num : (2 : ℝ) / 3 < 1)
  rwa [Real.rpow_one] at this

/-! ### Collapsing the sharper error brackets of `MainTheoremTight` to `EJensen`/`ELittlewood` -/

/-- **The Jensen bracket collapses: for `t > 10^12`,
`3.34/t^{1/3} + 4.01/t^{4/3} + 291/(t^{4/3} log t) ≤ 3.35/t^{1/3}`.**

### Summary of Proof
Write `t^{4/3} = t^{1/3}·t`. The two extra terms are `4.01/t` and `291/(t log t)` times `1/t^{1/3}`,
each at most `0.005/t^{1/3}` once `t ≥ 802` resp. `t log t ≥ 58200` — with `t > 10^12` and
`log t > 20` (`twenty_lt_log`) there is room to spare. This is the step the tex's own comment at
line 822 describes ("`t^{-1} ≤ 10^{-12}`, utterly negligible against `3.34`").

### References
tex: the commented-out collapse below `\ref{thm:rectangularjensen}` (Theorem 24), tex lines
822–826, and the `O^*` of `\ref{thm:main-jensen}` (Theorem 2), tex line 159.

### Dependencies
**Depends on:** `ten_thousand_le_rpow_third`, `twenty_lt_log`.
**Used by:** `mainJensen`. -/
theorem jensen_error_collapse {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
        + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t)
      ≤ 3.35 / t ^ ((1 : ℝ) / 3) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hu : (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := ten_thousand_le_rpow_third ht
  have hL : (20 : ℝ) < Real.log t := twenty_lt_log ht
  have hL0 : (0 : ℝ) < Real.log t := by linarith
  have h43 : t ^ ((4 : ℝ) / 3) = t ^ ((1 : ℝ) / 3) * t := by
    rw [show (4 : ℝ) / 3 = (1 : ℝ) / 3 + 1 by norm_num, Real.rpow_add ht0, Real.rpow_one]
  rw [h43]
  set u := t ^ ((1 : ℝ) / 3) with hu_def
  have hu0 : (0 : ℝ) < u := by linarith
  have hut : (0 : ℝ) < u * t := mul_pos hu0 ht0
  have h1 : 4.01 / (u * t) ≤ 0.005 / u := by
    rw [div_le_div_iff₀ hut hu0]
    nlinarith [mul_le_mul_of_nonneg_left ht.le hu0.le]
  have h2 : 291 / (u * t * Real.log t) ≤ 0.005 / u := by
    rw [div_le_div_iff₀ (mul_pos hut hL0) hu0]
    have hp : (10 : ℝ) ^ (12 : ℕ) * 20 ≤ t * Real.log t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hp hu0.le]
  have h3 : 3.34 / u + 0.005 / u + 0.005 / u = 3.35 / u := by ring
  linarith

/-- **The Littlewood bracket collapses: for `t > 10^12`,
`0.334 + 0.502/log t + 1.001/t + 72.48/(t log t) + 0.64/t^{1/3} + 46.3/(t^{1/3} log t)
  ≤ 0.335 + 0.51/log t`.**

### Summary of Proof
With `t > 10^12`, `t^{1/3} ≥ 10^4` (`ten_thousand_le_rpow_third`) and `log t > 20`
(`twenty_lt_log`): `1.001/t ≤ 0.0005`, `0.64/t^{1/3} ≤ 0.0005` (together the `0.001` gained in
the constant), and `72.48/(t log t) ≤ 0.001/log t`, `46.3/(t^{1/3} log t) ≤ 0.007/log t`
(together the `0.008` gained in the `1/log t` coefficient). The binding one is the last:
`46.3/10^4 = 0.00463 ≤ 0.007`.

### References
tex: the `O^*` of `\ref{thm:main-littlewood}` (Theorem 3), tex line 185, collapsed from the
six-term simplification inside `\ref{thm:littlewoodshort}` (Theorem 32), tex lines 1161–1164.

**Independent numeric check.** At `t = 10^12` the six-term bracket is
`0.334 + 0.502/27.63 + 10^{-12} + 2.6·10^{-12} + 6.4·10^{-5} + 1.68·10^{-4} = 0.35240`, against
the two-term `0.335 + 0.51/27.63 = 0.35346`; the collapse holds with margin `1.1·10^{-3}` there
and the margin grows with `t`.

### Dependencies
**Depends on:** `ten_thousand_le_rpow_third`, `twenty_lt_log`.
**Used by:** `mainLittlewood`. -/
theorem littlewood_error_collapse {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
        + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t)
      ≤ 0.335 + 0.51 / Real.log t := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hu : (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := ten_thousand_le_rpow_third ht
  have hL : (20 : ℝ) < Real.log t := twenty_lt_log ht
  have hL0 : (0 : ℝ) < Real.log t := by linarith
  set u := t ^ ((1 : ℝ) / 3) with hu_def
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : 1.001 / t ≤ 0.0005 := by rw [div_le_iff₀ ht0]; nlinarith
  have h2 : 0.64 / u ≤ 0.0005 := by rw [div_le_iff₀ hu0]; nlinarith
  have h3 : 72.48 / (t * Real.log t) ≤ 0.001 / Real.log t := by
    rw [div_le_div_iff₀ (mul_pos ht0 hL0) hL0]
    nlinarith [mul_le_mul_of_nonneg_right ht.le hL0.le]
  have h4 : 46.3 / (u * Real.log t) ≤ 0.007 / Real.log t := by
    rw [div_le_div_iff₀ (mul_pos hu0 hL0) hL0]
    nlinarith [mul_le_mul_of_nonneg_right hu hL0.le]
  have h5 : 0.502 / Real.log t + 0.001 / Real.log t + 0.007 / Real.log t
      = 0.51 / Real.log t := by ring
  linarith

/-! ### Positivity of the right-hand sides -/

/-- **`0 < U_J(α,r,h,t) + 3.35/(D_{r,α} t^{1/3})` for `0 < α < r < 1`, `h ≥ 0` and `t ≥ e`.**

### Summary of Proof
Every coefficient is non-negative — `B1_nonneg`, `B2_nonneg`, `B3_nonneg`, `B4_nonneg` from
`ConstantSigns`, `α̂_r = √(r²-α²) ≥ 0` — and so are `log t ≥ 1` and `log log t ≥ 0` once `t ≥ e`;
so `U_J ≥ 0`, while the error `3.35/(D_{r,α} t^{1/3})` is strictly positive (`rectDenom_pos`).

### Lean Notes
This is the whole content of Theorem 2 for `t ≤ 10^12` (where the count is zero) and for `h = 0`.
The threshold `t ≥ e` is exactly what makes `log log t ≥ 0`; below it the claim is false for the
paper's constants (see the module docstring).

### References
tex: the `t + h < H₀` case of `\ref{thm:main-jensen}` (Theorem 2), tex line 170, which the tex
calls "truly trivial" without mentioning the positivity of the right-hand side.

### Dependencies
**Depends on:** `UJensen`, `EJensen`, `B1_nonneg`, `B2_nonneg`, `B3_nonneg`, `B4_nonneg`,
`rectDenom_pos`, `hatAlpha`.
**Used by:** `mainJensen`, `HalvingConvention.mainJensenHalf`. -/
theorem UJensen_add_EJensen_pos {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht : Real.exp 1 ≤ t) (hh0 : 0 ≤ h) : 0 < UJensen α r h t + EJensen α r t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
  have hloglog : 0 ≤ Real.log (Real.log t) := Real.log_nonneg hlog1
  have hB1 := B1_nonneg hα0 hαr hr1
  have hB2 := B2_nonneg hα0 hαr
  have hB3 := B3_nonneg hα0 hαr hr1
  have hB4 := B4_nonneg hα0 hαr hr1
  have hA0 : 0 ≤ hatAlpha r α := Real.sqrt_nonneg _
  have hD : 0 < rectDenom r α := rectDenom_pos hα0 hαr
  have hbr : 0 ≤ B1 α r / Real.pi * Real.log t + B2 α r * Real.log (Real.log t) + B3 α r := by
    have h1 : 0 ≤ B1 α r / Real.pi * Real.log t :=
      mul_nonneg (div_nonneg hB1 Real.pi_pos.le) (by linarith)
    have h2 : 0 ≤ B2 α r * Real.log (Real.log t) := mul_nonneg hB2 hloglog
    linarith
  have hU : 0 ≤ UJensen α r h t := by
    unfold UJensen
    have : 0 ≤ (2 * h + 2 * hatAlpha r α)
        * (B1 α r / Real.pi * Real.log t + B2 α r * Real.log (Real.log t) + B3 α r) :=
      mul_nonneg (by linarith) hbr
    linarith
  have hE : 0 < EJensen α r t := by
    unfold EJensen
    exact div_pos (by norm_num) (mul_pos hD (Real.rpow_pos_of_pos ht0 _))
  linarith

/-- **`0 < U_L(α,r,h,t) + (1/(t(r-α)))(0.335 + 0.51/log t)` for `0 < α < r`, the pinned chord
index, `h ≥ 0` and `t ≥ e^e`.**

### Summary of Proof
`A1_nonneg`, `A2_nonneg`, `A4_nonneg`, `A5_nonneg`, `A6_nonneg` (`ConstantSigns`) make every
coefficient of `U_L` non-negative except `A₃`, whose sign is not available; `neg_A2_le_A3` gives
`A₃ ≥ -A₂`, and then `2h(A₂ log log t + A₃) ≥ 2hA₂(log log t - 1) ≥ 0` once `log log t ≥ 1`, i.e.
`t ≥ e^e`. The error term is strictly positive since `t > 0`, `r > α` and `log t > 0`.

### Lean Notes
This is the whole content of Theorem 3 for `t ≤ 10^12` (where the count is zero) and for `h = 0`.
The threshold `t ≥ e^e` (rather than Theorem 2's `t ≥ e`) is the price of not knowing `0 ≤ A₃`,
which is false for some chords (`ConstantSigns.neg_A2_le_A3`'s docstring). `r < 1` and `r > 0`
are derived from the chord hypotheses via `sigma_pos`/`sigma_lt_one`, as in
`mainLittlewoodTight`.

### References
tex: the `t + h < H₀` case of `\ref{thm:main-littlewood}` (Theorem 3), whose proof defers to
Theorem 2's (tex lines 194–198).

### Dependencies
**Depends on:** `ULittlewood`, `ELittlewood`, `A1_nonneg`, `A2_nonneg`, `neg_A2_le_A3`,
`A4_nonneg`, `A5_nonneg`, `A6_nonneg`, `sigma_pos`, `sigma_lt_one`.
**Used by:** `mainLittlewood`, `HalvingConvention.mainLittlewoodHalf`. -/
theorem ULittlewood_add_ELittlewood_pos {α r h t : ℝ} {k : ℤ} (hα0 : 0 < α) (hrα : α < r)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : Real.exp (Real.exp 1) ≤ t) (hh0 : 0 ≤ h) :
    0 < ULittlewood α r h t k + ELittlewood α r t := by
  have hr0 : (0 : ℝ) < r := by linarith [sigma_lt_one (k + 1), hk']
  have hr1 : r < 1 := by linarith [sigma_pos k, hk]
  have hrα' : (0 : ℝ) < r - α := by linarith
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hlog : Real.exp 1 ≤ Real.log t := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) ht
  have hlog0 : (0 : ℝ) < Real.log t := lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hloglog : (1 : ℝ) ≤ Real.log (Real.log t) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hlog
  have hA1 := A1_nonneg hrα hk hk'.le
  have hA2 := A2_nonneg (r := r) (k := k) hrα
  have hA3 := neg_A2_le_A3 hα0 hrα hr1 hk hk'.le
  have hA4 := A4_nonneg hr0 hr1 hrα
  have hA5 := A5_nonneg hr0 hrα
  have hA6 := A6_nonneg hα0 hrα hr1
  have hU : 0 ≤ ULittlewood α r h t k := by
    unfold ULittlewood
    have h1 : 0 ≤ (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log t := by
      apply mul_nonneg _ hlog0.le
      apply div_nonneg _ Real.pi_pos.le
      nlinarith
    have h2 : 0 ≤ 2 * A5 α r * Real.log (Real.log t) := by nlinarith
    have hsum : 0 ≤ A2 α r k + A3 α r k := by linarith
    have hp1 : 0 ≤ 2 * A2 α r k * h * (Real.log (Real.log t) - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA2) hh0) (by linarith)
    have hp2 : 0 ≤ 2 * h * (A2 α r k + A3 α r k) := mul_nonneg (by linarith) hsum
    nlinarith [hp1, hp2]
  have hE : 0 < ELittlewood α r t := by
    unfold ELittlewood
    apply mul_pos (one_div_pos.mpr (mul_pos ht0 hrα'))
    have : 0 ≤ 0.51 / Real.log t := div_nonneg (by norm_num) hlog0.le
    linarith
  linarith

/-! ### The two main theorems -/

/-- **Theorem `\ref{thm:main-jensen}` (Theorem 2, Jensen mechanism).** For `0 < α < r < 1` with
`α < 1/6`, `t ≥ e` and `0 ≤ h ≤ t^{2/3}`,
`N(t-h,t+h,α) < U_J(α,r,h,t) + O^*(3.35/(D_{r,α} t^{1/3}))`.

### Summary of Proof
Two cases (the tex's three collapse to these once `h ≤ t^{2/3}`; see the module docstring):

* `t > 10^12`. For `h > 0` this is `MainTheoremTight.mainJensenTight` — i.e.
  `Theorem \ref{thm:rectangularjensen}` (Theorem 24) with its `t > 10^12`, `h ≤ t^{2/3}`
  simplification — followed by `jensen_error_collapse`, which absorbs the two `t^{-4/3}` terms of
  the three-term bracket into `3.34 → 3.35`. For `h = 0` the window is empty (`Nrect_self`) and the
  right-hand side is positive (`UJensen_add_EJensen_pos`).
* `t ≤ 10^12`. Then `t + h ≤ 10^12 + 10^8 < H₀` (`rpow_two_thirds_le_ten_pow_eight`) and
  `t - h > 0` (`rpow_two_thirds_lt_self`), so the count is zero by Platt–Trudgian
  (`Nrect_eq_zero_of_le_H0`) and the claim is again `UJensen_add_EJensen_pos`.

### Lean Notes
**`ht : Real.exp 1 ≤ t`** is the tex's own threshold (tex line 158), and it is not slack: the
right-hand side contains `log log t` with a positive coefficient, so the statement fails for `t`
slightly above `1`. `t ≥ e` is exactly what `UJensen_add_EJensen_pos` needs.

**`hh0 : 0 ≤ h`** and **`hh : h ≤ t^{2/3}`** are the tex's `t^{2/3} ≥ h ≥ 0`, both non-strict.
The `h = 0` endpoint is closed here rather than by `mainJensenTight`, whose route through
`rectangularjensen_tight` needs `0 < h`. For `h < 0` the statement would be false (empty window,
`U_J → -∞` as `h → -∞`), so the tex's lower bound cannot be dropped.

The `α < 1/6` hypothesis is written as `α < alphaBoundTodo`, which is definitionally `1/6`; it is
the tex's own hypothesis, passed on to `mainJensenTight`.

Nothing on this route is `sorry` or `axiom`. Everything the Jensen mechanism does not prove
enters through the hypothesis classes carried in the signature (`LiteratureInputs`,
`NumericCertificates`, `BrentStirlingInputs`, `LaurentCertificate`, `InterpolationCertificates`,
`Hcompact2Certificates`), so `#print axioms` returns only `propext`, `Classical.choice` and
`Quot.sound`.

### References
tex: `\ref{thm:main-jensen}` (Theorem 2), tex lines 157–175. Consumes
`\ref{thm:rectangularjensen}` (Theorem 24) through `mainJensenTight`, and
`\cite{PlattTrudgian2021}` through `Nrect_eq_zero_of_le_H0`.

### Dependencies
**Depends on:** `UJensen`, `EJensen`, `alphaBoundTodo`, `Nrect`, `mainJensenTight`,
`jensen_error_collapse`, `UJensen_add_EJensen_pos`, `Nrect_eq_zero_of_le_H0`, `Nrect_self`,
`rpow_two_thirds_le_ten_pow_eight`, `rpow_two_thirds_lt_self`, `rectDenom_pos`.
**Used by:** `AllHypotheses.mainJensen'`, `HalvingConvention.mainJensenHalf`,
`MainCorollary.mainPositiveProportionCorollary_jensen`, `Solution.zero_density_jensen`. -/
theorem mainJensen {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (hα : α < alphaBoundTodo) (ht : Real.exp 1 ≤ t) (hh0 : 0 ≤ h)
    (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    (Nrect (t - h) (t + h) α : ℝ) < UJensen α r h t + EJensen α r t := by
  have hα16 : α < 1 / 6 := hα
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have ht1 : (1 : ℝ) < t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hht : h < t := lt_of_le_of_lt hh (rpow_two_thirds_lt_self ht1)
  have hpos := UJensen_add_EJensen_pos hα0 hαr hr1 ht hh0
  rcases le_or_gt t ((10 : ℝ) ^ (12 : ℕ)) with hsmall | hbig
  · -- `t ≤ 10^12`: the whole window lies below Platt–Trudgian's height, so the count is zero
    have h8 : t ^ ((2 : ℝ) / 3) ≤ 100000000 := by
      have := rpow_two_thirds_le_ten_pow_eight ht0.le hsmall
      norm_num at this
      exact this
    have h12 : t ≤ 1000000000000 := by norm_num at hsmall; exact hsmall
    have hH0 : t + h ≤ 3 * 10 ^ (12 : ℕ) := by norm_num; linarith
    rw [Nrect_eq_zero_of_le_H0 (by linarith) hH0 (by linarith)]
    simpa using hpos
  · rcases hh0.eq_or_lt with h0 | hhpos
    · -- `h = 0`: empty window
      subst h0
      rw [sub_zero, add_zero, Nrect_self]
      simpa using hpos
    · -- `t > 10^12`, `h > 0`: the regime form plus the numerical collapse of its bracket
      have hmain := mainJensenTight hα0 hαr hr1 hα16 hbig hhpos hh
      have hD : 0 < rectDenom r α := rectDenom_pos hα0 hαr
      have hcol : (1 / rectDenom r α) *
          (3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
            + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t)) ≤ EJensen α r t := by
        unfold EJensen
        rw [show 3.35 / (rectDenom r α * t ^ ((1 : ℝ) / 3))
            = (1 / rectDenom r α) * (3.35 / t ^ ((1 : ℝ) / 3)) by
          rw [div_mul_div_comm, one_mul]]
        exact mul_le_mul_of_nonneg_left (jensen_error_collapse hbig) (by positivity)
      linarith

/-- **Theorem `\ref{thm:main-littlewood}` (Theorem 3, Littlewood mechanism).** For `r > α > 0`
with `α < 1/6`, the chord index `k` pinned by `σ_k ≤ 1-r < σ_{k+1}`, `t ≥ e^e` and
`0 ≤ h ≤ t^{2/3}`,
`N(t-h,t+h,α) < U_L(α,r,h,t) + O^*((1/(t(r-α)))(0.335 + 0.51/log t))`.

### Summary of Proof
As for `mainJensen`, with `MainTheoremTight.mainLittlewoodTight` (i.e.
`Theorem \ref{thm:littlewoodshort}`, Theorem 32, with its `t > 10^12`, `h ≤ t^{2/3}`
simplification) in place of `mainJensenTight`, `littlewood_error_collapse` absorbing the four
small terms of the six-term bracket into `0.334 → 0.335`, `0.502 → 0.51`, and
`ULittlewood_add_ELittlewood_pos` for the two cases in which the count vanishes (`t ≤ 10^12`, and
`h = 0`).

### Lean Notes
**`ht : Real.exp (Real.exp 1) ≤ t`** is the tex's own threshold (tex line 184), one notch stronger
than Theorem 2's `t ≥ e`: the right-hand side's positivity below `10^12` needs `log log t ≥ 1`
because only `-A₂ ≤ A₃` is available (`ConstantSigns.neg_A2_le_A3`; `A₃` is genuinely negative for
some chords). See the module docstring.

**No hypothesis on `arg ζ`**: `argZeta` is the tex's constructed branch
(`LittlewoodMethod.argZetaDef`), so the polar form is a theorem rather than an assumption (see the
module docstring).

**`hzf_p`/`hzf_m`**: inherited from `mainLittlewoodTight` ← `littlewoodshort_tight` ←
`LittlewoodIdentity.littlewood_zero_density_integral` (Equation 13): no zero of `ζ` on the two
horizontal edges `Im s = t ± h`, `Re s ∈ [1-r, 1+ηr]`, which is the tex's first `arg ζ` case.
Nothing is assumed on the left edge `Re s = 1-r`: the tex's improper `∫ log|ζ(1-r+it)| dt` is a
Lebesgue integral of an integrable function
(`LittlewoodIdentity.intervalIntegrable_log_norm_zeta_vertical`). Used only in the `t > 10^12`,
`h > 0` case. The half-counted form with no edge hypothesis is
`HalvingConvention.mainLittlewoodHalf`.

**`hh0 : 0 ≤ h`**, **`hh : h ≤ t^{2/3}`**, **`α < 1/6`**: as in `mainJensen`. `r < 1` is not
assumed (as in the tex) but follows from `hk`; `hα12 : α < 1/2` of `mainLittlewoodTight` is
supplied from `α < 1/6`.

Nothing on this route is `sorry` or `axiom`; the unproved inputs are fields of the hypothesis
classes carried in the signature.

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3), tex lines 183–198. Consumes
`\ref{thm:littlewoodshort}` (Theorem 32) through `mainLittlewoodTight`; the tex's proof defers to
`\ref{thm:main-jensen}` (Theorem 2)'s.

### Dependencies
**Depends on:** `ULittlewood`, `ELittlewood`, `Nrect`, `sigma`, `argZeta`, `eta`,
`mainLittlewoodTight`, `littlewood_error_collapse`, `ULittlewood_add_ELittlewood_pos`,
`Nrect_eq_zero_of_le_H0`, `Nrect_self`, `rpow_two_thirds_le_ten_pow_eight`,
`rpow_two_thirds_lt_self`.
**Used by:** `AllHypotheses.mainLittlewood'`, `HalvingConvention.mainLittlewoodHalf`,
`MainCorollary.mainPositiveProportionCorollary_littlewood`, `Solution.zero_density_littlewood`. -/
theorem mainLittlewood {α r h t : ℝ} {k : ℤ} (hα0 : 0 < α) (hrα : α < r) (hα16 : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : Real.exp (Real.exp 1) ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t - h) * Complex.I) ≠ 0) :
    (Nrect (t - h) (t + h) α : ℝ) < ULittlewood α r h t k + ELittlewood α r t := by
  have hee : (1 : ℝ) < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
  have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hee ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hrα' : (0 : ℝ) < r - α := by linarith
  have hht : h < t := lt_of_le_of_lt hh (rpow_two_thirds_lt_self ht1)
  have hpos := ULittlewood_add_ELittlewood_pos (k := k) hα0 hrα hk hk' ht hh0
  rcases le_or_gt t ((10 : ℝ) ^ (12 : ℕ)) with hsmall | hbig
  · -- `t ≤ 10^12`: the whole window lies below Platt–Trudgian's height, so the count is zero
    have h8 : t ^ ((2 : ℝ) / 3) ≤ 100000000 := by
      have := rpow_two_thirds_le_ten_pow_eight ht0.le hsmall
      norm_num at this
      exact this
    have h12 : t ≤ 1000000000000 := by norm_num at hsmall; exact hsmall
    have hH0 : t + h ≤ 3 * 10 ^ (12 : ℕ) := by norm_num; linarith
    rw [Nrect_eq_zero_of_le_H0 (by linarith) hH0 (by linarith)]
    simpa using hpos
  · rcases hh0.eq_or_lt with h0 | hhpos
    · -- `h = 0`: empty window
      subst h0
      rw [sub_zero, add_zero, Nrect_self]
      simpa using hpos
    · -- `t > 10^12`, `h > 0`: the regime form plus the numerical collapse of its bracket
      have hmain := mainLittlewoodTight hα0 hrα (by linarith) hk hk' hbig hhpos hh hzf_p hzf_m
      have hcol : (1 / (t * (r - α))) *
          (0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
            + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t))
          ≤ ELittlewood α r t := by
        unfold ELittlewood
        exact mul_le_mul_of_nonneg_left (littlewood_error_collapse hbig)
          (one_div_pos.mpr (mul_pos ht0 hrα')).le
      linarith
