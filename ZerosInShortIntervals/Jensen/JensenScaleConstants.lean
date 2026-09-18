/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Background.BackgroundZetaBounds

/-! # Piecewise-linear scale constants for the Jensen bound

This file formalizes the family of constants from `\S1.1` ("Bounding Integrals Inside the Critical
Strip") of `ZerosInShortIntervals.tex`, culminating in `c₁,r`, `c₂,r`, `c₃,r` from
Proposition `\ref{prop:jensen-easy}` (**Proposition 8**).

**⚠ KNOWN DISCREPANCY WITH THE PAPER'S TABLES.** The source offers two admissible values for the
`k = 0` (half-line) coefficient triple: the main text's `(v₀,v₀',v₀'') = (1/6, 1, log 0.611)` (the
Hiary–Revers half-line bound `|ζ(1/2+it)| ≤ 0.611|t|^{1/6}log|t|`), and, in
`Remark \ref{rem:altcoefficients}` (Remark 7) just after, `(27/164, 0, log 66.7)` (the
Patel–Yang sub-Weyl bound `|ζ(1/2+it)| ≤ 66.7|t|^{27/164}`). **This file implements the main-text
triple; the paper's Tables 2–7 are computed with the Remark's.** Both give valid bounds, but the
constants differ substantially — recomputing the tex's own defining sums at `r = 1/2` gives
`c₃ = 0.0982` under the main-text triple against the tabulated `3.0615`, a factor of 31. So `c1`,
`c2`, `c3` here — and everything built on them (`C1..C3`, `B1..B4`, `A1..A6`) — are *not* the
numbers printed in the paper. Which triple is canonical is an author decision, so it is
deliberately not made here.

The source defines, for every integer `k` (positive `k` indexing lines close to `Re s = 1`,
negative `k` indexing the mirror lines close to `Re s = 0` via the functional equation), a
vertical line `σ_k` together with the coefficients `(v_k, v_k', v_k'')` of an explicit bound
`log|ζ(σ_k+it)| ≤ v_k log|t| + v_k' log log|t| + v_k''`, coming from `YANG2024128124` combined with
`lem:zetalessthanhalf`. Linear interpolation between consecutive lines `σ_k ≤ σ ≤ σ_{k+1}` gives
slopes/intercepts `(m_k,b_k)`, `(m_k',b_k')`, `(m_k'',b_k'')` (Equations `(eq:mk)`, `(eq:mkp)`,
`(eq:mkpp)`), which are then integrated in `θ` (via Equation `(eq:thetak)`) to produce `c₁,r`,
`c₂,r`, `c₃,r`.

**The index `K`.** The source sets `K = inf_k (r ≥ 1 - σ_k)` and explicitly admits the value
`-∞`. Since every application here has `r ≤ 1`, that can only happen at the single boundary value
`r = 1`, so `Kidx r` is taken to be the integer infimum (`sInf`), which is junk (`0`) exactly at
that one edge case.
-/

open scoped ComplexConjugate

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates]

/-- **The vertical lines `σ_k`, `k : ℤ`**, from Equation `\ref{eq:sigmak}` (Equation 4):
`σ_k = 1-(k+3)/(2^{k+3}-2)` for `k ≥ 0`, and `σ_{-k} = (k+3)/(2^{k+3}-2)` for the mirror lines.

### Summary of Proof
A definition. For `k ≥ 0` these increase to `1` from the left (`σ_0 = 1/2`, `σ_1 = 5/7`,
`σ_2 = 5/6`, …); the negative indices mirror them across `Re s = 1/2`, so `σ_{-k} = 1 - σ_k`
(proved as `sigma_neg_eq`). These are exactly the lines on which Yang's critical-strip bound,
combined with Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36), supplies estimates for `ζ`.

### Lean Notes
`σ_0 = 1/2` **exactly** (`ConstantSigns.sigma_zero_eq`). So at radius `r = 1/2` the abscissa
`1 - r` is a chord *endpoint*, not an interior point: the linear interpolation degenerates and
returns the tabulated value `vCoeff 0 = 1/6` on the nose. That is what makes the headline
corollary's constant positive for every `α` in `(0, 1/6)` with no side condition.

### References
tex: Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** none.
**Used by:** `Kidx`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `chordIdx`, `mCoeff`, `mCoeffP`,
`mCoeffPP`, `theta`, `vCoeff`, `vCoeffPP`, `vRatio`. -/
noncomputable def sigma (k : ℤ) : ℝ :=
  if 0 ≤ k then 1 - (k + 3 : ℝ) / (2 ^ (k + 3) - 2)
  else ((-k : ℝ) + 3) / (2 ^ (-k + 3) - 2)

/-- **The coefficients `v_k` of `log|t|`** in the bound `log|ζ(σ_k+it)| ≤ v_k log|t| + ⋯`:
`v_k = 1/(2^{k+3}-2)` for `k ≥ 0`, and `v_{-k} = σ_k - 1/2 + 1/(2^{k+3}-2)` for the mirror lines.

### Summary of Proof
A definition. The `k ≥ 0` values are read off Yang's critical-strip bound at `σ_k`; the `k < 0`
values are their reflections through the functional equation, Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36), which costs the extra `σ_k - 1/2`.

### Lean Notes
**`v₀` is the contested one.** Here `v₀ = 1/(2³-2) = 1/6`, the main text's value, coming from
the Hiary–Revers half-line bound. The tex's Remark permits `27/164` instead, and the paper's
Tables 2–7 are computed with that. Both are admissible — see
`JensenScaleConstantsAlt.zeta_piecewise_bound_alt`, which proves the Remark's triple admissible
without disturbing anything proved here — but the two choices give different downstream
constants. See this file's module docstring.

### References
tex: the display just after Equation `\ref{eq:sigmak}` (Equation 4), and its following
`Remark \ref{rem:altcoefficients}` (Remark 7).
External: Yang, arXiv:2301.03165, for the `k ≥ 0` anchors.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `mCoeff`, `bCoeff`, `vRatio`, `vCoeff_le`, `vCoeff_nonneg`, `vCoeff_lt_succ`,
`vCoeff_strictAnti`, `vCoeff_ratio_step`, `chord_vCoeff_nonneg`, `chord_vCoeff_le`,
`chord_mem_Icc`, and the four `zeta_chord_bound_*` families. -/
noncomputable def vCoeff (k : ℤ) : ℝ :=
  if 0 ≤ k then 1 / (2 ^ (k + 3) - 2)
  else sigma (-k) - 1 / 2 + 1 / (2 ^ (-k + 3) - 2)

/-- **The coefficients `v_k'` of `log log|t|`**: identically `1` for every `k`.

### Summary of Proof
A definition, constant in `k`. Because it is constant, the corresponding chord is flat —
`mCoeffP` is identically `0` and `bCoeffP` identically `1` (`mCoeffP_eq_zero`,
`bCoeffP_eq_one`) — which is what keeps the `c₂` sum trivial to bound.

### Lean Notes
**Slight extrapolation beyond the tex.** The display following Equation `\ref{eq:sigmak}`
(Equation 4) states `v_k' = 1` only for **k > 0**; it gives no `v_0'` in the main text. Taking it
to be `1` at `k = 0` is what the main-text half-line bound `0.611|t|^{1/6}log|t|` gives, since
its `log log|t|` coefficient really is `1`, and the `k < 0` values then follow by reflection. But
the source does not write this down, and its Remark offers `v₀' = 0` instead (paired with
`v₀ = 27/164`, `v₀'' = log 66.7`) — that alternative is formalized in
`JensenScaleConstantsAlt.vCoeffPAlt`.

### References
tex: the display following Equation `\ref{eq:sigmak}` (Equation 4), and its
`Remark \ref{rem:altcoefficients}` (Remark 7).

### Dependencies
**Depends on:** none.
**Used by:** `mCoeffP`, `bCoeffP`, `mCoeffP_eq_zero`, `bCoeffP_eq_one`, `c2_nonneg`,
`c2_le_pi_div_two`, the `zeta_chord_bound_*` families, `littlewood_mainterm`(`_tight`). -/
noncomputable def vCoeffP (_k : ℤ) : ℝ := 1

/-- **The constant-term coefficients `v_k''`**, by cases on the sign of `k`: `log(1.546)` for
`k > 0`, `log(0.611)` at `k = 0`, and `log(1.546) + (σ_k - 1/2)log|π|` for `k < 0`.

### Summary of Proof
A definition. For `k > 0` the constant is Yang's `1.546`. At `k = 0` the half-line bound supplies
`0.611` instead. For `k < 0` the value is obtained from `v_{-k}'' = log(1.546)` — valid at the
mirror point `σ_{-k} > 1/2` — by reflecting through the functional equation, Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36), whose constant correction term is exactly
`(σ-1/2)log|π|`.

### Lean Notes
**`v₀''` is the contested one**: `log(0.611)` here (main text), against `log(66.7)` in the tex's
Remark, which is what the paper's tables use. The Remark's value is formalized separately as
`JensenScaleConstantsAlt.vCoeffPPAlt` and proved admissible there. See this file's module
docstring.

### References
tex: the display following Equation `\ref{eq:sigmak}` (Equation 4), and its
`Remark \ref{rem:altcoefficients}` (Remark 7); Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36) for the reflection. External: Yang, arXiv:2301.03165.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `mCoeffPP`, `bCoeffPP`, `mCoeffPP_eq_zero_of_pos`, `bCoeffPP_eq_of_pos`,
`vCoeffPP_neg_eq`, the `zeta_chord_bound_*` families. -/
noncomputable def vCoeffPP (k : ℤ) : ℝ :=
  if 0 < k then Real.log 1.546
  else if k = 0 then Real.log 0.611
  else Real.log 1.546 + (sigma k - 1 / 2) * Real.log Real.pi

/-! ### The chord coefficients — CONVENTION

**The chord is `mCoeff k * σ + bCoeff k`, evaluated at `σ` itself — NOT at `1 - σ`.**

This matches Equation `(eq:mk)` (**Equation 5**) character for character, including the fact that
the slope's denominator `σ_k - σ_{k+1}` is *negative* (`σ` is increasing in `k`), so `mCoeff k < 0`
for the `log|t|` family. With `bCoeff k = v_k - mCoeff k * σ_k`, the affine function
`σ ↦ mCoeff k * σ + bCoeff k` is exactly the linear interpolation carrying `σ_k ↦ v_k` and
`σ_{k+1} ↦ v_{k+1}` (see `chord_vCoeff_nonneg`, `chord_vCoeff_le`, `chord_mem_Icc`).

Recording this explicitly matters because the opposite parameterisation (denominator
`σ_{k+1} - σ_k`, and `b = v - m(1-σ_k)`, so that the chord is a function of `1 - σ`) describes the
same line and is easy to confuse with this one: chord-in-`y` at `y` equals chord-in-`σ` at
`σ = 1-y`. The `Code/` scripts use the convention fixed here.
-/

/-- **Slope of `log|t|`'s coefficient on `[σ_k, σ_{k+1}]`**, from Equation `\ref{eq:mk}`
(Equation 5): `m_k = (v_k - v_{k+1})/(σ_k - σ_{k+1})`.

### Summary of Proof
A definition. Negative, since `v` decreases while `σ` increases (`mCoeff_neg`).

### Lean Notes
See the convention block above: the chord is `mCoeff k * σ + bCoeff k`, evaluated at `σ` itself,
with the denominator `σ_k - σ_{k+1}` **negative**.

### References
tex: Equation `\ref{eq:mk}` (Equation 5).

### Dependencies
**Depends on:** `vCoeff`, `sigma`.
**Used by:** `bCoeff`, `c1`, `A1`, `arcMaj`, `arcMaj_tight`, `chordA`, `mCoeff_neg`,
`mCoeff_add_bCoeff_neg`, `zeta_piecewise_bound`(`_tight_simple`), the `zeta_chord_bound_*`
families, `littlewood_mainterm`(`_tight`), `littlewoodshort`(`_tight`). -/
noncomputable def mCoeff (k : ℤ) : ℝ := (vCoeff k - vCoeff (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of `log|t|`'s coefficient on `[σ_k, σ_{k+1}]`**, from Equation `\ref{eq:mk}`
(Equation 5): `b_k = v_k - m_k σ_k`, pinned so the chord passes through `(σ_k, v_k)`.

### Summary of Proof
A definition. Together with `mCoeff` it makes `σ ↦ mCoeff k * σ + bCoeff k` the linear
interpolation carrying `σ_k ↦ v_k` and `σ_{k+1} ↦ v_{k+1}`.

### Lean Notes
See the convention block above.

### References
tex: Equation `\ref{eq:mk}` (Equation 5).

### Dependencies
**Depends on:** `vCoeff`, `mCoeff`, `sigma`.
**Used by:** `c1`, `A1`, `arcMaj`, `arcMaj_tight`, `chordA`, `bCoeff_pos`,
`mCoeff_add_bCoeff_neg`, `zeta_piecewise_bound`(`_tight_simple`), the `zeta_chord_bound_*`
families, `littlewood_mainterm`(`_tight`), `littlewoodshort`(`_tight`). -/
noncomputable def bCoeff (k : ℤ) : ℝ := vCoeff k - mCoeff k * sigma k

/-- **Slope of `log log|t|`'s coefficient on `[σ_k, σ_{k+1}]`**, from Equation `\ref{eq:mkp}`
(Equation 6).

### Summary of Proof
A definition. Since `vCoeffP` is constant, the numerator `v_k' - v_{k+1}'` vanishes, so this is
identically `0` (`mCoeffP_eq_zero`) and correspondingly `bCoeffP = 1` (`bCoeffP_eq_one`).

### References
tex: Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `vCoeffP`, `sigma`.
**Used by:** `bCoeffP`, `c2`, `A2`, `arcMaj`, `arcMaj_tight`, `chordA'`, `mCoeffP_eq_zero`, the
`zeta_chord_bound_*` families. -/
noncomputable def mCoeffP (k : ℤ) : ℝ := (vCoeffP k - vCoeffP (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of `log log|t|`'s coefficient on `[σ_k, σ_{k+1}]`**, from Equation
`\ref{eq:mkp}` (Equation 6). Identically `1`.

### Summary of Proof
A definition: `b_k' = v_k' - m_k' σ_k = 1 - 0·σ_k = 1`, since `mCoeffP` vanishes. Proved as
`bCoeffP_eq_one`.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `vCoeffP`, `mCoeffP`, `sigma`.
**Used by:** `c2`, `A2`, `arcMaj`, `arcMaj_tight`, `chordA'`, `bCoeffP_eq_one`, the
`zeta_chord_bound_*` families. -/
noncomputable def bCoeffP (k : ℤ) : ℝ := vCoeffP k - mCoeffP k * sigma k

/-- **Slope of the constant term on `[σ_k, σ_{k+1}]`**, from Equation `\ref{eq:mkpp}`
(Equation 7).

### Summary of Proof
A definition. It vanishes for `k > 0`, where `vCoeffPP` is the constant `log 1.546`
(`mCoeffPP_eq_zero_of_pos`) — which is what makes the `c₃` tail summable.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `vCoeffPP`, `sigma`.
**Used by:** `bCoeffPP`, `c3`, `A3`, `arcMaj`, `arcMaj_tight`, `chordA''`,
`mCoeffPP_eq_zero_of_pos`, `c3_summable`, the `zeta_chord_bound_*` families. -/
noncomputable def mCoeffPP (k : ℤ) : ℝ :=
  (vCoeffPP k - vCoeffPP (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of the constant term on `[σ_k, σ_{k+1}]`**, from Equation `\ref{eq:mkpp}`
(Equation 7).

### Summary of Proof
A definition: `b_k'' = v_k'' - m_k'' σ_k`. Equal to `log 1.546` for `k > 0`
(`bCoeffPP_eq_of_pos`), since there `mCoeffPP` vanishes — which is what makes the `c₃` tail
summable.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `vCoeffPP`, `mCoeffPP`, `sigma`.
**Used by:** `c3`, `A3`, `arcMaj`, `arcMaj_tight`, `chordA''`, `bCoeffPP_eq_of_pos`,
`c3_summable`, the `zeta_chord_bound_*` families. -/
noncomputable def bCoeffPP (k : ℤ) : ℝ := vCoeffPP k - mCoeffPP k * sigma k

/-- **`sigma` at a nonnegative index, unfolded to closed form** with an `ℕ`-power and no `if`.

### Summary of Proof
Unfold the definition, discharge the `if` by `0 ≤ n` (`positivity`), convert the `ℤ`-exponent
`(n:ℤ)+3` to the `ℕ`-exponent `n+3` by `omega` and `zpow_natCast`, then `push_cast; ring`.

### Lean Notes
Purely a normal-form lemma. `sigma` is defined by cases on the sign of `k` with a `zpow`; almost
every downstream computation wants the branch-free `ℕ`-power form instead.

### References
No tex counterpart — the tex writes the `k ≥ 0` formula of Equation `\ref{eq:sigmak}`
(Equation 4) directly, with no case split to unfold.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `one_sub_sigma_natCast_le_geom`, `sigma_natCast_mem`, `sigma_strictMono_succ`,
`vCoeff_ratio_step`, `zeta_chord_bound_nonneg`, `zeta_chord_bound_nonneg_tight`,
`zeta_chord_bound_nonneg_tight_simple`. -/
private theorem sigma_natCast (n : ℕ) : sigma (n:ℤ) = 1 - ((n:ℝ)+3)/(2^(n+3)-2) := by
  unfold sigma
  rw [ite_eq_left (by positivity), show ((n:ℤ)+3:ℤ) = ((n+3:ℕ):ℤ) by omega, zpow_natCast]
  push_cast; ring

/-- **`vCoeff` at a nonnegative index, unfolded to closed form**: `v_n = 1/(2^{n+3}-2)`.

### Summary of Proof
As `sigma_natCast`: unfold, discharge the `if` by `0 ≤ n`, and convert the `ℤ`-exponent to an
`ℕ`-exponent.

### Lean Notes
Purely a normal-form lemma, for the same reason as `sigma_natCast`.

### References
No tex counterpart — the tex writes this formula directly, in the display after Equation
`\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `vCoeff`.
**Used by:** `vCoeff_le`, `vCoeff_natCast_nonneg`, `vCoeff_ratio_step`,
`zeta_chord_bound_nonneg`, `zeta_chord_bound_nonneg_tight`,
`zeta_chord_bound_nonneg_tight_simple`. -/
private theorem vCoeff_natCast (n : ℕ) : vCoeff (n:ℤ) = 1/(2^(n+3)-2) := by
  unfold vCoeff
  rw [ite_eq_left (by positivity), show ((n:ℤ)+3:ℤ) = ((n+3:ℕ):ℤ) by omega, zpow_natCast]

/-- **`2m + 8 ≤ 2^{m+3}` for every natural `m`.**

### Summary of Proof
Induction on `m`. The base case is `8 ≤ 8`. The step uses
`2^{m+4} = 2·2^{m+3} ≥ 2(2m+8) = (2m+10) + (2m+6) ≥ 2(m+1)+8`, since `2m+6 > 0`.

### Lean Notes
Pure arithmetic plumbing. It is what shows the denominator `2^{k+3}-2` of `v_k` dominates the
numerator `k+3` of `σ_k`, which is what puts `σ_k` in `[1/2,1)` and hence keeps the chord data
well-formed.

### References
No tex counterpart — the tex treats the growth of `2^{k+3}` as evident.

### Dependencies
**Depends on:** none.
**Used by:** `sigma_natCast_mem`, `zeta_chord_bound_neg`, `zeta_chord_bound_neg_tight`,
`zeta_chord_bound_neg_tight_simple`. -/
private theorem two_mul_add_eight_le_pow (m : ℕ) : 2*(m:ℝ)+8 ≤ 2^(m+3) := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    have h2 : (2:ℝ)^(n+1+3) = 2*2^(n+3) := by rw [show n+1+3=(n+3)+1 by omega, pow_succ]; ring
    rw [h2]; push_cast; linarith

/-- **`sigma` is strictly increasing across consecutive nonnegative indices**,
`σ_m < σ_{m+1}`.

### Summary of Proof
Put both sides in closed form via `sigma_natCast`. Since `σ_m = 1 - (m+3)/(2^{m+3}-2)`, the
claim is that `(m+3)/(2^{m+3}-2)` strictly decreases. Writing `2^{m+4} = 2·2^{m+3}` and clearing
the two positive denominators with `div_lt_div_iff₀`, `nlinarith` closes it using `2^{m+3} ≥ 8`.

### References
No tex counterpart as a numbered claim — the tex asserts that the `σ_k` approach `1` from the
left when introducing Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_natCast`.
**Used by:** `sigma_lt_succ`, `zeta_chord_bound_neg`, `zeta_chord_bound_neg_tight`,
`zeta_chord_bound_neg_tight_simple`. -/
private theorem sigma_strictMono_succ (m : ℕ) : sigma (m:ℤ) < sigma ((m:ℤ)+1) := by
  have hs0 := sigma_natCast m
  have hs1 := sigma_natCast (m+1)
  push_cast at hs1
  rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs0, hs1]
  have e4 : (2:ℝ)^(m+1+3) = 2*2^(m+3) := by rw [show m+1+3=(m+3)+1 by omega, pow_succ]; ring
  rw [e4]
  have hy : (8:ℝ) ≤ 2^(m+3) := by
    calc (8:ℝ) = 2^3 := by norm_num
      _ ≤ 2^(m+3) := by apply pow_le_pow_right₀ (by norm_num); omega
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  rw [sub_lt_sub_iff_left, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **`σ_m ∈ [1/2, 1)` at every nonnegative index.**

### Summary of Proof
In closed form `σ_m = 1 - (m+3)/(2^{m+3}-2)`, so the claim is that the subtracted fraction lies
in `(0, 1/2]`. Positivity is immediate. The upper bound is exactly
`two_mul_add_eight_le_pow`, rearranged: `2(m+3) ≤ 2^{m+3}-2` is `2m+8 ≤ 2^{m+3}`.

### References
No tex counterpart as a numbered claim — implicit in Equation `\ref{eq:sigmak}` (Equation 4),
whose lines all lie in the critical strip.

### Dependencies
**Depends on:** `sigma_natCast`, `two_mul_add_eight_le_pow`.
**Used by:** `sigma_lt_one`, `sigma_pos`, `vCoeff_nonneg`, `zeta_chord_bound_neg`,
`zeta_chord_bound_neg_tight`, `zeta_chord_bound_neg_tight_simple`. -/
private theorem sigma_natCast_mem (m : ℕ) : (1:ℝ)/2 ≤ sigma (m:ℤ) ∧ sigma (m:ℤ) < 1 := by
  rw [sigma_natCast]
  have hpow := two_mul_add_eight_le_pow m
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hdiv : ((m:ℝ)+3)/(2^(m+3)-2) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hdiv_pos : (0:ℝ) < ((m:ℝ)+3)/(2^(m+3)-2) := div_pos (by linarith) (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **Mirror identity `σ_{-j} = 1 - σ_j`**, unconditional in `j : ℕ`.

### Summary of Proof
Case on whether `j = 0`. At `j = 0` both sides are `1/2`, by `norm_num`. For `j ≥ 1` the two
`if`-branches of `sigma` select opposite arms; unfolding both and cancelling gives
`(j+3)/(2^{j+3}-2) = 1 - (1 - (j+3)/(2^{j+3}-2))`, which is `ring`.

### Lean Notes
This is the reflection across `Re s = 1/2` that `sigma`'s definition encodes by its case split.
Stating it unconditionally — including at `j = 0`, where the two branches meet — is what lets the
negative-index proofs throughout the file reduce to the nonnegative ones.

### References
tex: Equation `\ref{eq:sigmak}` (Equation 4), where `σ_{-k}` is defined so that this holds.

### Dependencies
**Depends on:** `sigma`.
**Used by:** `Kidx_set_bddBelow`, `chordIdx_set_bddBelow`, `sigma_lt_one`, `sigma_lt_succ`,
`sigma_pos`, `vCoeffPP_neg_eq`, `vCoeff_ratio_step`, `zeta_chord_bound_neg`,
`zeta_chord_bound_neg_tight`, `zeta_chord_bound_neg_tight_simple`. -/
private theorem sigma_neg_eq (j : ℕ) : sigma (-(j:ℤ)) = 1 - sigma (j:ℤ) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; norm_num [sigma]
  · unfold sigma
    rw [ite_eq_right (by omega : ¬ (0:ℤ) ≤ -(j:ℤ)), ite_eq_left (by positivity : (0:ℤ) ≤ (j:ℤ))]
    rw [show (-(-(j:ℤ))) = (j:ℤ) by ring]
    push_cast; ring

/-- **Mirror identity for `vCoeff`**: `v_{-j} = σ_j - 1/2 + v_j`, unconditional in `j : ℕ`.

### Summary of Proof
Case on whether `j = 0`; at `j = 0` both sides are `1/6` by `norm_num`. For `j ≥ 1` this is
exactly `vCoeff`'s own defining formula for negative indices, once the `if`-branches are
discharged and `-(-j)` is simplified to `j`.

### Lean Notes
Restated with the index written as `j` rather than `sigma (-j)`, which is the form the
negative-index chord proofs consume.

### References
tex: the display after Equation `\ref{eq:sigmak}` (Equation 4), which defines `v_{-k}` by this
formula.

### Dependencies
**Depends on:** `vCoeff`.
**Used by:** `vCoeff_le`, `vCoeff_nonneg`, `vCoeff_ratio_step`, `zeta_chord_bound_neg`,
`zeta_chord_bound_neg_tight`, `zeta_chord_bound_neg_tight_simple`. -/
private theorem vCoeff_neg_eq (j : ℕ) : vCoeff (-(j:ℤ)) = sigma (j:ℤ) - 1/2 + vCoeff (j:ℤ) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; norm_num [vCoeff, sigma]
  · unfold vCoeff
    rw [ite_eq_right (by omega : ¬ (0:ℤ) ≤ -(j:ℤ)), ite_eq_left (by positivity : (0:ℤ) ≤ (j:ℤ))]
    rw [show (-(-(j:ℤ))) = (j:ℤ) by ring]

/-- **Mirror identity for `vCoeffPP`**:
`v_{-j}'' = v_j'' + (1/2 - σ_j)log π`, unconditional in `j : ℕ`.

### Summary of Proof
Case on whether `j = 0`. For `j ≥ 1`, discharge the three `if`-branches (`-j` is neither
positive nor zero, `j` is positive), rewrite `sigma (-j)` by `sigma_neg_eq`, and `ring`.

### Lean Notes
The `j = 0` case is the delicate one, and it works for a reason worth recording: the identity
holds there **only because the correction term `(1/2 - σ_0)log π` vanishes**, `σ_0` being exactly
`1/2`. That sidesteps `vCoeffPP 0`'s special-cased value — `log 0.611`, not `log 1.546` — which
would otherwise make the two sides disagree.

### References
tex: the display after Equation `\ref{eq:sigmak}` (Equation 4) for the `k < 0` form; Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36) is where the `(σ-1/2)log π` correction comes from.

### Dependencies
**Depends on:** `sigma_neg_eq`, `vCoeffPP`.
**Used by:** `zeta_chord_bound_neg`, `zeta_chord_bound_neg_tight`,
`zeta_chord_bound_neg_tight_simple`. -/
private theorem vCoeffPP_neg_eq (j : ℕ) :
    vCoeffPP (-(j:ℤ)) = vCoeffPP (j:ℤ) + (1/2 - sigma (j:ℤ)) * Real.log Real.pi := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; norm_num [vCoeffPP, sigma]
  · unfold vCoeffPP
    rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(j:ℤ)), ite_eq_right (by omega : ¬ (-(j:ℤ) = 0)),
        ite_eq_left (by exact_mod_cast hj : (0:ℤ) < (j:ℤ)), sigma_neg_eq]
    ring

/-! ### Nonnegativity of the interpolated `log|t|` coefficient

`LittlewoodMethod.littlewood_mainterm` integrates `zeta_piecewise_bound` over a symmetric window
and uses the *concavity* of `log` to discard the resulting error — which requires the coefficient
of `log|t|` to be nonnegative. That coefficient is the chord between `vCoeff k` and
`vCoeff (k+1)`, so it suffices that `vCoeff` is nonnegative everywhere and that `sigma` is
increasing. -/

/-- **`vCoeff` is nonnegative at nonnegative indices.**

### Summary of Proof
In closed form `v_n = 1/(2^{n+3}-2)`, and `2^{n+3} ≥ 2³ = 8`, so the denominator is at least
`6 > 0`; a quotient of nonnegatives.

### References
No tex counterpart as a numbered claim — evident from the formula in the display after Equation
`\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `vCoeff`, `vCoeff_natCast`.
**Used by:** `vCoeff_nonneg`. -/
theorem vCoeff_natCast_nonneg (n : ℕ) : 0 ≤ vCoeff (n : ℤ) := by
  rw [vCoeff_natCast]
  have h8 : (8:ℝ) ≤ 2 ^ (n + 3) := by
    calc (8:ℝ) = 2 ^ (3:ℕ) := by norm_num
      _ ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact div_nonneg (by norm_num) (by linarith)

/-- **`vCoeff` is nonnegative at every index.**

### Summary of Proof
For `k ≥ 0` this is `vCoeff_natCast_nonneg`. For `k < 0`, write `k = -j` and use the mirror
formula `v_{-j} = σ_j - 1/2 + v_j`: both summands are nonnegative, since `σ_j ≥ 1/2` for `j ≥ 0`
(`sigma_natCast_mem`) and `v_j ≥ 0`.

### Lean Notes
This is the sign hypothesis that `chord_vCoeff_nonneg` — and through it
`LittlewoodMethod.littlewood_mainterm` — needs in order to apply concavity of `log`.

### References
No tex counterpart as a numbered claim; the source uses the nonnegativity silently.

### Dependencies
**Depends on:** `sigma_natCast_mem`, `vCoeff`, `vCoeff_natCast_nonneg`, `vCoeff_neg_eq`.
**Used by:** `bCoeff_pos`, `chord_vCoeff_nonneg`, `vCoeff_lt_succ`. -/
theorem vCoeff_nonneg (k : ℤ) : 0 ≤ vCoeff k := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with n
    exact vCoeff_natCast_nonneg n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [vCoeff_neg_eq]
    linarith [(sigma_natCast_mem j).1, vCoeff_natCast_nonneg j]

/-- **`σ_k < 1` at every index.**

### Summary of Proof
For `k ≥ 0` this is the upper half of `sigma_natCast_mem`. For `k < 0`, the mirror identity gives
`σ_{-j} = 1 - σ_j ≤ 1 - 1/2 = 1/2 < 1`, using `σ_j ≥ 1/2`.

### Lean Notes
Used pervasively: `1 - σ_k > 0` is what makes `θ_{k,r} = arcsin((1-σ_k)/r)` well defined and
positive, and what keeps the Jensen disk arguments non-degenerate.

### References
No tex counterpart as a numbered claim — the `σ_k` are lines inside the critical strip by
construction, Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_natCast_mem`, `sigma_neg_eq`.
**Used by:** `chordIdx_eq`, `sigma_tendsto_one`, `sin_theta_eq`, `theta_nonneg`, `vCoeff_le`,
`vCoeff_lt_succ`, `vRatio_strictAnti`, `JensenBounds.arc_pointwise_bound_sin`, and 7 further call
sites. -/
theorem sigma_lt_one (k : ℤ) : sigma k < 1 := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with n
    exact (sigma_natCast_mem n).2
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [sigma_neg_eq]
    linarith [(sigma_natCast_mem j).1]

/-- **`0 < σ_k` at every index.**

### Summary of Proof
For `k ≥ 0` this follows from `σ_k ≥ 1/2` (`sigma_natCast_mem`). For `k < 0`, the mirror identity
gives `σ_{-j} = 1 - σ_j > 0`, using `σ_j < 1`.

### References
No tex counterpart as a numbered claim — the `σ_k` lie in the critical strip by construction,
Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_natCast_mem`, `sigma_neg_eq`.
**Used by:** `bCoeff_pos`, `chordIdx_eq`, `littlewoodshort`, `littlewoodshort_tight`. -/
theorem sigma_pos (k : ℤ) : 0 < sigma k := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with n
    linarith [(sigma_natCast_mem n).1]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [sigma_neg_eq]
    linarith [(sigma_natCast_mem j).2]

/-- **`σ_k < σ_{k+1}` for every `k : ℤ`** — `sigma` is strictly increasing.

### Summary of Proof
For `k ≥ 0` this is `sigma_strictMono_succ`. For `k < 0`, write `k = -(j+1)`; the mirror identity
turns the claim into `1 - σ_{j+1} < 1 - σ_j`, i.e. into `σ_j < σ_{j+1}`, which is the
nonnegative case again.

### Lean Notes
This is the fact that makes `[σ_k, σ_{k+1}]` — and not the other order — the chord interval, as
the sentence after Equation `\ref{eq:mk}` (Equation 5) also has it.

### References
No tex counterpart as a numbered claim; implicit in Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_neg_eq`, `sigma_strictMono_succ`.
**Used by:** `c1_term_le`, `c1_term_nonneg`, `chordA_star`, `chord_mem_Icc`, `chord_vCoeff_le`,
`chord_vCoeff_nonneg`, `mCoeff_add_bCoeff_neg`, `mCoeff_neg`, `sigma_strictMono`,
`sin_window_of_mem_chord`, `theta_antitone_succ`, `vCoeff_lt_succ`. -/
theorem sigma_lt_succ (k : ℤ) : sigma k < sigma (k + 1) := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with n
    exact sigma_strictMono_succ n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -((j : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    have e1 : sigma (-((j : ℤ) + 1)) = 1 - sigma ((j : ℤ) + 1) := by
      have h := sigma_neg_eq (j + 1)
      push_cast at h
      exact h
    have e2 : sigma (-((j : ℤ) + 1) + 1) = 1 - sigma (j : ℤ) := by
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) by ring, sigma_neg_eq]
    rw [e1, e2]
    linarith [sigma_strictMono_succ j]

/-- **The chord `mCoeff k · σ + bCoeff k` is nonnegative on `[σ_k, σ_{k+1}]`.**

### Summary of Proof
The chord is the affine function through `(σ_k, v_k)` and `(σ_{k+1}, v_{k+1})`. Writing
`l := (σ - σ_k)/(σ_{k+1} - σ_k) ∈ [0,1]` for the normalised position in the interval, an explicit
computation (`field_simp; ring`) identifies the chord with the convex combination
`(1-l)·v_k + l·v_{k+1}`. Both `v_k` and `v_{k+1}` are nonnegative by `vCoeff_nonneg`, so the
combination is too.

### Lean Notes
This is the sign hypothesis `LittlewoodMethod.littlewood_mainterm` needs in order to use the
concavity of `log`: it integrates `zeta_piecewise_bound` over a symmetric window and discards the
resulting error, which is only valid when the coefficient of `log|t|` is nonnegative.

### References
No tex counterpart as a numbered claim — the source uses the nonnegativity silently when
integrating.

### Dependencies
**Depends on:** `bCoeff`, `mCoeff`, `sigma_lt_succ`, `vCoeff`, `vCoeff_nonneg`.
**Used by:** `c1_boundary_nonneg`, `c1_term_nonneg`, `ConstantSigns.A1_nonneg`,
`JensenBounds.arc_pointwise_le_maj_sin`, `JensenBounds.arc_pointwise_le_maj_sin_tight`,
`JensenBounds.chordW_nonneg`, `LittlewoodMethod.littlewood_mainterm`,
`LittlewoodMethod.littlewood_mainterm_tight`. -/
theorem chord_vCoeff_nonneg {k : ℤ} {σ : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ ≤ sigma (k + 1)) :
    0 ≤ mCoeff k * σ + bCoeff k := by
  have hlt := sigma_lt_succ k
  have hd : (0:ℝ) < sigma (k + 1) - sigma k := by linarith
  have hne : sigma k - sigma (k + 1) ≠ 0 := by intro hc; linarith
  set l : ℝ := (σ - sigma k) / (sigma (k + 1) - sigma k) with hl_def
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
  have hl1 : l ≤ 1 := by rw [hl_def, div_le_one hd]; linarith
  have hkey : mCoeff k * σ + bCoeff k = (1 - l) * vCoeff k + l * vCoeff (k + 1) := by
    rw [hl_def]
    simp only [bCoeff, mCoeff]
    field_simp
    ring
  rw [hkey]
  nlinarith [vCoeff_nonneg k, vCoeff_nonneg (k + 1)]

/-- **`‖ζ(σ+it)‖` depends only on `|t|`.**

### Summary of Proof
Schwarz reflection. For `t ≥ 0` there is nothing to prove. For `t ≤ 0`, `σ + |t|i = σ - ti` is
the complex conjugate of `σ + ti`; `riemannZeta_conj` gives `ζ(conj s) = conj (ζ s)`, and
`RCLike.norm_conj` says conjugation preserves the norm.

### Lean Notes
This is what lets `zeta_piecewise_bound` reduce to the `t > 0` case throughout, so that the
underlying interpolation bounds — which are stated for positive `t` — can be applied.

### References
No tex counterpart — the source writes `log|t|` throughout and treats the reflection as evident.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_piecewise_bound`, `zeta_piecewise_bound_tight_simple`. -/
private theorem riemannZeta_norm_abs_im (σ t : ℝ) :
    ‖riemannZeta (σ + t * Complex.I)‖ = ‖riemannZeta (σ + |t| * Complex.I)‖ := by
  rcases le_total (0:ℝ) t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    have hconj : (σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I = conj ((σ:ℂ) + (t:ℂ) * Complex.I) := by
      simp
    rw [hconj, riemannZeta_conj, RCLike.norm_conj]

/-- **`zeta_piecewise_bound`, closed-interval nonnegative-index case.** For `σ ∈ [σ_m, σ_{m+1}]`
and `t > 10¹²`, `log‖ζ(σ+it)‖` is at most the three chords plus `3/t`.

### Summary of Proof
Reduces to `BackgroundZetaBounds.interpolated_bound_1b` (at `m = 0`: the chord from the
Hiary–Revers half-line bound at `σ_0 = 1/2`, which is where `vCoeffPP 0 = log 0.611` comes from,
to Yang's bound at `σ_1 = 5/7`) or `interpolated_bound_2` (at `m ≥ 1`, instantiated at
`k := m+3`), by a **two-point matching** argument.

`mCoeff m` and `bCoeff m` are *defined* as the unique affine function through `(σ_m, v_m)` and
`(σ_{m+1}, v_{m+1})`. The displayed coefficient of `interpolated_bound_2` is *also* affine in `σ`,
and agrees with `v` at those same two points — closed-form algebra in `x := 2^m`. An affine
function is determined by its values at two distinct points, so the two coincide identically,
with no need to verify the chord formula term by term.

### Lean Notes
The `3/t` slack is exactly `interpolated_bound_1b`/`_2`'s own `O^*(1/T)` Phragmén–Lindelöf
correction, taken at `T := t`, using that `t` is already the centre of its own trivial
`[t-1,t+1]` window.

The logs are written bare (`Real.log t`, hypothesis `10¹² < t`) rather than with bars. Callers
instantiate at `t := |t|`; had the conclusion carried bars it would produce `log ‖|t|‖`, a
syntactically distinct atom that `linarith` cannot match against the goal.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), cases (1b) and (2); the chord
definitions of Equations `\ref{eq:mk}`, `\ref{eq:mkp}`, `\ref{eq:mkpp}` (Equations 5–7).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `interpolated_bound_1b`,
`interpolated_bound_2`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma_natCast`, `vCoeff`, `vCoeffP`,
`vCoeffPP`, `vCoeff_natCast`.
**Used by:** `zeta_chord_bound_neg`, `zeta_piecewise_bound`. -/
private theorem zeta_chord_bound_nonneg (m : ℕ) {σ t : ℝ}
    (hσ : sigma (m:ℤ) ≤ σ) (hσ' : σ ≤ sigma ((m:ℤ)+1)) (ht : (10:ℝ) ^ (12:ℕ) < t) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (m:ℤ) * σ + bCoeff (m:ℤ)) * Real.log t
          + (mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ)) * Real.log (Real.log t)
          + (mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ)) + 3 / t := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero] at hσ hσ' ⊢
    have hσ0 : σ ∈ Set.Icc (1/2 : ℝ) (5/7) := by
      constructor
      · have : sigma 0 = 1/2 := by norm_num [sigma]
        linarith [this ▸ hσ]
      · have : sigma 1 = 5/7 := by norm_num [sigma]
        linarith [this ▸ hσ']
    have ht' : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have hT : (0:ℝ) ≤ t := by nlinarith [ht]
    have habs : |t| = t := abs_of_nonneg hT
    have key := interpolated_bound_1b ht ht' hσ0
    rw [habs] at key
    have heq1 : mCoeff 0 * σ + bCoeff 0 = 4 * (1 - σ) / 9 - 1 / 18 := by
      norm_num [mCoeff, bCoeff, vCoeff, sigma]; ring
    have heq2 : mCoeffP 0 * σ + bCoeffP 0 = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have heq3 : mCoeffPP 0 * σ + bCoeffPP 0
        = 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 := by
      norm_num [mCoeffPP, bCoeffPP, vCoeffPP, sigma]; ring
    rw [heq1, heq2, heq3]
    linarith [key]
  · have hs0 := sigma_natCast m
    have hs1 := sigma_natCast (m+1)
    have hv0 := vCoeff_natCast m
    have hv1 := vCoeff_natCast (m+1)
    push_cast at hs1 hv1
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1 hv1 hσ'
    have e3 : (2:ℝ)^(m+3) = 2^m*8 := by rw [pow_add]; ring
    have e4 : (2:ℝ)^(m+1+3) = 2^m*16 := by rw [show m+1+3=m+4 by omega, pow_add]; ring
    rw [e3] at hs0 hv0
    rw [e4] at hs1 hv1
    set x := (2:ℝ)^m with hx
    have hxge : (2:ℝ) ≤ x := by
      rw [hx]; calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^m := by apply pow_le_pow_right₀ (by norm_num); exact hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hd0 : x*8-2 > 0 := by linarith
    have hd1 : x*16-2 > 0 := by linarith
    have hsne : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := by
      rw [hs0, show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1]
      intro heq
      have : (↑m + 3) / (x * 8 - 2) = (↑m + 1 + 3) / (x * 16 - 2) := by linarith
      rw [div_eq_div_iff hd0.ne' hd1.ne'] at this
      nlinarith
    have hpt0 : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by
      unfold bCoeff; ring
    have hcross : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff
      rw [div_mul_cancel₀]
      exact sub_ne_zero.mpr hsne
    have hpt1 : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0, hcross, expand]
    have hzpow : (2:ℝ)^(1 - ((m+3:ℕ):ℤ)) = ((2:ℝ)^(m+2))⁻¹ := by
      have hcast : (1 - ((m+3:ℕ):ℤ) : ℤ) = -((m+2:ℕ):ℤ) := by push_cast; ring
      rw [hcast, zpow_neg, zpow_natCast]
    have e2 : (2:ℝ)^(m+2) = 2^m*4 := by rw [pow_add]; ring
    have hd2 : (m:ℝ)+2+x*4 > 0 := by nlinarith
    have hd3 : x*8*((m:ℝ)+2)+2 > 0 := by nlinarith
    have hA0 : (1 - sigma (m:ℤ)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff (m:ℤ) := by
      rw [hs0, hv0, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    have hA1 : (1 - sigma ((m:ℤ)+1)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff ((m:ℤ)+1) := by
      rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1, hv1, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    set D1 : ℝ := ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) with hD1
    set D2 : ℝ := 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 with hD2
    have hmC_eq : mCoeff (m:ℤ) = -(1/D1) := by
      have key : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = 0 := by
        have expand : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
            = mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
              + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 := by ring
        rw [expand, hcross]
        have hA_diff :
            (vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1)) + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 = 0 := by
          rw [← hA0, ← hA1]; ring
        linarith [hA_diff]
      rcases mul_eq_zero.mp key with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hsne
    have hbC_eq : bCoeff (m:ℤ) = 1/D1 - 1/D2 := by
      rw [hmC_eq] at hpt0
      rw [← hA0] at hpt0
      linear_combination hpt0
    have hmPeq : mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ) = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have hmPPeq : mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ) = Real.log 1.546 := by
      have h1 : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
      have h2 : (0:ℤ) < (m:ℤ)+1 := by linarith
      have hmPP : mCoeffPP (m:ℤ) = 0 := by
        unfold mCoeffPP vCoeffPP
        rw [ite_eq_left h1, ite_eq_left h2]; ring
      rw [hmPP]
      unfold bCoeffPP vCoeffPP
      rw [ite_eq_left h1, hmPP]; ring
    have hmCeq : mCoeff (m:ℤ) * σ + bCoeff (m:ℤ) = (1 - σ) / D1 - 1 / D2 := by
      rw [hmC_eq, hbC_eq]; ring
    rw [hmCeq, hmPeq, hmPPeq]
    have hs0' := sigma_natCast m
    have hs1' := sigma_natCast (m+1)
    push_cast at hs1'
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1'
    have key := interpolated_bound_2 (k := m+3) (by omega) ht
      (show t ∈ Set.Icc (t-1) (t+1) from ⟨by linarith, by linarith⟩)
      (show σ ∈ Set.Icc (1 - ((m+3:ℕ):ℝ)/(2^(m+3:ℕ)-2))
          (1 - (((m+3:ℕ):ℝ)+1)/(2^((m+3:ℕ)+1)-2)) from by
        constructor
        · rw [show ((m+3:ℕ):ℝ) = (m:ℝ)+3 by push_cast; ring, ← hs0']; exact hσ
        · rw [show ((m+3:ℕ)+1) = m+4 by omega,
              show (((m+3:ℕ):ℝ)+1) = ((m:ℝ)+1+3) by push_cast; ring,
              show m+4 = m+1+3 by omega]
          rw [← hs1']; exact hσ')
    have hT : (0:ℝ) ≤ t := by nlinarith [ht]
    have habs : |t| = t := abs_of_nonneg hT
    rw [habs] at key
    have hDeq : ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) = D1 := by rw [hD1]
    have hD2eq : 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 = D2 := by rw [hD2]
    rw [hDeq, hD2eq] at key
    linarith [key]

/-- **Tight version of `zeta_chord_bound_nonneg`**, with an `O(1/t²)` error in place of the
crude `3/t`.

### Summary of Proof
Identical two-point matching to `zeta_chord_bound_nonneg`, but drawing on
`BackgroundZetaBounds.interpolated_bound_1b_tight`/`interpolated_bound_2_tight` — Proposition
`\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)` bounds — instead of the
crude `O(1/t)` forms.

### Lean Notes
**No artificial `T`-window** is needed here at all: the tight bounds are already pointwise in
`t`, so this drops the crude proof's window-conversion boilerplate entirely.

The result is genuinely `σ`-dependent, not collapsed to a constant (unlike `_tight_simple`). The
`m ≥ 1` branch's own numerator uses `Q = e`, strictly smaller than `m = 0`'s `Q = 16` since
`4Q²+8Q` increases in `Q > 0`, so it is loosened up to the `Q = 16` form to give one uniform
closed-form statement across every `m`.

Threshold `t > 8` uniformly, the stricter of the two branches' own — `interpolated_bound_1b_tight`
needs `t > 8`, `interpolated_bound_2_tight` only `t > 3`.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), the tight forms of cases (1b) and
(2).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `interpolated_bound_1b_tight`,
`interpolated_bound_2_tight`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma_natCast`, `vCoeff`,
`vCoeffP`, `vCoeffPP`, `vCoeff_natCast`.
**Used by:** `zeta_chord_bound_neg_tight`. -/
theorem zeta_chord_bound_nonneg_tight (m : ℕ) {σ t : ℝ}
    (hσ : sigma (m:ℤ) ≤ σ) (hσ' : σ ≤ sigma ((m:ℤ)+1)) (ht : (8:ℝ) < t) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (m:ℤ) * σ + bCoeff (m:ℤ)) * Real.log t
          + (mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ)) * Real.log (Real.log t)
          + (mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ))
          + (3 / (2 * t ^ 2)
              + (2 * ((16 + σ) ^ 2 + (18 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                  / (8 * t ^ 2 * Real.log t)) := by
  have hT : (0:ℝ) ≤ t := by linarith
  have habs : |t| = t := abs_of_nonneg hT
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero] at hσ hσ' ⊢
    have hσ0 : σ ∈ Set.Icc (1/2 : ℝ) (5/7) := by
      constructor
      · have : sigma 0 = 1/2 := by norm_num [sigma]
        linarith [this ▸ hσ]
      · have : sigma 1 = 5/7 := by norm_num [sigma]
        linarith [this ▸ hσ']
    have key := interpolated_bound_1b_tight (t := t) (by rwa [habs]) hσ0
    rw [habs] at key
    have heq1 : mCoeff 0 * σ + bCoeff 0 = 4 * (1 - σ) / 9 - 1 / 18 := by
      norm_num [mCoeff, bCoeff, vCoeff, sigma]; ring
    have heq2 : mCoeffP 0 * σ + bCoeffP 0 = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have heq3 : mCoeffPP 0 * σ + bCoeffPP 0
        = 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 := by
      norm_num [mCoeffPP, bCoeffPP, vCoeffPP, sigma]; ring
    rw [heq1, heq2, heq3]
    linarith [key]
  · have hs0 := sigma_natCast m
    have hs1 := sigma_natCast (m+1)
    have hv0 := vCoeff_natCast m
    have hv1 := vCoeff_natCast (m+1)
    push_cast at hs1 hv1
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1 hv1 hσ'
    have e3 : (2:ℝ)^(m+3) = 2^m*8 := by rw [pow_add]; ring
    have e4 : (2:ℝ)^(m+1+3) = 2^m*16 := by rw [show m+1+3=m+4 by omega, pow_add]; ring
    rw [e3] at hs0 hv0
    rw [e4] at hs1 hv1
    set x := (2:ℝ)^m with hx
    have hxge : (2:ℝ) ≤ x := by
      rw [hx]; calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^m := by apply pow_le_pow_right₀ (by norm_num); exact hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hd0 : x*8-2 > 0 := by linarith
    have hd1 : x*16-2 > 0 := by linarith
    have hsne : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := by
      rw [hs0, show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1]
      intro heq
      have : (↑m + 3) / (x * 8 - 2) = (↑m + 1 + 3) / (x * 16 - 2) := by linarith
      rw [div_eq_div_iff hd0.ne' hd1.ne'] at this
      nlinarith
    have hpt0 : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by
      unfold bCoeff; ring
    have hcross : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff
      rw [div_mul_cancel₀]
      exact sub_ne_zero.mpr hsne
    have hpt1 : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0, hcross, expand]
    have hzpow : (2:ℝ)^(1 - ((m+3:ℕ):ℤ)) = ((2:ℝ)^(m+2))⁻¹ := by
      have hcast : (1 - ((m+3:ℕ):ℤ) : ℤ) = -((m+2:ℕ):ℤ) := by push_cast; ring
      rw [hcast, zpow_neg, zpow_natCast]
    have e2 : (2:ℝ)^(m+2) = 2^m*4 := by rw [pow_add]; ring
    have hd2 : (m:ℝ)+2+x*4 > 0 := by nlinarith
    have hd3 : x*8*((m:ℝ)+2)+2 > 0 := by nlinarith
    have hA0 : (1 - sigma (m:ℤ)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff (m:ℤ) := by
      rw [hs0, hv0, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    have hA1 : (1 - sigma ((m:ℤ)+1)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff ((m:ℤ)+1) := by
      rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1, hv1, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    set D1 : ℝ := ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) with hD1
    set D2 : ℝ := 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 with hD2
    have hmC_eq : mCoeff (m:ℤ) = -(1/D1) := by
      have key : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = 0 := by
        have expand : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
            = mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
              + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 := by ring
        rw [expand, hcross]
        have hA_diff :
            (vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1)) + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 = 0 := by
          rw [← hA0, ← hA1]; ring
        linarith [hA_diff]
      rcases mul_eq_zero.mp key with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hsne
    have hbC_eq : bCoeff (m:ℤ) = 1/D1 - 1/D2 := by
      rw [hmC_eq] at hpt0
      rw [← hA0] at hpt0
      linear_combination hpt0
    have hmPeq : mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ) = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have hmPPeq : mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ) = Real.log 1.546 := by
      have h1 : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
      have h2 : (0:ℤ) < (m:ℤ)+1 := by linarith
      have hmPP : mCoeffPP (m:ℤ) = 0 := by
        unfold mCoeffPP vCoeffPP
        rw [ite_eq_left h1, ite_eq_left h2]; ring
      rw [hmPP]
      unfold bCoeffPP vCoeffPP
      rw [ite_eq_left h1, hmPP]; ring
    have hmCeq : mCoeff (m:ℤ) * σ + bCoeff (m:ℤ) = (1 - σ) / D1 - 1 / D2 := by
      rw [hmC_eq, hbC_eq]; ring
    rw [hmCeq, hmPeq, hmPPeq]
    have hs0' := sigma_natCast m
    have hs1' := sigma_natCast (m+1)
    push_cast at hs1'
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1'
    have key := interpolated_bound_2_tight (k := m+3) (by omega) (by rw [habs]; linarith)
      (show σ ∈ Set.Icc (1 - ((m+3:ℕ):ℝ)/(2^(m+3:ℕ)-2))
          (1 - (((m+3:ℕ):ℝ)+1)/(2^((m+3:ℕ)+1)-2)) from by
        constructor
        · rw [show ((m+3:ℕ):ℝ) = (m:ℝ)+3 by push_cast; ring, ← hs0']; exact hσ
        · rw [show ((m+3:ℕ)+1) = m+4 by omega,
              show (((m+3:ℕ):ℝ)+1) = ((m:ℝ)+1+3) by push_cast; ring,
              show m+4 = m+1+3 by omega]
          rw [← hs1']; exact hσ')
    rw [habs] at key
    have hDeq : ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) = D1 := by rw [hD1]
    have hD2eq : 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 = D2 := by rw [hD2]
    rw [hDeq, hD2eq] at key
    have ht2pos : (0:ℝ) < t ^ 2 := by positivity
    have hlogtpos : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
    have hden : (0:ℝ) < 8 * t ^ 2 * Real.log t := mul_pos (mul_pos (by norm_num) ht2pos) hlogtpos
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hnumle : 2 * ((Real.exp 1 + σ) ^ 2 + (Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2
        ≤ 2 * ((16 + σ) ^ 2 + (18 - σ) ^ 2) + |2 - 2 * σ| ^ 2 := by
      -- both sides are `4(X+1)² + 8(1-σ)²` (the identity used throughout
      -- `BackgroundZetaBounds`), with `X = e` and `X = 16`, so the `σ` parts cancel outright and
      -- only `(e+1)² ≤ 289` is left.  `only` keeps the surrounding two-point-matching algebra
      -- out of the tableau; the one square nlinarith still forms is `he * he`.
      nlinarith only [he, he0]
    have hfracle : (2 * ((Real.exp 1 + σ) ^ 2 + (Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
        / (8 * t ^ 2 * Real.log t)
        ≤ (2 * ((16 + σ) ^ 2 + (18 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * t ^ 2 * Real.log t) := by
      -- after the cross-multiplication this is exactly `A·D ≤ B·D` from `A ≤ B` and `0 < D`
      rw [div_le_div_iff₀ hden hden]
      exact mul_le_mul_of_nonneg_right hnumle hden.le
    linarith [key, hfracle]

/-- **Tight, simplified version of `zeta_chord_bound_nonneg`**, with the `σ`-dependent numerator
collapsed to the constant `1158`.

### Summary of Proof
As `zeta_chord_bound_nonneg_tight`, but drawing on
`interpolated_bound_1b_tight_simple`/`interpolated_bound_2_tight_simple`, whose numerators are
already `σ`-independent. The uniform constant is the larger of the two branches' own simplified
numerators — `1158` for `m = 0` and `56` for `m ≥ 1`, and `56 ≤ 1158`.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), cases (1b) and (2).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `interpolated_bound_1b_tight_simple`,
`interpolated_bound_2_tight_simple`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma_natCast`, `vCoeff`,
`vCoeffP`, `vCoeffPP`, `vCoeff_natCast`.
**Used by:** `zeta_chord_bound_neg_tight_simple`, `zeta_piecewise_bound_tight_simple`. -/
theorem zeta_chord_bound_nonneg_tight_simple (m : ℕ) {σ t : ℝ}
    (hσ : sigma (m:ℤ) ≤ σ) (hσ' : σ ≤ sigma ((m:ℤ)+1)) (ht : (8:ℝ) < t) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (m:ℤ) * σ + bCoeff (m:ℤ)) * Real.log t
          + (mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ)) * Real.log (Real.log t)
          + (mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ))
          + (3 / (2 * t ^ 2) + 1158 / (8 * t ^ 2 * Real.log t)) := by
  have hT : (0:ℝ) ≤ t := by linarith
  have habs : |t| = t := abs_of_nonneg hT
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero] at hσ hσ' ⊢
    have hσ0 : σ ∈ Set.Icc (1/2 : ℝ) (5/7) := by
      constructor
      · have : sigma 0 = 1/2 := by norm_num [sigma]
        linarith [this ▸ hσ]
      · have : sigma 1 = 5/7 := by norm_num [sigma]
        linarith [this ▸ hσ']
    have key := interpolated_bound_1b_tight_simple (t := t) (by rwa [habs]) hσ0
    rw [habs] at key
    have heq1 : mCoeff 0 * σ + bCoeff 0 = 4 * (1 - σ) / 9 - 1 / 18 := by
      norm_num [mCoeff, bCoeff, vCoeff, sigma]; ring
    have heq2 : mCoeffP 0 * σ + bCoeffP 0 = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have heq3 : mCoeffPP 0 * σ + bCoeffPP 0
        = 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 := by
      norm_num [mCoeffPP, bCoeffPP, vCoeffPP, sigma]; ring
    rw [heq1, heq2, heq3]
    linarith [key]
  · have hs0 := sigma_natCast m
    have hs1 := sigma_natCast (m+1)
    have hv0 := vCoeff_natCast m
    have hv1 := vCoeff_natCast (m+1)
    push_cast at hs1 hv1
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1 hv1 hσ'
    have e3 : (2:ℝ)^(m+3) = 2^m*8 := by rw [pow_add]; ring
    have e4 : (2:ℝ)^(m+1+3) = 2^m*16 := by rw [show m+1+3=m+4 by omega, pow_add]; ring
    rw [e3] at hs0 hv0
    rw [e4] at hs1 hv1
    set x := (2:ℝ)^m with hx
    have hxge : (2:ℝ) ≤ x := by
      rw [hx]; calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^m := by apply pow_le_pow_right₀ (by norm_num); exact hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hd0 : x*8-2 > 0 := by linarith
    have hd1 : x*16-2 > 0 := by linarith
    have hsne : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := by
      rw [hs0, show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1]
      intro heq
      have : (↑m + 3) / (x * 8 - 2) = (↑m + 1 + 3) / (x * 16 - 2) := by linarith
      rw [div_eq_div_iff hd0.ne' hd1.ne'] at this
      nlinarith
    have hpt0 : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by
      unfold bCoeff; ring
    have hcross : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff
      rw [div_mul_cancel₀]
      exact sub_ne_zero.mpr hsne
    have hpt1 : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0, hcross, expand]
    have hzpow : (2:ℝ)^(1 - ((m+3:ℕ):ℤ)) = ((2:ℝ)^(m+2))⁻¹ := by
      have hcast : (1 - ((m+3:ℕ):ℤ) : ℤ) = -((m+2:ℕ):ℤ) := by push_cast; ring
      rw [hcast, zpow_neg, zpow_natCast]
    have e2 : (2:ℝ)^(m+2) = 2^m*4 := by rw [pow_add]; ring
    have hd2 : (m:ℝ)+2+x*4 > 0 := by nlinarith
    have hd3 : x*8*((m:ℝ)+2)+2 > 0 := by nlinarith
    have hA0 : (1 - sigma (m:ℤ)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff (m:ℤ) := by
      rw [hs0, hv0, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    have hA1 : (1 - sigma ((m:ℤ)+1)) / (((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ))
          - 1 / (2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2) = vCoeff ((m:ℤ)+1) := by
      rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring, hs1, hv1, hzpow, e2, e3]
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    set D1 : ℝ := ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) with hD1
    set D2 : ℝ := 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 with hD2
    have hmC_eq : mCoeff (m:ℤ) = -(1/D1) := by
      have key : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = 0 := by
        have expand : (mCoeff (m:ℤ) + 1/D1) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
            = mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
              + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 := by ring
        rw [expand, hcross]
        have hA_diff :
            (vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1)) + (sigma (m:ℤ) - sigma ((m:ℤ)+1))/D1 = 0 := by
          rw [← hA0, ← hA1]; ring
        linarith [hA_diff]
      rcases mul_eq_zero.mp key with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hsne
    have hbC_eq : bCoeff (m:ℤ) = 1/D1 - 1/D2 := by
      rw [hmC_eq] at hpt0
      rw [← hA0] at hpt0
      linear_combination hpt0
    have hmPeq : mCoeffP (m:ℤ) * σ + bCoeffP (m:ℤ) = 1 := by
      norm_num [mCoeffP, bCoeffP, vCoeffP]
    have hmPPeq : mCoeffPP (m:ℤ) * σ + bCoeffPP (m:ℤ) = Real.log 1.546 := by
      have h1 : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
      have h2 : (0:ℤ) < (m:ℤ)+1 := by linarith
      have hmPP : mCoeffPP (m:ℤ) = 0 := by
        unfold mCoeffPP vCoeffPP
        rw [ite_eq_left h1, ite_eq_left h2]; ring
      rw [hmPP]
      unfold bCoeffPP vCoeffPP
      rw [ite_eq_left h1, hmPP]; ring
    have hmCeq : mCoeff (m:ℤ) * σ + bCoeff (m:ℤ) = (1 - σ) / D1 - 1 / D2 := by
      rw [hmC_eq, hbC_eq]; ring
    rw [hmCeq, hmPeq, hmPPeq]
    have hs0' := sigma_natCast m
    have hs1' := sigma_natCast (m+1)
    push_cast at hs1'
    rw [show ((m:ℤ)+1) = ((m+1:ℤ)) by ring] at hs1'
    have key := interpolated_bound_2_tight_simple (k := m+3) (by omega) (by rw [habs]; linarith)
      (show σ ∈ Set.Icc (1 - ((m+3:ℕ):ℝ)/(2^(m+3:ℕ)-2))
          (1 - (((m+3:ℕ):ℝ)+1)/(2^((m+3:ℕ)+1)-2)) from by
        constructor
        · rw [show ((m+3:ℕ):ℝ) = (m:ℝ)+3 by push_cast; ring, ← hs0']; exact hσ
        · rw [show ((m+3:ℕ)+1) = m+4 by omega,
              show (((m+3:ℕ):ℝ)+1) = ((m:ℝ)+1+3) by push_cast; ring,
              show m+4 = m+1+3 by omega]
          rw [← hs1']; exact hσ')
    rw [habs] at key
    have hDeq : ((m+3:ℕ):ℝ) - 1 + 2 ^ (1 - ((m+3:ℕ):ℤ) : ℤ) = D1 := by rw [hD1]
    have hD2eq : 2 ^ (m+3:ℕ) * (((m+3:ℕ):ℝ) - 1) + 2 = D2 := by rw [hD2]
    rw [hDeq, hD2eq] at key
    have ht2pos : (0:ℝ) < t ^ 2 := by positivity
    have hlogtpos : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
    have hden : (0:ℝ) < 8 * t ^ 2 * Real.log t := mul_pos (mul_pos (by norm_num) ht2pos) hlogtpos
    have hloosen : (56:ℝ) / (8 * t ^ 2 * Real.log t) ≤ 1158 / (8 * t ^ 2 * Real.log t) := by
      -- after the cross-multiplication this is `56·D ≤ 1158·D` from `0 < D`
      rw [div_le_div_iff₀ hden hden]
      exact mul_le_mul_of_nonneg_right (by norm_num) hden.le
    linarith [key, hloosen]

/-- **Tight version of `zeta_chord_bound_neg`**, the negative-index case with an `O(1/t²)`
error.

### Summary of Proof
The same reflection as `zeta_chord_bound_neg`, but drawing on Proposition
`\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)` bounds throughout — via
`zeta_chord_bound_nonneg_tight` at the mirrored point, and
`BackgroundZetaBounds.zetalessthanhalf_upper`, which was already `O(1/t²)`.

### Lean Notes
The two error terms combine: `zeta_chord_bound_nonneg_tight`'s `3/(2t²) + NUM/(8t²log t)` plus
the reflection's `1/(2t²)` gives `2/t² + NUM/(8t²log t)`. Genuinely `σ`-dependent, through the
mirrored point `1-σ`, rather than collapsed to a constant.

Threshold `t > 10`, matching `zetalessthanhalf_upper`'s own — the stricter of the two pieces'
`t > 10` and `t > 8`.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), tight forms; Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36) for the reflection.

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`,
`sigma_natCast_mem`, `sigma_neg_eq`, `sigma_strictMono_succ`, `two_mul_add_eight_le_pow`,
`vCoeff`, `vCoeffP`, `vCoeffPP`, `vCoeffPP_neg_eq`, `vCoeff_neg_eq`,
`zeta_chord_bound_nonneg_tight`, `zetalessthanhalf_upper`.
**Used by:** none — the collapsed `_simple` variant is what the development consumes. Kept
because it records the exact, per-branch `σ`-dependent bound that `_simple` throws away. -/
theorem zeta_chord_bound_neg_tight (n : ℕ) (hn : 1 ≤ n) {σ t : ℝ}
    (hσ : sigma (-(n:ℤ)) ≤ σ) (hσ' : σ ≤ sigma (-(n:ℤ)+1)) (ht : (10:ℝ) < t)
    (hz : riemannZeta ((1:ℂ) - σ + t * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (-(n:ℤ)) * σ + bCoeff (-(n:ℤ))) * Real.log t
          + (mCoeffP (-(n:ℤ)) * σ + bCoeffP (-(n:ℤ))) * Real.log (Real.log t)
          + (mCoeffPP (-(n:ℤ)) * σ + bCoeffPP (-(n:ℤ)))
          + (2 / t ^ 2
              + (2 * ((16 + (1 - σ)) ^ 2 + (18 - (1 - σ)) ^ 2) + |2 - 2 * (1 - σ)| ^ 2)
                  / (8 * t ^ 2 * Real.log t)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m+1 := ⟨n-1, by omega⟩
  subst hm
  have hnm : (-(((m:ℕ)+1:ℕ):ℤ)+1) = -(m:ℤ) := by push_cast; ring
  rw [hnm] at hσ'
  have hτ0 : sigma (m:ℤ) ≤ 1 - σ := by
    rw [sigma_neg_eq] at hσ'; linarith
  have hτ1 : 1 - σ ≤ sigma ((m:ℤ)+1) := by
    have hσ2 := hσ
    rw [sigma_neg_eq] at hσ2
    rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hσ2
    linarith
  have hnonneg := zeta_chord_bound_nonneg_tight m hτ0 hτ1 (by linarith : (8:ℝ) < t)
  rw [show (((1-σ:ℝ)):ℂ) = (1:ℂ) - (σ:ℂ) by push_cast; ring] at hnonneg
  set C : ℝ := (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) * Real.log t
      + (mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ)) * Real.log (Real.log t)
      + (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) with hC_def
  -- σ ∈ [0, 1/2]
  have hσ_lb : (0:ℝ) ≤ σ := by
    have h1 : (0:ℝ) < sigma (-(((m+1:ℕ)):ℤ)) := by
      unfold sigma
      rw [ite_eq_right (by omega : ¬(0:ℤ) ≤ -(((m+1:ℕ)):ℤ))]
      rw [show (-(-(((m+1:ℕ)):ℤ))) = (((m+1:ℕ)):ℤ) by ring]
      have := two_mul_add_eight_le_pow (m+1)
      have h2 : (0:ℝ) < (2:ℝ)^((m+1)+3) - 2 := by push_cast at this ⊢; linarith
      apply div_pos (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (m+1)]) h2
    linarith [hσ, h1]
  have hσ_ub : σ ≤ 1/2 := by
    have h2 := (sigma_natCast_mem m).1
    linarith [hτ1, h2]
  have hσ_half : σ ∈ Set.Icc (0:ℝ) (1/2) := ⟨hσ_lb, hσ_ub⟩
  have hrefl := abs_le.mp (zetalessthanhalf_upper hσ_half ht hz)
  have hrefl_le := hrefl.2
  have ht0 : (0:ℝ) < t := by linarith
  have hlog2 : Real.log |t/2| = Real.log t - Real.log 2 := by
    rw [abs_of_pos (by linarith : (0:ℝ) < t/2)]
    rw [show t/2 = t*2⁻¹ by ring, Real.log_mul ht0.ne' (by norm_num), Real.log_inv]
    ring
  have hlogpi : Real.log |Real.pi| = Real.log Real.pi := by
    rw [abs_of_pos Real.pi_pos]
  rw [hlog2, hlogpi] at hrefl_le
  -- the exact algebraic identity: chord_{-n}(σ) = chord_m(1-σ) + (1/2-σ)*logt + (σ-1/2)*logπ
  have hsne_m : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := (sigma_strictMono_succ m).ne
  have hsne_n : sigma (-((m:ℤ)+1)) ≠ sigma (-((m:ℤ)+1)+1) := by
    have hmir1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    rw [show (-((m:ℤ)+1)+1) = -(m:ℤ) by ring, hmir1, sigma_neg_eq]
    intro heq
    exact hsne_m (by linarith)
  have hcoeff1 : mCoeff (-((m:ℤ)+1)) * σ + bCoeff (-((m:ℤ)+1))
      = (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) + (1/2-σ) := by
    have hpt0_neg : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = vCoeff (-((m:ℤ)+1)) := by unfold bCoeff; ring
    have hcross_neg : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeff (-((m:ℤ)+1)) - vCoeff (-((m:ℤ)+1)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg :
        mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeff (-((m:ℤ)+1)) = vCoeff (-(m:ℤ)) := by
      have expand : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) - mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by unfold bCoeff; ring
    have hcross_m :
        mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvc_mirror1 : vCoeff (-((m:ℤ)+1)) = sigma ((m:ℤ)+1) - 1/2 + vCoeff ((m:ℤ)+1) := by
      have h := vCoeff_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvc_mirror0 : vCoeff (-(m:ℤ)) = sigma (m:ℤ) - 1/2 + vCoeff (m:ℤ) := vCoeff_neg_eq m
    have h1 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeff (m:ℤ) + (1/2 - sigma (-((m:ℤ)+1))) := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvc_mirror1]
      ring
    have h2 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeff (m:ℤ)
          + (1/2 - sigma (-((m:ℤ)+1)+1)) := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvc_mirror0]
      ring
    have key : (mCoeff (-((m:ℤ)+1)) + (mCoeff (m:ℤ)+1))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeff (-((m:ℤ)+1)) = -(mCoeff (m:ℤ)) - 1 := by linarith [h]
      have hbeq : bCoeff (-((m:ℤ)+1)) = mCoeff (m:ℤ) + bCoeff (m:ℤ) + 1/2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hcoeffP : mCoeffP (-((m:ℤ)+1)) * σ + bCoeffP (-((m:ℤ)+1))
      = mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ) := by
    norm_num [mCoeffP, bCoeffP, vCoeffP]
  have hcoeffPP : mCoeffPP (-((m:ℤ)+1)) * σ + bCoeffPP (-((m:ℤ)+1))
      = (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) + (σ-1/2)*Real.log Real.pi := by
    have hpt0_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-((m:ℤ)+1)) := by unfold bCoeffPP; ring
    have hcross_neg : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeffPP (-((m:ℤ)+1)) - vCoeffPP (-((m:ℤ)+1)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-(m:ℤ)) := by
      have expand : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1))
            - mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeffPP (m:ℤ) * sigma (m:ℤ) + bCoeffPP (m:ℤ) = vCoeffPP (m:ℤ) := by
      unfold bCoeffPP; ring
    have hcross_m : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeffPP (m:ℤ) - vCoeffPP ((m:ℤ)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) + bCoeffPP (m:ℤ) = vCoeffPP ((m:ℤ)+1) := by
      have expand : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeffPP (m:ℤ) * sigma (m:ℤ) - mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvpp_mirror1 : vCoeffPP (-((m:ℤ)+1))
        = vCoeffPP ((m:ℤ)+1) + (1/2 - sigma ((m:ℤ)+1)) * Real.log Real.pi := by
      have h := vCoeffPP_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvpp_mirror0 :
        vCoeffPP (-(m:ℤ)) = vCoeffPP (m:ℤ) + (1/2 - sigma (m:ℤ)) * Real.log Real.pi :=
      vCoeffPP_neg_eq m
    have h1 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)) - 1/2) * Real.log Real.pi := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvpp_mirror1]
      ring
    have h2 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)+1) - 1/2) * Real.log Real.pi := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvpp_mirror0]
      ring
    have key : (mCoeffPP (-((m:ℤ)+1)) - Real.log Real.pi + mCoeffPP (m:ℤ))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeffPP (-((m:ℤ)+1)) = Real.log Real.pi - mCoeffPP (m:ℤ) := by linarith [h]
      have hbeq : bCoeffPP (-((m:ℤ)+1))
          = mCoeffPP (m:ℤ) + bCoeffPP (m:ℤ) - Real.log Real.pi / 2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hkey : (mCoeff (-((m+1:ℕ):ℤ)) * σ + bCoeff (-((m+1:ℕ):ℤ))) * Real.log t
      + (mCoeffP (-((m+1:ℕ):ℤ)) * σ + bCoeffP (-((m+1:ℕ):ℤ))) * Real.log (Real.log t)
      + (mCoeffPP (-((m+1:ℕ):ℤ)) * σ + bCoeffPP (-((m+1:ℕ):ℤ)))
      = C + (1/2-σ)*Real.log t + (σ-1/2)*Real.log Real.pi := by
    rw [hC_def, show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring, hcoeff1, hcoeffP, hcoeffPP]
    ring
  rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hkey ⊢
  rw [hkey]
  have hlog2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprod : (0:ℝ) ≤ (1/2-σ)*Real.log 2 := mul_nonneg (by linarith) hlog2pos
  have ht0'' : (0:ℝ) < t := by linarith
  have ht2pos : (0:ℝ) < t ^ 2 := by positivity
  have hlogtpos : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
  set numer : ℝ := 2 * ((16 + (1 - σ)) ^ 2 + (18 - (1 - σ)) ^ 2) + |2 - 2 * (1 - σ)| ^ 2
    with hnumer_def
  have hcombine : (3:ℝ) / (2 * t ^ 2) + numer / (8 * t ^ 2 * Real.log t) + 1 / (2 * t ^ 2)
      = 2 / t ^ 2 + numer / (8 * t ^ 2 * Real.log t) := by ring
  have hexpand : (1/2-σ)*(Real.log t - Real.log 2) = (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 := by
    ring
  rw [hexpand] at hrefl_le
  have step1 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ Real.log ‖riemannZeta (1 - ↑σ + ↑t * Complex.I)‖
        + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [hrefl_le]
  have step2 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + (3 / (2 * t ^ 2) + numer / (8 * t ^ 2 * Real.log t))
        + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi
        + 1/(2*t^2) := by
    linarith [step1, hnonneg]
  have step3 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + (3 / (2 * t ^ 2) + numer / (8 * t ^ 2 * Real.log t)) + (1/2-σ)*Real.log t
        + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [step2, hprod]
  linarith [step3, hcombine]


/-- **Tight, simplified version of `zeta_chord_bound_neg`**, with the numerator collapsed to
`1158`.

### Summary of Proof
As `zeta_chord_bound_neg_tight`, but routed through `zeta_chord_bound_nonneg_tight_simple`, whose
numerator is already the `σ`-independent constant `1158`.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35); Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`,
`sigma_natCast_mem`, `sigma_neg_eq`, `sigma_strictMono_succ`, `two_mul_add_eight_le_pow`,
`vCoeff`, `vCoeffP`, `vCoeffPP`, `vCoeffPP_neg_eq`, `vCoeff_neg_eq`,
`zeta_chord_bound_nonneg_tight_simple`, `zetalessthanhalf_upper`.
**Used by:** `zeta_piecewise_bound_tight_simple`. -/
theorem zeta_chord_bound_neg_tight_simple (n : ℕ) (hn : 1 ≤ n) {σ t : ℝ}
    (hσ : sigma (-(n:ℤ)) ≤ σ) (hσ' : σ ≤ sigma (-(n:ℤ)+1)) (ht : (10:ℝ) < t)
    (hz : riemannZeta ((1:ℂ) - σ + t * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (-(n:ℤ)) * σ + bCoeff (-(n:ℤ))) * Real.log t
          + (mCoeffP (-(n:ℤ)) * σ + bCoeffP (-(n:ℤ))) * Real.log (Real.log t)
          + (mCoeffPP (-(n:ℤ)) * σ + bCoeffPP (-(n:ℤ)))
          + (2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m+1 := ⟨n-1, by omega⟩
  subst hm
  have hnm : (-(((m:ℕ)+1:ℕ):ℤ)+1) = -(m:ℤ) := by push_cast; ring
  rw [hnm] at hσ'
  have hτ0 : sigma (m:ℤ) ≤ 1 - σ := by
    rw [sigma_neg_eq] at hσ'; linarith
  have hτ1 : 1 - σ ≤ sigma ((m:ℤ)+1) := by
    have hσ2 := hσ
    rw [sigma_neg_eq] at hσ2
    rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hσ2
    linarith
  have hnonneg := zeta_chord_bound_nonneg_tight_simple m hτ0 hτ1 (by linarith : (8:ℝ) < t)
  rw [show (((1-σ:ℝ)):ℂ) = (1:ℂ) - (σ:ℂ) by push_cast; ring] at hnonneg
  set C : ℝ := (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) * Real.log t
      + (mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ)) * Real.log (Real.log t)
      + (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) with hC_def
  -- σ ∈ [0, 1/2]
  have hσ_lb : (0:ℝ) ≤ σ := by
    have h1 : (0:ℝ) < sigma (-(((m+1:ℕ)):ℤ)) := by
      unfold sigma
      rw [ite_eq_right (by omega : ¬(0:ℤ) ≤ -(((m+1:ℕ)):ℤ))]
      rw [show (-(-(((m+1:ℕ)):ℤ))) = (((m+1:ℕ)):ℤ) by ring]
      have := two_mul_add_eight_le_pow (m+1)
      have h2 : (0:ℝ) < (2:ℝ)^((m+1)+3) - 2 := by push_cast at this ⊢; linarith
      apply div_pos (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (m+1)]) h2
    linarith [hσ, h1]
  have hσ_ub : σ ≤ 1/2 := by
    have h2 := (sigma_natCast_mem m).1
    linarith [hτ1, h2]
  have hσ_half : σ ∈ Set.Icc (0:ℝ) (1/2) := ⟨hσ_lb, hσ_ub⟩
  have hrefl := abs_le.mp (zetalessthanhalf_upper hσ_half ht hz)
  have hrefl_le := hrefl.2
  have ht0 : (0:ℝ) < t := by linarith
  have hlog2 : Real.log |t/2| = Real.log t - Real.log 2 := by
    rw [abs_of_pos (by linarith : (0:ℝ) < t/2)]
    rw [show t/2 = t*2⁻¹ by ring, Real.log_mul ht0.ne' (by norm_num), Real.log_inv]
    ring
  have hlogpi : Real.log |Real.pi| = Real.log Real.pi := by
    rw [abs_of_pos Real.pi_pos]
  rw [hlog2, hlogpi] at hrefl_le
  -- the exact algebraic identity: chord_{-n}(σ) = chord_m(1-σ) + (1/2-σ)*logt + (σ-1/2)*logπ
  have hsne_m : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := (sigma_strictMono_succ m).ne
  have hsne_n : sigma (-((m:ℤ)+1)) ≠ sigma (-((m:ℤ)+1)+1) := by
    have hmir1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    rw [show (-((m:ℤ)+1)+1) = -(m:ℤ) by ring, hmir1, sigma_neg_eq]
    intro heq
    exact hsne_m (by linarith)
  have hcoeff1 : mCoeff (-((m:ℤ)+1)) * σ + bCoeff (-((m:ℤ)+1))
      = (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) + (1/2-σ) := by
    have hpt0_neg : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = vCoeff (-((m:ℤ)+1)) := by unfold bCoeff; ring
    have hcross_neg : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeff (-((m:ℤ)+1)) - vCoeff (-((m:ℤ)+1)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg :
        mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeff (-((m:ℤ)+1)) = vCoeff (-(m:ℤ)) := by
      have expand : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) - mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by unfold bCoeff; ring
    have hcross_m :
        mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvc_mirror1 : vCoeff (-((m:ℤ)+1)) = sigma ((m:ℤ)+1) - 1/2 + vCoeff ((m:ℤ)+1) := by
      have h := vCoeff_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvc_mirror0 : vCoeff (-(m:ℤ)) = sigma (m:ℤ) - 1/2 + vCoeff (m:ℤ) := vCoeff_neg_eq m
    have h1 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeff (m:ℤ) + (1/2 - sigma (-((m:ℤ)+1))) := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvc_mirror1]
      ring
    have h2 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeff (m:ℤ)
          + (1/2 - sigma (-((m:ℤ)+1)+1)) := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvc_mirror0]
      ring
    have key : (mCoeff (-((m:ℤ)+1)) + (mCoeff (m:ℤ)+1))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeff (-((m:ℤ)+1)) = -(mCoeff (m:ℤ)) - 1 := by linarith [h]
      have hbeq : bCoeff (-((m:ℤ)+1)) = mCoeff (m:ℤ) + bCoeff (m:ℤ) + 1/2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hcoeffP : mCoeffP (-((m:ℤ)+1)) * σ + bCoeffP (-((m:ℤ)+1))
      = mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ) := by
    norm_num [mCoeffP, bCoeffP, vCoeffP]
  have hcoeffPP : mCoeffPP (-((m:ℤ)+1)) * σ + bCoeffPP (-((m:ℤ)+1))
      = (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) + (σ-1/2)*Real.log Real.pi := by
    have hpt0_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-((m:ℤ)+1)) := by unfold bCoeffPP; ring
    have hcross_neg : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeffPP (-((m:ℤ)+1)) - vCoeffPP (-((m:ℤ)+1)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-(m:ℤ)) := by
      have expand : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1))
            - mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeffPP (m:ℤ) * sigma (m:ℤ) + bCoeffPP (m:ℤ) = vCoeffPP (m:ℤ) := by
      unfold bCoeffPP; ring
    have hcross_m : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeffPP (m:ℤ) - vCoeffPP ((m:ℤ)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) + bCoeffPP (m:ℤ) = vCoeffPP ((m:ℤ)+1) := by
      have expand : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeffPP (m:ℤ) * sigma (m:ℤ) - mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvpp_mirror1 : vCoeffPP (-((m:ℤ)+1))
        = vCoeffPP ((m:ℤ)+1) + (1/2 - sigma ((m:ℤ)+1)) * Real.log Real.pi := by
      have h := vCoeffPP_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvpp_mirror0 :
        vCoeffPP (-(m:ℤ)) = vCoeffPP (m:ℤ) + (1/2 - sigma (m:ℤ)) * Real.log Real.pi :=
      vCoeffPP_neg_eq m
    have h1 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)) - 1/2) * Real.log Real.pi := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvpp_mirror1]
      ring
    have h2 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)+1) - 1/2) * Real.log Real.pi := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvpp_mirror0]
      ring
    have key : (mCoeffPP (-((m:ℤ)+1)) - Real.log Real.pi + mCoeffPP (m:ℤ))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeffPP (-((m:ℤ)+1)) = Real.log Real.pi - mCoeffPP (m:ℤ) := by linarith [h]
      have hbeq : bCoeffPP (-((m:ℤ)+1))
          = mCoeffPP (m:ℤ) + bCoeffPP (m:ℤ) - Real.log Real.pi / 2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hkey : (mCoeff (-((m+1:ℕ):ℤ)) * σ + bCoeff (-((m+1:ℕ):ℤ))) * Real.log t
      + (mCoeffP (-((m+1:ℕ):ℤ)) * σ + bCoeffP (-((m+1:ℕ):ℤ))) * Real.log (Real.log t)
      + (mCoeffPP (-((m+1:ℕ):ℤ)) * σ + bCoeffPP (-((m+1:ℕ):ℤ)))
      = C + (1/2-σ)*Real.log t + (σ-1/2)*Real.log Real.pi := by
    rw [hC_def, show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring, hcoeff1, hcoeffP, hcoeffPP]
    ring
  rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hkey ⊢
  rw [hkey]
  have hlog2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprod : (0:ℝ) ≤ (1/2-σ)*Real.log 2 := mul_nonneg (by linarith) hlog2pos
  have hcombine : (3:ℝ)/(2*t^2) + 1158/(8*t^2*Real.log t) + 1/(2*t^2)
      = 2/t^2 + 1158/(8*t^2*Real.log t) := by ring
  have hexpand : (1/2-σ)*(Real.log t - Real.log 2) = (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 := by
    ring
  rw [hexpand] at hrefl_le
  have step1 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ Real.log ‖riemannZeta (1 - ↑σ + ↑t * Complex.I)‖
        + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [hrefl_le]
  have step2 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + (3/(2*t^2) + 1158/(8*t^2*Real.log t))
        + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi
        + 1/(2*t^2) := by
    linarith [step1, hnonneg]
  have step3 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + (3/(2*t^2) + 1158/(8*t^2*Real.log t)) + (1/2-σ)*Real.log t
        + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [step2, hprod]
  linarith [step3, hcombine]


/-- **`zeta_piecewise_bound`, negative-index case, via reflection.**

### Summary of Proof
Write `n := -k ≥ 1` and `m := n-1 ≥ 0`. Combine
`BackgroundZetaBounds.zetalessthanhalf_upper` — which bounds `ζ(σ+it)` in terms of `ζ(1-σ+it)`,
Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36) — with `zeta_chord_bound_nonneg` at index `m`,
applied to the mirrored point `τ := 1-σ`.

The two-point matching argument recurs: `mCoeff(-n)`/`bCoeff(-n)` and the reflected chord
`mCoeff(m)(1-σ) + bCoeff(m) + (1/2-σ)` are both affine in `σ` and agree at `σ = σ_{-n}` and
`σ = σ_{-n+1}`, via the mirror identities `sigma_neg_eq`, `vCoeff_neg_eq`, `vCoeffPP_neg_eq`.

### Lean Notes
Those mirror identities are stated unconditionally in the index, which matters at the `m = 0`
edge case: there the reflection's `log π` coefficient `(1/2 - σ_0)` vanishes, sidestepping
`vCoeffPP 0`'s special-cased value `log 0.611` entirely.

**Slack accounting.** The `4/t` (rather than `3/t`) absorbs both `zeta_chord_bound_nonneg`'s own
`3/t` and `zetalessthanhalf_upper`'s reflection error `1/(2t²)`, which is at most the remaining
`1/t` once `t ≥ 1/2`. There is room to spare: `log|t/2| = log t - log 2` contributes a further
nonnegative slack term `(1/2-σ)log 2` that goes unused.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35); Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36); the mirror definitions of Equation `\ref{eq:sigmak}`
(Equation 4).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`,
`sigma_natCast_mem`, `sigma_neg_eq`, `sigma_strictMono_succ`, `two_mul_add_eight_le_pow`,
`vCoeff`, `vCoeffP`, `vCoeffPP`, `vCoeffPP_neg_eq`, `vCoeff_neg_eq`, `zeta_chord_bound_nonneg`,
`zetalessthanhalf_upper`.
**Used by:** `zeta_piecewise_bound`. -/
private theorem zeta_chord_bound_neg (n : ℕ) (hn : 1 ≤ n) {σ t : ℝ}
    (hσ : sigma (-(n:ℤ)) ≤ σ) (hσ' : σ ≤ sigma (-(n:ℤ)+1)) (ht : (10:ℝ) ^ (12:ℕ) < t)
    (hz : riemannZeta ((1:ℂ) - σ + t * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff (-(n:ℤ)) * σ + bCoeff (-(n:ℤ))) * Real.log t
          + (mCoeffP (-(n:ℤ)) * σ + bCoeffP (-(n:ℤ))) * Real.log (Real.log t)
          + (mCoeffPP (-(n:ℤ)) * σ + bCoeffPP (-(n:ℤ))) + 4 / t := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m+1 := ⟨n-1, by omega⟩
  subst hm
  have hnm : (-(((m:ℕ)+1:ℕ):ℤ)+1) = -(m:ℤ) := by push_cast; ring
  rw [hnm] at hσ'
  have hτ0 : sigma (m:ℤ) ≤ 1 - σ := by
    rw [sigma_neg_eq] at hσ'; linarith
  have hτ1 : 1 - σ ≤ sigma ((m:ℤ)+1) := by
    have hσ2 := hσ
    rw [sigma_neg_eq] at hσ2
    rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hσ2
    linarith
  have hnonneg := zeta_chord_bound_nonneg m hτ0 hτ1 ht
  rw [show (((1-σ:ℝ)):ℂ) = (1:ℂ) - (σ:ℂ) by push_cast; ring] at hnonneg
  set C : ℝ := (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) * Real.log t
      + (mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ)) * Real.log (Real.log t)
      + (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) with hC_def
  -- σ ∈ [0, 1/2]
  have hσ_lb : (0:ℝ) ≤ σ := by
    have h1 : (0:ℝ) < sigma (-(((m+1:ℕ)):ℤ)) := by
      unfold sigma
      rw [ite_eq_right (by omega : ¬(0:ℤ) ≤ -(((m+1:ℕ)):ℤ))]
      rw [show (-(-(((m+1:ℕ)):ℤ))) = (((m+1:ℕ)):ℤ) by ring]
      have := two_mul_add_eight_le_pow (m+1)
      have h2 : (0:ℝ) < (2:ℝ)^((m+1)+3) - 2 := by push_cast at this ⊢; linarith
      apply div_pos (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (m+1)]) h2
    linarith [hσ, h1]
  have hσ_ub : σ ≤ 1/2 := by
    have h2 := (sigma_natCast_mem m).1
    linarith [hτ1, h2]
  have hσ_half : σ ∈ Set.Icc (0:ℝ) (1/2) := ⟨hσ_lb, hσ_ub⟩
  have ht10 : (10:ℝ) < t := by nlinarith [ht]
  have hrefl := abs_le.mp (zetalessthanhalf_upper hσ_half ht10 hz)
  have hrefl_le := hrefl.2
  have ht0 : (0:ℝ) < t := by linarith
  have hlog2 : Real.log |t/2| = Real.log t - Real.log 2 := by
    rw [abs_of_pos (by linarith : (0:ℝ) < t/2)]
    rw [show t/2 = t*2⁻¹ by ring, Real.log_mul ht0.ne' (by norm_num), Real.log_inv]
    ring
  have hlogpi : Real.log |Real.pi| = Real.log Real.pi := by
    rw [abs_of_pos Real.pi_pos]
  rw [hlog2, hlogpi] at hrefl_le
  -- the exact algebraic identity: chord_{-n}(σ) = chord_m(1-σ) + (1/2-σ)*logt + (σ-1/2)*logπ
  have hsne_m : sigma (m:ℤ) ≠ sigma ((m:ℤ)+1) := (sigma_strictMono_succ m).ne
  have hsne_n : sigma (-((m:ℤ)+1)) ≠ sigma (-((m:ℤ)+1)+1) := by
    have hmir1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    rw [show (-((m:ℤ)+1)+1) = -(m:ℤ) by ring, hmir1, sigma_neg_eq]
    intro heq
    exact hsne_m (by linarith)
  have hcoeff1 : mCoeff (-((m:ℤ)+1)) * σ + bCoeff (-((m:ℤ)+1))
      = (mCoeff (m:ℤ) * (1-σ) + bCoeff (m:ℤ)) + (1/2-σ) := by
    have hpt0_neg : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = vCoeff (-((m:ℤ)+1)) := by unfold bCoeff; ring
    have hcross_neg : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeff (-((m:ℤ)+1)) - vCoeff (-((m:ℤ)+1)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg :
        mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeff (-((m:ℤ)+1)) = vCoeff (-(m:ℤ)) := by
      have expand : mCoeff (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) - mCoeff (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeff (m:ℤ) * sigma (m:ℤ) + bCoeff (m:ℤ) = vCoeff (m:ℤ) := by unfold bCoeff; ring
    have hcross_m :
        mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1)) = vCoeff (m:ℤ) - vCoeff ((m:ℤ)+1) := by
      unfold mCoeff; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeff (m:ℤ) * sigma ((m:ℤ)+1) + bCoeff (m:ℤ) = vCoeff ((m:ℤ)+1) := by
      have expand : mCoeff (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeff (m:ℤ) * sigma (m:ℤ) - mCoeff (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvc_mirror1 : vCoeff (-((m:ℤ)+1)) = sigma ((m:ℤ)+1) - 1/2 + vCoeff ((m:ℤ)+1) := by
      have h := vCoeff_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvc_mirror0 : vCoeff (-(m:ℤ)) = sigma (m:ℤ) - 1/2 + vCoeff (m:ℤ) := vCoeff_neg_eq m
    have h1 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeff (m:ℤ) + (1/2 - sigma (-((m:ℤ)+1))) := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvc_mirror1]
      ring
    have h2 : mCoeff (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeff (-((m:ℤ)+1))
        = mCoeff (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeff (m:ℤ)
          + (1/2 - sigma (-((m:ℤ)+1)+1)) := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvc_mirror0]
      ring
    have key : (mCoeff (-((m:ℤ)+1)) + (mCoeff (m:ℤ)+1))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeff (-((m:ℤ)+1)) = -(mCoeff (m:ℤ)) - 1 := by linarith [h]
      have hbeq : bCoeff (-((m:ℤ)+1)) = mCoeff (m:ℤ) + bCoeff (m:ℤ) + 1/2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hcoeffP : mCoeffP (-((m:ℤ)+1)) * σ + bCoeffP (-((m:ℤ)+1))
      = mCoeffP (m:ℤ) * (1-σ) + bCoeffP (m:ℤ) := by
    norm_num [mCoeffP, bCoeffP, vCoeffP]
  have hcoeffPP : mCoeffPP (-((m:ℤ)+1)) * σ + bCoeffPP (-((m:ℤ)+1))
      = (mCoeffPP (m:ℤ) * (1-σ) + bCoeffPP (m:ℤ)) + (σ-1/2)*Real.log Real.pi := by
    have hpt0_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-((m:ℤ)+1)) := by unfold bCoeffPP; ring
    have hcross_neg : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1))
        = vCoeffPP (-((m:ℤ)+1)) - vCoeffPP (-((m:ℤ)+1)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_n
    have heqidx : (-((m:ℤ)+1)+1) = -(m:ℤ) := by ring
    rw [heqidx] at hcross_neg
    have hpt1_neg : mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) + bCoeffPP (-((m:ℤ)+1))
        = vCoeffPP (-(m:ℤ)) := by
      have expand : mCoeffPP (-((m:ℤ)+1)) * (sigma (-((m:ℤ)+1)) - sigma (-(m:ℤ)))
          = mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1))
            - mCoeffPP (-((m:ℤ)+1)) * sigma (-(m:ℤ)) := by
        ring
      linarith [hpt0_neg, hcross_neg, expand]
    have hpt0_m : mCoeffPP (m:ℤ) * sigma (m:ℤ) + bCoeffPP (m:ℤ) = vCoeffPP (m:ℤ) := by
      unfold bCoeffPP; ring
    have hcross_m : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
        = vCoeffPP (m:ℤ) - vCoeffPP ((m:ℤ)+1) := by
      unfold mCoeffPP; rw [div_mul_cancel₀]; exact sub_ne_zero.mpr hsne_m
    have hpt1_m : mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) + bCoeffPP (m:ℤ) = vCoeffPP ((m:ℤ)+1) := by
      have expand : mCoeffPP (m:ℤ) * (sigma (m:ℤ) - sigma ((m:ℤ)+1))
          = mCoeffPP (m:ℤ) * sigma (m:ℤ) - mCoeffPP (m:ℤ) * sigma ((m:ℤ)+1) := by ring
      linarith [hpt0_m, hcross_m, expand]
    have hsig_mirror1 : sigma (-((m:ℤ)+1)) = 1 - sigma ((m:ℤ)+1) := by
      have h := sigma_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hvpp_mirror1 : vCoeffPP (-((m:ℤ)+1))
        = vCoeffPP ((m:ℤ)+1) + (1/2 - sigma ((m:ℤ)+1)) * Real.log Real.pi := by
      have h := vCoeffPP_neg_eq (m+1)
      rw [show (((m+1:ℕ)):ℤ) = ((m:ℤ)+1) by push_cast; ring] at h; exact h
    have hsig_mirror0 : sigma (-(m:ℤ)) = 1 - sigma (m:ℤ) := sigma_neg_eq m
    have hvpp_mirror0 :
        vCoeffPP (-(m:ℤ)) = vCoeffPP (m:ℤ) + (1/2 - sigma (m:ℤ)) * Real.log Real.pi :=
      vCoeffPP_neg_eq m
    have h1 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1))) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)) - 1/2) * Real.log Real.pi := by
      rw [hpt0_neg, hsig_mirror1, show (1 - (1 - sigma ((m:ℤ)+1))) = sigma ((m:ℤ)+1) by ring,
        hpt1_m, hvpp_mirror1]
      ring
    have h2 : mCoeffPP (-((m:ℤ)+1)) * sigma (-((m:ℤ)+1)+1) + bCoeffPP (-((m:ℤ)+1))
        = mCoeffPP (m:ℤ) * (1 - sigma (-((m:ℤ)+1)+1)) + bCoeffPP (m:ℤ)
          + (sigma (-((m:ℤ)+1)+1) - 1/2) * Real.log Real.pi := by
      rw [heqidx, hpt1_neg, hsig_mirror0, show (1 - (1 - sigma (m:ℤ))) = sigma (m:ℤ) by ring,
        hpt0_m, hvpp_mirror0]
      ring
    have key : (mCoeffPP (-((m:ℤ)+1)) - Real.log Real.pi + mCoeffPP (m:ℤ))
        * (sigma (-((m:ℤ)+1)) - sigma (-((m:ℤ)+1)+1)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · have hmeq : mCoeffPP (-((m:ℤ)+1)) = Real.log Real.pi - mCoeffPP (m:ℤ) := by linarith [h]
      have hbeq : bCoeffPP (-((m:ℤ)+1))
          = mCoeffPP (m:ℤ) + bCoeffPP (m:ℤ) - Real.log Real.pi / 2 := by
        rw [hmeq] at h1; linarith [h1]
      rw [hmeq, hbeq]; ring
    · exact absurd (sub_eq_zero.mp h) hsne_n
  have hkey : (mCoeff (-((m+1:ℕ):ℤ)) * σ + bCoeff (-((m+1:ℕ):ℤ))) * Real.log t
      + (mCoeffP (-((m+1:ℕ):ℤ)) * σ + bCoeffP (-((m+1:ℕ):ℤ))) * Real.log (Real.log t)
      + (mCoeffPP (-((m+1:ℕ):ℤ)) * σ + bCoeffPP (-((m+1:ℕ):ℤ)))
      = C + (1/2-σ)*Real.log t + (σ-1/2)*Real.log Real.pi := by
    rw [hC_def, show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring, hcoeff1, hcoeffP, hcoeffPP]
    ring
  rw [show ((m+1:ℕ):ℤ) = ((m:ℤ)+1) by push_cast; ring] at hkey ⊢
  rw [hkey]
  have hlog2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprod : (0:ℝ) ≤ (1/2-σ)*Real.log 2 := mul_nonneg (by linarith) hlog2pos
  have ht2 : 3/t + 1/(2*t^2) ≤ 4/t := by
    have ht0' : (0:ℝ) < t := by linarith
    have heq : 4/t - (3/t + 1/(2*t^2)) = (2*t-1)/(2*t^2) := by field_simp; ring
    have hnn : (0:ℝ) ≤ (2*t-1)/(2*t^2) := div_nonneg (by linarith) (by positivity)
    linarith [heq ▸ hnn]
  have hexpand : (1/2-σ)*(Real.log t - Real.log 2) = (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 := by
    ring
  rw [hexpand] at hrefl_le
  have step1 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ Real.log ‖riemannZeta (1 - ↑σ + ↑t * Complex.I)‖
        + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [hrefl_le]
  have step2 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + 3/t + (1/2-σ)*Real.log t - (1/2-σ)*Real.log 2 + (σ-1/2)*Real.log Real.pi
        + 1/(2*t^2) := by
    linarith [step1, hnonneg]
  have step3 : Real.log ‖riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ C + 3/t + (1/2-σ)*Real.log t + (σ-1/2)*Real.log Real.pi + 1/(2*t^2) := by
    linarith [step2, hprod]
  linarith [step3, ht2]

/-- **The fundamental piecewise bound underlying `mCoeff`/`bCoeff`/`mCoeffP`/`bCoeffP`/`mCoeffPP`/
`bCoeffPP`.** For `σ_k ≤ σ < σ_{k+1}` and `t` large enough, linear interpolation (in `σ`) between
the explicit bounds `vCoeff`/`vCoeffP`/`vCoeffPP` at the two lines `σ_k`, `σ_{k+1}` is valid,
**up to an explicit `O^*(4/t)` slack**: `log|ζ(σ+it)| ≤ (mCoeff k · σ + bCoeff k) log|t| +
(mCoeffP k · σ + bCoeffP k) log log|t| + (mCoeffPP k · σ + bCoeffPP k) + 4/|t|`.

### Summary of Proof
A consequence of `BackgroundZetaBounds.interpolated_bound_1b`/`2` (for `k ≥ 0`) and
`BackgroundZetaBounds.zetalessthanhalf_upper` (reflecting `k < 0` to the mirror index
`k' = -k-1`), via `zeta_chord_bound_nonneg`/`zeta_chord_bound_neg` above. In each case the chord
is identified with the interpolation bound's own displayed coefficient by two-point matching,
both being affine in `σ`.

### Lean Notes
**Two departures from the shape of the source's display, both forced.**

(1) The threshold is `10¹² < |t|`, inherited from `interpolated_bound_1b`/`2`, whose crude forms
convert `log|t|` to `log|T|` across a `[T-1,T+1]` window and only become effective for `t` this
large. The source's Proposition `\ref{prop:interpolation}` (Proposition 35) asks only `t > 12`
(and `t > 3` in its case (2)); the *tight* route below recovers that scale, needing only
`10 < |t|`.

(2) The conclusion carries an explicit `+4/|t|` slack, absorbing `interpolated_bound_1b`/`2`'s
own window correction (for `k ≥ 0`) plus, for `k < 0`, `zetalessthanhalf_upper`'s reflection
error. This is cruder in *shape* than the source's own `O^*(1/t²)` error; the variant matching
that shape is `zeta_piecewise_bound_tight_simple`, whose `1158/(8t²log|t|)` is literally the
source's `579/(4t²log|t|)`.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), cases (1b) and (2); Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36); the chord definitions of Equations `\ref{eq:mk}`,
`\ref{eq:mkp}`, `\ref{eq:mkpp}` (Equations 5–7).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`,
`riemannZeta_norm_abs_im`, `zeta_chord_bound_neg`, `zeta_chord_bound_nonneg`.
**Used by:** `JensenBounds.arc_pointwise_bound`, `LittlewoodMethod.littlewood_mainterm`,
`JensenScaleConstantsAlt.zeta_piecewise_bound_alt`. -/
theorem zeta_piecewise_bound {k : ℤ} {σ t : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ < sigma (k + 1))
    (ht : (10:ℝ) ^ (12:ℕ) < |t|)
    (hz : riemannZeta ((1:ℂ) - σ + |t| * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff k * σ + bCoeff k) * Real.log |t|
          + (mCoeffP k * σ + bCoeffP k) * Real.log (Real.log |t|)
          + (mCoeffPP k * σ + bCoeffPP k) + 4 / |t| := by
  rw [riemannZeta_norm_abs_im]
  have habst : (0:ℝ) < |t| := by
    have : (0:ℝ) < (10:ℝ)^(12:ℕ) := by positivity
    linarith [ht]
  have hslack : (3:ℝ) / |t| ≤ 4 / |t| := by
    rw [div_le_div_iff_of_pos_right habst]; norm_num
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk with m
    have := zeta_chord_bound_nonneg m hσ (le_of_lt hσ') ht
    linarith [this, hslack]
  · push Not at hk
    obtain ⟨n, hn, hkeq⟩ : ∃ n:ℕ, 1 ≤ n ∧ k = -(n:ℤ) := ⟨(-k).toNat, by omega, by omega⟩
    subst hkeq
    rw [show (-(n:ℤ)+1) = -(n:ℤ)+1 by ring] at hσ'
    have := zeta_chord_bound_neg n hn hσ (le_of_lt hσ') ht hz
    linarith [this]

/-- **Tight, simplified version of `zeta_piecewise_bound`**, with an `O(1/t²)` error in place of
the crude `4/|t|`.

### Summary of Proof
Same case split on the sign of `k` as `zeta_piecewise_bound`, but routed through
`zeta_chord_bound_nonneg_tight_simple`/`zeta_chord_bound_neg_tight_simple` — Proposition
`\ref{prop:interpolation}` (Proposition 35)'s tight `O(1/t²)` bounds, uniformly collapsed to the
constant `1158`.

### Lean Notes
**No genuinely tight (non-collapsed) counterpart is stated here**: the `k≥0`
branch's numerator is `f(σ) := 2((16+σ)²+(18-σ)²)+(2-2σ)²` while the `k<0` branch's is `f(1-σ)` —
two different functions of `σ`, not unifiable into one closed form without an artificial `max`.
Both are bounded by the same constant `1158` (the value of `f` at `σ=1/2`) because `f` is
decreasing on `(-∞,1)` and every `σ` arising in either branch satisfies `σ≥1/2` or `1-σ≥1/2`
respectively — see `zeta_chord_bound_nonneg_tight`/`zeta_chord_bound_neg_tight` directly for the
exact, per-branch `σ`-dependent bounds. Threshold `t>10` uniformly (the stricter of the two
branches' `t>8`/`t>10`).

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), tight forms of cases (1b) and (2).

### Dependencies
**Depends on:** `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`,
`riemannZeta_norm_abs_im`, `zeta_chord_bound_neg_tight_simple`,
`zeta_chord_bound_nonneg_tight_simple`.
**Used by:** `arc_pointwise_bound_tight`, `littlewood_mainterm_tight`. -/
theorem zeta_piecewise_bound_tight_simple {k : ℤ} {σ t : ℝ} (hσ : sigma k ≤ σ)
    (hσ' : σ < sigma (k + 1)) (ht : (10:ℝ) < |t|)
    (hz : riemannZeta ((1:ℂ) - σ + |t| * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeff k * σ + bCoeff k) * Real.log |t|
          + (mCoeffP k * σ + bCoeffP k) * Real.log (Real.log |t|)
          + (mCoeffPP k * σ + bCoeffPP k)
          + (2 / |t| ^ 2 + 1158 / (8 * |t| ^ 2 * Real.log |t|)) := by
  rw [riemannZeta_norm_abs_im]
  have habst : (0:ℝ) < |t| := by linarith [ht]
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk with m
    have hnn := zeta_chord_bound_nonneg_tight_simple m (t := |t|) hσ (le_of_lt hσ') (by linarith)
    have ht2pos : (0:ℝ) < |t| ^ 2 := by positivity
    have hslack : (3:ℝ) / (2 * |t| ^ 2) ≤ 2 / |t| ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) ht2pos]; nlinarith
    linarith [hnn, hslack]
  · push Not at hk
    obtain ⟨n, hn, hkeq⟩ : ∃ n:ℕ, 1 ≤ n ∧ k = -(n:ℤ) := ⟨(-k).toNat, by omega, by omega⟩
    subst hkeq
    rw [show (-(n:ℤ)+1) = -(n:ℤ)+1 by ring] at hσ'
    exact zeta_chord_bound_neg_tight_simple n (t := |t|) hn hσ (le_of_lt hσ') (by linarith) hz

/-- **The angles `θ_{k,r} = arcsin((1-σ_k)/r)`**, at which the line `σ_k` cuts the circle of
radius `r` about `1`.

### Summary of Proof
A definition, Equation `\ref{eq:thetak}` (Equation 8).

### Lean Notes
Only meaningful for `r ≥ 1 - σ_k`. `Real.arcsin` is total, extending the formula to all `r` by
clamping to `[-π/2, π/2]` — which happens to recover the source's own convention
`θ_{-∞,r} = π/2` in the limit `k → -∞`, where `(1-σ_k)/r → ∞` lands well outside `[-1,1]`.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `sigma`.
Used by: `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`,
`arc_majorant_boundary_integral`, `arc_majorant_boundary_integral_tight`, `arc_majorant_integral`,
`arc_majorant_integral_tight`, `arc_partial_sum`, `arc_piece_bound`, `arc_piece_bound_gen`,
`arc_piece_bound_gen_tight`, `arc_piece_bound_tight`, `arc_pointwise_bound_at`,
`arc_pointwise_le_maj`, `arc_pointwise_le_maj_tight`, `c1`, `c1_boundary_nonneg`,
`c1_eq_integral`, `c1_nonneg`, `c1_summable`, `c1_term_le`, `c1_term_nonneg`, `c2`,
`c2_le_pi_div_two`, `c2_nonneg`, `c3`, `c3_summable`, `chord_boundary_eq_integral`,
`chord_term_eq_integral`, `half_arc_bound`, `half_arc_bound_tight`, `hasSum_theta_diff`,
`integral_le_tsum_arc`, `sin_theta_eq`, `sin_window_of_mem_chord`, `sum_range_theta_telescope`,
`theta_antitone_succ`, `theta_diff_summable`, `theta_le_pi_div_two`, `theta_nonneg`,
`theta_tendsto_zero`, `tsum_eq_integral_arc`. -/
noncomputable def theta (k : ℤ) (r : ℝ) : ℝ := Real.arcsin ((1 - sigma k) / r)

/-- **`K = inf_k (r ≥ 1 - σ_k)`**, the least index whose line `σ_k` meets the disc of radius `r`
about `1`.

### Summary of Proof
A definition, `sInf` of the set of admissible indices. The source sets
`K = inf_k(r ≥ 1-σ_k)` and explicitly allows `K = -∞`.

### Lean Notes
See the remark at the top of the file for the (measure-zero) caveat at `r = 1`. Lean's `sInf` on
`ℤ` returns `0` for an unbounded-below set, so the `K = -∞` case is handled by the separate
summability arguments rather than by the index itself.

### References
tex: the definition of `K` immediately after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `sigma`.
Used by: `Kidx_mem`, `Kidx_sub_one`, `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`,
`c1`, `c1_boundary_nonneg`, `c1_eq_integral`, `c1_nonneg`, `c1_summable`, `c2`,
`c2_le_pi_div_two`, `c2_nonneg`, `c3`, `c3_summable`, `half_arc_bound`, `half_arc_bound_tight`. -/
noncomputable def Kidx (r : ℝ) : ℤ := sInf {k : ℤ | 1 - sigma k ≤ r}

/-! ### Elementary facts about `theta`

`θ_{k,r} = arcsin((1-σ_k)/r)` is nonnegative and antitone in `k` (since `sigma` is increasing with
`σ_k < 1`), and the `θ`-difference sums appearing in `c1`/`c2`/`c3` telescope. -/

/-- **The `θ`-difference sum telescopes**:
`∑_{j<n} (θ_{K+j,r} - θ_{K+j+1,r}) = θ_{K,r} - θ_{K+n,r}`.

### Summary of Proof
Induction on `n`; the successor step is `Finset.sum_range_succ` together with the index cast
`(K + m + 1 : ℤ) = K + ((m+1 : ℕ) : ℤ)`.

### Lean Notes
This is the bookkeeping behind the source's one-line assertion that the sums defining `c_{1,r}`,
`c_{2,r}`, `c_{3,r}` "are rapidly convergent, even if `K = -∞`". Each is built from consecutive
differences of `θ_{k,r}`, so its partial sums collapse to the two endpoints and convergence
reduces to the limit of `θ_{K+n,r}` alone.

### References
tex: the displays defining `c_{1,r}`, `c_{2,r}`, `c_{3,r}` after Equation `\ref{eq:thetak}`
(Equation 8), and the sentence asserting their convergence. No individual counterpart.

### Dependencies
**Depends on:** `theta`.
**Used by:** `c1_summable`, `c2_le_pi_div_two`, `hasSum_theta_diff`,
`theta_diff_summable`. -/
theorem sum_range_theta_telescope (K : ℤ) (r : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (theta (K + j) r - theta (K + j + 1) r)
      = theta K r - theta (K + n) r := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (K + (m:ℤ) + 1) = K + ((m+1 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; ring

/-- **`θ_{k,r} ≥ 0`.**

### Summary of Proof
Immediate from `arcsin ≥ 0` on nonnegative arguments: `1 - σ_k > 0` by `sigma_lt_one`, and
`r > 0` by hypothesis, so `(1-σ_k)/r ≥ 0`.

### Lean Notes
The source introduces the `θ_{k,r}` in Equation `\ref{eq:thetak}` (Equation 8) and thereafter
treats them as a decreasing sequence of angles in `[0, π/2]` without comment. This is one half of
that unstated bookkeeping; `theta_antitone_succ` and `theta_le_pi_div_two` are the rest.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8). No counterpart as a numbered claim.

### Dependencies
**Depends on:** `theta`, `sigma_lt_one`.
Used by: `c1_term_nonneg`, `c1_boundary_nonneg`, `c1_term_le`, `c1_summable`, `c1_eq_integral`,
`c2_le_pi_div_two`, `theta_diff_summable`, `sin_window_of_mem_chord`, `arc_boundary_bound_gen`,
`arc_boundary_bound_gen_tight`. -/
theorem theta_nonneg {k : ℤ} {r : ℝ} (hr : 0 < r) : 0 ≤ theta k r := by
  rw [theta]
  apply Real.arcsin_nonneg.2
  apply div_nonneg _ hr.le
  linarith [sigma_lt_one k]

/-- **`θ_{k+1,r} ≤ θ_{k,r}`** — the angles decrease in `k`.

### Summary of Proof
Since `σ` is increasing in `k` (`sigma_lt_succ`), `1 - σ_k` decreases, hence so does
`arcsin((1-σ_k)/r)` by monotonicity of `arcsin`.

### Lean Notes
The source uses this silently every time it writes a chord-piece contribution as
`(θ_{k,r} - θ_{k+1,r}) ≥ 0`, e.g. throughout the defining sums for `c_{1,r}`, `c_{2,r}`,
`c_{3,r}`. This makes it explicit.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8) and the `c_{i,r}` displays following it. No
counterpart as a numbered claim.

### Dependencies
**Depends on:** `theta`, `sigma_lt_succ`.
Used by: `c1_term_nonneg`, `c1_term_le`, `c1_eq_integral`, `c2_nonneg`, `c2_le_pi_div_two`,
`theta_diff_summable`, `arc_piece_bound`(`_tight`), `arc_piece_bound_gen`(`_tight`). -/
theorem theta_antitone_succ {k : ℤ} {r : ℝ} (hr : 0 < r) : theta (k + 1) r ≤ theta k r := by
  rw [theta, theta]
  apply Real.arcsin_le_arcsin
  apply div_le_div_of_nonneg_right _ hr.le
  linarith [sigma_lt_succ k]

/-! ### Nonnegativity of `c₁` and `c₂`

The `c_{1,r}` values cannot be negative: they are integrals of nonnegative functions. In the
closed form (see the `c_{i,r}` section below) every summand of `c₁` is literally
`∫_{θ_{k+1,r}}^{θ_{k,r}} (m_k(1 - r sin θ) + b_k) dθ`, whose integrand is the chord `A_k(σ)`
evaluated at `σ = 1 - r sin θ ∈ [σ_k, σ_{k+1}]` — nonnegative by `chord_vCoeff_nonneg`. The boundary
term is the same integral over `[θ_{K,r}, π/2]` against the chord indexed `K-1`, where
`σ = 1 - r sin θ ∈ [1-r, σ_K] ⊆ [σ_{K-1}, σ_K]` by the defining property of `K = Kidx r`
(`Kidx_mem`/`Kidx_sub_one`).

`c₁ ≥ 0` is what `RectangularBounds.rectangularjensen` needs in order to push the concavity of `log`
through Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s bound when integrating over the
window. -/

/-- **The chord integral in closed form**:
`∫_p^q (m(1 - r sin θ) + b) dθ = (m+b)(q-p) + m r (cos q - cos p)`.

### Summary of Proof
Direct integration: `∫ 1 dθ = q-p` and `∫ sin θ dθ = cos p - cos q`, so the integrand
`m + b - m r sin θ` integrates to `(m+b)(q-p) + m r(cos q - cos p)`.

### Lean Notes
This is the identity that exhibits each `c_{i,r}` summand as an integral, which is what lets the
sums be compared against `∫ F_{1+it,r}` rather than manipulated termwise. The point
`1 - r sin θ` is the real part of `1 + re^{iθ}` reflected into the chord variable.

### References
No tex counterpart — the source writes the `c_{i,r}` summands in the already-integrated form
`(m_k+b_k)(θ_k-θ_{k+1}) + m_k r(cos θ_k - cos θ_{k+1})`, in the displays after Equation
`\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** none.
**Used by:** `chord_boundary_eq_integral`, `chord_term_eq_integral`. -/
theorem integral_chord_sin (m b r p q : ℝ) :
    (∫ θ in p..q, (m * (1 - r * Real.sin θ) + b))
      = (m + b) * (q - p) + m * r * (Real.cos q - Real.cos p) := by
  have h1 : ∀ θ : ℝ, m * (1 - r * Real.sin θ) + b = (m + b) + (-(m*r)) * Real.sin θ := by
    intro θ; ring
  simp only [h1]
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((Real.continuous_sin.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, integral_sin, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- **`sigma` is strictly monotone** as a function `ℤ → ℝ`.

### Summary of Proof
Upgrades the consecutive-step statement `sigma_lt_succ` to full strict monotonicity, by the
standard induction on the gap between the two indices.

### References
No tex counterpart as a numbered claim; implicit in Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_lt_succ`.
Used by: `Kidx_set_bddBelow`, `c1_eq_integral`, `c1_nonneg`, `c1_summable`, `chordIdx_eq`,
`chordIdx_set_bddBelow`, `half_arc_bound`, `half_arc_bound_tight`, `sigma_tendsto_one`. -/
theorem sigma_strictMono : StrictMono sigma := strictMono_int_of_lt_succ sigma_lt_succ

/-- **`θ_{k,r} ≤ π/2`.**

### Summary of Proof
Unconditionally true of `arcsin`, whose range is `[-π/2, π/2]`; no hypothesis on `r` or `k` is
needed.

### Lean Notes
Together with `theta_nonneg` and `theta_antitone_succ`, this is the unstated bookkeeping the
source relies on when treating the `θ_{k,r}` as a decreasing sequence in `[0, π/2]`. It also
supplies the `θ_{-∞,r} = π/2` endpoint used in the boundary term of each `c_{i,r}`.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8). No counterpart as a numbered claim.

### Dependencies
**Depends on:** `theta`.
Used by: `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`, `c1_boundary_nonneg`,
`c1_eq_integral`, `c1_term_le`, `c1_term_nonneg`, `c2_nonneg`, `sin_window_of_mem_chord`. -/
theorem theta_le_pi_div_two (k : ℤ) (r : ℝ) : theta k r ≤ Real.pi / 2 :=
  Real.arcsin_le_pi_div_two _

/-- **`sin θ_{k,r} = (1-σ_k)/r`**, when the line `σ_k` meets the disc.

### Summary of Proof
`Real.sin_arcsin` inverts `arcsin` exactly on arguments in `[-1,1]`. The argument `(1-σ_k)/r` is
nonnegative by `sigma_lt_one`, and at most `1` precisely under the hypothesis `1-σ_k ≤ r` — which
is exactly the condition that the line meets the disc.

### Lean Notes
The hypothesis is not decorative: without `1-σ_k ≤ r`, `arcsin` clamps and the identity fails.
This is the point at which the Lean has to be explicit about a case the source's geometric
picture makes obvious.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8), which is stated "for each `k` with `r ≥ 1-σ_k`".

### Dependencies
**Depends on:** `sigma_lt_one`, `theta`.
Used by: `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`, `c1_boundary_nonneg`,
`c1_eq_integral`, `c1_term_le`, `c1_term_nonneg`, `sin_window_of_mem_chord`. -/
theorem sin_theta_eq {k : ℤ} {r : ℝ} (hr : 0 < r) (hk : 1 - sigma k ≤ r) :
    Real.sin (theta k r) = (1 - sigma k) / r := by
  rw [theta]
  apply Real.sin_arcsin
  · have : 0 ≤ (1 - sigma k) / r := div_nonneg (by linarith [sigma_lt_one k]) hr.le
    linarith
  · rw [div_le_one hr]; exact hk

/-- **A generic `c_{i,r}` summand, written as an integral** over `[θ_{k+1,r}, θ_{k,r}]`.

### Summary of Proof
`integral_chord_sin` evaluated between the two angles: the closed form
`(m+b)(θ_k-θ_{k+1}) + m r(cos θ_k - cos θ_{k+1})` is exactly the source's `k`-th summand.

### Lean Notes
Recasting the summands as integrals is what allows the whole `c_{i,r}` series to be compared
against `∫ F_{1+it,r}` in one step, rather than term by term.

### References
tex: the `k`-th term of the sums defining `c_{1,r}`, `c_{2,r}`, `c_{3,r}` after Equation
`\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `integral_chord_sin`, `theta`.
Used by: `arc_majorant_integral`, `arc_majorant_integral_tight`, `c1_eq_integral`, `c1_term_le`,
`c1_term_nonneg`. -/
theorem chord_term_eq_integral {k : ℤ} (m b r : ℝ) :
    (m + b) * (theta k r - theta (k+1) r)
      + m * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))
      = ∫ θ in (theta (k+1) r)..(theta k r), (m * (1 - r * Real.sin θ) + b) := by
  rw [integral_chord_sin]

/-- **The `c_{i,r}` boundary term, written as an integral** over `[θ_{K,r}, π/2]`.

### Summary of Proof
`integral_chord_sin` evaluated between `θ_{K,r}` and `π/2`, giving the source's leading term
`(m_{K-1}+b_{K-1})(π/2 - θ_{K,r}) - m_{K-1} r cos θ_{K,r}` — the `cos(π/2) = 0` endpoint is what
removes the second cosine.

### Lean Notes
This is the `K-1` term that sits outside the sum in each `c_{i,r}`; it covers the arc from the
top of the circle down to the first line that meets the disc.

### References
tex: the leading (boundary) term of each `c_{i,r}` display after Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `integral_chord_sin`, `theta`.
Used by: `arc_majorant_boundary_integral`, `arc_majorant_boundary_integral_tight`,
`c1_boundary_nonneg`, `c1_eq_integral`. -/
theorem chord_boundary_eq_integral (m b r : ℝ) (K : ℤ) :
    (m + b) * (Real.pi / 2 - theta K r) - m * r * Real.cos (theta K r)
      = ∫ θ in (theta K r)..(Real.pi / 2), (m * (1 - r * Real.sin θ) + b) := by
  rw [integral_chord_sin, Real.cos_pi_div_two]; ring

/-- **Each `c₁` summand is nonnegative.**

### Summary of Proof
Write the summand as an integral (`chord_term_eq_integral`) over `[θ_{k+1,r}, θ_{k,r}]`, which is
a genuine interval since the angles decrease (`theta_antitone_succ`). On it the integrand is the
chord evaluated at `1 - r sin θ`, and `sin_theta_eq` places that argument inside `[σ_k, σ_{k+1}]`,
where `chord_vCoeff_nonneg` gives nonnegativity. An integral of a nonnegative function over a
nondegenerate interval is nonnegative.

### References
No tex counterpart as a numbered claim — the source needs the `c_{1,r}` series to converge and be
usable, which its termwise sign makes routine.

### Dependencies
**Depends on:** `bCoeff`, `chord_term_eq_integral`, `chord_vCoeff_nonneg`, `mCoeff`,
`sigma_lt_succ`, `sin_theta_eq`, `theta`, `theta_antitone_succ`, `theta_le_pi_div_two`,
`theta_nonneg`.
Used by: `c1_nonneg`, `c1_summable`. -/
theorem c1_term_nonneg {k : ℤ} {r : ℝ} (hr : 0 < r) (hk : 1 - sigma k ≤ r) :
    0 ≤ (mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
      + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)) := by
  have hk1 : 1 - sigma (k+1) ≤ r := by linarith [sigma_lt_succ k]
  rw [chord_term_eq_integral]
  apply intervalIntegral.integral_nonneg (theta_antitone_succ hr)
  intro θ hθ
  have hθ1 : theta (k+1) r ≤ θ := hθ.1
  have hθ2 : θ ≤ theta k r := hθ.2
  have hlo : (0:ℝ) ≤ theta (k+1) r := theta_nonneg hr
  have hhi : theta k r ≤ Real.pi / 2 := theta_le_pi_div_two k r
  have hpi := Real.pi_pos
  have hs1 : Real.sin (theta (k+1) r) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hθ1
  have hs2 : Real.sin θ ≤ Real.sin (theta k r) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hhi hθ2
  rw [sin_theta_eq hr hk] at hs2
  rw [sin_theta_eq hr hk1] at hs1
  have hA : sigma k ≤ 1 - r * Real.sin θ := by
    have : r * Real.sin θ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr)] at this
    linarith
  have hB : 1 - r * Real.sin θ ≤ sigma (k+1) := by
    have : r * ((1 - sigma (k+1)) / r) ≤ r * Real.sin θ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr)] at this
    linarith
  have := chord_vCoeff_nonneg (k := k) (σ := 1 - r * Real.sin θ) hA hB
  linarith


/-! ### The defining property of `K = Kidx r`

`Kidx r = inf {k : 1 - σ_k ≤ r}`. For `0 < r < 1` that set is nonempty (since `1 - σ_n → 0`,
quantified by `one_sub_sigma_natCast_le_geom`) and bounded below (since `1 - σ_{-j} = σ_j → 1 > r`),
so `Int.csInf_mem` gives `1 - σ_K ≤ r` while minimality gives `r < 1 - σ_{K-1}`, i.e.
`σ_{K-1} < 1 - r ≤ σ_K` — the two facts the `c_{i,r}` boundary term needs. -/

/-- **Geometric decay `1 - σ_n ≤ (3/4)^n`** for `n : ℕ`.

### Summary of Proof
In closed form `1 - σ_n = (n+3)/(2^{n+3}-2)`. The successive ratio is
`(n+4)(2^{n+3}-2)/((n+3)(2^{n+4}-2))`, which is at most `3/4`, so the sequence is dominated by
the geometric one from `n = 0`, where `1 - σ_0 = 1/2 ≤ 1`.

### Lean Notes
The quantitative rate is what makes `Kidx` and `chordIdx` well defined: it shows `σ_n → 1` from
below fast enough to exhibit an explicit index beyond any given `σ < 1`, and by reflection
`σ_k → 0` as `k → -∞`.

### References
No tex counterpart — the source asserts the `σ_k` approach `1` without a rate.

### Dependencies
**Depends on:** `sigma_natCast`.
Used by: `Kidx_set_bddBelow`, `Kidx_set_nonempty`, `chordIdx_set_bddBelow`,
`chordIdx_set_nonempty`, `sigma_tendsto_one`. -/
private theorem one_sub_sigma_natCast_le_geom (n : ℕ) : 1 - sigma (n:ℤ) ≤ (3/4:ℝ)^n := by
  have key : ∀ m : ℕ, ((m:ℝ)+3)/(2^(m+3)-2) ≤ (3/4:ℝ)^m := by
    intro m
    induction m with
    | zero => norm_num
    | succ j ih =>
      have hp : (8:ℝ) ≤ 2^(j+3) := by
        calc (8:ℝ) = 2^(3:ℕ) := by norm_num
          _ ≤ 2^(j+3) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hd1 : (0:ℝ) < 2^(j+3) - 2 := by linarith
      have hd2 : (0:ℝ) < 2 * 2^(j+3) - 2 := by linarith
      have hjp : (0:ℝ) ≤ (j:ℝ) * 2^(j+3) := by positivity
      have hstep : ((j:ℝ)+1+3)/(2*2^(j+3)-2) ≤ (3/4) * (((j:ℝ)+3)/(2^(j+3)-2)) := by
        have hrw : (3:ℝ)/4 * (((j:ℝ)+3)/(2^(j+3)-2))
            = (3*((j:ℝ)+3)/4)/(2^(j+3)-2) := by ring
        rw [hrw, div_le_div_iff₀ hd2 hd1]
        nlinarith [hp, hjp]
      have hgeom : (3/4:ℝ)^(j+1) = (3/4) * (3/4:ℝ)^j := by ring
      have hpow : (2:ℝ)^(j+1+3) = 2 * 2^(j+3) := by ring
      push_cast
      rw [hpow, hgeom]
      calc ((j:ℝ)+1+3)/(2*2^(j+3)-2) ≤ (3/4) * (((j:ℝ)+3)/(2^(j+3)-2)) := hstep
        _ ≤ (3/4) * (3/4:ℝ)^j := by nlinarith [ih]
  rw [sigma_natCast]
  simpa using key n

/-- **The index set defining `Kidx` is nonempty**, for `0 < r`.

### Summary of Proof
By `one_sub_sigma_natCast_le_geom`, `1 - σ_n ≤ (3/4)^n → 0`, so choosing `n` with `(3/4)^n ≤ r`
exhibits an index with `1 - σ_n ≤ r`.

### Lean Notes
Needed before `sInf` can be characterised. The source writes `K = inf_k(r ≥ 1-σ_k)` and treats
its existence as evident.

### References
tex: the definition of `K` after Equation `\ref{eq:thetak}` (Equation 8). No counterpart as a
numbered claim.

### Dependencies
**Depends on:** `one_sub_sigma_natCast_le_geom`.
Used by: `Kidx_mem`. -/
theorem Kidx_set_nonempty {r : ℝ} (hr : 0 < r) : {k : ℤ | 1 - sigma k ≤ r}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (3/4:ℝ) < 1)
  exact ⟨(n:ℤ), by have := one_sub_sigma_natCast_le_geom n; simp only [Set.mem_ofPred_eq]; linarith⟩

/-- **The index set defining `Kidx` is bounded below**, for `r < 1`.

### Summary of Proof
By the reflection `σ_{-j} = 1 - σ_j` and the geometric decay, `σ_k → 0` as `k → -∞`, so
`1 - σ_k → 1`. Choosing `j` with `1 - (3/4)^j > r` gives a floor: any `k < -j` would force
`1 - σ_k > r`, excluding it from the set.

### Lean Notes
Companion to `Kidx_set_nonempty`; together they make the `sInf` in `Kidx` well behaved. Note the
hypothesis `r < 1` is essential — at `r = 1` every line meets the disc and the set really is
unbounded below, which is the source's `K = -∞` case.

### References
tex: the definition of `K` after Equation `\ref{eq:thetak}` (Equation 8), which explicitly admits
`K = -∞`. No counterpart as a numbered claim.

### Dependencies
**Depends on:** `one_sub_sigma_natCast_le_geom`, `sigma_neg_eq`, `sigma_strictMono`.
Used by: `Kidx_mem`, `Kidx_sub_one`. -/
theorem Kidx_set_bddBelow {r : ℝ} (hr1 : r < 1) : BddBelow {k : ℤ | 1 - sigma k ≤ r} := by
  obtain ⟨j0, hj0⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 1 - r)
    (by norm_num : (3/4:ℝ) < 1)
  have hsig : r < sigma (j0:ℤ) := by
    have := one_sub_sigma_natCast_le_geom j0; linarith
  refine ⟨-(j0:ℤ), fun k hk ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hk
  rcases le_or_gt 0 k with hk0 | hk0
  · omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [sigma_neg_eq] at hk
    have : sigma (j:ℤ) < sigma (j0:ℤ) := by linarith
    have hjj : (j:ℤ) < (j0:ℤ) := sigma_strictMono.lt_iff_lt.mp this
    omega

/-- **The infimum defining `Kidx` is attained**: `1 - σ_K ≤ r` at `K = Kidx r`.

### Summary of Proof
A nonempty set of integers bounded below contains its infimum (`Int.csInf_mem`), given
`Kidx_set_nonempty` and `Kidx_set_bddBelow`.

### Lean Notes
This is where the integrality of the index is used: over `ℝ` an infimum need not be attained, but
over `ℤ` it is, so `K` really is a legitimate index rather than only a bound.

### References
tex: the definition of `K` after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_set_bddBelow`, `Kidx_set_nonempty`.
Used by: `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`, `c1_boundary_nonneg`,
`c1_eq_integral`, `c1_nonneg`, `c1_summable`, `half_arc_bound`, `half_arc_bound_tight`. -/
theorem Kidx_mem {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 1 - sigma (Kidx r) ≤ r :=
  Int.csInf_mem (Kidx_set_nonempty hr) (Kidx_set_bddBelow hr1)

/-- **Minimality of `Kidx`**: `r < 1 - σ_{K-1}` at `K = Kidx r`.

### Summary of Proof
If `K-1` were also in the set, `K` would not be the least element, contradicting
`csInf_le` together with `Kidx_set_bddBelow`.

### Lean Notes
This is what makes the `K-1` boundary term of each `c_{i,r}` the correct one: the arc from `π/2`
down to `θ_{K,r}` lies strictly outside every line below `σ_K`.

### References
tex: the definition of `K` after Equation `\ref{eq:thetak}` (Equation 8), and the `K-1` boundary
term of the `c_{i,r}` displays.

### Dependencies
**Depends on:** `Kidx`, `Kidx_set_bddBelow`.
Used by: `arc_boundary_bound_gen`, `arc_boundary_bound_gen_tight`, `c1_boundary_nonneg`,
`c1_eq_integral`. -/
theorem Kidx_sub_one {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) : r < 1 - sigma (Kidx r - 1) := by
  by_contra hc
  push Not at hc
  have hmem : (Kidx r - 1) ∈ {k : ℤ | 1 - sigma k ≤ r} := hc
  have := csInf_le (Kidx_set_bddBelow hr1) hmem
  rw [Kidx] at this
  omega

/-! ### The chord index

Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s majorant is piecewise linear: on the chord
interval
`[σ_k, σ_{k+1})` it is `m_k σ + b_k`. `chordIdx σ` names that `k`, so the majorant can be written as
an honest function of `σ` (`chordA`/`chordA'`/`chordA''` in `JensenBounds`) and integrated over the
arc. Same `sInf` construction as `Kidx`, and well defined for exactly the same reason: `sigma` is
strictly increasing with `σ_k → 1` as `k → ∞` and `σ_k → 0` as `k → -∞`, both at the geometric rate
`(3/4)^{|k|}`. -/

/-- **The chord index of `σ`**: the least `k` with `σ < σ_{k+1}`, equivalently the unique `k`
with `σ_k ≤ σ < σ_{k+1}` when `0 < σ < 1`.

### Summary of Proof
A definition, as an `sInf` over `ℤ`. Its defining property is established in `chordIdx_spec`,
once the index set is shown nonempty and bounded below.

### Lean Notes
The source simply speaks of "the `k` with `σ_k ≤ σ < σ_{k+1}`" as though it evidently exists.
In Lean that `k` has to be constructed, which is what `chordIdx_set_nonempty`,
`chordIdx_set_bddBelow` and `chordIdx_spec` supply.

### References
No explicit tex counterpart — implicit wherever the source selects the chord containing a given
`σ`, e.g. in Theorem `\ref{thm:littlewoodshort}` (Theorem 32)'s hypothesis
`σ_k ≤ 1-r < σ_{k+1}`.

### Dependencies
**Depends on:** `sigma`.
Used by: `arc_pointwise_bound`, `arc_pointwise_bound_sin`, `arc_pointwise_bound_sin_tight`,
`arc_pointwise_bound_tight`, `chordA`, `chordA'`, `chordA''`, `chordA_antitone`, `chordA_star`,
`chordIdx_eq`, `chordIdx_le_of_le`, `chordIdx_spec`. -/
noncomputable def chordIdx (σ : ℝ) : ℤ := sInf {k : ℤ | σ < sigma (k + 1)}

/-- **The index set defining `chordIdx` is nonempty**, for `σ < 1`.

### Summary of Proof
`1 - σ_n ≤ (3/4)^n` (`one_sub_sigma_natCast_le_geom`), so `σ_n → 1` from below. Choosing `n` with
`(3/4)^n < 1 - σ` puts `σ < σ_n`, and `k = n-1` witnesses membership.

### Lean Notes
The source simply speaks of "the `k` with `σ_k ≤ σ < σ_{k+1}`" as though it evidently exists; in
Lean that `k` is obtained as an `sInf`, which needs the set nonempty and bounded below — this
lemma and `chordIdx_set_bddBelow` — before `chordIdx_spec` can characterise it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `one_sub_sigma_natCast_le_geom`.
**Used by:** `chordIdx_spec`. -/
theorem chordIdx_set_nonempty {σ : ℝ} (hσ : σ < 1) : {k : ℤ | σ < sigma (k + 1)}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 1 - σ)
    (by norm_num : (3/4:ℝ) < 1)
  refine ⟨(n:ℤ) - 1, ?_⟩
  have hrw : (n:ℤ) - 1 + 1 = (n:ℤ) := by ring
  simp only [Set.mem_ofPred_eq, hrw]
  have := one_sub_sigma_natCast_le_geom n
  linarith

/-- **The index set defining `chordIdx` is bounded below**, for `σ > 0`.

### Summary of Proof
By the reflection `σ_{-j} = 1 - σ_j` (`sigma_neg_eq`) and `1 - σ_j ≤ (3/4)^j`
(`one_sub_sigma_natCast_le_geom`), `σ_k → 0` as `k → -∞`. Picking `j` with `(3/4)^j < σ` gives a
floor: any `k` below `-j-1` would force `σ_{k+1} ≤ σ_{-j} < σ`, contradicting membership.

### Lean Notes
Companion to `chordIdx_set_nonempty`; together they make the `sInf` in `chordIdx` well behaved.

### References
No tex counterpart.

### Dependencies
**Depends on:** `one_sub_sigma_natCast_le_geom`, `sigma_neg_eq`, `sigma_strictMono`.
**Used by:** `chordIdx_spec`, `chordIdx_le_of_le`. -/
theorem chordIdx_set_bddBelow {σ : ℝ} (hσ : 0 < σ) : BddBelow {k : ℤ | σ < sigma (k + 1)} := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hσ (by norm_num : (3/4:ℝ) < 1)
  refine ⟨-(j:ℤ) - 1, fun k hk ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hk
  by_contra hc
  push Not at hc
  have hmono : sigma (k + 1) ≤ sigma (-(j:ℤ)) := sigma_strictMono.monotone (by omega)
  have h2 : sigma (-(j:ℤ)) = 1 - sigma (j:ℤ) := sigma_neg_eq j
  have h3 := one_sub_sigma_natCast_le_geom j
  rw [h2] at hmono
  linarith

/-- **`σ_k ≤ σ < σ_{k+1}` at `k = chordIdx σ`**, for `0 < σ < 1`.

### Summary of Proof
The upper bound `σ < σ_{k+1}` is membership of the infimum in its own set (`Int.csInf_mem`, using
`chordIdx_set_nonempty` and `chordIdx_set_bddBelow`). The lower bound `σ_k ≤ σ` is minimality: if
`σ < σ_k` then `k-1` would also lie in the set, contradicting `csInf_le`.

### Lean Notes
This is the characterisation that justifies the name — it is what lets every downstream chord
argument write `σ_k ≤ σ < σ_{k+1}` for `k := chordIdx σ`.

### References
No tex counterpart as a numbered claim; the source treats the existence of this `k` as evident.

### Dependencies
**Depends on:** `chordIdx`, `chordIdx_set_bddBelow`, `chordIdx_set_nonempty`.
Used by: `arc_pointwise_bound`, `arc_pointwise_bound_tight`, `chordA_antitone`, `chordA_star`,
`chordIdx_eq`, `chordIdx_le_of_le`, `chordW_le`, `chordW_nonneg`. -/
theorem chordIdx_spec {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    sigma (chordIdx σ) ≤ σ ∧ σ < sigma (chordIdx σ + 1) := by
  refine ⟨?_, Int.csInf_mem (chordIdx_set_nonempty h1) (chordIdx_set_bddBelow h0)⟩
  by_contra hc
  push Not at hc
  have hmem : (chordIdx σ - 1) ∈ {k : ℤ | σ < sigma (k + 1)} := by
    have hrw : chordIdx σ - 1 + 1 = chordIdx σ := by ring
    simp only [Set.mem_ofPred_eq, hrw]
    exact hc
  have hle := csInf_le (chordIdx_set_bddBelow h0) hmem
  rw [chordIdx] at hle
  omega

/-- **The `c₁` boundary term is nonnegative.**

### Summary of Proof
As `c1_term_nonneg`, but on the boundary arc `[θ_{K,r}, π/2]`. Write it as an integral
(`chord_boundary_eq_integral`); `Kidx_mem` and `Kidx_sub_one` place `1 - r sin θ` inside
`[σ_{K-1}, σ_K]` throughout that arc, where `chord_vCoeff_nonneg` gives the integrand's sign.

### References
No tex counterpart as a numbered claim — the boundary term of the `c_{1,r}` display after
Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `Kidx_sub_one`, `bCoeff`, `chord_boundary_eq_integral`,
`chord_vCoeff_nonneg`, `mCoeff`, `sin_theta_eq`, `theta`, `theta_le_pi_div_two`,
`theta_nonneg`.
Used by: `c1_nonneg`. -/
theorem c1_boundary_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 ≤ (mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
      - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r) := by
  have hK := Kidx_mem hr hr1
  have hK1 := Kidx_sub_one hr hr1
  have hpi := Real.pi_pos
  rw [chord_boundary_eq_integral]
  apply intervalIntegral.integral_nonneg (theta_le_pi_div_two _ _)
  intro θ hθ
  have hlo : (0:ℝ) ≤ theta (Kidx r) r := theta_nonneg hr
  have hs1 : Real.sin (theta (Kidx r) r) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hθ.2 hθ.1
  rw [sin_theta_eq hr hK] at hs1
  have hs2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hA : sigma (Kidx r - 1) ≤ 1 - r * Real.sin θ := by nlinarith
  have hB : 1 - r * Real.sin θ ≤ sigma (Kidx r - 1 + 1) := by
    rw [show Kidx r - 1 + 1 = Kidx r by ring]
    have : r * ((1 - sigma (Kidx r)) / r) ≤ r * Real.sin θ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr)] at this
    linarith
  have := chord_vCoeff_nonneg (k := Kidx r - 1) (σ := 1 - r * Real.sin θ) hA hB
  linarith

/-- **`chordIdx` is the unique index with `σ_k ≤ σ < σ_{k+1}`.**

### Summary of Proof
Existence is `chordIdx_spec`. Uniqueness is immediate from strict monotonicity of `sigma`: two
such indices `k' < k` would give `σ < σ_{k'+1} ≤ σ_k ≤ σ`, a contradiction.

### Lean Notes
Stating uniqueness separately is what lets callers that already know `σ_k ≤ σ < σ_{k+1}` for some
particular `k` conclude `k = chordIdx σ`, rather than having to route through the `sInf`.

### References
No tex counterpart as a numbered claim; the source treats the chord containing `σ` as evidently
unique.

### Dependencies
**Depends on:** `chordIdx`, `chordIdx_spec`, `sigma_lt_one`, `sigma_pos`, `sigma_strictMono`.
Used by: `arc_pointwise_bound_sin`, `arc_pointwise_bound_sin_tight`, `chordW_arc_eq`. -/
theorem chordIdx_eq {k : ℤ} {σ : ℝ} (h1 : sigma k ≤ σ) (h2 : σ < sigma (k + 1)) :
    chordIdx σ = k := by
  have h0 : 0 < σ := lt_of_lt_of_le (sigma_pos k) h1
  have hlt1 : σ < 1 := lt_trans h2 (sigma_lt_one (k + 1))
  obtain ⟨hs1, hs2⟩ := chordIdx_spec h0 hlt1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- chordIdx σ < k, so chordIdx σ + 1 ≤ k, so σ < σ_{chordIdx+1} ≤ σ_k ≤ σ
    have : sigma (chordIdx σ + 1) ≤ sigma k := sigma_strictMono.monotone (by omega)
    linarith
  · -- k < chordIdx σ, so k + 1 ≤ chordIdx σ, so σ < σ_{k+1} ≤ σ_{chordIdx} ≤ σ
    have : sigma (k + 1) ≤ sigma (chordIdx σ) := sigma_strictMono.monotone (by omega)
    linarith

/-- **Every `log log|t|` chord slope vanishes**: `mCoeffP k = 0`.

### Summary of Proof
`vCoeffP` is the constant `1`, so the numerator `v_k' - v_{k+1}'` of Equation `\ref{eq:mkp}`
(Equation 6) is `0`, and the quotient with it.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6), together with the display fixing `v_k' = 1`.

### Dependencies
**Depends on:** `mCoeffP`, `vCoeffP`.
Used by: `arc_pointwise_le_maj_sin`, `arc_pointwise_le_maj_sin_tight`, `bCoeffP_eq_one`,
`half_arc_bound`, `half_arc_bound_tight`. -/
theorem mCoeffP_eq_zero (k : ℤ) : mCoeffP k = 0 := by simp [mCoeffP, vCoeffP]

/-- **Every `log log|t|` chord intercept equals `1`**, so that chord is identically `1`.

### Summary of Proof
`b_k' = v_k' - m_k' σ_k = 1 - 0·σ_k = 1`, using `mCoeffP_eq_zero`.

### Lean Notes
Together with `mCoeffP_eq_zero` this collapses the whole `log log|t|` chord to the constant `1`,
which is why `c_{2,r}` reduces to a pure angle sum and is bounded by `π/2`.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `bCoeffP`, `mCoeffP_eq_zero`, `vCoeffP`.
Used by: `arc_pointwise_le_maj_sin`, `arc_pointwise_le_maj_sin_tight`, `half_arc_bound`,
`half_arc_bound_tight`. -/
theorem bCoeffP_eq_one (k : ℤ) : bCoeffP k = 1 := by simp [bCoeffP, vCoeffP, mCoeffP_eq_zero]

/-! ### Uniform bounds and the `θ_{k,r} → 0` limit

Two facts needed to turn Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s *countable*
decomposition of the arc into a convergent sum: the chords are uniformly bounded (so the partial
sums are bounded, hence summable), and `θ_{K+n,r} → 0` (so the partial integrals exhaust
`[0, θ_{K,r}]`). -/

/-- **`v_k ≤ 2/3` at every index.**

### Summary of Proof
For `k ≥ 0`, `v_k = 1/(2^{k+3}-2) ≤ 1/6`. For `k < 0` the mirror formula gives
`v_{-j} = σ_j - 1/2 + v_j ≤ 1 - 1/2 + 1/6 = 2/3`, using `σ_j < 1`.

### Lean Notes
The uniform ceiling is what bounds the `c₁` partial sums, via `chord_vCoeff_le`.

### References
No tex counterpart as a numbered claim — a consequence of the display after Equation
`\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma_lt_one`, `vCoeff`, `vCoeff_natCast`, `vCoeff_neg_eq`.
Used by: `chord_vCoeff_le`. -/
theorem vCoeff_le (k : ℤ) : vCoeff k ≤ 2/3 := by
  have hnat : ∀ n : ℕ, vCoeff (n : ℤ) ≤ 1/6 := by
    intro n
    rw [vCoeff_natCast]
    have h8 : (8:ℝ) ≤ 2 ^ (n + 3) := by
      calc (8:ℝ) = 2 ^ (3:ℕ) := by norm_num
        _ ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with n
    linarith [hnat n]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [vCoeff_neg_eq]
    linarith [hnat j, sigma_lt_one (j:ℤ)]

/-- **The chord `m_k σ + b_k` is at most `2/3` on `[σ_k, σ_{k+1}]`.**

### Summary of Proof
As in `chord_vCoeff_nonneg`, the chord is the convex combination `(1-l)v_k + l v_{k+1}` for
`l ∈ [0,1]`, so it is bounded by the larger of its two endpoint values — both at most `2/3` by
`vCoeff_le`.

### Lean Notes
The companion of `chord_vCoeff_nonneg`; between them the chord is pinned to `[0, 2/3]` on its
interval, which is what makes the arc sum's partial sums bounded.

### References
No tex counterpart as a numbered claim.

### Dependencies
**Depends on:** `bCoeff`, `mCoeff`, `sigma_lt_succ`, `vCoeff`, `vCoeff_le`.
Used by: `arc_pointwise_le_maj_sin`, `arc_pointwise_le_maj_sin_tight`, `c1_term_le`, `chordW_le`. -/
theorem chord_vCoeff_le {k : ℤ} {σ : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ ≤ sigma (k + 1)) :
    mCoeff k * σ + bCoeff k ≤ 2/3 := by
  have hlt := sigma_lt_succ k
  have hd : (0:ℝ) < sigma (k + 1) - sigma k := by linarith
  have hne : sigma k - sigma (k + 1) ≠ 0 := by intro hc; linarith
  set l : ℝ := (σ - sigma k) / (sigma (k + 1) - sigma k) with hl_def
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
  have hl1 : l ≤ 1 := by rw [hl_def, div_le_one hd]; linarith
  have hkey : mCoeff k * σ + bCoeff k = (1 - l) * vCoeff k + l * vCoeff (k + 1) := by
    rw [hl_def]
    simp only [bCoeff, mCoeff]
    field_simp
    ring
  rw [hkey]
  have h1 := vCoeff_le k
  have h2 := vCoeff_le (k + 1)
  nlinarith [h1, h2, hl0, hl1]

/-- **`σ_k → 1` as `k → ∞`.**

### Summary of Proof
Given `ε > 0`, pick `m` with `(3/4)^m < ε`; then `1 - σ_m ≤ (3/4)^m < ε` by
`one_sub_sigma_natCast_le_geom`, and monotonicity of `sigma` extends the estimate to every
`k ≥ m`. Combined with `σ_k < 1` this gives convergence to `1` from below.

### References
tex: the sentence introducing Equation `\ref{eq:sigmak}` (Equation 4), which describes the `σ_k`
as approaching `1`.

### Dependencies
**Depends on:** `one_sub_sigma_natCast_le_geom`, `sigma_lt_one`, `sigma_strictMono`.
Used by: `theta_tendsto_zero`. -/
theorem sigma_tendsto_one : Filter.Tendsto sigma Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (3/4:ℝ) < 1)
  refine ⟨(m:ℤ), fun k hk => ?_⟩
  have hmono : sigma (m:ℤ) ≤ sigma k := sigma_strictMono.monotone hk
  have hgeom : 1 - sigma (m:ℤ) ≤ (3/4:ℝ)^m := one_sub_sigma_natCast_le_geom m
  have h1 : sigma k < 1 := sigma_lt_one k
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

/-- **`θ_{K+n,r} → 0` as `n → ∞`.**

### Summary of Proof
`σ_k → 1` (`sigma_tendsto_one`), so `(1-σ_k)/r → 0`, and `arcsin` is continuous at `0` with
`arcsin 0 = 0`.

### Lean Notes
This is what makes the partition `[0, θ_{K,r}] = ⋃_j [θ_{K+j+1,r}, θ_{K+j,r}]` exhaust the
interval, so that the arc sum really does account for the whole quarter-circle rather than
stopping short.

### References
No tex counterpart — implicit in the source's treatment of the `c_{i,r}` sums as covering the
full arc.

### Dependencies
**Depends on:** `sigma_tendsto_one`, `theta`.
Used by: `hasSum_theta_diff`, `integral_le_tsum_arc`, `tsum_eq_integral_arc`. -/
theorem theta_tendsto_zero (K : ℤ) {r : ℝ} (_hr : 0 < r) :
    Filter.Tendsto (fun n : ℕ => theta (K + n) r) Filter.atTop (nhds 0) := by
  have hidx : Filter.Tendsto (fun n : ℕ => K + (n:ℤ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_left
    exact tendsto_natCast_atTop_atTop
  have hs : Filter.Tendsto (fun n : ℕ => sigma (K + (n:ℤ))) Filter.atTop (nhds 1) :=
    sigma_tendsto_one.comp hidx
  have hq : Filter.Tendsto (fun n : ℕ => (1 - sigma (K + (n:ℤ))) / r) Filter.atTop (nhds 0) := by
    have := (Filter.Tendsto.const_sub 1 hs).div_const r
    simpa using this
  have hcomp := (Real.continuous_arcsin.tendsto 0).comp hq
  simp only [Function.comp_def, Real.arcsin_zero] at hcomp
  simpa [theta] using hcomp

/-- **Each `c₁` summand is at most `(2/3)(θ_{k,r} - θ_{k+1,r})`.**

### Summary of Proof
The companion of `c1_term_nonneg`: apply `chord_vCoeff_le` — the chord is at most `2/3` on its
interval — to the same integral representation, and integrate the constant bound over an arc of
length `θ_{k,r} - θ_{k+1,r}`.

### Lean Notes
Comparing against a telescoping series is what makes the `c₁` sum summable; see `c1_summable`.

### References
No tex counterpart as a numbered claim — the source asserts convergence of these sums in one
sentence after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `bCoeff`, `chord_term_eq_integral`, `chord_vCoeff_le`, `mCoeff`,
`sigma_lt_succ`, `sin_theta_eq`, `theta`, `theta_antitone_succ`, `theta_le_pi_div_two`,
`theta_nonneg`.
Used by: `c1_summable`. -/
theorem c1_term_le {k : ℤ} {r : ℝ} (hr : 0 < r) (hk : 1 - sigma k ≤ r) :
    (mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
      + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))
      ≤ 2/3 * (theta k r - theta (k+1) r) := by
  have hk1 : 1 - sigma (k+1) ≤ r := by linarith [sigma_lt_succ k]
  have hle : theta (k+1) r ≤ theta k r := theta_antitone_succ hr
  rw [chord_term_eq_integral]
  have hconst : (2:ℝ)/3 * (theta k r - theta (k+1) r)
      = ∫ _θ in (theta (k+1) r)..(theta k r), (2:ℝ)/3 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst]
  refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const ?_
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro θ hθ
  have hθ1 : theta (k+1) r ≤ θ := hθ.1
  have hθ2 : θ ≤ theta k r := hθ.2
  have hlo : (0:ℝ) ≤ theta (k+1) r := theta_nonneg hr
  have hhi : theta k r ≤ Real.pi / 2 := theta_le_pi_div_two k r
  have hpi := Real.pi_pos
  have hs1 : Real.sin (theta (k+1) r) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hθ1
  have hs2 : Real.sin θ ≤ Real.sin (theta k r) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hhi hθ2
  rw [sin_theta_eq hr hk] at hs2
  rw [sin_theta_eq hr hk1] at hs1
  have hA : sigma k ≤ 1 - r * Real.sin θ := by
    have h : r * Real.sin θ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr)] at h
    linarith
  have hB : 1 - r * Real.sin θ ≤ sigma (k+1) := by
    have h : r * ((1 - sigma (k+1)) / r) ≤ r * Real.sin θ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr)] at h
    linarith
  have := chord_vCoeff_le (k := k) (σ := 1 - r * Real.sin θ) hA hB
  linarith

/-- **The `c₁` series converges.**

### Summary of Proof
Its terms are nonnegative (`c1_term_nonneg`), so it suffices to bound the partial sums. By
`c1_term_le` each term is at most `(2/3)(θ_{k,r} - θ_{k+1,r})`, and those telescope
(`sum_range_theta_telescope`) to at most `(2/3)·θ_{K,r} ≤ π/3`. A nonnegative series with bounded
partial sums converges.

### Lean Notes
This discharges, for `c₁`, the source's one-sentence assertion that "every sum above is rapidly
convergent, even if `K = -∞`".

### References
tex: the sentence following the `c_{i,r}` displays after Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `bCoeff`, `c1_term_le`, `c1_term_nonneg`, `mCoeff`,
`sigma_strictMono`, `sum_range_theta_telescope`, `theta`, `theta_nonneg`.
Used by: `c1_eq_integral`, `half_arc_bound`, `half_arc_bound_tight`. -/
theorem c1_summable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun j : ℕ =>
      (mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeff (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))) := by
  have hK := Kidx_mem hr hr1
  have hidx : ∀ j : ℕ, 1 - sigma (Kidx r + j) ≤ r := by
    intro j
    have hmono : sigma (Kidx r) ≤ sigma (Kidx r + j) := sigma_strictMono.monotone (by omega)
    linarith
  refine summable_of_sum_range_le (c := 2/3 * theta (Kidx r) r) ?_ ?_
  · intro j; exact c1_term_nonneg hr (hidx j)
  · intro n
    have hle : ∀ j ∈ Finset.range n,
        (mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
            * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
          + mCoeff (Kidx r + j) * r
              * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))
          ≤ 2/3 * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r) :=
      fun j _ => c1_term_le hr (hidx j)
    calc _ ≤ ∑ j ∈ Finset.range n,
            2/3 * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r) := Finset.sum_le_sum hle
      _ = 2/3 * (theta (Kidx r) r - theta (Kidx r + n) r) := by
          rw [← Finset.mul_sum, sum_range_theta_telescope]
      _ ≤ 2/3 * theta (Kidx r) r := by
          have := theta_nonneg (k := Kidx r + n) hr
          linarith

/-- **The telescoping angle series `Σ_j (θ_{K+j,r} - θ_{K+j+1,r})` converges.**

### Summary of Proof
Its terms are nonnegative (`theta_antitone_succ`) and its partial sums telescope
(`sum_range_theta_telescope`) to `θ_{K,r} - θ_{K+n,r} ≤ θ_{K,r}`, so they are bounded.

### Lean Notes
This is the comparison series for the `c₂` and `c₃` sums, whose own terms need **not** be
nonnegative — so unlike `c₁` they cannot be handled by a partial-sum bound directly, and need an
absolutely convergent dominating series instead.

### References
tex: the convergence sentence after the `c_{i,r}` displays following Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `sum_range_theta_telescope`, `theta`, `theta_antitone_succ`, `theta_nonneg`.
Used by: `c3_summable`, `hasSum_theta_diff`. -/
theorem theta_diff_summable (K : ℤ) {r : ℝ} (hr : 0 < r) :
    Summable (fun j : ℕ => theta (K + j) r - theta (K + j + 1) r) := by
  refine summable_of_sum_range_le (c := theta K r) ?_ ?_
  · intro j; linarith [theta_antitone_succ (k := K + j) hr]
  · intro n
    rw [sum_range_theta_telescope]
    linarith [theta_nonneg (k := K + n) hr]

/-! ### The countable arc decomposition

Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s "integrate term-by-term and regroup by `k`"
is a *countable* decomposition: `[0, θ_{K,r}] = ⋃_{j≥0} [θ_{K+j+1,r}, θ_{K+j,r}]`, exhausting
because `θ_{K+n,r} → 0` (`theta_tendsto_zero`). The three lemmas below turn that into a bound —
finite telescoping, continuity of the primitive in its lower endpoint, and the limit. -/

/-- **`u ↦ ∫_u^b f` is continuous** when `f` is interval integrable everywhere.

### Summary of Proof
Write `∫_u^b f = -∫_b^u f` and apply Mathlib's `intervalIntegral.continuous_primitive`, which
covers the upper-endpoint case; negation is continuous.

### Lean Notes
A general-purpose gap-filler: Mathlib supplies continuity of the primitive in its *upper*
endpoint, and this is the *lower*-endpoint companion. Needed because the arc integrals here are
naturally parameterised by their lower limit.

### References
No tex counterpart — pure real analysis.

### Dependencies
**Depends on:** none.
Used by: `integral_le_tsum_arc`, `tsum_eq_integral_arc`. -/
theorem continuous_primitive_left {f : ℝ → ℝ}
    (h_int : ∀ u v : ℝ, IntervalIntegrable f MeasureTheory.volume u v) (b : ℝ) :
    Continuous fun u => ∫ x in u..b, f x := by
  have he : (fun u => ∫ x in u..b, f x) = fun u => -(∫ x in b..u, f x) := by
    funext u; rw [intervalIntegral.integral_symm]
  rw [he]
  exact (intervalIntegral.continuous_primitive h_int b).neg

/-- **The finite arc decomposition**: `[θ_{K+n,r}, θ_{K,r}]` is the union of the `n` adjacent
intervals `[θ_{K+j+1,r}, θ_{K+j,r}]`, `j < n`.

### Summary of Proof
Induction on `n`, using additivity of the interval integral across a shared endpoint and the fact
that the angles decrease (`theta_antitone_succ`), so the intervals abut in the right order.

### Lean Notes
This is the finite stage of the argument; `theta_tendsto_zero` then lets `n → ∞` so that the
union exhausts `[0, θ_{K,r}]`.

### References
No tex counterpart — the source treats the decomposition of the arc into chord pieces as evident
from the geometry.

### Dependencies
**Depends on:** `theta`.
Used by: `integral_le_tsum_arc`, `tsum_eq_integral_arc`. -/
theorem arc_partial_sum {f : ℝ → ℝ} {K : ℤ} {r : ℝ}
    (hint : ∀ u v : ℝ, IntervalIntegrable f MeasureTheory.volume u v) (n : ℕ) :
    ∑ j ∈ Finset.range n, (∫ φ in (theta (K + j + 1) r)..(theta (K + j) r), f φ)
      = ∫ φ in (theta (K + n) r)..(theta K r), f φ := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := fun j : ℕ => theta (K + (j:ℤ)) r) (n := n) (fun k _ => hint _ _)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at h
  have hstep : ∀ k : ℕ, (∫ φ in (theta (K + k + 1) r)..(theta (K + k) r), f φ)
      = -(∫ φ in (theta (K + (k:ℤ)) r)..(theta (K + (k:ℤ) + 1) r), f φ) := by
    intro k
    rw [intervalIntegral.integral_symm]
  rw [Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_neg_distrib, h,
    intervalIntegral.integral_symm, neg_neg]

/-- **The countable arc bound.** If `f` is interval integrable and dominated on each piece
`[θ_{K+j+1,r}, θ_{K+j,r}]` by a summable sequence `g`, then `∫_0^{θ_{K,r}} f ≤ Σ' g`.

### Summary of Proof
The limit form of the source's "regrouping by `k`" step. Over the first `n` pieces the integral
splits by `arc_partial_sum` and is bounded by the corresponding partial sum of `g`. Letting
`n → ∞`, `theta_tendsto_zero` makes the pieces exhaust `[0, θ_{K,r}]`, and
`continuous_primitive_left` lets the integral over `[θ_{K+n,r}, θ_{K,r}]` converge to the
integral over `[0, θ_{K,r}]`.

### References
tex: the regrouping of `∫ F_{1+it,r}` into chord pieces that produces the `c_{i,r}` displays
after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `arc_partial_sum`, `continuous_primitive_left`, `theta`, `theta_tendsto_zero`.
Used by: `half_arc_bound`, `half_arc_bound_tight`. -/
theorem integral_le_tsum_arc {f : ℝ → ℝ} {g : ℕ → ℝ} {K : ℤ} {r : ℝ} (hr : 0 < r)
    (hint : ∀ u v : ℝ, IntervalIntegrable f MeasureTheory.volume u v)
    (hg : Summable g)
    (hle : ∀ j : ℕ, (∫ φ in (theta (K + j + 1) r)..(theta (K + j) r), f φ) ≤ g j) :
    (∫ φ in (0:ℝ)..(theta K r), f φ) ≤ ∑' j, g j := by
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ φ in (theta (K + n) r)..(theta K r), f φ)
      Filter.atTop (nhds (∫ φ in (0:ℝ)..(theta K r), f φ)) := by
    have hc := (continuous_primitive_left hint (theta K r)).continuousAt (x := (0:ℝ))
    exact hc.tendsto.comp (theta_tendsto_zero K hr)
  have hpartial : ∀ n : ℕ, (∫ φ in (theta (K + n) r)..(theta K r), f φ)
      ≤ ∑ j ∈ Finset.range n, g j := by
    intro n
    rw [← arc_partial_sum hint n]
    exact Finset.sum_le_sum (fun j _ => hle j)
  exact le_of_tendsto_of_tendsto' hlim hg.hasSum.tendsto_sum_nat hpartial

/-! ### The `c_{i,r}` constants

**What `c_{i,r}` is.** Parametrise the left half of the circle `1 + it + re^{iφ}` by
`σ = 1 - r sin θ`, `θ ∈ [0, π/2]` (so `φ = π/2 + θ`; note `σ_k = 1 - r sin θ_{k,r}` by
`(eq:thetak)`, and `θ ∈ (θ_{k+1,r}, θ_{k,r}]` is exactly `σ ∈ [σ_k, σ_{k+1})`). Then

  `c_{1,r} = ∫_0^{π/2} A(1 - r sin θ) dθ`,  `A(σ) := m_k σ + b_k` on `[σ_k, σ_{k+1}]`,

and likewise `c_{2,r}`, `c_{3,r}` with `A'`, `A''`. This makes `c_{1,r} ≥ 0` manifest, since
`A ≥ 0` (`chord_vCoeff_nonneg`) — a sign `RectangularBounds.rectangularjensen` needs.

Evaluating that integral piecewise gives the closed form used below,

  `c_{1,r} = (m_{K-1}+b_{K-1})(π/2 - θ_{K,r}) - m_{K-1}·r·cos θ_{K,r}`
          `+ Σ_{k≥K} [ (m_k+b_k)(θ_{k,r} - θ_{k+1,r}) + m_k·r·(cos θ_{k,r} - cos θ_{k+1,r}) ]`

which is the source's own display after Equation `\ref{eq:thetak}` (Equation 8), term for term.
Two features of it are worth spelling out, since they are easy to get wrong: the constant part of
`A(1 - r sin θ)` is `m_k·1 + b_k` and not `b_k`, because the parametrisation is centred at
`σ = 1`; and the boundary term is indexed `K-1`, not `K`, because on `θ ∈ (θ_{K,r}, π/2]` one has
`σ ∈ [1-r, σ_K)`, which by `σ_{K-1} < 1-r ≤ σ_K` lies in the *single* chord interval indexed
`K-1`.

**Verified numerically against the source's own Table `\ref{tab:crvalues}` (Table 2)** (250-digit
`mpmath`, tail to `k = K+80`), agreeing to 9 significant digits at `r = 1/2, 1/3, 1/4, 1/6` —
*provided* one uses the **alternate** `k = 0` coefficients of `Remark \ref{rem:altcoefficients}`
(Remark 7), `v_0 = 27/164`, `v_0' = 0`; with the main text's `v_0 = 1/6`, `v_0' = 1` the values
differ at those `r` where the `k = 0` chord is reached (`r ≥ 1/3`) and agree exactly where it is
not (`r = 1/4, 1/6`). So the table was computed with the alternate variant; the definitions here
use the main-text one. -/

/-- **`c_{1,r}`**, the coefficient of `log|t|/π` in Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Summary of Proof
A definition, transcribing the source's display: a boundary term
`(m_{K-1}+b_{K-1})(π/2 - θ_{K,r}) - m_{K-1} r cos θ_{K,r}` plus the series
`Σ_{k≥K} [(m_k+b_k)(θ_{k,r}-θ_{k+1,r}) + m_k r(cos θ_{k,r} - cos θ_{k+1,r})]`.

### Lean Notes
The series is a `tsum`, which Lean gives the value `0` when not summable; `c1_summable` supplies
the convergence that makes this the intended quantity.

Its numeric value depends on the `v₀` choice — see `vCoeff`. Under the main-text triple used here
`c_{1,1/2} = 0.14807`, against the `0.14679` of Table `\ref{tab:crvalues}` (Table 2), computed
with the Remark's triple. The tex's own remark just after Proposition `\ref{prop:jensen-easy}`
(Proposition 8) quotes `0.1480612309` for this value, agreeing with the main-text triple used
here rather than with its own table.

### References
tex: the `c_{1,r}` display following Equation `\ref{eq:thetak}` (Equation 8); used in
Proposition `\ref{prop:jensen-easy}` (Proposition 8) and tabulated in Table
`\ref{tab:crvalues}` (Table 2).

### Dependencies
**Depends on:** `Kidx`, `bCoeff`, `mCoeff`, `theta`.
Used by: `A4`, `B1`, `C1`, `C1_scaling`, `FcrZeta_integral_le`, `FcrZeta_outside_integral`,
`c1_eq_integral`, `c1_nonneg`, `c1_scaling`, `circularregions1`, `circularregions1_tight`,
`half_arc_bound`, `half_arc_bound_tight`, `interpolated_bound_1c`, `jensen_easy`,
`jensen_easy_lower_quarter`, `jensen_easy_lower_quarter_tight`, `jensen_easy_tight`,
`jensen_easy_upper_quarter`, `jensen_easy_upper_quarter_tight`, `littlewoodshort`,
`littlewoodshort_tight`, `log_bound_of_interp_1c`, `rectangularjensen`, `rectangularjensen_tight`.
-/
noncomputable def c1 (r : ℝ) : ℝ :=
  (mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeff (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- **`c_{2,r}`**, the coefficient of `log log|t|/π` in Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Summary of Proof
A definition, the same shape as `c1` but built from the primed chord data `m_k'`, `b_k'`. Because
those collapse to `m_k' = 0`, `b_k' = 1` (`mCoeffP_eq_zero`, `bCoeffP_eq_one`), the whole
expression telescopes to `π/2` — see `c2_nonneg` and `c2_le_pi_div_two`.

### References
tex: the `c_{2,r}` display following Equation `\ref{eq:thetak}` (Equation 8); used in
Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `Kidx`, `bCoeffP`, `mCoeffP`, `theta`.
Used by: `A5`, `B2`, `C2`, `C2_scaling`, `FcrZeta_integral_le`, `FcrZeta_outside_integral`,
`c2_le_pi_div_two`, `c2_nonneg`, `circularregions1`, `circularregions1_tight`, `half_arc_bound`,
`half_arc_bound_tight`, `jensen_easy`, `jensen_easy_lower_quarter`,
`jensen_easy_lower_quarter_tight`, `jensen_easy_tight`, `jensen_easy_upper_quarter`,
`jensen_easy_upper_quarter_tight`, `littlewoodshort`, `littlewoodshort_tight`,
`rectangularjensen`, `rectangularjensen_tight`. -/
noncomputable def c2 (r : ℝ) : ℝ :=
  (mCoeffP (Kidx r - 1) + bCoeffP (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeffP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- **`c_{3,r}`**, the constant-term coefficient (divided by `π`) in Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Summary of Proof
A definition, the same shape as `c1` but built from the double-primed chord data `m_k''`,
`b_k''`. Its tail is summable because those vanish for `k > 0` (`mCoeffPP_eq_zero_of_pos`), so
only finitely many terms are non-constant — see `c3_summable`.

### Lean Notes
Like `c1`, its numeric value depends on the `v₀''` choice. Under the main-text triple used here
`c_{3,1/2} = 0.0982`, against the `3.0615` of Table `\ref{tab:crvalues}` (Table 2), computed with
the Remark's triple — a factor of 31. See `vCoeff` and this file's module docstring.

### References
tex: the `c_{3,r}` display following Equation `\ref{eq:thetak}` (Equation 8); used in
Proposition `\ref{prop:jensen-easy}` (Proposition 8) and tabulated in Table
`\ref{tab:crvalues}` (Table 2).

### Dependencies
**Depends on:** `Kidx`, `bCoeffPP`, `mCoeffPP`, `theta`.
Used by: `A6`, `B3`, `C3`, `FcrZeta_integral_le`, `FcrZeta_outside_integral`, `circularregions1`,
`circularregions1_tight`, `half_arc_bound`, `half_arc_bound_tight`, `jensen_easy`,
`jensen_easy_lower_quarter`, `jensen_easy_lower_quarter_tight`, `jensen_easy_tight`,
`jensen_easy_upper_quarter`, `jensen_easy_upper_quarter_tight`, `littlewoodshort`,
`littlewoodshort_tight`, `rectangularjensen`, `rectangularjensen_tight`. -/
noncomputable def c3 (r : ℝ) : ℝ :=
  (mCoeffPP (Kidx r - 1) + bCoeffPP (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeffPP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeffPP (Kidx r + j) + bCoeffPP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffPP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- **`0 ≤ c_{1,r}` for `0 < r < 1`.**

### Summary of Proof
`c_{1,r}` is `∫_0^{π/2} A(1 - r sin θ)dθ` with the chord `A ≥ 0`, and in the closed form each
piece of that integral is nonnegative — the boundary term by `c1_boundary_nonneg`, each series
term by `c1_term_nonneg`.

### Lean Notes
No summability is needed: the `tsum` is nonnegative termwise, and Lean gives a non-summable
`tsum` the value `0`, which is also nonnegative.

This is exactly the sign fact `RectangularBounds.rectangularjensen` needs in order to push the
concavity of `log` through `JensenBounds.jensen_easy`'s bound when integrating over the window.

### References
tex: the `c_{1,r}` display after Equation `\ref{eq:thetak}` (Equation 8); the sign is the
author's observation, used but not separately numbered.

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `bCoeff`, `c1`, `c1_boundary_nonneg`, `c1_term_nonneg`,
`mCoeff`, `sigma_strictMono`, `theta`.
Used by: `littlewoodshort`, `littlewoodshort_tight`, `rectangularjensen`,
`rectangularjensen_tight`. -/
theorem c1_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 ≤ c1 r := by
  have hK := Kidx_mem hr hr1
  have hb := c1_boundary_nonneg hr hr1
  have ht : (0:ℝ) ≤ ∑' j : ℕ,
      ((mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeff (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))) := by
    apply tsum_nonneg
    intro j
    refine c1_term_nonneg hr ?_
    have hmono : sigma (Kidx r) ≤ sigma (Kidx r + j) :=
      sigma_strictMono.monotone (by omega)
    linarith
  rw [c1]
  linarith

/-- **`0 ≤ c_{2,r}`.**

### Summary of Proof
Since `v_k' ≡ 1`, every slope `m_k'` vanishes and every intercept `b_k'` equals `1`
(`mCoeffP_eq_zero`, `bCoeffP_eq_one`), so the definition collapses to
`c_{2,r} = (π/2 - θ_{K,r}) + Σ_{k≥K}(θ_{k,r} - θ_{k+1,r})`. Every summand is nonnegative, by
`theta_le_pi_div_two` and `theta_antitone_succ`.

### Lean Notes
In fact `c_{2,r} = π/2` exactly; `JensenBounds.c2_le_pi_div_two` is the matching upper bound.

### References
tex: the `c_{2,r}` display after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `Kidx`, `bCoeffP`, `c2`, `mCoeffP`, `theta`, `theta_antitone_succ`,
`theta_le_pi_div_two`, `vCoeffP`.
Used by: `littlewoodshort`, `littlewoodshort_tight`, `rectangularjensen`,
`rectangularjensen_tight`. -/
theorem c2_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ c2 r := by
  have hm : ∀ k : ℤ, mCoeffP k = 0 := by
    intro k; simp [mCoeffP, vCoeffP]
  have hb : ∀ k : ℤ, bCoeffP k = 1 := by
    intro k; simp [bCoeffP, vCoeffP, hm]
  rw [c2]
  simp only [hm, hb, zero_add, zero_mul, add_zero, one_mul, sub_zero]
  have ht : (0:ℝ) ≤ ∑' j : ℕ, (theta (Kidx r + j) r - theta (Kidx r + j + 1) r) := by
    apply tsum_nonneg
    intro j
    linarith [theta_antitone_succ (k := Kidx r + j) hr]
  linarith [theta_le_pi_div_two (Kidx r) r]

/-! ### Exact values of the telescoping `θ`-series, and summability of the `c₃` series

`half_arc_bound` in `JensenBounds` needs three things beyond `c1_summable`: the *value* of the
telescoping series `Σ_j (θ_{K+j,r} - θ_{K+j+1,r})` (it is `θ_{K,r}`, and it carries the `O^*(·)`
slack of `zeta_piecewise_bound` across the countable decomposition), and summability of the `c₂`
and `c₃` series. The `c₂` one is the telescoping series itself (`v_k' ≡ 1`); the `c₃` one has a
constant tail, since `v_k'' = log 1.546` for every `k > 0`. -/

/-- **The telescoping angle series sums to `θ_{K,r}`**:
`Σ_{j≥0} (θ_{K+j,r} - θ_{K+j+1,r}) = θ_{K,r}`.

### Summary of Proof
The partial sums are `θ_{K,r} - θ_{K+n,r}` (`sum_range_theta_telescope`), and
`θ_{K+n,r} → 0` (`theta_tendsto_zero`), so they converge to `θ_{K,r}`. Summability is
`theta_diff_summable`.

### References
No tex counterpart as a numbered claim — the exact value the source's convergence remark
implicitly relies on.

### Dependencies
**Depends on:** `sum_range_theta_telescope`, `theta`, `theta_diff_summable`,
`theta_tendsto_zero`.
Used by: `half_arc_bound`, `half_arc_bound_tight`. -/
theorem hasSum_theta_diff (K : ℤ) {r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => theta (K + j) r - theta (K + j + 1) r) (theta K r) := by
  have hs := theta_diff_summable K hr
  have h1 := hs.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n,
      (theta (K + j) r - theta (K + j + 1) r)) Filter.atTop (nhds (theta K r)) := by
    have he : (fun n : ℕ => ∑ j ∈ Finset.range n, (theta (K + j) r - theta (K + j + 1) r))
        = fun n : ℕ => theta K r - theta (K + n) r :=
      funext fun n => sum_range_theta_telescope K r n
    rw [he]
    simpa using (tendsto_const_nhds (x := theta K r) (f := Filter.atTop (α := ℕ))).sub
      (theta_tendsto_zero K hr)
  rw [show theta K r = ∑' j : ℕ, (theta (K + j) r - theta (K + j + 1) r) from
    tendsto_nhds_unique h2 h1]
  exact hs.hasSum

/-- **The constant-term chord slope vanishes for `k > 0`**: `mCoeffPP k = 0`.

### Summary of Proof
For `k > 0` both `v_k''` and `v_{k+1}''` equal `log 1.546`, so the numerator of Equation
`\ref{eq:mkpp}` (Equation 7) vanishes.

### Lean Notes
This is what truncates the `c₃` series: only finitely many terms are non-constant, which is why
`c3_summable` needs no decay estimate.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7) and the display fixing `v_k'' = log(1.546)` for
`k > 0`.

### Dependencies
**Depends on:** `mCoeffPP`, `vCoeffPP`.
Used by: `bCoeffPP_eq_of_pos`, `c3_summable`. -/
theorem mCoeffPP_eq_zero_of_pos {k : ℤ} (hk : 0 < k) : mCoeffPP k = 0 := by
  unfold mCoeffPP vCoeffPP
  rw [ite_eq_left hk, ite_eq_left (by omega : (0:ℤ) < k + 1)]
  simp

/-- **The constant-term chord equals `log 1.546` for `k > 0`**: `bCoeffPP k = log 1.546`.

### Summary of Proof
`b_k'' = v_k'' - m_k'' σ_k = log 1.546 - 0·σ_k`, using `mCoeffPP_eq_zero_of_pos`.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `bCoeffPP`, `mCoeffPP_eq_zero_of_pos`, `vCoeffPP`.
Used by: `c3_summable`. -/
theorem bCoeffPP_eq_of_pos {k : ℤ} (hk : 0 < k) : bCoeffPP k = Real.log 1.546 := by
  unfold bCoeffPP vCoeffPP
  rw [ite_eq_left hk, mCoeffPP_eq_zero_of_pos hk]
  ring

/-- **The `c₃` series converges.**

### Summary of Proof
Past `k = 0` the chord data is constant (`mCoeffPP_eq_zero_of_pos`, `bCoeffPP_eq_of_pos`), so
those terms are just `log(1.546)·(θ_{k,r} - θ_{k+1,r})`. Summability therefore reduces to
`theta_diff_summable` after dropping the finitely many terms with `k ≤ 0`.

### Lean Notes
Unlike `c₁`, the `c₃` terms need not be nonnegative — `log 1.546 > 0` but the `k ≤ 0` terms
involve `log 0.611 < 0` — so a partial-sum bound would not suffice and an absolutely convergent
dominating series is needed.

### References
tex: the convergence sentence after the `c_{i,r}` displays following Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `Kidx`, `bCoeffPP`, `bCoeffPP_eq_of_pos`, `mCoeffPP`,
`mCoeffPP_eq_zero_of_pos`, `theta`, `theta_diff_summable`.
Used by: `half_arc_bound`, `half_arc_bound_tight`. -/
theorem c3_summable {r : ℝ} (hr : 0 < r) :
    Summable (fun j : ℕ =>
      (mCoeffPP (Kidx r + j) + bCoeffPP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffPP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < Kidx r + N := ⟨(1 - Kidx r).toNat, by omega⟩
  rw [← summable_nat_add_iff N]
  have hpos : ∀ j : ℕ, 0 < Kidx r + ((j + N : ℕ) : ℤ) := by
    intro j; push_cast; omega
  have he : ∀ j : ℕ,
      (mCoeffPP (Kidx r + ((j + N : ℕ) : ℤ)) + bCoeffPP (Kidx r + ((j + N : ℕ) : ℤ)))
          * (theta (Kidx r + ((j + N : ℕ) : ℤ)) r - theta (Kidx r + ((j + N : ℕ) : ℤ) + 1) r)
        + mCoeffPP (Kidx r + ((j + N : ℕ) : ℤ)) * r
            * (Real.cos (theta (Kidx r + ((j + N : ℕ) : ℤ)) r)
                - Real.cos (theta (Kidx r + ((j + N : ℕ) : ℤ) + 1) r))
      = Real.log 1.546
          * (theta (Kidx r + N + (j : ℤ)) r - theta (Kidx r + N + (j : ℤ) + 1) r) := by
    intro j
    rw [mCoeffPP_eq_zero_of_pos (hpos j), bCoeffPP_eq_of_pos (hpos j),
      show Kidx r + ((j + N : ℕ) : ℤ) = Kidx r + N + (j : ℤ) by push_cast; ring]
    ring
  exact (Summable.congr (((theta_diff_summable (Kidx r + N) hr).mul_left (Real.log 1.546)))
    (fun j => (he j).symm))

/-! ### Star-shapedness of the chord data: `v_k/(1-σ_k)` is strictly decreasing in `k`

`Proposition \ref{prop:Cscaling}` (Proposition 17) (formalized as `JensenBounds.c1_scaling`)
justifies `c_{1,λr} ≤ λ·c_{1,r}` by asserting, among other things, `m_k + b_k ≤ 0`. That is the
quantity the argument needs — the constant term of the chord written in the arc variable, since
`A_k(1 - r sin φ) = (m_k + b_k) - m_k·r sin φ` — and it is proved strictly below as
`mCoeff_add_bCoeff_neg`. Note that the *summands* have opposite signs: `m_k < 0` (`mCoeff_neg`)
while `b_k > 0` (`bCoeff_pos`; e.g. `b_0 = 7/18`, and `b_k → 1/2` as `k → -∞`), with `|m_k| > b_k`.

And `m_k + b_k < 0` is *exactly* `v_k/(1-σ_k) > v_{k+1}/(1-σ_{k+1})` (`vCoeff_ratio_step`), i.e. the
chord function is **star-shaped about `σ = 1`** — which is in turn exactly why `r ↦ c_{1,r}/r` is
nondecreasing. For `k ≥ 0` the ratio is `1/(k+3)` on the nose; for `k < 0` it increases to `1/2`. -/

/-- **The nonnegative branch of `vCoeff_ratio_step`**, with `P = 2^{n+3}` abstracted.

### Summary of Proof
Pure algebra: with `P := 2^{n+3}` the difference of consecutive ratios is `1/((P-2)(2P-2))`,
visibly positive for `P ≥ 8`.

### Lean Notes
Abstracting the power to a variable `P` is what lets `field_simp`/`ring` handle the identity;
leaving `2^{n+3}` in place defeats them.

### References
No tex counterpart — the source does not discuss the monotonicity of `v_k/(1-σ_k)`.

### Dependencies
**Depends on:** none.
Used by: `vCoeff_ratio_step`. -/
private theorem ratio_step_pos_aux (n : ℕ) (P : ℝ) (hP : 8 ≤ P) :
    1/(2*P-2) * (1 - (1 - ((n:ℝ)+3)/(P-2)))
      < 1/(P-2) * (1 - (1 - ((n:ℝ)+1+3)/(2*P-2))) := by
  have h1 : (0:ℝ) < P - 2 := by linarith
  have h2 : (0:ℝ) < 2*P - 2 := by linarith
  have h1' : (P - 2) ≠ 0 := ne_of_gt h1
  have h2' : (2*P - 2) ≠ 0 := ne_of_gt h2
  rw [← sub_pos]
  have hid : 1/(P-2) * (1 - (1 - ((n:ℝ)+1+3)/(2*P-2)))
      - 1/(2*P-2) * (1 - (1 - ((n:ℝ)+3)/(P-2)))
      = 1 / ((P-2) * (2*P-2)) := by
    field_simp
    ring
  rw [hid]
  exact div_pos one_pos (mul_pos h1 h2)

/-- **The negative branch of `vCoeff_ratio_step`**, with `P = 2^{i+3}` abstracted.

### Summary of Proof
Pure algebra: with `P := 2^{i+3}` the difference of consecutive ratios is
`(P·i + 4)/(4(P-2)(P-1))`, visibly positive for `P ≥ 8` and `i ≥ 0`.

### Lean Notes
As `ratio_step_pos_aux`, the power is abstracted so the identity is in reach of `field_simp`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
Used by: `vCoeff_ratio_step`. -/
private theorem ratio_step_neg_aux (i : ℕ) (P : ℝ) (hP : 8 ≤ P) :
    ((1 - ((i:ℝ)+3)/(P-2)) - 1/2 + 1/(P-2)) * (1 - ((i:ℝ)+1+3)/(2*P-2))
      < ((1 - ((i:ℝ)+1+3)/(2*P-2)) - 1/2 + 1/(2*P-2)) * (1 - ((i:ℝ)+3)/(P-2)) := by
  have h1 : (0:ℝ) < P - 2 := by linarith
  have h2 : (0:ℝ) < 2*P - 2 := by linarith
  have h3 : (0:ℝ) < P - 1 := by linarith
  have h1' : (P - 2) ≠ 0 := ne_of_gt h1
  have h2' : (2*P - 2) ≠ 0 := ne_of_gt h2
  have h3' : (P - 1) ≠ 0 := ne_of_gt h3
  have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  rw [← sub_pos]
  have hid : ((1 - ((i:ℝ)+1+3)/(2*P-2)) - 1/2 + 1/(2*P-2)) * (1 - ((i:ℝ)+3)/(P-2))
      - ((1 - ((i:ℝ)+3)/(P-2)) - 1/2 + 1/(P-2)) * (1 - ((i:ℝ)+1+3)/(2*P-2))
      = (P * (i:ℝ) + 4) / (4 * (P-2) * (P-1)) := by
    field_simp
    ring
  rw [hid]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **`v_k/(1-σ_k)` is strictly decreasing in `k`**, stated multiplicatively.

### Summary of Proof
Case on the sign of the index and reduce to the two algebraic identities `ratio_step_pos_aux`
and `ratio_step_neg_aux`, which exhibit the difference of consecutive ratios as a manifestly
positive quotient.

### Lean Notes
Stated multiplicatively — as `v_k(1-σ_{k+1}) > v_{k+1}(1-σ_k)` rather than as a quotient
inequality — to avoid dividing by `1-σ_k`, which would need its positivity threaded through every
step.

Equivalent to `m_k + b_k < 0`, which is the form the source uses.

### References
tex: the inequality `m_k+b_k ≤ 0`, asserted mid-proof in Proposition `\ref{prop:Cscaling}`
(Proposition 17). This is the strict form of the same fact.

### Dependencies
**Depends on:** `ratio_step_neg_aux`, `ratio_step_pos_aux`, `sigma_natCast`, `sigma_neg_eq`,
`vCoeff`, `vCoeff_natCast`, `vCoeff_neg_eq`.
Used by: `mCoeff_add_bCoeff_neg`, `vCoeff_lt_succ`, `vRatio_strictAnti`. -/
theorem vCoeff_ratio_step (k : ℤ) :
    vCoeff (k+1) * (1 - sigma k) < vCoeff k * (1 - sigma (k+1)) := by
  have hpow : ∀ m : ℕ, (8:ℝ) ≤ 2^(m+3) := by
    intro m
    calc (8:ℝ) = 2^(3:ℕ) := by norm_num
      _ ≤ 2^(m+3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdouble : ∀ m : ℕ, (2:ℝ)^(m+1+3) = 2 * 2^(m+3) := by
    intro m; rw [show m+1+3 = (m+3)+1 by omega, pow_succ]; ring
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [show ((n:ℤ)+1) = ((n+1:ℕ):ℤ) by push_cast; ring]
    simp only [sigma_natCast, vCoeff_natCast, hdouble]
    push_cast
    convert ratio_step_pos_aux n ((2:ℝ)^(n+3)) (hpow n) using 1
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, k = -((i:ℤ)+1) := ⟨(-k-1).toNat, by omega⟩
    rw [show -((i:ℤ)+1) + 1 = -((i:ℕ):ℤ) by ring,
      show -((i:ℤ)+1) = -(((i+1:ℕ)):ℤ) by push_cast; ring]
    simp only [sigma_neg_eq, vCoeff_neg_eq, sigma_natCast, vCoeff_natCast, hdouble]
    push_cast
    convert ratio_step_neg_aux i ((2:ℝ)^(i+3)) (hpow i) using 1 <;> ring

/-- **`v_k` is strictly decreasing**: `v_{k+1} < v_k`.

### Summary of Proof
From `vCoeff_ratio_step` — `v_k/(1-σ_k)` decreases — together with `1-σ_k > 1-σ_{k+1} > 0`
(`sigma_lt_succ`, `sigma_lt_one`) and `v_{k+1} ≥ 0`. No case split on the sign of `k` is needed,
since `vCoeff_ratio_step` already covers both branches.

### References
No tex counterpart as a numbered claim — evident from the formula for `v_k`.

### Dependencies
**Depends on:** `sigma_lt_one`, `sigma_lt_succ`, `vCoeff`, `vCoeff_nonneg`,
`vCoeff_ratio_step`.
Used by: `chord_mem_Icc`, `mCoeff_neg`, `vCoeff_strictAnti`. -/
theorem vCoeff_lt_succ (k : ℤ) : vCoeff (k+1) < vCoeff k := by
  have hstep := vCoeff_ratio_step k
  have hσ := sigma_lt_succ k
  have h1 : (0:ℝ) < 1 - sigma k := by linarith [sigma_lt_one k]
  nlinarith [vCoeff_nonneg k]

/-- **The chord slopes are negative**: `m_k < 0`.

### Summary of Proof
Both the numerator `v_k - v_{k+1}` and the denominator's negation follow from monotonicity: `v`
strictly decreases (`vCoeff_lt_succ`) while `σ` strictly increases (`sigma_lt_succ`), so
`m_k = (v_k-v_{k+1})/(σ_k-σ_{k+1})` is a positive over a negative.

### References
No tex counterpart as a numbered claim; the sign is implicit in the source's use of the chords.

### Dependencies
**Depends on:** `mCoeff`, `sigma_lt_succ`, `vCoeff_lt_succ`.
Used by: `bCoeff_pos`, `chordA_antitone`. -/
theorem mCoeff_neg (k : ℤ) : mCoeff k < 0 :=
  div_neg_of_pos_of_neg (by linarith [vCoeff_lt_succ k])
    (by linarith [sigma_lt_succ k])

/-- **`m_k + b_k < 0`** — the constant term of the chord in the arc variable.

### Summary of Proof
Equivalent to `vCoeff_ratio_step`: unfolding `b_k = v_k - m_k σ_k` gives
`m_k + b_k = v_k - m_k(σ_k - 1)`, and substituting `m_k` shows this is negative exactly when
`v_k/(1-σ_k)` exceeds `v_{k+1}/(1-σ_{k+1})`.

### Lean Notes
The strict form of the source's own `m_k+b_k ≤ 0`, which it uses to argue that
`θ_{k,r}-θ_{k+1,r}` decreasing in `r` has the sign it needs.

### References
tex: `m_k+b_k \leq 0`, in the proof of Proposition `\ref{prop:Cscaling}` (Proposition 17).
Verified consistent with `bCoeff_pos` in `Code/verify_bk_sign.py`.

### Dependencies
**Depends on:** `bCoeff`, `mCoeff`, `sigma_lt_succ`, `vCoeff`, `vCoeff_ratio_step`.
Used by: `chordA_star`. -/
theorem mCoeff_add_bCoeff_neg (k : ℤ) : mCoeff k + bCoeff k < 0 := by
  have hlt := sigma_lt_succ k
  have hE : (0:ℝ) < sigma (k+1) - sigma k := by linarith
  have hE' : (sigma (k+1) - sigma k) ≠ 0 := ne_of_gt hE
  have hD' : (sigma k - sigma (k+1)) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
  have hnum : 0 < (vCoeff k - vCoeff (k+1)) * (1 - sigma k)
      + vCoeff k * (sigma k - sigma (k+1)) := by nlinarith [vCoeff_ratio_step k]
  have hm : mCoeff k + bCoeff k = mCoeff k * (1 - sigma k) + vCoeff k := by
    rw [bCoeff]; ring
  have hkey : (vCoeff k - vCoeff (k+1)) / (sigma k - sigma (k+1)) * (1 - sigma k) + vCoeff k
      = -(((vCoeff k - vCoeff (k+1)) * (1 - sigma k)
            + vCoeff k * (sigma k - sigma (k+1))) / (sigma (k+1) - sigma k)) := by
    field_simp
    ring
  rw [hm, mCoeff, hkey]
  exact neg_lt_zero.mpr (div_pos hnum hE)

/-- **`0 < b_k` for every `k`.**

### Summary of Proof
Immediate from `b_k = v_k - m_k σ_k` with `m_k < 0` (`mCoeff_neg`), `σ_k > 0` (`sigma_pos`) and
`v_k ≥ 0` (`vCoeff_nonneg`): the subtracted term is negative, so `b_k ≥ v_k > 0`.

### Lean Notes
This does **not** contradict the source, whose only sign claim about these quantities is
`m_k+b_k ≤ 0` — about the *sum*, and proved here as `mCoeff_add_bCoeff_neg`. The two are
perfectly compatible, since `m_k < 0` with `|m_k| > b_k`; e.g. at `k = 0`, `m_0 = -4/9`,
`b_0 = 7/18`, `m_0+b_0 = -1/18`. Verified at every index from `-6` to `8` in
`Code/verify_bk_sign.py`.

### References
tex: `m_k+b_k \leq 0`, in the proof of Proposition `\ref{prop:Cscaling}` (Proposition 17) — the
related, and correct, claim about the sum.

### Dependencies
**Depends on:** `bCoeff`, `mCoeff_neg`, `sigma_pos`, `vCoeff_nonneg`.
**Used by:** none — kept as the companion sign fact to `mCoeff_add_bCoeff_neg`. -/
theorem bCoeff_pos (k : ℤ) : 0 < bCoeff k := by
  have hm := mCoeff_neg k
  have hσ := sigma_pos k
  have hv := vCoeff_nonneg k
  rw [bCoeff]
  nlinarith

/-- **The chord value lies between its two endpoint values**, `v_{k+1} ≤ m_kσ+b_k ≤ v_k`.

### Summary of Proof
The same convex-combination identity as `chord_vCoeff_nonneg` — the chord equals
`(1-l)v_k + l v_{k+1}` for `l ∈ [0,1]` — now combined with `vCoeff_lt_succ` (which orders the two
endpoints) rather than `vCoeff_nonneg`.

### References
No tex counterpart as a numbered claim.

### Dependencies
**Depends on:** `bCoeff`, `mCoeff`, `sigma_lt_succ`, `vCoeff`, `vCoeff_lt_succ`.
Used by: `chordA_antitone`. -/
theorem chord_mem_Icc {k : ℤ} {σ : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ ≤ sigma (k + 1)) :
    vCoeff (k+1) ≤ mCoeff k * σ + bCoeff k ∧ mCoeff k * σ + bCoeff k ≤ vCoeff k := by
  have hlt := sigma_lt_succ k
  have hd : (0:ℝ) < sigma (k + 1) - sigma k := by linarith
  have hne : sigma k - sigma (k + 1) ≠ 0 := by intro hc; linarith
  set l : ℝ := (σ - sigma k) / (sigma (k + 1) - sigma k) with hl_def
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
  have hl1 : l ≤ 1 := by rw [hl_def, div_le_one hd]; linarith
  have hkey : mCoeff k * σ + bCoeff k = (1 - l) * vCoeff k + l * vCoeff (k + 1) := by
    rw [hl_def]
    simp only [bCoeff, mCoeff]
    field_simp
    ring
  have hv := (vCoeff_lt_succ k).le
  rw [hkey]
  exact ⟨by nlinarith, by nlinarith⟩

/-- **`vCoeff` is strictly antitone** as a function `ℤ → ℝ`.

### Summary of Proof
Upgrades the consecutive-step statement `vCoeff_lt_succ` to full strict antitonicity, by the
standard induction on the gap between the two indices.

### References
No tex counterpart as a numbered claim.

### Dependencies
**Depends on:** `vCoeff`, `vCoeff_lt_succ`.
Used by: `chordA_antitone`. -/
theorem vCoeff_strictAnti : StrictAnti vCoeff := strictAnti_int_of_succ_lt vCoeff_lt_succ

/-- **`chordIdx` is monotone on `(0,1)`**: a larger `σ` sits in a chord of larger index.

### Summary of Proof
If `σ ≤ τ` then every index admissible for `τ` is admissible for `σ`, so the defining set for `σ`
contains that for `τ` and its infimum is no larger.

### References
No tex counterpart.

### Dependencies
**Depends on:** `chordIdx`, `chordIdx_set_bddBelow`, `chordIdx_spec`.
Used by: `chordA_antitone`, `chordA_star`. -/
theorem chordIdx_le_of_le {σ σ' : ℝ} (h0 : 0 < σ) (hle : σ ≤ σ') (h1 : σ' < 1) :
    chordIdx σ ≤ chordIdx σ' := by
  have h0' : 0 < σ' := lt_of_lt_of_le h0 hle
  obtain ⟨-, hs2⟩ := chordIdx_spec h0' h1
  refine csInf_le (chordIdx_set_bddBelow h0) ?_
  change σ < sigma (chordIdx σ' + 1)
  linarith

/-- **The vertex ratio `v_k/(1-σ_k)`.**

### Summary of Proof
A definition. Its monotonicity (`vRatio_strictAnti`) is what expresses the star-shapedness of the
chord function about the point `(1,0)` — see the section header.

### References
No tex counterpart as a named quantity; the source works with the equivalent `m_k+b_k ≤ 0`, in
the proof of Proposition `\ref{prop:Cscaling}` (Proposition 17).

### Dependencies
**Depends on:** `sigma`, `vCoeff`.
Used by: `chordA_star`, `vRatio_strictAnti`. -/
noncomputable def vRatio (k : ℤ) : ℝ := vCoeff k / (1 - sigma k)

/-- **`v_k/(1-σ_k)` is strictly decreasing** — the division form of `vCoeff_ratio_step`.

### Summary of Proof
Divide the multiplicative statement `v_k(1-σ_{k+1}) > v_{k+1}(1-σ_k)` of `vCoeff_ratio_step` by
the positive quantity `(1-σ_k)(1-σ_{k+1})`, positive by `sigma_lt_one`.

### References
tex: `m_k+b_k ≤ 0`, in the proof of Proposition `\ref{prop:Cscaling}` (Proposition 17), of which
this is an equivalent form.

### Dependencies
**Depends on:** `sigma_lt_one`, `vCoeff_ratio_step`, `vRatio`.
Used by: `chordA_star`. -/
theorem vRatio_strictAnti : StrictAnti vRatio := by
  refine strictAnti_int_of_succ_lt fun k => ?_
  rw [vRatio, vRatio, div_lt_div_iff₀ (by linarith [sigma_lt_one (k+1)])
    (by linarith [sigma_lt_one k])]
  exact vCoeff_ratio_step k

/-- **The countable arc decomposition, as an equality**: if each piece integral equals `g j` and
`g` is summable, then `Σ' g = ∫_0^{θ_{K,r}} f`.

### Summary of Proof
The companion of `integral_le_tsum_arc`, with the inequality replaced by an equality throughout.
The partial sums equal `∫_{θ_{K+n,r}}^{θ_{K,r}} f` by `arc_partial_sum`; letting `n → ∞`,
`theta_tendsto_zero` and `continuous_primitive_left` identify the limit with
`∫_0^{θ_{K,r}} f`.

### Lean Notes
Used to identify `c_{1,r}` with `∫_0^{π/2} A(1 - r sin φ)dφ`, which is what makes the closed-form
series and the integral interchangeable downstream.

### References
tex: the regrouping producing the `c_{i,r}` displays after Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `arc_partial_sum`, `continuous_primitive_left`, `theta`,
`theta_tendsto_zero`.
Used by: `c1_eq_integral`. -/
theorem tsum_eq_integral_arc {f : ℝ → ℝ} {g : ℕ → ℝ} {K : ℤ} {r : ℝ} (hr : 0 < r)
    (hint : ∀ u v : ℝ, IntervalIntegrable f MeasureTheory.volume u v)
    (hg : Summable g)
    (heq : ∀ j : ℕ, (∫ φ in (theta (K + j + 1) r)..(theta (K + j) r), f φ) = g j) :
    ∑' j, g j = ∫ φ in (0:ℝ)..(theta K r), f φ := by
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ φ in (theta (K + n) r)..(theta K r), f φ)
      Filter.atTop (nhds (∫ φ in (0:ℝ)..(theta K r), f φ)) := by
    have hc := (continuous_primitive_left hint (theta K r)).continuousAt (x := (0:ℝ))
    exact hc.tendsto.comp (theta_tendsto_zero K hr)
  have hpartial : ∀ n : ℕ, ∑ j ∈ Finset.range n, g j
      = ∫ φ in (theta (K + n) r)..(theta K r), f φ := by
    intro n
    rw [← arc_partial_sum hint n]
    exact Finset.sum_congr rfl (fun j _ => (heq j).symm)
  have h1 := hg.hasSum.tendsto_sum_nat
  simp only [hpartial] at h1
  exact tendsto_nhds_unique h1 hlim

/-! ### Discharging the reflection hypothesis `hz` at the integration sites

`zetalessthanhalf_upper` — and hence `zeta_chord_bound_neg` and `zeta_piecewise_bound` — carries
the hypothesis `ζ(1-σ+it) ≠ 0`.  The tex needs no such hypothesis because it works with the
convention `log|0| = -∞`, under which the reflection identity degenerates harmlessly at a zero;
Lean's total `Real.log` sends `‖0‖` to the *finite* junk value `0` instead, and the statement is
then genuinely false there (it would assert RH on `0 ≤ σ ≤ 1/2`).

Every downstream consumer of these bounds integrates them, so the hypothesis can be discharged
once and for all by an almost-everywhere argument: `ζ` is holomorphic on `ℂ \ {1}` and not
identically zero, so `riemannZetaZeros` is closed and discrete (Mathlib's
`isClosed_riemannZetaZeros`/`isDiscrete_riemannZetaZeros`); pulling that back along a regular
real-analytic curve gives a *codiscrete*, hence conull, set of good parameters.  The three
lemmas below package exactly that, for the two curve shapes the development needs: the vertical
line `t ↦ 1-σ+it` (Littlewood's window integral) and the reflected circle
`φ ↦ b sin φ + i(a + c cos φ)` (the Jensen arc integrals). -/

/-- **`ζ` is non-zero at almost every point of a regular real-analytic curve.**

### Summary of Proof
Mathlib's `isClosed_riemannZetaZeros` and `isDiscrete_riemannZetaZeros` say that the zero set of
`ζ` is closed and discrete in `ℂ`, i.e. its complement lies in the codiscrete filter
(`compl_mem_codiscrete_iff`).  `AnalyticOnNhd.preimage_mem_codiscreteWithin` pulls a codiscrete
set back along an analytic, nowhere locally constant map, so `{x | ζ(γ x) ≠ 0}` is codiscrete in
`ℝ`; and `ae_restrict_le_codiscreteWithin` says a codiscrete subset of `ℝ` is conull.  Nowhere
local constancy comes from the derivative: if `γ` were constant near `x` its derivative there
would be `0`, contradicting `d x ≠ 0`.

### Lean Notes
No tex counterpart: this exists purely to repair Lean's `Real.log 0 = 0` junk value, which the
tex avoids by writing `log|0| = -∞`.  Stated for a curve `γ : ℝ → ℂ` with an explicitly supplied
derivative `d` rather than via `¬EventuallyConst`, because the derivative is what the concrete
instances (a line, a circle) compute most easily.

### References
No tex counterpart.

### Dependencies
**Depends on:** none (Mathlib only).
**Used by:** `ae_zeta_vline_ne_zero`, `ae_zeta_arc_ne_zero`. -/
theorem ae_zeta_curve_ne_zero {γ d : ℝ → ℂ}
    (hγ : ∀ x : ℝ, AnalyticAt ℝ γ x) (hd : ∀ x : ℝ, HasDerivAt γ (d x) x)
    (hd0 : ∀ x : ℝ, d x ≠ 0) :
    ∀ᵐ x : ℝ, riemannZeta (γ x) ≠ 0 := by
  have hZ : riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ :=
    compl_mem_codiscrete_iff.2 ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩
  have hZ' : riemannZetaZerosᶜ ∈ Filter.codiscreteWithin (γ '' Set.univ) :=
    Filter.codiscreteWithin_mono (Set.subset_univ (γ '' Set.univ)) hZ
  have hγU : AnalyticOnNhd ℝ γ Set.univ := fun x _ => hγ x
  have hnc : ∀ x ∈ (Set.univ : Set ℝ), ¬ Filter.EventuallyConst γ (nhds x) := by
    intro x _ hc
    obtain ⟨c, hcc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hc
    have h0 : HasDerivAt γ 0 x := (hasDerivAt_const x c).congr_of_eventuallyEq hcc
    exact hd0 x ((hd x).unique h0)
  have hpre : γ ⁻¹' riemannZetaZerosᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℝ) :=
    hγU.preimage_mem_codiscreteWithin hnc hZ'
  have hle := ae_restrict_le_codiscreteWithin
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (U := (Set.univ : Set ℝ))
    MeasurableSet.univ
  rw [MeasureTheory.Measure.restrict_univ] at hle
  filter_upwards [hle hpre] with x hx
  simpa [riemannZetaZeros] using hx

/-- **`ζ(1-c+iu) ≠ 0` for almost every `u`** — the vertical-line instance of
`ae_zeta_curve_ne_zero`.

### Summary of Proof
The curve `u ↦ 1-c+iu` is affine, hence real-analytic with constant derivative `i ≠ 0`, so
`ae_zeta_curve_ne_zero` applies.

### Lean Notes
The `1 - c` shape (rather than a bare constant) is chosen so that the conclusion matches, term
for term, the hypothesis `hz` of `zeta_piecewise_bound` at abscissa `c`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `ae_zeta_curve_ne_zero`.
**Used by:** `Littlewood.LittlewoodMethod.littlewood_mainterm`,
`Littlewood.LittlewoodMethod.littlewood_mainterm_tight`. -/
theorem ae_zeta_vline_ne_zero (c : ℝ) :
    ∀ᵐ u : ℝ, riemannZeta ((1 : ℂ) - (c : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
  refine ae_zeta_curve_ne_zero (d := fun _ => Complex.I) (fun x => ?_) (fun x => ?_)
    (fun _ => Complex.I_ne_zero)
  · exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt x).mul analyticAt_const)
  · simpa using ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).const_add
      ((1 : ℂ) - (c : ℂ))

/-- **`ζ(b sin φ + i(a + c cos φ)) ≠ 0` for almost every `φ`** — the circle instance of
`ae_zeta_curve_ne_zero`.

### Summary of Proof
The curve is `φ ↦ ia + i·(ε) e^{∓iφ}` up to sign conventions — a circle of radius `|c| = |b|`
about `ia` — which is real-analytic with derivative `b cos φ - i c sin φ`.  That derivative
vanishes only if both `cos φ = 0` and `sin φ = 0` (using `b ≠ 0`, `c ≠ 0`), impossible by
`sin² + cos² = 1`.  So `ae_zeta_curve_ne_zero` applies.

### Lean Notes
`b` and `c` are kept as independent nonzero reals rather than a single radius, because the two
Jensen quarter-arcs need `(b,c) = (r,r)` and `(b,c) = (r,-r)`: the reflected circle
`1 - conj(1+it+re^{iθ})` is traversed in opposite senses on the two halves.  The point
`b sin φ + i(a + c cos φ)` is exactly `1 - σ + i·(ordinate)` for the arc point with abscissa
`σ = 1 - b sin φ` and ordinate `a + c cos φ`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `ae_zeta_curve_ne_zero`.
**Used by:** `Jensen.JensenBounds.arc_piece_bound`, `Jensen.JensenBounds.arc_piece_bound_tight`,
`Jensen.JensenBounds.jensen_easy_lower_quarter`,
`Jensen.JensenBounds.jensen_easy_upper_quarter`,
`Jensen.JensenBounds.jensen_easy_lower_quarter_tight`,
`Jensen.JensenBounds.jensen_easy_upper_quarter_tight`,
`Littlewood.ZetaCircleFcr.FcrZeta_outside_integral`. -/
theorem ae_zeta_arc_ne_zero {b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) (a : ℝ) :
    ∀ᵐ φ : ℝ, riemannZeta (((b * Real.sin φ : ℝ) : ℂ)
        + ((a + c * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  refine ae_zeta_curve_ne_zero
    (d := fun x => ((b * Real.cos x : ℝ) : ℂ) + ((c * -Real.sin x : ℝ) : ℂ) * Complex.I)
    (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · have h1 : AnalyticAt ℝ (fun φ : ℝ => ((b * Real.sin φ : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.analyticAt _).comp (analyticAt_const.mul Real.analyticAt_sin)
    have h2 : AnalyticAt ℝ (fun φ : ℝ => ((a + c * Real.cos φ : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.analyticAt _).comp
        (analyticAt_const.add (analyticAt_const.mul Real.analyticAt_cos))
    exact h1.add (h2.mul analyticAt_const)
  · have h1 : HasDerivAt (fun φ : ℝ => ((b * Real.sin φ : ℝ) : ℂ))
        ((b * Real.cos x : ℝ) : ℂ) x :=
      (HasDerivAt.const_mul b (Real.hasDerivAt_sin x)).ofReal_comp
    have h2 : HasDerivAt (fun φ : ℝ => ((a + c * Real.cos φ : ℝ) : ℂ))
        ((c * -Real.sin x : ℝ) : ℂ) x :=
      ((HasDerivAt.const_mul c (Real.hasDerivAt_cos x)).const_add a).ofReal_comp
    exact h1.add (h2.mul_const Complex.I)
  · intro hx
    have hre : b * Real.cos x = 0 := by
      have h := congrArg Complex.re hx
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.zero_re, mul_zero, zero_mul, add_zero,
        sub_self] at h
      exact h
    have him : c * -Real.sin x = 0 := by
      have h := congrArg Complex.im hx
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, Complex.zero_im, mul_zero, mul_one, add_zero,
        zero_add] at h
      exact h
    have hcos : Real.cos x = 0 := by
      rcases mul_eq_zero.mp hre with h | h
      · exact absurd h hb
      · exact h
    have hsin : Real.sin x = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h hc
      · linarith
    have hpyth := Real.sin_sq_add_cos_sq x
    rw [hcos, hsin] at hpyth
    norm_num at hpyth
