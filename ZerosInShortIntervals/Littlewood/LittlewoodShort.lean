/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Common.RealLogBounds
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.JensenScaleConstants
import ZerosInShortIntervals.Jensen.JensenBounds
import ZerosInShortIntervals.Littlewood.LittlewoodMethod
import ZerosInShortIntervals.Littlewood.LittlewoodIdentity
import ZerosInShortIntervals.Littlewood.ArgIntegrals
import ZerosInShortIntervals.Littlewood.ZetaCircleFcr

/-! # Application to `ζ`: zero density for short intervals (`\S \ref{sec:littlewoodshortapp}`)

This file formalizes `\S`\ `\ref{sec:littlewoodshortapp}` (§3.2) of
`ZerosInShortIntervals.tex`, which specializes the Littlewood machinery of
`ZerosInShortIntervals.Littlewood.LittlewoodMethod` (main-term/outer-log/arg-setup lemmas) together
with the argument-integral bound of `ZerosInShortIntervals.Littlewood.ArgIntegrals` to obtain an
explicit bound on `N(T-h,T+h,α)`, culminating in **Theorem `\ref{thm:littlewoodshort}`
(Theorem 32)**.

Two versions of that theorem are proved here:
* `littlewoodshort` — a milestone with a crude flat error term and an inflated `10^{12} < T-h`
  threshold. Does **not** match the tex's stated error term; kept as a stepping stone.
* `littlewoodshort_tight` — matches Theorem `\ref{thm:littlewoodshort}` (Theorem 32) **exactly**,
  including its hypothesis `t-h>13` and its full un-collapsed `O^*` bracket.
-/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **`A_{1,α,r}` from `Theorem \ref{thm:littlewoodshort}` (Theorem 32)**, for the index `k` with
`σ_k ≤ 1-r < σ_{k+1}`: `(m_k(1-r)+b_k)/(2(r-α))`.

### Summary of Proof
A definition, transcribing the tex's `A_{1,α,r}` display verbatim. It is the `log|t|` coefficient
contributed by the chord majorant at the abscissa `σ = 1-r`.

### Lean Notes
**Chord convention.** `mCoeff`/`bCoeff` use the tex's own convention from Equation
`\ref{eq:mk}` (Equation 5): `m_k = (v_k - v_{k+1})/(σ_k - σ_{k+1})` (note the *negative*
denominator) and `b_k = v_k - m_k σ_k`, so `m_k·σ + b_k` is the chord interpolating
`(σ_k,v_k) → (σ_{k+1},v_{k+1})` **evaluated at `σ` itself**, not at `1-σ`. Here it is evaluated at
`σ = σ_0 = 1-r`, giving the `(1-r)`. This reproduces every row of
Table `\ref{tab:littlewoodshort}` (Table 7) exactly. The equivalent parameterisation by `1-σ`,
with `bCoeff = vCoeff - mCoeff(1-σ_k)`, would make the correct formula *look* wrong; the scripts
in `Code/` use the convention above.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{1,α,r}` display at tex line 1110; chord
convention from Equation `\ref{eq:mk}` (Equation 5). Values in
Table `\ref{tab:littlewoodshort}` (Table 7).

### Dependencies
**Depends on:** `mCoeff`, `bCoeff`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A1 (α r : ℝ) (k : ℤ) : ℝ := (mCoeff k * (1 - r) + bCoeff k) / (2 * (r - α))

/-- **`A_{2,α,r}` from `Theorem \ref{thm:littlewoodshort}` (Theorem 32)**: the `log log|t|`
analogue of `A1`, `(m_k'(1-r)+b_k')/(2π(r-α))`.

### Summary of Proof
A definition, built from the primed chord data of Equation `\ref{eq:mkp}` (Equation 6). Same
chord convention as `A1` — evaluated at `σ = 1-r`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{2,α,r}` display at tex line 1111; chord
data from Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `mCoeffP`, `bCoeffP`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A2 (α r : ℝ) (k : ℤ) : ℝ :=
  (mCoeffP k * (1 - r) + bCoeffP k) / (2 * Real.pi * (r - α))

/-- **`A_{3,α,r}` from `Theorem \ref{thm:littlewoodshort}` (Theorem 32)**: the constant-term
analogue of `A1`, `(m_k''(1-r)+b_k'')/(2π(r-α))`.

### Summary of Proof
A definition, built from the double-primed chord data of Equation `\ref{eq:mkpp}` (Equation 7).
Same chord convention as `A1` — evaluated at `σ = 1-r`.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{3,α,r}` display at tex line 1112; chord
data from Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `mCoeffPP`, `bCoeffPP`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A3 (α r : ℝ) (k : ℤ) : ℝ :=
  (mCoeffPP k * (1 - r) + bCoeffPP k) / (2 * Real.pi * (r - α))

/-- **`A_{4,α,r} = c_{1,r}r/(r-α)` from `Theorem \ref{thm:littlewoodshort}` (Theorem 32).**

### Summary of Proof
A definition. The `c_{1,r}` is `Proposition \ref{prop:jensen-easy}` (Proposition 8)'s `log|t|`
constant; it enters because the two `Δ arg ζ` integrals contribute exactly `r` times the bound of
`Theorem \ref{thm:circularregions1}` (Theorem 16).

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{4,α,r}` display at tex line 1113. `c_{1,r}`
is from `\ref{prop:jensen-easy}` (Proposition 8) via `\ref{thm:circularregions1}` (Theorem 16).

### Dependencies
**Depends on:** `c1`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A4 (α r : ℝ) : ℝ := c1 r * r / (r - α)

/-- **`A_{5,α,r} = (c_{2,r}r + πr)/(π(r-α))` from `Theorem \ref{thm:littlewoodshort}`
(Theorem 32).**

### Summary of Proof
A definition. The bare `πr` summand is the `log log|t|` coefficient `1` coming from Leong's bound
`-log ζ(1+it) < log log|t| + log(29.388)`, scaled by `r`. It is a genuine *main-term*
contribution, not an error term.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{5,α,r}` display at tex line 1114.
External: Leong, arXiv:2405.04869, via `ExternalFacts.leong_log_zeta_one_bound`.

### Dependencies
**Depends on:** `c2`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A5 (α r : ℝ) : ℝ := (c2 r * r + Real.pi * r) / (Real.pi * (r - α))

/-- **`A_{6,α,r}` from `Theorem \ref{thm:littlewoodshort}` (Theorem 32)**: the additive constant.

### Summary of Proof
A definition, collecting four contributions over `π(r-α)`:
* `c_{3,r}r + c_{4,r}πr` — the `Δ arg ζ` circle bound;
* `π log(29.388) r` — Leong's additive constant;
* `Φ(1+ηr)` — from `Lemma \ref{lemma:littlewood-outerlog}` (Lemma 26), bounding the integral
  outside the critical strip;
* `(1+η)r log ζ(1+ηr)` — from the displayed `arg ζ ≤ |log ζ| < log ζ(1+ηr)` step in Theorem 32's
  proof.

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), the `A_{6,α,r}` display at tex line 1115.
Contributions from `\ref{lemma:littlewood-outerlog}` (Lemma 26) and Equation `\ref{eq:eta}`
(Equation 15). External: Leong, arXiv:2405.04869.

**Independent numeric check.**
`Code/indep_mpmath_tables_spotcheck.py` recomputes `A1`–`A6` from these definitions with
plain mpmath quadrature (`c4`, `c5`, `Φ` by `quad`, `η` by `findroot`) at `α = 1/8`, `r = 1/2`,
`k = 0`, in the table's alternate chord triple, and reproduces the
Table `\ref{tab:littlewoodshort}` (Table 7) row
`0.2195122, 0, 1.782623, 0.1957157, 1.732003, 9.128594` to all 7 digits. (With Lean's main-text
triple the same point gives `A1 = 2/9`.)

### Dependencies
**Depends on:** `c3`, `c4`, `Phi`, `eta`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `MainTheorem.ULittlewood`,
`MainCorollary.C2Littlewood`. -/
noncomputable def A6 (α r : ℝ) : ℝ :=
  (c3 r * r + c4 r * Real.pi * r + Real.pi * Real.log 29.388 * r + (Phi (1 + eta * r : ℂ)).re
      + (1 + eta) * r * Real.log ‖riemannZeta (1 + eta * r : ℂ)‖)
    / (Real.pi * (r - α))

/-- **A crude bound `arcErr_tight r t < 3`**, valid once `t > 20`.

### Summary of Proof
Pure proof-engineering. Every piece of `arcErr_tight` is genuinely `O(1/t)`
or smaller, so bounding the sum by the flat constant `3` is comfortable once `t` is past a small
threshold. The proof bounds each of the four pieces separately: `r/(t-r) ≤ 1`, the ratio
`r/(t-r)/(log t - r/(t-r)) ≤ 1` using `log t > 2`, positivity of the two squared-denominator
terms, and finally the binding piece via `nlinarith`.

### Lean Notes
The binding piece numerically needs only `t - r > 9`-ish
(`2/(t-r)^2 + 1158/(8(t-r)^2 log(t-r)) < 1` fails at `t-r=8`, holds comfortably by `t-r=19`), so
`t > 20` is a generous-but-not-wasteful margin (`r<1` gives `t-r>19`).

Split out as its own lemma rather than a `have` inside the caller purely so its `nlinarith` calls
run in a small context — nested inside a large proof they time out, since `linarith`/`nlinarith`
scan the *entire* local context, not just the hints passed to them.

The tex never crudely bounds the arc-integral remainder; it carries `E(r,·)` exactly, as
`littlewoodshort_tight` does. This lemma exists only to support the cruder milestone.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcErr_tight`, `Common.RealLogBounds.two_lt_log_of_gt_eight`.
**Used by:** `littlewoodshort` only; `littlewoodshort_tight` does not use it. -/
theorem arcErr_tight_crude_lt_three {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ht20 : (20:ℝ) < t) : arcErr_tight r t < 3 := by
  unfold arcErr_tight
  have htr : (0:ℝ) < t - r := by linarith
  have h1 : r / (t - r) ≤ 1 := by rw [div_le_one htr]; linarith
  have hlt2 : (2:ℝ) < Real.log t := two_lt_log_of_gt_eight (by linarith)
  have hden_pos : (0:ℝ) < Real.log t - r / (t - r) := by linarith
  have h2 : r / (t - r) / (Real.log t - r / (t - r)) ≤ 1 := by
    rw [div_le_one hden_pos]; linarith
  have htr1 : (1:ℝ) < t - r := by linarith
  have hlogtr_pos : (0:ℝ) < Real.log (t - r) := Real.log_pos htr1
  have h3 : (0:ℝ) ≤ 2 / (t - r) ^ 2 + 1158 / (8 * (t - r) ^ 2 * Real.log (t - r)) := by
    positivity
  have h4 : 2 / (t - r) ^ 2 + 1158 / (8 * (t - r) ^ 2 * Real.log (t - r)) < 1 := by
    have htrbig : (19:ℝ) < t - r := by nlinarith [ht20]
    have hlog_th : (2:ℝ) < Real.log (t - r) := two_lt_log_of_gt_eight (by linarith)
    have h5 : (2:ℝ) / (t - r) ^ 2 < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [htrbig]
    have h6 : (1158:ℝ) / (8 * (t - r) ^ 2 * Real.log (t - r)) < 3 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have hsq : (19:ℝ) * 19 < (t - r) * (t - r) := by nlinarith [htrbig]
      nlinarith [hsq, hlog_th,
        mul_lt_mul_of_pos_left hlog_th (by nlinarith [hsq] : (0:ℝ) < (t - r) * (t - r))]
    linarith
  nlinarith [h1, h2, h3, h4]

/-- **Pure real-number core of the `Δ arg` contribution bound.** Combines the two one-sided
`arg_integrals` bounds at `T+h` and `T-h` into a single closed-form estimate, entirely as an
inequality between real numbers with every integral/norm/`arg` quantity abstracted to a free
variable.

### Summary of Proof
No tex counterpart as a statement — this is the bookkeeping the tex compresses into the single
sentence "the combined contribution from these two integrals is then precisely `1-σ_0=r` times
the bound obtained in Theorem `\ref{thm:circularregions1}`" in Theorem 32's proof.

The argument: scale each one-sided bound by `1/π`; add the two Leong bounds
`-L ≤ loglog + log29`; combine the `log`/`log log` window sums via `hlogsum`/`hloglogsum`; then
crudely round the two arc terms using `arcp, arcm < 3`, giving the flat `2*r`. The final step is
`ring_nf` across all hypotheses and the goal simultaneously, then `linarith` — normalising
everything to one canonical form is what makes the match succeed.

### Lean Notes
Stated over free real variables so it is independent of what the integrals actually are, and kept
as its own lemma purely so its `nlinarith`/`linarith` calls run in a small, clean context. Nested
inside `littlewoodshort`'s proof, with dozens of large integral hypotheses already in scope, the
single combined step it performs does not converge; isolated here, it does.

### References
No tex counterpart. Corresponds to a compression step in `\ref{thm:littlewoodshort}` (Theorem 32)'s
proof, invoking `\ref{thm:circularregions1}` (Theorem 16).

### Dependencies
**Depends on:** none — pure real arithmetic.
**Used by:** `littlewoodshort`. See `Dcombo_bound_exact` for the variant that keeps the arc terms
symbolic, used by `littlewoodshort_tight`. -/
theorem Dcombo_bound {c1' c2' c3' c4' logTp logTm loglogTp loglogTm Lp Lm Fp Fm arcp arcm
    logT loglogT log29 r : ℝ}
    (hr0 : 0 < r) (hc1nn : 0 ≤ c1') (hc2nn : 0 ≤ c2')
    (hFp : Fp ≤ Real.pi * c4' + c1' * logTp + c2' * loglogTp + c3' + Real.pi / 2 * arcp)
    (hFm : Fm ≤ Real.pi * c4' + c1' * logTm + c2' * loglogTm + c3' + Real.pi / 2 * arcm)
    (hLp : -Lp ≤ loglogTp + log29) (hLm : -Lm ≤ loglogTm + log29)
    (hlogsum : logTp + logTm ≤ 2 * logT) (hloglogsum : loglogTp + loglogTm ≤ 2 * loglogT)
    (harcp : arcp < 3) (harcm : arcm < 3) :
    r / 2 * (-Lp + 1 / Real.pi * Fp) + r / 2 * (-Lm + 1 / Real.pi * Fm)
      ≤ c1' * r / Real.pi * logT + (r + c2' * r / Real.pi) * loglogT
        + c4' * r + c3' * r / Real.pi + r * log29 + 2 * r := by
  have hpi := Real.pi_pos
  have hFp' : 1 / Real.pi * Fp
      ≤ c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hFp (show (0:ℝ) ≤ 1 / Real.pi by positivity)
    calc 1 / Real.pi * Fp
        ≤ 1 / Real.pi * (Real.pi * c4' + c1' * logTp + c2' * loglogTp + c3' + Real.pi / 2 * arcp) :=
          hmul
      _ = c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2 := by
          field_simp
  have hFm' : 1 / Real.pi * Fm
      ≤ c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hFm (show (0:ℝ) ≤ 1 / Real.pi by positivity)
    calc 1 / Real.pi * Fm
        ≤ 1 / Real.pi * (Real.pi * c4' + c1' * logTm + c2' * loglogTm + c3' + Real.pi / 2 * arcm) :=
          hmul
      _ = c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2 := by
          field_simp
  have hc1div : (0:ℝ) ≤ c1' / Real.pi := div_nonneg hc1nn hpi.le
  have hc2div : (0:ℝ) ≤ c2' / Real.pi := div_nonneg hc2nn hpi.le
  have hlog1 : c1' / Real.pi * logTp + c1' / Real.pi * logTm ≤ c1' / Real.pi * (2 * logT) := by
    have h := mul_le_mul_of_nonneg_left hlogsum hc1div
    nlinarith [h]
  have hlog2 : c2' / Real.pi * loglogTp + c2' / Real.pi * loglogTm
      ≤ c2' / Real.pi * (2 * loglogT) := by
    have h := mul_le_mul_of_nonneg_left hloglogsum hc2div
    nlinarith [h]
  have hrhalf : (0:ℝ) ≤ r / 2 := by linarith
  have e1 : -Lp + 1 / Real.pi * Fp
      ≤ (loglogTp + log29)
        + (c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2) := by
    linarith [hLp, hFp']
  have e2 : -Lm + 1 / Real.pi * Fm
      ≤ (loglogTm + log29)
        + (c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2) := by
    linarith [hLm, hFm']
  have h1 := mul_le_mul_of_nonneg_left e1 hrhalf
  have h2 := mul_le_mul_of_nonneg_left e2 hrhalf
  have hl1 := mul_le_mul_of_nonneg_left hlog1 hrhalf
  have hl2 := mul_le_mul_of_nonneg_left hlog2 hrhalf
  have hl3 := mul_le_mul_of_nonneg_left hloglogsum hrhalf
  have hl4 := mul_le_mul_of_nonneg_left (show arcp + arcm ≤ 6 by linarith [harcp, harcm]) hr0.le
  ring_nf at h1 h2 hl1 hl2 hl3 hl4 ⊢
  linarith [h1, h2, hl1, hl2, hl3, hl4, harcp, harcm, hr0]

/-- **Exact variant of `Dcombo_bound`**: keeps the arc contribution as the genuine
`r/4*(arcp+arcm)` term the proof actually produces, instead of rounding it up to `2*r`.

### Summary of Proof
Identical to `Dcombo_bound`'s — scale by `1/π`, add the Leong bounds, combine the window sums,
`ring_nf` then `linarith` — minus the final crude rounding step, dropping the `harcp`/`harcm`
hypotheses and leaving `r/4*(arcp+arcm)` in place.

### Lean Notes
No tex counterpart as a standalone statement, but it is what makes the Lean error term match
`Theorem \ref{thm:littlewoodshort}` (Theorem 32)'s printed `O^*` bracket *exactly*, since the tex
also carries the arc remainder `E(r,t±h)` symbolically rather than rounding it. Using this in
place of `Dcombo_bound` removes the need for `arcErr_tight_crude_lt_three`, and its threshold,
entirely from `littlewoodshort_tight`.

### References
No tex counterpart as a statement. Supports `\ref{thm:littlewoodshort}` (Theorem 32)'s exact
`O^*` bracket.

### Dependencies
**Depends on:** none — pure real arithmetic.
**Used by:** `littlewoodshort_tight`. -/
theorem Dcombo_bound_exact {c1' c2' c3' c4' logTp logTm loglogTp loglogTm Lp Lm Fp Fm arcp arcm
    logT loglogT log29 r : ℝ}
    (hr0 : 0 < r) (hc1nn : 0 ≤ c1') (hc2nn : 0 ≤ c2')
    (hFp : Fp ≤ Real.pi * c4' + c1' * logTp + c2' * loglogTp + c3' + Real.pi / 2 * arcp)
    (hFm : Fm ≤ Real.pi * c4' + c1' * logTm + c2' * loglogTm + c3' + Real.pi / 2 * arcm)
    (hLp : -Lp ≤ loglogTp + log29) (hLm : -Lm ≤ loglogTm + log29)
    (hlogsum : logTp + logTm ≤ 2 * logT) (hloglogsum : loglogTp + loglogTm ≤ 2 * loglogT) :
    r / 2 * (-Lp + 1 / Real.pi * Fp) + r / 2 * (-Lm + 1 / Real.pi * Fm)
      ≤ c1' * r / Real.pi * logT + (r + c2' * r / Real.pi) * loglogT
        + c4' * r + c3' * r / Real.pi + r * log29 + r / 4 * (arcp + arcm) := by
  have hpi := Real.pi_pos
  have hFp' : 1 / Real.pi * Fp
      ≤ c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hFp (show (0:ℝ) ≤ 1 / Real.pi by positivity)
    calc 1 / Real.pi * Fp
        ≤ 1 / Real.pi * (Real.pi * c4' + c1' * logTp + c2' * loglogTp + c3' + Real.pi / 2 * arcp) :=
          hmul
      _ = c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2 := by
          field_simp
  have hFm' : 1 / Real.pi * Fm
      ≤ c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hFm (show (0:ℝ) ≤ 1 / Real.pi by positivity)
    calc 1 / Real.pi * Fm
        ≤ 1 / Real.pi * (Real.pi * c4' + c1' * logTm + c2' * loglogTm + c3' + Real.pi / 2 * arcm) :=
          hmul
      _ = c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2 := by
          field_simp
  have hc1div : (0:ℝ) ≤ c1' / Real.pi := div_nonneg hc1nn hpi.le
  have hc2div : (0:ℝ) ≤ c2' / Real.pi := div_nonneg hc2nn hpi.le
  have hlog1 : c1' / Real.pi * logTp + c1' / Real.pi * logTm ≤ c1' / Real.pi * (2 * logT) := by
    have h := mul_le_mul_of_nonneg_left hlogsum hc1div
    nlinarith [h]
  have hlog2 : c2' / Real.pi * loglogTp + c2' / Real.pi * loglogTm
      ≤ c2' / Real.pi * (2 * loglogT) := by
    have h := mul_le_mul_of_nonneg_left hloglogsum hc2div
    nlinarith [h]
  have hrhalf : (0:ℝ) ≤ r / 2 := by linarith
  have e1 : -Lp + 1 / Real.pi * Fp
      ≤ (loglogTp + log29)
        + (c4' + c1' / Real.pi * logTp + c2' / Real.pi * loglogTp + c3' / Real.pi + arcp / 2) := by
    linarith [hLp, hFp']
  have e2 : -Lm + 1 / Real.pi * Fm
      ≤ (loglogTm + log29)
        + (c4' + c1' / Real.pi * logTm + c2' / Real.pi * loglogTm + c3' / Real.pi + arcm / 2) := by
    linarith [hLm, hFm']
  have h1 := mul_le_mul_of_nonneg_left e1 hrhalf
  have h2 := mul_le_mul_of_nonneg_left e2 hrhalf
  have hl1 := mul_le_mul_of_nonneg_left hlog1 hrhalf
  have hl2 := mul_le_mul_of_nonneg_left hlog2 hrhalf
  have hl3 := mul_le_mul_of_nonneg_left hloglogsum hrhalf
  ring_nf at h1 h2 hl1 hl2 hl3 ⊢
  linarith [h1, h2, hl1, hl2, hl3]

set_option maxHeartbeats 400000 in
-- what remains over the default budget is elaborating the STATEMENT (`whnf`), not the tactics.
-- This was 4000000 while three arithmetic steps ran `nlinarith` against the whole accumulated
-- hypothesis context; giving each the facts it actually needs (`linarith only [...]`, and an
-- explicit `mul_le_mul_of_nonneg_right` for the cross-multiplications) removed that cost
-- entirely.  What is left is `whnf` on the two statements, which no hint can reach.
-- Measured: fails at 300000, passes at 400000.
/-- **A "simple" milestone toward Theorem `\ref{thm:littlewoodshort}` (Theorem 32)**, with a cruder
error term and threshold than the source: for `10^{12} < T-h`, `h < T`, `r > α`, and `k` with
`σ_k ≤ 1-r < σ_{k+1}`,
`N(T-h,T+h,α) < (2A₁h+2A₄)/π log|T| + (2A₂h+2A₅) log log|T| + 2A₃h + A₆ + O^*(4h/(π(T-h)(r-α)) +
2/(r-α))`.

### Summary of Proof
Following the tex's proof of Theorem 32: apply
`LittlewoodIdentity.simplelittlewoodzerodensity` with `σ0 = 1-r`, `σ1 = 1+ηr`. Bound the first
pair of integrals via `littlewood_mainterm` (giving `A1,A2,A3`) and `littlewood_outerlog`
(contributing `Φ(1+ηr)/π` to `A6`). Convert the `arg ζ` integrals via `littlewood_argsetup`,
bounding `arg ζ(1+ηr+i(T±h)) ≤ |log ζ(1+ηr+i(T±h))| < log ζ(1+ηr)` (contributing
`(1+η)r log ζ(1+ηr)/π` to `A6`). For the two `Δ arg ζ` integrals, apply
`ArgIntegrals.arg_integrals` with `c=1` and `Fcr := ZetaCircleFcr.FcrZeta r (T±h)`, the tex's
`F_{c,r}` for `ζ` built as in the proof of `\ref{prop:jensen-easy}` (Proposition 8); by
`FcrZeta_integral_le` their combined contribution is exactly `r` times the bound of
`\ref{thm:circularregions1}` (Theorem 16), which is where `A4,A5,A6` and their `c1,c2,c3,c4` come
from. Finally track the accumulated `O^*` errors.

### Lean Notes
**This does NOT match Theorem 32's stated error term**, which is the exact, un-collapsed
`(1/(r-α))(h/(π(t-h)²)(2+1158/(8log(t-h))) + (r/4)(E(r,t+h)+E(r,t-h)))`. See
`littlewoodshort_tight`, which matches it verbatim, hypothesis `t-h>13` included. This milestone
is retained because it is a strictly simpler assembly — a flat constant in place of the arc
remainder. It is sound but weaker on both the threshold and the error.

**Why the error term carries a `1/(r-α)` factor.** Every piece `simplelittlewoodzerodensity`
bounds `Nrect` by sits inside a bracket divided by `r-α` as a *whole*, main and error terms alike,
and `r-α` has no lower bound in the hypotheses; an error term without the factor cannot absorb an
error piece that itself scales like `1/(r-α)`. The tex's Theorem 32 carries `1/(r-α)` explicitly.

**Three hypotheses worth naming**, none new relative to the source:
(i) `0 < α` — needed for `simplelittlewoodzerodensity`'s `1 - α ≤ σ1` (`σ1 = 1+ηr > 1 > 1-α`
needs `α > 0`); without it `1-α ≥ 1` and `Nrect = 0` trivially, a degenerate case not handled
here. (ii) `0 < h`, present in the tex's own statement — needed by `littlewood_mainterm`'s strict
`<`. (iii) `10^{12} < T - h`, not merely `10^{12} < T`, since `littlewood_mainterm` needs it
across the whole window and `h < T` puts no lower bound on `T-h`.

**Beyond the tex.** The tex compresses the assembly into half a page; the Lean proof is ~350 lines
and makes explicit the `1/(r-α)` scaling, the two-sided window bookkeeping
`log(T+h)+log(T-h) ≤ 2log|T|` (an AM–GM step the tex does not state) and its `log log` analogue,
the crude rounding via `arcErr_tight_crude_lt_three`, and `Dcombo_bound`. That assembly, not any
single input, is the substance.

**On `arg ζ`.** `argZeta` is the tex's constructed branch (`LittlewoodMethod.argZetaDef`), so the
two properties `ArgIntegrals.arg_integrals` needs of it — the polar form
`ζ = ‖ζ‖ e^{i·argZeta}` along the segments `[1-r, 1+ηr] + i(T±h)`
(`LittlewoodIdentity.zeta_eq_norm_mul_exp_argZetaDef'`) and continuity along them
(`argZetaDef_continuousOn_line'`) — are theorems here, both proved from `hzf_p`/`hzf_m`, rather
than hypotheses. The tex handles `arg ζ` in two cases, fixed after Equation
`\ref{eq:zerodensityintegral}` (Equation 13). (1) A horizontal line with no zero of `ζ`: there
`arg ζ` is *defined* by continuous variation to the right of `1` and then along the line — this is
`argZetaDef`. (2) A line through a zero: the tex uses instead the convention
`lim_{ε→0} ½(arg ζ(·+i(T+ε)) + arg ζ(·+i(T-ε)))` together with the matching convention for `N`,
remarked on in the proofs where needed. This theorem is case (1) for both lines `T±h`, which is
what the tex's Theorem 32 proves before invoking the convention; case (2) is not formalized.

**`hzf_p`/`hzf_m`** (no zero of `ζ` on the two horizontal edges) are inherited from
`LittlewoodIdentity.littlewood_zero_density_integral` (Equation 13) and are the tex's first case,
in which the tex's `arg ζ` is a continuous argument along the edge; the tex's second case (a zero
on an edge) is its halving convention, not formalized. No hypothesis on the left edge
`Re s = 1-r` is needed: the tex's improper `∫ log|ζ(1-r+it)| dt` is the Lebesgue integral of an
integrable function (`LittlewoodIdentity.intervalIntegrable_log_norm_zeta_vertical`).

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), tex lines 1093–1117, and
§`\ref{sec:littlewoodshortapp}` (§3.2). Consumes `\ref{lemma:littlewood-mainterm}` (Lemma 25),
`\ref{lemma:littlewood-outerlog}` (Lemma 26), `\ref{lem:littlewood-argsetup}` (Lemma 27),
`\ref{thm:arg-integrals}` (Theorem 31), `\ref{thm:circularregions1}` (Theorem 16).

### Dependencies
**Depends on:** `simplelittlewoodzerodensity`, `littlewood_mainterm`, `littlewood_outerlog`,
`littlewood_argsetup`, `arg_integrals`, `FcrZeta_integral_le`, `FcrZeta_even`,
`FcrZeta_intervalIntegrable`, `zeta_eq_norm_mul_exp_argZetaDef'`, `argZetaDef_continuousOn_line'`,
`zeta_ne_zero_line_of_Icc`, `c1_nonneg`, `c2_nonneg`,
`ExternalFacts.leong_log_zeta_one_bound`, `Dcombo_bound`, `arcErr_tight_crude_lt_three`,
`A1`–`A6`, `Common.RealLogBounds.two_lt_log_of_gt_eight`/`one_lt_log_of_ge_three`.
**Used by:** `HalvingConvention.littlewoodshortHalf`.  Downstream of that it is superseded by
`littlewoodshort_tight`, which is what `MainTheorem.ULittlewood`/`ELittlewood` are built to
match. -/
theorem littlewoodshort {T h r α : ℝ} {k : ℤ} (hT : (10 : ℝ) ^ (12 : ℕ) < T - h) (hh0 : 0 < h)
    (hh : h < T) (hα : 0 < α) (hrα : α < r) (hk : sigma k ≤ 1 - r)
    (hk' : 1 - r < sigma (k + 1))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (T + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (T - h) * Complex.I) ≠ 0) :
    (Nrect (T - h) (T + h) α : ℝ)
      < (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
        + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
        + 2 * A3 α r k * h + A6 α r
        + (4 * h / (Real.pi * (T - h)) + 2) / (r - α) := by
  have hpi := Real.pi_pos
  have h1e12 : (0:ℝ) < (10:ℝ) ^ (12:ℕ) := by norm_num
  have hTh0 : (0:ℝ) < T - h := by linarith
  have hTp0 : (0:ℝ) < T + h := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have habsT : |T| = T := abs_of_pos hT0
  have hr0 : (0:ℝ) < r := by linarith [sigma_lt_one (k + 1), hk']
  have hr1 : r < 1 := by linarith [sigma_pos k, hk]
  have heta := eta_mem_Ioo
  have hrα' : (0:ℝ) < r - α := by linarith
  have hσ1gt1 : (1:ℝ) < 1 + eta * r := by nlinarith [heta.1]
  have hσ0leσ1 : (1 - r : ℝ) ≤ 1 + eta * r := by nlinarith [heta.1.le]
  -- Step 1: `simplelittlewoodzerodensity`
  have hden : (0:ℝ) < 1 - (1 - r) - α := by linarith
  have hσ1ge : (1:ℝ) - α ≤ 1 + eta * r := by nlinarith [heta.1, hr0]
  have hmain := simplelittlewoodzerodensity (T := T) (h := h) (α := α) (σ0 := 1 - r)
    (σ1 := 1 + eta * r) hden hh0 hTh0 hσ1ge hσ1gt1 hzf_p hzf_m
  -- Step 2: `littlewood_mainterm` at `σ0 = 1-r`
  have hmt := littlewood_mainterm (k := k) (σ := 1 - r) (T := T) (h := h) hk hk' hh0 hT
  -- Step 3: `littlewood_outerlog` at `σ1 = 1+ηr`
  have hol := littlewood_outerlog (σ := 1 + eta * r) (T := T) (h := h) hh0.le hh hσ1gt1.le
  -- `argZeta = argZetaDef` is a continuous argument of `ζ` on the two zero-free edges
  have hzf_p' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hzf_p x hx
  have hzf_m' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hzf_m x hx
  have hline_p : ∀ x, 1 - r ≤ x → riemannZeta ((x : ℂ) + ((T + h : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    zeta_ne_zero_line_of_Icc hσ1gt1 hzf_p' le_rfl
  have hline_m : ∀ x, 1 - r ≤ x → riemannZeta ((x : ℂ) + ((T - h : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    zeta_ne_zero_line_of_Icc hσ1gt1 hzf_m' le_rfl
  have hpol_p' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I)
        = ‖riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I)‖
          * Complex.exp (argZeta (x + ((T + h : ℝ) : ℂ) * Complex.I) * Complex.I) :=
    fun x hx => zeta_eq_norm_mul_exp_argZetaDef' hTp0.ne' hline_p hx.1
  have hpol_m' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I)
        = ‖riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I)‖
          * Complex.exp (argZeta (x + ((T - h : ℝ) : ℂ) * Complex.I) * Complex.I) :=
    fun x hx => zeta_eq_norm_mul_exp_argZetaDef' hTh0.ne' hline_m hx.1
  have hcont_p : ContinuousOn (fun x : ℝ => argZeta (x + ((T + h : ℝ) : ℂ) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := argZetaDef_continuousOn_line' hTp0.ne' hline_p
  have hcont_m : ContinuousOn (fun x : ℝ => argZeta (x + ((T - h : ℝ) : ℂ) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := argZetaDef_continuousOn_line' hTh0.ne' hline_m
  have hcont_p2 : ContinuousOn (fun u : ℝ => argZeta (u + (T + h) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := by
    have := hcont_p
    push_cast at this
    exact this
  have hcont_m2 : ContinuousOn (fun u : ℝ => argZeta (u + (T - h) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := by
    have := hcont_m
    push_cast at this
    exact this
  have hint_p : IntervalIntegrable (fun u : ℝ => argZeta (u + ((T + h : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (1 - r) (1 + eta * r) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0leσ1]
    exact hcont_p
  have hint_m : IntervalIntegrable (fun u : ℝ => argZeta (u + ((T - h : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (1 - r) (1 + eta * r) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0leσ1]
    exact hcont_m
  -- Step 4: `littlewood_argsetup`
  obtain ⟨hclaim1, hclaim2⟩ :=
    littlewood_argsetup (σ0 := 1 - r) (σ1 := 1 + eta * r) (T := T) (h := h) hσ1gt1 hσ0leσ1
      hcont_p2 hcont_m2
  -- Step 5: `arg_integrals`, at `T+h` and `T-h`, with `c := 1`, radius `r`, `Fcr := FcrZeta r ·`.
  have hf : ∀ s : ℂ, (starRingEnd ℂ) (riemannZeta s) = riemannZeta ((starRingEnd ℂ) s) :=
    fun s => (riemannZeta_conj s).symm
  have hc_ineq : (1 + eta * r : ℝ) - 1 ≤ eta * (1 - (1 - r)) := le_of_eq (by ring)
  -- the hypotheses `arg_integrals` needs about `ζ` and `argZeta` on the two segments
  have hr1' : r < 1 := by linarith [sigma_pos k, hk]
  have hTr_p : r < T + h := by linarith [hT, hr1', hh0]
  have hTr_m : r < T - h := by linarith [hT, hr1']
  have hfan_gen : ∀ T' : ℝ, r < T' →
      AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall (((1 : ℝ) : ℂ) + ((T' : ℝ) : ℂ) * Complex.I) ((1 : ℝ) - (1 - r))) := by
    intro T' hT'
    apply analyticOn_riemannZeta.mono
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    subst h1
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have e : (1 : ℂ) - (((1 : ℝ) : ℂ) + ((T' : ℝ) : ℂ) * Complex.I)
        = -(((T' : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [e, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)] at hz
    linarith
  have hai_p := arg_integrals riemannZeta argZeta hf (σ0 := 1 - r) (σ1 := 1 + eta * r) (c := 1)
    (T := T + h) (Fcr := FcrZeta r (T + h))
    (by apply riemannZeta_ne_zero_of_one_le_re; simp)
    (by linarith) hσ1gt1.le hc_ineq (hfan_gen (T + h) hTr_p) hpol_p' hcont_p
    (FcrZeta_even r (T + h))
    (by
      intro θ
      have heq : (((1 : ℝ) : ℂ) - ((1 - r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := by push_cast; ring
      rw [heq]; unfold FcrZeta; norm_num)
    (FcrZeta_intervalIntegrable r (T + h) 0 Real.pi)
  have hai_m := arg_integrals riemannZeta argZeta hf (σ0 := 1 - r) (σ1 := 1 + eta * r) (c := 1)
    (T := T - h) (Fcr := FcrZeta r (T - h))
    (by apply riemannZeta_ne_zero_of_one_le_re; simp)
    (by linarith) hσ1gt1.le hc_ineq (hfan_gen (T - h) hTr_m) hpol_m' hcont_m
    (FcrZeta_even r (T - h))
    (by
      intro θ
      have heq : (((1 : ℝ) : ℂ) - ((1 - r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := by push_cast; ring
      rw [heq]; unfold FcrZeta; norm_num)
    (FcrZeta_intervalIntegrable r (T - h) 0 Real.pi)
  simp only [show (1:ℝ) - (1 - r) = r from by ring] at hai_p hai_m
  -- Rewrite each `arg_integrals` bound's inner quantity to `∫ deltaArgZeta T' σ1 u`, matching
  -- `hclaim2`'s own convention, via the same base-point decomposition `littlewood_argsetup` uses.
  have hexpand : ∀ T' : ℝ, IntervalIntegrable (fun u : ℝ => argZeta (u + T' * Complex.I))
        MeasureTheory.volume (1 - r) (1 + eta * r) →
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u)
      = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
        - ((1 + eta * r) - (1 - r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
    intro T' hint
    have hpt : ∀ u : ℝ, deltaArgZeta T' (1 + eta * r) u
        = argZeta (u + T' * Complex.I) - argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
      intro u; unfold deltaArgZeta; push_cast; ring
    calc (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u)
        = ∫ u in (1 - r)..(1 + eta * r),
            (argZeta (u + T' * Complex.I) - argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I)) :=
          intervalIntegral.integral_congr (fun u _ => hpt u)
      _ = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
          - ∫ _u in (1 - r)..(1 + eta * r), argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) :=
          intervalIntegral.integral_sub hint intervalIntegrable_const
      _ = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
          - ((1 + eta * r) - (1 - r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hinner_eq : ∀ T' : ℝ, IntervalIntegrable (fun u : ℝ => argZeta (u + T' * Complex.I))
        MeasureTheory.volume (1 - r) (1 + eta * r) →
      (∫ σ in (1 + eta * r)..(1 - r), argZeta (σ + T' * Complex.I))
        - ((1 - r) - (1 + eta * r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I)
      = -(∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u) := by
    intro T' hint
    rw [hexpand T' hint, intervalIntegral.integral_symm (1 - r) (1 + eta * r)]
    ring
  rw [hinner_eq (T + h) hint_p] at hai_p
  rw [hinner_eq (T - h) hint_m] at hai_m
  rw [abs_neg] at hai_p hai_m
  -- Step 6: `FcrZeta_integral_le` and `leong_log_zeta_one_bound`, at `T+h` and `T-h`.
  have hT13p : (13:ℝ) < T + h := by linarith
  have hT13m : (13:ℝ) < T - h := by linarith
  have hlog_of : ∀ t : ℝ, (13:ℝ) < t → r / (t - r) < Real.log t := by
    intro t ht13
    have htr : (0:ℝ) < t - r := by linarith
    have hlt2 : (2:ℝ) < Real.log t := two_lt_log_of_gt_eight (by linarith)
    have h1 : r / (t - r) ≤ 1 := by rw [div_le_one htr]; linarith
    linarith
  have hFI_p := FcrZeta_integral_le (r := r) (T := T + h) hr0 hr1 hT13p (hlog_of _ hT13p)
  have hFI_m := FcrZeta_integral_le (r := r) (T := T - h) hr0 hr1 hT13m (hlog_of _ hT13m)
  have hleong_p := leong_log_zeta_one_bound (t := T + h) (by rw [abs_of_pos hTp0]; linarith)
  have hleong_m := leong_log_zeta_one_bound (t := T - h) (by rw [abs_of_pos hTh0]; linarith)
  -- Step 7: `log(T+h)+log(T-h) ≤ 2 log|T|`, and the analogous `log log` bound.
  have hlogsum : Real.log (T + h) + Real.log (T - h) ≤ 2 * Real.log |T| := by
    rw [habsT]
    have heqmul : Real.log (T + h) + Real.log (T - h) = Real.log ((T + h) * (T - h)) :=
      (Real.log_mul hTp0.ne' hTh0.ne').symm
    rw [heqmul]
    have hle : (T + h) * (T - h) ≤ T * T := by nlinarith [sq_nonneg h]
    have h2 := Real.log_le_log (by positivity) hle
    rw [Real.log_mul hT0.ne' hT0.ne'] at h2
    linarith
  have hlogsum' : Real.log (T + h) + Real.log (T - h) ≤ 2 * Real.log T := by
    have hbridge : Real.log |T| = Real.log T := congrArg Real.log habsT
    linarith [hlogsum, hbridge]
  have hloglogsum : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
      ≤ 2 * Real.log (Real.log |T|) := by
    rw [habsT]
    have hlp : (0:ℝ) < Real.log (T + h) := Real.log_pos (by linarith)
    have hlm : (0:ℝ) < Real.log (T - h) := Real.log_pos (by linarith)
    have hlT : (0:ℝ) < Real.log T := Real.log_pos (by linarith)
    have hAMGM : Real.log (T + h) * Real.log (T - h) ≤ Real.log T * Real.log T := by
      -- writing `a = log(T+h)`, `b = log(T-h)`, `L = log T`, the two hints are
      -- `a² - 2ab + b² ≥ 0` and `4L² - a² - 2ab - b² ≥ 0`; they ADD to `4L² - 4ab ≥ 0`, so this
      -- is linear in the monomials and needs no product search.
      linarith only [sq_nonneg (Real.log (T + h) - Real.log (T - h)),
        mul_nonneg
          (show (0:ℝ) ≤ 2 * Real.log T - Real.log (T + h) - Real.log (T - h) by
            linarith [hlogsum'])
          (show (0:ℝ) ≤ 2 * Real.log T + Real.log (T + h) + Real.log (T - h) by
            linarith [hlogsum'])]
    have heqmul : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
        = Real.log (Real.log (T + h) * Real.log (T - h)) := (Real.log_mul hlp.ne' hlm.ne').symm
    rw [heqmul]
    have h2 := Real.log_le_log (by positivity) hAMGM
    rw [Real.log_mul hlT.ne' hlT.ne'] at h2
    linarith
  have hloglogsum' : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
      ≤ 2 * Real.log (Real.log T) := by
    have hbridge : Real.log (Real.log |T|) = Real.log (Real.log T) := by rw [habsT]
    linarith [hloglogsum, hbridge]
  -- Step 8: one-sided bounds on `(1/(2π))·∫D(T+h)` and `-(1/(2π))·∫D(T-h)` from `hai_p`/`hai_m`.
  have hDp_le : (1 / (2 * Real.pi)) *
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
      ≤ r / 2 * (-Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖
          + 1 / Real.pi * ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T + h) θ) := by
    have hstep : (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
        ≤ (1 / (2 * Real.pi)) *
          |∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    exact le_trans hstep hai_p
  have hDm_le : -((1 / (2 * Real.pi)) *
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u))
      ≤ r / 2 * (-Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖
          + 1 / Real.pi * ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T - h) θ) := by
    have hstep : -((1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u))
        ≤ (1 / (2 * Real.pi)) *
          |∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    exact le_trans hstep hai_m
  -- Step 9: a crude bound on `arcErr_tight`, using `T-h, T+h` both far in excess of `10^12`.
  have hTh12p : (10:ℝ) ^ (12:ℕ) < T + h := by linarith
  have harcErr_p := arcErr_tight_crude_lt_three hr0 hr1 (by linarith [hTh12p] : (20:ℝ) < T + h)
  have harcErr_m := arcErr_tight_crude_lt_three hr0 hr1 (by linarith [hT] : (20:ℝ) < T - h)
  -- Step 10: the exact closed form of the target, cleared of divisions, and the final comparison.
  have hclose : ((2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
        + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
        + 2 * A3 α r k * h + A6 α r
        + (4 * h / (Real.pi * (T - h)) + 2) / (r - α))
      * (2 * Real.pi * (1 - (1 - r) - α))
      = 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
          + 4 * c1 r * r * Real.log |T|
        + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
          + 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|)
        + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
        + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
          + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
          + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + 8 * h / (T - h) + 4 * Real.pi := by
    unfold A1 A2 A3 A4 A5 A6
    have hrα'' : (1:ℝ) - (1 - r) - α ≠ 0 := by
      rw [show (1:ℝ) - (1 - r) - α = r - α by ring]; exact hrα'.ne'
    have hTh0' : (T - h) ≠ 0 := hTh0.ne'
    push_cast
    field_simp
    ring
  refine lt_of_le_of_lt hmain ?_
  rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * (1 - (1 - r) - α)),
    hclose]
  -- Step 11: combine `hDp_le`,`hDm_le` with `FcrZeta_integral_le`/`leong_log_zeta_one_bound`/the
  -- `log`/`log log` window-sum bounds via `Dcombo_bound`, then chain through `hclaim2`, `hmt`,
  -- `hol` to bound the whole bracket, matching `hclose`'s closed form via one final `ring`.
  have hc1nn := c1_nonneg hr0 hr1
  have hc2nn := c2_nonneg hr0
  have hleong_p' : -Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖
      ≤ Real.log (Real.log (T + h)) + Real.log 29.388 := by
    rw [show |T + h| = T + h from abs_of_pos hTp0] at hleong_p
    rw [show ((1:ℝ):ℂ) = (1:ℂ) from by norm_num]
    exact hleong_p
  have hleong_m' : -Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖
      ≤ Real.log (Real.log (T - h)) + Real.log 29.388 := by
    rw [show |T - h| = T - h from abs_of_pos hTh0] at hleong_m
    rw [show ((1:ℝ):ℂ) = (1:ℂ) from by norm_num]
    exact hleong_m
  have hDcombo := Dcombo_bound (r := r) (c1' := c1 r) (c2' := c2 r) (c3' := c3 r) (c4' := c4 r)
    (logTp := Real.log (T + h)) (logTm := Real.log (T - h))
    (loglogTp := Real.log (Real.log (T + h))) (loglogTm := Real.log (Real.log (T - h)))
    (Lp := Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖)
    (Lm := Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖)
    (Fp := ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T + h) θ)
    (Fm := ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T - h) θ)
    (arcp := arcErr_tight r (T + h)) (arcm := arcErr_tight r (T - h))
    (logT := Real.log T) (loglogT := Real.log (Real.log T)) (log29 := Real.log 29.388)
    hr0 hc1nn hc2nn hFI_p hFI_m hleong_p' hleong_m' hlogsum' hloglogsum' harcErr_p harcErr_m
  have hDsum : (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
      - (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u)
      ≤ c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
        + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388 + 2 * r :=
    le_trans (by linarith [hDp_le, hDm_le]) hDcombo
  have hI3I4 : (1 / (2 * Real.pi)) *
      ((∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
        - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      ≤ (1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
            + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388 + 2 * r) :=
    hclaim2.trans (by linarith [hDsum])
  have hI1I2 : (1 / (2 * Real.pi)) *
      ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
        - ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
      < h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + 4 * h / (Real.pi * (T - h)) + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi := by
    have heq : (1 / (2 * Real.pi)) *
        ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        = (1 / (2 * Real.pi)) *
            (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          + -(1 / (2 * Real.pi) * ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖) := by
      ring
    rw [heq]
    linarith [hmt, hol]
  have hbracket_scaled : (1 / (2 * Real.pi)) *
      ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      < (h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + 4 * h / (Real.pi * (T - h)) + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
        + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
            + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388 + 2 * r)) := by
    have heq : (1 / (2 * Real.pi)) *
        ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
            - ∫ t in (T - h)..(T + h),
                Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
          + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
        - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      = (1 / (2 * Real.pi)) *
          ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
            - ∫ t in (T - h)..(T + h),
                Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + (1 / (2 * Real.pi)) *
          ((∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
            - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I)) := by
      ring
    rw [heq]
    linarith [hI1I2, hI3I4]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hmul := mul_lt_mul_of_pos_left hbracket_scaled h2pi
  have heqL : (2 * Real.pi) * ((1 / (2 * Real.pi)) *
      ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I)))
      = (((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I) := by
    rw [← mul_assoc, show (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 from by field_simp, one_mul]
  -- `heqR` is a genuine `≤`, not `=`: the `c1`/`c2` coefficients here carry deliberate slack
  -- (half the budget `hclose`'s `A4`/`A5` allow), and `4πr ≤ 4π` (via `r < 1`) absorbs the rest.
  have hlogTeq : Real.log T = Real.log |T| := by rw [habsT]
  have hloglogTeq : Real.log (Real.log T) = Real.log (Real.log |T|) := by rw [habsT]
  have hlogT_pos : (0:ℝ) < Real.log |T| := by rw [← hlogTeq]; exact Real.log_pos (by linarith)
  have hc1_slack : 2 * c1 r * r * Real.log T ≤ 4 * c1 r * r * Real.log |T| := by
    rw [hlogTeq]
    -- `2X ≤ 4X` for the single atom `X = c1 r * r * log|T| ≥ 0`; `only` keeps the ambient
    -- integral bounds out of the simplex tableau, which is what made this the file's hotspot.
    linarith only [mul_nonneg (mul_nonneg hc1nn hr0.le) hlogT_pos.le]
  have hc2_slack : (2 * Real.pi * r + 2 * c2 r * r) * Real.log (Real.log T)
      ≤ 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|) := by
    rw [hloglogTeq]
    have hloglogT_nonneg : (0:ℝ) ≤ Real.log (Real.log |T|) := by
      have hlogTgt1 : (1:ℝ) < Real.log T := one_lt_log_of_ge_three (by linarith)
      exact Real.log_nonneg (by linarith [hlogTeq])
    -- both sides are linear in the atom `log log|T|`; the two products supplied are exactly the
    -- slack, so `only` keeps the ambient bounds out of the tableau.
    linarith only [mul_nonneg (mul_nonneg hpi.le hr0.le) hloglogT_nonneg,
      mul_nonneg (mul_nonneg hc2nn hr0.le) hloglogT_nonneg]
  have hconst_slack : (4:ℝ) * Real.pi * r ≤ 4 * Real.pi := by nlinarith only [hpi, hr1]
  have heqR : (2 * Real.pi) *
      ((h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + 4 * h / (Real.pi * (T - h)) + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
        + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
            + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388 + 2 * r)))
      ≤ 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
          + 4 * c1 r * r * Real.log |T|
        + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
          + 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|)
        + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
        + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
          + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
          + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + 8 * h / (T - h) + 4 * Real.pi := by
    have heq : (2 * Real.pi) *
        ((h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
                + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
                + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
            + 4 * h / (Real.pi * (T - h)) + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
          + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
              + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                  + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388 + 2 * r)))
        = 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
            + 2 * c1 r * r * Real.log T
          + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
            + (2 * Real.pi * r + 2 * c2 r * r) * Real.log (Real.log T)
          + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
          + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
            + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
            + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
          + 8 * h / (T - h) + 4 * Real.pi * r := by
      have hTh0' : (T - h) ≠ 0 := hTh0.ne'
      field_simp
      ring
    rw [heq]
    linarith [hc1_slack, hc2_slack, hconst_slack]
  linarith [hmul, heqL, heqR]

set_option maxHeartbeats 400000 in
-- same large accumulated hypothesis context as `littlewoodshort`; see its own comment.
/-- **`Theorem \ref{thm:littlewoodshort}` (Theorem 32), tight version — matches the tex
exactly.** For `t-h>13`, `0<h`, `h<T`, `1>r>α>0` and `σ_k ≤ 1-r < σ_{k+1}`, bounds
`N(T-h,T+h,α)` by the `A₁…A₆` main term plus the tex's full un-collapsed `O^*` bracket.

### Summary of Proof
Exactly Theorem 32's own proof: apply Equation `\ref{eq:simplelittlewoodzerodensity}`
(Equation 14) with `σ_0 = 1-r`, `σ_1 = 1+ηr`; bound the first integral by
`Lemma \ref{lemma:littlewood-mainterm}` (Lemma 25), giving `A₁,A₂,A₃`; bound the integral outside
the critical strip by `Lemma \ref{lemma:littlewood-outerlog}` (Lemma 26), contributing
`Φ(1+ηr)/π` to `A₆`; convert the `arg ζ` integrals via `Lemma \ref{lem:littlewood-argsetup}`
(Lemma 27), with `arg ζ(1+ηr+i(t±h)) ≤ |log ζ| < log ζ(1+ηr)` contributing `(1+η)r log ζ(1+ηr)/π`
to `A₆`; and bound the two `Δ arg ζ` integrals by `r` times
`Theorem \ref{thm:circularregions1}` (Theorem 16), giving `A₄,A₅` and the rest of `A₆`. The `O^*`
term then tracks the accumulated errors.

### Lean Notes
**Exact match with the tex, term by term.** The tex's printed `O^*` bracket is
`(1/(r-α))( h/(π(t-h)²)(2 + 1158/(8log(t-h))) + (r/4)(E(r,t+h) + E(r,t-h)) )` with
`E(r,τ) = 2r/(3(τ-r)) + r/((τ-r)log τ - r) + 2/(τ-r)² + 1158/(8(τ-r)²log(τ-r))`.
The first factor is the first two Lean summands, and `E(r,τ)` is exactly
`JensenBounds.arcErr_tight r τ` — the middle term matching after multiplying numerator and
denominator by `(τ-r)`: `(r/(τ-r))/(log τ - r/(τ-r)) = r/((τ-r)log τ - r)`.

Assembled like `littlewoodshort` but with `littlewood_mainterm_tight`
(`\ref{prop:interpolation}`, Proposition 35's genuinely tight `O(1/t²)` bound) in place of
`littlewood_mainterm`'s `O(1/t)`, giving an error a full power of `T-h` sharper.

**No crude constant-bounding anywhere.** `arcErr_tight r (T±h)` appear directly as exact terms,
via `Dcombo_bound_exact`, which keeps `r/4*(arcp+arcm)` symbolic;
`arcErr_tight_crude_lt_three` — which would round the arc remainder to a flat constant `<3`,
producing a flat `+2` in the bracket and forcing an inflated threshold — is not called here.

**Threshold `13 < T - h` matches the tex exactly.** Without the crude rounding step the binding
constraint is `13 < T±h` from `FcrZeta_integral_le`/`leong_log_zeta_one_bound` (the
`circularregions1_tight` machinery); `littlewood_mainterm_tight` needs only `12 < T-h`. Since
`h > 0`, `13 < T-h` gives `13 < T+h` too, so it alone suffices.

The hypothesis `0 < h` is needed by `littlewood_mainterm_tight`'s strict `<`.

**On `arg ζ`.** As in `littlewoodshort`: `argZeta` is the tex's constructed branch
(`LittlewoodMethod.argZetaDef`), so the polar form and the continuity along the two segments
`[1-r, 1+ηr] + i(T±h)` that `ArgIntegrals.arg_integrals` (Theorem 31) needs are theorems, proved
from `hzf_p`/`hzf_m` (`LittlewoodIdentity.zeta_eq_norm_mul_exp_argZetaDef'`,
`argZetaDef_continuousOn_line'`), not hypotheses. The
tex's two cases for `arg ζ` after Equation `\ref{eq:zerodensityintegral}` (Equation 13) — a
zero-free line, where `arg ζ` is defined by continuous variation (this is `argZetaDef`), and a line
through a zero, where the tex uses the convention `lim_{ε→0} ½(arg ζ(·+i(T+ε)) + arg ζ(·+i(T-ε)))`
with the matching one for `N` — are as in `littlewoodshort`; this theorem is the first case for
both lines `T±h`, and the second is not formalized.

**`hzf_p`/`hzf_m`**: as in `littlewoodshort` — inherited from
`LittlewoodIdentity.littlewood_zero_density_integral` (Equation 13); both are the tex's first
case. No left-edge hypothesis is needed
(`LittlewoodIdentity.intervalIntegrable_log_norm_zeta_vertical`).

### References
tex: `\ref{thm:littlewoodshort}` (Theorem 32), tex lines 1093–1117. Consumes Equation
`\ref{eq:simplelittlewoodzerodensity}` (Equation 14), `\ref{lemma:littlewood-mainterm}`
(Lemma 25), `\ref{lemma:littlewood-outerlog}` (Lemma 26), `\ref{lem:littlewood-argsetup}`
(Lemma 27), `\ref{thm:circularregions1}` (Theorem 16), `\ref{prop:interpolation}`
(Proposition 35).

### Dependencies
**Depends on:** `simplelittlewoodzerodensity`, `littlewood_mainterm_tight`,
`littlewood_outerlog`, `littlewood_argsetup`, `arg_integrals`, `FcrZeta_integral_le`,
`FcrZeta_even`, `FcrZeta_intervalIntegrable`, `zeta_eq_norm_mul_exp_argZetaDef'`,
`argZetaDef_continuousOn_line'`, `zeta_ne_zero_line_of_Icc`, `c1_nonneg`, `c2_nonneg`,
`ExternalFacts.leong_log_zeta_one_bound`, `Dcombo_bound_exact`, `arcErr_tight`, `A1`–`A6`,
`Common.RealLogBounds.two_lt_log_of_gt_eight`/`one_lt_log_of_ge_three`.
**Used by:** `MainTheoremTight.mainLittlewoodTight`; and `MainTheorem.ULittlewood`/`ELittlewood`
transcribe this theorem's main and error terms for `\ref{thm:main-littlewood}` (Theorem 3). -/
theorem littlewoodshort_tight {T h r α : ℝ} {k : ℤ} (hT : (13 : ℝ) < T - h) (hh0 : 0 < h)
    (hh : h < T) (hα : 0 < α) (hrα : α < r) (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (T + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (T - h) * Complex.I) ≠ 0) :
    (Nrect (T - h) (T + h) α : ℝ)
      < (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
        + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
        + 2 * A3 α r k * h + A6 α r
        + (2 * h / (Real.pi * (T - h) ^ 2)
            + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h))
            + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h))) / (r - α) := by
  have hpi := Real.pi_pos
  have hTh0 : (0:ℝ) < T - h := by linarith
  have hTp0 : (0:ℝ) < T + h := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have habsT : |T| = T := abs_of_pos hT0
  have hr0 : (0:ℝ) < r := by linarith [sigma_lt_one (k + 1), hk']
  have hr1 : r < 1 := by linarith [sigma_pos k, hk]
  have heta := eta_mem_Ioo
  have hrα' : (0:ℝ) < r - α := by linarith
  have hσ1gt1 : (1:ℝ) < 1 + eta * r := by nlinarith [heta.1]
  have hσ0leσ1 : (1 - r : ℝ) ≤ 1 + eta * r := by nlinarith [heta.1.le]
  -- Step 1: `simplelittlewoodzerodensity`
  have hden : (0:ℝ) < 1 - (1 - r) - α := by linarith
  have hσ1ge : (1:ℝ) - α ≤ 1 + eta * r := by nlinarith [heta.1, hr0]
  have hmain := simplelittlewoodzerodensity (T := T) (h := h) (α := α) (σ0 := 1 - r)
    (σ1 := 1 + eta * r) hden hh0 hTh0 hσ1ge hσ1gt1 hzf_p hzf_m
  -- Step 2: `littlewood_mainterm_tight` at `σ0 = 1-r` (the tight replacement for
  -- `littlewood_mainterm`, needing only `12 < T-h`).
  have hTh12 : (12:ℝ) < T - h := by linarith
  have hmt := littlewood_mainterm_tight (k := k) (σ := 1 - r) (T := T) (h := h) hk hk' hh0 hTh12
  -- Step 3: `littlewood_outerlog` at `σ1 = 1+ηr`
  have hol := littlewood_outerlog (σ := 1 + eta * r) (T := T) (h := h) hh0.le hh hσ1gt1.le
  -- `argZeta = argZetaDef` is a continuous argument of `ζ` on the two zero-free edges
  have hzf_p' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hzf_p x hx
  have hzf_m' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hzf_m x hx
  have hline_p : ∀ x, 1 - r ≤ x → riemannZeta ((x : ℂ) + ((T + h : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    zeta_ne_zero_line_of_Icc hσ1gt1 hzf_p' le_rfl
  have hline_m : ∀ x, 1 - r ≤ x → riemannZeta ((x : ℂ) + ((T - h : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    zeta_ne_zero_line_of_Icc hσ1gt1 hzf_m' le_rfl
  have hpol_p' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I)
        = ‖riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I)‖
          * Complex.exp (argZeta (x + ((T + h : ℝ) : ℂ) * Complex.I) * Complex.I) :=
    fun x hx => zeta_eq_norm_mul_exp_argZetaDef' hTp0.ne' hline_p hx.1
  have hpol_m' : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r),
      riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I)
        = ‖riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I)‖
          * Complex.exp (argZeta (x + ((T - h : ℝ) : ℂ) * Complex.I) * Complex.I) :=
    fun x hx => zeta_eq_norm_mul_exp_argZetaDef' hTh0.ne' hline_m hx.1
  have hcont_p : ContinuousOn (fun x : ℝ => argZeta (x + ((T + h : ℝ) : ℂ) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := argZetaDef_continuousOn_line' hTp0.ne' hline_p
  have hcont_m : ContinuousOn (fun x : ℝ => argZeta (x + ((T - h : ℝ) : ℂ) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := argZetaDef_continuousOn_line' hTh0.ne' hline_m
  have hcont_p2 : ContinuousOn (fun u : ℝ => argZeta (u + (T + h) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := by
    have := hcont_p
    push_cast at this
    exact this
  have hcont_m2 : ContinuousOn (fun u : ℝ => argZeta (u + (T - h) * Complex.I))
      (Set.Icc (1 - r) (1 + eta * r)) := by
    have := hcont_m
    push_cast at this
    exact this
  have hint_p : IntervalIntegrable (fun u : ℝ => argZeta (u + ((T + h : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (1 - r) (1 + eta * r) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0leσ1]
    exact hcont_p
  have hint_m : IntervalIntegrable (fun u : ℝ => argZeta (u + ((T - h : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (1 - r) (1 + eta * r) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0leσ1]
    exact hcont_m
  -- Step 4: `littlewood_argsetup`
  obtain ⟨hclaim1, hclaim2⟩ :=
    littlewood_argsetup (σ0 := 1 - r) (σ1 := 1 + eta * r) (T := T) (h := h) hσ1gt1 hσ0leσ1
      hcont_p2 hcont_m2
  -- Step 5: `arg_integrals`, at `T+h` and `T-h`, with `c := 1`, radius `r`, `Fcr := FcrZeta r ·`.
  have hf : ∀ s : ℂ, (starRingEnd ℂ) (riemannZeta s) = riemannZeta ((starRingEnd ℂ) s) :=
    fun s => (riemannZeta_conj s).symm
  have hc_ineq : (1 + eta * r : ℝ) - 1 ≤ eta * (1 - (1 - r)) := le_of_eq (by ring)
  -- the hypotheses `arg_integrals` needs about `ζ` and `argZeta` on the two segments
  have hr1' : r < 1 := by linarith [sigma_pos k, hk]
  have hTr_p : r < T + h := by linarith [hT, hr1', hh0]
  have hTr_m : r < T - h := by linarith [hT, hr1']
  have hfan_gen : ∀ T' : ℝ, r < T' →
      AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall (((1 : ℝ) : ℂ) + ((T' : ℝ) : ℂ) * Complex.I) ((1 : ℝ) - (1 - r))) := by
    intro T' hT'
    apply analyticOn_riemannZeta.mono
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    subst h1
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have e : (1 : ℂ) - (((1 : ℝ) : ℂ) + ((T' : ℝ) : ℂ) * Complex.I)
        = -(((T' : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [e, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)] at hz
    linarith
  have hai_p := arg_integrals riemannZeta argZeta hf (σ0 := 1 - r) (σ1 := 1 + eta * r) (c := 1)
    (T := T + h) (Fcr := FcrZeta r (T + h))
    (by apply riemannZeta_ne_zero_of_one_le_re; simp)
    (by linarith) hσ1gt1.le hc_ineq (hfan_gen (T + h) hTr_p) hpol_p' hcont_p
    (FcrZeta_even r (T + h))
    (by
      intro θ
      have heq : (((1 : ℝ) : ℂ) - ((1 - r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := by push_cast; ring
      rw [heq]; unfold FcrZeta; norm_num)
    (FcrZeta_intervalIntegrable r (T + h) 0 Real.pi)
  have hai_m := arg_integrals riemannZeta argZeta hf (σ0 := 1 - r) (σ1 := 1 + eta * r) (c := 1)
    (T := T - h) (Fcr := FcrZeta r (T - h))
    (by apply riemannZeta_ne_zero_of_one_le_re; simp)
    (by linarith) hσ1gt1.le hc_ineq (hfan_gen (T - h) hTr_m) hpol_m' hcont_m
    (FcrZeta_even r (T - h))
    (by
      intro θ
      have heq : (((1 : ℝ) : ℂ) - ((1 - r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := by push_cast; ring
      rw [heq]; unfold FcrZeta; norm_num)
    (FcrZeta_intervalIntegrable r (T - h) 0 Real.pi)
  simp only [show (1:ℝ) - (1 - r) = r from by ring] at hai_p hai_m
  have hexpand : ∀ T' : ℝ, IntervalIntegrable (fun u : ℝ => argZeta (u + T' * Complex.I))
        MeasureTheory.volume (1 - r) (1 + eta * r) →
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u)
      = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
        - ((1 + eta * r) - (1 - r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
    intro T' hint
    have hpt : ∀ u : ℝ, deltaArgZeta T' (1 + eta * r) u
        = argZeta (u + T' * Complex.I) - argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
      intro u; unfold deltaArgZeta; push_cast; ring
    calc (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u)
        = ∫ u in (1 - r)..(1 + eta * r),
            (argZeta (u + T' * Complex.I) - argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I)) :=
          intervalIntegral.integral_congr (fun u _ => hpt u)
      _ = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
          - ∫ _u in (1 - r)..(1 + eta * r), argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) :=
          intervalIntegral.integral_sub hint intervalIntegrable_const
      _ = (∫ u in (1 - r)..(1 + eta * r), argZeta (u + T' * Complex.I))
          - ((1 + eta * r) - (1 - r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hinner_eq : ∀ T' : ℝ, IntervalIntegrable (fun u : ℝ => argZeta (u + T' * Complex.I))
        MeasureTheory.volume (1 - r) (1 + eta * r) →
      (∫ σ in (1 + eta * r)..(1 - r), argZeta (σ + T' * Complex.I))
        - ((1 - r) - (1 + eta * r)) * argZeta (((1 + eta * r : ℝ) : ℂ) + T' * Complex.I)
      = -(∫ u in (1 - r)..(1 + eta * r), deltaArgZeta T' (1 + eta * r) u) := by
    intro T' hint
    rw [hexpand T' hint, intervalIntegral.integral_symm (1 - r) (1 + eta * r)]
    ring
  rw [hinner_eq (T + h) hint_p] at hai_p
  rw [hinner_eq (T - h) hint_m] at hai_m
  rw [abs_neg] at hai_p hai_m
  -- Step 6: `FcrZeta_integral_le` and `leong_log_zeta_one_bound`, at `T+h` and `T-h`.
  have hT13p : (13:ℝ) < T + h := by linarith
  have hT13m : (13:ℝ) < T - h := by linarith
  have hlog_of : ∀ t : ℝ, (13:ℝ) < t → r / (t - r) < Real.log t := by
    intro t ht13
    have htr : (0:ℝ) < t - r := by linarith
    have hlt2 : (2:ℝ) < Real.log t := two_lt_log_of_gt_eight (by linarith)
    have h1 : r / (t - r) ≤ 1 := by rw [div_le_one htr]; linarith
    linarith
  have hFI_p := FcrZeta_integral_le (r := r) (T := T + h) hr0 hr1 hT13p (hlog_of _ hT13p)
  have hFI_m := FcrZeta_integral_le (r := r) (T := T - h) hr0 hr1 hT13m (hlog_of _ hT13m)
  have hleong_p := leong_log_zeta_one_bound (t := T + h) (by rw [abs_of_pos hTp0]; linarith)
  have hleong_m := leong_log_zeta_one_bound (t := T - h) (by rw [abs_of_pos hTh0]; linarith)
  -- Step 7: `log(T+h)+log(T-h) ≤ 2 log|T|`, and the analogous `log log` bound.
  have hlogsum : Real.log (T + h) + Real.log (T - h) ≤ 2 * Real.log |T| := by
    rw [habsT]
    have heqmul : Real.log (T + h) + Real.log (T - h) = Real.log ((T + h) * (T - h)) :=
      (Real.log_mul hTp0.ne' hTh0.ne').symm
    rw [heqmul]
    have hle : (T + h) * (T - h) ≤ T * T := by nlinarith [sq_nonneg h]
    have h2 := Real.log_le_log (by positivity) hle
    rw [Real.log_mul hT0.ne' hT0.ne'] at h2
    linarith
  have hlogsum' : Real.log (T + h) + Real.log (T - h) ≤ 2 * Real.log T := by
    have hbridge : Real.log |T| = Real.log T := congrArg Real.log habsT
    linarith [hlogsum, hbridge]
  have hloglogsum : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
      ≤ 2 * Real.log (Real.log |T|) := by
    rw [habsT]
    have hlp : (0:ℝ) < Real.log (T + h) := Real.log_pos (by linarith)
    have hlm : (0:ℝ) < Real.log (T - h) := Real.log_pos (by linarith)
    have hlT : (0:ℝ) < Real.log T := Real.log_pos (by linarith)
    have hAMGM : Real.log (T + h) * Real.log (T - h) ≤ Real.log T * Real.log T := by
      -- writing `a = log(T+h)`, `b = log(T-h)`, `L = log T`, the two hints are
      -- `a² - 2ab + b² ≥ 0` and `4L² - a² - 2ab - b² ≥ 0`; they ADD to `4L² - 4ab ≥ 0`, so this
      -- is linear in the monomials and needs no product search.
      linarith only [sq_nonneg (Real.log (T + h) - Real.log (T - h)),
        mul_nonneg
          (show (0:ℝ) ≤ 2 * Real.log T - Real.log (T + h) - Real.log (T - h) by
            linarith [hlogsum'])
          (show (0:ℝ) ≤ 2 * Real.log T + Real.log (T + h) + Real.log (T - h) by
            linarith [hlogsum'])]
    have heqmul : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
        = Real.log (Real.log (T + h) * Real.log (T - h)) := (Real.log_mul hlp.ne' hlm.ne').symm
    rw [heqmul]
    have h2 := Real.log_le_log (by positivity) hAMGM
    rw [Real.log_mul hlT.ne' hlT.ne'] at h2
    linarith
  have hloglogsum' : Real.log (Real.log (T + h)) + Real.log (Real.log (T - h))
      ≤ 2 * Real.log (Real.log T) := by
    have hbridge : Real.log (Real.log |T|) = Real.log (Real.log T) := by rw [habsT]
    linarith [hloglogsum, hbridge]
  -- Step 8: one-sided bounds on `(1/(2π))·∫D(T+h)` and `-(1/(2π))·∫D(T-h)` from `hai_p`/`hai_m`.
  have hDp_le : (1 / (2 * Real.pi)) *
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
      ≤ r / 2 * (-Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖
          + 1 / Real.pi * ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T + h) θ) := by
    have hstep : (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
        ≤ (1 / (2 * Real.pi)) *
          |∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    exact le_trans hstep hai_p
  have hDm_le : -((1 / (2 * Real.pi)) *
      (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u))
      ≤ r / 2 * (-Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖
          + 1 / Real.pi * ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T - h) θ) := by
    have hstep : -((1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u))
        ≤ (1 / (2 * Real.pi)) *
          |∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    exact le_trans hstep hai_m
  -- Step 10: the exact closed form of the target, cleared of divisions, and the final comparison.
  have hlogTh0 : Real.log (T - h) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hclose : ((2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log |T|
        + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log |T|)
        + 2 * A3 α r k * h + A6 α r
        + (2 * h / (Real.pi * (T - h) ^ 2)
            + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h))
            + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h))) / (r - α))
      * (2 * Real.pi * (1 - (1 - r) - α))
      = 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
          + 4 * c1 r * r * Real.log |T|
        + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
          + 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|)
        + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
        + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
          + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
          + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + 4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h))
        + Real.pi * r / 2 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)) := by
    unfold A1 A2 A3 A4 A5 A6
    have hrα'' : (1:ℝ) - (1 - r) - α ≠ 0 := by
      rw [show (1:ℝ) - (1 - r) - α = r - α by ring]; exact hrα'.ne'
    have hTh0' : (T - h) ≠ 0 := hTh0.ne'
    push_cast
    field_simp
    ring
  refine lt_of_le_of_lt hmain ?_
  rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * (1 - (1 - r) - α)),
    hclose]
  -- Step 11: combine `hDp_le`,`hDm_le` with `FcrZeta_integral_le`/`leong_log_zeta_one_bound`/the
  -- `log`/`log log` window-sum bounds via `Dcombo_bound_exact`, then chain through `hclaim2`,
  -- `hmt`, `hol` to bound the whole bracket, matching `hclose`'s closed form via one final `ring`.
  have hc1nn := c1_nonneg hr0 hr1
  have hc2nn := c2_nonneg hr0
  have hleong_p' : -Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖
      ≤ Real.log (Real.log (T + h)) + Real.log 29.388 := by
    rw [show |T + h| = T + h from abs_of_pos hTp0] at hleong_p
    rw [show ((1:ℝ):ℂ) = (1:ℂ) from by norm_num]
    exact hleong_p
  have hleong_m' : -Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖
      ≤ Real.log (Real.log (T - h)) + Real.log 29.388 := by
    rw [show |T - h| = T - h from abs_of_pos hTh0] at hleong_m
    rw [show ((1:ℝ):ℂ) = (1:ℂ) from by norm_num]
    exact hleong_m
  have hDcombo := Dcombo_bound_exact (r := r) (c1' := c1 r) (c2' := c2 r) (c3' := c3 r)
    (c4' := c4 r)
    (logTp := Real.log (T + h)) (logTm := Real.log (T - h))
    (loglogTp := Real.log (Real.log (T + h))) (loglogTm := Real.log (Real.log (T - h)))
    (Lp := Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T + h : ℝ):ℂ) * Complex.I)‖)
    (Lm := Real.log ‖riemannZeta (((1:ℝ):ℂ) + ((T - h : ℝ):ℂ) * Complex.I)‖)
    (Fp := ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T + h) θ)
    (Fm := ∫ θ in (0:ℝ)..Real.pi, FcrZeta r (T - h) θ)
    (arcp := arcErr_tight r (T + h)) (arcm := arcErr_tight r (T - h))
    (logT := Real.log T) (loglogT := Real.log (Real.log T)) (log29 := Real.log 29.388)
    hr0 hc1nn hc2nn hFI_p hFI_m hleong_p' hleong_m' hlogsum' hloglogsum'
  have hDsum : (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T + h) (1 + eta * r) u)
      - (1 / (2 * Real.pi)) *
        (∫ u in (1 - r)..(1 + eta * r), deltaArgZeta (T - h) (1 + eta * r) u)
      ≤ c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
        + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388
        + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)) :=
    le_trans (by linarith [hDp_le, hDm_le]) hDcombo
  have hI3I4 : (1 / (2 * Real.pi)) *
      ((∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
        - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      ≤ (1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
            + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388
            + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h))) :=
    hclaim2.trans (by linarith [hDsum])
  have hI1I2 : (1 / (2 * Real.pi)) *
      ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
        - ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
      < h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + (2 * h / (Real.pi * (T - h) ^ 2)
              + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h)))
          + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi := by
    have heq : (1 / (2 * Real.pi)) *
        ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        = (1 / (2 * Real.pi)) *
            (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          + -(1 / (2 * Real.pi) * ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖) := by
      ring
    rw [heq]
    linarith [hmt, hol]
  have hbracket_scaled : (1 / (2 * Real.pi)) *
      ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      < (h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + (2 * h / (Real.pi * (T - h) ^ 2)
              + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h)))
          + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
        + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
            + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388
                + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)))) := by
    have heq : (1 / (2 * Real.pi)) *
        ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
            - ∫ t in (T - h)..(T + h),
                Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
          + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
        - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I))
      = (1 / (2 * Real.pi)) *
          ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
            - ∫ t in (T - h)..(T + h),
                Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + (1 / (2 * Real.pi)) *
          ((∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
            - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I)) := by
      ring
    rw [heq]
    linarith [hI1I2, hI3I4]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hmul := mul_lt_mul_of_pos_left hbracket_scaled h2pi
  have heqL : (2 * Real.pi) * ((1 / (2 * Real.pi)) *
      ((((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I)))
      = (((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (((1 - r:ℝ):ℂ) + t * Complex.I)‖)
          - ∫ t in (T - h)..(T + h),
              Real.log ‖riemannZeta (((1 + eta * r:ℝ):ℂ) + t * Complex.I)‖)
        + ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T + ↑h) * Complex.I))
      - ∫ u in (1 - r)..(1 + eta * r), argZeta (↑u + (↑T - ↑h) * Complex.I) := by
    rw [← mul_assoc, show (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 from by field_simp, one_mul]
  have hlogTeq : Real.log T = Real.log |T| := by rw [habsT]
  have hloglogTeq : Real.log (Real.log T) = Real.log (Real.log |T|) := by rw [habsT]
  have hlogT_pos : (0:ℝ) < Real.log |T| := by rw [← hlogTeq]; exact Real.log_pos (by linarith)
  have hc1_slack : 2 * c1 r * r * Real.log T ≤ 4 * c1 r * r * Real.log |T| := by
    rw [hlogTeq]
    -- `2X ≤ 4X` for the single atom `X = c1 r * r * log|T| ≥ 0`; `only` keeps the ambient
    -- integral bounds out of the simplex tableau, which is what made this the file's hotspot.
    linarith only [mul_nonneg (mul_nonneg hc1nn hr0.le) hlogT_pos.le]
  have hc2_slack : (2 * Real.pi * r + 2 * c2 r * r) * Real.log (Real.log T)
      ≤ 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|) := by
    rw [hloglogTeq]
    have hloglogT_nonneg : (0:ℝ) ≤ Real.log (Real.log |T|) := by
      have hlogTgt1 : (1:ℝ) < Real.log T := one_lt_log_of_ge_three (by linarith)
      exact Real.log_nonneg (by linarith [hlogTeq])
    -- both sides are linear in the atom `log log|T|`; the two products supplied are exactly the
    -- slack, so `only` keeps the ambient bounds out of the tableau.
    linarith only [mul_nonneg (mul_nonneg hpi.le hr0.le) hloglogT_nonneg,
      mul_nonneg (mul_nonneg hc2nn hr0.le) hloglogT_nonneg]
  have heqR : (2 * Real.pi) *
      ((h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
          + (2 * h / (Real.pi * (T - h) ^ 2)
              + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h)))
          + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
        + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
            + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388
                + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)))))
      ≤ 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
          + 4 * c1 r * r * Real.log |T|
        + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
          + 4 * (c2 r * r + Real.pi * r) * Real.log (Real.log |T|)
        + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
        + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
          + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
          + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
        + 4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h))
        + Real.pi * r / 2 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)) := by
    have heq : (2 * Real.pi) *
        ((h * ((mCoeff k * (1 - r) + bCoeff k) / Real.pi * Real.log |T|
                + (mCoeffP k * (1 - r) + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
                + (mCoeffPP k * (1 - r) + bCoeffPP k) / Real.pi)
            + (2 * h / (Real.pi * (T - h) ^ 2)
                + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h)))
            + (Phi ((1 + eta * r : ℝ) : ℂ)).re / Real.pi)
          + ((1 + eta * r - (1 - r)) / Real.pi * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
              + (c1 r * r / Real.pi * Real.log T + (r + c2 r * r / Real.pi) * Real.log (Real.log T)
                  + c4 r * r + c3 r * r / Real.pi + r * Real.log 29.388
                  + r / 4 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)))))
        = 2 * h * (mCoeff k * (1 - r) + bCoeff k) * Real.log |T|
            + 2 * c1 r * r * Real.log T
          + 2 * h * (mCoeffP k * (1 - r) + bCoeffP k) * Real.log (Real.log |T|)
            + (2 * Real.pi * r + 2 * c2 r * r) * Real.log (Real.log T)
          + 2 * h * (mCoeffPP k * (1 - r) + bCoeffPP k)
          + 2 * c3 r * r + 2 * c4 r * Real.pi * r + 2 * Real.pi * Real.log 29.388 * r
            + 2 * (Phi ((1 + eta * r : ℝ) : ℂ)).re
            + 2 * (1 + eta) * r * Real.log ‖riemannZeta ((1 + eta * r : ℝ) : ℂ)‖
          + 4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h))
          + Real.pi * r / 2 * (arcErr_tight r (T + h) + arcErr_tight r (T - h)) := by
      have hTh0' : (T - h) ≠ 0 := hTh0.ne'
      field_simp
      ring
    rw [heq]
    linarith [hc1_slack, hc2_slack]
  linarith [hmul, heqL, heqR]
