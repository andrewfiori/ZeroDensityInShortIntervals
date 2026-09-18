/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Jensen.JensenScaleConstants

/-! # Remark `\ref{rem:altcoefficients}`'s alternative `k = 0` triple, and its admissibility

`ZerosInShortIntervals.tex` offers **two** admissible values for the `k = 0` (half-line)
coefficient triple `(v₀, v₀', v₀'')`:

* the **main text** (the display just after Equation `\ref{eq:sigmak}` (Equation 4)) takes
  `(1/6, 1, log 0.611)`, from the Hiary–Revers half-line bound
  `|ζ(1/2+it)| ≤ 0.611|t|^{1/6}log|t|`;
* Remark `\ref{rem:altcoefficients}` (Remark 7), immediately following, says it is "also
  admissible" to take `(27/164, 0, log 66.7)`, from the Patel–Yang sub-Weyl bound
  `|ζ(1/2+it)| ≤ 66.7|t|^{27/164}`.

`JensenScaleConstants.lean` implements the **main-text** triple. **Every displayed table in the
paper is computed with the Remark's triple** — Remark 7 says so in as many words, and
`Code/compute_C2_tables.sage` sets `vCoeff 0 = 27/164`, `vCoeffP 0 = 0`,
`vCoeffPP 0 = log 66.7`. That covers Tables 2–11, Table `\ref{table:chat}` (Table 1), and the
abstract's `13%` and `10^43`. So the constants proved in `JensenScaleConstants.lean` are not the
constants printed in the paper: recomputing the tex's own defining sums at `r = 1/2` gives
`c₃ = 0.0982` under the main-text triple against the tabulated `3.0615`, a factor of 31, and
`c₁ = 0.148070` against the tabulated `0.1467868`.
`Code/indep_mpmath_tables_spotcheck.py` reproduces a row of Table `\ref{tab:rectangularjensen}`
(Table 5) only under the alternative triple, and
`Code/verify_section2_worked_example.py` computes both side by side.

**This file is therefore what ties the Lean to the paper's printed numbers**, and it is the only
place the tables' convention is formalized. The two triples agree for every `k ≥ 1`, so the
difference is confined to the `k = 0` chord and its mirror — which is also why the headline
threshold differs: `4A₁(α, 1/2, 0) < 1` reads `α < 1/6` on the main-text triple
(`PositiveProportion.four_mul_A1_half_lt_one`) and `α < 7/41` on the Remark's.

**Remark 7 offers a second alternative**, `v₀'' = log(0.470795 + 4.04972/log|T|)`, which this file
does not implement and does not need to: it is already formalized in the appendix. Its constants
are Revers Remark 3.1's, assumed as `Hypotheses.LiteratureInputs.revers_remark31`, and case (1c)
of Proposition `\ref{prop:interpolation}` (Proposition 35) is stated with exactly them —
`BackgroundZetaBounds.interpolated_bound_1c` runs on
`interpG1c 1.546 0.470795 4.04972 (1/14) (4e)`, matching the tex's own case (1c) display. Unlike
the triple, that alternative changes only the constant term, so it needs no new chord family.

This file discharges the Remark's "also admissible" claim: it defines the alternative coefficient
family and proves `zeta_piecewise_bound_alt`, the exact analogue of
`JensenScaleConstants.zeta_piecewise_bound` for that family. Nothing here modifies the existing
definitions, so no constant proved elsewhere changes.

## Why this is cheap

The two triples differ **only at `k = 0`**. Since `vCoeff k` for `k < 0` is defined by reflecting
the index `-k ≥ 1` (never `0`), the only chords that see the change are

* `k = 0`, the chord `(σ₀,v₀) → (σ₁,v₁)` on `[1/2, 5/7]`, and
* `k = -1`, its mirror `(σ_{-1},v_{-1}) → (σ₀,v₀)` on `[2/7, 1/2]`.

Every other chord is literally unchanged (`mCoeffAlt_eq`/`bCoeffAlt_eq` below), so those cases
delegate straight back to `zeta_piecewise_bound`.

And the `k = 0` case needs no new analysis at all: `BackgroundZetaBounds.interpolated_bound_1a` is
*already* the Patel–Yang-anchored interpolation on `[1/2, 5/7]` (`A = 66.7`, `p = 27/164`,
`ra = 0`), and its displayed coefficients `47/123 - 107/246σ`, `14/3(σ-1/2)`, and
`14/3(5/7-σ)log 66.7 + 14/3(σ-1/2)log 1.546` are *exactly* the three alternative chords —
`mCoeffAlt 0 = -107/246`, `bCoeffAlt 0 = 47/123`, and so on. Case (1a) of Proposition
`\ref{prop:interpolation}` (Proposition 35) is the Remark's triple in disguise.

## Provenance parity

`interpolated_bound_1a` rests on the numeric obligation `interpolated_bound_1a_hcompact`, a
theorem whose body reads the class field
`BackgroundZetaBounds.InterpolationCertificates.interpolated_bound_1a_hcompact` (certified by
`Code/indep_arb_hcompact.sage` over 125 arb-certified boxes), exactly as the main-text track's
`interpolated_bound_1b`
rests on `interpolated_bound_1b_hcompact`. So the two triples are established on the same
footing, and this file assumes nothing the main-text track does not.
-/

open scoped ComplexConjugate

/- Unproved inputs enter through the hypothesis classes: `LiteratureInputs` from
`ZerosInShortIntervals/Hypotheses.lean`, `BrentStirlingInputs` from `Background/ExternalFacts.lean`,
and `InterpolationCertificates`/`Hcompact2Certificates` from
`Background/BackgroundZetaBounds.lean`.  Lean includes an instance-implicit section variable in
every theorem in scope, so some statements carry a binder they do not use; the linter for that is
silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates]

/-! ### The alternative coefficient family -/

/-- **Alternative `v_k`, carrying the tex Remark's half-line value `v₀ = 27/164`** (Patel–Yang)
in place of the main text's `1/6`. Identical to `vCoeff` away from `k = 0`.

### Summary of Proof
A definition, not a theorem: `if k = 0 then 27/164 else vCoeff k`.

### References
tex: Remark `\ref{rem:altcoefficients}` (Remark 7), following Equation `\ref{eq:sigmak}`
(Equation 4), which states this triple is "also admissible". The value comes from Patel–Yang's
sub-Weyl bound `|ζ(1/2+it)| ≤ 66.7|t|^{27/164}`.

### Dependencies
**Depends on:** `vCoeff`.
**Used by:** `bCoeffAlt`, `bCoeffAlt_eq`, `bCoeffAlt_zero`, `mCoeffAlt`, `mCoeffAlt_eq`,
`mCoeffAlt_zero`, `vCoeffAlt_eq_of_ne`, `zeta_piecewise_bound_alt`. -/
noncomputable def vCoeffAlt (k : ℤ) : ℝ := if k = 0 then 27 / 164 else vCoeff k

/-- **Alternative `v_k'`, carrying the Remark's `v₀' = 0`** in place of the main text's `1`.
Identical to `vCoeffP` away from `k = 0`.

### Summary of Proof
A definition: `if k = 0 then 0 else vCoeffP k`. The sub-Weyl bound `66.7|t|^{27/164}` carries no
`log log|t|` factor, which is exactly why its `log log` coefficient vanishes — unlike the
Hiary–Revers half-line bound `0.611|t|^{1/6}log|t|`, whose trailing `log|t|` forces `v₀' = 1`.

### References
tex: Remark `\ref{rem:altcoefficients}` (Remark 7), following Equation `\ref{eq:sigmak}`
(Equation 4).

### Dependencies
**Depends on:** `vCoeffP`.
**Used by:** `bCoeffPAlt`, `bCoeffPAlt_eq`, `bCoeffPAlt_zero`, `mCoeffPAlt`, `mCoeffPAlt_eq`,
`mCoeffPAlt_zero`, `vCoeffPAlt_eq_of_ne`, `zeta_piecewise_bound_alt`. -/
noncomputable def vCoeffPAlt (k : ℤ) : ℝ := if k = 0 then 0 else vCoeffP k

/-- **Alternative `v_k''`, carrying the Remark's `v₀'' = log 66.7`** in place of the main text's
`log 0.611`. Identical to `vCoeffPP` away from `k = 0`.

### Summary of Proof
A definition: `if k = 0 then Real.log 66.7 else vCoeffPP k`.

### References
tex: Remark `\ref{rem:altcoefficients}` (Remark 7), following Equation `\ref{eq:sigmak}`
(Equation 4). The constant is the leading factor of Patel–Yang's sub-Weyl bound.

### Dependencies
**Depends on:** `vCoeffPP`.
**Used by:** `bCoeffPPAlt`, `bCoeffPPAlt_eq`, `chordPPAlt_zero`, `mCoeffPPAlt`, `mCoeffPPAlt_eq`,
`vCoeffPPAlt_eq_of_ne`, `zeta_piecewise_bound_alt`. -/
noncomputable def vCoeffPPAlt (k : ℤ) : ℝ := if k = 0 then Real.log 66.7 else vCoeffPP k

/-- **Slope of the alternative `log|t|` chord**, `m_k = (v_k - v_{k+1})/(σ_k - σ_{k+1})`.

### Summary of Proof
A definition: Equation `\ref{eq:mk}` (Equation 5) verbatim, with `vCoeffAlt` in place of
`vCoeff`.

### Lean Notes
The convention is unchanged from `mCoeff`: the denominator `σ_k - σ_{k+1}` is **negative**, and
the chord is evaluated at `σ` itself, not at `1-σ`. Read either way round, the slope looks to
have the wrong sign; the two conventions must be kept together.

### References
tex: Equation `\ref{eq:mk}` (Equation 5).

### Dependencies
**Depends on:** `sigma`, `vCoeffAlt`.
**Used by:** `bCoeffAlt`, `bCoeffAlt_eq`, `bCoeffAlt_zero`, `mCoeffAlt_eq`, `mCoeffAlt_zero`,
`zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
noncomputable def mCoeffAlt (k : ℤ) : ℝ :=
  (vCoeffAlt k - vCoeffAlt (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of the alternative `log|t|` chord**, `b_k = v_k - m_k σ_k`.

### Summary of Proof
A definition, Equation `\ref{eq:mk}` (Equation 5) with `vCoeffAlt`/`mCoeffAlt`. Together with
`mCoeffAlt` it makes `mCoeffAlt k * σ + bCoeffAlt k` the chord through `(σ_k, v_k)` and
`(σ_{k+1}, v_{k+1})`.

### References
tex: Equation `\ref{eq:mk}` (Equation 5).

### Dependencies
**Depends on:** `mCoeffAlt`, `sigma`, `vCoeffAlt`.
**Used by:** `bCoeffAlt_eq`, `bCoeffAlt_zero`, `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`.
-/
noncomputable def bCoeffAlt (k : ℤ) : ℝ := vCoeffAlt k - mCoeffAlt k * sigma k

/-- **Slope of the alternative `log log|t|` chord.**

### Summary of Proof
A definition: Equation `\ref{eq:mkp}` (Equation 6) with `vCoeffPAlt`.

### Lean Notes
Unlike `mCoeffP` — identically `0`, since `vCoeffP ≡ 1` makes that chord constant — this is
**nonzero** at `k = 0` and `k = -1`, because `vCoeffPAlt 0 = 0 ≠ 1 = vCoeffPAlt 1`. It is the
one structural difference between the two families beyond the numeric value of `v₀`.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `sigma`, `vCoeffPAlt`.
**Used by:** `bCoeffPAlt`, `bCoeffPAlt_eq`, `bCoeffPAlt_zero`, `mCoeffPAlt_eq`, `mCoeffPAlt_zero`,
`zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
noncomputable def mCoeffPAlt (k : ℤ) : ℝ :=
  (vCoeffPAlt k - vCoeffPAlt (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of the alternative `log log|t|` chord.**

### Summary of Proof
A definition: `b_k' = v_k' - m_k' σ_k`, Equation `\ref{eq:mkp}` (Equation 6).

### References
tex: Equation `\ref{eq:mkp}` (Equation 6).

### Dependencies
**Depends on:** `mCoeffPAlt`, `sigma`, `vCoeffPAlt`.
**Used by:** `bCoeffPAlt_eq`, `bCoeffPAlt_zero`, `zeta_chord_alt_zero`,
`zeta_piecewise_bound_alt`. -/
noncomputable def bCoeffPAlt (k : ℤ) : ℝ := vCoeffPAlt k - mCoeffPAlt k * sigma k

/-- **Slope of the alternative constant-term chord.**

### Summary of Proof
A definition: Equation `\ref{eq:mkpp}` (Equation 7) with `vCoeffPPAlt`.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `sigma`, `vCoeffPPAlt`.
**Used by:** `bCoeffPPAlt`, `bCoeffPPAlt_eq`, `chordPPAlt_zero`, `mCoeffPPAlt_eq`,
`zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
noncomputable def mCoeffPPAlt (k : ℤ) : ℝ :=
  (vCoeffPPAlt k - vCoeffPPAlt (k + 1)) / (sigma k - sigma (k + 1))

/-- **Intercept of the alternative constant-term chord.**

### Summary of Proof
A definition: `b_k'' = v_k'' - m_k'' σ_k`, Equation `\ref{eq:mkpp}` (Equation 7).

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7).

### Dependencies
**Depends on:** `mCoeffPPAlt`, `sigma`, `vCoeffPPAlt`.
**Used by:** `bCoeffPPAlt_eq`, `chordPPAlt_zero`, `zeta_chord_alt_zero`,
`zeta_piecewise_bound_alt`. -/
noncomputable def bCoeffPPAlt (k : ℤ) : ℝ := vCoeffPPAlt k - mCoeffPPAlt k * sigma k

/-! ### Agreement with the main-text family away from `k ∈ {0, -1}` -/

/-- **The two families' `v` agree away from `k = 0`.**

### Summary of Proof
Immediate from the definition of `vCoeffAlt`: `simp` discharges the `if`, since `k ≠ 0`.

### References
No tex counterpart — bookkeeping for the two-family comparison.

### Dependencies
**Depends on:** `vCoeffAlt`.
**Used by:** `mCoeffAlt_eq`, `bCoeffAlt_eq`. -/
theorem vCoeffAlt_eq_of_ne {k : ℤ} (hk : k ≠ 0) : vCoeffAlt k = vCoeff k := by
  simp [vCoeffAlt, hk]

/-- **The two families' `v'` agree away from `k = 0`.**

### Summary of Proof
Immediate from the definition of `vCoeffPAlt`: `simp` discharges the `if`, since `k ≠ 0`.

### References
No tex counterpart — bookkeeping for the two-family comparison.

### Dependencies
**Depends on:** `vCoeffPAlt`.
**Used by:** `mCoeffPAlt_eq`, `bCoeffPAlt_eq`. -/
theorem vCoeffPAlt_eq_of_ne {k : ℤ} (hk : k ≠ 0) : vCoeffPAlt k = vCoeffP k := by
  simp [vCoeffPAlt, hk]

/-- **The two families' `v''` agree away from `k = 0`.**

### Summary of Proof
Immediate from the definition of `vCoeffPPAlt`: `simp` discharges the `if`, since `k ≠ 0`.

### References
No tex counterpart — bookkeeping for the two-family comparison.

### Dependencies
**Depends on:** `vCoeffPPAlt`.
**Used by:** `mCoeffPPAlt_eq`, `bCoeffPPAlt_eq`, `zeta_piecewise_bound_alt`. -/
theorem vCoeffPPAlt_eq_of_ne {k : ℤ} (hk : k ≠ 0) : vCoeffPPAlt k = vCoeffPP k := by
  simp [vCoeffPPAlt, hk]

/-- **The `log|t|` chord slopes coincide except on the two chords touching `σ₀ = 1/2`.**

### Summary of Proof
A chord at index `k` interpolates `v_k` and `v_{k+1}`, so it sees the changed value exactly when
`k = 0` or `k = -1`. For any other `k`, both `k ≠ 0` and `k+1 ≠ 0` (the latter by `omega`), so
`vCoeffAlt_eq_of_ne` rewrites both endpoints and the two slopes are literally the same
expression.

### References
No tex counterpart — this is what makes the Remark's claim cheap to check, since only two chords
need separate treatment.

### Dependencies
**Depends on:** `mCoeffAlt`, `vCoeffAlt_eq_of_ne`.
**Used by:** `bCoeffAlt_eq`, `zeta_piecewise_bound_alt`. -/
theorem mCoeffAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : mCoeffAlt k = mCoeff k := by
  have h1' : k + 1 ≠ 0 := by omega
  simp only [mCoeffAlt, mCoeff, vCoeffAlt_eq_of_ne h0, vCoeffAlt_eq_of_ne h1']

/-- **The `log|t|` chord intercepts coincide except on the two chords touching `σ₀ = 1/2`.**

### Summary of Proof
`b_k = v_k - m_k σ_k`, and both factors agree away from the two affected indices — `v_k` by
`vCoeffAlt_eq_of_ne`, `m_k` by `mCoeffAlt_eq`.

### References
No tex counterpart — companion of `mCoeffAlt_eq`.

### Dependencies
**Depends on:** `bCoeffAlt`, `mCoeffAlt_eq`, `vCoeffAlt_eq_of_ne`.
**Used by:** `zeta_piecewise_bound_alt`. -/
theorem bCoeffAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : bCoeffAlt k = bCoeff k := by
  simp only [bCoeffAlt, bCoeff, vCoeffAlt_eq_of_ne h0, mCoeffAlt_eq h0 h1]

/-- **The `log log|t|` chord slopes coincide away from the two affected chords.**

### Summary of Proof
As `mCoeffAlt_eq`: both endpoints `v_k'`, `v_{k+1}'` agree by `vCoeffPAlt_eq_of_ne` once
`k ≠ 0` and `k+1 ≠ 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `mCoeffPAlt`, `vCoeffPAlt_eq_of_ne`.
**Used by:** `bCoeffPAlt_eq`, `zeta_piecewise_bound_alt`. -/
theorem mCoeffPAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : mCoeffPAlt k = mCoeffP k := by
  have h1' : k + 1 ≠ 0 := by omega
  simp only [mCoeffPAlt, mCoeffP, vCoeffPAlt_eq_of_ne h0, vCoeffPAlt_eq_of_ne h1']

/-- **The `log log|t|` chord intercepts coincide away from the two affected chords.**

### Summary of Proof
`b_k' = v_k' - m_k' σ_k`, with both factors handled by `vCoeffPAlt_eq_of_ne` and
`mCoeffPAlt_eq`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bCoeffPAlt`, `mCoeffPAlt_eq`, `vCoeffPAlt_eq_of_ne`.
**Used by:** `zeta_piecewise_bound_alt`. -/
theorem bCoeffPAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : bCoeffPAlt k = bCoeffP k := by
  simp only [bCoeffPAlt, bCoeffP, vCoeffPAlt_eq_of_ne h0, mCoeffPAlt_eq h0 h1]

/-- **The constant-term chord slopes coincide away from the two affected chords.**

### Summary of Proof
As `mCoeffAlt_eq`, with `vCoeffPPAlt_eq_of_ne` at both endpoints.

### References
No tex counterpart.

### Dependencies
**Depends on:** `mCoeffPPAlt`, `vCoeffPPAlt_eq_of_ne`.
**Used by:** `bCoeffPPAlt_eq`, `zeta_piecewise_bound_alt`. -/
theorem mCoeffPPAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : mCoeffPPAlt k = mCoeffPP k := by
  have h1' : k + 1 ≠ 0 := by omega
  simp only [mCoeffPPAlt, mCoeffPP, vCoeffPPAlt_eq_of_ne h0, vCoeffPPAlt_eq_of_ne h1']

/-- **The constant-term chord intercepts coincide away from the two affected chords.**

### Summary of Proof
`b_k'' = v_k'' - m_k'' σ_k`, with both factors handled by `vCoeffPPAlt_eq_of_ne` and
`mCoeffPPAlt_eq`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bCoeffPPAlt`, `mCoeffPPAlt_eq`, `vCoeffPPAlt_eq_of_ne`.
**Used by:** `zeta_piecewise_bound_alt`. -/
theorem bCoeffPPAlt_eq {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ -1) : bCoeffPPAlt k = bCoeffPP k := by
  simp only [bCoeffPPAlt, bCoeffPP, vCoeffPPAlt_eq_of_ne h0, mCoeffPPAlt_eq h0 h1]

/-! ### The two changed chords, in closed form -/

/-- **The three abscissae bounding the two changed chords:** `σ₀ = 1/2`, `σ₁ = 5/7`,
`σ_{-1} = 2/7`.

### Summary of Proof
Direct evaluation of `sigma` at `0`, `1`, `-1` by `norm_num`. From Equation
`\ref{eq:sigmak}` (Equation 4): `σ_k = 1 - (k+3)/(2^{k+3}-2)` for `k ≥ 0`, giving
`σ₀ = 1 - 3/6 = 1/2` and `σ₁ = 1 - 4/14 = 5/7`; and `σ_{-1} = 4/14 = 2/7` from the reflected
branch.

### References
tex: Equation `\ref{eq:sigmak}` (Equation 4).

### Dependencies
**Depends on:** `sigma`.
**Used by:** `zeta_piecewise_bound_alt`. -/
theorem sigma_zero_one_negone :
    sigma 0 = 1 / 2 ∧ sigma 1 = 5 / 7 ∧ sigma (-1) = 2 / 7 := by
  refine ⟨by norm_num [sigma], by norm_num [sigma], by norm_num [sigma]⟩

/-- **The alternative `k = 0` `log|t|` chord has slope `-107/246`** — precisely the coefficient
displayed in `BackgroundZetaBounds.interpolated_bound_1a`.

### Summary of Proof
`norm_num` on the definitions. By hand:
`m₀ = (v₀ - v₁)/(σ₀ - σ₁) = (27/164 - 1/14)/(1/2 - 5/7) = (93/1148)/(-3/14) = -107/246`.
Verified in exact rational arithmetic by `Code/verify_alt_chords.py`.

### References
tex: Equation `\ref{eq:mk}` (Equation 5) at `k = 0`, with the Remark's `v₀`. The resulting
number is the `log|t|` coefficient of case (1a) of Proposition `\ref{prop:interpolation}`
(Proposition 35).

### Dependencies
**Depends on:** `mCoeffAlt`, `vCoeffAlt`, `sigma`.
**Used by:** `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
theorem mCoeffAlt_zero : mCoeffAlt 0 = -(107 / 246) := by
  norm_num [mCoeffAlt, vCoeffAlt, vCoeff, sigma]

/-- **The alternative `k = 0` `log|t|` chord has intercept `47/123`.**

### Summary of Proof
`b₀ = v₀ - m₀σ₀ = 27/164 + (107/246)(1/2) = 47/123`, by `norm_num`. Verified exactly in
`Code/verify_alt_chords.py`.

### References
tex: Equation `\ref{eq:mk}` (Equation 5) at `k = 0`; the constant term of case (1a) of
Proposition `\ref{prop:interpolation}` (Proposition 35)'s `log|t|` coefficient.

### Dependencies
**Depends on:** `bCoeffAlt`, `mCoeffAlt`, `vCoeffAlt`, `sigma`.
**Used by:** `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
theorem bCoeffAlt_zero : bCoeffAlt 0 = 47 / 123 := by
  norm_num [bCoeffAlt, mCoeffAlt, vCoeffAlt, vCoeff, sigma]

/-- **The alternative `k = 0` `log log|t|` chord has slope `14/3`.**

### Summary of Proof
`m₀' = (v₀' - v₁')/(σ₀ - σ₁) = (0 - 1)/(1/2 - 5/7) = (-1)/(-3/14) = 14/3`, by `norm_num`.
It is nonzero precisely because the sub-Weyl anchor has `v₀' = 0` while Yang's `σ₁` anchor has
`v₁' = 1`. Verified exactly in `Code/verify_alt_chords.py`.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6) at `k = 0`.

### Dependencies
**Depends on:** `mCoeffPAlt`, `vCoeffPAlt`, `vCoeffP`, `sigma`.
**Used by:** `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
theorem mCoeffPAlt_zero : mCoeffPAlt 0 = 14 / 3 := by
  norm_num [mCoeffPAlt, vCoeffPAlt, vCoeffP, sigma]

/-- **The alternative `k = 0` `log log|t|` chord has intercept `-7/3`.**

### Summary of Proof
`b₀' = v₀' - m₀'σ₀ = 0 - (14/3)(1/2) = -7/3`, by `norm_num`. So the chord is
`(14/3)σ - 7/3 = (14/3)(σ - 1/2)`, vanishing at `σ = 1/2` as it must, since the sub-Weyl anchor
has no `log log|t|` term there. Verified exactly in `Code/verify_alt_chords.py`.

### References
tex: Equation `\ref{eq:mkp}` (Equation 6) at `k = 0`.

### Dependencies
**Depends on:** `bCoeffPAlt`, `mCoeffPAlt`, `vCoeffPAlt`, `sigma`.
**Used by:** `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
theorem bCoeffPAlt_zero : bCoeffPAlt 0 = -(7 / 3) := by
  norm_num [bCoeffPAlt, mCoeffPAlt, vCoeffPAlt, vCoeffP, sigma]

/-- **The alternative `k = 0` constant-term chord equals
`(14/3)(5/7-σ)log 66.7 + (14/3)(σ-1/2)log 1.546`** — the constant displayed in
`BackgroundZetaBounds.interpolated_bound_1a`.

### Summary of Proof
Both sides are the affine function of `σ` carrying `1/2 ↦ log 66.7` and `5/7 ↦ log 1.546`, and
an affine function is determined by its values at two distinct points, so they agree identically.
Mechanically: unfold `mCoeffPPAlt`/`bCoeffPPAlt`, evaluate `v₀'' = log 66.7` and
`v₁'' = log 1.546`, then `ring`.

### Lean Notes
Stated as an identity in `σ` rather than as two endpoint evaluations, because that is the form
`zeta_chord_alt_zero` needs in order to rewrite case (1a)'s displayed constant directly into
chord form.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7) at `k = 0`. The right-hand side is the constant term
of case (1a) of Proposition `\ref{prop:interpolation}` (Proposition 35). The value `1.546` is
Yang's constant, `66.7` is Patel–Yang's.

### Dependencies
**Depends on:** `mCoeffPPAlt`, `bCoeffPPAlt`, `vCoeffPPAlt`, `vCoeffPP`, `sigma`.
**Used by:** `zeta_chord_alt_zero`, `zeta_piecewise_bound_alt`. -/
theorem chordPPAlt_zero (σ : ℝ) :
    mCoeffPPAlt 0 * σ + bCoeffPPAlt 0
      = 14 / 3 * (5 / 7 - σ) * Real.log 66.7 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 := by
  have hpp1 : vCoeffPPAlt 1 = Real.log 1.546 := by
    norm_num [vCoeffPPAlt, vCoeffPP]
  simp only [bCoeffPPAlt, mCoeffPPAlt, vCoeffPPAlt]
  norm_num [sigma, hpp1, vCoeffPP]
  ring

/-! ### Admissibility of the alternative family -/

/-- **`‖ζ(σ+it)‖` depends only on `|t|`.**

### Summary of Proof
Schwarz reflection. For `t ≥ 0` there is nothing to do. For `t ≤ 0`, `σ + |t|i = σ - ti` is the
complex conjugate of `σ + ti`, and `riemannZeta_conj` gives `ζ(conj s) = conj (ζ s)`, whose norm
is unchanged by `RCLike.norm_conj`.

### Lean Notes
A local copy of the private lemma of the same effect in `JensenScaleConstants`; duplicated rather
than exported because the original is `private`. The tex uses this silently whenever it writes
`log|t|` for a bound valid at `t > 0`.

### References
No tex counterpart — the tex treats the reflection as evident.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_piecewise_bound_alt`. -/
private theorem zeta_norm_abs_im_alt (σ t : ℝ) :
    ‖riemannZeta (σ + t * Complex.I)‖ = ‖riemannZeta (σ + |t| * Complex.I)‖ := by
  rcases le_total (0:ℝ) t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    have hconj : (σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I = conj ((σ:ℂ) + (t:ℂ) * Complex.I) := by
      simp
    rw [hconj, riemannZeta_conj, RCLike.norm_conj]

/-- **The changed `k = 0` chord is admissible**, on the closed interval `[1/2, 5/7]`:
`log‖ζ(σ+it)‖` is at most the alternative chords plus `3/t`.

### Summary of Proof
No new analysis is needed — the result is already in the development under another name. Case
(1a) of Proposition `\ref{prop:interpolation}` (Proposition 35) interpolates the Patel–Yang
sub-Weyl bound `|ζ(1/2+it)| ≤ 66.7|t|^{27/164}` at `σ = 1/2` against Yang's
`|ζ(5/7+it)| ≤ 1.546|t|^{1/14}log|t|` at `σ = 5/7`. Those two anchors *are* the Remark's triple
paired with `v₁`, so case (1a)'s three displayed coefficients are literally the three alternative
chords. The proof therefore just rewrites them into chord form via `mCoeffAlt_zero`,
`bCoeffAlt_zero`, `mCoeffPAlt_zero`, `bCoeffPAlt_zero` and `chordPPAlt_zero`.

### Lean Notes
Stated on the **closed** interval (rather than `σ < σ₁`) so that the mirror case `k = -1` can
invoke it at the endpoint `1-σ = 5/7`.

The logs are written bare — `Real.log t`, not `Real.log |t|` — with hypothesis `10¹² < t`,
matching the convention of `JensenScaleConstants.zeta_chord_bound_nonneg`. This matters: callers
instantiate at `t := |t|`, and had the conclusion been written with bars it would produce
`log ‖|t|‖`, a syntactically distinct atom from `log |t|` that `linarith` cannot identify with
the goal. `interpolated_bound_1a_pointwise` states its own logs with bars, so the proof bridges
with `abs_of_pos`.

### References
tex: case (1a) of Proposition `\ref{prop:interpolation}` (Proposition 35); Remark
`\ref{rem:altcoefficients}` (Remark 7). External anchors: Patel–Yang's sub-Weyl bound and
Yang's critical-strip bound.

### Dependencies
**Depends on:** `interpolated_bound_1a_pointwise`, `mCoeffAlt_zero`, `bCoeffAlt_zero`,
`mCoeffPAlt_zero`, `bCoeffPAlt_zero`, `chordPPAlt_zero`.
**Used by:** `zeta_piecewise_bound_alt`. -/
theorem zeta_chord_alt_zero {σ t : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 7)
    (ht : (10:ℝ) ^ (12:ℕ) < t) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeffAlt 0 * σ + bCoeffAlt 0) * Real.log t
          + (mCoeffPAlt 0 * σ + bCoeffPAlt 0) * Real.log (Real.log t)
          + (mCoeffPPAlt 0 * σ + bCoeffPPAlt 0) + 3 / t := by
  have key := interpolated_bound_1a_pointwise ht ⟨hσ0, hσ1⟩
  -- `interpolated_bound_1a_pointwise` states its logs as `log |t|` while taking `10¹² < t`;
  -- on that range `|t| = t`, and the bare form is what the callers need (they instantiate at
  -- `|t|`, where `log ‖|t|‖` would be a different atom from `log |t|`).
  have htpos : (0:ℝ) < t := by
    have h12 : (0:ℝ) < (10:ℝ) ^ (12:ℕ) := by positivity
    linarith
  rw [abs_of_pos htpos] at key
  rw [mCoeffAlt_zero, bCoeffAlt_zero, mCoeffPAlt_zero, bCoeffPAlt_zero, chordPPAlt_zero]
  have harith1 : -(107 / 246 : ℝ) * σ + 47 / 123 = 47 / 123 - 107 / 246 * σ := by ring
  have harith2 : (14 / 3 : ℝ) * σ + -(7 / 3) = 14 / 3 * (σ - 1 / 2) := by ring
  rw [harith1, harith2]
  linarith [key]

/-- **Remark `\ref{rem:altcoefficients}` (Remark 7)'s "also admissible" claim, formalized** — the
exact analogue of
`JensenScaleConstants.zeta_piecewise_bound` for the alternative family. For `σ_k ≤ σ < σ_{k+1}`
and `|t| > 10¹²`, `log|ζ(σ+it)|` is bounded by the alternative chords plus the same explicit
`O^*(4/|t|)` slack.

### Summary of Proof
The tex asserts admissibility in one sentence, without proof. Here it is established by four
cases on `k`, exploiting that the two families differ **only** at `k = 0`:

* `k ∉ {0,-1}` — the chords are *literally* the main-text ones (`mCoeffAlt_eq` and friends),
  so this is `zeta_piecewise_bound` verbatim. A chord at index `k` sees `v₀` only when it has
  `σ₀` as an endpoint, i.e. only for `k ∈ {0,-1}`.
* `k = 0` — `zeta_chord_alt_zero`, i.e. case (1a) of Proposition `\ref{prop:interpolation}`
  (Proposition 35), whose displayed coefficients are exactly these chords.
* `k = -1` — reflect. On `[σ_{-1}, σ₀] = [2/7, 1/2]` put `τ := 1-σ ∈ [1/2, 5/7]`, apply the
  `k = 0` case at `τ`, and convert back across the critical line with
  `BackgroundZetaBounds.zetalessthanhalf_upper` (Lemma `\ref{lem:zetalessthanhalf}`, Lemma 36).

### Lean Notes
**Mirror chord identities in closed form.** The `k = -1` branch checks
`m_{-1}σ + b_{-1} = (m₀(1-σ) + b₀) + (1/2-σ)` (and the two analogues) by evaluating the constants
directly, rather than through a general two-point argument, since the endpoints are the explicit
numbers `2/7`, `1/2`, `5/7`. All of these were re-verified in exact rational arithmetic by
`Code/verify_alt_chords.py`.

**Slack accounting**, matching `zeta_piecewise_bound` exactly: the `k = 0` branch spends `3/|t|`
(case (1a)'s own Phragmén–Lindelöf correction) and the `k = -1` branch spends that plus
`zetalessthanhalf_upper`'s reflection error `1/(2|t|²) ≤ 1/|t|`, both inside the stated `4/|t|`.
The reflection also contributes `-(1/2-σ)log 2`, which is `≤ 0` on this range and so is absorbed.

**A `linarith` subtlety in the final step.** The tactic treats `3/|t|`, `4/|t|` and `1/|t|` as
three unrelated atoms rather than multiples of `|t|⁻¹`, so the slack never cancels; the proof
factors them through one opaque `u = 1/|t|` first. The chord values are likewise abbreviated and
`clear_value`d, since otherwise degree-3 monomials such as `mCoeffAlt 0 * σ * log|t|` block the
cancellation.

**Provenance.** This rests on `interpolated_bound_1a`, whose numeric obligation
`interpolated_bound_1a_hcompact` reads the class field
`InterpolationCertificates.interpolated_bound_1a_hcompact`, certified by
`Code/verify_hcompact_boxes.sage` — the same footing as the main-text track's
`interpolated_bound_1b_hcompact`.

**The extra hypothesis `hz : ζ(1-σ+i|t|) ≠ 0`** is inherited from `zetalessthanhalf_upper` (and,
in the `k ∉ {0,-1}` branch, from `zeta_piecewise_bound`). The tex needs none, because it writes
`log|0| = -∞`; Lean's total `Real.log` gives the finite junk value `0` at a zero and the
reflection identity is then false there. Elsewhere in the development the hypothesis is
discharged a.e. at the integration site (`ae_zeta_arc_ne_zero`, `ae_zeta_vline_ne_zero`); this
lemma is a pointwise statement with no consumer, so it simply carries it. A single `hz` serves
both the `k = -1` reflection and the general branch, since both instantiate at the same `σ` and
the same `|t|`.

### References
tex: Remark `\ref{rem:altcoefficients}` (Remark 7), following Equation `\ref{eq:sigmak}`
(Equation 4), whose "also admissible" claim this discharges; Proposition
`\ref{prop:interpolation}` (Proposition 35) case (1a); Lemma `\ref{lem:zetalessthanhalf}`
(Lemma 36).

### Dependencies
**Depends on:** `zeta_chord_alt_zero`, `zeta_piecewise_bound`, `zetalessthanhalf_upper`,
`zeta_norm_abs_im_alt`, `mCoeffAlt_eq`, `bCoeffAlt_eq`, `mCoeffPAlt_eq`, `bCoeffPAlt_eq`,
`mCoeffPPAlt_eq`, `bCoeffPPAlt_eq`, `vCoeffPPAlt_eq_of_ne`, `sigma_zero_one_negone`, and the
closed-form chord evaluations `mCoeffAlt_zero`/`bCoeffAlt_zero`/`mCoeffPAlt_zero`/
`bCoeffPAlt_zero`/`chordPPAlt_zero`.
**Used by:** none — this is the admissibility statement itself, and the main development runs on
the main-text family. -/
theorem zeta_piecewise_bound_alt {k : ℤ} {σ t : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ < sigma (k + 1))
    (ht : (10:ℝ) ^ (12:ℕ) < |t|)
    (hz : riemannZeta ((1:ℂ) - σ + |t| * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (mCoeffAlt k * σ + bCoeffAlt k) * Real.log |t|
          + (mCoeffPAlt k * σ + bCoeffPAlt k) * Real.log (Real.log |t|)
          + (mCoeffPPAlt k * σ + bCoeffPPAlt k) + 4 / |t| := by
  obtain ⟨hs0, hs1, hsm1⟩ := sigma_zero_one_negone
  have habst : (0:ℝ) < |t| := by
    have : (0:ℝ) < (10:ℝ)^(12:ℕ) := by positivity
    linarith [ht]
  have ht12 : (10:ℝ) ^ (12:ℕ) < |t| := ht
  rcases eq_or_ne k 0 with rfl | hk0
  · -- `k = 0`: case (1a) of Proposition 35, directly.
    rw [zeta_norm_abs_im_alt]
    rw [hs0] at hσ
    rw [show (0:ℤ) + 1 = 1 by ring, hs1] at hσ'
    have h3 : (3:ℝ) / |t| ≤ 4 / |t| := by
      rw [div_le_div_iff_of_pos_right habst]; norm_num
    linarith [zeta_chord_alt_zero hσ (le_of_lt hσ') ht12, h3]
  rcases eq_or_ne k (-1) with rfl | hk1
  · -- `k = -1`: reflect through `σ ↦ 1-σ` onto the `k = 0` chord.
    rw [zeta_norm_abs_im_alt]
    rw [hsm1] at hσ
    rw [show (-1:ℤ) + 1 = 0 by ring, hs0] at hσ'
    -- the mirror point
    have hτ0 : (1:ℝ) / 2 ≤ 1 - σ := by linarith
    have hτ1 : (1:ℝ) - σ ≤ 5 / 7 := by linarith
    have hmain := zeta_chord_alt_zero hτ0 hτ1 ht12
    rw [show (((1 - σ : ℝ)):ℂ) = (1:ℂ) - (σ:ℂ) by push_cast; ring] at hmain
    -- reflection
    have hσ_half : σ ∈ Set.Icc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
    have ht10 : (10:ℝ) < |t| := by nlinarith [ht12]
    have hrefl := (abs_le.mp (zetalessthanhalf_upper hσ_half ht10 hz)).2
    -- `zetalessthanhalf_upper` is instantiated at `|t|`, so its `log |t/2|` appears here as the
    -- nested `log |(|t|)/2|`. That does not parse with `|…|` notation, hence the prefix `abs`.
    have hlog2 : Real.log (abs (abs t / 2)) = Real.log |t| - Real.log 2 := by
      rw [abs_of_pos (div_pos habst (by norm_num))]
      exact Real.log_div habst.ne' (by norm_num)
    have hlogpi : Real.log |Real.pi| = Real.log Real.pi := by rw [abs_of_pos Real.pi_pos]
    rw [hlog2, hlogpi] at hrefl
    -- the mirror chord identity, in closed form
    have hchord : mCoeffAlt (-1) * σ + bCoeffAlt (-1)
        = (mCoeffAlt 0 * (1-σ) + bCoeffAlt 0) + (1/2 - σ) := by
      rw [mCoeffAlt_zero, bCoeffAlt_zero]
      have hm : mCoeffAlt (-1) = -(139/246 : ℝ) := by
        norm_num [mCoeffAlt, vCoeffAlt, vCoeff, sigma]
      have hb : bCoeffAlt (-1) = (55/123 : ℝ) := by
        norm_num [bCoeffAlt, mCoeffAlt, vCoeffAlt, vCoeff, sigma]
      rw [hm, hb]; ring
    have hchordP : mCoeffPAlt (-1) * σ + bCoeffPAlt (-1)
        = (mCoeffPAlt 0 * (1-σ) + bCoeffPAlt 0) := by
      rw [mCoeffPAlt_zero, bCoeffPAlt_zero]
      have hm : mCoeffPAlt (-1) = -(14/3 : ℝ) := by
        norm_num [mCoeffPAlt, vCoeffPAlt, vCoeffP, sigma]
      have hb : bCoeffPAlt (-1) = (7/3 : ℝ) := by
        norm_num [bCoeffPAlt, mCoeffPAlt, vCoeffPAlt, vCoeffP, sigma]
      rw [hm, hb]; ring
    have hchordPP : mCoeffPPAlt (-1) * σ + bCoeffPPAlt (-1)
        = (mCoeffPPAlt 0 * (1-σ) + bCoeffPPAlt 0) + (σ - 1/2) * Real.log Real.pi := by
      rw [chordPPAlt_zero]
      have hpp0 : vCoeffPPAlt 0 = Real.log 66.7 := by norm_num [vCoeffPPAlt]
      have hppm1 : vCoeffPPAlt (-1) = Real.log 1.546 + (2/7 - 1/2 : ℝ) * Real.log Real.pi := by
        rw [vCoeffPPAlt_eq_of_ne (by norm_num)]
        norm_num [vCoeffPP, sigma]
      simp only [mCoeffPPAlt, bCoeffPPAlt, hppm1]
      norm_num [sigma, hpp0]
      ring
    rw [hchord, hchordP, hchordPP]
    -- Abbreviate the three `k = 0` chord values. Without this the goal carries degree-3
    -- monomials such as `mCoeffAlt 0 * σ * log|t|`, which `linarith` will not cancel across
    -- hypothesis and goal; as opaque atoms they are degree 2 and cancel cleanly.
    set X := mCoeffAlt 0 * (1 - σ) + bCoeffAlt 0
    set Y := mCoeffPAlt 0 * (1 - σ) + bCoeffPAlt 0
    set Z := mCoeffPPAlt 0 * (1 - σ) + bCoeffPPAlt 0
    -- `set` leaves let-bindings, which `linarith` unfolds again; discard the bodies so the
    -- three really are opaque.
    clear_value X Y Z
    have h1t : (1:ℝ)/(2*|t|^2) ≤ 1/|t| := by
      rw [div_le_div_iff₀ (by positivity) habst]; nlinarith [ht10]
    -- Substituting `hmain` into `hrefl` leaves the slack
    --   4/|t| - 3/|t| - 1/(2|t|²) + (1/2-σ)log 2  =  (1/|t| - 1/(2|t|²)) + (1/2-σ)log 2,
    -- nonnegative by `h1t` and, since `σ < 1/2`, by this product being nonnegative. The
    -- reflection's `-(1/2-σ)log 2` is what the `k = -1` chord has to absorb.
    have hlog2nn : (0:ℝ) ≤ (1/2 - σ) * Real.log 2 :=
      mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
    -- `linarith` treats `3/|t|`, `4/|t|` and `1/|t|` as three unrelated atoms rather than
    -- multiples of `|t|⁻¹`, so the slack never cancels. Factoring them through one opaque
    -- `u = 1/|t|` is what makes the final step linear.
    have e3 : (3:ℝ) / |t| = 3 * (1 / |t|) := by ring
    have e4 : (4:ℝ) / |t| = 4 * (1 / |t|) := by ring
    rw [e4]
    rw [e3] at hmain
    set u := 1 / |t|
    clear_value u
    nlinarith [hmain, hrefl, h1t, hlog2nn]
  · -- every other chord is unchanged
    rw [mCoeffAlt_eq hk0 hk1, bCoeffAlt_eq hk0 hk1, mCoeffPAlt_eq hk0 hk1,
      bCoeffPAlt_eq hk0 hk1, mCoeffPPAlt_eq hk0 hk1, bCoeffPPAlt_eq hk0 hk1]
    exact zeta_piecewise_bound hσ hσ' ht hz
