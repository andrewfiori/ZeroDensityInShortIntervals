/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Common.RealLogBounds
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.JensenScaleConstants
import ZerosInShortIntervals.Background.ExternalFacts
import ZerosInShortIntervals.Background.LogDerivZetaLaurent

/-! # Jensen bounds for circular regions (`\S \ref{sec:jensenclassic}`, Section 1)

This file formalizes Section 1 of `ZerosInShortIntervals.tex`, which bounds `N(s,α)`
using Jensen's formula.

**On the `O^*` error terms.** The source repeatedly writes bounds of the shape
`main term + O^*(bound)`, meaning the true quantity differs from the main term by at most `bound`
in absolute value. Throughout this development we formalize such a statement as the (weaker but
always valid) one-sided inequality `quantity ≤ main term + bound`.
-/

/- Everything this file assumes rather than proves enters through the six hypothesis classes
below: `LiteratureInputs` and `NumericCertificates` (`ZerosInShortIntervals/Hypotheses.lean`),
`BrentStirlingInputs` (`Background/ExternalFacts.lean`), `LaurentCertificate`
(`Background/LogDerivZetaLaurent.lean`), and `InterpolationCertificates`/`Hcompact2Certificates`
(`Background/BackgroundZetaBounds.lean`).  Lean includes an instance-implicit section variable in
every theorem in scope, so some statements carry a binder they do not use; the linter for that is
silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [NumericCertificates] [LaurentCertificate]
  [InterpolationCertificates] [Hcompact2Certificates]

/-- **The circle average `(1/2π)∫_{-π/2}^{3π/2} log|ζ(s+re^{iθ})| dθ`.**

### Summary of Proof
A definition, specialised (as in the source) to circles around points `s` on `Re s = 1`. It is
the right-hand side of Jensen's formula, Equation `\ref{eq:jensen}` (Equation 1), and the
quantity every zero-counting bound in this section is expressed against.

### Lean Notes
The integration range `(-π/2, 3π/2)` matches the source rather than Mathlib's `(0, 2π)`; the two
agree by periodicity of `θ ↦ ζ(s + re^{iθ})`, which `jensenbound` bridges.

### References
tex: throughout `\S \ref{sec:jensenclassic}` (Section 1); Equation `\ref{eq:jensen}`
(Equation 1).

### Dependencies
**Depends on:** none.
**Used by:** `circularregions1`, `circularregions1_tight`, `circularregions2`,
`intervalIntegrable_arcAvg`, `jensenbound`, `log_norm_le_jensenCircleAvg`. -/
noncomputable def jensenCircleAvg (s : ℂ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (-Real.pi / 2)..(3 * Real.pi / 2),
      Real.log ‖riemannZeta (s + r * Complex.exp (θ * Complex.I))‖

/-- **Proposition `\ref{prop:jensenbound}` (Proposition 6).** For any `s ∈ ℂ` and `r > α`,
`N(s,α) ≤ (jensenCircleAvg s r - log|ζ(s)|) / log(r/α)`.

### Summary of Proof
Each zero `ρ` with `|s-ρ| ≤ α` contributes at least
`log(r/α)` to the Jensen sum `∑_{|ρ-s|<r} log(r/|ρ-s|)`, so `log(r/α)·Ncirc s α` is at most that
sum, which by Jensen's formula (Equation `\ref{eq:jensen}`, Equation 1) equals
`jensenCircleAvg s r - log‖ζ(s)‖`.

### Lean Notes
The source's displayed formula writes `log|ζ(1+it)|` on the right; this is taken to mean
`log|ζ(s)|` for the general point `s`, matching the hypothesis "for any `s ∈ ℂ`" and the
specialisation to `s = 1+it` used everywhere the proposition is invoked.

The Lean argument is `AnalyticOnNhd.circleAverage_log_norm` from
`Mathlib.Analysis.Complex.JensenFormula` (Jensen's formula proper), combined with
`MeromorphicOn.AnalyticOnNhd.divisor_nonneg` and monotonicity of `u ↦ log(r/‖s-u‖)` in `‖s-u‖`.
It follows the same route as `AnalyticOnNhd.sum_divisor_le` in that file, which proves the
analogous statement for a *uniform bound* `M` on `‖ζ‖` in place of the exact circle average
`jensenCircleAvg`. One extra step is needed here: `jensenCircleAvg s r =
Real.circleAverage (log ‖ζ ·‖) s r`, i.e. matching the `(-π/2,3π/2)` integration range to
Mathlib's `(0,2π)` via periodicity of `θ ↦ ζ(s+r·exp(iθ))`.

Two hypotheses the source does not state are needed. `hs` excludes `ζ`'s pole from
`closedBall s r`, so that `ζ` is analytic there; `hζs` keeps `log‖ζ(s)‖` finite. Both hold at
every call site, where `s = 1+iT` with `T` larger than the radius, so the pole at `1` lies
outside the disc and `ζ(1+iT) ≠ 0`.

Stated with `≤` rather than the source's `<`, which is what the Jensen-sum comparison delivers.

### References
tex: Proposition `\ref{prop:jensenbound}` (Proposition 6); Jensen's formula, Equation
`\ref{eq:jensen}` (Equation 1).

### Dependencies
**Depends on:** `Ncirc`, `jensenCircleAvg`.
**Used by:** `circularregions1`, `circularregions1_tight`, `circularregions2`,
`log_norm_le_jensenCircleAvg`. -/
theorem jensenbound {s : ℂ} {r α : ℝ} (hrα : α < r) (hα : 0 < α)
    (hs : (1 : ℂ) ∉ Metric.closedBall s r) (hζs : riemannZeta s ≠ 0) :
    (Ncirc s α : ℝ) ≤ (jensenCircleAvg s r - Real.log ‖riemannZeta s‖) / Real.log (r / α) := by
  have hr : 0 < r := hα.trans hrα
  have hanalytic : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s |r|) := by
    rw [abs_of_pos hr]
    exact analyticOn_riemannZeta.mono (fun x hx hx1 => hs (hx1 ▸ hx))
  have hper : Function.Periodic
      (fun θ : ℝ => Real.log ‖riemannZeta (s + r * Complex.exp (θ * Complex.I))‖)
      (2 * Real.pi) := by
    intro θ
    have hexp : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by push_cast; ring
    change Real.log ‖riemannZeta (s + r * Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I))‖
        = Real.log ‖riemannZeta (s + r * Complex.exp ((θ : ℂ) * Complex.I))‖
    rw [hexp, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have havg : jensenCircleAvg s r = Real.circleAverage (fun x => Real.log ‖riemannZeta x‖) s r := by
    have h := hper.intervalIntegral_add_eq (-Real.pi / 2) 0
    have h1 : (-Real.pi / 2 : ℝ) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
    have h2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
    rw [h1, h2] at h
    change (1 / (2 * Real.pi)) *
        ∫ θ in (-Real.pi / 2)..(3 * Real.pi / 2),
          Real.log ‖riemannZeta (s + r * Complex.exp (θ * Complex.I))‖
      = (2 * Real.pi)⁻¹ •
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖riemannZeta (circleMap s r θ)‖
    simp only [circleMap, smul_eq_mul, one_div, ← h]
  have hjensen := hanalytic.circleAverage_log_norm hr.ne' hζs
  have hkey : jensenCircleAvg s r - Real.log ‖riemannZeta s‖
      = ∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u
          * Real.log (r * ‖s - u‖⁻¹) := by
    rw [havg, hjensen]; ring
  rw [hkey]
  have hαr : α ≤ r := hrα.le
  have hlogpos : 0 < Real.log (r / α) := Real.log_pos ((one_lt_div hα).mpr hrα)
  rw [le_div_iff₀ hlogpos]
  have hα_le_r : Metric.closedBall s α ⊆ Metric.closedBall s |r| := by
    rw [abs_of_pos hr]; exact Metric.closedBall_subset_closedBall hαr
  have hanalytic_α : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s α) :=
    hanalytic.mono hα_le_r
  have hNcirc_eq : (Ncirc s α : ℝ)
      = ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u : ℝ) :=
    map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor riemannZeta (Metric.closedBall s α)).finiteSupport
        (isCompact_closedBall s α))
  rw [hNcirc_eq]
  have hfin_α : (fun x => (MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) x : ℝ)
      * Real.log (r / α)).support.Finite :=
    ((MeromorphicOn.divisor riemannZeta (Metric.closedBall s α)).finiteSupport
      (isCompact_closedBall s α)).subset (fun x hx ↦ by
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h; apply hx; rw [h]; simp)
  have hfin_r : (fun x => (MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) x : ℝ)
      * Real.log (r * ‖s - x‖⁻¹)).support.Finite :=
    ((MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|)).finiteSupport
      (isCompact_closedBall s |r|)).subset (fun x hx ↦ by
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h; apply hx; rw [h]; simp)
  calc (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u : ℝ))
        * Real.log (r / α)
      = ∑ᶠ u, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u : ℝ)
          * Real.log (r / α)) := finsum_mul _ _
    _ ≤ ∑ᶠ u, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u : ℝ)
          * Real.log (r * ‖s - u‖⁻¹)) := by
        refine finsum_le_finsum' hfin_α hfin_r fun u ↦ ?_
        by_cases hu_r : u ∈ Metric.closedBall s |r|
        · by_cases hus : u = s
          · have hzero_α : MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u = 0 := by
              rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic_α
                  (hus ▸ Metric.mem_closedBall_self hα.le),
                hus, (hanalytic_α s (Metric.mem_closedBall_self hα.le)).analyticOrderAt_eq_zero.mpr
                  hζs]
              simp
            have hzero_r : MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u = 0 := by
              rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hu_r,
                hus, (hanalytic s (hus ▸ hu_r)).analyticOrderAt_eq_zero.mpr hζs]
              simp
            rw [hzero_α, hzero_r]; simp
          · by_cases hu_α : u ∈ Metric.closedBall s α
            · have hdiv_eq : MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u
                  = MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u := by
                rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic_α hu_α,
                  MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hu_r]
              rw [hdiv_eq]
              gcongr
              · have hnn : (0 : ℤ) ≤
                    MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u := by
                  simpa using MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic u
                exact Int.cast_nonneg hnn
              · have hne : ‖s - u‖ ≠ 0 := by
                  simp only [ne_eq, norm_eq_zero, sub_eq_zero]
                  exact fun h => hus h.symm
                have hle : ‖s - u‖ ≤ α := by
                  simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu_α
                have hpos : 0 < ‖s - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
                rw [div_eq_mul_inv]
                refine mul_le_mul_of_nonneg_left ?_ hr.le
                simpa using one_div_le_one_div_of_le hpos hle
            · have hzero : MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u = 0 :=
                Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu_α
              rw [hzero]
              simp only [Int.cast_zero, zero_mul]
              apply mul_nonneg
              · have hnn : (0 : ℤ) ≤
                    MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u := by
                  simpa using MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic u
                exact Int.cast_nonneg hnn
              · have hne : ‖s - u‖ ≠ 0 := by
                  simp only [ne_eq, norm_eq_zero, sub_eq_zero]; exact fun h => hus h.symm
                have hpos : 0 < ‖s - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
                have hle : ‖s - u‖ ≤ r := by
                  simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr, norm_sub_rev]
                    using hu_r
                apply Real.log_nonneg
                rw [div_eq_mul_inv] at *
                exact (le_div_iff₀ hpos).mpr (by linarith)
        · have hu_α : u ∉ Metric.closedBall s α := fun h => hu_r (hα_le_r h)
          have hzero_α : MeromorphicOn.divisor riemannZeta (Metric.closedBall s α) u = 0 :=
            Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu_α
          have hzero_r : MeromorphicOn.divisor riemannZeta (Metric.closedBall s |r|) u = 0 :=
            Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu_r
          rw [hzero_α, hzero_r]; simp

/-- **`Ncirc s α ≥ 0`.**

### Summary of Proof
`Ncirc` counts zeros with multiplicity via `MeromorphicOn.divisor`, and on a ball where `ζ` is
analytic — i.e. one avoiding its pole at `1` — that divisor is nonnegative, so the sum is.

### References
No tex counterpart — the source treats a zero count as evidently nonnegative.

### Dependencies
**Depends on:** `Ncirc`.
**Used by:** `log_norm_le_jensenCircleAvg`. -/
theorem Ncirc_nonneg {s : ℂ} {α : ℝ} (hs : (1:ℂ) ∉ Metric.closedBall s α) : 0 ≤ Ncirc s α :=
  finsum_nonneg fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (analyticOn_riemannZeta.mono (fun _ hx hx1 => hs (hx1 ▸ hx))) u

/-- **Jensen's inequality for `ζ`**: the circle average of `log‖ζ‖` dominates the value at the
centre.

### Summary of Proof
Immediate from `jensenbound`, which bounds `log(r/α)·Ncirc s α` by
`jensenCircleAvg s r - log‖ζ(s)‖`, together with `Ncirc_nonneg`: since the left side is
nonnegative, so is the right.

### References
tex: Proposition `\ref{prop:jensenbound}` (Proposition 6), of which this is the degenerate
zero-count-discarded case; Equation `\ref{eq:jensen}` (Equation 1).

### Dependencies
**Depends on:** `Ncirc`, `Ncirc_nonneg`, `jensenCircleAvg`, `jensenbound`.
**Used by:** `intervalIntegrable_arcAvg`. -/
theorem log_norm_le_jensenCircleAvg {s : ℂ} {r : ℝ} (hr : 0 < r)
    (hs : (1 : ℂ) ∉ Metric.closedBall s r) (hζs : riemannZeta s ≠ 0) :
    Real.log ‖riemannZeta s‖ ≤ jensenCircleAvg s r := by
  have hα : (0:ℝ) < r / 2 := by linarith
  have hrα : r / 2 < r := by linarith
  have hs' : (1:ℂ) ∉ Metric.closedBall s (r/2) := fun h =>
    hs (Metric.closedBall_subset_closedBall (by linarith) h)
  have hN := jensenbound hrα hα hs hζs
  have hN0 : (0:ℝ) ≤ (Ncirc s (r/2) : ℝ) := by exact_mod_cast Ncirc_nonneg hs'
  have hlog : 0 < Real.log (r / (r/2)) := by
    rw [show r / (r/2) = 2 by field_simp]
    exact Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog] at hN
  nlinarith [mul_nonneg hN0 hlog.le]

/-- **The circle point in `σ + it` coordinates**: `1 + iT + re^{iθ}` has `σ = 1 + r cos θ` and
ordinate `t = T + r sin θ`.

### Summary of Proof
Expanding `e^{iθ} = cos θ + i sin θ` and separating real and imaginary parts.

### Lean Notes
A small but pervasive bridge: every pointwise bound on the circle is stated in terms of `ζ` at a
complex argument, while the interpolation bounds it draws on are stated in `σ` and `t`. This is
what converts between them.

### References
No tex counterpart — the source moves between the two descriptions silently.

### Dependencies
**Depends on:** none.
**Used by:** `arc_pointwise_bound`, `arc_pointwise_bound_tight`, `integraloutside_bound`,
`prop_Richert`. -/
theorem circle_pt (T r θ : ℝ) :
    (1 + (T:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
      = ((1 + r * Real.cos θ : ℝ) : ℂ) + ((T + r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I]; push_cast; ring

/-! ### Towards Proposition `\ref{prop:jensen-easy}` (Proposition 8): the arc majorant

The source's proof runs: on `θ ∈ (θ_{k+1,r}+π/2, θ_{k,r}+π/2)` the piecewise-linear `F_{1+it,r}(θ)`
bounds `log|ζ(1+it+re^{iθ})|`; integrate term by term and regroup by `k` to get `c₁,r`, `c₂,r`,
`c₃,r`. The two halves of that are separated here:

* **the pointwise bound** (`arc_pointwise_bound`) — at `θ` the circle point is `σ + it'`
  with `σ = 1 + r cos θ` and `t' = t + r sin θ`, and `JensenScaleConstants.zeta_piecewise_bound`
  applies at the chord index `JensenScaleConstants.chordIdx σ`. Writing the majorant's three
  coefficients as honest functions of `σ` (`chordA`, `chordA'`, `chordA''`) is what makes the
  next step an integral of a function rather than of a case split;
* **the integral evaluation** — `∫_{π/2}^{3π/2} chordA (1 + r cos θ) dθ = 2·c₁ r` and its two
  companions. Under `φ = θ - π/2` and symmetry this is `2∫_0^{π/2} A(1 - r sin φ)dφ`, and the
  closed form of `c₁,r` is exactly that integral decomposed over the partition
  `[0,π/2] = [θ_{K,r},π/2] ∪ ⋃_{j≥0}[θ_{K+j+1,r}, θ_{K+j,r}]`
  (`JensenScaleConstants.chord_boundary_eq_integral`, `chord_term_eq_integral`). The source's
  regrouping "by `k`" is therefore a *countable* decomposition here; `θ_{K+j,r} → 0` as `j → ∞`
  is what makes the pieces exhaust the quarter, and `integral_le_tsum_arc`/`tsum_eq_integral_arc`
  carry out the termwise integration. `c1_eq_integral` below is the resulting equality.

Each half of the development comes in a crude and a tight version, differing only in which
pointwise input from `JensenScaleConstants` they use.

**The crude track's error is `O^*(3/t)`, larger than the source's printed
`5/(6(t-1)) + 1/(t-1)² + 579/(8(t-1)²log(t-1))`** (about `0.83/t` for large `t`). The printed
constant pays for `log|t+r|` versus `log|t|` plus the genuinely quadratic slack of Proposition
`\ref{prop:interpolation}` (Proposition 35). `zeta_piecewise_bound`, the crude input used by
`jensen_easy`, instead carries an `O^*(4/|t|)` slack (from `interpolated_bound_*`'s `3/T` and
`zetalessthanhalf_upper`'s `1/(2t²)`), and integrating that over an arc of length `π` and
dividing by `2π` already contributes `≈ 2/t`. The total is `arcErr r t / 2 < 2.4/t`, so `3/t` is
safe (`arcErr_le_six_div`). `circularregions1` and `rectangularjensen` use the matching enlarged
constants (`3/(T log(r/α))` and `(6h+6α̂_r)/((T-h-α̂_r)D)`). The tight track — `arcErr_tight`,
`jensen_easy_tight` — reproduces the printed error term instead.

**The crude track assumes `r < 1` and `t > 10¹² + 1`, against the source's `0 < r < 1` and
`t > 13`**: `r < 1` is what makes the chord index `JensenScaleConstants.chordIdx` (and `Kidx`)
well defined, while the far stronger ordinate threshold is what `zeta_piecewise_bound` needs at
the circle point's ordinate `t + r sin θ`. The tight track needs only `t > 13`. -/

/-- **`chordA σ`: the piecewise-linear majorant of `log|ζ(σ+it)|`'s `log|t|` coefficient**, as
an honest function of `σ`.

### Summary of Proof
A definition: `mCoeff k * σ + bCoeff k` at `k = chordIdx σ`, i.e. the chord of Equation
`\ref{eq:mk}` (Equation 5) belonging to whichever interval `[σ_k, σ_{k+1}]` contains `σ`.

### Lean Notes
**Chord convention — read this before comparing anything here to the scripts in `Code/`.**
`mCoeff` and `bCoeff` follow Equation `\ref{eq:mk}` (Equation 5) of the tex *exactly*:
`m_k = (v_k - v_{k+1})/(σ_k - σ_{k+1})` (note the negative denominator) and
`b_k = v_k - m_k σ_k`. Consequently the chord `mCoeff k * σ + bCoeff k` is evaluated at **`σ`
itself**, not at `1 - σ`, and it interpolates `(σ_k, v_k) → (σ_{k+1}, v_{k+1})`. `chordA` is that
chord. By contrast `chordW` below is the same function re-parametrised by the *distance from 1*,
`x = 1 - σ` (`chordW x = chordA (1 - x)`), because `r` and `α` are naturally distances from 1.
Both are correct; confusing them is not, and reading the `x = 1-σ` convention into the tex's
Equation `\ref{eq:mk}` (Equation 5) produces a spurious factor-13 discrepancy in `A_{1,α,r}`.
The scripts in `Code/` use the tex convention documented here.

### References
tex: Equation `\ref{eq:mk}` (Equation 5); the majorant display `F_{1+it,r}(θ)` in the proof of
Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `bCoeff`, `chordIdx`, `mCoeff`.
**Used by:** `arc_pointwise_bound`, `arc_pointwise_bound_sin`, `arc_pointwise_bound_sin_tight`,
`arc_pointwise_bound_tight`, `chordA_antitone`, `chordA_star`, `chordW`, `chordW_arc_eq`,
`chordW_eq`, `chordW_le`, `chordW_nonneg`. -/
noncomputable def chordA (σ : ℝ) : ℝ := mCoeff (chordIdx σ) * σ + bCoeff (chordIdx σ)

/-- **`chordA' σ`: the `log log|t|` coefficient chord**, as a function of `σ`.

### Summary of Proof
A definition: `mCoeffP k * σ + bCoeffP k` at `k = chordIdx σ`, the middle member of the
`chordA`/`chordA'`/`chordA''` family. Since `vCoeffP` is constant, this chord is identically `1`
(`mCoeffP_eq_zero`, `bCoeffP_eq_one`).

### References
tex: Equation `\ref{eq:mkp}` (Equation 6); the majorant display in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `bCoeffP`, `chordIdx`, `mCoeffP`.
**Used by:** `arc_pointwise_bound`, `arc_pointwise_bound_sin`,
`arc_pointwise_bound_sin_tight`, `arc_pointwise_bound_tight`. -/
noncomputable def chordA' (σ : ℝ) : ℝ := mCoeffP (chordIdx σ) * σ + bCoeffP (chordIdx σ)

/-- **The constant-term chord as a function of `σ`**: `A''(σ) = m_k''σ + b_k''` at
`k = chordIdx σ`.

### Summary of Proof
A definition, the third of the `chordA`/`chordA'`/`chordA''` family: the constant-term chord of
Equation `\ref{eq:mkpp}` (Equation 7), evaluated on whichever chord interval contains `σ`.

### References
tex: Equation `\ref{eq:mkpp}` (Equation 7); the majorant display in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8), where it is the constant term of `F_{1+it,r}`.

### Dependencies
**Depends on:** `bCoeffPP`, `chordIdx`, `mCoeffPP`.
**Used by:** `arc_pointwise_bound`, `arc_pointwise_bound_sin`, `arc_pointwise_bound_sin_tight`,
`arc_pointwise_bound_tight`. -/
noncomputable def chordA'' (σ : ℝ) : ℝ := mCoeffPP (chordIdx σ) * σ + bCoeffPP (chordIdx σ)

/-! ### `chordA` as a monotone function, and its star-shapedness

Two structural facts about the piecewise-linear coefficient `A(σ) = m_kσ + b_k` are needed for
`c1_scaling` (and they are what the source's "by inspection" is really appealing to).

* **`A` is antitone on `(0,1)`** (`chordA_antitone`). Within one chord this is `m_k < 0`; across
  chords it follows from the endpoint bounds `v_{k+1} ≤ A ≤ v_k` (`chord_mem_Icc`) and
  `vCoeff_strictAnti`, so no continuity-at-the-knots argument is needed.
* **`A` is star-shaped about `σ = 1`** (`chordA_star`): `A(σ)/(1-σ)` is antitone. Within one chord
  this is exactly `m_k + b_k < 0`, since
  `A(σ)(1-τ) - A(τ)(1-σ) = (m_k+b_k)(σ-τ)`; across chords it chains through the two knot values
  using `vRatio_strictAnti`.

`chordW` repackages `A` as a *globally* monotone function of `x = 1-σ`, clamped to `0` for `x ≤ 0`
and to `2/3` for `x ≥ 1`. That makes it measurable (`Monotone.measurable`) and bounded, hence
`fun φ ↦ chordW (r sin φ)` is interval integrable on every interval — which is all the arc
decomposition needs, and it avoids proving `A` continuous. -/

/-- **`chordA` is antitone on `(0,1)`.**

### Summary of Proof
Within a single chord interval this is `mCoeff_neg` — the slope is negative. Across intervals,
`chordIdx_le_of_le` says the index is monotone in `σ`, and `chord_mem_Icc` places each chord's
values between its two endpoint `v`'s, which decrease with the index; chaining the two gives
antitonicity globally on `(0,1)`.

### Lean Notes
This is the fact that makes `chordW` monotone after the reflection `x = 1-σ`, and hence
interval integrable.

### References
No tex counterpart as a numbered claim — the source's `F_{1+it,r}` is monotone by construction.

### Dependencies
**Depends on:** `chordA`, `chordIdx`, `chordIdx_le_of_le`, `chordIdx_spec`, `chord_mem_Icc`,
`mCoeff_neg`, `vCoeff`.
**Used by:** `chordW_mono`. -/
theorem chordA_antitone {σ τ : ℝ} (h0 : 0 < σ) (hle : σ ≤ τ) (h1 : τ < 1) :
    chordA τ ≤ chordA σ := by
  have h0' : 0 < τ := lt_of_lt_of_le h0 hle
  have h1' : σ < 1 := lt_of_le_of_lt hle h1
  obtain ⟨ha1, ha2⟩ := chordIdx_spec h0 h1'
  obtain ⟨hb1, hb2⟩ := chordIdx_spec h0' h1
  rcases eq_or_lt_of_le (chordIdx_le_of_le h0 hle h1) with heq | hlt
  · rw [chordA, chordA, ← heq]
    nlinarith [mCoeff_neg (chordIdx σ)]
  · have hA := (chord_mem_Icc ha1 ha2.le).1
    have hB := (chord_mem_Icc hb1 hb2.le).2
    have hv : vCoeff (chordIdx τ) ≤ vCoeff (chordIdx σ + 1) :=
      vCoeff_strictAnti.antitone (by omega)
    rw [chordA, chordA]
    linarith

/-- **`chordA` is star-shaped about `σ = 1`**: `A(σ)/(1-σ)` is antitone on `(0,1)`, stated
multiplicatively.

### Summary of Proof
Within one chord interval the claim reduces to `m_k + b_k < 0` (`mCoeff_add_bCoeff_neg`), the
source's own inequality. Across chords it chains the two knot values through
`vRatio_strictAnti`, which says the vertex ratios `v_k/(1-σ_k)` decrease.

### Lean Notes
Stated multiplicatively to avoid dividing by `1-σ`, whose positivity would otherwise have to be
carried through every step.

### References
tex: the inequality `m_k+b_k ≤ 0` in the proof of Proposition `\ref{prop:Cscaling}`
(Proposition 17).

### Dependencies
**Depends on:** `bCoeff`, `chordA`, `chordIdx`, `chordIdx_le_of_le`, `chordIdx_spec`, `mCoeff`,
`mCoeff_add_bCoeff_neg`, `sigma`, `sigma_lt_one`, `sigma_lt_succ`, `vCoeff`, `vRatio`.
**Used by:** `chordW_star`. -/
theorem chordA_star {σ τ : ℝ} (h0 : 0 < σ) (hle : σ ≤ τ) (h1 : τ < 1) :
    chordA τ * (1 - σ) ≤ chordA σ * (1 - τ) := by
  have h0' : 0 < τ := lt_of_lt_of_le h0 hle
  have h1' : σ < 1 := lt_of_le_of_lt hle h1
  obtain ⟨ha1, ha2⟩ := chordIdx_spec h0 h1'
  obtain ⟨hb1, hb2⟩ := chordIdx_spec h0' h1
  rcases eq_or_lt_of_le (chordIdx_le_of_le h0 hle h1) with heq | hlt
  · rw [chordA, chordA, ← heq]
    nlinarith [mCoeff_add_bCoeff_neg (chordIdx σ)]
  · set k := chordIdx σ with hk
    set k' := chordIdx τ with hk'
    have hp : (0:ℝ) < 1 - sigma (k+1) := by linarith [sigma_lt_one (k+1)]
    have hq : (0:ℝ) < 1 - sigma k' := by linarith [sigma_lt_one k']
    have hu : (0:ℝ) < 1 - σ := by linarith
    have hw : (0:ℝ) < 1 - τ := by linarith
    -- the chord `k'` carries `τ` back to its left knot `σ_{k'}`
    have hA : chordA τ * (1 - sigma k') ≤ vCoeff k' * (1 - τ) := by
      have hval : mCoeff k' * sigma k' + bCoeff k' = vCoeff k' := by rw [bCoeff]; ring
      rw [chordA, ← hval]
      nlinarith [mCoeff_add_bCoeff_neg k', hb1]
    -- the chord `k` carries `σ` forward to its right knot `σ_{k+1}`
    have hB : vCoeff (k+1) * (1 - σ) ≤ chordA σ * (1 - sigma (k+1)) := by
      have hval : mCoeff k * sigma (k+1) + bCoeff k = vCoeff (k+1) := by
        have hlt' := sigma_lt_succ k
        have hne : sigma k - sigma (k+1) ≠ 0 := by intro hc; linarith
        rw [bCoeff, mCoeff]; field_simp; ring
      rw [chordA, ← hval]
      nlinarith [mCoeff_add_bCoeff_neg k, ha2.le]
    -- and the two knots compare by `vRatio_strictAnti`
    have hC : vCoeff k' * (1 - sigma (k+1)) ≤ vCoeff (k+1) * (1 - sigma k') := by
      have h := vRatio_strictAnti.antitone (show k + 1 ≤ k' by omega)
      rw [vRatio, vRatio, div_le_div_iff₀ hq hp] at h
      linarith
    refine le_of_mul_le_mul_right ?_ (mul_pos hq hp)
    nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hu.le hp.le),
      mul_le_mul_of_nonneg_right hC (mul_nonneg hw.le hu.le),
      mul_le_mul_of_nonneg_right hB (mul_nonneg hq.le hw.le)]

/-- **`chordW`: the chord as a globally monotone, bounded function of `x = 1 - σ`**, clamped
outside `(0,1)`.

### Summary of Proof
A definition: `0` for `x ≤ 0`, `chordA (1-x)` for `0 < x < 1`, and `2/3` for `x ≥ 1`.

### Lean Notes
The reparametrisation by the *distance from 1* is natural because `r` and `α` are themselves
distances from `1`. The clamping is what makes the function globally monotone
(`chordW_mono`) and bounded (`chordW_nonneg`, `chordW_le`), hence interval integrable on every
interval with no side conditions — which the unclamped `chordA` is not.

### References
No tex counterpart — the source works with the affine chord directly and never needs a clamped
global version.

### Dependencies
**Depends on:** `chordA`.
**Used by:** `c1_eq_integral`, `chordW_arc_eq`, `chordW_eq`, `chordW_le`, `chordW_mono`,
`chordW_nonneg`, `chordW_star`, `intervalIntegrable_chordW`. -/
noncomputable def chordW (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x < 1 then chordA (1 - x) else 2/3

/-- **`chordW` agrees with `chordA` on the open unit interval**: `chordW x = chordA (1-x)` for
`0 < x < 1`.

### Summary of Proof
Unfold `chordW` and discharge its two guard conditions using `0 < x` and `x < 1`.

### Lean Notes
`chordW` is the reparametrisation of the chord by `x = 1-σ`, the distance from the line
`Re s = 1`, clamped to constants outside `(0,1)` so that it is globally monotone and bounded.
This lemma is what lets the clamped version be exchanged for the honest one wherever the argument
is known to lie in range.

### References
No tex counterpart — the clamping is an artifact of wanting a globally defined monotone function.

### Dependencies
**Depends on:** `chordA`, `chordW`.
**Used by:** `chordW_arc_eq`, `chordW_mono`, `chordW_star`. -/
theorem chordW_eq {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : chordW x = chordA (1 - x) := by
  rw [chordW, ite_eq_right (not_le.mpr h0), ite_eq_left h1]

/-- **`chordW` is nonnegative everywhere**: `0 ≤ chordW x`.

### Summary of Proof
Three cases from the definition. Outside `(0,1)` the clamped values are `0` and the value at the
right end, both nonnegative. Inside, `chordW x = chordA (1-x)` and `chordIdx_spec` places `1-x`
in its own chord interval, where `chord_vCoeff_nonneg` gives the sign.

### References
No tex counterpart — the source uses the nonnegativity of the `log|t|` coefficient silently.

### Dependencies
**Depends on:** `chordA`, `chordIdx_spec`, `chordW`, `chord_vCoeff_nonneg`.
**Used by:** `chordW_mono`, `intervalIntegrable_chordW`. -/
theorem chordW_nonneg (x : ℝ) : 0 ≤ chordW x := by
  rw [chordW]
  split_ifs with h1 h2
  · exact le_refl 0
  · have hx0 : (0:ℝ) < 1 - x := by linarith
    have hx1 : (1:ℝ) - x < 1 := by linarith [not_le.mp h1]
    obtain ⟨hs1, hs2⟩ := chordIdx_spec hx0 hx1
    rw [chordA]
    exact chord_vCoeff_nonneg hs1 hs2.le
  · norm_num

/-- **`chordW` is bounded by `2/3`**: `chordW x ≤ 2/3`.

### Summary of Proof
The companion of `chordW_nonneg`, by the same three-case split: the clamped values are within
range, and inside `(0,1)` the bound is `chord_vCoeff_le`, which caps every chord by `2/3`.

### Lean Notes
Together with `chordW_nonneg` this pins `chordW` to `[0, 2/3]` globally, which is what makes it
interval integrable without any further hypotheses.

### References
No tex counterpart.

### Dependencies
**Depends on:** `chordA`, `chordIdx_spec`, `chordW`, `chord_vCoeff_le`.
**Used by:** `chordW_mono`, `intervalIntegrable_chordW`. -/
theorem chordW_le (x : ℝ) : chordW x ≤ 2/3 := by
  rw [chordW]
  split_ifs with h1 h2
  · norm_num
  · have hx0 : (0:ℝ) < 1 - x := by linarith
    have hx1 : (1:ℝ) - x < 1 := by linarith [not_le.mp h1]
    obtain ⟨hs1, hs2⟩ := chordIdx_spec hx0 hx1
    rw [chordA]
    exact chord_vCoeff_le hs1 hs2.le
  · exact le_refl _

/-- **`chordW` is monotone** (nondecreasing) on all of `ℝ`.

### Summary of Proof
Case on where `x` and `y` fall relative to `(0,1)`. Below `0` the function is constantly `0` and
`chordW_nonneg` covers the step up; above `1` it is constant. Inside, `chordW x = chordA (1-x)`
and the reflection `x ↦ 1-x` turns `chordA`'s antitonicity (`chordA_antitone`) into monotonicity
in `x`.

### Lean Notes
Global monotonicity — rather than monotonicity on `(0,1)` — is exactly what the clamping buys,
and it is what makes `chordW` interval integrable and usable in the arc comparison without side
conditions.

### References
No tex counterpart.

### Dependencies
**Depends on:** `chordA_antitone`, `chordW`, `chordW_nonneg`.
**Used by:** `intervalIntegrable_chordW`. -/
theorem chordW_mono : Monotone chordW := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · rw [chordW, ite_eq_left hx]; exact chordW_nonneg y
  · rcases lt_or_ge y 1 with hy | hy
    · rw [chordW_eq hx (lt_of_le_of_lt hxy hy), chordW_eq (lt_of_lt_of_le hx hxy) hy]
      exact chordA_antitone (by linarith) (by linarith) (by linarith)
    · rw [show chordW y = 2/3 by
        rw [chordW, ite_eq_right (by linarith), ite_eq_right (by linarith)]]
      exact chordW_le x

/-- **Star-shapedness in the `x = 1-σ` variable**: `W(λx) ≤ λ·W(x)` for `0 < λ ≤ 1`,
`0 ≤ x < 1`.

### Summary of Proof
The reflection `x = 1-σ` turns `chordA_star`'s statement — that `A(σ)/(1-σ)` is antitone — into
exactly this scaling inequality, once `chordW_eq` identifies `chordW` with `chordA (1-·)` on the
range where both are honest.

### Lean Notes
This is the form the radius-scaling argument needs: it is what lets `c_{1,r}` be compared across
different radii `r` in `c1_scaling`.

### References
No tex counterpart as a numbered claim — the source uses the monotonicity of `c_{1,r}` in `r`
when comparing radii.

### Dependencies
**Depends on:** `chordA_star`, `chordW`, `chordW_eq`.
**Used by:** `c1_scaling`. -/
theorem chordW_star {x lam : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    chordW (lam * x) ≤ lam * chordW x := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, mul_zero, chordW, ite_eq_left (le_refl 0), mul_zero]
  · have hlx0 : 0 < lam * x := mul_pos hlam0 hx0
    have hlx1 : lam * x < 1 := by nlinarith
    rw [chordW_eq hlx0 hlx1, chordW_eq hx0 hx1]
    have h := chordA_star (σ := 1 - x) (τ := 1 - lam * x) (by linarith) (by nlinarith)
      (by linarith)
    simp only [sub_sub_cancel] at h
    have hxpos : (0:ℝ) < x := hx0
    nlinarith [h]

/-- **`φ ↦ chordW (r sin φ)` is interval integrable on every interval.**

### Summary of Proof
Measurability comes from `chordW_mono.measurable` composed with the continuous `φ ↦ r sin φ`;
boundedness from `chordW_nonneg` and `chordW_le`, which pin the values to `[0, 2/3]`. A bounded
measurable function is interval integrable on any bounded interval.

### Lean Notes
"On *every* interval", with no side conditions, is precisely what the clamping in `chordW` buys —
the unclamped `chordA` would need `σ ∈ (0,1)` threaded through each use.

### References
No tex counterpart — an integrability side condition the source does not mention.

### Dependencies
**Depends on:** `chordW`, `chordW_le`, `chordW_nonneg`.
**Used by:** `c1_eq_integral`, `c1_scaling`. -/
theorem intervalIntegrable_chordW (r a b : ℝ) :
    IntervalIntegrable (fun φ : ℝ => chordW (r * Real.sin φ)) MeasureTheory.volume a b := by
  have hmeas : Measurable (fun φ : ℝ => chordW (r * Real.sin φ)) :=
    chordW_mono.measurable.comp (by fun_prop)
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound
    (by rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    hmeas.aestronglyMeasurable (2/3) ?_
  filter_upwards with φ
  rw [Real.norm_eq_abs, abs_of_nonneg (chordW_nonneg _)]
  exact chordW_le _

/-- **On a chord window, `chordW (r sin φ)` is the affine function `m_k(1-r sin φ) + b_k`.**

### Summary of Proof
The window hypothesis is stated on `sin φ`, exactly as `sin_window_of_mem_chord` delivers it. It
places `1 - r sin φ` strictly inside `(0,1)`, so `chordW_eq` replaces the clamped `chordW` by
`chordA`, and `chordIdx_eq` identifies the chord index as `k`; unfolding `chordA` then gives the
affine expression.

### References
No tex counterpart — the source works with the affine expression directly and never introduces a
clamped version.

### Dependencies
**Depends on:** `bCoeff`, `chordA`, `chordIdx_eq`, `chordW`, `chordW_eq`, `mCoeff`, `sigma`,
`sigma_lt_one`.
**Used by:** `c1_eq_integral`. -/
theorem chordW_arc_eq {k : ℤ} {r φ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs1 : (1 - sigma (k+1))/r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k)/r) :
    chordW (r * Real.sin φ) = mCoeff k * (1 - r * Real.sin φ) + bCoeff k := by
  have hpos : 0 < (1 - sigma (k+1))/r := div_pos (by linarith [sigma_lt_one (k+1)]) hr0
  have hsin : 0 < Real.sin φ := lt_trans hpos hs1
  have hx0 : 0 < r * Real.sin φ := mul_pos hr0 hsin
  have hx1 : r * Real.sin φ < 1 := by nlinarith [Real.sin_le_one φ]
  rw [chordW_eq hx0 hx1, chordA]
  have hA : sigma k ≤ 1 - r * Real.sin φ := by
    have h : r * Real.sin φ ≤ r * ((1 - sigma k)/r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  have hB : 1 - r * Real.sin φ < sigma (k+1) := by
    have h : r * ((1 - sigma (k+1))/r) < r * Real.sin φ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  rw [show 1 - (r * Real.sin φ) = 1 - r * Real.sin φ from rfl, chordIdx_eq hA hB]

/-- **Pointwise bound on the circle**, for `cos θ < 0`: `log‖ζ(1+it+re^{iθ})‖` is at most the
three chords evaluated at `σ = 1 + r cos θ`, against `log` and `log log` of the ordinate
`t + r sin θ`, plus the `4/|·|` slack.

### Summary of Proof
`circle_pt` puts the point in `σ + it` coordinates, `σ = 1 + r cos θ` and ordinate
`t + r sin θ`. Since `cos θ < 0` and `r < 1`, that `σ` lies in `(0,1)`, so `chordIdx_spec` pins
the chord interval containing it and `JensenScaleConstants.zeta_piecewise_bound` applies at that
index. The three chord values are then repackaged as `chordA`, `chordA'`, `chordA''` at `σ`.

### Lean Notes
The hypothesis is `cos θ < 0` rather than a range of `θ`, which keeps the statement free of
branch bookkeeping; the caller supplies it from `θ ∈ (π/2, 3π/2)`.

The bound is still against `log(t + r sin θ)`, the *true* ordinate. Replacing that by `log t` is
a separate step, costed by `arcErr` in `log_arc_window`/`loglog_arc_window`.

**The hypothesis `hz`** is `zeta_piecewise_bound`'s reflection hypothesis, transported to the
circle: the mirror of the circle point `σ + i(t + r sin θ)` across `Re s = 1/2` is
`-r cos θ + i(t + r sin θ)`, and the bound needs `ζ` non-zero there. The tex needs no such
hypothesis, working with `log|0| = -∞`; Lean's total `Real.log` gives the finite junk value `0`
at a zero, where the reflection identity is then false. The hypothesis is propagated through
`arc_pointwise_bound_sin`/`arc_pointwise_le_maj_sin` and discharged almost everywhere at the
integration sites (`jensen_easy_lower_quarter`, `jensen_easy_upper_quarter`) via
`ae_zeta_arc_ne_zero`; it never reaches a main theorem.

### References
tex: the majorant display `F_{1+it,r}(θ)` in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8), resting on Proposition `\ref{prop:interpolation}` (Proposition 35).

### Dependencies
**Depends on:** `chordA`, `chordA'`, `chordA''`, `chordIdx`, `chordIdx_spec`, `circle_pt`,
`zeta_piecewise_bound`.
**Used by:** `arc_pointwise_bound_sin`. -/
theorem arc_pointwise_bound {r t θ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hcos : Real.cos θ < 0)
    (hz : riemannZeta (((-(r * Real.cos θ) : ℝ) : ℂ)
        + ((t + r * Real.sin θ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖
      ≤ chordA (1 + r * Real.cos θ) * Real.log (t + r * Real.sin θ)
        + chordA' (1 + r * Real.cos θ) * Real.log (Real.log (t + r * Real.sin θ))
        + chordA'' (1 + r * Real.cos θ)
        + 4 / (t + r * Real.sin θ) := by
  set σ : ℝ := 1 + r * Real.cos θ with hσ_def
  have hcos1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hσ0 : 0 < σ := by rw [hσ_def]; nlinarith
  have hσ1 : σ < 1 := by rw [hσ_def]; nlinarith
  obtain ⟨h1, h2⟩ := chordIdx_spec hσ0 hσ1
  have hsin : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
  have ht' : (10:ℝ)^(12:ℕ) < t + r * Real.sin θ := by nlinarith [Real.sin_le_one θ]
  have habs : |t + r * Real.sin θ| = t + r * Real.sin θ := by
    apply abs_of_pos
    have : (0:ℝ) < (10:ℝ)^(12:ℕ) := by positivity
    linarith
  have hkey := zeta_piecewise_bound (k := chordIdx σ) (σ := σ)
    (t := t + r * Real.sin θ) h1 h2 (by rw [habs]; exact ht')
    (by
      rw [habs, hσ_def,
        show (1:ℂ) - ((1 + r * Real.cos θ : ℝ) : ℂ) = ((-(r * Real.cos θ) : ℝ) : ℂ) by
          push_cast; ring]
      exact hz)
  rw [habs] at hkey
  rw [circle_pt]
  exact hkey

/-- **`θ ↦ log‖ζ(s + re^{iθ})‖` is interval integrable on every interval.**

### Summary of Proof
The composite `θ ↦ ζ(s + re^{iθ})` is real-meromorphic — `Definitions.meromorphicAt_riemannZeta`
composed with an entire function of `θ` — and `log‖·‖` of a real-meromorphic function is always
interval integrable, by `MeromorphicOn.intervalIntegrable_log_norm`. In particular the
logarithmic singularities at zeros of `ζ` on the circle are integrable.

### Lean Notes
Used to split `jensenCircleAvg`'s `(-π/2, 3π/2)` integral at `±π/2` into the "inside the strip"
and "outside the strip" halves — a step the source performs without comment, but which in Lean
needs integrability on each piece before the split is legitimate.

### References
No tex counterpart — an integrability side condition the source does not state.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `circle_full_split`, `circularregions1`, `circularregions1_tight`,
`circularregions2`, `integraloutside_bound`, `intervalIntegrable_arcAvg`, `jensen_easy`,
`jensen_easy_tight`. -/
theorem intervalIntegrable_log_zeta_circle (s : ℂ) (r a b : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.log ‖riemannZeta (s + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
      MeasureTheory.volume a b := by
  have hmero : MeromorphicOn
      (fun θ : ℝ => riemannZeta (s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)))
      (Set.uIcc a b) := by
    intro u _
    have hinner : AnalyticAt ℝ
        (fun θ : ℝ => s + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) u := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul analyticAt_const
      have h1 : AnalyticAt ℝ (fun θ : ℝ => (θ:ℂ) * Complex.I) u := by
        apply AnalyticAt.mul _ analyticAt_const
        exact Complex.ofRealCLM.analyticAt u
      exact AnalyticAt.comp (g := Complex.exp)
        (analyticAt_cexp (z := ((u:ℂ) * Complex.I))).restrictScalars h1
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **`φ ↦ log‖ζ(s + re^{i(φ+π/2)})‖` is interval integrable** — the shifted-arc form.

### Summary of Proof
The same real-meromorphy argument as `intervalIntegrable_log_zeta_circle`: the shift `φ ↦ φ+π/2`
is entire, so the composite remains real-meromorphic and
`MeromorphicOn.intervalIntegrable_log_norm` applies.

### Lean Notes
The shifted parametrisation is what the outside-strip half uses, since there the natural variable
is `φ = θ - π/2`, measuring the angle from the top of the circle.

### References
No tex counterpart.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `FcrZeta_shift_intervalIntegrable`, `arc_piece_bound`, `arc_piece_bound_tight`,
`jensen_easy_lower_quarter`, `jensen_easy_lower_quarter_tight`. -/
theorem intervalIntegrable_log_zeta_circle_shift (s : ℂ) (r c a b : ℝ) :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.log ‖riemannZeta (s + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I))‖)
      MeasureTheory.volume a b := by
  have hmero : MeromorphicOn
      (fun φ : ℝ => riemannZeta (s + (r:ℂ) * Complex.exp (((φ + c : ℝ):ℂ) * Complex.I)))
      (Set.uIcc a b) := by
    intro u _
    have hinner : AnalyticAt ℝ
        (fun φ : ℝ => s + (r:ℂ) * Complex.exp (((φ + c : ℝ):ℂ) * Complex.I)) u := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul analyticAt_const
      have h1 : AnalyticAt ℝ (fun φ : ℝ => ((φ + c : ℝ):ℂ) * Complex.I) u := by
        apply AnalyticAt.mul _ analyticAt_const
        have : (fun φ : ℝ => ((φ + c : ℝ):ℂ)) = fun φ : ℝ => (φ:ℂ) + (c:ℂ) := by
          funext φ; push_cast; ring
        rw [this]
        exact AnalyticAt.add (Complex.ofRealCLM.analyticAt u) analyticAt_const
      exact AnalyticAt.comp (g := Complex.exp)
        (analyticAt_cexp (z := (((u + c : ℝ):ℂ) * Complex.I))).restrictScalars h1
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **`φ ↦ log‖ζ(s + re^{i(c-φ)})‖` is interval integrable** — the reflected shifted-arc form.

### Summary of Proof
As `intervalIntegrable_log_zeta_circle_shift`: the reflection `φ ↦ c - φ` is entire, so the
composite stays real-meromorphic.

### Lean Notes
Needed for the upper quarter `θ ∈ [π, 3π/2]`, parametrised as `θ = 3π/2 - φ`. That the two
quarters give the same bound rests on the majorant depending on `φ` only through `sin φ`
(`arcMaj_pi_sub`) — the *integrand* is not symmetric about `θ = π`, since conjugation moves the
centre from `1+it` to `1-it`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `jensen_easy_upper_quarter`, `jensen_easy_upper_quarter_tight`. -/
theorem intervalIntegrable_log_zeta_circle_reflect (s : ℂ) (r c a b : ℝ) :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.log ‖riemannZeta (s + (r : ℂ) * Complex.exp (((c - φ : ℝ) : ℂ) * Complex.I))‖)
      MeasureTheory.volume a b := by
  have hmero : MeromorphicOn
      (fun φ : ℝ => riemannZeta (s + (r:ℂ) * Complex.exp (((c - φ : ℝ):ℂ) * Complex.I)))
      (Set.uIcc a b) := by
    intro u _
    have hinner : AnalyticAt ℝ
        (fun φ : ℝ => s + (r:ℂ) * Complex.exp (((c - φ : ℝ):ℂ) * Complex.I)) u := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul analyticAt_const
      have h1 : AnalyticAt ℝ (fun φ : ℝ => ((c - φ : ℝ):ℂ) * Complex.I) u := by
        apply AnalyticAt.mul _ analyticAt_const
        have : (fun φ : ℝ => ((c - φ : ℝ):ℂ)) = fun φ : ℝ => (c:ℂ) - (φ:ℂ) := by
          funext φ; push_cast; ring
        rw [this]
        exact AnalyticAt.sub analyticAt_const (Complex.ofRealCLM.analyticAt u)
      exact AnalyticAt.comp (g := Complex.exp)
        (analyticAt_cexp (z := (((c - u : ℝ):ℂ) * Complex.I))).restrictScalars h1
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **Window bound on the arc, for `log`**: replacing `log(t + r cos φ)` by `log t` costs at
most `r/(t-r)`.

### Summary of Proof
The ordinate of the circle point at `θ = φ + π/2` is `t + r cos φ`, which lies within `r` of `t`,
so `abs_log_sub_log_le'` applies with `d = r`.

### Lean Notes
This is one of the two contributions to `arcErr`. It is genuinely `O(1/t)` and is *not* improved
by the tight interpolation bounds — the window conversion is unrelated to Proposition
`\ref{prop:interpolation}` (Proposition 35), which is why `arcErr_tight` still carries an
`O(1/t)` piece.

### References
tex: the passage from `log|t+r|` to `log|t|` in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `abs_log_sub_log_le'`.
**Used by:** `arc_pointwise_le_maj_sin`, `arc_pointwise_le_maj_sin_tight`,
`loglog_arc_window`. -/
theorem log_arc_window {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1) (ht : 2 < t) :
    |Real.log (t + r * Real.cos φ) - Real.log t| ≤ r / (t - r) := by
  refine abs_log_sub_log_le' hr0.le (by linarith) ⟨?_, ?_⟩
  · nlinarith [Real.neg_one_le_cos φ]
  · nlinarith [Real.cos_le_one φ]

/-- **Window bound on the arc, for `log log`**: replacing `log log(t + r cos φ)` by
`log log t` costs at most `(r/(t-r))/(log t - r/(t-r))`.

### Summary of Proof
One more application of `abs_log_sub_log_le'`, now at `y = log t` with `d = r/(t-r)` — the
displacement supplied by `log_arc_window`.

### Lean Notes
The hypothesis `r/(t-r) < log t` in the callers is exactly what keeps this second application's
denominator positive; it is why `jensen_easy` carries that condition.

### References
tex: the passage from `log log|t+r|` to `log log|t|` in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `abs_log_sub_log_le'`, `log_arc_window`.
**Used by:** `arc_pointwise_le_maj_sin`, `arc_pointwise_le_maj_sin_tight`. -/
theorem loglog_arc_window {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1) (ht : 2 < t)
    (hlog : r / (t - r) < Real.log t) :
    |Real.log (Real.log (t + r * Real.cos φ)) - Real.log (Real.log t)|
      ≤ (r / (t - r)) / (Real.log t - r / (t - r)) := by
  have hd0 : (0:ℝ) ≤ r / (t - r) := le_of_lt (div_pos hr0 (by linarith))
  refine abs_log_sub_log_le' hd0 hlog ?_
  have h := log_arc_window (r := r) (t := t) (φ := φ) hr0 hr ht
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **On `φ ∈ (θ_{k+1,r}, θ_{k,r}]`, `sin φ` lies in the window `((1-σ_{k+1})/r, (1-σ_k)/r]`**
that pins the chord index to `k`.

### Summary of Proof
Both endpoints lie in `[0, π/2]` (`theta_nonneg`, `theta_le_pi_div_two`), where `sin` is
monotone, so the `φ`-interval maps onto the interval between `sin θ_{k+1,r}` and `sin θ_{k,r}`.
Those two values are `(1-σ_{k+1})/r` and `(1-σ_k)/r` by `sin_theta_eq`, and `sigma_lt_succ`
orders them.

### Lean Notes
This is the bridge between the two ways of indexing an arc piece — by angle, which is how the
integrals are set up, and by `sin φ`, which is how the chord index is pinned. Keeping the
pointwise bounds stated in `sin φ` is what makes the mirror arc free.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8) and the chord-piece decomposition in the proof of
Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `sigma`, `sigma_lt_succ`, `sin_theta_eq`, `theta`, `theta_le_pi_div_two`,
`theta_nonneg`.
**Used by:** `arc_piece_bound_gen`, `arc_piece_bound_gen_tight`, `arc_pointwise_bound_at`,
`arc_pointwise_le_maj`, `arc_pointwise_le_maj_tight`, `c1_eq_integral`. -/
theorem sin_window_of_mem_chord {k : ℤ} {r φ : ℝ} (hr0 : 0 < r) (hk : 1 - sigma k ≤ r)
    (hφ1 : theta (k+1) r < φ) (hφ2 : φ ≤ theta k r) :
    (1 - sigma (k+1)) / r < Real.sin φ ∧ Real.sin φ ≤ (1 - sigma k) / r := by
  have hpi := Real.pi_pos
  have hk1 : 1 - sigma (k+1) ≤ r := by linarith [sigma_lt_succ k]
  have hlo : (0:ℝ) ≤ theta (k+1) r := theta_nonneg hr0
  have hhi : theta k r ≤ Real.pi / 2 := theta_le_pi_div_two k r
  have hs2 : Real.sin φ ≤ Real.sin (theta k r) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hhi hφ2
  have hs1 : Real.sin (theta (k+1) r) < Real.sin φ :=
    Real.strictMonoOn_sin ⟨by linarith, by linarith [theta_le_pi_div_two (k+1) r]⟩
      ⟨by linarith, by linarith⟩ hφ1
  rw [sin_theta_eq hr0 hk] at hs2
  rw [sin_theta_eq hr0 hk1] at hs1
  exact ⟨hs1, hs2⟩

/-- **The pointwise bound on one chord piece, in sine form.**

### Summary of Proof
The circle point at `θ = φ + π/2` has `σ = 1 - r sin φ`, so the chord index is pinned to `k`
exactly when `σ_k ≤ 1 - r sin φ < σ_{k+1}`, i.e. `(1-σ_{k+1})/r < sin φ ≤ (1-σ_k)/r` — a
condition on `sin φ` alone. Under it, `chordIdx_eq` identifies the index and
`arc_pointwise_bound` supplies the estimate.

### Lean Notes
Stating the hypothesis on `sin φ` rather than as `φ ∈ (θ_{k+1,r}, θ_{k,r}]` earns two things.
The *mirror* arc `φ ∈ [π - θ_{k,r}, π - θ_{k+1,r})` becomes free, since `sin(π-ψ) = sin ψ`. And
it frees the boundary chord `k = K-1`, where `1 - σ_{K-1} > r` makes `θ_{K-1,r}` meaningless.

Carries `arc_pointwise_bound`'s hypothesis `hz`, rewritten at `θ = φ + π/2`: the mirror of the
arc point across `Re s = 1/2` is `r sin φ + i(t + r cos φ)`. See `arc_pointwise_bound` for why
Lean needs it and where it is discharged.

### References
tex: the majorant display `F_{1+it,r}(θ)` in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8), whose own parametrisation is by `sin(θ-π/2)`.

### Dependencies
**Depends on:** `arc_pointwise_bound`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `chordA`, `chordA'`,
`chordA''`, `chordIdx`, `chordIdx_eq`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`,
`sigma_lt_one`.
**Used by:** `arc_pointwise_bound_at`, `arc_pointwise_le_maj_sin`. -/
theorem arc_pointwise_bound_sin {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ (mCoeff k * (1 - r * Real.sin φ) + bCoeff k) * Real.log (t + r * Real.cos φ)
        + (mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k)
            * Real.log (Real.log (t + r * Real.cos φ))
        + (mCoeffPP k * (1 - r * Real.sin φ) + bCoeffPP k)
        + 4 / (t + r * Real.cos φ) := by
  -- the trig shift
  have hcosθ : Real.cos (φ + Real.pi/2) = -Real.sin φ := by
    rw [Real.cos_add_pi_div_two]
  have hsinθ : Real.sin (φ + Real.pi/2) = Real.cos φ := by
    rw [Real.sin_add_pi_div_two]
  -- `sin φ > 0`, since `σ_{k+1} < 1`
  have hpos : 0 < (1 - sigma (k+1)) / r := div_pos (by linarith [sigma_lt_one (k+1)]) hr0
  have hsinpos : 0 < Real.sin φ := lt_trans hpos hs1
  -- the two chord inequalities
  have hA : sigma k ≤ 1 - r * Real.sin φ := by
    have h : r * Real.sin φ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h
    linarith
  have hB : 1 - r * Real.sin φ < sigma (k+1) := by
    have h : r * ((1 - sigma (k+1)) / r) < r * Real.sin φ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h
    linarith
  -- apply the generic bound and pin the index
  have hbound := arc_pointwise_bound (r := r) (t := t) (θ := φ + Real.pi/2) hr0 hr ht
    (by rw [hcosθ]; linarith)
    (by
      rw [hcosθ, hsinθ, show (-(r * -Real.sin φ) : ℝ) = r * Real.sin φ by ring]
      exact hz)
  rw [hcosθ, hsinθ] at hbound
  have hidx : chordIdx (1 + r * -Real.sin φ) = k := by
    refine chordIdx_eq ?_ ?_ <;> · rw [show 1 + r * -Real.sin φ = 1 - r * Real.sin φ by ring]
                                   first | exact hA | exact hB
  simp only [chordA, chordA', chordA'', hidx] at hbound
  rw [show 1 + r * -Real.sin φ = 1 - r * Real.sin φ by ring] at hbound
  exact hbound

/-- **The angle form of `arc_pointwise_bound_sin`**, hypothesis stated as
`φ ∈ (θ_{k+1,r}, θ_{k,r}]`.

### Summary of Proof
`sin_window_of_mem_chord` converts the angle hypothesis into the `sin φ` window, using
`sin_theta_eq` and strict monotonicity of `sin` on `[-π/2, π/2]`.

### Lean Notes
Carries `arc_pointwise_bound_sin`'s non-vanishing hypothesis `hz` unchanged; see
`arc_pointwise_bound` for why Lean needs it and where it is discharged.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8); the majorant display in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `arc_pointwise_bound_sin`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`,
`mCoeffPP`, `sigma`, `sin_window_of_mem_chord`, `theta`.
**Used by:** none — the chain runs through `arc_pointwise_le_maj` instead, which folds in the
window conversion. Kept as the direct angle-form statement. -/
theorem arc_pointwise_bound_at {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hk : 1 - sigma k ≤ r)
    (hφ1 : theta (k+1) r < φ) (hφ2 : φ ≤ theta k r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ (mCoeff k * (1 - r * Real.sin φ) + bCoeff k) * Real.log (t + r * Real.cos φ)
        + (mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k)
            * Real.log (Real.log (t + r * Real.cos φ))
        + (mCoeffPP k * (1 - r * Real.sin φ) + bCoeffPP k)
        + 4 / (t + r * Real.cos φ) := by
  obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk hφ1 hφ2
  exact arc_pointwise_bound_sin hr0 hr ht hs1 hs2 hz

/-- **The per-unit-length arc error `arcErr r t`** of replacing the circle point's own ordinate
`t + r cos φ` by `t`.

### Summary of Proof
A definition, summing three contributions: the `log` window (`log_arc_window`) scaled by the
chord bound `2/3`; the `log log` window (`loglog_arc_window`), whose chord is identically `1`; and
the `4/|t'|` slack that `JensenScaleConstants.zeta_piecewise_bound` carries.

### Lean Notes
Only the third summand comes from the interpolation bound; the first two are pure window
conversion. That is why `arcErr_tight` — which improves only the third — still carries an `O(1/t)`
term rather than being uniformly `O(1/t²)`.

### References
tex: the `O^*` term of Proposition `\ref{prop:jensen-easy}` (Proposition 8). This is the
per-unit-length form of the *crude* track's error, which is larger than the printed one;
`arcErr_tight` is the one that matches it.

### Dependencies
**Depends on:** none.
**Used by:** `arcErr_le_six_div`, `arcMaj`, `arc_boundary_bound_gen`,
`arc_majorant_boundary_integral`, `arc_majorant_integral`, `arc_piece_bound`,
`arc_piece_bound_gen`, `arc_pointwise_le_maj_sin`, `half_arc_bound`, `jensen_easy`,
`jensen_easy_lower_quarter`, `jensen_easy_upper_quarter`. -/
noncomputable def arcErr (r t : ℝ) : ℝ :=
  (2/3) * (r / (t - r)) + (r / (t - r)) / (Real.log t - r / (t - r)) + 4 / (t - r)

/-- **The piecewise-affine majorant `arcMaj k r t φ`** on the chord piece indexed `k`.

### Summary of Proof
A definition: the three chords of index `k`, evaluated at `σ = 1 - r sin φ`, against `log t`,
`log log t` and `1`, plus `arcErr r t`. It is the source's `F_{1+it,r}` with `t` in place of the
circle point's own ordinate `t + r cos φ`, the substitution being paid for by `arcErr`.

### Lean Notes
Depending on `φ` only through `sin φ` is deliberate — see `arcMaj_pi_sub` — and is what makes the
upper quarter of the circle free.

### References
tex: the majorant display `F_{1+it,r}(θ)` in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `arcErr`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`, `mCoeffPP`.
**Used by:** `arcMaj_pi_sub`, `arc_boundary_bound_gen`, `arc_majorant_boundary_integral`,
`arc_majorant_integral`, `arc_piece_bound_gen`, `arc_pointwise_le_maj`,
`arc_pointwise_le_maj_sin`, `continuous_arcMaj`, `half_arc_bound`. -/
noncomputable def arcMaj (k : ℤ) (r t : ℝ) (φ : ℝ) : ℝ :=
  (mCoeff k * (1 - r * Real.sin φ) + bCoeff k) * Real.log t
    + (mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k) * Real.log (Real.log t)
    + (mCoeffPP k * (1 - r * Real.sin φ) + bCoeffPP k)
    + arcErr r t

/-- **`arcMaj k r t` is continuous** in the angle.

### Summary of Proof
Unfold the definition and apply `fun_prop`: the majorant is a fixed affine combination of `sin`,
`log` and constants, all continuous.

### Lean Notes
Continuity is what makes the majorant interval integrable on each chord piece, which the
comparison arguments need before they can integrate the pointwise bound.

### References
No tex counterpart — the source integrates its majorant without remark.

### Dependencies
**Depends on:** `arcMaj`.
**Used by:** `arc_boundary_bound_gen`, `arc_piece_bound`, `arc_piece_bound_gen`. -/
theorem continuous_arcMaj (k : ℤ) (r t : ℝ) : Continuous (arcMaj k r t) := by
  unfold arcMaj; fun_prop

/-- **The majorant is symmetric about `φ = π/2`**: `arcMaj k r t (π - φ) = arcMaj k r t φ`.

### Summary of Proof
Immediate from the definition, since `arcMaj` depends on `φ` only through `sin φ` and
`sin(π - φ) = sin φ`.

### Lean Notes
This is what makes the upper quarter `θ ∈ [π, 3π/2]` free once the lower quarter is done. Note
the *integrand* is **not** symmetric about `θ = π` — conjugation `ζ(conj s) = conj ζ(s)` moves
the centre from `1+it` to `1-it`. Only the majorant is symmetric, which is all the argument uses.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8), which treats the two
quarters as giving the same bound.

### Dependencies
**Depends on:** `arcMaj`.
**Used by:** `jensen_easy_upper_quarter`. -/
theorem arcMaj_pi_sub (k : ℤ) (r t φ : ℝ) : arcMaj k r t (Real.pi - φ) = arcMaj k r t φ := by
  unfold arcMaj; rw [Real.sin_pi_sub]

/-- **`∫ arcMaj` over a chord piece equals the three closed-form summands plus the error.**

### Summary of Proof
Apply `chord_term_eq_integral` to each of the three chord families in turn — that lemma is
exactly the closed form of `∫ (m(1 - r sin φ) + b) dφ` — and integrate the constant `arcErr` over
the piece.

### Lean Notes
This is the step that turns the pointwise majorant into the `k`-th summand of `c₁`, `c₂`, `c₃`,
so that the whole quarter-circle integral can be compared against those series.

### References
tex: the `k`-th summand of the `c_{i,r}` displays after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `arcErr`, `arcMaj`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `chord_term_eq_integral`,
`mCoeff`, `mCoeffP`, `mCoeffPP`, `theta`.
**Used by:** `arc_piece_bound`, `arc_piece_bound_gen`. -/
theorem arc_majorant_integral (k : ℤ) (r t : ℝ) :
    (∫ φ in (theta (k+1) r)..(theta k r), arcMaj k r t φ)
      = ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr r t := by
  have e1 := chord_term_eq_integral (k := k) (mCoeff k) (bCoeff k) r
  have e2 := chord_term_eq_integral (k := k) (mCoeffP k) (bCoeffP k) r
  have e3 := chord_term_eq_integral (k := k) (mCoeffPP k) (bCoeffPP k) r
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume
      (theta (k+1) r) (theta k r) := fun g hg => hg.intervalIntegrable _ _
  unfold arcMaj
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) intervalIntegrable_const,
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, ← e1, ← e2, ← e3]
  simp only [smul_eq_mul]

/-- **The pointwise majorant bound, in sine form**: `log‖ζ‖ ≤ arcMaj k r t φ` on the chord
window.

### Summary of Proof
Start from `arc_pointwise_bound_sin`, which bounds `log‖ζ‖` by the chords against the *true*
ordinate `t + r cos φ`. Replace `log(t + r cos φ)` by `log t` using `log_arc_window`, and
`log log(t + r cos φ)` by `log log t` using `loglog_arc_window`. Each replacement is paid for by
multiplying the window bound by the corresponding chord coefficient, bounded via
`chord_vCoeff_nonneg`/`chord_vCoeff_le` (`0 ≤ A_k ≤ 2/3`) and `bCoeffP_eq_one` (the `log log`
chord is identically `1`). Those products are exactly the summands of `arcErr`.

### Lean Notes
Carries `arc_pointwise_bound_sin`'s hypothesis `hz` — `ζ` non-zero at the mirror point
`r sin φ + i(t + r cos φ)` — which the tex does not need (it writes `log|0| = -∞`). This is the
live carrier: `jensen_easy_lower_quarter`/`jensen_easy_upper_quarter` discharge it almost
everywhere with `ae_zeta_arc_ne_zero`, so no non-vanishing hypothesis reaches `jensen_easy` or
anything above it.

### References
tex: the majorant display and the passage from `log|t+r|` to `log|t|` in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `arcErr`, `arcMaj`, `arc_pointwise_bound_sin`, `bCoeff`, `bCoeffP`,
`bCoeffP_eq_one`, `chord_vCoeff_le`, `chord_vCoeff_nonneg`, `log_arc_window`,
`loglog_arc_window`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `bCoeffPP`, `sigma`.
**Used by:** `arc_pointwise_le_maj`, `jensen_easy_lower_quarter`,
`jensen_easy_upper_quarter`. -/
theorem arc_pointwise_le_maj_sin {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t)
    (hlog : r / (t - r) < Real.log t)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ arcMaj k r t φ := by
  have hbig : (0:ℝ) < (10:ℝ)^(12:ℕ) := by positivity
  have ht2 : (2:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  have hd1 : (0:ℝ) ≤ r / (t - r) := le_of_lt (div_pos hr0 htr)
  have hpt := arc_pointwise_bound_sin hr0 hr ht hs1 hs2 hz
  -- the chord value at `φ`
  set A : ℝ := mCoeff k * (1 - r * Real.sin φ) + bCoeff k with hA_def
  have hpos : 0 < (1 - sigma (k+1)) / r := div_pos (by linarith [sigma_lt_one (k+1)]) hr0
  have hsinpos : 0 < Real.sin φ := lt_trans hpos hs1
  have hA1 : sigma k ≤ 1 - r * Real.sin φ := by
    have h : r * Real.sin φ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  have hA2 : 1 - r * Real.sin φ ≤ sigma (k+1) := by
    have h : r * ((1 - sigma (k+1)) / r) ≤ r * Real.sin φ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  have hA0 : 0 ≤ A := chord_vCoeff_nonneg hA1 hA2
  have hAle : A ≤ 2/3 := chord_vCoeff_le hA1 hA2
  -- the three replacements
  have hw1 := log_arc_window (r := r) (t := t) (φ := φ) hr0 hr ht2
  have hw2 := loglog_arc_window (r := r) (t := t) (φ := φ) hr0 hr ht2 hlog
  rw [abs_le] at hw1 hw2
  have hcos1 : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
  have h4 : 4 / (t + r * Real.cos φ) ≤ 4 / (t - r) := by
    apply div_le_div_of_nonneg_left (by norm_num) htr
    nlinarith
  have hAx : A * (Real.log (t + r * Real.cos φ) - Real.log t) ≤ (2/3) * (r / (t - r)) := by
    rcases le_or_gt (Real.log (t + r * Real.cos φ) - Real.log t) 0 with hx | hx
    · nlinarith [hA0, hd1]
    · nlinarith [hAle, hw1.2, hx]
  have hPeq : mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k = 1 := by
    rw [mCoeffP_eq_zero, bCoeffP_eq_one]; ring
  rw [arcMaj, arcErr, ← hA_def, hPeq]
  rw [hPeq] at hpt
  nlinarith [hpt, hw2.2, h4, hAx]

/-- **The angle form of `arc_pointwise_le_maj_sin`**, hypothesis stated as
`φ ∈ (θ_{k+1,r}, θ_{k,r}]`.

### Summary of Proof
`sin_window_of_mem_chord` converts the angle hypothesis into the `sin φ` window that
`arc_pointwise_le_maj_sin` expects.

### Lean Notes
Both forms are kept because the angle form is what the per-piece integrals consume, while the
sine form is what makes the mirror arc and the boundary chord free.

Carries `arc_pointwise_le_maj_sin`'s non-vanishing hypothesis `hz` unchanged; see
`arc_pointwise_bound` for why Lean needs it and where it is discharged.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8); the majorant display in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `arcMaj`, `arc_pointwise_le_maj_sin`, `sigma`, `sin_window_of_mem_chord`,
`theta`.
**Used by:** `arc_piece_bound`. -/
theorem arc_pointwise_le_maj {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hk : 1 - sigma k ≤ r)
    (hlog : r / (t - r) < Real.log t)
    (hφ1 : theta (k+1) r < φ) (hφ2 : φ ≤ theta k r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ arcMaj k r t φ := by
  obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk hφ1 hφ2
  exact arc_pointwise_le_maj_sin hr0 hr ht hlog hs1 hs2 hz

/-- **The bound on one chord piece, integrated.**

### Summary of Proof
Integrate the pointwise bound `arc_pointwise_le_maj` over the piece, using
`integral_mono_ae_restrict` to step over the single left endpoint — where `σ = σ_{k+1}` exactly
and the chord index jumps, so the pointwise bound is stated on a half-open interval. Then
`arc_majorant_integral` evaluates the majorant's integral in closed form.

### Lean Notes
The almost-everywhere version of monotonicity is what handles the endpoint; a single point is
null, so the bound failing there is harmless. This is bookkeeping the source has no need of.

The same a.e. step absorbs a second null set: `arc_pointwise_le_maj`'s non-vanishing hypothesis
`hz` fails exactly where `ζ` vanishes on the reflected circle, which `ae_zeta_arc_ne_zero` shows
is null. So `hz` is discharged here and does not appear in this statement.

### References
tex: the chord-piece decomposition in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr`, `arc_majorant_integral`,
`arc_pointwise_le_maj`, `bCoeff`, `bCoeffP`,
`bCoeffPP`, `continuous_arcMaj`, `intervalIntegrable_log_zeta_circle_shift`, `mCoeff`,
`mCoeffP`, `mCoeffPP`, `sigma`, `theta`, `arcMaj`.
**Used by:** none — superseded by the generic `arc_piece_bound_gen`, which the mirror arc can
also reuse. Kept as the direct, unabstracted form. -/
theorem arc_piece_bound {k : ℤ} {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hk : 1 - sigma k ≤ r)
    (hlog : r / (t - r) < Real.log t) :
    (∫ φ in (theta (k+1) r)..(theta k r),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖)
      ≤ ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr r t := by
  rw [← arc_majorant_integral k r t]
  refine intervalIntegral.integral_mono_ae_restrict (theta_antitone_succ hr0)
    (intervalIntegrable_log_zeta_circle_shift ((1:ℂ) + (t:ℂ) * Complex.I) r (Real.pi/2) _ _)
    ((continuous_arcMaj k r t).intervalIntegrable _ _) ?_
  have hfin : MeasureTheory.volume ({theta (k+1) r} : Set ℝ) = 0 :=
    MeasureTheory.measure_singleton _
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hfin,
    ae_zeta_arc_ne_zero (b := r) (c := r) hr0.ne' hr0.ne' t] with φ hφ hne hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  exact arc_pointwise_le_maj hr0 hr ht hk hlog (lt_of_le_of_ne hmem.1 (Ne.symm hφ)) hmem.2 hne

/-! ### Assembling `Proposition \ref{prop:jensen-easy}`

The pieces above bound `log|ζ|` on a single chord piece. What remains is bookkeeping, done in three
steps.

* `arc_majorant_boundary_integral` — the companion of `arc_majorant_integral` for the boundary
  piece `[θ_{K,r}, π/2]`, whose chord index is `K-1` (see the `c_{i,r}` docstring in
  `JensenScaleConstants`).
* `half_arc_bound` — the whole quarter `[0, π/2]`, for *any* `F` dominated by the sine-form
  majorant. Splitting at `θ_{K,r}` gives the boundary piece plus the countable family, and
  `integral_le_tsum_arc` turns the latter into a `tsum` that is exactly the `tsum` in the
  definition of `c_{i,r}`. The `O^*(·)` slack telescopes: `Σ_j (θ_{K+j,r} - θ_{K+j+1,r}) = θ_{K,r}`
  (`hasSum_theta_diff`) plus the boundary length `π/2 - θ_{K,r}` is `π/2`.
* the two quarters — `[π/2, π]` via `θ = φ + π/2`, and `[π, 3π/2]` via `θ = 3π/2 - φ`. Both are
  the same `F`-shaped integral over `[0, π/2]`, because the majorant depends on `φ` only through
  `sin φ` (`arcMaj_pi_sub`). This is the "symmetry about `φ = π/2`" the source's constants encode;
  note that the *integrand* is not symmetric (conjugating the circle point moves the centre from
  `1+it` to `1-it`), only the majorant is. -/

/-- **`∫ arcMaj (K-1)` over the boundary piece `[θ_{K,r}, π/2]` equals the three boundary
summands of `c₁`, `c₂`, `c₃` plus the error.**

### Summary of Proof
As `arc_majorant_integral`, but using `chord_boundary_eq_integral` — the closed form on
`[θ_{K,r}, π/2]`, where the `cos(π/2) = 0` endpoint removes the second cosine.

### References
tex: the leading (boundary) term of each `c_{i,r}` display after Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `arcErr`, `arcMaj`, `bCoeff`, `bCoeffP`, `bCoeffPP`,
`chord_boundary_eq_integral`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `theta`.
**Used by:** `arc_boundary_bound_gen`. -/
theorem arc_majorant_boundary_integral (K : ℤ) (r t : ℝ) :
    (∫ φ in (theta K r)..(Real.pi/2), arcMaj (K-1) r t φ)
      = ((mCoeff (K-1) + bCoeff (K-1)) * (Real.pi/2 - theta K r)
            - mCoeff (K-1) * r * Real.cos (theta K r)) * Real.log t
        + ((mCoeffP (K-1) + bCoeffP (K-1)) * (Real.pi/2 - theta K r)
            - mCoeffP (K-1) * r * Real.cos (theta K r)) * Real.log (Real.log t)
        + ((mCoeffPP (K-1) + bCoeffPP (K-1)) * (Real.pi/2 - theta K r)
            - mCoeffPP (K-1) * r * Real.cos (theta K r))
        + (Real.pi/2 - theta K r) * arcErr r t := by
  have e1 := chord_boundary_eq_integral (mCoeff (K-1)) (bCoeff (K-1)) r K
  have e2 := chord_boundary_eq_integral (mCoeffP (K-1)) (bCoeffP (K-1)) r K
  have e3 := chord_boundary_eq_integral (mCoeffPP (K-1)) (bCoeffPP (K-1)) r K
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume
      (theta K r) (Real.pi/2) := fun g hg => hg.intervalIntegrable _ _
  unfold arcMaj
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) intervalIntegrable_const,
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, ← e1, ← e2, ← e3]
  simp only [smul_eq_mul]

/-- **The generic per-piece bound**, for any `F` dominated by the sine-form majorant.

### Summary of Proof
As `arc_piece_bound`, but abstracted over the integrand: any `F` satisfying the sine-form
pointwise bound is integrated against `arcMaj` via `integral_mono_ae_restrict`, then
`arc_majorant_integral` gives the closed form.

### Lean Notes
The abstraction is what lets the **mirror** arc reuse the same lemma. Since the pointwise
hypothesis is stated on `sin φ`, and `sin(π-φ) = sin φ`, the reflected integrand satisfies it
too — so the upper quarter needs no separate argument.

**`hle` is an *almost-everywhere* domination hypothesis**, `∀ m, ∀ᵐ φ, window → F φ ≤ arcMaj …`,
not a pointwise one. Callers instantiate `F` with `log‖ζ‖` on the arc, whose pointwise majorant
(`arc_pointwise_le_maj_sin`) needs `ζ` non-zero at the mirror point; that fails on the null set
of zeros of `ζ` on the reflected circle. Since `F` is only ever integrated here, assuming the
domination a.e. costs nothing and keeps the non-vanishing hypothesis out of every statement
above this one.

### References
tex: the chord-piece decomposition in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `arcErr`, `arcMaj`, `arc_majorant_integral`, `bCoeff`, `bCoeffP`, `bCoeffPP`,
`continuous_arcMaj`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`, `sin_window_of_mem_chord`,
`theta`, `theta_antitone_succ`.
**Used by:** `half_arc_bound`. -/
theorem arc_piece_bound_gen {k : ℤ} {r t : ℝ} (hr0 : 0 < r) (hk : 1 - sigma k ≤ r)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj m r t φ) :
    (∫ φ in (theta (k+1) r)..(theta k r), F φ)
      ≤ ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr r t := by
  rw [← arc_majorant_integral k r t]
  refine intervalIntegral.integral_mono_ae_restrict (theta_antitone_succ hr0) (hint _ _)
    ((continuous_arcMaj k r t).intervalIntegrable _ _) ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2
    (MeasureTheory.measure_singleton (theta (k+1) r)), hle k] with φ hφ hφle hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk (lt_of_le_of_ne hmem.1 (Ne.symm hφ)) hmem.2
  exact hφle hs1 hs2

/-- **The generic boundary bound on `[θ_{K,r}, π/2]`.**

### Summary of Proof
On this arc `σ = 1 - r sin φ` runs over `[1-r, σ_K)`, which by `Kidx_mem` and `Kidx_sub_one` lies
entirely within the single chord interval indexed `K-1`. So one application of the pointwise
bound at that index suffices, and `arc_majorant_boundary_integral` evaluates the resulting
integral in closed form.

### Lean Notes
This is exactly where the **sine form** of the pointwise bound earns its keep: `θ_{K-1,r}` is
junk here, since `1 - σ_{K-1} > r` puts the argument of `arcsin` outside `[-1,1]` and the clamped
value is meaningless. A hypothesis phrased as `φ ∈ (θ_{K,r}, θ_{K-1,r}]` would therefore be
unusable, while the `sin φ` window is perfectly well behaved.

**`hle` is an *almost-everywhere* domination hypothesis**, as in `arc_piece_bound_gen`; see
there for why.

### References
tex: the boundary term of each `c_{i,r}` display after Equation `\ref{eq:thetak}` (Equation 8),
in the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `Kidx_sub_one`, `arcErr`, `arcMaj`,
`arc_majorant_boundary_integral`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `continuous_arcMaj`,
`mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`, `sigma_lt_one`, `sin_theta_eq`, `theta`,
`theta_le_pi_div_two`.
**Used by:** `half_arc_bound`. -/
theorem arc_boundary_bound_gen {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj m r t φ) :
    (∫ φ in (theta (Kidx r) r)..(Real.pi/2), F φ)
      ≤ ((mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)) * Real.log t
        + ((mCoeffP (Kidx r - 1) + bCoeffP (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeffP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)) * Real.log (Real.log t)
        + ((mCoeffPP (Kidx r - 1) + bCoeffPP (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeffPP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r))
        + (Real.pi/2 - theta (Kidx r) r) * arcErr r t := by
  have hpi := Real.pi_pos
  have hKmem : 1 - sigma (Kidx r) ≤ r := Kidx_mem hr0 hr1
  have hKsub : r < 1 - sigma (Kidx r - 1) := Kidx_sub_one hr0 hr1
  have hK0 : (0:ℝ) ≤ theta (Kidx r) r := theta_nonneg hr0
  have hKpi : theta (Kidx r) r ≤ Real.pi/2 := theta_le_pi_div_two (Kidx r) r
  rw [← arc_majorant_boundary_integral (Kidx r) r t]
  refine intervalIntegral.integral_mono_ae_restrict hKpi (hint _ _)
    ((continuous_arcMaj (Kidx r - 1) r t).intervalIntegrable _ _) ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2
    (MeasureTheory.measure_singleton (theta (Kidx r) r)), hle (Kidx r - 1)] with φ hφ hφle hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  have hlt : theta (Kidx r) r < φ := lt_of_le_of_ne hmem.1 (Ne.symm hφ)
  have hub : φ ≤ Real.pi/2 := hmem.2
  have hs1 : (1 - sigma ((Kidx r - 1) + 1)) / r < Real.sin φ := by
    rw [show Kidx r - 1 + 1 = Kidx r by ring, ← sin_theta_eq hr0 hKmem]
    exact Real.strictMonoOn_sin ⟨by linarith, hKpi⟩ ⟨by linarith, hub⟩ hlt
  have hs2 : Real.sin φ ≤ (1 - sigma (Kidx r - 1)) / r := by
    have h1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
    have h2 : (1:ℝ) < (1 - sigma (Kidx r - 1)) / r := by rw [lt_div_iff₀ hr0]; linarith
    linarith
  exact hφle hs1 hs2

/-- **The quarter-circle bound.** For any `F` dominated by the sine-form majorant,
`∫_0^{π/2} F ≤ c₁ log t + c₂ log log t + c₃ + (π/2)·arcErr`.

### Summary of Proof
This is Proposition `\ref{prop:jensen-easy}` (Proposition 8)'s "integrate term by term and
regroup by `k`" step. Split `[0, π/2]` into the chord pieces `[θ_{K+j+1,r}, θ_{K+j,r}]` and the
boundary piece `[θ_{K,r}, π/2]`; bound each by `arc_piece_bound_gen` and
`arc_boundary_bound_gen`; assemble with `integral_le_tsum_arc`. The resulting series are
definitionally `c₁`, `c₂`, `c₃`, with convergence from `c1_summable`, `c3_summable` and
`hasSum_theta_diff`.

### Lean Notes
The regrouping is carried out as a **countable** decomposition rather than the source's finite
one, which is what `integral_le_tsum_arc` exists for. The `θ_{K+n,r} → 0` limit
(`theta_tendsto_zero`) is what makes the pieces exhaust the quarter.

**`hle` is an *almost-everywhere* domination hypothesis**, as in `arc_piece_bound_gen`; see
there for why.

### References
tex: the `c_{i,r}` displays after Equation `\ref{eq:thetak}` (Equation 8) and the regrouping step
in the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `arcErr`, `arcMaj`, `arc_boundary_bound_gen`,
`arc_piece_bound_gen`, `bCoeffP`, `bCoeffP_eq_one`, `c1`, `c1_summable`, `c2`, `c3`,
`c3_summable`, `hasSum_theta_diff`, `integral_le_tsum_arc`, `mCoeffP`, `mCoeffP_eq_zero`,
`theta`, `theta_nonneg`.
**Used by:** `jensen_easy_lower_quarter`, `jensen_easy_upper_quarter`. -/
theorem half_arc_bound {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj m r t φ) :
    (∫ φ in (0:ℝ)..(Real.pi/2), F φ)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
        + (Real.pi/2) * arcErr r t := by
  have hidx : ∀ j : ℕ, 1 - sigma (Kidx r + j) ≤ r := by
    intro j
    have hmono : sigma (Kidx r) ≤ sigma (Kidx r + j) := sigma_strictMono.monotone (by omega)
    linarith [Kidx_mem hr0 hr1]
  -- the four component series
  have hths := hasSum_theta_diff (Kidx r) hr0
  have hc2s : HasSum (fun j : ℕ =>
      (mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
      (theta (Kidx r) r) := by
    have he : (fun j : ℕ =>
        (mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
            * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
          + mCoeffP (Kidx r + j) * r
              * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
        = fun j : ℕ => theta (Kidx r + j) r - theta (Kidx r + j + 1) r := by
      funext j; rw [mCoeffP_eq_zero, bCoeffP_eq_one]; ring
    rw [he]; exact hths
  have hgsum := (((((c1_summable hr0 hr1).hasSum.mul_right (Real.log t)).add
    (hc2s.mul_right (Real.log (Real.log t)))).add
      (c3_summable hr0).hasSum).add (hths.mul_right (arcErr r t)))
  -- the countable family
  have htail := integral_le_tsum_arc (K := Kidx r) hr0 hint hgsum.summable
    (fun j => arc_piece_bound_gen hr0 (hidx j) hint hle)
  rw [hgsum.tsum_eq] at htail
  -- the boundary piece
  have hbdry := arc_boundary_bound_gen hr0 hr1 hint hle
  calc (∫ φ in (0:ℝ)..(Real.pi/2), F φ)
      = (∫ φ in (0:ℝ)..(theta (Kidx r) r), F φ)
          + (∫ φ in (theta (Kidx r) r)..(Real.pi/2), F φ) :=
        (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
    _ ≤ _ := add_le_add htail hbdry
    _ = c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
          + (Real.pi/2) * arcErr r t := by rw [c1, c2, c3, hc2s.tsum_eq]; ring

/-- **The total slack: `arcErr r t ≤ 6/t`.**

### Summary of Proof
With `r < 1` and `t > 10¹²+1` one has `r/(t-r) ≤ 1/(t-1) ≤ 10⁻¹²`, so `log t - r/(t-r) ≥ 1` and
every summand of `arcErr` is at most a multiple of `1/(t-1)`. Adding them gives
`≤ (17/3)/(t-1) ≤ 6/t`.

### Lean Notes
The factor-of-two bookkeeping that turns this into the Proposition's error term: each quarter
circle contributes `(π/2)·arcErr`, and
`(1/(2π))·2·(π/2)·arcErr = arcErr/2 ≤ 3/t`.

### References
tex: the `O^*` term of Proposition `\ref{prop:jensen-easy}` (Proposition 8) — though note this
crude `3/t` is weaker than the printed error, which `jensen_easy_tight` matches instead.

### Dependencies
**Depends on:** `arcErr`.
**Used by:** `jensen_easy`. -/
theorem arcErr_le_six_div {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hlt : 2 < Real.log t) : arcErr r t ≤ 6 / t := by
  have hbig : (10:ℝ)^(12:ℕ) = 1000000000000 := by norm_num
  rw [hbig] at ht
  have ht0 : (0:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  have ht1 : (0:ℝ) < t - 1 := by linarith
  have hd0 : (0:ℝ) < r / (t - r) := div_pos hr0 htr
  have hd : r / (t - r) ≤ 1 / (t - 1) := by
    rw [div_le_div_iff₀ htr ht1]; nlinarith
  have hinv : 1 / (t - 1) ≤ 1 := by
    rw [div_le_one ht1]; linarith
  have h2 : (r / (t - r)) / (Real.log t - r / (t - r)) ≤ (r / (t - r)) / 1 := by
    apply div_le_div_of_nonneg_left hd0.le (by norm_num)
    linarith
  have h3 : 4 / (t - r) ≤ 4 / (t - 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) ht1
    linarith
  have hkey : arcErr r t ≤ (17/3) / (t - 1) := by
    unfold arcErr
    have e4 : (4:ℝ) / (t - 1) = 4 * (1 / (t - 1)) := by ring
    rw [div_one] at h2
    have e17 : (17/3 : ℝ) / (t - 1) = (2/3) * (1/(t-1)) + (1/(t-1)) + 4 * (1/(t-1)) := by ring
    rw [e17]
    have : (2/3) * (r / (t - r)) ≤ (2/3) * (1/(t-1)) := by linarith
    rw [e4] at h3
    linarith
  have hfin : (17/3 : ℝ) / (t - 1) ≤ 6 / t := by
    rw [div_le_div_iff₀ ht1 ht0]; nlinarith
  linarith

/-- **The lower quarter `θ ∈ [π/2, π]`**, via the substitution `θ = φ + π/2`.

### Summary of Proof
Reparametrise by `φ = θ - π/2`, so the quarter becomes `φ ∈ [0, π/2]`, then apply
`half_arc_bound` to the shifted integrand — whose sine-form domination is
`arc_pointwise_le_maj_sin` and whose integrability is
`intervalIntegrable_log_zeta_circle_shift`.

### Lean Notes
`half_arc_bound`'s domination hypothesis is supplied almost everywhere: `ae_zeta_arc_ne_zero`
(with `b = c = r`) discharges `arc_pointwise_le_maj_sin`'s `hz` off a null set of `φ`. This is
one of the two places where the reflection hypothesis introduced by `zetalessthanhalf_upper`
stops; nothing above this statement carries it.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8), whose stated `θ`-ranges
lie in `[π/2, π]`.

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr`, `arc_pointwise_le_maj_sin`, `c1`, `c2`, `c3`,
`half_arc_bound`, `intervalIntegrable_log_zeta_circle_shift`.
**Used by:** `jensen_easy`. -/
theorem jensen_easy_lower_quarter {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hlog : r / (t - r) < Real.log t) :
    (∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r + (Real.pi/2) * arcErr r t := by
  have hchg : (∫ φ in (0:ℝ)..(Real.pi/2),
      Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ):ℂ) * Complex.I))‖)
      = ∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
    rw [intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := Real.pi/2)
      (fun θ : ℝ => Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) (Real.pi/2),
      zero_add, show (Real.pi/2 + Real.pi/2 : ℝ) = Real.pi by ring]
  rw [← hchg]
  refine half_arc_bound hr0 hr
    (fun u v => intervalIntegrable_log_zeta_circle_shift ((1:ℂ) + (t:ℂ) * Complex.I) r
      (Real.pi/2) u v) ?_
  -- The pointwise bound needs `ζ` non-zero at the mirror point `r sin φ + i(t + r cos φ)`;
  -- that fails only on a discrete, hence null, set of `φ` (`ae_zeta_arc_ne_zero`).
  intro m
  filter_upwards [ae_zeta_arc_ne_zero (b := r) (c := r) hr0.ne' hr0.ne' t] with φ hne h1 h2
  exact arc_pointwise_le_maj_sin hr0 hr ht hlog h1 h2 hne

/-- **The upper quarter `θ ∈ [π, 3π/2]`**, via the substitution `θ = 3π/2 - φ`.

### Summary of Proof
Reparametrise by the reflection `φ = 3π/2 - θ`, again landing on `φ ∈ [0, π/2]`, and apply
`half_arc_bound`. The majorant is unchanged because it depends on `φ` only through `sin φ`
(`arcMaj_pi_sub`), so the same bound applies verbatim.

### Lean Notes
Worth being precise about what is and is not symmetric here. The *integrand* is **not** symmetric
about `θ = π`: conjugation `ζ(conj s) = conj ζ(s)` moves the centre from `1+it` to `1-it`. Only
the majorant is symmetric — and that is all the argument uses.

**The reflected circle runs the other way here**, so the null set to exclude is the one for
`ae_zeta_arc_ne_zero` with `c = -r`: the mirror of the arc point is `r sin φ + i(t - r cos φ)`.
As in `jensen_easy_lower_quarter`, this is where `arc_pointwise_le_maj_sin`'s `hz` is discharged.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8), which treats
`[π, 3π/2]` as the mirror image of `[π/2, π]`.

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr`, `arcMaj_pi_sub`, `arc_pointwise_le_maj_sin`,
`c1`, `c2`, `c3`, `half_arc_bound`, `intervalIntegrable_log_zeta_circle_reflect`.
**Used by:** `jensen_easy`. -/
theorem jensen_easy_upper_quarter {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10:ℝ)^(12:ℕ) + 1 < t) (hlog : r / (t - r) < Real.log t) :
    (∫ θ in Real.pi..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r + (Real.pi/2) * arcErr r t := by
  have hchg : (∫ φ in (0:ℝ)..(Real.pi/2),
      Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((3*Real.pi/2 - φ : ℝ):ℂ) * Complex.I))‖)
      = ∫ θ in Real.pi..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
    rw [intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Real.pi/2)
      (fun θ : ℝ => Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) (3*Real.pi/2),
      sub_zero, show (3*Real.pi/2 - Real.pi/2 : ℝ) = Real.pi by ring]
  rw [← hchg]
  refine half_arc_bound hr0 hr
    (fun u v => intervalIntegrable_log_zeta_circle_reflect ((1:ℂ) + (t:ℂ) * Complex.I) r
      (3*Real.pi/2) u v) ?_
  -- On the mirror quarter the reflected circle is traversed the other way, so the null set here
  -- is that of `ae_zeta_arc_ne_zero` with `c = -r`.
  intro m
  filter_upwards [ae_zeta_arc_ne_zero (b := r) (c := -r) hr0.ne' (neg_ne_zero.2 hr0.ne') t]
    with φ hne h1 h2
  have hs : Real.sin (Real.pi - φ) = Real.sin φ := Real.sin_pi_sub φ
  have hcs : Real.cos (Real.pi - φ) = -Real.cos φ := Real.cos_pi_sub φ
  have hz : riemannZeta (((r * Real.sin (Real.pi - φ) : ℝ) : ℂ)
      + ((t + r * Real.cos (Real.pi - φ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    rw [hs, hcs, show (t + r * -Real.cos φ : ℝ) = t + -r * Real.cos φ by ring]
    exact hne
  have hkey := arc_pointwise_le_maj_sin (k := m) (r := r) (t := t) (φ := Real.pi - φ)
    hr0 hr ht hlog (by rw [hs]; exact h1) (by rw [hs]; exact h2) hz
  rw [arcMaj_pi_sub] at hkey
  rw [show (3*Real.pi/2 - φ : ℝ) = ((Real.pi - φ) + Real.pi/2 : ℝ) by ring]
  exact hkey

/-- **Proposition `\ref{prop:jensen-easy}` (Proposition 8), crude version.** For `0 < r < 1`
and `t > 10¹² + 1`,
`(1/(2π))∫_{π/2}^{3π/2} log|ζ(1+it+re^{iθ})|dθ ≤ (c₁,r/π) log|t| + (c₂,r/π) log log|t| + c₃,r/π
+ O^*(3/t)`.

### Summary of Proof
The source bounds `log|ζ|` on the circle by the piecewise-linear majorant `F_{1+it,r}(θ)` built
from the chord data, then integrates that majorant. Because the majorant depends on `θ` only
through `sin(θ-π/2)`, the integral over the half `[π/2,3π/2]` is twice the quarter-circle
integral, and regrouping the quarter by chord index `k` produces exactly the series defining
`c_{1,r}`, `c_{2,r}`, `c_{3,r}`. The discrepancy between `log|t+r|` and `log|t|`, together with
the slack in the pointwise bound, is the `O^*` term.

### Lean Notes
**This is a deliberately weaker milestone than the printed Proposition
`\ref{prop:jensen-easy}` (Proposition 8).** The tex states the proposition for `t > 13` with the
sharp error `5/(6(t-1)) + 1/(t-1)² + 579/(8(t-1)²log(t-1))`; this version needs the far stronger
threshold `t > 10¹² + 1` and delivers only the flat `3/t`. `jensen_easy_tight` below is the one
that matches the printed statement exactly.

**The integration range is `[π/2,3π/2]`, the "outside the critical strip" half**, matching
`ZerosInShortIntervals.tex` exactly. (A naive reading of the geometry might suggest
the symmetric-looking `[-π/2,3π/2]` instead; three independent checks rule that out.)

* *The proof's own parametrisation.* The displayed bounding function is
  `F(θ) = (m_k r sin(θ-π/2) - b_k)log|t+r| + …` on `θ ∈ (θ_{k+1,r}+π/2, θ_{k,r}+π/2)`. Since the
  point on the circle has `σ = 1 + r cos θ`, i.e. `1 - σ = r sin(θ - π/2)`, the parametrisation only
  makes sense for `sin(θ-π/2) ≥ 0`, i.e. `θ ∈ [π/2, 3π/2]`, and the stated `θ`-ranges lie in
  `[π/2, π]` (with `[π, 3π/2]` its mirror image).
* *The constants.* The closed form (see `JensenScaleConstants`) is
  `c_{i,r} = ∫_0^{π/2} A_i(1 - r sin φ) dφ` over a **quarter** circle; the substitution `φ = θ-π/2`
  and symmetry about `φ = π/2` give `(1/(2π))∫_{π/2}^{3π/2} = (1/π)∫_0^{π/2}`, which is exactly the
  `c_{i,r}/π` of the displayed conclusion. Concretely `c_{2,r} = π/2` — the value `1.570797`
  printed in Table `\ref{tab:crvalues}` (Table 2) at the smaller radii — because the `log log`
  coefficient is identically `1`, so `c_2 = ∫_0^{π/2}1 dφ = π/2`: a quarter-circle normalisation,
  not a three-quarter one.
* *Theorem `\ref{thm:circularregions1}` (Theorem 16).* Its proof adds `c_{4,r}` from Proposition
  `\ref{prop:integraloutside}` (Proposition 15), which bounds precisely the *complementary* half
  `[-π/2,π/2]`, and its `C_{3,α,r}` indeed contains `c_{4,r}/log(r/α)`. With the printed range the
  half `[-π/2,π/2]` would be counted twice.

**Proof, as formalized.** By construction, on each interval `θ ∈ (θ_{k+1,r}+π/2, θ_{k,r}+π/2)` the
piecewise-linear function `F_{1+it,r}` above bounds `log|ζ(1+it+re^{iθ})|` — this is where
`YANG2024128124` and Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36) enter, through
`JensenScaleConstants.zeta_piecewise_bound` (a genuine consequence of
`BackgroundZetaBounds.interpolated_bound_1b/2` and `zetalessthanhalf_upper`, modulo the
strengthened threshold `10¹²<|t|` and the explicit `O^*(4/|t|)` slack in its conclusion). The four
steps are:

1. `arc_pointwise_le_maj_sin` — the pointwise bound, with the chord index pinned by a condition on
   `sin φ` alone, and the ordinate `t + r cos φ` of the circle point replaced by `t` at a cost of
   `arcErr r t` (`log_arc_window`, `loglog_arc_window`);
2. `arc_piece_bound_gen` / `arc_boundary_bound_gen` — one chord piece and the boundary piece
   `[θ_{K,r}, π/2]`, integrated against the affine majorant via `chord_term_eq_integral` and
   `chord_boundary_eq_integral`. Both step over the single endpoint where the index jumps, using
   `integral_mono_ae_restrict`;
3. `half_arc_bound` — the quarter `[0, π/2]`, assembled by `integral_le_tsum_arc`. The regrouping
   "by `k`" of the source is a *countable* decomposition here, `[0, θ_{K,r}] = ⋃_j [θ_{K+j+1,r},
   θ_{K+j,r}]`, and the resulting `tsum` is definitionally the one in `c1`/`c2`/`c3`
   (`c1_summable`, `c3_summable`, `hasSum_theta_diff`);
4. the two quarters `[π/2, π]` and `[π, 3π/2]` (`θ = φ + π/2` and `θ = 3π/2 - φ`), which give the
   same bound because the majorant depends on `φ` only through `sin φ` (`arcMaj_pi_sub`). Note the
   *integrand* is **not** symmetric about `θ = π`: `ζ(conj s) = conj ζ(s)` moves the centre from
   `1+it` to `1-it`. Only the majorant is symmetric, which is all the argument uses.

The `log|t+r|` vs. `log|t|` discrepancy plus `zeta_piecewise_bound`'s slack is `arcErr r t`, and
`arcErr_le_six_div` gives `(1/(2π))·π·arcErr = arcErr/2 ≤ 3/t`.

### References
tex: Proposition `\ref{prop:jensen-easy}` (Proposition 8); the majorant display and the
`c_{i,r}` definitions following Equation `\ref{eq:thetak}` (Equation 8);
`JensenScaleConstants.zeta_piecewise_bound`, resting on Proposition `\ref{prop:interpolation}`
(Proposition 35) and Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `arcErr`, `arcErr_le_six_div`, `c1`, `c2`, `c3`,
`intervalIntegrable_log_zeta_circle`, `jensen_easy_lower_quarter`, `jensen_easy_upper_quarter`,
`two_lt_log_of_gt_eight`.
**Used by:** `circularregions1`, `rectangularjensen`. -/
theorem jensen_easy {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) + 1 < t) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
          Real.log ‖riemannZeta (1 + t * Complex.I + r * Complex.exp (θ * Complex.I))‖
      ≤ c1 r / Real.pi * Real.log t + c2 r / Real.pi * Real.log (Real.log t) + c3 r / Real.pi
        + 3 / t := by
  have hpi := Real.pi_pos
  have hbig : (0:ℝ) < (10:ℝ)^(12:ℕ) := by positivity
  have ht0 : (0:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  -- `log t > 2`, hence `r/(t-r) < 1 < log t`
  have hlt : 2 < Real.log t := two_lt_log_of_gt_eight (by
    have : (8:ℝ) ≤ (10:ℝ)^(12:ℕ) := by norm_num
    linarith)
  have hlog : r / (t - r) < Real.log t := by
    have h1 : r / (t - r) ≤ 1 := by rw [div_le_one htr]; linarith
    linarith
  -- split the half circle at `θ = π`
  have hsplit : (∫ θ in (Real.pi/2)..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      = (∫ θ in (Real.pi/2)..Real.pi,
          Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + ∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log_zeta_circle ((1:ℂ) + (t:ℂ) * Complex.I) r _ _)
      (intervalIntegrable_log_zeta_circle ((1:ℂ) + (t:ℂ) * Complex.I) r _ _)).symm
  have hlow := jensen_easy_lower_quarter hr0 hr ht hlog
  have hup := jensen_easy_upper_quarter hr0 hr ht hlog
  have herr := arcErr_le_six_div hr0 hr ht hlt
  rw [hsplit]
  -- `(1/(2π))·(2·(c₁ log t + c₂ loglog t + c₃) + π·arcErr) = (c₁/π)log t + ⋯ + arcErr/2`
  have hsum : (∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + (∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ 2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
          + Real.pi * arcErr r t := by linarith
  have hmul : (1 / (2 * Real.pi)) * ((∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + ∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ (1 / (2 * Real.pi)) * (2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
          + Real.pi * arcErr r t) := by
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have hval : (1 / (2 * Real.pi)) * (2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
        + Real.pi * arcErr r t)
      = c1 r / Real.pi * Real.log t + c2 r / Real.pi * Real.log (Real.log t) + c3 r / Real.pi
        + arcErr r t / 2 := by
    field_simp
  rw [hval] at hmul
  have hlast : arcErr r t / 2 ≤ 3 / t := by
    have h6 : (3:ℝ) / t = (6 / t) / 2 := by ring
    rw [h6]; linarith
  linarith

/-- **Tight version of `arcErr`.**

### Summary of Proof
A definition. It replaces the `4/(t-r)` slack — which came from the crude, `O(1/t)`
`JensenScaleConstants.zeta_piecewise_bound` — with the genuinely tight `O(1/(t-r)²)` slack of
`zeta_piecewise_bound_tight_simple`.

### Lean Notes
The **two window-conversion pieces are unchanged**, because they have nothing to do with
Proposition `\ref{prop:interpolation}` (Proposition 35): converting `log(t + r cos φ)` to
`log t` costs `O(1/t)` whatever the interpolation bound is. So `arcErr_tight` is *not* uniformly
`O(1/t²)`; only its dominant summand improves.

### References
tex: the `O^*` term of Proposition `\ref{prop:jensen-easy}` (Proposition 8), whose printed form
this error is what makes reachable; Proposition `\ref{prop:interpolation}` (Proposition 35)
supplies the tight input.

### Dependencies
**Depends on:** none.
**Used by:** `FcrZeta_integral_le`, `FcrZeta_outside_integral`, `arcErr_tight_crude_lt_three`,
`arcErr_tight_le`, `arcMaj_tight`, `arc_boundary_bound_gen_tight`,
`arc_majorant_boundary_integral_tight`, `arc_majorant_integral_tight`,
`arc_piece_bound_gen_tight`, `arc_piece_bound_tight`, `arc_pointwise_le_maj_sin_tight`,
`half_arc_bound_tight`, `jensen_easy_tight`, `jensen_easy_lower_quarter_tight`,
`jensen_easy_upper_quarter_tight`, `arcMaj_tight_congr_sin`, `littlewoodshort_tight`. -/
noncomputable def arcErr_tight (r t : ℝ) : ℝ :=
  (2/3) * (r / (t - r)) + (r / (t - r)) / (Real.log t - r / (t - r))
    + (2 / (t - r) ^ 2 + 1158 / (8 * (t - r) ^ 2 * Real.log (t - r)))

/-- **The tight piecewise-affine majorant `arcMaj_tight k r t φ`** on the chord piece indexed
`k`.

### Summary of Proof
A definition, identical in shape to `arcMaj` — the three chords of index `k` evaluated at
`σ = 1 - r sin φ`, with `t` in place of the circle point's own ordinate `t + r cos φ` — but
carrying `arcErr_tight` in place of `arcErr`.

### References
tex: the majorant display `F_{1+it,r}(θ)` in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `arcErr_tight`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `mCoeff`, `mCoeffP`,
`mCoeffPP`.
**Used by:** `FcrZeta_minus_le_arcMaj`, `FcrZeta_plus_le_arcMaj`, `arcMaj_pi_sub_tight`,
`arcMaj_tight_congr_sin`, `arc_boundary_bound_gen_tight`,
`arc_majorant_boundary_integral_tight`, `arc_majorant_integral_tight`,
`arc_piece_bound_gen_tight`, `arc_pointwise_le_maj_sin_tight`, `arc_pointwise_le_maj_tight`,
`continuous_arcMaj_tight`, `half_arc_bound_tight`. -/
noncomputable def arcMaj_tight (k : ℤ) (r t : ℝ) (φ : ℝ) : ℝ :=
  (mCoeff k * (1 - r * Real.sin φ) + bCoeff k) * Real.log t
    + (mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k) * Real.log (Real.log t)
    + (mCoeffPP k * (1 - r * Real.sin φ) + bCoeffPP k)
    + arcErr_tight r t

/-- **`arcMaj_tight k r t` is continuous** in the angle.

### Summary of Proof
As `continuous_arcMaj`: unfold and `fun_prop`. The tight majorant differs only in its error term,
which is likewise a continuous function of the angle.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcMaj_tight`.
**Used by:** `arc_boundary_bound_gen_tight`, `arc_piece_bound_gen_tight`,
`arc_piece_bound_tight`. -/
theorem continuous_arcMaj_tight (k : ℤ) (r t : ℝ) : Continuous (arcMaj_tight k r t) := by
  unfold arcMaj_tight; fun_prop

/-- **The tight majorant is symmetric about `φ = π/2`**:
`arcMaj_tight k r t (π - φ) = arcMaj_tight k r t φ`.

### Summary of Proof
Immediate from the definition, since `arcMaj_tight` depends on `φ` only through `sin φ` and
`sin(π - φ) = sin φ`.

### Lean Notes
As for `arcMaj_pi_sub`: this is symmetry of the **majorant**, not of the integrand. The integrand
is not symmetric about `θ = π`, since conjugation moves the centre from `1+it` to `1-it`.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `arcMaj_tight`.
**Used by:** `jensen_easy_upper_quarter_tight`. -/
theorem arcMaj_pi_sub_tight (k : ℤ) (r t φ : ℝ) :
    arcMaj_tight k r t (Real.pi - φ) = arcMaj_tight k r t φ := by
  unfold arcMaj_tight; rw [Real.sin_pi_sub]

/-- **`∫ arcMaj_tight` over a chord piece equals the three closed-form summands plus the
error.**

### Summary of Proof
As `arc_majorant_integral`: apply `chord_term_eq_integral` to each of the three chord families
and integrate the constant `arcErr_tight` over the piece.

### References
tex: the `k`-th summand of the `c_{i,r}` displays after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `arcErr_tight`, `arcMaj_tight`, `bCoeff`, `bCoeffP`, `bCoeffPP`,
`chord_term_eq_integral`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `theta`.
**Used by:** `arc_piece_bound_gen_tight`, `arc_piece_bound_tight`. -/
theorem arc_majorant_integral_tight (k : ℤ) (r t : ℝ) :
    (∫ φ in (theta (k+1) r)..(theta k r), arcMaj_tight k r t φ)
      = ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr_tight r t := by
  have e1 := chord_term_eq_integral (k := k) (mCoeff k) (bCoeff k) r
  have e2 := chord_term_eq_integral (k := k) (mCoeffP k) (bCoeffP k) r
  have e3 := chord_term_eq_integral (k := k) (mCoeffPP k) (bCoeffPP k) r
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume
      (theta (k+1) r) (theta k r) := fun g hg => hg.intervalIntegrable _ _
  unfold arcMaj_tight
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) intervalIntegrable_const,
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, ← e1, ← e2, ← e3]
  simp only [smul_eq_mul]
set_option maxHeartbeats 300000 in
-- the extra `O(1/(t+r sin θ)²)` algebra pushes this past the default elaboration budget.
/-- **Tight version of `arc_pointwise_bound`**, with an `O(1/t²)` error.

### Summary of Proof
Identical to `arc_pointwise_bound` — `circle_pt` converts to `σ + it` coordinates,
`chordIdx_spec` pins the chord interval — but drawing on
`JensenScaleConstants.zeta_piecewise_bound_tight_simple`, Proposition
`\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)` bound, in place of the
crude `O(1/t)` `zeta_piecewise_bound`.

### Lean Notes
Carries the same non-vanishing hypothesis `hz` as `arc_pointwise_bound`, for the same reason and
discharged at the same kind of site (here `jensen_easy_*_quarter_tight` and
`Littlewood.ZetaCircleFcr.FcrZeta_outside_integral`).

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35), tight forms; the majorant display
in the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `chordA`, `chordA'`, `chordA''`, `chordIdx`, `chordIdx_spec`, `circle_pt`,
`zeta_piecewise_bound_tight_simple`.
**Used by:** `arc_pointwise_bound_sin_tight`. -/
theorem arc_pointwise_bound_tight {r t θ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hcos : Real.cos θ < 0)
    (hz : riemannZeta (((-(r * Real.cos θ) : ℝ) : ℂ)
        + ((t + r * Real.sin θ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖
      ≤ chordA (1 + r * Real.cos θ) * Real.log (t + r * Real.sin θ)
        + chordA' (1 + r * Real.cos θ) * Real.log (Real.log (t + r * Real.sin θ))
        + chordA'' (1 + r * Real.cos θ)
        + (2 / (t + r * Real.sin θ) ^ 2
            + 1158 / (8 * (t + r * Real.sin θ) ^ 2 * Real.log (t + r * Real.sin θ))) := by
  set σ : ℝ := 1 + r * Real.cos θ with hσ_def
  have hcos1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hσ0 : 0 < σ := by rw [hσ_def]; nlinarith
  have hσ1 : σ < 1 := by rw [hσ_def]; nlinarith
  obtain ⟨h1, h2⟩ := chordIdx_spec hσ0 hσ1
  have hsin : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
  have ht' : (10:ℝ) < t + r * Real.sin θ := by nlinarith [Real.sin_le_one θ]
  have habs : |t + r * Real.sin θ| = t + r * Real.sin θ := by
    apply abs_of_pos
    linarith
  have hkey := zeta_piecewise_bound_tight_simple (k := chordIdx σ) (σ := σ)
    (t := t + r * Real.sin θ) h1 h2 (by rw [habs]; exact ht')
    (by
      rw [habs, hσ_def,
        show (1:ℂ) - ((1 + r * Real.cos θ : ℝ) : ℂ) = ((-(r * Real.cos θ) : ℝ) : ℂ) by
          push_cast; ring]
      exact hz)
  rw [habs] at hkey
  rw [circle_pt]
  exact hkey
/-- **Pointwise bound on the arc, indexed by `sin φ`** — the tight counterpart of
`arc_pointwise_bound_sin`.

### Summary of Proof
As `arc_pointwise_bound_sin`, but built on `arc_pointwise_bound_tight`. The point of the
reindexing is that the chord index is pinned by a condition on `sin φ` alone: on the arc
`θ = φ + π/2` the abscissa is `σ = 1 - r sin φ`, so the hypothesis `σ_k ≤ 1 - r sin φ < σ_{k+1}`
identifies `k = chordIdx σ` via `chordIdx_eq`, and the three chords `chordA`, `chordA'`,
`chordA''` at that `σ` are exactly `mCoeff k · σ + bCoeff k` and its two companions.

### Lean Notes
Stating the bound in terms of `sin φ` rather than `θ` is what lets the later arc-piece integrals
be taken over `θ`-intervals whose endpoints are the `θ_{k,r}`, without re-deriving the chord
index at every step.

Carries `arc_pointwise_bound_tight`'s hypothesis `hz`, rewritten at `θ = φ + π/2` to
`ζ(r sin φ + i(t + r cos φ)) ≠ 0`.

### References
tex: the majorant display `F_{1+it,r}(θ)` in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8), whose parametrisation by `sin(θ-π/2)` this mirrors; the tight input is
Proposition `\ref{prop:interpolation}` (Proposition 35).

### Dependencies
**Depends on:** `arc_pointwise_bound_tight`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `chordA`,
`chordA'`, `chordA''`, `chordIdx`, `chordIdx_eq`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`,
`sigma_lt_one`.
**Used by:** `arc_pointwise_le_maj_sin_tight`. -/
theorem arc_pointwise_bound_sin_tight {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ (mCoeff k * (1 - r * Real.sin φ) + bCoeff k) * Real.log (t + r * Real.cos φ)
        + (mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k)
            * Real.log (Real.log (t + r * Real.cos φ))
        + (mCoeffPP k * (1 - r * Real.sin φ) + bCoeffPP k)
        + (2 / (t + r * Real.cos φ) ^ 2
            + 1158 / (8 * (t + r * Real.cos φ) ^ 2 * Real.log (t + r * Real.cos φ))) := by
  -- the trig shift
  have hcosθ : Real.cos (φ + Real.pi/2) = -Real.sin φ := by
    rw [Real.cos_add_pi_div_two]
  have hsinθ : Real.sin (φ + Real.pi/2) = Real.cos φ := by
    rw [Real.sin_add_pi_div_two]
  -- `sin φ > 0`, since `σ_{k+1} < 1`
  have hpos : 0 < (1 - sigma (k+1)) / r := div_pos (by linarith [sigma_lt_one (k+1)]) hr0
  have hsinpos : 0 < Real.sin φ := lt_trans hpos hs1
  -- the two chord inequalities
  have hA : sigma k ≤ 1 - r * Real.sin φ := by
    have h : r * Real.sin φ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h
    linarith
  have hB : 1 - r * Real.sin φ < sigma (k+1) := by
    have h : r * ((1 - sigma (k+1)) / r) < r * Real.sin φ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h
    linarith
  -- apply the generic bound and pin the index
  have hbound := arc_pointwise_bound_tight (r := r) (t := t) (θ := φ + Real.pi/2) hr0 hr ht
    (by rw [hcosθ]; linarith)
    (by
      rw [hcosθ, hsinθ, show (-(r * -Real.sin φ) : ℝ) = r * Real.sin φ by ring]
      exact hz)
  rw [hcosθ, hsinθ] at hbound
  have hidx : chordIdx (1 + r * -Real.sin φ) = k := by
    refine chordIdx_eq ?_ ?_ <;> · rw [show 1 + r * -Real.sin φ = 1 - r * Real.sin φ by ring]
                                   first | exact hA | exact hB
  simp only [chordA, chordA', chordA'', hidx] at hbound
  rw [show 1 + r * -Real.sin φ = 1 - r * Real.sin φ by ring] at hbound
  exact hbound

set_option maxHeartbeats 300000 in
-- the `h4` worst-point analysis (replacing a one-line bound with a multi-step `O(1/(t-r)²)`
-- comparison) pushes this past the default elaboration budget.
/-- **Tight version of `arc_pointwise_le_maj_sin`**: `log‖ζ‖ ≤ arcMaj_tight k r t φ` on the
chord window.

### Summary of Proof
As `arc_pointwise_le_maj_sin`, starting from `arc_pointwise_bound_sin_tight` and paying for the
two window conversions with `log_arc_window` and `loglog_arc_window`.

The one substantive difference is the worst-point step. The crude version bounds
`4/(t + r cos φ) ≤ 4/(t-r)` directly; here the analogous quantity is
`x ↦ 2/x² + 1158/(8x² log x)`, which is *decreasing* for `x > 1`, so its value at
`t + r cos φ ≥ t-r` is bounded by its value at `t-r`.

Carries `arc_pointwise_bound_sin_tight`'s hypothesis `hz` — `ζ` non-zero at the mirror point
`r sin φ + i(t + r cos φ)`. This is the live carrier on the tight track:
`jensen_easy_lower_quarter_tight`, `jensen_easy_upper_quarter_tight` and
`Littlewood.ZetaCircleFcr.FcrZeta_outside_integral` discharge it almost everywhere with
`ae_zeta_arc_ne_zero`, so nothing above them carries a non-vanishing hypothesis.

### References
tex: the majorant display in the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8);
Proposition `\ref{prop:interpolation}` (Proposition 35) for the tight input.

### Dependencies
**Depends on:** `arcErr_tight`, `arcMaj_tight`, `arc_pointwise_bound_sin_tight`, `bCoeff`,
`bCoeffP`, `bCoeffP_eq_one`, `chord_vCoeff_le`, `chord_vCoeff_nonneg`, `log_arc_window`,
`loglog_arc_window`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `bCoeffPP`, `sigma`.
**Used by:** `FcrZeta_plus_le_arcMaj`, `arc_pointwise_le_maj_tight`,
`jensen_easy_lower_quarter_tight`, `jensen_easy_upper_quarter_tight`. -/
theorem arc_pointwise_le_maj_sin_tight {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t)
    (hlog : r / (t - r) < Real.log t)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ arcMaj_tight k r t φ := by
  have ht2 : (2:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  have htr1 : (1:ℝ) < t - r := by linarith
  have hd1 : (0:ℝ) ≤ r / (t - r) := le_of_lt (div_pos hr0 htr)
  have hpt := arc_pointwise_bound_sin_tight hr0 hr ht hs1 hs2 hz
  -- the chord value at `φ`
  set A : ℝ := mCoeff k * (1 - r * Real.sin φ) + bCoeff k with hA_def
  have hpos : 0 < (1 - sigma (k+1)) / r := div_pos (by linarith [sigma_lt_one (k+1)]) hr0
  have hsinpos : 0 < Real.sin φ := lt_trans hpos hs1
  have hA1 : sigma k ≤ 1 - r * Real.sin φ := by
    have h : r * Real.sin φ ≤ r * ((1 - sigma k) / r) := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  have hA2 : 1 - r * Real.sin φ ≤ sigma (k+1) := by
    have h : r * ((1 - sigma (k+1)) / r) ≤ r * Real.sin φ := by nlinarith
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)] at h; linarith
  have hA0 : 0 ≤ A := chord_vCoeff_nonneg hA1 hA2
  have hAle : A ≤ 2/3 := chord_vCoeff_le hA1 hA2
  -- the three replacements
  have hw1 := log_arc_window (r := r) (t := t) (φ := φ) hr0 hr ht2
  have hw2 := loglog_arc_window (r := r) (t := t) (φ := φ) hr0 hr ht2 hlog
  rw [abs_le] at hw1 hw2
  have hcos1 : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
  have h4 : (2 / (t + r * Real.cos φ) ^ 2
      + 1158 / (8 * (t + r * Real.cos φ) ^ 2 * Real.log (t + r * Real.cos φ)))
      ≤ (2 / (t - r) ^ 2 + 1158 / (8 * (t - r) ^ 2 * Real.log (t - r))) := by
    have hxy : t - r ≤ t + r * Real.cos φ := by nlinarith [hcos1]
    have hsq : (t - r) ^ 2 ≤ (t + r * Real.cos φ) ^ 2 := by nlinarith [hxy, htr]
    have hlogTh : (0:ℝ) < Real.log (t - r) := Real.log_pos htr1
    have hlogle : Real.log (t - r) ≤ Real.log (t + r * Real.cos φ) := Real.log_le_log htr hxy
    have h2a : 2 / (t + r * Real.cos φ) ^ 2 ≤ 2 / (t - r) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity : (0:ℝ) < (t - r) ^ 2) hsq
    have hle2 : (t - r) ^ 2 * Real.log (t - r)
        ≤ (t + r * Real.cos φ) ^ 2 * Real.log (t + r * Real.cos φ) :=
      mul_le_mul hsq hlogle hlogTh.le (by positivity)
    have hd1 : (0:ℝ) < 8 * (t + r * Real.cos φ) ^ 2 * Real.log (t + r * Real.cos φ) := by
      have hlogpos : (0:ℝ) < Real.log (t + r * Real.cos φ) := lt_of_lt_of_le hlogTh hlogle
      have hxpos : (0:ℝ) < t + r * Real.cos φ := by linarith
      exact mul_pos (mul_pos (by norm_num) (pow_pos hxpos 2)) hlogpos
    have hd2 : (0:ℝ) < 8 * (t - r) ^ 2 * Real.log (t - r) := by positivity
    have h2b : 1158 / (8 * (t + r * Real.cos φ) ^ 2 * Real.log (t + r * Real.cos φ))
        ≤ 1158 / (8 * (t - r) ^ 2 * Real.log (t - r)) := by
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith [hle2]
    linarith [h2a, h2b]
  have hAx : A * (Real.log (t + r * Real.cos φ) - Real.log t) ≤ (2/3) * (r / (t - r)) := by
    rcases le_or_gt (Real.log (t + r * Real.cos φ) - Real.log t) 0 with hx | hx
    · nlinarith [hA0, hd1]
    · nlinarith [hAle, hw1.2, hx]
  have hPeq : mCoeffP k * (1 - r * Real.sin φ) + bCoeffP k = 1 := by
    rw [mCoeffP_eq_zero, bCoeffP_eq_one]; ring
  rw [arcMaj_tight, arcErr_tight, ← hA_def, hPeq]
  rw [hPeq] at hpt
  nlinarith [hpt, hw2.2, h4, hAx]

/-- **The angle form of `arc_pointwise_le_maj_sin_tight`**, hypothesis stated as
`φ ∈ (θ_{k+1,r}, θ_{k,r}]`.

### Summary of Proof
`sin_window_of_mem_chord` converts the angle hypothesis into the `sin φ` window that
`arc_pointwise_le_maj_sin_tight` expects.

### Lean Notes
Carries `arc_pointwise_le_maj_sin_tight`'s non-vanishing hypothesis `hz` unchanged; see
`arc_pointwise_bound` for why Lean needs it and where it is discharged.

### References
tex: Equation `\ref{eq:thetak}` (Equation 8); the majorant display in the proof of Proposition
`\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `arcMaj_tight`, `arc_pointwise_le_maj_sin_tight`, `sigma`,
`sin_window_of_mem_chord`, `theta`.
**Used by:** `arc_piece_bound_tight`. -/
theorem arc_pointwise_le_maj_tight {k : ℤ} {r t φ : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hk : 1 - sigma k ≤ r)
    (hlog : r / (t - r) < Real.log t)
    (hφ1 : theta (k+1) r < φ) (hφ2 : φ ≤ theta k r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((t + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖
      ≤ arcMaj_tight k r t φ := by
  obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk hφ1 hφ2
  exact arc_pointwise_le_maj_sin_tight hr0 hr ht hlog hs1 hs2 hz
/-- **The bound on one chord piece, integrated** — the tight counterpart of
`arc_piece_bound`.

### Summary of Proof
Integrate `arc_pointwise_le_maj_tight` over the piece with `integral_mono_ae_restrict`, stepping
over the single left endpoint where the chord index jumps, then evaluate the majorant's integral
by `arc_majorant_integral_tight`.

### Lean Notes
The a.e. comparison absorbs two null sets: the single endpoint where the chord index jumps, and
the zeros of `ζ` on the reflected circle, where `arc_pointwise_le_maj_tight`'s hypothesis `hz`
fails (`ae_zeta_arc_ne_zero`). So `hz` is discharged here and absent from this statement.

### References
tex: the chord-piece decomposition in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr_tight`, `arc_majorant_integral_tight`,
`arc_pointwise_le_maj_tight`,
`bCoeff`, `bCoeffP`, `bCoeffPP`, `continuous_arcMaj_tight`,
`intervalIntegrable_log_zeta_circle_shift`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`, `theta`,
`arcMaj_tight`.
**Used by:** none — superseded by the generic `arc_piece_bound_gen_tight`, which the mirror arc
can also reuse. Kept as the direct, unabstracted form. -/
theorem arc_piece_bound_tight {k : ℤ} {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hk : 1 - sigma k ≤ r)
    (hlog : r / (t - r) < Real.log t) :
    (∫ φ in (theta (k+1) r)..(theta k r),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I))‖)
      ≤ ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr_tight r t := by
  rw [← arc_majorant_integral_tight k r t]
  refine intervalIntegral.integral_mono_ae_restrict (theta_antitone_succ hr0)
    (intervalIntegrable_log_zeta_circle_shift ((1:ℂ) + (t:ℂ) * Complex.I) r (Real.pi/2) _ _)
    ((continuous_arcMaj_tight k r t).intervalIntegrable _ _) ?_
  have hfin : MeasureTheory.volume ({theta (k+1) r} : Set ℝ) = 0 :=
    MeasureTheory.measure_singleton _
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hfin,
    ae_zeta_arc_ne_zero (b := r) (c := r) hr0.ne' hr0.ne' t] with φ hφ hne hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  exact arc_pointwise_le_maj_tight hr0 hr ht hk hlog (lt_of_le_of_ne hmem.1 (Ne.symm hφ))
    hmem.2 hne
/-- **`∫ arcMaj_tight (K-1)` over the boundary piece `[θ_{K,r}, π/2]` equals the three boundary
summands of `c₁`, `c₂`, `c₃` plus the error.**

### Summary of Proof
As `arc_majorant_boundary_integral`, using `chord_boundary_eq_integral` for the closed form on
`[θ_{K,r}, π/2]`.

### References
tex: the leading (boundary) term of each `c_{i,r}` display after Equation `\ref{eq:thetak}`
(Equation 8).

### Dependencies
**Depends on:** `arcErr_tight`, `arcMaj_tight`, `bCoeff`, `bCoeffP`, `bCoeffPP`,
`chord_boundary_eq_integral`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `theta`.
**Used by:** `arc_boundary_bound_gen_tight`. -/
theorem arc_majorant_boundary_integral_tight (K : ℤ) (r t : ℝ) :
    (∫ φ in (theta K r)..(Real.pi/2), arcMaj_tight (K-1) r t φ)
      = ((mCoeff (K-1) + bCoeff (K-1)) * (Real.pi/2 - theta K r)
            - mCoeff (K-1) * r * Real.cos (theta K r)) * Real.log t
        + ((mCoeffP (K-1) + bCoeffP (K-1)) * (Real.pi/2 - theta K r)
            - mCoeffP (K-1) * r * Real.cos (theta K r)) * Real.log (Real.log t)
        + ((mCoeffPP (K-1) + bCoeffPP (K-1)) * (Real.pi/2 - theta K r)
            - mCoeffPP (K-1) * r * Real.cos (theta K r))
        + (Real.pi/2 - theta K r) * arcErr_tight r t := by
  have e1 := chord_boundary_eq_integral (mCoeff (K-1)) (bCoeff (K-1)) r K
  have e2 := chord_boundary_eq_integral (mCoeffP (K-1)) (bCoeffP (K-1)) r K
  have e3 := chord_boundary_eq_integral (mCoeffPP (K-1)) (bCoeffPP (K-1)) r K
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume
      (theta K r) (Real.pi/2) := fun g hg => hg.intervalIntegrable _ _
  unfold arcMaj_tight
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) intervalIntegrable_const,
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, ← e1, ← e2, ← e3]
  simp only [smul_eq_mul]

/-- **The generic per-piece bound**, tight version, for any `F` dominated by the sine-form
majorant.

### Summary of Proof
As `arc_piece_bound_gen`: abstracted over the integrand, so that any `F` satisfying the sine-form
pointwise bound is integrated against `arcMaj_tight` and evaluated by
`arc_majorant_integral_tight`.

### Lean Notes
The abstraction is what lets the mirror arc reuse the lemma, since the hypothesis is stated on
`sin φ` and `sin(π-φ) = sin φ`.

**`hle` is an *almost-everywhere* domination hypothesis**, as in `arc_piece_bound_gen`; see
there for why.

### References
tex: the chord-piece decomposition in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `arcErr_tight`, `arcMaj_tight`, `arc_majorant_integral_tight`, `bCoeff`,
`bCoeffP`, `bCoeffPP`, `continuous_arcMaj_tight`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`,
`sin_window_of_mem_chord`, `theta`, `theta_antitone_succ`.
**Used by:** `half_arc_bound_tight`. -/
theorem arc_piece_bound_gen_tight {k : ℤ} {r t : ℝ} (hr0 : 0 < r) (hk : 1 - sigma k ≤ r)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj_tight m r t φ) :
    (∫ φ in (theta (k+1) r)..(theta k r), F φ)
      ≤ ((mCoeff k + bCoeff k) * (theta k r - theta (k+1) r)
            + mCoeff k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r))) * Real.log t
        + ((mCoeffP k + bCoeffP k) * (theta k r - theta (k+1) r)
            + mCoeffP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
              * Real.log (Real.log t)
        + ((mCoeffPP k + bCoeffPP k) * (theta k r - theta (k+1) r)
            + mCoeffPP k * r * (Real.cos (theta k r) - Real.cos (theta (k+1) r)))
        + (theta k r - theta (k+1) r) * arcErr_tight r t := by
  rw [← arc_majorant_integral_tight k r t]
  refine intervalIntegral.integral_mono_ae_restrict (theta_antitone_succ hr0) (hint _ _)
    ((continuous_arcMaj_tight k r t).intervalIntegrable _ _) ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2
    (MeasureTheory.measure_singleton (theta (k+1) r)), hle k] with φ hφ hφle hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk (lt_of_le_of_ne hmem.1 (Ne.symm hφ)) hmem.2
  exact hφle hs1 hs2

/-- **The generic boundary bound on `[θ_{K,r}, π/2]`**, tight version.

### Summary of Proof
As `arc_boundary_bound_gen`: on this arc `σ = 1 - r sin φ` runs over `[1-r, σ_K)`, which by
`Kidx_mem` and `Kidx_sub_one` lies within the single chord interval indexed `K-1`, so one
application of the pointwise bound suffices; `arc_majorant_boundary_integral_tight` then
evaluates the integral.

### Lean Notes
Again this is where the sine form is indispensable: `θ_{K-1,r}` is junk here, since
`1 - σ_{K-1} > r` puts `arcsin`'s argument outside `[-1,1]`.

**`hle` is an *almost-everywhere* domination hypothesis**, as in `arc_piece_bound_gen`; see
there for why.

### References
tex: the boundary term of each `c_{i,r}` display after Equation `\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `Kidx_sub_one`, `arcErr_tight`, `arcMaj_tight`,
`arc_majorant_boundary_integral_tight`, `bCoeff`, `bCoeffP`, `bCoeffPP`,
`continuous_arcMaj_tight`, `mCoeff`, `mCoeffP`, `mCoeffPP`, `sigma`, `sigma_lt_one`,
`sin_theta_eq`, `theta`, `theta_le_pi_div_two`.
**Used by:** `half_arc_bound_tight`. -/
theorem arc_boundary_bound_gen_tight {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj_tight m r t φ) :
    (∫ φ in (theta (Kidx r) r)..(Real.pi/2), F φ)
      ≤ ((mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)) * Real.log t
        + ((mCoeffP (Kidx r - 1) + bCoeffP (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeffP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)) * Real.log (Real.log t)
        + ((mCoeffPP (Kidx r - 1) + bCoeffPP (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
            - mCoeffPP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r))
        + (Real.pi/2 - theta (Kidx r) r) * arcErr_tight r t := by
  have hpi := Real.pi_pos
  have hKmem : 1 - sigma (Kidx r) ≤ r := Kidx_mem hr0 hr1
  have hKsub : r < 1 - sigma (Kidx r - 1) := Kidx_sub_one hr0 hr1
  have hK0 : (0:ℝ) ≤ theta (Kidx r) r := theta_nonneg hr0
  have hKpi : theta (Kidx r) r ≤ Real.pi/2 := theta_le_pi_div_two (Kidx r) r
  rw [← arc_majorant_boundary_integral_tight (Kidx r) r t]
  refine intervalIntegral.integral_mono_ae_restrict hKpi (hint _ _)
    ((continuous_arcMaj_tight (Kidx r - 1) r t).intervalIntegrable _ _) ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2
    (MeasureTheory.measure_singleton (theta (Kidx r) r)), hle (Kidx r - 1)] with φ hφ hφle hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hφ
  have hlt : theta (Kidx r) r < φ := lt_of_le_of_ne hmem.1 (Ne.symm hφ)
  have hub : φ ≤ Real.pi/2 := hmem.2
  have hs1 : (1 - sigma ((Kidx r - 1) + 1)) / r < Real.sin φ := by
    rw [show Kidx r - 1 + 1 = Kidx r by ring, ← sin_theta_eq hr0 hKmem]
    exact Real.strictMonoOn_sin ⟨by linarith, hKpi⟩ ⟨by linarith, hub⟩ hlt
  have hs2 : Real.sin φ ≤ (1 - sigma (Kidx r - 1)) / r := by
    have h1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
    have h2 : (1:ℝ) < (1 - sigma (Kidx r - 1)) / r := by rw [lt_div_iff₀ hr0]; linarith
    linarith
  exact hφle hs1 hs2
/-- **The quarter-circle bound `[0, π/2]`** — the tight counterpart of `half_arc_bound`.

### Summary of Proof
As `half_arc_bound`: decompose the quarter into the chord pieces `[θ_{K+j+1,r}, θ_{K+j,r}]` plus
the boundary piece `[θ_{K,r}, π/2]`, bound each by its affine majorant
(`arc_piece_bound_gen_tight`, `arc_boundary_bound_gen_tight`), and assemble the countable sum
with `integral_le_tsum_arc`. The resulting series are definitionally `c1`, `c2`, `c3`, whose
convergence is `c1_summable`, `c3_summable` and `hasSum_theta_diff`.

### Lean Notes
Differs from `half_arc_bound` only in using the tight majorant `arcMaj_tight`, hence the tight
error `arcErr_tight` in place of `arcErr`.

**`hle` is an *almost-everywhere* domination hypothesis**, as in `arc_piece_bound_gen`; see
there for why.

### References
tex: the regrouping of `∫ F_{1+it,r}` producing the `c_{i,r}` displays after Equation
`\ref{eq:thetak}` (Equation 8), in the proof of Proposition `\ref{prop:jensen-easy}`
(Proposition 8).

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `arcErr_tight`, `arcMaj_tight`,
`arc_boundary_bound_gen_tight`, `arc_piece_bound_gen_tight`, `bCoeffP`, `bCoeffP_eq_one`, `c1`,
`c1_summable`, `c2`, `c3`, `c3_summable`, `hasSum_theta_diff`, `integral_le_tsum_arc`,
`mCoeffP`, `mCoeffP_eq_zero`, `theta`, `theta_nonneg`.
**Used by:** `FcrZeta_outside_integral`, `jensen_easy_lower_quarter_tight`,
`jensen_easy_upper_quarter_tight`. -/
theorem half_arc_bound_tight {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {F : ℝ → ℝ} (hint : ∀ u v : ℝ, IntervalIntegrable F MeasureTheory.volume u v)
    (hle : ∀ m : ℤ, ∀ᵐ φ : ℝ, (1 - sigma (m+1)) / r < Real.sin φ →
      Real.sin φ ≤ (1 - sigma m) / r → F φ ≤ arcMaj_tight m r t φ) :
    (∫ φ in (0:ℝ)..(Real.pi/2), F φ)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
        + (Real.pi/2) * arcErr_tight r t := by
  have hidx : ∀ j : ℕ, 1 - sigma (Kidx r + j) ≤ r := by
    intro j
    have hmono : sigma (Kidx r) ≤ sigma (Kidx r + j) := sigma_strictMono.monotone (by omega)
    linarith [Kidx_mem hr0 hr1]
  -- the four component series
  have hths := hasSum_theta_diff (Kidx r) hr0
  have hc2s : HasSum (fun j : ℕ =>
      (mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
      (theta (Kidx r) r) := by
    have he : (fun j : ℕ =>
        (mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
            * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
          + mCoeffP (Kidx r + j) * r
              * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))
        = fun j : ℕ => theta (Kidx r + j) r - theta (Kidx r + j + 1) r := by
      funext j; rw [mCoeffP_eq_zero, bCoeffP_eq_one]; ring
    rw [he]; exact hths
  have hgsum := (((((c1_summable hr0 hr1).hasSum.mul_right (Real.log t)).add
    (hc2s.mul_right (Real.log (Real.log t)))).add
      (c3_summable hr0).hasSum).add (hths.mul_right (arcErr_tight r t)))
  -- the countable family
  have htail := integral_le_tsum_arc (K := Kidx r) hr0 hint hgsum.summable
    (fun j => arc_piece_bound_gen_tight hr0 (hidx j) hint hle)
  rw [hgsum.tsum_eq] at htail
  -- the boundary piece
  have hbdry := arc_boundary_bound_gen_tight hr0 hr1 hint hle
  calc (∫ φ in (0:ℝ)..(Real.pi/2), F φ)
      = (∫ φ in (0:ℝ)..(theta (Kidx r) r), F φ)
          + (∫ φ in (theta (Kidx r) r)..(Real.pi/2), F φ) :=
        (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
    _ ≤ _ := add_le_add htail hbdry
    _ = c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
          + (Real.pi/2) * arcErr_tight r t := by rw [c1, c2, c3, hc2s.tsum_eq]; ring
set_option maxHeartbeats 300000 in
-- the extra `O(1/(t-1)²)` piece-3 algebra pushes this past the default elaboration budget.
/-- **Tight version of `arcErr_le_six_div`.**

### Summary of Proof
Collapse the two window-conversion pieces of `arcErr_tight` exactly as `arcErr_le_six_div` does,
giving `≤ 5/(3(t-1))` after dropping the `r`-dependence via `t-r > t-1`. The third piece is kept
genuinely quadratic rather than flattened to a further `O(1/t)` term: by the same worst-point
argument as `arc_pointwise_le_maj_sin_tight`'s, the decreasing function
`x ↦ 2/x² + 1158/(8x² log x)` is bounded by its value at the uniform point `t-1`.

### Lean Notes
This is what lets `jensen_easy_tight` reproduce the tex's printed error term exactly, rather than
the crude `3/t` of `jensen_easy` — the quadratic piece survives to the final statement.

### References
tex: the `O^*` term of Proposition `\ref{prop:jensen-easy}` (Proposition 8),
`5/(6(t-1)) + 1/(t-1)² + 579/(8(t-1)²log(t-1))`.

### Dependencies
**Depends on:** `arcErr_tight`.
**Used by:** `jensen_easy_tight`. -/
theorem arcErr_tight_le {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hlt : 2 < Real.log t) :
    arcErr_tight r t
      ≤ 5 / (3 * (t - 1))
          + (2 / (t - 1) ^ 2 + 1158 / (8 * (t - 1) ^ 2 * Real.log (t - 1))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  have ht1 : (0:ℝ) < t - 1 := by linarith
  have ht11 : (1:ℝ) < t - 1 := by linarith
  have hd0 : (0:ℝ) < r / (t - r) := div_pos hr0 htr
  have hd : r / (t - r) ≤ 1 / (t - 1) := by
    rw [div_le_div_iff₀ htr ht1]; nlinarith
  have hinv : 1 / (t - 1) ≤ 1 := by
    rw [div_le_one ht1]; linarith
  have h2 : (r / (t - r)) / (Real.log t - r / (t - r)) ≤ (r / (t - r)) / 1 := by
    apply div_le_div_of_nonneg_left hd0.le (by norm_num)
    linarith
  -- piece 3: `t - r ≥ t - 1 > 1`, and `x ↦ 2/x²+1158/(8x²log x)` is decreasing for `x > 1`.
  have hxy : t - 1 ≤ t - r := by linarith
  have hsq : (t - 1) ^ 2 ≤ (t - r) ^ 2 := by nlinarith [hxy, ht1]
  have hlogTh : (0:ℝ) < Real.log (t - 1) := Real.log_pos ht11
  have hlogle : Real.log (t - 1) ≤ Real.log (t - r) := Real.log_le_log ht1 hxy
  have h3a : 2 / (t - r) ^ 2 ≤ 2 / (t - 1) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity : (0:ℝ) < (t - 1) ^ 2) hsq
  have hle2 : (t - 1) ^ 2 * Real.log (t - 1) ≤ (t - r) ^ 2 * Real.log (t - r) :=
    mul_le_mul hsq hlogle hlogTh.le (by positivity)
  have hd1 : (0:ℝ) < 8 * (t - r) ^ 2 * Real.log (t - r) := by
    have hlogpos : (0:ℝ) < Real.log (t - r) := lt_of_lt_of_le hlogTh hlogle
    exact mul_pos (mul_pos (by norm_num) (pow_pos htr 2)) hlogpos
  have hd2 : (0:ℝ) < 8 * (t - 1) ^ 2 * Real.log (t - 1) := by positivity
  have h3b : 1158 / (8 * (t - r) ^ 2 * Real.log (t - r))
      ≤ 1158 / (8 * (t - 1) ^ 2 * Real.log (t - 1)) := by
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [hle2]
  unfold arcErr_tight
  rw [div_one] at h2
  have e5 : (5:ℝ) / (3 * (t - 1)) = (2/3) * (1/(t-1)) + (1/(t-1)) := by
    field_simp; ring
  rw [e5]
  have hpiece12 : (2/3) * (r / (t - r)) ≤ (2/3) * (1/(t-1)) := by linarith
  linarith [h2, hd, hpiece12, h3a, h3b]
/-- **The lower quarter `θ ∈ [π/2, π]`**, tight version, via `θ = φ + π/2`.

### Summary of Proof
Reparametrise by `φ = θ - π/2` onto `[0, π/2]` and apply `half_arc_bound_tight`, whose sine-form
domination hypothesis is `arc_pointwise_le_maj_sin_tight` and whose integrability is
`intervalIntegrable_log_zeta_circle_shift`.

### Lean Notes
`half_arc_bound_tight`'s domination hypothesis is supplied almost everywhere:
`ae_zeta_arc_ne_zero` (with `b = c = r`) discharges `arc_pointwise_le_maj_sin_tight`'s `hz` off
a null set of `φ`. The reflection hypothesis stops here; nothing above it carries one.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr_tight`, `arc_pointwise_le_maj_sin_tight`, `c1`,
`c2`, `c3`, `half_arc_bound_tight`, `intervalIntegrable_log_zeta_circle_shift`.
**Used by:** `jensen_easy_tight`. -/
theorem jensen_easy_lower_quarter_tight {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hlog : r / (t - r) < Real.log t) :
    (∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
        + (Real.pi/2) * arcErr_tight r t := by
  have hchg : (∫ φ in (0:ℝ)..(Real.pi/2),
      Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ):ℂ) * Complex.I))‖)
      = ∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
    rw [intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := Real.pi/2)
      (fun θ : ℝ => Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) (Real.pi/2),
      zero_add, show (Real.pi/2 + Real.pi/2 : ℝ) = Real.pi by ring]
  rw [← hchg]
  refine half_arc_bound_tight hr0 hr
    (fun u v => intervalIntegrable_log_zeta_circle_shift ((1:ℂ) + (t:ℂ) * Complex.I) r
      (Real.pi/2) u v) ?_
  -- As in `jensen_easy_lower_quarter`: the mirror-point non-vanishing hypothesis fails only on a
  -- null set of `φ`, so the domination is assumed only almost everywhere.
  intro m
  filter_upwards [ae_zeta_arc_ne_zero (b := r) (c := r) hr0.ne' hr0.ne' t] with φ hne h1 h2
  exact arc_pointwise_le_maj_sin_tight hr0 hr ht hlog h1 h2 hne

/-- **The upper quarter `θ ∈ [π, 3π/2]`**, tight version, via `θ = 3π/2 - φ`.

### Summary of Proof
Reparametrise by the reflection `φ = 3π/2 - θ` onto `[0, π/2]` and apply `half_arc_bound_tight`.
The majorant is unchanged because it depends on `φ` only through `sin φ`
(`arcMaj_pi_sub_tight`).

### Lean Notes
The *integrand* is not symmetric about `θ = π` — conjugation moves the centre from `1+it` to
`1-it` — but it does not need to be; only the majorant's symmetry is used.

**The reflected circle runs the other way here**, so the null set to exclude is the one for
`ae_zeta_arc_ne_zero` with `c = -r`; that is where `arc_pointwise_le_maj_sin_tight`'s `hz` is
discharged.

### References
tex: the proof of Proposition `\ref{prop:jensen-easy}` (Proposition 8).

### Dependencies
**Depends on:** `ae_zeta_arc_ne_zero`, `arcErr_tight`, `arcMaj_pi_sub_tight`,
`arc_pointwise_le_maj_sin_tight`, `c1`,
`c2`, `c3`, `half_arc_bound_tight`, `intervalIntegrable_log_zeta_circle_reflect`.
**Used by:** `jensen_easy_tight`. -/
theorem jensen_easy_upper_quarter_tight {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13:ℝ) < t) (hlog : r / (t - r) < Real.log t) :
    (∫ θ in Real.pi..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r
        + (Real.pi/2) * arcErr_tight r t := by
  have hchg : (∫ φ in (0:ℝ)..(Real.pi/2),
      Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp (((3*Real.pi/2 - φ : ℝ):ℂ) * Complex.I))‖)
      = ∫ θ in Real.pi..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
    rw [intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Real.pi/2)
      (fun θ : ℝ => Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) (3*Real.pi/2),
      sub_zero, show (3*Real.pi/2 - Real.pi/2 : ℝ) = Real.pi by ring]
  rw [← hchg]
  refine half_arc_bound_tight hr0 hr
    (fun u v => intervalIntegrable_log_zeta_circle_reflect ((1:ℂ) + (t:ℂ) * Complex.I) r
      (3*Real.pi/2) u v) ?_
  -- The mirror quarter's reflected circle runs the other way, so `c = -r` here.
  intro m
  filter_upwards [ae_zeta_arc_ne_zero (b := r) (c := -r) hr0.ne' (neg_ne_zero.2 hr0.ne') t]
    with φ hne h1 h2
  have hs : Real.sin (Real.pi - φ) = Real.sin φ := Real.sin_pi_sub φ
  have hcs : Real.cos (Real.pi - φ) = -Real.cos φ := Real.cos_pi_sub φ
  have hz : riemannZeta (((r * Real.sin (Real.pi - φ) : ℝ) : ℂ)
      + ((t + r * Real.cos (Real.pi - φ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    rw [hs, hcs, show (t + r * -Real.cos φ : ℝ) = t + -r * Real.cos φ by ring]
    exact hne
  have hkey := arc_pointwise_le_maj_sin_tight (k := m) (r := r) (t := t) (φ := Real.pi - φ)
    hr0 hr ht hlog (by rw [hs]; exact h1) (by rw [hs]; exact h2) hz
  rw [arcMaj_pi_sub_tight] at hkey
  rw [show (3*Real.pi/2 - φ : ℝ) = ((Real.pi - φ) + Real.pi/2 : ℝ) by ring]
  exact hkey

/-- **`C₈(t) = 4/3 + 1/(2 log(t-2)) + 1/(2 log t)`**, the `O(1/t)`-scale error constant used by
the rectangular track.

### Summary of Proof
A definition. The three summands are the leaf error term of Proposition
`\ref{prop:interpolation}` (Proposition 35) evaluated at the worst ordinate on the Jensen circle,
Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36)'s tail, and the cost of converting `log|t+r|` to
`log|t|`.

### Lean Notes
Nothing consumes it.  On the circle track the error is carried by `arcErr` and `arcErr_tight`, and
`jensen_easy_tight` reaches the tex's printed `O(1/t²)` term directly, so this collected form is
never needed.  It is kept because it is the shape the source's own error bookkeeping takes, and it
is the natural place to start if that bookkeeping is ever tightened.

### References
tex: Proposition `\ref{prop:interpolation}` (Proposition 35); Lemma
`\ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** none.
**Used by:** none. -/
noncomputable def C8 (t : ℝ) : ℝ :=
  4 / 3 + 1 / (2 * Real.log (t - 2)) + 1 / (2 * Real.log t)

set_option maxHeartbeats 300000 in
-- the extra `O(1/(t-1)²)` bookkeeping pushes this past the default elaboration budget.
/-- **Proposition `\ref{prop:jensen-easy}` (Proposition 8), tight version** — the one matching
the printed statement exactly.

### Summary of Proof
Identical in structure to `jensen_easy`: bound `log|ζ|` on the circle by the piecewise-linear
majorant, integrate, and regroup the quarter-circle by chord index into the `c_{i,r}` series. The
difference is entirely in the pointwise input.

### Lean Notes
Uses `JensenScaleConstants.zeta_piecewise_bound_tight_simple` — Proposition
`\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)` bound, uniformly
collapsed to the constant `1158` — in place of `jensen_easy`'s `zeta_piecewise_bound` (`O(1/t)`),
via the same proof strategy with `arcErr_tight` for `arcErr` throughout
(`arc_pointwise_le_maj_sin_tight`, `half_arc_bound_tight`,
`jensen_easy_lower_quarter_tight`/`_upper_quarter_tight`, and `arcErr_tight_le` in place of
`arcErr_le_six_div`). The two window-conversion pieces of the error have nothing to do with
Proposition `\ref{prop:interpolation}` (Proposition 35) and are unchanged, so the error is still
`O(1/t)` there; only the dominant pointwise contribution drops a full power of `t`.

**This is the statement matching the current tex exactly.** The hypothesis `13 < t` is the tex's
own `t > 13`, and the error term `5/(6(t-1)) + 1/(t-1)² + 1158/(16(t-1)²log(t-1))` is literally the
tex's `5/(6(t-1)) + 1/(t-1)² + 579/(8(t-1)²log(t-1))`, since `1158/16 = 579/8 = 72.375`. By
contrast `jensen_easy` above needs `t > 10¹²+1` and delivers only the cruder flat `3/t`, so it is
strictly weaker than the printed proposition.

### References
tex: Proposition `\ref{prop:jensen-easy}` (Proposition 8), matched exactly — hypothesis `t > 13`
and error `5/(6(t-1)) + 1/(t-1)² + 579/(8(t-1)²log(t-1))`. Rests on Proposition
`\ref{prop:interpolation}` (Proposition 35)'s tight forms.

### Dependencies
**Depends on:** `arcErr_tight`, `arcErr_tight_le`, `c1`, `c2`, `c3`,
`intervalIntegrable_log_zeta_circle`, `jensen_easy_lower_quarter_tight`,
`jensen_easy_upper_quarter_tight`, `two_lt_log_of_gt_eight`.
**Used by:** `circularregions1_tight`, `rectangularjensen_tight`. -/
theorem jensen_easy_tight {r t : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (ht : (13 : ℝ) < t) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
          Real.log ‖riemannZeta (1 + t * Complex.I + r * Complex.exp (θ * Complex.I))‖
      ≤ c1 r / Real.pi * Real.log t + c2 r / Real.pi * Real.log (Real.log t) + c3 r / Real.pi
        + (5 / (6 * (t - 1))
            + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1)))) := by
  have hpi := Real.pi_pos
  have ht0 : (0:ℝ) < t := by linarith
  have htr : (0:ℝ) < t - r := by linarith
  have hlt : 2 < Real.log t := two_lt_log_of_gt_eight (by linarith)
  have hlog : r / (t - r) < Real.log t := by
    have h1 : r / (t - r) ≤ 1 := by rw [div_le_one htr]; linarith
    linarith
  have hsplit : (∫ θ in (Real.pi/2)..(3*Real.pi/2),
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      = (∫ θ in (Real.pi/2)..Real.pi,
          Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + ∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log_zeta_circle ((1:ℂ) + (t:ℂ) * Complex.I) r _ _)
      (intervalIntegrable_log_zeta_circle ((1:ℂ) + (t:ℂ) * Complex.I) r _ _)).symm
  have hlow := jensen_easy_lower_quarter_tight hr0 hr ht hlog
  have hup := jensen_easy_upper_quarter_tight hr0 hr ht hlog
  have herr := arcErr_tight_le hr0 hr ht hlt
  rw [hsplit]
  have hsum : (∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + (∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ 2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
          + Real.pi * arcErr_tight r t := by linarith
  have hmul : (1 / (2 * Real.pi)) * ((∫ θ in (Real.pi/2)..Real.pi,
        Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
          + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + ∫ θ in Real.pi..(3*Real.pi/2),
            Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I
              + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
      ≤ (1 / (2 * Real.pi)) * (2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
          + Real.pi * arcErr_tight r t) := by
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have hval : (1 / (2 * Real.pi)) * (2 * (c1 r * Real.log t + c2 r * Real.log (Real.log t) + c3 r)
        + Real.pi * arcErr_tight r t)
      = c1 r / Real.pi * Real.log t + c2 r / Real.pi * Real.log (Real.log t) + c3 r / Real.pi
        + arcErr_tight r t / 2 := by
    field_simp
  rw [hval] at hmul
  have hlast : arcErr_tight r t / 2
      ≤ 5 / (6 * (t - 1)) + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1))) := by
    have ht1pos : (0:ℝ) < t - 1 := by linarith
    have ht11pos : (1:ℝ) < t - 1 := by linarith
    have hlogt1pos : (0:ℝ) < Real.log (t - 1) := Real.log_pos ht11pos
    have heq : 5 / (6 * (t - 1)) + (1 / (t - 1) ^ 2 + 1158 / (16 * (t - 1) ^ 2 * Real.log (t - 1)))
        = (5 / (3 * (t - 1))
            + (2 / (t - 1) ^ 2 + 1158 / (8 * (t - 1) ^ 2 * Real.log (t - 1)))) / 2 := by
      field_simp
      ring
    rw [heq]
    linarith [herr]
  linarith

/-- **The elliptic-integral constant `E_{1/2} = ∫_0^{π/2} cos(θ)^{3/2} dθ ≈ 0.874019…`.**

### Summary of Proof
A definition. It has the closed form `Γ(1/4)²/(6√(2π))`, a Beta-function evaluation
(`E_{1/2} = (1/2)B(5/4,1/2)`), which is what `Ehalf_bound` uses to bound it numerically.

### References
tex: Proposition `\ref{prop:Richert}` (Proposition 12), where `E_{1/2}` is introduced and its
value as an elliptic integral justified.

### Dependencies
**Depends on:** none.
**Used by:** `Ctilde1`, `Ctilde1_lt`, `Ehalf_bound`, `circularregions2`,
`integral_abs_cos_rpow_half_arc`, `prop_Richert`. -/
noncomputable def Ehalf : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ (3 / 2 : ℝ)

/-- **`∫_{π/2}^{3π/2} |cos θ|^{3/2} dθ = 2·E_{1/2}`.**

### Summary of Proof
Shift by `π`, using `cos(φ+π) = -cos φ`, to land on `[-π/2, π/2]`. There `|cos|` is even, so the
integral is twice that over `[0, π/2]`, where `cos ≥ 0` lets the absolute value be dropped —
leaving exactly `2·E_{1/2}`.

### Lean Notes
This is the elliptic-integral evaluation behind `prop_Richert`'s constant. The absolute value is
unavoidable in the statement: on `[π/2, 3π/2]` the cosine is negative, and the source's
`|cos θ|^{3/2}` would otherwise be a complex power.

### References
tex: Proposition `\ref{prop:Richert}` (Proposition 12).

### Dependencies
**Depends on:** `Ehalf`.
**Used by:** `prop_Richert`. -/
theorem integral_abs_cos_rpow_half_arc :
    (∫ θ in (Real.pi/2)..(3*Real.pi/2), |Real.cos θ| ^ (3/2 : ℝ)) = 2 * Ehalf := by
  have hshift : (∫ θ in (Real.pi/2)..(3*Real.pi/2), |Real.cos θ| ^ (3/2 : ℝ))
      = ∫ φ in (-(Real.pi/2))..(Real.pi/2), |Real.cos (φ + Real.pi)| ^ (3/2 : ℝ) := by
    rw [intervalIntegral.integral_comp_add_right (fun θ => |Real.cos θ| ^ (3/2 : ℝ)) Real.pi]
    ring_nf
  rw [hshift]
  have hcos : ∀ φ : ℝ, |Real.cos (φ + Real.pi)| ^ (3/2 : ℝ) = |Real.cos φ| ^ (3/2 : ℝ) := by
    intro φ; rw [Real.cos_add_pi, abs_neg]
  simp only [hcos]
  -- even integrand: `∫_{-π/2}^{π/2} = 2∫_0^{π/2}`, and `|cos| = cos` on `[0,π/2]`
  have hcont : Continuous (fun φ : ℝ => |Real.cos φ| ^ (3/2 : ℝ)) :=
    (continuous_abs.comp Real.continuous_cos).rpow_const
      (fun _ => Or.inr (by norm_num))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := -(Real.pi/2)) (b := 0) (c := Real.pi/2)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hrefl : (∫ φ in (-(Real.pi/2))..(0:ℝ), |Real.cos φ| ^ (3/2 : ℝ))
      = ∫ φ in (0:ℝ)..(Real.pi/2), |Real.cos φ| ^ (3/2 : ℝ) := by
    have := intervalIntegral.integral_comp_neg
      (a := (0:ℝ)) (b := Real.pi/2) (f := fun φ : ℝ => |Real.cos φ| ^ (3/2 : ℝ))
    simp only [Real.cos_neg, neg_zero] at this
    rw [← this]
  rw [hrefl, Ehalf]
  have hcc : (∫ φ in (0:ℝ)..(Real.pi/2), |Real.cos φ| ^ (3/2 : ℝ))
      = ∫ φ in (0:ℝ)..(Real.pi/2), (Real.cos φ) ^ (3/2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity)] at hφ
    simp only
    rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩)]
  rw [hcc]; ring


/-- **`e^{2/3} < 2`.**

### Summary of Proof
Since `2/3 < log 2 = 0.6931…`, exponentiating gives `e^{2/3} < 2`.

### Lean Notes
The radius used in `circularregions2` is `r = e^{2/3}α ≤ e^{2/3} = 1.9477…`, so this puts it
inside every `r < T` hypothesis under the mild assumption `2 < T`.

### References
No tex counterpart — arithmetic supporting Theorem `\ref{thm:circularregions2}` (Theorem 18)'s
radius `e^{2/3}α`.

### Dependencies
**Depends on:** none.
**Used by:** `circularregions2`. -/
theorem exp_two_thirds_lt_two : Real.exp (2/3) < 2 := by
  have h : (2:ℝ)/3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  calc Real.exp (2/3) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h
    _ = 2 := Real.exp_log (by norm_num)

/-- **`1 < e^{2/3}`.**

### Summary of Proof
From `Real.add_one_le_exp` at `2/3`: `e^{2/3} ≥ 1 + 2/3 > 1`.

### Lean Notes
Used together with `exp_two_thirds_lt_two` to place the radius `r = e^{2/3}α` of
`circularregions2` inside the hypotheses it must satisfy.

### References
No tex counterpart — arithmetic supporting Theorem `\ref{thm:circularregions2}` (Theorem 18)'s
radius `e^{2/3}α`.

### Dependencies
**Depends on:** none.
**Used by:** `circularregions2`. -/
theorem one_lt_exp_two_thirds : (1:ℝ) < Real.exp (2/3) := by
  have := Real.add_one_le_exp (2/3 : ℝ); linarith

/-- **Proposition `\ref{prop:Richert}` (Proposition 12).** Given a Richert-type bound on
`log|ζ(σ+it)|` for `t` in the window swept by the circle and `1-σ < r`,
`(1/(2π))∫_{π/2}^{3π/2} log|ζ(1+iT+re^{iθ})|dθ ≤ (E_{1/2} B r^{3/2}/π) log|T| +
(1/3) log log|T| + A/2`.

### Summary of Proof
The source states this proposition **without a proof block** — only the value of `E_{1/2}` as an
elliptic integral is justified there — so the argument below is this project's own.

At angle `θ` the circle point has `σ = 1 + r cos θ` (`circle_pt`), so `1 - σ = r|cos θ|` on
`[π/2, 3π/2]`. Feeding that into the Richert-type hypothesis makes the integrand at most
`B(r|cos θ|)^{3/2} log|t| + …`, and integrating `|cos θ|^{3/2}` over the half-circle gives
`2E_{1/2}` (`integral_abs_cos_rpow_half_arc`). Dividing by `2π` produces the displayed
`E_{1/2}Br^{3/2}/π`.

### Lean Notes
**The hypothesis window is `t ∈ [T-r,T+r]`, matching the tex exactly**, and it cannot be
narrowed. The point on the circle is `1 + iT + re^{iθ}`, whose imaginary part `T + r sin θ`
ranges over all of `[T-r, T+r]`; a fixed window such as `[T-1,T+1]` would be unavailable for
`r > 1`, and the only call site, `circularregions2`, has `r = e^{2/3}α` up to
`e^{2/3} ≈ 1.9477`. The hypothesis `0 < r` is the tex's own.

**The degenerate point `θ = π`.** There `1 - σ = r` exactly, so the hypothesis's strict
`1 - σ < r` fails and it applies only on the open arc minus that one point. A single point is
null, so the comparison uses `intervalIntegral.integral_mono_ae_restrict` rather than
`integral_mono_on`. Interval integrability of the integrand is
`MeromorphicOn.intervalIntegrable_log_norm`, `θ ↦ ζ(1+iT+re^{iθ})` being real-meromorphic.

The other two terms of the majorant are constant over an arc of length `π`, so dividing by `2π`
turns them into the displayed `(1/3) log log|T|` and `A/2`.

### References
tex: Proposition `\ref{prop:Richert}` (Proposition 12), where `E_{1/2}` is also introduced.

### Dependencies
**Depends on:** `Ehalf`, `circle_pt`, `integral_abs_cos_rpow_half_arc`,
`meromorphicAt_riemannZeta`.
**Used by:** `circularregions2`. -/
theorem prop_Richert {T r B A : ℝ} (hr : 0 < r)
    (H : ∀ σ t : ℝ, 1 - σ < r → t ∈ Set.Icc (T - r) (T + r) →
      Real.log ‖riemannZeta (σ + t * Complex.I)‖
        < B * (1 - σ) ^ (3 / 2 : ℝ) * Real.log |T| + (2 / 3) * Real.log (Real.log |T|) + A) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
          Real.log ‖riemannZeta (1 + T * Complex.I + r * Complex.exp (θ * Complex.I))‖
      ≤ Ehalf * B * r ^ (3 / 2 : ℝ) / Real.pi * Real.log |T|
        + (1 / 3) * Real.log (Real.log |T|) + A / 2 := by
  have hpi := Real.pi_pos
  have hab : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith
  -- integrand and majorant
  set f : ℝ → ℝ := fun θ =>
    Real.log ‖riemannZeta (1 + (T:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ with hf
  set g : ℝ → ℝ := fun θ => B * (r * |Real.cos θ|) ^ (3 / 2 : ℝ) * Real.log |T|
      + (2 / 3) * Real.log (Real.log |T|) + A with hg
  have hfi : IntervalIntegrable f MeasureTheory.volume (Real.pi/2) (3*Real.pi/2) := by
    have hmero : MeromorphicOn
        (fun θ : ℝ =>
          riemannZeta (1 + (T:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)))
        (Set.uIcc (Real.pi/2) (3*Real.pi/2)) := by
      intro u _
      have hinner : AnalyticAt ℝ
          (fun θ : ℝ => 1 + (T:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) u := by
        apply AnalyticAt.add analyticAt_const
        apply AnalyticAt.mul analyticAt_const
        have h1 : AnalyticAt ℝ (fun θ : ℝ => (θ:ℂ) * Complex.I) u := by
          apply AnalyticAt.mul _ analyticAt_const
          exact Complex.ofRealCLM.analyticAt u
        exact AnalyticAt.comp (g := Complex.exp)
          (analyticAt_cexp (z := ((u:ℂ) * Complex.I))).restrictScalars h1
      exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
    exact hmero.intervalIntegrable_log_norm
  have hgcont : Continuous g := by
    rw [hg]
    apply Continuous.add
    · apply Continuous.add
      · exact ((continuous_const.mul
          (((continuous_const.mul (continuous_abs.comp Real.continuous_cos))).rpow_const
            (fun _ => Or.inr (by norm_num)))).mul continuous_const)
      · exact continuous_const
    · exact continuous_const
  have hgi : IntervalIntegrable g MeasureTheory.volume (Real.pi/2) (3*Real.pi/2) :=
    hgcont.intervalIntegrable _ _
  -- pointwise, off the single point `θ = π` where `1-σ = r` and `H` is unavailable
  have hpt : ∀ θ ∈ Set.Ioo (Real.pi/2) (3*Real.pi/2), θ ≠ Real.pi → f θ ≤ g θ := by
    intro θ hθ hne
    have hcosneg : Real.cos θ < 0 := by
      apply Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1
      linarith [hθ.2, Real.pi_pos]
    have hcosgt : -1 < Real.cos θ := by
      rcases lt_or_eq_of_le (Real.neg_one_le_cos θ) with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp h.symm
        have hpi := Real.pi_pos
        have hk0 : k = 0 := by
          rcases lt_trichotomy k 0 with hlt | heq | hgt
          · have : (k:ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
            nlinarith [hθ.1]
          · exact heq
          · have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hgt
            nlinarith [hθ.2]
        rw [hk0] at hk
        simp at hk
        exact hne hk.symm
    have habs : |Real.cos θ| = -Real.cos θ := abs_of_neg hcosneg
    have hH := H (1 + r * Real.cos θ) (T + r * Real.sin θ)
      (by rw [show (1 : ℝ) - (1 + r * Real.cos θ) = -(r * Real.cos θ) by ring]; nlinarith)
      (by
        constructor
        · nlinarith [Real.neg_one_le_sin θ]
        · nlinarith [Real.sin_le_one θ])
    rw [hf, hg]
    simp only
    rw [circle_pt]
    refine le_of_lt (lt_of_lt_of_le hH (le_of_eq ?_))
    rw [show (1 : ℝ) - (1 + r * Real.cos θ) = r * |Real.cos θ| by rw [habs]; ring]
  -- integral comparison, then evaluate the majorant
  have hmono : (∫ θ in (Real.pi/2)..(3*Real.pi/2), f θ)
      ≤ ∫ θ in (Real.pi/2)..(3*Real.pi/2), g θ := by
    refine intervalIntegral.integral_mono_ae_restrict hab hfi hgi ?_
    have hfin : MeasureTheory.volume
        ({Real.pi/2, Real.pi, 3*Real.pi/2} : Set ℝ) = 0 :=
      (((Set.finite_singleton _).insert _).insert _).measure_zero _
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hfin] with θ hθ hmem
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
    exact hpt θ ⟨lt_of_le_of_ne hmem.1 (Ne.symm hθ.1),
      lt_of_le_of_ne hmem.2 hθ.2.2⟩ hθ.2.1
  -- evaluate the majorant integral
  have hsplit : (∫ θ in (Real.pi/2)..(3*Real.pi/2), g θ)
      = B * r ^ (3/2 : ℝ) * Real.log |T| * (2 * Ehalf)
        + Real.pi * ((2/3) * Real.log (Real.log |T|) + A) := by
    have hgeq : ∀ θ : ℝ, g θ
        = (B * r ^ (3/2 : ℝ) * Real.log |T|) * |Real.cos θ| ^ (3/2 : ℝ)
          + ((2/3) * Real.log (Real.log |T|) + A) := by
      intro θ
      rw [hg]
      simp only
      rw [Real.mul_rpow hr.le (abs_nonneg _)]
      ring
    have hci : IntervalIntegrable (fun θ : ℝ => |Real.cos θ| ^ (3/2 : ℝ))
        MeasureTheory.volume (Real.pi/2) (3*Real.pi/2) :=
      ((continuous_abs.comp Real.continuous_cos).rpow_const
        (fun _ => Or.inr (by norm_num))).intervalIntegrable _ _
    simp only [hgeq]
    rw [intervalIntegral.integral_add (hci.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_abs_cos_rpow_half_arc,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hsplit] at hmono
  have hscale : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hscale.le
  have hfin : (1 / (2 * Real.pi)) * (B * r ^ (3/2 : ℝ) * Real.log |T| * (2 * Ehalf)
      + Real.pi * ((2/3) * Real.log (Real.log |T|) + A))
      = Ehalf * B * r ^ (3/2 : ℝ) / Real.pi * Real.log |T|
        + (1/3) * Real.log (Real.log |T|) + A / 2 := by
    field_simp
    ring
  rw [hfin] at this
  exact this

/-! ### The three elementary `arcsin` integrals needed for `integraloutside_bound_secondary`

`Real.arcsin` is *not* defined via an integral in Mathlib (it is the inverse of the order
isomorphism `Real.sinOrderIso`, see `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse`), so
there is no single unlocking definitional trick here. Instead, all three integrals below are
evaluated by substituting `u = sin θ` (via `intervalIntegral.integral_comp_mul_deriv`, using
`Real.arcsin_sin` to simplify `arcsin (sin θ) = θ` for `θ ∈ [0, π/2]`), reducing each to a
standard integral of `θ`, `sin θ`, `cos θ` — and, for the hardest one, to Mathlib's already-proved
`Real.integral_log_sin_zero_pi_div_two : ∫ x in 0..π/2, log (sin x) = -log 2 * π / 2`. -/

/-- **`∫_0^1 arcsin(u) du = π/2 - 1`.**

### Summary of Proof
Substitute `u = sin θ`, reducing the integral to `∫_0^{π/2} θ cos θ dθ`, then integrate by parts:
`∫ θ cos θ = θ sin θ - ∫ sin θ`, which evaluates to `π/2 - 1`.

### References
No tex counterpart — the source evaluates this and the two integrals below in one line while
deriving `c_{4,r}` in Proposition `\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_mul_arcsin`, `integral_logzeta_arcsin_gt`,
`integraloutside_bound_secondary`, `outside3_lt`. -/
theorem integral_arcsin_zero_one : ∫ u in (0 : ℝ)..1, Real.arcsin u = Real.pi / 2 - 1 := by
  have hsub : (∫ x in (0 : ℝ)..(Real.pi / 2), (Real.arcsin ∘ Real.sin) x * Real.cos x)
      = ∫ u in Real.sin 0..Real.sin (Real.pi / 2), Real.arcsin u :=
    intervalIntegral.integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_sin x)
      Real.continuous_cos.continuousOn Real.continuous_arcsin
  simp only [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  have heq : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      (Real.arcsin ∘ Real.sin) x * Real.cos x = x * Real.cos x := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    have hx1 : -(Real.pi / 2) ≤ x := by linarith [Real.pi_pos, hx.1]
    simp only [Function.comp_apply, Real.arcsin_sin hx1 hx.2]
  rw [intervalIntegral.integral_congr heq]
  have hIBP : ∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.cos x =
      (Real.pi / 2) * Real.sin (Real.pi / 2) - 0 * Real.sin 0 -
        ∫ x in (0 : ℝ)..(Real.pi / 2), 1 * Real.sin x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := id) (u' := fun _ => (1 : ℝ))
      (v := Real.sin) (v' := Real.cos) (fun x _ => hasDerivAt_id x)
      (fun x _ => Real.hasDerivAt_sin x) intervalIntegrable_const
      (Real.continuous_cos.intervalIntegrable _ _)
  rw [hIBP]
  simp [Real.sin_pi_div_two, Real.sin_zero, integral_sin]

/-- **`∫_0^1 u·arcsin(u) du = π/8`.**

### Summary of Proof
Substitute `u = sin θ`, giving `∫_0^{π/2} θ sin θ cos θ dθ = (1/2)∫_0^{π/2} θ sin(2θ) dθ`, then
integrate by parts.

### References
No tex counterpart — evaluated in passing in the source's derivation of `c_{4,r}`, Proposition
`\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `integraloutside_bound_secondary`, `outside3_lt`. -/
theorem integral_mul_arcsin_zero_one :
    ∫ u in (0 : ℝ)..1, u * Real.arcsin u = Real.pi / 8 := by
  have hsub : (∫ x in (0 : ℝ)..(Real.pi / 2),
      (fun u => u * Real.arcsin u) (Real.sin x) * Real.cos x)
      = ∫ u in Real.sin 0..Real.sin (Real.pi / 2), u * Real.arcsin u :=
    intervalIntegral.integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_sin x)
      Real.continuous_cos.continuousOn
      (continuous_id.mul Real.continuous_arcsin)
  simp only [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  have heq : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      (fun u => u * Real.arcsin u) (Real.sin x) * Real.cos x
        = x * (Real.sin x * Real.cos x) := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    have hx1 : -(Real.pi / 2) ≤ x := by linarith [Real.pi_pos, hx.1]
    simp only [Real.arcsin_sin hx1 hx.2]
    ring
  rw [intervalIntegral.integral_congr heq]
  have hv : ∀ x : ℝ, HasDerivAt (fun x => Real.sin x ^ 2 / 2) (Real.sin x * Real.cos x) x := by
    intro x
    have h1 : HasDerivAt (fun x => Real.sin x * Real.sin x)
        (Real.cos x * Real.sin x + Real.sin x * Real.cos x) x :=
      (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x)
    have h2 := h1.div_const 2
    have hfun : (fun x => Real.sin x ^ 2 / 2) = (fun x => Real.sin x * Real.sin x / 2) := by
      funext x; rw [sq]
    rw [hfun]
    have heq2 : (Real.cos x * Real.sin x + Real.sin x * Real.cos x) / 2
        = Real.sin x * Real.cos x := by ring
    rwa [heq2] at h2
  have hIBP : ∫ x in (0 : ℝ)..(Real.pi / 2), x * (Real.sin x * Real.cos x) =
      (Real.pi / 2) * (Real.sin (Real.pi / 2) ^ 2 / 2) - 0 * (Real.sin 0 ^ 2 / 2) -
        ∫ x in (0 : ℝ)..(Real.pi / 2), 1 * (Real.sin x ^ 2 / 2) :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := id) (u' := fun _ => (1 : ℝ))
      (v := fun x => Real.sin x ^ 2 / 2) (v' := fun x => Real.sin x * Real.cos x)
      (fun x _ => hasDerivAt_id x) (fun x _ => hv x) intervalIntegrable_const
      (((Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable _ _)
  rw [hIBP]
  simp only [one_mul, Real.sin_pi_div_two, Real.sin_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_mul, sub_zero]
  rw [intervalIntegral.integral_div, integral_sin_sq]
  simp [Real.sin_pi_div_two, Real.sin_zero, Real.cos_pi_div_two, Real.cos_zero]
  ring

/-- **`∫_0^1 arcsin(u)/u du = (π log 2)/2`**, the classical inverse-sine integral.

### Summary of Proof
Substitute `u = sin θ` to reach `∫_0^{π/2} θ cot θ dθ`, then integrate by parts against
`d/dθ[θ log(sin θ)] = log(sin θ) + θ cot θ`, using Mathlib's
`integral_log_sin_zero_pi_div_two` for the remaining integral.

### Lean Notes
Two endpoint subtleties, neither visible in the source.

The change of variables uses `intervalIntegral.integral_comp_mul_deriv'''`, which needs only
`IntegrableOn`/continuity on the *open* image. That sidesteps the removable singularities at
`u = 0` and `θ = 0` entirely, with no explicit continuous extension.

The boundary limit `θ log(sin θ) → 0` as `θ → 0⁺` is handled by
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`, proved via `θ log θ → 0`,
`Real.mul_le_sin` (Jordan's inequality) for boundedness and integrability, and `sin θ/θ → 1` from
`HasDerivAt.tendsto_slope_zero_right`.

A note on a non-discrepancy: the source's displayed constant for this term in
`integraloutside_bound_secondary` is `(log 2)/2`, which is for the *scaled* term
`(1/π)∫ arcsin(u)/u du` actually appearing there. It is correct as stated — there is no missing
factor of `π` in the source.

### References
tex: the derivation of `c_{4,r}` in Proposition `\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `integraloutside_bound_secondary`. -/
theorem integral_arcsin_div_zero_one :
    ∫ u in (0 : ℝ)..1, Real.arcsin u / u = Real.pi * Real.log 2 / 2 := by
  have hpi := Real.pi_pos
  have huIcc : Set.uIcc (0 : ℝ) (Real.pi / 2) = Set.Icc 0 (Real.pi / 2) :=
    Set.uIcc_of_le (by positivity)
  have harcsin_le : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.arcsin u ≤ Real.pi / 2 * u := by
    intro u hu
    have h1 : Real.sin (Real.arcsin u) = u := Real.sin_arcsin (by linarith [hu.1]) hu.2
    have h2 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu.1
    have h3 : Real.arcsin u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
    have hmulsin := Real.mul_le_sin h2 h3
    rw [h1] at hmulsin
    have hmul2 := mul_le_mul_of_nonneg_left hmulsin (by positivity : (0:ℝ) ≤ Real.pi / 2)
    rw [show Real.pi / 2 * (2 / Real.pi * Real.arcsin u) = Real.arcsin u by field_simp] at hmul2
    linarith [hmul2]
  have hg_bound : ∀ u ∈ Set.Icc (0 : ℝ) 1, |Real.arcsin u / u| ≤ Real.pi / 2 := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · rw [← h0, div_zero, abs_zero]; positivity
    · rw [abs_of_nonneg (div_nonneg (Real.arcsin_nonneg.mpr hu.1) h0.le), div_le_iff₀ h0]
      linarith [harcsin_le u hu]
  have hg1 : MeasureTheory.IntegrableOn (fun u : ℝ => Real.arcsin u / u) (Set.Icc (0 : ℝ) 1) := by
    apply MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      (Real.continuous_arcsin.measurable.div measurable_id).aestronglyMeasurable (Real.pi / 2)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs]
    exact hg_bound u hu
  have hxcot_bound : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |Real.arcsin (Real.sin x) / Real.sin x * Real.cos x| ≤ Real.pi / 2 := by
    intro x hx
    rw [Real.arcsin_sin (by linarith [hx.1]) hx.2]
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rw [← h0, Real.sin_zero, div_zero, zero_mul, abs_zero]; positivity
    · have hsinpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [hx.2])
      have hcos_le : Real.cos x ≤ 1 := Real.cos_le_one x
      have hcos_nonneg : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩
      have hxsin_le : x / Real.sin x ≤ Real.pi / 2 := by
        rw [div_le_iff₀ hsinpos]
        have hmulsin := Real.mul_le_sin h0.le hx.2
        have hmul2 := mul_le_mul_of_nonneg_left hmulsin (by positivity : (0:ℝ) ≤ Real.pi / 2)
        rw [show Real.pi / 2 * (2 / Real.pi * x) = x by field_simp] at hmul2
        linarith [hmul2]
      rw [abs_of_nonneg (by positivity)]
      calc x / Real.sin x * Real.cos x
          ≤ Real.pi / 2 * 1 := mul_le_mul hxsin_le hcos_le hcos_nonneg (by positivity)
        _ = Real.pi / 2 := by ring
  have hg2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.arcsin (Real.sin x) / Real.sin x * Real.cos x)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    apply MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      (((Real.continuous_arcsin.comp Real.continuous_sin).measurable.div
        Real.continuous_sin.measurable).mul Real.continuous_cos.measurable).aestronglyMeasurable
      (Real.pi / 2)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs]
    exact hxcot_bound x hx
  have hg_cont : ContinuousOn (fun u : ℝ => Real.arcsin u / u) (Set.Ioi (0 : ℝ)) := by
    apply ContinuousOn.div Real.continuous_arcsin.continuousOn continuousOn_id
    intro x hx
    exact (Set.mem_Ioi.mp hx).ne'
  have hsub : (∫ x in (0 : ℝ)..(Real.pi / 2),
        ((fun u : ℝ => Real.arcsin u / u) ∘ Real.sin) x * Real.cos x)
      = ∫ u in Real.sin 0..Real.sin (Real.pi / 2), Real.arcsin u / u := by
    apply intervalIntegral.integral_comp_mul_deriv'''
    · exact Real.continuous_sin.continuousOn
    · intro x _; exact (Real.hasDerivAt_sin x).hasDerivWithinAt
    · apply hg_cont.mono
      rw [min_eq_left (by positivity : (0:ℝ) ≤ Real.pi / 2),
        max_eq_right (by positivity : (0:ℝ) ≤ Real.pi / 2)]
      rintro y ⟨x, hx, rfl⟩
      exact Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
    · rw [huIcc]
      apply hg1.mono_set
      rintro y ⟨x, hx, rfl⟩
      simp only [Set.mem_Icc] at hx
      exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2]), Real.sin_le_one x⟩
    · rw [huIcc]; exact hg2
  simp only [Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  have hIBPderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt
      (fun x : ℝ => x * Real.log (Real.sin x))
      (Real.log (Real.sin x) + x * (Real.cos x / Real.sin x)) x := by
    intro x hx
    have hsinpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
    have hnum : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hlog : HasDerivAt (fun y : ℝ => Real.log (Real.sin y)) (Real.cos x / Real.sin x) x :=
      (Real.hasDerivAt_sin x).log hsinpos.ne'
    have hmul := hnum.mul hlog
    have hfun : (fun y : ℝ => y) * (fun y : ℝ => Real.log (Real.sin y))
        = fun y : ℝ => y * Real.log (Real.sin y) := rfl
    rw [hfun] at hmul
    have heq : 1 * Real.log (Real.sin x) + x * (Real.cos x / Real.sin x)
        = Real.log (Real.sin x) + x * (Real.cos x / Real.sin x) := by ring
    rwa [heq] at hmul
  have hxcot_integrableOn : MeasureTheory.IntegrableOn
      (fun x : ℝ => x * (Real.cos x / Real.sin x)) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    apply hg2.congr_fun _ measurableSet_Icc
    intro x hx
    dsimp only
    rw [Real.arcsin_sin (by linarith [hx.1]) hx.2]
    ring
  have hintF' : IntervalIntegrable
      (fun x : ℝ => Real.log (Real.sin x) + x * (Real.cos x / Real.sin x))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    IntervalIntegrable.add intervalIntegrable_log_sin
      (huIcc ▸ hxcot_integrableOn).intervalIntegrable
  have htendsto0 : Filter.Tendsto (fun x : ℝ => x * Real.log (Real.sin x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x * Real.log x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hlim := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
      simp only [Real.rpow_one] at hlim
      simpa [mul_comm] using hlim
    have h2 : Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hd := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
      simp only [zero_add, Real.sin_zero, sub_zero, smul_eq_mul] at hd
      simpa [div_eq_inv_mul] using hd
    have h3 : Filter.Tendsto (fun x : ℝ => Real.log (Real.sin x / x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hlim := h2.log (by norm_num : (1:ℝ) ≠ 0)
      simpa using hlim
    have hid0 : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    have h5 : Filter.Tendsto (fun x : ℝ => x * Real.log (Real.sin x / x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hid0.mul h3
    have h4 : (fun x : ℝ => x * Real.log (Real.sin x)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun x => x * Real.log x + x * Real.log (Real.sin x / x)) := by
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_lt_nhds Real.pi_pos)] with x hx hxpi
      have hxpos : 0 < x := hx
      have hsinpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
      have hlogdiv : Real.log (Real.sin x / x) = Real.log (Real.sin x) - Real.log x :=
        Real.log_div hsinpos.ne' hxpos.ne'
      rw [hlogdiv]; ring
    have hsum := h1.add h5
    simp only [add_zero] at hsum
    exact hsum.congr' h4.symm
  have hcontpt : ContinuousAt (fun x : ℝ => x * Real.log (Real.sin x)) (Real.pi / 2) :=
    continuousAt_id.mul (Real.continuous_sin.continuousAt.log
      (by rw [Real.sin_pi_div_two]; exact one_ne_zero))
  have htendsto1 : Filter.Tendsto (fun x : ℝ => x * Real.log (Real.sin x))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hlim : Filter.Tendsto (fun x : ℝ => x * Real.log (Real.sin x))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (Real.pi / 2 * Real.log (Real.sin (Real.pi / 2)))) :=
      hcontpt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.sin_pi_div_two] using hlim
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by positivity : (0:ℝ) < Real.pi / 2) hIBPderiv hintF' htendsto0 htendsto1
  rw [sub_zero] at hFTC
  have hsplit : ∫ x in (0:ℝ)..(Real.pi / 2),
      (Real.log (Real.sin x) + x * (Real.cos x / Real.sin x))
      = (∫ x in (0:ℝ)..(Real.pi / 2), Real.log (Real.sin x))
        + ∫ x in (0:ℝ)..(Real.pi / 2), x * (Real.cos x / Real.sin x) :=
    intervalIntegral.integral_add intervalIntegrable_log_sin
      (huIcc ▸ hxcot_integrableOn).intervalIntegrable
  rw [hsplit, integral_log_sin_zero_pi_div_two] at hFTC
  have hxcot_eq : (∫ x in (0:ℝ)..(Real.pi / 2), x * (Real.cos x / Real.sin x))
      = ∫ x in (0:ℝ)..(Real.pi / 2), Real.arcsin (Real.sin x) / Real.sin x * Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [huIcc] at hx
    dsimp only
    rw [Real.arcsin_sin (by linarith [hx.1]) hx.2]
    ring
  rw [hxcot_eq] at hFTC
  linarith [hFTC]

/-! ### Convergence of the integral in Proposition `\ref{prop:integraloutside}` (Proposition 15)

The source's proof bounds the circle integral by `(1/π)∫_0^{π/2} log ζ(1+r\cos θ) dθ` "provided
this integral converges, which one can verify that it does (say by an integral comparison test)".
The convergence is a genuine issue: as `θ → π/2` the argument `1 + r\cos θ` approaches `ζ`'s
**pole at `s = 1`**, where `ζ(σ) = O(1/(σ-1))`, so the integrand grows like `-\log(r\cos θ)`.
That is a *logarithmic* singularity, integrable by comparison — which is exactly the content of
Mathlib's `MeromorphicOn.intervalIntegrable_log_norm`, once one knows `ζ` is meromorphic at its
pole. The two lemmas below supply this. -/

/-- **`θ ↦ log|ζ(1 + r cos θ)|` is interval integrable on every interval** — the convergence
deferred in Proposition `\ref{prop:integraloutside}` (Proposition 15).

### Summary of Proof
The composite `θ ↦ ζ(1 + r cos θ)` is real-meromorphic — `meromorphicAt_riemannZeta` composed
with the entire `θ ↦ 1 + r cos θ` — and `log‖·‖` of a real-meromorphic function is always
interval integrable.

### Lean Notes
No constraint on `r` is needed. In particular the result covers `[0, π/2]`, where `θ = π/2` sends
the argument exactly onto `ζ`'s pole at `1`; the logarithmic singularity there is integrable.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15), whose proof defers this
convergence to a remark about an integral comparison test.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `integral_log_zeta_cos_quarter_eq_c4`, `integraloutside_bound`,
`RectangularBounds.logzeta_cos_intervalIntegrable_ofReal`. -/
theorem intervalIntegrable_log_zeta_cos {r a b : ℝ} :
    IntervalIntegrable
      (fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (r : ℂ) * Complex.cos (θ : ℂ))‖)
      MeasureTheory.volume a b := by
  have hmero : MeromorphicOn
      (fun θ : ℝ => riemannZeta ((1 : ℂ) + (r : ℂ) * Complex.cos (θ : ℂ)))
      (Set.uIcc a b) := by
    intro t _
    have hinner : AnalyticAt ℝ (fun θ : ℝ => (1 : ℂ) + (r : ℂ) * Complex.cos (θ : ℂ)) t := by
      apply AnalyticAt.add analyticAt_const
      apply AnalyticAt.mul analyticAt_const
      exact (Complex.analyticAt_cos).restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **`arcsin u ≤ (π/2)·u` on `[0,1]`.**

### Summary of Proof
Concavity of `arcsin` on `[0,1]`, obtained from `Real.mul_le_sin` (Jordan's inequality
`(2/π)θ ≤ sin θ` on `[0, π/2]`) by substituting `θ = arcsin u`.

### Lean Notes
Extracted from the proof of `integral_arcsin_div_zero_one`, where it also supplies the bound
`arcsin u / u ≤ π/2` needed for integrability near `0`. Stated here, ahead of `c4`, because
`c4IntegrandBound_abs_le` below needs it too.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `arcsinAntideriv_le`, `integrableOn_arcsin_div`, `c4IntegrandBound_abs_le`,
`logzeta_cos_boundary_tendsto`. -/
theorem arcsin_le_half_pi_mul {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Real.arcsin u ≤ Real.pi / 2 * u := by
  have h1 : Real.sin (Real.arcsin u) = u := Real.sin_arcsin (by linarith [hu.1]) hu.2
  have h2 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu.1
  have h3 : Real.arcsin u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
  have hmulsin := Real.mul_le_sin h2 h3
  rw [h1] at hmulsin
  have hmul2 := mul_le_mul_of_nonneg_left hmulsin (le_of_lt (by positivity : (0:ℝ) < Real.pi / 2))
  rw [show Real.pi / 2 * (2 / Real.pi * Real.arcsin u) = Real.arcsin u by field_simp] at hmul2
  linarith [hmul2]

/-- **`arcsin (cos θ) = π/2 - θ` on `[0, π]`.**

### Summary of Proof
`cos θ = sin(π/2 - θ)` (`Real.sin_pi_div_two_sub`), and `arcsin (sin y) = y` for
`y ∈ [-π/2, π/2]` (`Real.arcsin_sin`); here `y = π/2 - θ` lies in that range precisely because
`θ ∈ [0, π]`.

### Lean Notes
This is what converts the `(θ - π/2)` antiderivative used in the integration by parts of
`integral_log_zeta_cos_quarter_eq_c4` into the `arcsin u` appearing in `c4`.

### References
No tex counterpart — bookkeeping for the substitution `u = cos θ` in Proposition
`\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_zeta_cos_quarter_eq_c4`, `logzeta_cos_boundary_tendsto`,
`RectangularBounds.phi_cos_integral_quarter`. -/
theorem arcsin_cos_eq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    Real.arcsin (Real.cos θ) = Real.pi / 2 - θ := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

open scoped ComplexOrder in
/-- **The real derivative of `log‖ζ(1+rw)‖` along the segment `w > 0`.**

### Summary of Proof
`log‖ζ(1+rw)‖` is the real part of `Complex.log (ζ(1+rw))` there — `ζ(1+ru)` is a positive real
for `ru > 0`, hence in `Complex.slitPlane` — so differentiating the composite by the chain rule
gives `r · Re(ζ'/ζ(1+ru))`.

### Lean Notes
**A duplicate of `RectangularBounds.logzeta_real_hasDerivAt`, and deliberately so.** That file
imports this one, not conversely, so the statement cannot be reused here and has to be restated.
The proofs are identical.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_log_zeta_cos_quarter_eq_c4`. -/
theorem logzeta_real_hasDerivAt' (r u : ℝ) (hru : 0 < r * u) :
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

/-- **`Re(ζ'/ζ(1+ru))`, the first factor of `c4`'s integrand.**

### Summary of Proof
A definition, written with the real-coerced argument `((1+ru : ℝ) : ℂ)` rather than `c4`'s
`(1 + r*u : ℂ)`; the two agree by `push_cast`, which
`integral_log_zeta_cos_quarter_eq_c4` discharges inline where the two conventions meet.

### References
tex: the integrand of `c_{4,r}` in Proposition `\ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** none.
**Used by:** `c4IntegrandBound_abs_le`, `logDerivZetaRe_arcsin_continuousOn`,
`logDerivZetaRe_arcsin_integrableOn`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`,
`integral_sin_mul_comp_cos`, `integral_log_zeta_cos_quarter_eq_c4`. -/
noncomputable def logDerivZetaRe (r u : ℝ) : ℝ :=
  (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) / riemannZeta ((1 + r * u : ℝ) : ℂ)).re

/-- **A uniform bound for `c4`'s integrand on `[0,1]`.**

### Summary of Proof
A definition: `π/(2r) + (|γ| + |γ²+2γ₁|·r)·(π/2)`, the constant produced by feeding the Laurent
estimate `LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two` — Lemma
`\ref{lemma:logderzetabound}` (Lemma 38) at `N = 1` — and `arcsin u ≤ (π/2)u` into
`|Re(ζ'/ζ(1+ru))·arcsin u|`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `stieltjesConstant1`.
**Used by:** `c4IntegrandBound_nonneg`, `c4IntegrandBound_abs_le`,
`logDerivZetaRe_arcsin_integrableOn`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`. -/
noncomputable def c4IntegrandBound (r : ℝ) : ℝ :=
  Real.pi / (2 * r)
    + (|Real.eulerMascheroniConstant|
        + |Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1| * r) * (Real.pi / 2)

/-- **`c4IntegrandBound r ≥ 0` for `r > 0`.**

### Summary of Proof
`positivity`, after unfolding: every summand is a product of non-negative factors.

### References
No tex counterpart.

### Dependencies
**Depends on:** `c4IntegrandBound`.
**Used by:** `c4IntegrandBound_abs_le`. -/
theorem c4IntegrandBound_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ c4IntegrandBound r := by
  unfold c4IntegrandBound
  have := Real.pi_pos
  positivity

/-- **The pole is cancelled: `|Re(ζ'/ζ(1+ru))·arcsin u| ≤ c4IntegrandBound r` on `[0,1]`.**

### Summary of Proof
At `u = 0` the product is `0` because `arcsin 0 = 0`. For `u > 0`, `Re(ζ'/ζ(1+ru))` is negative
(`Definitions.neg_logDeriv_zeta_re_pos`) and `arcsin u ≥ 0`, so the absolute value is
`(-Re(ζ'/ζ))·arcsin u`; the Laurent estimate `neg_logDeriv_zeta_bound_of_claim_two` (valid for
`ru ≤ 2`; for `ru > 2` antitonicity reduces to `σ = 3`) bounds the
first factor by `1/(ru) - γ + (γ²+2γ₁)ru`. The singular piece `(1/(ru))·arcsin u` is then at most
`π/(2r)` by `arcsin u ≤ (π/2)u` — **this is exactly where the simple pole is cancelled by the
simple zero of `arcsin`** — and the rest is bounded using `arcsin u ≤ π/2` and `u ≤ 1`.

### Lean Notes
**No `r ≤ 2` here, deliberately.** The tex restricts Proposition 15 to `r ≤ 2` in its
**"Moreover"** clause only — formalized as `integraloutside_bound_secondary`. Proposition 15's
*first* claim, which this lemma serves, stays general (`0 < r < t`), so constraining `r` here
would diverge from the source, and the restriction would cascade through
`logDerivZetaRe_arcsin_integrableOn`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`,
`integral_sin_mul_comp_cos` and `integral_log_zeta_cos_quarter_eq_c4` into the whole `c4` chain.

**The Laurent estimate is nevertheless applied only inside `(0,2]`**, via a split on `r*u ≤ 2`.
The estimate is needed solely to cancel the pole against `arcsin`'s zero, and that happens near
`u = 0` — where `r*u` is *small*. Away from the pole no Laurent estimate is required at all:

* `r*u ≤ 2` — the argument below, with `neg_logDeriv_zeta_bound_of_claim_two` invoked in range;
* `r*u > 2` — then `r > 2`, and `Definitions.neg_logDeriv_zeta_re_antitone` brings the value down
  to `σ = 3`, where the same lemma applies **at `z = 2`**, again in range. That gives
  `-Re(ζ'/ζ)(1+ru) ≤ 1/2 - γ + 2K = 0.2979…`, and since `arcsin u ≤ π/2` the product is at most
  `0.2979·π/2`, comfortably below `c4IntegrandBound r ≥ γ·π/2` because `γ > 1/2`
  (`Real.one_half_lt_eulerMascheroniConstant`) and `K·r ≥ 2K` for `r ≥ 2`.

So this lemma keeps its full `0 < r` generality — matching Proposition 15's unrestricted first
claim — while never invoking the Laurent estimate outside Lemma `\ref{lemma:logderzetabound}`
(Lemma 38)'s stated range. The antitonicity input comes from the **Dirichlet series**
(`LSeries_vonMangoldt_eq_…`), not the Laurent expansion, so it needs none of the
`LaurentCertificate` inputs.

### References
tex: the integrand of `c_{4,r}` in Proposition `\ref{prop:integraloutside}` (Proposition 15),
first claim — the one *not* restricted to `r ≤ 2`.

### Dependencies
**Depends on:** `logDerivZetaRe`, `c4IntegrandBound`, `c4IntegrandBound_nonneg`,
`arcsin_le_half_pi_mul`, `neg_logDeriv_zeta_re_pos`, `neg_logDeriv_zeta_re_antitone`,
`neg_one_eighth_lt_stieltjesConstant1`, `stieltjesConstant1`,
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`.
**Used by:** `logDerivZetaRe_arcsin_integrableOn`,
`sin_mul_logDerivZetaRe_arcsin_integrableOn`. -/
theorem c4IntegrandBound_abs_le {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |logDerivZetaRe r u * Real.arcsin u| ≤ c4IntegrandBound r := by
  have hpi := Real.pi_pos
  unfold logDerivZetaRe
  rcases eq_or_lt_of_le hu.1 with heq | hupos
  · rw [← heq]
    simp [c4IntegrandBound_nonneg hr]
  · have hru : 0 < r * u := mul_pos hr hupos
    have hσ : (1:ℝ) < 1 + r * u := by linarith
    have hpos := neg_logDeriv_zeta_re_pos (σ := 1 + r * u) hσ
    simp only [Complex.neg_re] at hpos
    have harc0 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.2 hu.1
    have harcu : Real.arcsin u ≤ Real.pi / 2 * u := arcsin_le_half_pi_mul hu
    have harcpi : Real.arcsin u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
    set γ : ℝ := Real.eulerMascheroniConstant
    set K : ℝ := Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1
    set p : ℝ :=
      (deriv riemannZeta ((1 + r * u : ℝ) : ℂ) / riemannZeta ((1 + r * u : ℝ) : ℂ)).re with hp
    have habs : |p * Real.arcsin u| = (-p) * Real.arcsin u := by
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith [hpos]) harc0)]
      ring
    rw [habs]
    -- **The pole split.** The Laurent estimate is only needed near `u = 0`, where `r*u ≤ 2`;
    -- away from the pole `-ζ'/ζ` is small and antitonicity suffices. So
    -- `neg_logDeriv_zeta_bound_of_claim_two` is never invoked outside its range `(0,2]`.
    rcases le_or_gt (r * u) 2 with hru2 | hru2
    swap
    · -- **Away from the pole:** `r*u > 2`, hence `r > 2`. Antitonicity brings the value down to
      -- `σ = 3`, where the Laurent estimate applies *at `z = 2`* — inside the range.
      have hrgt : (2:ℝ) < r := by nlinarith [hu.2]
      have hanti := neg_logDeriv_zeta_re_antitone (σ₁ := 3) (σ₂ := 1 + r * u)
        (by norm_num) (by linarith)
      have hb2 := neg_logDeriv_zeta_bound_of_claim_two (x := 2) (by norm_num) (by norm_num)
      norm_num at hb2
      simp only [Complex.neg_re] at hanti
      have hγ : (1:ℝ) / 2 < γ := Real.one_half_lt_eulerMascheroniConstant
      -- same two lines as `stieltjes_combo_pos` below, which is declared too late to cite here
      have hKpos : (0:ℝ) < K := by
        have h1 := neg_one_eighth_lt_stieltjesConstant1
        nlinarith [hγ]
      -- `-p ≤ -ζ'/ζ(3) < 1/2 - γ + 2K`
      have hple : -p ≤ 1 / 2 - γ + K * 2 := by
        have : (3:ℝ) = 1 + 2 := by norm_num
        rw [hp]
        push_cast at hanti hb2 ⊢
        linarith [hanti, hb2]
      have hmul : (-p) * Real.arcsin u ≤ (1 / 2 - γ + K * 2) * (Real.pi / 2) :=
        mul_le_mul hple harcpi harc0 (by linarith)
      unfold c4IntegrandBound
      rw [abs_of_pos (by linarith : (0:ℝ) < γ), abs_of_pos hKpos]
      have hKr : K * 2 ≤ K * r := by nlinarith
      have hπr : (0:ℝ) < Real.pi / (2 * r) := by positivity
      nlinarith [hmul, hKr, hπr, hγ]
    have hb := neg_logDeriv_zeta_bound_of_claim_two (x := r * u) hru hru2
    have hstep : (-p) * Real.arcsin u
        ≤ (1 / (r * u)) * Real.arcsin u + (-γ + K * (r * u)) * Real.arcsin u := by
      have h := mul_le_mul_of_nonneg_right hb.le harc0
      calc (-p) * Real.arcsin u
          ≤ (1 / (r * u) - γ + K * (r * u)) * Real.arcsin u := h
        _ = (1 / (r * u)) * Real.arcsin u + (-γ + K * (r * u)) * Real.arcsin u := by ring
    have hA : (1 / (r * u)) * Real.arcsin u ≤ Real.pi / (2 * r) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hru (by positivity)]
      nlinarith [harcu]
    have hB : (-γ + K * (r * u)) * Real.arcsin u ≤ (|γ| + |K| * r) * (Real.pi / 2) := by
      have h1 : (-γ + K * (r * u)) ≤ |γ| + |K| * r := by
        have h2 : -γ ≤ |γ| := neg_le_abs γ
        have hru_le : r * u ≤ r := by nlinarith [hu.2]
        have h3 : K * (r * u) ≤ |K| * r := by
          calc K * (r * u) ≤ |K| * (r * u) := mul_le_mul_of_nonneg_right (le_abs_self K) hru.le
            _ ≤ |K| * r := mul_le_mul_of_nonneg_left hru_le (abs_nonneg K)
        linarith
      have h4 : (0:ℝ) ≤ |γ| + |K| * r := by positivity
      nlinarith [harcpi, harc0, h1, h4]
    unfold c4IntegrandBound
    linarith

/-- **`c4`'s integrand is continuous on `(0,1]`.**

### Summary of Proof
`ζ` and `ζ'` are analytic off `s = 1` (`differentiableOn_riemannZeta.analyticOnNhd` and its
`deriv`), and for `u > 0` the argument `1+ru` avoids `1`; `ζ(1+ru) ≠ 0` there since its real part
exceeds `1`. So the quotient, its real part, and the product with the continuous `arcsin` are all
continuous at each such `u`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaRe`.
**Used by:** `logDerivZetaRe_arcsin_integrableOn`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`,
`integral_sin_mul_comp_cos`. -/
theorem logDerivZetaRe_arcsin_continuousOn {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun u : ℝ => logDerivZetaRe r u * Real.arcsin u) (Set.Ioc (0:ℝ) 1) := by
  have hzanal : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton
  have hdanal : AnalyticOnNhd ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ := hzanal.deriv
  have hmemc : ∀ v : ℝ, 0 < v → (((1 + r * v : ℝ)) : ℂ) ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hc
    have hre := congrArg Complex.re hc
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    nlinarith [mul_pos hr hv]
  intro u hu
  have hcc : ContinuousAt (fun v : ℝ => logDerivZetaRe r v * Real.arcsin v) u := by
    unfold logDerivZetaRe
    apply ContinuousAt.mul _ Real.continuous_arcsin.continuousAt
    apply Complex.continuous_re.continuousAt.comp
    apply ContinuousAt.div
    · exact ContinuousAt.comp (x := u) ((hdanal _ (hmemc u hu.1)).continuousAt)
        (by fun_prop : ContinuousAt (fun v : ℝ => (((1 + r * v : ℝ)) : ℂ)) u)
    · exact ContinuousAt.comp (x := u) ((hzanal _ (hmemc u hu.1)).continuousAt)
        (by fun_prop : ContinuousAt (fun v : ℝ => (((1 + r * v : ℝ)) : ℂ)) u)
    · apply riemannZeta_ne_zero_of_one_lt_re
      simp only [Complex.ofReal_re]
      nlinarith [mul_pos hr hu.1]
  exact hcc.continuousWithinAt

/-- **`c4`'s integrand is integrable on `(0,1]`.**

### Summary of Proof
It is continuous there (`logDerivZetaRe_arcsin_continuousOn`), hence measurable, and bounded by
the constant `c4IntegrandBound r` (`c4IntegrandBound_abs_le`); a measurable function bounded on a
set of finite measure is integrable (`MeasureTheory.IntegrableOn.of_bound`).

### Lean Notes
This is what makes `c4` a well-defined real number rather than a junk value.

### References
tex: `c_{4,r}` in Proposition `\ref{prop:integraloutside}` (Proposition 15), whose proof argues
that the integrand extends analytically across `u = 0` but gives no quantitative bound.

### Dependencies
**Depends on:** `logDerivZetaRe`, `c4IntegrandBound`, `c4IntegrandBound_abs_le`,
`logDerivZetaRe_arcsin_continuousOn`.
**Used by:** `integral_sin_mul_comp_cos`. -/
theorem logDerivZetaRe_arcsin_integrableOn {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun u : ℝ => logDerivZetaRe r u * Real.arcsin u)
      (Set.Ioc (0:ℝ) 1) := by
  apply MeasureTheory.IntegrableOn.of_bound
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    ((logDerivZetaRe_arcsin_continuousOn hr).aestronglyMeasurable measurableSet_Ioc)
    (c4IntegrandBound r)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs]
  exact c4IntegrandBound_abs_le hr ⟨hu.1.le, hu.2⟩

/-- **The `θ`-side integrand `sin θ · Re(ζ'/ζ(1+r cos θ))·arcsin(cos θ)` is integrable on
`[0, π/2]`.**

### Summary of Proof
On `[0, π/2)` the map `θ ↦ cos θ` lands in `(0,1]`, so the composite is continuous there, and it
is bounded by `c4IntegrandBound r` since `|sin θ| ≤ 1` and `cos θ ∈ [0,1]`. Bounded plus
measurable on a finite-measure set gives integrability on `[0, π/2)`, and `[0,π/2)` differs from
`[0,π/2]` by a null set.

### Lean Notes
The single point `θ = π/2` — where `cos θ = 0` and the integrand's continuity fails, `ζ` being at
its pole — is exactly the null set discarded by the `Ico`/`Icc` transfer.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaRe`, `c4IntegrandBound`, `c4IntegrandBound_nonneg`,
`c4IntegrandBound_abs_le`, `logDerivZetaRe_arcsin_continuousOn`.
**Used by:** `integral_sin_mul_comp_cos`, `integral_log_zeta_cos_quarter_eq_c4`. -/
theorem sin_mul_logDerivZetaRe_arcsin_integrableOn {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hpi := Real.pi_pos
  have hQcont : ContinuousOn
      (fun θ : ℝ => logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ))
      (Set.Ico 0 (Real.pi / 2)) := by
    have hmaps : Set.MapsTo Real.cos (Set.Ico 0 (Real.pi / 2)) (Set.Ioc (0:ℝ) 1) := by
      intro θ hθ
      exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩, Real.cos_le_one θ⟩
    exact (logDerivZetaRe_arcsin_continuousOn hr).comp Real.continuous_cos.continuousOn hmaps
  have hIco : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)))
      (Set.Ico 0 (Real.pi / 2)) := by
    apply MeasureTheory.IntegrableOn.of_bound
      (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
      ((Real.continuous_sin.continuousOn.mul hQcont).aestronglyMeasurable measurableSet_Ico)
      (c4IntegrandBound r)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ico] with θ hθ
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have h2 : |logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)| ≤ c4IntegrandBound r := by
      refine c4IntegrandBound_abs_le hr ⟨?_, Real.cos_le_one θ⟩
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩
    nlinarith [abs_nonneg (Real.sin θ),
      abs_nonneg (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)),
      c4IntegrandBound_nonneg hr]
  exact hIco.congr_set_ae (MeasureTheory.Ico_ae_eq_Icc).symm

/-- **The change of variables `u = cos θ`**, converting the `θ`-side integral produced by the
integration by parts into `c4`'s `u`-integral.

### Summary of Proof
`intervalIntegral.integral_deriv_smul_comp'''` with `f = cos`, `f' = -sin`. Its hypotheses are
met: `cos` is continuous with derivative `-sin`; the integrand is continuous on
`cos '' (0, π/2) ⊆ (0,1]`; it is integrable on `cos '' [0, π/2] ⊆ [0,1]`; and the `θ`-side
integrand is integrable by `sin_mul_logDerivZetaRe_arcsin_integrableOn`. Since `cos 0 = 1` and
`cos (π/2) = 0`, the resulting `u`-integral runs `1..0`, and reversing it cancels the sign of
`f' = -sin`.

### Lean Notes
**This substitution is non-singular**, which is the whole point of integrating by parts *before*
substituting: the integrand extends continuously to `u = 0` because `Re(ζ'/ζ(1+ru)) ~ -1/(ru)` is
cancelled by `arcsin u ~ u`. Crucially, `integral_deriv_smul_comp'''` asks for continuity only on
the image of the **open** interval, so the value at the endpoint never has to be addressed.

### References
tex: the substitution `u = cos θ` in the proof of Proposition `\ref{prop:integraloutside}`
(Proposition 15).

### Dependencies
**Depends on:** `logDerivZetaRe`, `logDerivZetaRe_arcsin_continuousOn`,
`logDerivZetaRe_arcsin_integrableOn`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`.
**Used by:** `integral_log_zeta_cos_quarter_eq_c4`. -/
theorem integral_sin_mul_comp_cos {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0:ℝ)..(Real.pi / 2),
        Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)))
      = ∫ u in (0:ℝ)..1, logDerivZetaRe r u * Real.arcsin u := by
  have hpi := Real.pi_pos
  have hle : (0:ℝ) ≤ Real.pi / 2 := by linarith
  have huIcc : Set.uIcc (0:ℝ) (Real.pi / 2) = Set.Icc 0 (Real.pi / 2) := Set.uIcc_of_le hle
  have himg_cl : Real.cos '' Set.uIcc (0:ℝ) (Real.pi / 2) ⊆ Set.Icc (0:ℝ) 1 := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [huIcc] at hθ
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩, Real.cos_le_one θ⟩
  have himg_op : Real.cos '' Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2))
      ⊆ Set.Ioc (0:ℝ) 1 := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [min_eq_left hle, max_eq_right hle] at hθ
    exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩, Real.cos_le_one θ⟩
  have hIcc : MeasureTheory.IntegrableOn
      (fun u : ℝ => logDerivZetaRe r u * Real.arcsin u) (Set.Icc (0:ℝ) 1) :=
    (logDerivZetaRe_arcsin_integrableOn hr).congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc).symm
  have hsub := intervalIntegral.integral_deriv_smul_comp'''
    (f := Real.cos) (f' := fun θ => -Real.sin θ)
    (g := fun u : ℝ => logDerivZetaRe r u * Real.arcsin u) (a := (0:ℝ)) (b := Real.pi / 2)
    (Real.continuous_cos.continuousOn)
    (fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt)
    ((logDerivZetaRe_arcsin_continuousOn hr).mono himg_op)
    (hIcc.mono_set himg_cl)
    (by
      have h := (sin_mul_logDerivZetaRe_arcsin_integrableOn hr).neg
      rw [huIcc]
      refine h.congr_fun ?_ measurableSet_Icc
      intro θ _
      simp only [Function.comp, smul_eq_mul, Pi.neg_apply]
      ring)
  rw [Real.cos_zero, Real.cos_pi_div_two] at hsub
  simp only [Function.comp, smul_eq_mul] at hsub
  rw [intervalIntegral.integral_symm (0:ℝ) 1] at hsub
  have hneg : (∫ θ in (0:ℝ)..(Real.pi / 2),
      -Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)))
      = -∫ θ in (0:ℝ)..(Real.pi / 2),
        Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun θ _ => by ring)
  rw [hneg] at hsub
  linarith [hsub]

/-- **`x·log‖ζ(1+x)‖ → 0` as `x → 0⁺`: `ζ`'s pole at `1` is only logarithmic.**

### Summary of Proof
Mathlib's `tendsto_riemannZeta_sub_one_div` gives `ζ(1+x) - 1/x → γ`. Multiplying by `x → 0`
gives `x·ζ(1+x) - 1 → 0`, i.e. `x·ζ(1+x) → 1`; taking norms and logs, `log(x‖ζ(1+x)‖) → 0`.
Since `x > 0`, `log(x‖ζ(1+x)‖) = log x + log‖ζ(1+x)‖`, so
`x·log‖ζ(1+x)‖ = x·log(x‖ζ(1+x)‖) - x·log x`, and both terms vanish — the second by
`Real.continuous_mul_log`, which encodes `x log x → 0`.

### Lean Notes
This is the quantitative heart of the whole evaluation: it is what makes the boundary term of the
integration by parts vanish at the singular endpoint. It is the same Mathlib entry point that
`Background.LogDerivZetaLaurent.logDerivZetaCoeff_zero` uses to prove `a₀ = γ`.

### References
No tex counterpart — the tex asserts the boundary term vanishes without argument.

### Dependencies
**Depends on:** none.
**Used by:** `logzeta_cos_boundary_tendsto`. -/
theorem x_mul_log_zeta_tendsto :
    Filter.Tendsto (fun x : ℝ => x * Real.log ‖riemannZeta ((1 + x : ℝ) : ℂ)‖)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
  have hxr : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hcont : Continuous (fun x : ℝ => ((1 + x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
  have hmap : Filter.Tendsto (fun x : ℝ => ((1 + x : ℝ) : ℂ))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (hcont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      have hx0 : (x : ℂ) = 0 := by push_cast at hcon ⊢; linear_combination hcon
      exact absurd (by exact_mod_cast hx0) (ne_of_gt hx)
  have hz := tendsto_riemannZeta_sub_one_div.comp hmap
  have hsub : ∀ x : ℝ, ((1 + x : ℝ) : ℂ) - 1 = (x : ℂ) := by intro x; push_cast; ring
  simp only [Function.comp_def, hsub] at hz
  have hx0C : Filter.Tendsto (fun x : ℝ => ((x : ℝ) : ℂ))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have hprod := hx0C.mul hz
  simp only [zero_mul] at hprod
  have hev : (fun x : ℝ => (x : ℂ) * (riemannZeta ((1 + x : ℝ) : ℂ) - 1 / (x : ℂ)))
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))]
        fun x : ℝ => (x : ℂ) * riemannZeta ((1 + x : ℝ) : ℂ) - 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    field_simp
  rw [Filter.tendsto_congr' hev] at hprod
  have hone : Filter.Tendsto (fun x : ℝ => (x : ℂ) * riemannZeta ((1 + x : ℝ) : ℂ))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 1) := by
    have h := hprod.add_const (1:ℂ)
    simpa using h
  have hnorm : Filter.Tendsto (fun x : ℝ => x * ‖riemannZeta ((1 + x : ℝ) : ℂ)‖)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 1) := by
    have h := hone.norm
    simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [abs_of_pos hx]
  have hlog : Filter.Tendsto
      (fun x : ℝ => Real.log (x * ‖riemannZeta ((1 + x : ℝ) : ℂ)‖))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hnorm
    simpa [Real.log_one, Function.comp_def] using h
  have hxlogx : Filter.Tendsto (fun x : ℝ => x * Real.log x)
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds 0) := by
    have h := (Real.continuous_mul_log.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have hsplit : (fun x : ℝ => x * Real.log ‖riemannZeta ((1 + x : ℝ) : ℂ)‖)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))] fun x : ℝ =>
        x * Real.log (x * ‖riemannZeta ((1 + x : ℝ) : ℂ)‖) - x * Real.log x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) < x := hx
    have h1 : (1:ℝ) < ((1 + x : ℝ) : ℂ).re := by simp; linarith
    have hzpos : 0 < ‖riemannZeta ((1 + x : ℝ) : ℂ)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re h1)
    rw [Real.log_mul (ne_of_gt hx') (ne_of_gt hzpos)]
    ring
  rw [Filter.tendsto_congr' hsplit]
  have hA := hxr.mul hlog
  simp only [mul_zero] at hA
  have h := hA.sub hxlogx
  simpa using h

/-- **The boundary term of the integration by parts vanishes at the singular endpoint.**

### Summary of Proof
For `θ` just below `π/2`, `arcsin (cos θ) = π/2 - θ` and `arcsin (cos θ) ≤ (π/2)cos θ`, so
`|log‖ζ(1+r cos θ)‖·(θ - π/2)| ≤ (π/(2r))·|r cos θ · log‖ζ(1+r cos θ)‖|`. The right-hand side is
`x·log‖ζ(1+x)‖` at `x = r cos θ → 0⁺`, which tends to `0` by `x_mul_log_zeta_tendsto`, so the
squeeze theorem applies.

### Lean Notes
This is the endpoint `integral_eq_sub_of_hasDerivAt_of_tendsto` needs as a `nhdsWithin` limit,
and the reason the antiderivative-of-`1` is taken to be `θ - π/2` rather than `θ`: only a factor
vanishing at `π/2` can kill the pole.

### References
tex: the boundary term in the proof of Proposition `\ref{prop:integraloutside}` (Proposition 15),
which the source does not justify.

### Dependencies
**Depends on:** `x_mul_log_zeta_tendsto`, `arcsin_cos_eq`, `arcsin_le_half_pi_mul`.
**Used by:** `integral_log_zeta_cos_quarter_eq_c4`. -/
theorem logzeta_cos_boundary_tendsto {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto
      (fun θ : ℝ => Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖ * (θ - Real.pi / 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi := Real.pi_pos
  have hIoo : Set.Ioo 0 (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    Ioo_mem_nhdsLT (by linarith)
  have hmapθ : Filter.Tendsto (fun θ : ℝ => r * Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun θ : ℝ => r * Real.cos θ) := by fun_prop
      have h := (hc.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
      simpa using h
    · filter_upwards [hIoo] with θ hθ
      exact mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have hcomp := x_mul_log_zeta_tendsto.comp hmapθ
  simp only [Function.comp_def] at hcomp
  refine squeeze_zero_norm' ?_ (?_ : Filter.Tendsto
      (fun θ : ℝ => (Real.pi / (2 * r)) *
        |r * Real.cos θ * Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
  · filter_upwards [hIoo] with θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have harc : Real.arcsin (Real.cos θ) = Real.pi / 2 - θ :=
      arcsin_cos_eq hθ.1.le (by linarith [hθ.2])
    have hle : Real.arcsin (Real.cos θ) ≤ Real.pi / 2 * Real.cos θ :=
      arcsin_le_half_pi_mul ⟨hcos.le, Real.cos_le_one θ⟩
    set L : ℝ := Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖ with hL
    have habs : |θ - Real.pi / 2| = Real.pi / 2 - θ := by
      rw [abs_of_nonpos (by linarith [hθ.2])]; ring
    have hkey : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by rw [← harc]; exact hle
    have hRHS : Real.pi / (2 * r) * |r * Real.cos θ * L| = Real.pi / 2 * Real.cos θ * |L| := by
      rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hcos]
      field_simp
    rw [Real.norm_eq_abs, abs_mul, habs, hRHS]
    calc |L| * (Real.pi / 2 - θ)
        ≤ |L| * (Real.pi / 2 * Real.cos θ) := mul_le_mul_of_nonneg_left hkey (abs_nonneg L)
      _ = Real.pi / 2 * Real.cos θ * |L| := by ring
  · have h := hcomp.abs
    simp only [abs_zero] at h
    have h2 := h.const_mul (Real.pi / (2 * r))
    simpa using h2

/-- **`c_{4,r} = (1/2) log ζ(1+r) - (r/π) ∫_0^1 (ζ'/ζ)(1+ru) arcsin(u) du`.**

### Summary of Proof
A definition, transcribing Proposition `\ref{prop:integraloutside}` (Proposition 15). The two
terms are the boundary contribution and the remaining integral produced by integrating
`(1/π)∫_0^1 log ζ(1+ru)/√(1-u²) du` by parts against `arcsin`.

### Lean Notes
It is the constant bounding the half of the Jensen circle *inside* the critical strip, the
complement of the half that `jensen_easy` handles. Theorem `\ref{thm:circularregions1}`
(Theorem 16)'s constant `C_{3,α,r}` contains `c_{4,r}/log(r/α)`.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15); sample values in Table
`\ref{tab:crvalues}` (Table 2).

**Independent numeric check.** `Code/indep_mpmath_tables_spotcheck.py` evaluates this definition
by plain mpmath quadrature (the integrand tends to `-1/r` at `u = 0`, handled via the Laurent
form below `u = 10⁻²⁰`) and reproduces Table 2's `c_{4,1/2} = 0.7795712` to 7 digits, confirming
the Sage ball value.

### Dependencies
**Depends on:** none.
**Used by:** `A6`, `C3`, `Ctilde3`, `FcrZeta_integral_le`,
`c4_lt_of_le_exp_two_thirds`, `circularregions1`, `circularregions1_tight`, `circularregions2`,
`integral_log_zeta_real_axis_eq_c4`, `integraloutside_bound`, `integraloutside_bound_secondary`,
`Ctilde3_lt_of_le_one`, `ConstantSigns.c4_nonneg`. -/
noncomputable def c4 (r : ℝ) : ℝ :=
  (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖
    - (r / Real.pi) *
        ∫ u in (0 : ℝ)..1,
          (deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re * Real.arcsin u

/-- **The closed-form evaluation underlying Proposition `\ref{prop:integraloutside}`
(Proposition 15):** `∫_0^{π/2} log‖ζ(1 + r cos θ)‖ dθ = π · c_{4,r}`.

### Summary of Proof
The source's own chain, in two moves.

*Substitute `u = cos θ`.* With `du = -sin θ dθ` and `sin θ = √(1-u²)` on `[0,π/2]`,
`∫_0^{π/2} log ζ(1+r cos θ) dθ = ∫_0^1 log ζ(1+ru)/√(1-u²) du`.

*Integrate by parts against `arcsin' u = 1/√(1-u²)`.* Taking `arcsin` as the antiderivative,
`∫_0^1 log ζ(1+ru) · arcsin'(u) du = [log ζ(1+ru)·arcsin u]_0^1 - r∫_0^1 (ζ'/ζ)(1+ru) arcsin u du`.
The boundary term at `1` is `log ζ(1+r)·(π/2)`; at `0` it **vanishes**, because `arcsin` has a
simple zero there which cancels the simple pole of `log ζ` — that cancellation is the whole
delicacy of the argument. Dividing by `π` gives exactly `c_{4,r}`.

### Lean Notes
**Integrated by parts in `θ` first, substituting `u = cos θ` afterwards** — the reverse of the
order the source uses. That order leaves only ONE singular endpoint instead of two, and never
requires writing the unbounded `1/√(1-u²)` at all.

The antiderivative-of-`1` is taken to be `θ - π/2` rather than `θ`, because it *vanishes at the
singular end*. With `g θ := log‖ζ(1+r cos θ)‖` and `P θ := g θ · (θ - π/2)`,

    ∫_0^{π/2} [g'(θ)(θ-π/2) + g θ] dθ = lim_{θ→π/2⁻} P - lim_{θ→0⁺} P
                                       = 0 - (-(π/2)·log‖ζ(1+r)‖).

The model followed is `RectangularBounds.integral_log_mul_arcsin`, which has exactly this shape
(a log singularity at an endpoint, against `arcsin`). Both use
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`, which **wants `HasDerivAt` only on
the open interval and takes both endpoint values as `nhdsWithin` limits** — so no `[ε, 1-ε]`
exhaustion and no splitting at `1/2` was needed; that lemma absorbs the improperness.

The four ingredients, each proved separately above:
1. `logzeta_real_hasDerivAt'` chained with `HasDerivAt cos (-sin θ)` gives `hderiv` on
   `Ioo 0 (π/2)`; its hypothesis `0 < r·cos θ` holds throughout.
2. `sin_mul_logDerivZetaRe_arcsin_integrableOn` gives integrability of the derivative.
3. `logzeta_cos_boundary_tendsto` kills the boundary term at `π/2` — the crux, which reduces to
   Mathlib's `tendsto_riemannZeta_sub_one_div` via `x_mul_log_zeta_tendsto`. That is the same
   entry point `Background.LogDerivZetaLaurent.logDerivZetaCoeff_zero` uses for `a₀ = γ`.
4. `integral_sin_mul_comp_cos` performs the (non-singular) substitution, using
   `arcsin (cos θ) = π/2 - θ`.

Coercion bookkeeping: `logDerivZetaRe` writes the argument as `((1+ru : ℝ) : ℂ)` whereas `c4`
writes `(1 + r*u : ℂ)`; the two agree by `push_cast`, reconciled at the end of the proof.

**This single lemma carries the analytic content shared by its two consumers.**
`integraloutside_bound` below and `Littlewood.ZetaCircleFcr.integral_log_zeta_real_axis_eq_c4`
are the same piece of real analysis, and both are proved from here, so the work is stated once.
It lives in this file, rather than in `ZetaCircleFcr`, because `ZetaCircleFcr` imports this file
and not conversely.

No upper bound on `r` is needed: `c4`'s integrand is bounded near `u = 0` for every `r > 0`
(there `(ζ'/ζ)(1+ru) ~ -1/(ru)` against `arcsin u ~ u`), and the argument `1+r` is off the pole
for every `r > 0`.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15), the displayed evaluation in its
proof.

### Dependencies
**Depends on:** `c4`, `arcsin_cos_eq`, `integral_sin_mul_comp_cos`,
`intervalIntegrable_log_zeta_cos`, `logDerivZetaRe`, `logzeta_cos_boundary_tendsto`,
`logzeta_real_hasDerivAt'`, `sin_mul_logDerivZetaRe_arcsin_integrableOn`.
**Used by:** `integraloutside_bound`,
`Littlewood.ZetaCircleFcr.integral_log_zeta_real_axis_eq_c4`. -/
theorem integral_log_zeta_cos_quarter_eq_c4 {r : ℝ} (hr0 : 0 < r) :
    (∫ θ in (0:ℝ)..(Real.pi / 2),
        Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖)
      = Real.pi * c4 r := by
  have hpi := Real.pi_pos
  have hhalf : (0:ℝ) < Real.pi / 2 := by linarith
  set g : ℝ → ℝ := fun θ => Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖ with hg
  -- (1) `P θ = g θ · (θ - π/2)` is differentiable on the open interval, with derivative
  -- `r · sin θ · Re(ζ'/ζ(1+r cos θ)) · arcsin(cos θ) + g θ` after `arcsin_cos_eq`.
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => g θ * (θ - Real.pi / 2))
        (r * (Real.sin θ *
          (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ))) + g θ) θ := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have h1 := logzeta_real_hasDerivAt' r (Real.cos θ) (mul_pos hr0 hcos)
    have h2 := h1.comp θ (Real.hasDerivAt_cos θ)
    have h3 := (hasDerivAt_id θ).sub_const (Real.pi / 2)
    have h4 := h2.mul h3
    refine h4.congr_deriv ?_
    have harc : Real.arcsin (Real.cos θ) = Real.pi / 2 - θ :=
      arcsin_cos_eq hθ.1.le (by linarith [hθ.2])
    rw [harc, hg]
    unfold logDerivZetaRe
    simp only [Function.comp_apply, id_eq]
    ring
  -- (2) both summands of the derivative are integrable
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 (Real.pi / 2) := by
    have hfun : g = fun θ : ℝ => Real.log ‖riemannZeta ((1:ℂ) + (r:ℂ) * Complex.cos (θ:ℂ))‖ := by
      funext θ; rw [hg]; norm_num
    rw [hfun]; exact intervalIntegrable_log_zeta_cos
  have hsq : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ)))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hhalf.le]
    exact sin_mul_logDerivZetaRe_arcsin_integrableOn hr0
  have hint : IntervalIntegrable
      (fun θ : ℝ =>
        r * (Real.sin θ * (logDerivZetaRe r (Real.cos θ) * Real.arcsin (Real.cos θ))) + g θ)
      MeasureTheory.volume 0 (Real.pi / 2) := (hsq.const_mul r).add hgint
  -- (3) the two endpoint limits: `P` is continuous at `0`, and vanishes at `π/2`
  have hgcont0 : ContinuousAt g 0 := by
    have hne : (((1 + r * Real.cos 0 : ℝ)) : ℂ) ≠ (1:ℂ) := by
      simp only [Real.cos_zero, mul_one]
      intro hc
      have hre := congrArg Complex.re hc
      simp only [Complex.ofReal_re, Complex.one_re] at hre
      linarith
    have hzc : ContinuousAt riemannZeta (((1 + r * Real.cos 0 : ℝ)) : ℂ) :=
      (differentiableAt_riemannZeta hne).continuousAt
    have hzero : riemannZeta (((1 + r * Real.cos 0 : ℝ)) : ℂ) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_lt_re
      simp only [Real.cos_zero, mul_one, Complex.ofReal_re]
      linarith
    rw [hg]
    have hc1 : ContinuousAt (fun θ : ℝ => riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)) 0 :=
      ContinuousAt.comp (x := 0) hzc
        (by fun_prop : ContinuousAt (fun θ : ℝ => (((1 + r * Real.cos θ : ℝ)) : ℂ)) 0)
    exact (hc1.norm).log (norm_ne_zero_iff.mpr hzero)
  have ha : Filter.Tendsto (fun θ : ℝ => g θ * (θ - Real.pi / 2))
      (nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ))) (nhds (g 0 * (0 - Real.pi / 2))) := by
    have hsub : ContinuousAt (fun θ : ℝ => θ - Real.pi / 2) 0 := by fun_prop
    have h : ContinuousAt (fun θ : ℝ => g θ * (θ - Real.pi / 2)) 0 := hgcont0.mul hsub
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Filter.Tendsto (fun θ : ℝ => g θ * (θ - Real.pi / 2))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    logzeta_cos_boundary_tendsto hr0
  -- (4) integrate by parts, (5) split the integral and substitute `u = cos θ`
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hhalf hderiv hint ha hb
  rw [intervalIntegral.integral_add (hsq.const_mul r) hgint,
    intervalIntegral.integral_const_mul, integral_sin_mul_comp_cos hr0] at heq
  -- (6) match `c4`'s coercion conventions
  have hg0 : g 0 = Real.log ‖riemannZeta (1 + r : ℂ)‖ := by
    rw [hg]; simp only [Real.cos_zero, mul_one]; norm_num
  have hphi : ∀ u : ℝ, logDerivZetaRe r u
      = (deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re := by
    intro u; unfold logDerivZetaRe; norm_num
  simp only [hphi] at heq
  rw [hg0] at heq
  unfold c4
  field_simp at heq ⊢
  linarith [heq]

/-- **Proposition `\ref{prop:integraloutside}` (Proposition 15)**, main bound: for `0 < r < t`,
`t > 2`, `(1/(2π))∫_{-π/2}^{π/2} log|ζ(1+it+re^{iθ})|dθ ≤ c_{4,r}`.

### Summary of Proof
For `θ ∈ (-π/2,π/2)`, `log|ζ(1+it+re^{iθ})| < log(ζ(1+r cos θ))` by monotonicity of `ζ` on the
real axis, so the integral is `< (1/π)∫_0^{π/2} log(ζ(1+r cos θ)) dθ`. Substituting `u = cos θ`
gives `(1/π)∫_0^1 log(ζ(1+ru))/√(1-u²) du`. Integrating by parts — using that `arcsin` has a
simple zero at `0` cancelling the simple pole of `ζ'/ζ` there, so the boundary terms combine to
`(1/2)log ζ(1+r)` and the remaining integral is exactly `c4 r`'s — gives the claim, with
convergence following from continuity of `u ↦ (ζ'/ζ)(1+ru)·arcsin(u)` on `[0,1]`.

### Lean Notes
The statement matches the tex's, `≤` included. The pointwise step is `‖ζ(s)‖ ≤ ζ(Re s)`
(`Definitions.zeta_norm_le_zeta_re`), a Dirichlet-series domination and hence genuinely `≤`,
where the source writes `<`. Strictness is true — `∑ n^{-s}` has no cancellation for `Im s ≠ 0`
by linear independence of `{log p}` over `ℚ` — but needs a separate argument the source does not
give, the same pattern as `RectangularBounds.outside2`/`outside3` and
`LittlewoodMethod.littlewood_outerlog`. Every downstream use of `c4` needs only `≤`.

**`_ht` and `_hr` are not used.** The bound holds for every `t`: the pointwise step only needs
`Re(1+it+re^{iθ}) = 1 + r cos θ > 1`, which follows from `0 < r` and `cos θ > 0` alone, and the
`c4 r` it is compared against does not involve `t`. Both hypotheses are kept for signature
compatibility with the tex's Proposition 15 and with this file's callers, and marked unused.

The closed-form evaluation of the quarter-circle integral is factored out as
`integral_log_zeta_cos_quarter_eq_c4`, stated and documented just above `c4`. What is proved here
is the reduction to it: the pointwise domination, integrated via
`intervalIntegral.integral_mono_on_of_le_Ioo` (which wants the bound only on the *open* interval,
exactly what the domination supplies; the closed-interval version would fail at `θ = ±π/2`, where
the comparison function hits `ζ`'s pole), then the evenness of `cos` folding `[-π/2, π/2]` onto
twice `[0, π/2]`.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15), main bound; `c_{4,r}` is defined
in the same proposition.

### Dependencies
**Depends on:** `c4`, `circle_pt`, `integral_log_zeta_cos_quarter_eq_c4`,
`intervalIntegrable_log_zeta_circle`, `intervalIntegrable_log_zeta_cos`, `log_zeta_norm_pos`,
`zeta_norm_le_zeta_re`.
**Used by:** `circularregions1`, `circularregions1_tight`, `circularregions2`. -/
theorem integraloutside_bound {t r : ℝ} (hr0 : 0 < r) (_ht : 2 < t) (_hr : r < t) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
          Real.log ‖riemannZeta (1 + t * Complex.I + r * Complex.exp (θ * Complex.I))‖
      ≤ c4 r := by
  have hpi := Real.pi_pos
  have hab : -Real.pi / 2 ≤ Real.pi / 2 := by linarith
  -- **Step 1: the pointwise Dirichlet-domination step.**
  -- At `θ` the point is `(1 + r cos θ) + i(t + r sin θ)` (`circle_pt`), whose real part exceeds
  -- `1` for `θ ∈ (-π/2, π/2)`, so `zeta_norm_le_zeta_re` gives
  -- `‖ζ(1+it+re^{iθ})‖ ≤ ‖ζ(1 + r cos θ)‖` and hence the same for the logs.
  have hstep1 : ∀ θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
      Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖
        ≤ Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖ := by
    intro θ hθ
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have hre : (1:ℝ) < (1 + (t:ℂ) * Complex.I
        + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)).re := by
      rw [circle_pt]
      simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.cos_ofReal_im, mul_zero, sub_zero, Complex.sin_ofReal_im,
        Complex.I_re, Complex.add_im, Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one,
        sub_self, lt_add_iff_pos_right]
      positivity
    have hz := zeta_norm_le_zeta_re hre
    have hrw : ((1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)).re : ℂ)
        = ((1 + r * Real.cos θ : ℝ) : ℂ) := by
      rw [circle_pt]; simp
    rw [hrw] at hz
    rcases eq_or_lt_of_le (norm_nonneg
      (riemannZeta (1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)))) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact (log_zeta_norm_pos (σ := 1 + r * Real.cos θ) (by nlinarith)).le
    · exact Real.log_le_log h0 hz
  -- **Step 2: integrate the pointwise bound, fold by symmetry, and evaluate.**
  -- The `cos`-integrand is even, so the symmetric interval contributes twice the quarter, and
  -- `integral_log_zeta_cos_quarter_eq_c4` turns that quarter into `π · c4 r`.
  set F : ℝ → ℝ := fun θ => Real.log ‖riemannZeta (((1 + r * Real.cos θ : ℝ)) : ℂ)‖ with hF
  have hFcos : F = fun θ : ℝ => Real.log ‖riemannZeta ((1:ℂ) + (r:ℂ) * Complex.cos (θ:ℂ))‖ := by
    funext θ; rw [hF]; norm_num
  have hRint : ∀ a b : ℝ, IntervalIntegrable F MeasureTheory.volume a b := by
    intro a b; rw [hFcos]; exact intervalIntegrable_log_zeta_cos
  have hLint := intervalIntegrable_log_zeta_circle ((1:ℂ) + (t:ℂ) * Complex.I) r
    (-Real.pi / 2) (Real.pi / 2)
  -- integrate Step 1's pointwise bound (which holds on the open interval, all that is needed)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab hLint (hRint _ _) hstep1
  -- evenness of `cos` folds `[-π/2, π/2]` onto twice `[0, π/2]`
  have heven : ∀ θ : ℝ, F (-θ) = F θ := by intro θ; rw [hF]; norm_num
  have hhalf : (∫ θ in (-Real.pi / 2)..(0:ℝ), F θ) = ∫ θ in (0:ℝ)..(Real.pi / 2), F θ := by
    have hneg : (-Real.pi / 2 : ℝ) = -(Real.pi / 2) := by ring
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := Real.pi / 2) (f := F)
    rw [neg_zero] at h
    rw [hneg, ← h]
    exact intervalIntegral.integral_congr (fun x _ => heven x)
  have hfold : (∫ θ in (-Real.pi / 2)..(Real.pi / 2), F θ)
      = 2 * ∫ θ in (0:ℝ)..(Real.pi / 2), F θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
      (hRint _ _) (hRint _ _), hhalf]
    ring
  rw [hfold, integral_log_zeta_cos_quarter_eq_c4 hr0] at hmono
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  calc (1 / (2 * Real.pi)) *
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
          Real.log ‖riemannZeta (1 + (t:ℂ) * Complex.I + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖
      ≤ (1 / (2 * Real.pi)) * (2 * (Real.pi * c4 r)) := by
        apply mul_le_mul_of_nonneg_left hmono
        positivity
    _ = c4 r := by field_simp

/-! ### Elementary bounds extracted for `integraloutside_bound_secondary` -/

/-- **`u ↦ arcsin u / u` is integrable on `[0,1]`.**

### Summary of Proof
The function extends continuously by `1` at `0`, and `arcsin_le_half_pi_mul` bounds it by `π/2`
throughout. A bounded measurable function on a bounded interval is integrable.

### Lean Notes
`integral_arcsin_div_zero_one` computes the value; this records the integrability separately,
since `integraloutside_bound_secondary` needs it as a dominating function rather than as an
evaluation.

### References
No tex counterpart — an integrability side condition the source does not state.

### Dependencies
**Depends on:** `arcsin_le_half_pi_mul`.
**Used by:** `intervalIntegrable_arcsin_div`. -/
theorem integrableOn_arcsin_div :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.arcsin u / u) (Set.Icc (0:ℝ) 1) := by
  apply MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (Real.continuous_arcsin.measurable.div measurable_id).aestronglyMeasurable (Real.pi / 2)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs]
  change |Real.arcsin u / u| ≤ Real.pi / 2
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, div_zero, abs_zero]; positivity
  · rw [abs_of_nonneg (div_nonneg (Real.arcsin_nonneg.mpr hu.1) h0.le), div_le_iff₀ h0]
    linarith [arcsin_le_half_pi_mul hu]

/-- **Interval-integrable form of `integrableOn_arcsin_div`.**

### Summary of Proof
Repackages `integrableOn_arcsin_div`'s `IntegrableOn` conclusion as `IntervalIntegrable`, which
is the form the interval-integral API consumes.

### References
No tex counterpart.

### Dependencies
**Depends on:** `integrableOn_arcsin_div`.
**Used by:** `integraloutside_bound_secondary`, which needs the dominating function in
interval-integral form. -/
theorem intervalIntegrable_arcsin_div :
    IntervalIntegrable (fun u : ℝ => Real.arcsin u / u) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact integrableOn_arcsin_div

/-- **Proposition `\ref{prop:integraloutside}` (Proposition 15)**, secondary explicit bound on
`c_{4,r}` in terms of the Euler–Mascheroni constant `γ` and the first Stieltjes constant `γ₁`.

### Summary of Proof
Substitute `LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`
(`-ζ'/ζ(1+z) < 1/z - γ + (γ²+2γ₁)z` for `0 < z ≤ 2`; Lemma `\ref{lemma:logderzetabound}`
(Lemma 38) at `N = 1`) into
`c4 r`'s defining integral at `z = ru`, giving the pointwise strict bound
`(-ζ'/ζ(1+ru))·arcsin u < (1/(ru) - γ + (γ²+2γ₁)ru)·arcsin u` on `(0,1]`; the right-hand side
splits into the three elementary integrals `integral_arcsin_div_zero_one`,
`integral_arcsin_zero_one`, `integral_mul_arcsin_zero_one`, and scaling by the outer `r/π` gives
exactly the source's three displayed constants — **verified term by term, and all three are correct
as printed**: `(1/π)(π log 2/2) = (log 2)/2`, `-(rγ/π)(π/2-1) = -(π-2)rγ/(2π)`, and
`((γ²+2γ₁)r²/π)(π/8) = r²(γ²+2γ₁)/8` (the first constant's `1/π`-scaled appearance here should not
be confused with the *standalone* integral `∫_0^1 arcsin(u)/u du = π log(2)/2` it derives from,
which carries an extra factor of `π`).

Two ingredients that the source leaves implicit and that the Lean proof has to supply:
* **integrability of `c4`'s integrand.** `(ζ'/ζ)(1+ru)` has a simple pole at `u = 0`, cancelled by
  `arcsin`'s simple zero; rather than argue that cancellation directly, the integrand is squeezed
  between `0` (`Definitions.neg_logDeriv_zeta_re_pos`, i.e. the source's "`ζ'/ζ < 0`") and the
  dominating function above, which is integrable — so `MeasureTheory.Integrable.mono` applies,
  using continuity on `(0,1]` (from `AnalyticOnNhd.deriv`) for measurability.
* **strictness.** The pointwise bound is strict on all of `(0,1]`, a set of positive measure, so
  `intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero` upgrades the
  integral comparison to a strict one, which is what the displayed `<` needs.

The hypothesis `0 < r` is the tex's own — Proposition 15 assumes `0 < r < t` — and it is what
lets the Laurent estimate be applied at `z = ru`; every call site has `r > α > 0`.

### Lean Notes
`hr2 : r ≤ 2` matches the tex, which restricts Proposition 15's **"Moreover"** clause — this
statement — to `r ≤ 2`. The reason is that the Laurent estimate is invoked at `z = ru` with
`u ∈ [0,1]`, while Lemma `\ref{lemma:logderzetabound}` (Lemma 38) supplies it only on `(0,2]`;
Proposition 15 otherwise allows `0 < r < t`.

The restriction stops here. Proposition 15's **first** claim — the identity/integrability behind
`c4` itself — does not use that lemma and is left general in the tex, so
`c4IntegrandBound_abs_le` and the integrability lemmas built on it deliberately keep their bare
`0 < r`. See `c4IntegrandBound_abs_le`'s own note.

Because the estimate it calls is Lemma 38's, this proposition — and through it `A6` and
`mainLittlewood` — inherits that lemma's two hypothesis inputs:
`LaurentCertificate.logDerivZetaG_boundary_bound` (the certified numeric boundary bound
`‖G‖ ≤ 0.6` on `[-6,8]+i[-7,7]`) and `LiteratureInputs.riemannZeta_lowest_zero_height`. Both are
visible in this theorem's signature; the tex states the inequality without any citation.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15), secondary bound (the `r ≤ 2`
"Moreover" clause); the truncated Laurent estimate is Lemma `\ref{lemma:logderzetabound}`
(Lemma 38) at `N = 1`.

### Dependencies
**Depends on:** `c4`, `integral_arcsin_div_zero_one`, `integral_arcsin_zero_one`,
`integral_mul_arcsin_zero_one`, `intervalIntegrable_arcsin_div`,
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`, `neg_logDeriv_zeta_re_pos`,
`stieltjesConstant1`.
**Used by:** `c4_lt_of_le_exp_two_thirds`. -/
theorem integraloutside_bound_secondary {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    c4 r < (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖ + Real.log 2 / 2
      - (Real.pi - 2) * r / (2 * Real.pi) * Real.eulerMascheroniConstant
      + r ^ 2 * (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1) / 8 := by
  have hpi := Real.pi_pos
  set γ : ℝ := Real.eulerMascheroniConstant with hγ
  set K : ℝ := γ ^ 2 + 2 * stieltjesConstant1 with hK
  set nf : ℝ → ℝ := fun u =>
    -(deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re * Real.arcsin u with hnf
  set g : ℝ → ℝ := fun u => (1 / (r * u) - γ + K * (r * u)) * Real.arcsin u with hg
  -- `g` splits into the three elementary arcsin integrals
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    have h1 : IntervalIntegrable (fun u : ℝ => (1/r) * (Real.arcsin u / u))
        MeasureTheory.volume 0 1 := intervalIntegrable_arcsin_div.const_mul _
    have h2 : IntervalIntegrable (fun u : ℝ => (-γ) * Real.arcsin u) MeasureTheory.volume 0 1 :=
      (Real.continuous_arcsin.intervalIntegrable _ _).const_mul _
    have h3 : IntervalIntegrable (fun u : ℝ => (K * r) * (u * Real.arcsin u))
        MeasureTheory.volume 0 1 :=
      ((continuous_id.mul Real.continuous_arcsin).intervalIntegrable _ _).const_mul _
    have := (h1.add h2).add h3
    apply this.congr
    intro u _
    rw [hg]
    simp only
    by_cases hu : u = 0
    · simp [hu]
    · field_simp; ring
  have hgval : (∫ u in (0:ℝ)..1, g u)
      = (1/r) * (Real.pi * Real.log 2 / 2) + (-γ) * (Real.pi/2 - 1) + (K*r) * (Real.pi/8) := by
    have h1 : IntervalIntegrable (fun u : ℝ => (1/r) * (Real.arcsin u / u))
        MeasureTheory.volume 0 1 := intervalIntegrable_arcsin_div.const_mul _
    have h2 : IntervalIntegrable (fun u : ℝ => (-γ) * Real.arcsin u) MeasureTheory.volume 0 1 :=
      (Real.continuous_arcsin.intervalIntegrable _ _).const_mul _
    have h3 : IntervalIntegrable (fun u : ℝ => (K * r) * (u * Real.arcsin u))
        MeasureTheory.volume 0 1 :=
      ((continuous_id.mul Real.continuous_arcsin).intervalIntegrable _ _).const_mul _
    have hcong : (∫ u in (0:ℝ)..1, g u)
        = ∫ u in (0:ℝ)..1, ((1/r) * (Real.arcsin u / u) + (-γ) * Real.arcsin u
            + (K * r) * (u * Real.arcsin u)) := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [hg]
      simp only
      by_cases hu : u = 0
      · simp [hu]
      · field_simp; ring
    rw [hcong, intervalIntegral.integral_add (h1.add h2) h3,
      intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_arcsin_div_zero_one,
      integral_arcsin_zero_one, integral_mul_arcsin_zero_one]
  -- `nf` is continuous on `(0,1]`, nonnegative there, and dominated by `g`
  have hzanal : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton
  have hdanal : AnalyticOnNhd ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ := hzanal.deriv
  have hmemc : ∀ u : ℝ, 0 < u → ((1 + r * u : ℂ)) ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hc
    have := congrArg Complex.re hc
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, add_eq_left, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (ne_of_gt hr)
    · exact absurd h (ne_of_gt hu)
  have hcont : ContinuousOn nf (Set.Ioc (0:ℝ) 1) := by
    intro u hu
    have hcc : ContinuousAt nf u := by
      rw [hnf]
      apply ContinuousAt.mul _ Real.continuous_arcsin.continuousAt
      apply ContinuousAt.neg
      apply Complex.continuous_re.continuousAt.comp
      apply ContinuousAt.div
      · exact ContinuousAt.comp (x := u) ((hdanal _ (hmemc u hu.1)).continuousAt)
          (by fun_prop : ContinuousAt (fun u : ℝ => ((1 + r * u : ℂ))) u)
      · exact ContinuousAt.comp (x := u) ((hzanal _ (hmemc u hu.1)).continuousAt)
          (by fun_prop : ContinuousAt (fun u : ℝ => ((1 + r * u : ℂ))) u)
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp; nlinarith [hu.1]
    exact hcc.continuousWithinAt
  -- pointwise strict domination on `(0,1]`
  have hcast : ∀ u : ℝ, ((1 + r * u : ℂ)) = (((1 + r * u : ℝ)) : ℂ) := by
    intro u; push_cast; ring
  have hdom : ∀ u ∈ Set.Ioc (0:ℝ) 1, nf u < g u := by
    intro u hu
    have hru : 0 < r * u := mul_pos hr hu.1
    have harc : 0 < Real.arcsin u := Real.arcsin_pos.2 hu.1
    have hb := neg_logDeriv_zeta_bound_of_claim_two (x := r * u) hru
      (le_trans (mul_le_of_le_one_right hr.le hu.2) hr2)
    rw [hnf, hg]
    simp only
    rw [hcast u]
    have : -(deriv riemannZeta ((1 + r * u : ℝ) : ℂ)
        / riemannZeta ((1 + r * u : ℝ) : ℂ)).re < 1 / (r * u) - γ + K * (r * u) := hb
    exact mul_lt_mul_of_pos_right this harc
  have hnn : ∀ u ∈ Set.Ioc (0:ℝ) 1, 0 ≤ nf u := by
    intro u hu
    have harc : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.2 hu.1.le
    have hp := neg_logDeriv_zeta_re_pos (σ := 1 + r * u) (by nlinarith [hu.1])
    rw [hnf]
    simp only
    apply mul_nonneg _ harc
    rw [hcast u]
    simpa using hp.le
  -- integrability of `nf`: continuous on `(0,1]`, and squeezed between `0` and `g`
  have hnfi : IntervalIntegrable nf MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hmeas : MeasureTheory.AEStronglyMeasurable nf
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hcont.aestronglyMeasurable measurableSet_Ioc
    have hgint : MeasureTheory.IntegrableOn g (Set.Ioc (0:ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]; exact hgi
    refine MeasureTheory.Integrable.mono hgint hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn u hu),
      abs_of_nonneg (le_trans (hnn u hu) (hdom u hu).le)]
    exact (hdom u hu).le
  -- strict integral comparison
  have hlt : (∫ u in (0:ℝ)..1, nf u) < ∫ u in (0:ℝ)..1, g u := by
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
      (by norm_num) hnfi hgi ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
      exact (hdom u hu).le
    · rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc]
      have hEq : {x | nf x < g x} ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 :=
        Set.inter_eq_self_of_subset_right (fun x hx => hdom x hx)
      rw [hEq, Real.volume_Ioc]
      norm_num
  -- assemble
  have hcnf : (∫ u in (0:ℝ)..1,
      (deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re * Real.arcsin u)
      = -(∫ u in (0:ℝ)..1, nf u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    rw [hnf]; simp only; ring
  have hscale : (0:ℝ) < r / Real.pi := by positivity
  have hkey : (r / Real.pi) * (∫ u in (0:ℝ)..1, g u)
      = Real.log 2 / 2 - (Real.pi - 2) * r / (2 * Real.pi) * γ + r ^ 2 * K / 8 := by
    rw [hgval]; field_simp; ring
  have hstep : (r / Real.pi) * (∫ u in (0:ℝ)..1, nf u)
      < (r / Real.pi) * (∫ u in (0:ℝ)..1, g u) := mul_lt_mul_of_pos_left hlt hscale
  rw [hkey] at hstep
  rw [c4, hcnf]
  have hring : (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖
      - r / Real.pi * -(∫ u in (0:ℝ)..1, nf u)
      = (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖
        + (r / Real.pi) * (∫ u in (0:ℝ)..1, nf u) := by ring
  rw [hring]
  linarith [hstep]

/-- **`C_{1,α,r} = c_{1,r}/log(r/α)`**, the `log|T|` coefficient of Theorem
`\ref{thm:circularregions1}` (Theorem 16).

### Summary of Proof
A definition. It is `c_{1,r}` divided by `L := log(r/α)`, the factor Jensen's formula contributes
when converting a circle average into a zero count.

### References
tex: Theorem `\ref{thm:circularregions1}` (Theorem 16); `c_{1,r}` is defined after Equation
`\ref{eq:thetak}` (Equation 8).

### Dependencies
**Depends on:** `c1`.
**Used by:** `C1_scaling`, `circularregions1`, `circularregions1_tight`. -/
noncomputable def C1 (α r : ℝ) : ℝ := c1 r / Real.log (r / α)

/-- **`C_{2,α,r} = c_{2,r}/(π log(r/α)) + 1/log(r/α)`**, the `log log|T|` coefficient of Theorem
`\ref{thm:circularregions1}` (Theorem 16).

### Summary of Proof
A definition. The bare `+1/log(r/α)` is not decoration: it is the `log log|T|` coefficient
contributed by `ExternalFacts.leong_log_zeta_one_bound` when bounding `-log‖ζ(1+iT)‖`, which
enters the numerator of Jensen's formula alongside the circle average.

### References
tex: Theorem `\ref{thm:circularregions1}` (Theorem 16). External: Leong, arXiv:2405.04869, for
the `log log` term.

### Dependencies
**Depends on:** `c2`.
**Used by:** `C2_scaling`, `circularregions1`, `circularregions1_tight`. -/
noncomputable def C2 (α r : ℝ) : ℝ := c2 r / (Real.log (r / α) * Real.pi) + 1 / Real.log (r / α)

/-- **`C_{3,α,r} = (c_{3,r}/π + c_{4,r} + log 29.388)/log(r/α)`**, the constant term of Theorem
`\ref{thm:circularregions1}` (Theorem 16).

### Summary of Proof
A definition, assembling the three constant contributions divided by `L := log(r/α)`: `c_{3,r}/π`
from the outside-strip half of the circle (`jensen_easy`), `c_{4,r}` from the inside-strip half
(`integraloutside_bound`), and `log 29.388` from `leong_log_zeta_one_bound`'s bound on
`-log‖ζ(1+iT)‖`.

### Lean Notes
That the two halves are complementary — `[π/2, 3π/2]` and `[-π/2, π/2]` — is what makes the sum
cover the whole circle exactly once. Getting that split wrong would double-count one half; see
`jensen_easy`'s docstring for the three independent checks pinning the range.

### References
tex: Theorem `\ref{thm:circularregions1}` (Theorem 16); Proposition
`\ref{prop:integraloutside}` (Proposition 15) for `c_{4,r}`. External: Leong,
arXiv:2405.04869.

### Dependencies
**Depends on:** `c3`, `c4`.
**Used by:** `circularregions1`, `circularregions1_tight`. -/
noncomputable def C3 (α r : ℝ) : ℝ :=
  c3 r / (Real.pi * Real.log (r / α)) + c4 r / Real.log (r / α)
    + Real.log 29.388 / Real.log (r / α)

/-- **Theorem `\ref{thm:circularregions1}` (Theorem 16), crude version.** For `0 < α`,
`α < r < 1` and `T > 10¹² + 1`,
`N(1+iT,α) ≤ (C_{1,α,r}/π) log|T| + C_{2,α,r} log log|T| + C_{3,α,r} + O^*(3/(T log(r/α)))`.

### Summary of Proof
Jensen's formula (`jensenbound`) at `s = 1+iT`, with the circle split at `θ = ±π/2`: the
inside-strip half is bounded by `integraloutside_bound`, giving `c_{4,r}`; the outside-strip half
by `jensen_easy`, giving `c_{1,r}`, `c_{2,r}`, `c_{3,r}`; and `-log‖ζ(1+iT)‖` by
`ExternalFacts.leong_log_zeta_one_bound`. Dividing through by `L := log(r/α)` produces the three
constants exactly as printed: `C₁/π = (c₁/π)/L`, `C₂ = (c₂/π + 1)/L` — the `+1` being Leong's
`log log|T|` contribution — and `C₃ = (c₃/π + c₄ + log 29.388)/L`.

### Lean Notes
**Weaker than the printed theorem**, in exactly the way `jensen_easy` is weaker than
Proposition `\ref{prop:jensen-easy}` (Proposition 8), and for the same reason: it is built on
`jensen_easy`. Theorem `\ref{thm:circularregions1}` (Theorem 16) carries the error
`O^*((1/log(r/α))(5/(6(T-1)) + 1/(T-1)² + 579/(8(T-1)²log(T-1))))` under `T > 13`; the bound
proved here is the *cruder* `3/(T·log(r/α))`, inherited from `jensen_easy`'s `O^*(3/T)`. At
`T = 10¹²` that is `3×10⁻¹²` against the tex's `≈8.3×10⁻¹³`, so this statement is **weaker than,
but implied by**, the printed one. `circularregions1_tight` below matches the tex term for term.

The tex's `1 > r > α` supplies `r < 1`, and it leaves `α > 0` implicit — forced by `log(r/α)` in
every denominator — whereas the Lean states it as the hypothesis `hα0`. The hypothesis
`_hα : α ≤ 1` is unused. The threshold `10¹² + 1 < T` is `jensen_easy`'s; it also delivers
`r < T`, i.e. `ζ`'s pole lies outside the disc, and `2 ≤ |T|` for Leong's bound.

The circle is split at `θ = ±π/2` into `jensen_easy`'s `[π/2, 3π/2]` and
`integraloutside_bound`'s complementary `[-π/2, π/2]`; see `jensen_easy`'s docstring for the
checks pinning that range.

### References
tex: Theorem `\ref{thm:circularregions1}` (Theorem 16); Proposition
`\ref{prop:jensen-easy}` (Proposition 8); Proposition `\ref{prop:integraloutside}`
(Proposition 15); Proposition `\ref{prop:jensenbound}` (Proposition 6). External: Leong,
arXiv:2405.04869.

### Dependencies
**Depends on:** `C1`, `C2`, `C3`, `Ncirc`, `c1`, `c2`, `c3`, `c4`, `integraloutside_bound`,
`intervalIntegrable_log_zeta_circle`, `jensenCircleAvg`, `jensen_easy`, `jensenbound`,
`leong_log_zeta_one_bound`.
**Used by:** none. -/
theorem circularregions1 {T α r : ℝ} (hα0 : 0 < α) (_hα : α ≤ 1) (hr : α < r) (hr1 : r < 1)
    (hT : (10 : ℝ) ^ (12 : ℕ) + 1 < T) :
    (Ncirc (1 + T * Complex.I) α : ℝ)
      ≤ C1 α r / Real.pi * Real.log |T| + C2 α r * Real.log (Real.log |T|) + C3 α r
        + 3 / (T * Real.log (r / α)) := by
  have hpi := Real.pi_pos
  have hT10 : (10:ℝ) ≤ T := by
    have : (10:ℝ) ≤ (10:ℝ) ^ (10:ℕ) := by norm_num
    linarith
  have hr0 : 0 < r := hα0.trans hr
  have hrT : r < T := by linarith
  have hTabs : |T| = T := abs_of_pos (by linarith)
  have hL0 : 0 < Real.log (r / α) := Real.log_pos ((one_lt_div hα0).mpr hr)
  have hball : (1 : ℂ) ∉ Metric.closedBall ((1 : ℂ) + (T:ℂ) * Complex.I) r := by
    simp only [Metric.mem_closedBall, Complex.dist_eq, not_le]
    have : (1 : ℂ) - (1 + (T:ℂ) * Complex.I) = -((T:ℂ) * Complex.I) := by ring
    rw [this, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real]
    simp [hTabs]
    linarith
  have hζ : riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have hjb := jensenbound (s := (1 : ℂ) + (T:ℂ) * Complex.I) (r := r) (α := α) hr hα0 hball hζ
  have hsplit : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      = (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) := by
    have hI := (intervalIntegral.integral_add_adjacent_intervals
        (a := -Real.pi/2) (b := Real.pi/2) (c := 3*Real.pi/2)
        (f := fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        (intervalIntegrable_log_zeta_circle _ _ _ _)
        (intervalIntegrable_log_zeta_circle _ _ _ _)).symm
    rw [jensenCircleAvg, hI, mul_add]
  have hin := integraloutside_bound (t := T) (r := r) hr0 (by linarith) hrT
  have hout := jensen_easy (r := r) (t := T) hr0 hr1 hT
  have hleong := leong_log_zeta_one_bound (t := T) (by rw [hTabs]; linarith)
  have hnum : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
      ≤ (c1 r / Real.pi * Real.log |T| + c2 r / Real.pi * Real.log (Real.log |T|)
          + c3 r / Real.pi + 3 / T)
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388) := by
    rw [hsplit, hTabs]
    have hneg : -Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
        ≤ Real.log (Real.log |T|) + Real.log 29.388 := by
      convert hleong using 3
    rw [hTabs] at hneg
    linarith
  have hstep : (jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
        - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖) / Real.log (r / α)
      ≤ ((c1 r / Real.pi * Real.log |T| + c2 r / Real.pi * Real.log (Real.log |T|)
          + c3 r / Real.pi + 3 / T)
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388)) / Real.log (r / α) := by
    gcongr
  refine hjb.trans (hstep.trans (le_of_eq ?_))
  rw [C1, C2, C3]
  field_simp
  ring

set_option maxHeartbeats 300000 in
-- the extra `O(1/(T-1)²)` bookkeeping pushes this past the default elaboration budget.
/-- **Theorem `\ref{thm:circularregions1}` (Theorem 16), tight version** — the one matching the
printed statement, with hypothesis `T > 13`.

### Summary of Proof
The same argument as `circularregions1`: Jensen's formula (`jensenbound`) at `s = 1+iT`, with the
circle split at `θ = ±π/2` into the outside-strip half — bounded by `jensen_easy_tight` — and the
inside-strip half — bounded by `integraloutside_bound`, giving `c_{4,r}` — plus
`leong_log_zeta_one_bound` for `-log‖ζ(1+iT)‖`, all divided by `L := log(r/α)`.

### Lean Notes
Differs from `circularregions1` only in using `jensen_easy_tight` in place of `jensen_easy`,
which brings Proposition `\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)`
bound and with it the tex's own threshold `t > 13` instead of `10¹²+1 < t`.

Everything else is unchanged and needs no threshold beyond `T > 13` — in fact each of
`jensenbound`, `integraloutside_bound` and `leong_log_zeta_one_bound` needs far less: `T > 2`,
`r < T`, and `2 ≤ |T|` respectively.

### References
tex: Theorem `\ref{thm:circularregions1}` (Theorem 16), matched exactly; Proposition
`\ref{prop:jensen-easy}` (Proposition 8); Proposition `\ref{prop:integraloutside}`
(Proposition 15).

### Dependencies
**Depends on:** `C1`, `C2`, `C3`, `Ncirc`, `c1`, `c2`, `c3`, `c4`, `integraloutside_bound`,
`intervalIntegrable_log_zeta_circle`, `jensenCircleAvg`, `jensen_easy_tight`, `jensenbound`,
`leong_log_zeta_one_bound`.
**Used by:** none yet — the tight track's consumer, `rectangularjensen_tight`, routes through
`jensen_easy_tight` directly. -/
theorem circularregions1_tight {T α r : ℝ} (hα0 : 0 < α) (_hα : α ≤ 1) (hr : α < r) (hr1 : r < 1)
    (hT : (13 : ℝ) < T) :
    (Ncirc (1 + T * Complex.I) α : ℝ)
      ≤ C1 α r / Real.pi * Real.log |T| + C2 α r * Real.log (Real.log |T|) + C3 α r
        + (5 / (6 * (T - 1)) + (1 / (T - 1) ^ 2 + 1158 / (16 * (T - 1) ^ 2 * Real.log (T - 1))))
            / Real.log (r / α) := by
  have hpi := Real.pi_pos
  have hr0 : 0 < r := hα0.trans hr
  have hrT : r < T := by linarith
  have hTabs : |T| = T := abs_of_pos (by linarith)
  have hL0 : 0 < Real.log (r / α) := Real.log_pos ((one_lt_div hα0).mpr hr)
  have hball : (1 : ℂ) ∉ Metric.closedBall ((1 : ℂ) + (T:ℂ) * Complex.I) r := by
    simp only [Metric.mem_closedBall, Complex.dist_eq, not_le]
    have : (1 : ℂ) - (1 + (T:ℂ) * Complex.I) = -((T:ℂ) * Complex.I) := by ring
    rw [this, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real]
    simp [hTabs]
    linarith
  have hζ : riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have hjb := jensenbound (s := (1 : ℂ) + (T:ℂ) * Complex.I) (r := r) (α := α) hr hα0 hball hζ
  have hsplit : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      = (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) := by
    have hI := (intervalIntegral.integral_add_adjacent_intervals
        (a := -Real.pi/2) (b := Real.pi/2) (c := 3*Real.pi/2)
        (f := fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        (intervalIntegrable_log_zeta_circle _ _ _ _)
        (intervalIntegrable_log_zeta_circle _ _ _ _)).symm
    rw [jensenCircleAvg, hI, mul_add]
  have hin := integraloutside_bound (t := T) (r := r) hr0 (by linarith) hrT
  have hout := jensen_easy_tight (r := r) (t := T) hr0 hr1 hT
  have hleong := leong_log_zeta_one_bound (t := T) (by rw [hTabs]; linarith)
  have hnum : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
      ≤ (c1 r / Real.pi * Real.log |T| + c2 r / Real.pi * Real.log (Real.log |T|)
          + c3 r / Real.pi
          + (5 / (6 * (T - 1)) + (1 / (T - 1) ^ 2 + 1158 / (16 * (T - 1) ^ 2 * Real.log (T - 1)))))
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388) := by
    rw [hsplit, hTabs]
    have hneg : -Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
        ≤ Real.log (Real.log |T|) + Real.log 29.388 := by
      convert hleong using 3
    rw [hTabs] at hneg
    linarith
  have hstep : (jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
        - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖) / Real.log (r / α)
      ≤ ((c1 r / Real.pi * Real.log |T| + c2 r / Real.pi * Real.log (Real.log |T|)
          + c3 r / Real.pi
          + (5 / (6 * (T - 1)) + (1 / (T - 1) ^ 2 + 1158 / (16 * (T - 1) ^ 2 * Real.log (T - 1)))))
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388)) / Real.log (r / α) := by
    gcongr
  refine hjb.trans (hstep.trans (le_of_eq ?_))
  have hT1pos : (0:ℝ) < T - 1 := by linarith
  have hlogT1pos : (0:ℝ) < Real.log (T - 1) := Real.log_pos (by linarith)
  rw [C1, C2, C3]
  field_simp
  ring

/-- **The integral representation of `c_{1,r}`**: `c_{1,r} = ∫_0^{π/2} A(1 - r sin φ) dφ`.

### Summary of Proof
This is the identity the closed form in `JensenScaleConstants` was derived from, run backwards.
Decompose `[0, π/2]` as before: the boundary piece `[θ_{K,r}, π/2]` carries chord index `K-1`,
and the countable family `[θ_{k+1,r}, θ_{k,r}]` carries index `k`. On each piece the integrand
*is* the affine chord function (`chordW_arc_eq`), so `chord_boundary_eq_integral` and
`chord_term_eq_integral` apply verbatim, and `tsum_eq_integral_arc` glues the pieces into the
whole quarter.

### Lean Notes
Unlike the bounds above, this is an **equality**, which is why it needs `tsum_eq_integral_arc`
rather than `integral_le_tsum_arc`. It is what makes the radius-scaling argument possible:
comparing `c₁` at two radii becomes comparing two integrals over the same interval.

### References
tex: the `c_{1,r}` display after Equation `\ref{eq:thetak}` (Equation 8), of which this is the
integral form.

### Dependencies
**Depends on:** `Kidx`, `Kidx_mem`, `Kidx_sub_one`, `bCoeff`, `c1`, `c1_summable`, `chordW`,
`chordW_arc_eq`, `chord_boundary_eq_integral`, `chord_term_eq_integral`,
`intervalIntegrable_chordW`, `mCoeff`, `chordW_eq`, `chordW_mono`, `sigma`, `sigma_lt_one`,
`sin_theta_eq`, `theta`, `theta_le_pi_div_two`, `tsum_eq_integral_arc`.
**Used by:** `c1_scaling`. -/
theorem c1_eq_integral {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    c1 r = ∫ φ in (0:ℝ)..(Real.pi/2), chordW (r * Real.sin φ) := by
  have hpi := Real.pi_pos
  have hKmem : 1 - sigma (Kidx r) ≤ r := Kidx_mem hr0 hr1
  have hKsub : r < 1 - sigma (Kidx r - 1) := Kidx_sub_one hr0 hr1
  have hK0 : (0:ℝ) ≤ theta (Kidx r) r := theta_nonneg hr0
  have hKpi : theta (Kidx r) r ≤ Real.pi/2 := theta_le_pi_div_two (Kidx r) r
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun φ : ℝ => chordW (r * Real.sin φ))
      MeasureTheory.volume u v := fun u v => intervalIntegrable_chordW r u v
  have hbdry : (mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi/2 - theta (Kidx r) r)
        - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
      = ∫ φ in (theta (Kidx r) r)..(Real.pi/2), chordW (r * Real.sin φ) := by
    rw [chord_boundary_eq_integral]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun φ hφ => ?_)
    rw [Set.uIoc_of_le hKpi] at hφ
    have hs1 : (1 - sigma ((Kidx r - 1)+1))/r < Real.sin φ := by
      rw [show Kidx r - 1 + 1 = Kidx r by ring, ← sin_theta_eq hr0 hKmem]
      exact Real.strictMonoOn_sin ⟨by linarith, hKpi⟩ ⟨by linarith [hφ.1], hφ.2⟩ hφ.1
    have hs2 : Real.sin φ ≤ (1 - sigma (Kidx r - 1))/r := by
      have h1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
      have h2 : (1:ℝ) < (1 - sigma (Kidx r - 1))/r := by rw [lt_div_iff₀ hr0]; linarith
      linarith
    exact (chordW_arc_eq hr0 hr1 hs1 hs2).symm
  have htsum : (∑' j : ℕ, ((mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeff (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r))))
      = ∫ φ in (0:ℝ)..(theta (Kidx r) r), chordW (r * Real.sin φ) := by
    refine tsum_eq_integral_arc hr0 hint (c1_summable hr0 hr1) ?_
    intro j
    rw [chord_term_eq_integral]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun φ hφ => ?_)
    rw [Set.uIoc_of_le (theta_antitone_succ hr0)] at hφ
    have hk : 1 - sigma (Kidx r + j) ≤ r := by
      have hmono : sigma (Kidx r) ≤ sigma (Kidx r + j) := sigma_strictMono.monotone (by omega)
      linarith
    obtain ⟨hs1, hs2⟩ := sin_window_of_mem_chord hr0 hk hφ.1 hφ.2
    exact chordW_arc_eq hr0 hr1 hs1 hs2
  rw [c1, hbdry, htsum, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)

/-- **The `c₁` scaling claim underlying `C1_scaling`**: `c₁(λr) ≤ λ·c₁(r)` for `0 < λ ≤ 1`.

### Summary of Proof
Both sides become integrals over the *same* interval via `c1_eq_integral`, after which the claim
reduces to the pointwise star-shapedness `W(λx) ≤ λ·W(x)` (`chordW_star`) — equivalently
`A(σ)/(1-σ)` antitone, which is `m_k + b_k < 0` within a chord and `vRatio_strictAnti` across
chords.

### Lean Notes
The source argues it differently, and less completely. Equivalently — its route — `r ↦ c₁(r)/r`
is nondecreasing, i.e.
`(d/dr)(c_{1,r}/r) ≥ 0`. The source's reasons, quoted: "`θ_{k,r} - θ_{k+1,r}` decreases as `r`
increases, but `b_k ≤ 0`. Notice also that `∑_{k=K}^∞ (-cos(θ_{k,r}) + cos(θ_{k+1,r}))` is constant
as `r` changes, but, as `r` increases, the weight shifts to lower values of `k` for which `m_k` is
larger." It is then asserted to follow "by inspection"; no term-by-term argument is given, and the
index `K = Kidx r` also moves with `r`, so a formal proof has to handle that jump as well.

Isolated here so that `C1_scaling` is a genuine consequence rather than a restatement.

The condition used is `m_k + b_k ≤ 0`, matching the tex and
`JensenScaleConstants.mCoeff_add_bCoeff_neg`. In the paper's own convention `b_k > 0` for every
`k`, so a bare `b_k ≤ 0` could not be what the argument needs.

**`r < 1` is needed.** `c_{1,r}` is defined through `K = Kidx r`, which is the integer infimum of
`{k : 1-σ_k ≤ r}`; for `r ≥ 1` that set is all of `ℤ` (every `σ_k > 0`), hence unbounded below, and
`sInf` returns junk. This is the `K = -∞` case the source admits but the closed form does not
cover. Every use of the Proposition has `r < 1` anyway.

### References
tex: Proposition `\ref{prop:Cscaling}` (Proposition 17), immediately following Theorem
`\ref{thm:circularregions1}` (Theorem 16); the inequality `m_k+b_k ≤ 0` appears in its proof.

### Dependencies
**Depends on:** `c1`, `c1_eq_integral`, `chordW_star`, `intervalIntegrable_chordW`.
**Used by:** `C1_scaling`. -/
theorem c1_scaling {r lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    c1 (lam * r) ≤ lam * c1 r := by
  have hpi := Real.pi_pos
  have hlr0 : 0 < lam * r := mul_pos hlam0 hr
  have hlr1 : lam * r < 1 := by nlinarith
  rw [c1_eq_integral hlr0 hlr1, c1_eq_integral hr hr1, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by positivity) (intervalIntegrable_chordW _ _ _)
    ((intervalIntegrable_chordW r _ _).const_mul lam) ?_
  intro φ hφ
  have hsin0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2])
  have hx0 : 0 ≤ r * Real.sin φ := mul_nonneg hr.le hsin0
  have hx1 : r * Real.sin φ < 1 := by nlinarith [Real.sin_le_one φ]
  rw [mul_assoc]
  exact chordW_star hx0 hx1 hlam0 hlam1

/-- **Rescaling `r` by `α/α₀` scales `C_{1,α,·}` by at most `α/α₀`** — first half of
`Proposition \ref{prop:Cscaling}` (Proposition 17).

### Summary of Proof
The reduction is exact and needs no estimates. Since `((α/α₀)·r)/α = r/α₀`, the two `log`
denominators *coincide*, so the claim is literally `c₁((α/α₀)r)/L ≤ (α/α₀)·c₁(r)/L` with
`L = log(r/α₀) > 0` — which is `c1_scaling` divided through by `L`.

### Lean Notes
**Hypothesis `r < 1`**, inherited from `c1_scaling`: `c_{1,ρ}` is only defined by the closed form
when `ρ < 1`, since otherwise `Kidx ρ` is the infimum of an unbounded-below set. This is the
source's `K = -∞` case, which the closed form does not cover.

### References
tex: Proposition `\ref{prop:Cscaling}` (Proposition 17), first half. The tex's extra assumption
`r ≥ e·α₀` is not needed here.

### Dependencies
**Depends on:** `C1`, `c1`, `c1_scaling`.
**Used by:** none — recorded as the scaling law the source states for `C_{1,α,r}`. -/
theorem C1_scaling {r α α0 : ℝ} (hα0 : 0 < α) (hrα0 : α0 < r) (hr1 : r < 1) (hα : α < α0) :
    C1 α ((α / α0) * r) ≤ C1 α0 r * (α / α0) := by
  have hα00 : (0:ℝ) < α0 := lt_trans hα0 hα
  have hr0 : (0:ℝ) < r := lt_trans hα00 hrα0
  have hlam0 : (0:ℝ) < α / α0 := by positivity
  have hlam1 : α / α0 ≤ 1 := by rw [div_le_one hα00]; linarith
  have hL : (0:ℝ) < Real.log (r / α0) := Real.log_pos (by rw [lt_div_iff₀ hα00]; linarith)
  have hden : ((α / α0) * r) / α = r / α0 := by field_simp
  rw [C1, C1, hden]
  rw [div_le_iff₀ hL]
  have := c1_scaling hr0 hr1 hlam0 hlam1
  calc c1 (α / α0 * r) ≤ (α / α0) * c1 r := this
    _ = c1 r / Real.log (r / α0) * (α / α0) * Real.log (r / α0) := by
        field_simp

/-- **`c₂ r ≤ π/2`** — in fact `c₂ r = π/2` exactly.

### Summary of Proof
Pure telescoping. `vCoeffP` is the constant function `1`, so `mCoeffP ≡ 0` and `bCoeffP ≡ 1`, and

  `c₂ r = (0+1)(π/2 - θ_{K,r}) - 0 + Σ_{j≥0} [(0+1)(θ_{K+j,r} - θ_{K+j+1,r}) + 0]`
       `= (π/2 - θ_{K,r}) + θ_{K,r} = π/2`,

the sum telescoping to `θ_{K,r}` because `θ_{k,r} = arcsin((1-σ_k)/r) → 0` as `k → ∞`
(`sigma k → 1`). Equivalently, and more transparently, `c₂ r = ∫_0^{π/2} 1 dθ = π/2`, since the
`log log|t|` chord is identically `1`.

Consistent with the source's Table `\ref{tab:crvalues}` (Table 2), whose `c_{2,r}` column is
exactly `1.570797 = π/2` at every tabulated `r ≤ 1/4` — precisely those `r` for which the `k = 0`
chord is never reached, so that the alternate `v_0' = 0` of Remark `\ref{rem:altcoefficients}`
(Remark 7) makes no difference. For `r = 1/3, 1/2, 1` the table is smaller, which is that
alternate variant showing.

The hypothesis `0 < r` is added here (needed for `theta`'s argument to be nonnegative). Only the
inequality is established, not the equality, and that keeps it short: the summands
`θ_{K+j} - θ_{K+j+1}` are nonnegative with partial sums `θ_K - θ_{K+n} ≤ θ_K`
(`JensenScaleConstants.sum_range_theta_telescope`, `theta_nonneg`, `theta_antitone_succ`), so
`Real.tsum_le_of_sum_range_le` bounds the tail by `θ_K` — no limit `θ_{K+n} → 0`, hence no
`sigma k → 1` argument, is needed.

### References
tex: the `c_{2,r}` display after Equation `\ref{eq:thetak}` (Equation 8), and Table
`\ref{tab:crvalues}` (Table 2), whose `c_{2,r}` column is `1.570797 = π/2` for the smaller radii.

### Dependencies
**Depends on:** `Kidx`, `bCoeffP`, `c2`, `mCoeffP`, `sum_range_theta_telescope`, `theta`,
`theta_antitone_succ`, `theta_nonneg`, `vCoeffP`.
**Used by:** `C2_scaling`. -/
theorem c2_le_pi_div_two {r : ℝ} (hr : 0 < r) : c2 r ≤ Real.pi / 2 := by
  have hm : ∀ k : ℤ, mCoeffP k = 0 := by
    intro k; simp [mCoeffP, vCoeffP]
  have hb : ∀ k : ℤ, bCoeffP k = 1 := by
    intro k; simp [bCoeffP, vCoeffP, hm]
  rw [c2]
  simp only [hm, hb, zero_add, zero_mul, add_zero, one_mul, sub_zero]
  have hnn : ∀ j : ℕ, 0 ≤ theta (Kidx r + j) r - theta (Kidx r + j + 1) r := by
    intro j; linarith [theta_antitone_succ (k := Kidx r + j) hr]
  have hle : ∀ n : ℕ, ∑ j ∈ Finset.range n,
      (theta (Kidx r + j) r - theta (Kidx r + j + 1) r) ≤ theta (Kidx r) r := by
    intro n
    rw [sum_range_theta_telescope]
    linarith [theta_nonneg (k := Kidx r + n) hr]
  have := Real.tsum_le_of_sum_range_le hnn hle
  linarith

/-- **Rescaling `r` by `α/α₀` keeps `C_{2,α,·}` bounded by `3/(2 log(r/α₀))`** — second half of
`Proposition \ref{prop:Cscaling}` (Proposition 17).

### Summary of Proof
Follows from `c2_le_pi_div_two`, and needs no lower bound on `r/α₀` at all. As with
`C1_scaling` the two `log` denominators coincide, so
`C₂(α, (α/α₀)r) = [c₂((α/α₀)r)/π + 1] / log(r/α₀)`. The numerator is `≤ 3/2` unconditionally
(`c₂ ≤ π/2`, `c2_le_pi_div_two`), and dividing that bound through by the *same* positive
denominator `log(r/α₀)` (needing only `r > α₀` for positivity, nothing more) gives the displayed
`3/(2\log(r/α₀))` directly — no need to separately show `log(r/α₀) ≥ 1`.

### Lean Notes
Proposition 17 also assumes `r ≥ e·α₀`; this statement does not need it. Only positivity of
`log(r/α₀)` is used, which `α₀ < r` already gives. Folding the denominator back in — bounding
`C₂(α,(α/α₀)r) ≤ 3/2` outright — is what would need `log(r/α₀) ≥ 1`.

### References
tex: Proposition `\ref{prop:Cscaling}` (Proposition 17), second half.

### Dependencies
**Depends on:** `C2`, `c2`, `c2_le_pi_div_two`.
**Used by:** none — recorded as the scaling law the source states for `C_{2,α,r}`. -/
theorem C2_scaling {r α α0 : ℝ} (hα0 : 0 < α) (hrα0 : α0 < r) (hα : α < α0) :
    C2 α ((α / α0) * r) ≤ 3 / (2 * Real.log (r / α0)) := by
  have hπ := Real.pi_pos
  have hα00 : (0:ℝ) < α0 := lt_trans hα0 hα
  have hL0 : (0:ℝ) < Real.log (r / α0) := Real.log_pos (by rw [lt_div_iff₀ hα00]; linarith)
  have hden : ((α / α0) * r) / α = r / α0 := by field_simp
  rw [C2, hden]
  have hr0 : (0:ℝ) < r := lt_trans hα00 hrα0
  have hc2 := c2_le_pi_div_two (r := α / α0 * r) (by positivity)
  have hnum : c2 (α / α0 * r) / Real.pi + 1 ≤ 3 / 2 := by
    rw [div_add' _ _ _ (ne_of_gt hπ), div_le_iff₀ hπ]
    linarith
  have hsplit : c2 (α / α0 * r) / (Real.log (r / α0) * Real.pi) + 1 / Real.log (r / α0)
      = (c2 (α / α0 * r) / Real.pi + 1) / Real.log (r / α0) := by
    field_simp
  rw [hsplit, div_le_div_iff₀ hL0 (by positivity : (0:ℝ) < 2 * Real.log (r / α0))]
  nlinarith [hnum, hL0, mul_le_mul_of_nonneg_right hnum
    (by linarith : (0:ℝ) ≤ 2 * Real.log (r / α0))]

/-- **`\tilde C_{1,α}`**, the `log|T|` coefficient of Theorem `\ref{thm:circularregions2}`
(Theorem 18).

### Summary of Proof
A definition, built from the elliptic-integral constant `E_{1/2}`. Its `π`-normalised value is
`(3e/2π)E_{1/2}·B·α^{3/2}`, bounded numerically by `Ctilde1_lt`.

### References
tex: Theorem `\ref{thm:circularregions2}` (Theorem 18); `E_{1/2}` is introduced in Proposition
`\ref{prop:Richert}` (Proposition 12).

### Dependencies
**Depends on:** `Ehalf`.
**Used by:** `Ctilde1_lt`, `circularregions2`. -/
noncomputable def Ctilde1 (α B : ℝ) : ℝ := 3 * Ehalf * Real.exp 1 * B * α ^ (3 / 2 : ℝ) / 2

/-- **`\tilde C_{3,α}`**, the constant term of Theorem `\ref{thm:circularregions2}`
(Theorem 18), at radius `e^{2/3}α`.

### Summary of Proof
A definition, assembled from `c_{4,r}` at `r = e^{2/3}α`.

### Lean Notes
The radius `e^{2/3}α` is the one forced by `log(r/α) = 2/3`; see `circularregions2`'s docstring.
The choice is load-bearing downstream: at `e^{2/3}` the threshold condition
`stieltjes_combo_bound` holds with margin `0.059`, whereas a radius near `e^{3/2}` would leave
only `1.9×10⁻⁵`, and then only under the extra restriction `α ≤ 0.998`.

### References
tex: Theorem `\ref{thm:circularregions2}` (Theorem 18); Proposition
`\ref{prop:integraloutside}` (Proposition 15) for `c_{4,r}`.

### Dependencies
**Depends on:** `c4`.
**Used by:** `Ctilde3_lt_of_le_one`, `circularregions2`. -/
noncomputable def Ctilde3 (α A : ℝ) : ℝ :=
  3 * A / 4 + 3 * c4 (Real.exp (2 / 3) * α) / 2 + 3 * Real.log 29.388 / 2

/-- **Theorem `\ref{thm:circularregions2}` (Theorem 18).** Given a Richert-type bound valid for
`1 - σ < e^{2/3}α` on the window swept by the circle,
`N(1+iT,α) ≤ (\tilde C_{1,α}/π) log|T| + 2 log log|T| + \tilde C_{3,α}`.

### Summary of Proof
**Follows the source's own one-line proof** — "follows as above [i.e. as `circularregions1`]
using Proposition `\ref{prop:Richert}` (Proposition 12) in place of Proposition
`\ref{prop:jensen-easy}` (Proposition 8), with `r = e^{2/3}α`, so that `log(r/α) = 2/3`":
`jensenbound` at `s = 1+iT` with radius `r`, splitting `jensenCircleAvg` at `θ = ±π/2` into the
inside-strip half (bounded by `integraloutside_bound`, i.e. `c4 r`) and the outside-strip half
(bounded by `prop_Richert`), and bounding `-log‖ζ(1+iT)‖` by
`ExternalFacts.leong_log_zeta_one_bound`. Everything is then divided by `L := log(r/α) = 2/3`.

**The radius `e^{2/3}α` is pinned by the printed constants.** Three of the four force `L = 2/3`,
hence `r/α = e^{2/3}`: `A/(2L) = 3A/4`, `c4 r/L = (3/2)c4 r`, and
`log(29.388)/L = (3/2)log 29.388`. The fourth confirms it: `prop_Richert`'s `log|T|` coefficient
divided by `L` is `(E_{1/2}B r^{3/2}/π)/L = (3/2)E_{1/2}B e α^{3/2}/π` **exactly when**
`(r/α)^{3/2} = e` and `L = 2/3`, giving `\tilde C_{1,α} = 3E_{1/2}eBα^{3/2}/2`. Independently,
`x = e^{2/3}` is the minimiser of `x^{3/2}/log x` (value `3e/2`), i.e. the optimal radius for
this argument.

**The `log log|T|` coefficient is `2`, and both contributions must be counted.** Two
`log log|T|` terms arrive — `1/3` from `prop_Richert` and `1` from `leong_log_zeta_one_bound` —
and *both* are divided by `L = 2/3`, giving `1/2 + 3/2 = 2`. Taking `1/L` alone would drop the
`prop_Richert` contribution. (`circularregions1` divides both as well: its
`C2 = c_{2,r}/(Lπ) + 1/L`.)

The radius is therefore at most `e^{2/3} = 1.9477…`, comfortably below the threshold
`r_max = 4.4735…` at which the source's derivation of the `\tilde C_{3,α}` bound breaks down (see
`c4_lt_of_le_exp_two_thirds` and `Ctilde3_lt_of_le_one`), so that argument is valid as written.

The hypotheses `0 < α`, `α ≤ 1` and `2 < T` are the tex's own. `2 < T` is what
`integraloutside_bound` and `leong_log_zeta_one_bound` need, and it gives `r < T`, i.e. `ζ`'s
pole lies outside the disc. The `prop_Richert` window is `[T-r, T+r]`, as in that proposition.

### References
tex: Theorem `\ref{thm:circularregions2}` (Theorem 18); Proposition `\ref{prop:Richert}`
(Proposition 12); Proposition `\ref{prop:integraloutside}` (Proposition 15); Proposition
`\ref{prop:jensenbound}` (Proposition 6). External: Leong, arXiv:2405.04869.

### Dependencies
**Depends on:** `Ctilde1`, `Ctilde3`, `Ehalf`, `Ncirc`, `c4`, `exp_two_thirds_lt_two`,
`integraloutside_bound`, `intervalIntegrable_log_zeta_circle`, `jensenCircleAvg`, `jensenbound`,
`leong_log_zeta_one_bound`, `one_lt_exp_two_thirds`, `prop_Richert`.
**Used by:** none — the Richert-type track is stated but not yet consumed downstream. -/
theorem circularregions2 {T α B A : ℝ} (hα : α ≤ 1) (hα0 : 0 < α) (hT : 2 < T)
    (H : ∀ σ t : ℝ, 1 - σ < Real.exp (2 / 3) * α →
        t ∈ Set.Icc (T - Real.exp (2 / 3) * α) (T + Real.exp (2 / 3) * α) →
      Real.log ‖riemannZeta (σ + t * Complex.I)‖
        < B * (1 - σ) ^ (3 / 2 : ℝ) * Real.log |T| + (2 / 3) * Real.log (Real.log |T|) + A) :
    (Ncirc (1 + T * Complex.I) α : ℝ)
      ≤ Ctilde1 α B / Real.pi * Real.log |T| + 2 * Real.log (Real.log |T|)
        + Ctilde3 α A := by
  have hpi := Real.pi_pos
  set r : ℝ := Real.exp (2/3) * α with hr_def
  have hr0 : 0 < r := by positivity
  have hαr : α < r := by
    rw [hr_def]; nlinarith [one_lt_exp_two_thirds]
  have hrT : r < T := by
    rw [hr_def]; nlinarith [exp_two_thirds_lt_two, one_lt_exp_two_thirds]
  have hTabs : |T| = T := abs_of_pos (by linarith)
  have hball : (1 : ℂ) ∉ Metric.closedBall ((1 : ℂ) + (T:ℂ) * Complex.I) r := by
    simp only [Metric.mem_closedBall, Complex.dist_eq, not_le]
    have : (1 : ℂ) - (1 + (T:ℂ) * Complex.I) = -((T:ℂ) * Complex.I) := by ring
    rw [this, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real]
    simp [hTabs]
    linarith
  have hζ : riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have hjb := jensenbound (s := (1 : ℂ) + (T:ℂ) * Complex.I) (r := r) (α := α) hαr hα0 hball hζ
  have hL : Real.log (r / α) = 2/3 := by
    rw [hr_def, mul_div_assoc, div_self (ne_of_gt hα0), mul_one, Real.log_exp]
  rw [hL] at hjb
  have hsplit : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      = (1 / (2 * Real.pi)) * (∫ θ in (-Real.pi/2)..(Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        + (1 / (2 * Real.pi)) * (∫ θ in (Real.pi/2)..(3*Real.pi/2),
          Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖) := by
    have hI := (intervalIntegral.integral_add_adjacent_intervals
        (a := -Real.pi/2) (b := Real.pi/2) (c := 3*Real.pi/2)
        (f := fun θ : ℝ => Real.log ‖riemannZeta ((1 : ℂ) + (T:ℂ) * Complex.I
            + (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖)
        (intervalIntegrable_log_zeta_circle _ _ _ _)
        (intervalIntegrable_log_zeta_circle _ _ _ _)).symm
    rw [jensenCircleAvg, hI, mul_add]
  have hin := integraloutside_bound (t := T) (r := r) hr0 hT hrT
  have hout := prop_Richert (T := T) (r := r) (B := B) (A := A) hr0 H
  have hleong := leong_log_zeta_one_bound (t := T) (by rw [hTabs]; linarith)
  have hnum : jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
      - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
      ≤ (Ehalf * B * r ^ (3/2 : ℝ) / Real.pi * Real.log |T|
          + (1/3) * Real.log (Real.log |T|) + A / 2)
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388) := by
    rw [hsplit]
    have : -Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖
        ≤ Real.log (Real.log |T|) + Real.log 29.388 := by
      convert hleong using 3
    linarith
  have hexp : (Real.exp (2/3)) ^ (3/2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_one_rpow (2/3 : ℝ), ← Real.rpow_mul (Real.exp_pos 1).le]
    norm_num
  have hstep : (jensenCircleAvg ((1 : ℂ) + (T:ℂ) * Complex.I) r
        - Real.log ‖riemannZeta ((1:ℂ) + (T:ℂ) * Complex.I)‖) / (2/3)
      ≤ ((Ehalf * B * r ^ (3/2 : ℝ) / Real.pi * Real.log |T|
          + (1/3) * Real.log (Real.log |T|) + A / 2)
        + c4 r + (Real.log (Real.log |T|) + Real.log 29.388)) / (2/3) := by
    gcongr
  refine hjb.trans (hstep.trans (le_of_eq ?_))
  rw [Ctilde1, Ctilde3, hr_def, Real.mul_rpow (Real.exp_pos _).le hα0.le, hexp]
  field_simp
  ring

-- The tex quotes this constant as `(3e/2π)E_{1/2} ∼ 1.134375 < 1.3478`, Ford's comparison
-- constant from `\cite[Lemma 4.2]{Ford2002,Ford2019}`. `Ctilde1` is always consumed
-- divided by `π` (`circularregions2`, `Ctilde1_lt`), so the `π` normalisation lines up with the
-- quoted constant.
--
-- `1.134375` cannot be reused verbatim as a strict upper bound: the true value is
-- `1.1343754886…` (see `Ehalf_bound` below), which *exceeds* `1.134375` by about `4.9×10⁻⁷`.
-- That is not an error in the source, which writes `∼ 1.134375` — an approximation, and indeed
-- the correct 7-significant-figure rounding. It only means Lean needs a genuine upper bound
-- where the tex claims an approximation, so `1.1343755` is stated instead (true with a thin but
-- positive margin). The qualitative point is unaffected, since `1.1343755 < 1.3478`; `1.135`
-- would give a more comfortable margin if a coarser constant were ever preferred.
/-- **`3e·Ehalf/(2π) < 1.1343755`** — a finite numerical fact, held as the hypothesis field
`NumericCertificates.ehalf_bound`.

### Summary of Proof
The body reads the class field `NumericCertificates.ehalf_bound`. `Ehalf` has the classical
closed form `Γ(1/4)²/(6√(2π))`, a Beta-function evaluation (`Ehalf = (1/2)B(5/4,1/2)`). That
closed form — rather than direct numerical quadrature of `Ehalf`'s defining integral, which is
unreliable because `cos(θ)^{3/2}` has a branch point at `θ = π/2` where `cos` vanishes — is what
`Code/verify_Ehalf_bound.sage` evaluates by certified ball arithmetic, giving the bound with
margin `≈1.14×10⁻⁸`. Run `sage Code/verify_Ehalf_bound.sage` to reproduce.

### Lean Notes
**Why this is a certificate and not a Lean proof.** The margin is genuinely thin:
`3e·Ehalf/(2π) = 1.1343754886…` against the asserted `1.1343755`, about `1.14×10⁻⁸` of room. A
Lean proof would run through the Beta evaluation `Ehalf = (1/2)B(5/4,1/2)` (Mathlib has
`Real.betaIntegral`, `Real.Gamma` and the Beta–Gamma relation) and then need roughly nine correct
digits of `Γ(1/4) = 3.62561…`, which Mathlib cannot enclose and `norm_num` cannot supply.

The bound is stated as `1.1343755` rather than the source's printed `1.134375` because the latter
is smaller than the true value by `≈4.9×10⁻⁷` and so is not a valid strict upper bound; the
qualitative conclusion is unaffected, since all that is used downstream is `< 1.3478`.

### References
tex: the constant `(3e/2π)E_{1/2} ∼ 1.134375` quoted in the remark following Proposition
`\ref{prop:Richert}` (Proposition 12). The source's `∼` is an approximation and is correct as
written at 7 significant figures; only Lean's need for a strict upper bound forces the extra
digit.

**Independent numeric check.** `Code/indep_mpmath_constants.py` block [A] recomputes `Ehalf`
three separate ways (the Beta function `(1/2)B(5/4,1/2)`, direct tanh-sinh quadrature of the
defining integral, and `Γ(1/4)²/(6√(2π))`), all agreeing to 50 digits, and finds
`3e·Ehalf/(2π) = 1.13437548863…`, i.e. a margin of `1.137×10⁻⁸` below `1.1343755`.

### Dependencies
**Depends on:** `Ehalf`, `Hypotheses.NumericCertificates.ehalf_bound`.
**Used by:** `Ctilde1_lt`. -/
theorem Ehalf_bound : 3 * Real.exp 1 * Ehalf / (2 * Real.pi) < 1.1343755 := by
  unfold Ehalf
  exact NumericCertificates.ehalf_bound

/-- **`\tilde C_{1,α}/π < 1.1343755·B·α^{3/2}`.**

### Summary of Proof
Unfold `Ctilde1`, whose `π`-normalised value is `(3e/2π)E_{1/2}·B·α^{3/2}`, and apply the
numeric bound `Ehalf_bound` (`3e·E_{1/2}/(2π) < 1.1343755`) with the positive factor
`B·α^{3/2}`.

### Lean Notes
The constant `1.1343755` is one digit longer than the source's printed `1.134375`, because Lean
needs a strict upper bound where the source writes an approximation. See `Ehalf_bound`.

### References
tex: the constant `\tilde C_{1,α}` of Theorem `\ref{thm:circularregions2}` (Theorem 18), and the
approximation `(3e/2π)E_{1/2} ∼ 1.134375` in the remark following Proposition
`\ref{prop:Richert}` (Proposition 12).

### Dependencies
**Depends on:** `Ctilde1`, `Ehalf`, `Ehalf_bound`.
**Used by:** none — recorded as the explicit numeric form of `\tilde C_{1,α}`. -/
theorem Ctilde1_lt (α B : ℝ) (hB : 0 < B) (hα : 0 < α) :
    Ctilde1 α B / Real.pi < 1.1343755 * B * α ^ (3 / 2 : ℝ) := by
  unfold Ctilde1
  have hα32 : (0:ℝ) < α ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
  have hpos : (0:ℝ) < B * α ^ (3 / 2 : ℝ) := mul_pos hB hα32
  calc 3 * Ehalf * Real.exp 1 * B * α ^ (3 / 2 : ℝ) / 2 / Real.pi
      = (3 * Real.exp 1 * Ehalf / (2 * Real.pi)) * (B * α ^ (3 / 2 : ℝ)) := by
        field_simp
    _ < 1.1343755 * (B * α ^ (3 / 2 : ℝ)) := mul_lt_mul_of_pos_right Ehalf_bound hpos
    _ = 1.1343755 * B * α ^ (3 / 2 : ℝ) := by ring

/-- **`0 < γ² + 2γ₁`** (`γ` = Euler–Mascheroni, `γ₁` = the first Stieltjes constant).

### Summary of Proof
This is the coefficient of `z` in the Laurent estimate
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`; its value is
`0.18754623284036522…`, and `Code/verify_stieltjes_combo_bound.sage` certifies that by ball
arithmetic.

The Lean proof needs no numerics of its own. Mathlib gives `γ > 1/2`, so `γ² > 1/4` and it
suffices that `γ₁ > -1/8`; that is `Definitions.neg_one_eighth_lt_stieltjesConstant1`, which
comes from the refined (trapezoid) lower bracket at `m = 5`, where the value `-0.07485…` clears
`-1/8` with margin `0.05`.

### Lean Notes
**A strictly stronger version exists elsewhere in the project.**
`Background/LogDerivZetaLaurent.stieltjes_combo_numeric_bounds` proves the two-sided
`0.15 ≤ γ²+2γ₁ ≤ 0.20`. The two are not one declaration because of the import direction:
`Jensen/RectangularBounds.lean` imports `Background/LogDerivZetaLaurent.lean`, so
`LogDerivZetaLaurent` cannot import `JensenBounds`. Unifying them would mean hoisting the fact
into a common ancestor (`Definitions.lean`, where `stieltjesConstant1` itself lives, is the
natural home).

### References
No direct tex counterpart as a numbered claim — the positivity is used implicitly wherever the
source's truncated-Laurent estimate for `-ζ'/ζ` is applied, e.g. in the derivation of
`\tilde C_{3,α}` in Theorem `\ref{thm:circularregions2}` (Theorem 18).

### Dependencies
**Depends on:** `stieltjesConstant1`, `neg_one_eighth_lt_stieltjesConstant1`.
**Used by:** `c4_lt_of_le_exp_two_thirds`, `stieltjes_combo_bound`. -/
theorem stieltjes_combo_pos :
    0 < Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have h1 := neg_one_eighth_lt_stieltjesConstant1
  nlinarith [hg, h1]

/-- **`e^{2/3}·(γ²+2γ₁)/8 ≤ (π-2)γ/(2π)`**, the threshold condition behind `\tilde C_{3,α}`.

### Summary of Proof
This is the threshold condition that makes the correction term dropped in the source's derivation
of `\tilde C_{3,α}` genuinely non-positive, at the largest radius that occurs,
`r = e^{2/3}α ≤ e^{2/3} = 1.9477…`. Certified by ball arithmetic in
`Code/verify_stieltjes_combo_bound.sage` (`0.0456604… ≤ 0.1048687…`, margin `≈ 0.0592`),
which also certifies the *exact* cutoff
`r_max = 4(π-2)γ/(π(γ²+2γ₁)) = 4.4735371439521245600…`. Run
`sage Code/verify_stieltjes_combo_bound.sage` to reproduce.

The Lean proof reduces it to a single finite computation. Clearing denominators, the claim is
`e^{2/3}·(γ²+2γ₁)·2π ≤ 8(π-2)γ`.  Using `e^{2/3} < 2` (because `2/3 < log 2`), positivity of
`γ²+2γ₁` (`stieltjes_combo_pos`), and `γ₁ ≤ 1/100`, it suffices that
`π(γ² - 2γ + 1/50) + 4γ ≤ 0`.  The bracket is negative for `γ ∈ (1/2, 2/3)`, so `π > 3.14`
(`Real.pi_gt_d2`) is the worst case, leaving `3.14γ² - 2.28γ + 0.0628 ≤ 0`, whose roots are
`0.0287` and `0.6974` — and `γ ∈ (1/2, 2/3)` sits strictly inside, with `0.031` to spare at the
top.

### Lean Notes
The bound `γ₁ ≤ 1/100` that the computation needs is supplied, with a lot to spare, by
`LogDerivZetaLaurent.stieltjesConstant1_upper_bound` (`γ₁ ≤ -0.0724`, from the Euler–Maclaurin
bracket at `m = 16`).

**Stated at radius `e^{2/3}`, which is where the margin is comfortable.** With
`circularregions2`'s radius `e^{2/3}α ≤ 1.9477…` the slack is `0.059`. At a radius near `e^{3/2}`
the same argument would leave a razor-thin `1.9×10⁻⁵`, and only after restricting to
`α ≤ 0.998`.

### References
tex: the derivation of `\tilde C_{3,α}` in Theorem `\ref{thm:circularregions2}` (Theorem 18).

### Dependencies
**Depends on:** `stieltjesConstant1`, `stieltjes_combo_pos`,
`LogDerivZetaLaurent.stieltjesConstant1_upper_bound`.
**Used by:** `c4_lt_of_le_exp_two_thirds`. -/
theorem stieltjes_combo_bound :
    Real.exp (2 / 3) * (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1) / 8
      ≤ (Real.pi - 2) * Real.eulerMascheroniConstant / (2 * Real.pi) := by
  have hglo := Real.one_half_lt_eulerMascheroniConstant
  have hghi := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := Real.pi_gt_d2
  have hpipos := Real.pi_pos
  have hSpos := stieltjes_combo_pos
  have hSle : Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1
      ≤ Real.eulerMascheroniConstant ^ 2 + 1 / 50 := by
    have := stieltjesConstant1_upper_bound
    linarith
  have hexp : Real.exp (2 / 3) < 2 := by
    have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    rw [← h2]
    exact Real.exp_lt_exp.mpr (by linarith [Real.log_two_gt_d9])
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  -- `e^{2/3}·S·2π ≤ 2·S·2π`, since `S > 0` and `π > 0`.
  have step1 : Real.exp (2 / 3)
      * (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1) * (2 * Real.pi)
      ≤ 2 * (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1) * (2 * Real.pi) := by
    have hfac : (0 : ℝ) ≤ (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1)
        * (2 * Real.pi) := by positivity
    nlinarith [hexp, hfac]
  -- `π·(γ² - 2γ + 1/50)` is worst at the smallest admissible `π`, the bracket being negative.
  have hq : Real.eulerMascheroniConstant ^ 2 - 2 * Real.eulerMascheroniConstant + 1 / 50 < 0 := by
    nlinarith [hglo, hghi]
  have hpiq : Real.pi
      * (Real.eulerMascheroniConstant ^ 2 - 2 * Real.eulerMascheroniConstant + 1 / 50)
      ≤ 3.14 * (Real.eulerMascheroniConstant ^ 2 - 2 * Real.eulerMascheroniConstant + 1 / 50) :=
    mul_le_mul_of_nonpos_right (le_of_lt hpi) (le_of_lt hq)
  have hquad : 3.14 * (Real.eulerMascheroniConstant ^ 2 - 2 * Real.eulerMascheroniConstant + 1 / 50)
      + 4 * Real.eulerMascheroniConstant ≤ 0 := by
    nlinarith [mul_pos (sub_pos.2 hglo) (sub_pos.2 hghi)]
  nlinarith [step1, hSle, hpiq, hquad, hpipos]

/-- **`c4 r < ½·log‖ζ(1+r)‖ + ½·log 2` for `0 < r ≤ e^{2/3}`**, by the source's own route.

### Summary of Proof
Obtained from `integraloutside_bound_secondary` — hence from the Laurent estimate
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`, valid on `(0,2]` — together with
`stieltjes_combo_pos` and `stieltjes_combo_bound`. The restriction `r ≤ e^{2/3} < 2` is what
keeps that estimate in range, and it is all Theorem `\ref{thm:circularregions2}` (Theorem 18)
needs, since it assumes `α ≤ 1`.

The correction terms `-(π-2)rγ/(2π) + r²(γ²+2γ₁)/8` cancel to something non-positive precisely
when `r(γ²+2γ₁)/8 ≤ (π-2)γ/(2π)`, i.e. when `r ≤ r_max = 4.4735…`. The radius in play,
`e^{2/3} = 1.9477…`, is comfortably inside.

### Lean Notes
The gain in the correction is **linear** in `r` and the loss **quadratic**, which is what creates
the cutoff. The margin is not generous in absolute terms: a radius of `e^{3/2} = 4.4817…` would
sit `0.18%` *above* `r_max`, and this route would fail outright.

### References
tex: Proposition `\ref{prop:integraloutside}` (Proposition 15); the derivation of
`\tilde C_{3,α}` in Theorem `\ref{thm:circularregions2}` (Theorem 18). Numerics certified in
`Code/verify_stieltjes_combo_bound.sage`.

### Dependencies
**Depends on:** `c4`, `integraloutside_bound_secondary`, `stieltjesConstant1`,
`stieltjes_combo_bound`, `stieltjes_combo_pos`.
**Used by:** `Ctilde3_lt_of_le_one`. -/
theorem c4_lt_of_le_exp_two_thirds {r : ℝ} (hr : 0 < r) (hrle : r ≤ Real.exp (2 / 3)) :
    c4 r < (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖ + Real.log 2 / 2 := by
  have hpi := Real.pi_pos
  set K : ℝ := Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 with hK
  have hKpos : 0 < K := stieltjes_combo_pos
  have hb := stieltjes_combo_bound
  -- `e^{2/3} = 1.9477… ≤ 2`, since `2/3 < log 2 = 0.6931…`
  have hexp : Real.exp (2 / 3 : ℝ) ≤ 2 := by
    have hlog := Real.log_two_gt_d9
    have h2 : Real.exp (2 / 3 : ℝ) < Real.exp (Real.log 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h2
    exact h2.le
  have h := integraloutside_bound_secondary hr (hrle.trans hexp)
  have hdrop : r ^ 2 * K / 8
      ≤ (Real.pi - 2) * r / (2 * Real.pi) * Real.eulerMascheroniConstant := by
    have h1 : r * (r * K / 8) ≤ r * (Real.exp (2/3) * K / 8) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      have : r * K ≤ Real.exp (2/3) * K := mul_le_mul_of_nonneg_right hrle hKpos.le
      linarith
    have h2 : r * (Real.exp (2/3) * K / 8)
        ≤ r * ((Real.pi - 2) * Real.eulerMascheroniConstant / (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hb hr.le
    have h3 : (Real.pi - 2) * r / (2 * Real.pi) * Real.eulerMascheroniConstant
        = r * ((Real.pi - 2) * Real.eulerMascheroniConstant / (2 * Real.pi)) := by
      field_simp
    nlinarith [h1, h2]
  linarith

/-- **`\tilde C_{3,α}` bound by the source's own route**, valid for `0 < α ≤ 1` — exactly the
range Theorem `\ref{thm:circularregions2}` (Theorem 18) assumes.

### Summary of Proof
`c4_lt_of_le_exp_two_thirds` at `r = e^{2/3}α`; at `α ≤ 1` the radius `e^{2/3}α ≤ e^{2/3}` stays
inside that lemma's range.

### Lean Notes
The dependency chain is short: `integraloutside_bound_secondary`, hence the Laurent estimate
`LogDerivZetaLaurent.neg_logDeriv_zeta_bound_of_claim_two`, together with `stieltjes_combo_pos`
and `stieltjes_combo_bound`. The restriction `α ≤ 1` is Theorem `\ref{thm:circularregions2}`
(Theorem 18)'s own, and it is exactly what keeps the radius `e^{2/3}α` inside
`c4_lt_of_le_exp_two_thirds`'s range.

### References
tex: Theorem `\ref{thm:circularregions2}` (Theorem 18) and its derivation of
`\tilde C_{3,α}`.

### Dependencies
**Depends on:** `Ctilde3`, `c4_lt_of_le_exp_two_thirds`.
**Used by:** none — recorded as the source-faithful route to the same bound. -/
theorem Ctilde3_lt_of_le_one {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (A : ℝ) :
    Ctilde3 α A
      < 3 * A / 4 + 3 / 4 * Real.log ‖riemannZeta (1 + Real.exp (2 / 3) * α : ℂ)‖
        + 3 * Real.log 2 / 4 + 3 * Real.log 29.388 / 2 := by
  have hr : (0:ℝ) < Real.exp (2 / 3) * α := by positivity
  have hrle : Real.exp (2 / 3) * α ≤ Real.exp (2 / 3) := by
    nlinarith [Real.exp_pos (2/3 : ℝ)]
  have h := c4_lt_of_le_exp_two_thirds hr hrle
  rw [Ctilde3]
  push_cast at h ⊢
  linarith
