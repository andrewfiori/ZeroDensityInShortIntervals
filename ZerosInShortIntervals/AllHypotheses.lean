/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Hypotheses
import ZerosInShortIntervals.HalvingConvention
import ZerosInShortIntervals.PositiveProportion

/-! # The headline results under one bundled hypothesis

Five classes carry everything this development assumes:

| class | what it holds | where |
|---|---|---|
| `LiteratureInputs` | 12 published results, transcribed | `Hypotheses.lean` |
| `BrentStirlingInputs` | Brent's two Stirling expansions, with remainders | `ExternalFacts.lean` |
| `NumericCertificates` | 2 arb-certified constants, Mathlib-only | `Hypotheses.lean` |
| `LaurentCertificate` | 1 mpmath bound on `ζ'/ζ` near `s = 1` | `LogDerivZetaLaurent.lean` |
| `InterpolationCertificates` | 3 arb windows, cases (1a)(1b)(1c) | `BackgroundZetaBounds.lean` |
| `Hcompact2Certificates` | 5 arb windows, the case-(2) family | `BackgroundZetaBounds.lean` |

(Six rows, five names plus the case-(2) split; they are separate because each is declared at the
first point in the import graph where its statements can be written, and because literature and
numerics deserve to be weighed differently.)

Internal lemmas carry whichever of them are in scope, because Lean includes an instance-implicit
section variable in every theorem of a file that declares one.  That is noise.  This file removes
it from the results a reader actually cites: `ZeroDensityHypotheses` bundles all six, and each
headline statement below is restated with that single binder.

**This is the shape a Palomar submission wants.**  The Challenge module states the result with its
hypotheses in the signature, the Solution proves it, and the proof term depends on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`.
`#print axioms` on any theorem in this file confirms that.

Nothing here is new mathematics; every proof is `exact` the corresponding result. -/

/-- **Every unproved input of this development, bundled.**

Extending the six classes makes each of them available from one instance, so a statement that
depends on the whole development needs one binder rather than six.

### Summary of Proof
A class; no proof.  It has no instance in this repository, by design.

### Lean Notes
An instance of `ZeroDensityHypotheses` is exactly: the twelve literature results, Brent's two
Stirling expansions, and the eleven numerical facts certified in `Code/`.  A reader who
accepts those accepts the headline theorems below; a reader who does not can see precisely what
is being asked.

### References
`Assumptions.txt` for the full inventory.

### Dependencies
**Depends on:** `Hypotheses.LiteratureInputs`, `Hypotheses.NumericCertificates`,
`BrentStirlingInputs`, `LaurentCertificate`, `InterpolationCertificates`,
`Hcompact2Certificates`.
**Used by:** every statement in this file. -/
class ZeroDensityHypotheses extends
    LiteratureInputs, BrentStirlingInputs, NumericCertificates, LaurentCertificate,
    InterpolationCertificates, Hcompact2Certificates

/-- **Theorem `\ref{thm:main-jensen}` (Theorem 2, Jensen mechanism)**, under the single bundled
hypothesis.

### Summary of Proof
`MainTheorem.mainJensen`.

### References
tex: `\ref{thm:main-jensen}` (Theorem 2).

### Dependencies
**Depends on:** `MainTheorem.mainJensen`, `ZeroDensityHypotheses`.
**Used by:** none. -/
theorem mainJensen' [ZeroDensityHypotheses] {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r)
    (hr1 : r < 1) (hα : α < alphaBoundTodo) (ht : Real.exp 1 ≤ t) (hh0 : 0 ≤ h)
    (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    (Nrect (t - h) (t + h) α : ℝ) < UJensen α r h t + EJensen α r t :=
  mainJensen hα0 hαr hr1 hα ht hh0 hh

/-- **Theorem `\ref{thm:main-littlewood}` (Theorem 3, Littlewood mechanism)**, under the single
bundled hypothesis.

### Summary of Proof
`MainTheorem.mainLittlewood`.

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3).

### Dependencies
**Depends on:** `MainTheorem.mainLittlewood`, `ZeroDensityHypotheses`.
**Used by:** none. -/
theorem mainLittlewood' [ZeroDensityHypotheses] {α r h t : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα16 : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : Real.exp (Real.exp 1) ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t - h) * Complex.I) ≠ 0) :
    (Nrect (t - h) (t + h) α : ℝ) < ULittlewood α r h t k + ELittlewood α r t :=
  mainLittlewood hα0 hrα hα16 hk hk' ht hh0 hh hzf_p hzf_m

/-- **Corollary `\ref{cor:main-jensen}` (Corollary 4)** in the tex's counting convention, under
the single bundled hypothesis.

### Summary of Proof
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`.

### References
tex: `\ref{cor:main-jensen}` (Corollary 4), Table `\ref{tab:C2J}` (Table 8).

### Dependencies
**Depends on:** `HalvingConvention.mainPositiveProportionCorollary_jensen_half`.
**Used by:** none. -/
theorem mainPositiveProportionCorollary_jensen_half' [ZeroDensityHypotheses]
    {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Jensen α r h0 t0 :=
  mainPositiveProportionCorollary_jensen_half hα0 hrα hr1 hα ht0 hh0 hh ht hht

/-- **Corollary `\ref{cor:main-littlewood}` (Corollary 5)** in the tex's counting convention,
under the single bundled hypothesis.

### Summary of Proof
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`.

### References
tex: `\ref{cor:main-littlewood}` (Corollary 5), Table `\ref{tab:C2L}` (Table 9).

### Dependencies
**Depends on:** `HalvingConvention.mainPositiveProportionCorollary_littlewood_half`.
**Used by:** none. -/
theorem mainPositiveProportionCorollary_littlewood_half' [ZeroDensityHypotheses]
    {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Littlewood α r h0 t0 k :=
  mainPositiveProportionCorollary_littlewood_half hα0 hrα hα hk hk' ht0 hh0 hh ht hht

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Jensen mechanism**, in the tex's prose form
and under the single bundled hypothesis: at least a `C_{α,h₀,t₀}` fraction of the window's zeros
have real part in `[α, 1-α]`.

### Summary of Proof
`HalvingConvention.simpleProportionCorollary_jensen_prose`.

### Lean Notes
This is the statement a Palomar Challenge module should carry for the Jensen mechanism.  The
factor of two it relies on is proved (`Reflection.lean`), not assumed.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `HalvingConvention.simpleProportionCorollary_jensen_prose`.
**Used by:** none. -/
theorem simpleProportionCorollary_jensen_prose' [ZeroDensityHypotheses] {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpJensen α r h0 t0 :=
  simpleProportionCorollary_jensen_prose hα0 hrα hr1 hα ht0 hh0 hh ht hht

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1), Littlewood mechanism**, in the tex's prose
form and under the single bundled hypothesis.

### Summary of Proof
`HalvingConvention.simpleProportionCorollary_littlewood_prose`.

### Lean Notes
This is the mechanism behind fourteen of the fifteen rows of Table `\ref{table:chat}` (Table 1),
including the abstract's `α = 1/16`, `h₀ = 100`, `t₀ = 10^100` example at `0.1374`.  It is the
statement a Palomar Challenge module should carry.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `HalvingConvention.simpleProportionCorollary_littlewood_prose`.
**Used by:** none. -/
theorem simpleProportionCorollary_littlewood_prose' [ZeroDensityHypotheses]
    {α r h t h0 t0 : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpLittlewood α r h0 t0 k :=
  simpleProportionCorollary_littlewood_prose hα0 hrα hα hk hk' ht0 hh0 hh ht hht

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1) in the tex's existential form, with the
constant proved positive**, under the single bundled binder.

### Summary of Proof
`exact` of `PositiveProportion.positiveProportion_littlewood`.

### Lean Notes
This is the statement the Palomar `Challenge`/`Solution` pair carries, and the only one of the
headline results that asserts anything about the SIGN of its constant.  The hypothesis
`4 * A1 α r k < 1` is exact rational arithmetic once `α`, `r`, `k` are fixed; see
`simpleProportionCorollary_littlewood_sixteenth'` for an instance.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), including "for `h₀` and `t₀` sufficiently large" and its
description of `C` as positive.

### Dependencies
**Depends on:** `PositiveProportion.positiveProportion_littlewood`.
**Used by:** none. -/
theorem positiveProportion_littlewood' [ZeroDensityHypotheses] {α r : ℝ} {k : ℤ}
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (hA1 : 4 * A1 α r k < 1) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood α r h0 t0 k ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > CsimpLittlewood α r h0 t0 k :=
  positiveProportion_littlewood hα0 hrα hα hk hk' hA1

/-- **The same at `α = 1/16`, `r = 1/5`, `k = 1`**, under the single bundled binder: a fully
concrete positive-proportion statement with no free parameters.

### Summary of Proof
`exact` of `PositiveProportion.positiveProportion_littlewood_sixteenth`.

### Lean Notes
There `4A₁ = 16/25 < 1` and the limiting constant is `1 - 4A₁ = 9/25 = 0.36`.  Nothing numeric is
assumed for the positivity; the chord data are explicit rationals.

### References
tex: the `α = 1/16` rows of Table `\ref{table:chat}` (Table 1).

### Dependencies
**Depends on:** `PositiveProportion.positiveProportion_littlewood_sixteenth`.
**Used by:** none. -/
theorem simpleProportionCorollary_littlewood_sixteenth' [ZeroDensityHypotheses] :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood (1 / 16) (1 / 5) h0 t0 1 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) (1 / 16) / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood (1 / 16) (1 / 5) h0 t0 1 :=
  positiveProportion_littlewood_sixteenth

/-- **Corollary `\ref{cor:simpmain}` (Corollary 1) with no side condition**, under the single
bundled binder: for every `α` in the paper's range `0 < α < 1/6`, the radius `r = 1/2` works.

### Summary of Proof
`exact` of `PositiveProportion.positiveProportion_littlewood_half`.

### Lean Notes
This supersedes `positiveProportion_littlewood'`, which carries a `4 * A1 α r k < 1` hypothesis.
At `r = 1/2` that inequality reads `(1/3)/(1/2 - α) < 1`, i.e. exactly `α < 1/6`, so the witness
can be supplied instead of assumed.  The parametrised version is kept because other `r` give
larger constants.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), whose hypothesis is exactly `0 < α < 1/6`.

### Dependencies
**Depends on:** `PositiveProportion.positiveProportion_littlewood_half`.
**Used by:** none. -/
theorem positiveProportion_littlewood_half' [ZeroDensityHypotheses] {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood α (1 / 2) h0 t0 0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood α (1 / 2) h0 t0 0 :=
  positiveProportion_littlewood_half hα0 hα

/-- **The tex's sentence**, under the single bundled binder: for `0 < α < 1/6` the proportion is
bounded below by an explicitly computable positive constant.

### Summary of Proof
`exact` of `PositiveProportion.positiveProportion_of_lt_sixth`.

### References
tex: `\ref{cor:simpmain}` (Corollary 1), first sentence.

### Dependencies
**Depends on:** `PositiveProportion.positiveProportion_of_lt_sixth`.
**Used by:** none. -/
theorem positiveProportion_of_lt_sixth' [ZeroDensityHypotheses] {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ C h0 t0 : ℝ, 0 < C ∧ (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > C :=
  positiveProportion_of_lt_sixth hα0 hα
