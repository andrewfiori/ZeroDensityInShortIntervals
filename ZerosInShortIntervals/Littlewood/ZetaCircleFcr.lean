/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.JensenScaleConstants
import ZerosInShortIntervals.Jensen.JensenBounds
import ZerosInShortIntervals.Background.ExternalFacts

/-! # A concrete `Fcr` bound for `ζ`-circles centred at `c = 1`

This file constructs the `Fcr` function needed to instantiate `ArgIntegrals.arg_integrals` (and
hence `Littlewood.littlewood_argsetup`'s `arg_integrals`-fed pieces) with `f = riemannZeta`,
`c = 1`, matching `ZerosInShortIntervals.tex`'s own construction ("we take `c=1` and
define `F_{c,r}(θ)` to be `log ζ(r cos θ)` when `0 ≤ θ ≤ π/2` and defined as in the proof of
Proposition `\ref{prop:jensen-easy}`" (Proposition 8) — §`\ref{sec:littlewoodshortapp}` (§3.2)).

**`FcrZeta` itself is just the honest pointwise maximum** (`hFcr_bound` is then a triviality); all
the work goes into bounding its *integral* over `[0,π]`, split into three pieces matching the
`cos θ ≥ 0` / `cos θ < 0` split used throughout `JensenBounds.lean`:

* **`θ ∈ [0,π/2)`** (`cos θ > 0`, i.e. `Re(1+r e^{iθ}) > 1`): both `ζ(1+re^{iθ}±iT)` are dominated
  by the *real-axis* value `ζ(1+r cos θ)` (`Definitions.zeta_norm_le_zeta_re`), giving a
  `T`-independent bound. Its own integral over `[0,π/2]` is exactly `π · c4 r`
  (`JensenBounds.c4`), by `JensenBounds.integral_log_zeta_cos_quarter_eq_c4` — the single lemma
  that also supplies `JensenBounds.integraloutside_bound`'s closed-form step, so the analytic
  content is proved once and cited twice (see `integral_log_zeta_real_axis_eq_c4` below).
* **`θ ∈ (π/2,π]`** (`cos θ < 0`): both `ζ(1+re^{iθ}+iT)` (directly) and `ζ(1+re^{iθ}-iT)` (via the
  conjugate identity `ζ(1+re^{iθ}-iT) = conj(ζ(1+re^{-iθ}+iT))` plus the majorant's own mirror
  symmetry `arcMaj_pi_sub_tight`) are bounded by the *same* `arcMaj_tight` piecewise majorant used
  in `JensenBounds.jensen_easy_upper_quarter_tight` — **no new closed-form derivation is needed
  here**, `JensenBounds.half_arc_bound_tight` gives the integral directly.
* **`θ = π/2`** (and its mirror `θ = -π/2`, a single point, contributing nothing to any integral):
  `Re(1+iT) = 1` exactly, where neither of the above applies (the pole boundary). Handled via
  `ExternalFacts.bellotti_richert_bound` at `σ = 1`, which gives a clean closed form there.
-/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

open Complex in
/-- **`Fcr` for the `ζ`-circle of radius `r` around `c = 1`, at height `T`: the honest pointwise
maximum of `log‖ζ(1+re^{iθ}+iT)‖` and `log‖ζ(1+re^{iθ}-iT)‖`.**

### Summary of Proof
A definition: the pointwise `max` of the two branches `log‖ζ(1+re^{iθ}+iT)‖` and
`log‖ζ(1+re^{iθ}-iT)‖`, so that the majorant hypothesis `hFcr_bound` of
`ArgIntegrals.arg_integrals` holds by `le_rfl`. All the content is in bounding its integral.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `FcrZeta_even`, `FcrZeta_inside_integral_le`, `FcrZeta_integral_le`,
`FcrZeta_intervalIntegrable`, `FcrZeta_le_inside`, `FcrZeta_outside_integral`,
`FcrZeta_shift_intervalIntegrable`, `littlewoodshort`, `littlewoodshort_tight`. -/
noncomputable def FcrZeta (r T θ : ℝ) : ℝ :=
  max (Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + (T : ℂ) * Complex.I)‖)
      (Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (T : ℂ) * Complex.I)‖)

/-- **`conj(θ·I) = (-θ)·I` for real `θ`, viewed in `ℂ`.**

### Summary of Proof
`map_mul` followed by `Complex.conj_ofReal` and `Complex.conj_I`, then `push_cast; ring`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `conj_exp_real_mul_I`. -/
private theorem conj_real_mul_I (θ : ℝ) :
    (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

/-- **`conj(exp(θ·I)) = exp((-θ)·I)` for real `θ`.**

### Summary of Proof
`Complex.exp_conj` moves the conjugation inside the exponential; `conj_real_mul_I` evaluates it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `conj_real_mul_I`.
**Used by:** `FcrZeta_even`, `FcrZeta_term_swap`. -/
private theorem conj_exp_real_mul_I (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, conj_real_mul_I]

/-- **The two terms of `FcrZeta` swap under `θ ↦ -θ`, via `ζ(s̄) = conj(ζ(s))`: this is the
conjugate-symmetry fact underlying both `FcrZeta_even` and the "outside" pointwise bound below.**

### Summary of Proof
The point `1 + re^{-iθ} + iT` is the conjugate of `1 + re^{iθ} - iT` (`conj_exp_real_mul_I`
plus `Complex.conj_I`), so `riemannZeta_conj` and `RCLike.norm_conj` identify the two norms.

### References
No tex counterpart.

### Dependencies
**Depends on:** `conj_exp_real_mul_I`.
**Used by:** `FcrZeta_even`, `FcrZeta_minus_le_arcMaj`. -/
theorem FcrZeta_term_swap (r T θ : ℝ) :
    Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) + (T : ℂ) * Complex.I)‖
      = Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (T : ℂ) * Complex.I)‖ := by
  have hconj : (1 : ℂ) + (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) + (T : ℂ) * Complex.I
      = (starRingEnd ℂ)
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (T : ℂ) * Complex.I) := by
    rw [map_sub, map_add, map_one, map_mul, Complex.conj_ofReal, conj_exp_real_mul_I,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, riemannZeta_conj, RCLike.norm_conj]

/-- **`FcrZeta` is even.**

### Summary of Proof
`θ ↦ -θ` swaps the two arguments of the `max`: one direction is `FcrZeta_term_swap`, the other
the same conjugation argument run on the `-iT` branch; `max_comm` finishes.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_term_swap`, `conj_exp_real_mul_I`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem FcrZeta_even (r T θ : ℝ) : FcrZeta r T (-θ) = FcrZeta r T θ := by
  unfold FcrZeta
  rw [FcrZeta_term_swap]
  have h2 : Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - (T : ℂ) * Complex.I)‖
      = Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + (T : ℂ) * Complex.I)‖ := by
    have hconj2 : (1 : ℂ) + (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - (T : ℂ) * Complex.I
        = (starRingEnd ℂ)
          (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + (T : ℂ) * Complex.I) := by
      rw [map_add, map_add, map_one, map_mul, Complex.conj_ofReal, conj_exp_real_mul_I,
        map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconj2, riemannZeta_conj, RCLike.norm_conj]
  rw [h2]
  exact max_comm _ _

/-- **`arcMaj_tight` depends on `φ` only through `Real.sin φ`.**

### Summary of Proof
`arcMaj_tight` mentions `φ` only inside a `Real.sin`, so `unfold` and rewrite with `h`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcMaj_tight`.
**Used by:** `FcrZeta_minus_le_arcMaj`. -/
theorem arcMaj_tight_congr_sin {k : ℤ} {r t φ φ' : ℝ} (h : Real.sin φ = Real.sin φ') :
    arcMaj_tight k r t φ = arcMaj_tight k r t φ' := by
  unfold arcMaj_tight; rw [h]

set_option maxHeartbeats 300000 in
-- the `ring` normalization of a `Complex.exp`-laden reordering pushes this past the default budget.
/-- **The `+iT` branch of `FcrZeta`, on the outside quarter, is bounded by `arcMaj_tight`: literally
`arc_pointwise_le_maj_sin_tight`, up to reordering the `+` (that lemma states the point as
`1 + T·I + r·exp(...)`, `FcrZeta` as `1 + r·exp(...) + T·I`).**

### Summary of Proof
`JensenBounds.arc_pointwise_le_maj_sin_tight` applied verbatim, after a `ring` step reordering
the sum: that lemma states the point as `1 + T·I + r·exp(...)`, `FcrZeta` as
`1 + r·exp(...) + T·I`.

### Lean Notes
The `ring` normalisation of a `Complex.exp`-laden reordering is what pushes this declaration past
the default `maxHeartbeats`.

Carries `arc_pointwise_le_maj_sin_tight`'s non-vanishing hypothesis `hz` — `ζ` non-zero at the
mirror point `r sin φ + i(T + r cos φ)`; it is discharged almost everywhere in
`FcrZeta_outside_integral`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arcMaj_tight`, `arc_pointwise_le_maj_sin_tight`.
**Used by:** `FcrZeta_minus_le_arcMaj`, `FcrZeta_outside_integral`. -/
theorem FcrZeta_plus_le_arcMaj {k : ℤ} {r T φ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hT : (13:ℝ) < T)
    (hlog : r / (T - r) < Real.log T)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((T + r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I) + (T : ℂ) * Complex.I)‖
      ≤ arcMaj_tight k r T φ := by
  rw [show (1 : ℂ) + (r : ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I)
        + (T : ℂ) * Complex.I
      = 1 + (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I) by
    ring]
  exact arc_pointwise_le_maj_sin_tight hr0 hr1 hT hlog hs1 hs2 hz

/-- **The `-iT` branch, on the outside quarter, is also bounded by the *same* `arcMaj_tight`: via
`FcrZeta_term_swap` (`ζ(1+re^{iθ}-iT) = conj(ζ(1+re^{-iθ}+iT))`) applied at `-φ-π`, whose sine
equals `sin φ`, so `arc_pointwise_le_maj_sin_tight` applies with the *same* window and
`arcMaj_tight_congr_sin` gives the same majorant value.**

### Summary of Proof
Set `ψ = -φ-π`, so `sin ψ = sin φ` and `cos ψ = -cos φ`. `FcrZeta_term_swap` at `φ+π/2` turns
the `-iT` branch into the `+iT` branch at `ψ+π/2`, where `FcrZeta_plus_le_arcMaj` applies with
the *same* window (the window constrains only `sin`), and `arcMaj_tight_congr_sin` identifies
the two majorant values.

### Lean Notes
Because the bound is applied at `ψ = -φ - π`, where `cos ψ = -cos φ`, the non-vanishing
hypothesis `hz` is the one for the *other* mirror point, `r sin φ + i(T - r cos φ)`; it is
discharged almost everywhere in `FcrZeta_outside_integral`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta_plus_le_arcMaj`, `FcrZeta_term_swap`, `arcMaj_tight`,
`arcMaj_tight_congr_sin`.
**Used by:** `FcrZeta_outside_integral`. -/
theorem FcrZeta_minus_le_arcMaj {k : ℤ} {r T φ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hT : (13:ℝ) < T)
    (hlog : r / (T - r) < Real.log T)
    (hs1 : (1 - sigma (k+1)) / r < Real.sin φ) (hs2 : Real.sin φ ≤ (1 - sigma k) / r)
    (hz : riemannZeta (((r * Real.sin φ : ℝ) : ℂ)
        + ((T + -r * Real.cos φ : ℝ) : ℂ) * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp (((φ + Real.pi/2 : ℝ) : ℂ) * Complex.I) - (T : ℂ) * Complex.I)‖
      ≤ arcMaj_tight k r T φ := by
  set ψ : ℝ := -φ - Real.pi with hψ_def
  have hsin : Real.sin ψ = Real.sin φ := by
    rw [hψ_def]
    rw [show -φ - Real.pi = -(φ + Real.pi) by ring, Real.sin_neg, Real.sin_add_pi]
    ring
  have hcs : Real.cos ψ = -Real.cos φ := by
    rw [hψ_def, show -φ - Real.pi = -(φ + Real.pi) by ring, Real.cos_neg, Real.cos_add]
    simp
  -- The mirrored angle `ψ` sees the reflected circle traversed the other way, so the
  -- non-vanishing hypothesis transported to `ψ` is the one stated with `-r cos φ`.
  have hzψ : riemannZeta (((r * Real.sin ψ : ℝ) : ℂ)
      + ((T + r * Real.cos ψ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    rw [hsin, hcs, show (T + r * -Real.cos φ : ℝ) = T + -r * Real.cos φ by ring]
    exact hz
  have hswap := FcrZeta_term_swap r T (φ + Real.pi/2)
  have hle := FcrZeta_plus_le_arcMaj hr0 hr1 hT hlog (φ := ψ) (k := k)
    (by rwa [hsin]) (by rwa [hsin]) hzψ
  rw [arcMaj_tight_congr_sin hsin] at hle
  have heq : ((-(φ + Real.pi/2) : ℝ) : ℂ) = ((ψ + Real.pi/2 : ℝ) : ℂ) := by
    rw [hψ_def]; push_cast; ring
  rw [heq] at hswap
  rw [← hswap]
  exact hle

/-- **`FcrZeta r T`, shifted by `c`, is interval integrable: each branch is
`intervalIntegrable_log_zeta_circle_shift`, and their max is integrable
(`MeasureTheory.Integrable.sup`).**

### Summary of Proof
`FcrZeta r T`, shifted by `c`, is interval integrable: each branch is
`intervalIntegrable_log_zeta_circle_shift`, and their max is integrable
(`MeasureTheory.Integrable.sup`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `intervalIntegrable_log_zeta_circle_shift`.
**Used by:** `FcrZeta_intervalIntegrable`, `FcrZeta_outside_integral`. -/
theorem FcrZeta_shift_intervalIntegrable (r T c a b : ℝ) :
    IntervalIntegrable (fun φ : ℝ => FcrZeta r T (φ + c)) MeasureTheory.volume a b := by
  have h1 : IntervalIntegrable
      (fun φ : ℝ => Real.log ‖riemannZeta
        (1 + (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I))‖)
      MeasureTheory.volume a b :=
    intervalIntegrable_log_zeta_circle_shift (1 + (T : ℂ) * Complex.I) r c a b
  have h2 : IntervalIntegrable
      (fun φ : ℝ => Real.log ‖riemannZeta
        (1 - (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I))‖)
      MeasureTheory.volume a b :=
    intervalIntegrable_log_zeta_circle_shift (1 - (T : ℂ) * Complex.I) r c a b
  have hmax : IntervalIntegrable
      (fun φ : ℝ =>
        max (Real.log ‖riemannZeta
              (1 + (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I))‖)
            (Real.log ‖riemannZeta
              (1 - (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I))‖))
      MeasureTheory.volume a b :=
    ⟨h1.1.sup h2.1, h1.2.sup h2.2⟩
  apply hmax.congr
  intro φ _
  simp only []
  unfold FcrZeta
  rw [show (1 : ℂ) + (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I)
      = 1 + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I) + (T : ℂ) * Complex.I by ring,
    show (1 : ℂ) - (T : ℂ) * Complex.I + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I)
      = 1 + (r : ℂ) * Complex.exp (((φ + c : ℝ) : ℂ) * Complex.I) - (T : ℂ) * Complex.I by ring]

/-- **The outside-quarter integral bound.** `∫_{π/2}^π FcrZeta r T θ dθ ≤ c1(r)·log T
+ c2(r)·log log T + c3(r) + (π/2)·arcErr_tight r T`.

### Summary of Proof
On the outside quarter `θ ∈ (π/2,π]` we have `cos θ < 0`, and *both* branches of the `max`
defining `FcrZeta` are bounded by the **same** `arcMaj_tight` piecewise majorant already used in
`JensenBounds.jensen_easy_upper_quarter_tight`: the `+iT` branch directly
(`FcrZeta_plus_le_arcMaj`), and the `-iT` branch via the conjugate identity
`ζ(1+re^{iθ}-iT) = conj(ζ(1+re^{-iθ}+iT))` together with the majorant's mirror symmetry
(`FcrZeta_minus_le_arcMaj`). So no new closed-form derivation is needed here —
`JensenBounds.half_arc_bound_tight` supplies the integral directly, and the result is exactly
`jensen_easy_upper_quarter_tight`'s own closed form.

### Lean Notes
`half_arc_bound_tight`'s domination hypothesis is supplied almost everywhere. Both branches need
`ζ` non-zero at a mirror point — the `+iT` branch at `r sin φ + i(T + r cos φ)`, the `-iT` branch
at `r sin φ + i(T - r cos φ)` — and each fails only on a null set of `φ`, by
`ae_zeta_arc_ne_zero` with `c = r` and `c = -r` respectively. This is where the reflection
hypothesis inherited from `zetalessthanhalf_upper` stops on the `FcrZeta` track.

### References
No tex counterpart. This realises part of the sentence in `\ref{thm:littlewoodshort}`
(Theorem 32)'s proof that defines `F_{c,r}` "as in the proof of `\ref{prop:jensen-easy}`
(Proposition 8)"; the closed form it lands on is `\ref{thm:circularregions1}` (Theorem 16)'s.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_minus_le_arcMaj`, `FcrZeta_plus_le_arcMaj`,
`FcrZeta_shift_intervalIntegrable`, `ae_zeta_arc_ne_zero`, `arcErr_tight`, `c1`, `c2`, `c3`,
`half_arc_bound_tight`.
**Used by:** `FcrZeta_integral_le`. -/
theorem FcrZeta_outside_integral {r T : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hT : (13:ℝ) < T)
    (hlog : r / (T - r) < Real.log T) :
    (∫ θ in (Real.pi/2)..Real.pi, FcrZeta r T θ)
      ≤ c1 r * Real.log T + c2 r * Real.log (Real.log T) + c3 r
        + (Real.pi/2) * arcErr_tight r T := by
  have hchg : (∫ φ in (0:ℝ)..(Real.pi/2), FcrZeta r T (φ + Real.pi/2))
      = ∫ θ in (Real.pi/2)..Real.pi, FcrZeta r T θ := by
    rw [intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := Real.pi/2)
      (fun θ : ℝ => FcrZeta r T θ) (Real.pi/2),
      zero_add, show (Real.pi/2 + Real.pi/2 : ℝ) = Real.pi by ring]
  rw [← hchg]
  refine half_arc_bound_tight hr0 hr1
    (fun u v => FcrZeta_shift_intervalIntegrable r T (Real.pi/2) u v) ?_
  -- Both branches need `ζ` non-zero at a mirror point — the `+iT` branch at
  -- `r sin φ + i(T + r cos φ)`, the `-iT` branch at `r sin φ + i(T - r cos φ)`.  Each fails only
  -- on a null set of `φ` (`ae_zeta_arc_ne_zero`), so the domination is assumed a.e.
  intro m
  filter_upwards [ae_zeta_arc_ne_zero (b := r) (c := r) hr0.ne' hr0.ne' T,
    ae_zeta_arc_ne_zero (b := r) (c := -r) hr0.ne' (neg_ne_zero.2 hr0.ne') T]
    with φ hzp hzm hs1 hs2
  exact max_le
    (FcrZeta_plus_le_arcMaj hr0 hr1 hT hlog hs1 hs2 hzp)
    (FcrZeta_minus_le_arcMaj hr0 hr1 hT hlog hs1 hs2 hzm)

/-- **The inside-quarter pointwise bound.** For `cos θ ≥ 0` (so `Re(1+re^{iθ}) ≥ 1`), both
`ζ(1+re^{iθ}±iT)` are dominated in norm by the real-axis value `ζ(1+r cos θ)`
(`Definitions.zeta_norm_le_zeta_re`), regardless of the sign of the imaginary shift `±T`.**

### Summary of Proof
Write the point as `(1+r cos θ) + i(sgn·T + r sin θ)`, whose real part exceeds `1` when
`cos θ > 0`; `Definitions.zeta_norm_le_zeta_re` then dominates its `ζ`-value by the real-axis
value, and `Real.log_le_log` transports the bound (the degenerate `‖ζ‖ = 0` case uses
`log_zeta_norm_pos`, since Lean's `log 0 = 0`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_zeta_norm_pos`, `zeta_norm_le_zeta_re`.
**Used by:** `FcrZeta_le_inside`. -/
theorem FcrZeta_inside_pointwise {r T θ sgn : ℝ} (hr0 : 0 < r) (hsgn : sgn = 1 ∨ sgn = -1)
    (hcos : 0 < Real.cos θ) :
    Real.log ‖riemannZeta
        (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + sgn * (T : ℂ) * Complex.I)‖
      ≤ Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖ := by
  have hpt : (1 : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + sgn * (T : ℂ) * Complex.I
      = ((1 + r * Real.cos θ : ℝ) : ℂ) + ((sgn * T + r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    rcases hsgn with h | h <;> (rw [h]; push_cast; ring)
  rw [hpt]
  have hreeq : ((((1 + r * Real.cos θ : ℝ) : ℂ)
        + ((sgn * T + r * Real.sin θ : ℝ) : ℂ) * Complex.I).re : ℝ) = 1 + r * Real.cos θ := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
  have hre : (1 : ℝ) <
      (((1 + r * Real.cos θ : ℝ) : ℂ) + ((sgn * T + r * Real.sin θ : ℝ) : ℂ) * Complex.I).re := by
    rw [hreeq]; nlinarith [mul_pos hr0 hcos]
  have hz := zeta_norm_le_zeta_re hre
  have hrw : ((((1 + r * Real.cos θ : ℝ) : ℂ)
        + ((sgn * T + r * Real.sin θ : ℝ) : ℂ) * Complex.I).re : ℝ) = 1 + r * Real.cos θ :=
    hreeq
  rw [hrw] at hz
  rcases eq_or_lt_of_le (norm_nonneg (riemannZeta
      (((1 + r * Real.cos θ : ℝ) : ℂ) + ((sgn * T + r * Real.sin θ : ℝ) : ℂ) * Complex.I)))
    with h0 | h0
  · rw [← h0, Real.log_zero]
    exact (log_zeta_norm_pos (σ := 1 + r * Real.cos θ) (by nlinarith)).le
  · exact Real.log_le_log h0 hz

/-- **`FcrZeta r T` is interval integrable (no shift).**

### Summary of Proof
`FcrZeta_shift_intervalIntegrable` at `c = 0`, then `simpa`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_shift_intervalIntegrable`.
**Used by:** `FcrZeta_inside_integral_le`, `FcrZeta_integral_le`,
`LittlewoodShort.littlewoodshort`, `LittlewoodShort.littlewoodshort_tight`. -/
theorem FcrZeta_intervalIntegrable (r T a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => FcrZeta r T θ) MeasureTheory.volume a b := by
  have h := FcrZeta_shift_intervalIntegrable r T 0 a b
  simpa using h

/-- **Interval integrability of the "inside" real-axis majorant.**

### Summary of Proof
`θ ↦ ζ(1 + r cos θ)` is meromorphic on the segment (`meromorphicAt_riemannZeta` composed with
the real-analytic `θ ↦ 1 + r cos θ`), and `MeromorphicOn.intervalIntegrable_log_norm` applies.

### References
No tex counterpart.

### Dependencies
**Depends on:** `meromorphicAt_riemannZeta`.
**Used by:** `FcrZeta_inside_integral_le`. -/
theorem intervalIntegrable_log_zeta_real_axis (r a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖)
      MeasureTheory.volume a b := by
  have hmero : MeromorphicOn (fun θ : ℝ => riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ))
      (Set.uIcc a b) := by
    intro u _
    have hinner : AnalyticAt ℝ (fun θ : ℝ => ((1 + r * Real.cos θ : ℝ) : ℂ)) u := by
      apply AnalyticAt.comp (g := fun x : ℝ => ((x : ℝ) : ℂ)) (f := fun θ : ℝ => 1 + r * Real.cos θ)
      · exact Complex.ofRealCLM.analyticAt _
      · exact analyticAt_const.add (analyticAt_const.mul (Real.analyticAt_cos (x := u)))
    exact (meromorphicAt_riemannZeta _).comp_analyticAt hinner
  exact hmero.intervalIntegrable_log_norm

/-- **`FcrZeta` itself, on the inside quarter (`cos θ > 0`), is bounded by the real-axis value:
`max_le` combining both signs of `FcrZeta_inside_pointwise`.**

### Summary of Proof
`FcrZeta` itself, on the inside quarter (`cos θ > 0`), is bounded by the real-axis value:
`max_le` combining both signs of `FcrZeta_inside_pointwise`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_inside_pointwise`.
**Used by:** `FcrZeta_inside_integral_le`. -/
theorem FcrZeta_le_inside {r T θ : ℝ} (hr0 : 0 < r) (hcos : 0 < Real.cos θ) :
    FcrZeta r T θ ≤ Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖ := by
  have h1 := FcrZeta_inside_pointwise (T := T) hr0 (Or.inl rfl) hcos
  have h2 := FcrZeta_inside_pointwise (T := T) hr0 (Or.inr rfl) hcos
  rw [show ((1:ℝ):ℂ) * (T : ℂ) * Complex.I = (T:ℂ) * Complex.I by push_cast; ring] at h1
  rw [show ((-1:ℝ):ℂ) * (T : ℂ) * Complex.I = -((T : ℂ) * Complex.I) by push_cast; ring] at h2
  exact max_le h1 h2

set_option maxHeartbeats 300000 in
-- the singleton-exclusion measure-theory bookkeeping pushes this past the default budget.
/-- **The inside-quarter integral bound.** `∫_0^{π/2} FcrZeta r T θ dθ ≤ ∫_0^{π/2} log‖ζ(1+r cos
θ)‖dθ`.

### Summary of Proof
`intervalIntegral.integral_mono_ae_restrict` with the pointwise bound `FcrZeta_le_inside`, which
holds on all of `[0,π/2]` except the single boundary point `θ = π/2` — there `cos θ = 0` and
neither branch's pointwise argument applies — and a singleton is null.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_intervalIntegrable`, `FcrZeta_le_inside`,
`intervalIntegrable_log_zeta_real_axis`.
**Used by:** `FcrZeta_integral_le`. -/
theorem FcrZeta_inside_integral_le {r T : ℝ} (hr0 : 0 < r) :
    (∫ θ in (0:ℝ)..(Real.pi/2), FcrZeta r T θ)
      ≤ ∫ θ in (0:ℝ)..(Real.pi/2), Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖ := by
  have hpi := Real.pi_pos
  refine intervalIntegral.integral_mono_ae_restrict (by linarith)
    (FcrZeta_intervalIntegrable r T 0 (Real.pi/2))
    (intervalIntegrable_log_zeta_real_axis r 0 (Real.pi/2)) ?_
  have hfin : MeasureTheory.volume ({Real.pi/2} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hfin] with θ hθ hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], lt_of_le_of_ne hmem.2 hθ⟩
  exact FcrZeta_le_inside hr0 hcos

/-- **The boundary point `θ = ±π/2` bound.** `log‖ζ(1+iT)‖ ≤ log(70.7) + (2/3) log log T`, from
`ExternalFacts.bellotti_richert_bound` at `σ = 1` exactly (where the `(1-σ)^{3/2}` exponent
vanishes, collapsing the bound to a pure `log T` power) — this is the one point neither the
"inside" (`Definitions.zeta_norm_le_zeta_re`, needs `Re > 1` strictly) nor "outside"
(`chordIdx`-based, needs `Re < 1` strictly) argument reaches.**

### Summary of Proof
At `σ = 1` the exponent `(1-σ)^{3/2}` in `ExternalFacts.bellotti_richert_bound` vanishes, so the
bound collapses to `‖ζ(1+iT)‖ ≤ 70.7·(log T)^{2/3}`; take logs (`Real.log_le_log`, legitimate
since `ζ(1+iT) ≠ 0` by `riemannZeta_ne_zero_of_one_le_re`) and split with `Real.log_mul`,
`Real.log_rpow`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bellotti_richert_bound`.
**Used by:** none — the single point `θ = π/2` is null, so `FcrZeta_integral_le` never needs a
value there. Kept because it is the only bound available at `Re s = 1` exactly. -/
theorem FcrZeta_boundary_le {T : ℝ} (hT : (3:ℝ) < T) :
    Real.log ‖riemannZeta (1 + (T : ℂ) * Complex.I)‖
      ≤ Real.log 70.7 + (2/3) * Real.log (Real.log T) := by
  have hTabs : |T| = T := abs_of_pos (by linarith)
  have hb := bellotti_richert_bound (σ := 1) (t := T)
    (by norm_num) (by rw [hTabs]; linarith)
  rw [hTabs, show (1 : ℝ) - 1 = 0 by ring,
    Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0), mul_zero, Real.rpow_zero, mul_one] at hb
  have hζpos : (0:ℝ) < ‖riemannZeta (1 + (T : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simp))
  have hlogT1 : (1:ℝ) < Real.log T := by
    have : Real.exp 1 < T := by
      have h1 := Real.exp_one_lt_d9
      linarith
    have := Real.log_lt_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hlogTpos : (0:ℝ) < Real.log T := by linarith
  calc Real.log ‖riemannZeta (1 + (T : ℂ) * Complex.I)‖
      ≤ Real.log (70.7 * Real.log T ^ (2/3 : ℝ)) := Real.log_le_log hζpos hb
    _ = Real.log 70.7 + Real.log (Real.log T ^ (2/3 : ℝ)) :=
        Real.log_mul (by norm_num) (by positivity)
    _ = Real.log 70.7 + (2/3) * Real.log (Real.log T) := by
        rw [Real.log_rpow hlogTpos]

/-- **The inside-half integral equals `π·c_{4,r}`:**
`∫_0^{π/2} log‖ζ(1+r cos θ)‖ dθ = π·c4 r`.

### Summary of Proof
Substitute `u = cos θ`, then integrate by parts against `arcsin`. The resulting integrand has a
logarithmic singularity at `u = 0`, where `ζ` has its pole; the standard argument is that the log
singularity is integrable and cancels against the pole's contribution, leaving the closed form
`c_{4,r}` that the tex records in `\ref{prop:integraloutside}` (Proposition 15).

### Lean Notes
This identity and `JensenBounds.integraloutside_bound`'s closed-form step are the same piece of
real analysis, and both are instances of the single lemma
`JensenBounds.integral_log_zeta_cos_quarter_eq_c4`, which carries the analytic content once.
This statement is its immediate instance.

The consolidating lemma lives in `JensenBounds` because this file imports that one and not
conversely, and because `c4` is defined there. It needs only `0 < r`, so the `r < 1` hypothesis
here is not used — it is kept for signature compatibility with this file's callers.

### References
tex: `c_{4,r}` is defined in `\ref{prop:integraloutside}` (Proposition 15); this identity is the
evaluation that proposition asserts.

### Dependencies
**Depends on:** `c4`, `integral_log_zeta_cos_quarter_eq_c4`.
**Used by:** `FcrZeta_integral_le`. -/
theorem integral_log_zeta_real_axis_eq_c4 (r : ℝ) (hr0 : 0 < r) (_hr1 : r < 1) :
    (∫ θ in (0:ℝ)..(Real.pi/2), Real.log ‖riemannZeta ((1 + r * Real.cos θ : ℝ) : ℂ)‖)
      = Real.pi * c4 r :=
  integral_log_zeta_cos_quarter_eq_c4 hr0

/-- **The full `FcrZeta` integral bound**, combining the inside quarter (`c4 r`), the outside
quarter (`c1 r, c2 r, c3 r, arcErr_tight`), and the single boundary point (measure zero, no
contribution).

### Summary of Proof
The inside quarter is `integral_log_zeta_real_axis_eq_c4`, the outside quarter is bounded by
`c1 r, c2 r, c3 r, arcErr_tight`, and the boundary point contributes nothing.

### Lean Notes
`intervalIntegral.integral_add_adjacent_intervals` splits `[0,π]` at `π/2`
(`FcrZeta_intervalIntegrable` on each half). The split point `θ = π/2`, where `Re(1+iT) = 1`
exactly and neither quarter's pointwise argument applies, is a single point and so contributes
nothing to either integral; `FcrZeta_boundary_le` records the bound available there.

### References
No tex counterpart.

### Dependencies
**Depends on:** `FcrZeta`, `FcrZeta_inside_integral_le`, `FcrZeta_intervalIntegrable`,
`FcrZeta_outside_integral`, `arcErr_tight`, `c1`, `c2`, `c3`, `c4`,
`integral_log_zeta_real_axis_eq_c4`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem FcrZeta_integral_le {r T : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hT : (13:ℝ) < T)
    (hlog : r / (T - r) < Real.log T) :
    (∫ θ in (0:ℝ)..Real.pi, FcrZeta r T θ)
      ≤ Real.pi * c4 r + c1 r * Real.log T + c2 r * Real.log (Real.log T) + c3 r
        + (Real.pi/2) * arcErr_tight r T := by
  have hsplit : (∫ θ in (0:ℝ)..Real.pi, FcrZeta r T θ)
      = (∫ θ in (0:ℝ)..(Real.pi/2), FcrZeta r T θ)
        + ∫ θ in (Real.pi/2)..Real.pi, FcrZeta r T θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (FcrZeta_intervalIntegrable r T 0 (Real.pi/2))
      (FcrZeta_intervalIntegrable r T (Real.pi/2) Real.pi)).symm
  rw [hsplit]
  have h1 := FcrZeta_inside_integral_le (T := T) hr0
  rw [integral_log_zeta_real_axis_eq_c4 r hr0 hr1] at h1
  have h2 := FcrZeta_outside_integral hr0 hr1 hT hlog
  linarith
