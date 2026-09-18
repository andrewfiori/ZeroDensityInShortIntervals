/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Common.RealLogBounds

/-! # The project's unproved inputs, as hypotheses

Everything this development assumes rather than proves is collected here and in three companion
classes declared further down the import graph (`ExternalFacts.BrentStirlingInputs`,
`LogDerivZetaLaurent.LaurentCertificate`, `BackgroundZetaBounds.InterpolationCertificates`), each
placed at the first point where its statements can be written.  A result that needs one of them
says so in its signature; nothing is assumed silently.

**Two kinds, deliberately kept apart.**

* `LiteratureInputs` — results taken from other people's papers.  These are ordinary mathematics,
  published and refereed; the project's claim is only that it has transcribed them correctly, and
  each field's docstring names the source.  The full provenance discussion (edition, page, which
  numbered statement, and any discrepancy found while checking) stays on the corresponding
  theorem in `Background/ExternalFacts.lean`, which is where a reader should look.
* `NumericCertificates` — finite numerical facts that are true, that the project has certified
  outside Lean by ball arithmetic (Sage/arb) or independent high-precision evaluation (mpmath),
  and that today's Mathlib cannot express as a proof term: there is no verified evaluation of `ζ`,
  and no sharp enclosure of `Γ(1/4)`.  The certifying script is named in each field's docstring
  and lives in `Code/`.

The two are on very different footings and a reader is entitled to weigh them differently, which
is why they are not one class.

**Why classes and not axioms.**  An `axiom` is invisible at the use site and makes
`#print axioms` the only way to discover it.  A class field appears in the signature of every
result that depends on it, and a proved `Solution` module that instantiates nothing depends on no
axiom at all — which is what the Palomar Registry requires of a submission.  Conditional results
state their hypotheses.

**The bundle.** `ZerosInShortIntervals.AllHypotheses.ZeroDensityHypotheses` gathers all five classes
into one, for the headline statements. -/

/-- **The results this project takes from the literature.**

Each field is a published theorem, transcribed.  The full citation, the edition checked, and any
discrepancy found during checking are recorded on the corresponding theorem in
`Background/ExternalFacts.lean` (and, for `riemannZeta_lowest_zero_height`, in
`Background/LogDerivZetaLaurent.lean`); the one-line pointers below say only which paper each
field comes from.

### Summary of Proof
A class; no proof.  It has no instance in this repository, by design: every theorem that needs one
of these results carries `[LiteratureInputs]`, so the dependency is visible in its type.

### Lean Notes
`Prop`-valued, so instances are proof-irrelevant and two of them cannot disagree.

### References
tex: the paper's own citations; `refs.bib` at the repository root carries each one's DOI or arXiv
identifier.

### Dependencies
**Depends on:** `Definitions.N`, `Definitions.Nrect`, `Common.RealLogBounds.bwM`.
**Used by:** the twelve `Background.ExternalFacts` theorems that read its fields, and transitively
the headline theorems.  `LogDerivZetaLaurent.riemannZeta_lowest_zero_height` reads the last
field. -/
class LiteratureInputs : Prop where
  /-- Hiary–Patel–Yang, Eq. (3.23): the explicit sixth-power bound on the critical line for
  `|t| > 10^12`.  See `ExternalFacts.hiary_eq_3_23`. -/
  hiary_eq_3_23: ∀ {t : ℝ}, (10 : ℝ) ^ (12 : ℕ) < |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.478013 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 3.853165 * |t| ^ (1 / 6 : ℝ) - 2.914229
  /-- Revers, Remark 3.1: the same shape with sharper constants, from `7·10^11`.
  See `ExternalFacts.revers_remark31`. -/
  revers_remark31 : ∀ {t : ℝ}, (7 : ℝ) * 10 ^ (11 : ℕ) ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) - 21.5437
  /-- Revers: the clean subconvexity bound `0.611 |t|^{1/6} log|t|` valid from `|t| ≥ 3`.
  See `ExternalFacts.revers_subconvexity_bound`. -/
  revers_subconvexity_bound : ∀ {t : ℝ}, 3 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.611 * |t| ^ (1 / 6 : ℝ) * Real.log |t|
  /-- Patel–Yang: the sub-Weyl bound `66.7 t^{27/164}` on the critical line.
  See `ExternalFacts.patel_yang_subweyl_bound`. -/
  patel_yang_subweyl_bound : ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 66.7 * t ^ (27 / 164 : ℝ)
  /-- Yang, *Explicit bounds on ζ in the critical strip*, Theorem 1.1, for `k ≥ 4`.
  See `ExternalFacts.yang_critical_strip_bound`. -/
  yang_critical_strip_bound : ∀ {k : ℕ}, 4 ≤ k → ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 - (k : ℝ) / (2 ^ k - 2) + t * Complex.I)‖
      ≤ 1.546 * t ^ ((1 : ℝ) / (2 ^ k - 2)) * Real.log t
  /-- Bellotti's explicit form of Richert's bound inside the critical strip.
  See `ExternalFacts.bellotti_richert_bound`. -/
  bellotti_richert_bound : ∀ {σ t : ℝ}, σ ∈ Set.Icc (1 / 2 : ℝ) 1 → 3 ≤ |t| →
    ‖riemannZeta (σ + t * Complex.I)‖
      ≤ 70.7 * |t| ^ (4.438 * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ)
  /-- Leong, *Explicit estimates for the logarithmic derivative of ζ*, Theorem 4: a lower bound
  for `|ζ(1+it)|`.  See `ExternalFacts.leong_log_zeta_one_bound`. -/
  leong_log_zeta_one_bound : ∀ {t : ℝ}, 2 ≤ |t| →
    -Real.log (‖riemannZeta (1 + t * Complex.I)‖) ≤ Real.log (Real.log |t|) + Real.log 29.388
  /-- Fiori, *A note on the Phragmén–Lindelöf theorem*, J. Math. Anal. Appl. **559** (2026) no. 1,
  130404, doi:10.1016/j.jmaa.2026.130404,
  Theorem 7 — the interpolation principle the appendix's `ζ` bounds are built on.  **This is the
  cited paper's Theorem 7, not this project's Proposition 8.**
  See `ExternalFacts.fiori_phragmenLindelof`. -/
  fiori_phragmenLindelof : ∀ {a b : ℝ}, a < b → ∀ {r : ℕ} (G : Fin r → ℂ → ℂ),
    (∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b}) →
    (∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G i s)) →
    ∀ {C1 C2 C3 : ℝ}, 0 < C1 → 0 < C2 → 0 < C3 → C3 < Real.pi / (b - a) →
    (∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      C1 * Real.exp (-C2 * Real.exp (C3 * |t|)) < ‖G i (σ + t * Complex.I)‖) →
    ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f {s : ℂ | s.re ∈ Set.Icc a b} →
    (∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖ < C1 * Real.exp (C2 * Real.exp (C3 * |t|))) →
    ∀ {α β : Fin r → ℝ}, (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) →
    (∀ t : ℝ, ‖f (a + t * Complex.I)‖ ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i) →
    (∀ t : ℝ, ‖f (b + t * Complex.I)‖ ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i) →
    ∀ {T0 : ℝ},
    (∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b))) →
    (∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖f (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a))) →
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖
        ≤ (∏ i, ‖G i (σ + t * Complex.I)‖ ^ α i) ^ ((b - σ) / (b - a))
            * (∏ i, ‖G i (σ + t * Complex.I)‖ ^ β i) ^ ((σ - a) / (b - a))
  /-- Platt–Trudgian: the Riemann hypothesis is verified up to height `H₀ = 3·10^12`.
  See `ExternalFacts.platt_trudgian_verified_below`. -/
  platt_trudgian_verified_below : ∀ (ρ : ℂ), 0 < ρ.im → ρ.im ≤ 3 * 10 ^ (12 : ℕ) →
    riemannZeta ρ = 0 → ρ.re = 1 / 2
  /-- Farzanfard, *Explicit zero density for ζ* (MSc thesis, U. of Lethbridge): the classical
  zero-density bound on an interval, used only for the `h ≫ t^{2/3}` regime.
  See `ExternalFacts.farzanfard_zero_density_interval`. -/
  farzanfard_zero_density_interval : ∀ {α T₁ T₂ : ℝ},
    α ∈ Set.Icc (0 : ℝ) (1 / 4) → 3 * 10 ^ (12 : ℕ) ≤ T₁ → T₁ ≤ T₂ →
    (Nrect T₁ T₂ α : ℝ)
      ≤ 12.45321 * T₂ ^ ((8 : ℝ) / 3 * α) * Real.log T₂ ^ (3 + 2 * α)
        + 3.869 * Real.log T₂ ^ (2 : ℕ)
  /-- Bellotti–Wong, Corollary 1.3: `|N(T) - M(T)| ≤ 0.097 log T + 4.954` for `T ≥ 1`, the lower
  bound for the denominator of every proportion statement.
  See `ExternalFacts.bellotti_wong_cor_1_3`. -/
  bellotti_wong_cor_1_3 : ∀ {T : ℝ}, 1 ≤ T →
    |((N T : ℤ) : ℝ) - bwM T| ≤ 0.097 * Real.log T + 4.954
  /-- The lowest nontrivial zero of `ζ` has ordinate above `14` (classical; it is `14.1347…`).
  See `LogDerivZetaLaurent.riemannZeta_lowest_zero_height`. -/
  riemannZeta_lowest_zero_height : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    14 < |ρ.im|

/-- **The finite numerical facts this project certifies outside Lean**, in the cases whose
statements need nothing beyond Mathlib.  The remaining certificates need project definitions to
state and live in `LogDerivZetaLaurent.LaurentCertificate` and
`BackgroundZetaBounds.InterpolationCertificates`.

Every field is a true statement about explicit constants, verified by interval (ball) arithmetic
or independent high-precision evaluation; the script is named in the field's docstring.  None is
expressible as a Lean proof term today: Mathlib has no verified evaluation of `ζ` and no sharp
enclosure of `Γ(1/4)`, and the margins here are `10^{-17}` and `10^{-8}`.

### Summary of Proof
A class; no proof.  See `Assumptions.txt` Part 1 for the full table, including the margins.

### Lean Notes
Stating these as hypotheses rather than leaving them open does not make them more or less true.
What it buys is visibility: every result that rests on one carries it in its own type, so a reader
can see the dependence without running `#print axioms`, and the project's proof terms are free of
`sorryAx`.  Both fields are `Prop`-valued, so instances are proof-irrelevant.

### References
`Code/` for the certifying scripts; `Assumptions.txt` Part 1 for the classification.

### Dependencies
**Depends on:** none (Mathlib only).
**Used by:** `RectangularBounds.integral_log_zeta_Ioi_one_lt`, `JensenBounds.Ehalf_bound`. -/
class NumericCertificates : Prop where
  /-- `Φ(1) = ∫_1^∞ log ζ(x) dx < 1.7975699586287395`.  Certified by arb quadrature in
  `Code/verify_Phi_one_bound.sage` (pole and tail handled by hand); margin `9.2×10^{-17}`.
  See `RectangularBounds.integral_log_zeta_Ioi_one_lt`. -/
  integral_log_zeta_Ioi_one_lt :
    (∫ x in Set.Ioi (1 : ℝ), Real.log ‖riemannZeta (x : ℂ)‖) < 1.7975699586287395
  /-- `3e·E_{1/2}/(2π) < 1.1343755`, where `E_{1/2} = ∫_0^{π/2} (cos θ)^{3/2} dθ = ½B(5/4,1/2)`.
  Certified by arb from the closed form `Γ(1/4)²/(6√(2π))`
  (`Code/indep_mpmath_constants.py`); margin `1.1×10^{-8}`, and it needs nine digits of
  `Γ(1/4)`, which Mathlib cannot enclose.  See `JensenBounds.Ehalf_bound`. -/
  ehalf_bound :
    3 * Real.exp 1 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ (3 / 2 : ℝ)) / (2 * Real.pi)
      < 1.1343755
