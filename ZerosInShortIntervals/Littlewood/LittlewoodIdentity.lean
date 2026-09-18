/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Littlewood.LittlewoodMethod
import ZerosInShortIntervals.Common.RectangleResidue

/-! # Littlewood's zero-counting identity, Equation `\ref{eq:zerodensityintegral}` (Equation 13)

This file **proves** Littlewood's identity for `ζ`,

  `∫_{σ0}^{σ1} N(σ,T1,T2) dσ = (1/2π)(∫_{T1}^{T2} log|ζ(σ0+it)| dt − ∫_{T1}^{T2} log|ζ(σ1+it)| dt
      + ∫_{σ0}^{σ1} arg ζ(u+iT2) du − ∫_{σ0}^{σ1} arg ζ(u+iT1) du)`,

as the theorem `littlewood_zero_density_integral` at the end of this file. Equation
`\ref{eq:simplelittlewoodzerodensity}` (Equation 14, `simplelittlewoodzerodensity`), the
specialization used downstream, follows it.

**Sources.** The proof follows Farzanfard's MSc thesis
(https://hdl.handle.net/10133/7053, Lemma 2.2, equations
(2.5)–(2.8)), which is itself "based on [Titchmarsh, page 221, (9.9)]", i.e.
`\cite[§9.9]{Titchmarsh1986}`, Theorem 9.9.1 and the residue computation (9.9.2). Both are
cited in the docstring of `littlewood_zero_density_integral`. The route is theirs: write the
horizontal edges as `Φ(σ1+it) − Φ(σ+it) = ∫_σ^{σ1} (ζ'/ζ)(u+it) du`, interchange the order of the
two integrations, apply the residue theorem to `ζ'/ζ` on the rectangle `[σ, σ1] × [T1, T2]` for
(almost) every `σ`, and collect the edges. Concretely:

* `Common.RectangleResidue.rectInt_eq_two_pi_I_mul_sum` is the residue theorem on a rectangle;
* `zeta_logDeriv_sub_bounded` gives the residue `m_ρ = zetaMult ρ` of `ζ'/ζ` at each zero;
* `Nsigma_eq_sum` identifies `N(σ,T1,T2)` with `Σ m_ρ` over the zeros of the open rectangle;
* `left_edge_identity` is the residue theorem applied and its three "good" edges evaluated by the
  fundamental theorem of calculus (`integral_logDerivZetaLine_eq_logZetaLine` horizontally, with
  the constructed logarithm `LittlewoodMethod.logZetaLine`;
  `integral_I_mul_logDerivZetaLine_vertical` on the right edge, where `logZetaLine = G`);
* `integrable_logDeriv_zeta_rect` is the two-dimensional integrability of `ζ'/ζ` on the rectangle
  (the `1/|s-ρ|` singularities are dominated, via `|s-ρ|² ≥ 2|x-β||y-γ|`, by products of
  `|x-β|^{-1/2}|y-γ|^{-1/2}`), which licenses Fubini in `littlewood_identity_argZetaDef`;
* `littlewood_zero_density_integral` restates the identity for `argZeta`, which *is* `argZetaDef`
  (`LittlewoodMethod.argZeta`), so the restatement is definitional.

**Which `arg` the two horizontal integrals need.** In the
source's proof the two horizontal integrals `∫ Φ(σ+iT1) dσ`, `∫ Φ(σ+iT2) dσ` are restrictions of
*one* function `Φ = log φ`: a single analytic branch on the right edge `Re s = σ1` (for `ζ` and
`σ1 > 1`, the Dirichlet series `G`), continued horizontally to the left along each edge. They are
**not** independent branches: adding `2πk` to the top edge only would change the right-hand side by
`k(σ1 − σ0)`. What the proof actually uses is (i) on each horizontal edge, `Φ(σ1+iT_j) − Φ(σ+iT_j) =
∫_σ^{σ1} ζ'/ζ`, i.e. `arg` is the continuous argument along the edge (any two such differ by a
constant `2πk_j`), and (ii) the two constants agree, because on the right edge
`Φ(σ1+iT2) − Φ(σ1+iT1) = ∫_{T1}^{T2} i ζ'/ζ (σ1+it) dt` is the *same* analytic function evaluated at
both heights — this is where the two edges are tied together. So: two parts of the same analytic
function on the rectangle cut along horizontal slits from each zero to the left edge; equivalently,
the branch on each edge is pinned by the common branch on the zero-free right edge. The
constructed `argZetaDef` (vertical leg `G`, then horizontal continuation) is exactly this function,
which is why `littlewood_identity_argZetaDef` needs no argument hypotheses at all. Since
`argZeta` is *defined* as `argZetaDef` (`LittlewoodMethod.argZeta`),
`littlewood_zero_density_integral` is the same statement, again with no hypothesis pinning the
branch.

**Hypotheses, versus the tex.** `σ0 < σ1`, `1 < σ1` (right edge zero-free, `Φ` analytic there),
`0 < T1 < T2` (the pole `s = 1` is outside the rectangle; `T1 < T2` for the tex's `T1 < T2`).
Zero-free horizontal edges `hz1`/`hz2` — the tex's first case; its second case (a zero on the
edge) is handled in the tex by the halving convention and is not formalized (there `Nsigma`, which
counts `T1 < Im ρ ≤ T2`, and the tex's half-counting differ). **No hypothesis on the left edge
`Re s = σ0`**: the tex reads `∫ log|ζ(σ0+it)| dt` as an improper integral when a zero sits on
`Re s = σ0`; Lean's `intervalIntegral` is the Lebesgue integral, which agrees with the improper
one as soon as the integrand is integrable, and `log‖ζ(σ0+it)‖` *is* integrable across an
isolated zero (`ζ(s) = (s-ρ)^m g(s)` locally, `log|t-γ|` integrable) — this is
`intervalIntegrable_log_norm_zeta_vertical`. -/

open Complex MeasureTheory intervalIntegral Set Filter

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates]

/-- **A null set is almost surely avoided.** `μ S = 0 → ∀ᵐ x ∂μ, x ∉ S` (`MeasureTheory.ae_iff`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_inv_norm_sub_prod`, `integrable_logDeriv_zeta_rect`,
`littlewood_identity_argZetaDef`, `log_norm_zeta_vertical_integrableAt`. -/
theorem ae_notMem_of_measure_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (h : μ S = 0) : ∀ᵐ x ∂μ, x ∉ S := by
  rw [ae_iff]; simpa using h

/-! ### `ζ` vanishes on no open set; the multiplicity of a zero -/

/-- **`ζ` is not identically zero near any point `p ≠ 1`.**

### Summary of Proof
`ζ` is analytic on the connected set `{1}ᶜ` (`analyticOn_riemannZeta`,
`isConnected_compl_singleton_of_one_lt_rank`), so by the identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) vanishing near `p` would force
`ζ(2) = 0`, contradicting `riemannZeta_ne_zero_of_one_le_re`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_norm_zeta_vertical_integrableAt`, `zeta_analyticOrderAt_eq`,
`zeta_logDeriv_sub_bounded`. -/
theorem riemannZeta_not_eventually_zero {p : ℂ} (hp : p ≠ 1) :
    ¬ ∀ᶠ z in nhds p, riemannZeta z = 0 := by
  intro h
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h0 : riemannZeta =ᶠ[nhds p] (0 : ℂ → ℂ) := h.mono (fun z hz => by simpa using hz)
  have hE := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hp h0
  have h2 : riemannZeta 2 = 0 := by
    have := hE (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    simpa using this
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2

/-- **The multiplicity `m_p` of `p` as a zero of `ζ`** (`0` if `ζ p ≠ 0`): the natural number
`(analyticOrderAt riemannZeta p).toNat`.

### References
tex: the multiplicity implicit in "counting zeros with multiplicity" throughout.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_analyticOrderAt_eq`, `zeta_logDeriv_sub_bounded`, `Nsigma_eq_sum`,
`left_edge_identity`, `zeta_logDeriv_bound_on_rect`, `integrable_logDeriv_zeta_rect`. -/
noncomputable def zetaMult (p : ℂ) : ℕ := (analyticOrderAt riemannZeta p).toNat

/-- **The analytic order of `ζ` at `p ≠ 1` is finite and equals `zetaMult p`.** Finite by
`riemannZeta_not_eventually_zero` and `analyticOrderAt_eq_top`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaMult`, `riemannZeta_not_eventually_zero`.
**Used by:** `Nsigma_eq_sum`. -/
theorem zeta_analyticOrderAt_eq {p : ℂ} (hp1 : p ≠ 1) :
    analyticOrderAt riemannZeta p = (zetaMult p : ℕ∞) := by
  have hne : analyticOrderAt riemannZeta p ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact riemannZeta_not_eventually_zero hp1 h
  exact (ENat.natCast_toNat hne).symm

/-- **The residue of `ζ'/ζ` at a zero: `ζ'/ζ − m_p/(s−p)` is bounded near `p`.**

### Summary of Proof
Near `p ≠ 1`, `ζ(s) = (s−p)^n g(s)` with `g` analytic and `g(p) ≠ 0`
(`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, since `ζ` is not locally zero), and `n` is
the analytic order, i.e. `zetaMult p` (`AnalyticAt.analyticOrderAt_eq_natCast`). Then
`logDeriv ζ = n/(s−p) + logDeriv g` off `p` (`logDeriv_congr_nhds`, `logDeriv_mul`,
`logDeriv_fun_pow`), and `logDeriv g = g'/g` is continuous at `p`, hence bounded on a small ball.

### Lean Notes
This is the `hres` hypothesis of `Common.RectangleResidue.rectInt_eq_two_pi_I_mul_sum` for
`f = ζ'/ζ`, `res p = zetaMult p`. Stated for every `p ≠ 1` (with `zetaMult p = 0` when `ζ p ≠ 0`).

### References
`\cite[§9.9]{Titchmarsh1986}` (9.9.2): the residue of `φ'/φ` at a zero of order `m` is `m`.

### Dependencies
**Depends on:** `zetaMult`, `riemannZeta_not_eventually_zero`.
**Used by:** `left_edge_identity`, `zeta_logDeriv_bound_on_rect`. -/
theorem zeta_logDeriv_sub_bounded {p : ℂ} (hp1 : p ≠ 1) :
    ∃ r > 0, ∃ M : ℝ, ∀ z ∈ Metric.ball p r \ {p},
      ‖logDeriv riemannZeta z - (zetaMult p : ℂ) / (z - p)‖ ≤ M := by
  have han : AnalyticAt ℂ riemannZeta p := analyticOn_riemannZeta p hp1
  have hne := riemannZeta_not_eventually_zero hp1
  obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hord : analyticOrderAt riemannZeta p = n :=
    han.analyticOrderAt_eq_natCast.mpr ⟨g, hg, hg0, hev⟩
  have hmult : (zetaMult p : ℂ) = (n : ℂ) := by
    simp [zetaMult, hord]
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hev
  have hgne : ∀ᶠ z in nhds p, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hgan : ∀ᶠ z in nhds p, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hLD : ContinuousAt (logDeriv g) p := by
    have : ContinuousAt (fun z => deriv g z / g z) p :=
      hg.deriv.continuousAt.div hg.continuousAt hg0
    exact this
  have hbdd : ∀ᶠ z in nhds p, ‖logDeriv g z‖ ≤ ‖logDeriv g p‖ + 1 := by
    have h2 : ∀ᶠ z in nhds p, dist (logDeriv g z) (logDeriv g p) < 1 :=
      hLD.tendsto (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h2] with z hz
    rw [dist_eq_norm] at hz
    linarith [norm_sub_norm_le (logDeriv g z) (logDeriv g p)]
  have hUn : ∀ᶠ z in nhds p, z ∈ U := hUo.mem_nhds hpU
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hUn.and (hgne.and (hgan.and hbdd)))
  refine ⟨r, hr, ‖logDeriv g p‖ + 1, ?_⟩
  intro z hz
  obtain ⟨hzU, hgz, hgaz, hbz⟩ := hball (Metric.mem_ball.mp hz.1)
  have hzp : z ≠ p := hz.2
  have hfun : (fun w : ℂ => (w - p) ^ n • g w) = fun w => (w - p) ^ n * g w := by
    funext w; simp [smul_eq_mul]
  have hev' : riemannZeta =ᶠ[nhds z] (fun w => (w - p) ^ n * g w) := by
    rw [← hfun]
    exact eventually_of_mem (hUo.mem_nhds hzU) (fun w hw => hU w hw)
  rw [(logDeriv_congr_nhds hev').eq_of_nhds, hmult]
  have hpow : (z - p) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzp)
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - p) ^ n) z := by fun_prop
  have hd2 : DifferentiableAt ℂ g z := hgaz.differentiableAt
  rw [logDeriv_mul z hpow hgz hd1 hd2]
  have hd0 : DifferentiableAt ℂ (fun w : ℂ => w - p) z := by fun_prop
  have hpowLD : logDeriv (fun w : ℂ => (w - p) ^ n) z = n * logDeriv (fun w : ℂ => w - p) z :=
    logDeriv_fun_pow hd0 n
  have hlin : logDeriv (fun w : ℂ => w - p) z = 1 / (z - p) := by
    rw [logDeriv_apply]
    simp
  rw [hpowLD, hlin]
  have e : (n : ℂ) * (1 / (z - p)) + logDeriv g z - (n : ℂ) / (z - p) = logDeriv g z := by ring
  rw [e]
  exact hbz

/-! ### The finitely many zeros in a closed rectangle -/

/-- **A closed rectangle is compact.** Closed (`IsClosed.reProdIm`) and bounded
(`Bornology.IsBounded.reProdIm`) in `ℂ`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectC`.
**Used by:** `zetaZeros_rectC_finite`, `zeta_logDeriv_bound_on_rect`. -/
theorem isCompact_rectC (a b c d : ℝ) : IsCompact (rectC a b c d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

/-- **A closed rectangle contains finitely many zeros of `ζ`**
(Mathlib's `IsCompact.inter_riemannZetaZeros_finite`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `isCompact_rectC`.
**Used by:** `mem_zetaZerosIn`, `zetaZerosIn`. -/
theorem zetaZeros_rectC_finite (a b c d : ℝ) : (rectC a b c d ∩ riemannZetaZeros).Finite :=
  (isCompact_rectC a b c d).inter_riemannZetaZeros_finite

/-- **The zeros of `ζ` in the closed rectangle `[a,b] × [c,d]`, as a `Finset`.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaZeros_rectC_finite`.
**Used by:** `Nsigma_eq_sum`, `congr_simp`, `integrable_logDeriv_zeta_rect`, `left_edge_identity`,
`littlewood_identity_argZetaDef`, `mem_zetaZerosIn`, `zetaZerosIn_inRectO`,
`zeta_logDeriv_bound_on_rect`. -/
noncomputable def zetaZerosIn (a b c d : ℝ) : Finset ℂ :=
  (zetaZeros_rectC_finite a b c d).toFinset

/-- **Membership in `zetaZerosIn`:** `p ∈ zetaZerosIn a b c d ↔ p ∈ rectC a b c d ∧ ζ p = 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaZerosIn`.
**Used by:** everything below that handles the zeros of a rectangle. -/
theorem mem_zetaZerosIn {a b c d : ℝ} {p : ℂ} :
    p ∈ zetaZerosIn a b c d ↔ p ∈ rectC a b c d ∧ riemannZeta p = 0 := by
  simp [zetaZerosIn, mem_riemannZetaZeros]

/-- **Membership in the closed rectangle, in coordinates.**

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectC`.
**Used by:** everything below that handles the zeros of a rectangle. -/
theorem mem_rectC_iff {a b c d : ℝ} {s : ℂ} :
    s ∈ rectC a b c d ↔ (a ≤ s.re ∧ s.re ≤ b) ∧ (c ≤ s.im ∧ s.im ≤ d) := by
  unfold rectC; rw [mem_reProdIm]; simp [mem_Icc]

/-- **A zero of `ζ` has real part `< 1`** (`riemannZeta_ne_zero_of_one_le_re`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zetaZerosIn_inRectO`, `Nsigma_eq_sum`, `littlewood_identity_argZetaDef`. -/
theorem zeta_zero_re_lt_one' {p : ℂ} (hp : riemannZeta p = 0) : p.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hp

/-- **A rectangle with `0 < c` misses the pole `s = 1`** (whose imaginary part is `0`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `rectC`.
**Used by:** `Nsigma_eq_sum`, `left_edge_identity`, `zeta_logDeriv_bound_on_rect`. -/
theorem rectC_ne_one {a b c d : ℝ} (hc : 0 < c) {s : ℂ} (hs : s ∈ rectC a b c d) : s ≠ 1 := by
  intro h
  have := (mem_rectC_iff.mp hs).2.1
  rw [h] at this
  simp at this
  linarith

/-! ### `N(σ,T1,T2)` as a finite sum over the zeros of the open rectangle -/

section Identity

variable {σ0 σ1 T1 T2 : ℝ}

/-- **For a good abscissa `σ`, every zero of `ζ` in the closed rectangle `[σ,σ1] × [T1,T2]` is
interior.** Good means: no zero of the big rectangle `[σ0,σ1] × [T1,T2]` has real part `σ`
(`hσB`); the horizontal edges are zero-free by `hz1`/`hz2`, and `Re ρ < 1 < σ1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaZerosIn`, `zeta_zero_re_lt_one'`.
**Used by:** `left_edge_identity`. -/
theorem zetaZerosIn_inRectO (hσ1 : 1 < σ1)
    (hz1 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T1 * I) ≠ 0)
    (hz2 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T2 * I) ≠ 0)
    {σ : ℝ} (hσ0 : σ0 ≤ σ)
    (hσB : ∀ p ∈ zetaZerosIn σ0 σ1 T1 T2, p.re ≠ σ) :
    ∀ p ∈ zetaZerosIn σ σ1 T1 T2, InRectO σ σ1 T1 T2 p := by
  intro p hp
  obtain ⟨hpR, hp0⟩ := mem_zetaZerosIn.mp hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := mem_rectC_iff.mp hpR
  have hpR0 : p ∈ zetaZerosIn σ0 σ1 T1 T2 :=
    mem_zetaZerosIn.mpr ⟨mem_rectC_iff.mpr ⟨⟨le_trans hσ0 h1, h2⟩, ⟨h3, h4⟩⟩, hp0⟩
  have hre : p.re ≠ σ := hσB p hpR0
  have hpeq : p = (p.re : ℂ) + p.im * I := (re_add_im p).symm
  refine ⟨lt_of_le_of_ne h1 (Ne.symm hre), lt_of_lt_of_le (zeta_zero_re_lt_one' hp0) hσ1.le, ?_, ?_⟩
  · refine lt_of_le_of_ne h3 ?_
    intro hT
    apply hz1 p.re ⟨le_trans hσ0 h1, h2⟩
    rw [hT, ← hpeq]; exact hp0
  · refine lt_of_le_of_ne h4 ?_
    intro hT
    apply hz2 p.re ⟨le_trans hσ0 h1, h2⟩
    rw [← hT, ← hpeq]; exact hp0

/-- **`N(σ,T1,T2) = Σ_ρ m_ρ` over the zeros `ρ` of the rectangle `[σ,σ1] × [T1,T2]`**, for a good
abscissa `σ` (no zero with `Re ρ = σ`) and a zero-free bottom edge.

### Summary of Proof
`Nsigma σ T1 T2 = Nrect T1 T2 (1−σ)` is the `finsum` of the divisor of `ζ` on the half-strip
`{T1 < Im ≤ T2, σ < Re}`. Its support consists of zeros, which have `Re < 1 < σ1`, so it lies in
`zetaZerosIn σ σ1 T1 T2` (`finsum_eq_sum_of_support_subset`); conversely every such zero is in the
half-strip (`Re ρ > σ` by `hσB`, `Im ρ > T1` by `hz1`), where the divisor is
`(analyticOrderAt ζ ρ).map ↑).untop₀ = m_ρ` (`AnalyticOnNhd.divisor_apply`,
`zeta_analyticOrderAt_eq`).

### References
tex: the definition of `N(σ,T1,T2)` in the introduction, and Farzanfard's Definition 2.1.

### Dependencies
**Depends on:** `Nsigma`, `Nrect`, `analyticOnNhd_riemannZeta_rect`, `zetaZerosIn`, `zetaMult`,
`zeta_analyticOrderAt_eq`, `zeta_zero_re_lt_one'`, `rectC_ne_one`.
**Used by:** `left_edge_identity`. -/
theorem Nsigma_eq_sum (hσ1 : 1 < σ1) (hT1 : 0 < T1)
    (hz1 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T1 * I) ≠ 0)
    {σ : ℝ} (hσ0 : σ0 ≤ σ)
    (hσB : ∀ p ∈ zetaZerosIn σ0 σ1 T1 T2, p.re ≠ σ) :
    ((Nsigma σ T1 T2 : ℤ) : ℂ) = ∑ p ∈ zetaZerosIn σ σ1 T1 T2, (zetaMult p : ℂ) := by
  unfold Nsigma Nrect
  have hset : {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ 1 - (1 - σ) < s.re}
      = {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ σ < s.re} := by
    ext s; simp
  rw [hset]
  set S := {s : ℂ | T1 < s.im ∧ s.im ≤ T2 ∧ σ < s.re} with hS
  have hanalytic : AnalyticOnNhd ℂ riemannZeta S := analyticOnNhd_riemannZeta_rect hT1
  have hsupp : Function.support (fun u => MeromorphicOn.divisor riemannZeta S u)
      ⊆ ↑(zetaZerosIn σ σ1 T1 T2) := by
    intro u hu
    rw [Function.mem_support] at hu
    have huS : u ∈ S := (MeromorphicOn.divisor riemannZeta S).supportWithinDomain hu
    have hzero : riemannZeta u = 0 := by
      by_contra hne
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic huS,
        (hanalytic u huS).analyticOrderAt_eq_zero.mpr hne] at hu
      simp at hu
    have hre1 : u.re < 1 := zeta_zero_re_lt_one' hzero
    obtain ⟨hu1, hu2, hu3⟩ := huS
    exact Finset.mem_coe.mpr (mem_zetaZerosIn.mpr
      ⟨mem_rectC_iff.mpr ⟨⟨hu3.le, by linarith⟩, ⟨hu1.le, hu2⟩⟩, hzero⟩)
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpR, hp0⟩ := mem_zetaZerosIn.mp hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := mem_rectC_iff.mp hpR
  have hpR0 : p ∈ zetaZerosIn σ0 σ1 T1 T2 :=
    mem_zetaZerosIn.mpr ⟨mem_rectC_iff.mpr ⟨⟨le_trans hσ0 h1, h2⟩, ⟨h3, h4⟩⟩, hp0⟩
  have hre : p.re ≠ σ := hσB p hpR0
  have hpeq : p = (p.re : ℂ) + p.im * I := (re_add_im p).symm
  have hIm : T1 < p.im := by
    refine lt_of_le_of_ne h3 ?_
    intro hT
    apply hz1 p.re ⟨le_trans hσ0 h1, h2⟩
    rw [hT, ← hpeq]; exact hp0
  have hpS : p ∈ S := ⟨hIm, h4, lt_of_le_of_ne h1 (Ne.symm hre)⟩
  have hp1 : p ≠ 1 := rectC_ne_one hT1 hpR
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hpS, zeta_analyticOrderAt_eq hp1]
  simp

/-! ### Horizontal lines that are zero-free from an abscissa `a` onwards

The line lemmas of `LittlewoodMethod` (`hasDerivAt_logZetaLine_line`, `exp_logZetaLine_line`, …)
assume `ζ ≠ 0` on `[a, 2] + iT`. Here we need the same with `ζ ≠ 0` on `[a, ∞) + iT` and the
conclusion at every `σ ≥ a` (also `σ > 2`); for `x ≥ 1` the hypothesis is automatic
(`riemannZeta_ne_zero_of_one_le_re`), so the two formulations are interchangeable in practice. -/

/-- **On the segment `uIcc σ 2` at height `T`, `ζ ≠ 0`**, given `ζ ≠ 0` on `[a,∞) + iT` and
`a ≤ σ`: points below `a` are then `≥ 2`, where `ζ ≠ 0` anyway.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `hasDerivAt_logZetaLine_line'`, `exp_logZetaLine_line'`. -/
theorem zeta_ne_zero_uIcc_two {T a : ℝ}
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) {σ : ℝ} (hσ : a ≤ σ)
    {x : ℝ} (hx : x ∈ uIcc σ 2) : riemannZeta ((x : ℂ) + T * I) ≠ 0 := by
  by_cases hax : a ≤ x
  · exact hzf x hax
  · push Not at hax
    have hx2 : 2 ≤ x := by
      rcases le_total σ 2 with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1]
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- **`LittlewoodMethod.hasDerivAt_logZetaLine_line` for lines zero-free on `[a,∞) + iT`**, at
every `σ ≥ a`. Same proof (`intervalIntegral.integral_hasDerivAt_left`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `logZetaLine_line_eq`, `continuous_zeta_line`, `logDerivZetaLine_continuousAt`,
`line_ne_one`, `zeta_ne_zero_uIcc_two`.
**Used by:** `exp_logZetaLine_line'`, `integral_logDerivZetaLine_eq_logZetaLine`,
`argZetaDef_continuousOn_line'`, `logZetaLine_continuousOn_line'`. -/
theorem hasDerivAt_logZetaLine_line' {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) {σ : ℝ} (hσ : a ≤ σ) :
    HasDerivAt (fun y : ℝ => logZetaLine ((y : ℂ) + T * I)) (logDerivZetaLine T σ) σ := by
  rw [logZetaLine_line_eq]
  have hopen : IsOpen {x : ℝ | riemannZeta ((x : ℂ) + T * I) ≠ 0} :=
    isOpen_ne_fun (continuous_zeta_line hT) continuous_const
  have hmeas : StronglyMeasurableAtFilter (logDerivZetaLine T) (nhds σ) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter hopen
      (fun x hx => logDerivZetaLine_continuousAt (line_ne_one hT x) hx) σ (hzf σ hσ)
  have hint : IntervalIntegrable (logDerivZetaLine T) MeasureTheory.volume σ 2 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (logDerivZetaLine_continuousAt (line_ne_one hT x)
      (zeta_ne_zero_uIcc_two hzf hσ hx)).continuousWithinAt
  have hcont : ContinuousAt (logDerivZetaLine T) σ :=
    logDerivZetaLine_continuousAt (line_ne_one hT σ) (hzf σ hσ)
  have h := (hasDerivAt_const σ (LSeries GTerm (2 + T * I))).sub
    (intervalIntegral.integral_hasDerivAt_left hint hmeas hcont)
  refine h.congr_deriv ?_
  ring

/-- **`LittlewoodMethod.exp_logZetaLine_line` for lines zero-free on `[a,∞) + iT`**:
`exp (logZetaLine (σ+iT)) = ζ(σ+iT)` for every `σ ≥ a`. Same proof (`ζ·exp(−L)` has zero
derivative and equals `1` at `Re = 2`).

### References
tex: the definition of `arg f` by continuous variation along a horizontal line.

### Dependencies
**Depends on:** `hasDerivAt_logZetaLine_line'`, `hasDerivAt_zeta_line`, `line_ne_one`,
`zeta_ne_zero_uIcc_two`, `logZetaLine`, `GTerm_LSeries_exp_eq_riemannZeta`.
**Used by:** `re_logZetaLine_line'`, `zeta_eq_norm_mul_exp_argZetaDef'`. -/
theorem exp_logZetaLine_line' {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) {σ : ℝ} (hσ : a ≤ σ) :
    Complex.exp (logZetaLine ((σ : ℂ) + T * I)) = riemannZeta ((σ : ℂ) + T * I) := by
  set L : ℝ → ℂ := fun y => logZetaLine ((y : ℂ) + T * I) with hL
  set φ : ℝ → ℂ := fun y => riemannZeta ((y : ℂ) + T * I) * Complex.exp (-(L y)) with hφ
  have hφderiv : ∀ y ∈ uIcc σ 2, HasDerivAt φ 0 y := by
    intro y hy
    have hz := zeta_ne_zero_uIcc_two hzf hσ hy
    have hy' : a ≤ y ∨ 2 ≤ y := by
      by_cases hay : a ≤ y
      · exact Or.inl hay
      · right
        push Not at hay
        rcases le_total σ 2 with h | h
        · rw [uIcc_of_le h] at hy; linarith [hy.1]
        · rw [uIcc_of_ge h] at hy; linarith [hy.1]
    have h2 : HasDerivAt L (logDerivZetaLine T y) y := by
      rcases hy' with hay | h2y
      · exact hasDerivAt_logZetaLine_line' hT hzf hay
      · exact hasDerivAt_logZetaLine_line' hT
          (fun x hx => riemannZeta_ne_zero_of_one_le_re (by simp; linarith)) h2y
    have h1 := hasDerivAt_zeta_line (T := T) (x := y) (line_ne_one hT y)
    have h3 := (h2.neg).cexp
    have h4 := h1.mul h3
    refine h4.congr_deriv ?_
    unfold logDerivZetaLine
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hφderiv
    (intervalIntegrable_const (c := (0 : ℂ)))
  simp only [intervalIntegral.integral_zero] at hFTC
  have hφσ : φ σ = φ 2 := by linear_combination hFTC
  have hL2 : L 2 = LSeries GTerm (2 + T * I) := by
    simp only [hL, logZetaLine]
    simp
  have h2re : (1 : ℝ) < ((2 : ℂ) + T * I).re := by simp
  have hζ2 : riemannZeta ((2 : ℂ) + T * I) = Complex.exp (LSeries GTerm (2 + T * I)) :=
    (GTerm_LSeries_exp_eq_riemannZeta h2re).symm
  have hφ2 : φ 2 = 1 := by
    simp only [hφ, hL2]
    push_cast
    rw [hζ2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [hφ2] at hφσ
  have hφσ' : riemannZeta ((σ : ℂ) + T * I) * (Complex.exp (L σ))⁻¹ = 1 := by
    rw [← Complex.exp_neg]; exact hφσ
  exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hφσ').symm

/-- **On a zero-free line, `Re (logZetaLine (σ+iT)) = log‖ζ(σ+iT)‖`** (from
`exp_logZetaLine_line'`, `Complex.norm_exp`, `Real.log_exp`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `exp_logZetaLine_line'`.
**Used by:** `littlewood_identity_argZetaDef`. -/
theorem re_logZetaLine_line' {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) {σ : ℝ} (hσ : a ≤ σ) :
    (logZetaLine ((σ : ℂ) + T * I)).re = Real.log ‖riemannZeta ((σ : ℂ) + T * I)‖ := by
  rw [← exp_logZetaLine_line' hT hzf hσ, Complex.norm_exp, Real.log_exp]

/-- **The horizontal fundamental theorem of calculus:**
`∫_a^b (ζ'/ζ)(x+iT) dx = logZetaLine (b+iT) − logZetaLine (a+iT)` on a line zero-free from `a`.
This is the thesis's `Φ(σ2+it) − Φ(σ+it) = ∫_σ^{σ2} φ'/φ` (its (2.6)).

### References
Farzanfard, Lemma 2.2, equation (2.6); `\cite[§9.9]{Titchmarsh1986}`.

### Dependencies
**Depends on:** `hasDerivAt_logZetaLine_line'`, `logDerivZetaLine_continuousAt`, `line_ne_one`.
**Used by:** `left_edge_identity`, `littlewood_identity_argZetaDef`. -/
theorem integral_logDerivZetaLine_eq_logZetaLine {T a b : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) (hab : a ≤ b) :
    ∫ x in a..b, logDerivZetaLine T x
      = logZetaLine ((b : ℂ) + T * I) - logZetaLine ((a : ℂ) + T * I) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_logZetaLine_line' hT hzf hx.1
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (logDerivZetaLine_continuousAt (line_ne_one hT x) (hzf x hx.1)).continuousWithinAt

/-- **`argZetaDef` is continuous along a line zero-free from `a`**, on any `Icc a b`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_logZetaLine_line'`, `argZetaDef`.
**Used by:** `littlewood_identity_argZetaDef`, and, in `LittlewoodShort`, `littlewoodshort` and
`littlewoodshort_tight` (as the `hargf_cont` input of `ArgIntegrals.arg_integrals`). -/
theorem argZetaDef_continuousOn_line' {T a b : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => argZetaDef ((x : ℂ) + T * I)) (Icc a b) := by
  intro x hx
  exact (Complex.continuous_im.continuousAt.comp
    (hasDerivAt_logZetaLine_line' hT hzf hx.1).continuousAt).continuousWithinAt

/-- **`logZetaLine` is continuous along a line zero-free from `a`**, on any `Icc a b`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_logZetaLine_line'`.
**Used by:** none yet. -/
theorem logZetaLine_continuousOn_line' {T a b : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => logZetaLine ((x : ℂ) + T * I)) (Icc a b) := by
  intro x hx
  exact (hasDerivAt_logZetaLine_line' hT hzf hx.1).continuousAt.continuousWithinAt

/-! ### The right edge `Re s = σ1 > 1`, where the logarithm is `G` -/

/-- **`t ↦ G(σ+it)` has derivative `i·(ζ'/ζ)(σ+it)` for `σ > 1`** (`Definitions.G_hasDerivAt`
along the vertical line, `HasDerivAt.comp_ofReal`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `G_hasDerivAt`, `logDerivZetaLine`.
**Used by:** `integral_I_mul_logDerivZetaLine_vertical`. -/
theorem hasDerivAt_G_vertical {σ y : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fun t : ℝ => LSeries GTerm ((σ : ℂ) + t * I)) (I * logDerivZetaLine y σ) y := by
  have hre : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have hd := G_hasDerivAt hre
  have h1 : HasDerivAt (fun w : ℂ => (σ : ℂ) + w * I) I (y : ℂ) := by
    have := ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (σ : ℂ)
    simpa using this
  have h2 := hd.comp (y : ℂ) h1
  refine h2.comp_ofReal.congr_deriv ?_
  unfold logDerivZetaLine
  ring

/-- **`y ↦ (ζ'/ζ)(σ+iy)` is continuous for `σ > 1`** (`ζ` analytic and nonvanishing there).

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaLine`.
**Used by:** `integral_I_mul_logDerivZetaLine_vertical`. -/
theorem continuous_logDerivZetaLine_vertical {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun y : ℝ => logDerivZetaLine y σ) := by
  have hmap : Continuous (fun y : ℝ => (σ : ℂ) + y * I) := by fun_prop
  have hne : ∀ y : ℝ, (σ : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1 : Continuous (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + y * I)) := by
    rw [continuous_iff_continuousAt]; intro y
    exact ((analyticOn_riemannZeta _ (hne y)).deriv.continuousAt).comp_of_eq
      hmap.continuousAt rfl
  have h2 : Continuous (fun y : ℝ => riemannZeta ((σ : ℂ) + y * I)) := by
    rw [continuous_iff_continuousAt]; intro y
    exact ((analyticOn_riemannZeta _ (hne y)).continuousAt).comp_of_eq hmap.continuousAt rfl
  exact h1.div h2 (fun y => riemannZeta_ne_zero_of_one_lt_re (by simp [hσ]))

/-- **The vertical fundamental theorem of calculus on the right edge:**
`∫_c^d i·(ζ'/ζ)(σ+iy) dy = G(σ+id) − G(σ+ic)` for `σ > 1`. This is the one place where the two
horizontal edges are tied to a *common* branch — see the module docstring.

### References
Farzanfard, Lemma 2.2, equation (2.7), the `∫_{σ2+iT1}^{σ2+iT2}` term.

### Dependencies
**Depends on:** `hasDerivAt_G_vertical`, `continuous_logDerivZetaLine_vertical`.
**Used by:** `left_edge_identity`. -/
theorem integral_I_mul_logDerivZetaLine_vertical {σ : ℝ} (hσ : 1 < σ) (c d : ℝ) :
    ∫ y in c..d, I * logDerivZetaLine y σ
      = LSeries GTerm ((σ : ℂ) + d * I) - LSeries GTerm ((σ : ℂ) + c * I) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro y _; exact hasDerivAt_G_vertical hσ
  · exact (continuous_const.mul (continuous_logDerivZetaLine_vertical hσ)).intervalIntegrable _ _

/-! ### The residue identity on `[σ, σ1] × [T1, T2]` for a good `σ` -/

/-- **A horizontal edge zero-free on `[σ0, σ1]` is zero-free on `[σ, ∞)` for `σ ≥ σ0`**, since
`ζ ≠ 0` on `Re ≥ 1` and `σ1 > 1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `left_edge_identity`, `littlewood_identity_argZetaDef`,
`LittlewoodShort.littlewoodshort`, `LittlewoodShort.littlewoodshort_tight`. -/
theorem zeta_ne_zero_line_of_Icc (hσ1 : 1 < σ1) {T : ℝ}
    (hz : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T * I) ≠ 0) {σ : ℝ} (hσ0 : σ0 ≤ σ) :
    ∀ x, σ ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0 := by
  intro x hx
  by_cases hx1 : x ≤ σ1
  · exact hz x ⟨le_trans hσ0 hx, hx1⟩
  · push Not at hx1
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- **The residue identity, edges evaluated (Farzanfard's (2.7)):** for a good abscissa
`σ ∈ [σ0, σ1)`,
`i ∫_{T1}^{T2} (ζ'/ζ)(σ+iy) dy = logZetaLine (σ+iT2) − logZetaLine (σ+iT1) − 2πi N(σ,T1,T2)`.

### Summary of Proof
`Common.RectangleResidue.rectInt_eq_two_pi_I_mul_sum` for `ζ'/ζ` on `[σ,σ1] × [T1,T2]`, whose
poles are the zeros of the open rectangle (`zetaZerosIn_inRectO`) with residues `m_ρ`
(`zeta_logDeriv_sub_bounded`), summing to `N(σ,T1,T2)` (`Nsigma_eq_sum`). The bottom and top
edges are `logZetaLine (σ1+iT_j) − logZetaLine (σ+iT_j)`
(`integral_logDerivZetaLine_eq_logZetaLine`),
the right edge is `G(σ1+iT2) − G(σ1+iT1) = logZetaLine (σ1+iT2) − logZetaLine (σ1+iT1)`
(`integral_I_mul_logDerivZetaLine_vertical`, `logZetaLine_eq_G`); the four `logZetaLine (σ1+·)`
values cancel and the left edge remains.

### References
Farzanfard, Lemma 2.2, equations (2.7)–(2.8); `\cite[§9.9]{Titchmarsh1986}`.

### Dependencies
**Depends on:** `rectInt_eq_two_pi_I_mul_sum`, `zetaZerosIn_inRectO`, `zeta_logDeriv_sub_bounded`,
`Nsigma_eq_sum`, `integral_logDerivZetaLine_eq_logZetaLine`,
`integral_I_mul_logDerivZetaLine_vertical`, `logZetaLine_eq_G`, `zeta_ne_zero_line_of_Icc`,
`rectC_ne_one`.
**Used by:** `littlewood_identity_argZetaDef`. -/
theorem left_edge_identity (hσ1 : 1 < σ1) (hT : T1 < T2) (hT1 : 0 < T1)
    (hz1 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T1 * I) ≠ 0)
    (hz2 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T2 * I) ≠ 0)
    {σ : ℝ} (hσ0 : σ0 ≤ σ) (hσσ1 : σ < σ1)
    (hσB : ∀ p ∈ zetaZerosIn σ0 σ1 T1 T2, p.re ≠ σ) :
    I * ∫ y in T1..T2, logDerivZetaLine y σ
      = logZetaLine ((σ : ℂ) + T2 * I) - logZetaLine ((σ : ℂ) + T1 * I)
        - 2 * Real.pi * I * ((Nsigma σ T1 T2 : ℤ) : ℂ) := by
  have hT2 : 0 < T2 := lt_trans hT1 hT
  set Z := zetaZerosIn σ σ1 T1 T2 with hZ
  have hP : ∀ p ∈ Z, InRectO σ σ1 T1 T2 p := zetaZerosIn_inRectO hσ1 hz1 hz2 hσ0 hσB
  have hf : DifferentiableOn ℂ (logDeriv riemannZeta) (rectC σ σ1 T1 T2 \ ↑Z) := by
    intro s hs
    have hs1 : s ≠ 1 := rectC_ne_one hT1 hs.1
    have hsz : riemannZeta s ≠ 0 := fun h0 => hs.2 (mem_zetaZerosIn.mpr ⟨hs.1, h0⟩)
    have han := analyticOn_riemannZeta s hs1
    have : DifferentiableAt ℂ (fun w => deriv riemannZeta w / riemannZeta w) s :=
      han.deriv.differentiableAt.div han.differentiableAt hsz
    exact this.differentiableWithinAt
  have hres : ∀ p ∈ Z, ∃ r > 0, ∃ M : ℝ, ∀ z ∈ Metric.ball p r \ {p},
      ‖logDeriv riemannZeta z - (fun q => (zetaMult q : ℂ)) p / (z - p)‖ ≤ M :=
    fun p hp => zeta_logDeriv_sub_bounded (rectC_ne_one hT1 (mem_zetaZerosIn.mp hp).1)
  have hR := rectInt_eq_two_pi_I_mul_sum hσσ1 hT Z (fun q => (zetaMult q : ℂ)) hP _ hf hres
  rw [← Nsigma_eq_sum hσ1 hT1 hz1 hσ0 hσB] at hR
  unfold rectInt at hR
  have hbot : (∫ x in σ..σ1, logDeriv riemannZeta ((x : ℂ) + T1 * I))
      = logZetaLine ((σ1 : ℂ) + T1 * I) - logZetaLine ((σ : ℂ) + T1 * I) :=
    integral_logDerivZetaLine_eq_logZetaLine hT1.ne' (zeta_ne_zero_line_of_Icc hσ1 hz1 hσ0)
      hσσ1.le
  have htop : (∫ x in σ..σ1, logDeriv riemannZeta ((x : ℂ) + T2 * I))
      = logZetaLine ((σ1 : ℂ) + T2 * I) - logZetaLine ((σ : ℂ) + T2 * I) :=
    integral_logDerivZetaLine_eq_logZetaLine hT2.ne' (zeta_ne_zero_line_of_Icc hσ1 hz2 hσ0)
      hσσ1.le
  have hright : I * (∫ y in T1..T2, logDeriv riemannZeta ((σ1 : ℂ) + y * I))
      = logZetaLine ((σ1 : ℂ) + T2 * I) - logZetaLine ((σ1 : ℂ) + T1 * I) := by
    have h := integral_I_mul_logDerivZetaLine_vertical hσ1 T1 T2
    rw [intervalIntegral.integral_const_mul] at h
    have e1 : logZetaLine ((σ1 : ℂ) + T2 * I) = LSeries GTerm ((σ1 : ℂ) + T2 * I) :=
      logZetaLine_eq_G (by simp [hσ1])
    have e2 : logZetaLine ((σ1 : ℂ) + T1 * I) = LSeries GTerm ((σ1 : ℂ) + T1 * I) :=
      logZetaLine_eq_G (by simp [hσ1])
    rw [e1, e2]
    exact h
  have hleft : (∫ y in T1..T2, logDeriv riemannZeta ((σ : ℂ) + y * I))
      = ∫ y in T1..T2, logDerivZetaLine y σ := rfl
  rw [hbot, htop, hright, hleft] at hR
  linear_combination -hR

/-! ### Two-dimensional integrability of `ζ'/ζ` on the rectangle -/

/-- **A function continuous on a compact set minus finitely many points, and bounded near each of
them, is bounded.**

### Summary of Proof
Remove an open ball `B(p, r_p)` around each exceptional `p`; what is left is compact and the
function is bounded there (`IsCompact.exists_bound_of_continuousOn`); inside the punctured balls
the local bounds apply.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_logDeriv_bound_on_rect`. -/
theorem exists_bound_of_continuousOn_diff_finite {K : Set ℂ} (hK : IsCompact K) (P : Finset ℂ)
    {u : ℂ → ℂ} (hu : ContinuousOn u (K \ ↑P))
    (hP : ∀ p ∈ P, ∃ r > 0, ∃ M : ℝ, ∀ z ∈ Metric.ball p r \ {p}, ‖u z‖ ≤ M) :
    ∃ M : ℝ, ∀ z ∈ K \ ↑P, ‖u z‖ ≤ M := by
  choose! r hr M hM using hP
  set K' := K \ ⋃ p ∈ P, Metric.ball p (r p) with hK'
  have hK'c : IsCompact K' := hK.diff (isOpen_biUnion fun p _ => Metric.isOpen_ball)
  have hK'sub : K' ⊆ K \ ↑P := by
    intro z hz
    refine ⟨hz.1, fun hzP => hz.2 ?_⟩
    exact mem_biUnion (Finset.mem_coe.mp hzP) (Metric.mem_ball_self (hr z (Finset.mem_coe.mp hzP)))
  obtain ⟨C, hC⟩ := hK'c.exists_bound_of_continuousOn (hu.mono hK'sub)
  have hsum : 0 ≤ ∑ p ∈ P, |M p| := Finset.sum_nonneg (fun p _ => abs_nonneg (M p))
  refine ⟨|C| + ∑ p ∈ P, |M p|, ?_⟩
  intro z hz
  by_cases hzK' : z ∈ K'
  · have := hC z hzK'
    linarith [le_abs_self C]
  · have hzU : z ∈ ⋃ p ∈ P, Metric.ball p (r p) := by
      by_contra hcon
      exact hzK' ⟨hz.1, hcon⟩
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hzU
    have hzne : z ≠ p := fun h => hz.2 (by rw [h]; exact Finset.mem_coe.mpr hp)
    have h1 := hM p hp z ⟨hzp, hzne⟩
    have h2 : M p ≤ ∑ q ∈ P, |M q| :=
      le_trans (le_abs_self _) (Finset.single_le_sum (fun q _ => abs_nonneg (M q)) hp)
    linarith [abs_nonneg C]

/-- **`‖ζ'/ζ(s)‖ ≤ M + Σ_ρ m_ρ/‖s−ρ‖` on the rectangle minus its zeros.**

### Summary of Proof
`u := ζ'/ζ − Σ_ρ m_ρ/(s−ρ)` is continuous off the zeros and bounded near each zero `p` (by
`zeta_logDeriv_sub_bounded` for the `p`-term and `dist(p,q)/2` for the others), hence bounded on
the rectangle minus the zeros (`exists_bound_of_continuousOn_diff_finite`); add the sum back.

### References
No tex counterpart; the integrability of `ζ'/ζ` is left implicit in the sources' interchange of
the two integrals.

### Dependencies
**Depends on:** `zetaZerosIn`, `zetaMult`, `zeta_logDeriv_sub_bounded`,
`exists_bound_of_continuousOn_diff_finite`, `isCompact_rectC`, `rectC_ne_one`.
**Used by:** `integrable_logDeriv_zeta_rect`. -/
theorem zeta_logDeriv_bound_on_rect (hT1 : 0 < T1) :
    ∃ Mb : ℝ, ∀ s ∈ rectC σ0 σ1 T1 T2 \ ↑(zetaZerosIn σ0 σ1 T1 T2),
      ‖logDeriv riemannZeta s‖
        ≤ Mb + ∑ p ∈ zetaZerosIn σ0 σ1 T1 T2, (zetaMult p : ℝ) / ‖s - p‖ := by
  set Z := zetaZerosIn σ0 σ1 T1 T2 with hZ
  set u : ℂ → ℂ := fun s => logDeriv riemannZeta s - ∑ p ∈ Z, (zetaMult p : ℂ) / (s - p) with hu
  have hucont : ContinuousOn u (rectC σ0 σ1 T1 T2 \ ↑Z) := by
    intro s hs
    have hs1 : s ≠ 1 := rectC_ne_one hT1 hs.1
    have hsz : riemannZeta s ≠ 0 := fun h0 => hs.2 (mem_zetaZerosIn.mpr ⟨hs.1, h0⟩)
    have han := analyticOn_riemannZeta s hs1
    have h1 : ContinuousAt (fun w => deriv riemannZeta w / riemannZeta w) s :=
      han.deriv.continuousAt.div han.continuousAt hsz
    have h2 : ContinuousAt (fun w => ∑ p ∈ Z, (zetaMult p : ℂ) / (w - p)) s := by
      have hterm : ∀ p ∈ Z, ContinuousAt (fun w => (zetaMult p : ℂ) / (w - p)) s := by
        intro p hp
        have hsp : s - p ≠ 0 :=
          sub_ne_zero.mpr (fun h => hs.2 (by rw [h]; exact Finset.mem_coe.mpr hp))
        exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) hsp
      exact tendsto_finsetSum _ (fun p hp => (hterm p hp).tendsto)
    exact (h1.sub h2).continuousWithinAt
  have hures : ∀ p ∈ Z, ∃ r > 0, ∃ M : ℝ, ∀ z ∈ Metric.ball p r \ {p}, ‖u z‖ ≤ M := by
    intro p hp
    have hp1 : p ≠ 1 := rectC_ne_one hT1 (mem_zetaZerosIn.mp hp).1
    obtain ⟨r0, hr0, M0, hM0⟩ := zeta_logDeriv_sub_bounded hp1
    have hopen : IsOpen ((↑(Z.erase p) : Set ℂ)ᶜ) := (Finset.finite_toSet _).isClosed.isOpen_compl
    have hpmem : p ∈ (↑(Z.erase p) : Set ℂ)ᶜ := by simp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hpmem
    refine ⟨min r0 (ε / 2), lt_min hr0 (by linarith), M0 + ∑ q ∈ Z, (zetaMult q : ℝ) * (2 / ε), ?_⟩
    intro z hz
    have hz0 : z ∈ Metric.ball p r0 := Metric.ball_subset_ball (min_le_left _ _) hz.1
    have hzε : dist z p < ε / 2 := lt_of_lt_of_le (Metric.mem_ball.mp hz.1) (min_le_right _ _)
    have hsplit : u z = (logDeriv riemannZeta z - (zetaMult p : ℂ) / (z - p))
        - ∑ q ∈ Z.erase p, (zetaMult q : ℂ) / (z - q) := by
      simp only [hu]
      rw [← Finset.sum_erase_add _ _ hp]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add (hM0 z ⟨hz0, hz.2⟩) ?_)
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ q ∈ Z.erase p, ‖(zetaMult q : ℂ) / (z - q)‖ ≤ (zetaMult q : ℝ) * (2 / ε) := by
      intro q hq
      have hqp : q ∉ Metric.ball p ε := fun hmem => (hball hmem) (Finset.mem_coe.mpr hq)
      have hdq : ε ≤ dist q p := not_lt.mp (fun h => hqp (Metric.mem_ball.mpr h))
      have hzq : ε / 2 ≤ dist z q := by
        have := dist_triangle q z p
        rw [dist_comm q z] at this
        linarith
      have hzq0 : 0 < ‖z - q‖ := by rw [← dist_eq_norm]; linarith
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ hzq0, ← dist_eq_norm]
      have : (zetaMult q : ℝ) * (2 / ε) * (ε / 2) = zetaMult q := by field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) (zetaMult q), hzq]
    refine (Finset.sum_le_sum hterm).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p Z)
    intro q _ _
    positivity
  obtain ⟨Mb, hMb⟩ := exists_bound_of_continuousOn_diff_finite (isCompact_rectC σ0 σ1 T1 T2) Z
    hucont hures
  refine ⟨Mb, ?_⟩
  intro s hs
  have h1 := hMb s hs
  have h2 : logDeriv riemannZeta s = u s + ∑ p ∈ Z, (zetaMult p : ℂ) / (s - p) := by
    simp only [hu]; ring
  rw [h2]
  refine (norm_add_le _ _).trans (add_le_add h1 ?_)
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro p _
  rw [norm_div, Complex.norm_natCast]

/-- **`|x − β|^r` is integrable on bounded intervals for `r > −1`.** Split at `β` and use
`intervalIntegrable_rpow'` on each side (composed with `x ↦ x − β` resp. `x ↦ β − x`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_inv_norm_sub_prod`. -/
theorem integrableOn_abs_sub_rpow_Ioc (β a b : ℝ) {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => |x - β| ^ r) (Ioc a b) := by
  have h1 : IntervalIntegrable (fun x : ℝ => (x - β) ^ r) volume a b := by
    have := (intervalIntegrable_rpow' (a := a - β) (b := b - β) hr).comp_sub_right β
    simpa using this
  have h2 : IntervalIntegrable (fun x : ℝ => (β - x) ^ r) volume a b := by
    have := (intervalIntegrable_rpow' (a := β - a) (b := β - b) hr).comp_sub_left β
    simpa using this
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at h1 h2
    have hsplit : Ioc a b = (Ioc a b ∩ Iic β) ∪ (Ioc a b ∩ Ioi β) := by
      rw [← inter_union_distrib_left, Iic_union_Ioi, inter_univ]
    rw [hsplit]
    apply IntegrableOn.union
    · refine (h2.mono_set inter_subset_left).congr_fun ?_
        (measurableSet_Ioc.inter measurableSet_Iic)
      intro x hx
      simp only
      rw [abs_of_nonpos (by linarith [mem_Iic.mp hx.2]), neg_sub]
    · refine (h1.mono_set inter_subset_left).congr_fun ?_
        (measurableSet_Ioc.inter measurableSet_Ioi)
      intro x hx
      simp only
      rw [abs_of_pos (by linarith [mem_Ioi.mp hx.2])]
  · rw [Ioc_eq_empty (not_lt.mpr hab.le)]
    exact integrableOn_empty

/-- **Lebesgue measure restricted to a bounded interval is finite.**

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_logDeriv_zeta_rect`, `littlewood_identity_argZetaDef`. -/
theorem isFiniteMeasure_restrict_Ioc (a b : ℝ) : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-- **A vertical line `{q.1 = β}` is null in the plane** (`Measure.prod_prod`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_inv_norm_sub_prod`, `integrable_logDeriv_zeta_rect`. -/
theorem prod_null_fst (β : ℝ) :
    (volume.prod volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.1 = β} = 0 := by
  have : {q : ℝ × ℝ | q.1 = β} = ({β} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext q; simp
  rw [this, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- **A horizontal line `{q.2 = γ}` is null in the plane** (`Measure.prod_prod`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_inv_norm_sub_prod`. -/
theorem prod_null_snd (γ : ℝ) :
    (volume.prod volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.2 = γ} = 0 := by
  have : {q : ℝ × ℝ | q.2 = γ} = (univ : Set ℝ) ×ˢ ({γ} : Set ℝ) := by
    ext q; simp
  rw [this, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **The AM–GM domination `1/‖s−p‖ ≤ (√2)⁻¹ |x−β|^{-1/2} |y−γ|^{-1/2}`** off the two lines through
`p = β + iγ`, for `s = x + iy`: from `(x−β)² + (y−γ)² ≥ 2|x−β||y−γ|`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_inv_norm_sub_prod`. -/
theorem inv_norm_sub_le_prod {x y : ℝ} {p : ℂ} (hx : x ≠ p.re) (hy : y ≠ p.im) :
    1 / ‖(x : ℂ) + y * I - p‖
      ≤ (Real.sqrt 2)⁻¹ * (|x - p.re| ^ (-(1 / 2 : ℝ)) * |y - p.im| ^ (-(1 / 2 : ℝ))) := by
  set u := |x - p.re| with hu
  set v := |y - p.im| with hv
  have hu0 : 0 < u := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hv0 : 0 < v := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hnorm : ‖(x : ℂ) + y * I - p‖ = Real.sqrt ((x - p.re) ^ 2 + (y - p.im) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, sub_im, add_im, mul_im, zero_add]
    ring
  have hamgm : 2 * u * v ≤ (x - p.re) ^ 2 + (y - p.im) ^ 2 := by
    have := sq_nonneg (u - v)
    rw [hu, hv] at *
    nlinarith [sq_abs (x - p.re), sq_abs (y - p.im)]
  have hsq : Real.sqrt (2 * u * v) ≤ Real.sqrt ((x - p.re) ^ 2 + (y - p.im) ^ 2) :=
    Real.sqrt_le_sqrt hamgm
  have hsq2 : Real.sqrt (2 * u * v) = Real.sqrt 2 * Real.sqrt u * Real.sqrt v := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have hrpow_u : u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hu0.le]
  have hrpow_v : v ^ (-(1 / 2 : ℝ)) = (Real.sqrt v)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hv0.le]
  rw [hnorm, hrpow_u, hrpow_v]
  have hpos : 0 < Real.sqrt 2 * Real.sqrt u * Real.sqrt v := by positivity
  rw [show (Real.sqrt 2)⁻¹ * ((Real.sqrt u)⁻¹ * (Real.sqrt v)⁻¹)
      = 1 / (Real.sqrt 2 * Real.sqrt u * Real.sqrt v) by field_simp]
  apply one_div_le_one_div_of_le hpos
  rw [← hsq2]
  exact hsq

/-- **`1/‖s − p‖` is integrable on a rectangle of the plane.** Dominated a.e. (off the two null
lines through `p`, `prod_null_fst`/`prod_null_snd`) by the product
`(√2)⁻¹ |x−β|^{-1/2} |y−γ|^{-1/2}` (`inv_norm_sub_le_prod`), which is integrable as a product of
two integrable functions of one variable (`Integrable.mul_prod`, `integrableOn_abs_sub_rpow_Ioc`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `integrableOn_abs_sub_rpow_Ioc`, `inv_norm_sub_le_prod`, `prod_null_fst`,
`prod_null_snd`, `ae_notMem_of_measure_zero`.
**Used by:** `integrable_logDeriv_zeta_rect`. -/
theorem integrable_inv_norm_sub_prod (p : ℂ) {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d) :
    Integrable (fun q : ℝ × ℝ => 1 / ‖(q.1 : ℂ) + q.2 * I - p‖)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  have hφ : Integrable (fun x : ℝ => |x - p.re| ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioc a b)) :=
    integrableOn_abs_sub_rpow_Ioc p.re a b (by norm_num)
  have hψ : Integrable (fun y : ℝ => |y - p.im| ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioc c d)) :=
    integrableOn_abs_sub_rpow_Ioc p.im c d (by norm_num)
  have hg : Integrable (fun q : ℝ × ℝ => (Real.sqrt 2)⁻¹
      * (|q.1 - p.re| ^ (-(1 / 2 : ℝ)) * |q.2 - p.im| ^ (-(1 / 2 : ℝ))))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) :=
    (hφ.mul_prod hψ).const_mul _
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => 1 / ‖(q.1 : ℂ) + q.2 * I - p‖)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I - p) := by fun_prop
    have hm : Measurable (fun q : ℝ × ℝ => ‖(q.1 : ℂ) + q.2 * I - p‖⁻¹) := hc.norm.measurable.inv
    simpa only [one_div] using hm
  refine Integrable.mono' hg hmeas ?_
  have hnull : (volume.prod volume : Measure (ℝ × ℝ))
      ({q : ℝ × ℝ | q.1 = p.re} ∪ {q : ℝ × ℝ | q.2 = p.im}) = 0 :=
    measure_union_null (prod_null_fst p.re) (prod_null_snd p.im)
  have hae : ∀ᵐ q ∂(volume.prod volume : Measure (ℝ × ℝ)),
      q ∉ ({q : ℝ × ℝ | q.1 = p.re} ∪ {q : ℝ × ℝ | q.2 = p.im}) :=
    ae_notMem_of_measure_zero hnull
  rw [Measure.prod_restrict]
  refine (ae_restrict_of_ae hae).mono ?_
  intro q hq
  simp only [mem_union, mem_ofPred_eq, not_or] at hq
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_norm_sub_le_prod hq.1 hq.2

/-- **`ζ'/ζ` is measurable** (`measurable_deriv`, and `ζ` is continuous off the single point `1`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integrable_logDeriv_zeta_rect`. -/
theorem measurable_logDeriv_zeta : Measurable (logDeriv riemannZeta) := by
  have h1 : Measurable (deriv riemannZeta) := measurable_deriv riemannZeta
  have h2 : Measurable riemannZeta :=
    measurable_of_continuousOn_compl_singleton 1 analyticOn_riemannZeta.continuousOn
  exact h1.div h2

/-- **`(x,y) ↦ (ζ'/ζ)(x+iy)` is integrable on the rectangle `(σ0,σ1] × (T1,T2]`** — the fact
that licenses the interchange of the two integrals in Farzanfard's (2.6), which the sources take
for granted.

### Summary of Proof
Dominate by `Mb + Σ_ρ m_ρ/‖s−ρ‖` (`zeta_logDeriv_bound_on_rect`, valid off the zeros, hence off
the finitely many null vertical lines through them), which is integrable
(`integrable_inv_norm_sub_prod`); measurability from `measurable_logDeriv_zeta`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zeta_logDeriv_bound_on_rect`, `integrable_inv_norm_sub_prod`,
`isFiniteMeasure_restrict_Ioc`, `measurable_logDeriv_zeta`, `prod_null_fst`,
`ae_notMem_of_measure_zero`, `zetaZerosIn`.
**Used by:** `littlewood_identity_argZetaDef`. -/
theorem integrable_logDeriv_zeta_rect (hσ : σ0 ≤ σ1) (hT : T1 ≤ T2) (hT1 : 0 < T1) :
    Integrable (Function.uncurry fun x y : ℝ => logDeriv riemannZeta ((x : ℂ) + y * I))
      ((volume.restrict (Ioc σ0 σ1)).prod (volume.restrict (Ioc T1 T2))) := by
  set Z := zetaZerosIn σ0 σ1 T1 T2 with hZ
  obtain ⟨Mb, hMb⟩ := zeta_logDeriv_bound_on_rect (σ0 := σ0) (σ1 := σ1) (T2 := T2) hT1
  have := isFiniteMeasure_restrict_Ioc σ0 σ1
  have := isFiniteMeasure_restrict_Ioc T1 T2
  set μ : Measure (ℝ × ℝ) := (volume.restrict (Ioc σ0 σ1)).prod (volume.restrict (Ioc T1 T2))
    with hμ
  have hD : Integrable (fun q : ℝ × ℝ =>
      Mb + ∑ p ∈ Z, (zetaMult p : ℝ) * (1 / ‖(q.1 : ℂ) + q.2 * I - p‖)) μ := by
    apply Integrable.add (integrable_const _)
    apply integrable_finsetSum
    intro p _
    exact (integrable_inv_norm_sub_prod p hσ hT).const_mul _
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y : ℝ => logDeriv riemannZeta ((x : ℂ) + y * I)) μ := by
    apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) := by fun_prop
    exact measurable_logDeriv_zeta.comp hc.measurable
  refine Integrable.mono' hD hmeas ?_
  have hBnull : (volume.prod volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | ∃ p ∈ Z, q.1 = p.re} = 0 := by
    have : {q : ℝ × ℝ | ∃ p ∈ Z, q.1 = p.re} = ⋃ p ∈ Z, {q : ℝ × ℝ | q.1 = p.re} := by
      ext q; simp
    rw [this]
    exact (measure_biUnion_null_iff Z.countable_toSet).mpr (fun p _ => prod_null_fst p.re)
  have hae1 : ∀ᵐ q ∂μ, q ∉ {q : ℝ × ℝ | ∃ p ∈ Z, q.1 = p.re} := by
    rw [hμ, Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_notMem_of_measure_zero hBnull)
  have hae2 : ∀ᵐ q ∂μ, q ∈ Ioc σ0 σ1 ×ˢ Ioc T1 T2 := by
    rw [hμ, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hae1, hae2] with q hq1 hq2
  have hq1'' : ∀ p ∈ Z, q.1 ≠ p.re := fun p hp h => hq1 ⟨p, hp, h⟩
  obtain ⟨hq1', hq2'⟩ := mem_prod.mp hq2
  have hsR : (q.1 : ℂ) + q.2 * I ∈ rectC σ0 σ1 T1 T2 := by
    rw [mem_rectC_iff]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    exact ⟨⟨hq1'.1.le, hq1'.2⟩, ⟨hq2'.1.le, hq2'.2⟩⟩
  have hsZ : (q.1 : ℂ) + q.2 * I ∉ (↑Z : Set ℂ) := by
    intro hmem
    exact hq1'' _ (Finset.mem_coe.mp hmem) (by simp)
  have hb := hMb _ ⟨hsR, hsZ⟩
  refine hb.trans (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

/-! ### The identity -/

/-- **`y ↦ ζ(σ+iy)` is continuous for `σ > 1`.**

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `littlewood_identity_argZetaDef`. -/
theorem continuous_zeta_vertical {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun y : ℝ => riemannZeta ((σ : ℂ) + y * I)) := by
  have hmap : Continuous (fun y : ℝ => (σ : ℂ) + y * I) := by fun_prop
  have hne : ∀ y : ℝ, (σ : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [continuous_iff_continuousAt]; intro y
  exact ((analyticOn_riemannZeta _ (hne y)).continuousAt).comp_of_eq hmap.continuousAt rfl

/-- **`log‖ζ(σ0 + iy)‖` is integrable near every `y0 ≠ 0`, including across a zero of `ζ`.**
This is the "improper integral" reading of `∫ log|ζ(σ0+it)| dt` in the tex: at a zero
`p = σ0 + i y0` of order `m`, `ζ(s) = (s-p)^m g(s)` with `g` analytic and nonvanishing near `p`,
so `log‖ζ(σ0+iy)‖ = m·log|y-y0| + log‖g(σ0+iy)‖`, and `log|y-y0|` is integrable.

### Summary of Proof
Case split on `ζ(p) = 0`. If not, `log‖ζ‖` is continuous on a small interval around `y0` (the
pole `s = 1` is avoided by shrinking the interval to radius `< |y0|`), and
`ContinuousOn.integrableAt_nhdsWithin` applies. If so,
`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` (with `riemannZeta_not_eventually_zero`)
gives the factorisation on a ball of radius `ε`; on `U = (y0-ε/2, y0+ε/2)` the function
`n·log(y-y0) + log‖g(σ0+iy)‖` is integrable (`intervalIntegrable_log'` shifted by
`comp_sub_right`, and continuity of `log‖g‖` on the closed interval), and it agrees with
`log‖ζ(σ0+iy)‖` off the null set `{y0}` (`IntegrableOn.congr_fun_ae`).

### Lean Notes
`IntegrableAtFilter f (𝓝 y0)` is the local statement `LocallyIntegrableOn` needs;
`intervalIntegrable_log_norm_zeta_vertical` assembles it over a compact interval. The distance
along the vertical line is `dist (σ0 + iy) (σ0 + iy0) = |y - y0|` (`hdist`).

### References
tex: the improper-integral reading of `∫ log|ζ(σ0+it)| dt` in `\ref{eq:zerodensityintegral}`
(Equation 13).

### Dependencies
**Depends on:** `analyticOn_riemannZeta`, `riemannZeta_not_eventually_zero`,
`ae_notMem_of_measure_zero`.
**Used by:** `intervalIntegrable_log_norm_zeta_vertical`. -/
theorem log_norm_zeta_vertical_integrableAt {y0 : ℝ} (hy0 : y0 ≠ 0) :
    IntegrableAtFilter (fun y : ℝ => Real.log ‖riemannZeta ((σ0 : ℂ) + y * I)‖) (nhds y0) := by
  set p : ℂ := (σ0 : ℂ) + y0 * I with hp
  have hp1 : p ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp only [hp, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add, one_im] at this
    exact hy0 this
  have han : AnalyticAt ℂ riemannZeta p := analyticOn_riemannZeta p hp1
  have hmap : Continuous (fun y : ℝ => (σ0 : ℂ) + y * I) := by fun_prop
  have hdist : ∀ y : ℝ, dist ((σ0 : ℂ) + y * I) p = |y - y0| := by
    intro y
    rw [dist_eq_norm]
    have : (σ0 : ℂ) + y * I - p = ((y - y0 : ℝ) : ℂ) * I := by rw [hp]; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases hz : riemannZeta p = 0
  · obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      (riemannZeta_not_eventually_zero hp1)
    have hgne : ∀ᶠ z in nhds p, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
    have hgan : ∀ᶠ z in nhds p, AnalyticAt ℂ g z := hg.eventually_analyticAt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and (hgne.and hgan))
    set U := Ioo (y0 - ε / 2) (y0 + ε / 2) with hU
    set K := Icc (y0 - ε / 2) (y0 + ε / 2) with hK
    have hKball : ∀ y ∈ K, dist ((σ0 : ℂ) + y * I) p < ε := by
      intro y hy
      rw [hdist]
      have : |y - y0| ≤ ε / 2 := abs_sub_le_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
      linarith
    refine ⟨U, Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    -- the two pieces
    have hgcont : ContinuousOn (fun y : ℝ => Real.log ‖g ((σ0 : ℂ) + y * I)‖) K := by
      intro y hy
      obtain ⟨_, hgz, hgaz⟩ := hball (hKball y hy)
      exact ((hgaz.continuousAt.comp_of_eq hmap.continuousAt rfl).norm.log
        (norm_ne_zero_iff.mpr hgz)).continuousWithinAt
    have hgint : IntegrableOn (fun y : ℝ => Real.log ‖g ((σ0 : ℂ) + y * I)‖) U :=
      (hgcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hlogint : IntegrableOn (fun y : ℝ => (n : ℝ) * Real.log (y - y0)) U := by
      have h1 : IntervalIntegrable (fun y : ℝ => Real.log (y - y0)) volume (y0 - ε / 2)
          (y0 + ε / 2) := by
        have := (intervalIntegral.intervalIntegrable_log' (a := -(ε / 2))
          (b := ε / 2)).comp_sub_right y0
        rwa [show -(ε / 2) + y0 = y0 - ε / 2 by ring, show ε / 2 + y0 = y0 + ε / 2 by ring] at this
      have h2 : IntegrableOn (fun y : ℝ => Real.log (y - y0)) U :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp h1
      exact Integrable.const_mul h2 (n : ℝ)
    have hsum : IntegrableOn (fun y : ℝ => (n : ℝ) * Real.log (y - y0)
        + Real.log ‖g ((σ0 : ℂ) + y * I)‖) U := hlogint.add hgint
    -- a.e. on `U` this is the function
    refine hsum.congr_fun_ae ?_
    have hae1 : ∀ᵐ y ∂(volume.restrict U), y ∉ ({y0} : Set ℝ) :=
      ae_restrict_of_ae (ae_notMem_of_measure_zero (measure_singleton y0))
    have hae2 : ∀ᵐ y ∂(volume.restrict U), y ∈ U := ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae1, hae2] with y hy1 hy2
    have hyne : y ≠ y0 := fun h => hy1 (by simp [h])
    obtain ⟨hzeq, hgz, _⟩ := hball (hKball y (Ioo_subset_Icc_self hy2))
    have hsub : (σ0 : ℂ) + y * I - p = ((y - y0 : ℝ) : ℂ) * I := by rw [hp]; push_cast; ring
    rw [hzeq, hsub, smul_eq_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr
      (sub_ne_zero.mpr hyne))) (norm_ne_zero_iff.mpr hgz), Real.log_pow, Real.log_abs]
  · -- no zero at `p`: the function is continuous near `y0`
    have hne : ∀ᶠ z in nhds p, riemannZeta z ≠ 0 := han.continuousAt.eventually_ne hz
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hne
    -- shrink the radius so that the interval also avoids `y = 0` (the pole `s = 1`)
    set δ := min ε |y0| with hδdef
    have hδ : 0 < δ := lt_min hε (abs_pos.mpr hy0)
    set V := Ioo (y0 - δ) (y0 + δ) with hV
    have hVmem : y0 ∈ V := ⟨by linarith, by linarith⟩
    have hcont : ContinuousOn (fun y : ℝ => Real.log ‖riemannZeta ((σ0 : ℂ) + y * I)‖) V := by
      intro y hy
      have hyδ : |y - y0| < δ := abs_sub_lt_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have hyd : dist ((σ0 : ℂ) + y * I) p < ε := by
        rw [hdist]; exact lt_of_lt_of_le hyδ (min_le_left _ _)
      have hyne0 : y ≠ 0 := by
        intro hy0z
        rw [hy0z, zero_sub, abs_neg] at hyδ
        exact absurd (lt_of_lt_of_le hyδ (min_le_right _ _)) (lt_irrefl _)
      have hyne1 : (σ0 : ℂ) + y * I ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
          zero_add, one_im] at this
        exact hyne0 this
      exact (((analyticOn_riemannZeta _ hyne1).continuousAt.comp_of_eq hmap.continuousAt
        rfl).norm.log (norm_ne_zero_iff.mpr (hball hyd))).continuousWithinAt
    have := ContinuousOn.integrableAt_nhdsWithin (μ := volume) hcont measurableSet_Ioo hVmem
    rwa [isOpen_Ioo.nhdsWithin_eq hVmem] at this

/-- **`log‖ζ(σ0 + iy)‖` is interval-integrable on `[T1, T2]` for `0 < T1 ≤ T2`**, with no
zero-free hypothesis on the line `Re s = σ0`. This is the integrability that Equation 13 needs
for its left-edge integral, and it is why no such hypothesis appears in the identity below.

### Summary of Proof
Integrability on a compact set follows from local integrability at each of its points
(`LocallyIntegrableOn.integrableOn_isCompact`), which is `log_norm_zeta_vertical_integrableAt`
(every `y ∈ [T1, T2]` is nonzero since `T1 > 0`).

### References
tex: the improper-integral reading of `∫ log|ζ(σ0+it)| dt` in `\ref{eq:zerodensityintegral}`
(Equation 13).

### Dependencies
**Depends on:** `log_norm_zeta_vertical_integrableAt`.
**Used by:** `littlewood_identity_argZetaDef`. -/
theorem intervalIntegrable_log_norm_zeta_vertical (hT1 : 0 < T1) (hT : T1 ≤ T2) :
    IntervalIntegrable (fun y : ℝ => Real.log ‖riemannZeta ((σ0 : ℂ) + y * I)‖) volume T1 T2 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine LocallyIntegrableOn.integrableOn_isCompact ?_ isCompact_Icc
  intro y hy
  exact (log_norm_zeta_vertical_integrableAt (by linarith [hy.1] : (0 : ℝ) < y).ne').filter_mono
    nhdsWithin_le_nhds

/-- **Littlewood's identity, Equation `\ref{eq:zerodensityintegral}` (Equation 13), for the
constructed `arg ζ` (`LittlewoodMethod.argZetaDef`).** For `σ0 < σ1`, `1 < σ1`, `0 < T1 < T2`,
with no zero of `ζ` on the two horizontal edges `[σ0,σ1] + iT_j`:
`∫_{σ0}^{σ1} N(σ,T1,T2) dσ = (1/2π)(∫ log|ζ(σ0+it)| − ∫ log|ζ(σ1+it)| + ∫ argZetaDef(u+iT2) −
∫ argZetaDef(u+iT1))`.

### Summary of Proof
Farzanfard's proof of his Lemma 2.2 ("inversion of the order of a double integration"), which
is Titchmarsh's. With `f = ζ'/ζ`: `left_edge_identity` gives, for every `σ ∈ [σ0, σ1)` off the
finitely many abscissas of zeros, `i ∫_{T1}^{T2} f(σ+iy) dy = L(σ+iT2) − L(σ+iT1) − 2πi N(σ)` with
`L = logZetaLine`; integrate in `σ` and interchange (`integral_integral_swap`, licensed by
`integrable_logDeriv_zeta_rect`); for a.e. `y` the inner `∫_{σ0}^{σ1} f(σ+iy) dσ` is
`L(σ1+iy) − L(σ0+iy)` (`integral_logDerivZetaLine_eq_logZetaLine`). Taking **real parts** of the
interchanged identity: on the `σ`-side `Re(∫ f dy) = Im(i∫ f dy) = argZetaDef(σ+iT2) −
argZetaDef(σ+iT1) − 2πN(σ)`, on the `y`-side `Re(L(σ1+iy) − L(σ0+iy)) = log‖ζ(σ1+iy)‖ −
log‖ζ(σ0+iy)‖` (`re_logZetaLine_line'`). Split the integrals (all pieces are continuous except
`log‖ζ(σ0+iy)‖`, which is integrable across zeros by `intervalIntegrable_log_norm_zeta_vertical`;
`N` is antitone) and rearrange.

### Lean Notes
The hypotheses and their relation to the tex are discussed in the module docstring: `hz1`/`hz2`
are the tex's first case. There is no hypothesis on the left edge: the tex's improper integral
`∫ log|ζ(σ0+it)| dt` is the Lebesgue integral of an integrable function
(`intervalIntegrable_log_norm_zeta_vertical`). No hypothesis on `arg` appears: `argZetaDef` is
the function the proof constructs.

### References
tex: `\ref{eq:zerodensityintegral}` (Equation 13). Farzanfard, MSc thesis (UofL 2025), Lemma 2.2,
(2.5)–(2.8); `\cite[§9.9]{Titchmarsh1986}`, Theorem 9.9.1 and (9.9.2).

### Dependencies
**Depends on:** `Nsigma`, `argZetaDef`, `logZetaLine`, `left_edge_identity`,
`integrable_logDeriv_zeta_rect`, `integral_logDerivZetaLine_eq_logZetaLine`,
`re_logZetaLine_line'`, `argZetaDef_continuousOn_line'`, `continuous_zeta_vertical`,
`zeta_ne_zero_line_of_Icc`, `zetaZerosIn`, `Nrect_mono`, `isFiniteMeasure_restrict_Ioc`,
`ae_notMem_of_measure_zero`, `intervalIntegrable_log_norm_zeta_vertical`.
**Used by:** `littlewood_zero_density_integral`. -/
theorem littlewood_identity_argZetaDef (hσ : σ0 < σ1) (hσ1 : 1 < σ1) (hT : T1 < T2) (hT1 : 0 < T1)
    (hz1 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T1 * I) ≠ 0)
    (hz2 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T2 * I) ≠ 0) :
    ∫ σ in σ0..σ1, (Nsigma σ T1 T2 : ℝ)
      = (1 / (2 * Real.pi)) *
          ((∫ t in T1..T2, Real.log ‖riemannZeta (σ0 + t * I)‖)
            - (∫ t in T1..T2, Real.log ‖riemannZeta (σ1 + t * I)‖)
            + (∫ u in σ0..σ1, argZetaDef (u + T2 * I))
            - (∫ u in σ0..σ1, argZetaDef (u + T1 * I))) := by
  have hT2 : 0 < T2 := lt_trans hT1 hT
  set Z := zetaZerosIn σ0 σ1 T1 T2 with hZ
  set f : ℝ → ℝ → ℂ := fun x y => logDeriv riemannZeta ((x : ℂ) + y * I) with hf
  have := isFiniteMeasure_restrict_Ioc σ0 σ1
  have := isFiniteMeasure_restrict_Ioc T1 T2
  have hF : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc σ0 σ1)).prod (volume.restrict (Ioc T1 T2))) :=
    integrable_logDeriv_zeta_rect hσ.le hT.le hT1
  have hFub := integral_integral_swap hF
  have hL : Integrable (fun x => ∫ y in Ioc T1 T2, f x y) (volume.restrict (Ioc σ0 σ1)) :=
    hF.integral_prod_left
  have hR : Integrable (fun y => ∫ x in Ioc σ0 σ1, f x y) (volume.restrict (Ioc T1 T2)) :=
    hF.integral_prod_right
  have hre := congrArg Complex.re hFub
  have h1 := integral_re hL
  have h2 := integral_re hR
  simp only [RCLike.re_to_complex] at h1 h2
  rw [← h1, ← h2] at hre
  have hLeq : (∫ x in Ioc σ0 σ1, (∫ y in Ioc T1 T2, f x y).re)
      = ∫ x in σ0..σ1, (∫ y in T1..T2, f x y).re := by
    rw [intervalIntegral.integral_of_le hσ.le]
    congr 1; funext x
    rw [intervalIntegral.integral_of_le hT.le]
  have hReq : (∫ y in Ioc T1 T2, (∫ x in Ioc σ0 σ1, f x y).re)
      = ∫ y in T1..T2, (∫ x in σ0..σ1, f x y).re := by
    rw [intervalIntegral.integral_of_le hT.le]
    congr 1; funext y
    rw [intervalIntegral.integral_of_le hσ.le]
  rw [hLeq, hReq] at hre
  -- the left side: for a.e. `x`, the residue identity
  have hBfin : ((fun p : ℂ => p.re) '' (↑Z : Set ℂ)).Finite := (Finset.finite_toSet Z).image _
  have hBnull : volume ((fun p : ℂ => p.re) '' (↑Z : Set ℂ) ∪ {σ1}) = 0 :=
    measure_union_null (hBfin.countable.measure_zero _) (measure_singleton _)
  have hae_x : ∀ᵐ x ∂volume, x ∉ ((fun p : ℂ => p.re) '' (↑Z : Set ℂ) ∪ {σ1}) :=
    ae_notMem_of_measure_zero hBnull
  have hIm : ∀ J : ℂ, (I * J).im = J.re := fun J => by simp
  have hLHS : ∫ x in σ0..σ1, (∫ y in T1..T2, f x y).re
      = ∫ x in σ0..σ1, (argZetaDef ((x : ℂ) + T2 * I) - argZetaDef ((x : ℂ) + T1 * I)
          - 2 * Real.pi * (Nsigma x T1 T2 : ℝ)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae_x] with x hx hxI
    simp only [mem_union, mem_image, Finset.mem_coe, mem_singleton_iff, not_or, not_exists,
      not_and] at hx
    obtain ⟨hxB, hxσ1⟩ := hx
    rw [uIoc_of_le hσ.le] at hxI
    have hx0 : σ0 ≤ x := hxI.1.le
    have hxσ1' : x < σ1 := lt_of_le_of_ne hxI.2 hxσ1
    have hσB : ∀ p ∈ Z, p.re ≠ x := fun p hp h => hxB p hp h
    have hid := left_edge_identity hσ1 hT hT1 hz1 hz2 hx0 hxσ1' hσB
    have hkey : (∫ y in T1..T2, f x y).re = (I * ∫ y in T1..T2, logDerivZetaLine y x).im := by
      rw [hIm]; rfl
    rw [hkey, hid]
    simp [argZetaDef]
  -- the right side: for a.e. `y`, the horizontal fundamental theorem of calculus
  have hCfin : ((fun p : ℂ => p.im) '' (↑Z : Set ℂ)).Finite := (Finset.finite_toSet Z).image _
  have hae_y : ∀ᵐ y ∂volume, y ∉ (fun p : ℂ => p.im) '' (↑Z : Set ℂ) :=
    ae_notMem_of_measure_zero (hCfin.countable.measure_zero _)
  have hRHS : ∫ y in T1..T2, (∫ x in σ0..σ1, f x y).re
      = ∫ y in T1..T2, (Real.log ‖riemannZeta ((σ1 : ℂ) + y * I)‖
          - Real.log ‖riemannZeta ((σ0 : ℂ) + y * I)‖) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae_y] with y hy hyI
    simp only [mem_image, Finset.mem_coe, not_exists, not_and] at hy
    rw [uIoc_of_le hT.le] at hyI
    have hy0 : y ≠ 0 := by linarith [hyI.1]
    have hzf : ∀ x, σ0 ≤ x → riemannZeta ((x : ℂ) + y * I) ≠ 0 := by
      intro x hx h0
      have hx1 : x < 1 := by
        have := zeta_zero_re_lt_one' h0
        simpa using this
      refine hy ((x : ℂ) + y * I) ?_ (by simp)
      refine mem_zetaZerosIn.mpr ⟨mem_rectC_iff.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h0⟩
      · simpa using hx
      · simp; linarith
      · simpa using hyI.1.le
      · simpa using hyI.2
    have hint : (∫ x in σ0..σ1, f x y)
        = logZetaLine ((σ1 : ℂ) + y * I) - logZetaLine ((σ0 : ℂ) + y * I) :=
      integral_logDerivZetaLine_eq_logZetaLine hy0 hzf hσ.le
    rw [hint, Complex.sub_re, re_logZetaLine_line' hy0 hzf hσ.le,
      re_logZetaLine_line' hy0 hzf le_rfl]
  rw [hLHS, hRHS] at hre
  -- integrability of the pieces, to split the integrals
  have hint_arg2 :
      IntervalIntegrable (fun x : ℝ => argZetaDef ((x : ℂ) + T2 * I)) volume σ0 σ1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hσ.le]
    exact argZetaDef_continuousOn_line' hT2.ne' (zeta_ne_zero_line_of_Icc hσ1 hz2 le_rfl)
  have hint_arg1 :
      IntervalIntegrable (fun x : ℝ => argZetaDef ((x : ℂ) + T1 * I)) volume σ0 σ1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hσ.le]
    exact argZetaDef_continuousOn_line' hT1.ne' (zeta_ne_zero_line_of_Icc hσ1 hz1 le_rfl)
  have hint_N : IntervalIntegrable (fun x : ℝ => (Nsigma x T1 T2 : ℝ)) volume σ0 σ1 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hσ.le]
    intro x _ y _ hxy
    simp only [Nsigma]
    exact_mod_cast Nrect_mono hT1 (by linarith : 1 - y ≤ 1 - x)
  have hint_l1 : IntervalIntegrable (fun y : ℝ => Real.log ‖riemannZeta ((σ1 : ℂ) + y * I)‖)
      volume T1 T2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log
    · exact (continuous_zeta_vertical hσ1).norm.continuousOn
    · intro y _
      exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simp [hσ1]))
  have hint_l0 : IntervalIntegrable (fun y : ℝ => Real.log ‖riemannZeta ((σ0 : ℂ) + y * I)‖)
      volume T1 T2 := intervalIntegrable_log_norm_zeta_vertical hT1 hT.le
  rw [intervalIntegral.integral_sub (hint_arg2.sub hint_arg1) (hint_N.const_mul _),
    intervalIntegral.integral_sub hint_arg2 hint_arg1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hint_l1 hint_l0] at hre
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hY : (∫ t in T1..T2, Real.log ‖riemannZeta ((σ0 : ℂ) + t * I)‖)
      - (∫ t in T1..T2, Real.log ‖riemannZeta ((σ1 : ℂ) + t * I)‖)
      + (∫ u in σ0..σ1, argZetaDef ((u : ℂ) + T2 * I))
      - (∫ u in σ0..σ1, argZetaDef ((u : ℂ) + T1 * I))
      = 2 * Real.pi * ∫ σ in σ0..σ1, (Nsigma σ T1 T2 : ℝ) := by linarith [hre]
  rw [hY, ← mul_assoc, one_div_mul_cancel hπ, one_mul]

/-! ### `argZetaDef` on a line zero-free from `a` onwards -/

/-- **`argZetaDef` is an argument of `ζ` on a line zero-free from `a`**
(`LittlewoodMethod.zeta_eq_norm_mul_exp_argZetaDef` in the `[a,∞)` formulation).

### References
tex: the definition of `arg f` by continuous variation, first case.

### Dependencies
**Depends on:** `exp_logZetaLine_line'`, `argZetaDef`.
**Used by:** `LittlewoodShort.littlewoodshort`, `littlewoodshort_tight` (as the polar-form input
`hargf` of `ArgIntegrals.arg_integrals`, for `argZeta = argZetaDef`). -/
theorem zeta_eq_norm_mul_exp_argZetaDef' {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x, a ≤ x → riemannZeta ((x : ℂ) + T * I) ≠ 0) {σ : ℝ} (hσ : a ≤ σ) :
    riemannZeta ((σ : ℂ) + T * I)
      = ‖riemannZeta ((σ : ℂ) + T * I)‖
          * Complex.exp ((argZetaDef ((σ : ℂ) + T * I) : ℂ) * I) := by
  have h := exp_logZetaLine_line' hT hzf hσ
  set L := logZetaLine ((σ : ℂ) + T * I) with hL
  have hnorm : ‖riemannZeta ((σ : ℂ) + T * I)‖ = Real.exp L.re := by
    rw [← h, Complex.norm_exp]
  rw [hnorm, ← h]
  unfold argZetaDef
  rw [← hL, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  exact (Complex.re_add_im L).symm

/-- **Littlewood's zero-counting identity**, Equation `\ref{eq:zerodensityintegral}` (Equation 13),
stated for `argZeta`.

### Summary of Proof
`littlewood_identity_argZetaDef`, verbatim: `argZeta` *is* the constructed `argZetaDef`
(`LittlewoodMethod.argZeta`), so the two statements are definitionally equal.

### Lean Notes
The hypotheses are those of `littlewood_identity_argZetaDef` — `σ0 < σ1`, `1 < σ1`, `0 < T1 < T2`,
zero-free horizontal edges `hz1`/`hz2` (the tex's first case). Nothing is assumed on the left
edge, where `intervalIntegrable_log_norm_zeta_vertical` supplies the tex's improper integral, and
nothing is assumed about `arg`, since `argZeta` is the branch the proof constructs.

`hz1`/`hz2` are genuinely needed: on a horizontal line through a zero the tex switches to its
halving convention, and there `Nsigma` (which counts `T1 < Im ρ ≤ T2`) and the tex's
half-counting differ, so no identity is claimed at those heights.

**Which branch the two horizontal integrals use:** one and the same analytic function on the slit
rectangle, pinned by the common branch `G` on the right edge — see the module docstring.

### References
tex: `\ref{eq:zerodensityintegral}` (Equation 13), and the paragraph after it defining `arg f`.
**Proof based on:** Farzanfard, *Explicit zero density estimates for the Riemann zeta function*,
MSc thesis, University of Lethbridge 2025
(https://hdl.handle.net/10133/7053), Lemma 2.2 with
equations (2.5)–(2.8), which follows Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
§9.9, Theorem 9.9.1 and (9.9.2) (`\cite[§9.9]{Titchmarsh1986}`,
Titchmarsh–Heath-Brown, 2nd ed., ISBN 978-0-19-853369-6).

### Dependencies
**Depends on:** `littlewood_identity_argZetaDef`, `Nsigma`, `argZeta`.
**Used by:** `simplelittlewoodzerodensity`. -/
theorem littlewood_zero_density_integral (hσ : σ0 < σ1) (hσ1 : 1 < σ1) (hT : T1 < T2)
    (hT1 : 0 < T1)
    (hz1 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T1 * I) ≠ 0)
    (hz2 : ∀ x ∈ Icc σ0 σ1, riemannZeta (x + T2 * I) ≠ 0) :
    ∫ σ in σ0..σ1, (Nsigma σ T1 T2 : ℝ)
      = (1 / (2 * Real.pi)) *
          ((∫ t in T1..T2, Real.log ‖riemannZeta (σ0 + t * I)‖)
            - (∫ t in T1..T2, Real.log ‖riemannZeta (σ1 + t * I)‖)
            + (∫ u in σ0..σ1, argZeta (u + T2 * I))
            - (∫ u in σ0..σ1, argZeta (u + T1 * I))) :=
  littlewood_identity_argZetaDef hσ hσ1 hT hT1 hz1 hz2

end Identity

/-- **Equation `\ref{eq:simplelittlewoodzerodensity}` (Equation 14).** The standard specialization
of Littlewood's identity to a bound on `N(T-h,T+h,α)`.

### Summary of Proof
The `argZeta` integrals here run `σ0..σ1`, matching `littlewood_zero_density_integral`.

**Hypotheses beyond the source's statement.** `σ1 ≥ 1-α` (the source's proof sketch flags this
as a gap: "else this needs more care — not spelled out in the source") is needed to run the
sub-interval comparison below, and `0 < T-h` is needed so that `Definitions.Nrect_mono`/
`Nrect_nonneg` apply (these guarantee the counting region never contains `ζ`'s pole at `1`).
`0 < h` makes `T-h < T+h`. `littlewood_zero_density_integral`'s own hypotheses are inherited:
`1 < σ1` (right edge inside the half-plane of absolute convergence) and no zero of `ζ` on the two
horizontal edges (`hz_p`, `hz_m` — the tex's first case; its second case is the halving
convention, not formalized). No hypothesis on `argZeta` is needed, since `argZeta` *is* the tex's
`arg ζ` (`LittlewoodMethod.argZetaDef`), and nothing is assumed on the left edge `Re s = σ0`,
where the tex's improper `log|ζ(σ0+it)|` integral is handled by
`intervalIntegrable_log_norm_zeta_vertical`. All hold at the call sites
(`LittlewoodShort.littlewoodshort`, `littlewoodshort_tight`), which carry them as hypotheses.

**Proof.** `σ ↦ Nsigma σ T1 T2` is nonincreasing (`Nrect_mono`), so for `σ ∈ [σ0, 1-α]`,
`Nsigma σ T1 T2 ≥ Nsigma (1-α) T1 T2 = Nrect T1 T2 α`; integrating over that range and comparing
with `littlewood_zero_density_integral` (bounding the `[σ0,σ1]` integral below by the `[σ0,1-α]`
sub-integral, using `Nrect_nonneg` to drop the remaining nonnegative `[1-α,σ1]` piece) gives the
displayed bound after dividing by `1-σ0-α`.

### References
tex: `\ref{eq:simplelittlewoodzerodensity}` (Equation 14).

### Dependencies
**Depends on:** `Nrect`, `Nrect_mono`, `Nrect_nonneg`, `Nsigma`, `argZeta`,
`littlewood_zero_density_integral`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem simplelittlewoodzerodensity {T h α σ0 σ1 : ℝ} (hden : 0 < 1 - σ0 - α) (hh : 0 < h)
    (hT1 : 0 < T - h) (hσ1 : 1 - α ≤ σ1) (hσ1' : 1 < σ1)
    (hz_p : ∀ x ∈ Set.Icc σ0 σ1, riemannZeta (x + (T + h) * Complex.I) ≠ 0)
    (hz_m : ∀ x ∈ Set.Icc σ0 σ1, riemannZeta (x + (T - h) * Complex.I) ≠ 0) :
    (Nrect (T - h) (T + h) α : ℝ)
      ≤ (1 / (2 * Real.pi * (1 - σ0 - α))) *
          ((∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ0 + t * Complex.I)‖)
            - (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ1 + t * Complex.I)‖)
            + (∫ u in σ0..σ1, argZeta (u + (T + h) * Complex.I))
            - (∫ u in σ0..σ1, argZeta (u + (T - h) * Complex.I))) := by
  have hσ0le : σ0 ≤ 1 - α := by linarith
  have hσ0leσ1 : σ0 ≤ σ1 := hσ0le.trans hσ1
  have hσ0ltσ1 : σ0 < σ1 := by linarith
  have hTlt : T - h < T + h := by linarith
  -- `σ ↦ Nsigma σ T1 T2` is nonincreasing.
  have hanti : AntitoneOn (fun σ => (Nsigma σ (T - h) (T + h) : ℝ)) (Set.Icc σ0 σ1) := by
    intro x _ y _ hxy
    change (Nsigma y (T - h) (T + h) : ℝ) ≤ (Nsigma x (T - h) (T + h) : ℝ)
    simp only [Nsigma]
    exact_mod_cast Nrect_mono hT1 (by linarith : 1 - y ≤ 1 - x)
  have hint_1 :
      IntervalIntegrable (fun σ => (Nsigma σ (T - h) (T + h) : ℝ)) MeasureTheory.volume σ0
        (1 - α) := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0le]
    exact hanti.mono (Set.Icc_subset_Icc_right hσ1)
  have hint_2 :
      IntervalIntegrable (fun σ => (Nsigma σ (T - h) (T + h) : ℝ)) MeasureTheory.volume (1 - α)
        σ1 := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ1]
    exact hanti.mono (Set.Icc_subset_Icc_left hσ0le)
  -- Step 1: `Nrect T1 T2 α ≤ Nsigma σ T1 T2` pointwise for `σ ∈ [σ0, 1-α]`.
  have hpoint : ∀ σ ∈ Set.Icc σ0 (1 - α),
      (Nrect (T - h) (T + h) α : ℝ) ≤ (Nsigma σ (T - h) (T + h) : ℝ) := by
    intro σ hσ
    simp only [Nsigma]
    exact_mod_cast Nrect_mono hT1 (by linarith [hσ.2])
  -- Step 2: integrate Step 1 over `[σ0, 1-α]`.
  have hstep2 : (1 - α - σ0) * (Nrect (T - h) (T + h) α : ℝ)
      ≤ ∫ σ in σ0..(1 - α), (Nsigma σ (T - h) (T + h) : ℝ) := by
    have hconst : ∫ _ in σ0..(1 - α), (Nrect (T - h) (T + h) α : ℝ)
        = (1 - α - σ0) * (Nrect (T - h) (T + h) α : ℝ) := by
      rw [intervalIntegral.integral_const]; ring
    rw [← hconst]
    exact intervalIntegral.integral_mono_on hσ0le (intervalIntegrable_const) hint_1 hpoint
  -- Step 3: the remaining `[1-α, σ1]` piece is nonnegative, so dropping it only decreases things.
  have hstep3 : (0:ℝ) ≤ ∫ σ in (1 - α)..σ1, (Nsigma σ (T - h) (T + h) : ℝ) := by
    apply intervalIntegral.integral_nonneg hσ1
    intro σ _
    simp only [Nsigma]
    exact_mod_cast Nrect_nonneg hT1
  have hstep23 : (1 - α - σ0) * (Nrect (T - h) (T + h) α : ℝ)
      ≤ ∫ σ in σ0..σ1, (Nsigma σ (T - h) (T + h) : ℝ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_1 hint_2]
    linarith
  -- Step 4: substitute Littlewood's identity and rearrange.
  -- the identity is stated with the casts `↑(T ± h)`; the hypotheses here carry `↑T ± ↑h`
  have hz_m' : ∀ x ∈ Set.Icc σ0 σ1, riemannZeta (x + ((T - h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hz_m x hx
  have hz_p' : ∀ x ∈ Set.Icc σ0 σ1, riemannZeta (x + ((T + h : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; push_cast; exact hz_p x hx
  rw [littlewood_zero_density_integral hσ0ltσ1 hσ1' hTlt hT1 hz_m' hz_p']
    at hstep23
  push_cast at hstep23
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith [Real.pi_pos] : (0:ℝ) < 2 * Real.pi)]
    at hstep23
  rw [div_mul_eq_mul_div, one_mul,
    le_div_iff₀ (by have := Real.pi_pos; nlinarith : (0:ℝ) < 2 * Real.pi * (1 - σ0 - α))]
  nlinarith [hstep23]

