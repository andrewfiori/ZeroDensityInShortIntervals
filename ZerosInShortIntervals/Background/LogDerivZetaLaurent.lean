/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Background.ExternalFacts

/-! # Lemma `\ref{lemma:logderzetabound}`: Laurent coefficients of `-ζ'/ζ` near `s=1`

This file formalizes `Lemma \ref{lemma:logderzetabound}` (Lemma 38) of
`ZerosInShortIntervals.tex`, a generalization of the truncated Laurent estimate
`-ζ'/ζ(1+z) < 1/z - γ + (γ²+2γ₁)z` used by `Proposition \ref{prop:integraloutside}`
(Proposition 15); that estimate is exactly this lemma's `N=1` case for the upper bound, and is
derived at the end of this file as `neg_logDeriv_zeta_bound_of_claim_two`.  The file also proves
the Stieltjes-constant bridge `hasDerivAt_riemannZeta₀_one` (`(riemannZeta₀)'(1) = -γ₁`).

**Why radius `7` and three patches.** The tex works on the box `V = [-6,8]+i[-7,7]` and removes
the singularities of `ζ'/ζ` at `1, -2, -4, -6`, giving
`a_n = 3^{-n-1}+5^{-n-1}+7^{-n-1} + O^*(C·7^{-n})`. Three patches (`K=3`) is the smallest count
for which that bound forces `logDerivZetaCoeff n > 0` at **every** `n ≥ 1`: a single patch at
radius `4` gives only `|a_n - 3^{-n-1}| ≤ 1.4·4^{-n}`, which leaves the sign of `a_n` undetermined
for small `n`, and claim 2 needs positivity at every index. The tex's constant is `C = 0.6`; a
boundary scan finds the true maximum `≈ 0.590`, so `0.6` holds with margin to spare — see
`LaurentCertificate.logDerivZetaG_boundary_bound`.

The lemma's own proof (per Chirre–Helfgott, arXiv:2512.15709, Lemma A.7, attributed there to
A. Kalmynin) reduces to one numerical claim: `‖G(s)‖ ≤ 0.6` on the boundary of the box
`V = [-6,8]+i[-7,7]`, where `G(s) := -ζ'(s)/ζ(s) - 1/(s-1) + 1/(s+2) + 1/(s+4) + 1/(s+6)`. This
file:

* constructs `zetaReg(s) := (s-1)ζ(s)`, entire (regularized at the removable singularity `s=1`),
  from Mathlib's `riemannZeta_residue_one` plus its removable-singularity theorem
  (`differentiable_zetaReg`);
* writes `G(s) = -(deriv zetaReg s / zetaReg s) + 1/(s+2) + 1/(s+4) + 1/(s+6)` (an algebraic
  identity with the displayed formula for `s ≠ 1`, avoiding `s=1`'s removable-singularity issue
  entirely since `zetaReg` is already regularized there);
* records `zetaReg`'s zero-freeness on `V` away from the trivial zeros `s ∈ {-2,-4,-6}`
  (`zetaReg_ne_zero_on_box`) as following from the classical fact that the lowest nontrivial zero
  of `ζ` has height `> 14` (rules out *every* zero with `0 < Re s < 1`, `|Im s| ≤ 7` — no need for
  `ExternalFacts.platt_trudgian_verified_below`'s critical-line information here, and `7 < 14` with
  room to spare) and the classical characterization of `ζ`'s zeros for `Re s ≤ 0` (the trivial
  zeros only, at the negative even integers; `s=-8`, the next one after `-6`, lies outside the box
  since the box's open real-part range is `(-6,8)`, EXCLUDING `-6` itself as an *interior* point,
  though `-6` sits in the box's frontier — see the boundary-bound discussion below) — the first
  read off the hypothesis field `LiteratureInputs.riemannZeta_lowest_zero_height` by the theorem
  `riemannZeta_lowest_zero_height`, the second PROVED from Mathlib's functional equation
  (`riemannZeta_eq_zero_of_re_nonpos`);
* constructs `G`'s holomorphic extension across its removable singularities at `s ∈ {-2,-4,-6}`
  (`logDerivZetaGext`, a definition by three `Function.update`s — the trivial zeros are proved
  simple by differentiating the functional equation, `deriv_riemannZeta_trivial_zero_ne_zero`, and
  Mathlib's removable-singularity theorem does the rest) and takes the numerical boundary bound
  itself as the single field of the hypothesis class `LaurentCertificate`
  (`logDerivZetaG_boundary_bound`, checked on a dense mesh by
  `Code/verify_lemmaA7_bound_radius7.sage` and independently by `Code/indep_mpmath_lemma37.py` —
  **note**: `s=-6` sits exactly on the box's frontier, not its interior, since the open box only
  reaches `Re s > -6`; the numerical scripts and this file's own boundary-bound statement both
  need to (and do) cover this point, via `logDerivZetaGext`'s own patched value there, not the raw
  `logDerivZetaG` which is undefined at `s=-6`);
* **proves** the reduction from those inputs to the coefficient bound
  `logDerivZetaCoeff_bound`, via the maximum modulus principle
  (`Complex.norm_le_of_forall_mem_frontier_norm_le`) and Cauchy's estimate for derivatives
  (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`);
* **proves** that `G`'s Taylor coefficients at `0` are real
  (`logDerivZetaCoeff_taylor_coeff_real`). Mathlib's `riemannZeta_conj`
  (`Mathlib.NumberTheory.Harmonic.ZetaAsymp`) supplies Schwarz reflection for `ζ` directly; it is
  propagated to `zetaReg`, `deriv zetaReg` and `logDerivZetaG` here via one general,
  hypothesis-free fact (`hasDerivAt_conj_comp_conj`: conjugating both input and output of a
  holomorphic map cancels the orientation reversal), then to every iterated derivative by
  induction;
* **proves** the coefficients are positive (`logDerivZetaCoeff_pos`) and that `a_n·x^n` is
  antitone on `x ∈ [0,2]` for **every** `n ≥ 0` (`logDerivZetaCoeff_antitone`). The `n ≥ 2` steps
  need no numeric input beyond claim 1's own bound; `n = 0 → 1` needs none either, since
  `logDerivZetaCoeff_zero` proves `a_0 = γ` *exactly* from Mathlib's
  `tendsto_riemannZeta_sub_one_div`; only `n = 1 → 2` needs numeric input, and that is routed
  through the exact identity `logDerivZetaCoeff_one` (`a_1 = γ² + 2γ₁`, the `n = 1` case of the
  source's own `Remark \ref{lemma:logderzetabound-remark}` (Remark 39)) together with
  `stieltjes_combo_numeric_bounds`, so that `logDerivZetaCoeff_one_bounds` (`0.15 ≤ a_1 ≤ 0.20`)
  is *derived* rather than postulated. Its docstring records why every Cauchy-estimate route
  provably cannot supply that step. That numeric bracket is in turn split into its two very
  unequal halves, both **proved**: `stieltjes_combo_lower_bound` (`0.15 ≤ γ²+2γ₁`) from
  `γ ≥ 0.5615` and `γ₁ ≥ -0.076`; `stieltjes_combo_upper_bound` (`γ²+2γ₁ ≤ 0.20`) from
  `γ ≤ 0.5851` and `γ₁ ≤ -0.0724`, the latter via the Euler–Maclaurin bracket
  `Definitions.stieltjesSeqHi` at `m = 16` (six prime logarithms instead of 139);
* states the full three-claim `Lemma \ref{lemma:logderzetabound}` as `logderzetabound`. All three
  claims are proved. Claim 1 is the coefficient bound. Claim 2 (the alternating-series bracket)
  rests on the `HasSum` identification of the Taylor series of `G(1+·)` with `-ζ'/ζ(1+x) - 1/x`
  (`hasSum_logDerivZetaCoeff`); `neg_logDeriv_zeta_lt_one_div` records the `N = 0` instance
  `-ζ'/ζ(1+x) < 1/x` on `(0,2]`, from that plus the antitone chain. Claim 3 (the FTC step) rests
  on `hasSum_logDerivZetaCoeff_integrated` — the termwise integration of that power series to
  `log‖ζ(1+x)‖ + log x` — obtained by matching derivatives of `Re G(1+y) + log y` and the
  integrated series on `(0,2)` and fixing the constant by the residue limit `y·ζ(1+y) → 1`.

Note also that `logderzetabound` is stated **without** a `1 ≤ N` hypothesis: the `N = 0` instance,
where the shorter partial sum is empty, is genuine extra content — see its own docstring for the
index convention and for the extra bounds this buys. -/

open Complex Filter Topology ComplexConjugate

/- The literature inputs this file needs (`riemannZeta_lowest_zero_height`, and whatever
`ExternalFacts` supplies) enter through the classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
below carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs]

/-! ## `zetaReg`: `(s-1)ζ(s)`, regularized to be entire -/

/-- **The regularised zeta function `zetaReg s = (s-1)ζ(s)`,** patched at `s = 1` to be entire.

### Summary of Proof
A definition. At the removable singularity `s = 1`, where `ζ` has its simple pole, the value is
set to the residue `1` (Mathlib's `riemannZeta_residue_one`). Entirety is `differentiable_zetaReg`.

### Lean Notes
No tex counterpart: the tex works with `(s-1)ζ(s)` informally and never names the regularised
function. Lean needs it so that the quotient `-(deriv zetaReg)/zetaReg` forming `G` has no
removable singularity at `s = 1` to reason around.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `deriv_zetaReg_conj`, `deriv_zetaReg_one`, `deriv_zetaReg_trivial_zero_ne_zero`,
`differentiable_zetaReg`, `hasDerivAt_deriv_zetaReg_one`, `hasDerivAt_zetaReg_one`,
`logDerivZetaCoeff_one`, `logDerivZetaG`, `logDerivZetaG_bddAbove_near_trivial_zero`,
`logDerivZetaG_shift_differentiableAt`, `logDeriv_zetaReg_eq`, `zetaReg_conj`, `zetaReg_eq_of_ne`,
`zetaReg_eq_riemannZeta₁`, `zetaReg_eq_zero_iff`, `zetaReg_ne_zero_iff`,
`zetaReg_ne_zero_of_mem_logDerivZetaGextW`, `zetaReg_ne_zero_on_box`, `zetaReg_one`,
`zetaReg_trivial_zero`. -/
noncomputable def zetaReg : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

/-- **Away from the patched point, `zetaReg` is literally `(s-1)ζ(s)`.**

### Summary of Proof
Pure bookkeeping: unfold `Function.update` at any `s ≠ 1`, which is exactly
`Function.update_of_ne`.

### References
No tex counterpart. `zetaReg` is a Lean-side device — the tex works with `(s-1)ζ(s)` informally
and never names the regularised function.

### Dependencies
**Depends on:** `zetaReg`.
**Used by:** `deriv_zetaReg_trivial_zero_ne_zero`, `hasDerivAt_zetaReg_one`,
`logDeriv_zetaReg_eq`, `zetaReg_conj`, `zetaReg_eq_riemannZeta₁`, `zetaReg_eq_zero_iff`,
`zetaReg_trivial_zero`. -/
theorem zetaReg_eq_of_ne {s : ℂ} (hs : s ≠ 1) : zetaReg s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs 1 _

/-- **The patched value: `zetaReg 1 = 1`.**

### Summary of Proof
True definitionally, by `Function.update_self`.

### Lean Notes
The value `1` is forced: it is `lim_{s→1}(s-1)ζ(s)`, the residue of `ζ`'s simple pole at `1`
(Mathlib's `riemannZeta_residue_one`), which is what makes `zetaReg` entire rather than merely
continuous.

### References
No tex counterpart. See `zetaReg_eq_of_ne`.

### Dependencies
**Depends on:** `zetaReg`.
**Used by:** `hasDerivAt_zetaReg_one`, `logDerivZetaCoeff_one`, `logDerivZetaCoeff_zero`,
`zetaReg_conj`, `zetaReg_eq_zero_iff`, `zetaReg_eq_riemannZeta₁`. -/
theorem zetaReg_one : zetaReg 1 = 1 := Function.update_self 1 1 _

/-- **`zetaReg` is Mathlib's `riemannZeta₁`,** as functions.

### Summary of Proof
Both sides are `1` at `s = 1` (`zetaReg_one`, `riemannZeta₁_one`). Away from `1`,
`riemannZeta_eq_inv_sub_mul` gives `ζ s = (s-1)⁻¹ · riemannZeta₁ s`, so
`(s-1)·ζ s = riemannZeta₁ s` after cancelling `(s-1) ≠ 0`; and `zetaReg s = (s-1)·ζ s` there by
`zetaReg_eq_of_ne`.

### Lean Notes
**Recorded because `zetaReg` duplicates Mathlib.** Mathlib's `riemannZeta₁` is the same
regularisation *extensionally, not definitionally* — this equation needs a case split and
`mul_inv_cancel₀`, so `rfl` will not close it. Mathlib's is
`riemannZeta₁ s = 1 + (s-1)·riemannZeta₀ s` with
`riemannZeta₀ s = ζ s - (s-1)⁻¹` patched by `γ` at `1`, in
`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` — and already supplies
`riemannZeta₁_one`, `differentiable_riemannZeta₁` and `deriv_riemannZeta₁_one`
(`ζ_reg'(1) = γ`), the exact content of `zetaReg_one`, `differentiable_zetaReg` and
`deriv_zetaReg_one` below. Each of the latter two is a one-line consequence of this equation:
`rw [zetaReg_eq_riemannZeta₁]; exact differentiable_riemannZeta₁` and
`rw [zetaReg_eq_riemannZeta₁, deriv_riemannZeta₁_one]`. They are left as they stand — the hand
proofs are correct and rewiring them is churn — but new work should prefer the Mathlib side.

**Why a `funext` equality and not an `EventuallyEq`.** The point of having it is to transport
statements about `deriv zetaReg`, and `deriv` is only rewritable under a genuine function
equality (`congrArg deriv`), not under agreement on a neighbourhood.

**This is the bridge that makes `hasDerivAt_deriv_zetaReg_one` a one-step consequence of the
Laurent-coefficient fact `ζ₀'(1) = -γ₁`**: with this equation,
`deriv zetaReg s = riemannZeta₀ s + (s-1)·(riemannZeta₀)'(s)` by the product rule, and
differentiating once more at `s = 1` the `(s-1)` factor annihilates the second-derivative term,
leaving `(ζ_reg)''(1) = 2·(riemannZeta₀)'(1) = -2γ₁`. The second differentiability of
`riemannZeta₀` needed for that step is Mathlib's `differentiable_riemannZeta₀.deriv`.

### References
No tex counterpart — a Lean-side identification of this file's `zetaReg` with Mathlib's
`riemannZeta₁`.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_one`, `zetaReg_eq_of_ne`.
**Used by:** `hasDerivAt_deriv_zetaReg_one`, which rewrites through it to reach Mathlib's
`riemannZeta₀`. It also documents the duplication with Mathlib. -/
theorem zetaReg_eq_riemannZeta₁ : zetaReg = riemannZeta₁ := by
  funext s
  rcases eq_or_ne s 1 with rfl | hs
  · rw [zetaReg_one, riemannZeta₁_one]
  · rw [zetaReg_eq_of_ne hs, riemannZeta_eq_inv_sub_mul hs, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero_of_ne hs), one_mul]

/-- **`zetaReg` is entire.**

### Summary of Proof
Two cases. Away from `s = 1`, `zetaReg` is literally `(s-1)ζ(s)`, differentiable because `ζ` is.
At `s = 1` this is Mathlib's removable-singularity theorem
`differentiableOn_update_limUnder_of_bddAbove`, applied using `riemannZeta_residue_one`: that
supplies both the boundedness near `1` (its norm eventually stays below `2`) and, via
`Filter.Tendsto.limUnder_eq`, that the limit is exactly the residue `1` — matching how `zetaReg`
was already defined, so the patched value is the right one.

### References
No tex counterpart. The tex takes the regularisation for granted.

### Dependencies
**Depends on:** `zetaReg`.
**Used by:** `deriv_zetaReg_conj`, `differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`,
`logDerivZetaG_bddAbove_near_trivial_zero`, `logDerivZetaG_shift_differentiableAt`. -/
theorem differentiable_zetaReg : Differentiable ℂ zetaReg := by
  intro s
  by_cases hs : s = 1
  · subst hs
    have htendsto := riemannZeta_residue_one
    have hbdd : ∀ᶠ s in 𝓝[≠] (1 : ℂ), ‖(s - 1) * riemannZeta s‖ < 2 :=
      htendsto.norm.eventually_lt_const (by norm_num)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hbdd
    obtain ⟨ε, hε0, hε⟩ := hbdd
    have hball : Metric.ball (1 : ℂ) ε ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds 1 hε0
    have hd : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
        (Metric.ball (1 : ℂ) ε \ {1}) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      exact DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz.2)
    have hb : BddAbove
        (norm ∘ (fun s : ℂ => (s - 1) * riemannZeta s) '' (Metric.ball (1 : ℂ) ε \ {1})) := by
      refine ⟨2, ?_⟩
      rintro x ⟨z, ⟨hz1, hz2⟩, rfl⟩
      simp only [Set.mem_singleton_iff, Metric.mem_ball] at hz1 hz2
      exact (hε hz1 hz2).le
    have hlim : limUnder (𝓝[≠] (1 : ℂ)) (fun s : ℂ => (s - 1) * riemannZeta s) = 1 :=
      htendsto.limUnder_eq
    have hdiff := differentiableOn_update_limUnder_of_bddAbove hball hd hb
    rw [hlim] at hdiff
    have heq : zetaReg = Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 := rfl
    rw [heq]
    exact (hdiff 1 (Metric.mem_ball_self hε0)).differentiableAt hball
  · have hda : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * riemannZeta s) s :=
      DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hs)
    have heq : zetaReg =ᶠ[𝓝 s] (fun s : ℂ => (s - 1) * riemannZeta s) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz using Function.update_of_ne hz 1 _
    exact hda.congr_of_eventuallyEq heq

/-- **`zetaReg`'s zero set is exactly `ζ`'s.**

### Summary of Proof
Case split on `s = 1`. There, `zetaReg 1 = 1 ≠ 0` and `ζ(1) ≠ 0` too (Mathlib's
`riemannZeta_ne_zero_of_one_le_re`), so both sides are false and the equivalence holds. Away from
`1`, `zetaReg s = (s-1)ζ(s)` is a product whose first factor is nonzero, so `mul_eq_zero` reduces
the claim to `ζ s = 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`, `zetaReg_one`.
**Used by:** `zetaReg_ne_zero_iff`. -/
theorem zetaReg_eq_zero_iff {s : ℂ} : zetaReg s = 0 ↔ riemannZeta s = 0 := by
  by_cases hs : s = 1
  · subst hs
    have h1 : riemannZeta (1:ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
    simp [zetaReg_one, h1]
  · rw [zetaReg_eq_of_ne hs]
    exact mul_eq_zero.trans (or_iff_right (sub_ne_zero.mpr hs))

/-- **Contrapositive of `zetaReg_eq_zero_iff`:** `zetaReg` is nonzero exactly where `ζ` is.

### Summary of Proof
`zetaReg_eq_zero_iff.not`.

### Lean Notes
This is the form actually consumed downstream: `zetaReg_ne_zero_on_box` needs non-vanishing in
order to divide by `zetaReg` when forming `G = -(deriv zetaReg)/zetaReg + …`, and it is cleaner
to transport `ζ`'s known zero-free regions across than to redo them for `zetaReg`.

### References
No tex counterpart — bookkeeping for the Lean-side `zetaReg`.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_zero_iff`.
**Used by:** `zetaReg_ne_zero_of_mem_logDerivZetaGextW`, `zetaReg_ne_zero_on_box`. -/
theorem zetaReg_ne_zero_iff {s : ℂ} : zetaReg s ≠ 0 ↔ riemannZeta s ≠ 0 :=
  zetaReg_eq_zero_iff.not

/-! ## Schwarz reflection

`riemannZeta_conj` (`riemannZeta (conj s) = conj (riemannZeta s)`) is already in Mathlib
(`Mathlib.NumberTheory.Harmonic.ZetaAsymp`), so no Dirichlet-series argument is needed here. All
that remains is to propagate it through `zetaReg`, `deriv zetaReg` and `logDerivZetaG`, which one
general, hypothesis-free fact about composing with conjugation twice accomplishes. -/

/-- **A holomorphic function's "double conjugate" is holomorphic,** with the expected derivative:
`HasDerivAt f f' z` gives `HasDerivAt (fun w => conj (f (conj w))) (conj f') (conj z)`.

### Summary of Proof
Purely formal, with no hypothesis on `f` beyond `HasDerivAt`: conjugating both the input and the
output of a holomorphic map cancels the orientation reversal that each conjugation introduces
separately. Proved directly from the `IsLittleO` characterisation of `HasDerivAt`, using that
conjugation is norm-preserving so the little-o estimate transports unchanged.

### References
No tex counterpart. The tex asserts realness of the Taylor coefficients without comment; this is
the first step of what Lean needs to prove it.

### Dependencies
**Depends on:** none.
**Used by:** `deriv_conj_of_conj_symm`, `deriv_zetaReg_conj`. -/
theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z) :
    HasDerivAt (fun w => conj (f (conj w))) (conj f') (conj z) := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  have hconj_tendsto : Tendsto (fun w : ℂ => conj w) (𝓝 (conj z)) (𝓝 z) := by
    have hc : Continuous (fun w : ℂ => conj w) := continuous_conj
    simpa using hc.tendsto (conj z)
  have hcomp0 : (fun w : ℂ => f (conj w) - f z - (conj w - z) * f')
      =o[𝓝 (conj z)] (fun w : ℂ => conj w - z) := h.comp_tendsto hconj_tendsto
  have hconj_iso : (fun w : ℂ => conj (f (conj w) - f z - (conj w - z) * f'))
      =o[𝓝 (conj z)] (fun w : ℂ => conj (conj w - z)) := by
    rw [Asymptotics.isLittleO_iff] at hcomp0 ⊢
    intro c hc
    filter_upwards [hcomp0 hc] with w hw
    simpa only [RCLike.norm_conj] using hw
  have heq1 : (fun w : ℂ => conj (f (conj w) - f z - (conj w - z) * f'))
      = (fun w : ℂ => conj (f (conj w)) - conj (f z) - (w - conj z) * conj f') := by
    funext w
    simp [map_sub, map_mul]
  have heq2 : (fun w : ℂ => conj (conj w - z)) = (fun w : ℂ => w - conj z) := by
    funext w
    simp [map_sub]
  rw [heq1, heq2] at hconj_iso
  have hgoalfun : (fun w : ℂ => conj (f (conj w)) - conj (f z) - (w - conj z) * conj f')
      = (fun w : ℂ => conj (f (conj w)) - conj (f (conj (conj z))) - (w - conj z) • conj f') := by
    funext w; rw [Complex.conj_conj]; rfl
  rwa [hgoalfun] at hconj_iso

/-- **`zetaReg` satisfies Schwarz reflection:** `zetaReg (conj s) = conj (zetaReg s)`.

### Summary of Proof
Case split on `s = 1`. Away from `1`, `zetaReg s = (s-1)ζ(s)` and Mathlib's `riemannZeta_conj`
gives the result directly, since `(s-1)` conjugates termwise. At `s = 1`, which `conj` fixes,
both sides are `1`.

### Lean Notes
`riemannZeta_conj` lives in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`; it is easy to miss when
searching, since the name mentions neither Schwarz nor reflection.

### References
No tex counterpart as a named result. The tex asserts realness of the Taylor coefficients of `G`
without comment, in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38).

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`, `zetaReg_one`.
**Used by:** `deriv_zetaReg_conj`, `logDerivZetaG_conj`. -/
theorem zetaReg_conj (s : ℂ) : zetaReg (conj s) = conj (zetaReg s) := by
  by_cases hs : s = 1
  · subst hs; simp [zetaReg_one]
  · have hs' : conj s ≠ 1 := by
      intro hc
      apply hs
      have := congrArg conj hc
      simpa using this
    rw [zetaReg_eq_of_ne hs', zetaReg_eq_of_ne hs, riemannZeta_conj]
    simp [map_sub, map_mul]

/-- **`deriv zetaReg` satisfies Schwarz reflection:**
`deriv zetaReg (conj s) = conj (deriv zetaReg s)`.

### Summary of Proof
Apply `hasDerivAt_conj_comp_conj` to `zetaReg`, then use `zetaReg_conj` to identify
`fun w => conj (zetaReg (conj w))` with `zetaReg` itself — pointwise, everywhere — and conclude
by uniqueness of the derivative.

### References
No tex counterpart. See `zetaReg_conj`.

### Dependencies
**Depends on:** `differentiable_zetaReg`, `hasDerivAt_conj_comp_conj`, `zetaReg`, `zetaReg_conj`.
**Used by:** `logDerivZetaG_conj`. -/
theorem deriv_zetaReg_conj (s : ℂ) : deriv zetaReg (conj s) = conj (deriv zetaReg s) := by
  have h1 : HasDerivAt zetaReg (deriv zetaReg s) s :=
    (differentiable_zetaReg s).hasDerivAt
  have h2 := hasDerivAt_conj_comp_conj h1
  have heqfun : (fun w => conj (zetaReg (conj w))) = zetaReg := by
    funext w
    rw [zetaReg_conj, Complex.conj_conj]
  rw [heqfun] at h2
  exact h2.deriv

/-! ## Zero-freeness of `ζ` on the box `V`, away from the trivial zeros `s = -2, -4` -/

/-- **The working box `V`:** the square `[-7,7]+i[-7,7]` in `z = s-1` coordinates.

### Summary of Proof
A definition. In `s` coordinates this is Chirre–Helfgott's box `V = [-6,8]+i[-7,7]`, i.e. radius
`7`, matching the tex's current `K = 3` version of the lemma.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), which says "We instead use a
radius of `7` and remove the singularities at `1`, `-2`, `-4`, and `-6`".
External: Chirre–Helfgott, arXiv:2512.15709, `\cite[Lemma A.7]{ChirreHelfgott2025}`.

### Dependencies
**Depends on:** none.
**Used by:** `_flat_ctor`, `ball7_subset_box`, `casesOn`, `closedBall7_subset_closure_box`,
`hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`,
`logDerivZetaCoeff_one`, and 12 further call sites. -/
noncomputable def logDerivZetaBox : Set ℂ := Set.Ioo (-7 : ℝ) 7 ×ℂ Set.Ioo (-7 : ℝ) 7

/-- **Classical fact:** the lowest nontrivial zero of `ζ` has `|Im ρ| > 14`.

### Summary of Proof
Not proved here — the statement reads the classical fact off the hypothesis field
`LiteratureInputs.riemannZeta_lowest_zero_height`. The true value is `≈ 14.134725`, first
located by Gram in 1903 and refined and verified many times since, including as part of the
computation underlying `ExternalFacts.platt_trudgian_verified_below`.

### Lean Notes
Stated as a bound on `|ρ.im|` rather than on `Re ρ`, which is what
`zetaReg_ne_zero_on_box` actually needs: it rules out *every* zero with `0 < Re ρ < 1` inside the
box directly, with no need to know `Re ρ = 1/2`. That is why
`ExternalFacts.platt_trudgian_verified_below` is not needed here, and why `7 < 14` closes the box
argument with room to spare.

It is a hypothesis-class field rather than a theorem because Mathlib has no explicit zero-free
region for `ζ` with usable constants and no verified zero enumeration; proving it here would mean
importing a verified zero-location computation, or combining an explicit zero-free region with a
Riemann–von Mangoldt counting argument.

### References
No tex counterpart as a numbered claim — the tex takes zero-freeness on its box for granted.

### Dependencies
**Depends on:** `Hypotheses.LiteratureInputs.riemannZeta_lowest_zero_height`.
**Used by:** `zetaReg_ne_zero_on_box`, `zetaReg_ne_zero_of_mem_logDerivZetaGextW`. -/
theorem riemannZeta_lowest_zero_height {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) : 14 < |ρ.im| :=
  LiteratureInputs.riemannZeta_lowest_zero_height hρ hre0 hre1

/-- **The only zeros of `ζ` with `Re s ≤ 0` are the trivial ones**, at the negative even
integers `s = -2(n+1)`.

### Summary of Proof
For `s ≠ 0` put `w = 1 - s`, so `Re w ≥ 1`. Mathlib's functional equation `riemannZeta_one_sub`
(valid since `w` is not a non-positive integer and `w ≠ 1`) gives
`ζ(s) = 2 (2π)^{-w} Γ(w) cos(πw/2) ζ(w)`. On the right `ζ(w) ≠ 0`
(`riemannZeta_ne_zero_of_one_le_re`), `Γ(w) ≠ 0` (`Complex.Gamma_ne_zero`) and `(2π)^{-w} ≠ 0`
(`Complex.cpow_eq_zero_iff`), so `ζ(s) = 0` forces `cos(πw/2) = 0`, i.e. `w = 2k+1` for an
integer `k` (`Complex.cos_eq_zero_iff`), i.e. `s = -2k`; `Re s ≤ 0` gives `k ≥ 0` and `s ≠ 0`
gives `k ≥ 1`, so `s = -2(n+1)` with `n = k-1`. For `s = 0`, `ζ(0) = -1/2` (`riemannZeta_zero`).

### Lean Notes
Mathlib names the trivial zeros (`riemannZeta_neg_two_mul_nat_add_one`) but not the
"completeness" direction proved here, which amounts to the nonvanishing of the other three
factors of the functional equation.

### References
No tex counterpart as a numbered claim; the tex takes it for granted when forming `G(z)` on
`|z| ≤ 7`.

### Dependencies
**Depends on:** none (Mathlib: `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`,
`riemannZeta_zero`, `Complex.Gamma_ne_zero`, `Complex.cos_eq_zero_iff`).
**Used by:** `zetaReg_ne_zero_of_mem_logDerivZetaGextW`, `zetaReg_ne_zero_on_box`,
`Reflection.NlineRe_one_eq_add`, `Reflection.Nrect_one_eq_add`,
`Reflection.divisor_support_finite_of_subset_strip`,
`HalvingConvention.zetaOrd_eq_zero_of_im_pos_of_re_nonpos`. -/
theorem riemannZeta_eq_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (hz : riemannZeta s = 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  by_cases hs0 : s = 0
  · exfalso
    rw [hs0, riemannZeta_zero] at hz
    norm_num at hz
  have hwre : 1 ≤ (1 - s).re := by simp; linarith
  have hwn : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : (1 - s) ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hz] at hfe
  have hζw : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hwn
  have h2π : ((2 : ℂ) * Real.pi) ^ (-(1 - s)) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    have := h.1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi] at this
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
    have h0 : (2 : ℂ) * (2 * Real.pi) ^ (-(1 - s)) * Complex.Gamma (1 - s)
        * Complex.cos (Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := hfe.symm
    simpa [h2π, hΓ, hζw] using h0
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hwk : (1 - s) = 2 * (k : ℂ) + 1 := by
    have h2 : (Real.pi : ℂ) * (1 - s) = (Real.pi : ℂ) * (2 * k + 1) := by
      linear_combination 2 * hk
    exact mul_left_cancel₀ hπ h2
  have hs_eq : s = -2 * (k : ℂ) := by linear_combination -hwk
  have hkre : s.re = -2 * (k : ℝ) := by rw [hs_eq]; simp
  have hk0 : 0 ≤ k := by
    have h1 : -2 * (k : ℝ) ≤ 0 := by rw [← hkre]; exact hs
    have h2 : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast h2
  have hk1 : k ≠ 0 := by
    intro h
    apply hs0
    rw [hs_eq, h]
    simp
  have hk1' : 0 ≤ k - 1 := by omega
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk1'
  refine ⟨m, ?_⟩
  rw [hs_eq]
  have hkm : (k : ℂ) = (m : ℂ) + 1 := by
    have : k = (m : ℤ) + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hkm]

/-- **`ζ`, equivalently `zetaReg`, is zero-free on the box `V` away from the trivial zeros
`z ∈ {-3,-5}`** (i.e. `s ∈ {-2,-4}`).

### Summary of Proof
Three regimes, by `Re s`.

* `Re s ≥ 1`: classical nonvanishing, Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
* `0 < Re s < 1`: `riemannZeta_lowest_zero_height` rules out *every* zero here, since it bounds
  `|Im s| > 14` directly while the box confines `|Im z| < 7`. No need to know `Re s = 1/2`, so
  `ExternalFacts.platt_trudgian_verified_below` is not needed, and `7 < 14` leaves room to spare.
* `Re s ≤ 0`: `riemannZeta_eq_zero_of_re_nonpos` says the only zeros are at negative even
  integers. The box's open real range is `(-7,7)` in `z`, i.e. `(-6,8)` in `s`, so the only ones
  inside are `s = -2, -4`, which are excluded by hypothesis.

### Lean Notes
`s = -6` does not need excluding: at radius `7` it lies exactly on the box's frontier, not its
*open* interior, so it is already outside `logDerivZetaBox`. See `logDerivZetaG_boundary_bound`
for how that point is handled separately. The next trivial zero `s = -8` lies strictly outside.

### References
tex: implicit in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), which forms
`G(z)` on `|z| ≤ 7` after removing the singularities at `1, -2, -4, -6` and takes the resulting
analyticity for granted.

### Dependencies
**Depends on:** `logDerivZetaBox`, `riemannZeta_eq_zero_of_re_nonpos`,
`riemannZeta_lowest_zero_height`, `zetaReg`, `zetaReg_ne_zero_iff`.
**Used by:** `logDerivZetaG_shift_differentiableAt`. -/
theorem zetaReg_ne_zero_on_box {z : ℂ} (hz : z ∈ logDerivZetaBox \ ({-3, -5} : Set ℂ)) :
    zetaReg (1 + z) ≠ 0 := by
  rw [zetaReg_ne_zero_iff]
  have hzbox : z ∈ logDerivZetaBox := hz.1
  have hne35 : z ≠ -3 ∧ z ≠ -5 := by
    simpa [Set.mem_insert_iff, not_or] using hz.2
  simp only [logDerivZetaBox, mem_reProdIm, Set.mem_Ioo] at hzbox
  obtain ⟨hre, him⟩ := hzbox
  have hsre : (1 + z).re = 1 + z.re := by simp
  have hsim : (1 + z).im = z.im := by simp
  intro hζ
  by_cases hre0 : (1 + z).re ≤ 0
  · obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos hre0 hζ
    have hz_eq : z = ((-2 * ((n : ℝ) + 1) - 1 : ℝ) : ℂ) := by
      have h1 : (1 : ℂ) + z = -2 * ((n : ℂ) + 1) := hn
      have h2 : ((-2 * ((n : ℝ) + 1) - 1 : ℝ) : ℂ) = -2 * ((n : ℂ) + 1) - 1 := by push_cast; ring
      rw [h2]; linear_combination h1
    have hnre : (((-2 * ((n:ℝ) + 1) - 1 : ℝ) : ℂ)).re = -2 * ((n:ℝ) + 1) - 1 := Complex.ofReal_re _
    rw [hz_eq, hnre] at hre
    have hn1 : n < 2 := by
      by_contra hn1
      push Not at hn1
      have h2r : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith [hre.1]
    interval_cases n
    · exact hne35.1 (by rw [hz_eq]; norm_num)
    · exact hne35.2 (by rw [hz_eq]; norm_num)
  · push Not at hre0
    by_cases hre1 : 1 ≤ (1 + z).re
    · exact riemannZeta_ne_zero_of_one_le_re hre1 hζ
    · push Not at hre1
      -- `riemannZeta_lowest_zero_height` alone (via `|ρ.im|`, no `Re ρ = 1/2` needed) already
      -- covers every zero with `0 < Re ρ < 1`; `platt_trudgian_verified_below` is not needed here.
      have hlow := riemannZeta_lowest_zero_height hζ hre0 hre1
      rw [hsim] at hlow
      have hbound : |z.im| < 7 := abs_lt.mpr him
      linarith

/-! ## `G(s) := -zetaReg'(s)/zetaReg(s) + 1/(s+2) + 1/(s+4) + 1/(s+6)`, and its removable
singularities at `s = -2, -4, -6` -/

/-- **The patched function `G`:**
`G(s) = -ζ'(s)/ζ(s) - 1/(s-1) + 1/(s+2) + 1/(s+4) + 1/(s+6)`.

### Summary of Proof
A definition, matching the tex's displayed `G` exactly. The tex writes
`G(z) = ζ'/ζ(1+z) + 1/z - 1/(z+3) - 1/(z+5) - 1/(z+7)`; in `s = 1+z` coordinates and with the
overall sign of `-ζ'/ζ`, that is this formula. The three patch terms remove the trivial zeros at
`s = -2, -4, -6`, and the `1/(s-1)` term removes `ζ`'s pole.

### Lean Notes
Written via `zetaReg` to sidestep the removable singularity at `s = 1` entirely: for `s ≠ 1`, the
quotient rule on `zetaReg(s) = (s-1)ζ(s)` gives
`-(deriv zetaReg s / zetaReg s) = -ζ'(s)/ζ(s) - 1/(s-1)`, so the first two displayed terms are a
single well-behaved quotient in Lean.

### References
tex: the displayed `G(z)` in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38).

### Dependencies
**Depends on:** `zetaReg`.
**Used by:** `differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`,
`logDerivZetaCoeff_one`, `logDerivZetaCoeff_taylor_coeff_real`, `logDerivZetaCoeff_zero`,
`logDerivZetaG_bddAbove_near_trivial_zero`, `logDerivZetaG_conj`,
`logDerivZetaG_shift_differentiableAt`, `logDerivZetaG_shift_iteratedDeriv_conj_symm`,
`logDerivZetaGext`, `logDerivZetaGext_eq`. -/
noncomputable def logDerivZetaG (s : ℂ) : ℂ :=
  -(deriv zetaReg s / zetaReg s) + 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6)

/-- **`logDerivZetaG` satisfies Schwarz reflection:**
`G (conj s) = conj (G s)`.

### Summary of Proof
Algebraic consequence of `deriv_zetaReg_conj` and `zetaReg_conj` for the quotient part, plus the
observation that the patch terms `1/(s+2k)` have real — hence conjugation-fixed — shifts, so each
conjugates termwise.

### References
No tex counterpart as a named result; the tex asserts realness of `G`'s Taylor coefficients
without comment in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38).

### Dependencies
**Depends on:** `deriv_zetaReg_conj`, `logDerivZetaG`, `zetaReg_conj`.
**Used by:** `logDerivZetaG_shift_iteratedDeriv_conj_symm`. -/
theorem logDerivZetaG_conj (s : ℂ) : logDerivZetaG (conj s) = conj (logDerivZetaG s) := by
  unfold logDerivZetaG
  rw [deriv_zetaReg_conj, zetaReg_conj]
  simp [map_ofNat (starRingEnd ℂ)]

/-! ### The trivial zeros are simple, and `G` extends holomorphically across them

The extension `logDerivZetaGext` of `G` across `s ∈ {-2,-4,-6}` rests on the simplicity of the
trivial zeros, a standard local computation carried out here: differentiating the functional
equation `ζ(s) = 2(2π)^{-(1-s)} Γ(1-s) cos(π(1-s)/2) ζ(1-s)` at `s = -2k` gives
`ζ'(-2k) = F(-2k)·(π/2)·(-1)^k ≠ 0`, hence `zetaReg = (s-p)·g` with `g(p) ≠ 0` near each trivial
zero `p`, hence `G = -g'/g + (the other patch terms)` on a punctured neighbourhood — bounded — and
Mathlib's removable-singularity theorem (`Complex.differentiableOn_update_limUnder_of_bddAbove`)
does the rest. -/

/-- **The trivial zeros are simple: `ζ'(-2k) ≠ 0` for `k ≥ 1`.**

### Summary of Proof
On a neighbourhood of `s₀ = -2k` (where `Re s < -1`) the functional equation
`riemannZeta_one_sub` reads `ζ(s) = F(s)·cos(π(1-s)/2)` with
`F(s) = 2(2π)^{-(1-s)} Γ(1-s) ζ(1-s)` differentiable at `s₀` (`Γ` and `ζ` are evaluated at
`1 - s₀ = 1 + 2k`). Differentiating the product at `s₀`: `cos(π(1-s₀)/2) = cos(π/2 + kπ) = 0` kills
the `F'` term and `sin(π/2 + kπ) = (-1)^k`, so `ζ'(s₀) = F(s₀)·(π/2)·(-1)^k`, and `F(s₀) ≠ 0`
(`Complex.Gamma_ne_zero`, `riemannZeta_ne_zero_of_one_le_re`, `Complex.cpow_eq_zero_iff`).

### References
Classical; no tex counterpart as a numbered claim (the tex writes `G` as analytic on `|z| ≤ 7`
without comment).

### Dependencies
**Depends on:** none (Mathlib: `riemannZeta_one_sub`, `Complex.differentiableAt_Gamma`,
`differentiableAt_riemannZeta`, `HasDerivAt.const_cpow`, `Complex.Gamma_ne_zero`).
**Used by:** `deriv_zetaReg_trivial_zero_ne_zero`. -/
theorem deriv_riemannZeta_trivial_zero_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    deriv riemannZeta (-2 * (k : ℂ)) ≠ 0 := by
  set s₀ : ℂ := -2 * (k : ℂ) with hs₀
  have hs₀re : s₀.re = -2 * (k : ℝ) := by simp [hs₀]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hopen : ∀ᶠ s in 𝓝 s₀, s.re < -1 := by
    have : Tendsto (fun s : ℂ => s.re) (𝓝 s₀) (𝓝 s₀.re) := (Complex.continuous_re.tendsto s₀)
    exact this.eventually (gt_mem_nhds (by rw [hs₀re]; linarith))
  have hfe : ∀ᶠ s in 𝓝 s₀, riemannZeta s
      = 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s)
          * Complex.cos (Real.pi * (1 - s) / 2) * riemannZeta (1 - s) := by
    filter_upwards [hopen] with s hs
    have h1 : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h2 : (1 - s) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have := riemannZeta_one_sub h1 h2
    rwa [sub_sub_cancel] at this
  set F : ℂ → ℂ := fun s => 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s)
    * riemannZeta (1 - s) with hF
  have hw : ∀ n : ℕ, (1 - s₀) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp [hs₀] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : (1 - s₀) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hs₀] at this
    linarith
  have hFd : DifferentiableAt ℂ F s₀ := by
    have hsub : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s₀ := (differentiableAt_id.const_sub 1)
    have hpow : DifferentiableAt ℂ (fun s : ℂ => (2 * (Real.pi : ℂ)) ^ (-(1 - s))) s₀ := by
      have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
        have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        exact mul_ne_zero two_ne_zero this
      exact (hsub.neg.hasDerivAt.const_cpow (Or.inl h2π)).differentiableAt
    have hΓ : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s)) s₀ :=
      (Complex.differentiableAt_Gamma (1 - s₀) hw).comp s₀ hsub
    have hζ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (1 - s)) s₀ :=
      (differentiableAt_riemannZeta hw1).comp s₀ hsub
    exact ((differentiableAt_const 2).mul hpow).mul hΓ |>.mul hζ
  have hcos : HasDerivAt (fun s : ℂ => Complex.cos (Real.pi * (1 - s) / 2))
      (-Complex.sin (Real.pi * (1 - s₀) / 2) * (Real.pi * (-1) / 2)) s₀ := by
    have : HasDerivAt (fun s : ℂ => Real.pi * (1 - s) / 2) (Real.pi * (-1) / 2) s₀ := by
      have h := ((hasDerivAt_id s₀).const_sub 1).const_mul (Real.pi : ℂ)
      exact h.div_const 2
    exact this.ccos
  have hprod : HasDerivAt (fun s => F s * Complex.cos (Real.pi * (1 - s) / 2))
      (deriv F s₀ * Complex.cos (Real.pi * (1 - s₀) / 2)
        + F s₀ * (-Complex.sin (Real.pi * (1 - s₀) / 2) * (Real.pi * (-1) / 2))) s₀ :=
    hFd.hasDerivAt.mul hcos
  have hζ' : HasDerivAt riemannZeta
      (deriv F s₀ * Complex.cos (Real.pi * (1 - s₀) / 2)
        + F s₀ * (-Complex.sin (Real.pi * (1 - s₀) / 2) * (Real.pi * (-1) / 2))) s₀ := by
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hfe] with s hs
    rw [hs]
    simp only [hF]
    ring
  have harg : (Real.pi : ℂ) * (1 - s₀) / 2 = Real.pi / 2 + (k : ℂ) * Real.pi := by
    rw [hs₀]; ring
  have hcos0 : Complex.cos (Real.pi * (1 - s₀) / 2) = 0 := by
    rw [harg, Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two,
      Complex.sin_nat_mul_pi]
    ring
  have hcosk : Complex.cos ((k : ℂ) * Real.pi) = (-1) ^ k := by
    have : ((k : ℂ) * (Real.pi : ℂ)) = (((k : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    push_cast
    ring
  have hsin : Complex.sin (Real.pi * (1 - s₀) / 2) = (-1) ^ k := by
    rw [harg, Complex.sin_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two,
      Complex.sin_nat_mul_pi, hcosk]
    ring
  rw [hζ'.deriv, hcos0, hsin, mul_zero, zero_add]
  have hF0 : F s₀ ≠ 0 := by
    rw [hF]
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s₀)) ≠ 0 := by
      intro h
      rw [Complex.cpow_eq_zero_iff] at h
      exact h2π h.1
    have hΓ : Complex.Gamma (1 - s₀) ≠ 0 := Complex.Gamma_ne_zero hw
    have hζ : riemannZeta (1 - s₀) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      have hre : (1 - s₀).re = 1 + 2 * (k : ℝ) := by simp [hs₀]
      rw [hre]
      linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hζ
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpm : ((-1 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have : -(-1 : ℂ) ^ k * ((Real.pi : ℂ) * (-1) / 2) ≠ 0 := by
    have : -(-1 : ℂ) ^ k * ((Real.pi : ℂ) * (-1) / 2) = (-1) ^ k * Real.pi / 2 := by ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hpm hπ) two_ne_zero
  exact mul_ne_zero hF0 this

/-- **`zetaReg` vanishes at the trivial zeros `-2(k+1)`.**

### Summary of Proof
`zetaReg_eq_of_ne` and Mathlib's `riemannZeta_neg_two_mul_nat_add_one`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`.
**Used by:** `logDerivZetaG_bddAbove_near_trivial_zero`. -/
theorem zetaReg_trivial_zero (k : ℕ) : zetaReg (-2 * ((k : ℂ) + 1)) = 0 := by
  have hne : (-2 * ((k : ℂ) + 1)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [zetaReg_eq_of_ne hne, riemannZeta_neg_two_mul_nat_add_one, mul_zero]

/-- **`zetaReg` has a simple zero at each trivial zero: `zetaReg'(-2(k+1)) ≠ 0`.**

### Summary of Proof
Near `s₀ = -2(k+1) ≠ 1`, `zetaReg s = (s-1)ζ(s)`, so `zetaReg'(s₀) = ζ(s₀) + (s₀-1)ζ'(s₀)
= (s₀-1)ζ'(s₀) ≠ 0` by `deriv_riemannZeta_trivial_zero_ne_zero`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`, `deriv_riemannZeta_trivial_zero_ne_zero`.
**Used by:** `logDerivZetaG_bddAbove_near_trivial_zero`. -/
theorem deriv_zetaReg_trivial_zero_ne_zero (k : ℕ) :
    deriv zetaReg (-2 * ((k : ℂ) + 1)) ≠ 0 := by
  set s₀ : ℂ := -2 * ((k : ℂ) + 1) with hs₀
  have hne : s₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hs₀] at this
    have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hev : zetaReg =ᶠ[𝓝 s₀] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hne] with s hs
    exact zetaReg_eq_of_ne hs
  have hζd : HasDerivAt riemannZeta (deriv riemannZeta s₀) s₀ :=
    (differentiableAt_riemannZeta hne).hasDerivAt
  have hprod : HasDerivAt (fun s => (s - 1) * riemannZeta s)
      (1 * riemannZeta s₀ + (s₀ - 1) * deriv riemannZeta s₀) s₀ :=
    ((hasDerivAt_id s₀).sub_const 1).mul hζd
  have hd := hprod.congr_of_eventuallyEq hev
  rw [hd.deriv]
  have hζ0 : riemannZeta s₀ = 0 := by
    rw [hs₀]; exact riemannZeta_neg_two_mul_nat_add_one k
  have hk1 : deriv riemannZeta s₀ ≠ 0 := by
    have := deriv_riemannZeta_trivial_zero_ne_zero (k + 1) (by omega)
    push_cast at this
    rw [hs₀]
    exact this
  rw [hζ0, mul_zero, zero_add]
  exact mul_ne_zero (sub_ne_zero.mpr hne) hk1

/-- **The open neighbourhood `-6.5 < Re s < 8.5`, `|Im s| < 7.5` of the closed box** (in
`s`-coordinates) on which `G` is analysed.

### Summary of Proof
A definition. It contains `1 + closure logDerivZetaBox = [-6,8] × [-7,7]`, and its only zeros of
`ζ` are the trivial zeros `-2, -4, -6` (`zetaReg_ne_zero_of_mem_logDerivZetaGextW`).

### References
tex: the disc `|z| ≤ 7` of `Lemma \ref{lemma:logderzetabound}` (Lemma 38).

### Dependencies
**Depends on:** none.
**Used by:** `zetaReg_ne_zero_of_mem_logDerivZetaGextW`,
`differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`,
`logDerivZetaGext_differentiableOn_ball`, `logDerivZetaGext_differentiableAt_of_mem_W`,
`logDerivZetaGext_diffContOnCl`. -/
def logDerivZetaGextW : Set ℂ := {s : ℂ | -6.5 < s.re ∧ s.re < 8.5 ∧ |s.im| < 7.5}

/-- **On `logDerivZetaGextW` away from `-2, -4, -6`, `zetaReg` does not vanish.**

### Summary of Proof
By `zetaReg_ne_zero_iff` it is about `ζ`. `Re s ≤ 0`: `riemannZeta_eq_zero_of_re_nonpos` puts a
zero at `-2(n+1)`, and `Re s > -6.5` forces `n < 3`. `0 < Re s < 1`:
`riemannZeta_lowest_zero_height` needs `|Im s| > 14`. `Re s ≥ 1`:
`riemannZeta_ne_zero_of_one_le_re`.

### References
The same three regimes as `zetaReg_ne_zero_on_box`.

### Dependencies
**Depends on:** `logDerivZetaGextW`, `zetaReg_ne_zero_iff`, `riemannZeta_eq_zero_of_re_nonpos`,
`riemannZeta_lowest_zero_height`.
**Used by:** `differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`. -/
theorem zetaReg_ne_zero_of_mem_logDerivZetaGextW {s : ℂ} (hs : s ∈ logDerivZetaGextW)
    (hs' : s ∉ ({-2, -4, -6} : Set ℂ)) : zetaReg s ≠ 0 := by
  rw [zetaReg_ne_zero_iff]
  obtain ⟨hre1, hre2, him⟩ := hs
  intro hζ
  rcases le_or_gt s.re 0 with hre0 | hre0
  · obtain ⟨n, hn⟩ := riemannZeta_eq_zero_of_re_nonpos hre0 hζ
    have hnre : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
    have hn3 : n < 3 := by
      by_contra h
      push Not at h
      have : (3 : ℝ) ≤ n := by exact_mod_cast h
      linarith
    apply hs'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    interval_cases n
    · left; rw [hn]; norm_num
    · right; left; rw [hn]; norm_num
    · right; right; rw [hn]; norm_num
  · rcases lt_or_ge s.re 1 with hre1' | hre1'
    · have := riemannZeta_lowest_zero_height hζ hre0 hre1'
      linarith [abs_lt.mp him]
    · exact riemannZeta_ne_zero_of_one_le_re hre1' hζ

/-- **`G` is differentiable at every point of `logDerivZetaGextW` other than `-2, -4, -6`.**

### Summary of Proof
`zetaReg` is entire (`differentiable_zetaReg`), so `deriv zetaReg` is too
(`AnalyticAt.deriv`), the quotient is differentiable where `zetaReg ≠ 0`
(`zetaReg_ne_zero_of_mem_logDerivZetaGextW`), and the three patch terms are differentiable away
from their poles.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaG`, `logDerivZetaGextW`, `zetaReg_ne_zero_of_mem_logDerivZetaGextW`,
`differentiable_zetaReg`.
**Used by:** `logDerivZetaGext_differentiableOn_ball`,
`logDerivZetaGext_differentiableAt_of_mem_W`. -/
theorem differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW {s : ℂ}
    (hs : s ∈ logDerivZetaGextW) (hs' : s ∉ ({-2, -4, -6} : Set ℂ)) :
    DifferentiableAt ℂ logDerivZetaG s := by
  have hz := zetaReg_ne_zero_of_mem_logDerivZetaGextW hs hs'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs'
  have h2 : s + 2 ≠ 0 := by intro h; apply hs'.1; linear_combination h
  have h4 : s + 4 ≠ 0 := by intro h; apply hs'.2.1; linear_combination h
  have h6 : s + 6 ≠ 0 := by intro h; apply hs'.2.2; linear_combination h
  unfold logDerivZetaG
  have hd : DifferentiableAt ℂ (deriv zetaReg) s :=
    ((differentiable_zetaReg.analyticAt s).deriv).differentiableAt
  refine (((hd.div (differentiable_zetaReg s) hz).neg.add ?_).add ?_).add ?_
  · exact (differentiableAt_const _).div (differentiableAt_id.add_const 2) h2
  · exact (differentiableAt_const _).div (differentiableAt_id.add_const 4) h4
  · exact (differentiableAt_const _).div (differentiableAt_id.add_const 6) h6

/-- **Near the trivial zero `p = -2(k+1)` (`k < 3`), `G` is bounded on a punctured ball**: the
patch term `1/(s-p)` cancels the simple pole of `zetaReg'/zetaReg`.

### Summary of Proof
`zetaReg` is analytic with `zetaReg(p) = 0 ≠ zetaReg'(p)` (`deriv_zetaReg_trivial_zero_ne_zero`),
so `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` gives `zetaReg = (s-p)^n g` with
`g(p) ≠ 0`, and `n = 1` (`n = 0` contradicts `zetaReg(p) = 0`, `n ≥ 2` gives `zetaReg'(p) = 0`).
Then on a punctured neighbourhood `zetaReg'/zetaReg = 1/(s-p) + g'/g`, so
`G = -g'/g + (1/(s+2) + 1/(s+4) + 1/(s+6) - 1/(s-p)) =: H`, and `H` is continuous at `p`: the
bracket is the sum of the *other two* patch terms once `p` is one of `-2, -4, -6`
(`interval_cases k`). Continuity gives the bound `‖H p‖ + 1` on a small ball.

### References
No tex counterpart (the tex takes the removable singularities for granted).

### Dependencies
**Depends on:** `logDerivZetaG`, `zetaReg_trivial_zero`, `deriv_zetaReg_trivial_zero_ne_zero`,
`differentiable_zetaReg`.
**Used by:** `logDerivZetaGext_differentiableOn_ball`. -/
theorem logDerivZetaG_bddAbove_near_trivial_zero (k : ℕ) (hk : k < 3) :
    ∃ δ > 0, BddAbove ((fun s => ‖logDerivZetaG s‖) ''
      (Metric.ball (-2 * ((k : ℂ) + 1)) δ \ {-2 * ((k : ℂ) + 1)})) := by
  set p : ℂ := -2 * ((k : ℂ) + 1) with hp
  have han : AnalyticAt ℂ zetaReg p := differentiable_zetaReg.analyticAt p
  have hd0 : deriv zetaReg p ≠ 0 := deriv_zetaReg_trivial_zero_ne_zero k
  have hz0 : zetaReg p = 0 := zetaReg_trivial_zero k
  have hnev : ¬ ∀ᶠ s in 𝓝 p, zetaReg s = 0 := by
    intro h
    have h' : zetaReg =ᶠ[𝓝 p] fun _ => (0 : ℂ) := h
    have := h'.deriv_eq
    rw [deriv_const] at this
    exact hd0 this
  obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnev
  have hn1 : n = 1 := by
    rcases Nat.lt_trichotomy n 1 with h | h | h
    · exfalso
      have h0 : n = 0 := by omega
      rw [h0] at hev
      have hev0 : zetaReg =ᶠ[𝓝 p] fun z => (z - p) ^ 0 • g z := hev
      have := hev0.eq_of_nhds
      simp only [sub_self, pow_zero, smul_eq_mul, one_mul] at this
      exact hg0 (this ▸ hz0)
    · exact h
    · exfalso
      have hgd : DifferentiableAt ℂ g p := hg.differentiableAt
      have hpowd : HasDerivAt (fun s : ℂ => (s - p) ^ n) ((n : ℂ) * (p - p) ^ (n - 1) * 1) p :=
        ((hasDerivAt_id p).sub_const p).pow n
      have hprod := hpowd.smul hgd.hasDerivAt
      have := (hprod.congr_of_eventuallyEq hev).deriv
      apply hd0
      rw [this, sub_self, zero_pow (by omega), zero_pow (by omega)]
      simp
  subst hn1
  have hgne : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hgan : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hderiv : ∀ᶠ s in 𝓝 p, deriv zetaReg s = g s + (s - p) * deriv g s := by
    have hev1 : zetaReg =ᶠ[𝓝 p] fun z => (z - p) ^ 1 • g z := hev
    have hev' : deriv zetaReg =ᶠ[𝓝 p] deriv (fun s => (s - p) ^ 1 • g s) := hev1.deriv
    filter_upwards [hev', hgan] with s hs hgs
    rw [hs]
    have hpow1 : HasDerivAt (fun s : ℂ => (s - p) ^ 1) ((1 : ℕ) * (s - p) ^ (1 - 1) * 1) s :=
      ((hasDerivAt_id s).sub_const p).pow 1
    have this : HasDerivAt (fun s : ℂ => (s - p) ^ 1 • g s)
        ((s - p) ^ 1 • deriv g s + ((1 : ℕ) * (s - p) ^ (1 - 1) * 1) • g s) s :=
      hpow1.smul hgs.differentiableAt.hasDerivAt
    rw [this.deriv]
    simp only [smul_eq_mul, pow_one, Nat.sub_self, pow_zero, mul_one, Nat.cast_one, one_mul]
    ring
  set H : ℂ → ℂ := fun s => -(deriv g s / g s)
    + (1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6) - 1 / (s - p)) with hH
  have hHeq : ∀ᶠ s in 𝓝[≠] p, logDerivZetaG s = H s := by
    have h1 : ∀ᶠ s in 𝓝[≠] p, zetaReg s = (s - p) ^ 1 • g s := nhdsWithin_le_nhds hev
    have h2 : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := nhdsWithin_le_nhds hgne
    have h3 : ∀ᶠ s in 𝓝[≠] p, deriv zetaReg s = g s + (s - p) * deriv g s :=
      nhdsWithin_le_nhds hderiv
    filter_upwards [h1, h2, h3, self_mem_nhdsWithin] with s hs1 hs2 hs3 hs4
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr hs4
    unfold logDerivZetaG
    rw [hs1, hs3, hH]
    simp only [pow_one, smul_eq_mul]
    field_simp
    ring
  have hHcont : ContinuousAt H p := by
    have hA : ContinuousAt (fun s => -(deriv g s / g s)) p :=
      ((hg.deriv.continuousAt).div hg.continuousAt hg0).neg
    have hB : ContinuousAt
        (fun s : ℂ => 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6) - 1 / (s - p)) p := by
      interval_cases k
      · have hfun : (fun s : ℂ => 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6) - 1 / (s - p))
            = fun s : ℂ => 1 / (s + 4) + 1 / (s + 6) := by
          funext s; rw [hp]; push_cast; ring
        rw [hfun]
        refine ContinuousAt.add ?_ ?_
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
      · have hfun : (fun s : ℂ => 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6) - 1 / (s - p))
            = fun s : ℂ => 1 / (s + 2) + 1 / (s + 6) := by
          funext s; rw [hp]; push_cast; ring
        rw [hfun]
        refine ContinuousAt.add ?_ ?_
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
      · have hfun : (fun s : ℂ => 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6) - 1 / (s - p))
            = fun s : ℂ => 1 / (s + 2) + 1 / (s + 4) := by
          funext s; rw [hp]; push_cast; ring
        rw [hfun]
        refine ContinuousAt.add ?_ ?_
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
        · exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (by rw [hp]; norm_num)
    exact hA.add hB
  obtain ⟨δ₁, hδ₁, hH1⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  have hHeq' : ∀ᶠ s in 𝓝 p, s ≠ p → logDerivZetaG s = H s := by
    rwa [eventually_nhdsWithin_iff] at hHeq
  obtain ⟨δ₂, hδ₂, hH2⟩ := Metric.eventually_nhds_iff.mp hHeq'
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ‖H p‖ + 1, ?_⟩
  rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
  have hs1' : dist s p < δ₁ := lt_of_lt_of_le hs1 (min_le_left _ _)
  have hs2' : dist s p < δ₂ := lt_of_lt_of_le hs1 (min_le_right _ _)
  have hsp : s ≠ p := hs2
  simp only
  rw [hH2 hs2' hsp]
  have := hH1 hs1'
  rw [dist_eq_norm] at this
  calc ‖H s‖ = ‖H p + (H s - H p)‖ := by ring_nf
    _ ≤ ‖H p‖ + ‖H s - H p‖ := norm_add_le _ _
    _ ≤ ‖H p‖ + 1 := by linarith

/-- **The holomorphic extension of `G` across its removable singularities at `s ∈ {-2,-4,-6}`**:
`logDerivZetaG` with its values at the three points replaced by the limits
`limUnder (𝓝[≠] p) logDerivZetaG`.

### Summary of Proof
A definition (three `Function.update`s). Its two usable properties are the theorems
`logDerivZetaGext_eq` (agreement with `G` off the three points, by `Function.update_of_ne`) and
`logDerivZetaGext_diffContOnCl` (holomorphic on the box and continuous on its closure, via
Mathlib's removable-singularity theorem and `logDerivZetaG_bddAbove_near_trivial_zero`).

### Lean Notes
The tex simply writes `G` as analytic on `|z| ≤ 7` without dwelling on the removable
singularities.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), where `G` is asserted analytic
on `|z| ≤ 7`.

### Dependencies
**Depends on:** `logDerivZetaG`.
**Used by:** `_flat_ctor`, `casesOn`, `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff`,
`logDerivZetaCoeff_bound`, `logDerivZetaCoeff_one`, `logDerivZetaCoeff_taylor_coeff_real`,
`logDerivZetaCoeff_zero`, and 12 further call sites. -/
noncomputable def logDerivZetaGext : ℂ → ℂ :=
  Function.update (Function.update (Function.update logDerivZetaG (-2)
    (limUnder (𝓝[≠] (-2)) logDerivZetaG)) (-4) (limUnder (𝓝[≠] (-4)) logDerivZetaG))
    (-6) (limUnder (𝓝[≠] (-6)) logDerivZetaG)

/-- **The one certified numerical fact about `-ζ'/ζ` near `s = 1`, as a hypothesis class.**

The Cauchy estimate behind `Lemma \ref{lemma:logderzetabound}` (Lemma 38) needs a bound for the
patched `G(s) = -ζ'(s)/ζ(s) - 1/(s-1) + 1/(s+2) + 1/(s+4) + 1/(s+6)` on the boundary of the box
`[-7,7]²` in `z = s-1` coordinates.  That bound is a finite numerical fact: `mpmath` evaluation
over the square boundary (`Code/indep_mpmath_lemma37.py`, 1604 mesh points plus local refinement)
gives a maximum of `0.59002` at the corners, against the `0.6` claimed — a margin of about
`10^{-2}`.

It cannot be a Lean proof term today: there is no ball-arithmetic evaluation of `ζ'` (arb has
none), so the evidence is high-precision floating point rather than a certificate.  That is
weaker than the `NumericCertificates` fields, which are arb-certified, and it is the reason this
one is separated out rather than merged with them — that, and the fact that its statement needs
`logDerivZetaBox` and `logDerivZetaGext`, which are defined in this file.

### Summary of Proof
A class; no proof.

### Lean Notes
The field is stated for `logDerivZetaGext`, the patched extension, because the frontier point
`z = -7` (`s = -6`) is one of the three removable singularities: `logDerivZetaG` is undefined
there, and the numerical check reaches that point through the same limit.

### References
`Code/indep_mpmath_lemma37.py`; `Assumptions.txt` Part 1.

### Dependencies
**Depends on:** `logDerivZetaBox`, `logDerivZetaGext`.
**Used by:** `logDerivZetaG_boundary_bound`. -/
class LaurentCertificate : Prop where
  /-- `‖G(1+z)‖ ≤ 0.6` on the boundary of the box `[-7,7]²`, where
  `G(s) = -ζ'(s)/ζ(s) - 1/(s-1) + 1/(s+2) + 1/(s+4) + 1/(s+6)` is the patched logarithmic
  derivative.  Verified by `Code/indep_mpmath_lemma37.py`; observed maximum `0.59002`. -/
  logDerivZetaG_boundary_bound :
    ∀ z ∈ frontier logDerivZetaBox, ‖logDerivZetaGext (1 + z)‖ ≤ 0.6

variable [LaurentCertificate]

/-- **The extension agrees with `G` away from the three patched points.**

### Summary of Proof
`Function.update_of_ne`, three times.

### Lean Notes
Every result about `G` on the box is proved for `logDerivZetaGext` and transported back to
`logDerivZetaG` through this equation, at the points where the latter is meaningful.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), which writes `G` as analytic on `|z| ≤ 7`
without dwelling on the removable singularities.

### Dependencies
**Depends on:** `logDerivZetaG`, `logDerivZetaGext`.
**Used by:** `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff_one`,
`logDerivZetaCoeff_taylor_coeff_real`, `logDerivZetaCoeff_zero`,
`logDerivZetaGext_differentiableOn_ball`, `logDerivZetaGext_differentiableAt_of_mem_W`. -/
theorem logDerivZetaGext_eq {s : ℂ} (hs : s ∉ ({-2, -4, -6} : Set ℂ)) :
    logDerivZetaGext s = logDerivZetaG s := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  unfold logDerivZetaGext
  rw [Function.update_of_ne hs.2.2, Function.update_of_ne hs.2.1, Function.update_of_ne hs.1]

/-- **`logDerivZetaGext` is differentiable on a ball around each of `-2, -4, -6`.**

### Summary of Proof
Mathlib's removable-singularity theorem `Complex.differentiableOn_update_limUnder_of_bddAbove` on
the ball of radius `min δ (1/2)` (with `δ` from `logDerivZetaG_bddAbove_near_trivial_zero`):
off the centre `p` the ball lies in `logDerivZetaGextW` and avoids the other two trivial zeros, so
`G` is differentiable there (`differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`) and
bounded. On the ball the triple update `logDerivZetaGext` coincides with the single update at `p`
(the other two centres are at distance `≥ 2`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaGext`, `logDerivZetaGext_eq`, `logDerivZetaGextW`,
`logDerivZetaG_bddAbove_near_trivial_zero`,
`differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`.
**Used by:** `logDerivZetaGext_differentiableAt_of_mem_W`. -/
theorem logDerivZetaGext_differentiableOn_ball (k : ℕ) (hk : k < 3) :
    ∃ δ > 0, DifferentiableOn ℂ logDerivZetaGext (Metric.ball (-2 * ((k : ℂ) + 1)) δ) := by
  obtain ⟨δ, hδ, hbdd⟩ := logDerivZetaG_bddAbove_near_trivial_zero k hk
  set p : ℂ := -2 * ((k : ℂ) + 1) with hp
  have hk' : (k : ℝ) < 3 := by exact_mod_cast hk
  have hpre : p.re = -2 * ((k : ℝ) + 1) := by simp [hp]
  have hpim : p.im = 0 := by simp [hp]
  set δ' := min δ (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hmem : ∀ s ∈ Metric.ball p δ' \ {p},
      s ∈ logDerivZetaGextW ∧ s ∉ ({-2, -4, -6} : Set ℂ) := by
    rintro s ⟨hs, hsp⟩
    have hsp' : s ≠ p := hsp
    have hd : dist s p < 1 / 2 := lt_of_lt_of_le hs (min_le_right _ _)
    have hd' : ‖s - p‖ < 1 / 2 := by rwa [dist_eq_norm] at hd
    have hre : |s.re - p.re| < 1 / 2 := by
      have := Complex.abs_re_le_norm (s - p)
      rw [Complex.sub_re] at this
      linarith
    have him : |s.im - p.im| < 1 / 2 := by
      have := Complex.abs_im_le_norm (s - p)
      rw [Complex.sub_im] at this
      linarith
    rw [hpre] at hre
    rw [hpim, sub_zero] at him
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linarith [abs_lt.mp hre]
    · linarith [abs_lt.mp hre]
    · exact lt_trans him (by norm_num)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      have hre' := abs_lt.mp hre
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        interval_cases k
        · exact hsp' (by rw [hp]; push_cast; rw [h]; ring)
        · linarith
        · linarith
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        interval_cases k
        · linarith
        · exact hsp' (by rw [hp]; push_cast; rw [h]; ring)
        · linarith
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        interval_cases k
        · linarith
        · linarith
        · exact hsp' (by rw [hp]; push_cast; rw [h]; ring)
  have hd : DifferentiableOn ℂ logDerivZetaG (Metric.ball p δ' \ {p}) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hmem s hs
    exact (differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW h1 h2).differentiableWithinAt
  have hb : BddAbove (norm ∘ logDerivZetaG '' (Metric.ball p δ' \ {p})) := by
    refine hbdd.mono (Set.image_mono ?_)
    intro s hs
    exact ⟨Metric.ball_subset_ball (min_le_left _ _) hs.1, hs.2⟩
  have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds p hδ'0) hd hb
  refine ⟨δ', hδ'0, ?_⟩
  apply hdiff.congr
  intro s hs
  by_cases hsp : s = p
  · subst hsp
    rw [Function.update_self]
    unfold logDerivZetaGext
    interval_cases k
    · simp only [hp]
      norm_num
    · simp only [hp]
      norm_num
    · simp only [hp]
      norm_num
  · rw [Function.update_of_ne hsp]
    exact logDerivZetaGext_eq (hmem s ⟨hs, hsp⟩).2

/-- **`logDerivZetaGext` is differentiable at every point of `logDerivZetaGextW`.**

### Summary of Proof
At `-2, -4, -6`: `logDerivZetaGext_differentiableOn_ball`. Elsewhere `logDerivZetaGext = G` on a
neighbourhood (`logDerivZetaGext_eq`, the three points forming a closed set) and `G` is
differentiable (`differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaGext`, `logDerivZetaGext_eq`, `logDerivZetaGextW`,
`logDerivZetaGext_differentiableOn_ball`,
`differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW`.
**Used by:** `logDerivZetaGext_diffContOnCl`. -/
theorem logDerivZetaGext_differentiableAt_of_mem_W {s : ℂ} (hs : s ∈ logDerivZetaGextW) :
    DifferentiableAt ℂ logDerivZetaGext s := by
  by_cases h : s ∈ ({-2, -4, -6} : Set ℂ)
  · have key : ∀ k : ℕ, k < 3 → s = -2 * ((k : ℂ) + 1) →
        DifferentiableAt ℂ logDerivZetaGext s := by
      intro k hk hsk
      obtain ⟨δ, hδ, hdiff⟩ := logDerivZetaGext_differentiableOn_ball k hk
      rw [hsk]
      exact hdiff.differentiableAt (Metric.ball_mem_nhds _ hδ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact key 0 (by norm_num) (by rw [h]; norm_num)
    · exact key 1 (by norm_num) (by rw [h]; norm_num)
    · exact key 2 (by norm_num) (by rw [h]; norm_num)
  · have hcl : IsClosed ({-2, -4, -6} : Set ℂ) := (Set.toFinite _).isClosed
    have hev : logDerivZetaGext =ᶠ[𝓝 s] logDerivZetaG := by
      filter_upwards [hcl.isOpen_compl.mem_nhds h] with t ht
      exact logDerivZetaGext_eq ht
    exact (differentiableAt_logDerivZetaG_of_mem_logDerivZetaGextW hs h).congr_of_eventuallyEq hev

/-- **`G` is holomorphic on the box `V`** (in `z = s-1` coordinates), and continuous on its
closure.

### Summary of Proof
`1 + closure logDerivZetaBox = [-6,8] × [-7,7] ⊆ logDerivZetaGextW` (`Complex.closure_reProdIm`,
`closure_Ioo`), and `logDerivZetaGext` is differentiable at every point of `logDerivZetaGextW`
(`logDerivZetaGext_differentiableAt_of_mem_W`), hence differentiable on the box and continuous on
its closure.

### Lean Notes
`s = -6` (`z = -7`) sits on `logDerivZetaBox`'s *frontier*, not its interior; the extension is
differentiable there too, which is more than the continuity `DiffContOnCl` asks for.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the analyticity of `G` on `|z| ≤ 7`.

### Dependencies
**Depends on:** `logDerivZetaBox`, `logDerivZetaGext`, `logDerivZetaGextW`,
`logDerivZetaGext_differentiableAt_of_mem_W`.
**Used by:** `hasSum_logDerivZetaCoeff`, `logDerivZetaG_bound_on_box`,
`logDerivZetaG_iteratedDeriv_bound`. -/
theorem logDerivZetaGext_diffContOnCl :
    DiffContOnCl ℂ (fun z => logDerivZetaGext (1 + z)) logDerivZetaBox := by
  have hW : ∀ z ∈ closure logDerivZetaBox, (1 + z) ∈ logDerivZetaGextW := by
    intro z hz
    rw [logDerivZetaBox, Complex.closure_reProdIm, closure_Ioo (by norm_num : (-7 : ℝ) ≠ 7),
      Complex.mem_reProdIm] at hz
    obtain ⟨hre, him⟩ := hz
    simp only [logDerivZetaGextW, Set.mem_ofPred_eq, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, zero_add]
    refine ⟨by linarith [hre.1], by linarith [hre.2], ?_⟩
    rw [abs_lt]
    constructor <;> linarith [him.1, him.2]
  refine ⟨?_, ?_⟩
  · intro z hz
    have := logDerivZetaGext_differentiableAt_of_mem_W (hW z (subset_closure hz))
    exact (this.comp z (differentiableAt_id.const_add 1)).differentiableWithinAt
  · intro z hz
    have := logDerivZetaGext_differentiableAt_of_mem_W (hW z hz)
    exact (this.comp z (differentiableAt_id.const_add 1)).continuousAt.continuousWithinAt

/-- **The boundary bound:** `‖G(1+z)‖ ≤ 0.6` for `z` on the frontier of the box `[-7,7]+i[-7,7]`.

### Summary of Proof
Not proved here — the statement reads the hypothesis field
`LaurentCertificate.logDerivZetaG_boundary_bound`. It is the tex's own "We rigorously verify the
bound on the boundary of `|G(z)| < 6/10` for `|z| = 7`" — a numeric verification,
Chirre–Helfgott-style but at `K = 3` and radius `7` rather than their radius. It is the single
numeric input from which claim 1's coefficient bound follows by Cauchy's estimate.
`Code/verify_lemmaA7_bound_radius7.sage` checks a dense mesh of the boundary at 60 digits; the
observed maximum is `≈ 0.590`, near the corners `z = -7±7i` (`s = -6±7i`), comfortably under
`0.6`. The point `z = -7` (`s = -6`) itself, on the frontier where the third patch sits, is
covered via `logDerivZetaGext`'s patched value — checked as a numerical limit approaching along
the boundary from both directions, converging to `≈ 0.578`.

### Lean Notes
Stated for `logDerivZetaGext`, the patched extension, not the raw `logDerivZetaG`, which is
undefined at `z = -7`.

The evidence is high-precision floating point, not ball arithmetic: Sage's `ComplexBallField`
exposes no `zeta'`, so the derivative in `ζ'/ζ` cannot be enclosed rigorously in that framework.
That is why this bound is the field of `LaurentCertificate` rather than one of the arb-certified
`NumericCertificates` — see that class's own docstring.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the sentence "We rigorously
verify the bound on the boundary of `|G(z)| < 6/10` for `|z| = 7`".
External: Chirre–Helfgott `\cite[Lemma A.7]{ChirreHelfgott2025}`, attributed there to A. Kalmynin
`\cite{Kalmynin2025}`.

**Independent numeric check.**
`Code/indep_mpmath_lemma37.py` block [A] (mpmath, 30 digits, written from the definition of
`logDerivZetaG`): on the **square** boundary — which is what `logDerivZetaBox` is, the tex's
"`|z| = 7`" notwithstanding — `max ‖G(1+z)‖ = 0.59002` at the corners `z = -7 ± 7i`
(1604 mesh points plus local refinement); on the circle `|z| = 7` the maximum is `0.57822` at
`z = -7`, the removable point, evaluated through its limit. Both are under `0.6`; the square is
the stronger statement and the one the Cauchy estimate needs.

### Dependencies
**Depends on:** `logDerivZetaBox`, `logDerivZetaGext`,
`LaurentCertificate.logDerivZetaG_boundary_bound`.
**Used by:** `logDerivZetaG_bound_on_box`. -/
theorem logDerivZetaG_boundary_bound :
    ∀ z ∈ frontier logDerivZetaBox, ‖logDerivZetaGext (1 + z)‖ ≤ 0.6 :=
  LaurentCertificate.logDerivZetaG_boundary_bound

/-! ## The reduction: maximum modulus + Cauchy's estimate -/

/-- **`G` is bounded by `0.6` on the whole closed box `V`,** not just its boundary.

### Summary of Proof
The maximum modulus principle. Mathlib's
`Complex.norm_le_of_forall_mem_frontier_norm_le` applied to
`logDerivZetaGext_diffContOnCl` (holomorphic inside, continuous on the closure) and
`logDerivZetaG_boundary_bound` (the bound on the frontier), with boundedness of the box supplied
by `Metric.isBounded_Ioo` on each factor.

### References
tex: implicit in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38) — the tex bounds the
Taylor coefficients "by the Cauchy integral formula", which needs the bound on the whole region,
not only the boundary.

### Dependencies
**Depends on:** `logDerivZetaBox`, `logDerivZetaG_boundary_bound`, `logDerivZetaGext`,
`logDerivZetaGext_diffContOnCl`.
**Used by:** `logDerivZetaG_iteratedDeriv_bound`. -/
theorem logDerivZetaG_bound_on_box {z : ℂ} (hz : z ∈ closure logDerivZetaBox) :
    ‖logDerivZetaGext (1 + z)‖ ≤ 0.6 :=
  Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo (-7:ℝ) 7).reProdIm (Metric.isBounded_Ioo (-7:ℝ) 7))
    logDerivZetaGext_diffContOnCl logDerivZetaG_boundary_bound hz

/-- **The open disc of radius `7` sits inside the open box `V`.**

### Summary of Proof
For `‖z‖ < 7`, both `|z.re| ≤ ‖z‖ < 7` and `|z.im| ≤ ‖z‖ < 7`, via `Complex.abs_re_le_norm` and
`Complex.abs_im_le_norm`.

### Lean Notes
No tex counterpart: the tex works on the disc `|z| ≤ 7` throughout, while the Lean development
uses the box for the maximum-modulus step (whose frontier is easier to enumerate) and the disc
for the Cauchy estimate. These two inclusion lemmas are the bridge.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaBox`.
**Used by:** `hasSum_logDerivZetaCoeff`, `logDerivZetaG_iteratedDeriv_bound`,
`logDerivZetaG_shift_differentiableAt`. -/
theorem ball7_subset_box {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 7) : z ∈ logDerivZetaBox := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
  rw [logDerivZetaBox, mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
  exact ⟨abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm z) hz),
    abs_lt.mp (lt_of_le_of_lt (Complex.abs_im_le_norm z) hz)⟩

/-- **The closed disc of radius `7` sits inside the closure of the box `V`.**

### Summary of Proof
As `ball7_subset_box`, but with non-strict inequalities, using `closure_reProdIm` and
`closure_Ioo` to identify the closure of the box as the product of closed intervals.

### References
No tex counterpart. See `ball7_subset_box`.

### Dependencies
**Depends on:** `logDerivZetaBox`.
**Used by:** `logDerivZetaG_iteratedDeriv_bound`. -/
theorem closedBall7_subset_closure_box {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 7) :
    z ∈ closure logDerivZetaBox := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
  rw [logDerivZetaBox, closure_reProdIm, closure_Ioo (by norm_num : (-7:ℝ) ≠ 7), mem_reProdIm]
  exact ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans hz),
    abs_le.mp ((Complex.abs_im_le_norm z).trans hz)⟩

/-! ### Realness of `G`'s Taylor coefficients at `0`

Everything below is self-contained, using only `zetaReg_ne_zero_on_box` and the Schwarz-reflection
facts above; it does not need `logDerivZetaGext`'s construction beyond `logDerivZetaGext_eq` at the
very last step (bridging to the actual definition used in `logDerivZetaCoeff`). -/

/-- **Schwarz reflection propagates to derivatives.** If `g` is complex-differentiable on a
conjugation-symmetric open set `D` and satisfies `g(conj z) = conj(g z)` there, then `deriv g`
satisfies the same functional equation.

### Summary of Proof
Apply `hasDerivAt_conj_comp_conj` to `g`, use the hypothesis to identify
`fun w => conj (g (conj w))` with `g` on a neighbourhood — which needs `D` open and
conjugation-symmetric — and conclude by uniqueness of the derivative.

### Lean Notes
The same pattern `deriv_zetaReg_conj` uses for `zetaReg` specifically, generalised so it can be
applied repeatedly, once per order, to `logDerivZetaG`'s iterated derivatives below.

### References
No tex counterpart. The tex asserts realness of the Taylor coefficients without comment.

### Dependencies
**Depends on:** `hasDerivAt_conj_comp_conj`.
**Used by:** `logDerivZetaG_shift_iteratedDeriv_conj_symm`. -/
theorem deriv_conj_of_conj_symm {g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hDsymm : ∀ z ∈ D, conj z ∈ D) (hdiff : ∀ z ∈ D, DifferentiableAt ℂ g z)
    (hsymm : ∀ z ∈ D, g (conj z) = conj (g z)) {s : ℂ} (hs : s ∈ D) :
    deriv g (conj s) = conj (deriv g s) := by
  have h1 : HasDerivAt g (deriv g s) s := (hdiff s hs).hasDerivAt
  have h2 := hasDerivAt_conj_comp_conj h1
  have heqfun : g =ᶠ[𝓝 (conj s)] (fun w => conj (g (conj w))) := by
    have hDs : D ∈ 𝓝 (conj s) := hD.mem_nhds (hDsymm s hs)
    filter_upwards [hDs] with w hw
    have hgw := hsymm w hw
    have hc := congrArg conj hgw
    rw [Complex.conj_conj] at hc
    exact hc.symm
  have h2' : HasDerivAt g (conj (deriv g s)) (conj s) := h2.congr_of_eventuallyEq heqfun
  have h3 : HasDerivAt g (deriv g (conj s)) (conj s) := (hdiff (conj s) (hDsymm s hs)).hasDerivAt
  exact h3.unique h2'

/-- **`fun z => G(1+z)` is complex-differentiable on the open unit ball.**

### Summary of Proof
Three ingredients, combined by `fun_prop`.

* The denominator `zetaReg (1+z)` is nonzero there: `ball 0 1 ⊆ logDerivZetaBox` and the ball
  avoids `-3` and `-5`, so `zetaReg_ne_zero_on_box` applies.
* `deriv zetaReg` is differentiable everywhere, since `zetaReg` is entire and hence so is its
  derivative (`Differentiable.deriv`).
* The three patch-term denominators `1+z+2`, `1+z+4`, `1+z+6` are nonzero for `‖z‖ < 1`, each
  having real part `≥ 2`.

### References
No tex counterpart as a named result — implicit in the tex's assertion that `G` is analytic.

### Dependencies
**Depends on:** `ball7_subset_box`, `differentiable_zetaReg`, `logDerivZetaBox`, `logDerivZetaG`,
`zetaReg`, `zetaReg_ne_zero_on_box`.
**Used by:** `logDerivZetaG_shift_iteratedDeriv_conj_symm`. -/
theorem logDerivZetaG_shift_differentiableAt {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    DifferentiableAt ℂ (fun w => logDerivZetaG (1 + w)) z := by
  have hzbox : z ∈ logDerivZetaBox := ball7_subset_box (Metric.ball_subset_ball (by norm_num) hz)
  have hne35 : z ≠ -3 ∧ z ≠ -5 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    constructor <;> intro hc <;> rw [hc] at hz <;> norm_num at hz
  have hzne : zetaReg (1 + z) ≠ 0 := zetaReg_ne_zero_on_box ⟨hzbox, by simp [hne35.1, hne35.2]⟩
  have hzre : |z.re| < 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
  have hzre1 : -1 < z.re := (abs_lt.mp hzre).1
  have hne2 : (1 : ℂ) + z + 2 ≠ 0 := by
    intro hc
    have hre : (1 + z + 2 : ℂ).re = 0 := by rw [hc]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    norm_num at hre; linarith
  have hne4 : (1 : ℂ) + z + 4 ≠ 0 := by
    intro hc
    have hre : (1 + z + 4 : ℂ).re = 0 := by rw [hc]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    norm_num at hre; linarith
  have hne6 : (1 : ℂ) + z + 6 ≠ 0 := by
    intro hc
    have hre : (1 + z + 6 : ℂ).re = 0 := by rw [hc]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    norm_num at hre; linarith
  unfold logDerivZetaG
  have hderiv_diff : DifferentiableAt ℂ (fun w : ℂ => deriv zetaReg (1 + w)) z :=
    (differentiable_zetaReg.deriv.differentiableAt).comp z (by fun_prop)
  have hreg_diff : DifferentiableAt ℂ (fun w : ℂ => zetaReg (1 + w)) z :=
    (differentiable_zetaReg.differentiableAt).comp z (by fun_prop)
  fun_prop (disch := first | exact hzne | exact hne2 | exact hne4 | exact hne6)

/-- **Every iterated derivative of `G(1+z)` is analytic on `ball 0 1` and satisfies Schwarz
reflection there.**

### Summary of Proof
Induction on `n`, carrying analyticity and the symmetry together so that each can feed the other's
successor step.

* Base case: analyticity is `logDerivZetaG_shift_differentiableAt` promoted through
  `DifferentiableOn.analyticOnNhd`; symmetry is `logDerivZetaG_conj`, using
  `conj (1+z) = 1 + conj z`.
* Step: `AnalyticOnNhd.deriv` propagates analyticity to the derivative, and
  `deriv_conj_of_conj_symm` propagates the symmetry — the latter needing analyticity at the
  previous order, which is why the two are proved simultaneously. Both are transported through
  `iteratedDeriv_succ`.

### References
No tex counterpart. The tex asserts realness of the Taylor coefficients without comment in the
proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38); this is the induction Lean needs.

### Dependencies
**Depends on:** `deriv_conj_of_conj_symm`, `logDerivZetaG`, `logDerivZetaG_conj`,
`logDerivZetaG_shift_differentiableAt`.
**Used by:** `logDerivZetaCoeff_taylor_coeff_real`. -/
theorem logDerivZetaG_shift_iteratedDeriv_conj_symm (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n (fun z => logDerivZetaG (1 + z))) (Metric.ball (0 : ℂ) 1)
      ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1,
          iteratedDeriv n (fun z => logDerivZetaG (1 + z)) (conj z)
            = conj (iteratedDeriv n (fun z => logDerivZetaG (1 + z)) z) := by
  induction n with
  | zero =>
    refine ⟨DifferentiableOn.analyticOnNhd
      (fun z hz => (logDerivZetaG_shift_differentiableAt hz).differentiableWithinAt)
      Metric.isOpen_ball, fun z _ => ?_⟩
    simp only [iteratedDeriv_zero]
    have : (1 : ℂ) + conj z = conj (1 + z) := by simp [map_add]
    rw [this, logDerivZetaG_conj]
  | succ n ih =>
    obtain ⟨ihA, ihS⟩ := ih
    have hAsucc : AnalyticOnNhd ℂ (iteratedDeriv (n + 1) (fun z => logDerivZetaG (1 + z)))
        (Metric.ball (0 : ℂ) 1) := by
      rw [iteratedDeriv_succ]
      exact ihA.deriv
    refine ⟨hAsucc, fun z hz => ?_⟩
    rw [iteratedDeriv_succ]
    exact deriv_conj_of_conj_symm Metric.isOpen_ball
      (fun w hw => by simpa [Metric.mem_ball, dist_eq_norm] using hw)
      (fun w hw => (ihA w hw).differentiableAt) ihS hz

/-- **The Taylor coefficients of `G(1+z)` at `z = 0` are real, at every order.**

### Summary of Proof
Two steps.

* `iteratedDeriv n (fun z => logDerivZetaG (1+z)) 0` is fixed by conjugation, from
  `logDerivZetaG_shift_iteratedDeriv_conj_symm` evaluated at `z = 0` (noting `conj 0 = 0`), hence
  real by `Complex.conj_eq_iff_im`.
* That value coincides with the `logDerivZetaGext` version actually used in
  `logDerivZetaCoeff`'s definition, because the two functions agree on the whole ball `‖z‖ < 1`
  (`logDerivZetaGext_eq`, since `1+z ∉ {-2,-4,-6}` there), hence so do all their iterated
  derivatives at any point of that ball (`Filter.EventuallyEq.iteratedDeriv`).

### Lean Notes
The whole content is Schwarz reflection for `ζ`, which Mathlib supplies as `riemannZeta_conj`.

### References
tex: implicit in `Lemma \ref{lemma:logderzetabound}` (Lemma 38), whose statement writes the `a_n`
as real numbers without justifying it.

### Dependencies
**Depends on:** `logDerivZetaG`, `logDerivZetaG_shift_iteratedDeriv_conj_symm`,
`logDerivZetaGext`, `logDerivZetaGext_eq`.
**Used by:** `hasSum_logDerivZetaCoeff`, which needs it to take real parts termwise; it also
records the realness that `logDerivZetaCoeff`'s use of `Complex.re` silently relies on. -/
theorem logDerivZetaCoeff_taylor_coeff_real (n : ℕ) :
    (iteratedDeriv n (fun z : ℂ => logDerivZetaGext (1 + z)) 0).im = 0 := by
  have hbridge : (fun z : ℂ => logDerivZetaGext (1 + z))
      =ᶠ[𝓝 (0 : ℂ)] (fun z => logDerivZetaG (1 + z)) := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    have hne : (1 : ℂ) + z ∉ ({-2, -4, -6} : Set ℂ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
      · have hz' : z = -3 := by linear_combination hc
        rw [hz'] at hz; norm_num at hz
      · have hz' : z = -5 := by linear_combination hc
        rw [hz'] at hz; norm_num at hz
      · have hz' : z = -7 := by linear_combination hc
        rw [hz'] at hz; norm_num at hz
    exact logDerivZetaGext_eq hne
  rw [(hbridge.iteratedDeriv n).self_of_nhds]
  have hsymm := (logDerivZetaG_shift_iteratedDeriv_conj_symm n).2 0 (Metric.mem_ball_self one_pos)
  simp only [map_zero] at hsymm
  have : (iteratedDeriv n (fun z => logDerivZetaG (1 + z)) 0)
      = conj (iteratedDeriv n (fun z => logDerivZetaG (1 + z)) 0) := hsymm
  exact Complex.conj_eq_iff_im.mp this.symm

/-- **Cauchy's estimate for `G(1+z)`'s Taylor coefficients at `z = 0`:**
`‖G^{(n)}(1)‖ ≤ n!·0.6/7ⁿ`.

### Summary of Proof
This is the tex's "We bound the Taylor coefficients of `G(z)`, which is analytic on `|z| ≤ 7`, by
the Cauchy integral formula". In Lean it is
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` applied on the disc of radius `7`,
with the sphere bound `‖G‖ ≤ 0.6` supplied by `logDerivZetaG_bound_on_box` (via
`closedBall7_subset_closure_box`) and the regularity by `logDerivZetaGext_diffContOnCl` restricted
along `ball7_subset_box`.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the Cauchy-integral step.

### Dependencies
**Depends on:** `ball7_subset_box`, `closedBall7_subset_closure_box`,
`logDerivZetaG_bound_on_box`, `logDerivZetaGext`, `logDerivZetaGext_diffContOnCl`.
**Used by:** `logDerivZetaCoeff_bound`. -/
theorem logDerivZetaG_iteratedDeriv_bound (n : ℕ) :
    ‖iteratedDeriv n (fun z => logDerivZetaGext (1 + z)) 0‖ ≤ n.factorial * 0.6 / 7 ^ n := by
  have hdcc : DiffContOnCl ℂ (fun z => logDerivZetaGext (1 + z)) (Metric.ball (0 : ℂ) 7) :=
    logDerivZetaGext_diffContOnCl.mono (fun z hz => ball7_subset_box hz)
  have hC : ∀ z ∈ Metric.sphere (0 : ℂ) 7, ‖logDerivZetaGext (1 + z)‖ ≤ 0.6 := by
    intro z hz
    have : z ∈ Metric.closedBall (0 : ℂ) 7 := Metric.sphere_subset_closedBall hz
    exact logDerivZetaG_bound_on_box (closedBall7_subset_closure_box this)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hdcc hC

/-! ## The coefficient bound (Lemma 38, claim 1) -/

/-- **The Laurent coefficients `a_n`** of `-ζ'/ζ(1+z) = 1/z + Σ (-1)^{n+1} a_n z^n`.

### Summary of Proof
A definition. `a_n` is assembled from the real part of `G`'s own Taylor coefficient at `z = 0`,
shifted by the explicit `3^{-n-1}+5^{-n-1}+7^{-n-1}` piece coming from `G`'s three patch terms
`1/(z+3)+1/(z+5)+1/(z+7)` — each contributing `1/(z+c) = Σ(-1)ⁿ zⁿ/c^{n+1}` for `|z| < c`. See
`logDerivZetaCoeff_bound`'s proof for the exact algebraic relation.

### Lean Notes
Taking `.re` is legitimate because the Taylor coefficients really are real; that is
`logDerivZetaCoeff_taylor_coeff_real`. The tex writes the `a_n` as reals without comment.

### References
tex: the `a_n` of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), defined by the displayed Laurent
series.

### Dependencies
**Depends on:** `logDerivZetaGext`.
**Used by:** `abs_logDerivZetaCoeff_le`, `hasSum_logDerivZetaCoeff`,
`hasSum_logDerivZetaCoeff_integrated`, `logDerivZetaCoeff_antitone`, `logDerivZetaCoeff_bound`,
`logDerivZetaCoeff_div_succ_antitone`, `logDerivZetaCoeff_div_succ_lt`,
`logDerivZetaCoeff_mul_pow_succ_le`, `logDerivZetaCoeff_mul_pow_succ_le_all`,
`logDerivZetaCoeff_mul_pow_succ_lt`, `logDerivZetaCoeff_one`, `logDerivZetaCoeff_one_bounds`,
`logDerivZetaCoeff_pos`, `logDerivZetaCoeff_pos_all`, `logDerivZetaCoeff_two_mul_succ_le`,
`logDerivZetaCoeff_two_mul_succ_le_all`, `logDerivZetaCoeff_two_mul_succ_lt`,
`logDerivZetaCoeff_zero`, `logderzetabound`, `logderzetabound_claim_two`,
`logderzetabound_claim_three`, `neg_logDeriv_zeta_bound_of_claim_two`,
`neg_logDeriv_zeta_lt_one_div`. -/
noncomputable def logDerivZetaCoeff (n : ℕ) : ℝ :=
  (-1:ℝ) ^ (n + 1) * (iteratedDeriv n (fun z : ℂ => logDerivZetaGext (1 + z)) 0).re / n.factorial
    + (3:ℝ) ^ (-(n:ℝ) - 1) + (5:ℝ) ^ (-(n:ℝ) - 1) + (7:ℝ) ^ (-(n:ℝ) - 1)

/-- **`Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 1.** For `n ≥ 1`,
`a_n = 3^{-n-1}+5^{-n-1}+7^{-n-1} + O^*(0.6·7^{-n})`.

### Summary of Proof
The tex follows Chirre–Helfgott's Lemma A.7, but at radius `7` with the singularities at
`1, -2, -4, -6` removed. Bound `G`'s Taylor coefficients by the Cauchy integral formula, using the
verified boundary bound `|G| < 6/10` on `|z| = 7`; rearranging then gives the result, since
`a_n` differs from `G`'s coefficient exactly by the explicit patch contributions
`3^{-n-1}+5^{-n-1}+7^{-n-1}`.

### Lean Notes
The chain is `logDerivZetaG_boundary_bound` (the one numeric input) → maximum modulus
(`logDerivZetaG_bound_on_box`) → Cauchy's estimate (`logDerivZetaG_iteratedDeriv_bound`) → here.
Unfolding `logDerivZetaCoeff` cancels the patch terms, leaving `|(-1)^{n+1}·G^{(n)}(1).re| / n!`,
bounded via `Complex.abs_re_le_norm`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 1.
External: Chirre–Helfgott `\cite[Lemma A.7]{ChirreHelfgott2025}`, attributed there to A. Kalmynin
`\cite{Kalmynin2025}`.

**Independent numeric check.**
`Code/indep_mpmath_lemma37.py` block [B] computes the Taylor coefficients of `G(1+z)` at `0`
by a 512-point Cauchy integral on `|z| = 3` (40 digits) and finds
`|a_n - (3^{-n-1}+5^{-n-1}+7^{-n-1})| / (0.6·7^{-n}) ≤ 0.305` for `1 ≤ n ≤ 60` (maximum at
`n = 2`), decaying like `(3/7)^n`; so the bound is comfortable in the constant and sharp only in the
exponent. Block [E] confirms `a_n > 0` and `a_n 2^n` decreasing from `n = 2`.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaG_iteratedDeriv_bound`, `logDerivZetaGext`.
**Used by:** `abs_logDerivZetaCoeff_le`, `logDerivZetaCoeff_pos`,
`logDerivZetaCoeff_two_mul_succ_le`, `logDerivZetaCoeff_two_mul_succ_le_all`,
`logDerivZetaCoeff_two_mul_succ_lt`, `logderzetabound`. -/
theorem logDerivZetaCoeff_bound {n : ℕ} (_hn : 1 ≤ n) :
    |logDerivZetaCoeff n - ((3:ℝ) ^ (-(n:ℝ) - 1) + (5:ℝ) ^ (-(n:ℝ) - 1) + (7:ℝ) ^ (-(n:ℝ) - 1))|
      ≤ 0.6 * 7 ^ (-(n:ℝ)) := by
  have hsub : logDerivZetaCoeff n
      - ((3:ℝ) ^ (-(n:ℝ) - 1) + (5:ℝ) ^ (-(n:ℝ) - 1) + (7:ℝ) ^ (-(n:ℝ) - 1))
      = (-1:ℝ) ^ (n + 1) * (iteratedDeriv n (fun z : ℂ => logDerivZetaGext (1 + z)) 0).re
          / n.factorial := by
    unfold logDerivZetaCoeff; ring
  rw [hsub, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hnfac : (0:ℝ) < n.factorial := by positivity
  rw [abs_of_pos hnfac]
  have h1 : |(iteratedDeriv n (fun z : ℂ => logDerivZetaGext (1 + z)) 0).re|
      ≤ n.factorial * 0.6 / 7 ^ n :=
    (Complex.abs_re_le_norm _).trans (logDerivZetaG_iteratedDeriv_bound n)
  have h2 : n.factorial * 0.6 / (7:ℝ) ^ n / n.factorial = 0.6 / 7 ^ n := by
    field_simp
  have h3 : (0.6:ℝ) / 7 ^ n = 0.6 * 7 ^ (-(n:ℝ)) := by
    have heq : (7:ℝ) ^ (-(n:ℝ)) = 1 / (7:ℝ) ^ n := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; ring
    rw [heq, mul_one_div]
  calc |(iteratedDeriv n (fun z : ℂ => logDerivZetaGext (1 + z)) 0).re| / n.factorial
      ≤ (n.factorial * 0.6 / 7 ^ n) / n.factorial := by gcongr
    _ = 0.6 / 7 ^ n := h2
    _ = 0.6 * 7 ^ (-(n:ℝ)) := h3

/-! ### Positivity and monotonicity of the coefficients

Both facts below are consequences of `logDerivZetaCoeff_bound` **alone** — no new numeric input.
The numeric picture (checked here to 40 digits by an independent mpmath contour-integral
computation of the true `a_n`, `n ≤ 15`, on `|z|=1`): `a_0 = γ = 0.5772…` to 40 digits,
`a_1 = 0.18754…`, `a_2 = 0.051688…`, and `a_n·2^n` is genuinely antitone for **all** `n ≥ 0`.
The *crude* bound, however, only certifies the antitone step from `n ≥ 2` onwards — see
`logDerivZetaCoeff_two_mul_succ_le`'s docstring for exactly where and why `n = 1` escapes it. -/

/-- **`c^(-n-1) = (c^(n+1))⁻¹`** for `c > 0`.

### Summary of Proof
Rewrite `-(n:ℝ)-1` as `-((n:ℝ)+1)`, apply `Real.rpow_neg`, then convert the remaining real
exponent to a natural one with `Real.rpow_natCast`.

### Lean Notes
No tex counterpart — pure arithmetic plumbing. It converts the `rpow` form used in
`logDerivZetaCoeff` into an `npow` form that `positivity`, `gcongr` and `linarith` can work with;
those tactics handle natural powers far better than real ones.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff_one`,
`logDerivZetaCoeff_two_mul_succ_le`, `logDerivZetaCoeff_two_mul_succ_lt`,
`logDerivZetaCoeff_zero`, `logDerivZeta_err_lt_main`. -/
theorem rpow_neg_natCast_sub_one {c : ℝ} (hc : 0 < c) (n : ℕ) :
    c ^ (-(n:ℝ) - 1) = (c ^ (n + 1))⁻¹ := by
  rw [show -(n:ℝ) - 1 = -((n:ℝ) + 1) by ring, Real.rpow_neg hc.le]
  congr 1
  rw [show ((n:ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- **`c^(-n) = (c^n)⁻¹`** for `c > 0`; companion to `rpow_neg_natCast_sub_one`.

### Summary of Proof
`Real.rpow_neg` followed by `Real.rpow_natCast`.

### References
No tex counterpart — arithmetic plumbing.

### Dependencies
**Depends on:** none.
**Used by:** `logDerivZetaCoeff_two_mul_succ_le`, `logDerivZetaCoeff_two_mul_succ_lt`,
`logDerivZeta_err_lt_main`. -/
theorem rpow_neg_natCast {c : ℝ} (hc : 0 < c) (n : ℕ) : c ^ (-(n:ℝ)) = (c ^ n)⁻¹ := by
  rw [Real.rpow_neg hc.le, Real.rpow_natCast]

/-- **The error term never swamps the main term:**
`0.6·7^{-n} < 3^{-n-1}+5^{-n-1}+7^{-n-1}` for every `n`.

### Summary of Proof
Bounding `3^{-n}, 5^{-n} ≥ 7^{-n}` collapses the right-hand side to
`≥ (1/3+1/5+1/7)·7^{-n} = 0.67619…·7^{-n}`, comfortably above `0.6·7^{-n}`.

### Lean Notes
No tex counterpart as a named claim, but it is the whole reason the tex's radius-`7`, `K = 3`
construction is used: this is the margin it buys. A `K = 1`, radius-`4` construction gives only
`|a_n - 3^{-n-1}| ≤ 1.4·4^{-n}`, which fails this inequality at small `n`, leaving the positivity
and monotonicity of the `a_n` out of reach.

### References
tex: implicit in `Lemma \ref{lemma:logderzetabound}` (Lemma 38), whose proof asserts that "the
only negative term decreases at least as quickly as the positive terms".

### Dependencies
**Depends on:** `rpow_neg_natCast`, `rpow_neg_natCast_sub_one`.
**Used by:** `logDerivZetaCoeff_pos`. -/
theorem logDerivZeta_err_lt_main (n : ℕ) :
    (0.6:ℝ) * 7 ^ (-(n:ℝ))
      < (3:ℝ) ^ (-(n:ℝ) - 1) + (5:ℝ) ^ (-(n:ℝ) - 1) + (7:ℝ) ^ (-(n:ℝ) - 1) := by
  rw [rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7),
      rpow_neg_natCast (by norm_num : (0:ℝ) < 7)]
  have hp3 : (3:ℝ) ^ n ≤ 7 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hp5 : (5:ℝ) ^ n ≤ 7 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h7 : (0:ℝ) < 7 ^ n := by positivity
  have h3 : (3:ℝ) ^ (n + 1) ≤ 3 * 7 ^ n := by rw [pow_succ]; nlinarith
  have h5 : (5:ℝ) ^ (n + 1) ≤ 5 * 7 ^ n := by rw [pow_succ]; nlinarith
  have i3 : (3 * (7:ℝ) ^ n)⁻¹ ≤ ((3:ℝ) ^ (n + 1))⁻¹ := by
    have hpos : (0:ℝ) < (3:ℝ) ^ (n + 1) := by positivity
    gcongr
  have i5 : (5 * (7:ℝ) ^ n)⁻¹ ≤ ((5:ℝ) ^ (n + 1))⁻¹ := by
    have hpos : (0:ℝ) < (5:ℝ) ^ (n + 1) := by positivity
    gcongr
  have e3 : (3 * (7:ℝ) ^ n)⁻¹ = (1 / 3) * ((7:ℝ) ^ n)⁻¹ := by field_simp
  have e5 : (5 * (7:ℝ) ^ n)⁻¹ = (1 / 5) * ((7:ℝ) ^ n)⁻¹ := by field_simp
  have e7 : ((7:ℝ) ^ (n + 1))⁻¹ = (1 / 7) * ((7:ℝ) ^ n)⁻¹ := by rw [pow_succ]; field_simp
  rw [e3] at i3
  rw [e5] at i5
  rw [e7]
  have hinv : (0:ℝ) < ((7:ℝ) ^ n)⁻¹ := by positivity
  linarith

/-- **The coefficients are positive:** `a_n > 0` for every `n ≥ 1`.

### Summary of Proof
This is the tex's "the sequence is positive". Immediate from claim 1's two-sided bound
(`logDerivZetaCoeff_bound`) together with `logDerivZeta_err_lt_main`: the error `0.6·7^{-n}` is
strictly smaller than the main term `3^{-n-1}+5^{-n-1}+7^{-n-1}`, so `a_n` cannot reach `0`.

### Lean Notes
Numerically `a_1 = 0.1875…`, decreasing to `0` like `3^{-n-1}`. `a_0 = γ` is positive too, but is
not covered here, since `logDerivZetaCoeff_bound` only speaks for `n ≥ 1`; it is handled
separately and exactly by `logDerivZetaCoeff_zero`.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2 — "We see that the
sequence is positive by noting that `a_0` is positive and that the only negative term decreases at
least as quickly as the positive terms".

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `logDerivZeta_err_lt_main`.
**Used by:** `logDerivZetaCoeff_mul_pow_succ_le`, `logDerivZetaCoeff_mul_pow_succ_le_all`,
`logDerivZetaCoeff_mul_pow_succ_lt`, `logDerivZetaCoeff_pos_all`,
`neg_logDeriv_zeta_lt_one_div`. -/
theorem logDerivZetaCoeff_pos {n : ℕ} (hn : 1 ≤ n) : 0 < logDerivZetaCoeff n := by
  have hb := abs_le.mp (logDerivZetaCoeff_bound hn)
  have hkey := logDerivZeta_err_lt_main n
  linarith [hb.1]

/-- **The crude antitone step:** `2·a_{n+1} ≤ a_n` for `n ≥ 2`.

### Summary of Proof
This is the tex's "The same idea applied to `d/dn (a_n 2^n)` gives that the `a_n 2^n` are a
decreasing sequence for `n ≥ 2`". It is the `x = 2` (hardest) endpoint of the monotonicity
`a_{n+1}·x^{n+1} ≤ a_n·x^n` that claim 2's alternating-series argument needs on `x ∈ [0,2]`.

Writing `S_n := 3^{-n-1}+5^{-n-1}+7^{-n-1}`, claim 1 gives `2a_{n+1} ≤ 2(S_{n+1}+0.6·7^{-n-1})`
and `a_n ≥ S_n - 0.6·7^{-n}`. So it suffices that
`2(S_{n+1}+0.6·7^{-n-1}) ≤ S_n - 0.6·7^{-n}`, i.e. after dividing by `7^{-n-1}`, that
`(1/3)(7/3)^{n+1} + (3/5)(7/5)^{n+1} + 5/7 ≥ 5.4`.

### Lean Notes
**Why `n ≥ 2` and not `n ≥ 1`.** At `n = 2` the left side above is `6.59…` and grows with `n`; at
`n = 1` it is only `3.70…`. So the crude bound genuinely fails at `n = 1`, and the `n = 0, 1`
steps of the antitone chain are *not* consequences of `logDerivZetaCoeff_bound` alone. This is
exactly the "one can check the first few terms through direct computations" that the tex's proof
appeals to.

Both steps are nonetheless true — an independent 40-digit computation gives `a_0 = γ = 0.57721…`,
`2a_1 = 0.37509…`, `4a_2 = 0.20675…`, so `a_0 ≥ 2a_1 ≥ 4a_2` with room. They are closed
separately: `n = 0 → 1` by the exact identity `logDerivZetaCoeff_zero`, and `n = 1 → 2` by
`logDerivZetaCoeff_one_bounds`.

After reducing the `rpow`s to `npow`s, the argument is `linarith` over `3^m, 5^m, 7^m` given
`3^m ≤ 7^m` and `5^m ≤ 7^m`.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `rpow_neg_natCast`,
`rpow_neg_natCast_sub_one`.
**Used by:** `logDerivZetaCoeff_mul_pow_succ_le`, `logDerivZetaCoeff_two_mul_succ_le_all`. -/
theorem logDerivZetaCoeff_two_mul_succ_le {n : ℕ} (hn : 2 ≤ n) :
    2 * logDerivZetaCoeff (n + 1) ≤ logDerivZetaCoeff n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hu := abs_le.mp (logDerivZetaCoeff_bound (n := m + 3) (by omega))
  have hl := abs_le.mp (logDerivZetaCoeff_bound (n := m + 2) (by omega))
  have hup : logDerivZetaCoeff (m + 2 + 1)
      ≤ ((3:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1) + (5:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1)
          + (7:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1)) + 0.6 * 7 ^ (-((m + 3 : ℕ) : ℝ)) := by
    have : m + 2 + 1 = m + 3 := by omega
    rw [this]; linarith [hu.2]
  have hlo : ((3:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1) + (5:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1)
        + (7:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1)) - 0.6 * 7 ^ (-((m + 2 : ℕ) : ℝ))
      ≤ logDerivZetaCoeff (m + 2) := by linarith [hl.1]
  rw [rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7),
      rpow_neg_natCast (by norm_num : (0:ℝ) < 7)] at hup hlo
  norm_num at hup hlo
  -- now purely `npow`: reduce to `3^m ≤ 7^m`, `5^m ≤ 7^m` and linear arithmetic
  have h3m : (0:ℝ) < 3 ^ m := by positivity
  have h5m : (0:ℝ) < 5 ^ m := by positivity
  have h7m : (0:ℝ) < 7 ^ m := by positivity
  have hp3 : (3:ℝ) ^ m ≤ 7 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have hp5 : (5:ℝ) ^ m ≤ 7 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have e34 : ((3:ℝ) ^ (m + 4))⁻¹ = (1 / 81) * ((3:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e33 : ((3:ℝ) ^ (m + 3))⁻¹ = (1 / 27) * ((3:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e54 : ((5:ℝ) ^ (m + 4))⁻¹ = (1 / 625) * ((5:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e53 : ((5:ℝ) ^ (m + 3))⁻¹ = (1 / 125) * ((5:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e74 : ((7:ℝ) ^ (m + 4))⁻¹ = (1 / 2401) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e73 : ((7:ℝ) ^ (m + 3))⁻¹ = (1 / 343) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e72 : ((7:ℝ) ^ (m + 2))⁻¹ = (1 / 49) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have i3 : ((7:ℝ) ^ m)⁻¹ ≤ ((3:ℝ) ^ m)⁻¹ := by gcongr
  have i5 : ((7:ℝ) ^ m)⁻¹ ≤ ((5:ℝ) ^ m)⁻¹ := by gcongr
  have hw : (0:ℝ) < ((7:ℝ) ^ m)⁻¹ := by positivity
  rw [e34, e54, e74, e73] at hup
  rw [e33, e53, e73, e72] at hlo
  linarith

/-- **The monotonicity claim 2 needs,** `a_{n+1}·x^{n+1} ≤ a_n·x^n` for `0 ≤ x ≤ 2`, `n ≥ 2`.

### Summary of Proof
The `x = 2` endpoint (`logDerivZetaCoeff_two_mul_succ_le`) is the hardest case, so it implies the
rest: `a_{n+1}·x ≤ a_{n+1}·2 ≤ a_n` for `x ≤ 2`, using `logDerivZetaCoeff_pos` to know
`a_{n+1} > 0` so that scaling by `x` preserves the direction. Multiplying through by `x^n ≥ 0`
gives the claim.

### References
tex: the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2 — the decreasing-terms
hypothesis of the alternating-series argument.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_pos`,
`logDerivZetaCoeff_two_mul_succ_le`.
**Used by:** none — superseded by `logDerivZetaCoeff_mul_pow_succ_le_all`, which covers every `n`.
Kept as the `n ≥ 2` statement that follows from claim 1 alone, with no numeric input. -/
theorem logDerivZetaCoeff_mul_pow_succ_le {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) {n : ℕ}
    (hn : 2 ≤ n) :
    logDerivZetaCoeff (n + 1) * x ^ (n + 1) ≤ logDerivZetaCoeff n * x ^ n := by
  have hpos : 0 < logDerivZetaCoeff (n + 1) := logDerivZetaCoeff_pos (by omega)
  have hstep : logDerivZetaCoeff (n + 1) * x ≤ logDerivZetaCoeff n := by
    nlinarith [logDerivZetaCoeff_two_mul_succ_le hn]
  have hxn : (0:ℝ) ≤ x ^ n := by positivity
  calc logDerivZetaCoeff (n + 1) * x ^ (n + 1)
      = (logDerivZetaCoeff (n + 1) * x) * x ^ n := by rw [pow_succ]; ring
    _ ≤ logDerivZetaCoeff n * x ^ n := by exact mul_le_mul_of_nonneg_right hstep hxn

/-! ### The patch terms' geometric series

`logDerivZetaCoeff` is defined as `G`'s own Taylor coefficient *plus* the explicit tail
`3^{-n-1}+5^{-n-1}+7^{-n-1}`. That explicit tail is exactly the Taylor series of `G`'s three patch
terms `1/(z+3)+1/(z+5)+1/(z+7)`, which is what these two lemmas supply; `hasSum_logDerivZetaCoeff`
combines them with `Complex.hasSum_taylorSeries_on_ball` for `G(1+·)`. -/

/-- **Geometric series for a shifted reciprocal:** `1/(z+c) = Σ_{n≥0} (-1)ⁿ zⁿ/c^{n+1}` for
`‖z‖ < c`, `c > 0` real.

### Summary of Proof
Write `1/(z+c) = (1/c)·(1 - (-z/c))⁻¹` and apply `hasSum_geometric_of_norm_lt_one`, which needs
`‖-z/c‖ < 1`, i.e. `‖z‖ < c`. Matching the general term against `(-1)ⁿ zⁿ/c^{n+1}` is `field_simp`
plus `ring`.

### References
No tex counterpart as a named result — the tex uses this expansion implicitly when it says the
patch terms contribute `3^{-n-1}+5^{-n-1}+7^{-n-1}` to `a_n`.

### Dependencies
**Depends on:** none.
**Used by:** `hasSum_patch_series`. -/
theorem hasSum_one_div_add {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : ‖z‖ < c) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * z ^ n / (c : ℂ) ^ (n + 1)) (1 / (z + c)) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hr : ‖(-z / (c : ℂ))‖ < 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_lt_one hc]; exact hz
  have hg := hasSum_geometric_of_norm_lt_one hr
  have hmul := hg.mul_left (1 / (c : ℂ))
  have hval : (1 / (c : ℂ)) * (1 - -z / (c : ℂ))⁻¹ = 1 / (z + c) := by
    field_simp; ring
  rw [hval] at hmul
  refine hmul.congr_fun fun n => ?_
  rw [div_pow, neg_pow, pow_succ]
  field_simp
  ring

/-- **The three patch terms of `G` as a single power series:** for `‖z‖ < 3`,
`1/(z+3)+1/(z+5)+1/(z+7) = Σ_{n≥0} (-1)ⁿ (3^{-n-1}+5^{-n-1}+7^{-n-1}) zⁿ`.

### Summary of Proof
Three applications of `hasSum_one_div_add`, at `c = 3, 5, 7`, added together. The radius is
governed by the smallest shift, hence `‖z‖ < 3`.

### Lean Notes
The right-hand side is exactly the explicit tail appearing in `logDerivZetaCoeff`'s definition.
Subtracting this series from `Complex.hasSum_taylorSeries_on_ball` for `G(1+·)` is what identifies
`a_n` as the true Laurent coefficients — step two of `hasSum_logDerivZetaCoeff`.

### References
tex: implicit in `Lemma \ref{lemma:logderzetabound}` (Lemma 38), where the patch terms'
contribution to `a_n` is read off without comment.

### Dependencies
**Depends on:** `hasSum_one_div_add`.
**Used by:** `hasSum_logDerivZetaCoeff` (the patch-series input to its proof). -/
theorem hasSum_patch_series {z : ℂ} (hz : ‖z‖ < 3) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * z ^ n *
        (((3:ℂ) ^ (n + 1))⁻¹ + ((5:ℂ) ^ (n + 1))⁻¹ + ((7:ℂ) ^ (n + 1))⁻¹))
      (1 / (z + 3) + 1 / (z + 5) + 1 / (z + 7)) := by
  have h3 := hasSum_one_div_add (c := 3) (by norm_num) (by exact_mod_cast hz)
  have h5 := hasSum_one_div_add (c := 5) (by norm_num) (show ‖z‖ < (5:ℝ) by linarith)
  have h7 := hasSum_one_div_add (c := 7) (by norm_num) (show ‖z‖ < (7:ℝ) by linarith)
  have hsum := (h3.add h5).add h7
  have hcast : ((3:ℝ):ℂ) = 3 := by norm_num
  have hcast5 : ((5:ℝ):ℂ) = 5 := by norm_num
  have hcast7 : ((7:ℝ):ℂ) = 7 := by norm_num
  rw [hcast, hcast5, hcast7] at hsum
  refine hsum.congr_fun fun n => ?_
  field_simp

/-! ### `a_0 = γ`, and the small-`n` antitone steps

`logDerivZetaCoeff_bound` (claim 1) says nothing at `n = 0`, and at `n = 1` it is too crude to
decide the antitone step (see `logDerivZetaCoeff_two_mul_succ_le`'s docstring). This section closes
both remaining steps:

* `n = 0 → 1` needs **no new numeric input at all**: `a_0 = γ` is an *exact identity*, proved below
  from Mathlib's `tendsto_riemannZeta_sub_one_div` (the constant term of `ζ`'s Laurent expansion
  at `1`), and combined with claim 1's upper bound on `a_1` and Mathlib's
  `Real.one_half_lt_eulerMascheroniConstant` it gives `2a_1 ≤ a_0` outright.
* `n = 1 → 2` genuinely does need one new numeric input, `logDerivZetaCoeff_one_bounds` — see that
  theorem's docstring for why every Cauchy-estimate route provably fails there. -/

/-- **`zetaReg` has derivative `γ` at `s = 1`.**

### Summary of Proof
The difference quotient of `zetaReg` at `1` is literally `ζ(s) - 1/(s-1)` away from `s = 1`, since
`zetaReg 1 = 1` and `zetaReg s = (s-1)ζ(s)`. So the claim is exactly Mathlib's
`tendsto_riemannZeta_sub_one_div` — the statement that `γ` is the constant term of `ζ`'s Laurent
expansion at its pole — after rewriting the slope.

### References
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39) at `n = 0`, which records
`a_0 = γ`.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`, `zetaReg_one`.
**Used by:** `deriv_zetaReg_one`, `logDerivZetaCoeff_one`. -/
theorem hasDerivAt_zetaReg_one :
    HasDerivAt zetaReg (Real.eulerMascheroniConstant : ℂ) 1 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_riemannZeta_sub_one_div.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  rw [slope_def_field, zetaReg_eq_of_ne hz, zetaReg_one]
  field_simp

/-- **`zetaReg'(1) = γ`,** the `deriv` form of `hasDerivAt_zetaReg_one`.

### Summary of Proof
`HasDerivAt.deriv` applied to `hasDerivAt_zetaReg_one`.

### Lean Notes
Restated in `deriv` form because the consumer `logDerivZetaCoeff_zero` needs `deriv zetaReg 1` as
a *value* — it appears inside `G(1+z) = -(deriv zetaReg)/zetaReg + …` evaluated at `z = 0` —
rather than as a differentiability statement.

This is what makes `a₀ = γ` provable outright rather than needing a numerical bound.

### References
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39) at `n = 0`.

### Dependencies
**Depends on:** `hasDerivAt_zetaReg_one`, `zetaReg`.
**Used by:** `logDerivZetaCoeff_one`, `logDerivZetaCoeff_zero`. -/
theorem deriv_zetaReg_one : deriv zetaReg 1 = (Real.eulerMascheroniConstant : ℂ) :=
  hasDerivAt_zetaReg_one.deriv

/-! ### `(riemannZeta₀)'(1) = -γ₁`: the Stieltjes constant is the Laurent coefficient

`Definitions.stieltjesConstant1` *defines* `γ₁` by the limit
`lim_m (Σ_{k≤m} (log k)/k - (log m)²/2)`, which says nothing about `ζ`; the development consumes
`γ₁` as the Laurent coefficient of `-(s-1)` in `ζ(s) = 1/(s-1) + γ - γ₁(s-1) + ⋯`.  The bridge is
`hasDerivAt_riemannZeta₀_one`, proved here from Mathlib's `ZetaAsymptotics` machinery — the same
machinery that proves `ζ(s) - 1/(s-1) → γ`.

For real `s > 1` Mathlib has (`ZetaAsymptotics.zeta_limit_aux1`)

  `ζ(s) - 1/(s-1) = 1 - s · T(s)`,  `T(s) := Σ_{n≥1} term n s`,
  `term n s = ∫_n^{n+1} (x-n)/x^{s+1} dx`,

and `T(1) = 1 - γ` (`term_tsum_one`).  Differentiating each `term n` in `s` under the integral
(`hasDerivAt_zetaTerm`), bounding the derivatives uniformly on `(1/2, 3/2)` by
`log(n+1)/n^{3/2}` (`zetaTermD_norm_le`, summable by `log x ≤ 4x^{1/4}`), and applying Mathlib's
`hasDerivAt_tsum_of_isPreconnected` gives `T'(1) = Σ_n ∂_s term n (1)` (`hasDerivAt_termTSum_one`).
Each derivative has the closed form `-∫_n^{n+1} (x-n) log x/x² dx`, whose partial sums telescope
(`sum_zetaTermD_one`) to `stieltjesSeq (N+1) + H_{N+1} - log(N+1) - 1 → γ₁ + γ - 1`
(`Definitions.tendsto_stieltjesSeq`, `Real.tendsto_harmonic_sub_log`).  So the real function
`s ↦ ζ₀(s) = 1 - s T(s)` has right derivative `-(T(1) + T'(1)) = -γ₁` at `1`; since
`riemannZeta₀` is entire (`differentiable_riemannZeta₀`), the one-sided real derivative is its
complex derivative (`HasDerivAt.comp_ofReal`, `UniqueDiffWithinAt.eq_deriv` on `Ioi 1`).
-/

/-- **The `s`-derivative of the integrand of `ZetaAsymptotics.term`, integrated:**
`zetaTermD n s = -∫_n^{n+1} (x-n) log x / x^{s+1} dx`.

### Summary of Proof
Definition; `hasDerivAt_zetaTerm` shows it is `∂_s term n s`.

### Dependencies
**Depends on:** none.
**Used by:** `hasDerivAt_riemannZeta₀_one`, `hasDerivAt_termTSum_one`, `hasDerivAt_zetaTerm`,
`hasSum_zetaTermD_one`, `sum_zetaTermD_one`, `zetaTermD_norm_le`, `zetaTermD_one_eq`. -/
noncomputable def zetaTermD (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (n : ℝ)..((n : ℝ) + 1), -((x - n) * Real.log x / x ^ (s + 1))

/-- **`∂_σ [(x-n)/x^{σ+1}] = -(x-n) log x / x^{σ+1}`** for `x > 0`.

### Summary of Proof
`Real.hasStrictDerivAt_const_rpow` for `σ ↦ x^{σ+1}`, then the reciprocal rule.

### Dependencies
**Depends on:** none.
**Used by:** `hasDerivAt_zetaTerm`. -/
theorem hasDerivAt_zetaTerm_integrand {n : ℕ} {x : ℝ} (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => (x - n) / x ^ (σ + 1))
      (-((x - n) * Real.log x / x ^ (s + 1))) s := by
  have h1 : HasDerivAt (fun σ : ℝ => x ^ (σ + 1)) (x ^ (s + 1) * Real.log x) s := by
    have := (Real.hasStrictDerivAt_const_rpow hx (s + 1)).hasDerivAt
    have h2 := this.comp s ((hasDerivAt_id s).add_const 1)
    rw [mul_one] at h2
    exact h2
  have hne : x ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 := (h1.inv hne).const_mul (x - n)
  have e : (fun σ : ℝ => (x - n) / x ^ (σ + 1)) = fun σ => (x - n) * (x ^ (σ + 1))⁻¹ := by
    funext σ; rw [div_eq_mul_inv]
  rw [e]
  refine h3.congr_deriv ?_
  field_simp

/-- **`s ↦ term n s` is differentiable for `s > 0`, `n ≥ 1`, with derivative `zetaTermD n s`.**

### Summary of Proof
Differentiation under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on the neighbourhood
`Ioi 0` of `s`: the `σ`-derivative of the integrand is `-(x-n) log x/x^{σ+1}`
(`hasDerivAt_zetaTerm_integrand`), bounded in absolute value by the constant `log(n+1)` on
`x ∈ (n, n+1]`, `σ > 0`; integrability of the integrand itself is Mathlib's
`ZetaAsymptotics.term_welldef`.

### References
Mathlib: `ZetaAsymptotics.term`,
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

### Dependencies
**Depends on:** `zetaTermD`, `hasDerivAt_zetaTerm_integrand`.
**Used by:** `hasDerivAt_termTSum_one`. -/
theorem hasDerivAt_zetaTerm {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => ZetaAsymptotics.term n σ) (zetaTermD n s) s := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (σ : ℝ) (x : ℝ) => (x - n) / x ^ (σ + 1))
    (F' := fun (σ : ℝ) (x : ℝ) => -((x - n) * Real.log x / x ^ (σ + 1)))
    (x₀ := s) (s := Set.Ioi 0) (a := (n : ℝ)) (b := (n : ℝ) + 1) (μ := MeasureTheory.volume)
    (bound := fun _ => Real.log ((n : ℝ) + 1)) (Ioi_mem_nhds hs) ?_
    (ZetaAsymptotics.term_welldef hn hs) ?_ ?_ ?_ ?_
  · exact key.2
  · exact Filter.Eventually.of_forall fun σ =>
      (by fun_prop : Measurable fun x : ℝ => (x - n) / x ^ (σ + 1)).aestronglyMeasurable
  · exact (by fun_prop :
      Measurable fun x : ℝ => -((x - n) * Real.log x / x ^ (s + 1))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x hx σ hσ => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx1 : (1 : ℝ) ≤ x := hn1.trans hx.1.le
    have hxpos : 0 < x := by linarith
    have hlog : Real.log x ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hxpos hx.2
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hpow : 1 ≤ x ^ (σ + 1) := Real.one_le_rpow hx1 (by linarith [Set.mem_Ioi.mp hσ])
    have hxn : x - n ≤ 1 := by linarith [hx.2]
    have hxn0 : 0 ≤ x - n := by linarith [hx.1]
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg hxn0 hlog0) (Real.rpow_nonneg hxpos.le _))]
    calc (x - n) * Real.log x / x ^ (σ + 1) ≤ (x - n) * Real.log x :=
          div_le_self (mul_nonneg hxn0 hlog0) hpow
      _ ≤ 1 * Real.log ((n : ℝ) + 1) := mul_le_mul hxn hlog hlog0 zero_le_one
      _ = Real.log ((n : ℝ) + 1) := one_mul _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun x hx σ _ => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact hasDerivAt_zetaTerm_integrand (by linarith [hx.1, hn1]) σ

/-- **`|zetaTermD n y| ≤ log(n+1)/n^{3/2}` for `y ≥ 1/2`, `n ≥ 1`.**

### Summary of Proof
`intervalIntegral.norm_integral_le_of_norm_le_const` with the pointwise bound
`(x-n) log x / x^{y+1} ≤ log(n+1)/n^{3/2}` on `(n, n+1]` (`x - n ≤ 1`, `log x ≤ log(n+1)`,
`x^{y+1} ≥ x^{3/2} ≥ n^{3/2}`).

### Dependencies
**Depends on:** `zetaTermD`.
**Used by:** `hasDerivAt_termTSum_one`, `hasSum_zetaTermD_one`. -/
theorem zetaTermD_norm_le {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖zetaTermD n y‖ ≤ Real.log ((n : ℝ) + 1) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold zetaTermD
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (C := Real.log ((n : ℝ) + 1) / (n : ℝ) ^ (3 / 2 : ℝ))
    (f := fun x => -((x - n) * Real.log x / x ^ (y + 1))) ?_
  · simpa using h
  · intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx1 : (1 : ℝ) ≤ x := hn1.trans hx.1.le
    have hxpos : (0 : ℝ) < x := by linarith
    have hxn0 : 0 ≤ x - n := by linarith [hx.1]
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg hxn0 hlog0) (Real.rpow_nonneg hxpos.le _))]
    have hlog : Real.log x ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hxpos hx.2
    have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ x ^ (y + 1) := by
      calc (n : ℝ) ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hx.1.le (by norm_num)
        _ ≤ x ^ (y + 1) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hnpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
    calc (x - n) * Real.log x / x ^ (y + 1)
        ≤ (1 * Real.log ((n : ℝ) + 1)) / (n : ℝ) ^ (3 / 2 : ℝ) := by
          apply div_le_div₀ (by rw [one_mul]; exact Real.log_nonneg (by linarith))
            (mul_le_mul (by linarith [hx.2]) hlog hlog0 zero_le_one) hnpos hpow
      _ = _ := by ring

/-- **`Σ_n log(n+2)/(n+1)^{3/2}` converges.**

### Summary of Proof
`log x ≤ 4 x^{1/4}` (`Real.log_le_rpow_div`) and `(n+2)^{1/4} ≤ 2(n+1)^{1/4}` give the majorant
`8 (n+1)^{-5/4}`, summable by `Real.summable_nat_rpow_inv`.

### Dependencies
**Depends on:** none.
**Used by:** `hasDerivAt_termTSum_one`, `hasSum_zetaTermD_one`. -/
theorem summable_zetaTermD_bound :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  have hs' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4))
    refine this.congr fun n => ?_
    push_cast
    rfl
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_nonneg
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) (by positivity)) (fun n => ?_)
    (hs'.mul_left 8)
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : Real.log ((n : ℝ) + 1 + 1) ≤ 4 * ((n : ℝ) + 1 + 1) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (x := (n : ℝ) + 1 + 1) (ε := 1 / 4) (by positivity) (by norm_num)
    rw [div_eq_mul_inv] at this
    norm_num at this
    linarith
  have h2 : ((n : ℝ) + 1 + 1) ^ (1 / 4 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
    calc ((n : ℝ) + 1 + 1) ^ (1 / 4 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
            (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hm.le
      _ ≤ 2 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have h3 : ((n : ℝ) + 1) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
      = (((n : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_sub hm, ← Real.rpow_neg hm.le]
    norm_num
  calc Real.log ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
      ≤ (8 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ)) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        gcongr
        linarith [h1, h2]
    _ = 8 * (((n : ℝ) + 1) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by ring
    _ = 8 * (((n : ℝ) + 1) ^ (5 / 4 : ℝ))⁻¹ := by rw [h3]

/-- **`T = termTSum` is differentiable at `1` with derivative `Σ_n zetaTermD (n+1) 1`.**

### Summary of Proof
Mathlib's `hasDerivAt_tsum_of_isPreconnected` on the open interval `(1/2, 3/2)`: each summand is
differentiable there (`hasDerivAt_zetaTerm`), the derivatives are dominated by the summable
`log(n+2)/(n+1)^{3/2}` (`zetaTermD_norm_le`, `summable_zetaTermD_bound`), and the series converges
at `1` (`term_tsum_one`).

### References
Mathlib: `hasDerivAt_tsum_of_isPreconnected`, `ZetaAsymptotics.termTSum`.

### Dependencies
**Depends on:** `hasDerivAt_zetaTerm`, `zetaTermD_norm_le`, `summable_zetaTermD_bound`.
**Used by:** `hasDerivAt_riemannZeta₀_one`. -/
theorem hasDerivAt_termTSum_one :
    HasDerivAt ZetaAsymptotics.termTSum (∑' n, zetaTermD (n + 1) 1) 1 := by
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => Real.log ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ))
    (t := Set.Ioo (1 / 2 : ℝ) (3 / 2)) (g := fun n s => ZetaAsymptotics.term (n + 1) s)
    (g' := fun n s => zetaTermD (n + 1) s) (y₀ := 1) (y := 1) summable_zetaTermD_bound isOpen_Ioo
    isPreconnected_Ioo ?_ ?_ (by norm_num) ?_ (by norm_num)
  · exact h
  · intro n y hy
    exact hasDerivAt_zetaTerm (Nat.succ_pos n) (by linarith [hy.1])
  · intro n y hy
    have := zetaTermD_norm_le (n := n + 1) (Nat.succ_pos n) (y := y) hy.1.le
    push_cast at this ⊢
    exact this
  · exact ZetaAsymptotics.term_tsum_one.summable

/-- **Closed form of `zetaTermD a 1`:**
`-∫_a^{a+1} (x-a) log x/x² dx = -[(log²(a+1) - log²a)/2 + a(log(a+1)+1)/(a+1) - (log a + 1)]`.

### Summary of Proof
The antiderivative of `(x-a) log x/x²` is `log²x/2 + a(log x + 1)/x`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`).

### Dependencies
**Depends on:** `zetaTermD`.
**Used by:** `sum_zetaTermD_one`. -/
theorem zetaTermD_one_eq {a : ℕ} (ha : 0 < a) :
    zetaTermD a 1 = -((Real.log ((a : ℝ) + 1) ^ 2 / 2 - Real.log (a : ℝ) ^ 2 / 2)
      + (a : ℝ) * (Real.log ((a : ℝ) + 1) + 1) / ((a : ℝ) + 1) - (Real.log (a : ℝ) + 1)) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  unfold zetaTermD
  have hderiv : ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + 1),
      HasDerivAt (fun x => -(Real.log x ^ 2 / 2 + (a : ℝ) * (Real.log x + 1) / x))
        (-((x - a) * Real.log x / x ^ ((1 : ℝ) + 1))) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 : HasDerivAt (fun x => Real.log x ^ 2 / 2) (Real.log x / x) x := by
      have := ((Real.hasDerivAt_log hx0.ne').pow 2).div_const 2
      refine this.congr_deriv ?_
      field_simp
      norm_num
    have h2 : HasDerivAt (fun x => (a : ℝ) * (Real.log x + 1) / x)
        (-(a : ℝ) * Real.log x / x ^ 2) x := by
      have := (((Real.hasDerivAt_log hx0.ne').add_const 1).const_mul (a : ℝ)).div
        (hasDerivAt_id x) hx0.ne'
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    have h3 := (h1.add h2).neg
    have hfun : (fun x => -(Real.log x ^ 2 / 2 + (a : ℝ) * (Real.log x + 1) / x))
        = -((fun x => Real.log x ^ 2 / 2) + fun x => (a : ℝ) * (Real.log x + 1) / x) := by
      funext y; simp [Pi.add_apply, Pi.neg_apply]
    rw [hfun]
    refine h3.congr_deriv ?_
    rw [show ((1 : ℝ) + 1) = 2 by norm_num, Real.rpow_two]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
  · field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hc : ContinuousAt (fun x : ℝ => x ^ ((1 : ℝ) + 1)) x :=
      continuousAt_id.rpow_const (Or.inl hx0.ne')
    exact (((continuousAt_id.sub continuousAt_const).mul (Real.continuousAt_log hx0.ne')).div hc
      (Real.rpow_pos_of_pos hx0 _).ne').neg

/-- **Partial sums of the derivative series telescope:**
`Σ_{n<N} zetaTermD (n+1) 1 = stieltjesSeq (N+1) + H_{N+1} - log(N+1) - 1`.

### Summary of Proof
Induction on `N`, with `zetaTermD_one_eq`, `Definitions.stieltjesSeq_succ_sub` and
`harmonic_succ`; the step is a rational identity in `N`, `log(N+1)`, `log(N+2)`.

### Dependencies
**Depends on:** `zetaTermD_one_eq`, `Definitions.stieltjesSeq_succ_sub`.
**Used by:** `hasSum_zetaTermD_one`. -/
theorem sum_zetaTermD_one (N : ℕ) :
    ∑ n ∈ Finset.range N, zetaTermD (n + 1) 1
      = stieltjesSeq (N + 1) + (harmonic (N + 1) : ℝ) - Real.log ((N : ℝ) + 1) - 1 := by
  induction N with
  | zero => simp [stieltjesSeq, harmonic, Finset.sum_range_succ]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, zetaTermD_one_eq (Nat.succ_pos N)]
    have hs := stieltjesSeq_succ_sub (N + 1)
    have hs' : stieltjesSeq (N + 1 + 1) = stieltjesSeq (N + 1)
        + (Real.log (((N + 1 : ℕ) : ℝ) + 1) / (((N + 1 : ℕ) : ℝ) + 1)
          - (Real.log (((N + 1 : ℕ) : ℝ) + 1) ^ 2 / 2 - Real.log ((N + 1 : ℕ) : ℝ) ^ 2 / 2)) := by
      linarith [hs]
    have hh : (harmonic (N + 1 + 1) : ℝ) = harmonic (N + 1) + 1 / ((N : ℝ) + 1 + 1) := by
      rw [harmonic_succ]; push_cast; ring
    rw [hs', hh]
    push_cast
    have hpos : (0 : ℝ) < (N : ℝ) + 1 + 1 := by positivity
    have hpos' : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp
    ring

/-- **`Σ_n zetaTermD (n+1) 1 = γ₁ + γ - 1`.**

### Summary of Proof
The series is summable (dominated by `summable_zetaTermD_bound`), and its partial sums
(`sum_zetaTermD_one`) tend to `γ₁ + γ - 1` by `Definitions.tendsto_stieltjesSeq` and Mathlib's
`Real.tendsto_harmonic_sub_log`.

### Dependencies
**Depends on:** `sum_zetaTermD_one`, `zetaTermD_norm_le`, `summable_zetaTermD_bound`,
`Definitions.tendsto_stieltjesSeq`.
**Used by:** `hasDerivAt_riemannZeta₀_one`. -/
theorem hasSum_zetaTermD_one :
    HasSum (fun n : ℕ => zetaTermD (n + 1) 1)
      (stieltjesConstant1 + Real.eulerMascheroniConstant - 1) := by
  have hsum : Summable (fun n : ℕ => zetaTermD (n + 1) 1) := by
    refine Summable.of_norm_bounded summable_zetaTermD_bound (fun n => ?_)
    have := zetaTermD_norm_le (n := n + 1) (Nat.succ_pos n) (y := 1) (by norm_num)
    push_cast at this ⊢
    exact this
  rw [hsum.hasSum_iff_tendsto_nat]
  simp only [sum_zetaTermD_one]
  have h1 : Filter.Tendsto (fun N : ℕ => stieltjesSeq (N + 1)) Filter.atTop
      (nhds stieltjesConstant1) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr tendsto_stieltjesSeq
  have h2 : Filter.Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ) - Real.log ((N : ℝ) + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have := (Filter.tendsto_add_atTop_iff_nat 1).mpr Real.tendsto_harmonic_sub_log
    refine this.congr fun N => ?_
    push_cast
    ring
  have := (h1.add h2).sub_const 1
  refine this.congr fun N => ?_
  ring

/-- **For real `s > 1`, `riemannZeta₀ s = 1 - s · termTSum s`.**

### Summary of Proof
`riemannZeta_eq_inv_sub_add`, the Dirichlet series `zeta_eq_tsum_one_div_nat_add_one_cpow`
(cast to the real series), and `ZetaAsymptotics.zeta_limit_aux1`.

### References
Mathlib: `ZetaAsymptotics.zeta_limit_aux1`, `riemannZeta_eq_inv_sub_add`.

### Dependencies
**Depends on:** none.
**Used by:** `hasDerivAt_riemannZeta₀_one`. -/
theorem riemannZeta₀_ofReal_of_one_lt {s : ℝ} (hs : 1 < s) :
    riemannZeta₀ (s : ℂ) = ((1 - s * ZetaAsymptotics.termTSum s : ℝ) : ℂ) := by
  have hs1 : (s : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h0 : riemannZeta₀ (s : ℂ) = riemannZeta s - ((s : ℂ) - 1)⁻¹ := by
    rw [riemannZeta_eq_inv_sub_add hs1]; ring
  rw [h0]
  have hre : 1 < (s : ℂ).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hz := ZetaAsymptotics.zeta_limit_aux1 hs
  have hcast : (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (s : ℂ))
      = ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1 with n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    norm_cast
  rw [hcast, ← hz]
  push_cast
  ring

/-- **`γ₁` is `ζ`'s order-one Laurent coefficient at `s = 1`:** `(riemannZeta₀)'(1) = -γ₁`,
with `riemannZeta₀` Mathlib's pole-free part `ζ(s) - 1/(s-1)` (extended by `γ` at `1`).

### Summary of Proof
`riemannZeta₀` is entire (`differentiable_riemannZeta₀`), so its derivative at `1` equals the
right derivative of the real restriction `y ↦ riemannZeta₀ y` (`HasDerivAt.comp_ofReal`,
`UniqueDiffWithinAt.eq_deriv` on `Ioi 1`).  On `(1, ∞)` that restriction is
`1 - y · termTSum y` (`riemannZeta₀_ofReal_of_one_lt`), and at `1` both sides equal `γ`
(`riemannZeta₀_one`, `term_tsum_one`); the product rule with `hasDerivAt_termTSum_one` and
`hasSum_zetaTermD_one` gives the derivative `-(T(1) + T'(1)) = -((1 - γ) + (γ₁ + γ - 1)) = -γ₁`.

### Lean Notes
This is the *only* place where the defining limit of `Definitions.stieltjesConstant1` meets `ζ`;
everything downstream (`hasDerivAt_deriv_zetaReg_one`, `logDerivZetaCoeff_one`,
`neg_logDeriv_zeta_bound_of_claim_two`) reaches `γ₁` through it.  The derivation runs to about
300 lines, none of it numeric; `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`.

Numerically corroborated by `Code/verify_riemannZeta0_deriv_one.py` (central differences of
`ζ(s) - 1/(s-1)` at `1` against mpmath's `stieltjes(1)`).

### References
Coffey, *The Stieltjes constants…*, arXiv:0706.0343v2, Eqs. (1)–(2); Titchmarsh §2.
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39), at `n = 1`.

### Dependencies
**Depends on:** `hasDerivAt_termTSum_one`, `hasSum_zetaTermD_one`, `riemannZeta₀_ofReal_of_one_lt`,
`stieltjesConstant1`.
**Used by:** `hasDerivAt_deriv_zetaReg_one`. -/
theorem hasDerivAt_riemannZeta₀_one :
    HasDerivAt riemannZeta₀ (-(stieltjesConstant1 : ℂ)) 1 := by
  have hd : HasDerivAt riemannZeta₀ (deriv riemannZeta₀ 1) 1 :=
    (differentiable_riemannZeta₀ 1).hasDerivAt
  have hd' : HasDerivAt riemannZeta₀ (deriv riemannZeta₀ 1) ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]; exact hd
  have hg : HasDerivAt (fun y : ℝ => riemannZeta₀ (y : ℂ)) (deriv riemannZeta₀ 1) 1 :=
    hd'.comp_ofReal
  have hT1 : ZetaAsymptotics.termTSum 1 = 1 - Real.eulerMascheroniConstant :=
    ZetaAsymptotics.term_tsum_one.tsum_eq
  have hTd := hasDerivAt_termTSum_one
  rw [hasSum_zetaTermD_one.tsum_eq] at hTd
  have hf : HasDerivAt (fun s : ℝ => 1 - s * ZetaAsymptotics.termTSum s)
      (-(1 * ZetaAsymptotics.termTSum 1
        + id (1 : ℝ) * (stieltjesConstant1 + Real.eulerMascheroniConstant - 1))) 1 :=
    ((hasDerivAt_id (1 : ℝ)).mul hTd).const_sub 1
  have hfC := hf.ofReal_comp
  have h1 : HasDerivWithinAt (fun y : ℝ => riemannZeta₀ (y : ℂ)) (deriv riemannZeta₀ 1)
      (Set.Ioi 1) 1 := hg.hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun y : ℝ => riemannZeta₀ (y : ℂ))
      (((-(1 * ZetaAsymptotics.termTSum 1
        + id (1 : ℝ) * (stieltjesConstant1 + Real.eulerMascheroniConstant - 1))) : ℝ) : ℂ)
      (Set.Ioi 1) 1 := by
    refine hfC.hasDerivWithinAt.congr (fun y hy => riemannZeta₀_ofReal_of_one_lt hy) ?_
    rw [Complex.ofReal_one, riemannZeta₀_one, hT1]
    push_cast
    ring
  have heq := (uniqueDiffWithinAt_Ioi (1 : ℝ)).eq_deriv (Set.Ioi 1) h1 h2
  rw [heq, hT1] at hd
  convert hd using 1
  simp only [id]
  push_cast
  ring

/-- **The bridge between the two characterisations of `γ₁`: `(ζ_reg)''(1) = -2γ₁`.**

### Summary of Proof
With `g(z) = zetaReg(1+z) = z·ζ(1+z)`, the Laurent expansion
`ζ(1+z) = 1/z + Σ_{n≥0} (-1)ⁿ γ_n zⁿ/n!` gives `g(z) = 1 + γz - γ₁z² + ⋯`, so `g''(0) = -2γ₁`.
In Mathlib's vocabulary `zetaReg = riemannZeta₁` (`zetaReg_eq_riemannZeta₁`), so
`(ζ_reg)''(1) = 2·(riemannZeta₀)'(1)`, and `(riemannZeta₀)'(1) = -γ₁` is
`hasDerivAt_riemannZeta₀_one`.  The reduction:
rewrite by `zetaReg_eq_riemannZeta₁`, apply the product rule to
`riemannZeta₁ s = 1 + (s-1)·riemannZeta₀ s` to get
`deriv zetaReg s = riemannZeta₀ s + (s-1)·(riemannZeta₀)'(s)` for all `s`, then differentiate
once more at `s = 1`, where the `(s-1)` factor annihilates the second-derivative term and leaves
`2·(riemannZeta₀)'(1) = -2γ₁`.  Second differentiability of `riemannZeta₀` is Mathlib's
`differentiable_riemannZeta₀.deriv`.

### Lean Notes
Stated as a `HasDerivAt` rather than an equation about `deriv (deriv zetaReg) 1` so that it
carries the differentiability of `deriv zetaReg` at `1` as well as its value — both are needed by
the quotient rule in `logDerivZetaCoeff_one`.

Corroborated numerically: `(ζ_reg)''(1) = -2γ₁ = 0.1456316909673534497…`, and
`γ² - (ζ_reg)''(1) = 0.187546232840365224597…` matches the independent 40-digit contour value of
`a_1` computed in `Code/verify_laurent_coefficients.py`.

### References
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39), the Stieltjes-constant formula, at
`n = 1`.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_riemannZeta₁`, `hasDerivAt_riemannZeta₀_one`,
`stieltjesConstant1`.
**Used by:** `logDerivZetaCoeff_one`. -/
theorem hasDerivAt_deriv_zetaReg_one :
    HasDerivAt (deriv zetaReg) (-(2 * (stieltjesConstant1 : ℂ))) 1 := by
  have hd0 : Differentiable ℂ riemannZeta₀ := differentiable_riemannZeta₀
  have hderiv : deriv zetaReg = fun s : ℂ => riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s := by
    rw [zetaReg_eq_riemannZeta₁]
    funext s
    have h : HasDerivAt riemannZeta₁ (riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s) s := by
      have hmul : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta₀ w)
          (1 * riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s) s :=
        ((hasDerivAt_id s).sub_const 1).mul (hd0 s).hasDerivAt
      have h2 := hmul.const_add (1 : ℂ)
      rw [one_mul] at h2
      exact h2
    exact h.deriv
  rw [hderiv]
  have hdd : DifferentiableAt ℂ (deriv riemannZeta₀) 1 := hd0.deriv.differentiableAt
  have h2 : HasDerivAt (fun s : ℂ => riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s)
      (-(stieltjesConstant1 : ℂ)
        + (1 * deriv riemannZeta₀ 1 + ((1 : ℂ) - 1) * deriv (deriv riemannZeta₀) 1)) 1 :=
    hasDerivAt_riemannZeta₀_one.add (((hasDerivAt_id (1 : ℂ)).sub_const 1).mul hdd.hasDerivAt)
  rw [hasDerivAt_riemannZeta₀_one.deriv] at h2
  convert h2 using 1
  ring

/-- **`a_0 = γ` exactly.**

### Summary of Proof
Unwind the definitions. `logDerivZetaCoeff 0` is `-(G(1)).re + (1/3+1/5+1/7)`, and
`G(1) = -(zetaReg'(1)/zetaReg(1)) + 1/3+1/5+1/7 = -γ + (1/3+1/5+1/7)`, using `deriv_zetaReg_one`
and `zetaReg_one`. The two patch contributions cancel and only `γ` survives.

### Lean Notes
An exact identity, not a numeric bound — which is what makes the `n = 0 → 1` antitone step free of
any numerical input. Independently confirmed to 40 digits by
`Code/verify_laurent_coefficients.py`.

### References
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39), the `n = 0` case of its
Stieltjes-constant formula. It also matches the leading `-γ` of
`neg_logDeriv_zeta_bound_of_claim_two`.

### Dependencies
**Depends on:** `deriv_zetaReg_one`, `logDerivZetaCoeff`, `logDerivZetaG`, `logDerivZetaGext`,
`logDerivZetaGext_eq`, `rpow_neg_natCast_sub_one`, `zetaReg_one`.
**Used by:** `abs_logDerivZetaCoeff_le`, `logDerivZetaCoeff_pos_all`,
`logDerivZetaCoeff_two_mul_succ_le_all`, `neg_logDeriv_zeta_bound_of_claim_two`,
`neg_logDeriv_zeta_lt_one_div`, `RectangularBounds.logzeta_le_linear`. -/
theorem logDerivZetaCoeff_zero : logDerivZetaCoeff 0 = Real.eulerMascheroniConstant := by
  have hne : (1 : ℂ) ∉ ({-2, -4, -6} : Set ℂ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hval : (iteratedDeriv 0 (fun z : ℂ => logDerivZetaGext (1 + z)) 0)
      = ((-Real.eulerMascheroniConstant + (1/3 + 1/5 + 1/7) : ℝ) : ℂ) := by
    rw [iteratedDeriv_zero]
    have h1 : (1 : ℂ) + 0 = 1 := by ring
    rw [h1, logDerivZetaGext_eq hne]
    unfold logDerivZetaG
    rw [deriv_zetaReg_one, zetaReg_one]
    push_cast
    norm_num
    ring
  rw [logDerivZetaCoeff, hval,
    rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3) 0,
    rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5) 0,
    rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7) 0]
  simp only [Complex.ofReal_re, Nat.factorial_zero, Nat.cast_one]
  norm_num
  linarith

/-! ### Numeric input: the two-sided bracket on `γ² + 2γ₁`

`logDerivZetaCoeff_one` identifies `a_1` with `γ² + 2γ₁` exactly, so all the numeric content of
the `n = 1` coefficient bound sits in the single constant `γ² + 2γ₁ = 0.187546232840365224597…`.
The two halves of `0.15 ≤ γ² + 2γ₁ ≤ 0.20` are of *very* different difficulty — the lower has
`0.0375` of slack, the upper only `0.0125`, and the derivative `d(γ²)/dγ = 2γ ≈ 1.15` amplifies
every error in `γ` — so they are stated and proved separately below: the lower from the trapezoid
bracket at `m = 5`, the upper from the Euler–Maclaurin bracket `Definitions.stieltjesSeqHi` at
`m = 16` (see `stieltjes_combo_upper_bound`'s `### Lean Notes` for why the crude bracket would
cost `m ≈ 800` and 139 prime logarithms).

The ingredients are:

* Mathlib's `Real.log_two_gt_d9` / `Real.log_two_lt_d9`, giving `log 2` to nine places;
* Mathlib's monotone bracket `eulerMascheroniSeq n < γ < eulerMascheroniSeq' n`;
* this project's bracket `stieltjesSeqMid m ≤ γ₁ ≤ stieltjesSeqHi m` (`Definitions`), valid from
  `m = 5`, with errors `O((log m)/m²)` and `O((log m)/m³)`;
* for `log 3, 5, 7, 11, 13`, Mathlib's Taylor estimate `Real.abs_log_sub_add_sum_range_le`,

    `|(∑_{i<n} xⁱ⁺¹/(i+1)) + log (1-x)| ≤ |x|ⁿ⁺¹/(1-|x|)`,

  whose error is **geometric** in the number of terms.  This is the decisive change of tool: the
  `Real.log_le_sub_one_of_pos` telescoping used elsewhere in this project loses `O((t-1)²)` per
  step and so converges only like `1/n`, which is not enough here (see
  `stieltjes_combo_lower_bound`'s `### Lean Notes`).

All of the closing arithmetic is certified in exact rational arithmetic by
`Code/verify_combo_lower_half.py`.
-/

/-- **`0.4052 ≤ log (3/2)`.**

### Summary of Proof
`Real.abs_log_sub_add_sum_range_le` at `x = -1/2` with `n = 12` terms: it bounds
`|∑_{i<12} (-1/2)ⁱ⁺¹/(i+1) + log (3/2)|` by `(1/2)¹³/(1/2) = 2⁻¹² = 0.000244…`.  The partial sum
is the alternating series `-(1/2 - 1/8 + 1/24 - ⋯)`, evaluated by `norm_num`; negating it and
subtracting the error term gives `log (3/2) ≥ 0.405458… - 0.000245 = 0.405214…`.

### Lean Notes
Only the lower half of the `abs_le` split is used.  Twelve terms are far more than the target
needs (the true value is `0.4054651081…`, so the stated `0.4052` has `0.00026` to spare); they
cost nothing, since the error is geometric.

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`.

### Dependencies
**Depends on:** none.
**Used by:** `log_three_lower_bound`. -/
theorem log_three_halves_lower_bound : (0.4052 : ℝ) ≤ Real.log (3 / 2) := by
  have habs : |(-(1 / 2) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 12
  rw [abs_le] at h
  have h1 := h.1
  have hx : (1 : ℝ) - -(1 / 2) = 3 / 2 := by norm_num
  rw [hx] at h1
  norm_num [Finset.sum_range_succ] at h1
  linarith

/-- **`log (5/4) ≤ 0.2233`.**

### Summary of Proof
`Real.abs_log_sub_add_sum_range_le` at `x = -1/4` with `n = 6` terms, whose error term is
`(1/4)⁷/(3/4) = 1/12288 = 0.0000814…`.  The true value is `0.2231435513…`, so the stated `0.2233`
has `0.00016` to spare.

### Lean Notes
Only the upper half of the `abs_le` split is used.  Fewer terms are needed than for `log (3/2)`
because the ratio `1/4` is smaller.

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`.

### Dependencies
**Depends on:** none.
**Used by:** `log_five_upper_bound`. -/
theorem log_five_quarters_upper_bound : Real.log (5 / 4) ≤ (0.2233 : ℝ) := by
  have habs : |(-(1 / 4) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 6
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - -(1 / 4) = 5 / 4 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  linarith

/-- **`1.098 ≤ log 3`.**

### Summary of Proof
`log 3 = log 2 + log (3/2)`, with `log 2 > 0.6931471803` (`Real.log_two_gt_d9`) and
`log (3/2) ≥ 0.4052` (`log_three_halves_lower_bound`); the sum is `1.0983471803…`.

### Lean Notes
The true value is `1.0986122886…`.  The cheaper route, one application of
`Real.log_le_sub_one_of_pos` at `2/3`, gives only `log 3 ≥ log 2 + 1/3 = 1.0264805…`, which is
`0.072` too small — enough to sink `stieltjes_combo_lower_bound` on its own.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_three_halves_lower_bound`.
**Used by:** `stieltjesConstant1_lower_bound`. -/
theorem log_three_lower_bound : (1.098 : ℝ) ≤ Real.log 3 := by
  have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  have h32 := log_three_halves_lower_bound
  rw [hsplit]
  norm_num at h2 h32 ⊢
  linarith

/-- **`log 5 ≤ 1.61`.**

### Summary of Proof
`log 5 = 2 log 2 + log (5/4)`, with `log 2 < 0.6931471808` (`Real.log_two_lt_d9`) and
`log (5/4) ≤ 0.2233` (`log_five_quarters_upper_bound`); the sum is `1.6095943616…`.

### Lean Notes
The true value is `1.6094379124…`.  Compare `Definitions.neg_one_eighth_lt_stieltjesSeqMid_five`'s
`log 5 ≤ 2 log 2 + 1/8 + 1/9 = 1.6225`, from the factorisation `5 = 4·(9/8)·(10/9)`: that is
`0.013` too large, and since the coefficient of `log 5` in `stieltjesSeqMid 5` is
`1/10 - log 5 ≈ -1.51`, it costs `0.020` — again enough on its own to sink
`stieltjes_combo_lower_bound`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_five_quarters_upper_bound`.
**Used by:** `stieltjesConstant1_lower_bound`. -/
theorem log_five_upper_bound : Real.log 5 ≤ (1.61 : ℝ) := by
  have hsplit : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring,
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_lt_d9
  have h54 := log_five_quarters_upper_bound
  rw [hsplit]
  norm_num at h2 h54 ⊢
  linarith

/-! #### Upper bounds on the logarithms of the primes up to `13`

These serve the *upper* half `γ² + 2γ₁ ≤ 0.20`, via `stieltjesSeqHi 16`, whose expansion
`stieltjesSeqHi_sixteen_eq` involves `log 2, 3, 5, 7, 11, 13` with positive coefficients (and
`-8 (log 2)²`, which needs `log 2` from *below*).  Each is Mathlib's `Real.log_two_lt_d9` plus one
application of `Real.abs_log_sub_add_sum_range_le` to a ratio close to `1`:
`3 = 2·(3/2)`, `5 = 4·(5/4)`, `7 = 8·(7/8)`, `11 = 12·(11/12)`, `13 = 12·(13/12)`.  All five are
correct to five decimals (true values `1.0986123, 1.6094379, 1.9459101, 2.3978953, 2.5649494`).
-/

/-- **`log 3 ≤ 1.09863`.**

### Summary of Proof
`log 3 = log 2 + log (3/2)`, `Real.log_two_lt_d9`, and `Real.abs_log_sub_add_sum_range_le` at
`x = -1/2` with `17` terms (error `2⁻¹⁷/(1/2) = 1.5·10⁻⁵`, against `1.09863 - log 3 = 1.8·10⁻⁵`).

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`, `Real.log_two_lt_d9`.

### Dependencies
**Depends on:** none.
**Used by:** `log_eleven_upper_bound`, `log_thirteen_upper_bound`,
`stieltjesConstant1_upper_bound`. -/
theorem log_three_upper_bound : Real.log 3 ≤ 1.09863 := by
  have habs : |(-(1 / 2) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 17
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - -(1 / 2) = 3 / 2 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_two_lt_d9
  rw [hsplit]
  linarith

/-- **`log 5 ≤ 1.60945`**, sharper than `log_five_upper_bound` (`≤ 1.61`).

### Summary of Proof
`log 5 = 2 log 2 + log (5/4)` and `Real.abs_log_sub_add_sum_range_le` at `x = -1/4` with `10`
terms (error `4⁻¹⁰/(3/4) = 1.3·10⁻⁶`).

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`, `Real.log_two_lt_d9`.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjesConstant1_upper_bound`. -/
theorem log_five_upper_bound_sharp : Real.log 5 ≤ 1.60945 := by
  have habs : |(-(1 / 4) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 10
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - -(1 / 4) = 5 / 4 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hsplit : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_two_lt_d9
  rw [hsplit]
  linarith

/-- **`log 7 ≤ 1.94592`.**

### Summary of Proof
`log 7 = 3 log 2 + log (7/8)` and `Real.abs_log_sub_add_sum_range_le` at `x = 1/8` with `8`
terms (error `8⁻⁸/(7/8) = 6.8·10⁻⁸`).

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`, `Real.log_two_lt_d9`.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjesConstant1_upper_bound`. -/
theorem log_seven_upper_bound : Real.log 7 ≤ 1.94592 := by
  have habs : |(1 / 8 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 8
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - 1 / 8 = 7 / 8 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hsplit : Real.log 7 = 3 * Real.log 2 + Real.log (7 / 8) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_two_lt_d9
  rw [hsplit]
  linarith

/-- **`log 11 ≤ 2.39792`.**

### Summary of Proof
`log 11 = 2 log 2 + log 3 + log (11/12)`, `log_three_upper_bound`, and
`Real.abs_log_sub_add_sum_range_le` at `x = 1/12` with `8` terms.

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`, `Real.log_two_lt_d9`.

### Dependencies
**Depends on:** `log_three_upper_bound`.
**Used by:** `stieltjesConstant1_upper_bound`. -/
theorem log_eleven_upper_bound : Real.log 11 ≤ 2.39792 := by
  have habs : |(1 / 12 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 8
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - 1 / 12 = 11 / 12 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hsplit : Real.log 11 = 2 * Real.log 2 + Real.log 3 + Real.log (11 / 12) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2' := Real.log_two_lt_d9
  have h3 := log_three_upper_bound
  rw [hsplit]
  linarith

/-- **`log 13 ≤ 2.56498`.**

### Summary of Proof
`log 13 = 2 log 2 + log 3 + log (13/12)`, `log_three_upper_bound`, and
`Real.abs_log_sub_add_sum_range_le` at `x = -1/12` with `8` terms.

### References
No tex counterpart.  Mathlib: `Real.abs_log_sub_add_sum_range_le`, `Real.log_two_lt_d9`.

### Dependencies
**Depends on:** `log_three_upper_bound`.
**Used by:** `stieltjesConstant1_upper_bound`. -/
theorem log_thirteen_upper_bound : Real.log 13 ≤ 2.56498 := by
  have habs : |(-(1 / 12) : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le habs 8
  rw [abs_le] at h
  have h2 := h.2
  have hx : (1 : ℝ) - -(1 / 12) = 13 / 12 := by norm_num
  rw [hx] at h2
  norm_num [Finset.sum_range_succ] at h2
  have hsplit : Real.log 13 = 2 * Real.log 2 + Real.log 3 + Real.log (13 / 12) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2' := Real.log_two_lt_d9
  have h3 := log_three_upper_bound
  rw [hsplit]
  linarith

/-- **`-0.076 ≤ γ₁`**, a sharpening of `Definitions.neg_one_eighth_lt_stieltjesConstant1`.

### Summary of Proof
The trapezoid lower bracket `Definitions.stieltjesSeqMid_le_stieltjesConstant1` at `m = 5`, whose
value `Definitions.stieltjesSeqMid_five_eq` expands as
`log 2 + (log 3)/3 + (log 5)/10 - (log 5)²/2`.  Feeding in `log 2 > 0.6931471803`,
`log 3 ≥ 1.098` and `0 ≤ log 5 ≤ 1.61` gives `≥ -0.0759028197…`.

Since `c ↦ c/10 - c²/2` is decreasing for `c ≥ 1/10`, the *upper* bound on `log 5` is the worst
case; the nonnegativity of `log 5` is needed as well, because the function is increasing below
`1/10`.  `nlinarith` is given the product hint `log 5 · (1.61 - log 5) ≥ 0`, which is exactly the
inequality `c² ≤ 1.61 c` that turns the quadratic into a linear one.

### Lean Notes
The true value of `stieltjesSeqMid 5` is `-0.0748501290…` and of `γ₁` is `-0.0728158455…`.

**Do not read that `0.0011` as proof slack.**  What the chain above actually establishes is
`≥ -0.0759028197…`, so the stated `-0.076` clears it by only `9.7·10⁻⁵`.  Tightening the constant
here, or loosening `log_three_lower_bound` / `log_five_upper_bound`, falls off a cliff almost
immediately; the room to absorb such a change lives in `stieltjes_combo_lower_bound`'s final
margin of `0.0133`, not in this step.

This supersedes `Definitions.neg_one_eighth_lt_stieltjesConstant1` (`γ₁ > -1/8 = -0.125`) for the
purposes of `stieltjes_combo_lower_bound`: that cruder bound, which suffices for
`Jensen.JensenBounds.stieltjes_combo_pos`, is `0.049` too weak here.  It is kept where it is
because it is what `stieltjes_combo_pos` needs and it has a cheaper proof.

### References
No tex counterpart.  Certified in exact rational arithmetic by
`Code/verify_combo_lower_half.py`.

### Dependencies
**Depends on:** `log_three_lower_bound`, `log_five_upper_bound`,
`Definitions.stieltjesSeqMid_le_stieltjesConstant1`, `Definitions.stieltjesSeqMid_five_eq`.
**Used by:** `stieltjes_combo_lower_bound`. -/
theorem stieltjesConstant1_lower_bound : (-0.076 : ℝ) ≤ stieltjesConstant1 := by
  refine le_trans ?_ (stieltjesSeqMid_le_stieltjesConstant1 (by norm_num : (5 : ℕ) ≤ 5))
  rw [stieltjesSeqMid_five_eq]
  have h2 := Real.log_two_gt_d9
  have h3 := log_three_lower_bound
  have hc := log_five_upper_bound
  have hcnn : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hcnn (sub_nonneg.2 hc)]

/-- **`0.5615 ≤ γ`.**

### Summary of Proof
Mathlib's `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant` at `n = 31`:
`γ > eulerMascheroniSeq 31 = harmonic 31 - log 32`.  The harmonic number is the exact rational
`290774257297357/72201776446800 = 4.0272451954…` (`norm_num` on the unfolded `Finset` sum), and
`log 32 = 5 log 2 < 5 · 0.6931471808 = 3.465735904` (`Real.log_two_lt_d9`).  The difference is
`0.5615092914…`.

### Lean Notes
`n = 31` is chosen so that `n + 1 = 32` is a **power of two**: `log 32 = 5 log 2` is then exact,
and the only transcendental input is Mathlib's nine-digit `log 2`.  No bound on `log 21`, or on
any other non-dyadic logarithm, is needed.

`n = 31` is also close to the smallest workable choice.  The requirement from
`stieltjes_combo_lower_bound` is `γ² ≥ 0.15 + 2·0.076 = 0.302`, i.e. `γ ≥ 0.54955`; the previous
dyadic candidate `n = 15` gives only `eulerMascheroniSeq 15 = 0.5456403…`, which fails.

**The stated constant is nearly exhausted**: the chain proves `γ ≥ 0.5615092914…`, clearing
`0.5615` by `9.3·10⁻⁶`.  Rounding it up to `0.5616` would break the proof.  As with
`stieltjesConstant1_lower_bound`, the real room is the `0.0133` margin of
`stieltjes_combo_lower_bound`, which is where a change of constants must be re-checked.

### References
No tex counterpart.  Mathlib: `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`,
`Real.log_two_lt_d9`.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjes_combo_lower_bound`. -/
theorem eulerMascheroniConstant_lower_bound : (0.5615 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hh : Real.eulerMascheroniSeq 31 = (290774257297357 / 72201776446800 : ℝ) - Real.log 32 := by
    rw [Real.eulerMascheroniSeq]
    norm_num [harmonic, Finset.sum_range_succ]
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_lt_d9
  rw [hh, h32] at h
  norm_num at h ⊢
  linarith

/-- **The lower half of the numeric claim: `0.15 ≤ γ² + 2γ₁`.**

### Summary of Proof
Combine `eulerMascheroniConstant_lower_bound` (`γ ≥ 0.5615`, hence `γ² ≥ 0.31528225`) with
`stieltjesConstant1_lower_bound` (`γ₁ ≥ -0.076`, hence `2γ₁ ≥ -0.152`).  The sum is
`0.16328225 ≥ 0.15`, a margin of `0.0133`.  The true value is `0.187546232840365224597…`.

### Lean Notes
**The margin is genuine but it is not large, and the route matters.**  The cheaper route that
suggests itself — `γ > harmonic 20 - log 21` with `log 21 ≤ 3.05029`, paired with
`γ₁ ≥ stieltjesSeqMid 5` — does not reach the claim, and `Code/verify_combo_lower_half.py`
records the arithmetic:

* with `log 21 ≤ 3.05029` the resulting `γ ≥ 0.54744966` gives `γ² ≥ 0.29970113`, so the claim
  needs `γ₁ ≥ -0.07485`.  That is the *exact value* of `stieltjesSeqMid 5` — the margin is
  `+1·10⁻⁶` — whereas the crude `γ₁ > -1/8` misses by `0.100`;
* the `log t ≤ t - 1` telescoping over `21/16 = (17/16)(18/17)⋯(21/20)` gives only
  `log 21 ≤ 3.0521`, and even paired with the exact `stieltjesSeqMid 5` that fails by `0.0020`.

What closes the gap is a *pair* of sharpenings, on both constants at once, using a tool with
geometric rather than `1/n` error: `Real.abs_log_sub_add_sum_range_le` for `log 3` and `log 5`,
and the dyadic choice `n = 31` (so `log 32 = 5 log 2`) for `γ`.  Neither sharpening alone
suffices — with `γ ≥ 0.5615` but the weaker `log 3 ≥ log 2 + 1/3` the sum lands at `0.1158`, and
with the weaker `log 5 ≤ 1.6225` at `0.1256`.

### References
No tex counterpart; see `stieltjes_combo_numeric_bounds`.  Certified in exact rational
arithmetic by `Code/verify_combo_lower_half.py`.

### Dependencies
**Depends on:** `eulerMascheroniConstant_lower_bound`, `stieltjesConstant1_lower_bound`.
**Used by:** `stieltjes_combo_numeric_bounds`. -/
theorem stieltjes_combo_lower_bound :
    0.15 ≤ Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 := by
  have hg := eulerMascheroniConstant_lower_bound
  have hg1 := stieltjesConstant1_lower_bound
  nlinarith [hg, hg1]

/-- **`stieltjesSeqHi 16` in terms of the logarithms of `2, 3, 5, 7, 11, 13`.**

### Summary of Proof
Unfold `stieltjesSeqHi 16 = ∑_{k≤16} (log k)/k - (log 16)²/2 - (log 16)/32 - (1 - log 16)/2048`
and factor each composite `k ≤ 16` (`log 4 = 2 log 2`, `log 6 = log 2 + log 3`, …,
`log 16 = 4 log 2`); `norm_num` and `ring` collect the coefficients.  The coefficient of `log p`
in the sum is `∑_{k≤16} v_p(k)/k`, which for `p = 2` is
`1/2 + 2/4 + 1/6 + 3/8 + 1/10 + 2/12 + 1/14 + 4/16 = 2.1298`, etc.

### Lean Notes
The right-hand side is left as an unsimplified sum of fractions so that each coefficient can be
read off against the factorisation; `norm_num` in `stieltjesConstant1_upper_bound` evaluates them.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Definitions.stieltjesSeqHi`, `Definitions.stieltjesSeqMid`,
`Definitions.stieltjesSeq`.
**Used by:** `stieltjesConstant1_upper_bound`. -/
theorem stieltjesSeqHi_sixteen_eq :
    stieltjesSeqHi 16
      = (1 / 2 + 2 / 4 + 1 / 6 + 3 / 8 + 1 / 10 + 2 / 12 + 1 / 14 + 4 / 16) * Real.log 2
        + (1 / 3 + 1 / 6 + 2 / 9 + 1 / 12 + 1 / 15) * Real.log 3
        + (1 / 5 + 1 / 10 + 1 / 15) * Real.log 5 + (1 / 7 + 1 / 14) * Real.log 7
        + Real.log 11 / 11 + Real.log 13 / 13
        - 8 * Real.log 2 ^ 2 - Real.log 2 / 8 - (1 - 4 * Real.log 2) / 2048 := by
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have l9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [← l4, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  simp only [stieltjesSeqHi, stieltjesSeqMid, stieltjesSeq, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [l4, l6, l8, l9, l10, l12, l14, l15, l16]
  ring

/-- **`γ₁ ≤ -0.0724`.**

### Summary of Proof
The Euler–Maclaurin upper bracket `Definitions.stieltjesConstant1_le_stieltjesSeqHi` at `m = 16`,
expanded by `stieltjesSeqHi_sixteen_eq`, is a linear form in `log 2, 3, 5, 7, 11, 13` with
positive coefficients, minus `8 (log 2)²`.  Upper bounds on the six logarithms
(`Real.log_two_lt_d9` and the five `log_*_upper_bound`s above) and the lower bound
`(log 2)² ≥ 0.6931471803²` (`Real.log_two_gt_d9`) give `≤ -0.07242…`.

### Lean Notes
The true values are `stieltjesSeqHi 16 = -0.0727270…` and `γ₁ = -0.0728158…`, so the bracket
itself has error `9·10⁻⁵`, and the five-decimal logarithm bounds lose a further `3·10⁻⁴` — all
of it in the `8 (log 2)²` term and in the `log 2` terms, whose coefficients are by far the
largest, which is why `log 2` alone is taken to nine decimals.  The stated `-0.0724` clears the
chain's `-0.07242` by `2·10⁻⁵`; the real room is the `0.0025` margin of
`stieltjes_combo_upper_bound`.

### References
No tex counterpart.  The bracket and the five-decimal logarithm bounds are checked in
`Code/verify_stieltjes_bracketing.py`, which also reports the error of `stieltjesSeqHi 16` against
the true `γ₁`.  (`Code/verify_combo_lower_half.py` does NOT certify this: it prices the rejected
route through `stieltjesSeq` at `m ≈ 800`.)

### Dependencies
**Depends on:** `Definitions.stieltjesConstant1_le_stieltjesSeqHi`, `stieltjesSeqHi_sixteen_eq`,
`log_three_upper_bound`, `log_five_upper_bound_sharp`, `log_seven_upper_bound`,
`log_eleven_upper_bound`, `log_thirteen_upper_bound`.
**Used by:** `stieltjes_combo_upper_bound`, `JensenBounds.stieltjes_combo_bound`. -/
theorem stieltjesConstant1_upper_bound : stieltjesConstant1 ≤ -0.0724 := by
  have h := stieltjesConstant1_le_stieltjesSeqHi (m := 16) (by norm_num)
  rw [stieltjesSeqHi_sixteen_eq] at h
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h3 := log_three_upper_bound
  have h5 := log_five_upper_bound_sharp
  have h7 := log_seven_upper_bound
  have h11 := log_eleven_upper_bound
  have h13 := log_thirteen_upper_bound
  have hsq : (0.6931471803 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num) h2.le
  nlinarith [h, h2, h2', h3, h5, h7, h11, h13, hsq]

/-- **`γ ≤ 0.5851`.**

### Summary of Proof
Mathlib's `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'` at `n = 64`:
`γ < harmonic 64 - log 64`.  The harmonic number is an exact rational `< 4.7438913` (`norm_num`
on the unfolded sum) and `log 64 = 6 log 2 > 6 · 0.6931471803` (`Real.log_two_gt_d9`).  The
difference is `0.58500…`.

### Lean Notes
As in `eulerMascheroniConstant_lower_bound`, `n` is a **power of two** so that the only
transcendental input is Mathlib's nine-digit `log 2`.  The true value is `γ = 0.5772157…`, so this
bracket has error `1/(2n) ≈ 0.0078`; with `γ₁ ≤ -0.0724` the requirement is `γ² ≤ 0.3448`, i.e.
`γ ≤ 0.5872`, and `n = 64` is the smallest power of two that meets it (`n = 32` gives `0.5927`).

### References
No tex counterpart.  Mathlib: `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`,
`Real.log_two_gt_d9`.

### Dependencies
**Depends on:** none.
**Used by:** `stieltjes_combo_upper_bound`. -/
theorem eulerMascheroniConstant_upper_bound : Real.eulerMascheroniConstant ≤ 0.5851 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hseq : Real.eulerMascheroniSeq' 64 = (harmonic 64 : ℝ) - Real.log 64 := by
    simp [Real.eulerMascheroniSeq']
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
  rw [hseq, h64] at h
  have hval : (harmonic 64 : ℝ) < 4.7438913 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have h2 := Real.log_two_gt_d9
  linarith

/-- **The upper half of the numeric claim: `γ² + 2γ₁ ≤ 0.20`.**

### Summary of Proof
Combine `eulerMascheroniConstant_upper_bound` (`γ ≤ 0.5851`, hence `γ² ≤ 0.34234`) with
`stieltjesConstant1_upper_bound` (`γ₁ ≤ -0.0724`, hence `2γ₁ ≤ -0.1448`).  The sum is
`0.19754 ≤ 0.20`, a margin of `0.0025`.  The true value is `γ² + 2γ₁ = 0.187546232840365224597…`.

### Lean Notes
**Why the Euler–Maclaurin bracket is used.**  With the crude upper bracket
`γ₁ ≤ stieltjesSeq m` (error `(log m)/(2m)`) the slack `0.0125` forces `m ≈ 800` and `n ≈ 142`,
i.e. certified bounds on the logarithms of all 139 primes below `800` — an estimated **5600
lines** of Lean at the ≈40 lines per logarithm that `log_three_upper_bound` costs.  The
Euler–Maclaurin bracket `Definitions.stieltjesConstant1_le_stieltjesSeqHi` (error
`O((log m)/m³)`, from the tangent-line convexity argument in
`Definitions.log_div_id_tangent_step`) brings `m` down to `16`, so only `log 2, 3, 5, 7, 11, 13`
are needed: the whole route is about **500 lines** including the bracket.

Bounding `a_1 = γ² + 2γ₁` instead through the Laurent expansion of `-ζ'/ζ` as in the proof of
`Lemma \ref{lemma:logderzetabound}` (Lemma 38, `logderzetabound`), using the known trivial zeros
and `N(T)` bounds for the nontrivial ones, does not reach the target: the Cauchy estimate on the
disc of radius `1/2` with `|G| ≤ 0.6` yields only `a_1 ≤ 0.257`, and any sharpening would need
certified values of `ζ'`, which the project deliberately avoids (see
`stieltjes_combo_numeric_bounds`, `### Lean Notes`).  The Euler–Maclaurin route needs no
evaluation of `ζ` or `ζ'` at all.

### References
No tex counterpart; see `stieltjes_combo_numeric_bounds`.  Checked in exact rational arithmetic by
`Code/verify_stieltjes_combo_bound.sage`, with the bracket itself checked separately in
`Code/verify_stieltjes_bracketing.py`.  (`Code/verify_combo_lower_half.py` does NOT certify this:
it prices the rejected route through `stieltjesSeq` at `m ≈ 800` with 139 prime logarithms.)

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [C], with mpmath's own `euler` and `stieltjes(1)`:
`γ² + 2γ₁ = 0.187546232840365224597…`, slack `0.01245` below `0.20` and `0.03755` above `0.15`.

### Dependencies
**Depends on:** `eulerMascheroniConstant_upper_bound`, `stieltjesConstant1_upper_bound`.
**Used by:** `stieltjes_combo_numeric_bounds`. -/
theorem stieltjes_combo_upper_bound :
    Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 ≤ 0.20 := by
  have hg := eulerMascheroniConstant_upper_bound
  have hg0 : (0 : ℝ) ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hg1 := stieltjesConstant1_upper_bound
  have hsq : Real.eulerMascheroniConstant ^ 2 ≤ (0.5851 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hg0 hg 2
  nlinarith [hsq, hg1]

/-- **Numeric claim:** `0.15 ≤ γ² + 2γ₁ ≤ 0.20`, with `γ` Euler–Mascheroni and
`γ₁ = Definitions.stieltjesConstant1` the first Stieltjes constant.

### Summary of Proof
The conjunction of `stieltjes_combo_lower_bound` and `stieltjes_combo_upper_bound`; no tex
counterpart as a standalone claim. The true value is `γ² + 2γ₁ = 0.187546232840365224597…`, so
the margins are `0.0375` below and `0.0125` above.

**The two halves are very unequal and are proved separately.**  This statement is merely their
conjunction, and is the form its sole consumer `logDerivZetaCoeff_one_bounds` uses:

* `stieltjes_combo_lower_bound` (`0.15 ≤ γ²+2γ₁`) — from `γ ≥ 0.5615` at `n = 31` and
  `γ₁ ≥ -0.076` at `m = 5` (trapezoid bracket), with margin `0.0133`;
* `stieltjes_combo_upper_bound` (`γ²+2γ₁ ≤ 0.20`) — from `γ ≤ 0.5851` at `n = 64` and
  `γ₁ ≤ -0.0724` at `m = 16` (Euler–Maclaurin bracket `Definitions.stieltjesSeqHi`), with margin
  `0.0025`.

### Lean Notes
**Constraining the constant rather than `a_1` is what makes this input rigorous.** Bounding `a_1`
directly would mean a 40-digit mpmath Cauchy-contour computation, which *cannot* be done in
certified ball arithmetic: it needs `ζ'`, and Sage's `ComplexBallField` does not expose it — the
same limitation `Code/verify_lemmaA7_bound_radius7.sage` records. Constraining only the
*constant* `γ² + 2γ₁` requires no evaluation of `ζ` or `ζ'` at all, so the whole enclosure is
rigorous.

**Relation to `JensenBounds.stieltjes_combo_pos`,** which asserts the strictly weaker
`0 < γ² + 2γ₁` and is certified by the same script: the two cannot presently be shared, because
this file does not import `JensenBounds` and must not — `RectangularBounds` already imports this
file, so the dependency would be circular. Unifying them means hoisting the numeric fact into a
common ancestor (`Definitions` or `ExternalFacts`); left as a follow-up.

### References
tex: no standalone counterpart; the combination `γ²+2γ₁` appears as the coefficient of `z` in
`neg_logDeriv_zeta_bound_of_claim_two` and via `Remark \ref{lemma:logderzetabound-remark}`
(Remark 39).

### Dependencies
**Depends on:** `stieltjes_combo_lower_bound`, `stieltjes_combo_upper_bound`,
`stieltjesConstant1`.
**Used by:** `logDerivZetaCoeff_one_bounds`. -/
theorem stieltjes_combo_numeric_bounds :
    0.15 ≤ Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1
      ∧ Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 ≤ 0.20 :=
  ⟨stieltjes_combo_lower_bound, stieltjes_combo_upper_bound⟩

/-- **`a_1 = γ² + 2γ₁` exactly.**

### Summary of Proof
This is the `n = 1` case of `Remark \ref{lemma:logderzetabound-remark}` (Remark 39)'s
Stieltjes-constant formula for the `a_n`, and precisely the coefficient of `z` in
`neg_logDeriv_zeta_bound_of_claim_two`.

Writing `g(z) := zetaReg(1+z) = z·ζ(1+z)`, the Laurent expansion
`ζ(1+z) = 1/z + Σ_{n≥0} (-1)ⁿ γ_n zⁿ / n!` gives `g(z) = 1 + γz - γ₁z² + (γ₂/2)z³ - ⋯`, while
`-ζ'/ζ(1+z) = 1/z - g'/g`. Matching against `1/z + Σ_{n≥0} (-1)^{n+1} a_n zⁿ` gives
`g'/g = a_0 - a_1 z + a_2 z² - ⋯`, and to first order
`g'/g = (γ - 2γ₁z)(1 - γz) + O(z²) = γ + (-2γ₁ - γ²)z + O(z²)`, whence `a_0 = γ` — which
`logDerivZetaCoeff_zero` proves outright — and `a_1 = γ² + 2γ₁`.

That derivation is carried out in Lean here.  Its one substantial input is
`hasDerivAt_deriv_zetaReg_one` (`(ζ_reg)''(1) = -2γ₁`), the bridge between the limit-formula
definition of `γ₁` and its role as a Laurent coefficient; everything else here is calculus.
Concretely: the quotient rule on `ζ_reg'/ζ_reg` at `1`, where `ζ_reg(1) = 1` (`zetaReg_one`) and
`ζ_reg'(1) = γ` (`deriv_zetaReg_one`), gives `(ζ_reg'/ζ_reg)'(1) = (ζ_reg)''(1) - γ² = -2γ₁ - γ²`.
The three patch terms contribute `-(1/9 + 1/25 + 1/49)`, which cancels exactly against the
`3^{-2} + 5^{-2} + 7^{-2}` added back in the definition of `logDerivZetaCoeff` — the same
cancellation that makes `logDerivZetaCoeff_zero` clean.  The derivative is taken of
`logDerivZetaGext`, which agrees with `logDerivZetaG` on a *neighbourhood* of `1`, the excluded
set `{-2,-4,-6}` being finite and hence closed.

### Lean Notes
An exact identity with named classical provenance, not a numeric bound.  It quarantines all the
numeric content of the `n = 1` coefficient into `stieltjes_combo_numeric_bounds` — which, unlike
a direct bracket on `a_1`, *is* certifiable by ball arithmetic — and it is what lets
`neg_logDeriv_zeta_bound_of_claim_two` exhibit `Proposition \ref{prop:integraloutside}`
(Proposition 15)'s truncated Laurent estimate as a special case.  Mathlib supplies the constant
term of `ζ`'s Laurent expansion at `1` (`tendsto_riemannZeta_sub_one_div`) but nothing one order
further, which is why `hasDerivAt_riemannZeta₀_one` has to be proved from `ZetaAsymptotics`.

Corroborated to `2.8·10⁻²¹` by `Code/verify_laurent_coefficients.py`'s independent 40-digit
contour computation of `a_1` (`0.1875462328403652246`, against
`γ² + 2γ₁ = 0.187546232840365224597…`).

### References
tex: `Remark \ref{lemma:logderzetabound-remark}` (Remark 39), at `n = 1`.

**Independent numeric check.**
`Code/indep_mpmath_lemma37.py` block [C]: the Cauchy-integral value
`a_1 = 0.1875462328403652245972034…` agrees with mpmath's `γ² + 2γ₁` to `3×10⁻⁴²`, and
`a_0 = γ` exactly to working precision (`logDerivZetaCoeff_zero`).

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `stieltjesConstant1`, `hasDerivAt_deriv_zetaReg_one`,
`hasDerivAt_zetaReg_one`, `zetaReg_one`, `deriv_zetaReg_one`, `logDerivZetaGext_eq`,
`rpow_neg_natCast_sub_one`.
**Used by:** `logDerivZetaCoeff_one_bounds`, `neg_logDeriv_zeta_bound_of_claim_two`. -/
theorem logDerivZetaCoeff_one :
    logDerivZetaCoeff 1 = Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 := by
  -- The three patch terms `1/(s+2k)`, whose derivatives at `1` are `-(2k+1)^{-2}`.
  have hpatch : ∀ c : ℂ, c + 1 ≠ 0 →
      HasDerivAt (fun s : ℂ => 1 / (s + c)) (-(1 / (1 + c) ^ 2)) 1 := by
    intro c hc
    have hc' : (1 : ℂ) + c ≠ 0 := by rwa [add_comm]
    have h : HasDerivAt (fun s : ℂ => 1 / (s + c))
        ((0 * ((1 : ℂ) + c) - 1 * 1) / ((1 : ℂ) + c) ^ 2) 1 :=
      (hasDerivAt_const (1 : ℂ) (1 : ℂ)).div ((hasDerivAt_id (1 : ℂ)).add_const c) hc'
    have heq : ((0 : ℂ) * ((1 : ℂ) + c) - 1 * 1) / ((1 : ℂ) + c) ^ 2 = -(1 / (1 + c) ^ 2) := by
      ring
    rwa [heq] at h
  have h2 := hpatch 2 (by norm_num)
  have h4 := hpatch 4 (by norm_num)
  have h6 := hpatch 6 (by norm_num)
  -- The quotient `ζ_reg'/ζ_reg`, by the quotient rule at `1`.
  have hzne : zetaReg 1 ≠ 0 := by rw [zetaReg_one]; norm_num
  have hq : HasDerivAt (fun s : ℂ => deriv zetaReg s / zetaReg s)
      ((-(2 * (stieltjesConstant1 : ℂ)) * zetaReg 1
        - deriv zetaReg 1 * (Real.eulerMascheroniConstant : ℂ)) / zetaReg 1 ^ 2) 1 :=
    hasDerivAt_deriv_zetaReg_one.div hasDerivAt_zetaReg_one hzne
  have hqval : (-(2 * (stieltjesConstant1 : ℂ)) * zetaReg 1
      - deriv zetaReg 1 * (Real.eulerMascheroniConstant : ℂ)) / zetaReg 1 ^ 2
      = -(2 * (stieltjesConstant1 : ℂ)) - (Real.eulerMascheroniConstant : ℂ) ^ 2 := by
    rw [zetaReg_one, deriv_zetaReg_one]
    ring
  rw [hqval] at hq
  -- Assemble `G`.
  have hG : HasDerivAt logDerivZetaG
      (-(-(2 * (stieltjesConstant1 : ℂ)) - (Real.eulerMascheroniConstant : ℂ) ^ 2)
        + -(1 / (1 + 2 : ℂ) ^ 2) + -(1 / (1 + 4 : ℂ) ^ 2) + -(1 / (1 + 6 : ℂ) ^ 2)) 1 := by
    unfold logDerivZetaG
    exact ((hq.neg.add h2).add h4).add h6
  -- `logDerivZetaGext` agrees with `logDerivZetaG` on a neighbourhood of `1`.
  have hnbhd : logDerivZetaGext =ᶠ[nhds (1 : ℂ)] logDerivZetaG := by
    have hopen : IsOpen (({-2, -4, -6} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    have h1 : (1 : ℂ) ∈ (({-2, -4, -6} : Set ℂ)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨by norm_num, by norm_num, by norm_num⟩
    filter_upwards [hopen.mem_nhds h1] with s hs
    exact logDerivZetaGext_eq hs
  have hval : iteratedDeriv 1 (fun z : ℂ => logDerivZetaGext (1 + z)) 0
      = ((Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1 : ℝ) : ℂ)
        - (1 / 9 + 1 / 25 + 1 / 49) := by
    rw [iteratedDeriv_one, deriv_comp_const_add, add_zero, hnbhd.deriv_eq, hG.deriv]
    push_cast
    ring
  rw [logDerivZetaCoeff, hval,
    rpow_neg_natCast_sub_one (by norm_num : (0 : ℝ) < 3) 1,
    rpow_neg_natCast_sub_one (by norm_num : (0 : ℝ) < 5) 1,
    rpow_neg_natCast_sub_one (by norm_num : (0 : ℝ) < 7) 1]
  simp only [Complex.sub_re, Complex.ofReal_re, Nat.factorial_one, Nat.cast_one]
  norm_num
  ring

/-- **`0.15 ≤ a_1 ≤ 0.20`.**

### Summary of Proof
Rewrite by the exact identity `logDerivZetaCoeff_one` (`a_1 = γ² + 2γ₁`) and apply
`stieltjes_combo_numeric_bounds`, whose two halves are proved separately (the upper one via the
Euler–Maclaurin bracket `Definitions.stieltjesSeqHi`).

### Lean Notes
**Why a numeric input on `a_1` is unavoidable for the `n = 1 → 2` antitone step.** That step needs
`2a_2 ≤ a_1`. Claim 1 gives `a_2 ≤ 0.0601974`, hence `2a_2 ≤ 0.1203948`, but only
`a_1 ≥ 0.0858049`, which does not reach it.

Nor does any sharper use of the same Cauchy data. The naive route would need boundary max
`M ≤ 0.41168` at radius `7`, where the truth is `≈ 0.590`. The *correlated* route — bounding the
single functional `g_1 + 2g_2 = (2πi)^{-1}∮G(z)(z+2)z^{-3}dz` in one go, rather than bounding
`g_1`, `g_2` separately and adding — gives `|g_1+2g_2| ≤ 0.0874666` against a requirement of
`≤ 0.0756143`, still short by about 14%. Enlarging the radius makes it worse: the requirement
`M(R) ≤ 0.0756·R` reads `M(7) ≤ 0.529` (actual `0.590`) and `M(8) ≤ 0.605` (actual `≈ 0.744`).

Only `n = 1 → 2` needs this; `n = 0 → 1` is closed by `logDerivZetaCoeff_zero` with no numeric
input at all.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the "one can check the first few terms
through direct computations" step of claim 2's proof.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_one`, `stieltjes_combo_numeric_bounds`.
**Used by:** `logDerivZetaCoeff_two_mul_succ_le_all`, `neg_logDeriv_zeta_lt_one_div`. -/
theorem logDerivZetaCoeff_one_bounds :
    0.15 ≤ logDerivZetaCoeff 1 ∧ logDerivZetaCoeff 1 ≤ 0.20 := by
  rw [logDerivZetaCoeff_one]
  exact stieltjes_combo_numeric_bounds

/-- **The antitone step `2·a_{n+1} ≤ a_n`, for every `n ≥ 0`.**

### Summary of Proof
Three cases, matching the tex's "the `a_n 2^n` are a decreasing sequence for `n ≥ 2`, one can
check the first few terms through direct computations".

* `n ≥ 2`: `logDerivZetaCoeff_two_mul_succ_le`, from claim 1 alone.
* `n = 1`: claim 1's upper bound on `a_2` against `logDerivZetaCoeff_one_bounds`' lower bound on
  `a_1`.
* `n = 0`: claim 1's upper bound on `a_1` with `logDerivZetaCoeff_zero` (`a_0 = γ`) and Mathlib's
  `Real.one_half_lt_eulerMascheroniConstant`, giving `2a_1 ≤ 0.4 < 1/2 < γ = a_0`.

### Lean Notes
This closes the tex's appeal to direct computation, and covers `n = 0` as well, which is what
licenses the `N = 0` instance of `logderzetabound`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2's proof.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `logDerivZetaCoeff_one_bounds`,
`logDerivZetaCoeff_two_mul_succ_le`, `logDerivZetaCoeff_zero`, `rpow_neg_natCast`,
`rpow_neg_natCast_sub_one`.
**Used by:** `logDerivZetaCoeff_div_succ_lt`, `logDerivZetaCoeff_mul_pow_succ_le_all`. -/
theorem logDerivZetaCoeff_two_mul_succ_le_all (n : ℕ) :
    2 * logDerivZetaCoeff (n + 1) ≤ logDerivZetaCoeff n := by
  match n with
  | 0 =>
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    have h1 := logDerivZetaCoeff_one_bounds.2
    rw [logDerivZetaCoeff_zero]
    norm_num at h1 ⊢
    linarith
  | 1 =>
    have h2 := abs_le.mp (logDerivZetaCoeff_bound (n := 2) (by norm_num))
    have hup : logDerivZetaCoeff 2
        ≤ ((3:ℝ) ^ (-((2:ℕ):ℝ) - 1) + (5:ℝ) ^ (-((2:ℕ):ℝ) - 1) + (7:ℝ) ^ (-((2:ℕ):ℝ) - 1))
          + 0.6 * 7 ^ (-((2:ℕ):ℝ)) := by linarith [h2.2]
    rw [rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3),
        rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5),
        rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7),
        rpow_neg_natCast (by norm_num : (0:ℝ) < 7)] at hup
    norm_num at hup
    have h1 := logDerivZetaCoeff_one_bounds.1
    norm_num at h1
    linarith
  | (m + 2) => exact logDerivZetaCoeff_two_mul_succ_le (n := m + 2) (by omega)

/-- **`a_{n+1}·x^{n+1} ≤ a_n·x^n` for every `n ≥ 0`** and `0 ≤ x ≤ 2`.

### Summary of Proof
As `logDerivZetaCoeff_mul_pow_succ_le`, but drawing on
`logDerivZetaCoeff_two_mul_succ_le_all` so that the `x = 2` endpoint is available at every `n`,
not only `n ≥ 2`. Scale by `x ≤ 2` using positivity of `a_{n+1}`, then multiply by `x^n ≥ 0`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2 — the decreasing-terms hypothesis of
the alternating-series argument, here in the full range the tex's `n ≥ 2` version leaves to
"direct computations".

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_pos`,
`logDerivZetaCoeff_two_mul_succ_le_all`.
**Used by:** `logDerivZetaCoeff_antitone`. -/
theorem logDerivZetaCoeff_mul_pow_succ_le_all {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (n : ℕ) :
    logDerivZetaCoeff (n + 1) * x ^ (n + 1) ≤ logDerivZetaCoeff n * x ^ n := by
  have hpos : 0 < logDerivZetaCoeff (n + 1) := logDerivZetaCoeff_pos (by omega)
  have hstep : logDerivZetaCoeff (n + 1) * x ≤ logDerivZetaCoeff n := by
    nlinarith [logDerivZetaCoeff_two_mul_succ_le_all n]
  have hxn : (0:ℝ) ≤ x ^ n := by positivity
  calc logDerivZetaCoeff (n + 1) * x ^ (n + 1)
      = (logDerivZetaCoeff (n + 1) * x) * x ^ n := by rw [pow_succ]; ring
    _ ≤ logDerivZetaCoeff n * x ^ n := mul_le_mul_of_nonneg_right hstep hxn

/-- **`fun n => a_n·x^n` is antitone on all of `ℕ`,** for `0 ≤ x ≤ 2`.

### Summary of Proof
`antitone_nat_of_succ_le` applied to `logDerivZetaCoeff_mul_pow_succ_le_all`.

### Lean Notes
This is exactly the hypothesis Mathlib's `Antitone.alternating_series_le_tendsto` and
`Antitone.tendsto_le_alternating_series` require, so it is the form in which claim 2's
decreasing-terms condition is consumed. Holding on *all* of `ℕ` rather than from `n = 2` is what
admits the `N = 0` instance of `logderzetabound`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2's "this being an alternating series"
step.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_mul_pow_succ_le_all`.
**Used by:** `logderzetabound_claim_two`, `neg_logDeriv_zeta_lt_one_div`. -/
theorem logDerivZetaCoeff_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Antitone (fun n => logDerivZetaCoeff n * x ^ n) :=
  antitone_nat_of_succ_le fun n => logDerivZetaCoeff_mul_pow_succ_le_all hx0 hx2 n

/-- **The antitone step is STRICT for `n ≥ 2`:** `2·a_{n+1} < a_n`.

### Summary of Proof
Identical to `logDerivZetaCoeff_two_mul_succ_le`, and from claim 1 alone: the same two-sided
bounds, the same reduction to `npow`, and the same final linear step — the arithmetic simply has
room to spare. Writing `n = m+2` and `A = 3^{-m}`, `B = 5^{-m}`, `C = 7^{-m}`, claim 1 gives

    a_{m+2} - 2·a_{m+3}  ≥  (1/81)A + (3/625)B - (164/12005)C,

and since `0 < C ≤ B` and `C ≤ A` (the hypotheses `i3`, `i5`, `hw` below) that is at least
`(423568/121550625)·C > 0`. Verified in `Code/verify_strict_antitone_step.py`.

### Lean Notes
**Why a separate strict version is needed, and why only for `n ≥ 2`.** Claim 2 asserts `<` where
Mathlib's alternating-series lemmas give `≤`, and closing that gap needs one strictly decreasing
step among the tail terms. The natural route — `a_{n+1}·x < a_n` — is *non-strict* at the endpoint
`x = 2`, where it reads `a_{n+1}·2 ≤ 2a_{n+1} ≤ a_n`; so strictness has to come from the
coefficient inequality itself.

It is genuinely unavailable at `n = 0, 1`: there claim 1's `0.6·7^{-n}` error term swamps the
margin, and `logDerivZetaCoeff_two_mul_succ_le_all` has to fall back on the exact values `a_0 = γ`
and the certified `a_1 = γ² + 2γ₁`. That is not a problem for claim 2, which only ever needs the
strict step at indices `≥ 2` — see `logderzetabound_claim_two`, which applies it at `2N+2` and
`2N+3`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2's "the `a_n2^n` are a decreasing
sequence for `n ≥ 2`" step, here with the strictness the alternating-series argument needs.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `rpow_neg_natCast`,
`rpow_neg_natCast_sub_one`.
**Used by:** `logDerivZetaCoeff_mul_pow_succ_lt`. -/
theorem logDerivZetaCoeff_two_mul_succ_lt {n : ℕ} (hn : 2 ≤ n) :
    2 * logDerivZetaCoeff (n + 1) < logDerivZetaCoeff n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hu := abs_le.mp (logDerivZetaCoeff_bound (n := m + 3) (by omega))
  have hl := abs_le.mp (logDerivZetaCoeff_bound (n := m + 2) (by omega))
  have hup : logDerivZetaCoeff (m + 2 + 1)
      ≤ ((3:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1) + (5:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1)
          + (7:ℝ) ^ (-((m + 3 : ℕ) : ℝ) - 1)) + 0.6 * 7 ^ (-((m + 3 : ℕ) : ℝ)) := by
    have : m + 2 + 1 = m + 3 := by omega
    rw [this]; linarith [hu.2]
  have hlo : ((3:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1) + (5:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1)
        + (7:ℝ) ^ (-((m + 2 : ℕ) : ℝ) - 1)) - 0.6 * 7 ^ (-((m + 2 : ℕ) : ℝ))
      ≤ logDerivZetaCoeff (m + 2) := by linarith [hl.1]
  rw [rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5),
      rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7),
      rpow_neg_natCast (by norm_num : (0:ℝ) < 7)] at hup hlo
  norm_num at hup hlo
  have h3m : (0:ℝ) < 3 ^ m := by positivity
  have h5m : (0:ℝ) < 5 ^ m := by positivity
  have h7m : (0:ℝ) < 7 ^ m := by positivity
  have hp3 : (3:ℝ) ^ m ≤ 7 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have hp5 : (5:ℝ) ^ m ≤ 7 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have e34 : ((3:ℝ) ^ (m + 4))⁻¹ = (1 / 81) * ((3:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e33 : ((3:ℝ) ^ (m + 3))⁻¹ = (1 / 27) * ((3:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e54 : ((5:ℝ) ^ (m + 4))⁻¹ = (1 / 625) * ((5:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e53 : ((5:ℝ) ^ (m + 3))⁻¹ = (1 / 125) * ((5:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e74 : ((7:ℝ) ^ (m + 4))⁻¹ = (1 / 2401) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e73 : ((7:ℝ) ^ (m + 3))⁻¹ = (1 / 343) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have e72 : ((7:ℝ) ^ (m + 2))⁻¹ = (1 / 49) * ((7:ℝ) ^ m)⁻¹ := by
    rw [pow_add]; field_simp; norm_num
  have i3 : ((7:ℝ) ^ m)⁻¹ ≤ ((3:ℝ) ^ m)⁻¹ := by gcongr
  have i5 : ((7:ℝ) ^ m)⁻¹ ≤ ((5:ℝ) ^ m)⁻¹ := by gcongr
  have hw : (0:ℝ) < ((7:ℝ) ^ m)⁻¹ := by positivity
  rw [e34, e54, e74, e73] at hup
  rw [e33, e53, e73, e72] at hlo
  linarith

/-- **`a_{n+1}·x^{n+1} < a_n·x^n` strictly, for `0 < x ≤ 2` and `n ≥ 2`.**

### Summary of Proof
From `logDerivZetaCoeff_two_mul_succ_lt`: `a_{n+1}·x ≤ 2a_{n+1} < a_n` (the first step using
`a_{n+1} > 0` and `x ≤ 2`), then multiply by `x^n > 0`, which needs `0 < x` rather than the
`0 ≤ x` of the non-strict version.

### Lean Notes
This is the strict companion of `logDerivZetaCoeff_mul_pow_succ_le_all`, restricted to `n ≥ 2`
because that is where the coefficient step is strict; see
`logDerivZetaCoeff_two_mul_succ_lt`'s notes.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_pos`,
`logDerivZetaCoeff_two_mul_succ_lt`.
**Used by:** `logderzetabound_claim_two`. -/
theorem logDerivZetaCoeff_mul_pow_succ_lt {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) {n : ℕ}
    (hn : 2 ≤ n) :
    logDerivZetaCoeff (n + 1) * x ^ (n + 1) < logDerivZetaCoeff n * x ^ n := by
  have hpos : 0 < logDerivZetaCoeff (n + 1) := logDerivZetaCoeff_pos (by omega)
  have hstep : logDerivZetaCoeff (n + 1) * x < logDerivZetaCoeff n := by
    nlinarith [logDerivZetaCoeff_two_mul_succ_lt hn]
  have hxn : (0:ℝ) < x ^ n := by positivity
  calc logDerivZetaCoeff (n + 1) * x ^ (n + 1)
      = (logDerivZetaCoeff (n + 1) * x) * x ^ n := by rw [pow_succ]; ring
    _ < logDerivZetaCoeff n * x ^ n := mul_lt_mul_of_pos_right hstep hxn

/-! ### The remaining `HasSum` identification, and a first consequence -/

/-- **The quotient rule for `zetaReg`:** `zetaReg'(s)/zetaReg(s) = 1/(s-1) + ζ'(s)/ζ(s)` away
from the pole, whenever `ζ(s) ≠ 0`.

### Summary of Proof
`zetaReg s = (s-1)ζ(s)` for `s ≠ 1`, so logarithmic differentiation splits the quotient into the
pole's contribution `1/(s-1)` and `ζ`'s own logarithmic derivative. Concretely the product rule
gives `zetaReg'(s) = ζ(s) + (s-1)ζ'(s)`; dividing by `zetaReg s = (s-1)ζ(s)` and cancelling is
then `field_simp`, using `s - 1 ≠ 0` and `ζ(s) ≠ 0`.

### Lean Notes
`zetaReg` is a `Function.update` of `fun s => (s-1) * ζ s` at the single point `1`, so it only
*agrees* with that product away from `1`. The derivative is therefore taken through
`Filter.EventuallyEq.deriv_eq`, with the neighbourhood supplied by `isOpen_ne.mem_nhds hs` — the
complement of `{1}` is open. Differentiability of `ζ` at `s` comes from Mathlib's
`differentiableAt_riemannZeta`, which needs exactly `s ≠ 1`.

This is step 4 of `hasSum_logDerivZetaCoeff`'s assembly: it is what converts `G`'s `zetaReg`-form
back into the `-ζ'/ζ` of that statement.

### References
tex: implicit in the proof of `Lemma \ref{lemma:logderzetabound}` (Lemma 38), where the `1/z` term
of the Laurent expansion is separated from `ζ'/ζ` without comment.

### Dependencies
**Depends on:** `zetaReg`, `zetaReg_eq_of_ne`.
**Used by:** `hasSum_logDerivZetaCoeff`. -/
theorem logDeriv_zetaReg_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv zetaReg s / zetaReg s = 1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hzd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have hev : zetaReg =ᶠ[nhds s] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw using zetaReg_eq_of_ne hw
  have hd1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hprod : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := hd1.mul hzd.hasDerivAt
  have hderiv : deriv zetaReg s = 1 * riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hev.deriv_eq]; exact hprod.deriv
  rw [hderiv, zetaReg_eq_of_ne hs]
  field_simp

/-- **The Laurent series converges:** `Σ (-1)ⁿ a_n xⁿ = 1/x + ζ'/ζ(1+x)` for `x ∈ (0,2]`.

### Summary of Proof
The tex takes this for granted — it simply *writes* the Laurent expansion
`-ζ'/ζ(1+z) = 1/z + Σ (-1)^{n+1} a_n zⁿ` as the definition of the `a_n` and proceeds. In Lean the
`a_n` are defined instead through Cauchy's estimate on `G`, so their identification with the
actual series coefficients has to be proved; that identification is the analytic core of claims
2 and 3.

The proof assembles four steps.

1. `Complex.hasSum_taylorSeries_on_ball` applied to `fun z => logDerivZetaGext (1+z)` on
   `Metric.ball 0 7`, giving `HasSum (fun n => (n!)⁻¹ • zⁿ • iteratedDeriv n G(1+·) 0) (G(1+z))`.
   The `DifferentiableOn` hypothesis comes from `logDerivZetaGext_diffContOnCl` restricted along
   `ball7_subset_box`.
2. Subtract `hasSum_patch_series`, valid for `‖z‖ < 3` and so covering `x ∈ (0,2]`. Since
   `logDerivZetaCoeff` is *defined* as `G`'s Taylor coefficient plus the explicit
   `3^{-n-1}+5^{-n-1}+7^{-n-1}`, this difference is exactly `(-1)ⁿ aₙ xⁿ` termwise.
3. Take real parts with `Complex.hasSum_re`, legitimate because
   `logDerivZetaCoeff_taylor_coeff_real` gives `(iteratedDeriv n G(1+·) 0).im = 0`.
4. Rewrite the resulting value with `logDeriv_zetaReg_eq`, converting `G`'s `zetaReg`-form back
   into `1/x + ζ'/ζ(1+x)`.

The patch terms cancel exactly: `G(1+x) = -(zetaReg'/zetaReg)(1+x) + 1/(x+3) + 1/(x+5) + 1/(x+7)`,
so subtracting `G` from the patch series leaves precisely `(zetaReg'/zetaReg)(1+x)`.

### Lean Notes
**Real parts are taken at the level of `HasSum`, not of the value.** Using `Complex.hasSum_re`
rather than `Complex.hasSum_ofReal` avoids ever needing `ζ'/ζ(1+x)` to be real — which is true by
Schwarz reflection but would be extra work. The statement's `.re` is then exactly what the
transfer produces.

Two small frictions, both in the termwise identity:
* Mathlib's Taylor series uses `•`, discharged by `simp only [smul_eq_mul]`.
* `ring` cannot simplify `(-1)ⁿ·(-1)ⁿ⁺¹ = -1` with a symbolic exponent, so the final step splits
  on `Nat.even_or_odd n` and rewrites with `Even.neg_one_pow`/`Odd.neg_one_pow`.

The `3^{-n-1}` of `logDerivZetaCoeff` are `Real.rpow`, while `hasSum_patch_series` produces
`((3:ℂ)^(n+1))⁻¹`; `rpow_neg_natCast_sub_one` bridges them.

Claim 2's bracketing follows from `Antitone.alternating_series_le_tendsto` and
`Antitone.tendsto_le_alternating_series`, which match the `range (2*N)` / `range (2*N+1)` shape
verbatim after the sign flip `(-1)^{n+1} a_n xⁿ = -(-1)ⁿ (a_n xⁿ)`;
`neg_logDeriv_zeta_lt_one_div` carries out exactly that comparison in the `N = 0` case.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the displayed Laurent series defining the
`a_n`.

**Independent numeric check.**
`Code/indep_mpmath_lemma37.py` block [D]: with `a_n` from a Cauchy integral, `Σ (-1)ⁿ aₙ xⁿ`
matches `1/x + ζ'/ζ(1+x)` at `x = 1/2, 1, 2` to the truncation error (61 terms).

### Dependencies
**Depends on:** `ball7_subset_box`, `hasSum_patch_series`, `logDerivZetaCoeff`,
`logDerivZetaCoeff_taylor_coeff_real`, `logDerivZetaGext`, `logDerivZetaGext_diffContOnCl`,
`logDerivZetaGext_eq`, `logDeriv_zetaReg_eq`, `rpow_neg_natCast_sub_one`.
**Used by:** `hasSum_logDerivZetaCoeff_integrated`, `logderzetabound_claim_two`,
`neg_logDeriv_zeta_lt_one_div`. -/
theorem hasSum_logDerivZetaCoeff {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    HasSum (fun n : ℕ => (-1:ℝ) ^ n * (logDerivZetaCoeff n * x ^ n))
      (1 / x + (deriv riemannZeta ((1:ℂ) + x) / riemannZeta ((1:ℂ) + x)).re) := by
  have hznorm : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hz7 : (x : ℂ) ∈ Metric.ball (0:ℂ) 7 := by
    rw [Metric.mem_ball, dist_zero_right, hznorm]; linarith
  have hz3 : ‖(x : ℂ)‖ < 3 := by rw [hznorm]; linarith
  have hxc : ((1:ℂ) + (x:ℂ)).re = 1 + x := by simp
  have hne1 : (1:ℂ) + (x:ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hxc] at this
    simp at this
    linarith
  have hre1 : (1:ℝ) ≤ ((1:ℂ) + (x:ℂ)).re := by rw [hxc]; linarith
  have hzne : riemannZeta ((1:ℂ) + (x:ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
  have hnot : (1:ℂ) + (x:ℂ) ∉ ({-2, -4, -6} : Set ℂ) := by
    intro hmem
    rcases hmem with h | h | h <;>
      · have := congrArg Complex.re h
        rw [hxc] at this
        norm_num at this
        linarith
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => logDerivZetaGext (1 + w))
      (Metric.ball (0:ℂ) 7) :=
    (logDerivZetaGext_diffContOnCl.mono (fun w hw => ball7_subset_box hw)).differentiableOn
  have hT := Complex.hasSum_taylorSeries_on_ball hdiff hz7
  have hP := hasSum_patch_series hz3
  have hpatch : (1 / ((x:ℂ) + 3) + 1 / ((x:ℂ) + 5) + 1 / ((x:ℂ) + 7))
      - logDerivZetaGext (1 + (x:ℂ))
      = deriv zetaReg (1 + (x:ℂ)) / zetaReg (1 + (x:ℂ)) := by
    rw [logDerivZetaGext_eq hnot]
    unfold logDerivZetaG
    ring_nf
  have hcomb := hP.sub hT
  rw [hpatch, logDeriv_zetaReg_eq hne1 hzne] at hcomb
  have hre := Complex.hasSum_re hcomb
  have hvalue : ((1:ℂ) / ((1 + (x:ℂ)) - 1)
        + deriv riemannZeta (1 + (x:ℂ)) / riemannZeta (1 + (x:ℂ))).re
      = 1 / x + (deriv riemannZeta ((1:ℂ) + x) / riemannZeta ((1:ℂ) + x)).re := by
    have h1 : (1:ℂ) + (x:ℂ) - 1 = (x:ℂ) := by ring
    rw [h1, Complex.add_re]
    congr 1
    rw [show (1:ℂ)/(x:ℂ) = ((1/x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hvalue] at hre
  refine hre.congr_fun ?_
  intro n
  have hD : iteratedDeriv n (fun w : ℂ => logDerivZetaGext (1 + w)) 0
      = ((iteratedDeriv n (fun w : ℂ => logDerivZetaGext (1 + w)) 0).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [logDerivZetaCoeff_taylor_coeff_real n]
  have key : (-1:ℂ) ^ n * (x:ℂ) ^ n *
        (((3:ℂ) ^ (n + 1))⁻¹ + ((5:ℂ) ^ (n + 1))⁻¹ + ((7:ℂ) ^ (n + 1))⁻¹) -
      ((n.factorial : ℂ))⁻¹ • (((x:ℂ) - 0) ^ n •
        iteratedDeriv n (fun w : ℂ => logDerivZetaGext (1 + w)) 0)
      = (((-1:ℝ) ^ n * (logDerivZetaCoeff n * x ^ n) : ℝ) : ℂ) := by
    rw [hD]
    unfold logDerivZetaCoeff
    rw [rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 3) n,
        rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 5) n,
        rpow_neg_natCast_sub_one (by norm_num : (0:ℝ) < 7) n]
    simp only [smul_eq_mul, sub_zero]
    push_cast
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, (he.add_one).neg_one_pow]; ring
    · rw [ho.neg_one_pow, (ho.add_one).neg_one_pow]; ring
  rw [key, Complex.ofReal_re]

/-- **`-ζ'/ζ(1+x) < 1/x` for `0 < x ≤ 2`.**

### Summary of Proof
The `N = 0` instance of claim 2's upper bound, where the partial sum is **empty**. Since the
alternating series `Σ(-1)^{n+1}a_n xⁿ` has a *negative* leading term, the empty partial sum `1/x`
is already a valid upper bound.

Unlocked precisely by the `n = 0` antitone step (`logDerivZetaCoeff_antitone`), which lets the
alternating-series comparison start at `n = 0` rather than `n = 2`. Strictness comes from running
the comparison at `k = 1` rather than `k = 0`: that gives `a_0 - a_1x ≤ L`, and `a_0 = γ > 1/2`
while `a_1x ≤ 0.2·2 = 0.4`, so `L ≥ γ - 0.4 > 0` strictly.

### Lean Notes
Via claim 3's FTC step this also yields `log ζ(1+x) > -log x`, i.e. `ζ(1+x) > 1/x`.

The tex states this case too: its `\sum_{n=0}^{2N-1}` form at `N = 0` has an empty upper sum,
under the stated convention that "an upper index of `-1` denotes the empty sum".

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2 at `N = 0`.

### Dependencies
**Depends on:** `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff`, `logDerivZetaCoeff_antitone`,
`logDerivZetaCoeff_one_bounds`, `logDerivZetaCoeff_pos`, `logDerivZetaCoeff_zero`.
**Used by:** none — recorded as the cleanest consequence of the `N = 0` case. -/
theorem neg_logDeriv_zeta_lt_one_div {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    -(deriv riemannZeta ((1:ℂ) + x) / riemannZeta ((1:ℂ) + x)).re < 1 / x := by
  have hsum := hasSum_logDerivZetaCoeff hx0 hx2
  have hanti := logDerivZetaCoeff_antitone hx0.le hx2
  have hk := hanti.alternating_series_le_tendsto hsum.tendsto_sum_nat 1
  rw [show 2 * 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ] at hk
  simp only [Finset.range_zero, Finset.sum_empty, pow_zero, pow_one, one_mul, mul_one] at hk
  have h0 : logDerivZetaCoeff 0 = Real.eulerMascheroniConstant := logDerivZetaCoeff_zero
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h1 := logDerivZetaCoeff_one_bounds.2
  have h1pos : 0 < logDerivZetaCoeff 1 := logDerivZetaCoeff_pos le_rfl
  have hx1 : logDerivZetaCoeff 1 * x ≤ 0.4 := by nlinarith
  rw [h0] at hk
  norm_num at hk hx1 h1 ⊢
  linarith

/-- **`Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2**, for every `N ≥ 0`:
`1/x + Σ_{n<2N+1} (-1)^{n+1}a_n xⁿ  <  -ζ'/ζ(1+x)  <  1/x + Σ_{n<2N} (-1)^{n+1}a_n xⁿ`.

### Summary of Proof
The series `Σ (-1)ⁿ a_n xⁿ` is alternating with `a_n xⁿ` antitone
(`logDerivZetaCoeff_antitone`) and summable to `1/x + ζ'/ζ(1+x)`
(`hasSum_logDerivZetaCoeff`), so consecutive partial sums bracket the limit — Mathlib's
`Antitone.alternating_series_le_tendsto` and `Antitone.tendsto_le_alternating_series`.

### Lean Notes
**Strictness, which those two lemmas do not give.** They yield `≤`; the statement asserts `<`.
The gap is closed by taking the Mathlib brackets **two steps further out** than the goal needs,
at `k = N+2` rather than `k = N`, and paying for the difference with one strictly decreasing
step. Writing `S_m` for the partial sum and `f n = a_n xⁿ`:

    S_{2N+4} = S_{2N} + (f(2N) - f(2N+1)) + (f(2N+2) - f(2N+3))  ≤  limit,
    S_{2N+5} = S_{2N+1} - (f(2N+1) - f(2N+2)) - (f(2N+3) - f(2N+4)),  limit ≤ S_{2N+5}.

In each line the first bracket is `≥ 0` by antitonicity and the second is `> 0` by
`logDerivZetaCoeff_mul_pow_succ_lt`, applied at `2N+2` and `2N+3` respectively.

**Why the indices are `2N+2` and `2N+3`, not `2N` and `2N+1`.** The strict step is available only
for `n ≥ 2` — at `n = 0,1` claim 1's error term is too coarse and the non-strict result has to
lean on the exact `a_0 = γ` and certified `a_1`. Reaching two steps out makes every index used
at least `2`, uniformly in `N`, so no `N = 0` special case is needed.

A general "an alternating series with nonzero first term has nonzero sum" argument does *not*
work here: for a merely antitone non-negative sequence the tail can vanish identically (take
`f = 1,1,0,0,…`), so some genuinely strict decrease is required, which is what
`logDerivZetaCoeff_two_mul_succ_lt` supplies.

`neg_logDeriv_zeta_lt_one_div` proves the `N = 0` upper bound separately by an ad-hoc numeric
route; this theorem subsumes it.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2.

### Dependencies
**Depends on:** `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff`, `logDerivZetaCoeff_antitone`,
`logDerivZetaCoeff_mul_pow_succ_lt`.
**Used by:** `logderzetabound`. -/
theorem logderzetabound_claim_two {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (N : ℕ) :
    1 / x + ∑ n ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ (n + 1) * logDerivZetaCoeff n * x ^ n
        < -(deriv riemannZeta ((1 : ℂ) + x) / riemannZeta ((1 : ℂ) + x)).re
      ∧ -(deriv riemannZeta ((1 : ℂ) + x) / riemannZeta ((1 : ℂ) + x)).re
        < 1 / x + ∑ n ∈ Finset.range (2 * N),
            (-1 : ℝ) ^ (n + 1) * logDerivZetaCoeff n * x ^ n := by
  have hsum := hasSum_logDerivZetaCoeff hx0 hx2
  have hanti := logDerivZetaCoeff_antitone hx0.le hx2
  have hA := hanti.alternating_series_le_tendsto hsum.tendsto_sum_nat (N + 2)
  have hB := hanti.tendsto_le_alternating_series hsum.tendsto_sum_nat (N + 2)
  -- expand four terms off the front of each Mathlib bracket
  have hexp : ∀ (m : ℕ) (g : ℕ → ℝ), ∑ i ∈ Finset.range (m + 4), g i
      = (∑ i ∈ Finset.range m, g i) + g m + g (m + 1) + g (m + 2) + g (m + 3) := by
    intro m g
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
  rw [show 2 * (N + 2) = 2 * N + 4 by ring, hexp] at hA
  rw [show 2 * (N + 2) + 1 = 2 * N + 1 + 4 by ring, hexp] at hB
  -- the four alternating signs
  have hev : (-1 : ℝ) ^ (2 * N) = 1 := by rw [pow_mul]; norm_num
  have hs1 : (-1 : ℝ) ^ (2 * N + 1) = -1 := by rw [pow_succ, hev]; ring
  have hs2 : (-1 : ℝ) ^ (2 * N + 2) = 1 := by rw [pow_succ, hs1]; ring
  have hs3 : (-1 : ℝ) ^ (2 * N + 3) = -1 := by rw [pow_succ, hs2]; ring
  have hs4 : (-1 : ℝ) ^ (2 * N + 4) = 1 := by rw [pow_succ, hs3]; ring
  simp only [hev, hs1, hs2, hs3, hs4, one_mul, neg_one_mul] at hA hB
  -- antitone gives the non-strict brackets, the strict step the positive ones
  have hd0 := hanti (show 2 * N ≤ 2 * N + 1 by omega)
  have hd1 := hanti (show 2 * N + 1 ≤ 2 * N + 2 by omega)
  have hp2 := logDerivZetaCoeff_mul_pow_succ_lt hx0 hx2 (n := 2 * N + 2) (by omega)
  have hp3 := logDerivZetaCoeff_mul_pow_succ_lt hx0 hx2 (n := 2 * N + 3) (by omega)
  simp only at hd0 hd1
  -- relate the goal's `(-1)^{n+1}` sums to Mathlib's `(-1)^n` ones
  have hconv : ∀ m : ℕ,
      (∑ n ∈ Finset.range m, (-1 : ℝ) ^ (n + 1) * logDerivZetaCoeff n * x ^ n)
        + (∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * (logDerivZetaCoeff i * x ^ i)) = 0 := by
    intro m
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [pow_succ]; ring
  have hc0 := hconv (2 * N)
  have hc1 := hconv (2 * N + 1)
  constructor
  · linarith
  · linarith

/-- **Positivity of every Laurent coefficient**, including `n = 0`.

### Summary of Proof
`logDerivZetaCoeff_pos` covers `n ≥ 1`; `n = 0` is `a_0 = γ` (`logDerivZetaCoeff_zero`) together
with Mathlib's `Real.one_half_lt_eulerMascheroniConstant`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2's positivity input.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_pos`, `logDerivZetaCoeff_zero`.
**Used by:** `logDerivZetaCoeff_div_succ_lt`. -/
theorem logDerivZetaCoeff_pos_all (n : ℕ) : 0 < logDerivZetaCoeff n := by
  match n with
  | 0 =>
    rw [logDerivZetaCoeff_zero]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  | (m + 1) => exact logDerivZetaCoeff_pos (by omega)

/-- **The integrated terms `a_n·x^{n+1}/(n+1)` decrease strictly, at every `n`.**

### Summary of Proof
`a_{n+1}·x ≤ a_n` (from `logDerivZetaCoeff_two_mul_succ_le_all` with `x ≤ 2`) gives
`a_{n+1}x^{n+2} ≤ a_n x^{n+1}`, and then the weights do the rest: dividing by `n+2` against
`n+1` is a strict loss because `a_n x^{n+1} > 0`.

### Lean Notes
**Unlike claim 2's strict step, this one is strict at *every* `n`, not just `n ≥ 2`.** The
`1/(n+1)` weights supply the strict decrease on their own, so no appeal to
`logDerivZetaCoeff_two_mul_succ_lt` — and hence no `n = 0,1` exception — is needed. That is why
claim 3 can use Mathlib's brackets one step out (`k = N+1`) where claim 2 needs two.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 3.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_pos_all`,
`logDerivZetaCoeff_two_mul_succ_le_all`.
**Used by:** `logDerivZetaCoeff_div_succ_antitone`, `logderzetabound_claim_three`. -/
theorem logDerivZetaCoeff_div_succ_lt {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (n : ℕ) :
    logDerivZetaCoeff (n + 1) * x ^ (n + 1 + 1) / ((n : ℝ) + 1 + 1)
      < logDerivZetaCoeff n * x ^ (n + 1) / ((n : ℝ) + 1) := by
  have hpos : 0 < logDerivZetaCoeff (n + 1) := logDerivZetaCoeff_pos_all (n + 1)
  have hstep : logDerivZetaCoeff (n + 1) * x ≤ logDerivZetaCoeff n := by
    nlinarith [logDerivZetaCoeff_two_mul_succ_le_all n]
  have hxp : (0:ℝ) < x ^ (n + 1) := by positivity
  have hprod : (0:ℝ) < logDerivZetaCoeff n * x ^ (n + 1) :=
    mul_pos (logDerivZetaCoeff_pos_all n) hxp
  have hnum : logDerivZetaCoeff (n + 1) * x ^ (n + 1 + 1)
      ≤ logDerivZetaCoeff n * x ^ (n + 1) := by
    calc logDerivZetaCoeff (n + 1) * x ^ (n + 1 + 1)
        = (logDerivZetaCoeff (n + 1) * x) * x ^ (n + 1) := by rw [pow_succ]; ring
      _ ≤ logDerivZetaCoeff n * x ^ (n + 1) := mul_le_mul_of_nonneg_right hstep hxp.le
  have hd1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hd2 : (0:ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [div_lt_div_iff₀ hd2 hd1]
  nlinarith

/-- **Antitonicity of the integrated terms**, the hypothesis claim 3's alternating-series
argument needs.

### Summary of Proof
`antitone_nat_of_succ_le` applied to `logDerivZetaCoeff_div_succ_lt`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 3.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_div_succ_lt`.
**Used by:** `logderzetabound_claim_three`. -/
theorem logDerivZetaCoeff_div_succ_antitone {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    Antitone (fun n : ℕ => logDerivZetaCoeff n * x ^ (n + 1) / ((n : ℝ) + 1)) :=
  antitone_nat_of_succ_le fun n => by
    have h := logDerivZetaCoeff_div_succ_lt hx0 hx2 n
    push_cast at h ⊢
    linarith

/-- **A crude geometric bound on the Laurent coefficients: `|a_n| ≤ 1.3·3^{-n}`.** Only the
decay rate matters here (it makes `Σ a_n y^n` and its termwise integral converge uniformly on
`|y| < 5/2`); the sharp bound is `logDerivZetaCoeff_bound`.

### Summary of Proof
`n = 0`: `a_0 = γ < 2/3 < 1.3` (`logDerivZetaCoeff_zero`,
`Real.eulerMascheroniConstant_lt_two_thirds`).
`n ≥ 1`: `logDerivZetaCoeff_bound` gives `|a_n − (3^{-n-1}+5^{-n-1}+7^{-n-1})| ≤ 0.6·7^{-n}`, and
each of the four terms is at most a constant times `3^{-n}`
(`3^{-n-1} = 3^{-n}/3`, `5^{-n-1} ≤ 3^{-n}/5`, `7^{-n-1} ≤ 3^{-n}/7`, `7^{-n} ≤ 3^{-n}`), so
`|a_n| ≤ (1/3 + 1/5 + 1/7 + 0.6)·3^{-n} < 1.28·3^{-n}`.

### Lean Notes
The `rpow` exponents `-(n:ℝ)-1` and `-(n:ℝ)` are converted to `((c:ℝ)^(n+1))⁻¹`, `((c:ℝ)^n)⁻¹`
with `Real.rpow_neg`/`Real.rpow_natCast` before the inequality is closed by `nlinarith`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the convergence remark for the Laurent
series of `ζ'/ζ` at `s = 1`.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `logDerivZetaCoeff_zero`.
**Used by:** `hasSum_logDerivZetaCoeff_integrated`. -/
theorem abs_logDerivZetaCoeff_le (n : ℕ) : |logDerivZetaCoeff n| ≤ 1.3 * (1 / 3 : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := Real.one_half_lt_eulerMascheroniConstant
    have h2 := Real.eulerMascheroniConstant_lt_two_thirds
    rw [logDerivZetaCoeff_zero, pow_zero, mul_one, abs_of_pos (by linarith)]
    linarith
  · have h := logDerivZetaCoeff_bound hn
    have e3 : (3 : ℝ) ^ (-(n : ℝ) - 1) = ((3 : ℝ) ^ (n + 1 : ℕ))⁻¹ := by
      rw [show (-(n : ℝ) - 1) = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
    have e5 : (5 : ℝ) ^ (-(n : ℝ) - 1) = ((5 : ℝ) ^ (n + 1 : ℕ))⁻¹ := by
      rw [show (-(n : ℝ) - 1) = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
    have e7 : (7 : ℝ) ^ (-(n : ℝ) - 1) = ((7 : ℝ) ^ (n + 1 : ℕ))⁻¹ := by
      rw [show (-(n : ℝ) - 1) = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
    have e7' : (7 : ℝ) ^ (-(n : ℝ)) = ((7 : ℝ) ^ n)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [e3, e5, e7, e7'] at h
    have hq : (1 / 3 : ℝ) ^ n = ((3 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
    have h5le : ((5 : ℝ) ^ (n + 1 : ℕ))⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ / 5 := by
      rw [pow_succ, mul_inv, div_eq_mul_inv]
      have : ((5 : ℝ) ^ n)⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    have h7le : ((7 : ℝ) ^ (n + 1 : ℕ))⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ / 7 := by
      rw [pow_succ, mul_inv, div_eq_mul_inv]
      have : ((7 : ℝ) ^ n)⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    have h7le' : ((7 : ℝ) ^ n)⁻¹ ≤ ((3 : ℝ) ^ n)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
    have h3eq : ((3 : ℝ) ^ (n + 1 : ℕ))⁻¹ = ((3 : ℝ) ^ n)⁻¹ / 3 := by
      rw [pow_succ, mul_inv, div_eq_mul_inv]
    rw [hq]
    have htri := abs_sub_abs_le_abs_sub (logDerivZetaCoeff n)
      (((3 : ℝ) ^ (n + 1 : ℕ))⁻¹ + ((5 : ℝ) ^ (n + 1 : ℕ))⁻¹ + ((7 : ℝ) ^ (n + 1 : ℕ))⁻¹)
    have hpos : 0 ≤ ((3 : ℝ) ^ (n + 1 : ℕ))⁻¹ + ((5 : ℝ) ^ (n + 1 : ℕ))⁻¹
        + ((7 : ℝ) ^ (n + 1 : ℕ))⁻¹ := by positivity
    rw [abs_of_nonneg hpos] at htri
    have hinv : 0 < ((3 : ℝ) ^ n)⁻¹ := by positivity
    nlinarith [h, htri, h3eq, h5le, h7le, h7le', hinv]

/-- **The integrated Laurent series** — the analytic ingredient of claim 3:
`Σ (-1)ⁿ a_n x^{n+1}/(n+1) = log‖ζ(1+x)‖ + log x` for `0 < x ≤ 2`.

### Summary of Proof
"Match derivatives", phrased on `Φ(y) := Re G(1+y) + log y − Σ (-1)ⁿ a_n y^{n+1}/(n+1)` where
`G = LSeries GTerm` is the logarithm of `ζ` on `Re s > 1` (`Definitions`), so that
`Re G(1+y) = log‖ζ(1+y)‖` (`GTerm_LSeries_re_eq_log_norm`).

* *Termwise differentiation.* With `|a_n| ≤ 1.3·3^{-n}` (`abs_logDerivZetaCoeff_le`) the
  derivative series `Σ (-1)ⁿ a_n y^n` is dominated by the summable `1.3·(5/6)^n` on
  `t = (-5/2, 5/2)`, and the series vanishes at `y = 0`; `hasDerivAt_tsum_of_isPreconnected`
  gives `d/dy Σ (-1)ⁿ a_n y^{n+1}/(n+1) = Σ (-1)ⁿ a_n y^n` on `t`, and
  `summable_of_summable_hasDerivAt_of_isPreconnected` the summability at every `y ∈ t`.
* *`Φ' = 0` on `(0,2)`.* `d/dy Re G(1+y) = Re(ζ'/ζ(1+y))` (`G_hasDerivAt` composed with
  `y ↦ 1+y`, then `HasDerivAt.real_of_complex`), `d/dy log y = 1/y`, and
  `hasSum_logDerivZetaCoeff` says `Σ (-1)ⁿ a_n y^n = 1/y + Re(ζ'/ζ(1+y))`.
* *`Φ` is constant on `(0,2)`* (`IsOpen.exists_is_const_of_deriv_eq_zero`), and the constant is
  `0`: as `y → 0⁺`, `Re G(1+y) + log y = log‖((1+y)−1)·ζ(1+y)‖ → log 1 = 0` by
  `riemannZeta_residue_one`, while the series tends to its value `0` at `y = 0` (it is
  differentiable there).
* *`x = 2`.* `Φ` is continuous at `2` (each piece has a derivative there), so `Φ(2)` is the limit
  of `Φ = 0` along `(0,2)` (`tendsto_nhds_unique` on `𝓝[Ioo 0 2] 2`, which is non-trivial since
  `2 ∈ closure (Ioo 0 2)`).

`Φ(x) = 0` and the summability at `x` give the `HasSum`.

### Lean Notes
The proof deliberately avoids `zetaReg`: the singular endpoint `y = 0` is
handled by the residue limit `riemannZeta_residue_one` alone. The constancy lemma needs an *open*
preconnected set, hence the separate continuity step at the endpoint `x = 2`; the derivative
identity is available only on `(0,2]` because `hasSum_logDerivZetaCoeff` is.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), the FTC step of claim 3's proof.

**Independent numeric check.**
`Code/indep_mpmath_lemma37.py` block [D]: with the `a_n` from the Cauchy integral, both this
sum and `hasSum_logDerivZetaCoeff`'s agree with their stated values at `x = 1/2, 1, 2` to the
truncation error (`10⁻³⁰` at `x = 1`, `10⁻¹¹` at `x = 2` with 61 terms) — the signs and the
`+ log x` are as stated.

### Dependencies
**Depends on:** `hasSum_logDerivZetaCoeff`, `logDerivZetaCoeff`, `abs_logDerivZetaCoeff_le`,
`Definitions.GTerm`, `Definitions.G_hasDerivAt`, `Definitions.GTerm_LSeries_re_eq_log_norm`.
**Used by:** `logderzetabound_claim_three`. -/
theorem hasSum_logDerivZetaCoeff_integrated {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (logDerivZetaCoeff n * x ^ (n + 1) / ((n : ℝ) + 1)))
      (Real.log ‖riemannZeta ((1 : ℂ) + x)‖ + Real.log x) := by
  set g : ℕ → ℝ → ℝ := fun n y => (-1 : ℝ) ^ n * (logDerivZetaCoeff n * y ^ (n + 1) / ((n : ℝ) + 1))
    with hg
  set g' : ℕ → ℝ → ℝ := fun n y => (-1 : ℝ) ^ n * (logDerivZetaCoeff n * y ^ n) with hg'
  set t : Set ℝ := Set.Ioo (-(5 / 2) : ℝ) (5 / 2) with ht
  have hu : Summable (fun n : ℕ => 1.3 * (5 / 6 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hgderiv : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * y ^ n) y :=
      hasDerivAt_pow (n + 1) y
    have h2 := ((h1.const_mul (logDerivZetaCoeff n)).div_const ((n : ℝ) + 1)).const_mul
      ((-1 : ℝ) ^ n)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    refine h2.congr_deriv ?_
    simp only [hg']
    push_cast
    field_simp
  have hgbound : ∀ n y, y ∈ t → ‖g' n y‖ ≤ 1.3 * (5 / 6 : ℝ) ^ n := by
    intro n y hy
    simp only [hg', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    have hy' : |y| ≤ 5 / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc |logDerivZetaCoeff n| * |y| ^ n
        ≤ (1.3 * (1 / 3 : ℝ) ^ n) * (5 / 2 : ℝ) ^ n :=
          mul_le_mul (abs_logDerivZetaCoeff_le n) (pow_le_pow_left₀ (abs_nonneg _) hy' n)
            (by positivity) (by positivity)
      _ = 1.3 * (5 / 6 : ℝ) ^ n := by rw [mul_assoc, ← mul_pow]; norm_num
  have h0mem : (0 : ℝ) ∈ t := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun n => g n 0) := by
    have : (fun n => g n 0) = fun _ => (0 : ℝ) := by
      funext n; simp [hg]
    rw [this]; exact summable_zero
  have hderiv : ∀ y ∈ t, HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := fun y hy =>
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hgderiv hgbound h0mem hg0 hy
  have hsummable : ∀ y ∈ t, Summable (fun n => g n y) := fun y hy =>
    summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hgderiv
      hgbound h0mem hg0 hy
  -- the function `Φ` with zero derivative on `(0, 2)`
  set Φ : ℝ → ℝ := fun y => (LSeries GTerm ((1 : ℂ) + y)).re + Real.log y - ∑' n, g n y with hΦ
  have hΦderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 2, HasDerivAt Φ 0 y := by
    intro y hy
    have hyt : y ∈ t := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hre : 1 < ((1 : ℂ) + (y : ℂ)).re := by simpa using hy.1
    have hG : HasDerivAt (fun w : ℂ => LSeries GTerm (1 + w))
        (deriv riemannZeta ((1 : ℂ) + y) / riemannZeta ((1 : ℂ) + y)) (y : ℂ) := by
      have := (G_hasDerivAt hre).comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_add 1)
      rw [mul_one] at this
      exact this
    have hGre : HasDerivAt (fun y : ℝ => (LSeries GTerm ((1 : ℂ) + y)).re)
        (deriv riemannZeta ((1 : ℂ) + y) / riemannZeta ((1 : ℂ) + y)).re y := hG.real_of_complex
    have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.1.ne'
    have hsum : ∑' n, g' n y
        = 1 / y + (deriv riemannZeta ((1 : ℂ) + y) / riemannZeta ((1 : ℂ) + y)).re :=
      (hasSum_logDerivZetaCoeff hy.1 hy.2.le).tsum_eq
    have := (hGre.add hlog).sub (hderiv y hyt)
    rw [hsum] at this
    refine this.congr_deriv ?_
    rw [one_div]; ring
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy => (hΦderiv y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hΦderiv y hy).deriv)
  -- `c = 0`: the limit `y → 0⁺`
  have hres : Tendsto (fun y : ℝ => Real.log ‖((1 : ℂ) + y - 1) * riemannZeta ((1 : ℂ) + y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (1 : ℂ) + y) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℝ => (1 : ℂ) + y) (𝓝 (0 : ℝ)) (𝓝 ((1 : ℂ) + ((0 : ℝ) : ℂ))) :=
          (continuous_const.add Complex.continuous_ofReal).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        intro h
        have := congrArg Complex.re h
        simp only [add_re, one_re, ofReal_re, add_eq_left] at this
        exact (ne_of_gt (Set.mem_Ioi.mp hy)) this
    have h2 := riemannZeta_residue_one.comp h1
    have h3 : Tendsto (fun y : ℝ => ‖((1 : ℂ) + y - 1) * riemannZeta ((1 : ℂ) + y)‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have := h2.norm
      simpa using this
    have h4 := (Real.continuousAt_log one_ne_zero).tendsto.comp h3
    rw [Real.log_one] at h4
    exact h4
  have hlogeq : ∀ᶠ (y : ℝ) in 𝓝[>] (0 : ℝ),
      Real.log ‖((1 : ℂ) + y - 1) * riemannZeta ((1 : ℂ) + y)‖
        = (LSeries GTerm ((1 : ℂ) + y)).re + Real.log y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := Set.mem_Ioi.mp hy
    have hre : 1 < ((1 : ℂ) + (y : ℂ)).re := by simpa using hy0
    have hz : riemannZeta ((1 : ℂ) + y) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
    rw [GTerm_LSeries_re_eq_log_norm hre, show (1 : ℂ) + y - 1 = (y : ℂ) by ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
      Real.log_mul hy0.ne' (norm_ne_zero_iff.mpr hz), add_comm]
  have htsum0 : Tendsto (fun y => ∑' n, g n y) (𝓝[>] (0 : ℝ)) (𝓝 (∑' n, g n 0)) :=
    ((hderiv 0 h0mem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hg00 : ∑' n, g n 0 = 0 := by
    have : (fun n => g n 0) = fun _ => (0 : ℝ) := by funext n; simp [hg]
    rw [this, tsum_zero]
  have hΦlim : Tendsto Φ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hres.congr' hlogeq).sub htsum0
    rw [hg00, sub_zero] at this
    exact this
  have hΦc : Tendsto Φ (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with y hy
    exact (hc y hy).symm
  have hc0 : c = 0 := tendsto_nhds_unique hΦc hΦlim
  -- conclude for `x ∈ (0, 2]`
  have hΦx : Φ x = 0 := by
    rcases lt_or_eq_of_le hx2 with hlt | heq
    · rw [hc x ⟨hx0, hlt⟩, hc0]
    · subst heq
      -- continuity of `Φ` at `2`, then the limit from the left
      have hΦcont : ContinuousAt Φ 2 := by
        have hre : 1 < ((1 : ℂ) + ((2 : ℝ) : ℂ)).re := by norm_num
        have hG : HasDerivAt (fun w : ℂ => LSeries GTerm (1 + w))
            (deriv riemannZeta ((1 : ℂ) + (2 : ℝ)) / riemannZeta ((1 : ℂ) + (2 : ℝ)))
            ((2 : ℝ) : ℂ) := by
          have := (G_hasDerivAt hre).comp ((2 : ℝ) : ℂ) ((hasDerivAt_id ((2 : ℝ) : ℂ)).const_add 1)
          rw [mul_one] at this
          exact this
        have hGre := hG.real_of_complex
        have h2t : (2 : ℝ) ∈ t := ⟨by norm_num, by norm_num⟩
        exact ((hGre.continuousAt.add (Real.continuousAt_log (by norm_num))).sub
          (hderiv 2 h2t).continuousAt)
      have hlim1 : Tendsto Φ (𝓝[Set.Ioo (0 : ℝ) 2] 2) (𝓝 (Φ 2)) :=
        hΦcont.tendsto.mono_left nhdsWithin_le_nhds
      have hlim2 : Tendsto Φ (𝓝[Set.Ioo (0 : ℝ) 2] 2) (𝓝 c) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hc y hy).symm
      have hne : (𝓝[Set.Ioo (0 : ℝ) 2] (2 : ℝ)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num)]
        exact ⟨by norm_num, le_rfl⟩
      rw [tendsto_nhds_unique hlim1 hlim2, hc0]
  have hxt : x ∈ t := ⟨by linarith, by linarith⟩
  have hsum := (hsummable x hxt).hasSum
  have hval : ∑' n, g n x = Real.log ‖riemannZeta ((1 : ℂ) + x)‖ + Real.log x := by
    have hre : 1 < ((1 : ℂ) + (x : ℂ)).re := by simpa using hx0
    have := hΦx
    simp only [hΦ] at this
    rw [GTerm_LSeries_re_eq_log_norm hre] at this
    linarith
  rw [hval] at hsum
  exact hsum

/-- **`Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 3**, for every `N ≥ 0`.

### Summary of Proof
Exactly claim 2's argument, run on the *integrated* series: the terms
`a_n x^{n+1}/(n+1)` are antitone (`logDerivZetaCoeff_div_succ_antitone`) and sum, with
alternating signs, to `log‖ζ(1+x)‖ + log x` (`hasSum_logDerivZetaCoeff_integrated`), so
consecutive partial sums bracket that value.

### Lean Notes
Two simplifications over claim 2. **No sign flip** — claim 3's summands already carry `(-1)ⁿ`,
matching Mathlib's convention, whereas claim 2's carry `(-1)^{n+1}`. And **only one step out**
is needed (`k = N+1`, not `N+2`), because `logDerivZetaCoeff_div_succ_lt` is strict at *every*
index, the `1/(n+1)` weights supplying the strict decrease that claim 2 had to extract from the
coefficients themselves.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 3.

### Dependencies
**Depends on:** `hasSum_logDerivZetaCoeff_integrated`, `logDerivZetaCoeff`,
`logDerivZetaCoeff_div_succ_antitone`, `logDerivZetaCoeff_div_succ_lt`.
**Used by:** `logderzetabound`, `RectangularBounds.logzeta_le_linear` (at `N = 0`). -/
theorem logderzetabound_claim_three {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (N : ℕ) :
    -Real.log x
        + ∑ n ∈ Finset.range (2 * N), (-1 : ℝ) ^ n * logDerivZetaCoeff n / (n + 1) * x ^ (n + 1)
        < Real.log ‖riemannZeta ((1 : ℂ) + x)‖
      ∧ Real.log ‖riemannZeta ((1 : ℂ) + x)‖
        < -Real.log x + ∑ n ∈ Finset.range (2 * N + 1),
            (-1 : ℝ) ^ n * logDerivZetaCoeff n / (n + 1) * x ^ (n + 1) := by
  have hsum := hasSum_logDerivZetaCoeff_integrated hx0 hx2
  have hanti := logDerivZetaCoeff_div_succ_antitone hx0 hx2
  have hA := hanti.alternating_series_le_tendsto hsum.tendsto_sum_nat (N + 1)
  have hB := hanti.tendsto_le_alternating_series hsum.tendsto_sum_nat (N + 1)
  have hexp : ∀ (m : ℕ) (g : ℕ → ℝ), ∑ i ∈ Finset.range (m + 2), g i
      = (∑ i ∈ Finset.range m, g i) + g m + g (m + 1) := by
    intro m g
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show 2 * (N + 1) = 2 * N + 2 by ring, hexp] at hA
  rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 2 by ring, hexp] at hB
  have hev : (-1 : ℝ) ^ (2 * N) = 1 := by rw [pow_mul]; norm_num
  have hs1 : (-1 : ℝ) ^ (2 * N + 1) = -1 := by rw [pow_succ, hev]; ring
  have hs2 : (-1 : ℝ) ^ (2 * N + 2) = 1 := by rw [pow_succ, hs1]; ring
  simp only [hev, hs1, hs2, one_mul, neg_one_mul] at hA hB
  have hp0 := logDerivZetaCoeff_div_succ_lt hx0 hx2 (2 * N)
  have hp1 := logDerivZetaCoeff_div_succ_lt hx0 hx2 (2 * N + 1)
  push_cast at hp0 hp1 hA hB
  have hconv : ∀ m : ℕ,
      (∑ n ∈ Finset.range m, (-1 : ℝ) ^ n * logDerivZetaCoeff n / (n + 1) * x ^ (n + 1))
        = ∑ i ∈ Finset.range m,
            (-1 : ℝ) ^ i * (logDerivZetaCoeff i * x ^ (i + 1) / ((i : ℝ) + 1)) := by
    intro m
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hconv (2 * N)]
  rw [hconv (2 * N + 1)]
  constructor
  · linarith
  · linarith

/-! ## The full three-claim `Lemma \ref{lemma:logderzetabound}` -/

/-- **`Lemma \ref{lemma:logderzetabound}` (Lemma 38), in full.** The coefficient bound (claim 1)
together with the two alternating-series bracket bounds (claims 2 and 3), for `x ∈ [0,2]` and
every `N ≥ 0`.

### Summary of Proof
Three claims, as in the tex.

* **Claim 1** follows Chirre–Helfgott's Lemma A.7, at radius `7` with the singularities at
  `1, -2, -4, -6` removed: bound `G`'s Taylor coefficients by the Cauchy integral formula, using
  the verified boundary bound `|G| < 6/10` on `|z| = 7`, then rearrange.
* **Claim 2** is "a simple consequence of this being an alternating series". The terms `a_n xⁿ`
  are positive — `a_0` is positive and the only negative term decreases at least as fast as the
  positive ones — and decreasing, so consecutive partial sums bracket the limit.
* **Claim 3** follows from claim 2 by the FTC argument
  `log ζ(1+x) = -log x + ∫₀ˣ (1/u + ζ'/ζ(1+u)) du`, integrating the bracket termwise.

### Lean Notes
Claim 1 is `logDerivZetaCoeff_bound`, claim 2 is `logderzetabound_claim_two` and claim 3 is
`logderzetabound_claim_three`; this statement is their conjunction.

**Why the hypothesis is `0 < x` and not `0 ≤ x`.** Claim 2 contains `1/x`, and Lean's `1/0 = 0`,
`0^0 = 1`, `0ⁿ = 0` (`n ≥ 1`), `Real.log 0 = 0` collapse each claim's two bounds onto each other
at `x = 0`, making the statement **false there**:

* **Claim 3, every `N`.** Every summand carries `x^{n+1}`, which vanishes at `x = 0`, so both
  sums are `0` and both sides are `-log 0 = 0`. The claim reads `0 < log‖ζ(1)‖ ∧ log‖ζ(1)‖ < 0`.
* **Claim 2, every `N ≥ 1`.** Only the `n = 0` term survives at `x = 0`, contributing `-a₀` to
  *both* `range (2N+1)` and `range (2N)` (the latter contains `0` as soon as `2N ≥ 1`). So both
  sides equal `-a₀` and the claim reads `-a₀ < R ∧ R < -a₀`.

Both are self-contradictory *independently of the junk values* Lean assigns to `ζ(1)` and
`deriv ζ 1` — no evaluation of those is needed. Requiring `0 < x` is what the mathematics
intends and costs nothing at the sole call site, `neg_logDeriv_zeta_bound_of_claim_two`, which
already has `0 < x`; the tex states the lemma for `x \in (0,2]` to match.

**Index convention: Lean and the tex agree.** The tex writes claim 2 as lower `∑_{n=0}^{2N}` /
upper `∑_{n=0}^{2N-1}`, and claim 3 as lower `∑_{n=0}^{2N-1}` / upper `∑_{n=0}^{2N}`, with the
convention that "an upper index of `-1` denotes the empty sum". In `Finset.range` terms those are
exactly the `range (2*N+1)` / `range (2*N)` and `range (2*N)` / `range (2*N+1)` used here.

Since these are `∀ N ≥ 0` statements, the `2N-1` form is strictly stronger than a `2N+1` one: it
recovers every `2N+1` instance at `N+1` and adds an `N = 0` instance, where the shorter sum is
**empty** and no truncated natural subtraction is involved. Hence no `1 ≤ N` hypothesis is
needed. The extra `N = 0` instance reads

* claim 2: `1/x - a_0 < -ζ'/ζ(1+x) < 1/x`,
* claim 3: `-log x < log ζ(1+x) < -log x + a_0·x`   (in particular `ζ(1+x) > 1/x`),

which is exactly what the `n = 0` antitone step unlocks.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), all three claims.
External: Chirre–Helfgott `\cite[Lemma A.7]{ChirreHelfgott2025}`, attributed there to A. Kalmynin
`\cite{Kalmynin2025}`.

### Dependencies
**Depends on:** `logDerivZetaCoeff`, `logDerivZetaCoeff_bound`, `logderzetabound_claim_two`,
`logderzetabound_claim_three`.
**Used by:** `neg_logDeriv_zeta_bound_of_claim_two`. -/
theorem logderzetabound {x : ℝ} (_hx0 : 0 < x) (_hx2 : x ≤ 2) {N : ℕ} :
    (∀ n, 1 ≤ n → |logDerivZetaCoeff n
        - ((3 : ℝ) ^ (-(n : ℝ) - 1) + (5 : ℝ) ^ (-(n : ℝ) - 1) + (7 : ℝ) ^ (-(n : ℝ) - 1))|
      ≤ 0.6 * 7 ^ (-(n : ℝ)))
      ∧ (1 / x + ∑ n ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ (n + 1) * logDerivZetaCoeff n * x ^ n
            < -(deriv riemannZeta ((1 : ℂ) + x) / riemannZeta ((1 : ℂ) + x)).re
          ∧ -(deriv riemannZeta ((1 : ℂ) + x) / riemannZeta ((1 : ℂ) + x)).re
            < 1 / x + ∑ n ∈ Finset.range (2 * N),
                (-1 : ℝ) ^ (n + 1) * logDerivZetaCoeff n * x ^ n)
      ∧ (-Real.log x
            + ∑ n ∈ Finset.range (2 * N), (-1 : ℝ) ^ n * logDerivZetaCoeff n / (n + 1) * x ^ (n + 1)
            < Real.log ‖riemannZeta ((1 : ℂ) + x)‖
          ∧ Real.log ‖riemannZeta ((1 : ℂ) + x)‖
            < -Real.log x + ∑ n ∈ Finset.range (2 * N + 1),
                (-1 : ℝ) ^ n * logDerivZetaCoeff n / (n + 1) * x ^ (n + 1)) := by
  exact ⟨fun n hn => logDerivZetaCoeff_bound hn, logderzetabound_claim_two _hx0 _hx2 N,
    logderzetabound_claim_three _hx0 _hx2 N⟩

/-- **The truncated Laurent estimate `-ζ'/ζ(1+x) < 1/x - γ + (γ²+2γ₁)x` on `(0, 2]`**, claim 2 of
`Lemma \ref{lemma:logderzetabound}` (Lemma 38) at `N = 1`.

### Summary of Proof
At `N = 1` the upper bound's shorter sum runs over `Finset.range (2*1) = {0,1}`, giving
`-ζ'/ζ(1+x) < 1/x - a_0 + a_1·x`. Substituting the two exact identities `a_0 = γ`
(`logDerivZetaCoeff_zero`) and `a_1 = γ² + 2γ₁` (`logDerivZetaCoeff_one`) turns the right-hand
side into `1/x - γ + (γ²+2γ₁)·x`.

### Lean Notes
The range `x ≤ 2` is inherited from `logderzetabound`, and is all any consumer needs:
`JensenBounds.c4IntegrandBound_abs_le` and `JensenBounds.integraloutside_bound_secondary` only
ever invoke the estimate with `x = ru ≤ 2` (for `ru > 2` they already reduce to `σ = 3` by
antitonicity).  Extending it to all `x > 0` would need a hand-checked window `[2, 2.37]` — see
the AM–GM remark in `Definitions.neg_logDeriv_zeta_re_antitone`'s docstring.

Through this theorem those two results — and, transitively, `A6`, `mainLittlewood` and
`Corollary \ref{cor:main-littlewood}` (Corollary 5) — rest on Lemma 38's two hypothesis fields,
`LaurentCertificate.logDerivZetaG_boundary_bound` and
`LiteratureInputs.riemannZeta_lowest_zero_height`.

### References
tex: `Lemma \ref{lemma:logderzetabound}` (Lemma 38), claim 2 at `N = 1`; used in the proof of
`Proposition \ref{prop:integraloutside}` (Proposition 15).

### Dependencies
**Depends on:** `logDerivZetaCoeff_one`, `logDerivZetaCoeff_zero`, `logderzetabound`,
`stieltjesConstant1`.
**Used by:** `JensenBounds.c4IntegrandBound_abs_le`,
`JensenBounds.integraloutside_bound_secondary`. -/
theorem neg_logDeriv_zeta_bound_of_claim_two {x : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) :
    -(deriv riemannZeta ((1 + x : ℝ) : ℂ) / riemannZeta ((1 + x : ℝ) : ℂ)).re
      < 1 / x - Real.eulerMascheroniConstant
        + (Real.eulerMascheroniConstant ^ 2 + 2 * stieltjesConstant1) * x := by
  have h := (logderzetabound (x := x) hx0 hx2 (N := 1)).2.1.2
  norm_num [Finset.sum_range_succ, logDerivZetaCoeff_zero, logDerivZetaCoeff_one] at h
  have hcast : ((1 + x : ℝ) : ℂ) = (1 : ℂ) + (x : ℂ) := by push_cast; ring
  -- `norm_num` above normalised `1/x` to `x⁻¹` in `h`; match it so `linarith` sees one atom.
  rw [hcast, one_div]
  linarith [h]
