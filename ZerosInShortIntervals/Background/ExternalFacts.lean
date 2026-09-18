/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Hypotheses
import ZerosInShortIntervals.Common.RealLogBounds

/-! # Facts imported from other sources

`ZerosInShortIntervals.tex` builds on a number of explicit bounds for `ζ` and `Γ`
proved elsewhere; these are recorded here with the originating reference, so that the rest of the
`ZerosInShortIntervals` development can be built on top of them. Each one's doc-comment gives the
`refs.bib` key of its source and, where it was checked against that source directly rather than
transcribed from the paper's citation alone, notes that check and any discrepancy it turned up.

We do *not* prove the external bounds here — the point of this file is to isolate exactly which
external inputs the paper's own arguments rely on. Each is a theorem whose body reads the
corresponding field of a hypothesis class: `Hypotheses.LiteratureInputs` for the twelve
literature bounds, and `BrentStirlingInputs` (declared below, after `logGammaAnalytic`, whose
statements it needs) for Brent's two Stirling expansions. A result depending on one of them says
so in its signature; the project contains no `axiom` and no `sorry`. The provenance discussion
lives here, on each theorem, and the class field carries a one-line pointer back.  That visibility
is what a registry submission requires: the axiom base of any result is readable off its signature.

Two declarations that carry the `[LiteratureInputs]` binder are proved rather than assumed:
`hiary_revers_half_line_bound`, derived from two of the bounds above it, and
`bellotti_wong_Lbound_le`, derived from `bellotti_wong_cor_1_3` together with the power-series
inequality of `Common.RealLogBounds`.

Two blocks are deliberately *outside* that section and so carry no hypothesis binder at all:
`exists_large_nat_cos_ge_half` together with `backlund_trick`, proved outright from Dirichlet's
approximation theorem, and the whole `logGammaAnalytic` development, proved outright from
Mathlib's `Complex.GammaSeq`. The first is load-bearing — it is what keeps
`Littlewood/ArgIntegrals.lean` free of hypothesis binders, which in turn is what makes
`arg_integrals` submittable on its own. See the comment above `exists_large_nat_cos_ge_half`.
-/

set_option linter.unusedSectionVars false

section
variable [LiteratureInputs]

/-- **Hiary–Patel–Yang's half-line bound, Eq. (3.23).** For `|t| > 10¹²`,
`|ζ(1/2+it)| ≤ 0.478013|t|^{1/6}log|t| + 3.853165|t|^{1/6} - 2.914229`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.hiary_eq_3_23`, recording an external result
verbatim. It is the sharper `t`-dependent-constant form of the subconvexity bound on the
critical line.

### Lean Notes
Recorded for completeness as one of the two inputs the source names, but not actually used: the
derivation of `hiary_revers_half_line_bound` below runs on `revers_remark31` instead, which is
sharper in the leading constant (`0.470795` against `0.478013`).

### References
External: Hiary–Patel–Yang, arXiv:2207.02366, `\cite[Eq. (3.23)]{HiaryPatelYang2024}`.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
theorem hiary_eq_3_23 {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.478013 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 3.853165 * |t| ^ (1 / 6 : ℝ) - 2.914229 :=
  LiteratureInputs.hiary_eq_3_23 ht

/-- **Revers' half-line bound, Remark 3.1.** For `|t| ≥ 7·10¹¹`,
`|ζ(1/2+it)| ≤ 0.470795|t|^{1/6}log|t| + 4.04972|t|^{1/6} - 21.5437`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.revers_remark31`, recording an external result
verbatim. It sharpens `hiary_eq_3_23`'s leading constant from `0.478013` to `0.470795`, at the
cost of a larger threshold in the second term.

### Lean Notes
This is the large-`|t|` half of `hiary_revers_half_line_bound`'s two-case derivation.

### References
External: Revers, arXiv:2602.05614, `\cite[Remark 3.1]{Revers2026}`.

### Dependencies
**Depends on:** none.
**Used by:** `hiary_revers_half_line_bound`. -/
theorem revers_remark31 {t : ℝ} (ht : (7 : ℝ) * 10 ^ (11 : ℕ) ≤ |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) - 21.5437 :=
  LiteratureInputs.revers_remark31 ht

/-- **Revers' headline subconvexity bound on the half-line.** For `3 ≤ |t|`,
`|ζ(1/2+it)| ≤ 0.611|t|^{1/6}log|t|`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.revers_subconvexity_bound`, recording an external
result verbatim. It is the improvement of `\cite{Revers2026}` over
`\cite[Theorem 1.1]{HiaryPatelYang2024}`'s `0.618`.

### Lean Notes
Unlike `hiary_revers_half_line_bound` (the sharper *asymptotic* form, better for large `|t|` and
worse for small `|t|`), this holds with a single clean constant across the whole line, which is
what `BackgroundZetaBounds.interpolated_bound_1b` needs as the `σ = 1/2` input to
Phragmén–Lindelöf.

The source's own prose ("recent claimed improvements to …", tex line 1249) flags this as a
*claimed* rather than fully-verified improvement. `BackgroundZetaBounds.interpolated_bound_1a`
anchors its `σ = 1/2` edge on Patel–Yang instead and so avoids the claim altogether; cases (1b)
and (1c) both rest on it — (1b) directly, (1c) through `hiary_revers_half_line_bound` — and the
three are stated side by side so that a consumer can see which `σ = 1/2` bound it inherits.

### References
External: Revers, arXiv:2602.05614, `\cite{Revers2026}`; contrasted
with Hiary–Patel–Yang, `\cite[Theorem 1.1]{HiaryPatelYang2024}`.
tex: quoted in the Appendix, `\S sec:background`.

### Dependencies
**Depends on:** none.
**Used by:** `hiary_revers_half_line_bound`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`. -/
theorem revers_subconvexity_bound {t : ℝ} (ht : 3 ≤ |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.611 * |t| ^ (1 / 6 : ℝ) * Real.log |t| :=
  LiteratureInputs.revers_subconvexity_bound ht

/-- **The half-line bound used in the Appendix — proved here, not assumed.** For `3 ≤ |t|`,
`|ζ(1/2+it)| < 0.470795|t|^{1/6}log|t| + 4.04972|t|^{1/6}`.

### Summary of Proof
The source states this for `|t| > 3` (tex line 1259), concluding it from
`\cite[Eq. (3.23)]{HiaryPatelYang2024}` and `\cite[Remark 3.1]{Revers2026}`.
Those two inputs are valid only for `|t| > 10¹²` resp. `|t| ≥ 7·10¹¹`, so on their own they
cannot cover the whole range.

What makes the conclusion work is an overlap. The *headline* bound `revers_subconvexity_bound`
(`0.611|t|^{1/6}log|t|`) already implies the displayed bound whenever
`0.611 log|t| ≤ 0.470795 log|t| + 4.04972`, i.e. whenever `log|t| ≤ 4.04972/0.140205 = 28.8842…`,
i.e. `|t| ≤ 3.50·10¹²`. Since `7·10¹¹ < 3.50·10¹²`, the large-`|t|` range of `revers_remark31`
and the small-`|t|` range of the headline bound **overlap**, so the two cases cover everything.

### Lean Notes
The case split is on `7·10¹¹ ≤ |t|`. The large branch is `revers_remark31` plus `linarith` (the
`-21.5437` is discarded). The small branch needs `log|t| < 28`, obtained by bounding
`7·10¹¹ < exp 28` via `2.7^28 ≤ (exp 1)^28 = exp 28` and `Real.exp_one_gt_d9`.

**Stated with `3 ≤ |t|`**, the closed form of the tex's `|t| > 3`: the small-`|t|` half runs on
`revers_subconvexity_bound`, which is itself available exactly from `3 ≤ |t|`, so the endpoint
comes for free.

### References
External: Hiary–Patel–Yang `\cite[Eq. (3.23)]{HiaryPatelYang2024}`; Revers
`\cite[Remark 3.1]{Revers2026}`.
tex: the Appendix's half-line bound, `\S sec:background`.

### Dependencies
**Depends on:** `revers_remark31`, `revers_subconvexity_bound`.
**Used by:** `interpolated_bound_1c`, `interpolated_bound_1c_tight`. -/
theorem hiary_revers_half_line_bound {t : ℝ} (ht : 3 ≤ |t|) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      < 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) := by
  have hpos : (0:ℝ) < |t| := by linarith
  have hX : (0:ℝ) < |t| ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hpos _
  rcases le_or_gt ((7 : ℝ) * 10 ^ (11 : ℕ)) |t| with hbig | hsmall
  · linarith [revers_remark31 hbig]
  · -- small range: the `0.611` headline bound already suffices, since `log|t| < 28`
    have hlog : Real.log |t| < 28 := by
      have hexp : ((7 : ℝ) * 10 ^ (11 : ℕ)) < Real.exp 28 := by
        have h27 : (2.7 : ℝ) ^ (28 : ℕ) ≤ Real.exp 28 := by
          calc (2.7 : ℝ) ^ (28 : ℕ) ≤ (Real.exp 1) ^ (28 : ℕ) := by
                apply pow_le_pow_left₀ (by norm_num)
                nlinarith [Real.exp_one_gt_d9]
            _ = Real.exp 28 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [h27]
      calc Real.log |t| < Real.log (Real.exp 28) :=
            Real.log_lt_log hpos (lt_trans hsmall hexp)
        _ = 28 := Real.log_exp 28
    nlinarith [revers_subconvexity_bound ht, hX, hlog]

/-- **Patel–Yang's explicit sub-Weyl bound.** For `t ≥ 3`,
`|ζ(1/2+it)| ≤ 66.7 t^{27/164}`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.patel_yang_subweyl_bound`, recording an external
result verbatim.

### Lean Notes
This is the `σ = 1/2` anchor of the alternative coefficient triple of
`Remark \ref{rem:altcoefficients}` (Remark 7),
`(v₀, v₀', v₀'') = (27/164, 0, log 66.7)`; the exponent `27/164` and constant `66.7` are exactly
`JensenScaleConstantsAlt.vCoeffAlt 0` and `vCoeffPPAlt 0`. The absence of a `log t` factor is why
that triple's `log log|t|` coefficient `v₀'` vanishes.

Stated for real `t ≥ 3`, not `|t| ≥ 3`: the reflection to negative `t` is handled downstream by
Schwarz reflection rather than being built into the hypothesis.

**Citation check.** Verified against the source PDF
(`PatelYang-2023-ExplicitSubWeylBoundZeta-arXiv.pdf`), Abstract.

### References
External: Patel–Yang, arXiv:2302.13444, Abstract, `\cite{PatelYang2024}`.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`. -/
theorem patel_yang_subweyl_bound {t : ℝ} (ht : 3 ≤ t) :
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 66.7 * t ^ (27 / 164 : ℝ) :=
  LiteratureInputs.patel_yang_subweyl_bound ht

/-- **Yang's explicit bound inside the critical strip.** For every integer `k ≥ 4` and `t ≥ 3`,
with `σ_k := 1 - k/(2^k-2)`, `|ζ(σ_k+it)| ≤ 1.546 t^{1/(2^k-2)} log t`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.yang_critical_strip_bound`, recording an external
result verbatim.

### Lean Notes
This is the source of the constant `log(1.546)` in `JensenScaleConstants.vCoeffPP`, and the
`σ_k` here is the point *near `1`*, matching `sigma`/`interpolated_bound_2`'s own convention. It
matches `ZerosInShortIntervals.tex` exactly (`σ_k := 1-k/(2^k-2)`, `k ≥ 4`), i.e.
`Equation \eqref{eq:sigmak}` (Equation 4).

**Citation check.** Verified against
`Yang-2024-ExplicitBoundsZetaCriticalStripZeroFreeRegion-arXiv.pdf` (Theorem 1.1, requiring
`k ≥ 4`) and against `Fiori-2026-PhragmenLindelofTheorem-JMAA.pdf`'s own "Second example" (§4.2),
which cites exactly this bound at `σ = 5/7 = 1-4/(2^4-2)`.

**Why `k ≥ 4` and not `k ≥ 3`.** The bound is Yang's, and Yang's Theorem 1.1 requires `k ≥ 4`;
`k = 3` would put `σ_k = 1/2`, which that theorem does not cover. The tex agrees: it states the
bound for `k ≥ 4` and special-cases the `σ = 1/2` anchor `vCoeffPP 0` to the sharper half-line
bound of `HIARY2024195`/`revers2026newimprovedexplicitestimate` instead, at the point
`1-k/(2^k-2)` as here.

### References
External: Yang, arXiv:2301.03165, Theorem 1.1, `\cite{Yang2024}`.
tex: `Equation \eqref{eq:sigmak}` (Equation 4) and the `v_k''` display following it.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`, `interpolated_bound_1c`, `interpolated_bound_1c_tight`,
`interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem yang_critical_strip_bound {k : ℕ} (hk : 4 ≤ k) {t : ℝ} (ht : 3 ≤ t) :
    ‖riemannZeta (1 - (k : ℝ) / (2 ^ k - 2) + t * Complex.I)‖
      ≤ 1.546 * t ^ ((1 : ℝ) / (2 ^ k - 2)) * Real.log t :=
  LiteratureInputs.yang_critical_strip_bound hk ht

/-- **Bellotti's Richert-type bound.** For `1/2 ≤ σ ≤ 1` and `|t| ≥ 3`,
`|ζ(σ+it)| ≤ 70.7 |t|^{4.438(1-σ)^{3/2}} (log|t|)^{2/3}`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.bellotti_richert_bound`, recording an external
result verbatim.

### Lean Notes
This is the hypothesis pattern used by `Proposition \ref{prop:Richert}` (Proposition 12) and
`Theorem \ref{thm:circularregions2}` (Theorem 18).

**Citation check.** Verified against the source PDF
(`Bellotti-2023-ZetaBoundsNewZeroFreeRegion-arXiv.pdf`), Abstract. The tex's own statement omits
the lower constraint `1/2 ≤ σ` present in Bellotti's theorem; it is restored here, so the Lean is
if anything more conservative than the source.

### References
External: Bellotti, arXiv:2306.10680, Abstract, `\cite{Bellotti2024}`.
tex: `Proposition \ref{prop:Richert}` (Proposition 12), `Theorem \ref{thm:circularregions2}`
(Theorem 18).

### Dependencies
**Depends on:** none.
**Used by:** `FcrZeta_boundary_le`, `zeta_envelope`. -/
theorem bellotti_richert_bound {σ t : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 3 ≤ |t|) :
    ‖riemannZeta (σ + t * Complex.I)‖
      ≤ 70.7 * |t| ^ (4.438 * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ) :=
  LiteratureInputs.bellotti_richert_bound hσ ht

/-- **Leong's explicit bound on `-log|ζ(1+it)|`.** For `2 ≤ |t|`,
`-log|ζ(1+it)| ≤ log log|t| + log 29.388`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.leong_log_zeta_one_bound`, recording an external
result verbatim.

### Lean Notes
Stated in the logarithmic form `-log‖ζ(1+it)‖ ≤ log log|t| + log 29.388`, which is the
exponentiated form of Leong's `|1/ζ(1+it)| ≤ 29.388 log t`; this is the shape the downstream
Jensen/Littlewood arguments consume directly. It supplies the `log log|T|` coefficient in
`C_{2,α,r}` of `Theorem \ref{thm:circularregions1}` (Theorem 16).

**Citation check.** Verified against `Leong-2024-ExplicitEstimatesLogDerivativeZeta-arXiv.pdf`:
the paper's Theorem 4 states, for `σ = 1` and `t ≥ 2`, `|1/ζ(1+it)| ≤ 29.388 log t`, matching the
constant `29.388` and hypothesis `2 ≤ |t|` used here exactly.

### References
External: Leong, arXiv:2405.04869, Theorem 4,
`\cite{Leong2024}`.
tex: used in the proof of `Theorem \ref{thm:circularregions1}` (Theorem 16).

### Dependencies
**Depends on:** none.
**Used by:** `circularregions1`, `circularregions1_tight`, `circularregions2`, `littlewoodshort`,
`littlewoodshort_tight`. -/
theorem leong_log_zeta_one_bound {t : ℝ} (ht : 2 ≤ |t|) :
    -Real.log (‖riemannZeta (1 + t * Complex.I)‖) ≤ Real.log (Real.log |t|) + Real.log 29.388 :=
  LiteratureInputs.leong_log_zeta_one_bound ht

end

/- Backlund's trick is proved outright, from Dirichlet's approximation theorem alone, so it is
kept outside the `[LiteratureInputs]` section above.  Everything from here to
`class BrentStirlingInputs` below is unconditional, and a consumer that uses only this block --
`ZerosInShortIntervals.Littlewood.ArgIntegrals` is the one that matters -- inherits no hypothesis
binder.  That is what keeps `arg_integrals` submittable on its own. -/

/-- **Arbitrarily large `N` with `cos (Nθ)` bounded away from zero.** For every angle `θ` and
every bound `m`, there is a natural number `N` with `m ≤ N`, `0 < N` and `1/2 ≤ cos (Nθ)`.

### Summary of Proof
Dirichlet's approximation theorem (`Real.exists_int_int_abs_mul_sub_le`), applied to
`ξ = θ/(2π)` with denominator bound `n = 6(m+1)`, gives integers `j`, `k` with `0 < k ≤ n` and
`|kξ - j| ≤ 1/(n+1)`. Scaling that approximation by `q = m+1` and setting `N := q·k` gives
`N ≥ q > m` (since `k ≥ 1`) together with
`|Nθ - (qj)·2π| = q·2π·|kξ - j| ≤ 2π(m+1)/(6(m+1)+1) < π/3`.
As `cos` is `2π`-periodic, even, and decreasing on `[0,π]`, this yields
`cos (Nθ) = cos |Nθ - (qj)·2π| ≥ cos (π/3) = 1/2`.

### Lean Notes
**No rational/irrational case split is needed.** Dirichlet's theorem holds for every real `ξ`,
and the "scale the approximation by `q`" step is what supplies arbitrarily *large* `N` uniformly
(Dirichlet alone only bounds `k` above by `n`). When `θ/π` is rational the same construction
simply lands on `cos = 1` exactly, so that case is subsumed rather than treated separately.

The constant `1/2` is arbitrary — any fixed positive lower bound would do; `1/2` is chosen only
because `Real.cos_pi_div_three` is on hand. What the consumer needs is that `cos (Nθ)` is
bounded away from `0`, which keeps `Real.log |cos (Nθ)|` bounded and, in particular, away from
the `Real.log 0 = 0` junk value that a vanishing cosine would produce.

### References
No tex counterpart. It is the number-theoretic core of Backlund's trick, isolated so that
`backlund_trick` below is pure algebra plus a squeeze.
External: Dirichlet's approximation theorem, via Mathlib's
`Real.exists_int_int_abs_mul_sub_le` (`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`).

### Dependencies
**Depends on:** none.
**Used by:** `backlund_trick`. -/
theorem exists_large_nat_cos_ge_half (θ : ℝ) (m : ℕ) :
    ∃ N : ℕ, m ≤ N ∧ 0 < N ∧ 1 / 2 ≤ Real.cos (N * θ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ' : Real.pi ≠ 0 := ne_of_gt hπ
  obtain ⟨j, k, hk0, -, hjk⟩ :=
    Real.exists_int_int_abs_mul_sub_le (θ / (2 * Real.pi)) (n := 6 * (m + 1)) (by omega)
  have hKpos : 0 < k.toNat := by omega
  have hKcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    have h : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk0.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  refine ⟨(m + 1) * k.toNat, ?_, Nat.mul_pos (Nat.succ_pos m) hKpos, ?_⟩
  · calc m ≤ m + 1 := Nat.le_succ m
      _ = (m + 1) * 1 := (mul_one _).symm
      _ ≤ (m + 1) * k.toNat := Nat.mul_le_mul_left _ hKpos
  · have hNcast : (((m + 1) * k.toNat : ℕ) : ℝ) = ((m : ℝ) + 1) * (k : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hKcast]
    have key : |((m : ℝ) + 1) * (k : ℝ) * θ - (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi)|
        ≤ Real.pi / 3 := by
      have heq : ((m : ℝ) + 1) * (k : ℝ) * θ - (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi)
          = (((m : ℝ) + 1) * (2 * Real.pi)) * ((k : ℝ) * (θ / (2 * Real.pi)) - (j : ℝ)) := by
        push_cast
        field_simp
      rw [heq, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1) * (2 * Real.pi))]
      have hb : |(k : ℝ) * (θ / (2 * Real.pi)) - (j : ℝ)| ≤ 1 / (6 * ((m : ℝ) + 1) + 1) := by
        refine hjk.trans_eq ?_
        push_cast
        ring
      calc (((m : ℝ) + 1) * (2 * Real.pi)) * |(k : ℝ) * (θ / (2 * Real.pi)) - (j : ℝ)|
          ≤ (((m : ℝ) + 1) * (2 * Real.pi)) * (1 / (6 * ((m : ℝ) + 1) + 1)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ Real.pi / 3 := by
            rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 6 * ((m : ℝ) + 1) + 1)]
            nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
    have hcosrw : Real.cos ((((m + 1) * k.toNat : ℕ) : ℝ) * θ)
        = Real.cos (((m : ℝ) + 1) * (k : ℝ) * θ
            - (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi)) := by
      rw [hNcast]
      conv_lhs =>
        rw [show ((m : ℝ) + 1) * (k : ℝ) * θ
            = (((m : ℝ) + 1) * (k : ℝ) * θ - (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi))
              + (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi) by ring]
      rw [Real.cos_add_int_mul_two_pi]
    rw [hcosrw, ← Real.cos_abs]
    calc (1 : ℝ) / 2 = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |((m : ℝ) + 1) * (k : ℝ) * θ
              - (((m + 1 : ℤ) * j : ℤ) : ℝ) * (2 * Real.pi)| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) key

/-- **Backlund's trick.** For `f` nonvanishing at `c+iT` and satisfying the single-value conjugate
identity `f(c-iT) = conj(f(c+iT))`, there is a sequence `N_m → ∞` of natural numbers with
`(1/N_m) log|F_{N_m}(c+iT)| → log|f(c+iT)|`, where `F_N(w) := ½(f(w+c+iT)^N + f(w+c-iT)^N)`.

### Summary of Proof
Write `a = f(c+iT)`, `R = ‖a‖ > 0` (from `hf0`) and `θ = arg a`, so `a = R e^{iθ}`. The
conjugate hypothesis gives `f(c-iT) = conj a`, hence `½(a^N + conj(a)^N) = Re(a^N)` is a REAL
number, equal to `R^N cos(Nθ)`. Therefore
`‖F_N(0)‖ = R^N |cos(Nθ)|` and, whenever `cos(Nθ) ≠ 0`,
`(1/N) log‖F_N(0)‖ = log R + (1/N) log|cos(Nθ)|`.
Since `log R = log‖f(c+iT)‖` is exactly the target, the whole statement reduces to choosing
`N_m → ∞` with `(1/N_m) log|cos(N_m θ)| → 0`. `exists_large_nat_cos_ge_half` supplies
`N_m ≥ m` with `cos(N_m θ) ≥ 1/2` (Dirichlet approximation to `θ/(2π)`); then
`|log|cos(N_m θ)|| ≤ log 2`, and dividing a bounded quantity by `N_m → ∞` gives `0`.

This is Hasanalizade–Shen–Wong's (HSW) argument with the intermediate normalisation removed: they
write `ζ(c+iT) = Re^{iθ}`, apply Dirichlet to `θ`, and conclude
`ζ(c+iT)^{N_m} f_{N_m}(c) → 1`.

### Lean Notes
**Both hypotheses are load-bearing; without either the statement is false.**

*`hconj`.* Over an arbitrary `f : ℂ → ℂ` carrying only `hf0` the conclusion fails: take `T ≠ 0`
and `f` sending `c + T*I ↦ 1` and everything else `↦ 2`. Then `a = 1 ≠ 0`, so `hf0` holds, but
`(1/N) log‖½(1^N + 2^N)‖ → log 2 ≠ 0 = log‖a‖`. What is assumed is the **single-value** identity
`hconj : f (c - T*I) = conj (f (c + T*I))` rather than a global `f(s̄) = conj(f(s))`: that is all
the proof uses, and it is what the source and the call site have. (Even weaker would do — only
`‖f(c-iT)‖ ≤ ‖f(c+iT)‖` is really needed for the inequality direction Theorem 31 consumes — but
`hconj` matches HSW and costs the call site nothing, since `arg_integrals` already carries the
global symmetry hypothesis `hf` and derives `hconj` from it.)

*`hf0`.* Without nonvanishing at `c + T*I` the statement fails too: if
`f (c + T * Complex.I) = 0` then `F_N(c) = ½ f(c - T*I)^N`, so
`(1/N) log‖F_N(c)‖ → log‖f(c - T*I)‖`, which need not equal
`log‖f(c+T*I)‖ = Real.log 0 = 0` (Lean's junk value). The real call site
(`c = 1`, `f = ζ`, via `arg_integrals`) discharges it with
`riemannZeta_ne_zero_of_one_le_re`.

**The target is `Nθ ≈ Mπ`, not `2Nθ ≈ (2M+1)π`.** Factoring `a^N` out of `a^N + b^N` leaves
`(b/a)^N`, and with `b/a = e^{-2iθ}` the factor `1 + (b/a)^N` *vanishes* exactly when
`2Nθ ≡ π (mod 2π)`. So the useful target is `2Nθ ≡ 0 (mod 2π)`, i.e. `Nθ ≈ Mπ` — which is what
`exists_large_nat_cos_ge_half` delivers.

**Junk values.** `Real.log (R^N · |cos(Nθ)|) = N log R + log|cos(Nθ)|` FAILS when `cos(Nθ) = 0`
(the left side is `Real.log 0 = 0`, the right side is not), so the splitting step is only ever
applied along the chosen sequence, where `cos(N_m θ) ≥ 1/2`.

**Citation check: confirmed**, read directly from
`HasanalizadeShenWong-2021-CountingZerosDedekindZeta-arXiv.pdf`. The sequence claim is a
proof-internal step of the cited proposition rather than its final statement. The paper's
**Lemma 3.3** — not Prop. 3.7, which states only the final `arg` bound for one fixed large `N` —
is exactly this claim: "For any `c > 1`, there is an infinite sequence of natural numbers `(N_m)`
such that `f_{N_m}(c) ≠ 0`". The `≠` is the paper's, as the surrounding argument requires: the
next sentence takes `log|f_{N_m}(c)|`, and HSW's construction gives `f_{N_m}(c) → 1/ζ_K(c) ≠ 0`.

That same lemma is what supplies the `F_{N_m}(0) ≠ 0` fact the tex's Jensen-formula step in
`thm:arg-integrals` needs. Here it comes for free from the construction and is the statement's
third conjunct.

HSW's own Prop. 3.2-vs-3.3 numbering is a red herring for locating this result: the Dedekind
paper's Lemma 3.3 is the real source regardless of which proposition the tex meant to cite.

### References
External: Hasanalizade–Shen–Wong, *Counting zeros of the Riemann zeta function*, J. Number Theory
235 (2022) 219–241; cited by the tex as `\cite[Prop. 3.3]{HasanalizadeShenWong2022}`, but see the
Lean Notes — the actual source is that paper's Lemma 3.3.
tex: used in the proof of `Theorem \ref{thm:arg-integrals}` (Theorem 31). The tex's proof invokes
the trick without restating the conjugate hypothesis, because Theorem 31's own hypotheses already
supply it: "Suppose `f` is analytic on the disc of radius `r` centered at `c+iT`, that
`\overline{f(s)} = f(\overline{s})` and that `f` has no zeros on the line connecting `σ₀+iT` to
`σ₁+iT`" (`ZerosInShortIntervals.tex` line 1074). Since `c ∈ [σ₀,σ₁]`, the point `c+iT`
lies on that line, so `f(c+iT) ≠ 0` comes with it. The tex is correct as written, and
`hconj`/`hf0` here are exactly what it assumes.

### Dependencies
**Depends on:** `exists_large_nat_cos_ge_half`.
**Used by:** `arg_integrals`. -/
theorem backlund_trick (f : ℂ → ℂ) (c T : ℝ) (hf0 : f (c + T * Complex.I) ≠ 0)
    (hconj : f (c - T * Complex.I) = (starRingEnd ℂ) (f (c + T * Complex.I))) :
    ∃ Ns : ℕ → ℕ, Filter.Tendsto Ns Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun m => (1 / (Ns m : ℝ)) *
          Real.log ‖(1 / 2 : ℂ) * (f (c + T * Complex.I) ^ (Ns m)
              + f (c - T * Complex.I) ^ (Ns m))‖)
        Filter.atTop (nhds (Real.log ‖f (c + T * Complex.I)‖)) ∧
      ∀ m : ℕ, (1 / 2 : ℂ) * (f (c + T * Complex.I) ^ (Ns m)
          + f (c - T * Complex.I) ^ (Ns m)) ≠ 0 := by
  set a : ℂ := f (c + T * Complex.I) with ha
  have hR : 0 < ‖a‖ := norm_pos_iff.mpr hf0
  -- Polar form: `Re (a ^ N) = ‖a‖ ^ N * cos (N * arg a)`.
  have hre : ∀ N : ℕ, (a ^ N).re = ‖a‖ ^ N * Real.cos (N * Complex.arg a) := by
    intro N
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
      show (N : ℂ) * ((Complex.arg a : ℂ) * Complex.I)
          = (((N : ℝ) * Complex.arg a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- `hconj` turns the symmetrised power into a real number, whose norm is `R ^ N |cos (Nθ)|`.
  have hnorm : ∀ N : ℕ,
      ‖(1 / 2 : ℂ) * (a ^ N + f (c - T * Complex.I) ^ N)‖
        = ‖a‖ ^ N * |Real.cos (N * Complex.arg a)| := by
    intro N
    rw [hconj, ← map_pow,
      show (1 / 2 : ℂ) * (a ^ N + (starRingEnd ℂ) (a ^ N)) = (((a ^ N).re : ℝ) : ℂ) by
        rw [Complex.add_conj]; push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, hre N, abs_mul,
      abs_of_nonneg (pow_nonneg (norm_nonneg a) N)]
  choose Ns hge hpos hcos using fun m : ℕ => exists_large_nat_cos_ge_half (Complex.arg a) m
  have hNs_atTop : Filter.Tendsto Ns Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hge Filter.tendsto_id
  refine ⟨Ns, hNs_atTop, ?_, ?_⟩
  swap
  · -- Nonvanishing, free from the construction: `cos (N_m θ) ≥ 1/2 > 0` and `‖a‖ > 0`, so the
    -- symmetrised power has norm `‖a‖ ^ N_m |cos (N_m θ)| ≥ ‖a‖ ^ N_m / 2 > 0`. The tex asserts
    -- this separately (\ref{thm:arg-integrals}, `F_N(0) ≠ 0`, cited to HSW Lemma 3.3); here it
    -- costs nothing, being already established inside the limit argument.
    intro m
    have hc2 : (0 : ℝ) < |Real.cos (Ns m * Complex.arg a)| :=
      abs_pos.mpr (by have := hcos m; intro h; rw [h] at this; norm_num at this)
    have hpos2 : (0 : ℝ) < ‖a‖ ^ (Ns m) * |Real.cos (Ns m * Complex.arg a)| :=
      mul_pos (pow_pos hR _) hc2
    refine norm_ne_zero_iff.mp ?_
    rw [hnorm (Ns m)]
    exact ne_of_gt hpos2
  -- Split the logarithm; legitimate because `cos (N_m θ) ≥ 1/2 > 0`.
  have hsplit : ∀ m : ℕ,
      Real.log ‖a‖ + (1 / (Ns m : ℝ)) * Real.log |Real.cos (Ns m * Complex.arg a)|
        = (1 / (Ns m : ℝ)) * Real.log ‖(1 / 2 : ℂ) * (a ^ (Ns m)
            + f (c - T * Complex.I) ^ (Ns m))‖ := by
    intro m
    have hNpos : (0 : ℝ) < (Ns m : ℝ) := by exact_mod_cast hpos m
    have hne : (Ns m : ℝ) ≠ 0 := ne_of_gt hNpos
    have hc2 : (0 : ℝ) < |Real.cos (Ns m * Complex.arg a)| :=
      abs_pos.mpr (by have := hcos m; intro h; rw [h] at this; norm_num at this)
    rw [hnorm (Ns m), Real.log_mul (by positivity) (ne_of_gt hc2), Real.log_pow]
    field_simp
  -- The correction term is `O(1/N_m)`, hence vanishes.
  have hzero : Filter.Tendsto
      (fun m : ℕ => (1 / (Ns m : ℝ)) * Real.log |Real.cos (Ns m * Complex.arg a)|)
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun m : ℕ => Real.log 2 / (Ns m : ℝ)) Filter.atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).comp hNs_atTop
    refine squeeze_zero_norm (fun m => ?_) hg
    have hNpos : (0 : ℝ) < (Ns m : ℝ) := by exact_mod_cast hpos m
    have h1 : (1 : ℝ) / 2 ≤ Real.cos (Ns m * Complex.arg a) := hcos m
    have h2 : Real.cos (Ns m * Complex.arg a) ≤ 1 := Real.cos_le_one _
    have habs : |Real.cos (Ns m * Complex.arg a)| = Real.cos (Ns m * Complex.arg a) :=
      abs_of_pos (by linarith)
    set L : ℝ := Real.log |Real.cos (Ns m * Complex.arg a)| with hL
    have hlog_le : L ≤ 0 := by
      rw [hL, habs]; exact Real.log_nonpos (by linarith) h2
    have hlog_ge : -Real.log 2 ≤ L := by
      rw [hL, habs, ← Real.log_inv]
      exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr (by linarith)
    have hbd : |L| ≤ Real.log 2 :=
      abs_le.mpr ⟨hlog_ge, by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]⟩
    calc ‖(1 / (Ns m : ℝ)) * L‖ = (1 / (Ns m : ℝ)) * |L| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos one_pos hNpos)]
      _ ≤ (1 / (Ns m : ℝ)) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hbd (le_of_lt (div_pos one_pos hNpos))
      _ = Real.log 2 / (Ns m : ℝ) := by ring
  have hmain : Filter.Tendsto
      (fun m : ℕ =>
        Real.log ‖a‖ + (1 / (Ns m : ℝ)) * Real.log |Real.cos (Ns m * Complex.arg a)|)
      Filter.atTop (nhds (Real.log ‖a‖)) := by
    simpa using tendsto_const_nhds.add hzero
  exact hmain.congr hsplit

/-! ## Brent's explicit Stirling expansions for `log Γ`

**Read this before using anything in this section.** Every expansion here is stated about
`logGammaAnalytic`, an *analytic* branch of `log Γ`, and never about `Complex.log ∘ Complex.Gamma`.
That is not fastidiousness: the principal-branch form is **inconsistent**.

Lean's `Complex.log` is the principal branch, so `Complex.log (Complex.Gamma z)` has imaginary
part in `(-π, π]`. The Stirling right-hand side's imaginary part grows like `(t/2)·log(t/2)`. An
equation between them therefore *forces* the remainder `R₂` to be a nonzero multiple of `2π`,
while `brent_stirling_remainder_bound` forces it below `≈ 10⁻⁵`. Measured at `z = 1/2 + it/2`,
the forced `‖R₂(z)‖` is an *exact* integer multiple of `2π` — the branch-cut signature:

    t = 10.5 → 1·2π      t = 20 → 2·2π      t = 100 → 23·2π      t = 1000 → 415·2π

against the bounds `6.64·10⁻⁵`, `9.70·10⁻⁶`, `7.79·10⁻⁸`, `7.79·10⁻¹¹`. Stated in that form the
expansion and its remainder bound would jointly prove `False` for every `z` of large `|Im z|`.
Substituting the analytic `log Γ` (mpmath's
`loggamma`, which does not wrap) at the same four points gives `1.91·10⁻⁵`, `2.78·10⁻⁶`,
`2.22·10⁻⁸`, `2.22·10⁻¹¹` — inside Brent's bound everywhere. So only the branch was wrong.

Brent flags the trap himself, in the paragraph of §2 defining `H*`: he takes `ln Γ` to be "an
analytic function on the cut-plane `ℂ \ (-∞, 0]`, such that `ln Γ(x) = log(Γ(x))` is real for
positive real `x`", and adds that "in a software implementation of the function `ln Γ(z)`, care
has to be taken because `ln Γ(z)` and `ln(Γ(z))` may differ by a multiple of `2πi`". Read directly
from the PDF.

**Everything else about these hypotheses is Brent's, verbatim** (read from the PDF): the
unshifted Eq. (2.1) form with the plain Bernoulli *number* `B₂`; the constant
`(1+√(2π))·B₄/(12z³)`, which is his Corollary 2.2 `|Rₖ(z)/Tₖ(z)| < 1 + √(πk)` at `k = 2` with
`T₂(z) = B₄/(12z³)`; and the shifted Eq. (3.4) with `T̂ⱼ` from his Eq. (3.2).

**Consistency of the family.** `logGammaAnalytic` is a *definition*, not an opaque name — the
Weierstrass series `-γz - log z + Σ (z/n - log(1 + z/n))` — and `exp_logGammaAnalytic` is a
theorem; `differentiableOn_logGammaAnalytic` and `logGammaAnalytic_ofReal_im` show it is the
holomorphic logarithm of `Γ` on the cut plane that is real on the positive axis, i.e. exactly
Brent's `ln Γ`.  The four `Prop` fields of `BrentStirlingInputs` (`brent_stirling_expansion`,
`brent_stirling_remainder_bound` and the shifted pair) are therefore statements about a fixed,
concrete function, with the two data fields `brent_stirling_remainder` := his `R₂` and
`brentShiftedRemainder` := his `R̂₂` the only opaque symbols left; they hold simultaneously under
that interpretation, as exhibited point by point in `Code/verify_brent_family_consistent.py`,
which instantiates them with mpmath's `loggamma` and the two truncation errors and checks every
statement, including `Im z < 0` points. Worst observed ratios: `0.2881` against the unshifted
bound, `0.2462` against the shifted one, and `exp ∘ lnΓ = Γ` to `10⁻⁴⁰`.

The whole Brent family lives in this file rather than in `BackgroundZetaBounds` because the
unshifted expansion needs `logGammaAnalytic`, and `ExternalFacts` cannot depend on that file.
-/

/-! ### The analytic branch of `log Γ`

Nothing in this section depends on any hypothesis class: `logGammaAnalytic` and the results about
it are proved outright from Mathlib.  The section variable was closed above, before Backlund's
trick, and is reopened below, so that these statements are unconditional. -/

/-- **The `n`-th Weierstrass term of `log Γ`:** `z/(n+1) - log(1 + z/(n+1))`, principal logarithm.

### Summary of Proof
Definition.  For `z` in the slit plane so is `1 + z/(n+1)` (`one_add_div_mem_slitPlane`), so the
term is analytic there; it is `O(‖z‖²/n²)` (`norm_logGammaTerm_le`).

### References
Whittaker–Watson §12.1, the Weierstrass product `1/Γ(z) = z e^{γz} ∏ (1 + z/n) e^{-z/n}`.

### Dependencies
**Depends on:** none.
**Used by:** `norm_logGammaTerm_le`, `summable_logGammaTerm`, `differentiableOn_logGammaTerm`,
`logGammaAnalytic`, `logGammaPartial`, `exp_logGammaPartial`,
`differentiableOn_logGammaAnalytic`, `logGammaAnalytic_ofReal_im`. -/
noncomputable def logGammaTerm (z : ℂ) (n : ℕ) : ℂ :=
  z / ((n : ℂ) + 1) - Complex.log (1 + z / ((n : ℂ) + 1))

/-- **`‖(n : ℂ) + 1‖ = n + 1`.**

### Summary of Proof
`Complex.norm_natCast` after writing `(n : ℂ) + 1 = ((n+1 : ℕ) : ℂ)`.

### Dependencies
**Depends on:** none.
**Used by:** `norm_logGammaTerm_le`. -/
theorem norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

/-- **`‖logGammaTerm z n‖ ≤ ‖z‖²/(n+1)²` once `n + 1 ≥ 2‖z‖`.**

### Summary of Proof
With `w = z/(n+1)`, `‖w‖ ≤ 1/2`, and Mathlib's `Complex.norm_log_one_add_sub_self_le` gives
`‖log(1+w) - w‖ ≤ ‖w‖²(1-‖w‖)⁻¹/2 ≤ ‖w‖²`.

### Dependencies
**Depends on:** `logGammaTerm`, `norm_natCast_add_one`.
**Used by:** `summable_logGammaTerm`, `differentiableOn_logGammaAnalytic`. -/
theorem norm_logGammaTerm_le {z : ℂ} {n : ℕ} (hn : 2 * ‖z‖ ≤ (n : ℝ) + 1) :
    ‖logGammaTerm z n‖ ≤ ‖z‖ ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set w := z / ((n : ℂ) + 1) with hwdef
  have hw : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by rw [hwdef, norm_div, norm_natCast_add_one]
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ hn1]; linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have h := Complex.norm_log_one_add_sub_self_le hw1
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  have e : logGammaTerm z n = -(Complex.log (1 + w) - w) := by
    simp only [logGammaTerm, hwdef]; ring
  rw [e, norm_neg]
  calc ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := h
    _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 / ((n : ℝ) + 1) ^ 2 := by rw [hw, div_pow]; ring

/-- **The Weierstrass series converges for every `z`.**

### Summary of Proof
`Summable.of_norm_bounded_eventually_nat` with the majorant `‖z‖²/(n+1)²` of
`norm_logGammaTerm_le`, valid for `n + 1 ≥ 2‖z‖`.

### Dependencies
**Depends on:** `norm_logGammaTerm_le`.
**Used by:** `tendsto_logGammaPartial`, `differentiableOn_logGammaAnalytic`. -/
theorem summable_logGammaTerm (z : ℂ) : Summable (logGammaTerm z) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => ‖z‖ ^ 2 / ((n : ℝ) + 1) ^ 2)
    ?_ ?_
  · have h0 := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    have h2 := (summable_nat_add_iff 1).mpr h0
    refine (h2.mul_left (‖z‖ ^ 2)).congr fun n => ?_
    push_cast; ring
  · filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have h1 : (2 * ‖z‖ : ℝ) ≤ ⌈2 * ‖z‖⌉₊ := Nat.le_ceil _
    have h2 : ((⌈2 * ‖z‖⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    exact norm_logGammaTerm_le (by linarith)

/-- **The slit plane is stable under `z ↦ 1 + z/(n+1)`.**

### Summary of Proof
`Complex.mem_slitPlane_iff`: if `0 < Re z` then `Re(1 + z/(n+1)) > 0`; if `Im z ≠ 0` then
`Im(1 + z/(n+1)) = Im z/(n+1) ≠ 0`.

### Dependencies
**Depends on:** none.
**Used by:** `exp_logGammaPartial`, `differentiableOn_logGammaTerm`. -/
theorem one_add_div_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) (n : ℕ) :
    1 + z / ((n : ℂ) + 1) ∈ Complex.slitPlane := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  have hre : (1 + z / ((n : ℂ) + 1)).re = 1 + z.re / ((n : ℝ) + 1) := by
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
  have him : (1 + z / ((n : ℂ) + 1)).im = z.im / ((n : ℝ) + 1) := by
    rw [Complex.add_im, Complex.one_im, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  rcases hz with h | h
  · left; rw [hre]; positivity
  · right; rw [him]; exact div_ne_zero h hn1.ne'

/-- **The analytic branch of `log Γ` on the slit plane — Brent's `ln Γ` — as the Weierstrass
series** `logGammaAnalytic z = -γz - log z + Σ_{n≥1} (z/n - log(1 + z/n))`, principal logarithms.

### Summary of Proof
Definition.  `exp_logGammaAnalytic` shows `exp ∘ logGammaAnalytic = Γ` on the slit plane
`ℂ \ (-∞, 0]`, `differentiableOn_logGammaAnalytic` that it is holomorphic there, and
`logGammaAnalytic_ofReal_im` that it is real on the positive real axis — which together
characterise Brent's `ln Γ` (the holomorphic logarithm of `Γ` on the cut plane that is real for
positive real arguments), so the Stirling expansions below are statements about *this* function.

### Lean Notes
Mathlib has only the principal branch `Complex.log ∘ Complex.Gamma`, which jumps by `2π` in its
imaginary part and cannot satisfy the Stirling expansions (see the section header); the series
definition avoids the branch problem entirely.  Off the slit plane the series still converges,
but nothing is claimed about it there.

### References
Whittaker–Watson §12.1; Brent, `\cite{Brent2019}`, §2 (the paragraph defining `ln Γ`).

### Dependencies
**Depends on:** `logGammaTerm`.
**Used by:** `BrentStirlingInputs` (all four of its `Prop` fields), `exp_logGammaAnalytic`,
`differentiableOn_logGammaAnalytic`, `logGammaAnalytic_ofReal_im`, `brent_stirling_expansion`,
`brent_stirling_shifted_expansion`, `BackgroundZetaBounds.re_logGammaAnalytic_eq`,
`BackgroundZetaBounds.log_norm_Gamma_eq_re_logGammaAnalytic`,
`BackgroundZetaBounds.logGammaAnalytic_shift_im`,
`BackgroundZetaBounds.arg_Gamma_eq_logGammaAnalytic_im_add_int`,
`BackgroundZetaBounds.argGamma_analytic`, `BackgroundZetaBounds.argGamma`. -/
noncomputable def logGammaAnalytic (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * z - Complex.log z + ∑' n, logGammaTerm z n

/-- **The `N`-th partial sum of the Weierstrass series with `γ` replaced by `H_N - log N`.**

### Summary of Proof
Definition.  `exp_logGammaPartial` shows its exponential is Mathlib's `Complex.GammaSeq z N`, and
`tendsto_logGammaPartial` that it converges to `logGammaAnalytic z`.

### Dependencies
**Depends on:** `logGammaTerm`.
**Used by:** `exp_logGammaAnalytic`, `exp_logGammaPartial`, `tendsto_logGammaPartial`. -/
noncomputable def logGammaPartial (z : ℂ) (N : ℕ) : ℂ :=
  -(((harmonic N : ℝ) - Real.log N : ℝ) : ℂ) * z - Complex.log z
    + ∑ n ∈ Finset.range N, logGammaTerm z n

/-- **`exp (logGammaPartial z N) = GammaSeq z N`** for `z` in the slit plane and `N ≥ 1`, where
`GammaSeq z N = N^z N!/∏_{j≤N}(z+j)` is Euler's approximant to `Γ`.

### Summary of Proof
Regroup the exponent as `z log N + (Σ z/(n+1) - H_N z) - log z - Σ log(1 + z/(n+1))`.  The first
exponential is `N^z` (`Complex.cpow_def_of_ne_zero`), the second is `1` (`harmonic` is the sum of
the reciprocals), the third is `z⁻¹`, and the fourth is `(∏(1 + z/(n+1)))⁻¹`
(`Complex.exp_sum`, `Complex.exp_log`, legitimate because each `1 + z/(n+1)` is in the slit plane).
Finally `∏_{n<N}(1 + z/(n+1)) = ∏_{j≤N}(z+j)/(z · N!)` (`Finset.prod_range_succ'`,
`Finset.prod_range_add_one_eq_factorial`), and `field_simp` closes.

### Dependencies
**Depends on:** `logGammaPartial`, `logGammaTerm`, `one_add_div_mem_slitPlane`.
**Used by:** `exp_logGammaAnalytic`. -/
theorem exp_logGammaPartial {z : ℂ} (hz : z ∈ Complex.slitPlane) {N : ℕ} (hN : 0 < N) :
    Complex.exp (logGammaPartial z N) = Complex.GammaSeq z N := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hne : ∀ n : ℕ, (1 : ℂ) + z / ((n : ℂ) + 1) ≠ 0 :=
    fun n => Complex.slitPlane_ne_zero (one_add_div_mem_slitPlane hz n)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnz : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hsplit : logGammaPartial z N
      = ((Real.log N : ℂ) * z)
        + (-(((harmonic N : ℝ) : ℂ) * z) + ∑ n ∈ Finset.range N, z / ((n : ℂ) + 1))
        + (-Complex.log z)
        + (-∑ n ∈ Finset.range N, Complex.log (1 + z / ((n : ℂ) + 1))) := by
    unfold logGammaPartial logGammaTerm
    rw [Finset.sum_sub_distrib]
    push_cast
    ring
  have hH : ∑ n ∈ Finset.range N, z / ((n : ℂ) + 1) = ((harmonic N : ℝ) : ℂ) * z := by
    rw [harmonic]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have e1 : Complex.exp ((Real.log N : ℂ) * z) = (N : ℂ) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hN0, ← Complex.ofReal_natCast,
      Complex.ofReal_log (Nat.cast_nonneg N)]
  have e2 : Complex.exp (-(((harmonic N : ℝ) : ℂ) * z) + ∑ n ∈ Finset.range N, z / ((n : ℂ) + 1))
      = 1 := by
    rw [hH]; simp
  have e3 : Complex.exp (-Complex.log z) = z⁻¹ := by
    rw [Complex.exp_neg, Complex.exp_log hz0]
  have e4 : Complex.exp (-∑ n ∈ Finset.range N, Complex.log (1 + z / ((n : ℂ) + 1)))
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))⁻¹ := by
    rw [Complex.exp_neg, Complex.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun n _ => Complex.exp_log (hne n)
  have hprod : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ j ∈ Finset.range (N + 1), (z + j)) / (z * (N.factorial : ℂ)) := by
    have hfac : ∏ n ∈ Finset.range N, ((n : ℂ) + 1) = (N.factorial : ℂ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
    have h1 : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      field_simp
      ring
    have hfac_ne : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
    rw [h1, hfac, Finset.prod_range_succ']
    push_cast
    rw [add_zero]
    field_simp
  have hprod_ne : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun n _ => hne n
  have hbig_ne : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ)) ≠ 0 := by
    intro h
    rw [hprod, h, zero_div] at hprod_ne
    exact hprod_ne rfl
  rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_add, e1, e2, e3, e4, hprod]
  unfold Complex.GammaSeq
  have hfac_ne : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  field_simp

/-- **`logGammaPartial z N → logGammaAnalytic z`.**

### Summary of Proof
`H_N - log N → γ` (Mathlib's `Real.tendsto_harmonic_sub_log`) and the partial sums of the
summable series converge to its sum (`summable_logGammaTerm`).

### Dependencies
**Depends on:** `logGammaPartial`, `logGammaAnalytic`, `summable_logGammaTerm`.
**Used by:** `exp_logGammaAnalytic`. -/
theorem tendsto_logGammaPartial (z : ℂ) :
    Filter.Tendsto (logGammaPartial z) Filter.atTop (nhds (logGammaAnalytic z)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (((harmonic N : ℝ) - Real.log N : ℝ) : ℂ)) Filter.atTop
      (nhds (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  have h2 := (summable_logGammaTerm z).hasSum.tendsto_sum_nat
  have := ((h1.neg.mul_const z).sub_const (Complex.log z)).add h2
  exact this

/-- **`logGammaAnalytic` is a logarithm of `Γ` on the slit plane:** `exp ∘ logGammaAnalytic = Γ`
on `ℂ \ (-∞,0]`.

### Summary of Proof
`exp (logGammaPartial z N) = GammaSeq z N` for `N ≥ 1` (`exp_logGammaPartial`); the left side
tends to `exp (logGammaAnalytic z)` (`tendsto_logGammaPartial`, continuity of `exp`) and the right
side to `Γ z` (Mathlib's `Complex.GammaSeq_tendsto_Gamma`); limits are unique.

### Lean Notes
Everything about `Complex.arg (Complex.Gamma z)`
that is recoverable from the analytic branch is recoverable through this equation and no more —
see `BackgroundZetaBounds.arg_Gamma_eq_logGammaAnalytic_im_add_int`, which is the exact bridge
(`arg` equals the analytic imaginary part *up to an unknown integer multiple of `2π`*).  The
domain is the whole slit plane `{z | 0 < z.re ∨ z.im ≠ 0}`, Brent's cut plane, which contains
both `{0 < z.re}` (the hypothesis of `brent_stirling_expansion`) and `{0 < z.im}`; existing call
sites pass `Or.inl`/`Or.inr`.

### References
Mathlib: `Complex.GammaSeq_tendsto_Gamma`.  External: Brent, `\cite{Brent2019}`, §2.

### Dependencies
**Depends on:** `exp_logGammaPartial`, `tendsto_logGammaPartial`.
**Used by:** `BackgroundZetaBounds.arg_Gamma_eq_logGammaAnalytic_im_add_int`,
`BackgroundZetaBounds.log_norm_Gamma_eq_re_logGammaAnalytic`. -/
theorem exp_logGammaAnalytic {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.exp (logGammaAnalytic z) = Complex.Gamma z := by
  have h1 : Filter.Tendsto (fun N => Complex.exp (logGammaPartial z N)) Filter.atTop
      (nhds (Complex.exp (logGammaAnalytic z))) :=
    (Complex.continuous_exp.tendsto _).comp (tendsto_logGammaPartial z)
  have h2 : Filter.Tendsto (fun N => Complex.exp (logGammaPartial z N)) Filter.atTop
      (nhds (Complex.Gamma z)) := by
    refine (Complex.GammaSeq_tendsto_Gamma z).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    exact (exp_logGammaPartial hz hN).symm
  exact tendsto_nhds_unique h1 h2

/-- **Each Weierstrass term is holomorphic on the slit plane.**

### Summary of Proof
`DifferentiableAt.clog` with `one_add_div_mem_slitPlane`.

### Dependencies
**Depends on:** `logGammaTerm`, `one_add_div_mem_slitPlane`.
**Used by:** `differentiableOn_logGammaAnalytic`. -/
theorem differentiableOn_logGammaTerm (n : ℕ) :
    DifferentiableOn ℂ (fun z => logGammaTerm z n) Complex.slitPlane := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z / ((n : ℂ) + 1)) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => 1 + z / ((n : ℂ) + 1)) z := by fun_prop
  have h3 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (1 + z / ((n : ℂ) + 1))) z :=
    h2.clog (one_add_div_mem_slitPlane hz n)
  exact (h1.sub h3).differentiableWithinAt

/-- **`logGammaAnalytic` is holomorphic on the slit plane.**

### Summary of Proof
Locally: on `slitPlane ∩ ball z₀ 1` split the series after `N₀ = ⌈2(‖z₀‖+1)⌉` terms; the finite
part is a sum of holomorphic functions and the tail is uniformly dominated by
`(‖z₀‖+1)²/(n+N₀+1)²` (`norm_logGammaTerm_le`), so Mathlib's
`Complex.differentiableOn_tsum_of_summable_norm` applies.  The `-γz - log z` part is
`Complex.differentiableAt_log`.

### Lean Notes
Together with `exp_logGammaAnalytic` and `logGammaAnalytic_ofReal_im` this identifies
`logGammaAnalytic` with Brent's `ln Γ`; it is not otherwise used.

### Dependencies
**Depends on:** `logGammaAnalytic`, `summable_logGammaTerm`, `norm_logGammaTerm_le`,
`differentiableOn_logGammaTerm`.
**Used by:** none (it exhibits the consistency of the Brent hypotheses). -/
theorem differentiableOn_logGammaAnalytic :
    DifferentiableOn ℂ logGammaAnalytic Complex.slitPlane := by
  intro z₀ hz₀
  have hopen : IsOpen (Complex.slitPlane ∩ Metric.ball z₀ 1) :=
    Complex.isOpen_slitPlane.inter Metric.isOpen_ball
  have hmem : z₀ ∈ Complex.slitPlane ∩ Metric.ball z₀ 1 := ⟨hz₀, Metric.mem_ball_self one_pos⟩
  set N0 : ℕ := ⌈2 * (‖z₀‖ + 1)⌉₊ with hN0
  have hN0ge : 2 * (‖z₀‖ + 1) ≤ (N0 : ℝ) := Nat.le_ceil _
  have htail : DifferentiableOn ℂ (fun w => ∑' n, logGammaTerm w (n + N0))
      (Complex.slitPlane ∩ Metric.ball z₀ 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => (‖z₀‖ + 1) ^ 2 / (((n + N0 : ℕ) : ℝ) + 1) ^ 2) ?_ ?_ hopen ?_
    · have h0 := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      have h2 := (summable_nat_add_iff (N0 + 1)).mpr h0
      refine (h2.mul_left ((‖z₀‖ + 1) ^ 2)).congr fun n => ?_
      push_cast; ring
    · intro n
      exact (differentiableOn_logGammaTerm (n + N0)).mono Set.inter_subset_left
    · intro n w hw
      have hwn : ‖w‖ ≤ ‖z₀‖ + 1 := by
        have := hw.2
        rw [Metric.mem_ball, dist_eq_norm] at this
        calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + 1 := by linarith
      have hn : 2 * ‖w‖ ≤ ((n + N0 : ℕ) : ℝ) + 1 := by
        push_cast
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc ‖logGammaTerm w (n + N0)‖ ≤ ‖w‖ ^ 2 / (((n + N0 : ℕ) : ℝ) + 1) ^ 2 :=
            norm_logGammaTerm_le hn
        _ ≤ (‖z₀‖ + 1) ^ 2 / (((n + N0 : ℕ) : ℝ) + 1) ^ 2 := by
            gcongr
  have hhead : DifferentiableOn ℂ (fun w => ∑ n ∈ Finset.range N0, logGammaTerm w n)
      (Complex.slitPlane ∩ Metric.ball z₀ 1) := by
    have e : (fun w => ∑ n ∈ Finset.range N0, logGammaTerm w n)
        = ∑ n ∈ Finset.range N0, fun w => logGammaTerm w n := by
      funext w; simp [Finset.sum_apply]
    rw [e]
    apply DifferentiableOn.sum
    intro n _
    exact (differentiableOn_logGammaTerm n).mono Set.inter_subset_left
  have hsum : DifferentiableOn ℂ (fun w => ∑' n, logGammaTerm w n)
      (Complex.slitPlane ∩ Metric.ball z₀ 1) := by
    have e : (fun w => ∑' n, logGammaTerm w n)
        = fun w => (∑ n ∈ Finset.range N0, logGammaTerm w n) + ∑' n, logGammaTerm w (n + N0) := by
      funext w
      exact ((summable_logGammaTerm w).sum_add_tsum_nat_add N0).symm
    rw [e]
    exact hhead.add htail
  have hlog : DifferentiableOn ℂ (fun w : ℂ => -(Real.eulerMascheroniConstant : ℂ) * w
      - Complex.log w) (Complex.slitPlane ∩ Metric.ball z₀ 1) := by
    intro w hw
    exact ((differentiableAt_id.const_mul _).sub
      (Complex.differentiableAt_log hw.1)).differentiableWithinAt
  have hall : DifferentiableOn ℂ logGammaAnalytic (Complex.slitPlane ∩ Metric.ball z₀ 1) :=
    hlog.add hsum
  exact (hall.differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt

/-- **`logGammaAnalytic` is real on the positive real axis.**

### Summary of Proof
Every term is the cast of a real number (`Complex.ofReal_log` for `1 + x/(n+1) > 0`), and
`Complex.ofReal_tsum` moves the cast through the sum.

### Lean Notes
This is the normalisation that distinguishes Brent's `ln Γ` among the logarithms of `Γ`
(`ln Γ(x) = log Γ(x)` for real `x > 0`).

### Dependencies
**Depends on:** `logGammaAnalytic`, `logGammaTerm`.
**Used by:** none (it exhibits the consistency of the Brent hypotheses). -/
theorem logGammaAnalytic_ofReal_im {x : ℝ} (hx : 0 < x) : (logGammaAnalytic (x : ℂ)).im = 0 := by
  have hterm : ∀ n : ℕ, logGammaTerm (x : ℂ) n
      = ((x / ((n : ℝ) + 1) - Real.log (1 + x / ((n : ℝ) + 1)) : ℝ) : ℂ) := by
    intro n
    have hpos : (0 : ℝ) ≤ 1 + x / ((n : ℝ) + 1) := by positivity
    unfold logGammaTerm
    rw [Complex.ofReal_sub, Complex.ofReal_log hpos]
    push_cast
    ring_nf
  unfold logGammaAnalytic
  have htsum : ∑' n, logGammaTerm (x : ℂ) n
      = ((∑' n : ℕ, (x / ((n : ℝ) + 1) - Real.log (1 + x / ((n : ℝ) + 1))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [htsum, ← Complex.ofReal_log hx.le]
  simp

/-- **Brent's explicit Stirling expansions for `log Γ`, as a hypothesis class.**

R. P. Brent, *Asymptotic approximation of central binomial coefficients with rigorous error
bounds*, `\cite{Brent2019}`: Eq. (2.1) with Corollary 2.2's remainder bound at `k = 2`, and the
shifted Eq. (3.4).  Both expansions name a remainder function and then bound it, so the class
carries the two functions as **data** and the four statements about them as `Prop` fields; that is
the honest reading of "there is a remainder with these properties".  It is the reason this class,
unlike `Hypotheses.LiteratureInputs` and `Hypotheses.NumericCertificates`, is not `Prop`-valued.

It is declared here rather than in `Hypotheses.lean` because its statements mention
`logGammaAnalytic`, which is defined above in this file.

The full provenance — which edition was checked, the principal-branch encoding that would make
this material *inconsistent*, and why the analytic branch `logGammaAnalytic` rather than
`Complex.log ∘ Complex.Gamma` is the right object — is on the six declarations below, which read
their content off this class.

### Summary of Proof
A class; no proof.

### Lean Notes
`brent_stirling_remainder` and `brentShiftedRemainder` are thin `def`s over the two data fields,
so the four expansions below can be stated in Brent's own notation for `R₂` and `R̂₂`.

### References
External: Brent, `\cite{Brent2019}`, Eq. (2.1), Corollary 2.2, Eq. (3.4).

### Dependencies
**Depends on:** `logGammaAnalytic`.
**Used by:** `brent_stirling_remainder`, `brentShiftedRemainder`, `brent_stirling_expansion`,
`brent_stirling_remainder_bound`, `brent_stirling_shifted_expansion`,
`brent_stirling_shifted_remainder_bound`. -/
class BrentStirlingInputs where
  /-- Brent's `R₂`, the remainder of the unshifted expansion Eq. (2.1). -/
  remainder : ℂ → ℂ
  /-- Brent's `R̂₂`, the remainder of the shifted expansion Eq. (3.4). -/
  shiftedRemainder : ℂ → ℂ
  /-- Brent, Eq. (2.1): `log Γ(z) = (z-½)log z - z + ½log(2π) + B₂/(2z) + R₂(z)` for `Re z > 0`,
  with `log Γ` read as the analytic branch `logGammaAnalytic`. -/
  expansion : ∀ {z : ℂ}, 0 < z.re →
    logGammaAnalytic z
      = (z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * Real.pi)
        + (bernoulli 2 : ℂ) / (2 * z) + remainder z
  /-- Brent, Corollary 2.2 at `k = 2`: `‖R₂(z)‖ < ‖(1+√(2π))B₄/(12z³)‖` for `Re z > 0`. -/
  remainder_bound : ∀ {z : ℂ}, 0 < z.re →
    ‖remainder z‖ < ‖(1 + Real.sqrt (2 * Real.pi)) * (bernoulli 4 : ℂ) / (12 * z ^ 3)‖
  /-- Brent, Eq. (3.4): the half-shifted expansion
  `log Γ(z+½) = z log z - z + ½log(2π) - 1/(24z) + R̂₂(z)` for `Im z > 5`. -/
  shifted_expansion : ∀ {z : ℂ}, 5 < z.im →
    logGammaAnalytic (z + 1 / 2)
      = z * Complex.log z - z + 1 / 2 * Complex.log (2 * Real.pi) - 1 / (24 * z)
        + shiftedRemainder z
  /-- Brent: `‖R̂₂(z)‖ ≤ (1/100)/‖z‖³` for `Im z > 5` and `|Re z| ≤ 1`. -/
  shifted_remainder_bound : ∀ {z : ℂ}, 5 < z.im → |z.re| ≤ 1 →
    ‖shiftedRemainder z‖ ≤ 1 / 100 / ‖z‖ ^ 3

variable [LiteratureInputs] [BrentStirlingInputs]

/-- **The remainder term `R₂` in Brent's Stirling expansion.** The data field
`BrentStirlingInputs.remainder`, named here so that `brent_stirling_expansion` and
`brent_stirling_remainder_bound` refer to the same remainder.

### Summary of Proof
Nothing to prove — a name for a data field, not a claim. Its two properties are the statements of
the next two theorems.

### Lean Notes
**Citation check.** The expansion below states Brent's Eq. (2.1) for `Γ(z)` itself, not
`Γ(z+1/2)`. `BRENT_2019`'s PDF is available
(`on-the-accuracy-of-asymptotic-approximations-...-riemann-siegel-theta-functions.pdf`). The
tex's display (line 1332), `\log\Gamma(z) = (z-1/2)\log z - z + (1/2)\log(2\pi) + B_2/(2z) +
R_2(z)` for `\Re z > 0`, matches Brent's Eq. (2.1) for `ln Γ(z)` coefficient-for-coefficient
(leading term `(z-1/2)log z`, plain Bernoulli *number* `B₂ = 1/6`). It is *not* Brent's shifted
Eq. (3.4) for `ln Γ(z+1/2)`, whose leading term is `z log z` and whose `j = 1` term is the
Bernoulli *polynomial* value `B₂(1/2) = -1/12`, giving `-1/(24z)`; that form is recorded
separately as `brent_stirling_shifted_expansion` below.

**The tex's display is a complex identity, not a claim about `\log|\Gamma|`.** `R₂(z)` is
complex, and so is `B₂/(2z)` off the real axis; the next display in the tex writes
`\log(\Gamma(a+it/2)) - \log(\Gamma(b+it/2))` and is followed by "Taking real parts we obtain".
Reading it instead with absolute-value bars is what would invite the principal-branch encoding
that makes these hypotheses inconsistent — see the section header above.

This is the form `BackgroundZetaBounds.zetalessthanhalf_upper`/`_lower` need: exactly
`log Γ(z)` at the plain (unshifted) arguments `z = 1-σ∓it` reached via Mathlib's
`riemannZeta_one_sub` — no half-argument/Legendre-duplication route is needed, since Mathlib's
functional equation already uses whole-argument `Gamma s`, unlike the tex's classical `χ(s)` via
`Γ(s/2)`, `Γ((1-s)/2)`. `Lemma \ref{lemma:argGamma}` (Lemma 37, `argGamma`), by contrast,
genuinely needs the imaginary-part analogue at a shifted point; that is available directly as
`brent_stirling_shifted_expansion` below, Brent's Eq. (3.4), which carries its own remainder
`brentShiftedRemainder`.

### References
External: Brent, `\cite[Eq. (2.1)]{Brent2019}`; the shifted form is that paper's Eq. (3.4),
recorded separately as `brent_stirling_shifted_expansion`.
tex: used in the proof of `Lemma \ref{lem:zetalessthanhalf}` (Lemma 36), and
`Lemma \ref{lemma:argGamma}` (Lemma 37) via the shifted form.

### Dependencies
**Depends on:** `BrentStirlingInputs.remainder`.
**Used by:** `brent_stirling_expansion`, `brent_stirling_remainder_bound`,
`BackgroundZetaBounds.brent_remainder_re_bound`,
`BackgroundZetaBounds.gamma_cos_estimate_general`, `BackgroundZetaBounds.re_logGammaAnalytic_eq`.
-/
noncomputable def brent_stirling_remainder (z : ℂ) : ℂ :=
  BrentStirlingInputs.remainder z

/-- **Brent's explicit Stirling expansion for `ln Γ(z)`.** For `Re z > 0`,
`lnΓ(z) = (z-1/2)log z - z + (1/2)log(2π) + B₂/(2z) + R₂(z)`, with `B₂ = 1/6` the plain
Bernoulli *number* and `lnΓ = logGammaAnalytic` the analytic branch.

### Summary of Proof
Not proved here — the field `BrentStirlingInputs.expansion`, recording Brent's Eq. (2.1)
verbatim. `R₂ = brent_stirling_remainder` is the truncation remainder, whose size is controlled
by `brent_stirling_remainder_bound`.

### Lean Notes
Taken as a hypothesis because Mathlib's pinned snapshot has asymptotic `Gamma` estimates but not
this explicit two-term-plus-bounded-remainder form with usable constants.

**The left side is `logGammaAnalytic z`, NOT `Complex.log (Complex.Gamma z)`.** With the
principal branch this statement and `brent_stirling_remainder_bound` would be jointly
inconsistent — they would prove `False` — for the reason set out in full in the section header
above, and Brent's `ln Γ` in Eq. (2.1) is the analytic branch in any case.

**The restatement costs the intended consumers nothing.** Two branches of `log Γ` differ by an
element of `2πiℤ`, which is *purely imaginary*, so `Re logGammaAnalytic z = Re log(Γ z)`
identically. `BackgroundZetaBounds.zetalessthanhalf_upper`/`_lower` use only the real part (they
go through `Real.log ‖·‖`), so they can be written against either. It is the imaginary part —
what `argGamma` needs — that genuinely differs, and there the principal-branch version is simply
false.

See `brent_stirling_remainder` above for the provenance discussion, including why this is the
*unshifted* form; `brent_stirling_shifted_expansion` below is Brent's Eq. (3.4).

### References
External: Brent, `\cite[Eq. (2.1)]{Brent2019}`, read directly from the PDF: `ln Γ(z) =
(z - 1/2) log z - z + (1/2) log(2π) + Σ_{j=1}^{k-1} Tⱼ(z) + Rₖ(z)` with
`Tⱼ(z) = B_{2j}/(2j(2j-1)z^{2j-1})`, taken at `k = 2` where the sum is `T₁(z) = B₂/(2z)`.
tex: used in the proof of `Lemma \ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `logGammaAnalytic`, `brent_stirling_remainder`.
**Used by:** `BackgroundZetaBounds.re_logGammaAnalytic_eq`, and through it the whole
`gamma_cos_estimate_*`/`zetalessthanhalf_*` family. -/
theorem brent_stirling_expansion {z : ℂ} (hz : 0 < z.re) :
    logGammaAnalytic z
      = (z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * Real.pi)
        + (bernoulli 2 : ℂ) / (2 * z) + brent_stirling_remainder z :=
  BrentStirlingInputs.expansion hz

/-- **Brent's bound on the Stirling remainder.** For `Re z > 0`,
`‖R₂(z)‖ < ‖(1+√(2π)) B₄ / (12 z³)‖`, with `B₄ = -1/30`.

### Summary of Proof
Not proved here — the field `BrentStirlingInputs.remainder_bound`, recording Brent's remainder
estimate verbatim.

### Lean Notes
This is what makes `brent_stirling_expansion` usable: the remainder decays like `1/|z|³`, so at
the arguments `z = 1-σ∓it` reached through Mathlib's `riemannZeta_one_sub` it is negligible
against the explicit terms for the large `|t|` in play.

The `(1+√(2π))` factor is Brent's, covering the whole right half-plane rather than only a sector.
A sharper constant is available for `Re z` bounded away from `0`, but is not needed here.

**This statement mentions only `brent_stirling_remainder`, not `log Γ`,** so the branch question
does not arise in it. It is nevertheless half of the inconsistency the section header describes:
paired with a principal-branch `brent_stirling_expansion` it would force `‖R₂‖ < 10⁻⁵` against a
value the branch cut forces to be a nonzero multiple of `2π`. Stating the expansion on the
analytic branch is what makes the pair consistent.

### References
External: Brent, `\cite{Brent2019}`, Corollary 2.2 at `k = 2`, read directly from the PDF:
`|Rₖ(z)/Tₖ(z)| < 1 + √(πk)` for `z ∈ H*`, with `Tₖ` from Eq. (2.2); at `k = 2`,
`T₂(z) = B₄/(4·3·z³) = B₄/(12z³)`, giving exactly the bound below.
tex: used in the proof of `Lemma \ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `brent_stirling_remainder`.
**Used by:** `BackgroundZetaBounds.brent_remainder_re_bound`, and through it the
`gamma_cos_estimate_*`/`zetalessthanhalf_*` family. -/
theorem brent_stirling_remainder_bound {z : ℂ} (hz : 0 < z.re) :
    ‖brent_stirling_remainder z‖
      < ‖(1 + Real.sqrt (2 * Real.pi)) * (bernoulli 4 : ℂ) / (12 * z ^ 3)‖ :=
  BrentStirlingInputs.remainder_bound hz

/-- **The remainder in the shifted Stirling expansion**, `R̂₂`. The data field
`BrentStirlingInputs.shiftedRemainder`, so that `brent_stirling_shifted_expansion` and
`brent_stirling_shifted_remainder_bound` refer to the same object — exactly the role
`brent_stirling_remainder` plays for the unshifted expansion.

### Summary of Proof
Nothing to prove — a name for a data field.

### References
External: Brent, `\cite{Brent2019}`, the `R̂₂` of his Eq. (3.4); see
`brent_stirling_shifted_expansion`.

### Dependencies
**Depends on:** `BrentStirlingInputs.shiftedRemainder`.
**Used by:** `brent_stirling_shifted_expansion`, `brent_stirling_shifted_remainder_bound`,
`BackgroundZetaBounds.argGamma_analytic`, `BackgroundZetaBounds.argGamma_im_diff`,
`BackgroundZetaBounds.logGammaAnalytic_shift_im`. -/
noncomputable def brentShiftedRemainder (z : ℂ) : ℂ := BrentStirlingInputs.shiftedRemainder z

/-- **The shifted Stirling expansion.** For `Im z > 5`,
`lnΓ(z + 1/2) = z log z - z + (1/2) log(2π) - 1/(24z) + R̂₂(z)`.

### Summary of Proof
Not proved here — the field `BrentStirlingInputs.shifted_expansion`, recording **Brent's
Eq. (3.4)** verbatim at `k = 2`. Brent derives
it from his Eq. (3.1) via the duplication formula `Γ(z+1/2) = 2^{1-2z}π^{1/2}Γ(2z)/Γ(z)` and
states it as *Gauss's asymptotic expansion of* `ln Γ(z+1/2)`:

    ln Γ(z + 1/2) = z log z - z + (1/2)log(2π) + Σ_{j=1}^{k-1} T̂ⱼ(z) + R̂ₖ(z),
    T̂ⱼ(z) = B_{2j}(1/2) / (2j(2j-1) z^{2j-1}) = (2^{1-2j}-1)B_{2j} / (2j(2j-1) z^{2j-1}).

At `k = 2` the sum is the single term `T̂₁(z) = B₂(1/2)/(2z) = (-1/12)/(2z) = -1/(24z)`, which is
the `-1/(24z)` written below, and `R̂₂ = brentShiftedRemainder`. The next term
`T̂₂(z) = B₄(1/2)/(12z³) = 7/(2880z³)` sets the size of the remainder.

### Lean Notes
**Citation verified against the source.** The PDF was extracted and read: Eq. (3.4) is exactly
the display above, with `T̂ⱼ` given by its Eq. (3.2). Independently,
`Code/verify_argGamma.py` section (D) measures `‖R̂₂(z)‖·‖z‖³ → 0.0024305`, matching
`7/2880 = 0.00243056` to six digits.

**Domain.** The hypothesis is `5 < z.im`, not `0 < z.re` as in the unshifted pair. The two
points needed by `BackgroundZetaBounds.argGamma_analytic` are `z = it/2` and `z = δ/2 + it/2`
with `t > 10` and `δ ∈ [-1/2, 1]`, so `Re z = δ/2` is *negative* for `δ < 0` and a `0 < z.re`
hypothesis would not cover them; `Im z = t/2 > 5` does, and keeps `z` far from `Γ`'s real poles.

**Branch.** `Complex.log z` on the right *is* the principal branch, and correctly so: `z` lies in
the open upper half plane, where the principal `log` is holomorphic. Only `log Γ` needs the
analytic branch — see the section header.

### References
External: Brent, `\cite[Eq. (3.4)]{Brent2019}` (with `T̂ⱼ` from that paper's Eq. (3.2)), read
directly from the PDF; coefficients also confirmed numerically via
`Code/verify_argGamma.py`.

### Dependencies
**Depends on:** `logGammaAnalytic`, `brentShiftedRemainder`.
**Used by:** `BackgroundZetaBounds.logGammaAnalytic_shift_im`. -/
theorem brent_stirling_shifted_expansion {z : ℂ} (hz : 5 < z.im) :
    logGammaAnalytic (z + 1 / 2)
      = z * Complex.log z - z + 1 / 2 * Complex.log (2 * Real.pi) - 1 / (24 * z)
        + brentShiftedRemainder z :=
  BrentStirlingInputs.shifted_expansion hz

/-- **Bound on the shifted Stirling remainder.** For `Im z > 5` and `|Re z| ≤ 1`,
`‖R̂₂(z)‖ ≤ (1/100)/‖z‖³`.

### Summary of Proof
Not proved here — the field `BrentStirlingInputs.shifted_remainder_bound`; the constant is
Brent's, not invented. Brent's
`R̂ₖ = T̂ₖ + R̂ₖ₊₁` together with his Corollary 3.3, `|R̂ₖ₊₁(z)/T̂ₖ(z)| < ηₖ√(πk)`, and his
Remark 3.4 (the factor `ηₖ` may be dropped once `|z| ≥ 1`, which holds here since
`|z| ≥ Im z > 5`) give, at `k = 2` with `T̂₂(z) = 7/(2880z³)`,

    ‖R̂₂(z)‖ ≤ (1 + √(2π))·|T̂₂(z)| = 3.5066 · 7/(2880‖z‖³) = 0.00853/‖z‖³ < (1/100)/‖z‖³.

This is the exact shifted analogue of the constant `(1+√(2π))·B₄/(12z³)` that
`brent_stirling_remainder_bound` takes from Brent's Corollary 2.2 at `k = 2`.

### Lean Notes
**Domain.** Brent's theorems are stated on `H* = {Re z ≥ 0} \ {0}`, whereas this hypothesis
allows `Re z ∈ [-1, 0)` too, which the application needs (`Re z = δ/2 < 0` when `δ < 0`). That
small extension is verified numerically rather than cited: `Code/verify_argGamma.py`
section (G) sweeps `Re z ∈ [-1,1]`, `Im z ∈ [5, 10⁵]` and finds
`max ‖R̂₂(z)‖·‖z‖³ = 0.0024623` (attained at the corner `Im z = 5`) — a factor `4.06` inside the
stated `1/100`, and in fact below Brent's own `0.00853` everywhere on that box. The `|Re z| ≤ 1`
restriction matters: with `Im z` fixed and `Re z → -∞` the point approaches the negative real
axis, where Stirling degrades. The application needs only `Re z ∈ [-1/4, 1/2]`.

### References
External: Brent, `\cite{Brent2019}`, Theorem 3.2 / Corollary 3.3 / Remark 3.4 (the bounds
accompanying Eq. (3.4)); the `Re z ∈ [-1,0)` corner verified numerically via
`Code/verify_argGamma.py`.

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [J] recomputes `R̂₂(z) = lgΓ(z+1/2) - (z log z - z +
log(2π)/2 - 1/(24z))` with mpmath's `loggamma` on `Re z ∈ [-1,1]`, `Im z ∈ [5, 10⁴]`:
`max ‖R̂₂‖·‖z‖³ = 0.0024623` at `z = 5i`, against Brent's leading term `7/2880 = 0.0024306` and
the stated `1/100` — confirming `verify_argGamma.py` §(G) by a second implementation.

### Dependencies
**Depends on:** `brentShiftedRemainder`.
**Used by:** `BackgroundZetaBounds.argGamma_analytic`. -/
theorem brent_stirling_shifted_remainder_bound {z : ℂ} (hz : 5 < z.im) (hre : |z.re| ≤ 1) :
    ‖brentShiftedRemainder z‖ ≤ 1 / 100 / ‖z‖ ^ 3 :=
  BrentStirlingInputs.shifted_remainder_bound hz hre

/-- **Fiori's explicit multi-function Phragmén–Lindelöf theorem.** Under a two-exponential growth
envelope, a function bounded on the two edges of a strip by products `∏Gᵢ^{αᵢ}`, `∏Gᵢ^{βᵢ}`
satisfies the linearly interpolated bound throughout the strip.

### Summary of Proof
Not proved here — the field `LiteratureInputs.fiori_phragmenLindelof`, recording the source's
Theorem 7. Informally: let `G 1, …, G r` be
holomorphic on the strip `a ≤ Re s ≤ b`, each `ℝ`-conjugation-symmetric
(`G i (conj s) = conj (G i s)`, so real on the real axis) and bounded below by a common envelope
`C1·exp(-C2·exp(C3|t|)) < |G i(σ+it)|`. Let `f` be holomorphic on the same strip with the
*matching* upper envelope `|f(σ+it)| < C1·exp(C2·exp(C3|t|))` — same `C1,C2`, and
`0 < C3 < π/(b-a)`. If `f` is bounded on the edges `Re s = a`, `Re s = b` by `∏Gᵢ^{αᵢ}`,
`∏Gᵢ^{βᵢ}` (`αᵢ,βᵢ ≥ 0`); each `|G i(σ+it)|` is monotonic in `σ` for `|t| > T0` (increasing if
`αᵢ>βᵢ`, decreasing if `βᵢ>αᵢ`); and `f` satisfies the same interpolated bound directly for
`|t| ≤ T0` (with each `|G i|` replaced by its minimum over `σ ∈ [a,b]` at that height), then
`|f(σ+it)| ≤ (∏Gᵢ(σ+it)^{αᵢ})^{(b-σ)/(b-a)}·(∏Gᵢ(σ+it)^{βᵢ})^{(σ-a)/(b-a)}` throughout.

### Lean Notes
Taken as a hypothesis because formalizing a Phragmén–Lindelöf contour argument from scratch needs
substantial complex-analysis infrastructure that is in neither this repository nor (yet) Mathlib.

Its instantiation to `ζ` *is* carried out here, in `PhragmenLindelofSetup.lean`, following the
source paper's own templates: `FIORI-PL`'s §4 "Third example" (between Eq. (6) and (7)) is the
model for `interpolated_bound_1a`/`1b`/`1c` — the sub-Weyl bound `66.7t^{27/164}` at `σ = 1/2`
against the Yang bound `1.546t^{1/14}log t` at `σ = 5/7`, via
`G(s) = ½(log(4e+s)+log(4e+2-s))` and Theorem 7 applied to `f(s) = ζ(s)`, reaching the same
constants `47/123 - 107/246σ` and `14/3(σ-1/2)`; §4's "Second example" is the analogue for
interpolating between consecutive `YANG2024128124` lines, which `interpolated_bound_2` needs.
The one thing the Lean derivation does not reproduce is the paper's error term: `FIORI-PL` tracks
a `(1+10⁻⁹)` factor for `T>10⁵` and an `O(1/t²)` correction, whereas `PhragmenLindelofSetup`
delivers `O^*(3/T)`. `BackgroundZetaBounds`'s "pointwise form" section says exactly where that
is lost.

**Citation check: confirmed against the published PDF**,
doi:10.1016/j.jmaa.2026.130404, word-for-word for Theorem 7.

The paper's informal `min_σ(|G(σ+it)|)` in the `|t| ≤ T0` hypothesis is rendered here as the
**subtype** infimum `⨅ τ : Set.Icc a b, ‖G i((τ:ℝ)+it)‖` — an infimum over the compact interval
`[a,b]`, well-defined and positive there by the growth lower bound on `G i`. The paper does not
spell out the range of `σ` for this minimum, but `[a,b]` is the only reading consistent with the
rest of the statement (matching the outer bound's own `σ ∈ [a,b]`) and with Remark 8 immediately
below Theorem 7, where numerical verification "on the whole region" is offered as a way to check
the hypothesis.

**Why the subtype binder and not `⨅ τ ∈ Set.Icc a b, …`.** The bounded-binder notation
`⨅ τ ∈ s, g τ` unfolds to `⨅ τ : ℝ, ⨅ _ : τ ∈ s, g τ`, an infimum over **all** of `ℝ`. At any
`τ ∉ [a,b]` the inner index type is empty, and `ℝ` is only conditionally complete
(`Real.sInf_empty : sInf ∅ = 0`), so that inner `iInf` is `0` rather than `⊤`. For nonnegative
`g` the outer infimum then picks the `0` up and the whole expression is identically `0` — which
would make this hypothesis, and every `_hcompact` statement discharging it, assert
`‖f(σ+it)‖ < 0`. The trap is recorded, and proved, by
`BackgroundZetaBounds.iInf_mem_Icc_eq_zero` and `norm_comp_iInf_Icc_eq_zero`.

**`hG_conj` is scoped to the strip, not all of `ℂ`.** The source introduces the `Gᵢ` as "complex
functions that are holomorphic for `Re(s) ∈ [a,b]`, have `Gᵢ(s̄) = conj(Gᵢ(s))`" — the conjugation
condition carries the same scope as the holomorphy condition, and must, since the `Gᵢ` are only
assumed defined on the strip. The proof of the source's Lemma 5 — the only place `hG_conj` is
used, via `F(s) = f(a+s)·conj(f(b-s̄))` and `Hᵢ(s) = Gᵢ(a+s)^{…}Gᵢ(b-s)^{…}` — only ever evaluates
`Gᵢ` at points with `Re ∈ [a,b]`.

Stating it over all of `ℂ` would make the hypothesis unsatisfiable for exactly the functions the
source's §4 examples use: `G(s) = ½(log(Q+s)+log(Q+2-s))` (`PhragmenLindelofSetup.GPL`) violates
a whole-plane version on the real axis left of `-Q`, where `Q+s` lands on `Complex.log`'s branch
cut and `conj(G(s)) ≠ G(conj s) = G(s)`. Restricted to the strip, where `Re(Q+s) > 0` for the `Q`
actually used, it is provable — see `PhragmenLindelofSetup.GPL_conj`. Since `(conj s).re = s.re`,
the restriction is symmetric in `s` and `conj s`, so the statement is well-scoped.

### References
External: A. Fiori, *A note on the Phragmén–Lindelöf theorem*, J. Math. Anal. Appl. 559 (2026)
130404, also arXiv:2502.13282; `\cite[Theorem 7]{Fiori2026}`. **This is the external paper's
Theorem 7, not this project's Proposition 8** (`prop:jensen-easy`).
tex: the one substantial external ingredient for the Appendix's interpolation Proposition
`\ref{prop:interpolation}` (Proposition 35).

### Dependencies
**Depends on:** none. (`C1`, `C2`, `C3` are this statement's own bound variables, not
declarations.)
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem fiori_phragmenLindelof {a b : ℝ} (hab : a < b) {r : ℕ} (G : Fin r → ℂ → ℂ)
    (hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b})
    (hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G i s))
    {C1 C2 C3 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3) (hC3b : C3 < Real.pi / (b - a))
    (hG_lower : ∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      C1 * Real.exp (-C2 * Real.exp (C3 * |t|)) < ‖G i (σ + t * Complex.I)‖)
    {f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f {s : ℂ | s.re ∈ Set.Icc a b})
    (hf_upper : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖ < C1 * Real.exp (C2 * Real.exp (C3 * |t|)))
    {α β : Fin r → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hf_a : ∀ t : ℝ, ‖f (a + t * Complex.I)‖ ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i)
    (hf_b : ∀ t : ℝ, ‖f (b + t * Complex.I)‖ ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i)
    {T0 : ℝ}
    (hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)))
    (hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖f (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a))) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖
        ≤ (∏ i, ‖G i (σ + t * Complex.I)‖ ^ α i) ^ ((b - σ) / (b - a))
            * (∏ i, ‖G i (σ + t * Complex.I)‖ ^ β i) ^ ((σ - a) / (b - a)) :=
  LiteratureInputs.fiori_phragmenLindelof hab G hG_holo hG_conj hC1 hC2 hC3 hC3b hG_lower
    hf_holo hf_upper hα hβ hf_a hf_b hG_mono hf_small_t

/-- **Platt–Trudgian's verification of RH to height `3×10¹²`.** Every zero `ρ` of `ζ` with
`0 < Im ρ ≤ 3×10¹²` has `Re ρ = 1/2`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.platt_trudgian_verified_below`, recording the
external computation verbatim.

### Lean Notes
This is `H₀ := 3×10¹²` in the tex's Theorems `\ref{thm:main-jensen}` and
`\ref{thm:main-littlewood}` (Theorems 2 and 3): below `H₀` every zero is known to lie on the
critical line.

`MainTheorem.Nrect_eq_zero_of_le_H0` reads it to conclude `Nrect T₁ T₂ α = 0` whenever `T₂ ≤ H₀`
and `α < 1/2` — a zero counted by `Nrect` has `Re ρ > 1 - α > 1/2`, contradicting `Re ρ = 1/2`.
That is the `t ≤ 10¹²` case of `mainJensen`/`mainLittlewood`. The tex's other use of `H₀` —
shifting the rectangle so its lower edge lands exactly at `H₀` when `T-h < H₀ < T+h` — is vacuous
under those theorems' `h ≤ t^{2/3}`; see `MainTheorem.lean`'s module docstring.

### References
External: Platt–Trudgian, `\cite{PlattTrudgian2021}`.
tex: `Theorem \ref{thm:main-jensen}` (Theorem 2), `Theorem \ref{thm:main-littlewood}`
(Theorem 3).

### Dependencies
**Depends on:** none.
**Used by:** `MainTheorem.Nrect_eq_zero_of_le_H0`. -/
theorem platt_trudgian_verified_below (ρ : ℂ) (him : 0 < ρ.im) (hle : ρ.im ≤ 3 * 10 ^ (12 : ℕ))
    (hζ : riemannZeta ρ = 0) : ρ.re = 1 / 2 :=
  LiteratureInputs.platt_trudgian_verified_below ρ him hle hζ

/-- **An explicit zero-density estimate on an interval**, Farzanfard's thesis, Corollary 4.50:
for `T₂ ≥ 3×10¹²` and `σ ∈ [0.75, 1]`,
`N(σ,T₁,T₂) ≤ 12.45321·T₂^{(8/3)(1-σ)}(log T₂)^{5-2σ} + 3.869(log T₂)²`.

### Summary of Proof
Not proved here — the field `LiteratureInputs.farzanfard_zero_density_interval`, recording an
external result verbatim. It is the Ingham/Ramaré zero-density argument in the form given by
Kadiri–Lumley–Ng, refined in the cited thesis and extended there from a half-line count to an
interval count.

### Lean Notes
Stated in this project's `α = 1 - σ` convention, in which `Nrect T₁ T₂ α` counts zeros with
`Re ρ > 1 - α`; so `σ ∈ [0.75,1]` becomes `α ∈ [0, 1/4]`, and the exponents `(8/3)(1-σ)` and
`5-2σ` become `(8/3)α` and `3+2α`.

**Why this source rather than `\cite{KadiriLumleyNg2018}` directly.** The tex cites
Kadiri–Lumley–Ng at this point, but their `N(σ,T)` counts zeros with `0 < Im ρ < T` — a count from
height `0`, not on an interval — and their Theorem 1.1 leaves the constants `C₁, C₂` as functions
of six parameters fixed only in the paper's numerical tables. The thesis's Corollary 4.50 is the
interval form with both constants made numeric, which is what `Nrect` needs.

**The `T₁` hypothesis is the conservative reading.** Corollary 4.50 displays only `T₂ ≥ 3×10¹²`;
its ambient Theorem 4.46 also carries `T₁ > H₀`, with `H₀` the RH-verification height, taken as
`3×10¹²` in the thesis's numerics. The statement here therefore requires `3×10¹² ≤ T₁ ≤ T₂`.
Relaxing the
lower endpoint is not a matter of a sharper citation: for `α < 1/2` every zero counted by `Nrect`
has `Re ρ > 1/2`, so by `platt_trudgian_verified_below` there are none below `3×10¹²` at all, and
`Nrect T₁ T₂ α = Nrect (max T₁ H₀) T₂ α`. `MainTheorem.Nrect_eq_zero_of_le_H0` proves the special
case in which the *whole* window lies below `H₀` (`T₂ ≤ H₀`, giving `Nrect = 0`); the
window-splitting form wanted here, with `T₁ < H₀ < T₂`, is not proved anywhere.

**Coverage: `α ∈ [0,1/4]` only.** Corollary 4.50 is stated for `σ ∈ [0.75,1]`. Both
`MainTheorem.mainJensen` (Theorem 2) and `mainLittlewood` (Theorem 3) assume `α < 1/6`, so every
consumer sits comfortably inside `[0,1/4]`. The range `α ∈ [1/4,1/2)` is intrinsically hard for
an Ingham-type estimate — as `α → 1/2` the count approaches the full zero count in the strip — so
covering it would need a different tool (plausibly the trivial `N(t+h) - N(t-h)` bound), not a
sharper constant here.

**This statement is deliberately the LOSSY form, and a sharper one is available.**
Corollary 4.50 is
doubly weakened relative to its own Theorem 4.46:

* its `U = 12.45321` and `V = 3.869` are the *maxima* over all of `σ ∈ [0.75,1]` (`U` attained at
  the top end, `V` at the bottom). The thesis's Table A.1 gives them per `σ`; in the range this
  project needs, `U` is roughly half — `6.19` at `α = 1/7`, `7.31` at `α = 1/9`.
* it quotes equation (4.160), which is (4.159) weakened by `log(1+y) ≤ y`. The sharper (4.159),
  `N ≤ (T₂-T₁)(log T₂)·log(1 + Y/(T₂-T₁)) + V(log T₂)²` with
  `Y = U·T₂^{(8/3)α}(log T₂)^{2+2α}`, has a leading term *linear in the interval length*
  `T₂-T₁ = 2h` — the same shape as `U_J`'s own `2h` factor — instead of `h`-independent. For the
  short intervals here that is a real gain whenever `Y/(2h)` is not small.

Together those are worth a factor of `3.5` at `α = 1/7`, `2.2` at `α = 1/8`
(`Code/verify_kln_large_h_case.py`, Part 4). That is **not enough** to close the branch — see
`MainTheorem.lean`'s module docstring and `Nrect_le_zero_density_bound` — so the lossy form is
kept here as the simpler statement until something is actually proved from it. Anyone attempting
that branch should start from (4.159) with per-`σ` constants instead.

### References
External: Golnoush Farzanfard, *Explicit zero density for the Riemann zeta function*, MSc thesis,
University of Lethbridge, 2025, Corollary 4.50 (equation (4.180)), specialising her Theorem 4.46;
`\cite{Farzanfard2024}`. Compare Kadiri–Lumley–Ng, *Explicit zero density for the Riemann
zeta function*, J. Math. Anal. Appl. **465** (2018) 22–46, Theorem 1.1 — the half-line antecedent
the tex cites as `\cite{KadiriLumleyNg2018}`.
tex: the `h > t^{2/3}` branch in the proofs of `\ref{thm:main-jensen}` (Theorem 2) and
`\ref{thm:main-littlewood}` (Theorem 3).

**The sharper LOG form, and what it buys.** Corollary 4.50 is
Theorem 4.46 / Remark 4.47 eq. (4.165),
`N(σ,T₁,T₂) ≤ (T₂-T₁)·log T₂·log(1 + U T₂^{(8/3)(1-σ)} (log T₂)^{4-2σ}/(T₂-T₁)) + V log²T₂`
(`T₁ > H₀ = 3·10¹²`, `T₂ > T₀`; `U(σ), V(σ)` from the thesis's Table A.1, maximised over
`σ ∈ [0.75,1]` to `12.45321`, `3.869`), weakened by `log(1+y) ≤ y`. The author suggested the
log form because its shape is `O(h log t)`, like `U_J`/`U_L`.
`Code/indep_mpmath_zero_density_4165.py` quantifies it: the ratio to `U_J`/`U_L` is
decreasing in `h`, so `h = t^{2/3}` stays the binding case, where at `α = 1/6`, `t = 3·10¹²` the
log form improves the ratio from `139` to `17.4` (uniform `U,V`) or `13.5` (per-σ), and lowers
the crossover height from `10^26.1` to `10^23.9` (Jensen) / `10^24.6` (Littlewood) — still far
above `10¹²`; `α ≤ 1/9` closes from `3·10¹²` with per-σ constants. Moving the case boundary to
`h = t^θ` closes the branch for all `t ≥ 3·10¹²` once `θ ≥ 0.82` (`α = 1/6`), `0.76` (`1/7`),
`0.71` (`1/8`). Using (4.165) in Lean would mean a second `LiteratureInputs` field in this shape
(and, for the per-σ constants, the thesis code run at `σ = 5/6, 6/7, …`).

### Dependencies
**Depends on:** `Nrect`.
**Used by:** `MainTheorem.Nrect_le_zero_density_bound`, the `(t-h,t+h)` instance intended for
the `h > t^{2/3}` branch of `MainTheorem.mainJensen` and `mainLittlewood`; see
`Code/verify_kln_large_h_case.py` for why that branch does not close as the tex sketches it. -/
theorem farzanfard_zero_density_interval {α T₁ T₂ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) (1 / 4)) (hT₁ : 3 * 10 ^ (12 : ℕ) ≤ T₁) (hT₁₂ : T₁ ≤ T₂) :
    (Nrect T₁ T₂ α : ℝ)
      ≤ 12.45321 * T₂ ^ ((8 : ℝ) / 3 * α) * Real.log T₂ ^ (3 + 2 * α)
        + 3.869 * Real.log T₂ ^ (2 : ℕ) :=
  LiteratureInputs.farzanfard_zero_density_interval hα hT₁ hT₁₂

/-- **Bellotti–Wong, Corollary 1.3 (second estimate): `|N(T) − M(T)| ≤ 0.097 log T + 4.954` for
`T ≥ 1`**, where `M(T) = (T/2π) log(T/(2πe))` (`Common.RealLogBounds.bwM`) is the main term of
the Riemann–von Mangoldt formula.

### Summary of Proof
Not proved here — the field `LiteratureInputs.bellotti_wong_cor_1_3`, recording the cited result
as stated. `N` is the project's counting function `Definitions.N` (zeros with `0 < Im ρ ≤ T`,
with multiplicity), which is the `N(T)` of the paper.

### Lean Notes
The cited result itself is what is assumed; its consequence `bellotti_wong_Lbound_le` (the lower
bound `L(h,t) ≤ N(t+h) − N(t−h)`) is proved below. The step between them is the inequality
`∫₀^λ −log(1−v²) dv ≤ 2(1−log 2)λ³`, `λ = h/t`, i.e. `2λ − φ(λ) ≤ 2(1−log 2)λ³` for
`φ(λ) = (1+λ)log(1+λ) − (1−λ)log(1−λ)`, which `Common.RealLogBounds.two_mul_sub_bwPhi_le`
proves by a power series.

### References
External: Chiara Bellotti and Peng-Jie Wong, *Counting zeros of Artin L-functions*,
`\cite[Cor. 1.3]{BellottiWong2026}` — the second of the two estimates there, valid for `T ≥ 1`.
tex: the display `|N(t) − (t/2π) log(t/2πe)| < 0.097 log|t| + 4.954` above `\ref{cor:main-jensen}`
(Corollary 4), tex line 201 (stated there with `<`; the hypothesis takes the weaker `≤`).

### Dependencies
**Depends on:** `N`, `Common.RealLogBounds.bwM`.
**Used by:** `bellotti_wong_Lbound_le`. -/
theorem bellotti_wong_cor_1_3 {T : ℝ} (hT : 1 ≤ T) :
    |((N T : ℤ) : ℝ) - bwM T| ≤ 0.097 * Real.log T + 4.954 :=
  LiteratureInputs.bellotti_wong_cor_1_3 hT

/-- **The lower bound `L(h,t)` on the number of zeros in `(t-h, t+h]`**, from Bellotti–Wong:
`N(t+h) - N(t-h) ≥ (log(t/2π)/π - (1-log 2)h²/(πt²))·h - 0.194·log t - 9.908`.

### Summary of Proof
`Common.RealLogBounds.bw_Lbound_of_cor` applied to `bellotti_wong_cor_1_3`. In words: Cor. 1.3 at
`T = t+h` and `T = t-h` gives
`N(t+h) - N(t-h) ≥ M(t+h) - M(t-h) - 0.097(log(t+h) + log(t-h)) - 9.908`;
`log(t+h) + log(t-h) = log(t²-h²) ≤ 2 log t` gives the `-0.194 log t` term; and
`M(t+h) - M(t-h) ≥ (log(t/2π)/π)h - (1-log 2)h³/(πt²)` is `bwM_sub_ge`: with `λ = h/t`,
`M(t+h) - M(t-h) = (h/π)(log t - log 2π) - h/π + (t/2π)φ(λ)`, and the needed
`2λ - φ(λ) ≤ 2(1-log 2)λ³` follows termwise from the power series
`2λ - φ(λ) = Σ_{k≥1} λ^{2k+1}/(k(2k+1))` (`hasSum_two_mul_sub_bwPhi`), the constant
`Σ 1/(k(2k+1)) ≤ 2(1-log 2)` being the `λ → 1⁻` limit of the same identity
(`bw_const_partial_le`).

### Lean Notes
The one nontrivial step between Cor. 1.3 and this statement is
`∫₀^λ -log(1-v²) dv ≤ 2(1-log 2)λ³` for `0 < λ < 1`. The power-series route
(`Common.RealLogBounds.two_mul_sub_bwPhi_le`) avoids both the antiderivative of `log(1-v²)` and
a comparison argument.

**Hypotheses.** `1 ≤ t - h` is what Cor 1.3 needs at *both* endpoints (it holds for `T ≥ 1`), and
it forces `h < t`. Every consumer here has `t > 10¹²` and `h < t`, so this is not restrictive.

The statement is spelled out rather than written via `MainCorollary.Lbound`, because that
definition lives downstream of this file; `MainCorollary.Lbound_le_N_sub_N` restates it in those
terms.

**The `h²` coefficient is the sharp one.** The subtracted term is `(1-log2)h²/(πt²)`, a factor
`2.5595` smaller than the `h²/(4t²)` a cruder estimate gives, hence a *stronger* claim, and that
is exactly what `two_mul_sub_bwPhi_le` proves: Bellotti–Wong Cor. 1.3 supplies only the tail
`-0.194 log t - 9.908`; the `h²` term comes from the exact identity
`M(t+h)-M(t-h) = (h/π)log(t/2π) + (t/2π)∫₀^λ log(1-v²)dv`, and a subtracted `C·h·λ²` is
admissible exactly when `∫₀^λ -log(1-v²)dv ≤ 2πC·λ³`; the ratio `(∫₀^λ -log(1-v²))/λ³` is
monotone increasing with limit `2-2log2`, so `C* = (1-log2)/π` is sharp and valid on all of
`0 < λ < 1` (`Code/verify_Lht_sharp_constant.py`). The tex's own `L(h,t)` display carries the
same coefficient. Note the `π` bookkeeping: this coefficient is `(1-log2)/π` *inside* `L`, but the
Corollaries display `L·π/(h log t)`, where it appears as `(1-log2)/(t^{2/3}log t)` with the `π`
cancelled — not `(1-log2)/(π t^{2/3} log t)`.

### References
External: Chiara Bellotti and Peng-Jie Wong, *Counting zeros of Artin L-functions*,
`\cite[Cor. 1.3]{BellottiWong2026}` — the second of the two estimates there, valid for `T ≥ 1`.
tex: the `L(h,t)` display just above `\ref{cor:main-jensen}` (Corollary 4), tex line 203.

### Dependencies
**Depends on:** `N`, `bellotti_wong_cor_1_3`, `Common.RealLogBounds.bw_Lbound_of_cor`,
`Common.RealLogBounds.bwM`.
**Used by:** `MainCorollary.Lbound_le_N_sub_N`. -/
theorem bellotti_wong_Lbound_le {h t : ℝ} (hh : 0 < h) (ht : 1 ≤ t - h) :
    (Real.log (t / (2 * Real.pi)) / Real.pi
          - (1 - Real.log 2) * h ^ 2 / (Real.pi * t ^ 2)) * h
        - (0.194 : ℝ) * Real.log t - 9.908
      ≤ ((N (t + h) : ℝ) - (N (t - h) : ℝ)) :=
  bw_Lbound_of_cor (Nf := fun T => ((N T : ℤ) : ℝ)) (fun _T hT => bellotti_wong_cor_1_3 hT) hh ht
