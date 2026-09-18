/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Background.ExternalFacts
import ZerosInShortIntervals.Background.PhragmenLindelofSetup

/-! # Appendix: explicit bounds for `log|ζ|` and `log Γ` (`\S sec:background`)

This file formalizes the Appendix of `ZerosInShortIntervals.tex`. The interpolation
`Proposition \ref{prop:interpolation}` (Proposition 35) is this paper's own result, built from
the external bounds in `ZerosInShortIntervals.Background.ExternalFacts` via the Phragmén–Lindelöf
theorem of `\cite{Fiori2026}`. Likewise `Lemma \ref{lem:zetalessthanhalf}` (Lemma 36, via the
functional equation, already available in Mathlib as `riemannZeta_one_sub`) and
`Lemma \ref{lemma:argGamma}` (Lemma 37, via Brent's explicit shifted Stirling expansion,
`ExternalFacts.brent_stirling_shifted_expansion`) are this paper's own derivations.

**The four `interpolated_bound_*` cases.** Each is an instance of a two-point
interpolation for `ζ`, the applied form of `\cite[Theorem 7]{Fiori2026}` (whose derivation from
`ExternalFacts.fiori_phragmenLindelof` is set up in full in `PhragmenLindelofSetup.lean`, applied
to `(s-1)ζ(s)` rather than `ζ(s)` to keep the pole out of the compact range — see the individual
theorems' docstrings). Cases (1a), (1b) and (2) go through the generic, constant-boundary `r = 3`
wrapper `PhragmenLindelofSetup.fiori_zeta_interpolation`; case (1c) — whose true `σ = 1/2` boundary
bound `0.470795|t|^{1/6}\log|t| + 4.04972|t|^{1/6}` is affine in a log, not a constant times a
power — goes through the dedicated `r = 4` instantiation
`PhragmenLindelofSetup.fiori_zeta_interpolation_1c` instead, whose second function `G_1 = G1shift`
carries that affine boundary directly (the appendix's own `G_1` is affine in a log in the same
way, though its displayed arguments differ — see `interpolated_bound_1c`). All four are
then pushed through a `log`-form bridge:
`PhragmenLindelofSetup.log_bound_of_interp` (cases 1a/1b), `log_bound_of_interp_1c` (case 1c, which
additionally converts the affine boundary's own `\log|t| → \log|T|` window), or
`log_bound_of_interp_self` (case 2, stated at the ordinate itself, no window conversion needed).

**The "compact range" numeric obligation of each case is isolated as its own named `_hcompact`
statement** (`interpolated_bound_1a_hcompact`, `_1b_hcompact`, `_1c_hcompact`, and — split by
`k` — the five pieces behind `_2_hcompact`), each a single closed claim with no free variables
beyond the universally quantified `t, σ` (and `k` for case 2). None of them can be proved inside
Lean: this Mathlib snapshot has no certified interval arithmetic for `ζ`. They are therefore
fields of the two hypothesis classes declared in this file, `InterpolationCertificates` and
`Hcompact2Certificates`, and their mathematical content is certified outside Lean by arb ball
arithmetic in `Code/indep_arb_hcompact.sage` (which prints `ALL CERTIFIED`), rechecked pointwise
by `Code/indep_mpmath_hcompact.py`. `_1c_hcompact` uses the `r = 4` layout (and the wider
`|t| ≤ 4e+1` compact range `interpolated_bound_1a` also needs, for the same reason: two of its
four functions carry genuine `σ`-monotonicity) — `G_0`, `G_2` of that layout are exactly linear
so their infima are unconditional closed-form endpoint values, while `G_1 = G1shift` and
`G_3 = GPL` are certified by the same subdivision technique as the r = 3 cases' log-type function.

**The `min_σ |G_i(σ+it)|` of the paper is written `⨅ τ : Set.Icc a b, ‖G i ((τ:ℝ) + t*I)‖`,** a
**subtype** infimum, whose index type is the compact interval itself and is nonempty whenever
`a ≤ b`. The bounded-binder spelling `⨅ τ ∈ Set.Icc a b, …` would mean something else entirely —
see `iInf_mem_Icc_eq_zero` immediately below, which proves it collapses to `0` over `ℝ`, and
`ExternalFacts.fiori_phragmenLindelof`'s Lean Notes.

**Two statements here carry a hypothesis the tex leaves tacit**, in both cases because Lean's
`Real.log 0` is the finite junk value `0` rather than `-∞`:

* `zetalessthanhalf_upper` and `_upper_tight` are stated for `σ ∈ [0,1/2]`, so `1-σ` lies in the
  critical strip; at a hypothetical zero of `ζ(1-σ+it)` both `log` terms would become `0` and the
  claim would assert RH on that range. Both carry `hz : ζ(1-σ+it) ≠ 0`, exactly what the
  functional-equation argument needs and what the tex assumes under its `log|0| = -∞` convention.
  The `_lower` pair needs no such hypothesis (`σ ∈ [-1,0]` puts `1-σ ∈ [1,2]`, where
  `riemannZeta_ne_zero_of_one_le_re` applies). Full argument in `zetalessthanhalf_upper`.
* `argGamma` is stated on the analytic branch `logGammaAnalytic` rather than the principal
  `Complex.arg`, with main term `-δπ/4 + δ²/(4t)` and error `0.21/t³` — the tex's own constants.
  The tex writes `\arg\Gamma` without naming a branch; the analytic one is the only reading under
  which the statement holds, and on the principal branch, or with a main term that drops the
  constant `-δπ/4`, it is false. See that declaration's Lean Notes.

Everything else — holomorphy, conjugate symmetry, growth envelopes, monotonicity, the exponent
bookkeeping, the coefficient identities including the general-`k` identity
`PhragmenLindelofSetup.yang_interp_coeff_eq` behind case (2), and the whole Stirling development
behind Lemmas 36 and 37 — is proved outright.
-/

/-! ## Guard lemmas: the `⨅ τ ∈ Set.Icc a b, …` collapse

Neither lemma below is used anywhere, and that is the intended state. They are true general facts
about the *bounded-binder* notation, which over `ℝ` means `0` rather than the intended minimum
over `[a,b]`; every statement in this file uses the subtype infimum instead. They are kept so
that anyone tempted to write `⨅ τ ∈ Set.Icc a b, …` here meets a *proof* that the notation means
`0` rather than having to rediscover it. **Do not "repair" these two statements to the subtype
form** — they would then be false, and would document nothing. -/

/-- **The `⨅ x ∈ Set.Icc a b, g x` notation collapses to `0` over `ℝ`.**

For a nonnegative `g` and any witness `c ∉ Set.Icc a b`, the "bounded infimum" notation
`⨅ x ∈ s, g x` — which unfolds to `⨅ x : ℝ, ⨅ _ : x ∈ s, g x` — evaluates to `0`, not to the
infimum of `g` over `s`.

### Summary of Proof
`0` is a lower bound (`Real.iInf_nonneg` twice), so the value is `≥ 0`. For the reverse, the
outer infimum is at most its value at the witness `c`, and there the inner index type
`c ∈ Set.Icc a b` is empty, so `Set.range_eq_empty` turns the inner `iInf` into `sInf ∅`, which is
`0` by `Real.sInf_empty` — `ℝ` is only conditionally complete, so an empty infimum is `0`, not
`⊤`. The `BddBelow` side condition of `ciInf_le` is supplied by the same nonnegativity.

### Lean Notes
This is the standard trap for `⨅ x ∈ s, f x` in a conditionally complete order. In a complete
lattice the same notation behaves as intended, which is why it is easy to write by mistake. What
this file uses instead is the subtype infimum `⨅ x : Set.Icc a b, g ↑x`, whose index type is
nonempty for `a ≤ b`; this lemma is retained purely as a guard.

### References
No tex counterpart. The mathematics this notation would mis-encode is
`\cite[Theorem 7]{Fiori2026}`'s `min_σ |G(σ+it)|`.

### Dependencies
**Depends on:** none.
**Used by:** `norm_comp_iInf_Icc_eq_zero`. -/
theorem iInf_mem_Icc_eq_zero {a b : ℝ} {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) {c : ℝ}
    (hc : c ∉ Set.Icc a b) : (⨅ x ∈ Set.Icc a b, g x) = 0 := by
  have hbdd : BddBelow (Set.range fun x : ℝ => ⨅ _ : x ∈ Set.Icc a b, g x) :=
    ⟨0, by rintro y ⟨x, rfl⟩; exact Real.iInf_nonneg fun _ => hg x⟩
  refine le_antisymm ?_ (Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => hg _)
  have hemp : IsEmpty (c ∈ Set.Icc a b) := ⟨hc⟩
  have hzero : (⨅ _ : c ∈ Set.Icc a b, g c) = 0 := by
    change sInf (Set.range fun _ : c ∈ Set.Icc a b => g c) = 0
    rw [Set.range_eq_empty, Real.sInf_empty]
  calc (⨅ x ∈ Set.Icc a b, g x) ≤ (⨅ _ : c ∈ Set.Icc a b, g c) := ciInf_le hbdd c
    _ = 0 := hzero

/-- **Any `⨅ τ ∈ Set.Icc a b, ‖G (τ + t*I)‖` written with the bounded binder is `0`.**

The specialisation of `iInf_mem_Icc_eq_zero` to the shape this file's statements are about: any
complex `G`, any strip `[a,b]` with `b < 2`, any ordinate `t`.

### Summary of Proof
`iInf_mem_Icc_eq_zero` with `g := fun τ => ‖G (τ + t*I)‖` (nonnegative, being a norm) and witness
`c := 2`, which lies outside `[a,b]` because `b < 2`.

### Lean Notes
`b < 2` is a convenience, not a restriction: every strip in this file is inside `[0,1]`. Any
witness outside `[a,b]` would do, and one always exists since `Set.Icc a b ≠ Set.univ`.

The bounded binder appears nowhere in this file except in this lemma and
`iInf_mem_Icc_eq_zero` themselves, so this statement is deliberately unused: a guard against
introducing the notation, not a working part of any proof.

### References
No tex counterpart.

### Dependencies
**Depends on:** `iInf_mem_Icc_eq_zero`.
**Used by:** none (kept as a guard; see Lean Notes). -/
theorem norm_comp_iInf_Icc_eq_zero (G : ℂ → ℂ) {a b : ℝ} (hb : b < 2) (t : ℝ) :
    (⨅ τ ∈ Set.Icc a b, ‖G (τ + t * Complex.I)‖) = 0 :=
  iInf_mem_Icc_eq_zero (fun _ => norm_nonneg _) (c := 2)
    (by simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith)

/-- **`(4e+1)² ≤ 140.9712`**, the `σ`-free half of the case (1a) and (1c) numerator bounds.

Each of those bounds has the shape `2((X+σ)² + (X+2-σ)²) + (2-2σ)²` or
`2((X+σ+1)² + (X+1-σ)²) + (2σ)²` with `X = 4e`, and both collapse by `ring` to
`4(X+1)² + 8·dev²` with `dev = 1-σ` resp. `σ`.  Splitting the constant off like this leaves
each call site linear in the atoms `{e, e², σ, σ²}`, so it closes by `linarith only` with one
supplied product and no nonlinear search.

**The decimal is load-bearing.**  `hnum2` of `interpolated_bound_1c_tight_simple` clears its
target `568` by only `0.034`, and the weaker `e² < 7.39` that the nested blocks of this file use
would push `4(4e+1)² + 8(25/49)` to `568.027`.  Do not relax `7.3890562` to `7.39` here.

### Summary of Proof
`(4e+1)² = 16e² + 8e + 1` is linear in the atoms `e` and `e²`, so
`16(7.3890562) + 8(2.7182818286) + 1 < 140.9712` is a `linarith` step.

### Lean Notes
`linarith only`, not `nlinarith`: linarith's own ring normalisation expands the square, leaving
nothing nonlinear to search for.

### References
No tex counterpart; an arithmetic step inside `Proposition \ref{prop:interpolation}`
(Proposition 35), cases (1a) and (1c).

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1a_tight_simple`, `interpolated_bound_1c_tight_simple`. -/
private theorem four_exp_one_add_one_sq_le : (4 * Real.exp 1 + 1) ^ 2 ≤ 140.9712 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 1 ^ 2 < 7.3890562 := by nlinarith [Real.exp_pos 1]
  linarith only [he, he2]

/-- **`(e+1)² ≤ 13.8257`**, the `σ`-free half of the case (2) numerator bound.

The case (2) window carries `X = e` rather than `4e`, but the same `ring` identity applies:
`2((e+σ)² + (e+2-σ)²) + (2-2σ)² = 4(e+1)² + 8(1-σ)²`.  See `four_exp_one_add_one_sq_le` for
why the split is worth making.

### Summary of Proof
`(e+1)² = e² + 2e + 1 < 7.3890562 + 2(2.7182818286) + 1 < 13.8257`, linear in `e` and `e²`.

### Lean Notes
As in `four_exp_one_add_one_sq_le`.  Here the margin against the `56` target is `0.044`, so
`e² < 7.39` would in fact have sufficed; the tighter constant is used only for uniformity.

### References
No tex counterpart; an arithmetic step inside `Proposition \ref{prop:interpolation}`
(Proposition 35), case (2).

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_2_tight_simple`. -/
private theorem exp_one_add_one_sq_le : (Real.exp 1 + 1) ^ 2 ≤ 13.8257 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 1 ^ 2 < 7.3890562 := by nlinarith [Real.exp_pos 1]
  linarith only [he, he2]

/-- **The compact-window certificates of `Proposition \ref{prop:interpolation}` (Proposition 35),
cases (1a), (1b) and (1c), as a hypothesis class.**

Fiori's Phragmén–Lindelöf interpolation needs, besides the two boundary bounds, that the
interpolated majorant already dominates `|(s-1)ζ(s)|` on a compact window of `t` — the `hcompact`
hypothesis.  On that window the claim is a finite check, and it is one this project certifies
outside Lean.

**Evidence.** `Code/indep_arb_hcompact.sage` verifies each claim by **arb ball arithmetic**
over a covering of the window by boxes, and prints `ALL CERTIFIED`: 125 boxes for (1a), 264 for
(1b), 137 for (1c).  `Code/indep_mpmath_hcompact.py` re-checks the same claims pointwise by an
independent route.  Certified interval arithmetic for `ζ` does not exist inside Lean, which is why
these are hypotheses and not proofs.

### Summary of Proof
A class; no proof.

### Lean Notes
The three fields are the three theorems' statements verbatim; each theorem reads its content off
this class and keeps its own provenance docstring.

The paper's `min_σ` is the **subtype** infimum `⨅ τ : Set.Icc a b, …`.  The bounded binder
`⨅ τ ∈ Set.Icc a b, …` would collapse to `0` over `ℝ`, making the right-hand side identically
zero; see the module docstring and `iInf_mem_Icc_eq_zero`.

### References
`Code/indep_arb_hcompact.sage`, `Code/indep_mpmath_hcompact.py`;
`Assumptions.txt`, Part 1 (the numerical certificates).

### Dependencies
**Depends on:** `PhragmenLindelofSetup.interpG`, `interpα`, `interpβ`, `interpG1c`, `interpα1c`,
`interpβ1c`.
**Used by:** `interpolated_bound_1a_hcompact`, `interpolated_bound_1b_hcompact`,
`interpolated_bound_1c_hcompact`. -/
class InterpolationCertificates : Prop where
  /-- Case (1a), the sub-Weyl window `|t| ≤ 4e+1` with `σ ∈ [1/2, 5/7]`.  arb-certified over 125
  boxes (`Code/indep_arb_hcompact.sage`). -/
  interpolated_bound_1a_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 66.7 1.546 (27 / 164) (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (27 / 164) 0 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2))
  /-- Case (1b), the Revers-subconvexity window `|t| ≤ 3` with `σ ∈ [1/2, 5/7]`.  arb-certified
  over 264 boxes. -/
  interpolated_bound_1b_hcompact :
    ∀ t : ℝ, |t| ≤ 3 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 0.611 1.546 (1 / 6) (1 / 14) 16 i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (1 / 6) 1 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2))
  /-- Case (1c), the four-factor variant on `|t| ≤ 4e+1`.  arb-certified over 137 boxes
  (`Code/indep_arb_hcompact.sage`).

  The constants `0.470795` and `4.04972` are Revers Remark 3.1's, assumed as
  `Hypotheses.LiteratureInputs.revers_remark31`, and this case is what formalizes the SECOND
  alternative of the tex's Remark `\ref{rem:altcoefficients}` (Remark 7),
  `v₀'' = log(0.470795 + 4.04972/log|T|)`.  The first alternative, the triple
  `(27/164, 0, log 66.7)`, is case (1a) above and is developed in
  `Jensen/JensenScaleConstantsAlt.lean`. -/
  interpolated_bound_1c_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG1c 1.546 0.470795 4.04972 (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα1c (1 / 6) i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ1c (1 / 14) i * (σ - 1 / 2) / (5 / 7 - 1 / 2))

/- The unproved inputs used below enter through the hypothesis classes of
`ZerosInShortIntervals/Hypotheses.lean` and the two declared in this file.  Lean includes an
instance-implicit section variable in every theorem in scope, so some statements carry a binder
they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]

/-- **The numeric obligation of `interpolated_bound_1a`, isolated** as the class field
`InterpolationCertificates.interpolated_bound_1a_hcompact`.

### Summary of Proof
Not proved here. This is the tex's own "we verify numerically … that the minimum value of the two
boundary bounds is larger than the maximum value of `|ζ(σ+it)|`" over the compact range — the
hypothesis Phragmén–Lindelöf needs before it can propagate the edge bounds into the strip.
Formally it is exactly `hcompact` from `PhragmenLindelofSetup.fiori_zeta_interpolation`,
instantiated at `a=1/2, b=5/7, A=66.7, B=1.546, p=27/164, q=1/14, ra=0, rb=1, Q=4e, T0=4e+1`.

### Lean Notes
A single closed numeric statement, with no free variables beyond the universally quantified
`t, σ`. Isolating it makes `interpolated_bound_1a` fully proved modulo this one numeric fact.
Turning it into a proof term needs certified interval arithmetic for `ζ` inside Lean, which this
Mathlib snapshot does not have; the interpolant half would need only the already-proved
`*_lower_const` lemmas.

Structure such a proof could exploit: `log RHS` is **affine in σ** — every base depends on `t`
alone and every exponent is affine in `σ` — so the σ-infimum is always at an endpoint, no
interior search. At `σ = 5/7` the product telescopes, since `C0·(B/C0)^(q·(1/q)) = B`, to
`RHS(5/7,t) = B · inf|s| · (inf|1-s|)^{1/14} · inf|GPL|`. And `t → -t` needs no separate
treatment: `|(s-1)ζ(s)|` and every `|G_i|` are conjugation-invariant.

**The decoupled split — comparing `sup_box |(s-1)ζ(s)|` against `inf_box RHS`, so that the two
sides can be certified separately — needs `t`-boxes of width `2`, not `4`.** Width `2` gives 6
boxes and worst `U/L = 0.7014`; width `1` gives `0.5347`; width `4` FAILS at `U/L = 1.4758`,
because `sup LHS` is attained near `t = 4` while `inf RHS` is attained at `t = 0`, where the RHS
at `σ = 5/7` is `1.7483` (by hand from the telescoped form, `1.546 × 0.5 × 0.9144 × 2.4734`).
Reference values: at `t = 0`, `sup LHS = 0.8411 < 1.7483 = inf RHS`; at `t = 4`,
`2.5801 < 17.3940`; at `t = 8`, `10.3623 < 38.2615`.

### References
tex: `Proposition \ref{prop:interpolation}` (Proposition 35), case (1a).
External: Fiori's Phragmén–Lindelöf paper, §4.3 "Third example".

**Independent numeric check.**
* `Code/verify_hcompact_1a_independent.py` and `Code/indep_mpmath_hcompact.py` (mpmath, written
  from this statement): pointwise worst ratio `LHS/RHS = 0.4811` at `σ = 5/7`, `t = 0`; the
  decoupled split behaves as recorded above.
* `Code/indep_arb_hcompact.sage` (arb, **certified**): the inequality is verified on `125`
  adaptively bisected `(σ,t)`-boxes covering `σ ∈ [1/2,5/7]`, `t ∈ [0, 4e+1]` (`t < 0` by
  conjugation symmetry), with the `ζ` side enclosed by a second-order Taylor form and the `G` side
  by `σ`-endpoint evaluation (log RHS is affine in `σ`). That run is the certificate this
  hypothesis stands for.

### Dependencies
**Depends on:** `InterpolationCertificates`, `PhragmenLindelofSetup.interpG`, `interpα`,
`interpβ`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`. -/
theorem interpolated_bound_1a_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 66.7 1.546 (27 / 164) (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (27 / 164) 0 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2)) :=
  InterpolationCertificates.interpolated_bound_1a_hcompact

/-- **`Proposition \ref{prop:interpolation}` (Proposition 35), case (1a).** For `1/2 ≤ σ ≤ 5/7`,
`log|ζ(σ+it)| < (47/123 - 107/246σ)log|T| + 14/3(σ-1/2)log log|T| + …  + 3/T`.

**Rests on one hypothesis**: `interpolated_bound_1a_hcompact`, the field
`InterpolationCertificates.interpolated_bound_1a_hcompact` — a closed numeric fact certified
outside Lean, with the pointwise claim independently rechecked in
`Code/verify_hcompact_1a_independent.py` at worst ratio `0.4811`.

### Summary of Proof
Interpolate two boundary bounds through Phragmén–Lindelöf. At `σ = 1/2` use Patel–Yang's sub-Weyl
bound `‖ζ(1/2+it)‖ ≤ 66.7|t|^{27/164}` (so `A = 66.7`, `p = 27/164`, `ra = 0`); at `σ = 5/7` use
Yang's critical-strip bound at `k = 4`, `‖ζ(5/7+it)‖ ≤ 1.546|t|^{1/14}log|t|` (so `B = 1.546`,
`q = 1/14`, `rb = 1`, using `1 - 4/(2⁴-2) = 5/7` and `1/(2⁴-2) = 1/14`). Then take logs and
convert the ordinate window.

The displayed coefficients come out exactly: with weights `w_a = 14/3(5/7-σ)` and
`w_b = 14/3(σ-1/2)`, one gets `27/164·w_a + 1/14·w_b = 47/123 - 107/246σ` and
`0·w_a + 1·w_b = 14/3(σ-1/2)`.

### Lean Notes
Proved via `PhragmenLindelofSetup.fiori_zeta_interpolation`, the applied form of Fiori's own
"Third example" (§4.3 of his Phragmén–Lindelöf paper), then pushed through the `log`-form bridge
`PhragmenLindelofSetup.log_bound_of_interp`. Everything is proved outright except the isolated
numeric fact `interpolated_bound_1a_hcompact`.

**The compact range here is `|t| ≤ 4e+1 = 11.8731…`**, the same compact region the tex names for
case (1). This is the only one of the four cases with `ra < rb`, hence the only one that actually
invokes the `σ`-monotonicity of `‖GPL Q‖`; and `PhragmenLindelofSetup.GPL_anti_of_large_t` shows
that monotonicity needs `|t| > Q+1`, which at `Q = 4e` is `11.8731…`.

The threshold is not an artifact. At `Q = 4e` on `σ ∈ [1/2,5/7]`, `‖GPL‖` is genuinely
**increasing** in `σ` for `|t| ≲ 10.2` — at `t = 3` it is `2.504520` at `σ=1/2` against
`2.505007` at `σ=5/7`, so the monotonicity hypothesis really does fail below the threshold and
the certified box has to cover all of `|t| ≤ 4e+1`. Cases (1b) and (2) have `ra = rb`, so their
monotonicity hypothesis is vacuous and their compact range stays `|t| ≤ 3`; case (1c) has
`ra ≠ rb` in its own `r = 4` layout and so shares this case's `|t| ≤ 4e+1`.

### References
tex: `Proposition \ref{prop:interpolation}` (Proposition 35), case (1a).
External: Patel–Yang `\cite{PatelYang2024}`; Yang `\cite{Yang2024}`; Fiori's
Phragmén–Lindelöf paper §4.3.

### Dependencies
**Depends on:** `GPL_anti_of_large_t`, `GPL_ge_log`, `fiori_zeta_interpolation`,
`interpolated_bound_1a_hcompact`, `log_bound_of_interp`, `patel_yang_subweyl_bound`,
`twenty_lt_log`, `yang_critical_strip_bound`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1a_pointwise`. -/
theorem interpolated_bound_1a {T t σ : ℝ} (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (47 / 123 - 107 / 246 * σ) * Real.log |T| + 14 / 3 * (σ - 1 / 2) * Real.log (Real.log |T|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 66.7 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + 3 / T := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hT0 : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have htpos : (0:ℝ) < t := by linarith [ht.1]
  have hatt : |t| = t := abs_of_pos htpos
  have ht3 : (3:ℝ) ≤ |t| := by rw [hatt]; linarith [ht.1]
  -- weights: `w_a = 14/3(5/7-σ)`, `w_b = 14/3(σ-1/2)`
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hwb1 : 14 / 3 * (σ - 1 / 2) ≤ 1 := by linarith
  -- the interpolated bound, from Fiori's PL theorem in applied form
  have hinterp := fiori_zeta_interpolation (a := 1 / 2) (b := 5 / 7) (A := 66.7)
      (B := 1.546) (p := 27 / 164) (q := 1 / 14) (ra := 0) (rb := 1) (Q := 4 * Real.exp 1)
      (T0 := 4 * Real.exp 1 + 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two])
      (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (fun _ => GPL_anti_of_large_t _ _ _ (by positivity)
        (by nlinarith [Real.exp_one_gt_two]) (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      -- boundary bound at `σ = 1/2`: Patel–Yang's sub-Weyl bound, reflected to `t ≤ -3`
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        push_cast
        rw [Real.rpow_zero, mul_one]
        exact patel_yang_subweyl_bound ht')
      -- boundary bound at `σ = 5/7`: Yang's `k = 4` bound (`1 - 4/(2⁴-2) = 5/7`, `1/(2⁴-2) = 1/14`)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        rw [Real.rpow_one]
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      -- **compact range**: the sole numeric obligation, isolated as
      -- `interpolated_bound_1a_hcompact`
      interpolated_bound_1a_hcompact
      σ ⟨hσ0, hσ1⟩ t (by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : Real.exp 1 ^ 2 < 7.39 := by nlinarith
        have hTb : (10:ℝ) ^ (12:ℕ) < T := hT
        have hTn : (1000000000000:ℝ) < T := by norm_num at hTb; linarith
        rw [hatt]
        nlinarith [ht.1, hTn])
  rw [hwa, hwb] at hinterp
  have hlogw : (0:ℝ) * (14 / 3 * (5 / 7 - σ)) + 1 * (14 / 3 * (σ - 1 / 2))
      = 14 / 3 * (σ - 1 / 2) := by ring
  rw [hlogw] at hinterp
  -- feed it to the log-form bridge with `A := 66.7^{w_a}`, `B := 1.546^{w_b}`
  have hbridge := log_bound_of_interp (L := ‖riemannZeta (σ + t * Complex.I)‖)
      (A := (66.7 : ℝ) ^ (14 / 3 * (5 / 7 - σ))) (B := (1.546 : ℝ) ^ (14 / 3 * (σ - 1 / 2)))
      (c := 27 / 164 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2)))
      (w := 14 / 3 * (σ - 1 / 2)) (T := T) (t := t)
      (norm_nonneg _) (by positivity) (by positivity) hT ht
      (by nlinarith) (by nlinarith) hwb0 hwb1
      -- `hnn`: every summand is nonnegative here (`66.7, 1.546 > 1` and the coefficient is `> 0`)
      (by
        have hlT : 20 < Real.log |T| := by
          rw [abs_of_pos (by linarith : (0:ℝ) < T)]; exact twenty_lt_log hT
        have hllT : 0 < Real.log (Real.log |T|) := Real.log_pos (by linarith)
        have h1 : Real.log ((66.7 : ℝ) ^ (14 / 3 * (5 / 7 - σ))) = 14 / 3 * (5 / 7 - σ) *
            Real.log 66.7 := Real.log_rpow (by norm_num) _
        have h2 : Real.log ((1.546 : ℝ) ^ (14 / 3 * (σ - 1 / 2))) = 14 / 3 * (σ - 1 / 2) *
            Real.log 1.546 := Real.log_rpow (by norm_num) _
        have h3 : (0:ℝ) ≤ Real.log 66.7 := Real.log_nonneg (by norm_num)
        have h4 : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        rw [h1, h2]
        nlinarith)
      hinterp
  -- rewrite the two `Real.log (·^·)` factors and match coefficients
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 66.7),
    Real.log_rpow (by norm_num : (0:ℝ) < 1.546)] at hbridge
  have hcoef : 27 / 164 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 47 / 123 - 107 / 246 * σ := by ring
  rw [hcoef] at hbridge
  linarith [hbridge]

/-- **Tight, pointwise version of `interpolated_bound_1a`**: no `T`-window, explicit `σ`-dependent
`O(1/t²)` error (`fiori_zeta_interpolation_tight`'s log-linear route), and — unlike case (1b) —
**no extra headroom above `T0` at all**: `hnn` holds already at `T0 = 4e+1`, since `A = 66.7 > 1`
and `B = 1.546 > 1` make *every* summand in the log-sum manifestly nonnegative (both boundary
constants have positive log, unlike (1b)'s `A = 0.611 < 1`), so `T1 := T0` works directly.

### Summary of Proof
Same Phragmén–Lindelöf interpolation as `interpolated_bound_1a` — Patel–Yang at `σ = 1/2` against
Yang at `σ = 5/7` — but stated pointwise at the ordinate `t` itself, with no `t → T` window
conversion, and carrying the genuinely `O(1/t²)` error rather than the coarser `3/T`. The sharper
tail comes from using `GPL_le_log_tight` in place of `GPL_le_log` when bounding the log-type
auxiliary function, which keeps the second-order term `(2((Q+σ)²+(Q+2-σ)²)+|2-2σ|²)/(8t² log t)`
explicit instead of absorbing it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL_anti_of_large_t`, `GPL_ge_log`, `fiori_zeta_interpolation_tight`,
`interpolated_bound_1a_hcompact`, `patel_yang_subweyl_bound`, `yang_critical_strip_bound`,
`zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1a_tight_simple`. -/
theorem interpolated_bound_1a_tight {t σ : ℝ} (ht : (4 * Real.exp 1 + 1:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (47 / 123 - 107 / 246 * σ) * Real.log |t| + 14 / 3 * (σ - 1 / 2) * Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 66.7 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2)
            + (2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                / (8 * |t| ^ 2 * Real.log |t|)) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hwb1 : 14 / 3 * (σ - 1 / 2) ≤ 1 := by linarith
  have hinterp := fiori_zeta_interpolation_tight (a := 1 / 2) (b := 5 / 7) (A := 66.7)
      (B := 1.546) (p := 27 / 164) (q := 1 / 14) (ra := 0) (rb := 1) (Q := 4 * Real.exp 1)
      (T0 := 4 * Real.exp 1 + 1) (T1 := 4 * Real.exp 1 + 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (le_refl _)
      (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (fun _ => GPL_anti_of_large_t _ _ _ (by positivity)
        (by nlinarith [Real.exp_one_gt_two]) (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        push_cast
        rw [Real.rpow_zero, mul_one]
        exact patel_yang_subweyl_bound ht')
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        rw [Real.rpow_one]
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      interpolated_bound_1a_hcompact
      -- `hnn`: every summand is `≥0` here (`66.7, 1.546 > 1`, `\log|t| > 2 > 0` at `|t| > 4e+1`),
      -- no threshold padding beyond `T0` needed.
      (by
        intro σ' hσ' t' ht'
        obtain ⟨hσ'0, hσ'1⟩ := hσ'
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : Real.exp 1 ^ 2 < 7.39 := by nlinarith
        have hexp2eq : Real.exp (2:ℝ) = Real.exp 1 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        have hT0gt : Real.exp 2 < 4 * Real.exp 1 + 1 := by
          rw [hexp2eq]; nlinarith [Real.exp_one_gt_two]
        have hL2 : (2:ℝ) < Real.log |t'| := by
          have h1 : Real.exp 2 < |t'| := lt_trans hT0gt ht'
          have hlog := Real.log_lt_log (Real.exp_pos 2) h1
          rwa [Real.log_exp] at hlog
        have hlogLpos : (0:ℝ) < Real.log (Real.log |t'|) := Real.log_pos (by linarith)
        have hwa'0 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hwb'0 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hlogApos : (0:ℝ) ≤ Real.log 66.7 := Real.log_nonneg (by norm_num)
        have hlogBpos : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        have hLpos : (0:ℝ) ≤ Real.log |t'| := by linarith
        have hp1 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) * Real.log |t'| := mul_nonneg hwa'0 hLpos
        have hp2 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log |t'| := mul_nonneg hwb'0 hLpos
        have hp3 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log (Real.log |t'|) :=
          mul_nonneg hwb'0 hlogLpos.le
        have hp4 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) * Real.log 66.7 := mul_nonneg hwa'0 hlogApos
        have hp5 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log 1.546 := mul_nonneg hwb'0 hlogBpos
        nlinarith [hp1, hp2, hp3, hp4, hp5])
      σ ⟨hσ0, hσ1⟩ t ht
  rw [hwa, hwb] at hinterp
  have hlogw : (0:ℝ) * (14 / 3 * (5 / 7 - σ)) + 1 * (14 / 3 * (σ - 1 / 2))
      = 14 / 3 * (σ - 1 / 2) := by ring
  rw [hlogw] at hinterp
  have hcoef : 27 / 164 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 47 / 123 - 107 / 246 * σ := by ring
  rw [hcoef] at hinterp
  linarith [hinterp]

/-- **Simplified corollary of `interpolated_bound_1a_tight`**: the `σ`-dependent `O^*` numerator
`2((4e+σ)²+(4e+2-σ)²)+(2-2σ)²` equals `4Q²+8Q+12-16σ+8σ²` with `Q=4e` (a short algebraic identity),
which is *decreasing* in `σ` on `[1/2,5/7]` (its `σ`-derivative `-16+16σ<0` there), so it is
maximized at `σ=1/2`; numerically `≈565.88`, and `4Q²+8Q+6 < 566` follows from
`four_exp_one_add_one_sq_le` (which is where `Real.exp_one_lt_d9` enters) together with the single
product `(σ-1/2)(5/7-σ) ≥ 0`.

### Summary of Proof
Matches the second display of Proposition `\ref{prop:interpolation}` (Proposition 35) case (1),
`ZerosInShortIntervals.tex`.
### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1a_tight`, `four_exp_one_add_one_sq_le`.
**Used by:** none. -/
theorem interpolated_bound_1a_tight_simple {t σ : ℝ} (ht : (4 * Real.exp 1 + 1:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (47 / 123 - 107 / 246 * σ) * Real.log |t| + 14 / 3 * (σ - 1 / 2) * Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 66.7 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2) + 566 / (8 * |t| ^ 2 * Real.log |t|)) := by
  have hbase := interpolated_bound_1a_tight ht hσ
  obtain ⟨hσ0, hσ1⟩ := hσ
  have ht1 : (1:ℝ) < |t| := by nlinarith [Real.exp_pos 1]
  have hL0 : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have habs : |2 - 2 * σ| ^ 2 = (2 - 2 * σ) ^ 2 := sq_abs _
  have ht2pos : (0:ℝ) < |t| ^ 2 := by positivity
  have hden : (0:ℝ) < 8 * |t| ^ 2 * Real.log |t| := mul_pos (mul_pos (by norm_num) ht2pos) hL0
  have hnum : 2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2
      ≤ 566 := by
    -- `ring`-normalised the goal is `4(4e+1)² + 8(1-σ)² ≤ 566`, linear in the atoms
    -- `{e, e², σ, σ²}`: the constant comes from `four_exp_one_add_one_sq_le` and the only
    -- nonlinear fact needed is the one product `(σ-1/2)(5/7-σ) ≥ 0`, supplied here rather than
    -- searched for.  The maximum over `σ ∈ [1/2, 5/7]` is at `σ = 1/2`, clearing `566` by `0.115`.
    rw [habs]
    linarith only [four_exp_one_add_one_sq_le, hσ0, hσ1,
      mul_nonneg (by linarith : (0:ℝ) ≤ σ - 1 / 2) (by linarith : (0:ℝ) ≤ 5 / 7 - σ)]
  have hfrac : (2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
      / (8 * |t| ^ 2 * Real.log |t|) ≤ 566 / (8 * |t| ^ 2 * Real.log |t|) := by
    -- after the cross-multiplication this is exactly `A·D ≤ 566·D` from `A ≤ 566`, `0 < D`
    rw [div_le_div_iff₀ hden hden]; exact mul_le_mul_of_nonneg_right hnum hden.le
  linarith [hbase, hfrac]

/-- **The numeric obligation of `interpolated_bound_1b`, isolated** as the class field
`InterpolationCertificates.interpolated_bound_1b_hcompact`. It is `hcompact` from
`fiori_zeta_interpolation`, instantiated at `a=1/2, b=5/7, A=0.611, B=1.546, p=1/6, q=1/14, ra=1,
rb=1, Q=16, T0=3`.

### Summary of Proof
Not proved here. `Code/indep_arb_hcompact.sage` **certifies** it with arb on `264` adaptively
bisected `(σ,t)`-boxes (second-order Taylor enclosure of `(s-1)ζ(s)`; arb's plain ball `zeta` is
far too loose here — radius `0.08` on a box of radius `0.004`), and
`Code/indep_mpmath_hcompact.py` rechecks it pointwise: worst ratio `0.94706` at `σ = 1/2`,
`t = 0`, where `‖(s-1)ζ(s)‖ = 0.730` against `RHS = 0.771`. The margin is under `6%`, so (1b) has
by far the least headroom of the four cases. `Code/verify_hcompact_boxes.sage` reports the same
`0.947` for its own case-(1b) box. The compact range stays `|t| ≤ 3`, since `ra = rb` makes the
`σ`-monotonicity hypothesis vacuous.

### Lean Notes
Turning the certification into a proof term needs verified interval arithmetic for `ζ` inside
Lean, which does not exist here.

**(1b) is the one case whose decoupled split has to cut `σ` as well as `t`.** Over
`σ ∈ [1/2,5/7]` the `ζ` side is largest at `σ = 5/7` (`0.835` at `t = 0`) while the interpolant
is smallest at `σ = 1/2` (`0.771` there) — the two extrema sit at *opposite* ends of the strip,
so `sup_box LHS > inf_box RHS` however finely the `t`-range alone is cut: `t`-width `2` gives
`1.5905`, width `1` gives `1.2125`, width `1/2` gives `1.1212`. Cutting `σ` too repairs it:
width `1/2` with `σ` in two gives `1.0480`, and **width `1/4` with `σ` in four gives `0.9897`** —
a working split; width `1/8` with `σ` in eight gives `0.9664`. Only the `|t| ≲ 0.5` boxes need
the `σ`-cut at all. (Cases (1a) and (1c) have their `σ`-argmin of RHS at `σ = 5/7`, alongside the
argmax of the `ζ` side, which is why `t`-only cuts decouple them.) All the figures above are
`Code/indep_mpmath_hcompact.py`'s.

### References
No tex counterpart for this numeric step; the bound it feeds is
`Proposition \ref{prop:interpolation}` (Proposition 35), case (1b).

### Dependencies
**Depends on:** `InterpolationCertificates`, `PhragmenLindelofSetup.interpG`, `interpα`,
`interpβ`.
**Used by:** `interpolated_bound_1b`, `interpolated_bound_1b_tight`. -/
theorem interpolated_bound_1b_hcompact :
    ∀ t : ℝ, |t| ≤ 3 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 0.611 1.546 (1 / 6) (1 / 14) 16 i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (1 / 6) 1 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2)) :=
  InterpolationCertificates.interpolated_bound_1b_hcompact

/-- **`Proposition \ref{prop:interpolation}` (Proposition 35), case (1b)**: as
`interpolated_bound_1a` but using the plain Revers subconvexity constant `0.611`.

**Rests on one hypothesis**: `interpolated_bound_1b_hcompact`, the field
`InterpolationCertificates.interpolated_bound_1b_hcompact` — a closed numeric fact certified
outside Lean. Its margin is the thinnest of the four cases (`6%`); see its own docstring.

### Summary of Proof
Structurally this is the `ra = rb = 1` case of `fiori_zeta_interpolation` (both boundary bounds
carry a `log|t|` factor), which is exactly why the `loglog|T|` coefficient here is the flat `1` (`=
w_a + w_b`) rather than `1a`'s `σ`-dependent `14/3(σ-1/2)`. **Uses `Q = 16`, not
`interpolated_bound_1a`'s `Q = 4e`, and applies Phragmén–Lindelöf to `(s-1)ζ(s)` rather than
`ζ(s)`.** Both choices are load-bearing here, not incidental: with `Q = 4e` and no `(s-1)` factor,
the compact-range hypothesis `hcompact` is not merely unverified but **false** — it implies
`fiori_phragmenLindelof`'s boundary hypothesis at `σ = a` for every `|t| ≤ T0` (the `⨅` over `τ ∈
[a,b]` is at most the value at `τ = a`), and at `t = 0`, `a = 1/2` that reads `|ζ(1/2)| = 1.46035…`
against `0.611·(1/2)^{1/6}·GPL_{4e}(1/2) = 0.611·0.89090·2.47339 = 1.34636…`, failing by `8.5%`.

* *The `(s-1)` factor* (`PhragmenLindelofSetup.interpα`/`interpβ`; see
  `fiori_zeta_interpolation`) is a no-op here: at `σ = 1/2`, `|s-1| = |s|` identically, so both
  sides scale by the same factor. (It does fix case (2) and improve (1a).)
* *`Q = 16`* is needed because `Q` is a free parameter of the `G`-family that never appears in
  the conclusion, and `GPL_Q(1/2)` increases with `Q`; the requirement is
  `GPL_Q(1/2) ≥ 2.68325`, i.e. `Q ≥ 13.65`. `Q = 16` gives worst ratio `0.947` over the whole
  box (`Code/verify_hcompact_boxes.sage`). `Q` re-enters only through
  `fiori_zeta_interpolation`'s range `(Q+2)² + 55 ≤ |t|`, which at `Q = 16` is `|t| ≥ 379` —
  against the available `|t| > 10¹² - 1`.

### References
tex: `Proposition \ref{prop:interpolation}` (Proposition 35), case (1b).

### Dependencies
**Depends on:** `GPL_ge_log`, `fiori_zeta_interpolation`, `interpolated_bound_1b_hcompact`,
`log_bound_of_interp`, `revers_subconvexity_bound`, `twenty_lt_log`, `yang_critical_strip_bound`,
`zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1b_pointwise`, `zeta_chord_bound_nonneg`. -/
theorem interpolated_bound_1b {T t σ : ℝ} (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (4 * (1 - σ) / 9 - 1 / 18) * Real.log |T| + Real.log (Real.log |T|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + 3 / T := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hT0 : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have htpos : (0:ℝ) < t := by linarith [ht.1]
  have hatt : |t| = t := abs_of_pos htpos
  have ht3 : (3:ℝ) ≤ |t| := by rw [hatt]; linarith [ht.1]
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hinterp := fiori_zeta_interpolation (a := 1 / 2) (b := 5 / 7) (A := 0.611)
      (B := 1.546) (p := 1 / 6) (q := 1 / 14) (ra := 1) (rb := 1) (Q := 16)
      (T0 := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (fun h => absurd h (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one]
        have hr := revers_subconvexity_bound (t := |t'|) (by rwa [abs_abs])
        rw [abs_abs] at hr
        push_cast
        exact hr)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        rw [Real.rpow_one]
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      -- **compact range**: the numeric obligation, isolated as `interpolated_bound_1b_hcompact`
      interpolated_bound_1b_hcompact
      σ ⟨hσ0, hσ1⟩ t (by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : Real.exp 1 ^ 2 < 7.39 := by nlinarith
        have hTb : (10:ℝ) ^ (12:ℕ) < T := hT
        have hTn : (1000000000000:ℝ) < T := by norm_num at hTb; linarith
        rw [hatt]
        nlinarith [ht.1, hTn])
  rw [hwa, hwb] at hinterp
  have hlogw : (1:ℝ) * (14 / 3 * (5 / 7 - σ)) + 1 * (14 / 3 * (σ - 1 / 2)) = 1 := by ring
  rw [hlogw] at hinterp
  have hbridge := log_bound_of_interp (L := ‖riemannZeta (σ + t * Complex.I)‖)
      (A := (0.611 : ℝ) ^ (14 / 3 * (5 / 7 - σ))) (B := (1.546 : ℝ) ^ (14 / 3 * (σ - 1 / 2)))
      (c := 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2)))
      (w := 1) (T := T) (t := t)
      (norm_nonneg _) (by positivity) (by positivity) hT ht
      (by nlinarith) (by nlinarith) zero_le_one le_rfl
      (by
        have hlT : 20 < Real.log |T| := by
          rw [abs_of_pos (by linarith : (0:ℝ) < T)]; exact twenty_lt_log hT
        have hllT : 0 < Real.log (Real.log |T|) := Real.log_pos (by linarith)
        have h1 : Real.log ((0.611 : ℝ) ^ (14 / 3 * (5 / 7 - σ))) = 14 / 3 * (5 / 7 - σ) *
            Real.log 0.611 := Real.log_rpow (by norm_num) _
        have h2 : Real.log ((1.546 : ℝ) ^ (14 / 3 * (σ - 1 / 2))) = 14 / 3 * (σ - 1 / 2) *
            Real.log 1.546 := Real.log_rpow (by norm_num) _
        have h4 : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        -- `log 0.611 ≥ log (1/2) = -log 2 > -0.7`, dominated by `c·log|T| ≥ (1/14)·20`
        have h5 : -Real.log 2 ≤ Real.log 0.611 := by
          rw [← Real.log_inv]
          exact Real.log_le_log (by norm_num) (by norm_num)
        have h6 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have hwa1 : 14 / 3 * (5 / 7 - σ) ≤ 1 := by linarith
        rw [h1, h2]
        nlinarith)
      hinterp
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 0.611),
    Real.log_rpow (by norm_num : (0:ℝ) < 1.546)] at hbridge
  have hcoef : 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 4 * (1 - σ) / 9 - 1 / 18 := by ring
  rw [hcoef] at hbridge
  linarith [hbridge]

/-- **Tight, pointwise version of `interpolated_bound_1b`**: no `T`-window, an explicit
`σ`-dependent `O(1/t²)` error obtained by summing `log` of each `Gᵢ`'s own tight error directly
(`fiori_zeta_interpolation_tight`'s log-linear route — see its docstring), instead of the flat
`3/T`.

### Summary of Proof
**The threshold is `8`, not `10¹²` — but also not exactly `interpolated_bound_1b_hcompact`'s `T0 =
3`.** `fiori_zeta_interpolation_tight`'s window/interpolation machinery only needs `T0 = 3 < |t|`;
the extra headroom is for a *different*, genuine reason: stating the bound as `\log‖ζ‖ ≤
(\text{sum})` forces `(\text{sum})` (excluding the `O(1/t²)` tail) to be `≥ 0` whenever `ζ` has an
exact zero at that point (`Real.log 0 = 0` in Lean's convention) — checked numerically, this first
becomes true (using the *exact* value of `\log\log|t|`) only past `|t| ≈ 3.74` (worst case `σ =
1/2`, where all the interpolation weight sits on the negative `\log(0.611)` term). The proof below
uses the cheap, generic lower bound `\log x ≥ 1-1/x` (`log_ge_one_sub_inv`) rather than pin down
`\log\log|t|` exactly, which costs some headroom — `|t| > 8` is what that cheaper route needs, not
the true minimum `≈3.74`. So `8` is a proof-engineering choice, not a claim that `8` is optimal,
and the requirement itself is load-bearing: it is what stating the conclusion in `≤`/log form
costs. Uses the *same* `interpolated_bound_1b_hcompact` as the untightened version: the
compact-range numeric obligation is completely unaffected by this tightening.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL_ge_log`, `fiori_zeta_interpolation_tight`, `interpolated_bound_1b_hcompact`,
`log_ge_one_sub_inv`, `revers_subconvexity_bound`, `yang_critical_strip_bound`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1b_tight_simple`, `zeta_chord_bound_nonneg_tight`. -/
theorem interpolated_bound_1b_tight {t σ : ℝ} (ht : (8:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2)
            + (2 * ((16 + σ) ^ 2 + (16 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                / (8 * |t| ^ 2 * Real.log |t|)) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have ht3 : (3:ℝ) < |t| := by linarith
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hwa1 : 14 / 3 * (5 / 7 - σ) ≤ 1 := by linarith
  have hwb1 : 14 / 3 * (σ - 1 / 2) ≤ 1 := by linarith
  have hinterp := fiori_zeta_interpolation_tight (a := 1 / 2) (b := 5 / 7) (A := 0.611)
      (B := 1.546) (p := 1 / 6) (q := 1 / 14) (ra := 1) (rb := 1) (Q := 16)
      (T0 := 3) (T1 := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (fun h => absurd h (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one]
        have hr := revers_subconvexity_bound (t := |t'|) (by rwa [abs_abs])
        rw [abs_abs] at hr
        push_cast
        exact hr)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        rw [Real.rpow_one]
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      interpolated_bound_1b_hcompact
      -- `hnn`: the log-sum, `wa·(L/6+\log 0.611) + wb·(L/14+\log 1.546) + \log\log|t|`, is `≥0`
      -- once `|t| > 8` (checked numerically against the *exact* value: worst case `σ=1/2`, i.e.
      -- `wa=1,wb=0`, first turns positive already at `|t|≈3.74`; the cruder, cheap-to-formalize
      -- bound `log_ge_one_sub_inv` used below needs the extra headroom to `8`).
      (by
        intro σ' hσ' t' ht'
        obtain ⟨hσ'0, hσ'1⟩ := hσ'
        have ht'8 : (8:ℝ) < |t'| := ht'
        have hL8 : Real.log 8 < Real.log |t'| := Real.log_lt_log (by norm_num) ht'8
        have hlog8eq : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
        have hL8' : (2.079:ℝ) < Real.log |t'| := by
          have h2 := Real.log_two_gt_d9
          rw [hlog8eq] at hL8
          linarith
        have hLpos : (0:ℝ) < Real.log |t'| := by linarith
        have hlogL_lb : (1 - 1/2.079 : ℝ) ≤ Real.log (Real.log |t'|) := by
          have hstep : (1:ℝ) / Real.log |t'| ≤ 1 / 2.079 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
          have := log_ge_one_sub_inv (Real.log |t'|) hLpos
          linarith
        have hwa'0 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hwb'0 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hwsum' : (5/7-σ')/(5/7-1/2:ℝ) + (σ'-1/2)/(5/7-1/2:ℝ) = 1 := by
          field_simp; ring
        have h5 : -Real.log 2 ≤ Real.log 0.611 := by
          rw [← Real.log_inv]
          exact Real.log_le_log (by norm_num) (by norm_num)
        have h6 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have h4 : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        have hp1 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) * (Real.log |t'| - 2.079) :=
          mul_nonneg hwa'0 (by linarith)
        have hp2 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * (Real.log |t'| - 2.079) :=
          mul_nonneg hwb'0 (by linarith)
        have hcomb : ((5/7-σ')/(5/7-1/2:ℝ) + (σ'-1/2)/(5/7-1/2:ℝ)) * Real.log (Real.log |t'|)
            = Real.log (Real.log |t'|) := by rw [hwsum']; ring
        nlinarith [hwa'0, hwb'0, hwsum', h5, h6, h4, hlogL_lb, hL8', hp1, hp2, hcomb])
      σ ⟨hσ0, hσ1⟩ t ht
  rw [hwa, hwb] at hinterp
  have hlogw : (1:ℝ) * (14 / 3 * (5 / 7 - σ)) + 1 * (14 / 3 * (σ - 1 / 2)) = 1 := by ring
  rw [hlogw] at hinterp
  have hcoef : 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 4 * (1 - σ) / 9 - 1 / 18 := by ring
  rw [hcoef] at hinterp
  linarith [hinterp]

/-- **Simplified corollary of `interpolated_bound_1b_tight`**: same numerator identity as
`interpolated_bound_1a_tight_simple` but with `Q=16` exactly, so `4Q²+8Q+6 = 1158` exactly (no
`Real.exp` bound needed), still maximized at `σ=1/2`.

### Summary of Proof
Matches the third display of Proposition `\ref{prop:interpolation}` (Proposition 35) case (1),
`ZerosInShortIntervals.tex`.
### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1b_tight`.
**Used by:** `zeta_chord_bound_nonneg_tight_simple`. -/
theorem interpolated_bound_1b_tight_simple {t σ : ℝ} (ht : (8:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2) + 1158 / (8 * |t| ^ 2 * Real.log |t|)) := by
  have hbase := interpolated_bound_1b_tight ht hσ
  obtain ⟨hσ0, hσ1⟩ := hσ
  have ht1 : (1:ℝ) < |t| := by linarith
  have hL0 : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have habs : |2 - 2 * σ| ^ 2 = (2 - 2 * σ) ^ 2 := sq_abs _
  have ht2pos : (0:ℝ) < |t| ^ 2 := by positivity
  have hden : (0:ℝ) < 8 * |t| ^ 2 * Real.log |t| := mul_pos (mul_pos (by norm_num) ht2pos) hL0
  have hnum : 2 * ((16 + σ) ^ 2 + (16 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2 ≤ 1158 := by
    -- the same identity as the other three numerators, here with `X = 16`:  `4·17² + 8(1-σ)²`.
    -- At `σ = 1/2` that is `1156 + 2 = 1158` exactly, so this bound is attained, not merely met.
    rw [habs]
    linarith only [hσ0, hσ1,
      mul_nonneg (by linarith : (0:ℝ) ≤ σ - 1 / 2) (by linarith : (0:ℝ) ≤ 5 / 7 - σ)]
  have hfrac : (2 * ((16 + σ) ^ 2 + (16 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
      / (8 * |t| ^ 2 * Real.log |t|) ≤ 1158 / (8 * |t| ^ 2 * Real.log |t|) := by
    -- after the cross-multiplication this is exactly `A·D ≤ 1158·D` from `A ≤ 1158`, `0 < D`
    rw [div_le_div_iff₀ hden hden]; exact mul_le_mul_of_nonneg_right hnum hden.le
  linarith [hbase, hfrac]

/-- **The numeric obligation of `interpolated_bound_1c`'s `hcompact` slot, isolated** as the class
field `InterpolationCertificates.interpolated_bound_1c_hcompact`. It is `hcompact` from
`fiori_zeta_interpolation_1c`, instantiated at `a=1/2, b=5/7, B=1.546, c=0.470795, d=4.04972,
q=1/14, Q=4e` — a single closed numeric statement with **no `T`-dependence at all**: the affine
boundary constant `0.470795 log|t| + 4.04972` is carried directly by the function `G_1 = G1shift`
(see `PhragmenLindelofSetup.G1shift` and the `### Case (1c)` section of
`PhragmenLindelofSetup.lean`), not folded into a `T`-dependent scalar `A`.

### Summary of Proof
Not proved here. **The compact range is `|t| ≤ 4e+1 = 11.8731…`, not `|t| ≤ 3`** — as in
`interpolated_bound_1a`, this is a case whose `r`-family invokes genuine `σ`-monotonicity on
*two* of its four functions (`G1shift` and `GPL`, both live since `ra = 0 ≠ 1 = rb` in this
layout), so `fiori_phragmenLindelof`'s `hG_mono` needs the same `|t| > Q+1` threshold
`interpolated_bound_1a` does. `Code/indep_arb_hcompact.sage` **certifies** the statement with arb
on `137` adaptively bisected `(σ,t)`-boxes: the linear factors `G_0`, `G_2` have unconditional
closed-form infima, while `G_1 = G1shift` and `G_3 = GPL` are certified by the same subdivision
technique the r = 3 cases use for their log-type function.

### Lean Notes
Turning the certification into a proof term needs verified interval arithmetic for `ζ` inside
Lean, which does not exist here.

The structural half is solid: `log RHS` is **affine in `σ`** (every base depends on `t` alone,
every exponent is affine in `σ`), so the `σ`-infimum always sits at an endpoint — `σ = 1/2` or
`σ = 5/7`, no interior search. At `σ = 5/7` the `r = 3` and `r = 4` families evaluate to the
identical expression `B·|a+it|·|1-b-it|^{q}·min_τ|GPL(τ+it)|`, since `(B^{1/q})^{q} = B`, which is
why (1c)'s `inf RHS` agrees with (1a)'s to six digits. And `t → -t` needs no separate treatment:
`|(s-1)ζ(s)|` and every `|G_i|` are conjugation-invariant.

**⚠ Two figures reported by other scripts do not describe anything real; do not quote them.**
`Code/verify_hcompact_boxes.sage` reports worst ratio `0.9989` for its case-(1c) box ("under
`0.2%` margin"), which is a ball-arithmetic artifact rather than real tightness: `verify_box_1c`
evaluates the RHS on a `σ` *ball*, so `w_a` and `w_b` enter the four exponents as independent
balls and arb cannot see that `w_a + w_b = 1`, making `R.lower()` far too small. And
the figure `0.9617` obtained from `σ`-endpoint evaluation over the
three width-4 boxes `|t| ∈ [0,4], [4,8], [8,12]` is wrong for the same reason it is wrong for
(1a): the width-4 split **fails**, at `U/L = 1.4758` (`sup LHS = 2.5801` on `|t| ≤ 4` against
`inf RHS = 1.7483` at `t = 0`). Width `2` gives `0.7014`, width `1` gives `0.5347`.

### References
No tex counterpart for this numeric step; the bound it feeds is
`Proposition \ref{prop:interpolation}` (Proposition 35), case (1c).

**Independent numeric check.** `Code/indep_mpmath_hcompact.py` (mpmath,
written from this statement): the pointwise worst ratio is `0.4811` at `σ = 5/7`, `t = 0` —
identical to (1a)'s, as the telescoping argument predicts.

### Dependencies
**Depends on:** `InterpolationCertificates`, `PhragmenLindelofSetup.interpG1c`, `interpα1c`,
`interpβ1c`.
**Used by:** `interpolated_bound_1c`, `interpolated_bound_1c_tight`. -/
theorem interpolated_bound_1c_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG1c 1.546 0.470795 4.04972 (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα1c (1 / 6) i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ1c (1 / 14) i * (σ - 1 / 2) / (5 / 7 - 1 / 2)) :=
  InterpolationCertificates.interpolated_bound_1c_hcompact

set_option maxHeartbeats 300000 in
-- the direct `r = 4` Phragmén–Lindelöf instantiation plus the `log_bound_of_interp_1c` bridge
-- push this well past the default elaboration budget.  What remains over is `whnf` on the
-- STATEMENT, not the tactics, so hinting cannot reduce it.  Measured: fails at 250000.
/-- **`Proposition \ref{prop:interpolation}` (Proposition 35), case (1c)**: as
`interpolated_bound_1b` but using the sharper `T`-dependent Hiary–Revers constant
`0.470795 + 4.04972/log|T|`.

### Summary of Proof
**Rests on one hypothesis.** The proof is complete modulo `interpolated_bound_1c_hcompact`, the
field `InterpolationCertificates.interpolated_bound_1c_hcompact` — a closed numeric fact
certified outside Lean; see its own docstring. The appendix's
own proof of this case uses a genuinely different choice of `G_1` than cases (1a)/(1b): it takes
`G_1(s) = 0.470795·GPL(4e)(s+1) + 4.04972` (`PhragmenLindelofSetup.G1shift`), an affine function of
a log rather than a scalar multiple of one — this is *not* a workaround for
`fiori_zeta_interpolation`'s constant-`A` interface, it is a different function, of the affine
shape the appendix's own choice has. (The appendix *displays* `G_1` with the unshifted arguments
`4e+s`, `4e+2-s`, but its own `O^*` term is written with the shifted `4e+σ+1`, `4e+1-σ`, which is
what `G1shift` uses.) `PhragmenLindelofSetup.fiori_zeta_interpolation_1c` instantiates
`ExternalFacts.fiori_phragmenLindelof` directly with the `r = 4` family `![linG 1 0, G1shift Q c d,
linGRefl (B^{1/q}) 1, GPL Q]` (`PhragmenLindelofSetup.interpG1c`) — `G_1 = G1shift` carries the
whole `σ = 1/2` boundary bound `0.470795|t|^{1/6}log|t| + 4.04972|t|^{1/6}`
(`ExternalFacts.hiary_revers_half_line_bound`, unconditional for `3 ≤ |t|`, no `T`-dependence
anywhere) directly, with none of it folded back into a constant. The bridge to this theorem's
`T`-indexed additive form is `PhragmenLindelofSetup.log_bound_of_interp_1c`, which handles the one
correction `log_bound_of_interp` doesn't need: `wa·(log A(t) - log A(T))` for `A(x) := 0.470795 +
4.04972/log x`, bounded via `A` being decreasing and `log(T-1) > 20`.

### References
tex: `Proposition \ref{prop:interpolation}` (Proposition 35), case (1c).

### Dependencies
**Depends on:** `G1shift`, `G1shift_le`, `G1shift_mono_of_large_t`, `GPL_anti_of_large_t`,
`GPL_ge_log`, `fiori_zeta_interpolation_1c`, `hiary_revers_half_line_bound`,
`interpolated_bound_1c_hcompact`, `log_bound_of_interp_1c`, `twenty_lt_log`,
`yang_critical_strip_bound`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1c_pointwise`. -/
theorem interpolated_bound_1c {T t σ : ℝ} (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (4 * (1 - σ) / 9 - 1 / 18) * Real.log |T| + Real.log (Real.log |T|)
        + 14 / 3 * (5 / 7 - σ)
            * Real.log (0.470795 + 4.04972 / Real.log |T|)
        + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 + 3 / T := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hT0 : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have htpos : (0:ℝ) < t := by linarith [ht.1]
  have hatt : |t| = t := abs_of_pos htpos
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hwa1 : (14 / 3 * (5 / 7 - σ) : ℝ) ≤ 1 := by linarith
  have hthresh : ((4 * Real.exp 1 + 2) ^ 2 + 110 : ℝ) ≤ |t| := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hTb : (10:ℝ) ^ (12:ℕ) < T := hT
    have hTn : (1000000000000:ℝ) < T := by norm_num at hTb; linarith
    rw [hatt]
    nlinarith [ht.1, hTn, he, he0]
  have hinterp := fiori_zeta_interpolation_1c (a := 1 / 2) (b := 5 / 7) (B := 1.546)
      (c := 0.470795) (d := 4.04972) (p := 1 / 6) (q := 1 / 14) (Q := 4 * Real.exp 1)
      (T0 := 4 * Real.exp 1 + 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by nlinarith [Real.exp_one_gt_two]) (by norm_num)
      (by norm_num) (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      -- `hG1mono`: `G1shift` is increasing in `σ` for `|t| > Q+1 = T0`
      (fun t' ht' => G1shift_mono_of_large_t (4 * Real.exp 1) 0.470795 4.04972 (1/2) (5/7)
        (by positivity) (by norm_num) (by norm_num) (by norm_num)
        (by nlinarith [Real.exp_one_gt_two]) t' ht')
      -- `hGmono`: `GPL` is decreasing in `σ` for `|t| > Q+1 = T0`
      (fun t' ht' => GPL_anti_of_large_t (4 * Real.exp 1) (1/2) (5/7) (by positivity)
        (by nlinarith [Real.exp_one_gt_two]) (by norm_num) t' ht')
      (by
        intro t' ht' σ' hσ'
        exact GPL_ge_log _ _ _ t' (by linarith) σ' hσ')
      -- `hbound_a`: `ExternalFacts.hiary_revers_half_line_bound`, unconditional, no `T`
      (by
        intro t' ht'
        have h := (hiary_revers_half_line_bound ht').le
        have heq : ((1/2:ℝ):ℂ) + (t':ℝ) * Complex.I = (1/2:ℂ) + t' * Complex.I := by
          push_cast; ring
        rw [heq]
        calc ‖riemannZeta ((1/2:ℂ) + t' * Complex.I)‖
            ≤ 0.470795 * |t'| ^ (1/6:ℝ) * Real.log |t'| + 4.04972 * |t'| ^ (1/6:ℝ) := h
          _ = (0.470795 * Real.log |t'| + 4.04972) * |t'| ^ (1/6:ℝ) := by ring)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      -- `hG1window`: the triangle-inequality slack bound on `G1shift`, via `G1shift_le`.
      -- Worked entirely in `|t'|` (not `t'`), since `t'` ranges over both signs here.
      (by
        intro t' ht' σ' hσ'
        have he9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have hA0 : (0:ℝ) < |t'| := by
          have : (0:ℝ) ≤ (4 * Real.exp 1 + 2) ^ 2 := by positivity
          linarith [ht']
        have hA275 : (275:ℝ) ≤ |t'| := by
          nlinarith [ht', he9, he0, Real.exp_one_gt_d9]
        have h1 : (0:ℝ) < 4 * Real.exp 1 + σ' + 1 := by linarith [hσ'.1]
        have h2 : (0:ℝ) < 4 * Real.exp 1 + 1 - σ' := by linarith [hσ'.2]
        have ht1 : (1:ℝ) ≤ |t'| := by linarith
        have hle := G1shift_le (4 * Real.exp 1) 0.470795 4.04972 σ' t' (by norm_num)
          (by norm_num) h1 h2 ht1
        have ht2eq : t' ^ 2 = |t'| ^ 2 := (sq_abs t').symm
        rw [ht2eq] at hle
        have hKbound : (4 * Real.exp 1 + σ' + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ') ^ 2 ≤ 288 := by
          nlinarith [hσ'.1, hσ'.2, he9, he0]
        have hsig : |2 * σ'| ≤ 10 / 7 := by
          rw [abs_of_nonneg (by linarith [hσ'.1] : (0:ℝ) ≤ 2 * σ')]
          linarith [hσ'.2]
        have hlognn : (0:ℝ) ≤ Real.log |t'| := Real.log_nonneg (by linarith)
        have h4A2 : (0:ℝ) < 4 * |t'| ^ 2 := by positivity
        have hstep : 0.470795 * (((4 * Real.exp 1 + σ' + 1) ^ 2
              + (4 * Real.exp 1 + 1 - σ') ^ 2) + |2 * σ'| * (2 * |t'|))
            ≤ (0.470795 * Real.log |t'| + 4.04972) * |t'| := by
          have hKprod : 0.470795 * ((4 * Real.exp 1 + σ' + 1) ^ 2
                + (4 * Real.exp 1 + 1 - σ') ^ 2) ≤ 0.470795 * 288 :=
            mul_le_mul_of_nonneg_left hKbound (by norm_num)
          have hprod : 0.470795 * (|2 * σ'| * (2 * |t'|)) ≤ 0.470795 * ((10/7) * (2 * |t'|)) := by
            have := mul_le_mul_of_nonneg_right hsig (by linarith : (0:ℝ) ≤ 2 * |t'|)
            exact mul_le_mul_of_nonneg_left this (by norm_num)
          have hlogprod : (0:ℝ) ≤ 0.470795 * |t'| * Real.log |t'| := by positivity
          nlinarith [hKprod, hprod, hlogprod, hA275]
        have heqL : 0.470795 * (((4 * Real.exp 1 + σ' + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ') ^ 2)
              / (4 * |t'| ^ 2) + |2 * σ'| / (2 * |t'|))
            = (0.470795 * (((4 * Real.exp 1 + σ' + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ') ^ 2)
                + |2 * σ'| * (2 * |t'|))) / (4 * |t'| ^ 2) := by
          field_simp; ring
        have heqR : (0.470795 * Real.log |t'| + 4.04972) * (1 / (4 * |t'|))
            = ((0.470795 * Real.log |t'| + 4.04972) * |t'|) / (4 * |t'| ^ 2) := by
          field_simp
        have hfinal : 0.470795 * (((4 * Real.exp 1 + σ' + 1) ^ 2
              + (4 * Real.exp 1 + 1 - σ') ^ 2) / (4 * |t'| ^ 2) + |2 * σ'| / (2 * |t'|))
            ≤ (0.470795 * Real.log |t'| + 4.04972) * (1 / (4 * |t'|)) := by
          rw [heqL, heqR]; gcongr
        calc ‖G1shift (4 * Real.exp 1) 0.470795 4.04972 (σ' + t' * Complex.I)‖
            ≤ 0.470795 * (Real.log |t'| + ((4 * Real.exp 1 + σ' + 1) ^ 2
                  + (4 * Real.exp 1 + 1 - σ') ^ 2) / (4 * |t'| ^ 2) + |2 * σ'| / (2 * |t'|))
                + 4.04972 := hle
          _ ≤ (0.470795 * Real.log |t'| + 4.04972) * (1 + 1 / (4 * |t'|)) := by nlinarith [hfinal])
      -- **compact range**: the numeric obligation, isolated as `interpolated_bound_1c_hcompact`
      interpolated_bound_1c_hcompact
      σ ⟨hσ0, hσ1⟩ t hthresh
  rw [hwa, hwb] at hinterp
  have hbridge := log_bound_of_interp_1c (c1 := 0.470795) (d1 := 4.04972)
      (Bw := (1.546:ℝ) ^ (14 / 3 * (σ - 1 / 2)))
      (cc := 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2)))
      (wa := 14 / 3 * (5 / 7 - σ)) (wb := 14 / 3 * (σ - 1 / 2)) (T := T) (t := t)
      (L := ‖riemannZeta (σ + t * Complex.I)‖)
      (norm_nonneg _) (by norm_num) (by norm_num) (by norm_num) (by positivity) hT ht
      (by nlinarith) (by nlinarith) hwa0 hwa1 hwb0 (by ring)
      (by
        have hlT : 20 < Real.log |T| := by
          rw [abs_of_pos (by linarith : (0:ℝ) < T)]; exact twenty_lt_log hT
        have hllT : 0 < Real.log (Real.log |T|) := Real.log_pos (by linarith)
        have h2 : Real.log ((1.546 : ℝ) ^ (14 / 3 * (σ - 1 / 2))) = 14 / 3 * (σ - 1 / 2) *
            Real.log 1.546 := Real.log_rpow (by norm_num) _
        have h4 : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        have hApos : (0:ℝ) < 0.470795 + 4.04972 / Real.log |T| := by positivity
        have hAge : (0.470795:ℝ) ≤ 0.470795 + 4.04972 / Real.log |T| := by
          have : (0:ℝ) < 4.04972 / Real.log |T| := by positivity
          linarith
        -- `log A ≥ log 0.470795 > log (exp (-1)) = -1`, dominated by `cc·log|T| ≥ (1/14)·20`
        have hexpneg : Real.exp (-1) ≤ 0.470795 := by
          rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
          nlinarith [Real.exp_one_gt_d9]
        have h5 : (-1 : ℝ) ≤ Real.log (0.470795 + 4.04972 / Real.log |T|) := by
          have := Real.log_le_log (Real.exp_pos (-1)) (le_trans hexpneg hAge)
          rwa [Real.log_exp] at this
        rw [h2]
        nlinarith)
      hinterp
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 1.546)] at hbridge
  have hcoef : 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 4 * (1 - σ) / 9 - 1 / 18 := by ring
  rw [hcoef] at hbridge
  linarith [hbridge]

/-- **Tight, pointwise version of `interpolated_bound_1c`**: no `T`-window, explicit `σ`-dependent
`O(1/t²)` error, and — as in cases (1a)/(2) — **no extra headroom above `T0 = 4e+1` needed**:
`c·\log|t|+d ≥ d = 4.04972 > 1` makes the affine boundary's own log term positive on its own (even
more trivially than (1a)'s `A = 66.7`), and `B = 1.546 > 1` as before, so `T1 := T0` works.

### Summary of Proof
The one extra step case (1c) needs that the others don't: `fiori_zeta_interpolation_1c_tight`'s
conclusion carries `\log(c\log|t|+d)` directly (no window, so no separate `A(t)` vs `A(T)`
correction is even possible here — that correction was *entirely* a `T`-window artifact, and has
vanished along with the window), which this unpacks via `c\log|t|+d = \log|t|\cdot(c+d/\log|t|)`
into the displayed `\log\log|t| + \log(c+d/\log|t|)` shape, matching `interpolated_bound_1c`'s own
display.
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift_mono_of_large_t`, `GPL_anti_of_large_t`, `GPL_ge_log`,
`fiori_zeta_interpolation_1c_tight`, `hiary_revers_half_line_bound`,
`interpolated_bound_1c_hcompact`, `yang_critical_strip_bound`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_1c_tight_simple`. -/
theorem interpolated_bound_1c_tight {t σ : ℝ} (ht : (4 * Real.exp 1 + 1:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log (0.470795 + 4.04972 / Real.log |t|)
        + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2)
            + (2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                / (8 * |t| ^ 2 * Real.log |t|)
            + 0.470795 * (2 * ((4 * Real.exp 1 + σ + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ) ^ 2)
                  + |2 * σ| ^ 2)
                / (8 * |t| ^ 2 * (0.470795 * Real.log |t| + 4.04972))) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hwa : (5 / 7 - σ) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (5 / 7 - σ) := by ring
  have hwb : (σ - 1 / 2) / (5 / 7 - 1 / 2 : ℝ) = 14 / 3 * (σ - 1 / 2) := by ring
  have hwa0 : (0:ℝ) ≤ 14 / 3 * (5 / 7 - σ) := by linarith
  have hwb0 : (0:ℝ) ≤ 14 / 3 * (σ - 1 / 2) := by linarith
  have hinterp := fiori_zeta_interpolation_1c_tight (a := 1 / 2) (b := 5 / 7) (B := 1.546)
      (c := 0.470795) (d := 4.04972) (p := 1 / 6) (q := 1 / 14) (Q := 4 * Real.exp 1)
      (T0 := 4 * Real.exp 1 + 1) (T1 := 4 * Real.exp 1 + 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by nlinarith [Real.exp_one_gt_two]) (le_refl _)
      (by norm_num) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (by nlinarith [Real.exp_one_gt_two]) (by nlinarith [Real.exp_one_gt_two])
      (fun t' ht' => G1shift_mono_of_large_t (4 * Real.exp 1) 0.470795 4.04972 (1/2) (5/7)
        (by positivity) (by norm_num) (by norm_num) (by norm_num)
        (by nlinarith [Real.exp_one_gt_two]) t' ht')
      (fun t' ht' => GPL_anti_of_large_t (4 * Real.exp 1) (1/2) (5/7) (by positivity)
        (by nlinarith [Real.exp_one_gt_two]) (by norm_num) t' ht')
      (by
        intro t' ht' σ' hσ'
        exact GPL_ge_log _ _ _ t' (by linarith) σ' hσ')
      (by
        intro t' ht'
        have h := (hiary_revers_half_line_bound ht').le
        have heq : ((1/2:ℝ):ℂ) + (t':ℝ) * Complex.I = (1/2:ℂ) + t' * Complex.I := by
          push_cast; ring
        rw [heq]
        calc ‖riemannZeta ((1/2:ℂ) + t' * Complex.I)‖
            ≤ 0.470795 * |t'| ^ (1/6:ℝ) * Real.log |t'| + 4.04972 * |t'| ^ (1/6:ℝ) := h
          _ = (0.470795 * Real.log |t'| + 4.04972) * |t'| ^ (1/6:ℝ) := by ring)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im]
        have hy := yang_critical_strip_bound (k := 4) (by norm_num) (t := |t'|) ht'
        push_cast at hy ⊢
        norm_num at hy ⊢
        exact hy)
      interpolated_bound_1c_hcompact
      -- `hnn`: `c\log|t'|+d ≥ d = 4.04972 > 1` makes its own log term `≥0` on its own; `B=1.546>1`
      -- as usual; no threshold padding beyond `T0` needed.
      (by
        intro σ' hσ' t' ht'
        obtain ⟨hσ'0, hσ'1⟩ := hσ'
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : Real.exp 1 ^ 2 < 7.39 := by nlinarith
        have hexp2eq : Real.exp (2:ℝ) = Real.exp 1 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        have hT0gt : Real.exp 2 < 4 * Real.exp 1 + 1 := by
          rw [hexp2eq]; nlinarith [Real.exp_one_gt_two]
        have hL2 : (2:ℝ) < Real.log |t'| := by
          have h1 : Real.exp 2 < |t'| := lt_trans hT0gt ht'
          have hlog := Real.log_lt_log (Real.exp_pos 2) h1
          rwa [Real.log_exp] at hlog
        have hlogLpos : (0:ℝ) < Real.log (Real.log |t'|) := Real.log_pos (by linarith)
        have hwa'0 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hwb'0 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) := by
          apply div_nonneg (by linarith) (by norm_num)
        have hLpos : (0:ℝ) ≤ Real.log |t'| := by linarith
        have hcdpos : (1:ℝ) ≤ 0.470795 * Real.log |t'| + 4.04972 := by nlinarith
        have hlogcdpos : (0:ℝ) ≤ Real.log (0.470795 * Real.log |t'| + 4.04972) :=
          Real.log_nonneg hcdpos
        have hlogBpos : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        have hp1 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ) * Real.log |t'| := mul_nonneg hwa'0 hLpos
        have hp2 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log |t'| := mul_nonneg hwb'0 hLpos
        have hp3 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log (Real.log |t'|) :=
          mul_nonneg hwb'0 hlogLpos.le
        have hp4 : (0:ℝ) ≤ (5/7-σ')/(5/7-1/2:ℝ)
            * Real.log (0.470795 * Real.log |t'| + 4.04972) := mul_nonneg hwa'0 hlogcdpos
        have hp5 : (0:ℝ) ≤ (σ'-1/2)/(5/7-1/2:ℝ) * Real.log 1.546 := mul_nonneg hwb'0 hlogBpos
        nlinarith [hp1, hp2, hp3, hp4, hp5])
      σ ⟨hσ0, hσ1⟩ t ht
  rw [hwa, hwb] at hinterp
  have hcoef : 1 / 6 * (14 / 3 * (5 / 7 - σ)) + 1 / 14 * (14 / 3 * (σ - 1 / 2))
      = 4 * (1 - σ) / 9 - 1 / 18 := by ring
  rw [hcoef] at hinterp
  have hlogtpos : (0:ℝ) < Real.log |t| := by
    have : Real.exp 1 < |t| := by nlinarith [Real.exp_one_gt_two, ht]
    have hlog := Real.log_lt_log (Real.exp_pos 1) this
    rw [Real.log_exp] at hlog
    linarith
  have hlogfact : Real.log (0.470795 * Real.log |t| + 4.04972)
      = Real.log (Real.log |t|) + Real.log (0.470795 + 4.04972 / Real.log |t|) := by
    have heq : (0.470795:ℝ) * Real.log |t| + 4.04972
        = Real.log |t| * (0.470795 + 4.04972 / Real.log |t|) := by
      field_simp
    rw [heq, Real.log_mul (ne_of_gt hlogtpos) (by positivity)]
  rw [hlogfact] at hinterp
  linarith [hinterp]

/-- **Simplified corollary of `interpolated_bound_1c_tight`**: bounds the `GPL`-type numerator by
`566`
exactly as `interpolated_bound_1a_tight_simple` does, and the `G1shift`-type numerator
`2((4e+σ+1)²+(4e+1-σ)²)+4σ²=4(4e+1)²+8σ²` (increasing in `σ`, so maximized at `σ=5/7`) by `568`.

### Summary of Proof
Then drops `0.470795 log|t|+4.04972` down to `0.470795 log|t|` in that term's denominator (valid
since `4.04972>0`), which cancels the `0.470795` against the `568·0.470795` numerator and lets it
combine with the `566/(8t²log|t|)` term into the single `1134/(8t²log|t|)` used in Proposition
`\ref{prop:interpolation}` (Proposition 35)'s simplified case (1c) display,
`ZerosInShortIntervals.tex`.
### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1c_tight`, `four_exp_one_add_one_sq_le`.
**Used by:** none. -/
theorem interpolated_bound_1c_tight_simple {t σ : ℝ} (ht : (4 * Real.exp 1 + 1:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log (0.470795 + 4.04972 / Real.log |t|)
        + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + (3 / (2 * |t| ^ 2) + 1134 / (8 * |t| ^ 2 * Real.log |t|)) := by
  have hbase := interpolated_bound_1c_tight ht hσ
  obtain ⟨hσ0, hσ1⟩ := hσ
  have ht1 : (1:ℝ) < |t| := by nlinarith [Real.exp_pos 1]
  have hL0 : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have habs : |2 - 2 * σ| ^ 2 = (2 - 2 * σ) ^ 2 := sq_abs _
  have habs2 : |2 * σ| ^ 2 = (2 * σ) ^ 2 := sq_abs _
  have ht2pos : (0:ℝ) < |t| ^ 2 := by positivity
  have hden : (0:ℝ) < 8 * |t| ^ 2 * Real.log |t| := mul_pos (mul_pos (by norm_num) ht2pos) hL0
  -- `(σ-1/2)(5/7-σ) ≥ 0` is the only nonlinear fact either numerator bound needs; naming it once
  -- keeps both of them inside `linarith only`, with no product search in either.
  have hprod : (0:ℝ) ≤ (σ - 1 / 2) * (5 / 7 - σ) :=
    mul_nonneg (by linarith) (by linarith)
  have hnum1 : 2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2
      ≤ 566 := by
    -- `ring`-normalised: `4(4e+1)² + 8(1-σ)² ≤ 566`.  Maximised at `σ = 1/2`; margin `0.115`.
    rw [habs]
    linarith only [four_exp_one_add_one_sq_le, hσ0, hσ1, hprod]
  have hfrac1 : (2 * ((4 * Real.exp 1 + σ) ^ 2 + (4 * Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
      / (8 * |t| ^ 2 * Real.log |t|) ≤ 566 / (8 * |t| ^ 2 * Real.log |t|) := by
    -- after the cross-multiplication this is exactly `A·D ≤ 566·D` from `A ≤ 566`, `0 < D`
    rw [div_le_div_iff₀ hden hden]; exact mul_le_mul_of_nonneg_right hnum1 hden.le
  have hnum2 : 2 * ((4 * Real.exp 1 + σ + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ) ^ 2) + |2 * σ| ^ 2
      ≤ 568 := by
    -- `ring`-normalised: `4(4e+1)² + 8σ² ≤ 568`.  Maximised at `σ = 5/7`, and the margin is only
    -- `0.034` — this is the tightest step in the file, and the one that forces
    -- `four_exp_one_add_one_sq_le` to carry `e² < 7.3890562` instead of the file's usual `7.39`.
    rw [habs2]
    linarith only [four_exp_one_add_one_sq_le, hσ1, hprod]
  have hd1 : (0:ℝ) < 0.470795 * Real.log |t| + 4.04972 := by nlinarith [hL0]
  have hden1 : (0:ℝ) < 8 * |t| ^ 2 * (0.470795 * Real.log |t| + 4.04972) :=
    mul_pos (mul_pos (by norm_num) ht2pos) hd1
  have hstep1 : (0.470795:ℝ)
      * (2 * ((4 * Real.exp 1 + σ + 1) ^ 2 + (4 * Real.exp 1 + 1 - σ) ^ 2) + |2 * σ| ^ 2)
        / (8 * |t| ^ 2 * (0.470795 * Real.log |t| + 4.04972))
      ≤ 0.470795 * 568 / (8 * |t| ^ 2 * (0.470795 * Real.log |t| + 4.04972)) := by
    rw [div_le_div_iff₀ hden1 hden1]
    -- again just `A·D ≤ B·D` from `A ≤ B` and `0 < D`, both already to hand
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnum2 (by norm_num : (0:ℝ) ≤ 0.470795)) hden1.le
  have hstep2 : (0.470795:ℝ) * 568 / (8 * |t| ^ 2 * (0.470795 * Real.log |t| + 4.04972))
      ≤ 568 / (8 * |t| ^ 2 * Real.log |t|) := by
    rw [div_le_div_iff₀ hden1 hden]
    nlinarith [ht2pos, hL0]
  have hfrac2 := hstep1.trans hstep2
  have hcombine : (566:ℝ) / (8 * |t| ^ 2 * Real.log |t|) + 568 / (8 * |t| ^ 2 * Real.log |t|)
      = 1134 / (8 * |t| ^ 2 * Real.log |t|) := by ring
  linarith [hbase, hfrac1, hfrac2, hcombine]

/-- **The case-(2) `hcompact` claim at a single `k`**, as a `Prop` so that the `∀ k ≥ 4`
statement can be split by cases on `k`.

`hcompact` from `fiori_zeta_interpolation`, instantiated at `a=σ_k=1-k/(2^k-2)`, `b=σ_{k+1}`,
`A=B=1.546`, `p=1/(2^k-2)`, `q=1/(2^{k+1}-2)`, `ra=rb=1`, `Q=e`, `T0=3`.

### Summary of Proof
A definition, not a theorem: it names the body of `interpolated_bound_2_hcompact` at one index.
Factoring it out is what lets the five pieces below (`k = 4,5,6,7` individually, and `k ≥ 8`
uniformly) be stated without repeating the display, and lets the assembly be a case split.

### Lean Notes
The paper's `min_σ` is the subtype infimum `⨅ τ : Set.Icc a b, …`; see the module docstring and
`iInf_mem_Icc_eq_zero` for why the bounded binder `⨅ τ ∈ Set.Icc a b, …` would say something
else entirely.

### References
No tex counterpart.

### Dependencies
**Depends on:** `interpG`, `interpα`, `interpβ`.
**Used by:** `hcompact2_four`, `hcompact2_five`, `hcompact2_six`, `hcompact2_seven`,
`hcompact2_tail`, `interpolated_bound_2_hcompact`. -/
def Hcompact2Claim (k : ℕ) : Prop :=
  ∀ t : ℝ, |t| ≤ 3 →
    ∀ σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
    ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
      < ∏ i, (⨅ τ : Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
            ‖interpG 1.546 1.546 (1 / ((2:ℝ) ^ k - 2)) (1 / ((2:ℝ) ^ (k + 1) - 2))
              (Real.exp 1) i ((τ : ℝ) + t * Complex.I)‖)
          ^ (interpα (1 / ((2:ℝ) ^ k - 2)) 1 i
                * ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - σ)
                / ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - (1 - (k:ℝ) / (2 ^ k - 2)))
              + interpβ (1 / ((2:ℝ) ^ (k + 1) - 2)) 1 i
                * (σ - (1 - (k:ℝ) / (2 ^ k - 2)))
                / ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - (1 - (k:ℝ) / (2 ^ k - 2))))

/-- **The case-(2) compact-window certificates, as a hypothesis class.**

`Hcompact2Claim k` is the `hcompact` hypothesis of the interpolation at the `k`-th chord
`[σ_k, σ_{k+1}]`, `σ_k = 1 - k/(2^k-2)`.  It is needed for every `k ≥ 4`, and is certified in
five pieces: `k = 4, 5, 6, 7` individually, and a single statement covering all `k ≥ 8` at once
through an explicit `k`-uniform lower bound on the right-hand side.

**Evidence.** `Code/indep_arb_hcompact.sage`, arb ball arithmetic, prints `ALL CERTIFIED`:
292, 302, 588 and 926 boxes for `k = 4, 5, 6, 7`, and 232 boxes for the `k ≥ 8` tail, where the
covering is uniform in `k`.  `Code/indep_mpmath_hcompact.py` re-checks pointwise.

**The tail is genuinely uniform in `k`.**  `hcompact2_tail` is a single statement covering every
`k ≥ 8`, and the arb run certifies it as such, through an explicit `k`-uniform lower bound on the
right-hand side rather than a sampled table — see that declaration's References, and the section
comment below for why the split sits at `8`.

### Summary of Proof
A class; no proof.

### Lean Notes
Kept separate from `InterpolationCertificates` because these are a different computation over a
different family of windows, and because `Hcompact2Claim` is defined here rather than in
`PhragmenLindelofSetup`.

### References
`Code/indep_arb_hcompact.sage`, `Code/indep_mpmath_hcompact.py`;
`Assumptions.txt`, Part 1 (the numerical certificates).

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `hcompact2_four`, `hcompact2_five`, `hcompact2_six`, `hcompact2_seven`,
`hcompact2_tail`. -/
class Hcompact2Certificates : Prop where
  /-- `k = 4`; arb-certified over 292 boxes. -/
  hcompact2_four : Hcompact2Claim 4
  /-- `k = 5`; arb-certified over 302 boxes. -/
  hcompact2_five : Hcompact2Claim 5
  /-- `k = 6`; arb-certified over 588 boxes. -/
  hcompact2_six : Hcompact2Claim 6
  /-- `k = 7`; arb-certified over 926 boxes. -/
  hcompact2_seven : Hcompact2Claim 7
  /-- All `k ≥ 8` at once, through a `k`-uniform lower bound on the right-hand side;
  arb-certified over 232 boxes. -/
  hcompact2_tail : ∀ {k : ℕ}, 8 ≤ k → Hcompact2Claim k

variable [Hcompact2Certificates]

/-! ### The five cases of `interpolated_bound_2_hcompact`

The `∀ k ≥ 4` obligation is split into five named claims, all of them fields of
`Hcompact2Certificates`:

* `k = 4,5,6,7` — four finite box checks, certified on their own coverings by
  `Code/indep_arb_hcompact.sage` (292, 302, 588 and 926 boxes) and rechecked pointwise by
  `Code/indep_mpmath_hcompact.py`;
* `k ≥ 8` — one claim covering infinitely many `k` at once, certified on 232 boxes through an
  explicit `k`-uniform lower bound on the right-hand side; see `hcompact2_tail`.

All five carry the same caveat and only that one: the certification is a run of an external
ball-arithmetic program, not a Lean proof term.

The split is at `8` because that is where the two sides separate. On the single box
`Re s ∈ [5/7,1]`, `|Im s| ≤ 3` — the union of every case-(2) strip — `sup |(s-1)ζ(s)| = 1.9139`,
attained at the corner `σ = 1, t = -3`; while `inf RHS` **increases** with `k`: `1.3631` at
`k = 4`, `1.6281`, `1.7918`, `1.8914`, then `1.9508` at `k = 8`, rising to the limit `2.0303`.
`1.9508 > 1.9139` is the crossing. For `k ≤ 7` the strips are still wide and the interpolant
correspondingly small, which is why they resist the uniform treatment. -/

/-- **Case `k = 4`** of `interpolated_bound_2_hcompact`.

### Summary of Proof
Not proved here — the field `Hcompact2Certificates.hcompact2_four`. Numerical: the `k = 4` run of
`Code/indep_arb_hcompact.sage` certifies the exact inequality — pole factor and `⨅_{τ∈[a,b]}`
infima included — by adaptive ball arithmetic on 292 boxes, and
`Code/verify_hcompact_boxes.sage` reports worst pointwise ratio `0.665` for the same case. This
is the tightest of the four finite cases: `Code/verify_hcompact_uniform_k.py` puts
`inf RHS = 1.3631` at `k = 4`, well below the `1.9139` the uniform box of `hcompact2_tail` needs.

### Lean Notes
The certification is a run of an external ball-arithmetic program, not a formal proof term;
turning it into one needs verified interval arithmetic for `ζ` inside Lean, which does not exist
in this snapshot. Every `_hcompact` fact in this file carries that same caveat.

### References
No tex counterpart.

**Independent numeric check.**
`Code/indep_mpmath_hcompact.py`: pointwise worst ratio `0.6646` (at `σ = σ₅`, `t = 0`);
`Code/indep_arb_hcompact.sage`: **certified** with arb on `292` boxes.

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `interpolated_bound_2_hcompact`. -/
theorem hcompact2_four : Hcompact2Claim 4 := Hcompact2Certificates.hcompact2_four

/-- **Case `k = 5`** of `interpolated_bound_2_hcompact`.

### Summary of Proof
Not proved here — the field `Hcompact2Certificates.hcompact2_five`. Numerical, exactly as
`hcompact2_four` at `k = 5`. `Code/verify_hcompact_uniform_k.py` records worst pointwise ratio
`0.5803` and `inf RHS = 1.6281` — still short of the `1.9139` the uniform box needs.

### Lean Notes
As `hcompact2_four`: the certification is not a formal proof term.

### References
No tex counterpart.

**Independent numeric check.**
`Code/indep_mpmath_hcompact.py`: pointwise worst ratio `0.5803` (at `σ = σ₆`, `t = 0`);
`Code/indep_arb_hcompact.sage`: **certified** with arb on `302` boxes.

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `interpolated_bound_2_hcompact`. -/
theorem hcompact2_five : Hcompact2Claim 5 := Hcompact2Certificates.hcompact2_five

/-- **Case `k = 6`** of `interpolated_bound_2_hcompact`.

### Summary of Proof
Not proved here — the field `Hcompact2Certificates.hcompact2_six`. Numerical, exactly as
`hcompact2_four` at `k = 6`. `Code/verify_hcompact_uniform_k.py` records worst pointwise ratio
`0.5403` and `inf RHS = 1.7918` — still short of `1.9139`.

### Lean Notes
As `hcompact2_four`: the certification is not a formal proof term.

### References
No tex counterpart.

**Independent numeric check.**
`Code/indep_mpmath_hcompact.py`: pointwise worst ratio `0.5403` (at `σ = σ₇`, `t = 0`);
`Code/indep_arb_hcompact.sage`: **certified** with arb on `588` boxes.

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `interpolated_bound_2_hcompact`. -/
theorem hcompact2_six : Hcompact2Claim 6 := Hcompact2Certificates.hcompact2_six

/-- **Case `k = 7`** of `interpolated_bound_2_hcompact`, the last case the uniform box misses.

### Summary of Proof
Not proved here — the field `Hcompact2Certificates.hcompact2_seven`. Numerical, exactly as
`hcompact2_four` at `k = 7`. `Code/verify_hcompact_uniform_k.py` records worst pointwise ratio
`0.5191` and `inf RHS = 1.8914`. That is the closest miss — it falls short of the uniform box's
`1.9139` by about `1.2%`, which is exactly why the split sits at `8` and not at `7`.

### Lean Notes
As `hcompact2_four`: the certification is not a formal proof term.

### References
No tex counterpart.

**Independent numeric check.**
`Code/indep_mpmath_hcompact.py`: pointwise worst ratio `0.5191` (at `σ = σ₈`, `t = 0`);
`Code/indep_arb_hcompact.sage`: **certified** with arb on `926` boxes.

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `interpolated_bound_2_hcompact`. -/
theorem hcompact2_seven : Hcompact2Claim 7 := Hcompact2Certificates.hcompact2_seven

/-- **The uniform tail, `k ≥ 8`** — one box covering every remaining case at once.

### Summary of Proof
Not proved here — the field `Hcompact2Certificates.hcompact2_tail`, certified on 232 boxes by
`Code/indep_arb_hcompact.sage`, uniformly in `k`, through the explicit `k`-uniform lower bound
on the right-hand side set out under References.

The shape of the argument: maximum modulus reduces the claim to a bound on `(s-1)ζ(s)` over a
box containing every case-(2) strip, compared against a uniform lower bound on the interpolant.
Both numbers are computed in `Code/verify_hcompact_uniform_k.py`:

* `sup |(s-1)ζ(s)| = 1.9139` over `Re s ∈ [5/7,1]`, `|Im s| ≤ 3`, attained at the corner
  `σ = 1, t = -3`. Widening to `Re s ∈ [1/2,1]` gives the **same** supremum, so the wider box
  costs nothing.
* `inf RHS ≥ 1.9508` for every `k ≥ 8`, since that infimum increases with `k` toward its limit
  `2.0303` (as the strip collapses to `σ = 1`, `RHS → 1.546·|1+it|·|G₂(1+it)|`, itself `≥ 2.03`
  at `t = 0` and larger for `t ≠ 0`).

`1.9508 > 1.9139` separates them, uniformly in `k`.

### Lean Notes
`k` enters the right-hand side through the exponents `interpα (1/(2^k-2))` and
`interpβ (1/(2^(k+1)-2))` and through the range of the infimum over `Icc (σ_k, σ_(k+1))`, not
only through the strip, so the claim is not reducible to a single box check. What makes it
uniform is the explicit `k`-uniform lower bound recorded under References, which replaces any
appeal to a sampled monotonicity in `k`. A Lean proof would need the maximum-modulus reduction
(a formal analytic step) on top of the interval-arithmetic-for-`ζ` obstacle that
`hcompact2_four`..`hcompact2_seven` share.

### References
No tex counterpart.

**Independent numeric check — the infinitely many `k` handled.**
`Code/indep_mpmath_hcompact.py` gives the per-`k` pointwise worst ratios `0.5074, 0.5008,
0.4971, …, 0.4927` for `k = 8, …, 16` (monotone, tending to `≈ 0.4926`). More importantly,
`Code/indep_arb_hcompact.sage` **certifies all `k ≥ 8` at once**, replacing the asserted
monotonicity in `k` by an explicit `k`-uniform lower bound: with `A = 1.546`, `p₈ = 1/254`,
`q₈ = 1/510`,
`RHS_k(σ,t) ≥ min(b, b^{1+p₈}) · (1-σ₉)^{q₈} · inf_{τ∈[σ₈,1]} ‖GPL_e(τ+it)‖`,
`b = A^{1/(1+p₈)} √(σ₈²+t²)`, valid for every `k ≥ 8` and `σ ∈ [σ_k, σ_{k+1}]` (each of the
three factors is bounded below termwise: `p, q` decrease and `σ_k` increases in `k`;
`(1-σ_{k+1})^{q_k}` is increasing in `k`, checked for `k ≤ 40` and monotone beyond;
`(A^{p/(p+1)})^{w_b} ≥ 1`). Against it, `sup_{σ∈[σ₈,1]} ‖(s-1)ζ(s)‖` is certified on `232` boxes,
with the boxes inside `|s-1| ≤ 1/4` handled by the Laurent bound
`‖(s-1)ζ(s) - 1‖ ≤ |s-1|·max_{|w-1|=1/4}‖ζ(w) - 1/(w-1)‖` (arb cannot evaluate `ζ` on a ball
containing `1`). Worst certified `U/L = 0.797`.

### Dependencies
**Depends on:** `Hcompact2Claim`.
**Used by:** `interpolated_bound_2_hcompact`. -/
theorem hcompact2_tail {k : ℕ} (hk : 8 ≤ k) : Hcompact2Claim k :=
  Hcompact2Certificates.hcompact2_tail hk

/-- **The numeric obligation of `interpolated_bound_2`, isolated.** `hcompact` from
`fiori_zeta_interpolation`, instantiated at `a=σ_k=1-k/(2^k-2)`, `b=σ_{k+1}`, `A=B=1.546`,
`p=1/(2^k-2)`, `q=1/(2^{k+1}-2)`, `ra=rb=1`, `Q=e`, `T0=3`, for a general `k ≥ 4`.

### Summary of Proof
Derived, by cases on `k`: `interval_cases` splits `4 ≤ k ≤ 7` into the four finite instances, and
`hcompact2_tail` covers `8 ≤ k` uniformly. See the section comment above for why the split sits
at `8`.

### Lean Notes
The five pieces are all fields of `Hcompact2Certificates`, and all five carry the same caveat:
the certification is a run of an external ball-arithmetic program, not a Lean proof term.
`hcompact2_tail` is the one that quantifies over infinitely many `k`; it is certified uniformly
in `k`, through an explicit `k`-uniform lower bound on the right-hand side rather than a sampled
table, and needs a maximum-modulus reduction on top of the shared obstacle — see that
declaration.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Hcompact2Claim`, `hcompact2_four`, `hcompact2_five`, `hcompact2_six`,
`hcompact2_seven`, `hcompact2_tail`.
**Used by:** `interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem interpolated_bound_2_hcompact {k : ℕ} (hk : 4 ≤ k) :
    ∀ t : ℝ, |t| ≤ 3 →
      ∀ σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
              ‖interpG 1.546 1.546 (1 / ((2:ℝ) ^ k - 2)) (1 / ((2:ℝ) ^ (k + 1) - 2))
                (Real.exp 1) i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (1 / ((2:ℝ) ^ k - 2)) 1 i
                  * ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - σ)
                  / ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - (1 - (k:ℝ) / (2 ^ k - 2)))
                + interpβ (1 / ((2:ℝ) ^ (k + 1) - 2)) 1 i
                  * (σ - (1 - (k:ℝ) / (2 ^ k - 2)))
                  / ((1 - ((k:ℝ) + 1) / (2 ^ (k+1) - 2)) - (1 - (k:ℝ) / (2 ^ k - 2)))) := by
  have h : Hcompact2Claim k := by
    rcases Nat.lt_or_ge k 8 with h7 | h8
    · interval_cases k
      · exact hcompact2_four
      · exact hcompact2_five
      · exact hcompact2_six
      · exact hcompact2_seven
    · exact hcompact2_tail (by omega)
  exact h

/-- **`Proposition \ref{prop:interpolation}` (Proposition 35), case (2)**: for `k ≥ 4` and
`1 - k/(2^k-2) ≤ σ ≤ 1 - (k+1)/(2^{k+1}-2)`, interpolating between consecutive `YANG2024128124`
lines.

**Rests on `interpolated_bound_2_hcompact`**, which splits into five fields of
`Hcompact2Certificates`: four finite box checks (`k = 4,5,6,7`) and one claim covering every
`k ≥ 8` at once. All five are certified outside Lean by ball arithmetic; none is provable inside
Lean without certified interval arithmetic for `ζ`.

### Summary of Proof
This uses `k ≥ 4`, matching `ZerosInShortIntervals.tex` and
`ExternalFacts.yang_critical_strip_bound`'s citation check (`YANG2024128124` requires `k ≥ 4`; at
`k=3` this range is `[1/2,5/7]`, already covered by cases (1a)-(1c) via
`HIARY2024195`/`revers2026...`/`patel2023explicit` instead). Both boundary inputs are the *same*
external bound (`yang_critical_strip_bound`, at `k` and at `k+1`), which is why the two constants
collapse into the single flat `log 1.546` term (`w_a + w_b = 1`) and the `loglog` coefficient is
likewise `1`. Note the conclusion here is stated in terms of `log|t|`/`loglog|t|` rather than
`log|T|`/`loglog|T|`, so no window conversion is involved — but `log_bound_of_interp` supplies the
`T`-form, which is *stronger* by the same window estimate, so it is applied and then transported.
**Applies Phragmén–Lindelöf to `(s-1)ζ(s)` rather than `ζ(s)`** (see
`PhragmenLindelofSetup.fiori_zeta_interpolation`) — necessary here: with `f = ζ` directly, the
compact-range hypothesis `hcompact` is **false**, and increasingly so as `k` grows. It implies
`‖ζ(b_k)‖ ≤ 1.546·(1-b_k)^{q}·‖GPL_e(b_k)‖` at `t = 0`, whose left side blows up like `1/(1-b_k) =
(2^{k+1}-2)/(k+1)` while the right side stays near `2` — `k = 4`: `5.435` vs `1.911`; `k = 6`:
`17.427` vs `1.984`; `k = 8`: `56.091` vs `2.014`; `k = 10`: `185.42` vs `2.025`. That divergence
is exactly `ζ`'s pole at `s = 1`, which `b_k → 1` walks into, and `(s-1)ζ(s) → 1` there kills it.
With the pole factor the worst ratio over the whole box is `0.665` at `k = 4` and *decreases* in
`k`, settling at `0.4927`. `Code/indep_arb_hcompact.sage` certifies `k = 4,5,6,7` on their own
coverings and every `k ≥ 8` at once.

### References
tex: `Proposition \ref{prop:interpolation}` (Proposition 35), case (2).

### Dependencies
**Depends on:** `GPL_ge_log`, `fiori_zeta_interpolation`, `half_le_sigmaYang`,
`interpolated_bound_2_hcompact`, `log_bound_of_interp_self`, `sigmaYang_lt_succ`,
`sigmaYang_mem_Ioo`, `twenty_lt_log'`, `two_lt_two_pow`, `yang_critical_strip_bound`,
`yang_interp_coeff_eq`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_2_pointwise`, `zeta_chord_bound_nonneg`. -/
theorem interpolated_bound_2 {T t σ : ℝ} {k : ℕ} (hk : 4 ≤ k) (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1))
    (hσ : σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2))) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < ((1 - σ) / (k - 1 + 2 ^ (1 - (k : ℤ) : ℤ) : ℝ) - 1 / (2 ^ k * (k - 1) + 2)) * Real.log |t|
        + Real.log (Real.log |t|) + Real.log 1.546 + 3 / T := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hk1 : 4 ≤ k + 1 := by omega
  have hT0 : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have htpos : (0:ℝ) < t := by linarith [ht.1]
  have hatt : |t| = t := abs_of_pos htpos
  have ht3 : (3:ℝ) ≤ |t| := by rw [hatt]; linarith [ht.1]
  -- the Yang-interval arithmetic: `1/2 ≤ a < b < 1`
  set a : ℝ := 1 - (k : ℝ) / (2 ^ k - 2) with ha_def
  set b : ℝ := 1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2) with hb_def
  have hbk : b < 1 := by
    rw [hb_def]
    have := (sigmaYang_mem_Ioo hk1).2
    push_cast at this ⊢
    exact_mod_cast this
  have hak : (1:ℝ) / 2 ≤ a := by rw [ha_def]; exact half_le_sigmaYang hk
  have hab : a < b := by rw [ha_def, hb_def]; exact_mod_cast sigmaYang_lt_succ hk
  have h2k : (2:ℝ) < 2 ^ k := two_lt_two_pow hk
  have h2k1 : (2:ℝ) < 2 ^ (k + 1) := two_lt_two_pow hk1
  have h16k : (16:ℝ) ≤ 2 ^ k := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h16k1 : (16:ℝ) ≤ 2 ^ (k + 1) := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpk : (0:ℝ) < 1 / ((2:ℝ) ^ k - 2) := by
    apply div_pos one_pos; linarith
  have hqk : (0:ℝ) < 1 / ((2:ℝ) ^ (k + 1) - 2) := by
    apply div_pos one_pos; linarith
  -- weights
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hba : (0:ℝ) < b - a := by linarith
  have hwa0 : (0:ℝ) ≤ wa := by rw [hwa_def]; apply div_nonneg (by linarith) hba.le
  have hwb0 : (0:ℝ) ≤ wb := by rw [hwb_def]; apply div_nonneg (by linarith) hba.le
  have hsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  have hinterp := fiori_zeta_interpolation (a := a) (b := b) (A := 1.546)
      (B := 1.546) (p := 1 / ((2:ℝ) ^ k - 2)) (q := 1 / ((2:ℝ) ^ (k + 1) - 2))
      (ra := 1) (rb := 1) (Q := Real.exp 1) (T0 := 3)
      hab hak hbk (by norm_num) (by norm_num) hpk hqk (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (by rw [div_le_one (by linarith)]; linarith [h16k])
      (by rw [div_le_one (by linarith)]; linarith [h16k1]) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two, hak]) (by nlinarith [Real.exp_one_gt_two, hbk])
      (fun h => absurd h (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      -- boundary bound at `σ = σ_k`: Yang at `k`
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one, ha_def]
        have hy := yang_critical_strip_bound (k := k) hk (t := |t'|) ht'
        push_cast at hy ⊢
        exact hy)
      -- boundary bound at `σ = σ_{k+1}`: Yang at `k+1`
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one, hb_def]
        have hy := yang_critical_strip_bound (k := k + 1) hk1 (t := |t'|) ht'
        push_cast at hy ⊢
        convert hy using 4)
      -- **compact range**: the numeric obligation, isolated as `interpolated_bound_2_hcompact`
      (ha_def ▸ hb_def ▸ interpolated_bound_2_hcompact hk)
      σ ⟨hσ0, hσ1⟩ t (by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
        have he2 : Real.exp 1 ^ 2 < 7.39 := by nlinarith
        have hTb : (10:ℝ) ^ (12:ℕ) < T := hT
        have hTn : (1000000000000:ℝ) < T := by norm_num at hTb; linarith
        rw [hatt]
        nlinarith [ht.1, hTn])
  rw [← hwa_def, ← hwb_def] at hinterp
  have hlogw : (1:ℝ) * wa + 1 * wb = 1 := by linarith [hsum]
  rw [hlogw] at hinterp
  -- the interpolated `log|t|` coefficient equals the one displayed in the statement
  set c : ℝ := 1 / ((2:ℝ) ^ k - 2) * wa + 1 / ((2:ℝ) ^ (k + 1) - 2) * wb with hc_def
  have hc0 : (0:ℝ) ≤ c := by rw [hc_def]; positivity
  have hcle : c ≤ 1 / 2 := by
    have h1 : 1 / ((2:ℝ) ^ k - 2) ≤ 1 / 14 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (16:ℝ) ≤ 2 ^ k := by
        calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
          _ ≤ 2 ^ k := by
              apply pow_le_pow_right₀ (by norm_num) hk
      linarith
    have h2 : 1 / ((2:ℝ) ^ (k + 1) - 2) ≤ 1 / 14 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (16:ℝ) ≤ 2 ^ (k + 1) := by
        calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
          _ ≤ 2 ^ (k + 1) := by
              apply pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    rw [hc_def]
    nlinarith
  have hbridge := log_bound_of_interp_self (L := ‖riemannZeta (σ + t * Complex.I)‖)
      (A := (1.546 : ℝ) ^ wa) (B := (1.546 : ℝ) ^ wb) (c := c) (w := 1) (T := T) (t := t)
      (norm_nonneg _) (by positivity) (by positivity) hT ht
      (by
        have hlt : (1:ℝ) < |t| := by rw [hatt]; linarith [ht.1]
        have hlogt : 0 < Real.log |t| := Real.log_pos hlt
        have hlogt20 : 20 < Real.log |t| := by
          rw [hatt]; exact twenty_lt_log' (by linarith [ht.1])
        have hllt : 0 < Real.log (Real.log |t|) := Real.log_pos (by linarith)
        have e1 : Real.log ((1.546:ℝ) ^ wa) = wa * Real.log 1.546 :=
          Real.log_rpow (by norm_num) _
        have e2 : Real.log ((1.546:ℝ) ^ wb) = wb * Real.log 1.546 :=
          Real.log_rpow (by norm_num) _
        have e3 : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        rw [e1, e2]
        have : (0:ℝ) ≤ c * Real.log |t| := by positivity
        nlinarith)
      hinterp
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 1.546),
    Real.log_rpow (by norm_num : (0:ℝ) < 1.546)] at hbridge
  -- match the displayed coefficient (a rational-function identity in `x := 2^k` and `k`)
  have hx : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hzp : ((2:ℝ) ^ (1 - (k:ℤ) : ℤ)) = 2 / (2:ℝ) ^ k := by
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hsucc : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hk4 : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h16 : (16:ℝ) ≤ (2:ℝ) ^ k := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hcoef : c = (1 - σ) / ((k : ℝ) - 1 + 2 / (2:ℝ) ^ k)
      - 1 / ((2:ℝ) ^ k * ((k:ℝ) - 1) + 2) := by
    rw [hc_def, hwa_def, hwb_def, ha_def, hb_def, hsucc]
    exact yang_interp_coeff_eq h16 hk4
  rw [hcoef, ← hzp] at hbridge
  have hlog1546 : wa * Real.log 1.546 + wb * Real.log 1.546 = Real.log 1.546 := by
    have he : wa * Real.log 1.546 + wb * Real.log 1.546 = (wa + wb) * Real.log 1.546 := by ring
    rw [he, hsum, one_mul]
  linarith [hbridge, hlog1546]

/-- **Tight, pointwise version of `interpolated_bound_2`**: no `T`-window at all (this case was
already pointwise), explicit `σ`-dependent `O(1/t²)` error, and — as in case (1a) — **no extra
headroom above `T0 = 3` needed**: `A = B = 1.546 > 1` makes every summand of the log-sum manifestly
nonnegative once `\log|t| > 1` (true since `T0 = 3 > e`), so `T1 := T0` works directly, uniformly
in `k`.

### Summary of Proof
Same interpolation as `interpolated_bound_2` — consecutive Yang lines `σ_k` and `σ_{k+1}`, both
anchored on `yang_critical_strip_bound`, so `A = B = 1.546` and `ra = rb = 1` — stated pointwise at
`t` with the `O(1/t²)` tail kept explicit, via `GPL_le_log_tight`. Because `ra = rb` the
`σ`-monotonicity hypothesis is vacuous here, so the compact range stays `|t| ≤ 3`, unlike case
(1a).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL_ge_log`, `fiori_zeta_interpolation_tight`, `half_le_sigmaYang`,
`interpolated_bound_2_hcompact`, `sigmaYang_lt_succ`, `sigmaYang_mem_Ioo`, `two_lt_two_pow`,
`yang_critical_strip_bound`, `yang_interp_coeff_eq`, `zeta_norm_abs_im`.
**Used by:** `interpolated_bound_2_tight_simple`, `zeta_chord_bound_nonneg_tight`. -/
theorem interpolated_bound_2_tight {t σ : ℝ} {k : ℕ} (hk : 4 ≤ k)
    (ht : (3:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2))) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ ((1 - σ) / (k - 1 + 2 ^ (1 - (k : ℤ) : ℤ) : ℝ) - 1 / (2 ^ k * (k - 1) + 2)) * Real.log |t|
          + Real.log (Real.log |t|) + Real.log 1.546
          + (3 / (2 * |t| ^ 2)
              + (2 * ((Real.exp 1 + σ) ^ 2 + (Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                  / (8 * |t| ^ 2 * Real.log |t|)) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hk1 : 4 ≤ k + 1 := by omega
  set a : ℝ := 1 - (k : ℝ) / (2 ^ k - 2) with ha_def
  set b : ℝ := 1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2) with hb_def
  have hbk : b < 1 := by
    rw [hb_def]
    have := (sigmaYang_mem_Ioo hk1).2
    push_cast at this ⊢
    exact_mod_cast this
  have hak : (1:ℝ) / 2 ≤ a := by rw [ha_def]; exact half_le_sigmaYang hk
  have hab : a < b := by rw [ha_def, hb_def]; exact_mod_cast sigmaYang_lt_succ hk
  have h2k : (2:ℝ) < 2 ^ k := two_lt_two_pow hk
  have h2k1 : (2:ℝ) < 2 ^ (k + 1) := two_lt_two_pow hk1
  have h16k : (16:ℝ) ≤ 2 ^ k := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h16k1 : (16:ℝ) ≤ 2 ^ (k + 1) := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpk : (0:ℝ) < 1 / ((2:ℝ) ^ k - 2) := by
    apply div_pos one_pos; linarith
  have hqk : (0:ℝ) < 1 / ((2:ℝ) ^ (k + 1) - 2) := by
    apply div_pos one_pos; linarith
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hba : (0:ℝ) < b - a := by linarith
  have hwa0 : (0:ℝ) ≤ wa := by rw [hwa_def]; apply div_nonneg (by linarith) hba.le
  have hwb0 : (0:ℝ) ≤ wb := by rw [hwb_def]; apply div_nonneg (by linarith) hba.le
  have hsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  have hinterp := fiori_zeta_interpolation_tight (a := a) (b := b) (A := 1.546)
      (B := 1.546) (p := 1 / ((2:ℝ) ^ k - 2)) (q := 1 / ((2:ℝ) ^ (k + 1) - 2))
      (ra := 1) (rb := 1) (Q := Real.exp 1) (T0 := 3) (T1 := 3)
      hab hak hbk (by norm_num) (by norm_num) hpk hqk (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (le_refl _)
      (by rw [div_le_one (by linarith)]; linarith [h16k])
      (by rw [div_le_one (by linarith)]; linarith [h16k1]) (by norm_num)
      (by nlinarith [Real.exp_one_gt_two, hak]) (by nlinarith [Real.exp_one_gt_two, hbk])
      (fun h => absurd h (by norm_num))
      (by
        intro t' ht'
        exact GPL_ge_log _ _ _ t' (by linarith))
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one, ha_def]
        have hy := yang_critical_strip_bound (k := k) hk (t := |t'|) ht'
        push_cast at hy ⊢
        exact hy)
      (by
        intro t' ht'
        rw [zeta_norm_abs_im, Real.rpow_one, hb_def]
        have hy := yang_critical_strip_bound (k := k + 1) hk1 (t := |t'|) ht'
        push_cast at hy ⊢
        convert hy using 4)
      (ha_def ▸ hb_def ▸ interpolated_bound_2_hcompact hk)
      -- `hnn`: `A=B=1.546>1` makes every summand `≥0` once `\log|t|>1` (true since `T0=3>e`).
      (by
        intro σ' hσ' t' ht'
        have hL1 : (1:ℝ) < Real.log |t'| := by
          have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          have h1 : Real.exp 1 < |t'| := by linarith
          have hlog := Real.log_lt_log (Real.exp_pos 1) h1
          rwa [Real.log_exp] at hlog
        have hlogLpos : (0:ℝ) < Real.log (Real.log |t'|) := Real.log_pos hL1
        have hwa'0 : (0:ℝ) ≤ (b - σ') / (b - a) := div_nonneg (by linarith [hσ'.2]) hba.le
        have hwb'0 : (0:ℝ) ≤ (σ' - a) / (b - a) := div_nonneg (by linarith [hσ'.1]) hba.le
        have hlogBpos : (0:ℝ) ≤ Real.log 1.546 := Real.log_nonneg (by norm_num)
        have hLpos : (0:ℝ) ≤ Real.log |t'| := by linarith
        have hp1 : (0:ℝ) ≤ (b - σ') / (b - a) * Real.log |t'| := mul_nonneg hwa'0 hLpos
        have hp2 : (0:ℝ) ≤ (σ' - a) / (b - a) * Real.log |t'| := mul_nonneg hwb'0 hLpos
        have hp3 : (0:ℝ) ≤ (b - σ') / (b - a) * Real.log (Real.log |t'|) :=
          mul_nonneg hwa'0 hlogLpos.le
        have hp4 : (0:ℝ) ≤ (σ' - a) / (b - a) * Real.log (Real.log |t'|) :=
          mul_nonneg hwb'0 hlogLpos.le
        have hp5 : (0:ℝ) ≤ (b - σ') / (b - a) * Real.log 1.546 := mul_nonneg hwa'0 hlogBpos
        have hp6 : (0:ℝ) ≤ (σ' - a) / (b - a) * Real.log 1.546 := mul_nonneg hwb'0 hlogBpos
        nlinarith [hp1, hp2, hp3, hp4, hp5, hp6])
      σ ⟨hσ0, hσ1⟩ t ht
  rw [← hwa_def, ← hwb_def] at hinterp
  have hlogw : (1:ℝ) * wa + 1 * wb = 1 := by linarith [hsum]
  rw [hlogw] at hinterp
  set c : ℝ := 1 / ((2:ℝ) ^ k - 2) * wa + 1 / ((2:ℝ) ^ (k + 1) - 2) * wb with hc_def
  have hx : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hzp : ((2:ℝ) ^ (1 - (k:ℤ) : ℤ)) = 2 / (2:ℝ) ^ k := by
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hsucc : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hk4 : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h16 : (16:ℝ) ≤ (2:ℝ) ^ k := by
    calc (16:ℝ) = 2 ^ (4:ℕ) := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hcoef : c = (1 - σ) / ((k : ℝ) - 1 + 2 / (2:ℝ) ^ k)
      - 1 / ((2:ℝ) ^ k * ((k:ℝ) - 1) + 2) := by
    rw [hc_def, hwa_def, hwb_def, ha_def, hb_def, hsucc]
    exact yang_interp_coeff_eq h16 hk4
  rw [hcoef, ← hzp] at hinterp
  have hlog1546 : wa * Real.log 1.546 + wb * Real.log 1.546 = Real.log 1.546 := by
    have he : wa * Real.log 1.546 + wb * Real.log 1.546 = (wa + wb) * Real.log 1.546 := by ring
    rw [he, hsum, one_mul]
  linarith [hinterp, hlog1546]

/-- **Auxiliary fact for `interpolated_bound_2_tight_simple`**: `7k+4 ≤ 2^{k+1}` for `k ≥ 4`,
equivalently `1 - k/(2^k-2) ≥ 5/7`.

### Summary of Proof
The Yang-interval ranges `[1-k/(2^k-2), 1-(k+1)/(2^{k+1}-2)]` for `k ≥ 4` are increasing in `k` and
their union is `[5/7,1)`, with `k = 4` giving the extremal left endpoint `5/7` exactly (equality
holds here at `k = 4`: `7·4+4 = 32 = 2^5`).
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_2_tight_simple`. -/
theorem seven_k_add_four_le_two_pow (k : ℕ) (hk : 4 ≤ k) : (7 * (k:ℝ) + 4) ≤ 2 ^ (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : (2:ℝ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
    have hn' : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    push_cast
    nlinarith [ih, h2, hn']

/-- **Simplified corollary of `interpolated_bound_2_tight`**: the `σ`-dependent `O^*` numerator
`2((e+σ)²+(e+2-σ)²)+(2-2σ)²` (same shape as `interpolated_bound_1a_tight_simple`, with `Q=e`) is
decreasing in `σ` on `(-∞,1)`, so it is maximized at the smallest `σ` occurring across *all* `k≥4`.

### Summary of Proof
By `seven_k_add_four_le_two_pow`, every `k≥4` range lies in `[5/7,1)`, so `σ≥5/7` uniformly, and
the numerator is bounded by its value at `σ=5/7`, `≈55.96 < 56`. Matches the fourth display of
Proposition `\ref{prop:interpolation}` (Proposition 35), `ZerosInShortIntervals.tex`.
### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_2_tight`, `seven_k_add_four_le_two_pow`, `two_lt_two_pow`,
`exp_one_add_one_sq_le`.
**Used by:** `zeta_chord_bound_nonneg_tight_simple`. -/
theorem interpolated_bound_2_tight_simple {t σ : ℝ} {k : ℕ} (hk : 4 ≤ k)
    (ht : (3:ℝ) < |t|)
    (hσ : σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2))) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      ≤ ((1 - σ) / (k - 1 + 2 ^ (1 - (k : ℤ) : ℤ) : ℝ) - 1 / (2 ^ k * (k - 1) + 2)) * Real.log |t|
          + Real.log (Real.log |t|) + Real.log 1.546
          + (3 / (2 * |t| ^ 2) + 56 / (8 * |t| ^ 2 * Real.log |t|)) := by
  have hbase := interpolated_bound_2_tight hk ht hσ
  obtain ⟨hσ0, hσ1⟩ := hσ
  have h2k : (2:ℝ) < 2 ^ k := two_lt_two_pow hk
  have hx : (0:ℝ) < (2:ℝ) ^ k - 2 := by linarith
  have hpow : (7 * (k:ℝ) + 4) ≤ 2 ^ (k + 1) := seven_k_add_four_le_two_pow k hk
  have hsucc : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hsucc] at hpow
  have hkey : (k:ℝ) / (2 ^ k - 2) ≤ 2 / 7 := by
    rw [div_le_div_iff₀ hx (by norm_num : (0:ℝ) < 7)]
    nlinarith [hpow]
  have ha57 : (5 / 7 : ℝ) ≤ 1 - (k:ℝ) / (2 ^ k - 2) := by linarith [hkey]
  have hσge57 : (5 / 7 : ℝ) ≤ σ := le_trans ha57 hσ0
  have h2k1 : (2:ℝ) < 2 ^ (k + 1) := two_lt_two_pow (by omega : 4 ≤ k + 1)
  have hy : (0:ℝ) < (2:ℝ) ^ (k + 1) - 2 := by linarith
  have hqpos : (0:ℝ) < ((k:ℝ) + 1) / (2 ^ (k + 1) - 2) := div_pos (by positivity) hy
  have hσlt1 : σ < 1 := by linarith [hσ1, hqpos]
  have ht1 : (1:ℝ) < |t| := by linarith
  have hL0 : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have habs : |2 - 2 * σ| ^ 2 = (2 - 2 * σ) ^ 2 := sq_abs _
  have ht2pos : (0:ℝ) < |t| ^ 2 := by positivity
  have hden : (0:ℝ) < 8 * |t| ^ 2 * Real.log |t| := mul_pos (mul_pos (by norm_num) ht2pos) hL0
  have hnum : 2 * ((Real.exp 1 + σ) ^ 2 + (Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2 ≤ 56 := by
    -- `ring`-normalised the goal is `4(e+1)² + 8(1-σ)² ≤ 56`.  Here `σ` ranges over `[5/7, 1)`,
    -- so the maximum is at `σ = 5/7`, and the single product `(σ-5/7)(1-σ) ≥ 0` is all the
    -- nonlinearity there is; margin `0.044`.
    rw [habs]
    linarith only [exp_one_add_one_sq_le, hσge57,
      mul_nonneg (by linarith : (0:ℝ) ≤ σ - 5 / 7) (by linarith : (0:ℝ) ≤ 1 - σ)]
  have hfrac : (2 * ((Real.exp 1 + σ) ^ 2 + (Real.exp 1 + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
      / (8 * |t| ^ 2 * Real.log |t|) ≤ 56 / (8 * |t| ^ 2 * Real.log |t|) := by
    -- after the cross-multiplication this is exactly `A·D ≤ 56·D` from `A ≤ 56`, `0 < D`
    rw [div_le_div_iff₀ hden hden]; exact mul_le_mul_of_nonneg_right hnum hden.le
  linarith [hbase, hfrac]

/-! ### **Proposition `\ref{prop:interpolation}` (Proposition 35)**
(`ZerosInShortIntervals.tex`), the pointwise form

`interpolated_bound_1a`, `_1b`, `_1c`, `_2` above are stated in a `T`-windowed form (a fixed
`T > 10¹²` and `t` ranging over `[T-1,T+1]`), because that is the shape every downstream caller
(`LittlewoodMethod`, `MainTheorem`, ...) actually needs. Proposition `\ref{prop:interpolation}`
(Proposition 35) itself is stated pointwise —
a single bound at `t` directly, no window — matching cases (1) and (2) of its `enumerate`. The four
`_pointwise` theorems below are exactly that restatement: each is the windowed theorem specialized
at `T := t` (so the window hypothesis `t ∈ [T-1,T+1]` becomes the trivial `t ∈ [t-1,t+1]`), with
**no change to the proof** — this is the "reuse the machinery, only the final step changes" the
appendix's own proof sketch already does structurally, since `fiori_zeta_interpolation`'s window
hypothesis `(Q+2)²+K ≤ |t|` was already stated purely in terms of `|t|`, never `|T|`; the `T`-window
was only ever an artifact of the log-conversion bridge (`log_bound_of_interp`/`_1c`), which vanishes
identically when `T = t`.

**The error term: these four pointwise theorems carry `O^*(3/t)`, where the tex's Proposition 35
displays an `O^*(·/t²)` — and the tex is right.** The `/t²` shape is confirmed against
doi:10.1016/j.jmaa.2026.130404, pp. 7–8 (the discussion immediately
preceding its Theorem 7): that paper's own `G_{Q₁,Q₂}` (its name for `GPL`) satisfies
`\log|t| < |G_{Q₁,Q₂}(σ+it)| < (1+O(1/(t²\log|t|)))\log|t|` — quadratic, in fact a shade better.
The linear `3/t` comes from `PhragmenLindelofSetup.GPL_le_log`, which bounds
`‖GPL_Q(σ+it)‖ ≤ |Re| + |Im|` (`Complex.norm_le_abs_re_add_abs_im`, an `L¹`-style triangle
inequality) *after* computing `Re` and `Im` separately. That discards the cancellation the paper
exploits — `\arg(1+σ+it) ∼ -\arg(1-σ-it)`, so the two `\arctan` error terms cancel before norms
are taken: `Im` alone is `Θ(1/t)`, and adding it linearly to the `Θ(\log|t|)` real part inflates
what would be a quadratic correction in the true Euclidean norm into a linear one. The same thing
happens in `G1shift_le`'s `|2σ|/(2|t|)` term for case (1c).

**The quadratic form is available here, in the `_tight` family above.**
`PhragmenLindelofSetup.GPL_le_log_tight` bounds the true Euclidean norm through
`√(x²+y²) ≤ x + y²/(2x)`, so the `Θ(1/|t|)` imaginary part enters only quadratically — the paper's
cancellation, reached by a different route — and `G1shift_le_tight` does the same for case (1c).
`interpolated_bound_1a_tight_simple`, `_1b_tight_simple`, `_1c_tight_simple` and
`_2_tight_simple` consume them and land on exactly the tex's displayed errors
`O^*(3/(2t²) + C/(t²\log|t|))`, with `C = 283/4, 579/4, 567/4` and `7` respectively. The four
`_pointwise` theorems below simply do not repeat that substitution: they are the plain
restatement of the windowed originals. (Contrast
`PhragmenLindelofSetup.norm_ratio_window`/`sqrt_le_window`, the pole-killing `(s-1)ζ(s)` device's
own cost, which already *is* `O(1/t²)` and was never the bottleneck.)

**The threshold.** Each `_pointwise` theorem below reuses its windowed original's `T > 10¹²`
hypothesis unchanged, which is certainly not the true minimum; the tex states Proposition 35 for
`t > 12`. The `(Q+2)²+55`-type window — `379` for (1b) at `Q = 16`, `≈221` for (1a) at `Q = 4e`,
`≈77` for (2) at `Q = e`, and `≈276` for (1c), whose `fiori_zeta_interpolation_1c` uses the wider
`(Q+2)²+110` — is *not* a restriction coming from `ExternalFacts.fiori_phragmenLindelof` itself:
that hypothesis's conclusion holds unconditionally for every real `t` (see its statement, whose
closing `∀ σ, ∀ t` carries no lower bound on `|t|` at all). The window is entirely a byproduct of
`fiori_zeta_interpolation`'s own subsequent choice to collapse the raw `∏ Gᵢ^{...}` conclusion into
the clean asymptotic shape `(1+1/|t|)·A^{...}·B^{...}·|t|^{...}·\log|t|^{...}`, which needs `|t|`
large enough that `sqrt_le_window`/`GPL_le_log`'s approximations of `‖σ+it‖` by `|t|` and `‖GPL_Q‖`
by `\log|t|` are both tight. The only threshold `fiori_phragmenLindelof` itself forces is `T0`, the
point up to which the compact-range hypothesis `hf_small_t`/`hcompact` is verified — `4e+1≈11.87`
for (1a)/(1c), `3` for (1b)/(2) — dramatically smaller than `379`. The `_tight` family already
reaches that floor, precisely because its window correction is `O(1/t²)`:
`interpolated_bound_1a_tight` and `_1c_tight` ask only `|t| > 4e+1`, `_2_tight` only `|t| > 3`,
and `_1b_tight` only `|t| > 8` — and that `8` is a sign requirement on the log-sum, not a window.
So `379`/`276`/`221`/`77` are the thresholds of the *non-tight* clean asymptotic form alone (still
far below `10¹²`), and `T0` is what the underlying theorem allows.

**These four theorems are proved only for real `t > 10¹²` (not `|t| > 10¹²`).** This restriction is
inherited unchanged from `interpolated_bound_1a`/`_1b`/`_1c`/`_2` (all four windowed originals force
`t ≥ T - 1 > 10¹² - 1 > 0` via their own `hT`/`ht`), not introduced here. The displayed `\log|t|` in
the `.tex` is a two-sided claim; the negative-`t` half is not separately formalized here, though it
should follow immediately from `riemannZeta_conj` (`‖ζ(σ-it)‖ = ‖ζ(σ+it)‖`). -/

/-- **Proposition `\ref{prop:interpolation}` (Proposition 35), case (1a), pointwise form.**
For `1/2 ≤ σ ≤ 5/7` and `t > 10¹²`, interpolating between the Patel–Yang sub-Weyl half-line bound
(`|ζ(1/2+it)| ≤ 66.7|t|^{27/164}`) at `σ = 1/2` and Yang's critical-strip bound at `σ = 5/7`.

### Summary of Proof
Proof: nothing new — this is `interpolated_bound_1a` specialised at `T := t`, so its window
hypothesis `t ∈ [T-1, T+1]` becomes trivially true. See the section note above for why the windowed
form was proved first, and for the `3/t` (rather than the source's `O^*(·/t²)`) error term.

### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1a`.
**Used by:** `Jensen.JensenScaleConstantsAlt.zeta_chord_alt_zero`, the `k = 0` chord of the
alternative coefficient triple of `Remark \ref{rem:altcoefficients}` (Remark 7). -/
theorem interpolated_bound_1a_pointwise {t σ : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (47 / 123 - 107 / 246 * σ) * Real.log |t| + 14 / 3 * (σ - 1 / 2) * Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 66.7 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + 3 / t :=
  interpolated_bound_1a (T := t) (t := t) ht ⟨by linarith, by linarith⟩ hσ

/-- **Proposition `\ref{prop:interpolation}` (Proposition 35), case (1b), pointwise form.**
Same range `1/2 ≤ σ ≤ 5/7` as case (1a), but anchored at `σ = 1/2` on the Hiary–Revers half-line
bound `|ζ(1/2+it)| ≤ 0.611|t|^{1/6}\log|t|` instead of the sub-Weyl one, giving the better
`log|t|`-exponent `4(1-σ)/9 - 1/18` at the cost of a `log log|t|` term.

### Summary of Proof
Proof: `interpolated_bound_1b` specialised at `T := t`; see the section note above.

### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1b`.
**Used by:** none yet — the windowed form is what downstream callers currently consume. -/
theorem interpolated_bound_1b_pointwise {t σ : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log 0.611 + 14 / 3 * (σ - 1 / 2) * Real.log 1.546
        + 3 / t :=
  interpolated_bound_1b (T := t) (t := t) ht ⟨by linarith, by linarith⟩ hσ

/-- **Proposition `\ref{prop:interpolation}` (Proposition 35), case (1c), pointwise form.**
As case (1b), but using Revers' sharper asymptotic half-line constant
`0.470795 + 4.04972/\log|t|` in place of the flat `0.611`, so the anchor improves as `t` grows.

### Summary of Proof
Proof: `interpolated_bound_1c` specialised at `T := t`; see the section note above.

### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_1c`.
**Used by:** none yet — the windowed form is what downstream callers currently consume. -/
theorem interpolated_bound_1c_pointwise {t σ : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7)) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < (4 * (1 - σ) / 9 - 1 / 18) * Real.log |t| + Real.log (Real.log |t|)
        + 14 / 3 * (5 / 7 - σ) * Real.log (0.470795 + 4.04972 / Real.log |t|)
        + 14 / 3 * (σ - 1 / 2) * Real.log 1.546 + 3 / t :=
  interpolated_bound_1c (T := t) (t := t) ht ⟨by linarith, by linarith⟩ hσ

/-- **Proposition `\ref{prop:interpolation}` (Proposition 35), case (2), pointwise form.**
The deeper-in-the-strip range `1 - k/(2^k-2) ≤ σ ≤ 1 - (k+1)/(2^{k+1}-2)` for `k ≥ 4`,
interpolating between consecutive instances of Yang's critical-strip bound. The hypothesis `k ≥ 4`
is Yang's own (see `ExternalFacts.yang_critical_strip_bound`), not an artifact.

### Summary of Proof
Proof: `interpolated_bound_2` specialised at `T := t`; see the section note above.

### References
tex: `\ref{prop:interpolation}`.

### Dependencies
**Depends on:** `interpolated_bound_2`.
**Used by:** none yet — the windowed form is what downstream callers currently consume. -/
theorem interpolated_bound_2_pointwise {t σ : ℝ} {k : ℕ} (hk : 4 ≤ k)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t)
    (hσ : σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2))) :
    Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < ((1 - σ) / (k - 1 + 2 ^ (1 - (k : ℤ) : ℤ) : ℝ) - 1 / (2 ^ k * (k - 1) + 2)) * Real.log |t|
        + Real.log (Real.log |t|) + Real.log 1.546 + 3 / t :=
  interpolated_bound_2 hk (T := t) (t := t) ht ⟨by linarith, by linarith⟩ hσ

/-- **The functional equation in log-norm form** — the reduction of
`Lemma \ref{lem:zetalessthanhalf}` (Lemma 36) to a statement with **no `ζ` on the right**.

For `t > 0` and `ζ(1-σ+it) ≠ 0`, writing `z := 1-σ-it`,

    log‖ζ(σ+it)‖ - log‖ζ(1-σ+it)‖
      = log 2 - (1-σ)·log(2π) + log‖Γ(z)‖ + log‖cos(πz/2)‖.

### Summary of Proof
Mathlib's `riemannZeta_one_sub` at `s = z` gives
`ζ(1-z) = 2·(2π)^{-z}·Γ(z)·cos(πz/2)·ζ(z)`, and `1-z = σ+it`. Its two hypotheses hold because
`Im z = -t ≠ 0`, so `z` is neither `1` nor a non-positive integer.

Taking norms and using `riemannZeta_conj` — `ζ(z) = ζ(conj(1-σ+it)) = conj(ζ(1-σ+it))`, of equal
norm — turns the `ζ(z)` factor into the `ζ(1-σ+it)` we want. Each remaining factor is nonzero
(`Γ` never vanishes; `cos(πz/2)` cannot, since `cos` vanishes only at real points and `Im z ≠ 0`),
so `Real.log` distributes over the product. `‖(2π)^{-z}‖ = (2π)^{-(1-σ)}` since the base is a
positive real.

### Lean Notes
**This is the useful half of `zetalessthanhalf_upper`, and it is unconditional in `σ`.** What
remains after it is a purely `Γ`-and-`cos` estimate — no `ζ` — which is where the real analytic
work lives; `gamma_cos_estimate_general` and its corollaries do that part.

The `hne` hypothesis is not a technicality: without it the target statement implies RH. See
`zetalessthanhalf_upper`'s Lean Notes.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), the functional-equation step of its proof.
External: Mathlib's `riemannZeta_one_sub` and `riemannZeta_conj`.

### Dependencies
**Depends on:** none.
**Used by:** `zetalessthanhalf_upper`, `zetalessthanhalf_lower`, `zetalessthanhalf_upper_tight`,
`zetalessthanhalf_lower_tight`, `zetalessthanhalf_upper_collapsed`,
`zetalessthanhalf_lower_collapsed`. -/
theorem log_norm_zeta_functional_eq {σ t : ℝ} (ht : 0 < t)
    (hne : riemannZeta ((1 - σ : ℝ) + t * Complex.I) ≠ 0) :
    Real.log ‖riemannZeta ((σ : ℝ) + t * Complex.I)‖
        - Real.log ‖riemannZeta ((1 - σ : ℝ) + t * Complex.I)‖
      = Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖ := by
  set z : ℂ := ((1 - σ : ℝ) : ℂ) - (t : ℂ) * Complex.I with hz
  have hzim : z.im = -t := by simp [hz]
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at hzim; simp at hzim; linarith
  have hzneg : ∀ n : ℕ, z ≠ -n := by
    intro n h; rw [h] at hzim; simp at hzim; linarith
  have hone : ((1 : ℂ) - z) = ((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by rw [hz]; push_cast; ring
  have hfe := riemannZeta_one_sub hzneg hzne1
  rw [hone] at hfe
  -- `ζ(z) = conj (ζ(1-σ+it))`, hence of the same norm
  have hconj : riemannZeta z
      = (starRingEnd ℂ) (riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [← riemannZeta_conj]
    congr 1
    rw [hz]
    simp [Complex.ext_iff]
  have hznorm : ‖riemannZeta z‖ = ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [hconj, RCLike.norm_conj]
  -- every factor is nonzero
  have hGne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (fun n h => hzneg n h)
  -- `cos` vanishes only at real points, and `Im z = -t ≠ 0`
  have hcosne : Complex.cos (↑Real.pi * z / 2) ≠ 0 := by
    intro h
    rw [Complex.cos_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have him : (↑Real.pi * z / 2).im = Real.pi * (-t) / 2 := by
      simp [Complex.mul_im, hzim]
    rw [hk] at him
    simp at him
    nlinarith [Real.pi_pos, him]
  have hcpowne : ((2 * (Real.pi : ℂ)) ^ (-z)) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    have : (0:ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt this)
  have hzetazne : riemannZeta z ≠ 0 := by rw [hconj]; simpa using hne
  -- norms of the product
  have hnorm : ‖riemannZeta (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      = 2 * ‖((2 * (Real.pi : ℂ)) ^ (-z))‖ * ‖Complex.Gamma z‖
        * ‖Complex.cos (↑Real.pi * z / 2)‖ * ‖riemannZeta z‖ := by
    rw [hfe]; simp
  have hbase : ‖((2 * (Real.pi : ℂ)) ^ (-z))‖ = (2 * Real.pi) ^ (-(1 - σ)) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp [hz]
  rw [hnorm, hbase, hznorm]
  rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hne),
    Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hcosne),
    Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hGne),
    Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow (by positivity)]
  ring

/-- **`‖cos(a - bi)‖² = cosh²b - sin²a` exactly**, for real `a`, `b`.

### Summary of Proof
`Complex.cos_add_mul_I` at `y = -b` gives `cos(a-bi) = cos a·cosh b + i·sin a·sinh b`, using
that `cosh` is even and `sinh` odd. So
`‖·‖² = cos²a·cosh²b + sin²a·sinh²b = cos²a·cosh²b + sin²a(cosh²b - 1) = cosh²b - sin²a`,
the last step by `cos² + sin² = 1` and `cosh² - sinh² = 1`.

### Lean Notes
Exact, with no error term — this is what makes the `cos` half of
`Lemma \ref{lem:zetalessthanhalf}` (Lemma 36) cheap: the only asymptotics needed afterwards is
`(1/2)log(cosh²(πt/2) - sin²a) = πt/2 - log 2 + O(e^{-πt})`, and `e^{-πt}` is negligible against
any `1/t^k` budget for `t > 10`.

Verified numerically to machine precision in `Code/verify_zetalessthanhalf_lower.py`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), the `cos(πz/2)` factor of its functional-equation
step.

### Dependencies
**Depends on:** none.
**Used by:** `log_norm_cos_estimate`. -/
theorem norm_cos_sub_mul_I_sq (a b : ℝ) :
    ‖Complex.cos ((a : ℂ) - (b : ℂ) * Complex.I)‖ ^ 2
      = Real.cosh b ^ 2 - Real.sin a ^ 2 := by
  have hrw : ((a : ℂ) - (b : ℂ) * Complex.I) = (a : ℂ) + ((-b : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrw, Complex.cos_add_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, zero_sub, add_zero]
  have hcosh : Real.cosh (-b) = Real.cosh b := Real.cosh_neg b
  have hsinh : Real.sinh (-b) = -Real.sinh b := Real.sinh_neg b
  rw [hcosh, hsinh]
  have hpyth : Real.cos a ^ 2 + Real.sin a ^ 2 = 1 := Real.cos_sq_add_sin_sq a
  have hhyp : Real.cosh b ^ 2 - Real.sinh b ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq b
  nlinarith [hpyth, hhyp]

/-- `D(σ) := σ(2σ-1)(1-σ)/12`, the exact `1/t²` coefficient of `Lemma \ref{lem:zetalessthanhalf}`
(Lemma 36), isolated in `gamma_cos_estimate_general`; `|D(σ)| ≤ √3/216` on `[0,1/2]` and
`|D(σ)| ≤ 1/2` on `[-1,0]` (`abs_Dcoeff_le_sqrt_three_div`, `abs_Dcoeff_le_half`).

### Summary of Proof
A definition, not a theorem. `D(σ)` is the exact coefficient of `1/t²` in the Stirling expansion
behind `zetalessthanhalf_upper_tight`/`_lower_tight`, kept in closed form so that the tight
statements leave only `O^*(0.06/t³)` resp. `O^*(1.4/t³)` tails rather than folding this term into
the error. In terms of `x = 1-σ` it is `(x-1/2)x²/2 - x³/3 + x/12`.

It is a *single* polynomial valid on **both** `σ`-ranges — the derivation in
`gamma_cos_estimate_general` never uses the sign of `σ` — which is why `Dcoeff2` is an
abbreviation for it rather than a separate cubic.

The test that pins it down is whether `residual · t³` stays bounded as `t` grows. With this `D`
it does, and shrinks: worst `1.2·10⁻⁵` on `[0,1/2]` and `2.5·10⁻³` on `[-1,0]` over
`t ∈ {10², 10³, 10⁴}` (`Code/verify_Dcoeff_corrected.py`). A wrong `1/t²` coefficient shows up
at once, the residual growing *linearly* in `t` instead.

Sharp bounds for `D`, both attained and both proved (`abs_Dcoeff_le_sqrt_three_div`,
`abs_Dcoeff_le_half`): `|D| ≤ √3/216 = 0.0080187538` on `[0,1/2]`, at the stationary point
`σ = (3-√3)/6`; and `|D| ≤ 1/2` on `[-1,0]`, at the endpoint `σ = -1`. The tex's Lemma 36
displays exactly these two constants.

### References
No tex counterpart for `D` itself — the tex states only the collapsed
`O^*((√3/216 + 0.17/t)/t²)` and `O^*((1/2 + 1.4/t)/t²)` forms, in `\ref{lem:zetalessthanhalf}`
(Lemma 36). The `1/t³` tail proved here is the sharper `0.06` in place of that `0.17`
(`gamma_cos_estimate_upper_tight`); see `Code/indep_mpmath_lemma35_constants.py`, Part B.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py` confirms `t²·residual → Dcoeff σ` as `t → ∞` at
`σ ∈ {0.1, 0.3, 0.5, -0.4, -1}` (to `10⁻⁴` at `t = 10⁶`), independently of
`verify_Dcoeff_corrected.py`.

### Dependencies
**Depends on:** none.
**Used by:** `gamma_cos_estimate_general`, `abs_Dcoeff_le_half`, `abs_Dcoeff_le_sqrt_three_div`,
`zetalessthanhalf_upper_tight`, `Dcoeff2`. -/
noncomputable def Dcoeff (σ : ℝ) : ℝ := σ * (2 * σ - 1) * (1 - σ) / 12

/-- `D₂ := D`. A separate name, kept only so that `zetalessthanhalf_lower_tight` can be stated in
the shape its `-1 ≤ σ ≤ 0` range suggests; it is the same polynomial.

### Summary of Proof
A definition, not a theorem. The `1/t²` coefficient is `σ(2σ-1)(1-σ)/12` on both `σ`-ranges,
because the Stirling derivation in `gamma_cos_estimate_general` is sign-agnostic in `σ`; no
separate cubic for `-1 ≤ σ ≤ 0` is needed. See `Dcoeff` above for the numerical evidence.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Dcoeff`.
**Used by:** `zetalessthanhalf_lower_tight`. -/
noncomputable def Dcoeff2 (σ : ℝ) : ℝ := Dcoeff σ

/-- **`arg z = π/2 - arctan(Re z / Im z)` on the open upper half plane.**

### Summary of Proof
Write `θ = π/2 - arctan(Re z / Im z)`. Since `arctan` lands in `(-π/2, π/2)`, `θ ∈ (0, π) ⊆
(-π, π]`, the principal range. Then `cos θ = sin(arctan u) = u/√(1+u²)` and
`sin θ = cos(arctan u) = 1/√(1+u²)` with `u = Re z / Im z`, and `√(1+u²) = ‖z‖/Im z` because
`Im z > 0`; so `‖z‖·cos θ = Re z` and `‖z‖·sin θ = Im z`, i.e. `z = ‖z‖(cos θ + i sin θ)`.
`Complex.arg_mul_cos_add_sin_mul_I` then reads off `arg z = θ`.

### Lean Notes
Mathlib defines `Complex.arg` by a three-way case split through `arcsin`, and has no
`arctan`-form lemma; this supplies one, uniformly in the sign of `Re z`, which is what the
application needs (`Re z = δ/2` changes sign as `δ` runs over `[-1/2, 1]`).

### References
No tex counterpart — Lean bookkeeping.

### Dependencies
**Depends on:** none.
**Used by:** `arg_sub_mul_I_eq`, `argGamma_im_diff`. -/
theorem arg_eq_pi_div_two_sub_arctan {z : ℂ} (hz : 0 < z.im) :
    Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have him : z.im ≠ 0 := ne_of_gt hz
  have hnorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hnorm' : ‖z‖ ≠ 0 := ne_of_gt hnorm
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hmem : Real.pi / 2 - Real.arctan (z.re / z.im) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two (z.re / z.im)
    have h2 := Real.neg_pi_div_two_lt_arctan (z.re / z.im)
    have hpi := Real.pi_pos
    exact ⟨by linarith, by linarith⟩
  have hsqrt : Real.sqrt (1 + (z.re / z.im) ^ 2) = ‖z‖ / z.im := by
    have hkey : (1 : ℝ) + (z.re / z.im) ^ 2 = (‖z‖ / z.im) ^ 2 := by
      rw [div_pow, div_pow, hn2]; field_simp; ring
    rw [hkey, Real.sqrt_sq (by positivity)]
  have hcos : Real.cos (Real.pi / 2 - Real.arctan (z.re / z.im)) = z.re / ‖z‖ := by
    rw [Real.cos_pi_div_two_sub, Real.sin_arctan, hsqrt]
    field_simp
  have hsin : Real.sin (Real.pi / 2 - Real.arctan (z.re / z.im)) = z.im / ‖z‖ := by
    rw [Real.sin_pi_div_two_sub, Real.cos_arctan, hsqrt]
    field_simp
  have key : z = (‖z‖ : ℂ)
      * (Complex.cos ((Real.pi / 2 - Real.arctan (z.re / z.im) : ℝ) : ℂ)
        + Complex.sin ((Real.pi / 2 - Real.arctan (z.re / z.im) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
    apply Complex.ext
    · simp [Complex.mul_re]; field_simp
    · simp [Complex.mul_im]; field_simp
  conv_lhs => rw [key]
  rw [Complex.arg_mul_cos_add_sin_mul_I hnorm hmem]

/-! ### The Stirling estimate behind Lemma 36

`Lemma \ref{lem:zetalessthanhalf}` (Lemma 36) reduces, through `log_norm_zeta_functional_eq`, to
a bound on the `ζ`-free quantity

    E(σ,t) := log 2 - (1-σ)log(2π) + log‖Γ(1-σ-it)‖ + log‖cos(π(1-σ-it)/2)‖
              - ((1/2-σ)log|t/2| + (σ-1/2)log|π|).

The lemmas of this section establish `E(σ,t) = Dcoeff σ / t² + O(1/t³)` with explicit constants,
for `-1 ≤ σ ≤ 1/2` and `t > 10`, by applying Brent's Stirling expansion once, at `z = 1-σ-it`
(`|z| ≥ t`), together with the elementary expansions of `log‖cos‖`, `arctan` and `log(1+u)`.
The exact `1/t²` coefficient comes out as `Dcoeff σ = σ(2σ-1)(1-σ)/12` (the `(x-1/2)x²/2 - x³/3
+ x/12` of `x = 1-σ`), and the `1/t³` remainder is controlled by Brent's bound
`(1+√(2π))/(360|z|³)` plus Taylor remainders of size `O(1/t⁴)`.  The numbers are checked
independently in `Code/indep_mpmath_lemma35_constants.py`. -/

/-- **Two-sided Taylor bound for `arctan`**: `0 ≤ arctan y - y + y³/3 ≤ y⁵/5` for `y ≥ 0`.

### Summary of Proof
`y ↦ arctan y - y + y³/3` has derivative `y⁴/(1+y²) ≥ 0`, and `y ↦ arctan y - y + y³/3 - y⁵/5`
has derivative `-y⁶/(1+y²) ≤ 0`; both vanish at `0`, so the first is `≥ 0` and the second `≤ 0` on
`[0,∞)` (`monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`).

### References
No tex counterpart — an elementary calculus fact ("several applications of Taylor's Theorem").

### Dependencies
**Depends on:** none.
**Used by:** `abs_arctan_sub_self_add_cube_le`, `gamma_cos_estimate_general`. -/
theorem arctan_sub_self_add_cube_bounds {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ Real.arctan y - y + y ^ 3 / 3 ∧ Real.arctan y - y + y ^ 3 / 3 ≤ y ^ 5 / 5 := by
  have hg : MonotoneOn (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((Real.continuous_arctan.sub continuous_id).add (by fun_prop)).continuousOn
    · intro z _
      exact (((Real.differentiable_arctan z).sub differentiableAt_id).add
        (by fun_prop)).differentiableWithinAt
    · intro z _
      have h1 := Real.hasDerivAt_arctan z
      have h2 : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (z ^ 2) z := by
        have := (hasDerivAt_pow 3 z).div_const 3
        have e : ((3 : ℕ) : ℝ) * z ^ (3 - 1) / 3 = z ^ 2 := by norm_num
        rw [e] at this
        exact this
      have hd : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
          (1 / (1 + z ^ 2) - 1 + z ^ 2) z := (h1.sub h2).add h3
      rw [hd.deriv]
      have hpos : (0:ℝ) < 1 + z ^ 2 := by positivity
      have : (1 - z ^ 2) ≤ 1 / (1 + z ^ 2) := by
        rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (z ^ 2)]
      linarith
  have hh : AntitoneOn (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3 - y ^ 5 / 5) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (((Real.continuous_arctan.sub continuous_id).add (by fun_prop)).sub
        (by fun_prop)).continuousOn
    · intro z _
      exact ((((Real.differentiable_arctan z).sub differentiableAt_id).add
        (by fun_prop)).sub (by fun_prop)).differentiableWithinAt
    · intro z _
      have h1 := Real.hasDerivAt_arctan z
      have h2 : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (z ^ 2) z := by
        have := (hasDerivAt_pow 3 z).div_const 3
        have e : ((3 : ℕ) : ℝ) * z ^ (3 - 1) / 3 = z ^ 2 := by norm_num
        rw [e] at this
        exact this
      have h4 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (z ^ 4) z := by
        have := (hasDerivAt_pow 5 z).div_const 5
        have e : ((5 : ℕ) : ℝ) * z ^ (5 - 1) / 5 = z ^ 4 := by norm_num
        rw [e] at this
        exact this
      have hd : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3 - y ^ 5 / 5)
          (1 / (1 + z ^ 2) - 1 + z ^ 2 - z ^ 4) z := ((h1.sub h2).add h3).sub h4
      rw [hd.deriv]
      have hpos : (0:ℝ) < 1 + z ^ 2 := by positivity
      have : 1 / (1 + z ^ 2) ≤ 1 - z ^ 2 + z ^ 4 := by
        rw [div_le_iff₀ hpos]; nlinarith [pow_nonneg (sq_nonneg z) 3]
      linarith
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hy' : y ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hy
  have hg0 := hg h0 hy' hy
  have hh0 := hh h0 hy' hy
  simp only [Real.arctan_zero] at hg0 hh0
  constructor <;> linarith

/-- **`|arctan y - y + y³/3| ≤ |y|⁵/5` for every real `y`.**

### Summary of Proof
`arctan_sub_self_add_cube_bounds` for `y ≥ 0`, and oddness of `arctan y - y + y³/3` for `y < 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `arctan_sub_self_add_cube_bounds`.
**Used by:** `argGamma_taylor_residue_sharp`. -/
theorem abs_arctan_sub_self_add_cube_le (y : ℝ) :
    |Real.arctan y - y + y ^ 3 / 3| ≤ |y| ^ 5 / 5 := by
  rcases le_or_gt 0 y with hy | hy
  · obtain ⟨h1, h2⟩ := arctan_sub_self_add_cube_bounds hy
    rw [abs_of_nonneg hy, abs_of_nonneg h1]; exact h2
  · obtain ⟨h1, h2⟩ := arctan_sub_self_add_cube_bounds (by linarith : 0 ≤ -y)
    rw [Real.arctan_neg] at h1 h2
    rw [abs_of_neg hy, abs_le]
    constructor <;> nlinarith

/-- **Second-order Taylor bound for `log`**: `u - u²/2 ≤ log(1+u) ≤ u` for `u ≥ 0`.

### Summary of Proof
The upper bound is `Real.log_le_sub_one_of_pos`; for the lower bound,
`u ↦ log(1+u) - u + u²/2` has derivative `u²/(1+u) ≥ 0` and vanishes at `0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_one_add_third_order`, `gamma_cos_estimate_general`. -/
theorem log_one_add_bounds {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  refine ⟨?_, by have := Real.log_le_sub_one_of_pos h1u; linarith⟩
  have hg : MonotoneOn (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.add
      · apply ContinuousOn.sub
        · apply ContinuousOn.log (by fun_prop)
          intro v hv; simp only [Set.mem_Ici] at hv; linarith
        · exact continuousOn_id
      · exact (by fun_prop : Continuous fun u : ℝ => u ^ 2 / 2).continuousOn
    · intro v hv
      rw [interior_Ici] at hv
      have hv0 : (0:ℝ) < 1 + v := by simp only [Set.mem_Ioi] at hv; linarith
      exact (((Real.differentiableAt_log hv0.ne').comp v
        ((differentiableAt_const _).add differentiableAt_id)).sub differentiableAt_id).add
        (by fun_prop) |>.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      have hv0 : (0:ℝ) < 1 + v := by simp only [Set.mem_Ioi] at hv; linarith
      have hd : HasDerivAt (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2)
          (1 / (1 + v) - 1 + v) v := by
        have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + v)) v := by
          have := ((hasDerivAt_id v).const_add 1).log hv0.ne'
          simpa using this
        have h2 : HasDerivAt (fun u : ℝ => u) 1 v := hasDerivAt_id v
        have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) v v := by
          have := (hasDerivAt_pow 2 v).div_const 2
          have e : ((2 : ℕ) : ℝ) * v ^ (2 - 1) / 2 = v := by norm_num
          rw [e] at this
          exact this
        exact (h1.sub h2).add h3
      rw [hd.deriv]
      have : 1 - v ≤ 1 / (1 + v) := by
        rw [le_div_iff₀ hv0]; nlinarith [sq_nonneg v]
      linarith
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hu' : u ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hu
  have := hg h0 hu' hu
  simp only [add_zero, Real.log_one] at this
  linarith

/-- **Third-order Taylor bound for `log`**: `0 ≤ log(1+u) - u + u²/2 ≤ u³/3` for `u ≥ 0`.

### Summary of Proof
The lower bound is `log_one_add_bounds`; `u ↦ log(1+u) - u + u²/2 - u³/3` has derivative
`-u³/(1+u) ≤ 0` and vanishes at `0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `log_one_add_bounds`.
**Used by:** `argGamma_taylor_residue_sharp`. -/
theorem log_one_add_third_order {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.log (1 + u) - u + u ^ 2 / 2 ∧ Real.log (1 + u) - u + u ^ 2 / 2 ≤ u ^ 3 / 3 := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hlo : u - u ^ 2 / 2 ≤ Real.log (1 + u) := (log_one_add_bounds hu).1
  refine ⟨by linarith, ?_⟩
  have hh : AntitoneOn (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2 - u ^ 3 / 3) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · apply ContinuousOn.sub
          · apply ContinuousOn.log (by fun_prop)
            intro v hv; simp only [Set.mem_Ici] at hv; linarith
          · exact continuousOn_id
        · exact (by fun_prop : Continuous fun u : ℝ => u ^ 2 / 2).continuousOn
      · exact (by fun_prop : Continuous fun u : ℝ => u ^ 3 / 3).continuousOn
    · intro v hv
      rw [interior_Ici] at hv
      have hv0 : (0:ℝ) < 1 + v := by simp only [Set.mem_Ioi] at hv; linarith
      exact ((((Real.differentiableAt_log hv0.ne').comp v
        ((differentiableAt_const _).add differentiableAt_id)).sub differentiableAt_id).add
        (by fun_prop)).sub (by fun_prop) |>.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      have hv0 : (0:ℝ) < 1 + v := by simp only [Set.mem_Ioi] at hv; linarith
      have hd : HasDerivAt (fun u : ℝ => Real.log (1 + u) - u + u ^ 2 / 2 - u ^ 3 / 3)
          (1 / (1 + v) - 1 + v - v ^ 2) v := by
        have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + v)) v := by
          have := ((hasDerivAt_id v).const_add 1).log hv0.ne'
          simpa using this
        have h2 : HasDerivAt (fun u : ℝ => u) 1 v := hasDerivAt_id v
        have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) v v := by
          have := (hasDerivAt_pow 2 v).div_const 2
          have e : ((2 : ℕ) : ℝ) * v ^ (2 - 1) / 2 = v := by norm_num
          rw [e] at this
          exact this
        have h4 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (v ^ 2) v := by
          have := (hasDerivAt_pow 3 v).div_const 3
          have e : ((3 : ℕ) : ℝ) * v ^ (3 - 1) / 3 = v ^ 2 := by norm_num
          rw [e] at this
          exact this
        exact ((h1.sub h2).add h3).sub h4
      rw [hd.deriv]
      have hvpos : (0:ℝ) < v := hv
      have : 1 / (1 + v) ≤ 1 - v + v ^ 2 := by
        rw [div_le_iff₀ hv0]; nlinarith [pow_nonneg hvpos.le 3]
      linarith
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hu' : u ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hu
  have := hh h0 hu' hu
  simp only [add_zero, Real.log_one] at this
  linarith

/-- **`log‖Γ z‖ = Re (logGammaAnalytic z)` for `Re z > 0`.**

### Summary of Proof
`ExternalFacts.exp_logGammaAnalytic` gives `exp (logGammaAnalytic z) = Γ z` on the slit plane
(which contains `Re z > 0`); take norms (`Complex.norm_exp`) and logarithms.

### References
No tex counterpart — the tex writes `log|Γ|` for the real part of Brent's `ln Γ`.

### Dependencies
**Depends on:** `ExternalFacts.exp_logGammaAnalytic`, `logGammaAnalytic`.
**Used by:** `gamma_cos_estimate_general`. -/
theorem log_norm_Gamma_eq_re_logGammaAnalytic {z : ℂ} (hz : 0 < z.re) :
    Real.log ‖Complex.Gamma z‖ = (logGammaAnalytic z).re := by
  rw [← exp_logGammaAnalytic (Or.inl hz), Complex.norm_exp, Real.log_exp]

/-- **`arg (x - ti) = arctan(x/t) - π/2` for `x, t > 0`.**

### Summary of Proof
`x - ti = conj (x + ti)`, `Complex.arg_conj`, and `arg_eq_pi_div_two_sub_arctan` at `x + ti`
(whose argument lies in `(0, π/2)`, so is not `π`).

### References
No tex counterpart — the tex writes `log(a+it/2) = log(t/2) + log(i + 2a/t)` for the same fact.

### Dependencies
**Depends on:** `arg_eq_pi_div_two_sub_arctan`.
**Used by:** `gamma_cos_estimate_general`. -/
theorem arg_sub_mul_I_eq {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    Complex.arg ((x : ℂ) - t * Complex.I) = Real.arctan (x / t) - Real.pi / 2 := by
  have hw : ((x : ℂ) - t * Complex.I) = (starRingEnd ℂ) ((x : ℂ) + t * Complex.I) := by
    apply Complex.ext <;> simp
  have himw : (0 : ℝ) < ((x : ℂ) + t * Complex.I).im := by simpa using ht
  have hargw : Complex.arg ((x : ℂ) + t * Complex.I) = Real.pi / 2 - Real.arctan (x / t) := by
    rw [arg_eq_pi_div_two_sub_arctan himw]
    simp
  have hne : Complex.arg ((x : ℂ) + t * Complex.I) ≠ Real.pi := by
    rw [hargw]
    have h1 : 0 ≤ Real.arctan (x / t) := Real.arctan_nonneg.mpr (by positivity)
    have h2 := Real.pi_pos
    intro h
    linarith
  rw [hw, Complex.arg_conj]
  simp only [hne, ite_false]
  rw [hargw]
  ring

/-- **Real part of Brent's Stirling expansion**, for `Re z > 0`:
`Re lnΓ(z) = (Re z - 1/2)log‖z‖ - Im z·arg z - Re z + ½log(2π) + Re z/(12‖z‖²) + Re R₂(z)`.

### Summary of Proof
Take real parts in `ExternalFacts.brent_stirling_expansion`, using `Complex.log_re`/`log_im` for
`(z-1/2)log z`, `bernoulli_two` for `B₂/(2z) = 1/(12z)`, and `Complex.inv_re` for `Re(1/z)`.

### References
External: Brent, `\cite[Eq. (2.1)]{Brent2019}`. tex: the Stirling display in the proof of
`\ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `ExternalFacts.brent_stirling_expansion`, `logGammaAnalytic`,
`brent_stirling_remainder`.
**Used by:** `gamma_cos_estimate_general`. -/
theorem re_logGammaAnalytic_eq {z : ℂ} (hz : 0 < z.re) :
    (logGammaAnalytic z).re
      = (z.re - 1 / 2) * Real.log ‖z‖ - z.im * Complex.arg z - z.re
        + 1 / 2 * Real.log (2 * Real.pi) + z.re / (12 * (z.re ^ 2 + z.im ^ 2))
        + (brent_stirling_remainder z).re := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hns : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hpos : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  have hB : ((bernoulli 2 : ℚ) : ℂ) / (2 * z) = (1 / 12 : ℂ) * z⁻¹ := by
    rw [bernoulli_two]
    push_cast
    field_simp
    norm_num
  have e1 : ((z - 1 / 2) * Complex.log z).re
      = (z.re - 1 / 2) * Real.log ‖z‖ - z.im * Complex.arg z := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
    simp
  have e2 : ((1 : ℂ) / 2 * Complex.log (2 * (Real.pi : ℂ))).re
      = 1 / 2 * Real.log (2 * Real.pi) := by
    have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.mul_re, hcast, Complex.log_re, Complex.log_im,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.inv_im, Complex.im_ofNat,
      neg_zero, zero_div, mul_zero, sub_zero, mul_eq_mul_left_iff, inv_eq_zero,
      OfNat.ofNat_ne_zero, or_false]
    rw [abs_of_pos Real.pi_pos]
  have e3 : ((1 / 12 : ℂ) * z⁻¹).re = z.re / (12 * (z.re ^ 2 + z.im ^ 2)) := by
    rw [Complex.mul_re, Complex.inv_re, Complex.inv_im, hns]
    simp
    field_simp
  rw [brent_stirling_expansion hz, hB]
  simp only [Complex.add_re, Complex.sub_re]
  rw [e1, e2, e3]

/-- **`e^{-πt} ≤ 1/(300 t⁴)` for `t > 10`.**

### Summary of Proof
The degree-7 term of the exponential series: `e^{πt} ≥ (πt)⁷/5040 ≥ 3⁷t⁷/5040 ≥ 300 t⁴`
(`Real.sum_le_exp_of_nonneg`, `π > 3`, `t³ ≥ 1000`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_norm_cos_estimate`. -/
theorem exp_neg_pi_mul_le_of_ten_lt {t : ℝ} (ht : 10 < t) :
    Real.exp (-(Real.pi * t)) ≤ 1 / (300 * t ^ 4) := by
  have hπ3 := Real.pi_gt_three
  have ht0 : (0:ℝ) < t := by linarith
  have hx : (0:ℝ) ≤ Real.pi * t := by positivity
  have hsum := Real.sum_le_exp_of_nonneg hx 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  have h7 : (Real.pi * t) ^ 7 / 5040 ≤ Real.exp (Real.pi * t) := by
    nlinarith [pow_nonneg hx 2, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5,
      pow_nonneg hx 6]
  have hpi7 : (2187:ℝ) * t ^ 7 ≤ (Real.pi * t) ^ 7 := by
    have : (3:ℝ) ^ 7 ≤ Real.pi ^ 7 := pow_le_pow_left₀ (by norm_num) hπ3.le 7
    rw [mul_pow]; nlinarith [pow_pos ht0 7]
  have ht3 : (1000:ℝ) ≤ t ^ 3 := by nlinarith [sq_nonneg t, sq_nonneg (t - 10)]
  have ht7 : (1000:ℝ) * t ^ 4 ≤ t ^ 7 := by
    have : t ^ 7 = t ^ 3 * t ^ 4 := by ring
    rw [this]; nlinarith [pow_pos ht0 4]
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith [h7, hpi7, ht7, pow_pos ht0 4]

/-- **`|log(1+w)| ≤ 2|w|` for `|w| ≤ 1/2`.**

### Summary of Proof
`log(1+w) ≤ w` and `log(1+w) ≥ 1 - 1/(1+w) = w/(1+w) ≥ -2|w|` for `w ≥ -1/2`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_norm_cos_estimate`. -/
theorem abs_log_one_add_le_two_mul_abs {w : ℝ} (hw : |w| ≤ 1 / 2) :
    |Real.log (1 + w)| ≤ 2 * |w| := by
  have hwl := abs_le.mp hw
  have h1w : 0 < 1 + w := by linarith
  have hup : Real.log (1 + w) ≤ w := by
    have := Real.log_le_sub_one_of_pos h1w; linarith
  have hlo : 1 - (1 + w)⁻¹ ≤ Real.log (1 + w) := Real.one_sub_inv_le_log_of_pos h1w
  have hlo' : -(2 * |w|) ≤ 1 - (1 + w)⁻¹ := by
    rcases le_or_gt 0 w with hw0 | hw0
    · have : (1 + w)⁻¹ ≤ 1 := by rw [inv_le_one₀ h1w]; linarith
      have := abs_nonneg w
      linarith
    · rw [abs_of_neg hw0]
      have h1 : 1 - (1 + w)⁻¹ = w / (1 + w) := by
        rw [eq_div_iff h1w.ne', sub_mul, one_mul, inv_mul_cancel₀ h1w.ne']; ring
      rw [h1, le_div_iff₀ h1w]
      have hprod : 0 ≤ (-w) * (1 + 2 * w) :=
        mul_nonneg (neg_nonneg.mpr hw0.le) (by linarith [hwl.1])
      nlinarith [hprod]
  rw [abs_le]
  exact ⟨by linarith, by linarith [le_abs_self w]⟩

/-- **`cosh² b - sin² a = (1/(4E))(1 + w)`** with `E = e^{-2b}`, `w = 2E + E² - 4 sin²a·E`.

### Summary of Proof
Expand `cosh b = (e^b + e^{-b})/2` and clear denominators.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `log_norm_cos_estimate`. -/
theorem cosh_sq_sub_sin_sq_eq (a b : ℝ) :
    Real.cosh b ^ 2 - Real.sin a ^ 2
      = (1 / (4 * Real.exp (-(2 * b)))) *
        (1 + (2 * Real.exp (-(2 * b)) + Real.exp (-(2 * b)) ^ 2
          - 4 * Real.sin a ^ 2 * Real.exp (-(2 * b)))) := by
  have hE : 0 < Real.exp (-(2 * b)) := Real.exp_pos _
  have hexp2 : Real.exp b ^ 2 = Real.exp (2 * b) := by rw [← Real.exp_nat_mul]; norm_num
  have hexpneg2 : Real.exp (-b) ^ 2 = Real.exp (-(2 * b)) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hexpprod : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
  have hEinv : Real.exp (2 * b) = 1 / Real.exp (-(2 * b)) := by
    rw [Real.exp_neg]; field_simp
  rw [Real.cosh_eq]
  have : (Real.exp b + Real.exp (-b)) ^ 2 = Real.exp (2 * b) + 2 + Real.exp (-(2 * b)) := by
    rw [add_sq, hexp2, hexpneg2, mul_assoc, hexpprod]; ring
  rw [div_pow, this, hEinv]
  field_simp
  ring

/-- **`log‖cos(π(x - ti)/2)‖ = πt/2 - log 2 + O(e^{-πt})`**, with the error at most `1/(100t⁴)`
for `t > 10`.

### Summary of Proof
`‖cos(a - bi)‖² = cosh²b - sin²a` (`norm_cos_sub_mul_I_sq`) with `a = πx/2`, `b = πt/2`; write it
as `(e^{2b}/4)(1 + w)` with `|w| ≤ 3e^{-2b}` (`cosh_sq_sub_sin_sq_eq`), so
`log‖cos‖ = b - log 2 + ½log(1+w)` and `|½log(1+w)| ≤ |w| ≤ 3e^{-πt} ≤ 1/(100t⁴)`
(`exp_neg_pi_mul_le_of_ten_lt`).

### References
tex: the `cos` factor of the functional equation, handled tacitly in the proof of
`\ref{lem:zetalessthanhalf}` (Lemma 36).

### Dependencies
**Depends on:** `norm_cos_sub_mul_I_sq`, `cosh_sq_sub_sin_sq_eq`, `exp_neg_pi_mul_le_of_ten_lt`,
`abs_log_one_add_le_two_mul_abs`.
**Used by:** `gamma_cos_estimate_general`. -/
theorem log_norm_cos_estimate {x t : ℝ} (ht : 10 < t) :
    |Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
        - (Real.pi * t / 2 - Real.log 2)| ≤ 1 / (100 * t ^ 4) := by
  have hπ := Real.pi_pos
  have ht0 : (0:ℝ) < t := by linarith
  have ht4 : (10000:ℝ) ≤ t ^ 4 := by
    have ht2 : (100:ℝ) ≤ t ^ 2 := by nlinarith
    have := mul_le_mul ht2 ht2 (by norm_num) (by positivity)
    nlinarith [this]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.pi * x / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.pi * t / 2 := ⟨_, rfl⟩
  have hrw : Real.pi * ((x : ℂ) - t * Complex.I) / 2
      = ((a : ℝ) : ℂ) - ((b : ℝ) : ℂ) * Complex.I := by
    rw [ha, hb]; push_cast; ring
  have h2b : 2 * b = Real.pi * t := by rw [hb]; ring
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(2 * b)) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEsmall : E ≤ 1 / (300 * t ^ 4) := by rw [hE, h2b]; exact exp_neg_pi_mul_le_of_ten_lt ht
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 2 * E + E ^ 2 - 4 * Real.sin a ^ 2 * E := ⟨_, rfl⟩
  have hsq : ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖ ^ 2
      = (1 / (4 * E)) * (1 + w) := by
    rw [hrw, norm_cos_sub_mul_I_sq a b, cosh_sq_sub_sin_sq_eq a b, ← hE, ← hw]
  have hsin2 : Real.sin a ^ 2 ≤ 1 := Real.sin_sq_le_one a
  have hsin0 : 0 ≤ Real.sin a ^ 2 := sq_nonneg _
  have hE1 : E ≤ 1 := by
    have : (1:ℝ) / (300 * t ^ 4) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hwabs : |w| ≤ 3 * E := by
    rw [hw, abs_le]
    have hE2 : E ^ 2 ≤ E := by nlinarith
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hsin2 hEpos.le,
      mul_nonneg hsin0 hEpos.le]
  have h3E : 3 * E ≤ 3 * (1 / (300 * t ^ 4)) := by linarith
  have hhalf : (3:ℝ) * (1 / (300 * t ^ 4)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hwhalf : |w| ≤ 1 / 2 := by linarith
  have h1w : 0 < 1 + w := by have := abs_le.mp hwhalf; linarith
  have hCpos : 0 < (1 / (4 * E)) * (1 + w) := by positivity
  have hnorm_pos : 0 < ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖ := by
    rcases (norm_nonneg (Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2))).lt_or_eq
      with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at hsq
      linarith
  have hlogcos : Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
      = Real.log ((1 / (4 * E)) * (1 + w)) / 2 := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hlogC : Real.log ((1 / (4 * E)) * (1 + w)) = -Real.log (4 * E) + Real.log (1 + w) := by
    rw [Real.log_mul (by positivity) h1w.ne', one_div, Real.log_inv]
  have hlog4E : Real.log (4 * E) = 2 * Real.log 2 - 2 * b := by
    rw [Real.log_mul (by norm_num) hEpos.ne', hE, Real.log_exp]
    have : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; ring
  have hlog1w := abs_log_one_add_le_two_mul_abs hwhalf
  have hkey : Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
      - (Real.pi * t / 2 - Real.log 2) = Real.log (1 + w) / 2 := by
    rw [hlogcos, hlogC, hlog4E, ← h2b]; ring
  rw [hkey, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hfin : (3:ℝ) * (1 / (300 * t ^ 4)) ≤ 1 / (100 * t ^ 4) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos ht0 4]
  linarith

/-- **Brent's remainder at `z = x - ti`** (`x, t > 0`): `|Re R₂(z)| ≤ (1+√(2π))/(360 t³)`.

### Summary of Proof
`ExternalFacts.brent_stirling_remainder_bound` gives `‖R₂(z)‖ < ‖(1+√(2π))B₄/(12z³)‖ =
(1+√(2π))/(360‖z‖³)` (`B₄ = -1/30`), and `‖z‖ ≥ t`.

### References
External: Brent, `\cite{Brent2019}`, Corollary 2.2 at `k = 2`.

### Dependencies
**Depends on:** `ExternalFacts.brent_stirling_remainder_bound`, `brent_stirling_remainder`.
**Used by:** `gamma_cos_estimate_general`. -/
theorem brent_remainder_re_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    |(brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re|
      ≤ (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) := by
  have hzre : (((x : ℂ) - t * Complex.I)).re = x := by simp
  have hzim : (((x : ℂ) - t * Complex.I)).im = -t := by simp
  have hpos : 0 < (((x : ℂ) - t * Complex.I)).re := by rw [hzre]; exact hx
  have hR := brent_stirling_remainder_bound hpos
  have hnorm : ‖((x : ℂ) - t * Complex.I)‖ = Real.sqrt (x ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hzre, hzim]; ring_nf
  have hnormge : t ≤ ‖((x : ℂ) - t * Complex.I)‖ := by
    rw [hnorm]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hB4 : ((bernoulli 4 : ℚ) : ℂ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; push_cast; ring
  have hsqrt : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hcast : ((1 : ℂ) + (Real.sqrt (2 * Real.pi) : ℂ))
      = ((1 + Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast] at hR
  have hrhs : ‖((1 + Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((bernoulli 4 : ℚ) : ℂ)
      / (12 * ((x : ℂ) - t * Complex.I) ^ 3)‖
      = (1 + Real.sqrt (2 * Real.pi)) / (360 * ‖((x : ℂ) - t * Complex.I)‖ ^ 3) := by
    rw [hB4, norm_div, norm_mul, norm_mul, Complex.norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖(-1 / 30 : ℂ)‖ = 1 / 30 := by
      rw [norm_div, norm_neg, norm_one]; simp
    have h2 : ‖(12 : ℂ)‖ = 12 := by simp
    rw [h1, h2]
    ring
  have hle := (Complex.abs_re_le_norm _).trans hR.le
  rw [hrhs] at hle
  have hpow : t ^ 3 ≤ ‖((x : ℂ) - t * Complex.I)‖ ^ 3 := pow_le_pow_left₀ ht.le hnormge 3
  calc |(brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re|
      ≤ (1 + Real.sqrt (2 * Real.pi)) / (360 * ‖((x : ℂ) - t * Complex.I)‖ ^ 3) := hle
    _ ≤ (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith

set_option maxHeartbeats 300000 in
-- the `field_simp; ring` identity `key` (five transcendental atoms, cleared denominators) and the
-- closing `linarith` over eight hypotheses each exceed the default budget.
-- Measured: fails at 250000.
/-- **The Stirling estimate behind `Lemma \ref{lem:zetalessthanhalf}` (Lemma 36), with the exact
`1/t²` coefficient `Dcoeff σ` isolated.** For `-1 ≤ σ ≤ 1/2` and `t > 10`,
`|E(σ,t) - Dcoeff σ/t²| ≤ ((1/2-σ)(1-σ)⁴/4 + (1-σ)⁵/5 + (1-σ)³/12 + 1/100)/t⁴ + (1+√(2π))/(360t³)`.

### Summary of Proof
With `x = 1-σ`, `z = x - ti`: `log‖Γ z‖ = Re lnΓ(z)` (`log_norm_Gamma_eq_re_logGammaAnalytic`)
is expanded by `re_logGammaAnalytic_eq`, with `arg z = arctan(x/t) - π/2` (`arg_sub_mul_I_eq`) and
`log‖z‖ = log t + ½log(1+x²/t²)`; `log‖cos‖ = πt/2 - log 2 + O(1/(100t⁴))`
(`log_norm_cos_estimate`). All `log t`, `log 2`, `log π`, `πt/2` terms cancel exactly, leaving

    E = (x-½)·½log(1+u) + t·arctan(x/t) - x + x/(12(x²+t²)) + Re R₂ + (cos error),  u = x²/t²,

and the second-order Taylor bounds `|log(1+u) - u| ≤ u²/2`, `0 ≤ arctan y - y + y³/3 ≤ y⁵/5`
(`y = x/t`) together with `x/(12(x²+t²)) = x/(12t²) - x³/(12t²(x²+t²))` isolate
`((x-½)x²/2 - x³/3 + x/12)/t² = Dcoeff σ/t²` with the stated remainder;
`brent_remainder_re_bound` bounds `Re R₂`.

### Lean Notes
Stirling is applied once, to `Γ(1-σ-it)` (`|z| ≥ t`), following `log_norm_zeta_functional_eq`'s
asymmetric functional equation rather than the tex's two half-argument Gammas; this is why the
`1/t³` constants here are smaller than the tex's own route can give (its two remainders at
`|z| ≈ t/2` alone cost `16(1+√(2π))/(360t³) ≈ 0.156/t³`).

### References
tex: the proof of `\ref{lem:zetalessthanhalf}` (Lemma 36), whose displayed expansions this
follows; `Code/indep_mpmath_lemma35_constants.py` checks every formula and constant here to
40 digits.

### Dependencies
**Depends on:** `log_norm_Gamma_eq_re_logGammaAnalytic`, `re_logGammaAnalytic_eq`,
`arg_sub_mul_I_eq`, `log_norm_cos_estimate`, `log_one_add_bounds`,
`arctan_sub_self_add_cube_bounds`, `brent_remainder_re_bound`, `Dcoeff`.
**Used by:** `gamma_cos_estimate_upper_tight`, `gamma_cos_estimate_lower_tight`. -/
theorem gamma_cos_estimate_general {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) (1 / 2)) (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)
        - Dcoeff σ / t ^ 2|
      ≤ ((1 / 2 - σ) * (1 - σ) ^ 4 / 4 + (1 - σ) ^ 5 / 5 + (1 - σ) ^ 3 / 12 + 1 / 100) / t ^ 4
        + (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, σ = 1 - x := ⟨1 - σ, by ring⟩
  have hx1 : 1 / 2 ≤ x := by linarith
  have hx2 : x ≤ 2 := by linarith
  have hx0 : 0 < x := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hπ := Real.pi_pos
  have e1 : (1 - (1 - x) : ℝ) = x := by ring
  simp only [e1]
  have hzre : (((x : ℂ) - t * Complex.I)).re = x := by simp
  have hzim : (((x : ℂ) - t * Complex.I)).im = -t := by simp
  have hzpos : 0 < (((x : ℂ) - t * Complex.I)).re := by rw [hzre]; exact hx0
  have hnorm : ‖((x : ℂ) - t * Complex.I)‖ = Real.sqrt (x ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hzre, hzim]; ring_nf
  have hxt : 0 < x ^ 2 + t ^ 2 := by positivity
  have hlognorm : Real.log ‖((x : ℂ) - t * Complex.I)‖
      = Real.log t + Real.log (1 + x ^ 2 / t ^ 2) / 2 := by
    rw [hnorm, Real.log_sqrt hxt.le]
    have : x ^ 2 + t ^ 2 = t ^ 2 * (1 + x ^ 2 / t ^ 2) := by field_simp; ring
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hΓ : Real.log ‖Complex.Gamma ((x : ℂ) - t * Complex.I)‖
      = (x - 1 / 2) * (Real.log t + Real.log (1 + x ^ 2 / t ^ 2) / 2)
        + t * (Real.arctan (x / t) - Real.pi / 2) - x + 1 / 2 * Real.log (2 * Real.pi)
        + x / (12 * (x ^ 2 + t ^ 2))
        + (brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re := by
    rw [log_norm_Gamma_eq_re_logGammaAnalytic hzpos, re_logGammaAnalytic_eq hzpos, hzre, hzim,
      arg_sub_mul_I_eq hx0 ht0, hlognorm]
    ring
  have hcos := log_norm_cos_estimate (x := x) ht
  have hu0 : (0:ℝ) ≤ x ^ 2 / t ^ 2 := by positivity
  have hy0 : (0:ℝ) ≤ x / t := by positivity
  obtain ⟨hl1, hl2⟩ := log_one_add_bounds hu0
  obtain ⟨ha1, ha2⟩ := arctan_sub_self_add_cube_bounds hy0
  have hR := brent_remainder_re_bound hx0 ht0
  have hDc : Dcoeff (1 - x) = x ^ 3 / 6 - x ^ 2 / 4 + x / 12 := by
    unfold Dcoeff; ring
  have hlog2π : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hπ.ne'
  have hlogt2 : Real.log |t / 2| = Real.log t - Real.log 2 := by
    rw [abs_of_pos (by positivity), Real.log_div ht0.ne' (by norm_num)]
  have hlogπ : Real.log |Real.pi| = Real.log Real.pi := by rw [abs_of_pos hπ]
  have key : Real.log 2 - x * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((x : ℂ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
        - ((1 / 2 - (1 - x)) * Real.log |t / 2| + ((1 - x) - 1 / 2) * Real.log |Real.pi|)
        - Dcoeff (1 - x) / t ^ 2
      = (x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)
        + t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)
        - x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2))
        + (brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re
        + (Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
            - (Real.pi * t / 2 - Real.log 2)) := by
    rw [hΓ, hDc, hlog2π, hlogt2, hlogπ]
    field_simp
    ring
  rw [key]
  have hb1 : |(x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)|
      ≤ (x - 1 / 2) * x ^ 4 / (4 * t ^ 4) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (x - 1 / 2) / 2)]
    have habs : |Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2| ≤ (x ^ 2 / t ^ 2) ^ 2 / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hm := mul_le_mul_of_nonneg_left habs (by linarith : (0:ℝ) ≤ (x - 1 / 2) / 2)
    have e : (x - 1 / 2) / 2 * ((x ^ 2 / t ^ 2) ^ 2 / 2) = (x - 1 / 2) * x ^ 4 / (4 * t ^ 4) := by
      field_simp
      ring
    linarith
  have hb2 : |t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)| ≤ x ^ 5 / (5 * t ^ 4) := by
    rw [abs_of_nonneg (mul_nonneg ht0.le ha1)]
    have hm := mul_le_mul_of_nonneg_left ha2 ht0.le
    have e : t * ((x / t) ^ 5 / 5) = x ^ 5 / (5 * t ^ 4) := by
      field_simp
    linarith
  have hb3 : |x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2))| ≤ x ^ 3 / (12 * t ^ 4) := by
    have hpos1 : (0:ℝ) < 12 * t ^ 2 * (x ^ 2 + t ^ 2) := by positivity
    have hpos2 : (0:ℝ) < 12 * t ^ 4 := by positivity
    have hx3 : (0:ℝ) ≤ x ^ 3 := by positivity
    rw [abs_of_nonneg (div_nonneg hx3 hpos1.le), div_le_div_iff₀ hpos1 hpos2]
    have h12 : (12:ℝ) * t ^ 4 ≤ 12 * t ^ 2 * (x ^ 2 + t ^ 2) := by
      nlinarith [sq_nonneg x, sq_nonneg t]
    exact mul_le_mul_of_nonneg_left h12 hx3
  have htri : |(x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)
        + t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)
        - x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2))
        + (brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re
        + (Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
            - (Real.pi * t / 2 - Real.log 2))|
      ≤ |(x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)|
        + |t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)|
        + |x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2))|
        + |(brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re|
        + |Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
            - (Real.pi * t / 2 - Real.log 2)| := by
    have i1 := abs_add_le ((x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2))
      (t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3))
    have i2 := abs_sub ((x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)
        + t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3))
      (x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2)))
    have i3 := abs_add_le ((x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)
        + t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)
        - x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2)))
      ((brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re)
    have i4 := abs_add_le ((x - 1 / 2) / 2 * (Real.log (1 + x ^ 2 / t ^ 2) - x ^ 2 / t ^ 2)
        + t * (Real.arctan (x / t) - x / t + (x / t) ^ 3 / 3)
        - x ^ 3 / (12 * t ^ 2 * (x ^ 2 + t ^ 2))
        + (brent_stirling_remainder ((x : ℂ) - t * Complex.I)).re)
      (Real.log ‖Complex.cos (Real.pi * ((x : ℂ) - t * Complex.I) / 2)‖
            - (Real.pi * t / 2 - Real.log 2))
    linarith
  have hsum : (x - 1 / 2) * x ^ 4 / (4 * t ^ 4) + x ^ 5 / (5 * t ^ 4) + x ^ 3 / (12 * t ^ 4)
        + (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) + 1 / (100 * t ^ 4)
      = ((1 / 2 - (1 - x)) * x ^ 4 / 4 + x ^ 5 / 5 + x ^ 3 / 12 + 1 / 100) / t ^ 4
        + (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) := by
    field_simp
    ring
  linarith [htri, hb1, hb2, hb3, hR, hcos, hsum]

/-- **`√(2π) < 2.51`.**

### Summary of Proof
`2π < 6.3 < 2.51²` from `Real.pi_lt_d2`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `gamma_cos_estimate_upper_tight`, `gamma_cos_estimate_lower_tight`. -/
theorem sqrt_two_pi_lt : Real.sqrt (2 * Real.pi) < 2.51 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := Real.pi_lt_d2
  nlinarith

/-- **`|Dcoeff σ| ≤ 1/2` on `[-1, 0]`** (attained at `σ = -1`).

### Summary of Proof
`Dcoeff σ = (-σ)(1-2σ)(1-σ)/12 ≥ 0` there, and the three factors are at most `1, 3, 2`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), second case, the `1/2` of its `O^*` constant.

### Dependencies
**Depends on:** `Dcoeff`.
**Used by:** `gamma_cos_estimate_lower_collapsed`. -/
theorem abs_Dcoeff_le_half {σ : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) : |Dcoeff σ| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := hσ
  unfold Dcoeff
  have hnn : 0 ≤ σ * (2 * σ - 1) * (1 - σ) := by
    have : 0 ≤ (-σ) * (1 - 2 * σ) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  rw [abs_of_nonneg (by positivity)]
  have hb : σ * (2 * σ - 1) * (1 - σ) ≤ 6 := by
    have e : σ * (2 * σ - 1) * (1 - σ) = (-σ) * (1 - 2 * σ) * (1 - σ) := by ring
    rw [e]
    have h3 : (-σ) * (1 - 2 * σ) ≤ 3 := by nlinarith
    have h4 : 0 ≤ (-σ) * (1 - 2 * σ) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  linarith

/-- **`|Dcoeff σ| ≤ √3/216` on `[0, 1/2]`**, sharp (attained at `σ = (3-√3)/6`).

### Summary of Proof
`-Dcoeff σ = (2σ³ - 3σ² + σ)/12 ≥ 0` there, and the exact identity
`√3/18 - (2σ³-3σ²+σ) = 2(σ-r)²(s-σ) - (√3² - 3)(2√3 + 18σ - 9)/108` with `r = (3-√3)/6`,
`s = (3+2√3)/6` (a polynomial identity, `ring`) shows the left side is `≥ 0` for `σ ≤ s`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), first case, the `√3/216` of its `O^*` constant
(`Code/indep_mpmath_lemma35_constants.py`, Part B).

### Dependencies
**Depends on:** `Dcoeff`.
**Used by:** `gamma_cos_estimate_upper_collapsed`. -/
theorem abs_Dcoeff_le_sqrt_three_div {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |Dcoeff σ| ≤ Real.sqrt 3 / 216 := by
  obtain ⟨h1, h2⟩ := hσ
  have hq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hq2 : Real.sqrt 3 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq1 : 1 ≤ Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  unfold Dcoeff
  have hnp : σ * (2 * σ - 1) * (1 - σ) ≤ 0 := by
    have : 0 ≤ σ * (1 - 2 * σ) := mul_nonneg h1 (by linarith)
    nlinarith
  rw [abs_of_nonpos (by linarith)]
  have hs : 0 ≤ (3 + 2 * Real.sqrt 3) / 6 - σ := by linarith
  have hsos : 0 ≤ 2 * (σ - (3 - Real.sqrt 3) / 6) ^ 2 * ((3 + 2 * Real.sqrt 3) / 6 - σ) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hs
  have key : Real.sqrt 3 / 18 - (2 * σ ^ 3 - 3 * σ ^ 2 + σ)
      = 2 * (σ - (3 - Real.sqrt 3) / 6) ^ 2 * ((3 + 2 * Real.sqrt 3) / 6 - σ)
        - (Real.sqrt 3 ^ 2 - 3) * (2 * Real.sqrt 3 + 18 * σ - 9) / 108 := by ring
  rw [hq] at key
  have : 2 * σ ^ 3 - 3 * σ ^ 2 + σ ≤ Real.sqrt 3 / 18 := by nlinarith [key, hsos]
  nlinarith [this]

/-- **Lemma 36's `Γ`-and-`cos` estimate, tight form, first case**: for `0 ≤ σ ≤ 1/2`, `t > 10`,
`|E(σ,t) - Dcoeff σ/t²| ≤ 0.06/t³`.

### Summary of Proof
`gamma_cos_estimate_general` with `(1/2-σ)(1-σ)⁴/4 + (1-σ)⁵/5 + (1-σ)³/12 + 1/100 ≤ 0.42` on
`[0,1/2]`, `0.42/t⁴ ≤ 0.042/t³` for `t ≥ 10`, and `(1+√(2π))/360 < 0.00975`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), first case, whose own `1/t³` constant is the
weaker `0.17`; `0.06` is what this route gives.

### Dependencies
**Depends on:** `gamma_cos_estimate_general`, `sqrt_two_pi_lt`.
**Used by:** `gamma_cos_estimate_upper_collapsed`, `zetalessthanhalf_upper_tight`. -/
theorem gamma_cos_estimate_upper_tight {σ t : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)
        - Dcoeff σ / t ^ 2|
      ≤ 0.06 / t ^ 3 := by
  obtain ⟨h1, h2⟩ := hσ
  have ht0 : (0:ℝ) < t := by linarith
  have hgen := gamma_cos_estimate_general ⟨by linarith, h2⟩ ht
  have hsq := sqrt_two_pi_lt
  have hx : (1 - σ) ≤ 1 := by linarith
  have hx0 : 0 ≤ 1 - σ := by linarith
  have hnum : (1 / 2 - σ) * (1 - σ) ^ 4 / 4 + (1 - σ) ^ 5 / 5 + (1 - σ) ^ 3 / 12 + 1 / 100
      ≤ 0.42 := by
    have h4 : (1 - σ) ^ 4 ≤ 1 := pow_le_one₀ hx0 hx
    have h5 : (1 - σ) ^ 5 ≤ 1 := pow_le_one₀ hx0 hx
    have h3 : (1 - σ) ^ 3 ≤ 1 := pow_le_one₀ hx0 hx
    have h40 : 0 ≤ (1 - σ) ^ 4 := by positivity
    nlinarith
  have ht4 : (0:ℝ) < t ^ 4 := by positivity
  have hb1 : ((1 / 2 - σ) * (1 - σ) ^ 4 / 4 + (1 - σ) ^ 5 / 5 + (1 - σ) ^ 3 / 12 + 1 / 100)
      / t ^ 4 ≤ 0.42 / t ^ 4 := div_le_div_of_nonneg_right hnum ht4.le
  have hb2 : (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) ≤ (1 + 2.51) / (360 * t ^ 3) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hA : (0.42:ℝ) / t ^ 4 ≤ 0.042 / t ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (pow_pos ht0 3).le (by linarith : (0:ℝ) ≤ t - 10)]
  have hB : (1 + 2.51 : ℝ) / (360 * t ^ 3) = 0.00975 / t ^ 3 := by
    field_simp
    norm_num
  have hC : (0.042:ℝ) / t ^ 3 + 0.00975 / t ^ 3 ≤ 0.06 / t ^ 3 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **Lemma 36's `Γ`-and-`cos` estimate, tight form, second case**: for `-1 ≤ σ ≤ 0`, `t > 10`,
`|E(σ,t) - Dcoeff σ/t²| ≤ 1.4/t³`.

### Summary of Proof
`gamma_cos_estimate_general` with `(1/2-σ)(1-σ)⁴/4 + (1-σ)⁵/5 + (1-σ)³/12 + 1/100 ≤ 13.08` on
`[-1,0]`, `13.08/t⁴ ≤ 1.308/t³` for `t ≥ 10`, and `(1+√(2π))/360 < 0.00975`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), second case, the `1.4/t` of its `O^*` constant.

### Dependencies
**Depends on:** `gamma_cos_estimate_general`, `sqrt_two_pi_lt`.
**Used by:** `gamma_cos_estimate_lower_collapsed`, `zetalessthanhalf_lower_tight`. -/
theorem gamma_cos_estimate_lower_tight {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)
        - Dcoeff σ / t ^ 2|
      ≤ 1.4 / t ^ 3 := by
  obtain ⟨h1, h2⟩ := hσ
  have ht0 : (0:ℝ) < t := by linarith
  have hgen := gamma_cos_estimate_general ⟨h1, by linarith⟩ ht
  have hsq := sqrt_two_pi_lt
  have hx : (1 - σ) ≤ 2 := by linarith
  have hx0 : 0 ≤ 1 - σ := by linarith
  have hnum : (1 / 2 - σ) * (1 - σ) ^ 4 / 4 + (1 - σ) ^ 5 / 5 + (1 - σ) ^ 3 / 12 + 1 / 100
      ≤ 13.08 := by
    have h4 : (1 - σ) ^ 4 ≤ 16 := by
      have := pow_le_pow_left₀ hx0 hx 4; norm_num at this; linarith
    have h5 : (1 - σ) ^ 5 ≤ 32 := by
      have := pow_le_pow_left₀ hx0 hx 5; norm_num at this; linarith
    have h3 : (1 - σ) ^ 3 ≤ 8 := by
      have := pow_le_pow_left₀ hx0 hx 3; norm_num at this; linarith
    have h40 : 0 ≤ (1 - σ) ^ 4 := by positivity
    nlinarith
  have ht4 : (0:ℝ) < t ^ 4 := by positivity
  have hb1 : ((1 / 2 - σ) * (1 - σ) ^ 4 / 4 + (1 - σ) ^ 5 / 5 + (1 - σ) ^ 3 / 12 + 1 / 100)
      / t ^ 4 ≤ 13.08 / t ^ 4 := div_le_div_of_nonneg_right hnum ht4.le
  have hb2 : (1 + Real.sqrt (2 * Real.pi)) / (360 * t ^ 3) ≤ (1 + 2.51) / (360 * t ^ 3) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hA : (13.08:ℝ) / t ^ 4 ≤ 1.308 / t ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (pow_pos ht0 3).le (by linarith : (0:ℝ) ≤ t - 10)]
  have hB : (1 + 2.51 : ℝ) / (360 * t ^ 3) = 0.00975 / t ^ 3 := by
    field_simp
    norm_num
  have hC : (1.308:ℝ) / t ^ 3 + 0.00975 / t ^ 3 ≤ 1.4 / t ^ 3 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **Lemma 36's `Γ`-and-`cos` estimate in the tex's collapsed form, first case**: for
`0 ≤ σ ≤ 1/2`, `t > 10`, `|E(σ,t)| ≤ (√3/216 + 0.06/t)/t²`.

### Summary of Proof
`gamma_cos_estimate_upper_tight` and `abs_Dcoeff_le_sqrt_three_div`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), first case — the same collapsed shape, with the
sharper `0.06` in place of the tex's `0.17`.

### Dependencies
**Depends on:** `gamma_cos_estimate_upper_tight`, `abs_Dcoeff_le_sqrt_three_div`.
**Used by:** `zetalessthanhalf_upper`, `zetalessthanhalf_upper_collapsed`. -/
theorem gamma_cos_estimate_upper_collapsed {σ t : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have htight := gamma_cos_estimate_upper_tight hσ ht
  have hD := abs_Dcoeff_le_sqrt_three_div hσ
  have htri := abs_sub_abs_le_abs_sub
    (Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
      + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
      + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
      - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|))
    (Dcoeff σ / t ^ 2)
  have hD' : |Dcoeff σ / t ^ 2| ≤ Real.sqrt 3 / 216 / t ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos ht0 2)]
    exact div_le_div_of_nonneg_right hD (by positivity)
  have e2 : (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2
      = Real.sqrt 3 / 216 / t ^ 2 + 0.06 / t ^ 3 := by
    field_simp
  linarith

/-- **Lemma 36's `Γ`-and-`cos` estimate in the tex's collapsed form, second case**: for
`-1 ≤ σ ≤ 0`, `t > 10`, `|E(σ,t)| ≤ (1/2 + 1.4/t)/t²`.

### Summary of Proof
`gamma_cos_estimate_lower_tight` and `abs_Dcoeff_le_half`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), second case — the tex's own collapsed constant
`(1/2 + 1.4/t)/t²` exactly.

### Dependencies
**Depends on:** `gamma_cos_estimate_lower_tight`, `abs_Dcoeff_le_half`.
**Used by:** `gamma_cos_estimate_lower`, `zetalessthanhalf_lower_collapsed`. -/
theorem gamma_cos_estimate_lower_collapsed {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ (1 / 2 + 1.4 / t) / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have htight := gamma_cos_estimate_lower_tight hσ ht
  have hD := abs_Dcoeff_le_half hσ
  have htri := abs_sub_abs_le_abs_sub
    (Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
      + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
      + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
      - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|))
    (Dcoeff σ / t ^ 2)
  have hD' : |Dcoeff σ / t ^ 2| ≤ 1 / 2 / t ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos ht0 2)]
    exact div_le_div_of_nonneg_right hD (by positivity)
  have e : (1 / 2 + 1.4 / t) / t ^ 2 = 1 / 2 / t ^ 2 + 1.4 / t ^ 3 := by
    field_simp
  linarith

/-- **Lemma `\ref{lem:zetalessthanhalf}`**, first case: for `0 ≤ σ ≤ 1/2` and `t > 10`,
`log|ζ(σ+it)| = log|ζ(1-σ+it)| + (1/2-σ)log|t/2| + (σ-1/2)log|π| + O^*(1/(2t²))`, via the
functional equation `riemannZeta_one_sub` and Brent's Stirling expansion (`ExternalFacts`).

### Summary of Proof
**The tex's route.** Take real parts of the functional equation written as
`ζ(σ+it) = χ(σ+it)ζ(1-σ+it)`, then expand `log|Γ((σ+it)/2)| - log|Γ((1-σ+it)/2)|` by Brent's
Stirling expansion at the two half-arguments (needing the shift `Γ(z) = Γ(z+1)/z` when `σ < 0`).

**The route taken here** avoids the half-arguments and Legendre duplication. Mathlib's
`riemannZeta_one_sub` is stated with the *whole*-argument `Gamma`: for `z := 1-σ-it`
(`Re z = 1-σ > 0`), `ζ(σ+it) = 2(2π)^{-z}Γ(z)cos(πz/2)ζ(z)` and `‖ζ(z)‖ = ‖ζ(1-σ+it)‖` by
`riemannZeta_conj`, so (`log_norm_zeta_functional_eq`)
`log‖ζ(σ+it)‖ - log‖ζ(1-σ+it)‖ = log 2 - (1-σ)log(2π) + log‖Γ(z)‖ + log‖cos(πz/2)‖`.
The right side minus the target `(1/2-σ)log|t/2| + (σ-1/2)log π` is the `ζ`-free quantity `E(σ,t)`
of `gamma_cos_estimate_general`, expanded by one application of Brent's expansion at `z` together
with `‖cos(a-bi)‖² = cosh²b - sin²a`; `gamma_cos_estimate_upper_collapsed` gives
`|E| ≤ (√3/216 + 0.06/t)/t² ≤ 1/(2t²)`.

### Lean Notes
The `1/(2t²)` here is the weaker constant the downstream users need; the collapsed form
`(√3/216 + 0.06/t)/t²` — the tex's shape, with its `0.17` sharpened to `0.06` — is
`zetalessthanhalf_upper_collapsed`, and the split form with `Dcoeff σ/t²` explicit is
`zetalessthanhalf_upper_tight`.

**Why `hz`: without it the statement would imply the Riemann Hypothesis.** This is a
`Real.log 0 = 0` artifact, the same one `LogDerivZetaLaurent.logderzetabound` has to handle at
`x = 0`.

Suppose `ζ` had a zero at `ρ = (1-σ) + it` with `σ < 1/2`, i.e. `Re ρ > 1/2`. The functional
equation writes `ζ(σ+it) = χ · ζ(1-σ-it)` with `χ = 2(2π)^{-z}Γ(z)cos(πz/2)` never zero, and
`ζ(1-σ-it) = conj(ζ(1-σ+it)) = 0`, so `σ+it` is a zero too. **Both** log terms would then be
`Real.log 0 = 0`, and the claim would collapse to

    |(1/2-σ)·log(t/(2π))| ≤ 1/(2t²),

whose left side *grows* with `t` while the right side shrinks. At `σ = 0, t = 100` it asserts
`1.384 ≤ 5·10⁻⁵`. The residual
vanishes only at `σ = 1/2`, which is exactly where `1-σ = 1/2` puts the hypothetical zero back on
the critical line. So without `hz` the statement would assert that `ζ` has no zero with
`Re ∈ (1/2,1]` and `t > 10` — RH on that range.

**This is NOT a discrepancy with the tex.** The tex uses the simplifying convention
`log|0| = -∞` at these points, under which its statement is correct as written and needs no
hypothesis: at a zero the left side is `-∞`, and `-∞ ≤ anything` holds. Lean cannot follow that
convention — `Real.log 0 = 0`, a *finite* junk value — so the same sentence becomes false rather
than vacuous, and `hz` is what restores the tex's intent. Stating the tex's fact in a way that is
simultaneously faithful and clear in Lean would be awkward: it would mean carrying
`EReal`-valued logarithms through the whole development for the sake of a null set.

**Nothing is lost by assuming it.** Every place this bound is ultimately used in Lean feeds an
*integration* — the `zeta_chord_bound_*` family and `integral_tight_tail_lt_window` all integrate
`log‖ζ‖` over a segment — and `ζ`'s zeros on any such segment are isolated, hence a null set. A
hypothesis excluding isolated points therefore does not change any integral's value, so the
consumers can discharge it almost everywhere and lose nothing.

**The alternative, if the hypothesis is ever unwanted,** is to restate the bound for the
functional-equation factor `χ` itself, which has no zeros or poles in `0 < Re s < 1` and so needs
no hypothesis at all. That form is **true**: numerically `log‖χ‖` against the target
`(1/2-σ)log|t/2| + (σ-1/2)log π` differs by `2.7·10⁻⁵` at `t = 15` and `6·10⁻⁷` at `t = 100`,
comfortably inside the `1/(2t²)` budget (`2.2·10⁻³` and `5·10⁻⁵`; same script).
`log_norm_zeta_functional_eq` above is that reduction, already proved.

**Why the whole-argument route.** The tex's own route — expanding
`log|Γ((σ+it)/2)| - log|Γ((1-σ+it)/2)|` at half-arguments — would require reconstructing Legendre
duplication from scratch in Lean, which the route above avoids entirely; it also needs only one
Brent remainder at `|z| ≥ t` instead of two at `|z| ≈ t/2`, which is why the `1/t³` constants
proved here (`0.06`, `1.4`) are smaller than the tex's route could give.

### References
tex: `\ref{lem:zetalessthanhalf}`.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py`: the residual is recomputed two ways (directly from
`ζ` at both points, and `ζ`-free via `log|χ(s)|`, `χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s)`; they agree
to `3×10⁻³⁹`, confirming the signs of the `log|t/2|` and `log π` terms as transcribed here).
`sup |residual|·t² = 0.00801` over `σ ∈ [0,1/2]`, `t ≥ 10` (at `σ = 0.2`, `t = 10`) — the stated
`1/2` has a factor-60 margin. The true `t⁻²` coefficient is `Dcoeff σ`, with
`|Dcoeff| ≤ √3/216 = 0.00802` on `[0,1/2]`, so the margin here is essentially exhausted.

### Dependencies
**Depends on:** `log_norm_zeta_functional_eq`, `gamma_cos_estimate_upper_collapsed`.
**Used by:** `Jensen.JensenScaleConstants.zeta_chord_bound_neg`, `zeta_chord_bound_neg_tight`,
`zeta_chord_bound_neg_tight_simple`, and
`Jensen.JensenScaleConstantsAlt.zeta_piecewise_bound_alt`. -/
theorem zetalessthanhalf_upper {σ t : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) (ht : 10 < t)
    (hz : riemannZeta ((1 : ℂ) - σ + t * Complex.I) ≠ 0) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ 1 / (2 * t ^ 2) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hz
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hz
  have hgc := gamma_cos_estimate_upper_collapsed hσ ht
  have hsq3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h06 : (0.06:ℝ) / t ≤ 0.006 := by rw [div_le_iff₀ ht0]; linarith
  have hle : (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 ≤ 1 / (2 * t ^ 2) := by
    have hs : Real.sqrt 3 / 216 + 0.06 / t ≤ 1 / 2 := by linarith
    calc (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 ≤ (1 / 2) / t ^ 2 :=
          div_le_div_of_nonneg_right hs (by positivity)
      _ = 1 / (2 * t ^ 2) := by rw [div_div]
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)| := by
        congr 1; linarith [hfe]
    _ ≤ (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 := hgc
    _ ≤ 1 / (2 * t ^ 2) := hle

/-- **The `Γ`-and-`cos` estimate that `zetalessthanhalf_lower` reduces to** — the same claim with
**no `ζ` anywhere**. For `-1 ≤ σ ≤ 0`, `t > 10`, writing `z := (1-σ) - it`,

    |log 2 - (1-σ)log(2π) + log‖Γ(z)‖ + log‖cos(πz/2)‖
       - ((1/2-σ)log|t/2| + (σ-1/2)log|π|)|  ≤  4/t².

### Summary of Proof
Two expansions in `1/t`, which must be combined *before* bounding — see Lean Notes.

*The `cos` factor is exact.* `norm_cos_sub_mul_I_sq` gives
`‖cos(πz/2)‖² = cosh²(πt/2) - sin²(π(1-σ)/2)`, so
`log‖cos(πz/2)‖ = πt/2 - log 2 + (1/2)log(1 + (2-4sin²a)e^{-πt} + e^{-2πt})`, and for `t > 10`
that last term is below `e^{-31}`, negligible against any `1/t^k`.

*The `Γ` factor.* `ExternalFacts.brent_stirling_expansion` at `z` (legitimate since
`Re z = 1-σ ≥ 1 > 0`) plus `Complex.log_re` give, with `u := 1-σ ∈ [1,2]`,

    log‖Γ(z)‖ = (u-1/2)·½log(u²+t²) + t·arg z - u + ½log(2π) + Re[B₂/(2z)] + Re[R(z)],

with `arg z = -arctan(t/u)`. Using `arctan(t/u) = π/2 - arctan(u/t)` and the arctan series,
`t·arg z = -πt/2 + u - u³/(3t²) + O(1/t⁴)`, while
`(u-1/2)·½log(u²+t²) = (u-1/2)log t + (u-1/2)u²/(2t²) + O(1/t⁴)`.

Assembling, `log 2` and `πt/2` cancel and the main terms reproduce
`(u-1/2)log t - (u-1/2)log(2π)`, which is exactly the target
`(1/2-σ)log|t/2| + (σ-1/2)log|π|`. What survives is `D(σ)/t² + O(1/t⁴)` with

    D(σ) = (u-1/2)u²/2 - u³/3 + u/12 = σ(2σ-1)(1-σ)/12,

and `|D| ≤ 1/2` on `[-1,0]` (attained at `σ = -1`), comfortably inside `4/t²`.

### Lean Notes
Proved as a corollary of `gamma_cos_estimate_lower_collapsed`, whose
`(1/2 + 1.4/t)/t²` is below `4/t²` for `t > 10`. The expansion sketched above is carried out, with
explicit remainders, in `gamma_cos_estimate_general`; the point that made it non-routine is that
the two `1/t²` contributions must be combined *before* bounding. At the worst point `u = 2`
(`σ = -1`) they are `(u-1/2)u²/2 = 3` and `-u³/3 = -8/3 ≈ -2.667`, whose *sum* with `u/12` is
`D = 1/2`, but bounded apart they would contribute `3 + 2.667 = 5.67 > 4`. The general lemma
therefore isolates the exact coefficient `Dcoeff σ` (a single `field_simp; ring` identity) and
bounds only the Taylor and Brent remainders.

Numerics confirming every step, including that `4/t²` holds with worst ratio `0.125` on the
stated range: `Code/verify_zetalessthanhalf_lower.py`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), second case.
External: Brent's Stirling expansion via `ExternalFacts.brent_stirling_expansion`.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py`: `sup |E|·t² = 0.5` over `σ ∈ [-1,0]`, `t ≥ 10`
(approached at `σ = -1`, `t → ∞`, where `E ~ Dcoeff(-1)/t² = 1/(2t²)`), against the stated `4`;
and `E` coincides with the `zetalessthanhalf_lower` residual to `2×10⁻³⁷`, as the functional
equation says it must.

### Dependencies
**Depends on:** `gamma_cos_estimate_lower_collapsed`.
**Used by:** `zetalessthanhalf_lower`. -/
theorem gamma_cos_estimate_lower {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
        + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
        + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
        - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ 4 / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h := gamma_cos_estimate_lower_collapsed hσ ht
  have h14 : (1.4:ℝ) / t ≤ 0.14 := by rw [div_le_iff₀ ht0]; linarith
  have hle : (1 / 2 + 1.4 / t) / t ^ 2 ≤ 4 / t ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact h.trans hle

/-- **Lemma `\ref{lem:zetalessthanhalf}`**, second case: for `-1 ≤ σ ≤ 0` and `t > 10`, the same
identity holds with error `O^*(4/t²)`.

### Summary of Proof
The `-1 ≤ σ ≤ 0` half of the same reflection identity as `zetalessthanhalf_upper`: take real parts
of the functional equation (`log_norm_zeta_functional_eq`) to express `log|ζ(σ+it)|` through
`log|ζ(1-σ+it)|` plus the explicit `Γ`- and `π`-factors, then bound the `ζ`-free remainder by
`gamma_cos_estimate_lower`. Only the error budget differs — `4/t²` here against `1/(2t²)` —
because the tex's half-argument route needs the shift identity `Γ(z) = Γ(z+1)/z` once more when
`σ < 0`, costing a little accuracy.

### Lean Notes
No `hz` hypothesis is needed here: `Re(1-σ+it) = 1-σ ≥ 1`, so `riemannZeta_ne_zero_of_one_le_re`
supplies the nonvanishing that `log_norm_zeta_functional_eq` requires. On the Mathlib-native route
(one Stirling application at `1-σ-it`) the tex's shift identity is unnecessary. The sharper
`(1/2 + 1.4/t)/t²` that the tex displays is `zetalessthanhalf_lower_collapsed`.

### References
tex: `\ref{lem:zetalessthanhalf}`.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py`: `sup |residual|·t² = 0.5` over `σ ∈ [-1,0]`,
`t ≥ 10` (the `σ = -1` limit, `Dcoeff(-1) = 1/2`), against the stated `4`.

### Dependencies
**Depends on:** `log_norm_zeta_functional_eq`, `gamma_cos_estimate_lower`.
**Used by:** none. -/
theorem zetalessthanhalf_lower {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ 4 / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  -- `Re(1-σ+it) = 1-σ ≥ 1` because `σ ≤ 0`, so `ζ` cannot vanish there
  have hne : riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_self]
    linarith [hσ.2]
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hne
  have hgc := gamma_cos_estimate_lower hσ ht
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)| := by
        congr 1; linarith [hfe]
    _ ≤ 4 / t ^ 2 := hgc

/-- **Tight version of `zetalessthanhalf_upper`**, matching the "moreover" clause of
`ZerosInShortIntervals.tex`'s Lemma `\ref{lem:zetalessthanhalf}`: keeps the `1/t²`-order
term `Dcoeff σ` explicit instead of folding it into the error, leaving only an `O^*(0.06/t³)` tail.
The tex states the combined form `O^*((√3/216+0.17/t)/t²)`; the same shape with the sharper
`0.06` is `zetalessthanhalf_upper_collapsed` below, and follows from this since
`|Dcoeff σ| ≤ √3/216`.

### Summary of Proof
`log_norm_zeta_functional_eq` rewrites the left side as `|E(σ,t) - Dcoeff σ/t²|` for the `ζ`-free
quantity `E` of `gamma_cos_estimate_upper_tight`, which bounds it by `0.06/t³`.

### Lean Notes
**`hz` is needed for the reason set out in full under `zetalessthanhalf_upper`** — briefly: this
is *not* a divergence from the tex, which uses the convention `log|0| = -∞` and so needs no
hypothesis, whereas Lean's `Real.log 0 = 0` is a finite junk value that turns the same sentence
false at a zero. Every downstream use integrates `log‖ζ‖`, and `ζ`'s zeros on a segment are
isolated, so excluding them changes no integral.

**Where `0.06` comes from.** It is what the proof gives: the Taylor remainders contribute at most
`0.42/t⁴ ≤ 0.042/t³` on this range, and Brent's remainder `(1+√(2π))/(360t³) < 0.00975/t³`. The
tex's Lemma 36 carries the same `√3/216` for the `1/t²` coefficient, but the weaker `0.17` for
this one; its two-half-argument route pays `≈ 0.156/t³` for its two Brent remainders at
`|z| ≈ t/2` alone (see `gamma_cos_estimate_general`'s Lean Notes).

### References
tex: `\ref{lem:zetalessthanhalf}`.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py`: `sup |residual - Dcoeff σ/t²|·t³ = 1.23×10⁻⁴` over
`σ ∈ [0,1/2]`, `t ≥ 10` (at `σ = 1/4`, `t = 10`), against the proved `0.06` — a factor `≈ 490` of
slack, all of it in the crude `t = 10` bounds on the `1/t⁴` Taylor terms.
`Code/indep_mpmath_lemma35_constants.py` (Part D) checks the constants `0.42`, `0.042`,
`0.00975` and their sum.

### Dependencies
**Depends on:** `Dcoeff`, `log_norm_zeta_functional_eq`, `gamma_cos_estimate_upper_tight`.
**Used by:** none. -/
theorem zetalessthanhalf_upper_tight {σ t : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) (ht : 10 < t)
    (hz : riemannZeta ((1 : ℂ) - σ + t * Complex.I) ≠ 0) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi| + Dcoeff σ / t ^ 2)|
      ≤ 0.06 / t ^ 3 := by
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hz
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hz
  have hgc := gamma_cos_estimate_upper_tight hσ ht
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|
            + Dcoeff σ / t ^ 2)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)
          - Dcoeff σ / t ^ 2| := by
        congr 1; linarith [hfe]
    _ ≤ 0.06 / t ^ 3 := hgc

/-- **Tight version of `zetalessthanhalf_lower`**, with tail `O^*(1.4/t³)`; see
`zetalessthanhalf_upper_tight`.

### Summary of Proof
The `-1 ≤ σ ≤ 0` counterpart of `zetalessthanhalf_upper_tight`: `log_norm_zeta_functional_eq`
(nonvanishing from `riemannZeta_ne_zero_of_one_le_re`, since `Re(1-σ+it) ≥ 1`) followed by
`gamma_cos_estimate_lower_tight`, with `Dcoeff2 σ = Dcoeff σ` by definition.

### Lean Notes
**Where `1.4` comes from.** It is what the proof gives: the Taylor remainders contribute at most
`13.08/t⁴ ≤ 1.308/t³` on `[-1,0]` (the `(1-σ)⁵/5 ≤ 32/5` term dominates), and Brent's remainder
`< 0.00975/t³`. The tex's second case reads `(1/2 + 1.4/t)/t²`, the collapsed form
`zetalessthanhalf_lower_collapsed`.

`Dcoeff2` is definitionally `Dcoeff`, the coefficient `σ(2σ-1)(1-σ)/12` — a single polynomial
valid on both `σ`-ranges, since the Stirling derivation never uses the sign of `σ`. A cubic that
merely interpolated the `-1 ≤ σ ≤ 0` case would not do: the candidate
`-(6σ³+6σ²+25σ+11)/6` agrees with the truth only at `σ = -1/2` and makes the residual times `t³`
grow linearly (`183.3` at `t = 10²`), which is what a divergence test exhibits. The live checks of
the corrected coefficient are `Code/verify_Dcoeff_corrected.py` and
`Code/indep_mpmath_zeta_functional_eq.py`.

### References
No tex counterpart for the split form; the tex's collapsed second case is
`zetalessthanhalf_lower_collapsed`.

**Independent numeric check.**
`Code/indep_mpmath_zeta_functional_eq.py`: `sup |residual - Dcoeff σ/t²|·t³ = 0.0248` over
`σ ∈ [-1,0]`, `t ≥ 10` (at `σ = -1`, `t = 10`), against the proved `1.4` — a factor `56` of slack.
`Code/indep_mpmath_lemma35_constants.py` (Part D) checks `13.08`, `1.308`, `0.00975`.

### Dependencies
**Depends on:** `Dcoeff2`, `log_norm_zeta_functional_eq`, `gamma_cos_estimate_lower_tight`.
**Used by:** none. -/
theorem zetalessthanhalf_lower_tight {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi| + Dcoeff2 σ / t ^ 2)|
      ≤ 1.4 / t ^ 3 := by
  unfold Dcoeff2
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  have hne : riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_self]
    linarith [hσ.2]
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hne
  have hgc := gamma_cos_estimate_lower_tight hσ ht
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|
            + Dcoeff σ / t ^ 2)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)
          - Dcoeff σ / t ^ 2| := by
        congr 1; linarith [hfe]
    _ ≤ 1.4 / t ^ 3 := hgc

/-- **Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36), first case, in the tex's collapsed shape**:
for `0 ≤ σ ≤ 1/2`, `t > 10` and `ζ(1-σ+it) ≠ 0`,
`log|ζ(σ+it)| = log|ζ(1-σ+it)| + (1/2-σ)log|t/2| + (σ-1/2)log π + O^*((√3/216 + 0.06/t)/t²)`,
with the `1/t³` constant sharpened from the tex's `0.17` to `0.06`.

### Summary of Proof
`log_norm_zeta_functional_eq` and `gamma_cos_estimate_upper_collapsed`.

### Lean Notes
`zetalessthanhalf_upper` is the weaker `1/(2t²)` form used downstream; this one keeps the tex's
own collapsed shape. `hz` as in `zetalessthanhalf_upper`.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), first case.

### Dependencies
**Depends on:** `log_norm_zeta_functional_eq`, `gamma_cos_estimate_upper_collapsed`.
**Used by:** none. -/
theorem zetalessthanhalf_upper_collapsed {σ t : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (ht : 10 < t) (hz : riemannZeta ((1 : ℂ) - σ + t * Complex.I) ≠ 0) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hz
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hz
  have hgc := gamma_cos_estimate_upper_collapsed hσ ht
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)| := by
        congr 1; linarith [hfe]
    _ ≤ (Real.sqrt 3 / 216 + 0.06 / t) / t ^ 2 := hgc

/-- **Lemma `\ref{lem:zetalessthanhalf}` (Lemma 36), second case, exactly as the tex states
it**: for `-1 ≤ σ ≤ 0` and `t > 10`,
`log|ζ(σ+it)| = log|ζ(1-σ+it)| + (1/2-σ)log|t/2| + (σ-1/2)log π + O^*((1/2 + 1.4/t)/t²)`.

### Summary of Proof
`log_norm_zeta_functional_eq` (nonvanishing from `riemannZeta_ne_zero_of_one_le_re`) and
`gamma_cos_estimate_lower_collapsed`.

### Lean Notes
`zetalessthanhalf_lower` is the weaker `4/t²` form; this one records the tex's constants
verbatim.

### References
tex: `\ref{lem:zetalessthanhalf}` (Lemma 36), second case.

### Dependencies
**Depends on:** `log_norm_zeta_functional_eq`, `gamma_cos_estimate_lower_collapsed`.
**Used by:** none. -/
theorem zetalessthanhalf_lower_collapsed {σ t : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 0) (ht : 10 < t) :
    |Real.log ‖riemannZeta (σ + t * Complex.I)‖
        - (Real.log ‖riemannZeta (1 - σ + t * Complex.I)‖ + (1 / 2 - σ) * Real.log |t / 2|
            + (σ - 1 / 2) * Real.log |Real.pi|)|
      ≤ (1 / 2 + 1.4 / t) / t ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have hcast : ((1 : ℂ) - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  have hne : riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_self]
    linarith [hσ.2]
  have hfe := log_norm_zeta_functional_eq (σ := σ) ht0 hne
  have hgc := gamma_cos_estimate_lower_collapsed hσ ht
  rw [hcast]
  calc |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - (Real.log ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            + (1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)|
      = |Real.log 2 - (1 - σ) * Real.log (2 * Real.pi)
          + Real.log ‖Complex.Gamma ((1 - σ : ℝ) - t * Complex.I)‖
          + Real.log ‖Complex.cos (Real.pi * ((1 - σ : ℝ) - t * Complex.I) / 2)‖
          - ((1 / 2 - σ) * Real.log |t / 2| + (σ - 1 / 2) * Real.log |Real.pi|)| := by
        congr 1; linarith [hfe]
    _ ≤ (1 / 2 + 1.4 / t) / t ^ 2 := hgc

/-! ## The Brent Stirling expansions live in `ExternalFacts`

`logGammaAnalytic` (the Weierstrass series), `exp_logGammaAnalytic`, the unshifted trio
`brent_stirling_remainder`/`brent_stirling_expansion`/`brent_stirling_remainder_bound` and the
shifted trio `brentShiftedRemainder`/`brent_stirling_shifted_expansion`/
`brent_stirling_shifted_remainder_bound` are all declared in
`ZerosInShortIntervals.Background.ExternalFacts`, so that the whole family is stated in one place
against one branch of `log Γ`. Neither file is in a namespace, so the names used below are
unqualified.

**Why they have to be there and not here.** The expansions must be stated about the *analytic*
branch `logGammaAnalytic`, never about `Complex.log ∘ Complex.Gamma`: the principal branch caps
the imaginary part at `π` while the Stirling right-hand side's grows like `(t/2)log(t/2)`, which
would force `‖R₂(z)‖` to be a nonzero multiple of `2π` against a bound of `≈ 10⁻⁵`. And
`ExternalFacts` cannot depend on this file, so `logGammaAnalytic` and everything stated about it
must live there. See that file's "Brent's explicit Stirling expansions" section header for the
full account, the measured multiples, and the PDF citations.
-/

/-- **The imaginary part of the shifted Stirling expansion.** For `Im z > 5`,
`Im logGammaAnalytic (z+1/2) = Re z · arg z + (Im z/2)·log(Re z² + Im z²) - Im z
  + Im z/(24(Re z² + Im z²)) + Im R̂₂(z)`.

### Summary of Proof
Take imaginary parts of `brent_stirling_shifted_expansion` term by term.
`Im(z log z) = Re z·Im log z + Im z·Re log z = Re z·arg z + Im z·log‖z‖`, and
`log‖z‖ = (1/2)log(‖z‖²) = (1/2)log(Re z² + Im z²)`. `Im(-z) = -Im z`. The constant
`(1/2)log(2π)` is real, so contributes nothing. Finally `Im(z⁻¹) = -Im z/‖z‖²`, so
`Im(-1/(24z)) = Im z/(24‖z‖²)`.

### Lean Notes
Stated with `Re z ^ 2 + Im z ^ 2` rather than `‖z‖ ^ 2` so that the two specialisations in
`argGamma_im_diff` need no square-root manipulation.

### References
No tex counterpart — the imaginary part of the tex's own displayed Stirling difference, on the
analytic branch.

### Dependencies
**Depends on:** `brent_stirling_shifted_expansion`, `logGammaAnalytic`, `brentShiftedRemainder`.
**Used by:** `argGamma_im_diff`. -/
theorem logGammaAnalytic_shift_im {z : ℂ} (hz : 5 < z.im) :
    (logGammaAnalytic (z + 1 / 2)).im
      = z.re * Complex.arg z + z.im / 2 * Real.log (z.re ^ 2 + z.im ^ 2) - z.im
        + z.im / (24 * (z.re ^ 2 + z.im ^ 2)) + (brentShiftedRemainder z).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  have hnorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hns : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hnspos : (0 : ℝ) < z.re ^ 2 + z.im ^ 2 := by rw [← hns]; exact Complex.normSq_pos.mpr hz0
  have hlog : Real.log ‖z‖ = 1 / 2 * Real.log (z.re ^ 2 + z.im ^ 2) := by
    rw [← hn2, Real.log_pow]; push_cast; ring
  have e1 : (z * Complex.log z).im = z.re * Complex.arg z + z.im * Real.log ‖z‖ := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re]
  have e2 : ((1 : ℂ) / 2 * Complex.log (2 * (Real.pi : ℂ))).im = 0 := by
    have harg : (Complex.log (2 * (Real.pi : ℂ))).im = 0 := by
      have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.log_im, Complex.arg_ofReal_of_nonneg (by positivity)]
    norm_num [Complex.mul_im, harg]
  have e3 : ((1 : ℂ) / (24 * z)).im = -(z.im / (24 * (z.re ^ 2 + z.im ^ 2))) := by
    have h24 : ((24 : ℂ) * z).im = 24 * z.im := by simp
    have hn24 : Complex.normSq ((24 : ℂ) * z) = 576 * (z.re ^ 2 + z.im ^ 2) := by
      rw [Complex.normSq_mul, hns]; norm_num [Complex.normSq_apply]
    rw [one_div, Complex.inv_im, h24, hn24]
    field_simp
    ring
  rw [brent_stirling_shifted_expansion hz]
  simp only [Complex.add_im, Complex.sub_im]
  rw [e1, e2, e3, hlog]
  ring

/-- **The exact `Im`-difference at the two points of `Lemma \ref{lemma:argGamma}` (Lemma 37).**
On the analytic branch, for `t > 10`,
`Im logGA(1/2+it/2) - Im logGA(1/2+δ/2+it/2)
  = -δπ/4 + (δ/2)arctan(δ/t) - (t/4)log(1+δ²/t²) + δ²/(12t(δ²+t²))
    + Im R̂₂(it/2) - Im R̂₂(δ/2+it/2)`.

### Summary of Proof
Apply `logGammaAnalytic_shift_im` at `z₀ = it/2` and `z₁ = δ/2 + it/2` (both have
`Im = t/2 > 5`) and subtract.

* At `z₀`: `Re z₀ = 0`, so the `arg` term drops out; `Re² + Im² = t²/4`, giving
  `(t/4)log(t²/4) - t/2 + 1/(12t)`.
* At `z₁`: `Re z₁ = δ/2` and `arg z₁ = π/2 - arctan(δ/t)` by `arg_eq_pi_div_two_sub_arctan`;
  `Re² + Im² = (δ²+t²)/4`, giving
  `(δ/2)(π/2 - arctan(δ/t)) + (t/4)log((δ²+t²)/4) - t/2 + t/(12(δ²+t²))`.

Subtracting: the `-t/2` cancel; the `π/2` term leaves `-δπ/4`; the logs combine as
`(t/4)(log(t²/4) - log((δ²+t²)/4)) = -(t/4)log(1+δ²/t²)`; and
`1/(12t) - t/(12(δ²+t²)) = δ²/(12t(δ²+t²))`.

**Where the `-δπ/4` comes from.** It is the `(a-b)·π/2` contribution of
`Im[(a - 1/2 + it/2)·log(i + 2a/t)]`, with `a - b = -δ/2`. It is a *constant*, so it does not
vanish as `t → ∞`; dropping it, or carrying `t/2` where `t/4` belongs, or flipping the sign of
the two `arctan` terms, all change the answer at leading order. The tex's displayed imaginary
part carries the same three choices as here.

### Lean Notes
Proved exactly as sketched: `simp` computes the real and
imaginary parts of the two points, `arg_eq_pi_div_two_sub_arctan` needs only `0 < Im z`, the
log combination `log(t²/4) - log((δ²+t²)/4) = -log(1+δ²/t²)` is justified via `Real.log_mul`
with both arguments positive (`Real.log` is total, so this cannot be left to `simp`), the
`1/(24|z|²)` terms are combined by `field_simp; ring`, and `linear_combination` assembles the
identity.

### References
tex: the displayed imaginary part inside the proof of `\ref{lemma:argGamma}` (Lemma 37).

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [E] evaluates the left side with mpmath's `loggamma`
(which *is* the analytic branch) and confirms the whole identity-plus-remainder picture: the full
residual `|Im lgΓ(1/2+it/2) - Im lgΓ(1/2+δ/2+it/2) + δπ/4 - δ²/(4t)|·t³` has supremum `0.04218`
(at `δ = 1`, `t = 10`), of which `1/24 = 0.04167` is the Taylor part isolated in
`argGamma_taylor_residue` and the rest is the two Brent remainders.

The tex's proof of Lemma 37 specialises its general `a`, `b` display at `a = 1/2`,
`b = 1/2 + δ/2`, which is exactly the pair of points used here.

### Dependencies
**Depends on:** `logGammaAnalytic_shift_im`, `arg_eq_pi_div_two_sub_arctan`.
**Used by:** `argGamma_analytic`. -/
theorem argGamma_im_diff {δ t : ℝ} (ht : 10 < t) :
    (logGammaAnalytic (1 / 2 + t * Complex.I / 2)).im
        - (logGammaAnalytic (1 / 2 + δ / 2 + t * Complex.I / 2)).im
      = -(δ * Real.pi) / 4 + δ / 2 * Real.arctan (δ / t)
        - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))
        + (brentShiftedRemainder (t * Complex.I / 2)).im
        - (brentShiftedRemainder (δ / 2 + t * Complex.I / 2)).im := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht0' : t ≠ 0 := ht0.ne'
  have hst : δ ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hre0 : (t * Complex.I / 2 : ℂ).re = 0 := by simp
  have him0 : (t * Complex.I / 2 : ℂ).im = t / 2 := by simp
  have hre1 : ((δ : ℂ) / 2 + t * Complex.I / 2).re = δ / 2 := by simp
  have him1 : ((δ : ℂ) / 2 + t * Complex.I / 2).im = t / 2 := by simp
  have hgt0 : (5 : ℝ) < (t * Complex.I / 2 : ℂ).im := by rw [him0]; linarith
  have hgt1 : (5 : ℝ) < ((δ : ℂ) / 2 + t * Complex.I / 2).im := by rw [him1]; linarith
  have hpos1 : (0 : ℝ) < ((δ : ℂ) / 2 + t * Complex.I / 2).im := by rw [him1]; positivity
  -- the two points, written as `z + 1/2` for `logGammaAnalytic_shift_im`
  have e0 : (1 / 2 + t * Complex.I / 2 : ℂ) = (t * Complex.I / 2) + 1 / 2 := by ring
  have e1 : (1 / 2 + δ / 2 + t * Complex.I / 2 : ℂ)
      = ((δ : ℂ) / 2 + t * Complex.I / 2) + 1 / 2 := by ring
  rw [e0, e1, logGammaAnalytic_shift_im hgt0, logGammaAnalytic_shift_im hgt1,
    arg_eq_pi_div_two_sub_arctan hpos1, hre0, him0, hre1, him1]
  have hδt : δ / 2 / (t / 2) = δ / t := by field_simp
  rw [hδt]
  -- `log(t²/4) - log((δ²+t²)/4) = -log(1+δ²/t²)`, both arguments positive
  have hlog : Real.log ((0:ℝ) ^ 2 + (t / 2) ^ 2) - Real.log ((δ / 2) ^ 2 + (t / 2) ^ 2)
      = - Real.log (1 + δ ^ 2 / t ^ 2) := by
    have hA : (0:ℝ) ^ 2 + (t / 2) ^ 2 = t ^ 2 / 4 := by ring
    have hB : (δ / 2) ^ 2 + (t / 2) ^ 2 = (t ^ 2 / 4) * (1 + δ ^ 2 / t ^ 2) := by
      field_simp
      ring
    rw [hA, hB, Real.log_mul (by positivity) (by positivity)]
    ring
  -- `1/(12t) - t/(12(δ²+t²)) = δ²/(12t(δ²+t²))`
  have hfrac : t / 2 / (24 * ((0:ℝ) ^ 2 + (t / 2) ^ 2))
        - t / 2 / (24 * ((δ / 2) ^ 2 + (t / 2) ^ 2))
      = δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)) := by
    field_simp
    ring
  linear_combination (t / 4) * hlog + hfrac

/-- **Taylor bound for `arctan`**: `|arctan x - x| ≤ |x|³/3` for `|x| ≤ 1`.

### Summary of Proof
`arctan x = x - x³/3 + x⁵/5 - …` is an alternating series with decreasing terms for `|x| ≤ 1`,
so truncating after the linear term costs at most the first omitted term, `|x|³/3`.
Equivalently, `arctan x - x = -∫₀ˣ u²/(1+u²) du` and `0 ≤ u²/(1+u²) ≤ u²`.

### Lean Notes
Proved with the sharp constant, by monotonicity rather than the
integral form: on `[0,∞)` both `y ↦ y - arctan y` (derivative `1 - 1/(1+y²) ≥ 0`) and
`y ↦ arctan y - y + y³/3` (derivative `1/(1+y²) - 1 + y² = y⁴/(1+y²) ≥ 0`) are monotone
(`monotoneOn_of_deriv_nonneg` on `Set.Ici 0`) and vanish at `0`, giving
`y - y³/3 ≤ arctan y ≤ y`; the case `x < 0` follows from `Real.arctan_neg`. Mathlib has no
`arctan` Taylor estimate of its own. The hypothesis `|x| ≤ 1` is not used — the bound holds for
every real `x` — but is kept so the statement is unchanged for its caller.

### References
No tex counterpart — an elementary calculus fact the tex applies silently ("several
applications of Taylor's Theorem").

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [G]: `sup_{0<x≤1} |arctan x - x|/(x³/3) = 0.9999994`
(approached as `x → 0`), so the constant `1/3` is sharp.

### Dependencies
**Depends on:** none.
**Used by:** `argGamma_taylor_residue`. -/
theorem abs_arctan_sub_self_le_cube_div_three {x : ℝ} (_hx : |x| ≤ 1) :
    |Real.arctan x - x| ≤ |x| ^ 3 / 3 := by
  -- both one-sided bounds on `[0,∞)`, by monotonicity of `y - arctan y` and `arctan y - y + y³/3`
  have key : ∀ y : ℝ, 0 ≤ y → y - y ^ 3 / 3 ≤ Real.arctan y ∧ Real.arctan y ≤ y := by
    intro y hy
    have hf : MonotoneOn (fun y : ℝ => y - Real.arctan y) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (continuous_id.sub Real.continuous_arctan).continuousOn
      · intro z _
        exact (differentiableAt_id.sub (Real.differentiable_arctan z)).differentiableWithinAt
      · intro z _
        have hd : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - 1 / (1 + z ^ 2)) z :=
          (hasDerivAt_id z).sub (Real.hasDerivAt_arctan z)
        rw [hd.deriv]
        have : (1:ℝ) / (1 + z ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith [sq_nonneg z]
        linarith
    have hg : MonotoneOn (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((Real.continuous_arctan.sub continuous_id).add (by fun_prop)).continuousOn
      · intro z _
        exact (((Real.differentiable_arctan z).sub differentiableAt_id).add
          (by fun_prop)).differentiableWithinAt
      · intro z _
        have h1 := Real.hasDerivAt_arctan z
        have h2 : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
        have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (z ^ 2) z := by
          have := (hasDerivAt_pow 3 z).div_const 3
          have e : ((3 : ℕ) : ℝ) * z ^ (3 - 1) / 3 = z ^ 2 := by
            norm_num
          rw [e] at this
          exact this
        have hd : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
            (1 / (1 + z ^ 2) - 1 + z ^ 2) z := (h1.sub h2).add h3
        rw [hd.deriv]
        have hpos : (0:ℝ) < 1 + z ^ 2 := by positivity
        have : (1 - z ^ 2) ≤ 1 / (1 + z ^ 2) := by
          rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (z ^ 2)]
        linarith
    have h0f := hf (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hy) hy
    have h0g := hg (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hy) hy
    simp only [Real.arctan_zero] at h0f h0g
    constructor <;> linarith
  rcases le_or_gt 0 x with hx0 | hx0
  · obtain ⟨h1, h2⟩ := key x hx0
    rw [abs_of_nonneg hx0, abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := key (-x) (by linarith)
    rw [Real.arctan_neg] at h1 h2
    have hx3 : 0 ≤ (-x) ^ 3 := pow_nonneg (by linarith) 3
    rw [abs_of_neg hx0, abs_le]
    constructor <;> linarith

/-- **Taylor bound for `log(1+x)`**: `|log(1+x) - x| ≤ x²` for `0 ≤ x`.

### Summary of Proof
Upper: `log(1+x) ≤ x`, which is `Real.log_le_sub_one_of_pos` at `1+x`.
Lower: `Real.one_sub_inv_le_log_of_pos` gives `log(1+x) ≥ 1 - 1/(1+x) = x/(1+x)`, and
`x/(1+x) = x - x²/(1+x) ≥ x - x²` for `x ≥ 0`.

### Lean Notes
The sharp constant is `x²/2`; `x²` is what Mathlib's two one-sided inequalities give directly,
and it is ample for `argGamma_taylor_residue`.

### References
No tex counterpart — an elementary calculus fact.

### Dependencies
**Depends on:** none.
**Used by:** `argGamma_taylor_residue`. -/
theorem abs_log_one_add_sub_self_le_sq {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have hup : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hlow : x - x ^ 2 ≤ Real.log (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos h1
    have h2 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [h2] at h
    have h3 : x - x ^ 2 ≤ x / (1 + x) := by
      rw [le_div_iff₀ h1]
      nlinarith [sq_nonneg x, mul_nonneg hx hx]
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- **The purely real Taylor residue of `Lemma \ref{lemma:argGamma}` (Lemma 37).**
For `|δ| ≤ 1` and `t > 10`,
`|(δ/2)arctan(δ/t) - (t/4)log(1+δ²/t²) - δ²/(4t) + δ²/(12t(δ²+t²))| ≤ 1/t³`.

### Summary of Proof
Write `A = (δ/2)arctan(δ/t)`, `B = (t/4)log(1+δ²/t²)`, `C = δ²/(12t(δ²+t²))`. Then

* `A = δ²/(2t) + A'` with `|A'| ≤ (|δ|/2)·|δ/t|³/3 = δ⁴/(6t³) ≤ 1/(6t³)`
  (`abs_arctan_sub_self_le_cube_div_three` at `x = δ/t`, legitimate since `|δ/t| < 1/10`);
* `B = δ²/(4t) + B'` with `|B'| ≤ (t/4)·(δ²/t²)² = δ⁴/(4t³) ≤ 1/(4t³)`
  (`abs_log_one_add_sub_self_le_sq` at `x = δ²/t² ≥ 0`);
* `0 ≤ C ≤ δ²/(12t·t²) ≤ 1/(12t³)`.

The explicit parts cancel exactly: `δ²/(2t) - δ²/(4t) - δ²/(4t) = 0`. So the residue is
`A' - B' + C`, of modulus at most `(1/6 + 1/4 + 1/12)/t³ = (1/2)/t³ ≤ 1/t³`.

### Lean Notes
The bound `1/t³` is deliberately loose — the true value is `(δ²/12 - δ⁴/24)/t³ + O(1/t⁵)`, at
most `(1/24)/t³ ≈ 0.0417/t³` on `|δ| ≤ 1`, confirmed in `Code/verify_argGamma.py`
section (F). The slack is what lets the two crude Taylor bounds above be used unsharpened.

The Lean proof follows exactly that split: the identity
`residue = (δ/2)(arctan(δ/t) - δ/t) - (t/4)(log(1+δ²/t²) - δ²/t²) + δ²/(12t(δ²+t²))` is
`field_simp; ring`, the three pieces are bounded by `1/(6t³)`, `1/(4t³)`, `1/(12t³)` using
`|δ| ≤ 1` (so `δ⁴ ≤ 1`), and the triangle inequality (`abs_add_le`, `abs_sub`) finishes with
`1/(2t³) ≤ 1/t³`.

### References
tex: the "several applications of Taylor's Theorem" at the end of the proof of
`\ref{lemma:argGamma}` (Lemma 37), made explicit — but note that the tex's own target expression
is a different one; see `argGamma`'s Lean Notes.

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [F]: the supremum of the residual times `t³` over
`|δ| ≤ 1`, `t ≥ 10` is `0.041667 = 1/24` (leading order `δ²/12 - δ⁴/24` at `δ = 1`), against the
stated `1`. A Lean proof from the two Taylor bounds named above gets `1/6 + 1/4 + 1/12 = 1/2`.

### Dependencies
**Depends on:** `abs_arctan_sub_self_le_cube_div_three`, `abs_log_one_add_sub_self_le_sq`.
**Used by:** none — `argGamma_analytic` uses the sharper `argGamma_taylor_residue_sharp`
instead. This is the loose form, kept because it is the one an unsharpened Taylor argument
gives. -/
theorem argGamma_taylor_residue {δ t : ℝ} (hδ : |δ| ≤ 1) (ht : 10 < t) :
    |δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))| ≤ 1 / t ^ 3 := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht3 : (0:ℝ) < t ^ 3 := by positivity
  have hδabs := abs_le.mp hδ
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hδ4 : δ ^ 4 ≤ 1 := by nlinarith [sq_nonneg (δ ^ 2), sq_nonneg δ]
  have hxabs : |δ / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht0, div_le_one ht0]; linarith
  have h1 := abs_arctan_sub_self_le_cube_div_three hxabs
  have hy0 : (0:ℝ) ≤ δ ^ 2 / t ^ 2 := by positivity
  have h2 := abs_log_one_add_sub_self_le_sq hy0
  -- the two main terms `δ²/(2t)` and `δ²/(4t)` cancel against `δ²/(4t)` exactly
  have hE : δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))
      = δ / 2 * (Real.arctan (δ / t) - δ / t)
        - t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)) := by
    field_simp
    ring
  rw [hE]
  -- the three pieces: `≤ 1/(6t³)`, `≤ 1/(4t³)`, `≤ 1/(12t³)`
  have hb1 : |δ / 2 * (Real.arctan (δ / t) - δ / t)| ≤ 1 / (6 * t ^ 3) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hx3 : |δ / t| ^ 3 = |δ| ^ 3 / t ^ 3 := by rw [abs_div, abs_of_pos ht0, div_pow]
    have hδ4' : |δ| ^ 4 = δ ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc |δ| / 2 * |Real.arctan (δ / t) - δ / t| ≤ |δ| / 2 * (|δ / t| ^ 3 / 3) := by gcongr
      _ = |δ| ^ 4 / (6 * t ^ 3) := by rw [hx3]; ring
      _ ≤ 1 / (6 * t ^ 3) := by
          rw [hδ4']
          exact div_le_div_of_nonneg_right hδ4 (by positivity)
  have hb2 : |t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2)| ≤ 1 / (4 * t ^ 3) := by
    rw [abs_mul, abs_div, abs_of_pos ht0, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    have hsq : t / 4 * (δ ^ 2 / t ^ 2) ^ 2 = δ ^ 4 / (4 * t ^ 3) := by
      field_simp
    calc t / 4 * |Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2| ≤ t / 4 * (δ ^ 2 / t ^ 2) ^ 2 := by
          gcongr
      _ = δ ^ 4 / (4 * t ^ 3) := hsq
      _ ≤ 1 / (4 * t ^ 3) := div_le_div_of_nonneg_right hδ4 (by positivity)
  have hb3 : δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)) ≤ 1 / (12 * t ^ 3) := by
    have hpos1 : (0:ℝ) < 12 * t * (δ ^ 2 + t ^ 2) := by positivity
    have hpos2 : (0:ℝ) < 12 * t ^ 3 := by positivity
    rw [div_le_div_iff₀ hpos1 hpos2]
    have hδt : δ ^ 2 * t ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hδt), mul_nonneg ht0.le (sq_nonneg δ)]
  have hb3' : |δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))| ≤ 1 / (12 * t ^ 3) := by
    rw [abs_of_nonneg (by positivity)]; exact hb3
  have hsum : 1 / (6 * t ^ 3) + 1 / (4 * t ^ 3) + 1 / (12 * t ^ 3) = 1 / (2 * t ^ 3) := by
    field_simp
    ring
  have htri : |δ / 2 * (Real.arctan (δ / t) - δ / t)
        - t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))|
      ≤ |δ / 2 * (Real.arctan (δ / t) - δ / t)|
        + |t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2)|
        + |δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))| := by
    have ha := abs_add_le (δ / 2 * (Real.arctan (δ / t) - δ / t)
        - t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2))
        (δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)))
    have hb := abs_sub (δ / 2 * (Real.arctan (δ / t) - δ / t))
        (t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2))
    linarith
  have hfin : 1 / (2 * t ^ 3) ≤ 1 / t ^ 3 :=
    div_le_div_of_nonneg_left zero_le_one ht3 (by linarith)
  linarith

/-- **Sharp form of `argGamma_taylor_residue`**: the pure-real residual of Lemma 37 is at most
`0.045/t³` for `|δ| ≤ 1`, `t > 10`.

### Summary of Proof
The exact decomposition (a `field_simp; ring` identity)

    residual = (δ²/12 - δ⁴/24)/t³ - δ⁴/(12t³(δ²+t²))
               + (δ/2)(arctan y - y + y³/3) - (t/4)(log(1+u) - u + u²/2),   y = δ/t, u = δ²/t²,

exhibits the `1/t³` coefficient `δ²/12 - δ⁴/24 ∈ [0, 1/24]`; the other three pieces are
`O(1/t⁵)` by `abs_arctan_sub_self_add_cube_le` (`≤ |y|⁵/5`) and `log_one_add_third_order`
(`≤ u³/3`): together `≤ (1/12 + 1/10 + 1/12)/t⁵ = (4/15)/t⁵ ≤ (4/1500)/t³`. Total
`1/24 + 4/1500 = 0.04433… ≤ 0.045`.

### Lean Notes
This is the Taylor part of Lemma 37's proof made explicit. `0.045` is what Taylor gives for the
explicit part alone; `argGamma_analytic` then adds `2 × 0.08` for the two Brent remainders to
reach the `0.21` the tex states. Numerically the *whole* residual, remainders included, has
supremum only `0.04218`, but that value is not reachable from Brent's stated remainder bound.

### References
tex: `\ref{lemma:argGamma}` (Lemma 37), the "several applications of Taylor's Theorem" step;
`Code/indep_mpmath_lemma35_constants.py` (Part E) checks the decomposition and the constants.

### Dependencies
**Depends on:** `abs_arctan_sub_self_add_cube_le`, `log_one_add_third_order`.
**Used by:** `argGamma_analytic`. -/
theorem argGamma_taylor_residue_sharp {δ t : ℝ} (hδ : |δ| ≤ 1) (ht : 10 < t) :
    |δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))| ≤ 0.045 / t ^ 3 := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht2 : (100:ℝ) ≤ t ^ 2 := by nlinarith
  have hδabs := abs_le.mp hδ
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hδ20 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [sq_nonneg (δ ^ 2)]
  have hδ6 : δ ^ 6 ≤ 1 := by nlinarith [pow_nonneg hδ20 3, sq_nonneg (δ ^ 3)]
  have hy := abs_arctan_sub_self_add_cube_le (δ / t)
  have hu0 : (0:ℝ) ≤ δ ^ 2 / t ^ 2 := by positivity
  obtain ⟨hl1, hl2⟩ := log_one_add_third_order hu0
  -- exact decomposition
  have hE : δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
        + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))
      = (δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3 - δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2))
        + δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3)
        - t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2 + (δ ^ 2 / t ^ 2) ^ 2 / 2) := by
    field_simp
    ring
  rw [hE]
  have hb0 : |(δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3| ≤ (1 / 24) / t ^ 3 := by
    rw [abs_div, abs_of_pos (pow_pos ht0 3)]
    have habs : |δ ^ 2 / 12 - δ ^ 4 / 24| ≤ 1 / 24 := by
      rw [abs_le]; constructor <;> nlinarith
    exact div_le_div_of_nonneg_right habs (by positivity)
  have hb1 : |δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2))| ≤ 1 / (12 * t ^ 5) := by
    rw [abs_of_nonneg (by positivity)]
    have hpos1 : (0:ℝ) < 12 * t ^ 3 * (δ ^ 2 + t ^ 2) := by positivity
    have hpos2 : (0:ℝ) < 12 * t ^ 5 := by positivity
    rw [div_le_div_iff₀ hpos1 hpos2]
    have : δ ^ 4 * (12 * t ^ 5) ≤ 1 * (12 * t ^ 3 * (δ ^ 2 + t ^ 2)) := by
      have ht5 : t ^ 5 = t ^ 3 * t ^ 2 := by ring
      rw [ht5]
      nlinarith [pow_pos ht0 3, mul_nonneg (pow_pos ht0 3).le hδ20]
    linarith
  have hb2 : |δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3)| ≤ 1 / (10 * t ^ 5) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h5 : |δ / t| ^ 5 = |δ| ^ 5 / t ^ 5 := by rw [abs_div, abs_of_pos ht0, div_pow]
    have hm := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ |δ| / 2)
    rw [h5] at hm
    have : |δ| / 2 * (|δ| ^ 5 / t ^ 5 / 5) ≤ 1 / (10 * t ^ 5) := by
      have h6 : |δ| ^ 6 ≤ 1 := by
        have : |δ| ^ 6 = δ ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [this]; exact hδ6
      have e : |δ| / 2 * (|δ| ^ 5 / t ^ 5 / 5) = |δ| ^ 6 / (10 * t ^ 5) := by ring
      rw [e]
      exact div_le_div_of_nonneg_right h6 (by positivity)
    linarith
  have hb3 : |t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2 + (δ ^ 2 / t ^ 2) ^ 2 / 2)|
      ≤ 1 / (12 * t ^ 5) := by
    rw [abs_mul, abs_div, abs_of_pos ht0, abs_of_pos (by norm_num : (0:ℝ) < 4),
      abs_of_nonneg hl1]
    have hm := mul_le_mul_of_nonneg_left hl2 (by positivity : (0:ℝ) ≤ t / 4)
    have e : t / 4 * ((δ ^ 2 / t ^ 2) ^ 3 / 3) = δ ^ 6 / (12 * t ^ 5) := by
      field_simp
      ring
    rw [e] at hm
    have : δ ^ 6 / (12 * t ^ 5) ≤ 1 / (12 * t ^ 5) :=
      div_le_div_of_nonneg_right hδ6 (by positivity)
    linarith
  have htri : |(δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3 - δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2))
        + δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3)
        - t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2 + (δ ^ 2 / t ^ 2) ^ 2 / 2)|
      ≤ |(δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3| + |δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2))|
        + |δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3)|
        + |t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2 + (δ ^ 2 / t ^ 2) ^ 2 / 2)| := by
    have i1 := abs_sub ((δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3) (δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2)))
    have i2 := abs_add_le
      ((δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3 - δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2)))
      (δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3))
    have i3 := abs_sub ((δ ^ 2 / 12 - δ ^ 4 / 24) / t ^ 3 - δ ^ 4 / (12 * t ^ 3 * (δ ^ 2 + t ^ 2))
        + δ / 2 * (Real.arctan (δ / t) - δ / t + (δ / t) ^ 3 / 3))
      (t / 4 * (Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / t ^ 2 + (δ ^ 2 / t ^ 2) ^ 2 / 2))
    linarith
  have hfin : (1 / 24) / t ^ 3 + 1 / (12 * t ^ 5) + 1 / (10 * t ^ 5) + 1 / (12 * t ^ 5)
      ≤ 0.045 / t ^ 3 := by
    have e : 1 / (12 * t ^ 5) + 1 / (10 * t ^ 5) + 1 / (12 * t ^ 5) = (4 / 15) / t ^ 5 := by
      field_simp; ring
    have h1 : (4 / 15) / t ^ 5 ≤ (4 / 1500) / t ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : t ^ 5 = t ^ 3 * t ^ 2 := by ring
      nlinarith [pow_pos ht0 3]
    have h045 : (1 / 24 : ℝ) / t ^ 3 + (4 / 1500) / t ^ 3 ≤ 0.045 / t ^ 3 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  calc _ ≤ _ := htri
    _ ≤ (1 / 24) / t ^ 3 + 1 / (12 * t ^ 5) + 1 / (10 * t ^ 5) + 1 / (12 * t ^ 5) :=
        add_le_add (add_le_add (add_le_add hb0 hb1) hb2) hb3
    _ ≤ 0.045 / t ^ 3 := hfin

/-- **`Complex.arg (Γ z)` equals the analytic imaginary part only modulo `2π`.**
For `0 < Im z` there is an integer `n` with
`arg (Γ z) = Im (logGammaAnalytic z) + n·2π`.

### Summary of Proof
`Γ z ≠ 0` (its only zeros would be at poles of `1/Γ`, i.e. non-positive integers, which are
real), so `exp (log (Γ z)) = Γ z = exp (logGammaAnalytic z)` by
`ExternalFacts.exp_logGammaAnalytic`, whose slit-plane hypothesis `0 < Re z ∨ Im z ≠ 0` is met
here by `Or.inr hz.ne'`. Two complex numbers with equal exponentials differ by an integer
multiple of `2πi` (`Complex.exp_eq_exp_iff_exists_int`); take imaginary parts, and use
`(Complex.log w).im = arg w`.

### Lean Notes
**This lemma is the precise reason `argGamma` is stated on the analytic branch and not with
`Complex.arg`.** The integer `n` is genuinely unknown and genuinely varies:
`Im logGammaAnalytic (1/2+it/2) ≈ (t/2)log(t/2)`, so
`n` changes as `t` grows, and at heights where the analytic value is near an odd multiple of
`π` the two points `1/2+it/2` and `1/2+δ/2+it/2` receive *different* `n`. Measured at
`t = 10.06, δ = 0.05` (`Code/verify_argGamma.py`, section (C)) the two principal arguments
differ by `6.2440` while the analytic difference is `-0.0392`.

### References
No tex counterpart — the branch bookkeeping the tex leaves implicit by writing `arg` for
`Im log`.

### Dependencies
**Depends on:** `exp_logGammaAnalytic`, `logGammaAnalytic`.
**Used by:** none (it documents the branch gap; cited from `argGamma`'s Lean Notes). -/
theorem arg_Gamma_eq_logGammaAnalytic_im_add_int {z : ℂ} (hz : 0 < z.im) :
    ∃ n : ℤ, Complex.arg (Complex.Gamma z) = (logGammaAnalytic z).im + n * (2 * Real.pi) := by
  have hne : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    rw [h] at hz
    simp at hz
  have h1 : Complex.exp (Complex.log (Complex.Gamma z)) = Complex.exp (logGammaAnalytic z) := by
    rw [Complex.exp_log hne, exp_logGammaAnalytic (Or.inr hz.ne')]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa [Complex.log_im, Complex.add_im, Complex.mul_im] using this

/-- **Lemma `\ref{lemma:argGamma}` (Lemma 37), on the analytic branch.**
For `-1/2 ≤ δ ≤ 1` and `t > 10`,
`Im logGA(1/2+it/2) - Im logGA(1/2+δ/2+it/2) = -δπ/4 + δ²/(4t) + O^*(0.21/t³)`.

### Summary of Proof
`argGamma_im_diff` gives the exact identity; `argGamma_taylor_residue_sharp` bounds its
non-explicit real part by `0.045/t³`; and `brent_stirling_shifted_remainder_bound` bounds the two
remainder imaginary parts. For both points `‖z‖ ≥ t/2` (their imaginary parts are `t/2`), so each
remainder contributes at most `(1/100)/(t/2)³ = 2/(25t³)`, hence at most `4/(25t³) = 0.16/t³`
together. Total `≤ 0.205/t³ ≤ 0.21/t³`.

### Lean Notes
**Two features of this statement are forced, not stylistic.**

1. **The main term must be `-δπ/4 + δ²/(4t)`, and the `-δπ/4` is a constant.** It is the
   `(a-b)·π/2` contribution to the imaginary part (see `argGamma_im_diff`), so it does not
   vanish as `t → ∞`. A purely `O(1/t)` main term such as `(-δ/2-δ²)/t` would therefore be wrong
   at leading order: in `Code/verify_argGamma.py` sections (A)/(B), at `δ = 1` the true
   difference tends to `-0.7854 = -π/4` while `(-δ/2-δ²)/t → 0`.
2. **`Im logGammaAnalytic`, not `Complex.arg ∘ Complex.Gamma`.** The principal argument wraps;
   see `arg_Gamma_eq_logGammaAnalytic_im_add_int`.

**Where `0.21` comes from.** It is exactly what this proof establishes from Brent's remainder as
stated in `BrentStirlingInputs`: the sharp Taylor residual `0.045/t³` (whose `1/t³` coefficient
is `δ²/12 - δ⁴/24 ≤ 1/24`) plus `2 × 0.08/t³` for the two shifted remainders at `‖z‖ ≥ t/2`. The
tex's Lemma 37 states the same `0.21`. The numerically true supremum is the much smaller
`0.04218`, but that is not reachable from Brent's stated remainder bound.

### References
tex: `\ref{lemma:argGamma}` (Lemma 37).
External: the shifted Stirling series (see `brent_stirling_shifted_expansion`).

**Independent numeric check.**
`Code/indep_mpmath_constants.py` block [E], using mpmath's `loggamma` for the analytic branch:
`sup |residual|·t³ = 0.04218` over `δ ∈ [-1/2,1]`, `t ≥ 10` (attained at `δ = 1`, `t = 10`). So the
bound `0.21/t³` proved here has a factor-5 margin, all of it in the Brent remainder bound: Brent's
true remainder at these points is about `7/2880·8/t³ ≈ 0.019/t³`, and the two remainders largely
cancel. `Code/indep_mpmath_lemma35_constants.py` (Part E) checks `0.045 + 0.16 = 0.205 ≤ 0.21`
and the Taylor coefficient `δ²/12 - δ⁴/24`.

### Dependencies
**Depends on:** `argGamma_im_diff`, `argGamma_taylor_residue_sharp`,
`brent_stirling_shifted_remainder_bound`, `logGammaAnalytic`, `brentShiftedRemainder`.
**Used by:** `argGamma`. -/
theorem argGamma_analytic {δ t : ℝ} (hδ : δ ∈ Set.Icc (-1 / 2 : ℝ) 1) (ht : 10 < t) :
    |(logGammaAnalytic (1 / 2 + t * Complex.I / 2)).im
        - (logGammaAnalytic (1 / 2 + δ / 2 + t * Complex.I / 2)).im
        - (-(δ * Real.pi) / 4 + δ ^ 2 / (4 * t))|
      ≤ 0.21 / t ^ 3 := by
  obtain ⟨hδ1, hδ2⟩ := hδ
  have ht0 : (0 : ℝ) < t := by linarith
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  have hδabs : |δ| ≤ 1 := abs_le.mpr ⟨by linarith, hδ2⟩
  -- the two points of the expansion, and their basic data
  have him0 : (t * Complex.I / 2 : ℂ).im = t / 2 := by simp
  have him1 : ((δ : ℂ) / 2 + t * Complex.I / 2).im = t / 2 := by simp
  have hre0 : (t * Complex.I / 2 : ℂ).re = 0 := by simp
  have hre1 : ((δ : ℂ) / 2 + t * Complex.I / 2).re = δ / 2 := by simp
  have hgt0 : (5 : ℝ) < (t * Complex.I / 2 : ℂ).im := by rw [him0]; linarith
  have hgt1 : (5 : ℝ) < ((δ : ℂ) / 2 + t * Complex.I / 2).im := by rw [him1]; linarith
  have hre0' : |(t * Complex.I / 2 : ℂ).re| ≤ 1 := by rw [hre0]; simp
  have hre1' : |((δ : ℂ) / 2 + t * Complex.I / 2).re| ≤ 1 := by
    rw [hre1, abs_div]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc |δ| / 2 ≤ 1 / 2 := by linarith
      _ ≤ 1 := by norm_num
  -- each remainder's imaginary part is at most 2/(25 t^3)
  have hbound : ∀ w : ℂ, 5 < w.im → |w.re| ≤ 1 → w.im = t / 2 →
      |(brentShiftedRemainder w).im| ≤ 2 / (25 * t ^ 3) := by
    intro w hw hwre hwim
    have h1 : |(brentShiftedRemainder w).im| ≤ ‖brentShiftedRemainder w‖ :=
      Complex.abs_im_le_norm _
    have h2 : ‖brentShiftedRemainder w‖ ≤ 1 / 100 / ‖w‖ ^ 3 :=
      brent_stirling_shifted_remainder_bound hw hwre
    have h3 : t / 2 ≤ ‖w‖ := by
      have := Complex.abs_im_le_norm w
      rw [hwim, abs_of_pos (by linarith)] at this
      exact this
    have h4 : (0 : ℝ) < t / 2 := by linarith
    have hcube : (t / 2) ^ 3 ≤ ‖w‖ ^ 3 := pow_le_pow_left₀ h4.le h3 3
    have hcubepos : (0 : ℝ) < (t / 2) ^ 3 := by positivity
    have hw3 : (0 : ℝ) < ‖w‖ ^ 3 := lt_of_lt_of_le hcubepos hcube
    have hinv : (1 : ℝ) / ‖w‖ ^ 3 ≤ 1 / (t / 2) ^ 3 := one_div_le_one_div_of_le hcubepos hcube
    have h5 : (1 : ℝ) / 100 / ‖w‖ ^ 3 ≤ 2 / (25 * t ^ 3) := by
      have e1 : (1 : ℝ) / 100 / ‖w‖ ^ 3 = 1 / 100 * (1 / ‖w‖ ^ 3) := by ring
      have e2 : (2 : ℝ) / (25 * t ^ 3) = 1 / 100 * (1 / (t / 2) ^ 3) := by field_simp; ring
      rw [e1, e2]
      linarith [hinv]
    linarith [h1, h2, h5]
  have hR0 := hbound (t * Complex.I / 2) hgt0 hre0' him0
  have hR1 := hbound ((δ : ℂ) / 2 + t * Complex.I / 2) hgt1 hre1' him1
  have hres := argGamma_taylor_residue_sharp hδabs ht
  rw [argGamma_im_diff (δ := δ) ht]
  have hkey : -(δ * Real.pi) / 4 + δ / 2 * Real.arctan (δ / t)
      - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2))
      + (brentShiftedRemainder (t * Complex.I / 2)).im
      - (brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im
      - (-(δ * Real.pi) / 4 + δ ^ 2 / (4 * t))
      = (δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
          + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)))
        + ((brentShiftedRemainder (t * Complex.I / 2)).im
          - (brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im) := by
    ring
  rw [hkey]
  have h25 : 2 / (25 * t ^ 3) + 2 / (25 * t ^ 3) + 0.045 / t ^ 3 ≤ 0.21 / t ^ 3 := by
    have e : (2 : ℝ) / (25 * t ^ 3) = (2 / 25) / t ^ 3 := div_mul_eq_div_div 2 25 (t ^ 3)
    rw [e, ← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hRdiff : |(brentShiftedRemainder (t * Complex.I / 2)).im
      - (brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im|
      ≤ 2 / (25 * t ^ 3) + 2 / (25 * t ^ 3) := by
    have := abs_add_le (brentShiftedRemainder (t * Complex.I / 2)).im
      (-(brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im)
    rw [abs_neg] at this
    have hsub : (brentShiftedRemainder (t * Complex.I / 2)).im
        - (brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im
        = (brentShiftedRemainder (t * Complex.I / 2)).im
          + -(brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im := by ring
    rw [hsub]
    linarith [this, hR0, hR1]
  have hsum := abs_add_le
    (δ / 2 * Real.arctan (δ / t) - t / 4 * Real.log (1 + δ ^ 2 / t ^ 2) - δ ^ 2 / (4 * t)
      + δ ^ 2 / (12 * t * (δ ^ 2 + t ^ 2)))
    ((brentShiftedRemainder (t * Complex.I / 2)).im
      - (brentShiftedRemainder ((δ : ℂ) / 2 + t * Complex.I / 2)).im)
  linarith [hsum, hres, hRdiff, h25]

/-- **Lemma `\ref{lemma:argGamma}` (Lemma 37).** For `-1/2 ≤ δ ≤ 1` and `t > 10`,
`Im logGA(1/2+it/2) - Im logGA(1/2+δ/2+it/2) = -δπ/4 + δ²/(4t) + O^*(0.21/t³)`, where `logGA` is
the analytic branch `logGammaAnalytic`.

### Summary of Proof
Definitionally `argGamma_analytic`: imaginary parts of Brent's shifted Stirling expansion at the
two points `1/2 + it/2` and `1/2 + δ/2 + it/2` (`argGamma_im_diff`), Taylor's theorem for the
`arctan`/`log` terms (`argGamma_taylor_residue_sharp`, `≤ 0.045/t³`), and Brent's remainder bound
at both points (`2 × 0.08/t³`).

### Lean Notes
**Why this shape, and not
`arg Γ(1/2+it/2) - arg Γ(1/2+δ/2+it/2) = (-δ/2-δ²)/t + O^*(2/t³)` with the principal
`Complex.arg`.** That form is false, for two independent reasons. Both are recorded here because
both are easy to write by mistake, and neither is visible to the build.

**Reason 1: `(-δ/2-δ²)/t` is the wrong main term.** Writing `D(δ,t)` for the difference of the
two `arg Γ` values on the *continuous* branch, the correct expansion is

    D(δ,t) = -δπ/4 + (δ²/4)/t + O^*(0.043/t³)      (0.043 measured; 0.21 is what is proved),

with the `1/t³` coefficient exactly `δ²/12 - δ⁴/24`. The discrepancy is a constant, `-δπ/4`, so
it does not vanish as `t → ∞`: at `δ = 1`, `D → -π/4 = -0.7854` while `(-δ/2-δ²)/t → 0`.
Measured (`Code/verify_argGamma.py`, section (A)):

    δ = 1:    t = 10.5 → |D - claimed| = 0.6187      t = 10⁴ → 0.7852
    δ = 1/2:  t = 10.5 → 0.3391                      t = 10⁴ → 0.3926

against a claimed bound `2/t³` (`= 0.0017` at `t = 10.5`, `2·10⁻¹²` at `t = 10⁴`). The missing
term is the `(a-b)·π/2` contribution of `Im[(a - 1/2 + it/2)·log(i + 2a/t)]` — with
`a - b = -δ/2` that is exactly `-δπ/4`. No choice of base point rescues it: the constant depends
only on `a - b = -δ/2`, so it is the same for `a = 1/4` as for `a = 1/2`, and any common
prefactor (e.g. `π^{-s/2}`) has `σ`-independent argument and cancels in the difference.
`argGamma_im_diff` is the identity that carries the term.

**Reason 2: `Complex.arg` is the principal branch.** Even with the correct main term, a
principal-argument statement is refuted by branch wrapping: `Complex.arg` has range `(-π, π]`
while `Im log Γ(1/2+it/2) ≈ (t/2)log(t/2)` grows without bound, so the two principal arguments
can receive different multiples of `2π` — for a set of `t` of density `≈ δ/8`. They do **not**
cancel merely because both points lie at the same height. Measured (same script, section (C)) at
`δ = 0.05`, as `t` crosses `10.06`, the principal-argument difference jumps from `-0.0392` to
`+6.2440` while the continuous difference stays at `-0.0392`; a `2/t³ = 0.00196` bound there is
hopeless. The exact relation available is `arg_Gamma_eq_logGammaAnalytic_im_add_int`: equality
only up to an unknown `n·2π`. Brent makes the same point about his own expansion: "`ln Γ(z)` and
`ln(Γ(z))` may differ by a multiple of `2πi`".

Neither refutation is a Lean proof term: that would need `Complex.Gamma` evaluated numerically at
a specific complex point, which neither Mathlib nor this repository can do. The evidence is the
`mpmath` computation named above. Both failures are of the "statement is false" kind, not "proof
is hard". The tex's Lemma 37 states the same main term and the same `0.21/t³`, and writes
`\arg\Gamma` without saying which branch it means. The analytic continuation is the only reading
under which the statement is true, and it is what the tex's own proof computes — that proof takes
imaginary parts of the `\log\Gamma` difference. `argGamma_analytic` records where `0.21` comes
from.

**Containment.** `\ref{lemma:argGamma}` is never `\ref`-ed anywhere in
`ZerosInShortIntervals.tex`, and this Lean theorem is `Used by: none`, so nothing —
in the paper or in the formalization — currently rests on it.

### References
tex: `\ref{lemma:argGamma}` (Lemma 37).
Numerics: `Code/verify_argGamma.py`, `Code/verify_argGamma_main_term.py`,
`Code/indep_mpmath_lemma35_constants.py` (Part E).

### Dependencies
**Depends on:** `argGamma_analytic`, `logGammaAnalytic`.
**Used by:** none. -/
theorem argGamma {δ t : ℝ} (hδ : δ ∈ Set.Icc (-1 / 2 : ℝ) 1) (ht : 10 < t) :
    |(logGammaAnalytic (1 / 2 + t * Complex.I / 2)).im
        - (logGammaAnalytic (1 / 2 + δ / 2 + t * Complex.I / 2)).im
        - (-(δ * Real.pi) / 4 + δ ^ 2 / (4 * t))|
      ≤ 0.21 / t ^ 3 :=
  argGamma_analytic hδ ht
