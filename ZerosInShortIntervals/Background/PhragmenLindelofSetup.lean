/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Common.RealLogBounds
import ZerosInShortIntervals.Background.ExternalFacts

/-! # Shared Phragmén–Lindelöf building blocks (`\S sec:background`)

This file collects the reusable pieces needed to instantiate `fiori_phragmenLindelof`
(Fiori's Theorem 7, doi:10.1016/j.jmaa.2026.130404, available here as
`ExternalFacts.fiori_phragmenLindelof`, a theorem reading the `LiteratureInputs` field of the same
name) for the four `interpolated_bound_*` propositions in `BackgroundZetaBounds.lean`.

**Why the decomposition has the shape it does.** The paper's own worked "Third example" (§4.3) is
the direct source for `interpolated_bound_1a`, but its displayed formula
`|ζ(σ+it)| ≤ (66.7|σ+it|^{27/164})^{w_a}·(1.546|σ+it|^{1/14}|G(σ+it)|)^{w_b}` (with
`G(s)=(1/2)(log(4e+s)+log(4e+2-s))`, `w_a=(b-σ)/(b-a)`, `w_b=(σ-a)/(b-a)`) is *not* literally an
instance of `fiori_phragmenLindelof`'s conclusion for a single `r=1` function `G`: matching the
exact displayed constants forces an **`r=3`** decomposition, which reproduces
`interpolated_bound_1a`'s stated coefficients `47/123-107/246σ` and `14/3(σ-1/2)` exactly (the
resulting linear system is solved and checked in `sympy`):
* `G₁(s) = 66.7^(164/27) · s`, exponents `(α₁,β₁) = (27/164, 0)` — carries *both* the sub-Weyl
  power growth and the `66.7` constant, contributing only at the `σ=1/2` boundary (its `β₁=0`
  kills it at `σ=5/7`). Needs `|G₁|` increasing in `σ` (holds: `α₁>β₁`, `|C·s|` increasing on
  `Re s>0`).
* `G₂(s) = 1.546^14 · (Q'-s)` for any fixed `Q' > 5/7` (e.g. `Q'=1`), exponents
  `(α₂,β₂) = (0, 1/14)` — the mirror image, carrying the Yang power growth and the `1.546`
  constant, contributing only at `σ=5/7`. Needs `|G₂|` decreasing in `σ` (holds: `β₂>α₂`, `|Q'-s|`
  decreasing on `Re s<Q'`).
* `G₃ = GPL 4e`, exponents `(α₃,β₃) = (0,1)` — the log-type function, contributing only at
  `σ=5/7` (matching `log|G(σ+it)|`, i.e. `loglog|t|`, in the target).

A single `G₀ = s` with *both* `(α₀,β₀) = (27/164,1/14)` nonzero (no split) is algebraically
equivalent and reproduces the same `log|t|` coefficient; the split exists *only* to also match the
two separate boundary constants `66.7`,`1.546`, which a single scaled `s` cannot do simultaneously
at both ends, since a single scalar multiple contaminates both exponents.

`interpolated_bound_1b` reuses `G₂,G₃` verbatim but replaces `G₁` (new constant, exponent `1/6`)
and switches `G₃`'s exponents to `(α₃,β₃)=(1,1)` (**equal**, Corollary 3 / Remark 4's device for a
`G` that is not monotone in `σ`, here used deliberately: `|GPL|` is *not* known to be monotone
with the exponent pattern `1b` needs, but equal exponents make `hG_mono` hold vacuously — see
`fiori_phragmenLindelof`'s `hG_mono`, whose two implications are vacuous when `α i = β i`) — which
is also why `1b`'s `loglog|T|` coefficient is the constant `1` (`= w_a+w_b`) rather than `1a`'s
`σ`-dependent `14/3(σ-1/2)` (`= w_b·1`, since `1a` uses `α₃=0`). `interpolated_bound_1c` keeps
`G₂,G₃` as well, but its `σ=1/2` boundary bound is affine in `log|t|`, so its `G₁` is the affine
`G1shift` rather than a scaled `s`, and `G₃` keeps `(α₃,β₃)=(0,1)` with the monotonicity supplied
outright by `GPL_anti_of_large_t`; its `loglog|T|` coefficient is again the flat `1`, this time
because `G₁`'s own `log` contributes `w_a` and `G₃`'s contributes `w_b`. That case has its own
`r=4` family — see the `### Case (1c)` section below.

`interpolated_bound_2` (general `k≥4`, interpolating Yang's bound at consecutive `k,k+1`) uses the
exact same *shape*: `G₁` carries `1.546^(2^k-2)·s` with exponent `1/(2^k-2)` (only at `σ=a_k`),
`G₂` carries `1.546^(2^{k+1}-2)·(Q'-s)` with exponent `1/(2^{k+1}-2)` (only at `σ=b_k`), and
`G₃ = GPL e` with equal exponents `(1,1)`. Solving for the exponents that make the interpolation
match the stated `(1-σ)/(k-1+2^{1-k}) - 1/(2^k(k-1)+2)` coefficient exactly (matching value at
`σ=a_k` and `σ=b_k`) confirms — via `sympy`, checked at `k=4,5,6,7` — that the needed exponents
are `1/(2^k-2)` and `1/(2^{k+1}-2)`, i.e. **exactly** `ExternalFacts.yang_critical_strip_bound`'s
own *exponent* at `k` and at `k+1` respectively — not the `k/(2^k-2)` that appears in the same
statement as the abscissa `σ_k = 1 - k/(2^k-2)`.

**Proved outright here** (so that every `interpolated_bound_*` proof gets them for free):
holomorphy and conjugate symmetry of all three `G` shapes; strict monotonicity in `σ` of the two
*linear* shapes; uniform positive lower bounds for all three on the strip
(`linG_lower_const`/`linGRefl_lower_const`/`GPL_lower_const`); the reduction
`envelope_of_const_lower`, which turns "each `‖Gᵢ‖ ≥` a positive constant" plus "`f` has *some*
two-exponential envelope" into the *shared* `(C1,C2,C3)` envelope `fiori_phragmenLindelof`
demands, and its packaged form `exists_shared_envelope`; the window lemmas
`abs_log_sub_log_le'`/`abs_log_sub_log_le` and `twenty_lt_log`; the reflection
`zeta_norm_abs_im`; the Yang-interval arithmetic (`add_two_lt_two_pow`, `two_lt_two_pow`,
`half_le_sigmaYang`, `sigmaYang_mem_Ioo`, `sigmaYang_lt_succ`) and the coefficient identity
`yang_interp_coeff_eq`; and — the workhorses downstream — the `log`-form bridges
`log_bound_of_interp`, `log_bound_of_interp_1c` and `log_bound_of_interp_self`, which take the
multiplicative conclusion of `fiori_zeta_interpolation`/`fiori_zeta_interpolation_1c` to the
additive, `3/T`-slack form the four `interpolated_bound_*` propositions are stated in.

**This file contains no `sorry` and no `axiom`.** Both facts the source verifies only numerically
are proved outright — the `|t|>T0` monotonicity in `σ` of `‖GPL Q‖` (`GPL_anti_of_large_t`, which
also *corrects* the threshold from `|t|>3` to `|t|>Q+1` and restricts the range to `σ ≤ 1`) and
its `≥ log|t|` lower bound (`GPL_ge_log`, which needs no hypotheses on `σ` or `Q` at all). The
double-exponential envelope for `(s-1)ζ(s)` on each strip (`zeta_envelope`), the remaining input
to the growth hypothesis of `fiori_phragmenLindelof`, is proved too. Downstream, the compact-range
(`|t| ≤ T0`) numeric check each `interpolated_bound_*` needs is a hypothesis rather than a proof:
a field of `BackgroundZetaBounds.InterpolationCertificates` (cases 1a, 1b, 1c) or of
`BackgroundZetaBounds.Hcompact2Certificates` (case 2), each certified outside Lean by ball
arithmetic in `Code/`.

**Why `hG_conj` is scoped to the strip.** `fiori_phragmenLindelof` asks for
`Gᵢ(s̄) = conj(Gᵢ(s))` only for `s.re ∈ Set.Icc a b`, and that restriction is essential for the
log-type `G` the source's own §4 examples use: for `GPL Q` the unrestricted `∀ s : ℂ` form is
false at real `s ≤ -Q`, where `Q+s` sits on `Complex.log`'s branch cut
(`Complex.log(Q+s) = log|Q+s| + iπ`, so a `+iπ/2` term appears which cannot be
conjugation-symmetric at a point where `conj s = s`). The source scopes the condition the same way
(Theorem 1: "… holomorphic for `Re(s) ∈ [a,b]`, have `Gᵢ(s̄) = conj(Gᵢ(s))`"), and its proof of
Lemma 5 only ever evaluates `Gᵢ` inside the strip. The restriction is symmetric in `s` and
`conj s`, since `(conj s).re = s.re`, and `GPL_conj` below discharges it outright. -/

noncomputable section

open Complex

/- The half-line and critical-strip bounds this file instantiates are hypotheses, collected in the
classes `LiteratureInputs` (`ZerosInShortIntervals/Hypotheses.lean`) and `BrentStirlingInputs`
(`Background/ExternalFacts.lean`); nothing here is an `axiom`.

Lean automatically includes an instance-implicit section variable in every *theorem* in scope,
whether or not that theorem's proof reaches it (definitions are not affected).  So the
binders below appear on more statements than strictly need them; each such statement is still
true, merely stated under a hypothesis it does not use.  Precision is recovered where it matters,
on the headline results: see `ZerosInShortIntervals/AllHypotheses.lean`.  The linter that reports
the unused ones is silenced here rather than answered with hundreds of `omit` clauses. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs]

/-- `linG C Q s = C*(Q+s)`: Fiori's "standard choice (2)" `G(s)=(Q+s)` (page 2), scaled by a
positive real constant `C` so that its value at a chosen boundary point can match an arbitrary
target constant.

### Summary of Proof
Entire, hence holomorphic everywhere; `‖linG C Q‖` is strictly increasing in `Re s` on `Re s > -Q`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `exists_shared_envelope`, `fiori_zeta_interpolation`,
`fiori_zeta_interpolation_tight`, `interpG`, `interpG1c`, `interpG1c_prod_α`, `interpG1c_prod_β`,
`interpG_prod_α`, `interpG_prod_β`, `linG_conj`, `linG_holomorphicOn`, `linG_lower_const`,
`linG_mono_of_pos`. -/
def linG (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) + s)

/-- `linGRefl C Q s = C*(Q-s)`: the mirror image of `linG`, per **Remark 6 / §2's first bullet of
Fiori's Phragmén–Lindelöf paper** (`\cite[Remark 6]{Fiori2026}`, "replace `G(s)` with `G(Q'-s)`") —
NOT this project's tex — used where a *decreasing* (in `σ`) linear `G` is needed instead.

### Summary of Proof
`‖linGRefl C Q‖` is strictly decreasing in `Re s` on `Re s < Q`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `linGRefl_holomorphicOn`, `linGRefl_conj`, `linGRefl_anti_of_pos`,
`linGRefl_lower_const`, `interpG`, `interpG1c`, and the four `fiori_zeta_interpolation*`. -/
def linGRefl (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) - s)

/-- `GPL Q s = (1/2)(log(Q+s) + log(Q+2-s))`: the log-type function used in Fiori's "Second" (`Q=e`)
and "Third" (`Q=4e`) worked examples.

### Summary of Proof
A definition, not a theorem. `GPL Q` is the log-type auxiliary function of Fiori's worked examples,
symmetric about `σ = 1`: the two logarithms `log(Q+s)` and `log(Q+2-s)` swap when `s ↦ 2-s`. That
symmetry is what makes `‖GPL‖` monotone in `σ` away from the centre, which is the hypothesis
Phragmén–Lindelöf needs. The source uses `Q = e` in its "Second example" and `Q = 4e` in its
"Third"; this project instantiates at `Q = 4e` (cases 1a and 1c), `Q = 16` (case 1b, chosen large
enough that `GPL 16` clears that case's compact-range check) and `Q = e` (case 2).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `G1shift`, `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`, `GPL_anti_of_large_t`,
`GPL_conj`, `GPL_ge_log`, `GPL_holomorphicOn`, `GPL_im_eq`, `GPL_le_log`, `GPL_le_log_tight`,
`GPL_lower_const`, `GPL_mono_of_large_t`, `GPL_reSq_lt_of_large_t`, `GPL_re_eq`,
`GPL_re_mono_of_large_t`, `exists_shared_envelope`, `fiori_zeta_interpolation`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`,
`fiori_zeta_interpolation_tight`, `interpG`, `interpG1c`, `interpG_prod_α`, `interpG_prod_β`. -/
def GPL (Q : ℝ) : ℂ → ℂ :=
  fun s => (1 / 2) * (Complex.log ((Q : ℂ) + s) + Complex.log ((Q : ℂ) + 2 - s))

/-- `linG C Q` is holomorphic on every vertical strip `Re s ∈ [a,b]`.

### Summary of Proof
No counterpart in `ZerosInShortIntervals.tex`: this is one of the hypothesis checks that
`fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`) demands of each auxiliary function `Gᵢ`.
Immediate, since `linG C Q s = C(Q+s)` is a polynomial, hence entire; the strip is irrelevant.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linG`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linG_holomorphicOn (C Q a b : ℝ) :
    DifferentiableOn ℂ (linG C Q) {s : ℂ | s.re ∈ Set.Icc a b} :=
  (differentiable_const _ |>.mul (differentiable_const _ |>.add differentiable_id)).differentiableOn

/-- `linGRefl C Q` is holomorphic on every vertical strip `Re s ∈ [a,b]`.

### Summary of Proof
The `linGRefl` analogue of `linG_holomorphicOn`; same reasoning (`C(Q-s)` is a polynomial), same
role — a hypothesis check for `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`). No tex
counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linGRefl`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linGRefl_holomorphicOn (C Q a b : ℝ) :
    DifferentiableOn ℂ (linGRefl C Q) {s : ℂ | s.re ∈ Set.Icc a b} :=
  (differentiable_const _ |>.mul
    (differentiable_const _ |>.sub differentiable_id)).differentiableOn

/-- `GPL Q` is holomorphic on the strip `Re s ∈ [a,b]`, given `1 ≤ Q+a` and `1 ≤ Q+2-b`.

### Summary of Proof
The `GPL` analogue of `linG_holomorphicOn`, and the only one of the three needing hypotheses: `GPL
Q s = ½(log(Q+s) + log(Q+2-s))` involves `Complex.log`, so both arguments must stay off the branch
cut. The two hypotheses force `Re(Q+s) ≥ Q+a ≥ 1 > 0` and `Re(Q+2-s) ≥ Q+2-b ≥ 1 > 0` throughout
the strip, which puts both in the right half-plane; `DifferentiableAt.clog` then applies.
(Requiring `≥ 1` rather than `> 0` is slack the call sites can afford and keeps the arithmetic side
conditions trivial.) No tex counterpart — a hypothesis check for `fiori_phragmenLindelof`
(`\cite[Theorem 7]{Fiori2026}`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_holomorphicOn`, the four `fiori_zeta_interpolation*`. -/
theorem GPL_holomorphicOn (Q a b : ℝ) (hQa : 1 ≤ Q + a) (hQb : 1 ≤ Q + 2 - b) :
    DifferentiableOn ℂ (GPL Q) {s : ℂ | s.re ∈ Set.Icc a b} := by
  intro s hs
  simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hs
  have h1 : (0 : ℝ) < ((Q : ℂ) + s).re := by simp; linarith [hs.1]
  have h2 : (0 : ℝ) < ((Q : ℂ) + 2 - s).re := by simp; linarith [hs.2]
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => Complex.log ((Q : ℂ) + w)) s := by
    apply DifferentiableAt.clog (by fun_prop)
    left; exact h1
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.log ((Q : ℂ) + 2 - w)) s := by
    apply DifferentiableAt.clog (by fun_prop)
    left; exact h2
  exact ((hd1.add hd2).const_mul _).differentiableWithinAt

/-- `linG C Q` commutes with complex conjugation: `G(s̄) = conj(G(s))`.

### Summary of Proof
This is the `hG_conj` hypothesis of `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`), which
that theorem needs so the maximum-modulus argument can be run on a half-strip and reflected.
Unconditional here, unlike `GPL_conj` below: `C(Q+s)` has real coefficients, so conjugation passes
straight through. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linG`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linG_conj (C Q : ℝ) (s : ℂ) :
    linG C Q (starRingEnd ℂ s) = starRingEnd ℂ (linG C Q s) := by
  simp [linG, map_add, map_mul]

/-- `linGRefl C Q` commutes with complex conjugation: `G(s̄) = conj(G(s))`.

### Summary of Proof
The `linGRefl` analogue of `linG_conj`, and equally unconditional (`C(Q-s)` again has real
coefficients). Supplies `fiori_phragmenLindelof`'s `hG_conj` hypothesis (`\cite[Theorem
7]{Fiori2026}`). No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linGRefl`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linGRefl_conj (C Q : ℝ) (s : ℂ) :
    linGRefl C Q (starRingEnd ℂ s) = starRingEnd ℂ (linGRefl C Q s) := by
  simp [linGRefl, map_sub, map_mul]

/-- `GPL_conj` proved only within the region where both `Q+s` and `Q+2-s` avoid `Complex.log`'s
branch cut (in particular, on any strip `Re s ∈ [a,b]` with `Q+a>0` and `Q+2-b>0`) — see this
file's module docstring for why the *unrestricted* `∀ s` form is false in general, and why
`fiori_phragmenLindelof` scopes its own `hG_conj` to the strip.

### Summary of Proof
Conjugation passes through each logarithm separately. `Complex.log` commutes with conjugation
exactly off its branch cut, so the two positivity hypotheses `0 < Re(Q+s)` and `0 < Re(Q+2-s)` are
what keep both arguments in the right half-plane and hence off the cut; `Complex.arg_eq_pi_iff`
turns each into the required `arg ≠ π`. The scoping to a region rather than all of `ℂ` is essential
and matches how `ExternalFacts.fiori_phragmenLindelof` states its own `hG_conj` hypothesis.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_conj`, `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `fiori_zeta_interpolation_tight`. -/
theorem GPL_conj (Q : ℝ) (s : ℂ) (h1 : 0 < ((Q : ℂ) + s).re) (h2 : 0 < ((Q : ℂ) + 2 - s).re) :
    GPL Q (starRingEnd ℂ s) = starRingEnd ℂ (GPL Q s) := by
  have e1 : (Q : ℂ) + starRingEnd ℂ s = starRingEnd ℂ ((Q : ℂ) + s) := by
    simp [map_add]
  have e2 : (Q : ℂ) + 2 - starRingEnd ℂ s = starRingEnd ℂ ((Q : ℂ) + 2 - s) := by
    simp [map_sub, map_add, map_ofNat]
  have ha1 : ((Q : ℂ) + s).arg ≠ Real.pi := fun h => by
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  have ha2 : ((Q : ℂ) + 2 - s).arg ≠ Real.pi := fun h => by
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  have half_conj : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  change (1 / 2 : ℂ) * (Complex.log ((Q : ℂ) + starRingEnd ℂ s)
      + Complex.log ((Q : ℂ) + 2 - starRingEnd ℂ s))
    = starRingEnd ℂ ((1 / 2 : ℂ) * (Complex.log ((Q : ℂ) + s) + Complex.log ((Q : ℂ) + 2 - s)))
  rw [e1, e2, Complex.log_conj _ ha1, Complex.log_conj _ ha2, map_mul, map_add, half_conj]

/-- `σ ↦ ‖linG C Q (σ+it)‖` is strictly increasing on `[a,b]`, for `C > 0` and `-Q < a`.

### Summary of Proof
This is the monotonicity `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`) requires of each
`Gᵢ` along the real direction — it is what makes the interpolated bound decrease across the strip.
**Proof.** Write `linG C Q (σ+it) = C(Q+σ) + (Ct)i`, so `‖·‖ = √((C(Q+σ))² + (Ct)²)` with the
imaginary part `Ct` independent of `σ`. The hypotheses give `C(Q+σ) ≥ 0` on `[a,b]` and strict
monotonicity of `σ ↦ C(Q+σ)`, so `gcongr` closes it. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linG`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linG_mono_of_pos (C Q a b : ℝ) (hC : 0 < C) (ha : -Q < a) (t : ℝ) :
    StrictMonoOn (fun σ : ℝ => ‖linG C Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hx' : -Q < x := lt_of_lt_of_le ha hx.1
  have key : ∀ σ : ℝ,
      linG C Q (σ + t * Complex.I) = (C * (Q + σ) : ℝ) + (C * t : ℝ) * Complex.I := by
    intro σ
    simp only [linG]
    push_cast
    ring
  simp only [key, Complex.norm_add_mul_I]
  have h0 : 0 ≤ C * (Q + x) := by nlinarith
  have h1 : C * (Q + x) < C * (Q + y) := by nlinarith
  gcongr

/-- `σ ↦ ‖linGRefl C Q (σ+it)‖` is strictly *decreasing* on `[a,b]`, for `C > 0` and `b < Q`.

### Summary of Proof
The mirror of `linG_mono_of_pos`, and the reason `linGRefl` exists: `fiori_phragmenLindelof`
(`\cite[Theorem 7]{Fiori2026}`) is applied with a family of `Gᵢ` of *both* monotonicity senses, so
that the interpolation can be pinned at either end of the strip. **Proof.** Same shape as
`linG_mono_of_pos`: `linGRefl C Q (σ+it) = C(Q-σ) + (-Ct)i`, the imaginary part is `σ`-independent,
and `hb : b < Q` gives `C(Q-σ) ≥ 0` on `[a,b]` with `σ ↦ C(Q-σ)` strictly decreasing. No tex
counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linGRefl`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linGRefl_anti_of_pos (C Q a b : ℝ) (hC : 0 < C) (hb : b < Q) (t : ℝ) :
    StrictAntiOn (fun σ : ℝ => ‖linGRefl C Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hy' : y < Q := lt_of_le_of_lt hy.2 hb
  have key : ∀ σ : ℝ,
      linGRefl C Q (σ + t * Complex.I) = (C * (Q - σ) : ℝ) + (-(C * t) : ℝ) * Complex.I := by
    intro σ
    simp only [linGRefl]
    push_cast
    ring
  simp only [key, Complex.norm_add_mul_I]
  have h0 : 0 ≤ C * (Q - y) := by nlinarith
  have h1 : C * (Q - y) < C * (Q - x) := by nlinarith
  gcongr

/-! ### `Re`, `Im` and monotonicity of `GPL`

Both facts the source verifies numerically — that `‖GPL Q(σ+it)‖` decreases in `σ` for large `|t|`,
and that it is at least `log|t|` — are proved here in closed form. Writing `A = Q+σ`, `B = Q+2-σ`
(so `A+B = 2Q+2` is independent of `σ`, `AB = (Q+1)² - (1-σ)²`, and `B-A = 2(1-σ)`):

  `Re GPL Q(σ+it) = ¼(log(A²+t²) + log(B²+t²))`,
  `Im GPL Q(σ+it) = ½(arctan(t/A) - arctan(t/B))`.

`GPL_ge_log` is then immediate from `‖z‖ ≥ Re z` and `A²+t², B²+t² ≥ t²`. For
`GPL_anti_of_large_t`, both `Re` and `|Im|` are shown to decrease in `σ` on `σ ≤ 1`. -/

/-- Squaring preserves `≤` on the nonnegatives: `0 ≤ u ≤ v` gives `u² ≤ v²`.

### Summary of Proof
Discharged by `nlinarith`. No tex counterpart — arithmetic plumbing for the `GPL` monotonicity
proofs, where `Re GPL` is compared through squares of `A = Q+σ` and `B = Q+2-σ`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem sq_le_sq_of_nonneg {u v : ℝ} (h1 : 0 ≤ u) (h2 : u ≤ v) : u^2 ≤ v^2 := by nlinarith

/-- The nonpositive mirror of `sq_le_sq_of_nonneg`: `v ≤ u ≤ 0` gives `u² ≤ v²`.

### Summary of Proof
Squaring reverses the order below `0`, so the hypothesis is `v ≤ u` rather than `u ≤ v`. Both signs
are needed because `B - A = 2(1-σ)` changes sign as `σ` crosses `1`. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem sq_le_sq_of_nonpos {u v : ℝ} (h1 : u ≤ 0) (h2 : v ≤ u) : u^2 ≤ v^2 := by nlinarith

/-- `t/d ≤ t/c` for `0 ≤ t` and `0 < c ≤ d`: enlarging a positive denominator shrinks a nonnegative
quotient.

### Summary of Proof
Proved by clearing denominators with `div_le_div_iff₀`. No tex counterpart — used on the
`arctan(t/A)` arguments, where `A` grows with `σ`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem div_antitone_of_nonneg {t c d : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hd : 0 < d)
    (h : c ≤ d) : t / d ≤ t / c := by
  rw [div_le_div_iff₀ hd hc]; nlinarith

/-- The `t ≤ 0` mirror of `div_antitone_of_nonneg`: for a nonpositive numerator the inequality
flips,
`t/c ≤ t/d`.

### Summary of Proof
Paired with it so the `Im GPL` estimates hold for both signs of `t`. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem div_monotone_of_nonpos {t c d : ℝ} (ht : t ≤ 0) (hc : 0 < c) (hd : 0 < d)
    (h : c ≤ d) : t / c ≤ t / d := by
  rw [div_le_div_iff₀ hc hd]; nlinarith

/-- `arg z = arctan(Im z/Re z)` in the right half-plane (from `Complex.tan_arg` and
`Real.arctan_tan`, valid because `|arg z| < π/2` there).

### Summary of Proof
In the open right half-plane `arg z` lies in `(-π/2, π/2)`, by `Complex.abs_arg_lt_pi_div_two_iff`.
On that range `arctan` inverts `tan`, so rewriting `Complex.tan_arg` and applying `Real.arctan_tan`
gives the closed form.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_im_eq`. -/
private theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at h
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- `‖z‖ = √((Re z)² + (Im z)²)` — the real-coordinate form of the complex modulus. Obtained by
rewriting `z` as `Re z + (Im z)i` (`Complex.re_add_im`) and applying `Complex.norm_add_mul_I`.

### Summary of Proof
Mathlib states the modulus via `Complex.abs`/`normSq`; this spelling is what the `nlinarith` calls
in the `GPL` estimates need, since they reason about `Re` and `Im` as independent reals. No tex
counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_le_log_tight`, `GPL_mono_of_large_t`,
`normSq_c_mul_add_d`. -/
private theorem norm_eq_sqrt (z : ℂ) : ‖z‖ = Real.sqrt (z.re^2 + z.im^2) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.norm_add_mul_I]

/-- `Re GPL Q(σ+it) = ¼(log((Q+σ)²+t²) + log((Q+2-σ)²+t²))` — `Complex.log_re` plus `log√u = ½log
u`.

### Summary of Proof
No hypotheses: `(Complex.log z).re = log‖z‖` holds unconditionally.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_ge`, `GPL_anti_of_large_t`, `GPL_le_log`, `GPL_le_log_tight`,
`GPL_reSq_lt_of_large_t`, `GPL_re_mono_of_large_t`. -/
theorem GPL_re_eq (Q σ t : ℝ) :
    (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = (1/4) * (Real.log ((Q+σ)^2 + t^2) + Real.log ((Q+2-σ)^2 + t^2)) := by
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hs1 : Real.log ‖((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I‖
      = (1/2) * Real.log ((Q+σ)^2 + t^2) := by
    rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]
    ring
  have hs2 : Real.log ‖((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
      = (1/2) * Real.log ((Q+2-σ)^2 + t^2) := by
    rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]
    ring_nf
  simp only [GPL, Complex.mul_re, Complex.add_re, Complex.log_re]
  rw [e1, e2, hs1, hs2]
  norm_num
  ring

/-- `Im GPL Q(σ+it) = ½(arctan(t/(Q+σ)) - arctan(t/(Q+2-σ)))`, valid where both factors lie in the
right half-plane.

### Summary of Proof
Split `GPL` into its two logarithms and take imaginary parts. Writing each argument in the form `x
+ yi` with `x > 0` puts it in the right half-plane, where `arg_eq_arctan` applies; the second
logarithm's argument is `(Q+2-σ) - ti`, contributing `arctan(-t/(Q+2-σ)) = -arctan(t/(Q+2-σ))`. The
overall factor `1/2` from `GPL`'s definition gives the stated form.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `arg_eq_arctan`.
**Used by:** `GPL_anti_of_large_t`, `GPL_le_log`, `GPL_le_log_tight`, `GPL_mono_of_large_t`. -/
theorem GPL_im_eq (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) :
    (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im
      = (1/2) * (Real.arctan (t / (Q + σ)) - Real.arctan (t / (Q + 2 - σ))) := by
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have ha1 : (((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I).arg = Real.arctan (t / (Q + σ)) := by
    rw [arg_eq_arctan (by simpa using h1)]
    congr 1; simp
  have ha2 : (((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).arg
      = Real.arctan (-(t / (Q + 2 - σ))) := by
    rw [arg_eq_arctan (by simpa using h2)]
    congr 1
    simp
    ring
  simp only [GPL, Complex.mul_im, Complex.add_im, Complex.log_im]
  rw [e1, e2, ha1, ha2, Real.arctan_neg]
  norm_num
  ring

/-- **`‖GPL Q(σ+it)‖` is strictly decreasing in `σ` on any `[a,b]` with `b ≤ 1`, once
`|t| > Q+1`.** The source verifies this numerically; it is proved here in closed form.

### Summary of Proof
**Correction to the source: the threshold `|t| > 3` it uses (§4.2's "for `t≥3` and `0<σ<2`",
§4.3's "for `σ∈[1/2,5/7]` and `t≥3`") is not enough, and the range must stop at `σ = 1`.** Writing
`A = Q+σ`, `B = Q+2-σ`, `v = 1-σ`, the two components are `Re = ¼log((A²+t²)(B²+t²))` and `Im =
½(arctan(t/A) - arctan(t/B))`, and since `A+B = 2Q+2` is independent of `σ`, `(A²+t²)(B²+t²) =
(AB)² - 2t²(AB) + t²(2Q+2)² + t⁴` with `AB = (Q+1)² - v²`. So `Re` is a decreasing function of `AB`
exactly when `t² > AB`, and `AB` increases as `σ ↑ 1`; hence `Re` decreases in `σ` iff `σ < 1` and
`t² > AB`, for which `|t| > Q+1 ≥ √(AB)` is sufficient. `|Im|` decreases in `σ` on `σ ≤ 1` with no
condition on `t`. **Both halves of this are needed.** *Symmetry about `σ = 1`*: `‖GPL Q(σ+it)‖`
depends on `σ` only through `|1-σ|`, so it is *increasing* for `σ > 1` — the source's `0 < σ < 2`
straddles the minimum and cannot give a monotone statement. *The threshold*: at `Q = 4e` (the
`\S4.3` example, used by `BackgroundZetaBounds.interpolated_bound_1a`) and `σ ∈ [1/2,5/7]`, `‖GPL‖`
is genuinely **increasing** in `σ` for `|t| ≲ 10.2` — e.g. at `t = 3` it goes from `2.504520` at
`σ=1/2` up to `2.505007` at `σ=5/7`. The sufficient bound proved here, `|t| > Q+1 = 11.874…`, is
safe; only `interpolated_bound_1a` (`ra = 0 < rb = 1`) actually needs the monotonicity, and there
the compact range handled separately has to grow from `|t| ≤ 3` to `|t| ≤ Q+1` accordingly.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_re_eq`, `div_antitone_of_nonneg`,
`div_monotone_of_nonpos`, `norm_eq_sqrt`, `sq_le_sq_of_nonneg`, `sq_le_sq_of_nonpos`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1c`,
`interpolated_bound_1c_tight`. -/
theorem GPL_anti_of_large_t (Q a b : ℝ) (hQ : 0 ≤ Q) (hQa : 0 < Q + a) (hb : b ≤ 1) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictAntiOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t htQ x hx y hy hxy
  have hQ0 : (0:ℝ) ≤ Q + 1 := by linarith
  have ht2 : (Q+1)^2 < t^2 := by
    calc (Q+1)^2 < |t|^2 := by nlinarith [htQ, hQ0]
      _ = t^2 := sq_abs t
  have hQ1 : (1:ℝ) ≤ (Q+1)^2 := by nlinarith
  have hy1 : y ≤ 1 := le_trans hy.2 hb
  have hx1 : x < 1 := lt_of_lt_of_le hxy hy1
  have hpx1 : 0 < Q + x := lt_of_lt_of_le hQa (by linarith [hx.1])
  have hpy1 : 0 < Q + y := lt_of_lt_of_le hQa (by linarith [hy.1])
  have hpx2 : 0 < Q + 2 - x := by linarith
  have hpy2 : 0 < Q + 2 - y := by linarith
  -- ** the `Re` comparison **
  have hAB : (Q+x)*(Q+2-x) - (Q+y)*(Q+2-y) < 0 := by
    nlinarith [mul_pos (show (0:ℝ) < y - x by linarith) (show (0:ℝ) < 2 - x - y by linarith)]
  have hABle : (Q+x)*(Q+2-x) + (Q+y)*(Q+2-y) - 2*t^2 < 0 := by
    nlinarith [sq_nonneg (1-x), sq_nonneg (1-y), ht2]
  have hprod : ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2) < ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2) := by
    have key : ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2) - ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2)
        = ((Q+x)*(Q+2-x) - (Q+y)*(Q+2-y))
          * ((Q+x)*(Q+2-x) + (Q+y)*(Q+2-y) - 2*t^2) := by ring
    have hDE := mul_pos_of_neg_of_neg hAB hABle
    linarith [key, hDE]
  have hlogx : Real.log ((Q+y)^2+t^2) + Real.log ((Q+2-y)^2+t^2)
      < Real.log ((Q+x)^2+t^2) + Real.log ((Q+2-x)^2+t^2) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_lt_log (by positivity) hprod
  have hReypos : 0 ≤ Real.log ((Q+y)^2+t^2) + Real.log ((Q+2-y)^2+t^2) := by
    have h1 : (1:ℝ) ≤ (Q+y)^2+t^2 := by nlinarith [sq_nonneg (Q+y)]
    have h2 : (1:ℝ) ≤ (Q+2-y)^2+t^2 := by nlinarith [sq_nonneg (Q+2-y)]
    linarith [Real.log_nonneg h1, Real.log_nonneg h2]
  have hReSq : (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re ^ 2
      < (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re ^ 2 := by
    rw [GPL_re_eq, GPL_re_eq]
    nlinarith [hlogx, hReypos]
  -- ** the `Im` comparison **
  have hImsq : ((GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).im)^2
      ≤ ((GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).im)^2 := by
    rw [GPL_im_eq Q x t hpx1 hpx2, GPL_im_eq Q y t hpy1 hpy2]
    rcases le_or_gt 0 t with htp | htn
    · have m1 : t / (Q + y) ≤ t / (Q + x) :=
        div_antitone_of_nonneg htp hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - x) ≤ t / (Q + 2 - y) :=
        div_antitone_of_nonneg htp hpy2 hpx2 (by linarith)
      have m3 : t / (Q + 2 - y) ≤ t / (Q + y) :=
        div_antitone_of_nonneg htp hpy1 hpy2 (by linarith)
      refine sq_le_sq_of_nonneg ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
    · have m1 : t / (Q + x) ≤ t / (Q + y) :=
        div_monotone_of_nonpos htn.le hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - y) ≤ t / (Q + 2 - x) :=
        div_monotone_of_nonpos htn.le hpy2 hpx2 (by linarith)
      have m3 : t / (Q + y) ≤ t / (Q + 2 - y) :=
        div_monotone_of_nonpos htn.le hpy1 hpy2 (by linarith)
      refine sq_le_sq_of_nonpos ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
  -- ** combine **
  simp only
  rw [norm_eq_sqrt, norm_eq_sqrt]
  apply Real.sqrt_lt_sqrt (by positivity)
  exact add_lt_add_of_lt_of_le hReSq hImsq

/-- **Shared `Re`-comparison step for `GPL_mono_of_large_t`/`GPL_re_mono_of_large_t`.** Extracted
since both the norm- and the bare-`Re`-monotonicity statements for `σ ≥ 1` need exactly this.

### Summary of Proof
The shared `Re`-comparison step behind both monotonicity lemmas. `Re GPL` is `½(log‖Q+s‖ +
log‖Q+2-s‖)`, so comparing at `x < y` reduces to comparing `((Q+x)²+t²)((Q+2-x)²+t²)` against the
same at `y`. Expanding, the difference is governed by `t²` against the `σ`-dependent quadratic
terms, so the hypothesis `Q+1 < |t|` is exactly what makes the `t²` term dominate and fixes the
sign.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_re_eq`.
**Used by:** `GPL_mono_of_large_t`, `GPL_re_mono_of_large_t`. -/
private theorem GPL_reSq_lt_of_large_t {Q a b x y t : ℝ} (hQ : 0 ≤ Q) (ha : 1 ≤ a)
    (_hQb : 0 < Q + 2 - b) (htQ : Q + 1 < |t|) (hx : x ∈ Set.Icc a b) (_hy : y ∈ Set.Icc a b)
    (hxy : x < y) :
    (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re ^ 2 < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re ^ 2 := by
  have hQ0 : (0:ℝ) ≤ Q + 1 := by linarith
  have ht2 : (Q+1)^2 < t^2 := by
    calc (Q+1)^2 < |t|^2 := by nlinarith [htQ, hQ0]
      _ = t^2 := sq_abs t
  have hQ1 : (1:ℝ) ≤ (Q+1)^2 := by nlinarith
  have ht0 : (0:ℝ) < t^2 := by linarith
  have hx1 : (1:ℝ) ≤ x := le_trans ha hx.1
  have hy1 : (1:ℝ) < y := lt_of_le_of_lt hx1 hxy
  have hAB : (0:ℝ) < (Q+x)*(Q+2-x) - (Q+y)*(Q+2-y) := by
    nlinarith [mul_pos (show (0:ℝ) < y - x by linarith) (show (0:ℝ) < x + y - 2 by linarith)]
  have hABle : (Q+x)*(Q+2-x) + (Q+y)*(Q+2-y) - 2*t^2 < 0 := by
    nlinarith [sq_nonneg (1-x), sq_nonneg (1-y), ht2]
  have hprod : ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2) < ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2) := by
    have key : ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2) - ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2)
        = ((Q+x)*(Q+2-x) - (Q+y)*(Q+2-y))
          * (2*t^2 - ((Q+x)*(Q+2-x) + (Q+y)*(Q+2-y))) := by ring
    have hDE := mul_pos hAB (by linarith : (0:ℝ) < 2*t^2 - ((Q+x)*(Q+2-x) + (Q+y)*(Q+2-y)))
    linarith [key, hDE]
  have hne1 : ((Q+x)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne2 : ((Q+2-x)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne3 : ((Q+y)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne4 : ((Q+2-y)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hlogx : Real.log ((Q+x)^2+t^2) + Real.log ((Q+2-x)^2+t^2)
      < Real.log ((Q+y)^2+t^2) + Real.log ((Q+2-y)^2+t^2) := by
    rw [← Real.log_mul hne1 hne2, ← Real.log_mul hne3 hne4]
    exact Real.log_lt_log (by positivity) hprod
  have hRexpos : 0 ≤ Real.log ((Q+x)^2+t^2) + Real.log ((Q+2-x)^2+t^2) := by
    have h1 : (1:ℝ) ≤ (Q+x)^2+t^2 := by nlinarith [sq_nonneg (Q+x)]
    have h2 : (1:ℝ) ≤ (Q+2-x)^2+t^2 := by nlinarith [sq_nonneg (Q+2-x)]
    linarith [Real.log_nonneg h1, Real.log_nonneg h2]
  rw [GPL_re_eq, GPL_re_eq]
  nlinarith [hlogx, hRexpos]

/-- **`‖GPL Q(σ+it)‖` is strictly increasing in `σ` on any `[a,b]` with `1 ≤ a`, once `|t| > Q+1`.**
The mirror of `GPL_anti_of_large_t` on the other side of the symmetry point `σ = 1`: the `Im`
comparison carries over with only the sign of the bracket flipped (it uses just that `Q+σ`
increases and `Q+2-σ` decreases in `σ`, true on both sides of `1`), while the `Re` comparison
reverses, since `AB = (Q+1)²-(1-σ)²` now *decreases* in `σ` (as `(1-σ)² = (σ-1)²` increases for
`σ ≥ 1`) instead of increasing.

### Summary of Proof
Compare the two components separately and recombine through `norm_eq_sqrt`: the squared norm is
`(Re)² + (Im)²`, so it suffices that `(Re)²` strictly increase while `(Im)²` does not decrease.
The `Re` half is `GPL_reSq_lt_of_large_t`, which is where `Q+1 < |t|` is used. The `Im` half
rewrites both sides with `GPL_im_eq` and compares the two `arctan` arguments monotonically
(`div_antitone_of_nonneg`/`div_monotone_of_nonpos` and `Real.arctan_mono`), the sign of the
bracket `arctan(t/(Q+σ)) - arctan(t/(Q+2-σ))` selecting `sq_le_sq_of_nonneg` or
`sq_le_sq_of_nonpos`; `Real.sqrt_lt_sqrt` transfers the strict inequality back to the norms.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_reSq_lt_of_large_t`, `div_antitone_of_nonneg`,
`div_monotone_of_nonpos`, `norm_eq_sqrt`, `sq_le_sq_of_nonneg`, `sq_le_sq_of_nonpos`.
**Used by:** `G1shift_mono_of_large_t`. -/
theorem GPL_mono_of_large_t (Q a b : ℝ) (hQ : 0 ≤ Q) (ha : 1 ≤ a) (hQb : 0 < Q + 2 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t htQ x hx y hy hxy
  have hx1 : (1:ℝ) ≤ x := le_trans ha hx.1
  have hy1 : (1:ℝ) < y := lt_of_le_of_lt hx1 hxy
  have hpx1 : 0 < Q + x := by linarith
  have hpy1 : 0 < Q + y := by linarith
  have hpx2 : 0 < Q + 2 - x := lt_of_lt_of_le hQb (by linarith [hx.2])
  have hpy2 : 0 < Q + 2 - y := lt_of_lt_of_le hQb (by linarith [hy.2])
  have hReSq := GPL_reSq_lt_of_large_t (Q := Q) (a := a) (b := b) hQ ha hQb htQ hx hy hxy
  -- ** the `Im` comparison.** The monotonicity of the two `arctan` arguments (`Q+σ` increasing,
  -- `Q+2-σ` decreasing in `σ`) is the same on both sides of `1`, but which side of `0` the
  -- bracket `arctan(t/(Q+σ))-arctan(t/(Q+2-σ))` sits on *flips* for `σ ≥ 1` versus `σ ≤ 1`
  -- (at `σ = 1` the bracket is exactly `0`; for `σ ≥ 1`, `Q+2-σ ≤ Q+σ`, the opposite ordering
  -- from the `σ ≤ 1` case), so the `t ≥ 0`/`t < 0` branches swap which `sq_le_sq_of_*` applies.
  have hImsq : ((GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).im)^2
      ≤ ((GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).im)^2 := by
    rw [GPL_im_eq Q x t hpx1 hpx2, GPL_im_eq Q y t hpy1 hpy2]
    rcases le_or_gt 0 t with htp | htn
    · have m1 : t / (Q + y) ≤ t / (Q + x) :=
        div_antitone_of_nonneg htp hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - x) ≤ t / (Q + 2 - y) :=
        div_antitone_of_nonneg htp hpy2 hpx2 (by linarith)
      have m3 : t / (Q + x) ≤ t / (Q + 2 - x) :=
        div_antitone_of_nonneg htp hpx2 hpx1 (by linarith [hx1])
      refine sq_le_sq_of_nonpos ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
    · have m1 : t / (Q + x) ≤ t / (Q + y) :=
        div_monotone_of_nonpos htn.le hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - y) ≤ t / (Q + 2 - x) :=
        div_monotone_of_nonpos htn.le hpy2 hpx2 (by linarith)
      have m3 : t / (Q + 2 - x) ≤ t / (Q + x) :=
        div_monotone_of_nonpos htn.le hpx2 hpx1 (by linarith [hx1])
      refine sq_le_sq_of_nonneg ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
  -- ** combine **
  simp only
  rw [norm_eq_sqrt, norm_eq_sqrt]
  apply Real.sqrt_lt_sqrt (by positivity)
  exact add_lt_add_of_lt_of_le hReSq hImsq

/-- **`‖GPL Q(σ+it)‖ ≥ log|t|` for `1 ≤ |t|`.** The source verifies this numerically; it is proved
here in closed form, and needs **no** hypotheses on `σ` or `Q` at all (the source's `0<σ<2` and
`t≥3` are both unnecessary).

### Summary of Proof
Along the author's own suggested line: `Re log z = log‖z‖`, so `‖GPL Q(σ+it)‖ ≥ Re GPL Q(σ+it) =
½(log‖(Q+σ)+it‖ + log‖(Q+2-σ)-it‖) ≥ ½(log|t| + log|t|)`, each norm being `√(·² + t²) ≥ |t|`.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`, `interpolated_bound_1c`, `interpolated_bound_1c_tight`,
`interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem GPL_ge_log (Q a b : ℝ) (t : ℝ) (ht : 1 ≤ |t|) :
    ∀ σ ∈ Set.Icc a b, Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖ := by
  intro σ _
  have ht0 : (0:ℝ) < |t| := by linarith
  -- the two factors, in `x + y*I` form
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hn1 : |t| ≤ ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [e1, Complex.norm_add_mul_I]
    rw [show |t| = Real.sqrt (t^2) from (Real.sqrt_sq_eq_abs t).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Q + σ)]
  have hn2 : |t| ≤ ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [e2, Complex.norm_add_mul_I]
    rw [show |t| = Real.sqrt (t^2) from (Real.sqrt_sq_eq_abs t).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Q + 2 - σ)]
  have hl1 : Real.log |t| ≤ Real.log ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖ :=
    Real.log_le_log ht0 hn1
  have hl2 : Real.log |t| ≤ Real.log ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ :=
    Real.log_le_log ht0 hn2
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = (1/2) * (Real.log ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖
        + Real.log ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖) := by
    simp [GPL, Complex.add_re, Complex.log_re, Complex.mul_re]
  have hle := Complex.re_le_norm (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I))
  rw [hre] at hle
  linarith

/-- **`(GPL Q(σ+it)).re` is strictly increasing in `σ` on `[a,b]` with `1 ≤ a`, once `|t| > Q+1`.**
From `GPL_reSq_lt_of_large_t` (`Re²` increasing) plus positivity of `Re` there
(`Re ≥ log|t| > 0`, since `|t| > Q+1 ≥ 1`), which lets `Re²` increasing upgrade to `Re` itself
increasing.

### Summary of Proof
The real-part-only version, needed where Phragmén–Lindelöf's monotonicity hypothesis is stated on
`Re G` rather than `‖G‖`. Immediate from `GPL_reSq_lt_of_large_t` once one knows `Re GPL ≥ log|t| >
0`, since squaring is strictly monotone on the positives.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_reSq_lt_of_large_t`, `GPL_re_eq`.
**Used by:** `G1shift_mono_of_large_t`. -/
theorem GPL_re_mono_of_large_t (Q a b : ℝ) (hQ : 0 ≤ Q) (ha : 1 ≤ a) (hQb : 0 < Q + 2 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => (GPL Q (σ + t * Complex.I)).re) (Set.Icc a b) := by
  intro t htQ x hx y hy hxy
  have hReSq := GPL_reSq_lt_of_large_t (Q := Q) (a := a) (b := b) hQ ha hQb htQ hx hy hxy
  have ht1 : (1:ℝ) < |t| := by linarith
  have hlogpos : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have hgre : ∀ σ : ℝ, Real.log |t| ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    intro σ
    rw [GPL_re_eq]
    have h1 : t ^ 2 ≤ (Q + σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + σ)]
    have h2 : t ^ 2 ≤ (Q + 2 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - σ)]
    have ht0 : (0:ℝ) < t ^ 2 := by nlinarith [sq_abs t]
    have hlt : Real.log (t^2) ≤ Real.log ((Q + σ) ^ 2 + t ^ 2) := Real.log_le_log ht0 h1
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - σ) ^ 2 + t ^ 2) := Real.log_le_log ht0 h2
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  have hrex : 0 < (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re := lt_of_lt_of_le hlogpos (hgre x)
  have hrey : 0 < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re := lt_of_lt_of_le hlogpos (hgre y)
  change (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re
  nlinarith [hReSq, hrex, hrey]

/-- `arctan` is `1`-Lipschitz: `|arctan x - arctan y| ≤ |x - y|`.

### Summary of Proof
**Proof.** `arctan' z = 1/(1+z²)`, whose norm is at most `1` everywhere since `z² ≥ 0`; the mean
value inequality on the (convex) whole line, in the form
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, converts that derivative bound into the
Lipschitz estimate. No tex counterpart — Fiori's paper uses the Lipschitz property of `arctan`
implicitly. Note this naive bound is *not* enough for `GPL_le_log_tight` on its own: applied
directly to `arctan(t/A) - arctan(t/B)` it gives `|t||B-A|/(AB)`, which grows with `|t|`. It
becomes useful only after `arctan_div_swap` inverts the arguments.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_le_log`, `GPL_le_log_tight`. -/
private theorem abs_arctan_sub_arctan_le (x y : ℝ) :
    |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  have hd : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.arctan (1 / (1 + z^2)) Set.univ z :=
    fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt
  have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖(1 : ℝ) / (1 + z^2)‖ ≤ 1 := by
    intro z _
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg z]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- **The argument-inversion identity that makes the `Im GPL` bound useful.**
`arctan(t/A) - arctan(t/B) = arctan(B/t) - arctan(A/t)` for `A, B > 0` and `t ≠ 0`.

### Summary of Proof
**Proof.** `t/A = (A/t)⁻¹`, and `arctan x⁻¹ = ±π/2 - arctan x` (`Real.arctan_inv_of_pos` /
`Real.arctan_inv_of_neg` according to the sign of `t`). The two `±π/2` terms cancel in the
difference, leaving the swapped form. The case split on `sign t` is exactly why both `arctan_inv`
lemmas appear. **Why it matters.** The naive Lipschitz bound on the left-hand side is
`|t||B-A|/(AB)`, which *grows* with `|t|` and so is worthless for the large-`|t|` regime the
interpolation needs. On the right-hand side the same Lipschitz bound gives `|B-A|/|t|`, which
decays. This swap is what turns the `Im` contribution into an `O(1/|t|)` error term. No tex
counterpart — the source performs the estimate without naming the step.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_le_log`, `GPL_le_log_tight`. -/
private theorem arctan_div_swap {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht : t ≠ 0) :
    Real.arctan (t / A) - Real.arctan (t / B)
      = Real.arctan (B / t) - Real.arctan (A / t) := by
  have hA' : t / A = (A / t)⁻¹ := by field_simp
  have hB' : t / B = (B / t)⁻¹ := by field_simp
  rcases lt_or_gt_of_ne ht with h | h
  · rw [hA', hB', Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hA h),
      Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hB h)]; ring
  · rw [hA', hB', Real.arctan_inv_of_pos (div_pos hA h),
      Real.arctan_inv_of_pos (div_pos hB h)]; ring

/-- **Upper counterpart of `GPL_ge_log`**: `‖GPL Q(σ+it)‖ ≤ log|t| + (A²+B²)/(4t²) + |B-A|/(2|t|)`
for `|t| ≥ 1`, where `A = Q+σ`, `B = Q+2-σ`. This is the missing half of Fiori's `Cᵢ(t₀) → 1`
bookkeeping (§4.1): together with `GPL_ge_log` it pins `‖GPL Q(σ+it)‖` between `log|t|` and
`(1+ε)log|t|` with an explicit `ε = O(1/(|t|log|t|))`.

### Summary of Proof
`Re` is bounded by `log(1+x) ≤ x` applied to `(A²+t²)/t²`. For `Im` the naive Lipschitz bound
`|arctan(t/A) - arctan(t/B)| ≤ |t||B-A|/(AB)` is useless (it *grows* with `|t|`); the fix is
`arctan(t/A) - arctan(t/B) = arctan(B/t) - arctan(A/t)` (`arctan_div_swap`, from
`Real.arctan_inv_of_pos`/`_of_neg` — it holds for **both** signs of `t`), after which
1-Lipschitzness gives the correct `|B-A|/|t|`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_re_eq`, `abs_arctan_sub_arctan_le`, `arctan_div_swap`.
**Used by:** `G1shift_le`, `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
theorem GPL_le_log (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) (ht : 1 ≤ |t|) :
    ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) + |2 - 2*σ| / (2 * |t|) := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have ht2 : (1:ℝ) ≤ t^2 := by nlinarith [sq_abs t]
  have habs2 : |t|^2 = t^2 := sq_abs t
  -- real part
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) := by
    rw [GPL_re_eq]
    have key : ∀ C : ℝ, Real.log (C^2 + t^2) ≤ 2 * Real.log |t| + C^2 / t^2 := by
      intro C
      have hlog : Real.log (C^2 + t^2) = Real.log (t^2) + Real.log (1 + C^2/t^2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      have h2t : Real.log (t^2) = 2 * Real.log |t| := by
        rw [← habs2, Real.log_pow]
        push_cast; ring
      have hb : Real.log (1 + C^2/t^2) ≤ C^2/t^2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + C^2/t^2 by positivity)
        linarith
      rw [hlog, h2t]; linarith
    have k1 := key (Q+σ)
    have k2 := key (Q+2-σ)
    have hpos : (0:ℝ) < t^2 := by linarith
    have he : ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)
        = (1/4) * ((Q+σ)^2/t^2 + (Q+2-σ)^2/t^2) := by field_simp
    rw [he]
    linarith [k1, k2]
  -- imaginary part
  have him : |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| ≤ |2 - 2*σ| / (2 * |t|) := by
    rw [GPL_im_eq Q σ t h1 h2, arctan_div_swap h1 h2 htne, abs_mul]
    have h := abs_arctan_sub_arctan_le ((Q+2-σ)/t) ((Q+σ)/t)
    have heq : (Q+2-σ)/t - (Q+σ)/t = (2 - 2*σ)/t := by field_simp; ring
    rw [heq, abs_div] at h
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    have hrw : |2 - 2*σ| / (2*|t|) = (1/2) * (|2-2*σ|/|t|) := by
      rw [div_mul_eq_div_div]; ring
    rw [hrw]
    linarith [h]
  have hnorm : ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re| + |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have hrenn : 0 ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1' : (1:ℝ) ≤ (Q+σ)^2 + t^2 := by nlinarith [sq_nonneg (Q+σ)]
    have h2' : (1:ℝ) ≤ (Q+2-σ)^2 + t^2 := by nlinarith [sq_nonneg (Q+2-σ)]
    have := Real.log_nonneg h1'
    have := Real.log_nonneg h2'
    linarith
  rw [abs_of_nonneg hrenn] at hnorm
  linarith

/-- `1 - 1/x ≤ \log x` for `x > 0`: the standard reverse of `Real.log_le_sub_one_of_pos`, applied at
`1/x`.

### Summary of Proof
Used to get an explicit numeric *lower* bound on `\log(\log|t|)` — needed to discharge the `hnn`
(log-sum nonnegativity) side condition each `interpolated_bound_*_tight` theorem carries, without
pinning down `\log(\log|t|)` exactly.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1b_tight`. -/
theorem log_ge_one_sub_inv (x : ℝ) (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have hinv : (0:ℝ) < 1/x := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_div one_ne_zero hx.ne', Real.log_one, zero_sub] at h
  linarith

/-- **Tight (`O(1/t²)`) upper counterpart of `GPL_ge_log`**, matching
doi:10.1016/j.jmaa.2026.130404 pp. 7–8's own
`log|t| < |G_{Q₁,Q₂}(σ+it)| < (1+O(1/(t²\log|t|)))\log|t|`.

### Summary of Proof
The extra beneficial `1/\log|t|` factor is dropped for a simpler `C/t²` shape, using `log|t| ≥ 1`
at `|t| ≥ 3`. Unlike `GPL_le_log`, which bounds `‖z‖ ≤ |Re z| + |Im z|`
(`Complex.norm_le_abs_re_add_abs_im`, a triangle inequality that adds the `Θ(1/|t|)` imaginary
part *linearly* to the `Θ(\log|t|)` real part), this bounds the true Euclidean norm via
`√(x²+y²) ≤ x + y²/(2x)` for `x > 0` (`x = Re`, `y = Im`), so the `Θ(1/|t|)` imaginary part enters
only *quadratically* — the paper's own cancellation trick, reached by a different route (direct
`Re`/`Im` quadrature instead of its `|1+i/t|`-on-the-product formulation, since the two are
equivalent once the pieces are already in hand here).
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_re_eq`, `abs_arctan_sub_arctan_le`, `arctan_div_swap`,
`norm_eq_sqrt`.
**Used by:** `G1shift_le_tight`, `fiori_zeta_interpolation_1c_tight`,
`fiori_zeta_interpolation_tight`. -/
theorem GPL_le_log_tight (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) (ht : (3:ℝ) ≤ |t|) :
    ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ Real.log |t| + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * t^2) := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  -- `Re` upper bound, exactly `GPL_le_log`'s own `hre` block
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) := by
    rw [GPL_re_eq]
    have key : ∀ C : ℝ, Real.log (C^2 + t^2) ≤ 2 * Real.log |t| + C^2 / t^2 := by
      intro C
      have hlog : Real.log (C^2 + t^2) = Real.log (t^2) + Real.log (1 + C^2/t^2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      have h2t : Real.log (t^2) = 2 * Real.log |t| := by
        rw [← sq_abs t, Real.log_pow]; push_cast; ring
      have hb : Real.log (1 + C^2/t^2) ≤ C^2/t^2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + C^2/t^2 by positivity)
        linarith
      rw [hlog, h2t]; linarith
    have k1 := key (Q+σ)
    have k2 := key (Q+2-σ)
    have he : ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)
        = (1/4) * ((Q+σ)^2/t^2 + (Q+2-σ)^2/t^2) := by field_simp
    rw [he]
    linarith [k1, k2]
  -- `Re` lower bound (the extra half `GPL_ge_log` doesn't expose)
  have hrelow : Real.log |t| ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1' : t ^ 2 ≤ (Q + σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + σ)]
    have h2' : t ^ 2 ≤ (Q + 2 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - σ)]
    have ht0' : (0:ℝ) < t ^ 2 := by
      rw [← sq_abs t]; exact pow_pos (abs_pos.mpr htne) 2
    have hlt : Real.log (t^2) ≤ Real.log ((Q + σ) ^ 2 + t ^ 2) := Real.log_le_log ht0' h1'
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - σ) ^ 2 + t ^ 2) := Real.log_le_log ht0' h2'
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  -- `Im` upper bound, exactly `GPL_le_log`'s own `him` block
  have him : |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| ≤ |2 - 2*σ| / (2 * |t|) := by
    rw [GPL_im_eq Q σ t h1 h2, arctan_div_swap h1 h2 htne, abs_mul]
    have h := abs_arctan_sub_arctan_le ((Q+2-σ)/t) ((Q+σ)/t)
    have heq : (Q+2-σ)/t - (Q+σ)/t = (2 - 2*σ)/t := by field_simp; ring
    rw [heq, abs_div] at h
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    have hrw : |2 - 2*σ| / (2*|t|) = (1/2) * (|2-2*σ|/|t|) := by
      rw [div_mul_eq_div_div]; ring
    rw [hrw]
    linarith [h]
  -- `log|t| ≥ 1` at `|t| ≥ 3` (since `e < 3`)
  have hlog1 : (1:ℝ) ≤ Real.log |t| := by
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hh : Real.log (Real.exp 1) ≤ Real.log |t| :=
      Real.log_le_log (Real.exp_pos 1) (by linarith)
    rwa [Real.log_exp] at hh
  have hxge1 : (1:ℝ) ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := hlog1.trans hrelow
  set x := (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re with hxdef
  set y := (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im with hydef
  have hxpos : (0:ℝ) < x := by linarith
  -- `√(x²+y²) ≤ x + y²/(2x)` for `x > 0`
  have hkey : Real.sqrt (x^2+y^2) ≤ x + y^2/(2*x) := by
    have hrhs_nonneg : (0:ℝ) ≤ x + y^2/(2*x) := by positivity
    rw [show x + y^2/(2*x) = Real.sqrt ((x+y^2/(2*x))^2) from (Real.sqrt_sq hrhs_nonneg).symm]
    apply Real.sqrt_le_sqrt
    have expand : (x+y^2/(2*x))^2 = x^2+y^2+(y^2/(2*x))^2 := by field_simp; ring
    rw [expand]
    linarith [sq_nonneg (y^2/(2*x))]
  -- the `y²/(2x)` correction: `y² ≤ (2-2σ)²/(4t²)` and `2x ≥ 2`, so `y²/(2x) ≤ (2-2σ)²/(8t²)`
  have hyx : y ^ 2 / (2 * x) ≤ (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by
    have hy2 : y ^ 2 ≤ (2 - 2 * σ) ^ 2 / (4 * t ^ 2) := by
      have hyy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      have h2 : |y| ^ 2 ≤ (|2 - 2 * σ| / (2 * |t|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg y) him 2
      have heq : (|2 - 2 * σ| / (2 * |t|)) ^ 2 = (2 - 2 * σ) ^ 2 / (4 * t ^ 2) := by
        rw [div_pow, sq_abs, mul_pow, sq_abs]; ring_nf
      rw [hyy, ← heq]; exact h2
    calc y ^ 2 / (2 * x) ≤ ((2 - 2 * σ) ^ 2 / (4 * t ^ 2)) / (2 * x) := by gcongr
      _ ≤ ((2 - 2 * σ) ^ 2 / (4 * t ^ 2)) / 2 := by gcongr; linarith
      _ = (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by ring
  have hnormeq : ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ = Real.sqrt (x^2+y^2) := norm_eq_sqrt _
  rw [hnormeq]
  have hsplit : Real.log |t| + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * t^2)
      = (Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)) + (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by
    rw [sq_abs]; ring
  rw [hsplit]
  linarith [hkey, hre, hyx]

/-- `((Q+σ)² + (Q+2-σ)²)/(4T²) ≤ 1/(2T)` when `(Q+2)² ≤ T` and `0 < σ < 1` — the `Re`-error term
of `GPL_le_log`, absorbed.

### Summary of Proof
Both `(Q+σ)²` and `(Q+2-σ)²` are at most `(Q+2)²` for `0 < σ < 1`, so the numerator is at most
`2(Q+2)²`. The hypothesis `(Q+2)² ≤ T` then turns `2(Q+2)²/(4T²)` into `2T/(4T²) = 1/(2T)`.
Clearing denominators with `div_le_div_iff₀` reduces the whole thing to `nlinarith`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
private theorem gpl_err_bound {Q σ T : ℝ} (hQ : 0 < Q) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hM : (Q + 2) ^ 2 ≤ T) (hT : 0 < T) :
    ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) / (4 * T ^ 2) ≤ 1 / (2 * T) := by
  have h1 : (Q + σ) ^ 2 ≤ (Q + 2) ^ 2 := by nlinarith
  have h2 : (Q + 2 - σ) ^ 2 ≤ (Q + 2) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1, h2, hM, hT]

/-- `1/T ≤ L/(4T)` for `T > 0` and `L ≥ 4` — absorbs a bare `1/T` error term into an `L/(4T)` one,
where `L` stands for `log T` (at least `4` in the operating range `T > 10¹²`, via
`four_le_log_of_ge_fiftyfive`).

### Summary of Proof
This is the step that lets the final bound be quoted with a `log T` in the denominator rather than
a constant. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
private theorem inv_le_log_div {L T : ℝ} (hT : 0 < T) (hL : 4 ≤ L) : (1:ℝ) / T ≤ L / (4 * T) := by
  rw [div_le_div_iff₀ hT (by positivity)]
  nlinarith

/-- `1/(2T) + 1/(2T) = 1/T` — combines the two half-sized error contributions (one from `Re`, one
from
`Im`) into a single `1/T`.

### Summary of Proof
Pure arithmetic, isolated so the main proofs read as a chain of named steps. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
private theorem two_halves_inv {T : ℝ} (hT : T ≠ 0) :
    (1:ℝ) / (2 * T) + 1 / (2 * T) = 1 / T := by field_simp; ring

/-- `1/(2T²) = (1/T)²/2` — re-expresses the quadratic error term in powers of `1/T`, so the final
bound
can be stated uniformly in the single small quantity `1/T`.

### Summary of Proof
No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`. -/
private theorem d_eq {T : ℝ} (hT : T ≠ 0) : (1:ℝ) / (2 * T ^ 2) = (1 / T) ^ 2 / 2 := by
  field_simp

/-- `1/(4T) = (1/T)/4` — the linear companion to `d_eq`, likewise re-expressing an error term in
powers
of `1/T`.

### Summary of Proof
No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`. -/
private theorem e_eq {T : ℝ} (hT : T ≠ 0) : (1:ℝ) / (4 * T) = (1 / T) / 4 := by
  field_simp

/-- The `r = 3` product expansion behind `fiori_zeta_interpolation`'s final step, with the extra
`s - 1` slot: `(A·N₁^{p+1}·N_G^{ra})^{wa}·(B·N₁·N₂^q·N_G^{rb})^{wb} =
A^{wa}B^{wb}(N₁^{p·wa}·N₁)N₂^{q·wb}N_G^{ra·wa+rb·wb}`, using `wa + wb = 1` to collapse
`(p+1)wa + wb` to `p·wa + 1`.

### Summary of Proof
Pure `rpow` bookkeeping for the `r = 3` product in `fiori_zeta_interpolation`: distribute each
weighted factor over its product using `Real.mul_rpow` (valid since every base is nonnegative),
then collect the two `N1` powers using `wa + wb = 1`, which is what turns `N1^(p·wa) · N1^(wa+wb)`
into `N1^(p·wa) · N1`. The `NG` exponents combine to `ra·wa + rb·wb`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`. -/
private theorem rpow_prod_expand {A B N1 N2 NG p q ra rb wa wb : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hN1 : 0 < N1) (hN2 : 0 ≤ N2) (hNG : 0 < NG)
    (hsum : wa + wb = 1) :
    (A * N1 ^ (p + 1) * NG ^ ra) ^ wa * (B * N1 * N2 ^ q * NG ^ rb) ^ wb
      = A ^ wa * B ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb)
          * NG ^ (ra * wa + rb * wb) := by
  have h1 : (0:ℝ) ≤ N1 ^ (p + 1) := Real.rpow_nonneg hN1.le _
  have h2 : (0:ℝ) ≤ NG ^ ra := Real.rpow_nonneg hNG.le _
  have h3 : (0:ℝ) ≤ NG ^ rb := Real.rpow_nonneg hNG.le _
  have h4 : (0:ℝ) ≤ N2 ^ q := Real.rpow_nonneg hN2 _
  rw [Real.mul_rpow (mul_nonneg hA.le h1) h2, Real.mul_rpow hA.le h1,
    Real.mul_rpow (mul_nonneg (mul_nonneg hB.le hN1.le) h4) h3,
    Real.mul_rpow (mul_nonneg hB.le hN1.le) h4, Real.mul_rpow hB.le hN1.le,
    ← Real.rpow_mul hN1.le, ← Real.rpow_mul hN2, ← Real.rpow_mul hNG.le,
    ← Real.rpow_mul hNG.le]
  have hcomb : N1 ^ ((p + 1) * wa) * N1 ^ wb = N1 ^ (p * wa) * N1 := by
    rw [← Real.rpow_add hN1, show (p + 1) * wa + wb = p * wa + 1 by linear_combination hsum,
      Real.rpow_add hN1, Real.rpow_one]
  have hcombG : NG ^ (ra * wa) * NG ^ (rb * wb) = NG ^ (ra * wa + rb * wb) :=
    (Real.rpow_add hNG _ _).symm
  calc A ^ wa * N1 ^ ((p + 1) * wa) * NG ^ (ra * wa)
        * (B ^ wb * N1 ^ wb * N2 ^ (q * wb) * NG ^ (rb * wb))
      = A ^ wa * B ^ wb * (N1 ^ ((p + 1) * wa) * N1 ^ wb) * N2 ^ (q * wb)
          * (NG ^ (ra * wa) * NG ^ (rb * wb)) := by ring
    _ = _ := by rw [hcomb, hcombG]

/-- `x^E ≤ y^E(1+c)` from `x ≤ y(1+c)` and `0 ≤ E ≤ 1`: `rpow` is monotone in the base, and
`(1+c)^E ≤ (1+c)^1` since `1+c ≥ 1`.

### Summary of Proof
Raise the hypothesis `x ≤ y(1+c)` to the power `E` by `Real.rpow_le_rpow`, split the right side
with `Real.mul_rpow`, then discard the exponent on the window factor: since `0 ≤ E ≤ 1` and `1+c ≥
1`, `Real.rpow_le_rpow_of_exponent_le` gives `(1+c)^E ≤ (1+c)^1 = 1+c`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `fiori_zeta_interpolation_tight`. -/
private theorem rpow_window {x y c E : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
    (hxy : x ≤ y * (1 + c)) (hE : 0 ≤ E) (hE1 : E ≤ 1) :
    x ^ E ≤ y ^ E * (1 + c) := by
  calc x ^ E ≤ (y * (1 + c)) ^ E := Real.rpow_le_rpow hx hxy hE
    _ = y ^ E * (1 + c) ^ E := Real.mul_rpow hy (by linarith)
    _ ≤ y ^ E * (1 + c) := by
        have h1 : (1 + c) ^ E ≤ (1 + c) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hE1
        rw [Real.rpow_one] at h1
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hy E)

/-- `√(σ²+t²) ≤ √((1-σ)²+t²)·(1 + 1/(2t²))` for `σ ∈ [0,1]`, `|t| ≥ 1`: the `‖s‖/‖s-1‖` ratio
introduced by applying Phragmén–Lindelöf to `(s-1)ζ(s)` instead of `ζ(s)`.

### Summary of Proof
This is the *entire* cost of the pole-killing device — `1 + O(1/t²)` on the leading constant,
nothing on any exponent.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `fiori_zeta_interpolation_tight`. -/
private theorem norm_ratio_window {σ t : ℝ} (ht : 1 ≤ |t|) (_h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    Real.sqrt (σ ^ 2 + t ^ 2) ≤ Real.sqrt ((1 - σ) ^ 2 + t ^ 2) * (1 + 1 / (2 * |t| ^ 2)) := by
  have hts : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [hts]
  have ht2 : (1:ℝ) ≤ t ^ 2 := by nlinarith [sq_abs t]
  have ht0 : (0:ℝ) < t ^ 2 := by linarith
  have hR : (0:ℝ) ≤ Real.sqrt ((1 - σ) ^ 2 + t ^ 2) * (1 + 1 / (2 * t ^ 2)) := by positivity
  have key : σ ^ 2 + t ^ 2
      ≤ (Real.sqrt ((1 - σ) ^ 2 + t ^ 2) * (1 + 1 / (2 * t ^ 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set w : ℝ := 1 / (2 * t ^ 2) with hw_def
    have hw0 : 0 < w := by rw [hw_def]; positivity
    have htne : t ≠ 0 := by intro hc; rw [hc] at ht0; norm_num at ht0
    have hwt : t ^ 2 * w = 1 / 2 := by rw [hw_def]; field_simp
    have hexpand : ((1 - σ) ^ 2 + t ^ 2) * (1 + w) ^ 2
        = (1 - σ) ^ 2 + t ^ 2 + 2 * (t ^ 2 * w) + 2 * w * (1 - σ) ^ 2
          + w ^ 2 * ((1 - σ) ^ 2 + t ^ 2) := by ring
    rw [hexpand, hwt]
    nlinarith [mul_nonneg hw0.le (sq_nonneg (1 - σ)),
      mul_nonneg (sq_nonneg w) (by positivity : (0:ℝ) ≤ (1 - σ) ^ 2 + t ^ 2)]
  calc Real.sqrt (σ ^ 2 + t ^ 2)
      ≤ Real.sqrt ((Real.sqrt ((1 - σ) ^ 2 + t ^ 2) * (1 + 1 / (2 * t ^ 2))) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_sq hR

/-- `(1+d)³(1+e) ≤ 1+u` when `d ≤ u²/2`, `e ≤ u/4`, `0 < u ≤ 1/55`.

### Summary of Proof
Three `(1+d)` factors: one each from `‖s‖`, `‖1-s‖`, and the `‖s‖/‖1-s‖` ratio; the `(1+e)` factor
is the `‖GPL‖` window. Discharged by `nlinarith` from `u ≤ 1/55`, which makes `u² ≤ u/55`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`. -/
private theorem four_factor_bound {d e u : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hu : 0 < u)
    (hu55 : u ≤ 1/55) (hd' : d ≤ u^2/2) (he' : e ≤ u/4) :
    (1+d)*(1+d)*(1+d)*(1+e) ≤ 1 + u := by
  have hu2 : u^2 ≤ u/55 := by nlinarith
  have hd1 : d ≤ u/110 := by nlinarith
  nlinarith [mul_nonneg hd he, mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd,
    mul_nonneg (mul_nonneg hd hd) he, mul_nonneg (mul_nonneg (mul_nonneg hd hd) hd) he,
    hd1, hu2, mul_pos hu hu]

/-- **Tight combination**: `(1+d)³(1+e) ≤ 1+7d+8e` when `0 ≤ d ≤ 1`, `0 ≤ e`.

### Summary of Proof
Unlike `four_factor_bound`, which forces the *target* slack `u` to be one order larger than `d` (`d
≤ u²/2`, matching a regime where `d = O(1/t²)` is negligible next to `e`, `u = O(1/t)`), this keeps
`d` and `e` on equal footing — needed once `e` is *also* `O(1/t²)`
(`GPL_le_log_tight`/`G1shift_le_tight`), where insisting `d ≤ u²/2` would force `u` back up to
`Ω(1/t)` and destroy the improvement. Only needs `d ≤ 1`, not any comparison between `d` and `e`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
private theorem four_factor_bound_tight {d e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he0 : 0 ≤ e) :
    (1+d)*(1+d)*(1+d)*(1+e) ≤ 1 + 7*d + 8*e := by
  nlinarith [mul_nonneg hd0 he0, mul_nonneg hd0 hd0, mul_nonneg (mul_nonneg hd0 hd0) hd0,
    mul_nonneg (mul_nonneg hd0 hd0) he0, mul_nonneg (mul_nonneg (mul_nonneg hd0 hd0) hd0) he0,
    mul_le_of_le_one_right hd0 hd1]

/-- `x² ≤ 1` for `x ∈ [0,1]` — supplies the `x² ≤ 1` hypothesis of `sqrt_le_window` at the
interpolation points, where `x` is a convex-combination weight and so automatically lies in the
unit interval.

### Summary of Proof
Discharged by `nlinarith`. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `fiori_zeta_interpolation_tight`. -/
private theorem sq_le_one_of_unit {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ 1 := by nlinarith

/-- `√(x²+t²) ≤ |t|(1 + 1/(2t²))` when `x² ≤ 1` and `|t| ≥ 1` — the `‖σ+it‖ ≈ |t|` half of
Fiori's `Cᵢ(t₀) → 1` bookkeeping.

### Summary of Proof
Square the proposed bound: `(|t|(1+1/(2t²)))² = t² + 1 + 1/(4t²)`, which exceeds `x² + t²` whenever
`x² ≤ 1`, the spare `1/(4t²)` being pure slack. Then apply `Real.sqrt_le_sqrt` and simplify the
square root of a square using `|t| ≥ 1 > 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `fiori_zeta_interpolation_tight`. -/
private theorem sqrt_le_window {x t : ℝ} (ht : 1 ≤ |t|) (hx : x ^ 2 ≤ 1) :
    Real.sqrt (x ^ 2 + t ^ 2) ≤ |t| * (1 + 1 / (2 * |t| ^ 2)) := by
  have hT0 : (0:ℝ) < |t| := by linarith
  have hsq : (|t| * (1 + 1 / (2 * |t| ^ 2))) ^ 2 = |t| ^ 2 + 1 + 1 / (4 * |t| ^ 2) := by
    field_simp; ring
  have hTsq : |t| ^ 2 = t ^ 2 := sq_abs t
  calc Real.sqrt (x ^ 2 + t ^ 2) ≤ Real.sqrt ((|t| * (1 + 1 / (2 * |t| ^ 2))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hsq, hTsq]
        have h4 : (0:ℝ) ≤ 1 / (4 * t ^ 2) := by positivity
        linarith
    _ = |t| * (1 + 1 / (2 * |t| ^ 2)) := Real.sqrt_sq (by positivity)

/-- `(1+d)²(1+e) ≤ 1+u` when `d ≤ u²/2`, `e ≤ u/4` and `0 < u ≤ 1/55` — the two-`(1+d)` form of
the `(1 + 1/|t|)` slack arithmetic, with `u = 1/|t|`. `fiori_zeta_interpolation` uses
`four_factor_bound` instead, since the pole-killing `s-1` factor contributes a third `(1+d)`.

### Summary of Proof
Multiply out `(1+d)²(1+e)` and bound each cross term. With `d ≤ u²/2` and `e ≤ u/4`, every term
beyond `1` is at most a multiple of `u²` or `u/4`; the hypothesis `u ≤ 1/55` makes `u² ≤ u/55`, so
the total stays below `u`. Discharged by `nlinarith` with those products supplied explicitly.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
private theorem three_factor_bound {d e u : ℝ} (hd : 0 ≤ d) (_he : 0 ≤ e) (hu : 0 < u)
    (hu55 : u ≤ 1/55) (hd' : d ≤ u^2/2) (he' : e ≤ u/4) :
    (1+d)*(1+d)*(1+e) ≤ 1 + u := by
  have hu2 : u^2 ≤ u/55 := by nlinarith
  nlinarith [sq_nonneg u, sq_nonneg d, mul_nonneg hd _he, mul_nonneg hd hd,
    mul_nonneg (mul_nonneg hd hd) _he, hu2, mul_pos hu hu]

/-- **Window lemma, general half-width.** For `x` within `d` of `y`, with `0 ≤ d < y`, `log x` and
`log y` differ by at most `d/(y-d)` — proved directly from the tangent-line bound
`Real.log_le_sub_one_of_pos` applied to `y/x` and to `x/y`, avoiding the MVT-cancellation
subtleties that make the analogous bound for `littlewood_mainterm` (variable half-width `h`)
delicate. The `d = 1` case is packaged separately as `abs_log_sub_log_le`.

### Summary of Proof
Both directions from the tangent-line bound `log w ≤ w - 1`. For one side, `log(y/x) ≤ y/x - 1 =
(y-x)/x ≤ d/(y-d)`, using `x ≥ y-d`; the other side is symmetric with the roles of `x` and `y`
exchanged. The hypothesis `d < y` keeps `y-d` positive so the quotient is well defined.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `abs_log_sub_log_le`, `log_arc_window`, `loglog_arc_window`. -/
theorem abs_log_sub_log_le' {y d x : ℝ} (hd : 0 ≤ d) (hdy : d < y)
    (hx : x ∈ Set.Icc (y - d) (y + d)) : |Real.log x - Real.log y| ≤ d / (y - d) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hx0 : (0:ℝ) < x := by linarith [hx.1]
  have hyd : (0:ℝ) < y - d := by linarith
  rw [abs_le]
  constructor
  · -- log y - log x ≤ d/(y-d), from log(y/x) ≤ y/x - 1 = (y-x)/x ≤ d/(y-d)
    have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (y / x) = Real.log y - Real.log x :=
      Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)
    have h3 : y / x - 1 ≤ d / (y - d) := by
      rw [div_sub_one (ne_of_gt hx0), div_le_div_iff₀ hx0 hyd]
      nlinarith [hx.1]
    linarith [h2 ▸ h1]
  · -- log x - log y ≤ d/y ≤ d/(y-d)
    have h1 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (x / y) = Real.log x - Real.log y :=
      Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)
    have h3 : x / y - 1 ≤ d / (y - d) := by
      rw [div_sub_one (ne_of_gt hy0), div_le_div_iff₀ hy0 hyd]
      nlinarith [hx.2]
    linarith [h2 ▸ h1]

/-- The `d = 1` specialization of `abs_log_sub_log_le'`: for `t` within `1` of `T` and `T > 1`,
`|log t - log T| ≤ 1/(T-1)`.

### Summary of Proof
Here the window half-width is the fixed `1` of the interpolation setup, utterly negligible against
`T > 10¹²`, so `abs_log_sub_log_le'`'s crude one-sided estimate suffices, with no need for exact
antiderivatives or sign case-splits. No tex counterpart — internal scaffolding for the
`interpolated_bound_*` family.

### References
No tex counterpart.

### Dependencies
**Depends on:** `abs_log_sub_log_le'`.
**Used by:** the `interpolated_bound_*` chain (via `log_arc_window` / `loglog_arc_window`). -/
theorem abs_log_sub_log_le (T t : ℝ) (hT : (1:ℝ) < T) (ht : t ∈ Set.Icc (T - 1) (T + 1)) :
    |Real.log t - Real.log T| ≤ 1 / (T - 1) :=
  abs_log_sub_log_le' zero_le_one hT ht

/-! ### The Yang interpolation intervals `[σ_k, σ_{k+1}]`

`interpolated_bound_2` interpolates `ExternalFacts.yang_critical_strip_bound` between the
consecutive lines `σ_k := 1 - k/(2^k-2)` and `σ_{k+1}`. The three facts below — that these are
nonempty intervals strictly inside `(0,1)` — are the elementary arithmetic behind that theorem's
`hab`, `hG_holo` and `hf_holo` hypotheses. -/

/-- `k + 2 < 2^k` for `k ≥ 4` (real-valued).

### Summary of Proof
Induction on `k` from the base case `k = 4`, where `6 < 16`. The successor step is `2^{k+1} = 2·2^k
> 2(k+2) = (k+3) + (k+1) > k+3`, using `k ≥ 4 > 0`. Cases below `4` are discharged by `omega`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `sigmaYang_mem_Ioo`, `two_lt_two_pow`. -/
theorem add_two_lt_two_pow : ∀ {k : ℕ}, 4 ≤ k → (k : ℝ) + 2 < 2 ^ k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro hk
    rcases Nat.lt_or_ge n 4 with h | h
    · have hn : n = 3 := by omega
      subst hn; norm_num
    · have hn := ih h
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

/-- `2 < 2^k` for `k ≥ 4` (real-valued); in particular `2^k - 2 > 0`.

### Summary of Proof
Immediate from `add_two_lt_two_pow`, which gives `k + 2 < 2^k`, together with `k ≥ 0`. Recorded
separately because the positivity of `2^k - 2` is needed as a side condition throughout the
Yang-line lemmas.

### References
No tex counterpart.

### Dependencies
**Depends on:** `add_two_lt_two_pow`.
**Used by:** `half_le_sigmaYang`, `interpolated_bound_2`, `interpolated_bound_2_tight`,
`interpolated_bound_2_tight_simple`, `sigmaYang_lt_succ`, `sigmaYang_mem_Ioo`. -/
theorem two_lt_two_pow {k : ℕ} (hk : 4 ≤ k) : (2 : ℝ) < 2 ^ k := by
  have h := add_two_lt_two_pow hk
  have : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
  linarith

/-- `2k + 2 ≤ 2^k` for `k ≥ 4` (real-valued) — the sharper form needed for `σ_k ≥ 1/2`.

### Summary of Proof
Induction on `k` from the base case `k = 4`, where `10 ≤ 16`. The successor step uses `2^{k+1} =
2·2^k ≥ 2(2k+2) = (2k+4) + 2k ≥ 2(k+1)+2`, which needs `k ≥ 4` to absorb the extra `2k`. Sharper
than `add_two_lt_two_pow`, and it is this sharper form that `half_le_sigmaYang` requires.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `half_le_sigmaYang`. -/
theorem two_mul_add_two_le_two_pow : ∀ {k : ℕ}, 4 ≤ k → 2 * (k : ℝ) + 2 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro hk
    rcases Nat.lt_or_ge n 4 with h | h
    · have hn : n = 3 := by omega
      subst hn; norm_num
    · have hn := ih h
      have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      rw [pow_succ]
      push_cast
      linarith

/-- The `k`-th Yang line `σ_k = 1 - k/(2^k-2)` is at least `1/2` for `k ≥ 4`, so every strip
`[σ_k, σ_{k+1}]` used by `interpolated_bound_2` sits inside `[1/2, 1)`.

### Summary of Proof
`σ_k ≥ 1/2` is equivalent to `k/(2^k-2) ≤ 1/2`, i.e. to `2k ≤ 2^k - 2`, which is exactly
`two_mul_add_two_le_two_pow`. Positivity of the denominator comes from `two_lt_two_pow`, so
`div_le_div_iff₀` may be used to clear it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `two_lt_two_pow`, `two_mul_add_two_le_two_pow`.
**Used by:** `interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem half_le_sigmaYang {k : ℕ} (hk : 4 ≤ k) : (1 : ℝ) / 2 ≤ 1 - (k : ℝ) / (2 ^ k - 2) := by
  have h2 : (0 : ℝ) < 2 ^ k - 2 := by linarith [two_lt_two_pow hk]
  have hle : (k : ℝ) / (2 ^ k - 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ h2 (by norm_num : (0:ℝ) < 2)]
    linarith [two_mul_add_two_le_two_pow hk]
  linarith

/-- The `k`-th Yang line `σ_k = 1 - k/(2^k-2)` lies strictly inside `(0,1)` for `k ≥ 4`.

### Summary of Proof
Two bounds. `σ_k < 1` because `k/(2^k-2)` is strictly positive, the denominator being positive by
`two_lt_two_pow`. `σ_k > 0` because `k/(2^k-2) < 1`, which after clearing the denominator is `k <
2^k - 2`, i.e. `add_two_lt_two_pow`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `add_two_lt_two_pow`, `two_lt_two_pow`.
**Used by:** `interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem sigmaYang_mem_Ioo {k : ℕ} (hk : 4 ≤ k) :
    0 < 1 - (k : ℝ) / (2 ^ k - 2) ∧ 1 - (k : ℝ) / (2 ^ k - 2) < 1 := by
  have h2 : (0 : ℝ) < 2 ^ k - 2 := by linarith [two_lt_two_pow hk]
  have hkp : (0 : ℝ) < (k : ℝ) := by
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  constructor
  · have : (k : ℝ) / (2 ^ k - 2) < 1 := by
      rw [div_lt_one h2]
      linarith [add_two_lt_two_pow hk]
    linarith
  · have : 0 < (k : ℝ) / (2 ^ k - 2) := by positivity
    linarith

/-- Consecutive Yang lines are strictly increasing: `σ_k < σ_{k+1}` for `k ≥ 4`.

### Summary of Proof
The Yang lines increase, i.e. `(k+1)/(2^{k+1}-2) < k/(2^k-2)`. Writing `2^{k+1} = 2·2^k` and
cross-multiplying — both denominators are positive by `two_lt_two_pow` — reduces this to a
polynomial inequality in `2^k` and `k` that holds for `k ≥ 4`. This is what makes the strips `[σ_k,
σ_{k+1}]` non-degenerate, so that `interpolated_bound_2` interpolates between genuinely distinct
lines.

### References
No tex counterpart.

### Dependencies
**Depends on:** `two_lt_two_pow`.
**Used by:** `interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem sigmaYang_lt_succ {k : ℕ} (hk : 4 ≤ k) :
    1 - (k : ℝ) / (2 ^ k - 2) < 1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2) := by
  have h2 : (0 : ℝ) < 2 ^ k - 2 := by linarith [two_lt_two_pow hk]
  have h2' : (0 : ℝ) < 2 ^ (k + 1) - 2 := by
    have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := by
      rw [pow_succ]; nlinarith [(by positivity : (0:ℝ) < (2:ℝ) ^ k)]
    linarith
  have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsucc : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have key : ((k : ℝ) + 1) / (2 ^ (k + 1) - 2) < (k : ℝ) / (2 ^ k - 2) := by
    rw [div_lt_div_iff₀ h2' h2, hsucc]
    nlinarith [(by positivity : (0:ℝ) < (2:ℝ) ^ k)]
  linarith

/-- **The coefficient identity behind `interpolated_bound_2`.** Writing `x := 2^k`, the
Phragmén–Lindelöf interpolant of Yang's exponents `1/(x-2)` at `σ_k = 1 - k/(x-2)` and `1/(2x-2)`
at `σ_{k+1} = 1 - (k+1)/(2x-2)` equals, identically in `σ`, the coefficient `(1-σ)/(k-1+2/x) -
1/(x(k-1)+2)` displayed in the source — both sides being `(x(1-σ) - 1)/(x(k-1) + 2)`.

### Summary of Proof
Stated with `x` and `kk` as *independent* reals (which is legitimate: the identity is a
rational-function identity, verified in `sympy`), so that `field_simp; ring` can discharge it.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem yang_interp_coeff_eq {x kk s : ℝ} (hx : 16 ≤ x) (hkk : 4 ≤ kk) :
    1 / (x - 2) * ((1 - (kk + 1) / (2 * x - 2) - s)
        / (1 - (kk + 1) / (2 * x - 2) - (1 - kk / (x - 2))))
      + 1 / (2 * x - 2) * ((s - (1 - kk / (x - 2)))
        / (1 - (kk + 1) / (2 * x - 2) - (1 - kk / (x - 2))))
    = (1 - s) / (kk - 1 + 2 / x) - 1 / (x * (kk - 1) + 2) := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : x - 2 ≠ 0 := by linarith
  have h2 : 2 * x - 2 ≠ 0 := by linarith
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx1' : (-1 : ℝ) + x ≠ 0 := by linarith
  have h3 : kk - 1 + 2 / x ≠ 0 := by
    have : (0:ℝ) < 2 / x := by positivity
    linarith
  have h4 : x * (kk - 1) + 2 ≠ 0 := by nlinarith
  have hN : x * (kk - 1) + 2 ≠ 0 := h4
  have hD : 1 - (kk + 1) / (2 * x - 2) - (1 - kk / (x - 2))
      = (x * (kk - 1) + 2) / ((x - 2) * (2 * x - 2)) := by
    field_simp
    ring
  rw [hD]
  field_simp
  ring

/-! ### Uniform positive lower bounds on the `Gᵢ`, and the growth-envelope reduction

`fiori_phragmenLindelof`'s `hG_lower`/`hf_upper` pair is a *single shared* two-exponential
envelope. In every application here each `‖Gᵢ‖` is in fact bounded below by a positive **constant**
on the strip (`linG`/`linGRefl` because they are `C` times a linear function that stays away from
`0` there; `GPL` because `Re (GPL Q s) = ½(log|Q+s| + log|Q+2-s|)` is bounded below by its value at
the "innermost" corner), which makes `hG_lower` free. The only genuine content left is that `f`
admits *some* two-exponential envelope, which `envelope_of_const_lower` then rescales to share
`C1,C2,C3` with the `Gᵢ`. -/

/-- A uniform positive lower bound on `‖linG C Q‖` across the strip: `C(Q+a) ≤ ‖linG C Q (σ+it)‖`
for `σ ∈ [a,b]`, given `C > 0` and `Q + a > 0`.

### Summary of Proof
The `linG` half of the pair completed by `linGRefl_lower_const`. `fiori_phragmenLindelof`
(`\cite[Theorem 7]{Fiori2026}`, i.e. Theorem 7 of *Fiori's Phragmén–Lindelöf paper*, not of this
project's tex) requires each `Gᵢ` to be bounded away from `0` on the strip, so that `log‖Gᵢ‖` is
finite and the interpolation exponents are well defined; `exists_shared_envelope` then combines
these per-`Gᵢ` constants into one envelope. **Proof.** `linG C Q (σ+it) = C(Q+σ) + (Ct)i`, so `‖·‖
= √((C(Q+σ))² + (Ct)²) ≥ √((C(Q+σ))²) = C(Q+σ) ≥ C(Q+a)`, the last step by `σ ≥ a` and `C > 0`. The
bound is attained at `σ = a`, `t = 0`, so it is sharp. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linG`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem linG_lower_const {C Q a b : ℝ} (hC : 0 < C) (ha : 0 < Q + a) (σ : ℝ)
    (hσ : σ ∈ Set.Icc a b) (t : ℝ) : C * (Q + a) ≤ ‖linG C Q (σ + t * Complex.I)‖ := by
  have key : linG C Q (σ + t * Complex.I) = (C * (Q + σ) : ℝ) + (C * t : ℝ) * Complex.I := by
    simp only [linG]; push_cast; ring
  rw [key, Complex.norm_add_mul_I]
  have h1 : C * (Q + a) ≤ C * (Q + σ) := by nlinarith [hσ.1]
  have h2 : (0:ℝ) < C * (Q + a) := by positivity
  calc C * (Q + a) = √((C * (Q + a)) ^ 2) := (Real.sqrt_sq h2.le).symm
    _ ≤ √((C * (Q + σ)) ^ 2 + (C * t) ^ 2) := by
        apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg (C * t)]

/-- A uniform positive lower bound on `‖linGRefl C Q‖` across the strip: `C(Q-b) ≤ ‖linGRefl C Q
(σ+it)‖` for `σ ∈ [a,b]`, given `C > 0` and `b < Q`.

### Summary of Proof
The `linGRefl` mirror of `linG_lower_const`. `fiori_phragmenLindelof` (`\cite[Theorem
7]{Fiori2026}`) needs each `Gᵢ` bounded away from `0` on the strip, so that `log‖Gᵢ‖` stays finite
and the interpolation exponents are well defined; `exists_shared_envelope` then combines these
per-`Gᵢ` constants into one envelope. **Proof.** `linGRefl C Q (σ+it) = C(Q-σ) + (-Ct)i`, so `‖·‖ =
√((C(Q-σ))² + (Ct)²) ≥ √((C(Q-σ))²) = C(Q-σ) ≥ C(Q-b)`, the last step by `σ ≤ b` and `C > 0`. Note
the bound is attained at `σ = b`, `t = 0`, so it is sharp. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linGRefl`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem linGRefl_lower_const {C Q a b : ℝ} (hC : 0 < C) (hb : b < Q) (σ : ℝ)
    (hσ : σ ∈ Set.Icc a b) (t : ℝ) : C * (Q - b) ≤ ‖linGRefl C Q (σ + t * Complex.I)‖ := by
  have key : linGRefl C Q (σ + t * Complex.I)
      = (C * (Q - σ) : ℝ) + (-(C * t) : ℝ) * Complex.I := by
    simp only [linGRefl]; push_cast; ring
  rw [key, Complex.norm_add_mul_I]
  have h1 : C * (Q - b) ≤ C * (Q - σ) := by nlinarith [hσ.2]
  have h2 : (0:ℝ) < C * (Q - b) := by
    have : (0:ℝ) < Q - b := by linarith
    positivity
  calc C * (Q - b) = √((C * (Q - b)) ^ 2) := (Real.sqrt_sq h2.le).symm
    _ ≤ √((C * (Q - σ)) ^ 2 + (-(C * t)) ^ 2) := by
        apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg (C * t)]

/-- `‖GPL Q (σ+it)‖ ≥ ½(log(Q+a) + log(Q+2-b)) > 0` on the strip, provided `Q+a > 1` and `Q+2-b >
1`.

### Summary of Proof
Proved from `‖w‖ ≥ Re w` together with `Re (Complex.log z) = log ‖z‖ ≥ log (Re z)`.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem GPL_lower_const {Q a b : ℝ} (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) (σ : ℝ)
    (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    (Real.log (Q + a) + Real.log (Q + 2 - b)) / 2 ≤ ‖GPL Q (σ + t * Complex.I)‖ := by
  set z₁ : ℂ := (Q : ℂ) + (σ + t * Complex.I) with hz₁
  set z₂ : ℂ := (Q : ℂ) + 2 - (σ + t * Complex.I) with hz₂
  have hre₁ : z₁.re = Q + σ := by simp [hz₁]
  have hre₂ : z₂.re = Q + 2 - σ := by simp [hz₂]
  have h₁ : 0 < Q + σ := by nlinarith [hσ.1]
  have h₂ : 0 < Q + 2 - σ := by nlinarith [hσ.2]
  have hlog₁ : Real.log (Q + a) ≤ (Complex.log z₁).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + a ≤ z₁.re := by rw [hre₁]; linarith [hσ.1]
      _ ≤ ‖z₁‖ := Complex.re_le_norm z₁
  have hlog₂ : Real.log (Q + 2 - b) ≤ (Complex.log z₂).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + 2 - b ≤ z₂.re := by rw [hre₂]; linarith [hσ.2]
      _ ≤ ‖z₂‖ := Complex.re_le_norm z₂
  have hval : GPL Q (σ + t * Complex.I) = (1 / 2 : ℂ) * (Complex.log z₁ + Complex.log z₂) := rfl
  calc (Real.log (Q + a) + Real.log (Q + 2 - b)) / 2
      ≤ (GPL Q (σ + t * Complex.I)).re := by
        rw [hval]; simp only [Complex.mul_re, Complex.add_re]; norm_num; linarith
    _ ≤ ‖GPL Q (σ + t * Complex.I)‖ := Complex.re_le_norm _

/-- **Envelope reduction.** If every `‖G i‖` is bounded below by a positive *constant* `c` on the
strip, and `f` admits *some* two-exponential envelope `(D1,D2,D3)` there, then `f` and the `Gᵢ`
admit a *shared* envelope in exactly the form `fiori_phragmenLindelof` demands.

### Summary of Proof
The rescaling is `C1 := min c D1` and `C2 := D2 + log (D1/C1)`, using `exp (C3*|t|) ≥ 1`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem envelope_of_const_lower {a b : ℝ} {r : ℕ} (G : Fin r → ℂ → ℂ)
    {c : ℝ} (hc : 0 < c)
    (hGc : ∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, c ≤ ‖G i (σ + t * Complex.I)‖)
    {f : ℂ → ℂ} {D1 D2 D3 : ℝ} (hD1 : 0 < D1) (hD2 : 0 < D2) (hD3 : 0 < D3)
    (hD3b : D3 < Real.pi / (b - a))
    (hf : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖f (σ + t * Complex.I)‖ < D1 * Real.exp (D2 * Real.exp (D3 * |t|))) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ C3 < Real.pi / (b - a) ∧
      (∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        C1 * Real.exp (-C2 * Real.exp (C3 * |t|)) < ‖G i (σ + t * Complex.I)‖) ∧
      (∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖f (σ + t * Complex.I)‖ < C1 * Real.exp (C2 * Real.exp (C3 * |t|))) := by
  refine ⟨min c D1, D2 + Real.log (D1 / min c D1), D3, lt_min hc hD1, ?_, hD3, hD3b, ?_, ?_⟩
  · have h1 : (0:ℝ) < min c D1 := lt_min hc hD1
    have h2 : (1:ℝ) ≤ D1 / min c D1 := (one_le_div h1).2 (min_le_right _ _)
    have : 0 ≤ Real.log (D1 / min c D1) := Real.log_nonneg h2
    linarith
  · -- lower bound: `min c D1 * exp(negative) < min c D1 ≤ c ≤ ‖G i‖`
    intro i σ hσ t
    have hpos : (0:ℝ) < min c D1 := lt_min hc hD1
    have hexp : Real.exp (-(D2 + Real.log (D1 / min c D1)) * Real.exp (D3 * |t|)) < 1 := by
      apply Real.exp_lt_one_iff.2
      have h1 : (0:ℝ) < Real.exp (D3 * |t|) := Real.exp_pos _
      have h2 : (0:ℝ) < D2 + Real.log (D1 / min c D1) := by
        have hd : (1:ℝ) ≤ D1 / min c D1 := (one_le_div hpos).2 (min_le_right _ _)
        linarith [Real.log_nonneg hd]
      nlinarith
    calc min c D1 * Real.exp (-(D2 + Real.log (D1 / min c D1)) * Real.exp (D3 * |t|))
        < min c D1 * 1 := by exact mul_lt_mul_of_pos_left hexp hpos
      _ = min c D1 := mul_one _
      _ ≤ c := min_le_left _ _
      _ ≤ ‖G i (σ + t * Complex.I)‖ := hGc i σ hσ t
  · -- upper bound: absorb the factor `D1 / min c D1 = exp (log (D1/min c D1))` into the exponent
    intro σ hσ t
    have hpos : (0:ℝ) < min c D1 := lt_min hc hD1
    have hd : (1:ℝ) ≤ D1 / min c D1 := (one_le_div hpos).2 (min_le_right _ _)
    have hE : (1:ℝ) ≤ Real.exp (D3 * |t|) := Real.one_le_exp (by positivity)
    refine lt_of_lt_of_le (hf σ hσ t) ?_
    have hsplit : (D2 + Real.log (D1 / min c D1)) * Real.exp (D3 * |t|)
        = D2 * Real.exp (D3 * |t|) + Real.log (D1 / min c D1) * Real.exp (D3 * |t|) := by ring
    rw [hsplit, Real.exp_add]
    have hstep : D1 ≤ min c D1 * Real.exp (Real.log (D1 / min c D1) * Real.exp (D3 * |t|)) := by
      have hlog_nonneg : 0 ≤ Real.log (D1 / min c D1) := Real.log_nonneg hd
      have h1 : Real.log (D1 / min c D1)
          ≤ Real.log (D1 / min c D1) * Real.exp (D3 * |t|) := by nlinarith
      have h2 : D1 / min c D1 = Real.exp (Real.log (D1 / min c D1)) :=
        (Real.exp_log (by positivity)).symm
      calc D1 = min c D1 * (D1 / min c D1) := by field_simp
        _ = min c D1 * Real.exp (Real.log (D1 / min c D1)) := by rw [← h2]
        _ ≤ min c D1 * Real.exp (Real.log (D1 / min c D1) * Real.exp (D3 * |t|)) := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hpos.le
    calc D1 * Real.exp (D2 * Real.exp (D3 * |t|))
        ≤ (min c D1 * Real.exp (Real.log (D1 / min c D1) * Real.exp (D3 * |t|)))
            * Real.exp (D2 * Real.exp (D3 * |t|)) := by
          exact mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ = min c D1 * (Real.exp (D2 * Real.exp (D3 * |t|))
            * Real.exp (Real.log (D1 / min c D1) * Real.exp (D3 * |t|))) := by ring

/-- `x^5/3125 ≤ exp x` for `x ≥ 0`, from `exp(x/5) ≥ x/5` — the crude polynomial-versus-
exponential step behind `zeta_envelope`.

### Summary of Proof
From `1 + u ≤ exp u` at `u = x/5`, so `x/5 ≤ exp(x/5)` for `x ≥ 0`. Raising both sides to the fifth
power — legitimate since both are nonnegative — and using `exp(x) = exp(x/5)^5` gives `x^5/3125 ≤
exp x`. The quintic is the weakest power that dominates the growth factor needed downstream.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_envelope`. -/
private theorem quintic_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ (5:ℕ) / 3125 ≤ Real.exp x := by
  have h : x / 5 ≤ Real.exp (x / 5) := by linarith [Real.add_one_le_exp (x / 5)]
  have h5 : Real.exp x = Real.exp (x / 5) ^ (5:ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h5]
  calc x ^ (5:ℕ) / 3125 = (x / 5) ^ (5:ℕ) := by ring
    _ ≤ Real.exp (x / 5) ^ (5:ℕ) := by gcongr

/-- `‖(s-1)ζ(s)‖` is bounded on the compact slice `Re s ∈ [a,b]`, `|Im s| ≤ 3`, since `b < 1`
keeps `ζ`'s pole out of it.

### Summary of Proof
`(s-1)ζ(s)` is continuous on the compact rectangle `[a,b] × [-3,3]`, because the factor `(s-1)`
cancels `ζ`'s only pole and `b < 1` keeps that pole off the slice anyway. A continuous function on
a compact set is bounded, so the supremum exists; the bound is taken nonnegative without loss.
Existential rather than explicit, since only boundedness is needed to feed the growth-envelope
hypothesis.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_envelope`. -/
private theorem compact_slice_bound {a b : ℝ} (hb : b < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Set.Icc a b, ∀ t ∈ Set.Icc (-3:ℝ) 3,
      ‖((σ:ℂ) + t * Complex.I - 1) * riemannZeta ((σ:ℂ) + t * Complex.I)‖ ≤ M := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (-3:ℝ) 3) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => ((p.1:ℂ) + p.2 * Complex.I - 1)
        * riemannZeta ((p.1:ℂ) + p.2 * Complex.I))
      (Set.Icc a b ×ˢ Set.Icc (-3:ℝ) 3) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hne : ((p.1:ℂ) + p.2 * Complex.I) ≠ 1 := by
      intro hc
      have := congrArg Complex.re hc
      simp at this
      have : p.1 ≤ b := (Set.mem_prod.mp hp).1.2
      linarith
    have hz : ContinuousAt riemannZeta ((p.1:ℂ) + p.2 * Complex.I) :=
      (differentiableAt_riemannZeta hne).continuousAt
    have haff : ContinuousAt (fun q : ℝ × ℝ => ((q.1:ℂ) + q.2 * Complex.I)) p := by fun_prop
    exact ContinuousAt.mul (by fun_prop)
      (ContinuousAt.comp (g := riemannZeta) (f := fun q : ℝ × ℝ => ((q.1:ℂ) + q.2 * Complex.I))
        hz haff)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ hσ t ht => ?_⟩
  exact le_trans (hC (σ, t) (Set.mk_mem_prod hσ ht)) (le_max_left _ _)

/-- **`ζ` admits a double-exponential envelope on any strip inside `(0,1)`.** This is the *sole*
remaining input to `fiori_phragmenLindelof`'s growth hypothesis for all four
`interpolated_bound_*`; `envelope_of_const_lower` converts it into the shared `(C1,C2,C3)` package.

### Summary of Proof
**Stated for `f(s) = (s-1)ζ(s)`, the function Phragmén–Lindelöf is actually applied to** (see
`fiori_zeta_interpolation`); the extra factor `‖s-1‖ ≤ 1 + |t|` is polynomial and so changes
nothing in the argument below. It is true with enormous room to spare and its proof needs no new
mathematics, only assembly: `ExternalFacts.bellotti_richert_bound` gives `‖ζ(σ+it)‖ ≤
70.7|t|^{4.438(1-σ)^{3/2}}(log|t|)^{2/3}` for `|t| ≥ 3` on `[1/2,1]` — polynomial in `|t|` with a
bounded exponent — while `exp (D2 · exp (D3|t|))` is doubly exponential and dominates it for any
`D2,D3 > 0` once `|t|` is large; for `|t| ≤ 3` the strip-slice `Set.Icc a b ×ℂ [-3,3]` is compact
and misses `ζ`'s only pole `s = 1` (because `b < 1`), so `‖ζ‖` is bounded there by continuity, and
`D1` can absorb that bound. The assembly is exactly the one sketched above: `D3 := π/(2(b-a))` (so
`D3 < π/(b-a)` with room), `D2 := 1`, and `D1 := 441875/D3⁵ + M + 1` where `M` bounds `‖(s-1)ζ(s)‖`
on the compact slice `[a,b] × [-3,3]` (`compact_slice_bound`). For `|t| ≥ 3`,
`bellotti_richert_bound` plus `‖s-1‖ ≤ 2|t|`, `4.438(1-σ)^{3/2} ≤ 3` and `(log|t|)^{2/3} ≤ log|t| ≤
|t|` give `‖(s-1)ζ(s)‖ ≤ 141.4|t|⁵`, while `exp(exp(D3|t|)) ≥ exp(D3|t|) ≥ (D3|t|)⁵/3125`
(`quintic_le_exp`) — and `141.4·3125 = 441875` is where `D1`'s first summand comes from. For `|t| ≤
3` the compact bound `M` beats `D1·exp(exp(·)) ≥ D1 ≥ M+1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bellotti_richert_bound`, `compact_slice_bound`, `quintic_le_exp`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem zeta_envelope {a b : ℝ} (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1) :
    ∃ D1 D2 D3 : ℝ, 0 < D1 ∧ 0 < D2 ∧ 0 < D3 ∧ D3 < Real.pi / (b - a) ∧
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
          < D1 * Real.exp (D2 * Real.exp (D3 * |t|)) := by
  have hpi := Real.pi_pos
  have hba : (0:ℝ) < b - a := by linarith
  set D3 : ℝ := Real.pi / (2 * (b - a)) with hD3_def
  have hD3 : 0 < D3 := by rw [hD3_def]; positivity
  have hD3b : D3 < Real.pi / (b - a) := by
    rw [hD3_def, div_lt_div_iff₀ (by positivity) hba]; nlinarith
  obtain ⟨M, hM0, hM⟩ := compact_slice_bound (a := a) hb
  -- the polynomial bound for `|t| ≥ 3`
  have hpoly : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 3 ≤ |t| →
      ‖((σ:ℂ) + t * Complex.I - 1) * riemannZeta ((σ:ℂ) + t * Complex.I)‖
        ≤ 141.4 * |t| ^ (5:ℕ) := by
    intro σ hσ t ht
    have hσ1 : (1:ℝ)/2 ≤ σ := le_trans ha hσ.1
    have hσ2 : σ ≤ 1 := le_of_lt (lt_of_le_of_lt hσ.2 hb)
    have hT1 : (1:ℝ) ≤ |t| := by linarith
    have hT0 : (0:ℝ) < |t| := by linarith
    have hbr := bellotti_richert_bound (σ := σ) (t := t) ⟨hσ1, hσ2⟩ ht
    have hs1 : ‖((σ:ℂ) + t * Complex.I - 1)‖ ≤ 2 * |t| := by
      have he : ((σ:ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ):ℂ) + (t:ℝ) * Complex.I := by
        push_cast; ring
      rw [he, Complex.norm_add_mul_I,
        show (2:ℝ) * |t| = Real.sqrt ((2*|t|)^2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_abs t, hT1]
    have hexp : |t| ^ (4.438 * (1 - σ) ^ (3/2:ℝ)) ≤ |t| ^ (3:ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      have h1 : (1 - σ) ^ (3/2:ℝ) ≤ ((1:ℝ)/2) ^ (3/2:ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have h2 : ((1:ℝ)/2) ^ (3/2:ℝ) ≤ ((1:ℝ)/2) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      rw [Real.rpow_one] at h2
      nlinarith
    have hl1 : (1:ℝ) ≤ Real.log |t| := by
      rw [Real.le_log_iff_exp_le hT0]
      linarith [Real.exp_one_lt_three]
    have hlogle : Real.log |t| ^ (2/3:ℝ) ≤ |t| := by
      have h1 : Real.log |t| ^ (2/3:ℝ) ≤ Real.log |t| ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
      rw [Real.rpow_one] at h1
      linarith [Real.log_le_sub_one_of_pos hT0]
    have hzpos : (0:ℝ) ≤ ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖ := norm_nonneg _
    have hrp3 : (0:ℝ) ≤ |t| ^ (3:ℝ) := Real.rpow_nonneg hT0.le _
    have hz : ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖ ≤ 70.7 * |t| ^ (3:ℝ) * |t| := by
      refine hbr.trans ?_
      have h1 : (70.7:ℝ) * |t| ^ (4.438 * (1 - σ) ^ (3/2:ℝ)) ≤ 70.7 * |t| ^ (3:ℝ) := by
        gcongr
      have h2 : Real.log |t| ^ (2/3:ℝ) ≤ |t| := hlogle
      have h3 : (0:ℝ) ≤ Real.log |t| ^ (2/3:ℝ) := Real.rpow_nonneg (by linarith) _
      nlinarith [h1, h2, h3, hrp3]
    rw [norm_mul]
    have hfin : (2 * |t|) * (70.7 * |t| ^ (3:ℝ) * |t|) = 141.4 * |t| ^ (5:ℕ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    calc ‖((σ:ℂ) + t * Complex.I - 1)‖ * ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖
        ≤ (2 * |t|) * (70.7 * |t| ^ (3:ℝ) * |t|) :=
          mul_le_mul hs1 hz hzpos (by positivity)
      _ = 141.4 * |t| ^ (5:ℕ) := hfin
  refine ⟨441875 / D3 ^ (5:ℕ) + M + 1, 1, D3, by positivity, one_pos, hD3, hD3b, ?_⟩
  intro σ hσ t
  have hEpos : (0:ℝ) < Real.exp (1 * Real.exp (D3 * |t|)) := Real.exp_pos _
  rcases le_or_gt 3 |t| with ht | ht
  · -- large `|t|`: the doubly-exponential envelope beats `141.4|t|^5`
    have hx : (0:ℝ) ≤ D3 * |t| := by positivity
    have h1 : (D3 * |t|) ^ (5:ℕ) / 3125 ≤ Real.exp (D3 * |t|) := quintic_le_exp hx
    have h2 : Real.exp (D3 * |t|) ≤ Real.exp (1 * Real.exp (D3 * |t|)) := by
      rw [one_mul]
      exact Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (D3 * |t|)])
    have hkey : 141.4 * |t| ^ (5:ℕ)
        ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) := by
      have he : (441875 / D3 ^ (5:ℕ)) * ((D3 * |t|) ^ (5:ℕ) / 3125) = 141.4 * |t| ^ (5:ℕ) := by
        field_simp
        ring
      calc 141.4 * |t| ^ (5:ℕ) = (441875 / D3 ^ (5:ℕ)) * ((D3 * |t|) ^ (5:ℕ) / 3125) := he.symm
        _ ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) := by
            apply mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
    have hMnn : (0:ℝ) ≤ (M + 1) * Real.exp (1 * Real.exp (D3 * |t|)) := by positivity
    have := hpoly σ hσ t ht
    nlinarith [this, hkey, hMnn, hEpos, hM0]
  · -- small `|t|`: the compact-slice bound, against `exp(exp(·)) ≥ 1`
    have htm : t ∈ Set.Icc (-3:ℝ) 3 := by
      rw [Set.mem_Icc]; constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have hMb := hM σ hσ t htm
    have hE1 : (1:ℝ) ≤ Real.exp (1 * Real.exp (D3 * |t|)) := by
      have : (0:ℝ) ≤ 1 * Real.exp (D3 * |t|) := by positivity
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (1 * Real.exp (D3 * |t|)) := Real.exp_le_exp.mpr this
    have hP : (0:ℝ) ≤ 441875 / D3 ^ (5:ℕ) := by positivity
    have hME : M ≤ M * Real.exp (1 * Real.exp (D3 * |t|)) := le_mul_of_one_le_right hM0 hE1
    have hPE : (0:ℝ) ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) :=
      mul_nonneg hP hEpos.le
    nlinarith [hMb, hE1, hM0, hME, hPE]


/-- The complete growth-hypothesis package (`hG_lower` and `hf_upper` sharing one `(C1,C2,C3)`) for
the `r = 3` family `![linG c₁ 0, linGRefl c₂ 1, GPL Q]` used by `interpolated_bound_1a`, `_1b` and
`_2`, on any strip `[a,b] ⊆ [1/2,1)`.

### Summary of Proof
The three constant lower bounds `linG_lower_const`, `linGRefl_lower_const` and `GPL_lower_const`
supply `envelope_of_const_lower`'s hypothesis, so the only genuine input left is `zeta_envelope`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_lower_const`, `envelope_of_const_lower`, `linG`,
`linGRefl`, `linGRefl_lower_const`, `linG_lower_const`, `zeta_envelope`.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`. -/
theorem exists_shared_envelope {a b c₁ c₂ Q : ℝ} (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ C3 < Real.pi / (b - a) ∧
      (∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        C1 * Real.exp (-C2 * Real.exp (C3 * |t|))
          < ‖(![linG c₁ 0, linGRefl c₂ 1, GPL Q] : Fin 3 → ℂ → ℂ) i (σ + t * Complex.I)‖) ∧
      (∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
          < C1 * Real.exp (C2 * Real.exp (C3 * |t|))) := by
  obtain ⟨D1, D2, D3, hD1, hD2, hD3, hD3b, hD⟩ := zeta_envelope hab ha hb
  -- the three constant lower bounds, then their minimum
  set m₁ : ℝ := c₁ * (0 + a) with hm₁
  set m₂ : ℝ := c₂ * (1 - b) with hm₂
  set m₃ : ℝ := (Real.log (Q + a) + Real.log (Q + 2 - b)) / 2 with hm₃
  have hm₁pos : 0 < m₁ := by
    rw [hm₁]
    have ha0 : (0:ℝ) < a := by linarith
    positivity
  have hm₂pos : 0 < m₂ := by
    rw [hm₂]; have : (0:ℝ) < 1 - b := by linarith
    positivity
  have hm₃pos : 0 < m₃ := by
    rw [hm₃]
    have h1 : 0 < Real.log (Q + a) := Real.log_pos hQa
    have h2 : 0 < Real.log (Q + 2 - b) := Real.log_pos hQb
    linarith
  set c : ℝ := min m₁ (min m₂ m₃) with hc
  have hcpos : 0 < c := lt_min hm₁pos (lt_min hm₂pos hm₃pos)
  have hGc : ∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      c ≤ ‖(![linG c₁ 0, linGRefl c₂ 1, GPL Q] : Fin 3 → ℂ → ℂ) i (σ + t * Complex.I)‖ := by
    intro i σ hσ t
    fin_cases i
    · exact le_trans (min_le_left _ _) (linG_lower_const hc₁ (by linarith) σ hσ t)
    · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
        (linGRefl_lower_const hc₂ hb σ hσ t)
    · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
        (GPL_lower_const hQa hQb σ hσ t)
  exact envelope_of_const_lower (f := fun s : ℂ => (s - 1) * riemannZeta s) _ hcpos hGc
    hD1 hD2 hD3 hD3b hD

/-! ### `G1shift`: an affine-in-`GPL` function for case (1c)'s `σ = 1/2` boundary bound

`interpolated_bound_1c`'s boundary bound at `σ = 1/2` is `A(t)|t|^{1/6}\log|t|` with
`A(t) = 0.470795+4.04972/\log|t|` genuinely `t`-dependent — not the constant-`A` shape `interpG`
below can express (see that section's docstring for why). The fix: use a *different* function at
this one boundary, `G_1(s) := c·GPL Q (s+1) + d` for constants `c,d>0`, matching
`0.470795|t|^{1/6}\log|t|+4.04972|t|^{1/6} = |t|^{1/6}(0.470795\log|t|+4.04972)` directly (no
`A(t)` needed at all — the affine structure `c\log|t|+d` is carried by `G_1` itself, not folded
back into a single multiplicative constant). The `s+1` shift re-centres `GPL Q` (symmetric about
`σ=1`) to be symmetric about `σ=0`, so that `σ∈[1/2,5/7]` sits on the *increasing* side
(`GPL_mono_of_large_t`, shifted) rather than the decreasing side plain `GPL Q` gives there. So
`G_1` is a genuinely different auxiliary function, not a workaround for `interpG`'s constant-`A`
interface. -/

/-- `G1shift Q c d s := c·GPL Q (s+1) + d`.

### Summary of Proof
A definition, not a theorem. `G1shift Q c d s = c·GPL Q(s+1) + d` is the shifted, affinely rescaled
log-type function used for case (1c)'s interpolation window, where the boundary bound is affine in
`log|t|` rather than a pure power. The `+1` shift moves `GPL`'s centre of symmetry from `σ = 1` to
`σ = 0`, so that the window `[1/2,5/7]` lies on the increasing side of it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`, `interpG1c`,
`interpG1c_prod_α`, `interpG1c_prod_β`, `interpolated_bound_1c`. -/
noncomputable def G1shift (Q c d : ℝ) : ℂ → ℂ := fun s => (c : ℂ) * GPL Q (s + 1) + (d : ℂ)

/-- `G1shift Q c d` is holomorphic on the strip `Re s ∈ [a,b]`, given `1 ≤ Q+a+1` and
`1 ≤ Q+1-b`.

### Summary of Proof
The `G1shift` analogue of `GPL_holomorphicOn`, and the `hG_holo` hypothesis of
`fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`) for the `1c` interpolation window.
**Proof.** `G1shift Q c d s = c·GPL Q (s+1) + d` is an affine function of `GPL Q ∘ (·+1)`, so it
suffices that `GPL Q` be holomorphic on the *shifted* strip `Re s ∈ [a+1,b+1]`; `Set.MapsTo`
records that `s ↦ s+1` sends one strip to the other, and the two hypotheses are exactly
`GPL_holomorphicOn`'s applied at `a+1`, `b+1`. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_holomorphicOn`.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem G1shift_holomorphicOn (Q c d a b : ℝ) (hQa : 1 ≤ Q + a + 1) (hQb : 1 ≤ Q + 1 - b) :
    DifferentiableOn ℂ (G1shift Q c d) {s : ℂ | s.re ∈ Set.Icc a b} := by
  have hmap : Set.MapsTo (fun s : ℂ => s + 1) {s : ℂ | s.re ∈ Set.Icc a b}
      {s : ℂ | s.re ∈ Set.Icc (a + 1) (b + 1)} := by
    intro s hs
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.one_re, Set.mem_Icc] at hs ⊢
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hshift : DifferentiableOn ℂ (fun s : ℂ => s + 1) {s : ℂ | s.re ∈ Set.Icc a b} :=
    (differentiable_id.add_const (1:ℂ)).differentiableOn
  have hcomp : DifferentiableOn ℂ (fun s : ℂ => GPL Q (s + 1)) {s : ℂ | s.re ∈ Set.Icc a b} :=
    (GPL_holomorphicOn Q (a + 1) (b + 1) (by linarith) (by linarith)).comp hshift hmap
  exact ((differentiableOn_const _).mul hcomp).add (differentiableOn_const _)

/-- `G1shift Q c d` commutes with complex conjugation, on the region where the underlying
`GPL Q (·+1)` stays off `Complex.log`'s branch cut.

### Summary of Proof
The `G1shift` analogue of `GPL_conj`, supplying `fiori_phragmenLindelof`'s `hG_conj` hypothesis
(`\cite[Theorem 7]{Fiori2026}`) for the `1c` window. Like `GPL_conj` — and unlike `linG_conj`
/`linGRefl_conj` — it is **conditional**: the two hypotheses `h1`/`h2` place `Q+(s+1)` and
`Q+2-(s+1)` in the right half-plane, which is what lets `Complex.log_conj` apply. See this file's
module docstring for why the unrestricted `∀ s` form is false in general for log-type `G`, and why
`fiori_phragmenLindelof` scopes its own `hG_conj` to the strip. **Proof.** Push the conjugation
through the shift (`conj
s + 1 = conj (s+1)`), apply `GPL_conj` at `s+1`, then move `conj` back out across the real scalars
`c`, `d` via `Complex.conj_ofReal`. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_conj`.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem G1shift_conj (Q c d : ℝ) (s : ℂ) (h1 : 0 < ((Q:ℂ) + (s+1)).re)
    (h2 : 0 < ((Q:ℂ) + 2 - (s+1)).re) :
    G1shift Q c d (starRingEnd ℂ s) = starRingEnd ℂ (G1shift Q c d s) := by
  have hconj1 : (starRingEnd ℂ) s + 1 = (starRingEnd ℂ) (s + 1) := by simp
  have hgpl : GPL Q ((starRingEnd ℂ) s + 1) = starRingEnd ℂ (GPL Q (s + 1)) := by
    rw [hconj1]; exact GPL_conj Q (s+1) h1 h2
  simp only [G1shift]
  rw [hgpl, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-- **Lower envelope for `G1shift`, a `t`-independent positive constant, valid for every `t`
(including
`t = 0`).** Unlike a reverse-triangle-inequality bound `‖c·w+d‖ ≥ c‖w‖-d` (which is useless here
since `d` dominates `c‖w‖` at the relevant `Q`), this goes via the real part: `Re(c·w+d) =
c·Re(w)+d` exactly, `Re(GPL Q(σ+1+it)) ≥ (log(Q+a+1)+log(Q+1-b))/2` on the shifted strip (mirroring
`GPL_lower_const`'s own derivation), and `‖·‖ ≥ Re(·)`.

### Summary of Proof
Needed for `fiori_phragmenLindelof`'s `hG_lower`, which quantifies over *all* `t : ℝ`, not just
`|t| ≥ 1` (where the weaker `G1shift_ge` would suffice).
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`.
**Used by:** `exists_shared_envelope_1c`. -/
theorem G1shift_lower_const {Q c d a b : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d) (hQa : 1 < Q + a + 1)
    (hQb : 1 < Q + 1 - b) (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    c * ((Real.log (Q + a + 1) + Real.log (Q + 1 - b)) / 2) + d
      ≤ ‖G1shift Q c d (σ + t * Complex.I)‖ := by
  set z₁ : ℂ := (Q : ℂ) + (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hz₁
  set z₂ : ℂ := (Q : ℂ) + 2 - (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hz₂
  have hre₁ : z₁.re = Q + σ + 1 := by simp [hz₁]; ring
  have hre₂ : z₂.re = Q + 1 - σ := by simp [hz₂]; ring
  have hlog₁ : Real.log (Q + a + 1) ≤ (Complex.log z₁).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + a + 1 ≤ z₁.re := by rw [hre₁]; linarith [hσ.1]
      _ ≤ ‖z₁‖ := Complex.re_le_norm z₁
  have hlog₂ : Real.log (Q + 1 - b) ≤ (Complex.log z₂).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + 1 - b ≤ z₂.re := by rw [hre₂]; linarith [hσ.2]
      _ ≤ ‖z₂‖ := Complex.re_le_norm z₂
  have hval : GPL Q (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) * (Complex.log z₁ + Complex.log z₂) := rfl
  have hReGPL : (Real.log (Q + a + 1) + Real.log (Q + 1 - b)) / 2
      ≤ (GPL Q (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [hval]; simp only [Complex.mul_re, Complex.add_re]; norm_num; linarith
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval2 : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hreG1 : (G1shift Q c d (σ + t * Complex.I)).re
      = c * (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re + d := by
    rw [hval2]; simp [Complex.add_re, Complex.mul_re]
  have hle := Complex.re_le_norm (G1shift Q c d (σ + t * Complex.I))
  rw [hreG1] at hle
  nlinarith [hReGPL, hc]

/-- **`G1shift` dominates `c·log|t|+d` at the boundary — the analogue of `GPL_ge_log`.** Since
`‖z‖ ≥ Re z` always and `Re(GPL Q(σ+1+it)) ≥ log|t|` (from the closed form `GPL_re_eq`, using
`(Q+σ)²+t², (Q+2-σ)²+t² ≥ t²`), `Re(G1shift Q c d(σ+it)) = c·Re(GPL Q(σ+1+it))+d ≥ c·log|t|+d`.

### Summary of Proof
The lower bound `c·log|t| + d ≤ ‖G1shift‖`. Since `‖z‖ ≥ Re z`, it suffices to bound the real part,
which is `c·Re GPL Q(σ+1+it) + d` by linearity. Then `Re GPL ≥ log|t|` — re-derived here from the
closed form `GPL_re_eq`, using `(Q+σ+1)²+t², (Q+1-σ)²+t² ≥ t²`, rather than by calling
`GPL_ge_log` — together with `c ≥ 0` gives the claim. This is the analogue of `GPL_ge_log` for the
shifted family, and supplies the boundary hypothesis Phragmén–Lindelöf needs at the affine edge.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_re_eq`.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem G1shift_ge (Q c d σ t : ℝ) (hc : 0 ≤ c) (_hd : 0 ≤ d) (ht : 1 ≤ |t|) :
    c * Real.log |t| + d ≤ ‖G1shift Q c d (σ + t * Complex.I)‖ := by
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hre : (G1shift Q c d (σ + t * Complex.I)).re
      = c * (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re + d := by
    rw [hval]; simp [Complex.add_re, Complex.mul_re]
  have hgre : Real.log |t| ≤ (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1 : t ^ 2 ≤ (Q + (σ + 1)) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + (σ + 1))]
    have h2 : t ^ 2 ≤ (Q + 2 - (σ + 1)) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - (σ + 1))]
    have ht0 : (0:ℝ) < t ^ 2 := by nlinarith [sq_abs t, ht]
    have hlt : Real.log (t^2) ≤ Real.log ((Q + (σ + 1)) ^ 2 + t ^ 2) := Real.log_le_log ht0 h1
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - (σ + 1)) ^ 2 + t ^ 2) := Real.log_le_log ht0 h2
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  have hle := Complex.re_le_norm (G1shift Q c d (σ + t * Complex.I))
  rw [hre] at hle
  nlinarith [hgre, hc]

/-- **Upper counterpart of `G1shift_ge`, via the plain triangle inequality** (no reverse triangle
inequality needed here, unlike `G1shift_lower_const`): `‖c·w+d‖ ≤ c‖w‖+d`, combined with
`GPL_le_log` (shifted) bounding `‖w‖ = ‖GPL Q(σ+1+it)‖` above.

### Summary of Proof
The upper counterpart of `G1shift_ge`, by the plain triangle inequality. Expand `G1shift` as `c·GPL
Q(σ+1+it) + d`, bound the norm by `c‖GPL‖ + d`, and feed in `GPL_le_log`, which controls `‖GPL‖` by
`log|t|` plus a second-order term. The two positivity hypotheses keep both of `GPL`'s logarithm
arguments in the right half-plane.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_le_log`.
**Used by:** `interpolated_bound_1c`. -/
theorem G1shift_le (Q c d σ t : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : 0 < Q + σ + 1)
    (h2 : 0 < Q + 1 - σ) (ht : 1 ≤ |t|) :
    ‖G1shift Q c d (σ + t * Complex.I)‖
      ≤ c * (Real.log |t| + ((Q+σ+1)^2 + (Q+1-σ)^2) / (4 * t^2) + |2*σ| / (2 * |t|)) + d := by
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hgle := GPL_le_log Q (σ+1) t (by linarith) (by linarith) ht
  have habs : |2 - 2*(σ+1)| = |2*σ| := by
    rw [show (2:ℝ) - 2*(σ+1) = -(2*σ) by ring, abs_neg]
  rw [habs] at hgle
  have hargeq : (Q+(σ+1))^2 + (Q+2-(σ+1))^2 = (Q+σ+1)^2 + (Q+1-σ)^2 := by ring
  rw [hargeq] at hgle
  calc ‖G1shift Q c d (σ + t * Complex.I)‖
      ≤ ‖(c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)‖ + ‖(d:ℂ)‖ := by
        rw [hval]; exact norm_add_le _ _
    _ = c * ‖GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)‖ + d := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hd]
    _ ≤ c * (Real.log |t| + ((Q+σ+1)^2 + (Q+1-σ)^2) / (4 * t^2) + |2*σ| / (2 * |t|)) + d := by
        gcongr

/-- **Tight (`O(1/t²)`) upper counterpart of `G1shift_le`**, via `GPL_le_log_tight` (shifted)
instead of `GPL_le_log` — the case (1c) analogue of the `GPL_le_log_tight` improvement, needed to
tighten `interpolated_bound_1c`'s `hG1window` the same way.

### Summary of Proof
As `G1shift_le`, but using `GPL_le_log_tight` in place of `GPL_le_log`. That replaces the
`O(1/|t|)` remainder by a genuinely `O(1/t²)` one, at the cost of the stronger hypothesis `|t| ≥
3`. This is the version the tight interpolation bounds consume, and it is what makes their errors
`O(1/t²)` rather than `O(1/t)`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_le_log_tight`.
**Used by:** `fiori_zeta_interpolation_1c_tight`. -/
theorem G1shift_le_tight (Q c d σ t : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : 0 < Q + σ + 1)
    (h2 : 0 < Q + 1 - σ) (ht : (3:ℝ) ≤ |t|) :
    ‖G1shift Q c d (σ + t * Complex.I)‖
      ≤ c * (Real.log |t|
          + (2 * ((Q+σ+1)^2 + (Q+1-σ)^2) + |2*σ|^2) / (8 * t^2)) + d := by
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hgle := GPL_le_log_tight Q (σ+1) t (by linarith) (by linarith) ht
  have habs : |2 - 2*(σ+1)| = |2*σ| := by
    rw [show (2:ℝ) - 2*(σ+1) = -(2*σ) by ring, abs_neg]
  rw [habs] at hgle
  have hargeq : (Q+(σ+1))^2 + (Q+2-(σ+1))^2 = (Q+σ+1)^2 + (Q+1-σ)^2 := by ring
  rw [hargeq] at hgle
  calc ‖G1shift Q c d (σ + t * Complex.I)‖
      ≤ ‖(c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)‖ + ‖(d:ℂ)‖ := by
        rw [hval]; exact norm_add_le _ _
    _ = c * ‖GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)‖ + d := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hd]
    _ ≤ c * (Real.log |t| + (2 * ((Q+σ+1)^2 + (Q+1-σ)^2) + |2*σ|^2) / (8 * t^2)) + d := by
        gcongr

/-- Expansion of the shifted modulus squared: `‖cw + d‖² = c²‖w‖² + 2cd·Re(w) + d²` for real
`c, d` and complex `w`.

### Summary of Proof
**Proof.** Rewrite both norms via `norm_eq_sqrt`, square away the square roots with `Real.sq_sqrt`,
expand the real and imaginary parts of `cw + d`, and finish with `ring`. **Why it is stated
separately.** This is the identity that makes `G1shift_mono_of_large_t` work: it exhibits
`‖G1shift‖²` as a sum of three terms, each nondecreasing in `σ` once `c > 0` and `d ≥ 0` — `c²‖w‖²`
by `GPL_mono_of_large_t`, `2cd·Re(w)` by `GPL_re_mono_of_large_t`, and the constant `d²`. Without
the expansion, monotonicity of `‖cw + d‖` does not follow from monotonicity of `‖w‖` alone, since
the shift by `d` can interact with the argument of `w`. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `norm_eq_sqrt`.
**Used by:** `G1shift_mono_of_large_t`. -/
private theorem normSq_c_mul_add_d (c d : ℝ) (w : ℂ) :
    ‖(c:ℂ) * w + (d:ℂ)‖ ^ 2 = c ^ 2 * ‖w‖ ^ 2 + 2 * c * d * w.re + d ^ 2 := by
  rw [norm_eq_sqrt, Real.sq_sqrt (by positivity), norm_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **`G1shift` is strictly increasing in `σ` on `[a,b]` with `0 ≤ a`, once `|t| > Q+1`** (and `0 ≤
Q`,
`0 < c`, `0 ≤ d`) — the shift means only `a+1 ≥ 1` is needed, matching where `GPL` itself is
increasing.

### Summary of Proof
Both `‖w‖` (`GPL_mono_of_large_t`, shifted) and `Re w` (`GPL_re_mono_of_large_t`, shifted) increase
in `σ`, where `w := GPL Q(σ+1+it)`; since `c > 0`, `d ≥ 0`, `‖G1shift‖² = c²‖w‖²+2cd·Re(w)+d²`
(`normSq_c_mul_add_d`) is then a sum of nondecreasing terms in `σ`, strictly so from the `‖w‖²`
term.
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_mono_of_large_t`, `GPL_re_mono_of_large_t`,
`normSq_c_mul_add_d`.
**Used by:** `interpolated_bound_1c`, `interpolated_bound_1c_tight`. -/
theorem G1shift_mono_of_large_t (Q c d a b : ℝ) (hQ : 0 ≤ Q) (hc : 0 < c) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hQb : 0 < Q + 1 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖G1shift Q c d (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t ht x hx y hy hxy
  have hmapx : x + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmapy : y + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hnormmono := GPL_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have hremono := GPL_re_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have heqx : (x:ℂ) + t * Complex.I + 1 = ((x + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have heqy : (y:ℂ) + t * Complex.I + 1 = ((y + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hvalx : G1shift Q c d (x + t * Complex.I)
      = (c:ℂ) * GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqx]
  have hvaly : G1shift Q c d (y + t * Complex.I)
      = (c:ℂ) * GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqy]
  have hwx_nn : (0:ℝ) ≤ ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ := norm_nonneg _
  have hsq : ‖G1shift Q c d (x + t * Complex.I)‖ ^ 2 < ‖G1shift Q c d (y + t * Complex.I)‖ ^ 2 := by
    rw [hvalx, hvaly, normSq_c_mul_add_d, normSq_c_mul_add_d]
    have h1 : c ^ 2 * ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2
        < c ^ 2 * ‖GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2 := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      exact pow_lt_pow_left₀ hnormmono hwx_nn (by norm_num)
    have h2 : 2 * c * d * (GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)).re
        ≤ 2 * c * d * (GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)).re := by
      rcases eq_or_lt_of_le hd with hd0 | hd0
      · simp [← hd0]
      · exact mul_le_mul_of_nonneg_left hremono.le (by positivity)
    linarith
  have hnn2 : (0:ℝ) ≤ ‖G1shift Q c d (y + t * Complex.I)‖ := norm_nonneg _
  exact lt_of_pow_lt_pow_left₀ 2 hnn2 hsq

/-! ### Fiori's Phragmén–Lindelöf theorem in the exact form applied here

`BackgroundZetaBounds`' `interpolated_bound_1a`, `_1b` and `_2` are instances of a *single*
two-point interpolation for `ζ`: a bound `A|t|^p (log|t|)^{ra}` on the line `Re s = a`, a bound
`B|t|^q (log|t|)^{rb}` on the line `Re s = b`, and the conclusion interpolating them geometrically
across the strip. Rather than re-derive that instance three times from `fiori_phragmenLindelof`
(which would mean discharging its holomorphy, conjugacy, envelope and monotonicity hypotheses
afresh each time), we record the applied form once, as `fiori_zeta_interpolation`. Case (1c)'s
boundary bound at `σ = a` has a shape this wrapper cannot express and gets its own instantiation,
`fiori_zeta_interpolation_1c`, further down. -/

/-- The `r = 3` family of auxiliary functions used to instantiate
`ExternalFacts.fiori_phragmenLindelof` in `fiori_zeta_interpolation`: `G₁ = A^{1/(p+1)}·s` carries
the power growth and the boundary constant at `σ = a`, `G₂ = (B/A^{1/(p+1)})^{1/q}·(1-s)` is its
mirror at `σ = b`, and `G₃ = GPL Q` carries the log-type factor at both ends. The exponent
`1/(p+1)` rather than `1/p`, and the compensating `A` in `G₂`'s constant, are forced by the
pole-killing `s-1` factor — see `interpα`/`interpβ` and `fiori_zeta_interpolation`.

### Summary of Proof
Named so that the compact-range hypothesis can be stated in `\cite[Theorem 7]{Fiori2026}`'s own
`min_σ |Gᵢ(σ+it)|` form.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `linG`, `linGRefl`.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`, `interpG_prod_α`,
`interpG_prod_β`, `interpolated_bound_1a_hcompact`, `interpolated_bound_1b_hcompact`,
`interpolated_bound_2_hcompact`. -/
noncomputable def interpG (A B p q Q : ℝ) : Fin 3 → ℂ → ℂ :=
  ![linG (A ^ (1 / (p + 1))) 0, linGRefl ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1, GPL Q]

/-- The exponents at `σ = a` for `interpG`.

### Summary of Proof
The `+1` on the first slot is the pole-killing factor `s - 1`: Phragmén–Lindelöf is applied to
`f(s) = (s-1)ζ(s)`, not to `ζ` — see `fiori_zeta_interpolation`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`, and the `_hcompact`
statements of `BackgroundZetaBounds`. -/
def interpα (p ra : ℝ) : Fin 3 → ℝ := ![p + 1, 0, ra]

/-- The exponents at `σ = b` for `interpG`.

### Summary of Proof
The `1` in the first slot carries the same `s - 1` factor. It has to sit on the *increasing* `G₀ =
C₀·s` rather than on the decreasing `G₁ = C₁·(1-s)`: putting it on `G₁` multiplies both sides of
the boundary hypotheses by the same `|1-s|` and is a no-op.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`, and the `_hcompact`
statements of `BackgroundZetaBounds`. -/
def interpβ (q rb : ℝ) : Fin 3 → ℝ := ![1, q, rb]

/-- The `Fin 3` product of `interpG` with the `α` exponents collapses to
`A·‖z‖^{p+1}·‖GPL Q z‖^{ra}` — this is where `(A^{1/(p+1)})^{p+1} = A` cashes in the encoding of
the boundary constant into `G₁` (and is why `0 < p` is assumed: the exponent inversion needs
`p + 1 ≠ 0`).

### Summary of Proof
Expand the `Fin 3` product with `Fin.prod_univ_three` and unfold `interpG`/`interpα`. The `α`
exponents are chosen so that the `linGRefl` factor carries exponent `0` and drops out via
`Real.rpow_zero`, while the two surviving factors combine: the constant `A^{1/(p+1)}` raised to
`p+1` returns `A`, and the `linG` factor contributes `‖z‖^{p+1}`. What remains is the `GPL` factor
with exponent `ra`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`. -/
theorem interpG_prod_α {A B p q Q : ℝ} (hA : 0 < A) (hp : 0 < p) (ra : ℝ) (z : ℂ) :
    (∏ i, ‖interpG A B p q Q i z‖ ^ interpα p ra i)
      = A * ‖z‖ ^ (p + 1) * ‖GPL Q z‖ ^ ra := by
  have hp1 : (0:ℝ) < p + 1 := by linarith
  rw [Fin.prod_univ_three]
  simp only [interpG, interpα, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, linG, linGRefl]
  rw [Real.rpow_zero, mul_one]
  have h1 : ‖((A ^ (1/(p+1)) : ℝ) : ℂ) * (((0:ℝ):ℂ) + z)‖ = A ^ (1/(p+1)) * ‖z‖ := by
    rw [Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hA _)]
  rw [h1, Real.mul_rpow (Real.rpow_pos_of_pos hA _).le (norm_nonneg _),
    ← Real.rpow_mul hA.le]
  rw [one_div, inv_mul_cancel₀ (ne_of_gt hp1), Real.rpow_one]

/-- Mirror of `interpG_prod_α` at the `b` end.

### Summary of Proof
The constant `C₁ = (B/A^{1/(p+1)})^{1/q}` is exactly what makes `C₀·C₁^q = B`, so the `A`
introduced by the `s - 1` slot cancels back out.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation`, `fiori_zeta_interpolation_tight`. -/
theorem interpG_prod_β {A B p q Q : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q)
    (rb : ℝ) (z : ℂ) :
    (∏ i, ‖interpG A B p q Q i z‖ ^ interpβ q rb i)
      = B * ‖z‖ * ‖1 - z‖ ^ q * ‖GPL Q z‖ ^ rb := by
  have hp1 : (0:ℝ) < p + 1 := by linarith
  have hC0 : (0:ℝ) < A ^ (1/(p+1)) := Real.rpow_pos_of_pos hA _
  have hC1 : (0:ℝ) < B / A ^ (1/(p+1)) := div_pos hB hC0
  rw [Fin.prod_univ_three]
  simp only [interpG, interpβ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, linG, linGRefl]
  have h0 : ‖((A ^ (1/(p+1)) : ℝ) : ℂ) * (((0:ℝ):ℂ) + z)‖ = A ^ (1/(p+1)) * ‖z‖ := by
    rw [Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hC0]
  have h1 : ‖(((B / A ^ (1/(p+1))) ^ (1/q) : ℝ) : ℂ) * (((1:ℝ):ℂ) - z)‖
      = (B / A ^ (1/(p+1))) ^ (1/q) * ‖1 - z‖ := by
    rw [Complex.ofReal_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hC1 _)]
  rw [h0, h1, Real.rpow_one,
    Real.mul_rpow (Real.rpow_pos_of_pos hC1 _).le (norm_nonneg _),
    ← Real.rpow_mul hC1.le, one_div q, inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]
  field_simp

/-- **Fiori's Phragmén–Lindelöf theorem, in the form applied in this project.** This is the exact
conclusion of the source's "Second example" (§4.2) and "Third example" (§4.3): given bounds of the
shape `A|t|^p (log|t|)^{ra}` for `ζ` on the line `Re s = a` and `B|t|^q (log|t|)^{rb}` on
`Re s = b`, `ζ` obeys the geometrically interpolated bound throughout the strip `[a,b] ⊆ [1/2,1)`.
(`interpolated_bound_1a` is the case `ra = 0, rb = 1`; `1b` and `2` are `ra = rb = 1`, which is
exactly why their `loglog|T|` coefficient is the constant `1 = w_a + w_b` rather than `1a`'s
`σ`-dependent `14/3(σ-1/2)`. Case `1c` goes through `fiori_zeta_interpolation_1c` instead, and
gets the flat coefficient `1` for the same reason.)

### Summary of Proof
Derived from `ExternalFacts.fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`) by the `r = 3`
decomposition documented at the top of this file. The proof below performs that instantiation with
`G = ![linG (A^{1/(p+1)}) 0, linGRefl ((B/A^{1/(p+1)})^{1/q}) 1, GPL Q]` (`interpG`),
`α = (p+1, 0, ra)` and `β = (1, q, rb)` (`interpα`/`interpβ`), and discharges
outright: holomorphy (`linG_holomorphicOn`/`linGRefl_holomorphicOn`/ `GPL_holomorphicOn`),
conjugate symmetry (`linG_conj`/`linGRefl_conj`/`GPL_conj`), the shared two-exponential envelope
(`exists_shared_envelope`, whose sole remaining input is `zeta_envelope`), holomorphy of `ζ` on the
strip, nonnegativity of the exponents, and the `T0 < |t|` monotonicity (`linG_mono_of_pos`,
`linGRefl_anti_of_pos`, and `hGmono`; the hypothesis `ra ≤ rb` makes `G₃`'s increasing-branch
obligation vacuous). Also discharged: the two boundary matches `hf_a`/`hf_b` (`hbound_a`/`hbound_b`
together with `|t| ≤ ‖σ+it‖` and `hGlog` for `3 ≤ |t|`, and `hcompact` for `|t| ≤ 3`, where the
interpolation exponents collapse to `αᵢ` resp. `βᵢ` at the endpoints and each `⨅` is bounded above
by its value there), and `hf_small_t`, which — now that `hcompact` is stated in `\cite[Theorem
7]{Fiori2026}`'s own `min_σ|Gᵢ(σ+it)|` form via `interpG` — is literally `hcompact`. **Applied to
`f(s) = (s-1)ζ(s)`, not to `ζ`.** This is the device `\cite[Remark 8]{Fiori2026}` points to ("one
can typically arrange for the condition for small values to be satisfied by adjusting `G` and
preserving the asymptotics"), and without it the compact-range hypothesis `hcompact` is **false**
in two of the four applications: at `t = 0` the strip meets the real segment `(0,1)`, where `ζ` is
large — unboundedly so for `interpolated_bound_2`, whose `b_k → 1` walks into `ζ`'s pole (`|ζ(b_k)|
~ (2^{k+1}-2)/(k+1)`, i.e. `185` at `k = 10` against a right-hand side near `2`). Multiplying by
`s-1` removes exactly that, since `(s-1)ζ(s) → 1` at the pole. **The extra power must sit on the
*increasing* `G₀ = C₀·s`**, giving `α = (p+1, 0, ra)`, `β = (1, q, rb)` (`interpα`/`interpβ`) with
`C₀ = A^{1/(p+1)}`, `C₁ = (B/C₀)^{1/q}` chosen so that `C₀^{p+1} = A` and `C₀·C₁^q = B`
(`interpG_prod_α`/`interpG_prod_β`). Putting it on the decreasing `G₁ = C₁(1-s)` instead is a
no-op: it multiplies both sides of every boundary hypothesis by the same `|1-s|`. The monotonicity
hypotheses still hold — `α₀ = p+1 > 1 = β₀` (increasing) and `β₁ = q > 0 = α₁` (decreasing). **The
cost is `1 + O(1/t²)` on the leading constant and nothing on any exponent.** Dividing the
conclusion back by `‖s-1‖` leaves precisely the factor `‖s‖/‖1-s‖ = √(1 + (2σ-1)/(t²+(1-σ)²)) ≤ 1 +
1/(2t²)` (`norm_ratio_window`), which at `|t| > 10¹²` is `≈ 2×10⁻²⁵` and disappears into the `(1 +
1/|t|)` slack. **Fiori's `Cᵢ(t₀) → 1` bookkeeping is carried out in full**, and it narrows the
range of validity below the source's: the conclusion holds for `|t| ≥ (Q+2)² + 55`, **not** for all
`|t| ≥ 3` as the source's headline statement suggests. Converting the `G`-shaped conclusion to
`|t|`/`log|t|` needs `‖σ+it‖, ‖1-(σ+it)‖ ≤ |t|(1 + 1/(2t²))` (`sqrt_le_window`) and `‖GPL Q(σ+it)‖
≤ log|t|·(1 + 1/(4|t|))` (`GPL_le_log`, the upper counterpart of `hGlog`), and the second of these
is *false* for small `|t|`: at `Q = 4e` and `|t| = 3`, `‖GPL‖ ≈ 2.5` against `log 3 ≈ 1.099`, a
ratio of `2.28`, nowhere near `1 + 1/3`. The two conditions that make the combined excess fit
inside the `(1 + 1/|t|)` factor are `log|t| ≥ 4` and `(Q+2)² ≤ |t|`, both implied by the stated
`(Q+2)² + 55 ≤ |t|` (`55 > e⁴ = 54.598…`). This matches the source's own §4.1 table of `Cᵢ(t₀)`
values, which is tabulated from `t₀ = 10` upward, never at `t₀ = 3` (`Cᵢ(10) < 1+4.6·10⁻²` against
`1/10`, `Cᵢ(10²) < 1+3.2·10⁻⁴` against `1/10²`, …). Every call site has `|t| > 10¹² - 1`, so
nothing downstream is affected. The hypotheses `p, q, rb ≤ 1` (satisfied in every application)
make the interpolation exponents `p·wₐ`, `q·w_b`, `ra·wₐ + rb·w_b` lie in `[0,1]`, which is what
lets each `(1+δ)^E` be absorbed as `(1+δ)`. **A known limitation of this
interface, worked around rather than removed.** Forcing the boundary bounds into the shape
`A·|t|^p·(log|t|)^r` with a *constant* `A` is less general than `\cite[Theorem 7]{Fiori2026}`, which
lets each `Gᵢ` be an arbitrary admissible function — the appendix's own case (1c) needs `G_1(s) =
0.470795·GPL(4e)(s+1) + 4.04972`, an affine function of a log, which this wrapper's constant-`A`
interface cannot express. Rather than generalizing this theorem to take the `Gᵢ` directly,
`fiori_zeta_interpolation_1c` below instantiates `ExternalFacts.fiori_phragmenLindelof` a second
time, directly, with a dedicated `r = 4` family that includes the affine `G_1`
(`PhragmenLindelofSetup.G1shift`) alongside the same `linG`/ `linGRefl`/`GPL` pieces this wrapper
uses — so this restriction is specific to *this* `r = 3` wrapper, not to what the project can
express overall. **How the four `fiori_zeta_interpolation*` variants differ** (they are
near-duplicates by construction, each a separate instantiation of
`ExternalFacts.fiori_phragmenLindelof`; they are deliberately not deduplicated, since a shared
skeleton would couple four long window-bookkeeping proofs):

| variant | `G`-family | error rate | extra hypotheses |
|---|---|---|---|
| `fiori_zeta_interpolation` | `r=3`: `linG`, `linGRefl`, `GPL` | `O(1/t)` via `GPL_le_log` | — |
| `..._tight` | same `r=3` family | `O(1/t²)` via `GPL_le_log_tight` | `T1`, `hnn` |
| `..._1c` | `r=4`: adds affine `G1shift` | `O(1/t)` via `GPL_le_log` | `hG1mono`, `hG1window` |
| `..._1c_tight` | same `r=4` family | `O(1/t²)` via `GPL_le_log_tight` | `T1`, `hnn`, `hG1mono` |

So the two axes are independent: `_tight` swaps the boundary estimate for the sharper one (and
takes an extra height parameter `T1` plus the nonnegativity hypothesis `hnn` to state it), while
`_1c` swaps the constant-`A` interface for the four-function family including `G1shift`, which is
what case (1c) of the appendix needs and this wrapper cannot express.

### References
No tex counterpart.

### Dependencies
**Depends on:** `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`), `exists_shared_envelope`,
`interpG`, `interpα`, `interpβ`, `interpG_prod_α`, `interpG_prod_β`, `linG`, `linGRefl`, `GPL` and
their `holomorphicOn`/`conj`/`mono`/`lower_const` lemmas, `GPL_le_log`.
**Used by:** `BackgroundZetaBounds.interpolated_bound_1a`, `..._1b`, `..._2`. -/
theorem fiori_zeta_interpolation {a b A B p q ra rb Q T0 : ℝ}
    (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hra : 0 ≤ ra) (hrb : 0 ≤ rb)
    (hrab : ra ≤ rb) (hT0 : 3 ≤ T0) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hrb1 : rb ≤ 1)
    (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b)
    (hGmono : ra < rb → ∀ t : ℝ, T0 < |t| →
      StrictAntiOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGlog : ∀ t : ℝ, 3 ≤ |t| → ∀ σ ∈ Set.Icc a b,
      Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖)
    (hbound_a : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (a + t * Complex.I)‖ ≤ A * |t| ^ p * Real.log |t| ^ ra)
    (hbound_b : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (b + t * Complex.I)‖ ≤ B * |t| ^ q * Real.log |t| ^ rb)
    (hcompact : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖interpG A B p q Q i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα p ra i * (b - σ) / (b - a) + interpβ q rb i * (σ - a) / (b - a))) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, (Q + 2) ^ 2 + 55 ≤ |t| →
      ‖riemannZeta (σ + t * Complex.I)‖
        ≤ (1 + 1 / |t|) * A ^ ((b - σ) / (b - a)) * B ^ ((σ - a) / (b - a))
            * |t| ^ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a)))
            * Real.log |t| ^ (ra * ((b - σ) / (b - a)) + rb * ((σ - a) / (b - a))) := by
  -- **The `r = 3` instantiation of `fiori_phragmenLindelof`.**
  -- `G₁ = A^{1/(p+1)}·s` carries the power growth and the constant at `σ = a`;
  -- `G₂ = (B/A^{1/(p+1)})^{1/q}·(1-s)` is its mirror at `σ = b`; `G₃ = GPL Q` carries the
  -- log-type factor at both ends.
  set G : Fin 3 → ℂ → ℂ := interpG A B p q Q with hG_def
  set α : Fin 3 → ℝ := interpα p ra with hα_def
  set β : Fin 3 → ℝ := interpβ q rb with hβ_def
  have hbpos : (0:ℝ) < b - a := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  have hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b} := by
    intro i
    fin_cases i
    · exact linG_holomorphicOn _ _ _ _
    · exact linGRefl_holomorphicOn _ _ _ _
    · exact GPL_holomorphicOn _ _ _ (by linarith) (by linarith)
  have hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i (starRingEnd ℂ s) = starRingEnd ℂ (G i s) := by
    intro i s hs
    simp only [Set.mem_Icc] at hs
    fin_cases i
    · exact linG_conj _ _ _
    · exact linGRefl_conj _ _ _
    · refine GPL_conj _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat] <;> linarith [hs.1, hs.2]
  have hα_nonneg : ∀ i, 0 ≤ α i := by
    intro i; fin_cases i <;> simp [hα_def, interpα] <;> linarith
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; fin_cases i <;> simp [hβ_def, interpβ] <;> linarith
  -- growth envelope: `exists_shared_envelope`, whose only remaining input is `zeta_envelope`
  have hAC : (0:ℝ) < A ^ (1 / (p + 1)) := Real.rpow_pos_of_pos hA _
  have henv := exists_shared_envelope (a := a) (b := b) (c₁ := A ^ (1 / (p + 1)))
    (c₂ := (B / A ^ (1 / (p + 1))) ^ (1 / q)) (Q := Q) hab ha hb hAC
    (Real.rpow_pos_of_pos (div_pos hB hAC) _) hQa hQb
  rw [show (![linG (A ^ (1 / (p + 1))) 0,
        linGRefl ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1, GPL Q] : Fin 3 → ℂ → ℂ)
      = G from by rw [hG_def, interpG]] at henv
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hG_lower, hf_upper⟩ := henv
  have hzeta_holo : DifferentiableOn ℂ riemannZeta {s : ℂ | s.re ∈ Set.Icc a b} := by
    apply differentiableOn_riemannZeta.mono
    rintro s hs rfl
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Complex.one_re] at hs
    linarith [hs.2]
  have hf_holo : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
      {s : ℂ | s.re ∈ Set.Icc a b} := by
    exact DifferentiableOn.mul (by fun_prop) hzeta_holo
  -- the two boundary matches: `hbound_a`/`hbound_b` for `3 ≤ |t|` (via `|t| ≤ ‖σ+it‖` and
  -- `hGlog`), and `hcompact` for `|t| ≤ 3` (where the exponents collapse to `αᵢ` resp. `βᵢ`,
  -- and each `⨅` is bounded above by its value at the endpoint).
  have hmemA : (a : ℝ) ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hmemB : (b : ℝ) ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hinf_nonneg : ∀ (i : Fin 3) (t : ℝ),
      0 ≤ ⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖ := fun i t =>
    Real.iInf_nonneg fun _ => norm_nonneg _
  have hinf_le : ∀ (i : Fin 3) (t τ : ℝ), τ ∈ Set.Icc a b →
      (⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖) ≤ ‖G i (τ + t * Complex.I)‖ := by
    intro i t τ hτ
    have hbdd : BddBelow (Set.range fun τ' : Set.Icc a b => ‖G i ((τ' : ℝ) + t * Complex.I)‖) := by
      refine ⟨0, ?_⟩
      rintro x ⟨τ', rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨τ, hτ⟩
  have habs_le : ∀ (σ t : ℝ), |t| ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ t
    rw [Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])
  -- on `|t| ≤ 3`, `hcompact`'s exponents at an endpoint collapse
  have hbane : b - a ≠ 0 := by linarith
  have hcollapseA : ∀ i : Fin 3,
      α i * (b - a) / (b - a) + β i * (a - a) / (b - a) = α i := by
    intro i; field_simp; ring
  have hcollapseB : ∀ i : Fin 3,
      α i * (b - b) / (b - a) + β i * (b - a) / (b - a) = β i := by
    intro i; field_simp; ring
  -- `‖s-1‖ ≤ ‖s‖` on `σ ≥ 1/2`, the one place `ha` is used for the pole factor
  have hsub_le : ∀ (σ : ℝ), 1/2 ≤ σ → ∀ t : ℝ,
      ‖(σ : ℂ) + t * Complex.I - 1‖ ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    have he : ((σ : ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
      push_cast; ring
    rw [he, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnormpos : ∀ (σ : ℝ), 0 < σ → ∀ t : ℝ, 0 < ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    rw [Complex.norm_add_mul_I]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hf_a : ∀ t : ℝ,
      ‖((a : ℂ) + t * Complex.I - 1) * riemannZeta (a + t * Complex.I)‖
        ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hα_def, interpG_prod_α hA hp]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(a : ℂ) + t * Complex.I‖ := hnormpos a (by linarith) t
      rw [norm_mul]
      have hstep : ‖(a : ℂ) + t * Complex.I - 1‖ * ‖riemannZeta (a + t * Complex.I)‖
          ≤ ‖(a : ℂ) + t * Complex.I‖ * (A * |t| ^ p * Real.log |t| ^ ra) :=
        mul_le_mul (hsub_le a (by linarith) t) (hbound_a t ht) (norm_nonneg _) (norm_nonneg _)
      refine hstep.trans ?_
      have hpow : ‖(a : ℂ) + t * Complex.I‖ ^ (p + 1)
          = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖ := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
      rw [hpow]
      have h1 : |t| ^ p ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p :=
        Real.rpow_le_rpow (abs_nonneg t) (habs_le a t) hp.le
      have h2 : Real.log |t| ^ ra ≤ ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra :=
        Real.rpow_le_rpow hlogpos (hGlog t ht a hmemA) hra
      have hpp : (0:ℝ) ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p := Real.rpow_nonneg hNpos.le _
      have hmul : |t| ^ p * Real.log |t| ^ ra
          ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hlogpos _) hpp
      calc ‖(a : ℂ) + t * Complex.I‖ * (A * |t| ^ p * Real.log |t| ^ ra)
          = (A * ‖(a : ℂ) + t * Complex.I‖) * (|t| ^ p * Real.log |t| ^ ra) := by ring
        _ ≤ (A * ‖(a : ℂ) + t * Complex.I‖)
              * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra) :=
            mul_le_mul_of_nonneg_left hmul (mul_nonneg hA.le hNpos.le)
        _ = A * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖)
              * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra := by ring
    · refine le_trans (hcompact t (by linarith) a hmemA).le ?_
      simp only [hcollapseA]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t a hmemA) (hα_nonneg i))
  have hf_b : ∀ t : ℝ,
      ‖((b : ℂ) + t * Complex.I - 1) * riemannZeta (b + t * Complex.I)‖
        ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hβ_def, interpG_prod_β hA hB hp hq]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(b : ℂ) + t * Complex.I‖ := hnormpos b (by linarith) t
      have hMeq : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ = ‖(b : ℂ) + t * Complex.I - 1‖ := by
        rw [← norm_neg]; congr 1; ring
      have hMpos : 0 < ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I]
        exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
      have hMle : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        rw [hMeq]; exact hsub_le b (by linarith) t
      have hTle : |t| ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - b)])
      rw [norm_mul, ← hMeq]
      -- `‖1-s‖ · B|t|^q (log|t|)^{rb} ≤ B‖s‖·‖1-s‖^q·‖GPL‖^{rb}`
      have hsplit : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
          = ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q := by
        rw [← Real.rpow_add hMpos]; norm_num
      have hkey : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
          ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        have e1 : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) :=
          Real.rpow_le_rpow (norm_nonneg _) hMle (by linarith)
        have e2 : |t| ^ q ≤ ‖(b : ℂ) + t * Complex.I‖ ^ q :=
          Real.rpow_le_rpow (abs_nonneg t) (le_trans hTle hMle) hq.le
        have e3 : ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q
            = ‖(b : ℂ) + t * Complex.I‖ := by
          rw [← Real.rpow_add hNpos]; norm_num
        calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q :=
              mul_le_mul e1 e2 (Real.rpow_nonneg (abs_nonneg t) _)
                (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖(b : ℂ) + t * Complex.I‖ := e3
      have hgl : Real.log |t| ^ rb ≤ ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb :=
        Real.rpow_le_rpow hlogpos (hGlog t ht b hmemB) hrb
      have hzb := hbound_b t ht
      have hMq : (0:ℝ) ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hstep : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
            * ‖riemannZeta ((b : ℂ) + t * Complex.I)‖
          ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t| ^ rb) :=
        mul_le_mul_of_nonneg_left hzb (norm_nonneg _)
      refine hstep.trans ?_
      calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t| ^ rb)
          = (‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q)
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q * Real.log |t| ^ rb) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ ‖(b : ℂ) + t * Complex.I‖
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
                  * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb) := by
            refine mul_le_mul hkey ?_
              (mul_nonneg (mul_nonneg hB.le hMq) (Real.rpow_nonneg hlogpos _)) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hgl (mul_nonneg hB.le hMq)
        _ = B * ‖(b : ℂ) + t * Complex.I‖ * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
              * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb := by ring
    · refine le_trans (hcompact t (by linarith) b hmemB).le ?_
      simp only [hcollapseB]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t b hmemB) (hβ_nonneg i))
  -- monotonicity at `|t| > T0`: `G₁` increasing (`linG_mono_of_pos`), `G₂` decreasing
  -- (`linGRefl_anti_of_pos`), `G₃` decreasing (`hGmono`) — and `hrab` makes `G₃`'s
  -- increasing-branch obligation vacuous.
  have hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) := by
    intro i t ht
    fin_cases i
    · exact ⟨fun _ => linG_mono_of_pos _ _ _ _ (Real.rpow_pos_of_pos hA _) (by simp; linarith) t,
        fun h => absurd h (by
          simp only [hα_def, interpα, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
            hβ_def, interpβ, add_lt_iff_neg_right, not_lt]
          exact hp.le)⟩
    · refine ⟨fun h => absurd h (by simp only [hβ_def, interpβ, Fin.mk_one, Fin.isValue,
          Matrix.cons_val_one, Matrix.cons_val_zero, hα_def, interpα, not_lt]; exact hq.le),
        fun _ => ?_⟩
      exact linGRefl_anti_of_pos ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1 a b
        (Real.rpow_pos_of_pos (div_pos hB hAC) _) hb t
    · constructor
      · intro h
        exact absurd h (by simp [hα_def, hβ_def, interpα, interpβ]; linarith)
      · intro h
        refine hGmono ?_ t ht
        simpa [hα_def, hβ_def, interpα, interpβ] using h
  -- **The compact range.** `hcompact` must be repackaged into
  -- `fiori_phragmenLindelof`'s `⨅ τ : Set.Icc a b, ‖G i((τ:ℝ)+it)‖` (subtype) form.
  have hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a)) := hcompact
  have hpl := fiori_phragmenLindelof (f := fun s : ℂ => (s - 1) * riemannZeta s)
    hab G hG_holo hG_conj hC1 hC2 hC3 hC3b
    hG_lower hf_holo hf_upper hα_nonneg hβ_nonneg hf_a hf_b hG_mono hf_small_t
  -- **Converting `hpl`'s `G`-shaped conclusion to `|t|`/`log|t|`** — Fiori's `Cᵢ(t₀) → 1`
  -- bookkeeping (§4.1), now carried out explicitly.
  intro σ hσ t hT
  obtain ⟨hσa, hσb⟩ := hσ
  have hσ : σ ∈ Set.Icc a b := ⟨hσa, hσb⟩
  have hQ0 : 0 < Q := by linarith
  set T : ℝ := |t| with hT_def
  have hMsq : (Q + 2) ^ 2 ≤ T - 55 := by linarith
  have hT55 : (55:ℝ) ≤ T := by nlinarith [sq_nonneg (Q + 2)]
  have hT0' : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  set L : ℝ := Real.log T with hL_def
  have hL4 : (4:ℝ) ≤ L := by rw [hL_def]; exact four_le_log_of_ge_fiftyfive hT55
  have hL0 : (0:ℝ) < L := by linarith
  -- the weights
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hwa0 : 0 ≤ wa := div_nonneg (by linarith) hbpos.le
  have hwb0 : 0 ≤ wb := div_nonneg (by linarith) hbpos.le
  have hwa1 : wa ≤ 1 := by rw [hwa_def, div_le_one hbpos]; linarith
  have hwb1 : wb ≤ 1 := by rw [hwb_def, div_le_one hbpos]; linarith
  have hwsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  -- the three quantities to convert
  set N1 : ℝ := ‖(σ:ℂ) + (t:ℂ) * Complex.I‖ with hN1_def
  set N2 : ℝ := ‖1 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hN2_def
  set NG : ℝ := ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNG_def
  have hN1nn : 0 ≤ N1 := norm_nonneg _
  have hN2nn : 0 ≤ N2 := norm_nonneg _
  have hNGpos : 0 < NG := lt_of_lt_of_le hL0 (hGlog t (by linarith) σ hσ)
  have hTsq : T ^ 2 = t ^ 2 := sq_abs t
  set d : ℝ := 1 / (2 * T ^ 2) with hd_def
  have hd0 : 0 ≤ d := by positivity
  have hsq1 : σ ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hsq2 : (1 - σ) ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hN1le : N1 ≤ T * (1 + d) := by
    rw [hN1_def, Complex.norm_add_mul_I, hd_def, hT_def]
    exact sqrt_le_window hT1 hsq1
  have hN2le : N2 ≤ T * (1 + d) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN2_def, he, Complex.norm_add_mul_I, hd_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact sqrt_le_window hT1 hsq2
  set e : ℝ := 1 / (4 * T) with he_def
  have he0 : 0 ≤ e := by positivity
  have hNGle : NG ≤ L * (1 + e) := by
    have hg := GPL_le_log Q σ t (by linarith) (by linarith) hT1
    rw [← hNG_def, ← hT_def, ← hL_def] at hg
    have hb1 : ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) / (4 * t ^ 2) ≤ 1 / (2 * T) := by
      rw [← hTsq]
      exact gpl_err_bound hQ0 (by linarith) (by linarith) (by linarith) hT0'
    have hb2 : |2 - 2 * σ| / (2 * T) ≤ 1 / (2 * T) := by
      have habs : |2 - 2 * σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
      gcongr
    have hLT : L * (1 + e) = L + L / (4 * T) := by
      rw [he_def, mul_add, mul_one, mul_one_div]
    have hLT2 : (1:ℝ) / T ≤ L / (4 * T) := inv_le_log_div hT0' hL4
    have hsum : 1 / (2 * T) + 1 / (2 * T) = 1 / T := two_halves_inv (ne_of_gt hT0')
    rw [hLT]
    linarith
  -- **the `rpow` bookkeeping**
  have hE1 : (0:ℝ) ≤ p * wa := mul_nonneg hp.le hwa0
  have hE1' : p * wa ≤ 1 := mul_le_one₀ hp1 hwa0 hwa1
  have hE2 : (0:ℝ) ≤ q * wb := mul_nonneg hq.le hwb0
  have hE2' : q * wb ≤ 1 := mul_le_one₀ hq1 hwb0 hwb1
  have hE3 : (0:ℝ) ≤ ra * wa + rb * wb :=
    add_nonneg (mul_nonneg hra hwa0) (mul_nonneg hrb hwb0)
  have hE3' : ra * wa + rb * wb ≤ 1 := by
    have h1 : ra * wa ≤ rb * wa := mul_le_mul_of_nonneg_right hrab hwa0
    have h2 : rb * wa + rb * wb = rb := by rw [← mul_add, hwsum, mul_one]
    linarith
  have h := hpl σ hσ t
  rw [hG_def, hα_def, hβ_def, interpG_prod_α hA hp, interpG_prod_β hA hB hp hq,
    ← hN1_def, ← hN2_def, ← hNG_def] at h
  have hnormeq : ‖((σ:ℂ) + (t:ℂ) * Complex.I - 1) * riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      = N2 * ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [norm_mul, hN2_def]
    have hn : ‖(σ:ℂ) + (t:ℂ) * Complex.I - 1‖ = ‖(1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hn]
  have htpos : (0:ℝ) < t ^ 2 := hTsq ▸ pow_pos hT0' 2
  have hN2pos : (0:ℝ) < N2 := by
    rw [hN2_def]
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    linarith [sq_nonneg (1 - σ)]
  have hN1pos : (0:ℝ) < N1 := by
    rw [hN1_def, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg σ]
  have hN1N2 : N1 ≤ N2 * (1 + d) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN1_def, hN2_def, he, Complex.norm_add_mul_I, Complex.norm_add_mul_I, hd_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact norm_ratio_window hT1 (by linarith) (by linarith)
  have hexp : (A * N1 ^ (p + 1) * NG ^ ra) ^ wa * (B * N1 * N2 ^ q * NG ^ rb) ^ wb
      = A ^ wa * B ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb)
          * NG ^ (ra * wa + rb * wb) :=
    rpow_prod_expand hA hB hN1pos hN2nn hNGpos hwsum
  rw [hnormeq, hexp] at h
  have hw1 := rpow_window hN1nn hT0'.le hd0 hN1le hE1 hE1'
  have hw2 := rpow_window hN2nn hT0'.le hd0 hN2le hE2 hE2'
  have hw3 := rpow_window hNGpos.le hL0.le he0 hNGle hE3 hE3'
  have hu : (0:ℝ) < 1 / T := div_pos one_pos hT0'
  have hu55 : (1:ℝ) / T ≤ 1 / 55 := by
    rw [div_le_div_iff₀ hT0' (by norm_num)]; linarith
  have hdu : d ≤ (1 / T) ^ 2 / 2 := le_of_eq (by rw [hd_def, d_eq (ne_of_gt hT0')])
  have heu : e ≤ (1 / T) / 4 := le_of_eq (by rw [he_def, e_eq (ne_of_gt hT0')])
  have hfour := four_factor_bound hd0 he0 hu hu55 hdu heu
  have hTadd : T ^ (p * wa + q * wb) = T ^ (p * wa) * T ^ (q * wb) := Real.rpow_add hT0' _ _
  clear_value d e L N1 N2 NG wa wb T
  have hAnn : (0:ℝ) ≤ A ^ wa := Real.rpow_nonneg hA.le _
  have hBnn : (0:ℝ) ≤ B ^ wb := Real.rpow_nonneg hB.le _
  have hT1nn : (0:ℝ) ≤ T ^ (p * wa) := Real.rpow_nonneg hT0'.le _
  have hT2nn : (0:ℝ) ≤ T ^ (q * wb) := Real.rpow_nonneg hT0'.le _
  have hLnn : (0:ℝ) ≤ L ^ (ra * wa + rb * wb) := Real.rpow_nonneg hL0.le _
  have hd1 : (0:ℝ) ≤ 1 + d := by linarith
  have he1 : (0:ℝ) ≤ 1 + e := by linarith
  have hbig : (0:ℝ)
      ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb) :=
    mul_nonneg (mul_nonneg (mul_nonneg hAnn hBnn) (mul_nonneg hT1nn hT2nn)) hLnn
  refine le_of_mul_le_mul_left (le_trans h ?_) hN2pos
  have hR1 : (0:ℝ) ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) :=
    mul_nonneg (mul_nonneg hAnn hBnn)
      (mul_nonneg (mul_nonneg hT1nn hd1) (mul_nonneg hN2pos.le hd1))
  have hR2 : (0:ℝ)
      ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) * (T ^ (q * wb) * (1 + d)) :=
    mul_nonneg hR1 (mul_nonneg hT2nn hd1)
  calc A ^ wa * B ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) * NG ^ (ra * wa + rb * wb)
      ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) * (T ^ (q * wb) * (1 + d))
          * (L ^ (ra * wa + rb * wb) * (1 + e)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ?_
          (mul_nonneg hAnn hBnn)) hw2 (Real.rpow_nonneg hN2nn _) hR1) hw3
          (Real.rpow_nonneg hNGpos.le _) hR2
        exact mul_le_mul hw1 hN1N2 hN1nn (mul_nonneg hT1nn hd1)
    _ = N2 * ((A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb))
          * ((1 + d) * (1 + d) * (1 + d) * (1 + e))) := by ring
    _ ≤ N2 * ((A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb))
          * (1 + 1 / T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfour hbig) hN2pos.le
    _ = N2 * ((1 + 1 / T) * A ^ wa * B ^ wb * T ^ (p * wa + q * wb)
          * L ^ (ra * wa + rb * wb)) := by rw [hTadd]; ring

set_option maxHeartbeats 300000 in
-- the tight log-linear finish (multiple chained `Real.log_mul`/`Real.log_rpow` rewrites) pushes
-- this past the default elaboration budget.  What runs over is `whnf` on the statement and
-- `isDefEq` on the `rpow` calc chain, not tactic search, so hinting cannot reduce it.
-- Measured: fails at 200000, passes at 300000.
/-- **Tight (`O(1/t²)`) version of `fiori_zeta_interpolation`**: the same hypotheses (in
particular the *same* `T0`, unrelated to how tight the conclusion is), plus a second height
`T1 ≥ T0` and the nonnegativity hypothesis `hnn`. The window threshold in the conclusion is then
`T1 < |t|` — not `(Q+2)²+55 ≤ |t|` — and the error is an explicit, `σ`-dependent `O(1/t²)`
quantity, stated additively, instead of the coarse multiplicative `1+1/|t|`.

### Summary of Proof
**Why `fiori_zeta_interpolation`'s `(Q+2)²+55` threshold is absent here.** That threshold is not a
consequence of `ExternalFacts.fiori_phragmenLindelof` itself (whose conclusion holds for every real
`t`, no lower bound at all) — it comes entirely from `gpl_err_bound` needing `(Q+2)² ≤ T` and from
needing `\log T ≥ 4` (`hL4`) to fold the `Re`-error into the `(1+1/|T|)`-shaped slack.
`GPL_le_log_tight`'s error term needs neither (`gpl_err_bound` is not used at all here), and the
window bookkeeping below needs nothing beyond `d ≤ 1`, itself immediate once `|t| ≥ 3` — already
guaranteed by `hT0 : 3 ≤ T0` together with `T0 < |t|`. So the thresholds surviving here are `T0`,
which the compact-range hypothesis imposes anyway, and `T1`, which the caller chooses to make
`hnn` hold. **Tight log-linear finish.** Rather than combining `(1+d)³(1+e)` into a single
polynomial slack `1+7d+8e` (`four_factor_bound_tight`, available for the multiplicative form),
this takes `Real.log` of the product directly: `3·log(1+d)+log(1+e) ≤ 3d+e`, strictly tighter (no
`7`/`8` inflation, no cross term) — the natural route of summing `cᵢ·log‖Gᵢ‖` that
`\cite{Fiori2026}`'s own Theorem 7 is stated in. Requires the extra hypothesis `hnn` (the log-sum,
excluding the `O(1/t²)` tail, is nonnegative) to handle `‖ζ‖ = 0`; there is no way around this for
a `≤`-conclusion in log form. **Place among the four variants**
(see `fiori_zeta_interpolation`'s docstring for the full table): this is the `r = 3` family
(`linG`/`linGRefl`/`GPL`, constant-`A` interface) with the *tight* `O(1/t²)` boundary estimate
`GPL_le_log_tight` in place of `GPL_le_log`, at the cost of the extra height parameter `T1` and the
nonnegativity hypothesis `hnn`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`), `exists_shared_envelope`,
`interpG`, `interpα`, `interpβ`, `interpG_prod_α`, `interpG_prod_β`, `linG`, `linGRefl`, `GPL`,
`GPL_le_log_tight`.
**Used by:** `BackgroundZetaBounds.interpolated_bound_1a_tight`, `..._1b_tight`, `..._2_tight`. -/
theorem fiori_zeta_interpolation_tight {a b A B p q ra rb Q T0 T1 : ℝ}
    (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hra : 0 ≤ ra) (hrb : 0 ≤ rb)
    (hrab : ra ≤ rb) (hT0 : 3 ≤ T0) (hT01 : T0 ≤ T1) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hrb1 : rb ≤ 1)
    (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b)
    (hGmono : ra < rb → ∀ t : ℝ, T0 < |t| →
      StrictAntiOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGlog : ∀ t : ℝ, 3 ≤ |t| → ∀ σ ∈ Set.Icc a b,
      Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖)
    (hbound_a : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (a + t * Complex.I)‖ ≤ A * |t| ^ p * Real.log |t| ^ ra)
    (hbound_b : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (b + t * Complex.I)‖ ≤ B * |t| ^ q * Real.log |t| ^ rb)
    (hcompact : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖interpG A B p q Q i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα p ra i * (b - σ) / (b - a) + interpβ q rb i * (σ - a) / (b - a)))
    (hnn : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, T1 < |t| →
      0 ≤ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a))) * Real.log |t|
          + (ra * ((b - σ) / (b - a)) + rb * ((σ - a) / (b - a))) * Real.log (Real.log |t|)
          + ((b - σ) / (b - a)) * Real.log A + ((σ - a) / (b - a)) * Real.log B) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, T1 < |t| →
      Real.log ‖riemannZeta (σ + t * Complex.I)‖
        ≤ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a))) * Real.log |t|
            + (ra * ((b - σ) / (b - a)) + rb * ((σ - a) / (b - a))) * Real.log (Real.log |t|)
            + ((b - σ) / (b - a)) * Real.log A + ((σ - a) / (b - a)) * Real.log B
            + 3 / (2 * |t| ^ 2)
            + (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2)
                / (8 * |t| ^ 2 * Real.log |t|) := by
  set G : Fin 3 → ℂ → ℂ := interpG A B p q Q with hG_def
  set α : Fin 3 → ℝ := interpα p ra with hα_def
  set β : Fin 3 → ℝ := interpβ q rb with hβ_def
  have hbpos : (0:ℝ) < b - a := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  have hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b} := by
    intro i
    fin_cases i
    · exact linG_holomorphicOn _ _ _ _
    · exact linGRefl_holomorphicOn _ _ _ _
    · exact GPL_holomorphicOn _ _ _ (by linarith) (by linarith)
  have hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i (starRingEnd ℂ s) = starRingEnd ℂ (G i s) := by
    intro i s hs
    simp only [Set.mem_Icc] at hs
    fin_cases i
    · exact linG_conj _ _ _
    · exact linGRefl_conj _ _ _
    · refine GPL_conj _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat] <;> linarith [hs.1, hs.2]
  have hα_nonneg : ∀ i, 0 ≤ α i := by
    intro i; fin_cases i <;> simp [hα_def, interpα] <;> linarith
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; fin_cases i <;> simp [hβ_def, interpβ] <;> linarith
  have hAC : (0:ℝ) < A ^ (1 / (p + 1)) := Real.rpow_pos_of_pos hA _
  have henv := exists_shared_envelope (a := a) (b := b) (c₁ := A ^ (1 / (p + 1)))
    (c₂ := (B / A ^ (1 / (p + 1))) ^ (1 / q)) (Q := Q) hab ha hb hAC
    (Real.rpow_pos_of_pos (div_pos hB hAC) _) hQa hQb
  rw [show (![linG (A ^ (1 / (p + 1))) 0,
        linGRefl ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1, GPL Q] : Fin 3 → ℂ → ℂ)
      = G from by rw [hG_def, interpG]] at henv
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hG_lower, hf_upper⟩ := henv
  have hzeta_holo : DifferentiableOn ℂ riemannZeta {s : ℂ | s.re ∈ Set.Icc a b} := by
    apply differentiableOn_riemannZeta.mono
    rintro s hs rfl
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Complex.one_re] at hs
    linarith [hs.2]
  have hf_holo : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
      {s : ℂ | s.re ∈ Set.Icc a b} := by
    exact DifferentiableOn.mul (by fun_prop) hzeta_holo
  have hmemA : (a : ℝ) ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hmemB : (b : ℝ) ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hinf_nonneg : ∀ (i : Fin 3) (t : ℝ),
      0 ≤ ⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖ := fun i t =>
    Real.iInf_nonneg fun _ => norm_nonneg _
  have hinf_le : ∀ (i : Fin 3) (t τ : ℝ), τ ∈ Set.Icc a b →
      (⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖) ≤ ‖G i (τ + t * Complex.I)‖ := by
    intro i t τ hτ
    have hbdd : BddBelow (Set.range fun τ' : Set.Icc a b => ‖G i ((τ' : ℝ) + t * Complex.I)‖) := by
      refine ⟨0, ?_⟩
      rintro x ⟨τ', rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨τ, hτ⟩
  have habs_le : ∀ (σ t : ℝ), |t| ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ t
    rw [Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])
  have hbane : b - a ≠ 0 := by linarith
  have hcollapseA : ∀ i : Fin 3,
      α i * (b - a) / (b - a) + β i * (a - a) / (b - a) = α i := by
    intro i; field_simp; ring
  have hcollapseB : ∀ i : Fin 3,
      α i * (b - b) / (b - a) + β i * (b - a) / (b - a) = β i := by
    intro i; field_simp; ring
  have hsub_le : ∀ (σ : ℝ), 1/2 ≤ σ → ∀ t : ℝ,
      ‖(σ : ℂ) + t * Complex.I - 1‖ ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    have he : ((σ : ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
      push_cast; ring
    rw [he, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnormpos : ∀ (σ : ℝ), 0 < σ → ∀ t : ℝ, 0 < ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    rw [Complex.norm_add_mul_I]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hf_a : ∀ t : ℝ,
      ‖((a : ℂ) + t * Complex.I - 1) * riemannZeta (a + t * Complex.I)‖
        ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hα_def, interpG_prod_α hA hp]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(a : ℂ) + t * Complex.I‖ := hnormpos a (by linarith) t
      rw [norm_mul]
      have hstep : ‖(a : ℂ) + t * Complex.I - 1‖ * ‖riemannZeta (a + t * Complex.I)‖
          ≤ ‖(a : ℂ) + t * Complex.I‖ * (A * |t| ^ p * Real.log |t| ^ ra) :=
        mul_le_mul (hsub_le a (by linarith) t) (hbound_a t ht) (norm_nonneg _) (norm_nonneg _)
      refine hstep.trans ?_
      have hpow : ‖(a : ℂ) + t * Complex.I‖ ^ (p + 1)
          = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖ := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
      rw [hpow]
      have h1 : |t| ^ p ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p :=
        Real.rpow_le_rpow (abs_nonneg t) (habs_le a t) hp.le
      have h2 : Real.log |t| ^ ra ≤ ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra :=
        Real.rpow_le_rpow hlogpos (hGlog t ht a hmemA) hra
      have hpp : (0:ℝ) ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p := Real.rpow_nonneg hNpos.le _
      have hmul : |t| ^ p * Real.log |t| ^ ra
          ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hlogpos _) hpp
      calc ‖(a : ℂ) + t * Complex.I‖ * (A * |t| ^ p * Real.log |t| ^ ra)
          = (A * ‖(a : ℂ) + t * Complex.I‖) * (|t| ^ p * Real.log |t| ^ ra) := by ring
        _ ≤ (A * ‖(a : ℂ) + t * Complex.I‖)
              * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra) :=
            mul_le_mul_of_nonneg_left hmul (mul_nonneg hA.le hNpos.le)
        _ = A * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖)
              * ‖GPL Q ((a : ℂ) + t * Complex.I)‖ ^ ra := by ring
    · refine le_trans (hcompact t (by linarith) a hmemA).le ?_
      simp only [hcollapseA]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t a hmemA) (hα_nonneg i))
  have hf_b : ∀ t : ℝ,
      ‖((b : ℂ) + t * Complex.I - 1) * riemannZeta (b + t * Complex.I)‖
        ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hβ_def, interpG_prod_β hA hB hp hq]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(b : ℂ) + t * Complex.I‖ := hnormpos b (by linarith) t
      have hMeq : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ = ‖(b : ℂ) + t * Complex.I - 1‖ := by
        rw [← norm_neg]; congr 1; ring
      have hMpos : 0 < ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I]
        exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
      have hMle : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        rw [hMeq]; exact hsub_le b (by linarith) t
      have hTle : |t| ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - b)])
      rw [norm_mul, ← hMeq]
      have hsplit : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
          = ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q := by
        rw [← Real.rpow_add hMpos]; norm_num
      have hkey : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
          ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        have e1 : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) :=
          Real.rpow_le_rpow (norm_nonneg _) hMle (by linarith)
        have e2 : |t| ^ q ≤ ‖(b : ℂ) + t * Complex.I‖ ^ q :=
          Real.rpow_le_rpow (abs_nonneg t) (le_trans hTle hMle) hq.le
        have e3 : ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q
            = ‖(b : ℂ) + t * Complex.I‖ := by
          rw [← Real.rpow_add hNpos]; norm_num
        calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q :=
              mul_le_mul e1 e2 (Real.rpow_nonneg (abs_nonneg t) _)
                (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖(b : ℂ) + t * Complex.I‖ := e3
      have hgl : Real.log |t| ^ rb ≤ ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb :=
        Real.rpow_le_rpow hlogpos (hGlog t ht b hmemB) hrb
      have hzb := hbound_b t ht
      have hMq : (0:ℝ) ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hstep : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
            * ‖riemannZeta ((b : ℂ) + t * Complex.I)‖
          ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t| ^ rb) :=
        mul_le_mul_of_nonneg_left hzb (norm_nonneg _)
      refine hstep.trans ?_
      calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t| ^ rb)
          = (‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q)
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q * Real.log |t| ^ rb) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ ‖(b : ℂ) + t * Complex.I‖
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
                  * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb) := by
            refine mul_le_mul hkey ?_
              (mul_nonneg (mul_nonneg hB.le hMq) (Real.rpow_nonneg hlogpos _)) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hgl (mul_nonneg hB.le hMq)
        _ = B * ‖(b : ℂ) + t * Complex.I‖ * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
              * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ ^ rb := by ring
    · refine le_trans (hcompact t (by linarith) b hmemB).le ?_
      simp only [hcollapseB]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t b hmemB) (hβ_nonneg i))
  have hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) := by
    intro i t ht
    fin_cases i
    · exact ⟨fun _ => linG_mono_of_pos _ _ _ _ (Real.rpow_pos_of_pos hA _) (by simp; linarith) t,
        fun h => absurd h (by
          simp only [hα_def, interpα, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
            hβ_def, interpβ, add_lt_iff_neg_right, not_lt]
          exact hp.le)⟩
    · refine ⟨fun h => absurd h (by simp only [hβ_def, interpβ, Fin.mk_one, Fin.isValue,
          Matrix.cons_val_one, Matrix.cons_val_zero, hα_def, interpα, not_lt]; exact hq.le),
        fun _ => ?_⟩
      exact linGRefl_anti_of_pos ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1 a b
        (Real.rpow_pos_of_pos (div_pos hB hAC) _) hb t
    · constructor
      · intro h
        exact absurd h (by simp [hα_def, hβ_def, interpα, interpβ]; linarith)
      · intro h
        refine hGmono ?_ t ht
        simpa [hα_def, hβ_def, interpα, interpβ] using h
  have hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a)) := hcompact
  have hpl := fiori_phragmenLindelof (f := fun s : ℂ => (s - 1) * riemannZeta s)
    hab G hG_holo hG_conj hC1 hC2 hC3 hC3b
    hG_lower hf_holo hf_upper hα_nonneg hβ_nonneg hf_a hf_b hG_mono hf_small_t
  -- **The tight window bookkeeping**: no `gpl_err_bound`/`hL4`/`(Q+2)²≤T` needed anywhere.
  intro σ hσ0 t hT1lt
  have hnnσt := hnn σ hσ0 t hT1lt
  have hT : T0 < |t| := by linarith
  obtain ⟨hσa, hσb⟩ := hσ0
  have hσ : σ ∈ Set.Icc a b := ⟨hσa, hσb⟩
  have hQ0 : 0 < Q := by linarith
  set T : ℝ := |t| with hT_def
  have hT0' : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT3 : (3:ℝ) ≤ T := by linarith
  set L : ℝ := Real.log T with hL_def
  have hL0 : (0:ℝ) < L := by rw [hL_def]; exact Real.log_pos (by linarith)
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hwa0 : 0 ≤ wa := div_nonneg (by linarith) hbpos.le
  have hwb0 : 0 ≤ wb := div_nonneg (by linarith) hbpos.le
  have hwa1 : wa ≤ 1 := by rw [hwa_def, div_le_one hbpos]; linarith
  have hwb1 : wb ≤ 1 := by rw [hwb_def, div_le_one hbpos]; linarith
  have hwsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  set N1 : ℝ := ‖(σ:ℂ) + (t:ℂ) * Complex.I‖ with hN1_def
  set N2 : ℝ := ‖1 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hN2_def
  set NG : ℝ := ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNG_def
  have hN1nn : 0 ≤ N1 := norm_nonneg _
  have hN2nn : 0 ≤ N2 := norm_nonneg _
  have hNGpos : 0 < NG := lt_of_lt_of_le hL0 (hGlog t (by linarith) σ hσ)
  have hTsq : T ^ 2 = t ^ 2 := sq_abs t
  set d : ℝ := 1 / (2 * T ^ 2) with hd_def
  have hd0 : 0 ≤ d := by positivity
  have hdub : d ≤ 1 := by
    rw [hd_def, div_le_one (by positivity)]
    nlinarith [hT1]
  have hsq1 : σ ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hsq2 : (1 - σ) ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hN1le : N1 ≤ T * (1 + d) := by
    rw [hN1_def, Complex.norm_add_mul_I, hd_def, hT_def]
    exact sqrt_le_window hT1 hsq1
  have hN2le : N2 ≤ T * (1 + d) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN2_def, he, Complex.norm_add_mul_I, hd_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact sqrt_le_window hT1 hsq2
  set e : ℝ := (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * T ^ 2 * L)
    with he_def
  have hLne : L ≠ 0 := hL0.ne'
  have hTne : T ≠ 0 := hT0'.ne'
  have he0 : 0 ≤ e := by
    rw [he_def]
    apply div_nonneg (by positivity)
    positivity
  have hNGle : NG ≤ L * (1 + e) := by
    have hg := GPL_le_log_tight Q σ t (by linarith) (by linarith) hT3
    rw [← hNG_def, ← hT_def] at hg
    have ht2T2 : t ^ 2 = T ^ 2 := by rw [hT_def]; exact (sq_abs t).symm
    rw [ht2T2, ← hL_def] at hg
    have heq : L * (1 + e) = L + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * T^2) := by
      rw [he_def]; field_simp
    rw [heq]; exact hg
  have hE1 : (0:ℝ) ≤ p * wa := mul_nonneg hp.le hwa0
  have hE1' : p * wa ≤ 1 := mul_le_one₀ hp1 hwa0 hwa1
  have hE2 : (0:ℝ) ≤ q * wb := mul_nonneg hq.le hwb0
  have hE2' : q * wb ≤ 1 := mul_le_one₀ hq1 hwb0 hwb1
  have hE3 : (0:ℝ) ≤ ra * wa + rb * wb :=
    add_nonneg (mul_nonneg hra hwa0) (mul_nonneg hrb hwb0)
  have hE3' : ra * wa + rb * wb ≤ 1 := by
    have h1 : ra * wa ≤ rb * wa := mul_le_mul_of_nonneg_right hrab hwa0
    have h2 : rb * wa + rb * wb = rb := by rw [← mul_add, hwsum, mul_one]
    linarith
  have h := hpl σ hσ t
  rw [hG_def, hα_def, hβ_def, interpG_prod_α hA hp, interpG_prod_β hA hB hp hq,
    ← hN1_def, ← hN2_def, ← hNG_def] at h
  have hnormeq : ‖((σ:ℂ) + (t:ℂ) * Complex.I - 1) * riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      = N2 * ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [norm_mul, hN2_def]
    have hn : ‖(σ:ℂ) + (t:ℂ) * Complex.I - 1‖ = ‖(1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hn]
  have htpos : (0:ℝ) < t ^ 2 := hTsq ▸ pow_pos hT0' 2
  have hN2pos : (0:ℝ) < N2 := by
    rw [hN2_def]
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    linarith [sq_nonneg (1 - σ)]
  have hN1pos : (0:ℝ) < N1 := by
    rw [hN1_def, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg σ]
  have hN1N2 : N1 ≤ N2 * (1 + d) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN1_def, hN2_def, he, Complex.norm_add_mul_I, Complex.norm_add_mul_I, hd_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact norm_ratio_window hT1 (by linarith) (by linarith)
  have hexp : (A * N1 ^ (p + 1) * NG ^ ra) ^ wa * (B * N1 * N2 ^ q * NG ^ rb) ^ wb
      = A ^ wa * B ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb)
          * NG ^ (ra * wa + rb * wb) :=
    rpow_prod_expand hA hB hN1pos hN2nn hNGpos hwsum
  rw [hnormeq, hexp] at h
  have hw1 := rpow_window hN1nn hT0'.le hd0 hN1le hE1 hE1'
  have hw2 := rpow_window hN2nn hT0'.le hd0 hN2le hE2 hE2'
  have hw3 := rpow_window hNGpos.le hL0.le he0 hNGle hE3 hE3'
  have hTadd : T ^ (p * wa + q * wb) = T ^ (p * wa) * T ^ (q * wb) := Real.rpow_add hT0' _ _
  have hAnn : (0:ℝ) ≤ A ^ wa := Real.rpow_nonneg hA.le _
  have hBnn : (0:ℝ) ≤ B ^ wb := Real.rpow_nonneg hB.le _
  have hT1nn : (0:ℝ) ≤ T ^ (p * wa) := Real.rpow_nonneg hT0'.le _
  have hT2nn : (0:ℝ) ≤ T ^ (q * wb) := Real.rpow_nonneg hT0'.le _
  have hLnn : (0:ℝ) ≤ L ^ (ra * wa + rb * wb) := Real.rpow_nonneg hL0.le _
  have hd1 : (0:ℝ) ≤ 1 + d := by linarith
  have he1 : (0:ℝ) ≤ 1 + e := by linarith
  have hR1 : (0:ℝ) ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) :=
    mul_nonneg (mul_nonneg hAnn hBnn)
      (mul_nonneg (mul_nonneg hT1nn hd1) (mul_nonneg hN2pos.le hd1))
  have hR2 : (0:ℝ)
      ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) * (T ^ (q * wb) * (1 + d)) :=
    mul_nonneg hR1 (mul_nonneg hT2nn hd1)
  -- **the tight step**: keep the product form `(1+d)³(1+e)` uncombined, and take `log` of it
  -- *directly* (`3·log(1+d)+log(1+e) ≤ 3d+e`) instead of first bounding the product by a single
  -- polynomial `1+7d+8e` (`four_factor_bound_tight`) — the polynomial route is strictly looser.
  have hmul : ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb)
          * ((1 + d) * (1 + d) * (1 + d) * (1 + e)) := by
    refine le_of_mul_le_mul_left (le_trans h ?_) hN2pos
    calc A ^ wa * B ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) * NG ^ (ra * wa + rb * wb)
        ≤ A ^ wa * B ^ wb * (T ^ (p * wa) * (1 + d) * (N2 * (1 + d))) * (T ^ (q * wb) * (1 + d))
            * (L ^ (ra * wa + rb * wb) * (1 + e)) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hAnn hBnn)) hw2 (Real.rpow_nonneg hN2nn _) hR1) hw3
            (Real.rpow_nonneg hNGpos.le _) hR2
          exact mul_le_mul hw1 hN1N2 hN1nn (mul_nonneg hT1nn hd1)
      _ = N2 * ((A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb))
            * ((1 + d) * (1 + d) * (1 + d) * (1 + e))) := by ring
  have hBIGpos : (0:ℝ)
      < A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb)) * L ^ (ra * wa + rb * wb) :=
    mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _))
      (mul_pos (Real.rpow_pos_of_pos hT0' _) (Real.rpow_pos_of_pos hT0' _)))
      (Real.rpow_pos_of_pos hL0 _)
  have hprodpos : (0:ℝ) < (1 + d) * (1 + d) * (1 + d) * (1 + e) := by positivity
  rcases eq_or_lt_of_le (norm_nonneg (riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I))) with hz | hz
  · rw [← hz, Real.log_zero]
    have h3d0 : (0:ℝ) ≤ 3 / (2 * T ^ 2) := by positivity
    linarith [hnnσt, he0, h3d0]
  · have hlog := Real.log_le_log hz hmul
    have hlogBIG : Real.log (A ^ wa * B ^ wb * (T ^ (p * wa) * T ^ (q * wb))
          * L ^ (ra * wa + rb * wb))
        = wa * Real.log A + wb * Real.log B + (p * wa + q * wb) * Real.log T
            + (ra * wa + rb * wb) * Real.log L := by
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hL0 _).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
        Real.log_mul (Real.rpow_pos_of_pos hT0' _).ne' (Real.rpow_pos_of_pos hT0' _).ne',
        Real.log_rpow hA, Real.log_rpow hB, Real.log_rpow hT0', Real.log_rpow hT0',
        Real.log_rpow hL0]
      ring
    rw [Real.log_mul (ne_of_gt hBIGpos) (ne_of_gt hprodpos), hlogBIG] at hlog
    have h3d : Real.log ((1 + d) * (1 + d) * (1 + d) * (1 + e)) ≤ 3 * d + e := by
      have hd1' : (0:ℝ) < 1 + d := by linarith
      have he1' : (0:ℝ) < 1 + e := by linarith
      rw [Real.log_mul (by positivity) he1'.ne', Real.log_mul (by positivity) hd1'.ne',
        Real.log_mul hd1'.ne' hd1'.ne']
      have hld : Real.log (1 + d) ≤ d := by
        calc Real.log (1 + d) ≤ (1 + d) - 1 := Real.log_le_sub_one_of_pos hd1'
          _ = d := by ring
      have hle : Real.log (1 + e) ≤ e := by
        calc Real.log (1 + e) ≤ (1 + e) - 1 := Real.log_le_sub_one_of_pos he1'
          _ = e := by ring
      linarith [hld, hle]
    have hclosed_eq : 3 * d + e = 3 / (2 * T ^ 2)
        + (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * T ^ 2 * L) := by
      rw [hd_def, he_def]
      have h8 : (8:ℝ) * T ^ 2 * L ≠ 0 := by
        have := hTne; have := hLne; positivity
      field_simp
    linarith [hlog, h3d, hclosed_eq]

/-! ### Case (1c): the `r = 4` family with `G1shift` replacing the rigid constant-`A` boundary

`interpolated_bound_1c`'s true boundary bound at `σ = a = 1/2` is
`‖ζ(1/2+it)‖ < 0.470795|t|^{1/6}\log|t| + 4.04972|t|^{1/6} = |t|^{1/6}(c\log|t|+d)`
(`ExternalFacts.hiary_revers_half_line_bound`, unconditionally for `3 ≤ |t|` — no `T`-dependent
constant anywhere), which is *not* the shape `A·|t|^p(\log|t|)^{ra}` that
`interpG`/`fiori_zeta_interpolation` demand, for a genuine reason (see that theorem's docstring):
the boundary function itself must be `G_1 = c·GPL Q(s+1)+d` (`PhragmenLindelofSetup.G1shift`),
affine in a log, not a scalar multiple of one. This section instantiates
`ExternalFacts.fiori_phragmenLindelof` directly with the `r = 4`
family `![linG 1 0, G1shift Q c d, linGRefl (B^{1/q}) 1, GPL Q]`: `G₀` carries the pole-killing
`s - 1` factor and the power growth `|t|^p` alone (no constant baked in, unlike `interpG`'s `G₀`,
since `G₁` carries the `σ = a` constant itself); `G₁ = G1shift` is the affine boundary function,
weight `1` at `a` and `0` at `b`; `G₂ = linGRefl(B^{1/q})` mirrors `interpG`'s second slot,
carrying the boundary constant `B` at `b` alone; `G₃ = GPL Q` carries the shared `\log|t|` factor,
weight `0` at `a` (subsumed into `G₁`) and `1` at `b`. -/

/-- The `r = 4` family of auxiliary functions for case (1c).

### Summary of Proof
See the module note above.
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `linG`, `linGRefl`.
**Used by:** `exists_shared_envelope_1c`, `fiori_zeta_interpolation_1c`,
`fiori_zeta_interpolation_1c_tight`, `interpG1c_prod_α`, `interpG1c_prod_β`,
`interpolated_bound_1c_hcompact`. -/
noncomputable def interpG1c (B c d q Q : ℝ) : Fin 4 → ℂ → ℂ :=
  ![linG 1 0, G1shift Q c d, linGRefl (B ^ (1 / q)) 1, GPL Q]

/-- The exponents at `σ = a` for `interpG1c`: all weight for the affine boundary function sits on
`G₁ = G1shift`, none on `G₃ = GPL Q` (unlike `interpα`, where the constant-`A` boundary needed
`GPL`'s own `\log|t|` factor via `ra`).

### Summary of Proof
A definition, not a theorem. The exponent vector at `σ = a` for case (1c)'s four-function family:
all the weight sits on the first two entries, `p+1` and `1`, with the remaining two zero. Unlike
the `r = 3` layout there is no separate constant `A`, because `G1shift` already carries both the
constant and the `log` factor.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`, and
`BackgroundZetaBounds.interpolated_bound_1c_hcompact`. -/
def interpα1c (p : ℝ) : Fin 4 → ℝ := ![p + 1, 1, 0, 0]

/-- The exponents at `σ = b` for `interpG1c`: as `interpβ` with `rb` fixed at `1` (case (1c)'s own
value) and no `G₁` contribution there.

### Summary of Proof
A definition, not a theorem. The exponent vector at `σ = b` for case (1c). It mirrors `interpβ`
with `rb` fixed at case (1c)'s own value `1`, and gives the `G1shift` entry weight `0`, since the
shifted function contributes only at the `a` end.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`, and
`BackgroundZetaBounds.interpolated_bound_1c_hcompact`. -/
def interpβ1c (q : ℝ) : Fin 4 → ℝ := ![1, 0, q, 1]

/-- The `Fin 4` product of `interpG1c` with the `α` exponents collapses to `‖z‖^{p+1}·‖G1shift z‖` —
no separate constant `A` or `\log` factor is needed at `σ = a`: `G1shift` carries both.

### Summary of Proof
Expand with `Fin.prod_univ_four` and unfold. Two of the four exponents are `0` and vanish by
`Real.rpow_zero`; one is `1` and simplifies by `Real.rpow_one`. What survives is `‖z‖^{p+1}` from
the `linG` factor and `‖G1shift z‖`, so no separate constant or `log` factor appears — `G1shift`
carries both.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem interpG1c_prod_α {B c d p q Q : ℝ} (z : ℂ) :
    (∏ i, ‖interpG1c B c d q Q i z‖ ^ interpα1c p i) = ‖z‖ ^ (p + 1) * ‖G1shift Q c d z‖ := by
  rw [Fin.prod_univ_four]
  simp only [interpG1c, interpα1c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, linG]
  rw [Real.rpow_zero, Real.rpow_zero, Real.rpow_one, mul_one, mul_one]
  congr 1
  simp [Complex.ofReal_one, Complex.ofReal_zero]

/-- Mirror of `interpG1c_prod_α` at the `b` end: collapses to `‖z‖·B·‖1-z‖^q·‖GPL Q z‖`, matching
`interpG_prod_β`'s shape with `rb = 1` and no constant carried by the `linG` slot (`interpG1c`
uses `linG 1 0`, since `G₁ = G1shift` already carries the `σ = a` constant).

### Summary of Proof
The mirror of `interpG1c_prod_α` at the `b` end. Expanding the `Fin 4` product, the `G1shift` entry
has exponent `0` and drops out, while the constant `B^{1/q}` raised to `q` returns `B`, leaving
`‖z‖·B·‖1-z‖^q·‖GPL Q z‖`. The `linGRefl` factor is what supplies `‖1-z‖`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem interpG1c_prod_β {B c d q Q : ℝ} (hB : 0 < B) (hq : 0 < q) (z : ℂ) :
    (∏ i, ‖interpG1c B c d q Q i z‖ ^ interpβ1c q i)
      = ‖z‖ * B * ‖1 - z‖ ^ q * ‖GPL Q z‖ := by
  have hC1 : (0:ℝ) < B ^ (1/q) := Real.rpow_pos_of_pos hB _
  rw [Fin.prod_univ_four]
  simp only [interpG1c, interpβ1c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, linG, linGRefl]
  rw [Real.rpow_one, Real.rpow_zero, Real.rpow_one, mul_one]
  have h0 : ‖((1:ℝ):ℂ) * (((0:ℝ):ℂ) + z)‖ = ‖z‖ := by
    rw [Complex.ofReal_zero, zero_add, Complex.ofReal_one, one_mul]
  have h1 : ‖((B ^ (1/q) : ℝ) : ℂ) * (((1:ℝ):ℂ) - z)‖ = B ^ (1/q) * ‖1 - z‖ := by
    rw [Complex.ofReal_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC1]
  rw [h0, h1, Real.mul_rpow hC1.le (norm_nonneg _), ← Real.rpow_mul hB.le,
    one_div q, inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]
  ring

/-- **Growth-envelope package for the `r = 4` family `interpG1c`.** As `exists_shared_envelope`,
reduced to `zeta_envelope` via `envelope_of_const_lower`, but with a fourth constant lower bound
(`G1shift_lower_const`, valid for *all* `t` including `t = 0`) folded into the shared minimum.

### Summary of Proof
Produces the common growth envelope `C1·exp(±C2·exp(C3|t|))` that `fiori_phragmenLindelof` demands
relate all four `Gᵢ` and `f`. Each `Gᵢ` — two linear, two log-type — is bounded below on the strip
by a positive *constant* (`linG_lower_const`, `G1shift_lower_const`, `linGRefl_lower_const`,
`GPL_lower_const`), and the minimum of the four is what `envelope_of_const_lower` consumes; the
upper half is `zeta_envelope`'s double-exponential bound for `(s-1)ζ(s)`, whose own compact part
comes from `compact_slice_bound`. `envelope_of_const_lower` then rescales the two into one shared
triple, `C1 := min c D1`, `C2 := D2 + log (D1/C1)`, `C3 := D3`, keeping `C3 < π/(b-a)`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift_lower_const`, `GPL_lower_const`,
`envelope_of_const_lower`, `interpG1c`, `linGRefl_lower_const`, `linG_lower_const`,
`zeta_envelope`.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem exists_shared_envelope_1c {a b B c d q Q : ℝ} (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hB : 0 < B) (_hq : 0 < q) (hc : 0 < c) (hd : 0 ≤ d)
    (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) (hQa1 : 1 < Q + a + 1) (hQb1 : 1 < Q + 1 - b) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ C3 < Real.pi / (b - a) ∧
      (∀ i, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        C1 * Real.exp (-C2 * Real.exp (C3 * |t|))
          < ‖interpG1c B c d q Q i (σ + t * Complex.I)‖) ∧
      (∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
          < C1 * Real.exp (C2 * Real.exp (C3 * |t|))) := by
  obtain ⟨D1, D2, D3, hD1, hD2, hD3, hD3b, hD⟩ := zeta_envelope hab ha hb
  have ha0 : (0:ℝ) < a := by linarith
  have hCb : (0:ℝ) < B ^ (1/q) := Real.rpow_pos_of_pos hB _
  have hlog1 : (0:ℝ) < (Real.log (Q+a+1) + Real.log (Q+1-b)) / 2 := by
    have h1 : (0:ℝ) < Real.log (Q+a+1) := Real.log_pos hQa1
    have h2 : (0:ℝ) < Real.log (Q+1-b) := Real.log_pos hQb1
    linarith
  have hlog2 : (0:ℝ) < (Real.log (Q+a) + Real.log (Q+2-b)) / 2 := by
    have h1 : (0:ℝ) < Real.log (Q+a) := Real.log_pos hQa
    have h2 : (0:ℝ) < Real.log (Q+2-b) := Real.log_pos hQb
    linarith
  set m1 : ℝ := (1:ℝ) * (0 + a) with hm1_def
  set m2 : ℝ := c * ((Real.log (Q+a+1) + Real.log (Q+1-b)) / 2) + d with hm2_def
  set m3 : ℝ := B ^ (1/q) * (1 - b) with hm3_def
  set m4 : ℝ := (Real.log (Q+a) + Real.log (Q+2-b)) / 2 with hm4_def
  set c0 : ℝ := min m1 (min m2 (min m3 m4)) with hc0_def
  have hm1pos : 0 < m1 := by rw [hm1_def]; nlinarith
  have hm2pos : 0 < m2 := by rw [hm2_def]; nlinarith [mul_pos hc hlog1]
  have hm3pos : 0 < m3 := by
    rw [hm3_def]; have : (0:ℝ) < 1 - b := by linarith
    positivity
  have hc0pos : 0 < c0 := lt_min hm1pos (lt_min hm2pos (lt_min hm3pos hlog2))
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hGlow, hfup⟩ :=
    envelope_of_const_lower (a := a) (b := b) (interpG1c B c d q Q)
      (f := fun s : ℂ => (s - 1) * riemannZeta s) hc0pos
      (by
        intro i σ hσ t
        fin_cases i
        · exact le_trans (min_le_left _ _)
            (linG_lower_const (Q := 0) (a := a) (b := b) one_pos (by linarith) σ hσ t)
        · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
            (G1shift_lower_const hc.le hd hQa1 hQb1 σ hσ t)
        · exact le_trans (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (min_le_left _ _))) (linGRefl_lower_const (Q := 1) (a := a) (b := b) hCb hb σ hσ t)
        · exact le_trans (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (min_le_right _ _))) (GPL_lower_const hQa hQb σ hσ t))
      hD1 hD2 hD3 hD3b hD
  exact ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hGlow, hfup⟩

/-- Analogue of `rpow_prod_expand` for case (1c)'s exponent layout: `‖G1shift‖` carries the `wa`
weight directly (no separate constant `A`), `N1` carries the extra `+1` from the pole factor.

### Summary of Proof
The case-(1c) analogue of `rpow_prod_expand`, for the four-function exponent layout. Same method:
distribute each weighted factor with `Real.mul_rpow`, legitimate since all bases are nonnegative,
then collect like powers using `wa + wb = 1`. The extra factor relative to the `r = 3` version is
the `G1shift` contribution, which appears only at the `a` end.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
private theorem rpow_prod_expand_1c {B N1 N2 NG NS p q wa wb : ℝ}
    (hB : 0 < B) (hN1 : 0 < N1) (hN2 : 0 ≤ N2) (hNG : 0 < NG) (hNS : 0 < NS)
    (hsum : wa + wb = 1) :
    (N1 ^ (p + 1) * NS) ^ wa * (N1 * B * N2 ^ q * NG) ^ wb
      = B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) := by
  have h1 : (0:ℝ) ≤ N1 ^ (p + 1) := Real.rpow_nonneg hN1.le _
  have h4 : (0:ℝ) ≤ N2 ^ q := Real.rpow_nonneg hN2 _
  rw [Real.mul_rpow h1 hNS.le, Real.mul_rpow (mul_nonneg (mul_nonneg hN1.le hB.le) h4) hNG.le,
    Real.mul_rpow (mul_nonneg hN1.le hB.le) h4, Real.mul_rpow hN1.le hB.le,
    ← Real.rpow_mul hN1.le, ← Real.rpow_mul hN2]
  have hcomb : N1 ^ ((p + 1) * wa) * N1 ^ wb = N1 ^ (p * wa) * N1 := by
    rw [← Real.rpow_add hN1, show (p + 1) * wa + wb = p * wa + 1 by linear_combination hsum,
      Real.rpow_add hN1, Real.rpow_one]
  calc N1 ^ ((p + 1) * wa) * NS ^ wa * (N1 ^ wb * B ^ wb * N2 ^ (q * wb) * NG ^ wb)
      = B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ ((p + 1) * wa) * N1 ^ wb) * N2 ^ (q * wb) := by ring
    _ = B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) := by rw [hcomb]

/-- Analogue of `four_factor_bound` with one extra window factor: `(1+d)³(1+e)(1+e₁) ≤ 1+u`,
needed because case (1c) has *two* `\log`-type window corrections (`GPL` at `b`, `G1shift` at `a`)
rather than one. The `u` budget for those two is split in half — `e, e₁ ≤ u/8` each, where
`four_factor_bound`'s single window may take `e ≤ u/4`.

### Summary of Proof
Multiplying out `(1+d)³(1+e)(1+e₁)` and bounding each cross term against the hypotheses on `d`,
`e`, `e₁` keeps the total below `1+u`: with `d ≤ u²/2` and `u ≤ 1/55` one gets `u² ≤ u/55` and
`d ≤ u/110`, so everything beyond `1 + e + e₁` is of size `O(u²)`. Discharged by `nlinarith` with
the relevant products supplied.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `fiori_zeta_interpolation_1c`. -/
private theorem five_factor_bound {d e e1 u : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (he1 : 0 ≤ e1)
    (hu : 0 < u) (hu55 : u ≤ 1 / 55) (hd' : d ≤ u ^ 2 / 2) (he' : e ≤ u / 8) (he1' : e1 ≤ u / 8) :
    (1 + d) * (1 + d) * (1 + d) * (1 + e) * (1 + e1) ≤ 1 + u := by
  have hu2 : u ^ 2 ≤ u / 55 := by nlinarith
  have hd1 : d ≤ u / 110 := by nlinarith
  nlinarith [mul_nonneg hd he, mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd,
    mul_nonneg (mul_nonneg hd hd) he, mul_nonneg (mul_nonneg (mul_nonneg hd hd) hd) he,
    mul_nonneg he he1, mul_nonneg hd he1, mul_nonneg (mul_nonneg hd hd) he1,
    mul_nonneg (mul_nonneg (mul_nonneg hd hd) hd) he1,
    mul_nonneg (mul_nonneg hd he) he1, mul_nonneg (mul_nonneg (mul_nonneg hd hd) he) he1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hd hd) hd) he) he1,
    hd1, hu2, mul_pos hu hu]

/-- **Tight** analogue of `five_factor_bound`, for the case (1c) `O(1/t²)` version: needs only
`dw ≤ 1` (automatic once `|t| ≥ 3`) and no comparison of `e`/`e1` to `1`, since `(1+e)(1+e1)` is
expanded *exactly* (`1+e+e1+e·e1`, no approximation) rather than bounded above, so no
`Q`-dependent size restriction on `e`/`e1` sneaks in through this step.

### Summary of Proof
The conclusion is a polynomial in `dw, e, e1`, not a comparison to some smaller target `u`:
`(1+dw)³ ≤ 1+7dw` from `dw ≤ 1`, after which `dw·e ≤ e`, `dw·e1 ≤ e1` and `dw·(e·e1) ≤ e·e1`
absorb the cross terms, leaving `1 + 7dw + 8e + 8e1 + 8(e·e1)`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
private theorem five_factor_bound_tight {dw e e1 : ℝ} (hdw0 : 0 ≤ dw) (hdw1 : dw ≤ 1)
    (he0 : 0 ≤ e) (he10 : 0 ≤ e1) :
    (1+dw)*(1+dw)*(1+dw)*(1+e)*(1+e1) ≤ 1 + 7*dw + 8*e + 8*e1 + 8*(e*e1) := by
  have hcube : (1+dw)*(1+dw)*(1+dw) ≤ 1 + 7*dw := by
    nlinarith [mul_nonneg hdw0 hdw0, mul_le_of_le_one_right hdw0 hdw1,
      mul_le_of_le_one_right (mul_nonneg hdw0 hdw0) hdw1]
  have hee1nn : (0:ℝ) ≤ 1 + e + e1 + e * e1 := by positivity
  have hstep : (1+dw)*(1+dw)*(1+dw)*(1+e)*(1+e1) ≤ (1+7*dw)*(1+e+e1+e*e1) := by
    have heq : (1+dw)*(1+dw)*(1+dw)*(1+e)*(1+e1)
        = ((1+dw)*(1+dw)*(1+dw))*(1+e+e1+e*e1) := by ring
    rw [heq]
    exact mul_le_mul hcube (le_refl _) hee1nn (by linarith)
  have hexpand : (1+7*dw)*(1+e+e1+e*e1)
      = 1+e+e1+e*e1+7*dw+7*(dw*e)+7*(dw*e1)+7*(dw*(e*e1)) := by ring
  rw [hexpand] at hstep
  have hde : dw*e ≤ e := mul_le_of_le_one_left he0 hdw1
  have hde1 : dw*e1 ≤ e1 := mul_le_of_le_one_left he10 hdw1
  have hdee1 : dw*(e*e1) ≤ e*e1 := mul_le_of_le_one_left (mul_nonneg he0 he10) hdw1
  linarith [hstep, hde, hde1, hdee1]

set_option maxHeartbeats 600000 in
-- the `r = 4` instantiation below is long (holomorphy/conjugacy/monotonicity dispatch on four
-- functions, plus the full window-bookkeeping conversion); the default budget is not enough.
-- The cost is `whnf` on the statement, not tactic search.  Measured: fails at 300000.
/-- **Fiori's Phragmén–Lindelöf theorem, case (1c)'s `r = 4` instantiation.** As
`fiori_zeta_interpolation`, but the boundary bound at `σ = a` is the affine-in-log
`(c·\log|t|+d)·|t|^p` that the source's own `G_1(s) = c·GPL Q(s+1)+d` (`G1shift`) realizes
directly — see this file's `### Case (1c)` section above for why `interpG`'s rigid constant-`A`
shape cannot express this. `hG1window` is a further obligation on the caller, alongside
`hbound_a`/`hbound_b`/`hcompact`: a triangle-inequality slack bound on `G1shift`, easiest to
discharge with the caller's *concrete* `Q, a, b, c, d` in hand (`G1shift_le` plus `norm_num`),
rather than re-derived generically here.

### Summary of Proof
**Place among the four variants** (see `fiori_zeta_interpolation`'s docstring for the full table):
this is the `r = 4` family — `linG`, `linGRefl`, `GPL` *plus* the affine `G1shift` — with the plain
`O(1/t)` boundary estimate `GPL_le_log`. The `r = 4` family exists precisely because case (1c)
needs `G_1(s) = 0.470795·GPL(4e)(s+1) + 4.04972`, which the `r = 3` wrapper's constant-`A`
interface cannot express.

### References
No tex counterpart.

### Dependencies
**Depends on:** `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`),
`exists_shared_envelope_1c`, `interpG1c`, `interpα1c`, `interpβ1c`, `interpG1c_prod_α`,
`interpG1c_prod_β`, `G1shift` and its `holomorphicOn`/`conj`/`ge` lemmas, `linG`, `linGRefl`,
`GPL`, `GPL_le_log`.
**Used by:** `BackgroundZetaBounds.interpolated_bound_1c`. -/
theorem fiori_zeta_interpolation_1c {a b B c d p q Q T0 : ℝ}
    (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hc : 0 < c) (hd : 0 ≤ d)
    (hT0 : 3 ≤ T0) (hp1 : p ≤ 1) (hq1 : q ≤ 1)
    (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) (hQa1 : 1 < Q + a + 1) (hQb1 : 1 < Q + 1 - b)
    (hG1mono : ∀ t : ℝ, T0 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖G1shift Q c d (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGmono : ∀ t : ℝ, T0 < |t| →
      StrictAntiOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGlog : ∀ t : ℝ, 3 ≤ |t| → ∀ σ ∈ Set.Icc a b,
      Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖)
    (hbound_a : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (a + t * Complex.I)‖ ≤ (c * Real.log |t| + d) * |t| ^ p)
    (hbound_b : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (b + t * Complex.I)‖ ≤ B * |t| ^ q * Real.log |t|)
    (hG1window : ∀ t : ℝ, (Q + 2) ^ 2 + 110 ≤ |t| → ∀ σ ∈ Set.Icc a b,
      ‖G1shift Q c d (σ + t * Complex.I)‖ ≤ (c * Real.log |t| + d) * (1 + 1 / (4 * |t|)))
    (hcompact : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖interpG1c B c d q Q i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα1c p i * (b - σ) / (b - a) + interpβ1c q i * (σ - a) / (b - a))) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, (Q + 2) ^ 2 + 110 ≤ |t| →
      ‖riemannZeta (σ + t * Complex.I)‖
        ≤ (1 + 2 / |t|) * (c * Real.log |t| + d) ^ ((b - σ) / (b - a))
            * B ^ ((σ - a) / (b - a))
            * |t| ^ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a)))
            * Real.log |t| ^ ((σ - a) / (b - a)) := by
  set G : Fin 4 → ℂ → ℂ := interpG1c B c d q Q with hG_def
  set α : Fin 4 → ℝ := interpα1c p with hα_def
  set β : Fin 4 → ℝ := interpβ1c q with hβ_def
  have hbpos : (0:ℝ) < b - a := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  have hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b} := by
    intro i
    fin_cases i
    · exact linG_holomorphicOn _ _ _ _
    · exact G1shift_holomorphicOn _ _ _ _ _ (by linarith) (by linarith)
    · exact linGRefl_holomorphicOn _ _ _ _
    · exact GPL_holomorphicOn _ _ _ (by linarith) (by linarith)
  have hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i (starRingEnd ℂ s) = starRingEnd ℂ (G i s) := by
    intro i s hs
    simp only [Set.mem_Icc] at hs
    fin_cases i
    · exact linG_conj _ _ _
    · refine G1shift_conj _ _ _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat, Complex.one_re] <;> linarith [hs.1, hs.2]
    · exact linGRefl_conj _ _ _
    · refine GPL_conj _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat] <;> linarith [hs.1, hs.2]
  have hα_nonneg : ∀ i, 0 ≤ α i := by
    intro i; fin_cases i <;> simp [hα_def, interpα1c]; linarith
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; fin_cases i <;> simp [hβ_def, interpβ1c]; linarith
  have henv := exists_shared_envelope_1c (a := a) (b := b) (B := B) (c := c) (d := d) (q := q)
    (Q := Q) hab ha hb hB hq hc hd hQa hQb hQa1 hQb1
  rw [show interpG1c B c d q Q = G from hG_def.symm] at henv
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hG_lower, hf_upper⟩ := henv
  have hzeta_holo : DifferentiableOn ℂ riemannZeta {s : ℂ | s.re ∈ Set.Icc a b} := by
    apply differentiableOn_riemannZeta.mono
    rintro s hs rfl
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Complex.one_re] at hs
    linarith [hs.2]
  have hf_holo : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
      {s : ℂ | s.re ∈ Set.Icc a b} := DifferentiableOn.mul (by fun_prop) hzeta_holo
  have hmemA : (a : ℝ) ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hmemB : (b : ℝ) ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hinf_nonneg : ∀ (i : Fin 4) (t : ℝ),
      0 ≤ ⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖ := fun i t =>
    Real.iInf_nonneg fun _ => norm_nonneg _
  have hinf_le : ∀ (i : Fin 4) (t τ : ℝ), τ ∈ Set.Icc a b →
      (⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖) ≤ ‖G i (τ + t * Complex.I)‖ := by
    intro i t τ hτ
    have hbdd : BddBelow (Set.range fun τ' : Set.Icc a b => ‖G i ((τ' : ℝ) + t * Complex.I)‖) := by
      refine ⟨0, ?_⟩
      rintro x ⟨τ', rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨τ, hτ⟩
  have habs_le : ∀ (σ t : ℝ), |t| ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ t
    rw [Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])
  have hbane : b - a ≠ 0 := by linarith
  have hcollapseA : ∀ i : Fin 4,
      α i * (b - a) / (b - a) + β i * (a - a) / (b - a) = α i := by
    intro i; field_simp; ring
  have hcollapseB : ∀ i : Fin 4,
      α i * (b - b) / (b - a) + β i * (b - a) / (b - a) = β i := by
    intro i; field_simp; ring
  have hsub_le : ∀ (σ : ℝ), 1/2 ≤ σ → ∀ t : ℝ,
      ‖(σ : ℂ) + t * Complex.I - 1‖ ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    have he : ((σ : ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
      push_cast; ring
    rw [he, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnormpos : ∀ (σ : ℝ), 0 < σ → ∀ t : ℝ, 0 < ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    rw [Complex.norm_add_mul_I]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hf_a : ∀ t : ℝ,
      ‖((a : ℂ) + t * Complex.I - 1) * riemannZeta (a + t * Complex.I)‖
        ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hα_def, interpG1c_prod_α]
      have hNpos : 0 < ‖(a : ℂ) + t * Complex.I‖ := hnormpos a (by linarith) t
      rw [norm_mul]
      have hstep : ‖(a : ℂ) + t * Complex.I - 1‖ * ‖riemannZeta (a + t * Complex.I)‖
          ≤ ‖(a : ℂ) + t * Complex.I‖ * ((c * Real.log |t| + d) * |t| ^ p) :=
        mul_le_mul (hsub_le a (by linarith) t) (hbound_a t ht) (norm_nonneg _) (norm_nonneg _)
      refine hstep.trans ?_
      have hpow : ‖(a : ℂ) + t * Complex.I‖ ^ (p + 1)
          = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖ := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
      rw [hpow]
      have h1 : |t| ^ p ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p :=
        Real.rpow_le_rpow (abs_nonneg t) (habs_le a t) hp.le
      have h2 : c * Real.log |t| + d ≤ ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ :=
        G1shift_ge Q c d a t hc.le hd (by linarith)
      have hcd0 : (0:ℝ) ≤ c * Real.log |t| + d :=
        add_nonneg (mul_nonneg hc.le (Real.log_nonneg (by linarith))) hd
      have hpp : (0:ℝ) ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p := Real.rpow_nonneg hNpos.le _
      have hmul : |t| ^ p * (c * Real.log |t| + d)
          ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ :=
        mul_le_mul h1 h2 hcd0 hpp
      calc ‖(a : ℂ) + t * Complex.I‖ * ((c * Real.log |t| + d) * |t| ^ p)
          = ‖(a : ℂ) + t * Complex.I‖ * (|t| ^ p * (c * Real.log |t| + d)) := by ring
        _ ≤ ‖(a : ℂ) + t * Complex.I‖
              * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖) :=
            mul_le_mul_of_nonneg_left hmul hNpos.le
        _ = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖
              * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ := by ring
    · refine le_trans (hcompact t (by linarith) a hmemA).le ?_
      simp only [hcollapseA]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t a hmemA) (hα_nonneg i))
  have hf_b : ∀ t : ℝ,
      ‖((b : ℂ) + t * Complex.I - 1) * riemannZeta (b + t * Complex.I)‖
        ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hβ_def, interpG1c_prod_β hB hq]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(b : ℂ) + t * Complex.I‖ := hnormpos b (by linarith) t
      have hMeq : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ = ‖(b : ℂ) + t * Complex.I - 1‖ := by
        rw [← norm_neg]; congr 1; ring
      have hMpos : 0 < ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I]
        exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
      have hMle : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        rw [hMeq]; exact hsub_le b (by linarith) t
      have hTle : |t| ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - b)])
      rw [norm_mul, ← hMeq]
      have hsplit : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
          = ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q := by
        rw [← Real.rpow_add hMpos]; norm_num
      have hkey : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
          ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        have e1 : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) :=
          Real.rpow_le_rpow (norm_nonneg _) hMle (by linarith)
        have e2 : |t| ^ q ≤ ‖(b : ℂ) + t * Complex.I‖ ^ q :=
          Real.rpow_le_rpow (abs_nonneg t) (le_trans hTle hMle) hq.le
        have e3 : ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q
            = ‖(b : ℂ) + t * Complex.I‖ := by
          rw [← Real.rpow_add hNpos]; norm_num
        calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q :=
              mul_le_mul e1 e2 (Real.rpow_nonneg (abs_nonneg t) _)
                (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖(b : ℂ) + t * Complex.I‖ := e3
      have hgl : Real.log |t| ≤ ‖GPL Q ((b : ℂ) + t * Complex.I)‖ := hGlog t ht b hmemB
      have hzb := hbound_b t ht
      have hMq : (0:ℝ) ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hstep : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
            * ‖riemannZeta ((b : ℂ) + t * Complex.I)‖
          ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hzb (norm_nonneg _)
      refine hstep.trans ?_
      calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t|)
          = (‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q)
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q * Real.log |t|) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ ‖(b : ℂ) + t * Complex.I‖
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
                  * ‖GPL Q ((b : ℂ) + t * Complex.I)‖) := by
            refine mul_le_mul hkey ?_
              (mul_nonneg (mul_nonneg hB.le hMq) hlogpos) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hgl (mul_nonneg hB.le hMq)
        _ = ‖(b : ℂ) + t * Complex.I‖ * B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
              * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ := by ring
    · refine le_trans (hcompact t (by linarith) b hmemB).le ?_
      simp only [hcollapseB]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t b hmemB) (hβ_nonneg i))
  have hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) := by
    intro i t ht
    fin_cases i <;> simp only [hα_def, hβ_def, interpα1c, interpβ1c, Fin.isValue, Fin.zero_eta,
      Matrix.cons_val_zero, lt_add_iff_pos_left, add_lt_iff_neg_right, Fin.mk_one,
      Matrix.cons_val_one, zero_lt_one, forall_const, isEmpty_Prop, not_lt, zero_le_one,
      IsEmpty.forall_iff, and_true, Fin.reduceFinMk, Matrix.cons_val, true_and]
    · exact ⟨fun _ => linG_mono_of_pos _ _ _ _ one_pos (by linarith) t,
        fun h => absurd h (by linarith)⟩
    · exact hG1mono t ht
    · exact ⟨fun h => absurd h (by linarith), fun _ =>
        linGRefl_anti_of_pos (B ^ (1/q)) 1 a b (Real.rpow_pos_of_pos hB _) hb t⟩
    · exact hGmono t ht
  have hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a)) := hcompact
  have hpl := fiori_phragmenLindelof (f := fun s : ℂ => (s - 1) * riemannZeta s)
    hab G hG_holo hG_conj hC1 hC2 hC3 hC3b
    hG_lower hf_holo hf_upper hα_nonneg hβ_nonneg hf_a hf_b hG_mono hf_small_t
  intro σ hσ t hT
  obtain ⟨hσa, hσb⟩ := hσ
  have hσ : σ ∈ Set.Icc a b := ⟨hσa, hσb⟩
  have hQ0 : 0 < Q := by linarith
  set T : ℝ := |t| with hT_def
  have hMsq : (Q + 2) ^ 2 ≤ T - 110 := by linarith
  have hT55 : (110:ℝ) ≤ T := by nlinarith [sq_nonneg (Q + 2)]
  have hT0' : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  set L : ℝ := Real.log T with hL_def
  have hL4 : (4:ℝ) ≤ L := by rw [hL_def]; exact four_le_log_of_ge_fiftyfive (by linarith)
  have hL0 : (0:ℝ) < L := by linarith
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hwa0 : 0 ≤ wa := div_nonneg (by linarith) hbpos.le
  have hwb0 : 0 ≤ wb := div_nonneg (by linarith) hbpos.le
  have hwa1 : wa ≤ 1 := by rw [hwa_def, div_le_one hbpos]; linarith
  have hwb1 : wb ≤ 1 := by rw [hwb_def, div_le_one hbpos]; linarith
  have hwsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  set N1 : ℝ := ‖(σ:ℂ) + (t:ℂ) * Complex.I‖ with hN1_def
  set N2 : ℝ := ‖1 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hN2_def
  set NG : ℝ := ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNG_def
  set NS : ℝ := ‖G1shift Q c d ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNS_def
  have hN1nn : 0 ≤ N1 := norm_nonneg _
  have hN2nn : 0 ≤ N2 := norm_nonneg _
  have hNGpos : 0 < NG := lt_of_lt_of_le hL0 (hGlog t (by linarith) σ hσ)
  have hNSpos : 0 < NS := by
    rw [hNS_def]
    calc (0:ℝ) < c * Real.log |t| + d := by
          have : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by rw [← hT_def]; linarith)
          nlinarith [mul_nonneg hc.le this]
      _ ≤ _ := G1shift_ge Q c d σ t hc.le hd (by rw [← hT_def]; linarith)
  have hTsq : T ^ 2 = t ^ 2 := sq_abs t
  set dw : ℝ := 1 / (2 * T ^ 2) with hdw_def
  have hdw0 : 0 ≤ dw := by positivity
  have hsq1 : σ ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hsq2 : (1 - σ) ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hN1le : N1 ≤ T * (1 + dw) := by
    rw [hN1_def, Complex.norm_add_mul_I, hdw_def, hT_def]
    exact sqrt_le_window hT1 hsq1
  have hN2le : N2 ≤ T * (1 + dw) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN2_def, he, Complex.norm_add_mul_I, hdw_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact sqrt_le_window hT1 hsq2
  set e : ℝ := 1 / (4 * T) with he_def
  have he0 : 0 ≤ e := by positivity
  have hNGle : NG ≤ L * (1 + e) := by
    have hg := GPL_le_log Q σ t (by linarith) (by linarith) hT1
    rw [← hNG_def, ← hT_def, ← hL_def] at hg
    have hb1 : ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) / (4 * t ^ 2) ≤ 1 / (2 * T) := by
      rw [← hTsq]
      exact gpl_err_bound hQ0 (by linarith) (by linarith) (by linarith) hT0'
    have hb2 : |2 - 2 * σ| / (2 * T) ≤ 1 / (2 * T) := by
      have habs : |2 - 2 * σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
      gcongr
    have hLT : L * (1 + e) = L + L / (4 * T) := by
      rw [he_def, mul_add, mul_one, mul_one_div]
    have hLT2 : (1:ℝ) / T ≤ L / (4 * T) := inv_le_log_div hT0' hL4
    have hsum : 1 / (2 * T) + 1 / (2 * T) = 1 / T := two_halves_inv (ne_of_gt hT0')
    rw [hLT]
    linarith
  set e1 : ℝ := 1 / (4 * T) with he1_def
  have he10 : 0 ≤ e1 := by positivity
  have hNSle : NS ≤ (c * L + d) * (1 + e1) := by
    have hg1 := hG1window t hT σ hσ
    rw [← hT_def, ← hL_def, ← he1_def] at hg1
    rw [hNS_def]
    exact hg1
  have hE1 : (0:ℝ) ≤ p * wa := mul_nonneg hp.le hwa0
  have hE1' : p * wa ≤ 1 := mul_le_one₀ hp1 hwa0 hwa1
  have hE2 : (0:ℝ) ≤ q * wb := mul_nonneg hq.le hwb0
  have hE2' : q * wb ≤ 1 := mul_le_one₀ hq1 hwb0 hwb1
  have h := hpl σ hσ t
  rw [hG_def, hα_def, hβ_def, interpG1c_prod_α, interpG1c_prod_β hB hq,
    ← hN1_def, ← hN2_def, ← hNG_def, ← hNS_def] at h
  have hnormeq : ‖((σ:ℂ) + (t:ℂ) * Complex.I - 1) * riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      = N2 * ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [norm_mul, hN2_def]
    have hn : ‖(σ:ℂ) + (t:ℂ) * Complex.I - 1‖ = ‖(1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hn]
  have htpos : (0:ℝ) < t ^ 2 := hTsq ▸ pow_pos hT0' 2
  have hN2pos : (0:ℝ) < N2 := by
    rw [hN2_def]
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    linarith [sq_nonneg (1 - σ)]
  have hN1pos : (0:ℝ) < N1 := by
    rw [hN1_def, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg σ]
  have hN1N2 : N1 ≤ N2 * (1 + dw) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN1_def, hN2_def, he, Complex.norm_add_mul_I, Complex.norm_add_mul_I, hdw_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact norm_ratio_window hT1 (by linarith) (by linarith)
  have hexp : (N1 ^ (p + 1) * NS) ^ wa * (N1 * B * N2 ^ q * NG) ^ wb
      = B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) :=
    rpow_prod_expand_1c hB hN1pos hN2nn hNGpos hNSpos hwsum
  rw [hnormeq, hexp] at h
  have hw1 := rpow_window hN1nn hT0'.le hdw0 hN1le hE1 hE1'
  have hw2 := rpow_window hN2nn hT0'.le hdw0 hN2le hE2 hE2'
  have hw3 := rpow_window hNGpos.le hL0.le he0 hNGle hwb0 hwb1
  have hw4 : NS ^ wa ≤ (c * L + d) ^ wa * (1 + e1) :=
    rpow_window hNSpos.le (by positivity) he10 hNSle hwa0 hwa1
  have hu : (0:ℝ) < 2 / T := by positivity
  have hu55 : (2:ℝ) / T ≤ 1 / 55 := by
    rw [div_le_div_iff₀ hT0' (by norm_num)]; linarith
  have hdwu : dw ≤ (2 / T) ^ 2 / 2 := by
    change (1 / (2 * T ^ 2) : ℝ) ≤ (2/T)^2/2
    have heq : (2/T:ℝ)^2/2 = 2 / T^2 := by field_simp
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg T]
  have heu : e ≤ (2 / T) / 8 := by
    change (1 / (4 * T) : ℝ) ≤ (2/T)/8
    linarith [(by ring : (1 / (4 * T) : ℝ) = (2/T)/8)]
  have he1u : e1 ≤ (2 / T) / 8 := by
    change (1 / (4 * T) : ℝ) ≤ (2/T)/8
    linarith [(by ring : (1 / (4 * T) : ℝ) = (2/T)/8)]
  have hfive := five_factor_bound hdw0 he0 he10 hu hu55 hdwu heu he1u
  have hTadd : T ^ (p * wa + q * wb) = T ^ (p * wa) * T ^ (q * wb) := Real.rpow_add hT0' _ _
  clear_value dw e e1 L N1 N2 NG NS wa wb T
  have hBnn : (0:ℝ) ≤ B ^ wb := Real.rpow_nonneg hB.le _
  have hT1nn : (0:ℝ) ≤ T ^ (p * wa) := Real.rpow_nonneg hT0'.le _
  have hT2nn : (0:ℝ) ≤ T ^ (q * wb) := Real.rpow_nonneg hT0'.le _
  have hLnn : (0:ℝ) ≤ L ^ wb := Real.rpow_nonneg hL0.le _
  have hcdnn : (0:ℝ) ≤ (c * L + d) ^ wa := Real.rpow_nonneg (by positivity) _
  have hdw1 : (0:ℝ) ≤ 1 + dw := by linarith
  have he1' : (0:ℝ) ≤ 1 + e := by linarith
  have hee1' : (0:ℝ) ≤ 1 + e1 := by linarith
  have hbig : (0:ℝ)
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb :=
    mul_nonneg (mul_nonneg (mul_nonneg hBnn hcdnn) (mul_nonneg hT1nn hT2nn)) hLnn
  refine le_of_mul_le_mul_left (le_trans h ?_) hN2pos
  have hR1 : (0:ℝ)
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw))) :=
    mul_nonneg (mul_nonneg hBnn hcdnn)
      (mul_nonneg (mul_nonneg hT1nn hdw1) (mul_nonneg hN2pos.le hdw1))
  have hR2 : (0:ℝ)
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw)))
          * (T ^ (q * wb) * (1 + dw)) :=
    mul_nonneg hR1 (mul_nonneg hT2nn hdw1)
  calc B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb)
      ≤ B ^ wb * ((c * L + d) ^ wa * (1 + e1)) * (L ^ wb * (1 + e))
          * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw))) * (T ^ (q * wb) * (1 + dw)) := by
        have h1 : N1 ^ (p * wa) * N1 ≤ T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw)) :=
          mul_le_mul hw1 hN1N2 hN1nn (mul_nonneg hT1nn hdw1)
        have h2 : NS ^ wa ≤ (c * L + d) ^ wa * (1 + e1) := hw4
        have h3 : NG ^ wb ≤ L ^ wb * (1 + e) := hw3
        have h4 : N2 ^ (q * wb) ≤ T ^ (q * wb) * (1 + dw) := hw2
        have hB' : (0:ℝ) ≤ B ^ wb := hBnn
        gcongr
    _ = N2 * ((B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb)
          * ((1 + dw) * (1 + dw) * (1 + dw) * (1 + e) * (1 + e1))) := by ring
    _ ≤ N2 * ((B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb)
          * (1 + 2 / T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfive hbig) hN2pos.le
    _ = N2 * ((1 + 2 / T) * (c * L + d) ^ wa * B ^ wb * T ^ (p * wa + q * wb)
          * L ^ wb) := by rw [hTadd]; ring

set_option maxHeartbeats 600000 in
-- as `fiori_zeta_interpolation_tight`, the `r = 4` bookkeeping is long.  Again `whnf`/`isDefEq`
-- on the statement and the `rpow` calc chain, not tactic search.  Measured: fails at 300000.
/-- **Tight (`O(1/t²)`) version of `fiori_zeta_interpolation_1c`.** As
`fiori_zeta_interpolation_tight`, but for the `r = 4` family: the window threshold is `T1 < |t|`
(not `(Q+2)²+110 ≤ |t|`), and the error carries *two* explicit `O(1/t²)` corrections — one for
`GPL`'s window (`GPL_le_log_tight`), one for `G1shift`'s (`G1shift_le_tight`) — stated additively,
instead of the coarse multiplicative `1+2/|t|`.

### Summary of Proof
**Place among the four variants** (see `fiori_zeta_interpolation`'s docstring for the full table):
this is the `r = 4` family (as `_1c`) combined with the tight `O(1/t²)` boundary estimates (as
`_tight`) — i.e. both axes at once, which is why it needs *two* `O(1/t²)` corrections and the extra
height parameter `T1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`),
`exists_shared_envelope_1c`, `interpG1c`, `interpα1c`, `interpβ1c`, `interpG1c_prod_α`,
`interpG1c_prod_β`, `G1shift`, `G1shift_le_tight`, `GPL_le_log_tight`, `linG`, `linGRefl`, `GPL`.
**Used by:** `BackgroundZetaBounds.interpolated_bound_1c_tight`. -/
theorem fiori_zeta_interpolation_1c_tight {a b B c d p q Q T0 T1 : ℝ}
    (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1)
    (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hc : 0 < c) (hd : 0 ≤ d)
    (hT0 : 3 ≤ T0) (hT01 : T0 ≤ T1) (hp1 : p ≤ 1) (hq1 : q ≤ 1)
    (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) (hQa1 : 1 < Q + a + 1) (hQb1 : 1 < Q + 1 - b)
    (hG1mono : ∀ t : ℝ, T0 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖G1shift Q c d (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGmono : ∀ t : ℝ, T0 < |t| →
      StrictAntiOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b))
    (hGlog : ∀ t : ℝ, 3 ≤ |t| → ∀ σ ∈ Set.Icc a b,
      Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖)
    (hbound_a : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (a + t * Complex.I)‖ ≤ (c * Real.log |t| + d) * |t| ^ p)
    (hbound_b : ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (b + t * Complex.I)‖ ≤ B * |t| ^ q * Real.log |t|)
    (hcompact : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖interpG1c B c d q Q i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα1c p i * (b - σ) / (b - a) + interpβ1c q i * (σ - a) / (b - a)))
    (hnn : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, T1 < |t| →
      0 ≤ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a))) * Real.log |t|
          + ((σ - a) / (b - a)) * Real.log (Real.log |t|)
          + ((b - σ) / (b - a)) * Real.log (c * Real.log |t| + d)
          + ((σ - a) / (b - a)) * Real.log B) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, T1 < |t| →
      Real.log ‖riemannZeta (σ + t * Complex.I)‖
        ≤ (p * ((b - σ) / (b - a)) + q * ((σ - a) / (b - a))) * Real.log |t|
            + ((σ - a) / (b - a)) * Real.log (Real.log |t|)
            + ((b - σ) / (b - a)) * Real.log (c * Real.log |t| + d)
            + ((σ - a) / (b - a)) * Real.log B
            + 3 / (2 * |t| ^ 2)
            + (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * |t| ^ 2 * Real.log |t|)
            + c * (2 * ((Q + σ + 1) ^ 2 + (Q + 1 - σ) ^ 2) + |2 * σ| ^ 2)
                / (8 * |t| ^ 2 * (c * Real.log |t| + d)) := by
  set G : Fin 4 → ℂ → ℂ := interpG1c B c d q Q with hG_def
  set α : Fin 4 → ℝ := interpα1c p with hα_def
  set β : Fin 4 → ℝ := interpβ1c q with hβ_def
  have hbpos : (0:ℝ) < b - a := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  have hG_holo : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | s.re ∈ Set.Icc a b} := by
    intro i
    fin_cases i
    · exact linG_holomorphicOn _ _ _ _
    · exact G1shift_holomorphicOn _ _ _ _ _ (by linarith) (by linarith)
    · exact linGRefl_holomorphicOn _ _ _ _
    · exact GPL_holomorphicOn _ _ _ (by linarith) (by linarith)
  have hG_conj : ∀ i, ∀ s : ℂ, s.re ∈ Set.Icc a b →
      G i (starRingEnd ℂ s) = starRingEnd ℂ (G i s) := by
    intro i s hs
    simp only [Set.mem_Icc] at hs
    fin_cases i
    · exact linG_conj _ _ _
    · refine G1shift_conj _ _ _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat, Complex.one_re] <;> linarith [hs.1, hs.2]
    · exact linGRefl_conj _ _ _
    · refine GPL_conj _ _ ?_ ?_ <;> simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.re_ofNat] <;> linarith [hs.1, hs.2]
  have hα_nonneg : ∀ i, 0 ≤ α i := by
    intro i; fin_cases i <;> simp [hα_def, interpα1c]; linarith
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; fin_cases i <;> simp [hβ_def, interpβ1c]; linarith
  have henv := exists_shared_envelope_1c (a := a) (b := b) (B := B) (c := c) (d := d) (q := q)
    (Q := Q) hab ha hb hB hq hc hd hQa hQb hQa1 hQb1
  rw [show interpG1c B c d q Q = G from hG_def.symm] at henv
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hC3b, hG_lower, hf_upper⟩ := henv
  have hzeta_holo : DifferentiableOn ℂ riemannZeta {s : ℂ | s.re ∈ Set.Icc a b} := by
    apply differentiableOn_riemannZeta.mono
    rintro s hs rfl
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Complex.one_re] at hs
    linarith [hs.2]
  have hf_holo : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
      {s : ℂ | s.re ∈ Set.Icc a b} := DifferentiableOn.mul (by fun_prop) hzeta_holo
  have hmemA : (a : ℝ) ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hmemB : (b : ℝ) ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hinf_nonneg : ∀ (i : Fin 4) (t : ℝ),
      0 ≤ ⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖ := fun i t =>
    Real.iInf_nonneg fun _ => norm_nonneg _
  have hinf_le : ∀ (i : Fin 4) (t τ : ℝ), τ ∈ Set.Icc a b →
      (⨅ τ' : Set.Icc a b, ‖G i ((τ' : ℝ) + t * Complex.I)‖) ≤ ‖G i (τ + t * Complex.I)‖ := by
    intro i t τ hτ
    have hbdd : BddBelow (Set.range fun τ' : Set.Icc a b => ‖G i ((τ' : ℝ) + t * Complex.I)‖) := by
      refine ⟨0, ?_⟩
      rintro x ⟨τ', rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨τ, hτ⟩
  have habs_le : ∀ (σ t : ℝ), |t| ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ t
    rw [Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])
  have hbane : b - a ≠ 0 := by linarith
  have hcollapseA : ∀ i : Fin 4,
      α i * (b - a) / (b - a) + β i * (a - a) / (b - a) = α i := by
    intro i; field_simp; ring
  have hcollapseB : ∀ i : Fin 4,
      α i * (b - b) / (b - a) + β i * (b - a) / (b - a) = β i := by
    intro i; field_simp; ring
  have hsub_le : ∀ (σ : ℝ), 1/2 ≤ σ → ∀ t : ℝ,
      ‖(σ : ℂ) + t * Complex.I - 1‖ ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    have he : ((σ : ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
      push_cast; ring
    rw [he, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnormpos : ∀ (σ : ℝ), 0 < σ → ∀ t : ℝ, 0 < ‖(σ : ℂ) + t * Complex.I‖ := by
    intro σ hσ t
    rw [Complex.norm_add_mul_I]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hf_a : ∀ t : ℝ,
      ‖((a : ℂ) + t * Complex.I - 1) * riemannZeta (a + t * Complex.I)‖
        ≤ ∏ i, ‖G i (a + t * Complex.I)‖ ^ α i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hα_def, interpG1c_prod_α]
      have hNpos : 0 < ‖(a : ℂ) + t * Complex.I‖ := hnormpos a (by linarith) t
      rw [norm_mul]
      have hstep : ‖(a : ℂ) + t * Complex.I - 1‖ * ‖riemannZeta (a + t * Complex.I)‖
          ≤ ‖(a : ℂ) + t * Complex.I‖ * ((c * Real.log |t| + d) * |t| ^ p) :=
        mul_le_mul (hsub_le a (by linarith) t) (hbound_a t ht) (norm_nonneg _) (norm_nonneg _)
      refine hstep.trans ?_
      have hpow : ‖(a : ℂ) + t * Complex.I‖ ^ (p + 1)
          = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖ := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
      rw [hpow]
      have h1 : |t| ^ p ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p :=
        Real.rpow_le_rpow (abs_nonneg t) (habs_le a t) hp.le
      have h2 : c * Real.log |t| + d ≤ ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ :=
        G1shift_ge Q c d a t hc.le hd (by linarith)
      have hcd0 : (0:ℝ) ≤ c * Real.log |t| + d :=
        add_nonneg (mul_nonneg hc.le (Real.log_nonneg (by linarith))) hd
      have hpp : (0:ℝ) ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p := Real.rpow_nonneg hNpos.le _
      have hmul : |t| ^ p * (c * Real.log |t| + d)
          ≤ ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ :=
        mul_le_mul h1 h2 hcd0 hpp
      calc ‖(a : ℂ) + t * Complex.I‖ * ((c * Real.log |t| + d) * |t| ^ p)
          = ‖(a : ℂ) + t * Complex.I‖ * (|t| ^ p * (c * Real.log |t| + d)) := by ring
        _ ≤ ‖(a : ℂ) + t * Complex.I‖
              * (‖(a : ℂ) + t * Complex.I‖ ^ p * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖) :=
            mul_le_mul_of_nonneg_left hmul hNpos.le
        _ = ‖(a : ℂ) + t * Complex.I‖ ^ p * ‖(a : ℂ) + t * Complex.I‖
              * ‖G1shift Q c d ((a:ℂ) + t * Complex.I)‖ := by ring
    · refine le_trans (hcompact t (by linarith) a hmemA).le ?_
      simp only [hcollapseA]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t a hmemA) (hα_nonneg i))
  have hf_b : ∀ t : ℝ,
      ‖((b : ℂ) + t * Complex.I - 1) * riemannZeta (b + t * Complex.I)‖
        ≤ ∏ i, ‖G i (b + t * Complex.I)‖ ^ β i := by
    intro t
    rcases le_or_gt 3 |t| with ht | ht
    · rw [hG_def, hβ_def, interpG1c_prod_β hB hq]
      have hlogpos : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hNpos : 0 < ‖(b : ℂ) + t * Complex.I‖ := hnormpos b (by linarith) t
      have hMeq : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ = ‖(b : ℂ) + t * Complex.I - 1‖ := by
        rw [← norm_neg]; congr 1; ring
      have hMpos : 0 < ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I]
        exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
      have hMle : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        rw [hMeq]; exact hsub_le b (by linarith) t
      have hTle : |t| ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ := by
        have he : (1 : ℂ) - ((b : ℂ) + t * Complex.I)
            = ((1 - b : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - b)])
      rw [norm_mul, ← hMeq]
      have hsplit : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
          = ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q := by
        rw [← Real.rpow_add hMpos]; norm_num
      have hkey : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
          ≤ ‖(b : ℂ) + t * Complex.I‖ := by
        have e1 : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q)
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) :=
          Real.rpow_le_rpow (norm_nonneg _) hMle (by linarith)
        have e2 : |t| ^ q ≤ ‖(b : ℂ) + t * Complex.I‖ ^ q :=
          Real.rpow_le_rpow (abs_nonneg t) (le_trans hTle hMle) hq.le
        have e3 : ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q
            = ‖(b : ℂ) + t * Complex.I‖ := by
          rw [← Real.rpow_add hNpos]; norm_num
        calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q
            ≤ ‖(b : ℂ) + t * Complex.I‖ ^ (1 - q) * ‖(b : ℂ) + t * Complex.I‖ ^ q :=
              mul_le_mul e1 e2 (Real.rpow_nonneg (abs_nonneg t) _)
                (Real.rpow_nonneg (norm_nonneg _) _)
          _ = ‖(b : ℂ) + t * Complex.I‖ := e3
      have hgl : Real.log |t| ≤ ‖GPL Q ((b : ℂ) + t * Complex.I)‖ := hGlog t ht b hmemB
      have hzb := hbound_b t ht
      have hMq : (0:ℝ) ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hstep : ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖
            * ‖riemannZeta ((b : ℂ) + t * Complex.I)‖
          ≤ ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hzb (norm_nonneg _)
      refine hstep.trans ?_
      calc ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ * (B * |t| ^ q * Real.log |t|)
          = (‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ (1 - q) * |t| ^ q)
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q * Real.log |t|) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ ‖(b : ℂ) + t * Complex.I‖
              * (B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
                  * ‖GPL Q ((b : ℂ) + t * Complex.I)‖) := by
            refine mul_le_mul hkey ?_
              (mul_nonneg (mul_nonneg hB.le hMq) hlogpos) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hgl (mul_nonneg hB.le hMq)
        _ = ‖(b : ℂ) + t * Complex.I‖ * B * ‖(1 : ℂ) - ((b : ℂ) + t * Complex.I)‖ ^ q
              * ‖GPL Q ((b : ℂ) + t * Complex.I)‖ := by ring
    · refine le_trans (hcompact t (by linarith) b hmemB).le ?_
      simp only [hcollapseB]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hinf_nonneg i t) _)
        (fun i _ => Real.rpow_le_rpow (hinf_nonneg i t) (hinf_le i t b hmemB) (hβ_nonneg i))
  have hG_mono : ∀ i, ∀ t : ℝ, T0 < |t| →
      (β i < α i → StrictMonoOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) ∧
      (α i < β i → StrictAntiOn (fun σ : ℝ => ‖G i (σ + t * Complex.I)‖) (Set.Icc a b)) := by
    intro i t ht
    fin_cases i <;> simp only [hα_def, hβ_def, interpα1c, interpβ1c, Fin.isValue, Fin.zero_eta,
      Matrix.cons_val_zero, lt_add_iff_pos_left, add_lt_iff_neg_right, Fin.mk_one,
      Matrix.cons_val_one, zero_lt_one, forall_const, isEmpty_Prop, not_lt, zero_le_one,
      IsEmpty.forall_iff, and_true, Fin.reduceFinMk, Matrix.cons_val, true_and]
    · exact ⟨fun _ => linG_mono_of_pos _ _ _ _ one_pos (by linarith) t,
        fun h => absurd h (by linarith)⟩
    · exact hG1mono t ht
    · exact ⟨fun h => absurd h (by linarith), fun _ =>
        linGRefl_anti_of_pos (B ^ (1/q)) 1 a b (Real.rpow_pos_of_pos hB _) hb t⟩
    · exact hGmono t ht
  have hf_small_t : ∀ t : ℝ, |t| ≤ T0 → ∀ σ ∈ Set.Icc a b,
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc a b, ‖G i ((τ : ℝ) + t * Complex.I)‖)
            ^ (α i * (b - σ) / (b - a) + β i * (σ - a) / (b - a)) := hcompact
  have hpl := fiori_phragmenLindelof (f := fun s : ℂ => (s - 1) * riemannZeta s)
    hab G hG_holo hG_conj hC1 hC2 hC3 hC3b
    hG_lower hf_holo hf_upper hα_nonneg hβ_nonneg hf_a hf_b hG_mono hf_small_t
  -- **The tight window bookkeeping**: no `gpl_err_bound`/`hL4`/`(Q+2)²≤T` needed anywhere.
  intro σ hσ t hT1lt
  have hnnσt := hnn σ hσ t hT1lt
  have hT : T0 < |t| := by linarith
  obtain ⟨hσa, hσb⟩ := hσ
  have hσ : σ ∈ Set.Icc a b := ⟨hσa, hσb⟩
  have hQ0 : 0 < Q := by linarith
  set T : ℝ := |t| with hT_def
  have hT0' : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT3 : (3:ℝ) ≤ T := by linarith
  set L : ℝ := Real.log T with hL_def
  have hL0 : (0:ℝ) < L := by rw [hL_def]; exact Real.log_pos (by linarith)
  set wa : ℝ := (b - σ) / (b - a) with hwa_def
  set wb : ℝ := (σ - a) / (b - a) with hwb_def
  have hwa0 : 0 ≤ wa := div_nonneg (by linarith) hbpos.le
  have hwb0 : 0 ≤ wb := div_nonneg (by linarith) hbpos.le
  have hwa1 : wa ≤ 1 := by rw [hwa_def, div_le_one hbpos]; linarith
  have hwb1 : wb ≤ 1 := by rw [hwb_def, div_le_one hbpos]; linarith
  have hwsum : wa + wb = 1 := by rw [hwa_def, hwb_def]; field_simp; ring
  set N1 : ℝ := ‖(σ:ℂ) + (t:ℂ) * Complex.I‖ with hN1_def
  set N2 : ℝ := ‖1 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hN2_def
  set NG : ℝ := ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNG_def
  set NS : ℝ := ‖G1shift Q c d ((σ:ℂ) + (t:ℂ) * Complex.I)‖ with hNS_def
  have hN1nn : 0 ≤ N1 := norm_nonneg _
  have hN2nn : 0 ≤ N2 := norm_nonneg _
  have hNGpos : 0 < NG := lt_of_lt_of_le hL0 (hGlog t (by linarith) σ hσ)
  have hcdpos : (0:ℝ) < c * L + d := by
    have : (0:ℝ) < c * L := mul_pos hc hL0
    linarith
  have hNSpos : 0 < NS := by
    rw [hNS_def]
    calc (0:ℝ) < c * Real.log |t| + d := by
          have : (0:ℝ) ≤ Real.log |t| := Real.log_nonneg (by rw [← hT_def]; linarith)
          nlinarith [mul_nonneg hc.le this]
      _ ≤ _ := G1shift_ge Q c d σ t hc.le hd (by rw [← hT_def]; linarith)
  have hTsq : T ^ 2 = t ^ 2 := sq_abs t
  set dw : ℝ := 1 / (2 * T ^ 2) with hdw_def
  have hdw0 : 0 ≤ dw := by positivity
  have hdwub : dw ≤ 1 := by
    rw [hdw_def, div_le_one (by positivity)]
    nlinarith [hT1]
  have hsq1 : σ ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hsq2 : (1 - σ) ^ 2 ≤ 1 := sq_le_one_of_unit (by linarith) (by linarith)
  have hN1le : N1 ≤ T * (1 + dw) := by
    rw [hN1_def, Complex.norm_add_mul_I, hdw_def, hT_def]
    exact sqrt_le_window hT1 hsq1
  have hN2le : N2 ≤ T * (1 + dw) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN2_def, he, Complex.norm_add_mul_I, hdw_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact sqrt_le_window hT1 hsq2
  set e : ℝ := (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * T ^ 2 * L)
    with he_def
  have hLne : L ≠ 0 := hL0.ne'
  have hTne : T ≠ 0 := hT0'.ne'
  have he0 : 0 ≤ e := by rw [he_def]; apply div_nonneg (by positivity); positivity
  have hNGle : NG ≤ L * (1 + e) := by
    have hg := GPL_le_log_tight Q σ t (by linarith) (by linarith) hT3
    rw [← hNG_def, ← hT_def] at hg
    have ht2T2 : t ^ 2 = T ^ 2 := by rw [hT_def]; exact (sq_abs t).symm
    rw [ht2T2, ← hL_def] at hg
    have heq : L * (1 + e) = L + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * T^2) := by
      rw [he_def]; field_simp
    rw [heq]; exact hg
  set e1 : ℝ := c * (2 * ((Q + σ + 1) ^ 2 + (Q + 1 - σ) ^ 2) + |2 * σ| ^ 2)
    / (8 * T ^ 2 * (c * L + d)) with he1_def
  have hcdne : c * L + d ≠ 0 := hcdpos.ne'
  have he10 : 0 ≤ e1 := by
    rw [he1_def]; apply div_nonneg (by positivity); positivity
  have hNSle : NS ≤ (c * L + d) * (1 + e1) := by
    have hg1 := G1shift_le_tight Q c d σ t hc.le hd (by linarith) (by linarith) hT3
    rw [← hNS_def] at hg1
    have ht2T2 : t ^ 2 = T ^ 2 := by rw [hT_def]; exact (sq_abs t).symm
    rw [← hT_def, ht2T2, ← hL_def] at hg1
    have heq : (c * L + d) * (1 + e1)
        = c * (L + (2 * ((Q+σ+1)^2 + (Q+1-σ)^2) + |2*σ|^2) / (8 * T^2)) + d := by
      rw [he1_def]; field_simp; ring
    rw [heq]; exact hg1
  have hE1 : (0:ℝ) ≤ p * wa := mul_nonneg hp.le hwa0
  have hE1' : p * wa ≤ 1 := mul_le_one₀ hp1 hwa0 hwa1
  have hE2 : (0:ℝ) ≤ q * wb := mul_nonneg hq.le hwb0
  have hE2' : q * wb ≤ 1 := mul_le_one₀ hq1 hwb0 hwb1
  have h := hpl σ hσ t
  rw [hG_def, hα_def, hβ_def, interpG1c_prod_α, interpG1c_prod_β hB hq,
    ← hN1_def, ← hN2_def, ← hNG_def, ← hNS_def] at h
  have hnormeq : ‖((σ:ℂ) + (t:ℂ) * Complex.I - 1) * riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      = N2 * ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [norm_mul, hN2_def]
    have hn : ‖(σ:ℂ) + (t:ℂ) * Complex.I - 1‖ = ‖(1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hn]
  have htpos : (0:ℝ) < t ^ 2 := hTsq ▸ pow_pos hT0' 2
  have hN2pos : (0:ℝ) < N2 := by
    rw [hN2_def]
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    linarith [sq_nonneg (1 - σ)]
  have hN1pos : (0:ℝ) < N1 := by
    rw [hN1_def, Complex.norm_add_mul_I]
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg σ]
  have hN1N2 : N1 ≤ N2 * (1 + dw) := by
    have he : (1:ℂ) - ((σ:ℂ) + (t:ℂ) * Complex.I)
        = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hN1_def, hN2_def, he, Complex.norm_add_mul_I, Complex.norm_add_mul_I, hdw_def, hT_def]
    have hneg : (-t) ^ 2 = t ^ 2 := by ring
    rw [hneg]
    exact norm_ratio_window hT1 (by linarith) (by linarith)
  have hexp : (N1 ^ (p + 1) * NS) ^ wa * (N1 * B * N2 ^ q * NG) ^ wb
      = B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb) :=
    rpow_prod_expand_1c hB hN1pos hN2nn hNGpos hNSpos hwsum
  rw [hnormeq, hexp] at h
  have hw1 := rpow_window hN1nn hT0'.le hdw0 hN1le hE1 hE1'
  have hw2 := rpow_window hN2nn hT0'.le hdw0 hN2le hE2 hE2'
  have hw3 := rpow_window hNGpos.le hL0.le he0 hNGle hwb0 hwb1
  have hw4 : NS ^ wa ≤ (c * L + d) ^ wa * (1 + e1) :=
    rpow_window hNSpos.le (by positivity) he10 hNSle hwa0 hwa1
  have hBnn : (0:ℝ) ≤ B ^ wb := Real.rpow_nonneg hB.le _
  have hT1nn : (0:ℝ) ≤ T ^ (p * wa) := Real.rpow_nonneg hT0'.le _
  have hT2nn : (0:ℝ) ≤ T ^ (q * wb) := Real.rpow_nonneg hT0'.le _
  have hLnn : (0:ℝ) ≤ L ^ wb := Real.rpow_nonneg hL0.le _
  have hcdnn : (0:ℝ) ≤ (c * L + d) ^ wa := Real.rpow_nonneg hcdpos.le _
  have hdw1 : (0:ℝ) ≤ 1 + dw := by linarith
  have he1' : (0:ℝ) ≤ 1 + e := by linarith
  have hee1' : (0:ℝ) ≤ 1 + e1 := by linarith
  have hR1 : (0:ℝ)
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw))) :=
    mul_nonneg (mul_nonneg hBnn hcdnn)
      (mul_nonneg (mul_nonneg hT1nn hdw1) (mul_nonneg hN2pos.le hdw1))
  have hR2 : (0:ℝ)
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw)))
          * (T ^ (q * wb) * (1 + dw)) :=
    mul_nonneg hR1 (mul_nonneg hT2nn hdw1)
  -- **the tight step**: `log((1+dw)³(1+e)(1+e1)) = 3log(1+dw)+log(1+e)+log(1+e1) ≤ 3dw+e+e1`,
  -- directly, with *no* cross term at all — strictly tighter than `five_factor_bound_tight`'s
  -- polynomial `1+7dw+8e+8e1+8(e·e1)`.
  have hmul : ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb
          * ((1 + dw) * (1 + dw) * (1 + dw) * (1 + e) * (1 + e1)) := by
    refine le_of_mul_le_mul_left (le_trans h ?_) hN2pos
    calc B ^ wb * NS ^ wa * NG ^ wb * (N1 ^ (p * wa) * N1) * N2 ^ (q * wb)
        ≤ B ^ wb * ((c * L + d) ^ wa * (1 + e1)) * (L ^ wb * (1 + e))
            * (T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw))) * (T ^ (q * wb) * (1 + dw)) := by
          have h1 : N1 ^ (p * wa) * N1 ≤ T ^ (p * wa) * (1 + dw) * (N2 * (1 + dw)) :=
            mul_le_mul hw1 hN1N2 hN1nn (mul_nonneg hT1nn hdw1)
          have h2 : NS ^ wa ≤ (c * L + d) ^ wa * (1 + e1) := hw4
          have h3 : NG ^ wb ≤ L ^ wb * (1 + e) := hw3
          have h4 : N2 ^ (q * wb) ≤ T ^ (q * wb) * (1 + dw) := hw2
          have hB' : (0:ℝ) ≤ B ^ wb := hBnn
          gcongr
      _ = N2 * ((B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb)
            * ((1 + dw) * (1 + dw) * (1 + dw) * (1 + e) * (1 + e1))) := by ring
  have hBIGpos : (0:ℝ)
      < B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb :=
    mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hcdpos _))
      (mul_pos (Real.rpow_pos_of_pos hT0' _) (Real.rpow_pos_of_pos hT0' _)))
      (Real.rpow_pos_of_pos hL0 _)
  have hprodpos : (0:ℝ) < (1 + dw) * (1 + dw) * (1 + dw) * (1 + e) * (1 + e1) := by positivity
  rcases eq_or_lt_of_le (norm_nonneg (riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I))) with hz | hz
  · rw [← hz, Real.log_zero]
    have h3d0 : (0:ℝ) ≤ 3 / (2 * T ^ 2) := by positivity
    linarith [hnnσt, he0, he10, h3d0]
  · have hlog := Real.log_le_log hz hmul
    have hlogBIG : Real.log (B ^ wb * (c * L + d) ^ wa * (T ^ (p * wa) * T ^ (q * wb)) * L ^ wb)
        = wb * Real.log B + wa * Real.log (c * L + d) + (p * wa + q * wb) * Real.log T
            + wb * Real.log L := by
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hL0 _).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hcdpos _).ne',
        Real.log_mul (Real.rpow_pos_of_pos hT0' _).ne' (Real.rpow_pos_of_pos hT0' _).ne',
        Real.log_rpow hB, Real.log_rpow hcdpos, Real.log_rpow hT0', Real.log_rpow hT0',
        Real.log_rpow hL0]
      ring
    rw [Real.log_mul (ne_of_gt hBIGpos) (ne_of_gt hprodpos), hlogBIG] at hlog
    have h3d : Real.log ((1 + dw) * (1 + dw) * (1 + dw) * (1 + e) * (1 + e1))
        ≤ 3 * dw + e + e1 := by
      have hdw1' : (0:ℝ) < 1 + dw := by linarith
      have he1'' : (0:ℝ) < 1 + e := by linarith
      have he11'' : (0:ℝ) < 1 + e1 := by linarith
      rw [Real.log_mul (by positivity) he11''.ne', Real.log_mul (by positivity) he1''.ne',
        Real.log_mul (by positivity) hdw1'.ne', Real.log_mul hdw1'.ne' hdw1'.ne']
      have hld : Real.log (1 + dw) ≤ dw := by
        calc Real.log (1 + dw) ≤ (1 + dw) - 1 := Real.log_le_sub_one_of_pos hdw1'
          _ = dw := by ring
      have hle : Real.log (1 + e) ≤ e := by
        calc Real.log (1 + e) ≤ (1 + e) - 1 := Real.log_le_sub_one_of_pos he1''
          _ = e := by ring
      have hle1 : Real.log (1 + e1) ≤ e1 := by
        calc Real.log (1 + e1) ≤ (1 + e1) - 1 := Real.log_le_sub_one_of_pos he11''
          _ = e1 := by ring
      linarith [hld, hle, hle1]
    have hclosed_eq : 3 * dw + e + e1 = 3 / (2 * T ^ 2)
        + (2 * ((Q + σ) ^ 2 + (Q + 2 - σ) ^ 2) + |2 - 2 * σ| ^ 2) / (8 * T ^ 2 * L)
        + c * (2 * ((Q + σ + 1) ^ 2 + (Q + 1 - σ) ^ 2) + |2 * σ| ^ 2)
            / (8 * T ^ 2 * (c * L + d)) := by
      rw [hdw_def, he_def, he1_def]
      have h8L : (8:ℝ) * T ^ 2 * L ≠ 0 := by positivity
      have h8cd : (8:ℝ) * T ^ 2 * (c * L + d) ≠ 0 := by positivity
      field_simp
    linarith [hlog, h3d, hclosed_eq]

/-! ### From the interpolated bound to the `log`-form stated in `BackgroundZetaBounds`

`interpolated_bound_1a`, `_1b` and `_1c` are stated logarithmically and in terms of `T` rather
than the actual ordinate `t ∈ [T-1, T+1]`. `log_bound_of_interp` performs that conversion once:
take `Real.log` of `fiori_zeta_interpolation`'s conclusion and re-express `log|t|`, `loglog|t|` in
terms of `T`, with every correction absorbed into the `3/T` slack (the source carries `2/T`, which
is just too small — see `log_bound_of_interp`). `interpolated_bound_2` is already stated at the
ordinate itself, so only the slack has to be absorbed (`log_bound_of_interp_self`); the `_tight`
variants come out of `fiori_zeta_interpolation_tight`/`_1c_tight` in log form already and need no
bridge (`log_bound_pointwise_tight` is the generic version of that step, kept but unused). -/

/-- `‖ζ(σ+it)‖` depends on `t` only through `|t|`, by `riemannZeta_conj`.

### Summary of Proof
Case split on the sign of `t`: for `t ≥ 0` there is nothing to do, and for `t ≤ 0` the point
`σ + |t|i` is the conjugate of `σ + ti`, so `riemannZeta_conj` and `RCLike.norm_conj` finish. This
lets the boundary bounds of `ExternalFacts`, all stated for `|t|`, be fed to
`fiori_zeta_interpolation`'s `hbound_a`/`_b`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`, `interpolated_bound_1c`, `interpolated_bound_1c_tight`,
`interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem zeta_norm_abs_im (σ t : ℝ) :
    ‖riemannZeta (σ + t * Complex.I)‖ = ‖riemannZeta (σ + |t| * Complex.I)‖ := by
  rcases le_total (0:ℝ) t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    have hconj : (σ:ℂ) + ((-t:ℝ):ℂ) * Complex.I
        = (starRingEnd ℂ) ((σ:ℂ) + (t:ℂ) * Complex.I) := by
      simp
    rw [hconj, riemannZeta_conj, RCLike.norm_conj]

/-- `log x > 20` for `x > 10¹² - 1` — used to make the `loglog` window correction negligible.

### Summary of Proof
For `x > 10¹² - 1`, `log x > 20`. Since `exp 20 < 10¹² - 1` — checked by bounding `exp 20 = (exp
1)^20` above using `Real.exp_one_lt_d9` — monotonicity of `log` gives the claim. The `20` is what
makes the `log log` window conversion lose only a negligible amount.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_2`, `log_bound_of_interp_1c`, `twenty_lt_log`. -/
theorem twenty_lt_log' {x : ℝ} (hx : (10 : ℝ) ^ (12 : ℕ) - 1 < x) : 20 < Real.log x := by
  have hexp : Real.exp 20 = Real.exp 1 ^ (20 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 ^ (20 : ℕ) < 3 ^ (20 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
  have hlt : Real.exp 20 < x := by
    rw [hexp]
    calc Real.exp 1 ^ (20 : ℕ) < 3 ^ (20 : ℕ) := h3
      _ < (10 : ℝ) ^ (12 : ℕ) - 1 := by norm_num
      _ < x := hx
  calc (20:ℝ) = Real.log (Real.exp 20) := (Real.log_exp 20).symm
    _ < Real.log x := Real.log_lt_log (Real.exp_pos 20) hlt

/-- `log T > 20` for `T > 10¹²` — the form of `twenty_lt_log'` used at the project's standard
threshold, obtained by weakening `T > 10¹²` to `T > 10¹² - 1` with `linarith`.

### Summary of Proof
Both spellings are kept because the interpolation lemmas meet the hypothesis in both shapes: the
window arguments produce `10¹² - 1 < x` after shrinking by the half-width, while the top-level
statements carry the clean `10¹² < T`. No tex counterpart — the source treats `log T > 20` as
obvious at this threshold.

### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log'`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1b`, `interpolated_bound_1c`,
`log_bound_of_interp`, `log_bound_of_interp_1c`. -/
theorem twenty_lt_log {T : ℝ} (hT : (10 : ℝ) ^ (12 : ℕ) < T) : 20 < Real.log T :=
  twenty_lt_log' (by linarith)

/-- **Log-form bridge.** Converts `fiori_zeta_interpolation`'s multiplicative conclusion at the
ordinate `t ∈ [T-1,T+1]` into the additive, `T`-indexed form of `interpolated_bound_*`.

### Summary of Proof
`hc` bounds the `log|t|` coefficient, `hw` the `loglog` weight, and `hnn` says the `T`-side of the
target is nonnegative — which is what lets the degenerate case `L = 0` (a real possibility for `L =
‖ζ(1/2+it)‖`, where `Real.log 0 = 0`) go through against the strictly positive `3/T` slack. **The
slack is `3/T`, not `2/T`.** For `t = T+1` the three corrections are `log(1+1/t) ≈ 1/T`,
`c·log(t/T) ≈ c/T` and `w·log(log t/log T) ≈ w/(T log T)`, totalling `(1 + c + w/log T)/T`. Under
the natural hypotheses `c ≤ 1`, `w ≤ 1` that is up to `2.05/T`, so `2/T` — the slack the source
carries — is *just* too small; `3/T` absorbs it with room. (Weakening `hc` to `c ≤ 1/2` would also
work, since every application has `c ≤ 1/6`, but enlarging the slack is the better trade: it costs
nothing downstream, where `JensenScaleConstants.zeta_piecewise_bound` already budgets `4/|t|` and
`3/t + 1/(2t²) ≤ 4/t` still holds.)

### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1b`. -/
theorem log_bound_of_interp {A B c w T t L : ℝ} (hL : 0 ≤ L)
    (hA : 0 < A) (hB : 0 < B) (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1))
    (hc0 : 0 ≤ c) (hc : c ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1)
    (hnn : 0 ≤ c * Real.log |T| + w * Real.log (Real.log |T|) + Real.log A + Real.log B)
    (hbd : L ≤ (1 + 1 / |t|) * A * B * |t| ^ c * Real.log |t| ^ w) :
    Real.log L
      < c * Real.log |T| + w * Real.log (Real.log |T|) + Real.log A + Real.log B + 3 / T := by
  have hTbig : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) < T := by linarith
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  have ht1 : (1:ℝ) < t := by linarith [ht.1]
  have hatT : |T| = T := abs_of_pos hT0
  have hatt : |t| = t := abs_of_pos ht0
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hlogT20 : 20 < Real.log T := twenty_lt_log hT
  have hslack : (0:ℝ) < 1 + 1 / |t| := by rw [hatt]; positivity
  -- the three corrections
  have hE1 : Real.log (1 + 1 / t) ≤ 1 / t := by
    calc Real.log (1 + 1 / t) ≤ (1 + 1 / t) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / t := by ring
  have herr : Real.log (1 + 1 / t) + c * (Real.log t - Real.log T)
      + w * (Real.log (Real.log t) - Real.log (Real.log T)) < 3 / T := by
    rcases le_or_gt t T with hcase | hcase
    · -- `t ≤ T`: both `log`-corrections are non-positive, and `1/t ≤ 1/(T-1) < 2/T`
      have hlt : Real.log t ≤ Real.log T := Real.log_le_log ht0 hcase
      have hll : Real.log (Real.log t) ≤ Real.log (Real.log T) := Real.log_le_log hlogt hlt
      have h2 : c * (Real.log t - Real.log T) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
      have h3 : w * (Real.log (Real.log t) - Real.log (Real.log T)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hw0 (by linarith)
      have h1 : (1:ℝ) / t ≤ 1 / (T - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith [ht.1])
      have h4 : (1:ℝ) / (T - 1) < 3 / T := by
        rw [div_lt_div_iff₀ (by linarith) hT0]; linarith
      linarith
    · -- `T < t ≤ T+1`: each correction is at most `1/T`, `c/T`, `w/(T·log T)` respectively
      have hdiff : Real.log t - Real.log T ≤ 1 / T := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < t / T by positivity)
        rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hT0)] at h
        have : t / T - 1 ≤ 1 / T := by
          rw [div_sub_one (ne_of_gt hT0), div_le_div_iff₀ hT0 hT0]; nlinarith [ht.2]
        linarith
      have hdiff0 : 0 ≤ Real.log t - Real.log T := by
        have := Real.log_le_log hT0 hcase.le
        linarith
      have hdiff2 : Real.log (Real.log t) - Real.log (Real.log T)
          ≤ (Real.log t - Real.log T) / Real.log T := by
        have h := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < Real.log t / Real.log T by positivity)
        rw [Real.log_div (ne_of_gt hlogt) (ne_of_gt hlogT)] at h
        have he : Real.log t / Real.log T - 1
            = (Real.log t - Real.log T) / Real.log T := by
          field_simp
        linarith [he ▸ h]
      have h1 : Real.log (1 + 1 / t) ≤ 1 / T := by
        refine hE1.trans ?_
        exact one_div_le_one_div_of_le hT0 hcase.le
      have h2 : c * (Real.log t - Real.log T) ≤ 1 * (1 / T) :=
        mul_le_mul hc hdiff hdiff0 (by norm_num)
      have hx : (0:ℝ) < 1 / T := by positivity
      have h3a : (Real.log t - Real.log T) / Real.log T ≤ (1 / T) / 20 := by
        rw [div_le_div_iff₀ hlogT (by norm_num : (0:ℝ) < 20)]
        nlinarith [hdiff, hx, mul_nonneg hx.le (by linarith : (0:ℝ) ≤ Real.log T - 20)]
      have hll0 : 0 ≤ Real.log (Real.log t) - Real.log (Real.log T) := by
        have := Real.log_le_log hlogT (by linarith : Real.log T ≤ Real.log t)
        linarith
      have h3 : w * (Real.log (Real.log t) - Real.log (Real.log T)) ≤ 1 * ((1 / T) / 20) :=
        mul_le_mul hw (hdiff2.trans h3a) hll0 (by norm_num)
      have he : (3:ℝ) / T = 3 * (1 / T) := by ring
      rw [he]
      linarith
  -- transport through `Real.log`
  rcases eq_or_lt_of_le hL with hz | hz
  · rw [← hz, Real.log_zero]
    have : (0:ℝ) < 3 / T := by positivity
    linarith
  · have hlog := Real.log_le_log hz hbd
    have hp1 : (0:ℝ) < |t| ^ c := by rw [hatt]; exact Real.rpow_pos_of_pos ht0 c
    have hp2 : (0:ℝ) < Real.log |t| ^ w := by rw [hatt]; exact Real.rpow_pos_of_pos hlogt w
    rw [Real.log_mul (by positivity) (ne_of_gt hp2),
      Real.log_mul (by positivity) (ne_of_gt hp1),
      Real.log_mul (by positivity) (ne_of_gt hB),
      Real.log_mul (ne_of_gt hslack) (ne_of_gt hA)] at hlog
    rw [hatt] at hlog
    rw [Real.log_rpow ht0, Real.log_rpow hlogt] at hlog
    rw [hatT]
    linarith [hlog, herr]

set_option maxHeartbeats 600000 in
-- four case-split correction terms (slack, power, loglog, and the `A(t)` vs `A(T)` bound)
-- push this past the default budget.  `whnf`/`isDefEq` again, not tactic search.
-- Measured: fails at 300000.
/-- **Log-form bridge, case (1c) variant.** As `log_bound_of_interp`, but the `σ = a` boundary
constant is the affine-in-log `A(x) := c1 + d1/log x` rather than a plain constant, matching
`fiori_zeta_interpolation_1c`'s conclusion.

### Summary of Proof
`wa` is `A`'s own exponent (`(b-σ)/(b-a)`); the `\log\log|T|` coefficient is fixed at `1` (not a
free weight), since `wa + wb = 1` identically in every application. The extra correction this needs
beyond `log_bound_of_interp`'s three (slack, power, `\log\log`) is `wa·(\log A(t) - \log A(T))`,
bounded via `hcd` (`d1 ≤ 20·c1`, satisfied with room by every actual instantiation) using that `A`
is decreasing and `\log(T-1) > 20`.
### References
No tex counterpart.

### Dependencies
**Depends on:** `twenty_lt_log`, `twenty_lt_log'`.
**Used by:** `interpolated_bound_1c`. -/
theorem log_bound_of_interp_1c {c1 d1 Bw cc wa wb T t L : ℝ} (hL : 0 ≤ L)
    (hc1 : 0 < c1) (hd1 : 0 ≤ d1) (hcd : d1 ≤ 20 * c1) (hBw : 0 < Bw)
    (hT : (10 : ℝ) ^ (12 : ℕ) < T) (ht : t ∈ Set.Icc (T - 1) (T + 1))
    (hcc0 : 0 ≤ cc) (hcc : cc ≤ 1 / 6)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (_hwb0 : 0 ≤ wb) (hwsum : wa + wb = 1)
    (hnn : 0 ≤ cc * Real.log |T| + Real.log (Real.log |T|)
             + wa * Real.log (c1 + d1 / Real.log |T|) + Real.log Bw)
    (hbd : L ≤ (1 + 2 / |t|) * (c1 * Real.log |t| + d1) ^ wa * Bw * |t| ^ cc
             * Real.log |t| ^ wb) :
    Real.log L < cc * Real.log |T| + Real.log (Real.log |T|)
        + wa * Real.log (c1 + d1 / Real.log |T|) + Real.log Bw + 3 / T := by
  have hTbig : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) < T := by linarith
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  have ht1 : (1:ℝ) < t := by linarith [ht.1]
  have hatT : |T| = T := abs_of_pos hT0
  have hatt : |t| = t := abs_of_pos ht0
  rw [hatT] at hnn
  have hlogt20 : (20:ℝ) < Real.log t := twenty_lt_log' (by linarith [ht.1])
  have hlogT20 : (20:ℝ) < Real.log T := twenty_lt_log hT
  have hlogt : (0:ℝ) < Real.log t := by linarith
  have hlogT : (0:ℝ) < Real.log T := by linarith
  have hslack : (0:ℝ) < 1 + 2 / |t| := by rw [hatt]; positivity
  have hAt : (0:ℝ) < c1 + d1 / Real.log t := by positivity
  have hAT : (0:ℝ) < c1 + d1 / Real.log T := by positivity
  -- **correction 1**: the `(1+2/t)` slack, `≤ 2/t`
  have hE1 : Real.log (1 + 2 / t) ≤ 2 / t := by
    calc Real.log (1 + 2 / t) ≤ (1 + 2 / t) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 2 / t := by ring
  -- **corrections 2–4**, in one case split on `t ≤ T` vs `t > T`
  have herr : Real.log (1 + 2 / t) + cc * (Real.log t - Real.log T)
      + (Real.log (Real.log t) - Real.log (Real.log T))
      + wa * (Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T)) < 3 / T := by
    rcases le_or_gt t T with hcase | hcase
    · -- `T - 1 ≤ t ≤ T`: corrections 2, 3 are `≤ 0`; correction 4 needs the explicit bound
      have hlt : Real.log t ≤ Real.log T := Real.log_le_log ht0 hcase
      have hll : Real.log (Real.log t) ≤ Real.log (Real.log T) := Real.log_le_log hlogt hlt
      have h2 : cc * (Real.log t - Real.log T) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcc0 (by linarith)
      have htT1 : (T:ℝ) - 1 ≤ t := ht.1
      have hslackT : (2:ℝ) / t ≤ 21 / (10 * T) := by
        rw [div_le_div_iff₀ ht0 (by positivity)]
        nlinarith [htT1, hT0]
      have hdiffTt : Real.log T - Real.log t ≤ 1 / t := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < T / t by positivity)
        rw [Real.log_div (ne_of_gt hT0) (ne_of_gt ht0)] at h
        have hstep : T / t - 1 ≤ 1 / t := by
          rw [div_sub_one (ne_of_gt ht0), div_le_div_iff₀ ht0 ht0]; nlinarith [hcase]
        linarith
      have ht2T : (1:ℝ) / t ≤ 11 / (10 * T) := by
        rw [div_le_div_iff₀ ht0 (by positivity)]
        nlinarith [htT1, hT0]
      have hAdiff : c1 + d1 / Real.log t - (c1 + d1 / Real.log T) ≤ d1 / (100 * T) := by
        have heq2 : c1 + d1 / Real.log t - (c1 + d1 / Real.log T)
            = d1 / Real.log t - d1 / Real.log T := by ring
        have he : d1 / Real.log t - d1 / Real.log T
            = d1 * (Real.log T - Real.log t) / (Real.log t * Real.log T) := by
          field_simp
        have hnum : d1 * (Real.log T - Real.log t) ≤ d1 * (11 / (10 * T)) :=
          mul_le_mul_of_nonneg_left (hdiffTt.trans ht2T) hd1
        have hden : (400:ℝ) ≤ Real.log t * Real.log T := by nlinarith [hlogt20, hlogT20]
        have hpos : (0:ℝ) < Real.log t * Real.log T := by positivity
        rw [heq2, he, div_le_div_iff₀ hpos (by positivity)]
        have hstep : d1 * (Real.log T - Real.log t) * (100 * T)
            ≤ d1 * (11 / (10 * T)) * (100 * T) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
        have heq3 : d1 * (11 / (10 * T)) * (100 * T) = d1 * 110 := by field_simp; ring
        rw [heq3] at hstep
        have hstep2 : d1 * 110 ≤ d1 * (Real.log t * Real.log T) := by nlinarith [hden, hd1]
        linarith [hstep, hstep2]
      have hA4 : Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T)
          ≤ d1 / (100 * T * c1) := by
        have step1 : Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T)
            = Real.log ((c1 + d1 / Real.log t) / (c1 + d1 / Real.log T)) :=
          (Real.log_div (ne_of_gt hAt) (ne_of_gt hAT)).symm
        rw [step1]
        have step2 : Real.log ((c1 + d1 / Real.log t) / (c1 + d1 / Real.log T))
            ≤ (c1 + d1 / Real.log t) / (c1 + d1 / Real.log T) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have step3 : (c1 + d1 / Real.log t) / (c1 + d1 / Real.log T) - 1
            = (c1 + d1 / Real.log t - (c1 + d1 / Real.log T)) / (c1 + d1 / Real.log T) := by
          field_simp
        rw [step3] at step2
        have step4 : (c1 + d1 / Real.log t - (c1 + d1 / Real.log T)) / (c1 + d1 / Real.log T)
            ≤ d1 / (100 * T * c1) := by
          have hmul := mul_le_mul_of_nonneg_right hAdiff
            (show (0:ℝ) ≤ 100 * T * c1 by positivity)
          have heq1 : d1 / (100 * T) * (100 * T * c1) = d1 * c1 := by field_simp
          rw [heq1] at hmul
          have hcTle : c1 ≤ c1 + d1 / Real.log T := by
            have : (0:ℝ) ≤ d1 / Real.log T := by positivity
            linarith
          have hle2 : d1 * c1 ≤ d1 * (c1 + d1 / Real.log T) :=
            mul_le_mul_of_nonneg_left hcTle hd1
          rw [div_le_div_iff₀ hAT (by positivity)]
          linarith [hmul, hle2]
        linarith [step2, step4]
      have h4 : wa * (Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T))
          ≤ d1 / (100 * T * c1) := by
        have hle := mul_le_mul_of_nonneg_left hA4 hwa0
        have heq : wa * (d1 / (100 * T * c1)) ≤ 1 * (d1 / (100 * T * c1)) :=
          mul_le_mul_of_nonneg_right hwa1 (by positivity)
        linarith [hle, heq]
      have hbudget : d1 / (100 * T * c1) ≤ 1 / (5 * T) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hcd, hT0]
      have e1 : Real.log (1 + 2 / t) ≤ 21 / (10 * T) := hE1.trans hslackT
      have e4 : wa * (Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T))
          ≤ 1 / (5 * T) := h4.trans hbudget
      have hXpos : (0:ℝ) < 1 / T := by positivity
      have hfinal : (21:ℝ) / (10 * T) + 1 / (5 * T) < 3 / T := by
        rw [show (21:ℝ) / (10 * T) + 1 / (5 * T) = (23/10) * (1/T) by ring,
          show (3:ℝ) / T = 3 * (1/T) by ring]
        linarith [hXpos]
      linarith [e1, h2, hll, e4, hfinal]
    · -- `T < t ≤ T + 1`: symmetric, and correction 4 is `≤ 0` (since `A` is decreasing)
      have hdiff : Real.log t - Real.log T ≤ 1 / T := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < t / T by positivity)
        rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hT0)] at h
        have hstep : t / T - 1 ≤ 1 / T := by
          rw [div_sub_one (ne_of_gt hT0), div_le_div_iff₀ hT0 hT0]; nlinarith [ht.2]
        linarith
      have hdiff0 : 0 ≤ Real.log t - Real.log T := by
        have := Real.log_le_log hT0 hcase.le; linarith
      have hdiff2 : Real.log (Real.log t) - Real.log (Real.log T)
          ≤ (Real.log t - Real.log T) / Real.log T := by
        have h := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < Real.log t / Real.log T by positivity)
        rw [Real.log_div (ne_of_gt hlogt) (ne_of_gt hlogT)] at h
        have he : Real.log t / Real.log T - 1
            = (Real.log t - Real.log T) / Real.log T := by field_simp
        linarith [he ▸ h]
      have h2 : cc * (Real.log t - Real.log T) ≤ 1 / (6 * T) := by
        have hle := mul_le_mul hcc hdiff hdiff0 (by norm_num : (0:ℝ) ≤ 1/6)
        have heq : (1:ℝ)/6 * (1/T) = 1/(6*T) := by ring
        linarith [hle, heq]
      have h3 : (Real.log t - Real.log T) / Real.log T ≤ (1 / T) / 20 := by
        rw [div_le_div_iff₀ hlogT (by norm_num : (0:ℝ) < 20)]
        nlinarith [hdiff, hlogT20, hT0]
      have hslackT : (2:ℝ) / t ≤ 2 / T := by
        apply div_le_div_of_nonneg_left (by norm_num) hT0 hcase.le
      have hlogtT : Real.log T ≤ Real.log t := by linarith [hdiff0]
      have hAle : c1 + d1 / Real.log t ≤ c1 + d1 / Real.log T := by
        have : d1 / Real.log t ≤ d1 / Real.log T :=
          div_le_div_of_nonneg_left hd1 hlogT hlogtT
        linarith [this]
      have h4 : wa * (Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T)) ≤ 0 := by
        have hle := Real.log_le_log hAt hAle
        have : wa * (Real.log (c1 + d1 / Real.log t) - Real.log (c1 + d1 / Real.log T)) ≤ wa * 0 :=
          mul_le_mul_of_nonneg_left (by linarith [hle]) hwa0
        linarith [this]
      have e1 : Real.log (1 + 2 / t) ≤ 2 / T := hE1.trans hslackT
      have e3 : Real.log (Real.log t) - Real.log (Real.log T) ≤ (1/T)/20 := hdiff2.trans h3
      have hXpos : (0:ℝ) < 1 / T := by positivity
      have hfinal : (2:ℝ) / T + 1 / (6 * T) + (1/T)/20 < 3 / T := by
        rw [show (2:ℝ) / T + 1 / (6 * T) + (1/T)/20 = (133/60) * (1/T) by ring,
          show (3:ℝ) / T = 3 * (1/T) by ring]
        linarith [hXpos]
      linarith [e1, h2, e3, h4, hfinal]
  rcases eq_or_lt_of_le hL with hz | hz
  · rw [← hz, Real.log_zero, hatT]
    have h1 : (0:ℝ) < wa * Real.log (c1 + d1 / Real.log T) + Real.log Bw
        + cc * Real.log T + Real.log (Real.log T) + 3 / T := by
      have h3T : (0:ℝ) < 3 / T := by positivity
      linarith [hnn, h3T]
    linarith [h1]
  · have hlog := Real.log_le_log hz hbd
    have hp1 : (0:ℝ) < |t| ^ cc := by rw [hatt]; exact Real.rpow_pos_of_pos ht0 cc
    have hp2 : (0:ℝ) < Real.log |t| ^ wb := by rw [hatt]; exact Real.rpow_pos_of_pos hlogt wb
    have hp3 : (0:ℝ) < (c1 * Real.log |t| + d1) ^ wa := by
      rw [hatt]; exact Real.rpow_pos_of_pos (by positivity) wa
    rw [Real.log_mul (by positivity) (ne_of_gt hp2),
      Real.log_mul (by positivity) (ne_of_gt hp1),
      Real.log_mul (by positivity) (ne_of_gt hBw),
      Real.log_mul (ne_of_gt hslack) (ne_of_gt hp3)] at hlog
    rw [hatt] at hlog
    rw [Real.log_rpow ht0, Real.log_rpow hlogt,
      Real.log_rpow (by positivity : (0:ℝ) < c1 * Real.log t + d1)] at hlog
    have heqA : c1 * Real.log t + d1 = Real.log t * (c1 + d1 / Real.log t) := by
      field_simp
    rw [heqA, Real.log_mul (ne_of_gt hlogt) (ne_of_gt hAt), mul_add] at hlog
    rw [mul_sub] at herr
    have hcomb : wa * Real.log (Real.log t) + wb * Real.log (Real.log t)
        = Real.log (Real.log t) := by rw [← add_mul, hwsum, one_mul]
    rw [hatT]
    linarith [hlog, herr, hcomb]

/-- **Tight, genuinely pointwise log-bridge**: unlike the other bridges in this file, there is no
`T`-window here at all. The multiplicative bound is taken at the ordinate `t` itself, with an
explicit nonnegative slack `err` (rather than a fixed shape like `1/|t|`), so the log form drops
out with *the same* `err`, additively, via `\log(1+x)\leq x`.

### Summary of Proof
No threshold beyond `|t| > 1` (for `\log|t|` to be positive) is needed — in particular nothing
like `T > 10¹²`. Nothing calls this at present: `fiori_zeta_interpolation_tight` and `_1c_tight`
already state their conclusions in log form, so they perform this step inline.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** none. -/
theorem log_bound_pointwise_tight {L A B c w err t : ℝ} (hL : 0 ≤ L)
    (hA : 0 < A) (hB : 0 < B) (herr : 0 ≤ err) (ht : (1:ℝ) < |t|)
    (hnn : 0 ≤ c * Real.log |t| + w * Real.log (Real.log |t|) + Real.log A + Real.log B)
    (hbd : L ≤ (1 + err) * A * B * |t| ^ c * Real.log |t| ^ w) :
    Real.log L ≤ c * Real.log |t| + w * Real.log (Real.log |t|) + Real.log A + Real.log B
      + err := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have hlogt : 0 < Real.log |t| := Real.log_pos ht
  have hslack : (0:ℝ) < 1 + err := by linarith
  have hlogslack : Real.log (1 + err) ≤ err := by
    calc Real.log (1 + err) ≤ (1 + err) - 1 := Real.log_le_sub_one_of_pos hslack
      _ = err := by ring
  rcases eq_or_lt_of_le hL with hz | hz
  · rw [← hz, Real.log_zero]
    linarith
  · have hlog := Real.log_le_log hz hbd
    have hp1 : (0:ℝ) < |t| ^ c := Real.rpow_pos_of_pos ht0 c
    have hp2 : (0:ℝ) < Real.log |t| ^ w := Real.rpow_pos_of_pos hlogt w
    rw [Real.log_mul (by positivity) (ne_of_gt hp2),
      Real.log_mul (by positivity) (ne_of_gt hp1),
      Real.log_mul (by positivity) (ne_of_gt hB),
      Real.log_mul (ne_of_gt hslack) (ne_of_gt hA)] at hlog
    rw [Real.log_rpow ht0, Real.log_rpow hlogt] at hlog
    linarith [hlog, hlogslack]

/-- **Log-form bridge, `t`-indexed variant.** `interpolated_bound_2`'s conclusion is stated in terms
of
`log|t|`, `loglog|t|` at the actual ordinate rather than at `T`, so no window conversion is needed
there — only the `(1 + 1/|t|)` slack has to be absorbed.

### Summary of Proof
The proof gives `2/T`; the conclusion is stated with `3/T` to match `log_bound_of_interp`, so that
all four `interpolated_bound_*` carry the same error term.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `interpolated_bound_2`. -/
theorem log_bound_of_interp_self {A B c w T t L : ℝ} (hL : 0 ≤ L)
    (hA : 0 < A) (hB : 0 < B) (hT : (10 : ℝ) ^ (12 : ℕ) < T)
    (ht : t ∈ Set.Icc (T - 1) (T + 1))
    (hnn : 0 ≤ c * Real.log |t| + w * Real.log (Real.log |t|) + Real.log A + Real.log B)
    (hbd : L ≤ (1 + 1 / |t|) * A * B * |t| ^ c * Real.log |t| ^ w) :
    Real.log L < c * Real.log |t| + w * Real.log (Real.log |t|) + Real.log A + Real.log B
      + 3 / T := by
  have hTbig : (1000000000000 : ℝ) < T := by norm_num at hT; linarith
  have hT0 : (0:ℝ) < T := by linarith
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  have hatt : |t| = t := abs_of_pos ht0
  have ht1 : (1:ℝ) < t := by linarith [ht.1]
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hslack : (0:ℝ) < 1 + 1 / |t| := by rw [hatt]; positivity
  have hlogslack : Real.log (1 + 1 / |t|) < 3 / T := by
    rw [hatt]
    have h1 : Real.log (1 + 1 / t) ≤ 1 / t := by
      calc Real.log (1 + 1 / t) ≤ (1 + 1 / t) - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / t := by ring
    have h2 : 1 / t < 3 / T := by
      rw [div_lt_div_iff₀ ht0 hT0]
      linarith [ht.1]
    linarith
  rcases eq_or_lt_of_le hL with hz | hz
  · rw [← hz, Real.log_zero]
    have : (0:ℝ) < 3 / T := by positivity
    linarith
  · have hlog := Real.log_le_log hz hbd
    have hp1 : (0:ℝ) < |t| ^ c := by rw [hatt]; exact Real.rpow_pos_of_pos ht0 c
    have hp2 : (0:ℝ) < Real.log |t| ^ w := by rw [hatt]; exact Real.rpow_pos_of_pos hlogt w
    rw [Real.log_mul (by positivity) (ne_of_gt hp2),
      Real.log_mul (by positivity) (ne_of_gt hp1),
      Real.log_mul (by positivity) (ne_of_gt hB),
      Real.log_mul (ne_of_gt hslack) (ne_of_gt hA)] at hlog
    rw [hatt] at hlog ⊢
    rw [Real.log_rpow ht0, Real.log_rpow hlogt] at hlog
    rw [hatt] at hlogslack
    linarith [hlog, hlogslack]
