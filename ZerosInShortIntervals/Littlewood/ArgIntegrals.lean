/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Background.ExternalFacts

/-! # Bounding integrals of `Δ arg f` (`\S \ref{sec:argintegrals}`, §3.1)

This file formalizes `\S \ref{sec:argintegrals}` (§3.1) of `ZerosInShortIntervals.tex`,
the re-interpretation of Backlund's trick used to bound `∫ Δ arg f` directly (rather than bounding
`arg f` pointwise), for a general function `f` satisfying `f(s̄) = \overline{f(s)}`.

**Tex results formalized here** (numbering per the current compiled PDF):
`Lemma \ref{lem:integralofarg}` (Lemma 28) → `integralofarg`;
`Lemma \ref{lem:supremumforarg}` (Lemma 29) → `supremumforarg_left`/`_right`/`_full`;
`Theorem \ref{thm:arg-integrals}` (Theorem 31) → `arg_integrals`.
`Equation \eqref{eq:eta}` (Equation 15) defines the `η` used throughout.

**This file is unconditional**: it declares no hypothesis-class section variable, so every
statement in it depends on nothing but `propext`, `Classical.choice` and `Quot.sound`. That is
deliberate — see the comment before `section IntegralOfArgIngredients` below.

**Ordering convention.** Every result in this file uses `σ0 < c < σ1` (`σ0 ≤ c ≤ σ1` where
non-strict suffices) — `σ0` the "far" boundary that the disk of radius `c-σ0` is built from, `σ1`
the "near" boundary close to `c` — and, where needed for the log-difference denominator below to
stay positive across the relevant domain, `(σ0+σ1)/2 < c`. This matches Lemmas 28/29,
`Lemma \ref{lem:littlewood-argsetup}` (Lemma 27) and Theorem 31 throughout
`\S \ref{sec:littlewood}` (Section 3).

**The chain.** `integralofarg` (Lemma 28) and `argSupConst_le_of_le` (Lemma 29) feed
`deltaArg_bound_finite_N`, the finite-`N` Backlund bound, which with Backlund's trick
(`ExternalFacts.backlund_trick`, `N → ∞`) gives `arg_integrals` (Theorem 31). Every statement in
the file matches the tex's own display, including the absolute value and the `∫_{σ1}^{σ0}`
orientation of Lemma 28.

**`Real.log 0 = 0` and punctured domains.** `argSupConst` and `supremumforarg_left/right/full`
all take their supremum over a domain **punctured at `σ = c`** (`Set.Ico`/`Set.Ioc`/a
set-difference, in place of the closed `Set.Icc` the source writes). The source's `log 0 = -∞`
reading makes the ratio `0` there, which is inert; Lean's total `Real.log` would instead give a
spurious finite value that can exceed `c-σ_0`. See `argSupConst`'s docstring for the full
discussion; the two readings agree, and the tex is deliberately left with the more readable
one. -/

/-- **`Δ arg f(x+iT)|ᵃᵇ` for a general continuously-varying argument function `argf`**,
specialized to the horizontal segment at height `T`.

### Summary of Proof
A definition, `argf(b+iT) - argf(a+iT)`. It is the `Δ arg f(x+iT)|_{σ1}^{u}` notation introduced
just before `Lemma \ref{lem:integralofarg}` (Lemma 28).

### Lean Notes
Taken as a definition rather than derived, since the tex fixes `arg` only up to the
continuous-variation convention described after Equation `\ref{eq:zerodensityintegral}`
(Equation 13). Parameterising over an arbitrary `argf` keeps that convention out of the
statements that use it.

### References
tex: the `Δ arg` notation introduced before `\ref{lem:integralofarg}` (Lemma 28); the `arg`
convention is fixed after Equation `\ref{eq:zerodensityintegral}` (Equation 13).

### Dependencies
**Depends on:** none.
**Used by:** `integralofarg`, `deltaArg_bound_finite_N`. -/
noncomputable def deltaArgGen (argf : ℂ → ℝ) (T a b : ℝ) : ℝ :=
  argf (b + T * Complex.I) - argf (a + T * Complex.I)

/-- `F_N(w) = (1/2)(f(w+c+iT)^N + f(w+c-iT)^N)`, from the paragraph preceding
`Lemma \ref{lem:integralofarg}` (Lemma 28), viewed as a function of the complex variable `w` (so
that `w = 0` corresponds to `s = c`).

### Summary of Proof
A definition. The point of `F_N` is that `Re(f(c+u+iT)^N) = F_N(u)` for real `u`, so the
real-axis sign changes of `F_N` count the `π/N`-steps of `arg f` — the amplification that makes
the step-function comparison in Lemma 28's proof sharp as `N → ∞`.

### Lean Notes
Viewed as a function of the complex variable `w`, so that `w = 0` corresponds to `s = c`.

### References
tex: the `F_N` display in the paragraph preceding `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** none.
**Used by:** `Ffun_analyticOnNhd`, `Ffun_ofReal_sub`, `integralofarg`,
`log_norm_Ffun_circleMap_le`, `circleAverage_log_norm_Ffun_le`, `deltaArg_bound_finite_N`,
`arg_integrals`. -/
noncomputable def Ffun (f : ℂ → ℂ) (c T : ℝ) (N : ℕ) : ℂ → ℂ :=
  fun w => (1 / 2) * (f (w + c + T * Complex.I) ^ N + f (w + c - T * Complex.I) ^ N)

/-- `n_g(u)`, the number of complex zeros of `g` (with multiplicity) in the closed ball of radius
`u` around `0`, as used for `n_{F_N}(u)` in `Lemma \ref{lem:integralofarg}` (Lemma 28).

### Summary of Proof
A definition: the number of complex zeros of `g`, with multiplicity, in the closed ball of radius
`u` about `0`.

### Lean Notes
Realized via Mathlib's `MeromorphicOn.divisor` summed over the ball, which counts with
multiplicity *and sign*. For the analytic `F_N` of Lemma 28 the divisor is nonnegative, so this
agrees with the tex's plain zero count.

### References
tex: `n_{F_N}(u)` in `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** none.
**Used by:** `ballZeroCount_eq_sum`, `ballZeroCount_nonneg`, `deltaArg_bound_finite_N`,
`integral_ballZeroCount_div_eq`, `integralofarg`, `sum_log_le_integral_ballZeroCount`. -/
noncomputable def ballZeroCount (g : ℂ → ℂ) (u : ℝ) : ℤ :=
  ∑ᶠ z, MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) u) z

/-- **`C_{c,σ0,σ1} = sup_{σ∈[σ0,σ1]} (σ-σ0)/(log(c-σ0)-log|σ-c|)`**, exactly as defined in
`Lemma \ref{lem:integralofarg}` (Lemma 28).

### Summary of Proof
A definition. It is the maximum possible ratio between the weight a zero receives in the
step-function sum bounding `∫Δ arg f` and the weight it receives in the `n_{F_N}(u)/u` integral —
which is why Lemma 28 carries it as a factor.

### Lean Notes
The numerator is `σ-σ0`, matching the tex. This is the quantity
`Lemma \ref{lem:supremumforarg}` (Lemma 29) exists to bound by `c-σ0`, and `supremumforarg_full`
below proves exactly that bound.

**Deliberate discrepancy with the tex: the domain is punctured at `σ = c`.** The tex takes the
supremum over the closed `[σ_0,σ_1]`, which contains `c`. There `|σ-c| = 0` and the tex reads
`log 0 = -∞`, so the denominator is infinite and the ratio is `(c-σ_0)/∞ = 0` — an informal but
entirely standard reading, and one that is easier to state than any punctured version. That value
`0` can never be the supremum, since the supremum is `c-σ_0 > 0`, so the point contributes
nothing and the tex's `C_{c,σ_0,σ_1}` is exactly the punctured supremum.

Lean's `Real.log` is **total**, with `log 0 = 0` rather than `-∞`. So on a closed domain the
ratio at `σ = c` would evaluate not to `0` but to `(c-σ_0)/log(c-σ_0)`, a spurious finite value
that can genuinely exceed `c-σ_0` — precisely when `c-σ_0 ∈ (1,e)`, and unboundedly so as
`c-σ_0 → 1⁺` (tabulated in `Code/verify_argSupConst_window.py`). That is an artifact of
totality, with no mathematical content whatever.

Excluding `σ = c` therefore captures the tex's *meaning* rather than its literal formula, and it
is what makes `supremumforarg_full` — which bounds exactly this punctured supremum — discharge
the bound `argSupConst ≤ c-σ_0` that Lemma 28 needs. The alternative, formalizing `1/∞ = 0` via
`EReal` or a junk-value convention, is possible but buys nothing here: at the call site `c` is
assumed not to be a zero of `f`, so the excluded point never arises.

**The tex is deliberately left as it stands** — the `1/∞ = 0` reading is the more readable
statement, and the two agree. Recorded so the difference is not later mistaken for an error in
either document.

### References
tex: the `C_{c,σ_0,σ_1}` display in `\ref{lem:integralofarg}` (Lemma 28), tex line 948. Bounded by
`\ref{lem:supremumforarg}` (Lemma 29).

### Dependencies
**Depends on:** none.
**Used by:** `weight_le_argSupConst`, `argSupConst_nonneg`, `integralofarg`, `argSupConst_le`,
`argSupConst_le_of_le`, `deltaArg_bound_finite_N`. -/
noncomputable def argSupConst (c σ0 σ1 : ℝ) : ℝ :=
  sSup ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' (Set.Icc σ0 σ1 \ {c}))

/- This file declares no hypothesis-class section variable, and every statement in it is therefore
unconditional.  That is deliberate and worth preserving: `arg_integrals` (Theorem 31) is the
paper's own technical contribution, it is a general statement about a conjugation-symmetric
analytic `f` rather than anything zeta-specific, and it is the intended Palomar Stage A
submission -- which requires that its proof term depend on nothing but `propext`,
`Classical.choice` and `Quot.sound`.  Its one external input, `ExternalFacts.backlund_trick`, is
proved outright and is section-scoped there to stay outside `[LiteratureInputs]`.  If a future
edit makes something here need a hypothesis class, put it in its own `section` rather than adding
a file-level `variable`. -/

section IntegralOfArgIngredients

open MeasureTheory intervalIntegral Set

/-! ### The ingredients of `integralofarg`

Lemma 28 is Backlund's trick integrated: `|Δ arg f|` along the segment is bounded by a step
function that jumps by `π/N` at each real zero of `F_N`, and the integrated step function is
compared with `∫₀^{c-σ0} n_{F_N}(u)/u du`. The lemmas below supply, in order: the pointwise
`[σ0, c)` bound on the ratio defining `C_{c,σ0,σ1}` (shared with Lemma 29); analyticity of
`F_N` on the disc `|w| ≤ c-σ0` (the lower disc by conjugate reflection); the real-axis identity
`F_N(x-c) = Re f(x+iT)^N = ‖f‖^N cos(N·arg f)`; the multiplicity bookkeeping for the zeros of
`F_N` (`MeromorphicOn.divisor`, finite support, positive multiplicities, finite order by the
identity theorem); `n_{F_N}(u)` as a finite sum over those zeros; the indicator integrals
`∫₀ᴿ 1_{a ≤ u} u⁻¹ du = log(R/a)`; the Nevanlinna-type comparison
`∑_ρ log(R/|ρ|) ≤ ∫₀ᴿ n(u)/u du`; the intermediate-value counting argument behind the step
function; the integral of the step function; and the bound of each zero's weight by
`C_{c,σ0,σ1}`. -/

/-- **Pointwise form of `Lemma \ref{lem:supremumforarg}` (Lemma 29)'s first claim:** for
`σ0 ≤ σ < c` the ratio `(σ-σ0)/(log(c-σ0)-log|σ-c|)` never exceeds `c-σ0`.

### Summary of Proof
On `[σ0,c)` we have `|σ-c| = c-σ`, so the bound to prove is
`(σ-σ0) ≤ (c-σ0)(log(c-σ0)-log(c-σ))` once the denominator is known positive. Substituting
`t = (c-σ)/(c-σ0) ∈ (0,1]` turns it into `1-t ≤ -log t`, i.e. the tangent-line inequality
`log t ≤ t-1` (`Real.log_le_sub_one_of_pos`).

That is the substance of the source's critical-point computation in closed form: the source
differentiates the ratio, finds the critical point `σ̂` solving
`(log(c-σ0)-log(c-σ̂))(c-σ̂) = σ̂-σ0`, and evaluates the critical value as `c-σ̂ ≤ c-σ0`.

### Lean Notes
Factored out because both `supremumforarg_left` (whose domain is exactly `[σ0,c)`) and
`supremumforarg_full` (on the left half of its domain) need it, as does `argRatio_bddAbove`
below. The degenerate endpoint `σ = σ0` is handled separately: there numerator and denominator
both vanish, and Lean's `x/0 = 0` convention gives the ratio `0 ≤ c-σ0`.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), first claim, tex line 981.

### Dependencies
**Depends on:** none.
**Used by:** `argRatio_bddAbove`, `argSupConst_le_of_le`, `supremumforarg_full`,
`supremumforarg_left`. -/
private theorem argRatio_le_of_lt {σ0 c σ : ℝ} (hσ0c : σ0 < c) (hσ0 : σ0 ≤ σ) (hσc : σ < c) :
    (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|) ≤ c - σ0 := by
  have hc0 : (0:ℝ) < c - σ0 := sub_pos.mpr hσ0c
  have habs : |σ - c| = c - σ := by rw [abs_of_neg (by linarith : σ - c < 0)]; ring
  rw [habs]
  rcases eq_or_lt_of_le hσ0 with heq | hlt
  · rw [← heq]
    simp only [sub_self, zero_div]
    linarith
  · have hcσ : (0:ℝ) < c - σ := by linarith
    have hd : 0 < Real.log (c - σ0) - Real.log (c - σ) := by
      have := Real.log_lt_log hcσ (by linarith : c - σ < c - σ0)
      linarith
    rw [div_le_iff₀ hd]
    have h1 : Real.log ((c - σ) / (c - σ0)) ≤ (c - σ) / (c - σ0) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hcσ hc0)
    rw [Real.log_div hcσ.ne' hc0.ne'] at h1
    have h2 : (c - σ) / (c - σ0) - 1 = -((σ - σ0) / (c - σ0)) := by
      field_simp
      ring
    rw [h2] at h1
    have key : (σ - σ0) / (c - σ0) ≤ Real.log (c - σ0) - Real.log (c - σ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left key hc0.le
    have hsimp : (c - σ0) * ((σ - σ0) / (c - σ0)) = σ - σ0 := by field_simp
    rw [hsimp] at hmul
    exact hmul

/-- **Conjugate reflection of analyticity**: if `conj (f s) = f (conj s)` and `f` is analytic at
`z`, then `f` is analytic at `conj z`.

### Summary of Proof
`f = conj ∘ f ∘ conj`, and Mathlib's `DifferentiableAt.conj_conj` makes the right-hand side
differentiable on the conjugate of the open set `{w | AnalyticAt ℂ f w}` (`isOpen_analyticAt`);
differentiability on an open set is analyticity (`DifferentiableOn.analyticOnNhd`).

### References
No tex counterpart — the tex takes analyticity of `f` on both discs `|s - (c ± iT)| ≤ c-σ0` for
granted, which for `f(s̄) = \overline{f(s)}` follows from the upper one.

### Dependencies
**Depends on:** none.
**Used by:** `Ffun_analyticOnNhd`. -/
theorem analyticAt_conj_of_conj_symm {f : ℂ → ℂ}
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))
    {z : ℂ} (hz : AnalyticAt ℂ f z) : AnalyticAt ℂ f ((starRingEnd ℂ) z) := by
  have hfeq : f = (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) := by
    funext s
    simp only [Function.comp]
    rw [hf ((starRingEnd ℂ) s), Complex.conj_conj]
  have hopen : IsOpen {w : ℂ | AnalyticAt ℂ f w} := isOpen_analyticAt ℂ f
  have hopen' : IsOpen ((starRingEnd ℂ) ⁻¹' {w : ℂ | AnalyticAt ℂ f w}) :=
    hopen.preimage Complex.continuous_conj
  have hdiff' : DifferentiableOn ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ))
      ((starRingEnd ℂ) ⁻¹' {w : ℂ | AnalyticAt ℂ f w}) := by
    intro w hw
    have hw' : AnalyticAt ℂ f ((starRingEnd ℂ) w) := hw
    have := hw'.differentiableAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have han := hdiff'.analyticOnNhd hopen'
  rw [← hfeq] at han
  apply han
  change AnalyticAt ℂ f ((starRingEnd ℂ) ((starRingEnd ℂ) z))
  rw [Complex.conj_conj]
  exact hz

/-- **`F_N` is analytic on the disc `|w| ≤ R`** when `f` is conjugate-symmetric and analytic on
`|s - (c+iT)| ≤ R`.

### Summary of Proof
`w ↦ f(w+c+iT)` is analytic by composition; `w ↦ f(w+c-iT)` because
`w + c - iT = conj(conj w + c + iT)` and `analyticAt_conj_of_conj_symm`; then sums, powers and
constants.

### References
tex: the paragraph defining `F_N` before `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `Ffun`, `analyticAt_conj_of_conj_symm`.
**Used by:** `deltaArg_bound_finite_N`, `integralofarg`. -/
theorem Ffun_analyticOnNhd {f : ℂ → ℂ}
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))
    {c T R : ℝ} (hfan : AnalyticOnNhd ℂ f (Metric.closedBall ((c : ℂ) + T * Complex.I) R))
    (N : ℕ) :
    AnalyticOnNhd ℂ (Ffun f c T N) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  have hwn : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall] using hw
  have hmem1 : w + c + T * Complex.I ∈ Metric.closedBall ((c : ℂ) + T * Complex.I) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : w + c + T * Complex.I - (c + T * Complex.I) = w := by ring
    rw [this]; exact hwn
  have hmem2 : (starRingEnd ℂ) w + c + T * Complex.I
      ∈ Metric.closedBall ((c : ℂ) + T * Complex.I) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : (starRingEnd ℂ) w + c + T * Complex.I - (c + T * Complex.I) = (starRingEnd ℂ) w := by
      ring
    rw [this, Complex.norm_conj]; exact hwn
  have haff1 : AnalyticAt ℂ (fun w : ℂ => w + c + T * Complex.I) w := by fun_prop
  have haff2 : AnalyticAt ℂ (fun w : ℂ => w + c - T * Complex.I) w := by fun_prop
  have h1 : AnalyticAt ℂ (fun w : ℂ => f (w + c + T * Complex.I)) w :=
    AnalyticAt.comp (f := fun w : ℂ => w + c + T * Complex.I) (hfan _ hmem1) haff1
  have hpt : (starRingEnd ℂ) ((starRingEnd ℂ) w + c + T * Complex.I) = w + c - T * Complex.I := by
    apply Complex.ext <;> simp
    ring
  have h2 : AnalyticAt ℂ (fun w : ℂ => f (w + c - T * Complex.I)) w := by
    have hA : AnalyticAt ℂ f (w + c - T * Complex.I) := by
      rw [← hpt]
      exact analyticAt_conj_of_conj_symm hf (hfan _ hmem2)
    exact AnalyticAt.comp (f := fun w : ℂ => w + c - T * Complex.I) hA haff2
  unfold Ffun
  exact analyticAt_const.mul ((h1.pow N).add (h2.pow N))

/-- **On the real axis `F_N(x-c) = Re f(x+iT)^N`.**

### Summary of Proof
`f(x+c-c-iT) = f(conj(x+iT)) = conj f(x+iT)` by `hf`, and `z^N + conj(z^N) = 2 Re(z^N)`
(`Complex.add_conj`).

### References
tex: "`Re(f(c+u+iT)^N) = F_N(u)`" before `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `Ffun`.
**Used by:** `integralofarg`. -/
theorem Ffun_ofReal_sub {f : ℂ → ℂ}
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s)) (c T : ℝ) (N : ℕ) (x : ℝ) :
    Ffun f c T N ((x - c : ℝ) : ℂ) = (((f (x + T * Complex.I)) ^ N).re : ℂ) := by
  unfold Ffun
  have e1 : ((x - c : ℝ) : ℂ) + c + T * Complex.I = x + T * Complex.I := by push_cast; ring
  have e2 : ((x - c : ℝ) : ℂ) + c - T * Complex.I = (starRingEnd ℂ) (x + T * Complex.I) := by
    apply Complex.ext <;> simp
  rw [e1, e2, ← hf, ← map_pow, Complex.add_conj]
  push_cast
  ring

/-- **`Re (z^N) = r^N cos(Nθ)` for `z = r e^{iθ}`** with `r, θ` real.

### Summary of Proof
`(r e^{iθ})^N = r^N e^{iNθ}` and `Complex.exp_ofReal_mul_I_re`.

### References
No tex counterpart (the tex writes `Re f^N = |f|^N cos(N arg f)` tacitly).

### Dependencies
**Depends on:** none.
**Used by:** `integralofarg`. -/
theorem re_pow_of_polar {z : ℂ} {r θ : ℝ} (hz : z = (r : ℂ) * Complex.exp (θ * Complex.I))
    (N : ℕ) : (z ^ N).re = r ^ N * Real.cos (N * θ) := by
  rw [hz, mul_pow, ← Complex.exp_nat_mul]
  have : (N : ℂ) * (θ * Complex.I) = ((N * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Finite order everywhere**: an analytic function on a preconnected set that is nonzero at
one point has finite `analyticOrderAt` at every point of the set.

### Summary of Proof
Infinite order means vanishing near the point; the identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) then forces `F ≡ 0`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `mem_divisor_support_iff`, `sum_log_le_integral_ballZeroCount`. -/
theorem analyticOrderAt_ne_top_of_ne_zero {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hF0 : F z₀ ≠ 0) {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt F z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz htop hz₀
  exact hF0 this

/-- **Multiplicities are `≥ 0`** at points of analyticity.

### Summary of Proof
`AnalyticAt.meromorphicOrderAt_eq` and a case split on the `ℕ∞`-valued order.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `ballZeroCount_nonneg`, `sum_log_le_integral_ballZeroCount`. -/
theorem untop_order_nonneg {F : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ F z) :
    (0 : ℤ) ≤ (meromorphicOrderAt F z).untop₀ := by
  rw [hz.meromorphicOrderAt_eq]
  induction (analyticOrderAt F z) using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- **The multiplicity vanishes where `F` does not.**

### Summary of Proof
`analyticOrderAt_eq_zero`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `mem_divisor_support_iff`, `ballZeroCount_eq_sum`. -/
theorem untop_order_eq_zero_of_ne_zero {F : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ F z)
    (h0 : F z ≠ 0) : (meromorphicOrderAt F z).untop₀ = 0 := by
  rw [hz.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h0)]
  simp

/-- **At a zero of finite order the multiplicity is `≥ 1`.**

### Summary of Proof
The order is neither `0` (`analyticOrderAt_eq_zero`) nor `⊤`, so it is a positive natural.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `mem_divisor_support_iff`, `sum_log_le_integral_ballZeroCount`. -/
theorem one_le_untop_order_of_eq_zero {F : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ F z)
    (h0 : F z = 0) (hfin : analyticOrderAt F z ≠ ⊤) :
    (1 : ℤ) ≤ (meromorphicOrderAt F z).untop₀ := by
  rw [hz.meromorphicOrderAt_eq]
  have hne : analyticOrderAt F z ≠ 0 := by
    intro h
    rw [analyticOrderAt_eq_zero] at h
    rcases h with h | h
    · exact h hz
    · exact h h0
  generalize hord : analyticOrderAt F z = o at hfin hne
  induction o using ENat.recTopCoe with
  | top => exact absurd rfl hfin
  | coe n =>
    have hn : n ≠ 0 := by
      intro h
      apply hne
      rw [h]
      simp
    have : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp only [ENat.map_natCast, WithTop.coe_natCast, WithTop.untop₀_natCast, Nat.one_le_cast,
      ge_iff_le]
    exact_mod_cast this

/-- **The zeros of `F` in the closed disc are the support of its divisor there**, when `F` is
analytic on the disc and `F 0 ≠ 0`.

### Summary of Proof
`MeromorphicOn.divisor_apply`/`divisor_def` reduce the divisor to the multiplicity, which is `0`
off the zeros (`untop_order_eq_zero_of_ne_zero`) and `≥ 1` at them
(`one_le_untop_order_of_eq_zero`, with finite order from `analyticOrderAt_ne_top_of_ne_zero`).

### References
tex: `n_{F_N}(u)` "denotes the number of complex zeros" — this identifies the tex's zero count
with the divisor sum used in `ballZeroCount`.

### Dependencies
**Depends on:** `untop_order_eq_zero_of_ne_zero`, `one_le_untop_order_of_eq_zero`,
`analyticOrderAt_ne_top_of_ne_zero`.
**Used by:** `ae_circleMap_ne_zero`, `ballZeroCount_eq_sum`, `ballZeroCount_nonneg`,
`integral_ballZeroCount_div_eq`, `integralofarg`, `sum_log_le_integral_ballZeroCount`. -/
theorem mem_divisor_support_iff {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) (z : ℂ) :
    z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall 0 R)).toFinset
      ↔ z ∈ Metric.closedBall (0 : ℂ) R ∧ F z = 0 := by
  rw [Set.Finite.mem_toFinset]
  change z ∈ Function.support _ ↔ _
  rw [Function.mem_support]
  constructor
  · intro hne
    have hz : z ∈ Metric.closedBall (0 : ℂ) R := by
      by_contra hz
      apply hne
      rw [MeromorphicOn.divisor_def]
      simp only [hz, and_false, ite_false]
    refine ⟨hz, ?_⟩
    by_contra h0
    apply hne
    rw [MeromorphicOn.divisor_apply hF.meromorphicOn hz]
    exact untop_order_eq_zero_of_ne_zero (hF z hz) h0
  · rintro ⟨hz, h0⟩
    rw [MeromorphicOn.divisor_apply hF.meromorphicOn hz]
    have := one_le_untop_order_of_eq_zero (hF z hz) h0
      (analyticOrderAt_ne_top_of_ne_zero hF (convex_closedBall (0 : ℂ) R).isPreconnected
        (Metric.mem_closedBall_self hR.le) hF0 hz)
    omega

/-- **`n_F(u)` as a finite sum over the zeros in the big disc**, for `u ≤ R`.

### Summary of Proof
The divisor of the small disc is supported in the big disc's zero set
(`finsum_eq_finsetSum_of_support_subset`), and equals the multiplicity inside the small disc
and `0` outside (`MeromorphicOn.divisor_apply`, `divisor_def`).

### References
tex: `n_{F_N}(u)` in `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `ballZeroCount`, `mem_divisor_support_iff`, `untop_order_eq_zero_of_ne_zero`.
**Used by:** `ballZeroCount_nonneg`, `integral_ballZeroCount_div_eq`,
`sum_log_le_integral_ballZeroCount`. -/
theorem ballZeroCount_eq_sum {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) {u : ℝ} (hu : u ≤ R) :
    ballZeroCount F u
      = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset,
          (if ‖z‖ ≤ u then (meromorphicOrderAt F z).untop₀ else 0) := by
  have hmemS := mem_divisor_support_iff hR hF hF0
  have hsub : Metric.closedBall (0 : ℂ) u ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall hu
  have hmer : MeromorphicOn F (Metric.closedBall (0 : ℂ) u) := (hF.mono hsub).meromorphicOn
  unfold ballZeroCount
  rw [finsum_eq_finsetSum_of_support_subset]
  · apply Finset.sum_congr rfl
    intro z _
    by_cases hzu : ‖z‖ ≤ u
    · have hzb : z ∈ Metric.closedBall (0 : ℂ) u := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      rw [MeromorphicOn.divisor_apply hmer hzb]
      simp only [hzu, ite_true]
    · have hzb : z ∉ Metric.closedBall (0 : ℂ) u := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      rw [MeromorphicOn.divisor_def]
      simp only [hzb, and_false, ite_false, hzu]
  · intro z hz
    rw [Function.mem_support] at hz
    have hzb : z ∈ Metric.closedBall (0 : ℂ) u := by
      by_contra h
      apply hz
      rw [MeromorphicOn.divisor_def]
      simp only [h, and_false, ite_false]
    rw [Finset.mem_coe, hmemS]
    refine ⟨hsub hzb, ?_⟩
    by_contra h0
    apply hz
    rw [MeromorphicOn.divisor_apply hmer hzb]
    exact untop_order_eq_zero_of_ne_zero (hF z (hsub hzb)) h0

/-- **A small closed disc about `0` on which `F` does not vanish**, of radius `≤ R`.

### Summary of Proof
Continuity of `F` at `0` and `F 0 ≠ 0` (`ContinuousAt.eventually_ne`,
`Metric.eventually_nhds_iff`).

### References
No tex counterpart — it is what makes `n_{F_N}(u)/u` integrable at `u = 0` (the tex's `F_N(0) ≠ 0`).

### Dependencies
**Depends on:** none.
**Used by:** `integral_ballZeroCount_div_eq`, `sum_log_le_integral_ballZeroCount`. -/
theorem exists_pos_radius_ne_zero {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) r₀, F z ≠ 0 := by
  have hcont : ContinuousAt F 0 := (hF 0 (Metric.mem_closedBall_self hR.le)).continuousAt
  have hev : ∀ᶠ z in nhds (0 : ℂ), F z ≠ 0 := hcont.eventually_ne hF0
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεF⟩ := hev
  refine ⟨min (ε / 2) R, by positivity, min_le_right _ _, ?_⟩
  intro z hz
  apply hεF
  rw [Metric.mem_closedBall] at hz
  calc dist z 0 ≤ min (ε / 2) R := hz
    _ ≤ ε / 2 := min_le_left _ _
    _ < ε := by linarith

/-- **`u ↦ 1_{a ≤ u} u⁻¹` is integrable on `[0, R]`** for `0 < a ≤ R`.

### Summary of Proof
It vanishes on `(0, a)` and is continuous on `[a, R]`; glue with `IntervalIntegrable.trans`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_ballZeroCount_div_eq`, `sum_log_le_integral_ballZeroCount`. -/
theorem indicator_inv_intervalIntegrable {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    IntervalIntegrable (fun u : ℝ => if a ≤ u then u⁻¹ else 0) volume 0 R := by
  have h1 : IntervalIntegrable (fun u : ℝ => if a ≤ u then u⁻¹ else 0) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le]
    apply (integrableOn_zero (μ := volume) (s := Ioo 0 a)).congr_fun _ measurableSet_Ioo
    intro u hu
    simp only [show ¬ (a ≤ u) from not_le.mpr hu.2, ite_false]
  have h2 : IntervalIntegrable (fun u : ℝ => if a ≤ u then u⁻¹ else 0) volume a R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haR]
    have hcont : ContinuousOn (fun u : ℝ => u⁻¹) (Icc a R) :=
      continuousOn_inv₀.mono (fun u hu => ne_of_gt (lt_of_lt_of_le ha hu.1))
    apply hcont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro u hu
    simp only [hu.1, ite_true]
  exact h1.trans h2

/-- **`∫₀ᴿ 1_{a ≤ u} u⁻¹ du = log R - log a`** for `0 < a ≤ R`.

### Summary of Proof
Split at `a`: the integral over `(0, a)` vanishes (`setIntegral_congr_fun` on the open interval,
where the indicator is `0`), and over `[a, R]` the integrand is `u⁻¹` (`integral_inv_of_pos`).

### References
tex: the evaluation `∫_{|ρ|}^{c-σ0} du/u = log((c-σ0)/|ρ|)` implicit in the Nevanlinna identity
of `\ref{lem:integralofarg}` (Lemma 28)'s proof.

### Dependencies
**Depends on:** none.
**Used by:** `integral_ballZeroCount_div_eq`, `sum_log_le_integral_ballZeroCount`. -/
theorem integral_indicator_inv {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ∫ u in (0 : ℝ)..R, (if a ≤ u then u⁻¹ else 0) = Real.log R - Real.log a := by
  have h1 : IntervalIntegrable (fun u : ℝ => if a ≤ u then u⁻¹ else 0) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le]
    apply (integrableOn_zero (μ := volume) (s := Ioo 0 a)).congr_fun _ measurableSet_Ioo
    intro u hu
    simp only [show ¬ (a ≤ u) from not_le.mpr hu.2, ite_false]
  have h2 : IntervalIntegrable (fun u : ℝ => if a ≤ u then u⁻¹ else 0) volume a R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haR]
    have hcont : ContinuousOn (fun u : ℝ => u⁻¹) (Icc a R) :=
      continuousOn_inv₀.mono (fun u hu => ne_of_gt (lt_of_lt_of_le ha hu.1))
    apply hcont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro u hu
    simp only [hu.1, ite_true]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ u in (0 : ℝ)..a, (if a ≤ u then u⁻¹ else 0) = 0 := by
    rw [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      simp only [show ¬ (a ≤ u) from not_le.mpr hu.2, ite_false]
  have e2 : ∫ u in a..R, (if a ≤ u then u⁻¹ else 0) = ∫ u in a..R, u⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le haR] at hu
    simp only [hu.1, ite_true]
  rw [e1, e2, integral_inv_of_pos ha (ha.trans_le haR), zero_add,
    Real.log_div (ha.trans_le haR).ne' ha.ne']

/-- **The Nevanlinna-type comparison**: for a finite set `W` of zeros of `F` in the disc,
`∑_{w ∈ W} (log R - log ‖w‖) ≤ ∫₀ᴿ n_F(u)/u du`.

### Summary of Proof
`n_F(u) ≥ ∑_{w ∈ W} 1_{‖w‖ ≤ u}` pointwise (`ballZeroCount_eq_sum`, multiplicities `≥ 1`), both
sides vanish on `[0, r₀]` (`exists_pos_radius_ne_zero`) and are monotone on `[r₀, R]`, so both
`n_F(u)/u` and the comparison function are integrable (`MonotoneOn.intervalIntegrable`,
`IntervalIntegrable.mul_continuousOn`), `intervalIntegral.integral_mono_on` applies, and the
comparison integral is `∑_w (log R - log ‖w‖)` by `integral_indicator_inv`.

### Lean Notes
Only the inequality is needed for Lemma 28; the exact Nevanlinna identity
`∫₀ᴿ n(u)/u du = ∑_ρ m_ρ log(R/|ρ|)` over *all* zeros would follow by the same computation with
the weights `m_ρ` and `W` the whole support.

### References
tex: the display `∫_0^{c-σ0} n_{F_N}(u)/u du ≥ ∑_{S_L} … + ∑_{S_R} …` in the proof of
`\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `ballZeroCount`, `mem_divisor_support_iff`, `ballZeroCount_eq_sum`,
`untop_order_nonneg`, `one_le_untop_order_of_eq_zero`, `analyticOrderAt_ne_top_of_ne_zero`,
`exists_pos_radius_ne_zero`, `indicator_inv_intervalIntegrable`, `integral_indicator_inv`.
**Used by:** `integralofarg`. -/
theorem sum_log_le_integral_ballZeroCount {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0)
    {W : Finset ℂ} (hW : ∀ w ∈ W, w ∈ Metric.closedBall (0 : ℂ) R ∧ F w = 0) :
    ∑ w ∈ W, (Real.log R - Real.log ‖w‖) ≤ ∫ u in (0 : ℝ)..R, (ballZeroCount F u : ℝ) / u := by
  have hmemS := mem_divisor_support_iff hR hF hF0
  have hWS : W ⊆ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset := fun w hw => (hmemS w).mpr (hW w hw)
  have hm0 : ∀ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset,
      (0 : ℝ) ≤ ((meromorphicOrderAt F z).untop₀ : ℝ) := by
    intro z hz
    have := untop_order_nonneg (hF z ((hmemS z).mp hz).1)
    exact_mod_cast this
  have hm1 : ∀ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset,
      (1 : ℝ) ≤ ((meromorphicOrderAt F z).untop₀ : ℝ) := by
    intro z hz
    obtain ⟨hzb, hz0⟩ := (hmemS z).mp hz
    have := one_le_untop_order_of_eq_zero (hF z hzb) hz0
      (analyticOrderAt_ne_top_of_ne_zero hF (convex_closedBall (0 : ℂ) R).isPreconnected
        (Metric.mem_closedBall_self hR.le) hF0 hzb)
    exact_mod_cast this
  have hn : ∀ u, u ≤ R → (ballZeroCount F u : ℝ)
      = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset,
          (if ‖z‖ ≤ u then ((meromorphicOrderAt F z).untop₀ : ℝ) else 0) := by
    intro u hu
    rw [ballZeroCount_eq_sum hR hF hF0 hu]
    push_cast
    rfl
  obtain ⟨r₀, hr₀, hr₀R, hFr₀⟩ := exists_pos_radius_ne_zero hR hF hF0
  have hSr : ∀ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset, r₀ < ‖z‖ := by
    intro z hz
    obtain ⟨_, hz0⟩ := (hmemS z).mp hz
    by_contra h
    exact hFr₀ z (by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.mp h) hz0
  have hWr : ∀ w ∈ W, r₀ < ‖w‖ := fun w hw => hSr w (hWS hw)
  have hle : ∀ u, u ≤ R → ∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)
      ≤ (ballZeroCount F u : ℝ) := by
    intro u hu
    rw [hn u hu]
    calc ∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)
        ≤ ∑ w ∈ W, (if ‖w‖ ≤ u then ((meromorphicOrderAt F w).untop₀ : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro w hw
          split_ifs
          · exact hm1 w (hWS hw)
          · exact le_rfl
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hWS
          intro z hz _
          split_ifs
          · exact hm0 z hz
          · exact le_rfl
  have hn0 : ∀ u, u ≤ r₀ → (ballZeroCount F u : ℝ) = 0 := by
    intro u hu
    rw [hn u (hu.trans hr₀R)]
    apply Finset.sum_eq_zero
    intro z hz
    have := hSr z hz
    simp only [show ¬ (‖z‖ ≤ u) by linarith, ite_false]
  have hh0 : ∀ u, u ≤ r₀ → ∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0) = 0 := by
    intro u hu
    apply Finset.sum_eq_zero
    intro w hw
    have := hWr w hw
    simp only [show ¬ (‖w‖ ≤ u) by linarith, ite_false]
  have hmono_n : MonotoneOn (fun u => (ballZeroCount F u : ℝ)) (Icc r₀ R) := by
    intro u hu v hv huv
    simp only
    rw [hn u hu.2, hn v hv.2]
    apply Finset.sum_le_sum
    intro z hz
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans huv) h2
    · exact hm0 z hz
    · exact le_rfl
  have hmono_h : MonotoneOn (fun u => ∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)) (Icc r₀ R) := by
    intro u _ v _ huv
    apply Finset.sum_le_sum
    intro w _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans huv) h2
    · exact zero_le_one
    · exact le_rfl
  have hint : ∀ g : ℝ → ℝ, (∀ u, u ≤ r₀ → g u = 0) → MonotoneOn g (Icc r₀ R) →
      IntervalIntegrable (fun u => g u / u) volume 0 R := by
    intro g hg0 hgmono
    have h1 : IntervalIntegrable (fun u => g u / u) volume 0 r₀ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr₀.le]
      apply (integrableOn_zero (μ := volume) (s := Ioc 0 r₀)).congr_fun _ measurableSet_Ioc
      intro u hu
      simp [hg0 u hu.2]
    have h2 : IntervalIntegrable (fun u => g u / u) volume r₀ R := by
      have hg : IntervalIntegrable g volume r₀ R := by
        apply MonotoneOn.intervalIntegrable
        rwa [uIcc_of_le hr₀R]
      have hinv : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc r₀ R) := by
        apply continuousOn_inv₀.mono
        intro u hu
        rw [uIcc_of_le hr₀R] at hu
        exact ne_of_gt (lt_of_lt_of_le hr₀ hu.1)
      have := hg.mul_continuousOn hinv
      simpa [div_eq_mul_inv] using this
    exact h1.trans h2
  have hint_n := hint _ hn0 hmono_n
  have hint_h := hint _ hh0 hmono_h
  have hcmp : ∫ u in (0 : ℝ)..R, (∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)) / u
      ≤ ∫ u in (0 : ℝ)..R, (ballZeroCount F u : ℝ) / u := by
    apply intervalIntegral.integral_mono_on hR.le hint_h hint_n
    intro u hu
    exact div_le_div_of_nonneg_right (hle u hu.2) hu.1
  have heval : ∫ u in (0 : ℝ)..R, (∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)) / u
      = ∑ w ∈ W, (Real.log R - Real.log ‖w‖) := by
    have e1 : ∀ u : ℝ, (∑ w ∈ W, (if ‖w‖ ≤ u then (1 : ℝ) else 0)) / u
        = ∑ w ∈ W, (if ‖w‖ ≤ u then u⁻¹ else 0) := by
      intro u
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    simp_rw [e1]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro w hw
      have hwR : ‖w‖ ≤ R := by
        have := (hW w hw).1
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      exact integral_indicator_inv (hr₀.trans (hWr w hw)) hwR
    · intro w hw
      have hwR : ‖w‖ ≤ R := by
        have := (hW w hw).1
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      exact indicator_inv_intervalIntegrable (hr₀.trans (hWr w hw)) hwR
  linarith [hcmp, heval]

/-- **Lattice counting via the intermediate value theorem.** If every value strictly between `a`
and `b` is attained by `φ` on `(u, σ1)`, and every zero of `cos ∘ φ` there lies in `Z`, then `Z`
has at least `(b-a)/π - 1` elements `≥ u`.

### Summary of Proof
Each half-integer multiple `(m+½)π` strictly between `a` and `b` is attained at some
`x ∈ (u, σ1)`, where `cos φ(x) = 0`, so `x ∈ Z`; the map `x ↦ ⌊φ(x)/π⌋` sends it back to `m`, so
it is a surjection from `{x ∈ Z : u ≤ x}` onto those `m` (`Finset.card_le_card_of_surjOn`), of
which there are `(⌈b/π-½⌉ - ⌊a/π-½⌋ - 1)⁺ ≥ (b-a)/π - 1` (`Int.card_Ioo`).

### Lean Notes
This replaces the tex's "step function increasing by `π/N` at each zero of `Re f^N`" with a
counting statement that needs no bookkeeping of consecutive zeros: the argument may well cross
the same half-integer level several times, which only makes `Z` larger.

### References
tex: the step-function sentence in the proof of `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** none.
**Used by:** `argStep_bound`. -/
theorem lattice_count_le {φ : ℝ → ℝ} {u σ1 a b : ℝ}
    (hIVT : ∀ v, a < v → v < b → ∃ x ∈ Ioo u σ1, φ x = v)
    {Z : Finset ℝ} (hZ : ∀ x ∈ Ioo u σ1, Real.cos (φ x) = 0 → x ∈ Z) :
    (b - a) / Real.pi - 1 ≤ ((Z.filter (fun x => u ≤ x)).card : ℝ) := by
  have hπ := Real.pi_pos
  have hsurj : Set.SurjOn (fun x : ℝ => ⌊φ x / Real.pi⌋)
      (↑(Z.filter (fun x => u ≤ x)) : Set ℝ)
      (↑(Finset.Ioo ⌊a / Real.pi - 1 / 2⌋ ⌈b / Real.pi - 1 / 2⌉) : Set ℤ) := by
    intro m hm
    rw [Finset.mem_coe, Finset.mem_Ioo] at hm
    obtain ⟨h1, h2⟩ := hm
    have h1' : a / Real.pi - 1 / 2 < m := Int.floor_lt.mp h1
    have h2' : (m : ℝ) < b / Real.pi - 1 / 2 := Int.lt_ceil.mp h2
    have hva : a < ((m : ℝ) + 1 / 2) * Real.pi := by
      have : a / Real.pi < (m : ℝ) + 1 / 2 := by linarith
      exact (div_lt_iff₀ hπ).mp this
    have hvb : ((m : ℝ) + 1 / 2) * Real.pi < b := by
      have : (m : ℝ) + 1 / 2 < b / Real.pi := by linarith
      exact (lt_div_iff₀ hπ).mp this
    obtain ⟨x, hx, hφx⟩ := hIVT _ hva hvb
    have hcos : Real.cos (φ x) = 0 := by
      rw [hφx, Real.cos_eq_zero_iff]
      exact ⟨m, by ring⟩
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hZ x hx hcos, hx.1.le⟩
    · change ⌊φ x / Real.pi⌋ = m
      rw [hφx, mul_div_assoc, div_self hπ.ne', mul_one, Int.floor_eq_iff]
      constructor <;> linarith
  have hcard := Finset.card_le_card_of_surjOn _ hsurj
  rw [Int.card_Ioo] at hcard
  have h1 : (⌈b / Real.pi - 1 / 2⌉ - ⌊a / Real.pi - 1 / 2⌋ - 1 : ℤ)
      ≤ ((⌈b / Real.pi - 1 / 2⌉ - ⌊a / Real.pi - 1 / 2⌋ - 1).toNat : ℤ) := Int.self_le_toNat _
  have h2 : b / Real.pi - 1 / 2 ≤ (⌈b / Real.pi - 1 / 2⌉ : ℝ) := Int.le_ceil _
  have h3 : (⌊a / Real.pi - 1 / 2⌋ : ℝ) ≤ a / Real.pi - 1 / 2 := Int.floor_le _
  have hcard' : (((⌈b / Real.pi - 1 / 2⌉ - ⌊a / Real.pi - 1 / 2⌋ - 1).toNat : ℕ) : ℝ)
      ≤ ((Z.filter (fun x => u ≤ x)).card : ℝ) := by exact_mod_cast hcard
  have h1' : ((⌈b / Real.pi - 1 / 2⌉ - ⌊a / Real.pi - 1 / 2⌋ - 1 : ℤ) : ℝ)
      ≤ (((⌈b / Real.pi - 1 / 2⌉ - ⌊a / Real.pi - 1 / 2⌋ - 1).toNat : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this ⊢
    exact this
  have e : (b - a) / Real.pi - 1 = (b / Real.pi - 1 / 2) - (a / Real.pi - 1 / 2) - 1 := by ring
  rw [e]
  push_cast at h1'
  linarith

/-- **The step-function bound on the argument.** If `φ` is continuous on `[σ0,σ1]` and every zero
of `cos ∘ φ` in `(σ0,σ1)` lies in `Z`, then for `u ∈ [σ0,σ1]`,
`|φ u - φ σ1| ≤ π (#{x ∈ Z : u ≤ x} + 1)`.

### Summary of Proof
`intermediate_value_Ioo`/`intermediate_value_Ioo'` on `[u, σ1]` supply the hypothesis of
`lattice_count_le` for the two orientations of `φ(u)` versus `φ(σ1)`.

### References
tex: `|Δ arg f| ≤ (π/N)(k(u)+1)` in the proof of `\ref{lem:integralofarg}` (Lemma 28), at
`φ = N · arg f`.

### Dependencies
**Depends on:** `lattice_count_le`.
**Used by:** `integralofarg`. -/
theorem argStep_bound {φ : ℝ → ℝ} {σ0 σ1 : ℝ} (hφ : ContinuousOn φ (Icc σ0 σ1))
    {Z : Finset ℝ} (hZ : ∀ x ∈ Ioo σ0 σ1, Real.cos (φ x) = 0 → x ∈ Z)
    {u : ℝ} (hu : u ∈ Icc σ0 σ1) :
    |φ u - φ σ1| ≤ Real.pi * (((Z.filter (fun x => u ≤ x)).card : ℝ) + 1) := by
  have hπ := Real.pi_pos
  obtain ⟨hu0, hu1⟩ := hu
  have hcont : ContinuousOn φ (Icc u σ1) := hφ.mono (Icc_subset_Icc hu0 le_rfl)
  have hZ' : ∀ x ∈ Ioo u σ1, Real.cos (φ x) = 0 → x ∈ Z :=
    fun x hx h0 => hZ x ⟨lt_of_le_of_lt hu0 hx.1, hx.2⟩ h0
  have key : ∀ a b : ℝ, (∀ v, a < v → v < b → ∃ x ∈ Ioo u σ1, φ x = v) →
      b - a ≤ Real.pi * (((Z.filter (fun x => u ≤ x)).card : ℝ) + 1) := by
    intro a b hIVT
    have := lattice_count_le hIVT hZ'
    have h2 : (b - a) / Real.pi ≤ ((Z.filter (fun x => u ≤ x)).card : ℝ) + 1 := by linarith
    rw [div_le_iff₀ hπ] at h2
    linarith
  rcases le_total (φ u) (φ σ1) with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact key (φ u) (φ σ1) (fun v hv1 hv2 => by
      obtain ⟨x, hx, hxv⟩ := intermediate_value_Ioo hu1 hcont ⟨hv1, hv2⟩
      exact ⟨x, hx, hxv⟩)
  · rw [abs_of_nonneg (by linarith)]
    exact key (φ σ1) (φ u) (fun v hv1 hv2 => by
      obtain ⟨x, hx, hxv⟩ := intermediate_value_Ioo' hu1 hcont ⟨hv1, hv2⟩
      exact ⟨x, hx, hxv⟩)

/-- **Integrating the step function**: `∫_{σ0}^{σ1} #{x ∈ Z : u ≤ x} du = ∑_{x ∈ Z} (x - σ0)`
for `Z ⊆ [σ0, σ1]`.

### Summary of Proof
`#{x ∈ Z : u ≤ x} = ∑_{x ∈ Z} 1_{u ≤ x}` (`Finset.card_filter`), and each indicator integrates
to `x - σ0` (`intervalIntegral.integral_indicator`).

### References
tex: "the sum on the right is precisely the integral of this step function", proof of
`\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** none.
**Used by:** `integralofarg`. -/
theorem integral_card_filter {σ0 σ1 : ℝ} {Z : Finset ℝ} (hZ : ∀ x ∈ Z, x ∈ Icc σ0 σ1) :
    ∫ u in σ0..σ1, ((Z.filter (fun x => u ≤ x)).card : ℝ) = ∑ x ∈ Z, (x - σ0) := by
  have heq : ∀ u : ℝ, ((Z.filter (fun x => u ≤ x)).card : ℝ)
      = ∑ x ∈ Z, indicator {u : ℝ | u ≤ x} (fun _ => (1 : ℝ)) u := by
    intro u
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    simp [Set.indicator_apply]
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [intervalIntegral.integral_indicator (hZ x hx)]
    simp
  · intro x _
    apply AntitoneOn.intervalIntegrable
    intro u _ v _ huv
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (huv.trans h1) h2
    · exact zero_le_one
    · exact le_rfl

/-- **The step function `u ↦ #{x ∈ Z : u ≤ x}` is antitone.**

### Summary of Proof
Filtering by a weaker predicate gives a larger finset (`Finset.card_le_card`).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integralofarg`. -/
theorem card_filter_antitone (Z : Finset ℝ) :
    Antitone (fun u : ℝ => ((Z.filter (fun x => u ≤ x)).card : ℝ)) := by
  intro u v huv
  simp only
  exact_mod_cast Finset.card_le_card (fun x hx => by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, huv.trans hx.2⟩)

/-- **The ratio set defining `argSupConst` is bounded above** when `σ1 - c < c - σ0`.

### Summary of Proof
On `[σ0, c)` the ratio is `≤ c-σ0` (`argRatio_le_of_lt`); on `(c, σ1]` the numerator is at most
`σ1-σ0` and the denominator at least `log(c-σ0) - log(σ1-c) > 0`.

### Lean Notes
This is what licenses `le_csSup` for `argSupConst` under Lemma 28's hypothesis
`c > (σ0+σ1)/2` alone — Lemma 29's sharper `η`-condition is not needed for boundedness.

### References
tex: the definition of `C_{c,σ0,σ1}` in `\ref{lem:integralofarg}` (Lemma 28), which presumes
the supremum finite.

### Dependencies
**Depends on:** `argRatio_le_of_lt`.
**Used by:** `weight_le_argSupConst`, `argSupConst_nonneg`. -/
theorem argRatio_bddAbove {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hσ1c : σ1 - c < c - σ0) :
    BddAbove ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) ''
      (Icc σ0 σ1 \ {c})) := by
  refine ⟨max (c - σ0) ((σ1 - σ0) / (Real.log (c - σ0) - Real.log (σ1 - c))), ?_⟩
  rintro y ⟨σ, ⟨⟨hσ0, hσσ1⟩, hσc⟩, rfl⟩
  have hσc' : σ ≠ c := hσc
  dsimp only
  rcases lt_or_gt_of_ne hσc' with h | h
  · exact le_max_of_le_left (argRatio_le_of_lt hσ0c hσ0 h)
  · apply le_max_of_le_right
    have hpos : 0 < σ - c := by linarith
    have hσ1c' : 0 < σ1 - c := by linarith
    rw [abs_of_pos hpos]
    have hD1 : 0 < Real.log (c - σ0) - Real.log (σ1 - c) := by
      have := Real.log_lt_log hσ1c' hσ1c
      linarith
    have hDσ : Real.log (c - σ0) - Real.log (σ1 - c) ≤ Real.log (c - σ0) - Real.log (σ - c) := by
      have := Real.log_le_log hpos (by linarith : σ - c ≤ σ1 - c)
      linarith
    exact div_le_div₀ (by linarith) (by linarith) hD1 hDσ

/-- **Each real zero's weight is at most `C_{c,σ0,σ1}` times its log weight**:
`x - σ0 ≤ C · (log(c-σ0) - log|x-c|)` for `x ∈ (σ0, σ1)`, `x ≠ c`.

### Summary of Proof
`le_csSup` (with `argRatio_bddAbove`) at `σ = x`, then clear the positive denominator.

### References
tex: "As we have defined `C_{c,σ0,σ1}` to be the maximum possible ratio between the weight for
a zero in the respective sums, this gives the result" — proof of `\ref{lem:integralofarg}`
(Lemma 28).

### Dependencies
**Depends on:** `argSupConst`, `argRatio_bddAbove`.
**Used by:** `integralofarg`. -/
theorem weight_le_argSupConst {σ0 σ1 c x : ℝ} (hσ0c : σ0 < c)
    (hσ1c : σ1 - c < c - σ0) (hx : x ∈ Ioo σ0 σ1) (hxc : x ≠ c) :
    x - σ0 ≤ argSupConst c σ0 σ1 * (Real.log (c - σ0) - Real.log |x - c|) := by
  have hbdd := argRatio_bddAbove hσ0c hσ1c
  have hD : 0 < Real.log (c - σ0) - Real.log |x - c| := by
    have h1 : 0 < |x - c| := abs_pos.mpr (sub_ne_zero.mpr hxc)
    have h2 : |x - c| < c - σ0 := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have := Real.log_lt_log h1 h2
    linarith
  have hmem : (x - σ0) / (Real.log (c - σ0) - Real.log |x - c|)
      ∈ (fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' (Icc σ0 σ1 \ {c}) :=
    ⟨x, ⟨⟨hx.1.le, hx.2.le⟩, hxc⟩, rfl⟩
  have hle := le_csSup hbdd hmem
  unfold argSupConst
  rw [div_le_iff₀ hD] at hle
  exact hle

/-- **`C_{c,σ0,σ1} ≥ 0`.**

### Summary of Proof
The ratio at `σ = σ0` is `0`, and `le_csSup`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `argSupConst`, `argRatio_bddAbove`.
**Used by:** `integralofarg`. -/
theorem argSupConst_nonneg {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hσ1 : σ0 < σ1)
    (hσ1c : σ1 - c < c - σ0) : 0 ≤ argSupConst c σ0 σ1 := by
  have hbdd := argRatio_bddAbove hσ0c hσ1c
  have hmem : (σ0 - σ0) / (Real.log (c - σ0) - Real.log |σ0 - c|)
      ∈ (fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' (Icc σ0 σ1 \ {c}) :=
    ⟨σ0, ⟨⟨le_rfl, hσ1.le⟩, hσ0c.ne⟩, rfl⟩
  have := le_csSup hbdd hmem
  unfold argSupConst
  simpa using this

set_option maxHeartbeats 300000 in
-- the assembly threads a `Finset`-indexed step function through `integral_congr`,
-- `integral_mono_on` and `integral_finsetSum`; elaboration exceeds the default budget
/-- **`Lemma \ref{lem:integralofarg}` (Lemma 28).** Fix `N > 0`, `σ0 < σ1`, and
`c > (σ0+σ1)/2`; let `f` be conjugate-symmetric and analytic on the closed disc
`|s - (c+iT)| ≤ c-σ0`, with `argf` a continuous argument of `f` along the segment `[σ0,σ1] + iT`
(`f = ‖f‖ e^{i·argf}` there), and `F_N(0) ≠ 0`. Then
`|∫_{σ1}^{σ0} Δ arg f(x+iT)|_{σ1}^u du| ≤ (π/N)((σ1-σ0) + C_{c,σ0,σ1} ∫_0^{c-σ0} n_{F_N}(u)/u du)`.

### Summary of Proof
Following the source. Let `S_L`, `S_R` be the zeros of `Re f^N` between `c` and `σ0`, `σ1`
respectively. Between consecutive zeros of `Re f(u+iT)^N` the value `f^N` stays in an open
half-plane, so `arg f` varies by less than `π/N` there; hence
`|Δ arg f|_{σ1}^u| ≤ (π/N)(k(u) + 1)` with `k(u)` the number of zeros of `Re f^N` between `u`
and `σ1`, and integrating, `|∫Δarg f| ≤ (π/N)((σ1-σ0) + ∑_{S_L∪S_R}(Re ρ - σ0))`. The
right-hand integral is the Nevanlinna counting identity
`∫_0^{c-σ0} n_{F_N}(u)/u du = ∑_{F_N(ρ)=0, |ρ|<c-σ0} log((c-σ0)/|ρ|)`, which dominates
`∑_{S_L} log((c-σ0)/(c-Re ρ)) + ∑_{S_R} log((c-σ0)/(Re ρ-c))` (the real zeros of `F_N` are
among all its zeros, and `Re f(u+iT)^N = F_N(u-c)` by conjugate symmetry). Since `C_{c,σ0,σ1}`
is the supremum of the ratio between the two sums' termwise weights, the result follows.

### Lean Notes
**Four steps.** (i) `Ffun_analyticOnNhd`: `F_N` is analytic
on the disc `|w| ≤ c-σ0` — the lower disc `|s-(c-iT)| ≤ c-σ0` comes for free from `hf` by
conjugate reflection (`analyticAt_conj_of_conj_symm`, via Mathlib's
`DifferentiableAt.conj_conj`) — and `Ffun_ofReal_sub`/`re_pow_of_polar` give
`F_N(x-c) = Re f(x+iT)^N = ‖f‖^N cos(N·argf)` on the real axis. (ii) `argStep_bound`: for
`u ∈ [σ0,σ1]`, `|φ(u) - φ(σ1)| ≤ π(k(u)+1)` with `φ = N·argf` and `k(u)` the number of real
zeros of `F_N` in `[u, σ1)`; proved by the intermediate value theorem (`lattice_count_le`):
every half-integer multiple of `π` strictly between `φ(u)` and `φ(σ1)` is attained at a zero of
`cos φ`, i.e. a real zero of `F_N`, and there are at least `|φ(u)-φ(σ1)|/π - 1` of them
(`Int.card_Ioo`). (iii) `integral_card_filter` integrates `k` to `∑_ρ (Re ρ - σ0)`, and
`weight_le_argSupConst` bounds each weight by `C·(log(c-σ0) - log|Re ρ - c|)` (`le_csSup`, the
ratio set being bounded by `argRatio_bddAbove`). (iv) `sum_log_le_integral_ballZeroCount`:
`∑_ρ log((c-σ0)/|ρ|) ≤ ∫₀^{c-σ0} n_{F_N}(u)/u du`, with `n_{F_N}` written as a finite sum over
the divisor's support (`ballZeroCount_eq_sum`), vanishing on `[0, r₀]` (`exists_pos_radius_ne_zero`)
and monotone after, so that `n/u` is integrable and the indicator integrals evaluate to logs
(`integral_indicator_inv`). Two of the tex's hypotheses turned out to be unnecessary and are not
taken: `T > 0` plays no role, and nonvanishing of `f` on the segment is not needed because
`hargf` is vacuous at a zero of `f` (both sides are `0`) — what matters is only that `argf` is
continuous and is *an* argument of `f` wherever `f ≠ 0`.

**Why the additive term is `(σ1-σ0)`, outside the integral.** Two constraints fix it.

1. It cannot sit *inside* the `1/u` integrand: `∫_0^{c-σ0} (1/2)/(Nu) du` diverges, so such a
   bound would be `+∞` (vacuous), and in Lean, where `intervalIntegral` of a non-integrable
   function is `0`, it would collapse to the false `|∫Δarg f| ≤ C · 0`.
2. Outside the integral the constant can be neither `1/2` nor absent: the left side and
   `∑(Re ρ - σ0)` scale like a *length*, so it must be `(σ1-σ0)`, which is what the
   step-function bound `(π/N)(k(u)+1)` integrates to. A *pointwise* `(π/N)(k(u) + 1/2)` also
   fails, at `k(u) = 0`: with no sign change of `Re f^N` the value `f^N` merely stays in one open
   half-plane, and its argument can move by anything below `π`. Witness: `f(s) = e^{s²}`
   (conjugate-symmetric), `T = 0.01`, `N = 1`, `σ0 = 100`, `σ1 = 200`, `c = 160`. Then
   `F_1(w) = e^{(w+c)²-T²} cos(2T(w+c))` has only real zeros
   `w = (2m+1)π/(4T) - c ∈ {-81.5, 75.6, …}`, none in `|w| ≤ 60`, so `n_{F_1} ≡ 0` and `Re f` has
   no sign change on the segment; yet `|Δ arg f| = 2T|u - σ1|` reaches `2 > π/2` at `u = σ0`, and
   the left side is `|∫_{200}^{100} 2T(u-200) du| = T(σ1-σ0)² = 100`, against `0` (no constant),
   `π/2` (a `1/2`), and `100π` (the constant used here).
   `Code/indep_mpmath_lemma27_counterexample.py` prints all these numbers.

**Hypotheses.** The tex states none, using them tacitly: `hf` (conjugate symmetry, so that
`Re f(u+iT)^N = F_N(u-c)`), `hfan` (analyticity on the disc `|s-(c+iT)| ≤ c-σ0`, which contains
the segment since `σ1 ≤ 2c-σ0`, and gives `F_N` its zeros as a finite set with `n_{F_N}` a step
function), `hargf`/`hargf_cont` (`argf` is a continuous argument of `f` along the segment), and
`hFN` (`F_N(0) ≠ 0`, so `n_{F_N}(u) = 0` near `u = 0` and `∫_0 n(u)/u du` converges; without it
the integral is undefined and Lean's `intervalIntegral` would silently return the junk value `0`,
the same trap `deltaArg_bound_finite_N`'s `hFN` guards against). The tex's `<` is stated here as
`≤`; the step-function bound is not strict in general.

**`hargf`/`hargf_cont` are NOT a discrepancy with the tex.** The tex defines `arg f` (after
Equation `\ref{eq:zerodensityintegral}`, Equation 13) by continuous variation to the right of the
zeros and then along the horizontal line, "provided that horizontal line does not contain a zero
of `f`"; on such a line the two hypotheses hold by definition. On a line through a zero the tex's
proofs use the halving convention `lim_{ε→0} ½(arg f(T+ε) + arg f(T-ε))` instead — this lemma's
own first sentence "reduce to the case of having no zeros on the horizontal line … using uniform
continuity" — so the Lean statement is the case the tex proves, and the convention-based
extension is the unformalized part.

**Orientation and absolute value match the tex exactly.** The statement is the
`|∫_{σ1}^{σ0} …|` form: outer integral decreasing (since `σ0 < σ1`), wrapped in absolute value.
The absolute value is what the proof delivers — the integral is bounded by a sum of non-negative
zero weights — and it is what licenses the call site's opposite orientation, since either
orientation follows from it immediately.

**Zero/no-zero case split.** The tex's discussion after Equation `\ref{eq:zerodensityintegral}`
(Equation 13) fixes the convention for `arg f`/`N(σ,T1,T2)` on a horizontal line through a zero of
`f` — a symmetric limit average, `(arg f(T+ε) + arg f(T-ε))/2` as `ε→0`, and likewise for `N`,
chosen so the identity still holds. A fully rigorous proof of this lemma inherits that case split
at the level of `Re F_N`: away from a zero of `F_N` on the path the step-function argument applies
as sketched; at such a zero, the relevant step reduces to uniform continuity or to the built-in
compatibility between the `arg`/`N` conventions. In Lean the no-zero case is the hypothesis
(`hargf`, `hargf_cont`: `argf` is a continuous argument of `f` along the segment), so the
convention never enters the proof. This lemma is the first step of `deltaArg_bound_finite_N`,
hence of `arg_integrals`.

### References
tex: `\ref{lem:integralofarg}` (Lemma 28), tex lines 962–985. The `arg`/`N`
convention is fixed after Equation `\ref{eq:zerodensityintegral}` (Equation 13).

**Independent numeric check.**
`Code/indep_mpmath_lemma27_counterexample.py`: the example above, with left side `100`
against the three candidate right-hand sides `0`, `1.5708`, `314.16`; also `sup|Δ arg f| = 2 < π`
on the segment (the `k(u) = 0` case of the step-function bound). The grid supremum
`C_{c,σ0,σ1} = 246.6` there exceeds `c-σ0 = 60`, as it may: this example has `σ1-c = 40`, outside
the range `σ1 - c ≤ η(c-σ0) = 16.7` in which Lemma 29 bounds `C` by `c-σ0`; Lemma 28 itself does
not need that range.

### Dependencies
**Depends on:** `deltaArgGen`, `argSupConst`, `Ffun`, `ballZeroCount`, `Ffun_analyticOnNhd`,
`Ffun_ofReal_sub`, `re_pow_of_polar`, `mem_divisor_support_iff`, `argStep_bound`,
`integral_card_filter`, `card_filter_antitone`, `weight_le_argSupConst`, `argSupConst_nonneg`,
`sum_log_le_integral_ballZeroCount`.
**Used by:** `deltaArg_bound_finite_N`. -/
theorem integralofarg (f : ℂ → ℂ) (argf : ℂ → ℝ)
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))
    {T : ℝ} {N : ℕ} (hN : 0 < N)
    {σ0 σ1 c : ℝ} (hσ : σ0 < σ1) (hc : (σ0 + σ1) / 2 < c)
    (hfan : AnalyticOnNhd ℂ f (Metric.closedBall (c + T * Complex.I) (c - σ0)))
    (hargf : ∀ x ∈ Set.Icc σ0 σ1,
      f (x + T * Complex.I)
        = ‖f (x + T * Complex.I)‖ * Complex.exp (argf (x + T * Complex.I) * Complex.I))
    (hargf_cont : ContinuousOn (fun x : ℝ => argf (x + T * Complex.I)) (Set.Icc σ0 σ1))
    (hFN : Ffun f c T N 0 ≠ 0) :
    |∫ u in σ1..σ0, deltaArgGen argf T σ1 u|
      ≤ Real.pi / N * ((σ1 - σ0) + argSupConst c σ0 σ1 *
          ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u) := by
  have hR : 0 < c - σ0 := by linarith
  have hσ1c : σ1 - c < c - σ0 := by linarith
  have hσ0c : σ0 < c := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hF : AnalyticOnNhd ℂ (Ffun f c T N) (Metric.closedBall (0 : ℂ) (c - σ0)) :=
    Ffun_analyticOnNhd hf hfan N
  have hmemS := mem_divisor_support_iff hR hF hFN
  -- the real zeros of `Re f^N` in `(σ0, σ1)`, as points of the `w`-plane and as reals
  set W : Finset ℂ := (((MeromorphicOn.divisor (Ffun f c T N)
      (Metric.closedBall (0 : ℂ) (c - σ0))).finiteSupport
        (isCompact_closedBall 0 (c - σ0))).toFinset).filter
      (fun w : ℂ => w.im = 0 ∧ σ0 - c < w.re ∧ w.re < σ1 - c) with hW
  set Z : Finset ℝ := W.image (fun w => w.re + c) with hZ
  have hWmem : ∀ w ∈ W, (w ∈ Metric.closedBall (0 : ℂ) (c - σ0) ∧ Ffun f c T N w = 0)
      ∧ (w.im = 0 ∧ σ0 - c < w.re ∧ w.re < σ1 - c) := by
    intro w hw
    rw [hW, Finset.mem_filter, hmemS] at hw
    exact hw
  have hZmem : ∀ x ∈ Z, x ∈ Set.Ioo σ0 σ1 ∧ x ≠ c := by
    intro x hx
    rw [hZ, Finset.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨⟨_, hw0⟩, hwim, hw1, hw2⟩ := hWmem w hw
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro hwc
    have hwre : w.re = 0 := by linarith
    have : w = 0 := Complex.ext hwre hwim
    rw [this] at hw0
    exact hFN hw0
  -- zeros of `cos (N θ)` in `(σ0,σ1)` are in `Z`
  have hcos : ∀ x ∈ Set.Ioo σ0 σ1,
      Real.cos ((N : ℝ) * argf (x + T * Complex.I)) = 0 → x ∈ Z := by
    intro x hx h0
    have hxI : x ∈ Set.Icc σ0 σ1 := ⟨hx.1.le, hx.2.le⟩
    have hFx : Ffun f c T N ((x - c : ℝ) : ℂ) = 0 := by
      rw [Ffun_ofReal_sub hf, re_pow_of_polar (hargf x hxI) N, h0, mul_zero,
        Complex.ofReal_zero]
    have hw : ((x - c : ℝ) : ℂ) ∈ W := by
      rw [hW, Finset.mem_filter, hmemS]
      refine ⟨⟨?_, hFx⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      · simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
        constructor <;> linarith [hx.1, hx.2]
    rw [hZ, Finset.mem_image]
    exact ⟨_, hw, by simp⟩
  -- pointwise step-function bound
  have hstep : ∀ u ∈ Set.Icc σ0 σ1,
      |argf (u + T * Complex.I) - argf (σ1 + T * Complex.I)|
        ≤ Real.pi / N * (((Z.filter (fun x => u ≤ x)).card : ℝ) + 1) := by
    intro u hu
    have hφ : ContinuousOn (fun x : ℝ => (N : ℝ) * argf (x + T * Complex.I)) (Set.Icc σ0 σ1) :=
      continuousOn_const.mul hargf_cont
    have h := argStep_bound hφ hcos hu
    have e : |(N : ℝ) * argf (u + T * Complex.I) - N * argf (σ1 + T * Complex.I)|
        = N * |argf (u + T * Complex.I) - argf (σ1 + T * Complex.I)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hNpos]
    rw [e] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [h]
  -- the left-hand side
  have hLHS : |∫ u in σ1..σ0, deltaArgGen argf T σ1 u|
      = |∫ u in σ0..σ1, (argf (u + T * Complex.I) - argf (σ1 + T * Complex.I))| := by
    rw [intervalIntegral.integral_symm σ0 σ1, abs_neg]
    rfl
  rw [hLHS]
  have hint1 : IntervalIntegrable
      (fun u => argf (u + T * Complex.I) - argf (σ1 + T * Complex.I))
      MeasureTheory.volume σ0 σ1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ.le]
    exact hargf_cont.sub continuousOn_const
  have hintcard : IntervalIntegrable
      (fun u : ℝ => ((Z.filter (fun x => u ≤ x)).card : ℝ)) MeasureTheory.volume σ0 σ1 :=
    (card_filter_antitone Z).antitoneOn _ |>.intervalIntegrable
  have hint2 : IntervalIntegrable
      (fun u : ℝ => Real.pi / N * (((Z.filter (fun x => u ≤ x)).card : ℝ) + 1))
      MeasureTheory.volume σ0 σ1 :=
    (hintcard.add intervalIntegrable_const).const_mul _
  have hZIcc : ∀ x ∈ Z, x ∈ Set.Icc σ0 σ1 := fun x hx =>
    ⟨(hZmem x hx).1.1.le, (hZmem x hx).1.2.le⟩
  -- the sum over `Z` versus the sum over `W`
  have hinj : Set.InjOn (fun w : ℂ => w.re + c) (↑W : Set ℂ) := by
    intro w hw w' hw' heq
    have hwim := (hWmem w hw).2.1
    have hw'im := (hWmem w' hw').2.1
    apply Complex.ext
    · simpa using heq
    · rw [hwim, hw'im]
  have hsumZW : ∑ x ∈ Z, (Real.log (c - σ0) - Real.log |x - c|)
      = ∑ w ∈ W, (Real.log (c - σ0) - Real.log ‖w‖) := by
    rw [hZ, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    have hwim := (hWmem w hw).2.1
    have hnorm : ‖w‖ = |w.re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hwim]
      simp [Real.sqrt_sq_eq_abs]
    rw [hnorm, add_sub_cancel_right]
  have hC0 := argSupConst_nonneg hσ0c hσ hσ1c
  have hsumC : ∑ x ∈ Z, (x - σ0)
      ≤ argSupConst c σ0 σ1 * ∑ x ∈ Z, (Real.log (c - σ0) - Real.log |x - c|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    exact weight_le_argSupConst hσ0c hσ1c (hZmem x hx).1 (hZmem x hx).2
  have hNev := sum_log_le_integral_ballZeroCount hR hF hFN (W := W) (fun w hw => (hWmem w hw).1)
  calc |∫ u in σ0..σ1, (argf (u + T * Complex.I) - argf (σ1 + T * Complex.I))|
      ≤ ∫ u in σ0..σ1, |argf (u + T * Complex.I) - argf (σ1 + T * Complex.I)| :=
        intervalIntegral.abs_integral_le_integral_abs hσ.le
    _ ≤ ∫ u in σ0..σ1, Real.pi / N * (((Z.filter (fun x => u ≤ x)).card : ℝ) + 1) :=
        intervalIntegral.integral_mono_on hσ.le hint1.abs hint2 hstep
    _ = Real.pi / N * ((σ1 - σ0) + ∑ x ∈ Z, (x - σ0)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hintcard intervalIntegrable_const,
          integral_card_filter hZIcc, intervalIntegral.integral_const]
        simp only [smul_eq_mul, mul_one]
        ring
    _ ≤ Real.pi / N * ((σ1 - σ0) + argSupConst c σ0 σ1 *
          ∑ x ∈ Z, (Real.log (c - σ0) - Real.log |x - c|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hsumC]
    _ ≤ Real.pi / N * ((σ1 - σ0) + argSupConst c σ0 σ1 *
          ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hsumZW]
        linarith [mul_le_mul_of_nonneg_left hNev hC0]

end IntegralOfArgIngredients

/-- **Pointwise form of `Lemma \ref{lem:supremumforarg}` (Lemma 29)'s third claim, on the right
half of its domain:** for `c < σ` with `σ-c ≤ η(c-σ0)`, the ratio
`(σ-σ0)/(log(c-σ0)-log|σ-c|)` never exceeds `c-σ0`.

### Summary of Proof
Exactly the source's. Write `A = c-σ0 > 0` and `u = σ-c ∈ (0, ηA]`. Then
`log A - log u ≥ log A - log(ηA) = -log η = 1+η`, the last step by Equation `\ref{eq:eta}`
(Equation 15, `Definitions.eta_eq`: `1+η+log η = 0`). Meanwhile the numerator is
`σ-σ0 = A+u ≤ (1+η)A`. Dividing, `(A+u)/(log A - log u) ≤ (1+η)A/(1+η) = A`.

That is the source's displayed computation
`(σ1-σ0)/(log(c-σ0)-log(σ1-c)) ≤ (1+η)(c-σ0)/(-log η) = c-σ0`.

### Lean Notes
Stated **pointwise in `σ`** rather than only at the endpoint `σ1`, which is what lets
`supremumforarg_full` avoid needing `supremumforarg_right`'s monotonicity argument.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), third claim, tex lines 990 and 1008–1018; Equation
`\ref{eq:eta}` (Equation 15).

### Dependencies
**Depends on:** `eta`, `eta_eq`, `eta_mem_Ioo`.
**Used by:** `argSupConst_le_of_le`, `supremumforarg_full`. -/
private theorem argRatio_le_of_gt {σ0 c σ : ℝ} (hσ0c : σ0 < c) (hcσ : c < σ)
    (hη : σ - c ≤ eta * (c - σ0)) :
    (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|) ≤ c - σ0 := by
  have hetamem := eta_mem_Ioo
  have hc0 : (0:ℝ) < c - σ0 := sub_pos.mpr hσ0c
  have hu : (0:ℝ) < σ - c := sub_pos.mpr hcσ
  rw [abs_of_pos hu]
  have hlogu : Real.log (σ - c) ≤ Real.log eta + Real.log (c - σ0) := by
    have h := Real.log_le_log hu hη
    rwa [Real.log_mul hetamem.1.ne' hc0.ne'] at h
  have hd_ge : 1 + eta ≤ Real.log (c - σ0) - Real.log (σ - c) := by
    have h := eta_eq
    linarith
  have hd : 0 < Real.log (c - σ0) - Real.log (σ - c) := by linarith [hetamem.1]
  rw [div_le_iff₀ hd]
  have hnum : σ - σ0 ≤ (c - σ0) * (1 + eta) := by nlinarith [hη]
  have hmul := mul_le_mul_of_nonneg_left hd_ge hc0.le
  linarith

/-- **`Lemma \ref{lem:supremumforarg}` (Lemma 29), first claim.** The supremum over
`σ ∈ [σ0,c)` of `(σ-σ0)/(log(c-σ0)-log|σ-c|)` is at most `c - σ0`.

### Summary of Proof
The tex looks for extreme values by differentiating the ratio in `σ`. To the left of `c` there is
at most one critical point `σ̂`, characterised by
`(log(c-σ0) - log(c-σ̂))(c-σ̂) = σ̂-σ0`; substituting that back into the ratio shows the critical
value is `c-σ̂ ≤ c-σ0`. Since that is also the limiting value at the left endpoint, and the ratio
tends to `0` as `σ→c`, the supremum is `c-σ0`.

### Lean Notes
No differentiation is needed. Substituting `t = (c-σ)/(c-σ0)` turns the pointwise claim into the
tangent-line inequality `log t ≤ t-1`, which is `Real.log_le_sub_one_of_pos`; that is the closed
form of the source's critical-point computation, and it is isolated as `argRatio_le_of_lt`.

The bound is `≤`, not `<`, and that is **sharp**: the supremum equals `c-σ0` exactly, approached
as `σ→σ0⁺` but never attained, since `log t < t-1` strictly for `t ≠ 1`. Verified at 30 dp in
`Code/verify_supremumforarg.py` — at `σ = σ0+10⁻¹⁴` with `c-σ0 = 1` the ratio is
`0.999999999999995`. A strict `<` would be false. The tex also writes `\leq`.

The domain is the punctured `Set.Ico σ0 c` rather than the source's closed `[σ0,c]`: Lean's
`Real.log` is total with `log 0 = 0`, so including `σ = c` would add a spurious finite candidate
to the `sSup` that has nothing to do with the mathematics.

`σ1` plays no role here — as in the tex, whose first claim mentions only `σ0` and `c` — so the
hypothesis is kept only for signature consistency with `_right`/`_full`, and marked unused.

The numerator is `σ-σ0`, as in the tex. With `σ-σ1` the claim would be vacuous: `σ-σ1 < 0`
throughout `[σ0,c)` forces the supremum `≤ 0`, which bounds nothing about `argSupConst`.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), first claim. The constant it bounds is
`C_{c,σ0,σ1}` of `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `argRatio_le_of_lt`.
**Used by:** none — `deltaArg_bound_finite_N` reaches the same bound through the `c ≤ σ1` variant
`argSupConst_le_of_le`. This lemma records Lemma 29's first claim on its own. -/
theorem supremumforarg_left {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (_hcσ1 : c < σ1) :
    sSup ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' Set.Ico σ0 c)
      ≤ c - σ0 := by
  have hne : ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) ''
      Set.Ico σ0 c).Nonempty :=
    ⟨_, ⟨σ0, ⟨le_refl σ0, hσ0c⟩, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨σ, ⟨hσ0, hσc⟩, rfl⟩
  exact argRatio_le_of_lt hσ0c hσ0 hσc

/-- **`Lemma \ref{lem:supremumforarg}` (Lemma 29), second claim.** The supremum over
`σ ∈ (c,σ1]` of `(σ-σ0)/(log(c-σ0)-log|σ-c|)` is attained at the endpoint `σ1`.

### Summary of Proof
The source says only "On the right of `c` we see that the function is increasing". Formalized:
writing `g(σ) = log(c-σ0)-log(σ-c)` (no absolute value needed, since `σ>c` throughout), the
hypothesis `(σ0+σ1)/2 < c` gives `g(σ) > 0` directly for every `σ ∈ (c,σ1]` — because
`σ-c ≤ σ1-c < c-σ0`, so `log(σ-c) < log(c-σ0)` — with no separate monotonicity argument for `g`
needed first. The quotient rule then gives `deriv f σ = (g(σ) + (σ-σ0)/(σ-c)) / g(σ)²`, whose
numerator is a sum of two positive terms (`g(σ)>0` just shown, and `(σ-σ0)/(σ-c)>0` since both
factors are positive). So `f` is `StrictMonoOn (Ioc c σ1)` via `strictMonoOn_of_deriv_pos`, hence
bounded above by its value at the right endpoint `σ1`.

### Lean Notes
Stated with `σ0 < c < σ1` and, additionally, `(σ0+σ1)/2 < c` (equivalently `σ1-c < c-σ0`) so the
denominator stays positive across the whole of `(c,σ1]` — matching `integralofarg`'s own
hypothesis of the same shape. That extra hypothesis is automatic in `supremumforarg_full` from its
`η`-hypothesis (since `η<1`), but does not follow from anything in this lemma alone.

The domain is punctured at `σ = c` (`Set.Ioc` in place of `Set.Icc c σ1`), for the same
`Real.log 0 = 0` reason as `_left`.

All three claims of Lemma 29 use the tex's numerator `σ-σ0`.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), second claim, tex line 985.

### Dependencies
**Depends on:** none.
**Used by:** none — `supremumforarg_full` gets the right-hand piece pointwise from
`argRatio_le_of_gt`, so the monotonicity argument recorded here is not needed downstream. -/
theorem supremumforarg_right {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hcσ1 : c < σ1)
    (hmid : (σ0 + σ1) / 2 < c) :
    sSup ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' Set.Ioc c σ1)
      ≤ (σ1 - σ0) / (Real.log (c - σ0) - Real.log |σ1 - c|) := by
  set f : ℝ → ℝ := fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log (σ - c)) with hf_def
  have habs_eq : ∀ σ ∈ Set.Ioc c σ1,
      (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|) = f σ := by
    intro σ hσ
    rw [abs_of_pos (by linarith [hσ.1] : (0:ℝ) < σ - c)]
  have hgpos : ∀ σ ∈ Set.Ioc c σ1, 0 < Real.log (c - σ0) - Real.log (σ - c) := by
    rintro σ ⟨hcσ, hσσ1⟩
    have h1 : σ - c < c - σ0 := by linarith
    have h2 : (0:ℝ) < σ - c := by linarith
    have h3 : (0:ℝ) < c - σ0 := sub_pos.mpr hσ0c
    linarith [Real.log_lt_log h2 h1]
  have hderiv : ∀ σ ∈ Set.Ioo c σ1, HasDerivAt f
      ((Real.log (c - σ0) - Real.log (σ - c) + (σ - σ0) / (σ - c)) /
        (Real.log (c - σ0) - Real.log (σ - c)) ^ 2) σ := by
    intro σ hσ
    have hσIoc : σ ∈ Set.Ioc c σ1 := ⟨hσ.1, hσ.2.le⟩
    have hσcpos : (0:ℝ) < σ - c := by linarith [hσ.1]
    have hnum : HasDerivAt (fun x : ℝ => x - σ0) 1 σ := (hasDerivAt_id σ).sub_const σ0
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x - c)) (1 / (σ - c)) σ :=
      ((hasDerivAt_id σ).sub_const c).log hσcpos.ne'
    have hden : HasDerivAt (fun x : ℝ => Real.log (c - σ0) - Real.log (x - c))
        (-(1 / (σ - c))) σ := hlog.const_sub (Real.log (c - σ0))
    have hdenne : Real.log (c - σ0) - Real.log (σ - c) ≠ 0 := (hgpos σ hσIoc).ne'
    have hquot := hnum.div hden hdenne
    have heq : (1 * (Real.log (c - σ0) - Real.log (σ - c))
        - (σ - σ0) * -(1 / (σ - c))) / (Real.log (c - σ0) - Real.log (σ - c)) ^ 2
        = (Real.log (c - σ0) - Real.log (σ - c) + (σ - σ0) / (σ - c)) /
          (Real.log (c - σ0) - Real.log (σ - c)) ^ 2 := by
      have : σ - c ≠ 0 := hσcpos.ne'
      field_simp
      ring
    rwa [heq] at hquot
  have hcontDen : ContinuousOn (fun x : ℝ => Real.log (c - σ0) - Real.log (x - c))
      (Set.Ioc c σ1) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    exact (sub_pos.mpr hx.1).ne'
  have hmono : StrictMonoOn f (Set.Ioc c σ1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc c σ1)
    · apply ContinuousOn.div (by fun_prop) hcontDen
      intro σ hσ
      exact (hgpos σ hσ).ne'
    · intro σ hσ
      rw [interior_Ioc] at hσ
      rw [hderiv σ hσ |>.deriv]
      have hσIoc : σ ∈ Set.Ioc c σ1 := ⟨hσ.1, hσ.2.le⟩
      have hg : 0 < Real.log (c - σ0) - Real.log (σ - c) := hgpos σ hσIoc
      have hquot : 0 < (σ - σ0) / (σ - c) := by
        apply div_pos <;> linarith [hσ.1]
      exact div_pos (add_pos hg hquot) (pow_pos hg 2)
  have hval : (σ1 - σ0) / (Real.log (c - σ0) - Real.log |σ1 - c|) = f σ1 :=
    habs_eq σ1 ⟨hcσ1, le_refl σ1⟩
  rw [hval]
  have hne : ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) ''
      Set.Ioc c σ1).Nonempty :=
    ⟨_, ⟨σ1, ⟨hcσ1, le_refl σ1⟩, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨σ, hσ, rfl⟩
  dsimp only
  rw [habs_eq σ hσ]
  rcases lt_or_eq_of_le hσ.2 with h | h
  · exact (hmono hσ ⟨hcσ1, le_refl σ1⟩ h).le
  · rw [h]

/-- **`Lemma \ref{lem:supremumforarg}` (Lemma 29), third ("moreover") claim**: if `σ0 < c < σ1`
and `σ1 - c ≤ η(c-σ0)`, the supremum over the full range `σ ∈ [σ0,σ1]\{c}` of
`(σ-σ0)/(log(c-σ0)-log|σ-c|)` is at most `c - σ0`.

### Summary of Proof
The source's argument for the "moreover" claim, under `σ1-c ≤ η(c-σ0)`:
`(σ1-σ0)/(log(c-σ0)-log(σ1-c)) ≤ (1+η)(c-σ0)/(-log η) = c-σ0`, using `1+η+log η = 0`.

Formalized by splitting at `c` and applying the two pointwise helpers: `argRatio_le_of_lt` on
`[σ0,c)` — the tangent-line inequality `log t ≤ t-1` — and `argRatio_le_of_gt` on `(c,σ1]` — the
`η` computation, using `σ-c ≤ σ1-c ≤ η(c-σ0)`. Because the second helper is pointwise in `σ`, no
monotonicity argument, and hence no appeal to `supremumforarg_right`, is required.

### Lean Notes
**The numerator is `σ-σ0`, matching the tex.** With `σ-σ1` the claim would be vacuous:
`σ-σ1 ≤ 0` throughout `[σ0,σ1]` while the denominator is `≥0`, so the supremum would be `≤ 0` and
the bound would say nothing. Three independent reasons it has to be `σ-σ0`: the quantity being
bounded (`argSupConst`) has that numerator; the tex's *own proof* computes the displayed
inequality above, which is the `σ-σ0` numerator evaluated at `σ=σ1`; and numerically the `σ-σ1`
version's supremum is `-5.0e-6` where the `σ-σ0` version's is `c-σ0` exactly.

**The bound is `≤`, not `<`, and that is sharp** — on the left piece the supremum `c-σ0` is
approached as `σ→σ0⁺`, and when the `η` hypothesis is tight (`σ1 = c+η(c-σ0)`) the right piece
*attains* `c-σ0` at `σ=σ1`, since `-log η = 1+η` exactly. Both verified at 30 dp in
`Code/verify_supremumforarg.py`.

Punctured domain as for `_left`/`_right`. `(σ0+σ1)/2 < c` is not needed as a separate hypothesis,
since it follows from `hη` with `η < 1` (`Definitions.eta_mem_Ioo`).

**This is exactly `argSupConst c σ0 σ1 ≤ c-σ0`**, which is what
`Lemma \ref{lem:integralofarg}` (Lemma 28) needs: `argSupConst` is defined over the same
punctured domain `Set.Icc σ0 σ1 \ {c}`, so the two match by definition. That agreement is the
point of puncturing the definition; see `argSupConst`'s docstring for why the punctured form is
the faithful reading of the tex.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), third claim, tex line 990, proof at tex lines
1008–1018; Equation `\ref{eq:eta}` (Equation 15). Serves `\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `argRatio_le_of_lt`, `argRatio_le_of_gt`, `eta`, `eta_mem_Ioo`.
**Used by:** `argSupConst_le`. -/
theorem supremumforarg_full {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hcσ1 : c < σ1)
    (hη : σ1 - c ≤ eta * (c - σ0)) :
    sSup ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) '' (Set.Icc σ0 σ1 \ {c}))
      ≤ c - σ0 := by
  have hne : ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) ''
      (Set.Icc σ0 σ1 \ {c})).Nonempty :=
    ⟨_, ⟨σ0, ⟨⟨le_refl σ0, (hσ0c.trans hcσ1).le⟩, hσ0c.ne⟩, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨σ, ⟨⟨hσ0, hσ1⟩, hσc⟩, rfl⟩
  rcases lt_or_gt_of_ne hσc with h | h
  · exact argRatio_le_of_lt hσ0c hσ0 h
  · exact argRatio_le_of_gt hσ0c h (by linarith)

/-- **`C_{c,σ_0,σ_1} ≤ c - σ_0`** — the bound `Lemma \ref{lem:integralofarg}` (Lemma 28) needs,
stated directly in terms of `argSupConst`.

### Summary of Proof
This is `Lemma \ref{lem:supremumforarg}` (Lemma 29) applied to its own purpose. The tex proves
the three supremum claims precisely so that the constant `C_{c,σ_0,σ_1}` appearing as a factor in
Lemma 28 can be replaced by `c-σ_0`.

### Lean Notes
Immediate from `supremumforarg_full`: `argSupConst` is *defined* as the supremum over the same
punctured domain `Set.Icc σ0 σ1 \ {c}`, so the two statements are syntactically identical and the
proof is the application itself. That agreement is the point of puncturing the definition — over
the tex's closed interval, Lean's total `Real.log` would assign `σ = c` a spurious value that can
exceed `c-σ_0`. See `argSupConst`'s docstring.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29) bounding the `C_{c,σ_0,σ_1}` of
`\ref{lem:integralofarg}` (Lemma 28).

### Dependencies
**Depends on:** `argSupConst`, `supremumforarg_full`.
**Used by:** none directly — `deltaArg_bound_finite_N` uses the `c ≤ σ1` variant
`argSupConst_le_of_le` to turn `integralofarg`'s `C_{c,σ0,σ1}` into its `(c-σ0)/2` prefactor. -/
theorem argSupConst_le {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hcσ1 : c < σ1)
    (hη : σ1 - c ≤ eta * (c - σ0)) :
    argSupConst c σ0 σ1 ≤ c - σ0 :=
  supremumforarg_full hσ0c hcσ1 hη

section DeltaArgBound

open MeasureTheory intervalIntegral Set

/-! ### From Lemma 28 to the finite-`N` Backlund bound

`deltaArg_bound_finite_N` below is derived from `integralofarg`: bound `C_{c,σ0,σ1} ≤ c-σ0` by
Lemma 29
(`argSupConst_le_of_le`), evaluate `∫₀ᴿ n_{F_N}(u)/u du` exactly through Jensen's formula
(`integral_ballZeroCount_div_eq`: it equals `circleAverage (log ‖F_N‖) 0 R - log ‖F_N(0)‖`), and
bound the circle average by `(N/π)∫₀^π Fcr` (`circleAverage_log_norm_Ffun_le`), using
`log ‖F_N‖ ≤ N·max(log|f(·+iT)|, log|f(·-iT)|)` off the (countable) zero set of `F_N` on the
circle, periodicity to shift the circle integral to `[-π, π]`, and evenness of `Fcr`. -/

/-- **`C_{c,σ0,σ1} ≤ c - σ0` under Lemma 29's hypothesis, allowing `c = σ1`.**

### Summary of Proof
`csSup_le` with the two pointwise bounds `argRatio_le_of_lt` (on `[σ0, c)`) and
`argRatio_le_of_gt` (on `(c, σ1]`, where `σ - c ≤ σ1 - c ≤ η(c-σ0)`).

### Lean Notes
`argSupConst_le` requires `c < σ1`; the finite-`N` bound is stated with `c ≤ σ1` (the tex's
`c ∈ [σ0,σ1]`), and at `c = σ1` the right half of the domain is empty, so the same proof goes
through.

### References
tex: `\ref{lem:supremumforarg}` (Lemma 29), applied inside `\ref{thm:arg-integrals}`
(Theorem 31).

### Dependencies
**Depends on:** `argSupConst`, `argRatio_le_of_lt`, `argRatio_le_of_gt`.
**Used by:** `deltaArg_bound_finite_N`. -/
theorem argSupConst_le_of_le {σ0 σ1 c : ℝ} (hσ0c : σ0 < c) (hcσ1 : c ≤ σ1)
    (hη : σ1 - c ≤ eta * (c - σ0)) : argSupConst c σ0 σ1 ≤ c - σ0 := by
  unfold argSupConst
  have hne : ((fun σ => (σ - σ0) / (Real.log (c - σ0) - Real.log |σ - c|)) ''
      (Set.Icc σ0 σ1 \ {c})).Nonempty :=
    ⟨_, ⟨σ0, ⟨⟨le_refl σ0, hσ0c.le.trans hcσ1⟩, hσ0c.ne⟩, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨σ, ⟨⟨hσ0, hσ1⟩, hσc⟩, rfl⟩
  rcases lt_or_gt_of_ne (hσc : σ ≠ c) with h | h
  · exact argRatio_le_of_lt hσ0c hσ0 h
  · exact argRatio_le_of_gt hσ0c h (by linarith)

/-- **`n_F(u) ≥ 0`** for `u ≤ R`.

### Summary of Proof
`ballZeroCount_eq_sum` with nonnegative multiplicities (`untop_order_nonneg`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `ballZeroCount_eq_sum`, `untop_order_nonneg`, `mem_divisor_support_iff`.
**Used by:** `deltaArg_bound_finite_N`. -/
theorem ballZeroCount_nonneg {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) {u : ℝ} (hu : u ≤ R) :
    (0 : ℝ) ≤ (ballZeroCount F u : ℝ) := by
  rw [ballZeroCount_eq_sum hR hF hF0 hu]
  push_cast
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact_mod_cast untop_order_nonneg (hF z ((mem_divisor_support_iff hR hF hF0 z).mp hz).1)
  · exact le_rfl

/-- **Nevanlinna's identity plus Jensen's formula**:
`∫₀ᴿ n_F(u)/u du = circleAverage (log ‖F‖) 0 R - log ‖F 0‖` for `F` analytic on the closed disc
with `F 0 ≠ 0`.

### Summary of Proof
`∫₀ᴿ n_F(u)/u du = ∑_ρ m_ρ (log R - log ‖ρ‖)` over the zeros in the disc (the computation of
`sum_log_le_integral_ballZeroCount` with the multiplicities kept, `integral_indicator_inv`), and
Mathlib's `AnalyticOnNhd.circleAverage_log_norm` says the right-hand side's Jensen sum is the same
weighted sum (`MeromorphicOn.divisor_apply` on the finite support).

### References
tex: the rewriting of `∫_0^{c-σ0} n_{F_N}(u)/u du` by Jensen's theorem in the proof of
`\ref{thm:arg-integrals}` (Theorem 31).

### Dependencies
**Depends on:** `ballZeroCount`, `ballZeroCount_eq_sum`, `mem_divisor_support_iff`,
`exists_pos_radius_ne_zero`, `integral_indicator_inv`, `indicator_inv_intervalIntegrable`.
**Used by:** `deltaArg_bound_finite_N`. -/
theorem integral_ballZeroCount_div_eq {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) :
    ∫ u in (0 : ℝ)..R, (ballZeroCount F u : ℝ) / u
      = Real.circleAverage (fun z => Real.log ‖F z‖) 0 R - Real.log ‖F 0‖ := by
  have hmemS := mem_divisor_support_iff hR hF hF0
  have hn : ∀ u, u ≤ R → (ballZeroCount F u : ℝ)
      = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset,
          (if ‖z‖ ≤ u then ((meromorphicOrderAt F z).untop₀ : ℝ) else 0) := by
    intro u hu
    rw [ballZeroCount_eq_sum hR hF hF0 hu]
    push_cast
    rfl
  obtain ⟨r₀, hr₀, hr₀R, hFr₀⟩ := exists_pos_radius_ne_zero hR hF hF0
  have hSr : ∀ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset, r₀ < ‖z‖ := by
    intro z hz
    obtain ⟨_, hz0⟩ := (hmemS z).mp hz
    by_contra h
    exact hFr₀ z (by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.mp h) hz0
  have hSR : ∀ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)).toFinset, ‖z‖ ≤ R := by
    intro z hz
    have := ((hmemS z).mp hz).1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have heval : ∫ u in (0 : ℝ)..R, (ballZeroCount F u : ℝ) / u
      = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset,
          ((meromorphicOrderAt F z).untop₀ : ℝ) * (Real.log R - Real.log ‖z‖) := by
    have e1 : ∀ u ∈ Icc (0 : ℝ) R, (ballZeroCount F u : ℝ) / u
        = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
            (isCompact_closedBall 0 R)).toFinset,
            ((meromorphicOrderAt F z).untop₀ : ℝ) * (if ‖z‖ ≤ u then u⁻¹ else 0) := by
      intro u hu
      rw [hn u hu.2, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp [div_eq_mul_inv]
    rw [intervalIntegral.integral_congr (fun u hu => e1 u (by rwa [uIcc_of_le hR.le] at hu))]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [intervalIntegral.integral_const_mul,
        integral_indicator_inv (hr₀.trans (hSr z hz)) (hSR z hz)]
    · intro z hz
      exact (indicator_inv_intervalIntegrable (hr₀.trans (hSr z hz)) (hSR z hz)).const_mul _
  have hJ := AnalyticOnNhd.circleAverage_log_norm (f := F) hR.ne'
    (by rwa [abs_of_pos hR]) hF0
  rw [abs_of_pos hR] at hJ
  have hfin : ∑ᶠ u, ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R) u : ℤ) : ℝ)
        * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)
      = ∑ z ∈ ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset,
          ((meromorphicOrderAt F z).untop₀ : ℝ) * (Real.log R - Real.log ‖z‖) := by
    rw [finsum_eq_finsetSum_of_support_subset]
    · apply Finset.sum_congr rfl
      intro z hz
      obtain ⟨hzb, hz0⟩ := (hmemS z).mp hz
      rw [MeromorphicOn.divisor_apply hF.meromorphicOn hzb]
      have hz_ne : z ≠ 0 := fun h => hF0 (h ▸ hz0)
      have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      rw [zero_sub, norm_neg, Real.log_mul hR.ne' (inv_ne_zero hnorm.ne'), Real.log_inv]
      ring
    · intro z hz
      rw [Function.mem_support] at hz
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      intro hne
      apply hz
      simp [hne]
  rw [heval, hJ, hfin]
  ring

/-- **`log ‖F_N(R e^{iθ})‖ ≤ N · Fcr θ`** wherever `F_N(R e^{iθ}) ≠ 0`, when `Fcr` dominates
`max(log|f(c+Re^{iθ}+iT)|, log|f(c+Re^{iθ}-iT)|)`.

### Summary of Proof
`‖F_N‖ = ‖(a^N + b^N)/2‖ ≤ max(‖a‖,‖b‖)^N`, and `log` is monotone on positives.

### Lean Notes
The nonvanishing hypothesis is what makes `log ‖F_N‖` honest: at a zero Lean's `log 0 = 0`
could exceed `N·Fcr θ` when both `|a|, |b| < 1`. Those `θ` form a countable set
(`ae_circleMap_ne_zero`), which is why the circle-average bound is proved almost everywhere.

### References
tex: the display bounding `(1/N) log|F_N(re^{iθ})|` by `F_{c,r}(θ)` in the proof of
`\ref{thm:arg-integrals}` (Theorem 31).

### Dependencies
**Depends on:** `Ffun`.
**Used by:** `circleAverage_log_norm_Ffun_le`. -/
theorem log_norm_Ffun_circleMap_le {f : ℂ → ℂ} {c T R : ℝ} {N : ℕ} {Fcr : ℝ → ℝ}
    (hFcr_bound : ∀ θ : ℝ,
      max (Real.log ‖f (c + R * Complex.exp (θ * Complex.I) + T * Complex.I)‖)
          (Real.log ‖f (c + R * Complex.exp (θ * Complex.I) - T * Complex.I)‖) ≤ Fcr θ)
    {θ : ℝ} (hne : Ffun f c T N (circleMap 0 R θ) ≠ 0) :
    Real.log ‖Ffun f c T N (circleMap 0 R θ)‖ ≤ N * Fcr θ := by
  have e1 : circleMap 0 R θ + c + T * Complex.I
      = c + R * Complex.exp (θ * Complex.I) + T * Complex.I := by
    unfold circleMap; ring
  have e2 : circleMap 0 R θ + c - T * Complex.I
      = c + R * Complex.exp (θ * Complex.I) - T * Complex.I := by
    unfold circleMap; ring
  have hFeq : Ffun f c T N (circleMap 0 R θ)
      = (1 / 2 : ℂ) * (f (c + R * Complex.exp (θ * Complex.I) + T * Complex.I) ^ N
          + f (c + R * Complex.exp (θ * Complex.I) - T * Complex.I) ^ N) := by
    change (1 / 2 : ℂ) * (f (circleMap 0 R θ + c + T * Complex.I) ^ N
        + f (circleMap 0 R θ + c - T * Complex.I) ^ N) = _
    rw [e1, e2]
  set a := f (c + R * Complex.exp (θ * Complex.I) + T * Complex.I) with ha
  set b := f (c + R * Complex.exp (θ * Complex.I) - T * Complex.I) with hb
  set M := max ‖a‖ ‖b‖ with hM
  have hMa : ‖a‖ ≤ M := le_max_left _ _
  have hMb : ‖b‖ ≤ M := le_max_right _ _
  have hnormle : ‖Ffun f c T N (circleMap 0 R θ)‖ ≤ M ^ N := by
    rw [hFeq]
    have h1 : ‖a ^ N + b ^ N‖ ≤ ‖a‖ ^ N + ‖b‖ ^ N := by
      calc ‖a ^ N + b ^ N‖ ≤ ‖a ^ N‖ + ‖b ^ N‖ := norm_add_le _ _
        _ = ‖a‖ ^ N + ‖b‖ ^ N := by rw [norm_pow, norm_pow]
    have h2 : ‖a‖ ^ N ≤ M ^ N := pow_le_pow_left₀ (norm_nonneg _) hMa N
    have h3 : ‖b‖ ^ N ≤ M ^ N := pow_le_pow_left₀ (norm_nonneg _) hMb N
    calc ‖(1 / 2 : ℂ) * (a ^ N + b ^ N)‖ = 1 / 2 * ‖a ^ N + b ^ N‖ := by
          rw [norm_mul]; norm_num
      _ ≤ 1 / 2 * (M ^ N + M ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith
      _ = M ^ N := by ring
  have hpos : 0 < ‖Ffun f c T N (circleMap 0 R θ)‖ := norm_pos_iff.mpr hne
  have hlogM : Real.log M ≤ max (Real.log ‖a‖) (Real.log ‖b‖) := by
    rcases max_choice ‖a‖ ‖b‖ with h | h
    · rw [hM, h]; exact le_max_left _ _
    · rw [hM, h]; exact le_max_right _ _
  calc Real.log ‖Ffun f c T N (circleMap 0 R θ)‖ ≤ Real.log (M ^ N) :=
        Real.log_le_log hpos hnormle
    _ = N * Real.log M := by rw [Real.log_pow]
    _ ≤ N * max (Real.log ‖a‖) (Real.log ‖b‖) :=
        mul_le_mul_of_nonneg_left hlogM (Nat.cast_nonneg N)
    _ ≤ N * Fcr θ := mul_le_mul_of_nonneg_left (hFcr_bound θ) (Nat.cast_nonneg N)

/-- **Almost every point of the circle `|w| = R` is not a zero of `F`**, for `F` analytic on the
closed disc with `F 0 ≠ 0`.

### Summary of Proof
The zeros of `F` in the disc form a finite set (`mem_divisor_support_iff`), and each is hit by
`circleMap 0 R` on a countable set of angles (`Complex.exp_eq_exp_iff_exists_int`); a countable
set is null (`Set.Countable.measure_zero`).

### References
No tex counterpart — a technicality of Lean's total `log`.

### Dependencies
**Depends on:** `mem_divisor_support_iff`.
**Used by:** `circleAverage_log_norm_Ffun_le`. -/
theorem ae_circleMap_ne_zero {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R)) (hF0 : F 0 ≠ 0) :
    ∀ᵐ θ : ℝ, F (circleMap 0 R θ) ≠ 0 := by
  have hmemS := mem_divisor_support_iff hR hF hF0
  have hsub : {θ : ℝ | F (circleMap 0 R θ) = 0}
      ⊆ ⋃ z ∈ (↑(((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
          (isCompact_closedBall 0 R)).toFinset) : Set ℂ), {θ : ℝ | circleMap 0 R θ = z} := by
    intro θ hθ
    have hθ' : F (circleMap 0 R θ) = 0 := hθ
    rw [Set.mem_iUnion₂]
    refine ⟨circleMap 0 R θ, ?_, rfl⟩
    rw [Finset.mem_coe, hmemS]
    refine ⟨?_, hθ'⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR]
  have hcount : ∀ z : ℂ, ({θ : ℝ | circleMap 0 R θ = z}).Countable := by
    intro z
    by_cases hne : ({θ : ℝ | circleMap 0 R θ = z}).Nonempty
    · obtain ⟨θ₀, hθ₀⟩ := hne
      have hθ₀' : circleMap 0 R θ₀ = z := hθ₀
      apply (Set.countable_range (fun n : ℤ => θ₀ + n * (2 * Real.pi))).mono
      intro θ hθ
      have hθ' : circleMap 0 R θ = z := hθ
      rw [← hθ₀'] at hθ'
      unfold circleMap at hθ'
      have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      have hexp : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
        simpa [hR'] using hθ'
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨n, hn⟩ := hexp
      refine ⟨n, ?_⟩
      have := congrArg Complex.im hn
      simp at this
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.countable_empty
  have hE : ({θ : ℝ | F (circleMap 0 R θ) = 0}).Countable :=
    (Set.Countable.biUnion (Finset.countable_toSet _) (fun z _ => hcount z)).mono hsub
  have hnull : volume {θ : ℝ | F (circleMap 0 R θ) = 0} = 0 := hE.measure_zero volume
  rw [ae_iff]
  simpa using hnull

/-- **The circle average of `log ‖F_N‖` is at most `(N/π) ∫₀^π Fcr`**, for an even integrable
majorant `Fcr` of `max(log|f(c+Re^{iθ}+iT)|, log|f(c+Re^{iθ}-iT)|)`.

### Summary of Proof
`circleAverage = (2π)⁻¹ ∫₀^{2π} log ‖F_N(Re^{iθ})‖ dθ`; shift to `∫_{-π}^{π}` by periodicity
(`Function.Periodic.intervalIntegral_add_eq`), bound the integrand by `N·Fcr` almost everywhere
(`log_norm_Ffun_circleMap_le`, `ae_circleMap_ne_zero`, `intervalIntegral.integral_mono_ae`), and
fold `∫_{-π}^{π} Fcr = 2∫₀^π Fcr` by evenness (`intervalIntegral.integral_comp_neg`).
Integrability of `log ‖F_N ∘ circleMap‖` is Mathlib's `MeromorphicOn.circleIntegrable_log_norm`.

### Lean Notes
`Fcr` is only assumed integrable on `[0, π]`; evenness gives `[-π, 0]`
(`IntervalIntegrable.iff_comp_neg`), and the circle integrand — not `Fcr` — is what is shifted,
so no periodicity of `Fcr` is needed.

### References
tex: the three displays after "by applying Lemmas 28, 29 and then Jensen's Theorem" in the proof
of `\ref{thm:arg-integrals}` (Theorem 31), together with the bound of `(1/N) log|F_N|` by
`F_{c,r}` that follows them.

### Dependencies
**Depends on:** `Ffun`, `log_norm_Ffun_circleMap_le`, `ae_circleMap_ne_zero`.
**Used by:** `deltaArg_bound_finite_N`. -/
theorem circleAverage_log_norm_Ffun_le {f : ℂ → ℂ} {c T R : ℝ} (hR : 0 < R) {N : ℕ}
    (hF : AnalyticOnNhd ℂ (Ffun f c T N) (Metric.closedBall (0 : ℂ) R))
    (hF0 : Ffun f c T N 0 ≠ 0)
    {Fcr : ℝ → ℝ} (hFcr_even : ∀ θ : ℝ, Fcr (-θ) = Fcr θ)
    (hFcr_bound : ∀ θ : ℝ,
      max (Real.log ‖f (c + R * Complex.exp (θ * Complex.I) + T * Complex.I)‖)
          (Real.log ‖f (c + R * Complex.exp (θ * Complex.I) - T * Complex.I)‖) ≤ Fcr θ)
    (hFcr_int : IntervalIntegrable Fcr volume 0 Real.pi) :
    Real.circleAverage (fun z => Real.log ‖Ffun f c T N z‖) 0 R
      ≤ (N / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ := by
  have hπ := Real.pi_pos
  have hgper : Function.Periodic (fun θ : ℝ => Real.log ‖Ffun f c T N (circleMap 0 R θ)‖)
      (2 * Real.pi) :=
    (periodic_circleMap 0 R).comp (fun z => Real.log ‖Ffun f c T N z‖)
  have hgint : IntervalIntegrable (fun θ : ℝ => Real.log ‖Ffun f c T N (circleMap 0 R θ)‖)
      volume 0 (2 * Real.pi) := by
    have hmer : MeromorphicOn (Ffun f c T N) (Metric.sphere (0 : ℂ) |R|) := by
      rw [abs_of_pos hR]
      exact (hF.mono Metric.sphere_subset_closedBall).meromorphicOn
    exact hmer.circleIntegrable_log_norm
  have hgint' : IntervalIntegrable (fun θ : ℝ => Real.log ‖Ffun f c T N (circleMap 0 R θ)‖)
      volume (-Real.pi) Real.pi :=
    hgper.intervalIntegrable (t := 0) (by positivity) (by simpa using hgint) _ _
  have hshift : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖Ffun f c T N (circleMap 0 R θ)‖
      = ∫ θ in (-Real.pi)..Real.pi, Real.log ‖Ffun f c T N (circleMap 0 R θ)‖ := by
    have := hgper.intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add] at this
    rw [this]
    congr 1
    ring
  have hFcr_neg : IntervalIntegrable Fcr volume (-Real.pi) 0 := by
    have h1 : IntervalIntegrable (fun x => Fcr (-x)) volume (-0) (-Real.pi) :=
      (IntervalIntegrable.iff_comp_neg (f := Fcr) (a := (0 : ℝ)) (b := Real.pi)
        (by finiteness)).mp hFcr_int
    have heven : (fun x => Fcr (-x)) = Fcr := funext hFcr_even
    rw [heven, neg_zero] at h1
    exact h1.symm
  have hFcr_int' : IntervalIntegrable Fcr volume (-Real.pi) Real.pi := hFcr_neg.trans hFcr_int
  have hFcr_sym : ∫ θ in (-Real.pi)..(0 : ℝ), Fcr θ = ∫ θ in (0 : ℝ)..Real.pi, Fcr θ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) Fcr
    simp only [hFcr_even, neg_zero] at this
    exact this.symm
  have hae : (fun θ : ℝ => Real.log ‖Ffun f c T N (circleMap 0 R θ)‖)
      ≤ᵐ[volume] (fun θ : ℝ => (N : ℝ) * Fcr θ) := by
    filter_upwards [ae_circleMap_ne_zero hR hF hF0] with θ hθ
    exact log_norm_Ffun_circleMap_le hFcr_bound hθ
  have hmono : ∫ θ in (-Real.pi)..Real.pi, Real.log ‖Ffun f c T N (circleMap 0 R θ)‖
      ≤ ∫ θ in (-Real.pi)..Real.pi, (N : ℝ) * Fcr θ :=
    intervalIntegral.integral_mono_ae (by linarith) hgint' (hFcr_int'.const_mul _) hae
  have hFint : ∫ θ in (-Real.pi)..Real.pi, (N : ℝ) * Fcr θ
      = N * (2 * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ) := by
    rw [intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add_adjacent_intervals hFcr_neg hFcr_int, hFcr_sym]
    ring
  unfold Real.circleAverage
  rw [smul_eq_mul, hshift]
  calc (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, Real.log ‖Ffun f c T N (circleMap 0 R θ)‖
      ≤ (2 * Real.pi)⁻¹ * (N * (2 * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ)) := by
        rw [← hFint]
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (N / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ := by
        field_simp

/-- **The core Backlund/Titchmarsh zero-counting bound, at finite `N`.** This is `arg_integrals`'s
own conclusion with `log‖f(c+iT)‖` replaced by `(1/N) log‖F_N(c)‖` (`F_N = Ffun f c T N`,
evaluated at `w = 0`, i.e. `s = c`) plus the additive `(σ1-σ0)/(2N)` — exactly what remains of
`arg_integrals` *before* Backlund's `N → ∞` limit (`ExternalFacts.backlund_trick`) is taken.

### Summary of Proof
`Lemma \ref{lem:integralofarg}` (Lemma 28, `integralofarg`) bounds `(1/2π)|∫Δarg f|` by
`(1/2N)((σ1-σ0) + C_{c,σ0,σ1} ∫₀^{c-σ0} n_{F_N}(u)/u du)`; `Lemma \ref{lem:supremumforarg}`
(Lemma 29, `argSupConst_le_of_le`) gives `C ≤ c-σ0`; Jensen's formula
(`integral_ballZeroCount_div_eq`) evaluates the counting integral as
`(1/2π)∮ log|F_N(re^{iθ})| dθ - log|F_N(0)|`; and `circleAverage_log_norm_Ffun_le` bounds the
circle average by `(N/π)∫₀^π Fcr`. The degenerate case `σ0 = c` (which forces `σ1 = c`) has both
sides equal to `0`.

### Lean Notes
**`argf` must be tied to `f`, and `Fcr` must be integrable.** Both hypotheses are load-bearing,
not bookkeeping. Without `hargf`/`hargf_cont` the bound would be asserted for an *arbitrary*
`argf : ℂ → ℝ`, and scaling `argf` refutes it: `f ≡ 1`, `argf s = 8π·Re s`, `σ0 = 0`,
`σ1 = c = 1`, `T = 0`, `Fcr ≡ 0` satisfy everything else and give left side `2`, right side `0`.
Without `hFcr_int`, a non-integrable `Fcr` makes Lean's `∫₀^π Fcr = 0`, which turns the
right-hand side negative whenever `|F_N(0)| > 1`. So this statement carries the hypotheses of
`integralofarg` — `hfan` (analyticity of `f` on the disc `|s-(c+iT)| ≤ c-σ0`), `hargf` and
`hargf_cont` (`argf` is a continuous argument of `f` along the segment) — together with
`hFcr_int`. `arg_integrals` inherits all four; at the call sites
(`LittlewoodShort.littlewoodshort`, `_tight`) they become the statement that `argZeta` is a
continuous argument of `ζ` along the two horizontal segments at heights `T ± h`.

**`hargf`/`hargf_cont` are NOT a discrepancy with the tex.** The tex fixes the meaning of
`arg f` after Equation `\ref{eq:zerodensityintegral}` (Equation 13): it is "defined by continuous
variation along a vertical line to the right of any zeros … followed by passing along a horizontal
line, provided that horizontal line does not contain a zero of `f`". On such a line `argf` is a
continuous argument of `f` *by that definition*, so the two hypotheses hold automatically and add
nothing. When the horizontal line does contain a zero, the tex does not use the definition but the
convention `lim_{ε→0} ½(arg f(T+ε) + arg f(T-ε))` (with the matching convention for `N`), which its
proofs invoke where needed ("reduce to the case of having no zeros on the horizontal line … using
uniform continuity"). The Lean statement is the no-zero case — the case the tex proves; the
convention-based extension is the part not formalized.

**Coefficient sign `(σ0 - σ1)`, not `(σ1 - σ0)`.** The outer integral runs `σ1..σ0` (decreasing,
matching the source's printed direction), so the base-point coefficient must be `(σ0 - σ1)` for the
bracketed quantity to vanish when `argf` is literally constant (a sanity check any "deviation from
the base value" functional must satisfy: `∫ σ in σ1..σ0, (K:ℝ) = (σ0 - σ1) * K` for constant `K`,
which cancels exactly against `-(σ0-σ1)*K` here). With this sign, `|inner| = |∫ u in σ1..σ0,
deltaArgGen argf T σ1 u|` — literally the quantity `integralofarg` bounds, in the tex's own
`|∫_{σ1}^{σ0} …|` orientation. At the real call site this is exactly what
`LittlewoodMethod.littlewood_argsetup`'s `deltaArgZeta` decomposition produces, needing no
further bridging algebra.

**`hc` is non-strict `≤`, not `<`.** `supremumforarg_full` above — the Lean analogue of
`lem:supremumforarg`'s third ("moreover") claim — is proved from exactly this non-strict
hypothesis (`hη : σ1 - c ≤ eta * (c - σ0)`), so there is no loss in weakening `hc` to `≤` here to
match. This matters at the real call site: `LittlewoodShort`'s natural choice
`σ0 = 1-r, σ1 = 1+ηr, c = 1` gives `σ1 - c = ηr = eta * (c - σ0)` *exactly*, which a strict `<`
would reject.

**`hFN : Ffun f c T N 0 ≠ 0` is not optional.** Without it the statement would be *stronger than
the mathematics it encodes*. The Jensen-formula step it abbreviates produces
`-(1/N)·log|F_N(0)|`, which is `+∞` when `F_N(0) = 0`; but Lean's `Real.log ‖0‖ = 0`, so the
right-hand side would silently collapse to a **finite, smaller** bound at exactly the `N` where
the real bound is vacuous — a total function quietly making a claim say more than intended.

The tex has the corresponding hypothesis (`\ref{thm:arg-integrals}`'s proof: "there exists an
infinite collection of `N` such that `F_N(0) ≠ 0`"), whose source is Hasanalizade–Shen–Wong (HSW)
**Lemma 3.3** — the same result the proof cites sixteen lines later for Backlund's trick, and
which concludes both halves.

**Discharged for free at the call site.** `ExternalFacts.backlund_trick` exports the
nonvanishing alongside its limit, because its own construction already establishes it: the chosen
`N_m` satisfy `cos (N_m θ) ≥ 1/2`, and `‖(1/2)(aᴺ + conj(a)ᴺ)‖ = ‖a‖ᴺ|cos (Nθ)| ≥ ‖a‖ᴺ/2 > 0`
using `‖a‖ > 0` from `hf0`. So no appeal to HSW is needed on the Lean side.

**`+ (σ1 - σ0)/(2N)` on the right-hand side.** Lemma 28's step-function
bound is `|Δ arg f|_{σ1}^u| ≤ (π/N)(k(u) + 1)` — the `+1` because between consecutive zeros of
`Re f^N` the value `f^N` only stays in an open half-plane, where its argument can still move by
anything below `π` — and the `+1` integrates over `u ∈ [σ0,σ1]` to `(π/N)(σ1 - σ0)`, i.e. to
`(σ1-σ0)/(2N)` after the `1/(2π)`. See `integralofarg` for why the term must sit outside the
`1/u` integral. It vanishes as `N → ∞`, so `arg_integrals` is unaffected — it absorbs the term
with one `Tendsto.div_atTop`.

**`hσ0c : σ0 ≤ c` and `hcσ1 : c ≤ σ1` are the tex's own `c ∈ [σ0, σ1]`**
(`\ref{thm:arg-integrals}`: "Assume `c ∈ [σ0,σ1]` satisfies …"), and they are load-bearing.
Without them one may take `σ1 < c < σ0`, which makes the prefactor `(c - σ0)/2` negative while
the bracket can be forced positive by choosing `Fcr` large, so the conclusion would read
`0 ≤ (negative)`: concretely `f ≡ 1`, `argf ≡ 0`, `σ0 = 1`, `σ1 = 0`, `c = 1/2`, `T = 0`,
`Fcr ≡ 1`, `N = 1` satisfies every other hypothesis (`hc` reads `-1/2 ≤ -η/2`, true since
`η < 1`; `F_1(0) = 1 ≠ 0`) and gives `0 ≤ -1/4`. With `σ0 ≤ c ≤ σ1` the degenerate case `c = σ0`
forces `σ1 = c` (from `hc`), where both sides are `0`, and the tex's geometric picture — a disk of
radius `c - σ0 ≥ 0` about `c + iT` covering the segment `[σ0, σ1]` — holds throughout. Every call
site (`c = 1`, `σ0 = 1 - r`, `σ1 = 1 + ηr` with `r > 0`) satisfies both trivially.

### References
tex: the finite-`N` core of `\ref{thm:arg-integrals}` (Theorem 31); the intended derivation is
`\ref{lem:integralofarg}` (Lemma 28) plus `\ref{lem:supremumforarg}` (Lemma 29). External:
Titchmarsh, *The Theory of the Riemann Zeta-Function*, `\cite[§9.9]{Titchmarsh1986}`, and
Hasanalizade–Shen–Wong for the Backlund trick.

### Dependencies
**Depends on:** `Ffun`, `eta`, `deltaArgGen`, `argSupConst`, `integralofarg`,
`argSupConst_le_of_le`, `Ffun_analyticOnNhd`, `ballZeroCount_nonneg`,
`integral_ballZeroCount_div_eq`, `circleAverage_log_norm_Ffun_le`.
**Used by:** `arg_integrals`. -/
theorem deltaArg_bound_finite_N (f : ℂ → ℂ) (argf : ℂ → ℝ)
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))
    {σ0 σ1 c T : ℝ} (hσ0c : σ0 ≤ c) (hcσ1 : c ≤ σ1) (hc : σ1 - c ≤ eta * (c - σ0))
    (hfan : AnalyticOnNhd ℂ f (Metric.closedBall (c + T * Complex.I) (c - σ0)))
    (hargf : ∀ x ∈ Set.Icc σ0 σ1,
      f (x + T * Complex.I)
        = ‖f (x + T * Complex.I)‖ * Complex.exp (argf (x + T * Complex.I) * Complex.I))
    (hargf_cont : ContinuousOn (fun x : ℝ => argf (x + T * Complex.I)) (Set.Icc σ0 σ1))
    {Fcr : ℝ → ℝ}
    (hFcr_even : ∀ θ : ℝ, Fcr (-θ) = Fcr θ)
    (hFcr_bound : ∀ θ : ℝ,
      max (Real.log ‖f (c + (c - σ0) * Complex.exp (θ * Complex.I) + T * Complex.I)‖)
          (Real.log ‖f (c + (c - σ0) * Complex.exp (θ * Complex.I) - T * Complex.I)‖)
        ≤ Fcr θ)
    (hFcr_int : IntervalIntegrable Fcr MeasureTheory.volume 0 Real.pi)
    {N : ℕ} (hN : 0 < N) (hFN : Ffun f c T N 0 ≠ 0) :
    (1 / (2 * Real.pi)) *
        |(∫ σ in σ1..σ0, argf (σ + T * Complex.I)) - (σ0 - σ1) * argf (σ1 + T * Complex.I)|
      ≤ (σ1 - σ0) / (2 * N) + (c - σ0) / 2 *
          (-(1 / (N : ℝ)) * Real.log ‖Ffun f c T N 0‖
            + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ) := by
  have hπ := Real.pi_pos
  have hη := eta_mem_Ioo
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le hσ0c with heq | hlt
  · -- degenerate case `σ0 = c`, which forces `σ1 = c`: both sides vanish
    have hσ1 : σ1 = c := by
      rw [← heq, sub_self, mul_zero] at hc
      linarith
    rw [heq, hσ1]
    simp
  · have hR : 0 < c - σ0 := by linarith
    have hσ : σ0 < σ1 := lt_of_lt_of_le hlt hcσ1
    have hσ1c : σ1 - c < c - σ0 := by nlinarith [hη.2]
    have hc' : (σ0 + σ1) / 2 < c := by linarith
    have hCle := argSupConst_le_of_le hlt hcσ1 hc
    have hint : IntervalIntegrable (fun σ : ℝ => argf (σ + T * Complex.I)) volume σ1 σ0 := by
      apply IntervalIntegrable.symm
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le hσ.le]
    have hLHS : (∫ σ in σ1..σ0, argf (σ + T * Complex.I))
        - (σ0 - σ1) * argf (σ1 + T * Complex.I)
        = ∫ σ in σ1..σ0, deltaArgGen argf T σ1 σ := by
      unfold deltaArgGen
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
    rw [hLHS]
    have hIA := integralofarg f argf hf hN hσ hc' hfan hargf hargf_cont hFN
    have hF := Ffun_analyticOnNhd hf hfan N
    have hI0 : 0 ≤ ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u :=
      intervalIntegral.integral_nonneg hR.le
        (fun u hu => div_nonneg (ballZeroCount_nonneg hR hF hFN hu.2) hu.1)
    have hIeq := integral_ballZeroCount_div_eq hR hF hFN
    have hFcr_bound' : ∀ θ : ℝ,
        max (Real.log ‖f (c + ((c - σ0 : ℝ) : ℂ) * Complex.exp (θ * Complex.I) + T * Complex.I)‖)
            (Real.log ‖f (c + ((c - σ0 : ℝ) : ℂ) * Complex.exp (θ * Complex.I) - T * Complex.I)‖)
          ≤ Fcr θ := by
      intro θ
      have := hFcr_bound θ
      push_cast
      exact this
    have hcirc := circleAverage_log_norm_Ffun_le hR hF hFN hFcr_even hFcr_bound' hFcr_int
    have hI_le : ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u
        ≤ (N / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Fcr θ) - Real.log ‖Ffun f c T N 0‖ := by
      rw [hIeq]; linarith [hcirc]
    have hCI : argSupConst c σ0 σ1 *
          ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u
        ≤ (c - σ0) * ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u :=
      mul_le_mul_of_nonneg_right hCle hI0
    have hpiN : (1 / (2 * Real.pi)) * (Real.pi / N) = 1 / (2 * N) := by
      field_simp
    calc (1 / (2 * Real.pi)) * |∫ σ in σ1..σ0, deltaArgGen argf T σ1 σ|
        ≤ (1 / (2 * Real.pi)) * (Real.pi / N * ((σ1 - σ0) + argSupConst c σ0 σ1 *
            ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u)) :=
          mul_le_mul_of_nonneg_left hIA (by positivity)
      _ = (1 / (2 * N)) * ((σ1 - σ0) + argSupConst c σ0 σ1 *
            ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u) := by
          rw [← mul_assoc, hpiN]
      _ ≤ (1 / (2 * N)) * ((σ1 - σ0) + (c - σ0) *
            ∫ u in (0 : ℝ)..(c - σ0), (ballZeroCount (Ffun f c T N) u : ℝ) / u) :=
          mul_le_mul_of_nonneg_left (by linarith [hCI]) (by positivity)
      _ ≤ (1 / (2 * N)) * ((σ1 - σ0) + (c - σ0) *
            ((N / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Fcr θ) - Real.log ‖Ffun f c T N 0‖)) :=
          mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_left hI_le hR.le]) (by positivity)
      _ = (σ1 - σ0) / (2 * N) + (c - σ0) / 2 *
            (-(1 / (N : ℝ)) * Real.log ‖Ffun f c T N 0‖
              + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ) := by
          field_simp
          ring

end DeltaArgBound

/-- **`Theorem \ref{thm:arg-integrals}` (Theorem 31).** Suppose `f(s̄) = \overline{f(s)}`,
`f(c+iT) ≠ 0`, and `c ∈ [σ0,σ1]` satisfies `σ1 - c ≤ η(c-σ0)`. With `r = c - σ0`, suppose `f` is
analytic on the closed disc `|s-(c+iT)| ≤ r`, that `argf` is a continuous argument of `f` along
`[σ0,σ1] + iT`, and that `Fcr` is an even, interval-integrable real-valued bound on
`max(log|f(c+re^{iθ}+iT)|, log|f(c+re^{iθ}-iT)|)`. Then
`(1/2π)|∫_{σ1}^{σ0} arg f(σ+iT)dσ - (σ0-σ1) arg f(σ1+iT)| ≤ (c-σ0)/2 (-log|f(c+iT)| +
(1/π)∫_0^π Fcr(θ)dθ)`.

### Summary of Proof
Apply `deltaArg_bound_finite_N` at each `N = N_m` from `ExternalFacts.backlund_trick`'s sequence
(eventually positive, since `N_m → ∞`), then let `m → ∞`: the left-hand side is `m`-independent,
and `Ffun f c T (N_m) 0 = (1/2)(f(c+iT)^{N_m} + f(c-iT)^{N_m})` is exactly the quantity
`backlund_trick` shows satisfies `(1/N_m) log‖·‖ → log‖f(c+iT)‖`. The finite-`N` bound's
additive term `(σ1-σ0)/(2N_m)` — Lemma 28's `+1` after integration, see
`deltaArg_bound_finite_N` — tends to `0` (`Tendsto.div_atTop`), so it leaves no trace here,
exactly as the tex's proof of Theorem 31 records.

### Lean Notes
The tex takes the `N → ∞` limit informally; here it is a genuine `Filter.Tendsto` argument
(`ge_of_tendsto` against an eventually-true bound along `backlund_trick`'s sequence `N_m`).

**Hypotheses `hfan`, `hargf`, `hargf_cont`, `hFcr_int`** are exactly what the tex uses tacitly:
`f` analytic on the disc `|s-(c+iT)| ≤ c-σ0` (for Jensen's formula), `arg f` a continuous
argument of `f` along the segment `[σ0,σ1] + iT`, and `F_{c,r}` integrable. All four are
load-bearing rather than bookkeeping — see `deltaArg_bound_finite_N`'s docstring for what fails
without `hargf`/`hargf_cont` or without `hFcr_int`. Nonvanishing of `f` on the segment is *not*
needed (`hargf` is vacuous at a zero), and neither is `T > 0`.

**`hargf`/`hargf_cont` are NOT a discrepancy with the tex.** By the tex's definition of `arg f`
after Equation `\ref{eq:zerodensityintegral}` (Equation 13) — continuous variation to the right
of the zeros and then along the horizontal line, "provided that horizontal line does not contain
a zero of `f`" — the two hypotheses hold automatically on every horizontal line without zeros of
`f`. On a line through a zero the tex switches to the halving convention
`lim_{ε→0} ½(arg f(T+ε) + arg f(T-ε))`, which this theorem's own proof invokes in its first
sentence ("reduce to the case of having no zeros on the horizontal line … using uniform
continuity"). So the Lean statement is the no-zero case, exactly the case the tex proves; the
passage to lines through zeros by the convention is what is not formalized.

**On `hf0`.** `ExternalFacts.backlund_trick` needs `f (c+T*I) ≠ 0`, threaded through here as
`hf0`. The tex states it inline, as part of `thm:arg-integrals`'s own opening sentence ("Suppose
`\bar{f(s)} = f(\bar s)` and `f(c+iT) ≠ 0`"). At the real call site (`c = 1`, `f = riemannZeta`,
from `Littlewood.LittlewoodShort`), this is `riemannZeta_ne_zero_of_one_le_re`.

**On the conjugate hypothesis `backlund_trick` takes.** That statement needs conjugate symmetry —
it is false without it, see its docstring — in the single-value form
`f (c - T*I) = conj (f (c + T*I))`. Nothing extra is needed here: this theorem assumes the global
symmetry `hf : ∀ s, conj (f s) = f (conj s)` — the tex's own `\bar{f(s)} = f(\bar s)`, stated in
the same opening sentence — and the single value is `hf (c + T*I)` combined with
`conj (c + T*I) = c - T*I`.

**The `η`-hypothesis is `≤`, one weakening beyond the source's `σ1-c < η(c-σ0)`.** `≤` is
sufficient — `supremumforarg_full` is proved from exactly this non-strict hypothesis — and it is
necessary, since the real call site (`σ0 = 1-r, σ1 = 1+ηr, c = 1`) lands exactly on the boundary.

**`hσ0c : σ0 ≤ c` and `hcσ1 : c ≤ σ1`** are the tex's own "`c ∈ [σ0,σ1]`"; see
`deltaArg_bound_finite_N`'s docstring for why the conclusion is false without them. Both are
discharged by `linarith` at the call sites.

### References
tex: `\ref{thm:arg-integrals}` (Theorem 31), whose opening sentence states both `hf` and `hf0`.
Equation `\ref{eq:eta}` (Equation 15) for `η`. External: Backlund's trick via
`ExternalFacts.backlund_trick` (Hasanalizade–Shen–Wong).

### Dependencies
**Depends on:** `deltaArg_bound_finite_N`, `backlund_trick`, `Ffun`, `eta`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem arg_integrals (f : ℂ → ℂ) (argf : ℂ → ℝ)
    (hf : ∀ s : ℂ, (starRingEnd ℂ) (f s) = f ((starRingEnd ℂ) s))
    {σ0 σ1 c T : ℝ} (hf0 : f (c + T * Complex.I) ≠ 0) (hσ0c : σ0 ≤ c) (hcσ1 : c ≤ σ1)
    (hc : σ1 - c ≤ eta * (c - σ0))
    (hfan : AnalyticOnNhd ℂ f (Metric.closedBall (c + T * Complex.I) (c - σ0)))
    (hargf : ∀ x ∈ Set.Icc σ0 σ1,
      f (x + T * Complex.I)
        = ‖f (x + T * Complex.I)‖ * Complex.exp (argf (x + T * Complex.I) * Complex.I))
    (hargf_cont : ContinuousOn (fun x : ℝ => argf (x + T * Complex.I)) (Set.Icc σ0 σ1))
    {Fcr : ℝ → ℝ}
    (hFcr_even : ∀ θ : ℝ, Fcr (-θ) = Fcr θ)
    (hFcr_bound : ∀ θ : ℝ,
      max (Real.log ‖f (c + (c - σ0) * Complex.exp (θ * Complex.I) + T * Complex.I)‖)
          (Real.log ‖f (c + (c - σ0) * Complex.exp (θ * Complex.I) - T * Complex.I)‖)
        ≤ Fcr θ)
    (hFcr_int : IntervalIntegrable Fcr MeasureTheory.volume 0 Real.pi) :
    (1 / (2 * Real.pi)) *
        |(∫ σ in σ1..σ0, argf (σ + T * Complex.I)) - (σ0 - σ1) * argf (σ1 + T * Complex.I)|
      ≤ (c - σ0) / 2 *
          (-Real.log ‖f (c + T * Complex.I)‖ + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ) := by
  have hconj : f (c - T * Complex.I) = (starRingEnd ℂ) (f (c + T * Complex.I)) := by
    rw [hf (c + T * Complex.I)]
    congr 1
    simp [Complex.ext_iff]
  obtain ⟨Ns, hNs_atTop, hNs_tendsto, hNs_ne⟩ := backlund_trick f c T hf0 hconj
  have hbound : ∀ᶠ m in Filter.atTop, (1 / (2 * Real.pi)) *
        |(∫ σ in σ1..σ0, argf (σ + T * Complex.I)) - (σ0 - σ1) * argf (σ1 + T * Complex.I)|
      ≤ (σ1 - σ0) / (2 * (Ns m : ℝ)) + (c - σ0) / 2 *
          (-(1 / (Ns m : ℝ)) * Real.log ‖Ffun f c T (Ns m) 0‖
            + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ) := by
    filter_upwards [hNs_atTop.eventually_gt_atTop 0] with m hm
    have hFN : Ffun f c T (Ns m) 0 ≠ 0 := by
      simpa [Ffun, zero_add] using hNs_ne m
    exact deltaArg_bound_finite_N f argf hf hσ0c hcσ1 hc hfan hargf hargf_cont hFcr_even
      hFcr_bound hFcr_int hm hFN
  -- the additive term of Lemma 28, `(σ1-σ0)/(2N_m)`, vanishes along the sequence
  have hzero : Filter.Tendsto (fun m => (σ1 - σ0) / (2 * (Ns m : ℝ))) Filter.atTop (nhds 0) := by
    have hcast : Filter.Tendsto (fun m => (Ns m : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hNs_atTop
    exact tendsto_const_nhds.div_atTop (hcast.const_mul_atTop two_pos)
  have htendsto : Filter.Tendsto
      (fun m => (σ1 - σ0) / (2 * (Ns m : ℝ)) + (c - σ0) / 2 *
          (-(1 / (Ns m : ℝ)) * Real.log ‖Ffun f c T (Ns m) 0‖
            + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ))
      Filter.atTop
      (nhds (0 + (c - σ0) / 2 *
          (-Real.log ‖f (c + T * Complex.I)‖
            + (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Fcr θ))) := by
    refine hzero.add ?_
    have hkey : Filter.Tendsto (fun m => -(1 / (Ns m : ℝ)) * Real.log ‖Ffun f c T (Ns m) 0‖)
        Filter.atTop (nhds (-Real.log ‖f (c + T * Complex.I)‖)) := by
      have heq : ∀ m, Ffun f c T (Ns m) 0
          = (1 / 2 : ℂ) * (f (c + T * Complex.I) ^ (Ns m) + f (c - T * Complex.I) ^ (Ns m)) := by
        intro m; unfold Ffun; congr 2 <;> ring
      have hseq : Filter.Tendsto
          (fun m => (1 / (Ns m : ℝ)) * Real.log ‖Ffun f c T (Ns m) 0‖)
          Filter.atTop (nhds (Real.log ‖f (c + T * Complex.I)‖)) := by
        simp only [heq]
        exact hNs_tendsto
      simpa using hseq.neg
    exact tendsto_const_nhds.mul (hkey.add tendsto_const_nhds)
  have hfin := ge_of_tendsto htendsto hbound
  rwa [zero_add] at hfin

