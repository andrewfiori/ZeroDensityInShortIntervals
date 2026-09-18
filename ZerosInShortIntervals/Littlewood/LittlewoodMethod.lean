/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.JensenScaleConstants

/-! # Littlewood zero detection (`\S \ref{sec:littlewood}`, Section 3)

This file formalizes the parts of Section `\ref{sec:littlewood}` (Section 3) of
`ZerosInShortIntervals.tex` up to (but not including) the argument-integral machinery of
`\S \ref{sec:argintegrals}` (Section 3.1), which lives in
`ZerosInShortIntervals.Littlewood.ArgIntegrals`.

Contents, with current tex numbers: the construction of the tex's `arg ζ` (`argZetaDef`, and
`argZeta := argZetaDef`, below), `Nsigma`, Lemma `\ref{lemma:littlewood-mainterm}` (Lemma 25,
`littlewood_mainterm`/`_tight`), Lemma `\ref{lemma:littlewood-outerlog}` (Lemma 26,
`littlewood_outerlog`), and Lemma `\ref{lem:littlewood-argsetup}` (Lemma 27,
`littlewood_argsetup`). Equation `\ref{eq:zerodensityintegral}` (Equation 13, Littlewood's
identity) and Equation `\ref{eq:simplelittlewoodzerodensity}` (Equation 14,
`simplelittlewoodzerodensity`) live in `ZerosInShortIntervals.Littlewood.LittlewoodIdentity`, where
Equation 13 is proved following Farzanfard's thesis, Lemma 2.2, and Titchmarsh §9.9.

**On `argZeta`.** The core input of this section is Littlewood's zero-counting identity
(`\cite[§9.9]{Titchmarsh1986}`), which involves `arg ζ` defined "by continuous variation
along a vertical line to the right of any zeros … followed by … a horizontal line" (i.e. a specific
branch of `arg ζ`, continued from `Re s = +∞` where `arg ζ → 0`). That branch is **not** jointly
continuous on `ℂ`: it jumps by `2π` across zero ordinates. So it cannot be characterised by
global continuity, and downstream statements ask instead for continuity along one segment at a
time.

**The tex's `arg ζ` is *constructed*, and `argZeta` is that construction** (section "The tex's
`arg ζ`, constructed"): `logZetaLine s := G(2 + i·Im s) - ∫_{Re s}^{2} (ζ'/ζ)(x + i·Im s) dx`,
`argZetaDef s := Im (logZetaLine s)`, and `argZeta := argZetaDef`. It is proved to agree with
`Im G` on `Re s > 1` (`argZetaDef_eq_im_G`, hence `argZeta_eq_im_G`) and, on every horizontal line
`Im s = T ≠ 0` carrying no zero of `ζ` on `[a, 2] + iT`, to be a continuous argument of `ζ` there
(`zeta_eq_norm_mul_exp_argZetaDef`, `argZetaDef_continuousOn_line`; the `[a, ∞)` versions are in
`LittlewoodIdentity`) — exactly the two properties the tex's definition (continuous variation to
the right of `1`, then along the horizontal line "provided that horizontal line does not contain a
zero of `f`") asserts. On a line through a zero the tex uses a halving convention; there
`argZetaDef` is a junk value (the integral in `logZetaLine` is not integrable) and no property is
claimed. Littlewood's identity (Equation 13) is proved for it
(`LittlewoodIdentity.littlewood_zero_density_integral`), with no argument hypothesis; downstream,
continuity of `u ↦ argZeta(u + iT)` on a segment is a hypothesis of `littlewood_argsetup` and is
supplied at the call sites from the zero-free-edge hypotheses `hzf_*`.
-/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates]

/-! ### The tex's `arg ζ`, constructed

The tex defines `arg ζ(s)` (more generally `arg f`) by continuous variation: start on the real axis
to the right of `1`, move vertically to height `Im s` inside `Re s > 1`, then along the horizontal
line to `s` — "provided that horizontal line does not contain a zero"; on a line through a zero a
halving convention is used instead. The vertical leg is `Im G` (`G = LSeries GTerm`, a logarithm of
`ζ` on `Re s > 1` that is real on the real axis), and the horizontal leg is the integral of `ζ'/ζ`.
So the whole construction is the single formula

  `logZetaLine s = G(2 + i·Im s) - ∫_{Re s}^{2} (ζ'/ζ)(x + i·Im s) dx`,
  `argZetaDef s = Im (logZetaLine s)`,

with the vertical leg taken at `Re = 2` (any abscissa `> 1` gives the same function on `Re s > 1`).
Below: `argZetaDef = Im G` on `Re s > 1` (`argZetaDef_eq_im_G`, by the fundamental theorem of
calculus with `Definitions.G_hasDerivAt`), and on a horizontal line `Im s = T ≠ 0` with no zero of
`ζ` on `[a, 2] + iT`, `exp (logZetaLine s) = ζ s` (`exp_logZetaLine_line`, because
`ζ·exp(-logZetaLine)` has zero derivative along the line and equals `1` at `Re = 2`), whence
`ζ s = ‖ζ s‖·exp(i·argZetaDef s)` (`zeta_eq_norm_mul_exp_argZetaDef`) and continuity in `Re s`
(`argZetaDef_continuousOn_line`). These are precisely the hypotheses `hargf`/`hargf_cont` of
`ArgIntegrals.integralofarg`/`deltaArg_bound_finite_N`/`arg_integrals`, for `f = ζ` on zero-free
lines; `LittlewoodShort.littlewoodshort` discharges them with the `[a, ∞)` variants proved in
`LittlewoodIdentity`. -/

/-- **`(ζ'/ζ)(x + iT)` as a function of the real variable `x`** — the integrand of the horizontal
leg of the tex's `arg ζ`.

### Summary of Proof
A definition.

### References
tex: the definition of `arg f` by continuous variation along a horizontal line.

### Dependencies
**Depends on:** none.
**Used by:** `logZetaLine`, `logDerivZetaLine_continuousAt`, `hasDerivAt_G_line`,
`integral_logDerivZetaLine_eq_G`, `hasDerivAt_logZetaLine_line`. -/
noncomputable def logDerivZetaLine (T x : ℝ) : ℂ :=
  deriv riemannZeta ((x : ℂ) + T * Complex.I) / riemannZeta ((x : ℂ) + T * Complex.I)

/-- **The tex's `log ζ(s)`: `G(2 + i·Im s)` continued along the horizontal line to `s`**,
`logZetaLine s = G(2 + i·Im s) - ∫_{Re s}^{2} (ζ'/ζ)(x + i·Im s) dx`.

### Summary of Proof
A definition. On `Re s > 1` it equals `G s` (`logZetaLine_eq_G`); on a zero-free horizontal line
it is a logarithm of `ζ` (`exp_logZetaLine_line`). On a line through a zero the integral is not
integrable in Lean's sense (the integrand has a simple pole on the segment), so the value there is
junk — which is where the tex uses its halving convention instead.

### References
tex: the definition of `arg f` by continuous variation (the paragraph after Equation 13).

### Dependencies
**Depends on:** `GTerm`, `logDerivZetaLine`.
**Used by:** `argZetaDef`, `logZetaLine_eq_G`, `logZetaLine_line_eq`,
`hasDerivAt_logZetaLine_line`, `exp_logZetaLine_line`; and, in `LittlewoodIdentity`, the
`[a, ∞)`-variants `hasDerivAt_logZetaLine_line'`/`exp_logZetaLine_line'`/`re_logZetaLine_line'`,
`integral_logDerivZetaLine_eq_logZetaLine` and `left_edge_identity`. -/
noncomputable def logZetaLine (s : ℂ) : ℂ :=
  LSeries GTerm (2 + s.im * Complex.I) - ∫ x in s.re..2, logDerivZetaLine s.im x

/-- **The tex's `arg ζ(s)`, constructed: `argZetaDef s = Im (logZetaLine s)`.**

### Summary of Proof
A definition. Its two defining properties are `argZetaDef_eq_im_G` (on `Re s > 1`) and
`zeta_eq_norm_mul_exp_argZetaDef` / `argZetaDef_continuousOn_line` (on zero-free horizontal
lines).

### Lean Notes
`argZeta` is *defined* to be this function, so every property proved here is a property of the
`arg ζ` used throughout the Littlewood chain.

### References
tex: the definition of `arg f` by continuous variation (the paragraph after Equation 13).

### Dependencies
**Depends on:** `logZetaLine`.
**Used by:** `argZetaDef_eq_im_G`, `zeta_eq_norm_mul_exp_argZetaDef`,
`argZetaDef_continuousOn_line`, `argZeta`, and, in `LittlewoodIdentity`,
`argZetaDef_continuousOn_line'`, `zeta_eq_norm_mul_exp_argZetaDef'`,
`littlewood_identity_argZetaDef`. -/
noncomputable def argZetaDef (s : ℂ) : ℝ := (logZetaLine s).im

/-- **A horizontal line at height `T ≠ 0` avoids `ζ`'s pole:** `x + iT ≠ 1`. Compare imaginary
parts.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `continuous_zeta_line`, `exp_logZetaLine_line`, `hasDerivAt_logZetaLine_line`,
`LittlewoodIdentity.exp_logZetaLine_line'`, `LittlewoodIdentity.hasDerivAt_logZetaLine_line'`,
`LittlewoodIdentity.integral_logDerivZetaLine_eq_logZetaLine`. -/
theorem line_ne_one {T : ℝ} (hT : T ≠ 0) (x : ℝ) : (x : ℂ) + T * Complex.I ≠ 1 := by
  intro h
  exact hT (by simpa using congrArg Complex.im h)

/-- **`x ↦ ζ(x + iT)` is continuous for `T ≠ 0`**, since `ζ` is analytic away from `1`
(`analyticOn_riemannZeta`) and the line misses `1` (`line_ne_one`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `line_ne_one`.
**Used by:** `hasDerivAt_logZetaLine_line`, `LittlewoodIdentity.hasDerivAt_logZetaLine_line'`. -/
theorem continuous_zeta_line {T : ℝ} (hT : T ≠ 0) :
    Continuous (fun x : ℝ => riemannZeta ((x : ℂ) + T * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmap : Continuous (fun y : ℝ => (y : ℂ) + T * Complex.I) := by fun_prop
  exact (analyticOn_riemannZeta _ (line_ne_one hT x)).continuousAt.comp_of_eq
    hmap.continuousAt rfl

/-- **`(ζ'/ζ)(x + iT)` is continuous in `x` wherever `x + iT ≠ 1` and `ζ(x + iT) ≠ 0`.** `ζ` is
analytic there, so `ζ'` is too (`AnalyticAt.deriv`), and the quotient of continuous functions with
nonzero denominator is continuous.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logDerivZetaLine`.
**Used by:** `hasDerivAt_logZetaLine_line`, `integral_logDerivZetaLine_eq_G`,
`LittlewoodIdentity.hasDerivAt_logZetaLine_line'`,
`LittlewoodIdentity.integral_logDerivZetaLine_eq_logZetaLine`. -/
theorem logDerivZetaLine_continuousAt {T x : ℝ} (hne1 : (x : ℂ) + T * Complex.I ≠ 1)
    (hz : riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0) :
    ContinuousAt (logDerivZetaLine T) x := by
  have hmap : Continuous (fun y : ℝ => (y : ℂ) + T * Complex.I) := by fun_prop
  have han : AnalyticAt ℂ riemannZeta ((x : ℂ) + T * Complex.I) :=
    analyticOn_riemannZeta _ hne1
  have h1 : ContinuousAt (fun y : ℝ => deriv riemannZeta ((y : ℂ) + T * Complex.I)) x :=
    han.deriv.continuousAt.comp_of_eq hmap.continuousAt rfl
  have h2 : ContinuousAt (fun y : ℝ => riemannZeta ((y : ℂ) + T * Complex.I)) x :=
    han.continuousAt.comp_of_eq hmap.continuousAt rfl
  exact h1.div h2 hz

/-- **`x ↦ ζ(x + iT)` has derivative `ζ'(x + iT)` wherever `x + iT ≠ 1`.** The complex derivative
(`differentiableAt_riemannZeta`) composed with the affine map `w ↦ w + iT`, restricted to the real
line by `HasDerivAt.comp_ofReal`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `exp_logZetaLine_line`, `LittlewoodIdentity.exp_logZetaLine_line'`. -/
theorem hasDerivAt_zeta_line {T x : ℝ} (hne1 : (x : ℂ) + T * Complex.I ≠ 1) :
    HasDerivAt (fun y : ℝ => riemannZeta ((y : ℂ) + T * Complex.I))
      (deriv riemannZeta ((x : ℂ) + T * Complex.I)) x := by
  have hd := (differentiableAt_riemannZeta hne1).hasDerivAt
  have hshift : HasDerivAt (fun w : ℂ => w + T * Complex.I) 1 (x : ℂ) :=
    (hasDerivAt_id _).add_const _
  have h1 := hd.comp (x : ℂ) hshift
  rw [mul_one] at h1
  exact h1.comp_ofReal

/-- **`x ↦ G(x + iT)` has derivative `(ζ'/ζ)(x + iT)` for `x > 1`** — `Definitions.G_hasDerivAt`
along the line, via `HasDerivAt.comp_ofReal`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `G_hasDerivAt`, `logDerivZetaLine`.
**Used by:** `integral_logDerivZetaLine_eq_G`. -/
theorem hasDerivAt_G_line {T x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => LSeries GTerm ((y : ℂ) + T * Complex.I))
      (logDerivZetaLine T x) x := by
  have hre : 1 < ((x : ℂ) + T * Complex.I).re := by simp [hx]
  have hd := G_hasDerivAt hre
  have hshift : HasDerivAt (fun w : ℂ => w + T * Complex.I) 1 (x : ℂ) :=
    (hasDerivAt_id _).add_const _
  have h1 := hd.comp (x : ℂ) hshift
  rw [mul_one] at h1
  exact h1.comp_ofReal

/-- **The horizontal leg inside `Re s > 1` is a difference of values of `G`:**
`∫_σ^2 (ζ'/ζ)(x + iT) dx = G(2 + iT) - G(σ + iT)` for `σ > 1`.

### Summary of Proof
The fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) with
`hasDerivAt_G_line` at every point of `[σ, 2]` (all have real part `> 1`), the integrand being
continuous there (`logDerivZetaLine_continuousAt`, as `ζ ≠ 0` on `Re > 1`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `hasDerivAt_G_line`, `logDerivZetaLine_continuousAt`.
**Used by:** `logZetaLine_eq_G`. -/
theorem integral_logDerivZetaLine_eq_G {T σ : ℝ} (hσ : 1 < σ) :
    ∫ x in σ..2, logDerivZetaLine T x
      = LSeries GTerm (2 + T * Complex.I) - LSeries GTerm ((σ : ℂ) + T * Complex.I) := by
  have hmem : ∀ x ∈ Set.uIcc σ 2, 1 < x := by
    intro x hx
    rcases le_total σ 2 with h | h
    · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
    · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc σ 2,
      HasDerivAt (fun y : ℝ => LSeries GTerm ((y : ℂ) + T * Complex.I))
        (logDerivZetaLine T x) x :=
    fun x hx => hasDerivAt_G_line (hmem x hx)
  have hint : IntervalIntegrable (logDerivZetaLine T) MeasureTheory.volume σ 2 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx1 := hmem x hx
    apply logDerivZetaLine_continuousAt
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    · exact riemannZeta_ne_zero_of_one_lt_re (by simp [hx1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- **`logZetaLine s = G s` for `Re s > 1`**: the vertical-then-horizontal continuation from the
real axis reproduces the Dirichlet series `G` on the whole half-plane
(`integral_logDerivZetaLine_eq_G` and `s = Re s + i·Im s`).

### References
tex: the "to the right of 1" clause of the definition of `arg f`.

### Dependencies
**Depends on:** `logZetaLine`, `integral_logDerivZetaLine_eq_G`.
**Used by:** `argZetaDef_eq_im_G`, `LittlewoodIdentity.left_edge_identity`. -/
theorem logZetaLine_eq_G {s : ℂ} (hs : 1 < s.re) : logZetaLine s = LSeries GTerm s := by
  unfold logZetaLine
  rw [integral_logDerivZetaLine_eq_G hs, sub_sub_cancel, Complex.re_add_im]

/-- **`argZetaDef s = Im G(s)` for `Re s > 1`** — the first of the two defining properties of the
tex's `arg ζ`: on the half-plane of absolute convergence the constructed branch is `Im G`.

### Summary of Proof
`logZetaLine_eq_G` and the definition `argZetaDef = Im ∘ logZetaLine`.

### References
tex: the "to the right of 1" clause of the definition of `arg f`.

### Dependencies
**Depends on:** `argZetaDef`, `logZetaLine_eq_G`.
**Used by:** `argZeta_eq_im_G`. -/
theorem argZetaDef_eq_im_G {s : ℂ} (hs : 1 < s.re) : argZetaDef s = (LSeries GTerm s).im := by
  unfold argZetaDef
  rw [logZetaLine_eq_G hs]

/-- **`logZetaLine` along the line `Im s = T`, as a function of `Re s`:**
`y ↦ G(2 + iT) - ∫_y^2 (ζ'/ζ)(x + iT) dx`. Unfolding, with `Re (y + iT) = y`, `Im (y + iT) = T`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `logZetaLine`.
**Used by:** `hasDerivAt_logZetaLine_line`, `LittlewoodIdentity.hasDerivAt_logZetaLine_line'`. -/
theorem logZetaLine_line_eq {T : ℝ} :
    (fun y : ℝ => logZetaLine ((y : ℂ) + T * Complex.I))
      = fun y : ℝ => LSeries GTerm (2 + T * Complex.I) - ∫ x in y..2, logDerivZetaLine T x := by
  funext y
  simp [logZetaLine]

/-- **On a zero-free horizontal line, `Re s ↦ logZetaLine s` has derivative `(ζ'/ζ)(s)`.** For
`T ≠ 0` and `ζ ≠ 0` on `[a, 2] + iT`, at every `σ ∈ [a, 2]`.

### Summary of Proof
`intervalIntegral.integral_hasDerivAt_left`: the derivative of `y ↦ ∫_y^2 g` at `σ` is `-g σ` when
`g` is interval-integrable on `[σ, 2]` and continuous at `σ`. Both hold for `g = (ζ'/ζ)(· + iT)`
by `logDerivZetaLine_continuousAt`, since the segment carries no zero and (`T ≠ 0`) no pole. The
measurability side condition is discharged from continuity on the *open* set
`{x | ζ(x + iT) ≠ 0}` (`isOpen_ne_fun`, `ContinuousAt.stronglyMeasurableAtFilter`).

### References
No tex counterpart.

### Dependencies
**Depends on:** `logZetaLine_line_eq`, `continuous_zeta_line`, `logDerivZetaLine_continuousAt`,
`line_ne_one`.
**Used by:** `exp_logZetaLine_line`, `argZetaDef_continuousOn_line`. -/
theorem hasDerivAt_logZetaLine_line {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x ∈ Set.Icc a 2, riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a 2) :
    HasDerivAt (fun y : ℝ => logZetaLine ((y : ℂ) + T * Complex.I))
      (logDerivZetaLine T σ) σ := by
  rw [logZetaLine_line_eq]
  have hopen : IsOpen {x : ℝ | riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0} :=
    isOpen_ne_fun (continuous_zeta_line hT) continuous_const
  have hmeas : StronglyMeasurableAtFilter (logDerivZetaLine T) (nhds σ)
      MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter hopen
      (fun x hx => logDerivZetaLine_continuousAt (line_ne_one hT x) hx) σ (hzf σ hσ)
  have hint : IntervalIntegrable (logDerivZetaLine T) MeasureTheory.volume σ 2 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hσ.2] at hx
    exact (logDerivZetaLine_continuousAt (line_ne_one hT x)
      (hzf x ⟨le_trans hσ.1 hx.1, hx.2⟩)).continuousWithinAt
  have hcont : ContinuousAt (logDerivZetaLine T) σ :=
    logDerivZetaLine_continuousAt (line_ne_one hT σ) (hzf σ hσ)
  have h := (hasDerivAt_const σ (LSeries GTerm (2 + T * Complex.I))).sub
    (intervalIntegral.integral_hasDerivAt_left hint hmeas hcont)
  refine h.congr_deriv ?_
  ring

/-- **On a zero-free horizontal line, `logZetaLine` is a logarithm of `ζ`:**
`exp (logZetaLine (σ + iT)) = ζ(σ + iT)` for `T ≠ 0`, `ζ ≠ 0` on `[a, 2] + iT`, `σ ∈ [a, 2]`.

### Summary of Proof
Let `φ(y) := ζ(y + iT)·exp(-logZetaLine (y + iT))`. By `hasDerivAt_zeta_line` and
`hasDerivAt_logZetaLine_line`, `φ' = exp(-L)·(ζ' - ζ·(ζ'/ζ)) = 0` on `[σ, 2]`, so `φ(σ) = φ(2)`
(the fundamental theorem of calculus with the zero derivative). At `y = 2` the integral leg
vanishes, `logZetaLine (2 + iT) = G(2 + iT)`, and `exp (G(2 + iT)) = ζ(2 + iT)`
(`Definitions.GTerm_LSeries_exp_eq_riemannZeta`), so `φ(2) = 1`. Hence `φ(σ) = 1`, i.e.
`ζ(σ + iT) = exp (logZetaLine (σ + iT))`.

### Lean Notes
This is where the tex's proviso "provided that horizontal line does not contain a zero of `f`"
enters: `hzf` is used both for the derivative of the integral leg and to cancel `ζ` in `φ'`.

### References
tex: the definition of `arg f` by continuous variation along a horizontal line.

### Dependencies
**Depends on:** `hasDerivAt_zeta_line`, `hasDerivAt_logZetaLine_line`, `line_ne_one`,
`logZetaLine`, `GTerm_LSeries_exp_eq_riemannZeta`.
**Used by:** `zeta_eq_norm_mul_exp_argZetaDef`. -/
theorem exp_logZetaLine_line {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x ∈ Set.Icc a 2, riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a 2) :
    Complex.exp (logZetaLine ((σ : ℂ) + T * Complex.I))
      = riemannZeta ((σ : ℂ) + T * Complex.I) := by
  set L : ℝ → ℂ := fun y => logZetaLine ((y : ℂ) + T * Complex.I) with hL
  set φ : ℝ → ℂ := fun y => riemannZeta ((y : ℂ) + T * Complex.I) * Complex.exp (-(L y))
    with hφ
  have hφderiv : ∀ y ∈ Set.uIcc σ 2, HasDerivAt φ 0 y := by
    intro y hy
    rw [Set.uIcc_of_le hσ.2] at hy
    have hy' : y ∈ Set.Icc a 2 := ⟨le_trans hσ.1 hy.1, hy.2⟩
    have hz := hzf y hy'
    have h1 := hasDerivAt_zeta_line (T := T) (x := y) (line_ne_one hT y)
    have h2 : HasDerivAt L (logDerivZetaLine T y) y :=
      hasDerivAt_logZetaLine_line hT hzf hy'
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
  have hL2 : L 2 = LSeries GTerm (2 + T * Complex.I) := by
    simp only [hL, logZetaLine]
    simp
  have h2re : (1 : ℝ) < ((2 : ℂ) + T * Complex.I).re := by simp
  have hζ2 : riemannZeta ((2 : ℂ) + T * Complex.I)
      = Complex.exp (LSeries GTerm (2 + T * Complex.I)) :=
    (GTerm_LSeries_exp_eq_riemannZeta h2re).symm
  have hφ2 : φ 2 = 1 := by
    simp only [hφ, hL2]
    push_cast
    rw [hζ2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [hφ2] at hφσ
  have hφσ' : riemannZeta ((σ : ℂ) + T * Complex.I) * (Complex.exp (L σ))⁻¹ = 1 := by
    rw [← Complex.exp_neg]; exact hφσ
  exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hφσ').symm

/-- **On a zero-free horizontal line, `argZetaDef` is an argument of `ζ`:**
`ζ(σ + iT) = ‖ζ(σ + iT)‖·exp(i·argZetaDef (σ + iT))` for `T ≠ 0`, `ζ ≠ 0` on `[a, 2] + iT`,
`σ ∈ [a, 2]`.

### Summary of Proof
From `exp_logZetaLine_line`: `ζ = exp L = exp (Re L)·exp (i·Im L)` and `‖ζ‖ = ‖exp L‖ = exp (Re L)`
(`Complex.norm_exp`), with `argZetaDef = Im L` by definition.

### Lean Notes
This is the polar-form hypothesis `hargf` of `ArgIntegrals.integralofarg`/
`deltaArg_bound_finite_N`, established for the tex's `arg ζ` on every zero-free line, i.e. in the
tex's first case. Since `argZeta := argZetaDef`, it is exactly what
`LittlewoodShort.littlewoodshort` supplies to `arg_integrals`, there in the `[a, ∞)` form
`LittlewoodIdentity.zeta_eq_norm_mul_exp_argZetaDef'`.

### References
tex: the definition of `arg f` by continuous variation along a horizontal line, first case.

### Dependencies
**Depends on:** `exp_logZetaLine_line`, `argZetaDef`.
**Used by:** none — the call sites need the `[a, ∞)` variant
`LittlewoodIdentity.zeta_eq_norm_mul_exp_argZetaDef'`, which is proved the same way from
`exp_logZetaLine_line'`. -/
theorem zeta_eq_norm_mul_exp_argZetaDef {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x ∈ Set.Icc a 2, riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a 2) :
    riemannZeta ((σ : ℂ) + T * Complex.I)
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖
          * Complex.exp ((argZetaDef ((σ : ℂ) + T * Complex.I) : ℂ) * Complex.I) := by
  have h := exp_logZetaLine_line hT hzf hσ
  set L := logZetaLine ((σ : ℂ) + T * Complex.I) with hL
  have hnorm : ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ = Real.exp L.re := by
    rw [← h, Complex.norm_exp]
  rw [hnorm, ← h]
  unfold argZetaDef
  rw [← hL, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  exact (Complex.re_add_im L).symm

/-- **On a zero-free horizontal line, `argZetaDef` is continuous in `Re s`:**
`x ↦ argZetaDef (x + iT)` is continuous on `[a, 2]` when `T ≠ 0` and `ζ ≠ 0` on `[a, 2] + iT`.
Immediate from differentiability (`hasDerivAt_logZetaLine_line`) and continuity of `Im`.

### Lean Notes
This is the hypothesis `hargf_cont` of `ArgIntegrals.integralofarg`/`deltaArg_bound_finite_N`
for `f = ζ`, in the tex's first case (zero-free line).

### References
tex: the definition of `arg f` by continuous variation along a horizontal line, first case.

### Dependencies
**Depends on:** `hasDerivAt_logZetaLine_line`, `argZetaDef`.
**Used by:** none — the call sites need the `[a, ∞)` variant
`LittlewoodIdentity.argZetaDef_continuousOn_line'`. -/
theorem argZetaDef_continuousOn_line {T a : ℝ} (hT : T ≠ 0)
    (hzf : ∀ x ∈ Set.Icc a 2, riemannZeta ((x : ℂ) + T * Complex.I) ≠ 0) :
    ContinuousOn (fun x : ℝ => argZetaDef ((x : ℂ) + T * Complex.I)) (Set.Icc a 2) := by
  intro x hx
  exact (Complex.continuous_im.continuousAt.comp
    (hasDerivAt_logZetaLine_line hT hzf hx).continuousAt).continuousWithinAt

/-- **`argZeta`, the tex's `arg ζ(s)`: continued from `Re s = +∞` (where `arg ζ → 0`) down a
vertical line and then along a horizontal line to `s`, as described in
`\cite[§9.9]{Titchmarsh1986}` and used throughout `\S sec:littlewood`.** It is the
constructed `argZetaDef`.

### Summary of Proof
A definition, `argZeta := argZetaDef`. Its two defining properties are theorems of `argZetaDef`:
`argZeta_eq_im_G` (`= Im G` on `Re s > 1`) and, on zero-free horizontal lines,
`zeta_eq_norm_mul_exp_argZetaDef`/`argZetaDef_continuousOn_line` (a continuous argument of `ζ`).

### References
tex: the definition of `arg f` by continuous variation (the paragraph after Equation 13);
`\cite[§9.9]{Titchmarsh1986}`.

### Dependencies
**Depends on:** `argZetaDef`.
**Used by:** `argZeta_abs_le`, `argZeta_eq_im_G`, `deltaArgZeta`, `littlewood_argsetup`,
`littlewood_zero_density_integral`, `littlewoodshort`, `littlewoodshort_tight`,
`simplelittlewoodzerodensity`. -/
noncomputable def argZeta : ℂ → ℝ := argZetaDef

/-- **`argZeta` is the tex's branch on `Re s > 1`: `arg ζ(s) = Im G(s)`**, where
`G(s) := LSeries GTerm s = Σ_{n≥2} Λ(n)/(log n)·n^{-s}` is the Dirichlet series of `log ζ` on
`Re s > 1` (`Definitions.GTerm_LSeries_exp_eq_riemannZeta`: `exp (G s) = ζ s`).

### Summary of Proof
`argZetaDef_eq_im_G`, since `argZeta = argZetaDef` by definition.

### Lean Notes
`Im G` is **not** the principal argument, even on `Re s > 1`: the principal argument lies in
`(-π, π]`, whereas `Im G(σ + it)` exceeds `π` in absolute value for suitable `t` once `σ` is close
to `1`, by Bohr's theorem. So this identity, not `Complex.arg`, is what fixes the tex's branch.

### References
tex: the definition of `arg f` by continuous variation (the paragraph after Equation 13);
`\cite[§9.9]{Titchmarsh1986}`.

### Dependencies
**Depends on:** `argZeta`, `argZetaDef_eq_im_G`, `GTerm`.
**Used by:** `argZeta_abs_le`. -/
theorem argZeta_eq_im_G {s : ℂ} (hs : 1 < s.re) : argZeta s = (LSeries GTerm s).im :=
  argZetaDef_eq_im_G hs

/-- **The classical Dirichlet-series bound on `arg ζ`** (`\cite[§9.9]{Titchmarsh1986}`):
for `σ > 1`, `|arg ζ(σ+iτ)| ≤ log ζ(σ)`.

### Summary of Proof
Follows `argZeta_eq_im_G` (`arg ζ(s) = Im(G(s))`) and
`Definitions.G_norm_le` (`‖G(w)‖ ≤ G(Re w).re`, the `GTerm`-analogue of `Definitions.Phi_norm_le`):
`|Im(G(s))| ≤ ‖G(s)‖ ≤ G(σ).re = log ζ(σ)` (`Definitions.GTerm_LSeries_re_eq_log_norm`).

Non-strict, matching `LittlewoodMethod.littlewood_outerlog`'s and
`Definitions.zeta_norm_le_zeta_re`'s own precedent: promoting to `<` needs a separate
non-degeneracy argument, not given.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GTerm`, `GTerm_LSeries_re_eq_log_norm`, `G_norm_le`, `argZeta`, `argZeta_eq_im_G`.
**Used by:** `littlewood_argsetup`. -/
theorem argZeta_abs_le {σ τ : ℝ} (hσ : 1 < σ) :
    |argZeta (σ + τ * Complex.I)| ≤ Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hsre : (1:ℝ) < ((σ:ℂ) + (τ:ℂ) * Complex.I).re := by simp [hσ]
  rw [show (σ:ℂ) + τ * Complex.I = (σ:ℂ) + (τ:ℂ) * Complex.I by ring,
    argZeta_eq_im_G hsre]
  calc |(LSeries GTerm ((σ:ℂ) + (τ:ℂ) * Complex.I)).im|
      ≤ ‖LSeries GTerm ((σ:ℂ) + (τ:ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
    _ ≤ (LSeries GTerm
          (((((σ:ℂ) + (τ:ℂ) * Complex.I)).re : ℝ) : ℂ)).re := G_norm_le hsre
    _ = Real.log ‖riemannZeta (σ : ℂ)‖ := by
      rw [show ((((σ:ℂ) + (τ:ℂ) * Complex.I)).re : ℝ) = σ by simp,
        GTerm_LSeries_re_eq_log_norm (by simpa using hσ)]

/-- **`Δ arg ζ(x)|ᵃᵇ`, the change in `argZeta` from `a` to `b` along a specified path, specialized
to
horizontal segments at height `T`; notation introduced just before Lemma
`\ref{lem:littlewood-argsetup}` (Lemma 27).**

### Summary of Proof
A definition, `argZeta (b + T·I) - argZeta (a + T·I)`. It packages the tex's `Δ arg` notation for
horizontal segments, so that the argument-variation terms of the Littlewood identity can be
manipulated without unfolding `argZeta` itself.

### References
tex: the `Δ arg` notation introduced just before `\ref{lem:littlewood-argsetup}` (Lemma 27).

### Dependencies
**Depends on:** `argZeta`.
**Used by:** `littlewood_argsetup`, `littlewoodshort`, `littlewoodshort_tight`. -/
noncomputable def deltaArgZeta (T a b : ℝ) : ℝ :=
  argZeta (b + T * Complex.I) - argZeta (a + T * Complex.I)

/-- **`N(σ,T₁,T₂)`: the number of zeros `ρ` of `ζ` with `T₁ < Im ρ ≤ T₂` and `Re ρ > σ`, the
convention recalled in the introduction and used for the generic Littlewood identity
`\ref{eq:zerodensityintegral}` (Equation 13).**

### Summary of Proof
A definition, `Nsigma σ T₁ T₂ = Nrect T₁ T₂ (1-σ)`. It re-indexes the project's rectangle counter
`Nrect` into the `N(σ,T₁,T₂)` convention the tex uses for the generic Littlewood identity —
counting zeros with `Re ρ > σ` rather than `Re ρ > 1-α`.

### References
tex: the `N(σ,T₁,T₂)` convention recalled in the introduction and used in Equation
`\ref{eq:zerodensityintegral}` (Equation 13).

### Dependencies
**Depends on:** `Nrect`.
**Used by:** in `LittlewoodIdentity`: `Nsigma_eq_sum`, `left_edge_identity`,
`littlewood_identity_argZetaDef`, `littlewood_zero_density_integral`,
`simplelittlewoodzerodensity`. -/
noncomputable def Nsigma (σ T₁ T₂ : ℝ) : ℤ := Nrect T₁ T₂ (1 - σ)

/-! ### Three window integrals for `littlewood_mainterm`

`log` and `log log` are *concave*, so over the symmetric window `[T-h,T+h]` their integrals sit
**below** length-times-midpoint-value; the linear (tangent-line) part integrates to exactly zero by
symmetry. This is what makes `littlewood_mainterm`'s `O^*(4h/(T-h))` error achievable with no
constraint on `h` beyond `h < T`: the two main terms contribute *no* error at all, and the whole
`4h/(T-h)` budget is spent on the `4/|t|` tail of `JensenScaleConstants.zeta_piecewise_bound`
(which needs only `8h/(T-h)` before dividing by `2π`, i.e. `4/π ≈ 1.273` of the budgeted `4`). -/

/-- **Concavity of `log`, in integral form: `∫_{T-h}^{T+h} log t dt ≤ 2h·log T`.**

### Summary of Proof
Proved from the
tangent-line bound `log t ≤ log T + (t-T)/T` (`Real.log_le_sub_one_of_pos` at `t/T`), whose linear
part integrates to `0` over the symmetric window.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `integral_loglog_le_window`, `littlewood_mainterm`, `littlewood_mainterm_tight`, and
`Jensen.RectangularBounds.integral_window_bound`/`_tight`. -/
theorem integral_log_le_window {T h : ℝ} (hh : 0 ≤ h) (hTh : 0 < T - h) :
    (∫ t in (T - h)..(T + h), Real.log t) ≤ 2 * h * Real.log T := by
  have hT0 : (0:ℝ) < T := by linarith
  have hab : T - h ≤ T + h := by linarith
  have hkey : (∫ t in (T - h)..(T + h), Real.log t)
      ≤ ∫ t in (T - h)..(T + h), ((Real.log T - 1) + (1 / T) * t) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegral.intervalIntegrable_log'
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have hl := Real.log_le_sub_one_of_pos (show (0:ℝ) < t / T by positivity)
    rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hT0)] at hl
    have hd : t / T - 1 = (1 / T) * t - 1 := by field_simp
    rw [hd] at hl
    linarith
  have hcalc : (∫ t in (T - h)..(T + h), ((Real.log T - 1) + (1 / T) * t))
      = 2 * h * Real.log T := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    field_simp
    ring
  linarith [hcalc ▸ hkey]

/-- **Concavity of `log ∘ log`, same form: `∫_{T-h}^{T+h} log log t dt ≤ 2h·log log T`.**

### Summary of Proof
The
tangent-line bound for `log` at the point `log T` reduces this to `integral_log_le_window`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `integral_log_le_window`.
**Used by:** `littlewood_mainterm`, `littlewood_mainterm_tight`, and
`Jensen.RectangularBounds.integral_window_bound`/`_tight`. -/
theorem integral_loglog_le_window {T h : ℝ} (hh : 0 ≤ h) (hTh : 1 < T - h) :
    (∫ t in (T - h)..(T + h), Real.log (Real.log t)) ≤ 2 * h * Real.log (Real.log T) := by
  have hT1 : (1:ℝ) < T := by linarith
  have hab : T - h ≤ T + h := by linarith
  have hlT : 0 < Real.log T := Real.log_pos hT1
  have hcont : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.log (ContinuousOn.log continuousOn_id ?_) ?_
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : (1:ℝ) < t := by linarith [ht.1]
      simp only [id]; linarith
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have h1 : (1:ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (Real.log_pos h1)
  have hint : IntervalIntegrable (fun t : ℝ => Real.log (Real.log t)) MeasureTheory.volume
      (T - h) (T + h) := hcont.intervalIntegrable
  have hkey : (∫ t in (T - h)..(T + h), Real.log (Real.log t))
      ≤ ∫ t in (T - h)..(T + h),
          ((Real.log (Real.log T) - 1) + (1 / Real.log T) * Real.log t) := by
    apply intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_log'.const_mul _))
    intro t ht
    have h1 : (1:ℝ) < t := by linarith [ht.1]
    have hlt : 0 < Real.log t := Real.log_pos h1
    have hl := Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.log t / Real.log T by positivity)
    rw [Real.log_div (ne_of_gt hlt) (ne_of_gt hlT)] at hl
    have hd : Real.log t / Real.log T - 1 = (1 / Real.log T) * Real.log t - 1 := by field_simp
    rw [hd] at hl
    linarith
  have hcalc : (∫ t in (T - h)..(T + h),
      ((Real.log (Real.log T) - 1) + (1 / Real.log T) * Real.log t))
      ≤ 2 * h * Real.log (Real.log T) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_log'.const_mul _)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have hlog := integral_log_le_window hh (by linarith : (0:ℝ) < T - h)
    have hinv : (0:ℝ) < 1 / Real.log T := by positivity
    have hmul : (1 / Real.log T) * (∫ t in (T - h)..(T + h), Real.log t)
        ≤ (1 / Real.log T) * (2 * h * Real.log T) :=
      mul_le_mul_of_nonneg_left hlog hinv.le
    have he : (1 / Real.log T) * (2 * h * Real.log T) = 2 * h := by field_simp
    rw [he] at hmul
    simp only [smul_eq_mul]
    nlinarith
  linarith

/-- **The `4/|t|` tail of `JensenScaleConstants.zeta_piecewise_bound`, integrated over the window:
`∫_{T-h}^{T+h} 4/t dt = 4 log((T+h)/(T-h)) < 8h/(T-h)`, by the *strict* form `log x < x - 1`
(`Real.log_lt_sub_one_of_pos`, applicable since `(T+h)/(T-h) ≠ 1` when `h > 0`).**

### Summary of Proof
Strictness here is
what supplies the strict `<` in `littlewood_mainterm`, which is why that theorem needs `0 < h`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `littlewood_mainterm`. -/
theorem integral_inv_lt_window {T h : ℝ} (hh : 0 < h) (hTh : 0 < T - h) :
    (∫ t in (T - h)..(T + h), 4 / t) < 8 * h / (T - h) := by
  have hab : T - h ≤ T + h := by linarith
  have hTp : (0:ℝ) < T + h := by linarith
  have hcalc : (∫ t in (T - h)..(T + h), 4 / t)
      = 4 * (Real.log (T + h) - Real.log (T - h)) := by
    simp only [div_eq_mul_inv, mul_comm (4:ℝ)]
    rw [intervalIntegral.integral_mul_const, integral_inv_of_pos hTh hTp]
    rw [Real.log_div (ne_of_gt hTp) (ne_of_gt hTh)]
  rw [hcalc]
  have hne : (T + h) / (T - h) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq (ne_of_gt hTh)]
    intro hc; linarith
  have hl : Real.log (T + h) - Real.log (T - h) < 2 * h / (T - h) := by
    have hx := Real.log_lt_sub_one_of_pos (show (0:ℝ) < (T + h) / (T - h) by positivity) hne
    rw [Real.log_div (ne_of_gt hTp) (ne_of_gt hTh)] at hx
    have hd : (T + h) / (T - h) - 1 = 2 * h / (T - h) := by field_simp; ring
    rw [hd] at hx
    linarith
  have h8 : (4:ℝ) * (2 * h / (T - h)) = 8 * h / (T - h) := by ring
  linarith

/-- **The tight `2/t²+1158/(8t²log t)` tail of
`JensenScaleConstants.zeta_piecewise_bound_tight_simple`, integrated over the window.**

### Summary of Proof
The `2/t²`
piece has the exact antiderivative `-2/t` (`hasDerivAt_inv`), giving
`2/(T-h)-2/(T+h) = 4h/((T-h)(T+h)) < 4h/(T-h)²` **strictly** (since `T+h > T-h` as `h>0`) — this
is the only source of strictness in `littlewood_mainterm_tight` below, matching how
`integral_inv_lt_window`'s strict `log x < x-1` is the sole source of strictness in
`littlewood_mainterm`. The `1158/(8t²log t)` piece has no elementary antiderivative, so — as in
the source's own proof of `littlewood_mainterm`, which evaluates at the worst point — it is bounded
(non-strictly) by its value at the window's worst point `t=T-h` (the integrand is decreasing, since
`t²log t` is increasing for `t>1`), giving `≤ 2h · 1158/(8(T-h)²log(T-h))`.

### References
No tex counterpart.

### Dependencies
**Depends on:** none — pure calculus on the window. The tail it integrates is the one
`JensenScaleConstants.zeta_piecewise_bound_tight_simple` supplies at the call site.
**Used by:** `littlewood_mainterm_tight`, `RectangularBounds.integral_window_bound_tight`. -/
theorem integral_tight_tail_lt_window {T h : ℝ} (hh : 0 < h) (hTh : (1:ℝ) < T - h) :
    (∫ t in (T - h)..(T + h), (2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t)))
      < 4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h)) := by
  have hab : T - h ≤ T + h := by linarith
  have hTp : (0:ℝ) < T + h := by linarith
  have hTh0 : (0:ℝ) < T - h := by linarith
  have hcont1 : ContinuousOn (fun t : ℝ => 2 / t ^ 2) (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hcont2 : ContinuousOn (fun t : ℝ => 1158 / (8 * t ^ 2 * Real.log t))
      (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : (0:ℝ) < t := by linarith [ht.1]
      exact ne_of_gt ht0
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : (1:ℝ) < t := by linarith [ht.1]
    have hlt : (0:ℝ) < Real.log t := Real.log_pos ht1
    positivity
  have hi1 : IntervalIntegrable (fun t : ℝ => 2 / t ^ 2) MeasureTheory.volume (T - h) (T + h) :=
    hcont1.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => 1158 / (8 * t ^ 2 * Real.log t))
      MeasureTheory.volume (T - h) (T + h) := hcont2.intervalIntegrable
  rw [intervalIntegral.integral_add hi1 hi2]
  -- piece 1: exact antiderivative `-2/t`
  have hderiv : ∀ t ∈ Set.uIcc (T - h) (T + h),
      HasDerivAt (fun x : ℝ => -2 * x⁻¹) (2 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0pos : (0:ℝ) < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := ht0pos.ne'
    have hd := (hasDerivAt_inv ht0).const_mul (-2:ℝ)
    have heq : (-2:ℝ) * -(t ^ 2)⁻¹ = 2 / t ^ 2 := by rw [neg_mul_neg, ← div_eq_mul_inv]
    rwa [heq] at hd
  have heq1 : (∫ t in (T - h)..(T + h), 2 / t ^ 2)
      = (-2 * (T + h)⁻¹) - (-2 * (T - h)⁻¹) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi1
  have hbound1 : (∫ t in (T - h)..(T + h), 2 / t ^ 2) < 4 * h / (T - h) ^ 2 := by
    rw [heq1]
    have hkey : (-2 * (T + h)⁻¹) - (-2 * (T - h)⁻¹) = 4 * h / ((T - h) * (T + h)) := by
      field_simp; ring
    rw [hkey]
    rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < (T - h) * (T + h))
      (by positivity : (0:ℝ) < (T - h) ^ 2)]
    have hexpand : 4 * h * ((T - h) * (T + h)) - 4 * h * (T - h) ^ 2 = 8 * h ^ 2 * (T - h) := by
      ring
    nlinarith [hexpand, mul_pos (mul_pos hh hh) hTh0]
  -- piece 2: pointwise worst-point bound (integrand decreasing on `t > 1`)
  have hbound2 : (∫ t in (T - h)..(T + h), 1158 / (8 * t ^ 2 * Real.log t))
      ≤ 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h)) := by
    have hconst : (∫ _t in (T - h)..(T + h), 1158 / (8 * (T - h) ^ 2 * Real.log (T - h)))
        = 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hlogpos : (0:ℝ) < Real.log (T - h) := Real.log_pos hTh
      field_simp
      ring
    have hpt : ∀ t ∈ Set.Icc (T - h) (T + h),
        1158 / (8 * t ^ 2 * Real.log t) ≤ 1158 / (8 * (T - h) ^ 2 * Real.log (T - h)) := by
      intro t ht
      have ht1 : (1:ℝ) < t := by linarith [ht.1]
      have hlogTh : (0:ℝ) < Real.log (T - h) := Real.log_pos hTh
      have hlogt : (0:ℝ) < Real.log t := Real.log_pos ht1
      have hle : (T - h) ^ 2 * Real.log (T - h) ≤ t ^ 2 * Real.log t := by
        have h1 : (T - h) ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
        have h2 : Real.log (T - h) ≤ Real.log t := Real.log_le_log (by linarith) ht.1
        have h3 : (0:ℝ) ≤ (T - h) ^ 2 := by positivity
        exact mul_le_mul h1 h2 hlogTh.le (by positivity)
      have hd1 : (0:ℝ) < 8 * t ^ 2 * Real.log t := by positivity
      have hd2 : (0:ℝ) < 8 * (T - h) ^ 2 * Real.log (T - h) := by positivity
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith [hle]
    have := intervalIntegral.integral_mono_on hab hi2
      (a := T - h) (b := T + h) intervalIntegrable_const hpt
    rw [hconst] at this
    linarith [this]
  linarith [hbound1, hbound2]

/-- **Lemma `\ref{lemma:littlewood-mainterm}` (Lemma 25).** For `σ_k ≤ σ < σ_{k+1}`,
`(1/(2π))∫_{T-h}^{T+h} log|ζ(σ+it)|dt < h((m_kσ+b_k)/π log|T| + (m_k'σ+b_k')/π log log|T| +
(m_k''σ+b_k'')/π) + O^*(4h/(T-h))`.**

### Summary of Proof
(The source's displayed bound uses `log|t|`/`log log|t|` with `t` free; we read this as `T`, the
height parameter, matching every other occurrence of this bound.)

**Proof sketch (source).** "Follows immediately from the validity of the bound on `log|ζ(σ+it)|`" —
isolated here as its own named dependency, `JensenScaleConstants.zeta_piecewise_bound` (a genuine
consequence of `BackgroundZetaBounds.interpolated_bound_1b/2` and `zetalessthanhalf_upper`) —
integrated in `t` over `[T-h,T+h]`. `zeta_piecewise_bound` needs `10¹²<|t|`, which is why this
theorem needs `10¹²<T-h` (not merely `h<T`) to legitimately invoke it throughout the window.

**The stated `O^*(4h/(T-h))` error is achievable with no extra hypothesis bounding `h` away from
`T`.** The key fact: `∫_{T-h}^{T+h}\log t\,dt - 2h\log T` is identically **negative** — `\log` is
concave, so a symmetric-window integral always sits *below* the midpoint value times the length —
so it never has to be absorbed into the error at all; it only helps the upper bound. (Numerically,
at `T=10^{12}`: `-333` at `h=10^{9}`, `-3.5\cdot10^{11}` at `h=9\cdot10^{11}` — negative however
large `h` is.) Ditto `\log\log t`, concave on `t>1`. So there is no `O(h^2/(T-h))`, no
`O(h^3/T^2)`, and no extra hypothesis bounding `h` away from `T`.

**The proof** (the three calculus steps are `integral_log_le_window`,
`integral_loglog_le_window`, `integral_inv_lt_window` above). Integrate
`JensenScaleConstants.zeta_piecewise_bound`,
`\log\|\zeta(\sigma+it)\| \leq A\log|t| + B\log\log|t| + C + 4/|t|`, over `[T-h,T+h]` (where
`t>0`, so `|t|=t`), and bound each piece:
* `A\int\log t\,dt \leq 2hA\log T` — the tangent-line bound `\log t \leq \log T + (t-T)/T`
  (`Real.log_le_sub_one_of_pos` at `t/T`), whose linear part integrates to *exactly zero* over the
  symmetric window. Needs `A \geq 0`, supplied by `JensenScaleConstants.chord_vCoeff_nonneg`.
* `B\int\log\log t\,dt \leq 2hB\log\log T` — the same tangent-line bound applied to `\log` at the
  point `\log T`, which reduces to the previous bullet. Here `B = 1` exactly (`vCoeffP` is the
  constant function `1`).
* `\int 4/t\,dt = 4\log\frac{T+h}{T-h} < 8h/(T-h)`, by the *strict* `\log x < x-1`
  (`Real.log_lt_sub_one_of_pos`, valid since `(T+h)/(T-h) \neq 1` when `h>0`). **This strictness is
  the only source of the theorem's strict `<`**, which is why `0 < h` is required.

Dividing by `2\pi` gives error exactly `4h/(\pi(T-h))`, so the conclusion is stated with that
sharper constant rather than the source's `4h/(T-h)` (which it implies, `4/\pi \approx 1.273`).

**Two hypotheses beyond the bare `h<T`.** (i) `0 < h`, for the strict `<` (at `h=0` both sides are
`0`), matching `ZerosInShortIntervals.tex` exactly. (ii) `10^{12} < T-h`: this
"simple" version's own threshold, chosen (rather than `littlewood_mainterm_tight`'s own, much
sharper `12`) purely so that `zeta_piecewise_bound` (which requires `10^{12}<|t|`) applies across
the whole window using this file's other `10^{12}`-threshold results.

**Interval integrability of `t \mapsto \log\|\zeta(\sigma+it)\|`** is Mathlib's
`MeromorphicOn.intervalIntegrable_log_norm`. The integrand is `-\infty` at each zero of `\zeta` on
the line `Re s = \sigma` — note the singularities here are `\zeta`'s *zeros*, not its pole at
`s=1`, which `\sigma < 1` (`JensenScaleConstants.sigma_lt_one`) keeps us away from — but
`\log\|f\|` is interval-integrable for any real-meromorphic `f`, and `t \mapsto \zeta(\sigma+it)`
is even real-analytic here.

**The comparison of integrands is made almost everywhere, not pointwise.**
`zeta_piecewise_bound` carries the hypothesis `\zeta(1-\sigma+it) \neq 0`, which Lean needs
because `Real.log \|0\|` is the finite junk value `0` where the tex writes `-\infty`. The
hypothesis fails only at the ordinates of the zeros of `\zeta` on the mirror line
`Re s = 1-\sigma`; those form a discrete, hence null, set (`ae_zeta_vline_ne_zero`), so
`intervalIntegral.integral_mono_ae_restrict` gives the same integral inequality. This is why no
non-vanishing hypothesis appears in the statement, and none reaches `littlewoodshort`.

### References
tex: `\ref{lemma:littlewood-mainterm}` (Lemma 25).

### Dependencies
**Depends on:** `ae_zeta_vline_ne_zero`, `bCoeff`, `bCoeffP`, `bCoeffPP`, `chord_vCoeff_nonneg`,
`integral_inv_lt_window`, `integral_log_le_window`, `integral_loglog_le_window`, `mCoeff`,
`mCoeffP`, `mCoeffPP`, `sigma_lt_one`, `vCoeffP`, `zeta_piecewise_bound`.
**Used by:** `littlewoodshort`. -/
theorem littlewood_mainterm {k : ℤ} {σ T h : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ < sigma (k + 1))
    (hh : 0 < h) (hTh : (10 : ℝ) ^ (12 : ℕ) < T - h) :
    (1 / (2 * Real.pi)) * ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < h * ((mCoeff k * σ + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * σ + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * σ + bCoeffPP k) / Real.pi)
          + 4 * h / (Real.pi * (T - h)) := by
  have hh0 : (0:ℝ) ≤ h := hh.le
  have h1e12 : (1:ℝ) < (10:ℝ) ^ (12:ℕ) := by norm_num
  have hTh1 : (1:ℝ) < T - h := by linarith
  have hTh0 : (0:ℝ) < T - h := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) < T := by linarith
  have habsT : |T| = T := abs_of_pos hT0
  have hab : T - h ≤ T + h := by linarith
  set A : ℝ := mCoeff k * σ + bCoeff k with hA_def
  set B : ℝ := mCoeffP k * σ + bCoeffP k with hB_def
  set C : ℝ := mCoeffPP k * σ + bCoeffPP k with hC_def
  -- `B = 1` exactly: `vCoeffP` is the constant function `1`, so its chord is too.
  have hB1 : B = 1 := by
    rw [hB_def]; simp [mCoeffP, bCoeffP, vCoeffP]
  -- The `log|t|` coefficient is nonnegative — needed to use `log`'s concavity in the favourable
  -- direction. `A` is the chord between `vCoeff k` and `vCoeff (k+1)`, both nonnegative.
  have hA0 : 0 ≤ A := chord_vCoeff_nonneg hσ hσ'.le
  -- Interval integrability of `log‖ζ(σ+it)‖`. The integrand is `-∞` at each zero of `ζ` on the
  -- line `Re s = σ`, but integrably so; this is exactly Mathlib's
  -- `MeromorphicOn.intervalIntegrable_log_norm`, applied to the real-meromorphic (indeed
  -- real-analytic, since `σ < 1` keeps us off `ζ`'s pole at `s = 1`) function `t ↦ ζ(σ+it)`.
  have hσ1 : σ < 1 := lt_trans hσ' (sigma_lt_one (k + 1))
  have hZint : IntervalIntegrable (fun t : ℝ => Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      MeasureTheory.volume (T - h) (T + h) := by
    have hmero : MeromorphicOn (fun t : ℝ => riemannZeta (σ + t * Complex.I))
        (Set.uIcc (T - h) (T + h)) := by
      intro t _
      apply AnalyticAt.meromorphicAt
      have hne : ((σ : ℂ) + t * Complex.I) ≠ 1 := by
        intro hc
        have hre := congrArg Complex.re hc
        simp at hre
        linarith
      have hzC : AnalyticAt ℂ riemannZeta ((σ : ℂ) + t * Complex.I) :=
        differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton _ (by simpa using hne)
      have hz : AnalyticAt ℝ riemannZeta ((σ : ℂ) + t * Complex.I) := hzC.restrictScalars
      have haff : AnalyticAt ℝ (fun t : ℝ => (σ : ℂ) + t * Complex.I) t := by
        apply AnalyticAt.add analyticAt_const
        apply AnalyticAt.mul _ analyticAt_const
        exact Complex.ofRealCLM.analyticAt t
      exact AnalyticAt.comp (g := riemannZeta) hz haff
    exact hmero.intervalIntegrable_log_norm
  -- continuity/integrability of the three majorant pieces
  have hcontLL : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.log (ContinuousOn.log continuousOn_id ?_) ?_
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : (1:ℝ) < t := by linarith [ht.1]
      simp only [id]; linarith
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have h1 : (1:ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (Real.log_pos h1)
  have hcontInv : ContinuousOn (fun t : ℝ => 4 / t) (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [id]
    have : (1:ℝ) < t := by linarith [ht.1]
    linarith
  have hi1 :
      IntervalIntegrable (fun t : ℝ => A * Real.log t) MeasureTheory.volume (T - h) (T + h) :=
    intervalIntegral.intervalIntegrable_log'.const_mul A
  have hi2 : IntervalIntegrable (fun t : ℝ => B * Real.log (Real.log t)) MeasureTheory.volume
      (T - h) (T + h) := hcontLL.intervalIntegrable.const_mul B
  have hi3 : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume (T - h) (T + h) :=
    intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun t : ℝ => 4 / t) MeasureTheory.volume (T - h) (T + h) :=
    hcontInv.intervalIntegrable
  -- Pointwise majorant from `zeta_piecewise_bound` (on the window `t > 0`, so `|t| = t`).  Its
  -- reflection hypothesis `ζ(1-σ+it) ≠ 0` fails exactly at the ordinates of the zeros of `ζ` on
  -- the mirror line `Re s = 1-σ`, a discrete — hence null — set (`ae_zeta_vline_ne_zero`), so the
  -- comparison of integrands is made almost everywhere rather than pointwise.
  have hmono : (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      ≤ ∫ t in (T - h)..(T + h),
          (A * Real.log t + B * Real.log (Real.log t) + C + 4 / t) := by
    refine intervalIntegral.integral_mono_ae_restrict hab hZint
      (((hi1.add hi2).add hi3).add hi4) ?_
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [ae_zeta_vline_ne_zero σ] with t hne ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have htabs : |t| = t := abs_of_pos ht0
    have hpt := zeta_piecewise_bound hσ hσ' (t := t) (by rw [htabs]; linarith [ht.1])
      (by rw [htabs]; exact hne)
    rw [htabs] at hpt
    exact hpt
  -- split the majorant integral and bound each piece
  have hsplit : (∫ t in (T - h)..(T + h),
      (A * Real.log t + B * Real.log (Real.log t) + C + 4 / t))
      = A * (∫ t in (T - h)..(T + h), Real.log t)
        + B * (∫ t in (T - h)..(T + h), Real.log (Real.log t))
        + (2 * h) * C
        + (∫ t in (T - h)..(T + h), 4 / t) := by
    rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hlog := integral_log_le_window hh0 hTh0
  have hloglog := integral_loglog_le_window hh0 hTh1
  have hinv := integral_inv_lt_window hh hTh0
  have hb1 : A * (∫ t in (T - h)..(T + h), Real.log t) ≤ A * (2 * h * Real.log T) :=
    mul_le_mul_of_nonneg_left hlog hA0
  have hb2 : B * (∫ t in (T - h)..(T + h), Real.log (Real.log t))
      ≤ B * (2 * h * Real.log (Real.log T)) := by
    rw [hB1]; simpa using hloglog
  have hchain : (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      < A * (2 * h * Real.log T) + B * (2 * h * Real.log (Real.log T)) + (2 * h) * C
        + 8 * h / (T - h) := by
    rw [hsplit] at hmono; linarith
  -- divide by `2π`: the tail contributes exactly `4h/(π(T-h))`, which is the stated error
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hdiv : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hchain hdiv
  have hrw : (1 / (2 * Real.pi)) * (A * (2 * h * Real.log T)
      + B * (2 * h * Real.log (Real.log T)) + (2 * h) * C + 8 * h / (T - h))
      = h * (A / Real.pi * Real.log T + B / Real.pi * Real.log (Real.log T) + C / Real.pi)
        + 4 * h / (Real.pi * (T - h)) := by
    field_simp
    ring
  rw [hrw] at hscaled
  rw [habsT]
  linarith

/-- **Lemma `\ref{lemma:littlewood-mainterm}` (Lemma 25), tight version — this is the one that
matches the current tex.** Uses `JensenScaleConstants.zeta_piecewise_bound_tight_simple`
(Proposition `\ref{prop:interpolation}` (Proposition 35)'s genuinely tight `O(1/t²)` bound,
uniformly collapsed to the constant `1158`) in place of `littlewood_mainterm` above's
`zeta_piecewise_bound` (`O(1/t)`).

### Summary of Proof
**Proof (tex).** Lemma 25's own proof is one line — "this follows immediately from the validity of
the bound on `log|ζ(σ+it)|`" — with the remark that to get the stated `O^*` term one integrates the
`log|t|` and `log log|t|` terms *together with* Proposition 35's error terms, rather than taking the
naive bound, and then Taylor-expands in `h/t`.

**Lean proof.** Exactly that: integrate the pointwise majorant over `[T-h,T+h]` and bound each
piece (`integral_log_le_window`, `integral_loglog_le_window` unchanged from the non-tight version;
`integral_tight_tail_lt_window` in place of `integral_inv_lt_window`), giving a genuinely
`O(h/(T-h)²)` error — a full power of `T-h` sharper than `littlewood_mainterm`'s `O(h/(T-h))`, and
matching the tex's printed `O^*(h/(π(T-h)²)(2 + 1158/(8log(T-h))))` exactly.

**Threshold `12 < T-h`**, matching `zeta_piecewise_bound_tight_simple`'s own `t > 10` with
comfortable margin, and matching the tex's Lemma 25, which states `T-h>12`.

**Almost-everywhere comparison**, exactly as in `littlewood_mainterm`:
`zeta_piecewise_bound_tight_simple`'s reflection hypothesis `ζ(1-σ+it) ≠ 0` fails only on the
null set of ordinates of zeros on the mirror line, so `ae_zeta_vline_ne_zero` plus
`intervalIntegral.integral_mono_ae_restrict` replaces the pointwise comparison and keeps the
hypothesis out of the statement.

### References
tex: `\ref{lemma:littlewood-mainterm}` (Lemma 25), `\ref{prop:interpolation}` (Proposition 35).

### Dependencies
**Depends on:** `ae_zeta_vline_ne_zero`, `zeta_piecewise_bound_tight_simple`,
`integral_log_le_window`, `integral_loglog_le_window`, `integral_tight_tail_lt_window`,
`chord_vCoeff_nonneg`, `sigma_lt_one`, `mCoeff`, `bCoeff`, `mCoeffP`, `bCoeffP`, `vCoeffP`,
`mCoeffPP`, `bCoeffPP`.
**Used by:** `LittlewoodShort.littlewoodshort_tight`. -/
theorem littlewood_mainterm_tight {k : ℤ} {σ T h : ℝ} (hσ : sigma k ≤ σ) (hσ' : σ < sigma (k + 1))
    (hh : 0 < h) (hTh : (12 : ℝ) < T - h) :
    (1 / (2 * Real.pi)) * ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖
      < h * ((mCoeff k * σ + bCoeff k) / Real.pi * Real.log |T|
              + (mCoeffP k * σ + bCoeffP k) / Real.pi * Real.log (Real.log |T|)
              + (mCoeffPP k * σ + bCoeffPP k) / Real.pi)
          + (2 * h / (Real.pi * (T - h) ^ 2)
              + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h))) := by
  have hh0 : (0:ℝ) ≤ h := hh.le
  have hTh10 : (10:ℝ) < T - h := by linarith
  have hTh1 : (1:ℝ) < T - h := by linarith
  have hTh0 : (0:ℝ) < T - h := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) < T := by linarith
  have habsT : |T| = T := abs_of_pos hT0
  have hab : T - h ≤ T + h := by linarith
  set A : ℝ := mCoeff k * σ + bCoeff k with hA_def
  set B : ℝ := mCoeffP k * σ + bCoeffP k with hB_def
  set C : ℝ := mCoeffPP k * σ + bCoeffPP k with hC_def
  have hB1 : B = 1 := by
    rw [hB_def]; simp [mCoeffP, bCoeffP, vCoeffP]
  have hA0 : 0 ≤ A := chord_vCoeff_nonneg hσ hσ'.le
  have hσ1 : σ < 1 := lt_trans hσ' (sigma_lt_one (k + 1))
  have hZint : IntervalIntegrable (fun t : ℝ => Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      MeasureTheory.volume (T - h) (T + h) := by
    have hmero : MeromorphicOn (fun t : ℝ => riemannZeta (σ + t * Complex.I))
        (Set.uIcc (T - h) (T + h)) := by
      intro t _
      apply AnalyticAt.meromorphicAt
      have hne : ((σ : ℂ) + t * Complex.I) ≠ 1 := by
        intro hc
        have hre := congrArg Complex.re hc
        simp at hre
        linarith
      have hzC : AnalyticAt ℂ riemannZeta ((σ : ℂ) + t * Complex.I) :=
        differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton _ (by simpa using hne)
      have hz : AnalyticAt ℝ riemannZeta ((σ : ℂ) + t * Complex.I) := hzC.restrictScalars
      have haff : AnalyticAt ℝ (fun t : ℝ => (σ : ℂ) + t * Complex.I) t := by
        apply AnalyticAt.add analyticAt_const
        apply AnalyticAt.mul _ analyticAt_const
        exact Complex.ofRealCLM.analyticAt t
      exact AnalyticAt.comp (g := riemannZeta) hz haff
    exact hmero.intervalIntegrable_log_norm
  have hcontLL : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.log (ContinuousOn.log continuousOn_id ?_) ?_
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : (1:ℝ) < t := by linarith [ht.1]
      simp only [id]; linarith
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have h1 : (1:ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (Real.log_pos h1)
  have hcontTail : ContinuousOn (fun t : ℝ => 2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t))
      (Set.uIcc (T - h) (T + h)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
    · apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.mul (by fun_prop)
        apply ContinuousOn.log (by fun_prop)
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht0 : (0:ℝ) < t := by linarith [ht.1]
        exact ne_of_gt ht0
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht1 : (1:ℝ) < t := by linarith [ht.1]
      have : (0:ℝ) < Real.log t := Real.log_pos ht1
      positivity
  have hi1 :
      IntervalIntegrable (fun t : ℝ => A * Real.log t) MeasureTheory.volume (T - h) (T + h) :=
    intervalIntegral.intervalIntegrable_log'.const_mul A
  have hi2 : IntervalIntegrable (fun t : ℝ => B * Real.log (Real.log t)) MeasureTheory.volume
      (T - h) (T + h) := hcontLL.intervalIntegrable.const_mul B
  have hi3 : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume (T - h) (T + h) :=
    intervalIntegrable_const
  have hi4 : IntervalIntegrable (fun t : ℝ => 2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t))
      MeasureTheory.volume (T - h) (T + h) := hcontTail.intervalIntegrable
  have hmono : (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      ≤ ∫ t in (T - h)..(T + h),
          (A * Real.log t + B * Real.log (Real.log t) + C
            + (2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t))) := by
    refine intervalIntegral.integral_mono_ae_restrict hab hZint
      (((hi1.add hi2).add hi3).add hi4) ?_
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [ae_zeta_vline_ne_zero σ] with t hne ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have htabs : |t| = t := abs_of_pos ht0
    have hpt := zeta_piecewise_bound_tight_simple hσ hσ' (t := t)
      (by rw [htabs]; linarith [ht.1]) (by rw [htabs]; exact hne)
    rw [htabs] at hpt
    exact hpt
  have hsplit : (∫ t in (T - h)..(T + h),
      (A * Real.log t + B * Real.log (Real.log t) + C
        + (2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t))))
      = A * (∫ t in (T - h)..(T + h), Real.log t)
        + B * (∫ t in (T - h)..(T + h), Real.log (Real.log t))
        + (2 * h) * C
        + (∫ t in (T - h)..(T + h), (2 / t ^ 2 + 1158 / (8 * t ^ 2 * Real.log t))) := by
    rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hlog := integral_log_le_window hh0 hTh0
  have hloglog := integral_loglog_le_window hh0 hTh1
  have htail := integral_tight_tail_lt_window hh hTh1
  have hb1 : A * (∫ t in (T - h)..(T + h), Real.log t) ≤ A * (2 * h * Real.log T) :=
    mul_le_mul_of_nonneg_left hlog hA0
  have hb2 : B * (∫ t in (T - h)..(T + h), Real.log (Real.log t))
      ≤ B * (2 * h * Real.log (Real.log T)) := by
    rw [hB1]; simpa using hloglog
  have hchain : (∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      < A * (2 * h * Real.log T) + B * (2 * h * Real.log (Real.log T)) + (2 * h) * C
        + (4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h))) := by
    rw [hsplit] at hmono; linarith
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hdiv : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hchain hdiv
  have hrw : (1 / (2 * Real.pi)) * (A * (2 * h * Real.log T)
      + B * (2 * h * Real.log (Real.log T)) + (2 * h) * C
      + (4 * h / (T - h) ^ 2 + 1158 * h / (4 * (T - h) ^ 2 * Real.log (T - h))))
      = h * (A / Real.pi * Real.log T + B / Real.pi * Real.log (Real.log T) + C / Real.pi)
        + (2 * h / (Real.pi * (T - h) ^ 2)
            + 1158 * h / (8 * Real.pi * (T - h) ^ 2 * Real.log (T - h))) := by
    have hlogpos : (0:ℝ) < Real.log (T - h) := Real.log_pos hTh1
    field_simp
    ring
  rw [hrw] at hscaled
  rw [habsT]
  linarith

/-- **`littlewood_outerlog` for `σ > 1` strictly, with `≤` in place of the source's `<`.**
`-(1/(2π))∫_{T-h}^{T+h} log‖ζ(σ+it)‖dt ≤ Φ(σ)/π`.

### Summary of Proof
Built from the FTC/domination machinery of `Definitions.lean` (`Phi_im_hasDerivAt`,
`Phi_norm_le`): `x ↦ Im(Φ(σ+xi))` has derivative `-log‖ζ(σ+xi)‖` everywhere — no
`ε`-regularization is needed, unlike `RectangularBounds.outside2`, because `σ > 1` strictly here —
so FTC gives `∫_{T-h}^{T+h} log‖ζ(σ+it)‖dt = Im(Φ(σ+i(T-h))) - Im(Φ(σ+i(T+h)))`, and each
`Im(Φ(σ+ix))` is bounded in absolute value by `‖Φ(σ+ix)‖ ≤ Φ(σ).re` (`Phi_norm_le`, same real part
`σ` throughout).

### Lean Notes
`σ > 1` strictly is the only regime any call site needs (`LittlewoodShort.A6` uses `σ = 1+ηr`
with `η,r>0`); the boundary case `σ = 1` is supplied separately by `littlewood_outerlog_le`,
which takes an `ε → 0⁺` limit, since `Phi_hasDerivAt` holds only for `Re s > 1` strictly.

The conclusion is `≤`, not the source's `<`: the triangle-inequality step `|Im Φ(s)| ≤ ‖Φ(s)‖`
gives only `≤`, and promoting it would need a separate non-degeneracy argument ruling out the
bound being exactly tight at both endpoints simultaneously.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_im_hasDerivAt`, `Phi_norm_le`.
**Used by:** `littlewood_outerlog_le`. -/
theorem littlewood_outerlog_of_one_lt {σ T h : ℝ} (hσ : 1 < σ) :
    -((1 / (2 * Real.pi)) * ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      ≤ (Phi σ).re / Real.pi := by
  have hne : ∀ x : ℝ, (σ : ℂ) + (x : ℂ) * Complex.I ≠ 1 := by
    intro x heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have haffine_cont : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hzcont : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + t * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (differentiableAt_riemannZeta (hne t)).continuousAt
      haffine_cont.continuousAt
  have hnz : ∀ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≠ 0 := fun t =>
    norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))
  have hlogcont : Continuous (fun t : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖) :=
    hzcont.norm.log hnz
  have hderiv : ∀ x ∈ Set.uIcc (T - h) (T + h),
      HasDerivAt (fun x : ℝ => (Phi ((σ : ℂ) + x * Complex.I)).im)
        (-Real.log ‖riemannZeta ((σ : ℂ) + x * Complex.I)‖) x :=
    fun x _ => Phi_im_hasDerivAt hσ x
  have hint : IntervalIntegrable (fun x : ℝ => -Real.log ‖riemannZeta ((σ : ℂ) + x * Complex.I)‖)
      MeasureTheory.volume (T - h) (T + h) := hlogcont.neg.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hFTC
  have hbound : ∀ x : ℝ, |(Phi ((σ : ℂ) + x * Complex.I)).im| ≤ (Phi σ).re := by
    intro x
    have h1 : |(Phi ((σ : ℂ) + x * Complex.I)).im| ≤ ‖Phi ((σ : ℂ) + x * Complex.I)‖ :=
      Complex.abs_im_le_norm _
    have h2 : ‖Phi ((σ : ℂ) + x * Complex.I)‖ ≤ (Phi (((σ : ℂ) + x * Complex.I).re : ℂ)).re :=
      Phi_norm_le (by simpa using hσ)
    have h3 : (((σ : ℂ) + x * Complex.I).re : ℂ) = (σ : ℂ) := by
      simp
    rw [h3] at h2
    linarith
  have hb1 : (Phi ((σ : ℂ) + ((T + h : ℝ) : ℂ) * Complex.I)).im ≤ (Phi σ).re := by
    simpa using (abs_le.mp (hbound (T + h))).2
  have hb2 : -(Phi σ).re ≤ (Phi ((σ : ℂ) + ((T - h : ℝ) : ℂ) * Complex.I)).im := by
    simpa using (abs_le.mp (hbound (T - h))).1
  have hcore : (Phi ((σ : ℂ) + ((T + h : ℝ) : ℂ) * Complex.I)).im
      - (Phi ((σ : ℂ) + ((T - h : ℝ) : ℂ) * Complex.I)).im ≤ 2 * (Phi σ).re := by linarith
  have hkey : -((1 / (2 * Real.pi)) *
        ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖)
      = (1 / (2 * Real.pi)) *
        ((Phi ((σ : ℂ) + ((T + h : ℝ) : ℂ) * Complex.I)).im
          - (Phi ((σ : ℂ) + ((T - h : ℝ) : ℂ) * Complex.I)).im) := by
    rw [← hFTC]; ring
  rw [hkey, show (Phi σ).re / Real.pi = (1 / (2 * Real.pi)) * (2 * (Phi σ).re) by
    field_simp]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

/-- **`littlewood_outerlog` extended to `σ = 1`, under the extra hypotheses `0 ≤ h`, `h < T`**
(so the rectangle `{s : 1 ≤ Re s} × [T-h,T+h]i` stays away from `ζ`'s pole at `s = 1`, which lies
on the line `Re s = 1` at height `0`).**

### Summary of Proof
Follows `littlewood_outerlog_of_one_lt` (valid for `σ > 1`)
plus the `ε → 0⁺` limit sketched in that theorem's docstring: continuity of the integral in `σ` at
`σ = 1` from the right (via `intervalIntegral.continuousWithinAt_of_dominated_interval`, using that
`ζ` is holomorphic and non-vanishing — `riemannZeta_ne_zero_of_one_le_re` — on a neighbourhood of
the compact rectangle `[1,2] × [T-h,T+h]`, which stays away from `ζ`'s pole since `T - h > 0`) and
continuity of `Phi` at `σ = 1` (`Definitions.Phi_continuousOn_closedHalfPlane`); this is exactly
`RectangularBounds.outside2_le`'s argument, specialized to a single fixed `h` (no `α̂_r` widening)
and the negated sign convention used here. `littlewood_outerlog` below states exactly this (with
the matching `≤`). Dropping `0 ≤ h`/`h < T` for a fully general version would be a genuinely
different statement — and generally false without some such hypothesis: if `0 ∈ [T-h,T+h]` the
rectangle meets `ζ`'s pole and the `σ → 1⁺` limit argument breaks down, though the inequality may
still happen to hold. The only call site (`LittlewoodShort.A6`) never needs it, since it always
has `σ = 1 + ηr` with `η, r > 0` strictly and `0 ≤ h < T`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `Phi`, `Phi_continuousOn_closedHalfPlane`, `littlewood_outerlog_of_one_lt`.
**Used by:** `littlewood_outerlog`. -/
theorem littlewood_outerlog_le {σ T h : ℝ} (hh : 0 ≤ h) (hT : h < T) (hσ : 1 ≤ σ) :
    -((1 / (2 * Real.pi)) * ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      ≤ (Phi σ).re / Real.pi := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [← heq]
    have hTh' : (0:ℝ) < T - h := by linarith
    have hle : T - h ≤ T + h := by linarith
    set F : ℝ → ℝ := fun σ => -((1 / (2 * Real.pi)) *
        ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖) with hF_def
    have hcontpt : ∀ p : ℝ × ℝ, 1 ≤ p.1 → T - h ≤ p.2 → p.2 ≤ T + h →
        ContinuousAt (fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I)) p := by
      intro p hp1 hp2 hp3
      have hne : (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ≠ 1 := by
        intro heq'
        have him := congrArg Complex.im heq'
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
          Complex.ofReal_re, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
        linarith
      have haff : ContinuousAt (fun q : ℝ × ℝ => (q.1:ℂ) + (q.2:ℂ) * Complex.I) p := by fun_prop
      have hcomp := ContinuousAt.comp
        (f := fun q : ℝ × ℝ => (q.1:ℂ) + (q.2:ℂ) * Complex.I) (x := p)
        (differentiableAt_riemannZeta hne).continuousAt haff
      exact hcomp
    have hcontpt1 : ∀ σ t : ℝ, 1 ≤ σ → T - h ≤ t → t ≤ T + h →
        ContinuousAt (fun s : ℝ => riemannZeta ((σ:ℂ) + (s:ℂ) * Complex.I)) t := by
      intro σ t h1 h2 h3
      have hinj : ContinuousAt (fun s : ℝ => ((σ, s) : ℝ × ℝ)) t :=
        continuousAt_const.prodMk continuousAt_id
      have hcomp := ContinuousAt.comp
        (g := fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I))
        (f := fun s : ℝ => ((σ, s) : ℝ × ℝ)) (x := t)
        (hcontpt (σ, t) h1 h2 h3) hinj
      exact hcomp
    have hcontpt2 : ∀ σ t : ℝ, 1 ≤ σ → T - h ≤ t → t ≤ T + h →
        ContinuousAt (fun s : ℝ => riemannZeta ((s:ℂ) + (t:ℂ) * Complex.I)) σ := by
      intro σ t h1 h2 h3
      have hinj : ContinuousAt (fun s : ℝ => ((s, t) : ℝ × ℝ)) σ :=
        continuousAt_id.prodMk continuousAt_const
      have hcomp := ContinuousAt.comp
        (g := fun q : ℝ × ℝ => riemannZeta (q.1 + q.2 * Complex.I))
        (f := fun s : ℝ => ((s, t) : ℝ × ℝ)) (x := σ)
        (hcontpt (σ, t) h1 h2 h3) hinj
      exact hcomp
    have hjointcont : ContinuousOn (fun p : ℝ × ℝ => Real.log ‖riemannZeta (p.1 + p.2 * Complex.I)‖)
        (Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h) (T + h)) := by
      apply ContinuousOn.log
      · intro p hp
        simp only [Set.mem_prod, Set.mem_Icc] at hp
        exact (hcontpt p hp.1.1 hp.2.1 hp.2.2).continuousWithinAt.norm
      · intro p hp
        simp only [Set.mem_prod, Set.mem_Icc] at hp
        exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hp.1.1))
    have hcompact : IsCompact (Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h) (T + h)) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hjointcont.norm
    have hCbound : ∀ p ∈ Set.Icc (1:ℝ) 2 ×ˢ Set.Icc (T - h) (T + h),
        ‖Real.log ‖riemannZeta (p.1 + p.2 * Complex.I)‖‖ ≤ C :=
      fun p hp => hC (Set.mem_image_of_mem _ hp)
    have hs_mem : Set.Icc (1:ℝ) 2 ∈ nhdsWithin (1:ℝ) (Set.Ici 1) := by
      apply Filter.mem_of_superset
        (inter_mem_nhdsWithin (Set.Ici 1) (isOpen_Iio.mem_nhds (show (1:ℝ) < 2 by norm_num)))
      intro x hx
      exact ⟨hx.1, le_of_lt hx.2⟩
    have hIntCont : ContinuousWithinAt
        (fun σ : ℝ => ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
        (Set.Ici 1) 1 := by
      have hmeas : ∀ σ : ℝ, 1 ≤ σ →
          MeasureTheory.AEStronglyMeasurable
            (fun t : ℝ => Real.log ‖riemannZeta (σ + t * Complex.I)‖)
            (MeasureTheory.volume.restrict (Set.uIoc (T - h) (T + h))) := by
        intro σ hσ'
        apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
        apply ContinuousOn.mono _ Set.uIoc_subset_uIcc
        rw [Set.uIcc_of_le hle]
        intro t ht
        exact ((hcontpt1 σ t hσ' ht.1 ht.2).continuousWithinAt).norm.log
          (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hσ')))
      apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (F := fun (σ t : ℝ) => Real.log ‖riemannZeta (σ + t * Complex.I)‖) (bound := fun _ => C)
      · filter_upwards [hs_mem] with σ hσ' using hmeas σ hσ'.1
      · filter_upwards [hs_mem] with σ hσ'
        apply MeasureTheory.ae_of_all
        intro t htmem
        have ht' : t ∈ Set.Icc (T - h) (T + h) := by
          rw [← Set.uIcc_of_le hle]; exact Set.uIoc_subset_uIcc htmem
        rw [Real.norm_eq_abs]
        exact hCbound (σ, t) ⟨hσ', ht'⟩
      · exact intervalIntegrable_const
      · apply MeasureTheory.ae_of_all
        intro t ht
        have ht' : t ∈ Set.Icc (T - h) (T + h) := by
          rw [← Set.uIcc_of_le hle]; exact Set.uIoc_subset_uIcc ht
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.log
        · exact (hcontpt2 1 t le_rfl ht'.1 ht'.2).norm
        · exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simp))
    have hFcont : ContinuousWithinAt F (Set.Ici 1) 1 := by
      rw [hF_def]; exact (hIntCont.const_mul (1 / (2 * Real.pi))).neg
    have hFcont' : Filter.Tendsto F (nhdsWithin 1 (Set.Ici 1)) (nhds (F 1)) := hFcont
    have hGcont : Filter.Tendsto (fun σ : ℝ => (Phi (σ:ℂ)).re / Real.pi)
        (nhdsWithin 1 (Set.Ici 1)) (nhds ((Phi 1).re / Real.pi)) := by
      have hmapsto : Set.MapsTo (fun σ : ℝ => (σ:ℂ)) (Set.Ici (1:ℝ)) {s : ℂ | 1 ≤ s.re} :=
        fun x hx => by simpa using hx
      have hcompPhi : ContinuousOn (fun σ : ℝ => Phi (σ:ℂ)) (Set.Ici 1) :=
        Phi_continuousOn_closedHalfPlane.comp Complex.continuous_ofReal.continuousOn hmapsto
      have h1mem : (1:ℝ) ∈ Set.Ici (1:ℝ) := Set.mem_Ici.mpr le_rfl
      have h0 := (hcompPhi 1 h1mem).tendsto
      have h2 := (Complex.continuous_re.tendsto (Phi (1:ℂ))).comp h0
      simpa [Function.comp] using h2.div_const Real.pi
    have hle_eventually : ∀ᶠ σ in nhdsWithin (1:ℝ) (Set.Ioi 1),
        F σ ≤ (Phi (σ:ℂ)).re / Real.pi := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ' using littlewood_outerlog_of_one_lt hσ'
    have hmono : (nhdsWithin (1:ℝ) (Set.Ioi 1)) ≤ nhdsWithin (1:ℝ) (Set.Ici 1) :=
      nhdsWithin_mono 1 Set.Ioi_subset_Ici_self
    exact le_of_tendsto_of_tendsto (hFcont'.mono_left hmono) (hGcont.mono_left hmono) hle_eventually
  · exact littlewood_outerlog_of_one_lt hlt

/-- **Lemma `\ref{lemma:littlewood-outerlog}` (Lemma 26).** For `0 ≤ h < T` and `σ ≥ 1`,
`-(1/(2π))∫_{T-h}^{T+h} log|ζ(σ+it)|dt ≤ Φ(σ)/π`.

### Summary of Proof
**Proof (tex).** One line: "this follows from the fundamental theorem of calculus and the absolute
convergence of the series defining `Φ`", where `Φ` is the antiderivative of `log ζ` of Equation
`\ref{eq:phis}` (Equation 12).

**Lean proof.** FTC applied to `Φ` on the segment, then the triangle inequality
`|Im Φ(s)| ≤ ‖Φ(s)‖ ≤ Φ(Re s).re`. The `σ = 1` boundary case is handled separately by a limiting
argument (`littlewood_outerlog_of_one_lt` on `Ioi 1`, then `le_of_tendsto_of_tendsto`), since `Φ`'s
defining series converges only for `Re s > 1`.

Exactly the same situation as `RectangularBounds.outside2`: the source's proof only ever derives
`|Im Φ(s)| ≤ ‖Φ(s)‖ ≤ Φ(Re s).re` (a triangle-inequality fact, genuinely `≤`) at the two integration
endpoints via FTC — promoting to `<` would need a separate non-degeneracy argument (ruling out the
bound being exactly tight at both endpoints simultaneously), not given. The `0 ≤ h`, `h < T`
hypotheses keep `[T-h,T+h]` away from `ζ`'s pole at `s=1`, needed for the `σ=1` boundary case
(`h<T` alone, without `h≥0`, does not); both always hold for the half-width `h`/height `T` as used
throughout the source. This theorem is literally `littlewood_outerlog_le`
(`littlewood_outerlog_of_one_lt` for `σ>1` strictly, extended to `σ=1` by an `ε→0⁺` limit — see
that theorem's docstring), and covers this lemma's only use site (`LittlewoodShort.A6`, which
always has `σ = 1 + ηr` with `η, r > 0` strictly and `0 ≤ h < T`), so nothing downstream needs
either the strict form or the fully general (possibly pole-adjacent) hypotheses dropped here.

### References
tex: `\ref{lemma:littlewood-outerlog}` (Lemma 26), `\ref{eq:phis}` (Equation 12).

### Dependencies
**Depends on:** `Phi`, `littlewood_outerlog_le`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`, `rectangularjensen`,
`rectangularjensen_tight`. -/
theorem littlewood_outerlog {σ T h : ℝ} (hh : 0 ≤ h) (hT : h < T) (hσ : 1 ≤ σ) :
    -((1 / (2 * Real.pi)) * ∫ t in (T - h)..(T + h), Real.log ‖riemannZeta (σ + t * Complex.I)‖)
      ≤ (Phi σ).re / Real.pi :=
  littlewood_outerlog_le hh hT hσ

/-- **Lemma `\ref{lem:littlewood-argsetup}` (Lemma 27).** For `σ1 > 1` and `σ0 ≤ σ1`,
`|arg ζ(σ1+i(T+h)) - arg ζ(σ1+i(T-h))| ≤ 2 log ζ(σ1)`, and hence the difference of the two
`arg ζ` integrals in Equation `\ref{eq:simplelittlewoodzerodensity}` (Equation 14) is bounded in
terms of `Δ arg ζ` integrals.

### Summary of Proof
Hypotheses strengthened/added relative to the source's `σ1 ≥ 1`: `1 < σ1` strictly, since
`argZeta_abs_le` (like `argZeta_eq_im_G`) needs `Re s > 1` — the actual call site,
`LittlewoodShort.A6` with `σ1 = 1+ηr`, always has this; and `σ0 ≤ σ1`, needed below for the sign of
the `(σ1-σ0)*(...)` term (always holds at the call site, `σ0 = 1-r < 1 < σ1`). First claim
non-strict (`≤`, not `<`), matching `argZeta_abs_le`'s own non-strict form — see its docstring.

The two integrals here run `σ0..σ1`, matching `simplelittlewoodzerodensity`'s direction.

**Proof.** First claim: triangle inequality (`|a-b|≤|a|+|b|`) applied to `argZeta_abs_le` at both
`σ1+i(T+h)` and `σ1+i(T-h)`. Second claim: rewrite `argZeta(u+i(T±h))` as
`argZeta(σ1+i(T±h)) + deltaArgZeta (T±h) σ1 u` (definitional), integrate termwise over `u ∈
[σ0,σ1]` (the continuity hypotheses `hcont_p`/`hcont_m` give integrability), take the difference,
and bound the resulting `(σ1-σ0)*(argZeta(σ1+i(T+h))-argZeta(σ1+i(T-h)))` term via the first
claim (nonnegative `σ1-σ0`).

### Lean Notes
**`hcont_p`/`hcont_m`**: continuity of `u ↦ argZeta(u + i(T±h))` on `[σ0,σ1]`, which is what makes
the two `arg ζ` integrals exist. They are stated segment by segment rather than as global
continuity of `argZeta` because the tex's branch jumps by `2π` across zero ordinates and so is not
continuous on `ℂ`. On zero-free edges they hold by
`LittlewoodIdentity.argZetaDef_continuousOn_line'`, which is how the call sites
(`littlewoodshort`, `littlewoodshort_tight`) supply them from their `hzf_p`/`hzf_m`.

### References
tex: `\ref{lem:littlewood-argsetup}` (Lemma 27).

### Dependencies
**Depends on:** `argZeta`, `argZeta_abs_le`, `deltaArgZeta`.
**Used by:** `littlewoodshort`, `littlewoodshort_tight`. -/
theorem littlewood_argsetup {σ0 σ1 T h : ℝ} (hσ1 : 1 < σ1) (hσ0σ1 : σ0 ≤ σ1)
    (hcont_p : ContinuousOn (fun u : ℝ => argZeta (u + (T + h) * Complex.I)) (Set.Icc σ0 σ1))
    (hcont_m : ContinuousOn (fun u : ℝ => argZeta (u + (T - h) * Complex.I)) (Set.Icc σ0 σ1)) :
    |argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I)|
      ≤ 2 * Real.log ‖riemannZeta (σ1 : ℂ)‖
    ∧ (1 / (2 * Real.pi)) *
          ((∫ u in σ0..σ1, argZeta (u + (T + h) * Complex.I))
            - (∫ u in σ0..σ1, argZeta (u + (T - h) * Complex.I)))
        ≤ (σ1 - σ0) / Real.pi * Real.log ‖riemannZeta (σ1 : ℂ)‖
          + (1 / (2 * Real.pi)) * (∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u)
          - (1 / (2 * Real.pi)) * (∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u) := by
  have hb1 := argZeta_abs_le (σ := σ1) (τ := T + h) hσ1
  have hb2 := argZeta_abs_le (σ := σ1) (τ := T - h) hσ1
  have hclaim1 : |argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I)|
      ≤ 2 * Real.log ‖riemannZeta (σ1 : ℂ)‖ := by
    rw [abs_le]
    obtain ⟨h1a, h1b⟩ := abs_le.mp hb1
    obtain ⟨h2a, h2b⟩ := abs_le.mp hb2
    push_cast at h1a h1b h2a h2b ⊢
    constructor <;> linarith
  refine ⟨hclaim1, ?_⟩
  have hint1 : IntervalIntegrable (fun u : ℝ => argZeta (u + (T + h) * Complex.I))
      MeasureTheory.volume σ0 σ1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0σ1]
    exact hcont_p
  have hint2 : IntervalIntegrable (fun u : ℝ => argZeta (u + (T - h) * Complex.I))
      MeasureTheory.volume σ0 σ1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ0σ1]
    exact hcont_m
  have hintD1 : IntervalIntegrable (fun u : ℝ => deltaArgZeta (T + h) σ1 u)
      MeasureTheory.volume σ0 σ1 := by
    have heq : (fun u : ℝ => deltaArgZeta (T + h) σ1 u)
        = fun u : ℝ => argZeta (u + (T + h) * Complex.I) - argZeta (σ1 + (T + h) * Complex.I) := by
      funext u; unfold deltaArgZeta; push_cast; ring
    rw [heq]
    exact hint1.sub intervalIntegrable_const
  have hintD2 : IntervalIntegrable (fun u : ℝ => deltaArgZeta (T - h) σ1 u)
      MeasureTheory.volume σ0 σ1 := by
    have heq : (fun u : ℝ => deltaArgZeta (T - h) σ1 u)
        = fun u : ℝ => argZeta (u + (T - h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I) := by
      funext u; unfold deltaArgZeta; push_cast; ring
    rw [heq]
    exact hint2.sub intervalIntegrable_const
  have hpt1 : ∀ u : ℝ, argZeta (u + (T + h) * Complex.I)
      = argZeta (σ1 + (T + h) * Complex.I) + deltaArgZeta (T + h) σ1 u := by
    intro u; unfold deltaArgZeta; push_cast; ring
  have hpt2 : ∀ u : ℝ, argZeta (u + (T - h) * Complex.I)
      = argZeta (σ1 + (T - h) * Complex.I) + deltaArgZeta (T - h) σ1 u := by
    intro u; unfold deltaArgZeta; push_cast; ring
  have heq1 : (∫ u in σ0..σ1, argZeta (u + (T + h) * Complex.I))
      = (σ1 - σ0) * argZeta (σ1 + (T + h) * Complex.I)
        + ∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u := by
    calc (∫ u in σ0..σ1, argZeta (u + (T + h) * Complex.I))
        = ∫ u in σ0..σ1, (argZeta (σ1 + (T + h) * Complex.I) + deltaArgZeta (T + h) σ1 u) :=
          intervalIntegral.integral_congr (fun u _ => hpt1 u)
      _ = (∫ _u in σ0..σ1, argZeta (σ1 + (T + h) * Complex.I))
          + ∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u :=
          intervalIntegral.integral_add intervalIntegrable_const hintD1
      _ = (σ1 - σ0) * argZeta (σ1 + (T + h) * Complex.I)
          + ∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have heq2 : (∫ u in σ0..σ1, argZeta (u + (T - h) * Complex.I))
      = (σ1 - σ0) * argZeta (σ1 + (T - h) * Complex.I)
        + ∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u := by
    calc (∫ u in σ0..σ1, argZeta (u + (T - h) * Complex.I))
        = ∫ u in σ0..σ1, (argZeta (σ1 + (T - h) * Complex.I) + deltaArgZeta (T - h) σ1 u) :=
          intervalIntegral.integral_congr (fun u _ => hpt2 u)
      _ = (∫ _u in σ0..σ1, argZeta (σ1 + (T - h) * Complex.I))
          + ∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u :=
          intervalIntegral.integral_add intervalIntegrable_const hintD2
      _ = (σ1 - σ0) * argZeta (σ1 + (T - h) * Complex.I)
          + ∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hdiff : (∫ u in σ0..σ1, argZeta (u + (T + h) * Complex.I))
        - (∫ u in σ0..σ1, argZeta (u + (T - h) * Complex.I))
      = (σ1 - σ0) * (argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I))
        + (∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u)
        - (∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u) := by
    rw [heq1, heq2]; ring
  have hb : (σ1 - σ0)
        * (argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I))
      ≤ (σ1 - σ0) * (2 * Real.log ‖riemannZeta (σ1 : ℂ)‖) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ σ1 - σ0)
    calc argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I)
        ≤ |argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I)| :=
          le_abs_self _
      _ ≤ 2 * Real.log ‖riemannZeta (σ1 : ℂ)‖ := hclaim1
  have hpi := Real.pi_pos
  have hexpand : (1 / (2 * Real.pi)) *
        ((σ1 - σ0)
            * (argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I))
          + (∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u)
          - (∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u))
      = (1 / (2 * Real.pi)) * ((σ1 - σ0)
            * (argZeta (σ1 + (T + h) * Complex.I) - argZeta (σ1 + (T - h) * Complex.I)))
        + (1 / (2 * Real.pi)) * (∫ u in σ0..σ1, deltaArgZeta (T + h) σ1 u)
        - (1 / (2 * Real.pi)) * (∫ u in σ0..σ1, deltaArgZeta (T - h) σ1 u) := by
    ring
  rw [hdiff, hexpand]
  have hb2' := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
  have heqc : (1 / (2 * Real.pi)) * ((σ1 - σ0) * (2 * Real.log ‖riemannZeta (σ1 : ℂ)‖))
      = (σ1 - σ0) / Real.pi * Real.log ‖riemannZeta (σ1 : ℂ)‖ := by ring
  linarith [hb2', heqc]
