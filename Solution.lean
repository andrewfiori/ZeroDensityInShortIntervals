/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import ZerosInShortIntervals

/-!
# Solution: the Challenge statements, proved from the development

**DRAFT.**  This is the Solution module of an intended Palomar Registry submission.  It is not
yet submitted and the accompanying metadata is not final.

## How this file relates to `Challenge.lean`

Everything down to the hypothesis class is a verbatim copy of `Challenge.lean`.  The duplication
is forced rather than chosen: Comparator compares a declaration of the same name in two modules,
so the two cannot share a module, and the Challenge may import nothing but Mathlib.  Read the
copy as the statement of record and this file as the proof of it.

What is added is a bridge and seven proofs.  The bridge turns this module's bundled hypothesis
class into the six classes the development uses, field by field; each field transfers by
definitional unfolding, because the definitions above are literal copies of the library's.  Then
`η`, characterised here by `1 + η + log η = 0` on `(0,1)`, is identified with the library's
`eta`, which is defined as the unique such root, and each statement follows by `exact` from the
development.

## What is claimed

Seven statements are compared.  Write `N(T₁,T₂,α)` for the number of nontrivial zeros of the
Riemann zeta function with imaginary part in `(T₁,T₂]` and real part `> 1-α`, counted with
multiplicity, and `N½` for the same count with a zero on either horizontal edge counted for half,
which is the source's convention.

* `zero_density_jensen` and `zero_density_littlewood` (Theorems 2 and 3 of the source) bound
  `N(t-h, t+h, α)` above by an explicit main term plus an explicit error, for `0 ≤ h ≤ t^{2/3}`.
  The two use different mechanisms, Jensen's formula and Littlewood's lemma, and neither
  dominates the other over the whole parameter range.
* `edge_proportion_jensen` and `edge_proportion_littlewood` (Corollaries 4 and 5) turn those into
  a bound on the *fraction* of the window's zeros lying in one edge strip, `N½(α)/N½(1) < C₂`.
* `positive_proportion_in_middle_band` (Corollary 1, the headline) says that for every `α` in
  `(0, 1/6)` there are `h₀` and `t₀` at which the constant `C = 1 - 2C₂` is positive, and beyond
  which a fraction at least `C` of the window's zeros have real part in the middle band
  `[α, 1-α]`, away from both edges.  There is no side condition: the radius `r = 1/2` is supplied
  and always works.  The factor two is the reflection `ρ ↦ 1 - conj ρ`, a multiplicity-preserving
  involution of the zero set, so the two edge strips carry equally many zeros; that is proved in
  the development, not assumed.
* `positive_proportion` is the same with the constant existentially quantified, which is the
  source's own sentence.
* `positive_proportion_sixteenth` is `α = 1/16` with the better radius `r = 1/5`, where the
  limiting constant is `9/25 ≈ 0.36` rather than `r = 1/2`'s `5/21 ≈ 0.238`.  The source's tables
  give `0.1374` at `h₀ = 100`, `t₀ = 10^100` and `0.3484` at `t₀ = 10^10000`, the former being the
  "at least 13%" of its abstract.

## What it is conditional on

`ZeroDensityHypotheses` bundles the development's assumptions, in the signature rather than
hidden.  They are of two kinds and a reader is entitled to weigh them differently: published
explicit bounds on `ζ` and `Γ` transcribed from other authors, and finite numerical certificates
established outside Lean by ball arithmetic on explicit compact boxes, which Mathlib cannot
reproduce because it has no verified evaluation of `ζ`.  Each field says which it is.  The bundle
carries the whole development's assumption set, including fields a given statement does not use,
which makes these statements slightly weaker than necessary.

The positivity of the constant is **proved**, not assumed, and carries no extra hypothesis: the
radius `r = 1/2` is supplied, and there `4A₁ = (1/3)/(1/2-α)`, which is `< 1` exactly when
`α < 1/6`.  No numerical certificate enters it.  Every term of `C₂` except the leading `2A₁`
carries a factor `1/h` or `1/log t`, so the constant tends to `1 - 4A₁`, and nothing about the
size of the remaining coefficients is needed, only that they do not depend on `h` or `t`.

## Provenance

The mathematics is due to A. Fiori, *Zero Density Theorems for Short Intervals*.  See
`formalization.yaml` for sources, licence, automation, review status, and the correspondence
between each statement here and the development it is restated from.
-/

namespace ZeroDensityShortIntervals

open Filter Topology Complex

/-! ## Counting zeros

All four counts are sums of the divisor of `riemannZeta` over a region.  `MeromorphicOn.divisor`
records the order of vanishing at each point with sign, so these count with multiplicity. -/

/-- `N T` is the number of nontrivial zeros with imaginary part in `(0, T]`, with multiplicity. -/
noncomputable def N (T : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.im ∧ s.im ≤ T} u

/-- The main term of the Riemann–von Mangoldt formula, `M(T) = (T/2π)·log(T/2πe)`. -/
noncomputable def bwM (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

/-- Zeros with imaginary part in `(T₁, T₂]` and real part `> 1 - α`: the right edge strip. -/
noncomputable def Nrect (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ 1 - α < s.re} u

/-- Zeros with imaginary part in `(T₁, T₂]` and real part in the middle band `[α, 1-α]`. -/
noncomputable def NrectMid (T₁ T₂ α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta
    {s : ℂ | T₁ < s.im ∧ s.im ≤ T₂ ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u

/-- Zeros on the horizontal line `Im s = T` with real part `> 1 - α`. -/
noncomputable def NlineRe (T α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ 1 - α < s.re} u

/-- Zeros on the horizontal line `Im s = T` with real part in `[α, 1-α]`. -/
noncomputable def NlineReMid (T α : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor riemannZeta {s : ℂ | s.im = T ∧ α ≤ s.re ∧ s.re ≤ 1 - α} u

/-- The right edge strip of the window `(T₁, T₂]`, counting a zero on either horizontal edge with
half its multiplicity.  This is the source's page-one convention. -/
noncomputable def Nhalf (T₁ T₂ α : ℝ) : ℝ :=
  (Nrect T₁ T₂ α : ℝ) - (NlineRe T₂ α : ℝ) / 2 + (NlineRe T₁ α : ℝ) / 2

/-- The middle band of the window `(T₁, T₂]`, with the same half-counting convention.  Note that
`Nhalf T₁ T₂ 1` is the count over the whole strip, since `1 - 1 < s.re` holds for every
nontrivial zero. -/
noncomputable def NhalfMid (T₁ T₂ α : ℝ) : ℝ :=
  (NrectMid T₁ T₂ α : ℝ) - (NlineReMid T₂ α : ℝ) / 2 + (NlineReMid T₁ α : ℝ) / 2

/-! ## The chord constants

The Littlewood bound is assembled from a piecewise-linear majorant of `log‖ζ‖` on the critical
strip.  `sigma k` are the abscissae where the pieces meet, `vCoeff`/`vCoeffP`/`vCoeffPP` the
values being interpolated, and `mCoeff`/`bCoeff` the slope and intercept of each chord. -/

/-- The chord abscissae, `σ_k = 1 - (k+3)/(2^{k+3}-2)` for `k ≥ 0` and its reflection below. -/
noncomputable def sigma (k : ℤ) : ℝ :=
  if 0 ≤ k then 1 - (k + 3 : ℝ) / (2 ^ (k + 3) - 2)
  else ((-k : ℝ) + 3) / (2 ^ (-k + 3) - 2)

/-- The value interpolated at `σ_k` by the leading chord family. -/
noncomputable def vCoeff (k : ℤ) : ℝ :=
  if 0 ≤ k then 1 / (2 ^ (k + 3) - 2)
  else sigma (-k) - 1 / 2 + 1 / (2 ^ (-k + 3) - 2)

/-- The `log log|t|` family interpolates the constant `1`. -/
noncomputable def vCoeffP (_k : ℤ) : ℝ := 1

/-- The constant-term family: `log 1.546`, `log 0.611`, and a reflected variant. -/
noncomputable def vCoeffPP (k : ℤ) : ℝ :=
  if 0 < k then Real.log 1.546
  else if k = 0 then Real.log 0.611
  else Real.log 1.546 + (sigma k - 1 / 2) * Real.log Real.pi

/-- Slope of the `k`-th chord of the leading family. -/
noncomputable def mCoeff (k : ℤ) : ℝ := (vCoeff k - vCoeff (k + 1)) / (sigma k - sigma (k + 1))

/-- Intercept of the `k`-th chord of the leading family. -/
noncomputable def bCoeff (k : ℤ) : ℝ := vCoeff k - mCoeff k * sigma k

/-- Slope of the `k`-th chord of the `log log|t|` family. -/
noncomputable def mCoeffP (k : ℤ) : ℝ := (vCoeffP k - vCoeffP (k + 1)) / (sigma k - sigma (k + 1))

/-- Intercept of the `k`-th chord of the `log log|t|` family. -/
noncomputable def bCoeffP (k : ℤ) : ℝ := vCoeffP k - mCoeffP k * sigma k

/-- Slope of the `k`-th chord of the constant-term family. -/
noncomputable def mCoeffPP (k : ℤ) : ℝ :=
  (vCoeffPP k - vCoeffPP (k + 1)) / (sigma k - sigma (k + 1))

/-- Intercept of the `k`-th chord of the constant-term family. -/
noncomputable def bCoeffPP (k : ℤ) : ℝ := vCoeffPP k - mCoeffPP k * sigma k

/-- The angle at which the circle of radius `r` about `1` meets the vertical line `Re s = σ_k`. -/
noncomputable def theta (k : ℤ) (r : ℝ) : ℝ := Real.arcsin ((1 - sigma k) / r)

/-- The least chord index whose abscissa the circle of radius `r` reaches. -/
noncomputable def Kidx (r : ℝ) : ℤ := sInf {k : ℤ | 1 - sigma k ≤ r}

/-- `c₁(r)`: the circular average of the leading chord majorant over the radius-`r` circle. -/
noncomputable def c1 (r : ℝ) : ℝ :=
  (mCoeff (Kidx r - 1) + bCoeff (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeff (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeff (Kidx r + j) + bCoeff (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeff (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- `c₂(r)`: the same average for the `log log|t|` family. -/
noncomputable def c2 (r : ℝ) : ℝ :=
  (mCoeffP (Kidx r - 1) + bCoeffP (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeffP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeffP (Kidx r + j) + bCoeffP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- `c₃(r)`: the same average for the constant-term family. -/
noncomputable def c3 (r : ℝ) : ℝ :=
  (mCoeffPP (Kidx r - 1) + bCoeffPP (Kidx r - 1)) * (Real.pi / 2 - theta (Kidx r) r)
    - mCoeffPP (Kidx r - 1) * r * Real.cos (theta (Kidx r) r)
  + ∑' j : ℕ,
      ((mCoeffPP (Kidx r + j) + bCoeffPP (Kidx r + j))
          * (theta (Kidx r + j) r - theta (Kidx r + j + 1) r)
        + mCoeffPP (Kidx r + j) * r
            * (Real.cos (theta (Kidx r + j) r) - Real.cos (theta (Kidx r + j + 1) r)))

/-- `c₄(r)`: the boundary term, an explicit integral of `Re(ζ'/ζ)` against `arcsin`. -/
noncomputable def c4 (r : ℝ) : ℝ :=
  (1 / 2) * Real.log ‖riemannZeta (1 + r : ℂ)‖
    - (r / Real.pi) *
        ∫ u in (0 : ℝ)..1,
          (deriv riemannZeta (1 + r * u : ℂ) / riemannZeta (1 + r * u : ℂ)).re * Real.arcsin u

/-- `Φ(s) = ∑_{n≥2} Λ(n)/(log n)²·n^{-s}`, the twice-integrated prime-counting Dirichlet series. -/
noncomputable def Phi (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n ≤ 1 then 0 else
    (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) ^ 2 / (n : ℂ) ^ s

/-! ## The Littlewood constant `C₂ᴸ`

`A₁,…,A₆` are the coefficients of Theorem 32 of the source; `C₂ᴸ` assembles them over the
Riemann–von Mangoldt denominator.  `η` is the unique root of `1 + η + log η = 0` in `(0,1)`,
approximately `0.2784645`; it is a parameter here, characterised by the hypotheses of the
theorem, rather than a definition, so that this module needs no proof of its existence. -/

/-- `A₁`: the leading coefficient. -/
noncomputable def A1 (α r : ℝ) (k : ℤ) : ℝ := (mCoeff k * (1 - r) + bCoeff k) / (2 * (r - α))

/-- `A₂`: the `log log|t|` coefficient. -/
noncomputable def A2 (α r : ℝ) (k : ℤ) : ℝ :=
  (mCoeffP k * (1 - r) + bCoeffP k) / (2 * Real.pi * (r - α))

/-- `A₃`: the constant-term coefficient. -/
noncomputable def A3 (α r : ℝ) (k : ℤ) : ℝ :=
  (mCoeffPP k * (1 - r) + bCoeffPP k) / (2 * Real.pi * (r - α))

/-- `A₄ = c₁(r)·r/(r-α)`. -/
noncomputable def A4 (α r : ℝ) : ℝ := c1 r * r / (r - α)

/-- `A₅ = (c₂(r)·r + πr)/(π(r-α))`. -/
noncomputable def A5 (α r : ℝ) : ℝ := (c2 r * r + Real.pi * r) / (Real.pi * (r - α))

/-- `A₆`: the additive constant, collecting four contributions over `π(r-α)`. -/
noncomputable def A6 (η α r : ℝ) : ℝ :=
  (c3 r * r + c4 r * Real.pi * r + Real.pi * Real.log 29.388 * r + (Phi (1 + η * r : ℂ)).re
      + (1 + η) * r * Real.log ‖riemannZeta (1 + η * r : ℂ)‖)
    / (Real.pi * (r - α))

/-- `α̂_r = √(r²-α²)`: the half-width of the chord the circle of radius `r` cuts from the line
`Re s = 1-α`. -/
noncomputable def hatAlpha (r α : ℝ) : ℝ := Real.sqrt (r ^ 2 - α ^ 2)

/-- `D_{r,α} = 2r√(1-(α/r)²) - 2α·arctan(√((r/α)²-1))`: the area factor of the rectangular
Jensen bound. -/
noncomputable def rectDenom (r α : ℝ) : ℝ :=
  2 * r * Real.sqrt (1 - (α / r) ^ 2) - 2 * α * Real.arctan (Real.sqrt ((r / α) ^ 2 - 1))

/-- `c₅(r)`: the boundary term of the rectangular Jensen bound. -/
noncomputable def c5 (r : ℝ) : ℝ :=
  (Phi (1 + r : ℂ)).re
    + (2 * r / Real.pi) * ∫ u in (0 : ℝ)..1, Real.log ‖riemannZeta (1 + r * u : ℂ)‖ * Real.arcsin u

/-- `B₁ = c₁(r)/D_{r,α}`, the leading Jensen coefficient. -/
noncomputable def B1 (α r : ℝ) : ℝ := c1 r / rectDenom r α

/-- `B₂ = c₂(r)/(π D_{r,α})`, the `log log|t|` Jensen coefficient. -/
noncomputable def B2 (α r : ℝ) : ℝ := c2 r / (Real.pi * rectDenom r α)

/-- `B₃ = c₃(r)/(π D_{r,α})`, the constant-term Jensen coefficient. -/
noncomputable def B3 (α r : ℝ) : ℝ := c3 r / (Real.pi * rectDenom r α)

/-- `B₄ = (2Φ(1) + c₅(r))/D_{r,α}`, the additive Jensen constant. -/
noncomputable def B4 (α r : ℝ) : ℝ := (2 * (Phi 1).re + c5 r) / rectDenom r α

/-- The main term of the Jensen bound, Theorem 2 of the source. -/
noncomputable def UJensen (α r h t : ℝ) : ℝ :=
  (2 * h + 2 * hatAlpha r α) *
      (B1 α r / Real.pi * Real.log t + B2 α r * Real.log (Real.log t) + B3 α r)
    + B4 α r

/-- The error term of the Jensen bound. -/
noncomputable def EJensen (α r t : ℝ) : ℝ :=
  3.35 / (rectDenom r α * t ^ ((1 : ℝ) / 3))

/-- The main term of the Littlewood bound, Theorem 3 of the source. -/
noncomputable def ULittlewood (η α r h t : ℝ) (k : ℤ) : ℝ :=
  (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log t
    + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log t)
    + 2 * A3 α r k * h + A6 η α r

/-- The error term of the Littlewood bound. -/
noncomputable def ELittlewood (α r t : ℝ) : ℝ :=
  (1 / (t * (r - α))) * (0.335 + 0.51 / Real.log t)

/-- The denominator: the Riemann–von Mangoldt main term, cleared of `h` and `log t`. -/
noncomputable def C2denom (h t : ℝ) : ℝ :=
  1 - Real.log (2 * Real.pi) / Real.log t
    - (1 - Real.log 2) / (t ^ ((2 : ℝ) / 3) * Real.log t)
    - 0.194 * Real.pi / h
    - 9.908 * Real.pi / (h * Real.log t)

/-- `C₂ᴸ`: the bound on the fraction of the window's zeros lying in one edge strip. -/
noncomputable def C2Littlewood (η α r h t : ℝ) (k : ℤ) : ℝ :=
  (2 * A1 α r k + 2 * A4 α r / h
      + Real.pi * (2 * A2 α r k + 2 * A5 α r / h) * Real.log (Real.log t) / Real.log t
      + 2 * Real.pi * A3 α r k / Real.log t
      + Real.pi * A6 η α r / (h * Real.log t)
      + Real.pi / ((r - α) * h * t * Real.log t) * (0.335 + 0.51 / Real.log t))
    / C2denom h t

/-- `C₂ᴶ`: the Jensen analogue, bounding the same fraction through Jensen's formula. -/
noncomputable def C2Jensen (α r h t : ℝ) : ℝ :=
  ((2 + 2 * hatAlpha r α / h) *
        (B1 α r + Real.pi * B2 α r * Real.log (Real.log t) / Real.log t
          + Real.pi * B3 α r / Real.log t)
      + Real.pi * B4 α r / (h * Real.log t)
      + 3.35 * Real.pi / (rectDenom r α * h * t ^ ((1 : ℝ) / 3) * Real.log t))
    / C2denom h t

/-- `C = 1 - 2C₂ᴸ`: the lower bound for the proportion in the middle band.  The factor two is the
reflection `ρ ↦ 1 - conj ρ`, which is a multiplicity-preserving involution of the zero set and so
makes the two edge strips carry equally many zeros. -/
noncomputable def CsimpLittlewood (η α r h t : ℝ) (k : ℤ) : ℝ :=
  1 - 2 * C2Littlewood η α r h t k

/-- The threshold `h` must exceed for the denominator to stay positive. -/
noncomputable def h0Threshold (t0 : ℝ) : ℝ :=
  (97 * Real.pi / 500) * ((1 + 4954 / (97 * Real.log t0)) /
    (1 - (1 - Real.log 2) / (t0 ^ ((2 : ℝ) / 3) * Real.log t0)
      - Real.log (2 * Real.pi) / Real.log t0))

/-! ## Auxiliary functions of the assumed bounds

These appear only inside the hypothesis class.  They are the objects the assumed estimates are
statements about: the analytic branch of `log Γ`, the regularised `ζ'/ζ`, and the factor systems
of the Phragmén–Lindelöf interpolation. -/

/-- The `n`-th term of the Weierstrass series for `log Γ`. -/
noncomputable def logGammaTerm (z : ℂ) (n : ℕ) : ℂ :=
  z / ((n : ℂ) + 1) - Complex.log (1 + z / ((n : ℂ) + 1))

/-- The analytic branch of `log Γ` on the slit plane, as a Weierstrass series. -/
noncomputable def logGammaAnalytic (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * z - Complex.log z + ∑' n, logGammaTerm z n

/-- `(s-1)ζ(s)`, patched to `1` at `s = 1` so that it is entire and nonzero near `1`. -/
noncomputable def zetaReg : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

/-- `G = -zetaReg'/zetaReg + 1/(s+2) + 1/(s+4) + 1/(s+6)`: the logarithmic derivative with the
pole at `1` and the first three trivial zeros removed. -/
noncomputable def logDerivZetaG (s : ℂ) : ℂ :=
  -(deriv zetaReg s / zetaReg s) + 1 / (s + 2) + 1 / (s + 4) + 1 / (s + 6)

/-- `logDerivZetaG` with its three removable singularities filled in by their limits. -/
noncomputable def logDerivZetaGext : ℂ → ℂ :=
  Function.update (Function.update (Function.update logDerivZetaG (-2)
    (limUnder (𝓝[≠] (-2)) logDerivZetaG)) (-4) (limUnder (𝓝[≠] (-4)) logDerivZetaG))
    (-6) (limUnder (𝓝[≠] (-6)) logDerivZetaG)

/-- The square `(-7,7)²` on which `G` is bounded. -/
noncomputable def logDerivZetaBox : Set ℂ := Set.Ioo (-7 : ℝ) 7 ×ℂ Set.Ioo (-7 : ℝ) 7

/-- `linG C Q s = C(Q+s)`, a linear comparison factor. -/
def linG (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) + s)

/-- `linGRefl C Q s = C(Q-s)`, its mirror image. -/
def linGRefl (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) - s)

/-- `GPL Q s = ½(log(Q+s) + log(Q+2-s))`, the log-type comparison factor. -/
noncomputable def GPL (Q : ℝ) : ℂ → ℂ :=
  fun s => (1 / 2) * (Complex.log ((Q : ℂ) + s) + Complex.log ((Q : ℂ) + 2 - s))

/-- `G1shift Q c d s = c·GPL Q (s+1) + d`, the shifted variant used in case (1c). -/
noncomputable def G1shift (Q c d : ℝ) : ℂ → ℂ := fun s => (c : ℂ) * GPL Q (s + 1) + (d : ℂ)

/-- The three comparison functions of the interpolation. -/
noncomputable def interpG (A B p q Q : ℝ) : Fin 3 → ℂ → ℂ :=
  ![linG (A ^ (1 / (p + 1))) 0, linGRefl ((B / A ^ (1 / (p + 1))) ^ (1 / q)) 1, GPL Q]

/-- The exponents at the left edge. -/
def interpα (p ra : ℝ) : Fin 3 → ℝ := ![p + 1, 0, ra]

/-- The exponents at the right edge. -/
def interpβ (q rb : ℝ) : Fin 3 → ℝ := ![1, q, rb]

/-- The four comparison functions of case (1c). -/
noncomputable def interpG1c (B c d q Q : ℝ) : Fin 4 → ℂ → ℂ :=
  ![linG 1 0, G1shift Q c d, linGRefl (B ^ (1 / q)) 1, GPL Q]

/-- The case (1c) exponents at the left edge. -/
def interpα1c (p : ℝ) : Fin 4 → ℝ := ![p + 1, 1, 0, 0]

/-- The case (1c) exponents at the right edge. -/
def interpβ1c (q : ℝ) : Fin 4 → ℝ := ![1, 0, q, 1]

/-- The interpolation claim on the `k`-th sub-strip of the critical strip, for `|t| ≤ 3`. -/
def Hcompact2Claim (k : ℕ) : Prop :=
  ∀ t : ℝ, |t| ≤ 3 →
    ∀ σ ∈ Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
    ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
      < ∏ i, (⨅ τ : Set.Icc (1 - (k : ℝ) / (2 ^ k - 2)) (1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)),
            ‖interpG 1.546 1.546 (1 / ((2 : ℝ) ^ k - 2)) (1 / ((2 : ℝ) ^ (k + 1) - 2))
              (Real.exp 1) i ((τ : ℝ) + t * Complex.I)‖)
          ^ (interpα (1 / ((2 : ℝ) ^ k - 2)) 1 i
                * ((1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)) - σ)
                / ((1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)) - (1 - (k : ℝ) / (2 ^ k - 2)))
              + interpβ (1 / ((2 : ℝ) ^ (k + 1) - 2)) 1 i
                * (σ - (1 - (k : ℝ) / (2 ^ k - 2)))
                / ((1 - ((k : ℝ) + 1) / (2 ^ (k + 1) - 2)) - (1 - (k : ℝ) / (2 ^ k - 2))))

/-! ## The hypotheses

One bundled class.  The underlying development keeps these as six separate classes so that a
reader can see which results rest on published literature and which on outside computation; they
are gathered here, with the distinction kept in the field comments, to keep this module short. -/

/-- Everything the theorem below assumes and does not prove. -/
class ZeroDensityHypotheses where
  /-- LITERATURE. Hiary–Patel–Yang, Eq. (3.23): the sixth-power bound on the critical line. -/
  hiary_eq_3_23 : ∀ {t : ℝ}, (10 : ℝ) ^ (12 : ℕ) < |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.478013 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 3.853165 * |t| ^ (1 / 6 : ℝ) - 2.914229
  /-- LITERATURE. Revers, Remark 3.1: the same shape with sharper constants. -/
  revers_remark31 : ∀ {t : ℝ}, (7 : ℝ) * 10 ^ (11 : ℕ) ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖
      ≤ 0.470795 * |t| ^ (1 / 6 : ℝ) * Real.log |t| + 4.04972 * |t| ^ (1 / 6 : ℝ) - 21.5437
  /-- LITERATURE. Revers: the clean subconvexity bound, valid from `|t| ≥ 3`. -/
  revers_subconvexity_bound : ∀ {t : ℝ}, 3 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.611 * |t| ^ (1 / 6 : ℝ) * Real.log |t|
  /-- LITERATURE. Patel–Yang: the sub-Weyl bound on the critical line. -/
  patel_yang_subweyl_bound : ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 66.7 * t ^ (27 / 164 : ℝ)
  /-- LITERATURE. Yang, Theorem 1.1, for `k ≥ 4`. -/
  yang_critical_strip_bound : ∀ {k : ℕ}, 4 ≤ k → ∀ {t : ℝ}, 3 ≤ t →
    ‖riemannZeta (1 - (k : ℝ) / (2 ^ k - 2) + t * Complex.I)‖
      ≤ 1.546 * t ^ ((1 : ℝ) / (2 ^ k - 2)) * Real.log t
  /-- LITERATURE. Bellotti's explicit form of Richert's bound inside the critical strip. -/
  bellotti_richert_bound : ∀ {σ t : ℝ}, σ ∈ Set.Icc (1 / 2 : ℝ) 1 → 3 ≤ |t| →
    ‖riemannZeta (σ + t * Complex.I)‖
      ≤ 70.7 * |t| ^ (4.438 * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ)
  /-- LITERATURE. Leong, Theorem 4: a lower bound for `|ζ(1+it)|`. -/
  leong_log_zeta_one_bound : ∀ {t : ℝ}, 2 ≤ |t| →
    -Real.log (‖riemannZeta (1 + t * Complex.I)‖) ≤ Real.log (Real.log |t|) + Real.log 29.388
  /-- LITERATURE. Fiori, *A Phragmén–Lindelöf theorem*, Theorem 7: the interpolation principle
  the assumed `ζ` bounds in the critical strip are built on. -/
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
  /-- LITERATURE, resting on computation. Platt–Trudgian: the Riemann hypothesis is verified up
  to height `3·10^12`. -/
  platt_trudgian_verified_below : ∀ (ρ : ℂ), 0 < ρ.im → ρ.im ≤ 3 * 10 ^ (12 : ℕ) →
    riemannZeta ρ = 0 → ρ.re = 1 / 2
  /-- LITERATURE. Farzanfard: the classical zero-density bound on an interval. -/
  farzanfard_zero_density_interval : ∀ {α T₁ T₂ : ℝ},
    α ∈ Set.Icc (0 : ℝ) (1 / 4) → 3 * 10 ^ (12 : ℕ) ≤ T₁ → T₁ ≤ T₂ →
    (Nrect T₁ T₂ α : ℝ)
      ≤ 12.45321 * T₂ ^ ((8 : ℝ) / 3 * α) * Real.log T₂ ^ (3 + 2 * α)
        + 3.869 * Real.log T₂ ^ (2 : ℕ)
  /-- LITERATURE. Bellotti–Wong, Corollary 1.3: the Riemann–von Mangoldt formula with an explicit
  error.  This is the lower bound for the denominator of the proportion. -/
  bellotti_wong_cor_1_3 : ∀ {T : ℝ}, 1 ≤ T →
    |((N T : ℤ) : ℝ) - bwM T| ≤ 0.097 * Real.log T + 4.954
  /-- LITERATURE. The lowest nontrivial zero has ordinate above `14`; it is `14.1347…`. -/
  riemannZeta_lowest_zero_height : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    14 < |ρ.im|
  /-- LITERATURE, a name. Brent's remainder `R₂` in the Stirling expansion. -/
  remainder : ℂ → ℂ
  /-- LITERATURE, a name. Brent's remainder `R̂₂` in the half-shifted expansion. -/
  shiftedRemainder : ℂ → ℂ
  /-- LITERATURE. Brent, Eq. (2.1): Stirling's expansion to the `B₂` term. -/
  expansion : ∀ {z : ℂ}, 0 < z.re →
    logGammaAnalytic z
      = (z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * Real.pi)
        + (bernoulli 2 : ℂ) / (2 * z) + remainder z
  /-- LITERATURE, resting on computation. Brent, Corollary 2.2 at `k = 2`. -/
  remainder_bound : ∀ {z : ℂ}, 0 < z.re →
    ‖remainder z‖ < ‖(1 + Real.sqrt (2 * Real.pi)) * (bernoulli 4 : ℂ) / (12 * z ^ 3)‖
  /-- LITERATURE. Brent, Eq. (3.4): the half-shifted expansion. -/
  shifted_expansion : ∀ {z : ℂ}, 5 < z.im →
    logGammaAnalytic (z + 1 / 2)
      = z * Complex.log z - z + 1 / 2 * Complex.log (2 * Real.pi) - 1 / (24 * z)
        + shiftedRemainder z
  /-- LITERATURE, resting on computation. Brent's bound on the shifted remainder. -/
  shifted_remainder_bound : ∀ {z : ℂ}, 5 < z.im → |z.re| ≤ 1 →
    ‖shiftedRemainder z‖ ≤ 1 / 100 / ‖z‖ ^ 3
  /-- NUMERICAL CERTIFICATE. `Φ(1) = ∫_1^∞ log ζ(x) dx < 1.7975699586287395`; arb quadrature,
  margin `9.2×10^{-17}`. -/
  integral_log_zeta_Ioi_one_lt :
    (∫ x in Set.Ioi (1 : ℝ), Real.log ‖riemannZeta (x : ℂ)‖) < 1.7975699586287395
  /-- NUMERICAL CERTIFICATE. `3e·E_{1/2}/(2π) < 1.1343755`, needing nine digits of `Γ(1/4)`;
  margin `1.1×10^{-8}`. -/
  ehalf_bound :
    3 * Real.exp 1 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ (3 / 2 : ℝ)) / (2 * Real.pi)
      < 1.1343755
  /-- NUMERICAL CERTIFICATE. `‖G(1+z)‖ ≤ 0.6` on the boundary of `(-7,7)²`; mpmath, observed
  maximum `0.59002`. -/
  logDerivZetaG_boundary_bound :
    ∀ z ∈ frontier logDerivZetaBox, ‖logDerivZetaGext (1 + z)‖ ≤ 0.6
  /-- NUMERICAL CERTIFICATE. Case (1a), the sub-Weyl window `|t| ≤ 4e+1`; arb over 125 boxes. -/
  interpolated_bound_1a_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 66.7 1.546 (27 / 164) (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (27 / 164) 0 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2))
  /-- NUMERICAL CERTIFICATE. Case (1b), the Revers window `|t| ≤ 3`; arb over 264 boxes. -/
  interpolated_bound_1b_hcompact :
    ∀ t : ℝ, |t| ≤ 3 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG 0.611 1.546 (1 / 6) (1 / 14) 16 i ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα (1 / 6) 1 i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ (1 / 14) 1 i * (σ - 1 / 2) / (5 / 7 - 1 / 2))
  /-- NUMERICAL CERTIFICATE. Case (1c), the four-factor variant; arb over 137 boxes. -/
  interpolated_bound_1c_hcompact :
    ∀ t : ℝ, |t| ≤ 4 * Real.exp 1 + 1 → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 7),
      ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
        < ∏ i, (⨅ τ : Set.Icc (1 / 2 : ℝ) (5 / 7),
              ‖interpG1c 1.546 0.470795 4.04972 (1 / 14) (4 * Real.exp 1) i
                ((τ : ℝ) + t * Complex.I)‖)
            ^ (interpα1c (1 / 6) i * (5 / 7 - σ) / (5 / 7 - 1 / 2)
                + interpβ1c (1 / 14) i * (σ - 1 / 2) / (5 / 7 - 1 / 2))
  /-- NUMERICAL CERTIFICATE. The `k = 4` sub-strip; arb over 292 boxes. -/
  hcompact2_four : Hcompact2Claim 4
  /-- NUMERICAL CERTIFICATE. The `k = 5` sub-strip; arb over 302 boxes. -/
  hcompact2_five : Hcompact2Claim 5
  /-- NUMERICAL CERTIFICATE. The `k = 6` sub-strip; arb over 588 boxes. -/
  hcompact2_six : Hcompact2Claim 6
  /-- NUMERICAL CERTIFICATE. The `k = 7` sub-strip; arb over 926 boxes. -/
  hcompact2_seven : Hcompact2Claim 7
  /-- NUMERICAL CERTIFICATE. All `k ≥ 8` at once, through a `k`-uniform lower bound on the
  right-hand side; arb over 232 boxes. -/
  hcompact2_tail : ∀ {k : ℕ}, 8 ≤ k → Hcompact2Claim k

/-! ## The bridge to the development

Each field transfers by definitional unfolding: the definitions above are literal copies of the
library's, so the two statements of each hypothesis are the same term. -/

section Bridge

variable [ZeroDensityHypotheses]

/-- The literature bounds, as the library's class. -/
instance instLiteratureInputs : _root_.LiteratureInputs where
  hiary_eq_3_23 := ZeroDensityHypotheses.hiary_eq_3_23
  revers_remark31 := ZeroDensityHypotheses.revers_remark31
  revers_subconvexity_bound := ZeroDensityHypotheses.revers_subconvexity_bound
  patel_yang_subweyl_bound := ZeroDensityHypotheses.patel_yang_subweyl_bound
  yang_critical_strip_bound := ZeroDensityHypotheses.yang_critical_strip_bound
  bellotti_richert_bound := ZeroDensityHypotheses.bellotti_richert_bound
  leong_log_zeta_one_bound := ZeroDensityHypotheses.leong_log_zeta_one_bound
  fiori_phragmenLindelof := ZeroDensityHypotheses.fiori_phragmenLindelof
  platt_trudgian_verified_below := ZeroDensityHypotheses.platt_trudgian_verified_below
  farzanfard_zero_density_interval := ZeroDensityHypotheses.farzanfard_zero_density_interval
  bellotti_wong_cor_1_3 := ZeroDensityHypotheses.bellotti_wong_cor_1_3
  riemannZeta_lowest_zero_height := ZeroDensityHypotheses.riemannZeta_lowest_zero_height

/-- Brent's two remainders and the four statements about them. -/
instance instBrentStirlingInputs : _root_.BrentStirlingInputs where
  remainder := ZeroDensityHypotheses.remainder
  shiftedRemainder := ZeroDensityHypotheses.shiftedRemainder
  expansion := ZeroDensityHypotheses.expansion
  remainder_bound := ZeroDensityHypotheses.remainder_bound
  shifted_expansion := ZeroDensityHypotheses.shifted_expansion
  shifted_remainder_bound := ZeroDensityHypotheses.shifted_remainder_bound

/-- The two Mathlib-expressible numerical certificates. -/
instance instNumericCertificates : _root_.NumericCertificates where
  integral_log_zeta_Ioi_one_lt := ZeroDensityHypotheses.integral_log_zeta_Ioi_one_lt
  ehalf_bound := ZeroDensityHypotheses.ehalf_bound

/-- The boundary bound behind the Laurent expansion of `ζ'/ζ`. -/
instance instLaurentCertificate : _root_.LaurentCertificate where
  logDerivZetaG_boundary_bound := ZeroDensityHypotheses.logDerivZetaG_boundary_bound

/-- The three interpolation windows. -/
instance instInterpolationCertificates : _root_.InterpolationCertificates where
  interpolated_bound_1a_hcompact := ZeroDensityHypotheses.interpolated_bound_1a_hcompact
  interpolated_bound_1b_hcompact := ZeroDensityHypotheses.interpolated_bound_1b_hcompact
  interpolated_bound_1c_hcompact := ZeroDensityHypotheses.interpolated_bound_1c_hcompact

/-- The five sub-strip certificates. -/
instance instHcompact2Certificates : _root_.Hcompact2Certificates where
  hcompact2_four := ZeroDensityHypotheses.hcompact2_four
  hcompact2_five := ZeroDensityHypotheses.hcompact2_five
  hcompact2_six := ZeroDensityHypotheses.hcompact2_six
  hcompact2_seven := ZeroDensityHypotheses.hcompact2_seven
  hcompact2_tail := ZeroDensityHypotheses.hcompact2_tail

/-- The bundle the library's headline statements take. -/
instance instZeroDensityHypotheses : _root_.ZeroDensityHypotheses where

end Bridge

/-- This module's `η`, characterised by `1 + η + log η = 0` on `(0,1)`, is the library's `eta`,
which is defined as the unique root of that equation there. -/
theorem eta_eq_of_spec {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (hη' : 1 + η + Real.log η = 0) : η = _root_.eta :=
  _root_.exists_unique_eta.unique ⟨hη, hη'⟩ ⟨_root_.eta_mem_Ioo, _root_.eta_eq⟩

-- Each proof is a single `exact`, but every symbol in the STATEMENT is this module's copy of a
-- library definition, so elaborating the type unfolds both sides through the whole constant
-- chain.  That, not the tactic block, is what costs: `#count_heartbeats` reports 103-365 for
-- these proofs, while the default 200000 is exhausted at `whnf` while elaborating the statement
-- of `edge_proportion_littlewood`.  Hence the scoped budget on each theorem below, at 250000 --
-- a quarter above the default, which is where the file was measured to still elaborate.

/-! ## The theorems -/

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **Theorem 2 of the source: the zero-density bound by Jensen's formula.**

For `t ≥ e` and `0 ≤ h ≤ t^{2/3}`, the number of zeros with imaginary part in `(t-h, t+h]` and
real part `> 1-α` is less than an explicit main term plus an explicit error.  The main term is
linear in the window width `2h` with coefficients built from the circular averages `c₁`, `c₂`,
`c₃` of a piecewise-linear majorant of `log‖ζ‖`, divided by the area factor `D_{r,α}`. -/
theorem zero_density_jensen [ZeroDensityHypotheses] {α r h t : ℝ}
    (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht : Real.exp 1 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    (Nrect (t - h) (t + h) α : ℝ) < UJensen α r h t + EJensen α r t :=
  mainJensen hα0 hαr hr1 hα ht hh0 hh

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **Theorem 3 of the source: the zero-density bound by Littlewood's lemma.**

The same shape as Theorem 2, through a different mechanism, and requiring `t ≥ e^e` and that `ζ`
not vanish on the two horizontal edges of the enlarged window.  `k` indexes the chord of the
majorant that `1-r` falls in, fixed by `hk` and `hk'`. -/
theorem zero_density_littlewood [ZeroDensityHypotheses] {η α r h t : ℝ} {k : ℤ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hη' : 1 + η + Real.log η = 0)
    (hα0 : 0 < α) (hrα : α < r) (hα16 : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : Real.exp (Real.exp 1) ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + η * r), riemannZeta (x + (t + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + η * r), riemannZeta (x + (t - h) * Complex.I) ≠ 0) :
    (Nrect (t - h) (t + h) α : ℝ) < ULittlewood η α r h t k + ELittlewood α r t := by
  obtain rfl : η = _root_.eta := eta_eq_of_spec hη hη'
  exact mainLittlewood hα0 hrα hα16 hk hk' ht hh0 hh hzf_p hzf_m

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **Corollary 4 of the source: the Jensen bound as a proportion.**

Dividing Theorem 2 by the Riemann–von Mangoldt count of the whole window turns it into a bound on
the *fraction* of the window's zeros that lie in the edge strip `Re s > 1-α`.  Both counts use
the half-counting convention.  `C₂ᴶ` is antitone in `h₀` and in `t₀`, so a single row of the
source's tables bounds the fraction for every larger window. -/
theorem edge_proportion_jensen [ZeroDensityHypotheses] {α r h t h0 t0 : ℝ}
    (hα0 : 0 < α) (hrα : α < r) (hr1 : r < 1) (hα : α < 1 / 6)
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Jensen α r h0 t0 :=
  mainPositiveProportionCorollary_jensen_half hα0 hrα hr1 hα ht0 hh0 hh ht hht

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **Corollary 5 of the source: the Littlewood bound as a proportion.**

Corollary 4 with the Littlewood mechanism.  This is the one the headline corollary below uses:
it gives the smaller constant over most of the parameter range. -/
theorem edge_proportion_littlewood [ZeroDensityHypotheses] {η α r h t h0 t0 : ℝ} {k : ℤ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hη' : 1 + η + Real.log η = 0)
    (hα0 : 0 < α) (hrα : α < r) (hα : α < 1 / 6)
    (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht0 : (10 : ℝ) ^ (12 : ℕ) < t0) (hh0 : h0Threshold t0 < h0)
    (hh : h0 < h) (ht : t0 < t) (hht : h < t ^ ((2 : ℝ) / 3)) :
    Nhalf (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 < C2Littlewood η α r h0 t0 k := by
  obtain rfl : η = _root_.eta := eta_eq_of_spec hη hη'
  exact mainPositiveProportionCorollary_littlewood_half hα0 hrα hα hk hk' ht0 hh0 hh ht hht

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **A positive proportion of the zeros in a short interval lie away from the edges of the
critical strip.**  Corollary 1 of the source, as the source states it.

Fix `α ∈ (0, 1/6)` and a radius `r > α` adapted to the chord decomposition by `hk`, `hk'`.  Then
**there exist** `h₀` and `t₀`, admissible in the sense that `t₀ > 10^12` and `h₀` exceeds the
explicit threshold `h0Threshold t₀`, such that the constant `C = 1 - 2C₂ᴸ` is **positive** there
and, for every `t > t₀` and every `h` with `h₀ < h < t^{2/3}`, the proportion of the zeros with
imaginary part in `(t-h, t+h]` whose real part lies in `[α, 1-α]` exceeds `C`.

Both counts use the source's convention: with multiplicity, and a zero on either horizontal edge
of the window counted once for half.

`η` is the unique root of `1 + η + log η = 0` in `(0,1)`, characterised here by `hη` and `hη'`
rather than constructed, which makes this statement slightly more general than the development's.

There is **no side condition**.  The radius is `r = 1/2` and the chord index `k = 0`, and that
choice always works: `σ₀ = 1/2`, so `1-r` lands on a chord endpoint, the interpolation collapses,
the numerator of `A₁` is `v₀ = 1/6` whatever the slope, and `4A₁ = (1/3)/(1/2-α) < 1` exactly when
`α < 1/6`.  Positivity of the constant is therefore proved, not assumed, from the same hypothesis
on `α` that the source already makes.

The mechanism behind it: every term of `C₂ᴸ` except the leading `2A₁` carries a factor `1/h`,
`1/log t` or `log log t / log t`, and the denominator tends to `1`, so `C₂ᴸ → 2A₁` and the
constant is eventually positive exactly when `4A₁ < 1`.  Nothing about the sizes of the other
coefficients is needed, only that they do not depend on `h` or `t`, so no numerical certificate
enters.

`r = 1/2` is the choice that always works, not the best one: see `positive_proportion_sixteenth`,
where `r = 1/5` gives a larger constant at `α = 1/16`.  It is sharp at the endpoint, though — at
`α = 1/6` it gives limiting constant exactly `0`, which is why the source's `α < 1/6` is strict. -/
theorem positive_proportion_in_middle_band [ZeroDensityHypotheses] {η α : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hη' : 1 + η + Real.log η = 0)
    (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood η α (1 / 2) h0 t0 0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood η α (1 / 2) h0 t0 0 := by
  obtain rfl : η = _root_.eta := eta_eq_of_spec hη hη'
  exact positiveProportion_littlewood_half hα0 hα

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **The same at explicit parameters**, so that nothing above is vacuous: `α = 1/16`, `r = 1/5`,
`k = 1`.

There `σ₁ = 5/7 ≤ 4/5 < 5/6 = σ₂`, so `k = 1` is the admissible chord index, and
`A₁ = 4/25`, giving `4A₁ = 16/25 < 1` and a limiting constant `1 - 4A₁ = 9/25 = 0.36`.  That is
the limit; the constant at the `(h₀, t₀)` produced here is merely positive.  The source's tables
give `0.3484` at `h₀ = 100`, `t₀ = 10^10000`, approaching `0.36` from below.

`η` remains quantified under its characterisation, since it is a root of a transcendental
equation and has no closed form. -/
theorem positive_proportion_sixteenth [ZeroDensityHypotheses] {η : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hη' : 1 + η + Real.log η = 0) :
    ∃ h0 t0 : ℝ, (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      0 < CsimpLittlewood η (1 / 16) (1 / 5) h0 t0 1 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) (1 / 16) / Nhalf (t - h) (t + h) 1
          > CsimpLittlewood η (1 / 16) (1 / 5) h0 t0 1 := by
  obtain rfl : η = _root_.eta := eta_eq_of_spec hη hη'
  exact positiveProportion_littlewood_sixteenth

set_option maxHeartbeats 250000 in
-- the cost is elaborating the STATEMENT, not the proof: every symbol here is this module's
-- copy of a library definition, so unification unfolds the whole constant chain.
/-- **The source's sentence, with nothing named:** for every `α` in `(0, 1/6)` the proportion of
the window's zeros lying in the middle band is "bounded below by an explicitly computable positive
constant".

This is the same content as `positive_proportion_in_middle_band` with the constant existentially
quantified.  It is stated separately because it is what the source's prose literally says, and
because it is the form in which the result is easiest to check against that prose: a reader need
not first work out what `CsimpLittlewood` is.  The constant is explicit — the witness is
`CsimpLittlewood η α (1/2) h₀ t₀ 0` — and the theorem above names it. -/
theorem positive_proportion [ZeroDensityHypotheses] {η α : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hη' : 1 + η + Real.log η = 0)
    (hα0 : 0 < α) (hα : α < 1 / 6) :
    ∃ C h0 t0 : ℝ, 0 < C ∧ (10 : ℝ) ^ (12 : ℕ) < t0 ∧ h0Threshold t0 < h0 ∧
      ∀ t h : ℝ, t0 < t → h0 < h → h < t ^ ((2 : ℝ) / 3) →
        NhalfMid (t - h) (t + h) α / Nhalf (t - h) (t + h) 1 > C := by
  obtain rfl : η = _root_.eta := eta_eq_of_spec hη hη'
  exact positiveProportion_of_lt_sixth hα0 hα

end ZeroDensityShortIntervals
