import ZerosInShortIntervals.Common.RealLogBounds
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Hypotheses
import ZerosInShortIntervals.Jensen.JensenScaleConstants
import ZerosInShortIntervals.Jensen.JensenScaleConstantsAlt
import ZerosInShortIntervals.Background.ExternalFacts
import ZerosInShortIntervals.Jensen.JensenBounds
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodMethod
import ZerosInShortIntervals.Common.RectangleResidue
import ZerosInShortIntervals.Littlewood.LittlewoodIdentity
import ZerosInShortIntervals.Littlewood.ArgIntegrals
import ZerosInShortIntervals.Littlewood.LittlewoodShort
import ZerosInShortIntervals.Background.BackgroundZetaBounds
import ZerosInShortIntervals.MainTerms
import ZerosInShortIntervals.ConstantSigns
import ZerosInShortIntervals.MainTheoremTight
import ZerosInShortIntervals.MainTheorem
import ZerosInShortIntervals.MainCorollary
import ZerosInShortIntervals.Reflection
import ZerosInShortIntervals.HalvingConvention
import ZerosInShortIntervals.PositiveProportion
import ZerosInShortIntervals.AllHypotheses

/-! # Zero Density Theorems for Short Intervals

Single entry point importing the whole `ZerosInShortIntervals` development, a formalization
of *Zero Density Theorems for Short Intervals* (A. Fiori). Extracted as a standalone project from
`PIMS_LEAN/PIMSLEAN/ZerosInShortIntervals` (originally flat, reorganized here into topic subfolders:
`Jensen/`, `Littlewood/`, `Background/`, plus `Definitions.lean`/`MainTheorem.lean` at the root).

Every claim from the source is stated (matching, as closely as reasonably possible, the
definitions/propositions/lemmas/theorems/corollaries of the source) and **proved**. Since
2026-09-11 the development contains no `axiom` and no `sorry`: what it imports from other papers,
and what it certifies by interval arithmetic outside Lean, are fields of six hypothesis classes
(see `Hypotheses` below), so every dependent result carries its assumptions in its signature and
every proof term rests only on `propext`, `Classical.choice` and `Quot.sound`. See the module
doc-comments of each file below for the correspondence with the source's section structure, and
for notes on apparent typos in the source that were resolved (or left unresolved and flagged)
along the way:

- `Definitions`: `N`, `Ncirc`, `Nrect`, `Phi`, `hatAlpha`, `eta`, `stieltjesConstant1`.
- `Hypotheses`: `LiteratureInputs` and `NumericCertificates`, the classes holding what this
  development assumes rather than proves. Since 2026-09-11 the project contains **no `axiom` and
  no `sorry`**: the 18 axioms and 11 numeric residues became fields of six hypothesis classes
  (the other four are declared further down the import graph, at the first point where their
  statements can be written), so every result that depends on one carries it in its signature and
  every proof term depends only on `propext`, `Classical.choice` and `Quot.sound`.
- `Jensen.JensenScaleConstants`: `sigma`, `vCoeff(P/PP)`, `m/bCoeff(P/PP)`, `theta`, `Kidx`, `c1`,
  `c2`, `c3` (`\S sec:inside`).
- `Background.ExternalFacts`: the explicit `ζ`/`Γ` bounds imported from other papers, each a
  theorem reading a field of `LiteratureInputs` or of `BrentStirlingInputs` (declared here, since
  it needs the analytic branch of `log Γ`). Two blocks are deliberately outside the hypothesis
  section and so unconditional: the `logGammaAnalytic` development, and Backlund's trick with its
  Dirichlet core. The latter is what keeps `Littlewood.ArgIntegrals` free of hypothesis binders.
- `Jensen.JensenBounds`: `\S sec:jensenclassic` and `\S sec:refinement-integration`.
- `Jensen.RectangularBounds`: `\S sec:rectangularjensen`.
- `Littlewood.LittlewoodMethod`: `\S sec:littlewood` (through Lemma
  `\ref{lem:littlewood-argsetup}`), including the construction of the tex's `arg ζ`
  (`argZetaDef`).
- `Common.RectangleResidue`: the residue theorem on a rectangle (generic complex analysis).
- `Littlewood.LittlewoodIdentity`: Littlewood's identity `\ref{eq:zerodensityintegral}`
  (Equation 13), **proved**, not assumed (from Farzanfard's thesis Lemma 2.2 / Titchmarsh §9.9),
  and Equation `\ref{eq:simplelittlewoodzerodensity}` (Equation 14).
- `Littlewood.ArgIntegrals`: `\S sec:argintegrals`.
- `Littlewood.LittlewoodShort`: `\S sec:littlewoodshortapp` (Theorem
  `\ref{thm:littlewoodshort}`).
- `Background.BackgroundZetaBounds`: Appendix `\S sec:background`.
- `MainTerms`: the main and error terms `U_J`, `U_L`, `E_J`, `E_L` (and the `α < 1/6` threshold)
  of Theorems `\ref{thm:main-jensen}`/`\ref{thm:main-littlewood}`, split out on 2026-09-06 so that
  both `MainTheoremTight` and `MainTheorem` can import them.
- `ConstantSigns`: non-negativity of the `B_{i,α,r}`/`A_{i,α,r}` coefficients and `-A₂ ≤ A₃`
  (moved from `MainCorollary` on 2026-09-06; `c3_nonneg`, its last `sorry`, proved 2026-09-08).
- `MainTheoremTight`: the sharper regime forms of Theorems 2 and 3 (`t > 10^12`, `0 < h ≤ t^{2/3}`,
  un-collapsed error brackets), both proved.
- `MainTheorem`: Theorems `\ref{thm:main-jensen}`/`\ref{thm:main-littlewood}` as the tex states
  them (`0 ≤ h ≤ t^{2/3}`, collapsed errors), **proved** since 2026-09-06 from `MainTheoremTight`
  for `t > 10^12` and from Platt–Trudgian (the count vanishes) plus `ConstantSigns` for
  `t ≤ 10^12`; the only departure from the tex is a lower bound `t ≥ e` resp. `t ≥ e^e` in place of
  "for any `t`" — see that file's module docstring.
- `MainCorollary`: the `U`/`L`/`h₀`/`C₂` monotonicity machinery behind
  `\ref{cor:main-jensen}`/`\ref{cor:main-littlewood}` (Corollaries 4 and 5), including the affine
  decomposition `C₂ᴸ = (P(t)h + Q(t))/(S(t)h - W(t))` that `PositiveProportion` takes the limit
  of, and the antitonicity of `C₂` in both `h₀` and `t₀`.
- `Reflection`: the map `ρ ↦ 1 - conj ρ`.  It preserves the order of vanishing of `ζ` off the
  real axis (the functional equation's multiplier is analytic and zero-free there), so a window's
  two edge strips `Re ρ < α` and `Re ρ > 1-α` carry equally many zeros.  That is the factor of two
  in every proportion statement of the paper, which the tex leaves implicit.
- `HalvingConvention`: Theorems 2, 3, 32 and Corollaries 4, 5 restated for the tex's page-1
  count `Nhalf` (boundary zeros with half their multiplicity, `Definitions.Nhalf`), with no
  zero-free-edge hypotheses, and the introduction's headline Corollary `\ref{cor:simpmain}`
  (Corollary 1) in both mechanisms (`simpleProportionCorollary_jensen`/`_littlewood`), in the
  displayed, the division-free and, using `Reflection`, the prose form.  Nothing here settles the
  sign of the constant; that is `PositiveProportion`.
- `PositiveProportion`: Corollary `\ref{cor:simpmain}` (Corollary 1) in the tex's own existential
  form, "for `h₀` and `t₀` sufficiently large", with the constant proved **positive**. Everything
  in `HalvingConvention` proves the inequality at a caller-supplied `(h₀,t₀)` and is silent about
  the sign of `C`, so on its own it is compatible with `C < 0`. The positivity needs no interval
  arithmetic: `C₂ᴸ → 2A₁` as `h,t → ∞` because every other term carries a `1/h` or `1/log t`, and
  what remains is `4A₁ < 1`, exact rational arithmetic once `α`, `r`, `k` are fixed. There is no
  side condition at all, because `r = 1/2` always works: `σ₀ = 1/2`, so `1-r` is a chord endpoint,
  the numerator of `A₁` collapses to `v₀ = 1/6` whatever the slope, and `4A₁ = (1/3)/(1/2-α) < 1`
  is exactly `α < 1/6` — the paper's own hypothesis. `positiveProportion_of_lt_sixth` is the
  paper's sentence: for `0 < α < 1/6` the proportion exceeds an explicit positive constant.
  `r = 1/2` is the choice that always works, not the best one: `r = 1/5` at `α = 1/16` gives a
  limiting `9/25` against `r = 1/2`'s `5/21`. The five limits are unconditional (2026-09-11).
- `AllHypotheses`: `ZeroDensityHypotheses`, the six classes bundled into one, and the headline
  theorems and corollaries restated under that single binder. This is the shape a Palomar
  Registry submission wants.
-/
