/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Definitions
import ZerosInShortIntervals.Jensen.RectangularBounds
import ZerosInShortIntervals.Littlewood.LittlewoodShort
import ZerosInShortIntervals.Background.ExternalFacts
import ZerosInShortIntervals.MainTerms

/-! # Sharper forms of Theorems `\ref{thm:main-jensen}`/`\ref{thm:main-littlewood}`

`ZerosInShortIntervals.MainTheorem` states the two headline theorems exactly as the tex's
introduction prints them, i.e. with their `O^*` errors collapsed to a single term
(`3.35/(D_{r,α} t^{1/3})`) and to two terms (`(1/(t(r-α)))(0.335 + 0.51/log t)`) respectively.
This file states the **sharper, un-collapsed** intermediate forms, which the tex gives inside
`Theorem \ref{thm:rectangularjensen}` (Theorem 24, tex lines 818–821) and
`Theorem \ref{thm:littlewoodshort}` (Theorem 32, tex lines 1161–1164) themselves as the
"if in addition `t > 10^12` and `h < t^{2/3}`" simplifications, before the final absorption step:

* Jensen: `(1/D_{r,α})(3.34/t^{1/3} + 4.01/t^{4/3} + 291/(t^{4/3}log t))`
* Littlewood: `(1/(t(r-α)))(0.334 + 0.502/log t + 1.001/t + 72.48/(t log t) + 0.64/t^{1/3}
  + 46.3/(t^{1/3}log t))`

Both are strictly stronger than their collapsed counterparts in `MainTheorem`, at the cost of
being stated only on the regime `t > 10^12`, `0 < h ≤ t^{2/3}` where those simplifications are
valid — whereas `MainTheorem.mainJensen`/`mainLittlewood` also cover `t ≤ 10^12` and `h = 0`,
where the count vanishes. That is the whole difference between the two files, and it is why both
are worth having. **Import direction:** this file imports
`ZerosInShortIntervals.MainTerms` (the `U`/`E` definitions) and is in turn imported by
`MainTheorem`, whose proofs of Theorems 2 and 3 consume `mainJensenTight`/`mainLittlewoodTight`
for `t > 10^12`. The hypothesis `h ≤ t^{2/3}` is non-strict, one notch more general than the
tex's `h < t^{2/3}`: every proof below only uses `h ≤ t/10000`, and the non-strict form is what
lets `MainTheorem` take the tex's `t^{2/3} ≥ h` at face value.

**How the two proofs are organised.** Each is reduced first to a single free-variable arithmetic
residue mentioning no zero-counting function (`jensenTight_collapse`,
`littlewoodTight_collapse`), and each residue is then split into per-term lemmas stated over free
variables in exactly the shape the goal presents — three for Jensen, six for Littlewood, the
latter against *half* their targets and applied once per arc. The splitting is not cosmetic: the
monolithic forms time out in `runSimplexAlgorithm`, whereas each small context is one fraction
against one fraction after `div_le_div_iff₀`. -/

/-! ### Regime facts for `t > 10^12`, `0 < h ≤ t^{2/3}`

Both theorems below live on the same regime, and both need the same handful of consequences of
it. They are isolated here so the two collapses can be stated over free variables. -/

/- Unproved inputs enter through the hypothesis classes of `ZerosInShortIntervals/Hypotheses.lean`.
Lean includes an instance-implicit section variable in every theorem in scope, so some statements
carry a binder they do not use; the linter for that is silenced. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs] [InterpolationCertificates]
  [Hcompact2Certificates] [NumericCertificates] [LaurentCertificate]

/-- **`10^4 ≤ t^{1/3}` for `t > 10^12`** — the cube-root half of the "hybrid substitution" step of
the tex's proof; `rpow_two_thirds_le_div` is the other half.

### Summary of Proof
`(10^4)^3 = 10^12 < t`, and `x ↦ x^{1/3}` is monotone.

### Lean Notes
Together with `rpow_two_thirds_le_div` this is what lets `h`, which enters only through
denominators like `t-h` and `τ-r`, be replaced by the clean bound `t/10000` rather than dragging
the fractional power `t^{2/3}` through logs and squares. The tex uses the same device; see
`mainLittlewoodTight`'s Summary of Proof.

### References
tex: the `t > 10^12`, `h < t^{2/3}` simplification inside `\ref{thm:littlewoodshort}`
(Theorem 32), tex lines 1161–1164.

### Dependencies
**Depends on:** none.
**Used by:** `rpow_two_thirds_le_div`, `jensenTight_collapse`, `littlewoodTight_collapse`,
`MainTheorem.jensen_error_collapse`, `MainTheorem.littlewood_error_collapse`. -/
theorem ten_thousand_le_rpow_third {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := by
  have hpow : ((10000 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = 10000 := by
    rw [← Real.rpow_natCast (10000 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10000)]
    norm_num
  have h12 : ((10000 : ℝ) ^ (3 : ℕ)) ≤ t := by nlinarith
  calc (10000 : ℝ) = ((10000 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := hpow.symm
    _ ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) h12 (by norm_num)

/-- **`t^{2/3} ≤ t/10000` for `t > 10^12`** — the "hybrid substitution" step (see the companion
`ten_thousand_le_rpow_third`).

### Summary of Proof
`t^{2/3} = t / t^{1/3}`, and `ten_thousand_le_rpow_third` gives `10000 ≤ t^{1/3}` on this range,
so dividing `t > 0` by the larger denominator only shrinks it.

### Lean Notes
Stated with `t/10000` rather than `t^{2/3}` because every downstream use needs a bound that is
LINEAR in `t`: it is what lets `h`, which enters the error terms only through `h ≤ t^{2/3}`, be
absorbed into a multiple of `t` and the whole collapse be run by `linarith`.

### References
tex: the "hybrid substitution" in the proof of Theorem `\ref{thm:littlewoodshort}` (Theorem 32).

### Dependencies
**Depends on:** `ten_thousand_le_rpow_third`.
**Used by:** `jensenTight_collapse`, `littlewoodTight_collapse`, `mainJensenTight`,
`mainLittlewoodTight`, `HalvingConvention.Nhalf_one_pos`,
`HalvingConvention.mainPositiveProportionCorollary_jensen_half`,
`HalvingConvention.mainPositiveProportionCorollary_littlewood_half`,
`HalvingConvention.simpleProportionCorollary_jensen_prose`,
`HalvingConvention.simpleProportionCorollary_littlewood_prose`,
`MainCorollary.mainPositiveProportionCorollary_jensen`,
`MainCorollary.mainPositiveProportionCorollary_littlewood`. -/
theorem rpow_two_thirds_le_div {t : ℝ} (ht : (10 : ℝ) ^ (12 : ℕ) < t) :
    t ^ ((2 : ℝ) / 3) ≤ t / 10000 := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hcube : (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := ten_thousand_le_rpow_third ht
  have hsplit : t = t ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add ht0]; norm_num
  have h23 : (0 : ℝ) < t ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos ht0 _
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)]
  nlinarith [mul_nonneg h23.le (by linarith : (0 : ℝ) ≤ t ^ ((1 : ℝ) / 3) - 10000)]

/-- **`hatAlpha r α < 1` for `0 < α < r < 1`.**

### Summary of Proof
`α̂_r = √(r²-α²) ≤ √(r²) = r < 1`.

### References
tex: `α̂_r` as defined for `\ref{thm:rectangularjensen}` (Theorem 24).

### Dependencies
**Depends on:** `hatAlpha`.
**Used by:** `mainJensenTight`, `jensenTight_collapse`. -/
theorem hatAlpha_lt_one {r α : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1) :
    hatAlpha r α < 1 := by
  have hr0 : (0 : ℝ) < r := hα0.trans hαr
  have h : Real.sqrt (r ^ 2 - α ^ 2) ≤ Real.sqrt (r ^ 2) := by
    apply Real.sqrt_le_sqrt; nlinarith
  rw [Real.sqrt_sq hr0.le] at h
  exact lt_of_le_of_lt h hr1

/-- **Abstract form of the first collapse term:** `5A/(3W) ≤ 1.7/u`.

### Summary of Proof
Cross-multiplying, `5Au ≤ 5(t+u)` and `1.7·3W ≥ 5.1·(4999/5000)t`, so the claim reduces to
`5u ≤ 0.09898t`, which `u·10⁸ ≤ t` gives with room to spare.

### Lean Notes
Stated over free variables with no `rpow` in sight — `u` stands for `t^{1/3}`, `A` for `h + α̂_r`,
`W` for the window `t-h-α̂_r-1`. Keeping each term's arithmetic in its own small context is what
makes `nlinarith` tractable here; the combined form times out.

### References
tex: first piece of `\ref{thm:rectangularjensen}` (Theorem 24)'s tight error.

### Dependencies
**Depends on:** none.
**Used by:** `jensenTight_collapse`. -/
private theorem tight_term_one {A W u t : ℝ} (_ht0 : 0 < t) (hu0 : 0 < u) (_hW0 : 0 < W)
    (hAu : A * u ≤ t + u) (hW : (4999 / 5000 : ℝ) * t ≤ W) (hut : u * 100000000 ≤ t) :
    5 * A / (3 * W) ≤ 1.7 / u := by
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 3 * W) hu0]
  nlinarith [hAu, hW, hut]

/-- **Abstract form of the second collapse term:** `2A/W² ≤ 2.01/(tu)`.

### Summary of Proof
Cross-multiplying, `2A·tu ≤ 2t(t+u)` and `2.01W² ≥ 2.01(4999/5000)²t²`, so the claim reduces to
`2u ≤ 0.00919t`, again immediate from `u·10⁸ ≤ t`.

### References
tex: second piece of `\ref{thm:rectangularjensen}` (Theorem 24)'s tight error.

### Dependencies
**Depends on:** none.
**Used by:** `jensenTight_collapse`. -/
private theorem tight_term_two {A W u t : ℝ} (ht0 : 0 < t) (hu0 : 0 < u) (hW0 : 0 < W)
    (hAu : A * u ≤ t + u) (hW : (4999 / 5000 : ℝ) * t ≤ W) (hut : u * 100000000 ≤ t) :
    2 * A / W ^ 2 ≤ 2.01 / (t * u) := by
  rw [div_le_div_iff₀ (pow_pos hW0 2) (mul_pos ht0 hu0)]
  nlinarith [mul_le_mul_of_nonneg_left hAu ht0.le,
    mul_le_mul_of_nonneg_left hut ht0.le,
    mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (4999 / 5000 : ℝ) * t) hW, ht0, hu0]

/-- **Abstract form of the third collapse term:** `1158A/(8W²·L_W) ≤ 145/(tu·L_t)`.

### Summary of Proof
Cross-multiplying, the left side is at most `1158(t+u)·t·L_t` and the right at least
`1160·(4999/5000)²(9999/10000)·t²L_t = 1159.42 t²L_t`, so the claim reduces to
`1158(t+u) ≤ 1159t`, immediate from `u·10⁸ ≤ t`.

### Lean Notes
`L_W` and `L_t` stand for `log W` and `log t`; the only fact needed relating them is
`L_W ≥ (9999/10000)L_t`, which comes from `W ≥ (4999/5000)t` and `log x ≤ x-1`. The two
multiplications (by `t·L_t`, and of the two lower bounds together) are supplied as explicit
hints, since `nlinarith` does not find degree-4 products reliably.

### References
tex: third piece of `\ref{thm:rectangularjensen}` (Theorem 24)'s tight error.

### Dependencies
**Depends on:** none.
**Used by:** `jensenTight_collapse`. -/
private theorem tight_term_three {A W u t LW Lt : ℝ} (ht0 : 0 < t) (hu0 : 0 < u)
    (hW0 : 0 < W) (hLt0 : 0 < Lt) (hAu : A * u ≤ t + u)
    (hW : (4999 / 5000 : ℝ) * t ≤ W) (hLW : (9999 / 10000 : ℝ) * Lt ≤ LW)
    (hut : u * 100000000 ≤ t) :
    1158 * A / (8 * W ^ 2 * LW) ≤ 145 / (t * u * Lt) := by
  have hLW0 : (0 : ℝ) < LW := by linarith
  have htL : (0 : ℝ) ≤ t * Lt := mul_nonneg ht0.le hLt0.le
  rw [div_le_div_iff₀
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (pow_pos hW0 2)) hLW0)
    (mul_pos (mul_pos ht0 hu0) hLt0)]
  have h1 : A * u * (t * Lt) ≤ (t + u) * (t * Lt) :=
    mul_le_mul_of_nonneg_right hAu htL
  have h2 : ((4999 / 5000 : ℝ) * t) ^ 2 * ((9999 / 10000 : ℝ) * Lt) ≤ W ^ 2 * LW := by
    refine mul_le_mul ?_ hLW (by linarith) (by positivity)
    nlinarith [hW, hW0, ht0]
  have h3 : 1158 * (t + u) ≤ 1159 * t := by nlinarith [hut, ht0]
  have h4 : 1158 * (t + u) * (t * Lt) ≤ 1159 * t * (t * Lt) :=
    mul_le_mul_of_nonneg_right h3 htL
  nlinarith [h1, h2, h4, ht0, hLt0, mul_pos ht0 hLt0]

/-- **The arithmetic core of `mainJensenTight`**, over free variables: Theorem 24's tight error
bracket is below the three-term target.

### Summary of Proof
Writing `W := t - h - α̂_r - 1`, the regime gives `W ≥ (4999/5000)t` (from `h ≤ t/10000`,
`α̂_r < 1`, `t > 10^12`) and `log W ≥ (9999/10000)log t`. With `h + α̂_r ≤ t^{2/3} + 1` the three
pieces bound as

| Theorem 24 piece | bound | target |
|---|---|---|
| `5(h+α̂)/(3W)` | `1.667/t^{1/3}` | `3.34/t^{1/3}` |
| `2(h+α̂)/W²` | `2.001/t^{4/3}` | `4.01/t^{4/3}` |
| `1158(h+α̂)/(8W² log W)` | `144.9/(t^{4/3}log t)` | `291/(t^{4/3}log t)` |

### Lean Notes
**Every margin here is roughly a factor of two**, unlike `littlewoodTight_collapse`, whose
tightest term has 0.09% to spare. That is why this one is stated with a strict `<` — which is
also what `mainJensenTight` needs, since `rectangularjensen_tight` supplies only `≤`.

The care needed is that `h` enters the numerators as `t^{2/3}` (giving the `t^{-1/3}` and
`t^{-4/3}` rates) while entering `W` only as `t/10000`.

### References
tex: the `t > 10^12`, `h < t^{2/3}` simplification inside `\ref{thm:rectangularjensen}`
(Theorem 24), tex lines 818–821.

### Dependencies
**Depends on:** `hatAlpha`, `rpow_two_thirds_le_div`, `hatAlpha_lt_one`,
`ten_thousand_le_rpow_third`, `twenty_lt_log`, `tight_term_one`, `tight_term_two`,
`tight_term_three`.
**Used by:** `mainJensenTight`. -/
theorem jensenTight_collapse {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) (_hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    5 * (h + hatAlpha r α) / (3 * (t - h - hatAlpha r α - 1))
        + (2 * (h + hatAlpha r α) / (t - h - hatAlpha r α - 1) ^ 2
            + 1158 * (h + hatAlpha r α)
                / (8 * (t - h - hatAlpha r α - 1) ^ 2
                    * Real.log (t - h - hatAlpha r α - 1)))
      < 3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
        + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have htbig : (1000000000000 : ℝ) < t := by nlinarith
  have hA1 : hatAlpha r α < 1 := hatAlpha_lt_one hα0 hαr hr1
  have hht : h ≤ t / 10000 := le_trans hh (rpow_two_thirds_le_div ht)
  -- cube-root bookkeeping
  have hu0 : (0 : ℝ) < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht0 _
  have hu4 : (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := ten_thousand_le_rpow_third ht
  have huv : t ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have h43 : t ^ ((4 : ℝ) / 3) = t * t ^ ((1 : ℝ) / 3) := by
    rw [show ((4 : ℝ) / 3) = 1 + (1 : ℝ) / 3 by norm_num, Real.rpow_add ht0, Real.rpow_one]
  have hcube : (t ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = t := by
    rw [← Real.rpow_natCast (t ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul ht0.le]; norm_num
  -- `t^{1/3} ≤ t/10^8`, the slack that makes every margin below comfortable
  have husq : (100000000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
    nlinarith [hu4, hu0]
  have hut8 : t ^ ((1 : ℝ) / 3) * 100000000 ≤ t := by
    nlinarith [hcube, mul_le_mul_of_nonneg_left husq hu0.le]
  -- the numerator bound `(h + α̂)·t^{1/3} ≤ t + t^{1/3}`
  have hAu : (h + hatAlpha r α) * t ^ ((1 : ℝ) / 3) ≤ t + t ^ ((1 : ℝ) / 3) := by
    have hha : h + hatAlpha r α ≤ t ^ ((2 : ℝ) / 3) + 1 := by linarith
    calc (h + hatAlpha r α) * t ^ ((1 : ℝ) / 3)
        ≤ (t ^ ((2 : ℝ) / 3) + 1) * t ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right hha hu0.le
      _ = t + t ^ ((1 : ℝ) / 3) := by rw [add_mul, one_mul, huv]
  -- the window `W` and its two denominator bounds
  set W : ℝ := t - h - hatAlpha r α - 1 with hWdef
  have hW : (4999 / 5000 : ℝ) * t ≤ W := by rw [hWdef]; linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogt : (20 : ℝ) < Real.log t := twenty_lt_log ht
  have hlogW : (9999 / 10000 : ℝ) * Real.log t ≤ Real.log W := by
    have h1 : Real.log ((4999 / 5000 : ℝ) * t) ≤ Real.log W :=
      Real.log_le_log (by positivity) hW
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0)] at h1
    have h2 : (-(1 : ℝ) / 4999) ≤ Real.log ((4999 : ℝ) / 5000) := by
      have h3 := Real.log_le_sub_one_of_pos (x := (5000 : ℝ) / 4999) (by norm_num)
      rw [show ((5000 : ℝ) / 4999) = ((4999 : ℝ) / 5000)⁻¹ by norm_num, Real.log_inv] at h3
      linarith
    linarith
  -- the three per-term bounds, each discharged in the small abstract context
  have hT1 := tight_term_one ht0 hu0 hW0 hAu hW hut8
  have hT2 := tight_term_two ht0 hu0 hW0 hAu hW hut8
  have hT3 :=
    tight_term_three ht0 hu0 hW0 (by linarith : (0 : ℝ) < Real.log t) hAu hW hlogW hut8
  -- combine: each bound is strictly below its target
  rw [h43]
  have hd2 : (0 : ℝ) < t * t ^ ((1 : ℝ) / 3) := mul_pos ht0 hu0
  have hd3 : (0 : ℝ) < t * t ^ ((1 : ℝ) / 3) * Real.log t :=
    mul_pos hd2 (by linarith)
  have hs1 : (1.7 : ℝ) / t ^ ((1 : ℝ) / 3) < 3.34 / t ^ ((1 : ℝ) / 3) := by
    rw [div_lt_div_iff₀ hu0 hu0]; nlinarith [hu0]
  have hs2 : (2.01 : ℝ) / (t * t ^ ((1 : ℝ) / 3)) < 4.01 / (t * t ^ ((1 : ℝ) / 3)) := by
    rw [div_lt_div_iff₀ hd2 hd2]; nlinarith [hd2]
  have hs3 : (145 : ℝ) / (t * t ^ ((1 : ℝ) / 3) * Real.log t)
      < 291 / (t * t ^ ((1 : ℝ) / 3) * Real.log t) := by
    rw [div_lt_div_iff₀ hd3 hd3]; nlinarith [hd3]
  linarith [hT1, hT2, hT3, hs1, hs2, hs3]

/-- **`Theorem \ref{thm:main-jensen}` (Theorem 2), sharper form.** On the regime `t > 10^12`,
`0 < h ≤ t^{2/3}`, the Jensen-mechanism error is the three-term
`(1/D_{r,α})(3.34/t^{1/3} + 4.01/t^{4/3} + 291/(t^{4/3}log t))`, sharper than
`MainTheorem.EJensen`'s collapsed `3.35/(D_{r,α}t^{1/3})`.

### Summary of Proof
`Theorem \ref{thm:rectangularjensen}` (Theorem 24)'s `O^*` error is `(1/D_{r,α})` times a sum of
three pieces, each carrying the factor `(h+α̂_r)` in its numerator and a power of
`(t-h-α̂_r-1)` in its denominator. Under `h < t^{2/3}` and `t > 10^12` one bounds `h+α̂_r` above
and `t-h-α̂_r-1` below by clean multiples of `t`, collapsing the three pieces to the displayed
`t^{-1/3}`, `t^{-4/3}`, `t^{-4/3}(log t)^{-1}` rates. Because every term carries `(h+α̂_r)` and
`h` may be as large as `t^{2/3}`, the overall decay is only `O(t^{-1/3})` — not `O(1/t)`. That is
why the Jensen error has a `t^{1/3}` in its denominator where the Littlewood one has a `t`.

### Lean Notes
The `α < 1/6` hypothesis is `\ref{thm:main-jensen}`'s (Theorem 2), carried to match the tex;
`0 < α < r < 1` is `\ref{thm:rectangularjensen}`'s (Theorem 24), which asks only `α ≤ 1` of the
route actually taken. The regime hypotheses `t > 10^12` and `0 < h ≤ t^{2/3}` are explicit here,
whereas `MainTheorem.mainJensen` also covers `t ≤ 10^12` and `h = 0` (where the count is zero) —
that restriction is exactly what buys the sharper error. `h ≤ t^{2/3}` is non-strict where the
tex writes `h < t^{2/3}`; the proof only uses `h ≤ t/10000`, and `MainTheorem.mainJensen` needs
the non-strict form to match the tex's `t^{2/3} ≥ h`. The three-term bracket matches the printed
simplification at tex line 820 exactly.

**`0 < h` cannot be dropped**, and the reason is not that `rectangularjensen_tight` happens to
require it. For `h ≤ 0` the interval `(t-h, t+h)` is empty, so `Nrect = 0` and the claim reduces
to `0 < U_J + error`; but `UJensen` is affine in `h` with strictly positive slope (the `log log t`
coefficient `B2` is positive), so `h → -∞` drives the right side to `-∞`. Checked for the
Littlewood analogue, whose slope has the same shape, in `Code/verify_mainTight_h_sign.py`. The
`h = 0` endpoint is recovered in `MainTheorem.mainJensen`, where the window is empty and the
claim is the positivity of the right-hand side.

The other hypotheses of `rectangularjensen_tight` come free: `13 < t - h - α̂_r` because
`h ≤ t^{2/3}` and `t > 10^12` give `h ≤ t/10000`, and `α̂_r = √(r²-α²) < 1` (`hatAlpha_lt_one`).
Theorem 2's case split does not enter: it is what makes `MainTheorem.mainJensen` true down to
`t ≥ e`, whereas this statement lives squarely inside the single case Theorem 24 covers.

### References
tex: `\ref{thm:main-jensen}` (Theorem 2), sharpened by the `t > 10^12`, `h < t^{2/3}`
simplification printed inside `\ref{thm:rectangularjensen}` (Theorem 24), tex lines 818–821.

### Dependencies
**Depends on:** `UJensen`, `Nrect`, `rectDenom`, `rectDenom_pos`, `hatAlpha_lt_one`,
`rpow_two_thirds_le_div`, `rectangularjensen_tight`, `jensenTight_collapse`.
**Used by:** `MainTheorem.mainJensen`. -/
theorem mainJensenTight {α r h t : ℝ} (hα0 : 0 < α) (hαr : α < r) (hr1 : r < 1)
    (hα : α < 1 / 6) (ht : (10 : ℝ) ^ (12 : ℕ) < t) (hh0 : 0 < h)
    (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    (Nrect (t - h) (t + h) α : ℝ)
      < UJensen α r h t
        + (1 / rectDenom r α) *
            (3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
              + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t)) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hA1 : hatAlpha r α < 1 := hatAlpha_lt_one hα0 hαr hr1
  have hA0 : (0 : ℝ) ≤ hatAlpha r α := Real.sqrt_nonneg _
  have hD : (0 : ℝ) < rectDenom r α := rectDenom_pos hα0 hαr
  have hht : h ≤ t / 10000 := le_trans hh (rpow_two_thirds_le_div ht)
  have hT13 : (13 : ℝ) < t - h - hatAlpha r α := by nlinarith
  have hmain := rectangularjensen_tight (T := t) (h := h) (α := α) (r := r)
    hα0 (by linarith) hαr hr1 hh0 hT13
  rw [abs_of_pos ht0] at hmain
  have hU : (2 * h + 2 * hatAlpha r α) *
      (B1 α r / Real.pi * Real.log t + B2 α r * Real.log (Real.log t) + B3 α r)
      + B4 α r = UJensen α r h t := rfl
  rw [hU] at hmain
  refine lt_of_le_of_lt hmain ?_
  -- only the error bracket remains, and the shared `1/D` factor is common to both sides
  have hcol := jensenTight_collapse (α := α) (r := r) (h := h) (t := t) hα0 hαr hr1 ht hh0 hh
  have hkey : (5 * (h + hatAlpha r α) / (3 * (t - h - hatAlpha r α - 1))
        + (2 * (h + hatAlpha r α) / (t - h - hatAlpha r α - 1) ^ 2
            + 1158 * (h + hatAlpha r α)
                / (8 * (t - h - hatAlpha r α - 1) ^ 2
                    * Real.log (t - h - hatAlpha r α - 1)))) / rectDenom r α
      < (1 / rectDenom r α) *
          (3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
            + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t)) := by
    rw [div_lt_iff₀ hD]
    have hexp : (1 / rectDenom r α) *
        (3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
          + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t)) * rectDenom r α
        = 3.34 / t ^ ((1 : ℝ) / 3) + 4.01 / t ^ ((4 : ℝ) / 3)
          + 291 / (t ^ ((4 : ℝ) / 3) * Real.log t) := by
      field_simp
    rw [hexp]
    exact hcol
  linarith [hkey]

/-- **`log X ≥ (49999/50000) log t` whenever `X ≥ (4999/5000) t`** and `log t ≥ 20`.

### Summary of Proof
`log X ≥ log(4999/5000) + log t`, and `log(4999/5000) = -log(5000/4999) ≥ -(5000/4999 - 1)
= -1/4999` by `log x ≤ x - 1`. So `log X ≥ log t - 1/4999`, which beats `(49999/50000) log t`
as soon as `log t ≥ 50000/4999 ≈ 10.01`.

### Lean Notes
The `log t ≥ 20` hypothesis is what makes the *relative* loss uniform: an additive loss of
`1/4999` is a relative loss of at most `1/(4999·20) < 1/50000`.

### Dependencies
**Depends on:** none.
**Used by:** `littlewoodTight_collapse`. -/
private theorem log_lb {t X : ℝ} (ht0 : 0 < t) (hL : (20 : ℝ) ≤ Real.log t)
    (hX : (4999 / 5000 : ℝ) * t ≤ X) :
    (49999 / 50000 : ℝ) * Real.log t ≤ Real.log X := by
  have h1 : Real.log ((4999 / 5000 : ℝ) * t) ≤ Real.log X :=
    Real.log_le_log (by positivity) hX
  rw [Real.log_mul (by norm_num) (ne_of_gt ht0)] at h1
  have h2 : (-(1 : ℝ) / 4999) ≤ Real.log ((4999 : ℝ) / 5000) := by
    have h3 := Real.log_le_sub_one_of_pos (x := (5000 : ℝ) / 4999) (by norm_num)
    rw [show ((5000 : ℝ) / 4999) = ((4999 : ℝ) / 5000)⁻¹ by norm_num, Real.log_inv] at h3
    linarith
  linarith

/-!
### The six per-term bounds of `littlewoodTight_collapse`

Each is stated over free variables in exactly the shape the collapse's goal presents after
distributing `t` across the bracket, so the assembly needs no rewriting at the call site: `u`
stands for `t^{1/3}` (with `u^3 = t` and `h ≤ u^2` encoding the regime `h < t^{2/3}`), `P` for
`π`, `L` for `log t`, `W` for `t-h`, `S` for one of the two shifted denominators `t±h-r`, `LW`
and `LS` for the logarithms of those, and `D` for the difference `log(t±h) - r/S`.

The four `B` bounds are stated against *half* the corresponding target, and applied once per
arc. That is what keeps every `nlinarith` down to one fraction against one fraction after
`div_le_div_iff₀`: cross-multiplying a sum of two fractions with distinct degree-2 denominators
is exactly the shape that times out. Verified numerically in
`Code/verify_mainLittlewoodTight_collapse.py` — the worst per-arc ratio over
`t ∈ [10^12, 10^40]` is `0.9992` (the `t-h` arc of the `2/(τ-r)^2` term).

That sweep fixes `r = 1` and `h = t^{2/3}`, so on its own it only checks an endpoint. What
makes the endpoint the worst case is the *shape of the lemmas*, not the sweep: each `B` bound
uses `r` only through `r ≤ 1`, and each `A` bound uses `h` only through `h ≤ u^2`, so both are
discharged at the endpoint and hold monotonically below it. The sweep's role is to confirm the
endpoint clears at all — the uniformity is the proofs'.
-/

/-- **`t·2h/(π(t-h)²) ≤ 0.64/t^{1/3}`.** Cross-multiplied: `2u⁴h ≤ 2u⁶` against
`0.64·P·W² ≥ 0.64·3.14·(4999/5000)²u⁶ = 2.0088u⁶`. Needs only `π ≥ 3.1263`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `linarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_A1 {t h u P W : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t)
    (hh : h ≤ u ^ 2) (hP : (3.14 : ℝ) ≤ P) (hW : (4999 / 5000 : ℝ) * t ≤ W) :
    t * (2 * h / (P * W ^ 2)) ≤ 0.64 / u := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hc : (0 : ℝ) ≤ (4999 / 5000 : ℝ) * u ^ 3 := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  rw [show u ^ 3 * (2 * h / (P * W ^ 2)) = 2 * u ^ 3 * h / (P * W ^ 2) from by ring,
    div_le_div_iff₀ (mul_pos hP0 (pow_pos hW0 2)) hu0]
  have k1 : 2 * u ^ 3 * h * u ≤ 2 * u ^ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hh (pow_nonneg hu0.le 4)]
  have k3 : (3.14 : ℝ) * (((4999 / 5000 : ℝ) * u ^ 3) * ((4999 / 5000 : ℝ) * u ^ 3))
      ≤ P * (W * W) :=
    mul_le_mul hP (mul_self_le_mul_self hc hW) (mul_nonneg hc hc) hP0.le
  linarith [k1, k3, pow_pos hu0 6]

/-- **`t·1158h/(8π(t-h)²log(t-h)) ≤ 46.3/(t^{1/3}log t)`.** Cross-multiplied: `1158u⁶L` against
`46.3·8·3.14·(4999/5000)²(49999/50000)·u⁶L = 1162.5u⁶L`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `nlinarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_A2 {t h u P W L LW : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t)
    (hh : h ≤ u ^ 2) (hP : (3.14 : ℝ) ≤ P) (hW : (4999 / 5000 : ℝ) * t ≤ W)
    (hL : (20 : ℝ) ≤ L) (hLW : (49999 / 50000 : ℝ) * L ≤ LW) :
    t * (1158 * h / (8 * P * W ^ 2 * LW)) ≤ 46.3 / (u * L) := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hc : (0 : ℝ) ≤ (4999 / 5000 : ℝ) * u ^ 3 := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLW0 : (0 : ℝ) < LW := by linarith
  rw [show u ^ 3 * (1158 * h / (8 * P * W ^ 2 * LW))
        = 1158 * u ^ 3 * h / (8 * P * W ^ 2 * LW) from by ring,
    div_le_div_iff₀
      (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hP0) (pow_pos hW0 2)) hLW0)
      (mul_pos hu0 hL0)]
  have k1 : 1158 * u ^ 3 * h * (u * L) ≤ 1158 * u ^ 6 * L := by
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (pow_nonneg hu0.le 4) hL0.le)]
  have k3 : (3.14 : ℝ) * (((4999 / 5000 : ℝ) * u ^ 3) * ((4999 / 5000 : ℝ) * u ^ 3))
      ≤ P * (W * W) :=
    mul_le_mul hP (mul_self_le_mul_self hc hW) (mul_nonneg hc hc) hP0.le
  have k4 : ((3.14 : ℝ) * (((4999 / 5000 : ℝ) * u ^ 3) * ((4999 / 5000 : ℝ) * u ^ 3)))
      * ((49999 / 50000 : ℝ) * L) ≤ (P * (W * W)) * LW :=
    mul_le_mul k3 hLW (by linarith) (by nlinarith [mul_nonneg hc hc])
  nlinarith [k1, k4]

/-- **One arc of `t·(r/4)·(2/3)(r/(τ-r)) ≤ 0.167`** (half of the `0.334` target). Reduces to
`u³r² ≤ 1.002·(4999/5000)u³`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `nlinarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_B1 {t u r S : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hS : (4999 / 5000 : ℝ) * t ≤ S) :
    t * (r / 4) * (2 / 3 * (r / S)) ≤ 0.167 := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hS0 : (0 : ℝ) < S := by linarith
  rw [show u ^ 3 * (r / 4) * (2 / 3 * (r / S)) = u ^ 3 * r ^ 2 / (6 * S) from by ring,
    div_le_iff₀ (by linarith : (0 : ℝ) < 6 * S)]
  nlinarith [hu3, hS, hr0, hr1,
    mul_le_of_le_one_right hu3.le (by nlinarith : r ^ 2 ≤ 1)]

/-- **One arc of `t·(r/4)·(r/(τ-r))/(log τ - r/(τ-r)) ≤ 0.251/log t`** (half of `0.502`).
Reduces to `u³L ≤ 1.004·(4999/5000)(9999/10000)u³L`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `linarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_B2 {t u r S L D : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hS : (4999 / 5000 : ℝ) * t ≤ S) (hL : (20 : ℝ) ≤ L)
    (hD : (9999 / 10000 : ℝ) * L ≤ D) :
    t * (r / 4) * (r / S / D) ≤ 0.251 / L := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hS0 : (0 : ℝ) < S := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hD0 : (0 : ℝ) < D := by linarith
  rw [show u ^ 3 * (r / 4) * (r / S / D) = u ^ 3 * r ^ 2 / (4 * S * D) from by ring,
    div_le_div_iff₀ (mul_pos (by linarith : (0 : ℝ) < 4 * S) hD0) hL0]
  have k1 : u ^ 3 * r ^ 2 * L ≤ u ^ 3 * L := by
    nlinarith [mul_nonneg (mul_pos hu3 hL0).le (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
  have k2 : ((4999 / 5000 : ℝ) * u ^ 3) * ((9999 / 10000 : ℝ) * L) ≤ S * D :=
    mul_le_mul hS hD (by linarith) (by linarith)
  linarith [k1, k2, mul_pos hu3 hL0]

/-- **One arc of `t·(r/4)·2/(τ-r)² ≤ 0.5005/t`** (half of `1.001`). This is the thinnest of the
six — `u⁶` against `1.001·(4999/5000)²u⁶ = 1.0006u⁶`, a margin of `0.06%`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `nlinarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_B3 {t u r S : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t) (_hr0 : 0 < r)
    (hr1 : r ≤ 1) (hS : (4999 / 5000 : ℝ) * t ≤ S) :
    t * (r / 4) * (2 / S ^ 2) ≤ 0.5005 / t := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hc : (0 : ℝ) ≤ (4999 / 5000 : ℝ) * u ^ 3 := by linarith
  have hS0 : (0 : ℝ) < S := by linarith
  rw [show u ^ 3 * (r / 4) * (2 / S ^ 2) = u ^ 3 * r / (2 * S ^ 2) from by ring,
    div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * S ^ 2) hu3]
  have k1 : u ^ 3 * r * u ^ 3 ≤ u ^ 6 := by
    nlinarith [mul_nonneg (mul_pos hu3 hu3).le (by linarith : (0 : ℝ) ≤ 1 - r)]
  nlinarith [k1, mul_self_le_mul_self hc hS]

/-- **One arc of `t·(r/4)·1158/(8(τ-r)²log(τ-r)) ≤ 36.24/(t log t)`** (half of `72.48`).
Reduces to `1158u⁶L ≤ 36.24·32·(4999/5000)²(49999/50000)u⁶L = 1159.2u⁶L`.

### Dependencies
**Depends on:** none — pure arithmetic, closed by `nlinarith` from local `have`s.
**Used by:** `littlewoodTight_collapse`. -/
private theorem lw_B4 {t u r S L LS : ℝ} (hu : (10000 : ℝ) ≤ u) (hut : u ^ 3 = t) (_hr0 : 0 < r)
    (hr1 : r ≤ 1) (hS : (4999 / 5000 : ℝ) * t ≤ S) (hL : (20 : ℝ) ≤ L)
    (hLS : (49999 / 50000 : ℝ) * L ≤ LS) :
    t * (r / 4) * (1158 / (8 * S ^ 2 * LS)) ≤ 36.24 / (t * L) := by
  subst hut
  have hu0 : (0 : ℝ) < u := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hc : (0 : ℝ) ≤ (4999 / 5000 : ℝ) * u ^ 3 := by linarith
  have hS0 : (0 : ℝ) < S := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLS0 : (0 : ℝ) < LS := by linarith
  rw [show u ^ 3 * (r / 4) * (1158 / (8 * S ^ 2 * LS))
        = 1158 * u ^ 3 * r / (32 * S ^ 2 * LS) from by ring,
    div_le_div_iff₀
      (mul_pos (by positivity : (0 : ℝ) < 32 * S ^ 2) hLS0) (mul_pos hu3 hL0)]
  have k1 : 1158 * u ^ 3 * r * (u ^ 3 * L) ≤ 1158 * u ^ 6 * L := by
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hu3 hu3).le hL0.le)
      (by linarith : (0 : ℝ) ≤ 1 - r)]
  have k3 : (((4999 / 5000 : ℝ) * u ^ 3) * ((4999 / 5000 : ℝ) * u ^ 3))
      * ((49999 / 50000 : ℝ) * L) ≤ (S * S) * LS :=
    mul_le_mul (mul_self_le_mul_self hc hS) hLS (by linarith)
      (by nlinarith [mul_pos hS0 hS0])
  nlinarith [k1, k3]

/-- **The arithmetic core of `mainLittlewoodTight`**, over free variables: Theorem 32's error
bracket, multiplied by `t`, is below the six-term target.

### Summary of Proof
Both sides of `mainLittlewoodTight` carry the factor `1/(r-α)`, so it cancels and the entire
content of that theorem is this inequality. The six terms match one-to-one, each target constant
strictly exceeding the limiting value of its piece:

| Theorem 32 piece | limit | target |
|---|---|---|
| `(r/4)·2·(2/3)(r/(τ-r))` | `r²/(3t)` | `0.334/t` |
| `(r/4)·2·(r/(τ-r))/(log τ - r/(τ-r))` | `r²/(2t log t)` | `0.502/(t log t)` |
| `(r/4)·2·2/(τ-r)²` | `r/t²` | `1.001/t²` |
| `(r/4)·2·1158/(8(τ-r)² log(τ-r))` | `72.375r/(t² log t)` | `72.48/(t² log t)` |
| `2h/(π(t-h)²)` | `2/(πt^{4/3})` | `0.64/t^{4/3}` |
| `1158h/(8π(t-h)² log(t-h))` | `46.07/(t^{4/3} log t)` | `46.3/(t^{4/3} log t)` |

The regime enters through `rpow_two_thirds_le_div`: `h` appears in a numerator only in the last
two pieces (where `h ≤ t^{2/3}` gives the genuinely sharper `t^{-4/3}` rate), and everywhere else
only inside a denominator, where the cruder `h ≤ t/10000` keeps `τ-r ≥ (4999/5000)t` and
`log(τ-r) ≥ (9999/10000)log t` clean.

### Lean Notes
The proof is the split into the six per-term bounds above, each discharged from the two
denominator bounds in its own small context — the `LittlewoodShort.Dcombo_bound` idiom — which is
what the thin margins demand. **Two of the six margins are thin, and that is the whole
difficulty.** Checked over `t ∈ [10^12, 10^30]`, `r ∈ (0,1)`, `h ∈ (0, t^{2/3})` in
`Code/verify_mainLittlewoodTight_collapse.py`: worst overall ratio `0.996`, attained as `r → 1`.
Term by term the tightest are the first (`0.3334` against `0.334`, 0.18%) and the fourth (`72.41`
against `72.48`, 0.09%). Both need the denominator bounds carried as exact rationals; a decimal
slip of one part in `10^3` breaks either.

### References
tex: the `t > 10^12`, `h < t^{2/3}` simplification inside `\ref{thm:littlewoodshort}`
(Theorem 32), tex lines 1161–1164.

### Dependencies
**Depends on:** `arcErr_tight`, `rpow_two_thirds_le_div`, `ten_thousand_le_rpow_third`,
`twenty_lt_log`, `log_lb`, and the ten instantiations of `lw_A1`, `lw_A2`, `lw_B1`–`lw_B4`.
**Used by:** `mainLittlewoodTight`. -/
theorem littlewoodTight_collapse {r h t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) (hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3)) :
    t * (2 * h / (Real.pi * (t - h) ^ 2)
        + 1158 * h / (8 * Real.pi * (t - h) ^ 2 * Real.log (t - h))
        + r / 4 * (arcErr_tight r (t + h) + arcErr_tight r (t - h)))
      ≤ 0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
        + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have htbig : (1000000000000 : ℝ) < t := by nlinarith
  have hht : h ≤ t / 10000 := le_trans hh (rpow_two_thirds_le_div ht)
  have hu4 : (10000 : ℝ) ≤ t ^ ((1 : ℝ) / 3) := ten_thousand_le_rpow_third ht
  have hL : (20 : ℝ) ≤ Real.log t := (twenty_lt_log ht).le
  -- name the cube root, then forget that it is one: every bound below is pure algebra in it
  set u : ℝ := t ^ ((1 : ℝ) / 3) with hudef
  clear_value u
  have hu0 : (0 : ℝ) < u := by linarith
  have hut : u ^ 3 = t := by
    rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul ht0.le]
    norm_num
  have hh2 : h ≤ u ^ 2 := by
    have hsq : u ^ 2 = t ^ ((2 : ℝ) / 3) := by
      rw [hudef, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul ht0.le]
      norm_num
    rw [hsq]; linarith
  have hP : (3.14 : ℝ) ≤ Real.pi := Real.pi_gt_d2.le
  -- the three denominators, all at least `(4999/5000)t`
  have hW : (4999 / 5000 : ℝ) * t ≤ t - h := by linarith
  have hSp : (4999 / 5000 : ℝ) * t ≤ t + h - r := by linarith
  have hSm : (4999 / 5000 : ℝ) * t ≤ t - h - r := by linarith
  have hSp0 : (0 : ℝ) < t + h - r := by linarith
  have hSm0 : (0 : ℝ) < t - h - r := by linarith
  -- their logarithms, all at least `(49999/50000)log t`
  have hLW : (49999 / 50000 : ℝ) * Real.log t ≤ Real.log (t - h) := log_lb ht0 hL hW
  have hLSp : (49999 / 50000 : ℝ) * Real.log t ≤ Real.log (t + h - r) := log_lb ht0 hL hSp
  have hLSm : (49999 / 50000 : ℝ) * Real.log t ≤ Real.log (t - h - r) := log_lb ht0 hL hSm
  have hLph : Real.log t ≤ Real.log (t + h) := Real.log_le_log ht0 (by linarith)
  -- the two `log τ - r/(τ-r)` differences: the subtracted quantity is below `1/1000`
  have hqp : r / (t + h - r) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hSp0 (by norm_num)]; linarith
  have hqm : r / (t - h - r) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hSm0 (by norm_num)]; linarith
  have hDp : (9999 / 10000 : ℝ) * Real.log t
      ≤ Real.log (t + h) - r / (t + h - r) := by linarith
  have hDm : (9999 / 10000 : ℝ) * Real.log t
      ≤ Real.log (t - h) - r / (t - h - r) := by linarith
  -- distribute `t` across the bracket and both arcs across `arcErr_tight`
  have hsplit : ∀ X Y E1 E2 : ℝ,
      t * (X + Y + r / 4 * (E1 + E2))
        = t * X + t * Y + (t * (r / 4) * E1 + t * (r / 4) * E2) := by
    intros; ring
  have harc : ∀ a b c d : ℝ,
      t * (r / 4) * (a + b + (c + d))
        = t * (r / 4) * a + t * (r / 4) * b + (t * (r / 4) * c + t * (r / 4) * d) := by
    intros; ring
  rw [hsplit, arcErr_tight, arcErr_tight, harc, harc]
  have b1 := lw_A1 hu4 hut hh2 hP hW
  have b2 := lw_A2 hu4 hut hh2 hP hW hL hLW
  have b3 := lw_B1 hu4 hut hr0 hr1.le hSp
  have b4 := lw_B1 hu4 hut hr0 hr1.le hSm
  have b5 := lw_B2 hu4 hut hr0 hr1.le hSp hL hDp
  have b6 := lw_B2 hu4 hut hr0 hr1.le hSm hL hDm
  have b7 := lw_B3 hu4 hut hr0 hr1.le hSp
  have b8 := lw_B3 hu4 hut hr0 hr1.le hSm
  have b9 := lw_B4 hu4 hut hr0 hr1.le hSp hL hLSp
  have b10 := lw_B4 hu4 hut hr0 hr1.le hSm hL hLSm
  -- the ten bounds sum to the target exactly, so chain them structurally rather than
  -- asking `linarith` to search: the two halves of each `B` target recombine by `ring`
  refine le_trans (add_le_add (add_le_add b1 b2)
    (add_le_add (add_le_add (add_le_add b3 b5) (add_le_add b7 b9))
      (add_le_add (add_le_add b4 b6) (add_le_add b8 b10)))) (le_of_eq ?_)
  ring

/-- **`Theorem \ref{thm:main-littlewood}` (Theorem 3), sharper form.** On the regime `t > 10^12`,
`0 < h ≤ t^{2/3}`, the Littlewood-mechanism error is the six-term expression stated inside
`Theorem \ref{thm:littlewoodshort}` (Theorem 32), sharper than `MainTheorem.ELittlewood`'s
collapsed two-term `(1/(t(r-α)))(0.335 + 0.51/log t)`.

### Summary of Proof
Theorem 32's `O^*` error is `(1/(r-α))` times the sum of Lemma 25's own error and the
arc-integral remainder `E(r,·)` evaluated at `t±h`. Under `t > 10^12`, `h < t^{2/3}` the tex uses
a *hybrid* substitution: `h ≤ t^{2/3}` directly wherever `h` sits in a numerator (which happens
only in the main term, giving it a genuinely sharper `t^{-4/3}` rate), and the derived consequence
`h < t/10000` — immediate since `t^{2/3}/t = t^{-1/3} ≤ 10^{-4}` there — wherever `h` enters only
through a denominator (`t-h`, and `τ-r`, `log τ`, `log(τ-r)` inside `E`). That keeps the
denominator bounds clean (`τ-r ≥ (4999/5000)t`, `log(τ-r) ≥ (49999/50000) log t`) instead of
dragging a fractional power through logs and squares. Collecting gives the six displayed terms.

The instantiation is `LittlewoodShort.littlewoodshort_tight` (Theorem 32), whose main terms are
*literally* `ULittlewood α r h t k` up to `|t| = t`, so only the error bracket has to be
collapsed; both sides carry `1/(r-α)`, that factor cancels, and what is left is exactly
`littlewoodTight_collapse`.

### Lean Notes
`hα12 : α < 1/2` is weaker than the `α < 1/6` that `\ref{thm:main-littlewood}` (Theorem 3)
states, so this form is more general than the tex's; the route through `littlewoodshort_tight`
— whose own hypotheses are `13 < t-h`, `0 < h`, `0 < α < r`, and the chord pinning
`σ_k ≤ 1-r < σ_{k+1}` — needs no bound on `α` beyond `α < r`. As with `mainJensenTight`, the
regime hypotheses `t > 10^12`, `0 < h ≤ t^{2/3}` are explicit here, where
`MainTheorem.mainLittlewood` also covers `t ≤ 10^12` and `h = 0`; `h ≤ t^{2/3}` is non-strict for
the same reason as there. The six-term bracket matches the printed simplification at tex line
1163 exactly.

**`0 < h` cannot be dropped.** For `h ≤ 0` the interval `(t-h, t+h)` is empty, so `Nrect = 0` and
the claim reduces to `0 < U_L + error`. But `ULittlewood` is affine in `h` with slope
`(2A_1/π)log t + 2A_2 log log t + 2A_3`, and `A_2 = 1/(2π(r-α))` **exactly** — `vCoeffP` is
identically `1`, so that chord is the constant `1` — making the slope strictly positive. Computed
across `α ∈ {1/7,…,1/16}`, `r ∈ [0.5,0.9]` at `t = 10^12` it ranges over `5.4 … 6.6`
(`Code/verify_mainTight_h_sign.py`), so `h → -∞` would drive the right side to `-∞`; `α = 1/7`,
`r = 0.5`, `t = 10^12`, `h = -10^6` is an explicit refutation of the `h`-free form. The `h = 0`
endpoint is recovered in `MainTheorem.mainLittlewood`.

Theorem 3's case split does not enter: it is what makes `MainTheorem.mainLittlewood` true down to
`t ≥ e^e`, including `t+h ≤ H₀`. Here `t > 10^12` and `h ≤ t^{2/3}`, where Theorem 32 applies
directly — its own threshold is only `13 < t-h`, far below `H₀` — so
`platt_trudgian_verified_below` is not used.

**On `arg ζ`** (inherited from `littlewoodshort_tight`): `argZeta` is the tex's constructed
branch (`LittlewoodMethod.argZetaDef`), so no polar-form hypothesis is needed. The tex treats
`arg ζ` in two cases (after Equation `\ref{eq:zerodensityintegral}`, Equation 13): on a
horizontal line without zeros, `arg ζ` is *defined* by continuous variation to the right of `1`
and then along the line — this is `argZetaDef`; on a line through a zero the tex uses the
convention `lim_{ε→0} ½(arg ζ(·+i(t+ε)) + arg ζ(·+i(t-ε)))` (with the matching one for `N`).
This theorem assumes the first case on both lines `t±h` (`hzf_p`/`hzf_m`); the statements that
need no edge hypothesis are `HalvingConvention.mainLittlewoodHalf` and `littlewoodshortHalf`,
reached there by an `ε`-shift. Nothing is assumed on the left edge `Re s = 1-r`
(`LittlewoodIdentity.intervalIntegrable_log_norm_zeta_vertical`).

### References
tex: `\ref{thm:main-littlewood}` (Theorem 3), sharpened by the `t > 10^12`, `h < t^{2/3}`
simplification printed inside `\ref{thm:littlewoodshort}` (Theorem 32) at tex lines 1161–1164,
which in turn rests on `\ref{lemma:littlewood-mainterm}` (Lemma 25).

### Dependencies
**Depends on:** `ULittlewood`, `Nrect`, `sigma`, `sigma_pos`, `sigma_lt_one`, `eta`,
`arcErr_tight`, `littlewoodshort_tight`, `rpow_two_thirds_le_div`, `littlewoodTight_collapse`.
**Used by:** `MainTheorem.mainLittlewood`. -/
theorem mainLittlewoodTight {α r h t : ℝ} {k : ℤ} (hα0 : 0 < α) (hrα : α < r)
    (hα12 : α < 1 / 2) (hk : sigma k ≤ 1 - r) (hk' : 1 - r < sigma (k + 1))
    (ht : (10 : ℝ) ^ (12 : ℕ) < t) (hh0 : 0 < h) (hh : h ≤ t ^ ((2 : ℝ) / 3))
    (hzf_p : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t + h) * Complex.I) ≠ 0)
    (hzf_m : ∀ x ∈ Set.Icc (1 - r) (1 + eta * r), riemannZeta (x + (t - h) * Complex.I) ≠ 0) :
    (Nrect (t - h) (t + h) α : ℝ)
      < ULittlewood α r h t k
        + (1 / (t * (r - α))) *
            (0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
              + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t)) := by
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hr0 : (0 : ℝ) < r := by linarith [sigma_lt_one (k + 1), hk']
  have hr1 : r < 1 := by linarith [sigma_pos k, hk]
  have hrα' : (0 : ℝ) < r - α := by linarith
  -- `h < t/10000`, hence `h < t` and `13 < t - h`
  have hht : h ≤ t / 10000 := le_trans hh (rpow_two_thirds_le_div ht)
  have hhlt : h < t := by nlinarith
  have hT13 : (13 : ℝ) < t - h := by nlinarith
  have hmain := littlewoodshort_tight (T := t) (h := h) (r := r) (α := α) (k := k)
    hT13 hh0 hhlt hα0 hrα hk hk' hzf_p hzf_m
  rw [abs_of_pos ht0] at hmain
  -- the main terms of `littlewoodshort_tight` are literally `ULittlewood`
  have hU : (2 * A1 α r k * h + 2 * A4 α r) / Real.pi * Real.log t
      + (2 * A2 α r k * h + 2 * A5 α r) * Real.log (Real.log t)
      + 2 * A3 α r k * h + A6 α r = ULittlewood α r h t k := rfl
  rw [hU] at hmain
  refine lt_of_lt_of_le hmain ?_
  -- so only the error bracket has to collapse, and the shared `1/(r-α)` cancels
  have hcol := littlewoodTight_collapse (r := r) (h := h) (t := t) hr0 hr1 ht hh0 hh
  have hkey : (2 * h / (Real.pi * (t - h) ^ 2)
        + 1158 * h / (8 * Real.pi * (t - h) ^ 2 * Real.log (t - h))
        + r / 4 * (arcErr_tight r (t + h) + arcErr_tight r (t - h))) / (r - α)
      ≤ (1 / (t * (r - α))) *
          (0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
            + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t)) := by
    rw [div_le_iff₀ hrα']
    have hexp : (1 / (t * (r - α))) *
        (0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
          + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t)) * (r - α)
        = (0.334 + 0.502 / Real.log t + 1.001 / t + 72.48 / (t * Real.log t)
            + 0.64 / t ^ ((1 : ℝ) / 3) + 46.3 / (t ^ ((1 : ℝ) / 3) * Real.log t)) / t := by
      field_simp
      try ring
    rw [hexp, le_div_iff₀ ht0]
    linarith [hcol]
  linarith [hkey]
