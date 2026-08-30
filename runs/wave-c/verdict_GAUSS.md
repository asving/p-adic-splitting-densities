# UNIT GAUSS2 — VERDICT: PROVED, COMPLETE (2026-08-30; finisher of the hung GAUSS unit)

Deliverable: `leanfinal/Uniformity/ChapI/IFCG19.lean` — sorry-free, warning-free, all 20
public declarations Lean-core only (`propext, Classical.choice, Quot.sound`); registered
in the `Uniformity/ChapI.lean` aggregator; targeted build green (9061 jobs, IFCG19 +
ChapI). Every proof in the unit landed FIRST-TRY (zero repair rounds).

## Headline 1 — the uniform Gauss/necklace census (all δ ≥ 1, every finite field)

* `sum_divisors_mul_card_irredFinset` / `sum_divisors_mul_natCard_irred`:
  `Σ_{d ∣ δ} d · N_d = q^δ` — in both IFCG17's `irredFinset` and IFCG4's
  `Nat.card (IrredOfDeg K d)` interfaces.
* `mul_natCard_irred_eq_moebius_sum`: the closed form
  `δ · N_δ = Σ_{(a,b): ab = δ} μ(a) · q^b` in `ℤ` (ArithmeticFunction Möbius inversion).
* `necklacePoly (δ) : ℚ[X]` + `necklacePoly_eval_card`: ONE polynomial whose value at
  `q = #K` is `N_δ`, uniformly over finite fields — the URLim-facing packaging.
* Engine: `frobPoly K δ = X^(q^δ) − X` monic (`monic_frobPoly`), degree `q^δ`
  (`natDegree_frobPoly`), squarefree (`squarefree_frobPoly`, via
  `galois_poly_separable`), and `irred_dvd_frobPoly_iff`: monic irreducible `g` divides
  `Φ_δ` ⟺ `deg g ∣ δ`.
* This closes IFCG4's honestly-left-open general-δ gap (its §1 pinned δ ≤ 4 only).

## Headline 2 — ★ the e = 1 clause of `SinglePointAggregateLaw` CLOSES, all δ ≥ 1,
UNCONDITIONALLY — and the conjectured δ ≥ 2 base-change leg DOES NOT EXIST at e = 1

* `stratPoly_irreducible` (the monomial lemma): over an irreducible residue polynomial
  `p` of degree δ, `stratPoly O δ N p = single {(1,δ)} q^(δ(N−1))` — H124's
  `decidedAt_of_mem_levelZeroStratum_irreducible` is DEGREE-UNIFORM (whole stratum
  decided at the inert type `⟨{(1,δ)}⟩`), H124b's `card_levelZeroStratum` prices it.
* `SPAgg_unit_block` + `spFamily_URLim_unit`: for `b = ⟨δ, [1]⟩` the normalized
  single-point family is the CONSTANT `N_δ(q)/q^δ` at the inert coefficient (0
  elsewhere) for N ≥ 1 — `URLim` with numerator `necklacePoly δ`, denominator `X^δ`.
* `singlePoint_law_unit_clause`: the clause in the kernel's exact binder shape — the
  mass window, smaller value laws, and deep-linear exclusion are ACCEPTED AND UNUSED.
* ⚠ Correction to IFCG18's scoping note: it conjectured "unramified base-change
  recentering" needed at δ ≥ 2. False at e = 1: H124's one-factor base carries every
  degree. Base change enters only at e ≥ 2 (deep cones) — untouched here.

## Bonus — the ALL-ONES SECTOR closes (merge-correction shapes)

`SPAgg_ones_block` / `spFamily_URLim_ones` / `singlePoint_law_ones_clause`: any block
`⟨δ, E⟩` with `E` nonempty and EVERY entry `= 1` (i.e. `E = replicate k 1`, the shapes
IFCG18's collision peel produces when unit blocks merge) — family constant
`N_δ(q)/q^(δk)` at the k-fold inert coefficient; `URLim` with denominator `X^(δk)`.
(`spFamily_URLim_ones` is even k = 0-uniform; the 1 ≤ k hypothesis proved unnecessary.)

## What remains OPEN of `SinglePointAggregateLaw` (never claimed here)

Blocks with ANY exponent ≥ 2: the fractional-slope / deep-OM-cone censuses (these DO
need the unramified base change at δ ≥ 2), and `DeepLinearClusterLaw`. These are the
campaign's remaining kernels.

## S1 search finding (for the record; supersedes IFCG4's 2026-08-28 note)

Pinned mathlib has NO packaged irreducible count — but it DOES have the hard half of the
classical route: `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`
(`Mathlib/FieldTheory/Finite/Extension.lean`, any field, `Nat.card` phrasing). Only the
easy converse needed proving (`AdjoinRoot` + `FiniteField.pow_card_pow`, 12 lines).
Local rg sufficed; no loogle/leansearch calls spent.

## Stages

- [x] S0: IFCG18 §3 kernels + H124/H124b + IFCG4 read; consumption map derived
- [x] S1: bounded mathlib search (finding above)
- [x] S2: skeleton compiled first-pass
- [x] S3: uniform census landed (degree-sum + Möbius closed form + ℚ[X] packaging)
- [x] S4: e = 1 clause CLOSED all δ ≥ 1 (no base-change leg) + all-ones sector
- [x] S5: AxCheck footer — 20/20 Lean core; aggregator import added; build green

## File map

`leanfinal/Uniformity/ChapI/IFCG19.lean` (~600 lines): §1 census engine · §2
`necklacePoly` · §3 monomial lemmas · §4 consumption + all-ones extension · AxCheck
footer. Aggregator: one import line added to `leanfinal/Uniformity/ChapI.lean`.
No landed file otherwise touched; no git ops (per charge).
