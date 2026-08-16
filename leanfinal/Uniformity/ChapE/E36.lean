/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E11
import Mathlib

/-!
# Uniformity.ChapE.E36 — the gcd dichotomy (ANNEX-LEMMA R2-a) + coprimality at `[IsIntegrallyClosed O]`

**Chapter E, NODE E.36** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §6), ENV-E2 + `[IsDomain O]`,
**as RE-SIGNED by amendment A-E.3 (2026-08-16)**. Both signed theorems land; the second lands at
the re-signed contract, i.e. with `[IsIntegrallyClosed O]` in its binders — a hypothesis this file
proves to be NECESSARY (machine-checked counterexample below) and SUFFICIENT.

## Landed here

* `gcd_dichotomy` — the signed statement, verbatim, PROVED (no `sorry`, Lean-core axioms only).
  This is the chapter's clearest net upgrade of a proof-only source unit to machine-checked
  (`EFF.HE7.119` is PROOF-ONLY at source: "The scenario it excludes is one the battery's frame
  cannot produce").
* `coprime_of_not_dvd` — at the A-E.3 signature (`[IsIntegrallyClosed O]` added, everything else
  byte-for-byte the committed form), PROVED. The A-E.3 rationale is call-site-free: every consumer
  instantiates at ENV-E2's `[IsDiscreteValuationRing O]`, from which mathlib derives
  `IsIntegrallyClosed O` by instance search (DVR → PID → UFD → integrally closed), so no consumer
  signature moves. See the ENV determination in the amendment.
* `coprime_of_not_dvd_of_descent` — the same conclusion with the descent step as an explicit
  hypothesis, kept as the isolating lemma (it is what makes the normality dependence visible).
* namespace `E36Refutation` — the refutation of the PRE-A-E.3 signature, kept verbatim as
  provenance for the re-sign. Nothing in it asserts the refuted statement.

## Why the re-sign: the committed signature (no `[IsIntegrallyClosed O]`) is FALSE

The committed second signed theorem read

```
theorem coprime_of_not_dvd {O} [CommRing O] [IsDomain O] {F Ψ : Polynomial O}
    (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D) (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ → g₀.natDegree ≠ 0 → D ≤ g₀.natDegree)
    (hndvd : ¬ Ψ ∣ F) :
    IsCoprime (F.map (algebraMap O (FractionRing O))) (Ψ.map (algebraMap O (FractionRing O)))
```

and it is **refuted** by the counterexample below (E wave 3, 2026-08-16). It is nowhere declared
in that form, so the refuted claim never enters the environment as a fact.

### The counterexample

Take `O = ℤ[2i] = {x + 2yi : x, y ∈ ℤ} ⊂ ℂ`, a domain, with `FractionRing O = ℚ(i)`
(`i = (2i)/2` is already a quotient of elements of `O`). Put

* `Ψ = X² + 1` — monic, `natDegree Ψ = 2 =: D > 0`, and `Ψ = (X − i)(X + i)` over `ℚ(i)`;
* `F = X² − (2i)·X − 1` — monic, coefficients `−2i ∈ O` and `−1 ∈ O`, and `F = (X − i)²`.

Every hypothesis holds:

* `hforce` holds. A monic `g₀ ∈ O[X]` dividing `Ψ` has `natDegree g₀ ≤ 2`. At `natDegree g₀ = 1`
  we have `g₀ = X − a` with `a ∈ O` and `a² = −1`; writing `a = x + 2yi` this is
  `x² − 4y² = −1` together with `4xy = 0`, which has **no integer solution** (`x = 0` gives
  `4y² = 1`; `y = 0` gives `x² = −1`). That arithmetic is machine-checked below
  (`no_sqrt_neg_one_in_Z2i`). So the only positive-degree case is `natDegree g₀ = 2`, where
  `D ≤ natDegree g₀` holds trivially. `hforce` is therefore TRUE, vacuously at degree 1.
* `hndvd` holds: `Ψ ∣ F` with both monic of degree 2 would force `F = Ψ`
  (`eq_of_monic_of_natDegree_eq_of_dvd` below), and `F ≠ Ψ` — their constant coefficients are
  `−1` and `1` (`fWitness_ne_psiWitness`, machine-checked; the `X`-coefficients differ too,
  `−2i` against `0`).
* The conclusion FAILS: `F` and `Ψ` share the factor `X − i` over `ℚ(i)`, so no Bézout identity
  `aF + bΨ = 1` can exist — evaluate at `i` and get `0 = 1`. Machine-checked below at the
  `ℂ`-level shadow (`witnesses_not_isCoprime`), which suffices: `IsCoprime` is preserved by the
  ring map `ℚ(i) → ℂ` (`IsCoprime.map` through `Polynomial.mapRingHom`), so a Bézout identity
  over `ℚ(i)` would give one over `ℂ`.

### Where the blueprint's proof breaks

Blueprint PROOF step 2 says: "over `FractionRing O` take the monic gcd `g`, pull its monic
`O`-lift back (Gauss/primitive)". **That pull-back is exactly what fails.** A monic factor of a
monic `O`-polynomial has coefficients in `Frac(O)` and is integral over `O`, so it lies in
`O[X]` **iff `O` is integrally closed**. `ℤ[2i]` is not: `i ∈ Frac(O)` is a root of
`X² + 1 ∈ O[X]` and `i ∉ O`. The blueprint's own SPLIT CANDIDATE note flagged this step as "the
one genuinely mathlib-dependent step"; the diagnosis here is sharper — it is not
mathlib-dependent, it is FALSE without a normality hypothesis.

### The repair, ADOPTED by amendment A-E.3 (2026-08-16)

Two repair forms were proved by the refuting wave; A-E.3 signs the second:

1. `coprime_of_not_dvd_of_descent` — the conclusion with the descent step promoted to an explicit
   hypothesis `hdesc`. This proves that `hdesc` is the *only* missing ingredient: everything else
   in the node's proof is done and machine-checked. Kept (not the signed contract).
2. **`coprime_of_not_dvd`, the A-E.3 contract** — the committed statement with
   `[IsIntegrallyClosed O]` added to the binders, PROVED by discharging `hdesc` through mathlib's
   `IsIntegrallyClosed.eq_map_mul_C_of_dvd` and
   `Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map`. (Before A-E.3 this declaration carried
   the provisional name `coprime_of_not_dvd_of_isIntegrallyClosed`; the proof term is unchanged.)

Adding `[IsIntegrallyClosed O]` is sufficient, and by the counterexample some such hypothesis is
necessary. The blueprint's own fallback contract (the conclusion at the `O` level,
`∀ g₀, Monic → dvd → dvd → natDegree = 0`) is the RECORDED ALTERNATIVE, not adopted: it is exactly
`gcd_dichotomy` + `hndvd`, hence already available from this file, but it would push the
fraction-field descent onto every consumer of `(KEY-FREE)`, which is spelled as `IsCoprime` over
`FractionRing O` at E.11's `BlockData.hkeyfree`.

**The ENV determination (why the class had to be written down).** The node's ENVIRONMENT tag is
ENV-E2 + `[IsDomain O]`, but its SIGNATURE deliberately binds the ENV-arithmetic weakening
`{O : Type*} [CommRing O] [IsDomain O]` — a bare domain, no `[IsDiscreteValuationRing O]` — so the
normality instance is NOT derivable inside the signed binder list and had to be added explicitly.
At full ENV-E2 the re-sign would have been mere instance-restatement: `IsDiscreteValuationRing O`
gives `IsIntegrallyClosed O` by instance search at our pin (checked), so every call site of this
node — all of which live in the DVR arena — is unaffected.

DEPENDS: E.11 (the coprimality spelling — `IsCoprime (F.map …) (Ψ.map …)` over `FractionRing O`,
matching `LadderKeyData.hkeyfree`) · mathlib `Polynomial.Monic.of_mul_monic_left`,
`eq_one_of_monic_natDegree_zero`, `EuclideanDomain.gcd_isUnit_iff`,
`IsIntegrallyClosed.eq_map_mul_C_of_dvd`, `Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map`.

SOURCE: `EFF.HE7.119` (ANNEX-LEMMA R2-a, statement + proof, incl. "a proper common factor would
be a Galois-stable factor of Ψ of degree ≥ deg Ψ"); `EFF.HE7.09` (the convention whose
equivalence chain this licenses — "Codex graded this a GAP as stated" pre-annex, closed by R2-a
*for the dichotomy half*; the coprimality half is closed at the A-E.3 signature, over a normal `O`).

TEETH: PROOF-ONLY at source → **Lean theorem** for both halves, plus a machine-checked refutation
of the committed (normality-free) coprimality signature — the evidence for A-E.3.

ENVIRONMENT: ENV-E2 (+ `[IsDomain O]`; the coprimality half additionally `[IsIntegrallyClosed O]`,
A-E.3 — free at ENV-E2 proper, where `O` is a DVR).

## Status

Sorry-free, Lean-core axioms only. Both signed theorems land (`coprime_of_not_dvd` at the A-E.3
signature); the descent-isolating lemma and the refutation of the pre-A-E.3 signature are kept.
-/

set_option linter.style.longLine false
-- `gcd_dichotomy`'s `hF` and `hD` binders are unused by its proof but are part of the FROZEN
-- signature (`leanspec/Leanspec/ChapE.lean`), so they stay: signature fidelity beats the linter.
set_option linter.unusedVariables false

namespace Uniformity.Density.Ladder

open Polynomial

/-- **NODE E.36**, the landed half — *the gcd dichotomy* (ANNEX-LEMMA R2-a, schema form). Under
the forcing datum `hforce` (instance content: a common root is a level-2 point whose full Galois
orbit sits inside `g₀`, forcing `deg g₀ ≥ [L_ξ : K₀] ≥ D″`), every monic common divisor of `F`
and `Ψ` is either a constant or `Ψ` itself: the degree squeeze `D ≤ deg g₀ ≤ deg Ψ = D` plus
monicity leaves no room. -/
theorem gcd_dichotomy {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree) :
    ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree = 0 ∨ g₀ = Ψ := by
  intro g₀ hg₀ hgF hgΨ
  by_cases h0 : g₀.natDegree = 0
  · exact Or.inl h0
  refine Or.inr ?_
  obtain ⟨q, hq⟩ := hgΨ
  -- `Ψ = g₀ * q` with `Ψ`, `g₀` monic forces `q` monic and the degrees to add.
  have hmul : (g₀ * q).Monic := hq ▸ hΨ
  have hqm : q.Monic := hg₀.of_mul_monic_left hmul
  have hdeg : Ψ.natDegree = g₀.natDegree + q.natDegree := by
    rw [hq, hg₀.natDegree_mul hqm]
  -- the squeeze: `D ≤ deg g₀` from `hforce`, `deg g₀ ≤ D` from `g₀ ∣ Ψ`
  have hlow := hforce g₀ hg₀ hgF ⟨q, hq⟩ h0
  have hq0 : q.natDegree = 0 := by omega
  rw [hq, eq_one_of_monic_natDegree_zero hqm hq0, mul_one]

/-- Helper (chapter-internal): over a field, failure of `IsCoprime` produces a MONIC common
divisor of positive degree — the normalized gcd. Used by the repair candidates below; stated
separately because it is the only place `EuclideanDomain.gcd` appears. -/
theorem monic_common_divisor_of_not_isCoprime {K : Type*} [Field K] {p q : K[X]}
    (hq : q.Monic) (hnc : ¬ IsCoprime p q) :
    ∃ g : K[X], g.Monic ∧ 0 < g.natDegree ∧ g ∣ p ∧ g ∣ q := by
  classical
  set g := EuclideanDomain.gcd p q with hgdef
  have hgu : ¬ IsUnit g := fun h => hnc (EuclideanDomain.gcd_isUnit_iff.mp h)
  have hdp : g ∣ p := EuclideanDomain.gcd_dvd_left _ _
  have hdq : g ∣ q := EuclideanDomain.gcd_dvd_right _ _
  have hgne : g ≠ 0 := ne_zero_of_dvd_ne_zero hq.ne_zero hdq
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgne
  have hmonic : (g * C (g.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hgne
  have hkey : (g * C (g.leadingCoeff)⁻¹) * C g.leadingCoeff = g := by
    rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have hdvd_g : (g * C (g.leadingCoeff)⁻¹) ∣ g := ⟨C g.leadingCoeff, hkey.symm⟩
  refine ⟨g * C (g.leadingCoeff)⁻¹, hmonic, ?_, hdvd_g.trans hdp, hdvd_g.trans hdq⟩
  rcases Nat.eq_zero_or_pos (g * C (g.leadingCoeff)⁻¹).natDegree with h0 | hpos
  · exfalso
    have h1 : g * C (g.leadingCoeff)⁻¹ = 1 := eq_one_of_monic_natDegree_zero hmonic h0
    apply hgu
    rw [← hkey, h1, one_mul]
    exact isUnit_C.mpr (IsUnit.mk0 _ hlc)
  · exact hpos

/-- Monic polynomials of equal degree that divide each other are equal — the degree-squeeze
step, isolated (it is also what makes `hndvd` true in the counterexample). -/
theorem eq_of_monic_of_natDegree_eq_of_dvd {R : Type*} [CommRing R] {F Ψ : R[X]}
    (hF : F.Monic) (hΨ : Ψ.Monic) (hdeg : F.natDegree = Ψ.natDegree) (hdvd : Ψ ∣ F) : F = Ψ := by
  obtain ⟨q, hq⟩ := hdvd
  have hmul : (Ψ * q).Monic := hq ▸ hF
  have hqm : q.Monic := hΨ.of_mul_monic_left hmul
  have hd : F.natDegree = Ψ.natDegree + q.natDegree := by rw [hq, hΨ.natDegree_mul hqm]
  have hq0 : q.natDegree = 0 := by omega
  rw [hq, eq_one_of_monic_natDegree_zero hqm hq0, mul_one]

/-- The descent-isolating lemma (NOT a signed name; kept as provenance for A-E.3). The signed
`coprime_of_not_dvd` with the descent step promoted to an explicit hypothesis `hdesc`: *every*
monic positive-degree common divisor over `FractionRing O` descends to a monic positive-degree
common divisor over `O`. With `hdesc` supplied, `gcd_dichotomy` + `hndvd` close the node.

This lemma is the precise statement of what the committed signature was missing: `hdesc` is FALSE
for general `[IsDomain O]` (see the module docstring's `ℤ[2i]` counterexample), and everything else
in the node's proof is here and machine-checked. -/
theorem coprime_of_not_dvd_of_descent {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree)
    (hdesc : ∀ g : Polynomial (FractionRing O), g.Monic → 0 < g.natDegree →
      g ∣ F.map (algebraMap O (FractionRing O)) →
      g ∣ Ψ.map (algebraMap O (FractionRing O)) →
      ∃ g₀ : Polynomial O, g₀.Monic ∧ g₀.natDegree ≠ 0 ∧ g₀ ∣ F ∧ g₀ ∣ Ψ)
    (hndvd : ¬ Ψ ∣ F) :
    IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Ψ.map (algebraMap O (FractionRing O))) := by
  by_contra hnc
  obtain ⟨g, hgm, hgpos, hgF, hgΨ⟩ :=
    monic_common_divisor_of_not_isCoprime (hΨ.map (algebraMap O (FractionRing O))) hnc
  obtain ⟨g₀, hg₀m, hg₀d, hg₀F, hg₀Ψ⟩ := hdesc g hgm hgpos hgF hgΨ
  rcases gcd_dichotomy hF hΨ hD hΨd hforce g₀ hg₀m hg₀F hg₀Ψ with h | h
  · exact hg₀d h
  · exact hndvd (h ▸ hg₀F)

/-- **NODE E.36**, the second signed theorem **at the A-E.3 signature** — *coprimality from
non-divisibility*. The committed statement with `[IsIntegrallyClosed O]` added to the binders
(everything else byte-unchanged). Normality is exactly what makes a monic factor of a monic
`O`-polynomial descend from `Frac(O)[X]` to `O[X]`; mathlib supplies the descent
(`IsIntegrallyClosed.eq_map_mul_C_of_dvd`, `Monic.dvd_of_fraction_map_dvd_fraction_map`), and the
counterexample in the module docstring shows some such hypothesis is NECESSARY — over the bare
domain `ℤ[2i]` the committed statement is false. The class is free at every call site: ENV-E2's
`[IsDiscreteValuationRing O]` yields it by instance search. -/
theorem coprime_of_not_dvd {O : Type*} [CommRing O] [IsDomain O]
    [IsIntegrallyClosed O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree)
    (hndvd : ¬ Ψ ∣ F) :
    IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Ψ.map (algebraMap O (FractionRing O))) := by
  refine coprime_of_not_dvd_of_descent hF hΨ hD hΨd hforce ?_ hndvd
  intro g hgm hgpos hgF hgΨ
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  -- the descent: a monic divisor of the monic `Ψ.map` has an `O`-lift, because `O` is normal
  obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing O) hΨ hgΨ
  rw [hgm.leadingCoeff, C_1, mul_one] at hg₀
  have hg₀m : g₀.Monic := by
    have hmapm : (g₀.map (algebraMap O (FractionRing O))).Monic := hg₀ ▸ hgm
    exact (Function.Injective.monic_map_iff hinj).mpr hmapm
  refine ⟨g₀, hg₀m, ?_, ?_, ?_⟩
  · have hdeg : g₀.natDegree = g.natDegree := by
      rw [← hg₀, Polynomial.natDegree_map_eq_of_injective hinj]
    omega
  · exact hF.dvd_of_fraction_map_dvd_fraction_map hg₀m (by rw [hg₀]; exact hgF)
  · exact hΨ.dvd_of_fraction_map_dvd_fraction_map hg₀m (by rw [hg₀]; exact hgΨ)

end Uniformity.Density.Ladder

/-! ## The refutation of the PRE-A-E.3 `coprime_of_not_dvd` (no `[IsIntegrallyClosed O]`), machine-checked

Kept verbatim as the provenance of the A-E.3 re-sign: it is the evidence that the added class is
necessary, not decorative. Nothing here asserts the refuted statement.

The counterexample is `O = ℤ[2i]`, `Ψ = X² + 1`, `F = X² − 2iX − 1 = (X − i)²`; the module
docstring carries the full argument. Formalizing `ℤ[2i]` and `FractionRing ℤ[2i] ≅ ℚ(i)` as Lean
objects is plumbing with no mathematical content, so what is checked here is the part where a
transcription error could actually hide:

* the ARITHMETIC that makes `hforce` true — no element of `ℤ[2i]` squares to `−1`;
* the two witnesses' common root, and the resulting failure of `IsCoprime` — checked at the `ℂ`
  shadow, which suffices because `IsCoprime` is preserved by any ring map out of `ℚ(i)`;
* the degree squeeze that makes `hndvd` true, plus `F ≠ Ψ`.

Everything else (that `ℤ[2i]` is a domain with fraction field `ℚ(i)`, that the two witnesses
have coefficients in it) is direct inspection. -/

namespace Uniformity.Density.Ladder.E36Refutation

open Polynomial Uniformity.Density.Ladder

/-- The counterexample's `Ψ = X² + 1`, at the `ℂ` shadow. -/
private noncomputable def psiWitness : ℂ[X] := X ^ 2 + 1

/-- The counterexample's `F = X² − 2iX − 1 = (X − i)²`, at the `ℂ` shadow. -/
private noncomputable def fWitness : ℂ[X] := X ^ 2 - C (2 * Complex.I) * X - 1

/-- **`hforce` is TRUE in the counterexample.** A degree-one monic divisor of `Ψ = X² + 1` over
`O = ℤ[2i]` would be `X − a` with `a = x + 2yi` and `a² = −1`, i.e. `x² − 4y² = −1` and
`4xy = 0`. There is no such integer pair, so no positive-degree monic common divisor of degree
below `D = 2` exists and `hforce` holds vacuously at degree 1. -/
theorem no_sqrt_neg_one_in_Z2i : ∀ x y : ℤ, 4 * x * y = 0 → x ^ 2 - 4 * y ^ 2 ≠ -1 := by
  intro x y h hsq
  rcases mul_eq_zero.mp h with h' | hy
  · rcases mul_eq_zero.mp h' with h4 | hx
    · omega
    · -- `x = 0`: `4y² = 1` has no integer solution
      rw [hx] at hsq
      have h1 : (4 : ℤ) * y ^ 2 = 1 := by linarith
      generalize y ^ 2 = z at h1
      omega
  · -- `y = 0`: `x² = −1` has no integer solution
    rw [hy] at hsq
    have h1 : x ^ 2 = -1 := by linarith
    nlinarith [sq_nonneg x]

/-- `F` vanishes at `i` (it is `(X − i)²`). -/
theorem fWitness_root : fWitness.eval Complex.I = 0 := by
  simp only [fWitness, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
  linear_combination -Complex.I_sq

/-- `Ψ` vanishes at `i` (it is `(X − i)(X + i)`). -/
theorem psiWitness_root : psiWitness.eval Complex.I = 0 := by
  simp only [psiWitness, eval_add, eval_pow, eval_X, eval_one]
  linear_combination Complex.I_sq

/-- A shared root defeats `IsCoprime`: a Bézout identity evaluated at the root gives `0 = 1`. -/
theorem not_isCoprime_of_common_root {p q : ℂ[X]} (hp : p.eval Complex.I = 0)
    (hq : q.eval Complex.I = 0) : ¬ IsCoprime p q := by
  rintro ⟨a, b, hab⟩
  have hev := congrArg (fun r => Polynomial.eval Complex.I r) hab
  simp [hp, hq] at hev

/-- **THE REFUTATION'S CONCLUSION.** The two witnesses are NOT coprime over a field containing
`i`. Since `IsCoprime` is preserved by ring maps, the same failure holds over `ℚ(i) = Frac(ℤ[2i])`,
which is the signed statement's conclusion. -/
theorem witnesses_not_isCoprime : ¬ IsCoprime fWitness psiWitness :=
  not_isCoprime_of_common_root fWitness_root psiWitness_root

/-- **`hndvd` is TRUE in the counterexample**: `F ≠ Ψ` (their `X`-free coefficients are `−1` and
`1`), so by `eq_of_monic_of_natDegree_eq_of_dvd` at equal degree 2, `Ψ ∤ F`. -/
theorem fWitness_ne_psiWitness : fWitness ≠ psiWitness := by
  intro h
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp [fWitness, psiWitness, Complex.ext_iff] at h0
  norm_num at h0

end Uniformity.Density.Ladder.E36Refutation

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.gcd_dichotomy
#print axioms Uniformity.Density.Ladder.monic_common_divisor_of_not_isCoprime
#print axioms Uniformity.Density.Ladder.eq_of_monic_of_natDegree_eq_of_dvd
#print axioms Uniformity.Density.Ladder.coprime_of_not_dvd_of_descent
#print axioms Uniformity.Density.Ladder.coprime_of_not_dvd
#print axioms Uniformity.Density.Ladder.E36Refutation.no_sqrt_neg_one_in_Z2i
#print axioms Uniformity.Density.Ladder.E36Refutation.witnesses_not_isCoprime
#print axioms Uniformity.Density.Ladder.E36Refutation.fWitness_ne_psiWitness

end AxCheck
