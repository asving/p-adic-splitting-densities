/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E11
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Uniformity.ChapE.E13 — degree bookkeeping of a σ-block: `deg F = μD`, and the hull is finite

**Chapter E, NODE E.13** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §4), ENV-E2 **+
`[IsDomain O]`** (the degree arithmetic needs `O` nontrivial so that a monic polynomial's
`degree` is its `natDegree`; the blueprint signs `[IsDomain O]` on both declarations).

Two facts about a block `B : BlockData C` (E.11) that every later accounting node assumes
without saying so:

* **(i) `BlockData.natDegree_F`** — `deg F = μ · D` and `F` is monic. This is `(DEV)`'s content:
  `F = Φ^μ + Σ_{j<μ} A_j Φ^j` with `Φ` monic of degree `D` and `deg A_j < D`, so the low terms
  cannot reach the top — the highest one, `A_{μ−1} Φ^{μ−1}`, has degree at most
  `(D−1) + (μ−1)D = μD − 1`.
* **(iii) `BlockData.suppVal_ne_top`** — every cleared support value `ladderSuppVal B.devHgt u ℓ μ`
  is finite. The polygon is honest: `+∞` is never fed to the accounting (`EFF.T2.23`'s "the peel
  occurs before `(WINDOW)` so `+∞` is never fed to Newton accounting" is this convention's
  analogue one clause down).

## What the SIGNATURE signs, and what it does not

The blueprint's STATEMENT has three clauses; the signed SIGNATURE has **two** declarations, (i)
and (iii). Clause **(ii)** — the two hull endpoints `devHgt μ = 0` and `devHgt 0 ≠ ⊤` — signs no
declaration and is NOT added as one here (signatures are frozen). It is instead exercised in the
gate below as executed `example`s, so the clause is kept honest without inventing a declaration.

Two honest readings of that split, both recorded rather than glossed:

* `devHgt μ = 0` (the monic top's height) is what (iii) actually consumes — it is definitional,
  and the proof of (iii) reads the `j = μ` endpoint and nothing else. In consequence **(iii) is
  proved uniformly in `(u, ℓ)`, including the degenerate `ℓ = 0`**, exactly as signed.
* `devHgt 0 ≠ ⊤` (the `(KEY-FREE)` endpoint) is therefore **NOT consumed by (iii)**. It is a real
  fact about a real block — it is where E.11's `hA0` and E.10's `hgt_ne_top` are spent — but the
  finiteness of the support value does not rest on it. Anyone citing (iii) as "the hull spans
  both endpoints" is over-reading it; the gate states the left endpoint separately for that
  reason.

## Fail-closed, structurally (the S7 reducible-key tooth)

`EFF.T2.11` derives `A₀ ≠ 0` from `(KEY-FREE)`, and E.11 carries it as the field `hA0` precisely
so this node consumes it without re-doing field theory inside a polygon argument. The tooth: a
reducible-key input (`Φ ∣ F`) forces `A₀ = 0`, so it does not merely make the finiteness clause
false — **it cannot produce a `BlockData` at all**. The corpus's fail-closed behaviour is
reproduced by the structure, not by a hypothesis of this lemma.

## Conditionality (read before citing these as unconditional)

Both statements are theorems ABOUT a `BlockData C`; neither asserts that one exists. Exhibiting a
`SlotCarrier`/`BlockData` over real polynomial data is the instance obligation of E.22/E.23, and
E.10/E.11 landed their carriers without instances by design. Until an instance lands, every
consumer of this node inherits that conditionality.

DEPENDS: E.10 (`SlotCarrier.hgt_ne_top`, `hD`), E.11 (`BlockData`, `devHgt`, `ladderSuppVal`) ·
mathlib `Polynomial.Monic.pow`, `Polynomial.Monic.natDegree_pow`, `Polynomial.natDegree_mul_le`,
`Polynomial.natDegree_sum_le_of_forall_le`, `Polynomial.degree_lt_degree`,
`Polynomial.degree_add_eq_left_of_degree_lt`, `Polynomial.Monic.add_of_left`, `Finset.inf_le`,
`ne_top_of_le_ne_top`.

SOURCE: `EFF.T2.11` (`deg F = μD` in `(DEV)`; the `(KEY-FREE) ⟹ A₀ ≠ 0 ⟹` hull-span
derivation); `EFF.T2.29` (finite window values as a hypothesis of the count derivation);
`EFF.T2.23` (the `+∞`-is-never-fed convention, one clause up).

TEETH: S7 reducible-key gate → the finiteness clauses are what a `Φ ∣ F` input violates (`hA0`
fails), reproducing the corpus's fail-closed behaviour structurally.

ENVIRONMENT: ENV-E2 + `[IsDomain O]`.

## Status

Sorry-free. Both declarations report exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}` — these arrive through mathlib's `Polynomial`/`WithTop`
instance graph, not through any project axiom. Types checked against the signed SIGNATURE
declaration by declaration (binder names, order and explicitness unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.13(i)** `(DEV)`'s degree bookkeeping: the development `F = Φ^μ + Σ_{j<μ} A_j Φ^j` of a
block has `deg F = μ · D` and is monic, because every low term has degree at most `μD − 1`
(`EFF.T2.11`). -/
theorem BlockData.natDegree_F {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : B.F.natDegree = B.μ * C.D ∧ B.F.Monic := by
  -- The top term `Φ^μ`: monic, of degree `μD`.
  have hpow : (B.Φ ^ B.μ).Monic := B.hΦ.pow B.μ
  have hnpow : (B.Φ ^ B.μ).natDegree = B.μ * C.D := by
    rw [B.hΦ.natDegree_pow, B.hΦdeg]
  -- The low terms: each `A_j Φ^j` has degree `≤ (D−1) + jD ≤ μD − 1`.
  have hsum : (∑ j ∈ Finset.range B.μ, B.A j * B.Φ ^ j).natDegree ≤ B.μ * C.D - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro j hj
    have hj' : j < B.μ := Finset.mem_range.mp hj
    have h1 : (B.A j * B.Φ ^ j).natDegree ≤ (B.A j).natDegree + (B.Φ ^ j).natDegree :=
      Polynomial.natDegree_mul_le
    have h2 : (B.Φ ^ j).natDegree = j * C.D := by rw [B.hΦ.natDegree_pow, B.hΦdeg]
    have h3 : (B.A j).natDegree < C.D := B.hdegA j hj'
    have h4 : j * C.D + C.D ≤ B.μ * C.D :=
      calc j * C.D + C.D = (j + 1) * C.D := by ring
        _ ≤ B.μ * C.D := Nat.mul_le_mul_right _ hj'
    omega
  -- Hence the low terms sit strictly below the top, and the top survives.
  have hlt : (∑ j ∈ Finset.range B.μ, B.A j * B.Φ ^ j).degree < (B.Φ ^ B.μ).degree := by
    refine Polynomial.degree_lt_degree ?_
    have hD := C.hD
    have hμ := B.hμ
    have hpos : 1 ≤ B.μ * C.D := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  refine ⟨?_, ?_⟩
  · rw [B.hdev,
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hlt)]
    exact hnpow
  · rw [B.hdev]
    exact hpow.add_of_left hlt

/-- **E.13(iii)** every cleared support value of a block's development is finite: the `j = μ`
endpoint contributes `ℓ • 0 + μ·u`, which is not `⊤`, and the support value is an infimum
(`EFF.T2.23`'s "`+∞` is never fed to Newton accounting", one clause down). Uniform in `(u, ℓ)`. -/
theorem BlockData.suppVal_ne_top {O : Type*} [CommRing O] [IsDomain O] {K : Type*}
    [Field K] {C : SlotCarrier O K} (B : BlockData C) (u ℓ : ℕ) :
    ladderSuppVal B.devHgt u ℓ B.μ ≠ ⊤ := by
  have hmem : B.μ ∈ Finset.range (B.μ + 1) := Finset.self_mem_range_succ B.μ
  have hle : ladderSuppVal B.devHgt u ℓ B.μ
      ≤ ℓ • B.devHgt B.μ + ((B.μ * u : ℕ) : WithTop ℤ) :=
    Finset.inf_le hmem
  -- clause (ii), the monic top: `devHgt μ = 0` by definition.
  have htop : B.devHgt B.μ = 0 := by simp [BlockData.devHgt]
  rw [htop, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (by simp) hle

/-! ## Gate (executed `example`s, not blueprint declarations)

Clause **(ii)** of the STATEMENT signs no declaration (see the header). Both of its endpoint
facts are stated here so that the clause is checked rather than asserted, and so that the split
recorded in the header — (iii) consumes the RIGHT endpoint only — is visible in the file. -/

section Gate

-- clause (ii), right endpoint (consumed by (iii) above): the monic top has height `0`.
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    (B : BlockData C) : B.devHgt B.μ = 0 := by
  simp [BlockData.devHgt]

-- clause (ii), left endpoint (NOT consumed by (iii)): `(KEY-FREE)`'s shadow `hA0` plus E.10's
-- `hgt_ne_top` make the hull's `j = 0` abscissa finite. This is where the S7 reducible-key
-- input dies: `Φ ∣ F` forces `A₀ = 0`, which no `BlockData` admits.
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    (B : BlockData C) : B.devHgt 0 ≠ ⊤ := by
  have hμ := B.hμ
  have h0 : B.devHgt 0 = C.hgt (B.A 0) := by
    have h1 : ¬ ((0 : ℕ) = B.μ) := by omega
    have h2 : (0 : ℕ) < B.μ := by omega
    simp [BlockData.devHgt, h1, h2]
  rw [h0]
  exact C.hgt_ne_top (B.A 0) B.hA0 (B.hdegA 0 hμ)

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.BlockData.natDegree_F
#print axioms Uniformity.Density.Ladder.BlockData.suppVal_ne_top

end AxCheck
