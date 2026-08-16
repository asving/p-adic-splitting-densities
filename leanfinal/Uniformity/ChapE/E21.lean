/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E20
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Uniformity.ChapE.E21 — `key_boundary`: THEOREM T2.KEY-BOUNDARY, schema form

**Chapter E, NODE E.21** [theorem] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §4 — the master
HE7.A suite's composition layer). ENV-E2 (+ `[IsDomain O]`). Landed at the signed SIGNATURE
byte-for-byte from `leanspec/Leanspec/ChapE.lean`.

`EFF.T2.32`: *"Adjoin the certified irreducible boundary factors `P_i`, and apply HE7.A
separately to each key-free residual block `B_j`."* Given the boundary decomposition
`(BOUNDARY-PROD)` `F = (Π_i P_i)·(Π_j B_j)` as data — two lists of monic polynomials — and, per
residual block, the terminal emission multiset its read produced (E.20's engine output, with the
engine's exhaustion identity `Σ emitted weights = deg B` as the hypothesis `hemit`), the boundary
degrees and the emitted weights account for `deg F` exactly.

## The proof in one paragraph

Degrees add along the two list products because the factors are monic, hence nonzero, and `O` is
a domain (`Polynomial.natDegree_multiset_prod` at the coerced lists, plus one
`Polynomial.natDegree_mul` for the outer product). Substituting `hemit` block by block
(`List.map_congr_left`) turns the emitted-weight sum into the block-degree sum, and the two sides
are then the same natural number.

## ⚠ WHAT THIS THEOREM DOES *NOT* SAY — the four-part corpus fence, transcribed

`EFF.T2.28`'s fence is carried verbatim by the blueprint and is honoured here structurally,
because the decomposition is an INPUT: *"Nothing asserts that `G = Φ`, that `Φ` is irreducible,
that one factor `Φ` is peeled, or that a peel lowers `μ` by exactly one."* Concretely, nothing
below computes a gcd, factors anything, or claims the lists are canonical — the gcd computation
producing `(BOUNDARY-PROD)` (`G = monicGCD_{K₀[x]}(F, Φ)`, `EFF.T2.28`) is the instances', and
`EFF.T2.44`'s ruling that *"a reducible key boundary is handled by a separate gcd/orbit
decomposition, never by a false one-factor peel"* is exactly why the boundary arrives as a LIST
rather than a single factor.

Two further disclosures:

* **`emit` is arbitrary data constrained only at the blocks.** The signed type quantifies over an
  arbitrary `emit : Polynomial O → Multiset ℕ` and constrains it only by `hemit`, only at members
  of `blocks`. It therefore claims nothing about *which* multiset a read produces, nor that reads
  are unique; that content is E.20's, and gate (b) below discharges the promise that E.20 really
  supplies this input by BUILDING `emit` from the engine.
* **The "pairwise-disjoint weight" language of the blueprint STATEMENT is carried by the sum, not
  by a separate clause.** At this abstraction disjointness *is* the additivity of the weight
  bookkeeping; no `Multiset`-level disjointness predicate appears in the signed type, and none is
  proved.

**DEPENDS.** E.20 (`read_terminates_exhausts` — the per-block engine; consumed at gate (b), which
is why it is imported) · mathlib `Polynomial.natDegree_multiset_prod`, `Polynomial.natDegree_mul`,
`Polynomial.Monic.ne_zero`, `List.map_congr_left`.

**SOURCE.** `EFF.T2.32` (THEOREM T2.KEY-BOUNDARY, statement + proof: "The boundary decomposition
already gives the polynomial product and the disjoint exhaustive partition … Multiplying the
resulting identities proves the assertion"); `EFF.T2.28` (`(BOUNDARY-PROD)`, the per-block suite
obligation, and the four-part negative fence transcribed above); `EFF.T2.44` (the reducible-key
ruling); the §4 fences `EFF.T2.39`/`.28`/`.32` this node carries.

**TEETH.** S7 Pass 1 reducible-key gate; Pass 2 multiple-boundary-factor tooth → this Lean
theorem is the composition layer; the per-block suites remain instance obligations (E.22/E.23).

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

## Status

Sorry-free, axiom-free beyond the Lean-core triple. Signature byte-identical to the committed
stub. The signed binder `hF` (`F.Monic`) is INERT — monicity of `F` follows from the two lists'
monicity through `hprod`, so the proof never reads it; it is KEPT per the statement fence and the
`unusedVariables` linter is disabled for this declaration only.
-/

namespace Uniformity.Density.Ladder

open Polynomial

-- `hF` is an INERT signed binder (monicity of `F` follows from the two lists through `hprod`);
-- it is KEPT per the statement fence, so the linter is disabled for this declaration only.
set_option linter.unusedVariables false in
/-- **E.21** THEOREM T2.KEY-BOUNDARY, schema form (`EFF.T2.32`): with `(BOUNDARY-PROD)` supplied
as data — monic boundary factors `P_i`, monic residual blocks `B_j`, and per-block terminal
emissions whose weights already total the block degree (E.20's engine output) — the boundary
degrees plus the emitted weights total `deg F`.

⚠ The decomposition is an INPUT. Nothing here computes a gcd, asserts `G = Φ`, asserts `Φ`
irreducible, peels one factor, or claims a peel lowers `μ` by one (`EFF.T2.28`'s four-part
fence); a reducible key boundary is exactly why `boundary` is a list (`EFF.T2.44`). -/
theorem key_boundary {O : Type*} [CommRing O] [IsDomain O]
    (F : Polynomial O) (hF : F.Monic)
    (boundary : List (Polynomial O)) (blocks : List (Polynomial O))
    (hprod : F = boundary.prod * blocks.prod)
    (hbmon : ∀ P ∈ boundary, Polynomial.Monic P)
    (hkmon : ∀ B ∈ blocks, Polynomial.Monic B)
    (emit : Polynomial O → Multiset ℕ)
    (hemit : ∀ B ∈ blocks, (emit B).sum = B.natDegree) :
    (boundary.map Polynomial.natDegree).sum
      + (blocks.map (fun B => (emit B).sum)).sum = F.natDegree := by
  -- monic ⟹ nonzero, so neither list contains `0` and neither product vanishes
  have hb0 : (0 : Polynomial O) ∉ (boundary : Multiset (Polynomial O)) := by
    simp only [Multiset.mem_coe]
    exact fun h => (hbmon 0 h).ne_zero rfl
  have hk0 : (0 : Polynomial O) ∉ (blocks : Multiset (Polynomial O)) := by
    simp only [Multiset.mem_coe]
    exact fun h => (hkmon 0 h).ne_zero rfl
  have hbne : boundary.prod ≠ 0 := by
    simpa using Multiset.prod_ne_zero (s := (boundary : Multiset (Polynomial O))) hb0
  have hkne : blocks.prod ≠ 0 := by
    simpa using Multiset.prod_ne_zero (s := (blocks : Multiset (Polynomial O))) hk0
  -- degrees add along each list product, and across the outer product
  have hbdeg : boundary.prod.natDegree = (boundary.map Polynomial.natDegree).sum := by
    simpa using Polynomial.natDegree_multiset_prod (boundary : Multiset (Polynomial O)) hb0
  have hkdeg : blocks.prod.natDegree = (blocks.map Polynomial.natDegree).sum := by
    simpa using Polynomial.natDegree_multiset_prod (blocks : Multiset (Polynomial O)) hk0
  have hF' : F.natDegree = boundary.prod.natDegree + blocks.prod.natDegree := by
    rw [hprod, Polynomial.natDegree_mul hbne hkne]
  -- the emitted weights are the block degrees, block by block
  have hmap : blocks.map (fun B => (emit B).sum) = blocks.map Polynomial.natDegree :=
    List.map_congr_left hemit
  rw [hF', hbdeg, hkdeg, hmap]

/-! ## Gate (executed `example`s, not blueprint declarations)

Three checks. (a) the identity fires at a real decomposition, with a genuinely composite
boundary/block split, so the two sides are not accidentally the same expression. (b) the DEPENDS
edge to E.20 is discharged as a term: the engine's per-block output really is a legal `emit`,
so the composition layer composes. (c) the monicity hypotheses are load-bearing — dropping them
makes the statement FALSE (a zero factor collapses the product's degree while the boundary sum
keeps counting), which is the failure mode `hbmon`/`hkmon` exist to exclude. -/

section Gate

-- (a) `F = X³` over `ℤ`, split as boundary `[X]` and one residual block `[X²]` whose read
-- emitted two terminal classes of weight 1. `1 + 2 = 3`, through the theorem.
example :
    ((([Polynomial.X] : List (Polynomial ℤ)).map Polynomial.natDegree).sum
      + (([Polynomial.X ^ 2] : List (Polynomial ℤ)).map
          (fun B => ((fun _ => ({1, 1} : Multiset ℕ)) B).sum)).sum)
      = (Polynomial.X ^ 3 : Polynomial ℤ).natDegree :=
  key_boundary (Polynomial.X ^ 3) (Polynomial.monic_X_pow 3) [Polynomial.X] [Polynomial.X ^ 2]
    (by simp only [List.prod_cons, List.prod_nil, mul_one]; ring)
    (by simp)
    (by simp)
    (fun _ => ({1, 1} : Multiset ℕ))
    (by simp)

-- (b) THE E.20 EDGE, DISCHARGED. Run E.20's engine once per block from a per-block start state
-- whose weight is the block's degree; the leaves' weight multiset is then a legal `emit`, and
-- `key_boundary` closes the accounting. This is the composition the blueprint asserts in prose
-- ("the terminal emissions of the blocks' reads, together with the boundary factors …").
example {O : Type*} [CommRing O] [IsDomain O] {W : Type*} (r : WellFoundedRelation W)
    (step : LadderState W → Finset (LadderState W))
    (terminal : LadderState W → Prop) [DecidablePred terminal]
    (wt : LadderState W → ℕ)
    (hdec : ∀ s, ¬ terminal s → ∀ s' ∈ step s, (ladderState_wf r).rel s' s)
    (hcons : ∀ s, ¬ terminal s → ∑ s' ∈ step s, wt s' = wt s)
    (F : Polynomial O) (hF : F.Monic) (boundary blocks : List (Polynomial O))
    (hprod : F = boundary.prod * blocks.prod)
    (hbmon : ∀ P ∈ boundary, Polynomial.Monic P)
    (hkmon : ∀ B ∈ blocks, Polynomial.Monic B)
    (start : Polynomial O → LadderState W)
    (hstart : ∀ B ∈ blocks, wt (start B) = B.natDegree) :
    ∃ emit : Polynomial O → Multiset ℕ,
      (∀ B ∈ blocks, (emit B).sum = B.natDegree) ∧
      (boundary.map Polynomial.natDegree).sum
        + (blocks.map (fun B => (emit B).sum)).sum = F.natDegree := by
  choose leaves _hterm hwt using read_terminates_exhausts r step terminal wt hdec hcons
  refine ⟨fun B => (leaves (start B)).map wt, fun B hB => ?_, ?_⟩
  · simpa using (hwt (start B)).trans (hstart B hB)
  · exact key_boundary F hF boundary blocks hprod hbmon hkmon _
      (fun B hB => by simpa using (hwt (start B)).trans (hstart B hB))

-- (c) MONICITY IS LOAD-BEARING. Without it the identity is false: over `ℤ` take the boundary
-- `[0, X]` and no blocks. The boundary degrees sum to `0 + 1 = 1`, while the product is `0`,
-- of `natDegree` `0`. So the hypotheses `hbmon`/`hkmon` are not decoration — they are what
-- makes "degrees add" true.
example : ¬ ∀ (F : Polynomial ℤ) (boundary blocks : List (Polynomial ℤ)),
    F = boundary.prod * blocks.prod →
    (boundary.map Polynomial.natDegree).sum
      + (blocks.map Polynomial.natDegree).sum = F.natDegree := by
  intro h
  have hbad := h 0 [0, Polynomial.X] [] (by simp)
  simp at hbad

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.key_boundary

end AxCheck
