/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B63
import Uniformity.ChapB.B67

/-!
# Uniformity.ChapB.B71 — the full order-1 `typeOf` read

**Chapter B, NODE B.71** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C. One signed
declaration.

*The statement.* Let `f` be monic of positive degree with `f̄ = ∏_{i ∈ s} φ̄_i ^ {a_i}`, the `φ̄_i`
distinct and the `φ_i` order-1 keys, and let a peel `g : ι → Polynomial O` be **supplied**
(`hgmon`/`hgprod`/`hgres` — B.67's conclusion as hypotheses, per §12 rule 4(c): an `axiom` stub
cannot bind an existential's witness, and landed peel uniqueness makes the statement well-posed
over any supplied peel). If every block has `dev (φ i) (g i) 0 ≠ 0`, separable residuals, and lies
in D-3's perimeter (or satisfies `B-BOX-1` outside it), then

```
(typeOf f).data = ∑_{i ∈ s} (order1Type π (φ i) (g i)).data.
```

## Proof

1. **The peel's multiset additivity.** B.63a's `typeOf_prod` over `hgprod` gives
   `(typeOf f).data = ∑ i ∈ s, (typeOf (g i)).data`.
2. **Per block, a rewrite.** *(A-F.11.)* B.63's re-signed conclusion delivers
   `(typeOf (g i)).data = (order1Type π (φ i) (g i)).data` **as its first clause**, applied at
   `(φ, f) := (φ i, g i)` with `hμ := a i` positive, `hsep i` / `hperim i` verbatim, and
   `hnz i` as B.63's new `h0`. A-F.9 had already added `hnz` here for an unrelated refutation
   (the singleton block `g i₀ = φ i₀`), and it is exactly the per-block hypothesis A-F.11 needs —
   so this node's SIGNATURE is byte-unchanged and no call site pays anything. The former route
   (open B.63's existential `T` per block and re-index) is void and was in any case underivable.
2′. **The one degenerate block the signature admits.** *(A-F.11.)* `a : ι → ℕ` carries no
   positivity clause while B.63 needs `0 < μ`, so `a i = 0` is handled off-route: there
   `(g i).map (residue O) = 1`, so `(g i).natDegree = 0` (landed `natDegree_eq_of_map_eq`) and
   `g i = 1` by monicity; both sides of the per-block identity are then the empty multiset —
   `typeOf 1` is `⟨0⟩` (the `typeOf_prod` instance at the empty index), and
   `slopeFinset π (φ i) 1 = ∅` because a one-point polygon has no two-point side (this is
   `B66.lean:149`'s `order1Type_zero` argument at `f = 1` rather than `f = 0`, isolated below as
   `slopeFinset_eq_empty_of_natDegree_zero`).
3. Sum.

DEPENDS: B.63 (`typeOf_of_separable_residuals`, its first clause) · B.66 (`order1Type`,
`order1Type_data`) · B.66a (`mem_slopeFinset_imp`, for step 2′) · B.63a (`typeOf_prod`, through
B.63's import) · landed `Uniformity.Hensel.natDegree_eq_of_map_eq`,
`Polynomial.eq_one_of_monic_natDegree_zero`.

**B.67 and B.68 are in the blueprint's DEPENDS but are not consumed here.** In the signed data
form the peel arrives as hypotheses, so B.67 is a *supplier for the caller*, not for this proof;
B.67 is imported anyway so that the DEPENDS edge is a real import edge. B.68 is the order-0
special case and is nowhere used.

**SIZE.** blueprint 26 lines; landed 27.

**TEETH.** `W12-SHAPE`, `W12-ORACLE`, `HE-SIG` → **executable regression** retained; the `σ(λ)`
readout dictionary of `EFF.W12.29` is this node's instance table and B.83/B.84's gates check two
of its rows.

SOURCE: `EFF.W12.09` (THEOREM W-12.A); `EFF.W12.29`; `EFF.HE3.16`.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through B.63 — the 2026-08-16
owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **Step 2′'s polygon fact.** A polynomial of degree `0` has a one-point `φ`-polygon, hence no
two-point side, hence no slope: the canonical slope supplier is empty. (`B66.lean`'s
`order1Type_zero` is the `f = 0` instance of this argument; step 2′ needs the `f = 1` one.) -/
theorem slopeFinset_eq_empty_of_natDegree_zero (π : O) (φ f : Polynomial O)
    (hf : f.natDegree = 0) : slopeFinset π φ f = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  have hcard := (mem_slopeFinset_imp hp).2.2
  have hsub : sideSet φ f p.1 p.2 ⊆ Finset.range (f.natDegree + 1) := by
    intro j hj
    have hj' : j ∈ Finset.filter (OnSide φ f p.1 p.2) (Finset.range (f.natDegree + 1)) := hj
    exact (Finset.mem_filter.mp hj').1
  have hle := Finset.card_le_card hsub
  rw [hf, Finset.card_range] at hle
  omega

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `hd : 0 < f.natDegree` is part of the frozen signature and is not used by the proof; the
-- statement holds at `f = 1` too (empty peel, empty type on both sides).
set_option linter.unusedVariables false in
/-- **B.71 — the full order-1 `typeOf` read.** Over a supplied peel of `f` into order-1 blocks,
the splitting type's datum is the sum of the blocks' order-1 data. -/
theorem typeOf_order1 (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ : ι → Polynomial O} {a : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    (hres : f.map (IsLocalRing.residue O)
      = ∏ i ∈ s, ((φ i).map (IsLocalRing.residue O)) ^ (a i))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic) (hgprod : f = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (a i))
    (hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)
    (hsep : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ h : (sideSet (φ i) (g i) u ℓ).Nonempty, 1 < (sideSet (φ i) (g i) u ℓ).card →
        ∀ H₀ : ℕ, npHgt (φ i) (g i) (sideMin (φ i) (g i) u ℓ h) = (H₀ : ℕ∞) →
          (resPoly π (φ i) (g i) u ℓ h H₀).Separable)
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g i → IsPure (φ i) gS u ℓ →
        ∀ hne : (sideSet (φ i) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt (φ i) gS (sideMin (φ i) gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField (φ i)), ψ.Monic → Irreducible ψ →
            (∃ c : (resField (φ i))ˣ, resPoly π (φ i) gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ (φ i).natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                (φ i).natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    (typeOf f).data = ∑ i ∈ s, (order1Type π (φ i) (g i)).data := by
  classical
  -- ## step 1 — the peel's multiset additivity
  rw [hgprod, typeOf_prod hgmon]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases Nat.eq_zero_or_pos (a i) with ha0 | hapos
  · -- ## step 2′ — the degenerate block `a i = 0`
    have hgi1 : g i = 1 := by
      refine Polynomial.eq_one_of_monic_natDegree_zero (hgmon i hi) ?_
      have := Uniformity.Hensel.natDegree_eq_of_map_eq (hgmon i hi) (hgres i hi)
      rwa [ha0, pow_zero, Polynomial.natDegree_one] at this
    have hone : (typeOf (1 : Polynomial O)).data = 0 := by
      have h := typeOf_prod (s := (∅ : Finset ι)) (g := g) (by simp)
      simpa using h
    rw [hgi1, hone, order1Type_data,
      slopeFinset_eq_empty_of_natDegree_zero π (φ i) 1 Polynomial.natDegree_one]
    simp
  · -- ## step 2 — B.63 at the block, a rewrite
    exact (typeOf_of_separable_residuals hπ (hkey i hi) (hgmon i hi) hapos (hgres i hi)
      (hnz i hi) (hsep i hi) (hperim i hi)).1

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.slopeFinset_eq_empty_of_natDegree_zero
#print axioms Uniformity.Density.Leaf.typeOf_order1
end AxCheck
