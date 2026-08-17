/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116b2
import Uniformity.ChapH.H116b3i
import Uniformity.ChapH.H116b3ii
import Uniformity.ChapH.H116b3iii
import Uniformity.ChapB.B39a

/-!
# Uniformity.ChapH.H116b3iiib — the ¬IsCSState transport, part 2 (SKELETON v2)

**Chapter H, NODE H.116b3-iii (2/2)** — the assembly `not_isCSState_plantedPoly_swap` at the
byte-frozen A-H.8 statement, per the block record §3's steps (3a)–(3f) as corrected by A-H.8.
FENCE A-H.8/F1 binds. ⚠ Consumes `B39a` (rider signed, owner ratification-by-compile
2026-08-17).

CHAIN: `planted_map_residue_eq` (PROVED — the u = 0 branch's engine) →
`planted_side_transport_at_zero` (u = 0: the full witness transport off the equal residue
maps) → `planted_delta_above_line` (u > 0: steps (3a)+(3b)+(3c), THE BEAST) → the assembly
(via b3-ii's congruences and part 1's bridge, `monicPoly_coeff_self` as the plumbing).
`sorry`-carrying until each fills; NOT in any roll-up until sorry-free.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The u = 0 engine (record step (3e), first half).** The two planted products have EQUAL
reductions mod `π`: every alpha factor reduces to `X ^ μ_p` independently of its presentation
(`alphaParent_map_residue`), and the cofactor is shared. -/
theorem planted_map_residue_eq {π : O} (hπ : Irreducible π) {N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) :
    (plantedPoly π L bb' Qc).map (residue O) = (plantedPoly π L bb Qc).map (residue O) := by
  unfold plantedPoly
  rw [Polynomial.map_mul, Polynomial.map_mul]
  congr 1
  rw [Polynomial.map_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [alphaParent_map_residue hπ _ (hLchild p.1 p.2).2.1,
    alphaParent_map_residue hπ _ (hLchild p.1 p.2).2.1]

/-- Height-0 digit polynomial of a constant: the residue. -/
private theorem digPoly_zero_C {π : O} (c : O) :
    digPoly π 0 (Polynomial.C c) = Polynomial.C (residue O c) := by
  unfold digPoly
  rw [Polynomial.natDegree_C]
  rw [Finset.sum_range_one, Polynomial.coeff_C_zero, pow_zero, mul_one, digAt_zero]

/-- The monic support value at slope `(0, 1)` vanishes (attained at the top coefficient). -/
private theorem suppVal_zero_one_of_monic {g : Polynomial O} (hg : g.Monic) :
    suppVal X g 0 1 = 0 := by
  refine le_antisymm ?_ zero_le
  have hmem : g.natDegree ∈ Finset.range (g.natDegree + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_self _)
  have hle := Finset.inf_le (f := fun j => (1 : ℕ) • npHgt X g j + ((0 * j : ℕ) : ℕ∞)) hmem
  have hval : (1 : ℕ) • npHgt X g g.natDegree + ((0 * g.natDegree : ℕ) : ℕ∞) = 0 := by
    rw [npHgt_X, hg.coeff_natDegree,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 isUnit_one]
    simp
  rw [suppVal]
  exact hval ▸ hle

/-- At `(0, 1)` on a monic polynomial, on-side means height zero, i.e. unit coefficient,
i.e. nonzero residue. -/
private theorem onSide_zero_one_iff {g : Polynomial O}
    (hg : g.Monic) (j : ℕ) :
    OnSide X g 0 1 j ↔ (g.map (residue O)).coeff j ≠ 0 := by
  have hOn : OnSide X g 0 1 j ↔ npHgt X g j = 0 := by
    unfold OnSide
    rw [suppVal_zero_one_of_monic hg]
    constructor
    · intro h
      have := h
      rwa [one_nsmul, Nat.zero_mul, Nat.cast_zero, add_zero] at this
    · intro h
      rw [one_nsmul, h, Nat.zero_mul, Nat.cast_zero, add_zero]
  rw [hOn, npHgt_X, Polynomial.coeff_map]
  constructor
  · intro h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
      (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  · intro h
    exact IsDiscreteValuationRing.addVal_eq_zero_iff.2
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h)

/-- **The u = 0 branch (record step (3e), second half).** At `(u, ℓ) = (0, 1)` the whole side
datum — support value, side set, pinned height (necessarily `0`), and residual polynomial —
is read off `f mod π`, so equal reductions transport the CS witness verbatim. B.77 is NOT
usable here (A-H.8 §2.2: `Visible π X f 1` fails on the planted `f`). -/
private theorem planted_side_transport_at_zero {π : O} (hπ : Irreducible π)
    {f f' : Polynomial O} (hf : f.Monic) (hf' : f'.Monic)
    (hdeg : f'.natDegree = f.natDegree)
    (hmap : f'.map (residue O) = f.map (residue O)) :
    sideSet X f' 0 1 = sideSet X f 0 1 ∧
      ∀ (hne : (sideSet X f 0 1).Nonempty) (hne' : (sideSet X f' 0 1).Nonempty),
        resPoly π X f' 0 1 hne' 0 = resPoly π X f 0 1 hne 0 := by
  classical
  have hres : ∀ j, residue O (f'.coeff j) = residue O (f.coeff j) := by
    intro j
    have := congrArg (fun p => Polynomial.coeff p j) hmap
    simpa [Polynomial.coeff_map] using this
  have hset : sideSet X f' 0 1 = sideSet X f 0 1 := by
    unfold sideSet
    rw [hdeg]
    refine Finset.filter_congr fun j _ => ?_
    rw [onSide_zero_one_iff hf', onSide_zero_one_iff hf, hmap]
  refine ⟨hset, fun hne hne' => ?_⟩
  have hmin : sideMin X f' 0 1 hne' = sideMin X f 0 1 hne := by
    unfold sideMin
    have key : ∀ (h₁ : (sideSet X f' 0 1).Nonempty) (h₂ : (sideSet X f 0 1).Nonempty),
        (sideSet X f' 0 1).min' h₁ = (sideSet X f 0 1).min' h₂ := by
      rw [hset]; intro h₁ h₂; rfl
    exact key hne' hne
  have hmax : sideMax X f' 0 1 hne' = sideMax X f 0 1 hne := by
    unfold sideMax
    have key : ∀ (h₁ : (sideSet X f' 0 1).Nonempty) (h₂ : (sideSet X f 0 1).Nonempty),
        (sideSet X f' 0 1).max' h₁ = (sideSet X f 0 1).max' h₂ := by
      rw [hset]; intro h₁ h₂; rfl
    exact key hne' hne
  have hdegs : sideDeg X f' 0 1 hne' = sideDeg X f 0 1 hne := by
    unfold sideDeg
    rw [hmin, hmax]
  unfold resPoly
  rw [hdegs]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  unfold resCoeff
  rw [hmin]
  unfold resMk
  rw [dev_X, dev_X, Nat.zero_sub, digPoly_zero_C, digPoly_zero_C, hres]

/-- **L2 = record steps (3a)+(3b)+(3c): the swap difference sits strictly above the planted
supporting line** at every `(u, ℓ)` with `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ` — exactly
b3-ii's `habove` hypothesis. Mechanism: the per-factor graded swap bound (b3-i), the
Minkowski identity by iterating `suppVal_mul_gen` over `L.attach` and once against the
cofactor (B39a; `hnfz` free from `sideSet_nonempty_gen`), and the convolution bound via
`Polynomial.coeff_mul`. -/
private theorem planted_delta_above_line {π : O} (hπ : Irreducible π) {N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) :
    ∀ j, suppVal X (plantedPoly π L bb Qc) u ℓ
      < ℓ • npHgt X (plantedPoly π L bb' Qc - plantedPoly π L bb Qc) j
          + ((u * j : ℕ) : ℕ∞) := by
  sorry

set_option linter.unusedVariables false in
/-- **H.116b3 = H.116b3-iii (2/2) [NEW NODE: A-H.7; RE-SPLIT: A-H.8].** THE `¬ IsCSState`
TRANSPORT — swapping the child presentations of a planted product while keeping the cofactor
cannot create a composite-stage event. Statement BYTE-UNCHANGED from the leanspec stub.
Assembly: extract the CS witness at the planted lift of `c'` (`monicPoly_coeff_self` + `hc'`),
transport its side data across the swap — `u > 0` through `planted_delta_above_line` +
b3-ii's three congruences, `u = 0` (whence `ℓ = 1` by coprimality) through
`planted_side_transport_at_zero` — and land the witness at the planted lift of `c`, closing
with part 1's `isCSState_of_exists_lift` against `hcs`. -/
theorem not_isCSState_plantedPoly_swap {π : O}
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hπ : Irreducible π) {m N r : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (hdeg : (∑ p ∈ L, p.1) + r = m)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) (c c' : ClusterState O m N)
    (hc : proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) = c.1)
    (hc' : proj O m N (fun i : Fin m => (plantedPoly π L bb' Qc).coeff (i : ℕ)) = c'.1)
    (h0 : ¬ IsDrainState c) (h0' : ¬ IsDrainState c') (hcs : ¬ IsCSState π c) :
    ¬ IsCSState π c' := by
  sorry

end Uniformity.Density.Induction
