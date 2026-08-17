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
  sorry

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
