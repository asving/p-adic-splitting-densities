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
# Uniformity.ChapH.H116b3iiib — the ¬IsCSState transport, part 2 (SKELETON)

**Chapter H, NODE H.116b3-iii (2/2)** — the assembly `not_isCSState_plantedPoly_swap` at the
byte-frozen A-H.8 statement, structured per the block record §3's step order (3a)–(3f) as
corrected by A-H.8 (findings F-1/F-2/F-3). FENCE A-H.8/F1 binds. ⚠ Consumes `B39a`'s
general graded product law — the human-review-flag rider is SIGNED (owner
ratification-by-compile, 2026-08-17).

SKELETON STATE: the lemma chain below carries `sorry` bodies (the survival floor after five
storm-killed agent attempts); NOT in any roll-up until sorry-free. Fill order: L2 (the
convolution estimate, hardest) → L3 (the u = 0 branch) → L1 (plumbing) → the assembly.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **L1 (plumbing).** A monic polynomial of `natDegree = m` is `monicPoly` of its own
coefficient vector — the identification of the planted lift. -/
private theorem monicPoly_coeffFn_eq {m : ℕ} {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = m) :
    monicPoly (fun i : Fin m => f.coeff (i : ℕ)) = f := by
  sorry

/-- **L2 = record steps (3a)+(3b)+(3c): the swap difference sits strictly above the planted
supporting line.** With `f := plantedPoly π L bb Qc`, `f' := plantedPoly π L bb' Qc`, at
every `(u, ℓ)` with `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, every abscissa satisfies b3-ii's
line-depth hypothesis for the perturbation `f' − f`. Mechanism: the per-factor graded swap
bound (b3-i `pow_grade_succ_dvd_coeff_alphaParent_sub` at the trivial frame difference),
the Minkowski identity by iterating `suppVal_mul_gen` over `L.attach` and once against the
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

/-- **L3 = record step (3e): the `u = 0` branch.** At `(u, ℓ) = (0, 1)` the whole side datum
is read off `f mod π`, and the two planted products have EQUAL reductions
(`alphaParent_map_residue`: both reduce to `X^{Σ μ_p}` times the cofactor's reduction), so
side set, side min, and residual polynomial agree on the nose. B.77 is NOT usable here
(A-H.8 §2.2: `Visible π X f 1` fails on the planted `f`); this is the record's direct
argument. -/
private theorem planted_side_data_eq_at_zero {π : O} (hπ : Irreducible π) {N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    sideSet X (plantedPoly π L bb' Qc) 0 ℓ = sideSet X (plantedPoly π L bb Qc) 0 ℓ := by
  sorry

set_option linter.unusedVariables false in
/-- **H.116b3 = H.116b3-iii (2/2) [NEW NODE: A-H.7; RE-SPLIT: A-H.8].** THE `¬ IsCSState`
TRANSPORT — swapping the child presentations of a planted product while keeping the cofactor
cannot create a composite-stage event. Statement BYTE-UNCHANGED from the leanspec stub.
Assembly = the record's step order: extract the CS witness at the planted lift of `c'`
(part 1's bridge direction reversed via L1), transport its side data across the swap —
`u > 0` through L2 + b3-ii's three congruences, `u = 0` through L3 — and land the witness at
the planted lift of `c`, closing with the part-1 bridge `isCSState_of_exists_lift` against
`hcs`. -/
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
