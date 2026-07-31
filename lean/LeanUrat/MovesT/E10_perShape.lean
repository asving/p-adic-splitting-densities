/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E8_treeExp
import LeanUrat.MovesT.E9_fiberDisjoint

/-! # T-E10 `perShape_law` [hard; pre-approved split E10a rigidity trio / E10b] —
Σ_{T of shape T̂} μ(fiber T) = C_T̂(p)·p^{−A(T̂)} (MOVES 7537–7545). `hfin`/`hA` are
GONE — both DERIVED (REV 5, Codex-4 #4). The `hdict` TWO-VERDICT COMPARISON ROW
(REV 6, Codex-5 #5 — HELD on the note's own text 7537–7540) rides in the blueprint;
`hdict` is the pointwise transcription of the note's shape-determination clause,
owner: the shape-side theory through T-V8's dictionary. MULTINOMIAL SCOPE
(7548–7557): the m!/(∏ mⱼ!) factorization is NOT claimed. `NsFree`/`shapeClass` are
Defs carriers. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- E10a rigidity leg 1 (REV 5, Codex-4 #4's hfin leg): ext-equal trees are EQUAL —
off `chains`, `hleaf`/`hns_leaf` force `leafV = none`/`¬ nsLeaf`. -/
theorem vtree_ext_eq (Tr Tr' : VTree p F) (h : VTree.ext Tr Tr') : Tr = Tr' := by
  obtain ⟨hchains, hhenV, hrest⟩ := h
  have hleafeq : Tr.leafV = Tr'.leafV := by
    funext H
    by_cases hH : H ∈ Tr.chains
    · exact (hrest H hH).1
    · have hH' : H ∉ Tr'.chains := by rw [← hchains]; exact hH
      have hA : Tr.leafV H = none :=
        Option.not_isSome_iff_eq_none.mp (by rw [Tr.hleaf H]; exact fun hc => hH hc.1)
      have hB : Tr'.leafV H = none :=
        Option.not_isSome_iff_eq_none.mp (by rw [Tr'.hleaf H]; exact fun hc => hH' hc.1)
      rw [hA, hB]
  have hnseq : Tr.nsLeaf = Tr'.nsLeaf := by
    funext H
    by_cases hH : H ∈ Tr.chains
    · exact propext (hrest H hH).2
    · have hH' : H ∉ Tr'.chains := by rw [← hchains]; exact hH
      have hA : ¬ Tr.nsLeaf H := fun hc => hH (Tr.hns_leaf H hc).1
      have hB : ¬ Tr'.nsLeaf H := fun hc => hH' (Tr'.hns_leaf H hc).1
      exact propext ⟨fun a => absurd a hA, fun a => absurd a hB⟩
  cases Tr with
  | mk chains hfin hne hcl henV hhen leafV hleaf nsLeaf hnsl =>
    cases Tr' with
    | mk chains' hfin' hne' hcl' henV' hhen' leafV' hleaf' nsLeaf' hnsl' =>
      subst hchains
      subst hhenV
      subst hleafeq
      subst hnseq
      rfl

/-- E10a rigidity leg 2: the class injects into the finite box's fiber sets. -/
theorem shapeClass_finite (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : (shapeClass Tr₀ T χ).Finite := by
  haveI : Finite ↥(shapeClass Tr₀ T χ) := by
    apply Finite.of_injective
      (β := Box p m) (fun Tr : ↥(shapeClass Tr₀ T χ) => Classical.choose Tr.2.2.2)
    intro Tr₁ Tr₂ hfx
    have hx : Classical.choose Tr₁.2.2.2 = Classical.choose Tr₂.2.2.2 := hfx
    have s1 := Classical.choose_spec Tr₁.2.2.2
    have s2 := Classical.choose_spec Tr₂.2.2.2
    rw [hx] at s1
    exact Subtype.ext (vtree_ext_eq Tr₁.1 Tr₂.1 (tree_fiber_disjoint Tr₁.1 Tr₂.1 T χ _ s1 s2))
  exact Set.toFinite _

/-- E10a rigidity leg 3: A(T̂) is constant across the class THROUGH the dictionary
(`shapeExp`, Defs §2.5 — the ShapeEquiv bijection transports per-site exponents). -/
theorem AofTr_shape_const (Tr₀ Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (heq : ShapeEquiv n Tr Tr₀) (L₀ : SiteLedger Tr₀ T CA χ)
    (L : SiteLedger Tr T CA χ)
    (hdict : ∀ H ∈ Tr.chains, L.siteExp H = shapeExp (shapeOfH H n) n)
    (hdict₀ : ∀ H ∈ Tr₀.chains, L₀.siteExp H = shapeExp (shapeOfH H n) n) :
    AofTr Tr L = AofTr Tr₀ L₀ := by
  obtain ⟨hhen, φ, ⟨hinj, hsurj⟩, hpre, hshape, hnsφ⟩ := heq
  have e1 : ∑ H ∈ Tr.hfin.toFinset, L.siteExp H
      = ∑ H ∈ Tr.hfin.toFinset, shapeExp (shapeOfH H n) n :=
    Finset.sum_congr rfl (fun H hH => hdict H (Tr.hfin.mem_toFinset.mp hH))
  have e0 : ∑ H ∈ Tr₀.hfin.toFinset, L₀.siteExp H
      = ∑ H ∈ Tr₀.hfin.toFinset, shapeExp (shapeOfH H n) n :=
    Finset.sum_congr rfl (fun H hH => hdict₀ H (Tr₀.hfin.mem_toFinset.mp hH))
  simp only [AofTr]
  rw [e1, e0]
  congr 1
  apply Finset.sum_bij (fun H hH => (φ ⟨H, Tr.hfin.mem_toFinset.mp hH⟩).1)
  · intro a ha
    rw [Set.Finite.mem_toFinset]
    exact (φ ⟨a, Tr.hfin.mem_toFinset.mp ha⟩).2
  · intro a₁ ha₁ a₂ ha₂ heqi
    exact congrArg Subtype.val (hinj (Subtype.ext heqi))
  · intro b hb
    obtain ⟨⟨a, ha⟩, hfa⟩ := hsurj ⟨b, Tr₀.hfin.mem_toFinset.mp hb⟩
    exact ⟨a, Tr.hfin.mem_toFinset.mpr ha, congrArg Subtype.val hfa⟩
  · intro a ha
    rw [hshape ⟨a, Tr.hfin.mem_toFinset.mp ha⟩]

/-- E10b: the per-shape law. RE-KEYED at the T RE-RATIFICATION (2026-08-01 — same
row changes as `treeExp`): `hjcm` keys the per-site `JCmultiAt` at the site's own
node `H.lastNode` (the site-entrance keying), and the site-level (SIB) row `hsibT`
is the ONE-CELL `SibCountAt` per class member (conditioning = roster cell =
`cellAt H`, the c/cSplit unification). -/
theorem perShape_law (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ)
    (hns₀ : NsFree Tr₀) (hreal₀ : Realizes T χ Tr₀)
    (L₀ : SiteLedger Tr₀ T CA.toCellData χ)
    (Lat : ∀ Tr ∈ shapeClass Tr₀ T χ, SiteLedger Tr T CA.toCellData χ)
    (scat : ∀ Tr h, TreeScaffold Tr T CA.toCellData χ (Lat Tr h) trackOf)
    (hjcm : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ),
      ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ (Lat Tr h))
        (h2 : 2 ≤ (Lat Tr h).sides H),
        JCmultiAt T CA.toCellData χ ((Lat Tr h).parentSt H) H.lastNode
          ((Lat Tr h).splitAt H hH.1 h2))
    (hsibT : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ),
      ∀ H (hH : H ∈ Tr.chains),
        2 ≤ (CA.toCellData.branchSetOf ((Lat Tr h).cellAt H)).card →
        SibCountAt T CA.toCellData χ ((Lat Tr h).parentSt H) H.lastNode
          ((Lat Tr h).cellAt H) ((scat Tr h).splitFrame H hH).S)
    (hdict : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ), ∀ H ∈ Tr.chains,
      (Lat Tr h).siteExp H = shapeExp (shapeOfH H n) n)
    (hdict₀ : ∀ H ∈ Tr₀.chains, L₀.siteExp H = shapeExp (shapeOfH H n) n)
    -- [QUEUE ITEM 5 (E5 hoist ripple 1, TV-A3 shape) 2026-07-31: the ∀-g (U)∧(R)
    --  row, Tr-independent — ONE row serves every class member's `treeExp` call.]
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    (∑ Tr ∈ (shapeClass_finite Tr₀ T χ).toFinset,
        Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x})
        * p ^ (AofTr Tr₀ L₀)
      = Nat.card ↥(shapeClass Tr₀ T χ) * p ^ m := by
  have hcard : Nat.card ↥(shapeClass Tr₀ T χ)
      = (shapeClass_finite Tr₀ T χ).toFinset.card := by
    rw [Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card (shapeClass Tr₀ T χ) (shapeClass_finite Tr₀ T χ)]
  have key : ∀ Tr ∈ (shapeClass_finite Tr₀ T χ).toFinset,
      Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x} * p ^ (AofTr Tr₀ L₀) = p ^ m := by
    intro Tr hTr
    have hmem : Tr ∈ shapeClass Tr₀ T χ := (Set.Finite.mem_toFinset _).mp hTr
    have heq : ShapeEquiv n Tr Tr₀ := hmem.1
    have hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H := hmem.2.1
    have hreal : Realizes T χ Tr := hmem.2.2
    have hE8 := treeExp Tr T χ trackOf CA hχ hrc hred hsib hreal (Lat Tr hmem)
      (scat Tr hmem) (hjcm Tr hmem) (hsibT Tr hmem) hdet hUR
    have hA : AofTr Tr (Lat Tr hmem) = AofTr Tr₀ L₀ :=
      AofTr_shape_const Tr₀ Tr T CA.toCellData χ heq L₀ (Lat Tr hmem)
        (hdict Tr hmem) hdict₀
    rw [← hA]
    exact hE8
  rw [Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_const, hcard, smul_eq_mul]

end LeanUrat.MovesT
