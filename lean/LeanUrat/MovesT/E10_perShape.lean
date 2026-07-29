/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
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
  sorry

/-- E10a rigidity leg 2: the class injects into the finite box's fiber sets. -/
theorem shapeClass_finite (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : (shapeClass Tr₀ T χ).Finite := by
  sorry

/-- E10a rigidity leg 3: A(T̂) is constant across the class THROUGH the dictionary
(`shapeExp`, Defs §2.5 — the ShapeEquiv bijection transports per-site exponents). -/
theorem AofTr_shape_const (Tr₀ Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (heq : ShapeEquiv n Tr Tr₀) (L₀ : SiteLedger Tr₀ T CA χ)
    (L : SiteLedger Tr T CA χ)
    (hdict : ∀ H ∈ Tr.chains, L.siteExp H = shapeExp (shapeOfH H n) n)
    (hdict₀ : ∀ H ∈ Tr₀.chains, L₀.siteExp H = shapeExp (shapeOfH H n) n) :
    AofTr Tr L = AofTr Tr₀ L₀ := by
  sorry

/-- E10b: the per-shape law. -/
theorem perShape_law (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (hsib : SibCount T CA χ)
    (hns₀ : NsFree Tr₀) (hreal₀ : Realizes T χ Tr₀)
    (L₀ : SiteLedger Tr₀ T CA χ)
    (Lat : ∀ Tr ∈ shapeClass Tr₀ T χ, SiteLedger Tr T CA χ)
    (scat : ∀ Tr h, TreeScaffold Tr T CA χ (Lat Tr h) trackOf)
    (hjcm : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ),
      ∀ H (hH : H ∈ multiSites Tr T CA χ (Lat Tr h))
        (h2 : 2 ≤ (Lat Tr h).sides H),
        JCmultiAt T CA χ ((Lat Tr h).parentSt H) ((Lat Tr h).cellAt H)
          ((Lat Tr h).splitAt H hH.1 h2))
    (hdict : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ), ∀ H ∈ Tr.chains,
      (Lat Tr h).siteExp H = shapeExp (shapeOfH H n) n)
    (hdict₀ : ∀ H ∈ Tr₀.chains, L₀.siteExp H = shapeExp (shapeOfH H n) n) :
    (∑ Tr ∈ (shapeClass_finite Tr₀ T χ).toFinset,
        Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x})
        * p ^ (AofTr Tr₀ L₀)
      = Nat.card ↥(shapeClass Tr₀ T χ) * p ^ m := by
  sorry

end LeanUrat.MovesT
