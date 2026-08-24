/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C130a — the freeze-v2 carrier core, re-homed (CC-0)

CC-0 of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§3, the reuse boundary): the chain-realization
carrier layers C.130b--k must reuse `StageLive`, `GaugeLive`, `DeepLive`, `TerminalReceiver`,
and `ArisingCore` — but those declarations lived in `Uniformity.ChapI.I10FreezeV2`, and a
chapter-C implementation cannot import chapter I without reversing the dependency.  This file
is therefore the MOVE mandated by CC-0: the five declarations below are byte-identical to the
freeze-v2 originals (same names, same namespace `Uniformity.Density.Tower`), and
`I10FreezeV2` now imports this module instead of declaring them.  There is exactly one
declaration site for each name; nothing here is new mathematics.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]

/-- D-TIF-4's range on which stage data may be read. -/
def StageLive (r j : ℕ) : Prop := 1 ≤ j ∧ j ≤ r

/-- D-TIF-4's range on which a gauge read may use `u_(j+1)`. -/
def GaugeLive (r j : ℕ) : Prop := 1 ≤ j ∧ j < r

/-- D-TIF-4's genuinely deep live range. -/
def DeepLive (r j : ℕ) : Prop := 3 ≤ j ∧ j < r

/-- D-TIF-3's single coherent interpretation of the frozen `Kt`: `Kt` is equivalent to the
terminal field `K_r`, while every live `K_j` maps into it through a chain-compatible embedding.

The family `levelHom` is total only because C.83's `DeepTower.fld` is total with junk outside
the live range.  Every law that reads tower data is explicitly range guarded. -/
structure TerminalReceiver (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r : ℕ)
    (T : DeepTower.{0, uKt} F H₀ hpin r) (Kt : Type uKt) [Field Kt] where
  topEquiv : T.fld r ≃+* Kt
  levelHom : (j : ℕ) → T.fld j →+* Kt
  levelHom_terminal : levelHom r = topEquiv.toRingHom
  levelHom_step : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r),
    levelHom j = (levelHom (j + 1)).comp
      ((T.step j hj1 hjr).symm.toRingHom.comp (AdjoinRoot.of (T.ψ j)))

/-- The already-typeable, non-residue part of D-TIF-4's legal GENTOW5-1 instance.

This is named `ArisingCore`, not `ArisingInput`: the latter name is reserved for the full
C.130j carrier after the OPEN C.130d/C.130g--C.130k layers and the §9 witness land. -/
structure ArisingCore (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (n : ℕ) where
  π : O
  hπ : Irreducible π
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  finite : Finite (IsLocalRing.ResidueField O)
  F : KeyFrame O π
  H₀ : ℕ
  hpin : F.Pin H₀
  r : ℕ
  i : ℕ
  hi : StageLive r i
  T : DeepTower.{0, uKt} F H₀ hpin r
  receiver : TerminalReceiver F H₀ hpin r T Kt
  stageKey : Polynomial O
  stageDeg : ℕ
  stageKey_monic : stageKey.Monic
  stageKey_degree : stageKey.natDegree = stageDeg
  F₀ : Polynomial O
  F₀_monic : F₀.Monic
  μ : ℕ
  hμ : 1 ≤ μ
  degree_input : F₀.natDegree = n
  degree_block : n = μ * stageDeg
  keyfree : IsCoprime
    (F₀.map (algebraMap O (FractionRing O)))
    (stageKey.map (algebraMap O (FractionRing O)))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.StageLive
#print axioms Uniformity.Density.Tower.GaugeLive
#print axioms Uniformity.Density.Tower.DeepLive
#print axioms Uniformity.Density.Tower.TerminalReceiver
#print axioms Uniformity.Density.Tower.ArisingCore

end AxCheck
