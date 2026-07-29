/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D14 `chain_charge_ledger` — MovesS §W4-SYNC S-6: the chain telescopes to the
chain's ROOT-CELL entrance (Σ₀), consuming `state_cell` at each step; the contract's
`ReadLedger` carrier DECLARED VERBATIM (`ReadLedgerT`, Defs) with the (BDY) index
convention L = the LAST READ INDEX (REV 4, Codex-3 #17). `fe` stays the one
owner-supplied datum (MovesV's `isEntrance` — the S-6 residual, quoted). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem chain_charge (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : ∀ H' ∈ chainReads Tr H, L.sides H' = 1)
    (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p))
    (hent : ∀ H₁ ∈ chainReads Tr H, H₁.nodes.length = 1 →
      L.parentSt H₁ = .red g ψ) :
    Nat.card ↥(stateEvent T (some H))
        * p ^ ((chainReads Tr H).map (L.siteExp ·)).sum
      = Nat.card ↥(rootCell χ g) := by
  sorry

/-- H's own read is a member, so the last-read index is well-defined on chains. -/
theorem chainReads_ne (Tr : VTree p F) (H : History p F) (hH : H ∈ Tr.chains) :
    (chainReads Tr H) ≠ [] := by
  sorry

/-- the (BDY)-split identities AT the constructed value — rfl-level unfolding
(= the contract's `W8_bdy RL` conjunction). PROVED. -/
theorem readLedgerOf_bdy (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellData p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F)
    (fe : ℕ) (hfe : fe ≤ (chainReads Tr H).length - 1) :
    (readLedgerOf Tr L H fe hfe).Wcharge
        = ∑ r ∈ Finset.Icc 0 fe, (readLedgerOf Tr L H fe hfe).charge r ∧
    (readLedgerOf Tr L H fe hfe).βcharge
        = ∑ r ∈ Finset.Icc (fe + 1) (readLedgerOf Tr L H fe hfe).L,
            (readLedgerOf Tr L H fe hfe).charge r :=
  ⟨rfl, rfl⟩

end LeanUrat.MovesT
