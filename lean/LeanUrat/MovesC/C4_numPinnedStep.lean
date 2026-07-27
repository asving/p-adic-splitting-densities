/-
Unit C4.numPinnedStep
moves_ref: §C.1.5' (ZC-c) codimension bookkeeping via PIN-WELLDEF (statement unchanged; JetSetup retyped)

The per-step PIN count law: consuming read `ν_i`'s fresh clauses adds exactly `m*(ν_i)` to the
pin count of the state cylinder. Proof (per the manifest sketch): write both masses as
p-powers via `C0.digitSystemMass` (`mass = p^{m−numPinned}`), combine with `C4.stepMass`
(`mass(Σ_{i+1})·p^{m*} = mass(Σ_i)`), and pin the exponent by `Nat.pow` injectivity (`p ≥ 2`,
each `numPinned ≤ m`), then discharge the Nat-subtraction bookkeeping with `omega`.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_digitSystemMass
import LeanUrat.MovesC.C4_stepMass

open Polynomial LeanUrat.Moves
namespace LeanUrat.MovesC
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `numPinned` never exceeds the number of coordinates. -/
private lemma numPinned_le {m : ℕ} (D : Locus p m) : D.numPinned ≤ m := by
  rw [DigitSystem.numPinned]
  calc (Finset.univ.filter (fun i => D.pinned i)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

theorem C4_numPinnedStep {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) (hi : i < H.nodes.length) : (J.Sigma (i+1)).numPinned = (J.Sigma i).numPinned + (J.fresh i).mstar := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  -- Both masses as p-powers (C0.digitSystemMass).
  have hM1 : (J.Sigma (i+1)).mass = p ^ (m - (J.Sigma (i+1)).numPinned) := C0_digitSystemMass _
  have hM0 : (J.Sigma i).mass = p ^ (m - (J.Sigma i).numPinned) := C0_digitSystemMass _
  -- The per-step mass relation (C4.stepMass).
  have hstep : (J.Sigma (i+1)).mass * p ^ (J.fresh i).mstar = (J.Sigma i).mass :=
    C4_stepMass J i hi
  -- Rewrite into a single equality of p-powers.
  rw [hM1, hM0, ← pow_add] at hstep
  -- Injectivity of `p ^ ·` (needs `2 ≤ p`) pins the exponents.
  have hexp : (m - (J.Sigma (i+1)).numPinned) + (J.fresh i).mstar = m - (J.Sigma i).numPinned :=
    Nat.pow_right_injective hp2 hstep
  -- Both pin counts are ≤ m; Nat-subtraction bookkeeping closes the goal.
  have hb1 : (J.Sigma (i+1)).numPinned ≤ m := numPinned_le _
  have hb0 : (J.Sigma i).numPinned ≤ m := numPinned_le _
  omega

end
end LeanUrat.MovesC
