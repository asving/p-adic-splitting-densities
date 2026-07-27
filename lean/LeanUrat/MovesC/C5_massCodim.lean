/-
Unit C5.massCodim
moves_ref: §C.1.5 (ZC-c): mass(Σ_{k−1}) = p^{nN}·∏ vol_nom(E_fresh), division-free
  (statement unchanged; JetSetup retyped)

Proof route (per the manifest sketch): rewrite `C0.digitSystemMass`
(`mass = p^{m − numPinned}`) then the `C5.massRec` content
(`numPinned (Σ_k) = Σ_{i<k} m*(ν_i)`).

`C0_digitSystemMass` is imported (a built sibling unit). The `C5.massRec` induction is
reproduced INLINE here because the sibling file `C5_massRec.lean` currently carries its
step brick as a private `sorry` (its `C4.numPinnedStep` dependency was restated, not yet
imported, when that file was written) — importing it would put `sorryAx` in this unit's
footprint. Instead the step brick is taken from the NOW-BUILT, sorry-free sibling unit
`C4_numPinnedStep` (imported below), so this file is fully proved: base case from
`J.init`, step from `C4_numPinnedStep`, assembly by the two rewrites.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_digitSystemMass
import LeanUrat.MovesC.C4_numPinnedStep

open Polynomial LeanUrat.Moves
namespace LeanUrat.MovesC
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C5_massCodim {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (k : ℕ) (hk : k ≤ H.nodes.length) : (J.Sigma k).mass = p ^ (m - (Finset.range k).sum (fun i => (J.fresh i).mstar)) := by
  -- `C5.massRec`, reproduced inline: `numPinned (Σ_k) = Σ_{i<k} m*(ν_i)`, induction on `k`,
  -- with the step brick supplied by the imported sorry-free unit `C4_numPinnedStep`.
  have hRec : ∀ k : ℕ, k ≤ H.nodes.length →
      (J.Sigma k).numPinned = (Finset.range k).sum (fun i => (J.fresh i).mstar) := by
    intro k
    induction k with
    | zero =>
        intro _
        -- base: `J.init` pins nothing before the root read, so `numPinned (Σ_0) = 0`.
        have hz : (J.Sigma 0).numPinned = 0 := by
          unfold DigitSystem.numPinned
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _
          rw [J.init i]
          simp
        rw [hz, Finset.range_zero, Finset.sum_empty]
    | succ k ih =>
        intro hk'
        have hklt : k < H.nodes.length := Nat.lt_of_succ_le hk'
        rw [C4_numPinnedStep J k hklt, Finset.sum_range_succ, ih (le_of_lt hklt)]
  -- assemble: `mass = p^{m − numPinned}` (C0) then `numPinned = Σ m*` (the reproduced rec).
  rw [C0_digitSystemMass (J.Sigma k), hRec k hk]

end
end LeanUrat.MovesC
