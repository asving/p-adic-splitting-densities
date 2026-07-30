/-
Unit C5.massCodim
moves_ref: §C.1.5 (ZC-c): mass(Σ_{k−1}) = p^{nN}·∏ vol_nom(E_fresh), division-free
  (statement unchanged; JetSetup retyped)

Proof route (per the manifest sketch): rewrite `C0.digitSystemMass`
(`mass = p^{m − numPinned}`) then the `C5.massRec` content
(`numPinned (Σ_k) = Σ_{i<k} m*(ν_i)`).

Both `C0_digitSystemMass` and `C5_massRec` are imported as built, sorry-free sibling units
(`C5_massRec` derives its step brick from `C4_numPinnedStep`), so this file is just the
two-rewrite assembly.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_digitSystemMass
import LeanUrat.MovesC.C5_massRec

open Polynomial LeanUrat.Moves
namespace LeanUrat.MovesC
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C5_massCodim {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (k : ℕ) (hk : k ≤ H.nodes.length) : (J.Sigma k).mass = p ^ (m - (Finset.range k).sum (fun i => (J.fresh i).mstar)) := by
  -- assemble: `mass = p^{m − numPinned}` (C0) then `numPinned = Σ m*` (C5.massRec).
  rw [C0_digitSystemMass (J.Sigma k), C5_massRec J k hk]

end
end LeanUrat.MovesC
