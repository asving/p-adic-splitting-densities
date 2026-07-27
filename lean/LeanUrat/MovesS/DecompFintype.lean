/-
Unit U-11 `decompFintype` (medium) — Fintype on multiset decompositions.
moves_ref: the b_e^split convolution index "σ′ = σ₁ ⊎ … ⊎ σ_m" is a finite sum.
sketch: induct on m; each g 0 ≤ σ' ranges over finitely many sub-multisets.
Sorried instance (E-phase); counted in the census.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable instance decompFintype {V : Type*} [DecidableEq V] (m : ℕ)
    (σ' : Multiset V) : Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'} :=
  sorry

end LeanUrat.MovesS
