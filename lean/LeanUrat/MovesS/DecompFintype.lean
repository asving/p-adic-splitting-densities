/-
Unit U-11 `decompFintype` (medium) — Fintype on multiset decompositions.
moves_ref: the b_e^split convolution index "σ′ = σ₁ ⊎ … ⊎ σ_m" is a finite sum.
sketch: induct on m; each g 0 ≤ σ' ranges over finitely many sub-multisets.
Filled instance (E-phase, sorry-free); counted in the census.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable instance decompFintype {V : Type*} [DecidableEq V] (m : ℕ)
    (σ' : Multiset V) : Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'} := by
  -- Each leg `g j` is a sub-multiset of `σ'` (it is ≤ the total sum, which is `σ'`),
  -- so the decomposition subtype injects into `Fin m → {μ // μ ≤ σ'}`, a finite type.
  have hfin : Finite {g : Fin m → Multiset V // ∑ j, g j = σ'} := by
    apply Finite.of_injective
      (β := Fin m → {μ : Multiset V // μ ≤ σ'})
      (fun g j => ⟨g.1 j,
        le_of_le_of_eq
          (Finset.single_le_sum (fun i _ => Multiset.zero_le (g.1 i)) (Finset.mem_univ j))
          g.2⟩)
    intro g g' h
    exact Subtype.ext (funext fun j => Subtype.ext_iff.mp (congrFun h j))
  -- Pass the finiteness witness explicitly: an implicit `Fintype.ofFinite _` would let
  -- instance resolution wander to a different `Finite` path in the import graph.
  exact @Fintype.ofFinite _ hfin

end LeanUrat.MovesS
