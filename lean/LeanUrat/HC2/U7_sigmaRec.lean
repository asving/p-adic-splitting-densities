/-
Unit U7.mkSigma_init_rec  (HC-2 campaign, E-phase — blueprint §5 Layer A; two lemmas)
moves_ref: MovesC `JetSetup.init`/`recursion` field types.
deps: D7, C0.pinTransport (PROVED), S.Theta_uni.  difficulty: medium.
hypothesis_fields: none.
sketch: init is definitional (`topLocus`); recursion = the ∃-witness for `IsFreshAttach`
(pinTransport's solution-set law + the strip/value pin-attachment constructor — the value
clause pins its whole support to the unique solution, by `LevelClause.count` at
codim = |support|) + `pinTransportSystem_spec`.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- INITIALIZATION: nothing is pinned before the root read (`JetSetup.init`'s type). -/
theorem mkSigma_init {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) :
    ∀ c : Fin (n * N), (mkSigma H n N S vOf 0).pinned c = false := by
  intro c; rfl

/-- THE STRATUM RECURSION (`JetSetup.recursion`'s type at `mkStratum`): the constructed
chain satisfies `Σ_{i+1} = Θ_i*(Σ_i ∩ stratum(ν_i))` solution-setwise. -/
theorem mkSigma_recursion {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ x : Fin (n * N) → ZMod p,
      (mkSigma H n N S vOf (i+1)).IsSolution x ↔
        ((mkSigma H n N S vOf i).IsSolution (S.Theta i x) ∧
          mkStratum H n N S vOf i (S.Theta i x)) := by
  -- STOP-THE-LINE (frozen frame mismatch; see the note block below the theorem).
  -- The RHS reads the fresh stratum at `S.Theta i x`, but `mkSigma (i+1)` is DEFINED as
  -- `pinTransportSystem … (mkFresh … i hi)`, whose only characterization,
  -- `IsFreshAttach` (HC2/Defs.lean), reads that fresh locus at `x` (`fd.sat x`).  After the
  -- forced reduction, the goal becomes
  --   `A ∧ (mkFresh … i hi).sat x  ↔  A ∧ (mkFresh … i hi).sat (S.Theta i x)`
  -- (with `A = (mkSigma … i).IsSolution (S.Theta i x)`), i.e. it demands `S.Theta i`-
  -- invariance of the fresh locus, which no `PresentSeed` field supplies (`Theta_uni` only
  -- gives unitriangularity, and `mkFresh`'s strip/value clauses are moved by the carries).
  -- Unprovable as stated without editing the frozen `IsFreshAttach` (`fd.sat x → fd.sat (Θ x)`).
  sorry

end LeanUrat.MovesJ
