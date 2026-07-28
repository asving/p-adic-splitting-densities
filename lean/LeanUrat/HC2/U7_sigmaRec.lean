/-
Unit U7.mkSigma_init_rec  (HC-2 campaign, E-phase — blueprint §5 Layer A; two lemmas)
moves_ref: MovesC `JetSetup.init`/`recursion` field types.
deps: D7, C0.pinTransport (PROVED), S.Theta_uni.  difficulty: medium.
hypothesis_fields: none.
sketch: init is definitional (`topLocus`); recursion = the ∃-witness for `IsFreshAttach`
(pinTransport's solution-set law + the strip/value pin-attachment constructor — the value
clause pins its whole support to the unique solution, by `LevelClause.count` at
codim = |support|) + `pinTransportSystem_spec`.
RESTATED-POST-DEFS-REPAIR DC-2 (2026-07-28; statement byte-unchanged): `IsFreshAttach`'s
solution-set clause repaired `fd.sat x → fd.sat (Θ x)` per the blueprint §9 F-7
authorization — the in-file stop-the-line obstruction is discharged; U7 is
QUEUED-PROVABLE-NOW.
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
  -- STOP-THE-LINE, SECOND RECORD (2026-07-28, ESCALATION ROUND — supersedes the DC-2
  -- "QUEUED-PROVABLE-NOW" note below): FALSE AS STATED, MACHINE-REFUTED.
  -- `lean/scratch_U7_recursion_false.lean` (`U7Refute.mkSigma_recursion_FALSE`, green,
  -- Lean-core axioms only) refutes THIS statement's ∀-S form: U27's concrete inert gate
  -- seed perturbed by the constant unitriangular shift `σ x c = x c + 1` is a LAWFUL
  -- `PresentSeed` (every field discharged; `Theta_uni` is the only law on Θ and does not
  -- see the correction's value), and at read 0 the post-DC-2 `IsFreshAttach` spec is
  -- UNSATISFIABLE: clause (1) `fd.sat (Θ x)` forces the all-ones point INTO the solution
  -- set (its σ-image is 0), clauses (2)+(3) (LITERAL-zero solve at the pinned strip
  -- coordinate) force it OUT. So `mkSigma` takes the junk branch (`= mkSigma i`) and the
  -- iff fails at x = 0. ROOT CAUSE: DC-2 transported clause (1) through Θ but left
  -- clauses (3)/(4) as literal zeros in the post-Θ coordinates; on the transported locus
  -- a strip coordinate solves to −corr_c(x_<c), not 0. Repair options (designer-round,
  -- DC-3 class — see the scratch file header): (i) transport clauses (3)/(4) through Θ
  -- (solve = −corr); (ii) a new D5-fenced seed law forcing Θ-corrections to vanish at
  -- fresh strip coordinates on the locus (the C.1.5(2) "carries vanish" content);
  -- (iii) re-key the (ZC-a) literal-zero consumers (U9c/U10c). Statement byte-untouched
  -- per the fence; sorry stands pending the ruling.
  -- [Superseded DC-2 record: the earlier `fd.sat x` mismatch was repaired; the route
  -- `C0.pinTransport` + pin-attachment + `pinTransportSystem_spec` was to close U7 —
  -- its ∃-obligation is exactly what the countermodel refutes.]
  sorry

end LeanUrat.MovesJ
