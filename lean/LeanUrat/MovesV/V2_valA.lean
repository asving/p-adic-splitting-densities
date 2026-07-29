/-  MovesV unit V2-4 `val_a_burden` (RE-KEYED Codex-4; REWRITTEN REV 5, M-1) —
    Theorem VAL(a)'s burden as the typed structure `ValA`: tbl_count AT THE
    DATUM'S OWN TargetIx, off-key zero clauses, guarded landing ties.
    `valA_gate` is DEFERRED to V6 (the gate instances). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

structure ValA (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) : Prop where
  tbl_count : ∀ (d : MoveData n C) {q₀}
    (x : S.Hist q₀ (V.toStepCells.symm d.src))
    (hzc : S.zc x) (hq : q₀ ∈ V.Pools) (j : Fin (V.mdom d).comps.length),
    ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ)
      = S.cntraw (V.moveOf d) x (((V.mdom d).comps.get j).base)
  tbl_offkey : ∀ (d : MoveData n C) (β : TargetIx n (C.bd d.s) C.bd d.m d.o)
    {q₀ : ℚ}, q₀ ∈ V.Pools → β ≠ d.tix →
    ((C.T d.s d.m d.o d.α β).eval q₀ : ℚ) = 0
  tbl_countT : ∀ {v} (d : TermData n C v) {q₀}
    (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩))
    (hzc : S.zc x) (hq : q₀ ∈ V.Pools) (j : Fin (V.mdomT d).comps.length),
    ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ)
      = S.cntrawT (V.moveOfT d) x (((V.mdomT d).comps.get j).base)
  tbl_offkeyT : ∀ {v} (d : TermData n C v) (v' : VLabel n)
    (ht' : ¬ (C.bd d.s).cont d.m d.o) {q₀ : ℚ}, q₀ ∈ V.Pools → v' ≠ v →
    ((C.T d.s d.m d.o d.α (.term ht' v')).eval q₀ : ℚ) = 0
  tgt_supported : ∀ (d : MoveData n C) {q₀}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (h : Hpt (S.dim (V.moveOf d))), q₀ ∈ V.Pools →
    V.activeState q₀ (V.toStepCells.symm d.src) →
    ¬ V.activeState q₀ (V.toStepCells.symm d.tgt) →
    S.cntraw (V.moveOf d) x h = 0
  ent_supported : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    ¬ V.activeState q₀ β₀ → V.entCensus ε β₀ q₀ = 0

end LeanUrat.MovesV
