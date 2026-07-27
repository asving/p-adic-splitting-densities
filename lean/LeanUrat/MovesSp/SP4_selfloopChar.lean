/-
Unit Sp.selfloopChar [REV 4, Codex-4 FIXED — the note's SUCC is
catalogue-restricted ("SUCC(s) := { s′ ∈ 𝒮_n^raw : … }"), so the characterized
relation is Succ-MEMBERSHIP for a catalogue letter, not bare SuccStep] —
moves_ref: "SELF-LOOPS, syntactically. s has a self-loop edge iff s ∈ SUCC(s):
necessarily e = g = 1 (else D grows strictly, (B1)) with W(s) = μ(s) — the
POST-REC species whose window equals their own selection multiplicity."
deps: Sp.memCoherent. sketch: Succ-membership = InCatalogue s ∧ SuccStep s s; the
helper: (→) D = e·g·D with D ≥ 1 forces e·g = 1; W = μ; the tag iff gives postRec.
(←) instantiate StageLaws' match; laws reflexive at e = g = 1, μ = W. loops3's
Bool filter reflects the helper. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem selfloop_iff {n : ℕ} {s : Species} (hs : InCatalogue n s) :
    s ∈ Succ n s ↔ (s.tag = .postRec ∧ s.e = 1 ∧ s.sel = some (1, s.W)) := sorry

/-- the StageLaws computation both directions use. -/
theorem selfloop_succStep_iff {n : ℕ} {s : Species}
    (hc : Coherent s) (hb : Budget n s) : SuccStep n s s ↔ (s.tag = .postRec ∧
    s.e = 1 ∧ s.sel = some (1, s.W)) := sorry

end LeanUrat.MovesSp
