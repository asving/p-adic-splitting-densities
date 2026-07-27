/-
Unit E9.encIdx_inj  (MovesD campaign, E-phase)
moves_ref: "The map enc′: η ⟼ (the side-digit tuples (d_j) of its reads; the selection
indices (s_r)) is an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r})" (L11 — now a
THEOREM at the η-class granularity).  [REV 9: rev-6's hnorm rider REMOVED as unused
(Fable#7/coordinator) — the injection is hypothesis-free.]
[REV 8, Codex#6 c.3 — the ∅ dispatch]: `encTargetP_empty` — L11's encoding at P̂ = ∅ is
the SINGLETON-TO-UNIT map (Pref(∅) = {∅}, target = the empty product, card 1 = C_∅).
deps: E1, E3, E4, E7, E8; Defs (Matches.hmonic, encIdx).
sketch: classes are (digit-tuple, ψ-image) sequences; the d_r counted digits + the scoped
monic tie (§0.5) recover the FULL digit tuple; the digit tuple determines RanchImage
(hRanch, coefficient images); E8 recovers ψImage from the rank. So encIdx equal ⟹
etaData equal ⟹ i = j (subtype ext).  difficulty: medium-hard.
hypothesis_fields: none [REV 9 — hnorm removed as unused].
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- L11's injection, at the η-class granularity — hypothesis-free. -/
theorem encIdx_inj :
    Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F (P : ShapePrefix)) := by
  sorry

/-- The ∅ dispatch: at P̂ = ∅ the encoding target is the empty product — card 1 = C_∅. -/
theorem encTargetP_empty (hP : (P : ShapePrefix).reads = []) :
    Nat.card (EncTargetP p F (P : ShapePrefix)) = 1 := by
  sorry

end LeanUrat.MovesD
