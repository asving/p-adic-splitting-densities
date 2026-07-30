/-
Unit Sp.n1singleton [REV 3, G2 — was Sp.n1Clause; the cycle is split: only the
root-confirming half is consumed here, and Sp.n1Word consumes THIS unit]
[REV 4, Codex-12 + Fable NOTE B — the sketch's route declared; confirmingRoot1 a
DefsN3 literal] — moves_ref: "(G6) … (or W = n = 1 at the root — the degenerate
degree)" + the n = 1 clause: "At n = 1 the catalogue word is the single ROOT letter".
deps: Sp.speciesEnumComplete, Sp.n1RootConfirming, Sp.succTerminal, Sp.g6Forcing.
sketch: root-admissible at n = 1 pins every field (g6Forcing at W = 1);
terminal ⇒ no step case. difficulty: easy-medium.
-/
import LeanUrat.MovesSp.DefsN3
import LeanUrat.MovesSp.SP1_g6Forcing
import LeanUrat.MovesSp.SP3_n1Root
import LeanUrat.MovesSp.SP0_succTerminal

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- The confirming root letter IS root-admissible at n = 1 (the backward witness):
every clause is a decidable evaluation except the two vacuous `sel = some gm →`
riders, discharged by `sel = none`. -/
private theorem rootAdmissible_confirmingRoot1 : RootAdmissible 1 confirmingRoot1 := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · -- Coherent confirmingRoot1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      first | rfl | decide
  · -- Budget 1 confirmingRoot1
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | rfl | decide

theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1 := by
  intro s
  constructor
  · intro h
    induction h with
    | @root s hRA =>
      obtain ⟨hRoot, hCoh, hBud⟩ := hRA
      obtain ⟨he, hell, hs0, ha, hlam, hlf, hrf, hsel⟩ := w1_forces hCoh hBud hRoot.2.2.2
      obtain ⟨_, _, _, ⟨hslots, hd⟩, _, _⟩ := hCoh
      obtain ⟨htag, hD, hw, hW⟩ := hRoot
      obtain ⟨tag, D, w, W, e, s0, ell, a, d, slots, lam, sel, lflank, rflank⟩ := s
      simp only at htag hD hw hW he hell hs0 ha hlam hlf hrf hsel hslots hd
      subst htag hD hw hW he hell hs0 ha hlam hlf hrf hsel hslots hd
      rfl
    | @step s s' hIn hSucc _ih =>
      exfalso
      exact stageLaws_terminal s s' (by rw [_ih]; rfl) hSucc.1
  · rintro rfl; exact InCatalogue.root rootAdmissible_confirmingRoot1

end LeanUrat.MovesSp
