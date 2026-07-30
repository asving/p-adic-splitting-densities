/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL01b_shallowMove
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T7_alphabetSpan

/-!
# HC1.CL01c_shallowTower — Tshallow assembly + the card certificate (BP5 CL-01c)

**Unit CL-01c** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4 CL-01, split
per REVISION 2 finding 11). E-PHASE SKELETON: statements + `sorry` bodies. The tower
literal below is compiled NOW (its `base`/`move` fields are the sorry slots), so the
projection pins hold by `rfl` already at E-phase.

**Informal statement.** Assemble ScratchC6's shallow instance
`Tshallow : Tower 2 (GaloisField 2 2)` — K = 1, stg = [TshallowBase, TshallowChild],
the one CL-01b increment — and certify the shallow-height deficiency at
(b, γ) = (0, 0): the level set is nonempty (the single coordinate l = 0, slots ≡ 0)
yet `card 𝔸(0,0) ≠ card F_{K+1}` (𝔸 is one base-digit line over F_Q = F₂:
card ≤ 2 < 4 = card F₄ — ScratchC6 header, MOVES 2160–2165's "STRICTLY SMALLER at
shallow heights").

**Deps.** CL-01a, CL-01b, DefsCar (`levelSet`/`alphabet`), T7_alphabetSpan (the card
toolkit for the ≤ 2 bound). CL-01c is the last of the CL-01 portfolio.

**Proof sketch.** Nonemptiness: exhibit `⟨0, fun _ => if top then 0 else 0, …⟩` — the
coordinate l = 0, slot ≡ 0 (top slot 0 = b); `ht = 0 + 0 = 0`, `blk = 0`. Uniqueness
at (0,0) (not stated, but drives the card bound): κ₀ = h₀/(e₀·STR₀) = 1 and κ₁ =
h′/(e′·STR₁) > 0 force l = 0, slots ≡ 0. Card: by the singleton level set, `alphabet
0 0` is the closure of ONE digit-line image `y ↦ typComposite (single c₀ y)` over
F_Q = F₂ (2 digits), so `card 𝔸 ≤ 2` (additive image of a 2-element digit group;
T7's span toolkit), while `card F_{K+1} = card ↥(⊤ : Subfield F₄) = 4` via
`TshallowChild_pins.1` + `C6_cardK_bridge`-style counting. 2 ≠ 4 closes.

**E-phase resolutions recorded.**
* The blueprint's "card F₄" is rendered as `Nat.card ↥(Tshallow.stg (Fin.last
  Tshallow.K)).K` — the exact right-hand side of the fenced C6 fullness clause, so the
  certificate composes (at CL-02's fence transition ONLY) with the live
  `C6_forces_unconditional_fullness` + `Tshallow_levelSet_nonempty` into the negation
  of pre-repair C6 at `Tshallow`.
* The nonemptiness certificate is split out (`Tshallow_levelSet_nonempty`): the fenced
  C6 carries an `hne` hypothesis, so the composition needs it as a separate piece.

**LANDING GATE (§3.1, BINDING — this is the unit the gate is FOR).** While
`C6_alphabetCard`'s sorry is live, NO negation-shaped compiled artifact lands in the
live tree, and conservatively (escalation E-2) the gate also holds back the
one-composition-away pieces: a PROVED `Tshallow` + `Tshallow_alphabet_deficient`.
This skeleton proves nothing (all certificate bodies `sorry`); the PROOFS develop on
a side branch / scratch build whose green record cites the branch commit, and the
compiled pieces land ATOMICALLY with CL-02's fence transition, retargeted at the
frozen `C6_stmt_pre_repair` copy of the pre-repair statement (the R-7
kernel-freezing pattern). difficulty: hard-fable (portfolio cap shared with
CL-01a/b). PERMITTED OUTCOME: BLOCKED + the exact missing-constructor list (feeds
Q-2: the adjudication may rest on the Lean-core ScratchC6 certificates + the
math-level record if the compiled tower is insanely costly). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **The shallow tower** (CL-01c assembly): one base read + one g = 2 increment.
The `base` and `move` fields are the unit's remaining construction slots
(`TshallowBase_isBase` and `TshallowMove` respectively); `K`, `stg`, `hcharF` are
fixed here so the projection pins below are definitional. -/
noncomputable def Tshallow : Tower 2 (GaloisField 2 2) where
  K := 1
  stg := ![TshallowBase, TshallowChild]
  base := TshallowBase_isBase
  move := fun k =>
    match k with
    | ⟨0, _⟩ => TshallowMove
    | ⟨n + 1, h⟩ => absurd h (by omega)
  hcharF := inferInstance

/-- Tshallow has exactly one move. -/
theorem Tshallow_K : Tshallow.K = 1 := rfl

/-- Stage 0 of Tshallow is CL-01a's base stage. -/
theorem Tshallow_stg_zero : Tshallow.stg 0 = TshallowBase := rfl

/-- The top stage of Tshallow is CL-01b's child stage. -/
theorem Tshallow_stg_last : Tshallow.stg (Fin.last Tshallow.K) = TshallowChild := rfl

/-- CL-01c certificate 1: the shallow level set at (b, γ) = (0, 0) is NONEMPTY (the
coordinate l = 0, slots ≡ 0) — the `hne` piece of the eventual composition against
the fenced C6. -/
theorem Tshallow_levelSet_nonempty : (Tshallow.levelSet 0 0).Nonempty := by
  sorry

/-- CL-01c certificate 2 (THE card certificate): at the shallow height the alphabet is
strictly deficient — `card 𝔸(0,0) ≠ card F_{K+1}` (2-element digit line vs the
4-element top residue field). Together with `Tshallow_levelSet_nonempty` and the live
`C6_forces_unconditional_fullness`, this refutes pre-repair `C6_alphabetCard` at
`Tshallow` — that composition is GATE-HELD (see the module docstring) and is NOT
compiled by this unit. -/
theorem Tshallow_alphabet_deficient :
    Nat.card ↥(Tshallow.alphabet 0 0)
      ≠ Nat.card ↥(Tshallow.stg (Fin.last Tshallow.K)).K := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.Tshallow_levelSet_nonempty
#print axioms LeanUrat.HC1.Tshallow_alphabet_deficient
