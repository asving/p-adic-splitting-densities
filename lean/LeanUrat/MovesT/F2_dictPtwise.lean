/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.F0_preHalt
import LeanUrat.MovesD.F1_enum

/-! # T-F2 `preHalt_dict_ptwise` [hard] — THE DICTIONARY, RESTRICTED TO PRE-HALT MARKS
(MOVES 7590–7603): the class↔chain bijection with EVERY leg warranted (REV 3, Codex-2
#15: `hph`/`hsep` explicit premises, §0-rowed, owner HC-2). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem preHalt_dict_ptwise {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (Tr : VTree p F) (x : Box p m) (hfib : Tr.fiberAt T χ x)
    (hsep : ∀ H H', H ∈ Tr.chains → H' ∈ Tr.chains →
      H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      (∃ i : PrefIdx n pol P, SameClass i H ∧ SameClass i H') → H = H') :
    Nat.card {i : PrefIdx n pol P //
        x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = Tr.chainCount n P := by
  -- FORWARD leg: a class `i` with `x ∈ S.fiber i` and `PreHalt (reprOf i)` sends its
  -- representative into `Tr.chains`, matching `P̂`.
  have key_fwd : ∀ (i : PrefIdx n pol P), x ∈ S.fiber i → PreHalt (reprOf i) →
      reprOf i ∈ Tr.chains ∧ (P : ShapePrefix).MatchesHist (reprOf i) := by
    intro i hx hph_i
    have hmem : T.mem (some (reprOf i)) x := (hcyl i x).mp hx
    have hprune : PrunedMem T (reprOf i) x :=
      (preHalt_prunedMem T (reprOf i) (reprOf i).nonempty x hmem).mpr hph_i
    have hchain : reprOf i ∈ Tr.chains :=
      (hfib.1 (reprOf i)).mpr ⟨(reprOf i).nonempty, hprune⟩
    exact ⟨hchain, (reprOf_mem i).1⟩
  -- BACKWARD leg (part 1): a chain of `Tr` matching `P̂` lies in `Pref(P̂)`, is realized,
  -- and is pre-halted.  `mem_realizable` supplies coherence/realizability/canonicity,
  -- `hib` supplies InBox, and T-F0 converts pruning to `PreHalt`.
  have key_bwd : ∀ (H : History p F), H ∈ Tr.chains → (P : ShapePrefix).MatchesHist H →
      H ∈ PrefSet n pol P ∧ T.mem (some H) x ∧ PreHalt H := by
    intro H hHc hHm
    have hprune : PrunedMem T H x := ((hfib.1 H).mp hHc).2
    have hmem : T.mem (some H) x := hprune.1
    have hreal := T.mem_realizable H x hmem
    have hinbox : InBox n H := hib H x hmem
    have hpref : H ∈ PrefSet n pol P := ⟨hHm, hreal.1, hreal.2.1, hinbox, hreal.2.2⟩
    have hphH : PreHalt H := (preHalt_prunedMem T H H.nonempty x hmem).mp hprune
    exact ⟨hpref, hmem, hphH⟩
  -- BACKWARD leg (part 2): the class of such a chain lands in the LHS subtype.
  have key_bwd2 : ∀ (H : History p F) (hHc : H ∈ Tr.chains)
      (hHm : (P : ShapePrefix).MatchesHist H),
      x ∈ S.fiber (⟨etaData (P : ShapePrefix) H,
            ⟨H, (key_bwd H hHc hHm).1, rfl⟩⟩ : PrefIdx n pol P) ∧
      PreHalt (reprOf (⟨etaData (P : ShapePrefix) H,
            ⟨H, (key_bwd H hHc hHm).1, rfl⟩⟩ : PrefIdx n pol P)) := by
    intro H hHc hHm
    obtain ⟨hpref, hmem, hphH⟩ := key_bwd H hHc hHm
    let j : PrefIdx n pol P := ⟨etaData (P : ShapePrefix) H, ⟨H, hpref, rfl⟩⟩
    show x ∈ S.fiber j ∧ PreHalt (reprOf j)
    have hsc : SameClass j H := rfl
    exact ⟨(hcyl j x).mpr ((heta j H hpref hsc x).mp hmem), (hph j H hpref hsc).mp hphH⟩
  -- BACKWARD leg (part 3): `reprOf` of that class is the chain itself — `hsep` pins the
  -- unique chain of `Tr` in one class (both are in `Tr.chains ∩ Pref(P̂)`).
  have key_right : ∀ (H : History p F) (hHc : H ∈ Tr.chains)
      (hHm : (P : ShapePrefix).MatchesHist H),
      reprOf (⟨etaData (P : ShapePrefix) H,
          ⟨H, (key_bwd H hHc hHm).1, rfl⟩⟩ : PrefIdx n pol P) = H := by
    intro H hHc hHm
    obtain ⟨hpref, hmem, hphH⟩ := key_bwd H hHc hHm
    obtain ⟨hfibx, hphR⟩ := key_bwd2 H hHc hHm
    let j : PrefIdx n pol P := ⟨etaData (P : ShapePrefix) H, ⟨H, hpref, rfl⟩⟩
    show reprOf j = H
    exact hsep (reprOf j) H (key_fwd j hfibx hphR).1 hHc (reprOf_mem j) hpref
      ⟨j, etaData_reprOf j, rfl⟩
  -- Assemble the bijection LHS ≃ {chains of `Tr` matching `P̂`}.
  unfold VTree.chainCount
  refine Nat.card_congr ?_
  refine {
    toFun := fun a => ⟨reprOf a.1, key_fwd a.1 a.2.1 a.2.2⟩
    invFun := fun b => ⟨⟨etaData (P : ShapePrefix) b.1,
        ⟨b.1, (key_bwd b.1 b.2.1 b.2.2).1, rfl⟩⟩, key_bwd2 b.1 b.2.1 b.2.2⟩
    left_inv := fun a => Subtype.ext (Subtype.ext (etaData_reprOf a.1))
    right_inv := fun b => Subtype.ext (key_right b.1 b.2.1 b.2.2) }

end LeanUrat.MovesT
