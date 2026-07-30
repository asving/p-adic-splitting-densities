/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-F0 `preHalt_prunedMem` — the box-free pre-halt IS the model-side pruning on
realized inputs (MOVES 7595–7598). THE PAYOFF: `PreHalt` is box-free, so Pref^τ is
shape/value-computable exactly as the note says. PROVED (E-phase prove-now set):
the ¬NsHalts leg exhibits the next node as a child through `mem_snoc` iterated along
the prefix chain (`mem_of_prefix` below). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- histories with equal node lists are equal (proof fields are propositional). -/
theorem history_ext {H H' : History p F} (h : H.nodes = H'.nodes) : H = H' := by
  cases H; cases H'
  simp only at h
  subst h
  rfl

/-- realized states are realized at every nonempty prefix (mem_snoc iterated). -/
theorem mem_of_prefix (T : TreeModel p F n N m pol) (x : Box p m) :
    ∀ (l : List (Node p F)) (H : History p F), H.nodes = l →
      T.mem (some H) x → ∀ H' : History p F, H'.IsPrefixOf H → T.mem (some H') x := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro H hHl _ H' _
    exact absurd hHl H.nonempty
  | append_singleton l' a ih =>
    intro H hHl hmem H' hpre
    rcases eq_or_ne H' H with rfl | hne
    · exact hmem
    -- H' is a PROPER prefix, so H'.nodes <+: l'
    have hpre' : H'.nodes <+: l' := by
      have h1 : H'.nodes <+: l' ++ [a] := hHl ▸ hpre
      rcases (List.prefix_concat_iff.mp h1) with h | h
      · exact absurd (history_ext (h.trans hHl.symm)) hne
      · exact h
    have hl'ne : l' ≠ [] := by
      intro h0
      have := List.prefix_nil.mp (h0 ▸ hpre')
      exact H'.nonempty this
    -- the length-l' prefix history
    have hroot' : ∀ (j : ℕ) (hj : j < l'.length),
        (l'[j]'hj).species = ReadSpecies.root ↔ j = 0 := by
      intro j hj
      have hj2 : j < H.nodes.length := by
        rw [hHl]; simp; omega
      have hval : H.nodes[j]'hj2 = l'[j]'hj := by
        simp only [hHl]
        exact List.getElem_append_left hj
      rw [← hval]
      exact H.root_iff j hj2
    set Hl : History p F := ⟨l', hl'ne, hroot'⟩ with hHldef
    -- a is a non-root node (its index in H is l'.length ≥ 1)
    have hspec : a.species ≠ ReadSpecies.root := by
      have hlen : l'.length < H.nodes.length := by rw [hHl]; simp
      have := H.root_iff l'.length hlen
      have hgt : H.nodes[l'.length]'hlen = a := by
        simp [hHl]
      rw [hgt] at this
      intro hcon
      exact hl'ne (List.length_eq_zero_iff.mp (this.mp hcon))
    -- H = Hl.snoc a
    have hHeq : H = Hl.snoc a hspec := by
      apply history_ext
      show H.nodes = Hl.nodes ++ [a]
      rw [hHl]
    have hmem' : T.mem (some Hl) x := ((T.mem_snoc Hl a hspec x).mp (hHeq ▸ hmem)).1
    exact ih Hl rfl hmem' H' hpre'

theorem preHalt_prunedMem (T : TreeModel p F n N m pol) (H : History p F)
    (hne : H.nodes ≠ []) (x : Box p m) (hmem : T.mem (some H) x) :
    PrunedMem T H x ↔ PreHalt H := by
  constructor
  · rintro ⟨_, hpr⟩ H' h1 h2 h3
    exact (hpr H' h1 h2 h3).1
  · intro hph
    refine ⟨hmem, fun H' hpre hneq hnn => ⟨hph H' hpre hneq hnn, ?_⟩⟩
    -- refute NsHalts at the proper prefix H': its next node in H is a child
    rintro ⟨hmem', hnochild⟩
    -- H'.nodes = H.nodes.take k, k := H'.nodes.length < H.nodes.length
    have htake : H'.nodes = H.nodes.take H'.nodes.length :=
      List.prefix_iff_eq_take.mp hpre
    have hklt : H'.nodes.length < H.nodes.length := by
      rcases Nat.lt_or_ge H'.nodes.length H.nodes.length with h | h
      · exact h
      · exfalso
        apply hneq
        apply history_ext
        have := List.IsPrefix.length_le hpre
        have hlen : H'.nodes.length = H.nodes.length := by omega
        rw [htake, hlen, List.take_length]
    set ν' : Node p F := H.nodes[H'.nodes.length]'hklt with hν'def
    -- ν' is non-root (index ≥ 1 since H' is nonempty)
    have hspec : ν'.species ≠ ReadSpecies.root := by
      have := H.root_iff H'.nodes.length hklt
      intro hcon
      exact hnn (List.length_eq_zero_iff.mp (this.mp hcon))
    -- the snoc extension is the (k+1)-prefix of H, hence realized at x
    have hpre2 : (H'.snoc ν' hspec).IsPrefixOf H := by
      show (H'.snoc ν' hspec).nodes <+: H.nodes
      have key : (H'.snoc ν' hspec).nodes = H.nodes.take (H'.nodes.length + 1) := by
        show H'.nodes ++ [ν'] = H.nodes.take (H'.nodes.length + 1)
        rw [List.take_succ, List.getElem?_eq_getElem hklt, ← htake]
        rfl
      rw [key]
      exact List.take_prefix _ _
    have hmemsnoc : T.mem (some (H'.snoc ν' hspec)) x :=
      mem_of_prefix T x H.nodes H rfl hmem _ hpre2
    have hchild := ((T.mem_snoc H' ν' hspec x).mp hmemsnoc).2
    exact hnochild ν' hchild

end LeanUrat.MovesT
