/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# MovesU/O5CountingB — U-D: O5triple Theorem B's abstract counting core

Lean unit U-D of SYNTH4 (`lean/notes/SYNTHESIS_PASS4_2026-08-01.md` §4), dispatched
2026-08-01 (LEANW6): the UNCONDITIONAL arithmetic mechanism of O5triple Theorem B
(`lean/notes/openmath/O5triple_phaseB_verifybrief_rev2.md` §6, V18/V23: no criticals) —

> an injection whose image's weighted total equals the whole total, with every weight
> ≥ 1, is onto —

stated as a general `Finset` lemma with NO GMN content.  In the O5triple reading:
`s` = the engine leaf slots of the decided tree `T`, `t` = the semantic leaves of
`𝒯(g)`, `φ = β_g` the leaf transport, `w L = e_L · f_L` (≥ 1), the two checksums
`Σ_slots e·f = n = Σ_leaves e·f` ((I-3) engine typing; Theorem A(4) semantic
checksum), injectivity = (I-2) dictionary faithfulness.  `surj_of_injOn_checksum`
is the counting step verbatim; `bijOn_of_injOn_checksum` packages Theorem B's
conclusion (β_g a bijection leafslots(T) → leaves(𝒯(g))); the `card_eq` corollary
is the |slots| = |leaves| consequence the D-7 assembly quotes.

This gives the D-7b mechanism ("coverage consumes NO no-missing clause" — the
V18-confirmed dependency sharpening) a permanent Lean core.  CONSUMERS STAY PARKED:
the instantiation at the engine/semantic carriers waits on the (I-1)–(I-3) interface
(the K-RUN-C composition of `lean/notes/openmath/O3adj_adjudication.md` §3.1 CU-7).
No existing statement is touched; Lean-core axioms only.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

/-- **U-D, the counting step (O5triple Theorem B's surjectivity argument).**
If `φ` maps `s` into `t` injectively, every weight on `t` is ≥ 1, and the
pulled-back weight total over `s` equals the weight total over `t` (the two
checksums), then every element of `t` is hit: the complement of the image has
weighted total 0, and all its terms are ≥ 1, so it is empty. -/
theorem surj_of_injOn_checksum {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (φ : α → β)
    (hmaps : ∀ a ∈ s, φ a ∈ t) (hinj : ∀ a ∈ s, ∀ a' ∈ s, φ a = φ a' → a = a')
    (w : β → ℕ) (hpos : ∀ b ∈ t, 1 ≤ w b)
    (hsum : ∑ a ∈ s, w (φ a) = ∑ b ∈ t, w b) :
    ∀ b ∈ t, ∃ a ∈ s, φ a = b := by
  classical
  -- the image and its complement in t
  have himg : s.image φ ⊆ t := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps a ha
  -- the pulled-back total is the image total (injectivity)
  have hpull : ∑ a ∈ s, w (φ a) = ∑ b ∈ s.image φ, w b :=
    (Finset.sum_image (fun a ha a' ha' h => hinj a ha a' ha' h)).symm
  -- split t's total over image ⊔ complement
  have hsplit : ∑ b ∈ t \ s.image φ, w b + ∑ b ∈ s.image φ, w b = ∑ b ∈ t, w b :=
    Finset.sum_sdiff himg
  -- all complement terms ≥ 1 ⟹ complement empty
  intro b hb
  by_contra hcon
  push Not at hcon
  have hbc : b ∈ t \ s.image φ := by
    refine Finset.mem_sdiff.mpr ⟨hb, ?_⟩
    intro hbi
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hbi
    exact hcon a ha hab
  have h1 : 1 ≤ ∑ b' ∈ t \ s.image φ, w b' :=
    le_trans (hpos b hb) (Finset.single_le_sum (fun b' hb' =>
      Nat.zero_le _) hbc)
  omega

/-- **U-D packaged (Theorem B's conclusion shape):** injectivity + the two
checksums make the transport a bijection of `s` onto `t` (`Set.BijOn`). -/
theorem bijOn_of_injOn_checksum {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (φ : α → β)
    (hmaps : ∀ a ∈ s, φ a ∈ t) (hinj : ∀ a ∈ s, ∀ a' ∈ s, φ a = φ a' → a = a')
    (w : β → ℕ) (hpos : ∀ b ∈ t, 1 ≤ w b)
    (hsum : ∑ a ∈ s, w (φ a) = ∑ b ∈ t, w b) :
    Set.BijOn φ ↑s ↑t := by
  refine ⟨fun a ha => hmaps a ha, fun a ha a' ha' h => hinj a ha a' ha' h, ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surj_of_injOn_checksum s t φ hmaps hinj w hpos hsum b hb
  exact ⟨a, ha, rfl⟩

/-- The cardinality tie the D-7 assembly quotes: |slots| = |leaves|. -/
theorem card_eq_of_injOn_checksum {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (φ : α → β)
    (hmaps : ∀ a ∈ s, φ a ∈ t) (hinj : ∀ a ∈ s, ∀ a' ∈ s, φ a = φ a' → a = a')
    (w : β → ℕ) (hpos : ∀ b ∈ t, 1 ≤ w b)
    (hsum : ∑ a ∈ s, w (φ a) = ∑ b ∈ t, w b) :
    s.card = t.card := by
  classical
  have hb := bijOn_of_injOn_checksum s t φ hmaps hinj w hpos hsum
  have himg : s.image φ = t := by
    apply Finset.Subset.antisymm
    · intro b hbm
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hbm
      exact hmaps a ha
    · intro b hbm
      obtain ⟨a, ha, rfl⟩ := surj_of_injOn_checksum s t φ hmaps hinj w hpos hsum b hbm
      exact Finset.mem_image_of_mem φ ha
  rw [← himg]
  exact (Finset.card_image_of_injOn (fun a ha a' ha' h => hinj a ha a' ha' h)).symm

end LeanUrat.MovesU

#print axioms LeanUrat.MovesU.surj_of_injOn_checksum
#print axioms LeanUrat.MovesU.bijOn_of_injOn_checksum
#print axioms LeanUrat.MovesU.card_eq_of_injOn_checksum
