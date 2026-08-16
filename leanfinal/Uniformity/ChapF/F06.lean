/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F01
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Uniformity.ChapF.F06 — the `F₂` degeneracy disclosure, made structural (`JD0-BOX-5`)

**Chapter F, NODE F.06** [lemma] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1 +
`[Fintype K]`. If `K` has exactly two elements then `Kˣ` is a subsingleton and every carry
gauge acts trivially — J-D0's clause (i) is VACUOUS at `F₂` levels, exactly the note's own
disclosure (`EFF.JD0.22` BOX-5: "Over K_j = F₂ the unit group is trivial: clause (i) is
vacuous at such levels"; the battery census: 252 residual-gauge levels nontrivial, 57
trivial). A vacuity DISCLOSURE promoted to a theorem — the strongest honest form (GC-8's
signed-vacuity sub-case, with a proof). It is why the gates run unit-character checks at
`q = 2` on `F₄`, never on `F₂` alone (GC-11 coincidence-regime discipline).

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16).
-/

namespace Uniformity.Density.Weld

theorem slotScale_eq_id_of_card_two {Γ K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) (u : Γ → Kˣ) : slotScale u = id := by
  classical
  have h1 : Fintype.card Kˣ = 1 := by rw [Fintype.card_units, hK]
  have hsub : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp h1.le
  funext v γ
  have hu : u γ = 1 := Subsingleton.elim _ _
  simp [slotScale, hu]

end Uniformity.Density.Weld
