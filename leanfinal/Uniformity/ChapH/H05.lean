/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H05 — genre SCHEMA finiteness

**Chapter H, NODE H.05** (`blueprint/CHAP-H_general_induction.md` §3). `GENHN.CLASS`(ii) in its
**corrected** scope: at fixed degree `n` there are finitely many genre *schemas* — triples
`(e₁, f₁, μ)` with `e₁ f₁ ≥ 2`, `μ ≥ 2`, `e₁ μ f₁ ≤ n` — and at most `n ^ 3` of them.

The statement is over raw triples, not over `GenreDatum` (H.01): that is exactly what makes it a
*schema* set. The residue cardinality `Q` and the slope numerator `h` are the schemas'
**parameters**, and the datum set they generate is genuinely INFINITE — the A2 refutation, landed
separately as H.06. Both halves are needed to tell the corrected clause from the refuted one.

DEPENDS: none.

SOURCE: `EFF.GENHN.07` clause (ii) as re-displayed by the owner directive: *"at fixed `n`, the
genres form FINITELY MANY PARAMETERIZED GENRE SCHEMAS — the triples `(e₁, f₁, μ)` with
`e₁f₁ ≥ 2`, `e₁f₁μ ≤ n` … with the residue field `Q`, the slope numerator `h` (`gcd(h, e₁) = 1`),
the window `N`, and the prehistory depths as the schemas' parameters"*; the sealed clause's own
bound `#{(a, b, μ) : ab ≥ 2, μ ≥ 2, abμ ≤ n} < ∞`.

**⚠ THE ENTRY-PATTERN CLAUSE IS NOT PROVED HERE** (blueprint). The re-display's second half —
*"each carrying finitely many `(A1)`-admissible entry-pattern families"* — is `W12` content
(honesty item H-12) and is out of chapter H's scope. This node is exactly the triple count, which
is what the consumer (H.69's genre count) needs.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The schema set at degree `n`: the triples `(e₁, f₁, μ)` a degree-`n` read can realize. -/
def schemaSet (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {p | 2 ≤ p.1 * p.2.1 ∧ 2 ≤ p.2.2 ∧ p.1 * p.2.2 * p.2.1 ≤ n}

/-- Auxiliary: the coordinate box `[1, n]³` that contains the schema set. -/
private def schemaBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n

/-- Auxiliary: every schema triple has all three coordinates in `[1, n]`. Each of `e₁, f₁` is
nonzero because `2 ≤ e₁ f₁`, and `μ ≥ 2`; the product bound `e₁ μ f₁ ≤ n` then bounds each
coordinate separately. -/
private theorem schemaSet_subset_box (n : ℕ) : schemaSet n ⊆ (schemaBox n : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨e, f, m⟩ hp
  obtain ⟨hef, hm, hn⟩ : 2 ≤ e * f ∧ 2 ≤ m ∧ e * m * f ≤ n := hp
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero fun h => by simp [h] at hef
  have hf1 : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at hef
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  have hef1 : 1 ≤ e * f := Nat.le_of_succ_le hef
  have hem1 : 1 ≤ e * m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hE : e ≤ e * m * f :=
    le_trans (Nat.le_mul_of_pos_right e hm1) (Nat.le_mul_of_pos_right (e * m) hf1)
  have hF : f ≤ e * m * f := by
    have hcomm : e * m * f = f * (e * m) := by ring
    rw [hcomm]; exact Nat.le_mul_of_pos_right f hem1
  have hM : m ≤ e * m * f := by
    have hcomm : e * m * f = m * (e * f) := by ring
    rw [hcomm]; exact Nat.le_mul_of_pos_right m hef1
  refine Finset.mem_coe.mpr ?_
  simp only [schemaBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨he1, le_trans hE hn⟩, ⟨hf1, le_trans hF hn⟩, ⟨hm1, le_trans hM hn⟩⟩

/-- Auxiliary: the box has exactly `n ^ 3` elements. -/
private theorem card_schemaBox (n : ℕ) : (schemaBox n).card = n ^ 3 := by
  simp only [schemaBox, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-- **Genre schema finiteness** (`GENHN.CLASS`(ii), corrected): at fixed degree `n` only finitely
many schemas `(e₁, f₁, μ)` occur. -/
theorem finite_schemaSet (n : ℕ) : (schemaSet n).Finite :=
  Set.Finite.subset (schemaBox n).finite_toSet (schemaSet_subset_box n)

/-- The quantitative form: at most `n ^ 3` schemas at degree `n`. Each coordinate lies in `[1, n]`
(no coordinate can vanish, since `2 ≤ e₁ f₁` and `2 ≤ μ`), so the box is `[1, n]³`. -/
theorem card_schemaSet_le (n : ℕ) : Nat.card (schemaSet n) ≤ n ^ 3 := by
  rw [Nat.card_coe_set_eq]
  calc (schemaSet n).ncard
      ≤ ((schemaBox n : Finset (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ)).ncard :=
        Set.ncard_le_ncard (schemaSet_subset_box n) (schemaBox n).finite_toSet
    _ = (schemaBox n).card := Set.ncard_coe_finset _
    _ = n ^ 3 := card_schemaBox n

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.schemaSet
#print axioms Uniformity.Density.Induction.finite_schemaSet
#print axioms Uniformity.Density.Induction.card_schemaSet_le

end AxCheck
