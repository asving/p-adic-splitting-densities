/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapG.G53 — `typeOf_three_cases`

**Chapter G, NODE G.53** (`blueprint/CHAP-G_base_cases_menus.md` §8). **The `n = 3` analogue of
`typeOf_two_cases`.** Every monic cubic over a DVR has one of the five types. **The proof is
purely combinatorial**: `typeOf_degree` forces `Σ eᵢfᵢ = 3` and `efPair_pos_of_mem` forces every
`eᵢ, fᵢ ≥ 1`, so the multiset of products is a partition of `3` into positive parts (`{3}`,
`{2,1}`, `{1,1,1}`), and `e·f = 3` with `3` prime gives `(e,f) ∈ {(1,3),(3,1)}`, `e·f = 2` gives
`(1,2)` or `(2,1)`, `e·f = 1` gives `(1,1)`.

DEPENDS: G.52 · landed `typeOf_degree` (`TypeOf.lean:372`), `efPair_pos_of_mem`
(`TypePositivity.lean:55`), `efPair_mul_le_natDegree` (`TypePositivity.lean:69`),
`monicPoly_monic`, `monicPoly_natDegree`, `FactorizationType.ext`.

**⚠ THIS NODE IS NEW.** `leancheck`'s `N3Drain.lean` docstring names its absence explicitly: the
converse of `drainage_three_of_triple` "would need the `n = 3` analogue of `typeOf_two_cases`".
Chapter G supplies it, and it is the input to G.54.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

/-! ## A private arithmetic lemma bank: positive-integer partitions of `3` -/

private theorem g53_pair_one_one {m n : ℕ} (h : m * n = 1) (hm : 0 < m) (hn : 0 < n) :
    m = 1 ∧ n = 1 := by
  have hb : m ≤ 1 := by nlinarith
  interval_cases m
  omega

private theorem g53_pair_two {m n : ℕ} (h : m * n = 2) (hm : 0 < m) (hn : 0 < n) :
    (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) := by
  have hb : m ≤ 2 := by nlinarith
  interval_cases m <;> omega

private theorem g53_pair_three {m n : ℕ} (h : m * n = 3) (hm : 0 < m) (hn : 0 < n) :
    (m = 1 ∧ n = 3) ∨ (m = 3 ∧ n = 1) := by
  have hb : m ≤ 3 := by nlinarith
  interval_cases m <;> omega

private theorem g53_sum_two {X Y : ℕ} (h : X + Y = 3) (hX : 0 < X) (hY : 0 < Y) :
    (X = 1 ∧ Y = 2) ∨ (X = 2 ∧ Y = 1) := by omega

private theorem g53_sum_three {X Y Z : ℕ} (h : X + Y + Z = 3) (hX : 0 < X) (hY : 0 < Y)
    (hZ : 0 < Z) : X = 1 ∧ Y = 1 ∧ Z = 1 := by omega

/-- **The abstract combinatorial content of G.53**: a multiset of positive-product pairs summing
to `3` is one of the five degree-`3` type multisets. Stated and proved independently of `typeOf`
so the case analysis is pure `Multiset`/`ℕ` arithmetic. -/
private theorem g53_multiset_cases {M : Multiset (ℕ × ℕ)}
    (hpos : ∀ p ∈ M, 0 < p.1 ∧ 0 < p.2)
    (hsum : (M.map (fun p : ℕ × ℕ => p.1 * p.2)).sum = 3) :
    M = c3split.data ∨ M = c3linInert.data ∨ M = c3inert.data ∨ M = c3linRam.data
      ∨ M = c3ram.data := by
  have hcard : Multiset.card M ≤ 3 := by
    have h1 : ∀ x ∈ M.map (fun p : ℕ × ℕ => p.1 * p.2), 1 ≤ x := by
      rintro x hx
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨h1, h2⟩ := hpos p hp
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have h2 := Multiset.card_nsmul_le_sum h1
    rw [Multiset.card_map, smul_eq_mul, mul_one, hsum] at h2
    exact h2
  have hc4 : Multiset.card M = 0 ∨ Multiset.card M = 1 ∨ Multiset.card M = 2
      ∨ Multiset.card M = 3 := by omega
  rcases hc4 with hc | hc | hc | hc
  · exfalso
    rw [Multiset.card_eq_zero.1 hc] at hsum
    simp at hsum
  · -- card 1
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 hc
    obtain ⟨p1, p2⟩ := p
    have hmem : (p1, p2) ∈ M := by rw [hp]; simp
    obtain ⟨hp1, hp2⟩ := hpos (p1, p2) hmem
    rw [hp] at hsum
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at hsum
    rcases g53_pair_three hsum hp1 hp2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (by rw [hp]; decide)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [hp]; decide))))
  · -- card 2
    obtain ⟨q1, q2, hp⟩ := Multiset.card_eq_two.1 hc
    obtain ⟨a1, a2⟩ := q1
    obtain ⟨b1, b2⟩ := q2
    have hmem1 : (a1, a2) ∈ M := by rw [hp]; simp
    have hmem2 : (b1, b2) ∈ M := by rw [hp]; simp
    obtain ⟨ha1, ha2⟩ := hpos (a1, a2) hmem1
    obtain ⟨hb1, hb2⟩ := hpos (b1, b2) hmem2
    rw [hp] at hsum
    simp [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton] at hsum
    have hXpos : 0 < a1 * a2 := Nat.mul_pos ha1 ha2
    have hYpos : 0 < b1 * b2 := Nat.mul_pos hb1 hb2
    rcases g53_sum_two hsum hXpos hYpos with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · obtain ⟨rfl, rfl⟩ := g53_pair_one_one e1 ha1 ha2
      rcases g53_pair_two e2 hb1 hb2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl (by rw [hp]; decide))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hp]; decide))))
    · rcases g53_pair_two e1 ha1 ha2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        obtain ⟨rfl, rfl⟩ := g53_pair_one_one e2 hb1 hb2
      · exact Or.inr (Or.inl (by rw [hp]; decide))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hp]; decide))))
  · -- card 3
    obtain ⟨q1, q2, q3, hp⟩ := Multiset.card_eq_three.1 hc
    obtain ⟨a1, a2⟩ := q1
    obtain ⟨b1, b2⟩ := q2
    obtain ⟨c1, c2⟩ := q3
    have hmem1 : (a1, a2) ∈ M := by rw [hp]; simp
    have hmem2 : (b1, b2) ∈ M := by rw [hp]; simp
    have hmem3 : (c1, c2) ∈ M := by rw [hp]; simp
    obtain ⟨ha1, ha2⟩ := hpos (a1, a2) hmem1
    obtain ⟨hb1, hb2⟩ := hpos (b1, b2) hmem2
    obtain ⟨hc1, hc2⟩ := hpos (c1, c2) hmem3
    rw [hp] at hsum
    simp [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton] at hsum
    have hsum' : a1 * a2 + b1 * b2 + c1 * c2 = 3 := by linarith
    obtain ⟨eA, eB, eC⟩ := g53_sum_three hsum' (Nat.mul_pos ha1 ha2) (Nat.mul_pos hb1 hb2)
      (Nat.mul_pos hc1 hc2)
    obtain ⟨rfl, rfl⟩ := g53_pair_one_one eA ha1 ha2
    obtain ⟨rfl, rfl⟩ := g53_pair_one_one eB hb1 hb2
    obtain ⟨rfl, rfl⟩ := g53_pair_one_one eC hc1 hc2
    exact Or.inl (by rw [hp]; decide)

/-- **Exactly five splitting types occur in degree 3.** No Newton polygon, no Hensel: the
statement is a consequence of `typeOf_degree` and the positivity of every `(e,f)` pair. -/
theorem typeOf_three_cases {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (a : Fin 3 → O) :
    typeOf (monicPoly a) = c3split ∨ typeOf (monicPoly a) = c3linInert
      ∨ typeOf (monicPoly a) = c3inert ∨ typeOf (monicPoly a) = c3linRam
      ∨ typeOf (monicPoly a) = c3ram := by
  have hmon : (monicPoly a).Monic := monicPoly_monic a
  have hdeg : (monicPoly a).natDegree = 3 := monicPoly_natDegree a
  have hsum : ((typeOf (monicPoly a)).data.map (fun p : ℕ × ℕ => p.1 * p.2)).sum = 3 := by
    have h := typeOf_degree hmon
    rw [hdeg] at h
    simpa [FactorizationType.degree] using h
  have hpos : ∀ p ∈ (typeOf (monicPoly a)).data, 0 < p.1 ∧ 0 < p.2 :=
    fun p hp => efPair_pos_of_mem hmon hp
  rcases g53_multiset_cases hpos hsum with h | h | h | h | h
  · exact Or.inl (FactorizationType.ext h)
  · exact Or.inr (Or.inl (FactorizationType.ext h))
  · exact Or.inr (Or.inr (Or.inl (FactorizationType.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (FactorizationType.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (FactorizationType.ext h))))

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_three_cases

end AxCheck
