/-
Unit Sp.compEncode — moves_ref: "the two flank compositions as indicator vectors
of their cut sets (≤ 2n entries, spans ≤ n by (B5))."
sketch: partial sums of a positive composition are strictly monotone; recover
parts as gaps of the sorted cut set; induction on lists. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- partial-sum cut set of a composition (blueprint: body = P-phase work).
`compCuts [c₁, …, cₖ]` is the set of partial sums `{c₁, c₁+c₂, …, c₁+⋯+cₖ}`
of the nonempty prefixes; equivalently the recursive shift
`insert a ((compCuts t).image (a + ·))`. -/
def compCuts : List ℕ → Finset ℕ
  | [] => ∅
  | a :: t => insert a ((compCuts t).image (a + ·))

/-- every cut of a positive composition is positive (all partial sums are ≥ the
first, positive, part). -/
theorem compCuts_pos {c : List ℕ} (hc : ∀ x ∈ c, 1 ≤ x) {y : ℕ}
    (hy : y ∈ compCuts c) : 1 ≤ y := by
  cases c with
  | nil => simp [compCuts] at hy
  | cons a t =>
    have ha : 1 ≤ a := hc a (by simp)
    simp only [compCuts, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨x, _, rfl⟩
    · exact ha
    · omega

theorem compCuts_inj {span} {c c' : List ℕ} (h : IsComposition c span)
    (h' : IsComposition c' span) (he : compCuts c = compCuts c') : c = c' := by
  induction c generalizing c' span with
  | nil =>
    have hspan : span = 0 := by simpa using h.2.symm
    cases c' with
    | nil => rfl
    | cons b r =>
      exfalso
      have hb : 1 ≤ b := h'.1 b (by simp)
      have hsum : b + r.sum = span := by simpa [List.sum_cons] using h'.2
      omega
  | cons a t ih =>
    cases c' with
    | nil =>
      exfalso
      have ha : 1 ≤ a := h.1 a (by simp)
      have hsum : a + t.sum = span := by simpa [List.sum_cons] using h.2
      have hspan0 : span = 0 := by simpa using h'.2.symm
      omega
    | cons b t' =>
      have ha : 1 ≤ a := h.1 a (by simp)
      have hb : 1 ≤ b := h'.1 b (by simp)
      have ht_pos : ∀ x ∈ t, 1 ≤ x := fun x hx => h.1 x (List.mem_cons_of_mem a hx)
      have ht'_pos : ∀ x ∈ t', 1 ≤ x := fun x hx => h'.1 x (List.mem_cons_of_mem b hx)
      simp only [compCuts] at he
      -- he : insert a ((compCuts t).image (a+·)) = insert b ((compCuts t').image (b+·))
      have hab : a = b := by
        have hA : a = b ∨ b < a := by
          have hmem : a ∈ insert b ((compCuts t').image (b + ·)) := by
            rw [← he]; exact Finset.mem_insert_self a _
          rcases Finset.mem_insert.mp hmem with h1 | h1
          · exact Or.inl h1
          · rw [Finset.mem_image] at h1
            obtain ⟨x, hx, hxa⟩ := h1
            have hxpos := compCuts_pos ht'_pos hx
            right; omega
        have hB : b = a ∨ a < b := by
          have hmem : b ∈ insert a ((compCuts t).image (a + ·)) := by
            rw [he]; exact Finset.mem_insert_self b _
          rcases Finset.mem_insert.mp hmem with h1 | h1
          · exact Or.inl h1
          · rw [Finset.mem_image] at h1
            obtain ⟨x, hx, hxb⟩ := h1
            have hxpos := compCuts_pos ht_pos hx
            right; omega
        omega
      subst b
      have hxa : a ∉ (compCuts t).image (a + ·) := by
        rw [Finset.mem_image]; rintro ⟨x, hx, hxeq⟩
        have hxpos := compCuts_pos ht_pos hx; omega
      have hya : a ∉ (compCuts t').image (a + ·) := by
        rw [Finset.mem_image]; rintro ⟨x, hx, hxeq⟩
        have hxpos := compCuts_pos ht'_pos hx; omega
      have himg : (compCuts t).image (a + ·) = (compCuts t').image (a + ·) := by
        rw [← Finset.erase_insert hxa, ← Finset.erase_insert hya, he]
      have hct : compCuts t = compCuts t' :=
        Finset.image_injective (add_right_injective a) himg
      have hst : t.sum = t'.sum := by
        have e1 : a + t.sum = span := by simpa [List.sum_cons] using h.2
        have e2 : a + t'.sum = span := by simpa [List.sum_cons] using h'.2
        omega
      have htt : t = t' := ih ⟨ht_pos, rfl⟩ ⟨ht'_pos, hst.symm⟩ hct
      rw [htt]

end LeanUrat.MovesSp
