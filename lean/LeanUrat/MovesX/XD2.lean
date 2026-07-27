/-
Unit XD.2 x2hypCount  [E-phase: stated, body sorry]
moves_ref: "Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read
history is carried by the +1" (unconditional; empty case both sides 0).
deps: Defs. difficulty: MEDIUM. hyp: HistWF.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Every element of a `ℕ`-list is at most its `foldr max 0`. -/
private theorem mem_le_foldr_max : ∀ (L : List ℕ) (x : ℕ), x ∈ L → x ≤ L.foldr max 0 := by
  intro L
  induction L with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    rw [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih x hx) (le_max_right _ _)

/-- Sum of a `ℕ`-list is at most `length · (foldr max 0)`. -/
private theorem sum_le_length_mul_foldr_max :
    ∀ (L : List ℕ), L.sum ≤ L.length * L.foldr max 0 := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.length_cons, List.foldr_cons]
    have ha : a ≤ max a (t.foldr max 0) := le_max_left _ _
    have hmM : t.foldr max 0 ≤ max a (t.foldr max 0) := le_max_right _ _
    have ht : t.sum ≤ t.length * max a (t.foldr max 0) :=
      ih.trans (Nat.mul_le_mul_left t.length hmM)
    calc a + t.sum ≤ max a (t.foldr max 0) + t.length * max a (t.foldr max 0) :=
          Nat.add_le_add ha ht
      _ = (t.length + 1) * max a (t.foldr max 0) := by ring

/-- From `termLast` (only the last node may be non-continuing) the length exceeds the
continuing-count by at most one. -/
private theorem length_le_dTotal_succ {n : ℕ} (H : XHistory n)
    (hterm : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true) :
    H.length ≤ dTotal H + 1 := by
  induction H with
  | nil => simp [dTotal]
  | cons a t ih =>
    -- termLast restricts to the tail
    have htTerm : ∀ j : Fin t.length, (j : ℕ) + 1 < t.length →
        (t.get j).continuing = true := by
      intro j hj
      have h := hterm j.succ (by simpa using hj)
      simpa [List.get_cons_succ] using h
    -- if the tail is nonempty, the head is continuing
    have haCont : t.length ≠ 0 → a.continuing = true := by
      intro hne
      have h := hterm ⟨0, Nat.succ_pos _⟩ (by simp; omega)
      simpa [List.get_cons_zero] using h
    have IH := ih htTerm
    by_cases hc : a.continuing = true
    · have hd : dTotal (a :: t) = dTotal t + 1 := by
        simp [dTotal, hc]
      simp only [List.length_cons]
      omega
    · have ht0 : t.length = 0 := by
        by_contra h0
        exact hc (haCont h0)
      simp only [List.length_cons, ht0]
      omega

theorem x2hypCount {n : ℕ} (H : XHistory n) (W : HistWF n H) :
    sumH H ≤ (dTotal H + 1) * maxH H := by
  have hA : sumH H ≤ H.length * maxH H := by
    have := sum_le_length_mul_foldr_max (H.map (fun ν => ν.h))
    simpa [sumH, maxH, List.length_map] using this
  have hB : H.length ≤ dTotal H + 1 := length_le_dTotal_succ H W.termLast
  calc sumH H ≤ H.length * maxH H := hA
    _ ≤ (dTotal H + 1) * maxH H := Nat.mul_le_mul_right (maxH H) hB

end LeanUrat.MovesX
