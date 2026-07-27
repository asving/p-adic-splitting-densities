/-
Unit U-2 `ktri` (easy) — (K-TRI): at m ≥ 2 every member size < e.
moves_ref: "at m ≥ 2 EVERY e_j < e".  sketch: μ.size + (m−1) ≤ Σ sizes ≤ e via
size_pos on the other members; omega.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- A list of members whose sizes are all ≥ 1 has total size at least its length. -/
private lemma length_le_sum_size {V : Type*} {State : ℕ → Type*}
    (l : List (Member V State)) (h : ∀ ν ∈ l, 1 ≤ ν.size) :
    l.length ≤ (l.map Member.size).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a.size := h a (List.mem_cons_self ..)
    have hl : l.length ≤ (l.map Member.size).sum :=
      ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem ktri {T : TableShape n} (hdc : DegCons T) {e : ℕ}
    (he : e ∈ Finset.Icc 1 n) {τ : T.State e} {o : T.Out e τ}
    (hm : 2 ≤ (T.odata e τ o).m) :
    ∀ μ ∈ (T.odata e τ o).mem, μ.size < e := by
  intro μ hμ
  have hpos : ∀ ν ∈ (T.odata e τ o).mem, 1 ≤ ν.size := hdc.size_pos e τ o
  have hsum : ((T.odata e τ o).mem.map Member.size).sum ≤ e := hdc.size_sum e he τ o
  -- length of the member list is m ≥ 2
  have hlen : 2 ≤ (T.odata e τ o).mem.length := hm
  -- split the list around μ
  obtain ⟨s, t, hst⟩ := List.append_of_mem hμ
  rw [hst] at hpos hsum hlen
  -- positivity on the two flanks
  have hs : s.length ≤ (s.map Member.size).sum :=
    length_le_sum_size s (fun ν hν => hpos ν (List.mem_append_left _ hν))
  have ht : t.length ≤ (t.map Member.size).sum :=
    length_le_sum_size t (fun ν hν =>
      hpos ν (List.mem_append_right _ (List.mem_cons_of_mem _ hν)))
  -- expand the sum over the split
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hsum
  simp only [List.length_append, List.length_cons] at hlen
  omega

end LeanUrat.MovesS
