/-
Unit Sp.lamEnumComplete — moves_ref: "(residual shape) the degree–multiplicity
partition λ … with Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ" + (B5)'s part caps.
sketch: enumeration by strong recursion on weight over a canonical (sorted)
representative; completeness by induction on the multiset. THE fiddly enum unit —
recommend List-of-sorted-lists internally, Multiset at the boundary.
difficulty: medium-hard.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- The canonical index of a pair `(g, μ)` in the `bound × bound` grid used by
`lamEnumAux`: pairs `(g, μ)` with `1 ≤ g, μ ≤ bound` correspond bijectively to
`k = (g-1)·bound + (μ-1) ∈ [0, bound²)`, and the enumeration emits them in
nondecreasing `idxPair` order (canonical sorted representative). -/
private def idxPair (bound : ℕ) (gm : ℕ × ℕ) : ℕ := (gm.1 - 1) * bound + (gm.2 - 1)

/-- Soundness of the list enumeration: every list produced by `lamEnumAux bound w lo`
has weight `Σ g·μ = w`. Strong induction on the fuel `w` (each recursive call
strictly decreases it, since `g·μ ≥ 1`). -/
private theorem lamEnumAux_map_sum (bound : ℕ) :
    ∀ (w lo : ℕ) (l : List (ℕ × ℕ)), l ∈ lamEnumAux bound w lo →
      (l.map fun gm => gm.1 * gm.2).sum = w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases w with _ | w'
    · intro lo l hl
      simp only [lamEnumAux, List.mem_singleton] at hl
      subst hl; simp
    · intro lo l hl
      simp only [lamEnumAux, List.mem_flatMap] at hl
      obtain ⟨k, hk, hl2⟩ := hl
      by_cases hc : (k / bound + 1) * (k % bound + 1) ≤ w' + 1
      · rw [if_pos hc, List.mem_map] at hl2
        obtain ⟨l', hl', rfl⟩ := hl2
        have := ih (w' + 1 - (k / bound + 1) * (k % bound + 1)) (by
          have : 0 < (k / bound + 1) * (k % bound + 1) :=
            Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
          omega) k l' hl'
        simp only [List.map_cons, List.sum_cons, this]
        omega
      · rw [if_neg hc] at hl2
        simp at hl2

/-- Completeness of the list enumeration: any list of in-range pairs that is sorted
nondecreasingly by `idxPair`, whose head index is `≥ lo`, and whose weight is `w`, is
produced by `lamEnumAux bound w lo`. Strong induction on `w`; the head becomes the
chosen grid index `k`, and the tail is handled by the induction hypothesis. -/
private theorem mem_lamEnumAux_of_pairwise (bound : ℕ) :
    ∀ (w : ℕ) (l : List (ℕ × ℕ)) (lo : ℕ),
      (∀ gm ∈ l, 1 ≤ gm.1 ∧ gm.1 ≤ bound ∧ 1 ≤ gm.2 ∧ gm.2 ≤ bound) →
      List.Pairwise (fun a b => idxPair bound a ≤ idxPair bound b) l →
      (∀ gm ∈ l.head?, lo ≤ idxPair bound gm) →
      (l.map fun gm => gm.1 * gm.2).sum = w →
      l ∈ lamEnumAux bound w lo := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro l lo hrange hpair hhead hsum
    match l with
    | [] =>
        simp only [List.map_nil, List.sum_nil] at hsum
        obtain rfl : w = 0 := hsum.symm
        simp [lamEnumAux]
    | gm₀ :: t =>
        obtain ⟨hg1, hgb, hm1, hmb⟩ := hrange gm₀ (by simp)
        have hbpos : 0 < bound := lt_of_lt_of_le hg1 hgb
        have hval1 : 1 ≤ gm₀.1 * gm₀.2 := Nat.mul_pos hg1 hm1
        simp only [List.map_cons, List.sum_cons] at hsum
        obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        have hlo : lo ≤ idxPair bound gm₀ := hhead gm₀ (by simp)
        have hlt2 : gm₀.2 - 1 < bound := by omega
        have hkdiv : idxPair bound gm₀ / bound = gm₀.1 - 1 := by
          unfold idxPair
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hlt2, Nat.zero_add]
        have hkmod : idxPair bound gm₀ % bound = gm₀.2 - 1 := by
          unfold idxPair
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
        simp only [lamEnumAux, List.mem_flatMap]
        refine ⟨idxPair bound gm₀, ?_, ?_⟩
        · rw [List.range_eq_range', List.drop_range', List.mem_range'_1]
          have key : ∀ b x y : ℕ, x < b → y < b → x * b + y < b * b := by
            intro b x y hx hy
            calc x * b + y < x * b + b := by omega
              _ = (x + 1) * b := by ring
              _ ≤ b * b := Nat.mul_le_mul_right _ (by omega)
          have hub : idxPair bound gm₀ < bound * bound := by
            unfold idxPair; exact key bound _ _ (by omega) (by omega)
          omega
        · simp only [hkdiv, hkmod, Nat.sub_add_cancel hg1, Nat.sub_add_cancel hm1]
          rw [if_pos (by omega), List.mem_map]
          refine ⟨t, ?_, rfl⟩
          apply ih (w' + 1 - gm₀.1 * gm₀.2) (by omega) t (idxPair bound gm₀)
          · exact fun gm h => hrange gm (List.mem_cons_of_mem _ h)
          · exact (List.pairwise_cons.mp hpair).2
          · intro gm hgm
            exact (List.pairwise_cons.mp hpair).1 gm (List.mem_of_mem_head? hgm)
          · omega

/-- Membership in the multiset-level enumeration unfolds to a sorted-list witness. -/
private theorem mem_lamEnum_iff {bound weight : ℕ} {lam : Multiset (ℕ × ℕ)} :
    lam ∈ lamEnum bound weight ↔
      ∃ l ∈ lamEnumAux bound weight 0, (↑l : Multiset (ℕ × ℕ)) = lam := by
  simp [lamEnum, eq_comm]

theorem lamEnum_complete {bound weight : ℕ} {lam : Multiset (ℕ × ℕ)}
    (hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2)
    (hbd : ∀ gm ∈ lam, gm.1 ≤ bound ∧ gm.2 ≤ bound) :
    ((lam.map fun gm => gm.1 * gm.2).sum = weight ↔ lam ∈ lamEnum bound weight) := by
  constructor
  · -- completeness: sort a list representative of `lam` by `idxPair`, feed to the list lemma
    intro hsum
    haveI : Std.Total (fun a b : ℕ × ℕ => idxPair bound a ≤ idxPair bound b) :=
      ⟨fun a b => Nat.le_total _ _⟩
    haveI : IsTrans (ℕ × ℕ) (fun a b : ℕ × ℕ => idxPair bound a ≤ idxPair bound b) :=
      ⟨fun a b c => Nat.le_trans⟩
    obtain ⟨l, hperm, hpw⟩ :
        ∃ l : List (ℕ × ℕ), l.Perm lam.toList ∧
          List.Pairwise (fun a b => idxPair bound a ≤ idxPair bound b) l :=
      ⟨_, List.perm_insertionSort _ _, List.pairwise_insertionSort _ _⟩
    have hcoe : (↑l : Multiset (ℕ × ℕ)) = lam :=
      (Multiset.coe_eq_coe.mpr hperm).trans (Multiset.coe_toList lam)
    rw [mem_lamEnum_iff]
    refine ⟨l, ?_, hcoe⟩
    apply mem_lamEnumAux_of_pairwise bound weight l 0
    · intro gm hgm
      have hgm' : gm ∈ lam := by rw [← hcoe]; exact Multiset.mem_coe.mpr hgm
      exact ⟨(hpos gm hgm').1, (hbd gm hgm').1, (hpos gm hgm').2, (hbd gm hgm').2⟩
    · exact hpw
    · intro gm _; exact Nat.zero_le _
    · rw [← hsum, ← hcoe, Multiset.map_coe, Multiset.sum_coe]
  · -- soundness: any enumerated multiset is a coerced list of the right weight
    intro hmem
    rw [mem_lamEnum_iff] at hmem
    obtain ⟨l, hl, rfl⟩ := hmem
    rw [Multiset.map_coe, Multiset.sum_coe]
    exact lamEnumAux_map_sum bound weight 0 l hl

end LeanUrat.MovesSp
