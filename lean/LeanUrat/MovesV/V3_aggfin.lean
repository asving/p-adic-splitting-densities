/-  MovesV unit V3-7 `ent_agg_finite` — ENT-AGG's hypothesis-free half:
    μ̂-additivity over disjoint mark families.  `CutsDisj`/`unionCut`
    (NAME→HOME: V3-7) DISPLAYED. -/
import LeanUrat.MovesV.V3_iota

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- pairwise-disjoint cut families. -/
def CutsDisj {n : ℕ} {ε : EntShapeV n} {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cs : List (EntranceCut n ε p F pol)) : Prop :=
  cs.Pairwise (fun c c' => ∀ i, ¬(c.lands i ∧ c'.lands i))

open Classical in
/-- the union cut (selection law inherited memberwise). -/
noncomputable def unionCut {n : ℕ} {ε : EntShapeV n} {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cs : List (EntranceCut n ε p F pol)) : EntranceCut n ε p F pol where
  lands i := ∃ c ∈ cs, c.lands i
  decL := Classical.decPred _
  lands_sel i hi := by
    obtain ⟨c, _, hc⟩ := hi
    exact c.lands_sel i hc

theorem ent_agg_finite {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cs : List (EntranceCut n ε p F pol)) (hd : CutsDisj cs) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) :
    iotaCount ε (unionCut cs) S = (cs.map (fun c => iotaCount ε c S)).sum := by
  induction cs with
  | nil =>
    change (∑ᶠ i ∈ {i | (unionCut ([] : List (EntranceCut n ε p F pol))).lands i},
        Nat.card ↥(S.fiber i)) = 0
    have hset : {i | (unionCut ([] : List (EntranceCut n ε p F pol))).lands i}
        = (∅ : Set (MovesD.PrefIdx n pol ε.Phat)) := by
      ext i; simp [unionCut]
    rw [hset, finsum_mem_empty]
  | cons c cs' ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
    have hset : {i | (unionCut (c :: cs')).lands i}
        = {i | c.lands i} ∪ {i | (unionCut cs').lands i} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨c'', hc'', hlands⟩
        rcases List.mem_cons.mp hc'' with rfl | hmem
        · exact Or.inl hlands
        · exact Or.inr ⟨c'', hmem, hlands⟩
      · rintro (h | ⟨c'', hc'', hlands⟩)
        · exact ⟨c, List.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨c'', List.mem_cons.mpr (Or.inr hc''), hlands⟩
    have hdisj : Disjoint {i | c.lands i} {i | (unionCut cs').lands i} := by
      rw [Set.disjoint_left]
      rintro i hci ⟨c'', hc'', hlands⟩
      exact hhead c'' hc'' i ⟨hci, hlands⟩
    change (∑ᶠ i ∈ {i | (unionCut (c :: cs')).lands i}, Nat.card ↥(S.fiber i))
        = ((c :: cs').map (fun c => iotaCount ε c S)).sum
    rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _),
      List.map_cons, List.sum_cons]
    congr 1
    exact ih htail

end LeanUrat.MovesV
