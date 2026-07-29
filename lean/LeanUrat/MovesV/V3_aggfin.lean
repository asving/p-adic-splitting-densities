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
  sorry

end LeanUrat.MovesV
