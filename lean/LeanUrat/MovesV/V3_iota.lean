/-  MovesV unit V3-6 `iota_muhat` (RESTATED C13) — ι's typing laws, the FALSE
    IFF STRUCK: sub-sum bound, one-direction totality, the D4R.1-SUM tie
    (via the EXPORTED MovesD.D4R1_SUM — G-4). -/
import LeanUrat.MovesV.Defs
import LeanUrat.MovesD.D10_sumLaw

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem iota_le_total {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) :
    iotaCount ε cut S ≤ ∑ᶠ i : MovesD.PrefIdx n pol ε.Phat,
      Nat.card ↥(S.fiber i) := by
  classical
  haveI : Fintype (MovesD.PrefIdx n pol ε.Phat) := Fintype.ofFinite _
  simp only [iotaCount]
  have hset : {i | cut.lands i}
      = (↑(Finset.univ.filter (fun i => cut.lands i)) : Set _) := by
    ext i; simp
  rw [hset, finsum_mem_coe_finset, finsum_eq_sum_of_fintype]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem iota_eq_of_total {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cut : EntranceCut n ε p F pol) (htot : ∀ i, cut.lands i) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) :
    iotaCount ε cut S = ∑ᶠ i : MovesD.PrefIdx n pol ε.Phat,
      Nat.card ↥(S.fiber i) := by
  classical
  simp only [iotaCount]
  have hset : {i | cut.lands i} = (Set.univ : Set _) := by
    ext i; simp [htot i]
  rw [hset, finsum_mem_univ]

/-- (c) the D4R.1-SUM tie at stabilized levels (the exported MovesD law at
the refined index — the fact discharging `CtsMeasured.ent_card`). -/
theorem iota_d10_tie {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (hA : (ε.Phat : MovesD.ShapePrefix).A n N = (ε.Phat : MovesD.ShapePrefix).A' n)
    (S : MovesD.Presented p F n N m pol ε.Phat) :
    (∑ᶠ i : MovesD.PrefIdx n pol ε.Phat, Nat.card ↥(S.fiber i))
        * p ^ ((ε.Phat : MovesD.ShapePrefix).A' n)
      = Nat.card (MovesD.PrefIdx n pol ε.Phat) * p ^ (n * N) :=
  MovesD.D4R1_SUM ε.hne N hA S

end LeanUrat.MovesV
