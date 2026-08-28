import Mathlib.RingTheory.DiscreteValuationRing.Basic

-- test: ℤ is not a DVR (it is not even local: 3 and 1 - 3 are both non-units)
example : ¬ IsDiscreteValuationRing ℤ := by
  intro dvr
  have h3 := dvr.toIsLocalRing.isUnit_or_isUnit_one_sub_self (3 : ℤ)
  rw [Int.isUnit_iff, Int.isUnit_iff] at h3
  norm_num at h3

-- test: destructuring an ∃-chain through a plain def head with rintro
def Wrapped (O : Type) [CommRing O] : Prop :=
  ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), True

example : ¬ Wrapped ℤ := by
  rintro ⟨dom, dvr, -⟩
  have h3 := dvr.toIsLocalRing.isUnit_or_isUnit_one_sub_self (3 : ℤ)
  rw [Int.isUnit_iff, Int.isUnit_iff] at h3
  norm_num at h3
