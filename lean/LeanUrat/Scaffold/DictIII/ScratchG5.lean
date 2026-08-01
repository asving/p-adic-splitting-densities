import Mathlib

open Classical in
noncomputable def gaussWprobe {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : Polynomial O) : WithTop ℤ :=
  if hB : B = 0 then ⊤ else
    Finset.min' (B.support.image fun k => algebraMap ℤ (WithTop ℤ) 0)
      (by simpa [Polynomial.support_nonempty] using hB)

set_option pp.numericTypes true in
#print gaussWprobe

-- what instance path? check the map's value
example : (algebraMap ℤ (WithTop ℤ) 0 : WithTop ℤ) = 0 := by norm_num

-- constant image: for B ≠ 0, gaussWprobe B = that constant
example {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : Polynomial O) (hB : B ≠ 0) :
    gaussWprobe B = algebraMap ℤ (WithTop ℤ) 0 := by
  rw [gaussWprobe, dif_neg hB]
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _
      (Polynomial.support_nonempty.mpr hB).choose_spec)
  · apply Finset.le_min'
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
