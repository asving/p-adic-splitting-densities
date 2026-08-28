import Uniformity.ChapB.B82

open Polynomial IsLocalRing
namespace Scratch

example : Irreducible ((X^2 + X + 1 : Polynomial ℤ_[2]).map (residue ℤ_[2])) := by
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (PadicInt.residueField (p := 2)))]
  have hmap : (Polynomial.mapEquiv (PadicInt.residueField (p := 2)))
      ((X^2 + X + 1 : Polynomial ℤ_[2]).map (residue ℤ_[2]))
      = (X^2 + X + 1 : Polynomial (ZMod 2)) := by
    show Polynomial.map _ _ = _
    rw [Polynomial.map_map]
    simp
  rw [hmap]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X^2 + X + 1 : Polynomial (ZMod 2)).natDegree = 2 := by compute_degree!
    simp [this]
  · intro x
    fin_cases x <;> simp [IsRoot] <;> decide

example : Irreducible ((X^2 + 1 : Polynomial ℤ_[3]).map (residue ℤ_[3])) := by
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (PadicInt.residueField (p := 3)))]
  have hmap : (Polynomial.mapEquiv (PadicInt.residueField (p := 3)))
      ((X^2 + 1 : Polynomial ℤ_[3]).map (residue ℤ_[3]))
      = (X^2 + 1 : Polynomial (ZMod 3)) := by
    show Polynomial.map _ _ = _
    rw [Polynomial.map_map]
    simp
  rw [hmap]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X^2 + 1 : Polynomial (ZMod 3)).natDegree = 2 := by compute_degree!
    simp [this]
  · intro x
    fin_cases x <;> simp [IsRoot] <;> decide

end Scratch
