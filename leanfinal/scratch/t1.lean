import Uniformity.ChapB.B82
import Uniformity.ChapB.B80

open Polynomial IsLocalRing
namespace Scratch

-- basic: divisibility of numerals in ℤ_[2]
example : ((2:ℤ_[2]))^2 ∣ (4 : ℤ_[2]) := by
  have := (PadicInt.pow_p_dvd_int_iff (p := 2) 2 4)
  push_cast at this
  rw [this]
  decide

example : ¬ ((2:ℤ_[2]))^2 ∣ (2 : ℤ_[2]) := by
  have := (PadicInt.pow_p_dvd_int_iff (p := 2) 2 2)
  push_cast at this
  rw [this]
  decide

-- irreducibility over the residue field
example : Irreducible ((X^2 + X + 1 : Polynomial ℤ_[2]).map (residue ℤ_[2])) := by
  sorry

end Scratch
