/-
Unit C0.moveMass — moves_ref: §C.2 move maps are global digit-level bijections
(Fact A/B): mass preserved.
A bijective move `Θ` on the box carries the pullback solution set onto the solution set,
so `#{x // D.IsSolution (Θ x)} = D.mass`.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

variable {p : ℕ}

theorem C0_moveMass {m : ℕ} (D : Locus p m) {Θ : (Fin m → ZMod p) → (Fin m → ZMod p)} (h : Function.Bijective Θ) : Nat.card {x : Fin m → ZMod p // D.IsSolution (Θ x)} = D.mass := by
  -- `D.mass = Nat.card {x // D.IsSolution x}` by definition; the bijective move
  -- `Θ` restricts to an equiv of the two solution subtypes (side condition is `Iff.rfl`
  -- since `Equiv.ofBijective Θ h` is defeq `Θ`), then `Nat.card_congr`.
  unfold Locus.mass
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Θ h) (fun _ => Iff.rfl))

end LeanUrat.MovesC
