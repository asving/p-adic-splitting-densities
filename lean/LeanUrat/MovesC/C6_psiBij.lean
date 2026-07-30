/-
Unit C6.psiBij — moves_ref: §C.2 Ψ_H is a global digit-level bijection (statement unchanged;
ROUND 3: the Θ's are H-determined via pres_theta/pres_block/keys — audit R2 F32/blocker 55).

The recorded move composite `Psi k = Θ_0 ∘ … ∘ Θ_{k−1}` is a bijection. Induction on `k`:
`Psi 0 = seg 0 0 = id` (bijective); `Psi (k+1) = seg 0 (k+1) = Psi k ∘ Θ_k`
(the `if 0 ≤ k` guard in `seg` reduces definitionally). Each `Θ_k` is bijective by
`C0_unitriBij` applied to `J.Theta_uni k`, and a composite of bijections is bijective.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_unitriBij

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C6_psiBij {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (k : ℕ) : Function.Bijective (J.Psi k) := by
  induction k with
  | zero =>
    -- `Psi 0 = seg 0 0 = id`.
    exact Function.bijective_id
  | succ k ih =>
    -- `Psi (k+1) = seg 0 (k+1) = Psi k ∘ Θ_k` (the `if 0 ≤ k` guard reduces to the `then`
    -- branch), so the goal is defeq to the composite and `exact` closes it directly.
    exact ih.comp (C0_unitriBij (J.Theta_uni k))

end LeanUrat.MovesC
