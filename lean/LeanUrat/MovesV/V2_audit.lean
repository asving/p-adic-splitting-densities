/-  MovesV unit V2-6 `exp_audit_pow` — the EXPONENT-MAP AUDIT's worked law +
    the per-entry audit carrier `AuditedEntry`. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

open Classical in
theorem exp_audit_pow {F : Type*} [Field F] [Fintype F] (a : ℕ) (ha : 0 < a) :
    (Finset.univ.image (fun t : Fˣ => t ^ a)).card
      = Fintype.card Fˣ / Nat.gcd a (Fintype.card Fˣ) := by
  have hcore : (Finset.univ.image (fun t : Fˣ => t ^ a)).card
      = Nat.card ↥((powMonoidHom a : Fˣ →* Fˣ)).range := by
    rw [← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_coe_set_eq]
    rw [show ((powMonoidHom a : Fˣ →* Fˣ)) = (fun t : Fˣ => t ^ a) from rfl]
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_range]
  rw [hcore, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, Nat.gcd_comm]

/-- the AUDIT as a duty: per entry, a proof term `cancels ⊕ splits`. -/
structure AuditedEntry (cancels splits : Prop) where
  audit : PSum cancels splits

end LeanUrat.MovesV
