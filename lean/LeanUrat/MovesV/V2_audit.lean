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
  sorry

/-- the AUDIT as a duty: per entry, a proof term `cancels ⊕ splits`. -/
structure AuditedEntry (cancels splits : Prop) where
  audit : PSum cancels splits

end LeanUrat.MovesV
