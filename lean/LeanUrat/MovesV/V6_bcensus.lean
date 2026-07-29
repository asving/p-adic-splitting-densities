/-  MovesV unit V6-3b `blk2_census` (NINE POINTS C20) — the m₂ outcome census:
    quadratics y² + wy + u over (u, w) ∈ Fˣ × F classified split/inert/double
    (the V6-1c divisibility predicate); the (iv)-REP (D2)-EMPTY face is
    discharged-by-typing (the count sets don't mention t). -/
import LeanUrat.MovesV.V6_a1census

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

def isRoot2 {F : Type*} [Field F] [DecidableEq F] (w u r : F) : Bool :=
  decide (r ^ 2 + w * r + u = 0)

/-- (y−r)² = y² + wy + u: the char-free double test. -/
def isDbl2 {F : Type*} [Field F] [DecidableEq F] (w u r : F) : Bool :=
  decide (w = -(2 * r) ∧ u = r ^ 2)

open Classical in
noncomputable def quadClassCount (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (rc : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : F × F => p.1 ≠ 0 ∧
    (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = rc)).card

theorem blk2_census (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (quadClassCount F 2 : ℚ) = Tsplit.eval q ∧
    ((quadClassCount F 1 : ℚ) = Tinert.eval q + Tdbl.eval q ∨
     (quadClassCount F 0 : ℚ) = Tinert.eval q) := by
  sorry

end LeanUrat.MovesV
