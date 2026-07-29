/-  MovesV unit V6-1c `rootTable_census` (NINE POINTS, CHAR-FREE — C20/A-4) —
    the COUNT SEMANTICS via the char-free divisibility multiplicity (no
    derivative, no discriminant).  [decide-roster attempt deferred; the
    classifier defs are CLOSED here.] -/
import LeanUrat.MovesV.V6_a1eval

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- r is a root of z³+az²+bz+c. -/
def isRoot3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (r ^ 3 + a * r ^ 2 + b * r + c = 0)

/-- (z−r)² divides (with cofactor z−s, s := −a−2r): the char-free test. -/
def isDbl3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (b = r * r + 2 * r * (-a - 2 * r) ∧ c = -(r * r * (-a - 2 * r)))

/-- (z−r)³ divides: the char-free test. -/
def isTri3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (a = -(3 * r) ∧ b = 3 * r ^ 2 ∧ c = -(r ^ 3))

open Classical in
/-- the (root count, max multiplicity) profile of z³+az²+bz+c. -/
noncomputable def rootProfile {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (a b c : F) : ℕ × ℕ :=
  ((Finset.univ.filter (fun r => isRoot3 a b c r)).card,
   Finset.univ.sup (fun r =>
     if isTri3 a b c r then 3
     else if isRoot3 a b c r && isDbl3 a b c r then 2
     else if isRoot3 a b c r then 1 else 0))

open Classical in
noncomputable def classCount (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (pr : ℕ × ℕ) : ℕ :=
  (Finset.univ.filter
    (fun t : F × F × F => rootProfile t.1 t.2.1 t.2.2 = pr)).card

/-- the census at ONE point (the nine-point roster instantiates F at
ZMod 2/3/5/7/11/13 and F4/F8/F9 — §8's decide budget; sorry-gated here). -/
theorem rootTable_census (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (classCount F (3, 1) : ℚ) = TH3.eval q ∧
    (classCount F (2, 2) : ℚ) = TH12.eval q ∧
    (classCount F (1, 3) : ℚ) = T3.eval q := by
  sorry

end LeanUrat.MovesV
