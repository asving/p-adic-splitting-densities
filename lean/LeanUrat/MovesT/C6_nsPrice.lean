/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesC.C6_thmC_b
import LeanUrat.MovesD.D0a_topLocus

/-! # T-C6 `ns_price` — "(ii) Theorem C(b) with Z = Z_M prices the lump exactly"
(MOVES 7225–7227): two `C6_thmC_b` instances share boxMass; cross-multiply. REV 9
re-check: `hlump`'s value conjunct makes `J.SHZ Z` THE lump event. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem ns_price {H : History p F} (J : JetSetup H n N m) (M : ℕ) (hM : M₀ J ≤ M)
    (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z)
    (hlump : IsLumpLocus J M Z) :
    Nat.card ↥(J.SHZ Z) * p ^ pinCount Z = Nat.card ↥(J.SHZ (topLocus p m)) := by
  -- Two instances of Theorem C(b) share the box mass `p^m`; cross-multiply.
  have hb := C6_thmC_b J Z hZ
  have htop := C6_thmC_b J (topLocus p m) (topLocus_admissible (J.Sigma H.nodes.length))
  unfold totalPins at hb htop
  rw [topLocus_numPinned, Nat.add_zero] at htop
  set S := (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) with hS
  -- `pinCount` counts pinned coordinates, i.e. `numPinned`.
  have hpc : pinCount Z = Z.numPinned := rfl
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine Nat.eq_of_mul_eq_mul_right (pow_pos hp S) ?_
  rw [hpc, htop, ← hb, pow_add]
  ring

end LeanUrat.MovesT
