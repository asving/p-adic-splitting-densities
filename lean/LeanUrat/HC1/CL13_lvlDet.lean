/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL12_nclAssembly

/-!
# HC1.CL13_lvlDet — LVL-DET: level detection in the graded piece (BP5 CL-13)

**Unit CL-13** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
display (9)). Downstream of the NCL gate (CL-10 → CL-11 → CL-12 → THIS): if NCL
falls, this falls with it.

**Informal statement (display (9)).** For `y ≠ 0` supported inside the (finite)
level set `levelSet b γ`: `T.inGr γ (T.slotCoeff b y) ≠ 0` — the class of the slot
coefficient in the height-γ graded piece is DETECTED, not just the polynomial
nonzero. This is the lemma CL-14's (i-b) minimality contradiction reads at every
lower populated height.

**Proof sketch (LVL-DET = NCL + T4 + T6-detects).** NCL (`CL12_ncl`) gives
`T.slotCoeff b y ≠ 0`; `T4_slotMinHt` on `y` (its `hfin` from T7's
`levelSet_finite'`, its `hsupp` from the level-set support, and every support
height = γ) pins `T.wQ (T.slotCoeff b y) = γ` EXACTLY (the attained minimum over a
constant-height support — no weight jump possible); then
`(T6_carrierLaws T).2`'s `inγ_detects` leg gives `T.inGr γ … ≠ 0`. On-lattice note:
the support is nonempty, so `γ = ht c` for a coordinate and CL-07's LAT + T3 put
`strTop·γ ∈ ℤ` — `inGr`'s lattice dif-condition is satisfiable, no extra
hypothesis.

**E-phase resolutions recorded.**
* Display (9)'s ŷ-extension form is stated on full-domain assignments with
  level-set support, EXACTLY as CL-12 (and the CL-10 probe) state it — so the
  chain composes without re-indexing through the subtype.
* Statement-minimal imports: the proof-time deps `T4_slotMinHt`, `T6_carrierLaws`,
  `T7_alphabetSpan` (for `levelSet_finite'` — private there; re-derive or route via
  T12's boxes), `T3_htChainWeight`, and `CL07_heightLattice` are NOT imported here
  at E-phase; the prover adds them (statement needs only DefsCar, via CL-12's
  chain).

**Deps.** CL-12 (+ T4/T6/T3/T7/CL-07 at proof time). difficulty: routine-opus.
Size: ~35. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **CL-13 (display (9), LVL-DET)**: a nonzero digit assignment supported inside
one level set has DETECTED class at its level — `inGr γ (slotCoeff b y) ≠ 0`
(NCL pins the polynomial nonzero, T4 pins its weight to exactly γ, T6's
`inγ_detects` reads it off). -/
theorem CL13_lvlDet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hne : ∃ c : T.Coord, y c ≠ 0)
    (hsupp : ∀ c : T.Coord, y c ≠ 0 → c ∈ T.levelSet b γ) :
    T.inGr γ (T.slotCoeff b y) ≠ 0 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL13_lvlDet
