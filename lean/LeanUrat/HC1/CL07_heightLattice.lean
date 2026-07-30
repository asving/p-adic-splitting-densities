/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower

/-!
# HC1.CL07_heightLattice — LAT: the height lattice lemma (BP5 CL-07)

**Unit CL-07** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4, "LAT";
§3.2 "Supporting arithmetic (LAT, unit CL-07)").

**Informal statement.** Every coordinate height lies on the nonnegative
`(1/strTop)·ℕ` lattice: `ht c ≥ 0` and `∃ n : ℕ, ht c = n / strTop`; supported by
the divisibility chain `e_r·STR_r ∣ strTop` for every level `r`.

**Proof sketch.** `κ_r = h_r/(e_r·STR_r)` (DefsTower `kappa`); nonnegativity is
direct from the formula (`l`, slots, `κ ≥ 0` as ℕ-casts). For the lattice claim
clear denominators via the divisibility chain: `e_r·STR_r = STR_{r+1}` divides
`STR_K·e_K = strTop` for every `r ≤ K` — induction on `strAux` (each step multiplies
by the next `e`, so `strAux (r+1) ∣ strAux (K+1) = strTop`; cf. the private
`t4_strAux`/`t4_strTop_eq` toolkit in `T4_slotMinHt.lean`). Then
`strTop·ht c = strTop·l + Σ_r slot_r·(h_r·(strTop/(e_r·STR_r)))` is a ℕ-sum.

**E-phase resolutions recorded.**
* The blueprint states the unit as one display joined by "+"; it is emitted here as
  TWO named declarations (`CL07_heightLattice`, `CL07_strTop_dvd`) so the downstream
  consumers (CL-08's `wE` well-definedness, CL-09's lattice-support legs, CL-13's
  on-lattice step) can cite each half separately. No content change.
* `T.str r` is DefsTower's EXCLUSIVE accumulated stretch (audit C-1), so
  `(T.stg r).e * T.str r = T.strAux (r.val + 1)` — the divisibility is stated in the
  blueprint's `e_r·STR_r` form verbatim.

**Deps.** none (day-one unit). difficulty: routine-opus. Size: ~40. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **CL-07 (LAT), divisibility half**: the per-level scale divides the frame scale —
`e_r·STR_r ∣ strTop` (each `κ_r = h_r/(e_r·STR_r)` has denominator dividing the
frame stretch `strTop = STR_K·e_K`). -/
theorem CL07_strTop_dvd (T : Tower p F) :
    ∀ r : Fin (T.K + 1), (T.stg r).e * T.str r ∣ T.strTop := by
  sorry

/-- **CL-07 (LAT), lattice half**: every coordinate height is nonnegative and lies on
the `(1/strTop)`-lattice: `0 ≤ ht c` and `ht c = n/strTop` for some `n : ℕ`. -/
theorem CL07_heightLattice (T : Tower p F) :
    ∀ c : T.Coord, 0 ≤ T.ht c ∧ ∃ n : ℕ, T.ht c = (n : ℚ) / (T.strTop : ℚ) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL07_strTop_dvd
#print axioms LeanUrat.HC1.CL07_heightLattice
