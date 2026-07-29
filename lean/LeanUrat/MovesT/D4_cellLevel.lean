/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D4 `cellLevel_local` — W4-2(b)(ii): the withdrawn cap-envelope `cell_local`
replaced at the per-state level (`siteLevel`, Defs §2.5). Soundness PROVED.

STATEMENT REPAIR 2026-07-29 (adjudicated; machine-verified refutation from the
prover fleet): the E-phase falsifier `capEnvelope_cellLocal_false` is UNPROVABLE —
over the finite coordinate type `Fin m` the uniform cap `sup(levelOf) + 1` always
exists, collapsing `CapEnvelopeCellLocal`'s premise to `x = x'`, so the envelope
HOLDS for every `T`, `CA` at every fixed finite `m` (and the existential-`m` form
is equally false). Blueprint row (MOVEST_LEAN_BLUEPRINT_2026-07-28.md, T-D4):
"theorem capEnvelope_cellLocal_false : ∃ …, ¬ CapEnvelopeCellLocal …" — the unit
is FLIPPED to the positive lemma `capEnvelope_cellLocal_holds` per the
adjudication; the blueprint row carries the matching bracket-correction. The
(b)/(c)-conflation record (W4-2(b)(ii)) is untouched: the withdrawn form is
withdrawn because it is CONTENT-FREE at finite m (one cap trivializes locality),
not because it is refutable — `cellLevel_local_sound` remains the working law. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem cellLevel_local_sound (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T)
    (o : Option (History p F)) (hlev : CA.cellLevel (embE o) = siteLevel n o)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, CA.levelOf c < siteLevel n o → x c = x' c) :
    CA.cellOf (embE o) x = CA.cellOf (embE o) x' := by
  apply CA.cell_local
  intro c hc
  exact hagree c (hlev ▸ hc)

/-- REPAIRED UNIT (2026-07-29, adjudicated): `CapEnvelopeCellLocal` HOLDS for
every `T`, `CA` at fixed finite `m` — the cap `sup(levelOf) + 1` puts every
coordinate below it, so the locality premise forces `x = x'` outright.
Blueprint row (MOVEST_LEAN_BLUEPRINT_2026-07-28.md T-D4, bracket-corrected in
place): "theorem capEnvelope_cellLocal_false : ∃ …, ¬ CapEnvelopeCellLocal …"
[REFUTED — flipped to this positive lemma]. The withdrawn-envelope record is
thereby SHARPENED: the uniform-cap form is trivially satisfiable (content-free),
which is WHY the per-state `cellLevel`/`siteLevel` law above is the real
replacement for W4-2(b)(ii). -/
theorem capEnvelope_cellLocal_holds (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) :
    CapEnvelopeCellLocal T CA := by
  classical
  refine ⟨(Finset.univ.sup CA.levelOf) + 1, fun es x x' hagree => ?_⟩
  have hx : x = x' := funext fun c =>
    hagree c (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ c)))
  rw [hx]

end LeanUrat.MovesT
