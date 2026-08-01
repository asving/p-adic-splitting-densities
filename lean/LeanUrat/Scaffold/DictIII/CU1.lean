/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Scaffold.DictIII.GMNReader
import LeanUrat.HC2.Defs

/-!
# Scaffold/DictIII/CU1 — Theorem CU-1 (BP_III §1.8)

E-phase target file for units III-U1..U8 (module §1.8, Theorem CU-1 +
Corollary CU-1-LVL).  Source of record: CU1 §2 Thm CU-1.

Status at hand-off (unit III-U5, 2026-08-01): BLOCKED — see the record below.
No declaration is landed; the verbatim blueprint statement is preserved in the
commented block (transcribing it weakened, or with invented placeholder
carriers for other units' owned definitions, would be a statement change).
-/

namespace LeanUrat.Scaffold.DictIII

/-! ## Unit III-U5 — `cu1` (BP_III §1.8): BLOCKED on missing dependencies

The verbatim blueprint statement is preserved in the commented block below; it
is NOT weakened or partially landed.  Status at hand-off (2026-08-01):

* -- BLOCKED(III-U5): four identifiers in the verbatim statement do not exist
  in the corpus, so the statement cannot compile as written.  Transcribed
  VERBATIM (only this file's standing `variable {p} [Fact p.Prime] {F} [Field F]
  [Finite F]` line supplying the ambient binders, as in every DictIII module),
  `lake env lean` reports, per identifier:
    - `InteriorChain` (line `(hint : InteriorChain H)`):
        "The identifier `InteriorChain` is unknown" — unit III-U2, not landed
        anywhere in `LeanUrat/` (grep over the corpus: zero declarations);
    - `CU1Pins` (line `(hpins : CU1Pins p F)`):
        "The identifier `CU1Pins` is unknown" — unit III-H3 is itself BLOCKED
        (Hyps.lean §III-H3: statement defect in row `frEQ`, `HC1.ReadFrame`
        arity/sort mismatch, fenced above unit authority); the structure exists
        only inside Hyps.lean's commented block, so it is not an available
        declaration;
    - `machineProj` (conclusion clause `(machineProj M hM).1 = H`):
        "The identifier `machineProj` is unknown" — unit III-U1, not landed;
    - `StateBinding` (conclusion clause `StateBinding M H hlift`):
        "The identifier `StateBinding` is unknown" — unit III-U3a, not landed.
  (All other vocabulary resolves: `EHist`/`EWF`/`Theta` from Carriers, `GMNData`/
  `GMNReader`/`ConsF` from GMNReader, `GRB`/`FRESH`/`LiftFn`/`OL1`/`OL6` from
  Hyps, `MovesC.History`/`MovesC.HistoryCoherent`/`MovesJ.ReadsOf` from the
  corpus.)
* Beyond statement elaboration, the assembly proof this unit owns ("List.rec on
  nodes; U2 base, U3b/c + U4 step") consumes the base and step lemmas of units
  III-U2, III-U3b, III-U3c, III-U4 — none landed.  Wave-4 order of record:
  III-U1, III-U2, III-U3a..c, III-U4 (and the III-H3 `frEQ` blueprint repair)
  must land before III-U5 can be attempted.

```
/-- THEOREM CU-1 (N-free realization + state binding), over the displayed rows:
    order-≤1 instances of GD-2/GD-3(min)/GD-6 outright; orders ≥ 2 via hGRB; plus
    hFRESH, the pins, OL6. Conclusion (i): a machine history M with
    machineProj M = 𝐇 and ReadsOf f M; (ii): the state frame after M equals the
    [F.0] stage data over Theta 𝐇 (key = Lift, width = μ_k). -/
theorem cu1 {n : ℕ} {f : Polynomial ℤ_[p]} (H : EHist p F) (hwf : EWF H)
    (hint : InteriorChain H)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (hcons : ConsF f H D R)
    (hGRB : GRB p F) (hFRESH : FRESH p F) (hpins : CU1Pins p F)
    (hOL6 : OL6 f (Theta H) D R)
    (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
    ∃ M : MovesC.History p F,
      ∃ hM : MovesC.HistoryCoherent M,
        (machineProj M hM).1 = H ∧
        MovesJ.ReadsOf p F n f M ∧ StateBinding M H hlift
```
-/

end LeanUrat.Scaffold.DictIII
