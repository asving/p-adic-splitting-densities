/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

/-!
# MovesGr / L4_genuine_imp_stageCoreL — the bridge (MANIFEST unit `L4_genuine_imp_stageCoreL`)

Statement byte-identical to `MANIFEST.json`. Honest status: `sorry` — see the interface-gap
note below, which is grounded in the actual field lists of `GenuineStageModel` and `StageCore`
(read 2026-07-26).

## Why this is a `sorry` and not a proof (interface underspecification)

`StageCoreL σ` (DefsL) unfolds to `⟨core : StageCore σ, tvec_unit : TvecUnitLaw σ,
coeff_loc : CoeffLocLaw σ⟩`, and `StageCore σ` (DefsCore) demands, among its 12 fields:

* `reps_nonempty : σ.reps ≠ []`
* `p_is_rep : Polynomial.C (p : ℤ_[p]) ∈ σ.reps`
* `wPrev_mul` / `wPrev_ult` — that the PARENT valuation `σ.wPrev` is multiplicative / ultrametric
* `prevIaug : (σ.e : ℤ) * σ.wPrev σ.Φ < (σ.h : ℤ)`
* `slot : SlotDecomp σ`, `coeff : CoeffFieldLawCore σ`, `tvec : TvecLaw σ`

NONE of these are recoverable from the two hypotheses actually in scope:

1. `σ : Stage p F` — its bundled fields (`Defs.lean` 106-182) constrain the CURRENT valuation
   `σ.w` (via `hwmul`, `hwult`, `hStretch`) and the residual `σ.R`, but leave `σ.reps` a free
   `List` (only `hreps` = a vacuous-if-empty membership guard) and `σ.wPrev` a FREE function with
   no multiplicativity/ultrametric field. So `reps_nonempty`, `p_is_rep`, `wPrev_mul`,
   `wPrev_ult`, `prevIaug` are independent of a bare `Stage`.
2. `M : GenuineStageModel σ` — its fields (`MovesGr/Defs.lean` 234-261: `S, hSw, Rg, homMon,
   homMon_gen, Lo, Loring, alg, isLoc, Tunit, Θ, hT, discharge`) build the associated graded ring
   from `σ.w` (via `hSw`) and pin `σ.grRes` (via `discharge`). The only mention of `σ.reps` is
   inside `homMon_gen`, which does not force it nonempty or containing `C p`; `σ.wPrev` never
   appears. So `M` supplies no round-4 combinatorial/slot/coefficient data.

This matches how the rest of the tower is wired: `StageCore`/`StageCoreL` is ALWAYS taken as an
explicit hypothesis (`hcore`) by downstream units — `L2_P6i`, `L4_TRANSvii`, `L4_TRANSviii_a`,
`L5_recVV`, `L5_landTwoSided` — and is CONSTRUCTED alongside the `Stage` at the base
(`L1_baseStage_exists` produces `∃ σ, ... ∧ StageCore σ`). It is never derived from a `Stage`
alone, precisely because it is strictly more data.

Hence the manifest statement, with hypotheses `(σ : Stage p F) (M : GenuineStageModel σ)` and no
`StageCore σ` (or the missing combinatorial fields) in scope, is NOT PROVABLE without weakening
the statement (adding a `StageCore σ` / richer-`GenuineStageModel` hypothesis) — which the
statement-fence forbids. The genuinely genuine-model-derivable parts (the tie laws feeding
`w_strict`/`w_jump`/`R_neg` via `Rg.if_mul` + `hSw`, and `CoeffLocLaw` via the discharge) do not
suffice, since the combinatorial fields above are missing. The honest fix is upstream: enrich
`GenuineStageModel` to carry (or `L4_genuine_imp_stageCoreL` to hypothesize) a `StageCore σ`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L4_genuine_imp_stageCoreL (σ : Stage p F) (M : GenuineStageModel σ) : StageCoreL σ := sorry
