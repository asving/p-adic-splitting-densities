/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers

/-!
# IB-G4 — Slot_rs0Lump FORMULATION SKELETON (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (the
rs0Lump row) + §4 group G (IB-G4: "Slot_rs0Lump. ADJ→H, statement-only") and
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q5: proceed now,
statement-only, Codex audit before consumers).

THE RESERVED PARAMETER (U10_theoremU.lean:70, verbatim): "`rs0Lump` — CL-9(α)
RS.0 lumpability (owner [3])" — one of the thirteen wave-4-boundary bare-Prop
parameters of `theoremU` (UNPINNED, True-instantiable, pending this carrier).
The parameter STAYS in `theoremU`'s signature (statement fence); IB-G13's
`theoremU_bridged` instantiates it at the Prop below, call-site only.

FORMULATION TARGET (H-phase; deps: the built §S corpus via `UCarriers`; owner
[3]; note display CL-9(α)): RS.0 LUMPABILITY — the fiber-process lumpability of
the measured side over the MovesD/MovesT tree strata: aggregating the measured
kernel's states along the stratum assignment commutes with the kernel step, i.e.
the `C.MS.kstep`-aggregation invariance of the `C.MS` rows vs the tree strata
(the lumped chain is again a chain on the strata; RS.0's α-face is exactly what
licenses reading the tree-stratified fiber process through the block-state
chain).  CANDIDATE VOCABULARY (blueprint §3.8, verified built 2026-07-30):
* `MovesS.MeasuredSide.kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ`
  (MovesS/Defs.lean:173) with its laws `LedgerIV.kstep_one`/`hmc`/`act_target`
  (Defs.lean:238–247) — carried at `C.chain.L : LedgerIV C.T C.MS`;
* `MovesS.RS4Chain.L` (Interfaces.lean:129, the `LedgerIV` field) — carried at
  `C.chain`;
* the stratum/aggregation map itself has NO built carrier (the MovesT tree
  strata enter MovesU only through `TreePin`/`TreeSeam`, per-p) — the H-phase
  designs it as bound data INSIDE the Prop (a state → stratum assignment +
  the lumping identity), per §3.8's "stated over built or NEWLY-DESIGNED
  carrier vocabulary".

E-PHASE DIVISION OF LABOR (as in IB-G2, per §3.8/R9): the body is `sorry`; the
displayed Prop is the ADJ→H deliverable behind the Q5 Codex-audit gate (these
rows were left bare precisely because faithful self-contained typing failed
once).  Filling the body is a statement-design event routed through the audit,
never a silent fill.
NON-VACUITY DUTY (IB-G11b): `example : ¬ Slot_rs0Lump degenerate…` — FALSE for a
degenerate instance the note would reject (e.g. a non-lumpable two-state row).
CLOSURE MANIFEST DUTY (IB-G12): every identifier → built decl path.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS (2026-07-30, cluster BP1-P10-slots; each a minimal ambiguity
resolution against the as-built corpus, FLAGGED for the Q5 Codex audit):
* (h1) THE STRATUM ASSIGNMENT IS PINNED, NOT FREE: the MovesD/MovesT tree strata
  enter the p-uniform MovesU corpus only through their σ-emission signature — a
  state's tree-visible datum is WHICH verdict multisets its terminal outcomes emit,
  i.e. `MovesS.verdictImage C.T e τ` (the σ-index data `TreeSeam`/`TreePin` key on,
  per-p).  The stratum assignment is therefore DEFINED as the σ-emission fiber
  (τ ↦ verdictImage C.T e τ), killing the two degenerate escapes an ∃-bound
  assignment would leave open (identity partition: trivially lumpable; total
  partition: never the note's strata).
* (h2) LUMPABILITY = STRONG (1-STEP) LUMPABILITY of the measured kernel `kstep 1`
  (the generator): two σ-emission-equal states aggregate identically into every
  emission fiber.  The k-step face follows from `LedgerIV.hmc`'s Chapman–Kolmogorov
  factorization and is NOT restated (no duplicate law).
* (h3) ACTIVITY GUARDS: every `kstep` law of the corpus is `activeState`-guarded
  (LedgerIV's R13 discipline); the slot carries the same guards on BOTH source
  states — off the active locus it asserts nothing.
NON-VACUITY (IB-G11b's duty): FALSE at a degenerate instance with two
σ-emission-equal active states whose aggregated rows differ — a non-lumpable
two-state row, exactly the file-header example.
-/

namespace LeanUrat.MovesU

/-- IB-G4 — **`Slot_rs0Lump`** (CL-9(α) RS.0 lumpability, owner [3]): the
fiber-process lumpability of the measured side over the tree strata — the
`C.MS.kstep`-aggregation invariance of the `C.MS` rows vs the strata (see the
file header for the formulation target and the candidate vocabulary).  H-phase
fills the displayed Prop; Codex audit before any consumer (Q5). -/
def Slot_rs0Lump (n : ℕ) (C : UCarriers n) : Prop :=
  ∀ e, e ∈ Finset.Icc 1 n → ∀ (τ τ' : C.T.State e),
    -- (h1) same tree stratum = same σ-emission signature:
    MovesS.verdictImage C.T e τ = MovesS.verdictImage C.T e τ' →
    ∀ q₀ ∈ C.MS.Pools, C.MS.activeState q₀ e τ → C.MS.activeState q₀ e τ' →
    -- (h2) the kernel step aggregated into ANY emission fiber is stratum-constant
    -- (strong lumpability of `kstep 1`; the lumped chain is again a chain on the
    -- strata):
    ∀ s : Finset (Multiset C.T.VType),
      ∑ β ∈ Finset.univ.filter
          (fun β : C.T.State e => MovesS.verdictImage C.T e β = s),
          C.MS.kstep 1 e τ β q₀
        = ∑ β ∈ Finset.univ.filter
            (fun β : C.T.State e => MovesS.verdictImage C.T e β = s),
            C.MS.kstep 1 e τ' β q₀

end LeanUrat.MovesU
