# R7 DESIGNER-ROUND RECORD (2026-07-31) — canPolicy/canPolicy_pin BLOCKED-FALSE-AS-QUANTIFIED

**Charge** (census §4.2 item 1 / D-TM (†15), IB-D26): fill the two designer data sorries
`canPolicy` / `canPolicy_pin` (MovesD/TreeCan.lean:485,492) — the `sorryAx` source of the
entire landed D-group. Statements fenced; countermodel-first if a law smells false.

**Outcome: BLOCKED — the pin is unsatisfiable as stated, for ANY policy.** The TreeCan
sorries are untouched. The compiled obstruction record is the new module
`lean/LeanUrat/MovesD/R7_pinProbe.lean` (imports `MovesD.PolPin` only; 0 sorry; every
declaration Lean-core `{propext, Classical.choice, Quot.sound}`; per-module build green,
8566 jobs).

## The finding (†R7)

`OffsetPPin.total` ("at every recentering node the policy's output realizes") composed
with `OffsetPPin.digits_prescribed` ("any realizer at a recentering is a center realizer:
`inC σ.Φ t ∧ σ.w t = σ.w σ.Φ ∧ σ.R t = C center · T 0`") forces every value of the bare
`Node` type with `species = recentering` to ADMIT a center realizer. But `Node` ties
nothing about the frame `ν.σ` to the species — `recProbeNode σ₀` (compiled) is a legal
recentering node over an ARBITRARY stage `σ₀`. Over a ramified frame no center realizer
can exist:

    t ≠ 0 ∧ inC σ.Φ t  ⟹  σ.w t = σ.e · σ.wPrev t     (Stage.hStretch)
    σ.w t = σ.w σ.Φ = σ.h                              (Stage.hwΦ)
    ⟹  σ.e ∣ σ.h  ⟹  σ.e = 1                          (Stage.hcop)

Compiled consequences:

* `offsetPPin_forces_stage_unramified : OffsetPPin pol → ∀ σ₀ : Stage p F, σ₀.e = 1`
  — ANY pin for ANY policy proves EVERY stage unramified. False in the intended
  semantics: every `e ≥ 2` increment read creates a ramified child stage (the `X² − p`
  Eisenstein side is the standard example; `TransitionCoreL` ties the child stage's index
  to the read's).
* `offsetPPin_isEmpty_of_ramified : σ₀.e ≠ 1 → ∀ pol, IsEmpty (OffsetPPin pol)` — the
  conditional countermodel: ONE in-corpus ramified `Stage` instance would empty the pin
  type globally. That instance is a bStage-scale construction (~600 lines, HC2/U31
  precedent) and was deliberately NOT attempted; the only in-corpus stages are e = 1
  (toyStage, bStage).

So `canPolicy_pin` is unfillable for ANY choice of `canPolicy`, and no HC-1 (S6b′)
vocabulary export can cure it — no formula can output a realizer where none exists. The
D-TM (†15)/IB-D26 ownership line ("the HC-1 wave instantiates Realizes … and discharges
all five laws") is SUPERSEDED by this record.

## Diagnosis: transcription over-reach, not a note error

L1's totality (note 4665–4666, "No node exists where the policy is partial") quantifies
over nodes OF A RUN. On run-reachable nodes existence holds: `LandingKey`
(MovesC/Defs.lean:552) already demands the RECORDED lift of every history-coherent
recentering node to be exactly such a center realizer — the node's own lift is the
witness, and the frame is forced unramified there. The pin's `total` (PolPin.lean, D2/D2″/
D2‴ revisions) widened "every node of the run" to "every value of the `Node` type", where
the frame is a free field. The D2‴ bypass-kill theorems (`no_pin_of_wrong_value` etc.)
proved emptiness for WRONG policies; nobody had checked non-emptiness for any policy.

## Repair options (fence event — PolPin.lean is ratified; NOT executed here)

1. Guard `total` by the frame side-condition runs guarantee (a center-realizer-existence
   antecedent, or `σ.e = 1` + weight reachability).
2. Re-key `total` to nodes of `HistoryCoherent` histories — `LandingKey`'s quantifier,
   the note-faithful domain.

Under either repair the PREVIOUSLY-RECORDED HC-1 residue stands, unchanged, at unramified
frames: `centerRealizer_exists_of_unramified_threshold` (compiled, repair-side evidence)
shows `hS6b` supplies the w/R clauses GIVEN the reachability law `wPrev Φ < h` (not
interface-derivable — a named law the repair must carry), and `support_forced`'s monomial
clause still needs the (S6b′) formula (`hS6b` shapes the residual, not the X-support).

## Consequence for the census

REMAINING_CENSUS_2026-07-31 §4.2 item 1 cannot be executed by proof as stated. Killing
the D-group `sorryAx` now requires: (a) the PolPin statement repair (new queue item,
needs sign-off), then (b) the re-scoped fill (which can then use classical choice against
`LandingKey`-style existence on the repaired domain, with the (S6b′) slot-selection
residue still named for HC-1). Until then `canPolicy`/`canPolicy_pin` remain the honest
sorries and the D-group conditionality stands.

Artifacts: `lean/LeanUrat/MovesD/R7_pinProbe.lean` (module) ·
`lean/LeanUrat/MovesD/MANIFEST.json` § `designer_round_R7_2026-07-31` (record) · this note.
