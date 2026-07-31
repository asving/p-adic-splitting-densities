# UNIT FORGE-A RECORD (2026-07-31) — the ramified Stage forged; R7 countermodel UNCONDITIONAL

**Charge**: build ONE compiled RAMIFIED `Stage` instance (e ≥ 2) and complete the R7
countermodel unconditionally (the conditional leg of `MovesD/R7_pinProbe.lean`,
`offsetPPin_isEmpty_of_ramified` — see `R7_PINPROBE_RECORD_2026-07-31.md`). Constraints:
new-leaf work only, statement fence, M1 coexistence rule (no TreeCan in the import
environment).

**Outcome: DELIVERED.** New leaf module `lean/LeanUrat/MovesD/R7_ramifiedForge.lean`
(0 sorry; per-file gate `lake env lean` green; all four `#print axioms` capstones
Lean-core `{propext, Classical.choice, Quot.sound}`; transitive import closure = 64
modules, TreeCan-free by script scan — TreeCan's only importer at HEAD remains
`MovesU/BridgeD1_treeModelWire`, outside this cone).

## The finding: no hand-build was needed

The R7 record priced the missing ramified instance as "a bStage-scale construction
(~600 lines, HC2/U31 precedent)". This unit's content is that the corpus already
CONTAINS the constructor: `HC1.S9_transStage` (the PROVED D.7 capstone — "every legal
increment read of a cored stage produces a cored child stage") outputs a child with
`σ'.e = e'` for ANY side `(e', h')` its `TransHyp` accepts, and NOTHING in `TransHyp`
pins `e' = 1`. Feeding it a RAMIFIED side forges the instance in ~40 lines of routing:

1. **`bStageP_stageCore` / `bStageP_stageCoreL`** — the FIRST assembly of
   `StageCoreL bStageP`. All thirteen pieces were already proved but never slotted:
   HK-13 (`bStageP_wPrev_mul/_ult`, `reps_nonempty`, `p_is_rep`, `w_strict`, `w_jump`,
   `R_neg`, `prevIaug`), HK-56 (`bStageP_slotDecomp`, `bStageP_coeffFieldLawCore`),
   HK-14 (`bStageP_tvecLaw`, `bStageP_tvecUnitLaw`, `bStageP_coeffLocLaw`). This
   discharges the `hσ` hypothesis of HK-16's `childStage_gate` as a byproduct.
2. **`transHyp_ramified : TransHyp bStageP ψ₂ 2 fq 2 5 ν₀.zbar`** — HK-47's
   `transHyp_gate` (side (1,3)) re-keyed to side **(e′, h′) = (2, 5)**. The seven
   read-shaped fields (hmonic/hirr/hne_z/hdeg/hg/hlift/hroot) do not mention (e′, h′)
   and are reused verbatim; the four side-keyed fields are new and cheap: `1 ≤ 2`,
   `1 ≤ 5`, `gcd(2,5) = 1`, and (I-aug) `5 > 2·w(fq) = 4` via the recorded normal form
   `bw fq = 2` (`HK13R.NF_θ_fq` — the same steepness fact HK-47 itself uses).
   Parameter choice: e′ = 2 is the ramification target; h′ = 5 is the least h′ with
   gcd(2, h′) = 1 clearing the I-aug threshold 2·w(fq) = 4.
3. **`ramifiedStage : Stage 2 F4`** := the `.choose` of
   `S9_transStage bStageP bStageP_stageCoreL transHyp_ramified (hEG : 1 < 1·2)`, with
   `ramifiedStage_e : e = 2`, `ramifiedStage_h : h = 5`,
   `ramifiedStage_K : K = bStageP.nextField ν₀.zbar`, `ramifiedStage_coreL :
   StageCoreL ramifiedStage`, and the full `TransitionCoreL` record
   (`ramifiedStage_trans`). Semantics: the slope-5/2, index-2 totally ramified read
   through the lift fq = X² + 2X + 4 over the p = 2 base pin — the R7 record's
   "X² − p Eisenstein side" species (an e ≥ 2 increment read whose child
   `TransitionCoreL` ties to the read's index), realized at the gate read the corpus
   already carries.
4. **`offsetPPin_isEmpty_unconditional : ∀ pol : CanonPolicy 2 F4,
   IsEmpty (OffsetPPin pol)`** (+ consumption form `no_offsetPPin`) — the R7
   countermodel with the hypothesis DISCHARGED: any pin would prove every `Stage 2 F4`
   unramified (`offsetPPin_forces_stage_unramified`), and `ramifiedStage` is not.

## Consequences

* The (†15) designer pair `canPolicy`/`canPolicy_pin` (MovesD/TreeCan.lean:485,492)
  is now refuted-at-instance with NO pending construction obligation: `OffsetPPin` as
  stated is empty for every policy over (2, F4). The sorries themselves are UNTOUCHED
  (statement fence); the PolPin statement-repair queue item from the R7 record stands
  unchanged and is still the only route to killing the D-group `sorryAx`.
* The forge is wave-D groundwork on two axes: (a) `StageCoreL bStageP` is assembled
  and reusable (HK-16's gate can now fire hypothesis-free); (b) `ramifiedStage` is a
  CORED ramified frame with a full transition record — deeper reads can be mounted on
  it exactly as S9/S10 mount on the base pin.
* Method note for future instance forges: before pricing a hand-built `Stage`, check
  whether `S9_transStage`/`S10_recStage` reach the target shape from an existing cored
  stage — the side `(e', h')` is a free parameter of `TransHyp`, so ramification,
  steep slopes, and residue growth are all producible by routing, not building.

**Artifacts**: `lean/LeanUrat/MovesD/R7_ramifiedForge.lean` (module) ·
`lean/LeanUrat/MovesD/MANIFEST.json` § `forge_A_ramified_2026-07-31` (record) · this note.

**Verification**: `lake env lean LeanUrat/MovesD/R7_ramifiedForge.lean` green,
first-pass; `#print axioms` (in-file) on `bStageP_stageCoreL`, `transHyp_ramified`,
`ramifiedStage_e`, `offsetPPin_isEmpty_unconditional` → Lean core only; import-closure
scan (python BFS over `import LeanUrat.*` lines): 64 modules, no TreeCan/BridgeD1.
