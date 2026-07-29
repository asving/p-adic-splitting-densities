# MovesV round-6 Codex verdict (2026-07-29)

I’ll audit the 15 REV-6 disposition rows first, then separately test `SelMatches`, `omem_sel`, HMC/HMCAug honesty, and the post-blueprint seam deltas against the as-built sources. I’ll distinguish statement-level failures (CRITICAL) from stale citations/pointers (GAP), without proposing edits.

The first high-risk point is already clear: `SelMatches` is a definition, but it is not actually incorporated into `EntranceCut.lands`, `iotaCount`, `entEvt`, or `entInst`; those carriers can ignore `selRec`. I’m now checking the same “declared repair versus load-bearing use” issue across the 15 disposition rows and the updated MovesS seam.

## Verdict

**REJECT (15/2)** — 15 CRITICAL findings, 2 GAPs.

The HMC proposition itself remains open, but several claimed REV-6 repairs are not load-bearing, and the changed MovesS seam introduces three statement-level incompatibilities.

## 1. REV-6 disposition table: all 15 rows

| Row | Result | Classification |
|---|---|---|
| Codex5-22 — selected member | `omem_sel` landed, but the complete package over-pins equal-skeleton members through `tcellM_tgt`. | **CRITICAL** |
| Codex5-23 — selection rank | `SelMatches` matches the E9 expression locally, but entrance cuts/events are not required to use it. The claimed definitional repair is not real. | **CRITICAL** |
| Codex5-21 — `CellOf`/`stepKey` | The supposed closed definitions occur only in comments/pseudocode; `evt_disj_cell` nevertheless consumes them. | **CRITICAL** |
| Codex5-24 — HMCAug witness | `RefEvents` landed, but the claim that the coupled toy proves `¬HMCAug` for every refinement is false/unsupported. | **CRITICAL** |
| Codex5-25 — XRB closure | Provenance was corrected, but `XhdS_Stmt` still contains literal prose: “`the same three clauses …`”. It is not a closed Lean expression. | **CRITICAL** |
| Codex5-26 — off-pool scope | “Forced only outside HDom; permitted-and-chosen inside” is consistently recorded. | PASS |
| Codex5-27 — 24 CTS-M statements | The 24 bodies are now displayed; their remaining semantic defects are counted separately below. | PASS |
| Codex5-28 — placeholder closure | `writeHeights`/`shapeOfSlots` in the normative Defs layer use later V3 declarations and proof lemmas. The claimed closure/declaration order is not real. | **CRITICAL** |
| Codex5-29 — V7-5 pointers | Re-pointed to V7-5a/b/c correctly. | PASS |
| Codex5-30 — V4/V7 cycle | V4-3 is now parametric; the stated dependency cycle is removed. | PASS |
| Codex5-31 — V4-12 status | The stale “inderivability witness” claim is corrected to OPEN/UNCLAIMED. | PASS |
| Codex5-32 — XHD-d recap | The recap now consistently says process-side `TReal`. Its disagreement with the note is a separate critical below. | PASS |
| G-A — HMC/HMCAug record | The logical scoping is honest: HMC implies HMCAug by identity refinement and does not prove HMC. But no theorem unit is allocated. | **GAP** |
| G-B — dimension branch | The pool×dimension double dispatch and third no-orphan leg are stated. | PASS |
| G-C — route accessor | The text now consumes `J.route_cont` directly. | PASS |

Thus the table’s claim that all 15 rows are resolved is false: **6 rows remain CRITICAL and 1 remains a GAP**.

## 2. `SelMatches` against as-built MovesD

The value expression itself is correct:

> `MovesD.selRank (branchingRead …).w ν % (branchingRead …).mbar`

This is the same component used by as-built E9/`encIdx`. For a valid realized read, E7 makes the modulo collapse the identity, and E8 supplies the intended injectivity. In that limited sense, the value tie is definitional.

It is not, however, definitionally attached to entrance membership:

> `structure EntranceCut ... where lands : PrefIdx ... → Prop`

and

> `iotaCount ... := ∑ᶠ i ∈ {i | cut.lands i}, ...`

Neither requires `SelMatches ε i`. Likewise, `CtsMeasured.entEvt` and `entInst` are free ε-keyed data with no selection-matching law. The prose says consumers “conjoin” `SelMatches`, but the displayed carriers do not. A selection-ignoring instance can therefore pass while merging note-distinct sibling selections.

There is a second quantifier mismatch:

> `IsBranchingRead (R) := 2 ≤ R.mbar`

The consumed MovesD fact is `eligible_card_le`: `mbar` is a bound/rank codomain, not proof that the realized eligible menu has at least two members. The blueprint silently replaces “every actual shallow branching cell” with “every read whose upper bound is at least two.”

Classification:

- **C1 — CRITICAL:** `SelMatches` is not load-bearing in entrance cuts, counts, or events.
- **C2 — CRITICAL:** the branching-read roster is keyed to an upper bound rather than actual branching.

Therefore the REV-6 replacement is syntactically definitional but not a faithful definitional interface.

## 3. `omem_sel`

The new law itself is appropriately existential:

> `∃ mu ∈ omem m o, mu.status = Sum.inr (tgtSk m o h)`

It closes the original “designated skeleton absent from the roster” gap and does not demand uniqueness.

The surrounding law over-pins:

> `tcellM_tgt : ∀ ... i ... hs, tcellM ... i ... hs = tcell ...`

This applies to every roster member whose status has the same target skeleton. If two continuing siblings share a skeleton but land in different target cells, all are forced to use the designated `tcell`. No uniqueness-of-target-skeleton invariant is present in `BlockData`.

- **C3 — CRITICAL:** `omem_sel` closes the existence gap, but the package closes it by imposing an unsupported equality on all same-skeleton members.

## 4. HMC and HMCAug

### HMC itself

The HMC kernel remains open in the displayed type:

- `XHDd` is keyed to `TReal`.
- `TmplEvents` has no composite recursion.
- `marks_chains` is only one-way.
- `CompSigma_Stmt`, `CompAgg_Stmt`, V5-5, and V7-6c carry explicit HMC antecedents.
- The false-HMC process toy is typeable.

The theorem `HMC → HMCAug` does not close HMC. The G-A scoping is logically honest.

### HMCAug non-vacuity claim

The blueprint repeatedly claims:

> “at V4-11’s coupled toy `¬HMCAug` is PROVABLE for EVERY refinement”

That does not follow. For the displayed coupling that excludes `(h₁,h₂)=(0,0)`, a finite refinement can split the intermediate state according to whether `h₁=0`; the corresponding refined tail domain excludes `h₂=0` only in that state. `assign_cover` routes the first assignment, while `tevt_cover` and `tinst_cover` reassemble the coarse event. Each refined domain can then factor.

- **C4 — CRITICAL:** Codex5-24’s claimed universal `¬HMCAug` repair is not real.
- **G1 — GAP:** the claimed approximately 30-line `HMC → HMCAug` theorem has no assigned theorem/unit despite being cited as recorded.

### HMC removed from the solve

`SolveCond_Stmt` says:

> `EscapeE0Rec L → ActiveValueAgree ... → EntCount ... → InitRat_Stmt L → DetHyp ... ∧ NeumannRec ...`

It omits HMC, although the note’s solve sentence is GIVEN clauses `(i)–(v)`, and explicitly says downstream fixpoint assertions retain the HMC tag.

- **C5 — CRITICAL:** the solve is stated without the open HMC premise. This does not prove HMC, but it improperly obtains an HMC-dependent downstream conclusion.

## 5. XHD and typed-hypothesis mismatches

### XHD-d object changed

The note explicitly defines:

> `T_γ(x,h) := #{fresh-assignment chains from x realizing (γ,h)}`

and states XHD-d’s no-orphan/no-stray laws using that `T_γ`. REV-6 instead says the occurrence is to be “READ PROCESS-SIDE” and keys exactness to eventual nonemptiness of `TmplEvents.tevt`.

- **C6 — CRITICAL:** `T_γ>0` was replaced by `TReal`, changing the object quantified over. This is a statement-level weakening, regardless of the motivation to preserve HMC openness.

### Additional ENT-AGG premise

The note gives full ENT-AGG convergence:

> “GIVEN XHD-s on the shallow layer”

REV-6 adds a separate premise:

> `EntMassSummable V`

and makes V3-8a consume it.

- **C7 — CRITICAL:** this strengthens the note’s per-clause hypothesis package.

### Added `MarkDisj` burdens

The note makes marked-space disjointness part of the marked-event construction. REV-6 introduces separate open `MarkDisj` and `MarkDisjT` hypotheses and makes the LedgerIV construction depend on them.

- **C8 — CRITICAL:** extra hypotheses are required for content that the note treats as typed/definitional finite-level marked-event structure.

### ACTIVE-VALUE quantifier

`AVRec_Stmt` closes over:

> `∀ (RB : RatBurdens ...) (hK : ...), ActiveValueAgree ...`

The note requires the finite agreement check for the actual table/solve instance, not every possible `RatBurdens` and `KmatHyp` package over the carriers.

- **C9 — CRITICAL:** the universal RB/hK closure is a silent strengthening.

## 6. Claimed closed definitions that are not closed

The REV-6 repair says `CellOf` and `stepKey` are “displayed closed,” but only their intended shapes appear inside comments below `evt_disj_cell`; there is no displayed Lean declaration.

- **C10 — CRITICAL:** Codex5-21’s claimed repair is absent from the operative definitions.

Similarly, normative §2.D defines `shapeOfSlots` and `writeHeights` using:

> `readOfLetter`, `writeHeights_wf`, `writeHeights_ties`

which are assigned to later V3-3d units. The declared order is Defs before V3.

- **C11 — CRITICAL:** Codex5-28’s closure leaves an impossible forward-declaration dependency.

Finally, `XhdS_Stmt` contains:

> `(the same three clauses at F.GcellT ... verbatim)`

inside what is presented as a closed Lean definition.

- **C12 — CRITICAL:** Codex5-25’s “four bodies CLOSED” claim is textually false.
- **G2 — GAP:** `MovesS.XRBPackage` remains absent from the supplied as-built source; the blueprint acknowledges a future co-build, so this is a reference/dependency gap rather than an additional statement defect.

## 7. Post-blueprint seam sync

### `RS4Chain.legs_read`

The updated structure has the mandatory field:

> `legs_read : ∀ p ... ∀ δ ∈ consumedDeltas T F, ... → LegAgree ...`

The blueprint’s “every MovesS interface field” table lists only `pools_e0/legs_reg`; it omits `legs_read`. V4-3’s old `ActiveValueAgree` also lacks the exact `LegAgree` package, `βmeas`, consumed-delta, non-all-active, and `hdet` quantifier structure.

- **C13 — CRITICAL:** V4-3, V7’s chain assembly perimeter, §4.2, and §4.3 W-6 are stale at statement level.

### `RS4Chain.wsh17_pin`

The blueprint says:

> “owner [3]: instantiated with W17ii’s statement at wave 4”

As built, `wsh17_pin` is a projection-def equal to `W17ii` at the chain’s own carriers; it is not a field that can be instantiated. REV-6 supplies `Wsh17PackageV`, but no theorem or explicit obligation of the actual `W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH` type.

- **C14 — CRITICAL:** V7-7, §4.2’s `wsh17_pin` row, §4.3 S-8, and the SF-2 record state the obsolete duty.

### `RatBurdens` per-cell J interface

The updated type requires:

- `jPCell`
- `jcell_ok`
- `jcell_interp`
- `jcell_sum`

REV-6 instead builds a parallel `CellPolyPack`, proves an aggregate `jRat`, and maps only the old `jP/j_ok/j_interp/j_deg*` fields. It does not target the as-built per-cell carrier `M.Cell` or prove the symbolic cell-fiber sum equals `jP`.

- **C15 — CRITICAL:** §2.H, V5-7b, V7-5a, §4.1’s RatBurdens map, and §4.3 CL-18 are stale at statement level.

### `deltaFactors`

No operative REV-6 duty explicitly defines or quotes the old all-member `deltaFactors` collection. References to `RegP` are ownership-level only. I find no separate stale blueprint unit attributable solely to the continuing-member narrowing.

### `legs_read`

The new field is covered by C13. The availability of `PolyGeomLaws`, `ReadOffBundle.legAgree_forall/ofLegAgree`, and the counted `ksub_*` variants does not itself invalidate a REV-6 statement; they are new proof routes, not mandatory references.

## Final count

- **CRITICAL: 15**
- **GAP: 2**

**REJECT (15/2).**