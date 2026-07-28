# MovesD E-phase Lean ratification — Codex (2026-07-28)

The deferred Codex leg on MovesD, per the rev-9 SPLIT RECORD
(`MOVESD_LEAN_BLUEPRINT_2026-07-28.md` §"THE SPLIT RECORD" and §16): "the core
goes to E-PHASE; the deferred Codex leg becomes a post-reset RATIFICATION pass
on the E-phase Lean." This is that pass — the CORE corpus (48 units, Lean at
`lean/LeanUrat/MovesD/`), now actually elaborated as `sorry`-bodied Lean
statements, checked against the note (§D4-R, `MOVES_2026-07-24.md` lines
4580-5435 + 6783-6831) and the blueprint's split record + §12/§13/§16 tables.
The SEAM (D15 + the four W4-SYNC contract entries) was supplied for context
only and explicitly fenced off as not-a-finding-target.

Run: `codex exec --skip-git-repo-check - < prompt` (stdin, not argv — the
~164KB prompt overflowed `ARG_MAX` on the first attempt: `nohup: Argument
list too long`; the immediate retry via stdin succeeded, so no second retry
was needed). Model `gpt-5.6-sol`, session `019fa764-ab30-75d3-8a23-db9f29d24da6`,
83,861 tokens. Full transcript: `/tmp/leanaudit_rats/d_verdict.txt`; prompt
assembly: `/tmp/leanaudit_rats/d_prompt.txt` (four parts — note excerpt,
split-record + §12/§13/§16 tables, §2.5 seam contract for context, then
Defs.lean + grepped theorem/lemma statements from all 48 core unit files).

## Verdict

**REJECT 0 crit / 1 gap** — i.e., in this project's grading, a clean pass:
zero DIFFERENT/STRONGER/VACUOUS findings, one WEAKER (gap-grade) finding, and
explicit FAITHFUL classifications recorded for the rest of the checked
surface (20 numbered items below).

## The one gap-grade finding

**#20, gate-block completeness (WEAKER).** The Lean gate block
(`G1_gates.lean`'s `PhatStar_W`/`PhatStar_Mfac`/`PhatStar_Nshape`/
`PhatStar_A'`/`PhatStar_NPband`) formalizes only the SHAPE-side arithmetic of
the sealed gate (W=7, M=1, Nshape=5, A'(3)=11, NPband(3)=5) and does not state
the sealed CLASSIFIER-side gate claims the note and blueprint §16 also list —
C_P̂*(2)=3, C_P̂*(3)=48, mult≡1, and the four level-N counts (the G1 file's own
docstring already flags these as "class-count semantics over PrefSet — owned
by the P-phase/menu wave, not statable as closed shape arithmetic here," so
this is a known, not a hidden, scope boundary). Concretely: `PhatStar_NPband =
5` proves the NPband helper's value, not the actual piecewise `Shape.NP pol`
— without a theorem that `PrefIdx n pol PhatStar` is inhabited, `Shape.NP`
could in principle take its empty branch (value 1) rather than the NPband
branch (value 5). One consolidated gate-completeness gap, not a defect in any
individual arithmetic theorem.

## What was checked and found FAITHFUL (no re-litigation needed)

Codex worked through 19 other numbered items and returned FAITHFUL on all of
them, with the highest-priority scrutiny reserved for the one item the split
record explicitly flagged as unsettled:

- **`gamTie`'s STR (stage-scale) factor — the item flagged hardest by the
  charge** (split record: "gate has strS = 1 — numerically untested").
  Codex's verdict: **FAITHFUL, and the apparent discrepancy is exactly the
  documented coordinate conversion** (`ShapeRead.ustar` is absolute-scale,
  `gam` is augmented-scale; the Lean equation `γ = e·STR·u* + j*·h` is the
  correct conversion, consistent with `lineS`'s slope
  `h/(e·STR·Dwidth)`). Quote: "Omitting `STR` would instead be wrong whenever
  `strS ≠ 1`; the gate's `strS = 1` does not test this, but the symbolic
  definitions and SW1 transport do." This retires the orchestrator's
  rev-9 PUSHBACK-on-merits ruling with an independent symbolic (non-numerical)
  confirmation — the exact gap the flagging asked this pass to close.
- The `ShapeRead`/`ShapeWF` certificate (species/e/h/g/μ/a, `hh`/`hcop`,
  `hspecInc`/`hspecRec`, `hmonicRoot`, `w0`/`wchain`, `gamTie`, `anchorTie`)
  against note L3 and §D4-R.6/§C.0 — all retained fields present, all
  adjudicated pins (`ENC-MONIC`, `ROOT-POOL`) correctly typed as open
  hypotheses rather than smuggled proofs.
- The `Shape n := {P // ShapeWF n P}` domain-subtype ruling (blueprint §13)
  and `MonicTie`'s two-directional tie (blueprint §12) — as adjudicated,
  no new argument raised.
- The encoding chain E1-E10 (`Ranch_deg`, `eligible_card_le`, `selRank_lt`,
  `rank_inj`, `encIdx_inj`, `fieldTower_card`) against L7-L11 — injectivity,
  pool-subfield eligibility, and the field-tower cardinality law all match.
- The mass laws (`D4R1_SUM`, `D4R1_EV`, `D4R1_EV_iff`, `D4R2_cor`) against
  D4R.1-SUM/EV — "sums indexed fibers and therefore deliberately counts
  overlaps with multiplicity," matching the note's branch-weighted-sum vs.
  event-bound split exactly, division-free rearrangement checked.
  The pool/coarse bounds (`D4R2'`, `Mfac_le`, `D4R2'_full`) against L11.
- The empty-prefix bridge (`PrefOpt_empty`, `CD_correspondence`,
  `emptyShape_law`, `D4R4_emptyPref`) against L12's `Pref(∅)={∅}` — "`none`
  is literally the empty history," the unrealizable-nonempty-shape case
  correctly kept separate from the ∅-shape case.
- `D4R4_all`/`TW_threshold_witness` against L12's uniform-N law — FAITHFUL
  "under the explicitly declared `NP-ID` seam pin"; does not overclaim
  presentation existence.
- `TreeModel`'s structural fields (`mem`/`child`/`root_mem`/`mem_single`/
  `mem_snoc`/`mem_realizable`, `tree_prefix_closed`) against L2 — root
  survives via `root_mem`, no spurious nonempty-branch law, and the absent
  all-and-only child semantics correctly counted as the declared seam, not a
  defect.

No fresh findings were raised against any item covered by the binding §12/§13
adjudications (root-inhabitation design, subtype ruling, `PresentNorm`
totality pin, `ClassFiberWelldef`, piecewise `NP`, `CanonPolicy` parameter
design) — the charge's do-not-relitigate instruction held.

## Disposition

Zero criticals; the corpus stands as ratified with one open, named,
non-blocking gap (#20) added to the ledger: the gate block should eventually
gain either (a) a `PrefIdx`-inhabitation witness at `PhatStar` tying
`PhatStar_NPband` to the actual `Shape.NP pol PhatStar` value, or (b) an
explicit statement of the classifier-side counts (C(2)=3, C(3)=48, mult≡1)
once the P-phase/menu-wave vocabulary that owns them exists — same
disposition class as the already-ledgered `NP-ID`/`ENC-MONIC`/`POL-PIN`
pins, not a new obstruction.
