# UNIT A24F verdict — amendment A-C.24″ ENACTED: C.39/C.38 re-signed over the twisted carrier; the A-C.24′ anch rows removed (2026-08-29)

**Charge:** enact A24C's delivered A-C.24″ draft in the signed surface
(`leanspec/Leanspec/ChapC.lean`): (1) pre-edit STOP-gate on the two A-C.24′ names;
(2) insert the twisted-carrier defs, re-sign C.38/C.39 over `dv2ResPolyTw` (display
scalar byte-kept), remove the refuted anch rows, write the dated A-C.24″ record;
(3) gates: leanspec ChapC exit 0, diffs quoted, everything else byte-unchanged;
(4) REVIEW_QUEUE Tier 2 row superseding A-C.24′; (5) if provable modulo ONLY the
digit-split convolution supplier, land the conditional C.39 in
`leanfinal/Uniformity/ChapC/C136f14e.lean`; attempt the supplier if within reach.

## 1. STOP-gate: PASSED (zero consumers, re-verified)

`rg "dv2ResPolyAnch_scalar|dv2ResPolyAnch_radical_eq"` over every `.lean` in the repo
(pre-edit): the ONLY hits were the two axiom declarations themselves
(`leanspec/Leanspec/ChapC.lean:1813` / `:1744`), C136f14c's boundary COMMENT (line 388,
which states no such theorem is declared), and the differently-named landed theorem
`dv2ResPolyAnch_radical_eq_of_scalar` (C136f14c — an adapter, NOT a consumer of the
axiom).  Non-`.lean` hits: verdicts/REVIEW_QUEUE prose only.  Zero consumers —
enactment proceeded.

## 2. THE ENACTMENT (leanspec/Leanspec/ChapC.lean; gate exit 0)

Four hunks, everything else byte-unchanged (`git diff`: 1 file, 83 insertions,
39 deletions, all confined to the NODE C.38a′–C.39 region):

* **NODE C.38a′ header** — one dated bracket appended: C.38/C.39 now re-signed over
  the TWISTED carrier defined over this cluster; every C.38a′ declaration
  (`dv2FullReadPoly`/`dv2FullRead`/`dv2ResPolyAnch`) byte-unchanged and consumed.
  `γg`/`pinHeight`/`γgAnch` defs at C.39: byte-unchanged.
* **NEW NODE C.38a″** (inserted after `dv2ResPolyAnch`): `twistExp` (DEFINITION
  HE7-3's exponents, exact cocycle-sum form) + `dv2ResPolyTw` (coefficient `t` =
  `root^{ε_t} ·` the anchored coefficient) — byte-faithful to C136f14d's landed shapes
  per A24C Draft 1.
* **NODE C.38** — `dv2ResPolyAnch_radical_eq` REMOVED, re-signed as
  `dv2ResPolyTw_radical_eq`: hypothesis block byte-identical, conclusion shape
  unchanged (equal `natDegree` + same monic irreducible divisors), carrier
  `dv2ResPolyAnch ↦ dv2ResPolyTw`.  Pointer records stacked (A-C.22 kept; A-C.24′
  marked superseded with the archive pointer; A-C.24″ pointer to the C.39 record).
  Rationale in the record: the degree half is carrier-indifferent
  (`natDegree_dv2ResPolyTw_eq`) but the RADICAL half is not slot-twist invariant
  (battery radical exhibit), so the radical row must live on the twisted carrier.
* **NODE C.39** — `dv2ResPolyAnch_scalar` REMOVED, re-signed as `dv2ResPolyTw_scalar`:
  hypothesis block byte-identical to the A-C.24′ row; conclusion the SOURCE display
  with the scalar byte-kept (`γgAnch L f * root^{L.cocycle (pinHeight …) 
  (complementConst L f)}`), carrier `dv2ResPolyAnch ↦ dv2ResPolyTw` on both sides.
  The full dated numbered A-C.24″ record precedes it, quoting: the archaeology
  (DEFINITION HE7-3's verbatim closed form; EFF.HE7.30 Step 2's "τ_t with res(τ_t) =
  β_ξ^{c_t}"; EFF.HE7.08's fixed-n₂ convention + tooth HE7-T-BADTWIST), the battery
  discrimination (enacted constant FAILS at exactly the 15 odd-c_z complements of 127;
  family and source-law-over-twisted-reads hold 127/127; S2's β = 1 and the decided
  ℓ = 1 branch degenerate), the no-dropped-stationarity finding (ID1 =
  `C136f14d.twistExp_cocycle_transfer` is the exact converter; machine bridge
  `dv2ResPolyTw_scalar_of_anch_family`), cite-freeness, and the archive commit
  **48927e49** (the pre-amendment text with the full A-C.24′ round-1/2 record).

**GATE:** `cd leanspec && lake env lean Leanspec/ChapC.lean` — **exit 0** both before
(baseline) and after the edits; the file's own `#eval`/`#guard` outputs unchanged.

## 3. REVIEW_QUEUE (charge 4)

`docs/REVIEW_QUEUE_2026-08-26.md` Tier 2: new A-C.24″ row inserted at the top
(newest-first), explicitly marked as SUPERSEDING the A-C.24′ row below it (round 4 of
the C.39 saga — the source vindicated, the transcription had dropped the carrier's
twist).  Carries the trust-boundary statement flags from A24C (`twistExp`,
`dv2ResPolyTw`, the A-C.24″ axiom texts) and the honest remainder (the digit-split
convolution supplier).

## 4. THE CONDITIONAL RE-SIGNED C.39 LANDED (charge 5a):
`leanfinal/Uniformity/ChapC/C136f14e.lean`

**LANDED FIRST-ATTEMPT, sorry-free, Lean-core ×5** (exit 0; every declaration
`[propext, Classical.choice, Quot.sound]` — no cite, no `exists_dvDissection`, no
sorryAx):

```text
cd leanfinal && timeout 590 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14e.lean
EXIT: 0    — 5/5 #print axioms: [propext, Classical.choice, Quot.sound]
```

* `γgAnch` — leanspec NODE C.39's pin-anchored complement read, byte-faithful twin
  (was not previously in `leanfinal`).
* `dv2Pin_sideMin_congr`, `dv2ResPolyTw_congr` — propositional transport along the
  exact split (the C136f14c `dvResPoly_congr` pattern); `pinHeight_eq_of_pin` — the
  GC-1 pin binder evaluates `pinHeight` to `M₂'`.
* ★★ `dv2ResPolyTw_scalar_of_conv_split` — **the conditional re-signed C.39**:
  conclusion byte-shaped as the signed axiom `dv2ResPolyTw_scalar` (the byte-kept
  source display `C (γgAnch L f * root^{L.cocycle (pinHeight …) (complementConst L f)})`
  over `dv2ResPolyTw` on both sides).  Proof = the four-step composition, all landed
  Lean-core: supplier `hconv` → F14C's assembler
  (`dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution`) → A24C's ID2 product law
  (`dv2ResPolyTw_mul_of_weightedConv`) → the degree-0 complement collapse (`ε_0 = 0`,
  `twistExp_zero`) + the congr transport + `ring`.

**The carried hypotheses, honestly inventoried** (the statement's premises):

* `hconv` — **the ONE proof-bearing open**: F14C §2.1's digit-split convolution
  supplier, byte-shaped as the assembler's premise instantiated at the
  block/complement pair (`g := blockFactor L f`, `z := f /ₘ blockFactor L f`,
  `Mg := M₂'`, `Mz := complementConst L f`, `Mgz := M₂`).
* Bookkeeping legs (C.36/C.37-genre side geometry at the split; open as theorems but
  none is the scalar mechanism): `hsplit` (exact split — C.35's clause under
  `BlockContext`), `hM` (pin addition `M₂ = M₂' + c_g` — C.37's translation at side
  minima), `hdeg` + `hzdeg` (side-degree addition; complement outer side is a POINT),
  `hpz` (complement's outer pin = `complementConst`), `hγ` (the complement's side-min
  digit reads as `γgAnch`), `hfS` (the block line floor), `hngz`/`hpgz` (the
  product-form binders, transported from `hne`/`hp₂` by `hsplit` — carried explicitly
  to host `hconv` in its natural form).
* **F14C §2.2's "terminal stationarity subgoal" — the obstruction that killed the
  A-C.24′ constant — does NOT appear anywhere in the premises**: it is discharged by
  ID1/ID2 (the twist bookkeeping).  This machine-confirms A24C's headline: closing
  `hconv` (+ the bookkeeping legs at genuine C.39 sites) retires the F1.4/F1.5 axiom
  rows outright.

The leanspec A-C.24″ record and the REVIEW_QUEUE row both point at this landing.
Wiring the roll-up import (`leanfinal/Uniformity/ChapC.lean` +1 line) is left to the
orchestrator, per A24C precedent.

## 5. The supplier itself (charge 5b): BLOCKED-BECAUSE, not attempted beyond triage

F14C §2.1 (the dedicated unit) records the intended route —
`C132rp5.dev_mul_conv_split_monic` + fixed-grade additivity + L2E1/L2E2 strict
off-pair and carry pricing + `dv2FullRead_modByMonic` + `dv2FullReadCarryLaw` — and
explicitly did NOT complete the pricing/reindexing proof.  That is a dedicated-unit
scope (a full strict-pricing composition over the C132rp5 monic split), not a
within-reach leg of this enactment unit; improvising it here would violate the
~3-repairs discipline.  RECORDED as the one open supplier; note that F14C §2.2's
OTHER obstruction (the terminal stationarity subgoal) is now fully discharged by
ID1/ID2 — the supplier is the LAST proof-bearing gap of the F1.4/F1.5 family.

## File inventory + gates

* `leanspec/Leanspec/ChapC.lean` — the enactment (4 hunks as quoted above + the
  one-line C136f14e pointer in the A-C.24″ record); gate `lake env lean
  Leanspec/ChapC.lean` exit 0 (run three times: baseline, post-enactment,
  post-pointer).
* `docs/REVIEW_QUEUE_2026-08-26.md` — the Tier 2 A-C.24″ row (supersedes A-C.24′).
* `leanfinal/Uniformity/ChapC/C136f14e.lean` — NEW (5 declarations, exit 0,
  Lean-core ×5, first-attempt).
* `runs/wave-c/verdict_A24F.md` — this record.
* No git operation; no other file touched.  (A concurrent unit's unstaged edit to
  `runs/wave-c/verdict_A0G.md` was observed in `git diff` — NOT this unit's.)

**Flagged for human review (trust boundary, new statement shapes):** the two
re-signed axiom texts `dv2ResPolyTw_radical_eq` / `dv2ResPolyTw_scalar` (the
A-C.24″ signature call, per the charge), the leanspec `twistExp`/`dv2ResPolyTw`
def twins, and `dv2ResPolyTw_scalar_of_conv_split`'s premise shapes (the carried
bookkeeping legs).
