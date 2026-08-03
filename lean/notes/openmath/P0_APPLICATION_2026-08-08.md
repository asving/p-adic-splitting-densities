# P0 APPLICATION EXECUTED — the σ.wPrev primed-mirror change-set landed (additive new-definition route; recovery unit, campaign date 2026-08-08, wallclock 2026-08-03)

UNIT: the P0 APPLICATION recovery unit (decision 1 of the 2026-08-03 delegation,
ledger commit b70a452).  The predecessor unit died mid-run on API 529s; its partial
`lean/LeanUrat/HC2/DefsPrime.lean` was sweep-checkpointed AS-IS at d0e2b74
(completeness UNVERIFIED).  This unit audited the fragment, completed the change-set
idempotently, ran the build gates, and executed the S3-vi rider audit.

## S0. What was applied (the charter, verified against the ledger before completing)

The ACCEPTED FGMN transcription-scale repair (`FGMN_REDERIVATION_2026-08-08.md`,
ACCEPTED at REVISION 10) applied as NEW definitions per the DITERSUP displays
(`DITERSUP_STMT_2026-08-08.md` §S1/§S2), leaving every compiled name byte-untouched.
Ledger decision 1 names the deliverable exactly: "the primed mirrors per the DITERSUP
displays: SideReads′/ReadsOf′/DIterJunctionSupplier′ + TruncRunFrom′/
FTiedTruncLanding′/ftie_extends′, carrying the ACCEPTED σ.wPrev semantics at the
three token sites' analogues."  All six landed in `lean/LeanUrat/HC2/DefsPrime.lean`.
`JuncForge.lean` untouched (READ-ONLY; byte-frozen records stay on the OLD clause).

Acceptance citation consumed by this unit, PASTED from the ledger's FGMN acceptance
block ("FGMN RE-DERIVATION ACCEPTED", 2026-08-02): "the transcription-scale diagnosis
(the compiled SideReads double-scales the stride weight vs the print's
parent-valuation keying), the ROW-A SOURCE-FIRES verdict, the three-token proposal
(HC2/Defs.lean:285/287/292, sigma.w -> sigma.wPrev), the fixed points (S1 two-scale
law; clauseIII_derivable; the DITER §S3 supplier obligations; the JuncForge/D0
retained semantics), and the PIN-GEN-i discharge are ACCEPTED. The application
change-set is the application unit's deliverable (REVISION-9 scope cut), adjudicated
on the actual scratch-worktree diff at the ASVIN GATE with a post-application hostile
pass".

## S1. Audit of the predecessor fragment (recovery duty)

The d0e2b74 fragment (133 lines) contained the module header + `SideReads'` +
`ReadsOf'` and ended cleanly at `end LeanUrat.MovesJ` — no half-written block, so no
in-place repair was needed; completion was purely additive (the four glue-route decls
appended).  Fragment verdict on what existed:

* **The three token substitutions: EXACTLY RIGHT.**  Verified token-by-token against
  the compiled `SideReads` (HC2/Defs.lean:280–314) and the DITERSUP §S1 display:
  tokens 1/2 in clause (i) (Defs.lean:285/287) and token 3 in clause (ii)
  (Defs.lean:292), each `ν.σ.w (B ·)` → `ν.σ.wPrev (B ·)` inside the window
  functional `ν.e * · + j * ν.h`; the clause-(ii) residual leg's T-exponent keeps the
  `ν.σ.wPrev` it always had (unsubstituted — correct: it was never defective).
* **Clauses (iii)–(vi): CODE-IDENTICAL** to the compiled originals (anchor/order at
  the graded `σ.R` scale — the `juncforge_clauseIII_derivable` fixed point; descent
  witness; lifts + root normalization; the N-4 vertex read-off), checked against
  Defs.lean:296–314.  Comments are pointers, not byte-copies (declared in the
  header's trust-boundary paragraph); the CODE matches.
* **The σ.wPrev identification documented, not improvised**: the parent-valuation
  accessor = `Stage.wPrev` (Moves/Defs.lean DEF-4: coefficient positions/weights are
  read against the PARENT valuation; at the base the Gauss valuation) — the accepted
  reading; no improvised semantics found.
* **`ReadsOf'`**: the compiled `ReadsOf` (Defs.lean:320–327) with the single
  substitution `SideReads` → `SideReads'`.  Matches the §S2 display verbatim.

## S2. What this unit completed (the four missing decls)

Appended in namespace `LeanUrat.Scaffold.HDischarge.H1` (the compiled originals'
namespace, same opens, so unsubstituted tokens resolve identically):

* `TruncRunFrom'` — the compiled kernel (TruncatedRun.lean:186–233) with the SINGLE
  substitution `SideReads` → `SideReads'` at the [T-5] interior-read clause
  (TruncatedRun.lean:230; grep-verified the kernel's only `SideReads` binding);
  [T-0]–[T-4] and the rest of [T-5] code-identical.
* `FTiedTruncLanding'` — the compiled def (GlueRun.lean:820–833) with exactly three
  name substitutions: `ReadsOf` → `ReadsOf'`, `SideReads` → `SideReads'`,
  `TruncRunFrom` → `TruncRunFrom'`.
* `ftie_extends'` — the compiled chain constructor (GlueRun.lean:835–849), same three
  substitutions; proof term the identical anonymous-constructor pair (the unit's one
  theorem, transcription-trivial).
* `DIterJunctionSupplier'` — the compiled named open (GlueRun.lean:875–884) with
  exactly three name substitutions (`ReadsOf` → `ReadsOf'`, `SideReads` →
  `SideReads'` twice) per the §S2 display; antecedent shape, the
  `σ₁.Φ.natDegree < n` depth guard, and the conclusion's ∃-shape verbatim; the
  ITER-LAW docstring fence carried over re-pointed (two constants + fibration term
  mandatory; cyclic form fenced OUT).  Stated, NEVER asserted.

## S3. Build gates (actuals, this machine, 2026-08-03)

* `lake env lean LeanUrat/HC2/DefsPrime.lean` — **EXIT 0** (first pass after
  completion).
* `lake build` — **"Build completed successfully (8579 jobs)", exit 0**.  Additive
  confirmed: the working tree's only .lean change is DefsPrime.lean (new module,
  no importers), so no existing module was touched or broken.  (Known repo gotcha:
  HC2/Scaffold modules sit outside the root import graph, so `lake build` does not
  compile DefsPrime itself; the per-module `lake env lean` above is the compile
  witness, per standing repo practice.)
* `lake env lean LeanUrat/AxChk_baseline.lean` — **EXIT 0**; 740 footprint lines,
  **zero `sorryAx` anywhere**; capstones unchanged:
  `LeanUrat.OM.RealInstanceV2.montes_unconditional` (and `_exhaustive`, and the
  W/W3/W4 instances) at exactly `[propext, Classical.choice, Quot.sound]`.
  No footprint regression (nothing on the AxChk import graph changed).

## S4. THE S3-vi RIDER (audit only): FGMN double-scale ≟ the V9/HK52 stretch seam

CHARGE (synthesis pass 8, S3 verdict (vi), executed with P0 per ledger decision 1):
do the `V9_K1nonrec` 4 sorries (HC1/V9_K1nonrec.lean:2621/2645/2699/2717) + the
HK52 stretch gate consume the same double-scaled weight as the FGMN defect?

**VERDICT: SAME-DEFECT at the root cause; DIFFERENT sites; the P0 diff discharges
neither.**  The shared root cause is the two-scale confusion at graded stages —
a coefficient weight at a stage's OWN scale consumed where the parent-scale quantity
is the faithful one — and both sides ride the SAME compiled Stage law:

* **The common law**: `Stage.hStretch` (Moves/Defs.lean:144):
  `w B = (e : ℤ) * wPrev B` for B ≠ 0 in the coefficient carrier `inC Φ`.
  Both defects are exact by the factor e′ through this identity and both are
  invisible on the e′ = 1 perimeter (w = wPrev pointwise there).
* **FGMN side (hypothesis-side manifestation)**: the compiled SideReads (i)/(ii)
  window functional reads `ν.e * ν.σ.w (B j)` — by hStretch this is
  `ν.e * (e′ · σ.wPrev (B j))` at a graded reading stage, double-scaling the stride
  weight; the print (FGMN eq (13)) keys the ordinate at the parent valuation.
  The functional is TOO BIG by e′.
* **V9/HK52 side (conclusion-side manifestation)**: `HK52.hk52_qform_stretch`
  (HK52_stretchGate.lean:86–94) derives `σ'.w B = e′ · σV.w B` from EXACTLY
  `σ'.hStretch` + `child_e` + `child_wPrev`; `hk52_v9_qform_reduction` then shows
  V9's displayed ℚ-form `σ_{i+1}.w (B μ) = strFrame(i+1)·lineᵢ.at(μ·cwᵢ)` pins a
  stage-scale weight to a parent-scale RHS — the display is TOO SMALL by e′ on the
  left's scale.  HK53's compiled repair (`readVertex_stretch`: the honest all-e′ law
  at `strFrame(i+2) = strFrame(i+1)·ν_{i+1}.e`) is the same move-to-the-other-scale
  cure, opposite sign.
* **The coupling is more than analogy**: HK53_e2Ruling's e′ ≥ 2 fences
  (`digit_stride_dvd` with its `e′² ∣ wSide` signature, `sideReads_belowWindow_tie`,
  `sideReads_unsat_e2_s0_zero`) are derived FROM the OLD SideReads (i)+(ii) ties —
  the very three tokens FGMN repairs.  The e′² congruence is the double-scale's
  arithmetic fingerprint (two factors of e′ where the print has one).  So the whole
  V9 e′ ≥ 2 vacuity landscape is downstream of the FGMN-defective clause.
* **Why DIFFERENT sites / nothing discharged**: the four V9 sorries bind the OLD
  `ReadsOf` in their hypotheses and their conclusion-scale defect was separately
  repaired at HK53 (`readVertex_stretch`, compiled at all e′); `SideReads'` touches
  neither their statements nor their fill-blockers (the F4/F5 ruling residue).  The
  V9 statements are BYTE-UNTOUCHED by this application.
* **Check-at-application consequence (recorded, not asserted)**: HK53's
  vacuity-rescope of the V9 cone was adjudicated AGAINST THE OLD CLAUSE.  Under
  `SideReads'` the stride-congruence arithmetic changes (one factor of e′, not two),
  so none of the HK53 fences transfer automatically to the primed route —
  primed-route satisfiability at e′ ≥ 2 junction reads is exactly gate J1's
  question, and any future V9-prime cone needs the congruence fences RE-DERIVED at
  the wPrev keying.  The compiled HK53 theorems keep their exact old-clause
  meanings (retained-semantics fixed point, same as JuncForge/D0).

## S5. HONEST GATE STATUS (nothing is discharged)

* Definitions only; the one theorem (`ftie_extends'`) is the transcription-trivial
  chain constructor.  No gate fires.
* The DITERSUP gates J1–J3b were BLOCKED-ON-APPLICATION; landing these definitions
  **UNBLOCKS them (statable against compiled names) but discharges NOTHING** — J1
  (primed-bundle satisfiability at the graded junction), J2, J3a (the row-A
  ITER-LAW-FREE degeneration instance), J3b (blocked further on the gr(w₂) tie,
  GRW2_TIE_DESIGN GRT-2) all remain open, priced in DITERSUP §S5.
* The byte-frozen record is UNTOUCHED: `SideReads`, `ReadsOf`, `TruncRunFrom`,
  `FTiedTruncLanding`/`ftie_extends`, `DIterJunctionSupplier`, and every
  JuncForge/D0 theorem keep their exact compiled meanings as statements about the
  OLD clause (the FGMN REVISION-10 acceptance list (c) fixed point).
* **The POST-APPLICATION HOSTILE PASS is OWED, not performed by this unit** (the
  FGMN REVISION-9 cut: the diff itself + the rebuilt tree + a hostile pass over the
  applied state is the only total completeness oracle).  Every primed decl carries
  a STATEMENT-REVIEW FLAG in its docstring.
* Change-set completeness caveat: the six decls are the ledger decision's named
  deliverable, landed in full; the FGMN informative map (REVISIONS 4–8) lists
  further mirrors (`SideClauseR1'`/`sideReads_r1'`, R2 pair, Window/CU1 twins,
  `GlueJunction'`/`readsOf_glue'`) that are NOT part of decision 1's list and NOT
  landed — the hostile pass adjudicates whether any of them is load-bearing for the
  gates that now unblock.

## S6. File map

* `lean/LeanUrat/HC2/DefsPrime.lean` — the change-set (6 decls; predecessor's 2 +
  this unit's 4).
* This note; ledger append in `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`.
* Read-only sources consulted: `FGMN_REDERIVATION_2026-08-08.md` (REVISIONS 9–10 +
  acceptance record), `DITERSUP_STMT_2026-08-08.md` (§S1/§S2 displays),
  HC2/Defs.lean:260–330, TruncatedRun.lean:186–246, GlueRun.lean:795–884,
  HK52_stretchGate.lean, HK53_e2Ruling.lean:1–60, HC1/V9_K1nonrec.lean (sorry
  sites + addenda), Moves/Defs.lean:144 (hStretch).
