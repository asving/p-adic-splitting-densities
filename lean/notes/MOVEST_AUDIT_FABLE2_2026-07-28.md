# MovesT blueprint (REV 2) — fresh-instance FABLE audit (2026-07-28)

ARTIFACT: `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` REV 2 (2109 lines, read in
full; 53 units). GROUND TRUTH: `MOVES_2026-07-24.md` §T-ASSEMBLY rev 7 (6970–7761, read
in full); the seam contracts re-read at source (MovesD blueprint §2.5 W4-1…W4-4; MovesS
§W4-SYNC S-1…S-11 + both ratification addenda + the typed package displays 1105–1346;
HC2 blueprint Walls A/B/C 60–145 + the clause-(vi) §7.6 sign-off note 1464–1480); the
sealed records (`CASE_SIB_SEALED_PREDICTIONS.md` L1 P2/P3 integers;
`FABLE_CONFIRM_TASM_REV6` p=2 census); and the CONSUMED LEAN SIGNATURES re-read at
source (`MovesC/Defs.lean`: `HistoryCoherent` in full, `FreshData`, `JetSetup`/`SHZ`/
`AdmissibleZ`, `Node`; `MovesC/C4_conditionalMass.lean`; `MovesD/Defs.lean`: `Box`,
`TreeModel` ALL fields incl. `mem_single`/`mem_snoc`/`mem_realizable`, `D4R_CYL`,
`ClassFiberWelldef`, `ShapeWF` ALL clauses, `PrefSet`/`reprOf`/`Nshape`/`NPband`;
`MovesD/SW1_shapeWF.lean` the FULL signature; `D8_bandShape`/`D4b_chartCount`; MovesSp
`Species`/`StageLaws`/`RootStage`/`Coherent`/`CatalogueWord`). History: round 1 =
Codex 35/10 + Fable 5/8. I verify by computation and construction; I fix nothing.

## VERDICT: **REJECT (3 crit / 4 gap)** — the rev-1 union is genuinely repaired
## (both computational refutations DIE, the seam map is honest, the Q1 fence holds);
## the fresh sweep finds three NEW statement-level defects, two introduced BY rev-2
## repairs, one pre-existing but newly constructible against the consumed signatures.

---

## 1. The charge's six hardest items — results

### (1) BOTH round-1 computational refutations re-run: they DIE. ✓

**SibCount (rev-1 Fable CRIT-1).** The rev-2 kernel (§2.6) types the conditioning
event as `cellEvent T CA o c` — a DEFINED object — and B := the cell's own branch set.
The round-1 counterexample Σc := (S₁ Δ S₂) ∩ cell is no longer expressible (no free
`Set` binder exists). At the note's F1 cell the rev-2 kernel instantiates to EXACTLY
the sealed identity: card = 2, exponent 1,
15,625 · 390,625 = 78,125² = 5¹⁴ (seal file line 131, verbatim). Falsifiability
survives the re-typing (T-S2's identical-continuations toy: k·N ≠ k² at the cell event
itself). DEAD. ✓

**T-E5 exponent (rev-1 Fable CRIT-3).** Rev 2's `numTracks` power re-derived from the
display 7485–7495: μ(fiber) = p⁻ⁿ·∏ᵢ μ(S_i│Σ₀) division-free with card(Σ₀)·pⁿ = pᵐ is
card(fiber)·card(Σ₀)ᵗ·pⁿ = pᵐ·∏ᵢ card(Σ₀ ∩ Sᵢ) — exponent t, as rev 2 states.
F1 (B22, t = 1): 5⁶·5¹⁸·5⁴ = 5²⁸ = 5²²·5⁶ ✓ EXACT. p=2 census (2⁹ box, t = 1):
8·2⁶·2³ = 2¹² = 2⁹·8 ✓ EXACT (N(root cell) = 64 = 2⁶, N(fiber) = 8, confirm line 65).
Rev-1's t−1 form dies at both (5¹⁰ = 5²⁸; 2⁶ = 2¹²). T-E8's exponent form re-verified
unchanged-and-correct at both censuses (5⁶·5^{4+12} = 5²²; 8·2^{3+3} = 2⁹). DEAD. ✓

**JCmultiAt (rev-1 Fable CRIT-2).** Typed at `cellEvent`/`stateEvent`; the Σc := {x₀}
instance is no longer expressible; the form is the display's side-product division-free
(card(cell)·p^{Σ sideExp} = card(state)). DEAD. ✓

### (2) The rebuilt seam map (21 rows) — honest, with ONE tally defect (GAP-1).

Row-by-row against the contract texts: **4 + 13 + 2 + 2 = 21 rows ✓; 19 seam entries =
4+11+2+2 ✓** (rev-1's arithmetic error fixed). Status semantics verified per row:
* **W4-4 DISCHARGED** — T-D7's statement IS W4-4(a) verbatim (∀ i, ∀ J — no `S.jet`
  weakening; checked against the contract display), route = the contract's own (c)
  (mstar_eq + fresh_band/fresh_cover + D8/D4b — all four verified to EXIST at source;
  MovesD MANIFEST line 127's conditionality pointer names exactly this). Fair.
* **S-9 DISCHARGED-for-[3t]-leg** — the three package structures are declared with the
  contract's EXACT field rosters (checked field-by-field against MovesS 1105–1346:
  XRBPackage 13 fields ✓, RS1GivenPackage 13 ✓, Wsh17Package 3 ✓; `w1mObligation`'s
  premise row = `RS1Given.holds`'s 13 conjuncts ✓); every [3t] field gets a real
  statement. Two field VALUES rest on undisplayed names (GAP-2 below).
* **W4-1/W4-2/W4-3 REDUCED** — bridge Props named (`WallAReconciled`, `RunKey`,
  `EtaLoc`), owners recorded, W4-2's crosswalk covers the contract's FULL rev-8 roster
  (checked name-by-name); T-D5's rev-2 `RunKey` (∀-jet OUTSIDE the iff) now genuinely
  yields both D4R_CYL legs at J := S.jet i, and T-D6 gets CFW (checked against the
  REAL `ClassFiberWelldef` = same-etaData ⟹ SHZ-top equality: RunKey equates each
  side with its representative's membership event, EtaLoc equates the membership
  events — sound; rev-1's quantifier error is dead). ✓
* **NOT-OURS rows (S-3, S-4, Wall B)** — each quotes the contract clause assigning the
  leg elsewhere; S-3's βmeas is indeed unstateable here; Wall B's SEED-EXIST trace is
  VERBATIM the HC2 display and MovesT's riders genuinely consume only downstream
  values. ✓
* **PARTIAL rows (S-5/S-6/S-7/S-8/S-10/S-11)** — each residual quoted verbatim from
  the contract (S-5's first-entrance-ancestor clause ✓; S-6's (BDY) fe-split ✓;
  S-7's βmeas law ✓; S-8's empty-menu/xhd_s ✓; S-10's R46 replacement act ✓; S-11's
  gate instance ✓). Honest.
* **DEFECT (GAP-1):** the headline status tally contradicts its own table on S-4 —
  the tally line counts S-4 under "12 SUPPLIED/PARTIAL ('plus S-4's recorded fence')"
  and claims "2 NOT-OURS (S-3, Wall B)", but S-4's OWN ROW says **NOT-OURS** (and
  rightly: "recorded posture only" delivers nothing). Row-faithful tally: 2
  DISCHARGED / 3 REDUCED / 11 SUPPLIED-or-PARTIAL / 3 NOT-OURS.

### (3) The site vocabulary vs the note displays. ✓ (with the E6 tie defect → CRIT-3)

`stateEvent` = the state cylinder Σ; `cellEvent` = the display's Σ_c (7290–7292);
`SiteLedger.siteExp := mstar` = the C.1.5/D.11 vol_nom exponent ✓; `AofTr` = n + Σ
window-site exponents = 7540's A(T̂) display, window sites ↔ chains (one read per
chain, prefix-closed) ✓; `siteLevel` (1 at root ✓ 7564; NPband at window sites — a
reasoned Scale-transcription, E-phase-flagged) ✓; `SitePresents` = the (JC-single)
stratum identification, whose conclusion via the REAL `C4_conditionalMass` signature
is verbatim ✓. The vocabulary is faithful; what is MISSING from it is the child-state
↔ cell-event tie (CRIT-3).

### (4) Q1 fence: **PASS.**

Corpus-wide sweep: `HistoryCoherent` appears ONLY in the consumes-header, §0 ledger
rows, docstrings/rev-notes, §4, and the disposition table — NO unit premises it.
`NodeDataLawful` re-read against the REAL `HistoryCoherent` (MovesC/Defs.lean
634–663): the child keying is HistoryCoherent's 4th conjunct
(IsRecenteringCore/IsNodeLift/TransitionCoreL + σ.s/σ.t ties — exactly task #44's V10
target); `NodeDataLawful` (e,g,μ ≥ 1 + K-card p-power) shares NO clause with it —
Q1-INSENSITIVE as claimed, nothing smuggled. `CellAssign` carries no vertex field;
G3 is spec-only `fenced-Q1`; the §4 designs match the 28j queue. (The fence HOLDS;
the fence REPAIR broke T-V8's provability — CRIT-2, a different failure.)

### (5) Disposition table: complete; truthful except two rows. ✓/✗

All 58 round-1 findings appear across 57 rows (Codex 12–13 merged); tally
43 F + 13 R + 1 PB = 57 re-counted from the rows EXACT ✓. Spot-verified dispositions
all check (Codex 1/2/3/8/10/16/17/18/20/21/24/25/29/34/35/37–45; Fable C-1…C-5,
G-1…G-8: each repair present where claimed). Two rows overstate:
* **Codex 9's "F"** — the fence is removed, but the replacement premise makes T-V8
  FALSE (CRIT-2): the repair as designed does not survive the consumed SW1 signature.
* **Codex 6's "F"** — T-V3's added "second equality" is the first conjunct multiplied
  by μ (vacuous); the display's actual second identity (CLUSTER DEGREE d = key
  degree·μ) is still absent — no cluster-degree datum appears in the statement (GAP-3).

### (6) Fresh sweep of the 53 units.

Census re-counted: 53 = 8V + 8C + 3S + 13E + 5F + 14D + 2G ✓; 13 easy / 30 medium /
10 hard re-tallied from the units EXACT ✓; hard list matches ✓. All moves_refs
spot-checked this round are accurate (incl. T-F0's 7595–7598 with the correct
irr-only pre-halt reading; T-G2's 64/58/6 and 6·390,625 = 2,343,750 = the note's
7750; T-G1's 9208–9209 census). The three findings below are the sweep's yield.

---

## 2. CRITICAL findings (all three verified by explicit construction)

**CRIT-1 · T-E8 (with T-E5, T-E11): the display's "REALIZABLE canonical tree"
qualifier is DROPPED — no hypothesis ties the tree's verdict data to the model, and
the units as typed are FALSE on the corpus's own day-one toy.**
The note quantifies TREE-EXP over "every complete finite REALIZABLE canonical tree T"
(7449–7451). T-E8's hypotheses (`hχ`/`hrc`/`hsib`/`L`/`hjcm`/`hdet`) nowhere mention
`Tr.henV`. Construction, entirely inside the blueprint's own T-G1 instance: let Tr₀ be
the toy tree (henV = {(1,1)}, census fiber = 8 on the 2⁹ box) and Tr' := Tr₀ with
henV := ∅ (lawful: `VTree.hhen` is vacuous on ∅; chains/leafV/nsLeaf unchanged). Every
T-E8 hypothesis for Tr' is the SAME PROPOSITION as for Tr₀ (the ledger L₀ reuses
verbatim — `SiteLedger` fields quantify over chains only; `toy_sib` supplies hsib;
hjcm vacuous; hdet unchanged). But fiber(Tr') = ∅: any fiber member realizes the head
chain (fiberAt (i)) ⟹ by `mem_single` + `child_cell` lies in the presented stratum
(SitePresents pins it) ⟹ f̄ = x²(x+1) ⟹ henPayload = {(1,1)} ≠ ∅ = Tr'.henV ⟹
fiberAt clause (iii) fails. So T-E8 concludes 0·2^{3+3} = 2⁹. FALSE. The same flip
kills T-E5 (fiber ∅, RHS = 2⁹·8 > 0; E5 additionally lacks a tracks-exhaust-the-cell
clause — `RootSplitData` partitions only Tr.chains, not the model's realized heads)
and T-E11 (thr reads no henV). T-E10 survives only because zero-fiber trees add 0 —
but then `CofShape`'s "realized" bracket is load-bearing and must be typed against
the SAME realization predicate. FIX SHAPE: add the display's own qualifier as a
hypothesis — `hreal : ∃ x, Tr.fiberAt T χ x` (T-D11's `Realizes`, already in-corpus)
— or a henV-tie + head-coverage pair; thread through E5/E8/E11 and CofShape.

**CRIT-2 · T-V8: the Q1-fence repair makes the ShapeWF conjunct FALSE — 
`NodeDataLawful` cannot source the certificate, and the cited dep SW1 DEMANDS
`HistoryCoherent`.**
The real `ShapeWF` (MovesD/Defs.lean 149–173) contains cross-node and node-law clauses
that `NodeDataLawful` (e,g,μ ≥ 1 + K-card p-power) does not touch: `dchain`
(D_{r+1} = childWidthS_r), `window` (s0'+w' ≤ μ_prev), `gamTie`, `anchorTie`, `edvd`
(e ∣ wSide), `gmu`, `w0` (w₀ = 1 — needs card K₀ = p EXACTLY, not a p-power),
`wchain`. Counter-instance: a two-node H with all e = g = μ = 1, K-cards p-powers
(NodeDataLawful ✓), InBox ✓, but node₁.Dwidth ≠ node₀.childWidth — `shapeOfH` copies
the fields, `dchain` fails: `ShapeWF n (shapeOfH H n)` is FALSE. And the unit's only
cited route is unusable: the REAL `ShapeWF_of_matches` signature
(MovesD/SW1_shapeWF.lean 67–72) is
`(hM) (hcoh : HistoryCoherent H) (hbox : InBox n H) (hmt0 …) (hw0 : card K₀ = p)` —
`hcoh` and `hw0` are not derivable from T-V8's premises (the blueprint itself insists
NodeDataLawful is STRICTLY WEAKER). Downstream: T-E10/T-E11 dep on T-V8; the W4-2
crosswalk cites it. Note also §0's row claim "`HistoryCoherent` implies
[NodeDataLawful] wherever both are stated" is itself unwarranted (no HistoryCoherent
clause forces μ ≥ 1 or K-card a p-power). FIX SHAPE: `NodeDataLawful` must be the
CHILD-KEYING-FREE FRAGMENT of history lawfulness (per-node laws + slope/γ/anchor ties
+ width/window/w-chains + w₀) — still Q1-insensitive, since Q1's target is solely the
4th-conjunct keying constants — plus a factored SW1 variant on the MovesD side (new
lemma, no statement change to existing units); and the §0 row's implication claim
restated honestly.

**CRIT-3 · T-E6 (and T-D14; T-E8's segment/decomposition steps): the child-state ↔
cell-event tie is silently assumed — the note's definitional "state left by the
recursion" has no typed counterpart, and E6 as displayed is refutable.**
E6 concludes card(stateEvent T (some H) ∩ E)·p^{siteExp} = card(stateEvent T
(parentSt H) ∩ E), but NOTHING ties `stateEvent T (some H)` to the presented cell:
via the REAL `mem_single`/`mem_snoc` + `child_cell`, state(some H) = the UNION of
`cellEvent(parent, c)` over ALL cells c with the node in `branchSetOf c` — and
`CellAssign` has NO uniqueness clause across cells. Construction: m = 2, Cell = Bool,
the SAME (lawful, coherent) node ν in BOTH branch sets, cellOf none x := (x 0 = 0);
T defined through mem_single/child_cell (consistent by construction); Tr = the single
maximal chain; ledger with Sigma := the free locus (stateEvent none = univ ✓), fd :=
one clause pinning coordinate 0 (mstar 1, presents ✓, free ✓, hcard ✓); E := univ
(SpectatorFor trivially ✓). Then state(some H₁) = univ (ν eligible at both cells):
LHS = 4·2 = 8 ≠ 4 = RHS. All stated hypotheses hold; the conclusion fails. The
missing content is precisely adjacent to Q2's FENCED vertex pin (§4's own words: the
pin is "exactly the clause making cellOf's digit frame at a child read WELL-DEFINED")
— i.e. E6/D14 (and E8's stitching, which must prove E7's `hdecomp` from fiberAt)
consume a consequence of fenced content with no named hypothesis. FIX SHAPE (fence-
compatible): a named hypothesis Prop — per-node cell uniqueness
(`∀ ν c c', ν ∈ branchSetOf c → ν ∈ branchSetOf c' → c = c'`) or a `SiteLedger` field
`state_cell : stateEvent T (some H) = cellEvent T CA (parentSt H) (cellAt H)` — on
T-E6/T-D14/T-E8, owner HC-2, listed in §0.

---

## 3. GAP findings

**GAP-1 · §5 tally line contradicts its own table on S-4** (detail in §1(2) above).
The headline is the artifact acceptance records quote; rev 1 was rejected partly for
exactly this channel (Fable GAP-1/Codex 35).

**GAP-2 · Undisplayed consumed names survive the REV-2 RULE ("`…` never as the body
of a consumed definition").** In T-D12's package instantiations — the S-9 [3t] leg
whose status is DISCHARGED — `tb_cap := (T-C1 ∧ T-C2 statements) ∧ NsAmendedPair …`
and `vp := VPPinned T …` bind two names defined NOWHERE in §2, with content described
only loosely in comments ("(c1)/(c2)/(c3-a) discharged + VP-SOUND's two cites as the
REMAINDER"). Also unpinned: `VdictCellData` (T-D3's `hvc`), `PartitionsDecided`
(T-F3's `hpart`), `levelIdx` (T-C2 — unbracketed), `CapIrrLaw` (pointer-pinned,
weakest case), `ClassTree`'s in-display ellipsis (bracket-flagged). The first two sit
directly under a DISCHARGED seam claim and need §2 displays.

**GAP-3 · T-V3's restatement does not deliver the display's second equality.** The
second conjunct `(∏e·∏g)·μ = (e·g·D)·μ` is the first conjunct times μ — contentless;
"cluster degree = key degree·μ" (7078–7080) needs the cluster degree d as a datum
tied to E·F·μ, which the statement never mentions. Either state d (if MovesSp carries
it) or record honestly that only the E·F = D′ leg is stateable in species vocabulary.

**GAP-4 · T-E7's rev-2 note promises "TWO displayed conjuncts, each exact" but the
statement displays ONE** (the SIB product); the jvol charge is the PREMISE `hcharge`,
which the displayed conclusion never uses. Either display the composed charge
conjunct or drop `hcharge` to E8 and fix the description — as written the E-phase
must guess which of two different units T-E7 is.

---

## 4. What checks out (recorded so the repairer does not re-litigate)

* Both rev-1 refutations dead (§1(1)); the three §0 in-corpus refutation records are
  accurate and correctly carried; `toy_sib`/`toy_e5_instance` are genuine regression
  gates for them.
* Rev-2's repairs of Codex 1–4, 7–8, 10, 14–18, 20–21, 24–25, 28–35, 36–45 and Fable
  C-4/C-5, G-1…G-8 all verified present and sound where claimed (in particular:
  `BranchDichotomy` is now the per-child saturate-or-continue law, faithful to
  7114–7118 and falsifiable; `PrunedMem`/`PreHalt` guards correct; `nsVerdictOf` pins
  the (z-3) value; T-E9/T-F1 provable under the pinned `fiberAt`; T-C2's cap is the
  contract's N(η′,⊤) with the NPband corollary consuming T-D7a explicitly; T-D5/D6
  sound from the re-quantified `RunKey`+`EtaLoc` against the REAL pinned Props;
  T-F2's `heta`+`hib` close the rev-1 surjectivity hole given the real
  `mem_realizable` roster; the gate architecture eliminates every `decide`-on-
  infinite-type; T-F4 exact; ns-null's finite-face rider present at T-C7, T-D12, §5
  S-2, AND §6).
* The conditionality ledger §0 is faithful to §T.5 (rider sites verified unit-by-
  unit); both note-refutation records honored (no (ns) cap anywhere; normalized-only
  ns bounds); quantifier honesty holds (per-(P,i) caps; member-indexed sibling
  products; no multinomial claim).
* All consumed signatures exist with the claimed shapes (spot-list in the header);
  `C4_conditionalMass`'s display is its verbatim signature; the package rosters are
  the contract's own; SEED-EXIST quoted verbatim.
* Census: 53 = 13/30/10 exact; hard list exact; splits recorded; §6's honesty block
  matches §T.5/§T.0 clause-for-clause.

## 5. Disposition

Rev 2 is a genuine structural repair: the two false-kernel classes are dead by
construction, the seam accounting is now the campaign's most honest, and the Q1 fence
is total. But the fresh sweep shows the E-layer's model ties were never re-audited as
a SYSTEM after the rev-1 fixes: the display's "realizable" qualifier fell out of the
central identities (CRIT-1, refutable on the corpus's own toy numbers), the Q1-fence
repair replaced T-V8's premise with one too weak for its own cited dep and conclusion
(CRIT-2, refutable against the real ShapeWF), and the recursion's state↔cell
identification is consumed with no typed carrier (CRIT-3, refutable through the real
mem_single/child_cell laws — content the blueprint itself locates behind the Q2
fence). All three have small, fence-compatible fix shapes (one hypothesis Prop each
plus one MovesD-side factored lemma). REJECT (3 crit / 4 gap); a rev 3 addressing
these plus the four gaps should re-audit clean.
