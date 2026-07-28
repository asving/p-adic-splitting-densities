# MovesT blueprint (REV 5) — fresh-instance FABLE audit (2026-07-28)

ARTIFACT: `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` REV 5 (4023 lines, read in
full; 55 units). GROUND TRUTH re-read at source: `MOVES_2026-07-24.md` §T-ASSEMBLY
rev 7 (6970–7761: VP-1/τ-rules 7055–7090, covering 7104–7120, TB-CAP(ns)/(ns-lump)/
(ns-null) 7185–7240 incl. the Scale-map clause 7205–7207 and the slot-0 ladder
7227–7229, JC clauses + first split + F1 ledger 7462–7529, per-shape law 7537–7557,
acceptance record + p=2 census 9205–9228); the seam contracts (MovesD §2.5 W4-1
318–337 — the (b)-union and (c) texts verified verbatim; MovesS §W4-SYNC preamble
1119–1122 — both declaration-site sentences verified); the round-4 verdicts
(`MOVEST_AUDIT_CODEX4` in full — every §7 quote checked word-for-word against its
original; `MOVEST_AUDIT_FABLE4` in full); and the BUILT SIGNATURES
(`MovesD/Defs.lean`: `ShapeRead` all fields, `ShapeRead.len` 122, **`ShapeWF` ALL 12
clauses 149–178 (species_iff/root_box/window/gmu/edvd/dchain0/dchain/monic/w0/
wchain/gamTie/anchorTie)**, `Node.sideDigit` 300–301, **`ShapeRead.Matches` 311–318 —
13 conjuncts re-walked one by one**, `MatchesHist` 320–323, `TreeModel` 566–583 incl.
**`mem_single` 573–578 (an IFF: `mem (some ⟨[ν],…⟩) x ↔ child none ν x`)** and
`mem_snoc`/`root_mem`/`mem_realizable`, `D4R_CYL`, `PrefSet`; `MovesD/SW1_shapeWF.lean`
`ShapeWF_of_matches` 67–72 with `hmt0`/`hw0`; `MovesC/Defs.lean`: `Node` all fields
incl. `hh : 1 ≤ h`, `hpatTop`, `hDwidth`, `pat`, `hRanch`, `hbezCanon`,
`History.root_iff` 565–569, `Node.childWidth` 465, `JetSetup` 792+ incl. `hm : m = n·N`
and `coordOf_sorted`; `MovesS/Defs.lean:210` `LedgerIV` Prop structure CONFIRMED;
`HC2/Defs.lean:283` `ReadsOf`; all four consumed `.olean` artifacts present on this
machine; code-level sorry-grep clean — comment hits only, at the recorded lines).
History: rev 1 = Codex 35/10 + Fable 5/8; rev 2 = 21/4 + 3/4; rev 3 = 18/5 + 2/4;
rev 4 = Codex 9/4 + Fable 1/1. I verify by computation and construction; I fix
nothing.

## VERDICT: **REJECT (1 crit / 2 gap)** — the ENTIRE round-4 union is genuinely
## repaired (the p = 3 monic counter-instance dies on the new `HistLawful` clause
## and the 13-conjunct Matches roster is complete and correctly sourced against the
## built signature; `ScaleFaithful`/`KBTotTower` kill both Codex-4 mechanism
## counter-models internally; the derived rigidity is genuinely derivable, not
## smuggled; the 15-row table is quote-faithful with the tally exact and the BDY
## hold licensed) — but the fresh sweep, computing the REV-5 closed-form toy
## tables against the BUILT `TreeModel`, finds them refuting `mem_single` on BOTH
## carriers, and the refutation generalizes: {`child_cell` at o = none +
## `RootCellsOf` + `mem_single`} vs {`state_cell`/`presents` at a positive-exponent
## one-side HEAD chain} are JOINTLY UNSATISFIABLE — T-E8/E10/E11's premise rows can
## never be instantiated at the note's census-shaped instances (F1's 10-pin head
## window; carrier A's mstar-4 head read).

---

## 1. The charge's six items — results

### (1) The monic-lead clause on the REAL accessor: VERIFIED. ✓

* **The p = 3 counter-instance dies.** Re-run: one-node H, root node, card K = 3,
  e = 1, wSide = 2, g = μ = 1, n := s0 + wSide, pat(wSide/e) := 2. The REV-5 clause
  (§2.2, displayed at the `HistLawful` body's last conjunct) fires exactly at the
  monic slot: s0 + wSide = n → `sideDigit (wSide/e) = 1`. At the instance,
  `sideDigit 2 = ((pat 2 : K) : F) = 2 ≠ 1` — **`HistLawful 3 n H` now FAILS**; the
  record-#9 instance is excluded at the premise. The clause reads the real accessor
  (`Node.sideDigit ν k = ((ν.pat k : ↥ν.σ.K) : F)`, MovesD/Defs 300–301) at the
  real index `wSide/e = R.len`.
* **The 13-conjunct Matches roster is complete and each conjunct sourced.** Walked
  against the built `ShapeRead.Matches` (311–318): conjuncts 1–11 are the eleven
  field equalities species/e/h/g/μ/a/s0/wSide/Dwidth/ustar/gam — `readOf` copies
  all eleven, definitional ✓; conjunct 12 (`Nat.card ↥ν.σ.K = p ^ R.w` with
  `R.w = max (factorization) 1`) ← the p-power clause + guard dead (w₀ = 1 +
  w-mult + g ≥ 1 give card K_i ≥ p — `readOf_guards_dead`) ✓; conjunct 13
  (`R.monicTop = true → ν.sideDigit R.len = 1`) ← the REV-5 clause DIRECTLY:
  `readOf`'s `monicTop` decides true exactly at (r = 0 ∧ s0 + wSide = n ∧ root
  species), the trigger implies the clause's own trigger, and `R.len` = the
  clause's `wSide/e` ✓. No 14th conjunct exists. Over-strengthening check: the
  clause fires only at the root monic slot, where §0.5's box-normalization law
  holds for every honest instance; `History.root_iff` (565–569) arms `monicTop`
  exactly as the sketch says; SW1's `hmt0` discharge (readOf + root_iff) stands.
* Cosmetic display slip, recorded (not counted): the §2.2 **ShapeWF** roster says
  "all 12 real clauses" but ENUMERATES 11 — `root_box` is missing from the list.
  It IS sourced, in the same unit: `HistLawful`'s displayed root-box clause
  (`s0 + wSide ≤ n`) + T-V8's sketch line "InBox is subsumed: `HistLawful`'s
  root-box clause carries the L3 bound". Sourcing exists; the enumeration should
  say so where it claims exhaustiveness. (Folded into GAP-2's row for repair
  convenience; the substance is carrier-B's, below.)

### (2) The two toy carriers: the ARITHMETIC is exact, the TABLES are ILLEGAL —
### the fresh CRIT-1 (both carriers refute the built `mem_single`) + GAP-1 (the
### carrier-B slopes are unlawful under the table's own consistency clause).

* **Carrier A's census integers are preserved by the arithmetic.** Computed:
  fiber = {x : x0…x5 = 0} against `fiberAt`'s six clauses (clause (v): henV = ∅ +
  two τ-irr leaves {(1,1)} sum to 2 = n ✓; clause (vi): heads = {tA1},
  trackDeg = 1+1 = 2 = the repeated factor's m·deg ψ = 2·1 for f̄ = x² ✓;
  `IrrHalts` at the leaves: accE·accF = 1 = childWidth·μ with leaf Dwidth 1, μ 1
  ✓; the head does NOT halt: 1 ≠ Dwidth·2 ✓). N(fiberA) = 8 = 2^{9−6} ✓,
  toyA = 2 + (4+0+0) = 6 ✓ — the 9208–9209 census integers EXACT. toy_e5:
  2³·(2⁷)¹·2² = 2¹² = 2⁹·2³ ✓ (exponent ^1 = numTracks, the CRIT-3 pin intact).
  toy_state_cell at tA2a: stateEvent = cellEventE(.st tA1, .splitC) = {x0…x5 = 0}
  ✓ equality on the nose. toy_sib: the only ≥2-branch cell event is
  (.st tA1, .splitC); both children's ContFiber events are the sure event on it —
  8·8 = 8·8 ✓ (all other entrance/cell pairs give empty cells, 0 = 0).
* **Carrier B's gate identity is exact and the hull is genuinely two-slope.**
  entEvent(.st tB1) = {x0,x1,x2 = 0} = 2⁶; cellEventE(.st tB1, .splitC) =
  {x0…x4 = 0} = 2⁴; sideExp 1+1; JCmultiAt: 2⁴·2² = 2⁶ ✓. k = 2 = sides
  (`hsplit_k`) ✓, spans {3}/{4} disjoint ✓, `hside_read` ties each branch's own
  `line.slope` to its side ✓ — record #2's multi-side GEOMETRY is hosted, and
  carrier A keeps its one-side site: Fable-4 GAP-1's fix is executed as specified.
* **The rev-4 bonus self-catch is honestly resolved**: the per-sibling-digit
  wording is replaced by window-digits-on-the-head (leaves mstar 0), the census
  exponent re-derived, the inconsistency note + the shared-split `AofTr` E-phase
  watch item ON RECORD at T-G1 ✓.
* **But the tables themselves are illegal — CRIT-1 below.** And carrier B's
  pinned slopes are unlawful — GAP-1 below.

### (3) ScaleFaithful/KBTotTower vs the note's ladder display: VERIFIED. ✓

* The defining clauses are the note's own, verbatim at source: `hScale H N'` =
  "M(N) := the largest window height with base level < N — the Scale map"
  (7205–7207 ✓ re-read) and the ladder "slot 0's block b₀ … has one coordinate
  per level, heights unit-spaced, so |Z_M| ≥ ⌊M − M₀⌋" (7227–7229 ✓ re-read);
  `hRes H` = the entrance resolution ("for each cap M ≥ M₀ (the entrance
  resolution)", 7213). Both are (H, N)-functions — the pinning is faithful.
* **Codex-4 #1's counter-model dies internally.** The degenerate jet's
  `Mlev J N = M₀ J` was free data; `ScaleFaithful` (a conjunct INSIDE
  `ns_lumps`'s ∃-J) removes it. Walked: at any level with hRes H < hScale H N'
  (supplied cofinally by `scale_grow`'s diverging gap), every family the
  childless/constant model supplies has `interiorFreshIdx J (M₀+1)` nonempty
  (capped `slot0` at M := M₀+1), `vanish` pins a digit, p ≥ 2 gives a violating
  box member, so `tie` + mem-everywhere force L(M₀+1) = univ — contradiction:
  the model fails `KBTotTower.perLevel` at that level, INSIDE the consumed
  object, accepting the finding's "external to KBTot itself" verbatim. The
  scale-degenerate per-level residue is disclosed and closed by the tower ✓.
* **Codex-4 #2's counter-assignment dies by type**: `hMgrow` is the GAP form
  `Tendsto (Mlev − M₀) atTop atTop` on T-C7, T-E12, `TreeExpNs`, `NsAmendedPair`
  leg 2, AND `KBTotTower.scale_grow` (all five sites checked); T-C7's sketch now
  consumes it verbatim in T-C4's tower form — no implication step remains. The
  H-fixed equivalence with Scale unboundedness is recorded, not assumed ✓.
* Inhabitation at intended instances survives: `ScaleFaithful` is free at
  presented jets (built chart uniqueness — `coordOf_sorted`, JetSetup 792+,
  re-verified), and `scale_grow` is the note's profinite all-heights ladder
  meeting the level family — owner HC-2/D4R0K, never proved here ✓.

### (4) The derived rigidity: GENUINELY DERIVABLE, not smuggled. ✓

* `vtree_ext_eq`: off `chains`, `hleaf` (isSome ↔ chain ∧ maximal) forces
  `leafV = none` and `hns_leaf` forces `¬ nsLeaf` — so ext's on-chain clauses +
  chains/henV equality determine EVERY data field; the remaining eight fields
  are Props (proof irrelevance); funext + propext + structure eta close it.
  Checked field-by-field against the §2.5 `VTree` roster ✓.
* `shapeClass_finite`: class members carry `Realizes` (nonempty fiber) BY the
  class definition; a shared fiber member gives ext by T-E9 (unconditional,
  re-checked) hence equality by the rigidity lemma; disjoint nonempty fibers
  inject the class into the finite box's subsets ✓. `hfin` deleted legitimately.
* `AofTr_shape_const`: `ShapeEquiv`'s bijection matches `shapeOfH` chainwise;
  `hdict`/`hdict₀` convert both exponent sums termwise; the sums transport along
  the bijection ✓. `hA` deleted legitimately; `hdict` is an HONEST named owner
  hypothesis whose warrant is the note's own conditional — "(JC-multi):
  shape-determined GIVEN its side-product form" (7537–7540, re-read at source) —
  entering as a visible premise, the same genre as `presents`/`state_cell`.
  T-E10's T-E8 application now supplies `trackOf`/`hred` ✓ (Codex-4 #4 all three
  legs executed).

### (5) The 15-row disposition table: quote-per-row VERIFIED, tally exact,
### BDY hold licensed. ✓

Every row's quoted core checked word-for-word against `MOVEST_AUDIT_CODEX4`
(rows 1–13) and `MOVEST_AUDIT_FABLE4` (C-1, G-1) — all faithful (elisions marked,
none distorting). Tally re-counted: 15 = 12 F + 2 F* (#6, #13) + 1 BDY (#5) ✓.
* **The BDY hold (#5, W4-1)**: the third-round comparison is genuinely on the §5
  row with both round-4 verdicts + both texts; the contract's (b) sentence and
  the charge's else-branch verified verbatim at `MOVESD_LEAN_BLUEPRINT` 330–333.
  The hold is legitimate: Codex-4's layer-separation point is ACCEPTED into the
  row (the (b)-demand at the W4-1 layer now stated as UNMET IN-CORPUS, the
  REDUCED residue, owner HC-2/Q1) — recording the boundary is exactly the
  charge's else-branch, and the only in-corpus falsification route passes
  through the fenced `HistoryCoherent` surface (`ReadsOf` carries it —
  HC2/Defs 283 re-verified). §6's bullet says UNMET, not "adjudicated" ✓.
  CAVEAT: CRIT-1 below shows the W4-1 layer's o = none leg is not merely
  unfalsifiable in-corpus but OVER-STRONG — the repair will touch this row.
* **The S-2 fold (#6)**: `ns_bridge` verified as a real typed slot on
  `xrbOfMovesT` (`ns_null := NsAmendedPair pol ∧ ns_bridge`), the xhd_*/rel2_*
  genre, executing Codex-4's own remedy sentence; the finite face stays the
  corpus's value with the rider riding ✓. #13's F* residual is honestly scoped
  (proof fields at the gate architecture's boundary) — though CRIT-1 shows the
  DATA fields themselves fail their decide obligations.

### (6) Fresh sweep of the 55 units, prior refutations re-armed.

Census re-counted per-unit: 55 = 9V+8C+3S+13E+5F+15D+2G ✓; easy/medium/hard
14/31/10 EXACT ✓; hard list matches §6 ✓. Seam tally re-counted from the rows:
1 DISCHARGED + 4 REDUCED + 12 SUPPLIED/PARTIAL + 2 NOT-OURS = 19 ✓, NO status
moves as claimed ✓. Build-check record RE-VERIFIED ON THIS MACHINE: all four
`.olean`s present; `LedgerIV` at MovesS/Defs.lean:210 verbatim; `ReadsOf` at
HC2/Defs.lean:283; sorry-grep comment-only at the recorded lines ✓. All twelve
§0 refutation records re-armed and DEAD at the rev-5 statements: free-Σc pair
(pinned events) ✓; numTracks−1 (F1 5⁶·5¹⁸·5⁴ = 5²⁸ ✓, toy 2³·2⁷·2² = 2¹² ✓);
henV-flip (`hreal`/`Realizes` everywhere + gate) ✓; V8-premise + E6 (HistLawful;
state_cell) ✓; wchain (w-mult clause displayed at the §2.2 body + gate) ✓;
slot-0 (capped, T-C5 `hMcap`) ✓; monic-lead (this round's item (1)) ✓; KBTot
degeneracy + hMgrow (item (3)) ✓; leafV permutation (key-unique `Finset`, `Vd`
DecidableEq holds — subtype of `Multiset (ℕ×ℕ)`) ✓. Both note-level records
(no (ns) cap anywhere — `TBCapPinned` has no ns leg ✓; no raw-count limit ✓).
New rev-5 mechanisms verified sound: `SubtreeFiber`/`scope`/`hscope` is faithful
to the note's subtree recursion ("each continuing child's factor is … the fiber
mass of the strictly smaller tree T_j", 7515–7521 — the recursion IS on
subtrees, so pricing the frame's own scope is the display's structure, and
outside-sibling conditions appear on neither side of the restated `hdecomp`);
`ClusterFactorOf` displayed with the `False`-reading dead and the retraction
present at §0 + §2.7 ✓; `RedCellPartition`'s anchored triple ✓; `ClassCover`'s
transport bundle ✓; typed `hjcm` on T-E10/E11 ✓; `SideSplit` hullSlope/hslope/
hside_read + `hsplit_k` ✓ as types. The sweep's fresh yield is the one critical
and two gaps below.

---

## 2. CRITICAL finding (verified by computation against the built signatures)

**CRIT-1 · T-G1 + §2.9/§2.5 (radiating to T-E8/E10/E11): the REV-5 closed-form
toy tables refute the BUILT `TreeModel.mem_single` on BOTH carriers — and the
refutation is not a table typo: {`CellAssign.child_cell` at o = none +
`RootCellsOf` + `mem_single`} and {`SiteLedger.state_cell` + `presents` at a
one-side HEAD chain with positive fresh exponent} are JOINTLY UNSATISFIABLE, for
EVERY model — so TREE-EXP/TREE-N/per-shape's premise rows are uninstantiable at
exactly the note's census-shaped instances.**
* **The computable witness.** Built `mem_single` (MovesD/Defs 573–578) is an IFF:
  `mem (some ⟨[ν],…⟩) x ↔ child none ν x`. Take x* := (0,0,1,0,…,0). Displayed
  `toyChildA` (blueprint 3584–3586): `child(none, tAν₁, x*) = (tAν₁ = tAν₁ ∧
  x*0 = 0 ∧ x*1 = 0)` = TRUE. Displayed `toyMemA` (3577–3583):
  `mem (some tA1) x*` demands x*2 = 0 — FALSE. **`mem_single` is REFUTED**; the
  bracket's claim that the structural proof fields "are G1a decide obligations
  over the tables above" is wrong — decide REFUTES this one. Carrier B
  identically (`toyChildB none` pins x0,x1 only; `toyMemB (some tB1)` pins
  x0,x1,x2). Every T-G1 gate referencing `toyModel`/`toyCA`/`toyModelB`/`toyCAB`
  (toy_gate, toy_sib, toy_state_cell, toy_e5_instance, toy_fiber_ne,
  toy_henflip_unrealizable, toy_jcmulti_site, plus T-G2 and T-D2's toy leg)
  cannot build — the day-one duty fails on day one.
* **No repair inside the displayed design escapes — the clash is structural.**
  (i) `child_cell` (a `CellAssign` FIELD, §2.9) at o = none + `root_mem` gives,
  for ALL x: `child(none, ν₀, x) ↔ ν₀ ∈ branchSetOf (cellOf .amb x)`.
  (ii) `RootCellsOf` (hrc — premised on T-E5/E8/E10/E11 and listed for T-G1)
  makes `cellOf .amb`'s fibers EXACTLY the reduction cells. (iii) `mem_single`
  then forces stateEvent(some ⟨[ν₀]⟩) = {x : ν₀ ∈ branchSetOf(cellOf .amb x)} =
  a UNION OF REDUCTION CELLS. (iv) But at a head chain H₀ (length 1 — `hparent`
  forces the `.red` entrance; `hclosed` puts H₀ in every tree's chains) with
  `sides H₀ = 1` and `siteExp H₀ ≥ 1`, the ledger's `state_cell` + `presents` +
  `hcard`/`free` force stateEvent(some H₀) = the presented cell event = a
  NONEMPTY PROPER sub-stratum of ONE reduction cell (p^{−mstar} of it; nonempty
  whenever the fiber is — fiberAt (i) puts fiber ⊆ stateEvent(H₀), so `hreal`
  supplies the member). A union of reduction cells that meets one cell contains
  ALL of it — it cannot be a nonempty proper subset. CONTRADICTION.
* **Scope.** The poisoned class is every instance whose ledger charges a
  positive fresh exponent at a one-side head read — carrier A (head mstar 4,
  toyA = 6: the census's own integers FORCE it) and the note's F1 shape
  verbatim ("F1's 14-pin Σ_c = the 4-pin level-0 cell {f̄ = x⁴} times the 10-pin
  full-span window cell", 7491–7495; "(JC-single) … Every SIB-gate cell, incl.
  F1's full-span root window, is of this kind", 7470–7472). T-E8 (`treeExp`),
  T-E11 (`treeN`), T-E10 (`perShape_law`) premise BOTH hrc and L — their
  hypothesis rows are pairwise-satisfiable but JOINTLY contradictory at every
  such instance, so the corpus centerpiece can only ever fire vacuously where
  the note's committed integers live. This is the doctrine's own critical class
  ("a hypothesis Prop … silently strengthened into unsatisfiability", REV-2
  rule; §6 audit charge: fixed-instance satisfiability is part of statement
  review). T-E5/E6/D14 are NOT poisoned (E5 carries no ledger; E6/D14 carry no
  hrc) — the clash needs all three legs.
* **Why eight prior passes missed it**: rev ≤ 4 kept `toyModel`/`toyCA` as
  ellipses (Codex-4 #13's exact complaint); filling them at rev 5 made the
  o = none seam computable for the first time, and both prior audits checked
  `state_cell` only at the DEPTH-1 site (tA2a — where parentSt = .st and the
  equality holds; verified again this round). `WallAReconciled` quantifies only
  `some H` states — the o = none leg of `child_cell` has NO reconciliation
  surface, which is the tell.
* **FIX SHAPE (statement-level, fence-compatible).** Scope `child_cell` to
  `o = some H` (the root-children law ALREADY exists in the honest per-track
  form: `RedCellPartition`'s anchored triple at `.red` entrances, whose cells DO
  read window digits); fix the toy `child(none)` tables to pin the head read's
  digits (mem_single then holds; with `child_cell` scoped away from o = none,
  nothing forces the .amb cell to decide them); re-route T-E5's bridge step (2)
  and T-D1/D2/D3's o = none consumptions through `hred` (`child_cell_red` +
  `RedCellPartition`); re-check `eligibleT`'s W4-1 row (the o = none leg of
  `eligibleT_iff_child` dies with the scoping — the §5 W4-1 row's boundary
  language must absorb this). Then re-verify carrier A's gates (the census
  arithmetic above already checks against the corrected tables — toyChildA with
  window pins makes mem_single an equality of the SAME stratum).

## 3. GAP findings

**GAP-1 · T-G1 carrier B: the pinned hull slopes 0/1 violate the table's own
`HistLawful`-consistency clause — the two-side design as pinned cannot build.**
The table bracket demands ALL six node constants' remaining fields be "junk
consistent with `HistLawful` — a value that cannot satisfy them is a build
failure". But `HistLawful`'s slope tie (§2.2, displayed) reads
`line.slope · (e · STR · Dwidth) = h` with the built `Node.hh : 1 ≤ h`
(MovesC/Defs, verified), and its chain clause demands strictly INCREASING slopes.
At depth 1 with e = 1, STR = 1, Dwidth = 1 (forced by the root-Φ-degree-1 +
Dwidth-chain clauses): slope(tBνc) = h ≥ 1 — the pinned slope 0 is IMPOSSIBLE
(h = 0 contradicts `hh`); and slope 1 fails the chain (head slope = h₀ ≥ 1
demands child slope > 1). So BOTH pinned hull slopes (0/1, tied to the branches'
own `line.slope` by the REV-5 `hside_read`) are unlawful; carrier B's table is
internally inconsistent as displayed. The JCmultiAt identity itself is
slope-value-independent — FIX: pin lawful distinct slopes (e.g. 2/3 with
h = 2/3, head h₀ = 1), touching nothing else (StrictMono, hside_read, and the
2⁴·2² = 2⁶ arithmetic all survive verbatim). Note carrier A is slope-clean (no
slopes pinned; h free ≥ 2 at the leaves works).

**GAP-2 · §2.2: the ShapeWF sourcing roster claims "all 12 real clauses" but
enumerates 11 — `root_box` is absent from the display.** Against the built
`ShapeWF` (MovesD/Defs 149–178: 12 clauses re-counted this round), the roster
names species_iff/monic/dchain0/dchain/window/gamTie/anchorTie/edvd/gmu/w0/
wchain = 11. The 12th, `root_box`, IS sourced in the same unit (the displayed
`HistLawful` root-box clause + T-V8's sketch sentence "InBox is subsumed"), so
nothing is UNDER-SOURCED — but a roster whose entire raison d'être is
exhaustiveness (three consecutive T-V8 refutations at exactly this channel; the
REV-5 audit-charge line demands per-conjunct rosters) must enumerate all twelve
or its "all 12" claim is unverifiable by count. One-line fix: add
"root_box ← `HistLawful`'s root-box clause (the L3 bound)" to the §2.2 display.

---

## 4. What checks out (recorded so the repairer does not re-litigate)

* Both Fable-4 rows and all thirteen Codex-4 rows are repaired AS DESIGNED at the
  statement level: the monic-lead clause is the real 13th-conjunct source and
  kills the p = 3 instance; `ScaleFaithful` + `KBTotTower` close the fixed-level
  degeneracy INSIDE the consumed object; the gap-form `hMgrow` is on all five
  sites; `scope`/`hscope`/`SubtreeFiber` price the frame's own subtree per the
  note's recursion; `hfin`/`hA` are legitimately DERIVED (`vtree_ext_eq` is real
  rigidity); `ClusterFactorOf` is displayed with the retraction; the `Finset`
  re-carrier kills the permutation model; `ClassCover` types the #9 bridges;
  `RedCellPartition` is track-anchored; `SideSplit` carries the polygon tie;
  the `hjcm`s are typed; the second carrier gives JC-multi a genuine two-slope
  site (modulo GAP-1's slope values).
* The 15-row table is quote-faithful (all rows word-checked), the tally
  12/2/1 = 15 exact, the BDY hold and the S-2 part-fold both licensed on the
  texts (contract + charge else-branch verified at source).
* Census 55 = 14/31/10 exact; seam tally 1/4/12/2 = 19 row-faithful, no moves;
  the §6 honesty block correctly extended (UNMET IN-CORPUS; `ns_bridge`;
  scale-degenerate residue; carrier-B census disclaimer).
* Carrier A's ARITHMETIC hits the census integers exactly (8 = 2^{9−6},
  toyA = 6) and carrier B's gate identity is exact (2⁴·2² = 2⁶) — the numbers
  survive the CRIT-1 table repair unchanged (the fix adds window pins to
  `child(none)` and re-scopes `child_cell`; no count moves).
* Build-check record independently re-verified on this machine.

## 5. Disposition

Rev 5 clears the complete round-4 union — the second consecutive revision to
clear a full prior union — and every one of its fifteen dispositions survives
adversarial re-walking at the built signatures and the note text. The residue is
ONE fresh critical of a new kind: not a mis-sourced clause but a THREE-WAY
interface clash (`child_cell`@none + `RootCellsOf` + `mem_single` vs the head
site's ledger) that the rev-5 closed-form tables made computable for the first
time — visible as a one-line `decide` refutation on the toys and provable as
joint unsatisfiability at every census-shaped instance, F1 included. The fix is
a contained re-scoping (`child_cell` to some-states, root children through the
already-built `RedCellPartition`) + toy-table pins + two small table/display
repairs (carrier-B slopes; the 12th roster line). REJECT (1 crit / 2 gap); a
rev 6 addressing these should re-audit clean.
