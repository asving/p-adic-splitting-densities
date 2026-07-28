# MovesT blueprint (REV 4) — fresh-instance FABLE audit (2026-07-28)

ARTIFACT: `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` REV 4 (3449 lines, read in
full; 55 units). GROUND TRUTH re-read at source: `MOVES_2026-07-24.md` §T-ASSEMBLY
rev 7 (6970–7761: VP-1/τ-rules 7055–7090, covering 7104–7120, TB-CAP(ns)/(ns-lump)/
(ns-null) 7185–7235, (SIB)+count face 7285–7304, SIB-STEP/PCI/indexing 7375–7423,
TREE-EXP + JC clauses + first split + F1 ledger 7440–7529, per-shape/TREE-N/ONE-F/
dictionary 7530–7611, §T.5 perimeter 7615–7665, gate scope 7694–7702, (TGT) 7014–7048,
acceptance record + p=2 census 9205–9228); the seam contracts (MovesD blueprint §2.5
W4-1…W4-4 at 318–379; MovesS §W4-SYNC 1105–1346 incl. both addenda, the preamble
sentences, `W3_recursion`'s `L : LedgerIV T M` premise, the package rosters,
`ReadLedger`/`W8_bdy`; HC2 blueprint Walls A/B/C 60–145); the round-3 verdicts
(`MOVEST_AUDIT_CODEX3` in full — every §7 quote checked against its original;
`MOVEST_AUDIT_FABLE3` in full); and the BUILT SIGNATURES (`MovesC/Defs.lean`: `Node`
all fields incl. `hDwidth`/`hbezCanon`/`pat`/`hpatTop`, `History`+`root_iff`+
`strFrame`, `HistoryCoherent` 636–658, `Node.childWidth` 465, `JetSetup` 792+ incl.
`hm : m = n·N`/`coordOf_sorted`/`coherent`/`realizable`, `C4_conditionalMass` verbatim;
`Moves/Defs.lean` `Stage` incl. `hdeg : 1 ≤ Φ.natDegree`; `MovesD/Defs.lean`:
`ShapeRead` ALL fields incl. `hw`/`hDw`/`hmonicRoot`, `ShapeRead.len` 89, `bezT` 135,
`ShapeWF` ALL 12 clauses 149–178, **`ShapeRead.Matches` 313–318 incl. the pool-card
clause AND the monic-lead tie `monicTop = true → ν.sideDigit R.len = 1`**,
`Node.sideDigit` 301, `MatchesHist` 320, `InBox` 362, `PrefSet`;
`MovesD/SW1_shapeWF.lean` `ShapeWF_of_matches` 67–72 full signature (`hmt0`/`hw0` =
the "two SW1 side conditions"); `MovesS/Defs.lean:210` `structure LedgerIV
(T : TableShape n) (M : MeasuredSide T) : Prop` CONFIRMED; `MovesS/Interfaces.lean`
34–58 `RS1Meas.βmeas`/`RS1Bundle.xrb`/`recursion_meas` incl. the `evalRe` callback +
`activeState` guard; `HC2/Defs.lean:283` `ReadsOf` incl. its internal
`HistoryCoherent`; all four consumed `.olean` artifacts present, code-level sorry-grep
clean). History: rev 1 = Codex 35/10 + Fable 5/8; rev 2 = Codex 21/4 + Fable 3/4;
rev 3 = Codex 18/5 + Fable 2/4. I verify by computation and construction; I fix
nothing.

## VERDICT: **REJECT (1 crit / 1 gap)** — the ENTIRE round-3 union is genuinely
## repaired (both rev-3 repair-mechanism criticals die at the built signatures: the
## wchain counter-instance now FAILS the new w-mult clause, and the capped ladder is
## satisfiable at presented jets while the childless falsifier is honestly
## tower-scoped; the LedgerIV import is real; the disposition table is quote-faithful
## with both pushbacks carried by the note's own sentences) — but the fresh sweep
## finds T-V8 refutable a THIRD time, at a third clause: the built
## `ShapeRead.Matches` carries the §0.5 monic-lead tie (`monicTop = true →
## ν.sideDigit len = 1`), no `HistLawful` clause sources it, and the sketch's
## "componentwise Matches is definitional" warrant is wrong at exactly that conjunct.

---

## 1. The charge's six items — results

### (1) The wchain fix: VERIFIED at the built signatures. ✓

* **The counter-instance dies on the new clause.** Re-run: F := 𝔽_{p²}, two-node H,
  card K₀ = p, card K₁ = p², g₀ = 1. The REV-4 chain clause (blueprint §2.2, displayed)
  demands `Nat.card ↥(nodes[1].σ.K) = Nat.card ↥(nodes[0].σ.K) ^ nodes[0].g`, i.e.
  p² = p¹ — FALSE. `HistLawful` now REJECTS the record-#7 instance; T-V8's premise
  excludes it. And the clause genuinely sources the real `ShapeWF.wchain`
  (MovesD/Defs 163: w_{r+1} = w_r·g_r): under w₀ (card K₀ = p) + NodeDataLawful
  p-powers + g ≥ 1, induction gives card K_i = p^{w_i} with w_i ≥ 1, and
  `(a^k).factorization p = k·(a.factorization p)` closes the chain — the `max … 1`
  guards are dead exactly as `readOf_guards_dead` states (w₀=1, w_{i+1}=w_i·g_i ≥ 1).
* **The rename is honest.** §0's row, §2.2's docstring, and §4's Q1 paragraph all now
  say KEYING-CONSTANT-FREE, and the disclosure is TRUE against the built
  `HistoryCoherent` (636–658): the fragment = conjuncts 1–3 VERBATIM + the 4th
  conjunct's non-keying trio; the omitted legs are exactly
  `IsRecenteringCore`/`IsNodeLift`/`TransitionCoreL` + the `σ.s`/`σ.t` ties; the
  w-mult clause pins only K-cards and g — no recentering core, lift, or Bézout datum
  (the V10/Q1 targets). The fence GROWS at §4 ("REV-4 ADDITION: the w-mult clause …
  its discharge is Q1-queued WITH the rest of the fragment") — present and correctly
  scoped.
* **The gmu fix reads real fields.** `g·μ ≤ wSide/e` — `wSide`, `e`, `g`, `μ` are all
  real `Node` fields; `ShapeRead.len = wSide/e` (MovesD/Defs 89) makes the shape-side
  `gmu` clause match exactly. The rev-3 `ν.len` ghost is gone.
* Bonus check (not chargeable, recorded): the remaining `ShapeRead` proof fields all
  discharge on junk nodes — `hDw : 1 ≤ Dwidth` via `Node.hDwidth` + `Stage.hdeg`
  (1 ≤ Φ.natDegree, a real Stage field); `hh`/`hcop`/`he`/`hg`/`hμ`/`hspecInc`/
  `hspecRec` are Node fields; `hw`/`hmonicRoot` by the REV-4 displayed guards.
  Fable-3 GAP-2 is genuinely closed. **The hole is elsewhere — in `Matches`, not
  `ShapeRead` (CRIT-1).**

### (2) The Mlev cap: the unsatisfiability DIES and the junk-binding evasion does
### not return. ✓ (walked at both bindings)

* **Faithful binding, inhabitation.** `slot0` now demands M − M₀ pins only for
  M₀ ≤ M ≤ Mlev; the demand tops out at Mlev − M₀, which the capped
  `ZCPack.slot0_grid` (one interior block per height in [M₀, Mlev], base 0) supplies
  inside `Fin m` — this is the note's own transcription boundary ((ns-lump) 7205–7207:
  "M(N) := the largest window height with base level < N — the Scale map"; the ladder
  7227–7229 "one coordinate per level, heights unit-spaced" runs to it). T-C5 with the
  new `hMcap` premise discharges the capped `slot0` at every presented jet, and
  `ns_lumps`' new conjunct `M₀ J ≤ Mlev J N` is T-C7's own `hM₀`. `KBTot`/`VPPinned`
  are inhabitable at the intended instances; the §2.10 `vp` value is no longer
  poisoned. (Type note, no finding: `∃ J : JetSetup H n N m` is empty off the standard
  layout — `JetSetup.hm : m = n·N` — so KBTot stays uninstantiable at m ≠ n·N models;
  every presented/intended instance is standard-layout, and falsity at junk instances
  is the right polarity for a hypothesis Prop.)
* **Degenerate model, faithful binding.** mem-everywhere/child-nowhere: `tie` forces
  ∀x ∀M x ∈ L M; at any level where the supplied jet has M₀ < Mlev, capped `slot0` at
  M := M₀+1 makes `interiorFreshIdx` nonempty, `vanish` pins a digit, and a p ≥ 2 box
  member violates it — NO family exists for that jet: the §2.4 falsifier fires exactly
  as displayed. The ∃-jet adversary gains nothing: `M₀` ("the entrance resolution")
  and `Mlev` ("largest window height with base level < N") are, per their PINNED
  defining clauses, functions of (H, N) — H's window data and the level — not of the
  jet's free data; and the built `JetSetup`'s chart is UNIQUE per level
  (`coordOf_sorted` forces the order-iso onto the n·N box coordinates), so all jets of
  (H, N) share the M₀/Mlev fate. The disclosed residue ("a level whose every jet has
  Mlev = M₀ … rejected ALONG PRESENTED TOWERS, `hMgrow` supplying falsifying levels
  cofinally") is therefore correctly scoped — and along a tower with FIXED H, M₀ is
  constant, so hMgrow (Mlev → ∞) does force Mlev − M₀ → ∞ as the parenthetical says.
* **Junk binding.** The rev-3 escape (junk-padded `interiorFreshIdx` to satisfy the
  unbounded ladder) is MOOT — the capped ladder needs no padding — and a junk binding
  would now violate the accessors' pinned defining clauses (§2.5a brackets pin them to
  the display 7217–7224, quoted at T-C5), which is exactly what the E-phase audit
  checks. The pointwise falsifier claim rev 3 made is withdrawn, tower-scoped, and the
  §6 honesty block carries it ("no pointwise-at-every-level childless-model
  falsifier"). Codex-3 #3's C6-invocation defect is also fixed (the §2.4 argument is
  pricing-free). T-C7's consumption survives verbatim (its T-C5 instance sits at
  M = Mlev, `le_refl`).

### (3) The three new toy gates: present and correctly specified — EXCEPT the
### multi-side gate has no site on the pinned toy (GAP-1).

`toy_v8_wchain` ✓: `¬ HistLawful 2 toyN twoNodeKcardH` at the record-#7 instance
(p = 2 ⟹ 𝔽₄ carrier, honestly bracketed as a SEPARATE carrier from the toy's ZMod 2);
provable via the w-mult clause (4 ≠ 2¹), and the regression pin is real IF the E-phase
instance satisfies the other clauses (the §0 record's constructibility argument
stands). `toy_state_cell` ✓ as a statement (enumerated-event equality + the ≠ face).
`toy_jcmulti_site` — see GAP-1: the PINNED toy design (one track, ONE depth-1 split
cell, both branches halting at one read) cannot carry BOTH a one-side site (which
`toy_state_cell`'s tie needs and the p=2 census shape implies) AND the "toy's one
multi-side site" the gate names. Gate ledger honesty otherwise ✓: records 1–7 each
named to a gate, record 8's protection declared TYPE-LEVEL, not oversold (Fable-3
GAP-3 closed).

### (4) The §7 disposition table: quote-per-row VERIFIED (11 rows spot-checked,
### incl. both PBs and the BDY row). ✓

Every checked row's "quoted core" is verbatim from `MOVEST_AUDIT_CODEX3` (rows 1, 2,
3, 4, 5, 8, 13, 14, 16, 17, 18 checked word-for-word; gaps 19–23 and the Fable rows
checked against my predecessor's text).
* **PB #8 (SideSplit)** — SUPPORTED: the note's own display 7477–7482 reads "the
  joint cell's literal system is the union of the k per-side systems over DISJOINT
  slot spans (hinge vertices shared, values consistent), and the CLAIMED mass is the
  side product … for a union system no accepted lemma covers" — the partition over
  disjoint spans IS the display's structure, the total-nominal-exponent pricing IS the
  open claim, and `JCmultiAt` is a hypothesis (states, never decides, the open
  theorem). The rev-4 `sideSpan`/`hspan_disj`/`hsupport` strengthening types the
  span-disjointness anyway. Fair pushback, note sentence on the row.
* **PB #13 (ns-null finite face)** — SUPPORTED: the note's (ns-null) display
  7210–7231 is the finite-level mechanism (Z_M admissible, C(b) pricing,
  |Z_M| ≥ M − M₀ ladder) closed by "continuity from above" — the profinite step —
  and the corpus's standing doctrine (§2.5 design note + §6: division-free counts,
  no measure API) genuinely cannot state it; the rider rides at T-C7/T-D12/S-2
  bindingly, and the contract's own DONE criterion ("re-keyed … and re-audited")
  routes the bridge decision to MovesS. The two-verdict record is honest.
* **BDY #14 (W4-1 layer)** — SUPPORTED: the contract's (b)-union text is quoted
  exactly (MovesD §2.5 W4-1(b), verified at 326–337: "L2's ALL-AND-ONLY children …
  ψ ranges over the eligible factors"; "NO `eligible := child` vacuity … the
  root-only childless tree must not satisfy the law for realizable inputs"); its
  corpus face IS `WallAReconciled` (a childless model's empty branch set falsifies
  the iff at every window-opening decoded input via L2 totality), and that face IS
  fenced (the built `ReadsOf` carries `HistoryCoherent` — verified at
  HC2/Defs.lean:283). Boundary declared at T-D2 + the §5 row, in-corpus rejection
  correctly named at tree level (fiberAt (v)/(vi)) + ledger level (KBTot along
  towers). Nothing overclaimed.
* **Rows #16/#17 (the BDY-index and telescope fixes)** — verified against the
  contract's `ReadLedger`/`W8_bdy` (roster verbatim; `Finset.Icc 0 L` inclusive with
  L the LAST READ INDEX): `hparent`'s `.st` leg is the immediate parent
  (length + 1, chains prefix-closed), `readLedgerOf` sets L := length − 1 with
  `chainReads_ne` supplying well-definedness and `hfe` excluding the phantom;
  `readLedgerOf_bdy` IS `W8_bdy` at the constructed value, rfl-level.
* **Row #4 (F*)** — the two-verdict split is decided by the BUILT signature as
  claimed: `Node.hDwidth : Dwidth = σ.Φ.natDegree` is a real field, so dchain0
  sources from it + the root Φ-degree-1 clause; the wchain leg is the confirmed one
  (fixed, (1) above).
* **Tally** re-counted from the rows: 29 union entries = 21 F + 5 F* + 2 PB + 1 BDY ✓
  (Codex 15 F + Fable 6 F; F* = #4/#11/#12/#22/#23; PB = #8/#13; BDY = #14).

### (5) The w3Rekeyed REAL-LedgerIV import: VERIFIED at the built file. ✓

`grep -n "structure LedgerIV" MovesS/Defs.lean` → **line 210,
`structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop`** — exactly the
blueprint's build-check claim; `.olean` artifacts present for all four consumed files;
code-level sorry-grep clean (note: the record's sentence names only the two
HC2/Defs.lean comment hits — MovesS/Defs.lean lines 7–8 also carry comment-text hits;
"code-level clean" remains true, cosmetic). `w3Rekeyed` premises
`MovesS.LedgerIV T' M` by name; the contract's `W3_recursion` takes `L : LedgerIV T M`
(MovesS blueprint 1266) — the slot-for-value pattern is dead, on BOTH the W3 and W1m
rows (`w1mObligation` carries the ledger too, per the addendum's nine-input demand).
`hxrbStmt` re-verified verbatim against the built `RS1Bundle.xrb`; the `w3Rekeyed`
conclusion re-verified verbatim against `recursion_meas` incl. the
`evalRe … (fun e' he' => βmeas e' he' h_ent)` callback and the `activeState` guard
(Interfaces.lean 44–57). Codex-3 #18: genuinely completed.

### (6) Fresh sweep of the 55 units, prior refutations re-armed.

Census re-counted: 55 = 9V+8C+3S+13E+5F+15D+2G ✓; easy/medium/hard re-tallied
per-unit = 14/31/10 EXACT ✓; hard list (C5, E5, E7, E8, E10, E11, F2, D3, D6, D7)
matches §6 ✓. Seam tally re-counted from the rows: 19 = 1 DISCHARGED (W4-4) +
4 REDUCED (W4-1/2/3, Wall A) + 12 SUPPLIED/PARTIAL + 2 NOT-OURS (S-4, Wall B) ✓;
REV 4 made no status moves as claimed ✓. Prior refutations, all re-armed and all
DEAD at the rev-4 statements: rev-1 free-Σc SibCount/JCmulti (pinned at
`cellEventE`) ✓; rev-1 numTracks−1 (E5's exponent is `htracks.t`, F1: 5⁶·5¹⁸·5⁴ =
5²⁸ = 5²²·5⁶ ✓, p=2: 8·2³·2⁶ = 2¹² ✓); rev-2 henV-flip (`hreal` on E5/E8/E11, E10's
domain + `hreal₀`, both §2.10 closures carry `Realizes`) ✓; rev-2 V8-premise and
E6-two-branch-sets (HistLawful; `state_cell` field) ✓; rev-3 wchain and slot-0 (this
round's items (1)/(2)) ✓. New rev-4 mechanisms verified sound: `IrrHalts` IS the
note's equation (7074–7080: "E·F = d(cluster)" with d = key degree·μ = childWidth·μ
in node data; NO lawfulness conjunct — "pure node/cell data" confirmed at source),
with T-V9's `acc_childWidth` telescope provable under the fragment (Dwidth₀ = 1 via
hDwidth + root clause) and `irr_iff_mu_one` exact; fiberAt clause (vi) is
well-formed (each chain lies over exactly ONE head by `hclosed` + head uniqueness;
(iii)+(vi) ⟹ (v) is real — simple + repeated factor degrees sum to n = deg f̄ —
so (v)'s derived status holds); `RedCellPartition` is satisfiable-and-faithful
(coverage + uniqueness over the reduction's own factors; second conjunct =
`child_cell_red`'s face); `TreeScaffold.hframe`'s `jointExp = siteExp` tie closes
Codex-3 #9; `rootSplit_exists` is constructible from `hfin`/`hclosed` alone (the `g`
parameter of `RootSplitData` is phantom — harmless, the g-tie enters via `hg`/`hfib`);
`CapIrrLaw`'s m'-quantifier is the family TREE-N consumes; `ClassTree`'s
`nsMark`/`rootV`/`hkeys` repair #15/#21; `SubtreeTransport` displayed; T-F3/wsh17/
capIrrOf/CapEnvelopeCellLocal binder slips all fixed (Fable-3 GAP-4). The sweep's
fresh yield is the one critical and one gap below.

---

## 2. CRITICAL finding (verified by construction against the built signatures)

**CRIT-1 · T-V8 (§2.2/§3): the `MatchesHist` LEG of `shapeOfH_matches` is refutable
— the built `ShapeRead.Matches` carries a 13th conjunct, the §0.5 MONIC-LEAD TIE
`R.monicTop = true → ν.sideDigit R.len = 1` (MovesD/Defs.lean 311–318: "the ONE
scoped monic tie (§0.5): `monicTop → sideDigit(ℓ_r) = 1`"; `Node.sideDigit ν k =
((ν.pat k : ↥ν.σ.K) : F)`, line 301) — and NO `HistLawful` clause constrains `pat`.**
The T-V8 sketch's warrant — "componentwise Matches is definitional (readOf copies
ν's fields; the w-card identity is the fragment's p-power clause …)" — is TRUE for
the eleven copied fields and the pool-card clause, and FALSE at exactly this
conjunct: `readOf` does not copy `pat`, and the REV-4 species guard makes `monicTop`
TRUE at every genuine monic root read (r = 0, s0 + wSide = n, root species — forced
by `History.root_iff`), which ARMS the tie. Counter-instance (same freedom class as
the record-#7 construction): p = 3, F = 𝔽₃, ONE-node H, root node with
σ.Φ.natDegree = 1 (⟹ Dwidth = 1 via `hDwidth`), card K = 3, e = 1, wSide = 2,
g = μ = 1 (gmu 1 ≤ 2 ✓), n := s0 + wSide (root-box EQUALITY — the monic slot),
slope/γ/anchor/line data chosen to satisfy the ties (all free), and the pattern top
digit `pat(wSide/e) := 2` — every Node proof field is satisfiable (`hpatTop` demands
only ≠ 0; `hOrd`/`hRanch` constrain Ranch's factorization, not the top digit's
VALUE; take Ranch = 2(z−c)(z−d), c ≠ d ≠ 0). Then `HistLawful p n H` HOLDS (chain
clauses vacuous at one node; every displayed clause checked), `readOf`'s monicTop
decides TRUE, and `Matches` demands sideDigit(2/1) = 2 = 1 — FALSE:
`(shapeOfH H n).MatchesHist H` fails, **T-V8 is FALSE as stated**, third round in a
row at this unit, at a third clause. Downstream: the L3-dictionary leg (thr(T),
TB-CAP(irr)'s shape reads, T-E11's `hthr` route through T-V8) rests on the broken
unit; `MatchesHist`'s other uses (`chainCount`, `PrefSet` filters) are definitional
and unaffected. The §2.2 hatch does not cover it: it is scoped to "any clause SW1b
needs beyond the §2.2 roster" (the ShapeWF leg), while the Matches leg is claimed
definitional — the same wrong-warrant channel Fable-3 CRIT-1 named. NOTE ALSO: the
real SW1's `hmt0` (ENC-MONIC, the monicTop ↔ s0+wSide = n iff) IS discharged by the
rev-4 `readOf` + `root_iff` — the "two SW1 side conditions" line checks out; the
hole is strictly the Matches DIGIT conjunct. FIX SHAPE (small, fence-compatible,
rev-3-CRIT-1-like): add the monic-lead normalization clause to `HistLawful` —
`∀ h0 : 0 < len, nodes[0].s0 + nodes[0].wSide = n → nodes[0].sideDigit
(nodes[0].wSide / nodes[0].e) = 1` — the L3 dictionary's §0.5 law (a monic box
member's degree-n slot digit IS 1), node-side DIGIT data, pinning no recentering/
lift/Bézout constant (keying-constant-free, Q1-insensitive); correct the T-V8 sketch
warrant; re-audit the Matches roster the way §2.2 re-audited ShapeWF's (13 conjuncts,
each named to its source — the other 12 check, verified this round). The gates would
NOT have caught this (an honest toy has pat_top = 1; gates catch over-strengthening,
not under-sourcing) — the roster re-audit is the only channel, which is why it must
cover BOTH conjuncts of the unit's conclusion.

## 3. GAP finding

**GAP-1 · T-G1: `toy_jcmulti_site`'s site does not exist on the PINNED toy design.**
The REV-4 pinned spec is one track (f̄ = x², one repeated factor), ONE depth-1 split
cell with two branches "each halting τ-irr at one read", census integers from the
single-window design (N(fiber) = 8 = 2^{9−6}, toyA = 6 — verified at MOVES
9208–9209). A single split site cannot be BOTH one-side (which `toy_state_cell`'s
tie instance needs, and which the F1-shaped census implies — "every SIB-gate cell …
is single-side", 7471–7472, and (JC-multi) is "census-untested (all gate cells are
single-side)", 7481–7482) AND "the toy's one multi-side site" that
`toy_jcmulti_site` names. As pinned, either the multi-side gate has no genuine
2-side hull to instantiate (an artificial `SideSplit` relabeling of a one-side
system would gate only the exponent bookkeeping, not record #2's multi-side
geometry), or — if "(z, z+1 sides)" is read as a genuine two-slope hull —
`toy_state_cell`'s one-side equality loses its site instead. Fix: extend the pinned
design (a second window shape with a genuine 2-side hull, with its own acceptance
integers) or pin a second toy carrier for the JC-multi gate, and say which gate
lives where. (The gate-ledger channel — the same §0 acceptance-record channel as
Fable-3 GAP-3; the OTHER two new gates are sound as specified.)

---

## 4. What checks out (recorded so the repairer does not re-litigate)

* Both round-3 criticals are repaired AS DESIGNED and verified at the built
  signatures: the w-mult clause is the wchain source and kills the record-#7
  instance; the Mlev cap restores fixed-level satisfiability with the falsifier
  honestly tower-scoped (and the ∃-jet adversary is disarmed by the accessors'
  pinned (H, N)-determined defining clauses + the built chart uniqueness —
  `coordOf_sorted`; worth a one-line bracket note at §2.4, not demanded).
* `IrrHalts` is the note's rule verbatim (7074–7080 re-read at source); the
  lawfulness conjunct is correctly REMOVED; T-V9 carries the parenthetical.
* fiberAt (vi) is the real per-track completeness face; (v) faithful AND derived;
  T-D2's clause-(vi) route is sound.
* The full 12-clause ShapeWF sourcing roster at §2.2 is CORRECT (each clause
  verified to its named source against the built ShapeWF/Node/History; `hmt0`/`hw0`
  are the real SW1 side conditions and both discharge). Only the Matches-leg
  conjunct (CRIT-1) is unsourced.
* The LedgerIV import is real and complete on both rows (W3 + W1m); `hxrbStmt` and
  the recursion conclusion re-verified verbatim against the built Interfaces.
* All §7 quotes are faithful; both PBs carry the note's/contract's own sentences and
  are substantively right; the BDY adjudication is honest and its fence claim is
  true at the built `ReadsOf`. Tally 21/5/2/1 = 29 exact.
* Census 55 = 14/31/10 exact; seam tally 1/4/12/2 = 19 row-faithful; §6 honesty
  block extended correctly (tower-scoped falsifier, w-mult fence growth, no τ-irr
  lawfulness conjunct).

## 5. Disposition

Rev 4 clears the complete round-3 union — the first revision of this artifact to
clear a full prior union — and both of its headline repairs survive adversarial
re-walking at the built signatures. The residue is ONE fresh critical, localized to
the single unit (T-V8) that has now failed three rounds at three different clauses
of its two-conjunct conclusion, each time behind a sourcing warrant asserted rather
than audited: rev 4 audited the ShapeWF conjunct's 12 clauses and left the Matches
conjunct's 13 unaudited. The fix is one added keying-constant-free HistLawful clause
(the §0.5 monic-lead digit law) + a warrant correction + a displayed Matches-roster
re-audit — plus the toy-design extension for GAP-1. REJECT (1 crit / 1 gap); a rev 5
addressing these two should re-audit clean.
