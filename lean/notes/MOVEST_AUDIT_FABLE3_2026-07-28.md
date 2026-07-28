# MovesT blueprint (REV 3) — fresh-instance FABLE audit (2026-07-28)

ARTIFACT: `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` REV 3 (2963 lines, read in
full; 55 units). GROUND TRUTH re-read at source: `MOVES_2026-07-24.md` §T-ASSEMBLY
rev 7 (6970–7761, in full); the seam contracts (MovesD blueprint §2.5 W4-1…W4-4
318–379; MovesS §W4-SYNC 1105–1346 incl. both addenda, the preamble, and the typed
package displays; HC2 blueprint Walls A/B/C 60–145 + the clause-(vi) sign-off note
1464–1480); the sealed integers (`verification/CASE_SIB_SEALED_PREDICTIONS.md` P1–P6);
and the CONSUMED LEAN SIGNATURES (`MovesC/Defs.lean`: `HistoryCoherent` 634–663 in
full, `Node` all fields incl. `hDwidth`/`hbezCanon`/`hAnchor`, `History` + `root_iff`
+ `strFrame`, `FreshData`/`LevelClause`, `Locus = DigitSystem m (ZMod p)`,
`C4_conditionalMass` verbatim; `MovesD/Defs.lean`: `ShapeRead` full roster incl. the
DERIVED `len`/`d`/`mbar`, `ShapeWF` ALL 12 clauses, `bezT`, `MatchesHist`, `TreeModel`
incl. `mem_realizable`, `D4R_CYL`, `ClassFiberWelldef`; `MovesD/SW1_shapeWF.lean`
`ShapeWF_of_matches` full signature; `MovesS/Interfaces.lean` `RS1Meas.βmeas` (ℝ-valued)
+ `RS1Bundle.xrb`/`recursion_meas`; `MovesSp/Defs.lean` `Species`/`Coherent`/`StageLaws`/
`RootStage`; `HC2/Defs.lean` `ReadsOf` at 283). History: rev 1 = Codex 35/10 + Fable
5/8; rev 2 = Codex 21/4 + Fable 3/4. I verify by computation and construction; I fix
nothing.

## VERDICT: **REJECT (2 crit / 4 gap)** — the entire round-2 union is genuinely
## repaired (the henV-flip dies on `hreal`; the seam map is contract-faithful with the
## S-3 reversal sound and typed over the real imported βmeas; the EntSt carrier reaches
## the F1 14-pin cell exactly at the sealed integers) — but the fresh sweep finds the
## two rev-3 REPAIR MECHANISMS themselves defective at the built signatures: the
## HistLawful roster cannot source ShapeWF.wchain (T-V8 false again, one clause over),
## and the (ns) slot-0 ladder is stated unbounded at a fixed finite level, which makes
## KBTot/VPPinned unsatisfiable-or-unfalsifiable (the Codex-2 #2 repair does not hold).

---

## 1. The charge's six items — results

### (1) The henV-flip adversary re-run against `hreal`: it DIES, on a hypothesis. ✓

Construction re-run: Tr' := the T-G1 toy tree with `henV := ∅` (lawful — `hhen`
vacuous on ∅). Under the rev-3 `fiberAt`: clause (v) demands
`(typemult.map (·.1*·.2)).sum = n`; Tr'.typemult loses the hen degree (sum 2 ≠ 3 = n
on the toy), so **fiberAt Tr' fails at EVERY x by type** — `Realizes T χ Tr'` is
false, and T-E5/E8/E11 now refuse the flip at `hreal` instead of concluding
0·2⁶ = 2⁹. Threading COMPLETE: `hreal` on E5/E8/E11, `Realizes` inside E10's
`shapeClass` domain, and inside the §2.10 ∀-closures `TreeExpFin`/`TreeNStmt` (the
package values are not flip-vulnerable). The regression gate
`toy_henflip_unrealizable` is specified surrogate+bridge. I also re-probed the t = 0
leak (Codex-2 #10): at an all-Hensel tree, `hrc` + `child_cell` make child
realization CELL-UNIFORM on the g-cell, so a single realized child would contradict
the `hreal` witness's clause (i) — the leak is genuinely closed by the stated
hypothesis set, not by luck. No remaining unit states a fiber-mass identity without
`hreal` (E13/F3 are additivity/covering — zero fibers harmless).

### (2) T-V8 / `HistLawful`: the fragment IS child-keying-free and the fence IS
### honest — but the roster canNOT source the real `ShapeWF` (CRIT-1).

Verified clause-by-clause against the REAL `HistoryCoherent` (MovesC/Defs.lean
634–663): HistLawful's root-degree/slope-tie/γ-tie ARE conjuncts 1–3 verbatim
(incl. `strFrame`); its chain clause is EXACTLY the 4th conjunct's non-keying trio
(window, Dwidth chain, slope increase); the omitted legs are exactly
`IsRecenteringCore`/`IsNodeLift`/`TransitionCoreL` + the `σ.s`/`σ.t` ties —
Q1-insensitivity as claimed. Fence sweep: NO unit premises `HistoryCoherent`
(`WallAReconciled` reaches it only inside the BUILT `HC2.ReadsOf`, spec-only ✓);
the §0 row now honestly DENIES the rev-2 implication claim ✓. `acc_pos`, T-V9's
`childWidth` warrant (`Node.childWidth = e·g·Dwidth`, a real def), and `dchain0`'s
source (root Φ-degree 1 + the real Node FIELD `hDwidth : Dwidth = σ.Φ.natDegree`)
all check. **But the real `ShapeWF` has 12 clauses, and one has no source — see
CRIT-1 (wchain).** Also the displayed gmu clause reads a nonexistent accessor
(`ν.len` — no such Node field or def exists; `len` is MovesD's DERIVED
`ShapeRead.len = wSide/e`), folded into CRIT-1.

### (3) The seam rows, one-by-one against the contract texts. ✓ (tally row-faithful)

* **S-3 REVERSED — SOUND.** The MovesS preamble sentences quoted in §2.10 are
  verbatim ("the contract MovesT/MovesV re-key when their vocabulary exists"; "The
  former file plan (`MovesS/Interfaces.lean`) is retired for these declarations"),
  and the S-3 demand row is quoted exactly. The imported type IS the contract one:
  the real `RS1Meas.βmeas : ∀ e, e ∈ Icc 1 n → ℕ → ∀ τ, Multiset VType → ℚ → ℝ`
  (Interfaces.lean ~35–43) — `hxrbStmt` is verbatim the real `RS1Bundle.xrb` field
  row, and `w3Rekeyed`'s conclusion is verbatim the real `recursion_meas` row incl.
  the `evalRe … (fun e' he' => βmeas e' he' h_ent)` callback shape and the
  `activeState` guard. Equality is in ℝ (βmeas is ℝ-valued — the blueprint never
  claims ℚ). Owner remainder honestly quoted. SUPPLIED is the right tag.
* **W4-4 DISCHARGED** — T-D7 = the contract's (a) verbatim (∀ i, ∀ J, level-set =
  bandLevels; no `S.jet` weakening), route = the contract's own (c). Fair.
* **S-9/S-1/S-2 SUPPLIED** — the package rosters match the contract structures
  field-for-field (XRBPackage 13 ✓, RS1GivenPackage 13 ✓, Wsh17Package 3 ✓;
  `RS1GivenHolds` = the contract's `RS1Given.holds` row ✓; `w1mObligation` carries
  the ledger slot bound to the real `LedgerIV` ✓); every [3t] field is a §2.10 def
  with a displayed body — EXCEPT the `pci` value's dependence on the undefined
  `SubtreeTransport` (GAP-1) and the `vp`/`tb_cap` values' satisfiability being
  poisoned by CRIT-2 (`VPPinned.covering : KBTot T` uninhabitable as typed).
* **S-6 PARTIAL** — `ReadLedgerT` matches the contract's `ReadLedger` roster
  verbatim (L/fe/hfe/charge/Wcharge/βcharge); `readLedgerOf_bdy` IS the contract's
  `W8_bdy` conjunction at the constructed value (both `Finset.Icc` splits exact);
  `chain_charge` telescopes to `rootCell χ g` via the `.red` entrance ✓; fe residual
  quoted with owner ✓.
* **Wall A REDUCED** — the pin now binds the BUILT `HC2.ReadsOf p F n (dec x)
  (H.snoc ν hν)` (signature verified at HC2/Defs.lean 283: monic + degree-n +
  HistoryCoherent + per-read development incl. clause (vi)); the residue
  {`dec`, canonical CA, instance proof} matches the HC2 blueprint's own Wall-A
  assignment. Wall B NOT-OURS with the SEED-EXIST quantifier trace verbatim ✓.
* **S-4 NOT-OURS; S-5/S-7/S-8/S-10/S-11 PARTIAL** — residuals quoted verbatim from
  the contract rows I re-read ✓.
* **Tally**: rows = 4+13+2+2 = 21; 19 seam entries; statuses re-counted from the
  rows: 1 DISCHARGED / 4 REDUCED / 12 SUPPLIED-or-PARTIAL / 2 NOT-OURS — the
  headline MATCHES its table (rev-2's GAP-1 fixed). ✓

### (4) The EntSt carrier vs the F1 14-pin cell: REACHED — computed exact. ✓

At es := `.red g ψ` (g = the 4-pin reduction {f̄ = x⁴}, ψ the repeated factor):
`entEvent = rootCell χ g` = 5^{22−4} = 5¹⁸ in B22, and `cellEventE` adds the 10
window pins through `cellOf (.red g ψ)` → 5^{22−14} = **390,625 = 5⁸ ✓** (seal P6's
Σ_c count). SibCount at this site (card 2, exponent card−1 = 1):
card(Σ_c ∩ S₁∩S₂)·card(Σ_c) = **15,625·390,625 = 5¹⁴ = 78,125² =**
∏ card(Σ_c ∩ Sᵢ) — the seal's P3 integers verbatim. JCmultiAt at the same site:
5⁸·5¹⁰ = 5¹⁸ = card(entEvent) ✓ (10 = the window mstar). Rev 2's unreachability is
CONFIRMED from the other side: `hrc`/`RootCellsOf` forces `.amb`-entrance cells to
be exactly the 4-pin reduction cells, and `.st H` entrances condition on states
AFTER the first window read — the 14-pin cell conditioned on Σ₀ had no carrier.
T-E5's F1 arithmetic re-verified (5⁶·5¹⁸·5⁴ = 5²⁸ = 5²²·5⁶) and T-E7's new (B)
conjunct is algebraically exact ((A)·C then ·p^j with hcharge substituted).

### (5) The decide gates. ✓ (architecture holds; one ledger overstatement → GAP-3)

Every `decide` sits on a finite surrogate with a hand bridge; no gate claims
`decide` over a `Set`/`History`/`EntSt` quantifier. `toy_sib`'s ∀-EntSt face is
classifiable: unrealized `.st H` entrances and junk `.red g ψ` entrances zero both
sides of the kernel (cellEventE ⊆ entEvent = ∅ ⟹ every factor 0), realized
entrances are the enumerated roster. `toy_henflip_unrealizable` is correctly
specified (the flip's fiber is empty BY TYPE, so the surrogate is decidable-per-x
and the bridge is over the finite box). `readOf`'s `decide` is a Bool value, fine.
BUT §0's claim "SIX refutation records … each has a Layer-G regression gate"
overstates: records 1/3/4 have gates (`toy_sib`, `toy_e5_instance`,
`toy_henflip_unrealizable`); records 2 (JCmulti), 5 (T-V8 premise), 6 (state↔cell)
have NONE (GAP-3).

### (6) Fresh sweep of the 55 units.

Census re-counted: 55 = 9V+8C+3S+13E+5F+15D+2G ✓; 14 easy / 31 medium / 10 hard
re-tallied from the units EXACT ✓; hard list matches ✓. §7 disposition table:
32 = 21 F + 11 R + 0 PB re-counted from the rows EXACT ✓; spot-verified rows all
check EXCEPT Codex-2 #2's "R" (the falsifier claim is defective — CRIT-2 below).
Verified sound this round (recorded so the repairer does not re-litigate): clause
(v) is faithful to (TGT)/VP-1's typing (7014–7020, 7061–7063 — complete trees
carry Σ E·F = n); T-E9's proof is sound and its conclusion IS `VTree.ext`; the
`VTree.ext` equivalence-relation argument via `hleaf`/`hns_leaf` is correct;
T-D2's `rootOnly_childless_rejected` genuinely rejects the degeneracy through
clause (v) (normalizedFactors degree accounting); T-V3's Species-roster claim is
exact (no cluster-degree field: tag/D/w/W/e/s0/ell/a/d/slots/lam/sel/flanks) and
T-V4/T-V9's warrants are the real `StageLaws` (D′ = e·g·D, W′ = μ) and `Coherent`
(G6) rows; `C4_conditionalMass`'s quote is its verbatim signature incl. `hfree`;
CapIrrLaw/`tbcap_irr_family` deliver the cross-level cap per the W4-2 addendum;
T-D5/D6 carried sound; T-F2's `hph`+`hsep` close the bijection legs. The two
criticals and four gaps below are the sweep's yield.

---

## 2. CRITICAL findings (both verified by construction against built signatures)

**CRIT-1 · T-V8 (§2.2 `HistLawful`): the displayed roster cannot source the real
`ShapeWF.wchain` — the sourcing claim is FALSE and the unit is refutable; also the
displayed gmu clause does not elaborate.**
The real `ShapeWF` (MovesD/Defs.lean) contains
`wchain : ∀ r, reads[r+1].w = reads[r].w * reads[r].g` — the residue-degree chain
w_{r+1} = w_r·g_r. Its node-side content (card K_{i+1} = card K_i^{g_i}, the field
growth F_{i+1} = F_i[z]/(ψ_i)) lives in exactly the 4th-conjunct KEYING legs
(`TransitionCoreL`) that `HistLawful` omits; NO displayed HistLawful clause
constrains consecutive K-cards. Counter-instance (same freedom class as the §0
record-#5 construction, one field re-chosen): F := 𝔽_{p²}; two-node H with
card K₀ = p (w₀ = 1 ✓), card K₁ = p² (a p-power — NodeDataLawful ✓), g₀ = 1;
window/Dwidth-chain/slope-increase/slope-tie/γ-tie/anchor clauses all satisfiable
(nodes are independent list entries; Fable-2 CRIT-2's record already established
two-node constructibility). Then `shapeOfH` has w₁ = 2 ≠ 1 = w₀·g₀ —
`ShapeWF n (shapeOfH H n)` FAILS `wchain` while `HistLawful p n H` HOLDS: T-V8 is
FALSE as stated, and the queued MovesD companion `SW1b ShapeWF_of_lawful` cannot
exist at the displayed roster. The §2.2 docstring's claim — "strong enough to
source the REAL ShapeWF (all clauses: dchain/window/gamTie/anchorTie/edvd/gmu/w0/
**wchain**)", with the sketch's warrant "wchain ← w-multiplicativity through
MatchesHist + the K-card p-powers" — is wrong: p-powers give each w_r SOME
exponent, never the chain law. SECONDARY (same unit): HistLawful's displayed gmu
clause reads `(H.nodes[i]).len`, but NO `len` field or def exists on the real
`Node` (`len` is MovesD's derived `ShapeRead.len = wSide/e`) — the display does not
elaborate; the intended node-side form is `g·μ ≤ wSide/e`. The E-phase deviation
hatch ("any clause SW1b needs beyond the §2.2 roster is ADDED … with a MANIFEST
deviation") anticipates additions, but the roster is declared NORMATIVE and the
strength claim is the thing rev 2 was rejected for at this exact unit. FIX SHAPE:
add the w-multiplicativity clause (card K_{i+1} = card K_i ^ g_i, or the
factorization form) to `HistLawful` — it pins no recentering/lift/Bézout constant,
so it stays child-keying-free and Q1-insensitive — and restate gmu on
`ν.wSide / ν.e`; then re-audit the roster against ALL 12 real clauses (species_iff
is `History.root_iff`'s, monic is `readOf`-definitional, dchain0 comes from
`Node.hDwidth` + root degree 1 — those three check).

**CRIT-2 · §2.5a/§2.4/T-C5: the slot-0 ladder is quantified over UNBOUNDED M at a
FIXED finite level — `NsLumpFamily.slot0`/`ZCPack.slot0_grid` are unsatisfiable at
faithful bindings (or the KBTot falsifier is false at junk bindings), and T-C5's
conclusion is refutable by cardinality.**
`Locus p m = DigitSystem m (ZMod p)` pins per-coordinate (`pinned : Fin m → Bool`),
so ANY admissible Z has pinCount ≤ m. T-C5 asserts, for every M ≥ M₀ at a FIXED
level (n, N, m are bound by J), `∃ Z, … ∧ M − M₀ ≤ pinCount Z` — FALSE at
M := M₀ + m + 1 whenever `ZCPack J` is satisfiable. And `ZCPack.slot0_grid`
(∀ ht ≥ M₀ an interior block at height ht, one per height) needs unboundedly many
distinct blocks, i.e. unboundedly many real coordinates — unsatisfiable at any
faithful binding to MovesC's finite-level chart (the jet's fresh apparatus is
`Fin m`-indexed: `mstar_eq` counts `{c : Fin m // inFreshBand …}`). The same ∀-M
ladder is a FIELD of `NsLumpFamily` (`slot0`), so at faithful bindings NO
`NsLumpFamily` exists at any fixed level — `KBTot.ns_lumps` (∃ J, Nonempty
(NsLumpFamily T J) at every realized state) is unsatisfiable for EVERY model, not
just the degenerate one: `hdi : KBTot T` becomes an uninstantiable premise (T-V6/
T-D3 vacuous), and `VPPinned` — whose `covering : KBTot T` is a structure field —
is UNINHABITABLE, poisoning the §2.10 package values `vp` (and `tb_cap`'s VP
conjunct) that S-1/S-2/S-9 hand to MovesS. Alternatively, if the E-phase binds
`interiorFreshIdx` to a junk-padded index type (digitAt ≡ 0 beyond the level) to
make slot0 satisfiable, then the §2.4 FALSIFIER claim — "a model with mem
everywhere and child nowhere … `ns_lumps` FAILS on it" — is FALSE: the full-box
junk family (L M := univ, junk blocks only) satisfies `vanish`/`interior_mono`/
`tie`/`slot0`, readmitting exactly the childless degeneracy Codex-2 #2 named. The
note's own display is PROFINITE (all heights exist, 7216–7231); the finite-level
transcription needs the level cap the corpus already defines for T-C7:
`M ≤ Mlev J N` (Scale cap). FIX SHAPE: cap the ladder clauses by `Mlev` (T-C5's
premise row, `slot0`, `slot0_grid`); restate the KBTot falsifier ALONG TOWERS
(where `hMgrow` forces Mlev − M₀ → ∞) rather than at one level; re-check T-C7's
consumption (it already instantiates at M = Mlev — it survives the capped forms).

---

## 3. GAP findings

**GAP-1 · `PCI` consumes the never-defined `SubtreeTransport`** (§2.6 line ~876 —
its ONLY occurrence in the artifact; not even bracket-defined). PCI's value is the
`pci` field of `rs1GivenOfMovesT` (S-9, a SUPPLIED row), so an undisplayed
load-bearing name sits inside a §2.10-consumed field value — the exact Codex-2 #23
class, and NOT in §7 #23's disclosed-residual list (which names only
`ClusterFactorOf`/`UnramifiedOfDeg`, both consumed by nothing). Display the
transport clause (same-prescribed-subtree at the two entrances) or move `pci` to a
parameter with an owner tag.

**GAP-2 · `readOf` as displayed is not definable as a total function** — the real
`ShapeRead` carries proof fields the displayed values cannot discharge on junk
nodes: `hw : 1 ≤ w` fails when `Nat.card ↥ν.σ.K` is not a p-power (no `CharP F p`
constraint exists in the binders), and `hmonicRoot : monicTop = true → species =
root` fails for junk (ν, r = 0) with s0+wSide = n and species ≠ root. The needed
junk-guards (e.g. `w := max … 1`, a species conjunct in monicTop) change the value
spec that `MatchesHist`/T-V8 consume — they must be displayed with their
dead-on-the-lawful-domain proofs, not left to the E-phase roster note.

**GAP-3 · §0's "each has a Layer-G regression gate" overstates** — records 2
(JCmulti free-Σc), 5 (T-V8 premise), 6 (E6 state↔cell) have no gate in Layers G;
only records 1/3/4 do. Either add gates (a V8-roster gate and a state_cell toy
instance are cheap) or restate the ledger line. (The acceptance-record channel —
the exact channel rev 1 and rev 2 were each dinged on.)

**GAP-4 · Elaboration-order/binding slips in displayed statements** (all trivially
E-phase-fixable, listed for the record): T-F3 binds `hsep` referencing `𝒯` BEFORE
`𝒯`'s binder; `wsh17OfMovesT` uses an unbound `χ` (not among its parameters or the
standing binders); `capIrrOf` binds an unused `{P : Shape n}`;
`capEnvelope_cellLocal_false`'s target `CapEnvelopeCellLocal` is undisplayed
(falsifier-only — weakest case, flag it as pointer-pinned like `CapIrrLaw` was).

---

## 4. What checks out (recorded so the repairer does not re-litigate)

* All three round-2 criticals are genuinely repaired AS DESIGNED: the henV-flip
  fails `hreal` (with the t = 0 leak closed by cell-uniformity of child
  realization); `HistLawful` is verbatim-faithful to HistoryCoherent's conjuncts
  1–3 + the non-keying trio, keying legs omitted, fence total, §0 row honest;
  `state_cell` is a one-side-scoped ledger FIELD that kills the two-branch-set
  counter-instance, with the multi-side face correctly routed through E7's
  `hdecomp`, and the Q2 placement per §4 is fence-compatible.
* The S-3 pushback reversal is sound and COMPLETE: contract sentences verbatim,
  types verbatim against the built `RS1Meas`/`RS1Bundle`/`evalRe` (ℝ-valued βmeas,
  activity guard, callback shape), status honesty right.
* The seam tally is row-faithful for the first time in three revisions; the
  package rosters, `ReadLedger`, and `W8_bdy` are the contract's own texts.
* The F1 14-pin site is reachable by the rev-3 kernel and the sealed P3/P6
  integers instantiate it exactly; the p = 2 census instantiates E5/E8 exactly.
* The disposition table's arithmetic (32 = 21+11+0) and all spot-checked rows
  except Codex-2 #2 are truthful; census 55 = 14/31/10 exact.

## 5. Disposition

Rev 3 clears the entire round-2 union — including the two structural channels
(seam accounting, E-layer model ties) that survived two revisions — and the seam
map is now the campaign's most contract-faithful artifact. Both fresh criticals
are localized to the two NEW rev-3 mechanisms and have small, fence-compatible fix
shapes: one added (still keying-free) HistLawful clause + a gmu accessor fix
(CRIT-1), and a level-cap on three ladder clauses + a tower-form falsifier
(CRIT-2). Neither requires touching the seam map, the EntSt carrier, `hreal`
threading, or any contract row. REJECT (2 crit / 4 gap); a rev 4 addressing these
plus the four gaps should re-audit clean.
