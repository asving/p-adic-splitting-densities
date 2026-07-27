# HC-2 blueprint REV 2 — fresh-instance re-audit / ACCEPTANCE PASS (Fable, 2026-07-28)

ARTIFACT: `lean/notes/HC2_LEAN_BLUEPRINT_2026-07-28.md` (rev 2, 1241 lines, 48 units), read in full.
CHARGE: the acceptance pass on the rev-1 REJECT (1 crit / 7 gap, `HC2_AUDIT_FABLE_2026-07-28.md`);
perimeter = §3 + the seven gap sites + the two inline ratification records, plus a fresh sweep of
all 48 units + doctrine. Ground truths actually read this pass: `Moves/Defs.lean` (full — the
`Stage` structure line-by-line), `Moves/DefsCore.lean` (StageCore 196–208, TransitionCore,
IsRecenteringCore 242), `Moves/DefsL.lean` (full — StageCoreL 186–189, TransitionCoreL 198–207,
LandingCylinderL 247–259, the header's "single remaining boundary"), `Moves/DefsT.lean`
(TransitionData 147–), `Moves/L3_liftExists.lean` (statement line), `MovesC/Defs.lean` (honest
boundary 195–202; IsNodeLift 535–543; LandingKey 552–557; JetSetup 792– with recursion 872 /
inh_implied 876; FreshData 317–319) + `MovesC/MANIFEST.json` (36 units) + the 36-file roster,
`MOVESD_LEAN_BLUEPRINT_2026-07-28.md` (rows 306/308/309/311, W4-1 326–335, W4-4 362, PresentNorm
675), `GMN_citations.md` (Thm 2.11/2.26/3.1/3.7/Cor 1.20/3.8 pins; (P4b) at 338, verified-verbatim
flag), `MOVES_2026-07-24.md` lines 2446–2449 (offset-P construction), 2583–2596 (D.10 lift clause),
4678 (the §D4-R F1 "simultaneously eligible" record), the rev-1 audit file in full, and the FULL
git diff rev 1 → rev 2 (`35bf18a` → `05ea66f`, 588+/293−). I fix nothing.

---

## Charge item (1) — the P-1 no-declaration analysis: **CONFIRMED against Lean ground truth**

* The blueprint's ledger inventory is EXACT. `Stage p F` (`Moves/Defs.lean` 106–182) carries as
  FIELDS: `hRadd`/`hRlt` (exact graded-map additivity/domination, 149–151), `hRΦ : R Φ = T s`
  (153), `he1t` (P2, 121), `hS5` (forced positions, 157–159), `hStretch` (144), `reps`/`hreps`/
  `Tvec`/`hTvec` (162–167), `hS6a`/`hS6b` exactness (174–182). `StageCoreL` (`DefsL` 186–189) =
  `StageCore` (tie laws `w_strict`/`w_jump`/`R_neg`, `TvecLaw`, `prevIaug`, `SlotDecomp`,
  `CoeffFieldLawCore` — `DefsCore` 196–208) + `TvecUnitLaw` + `CoeffLocLaw`. `TransitionCoreL`
  wraps `TransitionData σ σ' …` (`DefsT` 147), which is parameterized over the CHILD `Stage` —
  so the blueprint's key sentence ("ANY conclusion that so much as MENTIONS a `Stage` value
  smuggles the ledger") is literally true of the Lean ground truth. The DefsL header's
  "single remaining boundary" quote is verbatim (DefsL 66–69).
* The reduced skeleton is genuinely ledger-free: `w'`/`K'`/`R'` are bare data; the residual
  conjunct is up-to-unit at the POLYNOMIAL level (`R' : Polynomial ℤ_[p] → Polynomial ↥K'`,
  `∃ c : (↥K')ˣ, R'(fg) = c • (R' f · R' g)`) — matching GMN's ∼-forms as pinned in
  `GMN_citations.md` (Thm 2.26 / Thm 3.7, "∼" throughout); `IsSlotMinWeight`/`K1At` are
  Stage-free defs (`Moves/Defs.lean` 235/83). The Bézout window is gone from the axiom and
  present only in `StageTransHyp` — the right side of the selection/import line.
* The consumer analysis is correct: U17a/history construction must build `Node` values (full
  `Stage` inside) and supply `TransitionCoreL`/`StageCoreL` legs; the reduced conclusion can
  populate none of that. DEFAULT = NO DECLARATION is therefore not a stylistic retreat but the
  logically forced disposition — the third false-axiom catch converted into structure.
* The factored contingency's trigger is well-formed: `StageLedgerHyp` is a conditional
  (skeleton → lawful stage), so "StageLedgerHyp proved, skeleton existence stalled" is a
  coherent, precisely named state, and §7.4 scopes the gate chain to exactly it.
* `AxChk` discipline: exactly ONE `axiom` code display in the file — §3's P-1-REDUCED block,
  headed "PROPOSAL … (NOT DECLARED; contingency only)". Nothing declarable escapes the fence.

## Charge item (2) — hypothesis discipline: **CONFIRMED**

`StageTransHyp` (typed at §3, conclusion = the full `∃ σ'` with ties + `TransitionCoreL` +
`StageCoreL`, `hlift` keyed by `IsReadLift`), `OmUniqHyp` (typed at §3, verbatim U18/PresentNorm
(ii)), and SEED-EXIST (Wall B) are the ONLY supplier surfaces named in unit `hypothesis_fields`:
U15/U16 carry `hseed`+`hnorm`, U17a carries `StageTransHyp`, U18/U26 carry `OmUniqHyp`-on-failure.
The Wall-B and U15 displays of SEED-EXIST are byte-identical (the GAP-5 two-display drift is
gone). No unit spec contains an `axiom` keyword; U27/U30/U31 are explicitly axiom- and seed-free.
The MovesD consumer rows match: PRESENT-EXIST (MOVESD 309, sole consumer TW ✓ = U16), PresentNorm
(306/675 ✓ = U17/U18), POL-PIN (311 ✓ = D2/U24/U25 with the §7.6-registered sign-off copy).

## Charge item (3) — D8 `IsReadLift` + U1b vs the F10 conflation: **CONFIRMED**

Byte-compared: D8's `IsReadLift σ ψ g e' h' Φhat` is the literal `IsNodeLift` formula
(`MovesC/Defs.lean` 535–543) with `(ν.ψ, ν.g, ν.e, ν.h)` abstracted to `(ψ, g, e', h')` — same
current-valuation weights `σ.w (t_k) = h'·(g−k)`, same positions `−σ.t·σ.wPrev(t_k)`, same
assembly `Φ^{e'g} + Σ t_k Φ^{e'k}`; `isNodeLift_iff` is definitional as claimed. `IsStandardLift`
(`Moves/Defs.lean` 214–224) is genuinely differently keyed (`σ.wPrev (t_k) = σ.h·(g−k)`), and
`L3_liftExists` is stage-pair keyed WITH a threshold hypothesis
(`hthr : ∀ k < g, σ.wPrev σ.Φ < σ.h·(g−k)`) — which confirms U1b's NAMED RISK is real, not
hypothetical: the read-pair realizers must come from (S6b) at the node's scale, and the D.5
side-condition fallback is the honest fence. Both `StageTransHyp` and P-1-reduced key `hlift`
by `IsReadLift`; the re-keying-needs-guardian sentence is on record. GAP-1 discharged.

## Charge item (4) — U31 `gate_readsOf_inert2`: **CONFIRMED as a genuine anchor**, one wrinkle

U31 proves `ReadsOf 2 F 2 f H₀` by explicit development witness on concrete order-0 data,
axiom- and seed-free, scheduled in the first E-phase block with U27/U30 — an over-strengthened
`SideReads` transcription now fails at day one instead of silently vacuating U19–U24 and the
W4-1 seam. This is the realF2-gate pattern applied to the run predicate; GAP-4 discharged.
THE WRINKLE (the one counted finding, GAP-A below): D4's displayed signature
`SideReads (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)` cannot host clause (iv), whose
normative text references `H` and `i` (`LandingKey (H.nodes[i]) (nextKeyOf H i)`; the recorded
child key is node-(i+1) data, not a field of ν).

## Charge item (5) — `PresentSeed` pruning vs MovesC's deferred fields: **CONFIRMED**

* `JetSetup` (round 6) has exactly **29 fields** (counted field-by-field at Defs 792–) — the
  GAP-7(i) correction is right.
* The honest boundary (Defs 195–202) defers: presentation spine, K1-height reading, graded
  piece maps, (ZC) persistence. The pruned seed carries exactly `pres`(+zero/total/theta/block),
  `Theta`(+uni — marked DEFERRED in JetSetup's own docstring), `typObj`, `zcSeed` — and the (ZC)
  persistence is honestly SPLIT (U9/U10 provable side vs `zcSeed`, the declared
  seam-of-least-knowledge with the fence and the standing E-phase line-check).
* The moved-out fields are genuinely provable-or-parameter: chart → D1 `boxChart` (+2 lemmas,
  n=0 junk-guard); `keys` → parameter with `KeysLawful` whose two clauses are byte-identical to
  `JetSetup.keys_mid`/`landing`, proved by U1 (final read via U1b); `hm` eliminated by
  `m := n * N`; `hN` a U13 hypothesis. Minimality claim now true. GAP-5 discharged; the
  reprOf-form SEED-EXIST recorded as HC-1's deliverable, once.

## Charge item (6) — the ratified rulings: **CONFIRMED recorded correctly**

RULING 1 (§2.1 stratum := fresh): the rev-2 inline record reproduces the rev-1 ruling faithfully
(872–877 line cite correct — `recursion` at 872, `inh_implied` at 876; stronger-than-note law;
residue carried by U9/U10 + U27/U28; falsifiability via U6/U9/U10; U8 stays `Iff.rfl`).
RULING 2 (D2 polOM): recorded with the GAP-6 condition, and the condition IS discharged per the
ruling's own disjunct ("re-worded … or a sign-off recorded"): the D2 paragraph is the sign-off
(polOM = the (S6b′) offset-P policy, spec-realized), §7.6 registers the wave-4 copy into MovesD's
row. `RecenterLiftSpec` re-verified verbatim against LandingKey's recentering conjuncts (552–556)
and D.10's lift clause (MOVES 2593–2594, quoted exactly); the offset-P construction cite
(MOVES 2446–2449) checks.

## Charge item (7) — fresh 48-unit sweep + doctrine: **CLEAN**

* Census arithmetic exact: D1–D8 (8) + U1,U1b,U2–U8 (9) + U9a–c (3) + U10a–d (4) +
  U11,U13–U16 (5) + U17a,U17b-1..3,U17c (5) + U18 (1) + U19–U26 (8) + U27–U31 (5) = 48;
  easy 12 / medium 20 / hard 16 sums and matches the per-unit tags (U14/U20 "medium-hard"
  rounded to medium — consistent with rev 1's counting convention). Escalation-risk set
  unchanged and correctly re-declared.
* All named Lean dependencies exist on disk: MovesC 36/36 (incl. `C1_stripClause`,
  `C1_TYP_toClause`, `C6_thmC_a/b`, `C2_freshFree`, `C3_lineDom`, `C0_pinTransport`),
  Moves `L3_liftExists`, `L5_recLiftIndep_R4`, `L5_landVertexDigit(_repair)`,
  `L5_landTransport_R4`; `FreshData.disj` matches U2's statement; U5 "verbatim field type"
  claim checks against `fresh_assembled`; U7/U8/U9/U11 statements byte-consistent with
  `recursion`/`inh_implied`/`zc`/`root_height`; U21's vertex unit matches `LandingCylinderL`
  (DefsL 247–259) literally.
* The rev-1→rev-2 git diff is CONFINED to the declared perimeter: §3 rebuild/tombstones, the
  D8/U1b/U31 additions, the GAP-5 ripple (`S.coordOf` → `boxChart n N` in U3/U6/U9/U10; U13/U15
  re-signatures), U17a/U18/U26 hypothesis renames, U27's seed-construction rewording, the two
  ruling records, §8. No unit statement outside the perimeter was silently touched.
* Doctrine: falsifiability displays retained (§2.1 wave-3 check; U22's F-EMPTY citation duty;
  the hbr-drop probe as PERMANENT standing falsifier — its F1 basis re-verified at MOVES 4678);
  no stale references to the deleted seed fields; the phantom U12′ recorded-deleted and indeed
  never counted.

---

## Findings

### GAP-A (counted) — D4: `SideReads`' displayed signature cannot host its own clause (iv)

D4 displays `def SideReads … (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) : Prop := …`
"kept a separate def so U20–U22 can consume its conjuncts by name", but the normative clause
list's (iv) DESCENT WITNESS reads *"the landing key is realized: `LandingKey (H.nodes[i])
(nextKeyOf H i)` where `nextKeyOf H i` := the recorded child frame key (i+1 < len) or the
designated final key"* — data (`H`, `i`, the child key) not available from `(ν, B, Nd)`. The
E-phase transcription must either widen the signature (add the next-key parameter, or `H`/`i`)
or hoist (iv) into `ReadsOf`'s per-read bundle — and this choice affects which conjuncts U20–U22
vs U19 consume by name. Non-blocking: the body is already declared an E-phase transcription duty,
and U31/U19 force day-one detection at elaboration. Demand: a one-line signature disposition in
the E-phase Defs elaboration, recorded against this finding. **GAP** (spec display, one def).

### Remarks (not counted; no action required beyond noting)

* R-1: §7.3(v)'s "no unit names P-1/P-2/P-3" is slightly overstated — U17a's hypothesis_fields
  parenthetical and U1b's consumers line mention "the P-1-reduced contingency" as a DISCHARGE
  ROUTE. The discipline itself holds (the fields name `StageTransHyp`/`OmUniqHyp` only;
  consumer-invisibility is intact); the sentence should say "no unit CONSUMES P-1/P-2/P-3".
* R-2: `StageLedgerHyp` is prose-only, and its "with the tie fields" must be read as including
  the `(s', t')` window pinning (`σ'.s = s' ∧ σ'.t = t'`, and `hRΦ` at the given `s'`) for the
  displayed factoring `StageTransHyp ⇐ P-1-reduced + StageLedgerHyp` to typecheck — the
  skeleton carries no window data. HC-1-owned; record the window as an explicit input when
  StageLedgerHyp is first typed.
* R-3 (standing, for the contingency only): the SAYS-NO-LESS slogan "stronger hypotheses only
  weaken an axiom" is pure logic within a fixed conclusion, but if P-1-reduced is ever declared,
  the guardian must still rule on the HYPOTHESIS-side correspondence — that a `Stage`+`StageCoreL`
  datum is (or transports to) a genuine GMN order-r type, the DefsL-header boundary. Moot under
  the default (no declaration); named here so the §7.4 gate chain inherits it explicitly.

---

## Counts and verdict

CRITICAL: 0. GAP: 1 (GAP-A). Remarks: 3 (R-1..R-3, non-counted).

**ACCEPT (0 crit / 1 gap).** The rev-1 rejection's entire perimeter is discharged and verified
against Lean ground truth: the stage-minus-ledger analysis is exactly right (every claimed ledger
field exists on the `Stage`/`StageCoreL`/`TransitionCoreL` chain as claimed; the smuggling
conclusion is forced by `TransitionData`'s child-Stage parameter), DEFAULT = NO DECLARATION is
the honest and logically compelled disposition with a well-formed contingency trigger; P-2/P-3
tombstones are accurate (incl. the Fact-A provability and the (P4b) citation-direction points);
consumers are typed on named hypotheses throughout; D8/U1b resolve the F10 keying with a
definitional bridge verified byte-level; U31 genuinely anchors the W4-1 seam at order 0;
PresentSeed is now minimal against the 29-field ground truth; both rulings are recorded
faithfully with RULING 2's condition discharged. GAP-A is bookkeeping-grade, self-detecting at
E-phase, inside an already-fenced surface — it does not touch the axiom surface or any
load-bearing resolution. Proceed to the A-round / E-phase per §7.1, carrying GAP-A's signature
disposition and the two standing obligations (ZCSeedLaws line-check; R-3) into the E-phase audit
round. Codex final-confirmation leg remains batched post-reset per §7.5.

— Fable, fresh instance, acceptance pass, 2026-07-28. I fixed nothing.
