# MovesSp blueprint REV 3 — fresh-Fable CONFIRMATION audit (Fable #2)

DATE: 2026-07-28 · AUDITOR: fresh Fable instance #2 (no prior contact with this
corpus; confirmation pass on the identical rev-3 text Codex audits in parallel)
SCOPE: rev 3 of `MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` (1314 lines, read in full)
against the frozen §M-SPECIES text (`MOVES_2026-07-24.md` 5857–6782) + the
ERRATUM RECORD at file end, per the checklist of
`CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, INCLUDING: independent re-derivation of
every pinned-list decide target's order from catalogue3's definition;
independent re-verification of the §9 erratum; the three-member rosters;
collapseRuns/destutter semantics; the retargeted group-F fence; decidability
as typed for every decide unit; 6+ random unit spot-checks; fresh sweep.
Moves.HasAnchorK / Moves.Stage signature reuse: previously verified, no NEW
Moves names cited (checked) — not re-audited.

## VERDICT

**ACCEPT** — 0 critical / 0 gap. Two non-blocking NOTES recorded at the end
(below the charge's gap bar; reasoning displayed). Erratum: **CONCUR**.

## 1. catalogue3 order re-derived + EVERY pinned-list decide target checked

catalogue3 := groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI (§4), matching
SP.6's display order "GROUP R … GROUP Q3 … GROUP Q2 … GROUP Q1 … GROUP I".
List.filter preserves order; Nodup (n3card53) pins one occurrence each.

- **loops3** target `[loopQ3, loopQ23]`: re-derived the self-loop set from
  SuccStep — a self-loop needs StageLaws s s, i.e. D = e·g·D (⇒ e·g = 1 given
  WellTyped), W = μ, and tag = postRec forced by the tag-iffs; exhaustively
  over the 53: groupQ3's sole sel=(1,3) row (R6's "{(1,3)}▸(1,3)" — the only
  λ with a (1,3) part, since Σgμ = ℓ ≤ 3) and groupQ2's Q2.3 "▸(1,2)" row;
  all other rows fail on μ ≠ W or e·g ≥ 2 or sel = ⊥. Note: "exactly two loop
  classes at n = 3, both POST-REC". Q3-block precedes Q2-block in catalogue3
  ⇒ filter yields loopQ3 FIRST. Target order CORRECT (rev-3 C1 fix confirmed).
- **terminal3** target `groupQ1 ++ groupI`: W = 1 exactly on Q1 (stage (1,1,1))
  and I (4 letters); R/Q3/Q2 have W = 3/3/2. filter(cat3) = filter(Q1) ++
  filter(I) = groupQ1 ++ groupI (all pass, prior groups all fail). CORRECT.
- **fieldSizeExcluded2/3**: bodies are def-only; the §4 ORDER DISCIPLINE rule
  ("groups R → Q3 → Q2 → Q1 → I, within a group in the displayed row order")
  is the normative pin, and §4 declares them "in catalogue3 order". CONTENT
  re-derived independently: linCount ≥ 2 ⟺ λ ∈ {{(1,1)²}, {(1,2),(1,1)},
  {(1,1)³}} ⇒ letters R4/R5/Q3(R4)/Q3(R5)/Q2.3 (5) + R6▸(1,2)/R6▸(1,1)/both
  Q3(R6) copies (4) + R6/Q3(R6) {(1,1)³} (2) = 11 ✓ = the note's list;
  linCount ≥ 3 ⟺ {(1,1)³} = 2 ✓. Multiset multiplicity = number of DISTINCT
  factors of that shape ((1,2) is ONE distinct linear), so linCount faithfully
  implements "distinct nonzero roots demanded". A rule-violating def fails the
  decide LOUDLY (unprovable), never silently. CORRECT.
- **entrance filters**: the one pinned-list target,
  `groupR.filter (sel == some (1,2)) = [rootR4sel12, rootR5sel12, rootR6sel12]`
  — see §3 below; R4 < R5 < R6 in displayed row order. CORRECT. All remaining
  entrance conjuncts are `.all`/`.length`/membership forms — order-free ✓.
  §4's audit list of pinned-list targets is COMPLETE (I found no sixth
  `filter … = literal-list` target in any unit).

## 2. The erratum (§9) — INDEPENDENT re-verification: CONCUR

Note display (SP.6): "into the μ=2 block: root▸(1,2) [R4/R5 rows], or
root▸(1,3)·(Q3-loop)^d·▸(1,2)". The note's OWN R6 row: "{(1,2),(1,1)}▸(1,2)
and ▸(1,1)" — a ROOT letter with designated selection (1,2). The menu law
"▸(1,2) → Q2 letters" keys on the SELECTION only (SP.4's SUCC clause tests
stage fields D′ = e·g·D, w′ = g·w, W′ = μ, tag — no λ beyond the selection),
so R6's ▸(1,2) row's continuing branch lands in the child window [0,2] = the
μ=2 block, with the SAME stage laws as R4/R5's rows (all e = 1, g = 1, μ = 2).
Devil's-advocate check: nothing in the entrance definition (SP.4: last letter
= block-entry read "whose designated continuing branch enters the size-e
block") distinguishes R6's row — no e-difference, no λ-clause. The bracket
"[R4/R5 rows]" omits R6's row; the head clause "root▸(1,2)" is correct. The
loop-exit tail's Q3 mirror likewise has THREE ▸(1,2) rows. This matches §9's
three cross-checks and the note-end ERRATUM RECORD ("Corrected reading: [the
▸(1,2) rows of R4/R5/R6] … this record governs") verbatim. **CONCUR** — and
confirmed the blueprint bakes the erratum into NO target silently: unit
Sp.n3entrancePatterns pins the TRUE roster and cites §9 explicitly.

## 3. The three-member rosters — re-derived from the note's rows

Rows of R carrying ▸(1,2): needs (1,2) ∈ λ ⇒ λ = {(1,2)} (ℓ = 2: R4 a=0,
R5 a=1) or λ = {(1,2),(1,1)} (ℓ = 3: R6); R1–R3 (λ={(1,1)}), R7/R8 (ℓ=1)
carry none. Exactly THREE root ▸(1,2) letters, in groupR order R4 < R5 < R6 ⇒
`[rootR4sel12, rootR5sel12, rootR6sel12]` ✓. groupQ3 = the same 21 rows
retagged ⇒ its ▸(1,2) filter has length 3 ✓. Both targets CORRECT.
Loop-path witnesses re-checked as stage-law computations: rootR6sel13 → loopQ3
(D′=1, w′=1, W′=3, postRec ✓), loopQ3 → loopQ3 ✓, loopQ3 → each Q3 ▸(1,2) row
(targets at stage (1,1,3) ✓).

## 4. collapseRuns vs the note's collapsed-run semantics — MATCH

§2's defining equations remove adjacent EQUAL letters keeping one per maximal
run; Mathlib's `List.destutter (· ≠ ·)` does exactly this ("[2, 2, 3, 3, 2].
destutter (≠) = [2, 3, 2]", Mathlib Destutter.lean docstring) — for runs of
EQUAL elements first-of-run vs last-of-run is the same value, so the two
functions agree; the §2 "= List.destutter (· ≠ ·)" identity holds. Note's
intent, quoted: "self-loop repetition counts (DEPTHS — run-lengths of
equal-species consecutive reads)" (SP.1) and "the number of letters after
collapsing self-loop runs" (SP.2). On Chain'-(SuccStep)-words (the only
consumers: CollapsedWalk via collapseRuns_collapsedWalk, EntranceShape.word)
adjacent-equal-letters ⟺ self-loop edges (SuccStep n s s IS the loop edge),
so adjacent-duplicate removal = self-loop-run collapse exactly. Pinning: the
const-[] degenerate satisfier fails the [s]-equation, fails
collapseRuns_ne_nil, and fails collapseRuns_eq_self_iff (← at [s]); the
identity function fails eq_self_iff at [s,s]. Mathlib's
`destutter_eq_self_iff … ↔ l.IsChain R` backs the second lemma. SOUND.
(Minor observation, not counted: EntranceShape.depths is indexed by ALL
collapsed letters — one slot per maximal run including trivial length-1 runs
of non-loop letters, a superset of the note's "one depth slot per maximal
[self-loop] run". Inert data; appears in no theorem; the finiteness statements
quantify it away. No unit affected.)

## 5. The retargeted fence (REV 3, G3) vs SP-COMP's scoping — FAITHFUL

Checked field-by-field: hRoot (RootStage ∧ Coherent ∧ Budget at r = 0), hStage
(StageLaws), hCoh (Coherent ∧ Budget per read), hHalt, hVerdictPin — NONE
mentions InCatalogue/Succ/Out ✓. The fields are exactly the note's proof-step
OUTPUTS: steps (1)/(3)/(3′) "Budgets hold at every read"/"Geometric coherence
holds at every read"/root stage, steps (2)/(5) the D.7/D.8/D.10 stage laws.
The note's own completeness mechanism is "reachability by induction along the
word" — precisely what SP_COMP/compEdges derive (SuccStep ASSEMBLED from
hStage + hCoh; InCatalogue concluded by closure induction; Out through it).
The fence's "fields unfold to premises ≠ leak" claim is the note's own
scoping. hVerdictPin carries the D4R.0-K(c) residual as an explicit named
field, WHICH/WHERE/WHEN deliberately VP-owned; G4's weakened "visible, not
type-enforced" claim is accurate (the trivial discharge is displayed). The
conditionality ledger (§0 + group-F standing hypothesis_fields) matches SP.5's
ledger clause-for-clause. NO drop, NO strengthening.

## 6. Decidability as typed, every decide unit — ALL SOUND

Every kernel-decide target is a Bool equation or a DecidableEq-backed
equality: List.all/any/filter over Bool functions (succStepB etc.);
`==` via instBEqOfDecidableEq (Tag/ℕ/Option (ℕ×ℕ) all derive/inherit);
`(· ∈ list : Bool)` and `(2 ≤ linCount s)` via the core decide coercion
(Nat.decLe, List-membership from DecidableEq Species); List-equality targets
(loops3, terminal3, threshold filters) via DecidableEq (List Species);
shExample via DecidableEq ℤ with computable Int.fdiv (arithmetic re-checked:
(−2).fdiv 2 = −1, (−3).fdiv 2 = −2, the Bézout-variant census image 0 ✓);
Nodup via List.nodupDecidable. `deriving DecidableEq` on Species is fine
(Multiset/Finset decidable equality exist); `deriving Repr` fine (Repr
(Multiset _) in Mathlib Multiset/Sort.lean). Multiset-through-Quot kernel
reduction is honestly fenced at §6.2 with a designer-round fallback. No decide
unit needs a missing instance. (See NOTE A for the Prop-side aside — it
affects no decide unit.)

## 7. Spot-verified units (charge item 7; 8 drawn across groups)

- **Sp.shCongr**: t·γ = e·(t·u0) + s0·(t·h) with t·h = 1 − e·s ⇒ ≡ s0 mod e;
  statement = the note's display verbatim; Bézout order e·s + h·t = 1 ✓.
- **Sp.anchorBoundCensus**: all five conjuncts match "0 ≤ a ≤ ⌊(W − w′)/e⌋,
  a + ℓ ≤ ⌊W/e⌋ ≤ W ≤ n" + the e = 1 clause; ℕ-sub safe (w′ ≤ W by B3);
  a + ℓ ≤ W/e provable via ⌊s0/e⌋ + ℓ = ⌊(s0 + eℓ)/e⌋ ✓.
- **Sp.encodeCard**: Fintype.card (Fin a → Fin b) = b^a; exponent arithmetic
  1+3+5+(n+1)+n²+2+2n = n²+3n+12 re-checked ✓; entry ranges (d ≤ n+1 the
  widened one, tag needs n+2 ≥ 3 ⇒ hn) ✓.
- **Sp.selfloopChar**: both directions re-derived from StageLaws' match + tag
  iffs (given above at §1); faithful to "necessarily e = g = 1 … W(s) = μ(s)
  — the POST-REC species" ✓.
- **Sp.tauWord**: the three conjuncts = the note's word/τ-word split; sel-facts
  via (G6) through memCoherent; hne feeds the length identity ✓.
- **Sp.compEnumComplete**: IsComposition ↔ enum-membership, [] ↔ span 0 ✓.
- **Sp.rankStepRec** (the subtle SP-DAG case): the three-way split matches the
  note's bullets; the tagord = 2, μ = W branch: s full by (i), s′ full would
  force s′ = s via full_unique at the SAME stage (D′=D, w′=w, W′=μ=W, tag′=
  postRec) contra hne ⇒ fullBit rises 0 → 1 ✓. rankNat max re-computed:
  ((3n−1)n + (n−1))·2 + 1 = 6n² − 1 < 6n² ✓ (radix bounds tagord<3, n−W<n,
  bit<2 all justified by Coherent/Budget).
- **Sp.g6Forcing**: every conjunct forced exactly as the (G6) bracket displays;
  Multiset singleton step sound ✓.
Plus the whole H layer re-checked against SP.6: group counts 21/21/6/1/4 = 53
(R-row arithmetic 2+1+2+3+3+7+2+1 = 21 ✓, Q2 = 3+3 ✓), n3reachable's
one-step-from-root claim verified per stage, menuMap3's seven law-lines
re-computed as stage laws, n3postincW1 (only postInc letters are the 4 I
letters) ✓, R3 both flank variants with the saturated corrected (B5) ✓,
Nstar3six values 7/6/6/6/6/6 against the SIX COMPUTATIONS display ✓.

## 8. Fresh sweep (faithfulness/vacuity/hypotheses/defs/decomposition)

Coherent/Budget/StageLaws/RootStage/InCatalogue/Out/V_term transcriptions
checked display-by-display against (G1)–(G6)/(B1)–(B5)/SUCC — faithful,
including: rflank positivity+sum = IsComposition of W − s0 − w′ stated
additively (ℕ-sub avoided) ✓; w′ ≤ n omitted from (B5) but derivable inside
the same conjunction (B3 + W ≤ n), predicate equivalent ✓; the tag-iffs =
step (5) verbatim; hHalt = "up to and including its first W = 1 read";
CatalogueWord honestly scoped to confirming-terminated words (V_term-ended
and infinite branches prefixwise via CanTreeModel, stated) ✓. Non-vacuity:
the n = 3 layer + [confirmingRoot1] + word/entrance witnesses inhabit every
structure ✓. No axioms; native_decide banned twice ✓. p-independence by
typing, recorded not overclaimed ✓. N*₃/threshold layer definitions-only with
the docstring duties ✓ ("SEALED PREDICTION, not a theorem of this note"
carried). Roster arithmetic: 57 units re-counted per group (5+8+4+6+11+7+3+13)
✓; difficulty lists sum 30+23+4 = 57 ✓. Unit granularity: one display each;
the four medium-hard units carry pre-approved split points ✓.

## NON-BLOCKING NOTES (below the gap bar; zero faithfulness impact — reasons)

- **NOTE A** (§1.2): "Coherent/Budget/SuccStep as plain `Prop`
  conjunctions/matches, all decidable without instance gymnastics" — as
  literally typed, the clauses `∀ gm, s.sel = some gm → gm ∈ s.lam` (G4) and
  `∀ gm, s.sel = some gm → gm.1 * gm.2 ≤ s.ell` (B4) have NO off-the-shelf
  Decidable instance (unbounded ∀; the Eq-form is not discrimination-tree-
  visible as Option-∀-mem; no Option.decidableBAll found in Mathlib). A
  3-line match instance or `∀ gm ∈ s.sel, …` rephrasing fixes it. NOT counted:
  the operative decide mechanism is the hand-written Bool reflection layer
  (the same sentence's second half), no unit statement or decide target
  consumes Prop-decidability, and failure is loud (inferInstance error), so no
  unfaithful or vacuous artifact can result. Recommend a one-word repair at
  next touch.
- **NOTE B** (Sp.n1singleton): the sketch invokes "(g6Forcing at W = 1)" but
  the deps line (`speciesEnumComplete, n1RootConfirming, succTerminal`) omits
  Sp.g6Forcing. NOT counted: the deps as listed support a complete alternative
  route (enum membership + an internal decide over speciesEnum 1), so the
  dependency set is sufficient, merely route-ambiguous; either route is
  sound and the DAG stays acyclic either way.

## COUNTS AND VERDICT

Critical: 0. Gap: 0. (Two non-blocking notes above.)
Erratum §9: CONCUR (independently re-derived; the note-end ERRATUM RECORD
governs; blueprint bakes it into no target and cites it correctly).

**ACCEPT**
