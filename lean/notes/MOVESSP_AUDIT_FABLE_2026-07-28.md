# MovesSp blueprint REV 2 — fresh-Fable semantic audit (RE-AUDIT after Codex REJECT)

- **Date:** 2026-07-28 (executed 2026-07-27 machine time)
- **Auditor:** fresh Fable instance (fresh context; read the note first, blueprint second)
- **Scope:** rev-2 re-audit of `lean/notes/MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` (1187 lines,
  read in full) against the frozen rev-8 §M-SPECIES text,
  `lean/notes/MOVES_2026-07-24.md` lines 5857–6756 (read in full), per
  `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`. Includes: (a) verification that each of
  the 17 Codex findings' repairs is genuine, (b) a fresh full sweep (new defects introduced
  by repairs count fully), (c) the Moves-vocabulary signature check
  (`Moves.HasAnchorK`, `Moves.Stage`), (d) the campaign doctrine (interfaces FALSE for
  note-rejected instances; kernels as Props over concrete objects; hypotheses neither
  weakened nor silently strengthened; n=3 decide units decidable as typed AND
  content-pinned to the note's displays EXACTLY).

## 0. Moves signature check (charge addendum)

- `Moves.HasAnchorK` — EXISTS: `lean/LeanUrat/Moves/Defs.lean:243`,
  `def HasAnchorK {K : Type u} [Field K] (x : LaurentPolynomial K) (a : ℤ)
  (Ranch : Polynomial K) : Prop := Ranch.coeff 0 ≠ 0 ∧ x = LaurentPolynomial.T a *
  Polynomial.toLaurent Ranch`, in `namespace LeanUrat.Moves`. Sp.shAnchorInv's
  `hasAnchorK_T_mul` signature is compatible and the lemma is true of this definition
  (`T σ * (T a * toLaurent R) = T (a + σ) * toLaurent R`; the coeff-0 clause rides).
  COMPATIBLE.
- `Moves.Stage` — EXISTS: `Defs.lean:106`, `structure Stage (p : ℕ) [Fact p.Prime]
  (F : Type u) [Field F] [Finite F]` with fields `e h : ℕ`, `s t : ℤ`,
  `hbez : (e : ℤ) * s + (h : ℤ) * t = 1`, `he1t : e = 1 → t = 0` — exactly the fields and
  shapes Sp.shStage consumes (`σs.hbez`, `σs.he1t he1`); the ℕ→ℤ casts are acknowledged in
  the unit sketch. Name resolution `Moves.Stage` from inside `LeanUrat.MovesSp` works
  (both under the `LeanUrat` root). COMPATIBLE. No critical from this check.

## 1. Verification of the 17 repairs (findings→repairs table, blueprint §8)

- **F1/F2 (compMember/compEdges circularity) — GENUINE.** `CanTreeModel`'s fields are the
  raw per-read laws (`RootStage`+`Coherent`+`Budget` at r=0; `StageLaws` per pair;
  `Coherent ∧ Budget` per read; the halt endpoint); `InCatalogue`/`SuccStep`/`Out` occur in
  no field; SuccStep is assembled in the proofs. Full (n, p, f, η, r) prefix present, with
  `hf : f.Monic`, `hdeg : f.natDegree = n` carried for quantifier fidelity. Doctrine check:
  the interface is FALSE for engine trees the note rejects (a stray incoherent read fails
  `hCoh`; an off-stage-law transition fails `hStage`; a word running past its first W = 1
  read fails `hHalt`; a read with sel = none before the last position contradicts `hStage`'s
  match-none-False). Passes.
- **F3 (CatalogueWord endpoint) — GENUINE.** `hLast` (last letter W = 1) + `hFirstW1` (no
  earlier W = 1) force the note's "up to and including its first W = 1 read"; the
  continuing-letter/V_term and infinite cases are correctly routed to `CanTreeModel`
  prefixwise (parenthetical in §2). `tauWord := dropLast` matches "the catalogue word with
  that final confirming letter removed".
- **F4 (EntranceShape) — GENUINE IN STRUCTURE, one residual gap (G1 below).** Block-entry
  selection `(gsel, μsel)` via `hEntry`; height-pair slots per read and depth slots per
  maximal run as bare-data fields (the note: "one marker letter + one depth slot per
  maximal run"); finiteness quantifies over `EntranceShape` and lands in the SP-DAG bound
  via `collapseRuns`. But `collapseRuns` itself is unpinned — see G1.
- **F5 (thresholdData content-pinning) — GENUINE.** Filter identities on `linCount`
  (which faithfully counts distinct linear factors: distinct factors are distinct multiset
  elements, so `Multiset.card (lam.filter (·.1 = 1))` = the number of distinct linears the
  letter demands; q = 2 threshold ≥ 2, q = 3 threshold ≥ 3 match "one nonzero root"/"two
  nonzero roots"); named-letter list equalities; per-name N*₃ values (7/6/6/6/6/6 exactly
  per the SIX COMPUTATIONS); lengths demoted to trailing sanity. I recomputed the p = 2
  filter by hand over the 53 rows: λ ∈ {{(1,1)²}, {(1,2),(1,1)}, {(1,1)³}} → 5 + 4 + 2 = 11
  letters, exactly the note's list; p = 3: the 2 {(1,1)³} rows. Pinned.
- **F6 (R3 both flank variants) — GENUINE.** `R3letterA` ([2]) and `R3letterB` ([1,1]),
  both checked with a = 2 (the (B5) saturating witnesses).
- **F7 (D4R.0-K(c) explicit) — GENUINE AS DEMANDED**, with a prose overclaim (G4 below).
- **F8–F14 — ALL GENUINE.** F8: both iffs with full binders; F9: full binder list, e ≥ 1
  explicitly not assumed (pure divisibility — sound); F10: both `sh_slots`/`sh_anchor`
  spelled, and I verified the fdiv arithmetic against the note's displayed computation
  (`(j_k − tγ)/e + ⌊tγ/e⌋ = ⌊s₀′/e⌋ + k` using tγ ≡ s₀′ mod e); F11: `sh_image` is pure
  translation (no spurious hypothesis) and `sh_geo_slots` fully stated; F12: `sh_e1_stage`
  spelled (σ = 0 + position identity via `σs.he1t`); F13: hypothesis types written; F14:
  `fullBit` defined in §2, the four-case disjunction written out, and the mixed radix
  `(((D−1)·3 + tagord)·n + (n−W))·2 + fullBit` is order-isomorphic to the note's lex tuple
  on the catalogue ranges with max value 6n² − 1.
- **F15 (mcRoster) — GENUINE.** Struck; deferral recorded at §2, group F, and §6; no
  in-scope moves_ref exists (the (m, c) rows are §S-RESUM's), correct call.
- **F16 (rootLetters) — GENUINE.** The membership equivalence
  `RootAdmissible 3 s ↔ s ∈ groupR` is the strongest content pin available (the list must
  equal the predicate's satisfier set or the decide facts fail); multiplicity via
  n3card53's Nodup; the duplicate-enum-candidate caveat is sound.
- **F17 (entrancePatterns full roster) — REPAIR EXECUTED BUT ITS CONTENT IS FALSE** (C2
  below): the repair's full conjunction contains two unprovable conjuncts.

## 2. Fresh-sweep findings

### CRITICAL

**C1 — Sp.n3selfloops: the pinned filter order is impossible; the decide target is false
as typed.**
Offending spec text (§5 H): `theorem loops3 : catalogue3.filter (fun s => succStepB 3 s s)
= [loopQ23, loopQ3]`.
Blueprint §4 pins `catalogue3 := groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI`, and
`loopQ3 ∈ groupQ3` precedes `loopQ23 ∈ groupQ2` in that concatenation; `List.filter`
preserves order and Nodup gives one occurrence each, so the filter necessarily evaluates
to `[loopQ3, loopQ23]`. The unit is content-right (note: "exactly two loop classes at
n = 3 … Q2.3▸(1,2) and Q3▸(1,3)") but the stated list equality can never be proved —
`decide` would reduce it to `false`. (Contrast Sp.n3terminal5, which gets the analogous
order right: `groupQ1 ++ groupI`.) CRITICAL.

**C2 — Sp.n3entrancePatterns: two conjuncts are mathematically false — the ▸(1,2) roster
has THREE members per group, not two.**
Offending spec text (§5 H): `(groupR.filter fun s => s.sel == some (1, 2)) =
[rootR4sel12, rootR5sel12]` and `((groupQ3.filter fun s => s.sel == some (1, 2)).length
= 2)`.
By the note's own R6 display — "R6 … {(1,2),(1,1)}▸(1,2) and ▸(1,1)" (hand catalogue,
GROUP R) — R6's ▸(1,2) row is a root letter with selection (1,2), so the groupR filter has
three members (R4, R5, AND R6 rows), and likewise three in groupQ3; both conjuncts decide
to `false`. Root cause: the note's entrance gloss "into the μ=2 block: root▸(1,2) [R4/R5
rows]" is an incomplete bracket that contradicts the note's own R6 row and its own menu
law "▸(1,2) → Q2 letters"; the blueprint transcribed the bracket instead of the letter
roster. The repairer must fix the blueprint to the true filter content ([rootR4sel12,
rootR5sel12, rootR6sel12]; length 3) AND flag the note-side bracket for an erratum — the
blueprint may not silently state a false list to match a glossed display. CRITICAL.

### GAP

**G1 — `collapseRuns` is unpinned: every companion theorem is satisfied by the degenerate
`collapseRuns := fun _ => []`.**
Offending spec text (§2): `def collapseRuns : List Species → List Species   --
consecutive-dedup recursion` — a def-only comment. The const-[] implementation satisfies
`collapseRuns_sublist` ([] is a sublist), `collapseRuns_collapsedWalk` ([] is vacuously a
CollapsedWalk), `entrance_collapsed_len` (0 ≤ 6n²) and `entrance_collapsed_finite`
({[]} is finite) — i.e. the whole F4 finiteness chain is dischargeable with the wrong
function, and `EntranceShape.depths`' index type collapses to `Fin 0`. The note's object
("the number of letters after collapsing self-loop runs"; "one marker letter + one depth
slot per maximal run") needs a content-pinning unit — e.g.
`collapseRuns l = l ↔ l.Chain' (· ≠ ·)` plus the recursion equations, or equality to a
Mathlib destutter — none is specced. Underspecified-Defs dependency / non-vacuity trap. GAP.

**G2 — n1Clause ↔ n1singleton dependency cycle.**
Sp.n1Clause lists `deps: Sp.n1singleton, Sp.memCoherent`; Sp.n1singleton lists
`deps: Sp.speciesEnumComplete, Sp.n1Clause, Sp.succTerminal` — a cycle in the unit DAG.
Content is acyclic (n1singleton needs only n1Clause's FIRST theorem
`n1_root_confirming`, while n1Clause's SECOND theorem `n1_word` needs n1singleton), so the
fix is a split, but as specced the roster is not buildable in dependency order. GAP.

**G3 — the group-F fence contradicts §2's hRoot.**
Offending spec text (§5 F standing block): "NEVER strengthen (no field may assume
SuccStep/InCatalogue/RootAdmissible)" — yet `hRoot`'s content is definitionally
`RootAdmissible n (datum η 0)` (`RootStage ∧ Coherent ∧ Budget` is RootAdmissible's exact
unfolding, §2). Semantically harmless (the conjunction IS the note's step-(1) output, and
the F1 point — no CLOSURE-side conclusion in a field — still holds), but the fence as
written is violated by the blueprint's own interface and will confuse a repairer about
which side to change. The fence should name the closure-side objects only
(SuccStep/InCatalogue/Out). GAP.

**G4 — "non-detachable" overclaim on hVerdictPin.**
Offending spec text (Sp.compMember hypothesis_fields): "stating the theorem over the full
CanTreeModel keeps the conditionality visible and non-detachable." It is detachable: any
model discharges the pair (`verdict`, `hVerdictPin`) by `verdict := fun _ => some .z`
(the field's semantics being deliberately VP-owned, nothing constrains WHICH verdict), so
the Lean SP_COMP is exactly as strong with or without the field. The note's ledger
("SP-COMP's remaining conditionality is exactly the D4R.0-K(c) residual") is thus carried
by documentation, not by the type. The F7 repair is genuine as an explicitness repair;
this sentence claims more than the encoding enforces and should be weakened to "visible".
GAP.

## 3. Units checked clean (fresh sweep; against the note's displays)

§2 Defs: Species fields = SP.1's retained tuple exactly (heights/depths/values absent per
the FORGOTTEN list); Coherent = (G1)–(G4)+(G6) verbatim in census coordinates (a/d/slots
as fields with (G2)/(G3) as relations — faithful to the tuple+coherence split); Budget =
(B3)/(B4)/(B5) per-tuple clauses with the rev-3 corrected census anchor bound
`a ≤ (W − wraw)/e` (w′ ≤ n and flank-span ≤ n are extensionally implied by the retained
conjuncts, so the predicate is unchanged); StageLaws = the D′/w′/W′/tag laws with (G5)'s
iffs, match-form decidable; InCatalogue = the rev-3 least-set definition; Out = SUCC ∪
V_term with the superset discipline; Verdict = three bare labels. Shift block: shSigma/
Sh/geoPos match (SH)/(SH-G)/(SH-C); shCongr/shDvd/shSlots/shE1/shEquiv/shStage arithmetic
re-derived by hand against the note's displayed identities; shExample recomputed
(fdiv values −1, 0, 1, 0, 1, −2, 0 all correct, including the Bézout-check row).
Group C: anchorBoundCensus/Geo/g6Forcing/b4Derived match their displays (ℕ-truncation
sound under (B3)). Group D: the code-length arithmetic 1+3+5+(n+1)+n²+2+2n = n²+3n+12 and
entry range n+2 check out; hn : 1 ≤ n matches "n + 2 ≥ 3 for every n ≥ 1"; SP_FIN/SP_FIN′
faithful; p-independence by typing is the honest rendering and is recorded at §0.
Group E: selfloopChar's iff verified in both directions against "necessarily e = g = 1 …
W(s) = μ(s) — the POST-REC species"; fullForcing/fullUnique = SP-DAG (i); rank units =
SP-DAG (ii) with the subtle full-POST-REC branch routed through full_unique exactly as the
note's third bullet; dagWalk/dagWords = (iii) with the (|𝒮|+1)^{6n²} bound. Group F:
SP_COMP/SP_COMP_edges quantifier-faithful; tauWord_spec faithful (verdict pinning
correctly excluded as VP's); collapseWalk sound (modulo G1). Group G: compEnum/lamEnum
completeness iffs pin those enums non-degenerately (const-[] fails them, unlike G1's
collapseRuns). Group H: n3card53 (53 = 21+21+6+1+4, Nodup), n3rootLetters,
n3closureStep, n3reachable (I verified every non-root letter IS one SuccStep from a root
letter at n = 3, per the note's generation display), n3catalogueEq (the closure induction
is sound in both directions), n3menuMap (pins the displayed map against succStepB over
53×53; menuMap3's def comment transcribes the display), n3postincW1, n3terminal5 (order
correct), n3R3check, n3thresholdData, n1singleton — all decidable as typed and
content-pinned. Roster arithmetic (§7): 56 units, group and difficulty counts consistent.

## 4. Counts and verdict

Criticals: 2 (C1 loops3 order-false; C2 entrancePatterns ▸(1,2) roster-false ×2 conjuncts).
Gaps: 4 (G1 collapseRuns unpinned/degenerate-satisfiable; G2 n1 dependency cycle;
G3 fence-vs-hRoot contradiction; G4 non-detachability overclaim).

Both criticals are n=3-layer decide targets that are FALSE as typed — cheap to repair
(reorder one list; extend one roster to its true three members + note-erratum flag) but
they are exactly the content-pinning the layer exists for, and one of them (C2) traces to
an internal inconsistency in the frozen note that must be routed, not papered over.

**VERDICT: REJECT (2 crit / 4 gap)**
