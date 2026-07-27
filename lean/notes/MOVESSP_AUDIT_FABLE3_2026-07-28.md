# MOVESSP BLUEPRINT AUDIT — FABLE #3 (fresh instance, confirmation pass on REV 4)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable #3 (no prior context; parallel to the Codex rev-4 audit)
- **Scope:** REV 4 confirmation, including re-verification of every §7b split-verdict
  adjudication (both REFUTATIONS checked hardest), the eight charged deep checks, six
  unit spot-checks, and a fresh sweep of all 61 units + 3 def files.
- **Ground truth:** `lean/notes/MOVES_2026-07-24.md` lines 5857–6782 (§M-SPECIES,
  dual-accepted rev-8 text) + the ERRATUM RECORD at file end (lines 13796–13807).
- **Blueprint:** `lean/notes/MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` (1492 lines, read in full).
- **Charge:** `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` (below-the-line checklist;
  faithfulness / non-vacuity / hypothesis fidelity / Defs soundness / decomposition).

## 1. §7b adjudication re-verification (all 13 Codex items + the 6 rev-3 items)

**C-1 (the no-finiteness REFUTATION) — VERIFIED, refutation stands.** The note's scope
display found verbatim: "it bounds letter ALTERNATIONS only. The number of READS stays
unbounded (self-loop runs — the depth parameters — are arbitrarily long …)" (SP.2
count-free reading) and SP.5's "Infinite branches are catalogued prefixwise". So a
finiteness pin on branches/words would be UNFAITHFUL; `len : Branch → ℕ∞` with
`(r : ℕ∞) < len η` quantifiers represents exactly the note's SP-COMP domain ("terminal-
verdict branches and infinite branches alike, prefixwise"): len = ⊤ covers every finite
read index of an infinite chain; `hHalt` (len = r+1 at any W = 1 read) reproduces "up to
and including its first W = 1 read" and forces uniqueness of the confirming read, so an
infinite word correctly has no W = 1 read. len = 0 as a real case checks against the
quoted (τ-hen) display ("halts with NO window read ever opened"). `hTotal` is cited to
the note's own "parts (a) totality … are DISCHARGED" opening block and only blocks the
empty model. The SP-DAG tie landing as the CONCLUSION unit Sp.compCollapsed is the right
place (see check 7). Codex's finiteness demand refuted; the ℕ∞ design accepted.

**C-2 (the VP-owned rider REFUTATION) — VERIFIED, refutation stands.** The τ/cap content
is genuinely outside §M-SPECIES: SP.4's V_term definition says "Their SEMANTICS (which
multiset of (E, F) pairs a halt reports, when τ fires) is [3t]'s verdict pin VP … —
cited as owner, not consumed", and the ledger names the residual "(alphabet V + halting
rule τ + the uniform detection cap), owned by [3t] via VP". The note displays ownership,
never the rule, so no stronger field is encodable from the frozen text; `hVerdictPin` as
alphabet + attachment site is the honest named rider. The widened scope (every finite
nonempty word) matches the note's two word-ending displays ("its chain's τ-leaf carries
a verdict"; "Edges into V_term from a CONTINUING letter … end both words at that
letter"). The `0 < m` guard was checked deliberately: step (4) quantifies over ⊥-READS,
and the V_term-edge display requires a letter, so both attachment displays presuppose a
nonempty word; a zero-read (τ-hen) chain's verdict is pinned at the level-0 TRACK, VP
data outside the word — excluding m = 0 is faithful, not an omission.

**C-3 (outFinite) — upheld fix VERIFIED.** SP.4: "For s ∈ 𝒮_n^raw, the OUTGOING MENU
Out(s) …" + "FINITENESS: |Out(s)| ≤ |𝒮_n^raw| + 3 by SP-FIN". `hs : InCatalogue n s`
restores the display's quantifier; the honest sketch note (hs unused by the proof, kept
for faithfulness) is correct. — But see FINDING 1: the same standard was not applied to
the sibling SUCC-domain unit Sp.succTerminal.

**C-4 (selfloopChar) — upheld fix VERIFIED, and the content re-derived.** The note's
SUCC is catalogue-restricted, so the main statement `s ∈ Succ n s ↔ …` under
`hs : InCatalogue n s` is the right domain. Content re-derivation (both directions):
(→) StageLaws s s gives D = e·g·D with D ≥ 1 (WellTyped via memCoherent) ⇒ e·g = 1 ⇒
e = g = 1; W = μ; the tag-iff pair forces postRec; sel = some (1, W). (←) the laws are
reflexive at e = g = 1, μ = W; coherence/budget from hs. Matches "necessarily e = g = 1
… with W(s) = μ(s) — the POST-REC species whose window equals their own selection
multiplicity" exactly. The hc/hb helper is TRUE (unlike an unhypothesized version, which
fails at D = 0), and loops3's Bool filter correctly reflects the helper on catalogue
members.

**C-5 — VERIFIED.** The note itself types the entry objects away: "into a block entry
(e-block, landing cell β₀ — [1v] CTS-M(iii)'s objects)"; (gsel, μsel) is the letter-level
face ("whose designated continuing branch enters the size-e block"); depths are
parameters with no [2a] law ("self-loop runs carried as depth parameters"). Ownership
correctly in hypothesis_fields.

**C-6 — VERIFIED.** Routing block sound; §1.1's decidability sentence now honest (the
`∀ gm, s.sel = some gm → …` shape has no off-the-shelf instance; the Bool layer matches
on sel). Every decide target re-typed — see check 5.

**C-7 — VERIFIED.** menu3_exact_global's chain walked — see check 4.

**C-8 — VERIFIED.** multiSide6 pinned to six literals transcribing the R1–R4 rows — see
check 6.

**C-9/C-10/C-11/C-12/C-13 — all VERIFIED** (literal exclusion bodies in catalogue3
order; lamMatrix + lamMatrix_inj fully spelled with (B5) bounds; compEnum_nodup spelled;
confirmingRoot1 literal correct field-by-field against g6Forcing's forcing at W = n = 1,
with Sp.g6Forcing in n1singleton's deps; the collapse unit split into four).

**Rev-3 items (C1/C2/G1–G4) — all still correctly folded in.** loops3 order
[loopQ3, loopQ23] re-derived from catalogue3 = R ++ Q3 ++ Q2 ++ Q1 ++ I (Q3's loop
letter precedes Q2's); the ▸(1,2) roster's three members re-verified from the note's own
R6 row "{(1,2),(1,1)}▸(1,2)" + the row-unrestricted menu law "▸(1,2) → Q2 letters" — and
the note-side ERRATUM RECORD now exists at file end and governs, exactly as §9 routes
it; collapseRuns' defining equations exclude the const-[] satisfier; the n1 DAG is
acyclic (n1RootConfirming → n1singleton → n1Word); the fence correctly targets only
closure-side objects (checked: no CanTreeModel field mentions InCatalogue/Succ/Out);
G4's visible-not-enforced record is honest.

## 2. The charged deep checks (2)–(7)

**(2) selfloopChar vs the SUCC definition** — done under C-4 above: faithful, both
directions provable, domain right.

**(3) outFinite's hs vs SP.4's quantifier** — done under C-3: faithful. Card arithmetic
sound (|Succ| ≤ |SnRaw| via the InCatalogue conjunct; card Verdict = 3 = |V_term|).

**(4) menu3_exact_global's closure chain — WALKED, it closes.** Forward: SuccStep 3 s s'
carries Coherent s' ∧ Budget 3 s' AS ITS OWN CONJUNCTS ⇒ s' ∈ speciesEnum 3
(speciesEnumComplete, which quantifies over ALL Species with those two properties — this
is the step that reaches off-catalogue candidates) ⇒ closure_step3 (s ∈ catalogue3,
s' ∈ enum, succStepB true via reflSucc) yields catalogue3.contains s' ⇒ menu3_local
reads off (menuMap3 s).contains s'. Backward: menuMap3 s ⊆ catalogue3 by its group-membered
definition, so menu3_local's ← direction + reflSucc give SuccStep. So NO SuccStep edge
from a catalogue3 letter can leave catalogue3 — the sealed exactness, now genuinely
global over all Species targets. Deps (reflSucc, speciesEnumComplete, n3closureStep)
declared and sufficient.

**(5) Bool-routing block vs every decide target — ALL TYPED.** Checked one by one:
root3_enum_check (`==` on Bool, `groupR.contains` via derived BEq); groupR_admissible;
closure_step3 (`!… || …`); reachable3 (`|| … .any`); menu3_local (`== .contains`);
loops3 (List.filter over `succStepB 3 s s : Bool`; list equation decidable by
DecidableEq); postInc3_W1 (`s.tag == .postInc`, `s.W == 1` — derived BEq); terminal3
(filter on `s.W == 1`; `(s.W == 1) == (s.sel == none)` with BEq (Option (ℕ × ℕ)));
threshold_data_pinned (`decide (2 ≤ linCount s)` / `decide (3 ≤ …)` — the one place a
Prop atom occurs, correctly routed through `decide`; Nodup and Option-equations
decidable; `.isSome == .contains`); entrance3_patterns (filters on `s.sel == some (1,2)`,
`(s.e == 2) && !(s.sel == none)`; membership `.contains`; `rootR6sel13 ∈ groupR`
decidable via DecidableEq); n3card53 (Nodup decide, length rfl); shExample (Int
literals, Int.fdiv computable). No `(P : Bool)` coercion anywhere. Order discipline
re-audited: the only order-pinned targets are loops3 ✓, terminal3 (RHS is literally
groupQ1 ++ groupI) ✓, entrance's groupR filter (R4 < R5 < R6) ✓, fieldSizeExcluded2/3 —
re-derived against the row displays: within R6 the ≥2-linear rows in display order are
▸(1,2), ▸(1,1), {(1,1)³} ⇒ [… exR6b12, exR6b11, exR6t …]; groups R → Q3 → Q2 ⇒ exQ23c
last; 5 + 4 + 2 = 11 members match the note's three λ-classes exactly ✓.

**(6) multiSide6's six literals vs the note's rows — ALL SIX EXACT.** Field order (tag,
D, w, W, e, s0, ell, a, d, slots, lam, sel, lflank, rflank) checked term by term:
Q3(R1) rf (1,1): (postRec,1,1,3, e1, s0 0, ℓ1, a0, d2, Icc 0 1, {(1,1)}▸(1,1), [], [1,1]) ✓;
Q3(R2): s0 1, a1, Icc 1 2, [1],[1] ✓; Q3(R3) lf (1,1): s0 2, a2, Icc 2 3, [1,1],[] ✓;
the three Q3(R4) rows: ℓ2, d3, Icc 0 2, rflank [1], λ▸sel = {(2,1)}▸(2,1) /
{(1,2)}▸(1,2) / {(1,1),(1,1)}▸(1,1) ✓ (the {(1,1)²} multiset transcribed with both
copies). N*₃ values 7/6/6/6/6/6 match "N*_3 = 6; … N*_3 = 6; … N*_3 = 7" per name ✓.
Nodup + groupQ3-membership + the isSome==contains catalogue check keep the pin
non-trivial. Realizability semantics correctly absent (sealed prediction, not a theorem).

**(7) Sp.compCollapsed vs SP-DAG's display — FAITHFUL AND SOUND.** The statement bounds
only the collapsed image of the length-m read prefix (≤ 6n²) while m itself ranges over
all naturals ≤ len η (unbounded at len = ⊤) — the note's "letter ALTERNATIONS only /
READS stay unbounded" fence transposed exactly. Proof route checked index-by-index: all
prefix reads satisfy r < m ≤ len (compMember applies), all consecutive pairs satisfy
r+1 < m ≤ len (hStage applies), assembly gives a member-wise catalogued SuccStep chain,
collapseWalk gives a CollapsedWalk, dagWalk (hn present) bounds it. m = 0 degenerates
correctly ([] ↦ 0 ≤ 6n²).

## 3. Spot-checks (6, incl. one H-layer and one shift-map unit)

1. **Sp.shSlots (shift map):** re-derived the note's telescope p_{j_k} + σ = ⌊s₀′/e⌋ + k
   with fdiv exactness from sh_dvd; k = 0 anchor clause present. Faithful, provable. ✓
2. **Sp.n3terminal5 (H-layer):** the five W = 1 letters are Q1 ++ I in filter order (R/Q3
   have W = 3, Q2 has W = 2, so the filter is exactly the tail — order argument sound);
   the (G6) instance and the empty-menu face match "Out(s) = V_term exactly" jointly with
   succTerminal. ✓
3. **Sp.g6Forcing:** conclusion list = the note's bracketed forcing verbatim (e = ℓ = 1,
   s₀′ = a = 0, λ = {(1,1)}, no flanks, sel ⊥); each conjunct re-derived from
   (B3)/(G2)/(G4)/(G1)/(G6). ✓
4. **Sp.finThm:** SP-FIN verbatim; hn : 1 ≤ n matches the note's own "n + 2 ≥ 3 for
   every n ≥ 1" tag-entry remark; p-independence correctly a typing fact recorded in the
   docstring, not a vacuous clause. ✓
5. **Sp.rankStepRec:** the three-way display transposed; the subtle μ = W ∧ tagord = 2
   branch re-derived (s full by IsFull's definition; stage equality + full_unique force
   s' = s against hne, so fullBit rises 0 → 1). ✓
6. **Sp.tauWord:** word arithmetic + (G6) transport through hMem/memCoherent; hLast/
   hFirstW1 as structure laws render "closes at the confirming read" without an
   antecedent; VP's verdict-position correctly excluded (hypothesis_fields honest). ✓

## 4. Fresh sweep of all 61 units (+ Defs/DefsEnum/DefsN3)

Roster reconciled: A5 B8 C4 D6 E11 F11 G3 H13 = 61; difficulty table sums 32+25+4 = 61.
All moves_refs located in the frozen text; no fabricated quote found. Coherent/Budget
re-checked clause-by-clause against (G1)–(G6)/(B1)–(B5): faithful; the two omissions
(w′ ≤ n; flank spans ≤ n) are derivable inside the stated conjunction (extensionally
equal predicate, the recursions correctly living in RootStage/StageLaws per the note's
own "(B1)–(B3) recursions read as a generation rule"). StageLaws' tag-iff pair checked
safe in every consumed context (Coherent s' forces e·g ≥ 1 through D' ≥ 1). InCatalogue
= the rev-3 least-set definition verbatim. Encoding units match the note's corrected
ranges (d ≤ n+1; entry count n²+3n+12; sel ⊥ as reserved (0,0)). SP-COMP group: fields
are raw engine laws only; conclusions assembled, never assumed; hf/hdeg carried for
quantifier fidelity; hypothesis_fields present on every group-F unit with owners named.
Non-vacuity: catalogue3/confirmingRoot1 literals inhabit Species and InCatalogue;
CatalogueWord 1 inhabited by [confirmingRoot1]; CanTreeModel trivially instantiable and
honestly conditional (§0). Defs soundness: no def decides an open question (Nstar3six is
a censused-data table pinned to displayed values; menuMap3 is checked exact, not
assumed). n = 3 layer: 53 = 21+21+6+1+4, group contents, menu map, loops, thresholds,
entrances all re-derived against SP.6's displays. shExample's seven conjuncts recomputed
by hand (incl. the alternate Bézout representative: geoPos 2 (−1) 3 1 = 2, σ = −2,
image 0 ✓). Erratum §9 independently confirmed from the note's own three displays.

## 5. Findings

**FINDING 1 — GAP (SUCC-domain consistency; the C-3 standard not applied to the sibling
unit).** Sp.succTerminal, SP0_succTerminal.lean:
> statement: `theorem succ_terminal (n : ℕ) (s : Species) (h : s.sel = none) :
> Succ n s = ∅` … moves_ref: "and SUCC(s) := ∅ for terminal s (selection ⊥)."
The quoted clause sits INSIDE the note's catalogue-scoped definition block — "For
s ∈ 𝒮_n^raw, the OUTGOING MENU Out(s) … and SUCC(s) := ∅ for terminal s (selection ⊥)"
(SP.4, Definition (Out)) — the same "For s ∈ 𝒮_n^raw" quantifier whose restoration on
out_finite/selfloop_iff was upheld at C-3/C-4 ("never state more than the note does",
quoted in Sp.outFinite's own sketch). succ_terminal states the clause for ALL
s : Species. The statement is TRUE of the corpus's total `Succ` def (StageLaws' none-
branch is False), no consumer breaks (n1singleton's step case uses it on a catalogue
member), and the note's clause is definitional rather than a theorem display — hence
GAP, not critical. Repair is the exact C-3 pattern: add `hs : InCatalogue n s`
(faithfulness-only, unused by the proof) or record the domain deviation as a helper the
way selfloop_succStep_iff does. (`stageLaws_terminal` in the same unit is corpus-
internal bookkeeping and is fine unrestricted.)

No other finding. Specifically checked and CLEARED as non-findings: hVerdictPin's
`0 < m` guard (matches step (4)'s ⊥-read domain — the τ-hen verdict is track data
outside the word); hTotal (cited to the discharged totality, anti-vacuity only);
Budget's two derivable omissions (extensional equality); fullForcing/fullUnique/
rankRadix on hc/hb rather than InCatalogue (the F13-established convention for
SP-DAG-inner predicate lemmas, distinct from SUCC/Out-typed statements).

## Counts and verdict

Findings: 0 critical / 1 gap.

**REJECT (0 crit / 1 gap)**

(One-line repair path: apply the C-3 pattern to Sp.succTerminal. Everything else in
REV 4 — both §7b refutations, all 13 Codex dispositions, the erratum, the closure
chain, the literals, the Bool routing, and the other 60 units — confirms clean.)
