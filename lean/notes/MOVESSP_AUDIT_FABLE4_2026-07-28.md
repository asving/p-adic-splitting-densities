# MOVESSP blueprint audit — FABLE #4 (fresh instance, closing confirmation)

Date: 2026-07-28 · Auditor: fresh Fable #4 (no prior context) · Scope: REV 5 of
`MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` (1584 lines, read in full), the corpus's
CLOSING rev. Ground truth: `MOVES_2026-07-24.md` §M-SPECIES (lines 5857–6782)
+ the ERRATUM RECORD at file end (lines 13796–13807). Charge:
`CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` checklist. Method per campaign
calibration: verification by COMPUTATION and display-diff, not plausibility —
the full n = 3 / n = 1 decidable layer was re-implemented independently
(Python, from the blueprint's §2 defs alone) and every decide target checked;
the rev-4 → rev-5 diff was taken from git (7f3994d → 5cf8d13, 214 lines) and
read in full.

## 1. HARDEST ITEM (1): hN1 + Sp.n1Branch vs the note's n = 1 display

The note's display, found and quoted (SP.4, THE n = 1 CLAUSE, rev 5): "At
n = 1 the catalogue word is the single ROOT letter (W = n = 1, selection ⊥ —
(G6)'s degenerate degree)" … "the τ-WORD is EMPTY (the standing rule
'catalogue word minus the final confirming letter' applied to the one-letter
word …); the CATALOGUE WORD is the single confirming root letter — census
data, gate-walked". So the catalogue word is NONEMPTY at n = 1; only the
τ-word is empty — exactly what `hN1 : n = 1 → ∀ η, 0 < len η` encodes,
minimally (nonemptiness only; len = 1 and the letter identity derived).

ADVERSARY A (the rev-4 vacuity, must now fail): M with Branch := Unit,
len ≡ 0 at n = 1. hTotal ✓; hRoot/hStage/hCoh/hHalt all vacuous (every
antecedent needs 0 < len or r < 0); hVerdictPin vacuous (0 < m fails at
m = 0). Rev 4 accepted this model — Codex's crit stands conceded. Rev 5:
hN1 rfl η gives 0 < 0 — VIOLATED. Fixed as claimed. ✓

ADVERSARY B (over-restriction probe, must SURVIVE): the (τ-hen) len-0
branch at n = 3 (note: "(τ-hen) ROOT HENSEL LEAVES — … halts with NO window
read ever opened" — a Hensel track below a split f̄ carries no letter).
hN1's antecedent `3 = 1` is unprovable, so hN1 imposes NOTHING at n ≥ 2;
all per-read fields stay vacuous on that branch. SURVIVES — no silent
strengthening. ✓

DERIVATION CHECK (Sp.n1Branch's sketch, walked): hN1 → 0 < len η; hRoot →
RootAdmissible 1 (datum η 0); n1_root_confirming → W = 1 ∧ sel = none; hHalt
at r = 0 → len η = 1; SP_COMP + n1singleton → datum η 0 = confirmingRoot1;
packaging: hMem ✓, hChain trivial ✓, hLast ✓, hFirstW1 vacuous on a
singleton ✓. Deps (n1singleton, n1RootConfirming, compMember) acyclic ✓.
CONSISTENCY: at n = 1 the fields jointly force len ≡ 1 (no len = ⊤ branch:
hRoot's W = n = 1 + hHalt close it) — exactly the note's display, and the
n = 1 interface is INSTANTIABLE (checked: the one-branch model with datum ≡
confirmingRoot1 satisfies every field; RootAdmissible 1 confirmingRoot1
verified by hand AND by the independent implementation) — non-vacuous. ✓
COMPUTATION: the n = 1 closure enumerates to exactly ONE letter, equal to
the §4 literal ⟨.root,1,1,1,1,0,1,0,2,Icc 0 1,{(1,1)},none,[],[]⟩ ✓.

## 2. HARDEST ITEM (2): the 6 threshold units vs rev 4, diffed

Rev 4's `threshold_data_pinned` had exactly 7 content blocks; the mapping,
conjunct-by-conjunct from the git diff:
  (i)  2 linCount filter identities → Sp.n3exclusionLists — IDENTICAL text;
  (ii) multiSide6 = [6 literal Species rows] → Sp.n3multiSide6 — all six
       literals character-identical (tag/D/w/W/e/s0/ell/a/d/slots/lam/sel/
       lflank/rflank per row; field-order note retained);
  (iii) all-groupQ3 + Nodup → Sp.n3multiSideMem — identical;
  (iv) six N*₃ values 7/6/6/6/6/6 → Sp.n3NstarValues — identical;
  (v)  isSome == contains domain check → Sp.n3NstarDomain — identical;
  (vi) lengths 11 ∧ 2 → Sp.n3exclusionCards — identical.
NOTHING dropped, weakened, or reworded; docstring duties (field-size pass
"NECESSARY … NOT sufficient"; N*₃ gate-censused, never theorems; §0
realizability fence) moved to the shared group header, binding "on every
unit". Each unit now one display. ✓
CONTENT vs NOTE, computed: exclusion filters over the independently
re-derived 53-catalogue give |≥2 linears| = 11 = {R4c, R5c, R6▸(1,2),
R6▸(1,1) of {(1,2),(1,1)}, R6{(1,1)³}, the 5 Q3 copies, Q2.3c} and
|≥3| = 2 = {R6{(1,1)³}, Q3 copy} — exactly the note's "11 letters …
{(1,1)²}: R4, R5, Q3(R4), Q3(R5), Q2.3 (5); {(1,2),(1,1)}: … (4);
{(1,1)³}: … (2)" and "exactly the 2 letters with λ = {(1,1)³}". The six
multi-side literals: each transcribes its note row (Q3(R1) rf (1,1); Q3(R2);
Q3(R3) lf (1,1); three Q3(R4) λ-rows), each is a catalogue member of group
Q3, Nodup holds, d/slots match (2/Icc 0 1, 2/Icc 1 2, 2/Icc 2 3, 3/Icc 0 2
×3). N*₃ labels match "… N*_3 = 6; … N*_3 = 6; … N*_3 = 7" per copy.
ORDER DISCIPLINE re-audited: fieldSizeExcluded2/3 in catalogue3 order
(R4c < R5c < R6b12 < R6b11 < R6t < Q3-copies < Q23c; note's R6 row lists
▸(1,2) before ▸(1,1) before {(1,1)³} ✓). ✓ INTACT.

## 3. HARDEST ITEM (3): succ_terminal's hs / stageLaws_terminal asymmetry

The note's block is catalogue-scoped: "**Definition (Out; retyped at
rev 3).** For s ∈ 𝒮_n^raw, the OUTGOING MENU Out(s) ⊆ 𝒮_n^raw ∪ V_term …
and SUCC(s) := ∅ for terminal s (selection ⊥)." — the ∅-clause sits inside
"For s ∈ 𝒮_n^raw", so `hs : InCatalogue n s` on `succ_terminal` matches the
note's quantifier exactly (the C-3 pattern; hs faithfulness-only, unused by
the proof, as declared). `stageLaws_terminal` unrestricted is supported:
StageLaws is a blueprint-internal decomposition (the note has no bare-
StageLaws object outside the SUCC set-builder), and ¬StageLaws at sel = none
is definitional (the match's none-branch is False) — an internal lemma
asserting nothing note-facing; the C-4 precedent (helper kept, main
statement domain-restricted) applies. Consumers checked: n1singleton's step
case has InCatalogue available, so hs discharges. ✓

## 4. Spot-checks (8+, across layers, by computation where possible)

1. B/Sp.shExample: all seven Int values recomputed (fdiv floors): −1, 0, 1,
   0, 1, −2, 0 — match the note's verifier-example display exactly. ✓
2. B/Sp.shCongr: t·γ − s₀′ = e·(t·u₀ − s₀′·s) re-derived; ✓ vs (SH) block.
3. C/Sp.anchorBoundCensus: the (B5) ≤-chain matches "0 ≤ a ≤ ⌊(W − w′)/e⌋,
   a + ℓ ≤ ⌊W/e⌋ ≤ W ≤ n" + the e = 1 clause; ℕ-truncation safe under B3;
   a ≥ 0 free-in-ℕ recorded. ✓ (see NOTE B)
4. D/Sp.encodeCard: 1+3+5+(n+1)+n²+2+2n = n²+3n+12 ✓; card (Fin a → Fin b)
   = b^a ✓.
5. E/Sp.rankRadix: max rank = (((n−1)·3+2)·n+(n−1))·2+1 = 6n²−1 < 6n² ✓;
   digit bounds (D−1 < n, tagord < 3, n−W < n, bit < 2) all sourced. ✓
6. E/Sp.rankStepRec: the μ = W ∧ tagord = 2 branch via full_unique matches
   the note's third bullet verbatim; stages-match argument sound. ✓
7. F/Sp.compCollapsed: index bookkeeping walked (r+1 < m ≤ len keeps every
   hStage/hCoh antecedent strict); reads stay UNBOUNDED — the note's scope
   fence transposed, not violated. ✓
8. H/n3 layer, computed: closure = 53 (21/21/6/1/4); self-loops exactly
   {Q3{(1,3)}▸(1,3), Q2.3{(1,2)}▸(1,2)}, both postRec, order [loopQ3,
   loopQ23] correct in catalogue3 order; postInc all W = 1; the 5 terminal
   letters = Q1 ++ I with (G6) iff and empty menus; every non-root letter
   one SuccStep from group R (reachable3 TRUE); closure closed (no
   off-catalogue SuccStep target — menu3_exact_global's chain sound); root
   ▸(1,2) roster = exactly 3 (R4/R5/R6 rows — the §9/ERRATUM RECORD
   reading, which the note file itself now sanctions: "this record
   governs"); Q3 ▸(1,2) filter length = 3. ALL TRUE. ✓

## 5. Fresh sweep (all 67 units + the three def files)

Roster arithmetic: 61 − 1 (thresholdData) + 6 + 1 (n1Branch) = 67 ✓; groups
A5/B8/C4/D6/E11/F12/G3/H18 ✓; difficulty tallies 37/26/4 re-counted ✓. The
git diff confirms rev 5 = exactly the three declared repairs + bookkeeping
(no silent change; no stale live reference to n3thresholdData/n1Clause/
mcRoster — all remaining mentions are rev-history records). Defs layer
re-checked: Coherent/Budget/StageLaws/SuccStep/InCatalogue/Out transcribe
(G1)–(G6)/(B1)–(B5)/SP.4 faithfully (right-flank span stated additively,
avoiding ℕ-subtraction; B5's w′ ≤ n derivable within Budget from B3 + W ≤ n
— no constraint shrinkage); Bool routing clean (no Prop→Bool anywhere);
Nstar3six deliberately scoped to the six displayed computations ("per-NAME
table, none off multiSide6") — decides nothing the note leaves open; no
axioms; fence respected (no field mentions InCatalogue/Succ/Out); every
group-F unit names its riders, hVerdictPin's honest perimeter intact.
Units 1–67 swept individually against their moves_refs: quantifiers, side
conditions, edge cases (compEnum 0 = [[]], shDvd's no-e≥1 record, ℕ∞
prefixwise scope, hf/hdeg fidelity binders) — no defect found.

## Findings

CRITICAL: none.
GAP: none.
NOTE A (non-blocking, cosmetic): §0's SP-COMP bullet still enumerates the
interface fields as "(root stage, StageLaws, coherence/budgets, halt,
verdict pin)" — with hTotal (rev 4) and hN1 (rev 5) added, the parenthetical
under-enumerates §2's CanTreeModel. No checklist rule is broken (§2 is
authoritative and complete; hN1 is named in its consumer's
hypothesis_fields; hTotal is a discharged kernel) — suggest a one-line
touch-up if a future rev opens the file anyway.
NOTE B (observation, no action): anchorBoundCensus states (B5)'s normative
≤-chain and omits the shift-block's proof-internal identity a + ℓ =
⌊(s₀′ + w′)/e⌋ — correctly, since only the chain is (B5)'s display.

## Verdict

Counts: 0 critical / 0 gap (2 non-blocking notes).
ACCEPT
