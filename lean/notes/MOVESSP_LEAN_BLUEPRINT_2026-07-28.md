# MOVESSP LEAN BLUEPRINT (2026-07-28) — the §M-SPECIES corpus, unit specs

Campaign wave-1 blueprint (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md §5; unit-spec
format per §2). SOURCE OF TRUTH: `lean/notes/MOVES_2026-07-24.md`, the DUAL-ACCEPTED
rev-8 §M-SPECIES text (lines between `## §M-SPECIES` and `## §C: DUAL-ACCEPTED`;
acceptance record `## §M-SPECIES: DUAL-ACCEPTED (2026-07-27 — Codex pass 7 + the
Fable confirm ...)`). Every `moves_ref` below quotes that text. Corpus namespace
`LeanUrat.MovesSp`; files under `lean/LeanUrat/MovesSp/`.

## 0. Scope and conditionality (the note's own ledger, transposed)

DELIVERED BY THIS CORPUS (unconditional bookkeeping over ℕ/ℤ/Multiset — the note's
SP.5 ledger: "Unconditional given dual-accepted §B2-DEF (+ §C DOM via §D4-R L11 where
cited): SP.1's datum being well-typed, the (G1)–(G4) coherence, SP-FIN, SP-FIN′,
SP-OUT and its p-independence, the self-loop characterization, Lemma SP-DAG"):
the species datum structure; (G1)–(G6) + (B1)–(B5) as decidable predicates; the
closure 𝒮ₙ^raw; the shift map Sh + integrality; SP-FIN's catalogue bound; SP-DAG;
Out/V_term; the n = 3 layer (53 letters, menu map, loops) by `decide`.

CONDITIONAL, RIDING AS HYPOTHESES (never axioms, never silently strengthened):
- SP-COMP consumes the ENGINE (§B2-DEF D.4/D.5/D.7/D.8/D.10 read laws, §C DOM via
  §D4-R L11, §D4-R L2/L3/L5). Those live in Moves/MovesD/HC-1, not here. Lean form:
  an interface structure `EngineChain` whose FIELDS are exactly the per-read laws
  SP-COMP's proof steps (1)–(3′)/(5) derive from the engine; the corpus proves the
  closure absorbs any such chain. Discharging the fields = HC-1/MovesD territory.
- The D4R.0-K(c) residual (verdict pin: alphabet V + halting rule τ + detection cap,
  owner [3t] via VP) rides by OMISSION: `Verdict` is three bare labels, no semantics
  field anywhere; no unit states when a verdict fires. moves_ref: "V_term := { (z),
  (ep), (ns) } — §D4-R L5's terminal-verdict case labels, carried here as three bare
  LABELS."
- §C's (SAE): DISCHARGED (rev-14 dual acceptance) — no hypothesis needed; recorded.
- N*₃ threshold data: DEFINITIONS only (the note: gate-censused data + a SEALED
  PREDICTION, "not a theorem of this note"). No realizability theorem is stated.
- p-independence: discharged BY TYPING — `SnRaw : ℕ → Set Species` mentions no
  prime (the note: "no field of the datum ... mentions p — the same list serves
  every prime"). No unit; recorded here as the faithfulness witness.

NOT IN SCOPE (SP.5): counts/masses ([1]/[1v]/[3]); realizability at a given p
(menus are SUPERSETS — SP.4's superset duty); state types/geometry ([2b]); read/
depth/ladder bounds (SP-DAG bounds LETTERS only; TRACK-COUNT stays open, uncited);
termination.

## 1. Design decisions (the decidable layer)

1. **Species = one flat structure over ℕ/Multiset/List, `deriving DecidableEq`.**
   Fields exactly SP.1's retained tuple: tag, stage (D, w, W), side (e, s₀′, ℓ,
   census anchor a, digit count d, slot Finset), λ (Multiset (ℕ × ℕ)), selection
   (Option (ℕ × ℕ) — ⊥ = none, per the rev-3 retype "verdicts are NOT species"),
   two flank compositions (List ℕ). a/d/slots are FIELDS with (G2)/(G3) as
   RELATIONS (faithful to the note's tuple + coherence split), not derived defs.
   Heights (h_r, u*_r), depths, digit values: ABSENT — the note's FORGOTTEN list.
2. **Coherent/Budget/SuccStep as plain `Prop` conjunctions/matches, all decidable
   without instance gymnastics**, PLUS Bool reflection functions (`coherentB` etc.)
   with soundness iffs, so n = 3 facts kernel-`decide` over Bool — `native_decide`
   is BANNED (axiom fence: `Lean.ofReduceBool` is outside the allowed set).
3. **𝒮ₙ^raw as an inductive Prop closure** (`InCatalogue`): least set containing the
   coherent+admissible ROOT-stage tuples, closed under SuccStep — literally the
   rev-3 definition. Finiteness/decidability recovered via (a) the SP-FIN encoding
   injection, (b) a GENERATED enumeration `speciesEnum n : List Species` (coherent-
   by-construction candidates; a/d/slots computed from (s₀′, e, ℓ)) with a
   completeness lemma, making the n = 3 catalogue equality a closure induction over
   `decide`-checked base/step facts.
4. **Two coordinate systems**: census fields live in the letter; the shift block is
   a pure-ℤ lemma family (`Int.fdiv`, e ≥ 1) with hypotheses NAMED to match
   `Moves.Stage` (e h s t, hbez, he1t) + one bridging corollary consuming an actual
   `σ : Moves.Stage p F` (reuse, not duplication — the only Stage-typed unit).
   `R_anch` shift-invariance reuses `Moves.HasAnchorK` verbatim.
5. **Rank for SP-DAG as a mixed-radix ℕ** (order-isomorphic to the note's lex
   4-tuple on the bounded ranges), so the collapsed-walk bound is "strictly
   increasing ℕ-list below 6n² has length ≤ 6n²".
6. **Perf fences for `decide`**: enum generated with dependent bounds (n = 3 raw
   size ~2–3k, letters' numerals ≤ 7); decide targets phrased as `List.all … =
   true`; the three enum-quantified checks split PER STAGE GROUP (R/Q3/Q2/Q1/I) if
   a single decide exceeds ~60s kernel time. Fallback beyond that: designer round
   (statement-fence: additive helper lemmas only). NEVER native_decide.

## 2. Proposed `MovesSp/Defs.lean` skeleton (structures/defs only, no proofs)

```lean
import Mathlib
import LeanUrat.Moves.Defs   -- reuse: HasAnchorK, Stage (bridging unit only)

namespace LeanUrat.MovesSp

/-- (tag) the read's position class (SP.1): ROOT / POST-INC / POST-REC. -/
inductive Tag | root | postInc | postRec deriving DecidableEq, Repr

/-- SP.1's species datum: the retained, value-free, height-free fields of one read.
Heights (h_r, u*_r), depths, digit values, lifts: FORGOTTEN by design. -/
structure Species where
  tag : Tag
  D : ℕ            -- current key degree
  w : ℕ            -- pool residue degree
  W : ℕ            -- window width
  e : ℕ            -- stride e = e_read
  s0 : ℕ           -- raw left endpoint s₀′
  ell : ℕ          -- normalized side length ℓ = w′/e = deg R_anch
  a : ℕ            -- CENSUS anchor ⌊s₀′/e⌋  ((SH-C); (G2) is the relation)
  d : ℕ            -- digit count = #slots   ((G3) pins d = ℓ + 1)
  slots : Finset ℕ -- census slot set {p̂_k} ((G3) pins {a, …, a+ℓ})
  lam : Multiset (ℕ × ℕ)   -- residual partition λ = {(g⁽ⁱ⁾, μ⁽ⁱ⁾)}
  sel : Option (ℕ × ℕ)     -- selection (g, μ) ∈ λ, or ⊥ = none (rev-3 retype)
  lflank : List ℕ  -- left flank composition (composition of span s₀′)
  rflank : List ℕ  -- right flank composition (span W − s₀′ − w′)
deriving DecidableEq, Repr

namespace Species
/-- raw side width w′ = e·ℓ. -/
def wraw (s : Species) : ℕ := s.e * s.ell
end Species

/-- `c` is a composition of `span`: positive parts summing to `span` ([] ↔ span 0). -/
def IsComposition (c : List ℕ) (span : ℕ) : Prop := (∀ x ∈ c, 1 ≤ x) ∧ c.sum = span

/-- Structural positivity (typing: D, w, W, e, ℓ ≥ 1; λ-parts positive). -/
def WellTyped (s : Species) : Prop :=
  1 ≤ s.D ∧ 1 ≤ s.w ∧ 1 ≤ s.W ∧ 1 ≤ s.e ∧ 1 ≤ s.ell ∧
    ∀ gm ∈ s.lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2

/-- (G1)–(G4)+(G6), stated in CENSUS coordinates (rev 4). (G5) is `SuccStep`. -/
def Coherent (s : Species) : Prop :=
  WellTyped s ∧
  -- (G1) FLANK–SPAN: left span = s₀′; s₀′ + w′ + right span = W
  (IsComposition s.lflank s.s0 ∧ s.s0 + s.wraw + s.rflank.sum = s.W ∧
     ∀ x ∈ s.rflank, 1 ≤ x) ∧
  -- (G2) ANCHOR–POSITION (census): a = ⌊s₀′/e⌋
  (s.a = s.s0 / s.e) ∧
  -- (G3) SLOT-SET: {p̂_k} = {a, …, a+ℓ}, d = ℓ + 1
  (s.slots = Finset.Icc s.a (s.a + s.ell) ∧ s.d = s.ell + 1) ∧
  -- (G4) RESIDUAL–SELECTION: Σ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ; selection ∈ λ or ⊥
  ((s.lam.map fun gm => gm.1 * gm.2).sum = s.ell ∧
     ∀ gm, s.sel = some gm → gm ∈ s.lam) ∧
  -- (G6) TERMINAL RULE: selection = ⊥ iff W = 1
  (s.sel = none ↔ s.W = 1)

/-- (B1)–(B5), the PER-TUPLE budget clauses ((B1)/(B2)'s recursions live in
`SuccStep`; the anchor clause is the rev-3/4 CENSUS bound). -/
def Budget (n : ℕ) (s : Species) : Prop :=
  s.D ≤ n ∧ s.w ≤ n ∧                                     -- (B1)/(B2) caps
  (s.s0 + s.wraw ≤ s.W ∧ s.a + s.ell ≤ s.W ∧
     s.d ≤ s.wraw + 1 ∧ s.W ≤ n / s.D) ∧                  -- (B3)
  (∀ gm, s.sel = some gm → gm.1 * gm.2 ≤ s.ell) ∧          -- (B4)
  (s.e ≤ n ∧ s.ell ≤ n ∧ s.s0 ≤ n ∧ s.d ≤ n + 1 ∧ s.W ≤ n ∧
     (∀ gm ∈ s.lam, gm.1 ≤ n ∧ gm.2 ≤ n) ∧
     s.e ≤ s.wraw ∧ s.a ≤ (s.W - s.wraw) / s.e)            -- (B5, census anchor)

/-- ROOT stage pin ((G5) root clause): tag = ROOT forces (D, w, W) = (1, 1, n). -/
def RootStage (n : ℕ) (s : Species) : Prop :=
  s.tag = .root ∧ s.D = 1 ∧ s.w = 1 ∧ s.W = n

def RootAdmissible (n : ℕ) (s : Species) : Prop :=
  RootStage n s ∧ Coherent s ∧ Budget n s

/-- SP.4's SUCC clause = (G5)'s generation rule: stage laws D′ = e·g·D, w′ = g·w,
W′ = μ; tag′ = POST-INC iff e·g ≥ 2, POST-REC iff e = g = 1; target coherent and
budget-admissible. `match` (not ∃) keeps it decidable. -/
def SuccStep (n : ℕ) (s s' : Species) : Prop :=
  match s.sel with
  | none => False
  | some (g, μ) =>
      s'.D = s.e * g * s.D ∧ s'.w = g * s.w ∧ s'.W = μ ∧
      (s'.tag = .postInc ↔ 2 ≤ s.e * g) ∧
      (s'.tag = .postRec ↔ (s.e = 1 ∧ g = 1)) ∧
      Coherent s' ∧ Budget n s'

/-- 𝒮ₙ^raw (rev 3): the LEAST set containing every coherent, admissible ROOT-stage
tuple, closed under (G5)'s generation rule — an inductive Prop closure. -/
inductive InCatalogue (n : ℕ) : Species → Prop
  | root {s} : RootAdmissible n s → InCatalogue n s
  | step {s s'} : InCatalogue n s → SuccStep n s s' → InCatalogue n s'

def SnRaw (n : ℕ) : Set Species := {s | InCatalogue n s}

/-- V_term (SP.4, rev 3): three BARE labels, disjoint from Species. No fields, no
budgets, no menus; semantics owned by [3t]'s VP — deliberately absent here. -/
inductive Verdict | z | ep | ns deriving DecidableEq, Repr

/-- SUCC(s) ⊆ 𝒮ₙ^raw (SP.4); ∅ for terminal s (sel = none ⇒ SuccStep is False). -/
def Succ (n : ℕ) (s : Species) : Set Species :=
  {s' | InCatalogue n s' ∧ SuccStep n s s'}

/-- Out(s) := SUCC(s) ∪ V_term (disjoint union via Sum). -/
def Out (n : ℕ) (s : Species) : Set (Species ⊕ Verdict) :=
  (Sum.inl '' Succ n s) ∪ (Sum.inr '' Set.univ)

/-! ### The two coordinate systems and the shift map (SP.1's shift block) -/

/-- σ := ⌊t·γ/e⌋ (floor division: `Int.fdiv`). -/
def shSigma (t γ e : ℤ) : ℤ := (t * γ).fdiv e

/-- (SH) Sh_{t,γ} : ℤ → ℤ, p ↦ p + σ. -/
def Sh (t γ e : ℤ) (pz : ℤ) : ℤ := pz + shSigma t γ e

/-- (SH-G) the geometric position p_j(γ) = (j − t·γ)/e (D.3(c)); exact division on
on-line slots (the integrality lemma), `fdiv` as the total function. -/
def geoPos (e t γ j : ℤ) : ℤ := (j - t * γ).fdiv e

/-! ### SP-DAG rank and fullness -/

def tagord : Tag → ℕ | .root => 0 | .postInc => 1 | .postRec => 2

/-- FULL letter (SP-DAG): selection = (1, W). By (G6) full letters live at W ≥ 2. -/
def IsFull (s : Species) : Prop := s.sel = some (1, s.W)

/-- ρ(s) = (D, tagord, n − W, 1 − [full]) as a mixed-radix ℕ, order-isomorphic to
the note's lex tuple on catalogue ranges (D ∈ [1,n], tagord < 3, n − W < n,
bit < 2); rankNat < 6n² on catalogue members. -/
def rankNat (n : ℕ) (s : Species) : ℕ :=
  (((s.D - 1) * 3 + tagord s.tag) * n + (n - s.W)) * 2 +
    (if s.sel = some (1, s.W) then 0 else 1)

/-- A collapsed walk: consecutive SuccStep edges with self-loops struck (rev 3:
"the collapsed LETTER length of a walk"). -/
def CollapsedWalk (n : ℕ) (l : List Species) : Prop :=
  (∀ s ∈ l, InCatalogue n s) ∧ l.Chain' (fun s s' => SuccStep n s s' ∧ s ≠ s')

/-! ### SP-COMP interface (the conditionality carrier — §0) -/

/-- The per-read data of one engine chain, as SP-COMP's proof steps (1)–(3′)/(5)
DERIVE them from §B2-DEF/§C DOM/§D4-R. Fields = the open engine laws; discharging
them against `Moves.Stage` runs is HC-1/MovesD territory. Verdict semantics
(D4R.0-K(c)/VP) deliberately absent. -/
structure EngineChain (n : ℕ) where
  word : List Species
  hne : word ≠ []
  /-- step (1)+(3)+(3′): the r = 0 read is a coherent admissible ROOT-stage tuple. -/
  hRoot : ∀ s, word.head? = some s → RootAdmissible n s
  /-- steps (2)+(3)+(3′)+(5): consecutive reads obey the D.7/D.8/D.10 stage laws
  and each new read's datum is coherent and budget-admissible. -/
  hStep : word.Chain' (SuccStep n)

/-- A CATALOGUE WORD (SP-COMP's quantifier + SP.4's HALT CONVENTION): reads through
the FIRST confirming W = 1 read — only the last letter may be terminal. -/
structure CatalogueWord (n : ℕ) extends EngineChain n where
  hClose : ∀ s ∈ word.dropLast, s.sel ≠ none

/-- The τ-WORD: the catalogue word minus its final confirming letter (SP.4; at
n = 1 the empty word). -/
def CatalogueWord.tauWord {n : ℕ} (cw : CatalogueWord n) : List Species :=
  cw.word.dropLast

/-! ### CTS bridge + the (m, c)-relevant roster fields -/

/-- The plan's bounded current-state skeleton (SP.4 bridge, typing only):
(tower phase, stage, anchor, residual partition) — values forgotten. -/
def stateSkeleton (s : Species) : Tag × (ℕ × ℕ × ℕ) × ℕ × Multiset (ℕ × ℕ) :=
  (s.tag, (s.D, s.w, s.W), s.a, s.lam)

/-- m := member count of the read's outcome (one member per λ-factor). -/
def mOf (s : Species) : ℕ := Multiset.card s.lam

/-- c := continuing-member count: members with μ ≥ 2 ((G6): μ = 1 children open a
W = 1 confirming window, hence halt; semantics of halting = VP's, cited as owner). -/
def cOf (s : Species) : ℕ := Multiset.card (s.lam.filter fun gm => 2 ≤ gm.2)

/-- §S-RESUM (K-SUB)'s (m, c) CLASSIFICATION rows, as bookkeeping labels:
terminal-fin (c = 0, any m) / continuing (c = 1, m = 1) / branching (c ≥ 1, m ≥ 2). -/
inductive OutcomeClass | terminalFin | continuing | branching deriving DecidableEq, Repr

def outcomeClass (s : Species) : OutcomeClass :=
  if cOf s = 0 then .terminalFin else if mOf s = 1 then .continuing else .branching

end LeanUrat.MovesSp
```

Bool reflection (`coherentB budgetB rootAdmissibleB succStepB : … → Bool`, literal
Bool transcriptions) and the generated enumeration (`compEnum : ℕ → List (List ℕ)`,
`lamEnum : ℕ → ℕ → List (Multiset (ℕ × ℕ))` [bound n, weight ℓ], `speciesEnum : ℕ →
List Species`) live in `MovesSp/DefsEnum.lean`; the n = 3 letters + data tables in
`MovesSp/DefsN3.lean` (§4 below).

## 3. `MovesSp/DefsEnum.lean` sketch (defs only)

```lean
/-- All compositions of `span` (positive parts, ordered). compEnum 0 = [[]]. -/
def compEnum : ℕ → List (List ℕ)          -- recursion on span
/-- All multisets of pairs (g, μ), 1 ≤ g, μ ≤ bound, with Σ g·μ = weight. -/
def lamEnum (bound weight : ℕ) : List (Multiset (ℕ × ℕ))
/-- Generated candidates: for tag/D/w/W/e/s0/ell in dependent bounds, lam ∈ lamEnum,
sel ∈ none :: (lam.toList.map some), flanks ∈ compEnum; a := s0/e, d := ell + 1,
slots := Finset.Icc a (a + ell) COMPUTED (coherent-by-construction on (G2)/(G3)). -/
def speciesEnum (n : ℕ) : List Species
def coherentB (s : Species) : Bool
def budgetB (n : ℕ) (s : Species) : Bool
def rootAdmissibleB (n : ℕ) (s : Species) : Bool
def succStepB (n : ℕ) (s s' : Species) : Bool
```

## 4. `MovesSp/DefsN3.lean` sketch (defs only — the SEALED n = 3 data)

```lean
/-- The 53 letters (SP.6's hand catalogue, exhaustive; grouped R/Q3/Q2/Q1/I).
Helper constructors keep each row one line (e.g. `mkRoot e s0 ell lam sel lf rf`). -/
def groupR : List Species    -- 21 rows: R1..R8 with flank/λ▸sel variants
def groupQ3 : List Species   -- 21: the R rows retagged postRec, stage (1,1,3)
def groupQ2 : List Species   -- 6: Q2.1, Q2.2, Q2.3 (3 λ▸sel rows), Q2.4
def groupQ1 : List Species   -- 1: confirming ⊥ letter, stage (1,1,1)
def groupI  : List Species   -- 4: confirming ⊥ letters, stages (2,1),(2,2),(3,1),(3,3), W = 1
def catalogue3 : List Species := groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI
/-- The sealed menu map (SP.6): ▸(1,1)→Q1; ▸(1,2)→Q2; ▸(1,3)→Q3; ▸(2,1)→I(2,2);
▸(3,1)→I(3,3); e=2→I(2,1); e=3→I(3,1); terminal→[]. By selection/stride match. -/
def menuMap3 (s : Species) : List Species
def loopQ23 : Species := ...   -- Q2.3's {(1,2)}▸(1,2) row
def loopQ3  : Species := ...   -- Q3(R6)'s {(1,3)}▸(1,3) row
/-- Field-size exclusion lists (SP.6 threshold clause (1), sealed): 11 letters at
p = 2 (λ ⊇ two distinct linears / {(1,2),(1,1)} / {(1,1)³}); 2 at p = 3 ({(1,1)³}). -/
def fieldSizeExcluded2 : List Species   -- 11
def fieldSizeExcluded3 : List Species   -- 2
/-- The six multi-side μ = 3 letters (the N*₃ exceptions). -/
def multiSide6 : List Species
/-- N*₃ on the six (SP.6's SIX COMPUTATIONS): Q3(R4)-copies ↦ 6 (three), Q3(R2)/
Q3(R3) ↦ 6, Q3(R1) ↦ 7. Elsewhere: the note pins only N*₃ ≤ 5 (census), carried as
a Prop-free comment — NOT a def (no per-letter values are displayed). -/
def Nstar3six : Species → Option ℕ
```

## 5. Unit specs

Format per campaign §2: id · file (`lean/LeanUrat/MovesSp/<id>.lean`) · statement ·
moves_ref (≤ 3 lines, from the rev-8 text) · deps (Defs* always implicit) · sketch ·
difficulty · hypothesis_fields (DEFAULT: none — unconditional bookkeeping per SP.5's
ledger; only deviations are listed).

### A. Reflection and closure basics

**Sp.reflCoherent** · SP0_reflCoherent.lean
statement: `theorem coherentB_iff (s : Species) : coherentB s = true ↔ Coherent s`
moves_ref: "(G1)–(G6) … A species tuple is GEOMETRICALLY COHERENT iff" (the display).
deps: — · sketch: unfold both; `decide`-friendly Bool/Prop transcription, `simp
[coherentB, Coherent, List.all_eq_true, …]`. · difficulty: easy

**Sp.reflBudget** · SP0_reflBudget.lean
statement: `theorem budgetB_iff (n : ℕ) (s : Species) : budgetB n s = true ↔ Budget n s`
moves_ref: "(B1)–(B5) are inequalities between INTEGERS attached to shape fields".
deps: — · sketch: as reflCoherent. · difficulty: easy

**Sp.reflSucc** · SP0_reflSucc.lean
statement: `theorem succStepB_iff (n : ℕ) (s s' : Species) : succStepB n s s' = true
↔ SuccStep n s s'` and `theorem rootAdmissibleB_iff (n s) : … ↔ RootAdmissible n s`
moves_ref: "SUCC(s) := { s′ ∈ 𝒮_n^raw : D(s′) = e·g·D, w(s′) = g·w, W(s′) = μ, …}".
deps: Sp.reflCoherent, Sp.reflBudget · sketch: match on sel; conjunction transport.
difficulty: easy

**Sp.succTerminal** · SP0_succTerminal.lean
statement: `theorem succ_terminal (n : ℕ) (s : Species) (h : s.sel = none) :
Succ n s = ∅` (and `¬ SuccStep n s s'`)
moves_ref: "and SUCC(s) := ∅ for terminal s (selection ⊥)."
deps: — · sketch: unfold SuccStep, rewrite h, exact False.elim. · difficulty: easy

**Sp.memCoherent** · SP0_memCoherent.lean
statement: `theorem InCatalogue.coherent_budget {n s} (h : InCatalogue n s) :
Coherent s ∧ Budget n s`
moves_ref: "the least set … that contains every (G1)–(G4)+(G6)-coherent,
(B1)–(B5)-admissible ROOT-stage tuple … (each generated tuple again … admissible)".
deps: — · sketch: induction on h; both constructors carry the conjuncts.
difficulty: easy

### B. The two coordinate systems and the shift map (SP.1's shift block)

Pure-ℤ units; hypothesis names mirror `Moves.Stage` fields (hbez ↔ `hbez`, e = 1 ⇒
t = 0 ↔ `he1t`) so the bridging unit is verbatim.

**Sp.shCongr** · SP1_shCongr.lean
statement: `theorem sh_congr (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
(hγ : γ = e * u0 + s0 * h) : t * γ ≡ s0 [ZMOD e]`
moves_ref: "with u₀ := the left endpoint's height, γ = e·u₀ + s₀′·h, so modulo e
t·γ ≡ t·h·s₀′ ≡ (1 − e·s)·s₀′ ≡ s₀′".
deps: — · sketch: substitute hγ; t·γ − s₀′ = e·(t·u0) + s₀′·(t·h − 1) =
e·(t·u0 − s₀′·s); `Int.ModEq` via dvd, `ring_nf`. · difficulty: easy

**Sp.shDvd** · SP1_shDvd.lean
statement: `theorem sh_dvd (…same hyps…) (k : ℤ) : e ∣ (s0 + k * e - t * γ)`
moves_ref: "(SH-G) p_j(γ) = (j − t·γ)/e ∈ ℤ (D.3(c))" [j = j_k = s₀′ + k·e].
deps: Sp.shCongr · sketch: s0 − t·γ ≡ 0 [ZMOD e] from shCongr; add k·e.
difficulty: easy

**Sp.shSlots** · SP1_shSlots.lean
statement: `theorem sh_slots (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e) (hbez : …)
(hγ : …) (k : ℤ) : Sh t γ e (geoPos e t γ (s0 + k * e)) = s0.fdiv e + k` and
`theorem sh_anchor : Sh t γ e (geoPos e t γ s0) = s0.fdiv e`
moves_ref: "p_{j_k} + σ = (j_k − t·γ)/e + (t·γ − (s₀′ mod e))/e = … = ⌊s₀′/e⌋ + k;
k = 0 is the anchor identity."
deps: Sp.shDvd · sketch: fdiv-additivity on the exact divisions (shDvd + the σ
congruence give both remainders); `Int.add_mul_fdiv_right`, `omega` after
extracting the two dvd witnesses. · difficulty: medium

**Sp.shE1** · SP1_shE1.lean
statement: `theorem sh_e1 (h s t γ s0 : ℤ) (ht : t = 0) :
shSigma t γ 1 = 0 ∧ Sh t γ 1 (geoPos 1 t γ s0) = s0`
moves_ref: "At e = 1: t = 0 ((P2)), σ = 0 — THE SYSTEMS COINCIDE (a = a^geo = s₀′
= ord_z R; FC4's e = 1 clause)."
deps: — · sketch: `simp [shSigma, Sh, geoPos, Int.fdiv_one, ht]`. · difficulty: easy

**Sp.shEquiv** · SP1_shEquiv.lean
statement: `def shEquiv (σ : ℤ) : ℤ ≃ ℤ := Equiv.addRight σ` +
`theorem sh_image (t γ e ag : ℤ) (ℓ : ℕ) (hσ : … the slot identities of Sp.shSlots) :
(Finset.Icc ag (ag + ℓ)).image (Sh t γ e) = Finset.Icc (ag + shSigma t γ e)
(ag + shSigma t γ e + ℓ)`
moves_ref: "Sh_{t,γ} is an affine bijection carrying the geometric slot set onto
the census slot set and a^geo onto a, ALL OTHER FIELDS FIXED".
deps: — · sketch: `Finset.image_add_right_Icc`; the census identification then
rides on Sp.shSlots. · difficulty: easy

**Sp.shAnchorInv** · SP1_shAnchorInv.lean
statement: `theorem hasAnchorK_T_mul {K : Type*} [Field K] (x : LaurentPolynomial K)
(a σ : ℤ) (R : Polynomial K) (h : Moves.HasAnchorK x a R) :
Moves.HasAnchorK (LaurentPolynomial.T σ * x) (a + σ) R`
moves_ref: "the anchored residual is SHIFT-INVARIANT: R_anch := z^{−ord_z R}·R =
Σ_k c_{j_k}·z^k in BOTH displays (relabeling p ↦ p + σ multiplies R by z^σ, which
the anchoring cancels), so λ, the selection, and ℓ = deg R_anch never see σ."
deps: — (REUSES `Moves.HasAnchorK` — the corpus-link unit) · sketch: unfold
HasAnchorK; `LaurentPolynomial.T_add`, `mul_assoc`. · difficulty: medium

**Sp.shStage** · SP1_shStage.lean
statement: `theorem sh_congr_stage {p F} [Fact p.Prime] [Field F] [Finite F]
(σs : Moves.Stage p F) (γ u0 s0 : ℤ) (hγ : γ = σs.e * u0 + s0 * σs.h) :
σs.t * γ ≡ s0 [ZMOD σs.e]` + the e = 1 corollary via `σs.he1t`
moves_ref: "At a stage with read index (e, h) and pinned Bézout pair (s, t)
(e·s + t·h = 1; (P2): t = 0 at e = 1)".
deps: Sp.shCongr, Sp.shE1 · sketch: instantiate at (σs.e, σs.h, σs.s, σs.t) via
σs.hbez (mind the ℕ→ℤ casts). · difficulty: easy

**Sp.shExample** · SP1_shExample.lean
statement: `example : geoPos 2 1 3 1 = -1 ∧ geoPos 2 1 3 3 = 0 ∧ shSigma 1 3 2 = 1
∧ Sh 1 3 2 (-1) = 0 ∧ Sh 1 3 2 0 = 1 ∧ shSigma (-1) 3 2 = -2 ∧
Sh (-1) 3 2 (geoPos 2 (-1) 3 1) = 0 := by decide` (named theorem)
moves_ref: "THE VERIFIER'S EXAMPLE (pass-2 C1) … GEOMETRIC: p₁ = (1 − 3)/2 = −1,
p₃ = (3 − 3)/2 = 0 … CENSUS: a = ⌊1/2⌋ = 0 … BÉZOUT CHECK: (s, t) = (1, −1) …
σ = ⌊−3/2⌋ = −2 — the same census image ✓".
deps: — · sketch: `decide` (Int literals). · difficulty: easy

### C. Coherence/budget consequences

**Sp.anchorBoundCensus** · SP1_anchorBound.lean
statement: `theorem anchor_bound {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) : s.a ≤ (s.W - s.wraw) / s.e ∧ s.a + s.ell ≤ s.W / s.e ∧
s.W / s.e ≤ s.W ∧ s.W ≤ n ∧ (s.e = 1 → s.a = s.s0 ∧ s.a ≤ s.W - s.wraw)`
moves_ref: "from (B3)'s 0 ≤ s₀′ ≤ W − w′ and floor-monotonicity, 0 ≤ a ≤
⌊(W − w′)/e⌋, a + ℓ = ⌊(s₀′ + w′)/e⌋ ≤ ⌊W/e⌋ ≤ W ≤ n" (+ "At e = 1 the two
statements are ONE: 0 ≤ a = a^geo ≤ W − w′").
deps: — · sketch: (G2) a = s0/e; Nat.div_le_div_right on s0 ≤ W − w′; for a + ℓ:
a + ℓ ≤ (s0 + e·ℓ)/e (Nat.add_div_right arithmetic) ≤ W/e; Nat.div_le_self.
NOTE: a ≥ 0 is free in ℕ (the note's 0 ≤ a). · difficulty: medium

**Sp.anchorBoundGeo** · SP1_anchorBoundGeo.lean
statement: `theorem anchor_bound_geo {n} {s : Species} (hc : Coherent s)
(hb : Budget n s) (σ ageo : ℤ) (hshift : (s.a : ℤ) = ageo + σ) :
-σ ≤ ageo ∧ ageo ≤ ((s.W - s.wraw) / s.e : ℕ) - σ`
moves_ref: "GEOMETRIC IMAGE (through Sh⁻¹, per realized read): −σ ≤ a^geo ≤
⌊(W − w′)/e⌋ − σ with σ = ⌊tγ/e⌋ — height- and Bézout-dependent, hence NOT a
species-level bound".
deps: Sp.anchorBoundCensus · sketch: rearrange hshift with 0 ≤ a ≤ bound; omega.
difficulty: easy

**Sp.g6Forcing** · SP1_g6Forcing.lean
statement: `theorem w1_forces {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
(hW : s.W = 1) : s.e = 1 ∧ s.ell = 1 ∧ s.s0 = 0 ∧ s.a = 0 ∧ s.lam = {(1,1)} ∧
s.lflank = [] ∧ s.rflank = [] ∧ s.sel = none`
moves_ref: "(G6) TERMINAL RULE: selection = ⊥ iff W = 1. [A W = 1 window forces
the whole side datum — e = ℓ = 1, s₀′ = a = 0, λ = {(1,1)}, no flanks —]".
deps: — · sketch: s0 + e·ℓ ≤ 1 with e, ℓ ≥ 1 pins e = ℓ = 1, s0 = 0; a = 0/1 = 0;
Σ gμ = 1 with positive parts pins λ singleton (1,1) (Multiset: sum-1 with parts
≥ 1 ⇒ one part of weight 1 ⇒ g = μ = 1); flanks: compositions of span 0; sel by
(G6)→. Multiset step: induction/`Multiset.sum_eq_zero` on the erase. · difficulty: medium

**Sp.b4Derived** · SP2_b4Derived.lean
statement: `theorem egμD_le {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
{g μ : ℕ} (hsel : s.sel = some (g, μ)) : s.e * g * μ * s.D ≤ s.wraw * s.D ∧
s.wraw * s.D ≤ n`
moves_ref: "(B4) … hence the Σ eᵢgᵢμᵢ-type constraint e_r·g_r·μ_r·D_r ≤
e_r·ℓ_r·D_r = w′_r·D_r ≤ n."
deps: — · sketch: g·μ ≤ ℓ (B4) scaled by e·D; w′ ≤ W ≤ n/D (B3) ⇒ w′·D ≤ n
(Nat.div: W ≤ n/D → W·D ≤ n via Nat.le_div_iff_mul_le, D ≥ 1). · difficulty: easy

### D. SP-FIN — the catalogue bound (SP.2)

Code type: `Code n := Fin (n^2 + 3*n + 12) → Fin (n + 2)`, entries in the note's
order (tag 1; D w W 3; e ℓ a s₀′ d 5; slot indicator n+1; λ-matrix n²; sel 2;
flank cut-set indicators 2n). Needs `hn : 1 ≤ n` (the note: "n + 2 ≥ 3 for every
n ≥ 1" — the tag entry).

**Sp.compEncode** · SP2_compEncode.lean
statement: `def compCuts (c : List ℕ) : Finset ℕ` (partial-sum cut set) +
`theorem compCuts_inj {span} {c c' : List ℕ} (h : IsComposition c span)
(h' : IsComposition c' span) (he : compCuts c = compCuts c') : c = c'`
moves_ref: "the two flank compositions as indicator vectors of their cut sets
(≤ 2n entries, spans ≤ n by (B5))."
deps: — · sketch: partial sums of a positive composition are strictly monotone;
recover parts as gaps of the sorted cut set; induction on lists. · difficulty: medium

**Sp.lamEncode** · SP2_lamEncode.lean
statement: `theorem lam_count_inj {lam lam' : Multiset (ℕ × ℕ)}
(h : ∀ x, Multiset.count x lam = Multiset.count x lam') : lam = lam'` (Mathlib
`Multiset.ext`) specialized to the bounded matrix: `def lamMatrix (n) (lam) :
(Fin n × Fin n) → ℕ` + injectivity on part-bounded λ.
moves_ref: "λ as its multiplicity matrix c : {1..n}² → {0..n} with c(g, μ) := the
number of factors of shape (g, μ) (n² entries; (B4) forces Σ g·μ·c(g,μ) = ℓ ≤ n)".
deps: — · sketch: Multiset.ext + the (B5) part bound to shift indices into Fin n;
counts ≤ card ≤ ℓ ≤ n gives the {0..n} entry range. · difficulty: medium

**Sp.encodeInj** · SP2_encodeInj.lean
statement: `def encode (n : ℕ) (hn : 1 ≤ n) (s : Species) : Code n` +
`theorem encode_inj {n hn} {s s' : Species} (hs : Coherent s ∧ Budget n s)
(hs' : Coherent s' ∧ Budget n s') (h : encode n hn s = encode n hn s') : s = s'`
moves_ref: "Every species tuple is determined by an integer vector with all
entries in {0, 1, …, n+1} … Total length ≤ 1 + 3 + 5 + (n+1) + n² + 2 + 2n =
n² + 3n + 12, each entry taking ≤ n + 2 values".
deps: Sp.compEncode, Sp.lamEncode · sketch: field-by-field recovery: scalar
entries in range by (B5) (d ≤ n+1 the widened entry); λ via lamMatrix; sel via
the reserved (0,0) pair (WellTyped parts ≥ 1 keep it disjoint); flanks via
compCuts + spans s0 / W − s0 − w′ recovered from scalar entries; slots redundant
("kept for crudeness"). · difficulty: medium-hard (split candidate: scalar-block
recovery vs flank/λ blocks if > ~40 lines)

**Sp.encodeCard** · SP2_encodeCard.lean
statement: `theorem code_card (n : ℕ) : Nat.card (Code n) = (n+2)^(n^2 + 3*n + 12)`
moves_ref: "Hence the displayed bound." [|𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}]
deps: — · sketch: `Nat.card_fun`/`Fintype.card_fun`, card of Fin. · difficulty: easy

**Sp.finThm** · SP2_finThm.lean
statement: `theorem SP_FIN (n : ℕ) (hn : 1 ≤ n) : (SnRaw n).Finite ∧
Nat.card (SnRaw n) ≤ (n+2)^(n^2 + 3*n + 12)`
moves_ref: "Theorem SP-FIN. 𝒮_n^raw is FINITE and INDEPENDENT of p, with the
explicit (crude) bound |𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}."
deps: Sp.memCoherent, Sp.encodeInj, Sp.encodeCard · sketch: SnRaw ⊆ the coherent-
admissible set; encode injective there; `Set.Finite.of_finite_image`/
`Nat.card_le_card_of_injective`. p-INDEPENDENCE: by typing (§0) — record in the
docstring, no clause. · difficulty: medium

**Sp.finWords** · SP2_finWords.lean
statement: `theorem SP_FIN' (n L : ℕ) (hn : 1 ≤ n) : {w : List Species |
w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n}.Finite ∧ Nat.card {…} ≤
(Nat.card (SnRaw n))^L`
moves_ref: "Corollary SP-FIN′ (words). For every L, the set of length-L words
over 𝒮_n^raw is finite, of size ≤ |𝒮_n^raw|^L".
deps: Sp.finThm · sketch: inject into `Fin L → SnRaw-subtype` via get; standard
`List.injective` bookkeeping (`List.ext_get`). · difficulty: medium

### E. SP-OUT, self-loops, Lemma SP-DAG (SP.4)

**Sp.outFinite** · SP4_outFinite.lean
statement: `theorem out_finite (n : ℕ) (hn : 1 ≤ n) (s : Species) :
(Out n s).Finite ∧ Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3`
moves_ref: "FINITENESS: |Out(s)| ≤ |𝒮_n^raw| + 3 by SP-FIN."
deps: Sp.finThm · sketch: Succ n s ⊆ SnRaw n; union card ≤ sum; card Verdict = 3
(`Fintype` on the 3-label inductive). · difficulty: easy

**Sp.selfloopChar** · SP4_selfloopChar.lean
statement: `theorem selfloop_iff {n} {s : Species} (hc : Coherent s)
(hb : Budget n s) : SuccStep n s s ↔ (s.tag = .postRec ∧ s.e = 1 ∧
s.sel = some (1, s.W))`
moves_ref: "s has a self-loop edge iff s ∈ SUCC(s): necessarily e = g = 1 (else D
grows strictly, (B1)) with W(s) = μ(s) — the POST-REC species whose window equals
their own selection multiplicity."
deps: — · sketch: (→) D = e·g·D with D ≥ 1 forces e·g = 1; W = μ; the tag iff
gives postRec. (←) instantiate the match; all stage laws reflexive at e = g = 1,
μ = W; coherence/budget from hc/hb. · difficulty: medium

**Sp.selfloopFull** · SP4_selfloopFull.lean
statement: `theorem selfloop_isFull {n s} (hc) (hb) (h : SuccStep n s s) :
IsFull s ∧ s.tag = .postRec`
moves_ref: "n = 3 check: the two loop classes Q2.3▸(1,2) and Q3▸(1,3) are exactly
the full POST-REC letters at stages (1,1,2) and (1,1,3), per (i)."
deps: Sp.selfloopChar · sketch: unfold IsFull; direct from the characterization.
difficulty: easy

**Sp.fullForcing** · SP4_fullForcing.lean
statement: `theorem full_forces {n} {s : Species} (hc : Coherent s)
(hb : Budget n s) (hf : IsFull s) : s.e = 1 ∧ s.ell = s.W ∧ s.a = 0 ∧ s.s0 = 0 ∧
s.lam = {(1, s.W)} ∧ s.lflank = [] ∧ s.rflank = [] ∧ s.slots = Finset.Icc 0 s.W`
moves_ref: "(i) At each fixed (tag, D, w, W) there is AT MOST ONE full letter:
μ = W with (B4)'s g·μ ≤ ℓ and (B3)'s a + ℓ ≤ W forces g = 1, ℓ = W, a = 0,
λ = {(1, W)} …; then (B3)'s s₀′ + w′ ≤ W with w′ = e·ℓ = e·W forces e = 1 and
s₀′ = 0 …, by (G1) both flanks empty, by (G3) slots {0, …, W}".
deps: — · sketch: sel = (1, W): (B4) W ≤ ℓ; (B3) a + ℓ ≤ W so ℓ ≤ W ⇒ ℓ = W,
a = 0; λ: member (1, W) with Σ = W ⇒ erase has sum 0 & positive parts ⇒ singleton
(`Multiset.cons_erase` + sum_eq_zero); (B3) s0 + e·W ≤ W, e ≥ 1, W ≥ 1 ⇒ e = 1,
s0 = 0; (G1) flanks span 0; (G3). · difficulty: medium

**Sp.fullUnique** · SP4_fullUnique.lean
statement: `theorem full_unique {n} {s s' : Species} (hcs : Coherent s)
(hbs : Budget n s) (hcs' : Coherent s') (hbs' : Budget n s') (hf : IsFull s)
(hf' : IsFull s') (htag : s.tag = s'.tag) (hD : s.D = s'.D) (hw : s.w = s'.w)
(hW : s.W = s'.W) : s = s'`
moves_ref: "(i) At each fixed (tag, D, w, W) there is AT MOST ONE full letter …
every field determined."
deps: Sp.fullForcing · sketch: Species.ext; every remaining field pinned by
full_forces + (G2)/(G3) + sel = some (1, W). · difficulty: easy

**Sp.rankRadix** · SP4_rankRadix.lean
statement: `theorem rankNat_lt {n} {s} (hc : Coherent s) (hb : Budget n s) :
rankNat n s < 6 * n^2` and `theorem rankNat_lt_of_lex {n} {s s'} (hcb…: bounds) :
(s.D, tagord s.tag, n - s.W, fullBit s) <ₗₑₓ (s'.D, …) → rankNat n s < rankNat n s'`
(lex spelled as the 4-case disjunction to avoid Prod.Lex friction)
moves_ref: "it has at most |range(ρ)| ≤ n·3·n·2 = 6n² letters".
deps: — · sketch: D − 1 < n, tagord < 3, n − W < n (W ≥ 1), bit < 2; mixed-radix
strict-mono: omega after unfolding (4 cases). · difficulty: medium

**Sp.rankStepInc** · SP4_rankStepInc.lean
statement: `theorem rank_step_inc {n} {s s'} (h : SuccStep n s s')
(hcb : Coherent s ∧ Budget n s) (hg : ∀ g μ, s.sel = some (g,μ) → 2 ≤ s.e * g) :
s.D < s'.D`
moves_ref: "· e·g ≥ 2: D′ = e·g·D > D."
deps: — · sketch: D′ = e·g·D ≥ 2·D > D (D ≥ 1). · difficulty: easy

**Sp.rankStepRec** · SP4_rankStepRec.lean
statement: `theorem rank_step_rec {n} {s s'} (h : SuccStep n s s') (hne : s ≠ s')
(hin : InCatalogue n s) (hin' : InCatalogue n s')
(he1 : ∀ g μ, s.sel = some (g,μ) → s.e * g = 1) : rankNat n s < rankNat n s'`
moves_ref: "· e = g = 1, μ < W(s): D′ = D; tagord′ = 2 ≥ tagord; if tagord < 2
done, else n − W′ = n − μ > n − W(s). · e = g = 1, μ = W(s): s is full …; if
tagord(s) = 2, then s is THE full POST-REC letter at its stage, so s′ ≠ s … is
non-full by (i)'s uniqueness: the last coordinate rises 0 → 1."
deps: Sp.fullForcing, Sp.fullUnique, Sp.rankRadix, Sp.memCoherent · sketch: the
displayed three-way split on (μ vs W, tagord); the μ = W ∧ tagord = 2 branch:
s full; if s' full too then full_unique (stages match: D′ = D, w′ = w, W′ = μ =
W, tag′ = postRec = tag) forces s' = s, contra hne; so fullBit rises.
difficulty: medium-hard (the subtle case; keep the three branches as `have`s)

**Sp.rankStrict** · SP4_rankStrict.lean
statement: `theorem rank_strict {n} {s s'} (hin : InCatalogue n s)
(hin' : InCatalogue n s') (h : SuccStep n s s') (hne : s ≠ s') :
rankNat n s < rankNat n s'`
moves_ref: "(ii) The rank ρ(s) := (D, tagord, n − W, 1 − [s is full]) … STRICTLY
increases lexicographically along every non-self-loop SUCC edge s → s′".
deps: Sp.rankStepInc, Sp.rankStepRec, Sp.rankRadix · sketch: e·g = 1 ∨ e·g ≥ 2
(WellTyped positivity); dispatch. · difficulty: easy

**Sp.dagWalk** · SP4_dagWalk.lean
statement: `theorem SP_DAG_walk {n} (hn : 1 ≤ n) {l : List Species}
(h : CollapsedWalk n l) : l.length ≤ 6 * n^2`
moves_ref: "(iii) Hence the menu graph with self-loops collapsed is a DAG; every
collapsed walk visits pairwise-distinct ranks, so it has at most … 6n² letters".
deps: Sp.rankStrict, Sp.rankRadix · sketch: map rankNat: Chain' (· < ·) list of
ℕ < 6n²; strictly-increasing-below-B has length ≤ B (small induction or
`List.Sorted` + Nodup ⊆ range). · difficulty: medium

**Sp.dagWords** · SP4_dagWords.lean
statement: `theorem SP_DAG_words (n : ℕ) (hn : 1 ≤ n) : {l | CollapsedWalk n l}.Finite
∧ Nat.card {l | CollapsedWalk n l} ≤ (Nat.card (SnRaw n) + 1)^(6 * n^2)`
moves_ref: "with SP-FIN, the set of collapsed words over 𝒮_n^raw is FINITE, of
size ≤ (|𝒮_n^raw| + 1)^{6n²}."
deps: Sp.dagWalk, Sp.finThm · sketch: inject length-≤L lists into
`Fin L → Option (SnRaw-subtype)` (pad with none); card arithmetic. · difficulty: medium

### F. SP-COMP (conditional — the interface layer), words, entrances, (m,c)

**Sp.compMember** · SP3_compMember.lean
statement: `theorem SP_COMP {n : ℕ} (ch : EngineChain n) : ∀ s ∈ ch.word,
InCatalogue n s`
moves_ref: "every read r of η's CATALOGUE WORD …: the read's retained datum is a
member of 𝒮_n^raw, and each consecutive read pair is linked by an edge of the
syntactic menu Out (SP.4)."
deps: — · sketch: induction along word: head via `InCatalogue.root` (hRoot);
each next via `.step` (hStep Chain'). ≤ 20 lines.
difficulty: easy-medium
hypothesis_fields: `EngineChain.hRoot` (SP-COMP steps (1)/(3)/(3′) at r = 0 —
"the r = 0 read is at the root stage (key x: D = 1; pool F_p: w = 1; window
[0, n]: W = n)" + coherence, derived in the note from §B2-DEF/§C DOM/§D4-R,
OPEN here, owner HC-1/MovesD); `EngineChain.hStep` (steps (2)/(3)/(3′)/(5) —
"the stage fields of read r+1 are the D.7/D.8/D.10 outputs", same owner);
D4R.0-K(c)/VP residual rides by omission (no verdict semantics consumed) —
matching the note's ledger: "SP-COMP's remaining conditionality is exactly the
D4R.0-K(c) residual". NEVER strengthen: do not add fields claiming the engine
laws, and do not weaken: do not drop coherence from hStep.

**Sp.compEdges** · SP3_compEdges.lean
statement: `theorem SP_COMP_edges {n} (ch : EngineChain n) :
ch.word.Chain' (fun s s' => Sum.inl s' ∈ Out n s)`
moves_ref: "each consecutive read pair is linked by an edge of the syntactic menu
Out (SP.4)" (+ step (5): "which is precisely SP.4's edge relation").
deps: Sp.compMember · sketch: Chain' map: SuccStep + membership ⇒ Succ ⇒ inl ∈ Out.
difficulty: easy · hypothesis_fields: as Sp.compMember (inherited via EngineChain).

**Sp.tauWord** · SP3_tauWord.lean
statement: `theorem tauWord_spec {n} (cw : CatalogueWord n) :
cw.tauWord = cw.word.dropLast ∧ (∀ s ∈ cw.tauWord, s.sel ≠ none) ∧
∀ s, cw.word.getLast? = some s → s.W = 1 → cw.tauWord.length + 1 = cw.word.length`
moves_ref: "the CATALOGUE WORD (SP-COMP's quantifier, the census's object) closes
at the confirming read; the τ-WORD (every density consumer's object) is the
catalogue word with that final confirming letter removed".
deps: — · sketch: definitional unwinds + `List.length_dropLast`. · difficulty: easy
hypothesis_fields: verdict pinning (WHERE the halt verdict sits — parent read /
level-0 track) is VP's, NOT stated; only the word arithmetic is.

**Sp.n1Clause** · SP3_n1Clause.lean
statement: `theorem n1_root_confirming {s : Species} (h : RootAdmissible 1 s) :
s.W = 1 ∧ s.sel = none` and `theorem n1_word {cw : CatalogueWord 1} :
cw.word.length = 1 ∧ cw.tauWord = []`
moves_ref: "At n = 1 the catalogue word is the single ROOT letter (W = n = 1,
selection ⊥ — (G6)'s degenerate degree) … the τ-WORD is EMPTY".
deps: Sp.succTerminal, Sp.compMember · sketch: RootStage gives W = 1; (G6) gives
sel = none; Chain' + succTerminal kills any second letter; length-1 dropLast.
difficulty: easy-medium · hypothesis_fields: (τ-hen) SEMANTICS (the level-0 track
leaf, v = {(1,1)}) is VP's — only the word/letter arithmetic is stated.

**Sp.entranceDef** · SP3_entrance.lean
statement: `structure EntranceShape (n : ℕ) extends EngineChain n where
hLast : ∃ s g μ, word.getLast? = some s ∧ s.sel = some (g, μ)` (the designated
continuing branch) + `theorem entrance_collapsed_finite (n) (hn : 1 ≤ n) :
{l | CollapsedWalk n l ∧ (last-letter-continuing)}.Finite`
moves_ref: "a loop-collapsed entrance word is a collapsed walk in the menu graph,
so it has ≤ 6n² letters (SP-DAG(iii)); with SP-FIN the family of such words is
finite and p-independent — {ε} is finite up to its (height pair, depth)
parameters".
deps: Sp.dagWords · sketch: subset of collapsed walks; Set.Finite.subset. HEIGHT
PAIRS/DEPTH PARAMETERS: deliberately absent from the type (they are [2b]/[1]
parameter slots — the note: "its height pairs (h_r, u*_r) retained as
ℕ-parameter slots"); record in docstring that the Lean {ε} is the LETTER-WORD
part only. · difficulty: medium
hypothesis_fields: block-entry SEMANTICS ("enters the size-e block") is [1v]
CTS-M(iii)'s; here only "last letter continuing" is typed — flagged, not
strengthened.

**Sp.mcRoster** · SP4_mcRoster.lean
statement: `theorem outcomeClass_total (s : Species) : (outcomeClass s =
.terminalFin ↔ cOf s = 0) ∧ (outcomeClass s = .continuing ↔ (cOf s ≥ 1 ∧
mOf s = 1)) ∧ (outcomeClass s = .branching ↔ (cOf s ≥ 1 ∧ 2 ≤ mOf s)) ∧
cOf s ≤ mOf s ∧ (outcomeClass s = .continuing → cOf s = 1)`
moves_ref: §S-RESUM (K-SUB): "(o continuing = the (c = 1, m = 1) row of (K-SUB)'s
(m, c) CLASSIFICATION" / "(o terminal fin := the (c = 0, any m) row" / "[o
branching := the (c ≥ 1, m ≥ 2) row"; fields from SP.1's "(residual shape) …
multiset {(g⁽¹⁾, μ⁽¹⁾), …}".
deps: — · sketch: unfold the if-chain; cOf ≤ mOf by `Multiset.card_filter_le`;
c ≥ 1 ∧ m = 1 ⇒ c = 1 by omega. · difficulty: easy
hypothesis_fields: "continuing ⟺ μ ≥ 2" is DEFINITIONAL bookkeeping keyed to
(G6)'s W = 1 rule; that halting semantics matches VP is [3t]'s, cited as owner
in the docstring — no unit asserts it.

### G. The generated enumeration (feeds every n = 3 `decide`)

**Sp.compEnumComplete** · SP2_compEnum.lean
statement: `theorem compEnum_complete {span : ℕ} {c : List ℕ} :
IsComposition c span ↔ c ∈ compEnum span` (+ `compEnum_nodup`)
moves_ref: "each flank is a composition of its span" (G1).
deps: — · sketch: strong induction on span; compEnum span = [[]] at 0, else
first-part split. · difficulty: medium

**Sp.lamEnumComplete** · SP2_lamEnum.lean
statement: `theorem lamEnum_complete {bound weight : ℕ} {lam : Multiset (ℕ × ℕ)}
(hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2) (hbd : ∀ gm ∈ lam, gm.1 ≤ bound ∧
gm.2 ≤ bound) : ((lam.map fun gm => gm.1 * gm.2).sum = weight ↔ lam ∈ lamEnum
bound weight)`
moves_ref: "(residual shape) the degree–multiplicity partition λ … with
Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ" + (B5)'s part caps.
deps: — · sketch: enumeration by strong recursion on weight over a canonical
(sorted) representative; completeness by induction on the multiset. THE fiddly
enum unit — recommend List-of-sorted-lists internally, Multiset at the boundary.
difficulty: medium-hard

**Sp.speciesEnumComplete** · SP2_speciesEnum.lean
statement: `theorem speciesEnum_complete {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) : s ∈ speciesEnum n`
moves_ref: "𝒮_n^raw injects into the encoded set ((G1)–(G6) only shrink it)"
[here: the generated candidate list].
deps: Sp.compEnumComplete, Sp.lamEnumComplete · sketch: coherence pins a/d/slots
from (s0, e, ℓ) ((G2)/(G3)); budget pins every generator range ((B1)–(B5));
membership by product-list mem lemmas. · difficulty: medium-hard

### H. The n = 3 instance (SP.6) — the `decide` layer

All statements phrased over `List`/`Bool` (`List.all … = true`) for kernel
`decide`; perf fence §1.6 applies (split per stage group on overrun).

**Sp.n3card53** · SP6_card53.lean
statement: `theorem catalogue3_card : catalogue3.length = 53 ∧ catalogue3.Nodup`
(Nodup by `decide`; length by `rfl`) + `theorem groups_card : groupR.length = 21
∧ groupQ3.length = 21 ∧ groupQ2.length = 6 ∧ groupQ1.length = 1 ∧ groupI.length = 4`
moves_ref: "|𝒮₃^raw| = 21 + 21 + 6 + 1 + 4 = 53."
deps: DefsN3 · sketch: rfl/decide. · difficulty: easy

**Sp.n3rootLetters** · SP6_rootLetters.lean
statement: `theorem root3_exact : (speciesEnum 3).filter (rootAdmissibleB 3) ~
groupR` (permutation, or filter-membership iff: `∀ s, s ∈ speciesEnum 3 →
(rootAdmissibleB 3 s = true ↔ s ∈ groupR)` as `List.all … = true` by decide)
moves_ref: "GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters." + the
re-verification bracket "per stage, the (G1)–(G6)+(B1)–(B5corrected) letters are
exactly the displayed rows".
deps: Sp.speciesEnumComplete (for the ⊆ reading), DefsN3 · sketch: decide.
difficulty: medium (perf)

**Sp.n3closureStep** · SP6_closureStep.lean
statement: `theorem closure_step3 : (catalogue3.all fun s => (speciesEnum
3).all fun s' => !(succStepB 3 s s') || (s' ∈ catalogue3 : Bool)) = true`
moves_ref: "the (G5) closure from the root stage (1,1,3) generates exactly the
five displayed stage groups … nothing further from Q2/Q3; W = 1 terminal by (G6)".
deps: DefsN3, DefsEnum · sketch: decide (≈53 × |enum3| succStepB evals — THE perf
hotspot; pre-split into 5 per-group units if needed). · difficulty: medium (perf)

**Sp.n3reachable** · SP6_reachable.lean
statement: `theorem reachable3 : (catalogue3.all fun s' => rootAdmissibleB 3 s' ||
groupR.any fun s => succStepB 3 s s') = true`
moves_ref: "root selections (1,1)/(1,2)/(1,3) → stages (1,1,1)/(1,1,2)/(1,1,3);
▸(2,1), ▸(3,1), e=2, e=3 → the four POST-INC W = 1 stages".
deps: DefsN3 · sketch: decide (53 × 21). Every non-root letter is one SuccStep
from a ROOT letter at n = 3. · difficulty: easy

**Sp.n3catalogueEq** · SP6_catalogueEq.lean
statement: `theorem SnRaw3_eq : ∀ s, InCatalogue 3 s ↔ s ∈ catalogue3`
moves_ref: "**Definition (the raw catalogue; rev 3 …)** 𝒮_n^raw := the least set
…" + "[RE-VERIFIED against the rev-3 definition: …]".
deps: Sp.memCoherent, Sp.speciesEnumComplete, Sp.reflSucc, Sp.n3rootLetters,
Sp.n3closureStep, Sp.n3reachable · sketch: (→) induction on InCatalogue: root
case via n3rootLetters (s ∈ enum by speciesEnumComplete); step via n3closureStep.
(←) each letter: root case by rootAdmissibleB + refl lemmas; non-root via
n3reachable + `.step`. · difficulty: medium

**Sp.n3menuMap** · SP6_menuMap.lean
statement: `theorem menu3_exact : (catalogue3.all fun s => (catalogue3.all fun
s' => (succStepB 3 s s' == (s' ∈ menuMap3 s : Bool)))) = true`
moves_ref: "The n = 3 menu map (Out, sealed; stage laws of SP.4). ▸(1,1) → Q1;
▸(1,2) → Q2 letters; ▸(1,3) → Q3 letters; ▸(2,1) → I(2,2); ▸(3,1) → I(3,3); e=2
letters → I(2,1); e=3 letters → I(3,1)."
deps: DefsN3 · sketch: decide (53 × 53). With Sp.n3catalogueEq this IS the sealed
menu map on 𝒮₃^raw. · difficulty: medium (perf, moderate)

**Sp.n3selfloops** · SP6_selfloops.lean
statement: `theorem loops3 : catalogue3.filter (fun s => succStepB 3 s s) =
[loopQ23, loopQ3]`
moves_ref: "SELF-LOOPS: Q2.3▸(1,2) → Q2 (the μ = 2 loop) and Q3's ▸(1,3) rows →
Q3 (the μ = 3 loop) — exactly two loop classes at n = 3, both POST-REC".
deps: DefsN3 · sketch: decide. Cross-check `Sp.selfloopFull`: both are the full
POST-REC letters. · difficulty: easy

**Sp.n3postincW1** · SP6_postincW1.lean
statement: `theorem postInc3_W1 : (catalogue3.all fun s => !(s.tag == .postInc)
|| (s.W == 1)) = true`
moves_ref: "POST-INC W = 1 always at n = 3 (every genuine increment here has
μ = 1: g·μ ≤ ℓ and e·ℓ ≤ 3 force μ ≥ 2 into e = g = 1, the recentering class)."
deps: DefsN3 · sketch: decide. · difficulty: easy

**Sp.n3terminal5** · SP6_terminal5.lean
statement: `theorem terminal3 : catalogue3.filter (fun s => s.W == 1) =
groupQ1 ++ groupI ∧ (catalogue3.all fun s => (s.W == 1) == (s.sel == none)) =
true ∧ ((groupQ1 ++ groupI).all fun s => catalogue3.all fun s' =>
!(succStepB 3 s s')) = true`
moves_ref: "The five W = 1 letters of SP.6 have Out(s) = V_term exactly." + "W = 1
letters read the confirming side … and are TERMINAL: selection ⊥".
deps: DefsN3 · sketch: decide ×3 (5 letters + the (G6) instance + empty menus =
the closure-marker face; V_term itself is unconditional in Out's definition).
difficulty: easy

**Sp.n3R3check** · SP6_R3check.lean
statement: `theorem R3_member : coherentB R3letter = true ∧ budgetB 3 R3letter =
true ∧ R3letter ∈ groupR ∧ R3letter.a = 2` (both flank variants)
moves_ref: "R3's membership check under the rev-3 definition (spot-display …).
R3 = (ROOT, (D,w,W) = (1,1,3), e = 1, ℓ = 1, a = 2, s₀′ = 2, slots {2,3},
λ = {(1,1)} ▸ (1,1), …): … (B5, corrected anchor bound) a = 2 ≤ ⌊(W − w′)/e⌋ = 2 ✓".
deps: DefsN3 · sketch: decide — the note's own saturating witness for the
corrected (B5). · difficulty: easy

**Sp.n3thresholdData** · SP6_thresholdData.lean
statement: `theorem threshold_data_sane : fieldSizeExcluded2.length = 11 ∧
fieldSizeExcluded3.length = 2 ∧ multiSide6.length = 6 ∧ (multiSide6.all (· ∈
catalogue3)) = true ∧ (fieldSizeExcluded2.all (· ∈ catalogue3)) = true ∧
(fieldSizeExcluded3.all (· ∈ fieldSizeExcluded2)) = true ∧
multiSide6.map Nstar3six = [some 6, some 6, some 6, some 6, some 6, some 7]`
moves_ref: "p = 2 …: the 11 letters with λ ⊇ two distinct linears …; p = 3 (two
nonzero roots): exactly the 2 letters with λ = {(1,1)³}" + "THE SIX COMPUTATIONS
(all at p = 3 …): … N*_3 = 6; … N*_3 = 6; … N*_3 = 7."
deps: DefsN3 · sketch: decide. DEFINITIONS + internal sanity only — realizability
semantics (census/prediction) is NOT formalized (§0; the note: "this is the
queued re-seal gate's SEALED PREDICTION, not a theorem of this note").
difficulty: easy
hypothesis_fields: none stated — but the docstrings MUST carry the note's typing:
field-size pass is "NECESSARY for realization, NOT sufficient"; N*₃ values are
gate-censused data (M-n3-V2), not theorems.

**Sp.n3entrancePatterns** · SP6_entrance.lean
statement: `theorem entrance3_edges : succStepB 3 rootSel13 loopQ3 = true ∧
succStepB 3 loopQ3 loopQ3 = true ∧ (∃ q3 ∈ groupQ3, q3.sel = some (1,2) ∧
succStepB 3 loopQ3 q3 = true) ∧ …` (the displayed block-entry patterns'
edges, each a Bool check)
moves_ref: "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as depth slots): into the
μ=2 block: root▸(1,2) [R4/R5 rows], or root▸(1,3)·(Q3-loop)^d·▸(1,2); into the
μ=3 block: root▸(1,3); into each increment landing (D ≥ 2): …".
deps: DefsN3 · sketch: decide per edge; the loop-power is one loop edge + the
exit edge (depth is a parameter, not a letter — SP-DAG scope). · difficulty: easy

**Sp.n1singleton** · SP6_n1singleton.lean
statement: `theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1`
(confirmingRoot1 := the W = 1 root letter at stage (1,1,1))
moves_ref: "(G6) … (or W = n = 1 at the root — the degenerate degree)" + the n = 1
clause: "At n = 1 the catalogue word is the single ROOT letter".
deps: Sp.speciesEnumComplete, Sp.n1Clause, Sp.succTerminal · sketch: root-admissible
at n = 1 pins every field (g6Forcing at W = 1); terminal ⇒ no step case.
difficulty: easy-medium

## 6. Risks, fallbacks, and what deliberately is NOT here

1. **decide perf** (Sp.n3closureStep, Sp.n3rootLetters, Sp.n3menuMap): see §1.6.
   Estimated enum3 ≤ ~3k candidates; worst check ~160k cheap Bool evals. If kernel
   time explodes: split per stage group; then shrink enum3 by strengthening the
   generator bounds (additive change, no statement touched). native_decide BANNED.
2. **Multiset-in-kernel**: Multiset = Quotient List — `decide` reduces through
   `Quot.lift`; if it sticks, switch `lam` to a SORTED `List (ℕ × ℕ)` canonical
   representative (DESIGNER ROUND — statement fence: Species field type change
   needs sign-off; flag, do not improvise).
3. **The λ-multiset forcing steps** (Sp.g6Forcing, Sp.fullForcing) are the only
   hand-combinatorics; both ≤ ~40 lines with `Multiset.cons_erase`.
4. NOT HERE (per §0): realizability/census theorems; VP/verdict semantics; height
   parameters and depths (the P̂ enrichment — §D4-R L3 rev 9's (h_r, u*_r) pair);
   [2b] state types; any count or mass. Consumers: MovesV reads cells/menus from
   this corpus; MovesX reads SP.4/SP-DAG; MovesS reads the (m,c) roster fields.

## 7. Roster summary

56 units + 3 def-only files (Defs, DefsEnum, DefsN3). By group: A reflection/
closure 5 · B shift block 8 · C coherence/budget 4 · D SP-FIN 6 · E SP-OUT/SP-DAG
11 · F SP-COMP/words/entrance/(m,c) 6 · G enumeration 3 · H n = 3 decide layer 13.

easy: 30 — all of A; shCongr/shDvd/shE1/shEquiv/shStage/shExample;
  anchorBoundGeo/b4Derived; encodeCard; outFinite/selfloopFull/fullUnique/
  rankStepInc/rankStrict; compEdges/tauWord/mcRoster; n3card53/n3reachable/
  n3selfloops/n3postincW1/n3terminal5/n3R3check/n3thresholdData/n3entrancePatterns.
medium: 22 (incl. 3 easy-medium: compMember, n1Clause, n1singleton) — shSlots/
  shAnchorInv; anchorBoundCensus/g6Forcing; compEncode/lamEncode/finThm/finWords;
  selfloopChar/fullForcing/rankRadix/dagWalk/dagWords; entranceDef;
  compEnumComplete; n3rootLetters/n3closureStep/n3catalogueEq/n3menuMap.
medium-hard: 4 — encodeInj, rankStepRec, lamEnumComplete, speciesEnumComplete.
hard: 0 — nothing in this corpus needs one (the note's only real proofs are
  SP-FIN's encoding count and SP-DAG, both split above).

No unit expects > ~40 proof lines; the four medium-hard units carry pre-approved
split points (encodeInj: scalar vs flank/λ blocks; rankStepRec: the three
branches; lamEnumComplete: sorted-list core vs Multiset boundary;
speciesEnumComplete: per-field range lemmas).
