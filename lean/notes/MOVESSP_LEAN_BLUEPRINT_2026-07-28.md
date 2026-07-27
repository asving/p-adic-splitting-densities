# MOVESSP LEAN BLUEPRINT (2026-07-28) — the §M-SPECIES corpus, unit specs
# REV 3 (post-Fable-audit on rev 2: 2 crit / 4 gap repaired; NOTE ERRATUM
# CANDIDATE recorded at §9 — the entrance display's "[R4/R5 rows]" bracket)

REV 3 (Fable audit `lean/notes/MOVESSP_AUDIT_FABLE_2026-07-28.md`): C1 loops3
order corrected + an ORDER DISCIPLINE rule for every pinned-list decide target
(§4); C2 the ▸(1,2) entrance roster corrected to its TRUE three members per
group — the note-side bracket flagged as an erratum candidate (§9), verified,
never silently baked in; G1 collapseRuns pinned by its defining equations; G2
the n1 dependency cycle split; G3 the group-F fence retargeted to closure-side
objects only; G4 the non-detachability overclaim weakened to what the encoding
enforces. Table extended at §8.

# REV 2 (post-Codex-audit, 17 findings repaired)

REV 2 repairs ALL findings of `lean/notes/MOVESSP_AUDIT_CODEX_2026-07-28.md`
(6 crit / 11 gap): SP-COMP de-circularized over the `CanTreeModel` engine
interface with the note's full (n, p, f, η, r) quantifier prefix and D4R.0-K(c)
as the EXPLICIT field `hVerdictPin` (F1/F2/F7); `CatalogueWord` forces the halt
endpoint (F3); `EntranceShape` carries the block-entry datum + parameter slots
and feeds the finiteness theorem (F4); n = 3 data content-pinned (F5/F16/F17);
both R3 flank variants (F6); every binder/hypothesis spelled (F8–F14); the
(m, c) roster DEFERRED to MovesS (F15). Findings→repairs table at the end.

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
  §D4-R L11, §D4-R L2/L3/L5). Those live in Moves/MovesD/HC-1, not here. Lean form
  [REV 2, F1/F2]: the engine interface `CanTreeModel` (§2), whose FIELDS are the
  RAW per-read laws (root stage, StageLaws, coherence/budgets, halt, verdict pin)
  that SP-COMP's proof steps (1)–(3′)/(5) derive from the engine — the catalogue
  conclusions (InCatalogue/SuccStep/Out) occur in NO field; the corpus proves the
  closure absorbs any such tree, under the note's full (n, p, f, η, r) quantifier
  prefix. Discharging the fields = HC-1/MovesD territory.
- The D4R.0-K(c) residual (verdict pin: alphabet V + halting rule τ + detection cap,
  owner [3t] via VP) is an EXPLICIT hypothesis field [REV 2, F7]: `CanTreeModel.
  hVerdictPin` (§2) — the ⊥-read leaf-verdict law SP-COMP's step (4) consumes.
  `Verdict` stays three bare labels (no semantics: WHICH verdict, WHEN τ fires =
  VP's); the FIELD carries the residual, named, in every SP-COMP unit's
  hypothesis_fields. moves_ref: "SP-COMP's remaining conditionality is exactly the
  D4R.0-K(c) residual — the verdict pin …, owned by [3t] via VP — entering at step
  (4)'s leaf verdicts."
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

/-- The RAW per-read stage laws (SP-COMP steps (2)/(5): the D.5/D.6/D.7/D.8/D.10
outputs — D′ = e·g·D, w′ = g·w, W′ = μ, tag′ = POST-INC iff e·g ≥ 2, POST-REC iff
e = g = 1). NO coherence/budget clause: the ENGINE-facing half, so the catalogue's
SuccStep is never assumed where it must be concluded [REV 2, F1]. `match` (not ∃)
keeps it decidable. -/
def StageLaws (s s' : Species) : Prop :=
  match s.sel with
  | none => False
  | some (g, μ) =>
      s'.D = s.e * g * s.D ∧ s'.w = g * s.w ∧ s'.W = μ ∧
      (s'.tag = .postInc ↔ 2 ≤ s.e * g) ∧
      (s'.tag = .postRec ↔ (s.e = 1 ∧ g = 1))

/-- SP.4's SUCC clause = (G5)'s generation rule: the stage laws AND the target
coherent and budget-admissible. -/
def SuccStep (n : ℕ) (s s' : Species) : Prop :=
  StageLaws s s' ∧ Coherent s' ∧ Budget n s'

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

/-- The rank's last coordinate "1 − [s is full]", as a ℕ [REV 2, F14]. -/
def fullBit (s : Species) : ℕ := if s.sel = some (1, s.W) then 0 else 1

/-- ρ(s) = (D, tagord, n − W, 1 − [full]) as a mixed-radix ℕ, order-isomorphic to
the note's lex tuple on catalogue ranges (D ∈ [1,n], tagord < 3, n − W < n,
bit < 2); rankNat < 6n² on catalogue members. -/
def rankNat (n : ℕ) (s : Species) : ℕ :=
  (((s.D - 1) * 3 + tagord s.tag) * n + (n - s.W)) * 2 + fullBit s

/-- A collapsed walk: consecutive SuccStep edges with self-loops struck (rev 3:
"the collapsed LETTER length of a walk"). -/
def CollapsedWalk (n : ℕ) (l : List Species) : Prop :=
  (∀ s ∈ l, InCatalogue n s) ∧ l.Chain' (fun s s' => SuccStep n s s' ∧ s ≠ s')

/-! ### SP-COMP interface [REV 2, F1/F2/F3/F4/F7 — de-circularized] -/

/-- THE ENGINE INTERFACE: an abstract canonical tree over a fixed (p, f) with
per-read retained data. EVERY field is an OPEN engine law, cited to the note's
SP-COMP proof step that derives it from §B2-DEF/§C DOM/§D4-R (owner HC-1/MovesD);
NONE is proved in this corpus, and the catalogue conclusions (`InCatalogue`,
`SuccStep`, `Out`-membership) appear in NO field — they are what the SP-COMP
units derive by closure induction. -/
structure CanTreeModel (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p]) where
  /-- η ∈ T_can(f): the chains (§D4-R L2 — "terminal-verdict branches and
  infinite branches alike, prefixwise"); abstract here. -/
  Branch : Type
  /-- length of η's CATALOGUE WORD (through its first W = 1 read, if any;
  0 allowed for the prefixwise/no-read reading). -/
  len : Branch → ℕ
  /-- the retained datum of read r of η (junk above `len η`). -/
  datum : Branch → ℕ → Species
  /-- step (1)+(3)+(3′) at r = 0: root stage (D, w, W) = (1, 1, n), datum
  coherent and budget-admissible [§B2-DEF D.0 key x; §D4-R L3/L5; §C DOM]. -/
  hRoot : ∀ η, 0 < len η →
    RootStage n (datum η 0) ∧ Coherent (datum η 0) ∧ Budget n (datum η 0)
  /-- steps (2)/(5): the raw stage laws per consecutive read pair ["the stage
  fields of read r+1 are the D.7/D.8/D.10 outputs"]. -/
  hStage : ∀ η r, r + 1 < len η → StageLaws (datum η r) (datum η (r + 1))
  /-- steps (3)+(3′) at every read: budgets and coherence ["Budgets hold at
  every read" / "Geometric coherence holds at every read"]. -/
  hCoh : ∀ η r, r < len η → Coherent (datum η r) ∧ Budget n (datum η r)
  /-- the catalogue-word endpoint: the word closes AT its first confirming
  W = 1 read [SP-COMP: "up to and including its first W = 1 read"]. -/
  hHalt : ∀ η r, r < len η → (datum η r).W = 1 → r + 1 = len η
  /-- step (4): the leaf verdict of a ⊥-ended chain, from V_term. -/
  verdict : Branch → Option Verdict
  /-- step (4)'s law — THE D4R.0-K(c) RESIDUAL AS AN EXPLICIT FIELD [REV 2,
  F7]: a chain whose last read is terminal carries SOME V_term verdict at its
  τ-leaf ["its chain's τ-leaf carries a verdict from V_term"]. WHICH verdict,
  WHERE pinned (parent/track), WHEN τ fires: VP's, NOT modeled — this field is
  the note's sole remaining open kernel for SP-COMP, riding as a hypothesis. -/
  hVerdictPin : ∀ η, 0 < len η →
    (datum η (len η - 1)).sel = none → (verdict η).isSome

/-- A CATALOGUE WORD (SP-COMP's quantifier + SP.4's HALT CONVENTION) [REV 2,
F3]: letters in 𝒮ₙ^raw, Out-linked, and FORCED to close at the FIRST confirming
W = 1 read — the endpoint is a structure law, not an antecedent. (Words ended by
a V_term edge from a CONTINUING letter, and infinite branches, are catalogued
prefixwise via `CanTreeModel`, not by this structure.) -/
structure CatalogueWord (n : ℕ) where
  word : List Species
  hne : word ≠ []
  hMem : ∀ s ∈ word, InCatalogue n s
  hChain : word.Chain' (SuccStep n)
  /-- the last letter IS confirming: W = 1 (hence sel = ⊥ by (G6)). -/
  hLast : ∀ s, word.getLast? = some s → s.W = 1
  /-- …and it is the FIRST confirming read: no earlier letter has W = 1. -/
  hFirstW1 : ∀ s ∈ word.dropLast, s.W ≠ 1

/-- The τ-WORD: the catalogue word minus its final confirming letter (SP.4; at
n = 1 the empty word). -/
def CatalogueWord.tauWord {n : ℕ} (cw : CatalogueWord n) : List Species :=
  cw.word.dropLast

/-- Collapse self-loop runs: keep one letter per maximal run of equal
consecutive letters (the depth direction struck). PINNED by its defining
equations [REV 3, G1 — the const-[] degenerate satisfier is excluded: it
violates the singleton equation]. Equals `List.destutter (· ≠ ·)`. -/
def collapseRuns : List Species → List Species
  | [] => []
  | [s] => [s]
  | s :: s' :: rest =>
      if s = s' then collapseRuns (s' :: rest)
      else s :: collapseRuns (s' :: rest)

/-- An ENTRANCE SHAPE into a block entry [REV 2, F4]: an Out-linked word in
𝒮ₙ^raw whose LAST letter is the block-entry read with DESIGNATED continuing
selection (g, μ) — the size-e block/landing-cell β₀ identification of that
datum is [1v] CTS-M(iii)'s, cited as owner — carrying its height-pair
ℕ-parameter SLOTS (§D4-R L3 rev 9's (h_r, u*_r); bare data, no [2a] law) and
one depth slot per maximal self-loop run. -/
structure EntranceShape (n gsel μsel : ℕ) where
  word : List Species
  hne : word ≠ []
  hMem : ∀ s ∈ word, InCatalogue n s
  hChain : word.Chain' (SuccStep n)
  /-- the last letter's designated continuing branch: selection (gsel, μsel). -/
  hEntry : ∀ s, word.getLast? = some s → s.sel = some (gsel, μsel)
  /-- height-pair parameter slots (h_r, u*_r), one per read — data only. -/
  heights : Fin word.length → ℕ × ℕ
  /-- depth parameter slots, one per maximal self-loop run — data only. -/
  depths : Fin (collapseRuns word).length → ℕ

/-! ### CTS bridge (typing only) -/

/-- The plan's bounded current-state skeleton (SP.4's bridge display, typing
only): "stage (D, w, W) + tag (the tower phase) + anchor a + the residual
partition λ" — values forgotten. -/
def stateSkeleton (s : Species) : Tag × (ℕ × ℕ × ℕ) × ℕ × Multiset (ℕ × ℕ) :=
  (s.tag, (s.D, s.w, s.W), s.a, s.lam)

/- [REV 2, F15 — DEFERRAL RECORD] The rev-1 (m, c)-roster defs (mOf, cOf,
OutcomeClass, outcomeClass) and unit Sp.mcRoster are STRUCK from this corpus:
their sole anchor, the (m, c) CLASSIFICATION rows, is a display of §S-RESUM's
(K-SUB), NOT of the frozen §M-SPECIES text — no in-scope moves_ref exists.
They move to the MovesS blueprint (wave 4), where (K-SUB) is ground truth;
MovesS may define them on this corpus's `Species.lam` field (the import is
additive). Recorded also at §6/§7. -/

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
/-- NAMED LETTERS consumed by unit statements [REV 2, F5/F6/F17 — no positional
or cardinality-only references]. Each is an explicit `Species` literal. -/
def loopQ23 : Species   -- Q2.3's {(1,2)}▸(1,2) row (the μ = 2 loop)
def loopQ3  : Species   -- Q3(R6)'s {(1,3)}▸(1,3) row (the μ = 3 loop)
def R3letterA : Species -- R3, left flank [2]      [F6: BOTH variants]
def R3letterB : Species -- R3, left flank [1, 1]   [F6]
def rootR4sel12 : Species -- R4's {(1,2)}▸(1,2) row
def rootR5sel12 : Species -- R5's {(1,2)}▸(1,2) row
def rootR6sel12 : Species -- R6's {(1,2),(1,1)}▸(1,2) row [REV 3, C2/§9]
def rootR6sel13 : Species -- R6's {(1,3)}▸(1,3) row
def letterI21 : Species -- I, stage (D,w) = (2,1)  (via e = 2 sides)
def letterI22 : Species -- I, stage (2,2)          (via ▸(2,1))
def letterI31 : Species -- I, stage (3,1)          (via e = 3)
def letterI33 : Species -- I, stage (3,3)          (via ▸(3,1))
/-- The six multi-side μ = 3 letters (SP.6's SIX COMPUTATIONS), BY NAME:
"Q3(R1, right flank (1,1)), Q3(R2), Q3(R3, left flank (1,1)), and the three
Q3(R4) λ-rows". -/
def msQ3R1 : Species  -- Q3(R1)-copy, right flank [1, 1];  N*₃ = 7
def msQ3R2 : Species  -- Q3(R2)-copy;                       N*₃ = 6
def msQ3R3 : Species  -- Q3(R3)-copy, left flank [1, 1];    N*₃ = 6
def msQ3R4a : Species -- Q3(R4), λ = {(2,1)} ▸ (2,1);       N*₃ = 6
def msQ3R4b : Species -- Q3(R4), λ = {(1,2)} ▸ (1,2);       N*₃ = 6
def msQ3R4c : Species -- Q3(R4), λ = {(1,1)²} ▸ (1,1);      N*₃ = 6
def multiSide6 : List Species := [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c]
/-- λ's demand for distinct nonzero roots (the field-size criterion): the number
of monic-linear factors, WITH multiset multiplicity ("nonzero by the endpoint
convention: a is split off, so z ∤ R_anch"). -/
def linCount (s : Species) : ℕ := Multiset.card (s.lam.filter fun gm => gm.1 = 1)
/-- Field-size exclusion lists as LITERAL lists of named letters [F5]; their
λ-content is PINNED by Sp.n3thresholdData's filter identities (q = 2: ≥ 2
distinct linears, q = 3: ≥ 3), not by cardinality. -/
def fieldSizeExcluded2 : List Species  -- the 11 displayed letters, named
def fieldSizeExcluded3 : List Species  -- the 2 {(1,1)³} rows, named
/- ORDER DISCIPLINE [REV 3, C1 — this bug class repeats]: every literal list
that a unit equates with a `catalogue3.filter …` (or `groupX.filter …`) MUST
list its members in catalogue3 order — groups R → Q3 → Q2 → Q1 → I, and within
a group in the displayed row order — because `List.filter` preserves order and
Nodup pins one occurrence each. Audit of all pinned-list targets under this
rule: fieldSizeExcluded2/3 (declared here in catalogue3 order), loops3
([loopQ3, loopQ23] — Q3 before Q2), terminal3 (groupQ1 ++ groupI ✓),
entrance3_patterns' groupR filter ([rootR4sel12, rootR5sel12, rootR6sel12] —
R4 < R5 < R6 ✓); all other n = 3 targets are membership/`all` forms,
order-free. -/
/-- N*₃ on the six (SP.6): per-NAME table, `none` off multiSide6. -/
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
[REV 2, F8 — both statements in full]
statement: `theorem succStepB_iff (n : ℕ) (s s' : Species) :
succStepB n s s' = true ↔ SuccStep n s s'` AND
`theorem rootAdmissibleB_iff (n : ℕ) (s : Species) :
rootAdmissibleB n s = true ↔ RootAdmissible n s`
moves_ref: "SUCC(s) := { s′ ∈ 𝒮_n^raw : D(s′) = e·g·D, w(s′) = g·w, W(s′) = μ, …}"
and "(G5) STAGE REACHABILITY: tag = ROOT forces (D, w, W) = (1, 1, n)" (the
root-admissibility face).
deps: Sp.reflCoherent, Sp.reflBudget · sketch: match on sel (the StageLaws half);
And-transport with the two reflection iffs; rootAdmissibleB_iff = the RootStage
equality checks + the same transport. · difficulty: easy

**Sp.succTerminal** · SP0_succTerminal.lean
statement: `theorem succ_terminal (n : ℕ) (s : Species) (h : s.sel = none) :
Succ n s = ∅` AND `theorem stageLaws_terminal (s s' : Species)
(h : s.sel = none) : ¬ StageLaws s s'` [REV 2: second statement in full]
moves_ref: "and SUCC(s) := ∅ for terminal s (selection ⊥)."
deps: — · sketch: unfold StageLaws; the match's none-branch is False; Succ empty
via its StageLaws conjunct. · difficulty: easy

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
[REV 2, F9 — binders in full]
statement: `theorem sh_dvd (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
(hγ : γ = e * u0 + s0 * h) (k : ℤ) : e ∣ (s0 + k * e - t * γ)`
(no `1 ≤ e` hypothesis: pure divisibility, degenerate e included)
moves_ref: "(SH-G) p_j(γ) = (j − t·γ)/e ∈ ℤ (D.3(c))" [j = j_k = s₀′ + k·e].
deps: Sp.shCongr · sketch: s0 − t·γ ≡ 0 [ZMOD e] from shCongr; add k·e.
difficulty: easy

**Sp.shSlots** · SP1_shSlots.lean
[REV 2, F10 — binders in full, both theorems]
statement: `theorem sh_slots (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
(hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (k : ℤ) :
Sh t γ e (geoPos e t γ (s0 + k * e)) = s0.fdiv e + k` AND
`theorem sh_anchor (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
(hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) :
Sh t γ e (geoPos e t γ s0) = s0.fdiv e` (= sh_slots at k = 0)
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
[REV 2, F11 — the spurious hypothesis struck; both statements in full]
statement: `def shEquiv (σ : ℤ) : ℤ ≃ ℤ := Equiv.addRight σ` +
`theorem sh_image (t γ e ag : ℤ) (ℓ : ℕ) :
(Finset.Icc ag (ag + ℓ)).image (Sh t γ e) = Finset.Icc (ag + shSigma t γ e)
(ag + shSigma t γ e + ℓ)` (pure interval translation — NO extra hypothesis) AND
the census identification `theorem sh_geo_slots (e h s t γ u0 s0 : ℤ)
(he : 1 ≤ e) (hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (ℓ : ℕ) :
(Finset.image (fun k : Fin (ℓ + 1) => Sh t γ e (geoPos e t γ (s0 + k * e)))
Finset.univ) = Finset.Icc (s0.fdiv e) (s0.fdiv e + ℓ)` (the geometric slot set
carried onto the census slot set)
moves_ref: "Sh_{t,γ} is an affine bijection carrying the geometric slot set onto
the census slot set and a^geo onto a, ALL OTHER FIELDS FIXED".
deps: Sp.shSlots (for sh_geo_slots) · sketch: sh_image by
`Finset.image_add_right_Icc`; sh_geo_slots: rewrite each image point by
Sp.shSlots, then Fin-indexed image of k ↦ a + k is the Icc. · difficulty: easy

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
[REV 2, F12 — the corollary spelled in full]
statement: `theorem sh_congr_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F]
[Finite F] (σs : Moves.Stage p F) (γ u0 s0 : ℤ)
(hγ : γ = σs.e * u0 + s0 * σs.h) : σs.t * γ ≡ s0 [ZMOD σs.e]` AND
`theorem sh_e1_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F] [Finite F]
(σs : Moves.Stage p F) (γ s0 : ℤ) (he1 : σs.e = 1) :
shSigma σs.t γ σs.e = 0 ∧ Sh σs.t γ σs.e (geoPos σs.e σs.t γ s0) = s0`
(σ = 0 AND the position identity — the "systems coincide" display at a Stage;
via `σs.he1t he1 : σs.t = 0` and Sp.shE1)
moves_ref: "At a stage with read index (e, h) and pinned Bézout pair (s, t)
(e·s + t·h = 1; (P2): t = 0 at e = 1)".
deps: Sp.shCongr, Sp.shE1 · sketch: instantiate at (σs.e, σs.h, σs.s, σs.t) via
σs.hbez (mind the ℕ→ℤ casts); sh_e1_stage rewrites σs.t = 0 (he1t) into
Sp.shE1. · difficulty: easy

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
gives postRec. (←) instantiate StageLaws' match; the laws reflexive at e = g = 1,
μ = W; coherence/budget from hc/hb. · difficulty: medium

**Sp.selfloopFull** · SP4_selfloopFull.lean
[REV 2, F13 — hypothesis types in full]
statement: `theorem selfloop_isFull {n : ℕ} {s : Species} (hc : Coherent s)
(hb : Budget n s) (h : SuccStep n s s) : IsFull s ∧ s.tag = .postRec`
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

**Sp.rankRadix** · SP4_rankRadix.lean  [REV 2, F14 — fullBit defined in §2;
hypotheses and the four-case disjunction spelled in full]
statement: `theorem rankNat_lt {n : ℕ} {s : Species} (hn : 1 ≤ n)
(hc : Coherent s) (hb : Budget n s) : rankNat n s < 6 * n ^ 2` AND
`theorem rankNat_lt_of_lex {n : ℕ} {s s' : Species}
(hc : Coherent s) (hb : Budget n s) (hc' : Coherent s') (hb' : Budget n s')
(h : s.D < s'.D ∨
     (s.D = s'.D ∧ tagord s.tag < tagord s'.tag) ∨
     (s.D = s'.D ∧ s.tag = s'.tag ∧ n - s.W < n - s'.W) ∨
     (s.D = s'.D ∧ s.tag = s'.tag ∧ s.W = s'.W ∧ fullBit s < fullBit s')) :
rankNat n s < rankNat n s'`
moves_ref: "(ii) The rank ρ(s) := ( D,  tagord,  n − W,  1 − [s is full] ),
tagord := 0/1/2 for ROOT/POST-INC/POST-REC" + "it has at most |range(ρ)| ≤
n·3·n·2 = 6n² letters".
deps: — · sketch: digit bounds D − 1 < n (B1 + WellTyped), tagord < 3,
n − s.W < n (W ≥ 1), fullBit < 2; both claims are mixed-radix arithmetic —
unfold rankNat, `rcases` the disjunction, `omega` per case (the ordinary
strict-mono of a 4-digit radix-(n,3,n,2) numeral). · difficulty: medium

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

### F. SP-COMP (conditional — the interface layer), words, entrances

[REV 2, F1/F2: restated over `CanTreeModel` with the note's full quantifier
prefix (n, p, f, η ∈ T_can(f), r); the conclusions `InCatalogue`/`SuccStep`/
`Out`-membership occur in NO hypothesis field — the fields are the RAW engine
laws (§2), and the units' content is the note's own "reachability by induction
along the word".]

STANDING hypothesis_fields FOR THIS GROUP (each cited at its §2 field): hRoot,
hStage, hCoh, hHalt (SP-COMP proof steps (1)/(2)/(3)/(3′)/(5) — §B2-DEF
D.4/D.5/D.6/D.7/D.8/D.10 + §C DOM via §D4-R L11 + §D4-R L2/L3/L5; owner
HC-1/MovesD; OPEN, never proved here) and hVerdictPin (THE D4R.0-K(c)
RESIDUAL — the verdict pin, owner [3t] via VP; explicit per F7). FENCE
[REV 3, G3 — retargeted to the closure side]: NEVER strengthen — no field may
mention the CLOSURE-side objects `InCatalogue`, `Succ`, or `Out` (the
conclusions; the inductively generated catalogue). The per-read fields ARE the
note's engine outputs, and jointly they unfold to RootAdmissible at r = 0 and
to SuccStep per step — that is not a leak but the note's own scoping: steps
(1)–(3′)/(5) hand the closure exactly its premises, and the units' content is
the quantified induction, not a logical gap between fields and premises.
NEVER drop (hCoh's coherence stays).

**Sp.compMember** · SP3_compMember.lean
statement: `theorem SP_COMP (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
(hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
(η : M.Branch) (r : ℕ) (hr : r < M.len η) : InCatalogue n (M.datum η r)`
(hf/hdeg carry the note's "f in the monic degree-n coefficient box" binder —
unused computationally, kept for quantifier fidelity, linter-silenced)
moves_ref: "For every n, every prime p, every f in the monic degree-n
coefficient box, every chain η ∈ T_can(f) …, and every read r of η's CATALOGUE
WORD …: the read's retained datum is a member of 𝒮_n^raw".
deps: — · sketch: induction on r: r = 0 via `InCatalogue.root` (M.hRoot gives
RootStage + Coherent + Budget = RootAdmissible); r + 1 via `InCatalogue.step`
with SuccStep ASSEMBLED from M.hStage (StageLaws) + M.hCoh at r + 1
(Coherent ∧ Budget) — the assembly is the derivation, not an assumption.
difficulty: easy-medium
hypothesis_fields: the standing group list above; hVerdictPin UNUSED by this
unit's proof but part of the interface it quantifies over. [REV 3, G4 — what
IS enforced:] the field keeps the D4R.0-K(c) conditionality VISIBLE — named in
the interface every consumer instantiates — but does NOT type-enforce it: a
model discharges (verdict, hVerdictPin) trivially (e.g. verdict := fun _ =>
some .z), WHICH verdict being deliberately VP-owned; the ledger rides in the
named field + its docstring, and Lean-side SP_COMP is equally strong without
it. Faithful to the note: the residual is a cited OPEN kernel, not a
consumed premise of steps (1)–(3′)/(5).

**Sp.compEdges** · SP3_compEdges.lean
statement: `theorem SP_COMP_edges (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
(hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
(η : M.Branch) (r : ℕ) (hr : r + 1 < M.len η) :
Sum.inl (M.datum η (r + 1)) ∈ Out n (M.datum η r)`
moves_ref: "each consecutive read pair is linked by an edge of the syntactic
menu Out (SP.4)" + step (5): "which is precisely SP.4's edge relation; so each
realized transition is an Out edge."
deps: Sp.compMember · sketch: Succ-membership = InCatalogue (compMember at
r + 1) ∧ SuccStep (assembled as in compMember); then `Or.inl` into Out.
GENUINE step: the conclusion's Out is defined through InCatalogue, which no
field supplies. · difficulty: easy
hypothesis_fields: the standing group list above.

**Sp.tauWord** · SP3_tauWord.lean  [REV 2, F3 — the halt endpoint is now a
STRUCTURE LAW of CatalogueWord (§2: hLast forces W = 1 at the last letter,
hFirstW1 forbids earlier confirming reads); the theorem is unconditional]
statement: `theorem tauWord_spec {n : ℕ} (cw : CatalogueWord n) :
cw.tauWord.length + 1 = cw.word.length ∧
(∀ s, cw.word.getLast? = some s → s.W = 1 ∧ s.sel = none) ∧
(∀ s ∈ cw.tauWord, s.W ≠ 1 ∧ s.sel ≠ none)`
moves_ref: "the CATALOGUE WORD (SP-COMP's quantifier, the census's object)
closes at the confirming read; the τ-WORD (every density consumer's object) is
the catalogue word with that final confirming letter removed".
deps: Sp.memCoherent · sketch: length via `List.length_dropLast` + hne;
sel = none at the last letter from hLast + (G6) (memCoherent through hMem);
sel ≠ none on tauWord from hFirstW1 + (G6). · difficulty: easy
hypothesis_fields: verdict pinning (WHERE the halt verdict sits — parent read /
level-0 track) is VP's, NOT stated; only the word arithmetic is.

**Sp.n1RootConfirming** · SP3_n1Root.lean  [REV 3, G2 — split from the rev-2
Sp.n1Clause to break the n1singleton cycle: this half has NO n = 3/enum deps]
statement: `theorem n1_root_confirming {s : Species} (h : RootAdmissible 1 s) :
s.W = 1 ∧ s.sel = none`
moves_ref: "At n = 1 the catalogue word is the single ROOT letter (W = n = 1,
selection ⊥ — (G6)'s degenerate degree)".
deps: — · sketch: RootStage gives W = n = 1; (G6) gives sel = none.
difficulty: easy
hypothesis_fields: (τ-hen) SEMANTICS is VP's — only letter arithmetic stated.

**Sp.n1Word** · SP3_n1Word.lean  [REV 3, G2 — the other half; DAG:
n1RootConfirming → n1singleton → n1Word, acyclic]
statement: `theorem n1_word (cw : CatalogueWord 1) :
cw.word.length = 1 ∧ cw.tauWord = []`
moves_ref: "the τ-WORD is EMPTY (the standing rule 'catalogue word minus the
final confirming letter' applied to the one-letter word …); the CATALOGUE WORD
is the single confirming root letter".
deps: Sp.n1singleton, Sp.memCoherent · sketch: every letter of cw is
InCatalogue 1 (hMem) = confirmingRoot1 (n1singleton), so every letter has
W = 1; hFirstW1 then empties dropLast; length 1; tauWord = dropLast = [].
difficulty: easy-medium
hypothesis_fields: as Sp.n1RootConfirming.

**Sp.collapseWalk** · SP3_collapseWalk.lean  [REV 2, F4 — new: wires words to
SP-DAG]
statement: `theorem collapseRuns_collapsedWalk {n : ℕ} {l : List Species}
(hmem : ∀ s ∈ l, InCatalogue n s) (hch : l.Chain' (SuccStep n)) :
CollapsedWalk n (collapseRuns l)` AND `theorem collapseRuns_sublist
(l : List Species) : (collapseRuns l).Sublist l`
moves_ref: "a loop-collapsed entrance word is a collapsed walk in the menu
graph" + "(the number of letters after collapsing self-loop runs)".
PLUS the G1 pinning lemmas [REV 3]: `theorem collapseRuns_ne_nil {l : List
Species} (h : l ≠ []) : collapseRuns l ≠ []` and `theorem
collapseRuns_eq_self_iff (l : List Species) : collapseRuns l = l ↔
l.Chain' (· ≠ ·)` (with §2's defining equations, these exclude every
degenerate implementation — const-[] fails both)
deps: — · sketch: consecutive-dedup keeps membership (Sublist) and keeps
exactly the SuccStep edges with s ≠ s′ (a run boundary is a non-loop edge);
induction on l with the two-head case split; the pinning lemmas via Mathlib's
`List.destutter` API where it applies. · difficulty: medium

**Sp.entranceDef** · SP3_entrance.lean  [REV 2, F4 — EntranceShape (§2) now
carries the block-entry selection (gsel, μsel) + height/depth parameter slots;
the finiteness theorem quantifies over EntranceShape itself]
statement: `theorem entrance_collapsed_finite (n gsel μsel : ℕ) (hn : 1 ≤ n) :
{l : List Species | ∃ E : EntranceShape n gsel μsel, collapseRuns E.word = l}.Finite`
AND `theorem entrance_collapsed_len {n gsel μsel : ℕ} (hn : 1 ≤ n)
(E : EntranceShape n gsel μsel) : (collapseRuns E.word).length ≤ 6 * n ^ 2`
moves_ref: "so it has ≤ 6n² letters (SP-DAG(iii)); with SP-FIN the family of
such words is finite and p-independent — {ε} is finite up to its (height pair,
depth) parameters, which is exactly the finiteness CTS-M(iii) consumes".
deps: Sp.collapseWalk, Sp.dagWalk, Sp.dagWords · sketch: E.word is a member-
wise catalogued SuccStep chain (E.hMem, E.hChain); collapseRuns gives a
CollapsedWalk (collapseWalk), so ≤ 6n² (dagWalk) and the image set sits inside
the finite collapsed-word set (dagWords). The parameters (heights, depths) are
quantified AWAY by the image construction — "up to its parameters", exactly.
difficulty: medium
hypothesis_fields: the size-e-block / landing-cell β₀ IDENTIFICATION of the
entry datum is [1v] CTS-M(iii)'s (owner, cited); per-shape masses ι_{e,ε,β₀}
and entrance counts are [1]/[1v] objects, never assigned here.

[REV 2, F15] **Sp.mcRoster: STRUCK — deferred to MovesS (wave 4).** Its only
anchor is §S-RESUM (K-SUB)'s (m, c) CLASSIFICATION — not a display of the
frozen §M-SPECIES text, so it has no in-scope moves_ref. The defs (mOf, cOf,
OutcomeClass) move to the MovesS blueprint, defined there on this corpus's
`Species.lam` (additive import; §2's deferral record).

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

**Sp.n3rootLetters** · SP6_rootLetters.lean  [REV 2, F16 — ONE statement, the
membership equivalence the note asserts; multiplicity content carried by
n3card53's Nodup, so duplicate enum candidates (repeated equal λ-factors in
the generator) are harmless]
statement: `theorem rootAdmissible3_iff (s : Species) :
RootAdmissible 3 s ↔ s ∈ groupR`, proved from the two decide facts
`theorem root3_enum_check : ((speciesEnum 3).all fun s =>
rootAdmissibleB 3 s == (s ∈ groupR : Bool)) = true` and
`theorem groupR_admissible : (groupR.all (rootAdmissibleB 3)) = true`
moves_ref: "GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters." + "per
stage, the (G1)–(G6)+(B1)–(B5corrected) letters are exactly the displayed rows".
deps: Sp.speciesEnumComplete, Sp.reflSucc (rootAdmissibleB_iff) · sketch: (→)
RootAdmissible ⇒ Coherent ∧ Budget ⇒ s ∈ speciesEnum 3 (enumComplete), then
root3_enum_check reads off membership; (←) groupR_admissible + the reflection
iff. · difficulty: medium (perf)

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
[REV 3, C1 — target reordered to catalogue3's pinned order: loopQ3 ∈ groupQ3
precedes loopQ23 ∈ groupQ2 in groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI]
statement: `theorem loops3 : catalogue3.filter (fun s => succStepB 3 s s) =
[loopQ3, loopQ23]`
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

**Sp.n3R3check** · SP6_R3check.lean  [REV 2, F6 — BOTH flank variants, as the
two named letters of §4]
statement: `theorem R3_members : coherentB R3letterA = true ∧
budgetB 3 R3letterA = true ∧ R3letterA ∈ groupR ∧ R3letterA.a = 2 ∧
R3letterA.lflank = [2] ∧ coherentB R3letterB = true ∧
budgetB 3 R3letterB = true ∧ R3letterB ∈ groupR ∧ R3letterB.a = 2 ∧
R3letterB.lflank = [1, 1]`
moves_ref: "R3 = (ROOT, (D,w,W) = (1,1,3), e = 1, ℓ = 1, a = 2, s₀′ = 2, slots
{2,3}, λ = {(1,1)} ▸ (1,1), left flank (2) or (1,1), right empty)" + "(B5,
corrected anchor bound) a = 2 ≤ ⌊(W − w′)/e⌋ = 2 ✓ (saturated)".
deps: DefsN3 · sketch: decide — the note's own saturating witnesses for the
corrected (B5), one per flank composition. · difficulty: easy

**Sp.n3thresholdData** · SP6_thresholdData.lean  [REV 2, F5 — CONTENT-pinned:
the lists are decided EQUAL to the note's λ-defined filters and to the named
letters, never cardinality-only]
statement: `theorem threshold_data_pinned :
catalogue3.filter (fun s => 2 ≤ linCount s) = fieldSizeExcluded2 ∧
catalogue3.filter (fun s => 3 ≤ linCount s) = fieldSizeExcluded3 ∧
multiSide6 = [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c] ∧
(multiSide6.all (· ∈ groupQ3)) = true ∧
Nstar3six msQ3R1 = some 7 ∧ Nstar3six msQ3R2 = some 6 ∧
Nstar3six msQ3R3 = some 6 ∧ Nstar3six msQ3R4a = some 6 ∧
Nstar3six msQ3R4b = some 6 ∧ Nstar3six msQ3R4c = some 6 ∧
(catalogue3.all fun s => (Nstar3six s ≠ none : Bool) == (s ∈ multiSide6 : Bool))
= true ∧ fieldSizeExcluded2.length = 11 ∧ fieldSizeExcluded3.length = 2`
(the filter identities pin the λ-content: linCount counts monic-linear factors
with multiplicity — q = 2 has ONE nonzero root, so ≥ 2 distinct linears
excluded; q = 3 has TWO, so ≥ 3 excluded; lengths kept as trailing sanity)
moves_ref: "p = 2 (one nonzero root): the 11 letters with λ ⊇ two distinct
linears — {(1,1)²}: … {(1,2),(1,1)}: … {(1,1)³}: …; p = 3 (two nonzero roots):
exactly the 2 letters with λ = {(1,1)³}" + "THE SIX COMPUTATIONS …: the
sel-carrying Q3 copies …: Q3(R1, right flank (1,1)), Q3(R2), Q3(R3, left flank
(1,1)), and the three Q3(R4) λ-rows … N*_3 = 6; … N*_3 = 6; … N*_3 = 7."
deps: DefsN3 · sketch: decide throughout (53-letter filters + 6 named-value
reads). DEFINITIONS + internal pinning only — realizability semantics stays
out (§0; the note: "the queued re-seal gate's SEALED PREDICTION, not a theorem
of this note"). · difficulty: easy
hypothesis_fields: none stated — but the docstrings MUST carry the note's
typing: field-size pass is "NECESSARY for realization, NOT sufficient"; N*₃
values are gate-censused data (M-n3-V2), not theorems.

**Sp.n3entrancePatterns** · SP6_entrance.lean  [REV 2, F17: full roster, no
ellipses; REV 3, C2: the ▸(1,2) rosters corrected to their TRUE three members
per group — the note's own R6 row {(1,2),(1,1)}▸(1,2) is a root ▸(1,2) letter
and its menu law "▸(1,2) → Q2 letters" is row-unrestricted; the entrance
display's "[R4/R5 rows]" bracket is an ERRATUM CANDIDATE, verified at §9 and
NOT baked into any target]
statement: `theorem entrance3_patterns :
-- into the μ=2 block, direct: root▸(1,2) = the ▸(1,2) rows of R4/R5/R6
-- (three members; §9 — the note's bracket omits R6's)
(groupR.filter fun s => s.sel == some (1, 2)) =
  [rootR4sel12, rootR5sel12, rootR6sel12] ∧
-- into the μ=2 block, via the μ=3 loop: root▸(1,3)·(Q3-loop)^d·▸(1,2)
succStepB 3 rootR6sel13 loopQ3 = true ∧
succStepB 3 loopQ3 loopQ3 = true ∧
((groupQ3.filter fun s => s.sel == some (1, 2)).all fun q =>
  succStepB 3 loopQ3 q) = true ∧
((groupQ3.filter fun s => s.sel == some (1, 2)).length = 3) ∧
-- into the μ=3 block: root▸(1,3)
rootR6sel13.sel = some (1, 3) ∧ rootR6sel13 ∈ groupR ∧
-- into the increment landings (D ≥ 2): the ▸(2,1)/▸(3,1)/e=2/e=3 rows of
-- R, Q2, Q3, each stepping into its I letter
((catalogue3.filter fun s => s.sel == some (2, 1)).all fun s =>
  succStepB 3 s letterI22) = true ∧
((catalogue3.filter fun s => s.sel == some (3, 1)).all fun s =>
  succStepB 3 s letterI33) = true ∧
((catalogue3.filter fun s => (s.e == 2) && !(s.sel == none)).all fun s =>
  succStepB 3 s letterI21) = true ∧
((catalogue3.filter fun s => (s.e == 3) && !(s.sel == none)).all fun s =>
  succStepB 3 s letterI31) = true ∧
-- …and each such row lives in R, Q2, or Q3 (never I, Q1: those are terminal)
((catalogue3.filter fun s => s.sel == some (2, 1) || s.sel == some (3, 1) ||
  ((s.e == 2 || s.e == 3) && !(s.sel == none))).all fun s =>
  s ∈ groupR ++ groupQ2 ++ groupQ3) = true`
(the loop-power (Q3-loop)^d is witnessed by the ONE loop edge — depth d is a
parameter, not a letter: EntranceShape's depth slot, SP-DAG scope)
moves_ref: "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as depth slots): into
the μ=2 block: root▸(1,2) [R4/R5 rows], or root▸(1,3)·(Q3-loop)^d·▸(1,2); into
the μ=3 block: root▸(1,3); into each increment landing (D ≥ 2): the
▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3 prefixed by their cascades — a finite
list, displayed by the same map." [the bracket read per §9's verified
correction: the ▸(1,2) rows of R4/R5/R6]
deps: DefsN3 · sketch: decide per conjunct (filters over 53/21; edge checks).
difficulty: easy

**Sp.n1singleton** · SP6_n1singleton.lean
statement: `theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1`
(confirmingRoot1 := the W = 1 root letter at stage (1,1,1))
moves_ref: "(G6) … (or W = n = 1 at the root — the degenerate degree)" + the n = 1
clause: "At n = 1 the catalogue word is the single ROOT letter".
deps: Sp.speciesEnumComplete, Sp.n1RootConfirming, Sp.succTerminal
[REV 3, G2 — was Sp.n1Clause; the cycle is split: only the root-confirming
half is consumed here, and Sp.n1Word consumes THIS unit] · sketch: root-admissible
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
   this corpus; MovesX reads SP.4/SP-DAG; MovesS defines its (m, c) roster on
   `Species.lam` ITSELF (the F15 deferral — §2's record; wave-4 sync item).

## 7. Roster summary  [REV 3]

57 units + 3 def-only files (Defs, DefsEnum, DefsN3). By group: A reflection/
closure 5 · B shift block 8 · C coherence/budget 4 · D SP-FIN 6 · E SP-OUT/
SP-DAG 11 · F SP-COMP/words/entrance 7 (mcRoster STRUCK per F15; collapseWalk
ADDED per F4; n1Clause SPLIT into n1RootConfirming + n1Word per G2) ·
G enumeration 3 · H n = 3 decide layer 13.

easy: 30 — all of A; shCongr/shDvd/shE1/shEquiv/shStage/shExample;
  anchorBoundGeo/b4Derived; encodeCard; outFinite/selfloopFull/fullUnique/
  rankStepInc/rankStrict; compEdges/tauWord/n1RootConfirming; n3card53/
  n3reachable/n3selfloops/n3postincW1/n3terminal5/n3R3check/n3thresholdData/
  n3entrancePatterns.
medium: 23 (incl. 3 easy-medium: compMember, n1Word, n1singleton) — shSlots/
  shAnchorInv; anchorBoundCensus/g6Forcing; compEncode/lamEncode/finThm/
  finWords; selfloopChar/fullForcing/rankRadix/dagWalk/dagWords; collapseWalk/
  entranceDef; compEnumComplete; n3rootLetters/n3closureStep/n3catalogueEq/
  n3menuMap.
medium-hard: 4 — encodeInj, rankStepRec, lamEnumComplete, speciesEnumComplete.
hard: 0.

No unit expects > ~40 proof lines; the four medium-hard units carry
pre-approved split points (encodeInj: scalar vs flank/λ blocks; rankStepRec:
the three branches; lamEnumComplete: sorted-list core vs Multiset boundary;
speciesEnumComplete: per-field range lemmas).

## 8. REV 2 findings → repairs (audit MOVESSP_AUDIT_CODEX_2026-07-28.md)

  F1  crit compMember circular      → CanTreeModel (raw engine laws only: hRoot/
      hStage/hCoh/hHalt); full (n, p, f, η, r) prefix; SuccStep ASSEMBLED in
      the proof, InCatalogue concluded (§2 + group F).
  F2  crit compEdges circular       → same interface; Out-membership concluded
      through compMember's InCatalogue (no field mentions Out/Succ).
  F3  crit CatalogueWord endpoint   → structure laws hLast (last letter W = 1)
      + hFirstW1 (no earlier confirming read); tauWord_spec unconditional.
  F4  crit EntranceShape too weak   → block-entry selection (gsel, μsel) typed;
      height-pair + per-run depth parameter SLOTS as fields; finiteness theorem
      quantifies over EntranceShape via new collapseRuns/collapseWalk.
  F5  crit thresholdData unpinned   → filter identities on linCount (λ-content)
      + named-letter list equalities + per-name N*₃ values; lengths demoted to
      trailing sanity.
  F6  crit R3 single variant        → R3letterA ([2]) and R3letterB ([1,1])
      both defined, both checked.
  F7  gap  D4R.0-K(c) by omission   → explicit field CanTreeModel.hVerdictPin;
      §0 bullet rewritten; named in every group-F hypothesis_fields.
  F8  gap  reflSucc elided          → both iffs spelled with full binders;
      moves_ref extended to the root clause.
  F9  gap  shDvd "same hyps"        → full binder list; e ≥ 1 explicitly NOT
      assumed (recorded).
  F10 gap  shSlots elided           → both theorems with complete binders.
  F11 gap  shEquiv non-Prop hyp     → hypothesis struck; sh_image pure; census
      identification as fully-stated sh_geo_slots.
  F12 gap  shStage corollary        → sh_e1_stage spelled (σ = 0 + position
      identity at a Moves.Stage).
  F13 gap  selfloopFull types       → (hc : Coherent s) (hb : Budget n s) in
      the statement.
  F14 gap  rankRadix unauditable    → fullBit defined in §2; hypotheses and the
      four-case disjunction written out.
  F15 gap  mcRoster out-of-scope    → STRUCK; deferred to MovesS wave-4 (records
      in §2, group F, §6).
  F16 gap  rootLetters ambiguity    → ONE canonical statement (the membership
      equivalence) from two decide facts; multiplicity content via n3card53's
      Nodup; duplicate-candidate caveat recorded.
  F17 gap  entrancePatterns ellipsis→ full conjunction, one clause per displayed
      pattern, all letters named.

## 8b. REV 3 findings → repairs (audit MOVESSP_AUDIT_FABLE_2026-07-28.md)

  C1  crit loops3 order-false       → target reordered [loopQ3, loopQ23]
      (catalogue3 = R ++ Q3 ++ Q2 ++ Q1 ++ I); ORDER DISCIPLINE rule added at
      §4 with a full audit of every pinned-list decide target (terminal3 ✓,
      entrance groupR filter ✓, fieldSizeExcluded2/3 declared in catalogue3
      order, all other targets membership/`all`-form).
  C2  crit entrance ▸(1,2) roster   → corrected to the true THREE members per
      group ([rootR4sel12, rootR5sel12, rootR6sel12]; Q3 length 3), per the
      note's own R6 row and row-unrestricted menu law; the note-side
      "[R4/R5 rows]" bracket recorded as a VERIFIED erratum candidate (§9),
      cited by the unit, baked into no target.
  G1  gap  collapseRuns unpinned    → defining equations written into §2 (=
      List.destutter (· ≠ ·)); pinning lemmas collapseRuns_ne_nil +
      collapseRuns_eq_self_iff added to Sp.collapseWalk (const-[] now fails
      the def AND both lemmas).
  G2  gap  n1 dependency cycle      → Sp.n1Clause split: Sp.n1RootConfirming
      (no enum deps) → Sp.n1singleton → Sp.n1Word; deps rewritten; DAG
      acyclic.
  G3  gap  fence vs hRoot           → fence retargeted to CLOSURE-side objects
      only (InCatalogue/Succ/Out); the fields-unfold-to-premises fact stated
      as the note's own step-(1)–(3′)/(5) scoping, not a leak.
  G4  gap  non-detachable overclaim → weakened to "visible": the trivial
      (verdict, hVerdictPin) discharge displayed; ledger carried by the named
      field + docstring, not by the type.

## 9. NOTE ERRATUM CANDIDATE (routed to the coordinator; NOT applied to the
frozen note by this blueprint)

LOCATION: `lean/notes/MOVES_2026-07-24.md`, §M-SPECIES SP.6, the entrance
display (locate by text, per the note's own grep-anchor convention):

  "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as
   depth slots): into the μ=2 block: root▸(1,2) [R4/R5 rows], or
   root▸(1,3)·(Q3-loop)^d·▸(1,2); …"

FINDING (CONFIRMED as an incomplete gloss; Fable audit C2 root cause): the
bracket "[R4/R5 rows]" omits R6's ▸(1,2) row. Cross-check against the note's
OWN displays:
 (1) the hand catalogue's R6 row lists a ▸(1,2) selection —
     "R6  e=1, ℓ=3, a=0 | {(3,1)}▸(3,1); {(2,1),(1,1)}▸(2,1) and ▸(1,1);
      {(1,3)}▸(1,3); {(1,2),(1,1)}▸(1,2) and ▸(1,1); {(1,1)³}▸(1,1)" —
     a ROOT letter whose designated selection is (1, 2);
 (2) the menu law is row-unrestricted — "▸(1,2) → Q2 letters" — so that
     letter's continuing branch opens the child window [0, 2]: the μ=2 block;
 (3) the same display's increment-landing clause quantifies over "the
     ▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3" — the roster-of-rows form the
     ▸(1,2) clause evidently intends.
The head clause "root▸(1,2)" is CORRECT as stated; only the parenthetical
bracket is incomplete. PROPOSED CORRECTION: "[R4/R5 rows]" → "[the ▸(1,2)
rows of R4/R5/R6]" (three letters; likewise three Q3 copies on the loop-exit
path). No count, menu edge, or gate quantity of the note changes: the 53, the
menu map, and the M-n3/V2 gate records are untouched (the census walked the
true menu; only the gloss bracket under-listed). Blueprint-side: unit
Sp.n3entrancePatterns pins the TRUE roster and cites this section; nothing
silently repairs the note.
