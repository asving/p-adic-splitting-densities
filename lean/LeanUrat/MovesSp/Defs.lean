/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs   -- reuse: HasAnchorK, Stage (bridging unit only)

/-!
# MovesSp/Defs — the §M-SPECIES species datum, coherence, closure, and interfaces

E-phase transcription of `lean/notes/MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` §2 (rev 5,
dual-accepted 0/0). SOURCE OF TRUTH: `lean/notes/MOVES_2026-07-24.md` §M-SPECIES
(rev-8 text, DUAL-ACCEPTED 2026-07-27). Definitions and structures only — no theorems,
no `sorry`. The Bool reflection layer and the generated enumeration live in
`MovesSp/DefsEnum.lean`; the sealed n = 3 data in `MovesSp/DefsN3.lean`.

Conditionality ledger (blueprint §0): `CanTreeModel`'s fields are OPEN engine laws
(owner HC-1/MovesD; §B2-DEF D.4/D.5/D.7/D.8/D.10 + §C DOM via §D4-R L11 + §D4-R
L2/L3/L5), consumed as hypotheses, never proved here; `hVerdictPin` is the D4R.0-K(c)
residual (owner [3t] via VP), the ledger's named carrier, weak by design. FENCE
[REV 3, G3]: no field mentions the closure-side objects `InCatalogue`/`Succ`/`Out`.
p-independence of `SnRaw` is discharged BY TYPING: no field mentions a prime.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

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
deriving DecidableEq
-- [E-PHASE DEVIATION D1] `Repr` dropped from Species ONLY: `Finset.instRepr` is an
-- unsafe instance, so `deriving Repr` fails kernel compilation on the `slots` field.
-- Purely cosmetic (Repr is never consumed by any unit); DecidableEq retained.

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
  /-- TOTALITY PIN [REV 4, Codex-1]: T_can(f) is nonempty — "kernel D4R.0-K
  parts (a) totality … are DISCHARGED (D4R0K_DERIVATION rev 3, dual-verified
  2026-07-27)"; the EMPTY model now violates a field. -/
  hTotal : Nonempty Branch
  /-- length of η's CATALOGUE WORD in ℕ∞ [REV 4, Codex-1 — infinite branches
  are REPRESENTED: len η = ⊤ is the prefixwise-catalogued infinite chain
  ("Infinite branches are catalogued prefixwise", SP.5). len η = 0 stays a
  REAL case AT n ≥ 2 ("(τ-hen) ROOT HENSEL LEAVES — … halts with NO window
  read ever opened": a Hensel track below a SPLIT f̄ carries no catalogue
  letter). REFINED at REV 5 (Codex rev-4 crit — the conflation conceded AT
  n = 1): at n = 1 the note's word is NONEMPTY — see hN1.] -/
  len : Branch → ℕ∞
  /-- THE n = 1 CLAUSE AS A MODEL LAW [REV 5, Codex rev-4 crit]: "At n = 1 the
  catalogue word is the single ROOT letter (W = n = 1, selection ⊥ — (G6)'s
  degenerate degree)" — only the τ-WORD is empty. So at n = 1 no branch has an
  empty catalogue word; the all-len-0 CanTreeModel at n = 1 now VIOLATES this
  field. Stated as nonemptiness only: len η = 1 and datum η 0 = the confirming
  root letter are then DERIVED (Sp.n1Branch) via hRoot + hHalt + n1singleton —
  the minimal field carrying the display. -/
  hN1 : n = 1 → ∀ η, 0 < len η
  /-- the retained datum of read r < len η (junk above). -/
  datum : Branch → ℕ → Species
  /-- step (1)+(3)+(3′) at r = 0: root stage (D, w, W) = (1, 1, n), datum
  coherent and budget-admissible [§B2-DEF D.0 key x; §D4-R L3/L5; §C DOM]. -/
  hRoot : ∀ η, 0 < len η →
    RootStage n (datum η 0) ∧ Coherent (datum η 0) ∧ Budget n (datum η 0)
  /-- steps (2)/(5): the raw stage laws per consecutive read pair ["the stage
  fields of read r+1 are the D.7/D.8/D.10 outputs"]. -/
  hStage : ∀ η (r : ℕ), (r + 1 : ℕ∞) < len η →
    StageLaws (datum η r) (datum η (r + 1))
  /-- steps (3)+(3′) at every read: budgets and coherence ["Budgets hold at
  every read" / "Geometric coherence holds at every read"]. -/
  hCoh : ∀ η (r : ℕ), (r : ℕ∞) < len η →
    Coherent (datum η r) ∧ Budget n (datum η r)
  /-- the catalogue-word endpoint: the word closes AT its first confirming
  W = 1 read [SP-COMP: "up to and including its first W = 1 read"]. -/
  hHalt : ∀ η (r : ℕ), (r : ℕ∞) < len η → (datum η r).W = 1 →
    len η = (r + 1 : ℕ∞)
  /-- step (4): the leaf verdict of a FINITELY-ENDED chain, from V_term. -/
  verdict : Branch → Option Verdict
  /-- step (4)'s law — THE D4R.0-K(c) RESIDUAL AS AN EXPLICIT, NAMED RIDER
  [REV 2 F7; REV 4, Codex-2 — scope WIDENED to every finite nonempty word:
  the note ends words at terminal ⊥-reads AND at V_term edges from CONTINUING
  letters ("Edges into V_term from a CONTINUING letter … end both words at
  that letter"), and in both cases "the chain's τ-leaf carries that verdict";
  infinite branches (len = ⊤) carry none]. HONEST PERIMETER (the G4 record
  stands): the field carries the residual's ALPHABET (V_term as codomain) and
  its ATTACHMENT SITE (finite words), NOT the halting rule τ or the uniform
  detection cap — those are the kernel's CONTENT, owned by [3t] via VP and
  deliberately not encodable from §M-SPECIES's text; the field is the
  ledger's named carrier, weak by design, trivially dischargeable, and every
  SP-COMP unit's hypothesis_fields says so. -/
  hVerdictPin : ∀ η (m : ℕ), len η = (m : ℕ∞) → 0 < m → (verdict η).isSome

/-- A CATALOGUE WORD (SP-COMP's quantifier + SP.4's HALT CONVENTION) [REV 2,
F3]: letters in 𝒮ₙ^raw, Out-linked, and FORCED to close at the FIRST confirming
W = 1 read — the endpoint is a structure law, not an antecedent. (Words ended by
a V_term edge from a CONTINUING letter, and infinite branches, are catalogued
prefixwise via `CanTreeModel`, not by this structure.)

SCOPE [ratification N1, `lean/notes/MOVESSP_RATIFY_CODEX_2026-07-30.md`]: this
datatype is the CONFIRMING-ENDING SUBTYPE of the note's word notion — the
verdict, quoted: "Its laws require a nonempty word whose last letter has W = 1.
The note also allows finite words ending at a V_term edge from a continuing
letter, plus infinite branches prefixwise. Those cases are discussed through
`CanTreeModel`, but are not instances of the datatype named `CatalogueWord`.
The τ-word results are therefore correct only for the confirming-ending
subtype." All in-corpus consumers (`tauWord_spec`, the n = 1 word packaging)
are confirming-ending; the V_term-ended and infinite cases enter the wave-C
instantiation through `CanTreeModel.len` / `SpeciesReadout.lenOf`
(`SP8_instantiation.lean`), never through this structure. -/
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

/-! ### SP-FIN code type (blueprint §5 group D header) -/

/-- The SP-FIN encoding's code type: `Fin (n² + 3n + 12) → Fin (n + 2)`, entries in
the note's order (tag 1; D w W 3; e ℓ a s₀′ d 5; slot indicator n+1; λ-matrix n²;
sel 2; flank cut-set indicators 2n). "Every species tuple is determined by an
integer vector with all entries in {0, 1, …, n+1}". Shared by Sp.encodeInj /
Sp.encodeCard / Sp.finThm, hence declared here. -/
def Code (n : ℕ) : Type := Fin (n ^ 2 + 3 * n + 12) → Fin (n + 2)

end LeanUrat.MovesSp
