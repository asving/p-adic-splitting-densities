# MovesR LEAN BLUEPRINT — REV 4 (re-architecture per stuck-rule adjudication #1)

SOURCE (ground truth): `lean/notes/MOVES_2026-07-24.md` §R-LEDGER, rev 5, DUAL-ACCEPTED
2026-07-27; Lemma LST's §C display (MOVES 3728–3781) a consulted source since rev 3.
AUDIT TRAIL: rev 1 → Codex REJECT 15c/6g (all repaired rev 2); rev 2 → Fable REJECT
2c/5g, Codex repairs verified genuine (all repaired rev 3); rev 3 → MAXIMAL SPLIT:
fresh-Fable #2 ACCEPT 0/0 (`MOVESR_AUDIT_FABLE2_2026-07-28.md`, FF1–FF7 verified
leg-by-leg) vs Codex FINAL REJECT 15c/5g (`MOVESR_AUDIT_CODEX_FINAL_2026-07-28.md`).
ORCHESTRATOR ADJUDICATION (campaign ledger, stuck-rule #1): the split is systematic —
Codex reads explicit fences (K1-chain/in_γ internals, §B1 graded machinery) as DROPPED
CONTENT; Fable reads them as faithful declared pointers; unresolvable at the
statements-only level because §R-LEDGER's clauses genuinely POINT INTO §C machinery
with no Lean form. RESOLUTION = THIS REV: the §C machinery gets a minimal abstract
interface (`GradedCarrier` + per-lemma statement defs + `CStatements`), so every
clause field's TYPE is the cited lemma's full statement — no fence; instantiating the
interface from the OM engine is HC-1's declared deliverable. Codex-FINAL findings are
each triaged in §5 (survived → folded in / resolved-by-rearchitecture / note-rejected
after the ordered note-checks). The
campaign-wide lesson driving this revision: **STATEMENTS-ONLY ≠ CONTENT-FREE** — a
faithful obligation statement must be FALSE for instances the note would reject. So
every carrier structure now carries the note's own laws as fields (measure laws,
normalized-cylinder masses, nonemptiness/finiteness, typed clause content), and every
open kernel remains a named Prop that consumers hypothesize — nothing is discharged.
Units are definitions + elaboration checks; proof burden = the base-index layer only
(U2–U6, U12, U41). Unit format per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2.
Files land under `lean/LeanUrat/MovesR/`.

## 0. Design decisions

**(D1) WITT-VECTOR BASE LAYER: CONCRETE MATHLIB ROUTE — no axioms, no interface.**
(Unchanged from rev 1 except the card decision, overruled per finding 1.)
- Mathlib HAS: `WittVector p R`, `WittVector.map` + `map_injective`/`map_coeff`/
  `map_id` (`RingTheory/WittVector/Basic.lean`); `WittVector.teichmuller`
  (`Teichmuller.lean`); `AlgebraicClosure (ZMod p)`; `RingHom.eqLocusField`
  (`Algebra/Field/Subfield/Basic.lean:477`); `iterateFrobenius`
  (`Algebra/CharP/Lemmas.lean:327`); `Subfield.inclusion`; `AdjoinRoot`.
- Mathlib LACKS: a finite-subfields-of-F̄_p lattice, W(F_q)/unramified API, and
  `WittVector.map_comp` (3-line local ext lemma via `map_coeff`).
- DECISION: ambient `W(F̄_p) := WittVector p (AlgebraicClosure (ZMod p))`; `F_m` :=
  the fixed field of the m-th Frobenius iterate (`eqLocusField`, membership
  definitionally `x ^ p ^ m = x`); `O_m := (WittVector.map (F_m).subtype).range`.
  Composition law "(O_δ)_{δ′} = O_{δδ′}": `relExt m δ′ := O (m·δ′)` makes the display
  `rfl`/`mul_assoc` ("bookkeeping inside W(F̄_p), never an identification up to
  isomorphism"); the substantive content is `O_le : d ∣ m → O_d ≤ O_m` (provable)
  and `qq_mul : q_{mδ′} = q_m^{δ′}` (`pow_mul`). FALLBACK if the `ExpChar` instance
  fights: `(frobenius _ p) ^ (m : ℕ)` in the RingHom monoid, or the raw carrier
  `{x | x ^ p ^ m = x}` with closure proved once.
- **FINDING-1 REPAIR (rev-1 "deliberate non-unit" overruled):** the display "F_m is
  THE subfield of order p^m" includes the CARD FACT. New provable unit **R6**:
  `Fsub_card : Nat.card ↥(Fsub p m) = p ^ (m : ℕ)` (roots of the separable
  `X^{p^m} − X` in an algebraically closed field; `galois_poly_separable` +
  root-counting; difficulty hard). Stated NOW, proved by the wave-3 fleet.

**(D2) CARRIERS WITH LAWS; PARAMETERIZED REALIZED FAMILIES.** The ambient δ-based
MOVES theory does not exist in Lean (REL.1 is the kernel saying it does). Obligations
are typed over carrier structures whose fields are the note's objects AND the note's
laws about them (finding 2's lesson): `Setting` carries the realized-measure laws
(mass bounds, additivity on its event class, conditional normalization at positive
cells); `BoxVol` is a genuine normalized content function pinned on digit cylinders;
every carrier the note treats as nonempty/finite is typed nonempty/finite.
Quantification over realized instances is via `SettingsFamily` — a structure with
nonemptiness, a root (δ = 1) member, and TYPED descendant closure (findings 19/20).
Degenerate instances that survive (e.g. `cellMass = 0` cells) are exactly those the
note's own provisos exclude, and every display carries the proviso as its guard.

**(D3) MASS CODOMAIN ℚ.** All masses/entries (vol, condMass, β) are `ℚ`: the note's
masses are exact rationals ("sealed rational mass, displayed fractions"); β entries
are ℚ(q) evaluated at q = p^{δ_j} ∈ ℕ. No `ℝ≥0∞`.

**(D4) REL.1 = THE CInterface (REV-4 RE-ARCHITECTURE; supersedes the rev-2/3 clause
ledger and its fences).** Three layers:
(a) **`GradedCarrier p δ`** — the D.3(e)/§C graded vocabulary as ABSTRACT TYPES WITH
LAWS, ≤ ~10 fields, NO construction: coefficients, graded pieces Gr γ, the K1-chain-
weight function w, the initial-form/class map in_γ, ultrametric additivity of w,
additivity of in_γ at its weight, kills-weight-above, weight-detection. Instantiating
it from the OM engine is **HC-1's declared deliverable** (campaign plan §1).
(b) **Per-lemma statement defs + `CStatements`** — one named def per §C lemma the
ledger cites (`SecAStmt, SecB1Stmt, SecB2Stmt, ThmCaStmt, ThmCbStmt, C05Stmt, C1Stmt,
C15Stmt, LSTStmt, TYPStmt, DOMStmt`), each def's body = the lemma's FULL statement
over the carrier bundle at the base params — LST's def carries ALL of (i) including
the K1-chain-weight typing (`G.w (mono i) = ht i`) and the initial-form/level-set
functionality, plus (ii) and (iii), typed once, NO FENCE. `CStatements p Sp AD δ n K`
is the record with one field per lemma, each field's type the named def.
(c) **REL.1's ledger := `CStatements` at base δ** — a TYPED POINTER, the note's own
"MUTATIS MUTANDIS" (`def REL1 … := CStatements …`, with `ThmCbStmt` = the (REL.1-b)
display over the DEFINED count — FF2's pin retained). EQ-1/EQ-2 are ATTACHED to
REL.1 per the note (CF17): `REL1PassDeliverable := REL1 ∧ EQ1` (EQ-1 is "a named
checkpoint of REL.1's re-scoping pass") and `EQ2lawIfREL1 := REL1 → EQ2law` (the
note's "OPEN, REL.1-conditional" status, typed).
Retained from rev 3 (Fable-verified, re-keyed onto the interface): the count
definition (FF2), the (Sp, AD) wiring `posOfDigit`/`aDim_eq` (FF4), pin-statistics
invariance — now over a proper STATUS carrier (CF9) — the memberships (FF5), the
`_linked` pattern (FF6), and the unitriangularity anchors (FF7).

**(D5) THE (e) KEYING (findings 13/14 + CF13/CF14 repair).** `entryFirst : ℕ` is
FIXED per branch (the note: e_j defined "from b_j's data"). REV 4 (CF14): `consumed`
is NO LONGER an inhabitant-chosen field — it is a PARAMETER of the (e)-Props, supplied
by [3]/MovesS's export exactly like `tableConv` (the prescriptions [3]'s tables
actually consume at this key; choosing it here was the vacuity Codex flagged). (e5)'s
first disjunct `determines` says the consumed class is a singleton; (e3) `massEqEntry`
is stated GIVEN `determines` and prices every consumed prescription at THE REL.1 mass
(`_linked`, FF6). The re-keying escape stays a STATEMENT-FENCE EVENT. (e4)'s
obligation is `e4agrees (tableConv)` — [3]'s exported convention — ONLY; REV 4
(CF13): `firstIdxCandidate` is DEMOTED to a named CANDIDATE definition that NO
consumer may hypothesize (the note: "candidate … owed, not assumed"; it is removed
from the D7 hypothesis list and marked non-obligation in its docstring). (e1)'s
(a6)-compatibility stays typed (`stateDict_compat`).

**(D6) NON-UNITS (deliberate, with reasons).**
- **REL.3 (finding 21 repair — the rev-1 pseudo-statement is DELETED).** The note:
  "the [4]-side displays (SQ.0–SQ.2 …) DO NOT EXIST YET — … so no theorem statement
  is possible here". Rev 1's `SQConsumptionSite`/`REL3` invented a satisfiable shape
  (`REL3 []` was true) — exactly the "placeholder wearing a specification's clothes"
  the note itself retired at its rev 1. REV-2 DISPOSITION: NO Lean object for REL.3.
  It is a recorded non-unit: when [4] drafts SQ.0–SQ.2, REL.3's revision restates
  each consumed display verbatim re-scoped to O_δ (ABSOLUTE indices), enters THIS
  corpus as new audited units, and is passed like REL.1. What IS fixed from the plan
  ("the induction hypothesis is an input theorem about vol_{O_δ}, never the formal
  substitution q ↦ q^δ") is a discipline on those FUTURE units, recorded here and in
  the Defs file as a fenced comment block, not a Prop. Honest absence over fake shape.
- REL.2(c): re-homed to [3t]'s (SIB) (plan REV 9); the note "CITES (SIB) and never
  re-states it" — no sibling-independence Prop here; MovesT owns it.
- Gate REL-n4 + spec sheet (g1)–(g7): census-side numeric artifact (PARI/W(F₄)),
  runnable spec still OWED in the note; not a Lean object; nothing here consumes it.
- (R0-tower)'s PREDICTED bracket (value groups/stretches/κ_r) and (R0-reads)'
  reconstruction prose: fenced as REL.1-pass content — doc-comments only (typing
  them now would invent the API the pass must walk; asserting them would break the
  note's PREDICTED fences).

**(D7) HYPOTHESIS vs DELIVERABLE (explicit; per unit below).**
- HYPOTHESES (open kernels; named Props consumers hypothesize — never proved or
  axiomatized here): `REL1` (= `CStatements` at base δ; + `REL1PassDeliverable`,
  `EQ2lawIfREL1`), `REL2b`, `REL2e.massEqEntry` (e3), `REL2e.determines` (e5),
  `REL2e.e4agrees` (e4), `EQ1`, `EQ2law`, `EQ3`, `SIBOdelta`.
  (`firstIdxCandidate` REMOVED from this list at REV 4 — CF13: a candidate, not an
  obligation; no consumer may hypothesize it.)
- DELIVERABLES (data a future pass must EXHIBIT; the structure's INHABITANT is the
  deliverable): `REL2a` ((a1)–(a6) with `teich_pin` a FIELD), `REL2d` (square +
  typed node-data correspondence), `REL2e`'s data ((e1) dictionary + compat, β
  table, `entryFirst`, `consumed`), `BoxVol`, `ReBased`/`TowerData`,
  `SettingsFamily`. **Accuracy correction (FF7 — the rev-2 "law fields make junk
  inhabitants impossible" claim was FALSE and is withdrawn):** what the law fields
  actually enforce is that every inhabitant SATISFIES the note's typed laws
  (measure laws, cylinder pins, unitriangularity anchors, letter/word/verdict
  preservation, the Teichmüller pin); free-data inhabitants respecting those laws
  remain possible wherever the ambient engine's objects (transports, trees, reads)
  do not exist in Lean — RECORDED as widening (v) in §3. Full pinning of those
  objects is REL.1-pass territory, not this corpus's.
- PROVABLE NOW (the only proof burden): U2–U6, U12, U41.

**(D8) REUSE OF EXISTING CORPORA (new; supports D4).** `DigitSystem n α`
(`Moves/DefsT.lean:187`) is digit-polymorphic — instantiated at `α := ↥(Fsub p δ)`
(the F_δ-digit ATOM of (R0-box)). `IsUnitriangular` (`MovesC/Defs.lean:241`,
polymorphic `[Add R]`), `CoordPrec` (`MovesC/Defs.lean:221`, C.0's order on ℕ × ℕ
— the (a5) unitriangularity anchor, FF7), `Line` + `DomData` (`MovesC/Defs.lean:255/278`, base-free
ℚ-data — the note's "valuation geometry … carries over as written" is the warrant)
are imported, NOT re-declared. Exact namespaces/qualifications resolved at E-phase;
any semantic mismatch discovered there re-enters the audit loop.

**(D9) ELABORATION-CHECK POLICY (revised).** Carrier structures with honest trivial
instances (`Setting`, `SettingsFamily`, `SpeciesSyntax`, `AlphabetData`) get
instance `example`s (well-formedness only, never evidence — the surviving trivial
instances are exactly proviso-excluded or vacuous-by-the-note's-own-fences cases).
Structures whose inhabitation IS the obligation or HC-1's deliverable (`REL2a1`–
`REL2a6` + bundle, `REL2d`, `REL2e`, `BoxVol`, `GradedCarrier`, `ReBased`,
`TowerData`, `SIBPkg`) get `#check` type-correctness elaborations ONLY —
their inhabitation story is the future pass, and that is the point (audit charge:
"an inhabitation story OR an explicit instance unit"; the story is recorded per
structure in its docstring).

## 1. Defs skeleton (normative for content; E-phase fixes syntax only, statement fence applies)

```lean
import Mathlib
import LeanUrat.Moves.DefsT      -- DigitSystem (polymorphic)
import LeanUrat.MovesC.Defs      -- IsUnitriangular, CoordPrec, Line, DomData (base-free)
namespace MovesR
variable (p : ℕ) [hp : Fact p.Prime]

/-! ## R0. Base-index convention (file Base.lean; units R1–R6) -/

/-- `F̄_p`, fixed ONCE. -/
abbrev Kbar := AlgebraicClosure (ZMod p)
/-- `W(F̄_p)` — every base below is a LITERAL subring of this one ring. -/
abbrev Wbar := WittVector p (Kbar p)

/-- `F_m` — THE subfield of `F̄_p` of order `p^m` (fixed field of the m-th Frobenius
iterate; membership definitionally `x ^ p ^ m = x`; the order fact is unit R6). -/
def Fsub (m : ℕ+) : Subfield (Kbar p) :=
  RingHom.eqLocusField (iterateFrobenius (Kbar p) p (m : ℕ)) (RingHom.id _)

/-- `O_m := W(F_m) ⊂ W(F̄_p)`: "nested base changes then compose LITERALLY as
subrings … no per-pair embedding choices". -/
def O (m : ℕ+) : Subring (Wbar p) :=
  (WittVector.map (Subfield.subtype (Fsub p m))).range

/-- `q_m := p^m = |F_m|` (the note's `q_δ := p^δ`; = |F_m| by R6). -/
def qq (m : ℕ+) : ℕ := p ^ (m : ℕ)

/-- degree-δ′ unramified base change of `O_m` inside `W(F̄_p)` — BY THE CONVENTION
this IS `O_{m·δ′}` (ABSOLUTE indices; "never an identification up to isomorphism"). -/
def relExt (m δ' : ℕ+) : Subring (Wbar p) := O p (m * δ')

theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m := sorry            -- R2
theorem O_le {d m : ℕ+} (h : d ∣ m) : O p d ≤ O p m := sorry                     -- R3
theorem relExt_eq (m δ' : ℕ+) : relExt p m δ' = O p (m * δ') := rfl              -- R4
theorem relExt_relExt (m δ' δ'' : ℕ+) :
    relExt p (m * δ') δ'' = relExt p m (δ' * δ'') := by rw [relExt, mul_assoc]   -- R4
theorem O_le_relExt (m δ' : ℕ+) : O p m ≤ relExt p m δ' := O_le p ⟨δ', rfl⟩      -- R4
theorem qq_mul (m δ' : ℕ+) : qq p (m * δ') = qq p m ^ (δ' : ℕ) := sorry          -- R5
theorem Fsub_card (m : ℕ+) : Nat.card ↥(Fsub p m) = p ^ (m : ℕ) := sorry         -- R6

/-- The level-N digit cylinder at `g` in the degree-n coefficient box over `O_m`:
agreement of the first N Witt coordinates (F_m perfect ⇒ p^N W(F_m) = V^N W(F_m),
so this IS "f mod p^N" — (R0-box)'s level-N counting). -/
def cyl (m : ℕ+) {n : ℕ} (N : ℕ) (g : Fin n → ↥(O p m)) : Set (Fin n → ↥(O p m)) :=
  {h | ∀ (j : Fin n) (i : ℕ), i < N → ((h j : Wbar p)).coeff i = ((g j : Wbar p)).coeff i}

/-! ## The R.1 SETTING (file Interface.lean; units R7–R8) -/

/-- One realized instance of the note's SETTING ("Ambient base O_δ …, a realized
prefix η, state cylinder Σ (frame Ψ_η), digit cell c of Σ, and a branch b_j …").
η/Σ/c/b_j are absorbed into carriers; the REALIZED-MEASURE LAWS are fields
(finding 2): masses in [0,1], a conditional content on an event algebra,
normalized exactly at the positive-mass cells the note conditions on. -/
structure Setting where
  δ : ℕ+                                  -- ambient ABSOLUTE index (root: δ = 1)
  δrel : ℕ+                               -- δ_j^rel (residual degrees g over F_δ down b_j)
  d : ℕ+                                  -- d_j, the O_δ-degree of b_j's cluster
  Cont : Type                             -- continuation points of Σ_c
  contNe : Nonempty Cont
  AmbEvents : Set (Set Cont)              -- the ambient event algebra on Σ_c
  univ_mem : Set.univ ∈ AmbEvents
  compl_mem : ∀ E ∈ AmbEvents, Eᶜ ∈ AmbEvents
  union_mem : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents, E ∪ E' ∈ AmbEvents
  cellMass : ℚ                            -- μ(Σ_c)
  cellMass_nonneg : 0 ≤ cellMass
  cellMass_le_one : cellMass ≤ 1
  condMass : Set Cont → ℚ                 -- μ( · │ Σ_c )
  condMass_nonneg : ∀ E, 0 ≤ condMass E
  condMass_empty : condMass ∅ = 0
  condMass_univ : 0 < cellMass → condMass Set.univ = 1
  condMass_add : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents,
    Disjoint E E' → condMass (E ∪ E') = condMass E + condMass E'
  PTree : Type                            -- prescribed finite subtrees T_j for b_j
  prescNe : Nonempty PTree
  SEvent : PTree → Set Cont               -- S_j(T); (W1)'s reading kept opaque
  SEvent_mem : ∀ T, SEvent T ∈ AmbEvents
  StateIdx : Type                         -- [3]/[3t]'s state indices
  τ : StateIdx                            -- τ_j(c)
  /-- (CF10) the AMBIENT C.0.5 frame family at the cell ("state cylinder Σ (frame
  Ψ_η)"): frames and their transports on continuation points are SUPPLIED BY THE
  AMBIENT THEORY — (a5)'s commutation quantifies over THIS family, so no inhabitant
  can substitute a private identity-only family. -/
  FrameC : Type
  frameCNe : Nonempty FrameC
  reframe : FrameC → FrameC → Cont → Cont

/-- `δ_j := δ·δ_j^rel` — ABSOLUTE accumulated residue degree; target base O_{δ_j}. -/
def Setting.δabs (S : Setting) : ℕ+ := S.δ * S.δrel
/-- (a2)'s target degree `d_j^rel := d_j/δ_j^rel` (ℕ-division; integrality is
(a2)'s obligation `REL2a2`). -/
def Setting.dRel (S : Setting) : ℕ := (S.d : ℕ) / (S.δrel : ℕ)
/-- (e2)'s DEGREE CONVENTION pinned: "the β-argument is p^{δ_j} with δ_j ABSOLUTE". -/
def Setting.βarg (S : Setting) : ℕ := qq p S.δabs

/-- The REALIZED family the (SIB-Oδ) quantifier ranges over (findings 19/20):
nonempty, contains the root (δ = 1) reading, and is CLOSED UNDER DESCENT with the
absolute re-indexing — "the same typing applies at every descendant branching cell
inside T_j, ABSOLUTE indices throughout". Supplied by the ambient theory. -/
structure SettingsFamily where
  mem : Set (Setting p)
  ne : mem.Nonempty
  root_mem : ∃ S ∈ mem, S.δ = 1
  /-- (CF1; NOTE-CHECK RESULT recorded) the note displays NO positive-cell
  existence law; its only positivity text is (b)'s proviso "μ(Σ_c) > 0, the only
  cells any (SIB) display conditions on". `mem_pos` types exactly that FAMILY
  SCOPE: the family IS the family of (SIB)-conditioning sites, so its members are
  the positive-mass cells — the advertised all-zero-mass singleton is dead
  (ne + mem_pos), with no existence claim beyond the already-parameterized `ne`. -/
  mem_pos : ∀ S ∈ mem, 0 < S.cellMass
  desc : (S : Setting p) → S ∈ mem → S.PTree → Set (Setting p)
  desc_sub : ∀ S hS T, desc S hS T ⊆ mem
  desc_amb : ∀ S hS T, ∀ S' ∈ desc S hS T, S'.δ = S.δabs
```

```lean
/-! ## The equivariance trio (file Eq.lean; units R18–R21) — carriers before REL.2,
which consumes them (findings 11/12/15/16/17) -/

/-- (EQ-1) carrier: species letters are FINITE SYNTAX — "defined by stage tuples
(e, h, g, μ), side/lattice data, and polygon conventions … never by the residue
field's SIZE". `shape` exposes the stage tuple (the grammar anchor); `menu δ` is a
FINSET (finiteness typed — finding 15) and nonempty (species exist at every base). -/
structure SpeciesSyntax where
  Letter : Type
  shape : Letter → ℕ × ℕ × ℕ × ℕ          -- the stage tuple (e, h, g, μ)
  /-- (CF4) the rest of the note's grammar: "species letters are DEFINED BY stage
  tuples (e, h, g, μ), side/lattice data, and polygon conventions" — side/lattice
  and polygon-convention data as declared carriers, with `letter_det` typing
  "defined by": the full datum determines the letter. -/
  SideData : Type
  side : Letter → SideData
  PolyConv : Type
  poly : Letter → PolyConv
  letter_det : Function.Injective (fun l => (shape l, side l, poly l))
  menu : ℕ+ → Finset Letter               -- the realized menu over O_δ
  -- (CF3, NOTE-CHECK RESULT: rev-3's `menuNe` was a STRENGTHENING — the note
  -- asserts menu INVARIANCE only, and R.5 says "no menu/exhaustion claims".
  -- REMOVED; empty menus are back in the statement's range.)

/-- **(EQ-1)** [PREDICTED — "nothing derived here"; walked in REL.1's pass]:
"the species alphabet and menu are the SAME finite syntax over every O_δ …
What changes … is the REALIZATION multiplicity …, never the letter set." -/
def EQ1 (Sp : SpeciesSyntax) : Prop := ∀ δ : ℕ+, Sp.menu δ = Sp.menu 1

/-- (EQ-2) carrier (findings 16/17 repair): the alphabet 𝔸_δ at a position class is
typed as an actual ADDITIVE SPAN — a carrier group per (δ, position) with the
attainable image as an additively-closed subset — "the attainable additive
image/span of the RE-BASED slot maps"; `card_eq` is the note's UNCONDITIONAL
definition part |𝔸_δ| = p^{a_δ}. `posLetter` is the species letter realized at the
position over O_δ — the (a6)/(EQ-1) matching dictionary AS DATA — and `Stable` is
DEFINED from it (species persistence), not a free field. -/
structure AlphabetData (Sp : SpeciesSyntax) where
  Pos : Type                              -- shape position classes
  posNe : Nonempty Pos
  Carrier : ℕ+ → Pos → Type               -- the re-based receiving group
  [carrierGrp : ∀ δ x, AddCommGroup (Carrier δ x)]
  [carrierMod : ∀ δ x, Module ↥(Fsub p δ) (Carrier δ x)]   -- F_δ-structure (CF6)
  /-- (CF5) the RE-BASED SLOT MAPS themselves, as declared data ("D.3(e)(i)/C.3
  run over O_δ"): abstract domains with F_δ-structure and the piece maps. -/
  SlotDom : ℕ+ → Pos → Type
  [slotDomGrp : ∀ δ x, AddCommGroup (SlotDom δ x)]
  [slotDomMod : ∀ δ x, Module ↥(Fsub p δ) (SlotDom δ x)]
  slotMap : ∀ δ x, SlotDom δ x → Carrier δ x
  alpha : ∀ δ x, Set (Carrier δ x)        -- 𝔸_δ
  /-- (CF5) ATTAINABILITY, typed as span-generation equality: 𝔸_δ IS "the
  attainable additive image/span of the RE-BASED slot maps" — not an arbitrary
  additively-closed subset of the right size. -/
  alpha_attain : ∀ δ x,
    alpha δ x = ↑(AddSubgroup.closure (Set.range (slotMap δ x)))
  aDim : ℕ+ → Pos → ℕ                     -- a_δ: F_p-additive-span dimension
  card_eq : ∀ δ x, Nat.card (alpha δ x) = p ^ aDim δ x
  posLetter : ℕ+ → Pos → Sp.Letter        -- the realized species letter (owed dictionary, typed)

/-- δ-STABLE-SPECIES position (rev-4 comparison-domain pin), DEFINED: the species
letter persists under re-basing. Split positions fail this and are OUT-OF-DOMAIN
(the F₉ instance recombines across new branches — "REL.2/(SIB) territory"). -/
def AlphabetData.Stable {Sp} (AD : AlphabetData p Sp) (δ : ℕ+) (x : AD.Pos) : Prop :=
  AD.posLetter δ x = AD.posLetter 1 x

/-- **(EQ-2) the law ON THE PINNED PER-POSITION-CLASS DOMAIN** [OPEN,
REL.1-conditional; attachment typed as `EQ2lawIfREL1`]: "at a fixed shape position
WHOSE SPECIES IS δ-STABLE …, the re-based piece maps are F_δ-linear AND a_δ = δ·a"
— BOTH conjuncts typed (CF6: the linearity half is now stateable, the slot maps
being declared data with F_δ-module structure). -/
def EQ2law {Sp} (AD : AlphabetData p Sp) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x →
    IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x) ∧
    AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x

/-- (EQ-2)'s displayed consequence "|𝔸_δ| = q_δ^a = |𝔸|^δ" on the pinned domain —
PROVABLE (R20) from `card_eq` + hypothesized `EQ2law` by `pow_mul`. -/
theorem EQ2law_card {Sp} (AD : AlphabetData p Sp) (h : EQ2law p AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x →
      Nat.card (AD.alpha δ x) = qq p δ ^ AD.aDim 1 x ∧
      Nat.card (AD.alpha δ x) = Nat.card (AD.alpha 1 x) ^ (δ : ℕ) := sorry
      -- (proof consumes h's DIMENSION conjunct only; pow arithmetic as before)

-- (EQ-3) is declared after REL2b (it aliases it verbatim); see Rel2 block.
```

```lean
/-! ## REL.1 (file Rel1.lean; units R9–R13) -/

/-- The vol_{O_m} box-measure interface (finding 8 repair): a genuine normalized
finitely-additive content on an event algebra CONTAINING every digit cylinder, with
the cylinder masses PINNED to (R0-box)'s normalization ("coefficient box O_δ^n with
normalized Haar measure … = 1; f mod p^N ranges over q_δ^{nN} residue points").
`vol_cyl` rules out dummy measures. Inhabitation story: the Haar construction of
the REL.1 pass; no instance is built in MovesR. -/
structure BoxVol (m : ℕ+) (n : ℕ) where
  events : Set (Set (Fin n → ↥(O p m)))
  univ_mem : Set.univ ∈ events
  compl_mem : ∀ W ∈ events, Wᶜ ∈ events
  union_mem : ∀ W ∈ events, ∀ W' ∈ events, W ∪ W' ∈ events
  cyl_mem : ∀ (N : ℕ) (g : Fin n → ↥(O p m)), cyl p m N g ∈ events
  vol : Set (Fin n → ↥(O p m)) → ℚ
  vol_nonneg : ∀ W, 0 ≤ vol W
  vol_empty : vol ∅ = 0
  vol_univ : vol Set.univ = 1
  vol_add : ∀ W ∈ events, ∀ W' ∈ events,
    Disjoint W W' → vol (W ∪ W') = vol W + vol W'
  vol_cyl : ∀ (N : ℕ) (g : Fin n → ↥(O p m)),
    vol (cyl p m N g) = ((qq p m : ℚ) ^ (n * N))⁻¹
  /-- (CF15) LEVEL DETERMINATION: every event is, at some level, a finite union of
  level-N cylinders — so `vol` on the WHOLE event class is FORCED by additivity +
  `vol_cyl`: it IS the normalized Haar mass, not merely Haar-on-cylinders with
  freedom elsewhere. This is the finitely-additive reading of "(digit cylinders
  generate)", and it is the note's own discipline: (g7)'s "CERTIFIED determination
  radius — every level-N box's … verdict constant on the box" is exactly the
  requirement that priced events be level-determined. -/
  events_level : ∀ W ∈ events, ∃ (N : ℕ) (G : Finset (Fin n → ↥(O p m))),
    W = ⋃ g ∈ G, cyl p m N g

/-- **THE CInterface, layer (a) — `GradedCarrier`** (REV 4, D4): the D.3(e)/§C
graded vocabulary as abstract types with laws; NO construction — instantiation
from the OM engine is HC-1's declared deliverable. Fields: coefficients, graded
pieces, the K1-chain-weight function, the initial-form/class map, and its laws
(ultrametric weight, additivity at weight, kills-weight-above, weight detection). -/
structure GradedCarrier (δ : ℕ+) where
  Coeff : Type                             -- slot coefficients B
  [coeffAdd : AddCommGroup Coeff]
  Gr : ℚ → Type                            -- D.3(e)(i)'s graded pieces
  [grAdd : ∀ γ, AddCommGroup (Gr γ)]
  w : Coeff → WithTop ℚ                    -- the K1-chain-weight function
  inγ : (γ : ℚ) → Coeff → Gr γ             -- the initial-form / class map
  w_add : ∀ B B', min (w B) (w B') ≤ w (B + B')
  inγ_add : ∀ (γ : ℚ) (B B'), (γ : WithTop ℚ) ≤ w B → (γ : WithTop ℚ) ≤ w B' →
    inγ γ (B + B') = inγ γ B + inγ γ B'    -- additivity at weight γ
  inγ_kills : ∀ (γ : ℚ) B, (γ : WithTop ℚ) < w B → inγ γ B = 0  -- kills weight above
  inγ_detects : ∀ (γ : ℚ) B, w B = (γ : WithTop ℚ) → inγ γ B ≠ 0  -- weight detection

/-- (R0-tower) carrier: the re-based classifier tower of one history — "built
afresh, NOT by scalar-extending the ℤ_p tower". Base shape F₁ = F_δ[x]/(φ̄), climb
F_{k+1} = F_k[z]/(ψ_k), residual factors OVER THE NEW BASE (the polynomials live
over the actual tower carriers). Laws split §A / §B1 / §B2-DEF for the ledger. -/
structure TowerData (δ : ℕ+) where
  len : ℕ
  Res : Fin (len + 1) → Type              -- F₁, …, F_{len+1}
  [resField : ∀ k, Field (Res k)]
  baseEmbed : ↥(Fsub p δ) →+* Res 0
  stepEmbed : ∀ k : Fin len, Res k.castSucc →+* Res k.succ
  φbar : Polynomial ↥(Fsub p δ)           -- §A's φ̄, over F_δ
  ψ : ∀ k : Fin len, Polynomial (Res k.castSucc)  -- residual factors ψ_k over F_k

/-- §A re-based, the typed base-shape laws: φ̄ monic irreducible OVER F_δ and
F₁ ≃ F_δ[x]/(φ̄) compatibly with the base embedding. -/
structure TowerData.BaseLaws {δ} (T : TowerData p δ) : Prop where
  monic : T.φbar.Monic
  irr : Irreducible T.φbar
  pres : ∃ e : T.Res 0 ≃+* AdjoinRoot T.φbar,
    ∀ x : ↥(Fsub p δ), e (T.baseEmbed x) = algebraMap _ _ x

/-- §B2-DEF (D.0) re-based, the typed climb laws: each ψ_k monic irreducible over
the ACTUAL stage field, each step the quotient presentation F_{k+1} = F_k[z]/(ψ_k). -/
structure TowerData.ClimbLaws {δ} (T : TowerData p δ) : Prop where
  monic : ∀ k, (T.ψ k).Monic
  irr : ∀ k, Irreducible (T.ψ k)
  pres : ∀ k, ∃ e : T.Res k.succ ≃+* AdjoinRoot (T.ψ k),
    ∀ x, e (T.stepEmbed k x) = AdjoinRoot.of _ x

/-- §B1 re-based, the typable residue ("the same construction run over the new
base"): finite stage carriers of characteristic p. The graded internals
(gr_w(A), L, T) are (R0-tower)-fenced to REL.1's pass — recorded, not typed. -/
structure TowerData.StageCarrierLaws {δ} (T : TowerData p δ) : Prop where
  fin : ∀ k, Finite (T.Res k)
  charP : ∀ k, CharP (T.Res k) p

/-- Counting interface for (REL.1-b) (fixed box degree n; nonempty carriers; vols
THROUGH the pinned BoxVol; loci indexed by their history). NOTE (FF2): the display's
LHS `#{f mod p^N ∈ S(H,Z)}` is NOT a field — it is DEFINED (`ReBased.count` below)
from the classifier locus and the cylinder partition, so no instance can supply a
count unrelated to any classifier. -/
structure REL1Counting (δ : ℕ+) (n : ℕ) where
  V : BoxVol p δ n                        -- vol_{O_δ}, cylinder-pinned
  Hist : Type                             -- re-based histories H
  histNe : Nonempty Hist
  Locus : Hist → Type                     -- digit loci Z in H's frame
  locusNe : ∀ H, Nonempty (Locus H)
  kIdx : Hist → ℕ                         -- k, top node index
  Nmin : (H : Hist) → Locus H → ℕ         -- N(H, Z)
  freshEvent : (H : Hist) → ℕ → Set (Fin n → ↥(O p δ))    -- E_fresh(ν_i)
  freshEvent_mem : ∀ H i, freshEvent H i ∈ V.events
  locusEvent : (H : Hist) → Locus H → Set (Fin n → ↥(O p δ))  -- Z as a box event
  locusEvent_mem : ∀ H Z, locusEvent H Z ∈ V.events
```

```lean
/-- The re-based theory carriers ((R0-box/tower/reads/ledger) as typed objects):
digit spaces are F_δ-valued (the O_δ-digit ATOM), jets expand box points into
digit coordinates (C.0's block expansion over F_δ), towers per history, frames
with transports, per-position alphabet dimensions a_δ — WIRED to (EQ-2)'s
`AlphabetData` via `posOfDigit`/`aDim_eq` (FF4) — pin sets, (ZC) statistic, the
base-free floor lines for DOM, and the height/block/floor carriers Lemma LST's
legs consume (FF1). -/
structure ReBased (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) (δ : ℕ+) (n : ℕ) where
  C : REL1Counting p δ n
  mOf : C.Hist → ℕ                        -- digit count of H's jet frame
  mOf_pos : ∀ H, 0 < mOf H
  jet : (H : C.Hist) → (Fin n → ↥(O p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  tower : C.Hist → TowerData p δ          -- (R0-tower), per history
  Frame : C.Hist → Type                   -- C.0.5's frames
  frameNe : ∀ H, Nonempty (Frame H)
  T : (H : C.Hist) → Frame H → Frame H →  -- the frame transports
      (Fin (mOf H) → ↥(Fsub p δ)) → (Fin (mOf H) → ↥(Fsub p δ))
  SHZ : (H : C.Hist) → C.Locus H → Set (Fin n → ↥(O p δ))   -- the classifier locus S(H,Z)
  SHZ_mem : ∀ H Z, SHZ H Z ∈ C.V.events
  digitLocus : (H : C.Hist) → C.Locus H → DigitSystem (mOf H) ↥(Fsub p δ)  -- Z as digit system
  aDim : (H : C.Hist) → Fin (mOf H) → ℕ   -- a_δ at each digit position ((EQ-2) def part)
  /-- (FF4) the (R0-ledger)↔(EQ-2) wiring: each digit position sits at an
  `AlphabetData` position class, and its per-digit exponent IS that class's a_δ —
  "|𝔸_δ| = p^{a_δ} per (EQ-2)'s re-based-span definition". EQ2law now speaks about
  the exponents c1 consumes; REL-n4's exponent leg tests exactly these. -/
  posOfDigit : (H : C.Hist) → Fin (mOf H) → AD.Pos
  aDim_eq : ∀ H i, aDim H i = AD.aDim δ (posOfDigit H i)
  /-- (CF9) PIN STATUS as a proper carrier: each coordinate's pin-status datum
  (C.0/C.0.5's "cardinality-and-STATUS statistics"), with the pinned set DEFINED
  from it — alphabet dimensions are ledger weights, not statuses. -/
  Status : Type
  pinStatus : (H : C.Hist) → Frame H → C.Locus H → Fin (mOf H) → Status
  constrained : Status → Prop
  pinnedIn : (H : C.Hist) → Frame H → C.Locus H → Finset (Fin (mOf H))
  pinnedIn_spec : ∀ H F Z i, i ∈ pinnedIn H F Z ↔ constrained (pinStatus H F Z i)
  zcStat : (H : C.Hist) → Frame H → C.Locus H → ℤ            -- C.1.5's (ZC) statistic
  lines : (H : C.Hist) → ℕ → Line         -- base-free floor lines (MovesC, D8)
  interiorEnd : C.Hist → ℕ
  /-- THE CInterface ATTACHMENT (D4(a)): the graded carrier this instance's §C
  statements quantify over. -/
  G : GradedCarrier p δ
  /-- LST carriers (FF1, upgraded at REV 4): absolute height, block assignment,
  floors, factor-interior blocks, the engine's floor downset — PLUS the objects
  the previously-fenced LST(i) clauses need: each coordinate's BASIS MONOMIAL in
  the carrier and each block's SLOT COEFFICIENT at a digit vector (the engine's
  weight is now `G.w (slotCoeff …)`, not a free field). -/
  ht : (H : C.Hist) → Fin (mOf H) → ℚ
  blkOf : (H : C.Hist) → Fin (mOf H) → ℕ
  floorC : (H : C.Hist) → Fin (mOf H) → ℚ
  floorB : (H : C.Hist) → ℕ → ℚ
  interiorB : (H : C.Hist) → ℕ → Prop
  floorSet : (H : C.Hist) → ℕ → Set (Fin (mOf H))
  mono : (H : C.Hist) → Fin (mOf H) → G.Coeff
  slotCoeff : (H : C.Hist) → ℕ → (Fin (mOf H) → ↥(Fsub p δ)) → G.Coeff
  /-- (CF8) the note's own interior anchor: "on the factor interior — where ALL
  FRESH CONTENT lives (C.1's rim bullet)" — constrained digits sit on
  factor-interior blocks, so `interiorB ≡ False` forces the degenerate all-free
  perimeter instead of silently discharging the LST legs. -/
  interior_fresh : ∀ H (F : Frame H) Z, ∀ i ∈ pinnedIn H F Z, interiorB H (blkOf H i)

/-- `#{ f mod p^N ∈ S(H, Z) }` — the (REL.1-b) LHS, DEFINED from in-corpus
vocabulary (FF2 repair: kills the free-count instances): the number of level-N
cylinder classes meeting the classifier locus. For N ≥ N(H,Z) these are exactly
the level-N residue points of S(H,Z). -/
noncomputable def ReBased.count {Sp AD δ n} (K : ReBased p Sp AD δ n)
    (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ) : ℕ :=
  Nat.card {W : Set (Fin n → ↥(O p δ)) // ∃ f ∈ K.SHZ H Z, W = cyl p δ N f}

/-! **THE CInterface, layer (b): per-lemma statement defs** (D4; CF18's
decomposition — ONE display per def, each its own unit). Each def's body is the
cited lemma's FULL statement over the carrier bundle; the fences are gone. -/

/-- §A re-based: the base tower shape over F_δ (φ̄ monic irr, F₁ = F_δ[x]/(φ̄)). -/
def SecAStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, (K.tower H).BaseLaws
/-- §B1 re-based (CF16): the graded vocabulary is now TYPED — `K.G` carries the
pieces/class map/weight WITH their laws (its structure fields), so §B1's citation
is a typed pointer, not a fence; the statement asserts the stage-carrier laws AND
the block expansion's additivity into the carrier (slot coefficients additive in
the digit vector — the D.3(e) attachment). Localization L / degree-1 unit T ride
as HC-1 instantiation obligations, recorded in D4. -/
def SecB1Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  (∀ H, (K.tower H).StageCarrierLaws) ∧
  (∀ H (B : ℕ) (x y : Fin (K.mOf H) → ↥(Fsub p δ)),
    K.slotCoeff H B (x + y) = K.slotCoeff H B x + K.slotCoeff H B y)
/-- §B2-DEF re-based: the D.0 climb, residual factors OVER THE NEW BASE. -/
def SecB2Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, (K.tower H).ClimbLaws
/-- Theorem C(a): classifier locus = jet-preimage of the digit-system locus. -/
def ThmCaStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H Z, K.SHZ H Z = (fun f => K.jet H f) ⁻¹' {x | (K.digitLocus H Z).IsSolution x}
/-- Theorem C(b) = (REL.1-b), LHS the DEFINED count (FF2): "#{ f mod p^N ∈ S(H,Z) }
= q_δ^{nN} · ∏_{i=0}^{k} vol(E_fresh(ν_i)) · vol(Z) for every N ≥ N(H, Z)". -/
def ThmCbStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ), K.C.Nmin H Z ≤ N →
    (K.count H Z N : ℚ) = (qq p δ : ℚ) ^ (n * N) *
      ((∏ i ∈ Finset.range (K.C.kIdx H + 1), K.C.V.vol (K.C.freshEvent H i)) *
        K.C.V.vol (K.C.locusEvent H Z))
/-- C.0.5 + PIN-WELLDEF: transports unitriangular; pin statistics frame-invariant —
cardinality AND STATUS (CF9: over the `Status` carrier, pinned sets DEFINED from
it) AND the aDim ledger-weights c1 consumes. -/
def C05Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H (F F' : K.Frame H), IsUnitriangular (K.T H F F') ∧
    ∀ Z, (K.pinnedIn H F Z).card = (K.pinnedIn H F' Z).card ∧
      Multiset.map (K.pinStatus H F Z) Finset.univ.val
        = Multiset.map (K.pinStatus H F' Z) Finset.univ.val ∧
      (K.pinnedIn H F Z).val.map (K.aDim H) = (K.pinnedIn H F' Z).val.map (K.aDim H)
/-- C.1: "each constrained digit contributing the factor |𝔸_δ|⁻¹ of its ATTAINABLE
alphabet" — the locus mass is the per-pinned-digit product. -/
def C1Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H (F : K.Frame H) Z, K.C.V.vol (K.C.locusEvent H Z) =
    ∏ i ∈ K.pinnedIn H F Z, ((p : ℚ) ^ (K.aDim H i))⁻¹
/-- C.1.5's (ZC) invariant: the statistic is transport/frame-invariant. -/
def C15Stmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H F F' Z, K.zcStat H F Z = K.zcStat H F' Z
/-- Lemma LST (level-set scale-typing), FULL statement (§C display MOVES 3728;
CF7 RESOLVED-BY-REARCHITECTURE — the previously-fenced clauses are typed over the
carrier): (i-a) TYPING: "ht(b, l) is the K1-chain weight of the coordinate's basis
monomial" — `G.w (mono i) = ht i`; (i-b) "w(B) = min{ht(b, l) : (b, l) ∈ blk(B),
y ≠ 0} (the iterated slot-minimum)"; (i-c) "the weight-γ initial form in_γ(B) is a
function of exactly the LEVEL SET L_γ(B)"; (ii) FLOOR CONSTANCY ON THE INTERIOR;
(iii) SELECTION via the ht-downset. -/
def LSTStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ (H : K.C.Hist),
    (∀ i, K.G.w (K.mono H i) = ((K.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (B : ℕ) (x : Fin (K.mOf H) → ↥(Fsub p δ)),
      K.G.w (K.slotCoeff H B x) = (Finset.univ.filter fun i =>
        K.blkOf H i = B ∧ x i ≠ 0).inf fun i => ((K.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ (γ : ℚ) (B : ℕ) (x y : Fin (K.mOf H) → ↥(Fsub p δ)),
      (∀ i, K.blkOf H i = B → K.ht H i = γ → x i = y i) →
      K.G.inγ γ (K.slotCoeff H B x) = K.G.inγ γ (K.slotCoeff H B y)) ∧
    (∀ i, K.interiorB H (K.blkOf H i) → K.floorC H i = K.floorB H (K.blkOf H i)) ∧
    (∀ B, K.interiorB H B →
      K.floorSet H B = {i | K.blkOf H i = B ∧ K.ht H i ≤ K.floorB H B} ∧
      ∀ (γ' : ℚ), K.floorB H B < γ' →
        ∀ i, K.blkOf H i = B → K.ht H i = γ' → i ∉ K.floorSet H B)
/-- Lemma TYP: walk item (i)'s retyping (per-digit ADDITIVE on O_δ-digit blocks) +
TYP's graded leg at cardinality granularity: each digit position's ATTAINABLE
image has the alphabet's size p^{a_δ} ("SURJECTIVE onto the digit alphabet (image
= the additive span of the slot images, D.3(e)(i))"), tied to (EQ-2)'s data via
`aDim_eq`. F_δ-linearity stays EXPECTED, walked — not asserted (the note). -/
def TYPStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  (∀ H (i : Fin (K.mOf H)) (f g : Fin n → ↥(O p δ)),
    K.jet H (f + g) i = K.jet H f i + K.jet H g i) ∧
  (∀ H (i : Fin (K.mOf H)),
    Nat.card (Set.range fun f => K.jet H f i) = p ^ K.aDim H i)
/-- Lemma DOM: base-free floor domination, MovesC's `DomData` verbatim
("valuation geometry … carries over as written"). -/
def DOMStmt {Sp AD δ n} (K : ReBased p Sp AD δ n) : Prop :=
  ∀ H, ∀ i ≤ K.C.kIdx H, DomData (K.lines H) i (K.interiorEnd H)

/-- **THE CInterface, layer (b)-record: `CStatements`** — one field per §C lemma
the ledger cites; each field's type IS the named statement def. The note's clause
list, typed with no fence: "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b)
with C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM". -/
structure CStatements (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop where
  secA : SecAStmt p K
  secB1 : SecB1Stmt p K
  secB2 : SecB2Stmt p K
  thmCa : ThmCaStmt p K
  thmCb : ThmCbStmt p K
  c05PinWelldef : C05Stmt p K
  c1 : C1Stmt p K
  c15ZC : C15Stmt p K
  lst : LSTStmt p K
  typ : TYPStmt p K
  dom : DOMStmt p K

/-- **THE CInterface, layer (c): (REL.1) := `CStatements` at base δ** — the typed
mutatis-mutandis pointer [OPEN KERNEL — "a NEW THEOREM with its own verification
passes"]. Instantiating the carrier package = HC-1's deliverable; consumers
hypothesize per instance, ABSOLUTE index displayed per site. -/
def REL1 (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  CStatements p Sp AD δ n K
/-- (CF17) the pass's full deliverable: EQ-1 is "a named checkpoint of REL.1's
re-scoping pass, where it is walked" — attached, typed. -/
def REL1PassDeliverable (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  REL1 p Sp AD δ n K ∧ EQ1 Sp
/-- (CF17) (EQ-2)'s "OPEN, REL.1-conditional" status, typed. -/
def EQ2lawIfREL1 (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  REL1 p Sp AD δ n K → EQ2law p AD
```

```lean
/-! ## REL.2 (file Rel2.lean; units R14–R17) -/

/-! **(REL.2a) — SIX SUB-DELIVERABLES (a1)–(a6)** (CF19's decomposition: one
checklist item per structure, composed by the bundle; "nothing short of all six
items is '(a) stated'"). Inhabitation story: the future (a)-pass. -/

/-- (a1) DOMAIN + MEASURABILITY (FF5(i)): the free base coordinates (ℓ, i)
(infinitely many — Σ_c fixes finitely many digits), the identification with the
"measurable product of O_δ-digit spaces" ((R0-box)'s ATOM), the product-side
event algebra with digit cylinders, and event-algebra compatibility. -/
structure REL2a1 (S : Setting p) where
  freeCoords : Set (ℕ × ℕ)
  freeCoords_inf : freeCoords.Infinite
  domIdent : S.Cont ≃ (freeCoords → ↥(Fsub p S.δ))
  prodEvents : Set (Set (freeCoords → ↥(Fsub p S.δ)))
  prodCyl_mem : ∀ (E : Finset (ℕ × ℕ)) (v : (ℕ × ℕ) → ↥(Fsub p S.δ)),
    {x | ∀ c : freeCoords, (c : ℕ × ℕ) ∈ E → x c = v c} ∈ prodEvents
  domIdent_meas : ∀ W, W ∈ prodEvents ↔ (fun f => domIdent f) ⁻¹' W ∈ S.AmbEvents

/-- (a2) TARGET integrality of `d_j^rel := d_j/δ_j^rel` — "part of the obligation,
EXPECTED from the tower data, walked in (a)'s pass" (E·F ∣ d_j route EXPECTED only). -/
structure REL2a2 (S : Setting p) : Prop where
  drel_dvd : (S.δrel : ℕ) ∣ (S.d : ℕ)
  drel_pos : 0 < S.dRel

/-- (a3) EMBEDDING CONVENTION: the named F_{δ_j} ↪ (tower residue field) embedding
and the canonical-lift convention, PINNED to Mathlib's Teichmüller (a field). -/
structure REL2a3 (S : Setting p) where
  TowerRes : Type
  [towerResField : Field TowerRes]
  embed : ↥(Fsub p S.δabs) →+* TowerRes
  teich : ↥(Fsub p S.δabs) → ↥(O p S.δabs)
  teich_pin : ∀ x, ((teich x : ↥(O p S.δabs)) : Wbar p)
    = WittVector.teichmuller p (x : Kbar p)

/-- (a4) FORMULA: the map Θ_j itself, on (a1)'s coordinates. -/
structure REL2a4 (S : Setting p) (A1 : REL2a1 p S) where
  Θ : (A1.freeCoords → ↥(Fsub p S.δ)) → (Fin S.dRel → ↥(O p S.δabs))

/-- (a5) FRAME COMPATIBILITY over the AMBIENT family (CF10 repair): the transports
are S's OWN C.0.5 family (`S.reframe`, supplied by the ambient theory), conjugated
to the digit side through (a1) — an inhabitant can no longer substitute a private
identity-only family. Deliverables: the target-side transports and the displayed
commutation, with unitriangularity anchors on BOTH sides (FF7; `CoordPrec` = C.0's
order on the free coordinates, Fin-order on the target coefficients). -/
structure REL2a5 (S : Setting p) (A1 : REL2a1 p S) (A4 : REL2a4 p S A1) where
  tgtOf : S.FrameC → S.FrameC →
    ((Fin S.dRel → ↥(O p S.δabs)) ≃ (Fin S.dRel → ↥(O p S.δabs)))
  ambT_unitri : ∀ (F F' : S.FrameC) (x y : A1.freeCoords → ↥(Fsub p S.δ))
      (c : A1.freeCoords),
    (∀ c' : A1.freeCoords, CoordPrec (c' : ℕ × ℕ) (c : ℕ × ℕ) → x c' = y c') →
    A1.domIdent (S.reframe F F' (A1.domIdent.symm x)) c - x c
      = A1.domIdent (S.reframe F F' (A1.domIdent.symm y)) c - y c
  tgtT_unitri : ∀ (F F' : S.FrameC) (x y : Fin S.dRel → ↥(O p S.δabs))
      (j : Fin S.dRel),
    (∀ j' < j, x j' = y j') → tgtOf F F' x j - x j = tgtOf F F' y j - y j
  frame_compat : ∀ (F F' : S.FrameC) (f : S.Cont),
    A4.Θ (A1.domIdent (S.reframe F F' f)) = tgtOf F F' (A4.Θ (A1.domIdent f))

/-- (a6) READ DICTIONARY, PER READ FIELD (CF11 repair): (R0-reads)' node-datum
fields — "SHAPE (e, h, g, μ), anchor a, SIDE endpoints/height and stride
positions, DIGITS (d_j), branch factor ψ, recentering lifts" — with the
integer/lattice fields PRESERVED (the SAME GRAMMAR) and the residue-datum fields
(digits, ψ, lifts) transported by DECLARED per-read maps (RECONSTRUCTED over the
re-based tower — no canonical inclusion, so a transport map, never an equality). -/
structure REL2a6 (S : Setting p) (Sp : SpeciesSyntax) where
  AmbRead : Type
  ambReadNe : Nonempty AmbRead
  TgtRead : Type
  readDict : AmbRead → TgtRead
  readDict_inj : Function.Injective readDict
  ambLetter : AmbRead → Sp.Letter
  tgtLetter : TgtRead → Sp.Letter
  readDict_letter : ∀ r, tgtLetter (readDict r) = ambLetter r
  ambShape : AmbRead → ℕ × ℕ × ℕ × ℕ
  tgtShape : TgtRead → ℕ × ℕ × ℕ × ℕ
  readDict_shape : ∀ r, tgtShape (readDict r) = ambShape r
  ambAnchor : AmbRead → ℕ
  tgtAnchor : TgtRead → ℕ
  readDict_anchor : ∀ r, tgtAnchor (readDict r) = ambAnchor r
  ambSide : AmbRead → (ℚ × ℚ) × List ℕ
  tgtSide : TgtRead → (ℚ × ℚ) × List ℕ
  readDict_side : ∀ r, tgtSide (readDict r) = ambSide r
  AmbResDat : AmbRead → Type
  TgtResDat : TgtRead → Type
  resDict : ∀ r, AmbResDat r → TgtResDat (readDict r)

/-- **(REL.2a) the bundle** — all six items or nothing. -/
structure REL2a (S : Setting p) (Sp : SpeciesSyntax) where
  a1 : REL2a1 p S
  a2 : REL2a2 p S
  a3 : REL2a3 p S
  a4 : REL2a4 p S a1
  a5 : REL2a5 p S a1 a4
  a6 : REL2a6 p S Sp

/-- **(REL.2b) NORMALIZATION / JACOBIAN** [OPEN KERNEL]: "for every REL.1-measurable
continuation event W over O_{δ_j} (digit cylinders generate — V's `cyl_mem`),
μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W)", with the "only for cells with μ(Σ_c) > 0"
proviso as guard. Non-vacuous: `V.events` contains univ and every cylinder, and
`V.vol` is cylinder-pinned. FF5(ii): the Θ-pullback of every event is required IN
the ambient event algebra — the Θ-measurability half of "the PUSHFORWARD of the
conditional continuation measure … IS the normalized O_{δ_j}-box measure". -/
def REL2b (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs S.dRel) : Prop :=
  0 < S.cellMass →
    ∀ W ∈ V.events,
      (fun f => A.a4.Θ (A.a1.domIdent f)) ⁻¹' W ∈ S.AmbEvents ∧
      S.condMass ((fun f => A.a4.Θ (A.a1.domIdent f)) ⁻¹' W) = V.vol W

/-- (b) WITH ITS REL.1 CONDITIONALITY TYPED: the target measure IS the REL.1
theory's (`RB.C.V`), and REL.1 at (δ_j, d_j^rel) rides as an explicit conjunct —
"EVERY consumer below is conditional on REL.1, displayed per site". -/
def REL2b_linked (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  REL1 p Sp AD S.δabs S.dRel RB ∧ REL2b p S Sp A RB.C.V

/-- **(EQ-3) CONDITIONAL MASSES TRANSPORTED** — "REL.2(b) verbatim … no weaker
reading (bijection-only, or level-matching without normalization) counts."
(Alias inherits the finding-9 repair.) -/
abbrev EQ3 (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs S.dRel) : Prop := REL2b p S Sp A V
```

```lean
/-- **(REL.2d) LIFT-POLICY COMPATIBILITY — the acceptance-criterion COMMUTATIVE
SQUARE**, with the node-data correspondence SPECIFIED (findings 11/12): the
horizontal `nodeCorr` must preserve the species word ((EQ-1) letters), transport
the reads through (a6)'s dictionary, and preserve τ-verdicts; the (EQ-2) alphabet
wiring is the `posOf` assignment into `AD`; the (a3) lift policy enters through
`A.teich_pin` (a field of `A`). Also supplies the prescribed-subtree
identification, without which "(SIB-Oδ) below is ill-typed". -/
structure REL2d (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) where
  AmbTree : Type                          -- b_j's continuation subtrees of T_can(f)
  ambTreeNe : Nonempty AmbTree
  ambTcan : S.Cont → AmbTree
  TgtTree : Type                          -- the O_{δ_j}-engine's canonical trees
  tgtTcan : (Fin S.dRel → ↥(O p S.δabs)) → TgtTree
  nodeCorr : AmbTree → TgtTree            -- the SPECIFIED correspondence
  /-- "The square commutes for every f ∈ Σ_c." -/
  square : ∀ f : S.Cont, nodeCorr (ambTcan f) = tgtTcan (A.a4.Θ (A.a1.domIdent f))
  /-- node-data content of the correspondence: species word preserved … -/
  ambWord : AmbTree → List Sp.Letter
  tgtWord : TgtTree → List Sp.Letter
  corr_word : ∀ t, tgtWord (nodeCorr t) = ambWord t
  /-- … reads transported via (a6)'s dictionary … -/
  ambReads : AmbTree → List A.a6.AmbRead
  tgtReads : TgtTree → List A.a6.TgtRead
  corr_reads : ∀ t, tgtReads (nodeCorr t) = (ambReads t).map A.a6.readDict
  /-- … τ-verdicts preserved … -/
  ambVerdict : AmbTree → List Bool
  tgtVerdict : TgtTree → List Bool
  corr_verdict : ∀ t, tgtVerdict (nodeCorr t) = ambVerdict t
  /-- … and (EQ-2)'s alphabets: each target read sits at an `AD` position class. -/
  posOf : A.a6.TgtRead → AD.Pos
  /-- (CF12) posOf is CONSTRAINED: the position class assigned to a target read
  carries that read's species letter — the (EQ-2)-alphabet wiring is the read's
  own, not a free assignment. -/
  posOf_letter : ∀ r, AD.posLetter S.δabs (posOf r) = A.a6.tgtLetter r
  /-- canonical O_{δ_j}-side prescribed subtrees, T_j's identification, and the
  target realization predicate ((W1)'s reading inherited from [1]/[3t]). -/
  TgtSub : Type
  subtreeCorr : S.PTree → TgtSub
  TgtRealizes : TgtTree → TgtSub → Prop

/-- **(REL.2e) β-IDENTIFICATION, (e1)–(e5)** (findings 13/14 repairs: `entryFirst`
FIXED per branch; `consumed` = the prescriptions [3]'s entry actually consumes;
(e1)↔(a6) compatibility typed). Inhabitation story: the future (e)-pass with [3]'s
tables in hand. -/
structure REL2e (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) (D : REL2d p S Sp AD A) where
  /-- (e1) REL.1-side states over O_{δ_j} + the dictionary from τ_j(c) … -/
  RelState : Type
  relStateNe : Nonempty RelState
  stateDict : S.StateIdx → RelState
  /-- … "compatible with (a6)'s read dictionary", TYPED: states carry their
  defining reads; the dictionary transports them letter-for-letter. -/
  stateReadsAmb : S.StateIdx → List A.a6.AmbRead
  stateReadsRel : RelState → List A.a6.TgtRead
  stateDict_compat : ∀ s, stateReadsRel (stateDict s) = (stateReadsAmb s).map A.a6.readDict
  /-- [3]'s table, in [3]'s own keying: (first index, state, argument) ↦ entry. -/
  β : ℕ → S.StateIdx → ℕ → ℚ
  /-- (e4) the first index e_j, FROM b_j's DATA — one value per branch (finding 13).
  (CF14: the consumed-prescription set is NOT a field — it is a parameter of the
  (e)-Props below, supplied by [3]/MovesS exactly like `tableConv`.) -/
  entryFirst : ℕ

/-- (e4)'s agreement with [3]'s table convention, TYPED against the convention as
a parameter ([3]/MovesS's export — D5): a typed claim, not prose. -/
def REL2e.e4agrees {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (tableConv : ℕ → Prop) : Prop := tableConv E.entryFirst
/-- (e4)'s CANDIDATE ["candidate: (a2)'s O_{δ_j}-degree d_j^rel — owed, not
assumed"]. (CF13) DEMOTED: a NAMED CANDIDATE definition only — NOT an obligation,
REMOVED from D7's hypothesis list; NO consumer may hypothesize it. (e4)'s
obligation is `e4agrees` alone. -/
def REL2e.firstIdxCandidate {S Sp AD A D} (E : REL2e p S Sp AD A D) : Prop :=
  E.entryFirst = S.dRel
/-- (e5) first disjunct: "the entry's indices must DETERMINE the prescribed
subtree T_j". (CF14) `consumed` — the prescriptions [3]'s tables actually consume
at this key — is a PARAMETER supplied by [3]/MovesS's export, like `tableConv`:
choosing it here was the vacuity Codex flagged. Re-keying stays a statement-fence
event (D5). -/
def REL2e.determines {S Sp AD A D} (_E : REL2e p S Sp AD A D)
    (consumed : Set S.PTree) : Prop :=
  ∀ T ∈ consumed, ∀ T' ∈ consumed, T = T'
/-- (e3) MASS = ENTRY, stated GIVEN (e5): β_{e_j, τ_j(c)}(p^{δ_j}) IS **the REL.1
mass** (FF6 `_linked`: the vol is `RB.C.V` of a REL1-hypothesized package;
FF5(iii): the realization event ∈ `RB.C.V.events`; CF14: `consumed` is [3]'s
parameter). -/
def REL2e.massEqEntry {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (consumed : Set S.PTree) (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  REL1 p Sp AD S.δabs S.dRel RB ∧ E.determines p consumed ∧ ∀ T ∈ consumed,
    {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)} ∈ RB.C.V.events ∧
    E.β E.entryFirst S.τ (S.βarg p) =
      RB.C.V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}
/-- (CF20) THE COLLECTING CONJUNCTION — one Prop gathering the (e)-obligations
((e2) is the definitional `βarg_eq`; (e1) is E's data + `stateDict_compat` field):
the single hypothesis interface consumers cite. -/
def REL2eObligations {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (tableConv : ℕ → Prop) (consumed : Set S.PTree)
    (RB : ReBased p Sp AD S.δabs S.dRel) : Prop :=
  E.e4agrees p tableConv ∧ E.determines p consumed ∧ E.massEqEntry p consumed RB
```

```lean
/-- (e2) as the checkable identity behind `Setting.βarg`: "the β-argument is
p^{δ_j} with δ_j ABSOLUTE …, = q_δ^{δ_j^rel}" (provable via `qq_mul`, part of R5). -/
theorem βarg_eq (S : Setting p) : S.βarg p = qq p S.δ ^ (S.δrel : ℕ) := qq_mul p _ _

/-! ## R.2 — (SIB-Oδ) (file Sib.lean; units R22–R23) -/

/-- **(SIB-Oδ)** [FENCED = REL.1 + REL.2(a)+(b)+(d), composed; derived nowhere yet].
"For EVERY realized prefix η, EVERY branching cell c, EVERY branch b_j —
simultaneously over every unramified O_δ that arises (all δ ≥ 1 in one statement)
— the event S_j IS an O_{δ_j}-statement", with (REL.2b)'s pricing
  μ( S_j │ Σ_c ) = vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j },
the right side a REL.1-THEORY mass (the REL.1 conjunct is explicit — finding 20).
Quantifier = the realized `SettingsFamily` (nonempty, root δ = 1, descent-closed
with absolute re-indexing — findings 19/20); the positive-cell guard is the note's
own conditioning proviso; the first conjunct of the ∀T clause is the "S_j IS an
O_{δ_j}-statement" typing itself (S_j = the Θ-pullback of the target realization
event); the second is the pricing, at a realization event required IN
`RB.C.V.events` (FF5(iii)) so the REL.1 measure laws bind there.
REV 4 (CF1/CF2): the quantifier is over a `mem_pos`-restricted family (the
conditioning sites — the zero-mass singleton is dead), the identification data is
ONE COHERENT PACKAGE FUNCTION over the whole family with ONE (Sp, AD) — (EQ-1)'s
same-syntax-over-every-base — and the RECURSION CLAUSE is now TYPED COMPOSITION:
each descendant's AMBIENT theory IS the parent's TARGET theory (same base index by
`desc_amb`, same box degree, same carrier package up to the index transport) —
"the obligations must COMPOSE across nested base changes"; `O_chain` supplies the
literal subring chain TREE-EXP's induction consumes. -/
structure SIBPkg (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) (S : Setting p) where
  A : REL2a p S Sp
  D : REL2d p S Sp AD A
  ambDeg : ℕ                                    -- the ambient box degree at S's cell
  ambK : ReBased p Sp AD S.δ ambDeg             -- the AMBIENT REL.1 carrier (base O_δ)
  RB : ReBased p Sp AD S.δabs S.dRel            -- the TARGET REL.1 carrier (base O_{δ_j})

def SIBOdelta (F : SettingsFamily p) : Prop :=
  ∃ (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (pkg : ∀ S ∈ F.mem, SIBPkg p Sp AD S),
    ∀ S (hS : S ∈ F.mem), 0 < S.cellMass →
      REL1 p Sp AD S.δ (pkg S hS).ambDeg (pkg S hS).ambK ∧      -- ambient REL.1 (δ = 1: verbatim)
      REL1 p Sp AD S.δabs S.dRel (pkg S hS).RB ∧                -- target REL.1
      REL2b p S Sp (pkg S hS).A (pkg S hS).RB.C.V ∧
      (∀ T : S.PTree,
        {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)}
            ∈ (pkg S hS).RB.C.V.events ∧
        S.SEvent T = (fun f => (pkg S hS).A.a4.Θ ((pkg S hS).A.a1.domIdent f)) ⁻¹'
            {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)} ∧
        S.condMass (S.SEvent T) =
          (pkg S hS).RB.C.V.vol
            {g | (pkg S hS).D.TgtRealizes ((pkg S hS).D.tgtTcan g) ((pkg S hS).D.subtreeCorr T)}) ∧
      -- (CF2) COMPOSITION across nested base changes: descendant ambient = parent target
      (∀ (T : S.PTree) (S' : Setting p) (hS' : S' ∈ F.desc S hS T),
        (pkg S' (F.desc_sub S hS T hS')).ambDeg = S.dRel ∧
        HEq (pkg S' (F.desc_sub S hS T hS')).ambK (pkg S hS).RB)

/-- R23: the recursion clause's ring-side witness — "a branch of relative
accumulated degree δ″ at ambient O_{δ_j} targets O_{δ_j·δ″}, literally a subring
chain in W(F̄_p)". (Family-closure is `SettingsFamily.desc*`; this is the
ring-theoretic half, not a substitute — finding 20.) -/
theorem O_chain (S : Setting p) (δ'' : ℕ+) :
    O p S.δ ≤ O p S.δabs ∧ O p S.δabs ≤ O p (S.δabs * δ'') := sorry

/-! ## R.3 — (REL.3): NO LEAN OBJECT (finding 21; blueprint D6).
"The [4]-side displays (SQ.0–SQ.2 …) DO NOT EXIST YET — … so no theorem statement
is possible here." When [4] drafts SQ.0–SQ.2, REL.3's revision restates each
consumed display verbatim, base re-scoped to O_δ (ABSOLUTE indices), and enters
this corpus as NEW AUDITED UNITS. Discipline fixed now (plan): each consumed leg
β_m(p^δ) must arrive as a CERTIFIED vol_{O_δ}-statement (a `REL1`-conditional
theorem about `BoxVol`-masses), NEVER the formal substitution q ↦ q^δ in a
ℤ_p-display. This comment block is the whole of REL.3 in MovesR. -/

/-! ## Elaboration checks (per D9) -/
section Elab
-- Carrier instances (honest trivial cases only). REV-4 note: a trivial
-- `SettingsFamily` now needs a POSITIVE-mass member (mem_pos + ne) — use
-- cellMass := 1, condMass := indicator laws; desc _ _ _ := ∅ stays lawful.
--   example : Setting 2 := ⟨…, cellMass := 1, …, FrameC := PUnit, ⟨⟨⟩⟩,
--     reframe := fun _ _ => id, …⟩
--   example : SettingsFamily 2 := singleton on the above (mem_pos by rfl-arith)
--   example : SpeciesSyntax := ⟨PUnit, fun _ => (1,1,1,1), PUnit, fun _ => ⟨⟩,
--     PUnit, fun _ => ⟨⟩, injective-into-constant …, fun _ => ∅⟩  -- empty menus OK (CF3)
--   example : AlphabetData 2 Sp₀ := degenerate-lawful (alpha = closure of range of
--     the zero slotMap = {0}; card_eq : 1 = 2^0; aDim ≡ 0)
-- Obligation/deliverable structures: #check only (inhabitation = the pass/HC-1):
--   #check @GradedCarrier  #check @CStatements  #check @REL1  #check @LSTStmt
--   #check @REL2a  #check @REL2b_linked  #check @REL2d  #check @REL2eObligations
--   #check @SIBPkg  #check @SIBOdelta  #check @BoxVol  #check @ReBased.count
end Elab
end MovesR
```

SKELETON STATUS: NORMATIVE FOR CONTENT, not character-exact — E-phase fixes syntax
(instance-field bracketing, `Fin 0`-index forms, implicit-argument threading,
namespace qualification for `DigitSystem`/`IsUnitriangular`/`Line`/`DomData`)
WITHOUT changing any quantifier, equality, guard, or field list; anything beyond
syntax re-enters the audit loop (statement fence).

## 2. Unit specs (41 units; compact REV-4 format — id · statement · moves_ref key · deps · difficulty)

Files/import order: `Base` → `Interface` → `Eq` → `CInt` (GradedCarrier + statement
defs + CStatements) → `Rel1` → `Rel2` → `Sib`; `Defs.lean` re-export shim. Per-unit
acceptance: definitions land verbatim-from-skeleton + D9 elaboration compiles.
moves_ref keys quote §R-LEDGER (rev 5) unless marked §C (= the LST/TYP/DOM displays
at MOVES 3728–3831, consulted sources per the adjudication).

BASE (U1–U6; provable U2–U6):
- U1 base_defs: `Kbar/Wbar/Fsub/O/qq/relExt/cyl` · "F_m is THE subfield of order
  p^m and O_m := W(F_m) ⊂ W(F̄_p)" · — · easy.
- U2 Fsub_le · U3 O_le: nesting · "compose LITERALLY as subrings" · U1 · medium.
- U4 relExt_comp (`rfl`/`mul_assoc`/`O_le_relExt`) · "'(O_δ)_{δ′} = O_{δδ′}' is
  bookkeeping inside W(F̄_p)" · U1,U3 · easy.
- U5 qq_mul + βarg_eq · "q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}" + (e2) · U1,U7 · easy.
- U6 Fsub_card: `Nat.card ↥(Fsub p m) = p^m` · "THE subfield of order p^m" · U1 ·
  hard (wave-3).

INTERFACE (U7–U8):
- U7 Setting + δabs/dRel/βarg + FrameC/reframe (CF10's ambient family) + measure
  laws · the SETTING paragraph + "frame Ψ_η" · U1 · medium.
- U8 SettingsFamily + mem_pos (CF1, note-checked: the (b) proviso's "the only
  cells any (SIB) display conditions on") + desc closure · "(SIB-Oδ)" quantifier +
  recursion clause · U7 · medium.

EQ (U9–U12; provable U12):
- U9 SpeciesSyntax (shape/side/poly + letter_det — CF4; menuNe REMOVED — CF3) +
  EQ1 · "(EQ-1) … SAME finite syntax … never the letter set" · — · medium.
- U10 AlphabetData + slotMap/alpha_attain (CF5) + posLetter/Stable · "(EQ-2)
  DEFINITION (unconditional): … attainable additive image/span of the RE-BASED
  slot maps" · U1,U9 · medium.
- U11 EQ2law (BOTH conjuncts — F_δ-linearity + a_δ = δ·a, CF6) · "the re-based
  piece maps are F_δ-linear and a_δ = δ·a" (pinned domain) · U10 · easy-medium.
- U12 EQ2law_card · "|𝔸_δ| = q_δ^a = |𝔸|^δ" · U5,U11 · easy (provable).

CINTERFACE (U13–U29; one display per unit — CF18):
- U13 BoxVol + events_level (CF15: Haar characterized on the WHOLE event class;
  (g7)'s determination-radius discipline cited) · "(R0-box) … vol_{O_δ}(O_δ^n)=1;
  … q_δ^{nN} residue points" · U1 · medium.
- U14 GradedCarrier (D4(a): Coeff/Gr/w/inγ + 4 laws; ≤10 fields, no construction;
  instantiation = HC-1) · "(R0-tower) graded rings … D.3(e)(i)'s graded piece"
  (via §C consumption) · — · medium.
- U15 TowerData + Base/Climb/StageCarrier laws · "(R0-tower) F₁ := F_δ[x]/(φ̄) …
  F_{k+1} = F_k[z]/(ψ_k) … built afresh" · U1 · medium.
- U16 REL1Counting (no count field — FF2) · "(REL.1-b)" carriers · U13 · easy.
- U17 ReBased (carriers: jet/tower/frames/Status+pinStatus (CF9)/aDim wiring
  (FF4)/G attachment/LST carriers + mono/slotCoeff/interior_fresh (CF8)) +
  `ReBased.count` def (FF2) · (R0-box/tower/reads/ledger) · U9,U10,U14,U15,U16 ·
  hard (carrier only — no Props beyond laws).
- U18 SecAStmt · §A base shape · U17 · easy. — U19 SecB1Stmt (CF16: graded
  vocabulary typed via G; slotCoeff additivity) · "§B1 … same construction run
  over the new base" · U17 · easy-medium. — U20 SecB2Stmt · D.0 climb · U17 · easy.
- U21 ThmCaStmt · "Theorem C(a)" locus = jet-preimage · U17 · easy.
- U22 ThmCbStmt · "(REL.1-b)" verbatim over the DEFINED count · U17 · medium.
- U23 C05Stmt (unitri + card AND STATUS multiset (CF9) + aDim multiset) ·
  "C.0.5/PIN-WELLDEF … cardinality-and-status statistics" · U17 · medium.
- U24 C1Stmt · "(R0-ledger) … factor |𝔸_δ|⁻¹ of its ATTAINABLE alphabet" · U17 ·
  easy. — U25 C15Stmt · "C.1.5's (ZC) invariant" · U17 · easy.
- U26 LSTStmt (FULL: chain-weight typing + slot-min + in_γ/level-set + interior
  constancy + selection — CF7 resolved, no fence) · §C Lemma LST (i)/(ii)/(iii),
  MOVES 3728 · U14,U17 · hard (typing).
- U27 TYPStmt (additivity + attainable-image cardinality = p^{a_δ}) · §C Lemma
  TYP + walk item (i) · U17 · medium.
- U28 DOMStmt · §C Lemma DOM via MovesC `DomData` ("valuation geometry … carries
  over as written") · U17 · easy.
- U29 CStatements + REL1 (:= CStatements at δ — the typed mutatis-mutandis
  pointer) + REL1PassDeliverable/EQ2lawIfREL1 (CF17 attachments) · "(REL.1) …
  hold over O_δ … MUTATIS MUTANDIS" + (EQ-1)/(EQ-2) status lines · U18–U28 · easy.

REL.2 (U30–U39; one checklist item per unit — CF19/CF20):
- U30 REL2a1 (a1 + FF5(i)) · "(a1) DOMAIN … measurable product" · U7 · medium.
- U31 REL2a2 (a2) · "(a2) … integrality of d_j^rel" · U7 · easy.
- U32 REL2a3 (a3 + teich_pin) · "(a3) EMBEDDING CONVENTION … Teichmüller" · U1 ·
  easy-medium.
- U33 REL2a4 (a4) · "(a4) FORMULA: … Θ_j itself" · U30 · easy.
- U34 REL2a5 (a5 over the AMBIENT family — CF10; unitri anchors — FF7) · "(a5) …
  C.0.5's unitriangular transports" · U7,U30,U33 · medium.
- U35 REL2a6 (a6 PER READ FIELD — CF11: shape/anchor/side preserved, residue-datum
  transports declared) · "(a6) READ DICTIONARY … displayed per read field" +
  (R0-reads) · U9 · medium.
- U36 REL2a bundle · "nothing short of all six items" · U30–U35 · easy.
- U37 REL2b (+ FF5(ii) membership) + REL2b_linked + EQ3 · "(REL.2b)" display +
  "(EQ-3) … REL.2(b) verbatim" · U13,U29,U36 · medium.
- U38 REL2d (square + word/reads/verdict corr + posOf_letter — CF12) · "(REL.2d)
  … COMMUTATIVE SQUARE … SPECIFIED node-data correspondence" · U36,U9,U10 · hard.
- U39 REL2e + e4agrees/firstIdxCandidate(demoted — CF13)/determines/massEqEntry
  (consumed = [3]'s parameter — CF14) + REL2eObligations (CF20 conjunction) ·
  "(REL.2e) … (e1)–(e5)" · U29,U36,U38 · medium-hard.

SIB (U40–U41; provable U41):
- U40 SIBPkg + SIBOdelta (family package function + ambient/target REL1 + the CF2
  composition clause: descendant ambient = parent target, HEq up to index
  transport) · "(SIB-Oδ)" + "the obligations must COMPOSE across nested base
  changes" · U8,U29,U36,U37,U38 · hard.
- U41 O_chain · "literally a subring chain in W(F̄_p)" · U3,U7 · easy (provable).

(REL.3: NO UNIT — D6. REL.2(c), REL-n4, PREDICTED brackets: non-units, D6.)

## 3. Audit notes (wave-2 re-audit; budget: exactly one pass)

- FAITHFULNESS ANCHORS: every docstring quotes the rev-5 display it encodes; the
  moves_refs above are the check keys. Only `theorem`s: U2–U6, U12, U41 (base-index
  bookkeeping + the card fact + one hypothesis-conditional pow identity).
- DELIBERATE RESIDUAL WIDENINGS (each recorded): (i) `Setting` absorbs η/Σ_c/b_j
  into carriers-with-laws; the realized quantifier is `SettingsFamily` (supplied by
  the ambient theory; closure typed; conditioning sites per `mem_pos`).
  (ii) SUPERSEDED AT REV 4: the §B1/LST fences are GONE — the CInterface types the
  graded vocabulary (`GradedCarrier`) and each cited lemma's full statement
  (`*Stmt` defs); what remains recorded is that the interface's INSTANTIATION from
  the OM engine is HC-1's deliverable (localization L / degree-1 unit T ride
  there), not this corpus's.
  (iii) (e5)'s second disjunct (re-keying) is a statement-fence event, not a Prop
  disjunct (D5). (iv) WITHDRAWN at REV 3 (FF1); the rev-4 `LSTStmt` types ALL
  legs including the formerly-fenced clauses.
  (v) free-data relativity (FF7), NARROWED at REV 4: the ambient engine's
  transports are no longer inhabitant-chosen ((a5) quantifies over `S.reframe`,
  CF10); trees/reads/floors remain free data constrained by their typed laws
  (anchors, preservation, cylinder pins, teich_pin, `posOf_letter`, `mem_pos`,
  `interior_fresh`, attainability). Law-respecting junk remains constructible
  exactly where the engine has no Lean form; D7 says this accurately; full pinning
  = HC-1 + the REL.1 pass.
- CROSS-NOTE WATCHES INHERITED: (W1) `SEvent`/`TgtRealizes` stay opaque — every
  MovesR statement is neutral to the [1]/[3t] "realizes" pin; the pinned reading
  lands as the supplier's definition at the CL-10 sync, no statement changes.
  (W2) absolute indices enforced by construction (`δabs`, `βarg`, `relExt`).
- PLAN-SYNC FLAG (note R.1): CL-8 owes the (e) leg + the five-count; MovesR carries
  the five-obligation convention ((c) absent by re-homing).
- CONSUMER EDGES: MovesT consumes `SIBOdelta`/`Setting`/`SettingsFamily`/`O_chain`;
  MovesS consumes `REL2e` + `βarg_eq` and EXPORTS `tableConv` AND `consumed`
  ((e4)'s and (e5)'s parameters — CF14); MovesU consumes the future REL.3 units
  (none yet — D6); MovesV cites `REL1` (= `CStatements`); HC-1 owes the
  `GradedCarrier`/`ReBased` instantiation. Import direction: those corpora import
  MovesR, never conversely.

## 4. File map + status ledger

  lean/LeanUrat/MovesR/Base.lean       U1–U6   (defs + 5 provable lemmas + card)
  lean/LeanUrat/MovesR/Interface.lean  U7–U8   (Setting+FrameC+laws, SettingsFamily+mem_pos)
  lean/LeanUrat/MovesR/Eq.lean         U9–U12  (SpeciesSyntax+grammar, AlphabetData+spans, EQ-1/2)
  lean/LeanUrat/MovesR/CInt.lean       U13–U29 (BoxVol, GradedCarrier, TowerData, counting,
                                                ReBased+count, the 11 *Stmt defs, CStatements+REL1)
  lean/LeanUrat/MovesR/Rel2.lean       U30–U39 ((a1)–(a6)+bundle, (b)+EQ-3, (d), (e))
  lean/LeanUrat/MovesR/Sib.lean        U40–U41 (SIBPkg+SIBOdelta, chain)
  lean/LeanUrat/MovesR/Defs.lean       re-export shim
  (REL.3: no file, no object — D6.)

## 5. Findings → repairs (Codex audit 2026-07-28, 15 crit / 6 gap)

  F1  (crit, R1 card omitted)        → unit R6 `Fsub_card` stated (D1; overruled non-unit).
  F2  (crit, Setting degenerate)     → realized-measure law fields; nonempty Cont/PTree (R7).
  F3  (crit, ledger slots vacuous)   → ten TYPED clause fields over ReBased/TowerData (R12, D4).
  F4  (crit, counting vacuous/n)     → fixed n param; nonempty Hist/Locus; vols through pinned V (R11).
  F5  (crit, REL1 vacuous)           → REL1 := typed clauses ∧ display over non-degenerate carriers (R13).
  F6  (crit, (a5)/(a6) vacuous)      → nonempty FrameIdx/AmbRead; readDict injective + letter-preserving (R14).
  F7  (gap, teich pin external)      → `teich_pin` now a FIELD of REL2a; compat Props typed (R14).
  F8  (crit, BoxVol dummy)           → event algebra + content laws + `vol_cyl` cylinder pin (R10).
  F9  (crit, REL2b vacuous)          → events cylinder-populated; guard = the note's proviso (R15).
  F10 (gap, REL1 link prose-only)    → `REL2b_linked` conjoins REL1 at (δ_j, d_rel) (R15).
  F11 (crit, REL2d junk corr)        → corr_word/corr_reads/corr_verdict typed; PUnit example dropped (R16).
  F12 (gap, (a3)/(EQ-2) deps absent) → A.teich_pin field + AD parameter + posOf wiring (R16).
  F13 (crit, entryFirst varies)      → `entryFirst : ℕ` FIXED; `consumed` set carries the T-multiplicity (R17, D5).
  F14 (gap, (e1)/(e4) compat absent) → stateDict_compat typed; e4agrees(tableConv) parameterized (R17).
  F15 (crit, EQ1 infinite menus)     → Finset menu + menuNe + stage-tuple anchor (R18).
  F16 (crit, EQ2 arbitrary numbers)  → alphabets as additive spans; card_eq; Stable DEFINED via posLetter (R19).
  F17 (gap, Stable dictionary)       → posLetter = the owed dictionary AS DATA; Stable = letter persistence (R19).
  F18 (crit, EQ3 inherits vacuity)   → alias of the repaired REL2b (R15).
  F19 (crit, SIB empty/unguarded)    → SettingsFamily (ne, root, desc-closure); 0 < cellMass guard (R8, R22).
  F20 (gap, REL1/closure missing)    → REL1 conjunct in the ∃; closure typed in family; O_chain = ring half only (R22, R8, R23).
  F21 (crit, REL3 pseudo-statement)  → DELETED; REL.3 = recorded non-unit with acceptance path (D6).

Fresh-Fable audit (`MOVESR_AUDIT_FABLE_2026-07-28.md`, 2 crit / 5 gap; all 21
Codex repairs verified genuine there):

  FF1 (crit, lst mislabeled + entailed by REL1b) → `lst` RETYPED as Lemma LST's
      three legs (slot-min TYPING / interior FLOOR CONSTANCY / floor-downset
      SELECTION) over new ht/blk/floor carriers, per the §C display MOVES 3728;
      stabilization reading withdrawn; §3 widening (iv) withdrawn (R12, D4).
  FF2 (crit, count free data → lawful-junk REL1b) → count field DELETED;
      `ReBased.count` DEFINED from SHZ + cyl (level-N cylinder classes meeting
      the classifier locus); REL1b consumes the definition (R11, R12, R13).
  FF3 (gap, PIN-WELLDEF status leg dropped) → c05PinWelldef gains the second leg:
      frame-invariance of the pinned aDim-multiset (cardinality AND status) (R12).
  FF4 (gap, a_δ double-booked) → ReBased parameterized by (Sp, AD);
      `posOfDigit` + `aDim_eq` tie c1's exponents to (EQ-2)'s AlphabetData (R12).
  FF5 (gap, three measurability memberships dropped) → (i) REL2a gains
      prodEvents + digit-cylinder anchor + domIdent_meas; (ii) REL2b gains the
      Θ-pullback ∈ AmbEvents conjunct; (iii) SIBOdelta + massEqEntry require the
      realization event ∈ RB.C.V.events (R14, R15, R17, R22).
  FF6 (gap, (e3)'s vol arbitrary) → massEqEntry retyped on `RB : ReBased` with
      the REL1 conjunct — the _linked pattern; the mass is THE REL.1 theory's (R17).
  FF7 (gap, (a5) unanchored + D7 overclaim) → ambT_unitri/tgtT_unitri
      (CoordPrec-anchored unitriangularity); D7's false claim withdrawn and
      replaced; residue recorded as widening (v) (R14, D7, §3).

Codex FINAL audit on rev 3 (`MOVESR_AUDIT_CODEX_FINAL_2026-07-28.md`, 15 crit /
5 gap; parallel fresh-Fable #2: ACCEPT 0/0) — per-finding TRIAGE (adjudication #1;
S = survived, folded in · R = resolved-by-rearchitecture · N = note-rejected):

  CF1  (crit, zero-mass singleton)   S → `mem_pos` family-scope law (NOTE-CHECK: the note has
       NO positive-cell existence law; the (b) proviso "the only cells any (SIB) display
       conditions on" is the warrant — family = conditioning sites) (U8, U40).
  CF2  (crit, composition untyped)   S → ONE coherent package function per family + the typed
       composition clause: descendant AMBIENT theory = parent TARGET theory (ambDeg equality
       + HEq across desc_amb's index transport) (U40).
  CF3  (crit, menuNe strengthens)    S — NOTE-CHECK CONFIRMS CODEX ("no menu/exhaustion
       claims", R.5) → `menuNe` REMOVED; empty menus back in range (U9).
  CF4  (crit, species grammar)       S → SideData/PolyConv carriers + projections +
       `letter_det` injectivity ("letters are DEFINED BY …") (U9).
  CF5  (crit, alpha not attainable)  S → declared `slotMap` + `alpha_attain` span-generation
       equality (U10).
  CF6  (crit, EQ-2 linearity half)   R → the slot maps now EXIST as data with F_δ-module
       structure; EQ2law types BOTH conjuncts (U10, U11).
  CF7  (crit, LST incomplete)        R → `LSTStmt` types ALL legs over `GradedCarrier`:
       chain-weight typing `G.w (mono i) = ht i`, slot-min, in_γ/level-set functionality,
       (ii), (iii) — no fence (U14, U26).
  CF8  (crit, interiorB vacuous)     S → `interior_fresh` ("on the factor interior — where
       all fresh content lives"): constrained digits sit on interior blocks (U17).
  CF9  (crit, pin status ≠ aDim)     S → `Status` carrier + `pinStatus` + `pinnedIn_spec`;
       C05Stmt's status-multiset invariance leg (aDim multiset retained as the ledger
       weight) (U17, U23).
  CF10 (crit, (a5) identity family)  S → (a5) quantifies over the AMBIENT `S.reframe`
       family (Setting-supplied); deliverable = target transports + commutation (U7, U34).
  CF11 (crit, (a6) letter-only)      S → per-read-field typing: SHAPE/anchor/SIDE preserved;
       DIGITS/ψ/lifts as declared per-read transports (RECONSTRUCTED, per (R0-reads)) (U35).
  CF12 (crit, (d) unconstrained)     S (typable layer) → `posOf_letter` pins the alphabet
       wiring; reads structured via U35; the full canonical-tree/lift-policy pinning to the
       ENGINE = HC-1's instantiation, recorded in D4/§3(v) (U38).
  CF13 (crit, candidate promoted)    S → `firstIdxCandidate` DEMOTED (named candidate, no
       consumer may hypothesize it; removed from D7's list); (e4) = `e4agrees` alone (U39).
  CF14 (crit, consumed free)         S → `consumed` re-keyed as [3]/MovesS's exported
       PARAMETER, like `tableConv` (U39, §3 consumer edges).
  CF15 (crit, BoxVol not Haar)       S → `events_level`: every event a finite cylinder union
       at some level, so vol is FORCED everywhere by additivity + `vol_cyl` ((g7)'s
       determination-radius discipline cited) (U13).
  CF16 (gap, §B1 fenced)             R → `GradedCarrier` types the graded vocabulary + laws;
       `SecB1Stmt` adds slotCoeff additivity; localization/degree-1 unit ride at HC-1,
       recorded (U14, U19).
  CF17 (gap, EQ unattached)          S → `REL1PassDeliverable := REL1 ∧ EQ1` (the pass's
       named checkpoint) + `EQ2lawIfREL1 := REL1 → EQ2law` ("OPEN, REL.1-conditional") (U29).
  CF18 (gap, R12 multi-lemma)        S → split into U13–U29: carriers, count, and ELEVEN
       one-display statement defs, each its own unit.
  CF19 (gap, R14 multi-lemma)        S → split into U30–U36: one checklist item per
       structure + the bundle.
  CF20 (gap, R17 split ambiguity)    S → e-Props separated + `REL2eObligations` as THE single
       collecting conjunction consumers cite (U39).

  TRIAGE COUNTS: 17 SURVIVED (folded in) · 3 RESOLVED-BY-REARCHITECTURE (CF6, CF7,
  CF16) · 0 NOTE-REJECTED (both ordered note-checks resolved FOR the repair: CF1's
  law does not exist in the note — family-scope mechanism used instead; CF3's
  strengthening confirmed and removed).

STATUS (2026-07-28): REV 4 WRITTEN (re-architecture per stuck-rule adjudication #1)
— Codex 21/21 (rev 2) + Fable 7/7 (rev 3, confirmed genuine by Fable #2) + Codex
FINAL 20/20 triaged (17 folded / 3 by re-architecture). 41 units: 7 provable
(U2–U6, U12, U41), 34 statements-only; the CInterface (GradedCarrier + 11 *Stmt
defs + CStatements) replaces every fence; HC-1 owes the instantiation. No axioms;
no kernel discharged; statement fence in force. This corpus PARKS here pending the
campaign's next gate.
