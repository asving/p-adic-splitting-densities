# MovesR LEAN BLUEPRINT — REV 3

SOURCE (ground truth): `lean/notes/MOVES_2026-07-24.md` §R-LEDGER, rev 5, DUAL-ACCEPTED
2026-07-27. AUDITS: `MOVESR_AUDIT_CODEX_2026-07-28.md` — REJECT (15 crit / 6 gap) on
rev 1, all 21 repaired at rev 2 and verified genuine by the fresh-Fable re-audit;
`MOVESR_AUDIT_FABLE_2026-07-28.md` — REJECT (2 crit / 5 gap) on rev 2, all 7 (FF1–FF7)
repaired here (findings→repairs table, §5). For Lemma LST the §C display itself
(MOVES 3728–3781) is now a consulted source (the FF1 adjudication). The
campaign-wide lesson driving this revision: **STATEMENTS-ONLY ≠ CONTENT-FREE** — a
faithful obligation statement must be FALSE for instances the note would reject. So
every carrier structure now carries the note's own laws as fields (measure laws,
normalized-cylinder masses, nonemptiness/finiteness, typed clause content), and every
open kernel remains a named Prop that consumers hypothesize — nothing is discharged.
Units are definitions + elaboration checks; proof burden = the base-index layer only
(R2–R6, R20, R23). Unit format per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2.
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

**(D4) REL.1 = TYPED CLAUSE LEDGER + THE (REL.1-b) DISPLAY (findings 3/4/5 repair).**
The rev-1 arbitrary-Prop slots are RETIRED. `REL1Clauses` is now a Prop-structure
over a re-based carrier package `ReBased p δ n` (fixed box degree n — finding 4),
with TEN NAMED FIELDS, each typed over the actual objects its clause mentions, in
the vocabulary §R-LEDGER itself displays ((R0-box/tower/reads/ledger) + the walk
items): tower laws via `AdjoinRoot` presentations (§A/§B1/§B2-DEF), classifier locus
= jet-preimage of a digit system (Theorem C(a), MovesC's thmC_a shape), unitriangular
transports + frame-invariant pin statistics (C.0.5/PIN-WELLDEF), the per-constrained-
digit |𝔸_δ|⁻¹ = (p^{a_δ})⁻¹ product (C.1, (R0-ledger) verbatim), a transport-invariant
(ZC) statistic (C.1.5), Lemma LST's level-set scale-typing legs (LST — retyped at
REV 3 per FF1: ht-weight slot-minimum TYPING, interior FLOOR CONSTANCY, floor-downset
SELECTION, against the §C display at MOVES 3728; the rev-2 stabilization reading is
REFUTED and withdrawn), per-digit ADDITIVITY of the jet map (TYP — walk item (i)'s
retyping, verbatim), and MovesC's base-free `DomData` (DOM — the note: "valuation
geometry … carries over as written"). The (REL.1-b) LHS `count` is no longer free
data: it is DEFINED from in-corpus vocabulary (`SHZ` + `cyl`, FF2), so `REL1b` is a
counting fact about the classifier locus, not a relation between supplied numbers.
`ReBased` is parameterized by (Sp, AD) and carries `posOfDigit` + `aDim_eq`, tying
the c1 exponents to (EQ-2)'s alphabet data (FF4). The
clause fields REMAIN unproved obligations; their TYPES now pin their content. Where
§R-LEDGER's own text gives no display for a clause's internals (§B1's graded pieces),
the field types the typable residue (finite stage carriers, char p, tower embeddings)
and the docstring cites the (R0-tower) fence — recorded, not smuggled.

**(D5) THE (e) KEYING (findings 13/14 repair).** `entryFirst : ℕ` is FIXED per
branch (the note: e_j defined "from b_j's data" — never varying with T, which would
smuggle the subtree into the first index). The prescriptions [3]'s entry at this key
actually consumes form a deliverable set `consumed : Set S.PTree` (nonempty); (e5)'s
first disjunct `determines` says `consumed` is a singleton class (the entry's indices
determine T_j); (e3) `massEqEntry` is stated GIVEN `determines` (the note: without
(e5) the equation is ill-typed) and prices every consumed prescription. The re-keying
escape ("T_j added as an explicit further index, tables re-keyed") is a STATEMENT-
FENCE EVENT — if `determines` is refuted, R17's β field type changes only with
designer sign-off. (e4)'s agreement with [3]'s table convention is typed as
`e4agrees (tableConv : ℕ → Prop)` — the convention itself is [3]/MovesS's export,
threaded as a parameter, so the agreement is a typed claim, not prose. (e1)'s
compatibility with (a6) is typed: states carry defining reads, transported
letter-for-letter through `readDict` (`stateDict_compat`).

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
  axiomatized here): `REL1` (+ its `REL1Clauses` fields and `REL1b`), `REL2b`,
  `REL2e.massEqEntry` (e3), `REL2e.determines` (e5), `REL2e.e4agrees` +
  `firstIdxCandidate` (e4), `EQ1`, `EQ2law`, `EQ3`, `SIBOdelta`.
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
- PROVABLE NOW (the only proof burden): R2–R6, R20, R23.

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
Structures whose inhabitation IS the obligation (`REL2a`, `REL2d`, `REL2e`,
`BoxVol`, `ReBased`, `TowerData`) get `#check` type-correctness elaborations ONLY —
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

/-- `δ_j := δ·δ_j^rel` — ABSOLUTE accumulated residue degree; target base O_{δ_j}. -/
def Setting.δabs (S : Setting) : ℕ+ := S.δ * S.δrel
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
  menu : ℕ+ → Finset Letter               -- the realized menu over O_δ
  menuNe : ∀ δ, (menu δ).Nonempty

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
  alpha : ∀ δ x, Set (Carrier δ x)        -- 𝔸_δ: the attainable additive span
  alpha_zero : ∀ δ x, (0 : Carrier δ x) ∈ alpha δ x
  alpha_add : ∀ δ x, ∀ a ∈ alpha δ x, ∀ b ∈ alpha δ x, a + b ∈ alpha δ x
  aDim : ℕ+ → Pos → ℕ                     -- a_δ: F_p-additive-span dimension
  card_eq : ∀ δ x, Nat.card (alpha δ x) = p ^ aDim δ x
  posLetter : ℕ+ → Pos → Sp.Letter        -- the realized species letter (owed dictionary, typed)

/-- δ-STABLE-SPECIES position (rev-4 comparison-domain pin), DEFINED: the species
letter persists under re-basing. Split positions fail this and are OUT-OF-DOMAIN
(the F₉ instance recombines across new branches — "REL.2/(SIB) territory"). -/
def AlphabetData.Stable {Sp} (AD : AlphabetData p Sp) (δ : ℕ+) (x : AD.Pos) : Prop :=
  AD.posLetter δ x = AD.posLetter 1 x

/-- **(EQ-2) the a_δ = δ·a law ON THE PINNED PER-POSITION-CLASS DOMAIN** [OPEN,
REL.1-conditional]: "at a fixed shape position WHOSE SPECIES IS δ-STABLE …
the re-based piece maps are F_δ-linear and a_δ = δ·a". -/
def EQ2law {Sp} (AD : AlphabetData p Sp) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x → AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x

/-- (EQ-2)'s displayed consequence "|𝔸_δ| = q_δ^a = |𝔸|^δ" on the pinned domain —
PROVABLE (R20) from `card_eq` + hypothesized `EQ2law` by `pow_mul`. -/
theorem EQ2law_card {Sp} (AD : AlphabetData p Sp) (h : EQ2law p AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AD.Stable δ x →
      Nat.card (AD.alpha δ x) = qq p δ ^ AD.aDim 1 x ∧
      Nat.card (AD.alpha δ x) = Nat.card (AD.alpha 1 x) ^ (δ : ℕ) := sorry

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
  pinnedIn : (H : C.Hist) → Frame H → C.Locus H → Finset (Fin (mOf H))  -- constrained digits
  zcStat : (H : C.Hist) → Frame H → C.Locus H → ℤ            -- C.1.5's (ZC) statistic
  lines : (H : C.Hist) → ℕ → Line         -- base-free floor lines (MovesC, D8)
  interiorEnd : C.Hist → ℕ
  /-- LST carriers (FF1): absolute height ht(b,l) = l + off(b), block (slot-
  coefficient) assignment, per-coordinate and per-block floors, factor-interior
  blocks, the engine's floor downset, and the engine's slot-coefficient weight. -/
  ht : (H : C.Hist) → Fin (mOf H) → ℚ
  blkOf : (H : C.Hist) → Fin (mOf H) → ℕ
  floorC : (H : C.Hist) → Fin (mOf H) → ℚ
  floorB : (H : C.Hist) → ℕ → ℚ
  interiorB : (H : C.Hist) → ℕ → Prop
  floorSet : (H : C.Hist) → ℕ → Set (Fin (mOf H))
  wSlot : (H : C.Hist) → ℕ → (Fin (mOf H) → ↥(Fsub p δ)) → WithTop ℚ

/-- `#{ f mod p^N ∈ S(H, Z) }` — the (REL.1-b) LHS, DEFINED from in-corpus
vocabulary (FF2 repair: kills the free-count instances): the number of level-N
cylinder classes meeting the classifier locus. For N ≥ N(H,Z) these are exactly
the level-N residue points of S(H,Z). -/
noncomputable def ReBased.count {Sp AD δ n} (K : ReBased p Sp AD δ n)
    (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ) : ℕ :=
  Nat.card {W : Set (Fin n → ↥(O p δ)) // ∃ f ∈ K.SHZ H Z, W = cyl p δ N f}

/-- **The REL.1 clause ledger, TYPED (findings 3/5 repair).** Ten named fields =
the note's clause list "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b) with
C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM"; each typed over the actual
re-based objects; contents = the future re-scoping pass's theorems ("MUTATIS
MUTANDIS, NOT verbatim … RECONSTRUCTED over F_δ"). C(b) is `REL1b` below. -/
structure REL1Clauses (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop where
  /-- §A: base tower shape over F_δ (φ̄ monic irr, F₁ = F_δ[x]/(φ̄)). -/
  secA : ∀ H, (K.tower H).BaseLaws
  /-- §B1: the typable stage-carrier residue; graded internals (R0-tower)-fenced. -/
  secB1 : ∀ H, (K.tower H).StageCarrierLaws
  /-- §B2-DEF: the D.0 climb, residual factors computed OVER THE NEW BASE. -/
  secB2def : ∀ H, (K.tower H).ClimbLaws
  /-- Theorem C(a): classifier locus = jet-preimage of the digit-system locus
  (MovesC thmC_a's shape, re-based). -/
  thmCa : ∀ H Z, K.SHZ H Z =
    (fun f => K.jet H f) ⁻¹' {x | (K.digitLocus H Z).IsSolution x}
  /-- C.0.5 + PIN-WELLDEF: transports unitriangular ("ring-polynomial identities in
  strictly ≺-earlier coefficients"); pin statistics frame-invariant — BOTH legs of
  "cardinality-AND-STATUS statistics" (FF3): the pinned-set cardinality AND the
  multiset of per-digit alphabet exponents over the pinned set. -/
  c05PinWelldef : ∀ H F F', IsUnitriangular (K.T H F F') ∧
    ∀ Z, (K.pinnedIn H F Z).card = (K.pinnedIn H F' Z).card ∧
      (K.pinnedIn H F Z).val.map (K.aDim H) = (K.pinnedIn H F' Z).val.map (K.aDim H)
  /-- C.1: "each constrained digit contributing the factor |𝔸_δ|⁻¹ of its
  ATTAINABLE alphabet" — the locus mass is the per-pinned-digit product. -/
  c1 : ∀ H (F : K.Frame H) Z, K.C.V.vol (K.C.locusEvent H Z) =
    ∏ i ∈ K.pinnedIn H F Z, ((p : ℚ) ^ (K.aDim H i))⁻¹
  /-- C.1.5's (ZC) invariant: the statistic is transport/frame-invariant. -/
  c15ZC : ∀ H F F' Z, K.zcStat H F Z = K.zcStat H F' Z
  /-- LST = Lemma LST, level-set scale-typing (§C display, MOVES 3728 — the FF1
  repair; the rev-2 stabilization reading was REFUTED: non-LST content and entailed
  by REL1b). The three legs' typable residue: (i) TYPING — the engine's slot-
  coefficient weight is the iterated slot-minimum of the absolute height over the
  block's nonzero digits ("w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y ≠ 0}");
  (ii) FLOOR CONSTANCY ON THE INTERIOR — the per-coordinate floor is the block
  floor ("F_i(b) = old_i(slot(b)): ht-constant on each current block");
  (iii) SELECTION — the engine's floor downset IS the ht-downset {ht ≤ F_i}, hence
  the ENTIRE level set at γ' > floor avoids it ("lies strictly above the floor
  downset"). The K1-chain/in_γ graded internals stay §C-side (same fence as §B1's). -/
  lst : ∀ (H : K.C.Hist),
    (∀ (B : ℕ) (x : Fin (K.mOf H) → ↥(Fsub p δ)),
      K.wSlot H B x = (Finset.univ.filter fun i =>
        K.blkOf H i = B ∧ x i ≠ 0).inf fun i => ((K.ht H i : ℚ) : WithTop ℚ)) ∧
    (∀ i, K.interiorB H (K.blkOf H i) → K.floorC H i = K.floorB H (K.blkOf H i)) ∧
    (∀ B, K.interiorB H B →
      K.floorSet H B = {i | K.blkOf H i = B ∧ K.ht H i ≤ K.floorB H B} ∧
      ∀ (γ' : ℚ), K.floorB H B < γ' →
        ∀ i, K.blkOf H i = B → K.ht H i = γ' → i ∉ K.floorSet H B)
  /-- TYP, walk item (i)'s RETYPING verbatim: "per-digit ADDITIVE on O_δ-digit
  blocks" (additivity is all TYP(b) consumes; F_δ-linearity stays EXPECTED, walked). -/
  typ : ∀ H (i : Fin (K.mOf H)) (f g : Fin n → ↥(O p δ)),
    K.jet H (f + g) i = K.jet H f i + K.jet H g i
  /-- DOM: base-free floor domination, MovesC's `DomData` verbatim ("valuation
  geometry … carries over as written"). -/
  dom : ∀ H, ∀ i ≤ K.kIdx H, DomData (K.lines H) i (K.interiorEnd H)

/-- (REL.1-b), typed verbatim through the pinned BoxVol, LHS the DEFINED count
(FF2): "#{ f mod p^N ∈ S(H, Z) } = q_δ^{nN} · ∏_{i=0}^{k} vol(E_fresh(ν_i)) ·
vol(Z) for every N ≥ N(H, Z)". -/
def REL1b (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  ∀ (H : K.C.Hist) (Z : K.C.Locus H) (N : ℕ), K.C.Nmin H Z ≤ N →
    (K.count H Z N : ℚ) = (qq p δ : ℚ) ^ (n * N) *
      ((∏ i ∈ Finset.range (K.C.kIdx H + 1), K.C.V.vol (K.C.freshEvent H i)) *
        K.C.V.vol (K.C.locusEvent H Z))

/-- **(REL.1), the Prop-family over δ** [OPEN KERNEL — "a NEW THEOREM with its own
verification passes"]. Parameterized by the carrier package the pass must supply;
consumers hypothesize it per instance, ABSOLUTE index displayed per site. -/
def REL1 (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (δ : ℕ+) (n : ℕ) (K : ReBased p Sp AD δ n) : Prop :=
  REL1Clauses p Sp AD δ n K ∧ REL1b p Sp AD δ n K
```

```lean
/-! ## REL.2 (file Rel2.lean; units R14–R17) -/

/-- **(REL.2a) COORDINATE IDENTIFICATION — the six-item deliverables checklist**
["nothing short of all six items is '(a) stated'"]. Findings 6/7 repairs: nonempty
frame/read carriers; `readDict` letter-for-letter (injective + species-letter-
preserving through `Sp`); the (a3) Teichmüller pin is now a FIELD (`teich_pin`), so
every inhabitant carries the convention. Inhabitation story: the future (a)-pass. -/
structure REL2a (S : Setting p) (Sp : SpeciesSyntax) where
  /-- (a2) integrality of d_j^rel := d_j/δ_j^rel — "part of the obligation …
  EXPECTED from the tower data, walked in (a)'s pass" (E·F ∣ d_j route EXPECTED only). -/
  drel_dvd : (S.δrel : ℕ) ∣ (S.d : ℕ)
  drel_pos : 0 < (S.d : ℕ) / (S.δrel : ℕ)
  /-- (a1) DOMAIN: the free base coordinates (ℓ, i) — infinitely many (Σ_c fixes
  finitely many digits; the continuation is a full sub-box). -/
  freeCoords : Set (ℕ × ℕ)
  freeCoords_inf : freeCoords.Infinite
  /-- (a1) the identification with the "measurable product of O_δ-digit spaces"
  (one F_δ-valued digit per free coordinate — (R0-box)'s ATOM, never unpacked). -/
  domIdent : S.Cont ≃ (freeCoords → ↥(Fsub p S.δ))
  /-- (a1) MEASURABILITY (FF5(i)): the product-side event algebra — finite-
  coordinate digit cylinders present — and the identification is event-algebra-
  compatible ("as a MEASURABLE product" was previously a bare Equiv). -/
  prodEvents : Set (Set (freeCoords → ↥(Fsub p S.δ)))
  prodCyl_mem : ∀ (E : Finset (ℕ × ℕ)) (v : (ℕ × ℕ) → ↥(Fsub p S.δ)),
    {x | ∀ c : freeCoords, (c : ℕ × ℕ) ∈ E → x c = v c} ∈ prodEvents
  domIdent_meas : ∀ W, W ∈ prodEvents ↔ (fun f => domIdent f) ⁻¹' W ∈ S.AmbEvents
  /-- (a3) the named F_{δ_j} ↪ (tower residue field) embedding. -/
  TowerRes : Type
  [towerResField : Field TowerRes]
  embed : ↥(Fsub p S.δabs) →+* TowerRes
  /-- (a3) the canonical-lift convention — datum + PIN AS A FIELD (finding 7):
  agreement with Mathlib's Teichmüller representative in W(F̄_p). -/
  teich : ↥(Fsub p S.δabs) → ↥(O p S.δabs)
  teich_pin : ∀ x, ((teich x : ↥(O p S.δabs)) : Wbar p)
    = WittVector.teichmuller p (x : Kbar p)
  /-- (a4) FORMULA: the map Θ_j itself. -/
  Θ : (freeCoords → ↥(Fsub p S.δ)) → (Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs))
  /-- (a5) FRAME COMPATIBILITY: commutation with C.0.5's UNITRIANGULAR transports;
  nonempty transport family (the identity frame change exists). FF7's anchor: both
  transport families carry the unitriangularity law — the offset added at a
  coordinate depends only on strictly ≺-earlier coordinates (C.0's order on the
  free (ℓ, i)-coordinates via MovesC's `CoordPrec`; the Fin-order on the target's
  C.0-order digit coordinates) — so `frame_compat` is commutation with C.0.5-shaped
  transports, not with arbitrary bijections. -/
  FrameIdx : Type
  frameIdxNe : Nonempty FrameIdx
  ambT : FrameIdx → ((freeCoords → ↥(Fsub p S.δ)) ≃ (freeCoords → ↥(Fsub p S.δ)))
  tgtT : FrameIdx → ((Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs)) ≃
                     (Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs)))
  ambT_unitri : ∀ (i : FrameIdx) (x y : freeCoords → ↥(Fsub p S.δ)) (c : freeCoords),
    (∀ c' : freeCoords, CoordPrec (c' : ℕ × ℕ) (c : ℕ × ℕ) → x c' = y c') →
    ambT i x c - x c = ambT i y c - y c
  tgtT_unitri : ∀ (i : FrameIdx)
      (x y : Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs))
      (j : Fin ((S.d : ℕ) / (S.δrel : ℕ))),
    (∀ j' < j, x j' = y j') → tgtT i x j - x j = tgtT i y j - y j
  frame_compat : ∀ (i : FrameIdx) x, Θ (ambT i x) = tgtT i (Θ x)
  /-- (a6) READ DICTIONARY, letter-for-letter (finding 6): injective, and each
  read's SPECIES LETTER is preserved ((EQ-1)'s dictionary); reads nonempty (the
  branch's continuation has its defining read). Residue-datum fields are
  RECONSTRUCTED, not included (R0-reads' no-monotonicity fence). -/
  AmbRead : Type
  ambReadNe : Nonempty AmbRead
  TgtRead : Type
  readDict : AmbRead → TgtRead
  readDict_inj : Function.Injective readDict
  ambLetter : AmbRead → Sp.Letter
  tgtLetter : TgtRead → Sp.Letter
  readDict_letter : ∀ r, tgtLetter (readDict r) = ambLetter r

/-- (a2)'s target degree d_j^rel, named. -/
def REL2a.dRel {S : Setting p} {Sp} (_A : REL2a p S Sp) : ℕ := (S.d : ℕ) / (S.δrel : ℕ)

/-- **(REL.2b) NORMALIZATION / JACOBIAN** [OPEN KERNEL]: "for every REL.1-measurable
continuation event W over O_{δ_j} (digit cylinders generate — V's `cyl_mem`),
μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W)", with the "only for cells with μ(Σ_c) > 0"
proviso as guard. Non-vacuous: `V.events` contains univ and every cylinder, and
`V.vol` is cylinder-pinned. FF5(ii): the Θ-pullback of every event is required IN
the ambient event algebra — the Θ-measurability half of "the PUSHFORWARD of the
conditional continuation measure … IS the normalized O_{δ_j}-box measure". -/
def REL2b (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs A.dRel) : Prop :=
  0 < S.cellMass →
    ∀ W ∈ V.events,
      (fun f => A.Θ (A.domIdent f)) ⁻¹' W ∈ S.AmbEvents ∧
      S.condMass ((fun f => A.Θ (A.domIdent f)) ⁻¹' W) = V.vol W

/-- (b) WITH ITS REL.1 CONDITIONALITY TYPED: the target measure IS the REL.1
theory's (`RB.C.V`), and REL.1 at (δ_j, d_j^rel) rides as an explicit conjunct —
"EVERY consumer below is conditional on REL.1, displayed per site". -/
def REL2b_linked (S : Setting p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (A : REL2a p S Sp) (RB : ReBased p Sp AD S.δabs A.dRel) : Prop :=
  REL1 p Sp AD S.δabs A.dRel RB ∧ REL2b p S Sp A RB.C.V

/-- **(EQ-3) CONDITIONAL MASSES TRANSPORTED** — "REL.2(b) verbatim … no weaker
reading (bijection-only, or level-matching without normalization) counts."
(Alias inherits the finding-9 repair.) -/
abbrev EQ3 (S : Setting p) (Sp : SpeciesSyntax) (A : REL2a p S Sp)
    (V : BoxVol p S.δabs A.dRel) : Prop := REL2b p S Sp A V
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
  tgtTcan : (Fin A.dRel → ↥(O p S.δabs)) → TgtTree
  nodeCorr : AmbTree → TgtTree            -- the SPECIFIED correspondence
  /-- "The square commutes for every f ∈ Σ_c." -/
  square : ∀ f : S.Cont, nodeCorr (ambTcan f) = tgtTcan (A.Θ (A.domIdent f))
  /-- node-data content of the correspondence: species word preserved … -/
  ambWord : AmbTree → List Sp.Letter
  tgtWord : TgtTree → List Sp.Letter
  corr_word : ∀ t, tgtWord (nodeCorr t) = ambWord t
  /-- … reads transported via (a6)'s dictionary … -/
  ambReads : AmbTree → List A.AmbRead
  tgtReads : TgtTree → List A.TgtRead
  corr_reads : ∀ t, tgtReads (nodeCorr t) = (ambReads t).map A.readDict
  /-- … τ-verdicts preserved … -/
  ambVerdict : AmbTree → List Bool
  tgtVerdict : TgtTree → List Bool
  corr_verdict : ∀ t, tgtVerdict (nodeCorr t) = ambVerdict t
  /-- … and (EQ-2)'s alphabets: each target read sits at an `AD` position class. -/
  posOf : A.TgtRead → AD.Pos
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
  stateReadsAmb : S.StateIdx → List A.AmbRead
  stateReadsRel : RelState → List A.TgtRead
  stateDict_compat : ∀ s, stateReadsRel (stateDict s) = (stateReadsAmb s).map A.readDict
  /-- [3]'s table, in [3]'s own keying: (first index, state, argument) ↦ entry. -/
  β : ℕ → S.StateIdx → ℕ → ℚ
  /-- (e4) the first index e_j, FROM b_j's DATA — one value per branch (finding 13). -/
  entryFirst : ℕ
  /-- the prescriptions [3]'s entry at this key consumes (nonempty deliverable). -/
  consumed : Set S.PTree
  consumedNe : consumed.Nonempty

/-- (e4)'s agreement with [3]'s table convention, TYPED against the convention as
a parameter ([3]/MovesS's export — D5): a typed claim, not prose. -/
def REL2e.e4agrees {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (tableConv : ℕ → Prop) : Prop := tableConv E.entryFirst
/-- (e4)'s CANDIDATE ["candidate: (a2)'s O_{δ_j}-degree d_j^rel — owed, not
assumed"]: named, hypothesis-side, asserted nowhere. -/
def REL2e.firstIdxCandidate {S Sp AD A D} (E : REL2e p S Sp AD A D) : Prop :=
  E.entryFirst = A.dRel
/-- (e5) first disjunct: "the entry's indices must DETERMINE the prescribed subtree
T_j" — the consumed class at this key is a singleton. The second disjunct
(re-keying) is a statement-fence event (D5). -/
def REL2e.determines {S Sp AD A D} (E : REL2e p S Sp AD A D) : Prop :=
  ∀ T ∈ E.consumed, ∀ T' ∈ E.consumed, T = T'
/-- (e3) MASS = ENTRY, stated GIVEN (e5) (the note: without (e5) the equation is
ill-typed): β_{e_j, τ_j(c)}(p^{δ_j}) IS **the REL.1 mass** — FF6: the _linked
pattern applied, so the vol is `RB.C.V` of a REL1-hypothesized package, never an
arbitrary BoxVol ("IS the REL.1 mass vol_{O_{δ_j}}{…}" — the note names the
theory's measure, not a measure). FF5(iii): the realization event is required IN
`RB.C.V.events`, so V's measure laws bind at it. -/
def REL2e.massEqEntry {S Sp AD A D} (E : REL2e p S Sp AD A D)
    (RB : ReBased p Sp AD S.δabs A.dRel) : Prop :=
  REL1 p Sp AD S.δabs A.dRel RB ∧ E.determines p ∧ ∀ T ∈ E.consumed,
    {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)} ∈ RB.C.V.events ∧
    E.β E.entryFirst S.τ (S.βarg p) =
      RB.C.V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}
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
`RB.C.V.events` (FF5(iii)) so the REL.1 measure laws bind there. RECURSION CLAUSE
= `F.desc*` (family closure) + `O_chain` (the literal subring chain TREE-EXP's
induction consumes). -/
def SIBOdelta (F : SettingsFamily p) : Prop :=
  ∀ S ∈ F.mem, 0 < S.cellMass →
    ∃ (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) (A : REL2a p S Sp)
      (D : REL2d p S Sp AD A) (RB : ReBased p Sp AD S.δabs A.dRel),
      REL1 p Sp AD S.δabs A.dRel RB ∧
      REL2b p S Sp A RB.C.V ∧
      ∀ T : S.PTree,
        {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)} ∈ RB.C.V.events ∧
        S.SEvent T = (fun f => A.Θ (A.domIdent f)) ⁻¹'
            {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)} ∧
        S.condMass (S.SEvent T) =
          RB.C.V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}

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
-- Carrier instances (honest trivial cases only):
--   example : Setting 2 := ⟨1, 1, 1, PUnit, ⟨⟨⟩⟩, Set.univ, trivial, …, 0, le_rfl,
--     zero_le_one, fun _ => 0, …⟩   -- a cellMass = 0 cell: proviso-excluded by
--                                   -- every display's guard, honest as a carrier
--   example : SettingsFamily 2 := singleton family on the above, desc _ _ _ := ∅
--   example : SpeciesSyntax := ⟨PUnit, fun _ => (1,1,1,1), fun _ => {PUnit.unit}, …⟩
--   example : AlphabetData 2 Sp₀ := ⟨PUnit, ⟨⟨⟩⟩, fun _ _ => PUnit, …, {0}, …⟩
--     (card_eq: Nat.card {0} = 1 = 2^0 with aDim ≡ 0 — a degenerate but LAWFUL
--      alphabet; the EQ2law statement about it is not asserted anywhere)
-- Obligation/deliverable structures: #check only (inhabitation = the pass):
--   #check @REL1  #check @REL1Clauses  #check @REL2a  #check @REL2b_linked
--   #check @REL2d #check @REL2e.massEqEntry  #check @SIBOdelta  #check @BoxVol
end Elab
end MovesR
```

SKELETON STATUS: NORMATIVE FOR CONTENT, not character-exact — E-phase fixes syntax
(instance-field bracketing, `Fin 0`-index forms, implicit-argument threading,
namespace qualification for `DigitSystem`/`IsUnitriangular`/`Line`/`DomData`)
WITHOUT changing any quantifier, equality, guard, or field list; anything beyond
syntax re-enters the audit loop (statement fence).

## 2. Unit specs (23 units)

Files: `Base.lean` R1–R6 · `Interface.lean` R7–R8 · `Eq.lean` R18–R21 (carriers
consumed by Rel2) · `Rel1.lean` R9–R13 · `Rel2.lean` R14–R17 · `Sib.lean` R22–R23 ·
`Defs.lean` re-export shim. Import order: Base → Interface → Eq → Rel1 → Rel2 → Sib.
Acceptance per def-unit: definitions land verbatim-from-skeleton + its D9
elaboration compiles.

**R1 base_defs** · Base.lean · defs `Kbar, Wbar, Fsub, O, qq, relExt, cyl` + `#check`s.
moves_ref: "Fix an algebraic closure F̄_p once; F_m is THE subfield of order p^m and
O_m := W(F_m) ⊂ W(F̄_p)." · deps: — · sketch: D1 route; cyl via Witt-coefficient
truncation (perfect residue field) · easy · hyp_fields: none (concrete).

**R2 Fsub_le** · `d ∣ m → Fsub p d ≤ Fsub p m` · moves_ref: "Nested base changes
then compose LITERALLY as subrings — O_δ ⊂ O_{δδ′}". · deps R1 · sketch: x^{p^d}=x ⇒
x^{p^{dk}}=x by pow-iteration · medium · PROVED-class.

**R3 O_le** · `d ∣ m → O p d ≤ O p m` · moves_ref: as R2 (subring layer). · deps R1,
R2 · sketch: local `map_comp` by `WittVector.ext`+`map_coeff`; ranges nest via
`Subfield.inclusion` · medium · PROVED-class.

**R4 relExt_comp** · `relExt_eq` (rfl), `relExt_relExt` (mul_assoc), `O_le_relExt` ·
moves_ref: "'(O_δ)_{δ′} = O_{δδ′}' is bookkeeping inside W(F̄_p), never an
identification up to isomorphism." · deps R1, R3 · easy · PROVED-class (the
charge's definitional lemma).

**R5 qq_mul + βarg_eq** · `qq p (m*δ') = qq p m ^ δ'`; `S.βarg = qq p S.δ ^ S.δrel` ·
moves_ref: "pool size q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}" + (e2). · deps R1 (βarg_eq
also R7) · sketch: pow_mul · easy · PROVED-class.

**R6 Fsub_card [NEW — finding 1]** · `Nat.card ↥(Fsub p m) = p ^ (m : ℕ)` ·
moves_ref: "F_m is THE subfield of order p^m". · deps R1 · sketch: fixed points of
Frob^m = roots of the separable X^{p^m} − X, which splits in F̄_p; count roots
(`galois_poly_separable`, `Polynomial.card_roots_le_degree` + separability for
equality) · hard · PROVED-class (wave-3 fleet; statement frozen now).

**R7 Setting [finding 2 repaired]** · structure + `δabs` + `βarg` + carrier example.
moves_ref: "Ambient base O_δ …, a realized prefix η, state cylinder Σ (frame Ψ_η),
digit cell c of Σ, and a branch b_j … δ_j := δ·δ_j^rel, the ABSOLUTE accumulated
residue degree." · deps R1 · sketch: opaque carriers + REALIZED-MEASURE LAWS
(nonneg, ≤ 1, event algebra, additivity, conditional normalization guarded by
μ(Σ_c) > 0); nonempty Cont/PTree · medium · hyp_fields: none asserted — the law
fields are carrier well-formedness, the note's own.

**R8 SettingsFamily [findings 19/20 repaired]** · structure + singleton example.
moves_ref: "simultaneously over every unramified O_δ that arises (all δ ≥ 1 in one
statement)… the same typing applies at every descendant branching cell inside T_j,
ABSOLUTE indices throughout." · deps R7 · sketch: nonempty + root δ=1 + typed
descent closure (`desc_sub`, `desc_amb : S'.δ = S.δabs`) · easy-medium ·
hyp_fields: none (carrier; closure fields are the recursion clause's typing).

**R9 TowerData + Laws [finding 3 part]** · structure + BaseLaws/ClimbLaws/
StageCarrierLaws + `#check`. moves_ref: "F₁ := F_δ[x]/(φ̄) … the tower F_{k+1} =
F_k[z]/(ψ_k) climbs by residual factors COMPUTED OVER THE NEW BASE — built afresh,
NOT by scalar-extending." · deps R1 · sketch: AdjoinRoot presentations; laws split
§A/§B1/§B2-DEF; §B1 = typable residue + (R0-tower) fence in docstring · medium ·
hyp_fields: the three Law bundles (obligations, consumed by R11).

**R10 BoxVol [finding 8 repaired]** · structure + `#check` (no instance — D9).
moves_ref: "(R0-box) … normalized Haar measure vol_{O_δ}(O_δ^n) = 1 … f mod p^N
ranges over q_δ^{nN} residue points." · deps R1 · sketch: event algebra containing
all cylinders; nonneg/additive/normalized content; `vol_cyl` pins cylinder masses
to q^{-nN} · medium · hyp_fields: all law fields (well-formedness of the note's
measure; inhabitation = Haar, the pass's).

**R11 REL1Counting [FF2 repaired]** · structure + `#check`. moves_ref:
"(REL.1-b) #{ f mod p^N ∈ S(H, Z) } = q_δ^{nN} · ∏_{i=0}^{k} vol(E_fresh(ν_i)) ·
vol(Z) for every N ≥ N(H, Z)." · deps R10 · sketch: fixed degree n; nonempty
Hist/per-H Locus; fresh/locus events IN V.events; NO count field — the LHS is
`ReBased.count`, DEFINED (R12) · medium · hyp_fields: none asserted (carrier).

**R12 ReBased + count + REL1Clauses [FF1/FF2/FF3/FF4 repaired]** · structures +
def + `#check`. moves_ref: "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b)
with C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM — hold over O_δ … MUTATIS
MUTANDIS" + Lemma LST's display (MOVES 3728, the FF1 source). · deps R9, R10, R11,
R18, R19 (+ D8 imports) · sketch: ReBased parameterized by (Sp, AD) with
`posOfDigit`/`aDim_eq` tying c1's exponents to (EQ-2)'s data (FF4) and the LST
carriers (ht/blkOf/floors/interior/floorSet/wSlot); `ReBased.count` DEFINED as the
level-N cylinder-class count of SHZ (FF2 — the free-count instance family is
dead); ten TYPED clause fields — tower laws, thmCa jet-preimage, C.0.5 unitri +
pin statistics BOTH legs (cardinality AND the aDim-multiset — FF3), |𝔸_δ|⁻¹
product, (ZC) invariance, LST's three legs (slot-min TYPING, interior FLOOR
CONSTANCY, floor-downset SELECTION — FF1), TYP additivity, DomData · hard (the
corpus's largest unit — split at E-phase into ReBased/REL1Clauses files if
elaboration drags) · hyp_fields: every clause field (open; the pass's theorems).

**R13 REL1b + REL1** · defs + `#check`. moves_ref: "STATUS: a NEW THEOREM with its
own verification passes — not a corollary, not 'by inspection'." · deps R12 ·
sketch: REL1 := REL1Clauses ∧ REL1b, over (Sp, AD)-parameterized carriers, LHS the
DEFINED count — REL1b is now a counting fact about the classifier locus (FF2) ·
easy · hyp_fields: REL1 (THE open kernel; never instantiated here).

**R14 REL2a [FF5(i)/FF7 repaired]** · structure + `dRel` + `#check`. moves_ref:
"(a) is now a DELIVERABLES CHECKLIST, and nothing short of all six items is '(a)
stated' … (a1) … as a MEASURABLE product of O_δ-digit spaces … (a5) … C.0.5's
unitriangular transports." · deps R1, R7, R18 (+ D8 `CoordPrec`) · sketch: six
field-blocks; NONEMPTY FrameIdx/AmbRead; readDict injective + letter-preserving;
`teich_pin` a FIELD; freeCoords infinite; (a1) now carries `prodEvents` +
digit-cylinder anchor + `domIdent_meas` (the measurability half — FF5(i)); (a5)
now carries `ambT_unitri`/`tgtT_unitri` (offset depends only on strictly ≺-earlier
coordinates, C.0's order — the C.0.5 anchor, FF7) · hard (largest structure) ·
hyp_fields: none asserted; the INHABITANT is (a)'s deliverable (#check per D9).

**R15 REL2b + REL2b_linked + EQ3 [FF5(ii) repaired]** · defs + `#check`.
moves_ref: "for every REL.1-measurable continuation event W over O_{δ_j} (digit
cylinders generate), μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W) … the pushforward of
the conditional continuation measure under Θ_j IS the normalized O_{δ_j}-box
measure" + "(EQ-3) … REL.2(b) verbatim". · deps R13, R14 · sketch: guard
0 < cellMass; V.events cylinder-populated; NEW conjunct: Θ-pullback ∈ AmbEvents
(the pushforward reading's measurability half — FF5(ii)); `REL2b_linked` conjoins
REL1 at (δ_j, d_rel) over the (Sp, AD)-parameterized ReBased; EQ3 aliases the
repaired REL2b · easy-medium · hyp_fields: REL2b (OPEN KERNEL = (EQ-3)); REL1
(in _linked).

**R16 REL2d [findings 11/12 repaired]** · structure + `#check`. moves_ref: "a
displayed COMMUTATIVE SQUARE — vertices … — with horizontal maps Θ_j ((a4)) and a
SPECIFIED node-data correspondence (species word, node datum fields, τ-verdicts,
via (a6)'s dictionary + (EQ-2)'s alphabets)." · deps R14, R18, R19 · sketch:
square + corr_word/corr_reads/corr_verdict (the correspondence SPECIFIED, junk
nodeCorr excluded) + posOf into AD (EQ-2 wiring); (a3) policy via A.teich_pin;
TgtSub/subtreeCorr/TgtRealizes for (SIB-Oδ)'s typing · hard · hyp_fields:
inhabitant = (d)'s deliverable; `square`+corr fields are its displays.

**R17 REL2e [FF5(iii)/FF6 repaired]** · structure + e4agrees/firstIdxCandidate/
determines/massEqEntry + `#check`. moves_ref: "(e1) STATE-INDEX CORRESPONDENCE …
(e2) DEGREE CONVENTION … (e3) MASS = ENTRY — the displayed equation that [3]'s
table entry β_{e_j, τ_j(c)}(p^{δ_j}) IS the REL.1 mass … (e4) FIRST-INDEX
DICTIONARY … (e5) SUBTREE/OUTCOME TYPING." · deps R5, R13, R14, R16 · sketch:
entryFirst FIXED; `consumed` nonempty; stateDict_compat types (e1)↔(a6); e4agrees
takes [3]'s convention as parameter; massEqEntry now takes `RB : ReBased` and
conjoins REL1 (the _linked pattern — FF6: THE REL.1 mass, not an arbitrary
BoxVol) plus realization-event ∈ RB.C.V.events (FF5(iii)); re-keying =
statement-fence event (D5) · medium-hard · hyp_fields: massEqEntry (e3, now
REL1-carrying), determines (e5), e4agrees + firstIdxCandidate (e4) — open; data
fields deliverable.

**R18 SpeciesSyntax + EQ1 [finding 15 repaired]** · structure + def + example.
moves_ref: "the species alphabet and menu are the SAME finite syntax over every O_δ
… never the letter set. STATUS: PREDICTED." · deps: — · sketch: Finset menu
(finiteness typed), menuNe, shape = the stage tuple (e,h,g,μ); EQ1 := ∀ δ, menu δ =
menu 1 · easy · hyp_fields: EQ1 (PREDICTED, fenced into REL.1's pass).

**R19 AlphabetData + Stable + EQ2law [findings 16/17 repaired]** · structure + defs
+ degenerate-lawful example. moves_ref: "DEFINITION (unconditional): … the
attainable additive image/span of the RE-BASED slot maps … |𝔸_δ| = p^{a_δ} …
PREDICTION … at a fixed shape position WHOSE SPECIES IS δ-STABLE … a_δ = δ·a." ·
deps R1, R18 · sketch: alphabets as additively-closed subsets of carrier groups
(span typed); card_eq = the unconditional part; posLetter = the owed matching
dictionary AS DATA; Stable DEFINED (letter persistence), Pos nonempty · medium ·
hyp_fields: EQ2law (OPEN, REL.1-conditional, pinned domain).

**R20 EQ2law_card** · theorem (skeleton). moves_ref: "i.e. |𝔸_δ| = q_δ^a = |𝔸|^δ —
whence exponent preservation in base q_δ." · deps R5, R19 · sketch: card_eq +
hypothesized law + pow_mul/pow_right_comm · easy · PROVED-class
(hypothesis-conditional arithmetic; no kernel discharged).

**R21 EQ3 placement** · covered in R15 (alias, same file section); listed for the
ledger's 1:1 clause coverage. moves_ref: "(EQ-3) CONDITIONAL MASSES TRANSPORTED.
REL.2(b) verbatim." · deps R15 · easy · hyp_fields: = REL2b.

**R22 SIBOdelta [FF5(iii) repaired]** · def + `#check`. moves_ref: "(SIB-Oδ)
[FENCED = REL.1 + REL.2(a)+(b)+(d), composed …] … μ( S_j │ Σ_c ) =
vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j }, the right side a
REL.1-theory mass." · deps R8, R13, R14, R15, R16 · sketch: ∀ over the realized
family (nonempty, root, descent-closed), guard 0 < cellMass, ∃-composition WITH
the REL1 conjunct over the (Sp, AD)-parameterized ReBased; per T: realization
event ∈ RB.C.V.events (FF5(iii)) + event-typing + pricing · medium-hard ·
hyp_fields: SIBOdelta (OPEN — the sentence [3t]-COND waits on).

**R23 O_chain** · theorem. moves_ref: "a branch of relative accumulated degree δ″ at
ambient O_{δ_j} targets O_{δ_j·δ″}, literally a subring chain in W(F̄_p)." · deps
R3, R7 · sketch: O_le at δ ∣ δ·δrel and δabs ∣ δabs·δ″ · easy · PROVED-class
(ring half of the recursion clause; family half is R8's closure).

(REL.3: NO UNIT — finding 21, D6. REL.2(c), REL-n4, (R0-tower) bracket: non-units,
D6, unchanged rationale.)

## 3. Audit notes (wave-2 re-audit; budget: exactly one pass)

- FAITHFULNESS ANCHORS: every docstring quotes the rev-5 display it encodes; the
  moves_refs above are the check keys. Only `theorem`s: R2–R6, R20, R23 (base-index
  bookkeeping + the card fact + one hypothesis-conditional pow identity).
- DELIBERATE RESIDUAL WIDENINGS (each recorded): (i) `Setting` absorbs η/Σ_c/b_j
  into carriers-with-laws; the realized quantifier is `SettingsFamily` (supplied by
  the ambient theory; closure typed). (ii) REL.1's clause fields type each clause's
  HEAD SHAPE in §R-LEDGER's own vocabulary — their full §C-level content is the
  re-scoping pass's (the note: the clause list is re-scoped THERE, not here); where
  §R-LEDGER displays nothing (§B1 internals), the field types the typable residue
  and the docstring cites the fence. (iii) (e5)'s second disjunct (re-keying) is a
  statement-fence event, not a Prop disjunct — a satisfiable-by-construction
  disjunct would be vacuous (D5). (iv) WITHDRAWN at REV 3 (FF1): the rev-2 premise
  that LST had no named display was factually wrong — Lemma LST exists (§C, MOVES
  3728, "level-set scale-typing") and `lst` now types its three legs' residue; the
  K1-chain/in_γ graded internals stay §C-side under the §B1-style fence.
  (v) NEW (FF7): free-data relativity — where the ambient engine's objects
  (transports, trees, reads, floors) do not exist in Lean, the corresponding
  deliverable fields are free data constrained ONLY by their typed laws
  (unitriangularity anchors, letter/word/verdict preservation, cylinder pins,
  teich_pin, the floor-downset pin); law-respecting junk remains constructible,
  and D7 now says exactly this. Full pinning = REL.1-pass territory.
- CROSS-NOTE WATCHES INHERITED: (W1) `SEvent`/`TgtRealizes` stay opaque — every
  MovesR statement is neutral to the [1]/[3t] "realizes" pin; the pinned reading
  lands as the supplier's definition at the CL-10 sync, no statement changes.
  (W2) absolute indices enforced by construction (`δabs`, `βarg`, `relExt`).
- PLAN-SYNC FLAG (note R.1): CL-8 owes the (e) leg + the five-count; MovesR carries
  the five-obligation convention ((c) absent by re-homing).
- CONSUMER EDGES: MovesT consumes `SIBOdelta`/`Setting`/`SettingsFamily`/R23;
  MovesS consumes `REL2e` + `βarg_eq` and EXPORTS `tableConv` (e4's parameter);
  MovesU consumes the future REL.3 units (none yet — D6); MovesV cites `REL1`.
  Import direction: those corpora import MovesR, never conversely.

## 4. File map + status ledger

  lean/LeanUrat/MovesR/Base.lean       R1–R6   (defs + 5 provable lemmas + card)
  lean/LeanUrat/MovesR/Interface.lean  R7–R8   (Setting+laws, SettingsFamily)
  lean/LeanUrat/MovesR/Eq.lean         R18–R21 (SpeciesSyntax, AlphabetData, EQ-1/2)
  lean/LeanUrat/MovesR/Rel1.lean       R9–R13  (TowerData, BoxVol, counting, clauses)
  lean/LeanUrat/MovesR/Rel2.lean       R14–R17 ((a), (b)+EQ-3, (d), (e))
  lean/LeanUrat/MovesR/Sib.lean        R22–R23 ((SIB-Oδ), chain)
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

STATUS (2026-07-28): REV 3 WRITTEN — Codex 21/21 + Fable 7/7 repaired. 23 units:
7 provable (R2–R6, R20, R23), 16 statements-only. No axioms; no kernel discharged;
statement fence in force. Next gate: the Codex FINAL confirmation pass, then E-phase.
