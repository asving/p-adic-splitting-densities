# MovesR LEAN BLUEPRINT (2026-07-28) — §R-LEDGER, the statements-only corpus

SOURCE (ground truth): `lean/notes/MOVES_2026-07-24.md` §R-LEDGER, rev 5, DUAL-ACCEPTED
2026-07-27 (Codex pass 6 `RLED_PASS6` + `FABLE_CONFIRM_RLED_REV5`, 0/0 each). The note
DERIVES NOTHING by design ("DERIVED IN THIS NOTE: nothing", R.5) — so MovesR is a
STATEMENTS-ONLY corpus: every obligation lands as a precisely-typed Prop/structure;
the units are definitions + `example` elaboration checks. ZERO proof burden except the
base-index layer (units R2–R5, R17, R20 — small, Mathlib-only, flagged per unit).
Campaign spec: `lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2 unit format.
Files land under `lean/LeanUrat/MovesR/`. No unit asserts, discharges, or weakens any
open kernel: kernels appear ONLY as named Prop definitions that consumers hypothesize.

## 0. Design decisions (recorded per the wave-1 charge)

**(D1) THE WITT-VECTOR BASE LAYER: CONCRETE MATHLIB ROUTE — no axioms, no interface.**
Investigated against the pinned mathlib (4.31.0 toolchain package):
- Mathlib HAS: `WittVector p R` + `WittVector.map (f : R →+* S) : 𝕎 R →+* 𝕎 S`,
  `WittVector.map_injective`, `WittVector.map_coeff`, `WittVector.map_id`
  (`Mathlib/RingTheory/WittVector/Basic.lean`); `WittVector.teichmuller : R →* 𝕎 R`
  (`Teichmuller.lean`); `AlgebraicClosure (ZMod p)`; `RingHom.eqLocusField
  (f g : K →+* L) : Subfield K` (`Algebra/Field/Subfield/Basic.lean:477`);
  `iterateFrobenius : R →+* R` (`Algebra/CharP/Lemmas.lean:327`);
  `Subfield.inclusion (h : S ≤ T) : S →+* T`.
- Mathlib LACKS: any named "finite subfields of F̄_p" lattice, any W(F_q)/unramified-
  extension-of-ℤ_p API, and a `WittVector.map_comp` composition lemma.
- DECISION: build the convention from the pieces. Ambient W(F̄_p) :=
  `WittVector p (AlgebraicClosure (ZMod p))`. `F_m` := the fixed subfield of the m-th
  Frobenius iterate, `RingHom.eqLocusField (iterateFrobenius _ p m) (RingHom.id _)` —
  membership is definitionally `x ^ p ^ m = x`, the standard characterization of THE
  subfield of order p^m. `O_m` := `(WittVector.map (F_m).subtype).range : Subring`.
  Nesting `O_d ≤ O_m` for `d ∣ m` is provable (R2/R3): `Fsub`-monotonicity is a
  `pow`-iteration argument; range-monotonicity follows from `WittVector.map` of
  `Subfield.inclusion` via coefficientwise `map_coeff` + `WittVector.ext` (the missing
  `map_comp` is a 3-line ext lemma, proved locally, offered upstream later).
  The composition law "(O_δ)_{δ′} = O_{δδ′}" (R4): the relative base-change operator is
  DEFINED as `relExt m δ′ := O (m·δ′)` — the note's convention is that the display "is
  bookkeeping inside W(F̄_p), never an identification up to isomorphism", so the law is
  `rfl` at one step and `mul_assoc` under composition, with the SUBSTANTIVE content in
  the inclusion `O m ≤ relExt m δ′` (R3/R4) and the pool-size law `q_{mδ′} = q_m^{δ′}`
  (R5, `pow_mul`). FALLBACK if `iterateFrobenius`'s `ExpChar` instance fights
  elaboration: `(frobenius (Kbar p) p) ^ (m : ℕ)` in the `RingHom`-composition monoid,
  or the raw carrier `{x | x ^ p ^ m = x}` with the three closure obligations proved
  once (still Mathlib-only; still no axiom).
- DELIBERATE NON-UNIT: `Nat.card (F_m) = p^m` (existence/size of the fixed field).
  True, standard, NOT consumed by any statement in this corpus (q_δ is DEFINED
  numerically as `p ^ δ`, matching the note's `q_δ := p^δ`); certifying it needs
  root-counting of `X^{p^m} − X`. Recorded here so nobody mistakes its absence for
  an oversight. If a later corpus consumes it, it becomes a normal medium unit.

**(D2) OPAQUE-INTERFACE DISCIPLINE.** The ambient δ-based MOVES theory does not exist
in Lean (REL.1 is exactly the open kernel saying it exists). Every obligation is typed
over OPAQUE CARRIERS bundled in small structures (`Setting`, `REL1Counting`, `BoxVol`,
…): fields are the exact objects the note's SETTING/display names, nothing finer.
Quantification over settings is PARAMETERIZED (`∀ S ∈ Settings`), the realized family
`Settings` to be supplied by the future ambient theory — this avoids silently
STRENGTHENING statements to junk instances of the abstract types. Trivial-instance
`example`s are ELABORATION CHECKS ONLY (well-formedness), never discharge evidence.

**(D3) MASS CODOMAIN ℚ.** All masses/entries (vol, condMass, β) are `ℚ`: the note's
masses are exact rationals ("sealed rational mass, displayed fractions") and [3]'s β
entries are ℚ(q) evaluated at q = p^{δ_j} ∈ ℕ. No `ℝ≥0∞` anywhere.

**(D4) REL.1 = CLAUSE LEDGER + ONE TYPED DISPLAY.** The note types exactly ONE display,
(REL.1-b); the clause list ("§A, §B1, §B2-DEF, §C … MUTATIS MUTANDIS") is fenced as the
future re-scoping pass's content. Lean form: `REL1ClauseLedger` — ten NAMED Prop-valued
SLOTS (data fields of sort Prop) whose inhabiting Props the re-scoping pass supplies —
plus `REL1b` typed exactly against a counting interface, plus the family
`REL1 p δ C L : Prop := L.Holds ∧ REL1b p δ C`. This is an obligations LEDGER in Lean,
mirroring the note's own genre; it is bookkeeping-precise and claims nothing.

**(D5) THE (e3)/(e5) KEYING.** β is typed with the note's own table shape
`β : ℕ → StateIdx → ℕ → ℚ` (first index, state, argument). The first index is a
deliverable function `entryFirst : PTree → ℕ` of the prescribed subtree (the note's
candidate — constant `A.dRel` — is a separate named Prop `firstIdxCandidate`, owed not
assumed). (e5) is the determination Prop (at fixed cell, `entryFirst` injective on
prescribed subtrees); WITHOUT (e5), (e3)'s ∀T display would force equal masses for
key-sharing subtrees — the exact ill-typing the note flags, here a false instance
rather than a type error, guarded by hypothesizing (e5) alongside (e3). The note's
re-keying escape ("T_j added as an explicit further index") is recorded in R14's
docstring as the alternative if (e5)'s first disjunct fails.

**(D6) NON-UNITS (deliberate, with reasons).**
- REL.2(c): re-homed to [3t]'s (SIB) (plan REV 9); the note "CITES (SIB) and never
  re-states it" — so MovesR contains NO sibling-independence Prop; MovesT owns it.
- Gate REL-n4 (+ spec sheet (g1)–(g7)): a census-side numeric artifact (PARI/W(F₄)
  enumeration), OUTLINED with the runnable spec still OWED in the note; not a Lean
  object. Nothing in this corpus consumes it.
- (R0-tower)'s PREDICTED bracket (value groups/stretches/κ_r unchanged) and (R0-reads)'
  reconstruction prose: fenced as REL.1-pass content, carriers absent — doc-comments
  in Defs only, no Prop (typing them now would invent the very API the pass must walk).
- The (a5)/(a6)/(e1) "displayed per field" compatibility glosses: acceptance-criterion
  prose for the future pass, recorded in docstrings; the DATA fields are typed.

**(D7) HYPOTHESIS vs DELIVERABLE (explicit, per unit below).**
- HYPOTHESES (open kernels; consumers take them as named Prop arguments, NEVER proved
  or axiomatized here): `REL1` (family), `REL2b`, `REL2d.square`'s inhabitation,
  `REL2e.massEqEntry` (e3), `REL2e.determines` (e5), `TeichPinned` (a3's pin),
  `firstIdxCandidate` (e4's candidate), `EQ1`, `EQ2law`, `EQ3`, `SIBOdelta`, `REL3`.
- DELIVERABLES (data a future pass must EXHIBIT; Lean form = structure whose
  INHABITANT is the deliverable): `REL2a` (the six-item (a1)–(a6) checklist),
  `REL2d` (the commutative-square vertices + maps), `REL2e`'s data fields ((e1)
  dictionary, (e4) first index, the β table), `BoxVol`, `SQConsumptionSite`s.
- PROVABLE NOW (the only proof burden): R2, R3, R4, R5, R17, R20.

## 1. Defs skeleton (inline; lands as `lean/LeanUrat/MovesR/Defs.lean` unless split noted)

```lean
import Mathlib
namespace MovesR
/-! # MovesR — §R-LEDGER statements-only corpus (rev 5, dual-accepted).
Obligations ledger in Lean: NOTHING here is derived beyond the base-index layer.
Doc-comments quote the note; (R0-tower)/(R0-reads) prose rides as comments only. -/

/-! ## R0. The base-index convention (note R.1 head; pass-1 crit 7 + gap 8 repair) -/
variable (p : ℕ) [hp : Fact p.Prime]

/-- `F̄_p`, fixed ONCE (the convention's ambient algebraic closure). -/
abbrev Kbar := AlgebraicClosure (ZMod p)
/-- `W(F̄_p)` — every base ring below is a LITERAL subring of this one ring. -/
abbrev Wbar := WittVector p (Kbar p)

/-- `F_m` — THE subfield of `F̄_p` of order `p^m`, pinned as the fixed field of the
m-th Frobenius iterate: membership is definitionally `x ^ p ^ m = x`.
(Size `p^m` itself: deliberate non-unit, see blueprint D1.) -/
def Fsub (m : ℕ+) : Subfield (Kbar p) :=
  RingHom.eqLocusField (iterateFrobenius (Kbar p) p (m : ℕ)) (RingHom.id _)

/-- `O_m := W(F_m) ⊂ W(F̄_p)` — a subring, never an abstract ring: "nested base
changes then compose LITERALLY as subrings … no per-pair embedding choices". -/
def O (m : ℕ+) : Subring (Wbar p) :=
  (WittVector.map (Subfield.subtype (Fsub p m))).range

/-- `q_m := p^m = |F_m|` (numeric definition; the note's `q_δ := p^δ`). -/
def qq (m : ℕ+) : ℕ := p ^ (m : ℕ)

/-- The degree-δ′ unramified base change of `O_m` INSIDE `W(F̄_p)`: by the BASE-INDEX
CONVENTION this IS `O_{m·δ′}` — "'(O_δ)_{δ′} = O_{δδ′}' is bookkeeping inside
W(F̄_p), never an identification up to isomorphism". ABSOLUTE indices. -/
def relExt (m δ' : ℕ+) : Subring (Wbar p) := O p (m * δ')

-- Units R2–R5 (the ONLY proof burden of the corpus, all Mathlib-only):
theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m := sorry        -- R2
theorem O_le {d m : ℕ+} (h : d ∣ m) : O p d ≤ O p m := sorry                 -- R3
theorem relExt_eq (m δ' : ℕ+) : relExt p m δ' = O p (m * δ') := rfl          -- R4
theorem relExt_relExt (m δ' δ'' : ℕ+) :
    relExt p (m * δ') δ'' = relExt p m (δ' * δ'') := by rw [relExt, mul_assoc] -- R4
theorem O_le_relExt (m δ' : ℕ+) : O p m ≤ relExt p m δ' := O_le p ⟨δ', rfl⟩  -- R4
theorem qq_mul (m δ' : ℕ+) : qq p (m * δ') = qq p m ^ (δ' : ℕ) := sorry      -- R5

/-! ## The R.1 SETTING (opaque carriers; quantification parameterized per D2) -/

/-- One instance of the note's SETTING: "Ambient base O_δ (δ = 1 at the root …), a
realized prefix η, state cylinder Σ (frame Ψ_η), digit cell c of Σ, and a branch b_j
of c's branch set (… the (side, ψ)-selection)". η/Σ/c/b_j are ABSORBED into the
opaque carriers; the numeric fields are the note's named quantities. -/
structure Setting where
  /-- ambient ABSOLUTE base index (root instance: δ = 1). -/
  δ : ℕ+
  /-- `δ_j^rel` := product of the residual degrees g down b_j MEASURED OVER F_δ
  ("the whole unramified part absorbed into ONE base change"). -/
  δrel : ℕ+
  /-- `d_j` := the O_δ-degree of b_j's cluster. -/
  d : ℕ+
  /-- OPAQUE: the continuation points of the cell event Σ_c (what b_j's
  continuation reads see). -/
  Cont : Type
  /-- `μ(Σ_c)` — the ambient (unconditional) mass of the cell. -/
  cellMass : ℚ
  /-- `μ( · │ Σ_c )` — the conditional continuation mass, on subsets of `Cont`. -/
  condMass : Set Cont → ℚ
  /-- OPAQUE: prescribed finite subtrees `T_j` for branch b_j. -/
  PTree : Type
  /-- `S_j(T)`: the event that b_j's continuation realizes `T`. The READING of
  "realizes" (rooted-prefix vs truncation-fiber) is (W1)'s duty at §T.3/[1];
  kept OPAQUE here so every MovesR statement is neutral to that pin. -/
  SEvent : PTree → Set Cont
  /-- OPAQUE: [3]/[3t]'s state indices. -/
  StateIdx : Type
  /-- `τ_j(c)`, the state index at cell c. -/
  τ : StateIdx

/-- `δ_j := δ·δ_j^rel` — "the ABSOLUTE accumulated residue degree. The target base
is O_{δ_j} — ABSOLUTE index". -/
def Setting.δabs (S : Setting) : ℕ+ := S.δ * S.δrel

/-- (e2)'s DEGREE CONVENTION, pinned at the definition: "the β-argument is p^{δ_j}
with δ_j ABSOLUTE". The identity `βarg = q_δ^{δ_j^rel}` is R5 + `Setting.δabs`. -/
def Setting.βarg (S : Setting) : ℕ := qq p S.δabs
```

```lean
/-! ## (REL.1) — the re-scoping Prop-family over δ (OPEN KERNEL; blueprint D4) -/

/-- The clause LEDGER of (REL.1): ten named slots, one per accepted clause the note
lists — "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b) with C.0.5/PIN-WELLDEF,
C.1, C.1.5/(ZC), LST, TYP, DOM — hold over O_δ … MUTATIS MUTANDIS, NOT verbatim".
The slots are Prop-valued DATA: the future derivation-grade re-scoping pass supplies
the actual re-based statements (every residue-theoretic object RECONSTRUCTED over
F_δ, never a cardinality substitution). C(b)'s quantitative content is NOT a slot:
it is the typed display `REL1b` below. -/
structure REL1ClauseLedger where
  secA secB1 secB2def thmCa c05PinWelldef c1 c15ZC lst typ dom : Prop

/-- All ten slots hold. -/
def REL1ClauseLedger.Holds (L : REL1ClauseLedger) : Prop :=
  L.secA ∧ L.secB1 ∧ L.secB2def ∧ L.thmCa ∧ L.c05PinWelldef ∧ L.c1 ∧ L.c15ZC ∧
  L.lst ∧ L.typ ∧ L.dom

/-- Counting interface for the ONE display the note fixes, (REL.1-b). Carriers
opaque; signatures exactly the display's: histories H, loci Z, the level-N residue
count `#{f mod p^N ∈ S(H,Z)}`, the threshold N(H,Z), the fresh-band volumes
vol(E_fresh(ν_i)) for i = 0..k, and vol(Z) — "every per-digit alphabet factor
computed over F_δ" is the pass's burden, not typable here. -/
structure REL1Counting (δ : ℕ+) where
  Hist : Type
  Locus : Type
  /-- n, the box degree of H's instance. -/
  deg : Hist → ℕ
  /-- k, the top node index of H. -/
  kIdx : Hist → ℕ
  /-- `#{ f mod p^N ∈ S(H, Z) }`. -/
  count : Hist → Locus → ℕ → ℕ
  /-- `N(H, Z)`, the stabilization threshold. -/
  Nmin : Hist → Locus → ℕ
  /-- `vol(E_fresh(ν_i))` in vol_{O_δ}. -/
  freshVol : Hist → ℕ → ℚ
  /-- `vol(Z)` in vol_{O_δ}. -/
  locusVol : Locus → ℚ

/-- (REL.1-b), typed verbatim: "#{ f mod p^N ∈ S(H, Z) } = q_δ^{nN} · ∏_{i=0}^{k}
vol(E_fresh(ν_i)) · vol(Z)  for every N ≥ N(H, Z)". -/
def REL1b (δ : ℕ+) (C : REL1Counting δ) : Prop :=
  ∀ (H : C.Hist) (Z : C.Locus) (N : ℕ), C.Nmin H Z ≤ N →
    (C.count H Z N : ℚ) =
      (qq p δ : ℚ) ^ (C.deg H * N) *
        (∏ i ∈ Finset.range (C.kIdx H + 1), C.freshVol H i) * C.locusVol Z

/-- **(REL.1) the Prop-family over δ** [OPEN KERNEL — "a NEW THEOREM with its own
verification passes — not a corollary, not 'by inspection'"]. Hypothesis-side only:
no instance is constructed anywhere in MovesR. -/
def REL1 (δ : ℕ+) (C : REL1Counting δ) (L : REL1ClauseLedger) : Prop :=
  L.Holds ∧ REL1b p δ C

/-! ## (REL.2) — the sub-cluster base change: (a), (b), (d), (e) ((c) re-homed, D6) -/

/-- A REL.1-theory box measure over `O_m` on the degree-n coefficient box — the
target-side vol that (b)/(e3) price against. `events` is the REL.1-measurable class
("digit cylinders generate" — the generation claim is REL.1-side, not typed here);
`vol_univ` is the normalization (R0-box: "normalized Haar measure … = 1"). -/
structure BoxVol (m : ℕ+) (n : ℕ) where
  events : Set (Set (Fin n → ↥(O p m)))
  vol : Set (Fin n → ↥(O p m)) → ℚ
  vol_univ : vol Set.univ = 1

/-- **(REL.2a) COORDINATE IDENTIFICATION — the six-item deliverables checklist**
["nothing short of all six items is '(a) stated'"]. An INHABITANT of this structure
is the deliverable; constructing one is the future pass's burden. -/
structure REL2a (S : Setting) where
  /-- (a2, part) integrality of `d_j^rel := d_j/δ_j^rel` — "part of the obligation,
  EXPECTED from the tower data, walked in (a)'s pass" (the E·F ∣ d_j route is
  EXPECTED only; rev-4 F1). -/
  drel_dvd : (S.δrel : ℕ) ∣ (S.d : ℕ)
  /-- (a1) DOMAIN: "the explicit list of continuation coordinates on Σ_c — which
  base coordinates (ℓ, i) are free (not fixed by Σ_c)". C.0's global order on
  ℕ × ℕ, unchanged. -/
  freeCoords : Set (ℕ × ℕ)
  /-- (a1 cont.) the identification of Σ_c's continuation points with "a measurable
  product of O_δ-digit spaces" — one F_δ-valued digit per free coordinate (R0-box:
  the O_δ-digit is THE ATOM; never unpacked into δ F_p-components). -/
  domIdent : S.Cont ≃ (freeCoords → ↥(Fsub p S.δ))
```

```lean
  -- (REL2a continued)
  /-- (a2) TARGET degree `d_j^rel = d_j/δ_j^rel` (ℕ-division; `drel_dvd` records
  integrality). Target box := `Fin dRel → ↥(O p S.δabs)`, "the coefficient box of
  monic degree-d_j^rel polynomials over O_{δ_j}, with its own C.0-order digit
  coordinates" (the C.0 order on the target is the re-based theory's, doc-level). -/
  -- def-level: `REL2a.dRel := (S.d : ℕ) / (S.δrel : ℕ)` (declared after the structure)
  /-- (a3) EMBEDDING CONVENTION: the tower residue field at b_j (opaque) and "the
  named F_{δ_j} ↪ (tower residue field) embedding". -/
  TowerRes : Type
  [towerResField : Field TowerRes]
  embed : ↥(Fsub p S.δabs) →+* TowerRes
  /-- (a3 cont.) "the canonical-lift (Teichmüller/Frobenius) convention, fixed per
  the BASE-INDEX CONVENTION" — the lift as DATA; the pin to Mathlib's Teichmüller
  is the named Prop `TeichPinned` below (hypothesis-side, so trivial elaboration
  instances stay proof-free). -/
  teich : ↥(Fsub p S.δabs) → ↥(O p S.δabs)
  /-- (a4) FORMULA: "the target coefficients as explicit functions of the
  (a1)-coordinates — the map Θ_j itself". -/
  Θ : (freeCoords → ↥(Fsub p S.δ)) → (Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs))
  /-- (a5) FRAME COMPATIBILITY: "the displayed commutation of Θ_j with C.0.5's
  unitriangular transports" — transport families opaque, the commutation typed. -/
  FrameIdx : Type
  ambT : FrameIdx → ((freeCoords → ↥(Fsub p S.δ)) ≃ (freeCoords → ↥(Fsub p S.δ)))
  tgtT : FrameIdx → ((Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs)) ≃
                     (Fin ((S.d : ℕ) / (S.δrel : ℕ)) → ↥(O p S.δabs)))
  frame_compat : ∀ (i : FrameIdx) x, Θ (ambT i x) = tgtT i (Θ x)
  /-- (a6) READ DICTIONARY: "letter-for-letter transport of b_j's continuation READS
  to O_{δ_j}-classifier reads ((EQ-1)'s dictionary), displayed per read field" —
  the per-read-field displays are the pass's burden; the dictionary is the datum. -/
  AmbRead : Type
  TgtRead : Type
  readDict : AmbRead → TgtRead

/-- (a2)'s target degree, named. -/
def REL2a.dRel {S : Setting} (_A : REL2a p S) : ℕ := (S.d : ℕ) / (S.δrel : ℕ)

/-- (a3)'s PIN [named Prop, hypothesis-side]: the lift datum agrees with Mathlib's
Teichmüller representative, computed in W(F̄_p) — the BASE-INDEX CONVENTION's
"canonical-lift (Teichmüller/Frobenius) convention". -/
def TeichPinned {S : Setting} (A : REL2a p S) : Prop :=
  ∀ x : ↥(Fsub p S.δabs),
    ((A.teich x : ↥(O p S.δabs)) : Wbar p) = WittVector.teichmuller p (x : Kbar p)

/-- **(REL.2b) NORMALIZATION / JACOBIAN** [OPEN; "stated RELATIVE to (a1)–(a4) …
and only for cells with μ(Σ_c) > 0"]. "for every REL.1-measurable continuation
event W over O_{δ_j} (digit cylinders generate), μ( Θ_j⁻¹(W) │ Σ_c ) =
vol_{O_{δ_j}}(W)" — a MEASURE COMPARISON, not a bijection alone; "nothing short of
the display above is accepted as '(b) done'". `V` is REL.1's box measure
(conditional on REL.1, displayed per site). -/
def REL2b (S : Setting) (A : REL2a p S) (V : BoxVol p S.δabs A.dRel) : Prop :=
  0 < S.cellMass →
    ∀ W ∈ V.events, S.condMass ((fun f => A.Θ (A.domIdent f)) ⁻¹' W) = V.vol W

/-- **(REL.2d) LIFT-POLICY COMPATIBILITY — the acceptance-criterion COMMUTATIVE
SQUARE** ["well-posed only AFTER (a1)–(a6) exist"]. Vertices: b_j's continuation
data on Σ_c; the O_{δ_j} coefficient box; b_j's continuation subtree of T_can(f);
the O_{δ_j}-engine's canonical tree. Horizontals: Θ_j and "a SPECIFIED node-data
correspondence (species word, node datum fields, τ-verdicts, via (a6)'s dictionary
+ (EQ-2)'s alphabets), the canonical residue-field-lift handling of [1]'s policy
re-based per (a3)". Also supplies the prescribed-subtree identification WITHOUT
which "(SIB-Oδ) below is ill-typed". An INHABITANT is the deliverable; the field
`square` is the obligation's display. -/
structure REL2d (S : Setting) (A : REL2a p S) where
  /-- b_j's continuation subtrees of T_can(f) ([1]'s canonical tree, REV 8's
  per-branch form) — opaque. -/
  AmbTree : Type
  ambTcan : S.Cont → AmbTree
  /-- the O_{δ_j}-engine's canonical trees — opaque. -/
  TgtTree : Type
  tgtTcan : (Fin A.dRel → ↥(O p S.δabs)) → TgtTree
  /-- the SPECIFIED node-data correspondence. -/
  nodeCorr : AmbTree → TgtTree
  /-- "The square commutes for every f ∈ Σ_c." -/
  square : ∀ f : S.Cont, nodeCorr (ambTcan f) = tgtTcan (A.Θ (A.domIdent f))
  /-- canonical O_{δ_j}-side prescribed subtrees + the identification of T_j
  ("a prescribed-subtree event S_j has no canonical O_{δ_j}-side meaning" without
  it) and the target-side realization predicate ((W1)'s reading inherited). -/
  TgtSub : Type
  subtreeCorr : S.PTree → TgtSub
  TgtRealizes : TgtTree → TgtSub → Prop
```

```lean
/-- **(REL.2e) β-IDENTIFICATION — the five-item typing checklist (e1)–(e5)**
[pass-1 gap 15 + pass-2 crit 2's repairs]. DATA fields = deliverables (e1)/(e4) +
the table; the obligations (e2)/(e3)/(e5) are the named Props below the structure.
(e5)'s re-keying escape ("or T_j added as an explicit further index of the entry,
with [3]'s tables re-keyed") is the fallback if `determines` fails — blueprint D5. -/
structure REL2e (S : Setting) (A : REL2a p S) (D : REL2d p S A) where
  /-- (e1) STATE-INDEX CORRESPONDENCE: REL.1-side states over O_{δ_j} (opaque) and
  the dictionary from [3]/[3t]'s τ_j(c); "compatible with (a6)'s read dictionary"
  is the pass's displayed burden. -/
  RelState : Type
  stateDict : S.StateIdx → RelState
  /-- [3]'s table: (first index, state, argument q) ↦ entry — the note's own shape. -/
  β : ℕ → S.StateIdx → ℕ → ℚ
  /-- (e4) FIRST-INDEX DICTIONARY: "an explicit definition of the entry's first
  index e_j from b_j's data … displayed to agree with [3]'s table convention".
  Typed per prescribed subtree (see (e5)); the candidate is `firstIdxCandidate`. -/
  entryFirst : S.PTree → ℕ

/-- (e4)'s CANDIDATE ["candidate: (a2)'s O_{δ_j}-degree d_j^rel — owed, not
assumed"]: named Prop, hypothesis-side, asserted nowhere. -/
def REL2e.firstIdxCandidate {S : Setting} {A : REL2a p S} {D : REL2d p S A}
    (E : REL2e p S A D) : Prop := ∀ T : S.PTree, E.entryFirst T = A.dRel

/-- (e2) DEGREE CONVENTION, as the checkable identity behind `Setting.βarg`:
"the β-argument is p^{δ_j} with δ_j ABSOLUTE …, = q_δ^{δ_j^rel}". -/
theorem βarg_eq (S : Setting) : S.βarg p = qq p S.δ ^ (S.δrel : ℕ) := qq_mul p _ _

/-- (e3) MASS = ENTRY ["keyed so this is [3]'s definition or a cited theorem, never
a notational overlap"]: β_{e_j, τ_j(c)}(p^{δ_j}) IS the REL.1 mass
vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j }. OPEN; hypothesis-side. -/
def REL2e.massEqEntry {S : Setting} {A : REL2a p S} {D : REL2d p S A}
    (E : REL2e p S A D) (V : BoxVol p S.δabs A.dRel) : Prop :=
  ∀ T : S.PTree,
    E.β (E.entryFirst T) S.τ (S.βarg p) =
      V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}

/-- (e5) SUBTREE/OUTCOME TYPING, first disjunct: "the entry's indices must DETERMINE
the prescribed subtree T_j" — at the fixed cell (τ_j(c) fixed), distinct prescribed
subtrees may not share an entry key. OPEN; hypothesis-side (escape: re-key, D5). -/
def REL2e.determines {S : Setting} {A : REL2a p S} {D : REL2d p S A}
    (E : REL2e p S A D) : Prop :=
  ∀ T T' : S.PTree, E.entryFirst T = E.entryFirst T' → T = T'

/-! ## The equivariance trio (EQ-1/2/3) -/

/-- (EQ-1) carrier: the species SYNTAX (letters = "stage tuples (e, h, g, μ),
side/lattice data, and polygon conventions — a grammar parameterized by integers
and residual-degree data, never by the residue field's SIZE"), with the per-δ
realized menu. -/
structure SpeciesSyntax where
  Letter : Type
  menu : ℕ+ → Set Letter

/-- **(EQ-1) SPECIES/MENU SYNTAX INVARIANT** [STATUS: PREDICTED — "nothing derived
here"; the formal check is a named checkpoint of REL.1's pass]: "the species
alphabet and menu are the SAME finite syntax over every O_δ … What changes … is the
REALIZATION multiplicity of each letter …, never the letter set." -/
def EQ1 (Sp : SpeciesSyntax) : Prop := ∀ δ : ℕ+, Sp.menu δ = Sp.menu 1

/-- (EQ-2) carrier: per-(δ, position-class) alphabet data. `card_eq` is the
UNCONDITIONAL definition part ("Unconditionally |𝔸_δ| = p^{a_δ}, a_δ := the
F_p-additive-span dimension of the re-based images" — D.3(e)(i)/C.3 run over O_δ,
NOT a scalar extension of 𝔸). `Stable` is the rev-4 COMPARISON-DOMAIN pin:
δ-STABLE-SPECIES positions, "matched per (a6)/(EQ-1)'s owed dictionary". -/
structure AlphabetData where
  Pos : Type
  aDim : ℕ+ → Pos → ℕ
  card : ℕ+ → Pos → ℕ
  card_eq : ∀ (δ : ℕ+) (x : Pos), card δ x = p ^ aDim δ x
  Stable : ℕ+ → Pos → Prop

/-- **(EQ-2) the a_δ = δ·a law, ON THE PINNED PER-POSITION-CLASS DOMAIN** [OPEN,
REL.1-conditional]: "at a fixed shape position WHOSE SPECIES IS δ-STABLE …, the
re-based piece maps are F_δ-linear and a_δ = δ·a". Split positions are OUTSIDE the
domain (the F₉ instance re-distributes; REL.2/(SIB) territory) — captured here by
the `Stable` guard, so nothing is claimed off-domain. -/
def EQ2law (A : AlphabetData p) : Prop :=
  ∀ (δ : ℕ+) (x : A.Pos), A.Stable δ x → A.aDim δ x = (δ : ℕ) * A.aDim 1 x

/-- (EQ-2)'s displayed consequence "|𝔸_δ| = q_δ^a = |𝔸|^δ" on the pinned domain —
PROVABLE from `card_eq` + `EQ2law` by `pow_mul` (unit R17; the note's chain is
notation once the law is hypothesized). -/
theorem EQ2law_card (A : AlphabetData p) (h : EQ2law p A) :
    ∀ (δ : ℕ+) (x : A.Pos), A.Stable δ x →
      A.card δ x = qq p δ ^ A.aDim 1 x ∧ A.card δ x = A.card 1 x ^ (δ : ℕ) := sorry

/-- **(EQ-3) CONDITIONAL MASSES TRANSPORTED** — "REL.2(b) verbatim …; no weaker
reading (bijection-only, or level-matching without normalization) counts." -/
abbrev EQ3 (S : Setting) (A : REL2a p S) (V : BoxVol p S.δabs A.dRel) : Prop :=
  REL2b p S A V
```

```lean
/-! ## R.2 — the (SIB) O_δ quantifier: this corpus's deliverable statement -/

/-- **(SIB-Oδ)** [FENCED = REL.1 + REL.2(a)+(b)+(d), composed; derived nowhere yet].
"For EVERY realized prefix η, EVERY branching cell c, EVERY branch b_j —
simultaneously over every unramified O_δ that arises (all δ ≥ 1 in one statement;
no per-δ case analysis) — the event S_j IS an O_{δ_j}-statement": (REL.2a)
identifies the continuation with the monic degree-d_j^rel box over O_{δ_j};
(REL.2d) identifies T_j with a canonical O_{δ_j}-subtree; (REL.2b) prices
  μ( S_j │ Σ_c ) = vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j },
the right side a REL.1-theory mass. `Settings` is the PARAMETER family of realized
(η, c, b_j, δ)-instances (blueprint D2) — supplied by the ambient theory, so the
∀ ranges over exactly the note's quantifier, not junk instances. The extra
`S.SEvent T = …` conjunct is the "S_j IS an O_{δ_j}-statement" typing itself: the
ambient event is the Θ-pullback of the target-side realization event.
RECURSION CLAUSE: "the same typing applies at every descendant branching cell
inside T_j, ABSOLUTE indices throughout — a branch of relative accumulated degree
δ″ at ambient O_{δ_j} targets O_{δ_j·δ″}, literally a subring chain in W(F̄_p)" —
carried by (i) `Settings` containing every descendant instance with its ambient
index set to δ_j (the family is closed under descent — a closure property of the
SUPPLIER, recorded here as the reading), and (ii) the chain lemma `O_chain` (R20)
witnessing the literal subring chain. -/
def SIBOdelta (Settings : Set (Setting)) : Prop :=
  ∀ S ∈ Settings,
    ∃ (A : REL2a p S) (D : REL2d p S A) (V : BoxVol p S.δabs A.dRel),
      REL2b p S A V ∧
      ∀ T : S.PTree,
        (S.SEvent T =
          (fun f => A.Θ (A.domIdent f)) ⁻¹' {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}) ∧
        S.condMass (S.SEvent T) =
          V.vol {g | D.TgtRealizes (D.tgtTcan g) (D.subtreeCorr T)}

/-- R20: the recursion clause's subring chain, "(unramified over unramified is
unramified)" bookkeeping: O_δ ⊆ O_{δ_j} ⊆ O_{δ_j·δ″} literally in W(F̄_p). -/
theorem O_chain (S : Setting) (δ'' : ℕ+) :
    O p S.δ ≤ O p S.δabs ∧ O p S.δabs ≤ O p (S.δabs * δ'') := sorry

/-! ## R.3 — (REL.3), the DEFERRED-STATEMENT obligation -/

/-- One [4]-side consumption site, ONCE [4]'s displays exist: "REL.3's revision
restates each consumed display verbatim with the base re-scoped to O_δ (ABSOLUTE
indices)". Until then this structure types the SHAPE only — "the [4]-side displays
(SQ.0–SQ.2's actual events, quantifiers, and inequalities) DO NOT EXIST YET …
so no theorem statement is possible here". -/
structure SQConsumptionSite where
  /-- the consumed display, re-scoped, as a δ-indexed Prop family. What IS fixed
  from the plan: "the induction hypothesis is an input theorem about vol_{O_δ},
  never the formal substitution q ↦ q^δ in a ℤ_p-display" — i.e. `rescoped δ` must
  be a STATEMENT ABOUT the O_δ theory; enforcing that is [2r]'s future revision. -/
  rescoped : ℕ+ → Prop

/-- **(REL.3)** deferred form: every site's re-scoped display at every δ. [2r] OWNS
the obligation; [4] names the sites (`sites` is their parameter slot). -/
def REL3 (sites : List SQConsumptionSite) : Prop :=
  ∀ s ∈ sites, ∀ δ : ℕ+, s.rescoped δ

/-! ## Elaboration checks (well-formedness ONLY — blueprint D2; never evidence) -/
section Elab
-- R6/R10/R12/R13/R14/R19/R21-style checks; trivial carriers, all-zero masses.
-- e.g.:  def S₀ : Setting := { δ := 1, δrel := 1, d := 1, Cont := PUnit,
--   cellMass := 0, condMass := fun _ => 0, PTree := PEmpty,
--   SEvent := PEmpty.elim, StateIdx := PUnit, τ := ⟨⟩ }
-- example : REL2a 2 S₀ := { drel_dvd := ⟨1, rfl⟩, freeCoords := ∅, domIdent := …,
--   TowerRes := ↥(Fsub 2 1), embed := …, teich := fun _ => 0, Θ := fun _ _ => 0,
--   FrameIdx := PEmpty, ambT := PEmpty.elim, tgtT := PEmpty.elim,
--   frame_compat := fun i => i.elim, AmbRead := PEmpty, TgtRead := PUnit,
--   readDict := PEmpty.elim }
-- #check @REL1  #check @REL2b  #check @SIBOdelta  #check @REL3  (etc.)
end Elab
end MovesR
```

SKELETON STATUS: NORMATIVE FOR CONTENT, not character-exact — the E-phase fixes
syntax (e.g. instance-field bracketing, universe/implicit tweaks, the dangling
(a2)-comment placement) WITHOUT changing any quantifier, equality, or field list;
any such change beyond syntax re-enters the audit loop (statement fence).

## 2. Unit specs (21 units; format per campaign §2)

Files: `Base.lean` (R1–R5), `Interface.lean` (R6), `Rel1.lean` (R7–R9),
`Rel2.lean` (R10–R14), `Eq.lean` (R15–R18), `Sib.lean` (R19–R20), `Rel3.lean` (R21).
`Defs.lean` = re-export shim. Every def-unit's acceptance = the definitions land
verbatim-from-skeleton + its `example`/`#check` elaboration compiles.

**R1 MovesR.base_defs** · Base.lean · statement: defs `Kbar, Wbar, Fsub, O, qq,
relExt` (skeleton §R0) + `#check` elaborations.
moves_ref: "Fix an algebraic closure F̄_p once; F_m is THE subfield of order p^m and
O_m := W(F_m) ⊂ W(F̄_p)." · deps: — · sketch: definitions only; Fsub via
eqLocusField+iterateFrobenius (fallback D1 if ExpChar instance balks) · easy ·
hypothesis_fields: none (concrete).

**R2 MovesR.Fsub_le** · Base.lean · statement:
`theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m`.
moves_ref: "Nested base changes then compose LITERALLY as subrings — O_δ ⊂ O_{δδ′},
no per-pair embedding choices" (field layer). · deps: R1 · sketch: x^{p^d} = x ⇒
x^{p^{dk}} = x by induction on k (pow_mul/pow_pow arithmetic; or
iterateFrobenius_add + hom-iteration) · medium · hypothesis_fields: none (PROVED).

**R3 MovesR.O_le** · Base.lean · statement:
`theorem O_le {d m : ℕ+} (h : d ∣ m) : O p d ≤ O p m`.
moves_ref: same display as R2 (the subring layer). · deps: R1, R2 · sketch: local
lemma `map_comp` by `WittVector.ext` + `map_coeff`; then
`map (subtype d) = (map (subtype m)).comp (map (Subfield.inclusion (Fsub_le h)))`,
ranges nest · medium · hypothesis_fields: none (PROVED).

**R4 MovesR.relExt_comp** · Base.lean · statement: `relExt_eq` (`rfl`),
`relExt_relExt` (`mul_assoc`), `O_le_relExt` (from R3) — skeleton §R0.
moves_ref: "'(O_δ)_{δ′} = O_{δδ′}' is bookkeeping inside W(F̄_p), never an
identification up to isomorphism." · deps: R1, R3 · sketch: the composition law IS
definitional under D1's convention; the content is the inclusion · easy ·
hypothesis_fields: none (PROVED — this is the charge's "definitional lemma").

**R5 MovesR.qq_mul** · Base.lean · statement:
`theorem qq_mul (m δ' : ℕ+) : qq p (m * δ') = qq p m ^ (δ' : ℕ)`.
moves_ref: "pool size q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}". · deps: R1 · sketch:
`pow_mul` + PNat coercion push · easy · hypothesis_fields: none (PROVED).

**R6 MovesR.Setting** · Interface.lean · statement: `structure Setting`,
`Setting.δabs`, `Setting.βarg` (skeleton) + trivial-instance `example`.
moves_ref: "Ambient base O_δ (δ = 1 at the root …), a realized prefix η, state
cylinder Σ (frame Ψ_η), digit cell c of Σ, and a branch b_j … δ_j := δ·δ_j^rel, the
ABSOLUTE accumulated residue degree." · deps: R1 · sketch: opaque carriers per D2;
S_j's "realizes" reading left opaque per (W1) · easy · hypothesis_fields: none
(carrier only; asserts nothing).

**R7 MovesR.REL1_ledger** · Rel1.lean · statement: `structure REL1ClauseLedger` +
`REL1ClauseLedger.Holds` + `example` (all-`True` instance elaborates).
moves_ref: "§A, §B1, §B2-DEF, and §C — through Theorem C(a)/(b) with
C.0.5/PIN-WELLDEF, C.1, C.1.5/(ZC), LST, TYP, DOM — hold over O_δ … MUTATIS
MUTANDIS, NOT verbatim." · deps: — · sketch: ten named Prop slots (D4); contents
owed by the re-scoping pass · easy · hypothesis_fields: all ten slots (open).

**R8 MovesR.REL1_counting** · Rel1.lean · statement: `structure REL1Counting` +
`def REL1b` (skeleton) + `#check`.
moves_ref: "(REL.1-b) #{ f mod p^N ∈ S(H, Z) } = q_δ^{nN} · ∏_{i=0}^{k}
vol(E_fresh(ν_i)) · vol(Z) for every N ≥ N(H, Z)." · deps: R1 · sketch: the one
display the note fixes, typed verbatim over opaque H/Z carriers · medium (typing
care: ℚ-cast, range (k+1) product) · hypothesis_fields: REL1b itself (open).

**R9 MovesR.REL1_family** · Rel1.lean · statement:
`def REL1 (δ : ℕ+) (C : REL1Counting δ) (L : REL1ClauseLedger) : Prop` + `#check`.
moves_ref: "STATUS: a NEW THEOREM with its own verification passes — not a
corollary, not 'by inspection' … EVERY consumer below is conditional on REL.1,
displayed per site." · deps: R7, R8 · sketch: `L.Holds ∧ REL1b p δ C`; the
Prop-family over δ the charge names · easy · hypothesis_fields: REL1 (OPEN KERNEL;
never instantiated in MovesR).

**R10 MovesR.REL2a** · Rel2.lean · statement: `structure REL2a (S : Setting)` with
fields `drel_dvd, freeCoords, domIdent, TowerRes, embed, teich, Θ, FrameIdx, ambT,
tgtT, frame_compat, AmbRead, TgtRead, readDict` + `REL2a.dRel` + `TeichPinned` +
trivial `example` (D1-fallback carriers).
moves_ref: "(a) is now a DELIVERABLES CHECKLIST, and nothing short of all six items
is '(a) stated', let alone proved. The pass that closes (a) must EXHIBIT: (a1)…(a6)."
deps: R1, R6 · sketch: one field-block per checklist item; (a2)'s integrality a Prop
field; (a3)'s Teichmüller pin split out as `TeichPinned` so the trivial instance is
proof-free · medium (largest structure) · hypothesis_fields: `TeichPinned` (open
pin); the whole INHABITANT is the future pass's deliverable.

**R11 MovesR.BoxVol** · Rel2.lean · statement: `structure BoxVol (m : ℕ+) (n : ℕ)`
(events, vol, vol_univ) + trivial `example` (vol := indicator of univ… any
normalized dummy).
moves_ref: "(R0-box) … coefficient box O_δ^n with normalized Haar measure
vol_{O_δ}(O_δ^n) = 1." · deps: R1 · sketch: the REL.1-side measure interface;
"digit cylinders generate" recorded doc-level · easy · hypothesis_fields:
`vol_univ` (normalization, a structure field); instances conditional on REL.1.

**R12 MovesR.REL2b** · Rel2.lean · statement:
`def REL2b (S) (A : REL2a p S) (V : BoxVol p S.δabs A.dRel) : Prop` + `#check`.
moves_ref: "for every REL.1-measurable continuation event W over O_{δ_j} (digit
cylinders generate), μ( Θ_j⁻¹(W) │ Σ_c ) = vol_{O_{δ_j}}(W)" — with the
"only for cells with μ(Σ_c) > 0" proviso as antecedent. · deps: R10, R11 · sketch:
measure comparison, not bijection; pushforward = normalized box measure · easy ·
hypothesis_fields: REL2b (OPEN KERNEL = (EQ-3)).

**R13 MovesR.REL2d** · Rel2.lean · statement: `structure REL2d (S) (A : REL2a p S)`
(AmbTree, ambTcan, TgtTree, tgtTcan, nodeCorr, square, TgtSub, subtreeCorr,
TgtRealizes) + trivial `example` (PUnit trees, square by `rfl`).
moves_ref: "a displayed COMMUTATIVE SQUARE — vertices: b_j's continuation data on
Σ_c; the O_{δ_j} coefficient box; b_j's continuation subtree of T_can(f); the
O_{δ_j}-engine's canonical tree … The square commutes for every f ∈ Σ_c."
deps: R10 · sketch: acceptance-criterion square as structure; prescribed-subtree
identification included (else (SIB-Oδ) ill-typed) · medium · hypothesis_fields:
inhabitation = deliverable; `square` is the obligation's display.

**R14 MovesR.REL2e** · Rel2.lean · statement: `structure REL2e (S) (A) (D)`
(RelState, stateDict, β, entryFirst) + `firstIdxCandidate`, `massEqEntry`,
`determines` + `βarg_eq` + trivial `example`.
moves_ref: "(e1) STATE-INDEX CORRESPONDENCE … (e2) DEGREE CONVENTION — the
β-argument is p^{δ_j} with δ_j ABSOLUTE … (e3) MASS = ENTRY … (e4) FIRST-INDEX
DICTIONARY … (e5) SUBTREE/OUTCOME TYPING." · deps: R5, R10, R11, R13 · sketch: D5's
keying; (e2) = `βarg_eq` (provable via R5, one rewrite); (e3)/(e5) hypothesis-side
Props · medium · hypothesis_fields: `massEqEntry` (e3), `determines` (e5),
`firstIdxCandidate` (e4's candidate) — all open; data fields deliverable.

**R15 MovesR.EQ1** · Eq.lean · statement: `structure SpeciesSyntax` + `def EQ1` +
`#check`.
moves_ref: "(EQ-1) … species letters are defined by stage tuples (e, h, g, μ) …
never by the residue field's SIZE … STATUS: PREDICTED — nothing derived here."
deps: — · sketch: fixed Letter syntax, per-δ menu, EQ1 := ∀ δ, menu δ = menu 1 ·
easy · hypothesis_fields: EQ1 (PREDICTED, fenced into REL.1's pass).

**R16 MovesR.EQ2** · Eq.lean · statement: `structure AlphabetData` (Pos, aDim,
card, card_eq, Stable) + `def EQ2law` + trivial `example` (card := p^aDim).
moves_ref: "DEFINITION (unconditional): … |𝔸_δ| = p^{a_δ} … PREDICTION (OPEN …
COMPARISON DOMAIN PINNED …): at a fixed shape position WHOSE SPECIES IS δ-STABLE …
a_δ = δ·a." · deps: R1 · sketch: definition part = `card_eq` field (unconditional);
law guarded by `Stable` (the rev-4 per-position-class pin; split positions
out-of-domain by construction) · medium · hypothesis_fields: EQ2law (OPEN,
REL.1-conditional); `Stable`'s matching dictionary owed at (a6)/(EQ-1).

**R17 MovesR.EQ2law_card** · Eq.lean · statement: `theorem EQ2law_card` (skeleton).
moves_ref: "i.e. |𝔸_δ| = q_δ^a = |𝔸|^δ — whence exponent preservation in base q_δ
for every per-digit factor." · deps: R16, R5 · sketch: p^{δ·a} = (p^δ)^a = (p^a)^δ
(`pow_mul`, `pow_right_comm`), from `card_eq` + hypothesized law · easy (PROVED —
conditional-on-hypothesis arithmetic, no kernel discharged) · hypothesis_fields:
takes `EQ2law` as hypothesis `h`.

**R18 MovesR.EQ3** · Eq.lean · statement: `abbrev EQ3 … := REL2b p S A V` + `#check`.
moves_ref: "(EQ-3) CONDITIONAL MASSES TRANSPORTED. REL.2(b) verbatim … no weaker
reading … counts." · deps: R12 · sketch: definitional alias, keeping the note's
name in the API · easy · hypothesis_fields: = REL2b (open).

**R19 MovesR.SIBOdelta** · Sib.lean · statement:
`def SIBOdelta (Settings : Set Setting) : Prop` (skeleton) + `#check` + `example`
with `Settings := ∅` elaborating (NOT evidence — D2).
moves_ref: "(SIB-Oδ) [FENCED = REL.1 + REL.2(a)+(b)+(d), composed; derived nowhere
yet] … the event S_j IS an O_{δ_j}-statement … μ( S_j │ Σ_c ) =
vol_{O_{δ_j}}{ g : T_can^{O_{δ_j}}(g) realizes T_j }." · deps: R6, R10, R11, R12,
R13 · sketch: ∃-composition of (a)/(d)/(V) with (b) + the event-typing conjunct +
the pricing display; recursion clause = supplier-side closure (docstring) + R20 ·
medium (the corpus's key deliverable statement) · hypothesis_fields: SIBOdelta
(OPEN — the exact sentence [3t]-COND's acceptance record waits on).

**R20 MovesR.O_chain** · Sib.lean · statement:
`theorem O_chain (S : Setting) (δ'' : ℕ+) : O p S.δ ≤ O p S.δabs ∧ O p S.δabs ≤ O p (S.δabs * δ'')`.
moves_ref: "a branch of relative accumulated degree δ″ at ambient O_{δ_j} targets
O_{δ_j·δ″}, literally a subring chain in W(F̄_p) per the BASE-INDEX CONVENTION."
deps: R3, R6 · sketch: both legs are `O_le` at divisibilities δ ∣ δ·δrel and
δabs ∣ δabs·δ″ · easy (PROVED) · hypothesis_fields: none.

**R21 MovesR.REL3_deferred** · Rel3.lean · statement:
`structure SQConsumptionSite` + `def REL3 (sites : List SQConsumptionSite) : Prop`
+ `#check` + `example : REL3 [] := by simp [REL3]` (empty-sites elaboration).
moves_ref: "(REL.3) [DEFERRED-STATEMENT OBLIGATION …]. The [4]-side displays … DO
NOT EXIST YET — … no theorem statement is possible here … the induction hypothesis
is an input theorem about vol_{O_δ}, never the formal substitution q ↦ q^δ."
deps: — · sketch: shape-only typing; [4] supplies `sites` verbatim-re-scoped, then
REL.3's real statement replaces this per the note's ACCEPTANCE CRITERION and
re-enters audit · easy · hypothesis_fields: REL3 (deferred obligation; owner [2r],
consumption sites named by [4]).

## 3. Audit notes (for the wave-2 Codex pass)

- FAITHFULNESS ANCHORS: every docstring quotes the rev-5 display it encodes; the
  unit moves_refs above are the check keys. The note derives NOTHING — accordingly
  the ONLY `theorem`s are R2/R3/R4/R5/R17/R20 (base-index bookkeeping + one
  hypothesis-conditional pow identity), none of which touches an obligation.
- KNOWN WIDENINGS (deliberate, flag-checked): (i) `Setting` absorbs η/Σ_c/b_j into
  opaque carriers — the note's quantifier is recovered via the `Settings` parameter
  (D2); (ii) (e5) types the note's FIRST disjunct only, escape recorded (D5);
  (iii) REL.3 is a shape, not a statement (the note says none is possible);
  (iv) (a3)'s "named embedding … fixed per the BASE-INDEX CONVENTION" is a datum +
  `TeichPinned`; the NAMING of the F_{δ_j} ↪ tower embedding stays pass-side.
- CROSS-NOTE WATCHES INHERITED: (W1) "realizes T_j" — `SEvent`/`TgtRealizes` opaque,
  so every MovesR statement is neutral to the [1]/[3t] pin; at the CL-10 sync the
  pinned reading lands as the SUPPLIER's definition, no MovesR statement changes.
  (W2) absolute-index annotation — enforced by construction (`Setting.δabs`,
  `βarg`, `relExt` all absolute).
- PLAN-SYNC FLAG (note R.1): CL-8 must ledger REL.2's (e) leg + the five-count;
  MovesR already carries the five-obligation convention ((c) absent by re-homing).
- CONSUMER EDGES (Lean-side): MovesT ((SIB)'s O_δ quantifier consumes `SIBOdelta`,
  `Setting`, R20); MovesS (β legs consume `REL2e` + `βarg_eq`); MovesU (SQ.2 via
  `REL3`); MovesV (conditionality record cites `REL1`). Import direction: those
  corpora import MovesR, never conversely.

## 4. File map + status ledger

  lean/LeanUrat/MovesR/Base.lean       R1–R5   (defs + the 4 provable lemmas)
  lean/LeanUrat/MovesR/Interface.lean  R6      (Setting, δabs, βarg)
  lean/LeanUrat/MovesR/Rel1.lean       R7–R9   (ledger, counting, family)
  lean/LeanUrat/MovesR/Rel2.lean       R10–R14 ((a), BoxVol, (b), (d), (e))
  lean/LeanUrat/MovesR/Eq.lean         R15–R18 (EQ-1/2/2card/3)
  lean/LeanUrat/MovesR/Sib.lean        R19–R20 ((SIB-Oδ), chain)
  lean/LeanUrat/MovesR/Rel3.lean       R21     (deferred shape)
  lean/LeanUrat/MovesR/Defs.lean       re-export shim (import-all)

STATUS (2026-07-28): BLUEPRINT WRITTEN (this file). Next gate: wave-2 Codex
semantic audit (statements faithful / non-vacuous / quantifier-exact), then
E-phase elaboration. 21 units: 6 provable (R2–R5, R17, R20), 15 statements-only.
No axioms introduced; no kernel touched; statement fence in force.
