/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H2.TransDeep
import LeanUrat.MovesC.Defs

/-!
# B2D/TDDefs — the TransDeep-supplier definitional layer  [B2DEF_LEAN unit E2; wave E]

**V1 SEMANTICS SUPERSEDED (2026-08-02, statement round 2).** The semantic
layer of this file — `LedgerSemantics`, `LedgerLawful`, `LedgerStrata` — was
REFUTED as the reading of the accepted §B2-DEF mathematics at the TD-0/TD-3
hard-hole run (commit 5371139): `Nat.card` over ALL of `Coord → ℕ` is
empty-or-infinite under box-supported membership, forcing every fiber count
to 0 against the positive `slot_count_val` product (`TD3_countermodel.lean`,
the compiled refutation; design flag 1 below turned out CONTRADICTORY with
lawfulness, exactly as the countermodel isolates). These decls STAY, byte
unchanged, as the refutation record's carrier — but NO unit may consume them.
The live semantic layer is `TDDefsV2.lean` (`LedgerSemanticsV2`,
`LedgerLawfulV2`, `LedgerStrataV2`: finite-box counts over `supportUnion`
with `Fin q₀` values, MOVES D.11's `#{f mod p^N}` reading — the N-TD1-matched
spec), with the mechanism-inapplicability control in `TD3v2_control.lean`.
The datum `LedgerStratumData`, `ledgerJoint` + its proved support-constraint
lemmas, `blockCount`, `LedgerScope`, `LedgerClean` are NOT superseded — v2
consumes them unchanged.

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §3 + §5 (unit E2).
moves_ref: §B2-DEF D.3(e)(ii), D.8, D.11. deps: none (wave E).
difficulty: easy-medium (definitions; two proved support lemmas).

**E-PHASE NOTE (historical; status corrected 2026-08-08, F6 hygiene pass;
route (a) executed 2026-08-08).**
At E-phase landing this module and the `TD1..TD6` fan-out were skeleton: the
definitional layer plus theorem statements whose `sorry` bodies were the
campaign's OPEN-GOALS LEDGER, tracked by the blueprint (each `sorry` carried
its unit ID). AS OF 2026-08-08 the TD front is SORRY-FREE end-to-end: TD-1..TD-6
are PROVED on `LedgerLawfulV3` (`transDeep_of_ledger` fills
`fresh_of_transDeep`, machine-checked). B2D is now **0 sorries**: the former 3
GR entries (GR-3 ×2 + GR-4 ×1) were DISCHARGED at the ReadHyps-pinned face by
the route-(a) statement change (`ReadHyps` frame pins `hσs`/`hσt`;
GR34_DISPOSITION 2026-08-08), retiring the believed-false abstract σ.e ≥ 2
scope. THIS file has NO sorry.

## The two-layer design [R1-G1 fold], as landed

* **Layer 1 (the q-generic carrier)**: `ledgerJoint L : JointStratum D W P` — the
  H2 skeletal counting fields, defined from the datum's q₀-content and GATED at
  `q = q₀`. **SUPPORT CONSTRAINT [R2-C1 fold, load-bearing]**: `rhoCount` VANISHES
  off `q₀` (in particular at `q ∈ {0, 1}`, where `JunctionPinLaw`'s
  `∃ c ≠ 0, c < q^d` is unsatisfiable), so every `∀ q` H2 law is vacuous off `q₀`
  and substantive at `q₀` — proved below (`ledger_rhoCount_off_support`,
  `ledger_rhoCount_lt_two`), the R0Instance skeletal-carrier pattern.
* **Layer 2 (the q₀ semantics)**: the datum's counting fields (`cylFiber`,
  `cylFiberDigits`, `cylSlot`, `cylSlotDigits`) are ABSTRACT here and are tied to
  actual level-N digit-cylinder counts by `LedgerSemantics` + the `blockCount`
  per-block counts — the clauses of `LedgerLawful`, which unit TD-0 DISCHARGES at
  the designated instance built from the §B2-DEF ledger strata (S16/S17, T9/T12,
  C1–C5). The `Fin (q^D.d)` digit-value coding [R1-G2] enters through the pin's
  ℕ-code (`pin ρ < q0^d`), the digit-range clause, and the `slotCoord` read; the
  field-element-to-code bijection is TD-0's semantics duty.

## E-PHASE DESIGN FLAGS (for the statement audit; sanctioned-respelling class)

1. Members are `x : Coord → ℕ` (the MovesC `Coord = ℕ × ℕ` box chart, digit
   ℕ-codes). TD-0's member predicate must be BOX-SUPPORTED (off-box coordinates
   pinned) for the `Nat.card` semantics to be non-degenerate — the `boxChart`
   `Fin (n·N)` coding; flagged as TD-0's duty, not a law here.
2. `LedgerLawful` carries the §B2-DEF STRUCTURAL facts (cylinder split, block
   supports, disjointness (ii.3), forcing (ii.4), the D.8 (VERTEX) junction pin,
   the D.8 (BOX)+D.11 slot-count value) as named clauses. CONSEQUENCE, FLAGGED:
   the count-VALUE content the blueprint priced at TD-1 necessarily rides the
   `slot_count_val` clause (an abstract datum has no ℤ_p content to derive a
   value from), so TD-1's residual work is the law-from-lawfulness derivation and
   the LED/CL5 substance moves into TD-0's discharge of the clause. Wave-1
   staffing re-adjudicates unit pricing on this finding (blueprint §5's own
   provision); no STATEMENT deviates.
3. `hexact` (the S16/S17 anchored-march exactness pin, per-stratum data) rides as
   a bare-`Prop` field — the corpus's documented `RootHyps` E-phase device;
   True-instantiable; no law in this file consumes it; TD-0 types it against
   `L5_landTwoSided`'s `hexact` at instantiation.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC

variable {D : CensusData}

/-- **The §B2-DEF ledger-stratum datum at level N** (blueprint §5 E2): the
window chain / per-slot heights / junction ride the H2 carriers `W`, `P`; this
datum adds the level, the corpus prime power `q₀`, the parent-realization count,
the per-realization member predicates and block geometry, the abstract cylinder
counts (tied down by `LedgerLawful`), the ρ-determined junction pin code, and the
per-stratum `hexact` anchor pin. -/
structure LedgerStratumData (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) where
  /-- the joint level -/
  N : ℕ
  hN : P.N0 ≤ N
  /-- the corpus prime power q₀ = p^δ — the ONE alphabet size carrying content -/
  q0 : ℕ
  /-- support floor [R2-C1]: q₀ ≥ 2, so the junction pin code can be nonzero -/
  hq0 : 2 ≤ q0
  /-- the number of parent realizations ρ at q₀ (level N0) -/
  rho0 : ℕ
  /-- per-realization member predicate of the level-N ledger stratum (digit
      ℕ-codes on the `Coord` box chart; TD-0 instantiates from S16/S17) -/
  inStratum : ℕ → (Coord → ℕ) → Prop
  /-- the realized parent condition of ρ (D.3(e)(ii): parent equations) -/
  parentCond : ℕ → (Coord → ℕ) → Prop
  /-- the per-slot joint condition at slot k (height floor + digit content) -/
  slotCond : ℕ → Fin (W.ℓ + 1) → (Coord → ℕ) → Prop
  /-- the parent-pinned coordinate block (D.3(e)(ii.3)'s "blocks") -/
  parentBlock : Finset Coord
  /-- slot k's coordinate block (the height-β_k window block) -/
  slotBlock : Fin (W.ℓ + 1) → Finset Coord
  /-- the height-β_k digit coordinate of on-line slot k (the (FRESH) read leaf) -/
  slotCoord : ↥W.onLine → Coord
  /-- ABSTRACT per-realization per-slot height count at q₀ (tied by `LedgerLawful`) -/
  cylSlot : ℕ → Fin (W.ℓ + 1) → ℕ
  /-- ABSTRACT per-realization per-on-line-slot per-digit count at q₀ -/
  cylSlotDigits : ℕ → ↥W.onLine → ℕ → ℕ
  /-- ABSTRACT per-realization height-only fiber count at q₀ -/
  cylFiber : ℕ → ℕ
  /-- ABSTRACT per-realization prescribed-digit-vector count at q₀ -/
  cylFiberDigits : ℕ → (↥W.onLine → ℕ) → ℕ
  /-- the ρ-determined junction pin code (D.8 (VERTEX), Fin (q₀^d)-coded [R1-G2]) -/
  pin : ℕ → ℕ
  /-- the pin is nonzero (D.6: dig′ lands in F′ˣ) -/
  hpin_ne : ∀ ρ, ρ < rho0 → pin ρ ≠ 0
  /-- the pin code is in range (the Fin (q₀^d) coding) -/
  hpin_lt : ∀ ρ, ρ < rho0 → pin ρ < q0 ^ D.d
  /-- the S16/S17 anchored-march exactness pin — bare-`Prop` `RootHyps` device
      (module docstring flag 3); typed at TD-0 instantiation -/
  hexact : Prop

namespace LedgerStratumData

variable {W : WindowDatum D} {P : ParentShape D W}

/-- **Layer 1: the q-generic H2 counting carrier** — the datum's q₀-counts gated
at `q = q₀`, zero off support [R2-C1]. -/
noncomputable def ledgerJoint (L : LedgerStratumData D W P) :
    JointStratum D W P where
  N := L.N
  hN := L.hN
  rhoCount := fun q => if q = L.q0 then L.rho0 else 0
  slotCount := fun ρ k q => if q = L.q0 then L.cylSlot ρ k else 0
  slotDigits := fun ρ k z q => if q = L.q0 then L.cylSlotDigits ρ k z else 0
  fiber := fun ρ q => if q = L.q0 then L.cylFiber ρ else 0
  fiberDigits := fun ρ z q => if q = L.q0 then L.cylFiberDigits ρ z else 0

/-- THE SUPPORT CONSTRAINT [R2-C1], proved: `rhoCount` vanishes off `q₀`, so
every `∀ q` H2 law over `ρ < rhoCount q` is vacuous off the corpus prime power. -/
theorem ledger_rhoCount_off_support (L : LedgerStratumData D W P) :
    ∀ q : ℕ, q ≠ L.q0 → (L.ledgerJoint).rhoCount q = 0 := by
  intro q hq
  simp [ledgerJoint, hq]

/-- The [R2-C1] corner named in the blueprint: at `q ∈ {0, 1}` (where
`JunctionPinLaw`'s `∃ c ≠ 0, c < q^D.d` is unsatisfiable) the carrier is
vacuous — `q < 2 < q₀ + 1` forces `q ≠ q₀`. -/
theorem ledger_rhoCount_lt_two (L : LedgerStratumData D W P) :
    ∀ q : ℕ, q < 2 → (L.ledgerJoint).rhoCount q = 0 := by
  intro q hq
  have hne : q ≠ L.q0 := by have := L.hq0; omega
  exact L.ledger_rhoCount_off_support q hne

/-- **Layer 2, per-block counts**: the number of digit assignments on the finite
block `B` (values in `Fin q`, zero-extended off `B`) satisfying `cond` — the
per-block restricted cylinder count the per-slot semantics clauses use. -/
noncomputable def blockCount (q : ℕ) (B : Finset Coord)
    (cond : (Coord → ℕ) → Prop) : ℕ :=
  Nat.card {v : (↥B → Fin q) //
    cond (fun c => if h : c ∈ B then (v ⟨c, h⟩ : ℕ) else 0)}

/-- **Layer 2: the q₀ cylinder-count semantics** [R1-G1] — the datum's fiber
counting fields ARE the `Nat.card`s of its level-N member cylinders (the
R0Instance pattern at r ≥ 1); the digit reads pass through `slotCoord` and the
ℕ-coding [R1-G2]. Stated for ALL digit vectors z (`JunctionPinLaw` consumes
off-alphabet z too). TD-0 duty (b) discharges this at the designated instance. -/
def LedgerSemantics (L : LedgerStratumData D W P) : Prop :=
  ∀ ρ, ρ < L.rho0 →
    (L.cylFiber ρ = Nat.card {x : Coord → ℕ // L.inStratum ρ x}) ∧
    (∀ z : ↥W.onLine → ℕ,
      L.cylFiberDigits ρ z
        = Nat.card {x : Coord → ℕ // L.inStratum ρ x ∧
            ∀ k : ↥W.onLine, x (L.slotCoord k) = z k})

/-- **The lawfulness pack** [R1-G3 fold] — what unit TD-0 PROVES at the designated
instance (from S16/S17, T9 `T9_blockDisjoint`, T12 `T12_coordFin`, T10/C6(CL5),
`L5_landVertexDigit` + `K1_vertexPin` — never V9, §6 fence (v)), and what units
TD-1..TD-5 consume. Clause names carry their §B2-DEF displays. -/
structure LedgerLawful (L : LedgerStratumData D W P) : Prop where
  /-- layer-2 semantics: counting fields = cylinder cards -/
  semantics : LedgerSemantics L
  /-- D.3(e)(ii): the stratum is a digit CYLINDER — parent equations ∧ per-slot
      conditions over the box slots -/
  member_split : ∀ ρ x, L.inStratum ρ x ↔
    (L.parentCond ρ x ∧ ∀ k ∈ W.boxSlots, L.slotCond ρ k x)
  /-- the parent condition reads only the parent block -/
  parent_support : ∀ ρ x y, (∀ c ∈ L.parentBlock, x c = y c) →
    (L.parentCond ρ x ↔ L.parentCond ρ y)
  /-- slot k's condition reads only slot k's block -/
  slot_support : ∀ ρ k x y, (∀ c ∈ L.slotBlock k, x c = y c) →
    (L.slotCond ρ k x ↔ L.slotCond ρ k y)
  /-- slot blocks are pairwise disjoint (the product-box geometry) -/
  slots_disjoint : ∀ k k' : Fin (W.ℓ + 1), k ≠ k' →
    Disjoint (L.slotBlock k) (L.slotBlock k')
  /-- the on-line read leaf sits in its own slot's block -/
  slot_coord_mem : ∀ k : ↥W.onLine, L.slotCoord k ∈ L.slotBlock (k : Fin (W.ℓ + 1))
  /-- (ii.3): parent-pinned blocks are DISJOINT from every interior on-line
      slot's block (the typed (L) input; T9's display) -/
  parent_interior_disjoint : ∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    Disjoint L.parentBlock (L.slotBlock (k : Fin (W.ℓ + 1)))
  /-- (ii.4): each parent-pinned leaf's value is FORCED given ≺-predecessors,
      whatever the predecessors (T12's unit-diagonal display) -/
  pinned_forced : ∀ ρ, ρ < L.rho0 → ∀ c ∈ L.parentBlock,
    ∀ x y : Coord → ℕ, L.inStratum ρ x → L.inStratum ρ y →
    (∀ c' : Coord, CoordPrec c' c → x c' = y c') → x c = y c
  /-- D.8 (VERTEX) + D.6 + D.10: every member's junction read IS the ρ-determined
      pin code (nonzero by `hpin_ne`) -/
  junction : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ hk : W.ks ∈ W.onLine, x (L.slotCoord ⟨W.ks, hk⟩) = L.pin ρ
  /-- range: members' on-line digit reads are in the Fin (q₀^d) code range -/
  digit_range : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ k : ↥W.onLine, x (L.slotCoord k) < L.q0 ^ D.d
  /-- per-slot count semantics: the height count IS slot k's block count -/
  slot_sem : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k = blockCount L.q0 (L.slotBlock k) (L.slotCond ρ k)
  /-- per-slot per-digit count semantics through the `slotCoord` read -/
  slotDigits_sem : ∀ ρ, ρ < L.rho0 → ∀ (k : ↥W.onLine) (z : ℕ),
    L.cylSlotDigits ρ k z
      = blockCount L.q0 (L.slotBlock (k : Fin (W.ℓ + 1)))
          (fun x => L.slotCond ρ (k : Fin (W.ℓ + 1)) x ∧ x (L.slotCoord k) = z)
  /-- D.8 (BOX) + D.11 through the proved A1/TRI ledger: the per-slot height
      count VALUE at the joint floor (design flag 2: the LED/CL5 substance is
      discharged HERE by TD-0; TD-1 derives the H2 law from it) -/
  slot_count_val : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k
      = L.q0 ^ ((D.period * D.d) * L.N - D.s (max (W.beta k) (P.g k)))

end LedgerStratumData

/-- **The designated strata family** (blueprint §3 "fill the row"): the lawful
ledger instances' q-generic carriers. TD-0 de-vacuifies it (one compiled r ≥ 1
witness — duty (c), the `R0Instance` precedent). -/
def LedgerStrata (D : CensusData) (W : WindowDatum D) (P : ParentShape D W) :
    Set (JointStratum D W P) :=
  {J | ∃ L : LedgerStratumData D W P,
    L.LedgerLawful ∧ J = L.ledgerJoint}

/-- The CEN-J scope guard as a named predicate (`hscope` of the consuming
theorems, per the H2 FreshLaws docstring — never silently assumed). -/
def LedgerScope (W : WindowDatum D) (P : ParentShape D W) : Prop :=
  ∀ k ∈ W.onLine, P.g k ≤ W.beta k

/-- The clean-threshold regime at level N (`hclean`): the LED(i) window
`m·N ≥ s(·) + d` at every box slot — one full alphabet layer above the joint
floor (the CL5/CI-1..CI-4 full-attainment scope; E-phase rendering, FLAGGED for
the statement audit against C6's clean-threshold spec). -/
def LedgerClean (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
    (N : ℕ) : Prop :=
  ∀ k ∈ W.boxSlots,
    D.s (max (W.beta k) (P.g k)) + D.d ≤ (D.period * D.d) * N

end LeanUrat.B2D

#print axioms LeanUrat.B2D.LedgerStratumData.ledger_rhoCount_off_support
#print axioms LeanUrat.B2D.LedgerStratumData.ledger_rhoCount_lt_two
