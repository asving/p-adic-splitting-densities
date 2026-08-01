# BP_IV — Movement IV: THE VALUE SIDE (ROOT Steps 13–18b)

Blueprint architect deliverable for the Lean conversion swarm (authority: ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, "THE LEAN CONVERSION SWARM",
Asvin 2026-08-03; scaffold shape per the 2026-08-01 "THE PROOF SCAFFOLD" entry).
Math source of record: `docs/ROOT_ASSEMBLY_2026-08-02.md` REVISION 5 (cited below
as ROOT §2 Step k), plus the leaf briefs in `lean/notes/openmath/` cited per unit.

## 0. Charter, scope, ground rules

**Movement:** IV — the value side (the tables evaluate correctly). Steps and leaves:

| ROOT step | leaf | math grade (REV 5) | this blueprint's slice |
|---|---|---|---|
| 13 | O-4 + O4T (drainage transfer) | M05 core VERIFIED; O4T ADJUDICATED VERIFIED (leaf #7) | the ABSTRACT transfer layer (TR-0/FLOOR/TR-Q) + the envelope assembly; Theorem N3's n ≤ 3 read ceiling enters as a NAMED ROW, its proof a queued HARD unit |
| 14 | O-9 (order-r stratum census) | ADJUDICATED VERIFIED (leaf #8) at scope (GR-B)+(FRESH)+(ADM)-FULL | census carriers, (ADM)-FULL as a decidable named row, r = 0 automaticity, r = 1 criterion, the M08 level-1 census law; CEN-W r ≥ 1 = queued HARD, (GR-B)/(FRESH)-conditional |
| 15 | O-10 (K-COUNT / Smith profile) | VERIFIED at scope (leaf #6) | the whole K-COUNT chain (Mathlib SNF territory) + the adapted-cell (SIB) product law; K-LOC/(I-τ) as named rows |
| 17 | D-11 first tranche (MASS-ID M1/M1′/M3) | PROVED-UNVERIFIED at r3, pass 3 owed; clause 4 = (PACK) [M] | the M1 UNCONDITIONAL layer (kernel-value identities, row-sum-one, termination margins over the O-12 lemma base) + M3 glue; (PACK) as a named row, never proved here |
| 18 | O-11 (SERIES-TIE) | PROVED-UNVERIFIED (assembled) at r3 | the M04 abstract resummation core (lfp/Bekić/Neumann) + the tie assembly `seriesTie_of_kernels` targeting the corpus row `BridgeKernels.series_tie`; (K3-δ) as a named row |
| 18b | D-11 second tranche (MASS-ID M2) | proof on file at r3, monic scope | the squeeze (density = series) over the corpus `TreeSeam.finiteness_stack`, and the movement capstone `valueSide_massTie` |

Step 16 (O-8b/D-3, clause (UB)) is NOT this movement's (Movement V/UB architect);
we CONSUME its (R1)–(R4)/(UB-X) rows by name only (§1.0, §5).

**Ground rules bound here (ledger, verbatim consequences):** new modules ONLY under
`lean/LeanUrat/Scaffold/` in `namespace LeanUrat.Scaffold`; parked items 22–29 and all
fenced statements untouched; NO new axioms (the two audited axioms usable; nothing
below needs them); every [M] hypothesis a NAMED structure/row, never a `sorry` and
never silently strengthened; corpus reuse by import (§3); per-file `lake env lean`
gates during waves, full `lake build` + `AxChk_baseline` at division checkpoints;
when a leaf brief revs, this file's owner folds the delta (§5).

**Minimality is the design goal** (Asvin: "each piece should be minimal and
formalizable quickly and cleanly"): every unit ≤ ~40 lines of Lean; where a paper
lemma splits into three one-idea lemmas, it is three units.

**Module map (all new, all `LeanUrat/Scaffold/ValueSide/`):**

| file | step | contents |
|---|---|---|
| `CensusCore.lean` | 14 | `CensusData`, its derived finite carriers, and `ADMFull`; imports no value-side module |
| `Hyps.lean` | — | the independent named [M] rows `PackCorrespondence` and `K3DeltaRow`; imports `CensusCore.lean` only when re-exporting `ADMFull` |
| `Transfer.lean` | 13 | abstract drainage transfer over `ClassifierSpec` |
| `Census.lean` | 14 | imports `CensusCore.lean` and `Hyps.lean`; proves the (ADM)-FULL and level-1 census layers |
| `KCount.lean` | 15 | Smith-profile fiber counts + adapted-cell product law |
| `MassId.lean` | 17 | M1 unconditional layer + M3 glue |
| `SeriesTie.lean` | 18 | resummation core + `seriesTie_of_kernels` |
| `DensityTie.lean` | 18b | squeeze + `valueSide_massTie` |

Existing corpus types are used AS IS (never redefined): `SplittingType n`, `Box p n N`,
`boxProj`, `ClassifierSpec` (with `.decided/.undec/.env/.dmass`), `VPSound`,
`FiberSeries` (with `.seriesSum/.thrSlice/.mem_slice_iff`), `TreeSeam` (with the PROVED
`finiteness_stack`), `SolveSeam`, `SolveData`, `RegData`/`RegP`/`RegPin`, `UCarriers`,
`BridgeKernels` — all `LeanUrat/MovesU/Defs.lean`, `DefsCarriers.lean`,
`DefsLedger.lean`, `BridgeKernels.lean` (§3 has the exact declaration list).

---

## 1. STATEMENT LAYER

All sketches below are signature-accurate targets; provers may adjust implicit
binders/instance arguments but NOT the mathematical content (statement changes
escalate to the division lead → orchestrator, per the statement fence).

### 1.0 `CensusCore.lean` and `Hyps.lean` — the named [M] hypothesis rows

`CensusData` and `ADMFull` are declared together in `CensusCore.lean`; this module
imports neither `Census.lean` nor `Hyps.lean`. `Hyps.lean` contains the independent
(PACK) and (K3-δ) rows and may re-export `CensusCore.lean`. Thus the import graph is
`CensusCore → Hyps` and `{CensusCore, Hyps} → Census`, never a cycle. All [M] rows
are datum-indexed Prop-valued structures, not axioms or proposition aliases.

```lean
namespace LeanUrat.Scaffold

/-- **(ADM)-FULL** (ROOT §3.1 (ADM), the single operative O-9 r4 form; unit of
record 35faac7): every on-line lattice slot's β_k is FULLY attained by the
ledger — `attainDim β_k = d`, equivalently
`#{j : wt j ≡ β_k (mod e), wt j ≤ β_k} = d`.  p-free, per-datum decidable
(unit C3).  Automatic at r = 0 ONLY (unit C1); NOT automatic at r ≥ 1 (two
countermodels on file, O-9 pass-2/pass-3 records). -/
-- In `CensusCore.lean`, immediately after `CensusData` and its derived definitions:
structure ADMFull (D : CensusData) : Prop where
  full_attained : ∀ β ∈ D.onLineSlots, D.attainDim β = D.d

/-- **(PACK)** = (ROOT-C)(H5) (ROOT §3.1, REVISION 4 finding VC4-3): the CONCRETE
assembled pack equals the intended 𝔅_n instantiation ENTRY-FOR-ENTRY (D-11's
OPEN clause 4 = OL-O12-2's data half).  `AssembledPack` is the finite table
carrier (fields below); `intendedEntry` is the 𝔅_n reference read off the
`UCarriers` chain.  No proof of this row exists anywhere; Steps 18/18b consume
Step 17 AS this correspondence. -/
structure AssembledPack (n : ℕ) where
  Row : Type
  instR : Fintype Row
  entry : Row → RatFunc ℚ
  blockOf : Row → ℕ
  blockOf_pos : ∀ r, 1 ≤ blockOf r
  blockOf_le : ∀ r, blockOf r ≤ n

attribute [instance] AssembledPack.instR

/-- The independently typed reference table read from `C`; unit H2 supplies the
actual reader without mentioning an out-of-scope pack variable. -/
structure PackReference (n : ℕ) (C : UCarriers n) (P : AssembledPack n) where
  intendedEntry : P.Row → RatFunc ℚ
  intendedBlock : P.Row → ℕ
  intendedBlock_pos : ∀ r, 1 ≤ intendedBlock r
  intendedBlock_le : ∀ r, intendedBlock r ≤ n

structure PackCorrespondence (n : ℕ) (C : UCarriers n) (P : AssembledPack n)
    (R : PackReference n C P) : Prop where
  entry_eq : ∀ r : P.Row, P.entry r = R.intendedEntry r
  block_eq : ∀ r : P.Row, P.blockOf r = R.intendedBlock r

/-- **(K3-δ)** (ROOT §3.1 (UB-X)(b) restricted; REVISION 4 finding VC4-1): every
REALIZED δ > 1 pool of Step 18's K3-c is a δ-STABLE position class.
`DeltaStablePos` is OWNED by Movement V (O-8b's blueprint) — consumed here as an
opaque predicate parameter so this row compiles before Movement V lands. -/
structure K3DeltaRow (p : ℕ) (D : RegData p)
    (RealizedPool DeltaStablePos : ℕ → Prop) : Prop where
  depthSet_iff_realized : ∀ δ, δ ∈ D.depthSet ↔ RealizedPool δ
  realized_stable : ∀ δ, RealizedPool δ → 1 < δ → DeltaStablePos δ
```

Rows owned by OTHER movements are consumed using their actual datum-indexed
structures. There are no `Prop` aliases or placeholder definitions in this
movement. Their owner modules are explicit prerequisites of the first consuming
wave; if an owner has not landed, that consuming unit is blocked rather than
compiled against a weaker signature:

| row | owner blueprint | consumed at (units) |
|---|---|---|
| (GR-B) orders ≥ 2 (`GRBRow`) | BP_III (GD dictionary) | C5 (CEN-W r ≥ 1), S5, D4 |
| (FRESH) (`FreshRow`) | BP_III | C5' (CEN-J), S5, D4 |
| (R1)–(R4) = (H4a) (`R1R4Row`) | BP_V (O-8b/UB) | S5 (K3-c leg) |
| (H6) terminal-seam group (`TerminalSeamRows`) | BP_III (CU-2t owner) | S5 (K4/D-a leg) |
| K-LOC = M07 OL-3, (I-τ) | BP_III (dictionary) | K10 (application clause) |
| D-15 / O5triple Thm E rows | BP_III (Steps 6/12) | M7 (M3 glue) |

### 1.1 `Transfer.lean` — Step 13, the drainage-transfer layer (O4T)

Everything is stated over the corpus `ClassifierSpec n p` (counts, not measures —
the scaffold's cylinder-limit shape). Source: `O4T_phaseB_verifybrief_rev4.md`
§2 (TR-0, FLOOR, TR-Q with the UNBOUNDED majorant hypothesis — the V30-critical
repair is baked into the statement), §3.4 (N3-ENV).

```lean
/-- T0: fibers of the level reduction have exact size p^{n(N'−N)}. -/
theorem card_boxProj_fiber {p n : ℕ} [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (f : Box p n N) :
    Nat.card {g : Box p n N' // boxProj p n h g = f} = p ^ (n * (N' - N))

/-- T1 (stability ⇒ monotone envelope): env is antitone. -/
theorem ClassifierSpec.env_antitone {n p : ℕ} [Fact p.Prime]
    (X : ClassifierSpec n p) : Antitone X.env

/-- T2 (FLOOR, abstract): pointwise undecided-nesting transfers envelopes. -/
theorem env_le_of_undec_subset {n p : ℕ} [Fact p.Prime]
    {X Y : ClassifierSpec n p}
    (hsub : ∀ N (f : Box p n N), X.canonical N f = none → Y.canonical N f = none) :
    ∀ N, X.env N ≤ Y.env N

/-- T3 (TR-Q skeleton): an antitone envelope dominated along an unbounded monotone
    reparametrization by a vanishing bound itself vanishes.  (The O4T pass-1
    critical — Γ unbounded — is the `hg` hypothesis; never state without it.) -/
theorem env_tendsto_zero_of_majorant {E B : ℕ → ℝ} {g : ℕ → ℕ}
    (hE : Antitone E) (hE0 : ∀ N, 0 ≤ E N) (hg : Tendsto g atTop atTop)
    (hle : ∀ N, E (g N) ≤ B N) (hB : Tendsto B atTop (nhds 0)) :
    Tendsto E atTop (nhds 0)

/-- The two EXTERNAL analytic imports of Step 13, as one displayed row structure
    (I-TAIL = the discriminant tail bound, M05 Lemma C's counting form; CEIL = the
    Theorem-N3 read ceiling L(f) ≤ v_p(disc f) + 1 at 2 ≤ n ≤ 3).  `discV` is the
    level-N truncated discriminant valuation (a definition of this file, unit T4a).
    CEIL is the movement's queued HARD unit T7; until it lands the structure is a
    named row, exactly O4T's honest conditionality shape. -/
structure DrainageImports (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p) : Prop where
  n_lower : 2 ≤ n
  n_upper : n ≤ 3
  ceil : ∀ N (f : Box p n N), discV p n N f + 1 ≤ N → X.canonical N f ≠ none
  tail : ∀ N m : ℕ, (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
      ≤ tailC n * (p : ℝ) ^ (n * N) * (p : ℝ) ^ (-(m : ℝ) / (2 * (n - 1)))

/-- T6 (N3-ENV assembled): the scoped imports force drainage. -/
theorem env_tendsto_zero_of_imports {n p : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} (hI : DrainageImports n p X) :
    Tendsto X.env atTop (nhds 0)

/-- T7's complete CEIL interface. `canonicalOrderLEOne` is the concrete
classifier definition of unit T4b; the theorem has exactly the N3 degree scope. -/
noncomputable def canonicalOrderLEOne (n p : ℕ) [Fact p.Prime] :
    ClassifierSpec n p
theorem canonicalOrderLEOne_ceil {n p : ℕ} [Fact p.Prime]
    (hn0 : 2 ≤ n) (hn1 : n ≤ 3) :
    ∀ N (f : Box p n N), discV p n N f + 1 ≤ N →
      (canonicalOrderLEOne n p).canonical N f ≠ none
```

`env_tendsto_zero_of_imports` is EXACTLY the shape of the corpus row
`BridgeKernels.env_tendsto` (CL-4's supply): the delivery seam of Step 13. The n = 2
OM-model instance `OM.SeriesAssembly.hExhaust_n2` stays the independent gate (its
model differs; agreement seam D19 per the corpus docstring — NOT a discharge of this
row, recorded to prevent a false reuse).

### 1.2 `Census.lean` — Step 14, the order-r census carriers + the r ≤ 1 layers

Source: `O9_phaseB_verifybrief_rev5.md` (§§1, 5.1, the r4 FULL-attainment form) and
M08 (`M08-cl6-general_fable.md` §2, Theorem 2 — the r = 0 law, PROVED on paper,
46-strata machine check). The census carrier is fully specified NEW data:

```lean
/-- The order-r census datum: the ledger of stage triples (e_i, h_i, f_i),
    i = 0..r, with e_i, f_i ≥ 1.  Derived: d = ∏ f_i (census field degree —
    O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the period
    e = ∏ e_i, the slot-weight function wt on the mixed-radix φ-monomial index
    set J (a Fintype), the graded pieces G_β, and s(β) = #{j | wt j ≤ β}. -/
structure CensusData where
  r : ℕ
  e : Fin (r + 1) → ℕ
  h : Fin (r + 1) → ℕ
  f : Fin (r + 1) → ℕ
  he : ∀ i, 1 ≤ e i
  hf : ∀ i, 1 ≤ f i
  triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i
  h_coprime : ∀ i, Nat.Coprime (h i) (e i)

namespace CensusData
def d (D : CensusData) : ℕ := ∏ i, D.f i
def period (D : CensusData) : ℕ := ∏ i, D.e i
def J (D : CensusData) : Type := (i : Fin (D.r + 1)) → Fin (D.e i) × Fin (D.f i)
noncomputable def wt (D : CensusData) : D.J → ℕ                      -- unit C0
noncomputable def Gset (D : CensusData) (β : ℕ) : Finset D.J :=
  Finset.univ.filter
    (fun j => D.wt j % D.period = β % D.period ∧ D.wt j ≤ β)         -- unit C0c
noncomputable def attainDim (D : CensusData) (β : ℕ) : ℕ := (D.Gset β).card
noncomputable def s (D : CensusData) (β : ℕ) : ℕ :=
  (Finset.univ.filter fun j : D.J => D.wt j ≤ β).card                -- unit C0c
noncomputable def onLineSlots (D : CensusData) : Finset ℕ            -- unit C0d
end CensusData

/-- C3: (ADM)-FULL is per-datum decidable — the ROOT §3.1 row's "finite lattice
    check" clause, machine-checked at type level. -/
instance : ∀ D : CensusData, Decidable (ADMFull D)

/-- C1: r = 0 automaticity — the ONLY automatic case (ROOT (ADM) row, exact). -/
theorem admFull_of_r_eq_zero {D : CensusData} (hr : D.r = 0) : ADMFull D

/-- C2: the r = 1 displayed criterion (O-9 r4, collapsing to the r3 form at
    f₁ = 1): FULL attainment at β ⟺ β ≥ h₁·((h₁⁻¹β mod e₁) + (f₁ − 1)·e₁). -/
theorem admFull_r1_iff {D : CensusData} (hr : D.r = 1) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots,
      r1Bound D β ≤ β
    -- `r1Bound` uses `D.h_coprime`; no undefined auxiliary proposition occurs.

/-- C6+C7: the census value CEN-W as data: a ℕ-coefficient polynomial in q per
    stratum (p-freeness is BY TYPE), with the padding law census = 0 at
    unattained vertices. -/
noncomputable def censusW (D : CensusData) : Polynomial ℕ                -- unit C4c
theorem censusW_eq_zero_of_unattained {D : CensusData} (h : ¬ Attained D) :
    censusW D = 0

/-- C4 (M08 Theorem 2, the r = 0 / level-1 census law): census = q^E · ∏ M_{λ_S}(q)
    with c_i = Δ(i) + 1 at lattice slots — stated for the level-1 stratum carrier
    `Stratum1` (a Finset-of-boxes datum, unit C4a), as an exact ℕ-count identity
    at every prime power: count = (censusW D).eval q. -/
noncomputable def canonicalStratum1 (D : CensusData) : Stratum1 D

theorem census_r0_law {D : CensusData} (hr : D.r = 0)
    {p N : ℕ} [Fact p.Prime] (q : ℕ) (hq : q = p ^ N) :
    (canonicalStratum1 D).count q = (censusW D).eval q

/-- C5/C5′: the queued r≥1 mathematics is represented by a named hypothesis row,
not by an unproved theorem declaration. The lower scope and both conclusions are
visible fields. Wave 4 proves a constructor for this row. -/
structure CensusValueRows (D : CensusData) : Prop where
  cenW : 1 ≤ D.r → GRBRow D → ADMFull D →
    ∀ (S : StratumR D) {p N : ℕ}, Fact p.Prime → ∀ q : ℕ, q = p ^ N →
      S.count q = (censusW D).eval q
  cenJ : 1 ≤ D.r → GRBRow D → FreshRow D → ADMFull D →
    ∀ (S : JunctionStratum D) {p N : ℕ}, Fact p.Prime → ∀ q : ℕ, q = p ^ N →
      S.count q = (censusW D).eval q

theorem censusValueRows_of_anchoredMarch (D : CensusData)
    (hproof : AnchoredMarchProof D) : CensusValueRows D
```

(CEN-J adds `hFresh : FreshRow D` — unit C5', same shape.) The K5/K6/K7 falsifier
ledgers stay Python-side (`verification/openmath/`); Lean-side the r ≤ 1 layer is
proved, the r ≥ 1 layer is displayed-conditional. Nothing here consumes the two
REFUTED (ADM) forms (the r2 class form, the r3 value form) — they must NOT appear
in any Lean statement (verifier charge for the division lead).

### 1.3 `KCount.lean` — Step 15, the Smith-profile fiber count + (SIB)

Source: `O10_phaseB_attempt_rev2.md` §§1–4 (VERIFIED leaf #6). This uses the
Smith-normal-form API exported by `Mathlib.LinearAlgebra.FreeModule.PID`, but K8a
must first capture the exact declaration available at repository HEAD with a
compiling `#check`. K8b then adapts that generic PID result to the particular Φ
matrix and exposes U, D, V, their inverse identities, and the `Fin n` exponent
indexing used by `MulFiberData`; generic existence alone does not discharge K8.

```lean
/-- K0: truncated valuation on ZMod (p^M) vectors: v(x) := min(v_p(lift x), M),
    minVal over coordinates; the three laws the absorption argument needs
    (v(x+y) ≥ min, v(p^a·x) ≥ min(a + v x, M), finite-difference factorization
    transport: polynomial maps are v-Lipschitz). -/
noncomputable def zmodVal {p M : ℕ} [Fact p.Prime] (x : ZMod (p ^ M)) : ℕ
noncomputable def minVal {p M n : ℕ} [Fact p.Prime] (c : Fin n → ZMod (p ^ M)) : ℕ

/-- K1 (Newton absorption, O-10 §3 Step 3): a v-contractive perturbation of the
    identity is injective.  `hS` is the finite-difference Lipschitz law (supplied
    for polynomial maps by K0's third law). -/
theorem newton_absorption_injective {p M n : ℕ} [Fact p.Prime]
    {S : (Fin n → ZMod (p ^ M)) → (Fin n → ZMod (p ^ M))} {a : Fin n → ℕ}
    (ha : ∀ i, 1 ≤ a i)
    (hS : ∀ c c', minVal (S c - S c') ≥ minVal (c - c')) :
    Function.Injective (fun c => c + fun i => (p : ZMod (p ^ M)) ^ a i * S c i)

/-- K2: injective ⇒ bijective on the finite vector space (Mathlib
    `Finite.injective_iff_bijective` — a one-line cite unit, kept separate so K1
    stays a pure valuation argument). -/

/-- K3: the target subgroup count (O-10 §3 Step 4):
    #{c | ∀ i, p^(max (M − e i) 0) ∣ c i} = p^(Σ i, min (e i) M) = p^(s M).
    Split: K3a single coordinate, K3b the product. -/
theorem card_smithSubgroup {p M n : ℕ} [Fact p.Prime] (e : Fin n → ℕ) :
    Nat.card {c : Fin n → ZMod (p ^ M) //
      ∀ i, (p : ZMod (p ^ M)) ^ (M - e i) ∣ c i} = p ^ (∑ i, min (e i) M)

/-- K7: the fiber chart (O-10 §3 Step 1 + Step 2 packaged): a bijection between a
    nonempty fiber of the level-N multiplication map and the solution set of the
    Smith-diagonalized congruence (⋆⋆).  `MulFiberData` carries: the factor
    polydisc (monic factor degrees d_j, base point, separation level τ with
    (SEP): τ ≥ ρ + 1), the Jacobian-type map Φ, its Smith data (U, D, V — from
    K8), and the quadratic remainder Q with its p^{2τ} factor (K7b).
    K7a = the subset product expansion (`Finset.prod_add`);
    K7c = the chart bijection itself. -/
structure MulFiberData (p : ℕ) [Fact p.Prime] (n N : ℕ) where
  τ : ℕ
  ρ : ℕ
  τ_sep : ρ + 1 ≤ τ
  FactorPoint : Type
  instFactorPoint : Fintype FactorPoint
  base : FactorPoint
  polydisc : Finset FactorPoint
  Fiber : Type
  instFiber : Fintype Fiber
  FiberNonempty : Prop
  SolutionSet : Type
  instSolutionSet : Fintype SolutionSet
  smithExp : FactorPoint → Fin n → ℕ

attribute [instance] MulFiberData.instFactorPoint
attribute [instance] MulFiberData.instFiber
attribute [instance] MulFiberData.instSolutionSet

theorem fiber_equiv_solutions {p n N : ℕ} [Fact p.Prime]
    (F : MulFiberData p n N) (hne : F.FiberNonempty) :
    Nonempty (F.Fiber ≃ F.SolutionSet)

/-- K8 (Lemma 2 half 1): Smith normal form of Φ over ℤ_p exists — transcription
    of Mathlib `Submodule.smithNormalForm` at the matrix of Φ. -/

/-- K9 (Lemma 2 half 2, HARD, wave 4): the Smith exponents are CONSTANT across
    the ρ-separated polydisc.  Until it lands: the named row `SmithStable F`
    (a field-displayed hypothesis, consumed by K5), mirroring the paper's
    Lemma-2 dependency honestly. -/
structure SmithStable {p n N : ℕ} [Fact p.Prime] (F : MulFiberData p n N) : Prop where
  exponents_const : ∀ h ∈ F.polydisc, F.smithExp h = F.smithExp F.base

/-- K5 (THE K-COUNT, O-10 Theorem 1(i)): every nonempty fiber has size exactly
    p^(s M), M = N − τ.  = K7 ∘ K1/K2 ∘ K4 ∘ K3. -/
theorem kcount_fiber_card {p n N : ℕ} [Fact p.Prime] (F : MulFiberData p n N)
    (hS : SmithStable F) (hne : F.FiberNonempty) :
    Nat.card F.Fiber = p ^ (∑ i, min (F.smithExp F.base i) (N - F.τ))

/-- K6 (Theorem 1(ii), the D-8 guard range): M ≥ e_max ⇒ s(M) = ρ (pure Finset
    arithmetic; with K5 this is the p^ρ clause). -/

/-- K10 (Theorem 2, the adapted-cell (SIB) product law, O-10 §4.2): at an
    `AdaptedCell` (structure carrying the (A1)–(A3) clauses of §4.1 as fields),
    the level-N count of the assembled cell is the product of the per-factor
    counts divided by the K5 fiber size — UNCONDITIONAL in factor coordinates.
    The APPLICATION to engine strata is a separate statement consuming the
    named rows K-LOC and (I-τ) (owner BP_III), displayed as binders. -/
structure AdaptedCell (p n N : ℕ) [Fact p.Prime] where
  Factor : Type
  instFactor : Fintype Factor
  toMulFiberData : MulFiberData p n N
  cellCount : ℕ
  factorCount : Factor → ℕ
  sM : ℕ
  domainCount_eq : Nat.card Factor = ∏ j, factorCount j
  fiber_nonempty : toMulFiberData.FiberNonempty

attribute [instance] AdaptedCell.instFactor

theorem sib_product_law {p n N : ℕ} [Fact p.Prime] (A : AdaptedCell p n N)
    (hS : SmithStable A.toMulFiberData) :
    A.cellCount * p ^ A.sM = ∏ j, A.factorCount j
```

### 1.4 `MassId.lean` — Step 17, the D-11 M1 unconditional layer + M3 glue

Source: `D11_massid_phaseB_attempt_rev3.md` §2 (Theorem M1 at its REV-3
in-statement scope) and §4 (M3). Scaffold form = counting: "Haar mass" of a
level-k cylinder event is count/q₀^(k·dim) — no measure theory needed at this
layer (the corpus `TreeSeam.count_tie` already fixed that convention).
The algebraic M1 consequences are targeted conditionally on the named
`BlockCountLaws` row until constructors deriving those laws from the established
O-12 base have landed. No theorem is called unconditional merely because its
premises were stored as carrier fields. M1(c)'s multi-block a.s.
termination (Lemma M2.0) consumes (S1-m)+(DET) and is NOT a unit here — it
rides Step 18b's row display (unit D4's binder list).

```lean
/-- The one-step block carrier contains objects and counts only. -/
structure BlockStrata (E e : ℕ) (q₀ : ℕ) where
  hq : 2 ≤ q₀
  hEe : e ≤ E
  descentCount : ℕ
  cellCount : ℕ
  centerCount : ℕ
  o1Count : ℕ

/-- The hard counting content is an explicit named row, not data smuggled into
`BlockStrata`. Constructors for this row must be derived from the imported O-12
base before any M1 specialization is called unconditional. -/
structure BlockCountLaws {E e q₀ : ℕ} (B : BlockStrata E e q₀) : Prop where
  cell_pos : 0 < B.cellCount
  descent_law : B.descentCount * q₀ ^ E = B.cellCount
  center_law : B.centerCount = q₀
  o1_law : B.o1Count * q₀ ^ E = B.cellCount * q₀

/-- M1a ((O1) kernel value IS the continuation mass): K_e(q₀) = q₀^{1−E} as the
    exact count ratio of the displayed event. -/
theorem kernel_O1_mass {E e q₀ : ℕ} (B : BlockStrata E e q₀)
    (hB : BlockCountLaws B) :
    (B.o1Count : ℚ) / B.cellCount = (q₀ : ℚ) ^ (1 - (E : ℤ))

/-- M1b ((O2)/(O2′), c = 0): K_e(q₀) = q₀^{−E}.  MECH from the same laws. -/

/-- M1c ((O3) resummation): Σ_{L≥1} κ₀^{L−1}·κ₁ = κ₁/(1−κ₀) = (q₀−1)/(q₀^E−1),
    κ₀ = q₀^{−E}, κ₁ = (q₀−1)q₀^{−E} — `tsum_geometric_of_lt_one` over ℝ≥0,
    with κ₀ < 1 from q₀ ≥ 2. -/
theorem kernel_O3_resummed {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 1 ≤ E) :
    ∑' L : ℕ, ((q₀ : ℝ≥0) ^ E)⁻¹ ^ L * ((q₀ - 1) * ((q₀ : ℝ≥0) ^ E)⁻¹)
      = ((q₀ : ℝ≥0) - 1) / ((q₀ : ℝ≥0) ^ E - 1)

/-- M2 (row-sum-one — "Σ = 1 across each row now a THEOREM"): the one-step strata
    partition C_e up to the displayed null/padding set, so the row's mass column
    sums to 1.  Stated over a `RowPartition` hypothesis structure whose fields
    are M1(b)'s disjointness/exhaustion clauses (the D-11 (b) content). -/
theorem row_sum_one {E e q₀ : ℕ} {B : BlockStrata E e q₀} (P : RowPartition B) :
    ∑ s ∈ P.strata, P.mass s = 1

/-- M3' (per-visit termination margin, M1(c)'s per-block half): the continuation
    mass is κ₀ + κ₁ = q₀^{1−E} ≤ 1/2, and k-step survival ≤ 2^{−k} → 0. -/
theorem perVisit_margin {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 2 ≤ E) :
    ((q₀ : ℝ≥0) ^ (E - 1))⁻¹ ≤ 1 / 2
theorem perBlock_exit {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 2 ≤ E) :
    Tendsto (fun k => (((q₀ : ℝ≥0) ^ (E - 1))⁻¹) ^ k) atTop (nhds 0)

/-- M4 ((r1) margins over the VERIFIED O-12 lemma base): the block determinant
    does not vanish at any q₀ = p^δ ≥ 2 — reuse `RegP.detFull_ne_zero` +
    `cycS_eval_pos` (§3); packaged as: RegP transports the margin to every pool
    member. -/
theorem r1_margin_of_regP {p : ℕ} {D : RegData p} (h : RegP D) (e : D.Block) :
    ∀ q₀ ∈ D.Pool, RatFunc.eval (q₀ : ℚ) (D.detFull e) ≠ 0

/-- M7 (M3, row labels are true types — the σ-constancy glue): given the two
    Movement-III rows (O5triple Thm E: per-box lift uniformity; D-15), the true
    type is constant across one continuation event's cylinder.  SEAM(BP_III):
    both rows are binders. -/
theorem trueType_const_on_cylinder {n p : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} (hThmE : ThmERow n p X) (hD15 : D15Row n p X)
    {N : ℕ} (cyl : CylEvent n p N) (hcyl : IsContinuationEvent X cyl) :
    ∀ f g, f ∈ cyl → g ∈ cyl → X.trueType N f = X.trueType N g
```

M1(a″)'s exclusions are enforced STRUCTURALLY: no unit states a mass identity for
family-(iv) arbitrary-α rows, families (vi)/(vii), or the projective weight (S3)
— there is simply no such statement in the module (division-lead verifier charge:
grep the module for `projective` and for α-generic mass claims; must be empty).

### 1.5 `SeriesTie.lean` — Step 18, the resummation core + the tie assembly

Source: `M04-series-tie_fable.md` (Theorem 4's reduction, glue PROVED on paper;
Lemmas 3.1–3.3 self-contained) + `O11_phaseB_attempt.md` r2/r3 (the K1–K4
pricing). The TARGET ROW is the existing corpus field — verbatim:

```lean
-- BridgeKernels.series_tie (MovesU/BridgeKernels.lean:223):
--   series_tie : ∀ σ : SplittingType n,
--     F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
```

The movement produces `seriesTie_of_kernels`, deriving that row from displayed
kernel/hypothesis rows. The abstract core (over `Fin m → ℝ≥0∞`; NO engine
vocabulary — maximal reuse across n):

```lean
/-- S1 (M04 Lemma 3.1 half 1): the Neumann sum solves the affine recursion
    x = b + A·x and is its LEAST solution in (ℝ≥0∞)^m (S1a: solution;
    S1b: leastness by induction on partial sums). -/
noncomputable def neumannSum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ≥0∞ := fun i => ∑' k, (A ^ k).mulVec b i
theorem neumannSum_isLFP {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) :
    neumannSum A b = b + A.mulVec (neumannSum A b)
    ∧ ∀ y, y = b + A.mulVec y → neumannSum A b ≤ y

/-- S2 (Lemma 3.1 half 2, the tree side): any `FiberSeries` whose slice sums
    satisfy the K1 recursion has seriesSum = the lfp.  `TreeRecursion` is the
    hypothesis structure whose fields are EXACTLY what K1 supplies (the O-10
    product law + (SIB)/(JC-multi) rows + CU leaf labels): per-σ, the level-N
    slice sum = entrance row + kernel matrix · level-(N−1) slice sums. -/
structure TreeRecursion {n p m : ℕ} [Fact p.Prime]
    (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞) : Prop where
  stateOf : SplittingType n → Fin m
  slice : ℕ → Fin m → ℝ≥0∞
  slice_zero : slice 0 = b
  slice_succ : ∀ N, slice (N + 1) = b + A.mulVec (slice N)
  series_eq_iSup : ∀ σ, F.seriesSum σ = ⨆ N, slice N (stateOf σ)

theorem seriesSum_eq_lfp {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (hrec : TreeRecursion X F A b) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = neumannSum A b (hrec.stateOf σ)

/-- S3 (Bekić/triangular prefix independence). -/
noncomputable def prefixMatrix {m : ℕ} (k : ℕ)
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) : Matrix (Fin m) (Fin m) ℝ≥0∞ :=
  fun i j => if i.1 < k ∧ j.1 < k then A i j else 0
noncomputable def prefixVector {m : ℕ} (k : ℕ)
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ≥0∞ :=
  fun i => if i.1 < k then b i else 0
theorem neumannSum_blockTriangular {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0) :
    ∀ i, i.1 < k →
      neumannSum A b i = neumannSum (prefixMatrix k A) (prefixVector k b) i

/-- S4: finite Neumann sums agree with every real affine solution under a strict
row-sum margin. -/
noncomputable def matrixToReal {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (A i j).toReal
noncomputable def vectorToReal {m : ℕ}
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ := fun i => (b i).toReal
theorem neumann_eq_solve_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal b + (matrixToReal A).mulVec x) :
    ∀ i, (neumannSum A b i).toReal = x i

/-- S5 (THE TIE ASSEMBLY — the movement's Step-18 capstone): `series_tie` from
    the displayed row list, one binder per ROOT consumption:
    K1 = `hrec : TreeRecursion …` (product law; BP_III's SibJcRows feed it),
    K2 = `hreg : RegP D`, `hpin : RegPin C D`, `hpack : PackCorrespondence n C P`,
    K3 = `hcen : CensusValueRows …` (the census half: binders `hGRB`, `hFresh`,
         `hadm : ADMFull`, `hR14 : R1R4Row`, `hK3δ : K3DeltaRow …`),
    K4 = `hmass : TerminalSeamRows …` + the `TreeSeam` in scope (D-a/K4-CYL).
    Conclusion: the corpus row, verbatim. -/
theorem seriesTie_of_kernels {n p m : ℕ} [Fact p.Prime]
    {C : UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {CD : CensusData} {RD : RegData p} {P : AssembledPack n}
    {R : PackReference n C P}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    {RealizedPool DeltaStablePos : ℕ → Prop}
    (seam : TreeSeam n p X F)
    (K1 : TreeRecursion X F A b)
    (hreg : RegP RD) (hpin : RegPin C RD)
    (hpack : PackCorrespondence n C P R)
    (hGRB : GRBRow CD) (hFresh : FreshRow CD) (hadm : ADMFull CD)
    (hcen : CensusValueRows CD)
    (hR14 : R1R4Row n p X)
    (hK3δ : K3DeltaRow p RD RealizedPool DeltaStablePos)
    (K4 : TerminalSeamRows n p X F) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
```

S5's binder list IS the honest conditionality display: at ROOT REVISION 5, clause
(R)'s attribution is (H1)–(H3) + (H4a) + (H5) + (K3-δ) + (H6) — every one appears
as a named binder, none as an axiom, none silently dropped. The M04 F1 finding is
a standing fence: the DEVICE n = 2 chain (`n2Chain`) must never instantiate S5's
carriers (its Rval triple is refuted against the true densities); only the
S-area's real pack qualifies.

### 1.6 `DensityTie.lean` — Step 18b, density = series (the squeeze) + capstone

Source: `D11_massid_phaseB_attempt_rev3.md` §3 (Theorem M2, MONIC scope — (S3)
projective weight consumed NOWHERE, enforced as in §1.4) + ROOT Step 18b.
The cylinder-limit density is the scaffold's α (THE PROOF SCAFFOLD shape):

```lean
/-- D0: the (lower) cylinder density of type σ — the scaffold's α(n, τ; p),
    counting form: the monotone limit of decided-σ mass.  Monotonicity of
    `dmass` in N is D0a (from `canonical_stable`, same counting as T1). -/
noncomputable def cylDensity {n p : ℕ} [Fact p.Prime] (X : ClassifierSpec n p)
    (σ : SplittingType n) : ℝ := ⨆ N, X.dmass σ N

/-- D1 (slice identity — REUSE, not re-proof): dmass σ N = slice sum, i.e. the
    corpus `TreeSeam.finiteness_stack` (PROVED) recast over ℝ (one ofReal cast
    lemma). -/
theorem dmass_eq_sliceSum {n p : ℕ} [NeZero p] …

/-- D2 (the squeeze): Σ_σ dmass σ N = 1 − env-defect N with defect ≤ env N;
    with `env → 0` (Step 13's delivery) every cylDensity exists as a true limit
    and Σ_σ cylDensity = 1.  (Generalizes the proved n = 2 pattern
    `decided6_lower/upper` in `OM/SeriesAssembly.lean`.) -/
theorem sum_cylDensity_eq_one {n p : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} (henv : Tendsto X.env atTop (nhds 0)) :
    ∑ σ : SplittingType n, cylDensity X σ = 1
    -- needs Fintype (SplittingType n): corpus unit U0b, already landed

/-- D3 (density IS the series, D-11 M2's (S2)-free half): cylDensity =
    (seriesSum's ℝ-value) — from D1 + M04 Theorem 1's ⨆-characterization of
    seriesSum + henv.  D3a: seriesSum σ = ⨆ N (slice sum) (M04 Thm 1, an
    interface lemma over `mem_slice_iff`); D3b: the cast chain. -/
theorem cylDensity_eq_seriesSum {n p : ℕ} [Fact p.Prime] [NeZero p]
    {X : ClassifierSpec n p} {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (henv : Tendsto X.env atTop (nhds 0)) (σ : SplittingType n)
    (hfin : F.seriesSum σ ≠ ⊤) :
    cylDensity X σ = (F.seriesSum σ).toReal

/-- D5 (the (r1) uniqueness pivot): under the margin, the renewal solution is
    UNIQUE (not merely least) — S1b's leastness + S4a's finiteness. -/
theorem renewal_unique_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (b x y : Fin m → ℝ)
    (hmargin : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ i, ∑ j, |A i j| ≤ ρ)
    (hx : x = b + A.mulVec x) (hy : y = b + A.mulVec y) :
    x = y

/-- D4 (THE MOVEMENT CAPSTONE — α = R_τ at the full displayed hypothesis set). -/
theorem valueSide_massTie {n p m : ℕ} [Fact p.Prime] [NeZero p]
    {C : UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {CD : CensusData} {RD : RegData p} {P : AssembledPack n}
    {R : PackReference n C P}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    {RealizedPool DeltaStablePos : ℕ → Prop}
    (seam : TreeSeam n p X F)
    (K1 : TreeRecursion X F A b)
    (hreg : RegP RD) (hpin : RegPin C RD)
    (hpack : PackCorrespondence n C P R)
    (hGRB : GRBRow CD) (hFresh : FreshRow CD) (hadm : ADMFull CD)
    (hcen : CensusValueRows CD)
    (hR14 : R1R4Row n p X)
    (hK3δ : K3DeltaRow p RD RealizedPool DeltaStablePos)
    (K4 : TerminalSeamRows n p X F)
    (henv : Tendsto X.env atTop (nhds 0)) :
    ∀ σ : SplittingType n,
      cylDensity X σ = C.chain.Rval (vmap C.T σ) (p : ℚ)
```

---

## 2. UNIT TABLE

Legend: MECH = definition/cite/omega-grade; EASY ≤ ~15 lines of real proof;
MED = one genuine idea, ≤ ~40 lines; HARD = queued core (wave 4), statement
lands early, proof is its own dedicated effort. "src" = blueprint-source
paragraph. Deps name unit ids; corpus imports are in §3.

### Hyps (H)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| H1 | `ADMFull` structure in `CensusCore.lean` | definition after C0's finite datum interface; no reverse import | C0 | MECH | ROOT §3.1 (ADM) row |
| H2a | `AssembledPack` with installed `Fintype` and one-based block bounds | definition only | — | MECH | ROOT §3.1 (PACK) |
| H2b | `PackReference` and `PackCorrespondence` | datum-indexed reference and entry/block equalities | H2a | MECH | ROOT §3.1 (PACK); D11 r3 §5 clause 4 |
| H3 | `K3DeltaRow` | records `depthSet ↔ RealizedPool` and stability of every realized δ | — | MECH | ROOT §3.1 (UB-X)(b)/(K3-δ) |
| H4 | imports of the actual BP_III/BP_V row modules | no local declarations or aliases; first consumers wait for owner modules | — | MECH | §1.0 table |

### Transfer (T) — Step 13

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| T0 | `card_boxProj_fiber` | per-coordinate: fiber of `ZMod.castHom` has size p^(N'−N); product over Fin n | — | EASY | O4T brief §2 (level bookkeeping) |
| T1 | `env_antitone` | undec(N') classes inject into lifts of undec(N) classes via `canonical_stable`; count with T0 | T0 | EASY | O4T §2 TR-0 prelim |
| T2 | `env_le_of_undec_subset` (FLOOR) | subtype injection ⇒ Nat.card mono; divide | — | MECH | O4T §2 FLOOR |
| T3 | `env_tendsto_zero_of_majorant` (TR-Q skeleton) | antitone + vanishing along cofinal unbounded g ⇒ vanishing (squeeze on filters) | — | EASY | O4T §2 TR-Q (UNBOUNDED hyp displayed) |
| T4a | `discV` def: truncated discriminant valuation of `Box.toPoly` | resultant/discriminant of the level-N polynomial, `Polynomial.disc` or resultant formula; valuation in ZMod via zmodVal | K0 | MED | O4T §3.1; LIT-8c |
| T4 | `DrainageImports` structure + `undec_subset_tail`: CEIL ⇒ Undec(N) ⊆ {discV ≥ N} | set inclusion from the ceiling inequality | T4a | EASY | O4T §3.4 N3-ENV step 1 |
| T5 | `env_le_tail`: env N ≤ tailC·p^(−(N−1)/(2(n−1))) | T4's inclusion + card mono + the `tail` field | T4 | EASY | O4T §3.4 N3-ENV step 2 |
| T6 | `env_tendsto_zero_of_imports` | T5's bound → 0 (exponential decay) + T3 | T3,T5 | EASY | O4T §3.4 N3-ENV |
| T7 | HARD (wave 4): the CEIL clause at 2 ≤ n ≤ 3 — discharge `DrainageImports.ceil` for the canonical order-≤1 classifier | the Theorem-N3 (CEIL) chains ((I1) "> 0" criterion per rev 4, Krasner via M05 Lemma D, Facts SEP/DES) — a dedicated formalization campaign | T4a + OM engine | HARD | O4T §3.2–3.4, rev-4 dispositions |
| T8 | HARD (wave 4): the `tail` clause (I-TAIL counting form) | Lemma C's discriminant tail count: resultant divisibility ⇒ coefficient constraints; wild shift n·v_p(n) additive | T4a | HARD | M05 Lemma C; O4T §3.1 (THREE imports note) |

### Census (C) — Step 14

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| C0 | `CensusData` + `d/period/J/wt/Gset/attainDim/s/onLineSlots` + Fintype instances | definitions; wt = the mixed-radix φ-monomial weight (O9 ledger LED) | — | MECH | O9 brief §1 (A1/TRI/LED) |
| C1 | `admFull_of_r_eq_zero` | at r = 0, J = Fin e₀ × Fin f₀, wt affine in the single digit; count the f₀ on-line j directly | C0,H1 | MED | O9 r4 (automaticity: r = 0 ONLY) |
| C2a | `r1Bound` def (the displayed r = 1 RHS h₁((h₁⁻¹β mod e₁)+(f₁−1)e₁)) | definition (needs h₁ invertible mod e₁: `coprimeHyp` field) | C0 | MECH | O9 r4 display |
| C2 | `admFull_r1_iff` | both directions by counting Gset at r = 1: the ≤ β window catches all f₁ residue copies iff β clears r1Bound | C1,C2a | MED | O9 r4 (r = 1 decidable inequality) |
| C3 | `Decidable (ADMFull D)` instance | Finset.decidableBAll over onLineSlots | C0,H1 | MECH | ROOT (ADM) row "per-datum DECIDABLE" |
| C4a | `Stratum1` carrier (level-1 stratum as Finset of boxes with per-coordinate windows c_i = Δ(i)+1) | definition | C0 | MECH | M08 §2.1 |
| C4b | vertex-chain telescope (M08 Lemma D): the chain-aggregated count factors ∏ M_{λ_S}(q) | telescoping product over the chain; each factor a geometric window count | C4a | MED | M08 §2.6 |
| C4c | `censusW` def + `census_r0_law` (M08 Theorem 2) | C = q^E · Z_D = q^E ∏ M_{λ_S}(q); assemble C4b + the per-coordinate factorization | C4a,C4b | MED | M08 §2.6 Thm 2 |
| C5 | `census_law_of_grb` (CEN-W, r ≥ 1) — statement lands wave 0, proof HARD wave 4 | the anchored-march transport: (GR-B) digit read = surjective F_q-linear map on graded piece ⇒ each digit costs q^d; E′ strict left tail floor(line)+1 | C0,C4c,H1,H4(GRB) | HARD | O9 brief §5.1 + r2 E′ repair |
| C5' | CEN-J variant (adds `hFresh`) — statement only this campaign | same + junction pin kills (q^d−1)^ε | C5,H4(FRESH) | HARD | O9 CEN-J |
| C6 | p-freeness by type: `censusW : Polynomial ℕ` + eval nonneg | by construction; one `simp` lemma | C4c | MECH | ROOT Step 14 "one ℕ-valued polynomial" |
| C7 | `censusW_eq_zero_of_unattained` | padding value 0 by definition of censusW at unattained vertices | C4c | EASY | ROOT (ADM) row, padding clause |

### KCount (K) — Step 15

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| K0 | `zmodVal/minVal` + three valuation laws | lift-based def; `min` juggling with `omega`; finite-difference factorization P(c)−P(c') = Σ δ_i G_i via `Finset.prod`-telescope | — | MED | O10 §3 Step 3 (valuation conventions) |
| K1 | `newton_absorption_injective` | the w := minVal δ contraction: v(δ_i) ≥ min(M, 1+w) ⇒ w ≥ M ⇒ δ = 0 | K0 | MED | O10 §3 Step 3 |
| K2 | injective ⇒ bijective (cite) | `Finite.injective_iff_bijective` | K1 | MECH | O10 §3 Step 3 |
| K3a | single-coordinate subgroup card: #(p^a · ZMod(p^M)) = p^(M−a) | ZMod ideal card; possibly `ZMod.card_multiples` or direct orbit count | — | EASY | O10 §3 Step 4 |
| K3b | `card_smithSubgroup` product form | product of K3a over Fin n; `Nat.card_pi` | K3a | MECH | O10 §3 Step 4 |
| K4 | per-coordinate equivalence: (⋆⋆)_i ⟺ T(c)_i ≡ 0 mod p^(M−e_i); vacuous at e_i > M | unit-cancel p^{e_i}; ZMod divisibility shuffle | K0 | MED | O10 §3 Step 4 |
| K7a | subset product expansion Π(h_j+a_j) − Π h_j = Σ_{|S|≥1} …  | `Finset.prod_add` + split |S| = 1 vs ≥ 2 | — | EASY | O10 §3 Step 1 |
| K7b | the p^{2τ} extraction: Q(p^τ b) = p^{2τ} Q̃(b), Q̃ ℤ_p-coefficients | factor p^{τ|S|}, |S| ≥ 2 | K7a | EASY | O10 §3 Step 1 |
| K7c | `MulFiberData` + `fiber_equiv_solutions` | monic-lift parametrization (differences of monics = degree-< d_j polys, p^τ-divisible); mod-p^N well-definedness; assemble (⋆) | K7a,K7b | HARD (borderline MED; the one big glue) | O10 §3 Steps 1–2 |
| K8a | PID Smith theorem availability gate | import `Mathlib.LinearAlgebra.FreeModule.PID`; use `#check` to record the exact declaration available at repository HEAD before fixing the adapter proof | — | MECH | O10 §2 Lemma 2 half 1 |
| K8b | `SmithData` adapter for the particular Φ matrix | instantiate the checked PID theorem, then expose the concrete U/D/V matrices, inverse laws, diagonal equality, and `Fin n` exponent indexing required by `MulFiberData` | K8a,K7d | MED | O10 §2 Lemma 2 half 1 |
| K9 | HARD (wave 4): `SmithStable` discharge (exponent constancy on the polydisc) | Lemma 2's ρ-separation argument (resultant lower bounds); until landed the row is a displayed hypothesis | K8 | HARD | O10 §2 Lemma 2 |
| K5 | `kcount_fiber_card` (Theorem 1(i)) | chart K7c; change variables (V bijection); K4 reduces to subgroup membership; K1/K2 bijection T; count K3b | K1–K4,K7c,K8 | EASY (glue) | O10 §3 Thm 1(i) |
| K6 | guard range (Theorem 1(ii)): M ≥ e_max ⇒ Σ min(e_i,M) = ρ | `Finset.sum_congr` + `min_eq_left`; omega | — | MECH | O10 §3 Thm 1(ii) |
| K10a | `AdaptedCell` structure ((A1)–(A3) as fields) | definition | K7c | MECH | O10 §4.1 |
| K10b | constant-fiber image theorem | combine the concrete cell map, nonempty fibers, and K5's exact fiber cardinality | K5,K10a + O5CountingB | MED | O10 §4.2 |
| K10c | domain-product cardinality | identify the domain with the product of factor cells | K10a | EASY | O10 §4.2 |
| K10 | `sib_product_law` in multiplicative form | combine K10b and K10c; no truncated division | K10b,K10c | EASY | O10 §4.2 |
| K11 | `EngineSIBRow` named structure consuming actual K-LOC and (I-τ) rows | a Wave-4/owner constructor supplies the application; never an unproved theorem declaration | K10,H4 | MECH | O10 §4.3/§5.3 |

### MassId (M) — Step 17

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| M0a | `BlockStrata` carrier without mathematical laws | definition of counts and indices only | — | MECH | D11 §1 |
| M0b | named `BlockCountLaws` row | explicit L1/L2/L3 count hypotheses; no axiom and no claim of unconditionality | M0a | MECH | D11 §1 |
| M1a | `kernel_O1_mass` conditional on `BlockCountLaws B` | field algebra from the named row | M0b | EASY | D11 §2 (a) (O1) |
| M1b | (O2) value q₀^{−E} | same, c = 0 | M0 | MECH | D11 §2 (a) (O2) |
| M1c | `kernel_O3_resummed` | geometric `tsum` over ℝ≥0, ratio κ₀ = q₀^{−E} < 1 | — | EASY | D11 §2 (a) (O3) |
| M2 | `row_sum_one` | Finset.sum over the partition fields; disjointness+exhaustion ⇒ counts add to cellCount | M0 | EASY | D11 §2 (b) |
| M3' | `perVisit_margin` + `perBlock_exit` | q₀^{1−E} ≤ 2^{1−E} ≤ 1/2; geometric `Tendsto` (pattern: `tendsto_envBound_zero`) | — | EASY | D11 §2 (c) per-block half |
| M4 | `r1_margin_of_regP` | `RegP.detFull_ne_zero` + `regP_iff_pool_avoids`; evaluate via `cycS_eval_pos` at x = q₀ ≥ 2 | — | MED | D11 §2 (c) (r1); O-12 lemma base |
| M5 | divisor-pattern mass row (family (ii)): m(π)(q₀) = q₀^{−(E−e)}·N_π(q₀)·q₀^{−e} | field algebra over M0 + a `pattCount` field (Fact F(ii) as a law) | M0 | EASY | D11 §2 (a) divisor bullets |
| M6 | polygon-family cell mass (family (iii)): per-cell (1−q₀^{−1})^k·q₀^{−N(P)} + affine-cone geometric sum | cone sum = product of geometric series (c_j ≥ 1); `tsum_geometric` per axis + Fubini for finitely many axes | M1c | MED | D11 §2 (a) polygon bullet (L6a/L6b/L6e) |
| M7 | `trueType_const_on_cylinder` (M3 glue) | two-row transport: Thm E gives per-box σ-constancy of lifts, D-15 the per-box uniformity; chain across the cylinder | H4 | EASY | D11 §4 |
| M8 | M1′ gate object (the recorded concrete α₂ row at n = 2) — OPTIONAL | one concrete Finset computation | M0 | MECH | D11 §2 M1′ |

### SeriesTie (S) — Step 18

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| S1a | `neumannSum` solves x = b + A·x | ℝ≥0∞ tsum shift: Σ_{k} A^{k+1}b = A·Σ A^k b (ENNReal.tsum commutes with mulVec — finite sums) | — | MED | M04 Lemma 3.1 |
| S1b | leastness | induction: partial sums ≤ any solution; `iSup` ≤ | S1a | MED | M04 Lemma 3.1 |
| S0 | seriesSum is the supremum of slice sums | proved in `SeriesTie.lean`, so this file has no dependency on `DensityTie.lean` | — | MED | M04 Thm 1 |
| S2a | recursion identifies every finite slice with a partial Neumann sum | induction on N using `TreeRecursion.slice_zero/slice_succ` | S1a | MED | M04 Thm 4 K1 leg |
| S2b | `seriesSum_eq_lfp` | combine S0, S2a, and monotone convergence | S0,S1b,S2a | MED | M04 Thm 1 + Thm 4 K1 leg |
| S3a | Bekić 2×2 block | substitute the solved lower block; verify both lfp properties | S1a,S1b | MED | M04 Lemma 3.2 |
| S3b | full triangularization | induction on blocks via S3a | S3a | MED | M04 Lemma 3.2 |
| S4a | summability from margin | row-sum ρ ≤ q₀^{1−E} ≤ 1/2 (M3') ⇒ ‖A^k b‖ ≤ 2^{−k}‖b‖; comparison | M3' | MED | M04 Lemma 3.3 |
| S4b | (1−A)·neumannSum = b over ℝ≥0 (finite regime) | telescope on partial sums; pass to limit by S4a | S4a | MED | M04 Lemma 3.3 |
| S4c | agreement with the RatFunc solve value at q₀ under RegP | Cramer: (1−K_e(q₀)) invertible by M4; solution unique (S1b + finiteness) = matrix solve; tie to `SolveSeam.r_is_solve`'s `Rsh` | S4b,M4 | HARD (borderline MED; evaluation plumbing) | M04 Lemma 3.3 + O11 K2 |
| S5 | `seriesTie_of_kernels` | assemble: S2 (K1) + S3 (block order) + S4 (K2) + census value rows (K3: C5/C5'/H1/H3/H4) + K4 rows; conclusion = the corpus row verbatim | S2,S3b,S4c,H1–H4,C5 | MED (pure glue, big binder list) | M04 Thm 4; O11 r3 §tiers |

### DensityTie (D) — Step 18b

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| D0a | `dmass` monotone in N | same counting as T1 on decided classes | T0 | EASY | scaffold shape |
| D0 | `cylDensity` def | definition (⨆) | D0a | MECH | THE PROOF SCAFFOLD (cylinder-limit density) |
| D1 | `dmass_eq_sliceSum` | cast `TreeSeam.finiteness_stack` (PROVED corpus) to ℝ; divide by p^{nN} | — | EASY | D11 §3 (R-read); corpus reuse |
| D2 | `sum_cylDensity_eq_one` | Σ_σ decided + undec = p^{nN} (box partition); env → 0 squeeze; generalize `decided6_lower/upper` | D0a,T1 | MED | D11 M2 proof; SeriesAssembly pattern |
| S0 | seriesSum σ = ⨆_N slice sums, located in `SeriesTie.lean` | `mem_slice_iff` monotone slices; ℝ≥0∞ `iSup` of monotone Finset sums = tsum | — | MED | M04 Thm 1 |
| D3 | `cylDensity_eq_seriesSum` | D1 + imported S0 + toReal cast under `hfin` | D1,S0 | MED | D11 M2 (S2) leg |
| D5 | `renewal_unique_of_margin` | least solution + any solution differ by a fixed point of A; margin kills it | S1b,S4a | MED | D11 (r1) pivot |
| D4 | `valueSide_massTie` (CAPSTONE) | pointwise rewrite by D3 and S5; D2 is not used | D3,S5 | EASY (glue) | ROOT Step 18b |

No aggregate unit-count claim is made: composite rows are split at assignment
time as listed in §4. In particular C0, K0, K7c, K10, M0, M6, S2, S3b, S4c,
and S5 are multi-unit chains, each assignment targeting one definition or one
proof idea and approximately 40 Lean lines or fewer. T7, T8, C5/C5′, and K9
export named hypothesis structures until their dedicated constructor proofs land.
Every wave boundary is zero-`sorry`.

---

## 3. CORPUS-REUSE MAP (existing proved declarations → units they discharge/serve)

All reuse is BY IMPORT; nothing is moved or restated. Declaration names verified
against HEAD (2ab2a48).

| corpus declaration (file) | what it is | serves units |
|---|---|---|
| `TreeSeam.finiteness_stack` (`MovesU/DefsLedger.lean:248`) | PROVED: decided_σ(N) = p^{nN}·Σ_{thr≤N} mass | D1 (verbatim engine; D1 is a cast wrapper) |
| `TreeSeam.count_tie` field (`DefsLedger.lean:241`) | the per-tree fiber count row | D1, S2's `TreeRecursion` design |
| `ClassifierSpec.decided/undec/env/dmass` (`MovesU/Defs.lean`) | the counting vocabulary | T1–T6, D0–D4 (no new defs needed) |
| `ClassifierSpec.canonical_stable` (`Defs.lean`) | decision stability | T1, D0a |
| `FiberSeries.seriesSum/thrSlice/mem_slice_iff/slice_mono` (`Defs.lean`) | the series carrier + slice laws | S2, D3a |
| `BridgeKernels.series_tie` row (`MovesU/BridgeKernels.lean:223`) | THE TARGET ROW (owner [3t]) | S5's conclusion shape (byte-matched) |
| `BridgeKernels.env_tendsto` row (`BridgeKernels.lean`) | CL-4's envelope row | T6's conclusion shape |
| `SolveSeam` (+ `r_is_solve`, `R_defined`) (`DefsLedger.lean:578`) | the solve pin to `MovesS.Rsh` | S4c, S5 (K2 leg) |
| `RegP.detFull_ne_zero`, `RegPin.detFull_eq`, `regP_iff_pool_avoids`, `RegData.zeroPoleSet` (`MovesU/RegPFinite.lean`) | M17's (REG-p) dictionary, PROVED; supports nonzero evaluation, not a pole predicate | M4, S4c |
| `cycS_eval_pos`, `MemRcyc.*`, `memRcyc_inv_cycS`, `MemRcyc.eq_div` (`MovesU/O12PoleFree.lean`) | O-12's 𝒮-positivity/localization layer, PROVED | M4 (nonvanishing at q₀ ≥ 2), S4c |
| `surj_of_injOn_checksum`, `bijOn_of_injOn_checksum`, `card_eq_of_injOn_checksum` (`MovesU/O5CountingB.lean`) | O5triple Theorem B's counting core | K10 (image/fiber count), M2 (partition count option) |
| `UCarriers.cl11_ksub_general`, `ksub_exists_form`, `ksubM1C1T_of_degCons` (`MovesU/KsubGeneral.lean`) | (K-SUB) m = 1 classification, general n | S5's K3 leg (the m = 1 verdict-row value fragment) |
| `UCarriers.detHyp`, `RegPin.act_agree` (`RegPFinite.lean`) | Theorem B wired to carriers | M4, S4c |
| `hExhaust_n2`, `envBound_le`, `tendsto_envBound_zero`, `decided6_lower/upper`, `undecided_envelope` (`OM/SeriesAssembly.lean`) | the n = 2 OM-model drainage + squeeze, PROVED | T3/T6/D2 as the PATTERN + the n = 2 gate; NOT a discharge of `env_tendsto` at the bridge model (different model — D19 agreement seam; fence recorded §1.1) |
| `runRealizerExists_zmod` (`MovesD/R7_runRealizer.lean:543`) | R7 realizer supply (prime field) | no direct unit; S2's `TreeRecursion` instances at n ≤ 3 gates (via BP_III) |
| `sigmaV_vertexLaw`, `readVertex_e1`, `readBox_e1` (`HC2/HK11a_vertexTransport.lean`) | the e′ = 1 vertex read laws | K11's engine application; S5 K3-c β-leg instances |
| `vtx_m6bi_n4upper`, `vtx_htUpper_div` (`HC2/UE_vtxUpper.lean`) | WGEO/VTX degree-1 perimeter | K11 (adapted-cell guard arithmetic at the engine site) |
| D-SC slot layer: `SlotsG14_relSite` … `SlotsG19e_valueFalsifiers` (`MovesU/Slots*.lean`) | the sited value-law carriers + falsifier gates | S5's K3 keying: `CensusValueRows` should be STATED over the SlotsG15 `SiteData` carriers, not re-invented — E-phase instruction to the prover |
| `n2_polyGeomLaws_nonempty` (`MovesS/N2PolyGeom.lean`, per BridgeKernels cl6 docstring) | the n = 2 value+degree law witness | S5's cl6-adjacent gates at n = 2 |
| `Fintype (SplittingType n)` (corpus unit U0b) | finiteness of the type menu | D2's Σ_σ |
| Mathlib PID Smith-normal-form API (`Mathlib.LinearAlgebra.FreeModule.PID`) | exact declaration name and arguments must be captured by K8a's compiling `#check`; K8b supplies the problem-specific U/D/V adapter | K8a,K8b |
| Mathlib: `Finset.prod_add` | subset-expansion of products | K7a |
| Mathlib: `Finite.injective_iff_bijective` | finite injectivity upgrade | K2 |
| Mathlib: `tsum_geometric_of_lt_one` (ℝ≥0), `ENNReal.tsum_*` | geometric resummation | M1c, M6, S1a, S4a |
| Mathlib: `tendsto_const_div_atTop_nhds_zero_nat`, squeeze lemmas | envelope limits | T3, M3', D2 |

**Known-absent (checked, do NOT hunt):** no existing Lean census polynomial at
general r (MovesS's `RS4Chain`/`N2PolyGeom` are n = 2 value-law instances — gates
for C4c/C5's n = 2 shadows, not engines); no existing SNF-over-ℤ_p application;
no existing abstract Neumann/Bekić layer (M04's Lemmas 3.1–3.3 were paper-only).

---

## 4. WAVE PLAN (for the division lead)

Waves are dependency-closed; within a wave every unit is independently assignable
to one prover. Per-file `lake env lean` gate after each unit; `lake build` +
`LeanUrat/AxChk_baseline.lean` at each wave boundary. Prover prompts carry the
64k staged-write discipline and the statement fence (no signature edits without
division-lead sign-off).

**Wave 0a — independent carrier roots:**
C0a (`CensusData`) ; H2a ; H3 ; K0a (`zmodVal`) ; M0a (`BlockStrata`) ;
module skeletons, including `CensusCore.lean`. No unit in this subwave depends on
another unit in the subwave.

**Wave 0b — carrier derivatives:**
C0b (`d/period/J`), then C0c (`wt/Gset/attainDim/s`), then C0d
(`onLineSlots`), each gated before its dependents; H1 after C0d; H2b after H2a;
K0b (`minVal`) after K0a; M0b (`BlockCountLaws`) after M0a. Actual BP_III/BP_V
row modules must already compile before H4 is marked complete.

**Wave 1a — independent easy roots:**
T0, T2, T3 ; K3a, K6, K7a ; M1c, M3' ; D1 ; S0.
**Wave 1b — easy dependents:**
T1 after T0; K3b after K3a; K7b after K7a; D0a after T0, then D0; C3 after H1;
C6 and C7 only after C4c in Wave 2; K2 only after K1 in Wave 2.
Every declaration is proved in the same wave in which its theorem statement is
introduced; there are no “statement-only” theorem declarations.

**Wave 2 — dependency-ordered MED chains:**
T4a → T4b → T4 → T5 → T6;
C1, C2a → C2, C4a → C4b → C4c → {C6,C7};
K0b → K1 → K2, K4, and K8a;
M0b → {M1a,M1b,M2,M5}, plus M4, M6a → M6b, M7;
S1a → S1b, S3a, S4a; D0 → D2, and D1+S0 → D3; S1b+S4a → D5.
Items separated by an arrow are serial assignments, not parallel work.

**Wave 3 — split glue chains:**
K7b → K7c (monic parametrization) → K7d (quotient well-definedness) →
K7e (`fiber_equiv_solutions`) → K8b → K5 → K10b (constant-fiber map) →
K10c (domain-product identification) → K10; K11 is an `EngineSIBRow`
hypothesis structure until its owner proof lands.
S0+S1b → S2a → S2b; S3a → S3b1 (one induction step) → S3b2;
S4a → S4b → S4c1 (finite evaluation) → S4c2 (SolveSeam agreement);
then S5a (state/block reindexing) → S5b (`seriesTie_of_kernels`) → D4.
No file in this chain imports `DensityTie.lean`; `DensityTie.lean` imports the
completed `SeriesTie.lean`.

**Wave 4 — dedicated HARD constructors:**
T7 and T8 construct the two fields of `DrainageImports`; C5/C5′ prove
`censusValueRows_of_anchoredMarch`; K9 proves a constructor of `SmithStable`.
Their named row structures may be consumed earlier, but no theorem asserting the
hard content is introduced before its proof. Consumers remain conditional.

After every unit, run `lake env lean` on the modified file. After every numbered
wave, run full `lake build` and `LeanUrat/AxChk_baseline.lean`. A subwave does not
start until all dependency predecessors and owner-module imports pass their gates.

**Failure protocol:** a unit refuted at statement level (type error traceable to
this blueprint's sketch) escalates to the blueprint owner (me) for a signature
fix + ledger note — never a silent prover-side restatement. A unit stalled twice
returns to the division lead with the compiled obstruction attached (repo
standing practice).

---

## 5. Cross-blueprint seams + revision-sync duty

* **BP_III (dictionary/CU movement):** owns GRBRow, FreshRow, TerminalSeamRows,
  ThmERow, D15Row, K-LOC, (I-τ), and the `TreeRecursion`-feeding product-law
  instances (SibJcRows). Their real datum-indexed modules are prerequisites for
  C5/C5′/K11/M7/S5; BP_IV defines no aliases and permits no later signature re-key.
* **BP_V (UB/O-8b movement):** owns R1R4Row and `DeltaStablePos`. Their actual
  modules are prerequisites for H3's consumers; `K3DeltaRow` additionally records
  equality between `RegData.depthSet` and the realized-pool predicate.
* **BP_VI / spine architect:** D4's `valueSide_massTie` is Movement IV's export to
  the root assembly; its binder list must be consumed VERBATIM by the spine's
  clause-(R) statement (any spine-side weakening of the binder list is a
  statement-fence event).
* **Math-revision sync:** O-9 is VERIFIED at r5 and O-10/O4T are VERIFIED — low
  churn expected; D-11 (pass 3 owed) and O-11 (r3, pass owed) are LIVE — if their
  next passes force statement changes, the M and S blocks re-sync BEFORE wave 3
  launches (the D-11/O-11 units deliberately sit in waves 2–3, latest possible).
  The (ADM) row history (two REFUTED forms) is a standing verifier charge: any
  Lean statement matching the r2-class or r3-value form is a stop-the-line defect.

— BP_IV architect (Fable), conversion swarm, per the 2026-08-03 ledger authority.

## REVISION 2 (review fold, 2026-08-03)

| finding | disposition | where/why |
|---|---|---|
| 1 | FIXED | §1.0 and module map introduce acyclic `CensusCore.lean`; `ADMFull` lives beside `CensusData`. |
| 2 | FIXED | §§1.0, 1.3, 1.5, and 1.6 now display complete signatures for pack, fiber, cell, recursion, Neumann, uniqueness, and both capstones; free identifiers and ellipses are removed. |
| 3 | FIXED | §4 introduces theorem statements only with their proofs; C5/C5′ and K11 are named hypothesis structures pending dedicated constructors. |
| 4 | FIXED | §4 is dependency-ordered into subwaves; K1 precedes K2, C4c precedes C6/C7, K7 units are serial, and duplicate/serial Wave-0 assignments are removed. |
| 5 | FIXED | S0 moved to `SeriesTie.lean`; `SeriesTie.lean` no longer imports `DensityTie.lean`, while `DensityTie.lean` imports SeriesTie. |
| 6 | FIXED | `DrainageImports` records `2 ≤ n ≤ 3`, so T6 has the decay denominator scope required by CEIL. |
| 7 | FIXED | S5 explicitly binds GRB, FRESH, ADM-FULL, `CensusValueRows`, R1–R4, K3-δ, and H6 with complete types. |
| 8 | FIXED | H4 proposition aliases are prohibited; actual owner structures are compile-time prerequisites. |
| 9 | FIXED | `PackReference` scopes `C` and `P` dependently, while `AssembledPack.blockOf` is a one-based natural with bounds. |
| 10 | FIXED | `CensusValueRows.cenW` explicitly requires `1 ≤ D.r`. |
| 11 | FIXED | `census_r0_law` applies to the constructed `canonicalStratum1 D`, not every arbitrary carrier. |
| 12 | FIXED | Count laws moved from `BlockStrata` into the named `BlockCountLaws` hypothesis row; M1 is described as conditional until O-12-derived constructors land. |
| 13 | FIXED | K10 concludes the exact multiplicative identity `cellCount * p^sM = ∏ factorCount`, avoiding truncated division. |
| 14 | FIXED | M4 now concludes nonzero rational-function evaluation, exactly matching the cited reuse facts, rather than absence of a pole. |
| 15 | FIXED | C0 uses `Finset.univ.filter` and explicit cardinality; finite instances are supplied by the dependent `Fin`/Pi carrier. |
| 16 | FIXED | `CensusData` now contains named triangular and modular-coprimality rows; the undefined `coprimeHyp` binder is removed. |
| 17 | FIXED | `AssembledPack.instR` and the analogous fiber/cell instances are explicitly installed with `attribute [instance]`. |
| 18 | FIXED | `K3DeltaRow` records `depthSet_iff_realized` and quantifies stability over the realized-pool predicate. |
| 19 | FIXED | K8 is split into an exact-API `#check` gate and a problem-specific U/D/V adapter with concrete indexing. |
| 20 | FIXED | K10 is split into constant-fiber, domain-product, and multiplicative-cardinality units; O5 counting is cited only for the image/counting step. |
| 21 | FIXED | §4 and the unit-count paragraph split all flagged composites into one-definition/one-idea assignments capped near 40 lines. |
| 22 | FIXED | D4 depends only on D3 and S5; the spurious D2 edge is removed. |
| 23 | FIXED | Unsupported totals “58/48” are deleted; the blueprint uses explicit split chains instead of unreliable aggregate arithmetic. |
| 24 | FIXED | T7 now has a complete signature with explicit `2 ≤ n`, `n ≤ 3`, and the concrete `canonicalOrderLEOne` classifier. |

## REVISION 3 (mop-up adjudications, 2026-08-01)

**Provenance.** The division run proved 69/88 units; SEVENTEEN were BLOCKED in
three classes (missing-root cascades, refuted statements with compiled
countermodels, ill-typed displays).  The first mop-up architect pass was
rate-limit-killed mid-work (its landed half committed by the WIP sweep at
ce9b384, in-file provenance blocks already citing "BP_IV REVISION 3"); this
section is that promised blueprint-side record, covering BOTH passes.  Every
repaired statement below is compile-verified in its landed module; the whole
`Scaffold/ValueSide/` set builds green at this revision's commit with exactly
ONE honest `sorry` (T7's per-cluster core, disposition below).  Adjudication
charter: fix the CARRIER and keep the law when the transcription was wrong;
re-scope minimally with the countermodel displayed as warrant when the law was
false as scoped; opaque-parameter the cross-blueprint rows that BP_III/BP_V
never chartered; never weaken silently.

### R3.1 The seventeen blocked units — disposition table

| unit | class | old (this blueprint's display) | new (landed) | warrant |
|---|---|---|---|---|
| C0d | missing root | `onLineSlots` signature only, no body | `onLineSlots D := Finset.image D.wt Finset.univ` (`CensusCore.lean`) — the O9 §2 TRI bullet's v = 0 fundamental layer of the on-line lattice `{e·v + wt(𝐣)}` | carrier holds no polygon datum, so the ledger-attained weights are the canonical finite slot set; the alternative (all lattice points ≤ max wt) is REFUTED against C1 (contains sub-weight class points with attainDim = 0 ≠ d); body flagged for Codex ratification |
| H1 | cascade (C0d) | §1.0 `ADMFull` display | landed VERBATIM in `CensusCore.lean` immediately after the derived defs | pure cascade; no change |
| C1 | REFUTED | statement `admFull_of_r_eq_zero` (kept) over the pre-revision C0 carrier | statement UNCHANGED, PROVED over the REVISION-3 carrier (R3.3) | compiled countermodel `C1Refutation.not_admFull_cmC1` (r = 0, e₀ = 2, h₀ = 1, f₀ = 1: attainDim 0 = e₀·f₀ = 2 ≠ 1 = d), git 33656d2; the CARRIER was wrong, the LAW right |
| C2 | REFUTED both directions | statement `admFull_r1_iff` (kept) over the pre-revision carrier | statement UNCHANGED, PROVED via the pointwise core `attainDim_eq_d_iff_r1Bound_le` | compiled countermodels `C2Refutation.*` (both directions), git 33656d2; same carrier root cause as C1 |
| T4→T5 | missing root | `discV` nowhere; T5 row unprovable | T4a `discV` (K0 `zmodVal` of `Polynomial.discr ∘ Box.toPoly`, cap-at-N convention) + T4 (`DrainageImports` verbatim + `undec_subset_tail`; NEW flagged supporting def `tailC n = (n−1)·n²`) + T5 `env_le_tail` landed standalone (the −N → −(N−1) exponent relaxation of T6's inline m = N bound) | T6 had been proved with the T5 bound INLINE (green independently of T5); the standalone displayed T5 row is now landed, closing the unit |
| C4c→C6 | missing root | `censusW` missing | C4a `Stratum1`/`Box1` carrier + C4b `vertexChain_telescope(_units)` + C4c `censusW`/`canonicalStratum1`/`census_r0_law` + C6 `censusW_eval(_nonneg)` landed (`Census.lean`) | intent per M08 §2 Theorem 2; canonical carrier junction-pinned; NOTE: at r ≥ 1 the landed `censusW` reads the stage-0 shadow only — re-key chartered to the C5 wave-4 constructor |
| C7 | cascade (C4c) | `censusW_eq_zero_of_unattained` | landed VERBATIM but VACUOUS: `Attained D := 0 < D.attainDim 0` is a THEOREM (`attained_always` — Gset 0 always contains the zero index), so `¬ Attained D` is empty | honesty invariant on display (`sorry`-free ≠ non-vacuous): the M08 padding clause lives at ATTAINED-VERTEX granularity the skeletal carrier does not key; the honest padding law re-lands with the C5 constructor's `censusW` re-key |
| K5 | cascade (MulFiberData/SmithStable) | `kcount_fiber_card (F) (hS) (hne)` | carriers landed; K5 RE-SCOPED + PROVED with ONE new named binder `hsol : Nat.card F.SolutionSet = p^(Σ min …)` — the K1/K2∘K4∘K3 leg at the concrete (⋆⋆) set, supplied by the K7f builder | over the abstract carrier `SolutionSet`/`smithExp` are unrelated fields — instances with `\|SolutionSet\| ≠ p^Σmin` survive even the chart repair; `hS` kept to mirror the displayed binder list |
| S2a | missing root | `TreeRecursion` never landed | landed in `SeriesTie.lean` with fields VERBATIM; S2a `slice_eq_partialNeumann` + S2b `seriesSum_eq_lfp` PROVED | ONE deviation, flagged: the §1.5 `: Prop` ascription is REJECTED by Lean 4.31 (a Prop structure cannot carry the data field `stateOf`; exact error in the S2b section); structure lands in `Type`, statement byte-identical |
| C5/C5′ | elaboration failure | `CensusValueRows` binding five undeclared types + internal `∀ S : StratumR D` | landed (`Census.lean`): BP_IV-OWNED skeletal carriers `StratumR`/`JunctionStratum` (`hr : 1 ≤ D.r`, `count : ℕ → ℕ`); (GR-B)/(FRESH) as OPAQUE PARAMETERS `{GRBRow FreshRow : CensusData → Prop}`; strata as PARAMETERS `SW`/`SJ` | BP_III's landed `DictIII.GRB/FRESH` carry a DIFFERENT signature (prime+field, not CensusData) and BP_III.md never charters census-keyed forms — seam failure (R3.2); an internal ∀ over skeletal carriers is UNSATISFIABLE (arbitrary `count` falsifies any value law), killing every consumer — the parametric form asserts the law AT the engine's constructed strata (`canonicalStratum1` precedent, REV-2 finding 11) |
| D4 + S5b | elaboration failure + under-constraint | §1.5/§1.6 displays binding `GRBRow/FreshRow/CensusValueRows/R1R4Row/TerminalSeamRows` (five unknown identifiers) and tying (A, b) to `C.chain` by NOTHING | LANDED (S5b in `SeriesTie.lean`, D4 in `DensityTie.lean`): opaque parameters per R3.2; `CensusValueRows` per its landed form; + ONE new named row `K2 : SolvePricing C K1` (the O11-K2 pricing content: solve datum pinned to `Rsh` byte-identically to `SolveSeam.r_is_solve`, margin regime, real solution reading off `evalℝ` at every σ-state, nonnegativity `sol_nonneg`).  D4 = S5b's binder list + `henv`; both PROVED (S5a/S4c2 assembly resp. D3+S5b with `ENNReal.toReal_ofReal` at `sol_nonneg`) | type-level warrant: the five-identifier probe transcript (kept verbatim in both files); proof-level warrant: with A = 0, b = 0, slice ≡ 0 (a legal `TreeRecursion`, forcing seriesSum ≡ 0) and all opaque rows `fun _ => True`, the displayed conclusion equates 0 with an arbitrary carrier's `Rval` — the display omitted exactly M04 Lemma 3.3's application scope (O-11 K2); no compiled countermodel owed since the display never elaborated |
| K7e | REFUTED (escalated per §4) | `fiber_equiv_solutions` over the data-only `MulFiberData` | carrier gains the LAW field `chart : FiberNonempty → Fiber ≃ SolutionSet`; K7e = its projection, VERBATIM statement PROVED; O-10 Steps 1–2 content moves to NEW queued unit K7f (concrete instance builder over the landed K7a–K7d + K8b engine) | compiled countermodel `mulFiberDataCounter` + `fiber_equiv_solutions_display_refuted` (Fiber card 1 ≠ 2 = SolutionSet card, `FiberNonempty := True`), git 33656d2; the §1.3 doc comment PROMISES the chart the display dropped; statement fix made at the blueprint level, never prover-side |
| K10 | REFUTED | `sib_product_law (A) (hS)` | RE-SCOPED + PROVED with ONE new named binder `himg : A.cellCount * p ^ A.sM = Nat.card A.Factor` (K10b's conclusion, discharged verbatim by `adaptedCell_constFiber_image_card`) | compiled countermodel STANDS on file as warrant: `K10Probe.sib_product_law_as_displayed_refuted` (`cellCount := 0`, `sM := 0`, `factorCount ≡ 1` satisfies every displayed field, 0 = 1 refutes); carrier itself unchanged |
| M4 | ill-typed | `RatFunc.eval (q₀ : ℚ) (D.detFull e)` | `(D.detFull e).eval (RingHom.id ℚ) (q₀ : ℚ)` — Mathlib's `RatFunc.eval` takes the coefficient ring hom FIRST; this is the exact corpus spelling of `RegP.detFull_clause`; PROVED (the (r1)-projection of that clause) | application mismatch at the display; no content change |
| M7 | ill-typed (four binder types) | `trueType_const_on_cylinder` binding `ThmERow`/`D15Row`/`CylEvent`/`IsContinuationEvent`, all undeclared | `CylEvent`/`IsContinuationEvent` AUTHORED (BP_IV-owned — they occur nowhere but this display): a level-N event is a `Finset (Box p n N)` (landed as `abbrev` — R3.4), a continuation event has all members undecided.  `ThmERow`/`D15Row` remain OWNER-BLOCKED: M7's PROOF consumes their CONTENT (the two-row transport), so the opaque-parameter pattern would leave M7 unprovable — not honest.  M7 stays blocked per the §4 failure protocol; it elaborates the moment BP_III lands the rows | BP_III.md charters neither row at any signature (R3.2); carriers flagged for Codex ratification |
| K11 | no verbatim statement exists | §2 row description only ("`EngineSIBRow` named structure consuming actual K-LOC and (I-τ) rows") | AUTHORED (`KCount.lean` end): `EngineSIBRow (p n N) (KLoc ITau : Prop) (stratumCount : ℕ) : Prop` with fields `kloc`/`itau`/`cell` (an `AdaptedCell` carrying `SmithStable` + the K10b image law + `cellCount = stratumCount`) — K-LOC/(I-τ) as opaque Prop parameters (`K3DeltaRow` pattern); named [M] row, constructors owner-side | the §1.3 application note fixes the content ("displayed as binders"); BP_III owns the two rows and never chartered them |

### R3.2 The cross-blueprint seam failure + the opaque-parameter ruling

Grep of `blueprints/BP_III.md` and `BP_V.md` (2026-08-01): ZERO hits for
`GRBRow`/`FreshRow`/`R1R4Row`/`TerminalSeamRows`/`ThmERow`/`D15Row`/K-LOC
row names at any signature — §1.0's owner table pointed at modules the owner
blueprints never chartered.  ESCALATED to the orchestrator as a seam failure.
Since no owner declaration can be awaited, the ruling (H4 ledger,
`ValueSide/Hyps.lean`) replaces "wait" with the sanctioned `K3DeltaRow`
OPAQUE-PARAMETER pattern wherever the consumer's PROOF does not need the
row's content: (R1)–(R4) as `{R1R4Row : ClassifierSpec n p → Prop}` applied
at `X` (display token `R1R4Row n p X` → parameter applied at `X`, indices in
the parameter's type); (H6) as `{TerminalSeamRows : FiberSeries n p X → Prop}`
applied at `F`; (GR-B)/(FRESH) census-keyed forms as
`{GRBRow FreshRow : CensusData → Prop}` (of `CensusValueRows` and of S5b/D4);
K-LOC/(I-τ) as the Prop parameters of K11's `EngineSIBRow`.  When BP_III/BP_V
land the real rows they INSTANTIATE the parameters — no re-key of any BP_IV
statement.  The ONE consumer whose proof needs row CONTENT (M7) stays
owner-blocked (table above).  `DictIII.Hyps` (GRB/FRESH, prime+field-indexed)
is imported as the H4 partial; the census-keyed bridge is BP_III's to state.

### R3.3 The C0 carrier fix (the J-staging adjudication behind C1/C2)

The §1.2 display gave stage 0 a full `Fin (e 0) × Fin (f 0)` pair in `J` and
an `e 0` factor in `period`.  The O9 ledger (rev5 §§1–2, math source of
record) has stage 0 contributing the `f₀` monomials ONLY (φ₀ = x, weight 0;
"m = f₀ = d at r = 0") and the period `e = e₁⋯e_r` (the O9 convention is
e₀ = 1).  Against the display, C1 and C2 are FALSE (countermodels at e₀ = 2,
R3.1); the TRANSCRIPTION was wrong, not the laws.  Fix (`CensusCore.lean`):
the ledger stage multiplicity `ledgerE` (= 1 at stage 0, `e i` at i ≥ 1)
replaces `e i` in the DERIVED defs `J`/`period`/`wt`-radix; the stage-0
FIELDS `e 0`/`h 0` remain carrier data (consumed by C4c's canonical level-1
polygon, untouched).  `wt` = the mixed-radix φ-monomial weight over the
(P3) V-recursion (`Vrec`/`wphi`), transcribing O9 §4 (LED).  C1/C2 statements
are byte-UNCHANGED and now PROVED; the retired countermodel datum satisfies
C1 on the repaired carrier.

### R3.4 Compile-gate repair from the 429-killed pass

`CylEvent` had landed as `def` — `IsContinuationEvent`'s `∀ f ∈ cyl` binder
then fails instance synthesis (`Membership ?m (CylEvent n p N)`), breaking
`Hyps.lean` (and everything downstream) at HEAD.  Repaired to `abbrev`
(reducible: the Finset `Membership` instance flows through); this was the
sole red module of the committed WIP state.

### R3.5 Retirements and re-charters

* **S3b2 RETIRED**: the §1.5-displayed S3 statement `neumannSum_blockTriangular`
  is landed and PROVED directly, and `neumannSum_blockTriangular_step` covers
  the chained multi-block passage — the "induction on blocks" was one possible
  proof route, not a residual obligation.
* **K7f NEW queued unit (wave 4)**: the concrete `MulFiberData` instance
  builder at the multiplication-map site — constructs `chart` (O-10 §3
  Steps 1–2 via the landed K7a/K7b/K7c/K7d lemmas) and K5's `hsol` (via
  K1/K2/K3/K4 + K8b's `SmithData`), and discharges K10's `himg` at concrete
  cells via `adaptedCell_constFiber_image_card`.
* **C5/C5′ constructor RE-CHARTERED (wave 4)**: `AnchoredMarchProof` had no
  spec anywhere; the HARD unit now includes designing that carrier (the
  anchored-march digit-read ladder, O9 rev-5 §5.1 — its counting kernels
  `digitCost_of_surjective_read`/`digitCost_of_surjective_linear_read` are
  landed and PROVED), proving `censusValueRows_of_anchoredMarch`, RE-KEYING
  `censusW` beyond the stage-0 shadow, and carrying the O9 §4 padding clause
  (C7's honest re-land).
* **T7 stands PARTIAL**: verbatim `canonicalOrderLEOne_ceil` compiles; the
  closure-reduction and Step-0 assembly layers are PROVED; the ONE honest
  `sorry` is the per-cluster core `OrderLEOne.clusterWalk_audit` (Theorem N3's
  walk-completion chain over Q̄_p root valuations — Facts EXT/DES/SF/HEN/EF/
  GRD/HRG/D have no corpus or Mathlib carrier; a dedicated campaign, exactly
  as §2 grades T7).  T8 is DISCHARGED (`discV_tail_count` constructs the
  `tail` row through the corpus `MovesX.tailCountBound`).
* **K9 constructor LANDED** (`smithStable_of_detDivisorRows`): `SmithStable`
  from per-point determinantal-divisor rows + the mod-p^τ polydisc congruence
  + the ρ-resultant bound, via `IsDetDivisor` uniqueness/transport; non-vacuity
  gate `K9Gate.gate_smithStable` over a nonempty polydisc.  The named row
  stays the single §1.3 carrier.

### R3.6 The spine seam, re-pointed (supersedes §5's D4 bullet)

`valueSide_massTie`'s binder list is now the REVISION-3 list: S5b's binders
(with `SolvePricing` and the opaque row parameters) + `henv`.  BP_VI's
clause-(R) statement must consume THIS list verbatim; any spine-side weakening
remains a statement-fence event.  The M04 F1 fence is restated: the DEVICE
`n2Chain` must never instantiate S5b/D4's carriers.

### R3.7 Remaining open units after this revision

| id | file | content | status |
|---|---|---|---|
| T7-core | `Transfer.lean` | `OrderLEOne.clusterWalk_audit` (the one `sorry`) | HARD, dedicated campaign (extended-valuation root theory) |
| C5/C5′-ctor | `Census.lean` | `AnchoredMarchProof` design + `censusValueRows_of_anchoredMarch` + `censusW` re-key + padding clause | HARD, wave 4 (re-chartered, R3.5) |
| K7f | `KCount.lean` | the concrete `MulFiberData`/`AdaptedCell` instance builder (chart + `hsol` + `himg`) | NEW queued, wave 4 |
| M7 | `MassId.lean` | `trueType_const_on_cylinder` | OWNER-BLOCKED on BP_III's `ThmERow`/`D15Row` content rows |

Everything else in the §2 unit table is landed and proved at this revision.

— BP_IV mop-up architect (Fable), 2026-08-01, completing the 429-killed first
pass; per the division-lead escalation and the §4 failure protocol.
