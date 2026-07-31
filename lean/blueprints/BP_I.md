# BP_I — Movement I: THE MEASURE FLOOR (ROOT Steps 1–4)

Blueprint architect deliverable for the Lean conversion swarm (authority: ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, "THE LEAN CONVERSION SWARM",
2026-08-03; scaffold shape: "THE PROOF SCAFFOLD" entry, 2026-08-01). Sources:
`docs/ROOT_ASSEMBLY_2026-08-02.md` REVISION 5, §2 Movement I (Steps 1–4) + §1
clauses (0)/(SQ); the VERIFIED Dfloor leaf
`lean/notes/openmath/Dfloor_phaseB_verifybrief_rev2.md` (leaf #3, V22 + Fable
pass 2, adjudicated dbccbc1) — the mathematical ground truth every unit below
transcribes; the existing Lean corpus (reuse map §3).

## 0. Scope, honesty display, and design decisions

**What this movement contributes to the scaffold spine.** The cylinder-limit
density definition α(n,τ;p) (ROOT clause (0)), the level-k squeeze display
(clause (SQ)'s measure content: BRACKET + drainage shells), Haar-on-Box (the
cylinder mass law μ(C_N(x)) = p^{−nN}), SUM-ONE + the TRANSFER/interpolation
principle (feeding Step 19's Σ_τ R_τ = 1), the n = 1 and n = 0 root instances,
and the T-layer measure imports (the `squeeze_unique` firing shape Theorem U /
Step 19 consumes). Steps 3–4 of the movement are ALREADY Lean-landed
(`MovesV/SkeletonFinite.lean`, `MovesU/RegPFinite.lean` — §3); this blueprint
adds NO units for them, only the reuse rows.

**Hypothesis honesty (the VC4-4 attribution, transcribed).** ROOT-C's clauses
(0) and (SQ) consume NO §3.1 open-mathematics row — they rest on Step 1 alone
(+ Step 13's semantic drainage, also unconditional). Accordingly this blueprint
introduces NONE of (H1)–(H6) as hypothesis rows. It exposes five semantic interface rows: **(TYPE-OF)**,
**(TYPE-OF-ISTYPE)**, **(LOC)**, **(NS-NULL)**, and **(LIN)**. None is an
axiom. `TypeData` packages the first two; `LocalityRow`, `NsNullRow`, and
`LinRow` are separate named structures so each theorem assumes exactly the
rows it consumes. No canonical `TypeData` is constructed in this movement:
the principal results are implications from these named Movement-III inputs.
Wave H proves an inhabitant-free theorem supplying (NS-NULL), while
(TYPE-OF), (TYPE-OF-ISTYPE), (LOC), and (LIN) remain Movement-III seams.

**Design decisions (the load-bearing choices, for the plan-review pass).**

1. **Carrier = coefficient tuples.** `Coeff p n := Fin n → ℤ_[p]`, the monic
   f = Xⁿ + Σ aᵢXⁱ identified with a (brief §1). The polynomial-subtype
   carrier `MovesX.MonicBox n p` already exists with the bridge
   `MovesX.polyOfCoeffs`; measure theory is done on `Coeff` (a compact
   metrizable topological group where mathlib's Haar machinery fires), and the
   polynomial side enters only through `mPoly := polyOfCoeffs ℤ_[p] n`.
2. **Haar via mathlib, aggressively.** ℤ_[p] is `CompactSpace`
   (`Mathlib/NumberTheory/Padics/ProperSpace.lean`), a topological additive
   group; take `μ₁ := MeasureTheory.Measure.addHaarMeasure ⊤` (the
   `PositiveCompacts` ⊤ of a compact nonempty space, `coe_top = univ`;
   `addHaarMeasure_self` gives probability normalization), and
   `μ := Measure.pi (fun _ => μ₁)` on `Coeff p n`. The brief's Prop H1
   (Carathéodory + π–λ, existence/uniqueness/product form) maps ENTIRELY onto
   mathlib: existence+invariance = `addHaarMeasure` instances; uniqueness =
   `isAddHaarMeasure_eq_of_isProbabilityMeasure`
   (`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`); the mass law is then
   the ~5-unit translate-partition argument (Wave B), not a from-scratch
   construction.
3. **Levels via `toZModPow`, not metric balls.** The level-N class of the
   brief's (1) is the fiber of
   `toLevel N : Coeff p n → (Fin n → ZMod (p^N))`, componentwise
   `PadicInt.toZModPow`. Cosets/clopenness come from `ker_toZModPow`; the
   closed-ball reading (V17 finding 3) becomes a remark, not a proof
   obligation. The level space `Fin n → ZMod (p^N)` is the tuple-side twin of
   the landed `OM/QuotientBox.monicBox` (polynomial side); counts bridge via
   `card_monicBox`.
4. **Abstract-then-instantiate (the T-layer import shape).** The decided
   machinery (nested per-level verdicts → monotone cylinder unions → mass law
   → BRACKET → drainage → limit) is stated ONCE for an ABSTRACT
   `LevelVerdicts` structure (Wave C) and instantiated at the STRICT semantic
   convention (brief (5)) in Wave E. This is exactly what Step 2's T-layer and
   Step 19's Theorem U consume as "measure imports": the classifier movements
   plug their own verdict assignments into the same shells, and the K-12
   `decided`/`hExhaustP` faithfulness audit (brief §8; tree §D1.5(g)) becomes
   a seam row, not a blocker.
5. **Value plumbing.** Measures live in ℝ≥0∞; the squeeze display exports to ℝ
   via `toReal` cast units; counts are ℕ and normalized counts ℚ, matching the
   corpus's count-side spine (`SeriesAssembly`, `UniformCapstone`) so the n=2
   anchors stay comparable. The TRANSFER layer lives on `RatFunc ℚ`
   (mathlib), tied to the corpus's `RatFn.IsRationalFn` by a remark unit only.
6. **Conventions transcribed exactly.** The strict decided convention (5) is
   primary (clause (iv) EXACT); the lax deltas (6) are OMITTED from the Lean
   spine (the root consumes strict; recorded as a parked extension row). The
   n = 0 Dirac floor and the n ≥ 1 hypothesis on singleton-nullity (V17
   finding 1 / brief (2′)) are displayed in the statements. SEM-DRAIN-RATE
   (quantitative envelope) is PARKED — Step 19 consumes qualitative drainage
   only; the rate row is displayed with its I-3 provenance for a later wave.

**New modules (all under `LeanUrat/Scaffold/`, namespace `LeanUrat.Scaffold`):**

| module | contents |
|---|---|
| `Scaffold/MeasureFloor/Space.lean` | `Coeff`, instances, `Level`, `toLevel`, cylinders |
| `Scaffold/MeasureFloor/Haar.lean` | `μ₁`, `μHaar`, invariance, **Haar-on-Box** |
| `Scaffold/MeasureFloor/Decided.lean` | `LevelVerdicts`, decided/undec sets, BRACKET/limit/squeeze shells |
| `Scaffold/MeasureFloor/Types.lean` | `IsType`, finiteness (FIN), the (C0) monoid |
| `Scaffold/MeasureFloor/Semantic.lean` | `mPoly`/`Sep`, `TypeData` and separate row structures, MEAS-BRIDGE, SEM-DRAIN, α |
| `Scaffold/MeasureFloor/SumOne.lean` | partition, SUM-ONE, Lemma ID, TRANSFER |
| `Scaffold/MeasureFloor/Base.lean` | BASE-0, BASE-1 (n = 1 root instance) |
| `Scaffold/MeasureFloor/NsNull.lean` | the (NS-NULL) discharge (discriminant zero-locus null) |

## 1. THE STATEMENT LAYER

Everything below is `namespace LeanUrat.Scaffold` with
`variable (p : ℕ) [Fact p.Prime] (n : ℕ)` unless shown. Signatures are
sketches: field/argument names are binding, exact implicit/explicit
bookkeeping is the E-phase's to adjust.

### 1.1 Space and cylinders (`Space.lean`)

```lean
/-- Monic degree-n polynomials over ℤ_p, as coefficient tuples (brief §1). -/
abbrev Coeff (p n : ℕ) [Fact p.Prime] : Type := Fin n → ℤ_[p]

-- instances (I-A1/I-A2): CompactSpace, T2Space, IsTopologicalAddGroup,
-- SecondCountableTopology (compact metrizable), MeasurableSpace := borel,
-- BorelSpace.  ℤ_[p] side first, then Pi closure.

/-- The level-N residue space: coefficient tuples mod p^N (brief (1); the
tuple twin of `OM.QuotientBox.monicBox`). -/
abbrev Level (p n N : ℕ) : Type := Fin n → ZMod (p ^ N)

theorem card_level (N : ℕ) : Nat.card (Level p n N) = p ^ (n * N)

/-- Componentwise reduction mod p^N (an AddMonoidHom; RingHom per slot). -/
def toLevel (N : ℕ) : Coeff p n → Level p n N := fun a i => PadicInt.toZModPow N (a i)

theorem toLevel_add (N : ℕ) (a b : Coeff p n) :
    toLevel p n N (a + b) = toLevel p n N a + toLevel p n N b

theorem toLevel_surjective (N : ℕ) : Function.Surjective (toLevel p n N)

/-- The level-N residue class C_N(x) (brief (1)), as a `toLevel` fiber. -/
def cylinder (N : ℕ) (x : Level p n N) : Set (Coeff p n) := toLevel p n N ⁻¹' {x}

theorem mem_cylinder_self (N : ℕ) (a : Coeff p n) : a ∈ cylinder p n N (toLevel p n N a)
theorem cylinder_disjoint (N : ℕ) : Pairwise (Disjoint on cylinder p n N)
theorem iUnion_cylinder (N : ℕ) : ⋃ x, cylinder p n N x = Set.univ
theorem isClopen_cylinder (N : ℕ) (x : Level p n N) : IsClopen (cylinder p n N x)
theorem measurableSet_cylinder (N : ℕ) (x : Level p n N) :
    MeasurableSet (cylinder p n N x)

/-- Cylinders form a topological basis, including the unique degree-zero
cylinder. -/
theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis {s : Set (Coeff p n) | ∃ N x, s = cylinder p n N x}

/-- Lemma H0: the σ-algebra generated by all cylinders is exactly Borel. -/
theorem generateFrom_cylinders_eq_borel :
    MeasurableSpace.generateFrom
      {s : Set (Coeff p n) | ∃ N x, s = cylinder p n N x} = borel (Coeff p n)

/-- Refinement: each level-(N+1) class sits inside its level-N cast (brief
Prop H1's splitting; carries the D_σ nesting). -/
theorem cylinder_succ_subset (N : ℕ) (x : Level p n (N + 1)) :
    cylinder p n (N + 1) x ⊆ cylinder p n N (levelCast p n N x)
-- where `levelCast : Level p n (N+1) → Level p n N` is componentwise ZMod.castHom.
/-- Translation moves classes to classes (feeds the mass law). -/
theorem cylinder_vadd (N : ℕ) (g : Coeff p n) (x : Level p n N) :
    (g + ·) ⁻¹' cylinder p n N x = cylinder p n N (x - toLevel p n N g)
```

### 1.2 Haar and the box mass law (`Haar.lean`)

```lean
/-- Normalized Haar probability on ℤ_p: `addHaarMeasure` at the positive
compact ⊤ of the compact group (brief Prop H1(a) existence). -/
noncomputable def μ₁ (p : ℕ) [Fact p.Prime] : MeasureTheory.Measure ℤ_[p] :=
  MeasureTheory.Measure.addHaarMeasure ⊤

instance : MeasureTheory.IsProbabilityMeasure (μ₁ p)
instance : (μ₁ p).IsAddLeftInvariant   -- addHaarMeasure instance, re-exported

/-- Haar probability on the coefficient space: the n-fold product (brief Prop
H1 "μ = μ₁^{⊗n}"; product form BY DEFINITION here, uniqueness available from
mathlib `isAddHaarMeasure_eq_of_isProbabilityMeasure` as a remark unit). -/
noncomputable def μHaar (p n : ℕ) [Fact p.Prime] : MeasureTheory.Measure (Coeff p n) :=
  MeasureTheory.Measure.pi fun _ => μ₁ p

instance : MeasureTheory.IsProbabilityMeasure (μHaar p n)

/-- Translation invariance, exported without freezing the version-sensitive
`IsAddLeftInvariant` instance shape for a `Measure.pi`. -/
theorem μHaar_map_add (g : Coeff p n) :
    Measure.map (fun a => g + a) (μHaar p n) = μHaar p n

/-- **HAAR-ON-BOX (brief Prop H1 (2); D-1(ii)'s layer; MEAS-BRIDGE(ii) first
half).** Every level-N class has Haar mass exactly p^{−nN}. -/
theorem μHaar_cylinder (N : ℕ) (x : Level p n N) :
    μHaar p n (cylinder p n N x) = 1 / (p : ENNReal) ^ (n * N)

/-- (2′) with its DISPLAYED n ≥ 1 hypothesis (V17 finding 1: FALSE at n = 0,
where μHaar is the Dirac mass — BASE-0). -/
theorem μHaar_singleton (hn : 1 ≤ n) (a : Coeff p n) : μHaar p n {a} = 0

theorem μHaar_cylinder_toReal (N : ℕ) (x : Level p n N) :
    (μHaar p n (cylinder p n N x)).toReal = 1 / (p : ℝ) ^ (n * N)
```

### 1.3 The abstract decided layer (`Decided.lean`) — the T-layer import shape

```lean
/-- A per-level verdict assignment with NESTING (the abstract skeleton of the
decided conventions (5)/(6); brief §4.1, MEAS-BRIDGE(iii)'s mechanism). `T` is
the verdict alphabet (instantiated at degree-n splitting types). NESTED: a
class decided at level N stays decided, same verdict, at level N+1. -/
structure LevelVerdicts (p n : ℕ) [Fact p.Prime] (T : Type*) where
  verdict : (N : ℕ) → Level p n N → Option T
  nested : ∀ (N : ℕ) (x : Level p n (N + 1)) (τ : T),
    verdict N (levelCast p n N x) = some τ → verdict (N + 1) x = some τ

variable {T : Type*} (V : LevelVerdicts p n T)

/-- D_τ(N): the union of the τ-decided level-N classes (brief (5)). -/
def decidedSet (τ : T) (N : ℕ) : Set (Coeff p n) :=
  toLevel p n N ⁻¹' {x | V.verdict N x = some τ}
/-- decided_τ(N), the count. -/
noncomputable def decidedCount (τ : T) (N : ℕ) : ℕ :=
  Nat.card {x : Level p n N // V.verdict N x = some τ}
/-- U_N and undec(N) (brief §4.2). -/
def undecSet (N : ℕ) : Set (Coeff p n) := toLevel p n N ⁻¹' {x | V.verdict N x = none}
noncomputable def undecMass (N : ℕ) : ENNReal := μHaar p n (V.undecSet N)

theorem measurableSet_decidedSet (τ : T) (N : ℕ) : MeasurableSet (V.decidedSet τ N)
theorem decidedSet_mono (τ : T) : Monotone (V.decidedSet τ)          -- (iii)
theorem undecSet_antitone : Antitone V.undecSet
/-- MEAS-BRIDGE(ii) second half: mass = count · p^{−nN}. -/
theorem μHaar_decidedSet (τ : T) (N : ℕ) :
    μHaar p n (V.decidedSet τ N) = (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)

/-- **BRACKET shell (brief Cor BRACKET; the semantic side of (U-GEN)(i)).**
For any measurable L trapped between the decided set and its undecided
complement, the two-sided level-N bracket holds. -/
theorem bracket_abstract {L : Set (Coeff p n)} (τ : T) (N : ℕ)
    (hlow : V.decidedSet τ N ⊆ L) (hcov : L ⊆ V.decidedSet τ N ∪ V.undecSet N) :
    (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) ≤ μHaar p n L ∧
    μHaar p n L ≤ (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) + V.undecMass N

/-- **Clause (0) shell (brief MEAS-BRIDGE(v)): the cylinder-limit density.**
Continuity from below alone — NO drainage hypothesis (brief D-1(v) note). -/
theorem alpha_limit_abstract {L : Set (Coeff p n)} (τ : T)
    (hL : MeasurableSet L) (hexh : ⋃ N, V.decidedSet τ N = L) :
    Filter.Tendsto (fun N => (V.decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds ((μHaar p n L).toReal))

/-- Drainage shell (brief Cor SEM-DRAIN's measure half): if the residual
intersection is null, undec(N) ↓ 0. -/
theorem undec_tendsto_zero (hnull : μHaar p n (⋂ N, V.undecSet N) = 0) :
    Filter.Tendsto (fun N => (V.undecMass N).toReal) Filter.atTop (nhds 0)

/-- **THE THEOREM-U MEASURE IMPORT (Step 19 seam; T-U §U.SQ consumption).**
Two reals obeying the same shrinking bracket are equal: the shape by which
the solve value R_τ(p) gets identified with α once the classifier-side counts
match. Pure real analysis; stated here so Movement V consumes ONE name. -/
theorem squeeze_unique {l u : ℕ → ℝ} {x y : ℝ}
    (hx : ∀ N, l N ≤ x ∧ x ≤ l N + u N) (hy : ∀ N, l N ≤ y ∧ y ≤ l N + u N)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0)) : x = y
```

### 1.4 Splitting types (`Types.lean`)

Reuses the corpus type `LeanUrat.FactorizationType` (Interface.lean:152 —
`data : Multiset (ℕ × ℕ)` with `degree = Σ e·f`). NOTE (displayed): bare
`FactorizationType` admits (0,k) parts of degree 0, so "degree n" alone is NOT
finite — the positivity guard is part of `IsType` (brief (3): pairs in
ℤ_{≥1} × ℤ_{≥1}).

```lean
/-- σ ∈ Σ_n (brief (3)): degree n and every part positive. -/
def IsType (n : ℕ) (σ : FactorizationType) : Prop :=
  σ.degree = n ∧ ∀ ef ∈ σ.data, 1 ≤ ef.1 ∧ 1 ≤ ef.2

/-- Lemma FIN: Σ_n is finite. -/
theorem isType_finite (n : ℕ) : {σ : FactorizationType | IsType n σ}.Finite
/-- The Finset carrier of Σ_n used by SUM-ONE (choice-free consumption). -/
noncomputable def typesFinset (n : ℕ) : Finset FactorizationType
theorem mem_typesFinset {n σ} : σ ∈ typesFinset n ↔ IsType n σ

-- (C0) the graded type monoid (brief §6.2): ⊎ = Multiset add on `data`.
instance : Add FactorizationType            -- σ₁ ⊎ σ₂ := ⟨σ₁.data + σ₂.data⟩
theorem degree_add (σ₁ σ₂ : FactorizationType) :
    (σ₁ + σ₂).degree = σ₁.degree + σ₂.degree
theorem add_comm' / add_assoc' / add_left_cancel'   -- monoid + cancellation, from Multiset
def typeEmpty : FactorizationType := ⟨0⟩            -- the unit ∅; degree_empty : degree = 0

theorem isType_one_iff (σ) : IsType 1 σ ↔ σ = ⟨{(1, 1)}⟩          -- BASE-1(a)
theorem isType_zero_iff (σ) : IsType 0 σ ↔ σ = typeEmpty          -- BASE-0(a)
```

### 1.5 The semantic layer (`Semantic.lean`) — MEAS-BRIDGE at the strict convention

```lean
/-- The monic polynomial of a coefficient tuple (REUSE: `MovesX.polyOfCoeffs`). -/
noncomputable def mPoly (a : Coeff p n) : Polynomial ℚ_[p] :=
  (MovesX.polyOfCoeffs ℤ_[p] n a).map (algebraMap ℤ_[p] ℚ_[p])

/-- Separability over the FIELD ℚ_p (mathlib `Polynomial.Separable` =
IsCoprime f f′; brief Lemma SEP(ii)'s working form). -/
def Sep (a : Coeff p n) : Prop := (mPoly p n a).Separable

/-- **THE INTERFACE ROW CARRIERS** — the semantic inputs of Dfloor, as NAMED
STRUCTURE FIELDS (never axioms). `TypeData` contains only TYPE-OF and
TYPE-OF-ISTYPE; LOC and NS-NULL are independent structures. Provenance:
* `typeOf`/`typeOf_isType` — brief Thm TYPE (UFD + I-2 e·f = deg; the K-11/M16
  audited bridge). Lean discharge = the Movement-III dictionary seam (the
  concrete OM/QpType-side construction + `SerreLocalFields.AX_integralClosure_dvr`
  footprint); junk value off the separable locus.
* `locality` **(LOC)** — brief import I-1 (M05 Lemma D, V2-upheld, wild-valid):
  the type is constant on a small enough cylinder around every separable point.
  Stated at bare ∃N (the 2v+1 modulus is the RATE refinement, parked).
* **(NS-NULL)** — brief Appendix A / I-3 null clause. Wave H constructs this
  row for every `n`; the stable consumer interface is not deleted or migrated. -/
structure TypeData (p n : ℕ) [Fact p.Prime] where
  typeOf : Coeff p n → FactorizationType
  typeOf_isType : ∀ a, Sep p n a → IsType n (typeOf a)

/-- **(LOC)**, separated so only locality consumers carry it. -/
structure LocalityRow (TD : TypeData p n) : Prop where
  locality : ∀ a, Sep p n a →
    ∃ N, ∀ b ∈ cylinder p n N (toLevel p n N a),
      Sep p n b ∧ TD.typeOf b = TD.typeOf a

/-- **(NS-NULL)**, separated so normalization/drainage alone carry it. -/
structure NsNullRow (p n : ℕ) [Fact p.Prime] : Prop where
  ns_null : μHaar p n {a | ¬ Sep p n a} = 0

variable (TD : TypeData p n)

/-- L_τ (brief Cor PART). -/
def locus (τ : FactorizationType) : Set (Coeff p n) :=
  {a | Sep p n a ∧ TD.typeOf a = τ}

/-- The STRICT decided predicate (brief (5)): every lift separable of type τ. -/
def StrictDecided (N : ℕ) (x : Level p n N) (τ : FactorizationType) : Prop :=
  ∀ a ∈ cylinder p n N x, Sep p n a ∧ TD.typeOf a = τ

/-- The strict verdict assignment, packaged for the abstract layer (verdict by
choice on the ≤-one-τ fact; nesting from `cylinder_succ_subset`). -/
noncomputable def strictVerdicts : LevelVerdicts p n FactorizationType

theorem strictVerdicts_spec (N x τ) :
    (TD.strictVerdicts p n).verdict N x = some τ ↔ TD.StrictDecided p n N x τ

/-- MEAS-BRIDGE(iv), EXACT in the strict convention (the leaf's headline). -/
theorem iUnion_decided_eq_locus (LR : LocalityRow p n TD) (τ) :
    ⋃ N, (TD.strictVerdicts p n).decidedSet τ N = TD.locus p n τ
theorem isOpen_locus (LR : LocalityRow p n TD) (τ) :
    IsOpen (TD.locus p n τ)                                           -- (i)

/-- **THE SCAFFOLD DENSITY (clause (0)'s α).** -/
noncomputable def alpha (τ : FactorizationType) : ENNReal := μHaar p n (TD.locus p n τ)
noncomputable def alphaR (τ : FactorizationType) : ℝ := (TD.alpha p n τ).toReal

/-- Clause (0): α is the cylinder-count limit (glue: `alpha_limit_abstract` +
`iUnion_decided_eq_locus`). -/
theorem alpha_eq_lim (LR : LocalityRow p n TD) (τ) :
    Filter.Tendsto
      (fun N => ((TD.strictVerdicts p n).decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds (TD.alphaR p n τ))

/-- The cover L_τ ⊆ D_τ(N) ∪ U_N (brief Cor BRACKET upper half's set step). -/
theorem locus_subset_decided_union_undec (τ N) :
    TD.locus p n τ ⊆ (TD.strictVerdicts p n).decidedSet τ N ∪ (TD.strictVerdicts p n).undecSet N

/-- **Clause (SQ)'s bracket at the semantic instance** (glue via `bracket_abstract`). -/
theorem alpha_bracket (τ N) :
    ((TD.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        ≤ TD.alpha p n τ ∧
    TD.alpha p n τ ≤ ((TD.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        + (TD.strictVerdicts p n).undecMass p n N

/-- SEM-DRAIN: ⋂_N U_N = the nonseparable locus; hence undec ↓ 0 (via
`undec_tendsto_zero` + `ns_null`). Unconditional at every prime incl. wild. -/
theorem iInter_undec_eq_nonSep (LR : LocalityRow p n TD) :
    ⋂ N, (TD.strictVerdicts p n).undecSet N = {a | ¬ Sep p n a}
theorem undec_tendsto_zero_sem (LR : LocalityRow p n TD) (NR : NsNullRow p n) :
    Filter.Tendsto (fun N => ((TD.strictVerdicts p n).undecMass p n N).toReal)
      Filter.atTop (nhds 0)
```

### 1.6 SUM-ONE and TRANSFER (`SumOne.lean`)

```lean
/-- Cor PART: the loci partition the separable locus over Σ_n. -/
theorem locus_pairwise_disjoint :
    Set.PairwiseDisjoint (typesFinset n) (TD.locus p n ·)
theorem sep_eq_biUnion_locus :
    {a | Sep p n a} = ⋃ τ ∈ typesFinset n, TD.locus p n τ

/-- **SUM-ONE (Thm SUM-ONE(iii)): Σ_τ α(n,τ;p) = 1 at every p,
including n = 0.** -/
theorem sum_alpha_eq_one (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alpha p n τ = 1
theorem sum_alphaR_eq_one (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alphaR p n τ = 1

/-- Lemma ID (the interpolation principle), over an arbitrary infinite Z ⊆ ℕ
(deliberately: the D-3 unramified-base clause wants prime powers q = p^δ). -/
theorem ratFunc_eq_zero_of_infinite (R : RatFunc ℚ) {Z : Set ℕ} (hZ : Z.Infinite)
    (hdef : ∀ z ∈ Z, (RatFunc.denom R).eval (z : ℚ) ≠ 0)
    (hval : ∀ z ∈ Z, (RatFunc.num R).eval (z : ℚ) = 0) : R = 0

/-- **TRANSFER (D-2 (iii)–(iv), hypothesis-explicit).** Stated over an
ABSTRACT per-prime density family `A` (so no quantification over
`TypeSemantics` instances leaks into hypothesis position): the ONLY facts
consumed about `A` are per-prime normalization (`hsum`, supplied by SUM-ONE
at any semantic instance) and the pointwise tie to R (`htie`, the T-U-ledger
row at general n; unconditional at n = 1, 2 — §3). The prime set P is a NAMED
HYPOTHESIS ROW ((REG-p) primes at general n, infinite by `MovesU/RegPFinite`
+ Euclid). -/
theorem sum_R_eq_one_of_alpha_eq (R : FactorizationType → RatFunc ℚ)
    (A : ℕ → FactorizationType → ℝ) {P : Set ℕ} (hP : P.Infinite)
    (hsum : ∀ q ∈ P, ∑ τ ∈ typesFinset n, A q τ = 1)
    (hdef : ∀ q ∈ P, ∀ τ ∈ typesFinset n, (RatFunc.denom (R τ)).eval (q : ℚ) ≠ 0)
    (htie : ∀ q ∈ P, ∀ τ ∈ typesFinset n,
      A q τ = (RatFunc.num (R τ)).eval (q : ℚ) / (RatFunc.denom (R τ)).eval (q : ℚ)) :
    ∑ τ ∈ typesFinset n, R τ = 1
-- Consumption shape: A q := (canonical TypeSemantics at q).alphaR q n, with
-- hsum := sum_alphaR_eq_one; the (REG-p) instance takes P := regular primes.
```

### 1.7 Base cases (`Base.lean`)

```lean
-- BASE-0 (brief Thm BASE-0; the n = 0 Dirac floor, V17-finding-1 honest):
instance : Unique (Coeff p 0)
theorem μHaar_zero_eq_dirac : μHaar p 0 = MeasureTheory.Measure.dirac default
theorem sep_zero (a : Coeff p 0) : Sep p 0 a          -- mPoly = 1, empty product
theorem type_zero (TD : TypeData p 0) : TD.typeOf default = typeEmpty
theorem strictVerdicts_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).verdict 0 default = some typeEmpty
theorem decidedCount_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).decidedCount typeEmpty 0 = 1
theorem undecMass_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).undecMass p 0 0 = 0
theorem alpha_zero (TD : TypeData p 0) :
    TD.alpha p 0 typeEmpty = 1
theorem alphaR_zero (TD : TypeData p 0) :
    TD.alphaR p 0 typeEmpty = 1
theorem alpha_bracket_zero (TD : TypeData p 0) :
    ((TD.strictVerdicts p 0).decidedCount typeEmpty 0 : ENNReal) ≤
      TD.alpha p 0 typeEmpty ∧
    TD.alpha p 0 typeEmpty ≤
      ((TD.strictVerdicts p 0).decidedCount typeEmpty 0 : ENNReal) +
        (TD.strictVerdicts p 0).undecMass p 0 0

-- BASE-1 (brief Thm BASE-1(a)–(e); SEMANTIC clauses ONLY — the (f) fence):
theorem sep_one (a : Coeff p 1) : Sep p 1 a           -- derivative = 1, IsCoprime trivial

/-- **(LIN) — the n = 1 normalization row**: monic linear ⇒ type {(1,1)}
(brief BASE-1(b): K_f ≅ ℚ_p, e = f = 1). Movement-III discharge; consumed
ONLY by the n = 1 instance below. -/
structure LinRow (TD : TypeData p 1) : Prop where
  linear_type : ∀ a, TD.typeOf a = ⟨{(1, 1)}⟩

/-- **THE n = 1 ROOT INSTANCE (semantic clauses, unconditional given (LIN)):**
every class strictly decided at EVERY level including N = 0; counts = p^N;
undec = 0; α = 1 = R(p) with R := 1; bracket exact.  The ALGORITHMIC half
(one-state classifier, the 1×1 solve, count faithfulness) is BASE-1(f)'s
fence — classifier-side, NOT claimed here (V17 finding 2; lives at the
Movement-III/O-layer seams). -/
theorem base1_decided (TD) (hlin : LinRow p TD) (N x) :
    (TD.strictVerdicts p 1).verdict N x = some ⟨{(1, 1)}⟩
theorem base1_counts (TD) (hlin : LinRow p TD) (N) :
    (TD.strictVerdicts p 1).decidedCount ⟨{(1, 1)}⟩ N = p ^ N
theorem base1_undec (TD) (hlin : LinRow p TD) (N) :
    (TD.strictVerdicts p 1).undecMass p 1 N = 0
theorem base1_alpha (TD) (hlin : LinRow p TD) :
    TD.alphaR p 1 ⟨{(1, 1)}⟩ = 1
theorem base1_alpha_eq_ratFunc_one (TD) (hlin : LinRow p TD) :
    TD.alphaR p 1 ⟨{(1, 1)}⟩ =
      (RatFunc.num (1 : RatFunc ℚ)).eval (p : ℚ) /
        (RatFunc.denom (1 : RatFunc ℚ)).eval (p : ℚ)
theorem base1_sumR : (∑ τ ∈ typesFinset 1, (1 : RatFunc ℚ)) = 1
```

### 1.8 The (NS-NULL) discharge (`NsNull.lean`)

```lean
theorem μ₁_singleton (x : ℤ_[p]) : μ₁ p {x} = 0        -- coordinate case of (2′)
/-- Zero set of a nonzero one-variable polynomial is μ₁-null (finitely many
roots in the field + singleton-null). -/
theorem null_zeroLocus_one_var (f : Polynomial ℚ_[p]) (hf : f ≠ 0) :
    μ₁ p {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0} = 0
/-- Lemma NULL (brief Appendix A): nonzero m-variable polynomial zero locus is
null, by induction on m via `Measure.pi` slicing (measure_prod_null +
measurePreserving_piFinSuccAbove). -/
theorem null_zeroLocus (m : ℕ) (P : MvPolynomial (Fin m) ℚ_[p]) (hP : P ≠ 0) :
    μHaar p m {a | MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0} = 0
/-- The generic discriminant: discr(polyOfCoeffs) as an MvPolynomial in the
coefficients, with the evaluation law (naturality of resultants under ring
maps; mathlib `Polynomial.discr` = Resultant/Basic.lean:930). -/
noncomputable def discrPoly (n : ℕ) : MvPolynomial (Fin n) ℚ_[p]
theorem discr_mPoly_eq_eval (a : Coeff p n) :
    (mPoly p n a).discr = MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) (discrPoly p n)
/-- SEP(ii): monic, positive degree, over the field ℚ_p: separable ↔ discr ≠ 0
(via `isUnit_resultant_iff_isCoprime` / `resultant_eq_zero_iff`). -/
theorem sep_iff_discr_ne_zero (hn : 1 ≤ n) (a : Coeff p n) :
    Sep p n a ↔ (mPoly p n a).discr ≠ 0
/-- SEP(iii): the witness ∏ (X − pⁱ) has distinct roots ⇒ discrPoly ≠ 0. -/
theorem discrPoly_ne_zero (hn : 1 ≤ n) : discrPoly p n ≠ 0
/-- Positive-degree discriminant proof. -/
theorem ns_null_proved_pos (hn : 1 ≤ n) :
    μHaar p n {a | ¬ Sep p n a} = 0
/-- **(NS-NULL) PROVED for every degree.** At n = 0 use `sep_zero`; at
positive degree use `ns_null_proved_pos`. -/
theorem ns_null_proved : μHaar p n {a | ¬ Sep p n a} = 0
def nsNullRowProved : NsNullRow p n := ⟨ns_null_proved p n⟩
```

## 2. THE UNIT TABLE

Units are declaration-sized and intended for quick isolated compilation.
There is no blanket source-line cap: proof-heavy work is split at reusable
lemma boundaries, especially I-H3c1–I-H3c4 and I-H4a–I-H4c. Difficulty:
MECH (mechanical/defs), EASY (one-idea proof), MED (several steps or API
hunting), HARD (genuine work).
"Source" = the paragraph of `Dfloor_phaseB_verifybrief_rev2.md` (cited `Df
§…`) or `docs/ROOT_ASSEMBLY_2026-08-02.md` (cited `ROOT §…`) the unit
transcribes. Deps name unit ids + corpus/mathlib imports.

### Wave A — space and cylinders (`Space.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-A1 | `Coeff`, `Level` abbrevs + topology instances on `Coeff` (CompactSpace, T2, IsTopologicalAddGroup, SecondCountableTopology) | Pi closure of ℤ_[p] instances; `PadicInt.compactSpace`; second-countable from compact+metrizable (mathlib instance chain) | mathlib `NumberTheory/Padics/ProperSpace` | MECH | Df §1.1, Lemma H0 |
| I-A2 | `MeasurableSpace (Coeff p n) := borel` + `BorelSpace` instances (declared on ℤ_[p] then Pi) | `borel`/`BorelSpace` + Pi instance chain (needs I-A1 second-countability) | I-A1 | EASY | Df §1.1 H0 |
| I-A2b | `isTopologicalBasis_cylinders` | product-basic neighborhoods contain a common-depth congruence cylinder; pad finitely many coordinate depths to their maximum | I-A1, I-A4, I-A6 | MED | Df §1.1 H0 |
| I-A2c | `generateFrom_cylinders_eq_borel` | both inclusions: cylinder measurability for `≤`; I-A2b plus `borel_eq_generateFrom_of_isTopologicalBasis` for `≥` | I-A2, I-A2b | EASY | Df §1.1 H0, verbatim σ(cyl)=Borel |
| I-A3 | `card_level : Nat.card (Level p n N) = p^(n*N)` | `Nat.card_pi` + `ZMod.card` + `pow_mul` | mathlib; cf. landed `QuotientBox.card_residueRing` | MECH | Df §1.1 "p^{nN} classes" |
| I-A4 | `toLevel` def + `toLevel_add` (AddMonoidHom law) | componentwise `RingHom.map_add` of `PadicInt.toZModPow` | I-A1 | MECH | Df §1.1 (1) |
| I-A5 | `cylinder` def + `mem_cylinder_self`, `cylinder_disjoint`, `iUnion_cylinder` | fibers of a function: disjointness + covering are `Set.preimage` bookkeeping | I-A4 | MECH | Df §1.1 (1) |
| I-A6 | `isClopen_cylinder` + `measurableSet_cylinder` | `toLevel` continuous (`PadicInt.continuous_toZModPow` per slot, `continuous_pi`); singleton clopen in the discrete `Level`; preimage; clopen→measurable | I-A2, I-A4 | EASY | Df §1.1 H0(a) |
| I-A7 | `levelCast` def + `toLevel_levelCast : levelCast ∘ toLevel (N+1) = toLevel N` + `cylinder_succ_subset` | `ZMod.castHom_comp` / `PadicInt.zmod_cast_comp_toZModPow` (exists in RingHoms.lean); fiber refinement | I-A4 | EASY | Df §1.2 H1 proof ("each level-M class splits") |
| I-A8 | `toLevel_surjective` | per-slot: `ZMod (p^N) → ℤ_[p]` natural lift (`ZMod.val` cast) is a section of `toZModPow` (`PadicInt.toZModPow_natCast` shape; else `zmod_congr_of_sub_mem_span`) | I-A4 | MED | Df §1.1 (classes nonempty) |
| I-A9 | `cylinder_vadd` (translation permutes classes) | `toLevel_add` + fiber algebra: `a ∈ g + C ↔ toLevel a − toLevel g = x` | I-A4, I-A5 | EASY | Df §1.2 H1 "TRANSLATION INVARIANCE" ¶ |

### Wave B — Haar and the box law (`Haar.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-B1 | `μ₁` def + `IsProbabilityMeasure (μ₁ p)` + invariance instance re-export | `addHaarMeasure ⊤`; `addHaarMeasure_self` + `PositiveCompacts.coe_top` ⇒ μ(univ)=1; instances by `inferInstance` | I-A1/A2 (ℤ_[p] layer); mathlib Haar/Basic | EASY | Df §1.2 H1(a) existence |
| I-B2 | `μHaar` def + `IsProbabilityMeasure (μHaar p n)` | `Measure.pi`; `Measure.pi_univ` product of 1s | I-B1 | MECH | Df §1.2 H1 "PRODUCT FORM" |
| I-B3a | per-coordinate translation is measure-preserving for `μ₁` | derive from the installed Haar invariance API; the exact class projection is discovered and compiled before I-B3b | I-B1 | MED | Df §1.2 H1 invariance ¶ |
| I-B3b | `μHaar_map_add` | apply the finite-product map theorem coordinatewise; this public equality avoids committing to an unverified `IsAddLeftInvariant` instance form for `Measure.pi` | I-B2, I-B3a | MED | Df §1.2 H1 invariance ¶ |
| I-B4a | `μHaar_cylinder_eq` : any two level-N cylinders have equal mass | translate by a preimage difference: I-A8 gives g with `toLevel g = x-y`; rewrite by I-A9 and I-B3b's map equality | I-A8, I-A9, I-B3b | EASY | Df §1.2 H1 uniqueness ¶ ("pairwise translates") |
| I-B4b | `sum_μHaar_cylinder : ∑ x, μHaar (cylinder N x) = 1` | finite disjoint cover (I-A5) + `measure_iUnion_fintype` + `IsProbabilityMeasure` | I-A5, I-A6, I-B2 | EASY | Df §1.2 H1 mass-law ¶ |
| I-B4c | **`μHaar_cylinder` (HAAR-ON-BOX)**: mass = 1/p^{nN} in ℝ≥0∞ | B4a: all masses equal m; B4b: card·m = 1; I-A3 card; solve in ℝ≥0∞ (`ENNReal.eq_div_iff`) | I-A3, I-B4a, I-B4b | EASY | Df §1.2 H1 (2) |
| I-B5 | `μHaar_singleton (hn : 1 ≤ n)` = 0, hypothesis DISPLAYED | {a} ⊆ cylinder N (toLevel a) for every N; `le_of_forall` + `ENNReal` power → 0 needs n ≥ 1 | I-B4c | EASY | Df §1.2 (2′) + non-removability note (V17 f.1) |
| I-B6 | `μHaar_cylinder_toReal` + `μHaar_decided-count cast pack` (ℝ≥0∞→ℝ→ℚ-compatible display lemmas) | `ENNReal.toReal_div`, `toReal_pow`, `Nat.cast` | I-B4c | MECH | ROOT §1 (0) display |
| I-B7 | (optional remark) `μHaar_eq_addHaar`: μHaar equals any Haar probability on `Coeff` | I-A2b supplies a cylinder basis; B4c gives positive mass to every basis cylinder, hence every nonempty open set; then apply Haar uniqueness after the exact API is compiled | I-A2b, I-B3b, I-B4c | MED | Df §1.2 H1 uniqueness (not consumed downstream) |

### Wave C — the abstract decided layer (`Decided.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-C1 | `structure LevelVerdicts` (verdict + nested), + `decidedSet`/`decidedCount`/`undecSet`/`undecMass` defs | statement-only | I-A7 (levelCast in `nested`) | MECH | Df §4.1 (5) abstracted; ROOT Step 1 |
| I-C2 | `measurableSet_decidedSet`/`_undecSet` (finite unions of cylinders) | preimage of a set under `toLevel` = union of fibers; I-A6 | I-A6, I-C1 | MECH | Df §4 (ii) |
| I-C3 | `decidedSet_mono` + `undecSet_antitone` | `nested` + I-A7 refinement: each level-(N+1) class inside a decided level-N class is decided; complement | I-A7, I-C1 | MED | Df §4 proof of (iii) |
| I-C4 | `μHaar_decidedSet = count/p^{nN}` | decidedSet = disjoint union over the decided fiber Finset; `measure_biUnion_finset` + I-B4c + card | I-B4c, I-C2 | EASY | Df §4 proof of (ii) |
| I-C5 | `bracket_abstract` (two-sided, hypothesis-carrying) | lower: `measure_mono hlow` + I-C4; upper: `measure_union_le` on hcov + I-C4 | I-C4 | EASY | Df §4.2 Cor BRACKET |
| I-C6 | `alpha_limit_abstract` (clause (0) shell) | `tendsto_measure_iUnion_atTop` using I-C3, measurable decided sets from I-C2, I-C4 rewrite, and `ENNReal.toReal` continuity at the probability-finite limit | I-C2, I-C3, I-C4, I-B2 | MED | Df §4 proof of (v) |
| I-C7 | **`squeeze_unique`** (the Theorem-U measure import) | \|x−y\| ≤ u N for all N (both in the bracket); `le_of_forall_lt` + `tendsto` ⇒ \|x−y\| ≤ 0 | pure ℝ | EASY | ROOT Step 19 squeeze machinery; Df §4.3 scope note |
| I-C8 | `undec_tendsto_zero` (drainage shell from a null intersection) | `tendsto_measure_iInter_atTop` using antitonicity I-C3, measurable undecided sets I-C2, probability/finite measure I-B2, hnull, and `toReal` | I-B2, I-C2, I-C3 | MED | Df §4.2 Cor SEM-DRAIN measure half |

### Wave D — types (`Types.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-D1 | `IsType` def + positivity-guard note (bare degree-n is NOT finite) | statement-only | corpus `FactorizationType` | MECH | Df §1.3 (3) |
| I-D2 | `isType_finite` + `typesFinset` + `mem_typesFinset` | data ⊆ (range n+1)² pairs, card ≤ n ⇒ inject into multisets of bounded card over a Fintype (`Multiset.card_le` + `Sym`/powerset finiteness) | I-D1 | MED | Df §1.3 Lemma FIN |
| I-D3 | (C0): `Add FactorizationType`, `degree_add`, comm/assoc/cancel, `typeEmpty` + `degree_empty` | Multiset add laws, `Multiset.sum_map_add` | corpus type | MECH | Df §6.2 (C0) |
| I-D4 | `isType_one_iff` | degree-1 multiset analysis: one part, e·f = 1 ⇒ (1,1) | I-D1 | EASY | Df §6.1 BASE-1(a) |
| I-D5 | `isType_zero_iff` | every part contributes ≥ 1 | I-D1 | MECH | Df §6.2 BASE-0(a) |

### Wave E — the semantic instantiation (`Semantic.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-E1 | `mPoly` def (via `MovesX.polyOfCoeffs` + map) + `Sep` def + `mPoly_monic`, `mPoly_natDegree` | map of monic is monic (`Polynomial.Monic.map`); degree preserved (injective algebraMap) | corpus MovesX/Defs | EASY | Df §1 setting + §3.1 |
| I-E2a | `structure TypeData` — named TYPE-OF and TYPE-OF-ISTYPE rows | statement-only; no canonical constructor is claimed here | I-D1, I-E1 | MECH | Df §3.2 TYPE |
| I-E2b | `structure LocalityRow` + `structure NsNullRow` | separate named hypothesis carriers; provenance docstrings mandatory (I-1 = M05 Lemma D V2-upheld; NS-NULL = Df App A) | I-E2a | MECH | Df §2 imports I-1/I-3 |
| I-E3 | `StrictDecided` def + at-most-one-τ lemma + `strictVerdicts : LevelVerdicts` + `strictVerdicts_spec` | uniqueness: a class member witnesses both verdicts (Df Lemma EX's uniqueness half — nonemptiness of cylinders from I-A8, no measure needed); Option by `Classical.choice`; nested from I-A7 | I-A7, I-A8, I-C1 | MED | Df §4.1 (5) + Lemma EX |
| I-E4 | `iUnion_decided_eq_locus (LR : LocalityRow p n TD)` (MEAS-BRIDGE(iv), EXACT) | ⊆: a is a lift of its own class; ⊇: `LR.locality` gives the decided level | I-E3, I-E2b | MED | Df §4 proof of (iv) |
| I-E5 | `isOpen_locus` (i) + `measurableSet_locus` | union of cylinders via I-E4 + I-A6; or directly (LOC) neighborhoods | I-E4 | EASY | Df §4 proof of (i) |
| I-E6a | `alpha`/`alphaR` defs | measure of `TD.locus`; consumes TYPE-OF only and no LOC/NS-NULL row | I-E2a | MECH | ROOT §1 (0) |
| I-E6b | **`alpha_eq_lim (LR : LocalityRow p n TD)` (CLAUSE (0))** | glue I-C6 with exhaustion I-E4 and measurability I-E5; consumes LOC but not NS-NULL | I-C6, I-E4, I-E5, I-E6a | EASY | ROOT §1 (0); Df §4 (v) |
| I-E7 | `locus_subset_decided_union_undec` + **`alpha_bracket` (CLAUSE (SQ) bracket)** | either a's class is decided (verdict forced by the lift argument) or undecided; then I-C5; consumes TYPE-OF only, neither LOC nor NS-NULL | I-E3, I-C5, I-E6a | MED | Df §4.2 BRACKET proof |
| I-E8a | `iInter_undec_eq_nonSep (LR : LocalityRow p n TD)` | a decided at some N iff separable; the reverse direction is LOC | I-E4 | MED | Df §4.2 SEM-DRAIN |
| I-E8b | `undec_tendsto_zero_sem (LR) (NR : NsNullRow p n)` | rewrite the intersection by I-E8a, use `NR.ns_null`, then I-C8 | I-C8, I-E8a, I-E2b | EASY | Df §4.2 SEM-DRAIN |
| I-E9 | (parked row, statement displayed, NO proof unit) SEM-DRAIN-RATE with the I-3 tail bound | — consumes M05 Lemmas B+C quantitatively; schedule after Wave H | — | — | Df §4.2 SEM-DRAIN-RATE |

### Wave F — SUM-ONE + TRANSFER (`SumOne.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-F1 | `locus_pairwise_disjoint` + degree-unrestricted `sep_eq_biUnion_locus` | TYPE-OF is a function; TYPE-OF-ISTYPE puts every separable point's type in the Finset; valid also at n = 0 | I-D2, I-E2a | EASY | Df §3.2 Cor PART |
| I-F2 | **`sum_alpha_eq_one (NR : NsNullRow p n)`** + ℝ version | probability mass of the separable locus plus `NR.ns_null`; finite disjoint union from I-F1; consumes NS-NULL but not LOC | I-F1, I-B2, I-E6a, I-E2b | MED | Df §5 SUM-ONE(iii) |
| I-F3 | `ratFunc_eq_zero_of_infinite` (Lemma ID) | num/denom: A(z)=0 on infinite Z ⊆ ℚ-embedded ℕ ⇒ `Polynomial.eq_zero_of_infinite_isRoot` ⇒ num = 0 | mathlib RatFunc | MED | Df §5 Lemma ID |
| I-F4 | **`sum_R_eq_one_of_alpha_eq` (TRANSFER)** — abstract density family A + P as NAMED hypothesis rows (see §1.6 re-key note) | Q := Σ R_τ − 1 vanishes at P (`hsum` + `htie` per prime); I-F3; the (REG-p) instance remark cites `MovesU/RegPFinite.regP_cofinite` + `Nat.infinite_setOf_prime` | I-F3 (I-F2 supplies `hsum` at consumption) | MED | Df §5 TRANSFER + instances |
| I-F5 | (remark unit) instance rows: n = 1 (Wave G, unconditional), n = 2 (unconditional — corpus `UniformCapstone` values; direct table check 1/(q+1)+q/(2(q+1))·2 = 1 as a `RatFunc` computation) | `field_simp` on the n = 2 table | I-F4, corpus OM/UniformCapstone | EASY | Df §5 instances ¶ |

### Wave G — base cases (`Base.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-G1a | `Unique (Coeff p 0)` + `μHaar_zero_eq_dirac` + `sep_zero` | one-point probability space; `mPoly = 1` and `Polynomial.separable_one` | I-B2, I-E1 | EASY | Df §6.2 BASE-0 |
| I-G1b | `type_zero` + `strictVerdicts_zero` + `decidedCount_zero` + `undecMass_zero` | TYPE-OF-ISTYPE and `isType_zero_iff`; the unique level-0 class is strictly decided | I-D5, I-E3, I-G1a | EASY | Df §6.2 BASE-0 |
| I-G1c | `alpha_zero` + `alphaR_zero` + `alpha_bracket_zero` | locus is univ; probability normalization; rewrite I-G1b | I-E6a, I-G1a, I-G1b | EASY | Df §6.2 BASE-0 |
| I-G2 | `sep_one : ∀ a : Coeff p 1, Sep p 1 a` | mPoly = X + C a₀, derivative 1, `IsCoprime` with unit (`Polynomial.separable_X_add_C` shape) | I-E1 | EASY | Df §6.1 BASE-1(b) |
| I-G3 | `structure LinRow` (the named LIN row) + `base1_decided` | LIN + I-G2 make StrictDecided at every `(N,x)`, including N = 0 | I-E2a, I-E3, I-G2 | EASY | Df §6.1 BASE-1(b)(d) |
| I-G4 | `base1_counts` (= p^N) + `base1_undec` (= 0) | all classes decided (I-G3): count = card(Level p 1 N) = p^N (I-A3); undecSet = ∅ | I-A3, I-G3 | EASY | Df §6.1 BASE-1(d) |
| I-G5 | **`base1_alpha` + `base1_alpha_eq_ratFunc_one` + `base1_sumR`** — the n = 1 semantic instance | locus = univ; α = 1; explicitly identify α with the numerator/denominator evaluation of `1 : RatFunc ℚ`; sum over the singleton menu | I-E6a, I-G4, I-D4 | EASY | Df §6.1 BASE-1(c)(e)(f) |

### Wave H — the (NS-NULL) discharge (`NsNull.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-H1 | `μ₁_singleton = 0` | n = 1 coordinate case of I-B5 (or directly: singleton inside every 1-dim cylinder) | I-B4c | MECH | Df §1.2 (2′) |
| I-H2 | `null_zeroLocus_one_var` | f ≠ 0 over a field: finitely many roots (`Polynomial.setOf_isRoot_finite`); finite sets null by I-H1 + `measure_biUnion_null` | I-H1 | EASY | Df App A base case |
| I-H3a | define the explicit `Fin (m+1)` coordinate equivalence and prove its product-measure transport | prove the public transport theorem from the available `Measure.pi` map API; `measurePreserving_piFinSuccAbove` is only a search hint, not a frozen dependency | I-B2 | MED | Df App A induction plumbing |
| I-H3b | zero-locus measurability for an `MvPolynomial` evaluation on `Coeff` | polynomial evaluation is continuous after the explicit ℤ_p→ℚ_p cast | I-E1 | EASY | Df App A Tonelli step |
| I-H3c1 | slicing lemma: a measurable set with almost-everywhere μ₁-null slices is product-null | product-measure/Tonelli null-section theorem | I-H3a, I-H3b | MED | Df App A Tonelli step |
| I-H3c2 | leading-coefficient exceptional-locus lemma | expose a nonzero lower-dimensional coefficient polynomial controlling identically-zero slices | I-H3b | MED | Df App A Lemma NULL |
| I-H3c3 | induction step for multivariable zero loci | off the exceptional locus apply I-H2 to each slice; on it apply the induction hypothesis; assemble with I-H3c1 | I-H2, I-H3c1, I-H3c2 | HARD | Df App A Lemma NULL |
| I-H3c4 | **`null_zeroLocus` (Lemma NULL)** | induction wrapper using I-H3c3, with m = 0 discharged directly | I-H3c3 | EASY | Df App A Lemma NULL |
| I-H4a | construct the generic monic polynomial and `discrPoly` | coefficient-index bookkeeping only | mathlib MvPolynomial, Resultant/Basic | MED | Df §3.1 SEP(i) |
| I-H4b | generic-polynomial evaluation equals `mPoly` | explicit coefficient casts and `Fin` index transport | I-E1, I-H4a | MED | Df §3.1 SEP(i) |
| I-H4c | `discr_mPoly_eq_eval` | prove discriminant naturality using a verified resultant-map lemma, or isolate determinant naturality here if absent | I-H4a, I-H4b | HARD | Df §3.1 SEP(i) |
| I-H5 | `sep_iff_discr_ne_zero` | Separable = IsCoprime f f′; monic ⇒ `isUnit_resultant_iff_isCoprime`; field ⇒ unit ↔ ≠ 0 (`resultant_eq_zero_iff`); discr vs resultant unwind | mathlib | MED | Df §3.1 SEP(ii) |
| I-H6 | `discrPoly_ne_zero` via the witness ∏ᵢ (X − pⁱ) | distinct roots imply separability; use I-H5 and evaluation I-H4c | I-H4c, I-H5 | MED | Df §3.1 SEP(iii) |
| I-H7 | `ns_null_proved_pos` | identify nonSep with the discriminant zero locus and apply I-H3c4 plus I-H6 | I-H3c4, I-H4c, I-H5, I-H6 | EASY | Df App A + §2 I-3 |
| I-H8 | degree-unrestricted `ns_null_proved` + `nsNullRowProved` | cases on n; n = 0 uses `sep_zero`, successor uses I-H7 | I-G1a, I-H7 | EASY | Df App A + BASE-0 |

Accounting after the review split: A 11, B 10, C 8, D 5, E 12, F 5, G 7,
H 14 = **72 table rows total**. I-E9 is the sole parked row, leaving 71
scheduled rows. Structure/definition rows are still scheduled compilation
units; they are not subtracted from the total. H is not on the α/bracket
interface path, but its proved `NsNullRow` gates unconditional drainage and
SUM-ONE claims.

## 3. THE CORPUS-REUSE MAP

Which existing PROVED declarations reuse or anchor parts of this movement.
Only an exact theorem-level implication counts as a discharge. Reuse is BY
IMPORT; no fenced statement is touched; parked items 22–29 remain untouched.

| corpus declaration (module) | discharges / anchors |
|---|---|
| `MovesV.SkeletonFinite.skeleton_finite` | **ROOT Step 3 wholesale** (O-13 menu finiteness). No Movement-I unit; listed because Step 3 sits in this movement's step range. D-12r stays a Movement-III residue. |
| `MovesU/RegPFinite.lean` (`regP_cofinite`, `regP_failing_finite`, `RegP.detFull_ne_zero`, …) | **ROOT Step 4 wholesale** (K-13 (REG-p) finiteness, 14 theorems, Lean-core). Consumed by I-F4's (REG-p) instance remark: the hypothesis set P infinite = `regP_cofinite` + infinitude of primes. |
| `MovesU/O12PoleFree.lean` + `MovesU/BridgeSolve.lean`/`BridgeKernels.lean` | Movement II/IV territory (Step 5 / T-8); named here only as the consumers of I-F4's definedness row `hdef` (pole-freeness supplies it at every prime power). |
| `MovesX.polyOfCoeffs`, `MovesX.MonicBox`, `MovesX.discZero`, `MovesX.vdisc` (`MovesX/Defs.lean`) | I-E1's `mPoly` reuses `polyOfCoeffs` VERBATIM (dedup rule: no parallel poly-builder). `MonicBox ≃ Coeff` transport is a deferred remark unit; `discZero`/`vdisc` align Wave H's discriminant locus with the MovesX carrier. |
| `MovesX.XCtx.frac` interface + `MovesX.discZeroNull` (XF10) + `Kernels/KA4c.ka4c_nsFiberUnion_null` | PAYOFF, not dependency: `μHaar` + I-B4c + I-H7 eventually furnish the first GENUINE (measure-backed) `frac` candidate for the frozen `XCtx` interface (`frac_univ`/`frac_mono`/`frac_iUnion_null` = probability-measure facts; `vdisc_le_tail` = I-B4c + a count). Recorded for the division lead; NOT a wave here (XCtx interface frozen by standing adjudications). |
| `OM.QuotientBox.ResidueRing`, `card_residueRing`, `card_monicBox` (`OM/QuotientBox.lean`) | I-A3's card-computation anchor only. `card_monicBox` gives matching cardinalities, not a tuple/polynomial level-space equivalence; any such equivalence is a separate deferred seam. |
| `OM.SeriesAssembly.hExhaust_n2`, `decided6_upper`, + the W6q census layer (`OM/SeriesAssembly.lean`) | The n = 2 ANCHOR: the count-side drainage + bracket already machine-checked at n = 2. Gate duty: when Waves C/E land, the n = 2 semantic shells must be CONSISTENT with these (same limit values via `UniformCapstone`); the formal tie of the classifier-side `decided`/`hExhaustP` to the strict convention (5) is the K-12 faithfulness audit row — Movement III seam, displayed in `Decided.lean`'s module docstring. |
| `OM.UniformCapstone` (`uniformValueFn`, `montes_uniform_n2`, value/denominator lemmas) | n = 2 value anchor and direct rational-function table check. It does not identify those values with the new `alpha`; that faithfulness/tie remains an integration seam, so no unconditional α-instance is claimed here. |
| `LeanUrat/RatFn.lean` (`IsRationalFn` + closure lemmas) | Compatibility remark for I-F3/I-F4: the corpus's ℕ→ℚ rational-function predicate vs `RatFunc ℚ`; a one-lemma bridge (`IsRationalFn` of `fun q => R.eval q`) IF a consumer wants it — not on the spine. |
| `OM/LimitSpine.lean`, `OM/LevelNCount.lean`, `NestedCollapse.geometricLimit_of_selfLoop` | Movement IV/V's count-side limit engine. Movement I's I-C6/I-C7 are their MEASURE-side counterparts; no shared code, but the division leads should keep `Filter.Tendsto`-at-`atTop`-`nhds` phrasing IDENTICAL (it already matches) so Step 19's composition is definitional. |
| `Moves/L6_measureExact_R4.lean` (`LandingCylinderL`, `hexact`) | Precedent only: the Moves-layer cylinder-exactness pattern (R1 re-point, signed off 2026-07-30). No import. |
| `SerreLocalFields.AX_integralClosure_dvr` (audited axiom) + `GMNIndex` | The eventual Movement-III discharge of `TypeSemantics.typeOf`/`typeOf_isType` (I-2's e·f = deg enters THERE, not in this movement). Axiom-footprint rule: `Scaffold/MeasureFloor/*` stays Lean-core — the axiom must NOT enter any Wave A–H unit (it may enter the Movement-III instance file that CONSTRUCTS a `TypeSemantics`). AxChk duty at every division checkpoint. |
| mathlib (pinned 4.31 tree; names marked “search hint” below are not treated as verified) | `PadicInt.compactSpace` (ProperSpace.lean:55); `PadicInt.toZModPow` + `ker_toZModPow` (RingHoms.lean:445/457); `Measure.addHaarMeasure` + `addHaarMeasure_self` + Haar instances (Haar/Basic.lean:517–570, `to_additive`); `⊤ : PositiveCompacts` + `coe_top` (Topology/Sets/Compacts.lean:570/584); `isAddHaarMeasure_eq_of_isProbabilityMeasure` (Haar/Unique.lean:692); `measure_preimage_add` (Group/Measure.lean:231 additive twin); `tendsto_measure_iUnion_atTop` (MeasureSpace.lean:648); `Measure.pi`; `Polynomial.discr` (RingTheory/Polynomial/Resultant/Basic.lean:930) + `isUnit_resultant_iff_isCoprime` (:885) + `resultant_eq_zero_iff` (:908); `Polynomial.eq_zero_of_infinite_isRoot` (Roots.lean:145); `RatFunc`. API search hints, not mechanically approved names: `PadicInt.continuous_toZModPow` (I-A6 fallback: prove locally constant), the exact `toZModPow` section lemma (I-A8), `measurePreserving_piFinSuccAbove` (I-H3a uses its own public transport theorem), and `resultant_map` (I-H4c isolates the fallback determinant proof). Each affected helper must pass its file-local `lake env lean` gate before a dependent row starts. |

**Statement-fence note.** No existing statement is modified. The capstone
`OM/UniformCapstone.montes_uniform_n2` and the V2 spine stay untouched; the
scaffold restatement of the capstone onto `alpha`/`alpha_eq_lim` is the
INTEGRATION architect's seam (BP of the spine movement), consuming this
blueprint's I-E6 as its density definition.

## 4. THE WAVE PLAN (for the division lead)

Dependency-ordered stages; only rows explicitly grouped on the same stage are
parallel. Intra-file arrows below are binding. After every stage touching a
file, run `lake env lean` on that file before releasing its declarations to
the next stage. At each checkpoint also run `lake build` and
`lake env lean LeanUrat/AxChk_baseline.lean`; commit explicit paths only.

* **WAVE 1 = A (11 rows, `Space.lean`).** Stages:
  A1; then A4; then A5/A7/A8; then A6/A9; then A2b; then A2c.
  A2 and A3 may start after A1. Run
  `lake env lean LeanUrat/Scaffold/MeasureFloor/Space.lean` after every stage.
  I-A8 is the riskiest API search and must compile before A7/A9 consumers.
* **WAVE 2 = B (10 rows, `Haar.lean`) and D (5 rows, `Types.lean`).**
  The files may run in parallel. B stages are B1; B2/B3a; B3b/B4b;
  B4a; B4c; B5/B6; optional B7. D stages are D1/D3; then D2/D4/D5.
  Gate each B stage with
  `lake env lean LeanUrat/Scaffold/MeasureFloor/Haar.lean`, and each D stage
  with `lake env lean LeanUrat/Scaffold/MeasureFloor/Types.lean`.
  Haar-on-Box lands only at B4c.
* **WAVE 3 = C (8 rows, `Decided.lean`).** Stages are C1/C7; then C2/C3;
  then C4; then C5/C6/C8. Gate every stage with
  `lake env lean LeanUrat/Scaffold/MeasureFloor/Decided.lean`.
  C6 explicitly waits for C2/C3/C4; C8 waits for B2/C2/C3.
* **WAVE 4 = E (12 rows, `Semantic.lean`).** Stages are E1; E2a; E2b/E3/E6a;
  E4/E7; E5/E8a; E6b/E8b. Gate each stage with
  `lake env lean LeanUrat/Scaffold/MeasureFloor/Semantic.lean`.
  Report exact interfaces: `alpha` and `alpha_bracket` need only `TypeData`;
  `alpha_eq_lim` needs `TypeData + LocalityRow`; drainage needs those plus
  `NsNullRow`. No canonical root instance is claimed.
* **WAVE 5 = G (7 rows, `Base.lean`) then F (5 rows, `SumOne.lean`).**
  G stages are G1a/G2; G1b/G3; G1c/G4; G5. F stages are F1/F3; F2/F4; F5.
  Gate every G stage with
  `lake env lean LeanUrat/Scaffold/MeasureFloor/Base.lean`, and every F stage
  with `lake env lean LeanUrat/Scaffold/MeasureFloor/SumOne.lean`.
  The milestone is conditional on the displayed TYPE/NS-NULL/LIN rows; the
  n = 2 corpus values remain anchors until the α-faithfulness tie exists.
* **WAVE 6 = H (14 rows, `NsNull.lean`).** It may begin only after B4c and E1;
  H4a/H4b also wait for E1. Stages are H1/H3a/H3b/H4a/H5; then H2/H4b;
  then H3c1/H3c2/H4c; then H3c3/H6; then H3c4/H7; then H8.
  Gate every stage with
  `lake env lean LeanUrat/Scaffold/MeasureFloor/NsNull.lean`.
  H3c1 waits for H3b, eliminating the former H3b→H4 forward dependency.
  Landing constructs `nsNullRowProved`; it never deletes or rewrites the
  stable row interface. If H4c stalls, keep the named row and record the exact
  API obstruction.
* **Cross-movement seams (report, don't build):** TYPE-OF +
  TYPE-OF-ISTYPE + LOC + LIN construction → Movement III (dictionary);
  K-12 `decided`/`hExhaustP`
  faithfulness audit → Movement III; `squeeze_unique`+`bracket_abstract`+
  `undec_tendsto_zero` names → Movement V (Step 19); `sum_R_eq_one_of_alpha_eq`
  + `hdef` row → Movements II/IV (O-12 pole-freeness supplies definedness);
  SEM-DRAIN-RATE (I-E9) parked pending a quantitative M05 import decision.

**Math-revision sync duty.** This blueprint folds Dfloor REV 2 (post-V17
repairs: the n ≥ 1 singleton hypothesis, the BASE-1(f) fence, the reordered
ADD proof — ADD itself is NOT in this movement's unit table; it ships with the
Movement-III `TypeSemantics` instance where `typeOf` is concrete). If Dfloor
revs again (three minor gaps ride the next doc touch, per ROOT Step 1's
status line), the owner of this file folds the delta before the affected wave
launches.

## REVISION 2 (review fold, 2026-08-03)
| finding | disposition | where / why |
|---:|---|---|
| 1 | FIXED | Added `isTopologicalBasis_cylinders` and the verbatim H0 equality `generateFrom_cylinders_eq_borel`; A2b/A2c now prove rather than rename σ(cyl)=Borel. |
| 2 | FIXED | Replaced monolithic `TypeSemantics` by `TypeData`, `LocalityRow`, and `NsNullRow`; α/bracket, limit, drainage, and SUM-ONE now expose exactly their consumed rows. |
| 3 | FIXED | The honesty display now lists TYPE-OF and TYPE-OF-ISTYPE as Movement-III inputs and explicitly denies a canonical root constructor in this movement. |
| 4 | FIXED | Added degree-unrestricted `ns_null_proved` with a `sep_zero` branch and stable `nsNullRowProved`; n=0 consumers are covered. |
| 5 | FIXED | Wave H no longer deletes a structure field; consumers retain the stable `NsNullRow` signature. |
| 6 | FIXED | Replaced the false internally-parallel claim by explicit dependency-ordered per-file stages. |
| 7 | FIXED | Added C2/B2 dependencies to C6/C8, removed H3b’s H4 forward dependency via independent H3b measurability, and delayed H until B4c/E1. |
| 8 | FIXED | Recounted the revised table explicitly as 72 rows, 71 scheduled plus one parked, without subtracting carrier rows. |
| 9 | FIXED | Removed the blanket 40-line claim and split zero-locus induction, generic discriminant naturality, semantic carriers, and other compound work at compiled lemma boundaries. |
| 10 | FIXED | Removed positive-degree hypotheses from PART and SUM-ONE; the degree-zero case is supported by BASE-0 and degree-unrestricted NS-NULL. |
| 11 | FIXED | BASE-0 now exposes type, strict verdict, count, undecided mass, α/αR, and exact bracket statements. |
| 12 | FIXED | Added `base1_alpha_eq_ratFunc_one`, explicitly tying α to the rational-function numerator/denominator evaluation at p. |
| 13 | FIXED | Reuse wording now distinguishes anchors from discharges and explicitly records the missing level equivalence and n=2 α-faithfulness tie. |
| 14 | FIXED | B7 now depends on the cylinder topological-basis theorem, which supplies positive basis neighborhoods before Haar uniqueness. |
| 15 | FIXED | Replaced the risky public Pi-invariance form by `μHaar_map_add`, made casts explicit in the one-variable zero locus, and demoted unverified Mathlib identifiers to compile-gated search hints. |
