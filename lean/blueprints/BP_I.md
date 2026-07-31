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
introduces NONE of (H1)–(H6) as hypothesis rows. It DOES carry three
interface rows of its own — **(LOC)**, **(NS-NULL)**, **(LIN)** below — which
are NOT open mathematics: they are Dfloor-internal VERIFIED math (brief §2
imports I-1/I-3 + §6.1) awaiting Lean discharge. (NS-NULL) has a discharge
wave inside this blueprint (Wave H); (LOC) and (LIN) discharge at the
Movement-III seam (the semantic `typeOf` construction). Until discharged they
are NAMED STRUCTURE FIELDS — never axioms (ground rule: no new axioms without
the full policy loop; the two audited axioms stay where they are).

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
| `Scaffold/MeasureFloor/Semantic.lean` | `mPoly`/`Sep`, `TypeSemantics` rows, MEAS-BRIDGE, SEM-DRAIN, α |
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
theorem μHaar_addLeftInvariant : (μHaar p n).IsAddLeftInvariant

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

/-- **THE INTERFACE ROW CARRIER** — the semantic inputs of Dfloor, as NAMED
FIELDS (never axioms). Provenance per field, displayed:
* `typeOf`/`typeOf_isType` — brief Thm TYPE (UFD + I-2 e·f = deg; the K-11/M16
  audited bridge). Lean discharge = the Movement-III dictionary seam (the
  concrete OM/QpType-side construction + `SerreLocalFields.AX_integralClosure_dvr`
  footprint); junk value off the separable locus.
* `locality` **(LOC)** — brief import I-1 (M05 Lemma D, V2-upheld, wild-valid):
  the type is constant on a small enough cylinder around every separable point.
  Stated at bare ∃N (the 2v+1 modulus is the RATE refinement, parked).
* `ns_null` **(NS-NULL)** — brief Appendix A / I-3 null clause. Discharge wave
  H below (then this field is REMOVED and consumers re-pointed at
  `NsNull.ns_null_proved`). -/
structure TypeSemantics (p n : ℕ) [Fact p.Prime] where
  typeOf : Coeff p n → FactorizationType
  typeOf_isType : ∀ a, Sep p n a → IsType n (typeOf a)
  locality : ∀ a, Sep p n a →
    ∃ N, ∀ b ∈ cylinder p n N (toLevel p n N a), Sep p n b ∧ typeOf b = typeOf a
  ns_null : μHaar p n {a | ¬ Sep p n a} = 0

variable (TS : TypeSemantics p n)

/-- L_τ (brief Cor PART). -/
def locus (τ : FactorizationType) : Set (Coeff p n) :=
  {a | Sep p n a ∧ TS.typeOf a = τ}

/-- The STRICT decided predicate (brief (5)): every lift separable of type τ. -/
def StrictDecided (N : ℕ) (x : Level p n N) (τ : FactorizationType) : Prop :=
  ∀ a ∈ cylinder p n N x, Sep p n a ∧ TS.typeOf a = τ

/-- The strict verdict assignment, packaged for the abstract layer (verdict by
choice on the ≤-one-τ fact; nesting from `cylinder_succ_subset`). -/
noncomputable def strictVerdicts : LevelVerdicts p n FactorizationType

theorem strictVerdicts_spec (N x τ) :
    (TS.strictVerdicts p n).verdict N x = some τ ↔ TS.StrictDecided p n N x τ

/-- MEAS-BRIDGE(iv), EXACT in the strict convention (the leaf's headline). -/
theorem iUnion_decided_eq_locus (τ) :
    ⋃ N, (TS.strictVerdicts p n).decidedSet τ N = TS.locus p n τ
theorem isOpen_locus (τ) : IsOpen (TS.locus p n τ)                    -- (i)

/-- **THE SCAFFOLD DENSITY (clause (0)'s α).** -/
noncomputable def alpha (τ : FactorizationType) : ENNReal := μHaar p n (TS.locus p n τ)
noncomputable def alphaR (τ : FactorizationType) : ℝ := (TS.alpha p n τ).toReal

/-- Clause (0): α is the cylinder-count limit (glue: `alpha_limit_abstract` +
`iUnion_decided_eq_locus`). -/
theorem alpha_eq_lim (τ) :
    Filter.Tendsto
      (fun N => ((TS.strictVerdicts p n).decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds (TS.alphaR p n τ))

/-- The cover L_τ ⊆ D_τ(N) ∪ U_N (brief Cor BRACKET upper half's set step). -/
theorem locus_subset_decided_union_undec (τ N) :
    TS.locus p n τ ⊆ (TS.strictVerdicts p n).decidedSet τ N ∪ (TS.strictVerdicts p n).undecSet N

/-- **Clause (SQ)'s bracket at the semantic instance** (glue via `bracket_abstract`). -/
theorem alpha_bracket (τ N) :
    ((TS.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        ≤ TS.alpha p n τ ∧
    TS.alpha p n τ ≤ ((TS.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        + (TS.strictVerdicts p n).undecMass p n N

/-- SEM-DRAIN: ⋂_N U_N = the nonseparable locus; hence undec ↓ 0 (via
`undec_tendsto_zero` + `ns_null`). Unconditional at every prime incl. wild. -/
theorem iInter_undec_eq_nonSep : ⋂ N, (TS.strictVerdicts p n).undecSet N = {a | ¬ Sep p n a}
theorem undec_tendsto_zero_sem :
    Filter.Tendsto (fun N => ((TS.strictVerdicts p n).undecMass p n N).toReal)
      Filter.atTop (nhds 0)
```

### 1.6 SUM-ONE and TRANSFER (`SumOne.lean`)

```lean
/-- Cor PART: the loci partition the separable locus over Σ_n. -/
theorem locus_pairwise_disjoint : Set.PairwiseDisjoint (typesFinset n) (TS.locus p n ·)
theorem sep_eq_biUnion_locus (hn : 1 ≤ n) :
    {a | Sep p n a} = ⋃ τ ∈ typesFinset n, TS.locus p n τ

/-- **SUM-ONE (Thm SUM-ONE(iii)): Σ_τ α(n,τ;p) = 1 at every p.** -/
theorem sum_alpha_eq_one (hn : 1 ≤ n) : ∑ τ ∈ typesFinset n, TS.alpha p n τ = 1
theorem sum_alphaR_eq_one (hn : 1 ≤ n) : ∑ τ ∈ typesFinset n, TS.alphaR p n τ = 1

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
theorem alpha_zero (TS : TypeSemantics p 0) (h∅ : TS.typeOf default = typeEmpty) :
    TS.alpha p 0 typeEmpty = 1                        -- decided at N = 0

-- BASE-1 (brief Thm BASE-1(a)–(e); SEMANTIC clauses ONLY — the (f) fence):
theorem sep_one (a : Coeff p 1) : Sep p 1 a           -- derivative = 1, IsCoprime trivial

/-- **(LIN) — the n = 1 normalization row**: monic linear ⇒ type {(1,1)}
(brief BASE-1(b): K_f ≅ ℚ_p, e = f = 1). Movement-III discharge; consumed
ONLY by the n = 1 instance below. -/
def LinRow (TS : TypeSemantics p 1) : Prop := ∀ a, TS.typeOf a = ⟨{(1, 1)}⟩

/-- **THE n = 1 ROOT INSTANCE (semantic clauses, unconditional given (LIN)):**
every class strictly decided at EVERY level including N = 0; counts = p^N;
undec = 0; α = 1 = R(p) with R := 1; bracket exact.  The ALGORITHMIC half
(one-state classifier, the 1×1 solve, count faithfulness) is BASE-1(f)'s
fence — classifier-side, NOT claimed here (V17 finding 2; lives at the
Movement-III/O-layer seams). -/
theorem base1_decided (TS) (hlin : LinRow p TS) (N x) :
    (TS.strictVerdicts p 1).verdict N x = some ⟨{(1, 1)}⟩
theorem base1_counts (TS) (hlin : LinRow p TS) (N) :
    (TS.strictVerdicts p 1).decidedCount ⟨{(1, 1)}⟩ N = p ^ N
theorem base1_undec (TS) (hlin : LinRow p TS) (N) :
    (TS.strictVerdicts p 1).undecMass p 1 N = 0
theorem base1_alpha (TS) (hlin : LinRow p TS) : TS.alphaR p 1 ⟨{(1, 1)}⟩ = 1
theorem base1_sumR : (∑ τ ∈ typesFinset 1, (1 : RatFunc ℚ)) = 1   -- Σ over the singleton menu
```

### 1.8 The (NS-NULL) discharge (`NsNull.lean`)

```lean
theorem μ₁_singleton (x : ℤ_[p]) : μ₁ p {x} = 0        -- coordinate case of (2′)
/-- Zero set of a nonzero one-variable polynomial is μ₁-null (finitely many
roots in the field + singleton-null). -/
theorem null_zeroLocus_one_var (f : Polynomial ℚ_[p]) (hf : f ≠ 0) :
    μ₁ p {x : ℤ_[p] | Polynomial.aeval x f = 0} = 0
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
/-- **(NS-NULL) PROVED** — replaces the TypeSemantics field on landing. -/
theorem ns_null_proved (hn : 1 ≤ n) : μHaar p n {a | ¬ Sep p n a} = 0
```

## 2. THE UNIT TABLE

Every unit ≤ ~40 lines of Lean. Difficulty: MECH (mechanical/defs), EASY
(one-idea proof), MED (several steps or API hunting), HARD (genuine work).
"Source" = the paragraph of `Dfloor_phaseB_verifybrief_rev2.md` (cited `Df
§…`) or `docs/ROOT_ASSEMBLY_2026-08-02.md` (cited `ROOT §…`) the unit
transcribes. Deps name unit ids + corpus/mathlib imports.

### Wave A — space and cylinders (`Space.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-A1 | `Coeff`, `Level` abbrevs + topology instances on `Coeff` (CompactSpace, T2, IsTopologicalAddGroup, SecondCountableTopology) | Pi closure of ℤ_[p] instances; `PadicInt.compactSpace`; second-countable from compact+metrizable (mathlib instance chain) | mathlib `NumberTheory/Padics/ProperSpace` | MECH | Df §1.1, Lemma H0 |
| I-A2 | `MeasurableSpace (Coeff p n) := borel` + `BorelSpace` instances (declared on ℤ_[p] then Pi) | `borel`/`BorelSpace` + `Pi.borelSpace` (needs I-A1 second-countability) | I-A1 | EASY | Df §1.1 H0 (σ(cyl)=Borel becomes the Borel-instance layer) |
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
| I-B3 | `μHaar_addLeftInvariant : (μHaar p n).IsAddLeftInvariant` | translation of a Pi space = Pi of coordinate translations; `Measure.pi_map_...`/`MeasurePreserving.pi` with per-slot `measurePreserving_add_left (μ₁)` | I-B1, I-B2 | MED | Df §1.2 H1 invariance ¶ |
| I-B4a | `μHaar_cylinder_eq` : any two level-N cylinders have equal mass | translate by a preimage difference: I-A8 gives g with toLevel g = x−y; I-A9 + `measure_preimage_add` (IsAddLeftInvariant) | I-A8, I-A9, I-B3 | EASY | Df §1.2 H1 uniqueness ¶ ("pairwise translates") |
| I-B4b | `sum_μHaar_cylinder : ∑ x, μHaar (cylinder N x) = 1` | finite disjoint cover (I-A5) + `measure_iUnion_fintype` + `IsProbabilityMeasure` | I-A5, I-A6, I-B2 | EASY | Df §1.2 H1 mass-law ¶ |
| I-B4c | **`μHaar_cylinder` (HAAR-ON-BOX)**: mass = 1/p^{nN} in ℝ≥0∞ | B4a: all masses equal m; B4b: card·m = 1; I-A3 card; solve in ℝ≥0∞ (`ENNReal.eq_div_iff`) | I-A3, I-B4a, I-B4b | EASY | Df §1.2 H1 (2) |
| I-B5 | `μHaar_singleton (hn : 1 ≤ n)` = 0, hypothesis DISPLAYED | {a} ⊆ cylinder N (toLevel a) for every N; `le_of_forall` + `ENNReal` power → 0 needs n ≥ 1 | I-B4c | EASY | Df §1.2 (2′) + non-removability note (V17 f.1) |
| I-B6 | `μHaar_cylinder_toReal` + `μHaar_decided-count cast pack` (ℝ≥0∞→ℝ→ℚ-compatible display lemmas) | `ENNReal.toReal_div`, `toReal_pow`, `Nat.cast` | I-B4c | MECH | ROOT §1 (0) display |
| I-B7 | (remark unit) `μHaar_eq_addHaar`: μHaar equals any Haar probability on `Coeff` — the H1 uniqueness, from mathlib | `isAddHaarMeasure_eq_of_isProbabilityMeasure` once `IsAddHaarMeasure (μHaar)` shown (open-pos on cylinders via B4c) | I-B3, I-B4c | MED | Df §1.2 H1 uniqueness (not consumed downstream; audit anchor) |

### Wave C — the abstract decided layer (`Decided.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-C1 | `structure LevelVerdicts` (verdict + nested), + `decidedSet`/`decidedCount`/`undecSet`/`undecMass` defs | statement-only | I-A7 (levelCast in `nested`) | MECH | Df §4.1 (5) abstracted; ROOT Step 1 |
| I-C2 | `measurableSet_decidedSet`/`_undecSet` (finite unions of cylinders) | preimage of a set under `toLevel` = union of fibers; I-A6 | I-A6, I-C1 | MECH | Df §4 (ii) |
| I-C3 | `decidedSet_mono` + `undecSet_antitone` | `nested` + I-A7 refinement: each level-(N+1) class inside a decided level-N class is decided; complement | I-A7, I-C1 | MED | Df §4 proof of (iii) |
| I-C4 | `μHaar_decidedSet = count/p^{nN}` | decidedSet = disjoint union over the decided fiber Finset; `measure_biUnion_finset` + I-B4c + card | I-B4c, I-C2 | EASY | Df §4 proof of (ii) |
| I-C5 | `bracket_abstract` (two-sided, hypothesis-carrying) | lower: `measure_mono hlow` + I-C4; upper: `measure_union_le` on hcov + I-C4 | I-C4 | EASY | Df §4.2 Cor BRACKET |
| I-C6 | `alpha_limit_abstract` (clause (0) shell) | `tendsto_measure_iUnion_atTop` (I-C3 monotone) + I-C4 rewrite + `ENNReal.toReal` continuity at finite value (`ENNReal.tendsto_toReal`) | I-C3, I-C4 | MED | Df §4 proof of (v) |
| I-C7 | **`squeeze_unique`** (the Theorem-U measure import) | \|x−y\| ≤ u N for all N (both in the bracket); `le_of_forall_lt` + `tendsto` ⇒ \|x−y\| ≤ 0 | pure ℝ | EASY | ROOT Step 19 squeeze machinery; Df §4.3 scope note |
| I-C8 | `undec_tendsto_zero` (drainage shell from a null intersection) | `tendsto_measure_iInter_atTop` (antitone I-C3, finite measure) + hnull + `toReal` | I-C3 | MED | Df §4.2 Cor SEM-DRAIN measure half |

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
| I-E2 | `structure TypeSemantics` — the (LOC)/(NS-NULL) ROW CARRIER + `typeOf_isType` | statement-only; provenance docstrings MANDATORY (I-1 = M05 Lemma D V2-upheld; NS-NULL = Df App A) | I-D1, I-E1 | MECH | Df §2 imports I-1/I-3; §3.2 TYPE |
| I-E3 | `StrictDecided` def + at-most-one-τ lemma + `strictVerdicts : LevelVerdicts` + `strictVerdicts_spec` | uniqueness: a class member witnesses both verdicts (Df Lemma EX's uniqueness half — nonemptiness of cylinders from I-A8, no measure needed); Option by `Classical.choice`; nested from I-A7 | I-A7, I-A8, I-C1 | MED | Df §4.1 (5) + Lemma EX |
| I-E4 | `iUnion_decided_eq_locus` (MEAS-BRIDGE(iv), EXACT) | ⊆: a is a lift of its own class; ⊇: (LOC) gives the decided level | I-E3, (LOC) row | MED | Df §4 proof of (iv) |
| I-E5 | `isOpen_locus` (i) + `measurableSet_locus` | union of cylinders via I-E4 + I-A6; or directly (LOC) neighborhoods | I-E4 | EASY | Df §4 proof of (i) |
| I-E6 | `alpha`/`alphaR` defs + **`alpha_eq_lim` (CLAUSE (0))** | glue: I-C6 at hexh := I-E4 | I-C6, I-E4, I-E5 | EASY | ROOT §1 (0); Df §4 (v) |
| I-E7 | `locus_subset_decided_union_undec` + **`alpha_bracket` (CLAUSE (SQ) bracket)** | either a's class is decided (verdict forced = τ by the lift argument) or undecided; then I-C5 | I-E3, I-C5 | MED | Df §4.2 BRACKET proof |
| I-E8 | `iInter_undec_eq_nonSep` + `undec_tendsto_zero_sem` (SEM-DRAIN) | a decided at some N ↔ a separable (⇐ is (LOC); ⇒ lift argument); complement; I-C8 + `ns_null` row | I-E4, I-C8, (NS-NULL) row | MED | Df §4.2 SEM-DRAIN |
| I-E9 | (parked row, statement displayed, NO proof unit) SEM-DRAIN-RATE with the I-3 tail bound | — consumes M05 Lemmas B+C quantitatively; schedule after Wave H | — | — | Df §4.2 SEM-DRAIN-RATE |

### Wave F — SUM-ONE + TRANSFER (`SumOne.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-F1 | `locus_pairwise_disjoint` + `sep_eq_biUnion_locus` | typeOf is a function (disjoint); `typeOf_isType` puts τ in the Finset (cover) | I-D2, I-E2 | EASY | Df §3.2 Cor PART |
| I-F2 | **`sum_alpha_eq_one` (SUM-ONE)** + ℝ version | 1 = μ(univ) = μ(nonSep) + Σ μ(locus): `measure_biUnion_finset` + (NS-NULL) row + I-F1 | I-F1, I-B2 | MED | Df §5 SUM-ONE(iii) |
| I-F3 | `ratFunc_eq_zero_of_infinite` (Lemma ID) | num/denom: A(z)=0 on infinite Z ⊆ ℚ-embedded ℕ ⇒ `Polynomial.eq_zero_of_infinite_isRoot` ⇒ num = 0 | mathlib RatFunc | MED | Df §5 Lemma ID |
| I-F4 | **`sum_R_eq_one_of_alpha_eq` (TRANSFER)** — abstract density family A + P as NAMED hypothesis rows (see §1.6 re-key note) | Q := Σ R_τ − 1 vanishes at P (`hsum` + `htie` per prime); I-F3; the (REG-p) instance remark cites `MovesU/RegPFinite.regP_cofinite` + `Nat.infinite_setOf_prime` | I-F3 (I-F2 supplies `hsum` at consumption) | MED | Df §5 TRANSFER + instances |
| I-F5 | (remark unit) instance rows: n = 1 (Wave G, unconditional), n = 2 (unconditional — corpus `UniformCapstone` values; direct table check 1/(q+1)+q/(2(q+1))·2 = 1 as a `RatFunc` computation) | `field_simp` on the n = 2 table | I-F4, corpus OM/UniformCapstone | EASY | Df §5 instances ¶ |

### Wave G — base cases (`Base.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-G1 | `Unique (Coeff p 0)` + `μHaar_zero_eq_dirac` + `sep_zero` + `alpha_zero` (BASE-0) | one-point space: every measure = mass·dirac, probability ⇒ dirac; mPoly = 1 separable (`Polynomial.separable_one`) | I-B2, I-E1 | EASY | Df §6.2 BASE-0 |
| I-G2 | `sep_one : ∀ a : Coeff p 1, Sep p 1 a` | mPoly = X + C a₀, derivative 1, `IsCoprime` with unit (`Polynomial.separable_X_add_C` shape) | I-E1 | EASY | Df §6.1 BASE-1(b) |
| I-G3 | `LinRow` def (the (LIN) row, Movement-III discharge) + `base1_decided` | (LIN) + I-G2 make StrictDecided at every (N, x) incl. N = 0 | I-E3, I-G2 | EASY | Df §6.1 BASE-1(b)(d) |
| I-G4 | `base1_counts` (= p^N) + `base1_undec` (= 0) | all classes decided (I-G3): count = card(Level p 1 N) = p^N (I-A3); undecSet = ∅ | I-A3, I-G3 | EASY | Df §6.1 BASE-1(d) |
| I-G5 | **`base1_alpha` (= 1) + `base1_sumR` — the n = 1 ROOT INSTANCE, semantic clauses; BASE-1(f) fence DISPLAYED in the docstring** | locus = univ (I-G2 + LIN); α = 1; bracket exact by I-G4; Σ over singleton menu (I-D4) | I-E6, I-G4, I-D4 | EASY | Df §6.1 BASE-1(c)(e)(f) |

### Wave H — the (NS-NULL) discharge (`NsNull.lean`)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| I-H1 | `μ₁_singleton = 0` | n = 1 coordinate case of I-B5 (or directly: singleton inside every 1-dim cylinder) | I-B4c | MECH | Df §1.2 (2′) |
| I-H2 | `null_zeroLocus_one_var` | f ≠ 0 over a field: finitely many roots (`Polynomial.setOf_isRoot_finite`); finite sets null by I-H1 + `measure_biUnion_null` | I-H1 | EASY | Df App A base case |
| I-H3a | measure-preserving splitting `Coeff p (m+1) ≈ ℤ_[p] × Coeff p m` for `Measure.pi` | `MeasureTheory.measurePreserving_piFinSuccAbove` (mathlib) specialization | I-B2 | MED | Df App A induction plumbing |
| I-H3b | slicing: μ(Z) = 0 if a.e. slice is μ₁-null | `MeasureTheory.measure_prod_null` (+ measurability of the zero locus: polynomial maps continuous — needs I-H4's eval form) | I-H3a | MED | Df App A Tonelli step |
| I-H3c | **`null_zeroLocus` (Lemma NULL)** by induction on m | leading-coefficient split: write P in the last variable; the locus where the top slice-poly is identically 0 recurses (nonzero lower-dim polynomial); elsewhere I-H2 per slice; assemble via I-H3b | I-H2, I-H3a, I-H3b | HARD | Df App A Lemma NULL |
| I-H4 | `discrPoly` + `discr_mPoly_eq_eval` (naturality) | discr of the generic polynomial over `MvPolynomial (Fin n) ℚ_[p]`; `Polynomial.discr`/resultant commute with `Polynomial.map` along `aeval` (Sylvester-determinant naturality — mathlib `resultant_map` if present, else `RingHom.map_det`) | mathlib Resultant/Basic | HARD | Df §3.1 SEP(i) |
| I-H5 | `sep_iff_discr_ne_zero` | Separable = IsCoprime f f′; monic ⇒ `isUnit_resultant_iff_isCoprime`; field ⇒ unit ↔ ≠ 0 (`resultant_eq_zero_iff`); discr vs resultant unwind | mathlib | MED | Df §3.1 SEP(ii) |
| I-H6 | `discrPoly_ne_zero` via the witness ∏ᵢ (X − pⁱ) | distinct roots pⁱ ⇒ separable (`Polynomial.separable_prod_X_sub_C_iff`) ⇒ discr ≠ 0 (I-H5) ⇒ eval of discrPoly ≠ 0 at the witness coefficients (I-H4) | I-H4, I-H5 | MED | Df §3.1 SEP(iii) |
| I-H7 | **`ns_null_proved`** + the re-point PR (delete the `ns_null` field, wire consumers) | nonSep = zero locus of discrPoly (I-H4 + I-H5, n ≥ 1); I-H3c + I-H6 | I-H3c–I-H6 | EASY | Df App A + §2 I-3 |

Unit count: 41 rows, 38 provable units + 1 statement-parked (I-E9) + 2
structure/def-only carriers (I-C1, I-E2). Nothing exceeds ~40 lines; the two
HARD units (I-H3c, I-H4) are the movement's only genuine work and sit OFF the
(0)/(SQ) critical path (they upgrade a named row, they do not gate it).

## 3. THE CORPUS-REUSE MAP

Which existing PROVED declarations discharge (or anchor) which parts of this
movement. Reuse is BY IMPORT; no fenced statement is touched; parked items
22–29 untouched.

| corpus declaration (module) | discharges / anchors |
|---|---|
| `MovesV.SkeletonFinite.skeleton_finite` | **ROOT Step 3 wholesale** (O-13 menu finiteness). No Movement-I unit; listed because Step 3 sits in this movement's step range. D-12r stays a Movement-III residue. |
| `MovesU/RegPFinite.lean` (`regP_cofinite`, `regP_failing_finite`, `RegP.detFull_ne_zero`, …) | **ROOT Step 4 wholesale** (K-13 (REG-p) finiteness, 14 theorems, Lean-core). Consumed by I-F4's (REG-p) instance remark: the hypothesis set P infinite = `regP_cofinite` + infinitude of primes. |
| `MovesU/O12PoleFree.lean` + `MovesU/BridgeSolve.lean`/`BridgeKernels.lean` | Movement II/IV territory (Step 5 / T-8); named here only as the consumers of I-F4's definedness row `hdef` (pole-freeness supplies it at every prime power). |
| `MovesX.polyOfCoeffs`, `MovesX.MonicBox`, `MovesX.discZero`, `MovesX.vdisc` (`MovesX/Defs.lean`) | I-E1's `mPoly` reuses `polyOfCoeffs` VERBATIM (dedup rule: no parallel poly-builder). `MonicBox ≃ Coeff` transport is a deferred remark unit; `discZero`/`vdisc` align Wave H's discriminant locus with the MovesX carrier. |
| `MovesX.XCtx.frac` interface + `MovesX.discZeroNull` (XF10) + `Kernels/KA4c.ka4c_nsFiberUnion_null` | PAYOFF, not dependency: `μHaar` + I-B4c + I-H7 eventually furnish the first GENUINE (measure-backed) `frac` candidate for the frozen `XCtx` interface (`frac_univ`/`frac_mono`/`frac_iUnion_null` = probability-measure facts; `vdisc_le_tail` = I-B4c + a count). Recorded for the division lead; NOT a wave here (XCtx interface frozen by standing adjudications). |
| `OM.QuotientBox.ResidueRing`, `card_residueRing`, `card_monicBox` (`OM/QuotientBox.lean`) | I-A3's card computation pattern; the tuple↔monic-polynomial level-space bridge (`card_monicBox` = the polynomial-side count at `Level`); keeps Movement-IV counts comparable. |
| `OM.SeriesAssembly.hExhaust_n2`, `decided6_upper`, + the W6q census layer (`OM/SeriesAssembly.lean`) | The n = 2 ANCHOR: the count-side drainage + bracket already machine-checked at n = 2. Gate duty: when Waves C/E land, the n = 2 semantic shells must be CONSISTENT with these (same limit values via `UniformCapstone`); the formal tie of the classifier-side `decided`/`hExhaustP` to the strict convention (5) is the K-12 faithfulness audit row — Movement III seam, displayed in `Decided.lean`'s module docstring. |
| `OM.UniformCapstone` (`uniformValueFn`, `montes_uniform_n2`, value/denominator lemmas) | I-F5's n = 2 unconditional TRANSFER instance (P = all primes); the n = 2 table for the direct Σ = 1 check. |
| `LeanUrat/RatFn.lean` (`IsRationalFn` + closure lemmas) | Compatibility remark for I-F3/I-F4: the corpus's ℕ→ℚ rational-function predicate vs `RatFunc ℚ`; a one-lemma bridge (`IsRationalFn` of `fun q => R.eval q`) IF a consumer wants it — not on the spine. |
| `OM/LimitSpine.lean`, `OM/LevelNCount.lean`, `NestedCollapse.geometricLimit_of_selfLoop` | Movement IV/V's count-side limit engine. Movement I's I-C6/I-C7 are their MEASURE-side counterparts; no shared code, but the division leads should keep `Filter.Tendsto`-at-`atTop`-`nhds` phrasing IDENTICAL (it already matches) so Step 19's composition is definitional. |
| `Moves/L6_measureExact_R4.lean` (`LandingCylinderL`, `hexact`) | Precedent only: the Moves-layer cylinder-exactness pattern (R1 re-point, signed off 2026-07-30). No import. |
| `SerreLocalFields.AX_integralClosure_dvr` (audited axiom) + `GMNIndex` | The eventual Movement-III discharge of `TypeSemantics.typeOf`/`typeOf_isType` (I-2's e·f = deg enters THERE, not in this movement). Axiom-footprint rule: `Scaffold/MeasureFloor/*` stays Lean-core — the axiom must NOT enter any Wave A–H unit (it may enter the Movement-III instance file that CONSTRUCTS a `TypeSemantics`). AxChk duty at every division checkpoint. |
| mathlib (pinned 4.31 tree, verified present) | `PadicInt.compactSpace` (ProperSpace.lean:55); `PadicInt.toZModPow` + `ker_toZModPow` (RingHoms.lean:445/457); `Measure.addHaarMeasure` + `addHaarMeasure_self` + Haar instances (Haar/Basic.lean:517–570, `to_additive`); `⊤ : PositiveCompacts` + `coe_top` (Topology/Sets/Compacts.lean:570/584); `isAddHaarMeasure_eq_of_isProbabilityMeasure` (Haar/Unique.lean:692); `measure_preimage_add` (Group/Measure.lean:231 additive twin); `tendsto_measure_iUnion_atTop` (MeasureSpace.lean:648); `Measure.pi`; `Polynomial.discr` (RingTheory/Polynomial/Resultant/Basic.lean:930) + `isUnit_resultant_iff_isCoprime` (:885) + `resultant_eq_zero_iff` (:908); `Polynomial.eq_zero_of_infinite_isRoot` (Roots.lean:145); `RatFunc`. Names NOT yet verified (E-phase `lean_local_search` duty, flagged): `PadicInt.continuous_toZModPow`? (I-A6 fallback: locally-constant), the exact `toZModPow` section lemma (I-A8), `measurePreserving_piFinSuccAbove` exact name (I-H3a), `resultant_map` naturality (I-H4 — the riskiest external dependency; if absent, I-H4 upgrades to writing Sylvester-matrix naturality by hand, still ≤ 3 units). |

**Statement-fence note.** No existing statement is modified. The capstone
`OM/UniformCapstone.montes_uniform_n2` and the V2 spine stay untouched; the
scaffold restatement of the capstone onto `alpha`/`alpha_eq_lim` is the
INTEGRATION architect's seam (BP of the spine movement), consuming this
blueprint's I-E6 as its density definition.

## 4. THE WAVE PLAN (for the division lead)

Dependency-ordered; waves are internally parallel (every row within a wave is
independent given the prior waves). Per-file gates during waves; `lake build`
+ `lake env lean LeanUrat/AxChk_baseline.lean` at each checkpoint; commit per
wave with explicit paths.

* **WAVE 1 = A (9 units, Space.lean).** No intra-repo deps. Riskiest: I-A8
  (section of `toZModPow`) — assign it first, with the fallback route named.
  Gate: file compiles, no sorry, Lean-core.
* **WAVE 2 = B (7 units, Haar.lean) + D (5 units, Types.lean) in parallel.**
  B needs A; D needs only the corpus `FactorizationType`. Riskiest: I-B3
  (pi invariance). I-B7 is optional (audit anchor) — do not block the wave on
  it. Gate: `μHaar_cylinder` PROVED = **Haar-on-Box landed**; spot-check
  `#eval`-style: the ℝ display at (p,n,N) = (3,2,1) equals 1/9 by `norm_num`.
* **WAVE 3 = C (8 units, Decided.lean).** Needs A + B. I-C7 (`squeeze_unique`)
  has NO deps — it may run in Wave 1 if Movement V wants its name early;
  it is the Step-19 seam and its name is FROZEN on landing.
* **WAVE 4 = E (8 units, Semantic.lean) + G1 (BASE-0).** Needs C + D + the
  row carrier I-E2. On landing: **clauses (0) and (SQ) exist as Lean
  statements at the scaffold spine**, conditional exactly on the displayed
  (LOC)/(NS-NULL) rows — report this milestone to the orchestrator verbatim
  WITH the row conditionality (never as "clause (0) machine-checked
  unconditionally" until Wave H + Movement III land).
* **WAVE 5 = F (5 units, SumOne.lean) + G2–G5 (n = 1 instance).** Needs E.
  Milestone: SUM-ONE + TRANSFER + the n = 1 root instance = ROOT Step 1's
  Delivers-line complete at the statement layer.
* **WAVE 6 = H (9 units, NsNull.lean).** Independent of C–G except I-B4c/I-E1;
  may start alongside Wave 3 if prover capacity allows. Lands = the
  (NS-NULL) row DELETED from `TypeSemantics` (a statement change to a
  NEW-in-this-campaign structure — allowed, but re-run every consumer and
  re-report the conditionality line). Escalation: if I-H4 stalls > 2 rounds
  (resultant naturality), park Wave H, KEEP the row, and record the exact
  obstruction — the (0)/(SQ) spine does not wait.
* **Cross-movement seams (report, don't build):** (LOC)+(LIN)+`typeOf`
  construction → Movement III (dictionary); K-12 `decided`/`hExhaustP`
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
