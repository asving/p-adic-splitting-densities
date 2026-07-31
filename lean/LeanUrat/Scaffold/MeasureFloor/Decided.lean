/-
BP_I §1.3 — The abstract decided layer (`Decided.lean`), the T-layer import
shape.

Unit I-C1: `structure LevelVerdicts` (verdict + nested) +
`decidedSet`/`decidedCount`/`undecSet`/`undecMass` defs (statement-only;
Df §4.1 (5) abstracted; ROOT Step 1). The measurability/mono/mass/BRACKET/
limit/drainage shells are units I-C2–C6/C8 and land here as separate waves.
Unit I-C7: `squeeze_unique` — THE Theorem-U measure import (Step 19 seam;
T-U §U.SQ consumption). Pure real analysis, no unit deps; Movement V
consumes this ONE name.

**K-12 FAITHFULNESS SEAM (BP_I §3 corpus-reuse map, `OM.SeriesAssembly`
row).** The n = 2 ANCHOR: the count-side drainage + bracket are already
machine-checked at n = 2 (`OM.SeriesAssembly.hExhaust_n2`, `decided6_upper`,
+ the W6q census layer in `OM/SeriesAssembly.lean`). Gate duty: when Waves
C/E land, the n = 2 semantic shells must be CONSISTENT with these (same
limit values via `OM.UniformCapstone`); the formal tie of the
classifier-side `decided`/`hExhaustP` to the strict decided convention (5)
is the K-12 faithfulness audit row — a Movement III seam, displayed here
per the blueprint, NOT discharged in this movement.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space
import LeanUrat.Scaffold.MeasureFloor.Haar

namespace LeanUrat.Scaffold

open MeasureTheory

variable (p n : ℕ) [Fact p.Prime]

/-! ## Unit I-C1: the abstract `LevelVerdicts` structure + decided/undecided defs -/

/-- A per-level verdict assignment with NESTING (the abstract skeleton of the
decided conventions (5)/(6); brief §4.1, MEAS-BRIDGE(iii)'s mechanism). `T` is
the verdict alphabet (instantiated at degree-n splitting types). NESTED: a
class decided at level N stays decided, same verdict, at level N+1. -/
structure LevelVerdicts (p n : ℕ) [Fact p.Prime] (T : Type*) where
  verdict : (N : ℕ) → Level p n N → Option T
  nested : ∀ (N : ℕ) (x : Level p n (N + 1)) (τ : T),
    verdict N (levelCast p n N x) = some τ → verdict (N + 1) x = some τ

/-! ## Unit I-C2 helper: `toLevel` preimages are measurable -/

/-- I-C2 mechanism (BP row: "preimage of a set under `toLevel` = union of
fibers; I-A6"): the `toLevel` preimage of ANY level-N set is the (finite)
union of the fiber cylinders of its members, each measurable by I-A6
(`measurableSet_cylinder`). -/
theorem measurableSet_toLevel_preimage (N : ℕ) (S : Set (Level p n N)) :
    MeasurableSet (toLevel p n N ⁻¹' S) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out (p := p.Prime)).ne_zero⟩
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion (Set.to_countable S)
    fun x _ => measurableSet_cylinder p n N x

namespace LevelVerdicts

-- `p n` implicit here so the §1.3 dot-notation statements (`V.decidedSet τ N`,
-- `V.undecSet N`, …) elaborate as displayed in the blueprint.
variable {p n : ℕ} [Fact p.Prime] {T : Type*} (V : LevelVerdicts p n T)

/-- D_τ(N): the union of the τ-decided level-N classes (brief (5)). -/
def decidedSet (τ : T) (N : ℕ) : Set (Coeff p n) :=
  toLevel p n N ⁻¹' {x | V.verdict N x = some τ}

/-- decided_τ(N), the count. -/
noncomputable def decidedCount (τ : T) (N : ℕ) : ℕ :=
  Nat.card {x : Level p n N // V.verdict N x = some τ}

/-- U_N and undec(N) (brief §4.2). -/
def undecSet (N : ℕ) : Set (Coeff p n) := toLevel p n N ⁻¹' {x | V.verdict N x = none}

noncomputable def undecMass (N : ℕ) : ENNReal := μHaar p n (V.undecSet N)

/-! ## Unit I-C2 (decided half): measurable decided sets — the `toLevel`
preimage is a (finite) union of the fiber cylinders (Df §4 (ii)); each
cylinder is measurable by I-A6 (`measurableSet_cylinder`), via the
preimage helper above. -/

theorem measurableSet_decidedSet (τ : T) (N : ℕ) : MeasurableSet (V.decidedSet τ N) :=
  measurableSet_toLevel_preimage p n N _

/-! ## Unit I-C3: nesting in the large (Df §4 proof of (iii)) — monotone
decided sets, antitone undecided sets. `nested` + the I-A7 refinement
(`toLevel_levelCast`); complement for the antitone half. -/

theorem decidedSet_mono (τ : T) : Monotone (V.decidedSet τ) := by          -- (iii)
  refine monotone_nat_of_le_succ fun N a ha => ?_
  -- `ha` (definitionally): the level-N class of `a` carries verdict τ.
  have hcast : levelCast p n N (toLevel p n (N + 1) a) = toLevel p n N a :=
    congr_fun (toLevel_levelCast p n N) a
  -- I-A7 refinement + `nested`: the level-(N+1) class of `a` refines the
  -- decided level-N class, hence is decided with the same verdict.
  show V.verdict (N + 1) (toLevel p n (N + 1) a) = some τ
  exact V.nested N (toLevel p n (N + 1) a) τ (by rw [hcast]; exact ha)

theorem undecSet_antitone : Antitone V.undecSet := by
  refine antitone_nat_of_succ_le fun N a ha => ?_
  have ha' : V.verdict (N + 1) (toLevel p n (N + 1) a) = none := ha
  have hcast : levelCast p n N (toLevel p n (N + 1) a) = toLevel p n N a :=
    congr_fun (toLevel_levelCast p n N) a
  -- Complement of nesting: were the level-N class decided (`some τ`), `nested`
  -- would decide the level-(N+1) class, contradicting `ha'`.
  show V.verdict N (toLevel p n N a) = none
  cases hv : V.verdict N (toLevel p n N a) with
  | none => rfl
  | some τ =>
    exact absurd
      ((V.nested N (toLevel p n (N + 1) a) τ (by rw [hcast]; exact hv)).symm.trans ha')
      (Option.some_ne_none τ)

/-! ## Unit I-C2 (undec half, transcribed as the I-C8 prerequisite):
measurable undecided sets — the `toLevel` preimage is a finite union of
cylinders (Df §4 (ii)); each cylinder is measurable by I-A6. -/

theorem measurableSet_undecSet (N : ℕ) : MeasurableSet (V.undecSet N) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out (p := p.Prime)).ne_zero⟩
  have h : V.undecSet N
      = ⋃ x ∈ {x : Level p n N | V.verdict N x = none}, cylinder p n N x := by
    ext a
    simp [undecSet, cylinder, eq_comm]
  rw [h]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun x _ => measurableSet_cylinder p n N x)

/-! ## Unit I-C4: the decided mass law (Df §4 proof of (ii)) — decidedSet is
the disjoint union of its decided fiber cylinders; `measure_biUnion_finset` +
I-B4c (`μHaar_cylinder`) + the I-A3 card. (Deduped at the I-C4 landing with
the I-C5 prover's transcribed prerequisite copy — one canonical declaration.) -/

/-- MEAS-BRIDGE(ii) second half: mass = count · p^{−nN}. -/
theorem μHaar_decidedSet (τ : T) (N : ℕ) :
    μHaar p n (V.decidedSet τ N) = (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out (p := p.Prime)).ne_zero⟩
  classical
  -- decidedSet = the (disjoint, measurable) union of its decided fiber cylinders
  have hset : V.decidedSet τ N
      = ⋃ x ∈ Finset.univ.filter (fun x : Level p n N => V.verdict N x = some τ),
          cylinder p n N x := by
    ext a
    simp [decidedSet, cylinder, eq_comm]
  -- the subtype count reads as the fiber Finset card
  have hcount : V.decidedCount τ N
      = (Finset.univ.filter (fun x : Level p n N => V.verdict N x = some τ)).card := by
    rw [decidedCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc μHaar p n (V.decidedSet τ N)
      = ∑ x ∈ Finset.univ.filter (fun x : Level p n N => V.verdict N x = some τ),
          μHaar p n (cylinder p n N x) := by
        rw [hset]
        exact measure_biUnion_finset ((cylinder_disjoint p n N).set_pairwise _)
          fun x _ => measurableSet_cylinder p n N x
    _ = (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) := by
        rw [Finset.sum_congr rfl fun x _ => μHaar_cylinder p n N x,
          Finset.sum_const, nsmul_eq_mul, hcount, mul_one_div]

/-! ## Unit I-C5: the two-sided BRACKET shell (Df §4.2 Cor BRACKET) -/

/-- **BRACKET shell (brief Cor BRACKET; the semantic side of (U-GEN)(i)).**
For any measurable L trapped between the decided set and its undecided
complement, the two-sided level-N bracket holds. -/
theorem bracket_abstract {L : Set (Coeff p n)} (τ : T) (N : ℕ)
    (hlow : V.decidedSet τ N ⊆ L) (hcov : L ⊆ V.decidedSet τ N ∪ V.undecSet N) :
    (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) ≤ μHaar p n L ∧
    μHaar p n L ≤ (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) + V.undecMass N := by
  constructor
  · -- lower: monotonicity from `hlow`, decided mass read by I-C4
    rw [← V.μHaar_decidedSet τ N]
    exact measure_mono hlow
  · -- upper: monotonicity into the cover, subadditivity, I-C4 + `undecMass`
    calc μHaar p n L
        ≤ μHaar p n (V.decidedSet τ N ∪ V.undecSet N) := measure_mono hcov
      _ ≤ μHaar p n (V.decidedSet τ N) + μHaar p n (V.undecSet N) := measure_union_le _ _
      _ = (V.decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N) + V.undecMass N := by
          rw [V.μHaar_decidedSet τ N]; rfl

/-! ## Unit I-C8: the drainage shell (Df §4.2 Cor SEM-DRAIN measure half) -/

/-- Drainage shell (brief Cor SEM-DRAIN's measure half): if the residual
intersection is null, undec(N) ↓ 0. -/
theorem undec_tendsto_zero (hnull : μHaar p n (⋂ N, V.undecSet N) = 0) :
    Filter.Tendsto (fun N => (V.undecMass N).toReal) Filter.atTop (nhds 0) := by
  -- continuity from above at the antitone (I-C3), measurable (I-C2),
  -- finite-mass (I-B2 probability) undecided sequence
  have hlim : Filter.Tendsto (fun N => μHaar p n (V.undecSet N)) Filter.atTop
      (nhds (μHaar p n (⋂ N, V.undecSet N))) :=
    MeasureTheory.tendsto_measure_iInter_atTop
      (fun N => (V.measurableSet_undecSet N).nullMeasurableSet)
      V.undecSet_antitone ⟨0, measure_ne_top _ _⟩
  rw [hnull] at hlim
  -- `toReal` is continuous at the finite limit 0
  have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hlim
  simpa [undecMass, Function.comp_def] using h

/-! (dedup, wave-C merge: the I-C6 landing's transcribed I-C4 + I-C5
prerequisites — same BP-verbatim statements as the canonical `μHaar_decidedSet`
(I-C4 section) and `bracket_abstract` (I-C5 section) declared above — stood
here; removed, each theorem is declared once.) -/

/-! ## Unit I-C6: clause (0) shell — the cylinder-count limit (Df §4 proof
of (v)). Continuity from below (`tendsto_measure_iUnion_atTop`) at the
monotone (I-C3) decided sequence, the I-C4 mass law, and `ENNReal.toReal`
continuity at the probability-finite (I-B2) limit. NO drainage hypothesis. -/

set_option linter.unusedVariables false in
/-- **Clause (0) shell (brief MEAS-BRIDGE(v)): the cylinder-limit density.**
Continuity from below alone — NO drainage hypothesis (brief D-1(v) note).
(`hL` is blueprint-mandated interface; unused here since continuity from
below at a monotone sequence needs no measurability.) -/
theorem alpha_limit_abstract {L : Set (Coeff p n)} (τ : T)
    (hL : MeasurableSet L) (hexh : ⋃ N, V.decidedSet τ N = L) :
    Filter.Tendsto (fun N => (V.decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds ((μHaar p n L).toReal)) := by
  -- continuity from below at the monotone (I-C3) decided sequence
  have hlim : Filter.Tendsto (fun N => μHaar p n (V.decidedSet τ N)) Filter.atTop
      (nhds (μHaar p n L)) := by
    have h := MeasureTheory.tendsto_measure_iUnion_atTop (μ := μHaar p n)
      (V.decidedSet_mono τ)
    rw [hexh] at h
    simpa [Function.comp_def] using h
  -- `toReal` is continuous at the finite (I-B2 probability) limit
  have h := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  -- the I-C4 mass law + the I-B6 cast pack identify each term
  have heq : ∀ N, (μHaar p n (V.decidedSet τ N)).toReal
      = (V.decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N) := fun N => by
    rw [V.μHaar_decidedSet τ N, count_div_pow_toReal]
  exact (Filter.Tendsto.congr heq h :)

end LevelVerdicts

/-! ## Unit I-C7: the squeeze import -/

/-- **THE THEOREM-U MEASURE IMPORT (Step 19 seam; T-U §U.SQ consumption).**
Two reals obeying the same shrinking bracket are equal: the shape by which
the solve value R_τ(p) gets identified with α once the classifier-side counts
match. Pure real analysis; stated here so Movement V consumes ONE name. -/
theorem squeeze_unique {l u : ℕ → ℝ} {x y : ℝ}
    (hx : ∀ N, l N ≤ x ∧ x ≤ l N + u N) (hy : ∀ N, l N ≤ y ∧ y ≤ l N + u N)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0)) : x = y := by
  -- both in the bracket ⇒ |x − y| ≤ u N for every N
  have habs : ∀ N, |x - y| ≤ u N := by
    intro N
    obtain ⟨hx₁, hx₂⟩ := hx N
    obtain ⟨hy₁, hy₂⟩ := hy N
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- u → 0 ⇒ |x − y| ≤ 0 ⇒ x = y
  have h0 : |x - y| ≤ 0 := ge_of_tendsto hu (Filter.Eventually.of_forall habs)
  have hz : x - y = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  linarith

end LeanUrat.Scaffold
