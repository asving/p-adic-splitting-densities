/-
BP_I §1.2 — Haar and the box mass law (MeasureFloor).
Unit I-B1: `μ₁` def + `IsProbabilityMeasure (μ₁ p)` + the
`IsAddLeftInvariant` instance re-export (Df §1.2 H1(a) existence).
Unit I-B2: `μHaar` def (`Measure.pi` of `μ₁`) + `IsProbabilityMeasure
(μHaar p n)` via `Measure.pi_univ` product of 1s (Df §1.2 H1 "PRODUCT FORM").
Rests on the I-A1/I-A2 instance layer in `Space.lean`
(Borel σ-algebra on ℤ_[p]; compact T2 topological add-group).
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space

namespace LeanUrat.Scaffold

open MeasureTheory TopologicalSpace

variable (p : ℕ) [Fact p.Prime]

/-- Normalized Haar probability on ℤ_p: `addHaarMeasure` at the positive
compact ⊤ of the compact group (brief Prop H1(a) existence). -/
noncomputable def μ₁ (p : ℕ) [Fact p.Prime] : MeasureTheory.Measure ℤ_[p] :=
  MeasureTheory.Measure.addHaarMeasure ⊤

instance : MeasureTheory.IsProbabilityMeasure (μ₁ p) :=
  ⟨by rw [μ₁, ← PositiveCompacts.coe_top (α := ℤ_[p])]
      exact Measure.addHaarMeasure_self⟩

instance : (μ₁ p).IsAddLeftInvariant :=   -- addHaarMeasure instance, re-exported
  inferInstanceAs
    (MeasureTheory.Measure.addHaarMeasure (⊤ : PositiveCompacts ℤ_[p])).IsAddLeftInvariant

/-! ## Unit I-B2: the product Haar probability on `Coeff` -/

variable (n : ℕ)

/-- Haar probability on the coefficient space: the n-fold product (brief Prop
H1 "μ = μ₁^{⊗n}"; product form BY DEFINITION here, uniqueness available from
mathlib `isAddHaarMeasure_eq_of_isProbabilityMeasure` as a remark unit). -/
noncomputable def μHaar (p n : ℕ) [Fact p.Prime] : MeasureTheory.Measure (Coeff p n) :=
  MeasureTheory.Measure.pi fun _ => μ₁ p

instance : MeasureTheory.IsProbabilityMeasure (μHaar p n) :=
  ⟨by rw [μHaar, MeasureTheory.Measure.pi_univ]; simp⟩

/-! ## Unit I-B3a: per-coordinate translation is measure-preserving for `μ₁` -/

/-- I-B3a: translation by a fixed `c : ℤ_[p]` preserves `μ₁` — projected out
of the installed `IsAddLeftInvariant` Haar API (Df §1.2 H1 invariance ¶). -/
theorem μ₁_measurePreserving_add_left (c : ℤ_[p]) :
    MeasureTheory.MeasurePreserving (fun x => c + x) (μ₁ p) (μ₁ p) :=
  MeasureTheory.measurePreserving_add_left (μ₁ p) c

/-! ## Unit I-B3b: translation invariance of `μHaar`, as a public map equality -/

/-- Translation invariance, exported without freezing the version-sensitive
`IsAddLeftInvariant` instance shape for a `Measure.pi`. -/
theorem μHaar_map_add (g : Coeff p n) :
    Measure.map (fun a => g + a) (μHaar p n) = μHaar p n :=
  (MeasureTheory.measurePreserving_pi (fun _ => μ₁ p) (fun _ => μ₁ p)
    (fun i => μ₁_measurePreserving_add_left p (g i))).map_eq

/-! ## Unit I-B4b: the level-N cylinder masses sum to 1 -/

/-- The p^{nN} level-N cylinders are a finite disjoint measurable cover
(I-A5/I-A6), so their masses sum to the total mass 1 (Df §1.2 H1 mass law).
Proof note: the BP sketch's `measure_iUnion_fintype` is not in this mathlib;
`measure_iUnion` (countable, tsum form) + `tsum_fintype` is the same fact. -/
theorem sum_μHaar_cylinder (N : ℕ) :
    ∑ x, μHaar p n (cylinder p n N x) = 1 :=
  calc ∑ x, μHaar p n (cylinder p n N x)
      = ∑' x, μHaar p n (cylinder p n N x) :=
        (tsum_fintype fun x => μHaar p n (cylinder p n N x)).symm
    _ = μHaar p n (⋃ x, cylinder p n N x) :=
        (measure_iUnion (cylinder_disjoint p n N)
          (measurableSet_cylinder p n N)).symm
    _ = 1 := by rw [iUnion_cylinder, measure_univ]

/-! ## Unit I-B7 (optional remark): Haar uniqueness on `Coeff` -/

/-- I-B7 (Df §1.2 H1 uniqueness; not consumed downstream): `μHaar` equals ANY
Haar probability measure on `Coeff`. The exact API compiled here: `μHaar` is
itself add-Haar (`Measure.pi.isAddHaarMeasure` over the `addHaarMeasure ⊤`
slots), and two add-Haar probabilities on the compact group coincide by
mathlib `isAddHaarMeasure_eq_of_isProbabilityMeasure`. -/
theorem μHaar_eq_addHaar (ν : MeasureTheory.Measure (Coeff p n))
    [ν.IsAddHaarMeasure] [MeasureTheory.IsProbabilityMeasure ν] :
    μHaar p n = ν := by
  haveI : (μ₁ p).IsAddHaarMeasure :=
    inferInstanceAs
      (MeasureTheory.Measure.addHaarMeasure (⊤ : PositiveCompacts ℤ_[p])).IsAddHaarMeasure
  haveI : (μHaar p n).IsAddHaarMeasure :=
    inferInstanceAs (MeasureTheory.Measure.pi fun _ : Fin n => μ₁ p).IsAddHaarMeasure
  exact MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure (μHaar p n) ν

/-! ## Unit I-B4a: any two level-N cylinders have equal mass -/

/-- Any two level-N cylinders have equal mass: translate by a preimage
difference — I-A8 (`toLevel_surjective`) gives g with `toLevel g = x - y`;
rewrite by I-A9 (`cylinder_vadd`) and I-B3b's map equality (Df §1.2 H1
uniqueness ¶, "pairwise translates"). -/
theorem μHaar_cylinder_eq (N : ℕ) (x y : Level p n N) :
    μHaar p n (cylinder p n N x) = μHaar p n (cylinder p n N y) := by
  obtain ⟨g, hg⟩ := toLevel_surjective p n N (x - y)
  have hmeas : Measurable (fun a : Coeff p n => g + a) :=
    (continuous_const.add continuous_id).measurable
  calc μHaar p n (cylinder p n N x)
      = Measure.map (fun a => g + a) (μHaar p n) (cylinder p n N x) := by
        rw [μHaar_map_add]
    _ = μHaar p n ((fun a => g + a) ⁻¹' cylinder p n N x) :=
        Measure.map_apply hmeas (measurableSet_cylinder p n N x)
    _ = μHaar p n (cylinder p n N y) := by
        rw [show (fun a : Coeff p n => g + a) = (g + ·) from rfl,
          cylinder_vadd p n N g x, hg, sub_sub_cancel]

/-! ## Unit I-B4c: HAAR-ON-BOX — the level-N box mass law

(dedup, wave-2 merge: a second concurrently-landed copy of `μHaar_cylinder` —
same BP-verbatim statement, `ENNReal.eq_div_iff`-first calc route — stood
here; removed, the theorem is declared once below.) -/

/-- **HAAR-ON-BOX (brief Prop H1 (2); D-1(ii)'s layer; MEAS-BRIDGE(ii) first
half).** Every level-N class has Haar mass exactly p^{−nN}. -/
theorem μHaar_cylinder (N : ℕ) (x : Level p n N) :
    μHaar p n (cylinder p n N x) = 1 / (p : ENNReal) ^ (n * N) := by
  -- the I-A3 count p^{nN}, cast into ℝ≥0∞
  have hcard : (Fintype.card (Level p n N) : ENNReal) = (p : ENNReal) ^ (n * N) := by
    have h := card_level p n N
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  -- all level-N masses are equal (I-B4a), so the mass law (I-B4b) reads card·m = 1
  have hconst : ∑ y : Level p n N, μHaar p n (cylinder p n N y)
      = (Fintype.card (Level p n N) : ENNReal) * μHaar p n (cylinder p n N x) := by
    rw [Finset.sum_congr rfl fun y _ => μHaar_cylinder_eq p n N y x,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmul : (p : ENNReal) ^ (n * N) * μHaar p n (cylinder p n N x) = 1 := by
    rw [← hcard, ← hconst, sum_μHaar_cylinder]
  have hne0 : ((p : ENNReal) ^ (n * N)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero)
  have hnetop : ((p : ENNReal) ^ (n * N)) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  -- solve card·m = 1 for m in ℝ≥0∞
  rw [ENNReal.eq_div_iff hne0 hnetop]
  exact hmul

/-! ## Unit I-B5: singletons are null (n ≥ 1 DISPLAYED) -/

/-- I-B5 support: the punctured neighborhood filter of 0 in ℤ_[p] is
nontrivial — the nonzero sequence p^k → 0 accumulates at 0. Feeds mathlib's
`IsAddHaarMeasure.noAtoms`. -/
instance : (nhdsWithin (0 : ℤ_[p]) {(0 : ℤ_[p])}ᶜ).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have hplt : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    have h1p : 1 < (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt
    rw [inv_lt_one_iff₀]
    exact Or.inr h1p
  have hp0 : (p : ℤ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero
  refine mem_closure_of_tendsto (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hplt)
    (Filter.Eventually.of_forall fun k => ?_)
  simpa using pow_ne_zero k hp0

/-- (2′) with its DISPLAYED n ≥ 1 hypothesis (V17 finding 1: FALSE at n = 0,
where μHaar is the Dirac mass — BASE-0). -/
theorem μHaar_singleton (hn : 1 ≤ n) (a : Coeff p n) : μHaar p n {a} = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : (μ₁ p).IsAddHaarMeasure :=
    inferInstanceAs
      (MeasureTheory.Measure.addHaarMeasure (⊤ : PositiveCompacts ℤ_[p])).IsAddHaarMeasure
  haveI : MeasureTheory.NoAtoms (μ₁ p) := inferInstance
  show MeasureTheory.Measure.pi (fun _ : Fin n => μ₁ p) {a} = 0
  exact MeasureTheory.measure_singleton a

/-! ## Unit I-B6: `μHaar_cylinder_toReal` + the decided-count cast pack
(ROOT §1 (0) display; ℝ≥0∞ → ℝ → ℚ-compatible display lemmas).

Dependency note (historical): I-B6 landed before I-B4c, deriving the mass
law in a `private` scaffold lemma; per its DEDUP note, the I-B4c landing
re-pointed `μHaar_cylinder_toReal` at the public `μHaar_cylinder` above and
deleted the private lemma. -/

/-- The ROOT §1 (0) display of HAAR-ON-BOX: the level-N cylinder mass, read
in ℝ through `ENNReal.toReal` (I-B6). -/
theorem μHaar_cylinder_toReal (N : ℕ) (x : Level p n N) :
    (μHaar p n (cylinder p n N x)).toReal = 1 / (p : ℝ) ^ (n * N) := by
  rw [μHaar_cylinder p n N x, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

omit [Fact p.Prime] in
/-- Decided-count cast pack (I-B6), ℝ≥0∞ → ℝ leg: a normalized count
`c/p^{nN}` computed in ℝ≥0∞ (where the Wave-C mass law `μHaar_decidedSet`
lives) reads in ℝ as the same display. -/
theorem count_div_pow_toReal (c N : ℕ) :
    ((c : ENNReal) / (p : ENNReal) ^ (n * N)).toReal = (c : ℝ) / (p : ℝ) ^ (n * N) := by
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

omit [Fact p.Prime] in
/-- Decided-count cast pack (I-B6), ℚ → ℝ leg: the corpus's count-side spine
stores normalized counts in ℚ; its real display agrees with the measure-side
one. -/
theorem ratCast_count_div_pow (c N : ℕ) :
    (((c : ℚ) / (p : ℚ) ^ (n * N) : ℚ) : ℝ) = (c : ℝ) / (p : ℝ) ^ (n * N) := by
  push_cast
  ring

end LeanUrat.Scaffold
