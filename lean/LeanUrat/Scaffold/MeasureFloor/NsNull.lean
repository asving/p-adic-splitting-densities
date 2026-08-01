/-
BP_I §1.8 — the (NS-NULL) discharge (MeasureFloor).
Unit I-H1: `μ₁_singleton` — singletons in ℤ_[p] are μ₁-null; the n = 1
coordinate case of (2′) (Df §1.2 (2′)). Rests on the Haar layer of
`Haar.lean` (I-B1's `μ₁`, the punctured-neighborhood `NeBot` instance,
and the `addHaarMeasure` instance chain).
Unit I-H3b: zero-locus measurability for an `MvPolynomial` evaluation on
`Coeff` — the evaluation map is continuous after the explicit ℤ_p→ℚ_p cast
(casts explicit per REVISION 2 finding 15), so the zero locus is closed,
hence Borel-measurable (Df App A Tonelli step; the set expression is the
one BP_I §1.8's `null_zeroLocus` displays verbatim, and I-H3c1/I-H3c2
consume this measurability).
Unit I-H4a: the generic monic polynomial (`genericMonic`) and `discrPoly`,
verbatim per BP_I §1.8 (Df §3.1 SEP(i)). REUSE: `MovesX.polyOfCoeffs`
VERBATIM at the coefficient-variable ring (dedup rule: no parallel
poly-builder). Unit lemmas `genericMonic_monic`, `genericMonic_natDegree`
anchor the "generic MONIC polynomial" claim and feed I-H4c's discriminant
naturality. The degree bound `polyOfCoeffs_lower_degree_lt'` is re-proved
file-locally because both existing copies (MovesX/Defs, Semantic) are
`private`.
Unit I-H4b: `genericMonic_eval_eq_mPoly` — generic-polynomial evaluation
equals `mPoly` (Df §3.1 SEP(i)); table-only row, statement designed by the
prover (see the in-file provenance note), with the evaluation hom keyed to
the `MvPolynomial.aeval` cast tuple of I-H4c's verbatim statement.
Unit I-H3c1: `prod_null_of_ae_null_slices` (+ the `Coeff p (m+1)`-shaped
corollary `μHaar_succ_null_of_ae_null_slices` consuming I-H3a's transport) —
the slicing lemma: a measurable set with almost-everywhere μ₁-null slices is
product-null (product-measure/Tonelli null-section theorem; Df App A Tonelli
step, the μ_m(Z) = ∫ μ₁(Z_{y′}) dμ_{m−1}(y′) display). Table-only row (no
§1.8 verbatim display).
Unit I-H4c: `discr_mPoly_eq_eval`, verbatim per BP_I §1.8 — discriminant
naturality under ring maps (Df §3.1 SEP(i)). The BP §3 search hint
`resultant_map` resolves POSITIVELY in the pinned tree as mathlib's
`Polynomial.resultant_map_map` (Sylvester matrices at FIXED explicit sizes
commute with entrywise maps — no degree hypotheses), so per the BP row the
fallback determinant-naturality proof is NOT needed. The reusable kernel is
`discr_map_of_monic`: for MONIC f with nontrivial target,
`(f.map φ).discr = φ f.discr`, by `Polynomial.resultant_deriv` on both
sides with `resultant_map_map` in the middle (monicity keeps `natDegree`
and kills the `leadingCoeff` factor; the `(-1)^k` sign is a unit, so it
cancels); the `natDegree = 0` corner is `Monic.natDegree_eq_zero_iff_eq_one`
+ `discr_C`. Consumes I-H4a (`genericMonic`, `discrPoly`) and I-H4b
(`genericMonic_eval_eq_mPoly`, the prover-designed statement — this
consumption is part of what the division lead ratifies).
Unit I-H5: `sep_iff_discr_ne_zero` — SEP(ii), verbatim per BP_I §1.8.
Separable = IsCoprime f f′ (mathlib `Polynomial.separable_def`); monic ⇒
`isUnit_resultant_iff_isCoprime`; field ⇒ unit ↔ ≠ 0 (`isUnit_iff_ne_zero`);
the discr-vs-resultant unwind is mathlib `Polynomial.resultant_deriv`:
Res(f, f′) = (−1)^{n(n−1)/2} · lc(f) · discr(f) at positive degree, with
lc = 1 by monicity and the sign a unit of the field (Df §3.1 SEP(ii)).
Unit I-H6: `discrPoly_ne_zero` — SEP(iii), verbatim per BP_I §1.8: the
witness ∏ᵢ (X − pⁱ) (unit helpers `sepWitnessPoly`/`sepWitnessCoeffs`) has
distinct roots (pⁱ = pʲ ⇒ i = j via `Nat.cast_injective` in char 0 +
`Nat.pow_right_injective` at 2 ≤ p), hence is separable
(`separable_prod_X_sub_C_iff`); I-H5 turns that into discr ≠ 0, and the
I-H4c evaluation law reads it as a nonvanishing value of `discrPoly`
(Df §3.1 SEP(iii)).
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Haar
import LeanUrat.Scaffold.MeasureFloor.Semantic
import LeanUrat.MovesX.Defs

namespace LeanUrat.Scaffold

open MeasureTheory TopologicalSpace

variable (p : ℕ) [Fact p.Prime]

/-! ## Unit I-H1: singletons are μ₁-null (coordinate case of (2′)) -/

/-- I-H1: every singleton of ℤ_[p] is μ₁-null — the n = 1 coordinate case of
(2′) (Df §1.2 (2′)). μ₁ is an additive Haar measure on a group whose
punctured neighborhood filter at 0 is nontrivial (instance in `Haar.lean`),
so it has no atoms. -/
theorem μ₁_singleton (x : ℤ_[p]) : μ₁ p {x} = 0 := by
  haveI : (μ₁ p).IsAddHaarMeasure :=
    inferInstanceAs
      (MeasureTheory.Measure.addHaarMeasure (⊤ : PositiveCompacts ℤ_[p])).IsAddHaarMeasure
  haveI : MeasureTheory.NoAtoms (μ₁ p) := inferInstance
  exact MeasureTheory.measure_singleton x

/-! ## Unit I-H2: the zero locus of a nonzero one-variable polynomial is μ₁-null -/

/-- Zero set of a nonzero one-variable polynomial is μ₁-null (finitely many
roots in the field + singleton-null). -/
theorem null_zeroLocus_one_var (f : Polynomial ℚ_[p]) (hf : f ≠ 0) :
    μ₁ p {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0} = 0 := by
  -- the zero set is the coercion-preimage of the root set of f in ℚ_p
  have hpre : {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0}
      = ((↑) : ℤ_[p] → ℚ_[p]) ⁻¹' {y : ℚ_[p] | f.IsRoot y} := rfl
  -- finitely many roots over the field, pulled back along the injective coercion
  have hfin : {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0}.Finite := by
    rw [hpre]
    exact (Polynomial.finite_setOf_isRoot hf).preimage
      (Set.injOn_of_injective Subtype.coe_injective)
  -- a countable union of null singletons (I-H1) is null
  calc μ₁ p {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0}
      = μ₁ p (⋃ x ∈ {x : ℤ_[p] | f.eval ((x : ℤ_[p]) : ℚ_[p]) = 0}, {x}) := by
        rw [Set.biUnion_of_singleton]
    _ = 0 := (measure_biUnion_null_iff hfin.countable).mpr fun x _ => μ₁_singleton p x

/-! ## Unit I-H3b: zero-locus measurability for an `MvPolynomial` evaluation on `Coeff` -/

/-- I-H3b, continuity half: the evaluation map `Coeff p m → ℚ_[p]`,
`a ↦ P((a 0 : ℚ_[p]), …, (a (m-1) : ℚ_[p]))` with the explicit per-slot
ℤ_p→ℚ_p cast (a `Subtype.val`, continuous for the induced topology), is
continuous. -/
theorem continuous_mvPolynomial_aeval_cast (m : ℕ) (P : MvPolynomial (Fin m) ℚ_[p]) :
    Continuous fun a : Coeff p m =>
      MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P := by
  have hcast : Continuous fun a : Coeff p m => fun i : Fin m => ((a i : ℤ_[p]) : ℚ_[p]) :=
    continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  simpa [Function.comp_def, MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.continuous_eval P).comp hcast

/-- **I-H3b (zero-locus measurability)**: the zero locus on `Coeff p m` of an
`MvPolynomial` evaluated through the explicit ℤ_p→ℚ_p cast is measurable —
it is the preimage of the closed `{0}` under the continuous evaluation map,
hence closed, hence Borel (I-A2 instance layer). The set expression matches
BP_I §1.8's `null_zeroLocus` verbatim; consumed by the Tonelli slicing step
I-H3c1 and the exceptional-locus lemma I-H3c2. -/
theorem measurableSet_zeroLocus (m : ℕ) (P : MvPolynomial (Fin m) ℚ_[p]) :
    MeasurableSet {a : Coeff p m |
      MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0} := by
  have hclosed : IsClosed {a : Coeff p m |
      MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0} :=
    isClosed_singleton.preimage (continuous_mvPolynomial_aeval_cast p m P)
  exact hclosed.measurableSet

/-! ## Unit I-H4a: the generic monic polynomial and `discrPoly` -/

/-- The lower-order part of `polyOfCoeffs` has degree `< n` (all `n`,
including the empty sum at `n = 0`; file-local re-proof — the MovesX and
Semantic copies are `private`). -/
private lemma polyOfCoeffs_lower_degree_lt' {R : Type} [CommRing R] {n : ℕ}
    (a : Fin n → R) :
    (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
  intro i _
  calc (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      ≤ ((i : ℕ) : WithBot ℕ) := Polynomial.degree_C_mul_X_pow_le _ _
    _ < (n : WithBot ℕ) := by exact_mod_cast i.2

/-- The generic monic polynomial `Xⁿ + Σᵢ (var i)·Xⁱ` over the
coefficient-variable ring `MvPolynomial (Fin n) ℚ_[p]`: `polyOfCoeffs`
applied to the tuple of variables (REUSE: `MovesX.polyOfCoeffs` — dedup
rule: no parallel poly-builder). -/
noncomputable def genericMonic (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) ℚ_[p]) :=
  MovesX.polyOfCoeffs (MvPolynomial (Fin n) ℚ_[p]) n MvPolynomial.X

/-- I-H4a: the generic polynomial is monic (all `n`; at `n = 0` it is `1`). -/
theorem genericMonic_monic (n : ℕ) : (genericMonic p n).Monic := by
  unfold genericMonic MovesX.polyOfCoeffs
  exact Polynomial.monic_X_pow_add (polyOfCoeffs_lower_degree_lt' _)

/-- I-H4a: the generic polynomial has `natDegree = n`. -/
theorem genericMonic_natDegree (n : ℕ) : (genericMonic p n).natDegree = n := by
  unfold genericMonic MovesX.polyOfCoeffs
  have hlt : (∑ i : Fin n, Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin n) ℚ_[p])
        * Polynomial.X ^ (i : ℕ)).degree
      < (Polynomial.X ^ n : Polynomial (MvPolynomial (Fin n) ℚ_[p])).degree := by
    rw [Polynomial.degree_X_pow]; exact polyOfCoeffs_lower_degree_lt' _
  rw [Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_left_of_degree_lt hlt),
    Polynomial.natDegree_X_pow]

/-- I-H4a (coefficient-index bookkeeping): the lower coefficients of the
generic polynomial are exactly the variables, `coeff i = Xᵢ` for `i : Fin n`
(the I-H4b-facing extraction law; file-local mirror of XF7's `private`
`polyOfCoeffs_coeff`). -/
theorem genericMonic_coeff (n : ℕ) (i : Fin n) :
    (genericMonic p n).coeff (i : ℕ) = MvPolynomial.X i := by
  unfold genericMonic MovesX.polyOfCoeffs
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ (i : ℕ) = n), zero_add,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hji (Fin.ext h.symm)), mul_zero]
  · intro hcontra; exact absurd (Finset.mem_univ i) hcontra

/-- The generic discriminant: discr(polyOfCoeffs) as an MvPolynomial in the
coefficients, with the evaluation law (naturality of resultants under ring
maps; mathlib `Polynomial.discr` = Resultant/Basic.lean:930). -/
noncomputable def discrPoly (n : ℕ) : MvPolynomial (Fin n) ℚ_[p] :=
  (genericMonic p n).discr

/-! ## Unit I-H4b: generic-polynomial evaluation equals `mPoly`

PROVENANCE NOTE (I-H4b prover): the division rules point at
`lean/blueprints/undefined.md` for this unit's verbatim statement; that file
does not exist (orchestration variable bug), and BP_I §1.8 displays no
verbatim statement for this row. The statement below was therefore DESIGNED
by this prover from the BP_I §2 Wave-H row ("generic-polynomial evaluation
equals `mPoly` — explicit coefficient casts and `Fin` index transport", Df
§3.1 SEP(i)), keyed so that its evaluation hom is LITERALLY the
`MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p]))` that I-H4c's
verbatim `discr_mPoly_eq_eval` consumes — division lead must ratify before
I-H4c consumes it. -/

/-- **I-H4b: generic-polynomial evaluation equals `mPoly`** (Df §3.1 SEP(i)).
Specializing the generic monic polynomial (I-H4a) at a coefficient tuple
`a : Coeff p n` — mapping its coefficients along the ring hom underlying
`MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p]))`, the SAME evaluation
hom as in I-H4c's `discr_mPoly_eq_eval` — recovers `mPoly p n a` (I-E1).
The explicit coefficient cast is definitional
(`algebraMap ℤ_[p] ℚ_[p] = ↑·`), and both lower-order sums are indexed by
the same `Fin n`, so the index transport is the identity. -/
theorem genericMonic_eval_eq_mPoly (n : ℕ) (a : Coeff p n) :
    (genericMonic p n).map
        (MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p]))).toRingHom
      = mPoly p n a := by
  simp only [genericMonic, mPoly, MovesX.polyOfCoeffs, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

/-! ## Unit I-H3a: the `Fin (m+1)` coordinate equivalence + product-measure transport

The explicit coordinate equivalence (`coeffSuccEquiv`, peeling off coordinate
0, matching the `MvPolynomial.finSuccEquiv` variable split used downstream)
and its product-measure transport (Df App A induction plumbing). The BP row
displays no verbatim statement (definition-design row); the public transport
theorem is proved from the `Measure.pi` map API
(`measurePreserving_piFinSuccAbove` — a BP §3 search hint that verified in
the pinned tree). Rests on I-B2 (`μHaar` as `Measure.pi` of `μ₁`). -/

/-- I-H3a (definition half): the explicit coordinate equivalence
`Coeff p (m+1) ≃ᵐ ℤ_[p] × Coeff p m`, peeling off coordinate `0`:
`a ↦ (a 0, fun j => a j.succ)` (see `coeffSuccEquiv_apply`), with inverse
`Fin.cons` (see `coeffSuccEquiv_symm_apply`). -/
noncomputable def coeffSuccEquiv (m : ℕ) : Coeff p (m + 1) ≃ᵐ ℤ_[p] × Coeff p m :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℤ_[p]) 0

/-- The equivalence made explicit, forward direction. -/
theorem coeffSuccEquiv_apply (m : ℕ) (a : Coeff p (m + 1)) :
    coeffSuccEquiv p m a = (a 0, fun j => a j.succ) := by
  simp [coeffSuccEquiv]
  rfl

/-- The equivalence made explicit, inverse direction: `Fin.cons`. -/
theorem coeffSuccEquiv_symm_apply (m : ℕ) (x : ℤ_[p]) (b : Coeff p m) :
    (coeffSuccEquiv p m).symm (x, b) = Fin.cons x b := by
  simp [coeffSuccEquiv]
  rfl

/-- I-H3a (transport half, the public transport theorem): `coeffSuccEquiv`
carries `μHaar p (m+1)` to the product measure `μ₁ ⊗ μHaar p m`. Both sides
are `Measure.pi` of copies of `μ₁` (I-B2), so mathlib's
`measurePreserving_piFinSuccAbove` applies definitionally. -/
theorem measurePreserving_coeffSuccEquiv (m : ℕ) :
    MeasurePreserving (coeffSuccEquiv p m) (μHaar p (m + 1))
      ((μ₁ p).prod (μHaar p m)) :=
  measurePreserving_piFinSuccAbove (fun _ => μ₁ p) 0

/-- Transport in map form. -/
theorem μHaar_succ_map (m : ℕ) :
    Measure.map (coeffSuccEquiv p m) (μHaar p (m + 1)) = (μ₁ p).prod (μHaar p m) :=
  (measurePreserving_coeffSuccEquiv p m).map_eq

/-- Transport in set form, for ARBITRARY sets (no measurability hypothesis:
a `MeasurableEquiv` evaluates `map` by preimage on every set). This is the
I-H3c1-facing workhorse. -/
theorem μHaar_succ_transport (m : ℕ) (S : Set (Coeff p (m + 1))) :
    μHaar p (m + 1) S = ((μ₁ p).prod (μHaar p m)) (coeffSuccEquiv p m '' S) := by
  rw [← μHaar_succ_map p m, MeasurableEquiv.map_apply,
    Set.preimage_image_eq S (coeffSuccEquiv p m).injective]

/-! ## Unit I-H5: SEP(ii) — separable ↔ discriminant ≠ 0 -/

section SepIffDiscr

variable (n : ℕ)

/-- SEP(ii): monic, positive degree, over the field ℚ_p: separable ↔ discr ≠ 0
(via `isUnit_resultant_iff_isCoprime` / `resultant_eq_zero_iff`). -/
theorem sep_iff_discr_ne_zero (hn : 1 ≤ n) (a : Coeff p n) :
    Sep p n a ↔ (mPoly p n a).discr ≠ 0 := by
  have hmon : (mPoly p n a).Monic := mPoly_monic p n a
  have hnd : 0 < (mPoly p n a).natDegree := by
    rw [mPoly_natDegree]; exact hn
  have hdpos : 0 < (mPoly p n a).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hnd
  -- the derivative's natDegree is the default resultant size n − 1 (char 0)
  have hd' : (Polynomial.derivative (mPoly p n a)).natDegree
      = (mPoly p n a).natDegree - 1 :=
    Polynomial.natDegree_derivative _
  -- the discr-vs-resultant unwind
  have hres := Polynomial.resultant_deriv hdpos
  -- the sign is a unit of the field
  have hsgn : ((-1 : ℚ_[p]))
      ^ ((mPoly p n a).natDegree * ((mPoly p n a).natDegree - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  calc Sep p n a
      ↔ IsCoprime (mPoly p n a) (Polynomial.derivative (mPoly p n a)) :=
        Polynomial.separable_def _
    _ ↔ IsUnit ((mPoly p n a).resultant (Polynomial.derivative (mPoly p n a))) :=
        (Polynomial.isUnit_resultant_iff_isCoprime hmon).symm
    _ ↔ (mPoly p n a).discr ≠ 0 := by
        rw [isUnit_iff_ne_zero, hd', hres, hmon.leadingCoeff, mul_one,
          mul_ne_zero_iff]
        exact and_iff_right hsgn

end SepIffDiscr

/-! ## Unit I-H3c2: the leading-coefficient exceptional locus

PROVENANCE NOTE (I-H3c2 prover): the division rules point at
`lean/blueprints/undefined.md` for this unit's verbatim statement; that file
does not exist (orchestration variable bug), and BP_I §1.8 displays verbatim
statements only for the outer Wave-H theorems. The statement below was
therefore DESIGNED by this prover from the BP_I §2 Wave-H row
(“expose a nonzero lower-dimensional coefficient polynomial controlling
identically-zero slices”, Df App A Lemma NULL) — division lead must ratify
before I-H3c3 consumes it. -/

/-- **I-H3c2 (Df App A Lemma NULL, exceptional-locus step).** Split a nonzero
`(m+1)`-variable polynomial `P` over ℚ_p into a one-variable polynomial in
`X 0` with `m`-variable coefficients (`MvPolynomial.finSuccEquiv`). The
witness `Q` is its leading coefficient: a NONZERO `m`-variable polynomial
such that every slice point `y` whose one-variable slice polynomial
`Polynomial.map (MvPolynomial.eval y) (finSuccEquiv ℚ_[p] m P)` is
IDENTICALLY zero lies in the zero locus of `Q`. Contrapositive, for I-H3c3:
off `Q`'s zero locus the slice polynomial is nonzero, so I-H2 applies to it;
mathlib's `MvPolynomial.eval_eq_eval_mv_eval'` identifies the slice
polynomial's values with `P`'s values at `Fin.cons x y`. -/
theorem exists_exceptional_coeffPoly (m : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℚ_[p]) (hP : P ≠ 0) :
    ∃ Q : MvPolynomial (Fin m) ℚ_[p], Q ≠ 0 ∧
      ∀ y : Fin m → ℚ_[p],
        Polynomial.map (MvPolynomial.eval y) (MvPolynomial.finSuccEquiv ℚ_[p] m P) = 0 →
          MvPolynomial.eval y Q = 0 := by
  set F : Polynomial (MvPolynomial (Fin m) ℚ_[p]) :=
    MvPolynomial.finSuccEquiv ℚ_[p] m P with hF
  -- `finSuccEquiv` is an algebra equivalence, so `F` inherits nonvanishing
  have hFne : F ≠ 0 := by
    intro h0
    apply hP
    have h1 := congrArg (MvPolynomial.finSuccEquiv ℚ_[p] m).symm (hF ▸ h0)
    simpa using h1
  refine ⟨F.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hFne, ?_⟩
  intro y h
  -- an identically-zero slice kills every coefficient, in particular the leading one
  have hc : (Polynomial.map (MvPolynomial.eval y) F).coeff F.natDegree = 0 := by
    rw [h, Polynomial.coeff_zero]
  rw [Polynomial.coeff_map] at hc
  exact hc

/-! ## Unit I-H3c1: the slicing lemma (Df App A Tonelli step)

PROVENANCE NOTE (I-H3c1 prover): the division rules point at
`lean/blueprints/undefined.md` for this unit's verbatim statement; that file
does not exist (orchestration variable bug), and BP_I §1.8 displays no
verbatim statement for this row (table-only). The statements below were
DESIGNED by this prover from the BP_I §2 Wave-H row ("slicing lemma: a
measurable set with almost-everywhere μ₁-null slices is product-null —
product-measure/Tonelli null-section theorem", Df App A Tonelli step:
μ_m(Z) = ∫ μ₁(Z_{y′}) dμ_{m−1}(y′) = 0), keyed to I-H3a's landed transport
shape `(μ₁ p).prod (μHaar p m)` (slice coordinate FIRST, base second) —
division lead must ratify before I-H3c3 consumes it. -/

/-- **I-H3c1 (slicing lemma, product core; Df App A Tonelli step).** A
measurable set of `ℤ_[p] × Coeff p m` whose μ₁-slices `{y | (y, b) ∈ S}` are
null at `μHaar p m`-almost every base point `b` is null for the product
measure `μ₁ ⊗ μHaar p m` — the product-measure/Tonelli null-section theorem
(mathlib `Measure.prod_apply_symm`; the s-finiteness it needs comes from the
probability-measure instances on `μ₁` and `μHaar`). The product carries
I-H3a's transport shape: slice coordinate first, base second. -/
theorem prod_null_of_ae_null_slices (m : ℕ) {S : Set (ℤ_[p] × Coeff p m)}
    (hS : MeasurableSet S)
    (hslice : ∀ᵐ b ∂ μHaar p m, μ₁ p {y : ℤ_[p] | (y, b) ∈ S} = 0) :
    ((μ₁ p).prod (μHaar p m)) S = 0 := by
  rw [Measure.prod_apply_symm hS]
  calc ∫⁻ b, μ₁ p ((fun y => (y, b)) ⁻¹' S) ∂ μHaar p m
      = ∫⁻ b, 0 ∂ μHaar p m :=
        lintegral_congr_ae (by filter_upwards [hslice] with b hb; exact hb)
    _ = 0 := lintegral_zero

/-- **I-H3c1 (slicing lemma, `Coeff p (m+1)` shape).** The same statement
transported along I-H3a: a measurable `S ⊆ Coeff p (m+1)` whose coordinate-0
slice `{y | Fin.cons y b ∈ S}` is μ₁-null for `μHaar p m`-almost every tail
`b` is `μHaar p (m+1)`-null. This is the assembly shape for the induction
step I-H3c3, whose slices are the `finSuccEquiv` slice polynomials' zero
sets at `Fin.cons` (I-H3c2). -/
theorem μHaar_succ_null_of_ae_null_slices (m : ℕ) {S : Set (Coeff p (m + 1))}
    (hS : MeasurableSet S)
    (hslice : ∀ᵐ b ∂ μHaar p m, μ₁ p {y : ℤ_[p] | Fin.cons y b ∈ S} = 0) :
    μHaar p (m + 1) S = 0 := by
  rw [μHaar_succ_transport p m S]
  refine prod_null_of_ae_null_slices p m ?_ ?_
  · rw [MeasurableEquiv.image_eq_preimage_symm]
    exact (coeffSuccEquiv p m).symm.measurable hS
  · filter_upwards [hslice] with b hb
    have hset : {y : ℤ_[p] | (y, b) ∈ coeffSuccEquiv p m '' S}
        = {y : ℤ_[p] | Fin.cons y b ∈ S} := by
      ext y
      simp only [Set.mem_setOf_eq, MeasurableEquiv.image_eq_preimage_symm,
        Set.mem_preimage, coeffSuccEquiv_symm_apply]
    rw [hset]; exact hb

/-! ## Unit I-H4c: `discr_mPoly_eq_eval` — discriminant naturality under ring maps

The BP §2 row's `resultant_map` search hint resolves to the VERIFIED mathlib
lemma `Polynomial.resultant_map_map` (Resultant/Basic.lean:140, determinant
naturality already packaged: Sylvester matrices at FIXED sizes `m n` commute
with `RingHom.mapMatrix`, and `det` commutes with ring maps). The kernel
below combines it with `Polynomial.resultant_deriv` (:973) on both sides of
the map: monicity keeps `natDegree` (so the Sylvester sizes agree and the
two `resultant_deriv` unwinds carry the SAME sign exponent), the leading
coefficients are `1`, and the common sign `(-1)^(d(d-1)/2)` cancels via
`(-1)^k · (-1)^k = 1` — no cancellativity assumption on the target ring.
The `natDegree = 0` corner (monic constant ⇒ the polynomial is `1`) is a
direct computation: both discriminants are `1`. -/

/-- **The I-H4c naturality kernel:** the discriminant of a MONIC polynomial
commutes with an arbitrary ring map into a nontrivial ring. -/
private lemma discr_map_of_monic {A B : Type*} [CommRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) {F : Polynomial A} (hF : F.Monic) :
    (F.map φ).discr = φ F.discr := by
  rcases Nat.eq_zero_or_pos F.natDegree with h0 | hdeg
  · -- natDegree = 0: a monic constant is 1; both discriminants are 1.
    have hF1 : F = 1 := (Polynomial.Monic.natDegree_eq_zero hF).mp h0
    rw [hF1, Polynomial.map_one, ← Polynomial.C_1 (R := B), Polynomial.discr_C,
      ← Polynomial.C_1 (R := A), Polynomial.discr_C, map_one]
  · have hFm : (F.map φ).Monic := hF.map φ
    have hnd : (F.map φ).natDegree = F.natDegree := hF.natDegree_map φ
    have hdegF : 0 < F.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
    have hdegFm : 0 < (F.map φ).degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, hnd]; exact hdeg
    -- the two resultant unwinds, at the SAME sizes and the SAME sign exponent
    have h1 := Polynomial.resultant_deriv hdegF
    have h2 := Polynomial.resultant_deriv hdegFm
    rw [hF.leadingCoeff, mul_one] at h1
    rw [hFm.leadingCoeff, mul_one, hnd, Polynomial.derivative_map,
      Polynomial.resultant_map_map, h1, map_mul, map_pow, map_neg, map_one] at h2
    -- h2 : (-1)^k * φ F.discr = (-1)^k * (F.map φ).discr; cancel the sign square
    set k := F.natDegree * (F.natDegree - 1) / 2 with hk
    have hsq : ((-1 : B) ^ k) * ((-1 : B) ^ k) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
    have h3 := congrArg (fun x => ((-1 : B) ^ k) * x) h2.symm
    simpa only [← mul_assoc, hsq, one_mul] using h3

/-- **I-H4c (`discr_mPoly_eq_eval`, verbatim BP_I §1.8): the evaluation law
for the generic discriminant** — the discriminant of `mPoly p n a` is the
evaluation of `discrPoly` at the coefficient tuple (naturality of
resultants/discriminants under ring maps). Route: I-H4b rewrites `mPoly` as
the map of the generic monic polynomial (I-H4a) along the coefficient
evaluation hom, and the kernel `discr_map_of_monic` commutes `discr` past
that map (`genericMonic_monic` supplies monicity). -/
theorem discr_mPoly_eq_eval (n : ℕ) (a : Coeff p n) :
    (mPoly p n a).discr
      = MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) (discrPoly p n) := by
  have h := discr_map_of_monic
      (MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p]))).toRingHom
      (genericMonic_monic p n)
  rw [genericMonic_eval_eq_mPoly p n a] at h
  simpa only [discrPoly, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

/-! ## Unit I-H6: SEP(iii) — the witness ∏ᵢ (X − pⁱ) forces `discrPoly ≠ 0` -/

section SepWitness

open Polynomial

variable (n : ℕ)

/-- The I-H6 separability witness `∏ᵢ (X − pⁱ)` over ℤ_[p] (BP_I §1.8
SEP(iii); Df §3.1): a monic degree-`n` polynomial with the `n` distinct
roots `p⁰, …, p^(n−1)`. -/
noncomputable def sepWitnessPoly : Polynomial ℤ_[p] :=
  ∏ i : Fin n, (X - C ((p : ℤ_[p]) ^ (i : ℕ)))

/-- The witness is monic (product of the monic linear factors `X − pⁱ`). -/
lemma sepWitnessPoly_monic : (sepWitnessPoly p n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The witness has `natDegree = n` (each of the `n` factors is linear). -/
lemma sepWitnessPoly_natDegree : (sepWitnessPoly p n).natDegree = n := by
  rw [sepWitnessPoly, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero _]
  simp only [natDegree_X_sub_C]
  simp

/-- The coefficient tuple of the witness — the point of `Coeff p n` at which
`discrPoly` will be evaluated. -/
noncomputable def sepWitnessCoeffs : Coeff p n :=
  fun i => (sepWitnessPoly p n).coeff i

/-- Reassembling the witness from its coefficient tuple: `polyOfCoeffs` at
`sepWitnessCoeffs` recovers `sepWitnessPoly` (monic of `natDegree = n`, so
`Monic.as_sum` gives exactly the `Xⁿ + Σ_{i<n} coeff i · Xⁱ` shape, and
`Finset.sum_range` transports the `range n` sum to the `Fin n` sum). -/
lemma polyOfCoeffs_sepWitnessCoeffs :
    MovesX.polyOfCoeffs ℤ_[p] n (sepWitnessCoeffs p n) = sepWitnessPoly p n := by
  conv_rhs => rw [(sepWitnessPoly_monic p n).as_sum, sepWitnessPoly_natDegree]
  rw [MovesX.polyOfCoeffs]
  congr 1
  rw [Finset.sum_range fun i => C ((sepWitnessPoly p n).coeff i) * X ^ i]
  rfl

/-- `mPoly` at the witness tuple is `∏ᵢ (X − pⁱ)` over ℚ_p (the ℤ_p→ℚ_p
coefficient map distributes over the product and fixes each `X − pⁱ`). -/
lemma mPoly_sepWitnessCoeffs :
    mPoly p n (sepWitnessCoeffs p n) =
      ∏ i : Fin n, (X - C ((p : ℚ_[p]) ^ (i : ℕ))) := by
  rw [mPoly, polyOfCoeffs_sepWitnessCoeffs, sepWitnessPoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  norm_num

/-- The witness is separable: its roots `pⁱ` are pairwise distinct
(`pⁱ = pʲ` in ℚ_p casts to `pⁱ = pʲ` in ℕ by char 0, whence `i = j` by
`Nat.pow_right_injective` at `2 ≤ p`), so `separable_prod_X_sub_C_iff`
applies. -/
lemma sep_sepWitnessCoeffs : Sep p n (sepWitnessCoeffs p n) := by
  rw [Sep, mPoly_sepWitnessCoeffs, separable_prod_X_sub_C_iff]
  intro i j hij
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcast : ((p ^ (i : ℕ) : ℕ) : ℚ_[p]) = ((p ^ (j : ℕ) : ℕ) : ℚ_[p]) := by
    push_cast; exact hij
  exact Fin.ext (Nat.pow_right_injective hp2 (Nat.cast_injective hcast))

/-- SEP(iii): the witness ∏ (X − pⁱ) has distinct roots ⇒ discrPoly ≠ 0. -/
theorem discrPoly_ne_zero (hn : 1 ≤ n) : discrPoly p n ≠ 0 := by
  intro h
  have hsep : Sep p n (sepWitnessCoeffs p n) := sep_sepWitnessCoeffs p n
  rw [sep_iff_discr_ne_zero p n hn] at hsep
  exact hsep (by rw [discr_mPoly_eq_eval, h, map_zero])

end SepWitness

/-! ## Unit I-H3c3: the induction step for multivariable zero loci

PROVENANCE NOTE (I-H3c3 prover): the division rules point at
`lean/blueprints/undefined.md` for this unit's verbatim statement; that file
does not exist (orchestration variable bug), and BP_I §1.8 displays no
verbatim statement for this row (table-only). The statement below was
DESIGNED by this prover from the BP_I §2 Wave-H row ("off the exceptional
locus apply I-H2 to each slice; on it apply the induction hypothesis;
assemble with I-H3c1", Df App A Lemma NULL): it is exactly the successor
step of BP_I §1.8's VERBATIM `null_zeroLocus` statement, with the
`m`-variable instance of that verbatim statement as the named induction
hypothesis `ih`, so that I-H3c4 is `induction m` plus this lemma (base case
direct). Division lead must ratify before I-H3c4 consumes it. -/

/-- **I-H3c3 (Df App A Lemma NULL, induction step).** If every nonzero
`m`-variable polynomial over ℚ_p has `μHaar p m`-null zero locus on
`Coeff p m` (the induction hypothesis `ih` — the `m`-variable instance of
BP_I §1.8's `null_zeroLocus`), then every nonzero `(m+1)`-variable
polynomial `P` has `μHaar p (m+1)`-null zero locus on `Coeff p (m+1)`.

Proof shape (Df App A): split off variable 0 (`MvPolynomial.finSuccEquiv`,
the variable split aligned with I-H3a's `coeffSuccEquiv`). I-H3c2
(`exists_exceptional_coeffPoly`) exposes a nonzero `m`-variable
coefficient polynomial `g` controlling the identically-zero slices; `ih g`
makes that exceptional locus null. Off it, the slice polynomial at a tail
`b` is a NONZERO one-variable polynomial whose value at `y : ℤ_[p]` is `P`'s
value at `Fin.cons y b` (`MvPolynomial.eval_eq_eval_mv_eval'`), so I-H2
(`null_zeroLocus_one_var`) nullifies each such slice; I-H3c1
(`μHaar_succ_null_of_ae_null_slices`, fed I-H3b's
`measurableSet_zeroLocus`) assembles the slices into product-nullity. -/
theorem null_zeroLocus_succ (m : ℕ)
    (ih : ∀ Q : MvPolynomial (Fin m) ℚ_[p], Q ≠ 0 →
      μHaar p m {a | MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) Q = 0} = 0)
    (P : MvPolynomial (Fin (m + 1)) ℚ_[p]) (hP : P ≠ 0) :
    μHaar p (m + 1)
      {a | MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0} = 0 := by
  -- I-H3c2: the exceptional coefficient polynomial `g`
  obtain ⟨g, hg, hcontrol⟩ := exists_exceptional_coeffPoly p m P hP
  -- I-H3c1 assembly, with I-H3b measurability
  refine μHaar_succ_null_of_ae_null_slices p m
    (measurableSet_zeroLocus p (m + 1) P) ?_
  -- ON the exceptional locus: the induction hypothesis makes it null …
  have hE : μHaar p m {b : Coeff p m |
      MvPolynomial.aeval (fun i => ((b i : ℤ_[p]) : ℚ_[p])) g = 0} = 0 := ih g hg
  -- … so almost every tail `b` lies OFF it
  filter_upwards [compl_mem_ae_iff.mpr hE] with b hb
  set castb : Fin m → ℚ_[p] := fun i => ((b i : ℤ_[p]) : ℚ_[p]) with hcastb
  -- the slice polynomial at `b`
  set fb : Polynomial ℚ_[p] :=
    Polynomial.map (MvPolynomial.eval castb) (MvPolynomial.finSuccEquiv ℚ_[p] m P)
    with hfb
  -- OFF the exceptional locus the slice polynomial is nonzero (I-H3c2, contrapositive)
  have hfb_ne : fb ≠ 0 := by
    intro h0
    apply hb
    change MvPolynomial.aeval castb g = 0
    rw [MvPolynomial.aeval_eq_eval]
    exact hcontrol castb h0
  -- the slice IS the slice polynomial's zero set (`eval_eq_eval_mv_eval'`)
  have hset : {y : ℤ_[p] | Fin.cons y b ∈
        {a : Coeff p (m + 1) |
          MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0}}
      = {y : ℤ_[p] | fb.eval ((y : ℤ_[p]) : ℚ_[p]) = 0} := by
    ext y
    have hcons : (fun i => (((Fin.cons y b : Coeff p (m + 1)) i : ℤ_[p]) : ℚ_[p]))
        = Fin.cons ((y : ℤ_[p]) : ℚ_[p]) castb := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [hcastb]
    simp only [Set.mem_setOf_eq, MvPolynomial.aeval_eq_eval, hcons, hfb,
      MvPolynomial.eval_eq_eval_mv_eval']
  -- OFF the locus: I-H2 on each slice
  exact hset ▸ null_zeroLocus_one_var p fb hfb_ne

/-! ## Unit I-H7: `ns_null_proved_pos` — the positive-degree (NS-NULL) discharge

Statement BP_I §1.8 VERBATIM. Proof per the BP §2 Wave-H row: identify the
nonseparable locus with the zero locus of the generic discriminant — SEP(ii)
(I-H5 `sep_iff_discr_ne_zero`) composed with the evaluation law (I-H4c
`discr_mPoly_eq_eval`) — and kill it by Lemma NULL at the nonzero generic
discriminant (I-H6 `discrPoly_ne_zero`).

WIRING NOTE (I-H7 prover): at landing time I-H3c4's `null_zeroLocus` had not
yet landed in this file (that unit runs in PARALLEL with this one per the
division schedule), so Lemma NULL enters as an inline `have hnull` — the
induction wrapper over the LANDED induction step I-H3c3
(`null_zeroLocus_succ`), base case `m = 0` direct (a nonzero 0-variable
polynomial is a nonzero constant, `MvPolynomial.C_surjective`; empty locus).
Once I-H3c4 lands, `hnull` is a golf seam: replace `hnull n` by
`null_zeroLocus p n` and delete the wrapper — no statement change. -/

section NsNullPos

variable (n : ℕ)

/-- Positive-degree discriminant proof. -/
theorem ns_null_proved_pos (hn : 1 ≤ n) :
    μHaar p n {a | ¬ Sep p n a} = 0 := by
  -- Lemma NULL (Df App A), inline: induction over I-H3c3's `null_zeroLocus_succ`
  have hnull : ∀ (m : ℕ) (P : MvPolynomial (Fin m) ℚ_[p]), P ≠ 0 →
      μHaar p m {a | MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) P = 0} = 0 := by
    intro m
    induction m with
    | zero =>
      -- base: a nonzero 0-variable polynomial is a nonzero constant; empty locus
      intro P hP
      obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) P
      have hc : c ≠ 0 := fun h => hP (by rw [h, map_zero])
      have hempty : {a : Coeff p 0 |
          MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) (MvPolynomial.C c) = 0}
          = ∅ := by
        ext a
        simp [hc]
      rw [hempty]
      exact measure_empty
    | succ m ih => exact null_zeroLocus_succ p m ih
  -- the nonseparable locus IS the discriminant zero locus (I-H5 + I-H4c)
  have hset : {a : Coeff p n | ¬ Sep p n a}
      = {a : Coeff p n |
          MvPolynomial.aeval (fun i => ((a i : ℤ_[p]) : ℚ_[p])) (discrPoly p n) = 0} := by
    ext a
    simp only [Set.mem_setOf_eq, sep_iff_discr_ne_zero p n hn a, not_ne_iff,
      discr_mPoly_eq_eval p n a]
  rw [hset]
  -- Lemma NULL at the nonzero generic discriminant (I-H6)
  exact hnull n (discrPoly p n) (discrPoly_ne_zero p n hn)

end NsNullPos

end LeanUrat.Scaffold
