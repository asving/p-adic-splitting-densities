/-
BP_I §1.7 — Base cases (`Base.lean`).
Unit I-G1a: `Unique (Coeff p 0)` + `μHaar_zero_eq_dirac` + `sep_zero`,
verbatim per BP_I §1.7 (BASE-0, the n = 0 Dirac floor, V17-finding-1
honest): one-point probability space; `mPoly = 1` (empty lower sum) and
`Polynomial.separable_one`. Deps: I-B2 (`μHaar` from Haar.lean), I-E1
(`mPoly`, `Sep` from Semantic.lean).
Unit I-G1b: `type_zero` + `strictVerdicts_zero` + `decidedCount_zero` +
`undecMass_zero`, verbatim per BP_I §1.7 (Df §6.2 BASE-0): TYPE-OF-ISTYPE
plus I-D5 (`isType_zero_iff`) pin the type of the unique point; the unique
level-0 class is then strictly decided with verdict `typeEmpty` (I-E3
spec). Deps: I-D5, I-E3, I-G1a. Display adjustment (same sanctioned
convention as the I-G4 note below): the §1.7 display `.undecMass p 0 0`
reads `.undecMass 0` here.
Unit I-G2: `sep_one`, verbatim per BP_I §1.7 (brief Thm BASE-1(a)): every
monic linear is separable — mPoly = X + C a₀, derivative 1, `IsCoprime`
trivial (the `Polynomial.separable_X_add_C` shape). Deps: I-E1 (`mPoly`,
`Sep` from Semantic.lean).
Unit I-G3: `structure LinRow` — the named **(LIN)** row (monic linear ⇒
type {(1,1)}; Movement-III discharge, consumed ONLY by the n = 1 instance)
+ `base1_decided` — StrictDecided at every `(N, x)` including N = 0.
Verbatim per BP_I §1.7 (Df §6.1 BASE-1(b)(d)). Deps: I-E2a (`TypeData`),
I-E3 (`strictVerdicts`/`strictVerdicts_spec`), I-G2 (`sep_one`).
Unit I-G4: `base1_counts` (= p^N: all classes decided by I-G3, card via
I-A3 `card_level`) + `base1_undec` (= 0: undecSet = ∅), verbatim per BP_I
§1.7 (Df §6.1 BASE-1(d)). Deps: I-A3, I-G3. Display adjustment (same
sanctioned convention as Semantic.lean's §1.5 consumption sites):
`undecMass` carries `{p n}` implicit (Decided.lean, §1.3-display fidelity),
so the §1.7 display `.undecMass p 1 N` reads `.undecMass N` here.
Unit I-G5: `base1_alpha` + `base1_alpha_eq_ratFunc_one` + `base1_sumR` —
the n = 1 root instance, SEMANTIC clauses ONLY, verbatim per BP_I §1.7
(Df §6.1 BASE-1(c)(e)(f)): locus = univ, α = 1 = R(p) with R := 1, sum over
the singleton menu Σ₁. The ALGORITHMIC half (one-state classifier, the 1×1
solve, count faithfulness) is BASE-1(f)'s fence — classifier-side, NOT
claimed here (V17 finding 2; the Movement-III/O-layer seam). Deps: I-E6a
(`alpha`/`alphaR`), I-G4, I-D4 (`isType_one_iff`).
Unit I-G1c: `alpha_zero` + `alphaR_zero` + `alpha_bracket_zero`, verbatim
per BP_I §1.7 (Df §6.2 BASE-0): locus is univ; probability normalization;
rewrite I-G1b. Deps: I-E6a, I-G1a (`sep_zero` above), I-G1b (the canonical
`type_zero`/`decidedCount_zero`/`undecMass_zero` block above, which landed
concurrently; this unit's transcribed prerequisite copies were removed at
the collision — each declaration is made once). Display adjustment (same
sanctioned convention as the I-G4 note above): `undecMass` carries `{p n}`
implicit, so the §1.7 displays `.undecMass p 0 0` read `.undecMass 0` here.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space
import LeanUrat.Scaffold.MeasureFloor.Haar
import LeanUrat.Scaffold.MeasureFloor.Semantic

namespace LeanUrat.Scaffold

variable (p : ℕ) [Fact p.Prime]

/-! ## Unit I-G1a: BASE-0 (brief Thm BASE-0; the n = 0 Dirac floor) -/

/-- BASE-0: the degree-0 coefficient space is one point (the empty tuple) —
mathlib's `Pi.uniqueOfIsEmpty` over `Fin 0`, re-declared as the unit's named
deliverable via `inferInstance` (definitionally THE existing instance, so no
diamond). -/
instance : Unique (Coeff p 0) := inferInstance

/-- BASE-0: at n = 0 the Haar measure is the Dirac mass at the unique point
(the empty product measure, mathlib `Measure.pi_of_empty`; the V17-finding-1
honest floor — `μHaar_singleton` is FALSE here, hence its displayed n ≥ 1). -/
theorem μHaar_zero_eq_dirac : μHaar p 0 = MeasureTheory.Measure.dirac default := by
  rw [μHaar]
  exact MeasureTheory.Measure.pi_of_empty _ default

/-- BASE-0: the unique degree-0 tuple is separable — `mPoly = 1` (the empty
product; the lower sum is empty), and `Polynomial.separable_one`. -/
theorem sep_zero (a : Coeff p 0) : Sep p 0 a := by
  show (mPoly p 0 a).Separable
  have h1 : mPoly p 0 a = 1 := by
    simp [mPoly, MovesX.polyOfCoeffs]
  rw [h1]
  exact Polynomial.separable_one

/-! ## Unit I-G1b: BASE-0 — the unique level-0 class is strictly decided
(TYPE-OF-ISTYPE + I-D5 `isType_zero_iff`; Df §6.2 BASE-0).

(Wave-G merge dedup, executed at the I-G1b landing: the I-G1c prover's
transcribed I-G1b prerequisite copies — same BP-verbatim statements — stood
below, before the I-G1c section; merged HERE into the one canonical block,
adopting their all-points helpers `typeOf_eq_empty`/`verdict_eq_some_empty`,
which I-G1c consumes.) -/

/-- Every degree-0 tuple has type `typeEmpty` — TYPE-OF-ISTYPE at the
separable (by `sep_zero`: every) point, read through I-D5
(`isType_zero_iff`). The all-points form of `type_zero`. -/
private lemma typeOf_eq_empty (TD : TypeData p 0) (a : Coeff p 0) :
    TD.typeOf a = typeEmpty :=
  (isType_zero_iff _).mp (TD.typeOf_isType a (sep_zero p a))

/-- Every level-N class at n = 0 is strictly decided with verdict
`typeEmpty`: every lift is separable (`sep_zero`) of type `typeEmpty`
(`typeOf_eq_empty`), so the strict predicate (5) holds outright and the
I-E3 spec reads the verdict back. -/
private lemma verdict_eq_some_empty (TD : TypeData p 0) (N : ℕ)
    (x : Level p 0 N) :
    (TD.strictVerdicts p 0).verdict N x = some typeEmpty :=
  (TD.strictVerdicts_spec p 0 N x typeEmpty).mpr
    fun a _ => ⟨sep_zero p a, typeOf_eq_empty p TD a⟩

/-- I-G1b (BASE-0(a)): the type at the unique degree-0 point is the empty
type. -/
theorem type_zero (TD : TypeData p 0) : TD.typeOf default = typeEmpty :=
  typeOf_eq_empty p TD default

/-- I-G1b: the unique level-0 class is STRICTLY decided with verdict
`typeEmpty` (the level-0 case of `verdict_eq_some_empty`). -/
theorem strictVerdicts_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).verdict 0 default = some typeEmpty :=
  verdict_eq_some_empty p TD 0 default

/-- I-G1b: exactly ONE decided class at level 0 — the class space
`Level p 0 0` is a one-point space, and its sole class carries the verdict
(`verdict_eq_some_empty`). -/
theorem decidedCount_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).decidedCount typeEmpty 0 = 1 := by
  haveI : Unique {x : Level p 0 0 //
      (TD.strictVerdicts p 0).verdict 0 x = some typeEmpty} :=
    { default := ⟨default, verdict_eq_some_empty p TD 0 default⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  show Nat.card {x : Level p 0 0 //
      (TD.strictVerdicts p 0).verdict 0 x = some typeEmpty} = 1
  exact Nat.card_unique

/-- I-G1b: no undecided mass at level 0 — every class is decided
(`verdict_eq_some_empty`), so U_0 is empty. (§1.7 display
`.undecMass p 0 0`; reads `.undecMass 0` per the header note.) -/
theorem undecMass_zero (TD : TypeData p 0) :
    (TD.strictVerdicts p 0).undecMass 0 = 0 := by
  have hempty : (TD.strictVerdicts p 0).undecSet 0 = ∅ := by
    ext a
    simp [LevelVerdicts.undecSet, verdict_eq_some_empty p TD 0]
  show μHaar p 0 ((TD.strictVerdicts p 0).undecSet 0) = 0
  rw [hempty]
  exact MeasureTheory.measure_empty

/-! ## Unit I-G2: BASE-1(a) -/

/-- The `n = 1` polynomial in closed form: `mPoly p 1 a = X + C a₀` (image of
`a 0` under the coefficient map ℤ_p → ℚ_p). -/
theorem mPoly_one (a : Coeff p 1) :
    mPoly p 1 a = Polynomial.X + Polynomial.C ((algebraMap ℤ_[p] ℚ_[p]) (a 0)) := by
  simp [mPoly, MovesX.polyOfCoeffs, Polynomial.map_add]

/-- I-G2 (brief Thm BASE-1(a)): every monic linear is separable — mPoly =
`X + C a₀`, derivative `1`, `IsCoprime` trivial (`Polynomial.separable_X_add_C`
shape). -/
theorem sep_one (a : Coeff p 1) : Sep p 1 a := by
  show (mPoly p 1 a).Separable
  rw [mPoly_one]
  exact Polynomial.separable_X_add_C _

/-! ## Unit I-G3: the (LIN) row + the n = 1 strict decision at every level -/

/-- **(LIN) — the n = 1 normalization row**: monic linear ⇒ type {(1,1)}
(brief BASE-1(b): K_f ≅ ℚ_p, e = f = 1). Movement-III discharge; consumed
ONLY by the n = 1 instance below. -/
structure LinRow (TD : TypeData p 1) : Prop where
  linear_type : ∀ a, TD.typeOf a = ⟨{(1, 1)}⟩

/-- I-G3 (brief BASE-1(d), semantic clause): given (LIN), every class is
STRICTLY decided at EVERY level — including N = 0 — with verdict {(1,1)}:
every lift is separable (I-G2 `sep_one`) and of type {(1,1)} ((LIN)), so the
strict predicate (5) holds outright and the I-E3 spec reads the verdict back. -/
theorem base1_decided (TD) (hlin : LinRow p TD) (N x) :
    (TD.strictVerdicts p 1).verdict N x = some ⟨{(1, 1)}⟩ := by
  rw [TD.strictVerdicts_spec p 1]
  intro a _ha
  exact ⟨sep_one p a, hlin.linear_type a⟩

/-! ## Unit I-G4: the n = 1 counts — decided = p^N (I-A3), undec = 0 -/

/-- I-G4 count half (Df §6.1 BASE-1(d)): ALL classes are decided (I-G3), so
the decided count is the full level-N card p^(1·N) = p^N (I-A3 `card_level`). -/
theorem base1_counts (TD) (hlin : LinRow p TD) (N) :
    (TD.strictVerdicts p 1).decidedCount ⟨{(1, 1)}⟩ N = p ^ N := by
  have hall : ∀ x : Level p 1 N,
      (TD.strictVerdicts p 1).verdict N x = some ⟨{(1, 1)}⟩ :=
    base1_decided p TD hlin N
  calc (TD.strictVerdicts p 1).decidedCount ⟨{(1, 1)}⟩ N
      = Nat.card {x : Level p 1 N //
          (TD.strictVerdicts p 1).verdict N x = some ⟨{(1, 1)}⟩} := rfl
    _ = Nat.card (Level p 1 N) := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    _ = p ^ (1 * N) := card_level p 1 N
    _ = p ^ N := by rw [one_mul]

/-- I-G4 undecided half (Df §6.1 BASE-1(d)): every class is decided (I-G3),
so the undecided set is empty and the undecided mass vanishes at every level. -/
theorem base1_undec (TD) (hlin : LinRow p TD) (N) :
    (TD.strictVerdicts p 1).undecMass N = 0 := by
  have hempty : (TD.strictVerdicts p 1).undecSet N = ∅ := by
    ext a
    simp [LevelVerdicts.undecSet, base1_decided p TD hlin N]
  show μHaar p 1 ((TD.strictVerdicts p 1).undecSet N) = 0
  rw [hempty]
  exact MeasureTheory.measure_empty

/-! ## Unit I-G5: the n = 1 root instance, SEMANTIC clauses
(Df §6.1 BASE-1(c)(e)(f)) -/

/-- BASE-1(c): the (1,1)-locus is EVERYTHING — `sep_one` + (LIN) — so
α = μHaar(univ) = 1. -/
theorem base1_alpha (TD) (hlin : LinRow p TD) :
    TD.alphaR p 1 ⟨{(1, 1)}⟩ = 1 := by
  have hloc : TD.locus p 1 ⟨{(1, 1)}⟩ = Set.univ := by
    ext a
    simp only [TypeData.locus, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨sep_one p a, hlin.linear_type a⟩
  simp [TypeData.alphaR, TypeData.alpha, hloc]

/-- BASE-1(e): α explicitly identified with the numerator/denominator
evaluation of `1 : RatFunc ℚ` at p (the R := 1 tie of the transfer seam). -/
theorem base1_alpha_eq_ratFunc_one (TD) (hlin : LinRow p TD) :
    TD.alphaR p 1 ⟨{(1, 1)}⟩ =
      (RatFunc.num (1 : RatFunc ℚ)).eval (p : ℚ) /
        (RatFunc.denom (1 : RatFunc ℚ)).eval (p : ℚ) := by
  rw [base1_alpha p TD hlin]
  simp [RatFunc.num_one, RatFunc.denom_one]

set_option linter.unusedVariables false in
/-- BASE-1(f), SEMANTIC side: the sum of R := 1 over the singleton menu
Σ₁ = {(1,1)} (I-D4 `isType_one_iff`) is 1. (Linter silenced: the constant
summand leaves the §1.7-verbatim binder `τ` unreferenced.) -/
theorem base1_sumR : (∑ τ ∈ typesFinset 1, (1 : RatFunc ℚ)) = 1 := by
  have h : typesFinset 1 = {(⟨{(1, 1)}⟩ : FactorizationType)} := by
    ext σ
    rw [mem_typesFinset, Finset.mem_singleton, isType_one_iff]
  rw [h, Finset.sum_singleton]

/-! (dedup, wave-G merge at the I-G1b landing: the I-G1c prover's transcribed
I-G1b prerequisites — same BP-verbatim `type_zero`/`strictVerdicts_zero`/
`decidedCount_zero`/`undecMass_zero` statements as the canonical Unit I-G1b
block declared above, via `typeOf_eq_empty`/`verdict_eq_some_empty` helpers —
stood here; removed, each declaration is made once. I-G1c consumes the
canonical copies; the two private helpers were hoisted INTO the canonical
I-G1b block above, where I-G1c reads them.) -/

/-! ## Unit I-G1c: `alpha_zero` + `alphaR_zero` + `alpha_bracket_zero`
(verbatim per BP_I §1.7; Df §6.2 BASE-0) -/

/-- BASE-0: the `typeEmpty` locus is EVERYTHING (`sep_zero` +
`typeOf_eq_empty`), so α is the total mass 1 of the I-B2 probability. -/
theorem alpha_zero (TD : TypeData p 0) :
    TD.alpha p 0 typeEmpty = 1 := by
  have hloc : TD.locus p 0 typeEmpty = Set.univ :=
    Set.eq_univ_of_forall fun a => ⟨sep_zero p a, typeOf_eq_empty p TD a⟩
  show μHaar p 0 (TD.locus p 0 typeEmpty) = 1
  rw [hloc]
  exact MeasureTheory.measure_univ

/-- BASE-0, real display: `toReal` of the finite value 1. -/
theorem alphaR_zero (TD : TypeData p 0) :
    TD.alphaR p 0 typeEmpty = 1 := by
  show (TD.alpha p 0 typeEmpty).toReal = 1
  rw [alpha_zero p TD]
  simp

/-- BASE-0 bracket, EXACT: rewrite I-G1b (`decidedCount_zero`,
`undecMass_zero`) and `alpha_zero` — the bracket reads 1 ≤ 1 ∧ 1 ≤ 1 + 0.
(§1.7 display `.undecMass p 0 0`; reads `.undecMass 0` per the header
note.) -/
theorem alpha_bracket_zero (TD : TypeData p 0) :
    ((TD.strictVerdicts p 0).decidedCount typeEmpty 0 : ENNReal) ≤
      TD.alpha p 0 typeEmpty ∧
    TD.alpha p 0 typeEmpty ≤
      ((TD.strictVerdicts p 0).decidedCount typeEmpty 0 : ENNReal) +
        (TD.strictVerdicts p 0).undecMass 0 := by
  rw [alpha_zero p TD, decidedCount_zero p TD, undecMass_zero p TD]
  simp

end LeanUrat.Scaffold
