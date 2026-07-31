/-
BP_I §1.5 — The semantic layer (MeasureFloor): MEAS-BRIDGE at the strict
convention.
Unit I-E1: `mPoly` + `Sep`, verbatim per BP_I §1.5 (REUSE:
`MovesX.polyOfCoeffs` VERBATIM — dedup rule: no parallel poly-builder),
plus the unit lemmas `mPoly_monic`, `mPoly_natDegree`.
Unit I-E2a: `structure TypeData` — the named TYPE-OF and TYPE-OF-ISTYPE
interface rows, verbatim per BP_I §1.5. STATEMENT-ONLY: no canonical
constructor is claimed in this movement (the Movement-III dictionary seam).
Unit I-E5: `isOpen_locus` (MEAS-BRIDGE(i)) + `measurableSet_locus`, by the
BP row's SECOND route — directly from (LOC) neighborhoods: around every
point of L_τ the locality row freezes `Sep` and `typeOf` on a whole
cylinder, open by I-A6 (`isClopen_cylinder`); open → measurable through the
I-A2 Borel layer. (The first route, union of cylinders via I-E4 + I-A6, is
untouched; I-E4's verdict machinery is NOT transcribed here.) Consumes the
I-E2b carrier `LocalityRow` and the I-E6a `locus` as landed by their owning
units below.
Unit I-E6a: `locus` (L_τ, brief Cor PART) + `alpha`/`alphaR` — THE SCAFFOLD
DENSITY (clause (0)'s α = μHaar of `TD.locus`), verbatim per BP_I §1.5;
consumes TYPE-OF only, no LOC/NS-NULL row.
Unit I-E3: `StrictDecided` def + at-most-one-τ lemma (`strictDecided_unique`)
+ `strictVerdicts : LevelVerdicts` + `strictVerdicts_spec`, verbatim per
BP_I §1.5 (Df §4.1 (5) + Lemma EX). Verdict by `Classical.choice` on the
≤-one-τ fact; nesting from I-A7 (`cylinder_succ_subset`); cylinder
nonemptiness from I-A8 (`toLevel_surjective`), no measure needed.
Unit I-E4: `iUnion_decided_eq_locus (LR : LocalityRow p n TD)` —
MEAS-BRIDGE(iv), EXACT in the strict convention (the leaf's headline),
verbatim per BP_I §1.5. ⊆: a lifts its own class; ⊇: `LR.locality` gives
the decided level.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space
import LeanUrat.Scaffold.MeasureFloor.Haar
import LeanUrat.Scaffold.MeasureFloor.Types
import LeanUrat.Scaffold.MeasureFloor.Decided
import LeanUrat.MovesX.Defs

namespace LeanUrat.Scaffold

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-! ## I-E1: `mPoly`, `Sep`, monicity, degree -/

/-- The monic polynomial of a coefficient tuple (REUSE: `MovesX.polyOfCoeffs`). -/
noncomputable def mPoly (a : Coeff p n) : Polynomial ℚ_[p] :=
  (MovesX.polyOfCoeffs ℤ_[p] n a).map (algebraMap ℤ_[p] ℚ_[p])

/-- Separability over the FIELD ℚ_p (mathlib `Polynomial.Separable` =
IsCoprime f f′; brief Lemma SEP(ii)'s working form). -/
def Sep (a : Coeff p n) : Prop := (mPoly p n a).Separable

/-- The lower-order part of `polyOfCoeffs` has degree `< n` (all `n`,
including the empty sum at `n = 0`; the XF7 bound, re-proved here because
the MovesX copy is `private`). -/
private lemma polyOfCoeffs_lower_degree_lt {R : Type} [CommRing R] {n : ℕ}
    (a : Fin n → R) :
    (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
  intro i _
  calc (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      ≤ ((i : ℕ) : WithBot ℕ) := Polynomial.degree_C_mul_X_pow_le _ _
    _ < (n : WithBot ℕ) := by exact_mod_cast i.2

/-- `polyOfCoeffs` is monic (all `n`; at `n = 0` it is `1`). -/
private lemma polyOfCoeffs_monic {R : Type} [CommRing R] {n : ℕ}
    (a : Fin n → R) : (MovesX.polyOfCoeffs R n a).Monic := by
  unfold MovesX.polyOfCoeffs
  exact Polynomial.monic_X_pow_add (polyOfCoeffs_lower_degree_lt a)

/-- `polyOfCoeffs` has `natDegree = n` over a nontrivial ring (all `n`). -/
private lemma polyOfCoeffs_natDegree {R : Type} [CommRing R] [Nontrivial R]
    {n : ℕ} (a : Fin n → R) : (MovesX.polyOfCoeffs R n a).natDegree = n := by
  unfold MovesX.polyOfCoeffs
  have hlt : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      < (Polynomial.X ^ n : Polynomial R).degree := by
    rw [Polynomial.degree_X_pow]; exact polyOfCoeffs_lower_degree_lt a
  rw [Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_left_of_degree_lt hlt),
    Polynomial.natDegree_X_pow]

/-- I-E1: `mPoly` is monic (map of monic is monic, `Polynomial.Monic.map`). -/
theorem mPoly_monic (a : Coeff p n) : (mPoly p n a).Monic :=
  (polyOfCoeffs_monic a).map (algebraMap ℤ_[p] ℚ_[p])

/-- I-E1: `mPoly` has `natDegree = n` (degree preserved under the map — via
monicity, so no injectivity argument is even needed). -/
theorem mPoly_natDegree (a : Coeff p n) : (mPoly p n a).natDegree = n := by
  rw [mPoly, Polynomial.Monic.natDegree_map (polyOfCoeffs_monic a)]
  exact polyOfCoeffs_natDegree a

/-! ## I-E2a: the `TypeData` interface rows (TYPE-OF, TYPE-OF-ISTYPE) -/

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

/-! ## Unit I-E2b: the LOC and NS-NULL hypothesis carriers (verbatim per
BP_I §1.5) — separate NAMED structure rows, never axioms, never discharged
by fiat. -/

/-- **(LOC)**, separated so only locality consumers carry it. Provenance:
brief import I-1 = M05 Lemma D, V2-upheld, WILD-VALID (holds at every prime,
including wild p ≤ n): the splitting type is constant on a small enough
cylinder around every separable point. Stated at bare ∃N (the 2v+1 modulus
is the RATE refinement, parked — I-E9). A named hypothesis row, never an
axiom; its Lean discharge is not claimed in this movement. -/
structure LocalityRow (TD : TypeData p n) : Prop where
  locality : ∀ a, Sep p n a →
    ∃ N, ∀ b ∈ cylinder p n N (toLevel p n N a),
      Sep p n b ∧ TD.typeOf b = TD.typeOf a

/-- **(NS-NULL)**, separated so normalization/drainage alone carry it.
Provenance: brief Appendix A / import I-3 null clause (Df App A): the
non-separable locus is `μHaar`-null. Wave H constructs this row for every
`n`; the stable consumer interface is not deleted or migrated. A named
hypothesis row, never an axiom. -/
structure NsNullRow (p n : ℕ) [Fact p.Prime] : Prop where
  ns_null : μHaar p n {a | ¬ Sep p n a} = 0

/-! ## Unit I-E6a: `locus` (L_τ) + `alpha`/`alphaR` — THE SCAFFOLD DENSITY

Verbatim per BP_I §1.5 (ROOT §1 (0)): α(τ) := μHaar of `TD.locus p n τ`.
Consumes TYPE-OF only — no LOC (`LocalityRow`) and no NS-NULL (`NsNullRow`)
row enters these defs. In the `TypeData` namespace with `p n` explicit so the
§1.5 dot-notation consumption sites (`TD.locus p n τ`, `TD.alpha p n τ`,
`TD.alphaR p n τ`) elaborate exactly as displayed in the blueprint. -/

namespace TypeData

variable (TD : TypeData p n)

/-- L_τ (brief Cor PART). -/
def locus (τ : FactorizationType) : Set (Coeff p n) :=
  {a | Sep p n a ∧ TD.typeOf a = τ}

/-- **THE SCAFFOLD DENSITY (clause (0)'s α).** -/
noncomputable def alpha (τ : FactorizationType) : ENNReal := μHaar p n (TD.locus p n τ)
noncomputable def alphaR (τ : FactorizationType) : ℝ := (TD.alpha p n τ).toReal

/-! ## Unit I-E3: the strict decided convention + the strict verdicts

`StrictDecided`/`strictVerdicts`/`strictVerdicts_spec` verbatim per BP_I §1.5,
in the `TypeData` namespace with `p n` explicit so the §1.5 dot-notation
consumption sites (`TD.StrictDecided p n N x τ`, `TD.strictVerdicts p n`)
elaborate exactly as displayed in the blueprint. -/

/-- The STRICT decided predicate (brief (5)): every lift separable of type τ. -/
def StrictDecided (N : ℕ) (x : Level p n N) (τ : FactorizationType) : Prop :=
  ∀ a ∈ cylinder p n N x, Sep p n a ∧ TD.typeOf a = τ

/-- The at-most-one-τ lemma (Df Lemma EX's uniqueness half): a class member —
cylinders are nonempty by I-A8 (`toLevel_surjective`), NO measure needed —
witnesses both verdicts, and `typeOf` is a function. -/
theorem strictDecided_unique {N : ℕ} {x : Level p n N} {τ τ' : FactorizationType}
    (h : TD.StrictDecided p n N x τ) (h' : TD.StrictDecided p n N x τ') :
    τ = τ' := by
  obtain ⟨a, ha⟩ := toLevel_surjective p n N x
  have hmem : a ∈ cylinder p n N x := ha
  exact (h a hmem).2.symm.trans (h' a hmem).2

/-- Persistence one level down the tower (the I-A7 refinement
`cylinder_succ_subset`): the level-(N+1) cylinder is a subset of the decided
level-N cylinder, so the strict verdict transports. -/
theorem strictDecided_succ {N : ℕ} {x : Level p n (N + 1)} {τ : FactorizationType}
    (h : TD.StrictDecided p n N (levelCast p n N x) τ) :
    TD.StrictDecided p n (N + 1) x τ :=
  fun a ha => h a (cylinder_succ_subset p n N x ha)

open Classical in
/-- The strict verdict assignment, packaged for the abstract layer (verdict by
choice on the ≤-one-τ fact; nesting from `cylinder_succ_subset`). -/
noncomputable def strictVerdicts : LevelVerdicts p n FactorizationType where
  verdict N x :=
    if h : ∃ τ, TD.StrictDecided p n N x τ then some h.choose else none
  nested N x τ h := by
    by_cases hN : ∃ τ', TD.StrictDecided p n N (levelCast p n N x) τ'
    · rw [dif_pos hN] at h
      -- the chosen verdict at level N is τ, and it transports down (I-A7)
      have hτ : TD.StrictDecided p n N (levelCast p n N x) τ :=
        Option.some.inj h ▸ hN.choose_spec
      have hsucc : TD.StrictDecided p n (N + 1) x τ := TD.strictDecided_succ p n hτ
      have hex : ∃ τ', TD.StrictDecided p n (N + 1) x τ' := ⟨τ, hsucc⟩
      rw [dif_pos hex]
      -- ≤-one-τ pins the choice at level N+1 to τ
      exact congrArg some (TD.strictDecided_unique p n hex.choose_spec hsucc)
    · rw [dif_neg hN] at h
      exact absurd h (by simp)

theorem strictVerdicts_spec (N x τ) :
    (TD.strictVerdicts p n).verdict N x = some τ ↔ TD.StrictDecided p n N x τ := by
  constructor
  · intro h
    by_cases hex : ∃ τ', TD.StrictDecided p n N x τ'
    · have h' : some hex.choose = some τ := by
        rw [← h]; simp [strictVerdicts, dif_pos hex]
      exact Option.some.inj h' ▸ hex.choose_spec
    · simp [strictVerdicts, dif_neg hex] at h
  · intro h
    have hex : ∃ τ', TD.StrictDecided p n N x τ' := ⟨τ, h⟩
    have hch : (TD.strictVerdicts p n).verdict N x = some hex.choose := by
      simp [strictVerdicts, dif_pos hex]
    rw [hch]
    exact congrArg some (TD.strictDecided_unique p n hex.choose_spec h)

end TypeData

variable (TD : TypeData p n)

/-! ## Unit I-E5: MEAS-BRIDGE(i) — the locus is open, hence measurable

Route (the BP row's second option, no I-E4 machinery): around every point of
L_τ, `LR.locality` freezes `Sep` and `typeOf` on a whole cylinder, and
cylinders are open by I-A6 (`isClopen_cylinder`). -/

theorem isOpen_locus (LR : LocalityRow p n TD) (τ) :
    IsOpen (TD.locus p n τ)                                           -- (i)
  := by
  rw [isOpen_iff_forall_mem_open]
  rintro a ⟨hsep, htype⟩
  obtain ⟨N, hN⟩ := LR.locality a hsep
  refine ⟨cylinder p n N (toLevel p n N a), fun b hb => ?_,
    (isClopen_cylinder p n N _).isOpen, mem_cylinder_self p n N a⟩
  obtain ⟨hbsep, hbtype⟩ := hN b hb
  exact ⟨hbsep, hbtype.trans htype⟩

/-- The measurability half of I-E5: open (`isOpen_locus`) → Borel-measurable
through the I-A2 `BorelSpace` layer. -/
theorem measurableSet_locus (LR : LocalityRow p n TD) (τ) :
    MeasurableSet (TD.locus p n τ) :=
  (isOpen_locus p n TD LR τ).measurableSet

/-! ## Unit I-E4: MEAS-BRIDGE(iv), EXACT in the strict convention — the
decided sets exhaust the locus (Df §4 proof of (iv); the Dfloor leaf's
headline). ⊆: a is a lift of its own class (I-A5 `mem_cylinder_self`), so a
strict verdict on a's class reads back on a itself. ⊇: `LR.locality` gives
the decided level — the (LOC) cylinder around a is strictly decided with
verdict τ, so a's class carries the verdict there (I-E3 spec). -/

/-- MEAS-BRIDGE(iv), EXACT in the strict convention (the leaf's headline). -/
theorem iUnion_decided_eq_locus (LR : LocalityRow p n TD) (τ) :
    ⋃ N, (TD.strictVerdicts p n).decidedSet τ N = TD.locus p n τ := by
  ext a
  simp only [Set.mem_iUnion]
  constructor
  · -- ⊆: a is a lift of its own class
    rintro ⟨N, ha⟩
    have hd : TD.StrictDecided p n N (toLevel p n N a) τ :=
      (TD.strictVerdicts_spec p n N (toLevel p n N a) τ).mp ha
    exact hd a (mem_cylinder_self p n N a)
  · -- ⊇: `LR.locality` gives the decided level
    rintro ⟨hsep, hτ⟩
    obtain ⟨N, hN⟩ := LR.locality a hsep
    refine ⟨N, (TD.strictVerdicts_spec p n N (toLevel p n N a) τ).mpr
      fun b hb => ?_⟩
    obtain ⟨hbsep, hbτ⟩ := hN b hb
    exact ⟨hbsep, hbτ.trans hτ⟩

/-! (dedup, wave-E merge: the I-E8a prover's transcribed I-E3 prerequisites —
same BP-verbatim `StrictDecided`/`strictVerdicts`/`strictVerdicts_spec`
statements as the canonical I-E3 block declared above — stood here; removed,
each declaration is made once. I-E8a consumes the canonical copy.) -/

/-! (dedup, wave-E merge at the I-E8b landing: a SECOND I-E4 landing — same
BP-verbatim `iUnion_decided_eq_locus` statement and same route as the
canonical I-E4 block declared above — stood here; removed, the theorem is
declared once. Consumers use the canonical copy above.) -/

/-! ## Unit I-E8a: SEM-DRAIN, the set half (Df §4.2)

⊆ ("decided at some N iff separable", forward): a separable point's (LOC)
cylinder is strictly decided at its level — the point leaves U_N there, so
membership in every U_N forces nonseparability. ⊇ (LOC-free): a nonseparable
point is a lift of its own class at every level (I-A5 `mem_cylinder_self`),
so no strict verdict can ever fire; the class stays undecided at every N. -/

/-- SEM-DRAIN: ⋂_N U_N = the nonseparable locus; hence undec ↓ 0 (via
`undec_tendsto_zero` + `ns_null`). Unconditional at every prime incl. wild. -/
theorem iInter_undec_eq_nonSep (LR : LocalityRow p n TD) :
    ⋂ N, (TD.strictVerdicts p n).undecSet N = {a | ¬ Sep p n a} := by
  ext a
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · -- forward: undecided at every level ⇒ nonseparable (the LOC direction)
    intro hund hsep
    obtain ⟨N, hN⟩ := LR.locality a hsep
    -- the (LOC) cylinder is strictly decided with verdict `TD.typeOf a` …
    have hdec : TD.StrictDecided p n N (toLevel p n N a) (TD.typeOf a) := hN
    have hsome := (TD.strictVerdicts_spec p n N (toLevel p n N a)
      (TD.typeOf a)).mpr hdec
    -- … contradicting membership in U_N
    have hnone : (TD.strictVerdicts p n).verdict N (toLevel p n N a) = none :=
      hund N
    rw [hnone] at hsome
    exact Option.some_ne_none _ hsome.symm
  · -- reverse: nonseparable ⇒ never decided (a witnesses its own class)
    intro hnsep N
    show (TD.strictVerdicts p n).verdict N (toLevel p n N a) = none
    cases hv : (TD.strictVerdicts p n).verdict N (toLevel p n N a) with
    | none => rfl
    | some τ =>
      have hdec := (TD.strictVerdicts_spec p n N (toLevel p n N a) τ).mp hv
      exact absurd (hdec a (mem_cylinder_self p n N a)).1 hnsep

/-! ## Unit I-E8b: SEM-DRAIN, the measure half (Df §4.2; ROOT Step 13)

Glue: rewrite the residual intersection ⋂_N U_N by I-E8a
(`iInter_undec_eq_nonSep`), read its mass by the (NS-NULL) row (`NR.ns_null`),
then fire the I-C8 drainage shell (`LevelVerdicts.undec_tendsto_zero`).
Statement BP_I §1.5 VERBATIM, with the §1 preamble's licensed bookkeeping
adjustment: the §1.5 display `.undecMass p n N` reads `.undecMass N` against
the LANDED I-C1 signature (`p n` implicit on `LevelVerdicts`, per the
Decided.lean dot-notation convention). -/

/-- SEM-DRAIN: undec ↓ 0 (via `undec_tendsto_zero` + `ns_null`).
Unconditional at every prime incl. wild. -/
theorem undec_tendsto_zero_sem (LR : LocalityRow p n TD) (NR : NsNullRow p n) :
    Filter.Tendsto (fun N => ((TD.strictVerdicts p n).undecMass N).toReal)
      Filter.atTop (nhds 0) :=
  (TD.strictVerdicts p n).undec_tendsto_zero
    (by rw [iInter_undec_eq_nonSep p n TD LR]; exact NR.ns_null)

/-! (dedup, wave-E merge: a second I-E3 transcription — same BP-verbatim
`StrictDecided`/`strictVerdicts`/`strictVerdicts_spec` statements as the
canonical I-E3 block in the `TypeData` namespace above, via a `strictVerdict`
helper — stood here, AFTER its I-E8a consumer; removed, each declaration is
made once. I-E8a consumes the canonical copy above.) -/

/-! (dedup, wave-E merge: the I-E6b prover's transcribed I-E4 dependency —
same BP-verbatim `iUnion_decided_eq_locus` statement as the canonical Unit
I-E4 declaration above, which landed concurrently — stood here; removed, the
theorem is declared once. I-E6b consumes the canonical copy.) -/

/-! ## Unit I-E6b: CLAUSE (0) — α is the cylinder-count limit

(ROOT §1 (0); Df §4 (v).) Glue: the I-C6 abstract shell
`LevelVerdicts.alpha_limit_abstract` at the strict verdicts, with exhaustion
I-E4 (`iUnion_decided_eq_locus`) and measurability I-E5
(`measurableSet_locus`). INTERFACE (BP_I §4 wave-plan report): `alpha`/
`alphaR` consume `TypeData` only; `alpha_eq_lim` consumes
`TypeData + LocalityRow` (LOC) — and NO NS-NULL row: no drainage enters
clause (0). -/

/-- Clause (0): α is the cylinder-count limit (glue: `alpha_limit_abstract` +
`iUnion_decided_eq_locus`). -/
theorem alpha_eq_lim (LR : LocalityRow p n TD) (τ) :
    Filter.Tendsto
      (fun N => ((TD.strictVerdicts p n).decidedCount τ N : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds (TD.alphaR p n τ)) := by
  have h := (TD.strictVerdicts p n).alpha_limit_abstract τ
    (measurableSet_locus p n TD LR τ) (iUnion_decided_eq_locus p n TD LR τ)
  simpa [TypeData.alphaR, TypeData.alpha] using h

/-! ## Unit I-E7: CLAUSE (SQ)'s bracket at the semantic instance

(Df §4.2 BRACKET proof.) The cover step: either a's level-N class is decided
— and the verdict is then FORCED to τ by the lift argument (a witnesses its
own class, I-A5 `mem_cylinder_self`, read against the I-E3 spec) — or the
class is undecided. Then the I-C5 abstract shell
`LevelVerdicts.bracket_abstract` fires at the strict verdicts (lower
inclusion D_τ(N) ⊆ L_τ by the same lift argument). INTERFACE (BP_I §4
wave-plan report): consumes TYPE-OF only — neither LOC (`LocalityRow`) nor
NS-NULL (`NsNullRow`) enters. (Bookkeeping note, per BP_I §1 preamble "exact
implicit/explicit bookkeeping is the E-phase's to adjust": the landed I-C1
`undecMass` carries `{p n}` implicit — Decided.lean, §1.3-display fidelity —
so the §1.5 display's `.undecMass p n N` reads `.undecMass N` here; the same
term, no statement change.) -/

/-- The cover L_τ ⊆ D_τ(N) ∪ U_N (brief Cor BRACKET upper half's set step). -/
theorem locus_subset_decided_union_undec (τ N) :
    TD.locus p n τ ⊆ (TD.strictVerdicts p n).decidedSet τ N
      ∪ (TD.strictVerdicts p n).undecSet N := by
  rintro a ⟨hsep, hτa⟩
  cases hv : (TD.strictVerdicts p n).verdict N (toLevel p n N a) with
  | none =>
    -- undecided class: a lands in U_N
    exact Or.inr hv
  | some τ' =>
    -- decided class: the verdict is forced to τ by the lift argument
    refine Or.inl (show (TD.strictVerdicts p n).verdict N (toLevel p n N a)
      = some τ from ?_)
    have hd := (TD.strictVerdicts_spec p n N (toLevel p n N a) τ').mp hv
    rw [hv, ((hd a (mem_cylinder_self p n N a)).2.symm).trans hτa]

/-- **Clause (SQ)'s bracket at the semantic instance** (glue via
`bracket_abstract`). -/
theorem alpha_bracket (τ N) :
    ((TD.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        ≤ TD.alpha p n τ ∧
    TD.alpha p n τ ≤ ((TD.strictVerdicts p n).decidedCount τ N : ENNReal) / (p : ENNReal) ^ (n * N)
        + (TD.strictVerdicts p n).undecMass N := by
  -- lower inclusion D_τ(N) ⊆ L_τ: every point of a strictly τ-decided class
  -- is separable of type τ (the lift argument again, via the I-E3 spec)
  have hlow : (TD.strictVerdicts p n).decidedSet τ N ⊆ TD.locus p n τ :=
    fun a ha => ((TD.strictVerdicts_spec p n N (toLevel p n N a) τ).mp ha) a
      (mem_cylinder_self p n N a)
  -- the I-C5 shell at the strict verdicts, with the cover above
  have h := (TD.strictVerdicts p n).bracket_abstract τ N hlow
    (locus_subset_decided_union_undec p n TD τ N)
  simpa [TypeData.alpha] using h

/-! ## I-E9 (PARKED ROW — statement displayed, NO proof unit): SEM-DRAIN-RATE

Source: Df §4.2 Corollary SEM-DRAIN-RATE
(`lean/notes/openmath/Dfloor_phaseB_verifybrief_rev2.md` L394–406);
blueprint row: `lean/blueprints/BP_I.md` §2 Wave E, I-E9. Parked pending a
quantitative M05 import decision; scheduled after Wave H (BP_I §0 convention
6 and §4 cross-movement seams). Step 19 consumes QUALITATIVE drainage only
(`undec_tendsto_zero_sem`, I-E8b); this row is its quantitative envelope.
NO Lean declaration is made here — displayed with its I-3 provenance only.

**Corollary SEM-DRAIN-RATE** [(b): a one-line strengthening of M05's
verified Theorem E from the lax to the strict convention]. For n ≥ 2 and
w := n·v_p(n):

    undec(N) ≤ (n−1) · p^{−max(0, ⌈(⌈N/2⌉ − w)/(n−1)⌉)}.

Proof shape (Df §4.2, not formalized here): if a ∈ U_N and f_a is separable
with 2·v(disc f_a) + 1 ≤ N, then every lift of a's level-N class is ≡ f_a
(mod p^{2v+1}), so by I-1 (M05 Lemma D, V2-upheld) a's class is
σ(f_a)-decided — contradiction. For integers v, 2v + 1 > N ⟺ v ≥ ⌈N/2⌉,
hence U_N ⊆ {a : v(disc f_a) ≥ ⌈N/2⌉} (v(0) = ∞), and the I-3 tail bound
applies at m = ⌈N/2⌉.

I-3 provenance (the quantitative import this row consumes): for n ≥ 2, every
prime p, every m ≥ 0, with w := n·v_p(n),

    μ{a : v(disc f_a) ≥ m} ≤ (n−1)·p^{−max(0, ⌈(m−w)/(n−1)⌉)}

(the event read with v(0) = ∞); in particular μ{a : disc f_a = 0} = 0.
[M05 §§2–3 (Lemmas B + C); the Codex pass V2 items 6–7 upheld exactly these.
The tail clause is consumed ONLY by SEM-DRAIN-RATE — the NULL clause has
independent carriers (Df Appendix A; T-6 (ns-null)).] Unconditional at every
prime including wild. -/

end LeanUrat.Scaffold
