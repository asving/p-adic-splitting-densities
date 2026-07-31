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
untouched; I-E4's verdict machinery is NOT transcribed here.) With I-E5's
BP-verbatim transcribed dependencies I-E2b (`LocalityRow`, `NsNullRow`) and
the `locus` def.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space
import LeanUrat.Scaffold.MeasureFloor.Haar
import LeanUrat.Scaffold.MeasureFloor.Types
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

end TypeData

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
