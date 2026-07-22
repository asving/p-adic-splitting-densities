/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.ChainMenu

/-!
# QpTypeChain — the PROVED translation/rescale invariance of `qpType`, and the axiom-free
depth-1 chain-gate anchor (Wild Wave 5c, `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §2-W5c)

**Provenance.** The W5c declaration gate (boundary #5, lift invariance) was completed 2026-07-22:
`notes/GMN_citations.md` §"Lift/representative invariance — pin (P4)". Per (P4d) there, the paper
does NOT state translation-form invariance; the translation content is PROVED here, not imported:

* `affLift a c h` — the factor transport along the substitution `x = a·y + c`: for monic `h` of
  degree `d`, the monic polynomial `a^d·h((x − c)/a)` with `ℤ_[p]`-coefficients, characterized by
  `(affLift a c h).comp (C a * X + C c) = C (a^d) * h` (`affLift_comp`).
* `qpType_translate_rescale` — **the [COUNT] translation lemma** (the blueprint §1 σ-keying
  design lemma, note `MATH_FULLTYPE_DECOMPOSITION` §1/§6): if
  `f.comp (C a * X + C c) = C (a^{deg g}) * g` (i.e. `g(y) = f(a·y + c)/a^{deg g}` — the
  whole-window recenter–rescale at `a = p^m`, `c = ĉp^m`, or a pure translation at `a = 1`), then
  every `QpFactorization` of `g` transports to one of `f` **with the same `qpType`**: roots
  correspond along the affine bijection, each factor generates the SAME field `L` (the bundle
  `LocalFactorData` transports with `L`, `O` literally unchanged — `compData` — so `eOf`/`fOf`
  are untouched). Stated for ANY `a ≠ 0`, any degree (stronger than the n = 2 need).
* `chainGateFiber_decode` / `chainGate_irreducible` / `chainGate_ef_forced` — **the axiom-free
  depth-1 chain-gate anchor** (blueprint §2-W5c "Anchors"): membership of a genuine monic
  quadratic in the `ChainCell [1] (ram 1)` fiber at level `N ≥ 4` forces, END TO END with no
  axiom: the recentered polynomial `g = f(ĉp + p·y)/p²` is genuinely Eisenstein
  (via the box→genuine digit decode `dvd_of_box_dvd`/`box_shift_cast`), hence `f` itself is
  IRREDUCIBLE over ℚ_p and EVERY `LocalFactorData` bundle on `f` carries `efOf = (2, 1)`
  (via `QpTypeEisenstein.ef_of_eisenstein` on `g` + the bundle transport back along the
  substitution). This is the full semantic anchor for the chain branch of the re-scoped axiom.
* `chainGatePoly` (`X² + 4` over `ℤ_[2]`, `N = 4` — the recentered read is exactly the W1 gate
  witness `y² + 2y + 2`) — the chain-gate fiber is INHABITED, so the scope-#4 mutation probes
  (evidence blocks below) genuinely fire.

Leaf module discipline: **no axiom, no `sorry`** — every declaration core-only (AxCheck at
bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.QpTypeChain

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## Block 1 — the affine factor transport `affLift` (any commutative ring) -/

section AffLift

variable {R : Type*} [CommRing R]

/-- **The affine factor transport**: for the substitution `x = a·y + c`, the polynomial
`affLift a c h = Σ_j h_j·a^{d−j}·(x − c)^j` (`d = deg h`) — i.e. `a^d·h((x − c)/a)` with the
denominators cleared. For monic `h` it is monic of the same degree (`affLift_monic`), and it is
characterized by the composition identity `affLift_comp`. -/
noncomputable def affLift (a c : R) (h : R[X]) : R[X] :=
  ∑ j ∈ Finset.range (h.natDegree + 1), C (h.coeff j * a ^ (h.natDegree - j)) * (X - C c) ^ j

/-- **The characterizing composition identity**: `(affLift a c h)(a·y + c) = a^{deg h}·h(y)`. -/
theorem affLift_comp (a c : R) (h : R[X]) :
    (affLift a c h).comp (C a * X + C c) = C (a ^ h.natDegree) * h := by
  rw [affLift]
  show Polynomial.eval₂ C (C a * X + C c) _ = _
  rw [Polynomial.eval₂_finsetSum]
  have hterm : ∀ j ∈ Finset.range (h.natDegree + 1),
      Polynomial.eval₂ C (C a * X + C c) (C (h.coeff j * a ^ (h.natDegree - j)) * (X - C c) ^ j)
        = C (a ^ h.natDegree) * (C (h.coeff j) * X ^ j) := by
    intro j hj
    have hjd : j ≤ h.natDegree := by
      have := Finset.mem_range.mp hj
      omega
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, add_sub_cancel_right, mul_pow, ← Polynomial.C_pow]
    rw [show (C (a ^ j) : R[X]) * X ^ j = C (a ^ j) * X ^ j from rfl]
    have hpow : a ^ (h.natDegree - j) * a ^ j = a ^ h.natDegree := by
      rw [← pow_add]
      congr 1
      omega
    calc C (h.coeff j * a ^ (h.natDegree - j)) * (C (a ^ j) * X ^ j)
        = C (h.coeff j * (a ^ (h.natDegree - j) * a ^ j)) * X ^ j := by
          rw [← mul_assoc, ← Polynomial.C_mul, mul_assoc]
      _ = C (a ^ h.natDegree) * (C (h.coeff j) * X ^ j) := by
          rw [hpow, ← mul_assoc, ← Polynomial.C_mul, mul_comm (h.coeff j) (a ^ h.natDegree)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  exact (Polynomial.as_sum_range_C_mul_X_pow h).symm

variable [IsDomain R]

/-- Composition with a genuinely linear polynomial is injective (over a domain). -/
theorem comp_linear_injective {a : R} (ha : a ≠ 0) (c : R) :
    Function.Injective (fun P : R[X] => P.comp (C a * X + C c)) := by
  have hq1 : (C a * X + C c).natDegree = 1 := Polynomial.natDegree_linear ha
  intro P₁ P₂ hP
  by_contra hne
  have hsub : (P₁ - P₂).comp (C a * X + C c) = 0 := by
    rw [Polynomial.sub_comp]
    simpa using sub_eq_zero_of_eq hP
  have hP0 : P₁ - P₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hlead : ((P₁ - P₂).comp (C a * X + C c)).leadingCoeff
      = (P₁ - P₂).leadingCoeff * (C a * X + C c).leadingCoeff ^ (P₁ - P₂).natDegree :=
    Polynomial.leadingCoeff_comp (by rw [hq1]; omega)
  have hqne : (C a * X + C c) ≠ 0 := by
    intro h0
    rw [h0] at hq1
    simp at hq1
  have hne0 : ((P₁ - P₂).comp (C a * X + C c)).leadingCoeff ≠ 0 := by
    rw [hlead]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP0)
      (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hqne))
  rw [hsub] at hne0
  simp at hne0

/-- `affLift` of a monic polynomial is monic. -/
theorem affLift_monic {h : R[X]} (hm : h.Monic) (a c : R) : (affLift a c h).Monic := by
  rw [affLift, Finset.sum_range_succ, hm.coeff_natDegree, Nat.sub_self, pow_zero, mul_one,
    map_one, one_mul]
  refine Polynomial.Monic.add_of_right ((monic_X_sub_C c).pow _) ?_
  have hpowdeg : ((X - C c) ^ h.natDegree : R[X]).degree = (h.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
    simp
  rw [hpowdeg]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
  intro j hj
  have hjd : j < h.natDegree := Finset.mem_range.mp hj
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have h1 : (C (h.coeff j * a ^ (h.natDegree - j)) : R[X]).degree ≤ 0 := Polynomial.degree_C_le
  have h2 : ((X - C c) ^ j : R[X]).degree = (j : WithBot ℕ) := by
    rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
    simp
  calc (C (h.coeff j * a ^ (h.natDegree - j)) : R[X]).degree + ((X - C c) ^ j).degree
      ≤ 0 + (j : WithBot ℕ) := add_le_add h1 (le_of_eq h2)
    _ = (j : WithBot ℕ) := zero_add _
    _ < (h.natDegree : WithBot ℕ) := by exact_mod_cast hjd

/-- `affLift` preserves the degree of a monic polynomial (`a ≠ 0`): read off the composition
identity. -/
theorem affLift_natDegree {h : R[X]} (hm : h.Monic) {a : R} (ha : a ≠ 0) (c : R) :
    (affLift a c h).natDegree = h.natDegree := by
  have hcompdeg := congrArg Polynomial.natDegree (affLift_comp a c h)
  have hq1' : (C a * X + C c).natDegree = 1 := Polynomial.natDegree_linear ha
  rw [Polynomial.natDegree_comp, hq1', mul_one] at hcompdeg
  have hCne : (C (a ^ h.natDegree) : R[X]) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ ha
  rw [Polynomial.natDegree_mul hCne hm.ne_zero, Polynomial.natDegree_C, zero_add] at hcompdeg
  exact hcompdeg

/-- **Injectivity of `affLift` on monic polynomials** (`a ≠ 0`): the composition identity plus
degree bookkeeping recover `h` from `affLift a c h`. -/
theorem affLift_injective {h₁ h₂ : R[X]} (hm₁ : h₁.Monic) (hm₂ : h₂.Monic) {a : R} (ha : a ≠ 0)
    (c : R) (heq : affLift a c h₁ = affLift a c h₂) : h₁ = h₂ := by
  have hdeg : h₁.natDegree = h₂.natDegree := by
    rw [← affLift_natDegree hm₁ ha c, ← affLift_natDegree hm₂ ha c, heq]
  have hcomp : C (a ^ h₁.natDegree) * h₁ = C (a ^ h₂.natDegree) * h₂ := by
    rw [← affLift_comp a c h₁, ← affLift_comp a c h₂, heq]
  rw [← hdeg] at hcomp
  exact mul_left_cancel₀ (by rw [Ne, Polynomial.C_eq_zero]; exact pow_ne_zero _ ha) hcomp

end AffLift

/-! ## Block 2 — irreducibility transfer along affine substitution (any field) -/

section AffField

variable {K : Type*} [Field K]

/-- The affine substitution `P ↦ P(a·X + c)` as an algebra automorphism of `K[X]` (`a ≠ 0`). -/
noncomputable def affEquiv (a : K) (ha : a ≠ 0) (c : K) : K[X] ≃ₐ[K] K[X] :=
  AlgEquiv.ofAlgHom (Polynomial.aeval (C a * X + C c))
    (Polynomial.aeval (C a⁻¹ * X + C (-(c / a))))
    (by
      refine Polynomial.algHom_ext ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, AlgHom.coe_id, id_eq]
      rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
      simp only [Polynomial.algebraMap_eq]
      rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1,
        one_mul, ← Polynomial.C_mul, add_assoc, ← Polynomial.C_add,
        show a⁻¹ * c + -(c / a) = 0 from by field_simp; ring, Polynomial.C_0, add_zero])
    (by
      refine Polynomial.algHom_ext ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, AlgHom.coe_id, id_eq]
      rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
      simp only [Polynomial.algebraMap_eq]
      rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ ha, Polynomial.C_1,
        one_mul, ← Polynomial.C_mul, add_assoc, ← Polynomial.C_add,
        show a * -(c / a) + c = 0 from by field_simp; ring, Polynomial.C_0, add_zero])

theorem affEquiv_apply (a : K) (ha : a ≠ 0) (c : K) (P : K[X]) :
    affEquiv a ha c P = P.comp (C a * X + C c) := by
  show Polynomial.aeval (C a * X + C c) P = P.comp (C a * X + C c)
  rw [Polynomial.aeval_def, Polynomial.comp, Polynomial.algebraMap_eq]

/-- **Irreducibility transfers along affine substitution** (`a ≠ 0`, over a field). -/
theorem irreducible_comp_linear_iff (a : K) (ha : a ≠ 0) (c : K) (P : K[X]) :
    Irreducible (P.comp (C a * X + C c)) ↔ Irreducible P := by
  rw [← affEquiv_apply a ha c]
  exact MulEquiv.irreducible_iff (affEquiv a ha c).toMulEquiv

/-- Irreducibility is unchanged by a nonzero constant factor (over a field). -/
theorem irreducible_C_mul_iff {u : K} (hu : u ≠ 0) (P : K[X]) :
    Irreducible (C u * P) ↔ Irreducible P := by
  have hunit : IsUnit (C u : K[X]) := Polynomial.isUnit_C.mpr (Ne.isUnit hu)
  rw [← hunit.unit_spec]
  exact irreducible_units_mul hunit.unit

end AffField

/-! ## Block 3 — the bundle transport `compData` (same `L`, same `O`, new root) -/

section Transport

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Bundle transport along an affine comp identity.** If
`(h'.map ℚ_p).comp (C α·X + C β) = C γ · (h.map ℚ_p)` with `α ≠ 0` and `deg h' = deg h`, every
`LocalFactorData` bundle on `h` yields one on `h'` with the SAME field `L` and the SAME integer
ring `O` (the root of `h'` is the affine image `α·x + β` of the root of `h`, generating the same
field) — so `eOf`/`fOf` are literally unchanged (`efOf_compData`). -/
noncomputable def compData {h h' : ℤ_[p][X]} (α β γ : ℚ_[p]) (hα : α ≠ 0)
    (hdeg : h'.natDegree = h.natDegree)
    (hcomp : (h'.map (algebraMap ℤ_[p] ℚ_[p])).comp (C α * X + C β)
      = C γ * h.map (algebraMap ℤ_[p] ℚ_[p]))
    (D : QpType.LocalFactorData p h) : QpType.LocalFactorData p h' :=
  letI := D.fieldL
  letI := D.algQL
  letI := D.algZL
  letI := D.towerZQL
  { L := D.L
    fieldL := D.fieldL
    algQL := D.algQL
    algZL := D.algZL
    towerZQL := D.towerZQL
    finrank_eq := by rw [hdeg]; exact D.finrank_eq
    hasRoot := by
      obtain ⟨x, hx0, hxadj⟩ := D.hasRoot
      refine ⟨algebraMap ℚ_[p] D.L α * x + algebraMap ℚ_[p] D.L β, ?_, ?_⟩
      · have hev := congrArg (Polynomial.aeval x) hcomp
        rw [Polynomial.aeval_comp] at hev
        rw [map_mul, Polynomial.aeval_C, hx0, mul_zero] at hev
        have hq : Polynomial.aeval x (C α * X + C β : ℚ_[p][X])
            = algebraMap ℚ_[p] D.L α * x + algebraMap ℚ_[p] D.L β := by
          rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
        rwa [hq] at hev
      · set x' : D.L := algebraMap ℚ_[p] D.L α * x + algebraMap ℚ_[p] D.L β with hx'def
        have hxmem : x ∈ Algebra.adjoin ℚ_[p] ({x'} : Set D.L) := by
          have hself : x' ∈ Algebra.adjoin ℚ_[p] ({x'} : Set D.L) :=
            Algebra.subset_adjoin (Set.mem_singleton _)
          have hxeq : x = algebraMap ℚ_[p] D.L α⁻¹ * (x' - algebraMap ℚ_[p] D.L β) := by
            rw [hx'def, add_sub_cancel_right, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hα,
              map_one, one_mul]
          rw [hxeq]
          exact mul_mem (Subalgebra.algebraMap_mem _ _)
            (sub_mem hself (Subalgebra.algebraMap_mem _ _))
        have hle : Algebra.adjoin ℚ_[p] ({x} : Set D.L)
            ≤ Algebra.adjoin ℚ_[p] ({x'} : Set D.L) :=
          Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxmem)
        rw [hxadj] at hle
        exact eq_top_iff.mpr hle
    O := D.O
    crO := D.crO
    domO := D.domO
    dvrO := D.dvrO
    algZO := D.algZO
    algOL := D.algOL
    towerZOL := D.towerZOL
    intClosure := D.intClosure
    liesOver := D.liesOver }

/-- The transported bundle has the SAME `(e, f)` — `L` and `O` are literally unchanged. -/
theorem efOf_compData {h h' : ℤ_[p][X]} (α β γ : ℚ_[p]) (hα : α ≠ 0)
    (hdeg : h'.natDegree = h.natDegree)
    (hcomp : (h'.map (algebraMap ℤ_[p] ℚ_[p])).comp (C α * X + C β)
      = C γ * h.map (algebraMap ℤ_[p] ℚ_[p]))
    (D : QpType.LocalFactorData p h) :
    QpType.efOf p (compData p α β γ hα hdeg hcomp D) = QpType.efOf p D := rfl

end Transport

/-! ## Block 4 — the [COUNT] translation lemma `qpType_translate_rescale` -/

section Translate

variable (p : ℕ) [hp : Fact p.Prime]

/-- A list of monics has monic product. -/
theorem monic_list_prod (l : List ℤ_[p][X]) (hm : ∀ h ∈ l, h.Monic) : l.prod.Monic := by
  induction l with
  | nil =>
      rw [List.prod_nil]
      exact monic_one
  | cons h t ih =>
      rw [List.prod_cons]
      exact (hm h List.mem_cons_self).mul
        (ih fun x hx => hm x (List.mem_cons_of_mem h hx))

/-- Degree of a product of monics is the sum of degrees. -/
theorem natDegree_list_prod_of_monic (l : List ℤ_[p][X]) (hm : ∀ h ∈ l, h.Monic) :
    l.prod.natDegree = (l.map Polynomial.natDegree).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        (hm h List.mem_cons_self).natDegree_mul
          (monic_list_prod p t fun x hx => hm x (List.mem_cons_of_mem h hx)),
        ih fun x hx => hm x (List.mem_cons_of_mem h hx)]

/-- The transported factor list composes back: the product of the `affLift`s picks up exactly
the factor `C (a^{Σ degrees})`. -/
theorem prod_map_affLift_comp (a c : ℤ_[p]) (l : List ℤ_[p][X]) :
    ((l.map (affLift a c)).prod).comp (C a * X + C c)
      = C (a ^ (l.map Polynomial.natDegree).sum) * l.prod := by
  induction l with
  | nil => simp
  | cons h t ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, Polynomial.mul_comp, affLift_comp, ih,
        List.map_cons, List.sum_cons, pow_add, map_mul]
      ring

/-- Congruence for the `efOf` read of a factorization's bundle (membership proofs are
irrelevant). -/
theorem efOf_data_congr {g : ℤ_[p][X]} (F : QpType.QpFactorization p g) {h₁ h₂ : ℤ_[p][X]}
    (e : h₁ = h₂) (m₁ : h₁ ∈ F.factors) (m₂ : h₂ ∈ F.factors) :
    QpType.efOf p (F.data h₁ m₁) = QpType.efOf p (F.data h₂ m₂) := by
  subst e; rfl

/-- `pmap` over a mapped list agrees with `pmap` over the original when the values agree
pointwise. -/
theorem pmap_map_eq {α β γ : Type*} (tr : α → β) (l : List α)
    {P : β → Prop} {Q : α → Prop}
    (F1 : ∀ b, P b → γ) (F2 : ∀ a, Q a → γ)
    (H1 : ∀ b ∈ l.map tr, P b) (H2 : ∀ a ∈ l, Q a)
    (hcong : ∀ a, a ∈ l → ∀ (h1 : P (tr a)) (h2 : Q a), F1 (tr a) h1 = F2 a h2) :
    (l.map tr).pmap F1 H1 = l.pmap F2 H2 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      simp only [List.map_cons, List.pmap]
      congr 1
      · exact hcong x List.mem_cons_self _ _
      · exact ih _ _ (fun a ha h1 h2 => hcong a (List.mem_cons_of_mem x ha) h1 h2)

/-- The mapped composition identity for `affLift` over ℚ_p. -/
theorem affLift_map_comp (a c : ℤ_[p]) (h : ℤ_[p][X]) :
    ((affLift a c h).map (algebraMap ℤ_[p] ℚ_[p])).comp
        (C ((algebraMap ℤ_[p] ℚ_[p]) a) * X + C ((algebraMap ℤ_[p] ℚ_[p]) c))
      = C (((algebraMap ℤ_[p] ℚ_[p]) a) ^ h.natDegree) * h.map (algebraMap ℤ_[p] ℚ_[p]) := by
  have hmc := congrArg (Polynomial.map (algebraMap ℤ_[p] ℚ_[p])) (affLift_comp a c h)
  rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C, map_pow] at hmc
  exact hmc

/-- The algebra map `ℤ_[p] → ℚ_[p]` reflects nonzeroness. -/
theorem algebraMap_ne_zero {a : ℤ_[p]} (ha : a ≠ 0) : (algebraMap ℤ_[p] ℚ_[p]) a ≠ 0 :=
  fun h0 => ha (IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h0, map_zero]))

/-- **The transported bundle along `affLift`**: `compData` at the mapped composition
identity. Same `L`, same `O`; `efOf` unchanged (`efOf_affData`). -/
noncomputable def affData (a c : ℤ_[p]) (ha : a ≠ 0) {h : ℤ_[p][X]} (hm : h.Monic)
    (D : QpType.LocalFactorData p h) : QpType.LocalFactorData p (affLift a c h) :=
  compData p ((algebraMap ℤ_[p] ℚ_[p]) a) ((algebraMap ℤ_[p] ℚ_[p]) c)
    (((algebraMap ℤ_[p] ℚ_[p]) a) ^ h.natDegree) (algebraMap_ne_zero p ha)
    (affLift_natDegree hm ha c) (affLift_map_comp p a c h) D

theorem efOf_affData (a c : ℤ_[p]) (ha : a ≠ 0) {h : ℤ_[p][X]} (hm : h.Monic)
    (D : QpType.LocalFactorData p h) :
    QpType.efOf p (affData p a c ha hm D) = QpType.efOf p D := rfl

/-- Transport of a bundle across a polynomial equality. -/
noncomputable def castData {h₁ h₂ : ℤ_[p][X]} (e : h₁ = h₂)
    (D : QpType.LocalFactorData p h₁) : QpType.LocalFactorData p h₂ := e ▸ D

/-- `efOf` is invariant under transporting a bundle across a polynomial equality. -/
theorem efOf_castData {h₁ h₂ : ℤ_[p][X]} (e : h₁ = h₂) (D : QpType.LocalFactorData p h₁) :
    QpType.efOf p (castData p e D) = QpType.efOf p D := by
  subst e
  rfl

/-- **The transported factorization** along `f.comp (C a·X + C c) = C (a^{deg g})·g`
(i.e. `g(y) = f(a·y + c)/a^{deg g}`): factors are the `affLift`s, bundles transport by
`affData` (fields unchanged). -/
noncomputable def translateFactorization (a c : ℤ_[p]) (ha : a ≠ 0) {f g : ℤ_[p][X]}
    (hrel : f.comp (C a * X + C c) = C (a ^ g.natDegree) * g)
    (F : QpType.QpFactorization p g) : QpType.QpFactorization p f where
  factors := F.factors.map (affLift a c)
  prod_eq := by
    have hdegsum : (F.factors.map Polynomial.natDegree).sum = g.natDegree := by
      rw [← natDegree_list_prod_of_monic p F.factors F.monic, F.prod_eq]
    apply comp_linear_injective ha c
    show ((F.factors.map (affLift a c)).prod).comp (C a * X + C c) = f.comp (C a * X + C c)
    rw [prod_map_affLift_comp, hdegsum, F.prod_eq, hrel]
  monic := by
    intro g' hg'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg'
    exact affLift_monic (F.monic h hh) a c
  irred := by
    intro g' hg'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg'
    have haQ : (algebraMap ℤ_[p] ℚ_[p]) a ≠ 0 := algebraMap_ne_zero p ha
    have hiff := irreducible_comp_linear_iff ((algebraMap ℤ_[p] ℚ_[p]) a) haQ
      ((algebraMap ℤ_[p] ℚ_[p]) c) ((affLift a c h).map (algebraMap ℤ_[p] ℚ_[p]))
    rw [affLift_map_comp, irreducible_C_mul_iff (pow_ne_zero _ haQ)] at hiff
    exact hiff.mp (F.irred h hh)
  data := fun g' hg' =>
    castData p (List.mem_map.mp hg').choose_spec.2
      (affData p a c ha (F.monic _ (List.mem_map.mp hg').choose_spec.1)
        (F.data _ (List.mem_map.mp hg').choose_spec.1))

/-- **The transported factorization has the SAME `qpType`.** -/
theorem qpType_translateFactorization (a c : ℤ_[p]) (ha : a ≠ 0) {f g : ℤ_[p][X]}
    (hrel : f.comp (C a * X + C c) = C (a ^ g.natDegree) * g)
    (F : QpType.QpFactorization p g) :
    QpType.qpType p (translateFactorization p a c ha hrel F) = QpType.qpType p F := by
  have hlist : (F.factors.map (affLift a c)).pmap
      (fun g' hg' => QpType.efOf p ((translateFactorization p a c ha hrel F).data g' hg'))
      (fun _ h => h)
    = F.factors.pmap (fun h hh => QpType.efOf p (F.data h hh)) (fun _ h => h) := by
    refine pmap_map_eq (affLift a c) F.factors _ _ _ _ ?_
    intro h hh h1 h2
    show QpType.efOf p (castData p (List.mem_map.mp h1).choose_spec.2
        (affData p a c ha (F.monic _ (List.mem_map.mp h1).choose_spec.1)
          (F.data _ (List.mem_map.mp h1).choose_spec.1)))
      = QpType.efOf p (F.data h h2)
    rw [efOf_castData, efOf_affData]
    exact efOf_data_congr p F
      (affLift_injective (F.monic _ (List.mem_map.mp h1).choose_spec.1) (F.monic h hh) ha c
        (List.mem_map.mp h1).choose_spec.2)
      _ _
  show (⟨((F.factors.map (affLift a c)).pmap
      (fun g' hg' => QpType.efOf p ((translateFactorization p a c ha hrel F).data g' hg'))
      (fun _ h => h) : List (ℕ × ℕ))⟩ : FactorizationType)
    = ⟨(F.factors.pmap (fun h hh => QpType.efOf p (F.data h hh)) (fun _ h => h) : List (ℕ × ℕ))⟩
  rw [hlist]

/-- **The [COUNT] translation lemma** (blueprint §2-W5c task A; note
`MATH_FULLTYPE_DECOMPOSITION` §1 "Canonical lifts" / §6): if
`f.comp (C a·X + C c) = C (a^{deg g})·g` — i.e. `g(y) = f(a·y + c)/a^{deg g}`, the
whole-window recenter–rescale at `a = p^m, c = ĉp^m`, or a pure translation at `a = 1` — then
every ℚ_p-factorization certificate of `g` transports to one of `f` with the SAME `qpType`.
Stated for arbitrary `a ≠ 0` and arbitrary degree (stronger than the `n = 2` need). -/
theorem qpType_translate_rescale (a c : ℤ_[p]) (ha : a ≠ 0) {f g : ℤ_[p][X]}
    (hrel : f.comp (C a * X + C c) = C (a ^ g.natDegree) * g)
    (F : QpType.QpFactorization p g) :
    ∃ F' : QpType.QpFactorization p f, QpType.qpType p F' = QpType.qpType p F :=
  ⟨translateFactorization p a c ha hrel F, qpType_translateFactorization p a c ha hrel F⟩

end Translate

/-! ## Block 5 — box→genuine digit decode toolkit -/

section Decode

variable (p : ℕ) [hp : Fact p.Prime]

/-- ℕ-cast of a remainder is the cast whenever the target modulus divides the remainder
modulus. -/
theorem natCast_mod_eq {M b : ℕ} (hMb : M ∣ b) (a : ℕ) :
    ((a % b : ℕ) : ZMod M) = (a : ZMod M) := by
  obtain ⟨t, rfl⟩ := hMb
  conv_rhs => rw [← Nat.mod_add_div a (M * t)]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- `val` of `p^k·x` at level `N`: the digits shift up by `k`, the top `k` digits truncate. -/
theorem val_pow_mul {N k : ℕ} (hk : k ≤ N) (x : ZMod (p ^ N)) :
    ((p : ZMod (p ^ N)) ^ k * x).val = p ^ k * (x.val % p ^ (N - k)) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have hx : ((p : ZMod (p ^ N)) ^ k * x) = ((p ^ k * x.val : ℕ) : ZMod (p ^ N)) := by
    push_cast
    rw [show ((x.val : ℕ) : ZMod (p ^ N)) = x from ZMod.natCast_rightInverse x]
  rw [hx, ZMod.val_natCast]
  generalize x.val = v
  rw [show p ^ N = p ^ k * p ^ (N - k) from by rw [← pow_add]; congr 1; omega,
    Nat.mul_mod_mul_left]

/-- **Genuine divisibility decode**: `p^k ∣ (toZModPow N z).val → p^k ∣ z` in `ℤ_[p]`
(`k ≤ N`). -/
theorem dvd_of_box_dvd {N k : ℕ} (hk : k ≤ N) {z : ℤ_[p]}
    (h : p ^ k ∣ (PadicInt.toZModPow N z).val) : (p : ℤ_[p]) ^ k ∣ z := by
  have hval : (((PadicInt.toZModPow N z).val : ℕ) : ZMod (p ^ N)) = PadicInt.toZModPow N z :=
    ZMod.natCast_rightInverse _
  have hker : z - (((PadicInt.toZModPow N z).val : ℕ) : ℤ_[p])
      ∈ RingHom.ker (PadicInt.toZModPow (p := p) N) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hval, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨u, hu⟩ := hker
  obtain ⟨t, ht⟩ := h
  have hz : z = ((p ^ k * t : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ N * u := by
    have hz0 : z = (((PadicInt.toZModPow N z).val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ N * u := by
      linear_combination hu
    rw [hz0, ht]
  rw [hz]
  refine dvd_add ⟨(t : ℤ_[p]), by push_cast; ring⟩
    (dvd_mul_of_dvd_left (pow_dvd_pow _ hk) u)

/-- **The shift decode**: the shifted box digits of `p^k·w`, read at any target level
`M ≤ N − k`, are the box of `w`. -/
theorem box_shift_cast {N k M : ℕ} (hk : k ≤ N) (hM : M ≤ N - k) (w : ℤ_[p]) :
    (((PadicInt.toZModPow N ((p : ℤ_[p]) ^ k * w)).val / p ^ k : ℕ) : ZMod (p ^ M))
      = PadicInt.toZModPow M w := by
  have hmap : PadicInt.toZModPow N ((p : ℤ_[p]) ^ k * w)
      = (p : ZMod (p ^ N)) ^ k * PadicInt.toZModPow N w := by
    rw [map_mul, map_pow, map_natCast]
  rw [hmap, val_pow_mul p hk, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k),
    natCast_mod_eq (pow_dvd_pow p hM)]
  have hMN : M ≤ N := le_trans hM (Nat.sub_le _ _)
  have hcomp := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow M N hMN) w
  rw [← hcomp, RingHom.comp_apply, ZMod.castHom_apply, ← ZMod.natCast_val]

/-- **Nonzero shifted digit forces a unit shift**: if the height-`k` digit of the box of
`p^k·w` is nonzero, then `p ∤ w` in `ℤ_[p]`. -/
theorem not_dvd_of_box_digit_ne {N k : ℕ} (hk : k + 1 ≤ N) {w : ℤ_[p]}
    (hd : CellCard.digit p N k (PadicInt.toZModPow N ((p : ℤ_[p]) ^ k * w)) ≠ 0) :
    ¬ (p : ℤ_[p]) ∣ w := by
  intro hdvd
  obtain ⟨w', rfl⟩ := hdvd
  refine hd ?_
  show (((PadicInt.toZModPow N ((p : ℤ_[p]) ^ k * ((p : ℤ_[p]) * w'))).val / p ^ k : ℕ)
    : ZMod p) = 0
  have hre : (p : ℤ_[p]) ^ k * ((p : ℤ_[p]) * w') = (p : ℤ_[p]) ^ (k + 1) * w' := by
    rw [pow_succ]
    ring
  rw [hre]
  have hmap : PadicInt.toZModPow N ((p : ℤ_[p]) ^ (k + 1) * w')
      = (p : ZMod (p ^ N)) ^ (k + 1) * PadicInt.toZModPow N w' := by
    rw [map_mul, map_pow, map_natCast]
  rw [hmap, val_pow_mul p hk, pow_succ,
    Nat.mul_comm (p ^ k) p, Nat.mul_assoc,
    Nat.mul_div_assoc p (Dvd.intro _ rfl)]
  · rw [Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k), Nat.cast_mul, ZMod.natCast_self,
      zero_mul]

end Decode

/-! ## Block 6 — the axiom-free depth-1 chain-gate anchor -/

section ChainGate

variable (p : ℕ) [hp : Fact p.Prime]

/-- Monic quadratic expansion. -/
theorem monic_quadratic_eq {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2) :
    f = X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' f (n := 3) (by omega)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    show f.coeff 2 = 1 from by rw [← hdeg]; exact hf.coeff_natDegree, Polynomial.C_1]
  ring

/-- **The chain-gate decode** (blueprint §2-W5c anchor step): a genuine monic quadratic in the
`ChainCell [1] (ram 1)` box fiber at level `N ≥ 4` yields a genuine recentered polynomial `g`
with `f(p·y + ĉp) = p²·g(y)`, and `g` satisfies the genuine EISENSTEIN conditions
(`v(g₀) = 1`, `g₁ ∈ (p)`) — the W1 wild-gate stratum conditions in the child frame,
axiom-free. -/
theorem chainGateFiber_decode {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.ram 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    ∃ (c₀ : ℤ_[p]) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C (p : ℤ_[p]) * X + C c₀) = C ((p : ℤ_[p]) ^ 2) * g ∧
      (g.coeff 0).valuation = 1 ∧ g.coeff 1 ∈ maximalIdeal ℤ_[p] := by
  -- unpack the fiber to the coefficient pair of the box
  have hcoeff : ∀ i, ((PadicLift.toBox p 2 N hN0 f hf hdeg).1).coeff i
      = PadicInt.toZModPow N (f.coeff i) := by
    intro i
    rw [PadicLift.toBox_val, Polynomial.coeff_map]
  have hfib' : ChainMenu.ChainPair p [1] (ChainMenu.ChainLeaf.ram 1) N N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)) := by
    have h := hfib
    unfold ChainMenu.ChainCell at h
    rwa [hcoeff 0, hcoeff 1] at h
  simp only [ChainMenu.ChainPair] at hfib'
  obtain ⟨c, hstep, hleaf⟩ := hfib'
  simp only [RecenterBox.StratumPair, RecenterBox.CoordCond] at hstep
  obtain ⟨⟨hd0, hdig0⟩, ⟨hd1, hdig1⟩⟩ := hstep
  -- genuine divisibility of the coefficients
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p (show 2 * 1 ≤ N by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show 1 ≤ N by omega) hd1
  -- the recentering digit and the genuine recentered coefficients
  set ĉ : ℕ := ((c : ZMod p)).val with hĉ
  set b₁ : ℤ_[p] := w₁ + 2 * (ĉ : ℤ_[p]) with hb₁
  set b₀ : ℤ_[p] := w₀ + (ĉ : ℤ_[p]) * w₁ + (ĉ : ℤ_[p]) ^ 2 with hb₀
  set g : ℤ_[p][X] := X ^ 2 + C b₁ * X + C b₀ with hgdef
  have hg : g.Monic := by
    rw [hgdef]
    monicity!
  have hgdeg : g.natDegree = 2 := by
    rw [hgdef]
    compute_degree!
  have hg0 : g.coeff 0 = b₀ := by
    rw [hgdef]
    simp
  have hg1 : g.coeff 1 = b₁ := by
    rw [hgdef]
    simp
  -- the composition identity
  have hrel : f.comp (C (p : ℤ_[p]) * X + C ((ĉ : ℤ_[p]) * p)) = C ((p : ℤ_[p]) ^ 2) * g := by
    conv_lhs => rw [monic_quadratic_eq p hf hdeg]
    rw [hw₀, hw₁, hgdef, hb₀, hb₁]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_add, map_mul, map_pow, map_ofNat]
    push_cast
    ring
  -- the leaf conditions transfer to the genuine recentered coefficients
  have hdesc : ChainMenu.descendPair p 1 ĉ
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))
      = (PadicInt.toZModPow (N - 2 * 1) b₀, PadicInt.toZModPow (N - 1) b₁) := by
    unfold ChainMenu.descendPair
    refine Prod.ext ?_ ?_
    · show ((((PadicInt.toZModPow N (f.coeff 0)).val / p ^ (2 * 1) : ℕ))
          : ZMod (p ^ (N - 2 * 1)))
        + (ĉ : ZMod (p ^ (N - 2 * 1)))
            * (((PadicInt.toZModPow N (f.coeff 1)).val / p ^ 1 : ℕ) : ZMod (p ^ (N - 2 * 1)))
        + (ĉ : ZMod (p ^ (N - 2 * 1))) ^ 2 = PadicInt.toZModPow (N - 2 * 1) b₀
      rw [hw₀, hw₁, box_shift_cast p (show 2 * 1 ≤ N by omega) (le_refl _),
        box_shift_cast p (show 1 ≤ N by omega) (show N - 2 * 1 ≤ N - 1 by omega),
        hb₀, map_add, map_add, map_mul, map_pow, map_natCast]
    · show (((PadicInt.toZModPow N (f.coeff 1)).val / p ^ 1 : ℕ) : ZMod (p ^ (N - 1)))
        + 2 * (ĉ : ZMod (p ^ (N - 1))) = PadicInt.toZModPow (N - 1) b₁
      rw [hw₁, box_shift_cast p (show 1 ≤ N by omega) (le_refl _),
        hb₁, map_add, map_mul, map_natCast, map_ofNat]
  rw [hdesc] at hleaf
  simp only [ChainMenu.LeafPair] at hleaf
  obtain ⟨⟨hlb0, hldig⟩, hlb1⟩ := hleaf
  -- decode the b₁ leg: p ∣ b₁
  have hb₁mem : b₁ ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    have hdd := dvd_of_box_dvd p (show (1 + 1) / 2 ≤ N - 1 by omega) hlb1
    rwa [show ((1 + 1) / 2 : ℕ) = 1 from rfl, pow_one] at hdd
  -- decode the b₀ leg: v(b₀) = 1
  obtain ⟨w', hw'⟩ : (p : ℤ_[p]) ∣ b₀ := by
    have := dvd_of_box_dvd p (show 1 ≤ N - 2 * 1 by omega) hlb0
    rwa [pow_one] at this
  have hnotdvd : ¬ (p : ℤ_[p]) ∣ w' := by
    refine not_dvd_of_box_digit_ne p (show 1 + 1 ≤ N - 2 * 1 by omega) ?_
    rw [pow_one, ← hw']
    exact hldig
  have hb₀ne : b₀ ≠ 0 := by
    intro h0
    refine hnotdvd ?_
    have hw'0 : w' = 0 := by
      have hpne : (p : ℤ_[p]) ≠ 0 := by
        exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
      have := h0 ▸ hw'
      exact (mul_eq_zero.mp this.symm).resolve_left hpne
    rw [hw'0]
    exact dvd_zero _
  have hval : b₀.valuation = 1 := by
    have h1le : 1 ≤ b₀.valuation := by
      refine (PadicInt.mem_span_pow_iff_le_valuation b₀ hb₀ne 1).mp ?_
      rw [pow_one, Ideal.mem_span_singleton]
      exact ⟨w', hw'⟩
    have hnot2 : ¬ 2 ≤ b₀.valuation := by
      intro h2
      have hmem := (PadicInt.mem_span_pow_iff_le_valuation b₀ hb₀ne 2).mpr h2
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨t, ht⟩ := hmem
      refine hnotdvd ⟨t, ?_⟩
      have hpne : (p : ℤ_[p]) ≠ 0 := by
        exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
      have : (p : ℤ_[p]) * w' = (p : ℤ_[p]) * ((p : ℤ_[p]) * t) := by
        rw [← hw', ht]
        ring
      exact mul_left_cancel₀ hpne this
    omega
  exact ⟨(ĉ : ℤ_[p]) * p, g, hg, hgdeg, hrel, by rw [hg0]; exact hval, by rw [hg1]; exact hb₁mem⟩

/-- **Anchor leg 1 (irreducibility)**: the depth-1 chain-gate fiber forces `f` IRREDUCIBLE over
ℚ_p — axiom-free, end-to-end (fiber → recentered Eisenstein → transport back along the affine
substitution). -/
theorem chainGate_irreducible {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.ram 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg)) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  obtain ⟨c₀, g, hg, hgdeg, hrel, hv0, hv1⟩ := chainGateFiber_decode p hN0 hN4 hf hdeg hfib
  have hgirr : Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p])) :=
    QpType.wildFiber_irreducible' p hg hgdeg hv0 hv1
  have hpQ : (algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p]) ≠ 0 := fun h0 =>
    (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero : (p : ℤ_[p]) ≠ 0)
      (IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h0, map_zero]))
  have hrelQ : (f.map (algebraMap ℤ_[p] ℚ_[p])).comp
      (C ((algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p])) * X + C ((algebraMap ℤ_[p] ℚ_[p]) c₀))
        = C (((algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p])) ^ 2)
            * g.map (algebraMap ℤ_[p] ℚ_[p]) := by
    have hmc := congrArg (Polynomial.map (algebraMap ℤ_[p] ℚ_[p])) hrel
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C, map_pow] at hmc
    exact hmc
  have hiff := irreducible_comp_linear_iff ((algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p])) hpQ
    ((algebraMap ℤ_[p] ℚ_[p]) c₀) (f.map (algebraMap ℤ_[p] ℚ_[p]))
  rw [hrelQ, irreducible_C_mul_iff (pow_ne_zero _ hpQ)] at hiff
  exact hiff.mp hgirr

/-- **Anchor leg 2 (the full (e,f) payload)**: the depth-1 chain-gate fiber forces
`efOf = (2, 1)` for EVERY `LocalFactorData` bundle on `f` — axiom-free (bundle transport to the
recentered Eisenstein `g` + `QpTypeEisenstein.ef_of_eisenstein`). This is the FULL semantic
anchor for the chain branch of the scope-#4 axiom: type `{(2,1)}` pinned in both coordinates. -/
theorem chainGate_ef_forced {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenu.ChainCell p [1] (ChainMenu.ChainLeaf.ram 1)
      (PadicLift.toBox p 2 N hN0 f hf hdeg))
    (D : QpType.LocalFactorData p f) :
    QpType.efOf p D = (2, 1) := by
  obtain ⟨c₀, g, hg, hgdeg, hrel, hv0, hv1⟩ := chainGateFiber_decode p hN0 hN4 hf hdeg hfib
  have hEis : g.IsEisensteinAt (maximalIdeal ℤ_[p]) :=
    QpType.isEisensteinAt_of_wildGate p hg hgdeg hv0 hv1
  set ρ : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hρ
  have hpQ : ρ (p : ℤ_[p]) ≠ 0 := fun h0 =>
    (by exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero : (p : ℤ_[p]) ≠ 0)
      (IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h0, map_zero]))
  have hrelQ : (f.map ρ).comp (C (ρ (p : ℤ_[p])) * X + C (ρ c₀))
      = C ((ρ (p : ℤ_[p])) ^ 2) * g.map ρ := by
    have hmc := congrArg (Polynomial.map ρ) hrel
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C, map_pow] at hmc
    exact hmc
  -- invert the affine substitution: (g.map).comp (C (ρp)⁻¹·X + C (−ρc₀/ρp)) = C (ρp²)⁻¹ · f.map
  set a' : ℚ_[p] := ρ (p : ℤ_[p]) with ha'
  set c' : ℚ_[p] := ρ c₀ with hc'
  have hqcomp : (C a' * X + C c').comp (C a'⁻¹ * X + C (-(c' / a')) : ℚ_[p][X]) = X := by
    rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hpQ, Polynomial.C_1, one_mul,
      ← Polynomial.C_mul, add_assoc, ← Polynomial.C_add]
    have : a' * -(c' / a') + c' = 0 := by field_simp; ring
    rw [this, Polynomial.C_0, add_zero]
  have hgQcomp : (g.map ρ).comp (C a'⁻¹ * X + C (-(c' / a')))
      = C ((a' ^ 2)⁻¹) * f.map ρ := by
    have hgeq : g.map ρ = C ((a' ^ 2)⁻¹) * (f.map ρ).comp (C a' * X + C c') := by
      rw [hrelQ, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero _ hpQ),
        Polynomial.C_1, one_mul]
    rw [hgeq, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc, hqcomp,
      Polynomial.comp_X]
  -- transport the bundle to g, where Eisenstein forces (e, f) = (2, 1)
  have hdeg2 : g.natDegree = f.natDegree := by rw [hgdeg, hdeg]
  have hef := QpTypeEisenstein.ef_of_eisenstein p hg hEis (by rw [hgdeg]; norm_num)
    (compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ) hdeg2 hgQcomp D)
  have hkey := efOf_compData p a'⁻¹ (-(c' / a')) ((a' ^ 2)⁻¹) (inv_ne_zero hpQ)
    hdeg2 hgQcomp D
  rw [← hkey]
  unfold QpType.efOf
  rw [hef.1, hef.2, hgdeg]

end ChainGate

/-! ## Block 7 — the chain-gate witness (`X² + 4` over `ℤ_[2]`, level `N = 4`) and the menu
membership of the chain-gate shape

`X² + 4` recentered at `x = 2 + 2y` is `(4 + 8y + 4y² + 4)/4 = y² + 2y + 2` — exactly the W1
gate witness `OmLeafFaithful.gatePoly`. Its box at `N = 4` is `X² + C 4` over `ZMod 16`:
stratum digits `v(a₀) = 2` exact with digit `1 = c̃²`, `v(a₁) ≥ 2` (`−2c̃ = 0` at `p = 2`),
leaf digits `v(b₀) = 1` exact, `v(b₁) ≥ 1` — the depth-1 `ram 1` chain stratum. -/

section Witness

/-- The chain-gate witness polynomial `X² + 4` over `ℤ_[2]`. -/
noncomputable def chainGatePoly : Polynomial ℤ_[2] := X ^ 2 + C 4

theorem chainGatePoly_monic : chainGatePoly.Monic := by
  unfold chainGatePoly
  monicity!

theorem chainGatePoly_natDegree : chainGatePoly.natDegree = 2 := by
  unfold chainGatePoly
  compute_degree!

/-- The box of the witness at level `4` is `X² + C 4` over `ZMod 16`. -/
theorem toBox_chainGatePoly :
    ((PadicLift.toBox 2 2 4 (by norm_num) chainGatePoly chainGatePoly_monic
      chainGatePoly_natDegree).1)
      = (X ^ 2 + C 4 : (ZMod (2 ^ 4))[X]) := by
  rw [PadicLift.toBox_val]
  unfold chainGatePoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_ofNat]

/-- **The chain-gate fiber is INHABITED**: the witness lies in the `ChainCell [1] (ram 1)`
fiber at `p = 2`, `N = 4` — so the scope-#4 chain instances of the axiom are not vacuous and
the mutation probes genuinely fire. -/
theorem chainGateFiber_nonempty :
    ChainMenu.ChainCell 2 [1] (ChainMenu.ChainLeaf.ram 1)
      (PadicLift.toBox 2 2 4 (by norm_num) chainGatePoly chainGatePoly_monic
        chainGatePoly_natDegree) := by
  unfold ChainMenu.ChainCell
  rw [toBox_chainGatePoly]
  have hc0 : (X ^ 2 + C 4 : (ZMod (2 ^ 4))[X]).coeff 0 = 4 := by
    simp
  have hc1 : (X ^ 2 + C 4 : (ZMod (2 ^ 4))[X]).coeff 1 = 0 := by
    simp
  rw [hc0, hc1]
  show ChainMenu.ChainPair 2 [1] (ChainMenu.ChainLeaf.ram 1) 4 4 ((4 : ZMod (2 ^ 4)), 0)
  refine ⟨1, ?_, ?_⟩
  · -- StratumPair 2 4 4 1 1 (4, 0)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · -- LeafPair (ram 1) in the frame (2, 3) on descendPair
    show ChainMenu.LeafPair 2 (ChainMenu.ChainLeaf.ram 1) (4 - 2 * 1) (4 - 1)
      (ChainMenu.descendPair 2 1 (((1 : (ZMod 2)ˣ) : ZMod 2)).val ((4 : ZMod (2 ^ 4)), 0))
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

end Witness

section Membership

/-- The depth-1 `ram 1` chain-gate shape is on the Wave-5 menu at `n = 2`, `σ = {(2,1)}`,
window `D = K = 1`. -/
theorem chainGate_mem_omMenu5 :
    ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.ram 1)
      ∈ ChainMenu.omMenu5 2 1 1 ChainMenu.ramType2 := by
  rw [ChainMenu.omMenu5, Finset.mem_union]
  right
  rw [ChainMenu.mem_chainShapes]
  refine ⟨rfl, [1], ChainMenu.ChainLeaf.ram 1, ?_, by simp, ?_, rfl⟩
  · rw [ChainMenu.mem_msMenu]
    refine ⟨by simp, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm
    omega
  · rw [ChainMenu.chainLeaves, if_pos rfl, Finset.mem_image]
    exact ⟨1, by rw [Finset.mem_Icc]; omega, by norm_num⟩

end Membership

/-! ## Block 7b — W5c mutation probe evidence (machine-checked 2026-07-22, scratch NOT
committed)

**The two W5c mutations at the depth-1 chain gate** — the re-scoped axiom's hypotheses
VERBATIM (over `ChainMenu.omMenu5` with `fiberOf5`), conclusion replaced by (A) the SPLIT type
`{(1,1),(1,1)}` and (B) the fine-(e,f)-swapped singleton `{(1,2)}` — were compiled against
this module and `OM/OmLeafFaithful.lean`, and `lake env lean` accepted the following scratch
with zero errors: `False` DERIVES from each mutated axiom + the inhabited chain-gate fiber
(`chainGateFiber_nonempty` / `OmLeafFaithful.chainGateFiber5_nonempty`) + THIS module's
AXIOM-FREE anchors (`chainGate_irreducible` for (A); `chainGate_ef_forced` +
`QpTypeEisenstein.qpType_singleton_forces` for (B)). The real `om_leaf_faithful` appears in
NEITHER refutation cone; the chain branch's `(e,f)` payload is pinned in both coordinates.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeChain

namespace LeanUrat.OM.QpTypeChainScratch

open Polynomial
open LeanUrat LeanUrat.OM

axiom om_leaf_faithful_MUTATED_chainsplit (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

theorem mutation_chainsplit_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_chainsplit 2 2 4 (by norm_num)
    ChainMenu.ramType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.ram 1)) 1 1
    QpTypeChain.chainGate_mem_omMenu5 QpTypeChain.chainGatePoly
    QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
    OmLeafFaithful.chainGateFiber5_nonempty
  have hirr : Irreducible (QpTypeChain.chainGatePoly.map (algebraMap ℤ_[2] ℚ_[2])) :=
    QpTypeChain.chainGate_irreducible 2 (by norm_num) (by norm_num)
      QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
      QpTypeChain.chainGateFiber_nonempty
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, g₂, hfac⟩ := List.length_eq_two.mp hlen
  have h1 : ¬ IsUnit (g₁.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₁ (by rw [hfac]; exact List.mem_cons_self ..)).not_isUnit
  have h2 : ¬ IsUnit (g₂.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₂ (by rw [hfac]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).not_isUnit
  have hmap : QpTypeChain.chainGatePoly.map (algebraMap ℤ_[2] ℚ_[2])
      = g₁.map (algebraMap ℤ_[2] ℚ_[2]) * g₂.map (algebraMap ℤ_[2] ℚ_[2]) := by
    rw [← F.prod_eq, hfac]
    simp [Polynomial.map_mul]
  rcases hirr.isUnit_or_isUnit hmap with h | h
  · exact h1 h
  · exact h2 h

axiom om_leaf_faithful_MUTATED_chainefswap (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

theorem mutation_chainefswap_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_chainefswap 2 2 4 (by norm_num)
    ChainMenu.ramType2 (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.ram 1)) 1 1
    QpTypeChain.chainGate_mem_omMenu5 QpTypeChain.chainGatePoly
    QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
    OmLeafFaithful.chainGateFiber5_nonempty
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((1 : ℕ), (2 : ℕ)) hF
  have hef2 : QpType.efOf 2 (F.data QpTypeChain.chainGatePoly hmem) = (2, 1) :=
    QpTypeChain.chainGate_ef_forced 2 (by norm_num) (by norm_num)
      QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
      QpTypeChain.chainGateFiber_nonempty (F.data QpTypeChain.chainGatePoly hmem)
  rw [hef] at hef2
  exact absurd hef2 (by decide)

end LeanUrat.OM.QpTypeChainScratch

#print axioms LeanUrat.OM.QpTypeChainScratch.mutation_chainsplit_refuted
#print axioms LeanUrat.OM.QpTypeChainScratch.mutation_chainefswap_refuted
```

`lake env lean` output on the scratch (2026-07-22): NO errors; exactly the two info lines

```
'LeanUrat.OM.QpTypeChainScratch.mutation_chainsplit_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainScratch.om_leaf_faithful_MUTATED_chainsplit]
'LeanUrat.OM.QpTypeChainScratch.mutation_chainefswap_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeChainScratch.om_leaf_faithful_MUTATED_chainefswap]
```

i.e. `False` follows from each MUTATED axiom + Lean core + PROVED theorems alone — the real
`om_leaf_faithful` appears in neither cone. -/

/-! ## Block 8 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeChain.affLift_comp
#print axioms LeanUrat.OM.QpTypeChain.affLift_monic
#print axioms LeanUrat.OM.QpTypeChain.affLift_natDegree
#print axioms LeanUrat.OM.QpTypeChain.affLift_injective
#print axioms LeanUrat.OM.QpTypeChain.comp_linear_injective
#print axioms LeanUrat.OM.QpTypeChain.irreducible_comp_linear_iff
#print axioms LeanUrat.OM.QpTypeChain.irreducible_C_mul_iff
#print axioms LeanUrat.OM.QpTypeChain.compData
#print axioms LeanUrat.OM.QpTypeChain.efOf_compData
#print axioms LeanUrat.OM.QpTypeChain.translateFactorization
#print axioms LeanUrat.OM.QpTypeChain.qpType_translateFactorization
#print axioms LeanUrat.OM.QpTypeChain.qpType_translate_rescale
#print axioms LeanUrat.OM.QpTypeChain.dvd_of_box_dvd
#print axioms LeanUrat.OM.QpTypeChain.box_shift_cast
#print axioms LeanUrat.OM.QpTypeChain.not_dvd_of_box_digit_ne
#print axioms LeanUrat.OM.QpTypeChain.chainGateFiber_decode
#print axioms LeanUrat.OM.QpTypeChain.chainGate_irreducible
#print axioms LeanUrat.OM.QpTypeChain.chainGate_ef_forced
#print axioms LeanUrat.OM.QpTypeChain.chainGatePoly
#print axioms LeanUrat.OM.QpTypeChain.toBox_chainGatePoly
#print axioms LeanUrat.OM.QpTypeChain.chainGateFiber_nonempty
#print axioms LeanUrat.OM.QpTypeChain.chainGate_mem_omMenu5

end AxCheck

end LeanUrat.OM.QpTypeChain
