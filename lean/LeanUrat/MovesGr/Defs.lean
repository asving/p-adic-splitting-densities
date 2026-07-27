/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL

/-!
# MovesGr/Defs — the genuine graded ring `gr_w(A)` for the §B2-DEF tower (R5.3 boundary)

**Provenance.** Discharges the STANDING BOUNDARY recorded in
`lean/notes/MOVES_LEAN_BLUEPRINT_2026-07-26.md` §R5.3 and the "definitional façade" objection of
`lean/notes/MOVES_LEAN_SEMAUDIT5_2026-07-26.md`: the round-5 `Stage.grRes`
(`DefsL.lean`) is defined BACKWARDS from the residual data `σ.R`, so it certifies formal `LTwo`
objects rather than a genuine graded localization. This file constructs the real objects of
§B2-DEF D.1(a)-(e), from which `σ.grRes` is a THEOREM (the fiat discharged).

Design doc + DAG + mathlib-reuse report + honest gaps:
`lean/notes/MOVESGR_LEAN_BLUEPRINT_2026-07-26.md`. Machine-checkable statement list:
`lean/LeanUrat/MovesGr/MANIFEST.json`. This file is DEFINITIONS + validated structural lemmas
ONLY — no `sorry`, no axioms (`lake env lean` clean); the graded ring/localization/iso PROOFS are
the ~24 MANIFEST units.

## The construction (D.1(a)-(e), taken literally)

* **The side valuation** is bundled as `SideVal p` (`w : A → WithTop ℤ` with the ultrametric +
  submultiplicative + scalar laws; `A = ℤ_[p][X]`). A `Stage`'s own `σ.w` (extended by `0 ↦ ⊤`)
  is such a bundle — the graded ring is built from `σ`'s OWN valuation, not from `σ.R`.
* **The side filtration** `A_{≥γ} = {f | γ ≤ w f}` / `A_{>γ} = {f | γ < w f}` are honest
  `ℤ_[p]`-submodules (`ge`/`gt`); `grPiece γ := A_{≥γ}/A_{>γ}` is the degree-`γ` piece and
  `Gr := ⊕_γ grPiece γ` (`DirectSum`) is `gr_w(A)` (D.1). The multiplication `pmul` on pieces is
  INDUCED FROM `A`'s multiplication (via `LinearMap.liftQ₂`), the genuine content D.1(a) — NOT
  read off `σ.R`. `initialForm f := [f]` in degree `deg f` is the genuine initial-form map.
* **`GradedRingStr S`** packages the graded commutative RING structure on `Gr` whose product
  restricts to `pmul` (`mul_of`) with `initialForm` multiplicative (`if_mul`, D.1(c) — the
  domain/valuation content) and additive ties (D.1(b)). Constructed by the L1 units.
* **`GenuineStageModel σ`** is the R5.3 (1)-(4) bundle: the `SideVal` built from `σ.w`, the graded
  ring, the homogeneous LOCALIZATION `L` at `⟨U ∪ {Y}⟩` (mathlib `IsLocalization`), a
  degree-1 unit `T`, the D.1(e) ring iso `Θ : L ≅ L₀[T^{±1}] = LTwo ↥σ.K`, and the FIAT DISCHARGE
  `discharge : Θ(ι[f]) = σ.grRes f` — the exact identification audit #5 §7 said the signatures
  lacked. `L₀ ≅ ↥σ.K[z^{±1}]` is the last standing fiat (`hL0`), now an explicit hypothesis of the
  bundle rather than a silent codomain choice.

Every definition here is flagged for semantic-guardian review (the trust boundary). The honest
gaps (what is still bundled rather than derived) are §5 of the blueprint.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.MovesGr

open Polynomial LeanUrat.Moves

/-! ## 1. Side valuations and the side filtration -/

/-- A **side valuation** on `A = ℤ_[p][X]`: `w : A → WithTop ℤ` (value `⊤` at `0`), ultrametric,
submultiplicative, with scalars not decreasing weight. This is the D.1 hypothesis package;
a genuine OM-stage's `σ.w` (extended by `0 ↦ ⊤`) is an instance (built by the L1 units). -/
structure SideVal (p : ℕ) [Fact p.Prime] where
  /-- the extended valuation (`⊤` marks `0`) -/
  w : Polynomial ℤ_[p] → WithTop ℤ
  w_zero : w 0 = ⊤
  w_ne_top : ∀ f, f ≠ 0 → w f ≠ ⊤
  w_neg : ∀ f, w (-f) = w f
  w_add : ∀ f g, min (w f) (w g) ≤ w (f + g)
  w_smul : ∀ (c : ℤ_[p]) f, w f ≤ w (Polynomial.C c * f)
  w_mul : ∀ f g, w f + w g ≤ w (f * g)
  w_one : w 1 = 0

namespace SideVal

/-- The integer degree `deg f := untop of w f` (`0` at `f = 0`). -/
noncomputable def deg {p : ℕ} [Fact p.Prime] (S : SideVal p) (f : Polynomial ℤ_[p]) : ℤ := (S.w f).untopD 0

lemma coe_deg_le {p : ℕ} [Fact p.Prime] (S : SideVal p) (f : Polynomial ℤ_[p]) :
    (↑(S.deg f) : WithTop ℤ) ≤ S.w f := by
  unfold deg; cases h : S.w f with
  | top => simp
  | coe n => simp

lemma deg_eq {p : ℕ} [Fact p.Prime] (S : SideVal p) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    (↑(S.deg f) : WithTop ℤ) = S.w f := by
  unfold deg; cases h : S.w f with
  | top => exact absurd h (S.w_ne_top f hf)
  | coe n => simp

/-- The submodule `A_{≥γ} = {f : γ ≤ w f}` (D.1). -/
noncomputable def ge {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ : ℤ) : Submodule ℤ_[p] (Polynomial ℤ_[p]) where
  carrier := {f | (γ : WithTop ℤ) ≤ S.w f}
  zero_mem' := by simp [S.w_zero]
  add_mem' := by intro a b ha hb; exact le_trans (le_min ha hb) (S.w_add a b)
  smul_mem' := by
    intro c a ha
    have h : c • a = Polynomial.C c * a := by simp [Polynomial.smul_eq_C_mul]
    rw [h]; exact le_trans ha (S.w_smul c a)

/-- The submodule `A_{>γ} = {f : γ < w f}` (D.1). -/
noncomputable def gt {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ : ℤ) : Submodule ℤ_[p] (Polynomial ℤ_[p]) where
  carrier := {f | (γ : WithTop ℤ) < S.w f}
  zero_mem' := by simp [S.w_zero]
  add_mem' := by intro a b ha hb; exact lt_of_lt_of_le (lt_min ha hb) (S.w_add a b)
  smul_mem' := by
    intro c a ha
    have h : c • a = Polynomial.C c * a := by simp [Polynomial.smul_eq_C_mul]
    rw [h]; exact lt_of_lt_of_le ha (S.w_smul c a)

/-- `A_{>γ}` viewed inside `A_{≥γ}` (the relation defining the degree-`γ` quotient). -/
noncomputable def gtIn {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ : ℤ) : Submodule ℤ_[p] (S.ge γ) :=
  (S.gt γ).comap (S.ge γ).subtype

/-- The **degree-`γ` graded piece** `gr_γ(A) = A_{≥γ}/A_{>γ}` (D.1). -/
abbrev grPiece {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ : ℤ) : Type _ :=
  (S.ge γ) ⧸ (S.gtIn γ)

/-- The **associated graded ring** `gr_w(A) = ⊕_γ A_{≥γ}/A_{>γ}` (D.1), as an additive group; the
graded commutative ring structure whose product restricts to `pmul` is packaged in
`GradedRingStr` and built by the L1 units. -/
abbrev Gr {p : ℕ} [Fact p.Prime] (S : SideVal p) : Type _ :=
  DirectSum ℤ (fun γ => S.grPiece γ)

/-- Multiplication `A_{≥γ} × A_{≥δ} → A_{≥γ+δ}`, `(a,b) ↦ a·b`, as a `ℤ_[p]`-bilinear map — the
raw source of the graded multiplication (submultiplicativity gives the target membership). -/
noncomputable def mulToGe {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ δ : ℤ) :
    S.ge γ →ₗ[ℤ_[p]] S.ge δ →ₗ[ℤ_[p]] S.ge (γ + δ) where
  toFun a := {
    toFun := fun b => ⟨(a : Polynomial ℤ_[p]) * (b : Polynomial ℤ_[p]), by
      have hle : (γ : WithTop ℤ) + (δ : WithTop ℤ) ≤ S.w ((a : Polynomial ℤ_[p]) * b) :=
        le_trans (add_le_add a.2 b.2) (S.w_mul _ _)
      show (↑(γ + δ) : WithTop ℤ) ≤ _; rw [WithTop.coe_add]; exact hle⟩
    map_add' := by intro x y; ext; simp [mul_add]
    map_smul' := by intro c x; ext; simp }
  map_add' := by intro x y; ext b; simp [add_mul]
  map_smul' := by intro c x; ext b; simp

/-- The **genuine graded multiplication on pieces** `gr_γ × gr_δ → gr_{γ+δ}`, `[a]·[b] = [a·b]`,
descended from `A`'s multiplication through both quotients (well-defined by submultiplicativity:
raising the weight of either factor raises the product's weight). This is D.1(a) — the product is
induced from `A`, NOT read off `σ.R` (the exact point of audit #5). -/
noncomputable def pmul {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ δ : ℤ) :
    S.grPiece γ →ₗ[ℤ_[p]] S.grPiece δ →ₗ[ℤ_[p]] S.grPiece (γ + δ) :=
  ((S.mulToGe γ δ).compr₂ (S.gtIn (γ + δ)).mkQ).liftQ₂ (S.gtIn γ) (S.gtIn δ)
    (by
      intro a ha
      rw [LinearMap.mem_ker]; ext b
      simp only [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      have haw : (γ : WithTop ℤ) < S.w (a : Polynomial ℤ_[p]) := ha
      show (↑(γ + δ) : WithTop ℤ) < S.w ((a : Polynomial ℤ_[p]) * (b : Polynomial ℤ_[p]))
      rw [WithTop.coe_add]
      exact lt_of_lt_of_le (WithTop.add_lt_add_of_lt_of_le WithTop.coe_ne_top haw b.2) (S.w_mul _ _))
    (by
      intro b hb
      rw [LinearMap.mem_ker]; ext a
      simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      have hbw : (δ : WithTop ℤ) < S.w (b : Polynomial ℤ_[p]) := hb
      show (↑(γ + δ) : WithTop ℤ) < S.w ((a : Polynomial ℤ_[p]) * (b : Polynomial ℤ_[p]))
      rw [WithTop.coe_add]
      exact lt_of_lt_of_le (WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top a.2 hbw) (S.w_mul _ _))

/-- The class `[f] ∈ gr_{deg f}(A)` of `f` in its own degree-`γ` piece (`γ = deg f`). -/
noncomputable def mkPiece {p : ℕ} [Fact p.Prime] (S : SideVal p) (f : Polynomial ℤ_[p]) : S.grPiece (S.deg f) :=
  Submodule.Quotient.mk ⟨f, S.coe_deg_le f⟩

/-- The **genuine initial-form map** `[·] : A → gr_w(A)`, `f ↦ [f]` placed in degree `deg f`
(D.1(a)-(b)). This is the map audit #5 said `Stage.grRes` should have been built from. -/
noncomputable def initialForm {p : ℕ} [Fact p.Prime] (S : SideVal p) (f : Polynomial ℤ_[p]) : S.Gr :=
  DirectSum.of (fun γ => S.grPiece γ) (S.deg f) (S.mkPiece f)

end SideVal

/-! ## 2. The residual codomain `L₀[T^{±1}]` (matching `DefsL.LTwo`) -/

/-- The D.1(e) target ring `L₀[T^{±1}]` with the codomain fiat `L₀ = K[z^{±1}]`; DEFINITIONALLY
`DefsL.LTwo K = LaurentPolynomial (LaurentPolynomial K)`, so the fiat-discharge equation lands in
the SAME type as `Stage.grRes`. -/
abbrev LExt (K : Type*) [Field K] : Type _ := LeanUrat.Moves.LTwo K

/-! ## 3. The graded RING structure bundle (D.1(a)-(c)) -/

/-- **The graded commutative ring structure on `gr_w(A)`** (D.1(a)-(c)), as a bundle to be
CONSTRUCTED by the base and transported: a `CommRing` on `Gr` whose product restricts to `pmul`
on homogeneous pieces (`mul_of` — so the ring is the GENUINE one induced from `A`, not an
arbitrary structure), with `initialForm` sending `1 ↦ 1` (`one_def`) and MULTIPLICATIVE
(`if_mul`, D.1(c): `[fg] = [f][g]`, equivalently `w` is a valuation and `gr` a domain), and the
D.1(b) additive tie (`if_add_lt`: strictly-lower weight wins). Non-vacuity of the whole tower
rests on the L1 units inhabiting this for the base stage. -/
structure GradedRingStr {p : ℕ} [Fact p.Prime] (S : SideVal p) where
  /-- the commutative ring structure on `gr_w(A)` -/
  ring : CommRing S.Gr
  /-- the additive structure is the DirectSum's — D.1 makes gr's additive group part of
  the DEFINITION; only the multiplication is new structure. Stated COMPONENTWISE (the
  DirectSum addition IS the componentwise one, and DirectSum elements are equal iff all
  components are): a Gr-level `x + y` RHS would silently re-read the ambient `ring`
  field's `+` and state a tautology (machine-checked; blueprint §8.4). -/
  add_def : ∀ (x y : S.Gr) (γ : ℤ), (letI := ring; x + y) γ = x γ + y γ
  /-- the product restricts to the genuine piece multiplication `pmul` (D.1(a)) -/
  mul_of : letI := ring; ∀ (γ δ : ℤ) (x : S.grPiece γ) (y : S.grPiece δ),
      DirectSum.of _ γ x * DirectSum.of _ δ y = DirectSum.of _ (γ + δ) (S.pmul γ δ x y)
  /-- the unit is the initial form of `1` -/
  one_def : letI := ring; (1 : S.Gr) = S.initialForm 1
  /-- (D.1(c)) `[·]` is multiplicative — the valuation/domain content -/
  if_mul : letI := ring; ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 →
      S.initialForm (f * g) = S.initialForm f * S.initialForm g
  /-- (D.1(b)) the additive tie: a strictly lower weight dominates -/
  if_add_lt : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      S.deg f < S.deg g → S.initialForm (f + g) = S.initialForm f

/-! ## 4. The R5.3 (1)-(4) bundle: `GenuineStageModel` — the fiat DISCHARGED -/

section Model
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The genuine graded model of a stage** `σ` — the object audit #5 §7 said the theorem
signatures must contain. Its inhabitation for the base and its transport through TRANS /
recentering is exactly what makes `L1.baseStage_exists`, `L4.TRANSvi`, `L4.TRANSstage`,
`L5.recTRANSRS` non-vacuous. Fields, in the R5.3 order:

* `S`, `hSw` — **(1a)** the associated graded is built from `σ`'s OWN valuation `σ.w`
  (extended by `0 ↦ ⊤`), NOT from `σ.R`;
* `Rg` — **(1b)** `gr_w(A)` is a graded commutative ring / domain, `[·]` the genuine initial form;
* `homMon`, `Lo`, `Loring`, `alg`, `isLoc` — **(2)** the homogeneous LOCALIZATION
  `L = gr[⟨U ∪ {Y}⟩⁻¹]` (mathlib `IsLocalization` at the submonoid `homMon` generated by the
  initial forms of the representatives `σ.reps` and the key `σ.Φ`);
* `Tunit`, `hT` — **(3)** the degree-1 unit `T ∈ L` (D.1(e));
* `Θ`, `hL0` — **(3)-(4a)** the D.1(e) ring iso `Θ : L ≅ L₀[T^{±1}] = LTwo ↥σ.K` (`L₀ = K[z^{±1}]`
  is the last standing fiat, an EXPLICIT hypothesis `hL0` here, not a silent codomain choice);
* `discharge` — **(4b)** the fiat discharged: `Θ(ι[f]) = σ.grRes f` for every `f ≠ 0`. Since
  `σ.grRes f = C(σ.R f)·T^{w f}` (DefsL) and `T = locT`, this is exactly D.1(e)'s
  `Θ([f]·T^{−w f}) = σ.R f`, i.e. `(σ.w, σ.R)` ARE `x ↦ ([x], deg)` composed with the genuine
  structure — no residual is ever read backwards. -/
structure GenuineStageModel (σ : Stage p F) where
  /-- (1a) the side valuation of the graded ring -/
  S : SideVal p
  /-- gr is built from `σ`'s own valuation -/
  hSw : ∀ f, f ≠ 0 → S.w f = (σ.w f : WithTop ℤ)
  /-- (1b) the graded ring / domain structure -/
  Rg : GradedRingStr S
  /-- (2) the homogeneous multiplicative set `⟨U ∪ {Y}⟩` -/
  homMon : letI := Rg.ring; Submonoid S.Gr
  /-- `homMon` is generated by the initial forms of the representatives and the key -/
  homMon_gen : letI := Rg.ring;
      homMon = Submonoid.closure
        ((fun ũ => S.initialForm ũ) '' {ũ | ũ ∈ σ.reps} ∪ {S.initialForm σ.Φ})
  /-- (2) the localization ring `L` -/
  Lo : Type
  Loring : CommRing Lo
  alg : letI := Rg.ring; Algebra S.Gr Lo
  isLoc : letI := Rg.ring; letI := alg; IsLocalization homMon Lo
  /-- (3) the degree-1 unit `T ∈ L` -/
  Tunit : letI := Loring; Loˣ
  /-- (3)-(4a) the D.1(e) ring iso `Θ : L ≅ L₀[T^{±1}]`; the target is `LTwo ↥σ.K` -/
  Θ : letI := Loring; Lo ≃+* LExt ↥σ.K
  /-- `T` maps to the outer Laurent variable `locT` — the degree-1 normalizing unit of D.1(e) -/
  hT : letI := Loring; Θ (Tunit : Lo) = (LeanUrat.Moves.locT ↥σ.K : LeanUrat.Moves.LTwo ↥σ.K)
  /-- (4b) the FIAT DISCHARGED: `Θ(ι[f]) = σ.grRes f` (D.1(e)'s `Θ([f]·T^{−w f}) = σ.R f`) -/
  discharge : letI := Rg.ring; letI := alg; ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      Θ (algebraMap S.Gr Lo (S.initialForm f)) = σ.grRes f

end Model

end LeanUrat.MovesGr
