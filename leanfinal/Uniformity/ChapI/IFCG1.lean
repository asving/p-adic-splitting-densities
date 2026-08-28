/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC7
import Uniformity.ChapH.H123a

/-!
# Uniformity.ChapI.IFCG1 — [A0G2 2026-08-28] the degree-generic coefficient boxes (node A0G-CV)

**Uniform-a0 campaign, NODE A0G-CV** (`docs/in-progress/A0_GENERAL_2026-08-28.md` §§3.2–3.3 and
the §6 A0G-CV row): the degree-generic recentring vector `shiftVecN`, the degree-generic
mixed-precision box `MBoxN` with its truncation `mtruncN`, the translation bijections at the
vector and the class level, and the EXACT box cardinalities.  The degree-3 models being
generalized are `H97r1.shiftVec` (with `typeOf_shiftVec`, `shiftVec_shiftVec_neg`,
`dvd_shiftVec_sub`), `H97r3`'s `MBox`/`mtrunc`/`mkBox`/`card_mbox`/`card_preimage_mtrunc`, and
IFC7 §1's cube-frame translations; the degree-2 model is IFC7 §4's `shiftVec2`.

**DEDUP DISCIPLINE.**  A degree-generic recentring ALREADY LANDED at H.123a
(`Uniformity.Density.Induction.recentreVec`, with `monicPoly_recentreVec`,
`recentreVec_recentreVec`, `proj_recentreVec_congr`, and the class-level `recentreClass` bank).
This file does NOT redefine it: `shiftVecN` is a reducible wrapper over
`Induction.recentreVec` (`shiftVecN_def` is `rfl`), and every H.123a lemma is consumed as-is.
NEW here is everything the A0G-CV row asks for beyond H.123a:

* the group law (`shiftVecN_zero`, `shiftVecN_add`) and the bundled translation bijections
  `shiftEquivN` (vector level) and `coeffShiftEquivN` (level-`N` class level, wrapping the
  landed `recentreClass`);
* the `typeOf` invariance `typeOf_shiftVecN` — the mandated direct consumption of the landed
  `typeOf_shift` (HYP.05);
* the divisibility transport `dvd_shiftVecN_sub` — the degree-generic
  `H97r1.dvd_shiftVec_sub`, proved for an ARBITRARY modulus `d` (no irreducibility needed:
  it is a ring identity through the finite-sum decomposition of `monicPoly a' - monicPoly a`);
* the explicit coefficient law `shiftVecN_apply` (binomial/Hasse-derivative form) and the
  evaluation pins `shiftVecN_coeff_zero`/`shiftVecN_coeff_one` (`F(γ)`, `F′(γ)` — the generic
  forms of `shiftVec_zero`/`shiftVec_one`);
* the generic certificate transport `decidedAt_of_shiftVecN_cert` (the degree-generic
  `H97r3.decidedAt_of_shift_cert`, with an arbitrary certificate depth `k ≤ M`);
* **the degree-generic mixed-precision box** `MBoxN O n M := (i : Fin n) → Res O (M + i)`
  (the size-`m` cluster extraction `X = πY` pins coordinate `i` to precision `M + i` — at
  `n = 3` this is exactly H97r3's `MBox`), with `mtruncN`, `mkBoxN`, surjectivity, the record
  laws, and the EXACT cardinalities
  `#(MBoxN O n M) = q ^ (n*M + n*(n-1)/2)` (`card_MBoxN`) and the fibre law
  `#(mtruncN⁻¹ S) = #S · q ^ (n*(n-1)/2)` (`card_preimage_mtruncN_eq`) — the `n(n-1)/2` is
  the `κ_m = m(m-1)/2` coefficient loss of §3.2 of the A0 plan;
* **the n = 2, 3 recovery bank** (the gate): `shiftVecN_three` recovers `H97r1.shiftVec`,
  `shiftVecN_two` recovers `IFC7.shiftVec2` (both through `monicPoly`-injectivity against the
  landed `monicPoly_shiftVec`/`monicPoly_shiftVec2`); `mboxEquivThree` identifies
  `MBoxN O 3 M` with H97r3's `MBox O M`, `mboxEquivThree_mkBoxN` is `rfl` (the definitional
  instantiation), `mtrunc_mboxEquivThree` recovers `mtrunc`, and the cardinality pins
  `card_MBoxN_two`/`card_MBoxN_three` machine-check the exponents `2M+1` and `3M+3` (the
  latter = the landed `card_mbox` exponent).

**GATE (A0G-CV row).**  No `Fin 3` (or any fixed-degree type) appears in any signature of
§§1–4 (the generic API); fixed degrees occur ONLY in §5, the mandated recovery statements
themselves.  `typeOf_shift` is consumed directly (in `typeOf_shiftVecN`).

**⚠ TRUST BOUNDARY.**  Every `theorem` here is NEW and flagged for the standing review;
zero `sorry`, zero new axiom intended; AxCheck footer expects Lean core only.  No landed file
is touched; every landed name is consumed as-is.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG1

open IsLocalRing Polynomial

/-! ## §0 Prelude: `monicPoly` injectivity and the trivial truncation -/

section Prelude

variable {O : Type*} [CommRing O] [IsDomain O]

/-- **`monicPoly` is injective on coefficient vectors** — the reconstruction principle behind
every recovery lemma below (`monicPoly_coeff_lt` reads the vector back off the polynomial). -/
theorem monicPoly_injective {n : ℕ} :
    Function.Injective (monicPoly (O := O) (n := n)) := by
  intro a b h
  funext i
  have ha := monicPoly_coeff_lt a i.isLt
  have hb := monicPoly_coeff_lt b i.isLt
  simp only [Fin.eta] at ha hb
  rw [← ha, ← hb, h]

end Prelude

section Prelude2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Truncation from a level to itself is the identity. -/
theorem resFactor_self {N : ℕ} (h : N ≤ N) (x : Res O N) :
    resFactor (O := O) h x = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end Prelude2

/-! ## §1 The degree-generic recentring `shiftVecN`

`shiftVecN a γ` is the coefficient vector of `F_a(X + γ)` at every degree `n` — DEFINITIONALLY
the landed `Induction.recentreVec` (H.123a); the new content is the algebra of translations. -/

section ShiftVec

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The degree-generic recentred coefficient vector** (node A0G-CV, candidate name from the
A0 plan §6).  Reducible wrapper over the LANDED `Induction.recentreVec` (H.123a) — consumed,
not duplicated. -/
abbrev shiftVecN {n : ℕ} (a : Fin n → O) (γ : O) : Fin n → O :=
  Induction.recentreVec a γ

theorem shiftVecN_def {n : ℕ} (a : Fin n → O) (γ : O) (i : Fin n) :
    shiftVecN a γ i = ((monicPoly a).comp (X + C γ)).coeff (i : ℕ) := rfl

/-- **Recentring is the substitution `X ↦ X + γ`** (landed `Induction.monicPoly_recentreVec`,
in the campaign name). -/
theorem monicPoly_shiftVecN {n : ℕ} (a : Fin n → O) (γ : O) :
    monicPoly (shiftVecN a γ) = (monicPoly a).comp (X + C γ) :=
  Induction.monicPoly_recentreVec a γ

/-- **Recentring does not change the splitting type at any degree** — the direct consumption
of the landed `typeOf_shift` (HYP.05) mandated by the A0G-CV row. -/
theorem typeOf_shiftVecN {n : ℕ} (a : Fin n → O) (γ : O) :
    typeOf (monicPoly (shiftVecN a γ)) = typeOf (monicPoly a) := by
  rw [monicPoly_shiftVecN]
  exact typeOf_shift (monicPoly_monic a) γ

/-- Recentring at `0` is the identity. -/
theorem shiftVecN_zero {n : ℕ} (a : Fin n → O) : shiftVecN a 0 = a := by
  refine monicPoly_injective ?_
  rw [monicPoly_shiftVecN, map_zero, add_zero, comp_X]

/-- **The translation group law**: recentring at `γ` then at `δ` is recentring at `γ + δ`. -/
theorem shiftVecN_add {n : ℕ} (a : Fin n → O) (γ δ : O) :
    shiftVecN (shiftVecN a γ) δ = shiftVecN a (γ + δ) := by
  refine monicPoly_injective ?_
  rw [monicPoly_shiftVecN, monicPoly_shiftVecN, monicPoly_shiftVecN, comp_assoc]
  congr 1
  simp only [add_comp, X_comp, C_comp, map_add]
  ring

/-- **Recentring is invertible** (landed `Induction.recentreVec_recentreVec`, campaign name). -/
theorem shiftVecN_shiftVecN_neg {n : ℕ} (a : Fin n → O) (γ : O) :
    shiftVecN (shiftVecN a γ) (-γ) = a :=
  Induction.recentreVec_recentreVec a γ

/-- **The vector-level translation bijection** at every degree. -/
def shiftEquivN {n : ℕ} (γ : O) : (Fin n → O) ≃ (Fin n → O) where
  toFun a := shiftVecN a γ
  invFun a := shiftVecN a (-γ)
  left_inv a := shiftVecN_shiftVecN_neg a γ
  right_inv a := by
    have h := shiftVecN_shiftVecN_neg a (-γ)
    rwa [neg_neg] at h

theorem shiftEquivN_apply {n : ℕ} (γ : O) (a : Fin n → O) :
    shiftEquivN γ a = shiftVecN a γ := rfl

/-- **Recentring preserves divisibility of coefficient differences by an ARBITRARY modulus**
(the degree-generic `dvd_shiftVec_sub`; the modulus `π ^ N` of the models is the special case).
A ring identity: `F_{a'} − F_a = Σ_j C(a'_j − a_j)·X^j`, and composition with `X + C γ` keeps
every coefficient in the ideal generated by the `a'_j − a_j`. -/
theorem dvd_shiftVecN_sub {n : ℕ} {d : O} {a a' : Fin n → O} (γ : O)
    (h : ∀ i, d ∣ (a' i - a i)) :
    ∀ i, d ∣ (shiftVecN a' γ i - shiftVecN a γ i) := by
  intro i
  have hsub : monicPoly a' - monicPoly a = ∑ j : Fin n, C (a' j - a j) * X ^ (j : ℕ) := by
    calc monicPoly a' - monicPoly a
        = (∑ j : Fin n, C (a' j) * X ^ (j : ℕ)) - ∑ j : Fin n, C (a j) * X ^ (j : ℕ) := by
          simp only [monicPoly]; ring
      _ = ∑ j : Fin n, (C (a' j) * X ^ (j : ℕ) - C (a j) * X ^ (j : ℕ)) := by
          rw [← Finset.sum_sub_distrib]
      _ = ∑ j : Fin n, C (a' j - a j) * X ^ (j : ℕ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← sub_mul, ← C_sub]
  have hdiff : shiftVecN a' γ i - shiftVecN a γ i
      = ∑ j : Fin n, (a' j - a j) * (((X + C γ) ^ (j : ℕ)).coeff (i : ℕ)) := by
    rw [shiftVecN_def, shiftVecN_def, ← coeff_sub, ← sub_comp, hsub, sum_comp,
      finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul]
  rw [hdiff]
  exact Finset.dvd_sum fun j _ => ((h j).mul_right _)

/-- The models' phrasing: `π ^ N`-congruent vectors recentre to `π ^ N`-congruent vectors. -/
theorem dvd_pow_shiftVecN_sub {n : ℕ} {π : O} {N : ℕ} {a a' : Fin n → O} (γ : O)
    (h : ∀ i, π ^ N ∣ (a' i - a i)) :
    ∀ i, π ^ N ∣ (shiftVecN a' γ i - shiftVecN a γ i) :=
  dvd_shiftVecN_sub γ h

/-- Recentring descends to level-`N` classes (landed `proj_recentreVec_congr`, campaign
name). -/
theorem proj_shiftVecN_congr {n : ℕ} {π : O} (hπ : Irreducible π) {N : ℕ}
    {a a' : Fin n → O} (h : proj O n N a = proj O n N a') (γ : O) :
    proj O n N (shiftVecN a γ) = proj O n N (shiftVecN a' γ) :=
  Induction.proj_recentreVec_congr hπ h γ

end ShiftVec

/-! ## §2 The explicit coefficient law -/

section CoeffLaw

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The explicit binomial coefficient law** for the recentred vector:
`shiftVecN a γ i = C(n,i)·γ^(n−i) + Σ_j C(j,i)·a_j·γ^(j−i)`.  Truncated subtraction is
harmless: for `j < i` the binomial coefficient vanishes.  Proof through the Taylor/Hasse
derivative (`taylor_coeff`, `hasseDeriv_monomial`). -/
theorem shiftVecN_apply {n : ℕ} (a : Fin n → O) (γ : O) (i : Fin n) :
    shiftVecN a γ i = (n.choose (i : ℕ) : O) * γ ^ (n - (i : ℕ))
      + ∑ j : Fin n, ((j : ℕ).choose (i : ℕ) : O) * a j * γ ^ ((j : ℕ) - (i : ℕ)) := by
  rw [shiftVecN_def, ← taylor_apply, taylor_coeff]
  simp only [monicPoly, map_add, map_sum, X_pow_eq_monomial, C_mul_monomial,
    hasseDeriv_monomial, eval_add, eval_finsetSum, eval_monomial, mul_one]

/-- The constant recentred coefficient is the VALUE `F_a(γ)` — the generic `shiftVec_zero`. -/
theorem shiftVecN_coeff_zero {n : ℕ} (a : Fin n → O) (γ : O) (h0 : 0 < n) :
    shiftVecN a γ ⟨0, h0⟩ = (monicPoly a).eval γ := by
  rw [shiftVecN_def, ← taylor_apply]
  exact taylor_coeff_zero γ (monicPoly a)

/-- The linear recentred coefficient is the DERIVATIVE `F_a′(γ)` — the generic
`shiftVec_one`. -/
theorem shiftVecN_coeff_one {n : ℕ} (a : Fin n → O) (γ : O) (h1 : 1 < n) :
    shiftVecN a γ ⟨1, h1⟩ = (monicPoly a).derivative.eval γ := by
  rw [shiftVecN_def, ← taylor_apply]
  exact taylor_coeff_one γ (monicPoly a)

end CoeffLaw

/-! ## §3 The class-level translation bijection and the certificate transport

The class-level carrier is the LANDED `Induction.recentreClass` (H.123a); new here are the
bundled bijection, the proj law in the campaign name, the cardinality invariance, and the
generic certificate transport. -/

section ClassShift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The level-`N` class translation bijection** at every degree — the bundled form of the
landed `recentreClass` involution. -/
def coeffShiftEquivN (n N : ℕ) (γ : O) : Coeff O n N ≃ Coeff O n N where
  toFun := Induction.recentreClass O n N γ
  invFun := Induction.recentreClass O n N (-γ)
  left_inv c := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    exact Induction.recentreClass_recentreClass hπ γ c
  right_inv c := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h := Induction.recentreClass_recentreClass hπ (-γ) c
    rwa [neg_neg] at h

/-- The class translation computes on every lift through `shiftVecN` (landed
`proj_recentreVec`, campaign phrasing). -/
theorem coeffShiftEquivN_proj {π : O} (hπ : Irreducible π) {n N : ℕ} (γ : O)
    (a : Fin n → O) :
    coeffShiftEquivN n N γ (proj O n N a) = proj O n N (shiftVecN a γ) :=
  (Induction.proj_recentreVec hπ rfl γ).symm

/-- **Translations preserve set cardinalities in the box** — the counting form the weight
bookkeeping (A0G-RW) consumes. -/
theorem card_image_coeffShiftEquivN {n N : ℕ} (γ : O) (S : Set (Coeff O n N)) :
    Nat.card ((coeffShiftEquivN (O := O) n N γ) '' S) = Nat.card S :=
  Nat.card_image_of_injective (coeffShiftEquivN (O := O) n N γ).injective S

/-- **The generic certificate transport** (degree-generic `decidedAt_of_shift_cert`, with an
arbitrary certificate depth `k ≤ M`): a type verdict that only reads the recentred vector mod
`π ^ k` decides the level-`M` class. -/
theorem decidedAt_of_shiftVecN_cert {π : O} (hπ : Irreducible π) {n M k : ℕ} (hk : k ≤ M)
    {a : Fin n → O} (γ : O) {σ : FactorizationType}
    (hcert : ∀ b : Fin n → O, (∀ i, π ^ k ∣ (b i - shiftVecN a γ i)) →
      typeOf (monicPoly b) = σ) :
    DecidedAt O n σ M (proj O n M a) := by
  refine decidedAt_of_congr hπ (fun b hb => ?_)
  have hM : ∀ i, π ^ M ∣ (shiftVecN b γ i - shiftVecN a γ i) := dvd_pow_shiftVecN_sub γ hb
  have hK : ∀ i, π ^ k ∣ (shiftVecN b γ i - shiftVecN a γ i) := fun i =>
    (pow_dvd_pow π hk).trans (hM i)
  rw [← typeOf_shiftVecN b γ]
  exact hcert _ hK

end ClassShift

/-! ## §4 The degree-generic mixed-precision box `MBoxN`

The size-`m` cluster extraction `X = πY` divides coordinate `i` of the recentred vector by
`π^(m−i)` (§3.2 of the A0 plan), so the level-`(M+m)` class pins the extracted coordinate `i`
to precision exactly `M + i`.  At `n = 3` this is H97r3's `MBox` (recovered in §5). -/

section MBoxGen

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The degree-generic mixed-precision box**: coordinate `i` at precision `M + i`. -/
abbrev MBoxN (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n M : ℕ) : Type _ :=
  (i : Fin n) → Res O (M + (i : ℕ))

/-- Truncation of the mixed box to the uniform level-`M` coefficient box, as an additive
homomorphism (all fibres the same size). -/
def mtruncN (n M : ℕ) : MBoxN O n M →+ Coeff O n M :=
  AddMonoidHom.pi fun i =>
    (resFactor (O := O) (Nat.le_add_right M (i : ℕ))).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun j : Fin n => Res O (M + (j : ℕ))) i)

theorem mtruncN_apply (n M : ℕ) (b : MBoxN O n M) (i : Fin n) :
    mtruncN (O := O) n M b i = resFactor (Nat.le_add_right M (i : ℕ)) (b i) := rfl

theorem mtruncN_surjective (n M : ℕ) : Function.Surjective (mtruncN (O := O) n M) := by
  intro c
  choose y hy using fun i : Fin n =>
    resFactor_surjective (O := O) (Nat.le_add_right M (i : ℕ)) (c i)
  exact ⟨y, funext hy⟩

/-- The mixed-box record of a lift vector — coordinate `i` at its natural precision `M + i`. -/
def mkBoxN (n M : ℕ) (d : Fin n → O) : MBoxN O n M :=
  fun i => Ideal.Quotient.mk ((maximalIdeal O) ^ (M + (i : ℕ))) (d i)

/-- Truncating the record recovers the level-`M` class (generic `mtrunc_mkBox`). -/
theorem mtruncN_mkBoxN (n M : ℕ) (d : Fin n → O) :
    mtruncN (O := O) n M (mkBoxN n M d) = proj O n M d := by
  funext i
  exact resFactor_mk (Nat.le_add_right M (i : ℕ)) (d i)

/-- **The record laws** (generic `dvd_of_mkBox_eq`, as an iff): equal records are exactly the
mixed-precision congruences. -/
theorem mkBoxN_eq_iff_dvd {π : O} (hπ : Irreducible π) {n M : ℕ} {d d' : Fin n → O} :
    mkBoxN (O := O) n M d = mkBoxN n M d' ↔
      ∀ i : Fin n, π ^ (M + (i : ℕ)) ∣ (d' i - d i) := by
  constructor
  · intro h i
    have hi : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + (i : ℕ))) (d i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + (i : ℕ))) (d' i) := congrFun h i
    exact dvd_sub_comm.mp
      ((Induction.mem_maximalIdeal_pow_iff_dvd_of_irr hπ (M + (i : ℕ)) _).1 (Ideal.Quotient.eq.1 hi))
  · intro h
    funext i
    exact Ideal.Quotient.eq.2
      ((Induction.mem_maximalIdeal_pow_iff_dvd_of_irr hπ (M + (i : ℕ)) _).2 (dvd_sub_comm.mp (h i)))

/-- Every mixed record is realized by a lift vector. -/
theorem mkBoxN_surjective (n M : ℕ) : Function.Surjective (mkBoxN (O := O) n M) := by
  intro b
  choose y hy using fun i : Fin n => Ideal.Quotient.mk_surjective (b i)
  exact ⟨y, funext hy⟩

/-- **The mixed precisions multiply back up with NO loss** — the degree-generic mechanism of
H97r3's sharp count: if two extracted vectors (`b i = π^(n−i)·d i`) have EQUAL mixed records,
then the assembled vectors agree to the FULL precision `M + n`, because the extracted power
`π^(n−i)` exactly complements the record precision `M + i`. -/
theorem dvd_extract_sub_of_mkBoxN_eq {π : O} (hπ : Irreducible π) {n M : ℕ}
    {d d' b b' : Fin n → O}
    (hb : ∀ i : Fin n, b i = π ^ (n - (i : ℕ)) * d i)
    (hb' : ∀ i : Fin n, b' i = π ^ (n - (i : ℕ)) * d' i)
    (h : mkBoxN (O := O) n M d = mkBoxN n M d') :
    ∀ i : Fin n, π ^ (M + n) ∣ (b' i - b i) := by
  intro i
  obtain ⟨t, ht⟩ := (mkBoxN_eq_iff_dvd hπ).1 h i
  refine ⟨t, ?_⟩
  rw [hb' i, hb i, ← mul_sub, ht, ← mul_assoc, ← pow_add]
  congr 2
  omega

end MBoxGen

section MBoxCard

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **THE EXACT BOX CARDINALITY**: `#(MBoxN O n M) = q ^ (nM + n(n−1)/2)`.  The excess
exponent `n(n−1)/2 = κ_n` is §3.2's coefficient-loss constant. -/
theorem card_MBoxN (n M : ℕ) :
    Nat.card (MBoxN O n M) = residueCard O ^ (n * M + n * (n - 1) / 2) := by
  rw [Nat.card_pi]
  simp only [card_res]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => M + i), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, Finset.sum_range_id]

/-- **The proportion is preserved by the mixed-precision refinement** (generic
`card_preimage_mtrunc`). -/
theorem card_preimage_mtruncN (n M : ℕ) (S : Set (Coeff O n M)) :
    Nat.card ((mtruncN (O := O) n M) ⁻¹' S) * Nat.card (Coeff O n M)
      = Nat.card S * Nat.card (MBoxN O n M) := by
  have hs := mtruncN_surjective (O := O) n M
  have h1 := card_preimage_of_surjective (mtruncN (O := O) n M) hs S
  have h2 := card_preimage_of_surjective (mtruncN (O := O) n M) hs Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h2
  rw [h1, h2]
  ring

/-- **The exact fibre law**: pulling back along `mtruncN` multiplies counts by exactly
`q ^ (n(n−1)/2)`. -/
theorem card_preimage_mtruncN_eq (n M : ℕ) (S : Set (Coeff O n M)) :
    Nat.card ((mtruncN (O := O) n M) ⁻¹' S)
      = Nat.card S * residueCard O ^ (n * (n - 1) / 2) := by
  have h := card_preimage_mtruncN (O := O) n M S
  rw [card_coeff, card_MBoxN, pow_add] at h
  refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) (n * M)) ?_
  rw [h]
  ring

end MBoxCard

/-! ## §5 The recovery bank at `n = 2, 3` (THE GATE)

The generic definitions instantiate to the landed degree-2/3 shapes.  Fixed degrees appear
ONLY in this section — these ARE the mandated recovery statements. -/

section Recovery

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **RECOVERY (n = 3)**: the generic recentring instantiates to the landed `H97r1.shiftVec`. -/
theorem shiftVecN_three (a : Fin 3 → O) (γ : O) : shiftVecN a γ = shiftVec a γ :=
  monicPoly_injective (by rw [monicPoly_shiftVecN, monicPoly_shiftVec])

/-- **RECOVERY (n = 2)**: the generic recentring instantiates to the landed
`IFC7.shiftVec2`. -/
theorem shiftVecN_two [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    (b : Fin 2 → O) (γ : O) : shiftVecN b γ = IFC7.shiftVec2 b γ :=
  monicPoly_injective (by rw [monicPoly_shiftVecN, IFC7.monicPoly_shiftVec2])

/-- The landed cubic certificate wrapper `decidedAt_of_shift_cert` is an instance of the
generic transport (`n = 3`, depth `k = 3`, level `M + 3`). -/
theorem decidedAt_of_shift_cert_recover [Finite (ResidueField O)] {π : O}
    (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O} {σ : FactorizationType}
    (hcert : ∀ b : Fin 3 → O, (∀ i, π ^ 3 ∣ (b i - shiftVec a γ i)) →
      typeOf (monicPoly b) = σ) :
    DecidedAt O 3 σ (M + 3) (proj O 3 (M + 3) a) := by
  refine decidedAt_of_shiftVecN_cert (k := 3) hπ (by omega) γ ?_
  rw [shiftVecN_three]
  exact hcert

variable [Finite (ResidueField O)]

/-- **RECOVERY (n = 3, box)**: the generic mixed box at degree 3 IS H97r3's `MBox`. -/
def mboxEquivThree (M : ℕ) : MBoxN O 3 M ≃ MBox O M where
  toFun b := (b 0, b 1, b 2)
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 (Fin.cons p.2.2 finZeroElim))
  left_inv b := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

/-- The generic record instantiates DEFINITIONALLY to the landed `mkBox` (`rfl`). -/
theorem mboxEquivThree_mkBoxN (M : ℕ) (d : Fin 3 → O) :
    mboxEquivThree M (mkBoxN (O := O) 3 M d) = mkBox M d := rfl

/-- The generic truncation instantiates to the landed `mtrunc` through the identification. -/
theorem mtrunc_mboxEquivThree (M : ℕ) (b : MBoxN O 3 M) :
    mtrunc (O := O) M (mboxEquivThree M b) = mtruncN (O := O) 3 M b := by
  funext i
  fin_cases i
  · exact (resFactor_self (le_refl M) (b 0)).symm
  · rfl
  · rfl

/-- Cardinality recovery (n = 3): the generic box has the landed `MBox` cardinality. -/
theorem card_MBoxN_eq_card_mbox (M : ℕ) :
    Nat.card (MBoxN O 3 M) = Nat.card (MBox O M) :=
  Nat.card_congr (mboxEquivThree (O := O) M)

/-- Exponent pin (n = 3): `3M + 3`, the landed `card_mbox` exponent. -/
theorem card_MBoxN_three (M : ℕ) :
    Nat.card (MBoxN O 3 M) = residueCard O ^ (3 * M + 3) := by
  rw [card_MBoxN]

/-- Exponent pin (n = 2): `2M + 1` — the `κ_2 = 1` mixed box the quadratic cluster
extraction uses. -/
theorem card_MBoxN_two (M : ℕ) :
    Nat.card (MBoxN O 2 M) = residueCard O ^ (2 * M + 1) := by
  rw [card_MBoxN]

end Recovery

end Uniformity.Density.IFCG1

end

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.IFCG1.monicPoly_injective
#print axioms Uniformity.Density.IFCG1.typeOf_shiftVecN
#print axioms Uniformity.Density.IFCG1.shiftVecN_zero
#print axioms Uniformity.Density.IFCG1.shiftVecN_add
#print axioms Uniformity.Density.IFCG1.dvd_shiftVecN_sub
#print axioms Uniformity.Density.IFCG1.shiftVecN_apply
#print axioms Uniformity.Density.IFCG1.shiftVecN_coeff_zero
#print axioms Uniformity.Density.IFCG1.shiftVecN_coeff_one
#print axioms Uniformity.Density.IFCG1.coeffShiftEquivN_proj
#print axioms Uniformity.Density.IFCG1.card_image_coeffShiftEquivN
#print axioms Uniformity.Density.IFCG1.decidedAt_of_shiftVecN_cert
#print axioms Uniformity.Density.IFCG1.proj_shiftVecN_congr
#print axioms Uniformity.Density.IFCG1.mtruncN_surjective
#print axioms Uniformity.Density.IFCG1.mtruncN_mkBoxN
#print axioms Uniformity.Density.IFCG1.mkBoxN_eq_iff_dvd
#print axioms Uniformity.Density.IFCG1.mkBoxN_surjective
#print axioms Uniformity.Density.IFCG1.dvd_extract_sub_of_mkBoxN_eq
#print axioms Uniformity.Density.IFCG1.card_MBoxN
#print axioms Uniformity.Density.IFCG1.card_preimage_mtruncN
#print axioms Uniformity.Density.IFCG1.card_preimage_mtruncN_eq
#print axioms Uniformity.Density.IFCG1.shiftVecN_three
#print axioms Uniformity.Density.IFCG1.shiftVecN_two
#print axioms Uniformity.Density.IFCG1.decidedAt_of_shift_cert_recover
#print axioms Uniformity.Density.IFCG1.mboxEquivThree_mkBoxN
#print axioms Uniformity.Density.IFCG1.mtrunc_mboxEquivThree
#print axioms Uniformity.Density.IFCG1.card_MBoxN_eq_card_mbox
#print axioms Uniformity.Density.IFCG1.card_MBoxN_three
#print axioms Uniformity.Density.IFCG1.card_MBoxN_two

end AxCheck
