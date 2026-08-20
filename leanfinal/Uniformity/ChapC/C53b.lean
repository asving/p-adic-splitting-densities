/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C53
import Uniformity.ChapC.C47
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06

/-!
# Uniformity.ChapC.C53b — the GENERAL TWO-KEY DIGIT DICTIONARY

**Sub-unit of NODE C.53** (`C53_BLOCKED_2026-08-20.md`, GOAL 3 / leg 2), and the supplier
obstruction 4 of `C52_BLOCKED_2026-08-18.md` names.  Nothing here is signed; nothing in
`C53.lean` is edited.

## What this file is

The **two-key dictionary**: a mutually inverse pair between

* raw coefficient vectors `a : Fin (μ₂D₂) → O` of monic degree-`μ₂D₂` polynomials, and
* two-key digit vectors `c : Fin (μ₂D₂) → O`, `c` at raw index `i = j·D₂ + b·D′ + a'` being the
  degree-`a'` coefficient of the `b`-th `Φ′`-digit of the `j`-th `Φ₂`-digit,

realized as `digitVec` (`a ↦ c`) and `polyVec` (`c ↦ a`), with `polyVec` computed from the
explicit two-key monomial expansion `Φ₂^{μ₂} + ∑ᵢ cᵢ·X^{a'}Φ′^{b}Φ₂^{j}`.  Both directions are
proved from the one-key development API alone (B.02 `dev`, B.03 `degree_dev_lt`,
B.05 `sum_dev_eq`, B.06 `dev_unique`) — no polygon, no purity, no residual, no completeness, no
Hensel lifting.  Style modelled on `C110.lean` clause 2's `dev_sub_C`: an exact identity in
`O[X]`, never a "the change of coordinates is unitriangular" hand-wave.

## Status

Sorry-free. Axiom footprint: Lean core (AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing
open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The two-key monomial basis -/

/-- **The two-key monomial** `X^{a}·Φ′^{b}·Φ₂^{j}` (`Φ′ = F.key`, `Φ₂ = composedKey T`).  For
`a < D′`, `b < e₂f₂`, `j < μ₂` it is monic of degree exactly `j·D₂ + b·D′ + a`, and these
`μ₂D₂` monomials together with `Φ₂^{μ₂}` are the basis in which the two-key digits are the
coordinates. -/
noncomputable def twoKeyMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (j a b : ℕ) : Polynomial O :=
  X ^ a * F.key ^ b * (composedKey T) ^ j

/-- The two-key monomial at the **raw index** `i`, decoded exactly as `budgetSlot` decodes it:
`j = i / D₂`, `a = i % D₂ % D′`, `b = i % D₂ / D′`, so that `i = j·D₂ + b·D′ + a`. -/
noncomputable def slotMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (i : ℕ) : Polynomial O :=
  twoKeyMon T (i / T.D₂) (i % T.D₂ % (F.e₁ * F.f₁)) (i % T.D₂ / (F.e₁ * F.f₁))

/-- **The reconstruction map on polynomials**: the monic degree-`μ₂D₂` polynomial whose two-key
digit vector is `c`. -/
noncomputable def slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) : Polynomial O :=
  (composedKey T) ^ μ₂ + ∑ i : Fin (μ₂ * T.D₂), C (c i) * slotMon T i.1

/-- **The digit map** `a ↦ c`: the two-key digit vector of `monicPoly a`, indexed by the same
raw slot decoding `budgetSlot` uses. -/
noncomputable def digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (a : Fin (μ₂ * T.D₂) → O) : Fin (μ₂ * T.D₂) → O :=
  fun i => (dev F.key (dev (composedKey T) (monicPoly a) (i.1 / T.D₂))
    (i.1 % T.D₂ / (F.e₁ * F.f₁))).coeff (i.1 % T.D₂ % (F.e₁ * F.f₁))

/-- **The reconstruction map** `c ↦ a`: the raw coefficient vector of `slotPoly`. -/
noncomputable def polyVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) : Fin (μ₂ * T.D₂) → O :=
  fun i => (slotPoly T μ₂ c).coeff i.1

/-! ### Arithmetic preliminaries

`sum_range_div_mod'` is the `AddCommMonoid`-valued generalization of `C53.lean`'s `ℕ`-valued
`private` `sum_range_div_mod` (which cannot be imported); it is needed here for
`Polynomial O`-valued sums.  Same three-line induction. -/

private theorem sum_range_div_mod' {M : Type*} [AddCommMonoid M] {d : ℕ} (hd : 0 < d)
    (g : ℕ → ℕ → M) (a : ℕ) :
    ∑ i ∈ Finset.range (a * d), g (i / d) (i % d)
      = ∑ j ∈ Finset.range a, ∑ s ∈ Finset.range d, g j s := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hsplit : (a + 1) * d = a * d + d := by ring
    rw [hsplit, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < d := Finset.mem_range.1 hi
    have hdiv : (a * d + i) / d = a := by
      rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hi', Nat.add_zero]
    have hmod : (a * d + i) % d = i := by
      rw [Nat.mul_comm a d, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
    rw [hdiv, hmod]

private theorem hEpos {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : 0 < T.e₂ * T.f₂ := Nat.mul_pos T.he₂ T.hf₂

private theorem hD₂pos {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : 0 < T.D₂ := by
  rw [TowerDatum.D₂]; exact Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (hEpos T)

/-- **`deg Φ₂ = D₂`**, C.47's clause 2 read through C.42's numeral instead of the level-2
dictionary's `keyDeg₂` (the form every consumer here wants). -/
theorem composedKey_natDegree_D₂ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (composedKey T).natDegree = T.D₂ := by
  have hd : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  have hl : (T.levelDatum hπ).ℓ = T.e₂ := rfl
  rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂, hd, hl, TowerDatum.D₂]
  ring

/-- extension of a `Fin n`-indexed vector to a total function on `ℕ`, by zero. -/
private def vext {n : ℕ} (a : Fin n → O) : ℕ → O := fun i => if h : i < n then a ⟨i, h⟩ else 0

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem vext_apply {n : ℕ} (a : Fin n → O) (i : Fin n) : vext a i.1 = a i := by
  simp only [vext, dif_pos i.isLt]

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem vext_of_lt {n : ℕ} (a : Fin n → O) {i : ℕ} (h : i < n) :
    vext a i = a ⟨i, h⟩ := by
  simp only [vext, dif_pos h]

/-! ### The two families of digits of a slot vector

`slotDig1 T u j b` is the degree-`< D′` polynomial `∑_{a < D′} u_{jD₂+bD′+a}·X^a`, and
`slotDig0 T u j` is the degree-`< D₂` polynomial `∑_{b < e₂f₂} (slotDig1 T u j b)·Φ′^b`.  These
are the two nested development digit families that `dev_unique` will identify. -/

private noncomputable def slotDig1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j b : ℕ) : Polynomial O :=
  ∑ a ∈ Finset.range (F.e₁ * F.f₁), C (u (j * T.D₂ + b * (F.e₁ * F.f₁) + a)) * X ^ a

private noncomputable def slotDig0 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j : ℕ) : Polynomial O :=
  ∑ b ∈ Finset.range (T.e₂ * T.f₂), slotDig1 T u j b * F.key ^ b

private theorem natDegree_slotDig1_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j b : ℕ) :
    (slotDig1 T u j b).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hbound : (slotDig1 T u j b).natDegree ≤ F.e₁ * F.f₁ - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
    have ha' : a < F.e₁ * F.f₁ := Finset.mem_range.1 ha
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  omega

private theorem degree_slotDig1_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j b : ℕ) :
    (slotDig1 T u j b).degree < F.key.degree := by
  refine Polynomial.degree_lt_degree ?_
  rw [F.hdeg]
  exact natDegree_slotDig1_lt T u j b

private theorem natDegree_slotDig0_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j : ℕ) :
    (slotDig0 T u j).natDegree < T.D₂ := by
  have hpos : 0 < T.D₂ := hD₂pos T
  have hbound : (slotDig0 T u j).natDegree ≤ T.D₂ - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    have hb' : b < T.e₂ * T.f₂ := Finset.mem_range.1 hb
    have h1 : (slotDig1 T u j b * F.key ^ b).natDegree
        ≤ (slotDig1 T u j b).natDegree + b * (F.e₁ * F.f₁) := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, F.hdeg]
    have h2 : (slotDig1 T u j b).natDegree < F.e₁ * F.f₁ := natDegree_slotDig1_lt T u j b
    have h3 : b * (F.e₁ * F.f₁) ≤ (T.e₂ * T.f₂ - 1) * (F.e₁ * F.f₁) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : T.D₂ = (F.e₁ * F.f₁) * (T.e₂ * T.f₂) := by rw [TowerDatum.D₂]
    have h5 : 0 < T.e₂ * T.f₂ := hEpos T
    have hsucc : T.e₂ * T.f₂ - 1 + 1 = T.e₂ * T.f₂ := Nat.succ_pred_eq_of_pos h5
    have h6 : (T.e₂ * T.f₂ - 1) * (F.e₁ * F.f₁) + (F.e₁ * F.f₁)
        = (F.e₁ * F.f₁) * (T.e₂ * T.f₂) := by
      calc (T.e₂ * T.f₂ - 1) * (F.e₁ * F.f₁) + (F.e₁ * F.f₁)
          = (T.e₂ * T.f₂ - 1 + 1) * (F.e₁ * F.f₁) := by ring
        _ = (F.e₁ * F.f₁) * (T.e₂ * T.f₂) := by rw [hsucc]; ring
    omega
  omega

private theorem degree_slotDig0_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (u : ℕ → O) (j : ℕ) :
    (slotDig0 T u j).degree < (composedKey T).degree := by
  refine Polynomial.degree_lt_degree ?_
  rw [composedKey_natDegree_D₂ T hπ]
  exact natDegree_slotDig0_lt T u j

/-- reading a coefficient off `slotDig1` inside its range just reads the slot vector. -/
private theorem coeff_slotDig1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j b : ℕ) {a : ℕ} (ha : a < F.e₁ * F.f₁) :
    (slotDig1 T u j b).coeff a = u (j * T.D₂ + b * (F.e₁ * F.f₁) + a) := by
  classical
  simp only [slotDig1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (F.e₁ * F.f₁)) a
    (fun k => u (j * T.D₂ + b * (F.e₁ * F.f₁) + k))]
  simp [Finset.mem_range.2 ha]

/-! ### The grouped form: the flat slot sum IS a two-level development

`slotSum_grouped` is the whole combinatorial content of the dictionary — the flat sum over the
`μ₂D₂` raw indices, regrouped along `i = j·D₂ + b·D′ + a`, is literally the nested development
`∑_j (∑_b (∑_a c·X^a)·Φ′^b)·Φ₂^j`.  Everything after this is `dev_unique` / `sum_dev_eq`. -/

private theorem slotSum_grouped {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (u : ℕ → O) :
    ∑ i ∈ Finset.range (μ₂ * T.D₂), C (u i) * slotMon T i
      = ∑ j ∈ Finset.range μ₂, slotDig0 T u j * (composedKey T) ^ j := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hE : 0 < T.e₂ * T.f₂ := hEpos T
  have hD₂ : 0 < T.D₂ := hD₂pos T
  -- the outer regrouping `i ↦ (i / D₂, i % D₂)`
  have hg := sum_range_div_mod' hD₂ (fun j s => C (u (j * T.D₂ + s)) *
      (X ^ (s % (F.e₁ * F.f₁)) * F.key ^ (s / (F.e₁ * F.f₁)) * (composedKey T) ^ j)) μ₂
  have hlhs : ∑ i ∈ Finset.range (μ₂ * T.D₂), C (u i) * slotMon T i
      = ∑ i ∈ Finset.range (μ₂ * T.D₂), C (u (i / T.D₂ * T.D₂ + i % T.D₂)) *
          (X ^ (i % T.D₂ % (F.e₁ * F.f₁)) * F.key ^ (i % T.D₂ / (F.e₁ * F.f₁)) *
            (composedKey T) ^ (i / T.D₂)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.div_add_mod']
    rfl
  rw [hlhs, hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- the inner regrouping `s ↦ (s / D′, s % D′)` on `range ((e₂f₂)·D′)`
  have hcomm : T.D₂ = (T.e₂ * T.f₂) * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
  have hinner : ∀ K : ℕ, ∀ P : Polynomial O,
      ∑ s ∈ Finset.range ((T.e₂ * T.f₂) * (F.e₁ * F.f₁)), C (u (K + s)) *
          (X ^ (s % (F.e₁ * F.f₁)) * F.key ^ (s / (F.e₁ * F.f₁)) * P)
        = ∑ b ∈ Finset.range (T.e₂ * T.f₂), ∑ a ∈ Finset.range (F.e₁ * F.f₁),
            C (u (K + (b * (F.e₁ * F.f₁) + a))) * (X ^ a * F.key ^ b * P) := by
    intro K P
    rw [← sum_range_div_mod' hD' (fun b a => C (u (K + (b * (F.e₁ * F.f₁) + a))) *
      (X ^ a * F.key ^ b * P)) (T.e₂ * T.f₂)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Nat.div_add_mod']
  have hstep2 := hinner (j * T.D₂) ((composedKey T) ^ j)
  rw [← hcomm] at hstep2
  rw [hstep2, slotDig0, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [slotDig1, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidx : j * T.D₂ + (b * (F.e₁ * F.f₁) + a) = j * T.D₂ + b * (F.e₁ * F.f₁) + a := by ring
  rw [hidx]
  ring

/-- **The grouped form of `slotPoly`.**  `slotPoly T μ₂ c = Φ₂^{μ₂} + ∑_{j<μ₂} A_j·Φ₂^j` with
`A_j = ∑_{b<e₂f₂} (∑_{a<D′} c_{jD₂+bD′+a}·X^a)·Φ′^b`: exactly the shape of a `Φ₂`-adic
development whose digits are themselves `Φ′`-adic developments. -/
private theorem slotPoly_grouped {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) :
    slotPoly T μ₂ c
      = (composedKey T) ^ μ₂
        + ∑ j ∈ Finset.range μ₂, slotDig0 T (vext c) j * (composedKey T) ^ j := by
  rw [slotPoly]
  congr 1
  rw [← slotSum_grouped T μ₂ (vext c),
    ← Fin.sum_univ_eq_sum_range (fun i => C (vext c i) * slotMon T i) (μ₂ * T.D₂)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vext_apply]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.twoKeyMon
#print axioms Uniformity.Density.Tower.slotMon
#print axioms Uniformity.Density.Tower.slotPoly
#print axioms Uniformity.Density.Tower.digitVec
#print axioms Uniformity.Density.Tower.polyVec
#print axioms Uniformity.Density.Tower.composedKey_natDegree_D₂

end AxCheck
