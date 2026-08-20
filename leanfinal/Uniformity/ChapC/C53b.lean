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

/-! ### `slotPoly` is monic of degree `μ₂D₂`, and `monicPoly` inverts coefficient reading -/

private theorem monic_slotMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (i : ℕ) : (slotMon T i).Monic :=
  ((Polynomial.monic_X_pow _).mul (F.hmonic.pow _)).mul ((composedKey_monic T).pow _)

/-- **The two-key monomial at raw index `i` has degree exactly `i`** — the "unipotent in the
x-degree filtration" statement, as an identity rather than a hand-wave.  Unconditional in `i`:
`i%D₂%D′ + (i%D₂/D′)·D′ + (i/D₂)·D₂ = i` is two applications of `Nat.mod_add_div`. -/
private theorem natDegree_slotMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (i : ℕ) : (slotMon T i).natDegree = i := by
  rw [slotMon, twoKeyMon,
    ((Polynomial.monic_X_pow _).mul (F.hmonic.pow _)).natDegree_mul ((composedKey_monic T).pow _),
    (Polynomial.monic_X_pow _).natDegree_mul (F.hmonic.pow _),
    Polynomial.natDegree_X_pow, Polynomial.natDegree_pow, Polynomial.natDegree_pow, F.hdeg,
    composedKey_natDegree_D₂ T hπ]
  have h1 : i % T.D₂ % (F.e₁ * F.f₁) + (F.e₁ * F.f₁) * (i % T.D₂ / (F.e₁ * F.f₁)) = i % T.D₂ :=
    Nat.mod_add_div _ _
  have h2 : i % T.D₂ + T.D₂ * (i / T.D₂) = i := Nat.mod_add_div _ _
  calc i % T.D₂ % (F.e₁ * F.f₁) + (i % T.D₂ / (F.e₁ * F.f₁)) * (F.e₁ * F.f₁)
        + (i / T.D₂) * T.D₂
      = (i % T.D₂ % (F.e₁ * F.f₁) + (F.e₁ * F.f₁) * (i % T.D₂ / (F.e₁ * F.f₁)))
        + T.D₂ * (i / T.D₂) := by ring
    _ = i := by rw [h1, h2]

private theorem natDegree_slotTail_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (hμ : 0 < μ₂)
    (c : Fin (μ₂ * T.D₂) → O) :
    (∑ i : Fin (μ₂ * T.D₂), C (c i) * slotMon T i.1).natDegree < μ₂ * T.D₂ := by
  have hpos : 0 < μ₂ * T.D₂ := Nat.mul_pos hμ (hD₂pos T)
  have hbound : (∑ i : Fin (μ₂ * T.D₂), C (c i) * slotMon T i.1).natDegree ≤ μ₂ * T.D₂ - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [natDegree_slotMon T hπ]
    have := i.isLt
    omega
  omega

private theorem monic_slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (hμ : 0 < μ₂)
    (c : Fin (μ₂ * T.D₂) → O) : (slotPoly T μ₂ c).Monic := by
  have hpow : ((composedKey T) ^ μ₂).Monic := (composedKey_monic T).pow μ₂
  have hdeg : ((composedKey T) ^ μ₂).natDegree = μ₂ * T.D₂ := by
    rw [Polynomial.natDegree_pow, composedKey_natDegree_D₂ T hπ]
  rw [slotPoly]
  refine hpow.add_of_left (Polynomial.degree_lt_degree ?_)
  rw [hdeg]
  exact natDegree_slotTail_lt T hπ hμ c

private theorem natDegree_slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (hμ : 0 < μ₂)
    (c : Fin (μ₂ * T.D₂) → O) : (slotPoly T μ₂ c).natDegree = μ₂ * T.D₂ := by
  have hpow : ((composedKey T) ^ μ₂).Monic := (composedKey_monic T).pow μ₂
  have hdeg : ((composedKey T) ^ μ₂).natDegree = μ₂ * T.D₂ := by
    rw [Polynomial.natDegree_pow, composedKey_natDegree_D₂ T hπ]
  have hlt : (∑ i : Fin (μ₂ * T.D₂), C (c i) * slotMon T i.1).degree
      < ((composedKey T) ^ μ₂).degree :=
    Polynomial.degree_lt_degree (by rw [hdeg]; exact natDegree_slotTail_lt T hπ hμ c)
  rw [slotPoly,
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hlt), hdeg]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`monicPoly` inverts coefficient reading**: a monic polynomial of degree `n` is `monicPoly`
of its own low coefficient vector. -/
private theorem monicPoly_coeff_self {n : ℕ} {f : Polynomial O} (hf : f.Monic)
    (hn : f.natDegree = n) : monicPoly (fun i : Fin n => f.coeff i.1) = f := by
  classical
  have hlead : f.coeff n = 1 := by rw [← hn]; exact hf.coeff_natDegree
  refine Polynomial.ext fun m => ?_
  rw [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  have hsum : ∑ i : Fin n, (C (f.coeff i.1) * X ^ (i.1 : ℕ) : Polynomial O).coeff m
      = if m < n then f.coeff m else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (C (f.coeff k) * X ^ k : Polynomial O).coeff m) n]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range n) m (fun k => f.coeff k)]
    simp [Finset.mem_range]
  rw [hsum]
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg (by omega), if_pos h, zero_add]
  · subst h
    rw [if_pos rfl, if_neg (by omega), add_zero, hlead]
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem monicPoly_coeff_val {n : ℕ} (a : Fin n → O) (i : Fin n) :
    (monicPoly a).coeff i.1 = a i := by
  classical
  rw [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    if_neg (by have := i.isLt; omega), zero_add]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun hcon => hb (Fin.val_injective hcon.symm))]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-! ### Dictionary, direction B: `digitVec ∘ polyVec = id` -/

private theorem degree_slotA_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ : ℕ) (u : ℕ → O) (j : ℕ) :
    ((if j = μ₂ then 1 else slotDig0 T u j) : Polynomial O).degree < (composedKey T).degree := by
  by_cases h : j = μ₂
  · rw [if_pos h]
    refine Polynomial.degree_lt_degree ?_
    rw [Polynomial.natDegree_one, composedKey_natDegree_D₂ T hπ]
    exact hD₂pos T
  · rw [if_neg h]
    exact degree_slotDig0_lt T hπ u j

private theorem slotPoly_eq_devSum {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) :
    slotPoly T μ₂ c = ∑ j ∈ Finset.range (μ₂ + 1),
      (if j = μ₂ then 1 else slotDig0 T (vext c) j) * (composedKey T) ^ j := by
  rw [slotPoly_grouped, Finset.sum_range_succ, if_pos rfl, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (by have := Finset.mem_range.1 hj; omega)]

private theorem dev_slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O)
    {j : ℕ} (hj : j < μ₂) :
    dev (composedKey T) (slotPoly T μ₂ c) j = slotDig0 T (vext c) j := by
  have hmon := composedKey_monic T
  have hpos : 0 < (composedKey T).natDegree := by
    rw [composedKey_natDegree_D₂ T hπ]; exact hD₂pos T
  have h := dev_unique hmon hpos (fun j' => degree_slotA_lt T hπ μ₂ (vext c) j')
    (slotPoly_eq_devSum T μ₂ c).symm j (by omega)
  rw [if_neg (by omega : ¬ j = μ₂)] at h
  exact h.symm

private theorem dev_slotDig0 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (u : ℕ → O) (j : ℕ) {b : ℕ} (hb : b < T.e₂ * T.f₂) :
    dev F.key (slotDig0 T u j) b = slotDig1 T u j b := by
  have hpos : 0 < F.key.natDegree := by rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  exact (dev_unique F.hmonic hpos (fun b' => degree_slotDig1_lt T u j b') rfl b hb).symm

/-- **THE DICTIONARY, direction B.**  Reading the two-key digits of the reconstruction returns
the digit vector one started from: `digitVec ∘ polyVec = id`. -/
theorem digitVec_polyVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (hμ : 0 < μ₂)
    (c : Fin (μ₂ * T.D₂) → O) : digitVec T μ₂ (polyVec T μ₂ c) = c := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hD₂ : 0 < T.D₂ := hD₂pos T
  have hmp : monicPoly (polyVec T μ₂ c) = slotPoly T μ₂ c :=
    monicPoly_coeff_self (monic_slotPoly T hπ hμ c) (natDegree_slotPoly T hπ hμ c)
  funext i
  have hi := i.isLt
  -- the three decoded indices are in range
  have hj : i.1 / T.D₂ < μ₂ := (Nat.div_lt_iff_lt_mul hD₂).2 hi
  have hb : i.1 % T.D₂ / (F.e₁ * F.f₁) < T.e₂ * T.f₂ := by
    refine (Nat.div_lt_iff_lt_mul hD').2 ?_
    have hlt : i.1 % T.D₂ < T.D₂ := Nat.mod_lt _ hD₂
    have : T.D₂ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
    omega
  have ha : i.1 % T.D₂ % (F.e₁ * F.f₁) < F.e₁ * F.f₁ := Nat.mod_lt _ hD'
  -- the index recomposes
  have hrec : i.1 / T.D₂ * T.D₂ + i.1 % T.D₂ / (F.e₁ * F.f₁) * (F.e₁ * F.f₁)
      + i.1 % T.D₂ % (F.e₁ * F.f₁) = i.1 := by
    have h1 : i.1 % T.D₂ / (F.e₁ * F.f₁) * (F.e₁ * F.f₁) + i.1 % T.D₂ % (F.e₁ * F.f₁)
        = i.1 % T.D₂ := Nat.div_add_mod' _ _
    have h2 : i.1 / T.D₂ * T.D₂ + i.1 % T.D₂ = i.1 := Nat.div_add_mod' _ _
    omega
  simp only [digitVec, hmp]
  rw [dev_slotPoly T hπ μ₂ c hj, dev_slotDig0 T (vext c) _ hb, coeff_slotDig1 T (vext c) _ _ ha,
    hrec, vext_apply]

/-! ### Dictionary, direction A: `polyVec ∘ digitVec = id` -/

private theorem natDegree_dev_lt' {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) (j : ℕ) : (dev φ f j).natDegree < φ.natDegree := by
  by_cases h : dev φ f j = 0
  · rw [h, Polynomial.natDegree_zero]; exact hd
  · exact natDegree_lt_natDegree h (degree_dev_lt hφ hd f j)

private theorem slotDig1_digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} (a : Fin (μ₂ * T.D₂) → O)
    {j b : ℕ} (hj : j < μ₂) (hb : b < T.e₂ * T.f₂) :
    slotDig1 T (vext (digitVec T μ₂ a)) j b
      = dev F.key (dev (composedKey T) (monicPoly a) j) b := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hD₂ : 0 < T.D₂ := hD₂pos T
  have hkeypos : 0 < F.key.natDegree := by rw [F.hdeg]; exact hD'
  have hdeglt : (dev F.key (dev (composedKey T) (monicPoly a) j) b).natDegree < F.e₁ * F.f₁ := by
    have := natDegree_dev_lt' F.hmonic hkeypos (dev (composedKey T) (monicPoly a) j) b
    rw [F.hdeg] at this
    exact this
  rw [Polynomial.as_sum_range_C_mul_X_pow' _ hdeglt, slotDig1]
  refine Finset.sum_congr rfl fun a' ha' => ?_
  have ha'' : a' < F.e₁ * F.f₁ := Finset.mem_range.1 ha'
  -- the inner index `b·D′ + a'` is below `D₂`, so it is the `% D₂` residue
  have hr : b * (F.e₁ * F.f₁) + a' < T.D₂ := by
    have hDD : T.D₂ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
    have : b * (F.e₁ * F.f₁) + (F.e₁ * F.f₁) ≤ T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by
      have : (b + 1) * (F.e₁ * F.f₁) ≤ T.e₂ * T.f₂ * (F.e₁ * F.f₁) :=
        Nat.mul_le_mul_right _ (by omega)
      calc b * (F.e₁ * F.f₁) + (F.e₁ * F.f₁) = (b + 1) * (F.e₁ * F.f₁) := by ring
        _ ≤ T.e₂ * T.f₂ * (F.e₁ * F.f₁) := this
    omega
  have hidx : j * T.D₂ + b * (F.e₁ * F.f₁) + a' < μ₂ * T.D₂ := by
    have : (j + 1) * T.D₂ ≤ μ₂ * T.D₂ := Nat.mul_le_mul_right _ (by omega)
    have hexp : (j + 1) * T.D₂ = j * T.D₂ + T.D₂ := by ring
    omega
  have hassoc : j * T.D₂ + b * (F.e₁ * F.f₁) + a' = j * T.D₂ + (b * (F.e₁ * F.f₁) + a') := by ring
  have hdiv : (j * T.D₂ + (b * (F.e₁ * F.f₁) + a')) / T.D₂ = j := by
    rw [Nat.mul_comm j T.D₂, Nat.mul_add_div hD₂, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hmod : (j * T.D₂ + (b * (F.e₁ * F.f₁) + a')) % T.D₂ = b * (F.e₁ * F.f₁) + a' := by
    rw [Nat.mul_comm j T.D₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hdiv2 : (b * (F.e₁ * F.f₁) + a') / (F.e₁ * F.f₁) = b := by
    rw [Nat.mul_comm b (F.e₁ * F.f₁), Nat.mul_add_div hD', Nat.div_eq_of_lt ha'', Nat.add_zero]
  have hmod2 : (b * (F.e₁ * F.f₁) + a') % (F.e₁ * F.f₁) = a' := by
    rw [Nat.mul_comm b (F.e₁ * F.f₁), Nat.mul_add_mod, Nat.mod_eq_of_lt ha'']
  rw [vext_of_lt _ hidx]
  congr 2
  simp only [digitVec, hassoc, hdiv, hmod, hdiv2, hmod2]

private theorem slotDig0_digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (a : Fin (μ₂ * T.D₂) → O)
    {j : ℕ} (hj : j < μ₂) :
    slotDig0 T (vext (digitVec T μ₂ a)) j = dev (composedKey T) (monicPoly a) j := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hkeypos : 0 < F.key.natDegree := by rw [F.hdeg]; exact hD'
  have hΦpos : 0 < (composedKey T).natDegree := by
    rw [composedKey_natDegree_D₂ T hπ]; exact hD₂pos T
  have hk : (dev (composedKey T) (monicPoly a) j).natDegree < (T.e₂ * T.f₂) * F.key.natDegree := by
    have h := natDegree_dev_lt' (composedKey_monic T) hΦpos (monicPoly a) j
    rw [composedKey_natDegree_D₂ T hπ] at h
    have hDD : T.D₂ = (T.e₂ * T.f₂) * F.key.natDegree := by rw [TowerDatum.D₂, F.hdeg]; ring
    omega
  rw [slotDig0]
  rw [Finset.sum_congr rfl fun b hb =>
    congrArg (fun P => P * F.key ^ b) (slotDig1_digitVec T a hj (Finset.mem_range.1 hb))]
  exact sum_dev_eq F.hmonic hkeypos (dev (composedKey T) (monicPoly a) j) hk

/-- **THE DICTIONARY, direction A.**  Reconstructing from the two-key digits of `monicPoly a`
returns `monicPoly a` on the nose — the exact identity in `O[X]`

  `monicPoly a = Φ₂^{μ₂} + ∑_{i < μ₂D₂} 𝔠ᵢ·X^{a'(i)}Φ′^{b(i)}Φ₂^{j(i)}`,   `𝔠 = digitVec T μ₂ a`,

with `deg (X^{a'}Φ′^{b}Φ₂^{j}) = i` exactly (`natDegree_slotMon`). -/
theorem slotPoly_digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (a : Fin (μ₂ * T.D₂) → O) :
    slotPoly T μ₂ (digitVec T μ₂ a) = monicPoly a := by
  have hD₂ : 0 < T.D₂ := hD₂pos T
  have hΦpos : 0 < (composedKey T).natDegree := by
    rw [composedKey_natDegree_D₂ T hπ]; exact hD₂
  have hfdeg : (monicPoly a).natDegree = μ₂ * (composedKey T).natDegree := by
    rw [monicPoly_natDegree, composedKey_natDegree_D₂ T hπ]
  have htop : dev (composedKey T) (monicPoly a) μ₂ = 1 :=
    dev_top (composedKey_monic T) hΦpos (monicPoly_monic a) hfdeg
  have hk : (monicPoly a).natDegree < (μ₂ + 1) * (composedKey T).natDegree := by
    rw [hfdeg]
    have : μ₂ * (composedKey T).natDegree < (μ₂ + 1) * (composedKey T).natDegree := by
      have hexp : (μ₂ + 1) * (composedKey T).natDegree
          = μ₂ * (composedKey T).natDegree + (composedKey T).natDegree := by ring
      omega
    exact this
  have hsum := sum_dev_eq (composedKey_monic T) hΦpos (monicPoly a) hk
  rw [Finset.sum_range_succ, htop, one_mul] at hsum
  rw [slotPoly_grouped,
    Finset.sum_congr rfl fun j hj =>
      congrArg (fun P => P * (composedKey T) ^ j)
        (slotDig0_digitVec T hπ a (Finset.mem_range.1 hj)),
    add_comm]
  exact hsum

/-- **THE DICTIONARY, direction A, in coordinates**: `polyVec ∘ digitVec = id`. -/
theorem polyVec_digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (a : Fin (μ₂ * T.D₂) → O) :
    polyVec T μ₂ (digitVec T μ₂ a) = a := by
  funext i
  rw [polyVec, slotPoly_digitVec T hπ a, monicPoly_coeff_val]

/-! ### The slot index bijection, and the digit-floor condition in flat form -/

private theorem slot_decode {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ i : ℕ} (hi : i < μ₂ * T.D₂) :
    i / T.D₂ < μ₂ ∧ i % T.D₂ % (F.e₁ * F.f₁) < F.e₁ * F.f₁
      ∧ i % T.D₂ / (F.e₁ * F.f₁) < T.e₂ * T.f₂ := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hD₂ : 0 < T.D₂ := hD₂pos T
  refine ⟨(Nat.div_lt_iff_lt_mul hD₂).2 hi, Nat.mod_lt _ hD', ?_⟩
  refine (Nat.div_lt_iff_lt_mul hD').2 ?_
  have hlt : i % T.D₂ < T.D₂ := Nat.mod_lt _ hD₂
  have hDD : T.D₂ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
  omega

private theorem slot_encode {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ j a' b : ℕ} (hj : j < μ₂) (ha' : a' < F.e₁ * F.f₁)
    (hb : b < T.e₂ * T.f₂) :
    j * T.D₂ + b * (F.e₁ * F.f₁) + a' < μ₂ * T.D₂
      ∧ (j * T.D₂ + b * (F.e₁ * F.f₁) + a') / T.D₂ = j
      ∧ (j * T.D₂ + b * (F.e₁ * F.f₁) + a') % T.D₂ % (F.e₁ * F.f₁) = a'
      ∧ (j * T.D₂ + b * (F.e₁ * F.f₁) + a') % T.D₂ / (F.e₁ * F.f₁) = b := by
  have hD' : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hD₂ : 0 < T.D₂ := hD₂pos T
  have hDD : T.D₂ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
  have hr : b * (F.e₁ * F.f₁) + a' < T.D₂ := by
    have h1 : (b + 1) * (F.e₁ * F.f₁) ≤ T.e₂ * T.f₂ * (F.e₁ * F.f₁) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (b + 1) * (F.e₁ * F.f₁) = b * (F.e₁ * F.f₁) + (F.e₁ * F.f₁) := by ring
    omega
  have hassoc : j * T.D₂ + b * (F.e₁ * F.f₁) + a' = j * T.D₂ + (b * (F.e₁ * F.f₁) + a') := by ring
  have hlt : j * T.D₂ + b * (F.e₁ * F.f₁) + a' < μ₂ * T.D₂ := by
    have h1 : (j + 1) * T.D₂ ≤ μ₂ * T.D₂ := Nat.mul_le_mul_right _ (by omega)
    have h2 : (j + 1) * T.D₂ = j * T.D₂ + T.D₂ := by ring
    omega
  have hmod : (j * T.D₂ + b * (F.e₁ * F.f₁) + a') % T.D₂ = b * (F.e₁ * F.f₁) + a' := by
    rw [hassoc, Nat.mul_comm j T.D₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  refine ⟨hlt, ?_, ?_, ?_⟩
  · rw [hassoc, Nat.mul_comm j T.D₂, Nat.mul_add_div hD₂, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [hmod, Nat.mul_comm b (F.e₁ * F.f₁), Nat.mul_add_mod, Nat.mod_eq_of_lt ha']
  · rw [hmod, Nat.mul_comm b (F.e₁ * F.f₁), Nat.mul_add_div hD', Nat.div_eq_of_lt ha',
      Nat.add_zero]

/-- **The triple-indexed digit-floor condition IS the flat per-slot condition on `digitVec`.**
This is the re-indexing half of C.53 leg 2, and it is TRUE: it is the slot bijection
`i ↔ (j, a', b)` of `budgetSlot`, nothing more. -/
private theorem digitFloors_iff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} (a : Fin (μ₂ * T.D₂) → O) :
    (∀ j a' b : ℕ, j < μ₂ → a' < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
        ((budgetFloor T μ₂ j a' b : ℕ) : ℕ∞)
          ≤ addVal O ((dev F.key (dev (composedKey T) (monicPoly a) j) b).coeff a'))
      ↔ ∀ i : Fin (μ₂ * T.D₂),
          ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (digitVec T μ₂ a i) := by
  constructor
  · intro h i
    obtain ⟨hj, ha', hb⟩ := slot_decode T i.isLt
    simpa only [budgetSlot, digitVec] using h _ _ _ hj ha' hb
  · intro h j a' b hj ha' hb
    obtain ⟨hlt, hdiv, hmodmod, hmoddiv⟩ := slot_encode T hj ha' hb
    have hh := h ⟨j * T.D₂ + b * (F.e₁ * F.f₁) + a', hlt⟩
    simp only [budgetSlot, digitVec, hdiv, hmodmod, hmoddiv] at hh
    exact hh

/-! ### The reconstruction descends to level `N`, and is a BIJECTION there

This is the honest replacement for the refuted "the digit box and the raw box cut out the same
classes" (see `C53_LEG2_REFUTED_2026-08-20.md`): the reconstruction `polyVec` is visibly affine
over `O`, hence descends to `slotClassMap` on `Coeff O n N`; `polyVec ∘ digitVec = id` makes that
descent surjective; `Coeff O n N` is finite, so it is a bijection.  No unitriangularity, no
matrix, no determinant — and, crucially, no claim that the box is preserved (it is not). -/

private theorem coeff_slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (u : Fin (μ₂ * T.D₂) → O) (m : ℕ) :
    (slotPoly T μ₂ u).coeff m
      = ((composedKey T) ^ μ₂).coeff m
        + ∑ i : Fin (μ₂ * T.D₂), u i * (slotMon T i.1).coeff m := by
  rw [slotPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Polynomial.coeff_C_mul _

private theorem polyVec_proj_congr [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ)
    {u u' : Fin (μ₂ * T.D₂) → O} (h : proj O (μ₂ * T.D₂) N u = proj O (μ₂ * T.D₂) N u') :
    proj O (μ₂ * T.D₂) N (polyVec T μ₂ u) = proj O (μ₂ * T.D₂) N (polyVec T μ₂ u') := by
  have hi : ∀ k : Fin (μ₂ * T.D₂),
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (u k)
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (u' k) := fun k => congrFun h k
  funext i
  simp only [proj, polyVec, coeff_slotPoly, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, hi k]

/-- the reconstruction map, descended to the level-`N` coefficient box. -/
private noncomputable def slotClassMap [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) :
    Coeff O (μ₂ * T.D₂) N → Coeff O (μ₂ * T.D₂) N :=
  fun c => proj O (μ₂ * T.D₂) N
    (polyVec T μ₂ (Classical.choose (proj_surjective O (μ₂ * T.D₂) N c)))

private theorem slotClassMap_apply [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) (u : Fin (μ₂ * T.D₂) → O) :
    slotClassMap T μ₂ N (proj O (μ₂ * T.D₂) N u)
      = proj O (μ₂ * T.D₂) N (polyVec T μ₂ u) :=
  polyVec_proj_congr T μ₂ N
    (Classical.choose_spec (proj_surjective O (μ₂ * T.D₂) N (proj O (μ₂ * T.D₂) N u)))

private theorem slotClassMap_surjective [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N : ℕ) :
    Function.Surjective (slotClassMap T μ₂ N) := by
  intro c
  obtain ⟨a, ha⟩ := proj_surjective O (μ₂ * T.D₂) N c
  refine ⟨proj O (μ₂ * T.D₂) N (digitVec T μ₂ a), ?_⟩
  rw [slotClassMap_apply, polyVec_digitVec T hπ a, ha]

private theorem slotClassMap_injective [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N : ℕ) :
    Function.Injective (slotClassMap T μ₂ N) :=
  Finite.injective_iff_surjective.2 (slotClassMap_surjective T hπ μ₂ N)

/-- **The CARD-level dictionary — the honest replacement for C.53's refuted leg 2.**

For ANY predicate `Q` on integral coefficient vectors, the level-`N` classes admitting a lift
whose TWO-KEY DIGITS satisfy `Q` are exactly as MANY as those admitting a lift whose RAW
coefficients satisfy `Q` — the two families of classes being a translate of one another under the
bijection `slotClassMap`.  They are NOT the same family: at `Q =` "clear the budget floors" the
sets genuinely differ (`C53_LEG2_REFUTED_2026-08-20.md`), which is exactly why this statement is
about `Nat.card` and not about membership. -/
theorem card_digitVec_transport [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (N : ℕ) (Q : (Fin (μ₂ * T.D₂) → O) → Prop) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧ Q (digitVec T μ₂ a)}
      = Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ u : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N u = c ∧ Q u} := by
  classical
  set f : {c : Coeff O (μ₂ * T.D₂) N //
      ∃ u : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N u = c ∧ Q u}
      → {c : Coeff O (μ₂ * T.D₂) N //
      ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧ Q (digitVec T μ₂ a)} :=
    fun x => ⟨slotClassMap T μ₂ N x.1, by
      obtain ⟨u, hu, hQ⟩ := x.2
      refine ⟨polyVec T μ₂ u, ?_, ?_⟩
      · rw [← hu, slotClassMap_apply]
      · rw [digitVec_polyVec T hπ hμ₂ u]; exact hQ⟩ with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : slotClassMap T μ₂ N x.1 = slotClassMap T μ₂ N y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (slotClassMap_injective T hπ μ₂ N h1)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hQ⟩ := y.2
    refine ⟨⟨proj O (μ₂ * T.D₂) N (digitVec T μ₂ a), ⟨digitVec T μ₂ a, rfl, hQ⟩⟩, ?_⟩
    refine Subtype.ext ?_
    show slotClassMap T μ₂ N (proj O (μ₂ * T.D₂) N (digitVec T μ₂ a)) = y.1
    rw [slotClassMap_apply, polyVec_digitVec T hπ a, ha]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

/-! ### NODE C.53 from LEG 1 ALONE -/

/-- **The signed conclusion of `towerLocus_fibration`, from leg 1 alone.**

`TowerBudgetIff` (leg 1 = C.52's signed `towerLocus_iff_budget`) is now the ONLY remaining input:
leg 2 (`TriangularDigitRead`) is eliminated, not reduced.  It had to be — it is FALSE
(`C53_LEG2_REFUTED_2026-08-20.md`).  What replaces it is `card_digitVec_transport`: the two-key
change of coordinates is measure-preserving without being box-preserving, and `towerLocus_fibration`
only ever needed the measure. -/
theorem towerLocus_fibration_of_leg1 [Finite (ResidueField O)] (hπ : Irreducible π)
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) {μ₂ : ℕ}
    (hμ₂ : 0 < μ₂) (N : ℕ) (h1 : TowerBudgetIff T μ₂) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O,
          proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂}
      = residueCard O ^ towerFreeCount T μ₂ N := by
  have hstep1 : ∀ c : Coeff O (μ₂ * T.D₂) N,
      (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂)
        ↔ (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
            ∀ i : Fin (μ₂ * T.D₂),
              ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (digitVec T μ₂ a i)) := by
    intro c
    constructor
    · rintro ⟨a, ha, hmem⟩
      exact ⟨a, ha, (digitFloors_iff T a).1
        ((h1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).1 hmem)⟩
    · rintro ⟨a, ha, hbud⟩
      exact ⟨a, ha, (h1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).2
        ((digitFloors_iff T a).2 hbud)⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hstep1),
    card_digitVec_transport T hπ hμ₂ N
      (fun u => ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (u i))]
  exact card_budgetBox hπ T μ₂ N

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.twoKeyMon
#print axioms Uniformity.Density.Tower.slotMon
#print axioms Uniformity.Density.Tower.slotPoly
#print axioms Uniformity.Density.Tower.digitVec
#print axioms Uniformity.Density.Tower.polyVec
#print axioms Uniformity.Density.Tower.composedKey_natDegree_D₂
#print axioms Uniformity.Density.Tower.digitVec_polyVec
#print axioms Uniformity.Density.Tower.slotPoly_digitVec
#print axioms Uniformity.Density.Tower.polyVec_digitVec
#print axioms Uniformity.Density.Tower.card_digitVec_transport
#print axioms Uniformity.Density.Tower.towerLocus_fibration_of_leg1

end AxCheck
