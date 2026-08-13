/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# UniformityCheck.Counting — the level-`N` counting infrastructure for the `n = 2` census

This file is pure counting bookkeeping over the level-`N` truncation `Res O N = O ⧸ 𝔪 ^ N`:

* `resPi π N` — the image of a uniformizer, and `dvd_res_iff`: inside the window,
  divisibility by `π ^ k` can be read either upstairs or downstairs;
* `dvdSet π k N` / `exactSet π k N` — the classes of valuation `≥ k` resp. exactly `k`, with
  their cardinalities `q ^ (N - k)` and `q ^ (N-k) - q ^ (N-k-1)`;
* `readEquiv γ` — the re-coordinatisation of a level-`N` coefficient class by the pair
  `(F(γ), F'(γ))` (value and derivative at the centre `γ`).  It is a bijection, which is the
  engine of every census here;
* **`card_certSet`** — THE CENSUS LEMMA. If a "certificate at a centre" is (i) a condition on
  `(F(γ), F'(γ))` alone, (ii) invariant under moving the centre inside `γ + 𝔪 ^ m`, and
  (iii) only satisfiable by centres in one such coset, then the number of certified classes is
  `q ^ m * #{admissible (V, D) pairs}`.

Everything is stated for an arbitrary discrete valuation ring with finite residue field.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

/-! ## 1. Divisibility inside the window -/

section Dvd

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The image of the uniformizer `π` in the level-`N` truncation. -/
def resPi (π : O) (N : ℕ) : Res O N := Ideal.Quotient.mk _ π

theorem resPi_pow {π : O} {N : ℕ} (k : ℕ) :
    resPi π N ^ k = (Ideal.Quotient.mk _ (π ^ k) : Res O N) := by
  rw [resPi, ← map_pow]

/-- **Inside the window, divisibility can be read downstairs.** -/
theorem dvd_res_iff {π : O} (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) (x : O) :
    resPi π N ^ k ∣ (Ideal.Quotient.mk _ x : Res O N) ↔ π ^ k ∣ x := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) z
    rw [resPi_pow, ← map_mul, Ideal.Quotient.eq] at hz
    have hmem := (mem_maximalIdeal_pow_iff_dvd hπ N _).1 hz
    have : π ^ k ∣ x - π ^ k * y :=
      dvd_trans (pow_dvd_pow π hk) hmem
    have hx : x = (x - π ^ k * y) + π ^ k * y := by ring
    rw [hx]
    exact dvd_add this ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨Ideal.Quotient.mk _ y, by rw [resPi_pow, ← map_mul]⟩

/-- The classes of valuation at least `k`. -/
def dvdSet (π : O) (k N : ℕ) : Set (Res O N) := {x | resPi π N ^ k ∣ x}

/-- The classes of valuation exactly `k`. -/
def exactSet (π : O) (k N : ℕ) : Set (Res O N) :=
  {x | resPi π N ^ k ∣ x ∧ ¬ resPi π N ^ (k + 1) ∣ x}

theorem exactSet_subset (π : O) (k N : ℕ) : exactSet π k N ⊆ dvdSet π k N := fun _ hx => hx.1

theorem dvdSet_succ_subset (π : O) (k N : ℕ) : dvdSet π (k + 1) N ⊆ dvdSet π k N :=
  fun _ hx => dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) hx

theorem exactSet_eq_diff (π : O) (k N : ℕ) :
    exactSet π k N = dvdSet π k N \ dvdSet π (k + 1) N := rfl

end Dvd

/-! ## 2. Cardinalities of the valuation strata -/

section Card

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The level-`k` truncation of the level-`N` classes has kernel exactly `dvdSet π k N`. -/
theorem dvdSet_eq_ker {π : O} (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) :
    dvdSet π k N = {x : Res O N | resFactor (O := O) hk x = 0} := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) x
  simp only [Set.mem_setOf_eq, dvdSet, resFactor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [dvd_res_iff hπ hk, mem_maximalIdeal_pow_iff_dvd hπ]

/-- **`#{v ≥ k} = q ^ (N - k)`**, in multiplicative form. -/
theorem card_dvdSet_mul {π : O} (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) :
    Nat.card (dvdSet π k N) * residueCard O ^ k = residueCard O ^ N := by
  classical
  set f : Res O N →+ Res O k := (resFactor (O := O) hk).toAddMonoidHom with hf
  have hsurj : Function.Surjective f := resFactor_surjective hk
  have hker : dvdSet π k N = (f.ker : Set (Res O N)) := by
    rw [dvdSet_eq_ker hπ hk]; rfl
  have h1 := card_preimage_of_surjective f hsurj (Set.univ : Set (Res O k))
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ, card_res, card_res] at h1
  rw [hker]
  have : Nat.card ((f.ker : Set (Res O N))) = Nat.card f.ker := rfl
  rw [this, h1]

theorem card_dvdSet {π : O} (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (dvdSet π k (k + r)) = residueCard O ^ r := by
  have h := card_dvdSet_mul hπ (k := k) (N := k + r) (Nat.le_add_right k r)
  have hq : 0 < residueCard O ^ k := pow_pos (residueCard_pos O) k
  have : residueCard O ^ (k + r) = residueCard O ^ r * residueCard O ^ k := by
    rw [← pow_add]; ring_nf
  rw [this] at h
  exact Nat.eq_of_mul_eq_mul_right hq h

/-- **`#{v = k} = q ^ (N-k) - q ^ (N-k-1)`**, in the subtraction-free form
`#{v = k} + q ^ r = q ^ (r+1)` at `N = k + r + 1`. -/
theorem card_exactSet_add {π : O} (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (exactSet π k (k + r + 1)) + residueCard O ^ r = residueCard O ^ (r + 1) := by
  classical
  have hsub : dvdSet π (k + 1) (k + r + 1) ⊆ dvdSet π k (k + r + 1) := dvdSet_succ_subset _ _ _
  have h1 : Nat.card (dvdSet π k (k + r + 1)) = residueCard O ^ (r + 1) := by
    have := card_dvdSet (π := π) hπ (k := k) (r := r + 1)
    rwa [show k + (r + 1) = k + r + 1 from by ring] at this
  have h2 : Nat.card (dvdSet π (k + 1) (k + r + 1)) = residueCard O ^ r := by
    have := card_dvdSet (π := π) hπ (k := k + 1) (r := r)
    rwa [show k + 1 + r = k + r + 1 from by ring] at this
  have h3 : (exactSet π k (k + r + 1)).ncard
      = (dvdSet π k (k + r + 1)).ncard - (dvdSet π (k + 1) (k + r + 1)).ncard := by
    rw [exactSet_eq_diff]
    exact Set.ncard_sdiff hsub (Set.toFinite _)
  have hle : (dvdSet π (k + 1) (k + r + 1)).ncard ≤ (dvdSet π k (k + r + 1)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Nat.card_coe_set_eq, h3, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h1, h2]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h1, h2] at hle
  omega

end Card

/-! ## 3. Re-coordinatising a class by `(F(γ), F'(γ))` -/

section Read

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {N : ℕ}

/-- **The centred reading of a level-`N` class.** A coefficient class `c = (c₀, c₁)` is carried
to the pair `(F(γ), F'(γ)) = (γ² + c₁γ + c₀, 2γ + c₁)` of value and derivative at `γ`. For each
fixed centre this is a bijection of the level-`N` box with `Res O N × Res O N`. -/
def readEquiv (γ : Res O N) : Coeff O 2 N ≃ Res O N × Res O N where
  toFun c := (c 0 + c 1 * γ + γ ^ 2, c 1 + 2 * γ)
  invFun p := ![p.1 + γ ^ 2 - p.2 * γ, p.2 - 2 * γ]
  left_inv c := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv p := by
    have h0 : (![p.1 + γ ^ 2 - p.2 * γ, p.2 - 2 * γ] : Coeff O 2 N) 0
        = p.1 + γ ^ 2 - p.2 * γ := rfl
    have h1 : (![p.1 + γ ^ 2 - p.2 * γ, p.2 - 2 * γ] : Coeff O 2 N) 1 = p.2 - 2 * γ := rfl
    ext <;> simp only [h0, h1] <;> ring

theorem readEquiv_proj (a : Fin 2 → O) (γ : O) :
    readEquiv (Ideal.Quotient.mk _ γ : Res O N) (proj O 2 N a)
      = (Ideal.Quotient.mk _ (qval a γ), Ideal.Quotient.mk _ (qder a γ)) := by
  have h0 : proj O 2 N a 0 = Ideal.Quotient.mk _ (a 0) := rfl
  have h1 : proj O 2 N a 1 = Ideal.Quotient.mk _ (a 1) := rfl
  ext
  · show proj O 2 N a 0 + proj O 2 N a 1 * _ + _ = _
    rw [h0, h1, qval, ← map_pow, ← map_mul, ← map_add, ← map_add]
    congr 1
    ring
  · show proj O 2 N a 1 + 2 * _ = _
    rw [h1, qder, ← map_ofNat (f := Ideal.Quotient.mk ((maximalIdeal O) ^ N)) 2, ← map_mul,
      ← map_add]
    congr 1
    ring

end Read

/-! ## 4. Sections of the truncation tower -/

section Section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- A set-theoretic section of the level-`N` → level-`m` truncation. -/
noncomputable def resSection {m N : ℕ} (h : m ≤ N) : Res O m → Res O N :=
  Function.surjInv (resFactor_surjective (O := O) h)

theorem resFactor_resSection {m N : ℕ} (h : m ≤ N) (x : Res O m) :
    resFactor (O := O) h (resSection h x) = x :=
  Function.surjInv_eq _ x

theorem resFactor_eq_iff_dvd {π : O} (hπ : Irreducible π) {m N : ℕ} (h : m ≤ N) (x y : O) :
    resFactor (O := O) h (Ideal.Quotient.mk _ x) = resFactor h (Ideal.Quotient.mk _ y)
      ↔ π ^ m ∣ (y - x) := by
  rw [resFactor_mk, resFactor_mk, Ideal.Quotient.eq, mem_maximalIdeal_pow_iff_dvd hπ]
  exact ⟨fun h => (dvd_sub_comm).1 h, fun h => (dvd_sub_comm).1 h⟩

end Section

/-! ## 5. THE CENSUS LEMMA -/

section Census

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **THE CENSUS LEMMA.** Let `cert γ c` be a "certificate at the centre `γ`" for level-`N`
classes which

* reads only the pair `(F(γ), F'(γ))`, through a fixed admissible set `S` (`hcert`);
* survives every move of the centre inside its coset mod `𝔪 ^ m` (`hshift`);
* forces all its centres into one such coset (`huniq`).

Then the certified classes number exactly `q ^ m * #S`: the centre contributes `q ^ m` and the
admissible data `#S`. -/
theorem card_certSet {N m : ℕ} (hm : m ≤ N) (S : Set (Res O N × Res O N))
    (cert : Res O N → Coeff O 2 N → Prop)
    (hcert : ∀ γ c, cert γ c ↔ readEquiv γ c ∈ S)
    (hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c)
    (huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ) :
    Nat.card {c : Coeff O 2 N | ∃ γ, cert γ c} = residueCard O ^ m * Nat.card S := by
  classical
  -- the parametrisation `(γ̄, (V, D)) ↦ the class read at the section representative of γ̄`
  set Ξ : Res O m × S → {c : Coeff O 2 N | ∃ γ, cert γ c} := fun p =>
    ⟨(readEquiv (resSection hm p.1)).symm p.2,
      ⟨resSection hm p.1, (hcert _ _).2 (by rw [Equiv.apply_symm_apply]; exact p.2.2)⟩⟩ with hΞ
  have hbij : Function.Bijective Ξ := by
    constructor
    · rintro ⟨g, p⟩ ⟨g', p'⟩ hpp
      have hc : (readEquiv (resSection hm g)).symm (p : Res O N × Res O N)
          = (readEquiv (resSection hm g')).symm (p' : Res O N × Res O N) := congrArg Subtype.val hpp
      have hcert1 : cert (resSection hm g) ((readEquiv (resSection hm g)).symm (p : Res O N × Res O N)) :=
        (hcert _ _).2 (by rw [Equiv.apply_symm_apply]; exact p.2)
      have hcert2 : cert (resSection hm g') ((readEquiv (resSection hm g)).symm (p : Res O N × Res O N)) := by
        refine (hcert _ _).2 ?_
        rw [hc, Equiv.apply_symm_apply]
        exact p'.2
      have hgg : g' = g := by
        have h := huniq _ _ _ hcert1 hcert2
        rwa [resFactor_resSection, resFactor_resSection] at h
      rw [hgg] at hc
      simp only [Prod.mk.injEq]
      exact ⟨hgg.symm, Subtype.ext ((readEquiv (resSection hm g)).symm.injective hc)⟩
    · rintro ⟨c, γ, hγ⟩
      refine ⟨(resFactor hm γ, ⟨readEquiv (resSection hm (resFactor hm γ)) c, ?_⟩), ?_⟩
      · refine (hcert _ _).1 (hshift γ _ c hγ ?_)
        rw [resFactor_resSection]
      · exact Subtype.ext (by simp only [hΞ, Equiv.symm_apply_apply])
  rw [← Nat.card_eq_of_bijective Ξ hbij, Nat.card_prod, card_res]

end Census

end UniformityCheck
