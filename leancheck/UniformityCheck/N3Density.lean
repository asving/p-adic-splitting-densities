/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity
import UniformityCheck.Counting
import UniformityCheck.AniCount
import UniformityCheck.N3Base
import UniformityCheck.N3Certs

/-!
# UniformityCheck.N3Density — turning `n = 3` certificates into density lower bounds

Three pieces of plumbing, then the two ramified families:

* **`decidedDensity_ge_of_inj`** — an injection of a finite type into the `σ`-decided level-`N`
  classes is a density lower bound `#A / q ^ (3N) ≤ decidedDensity`. (Only an injection is
  needed, never an exact cardinality, which is what makes the family bounds cheap.)
* **`proj3_dvd`** — two lifts of the same level-`N` class agree modulo `π ^ N` coefficientwise.
* **`bracket_five`** — the 5-type analogue of `leanfinal`'s `bracket_two_decided`: lower bounds on the
  five cubic types turn, through `sum_decidedDensity_le_one` (which is general in `n`), into an
  upper bound on each one.

and then the two families whose certificates live in `N3Certs`:

* `gate_linRam_lower` : `(q-1)² / q⁴ ≤ decidedDensity O 3 c3linRam`  (level 2, `q²(q-1)²` classes);
* `gate_split3_lower` : `1 / q⁹ ≤ decidedDensity O 3 c3split`         (level 3, one class);
* `gate_linInert_lower` : `1 / q³ ≤ decidedDensity O 3 c3linInert`    (level 1, one class —
  the sharpened count needs `CubicCount`, see `N3Gates`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Plumbing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Two lifts of the same level-`N` class agree modulo `π ^ N`, coefficientwise. -/
theorem proj3_dvd {π : O} (hπ : Irreducible π) {n N : ℕ} {a b : Fin n → O}
    (h : proj O n N a = proj O n N b) (i : Fin n) : π ^ N ∣ (b i - a i) := by
  have hi := congrFun h i
  rw [proj, proj, Ideal.Quotient.eq] at hi
  exact dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ N _).1 hi)

variable [IsAdicComplete (maximalIdeal O) O]

/-- **An injection into the decided classes is a density lower bound.** -/
theorem decidedDensity_ge_of_inj {n N : ℕ} {σ : FactorizationType} {A : Type*} [Finite A]
    (f : A → Coeff O n N) (hinj : Function.Injective f)
    (hf : ∀ x, DecidedAt O n σ N (f x)) :
    (Nat.card A : ℝ) / (residueCard O : ℝ) ^ (n * N) ≤ decidedDensity O n σ := by
  have hcard : Nat.card A ≤ decidedCount O n σ N := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨f x, hf x⟩ : decidedSet O n σ N)) (fun x y hxy => ?_)
    exact hinj (congrArg Subtype.val hxy)
  have hA : (Nat.card A : ℝ) ≤ (decidedCount O n σ N : ℝ) := by exact_mod_cast hcard
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos (O := O) _
  refine le_trans ?_ (decidedSeq_le_decidedDensity n σ N)
  rw [decidedSeq, div_le_div_iff₀ hq hq]
  nlinarith [hA, hq]

/-- **The 5-type bracket engine.** -/
theorem bracket_five {ls li lc lr lt : ℝ}
    (hs : ls ≤ decidedDensity O 3 c3split)
    (hi : li ≤ decidedDensity O 3 c3linInert)
    (hc : lc ≤ decidedDensity O 3 c3inert)
    (hr : lr ≤ decidedDensity O 3 c3linRam)
    (ht : lt ≤ decidedDensity O 3 c3ram) :
    decidedDensity O 3 c3split ≤ 1 - li - lc - lr - lt
    ∧ decidedDensity O 3 c3linInert ≤ 1 - ls - lc - lr - lt
    ∧ decidedDensity O 3 c3inert ≤ 1 - ls - li - lr - lt
    ∧ decidedDensity O 3 c3linRam ≤ 1 - ls - li - lc - lt
    ∧ decidedDensity O 3 c3ram ≤ 1 - ls - li - lc - lr := by
  classical
  have hsum : ∑ τ ∈ ({c3split, c3linInert, c3inert, c3linRam, c3ram} :
      Finset FactorizationType), decidedDensity O 3 τ ≤ 1 := sum_decidedDensity_le_one 3 _
  rw [Finset.sum_insert (by
      simp [c3split_ne_c3linInert, c3split_ne_c3inert, c3split_ne_c3linRam, c3split_ne_c3ram]),
    Finset.sum_insert (by
      simp [c3linInert_ne_c3inert, c3linInert_ne_c3linRam, c3linInert_ne_c3ram]),
    Finset.sum_insert (by simp [c3inert_ne_c3linRam, c3inert_ne_c3ram]),
    Finset.sum_insert (by simp [c3linRam_ne_c3ram]), Finset.sum_singleton] at hsum
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Plumbing

/-! ## The valuation strata used by the ramified families -/

section Strata

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The units of the level-`N` truncation: the complement of `dvdSet π 1 N`. -/
def unitSet (π : O) (N : ℕ) : Set (Res O N) := (dvdSet π 1 N)ᶜ

theorem card_dvdSet_two {π : O} (hπ : Irreducible π) :
    Nat.card (dvdSet π 1 2) = residueCard O := by
  have h := card_dvdSet (π := π) hπ (k := 1) (r := 1)
  simpa using h

theorem card_exactSet_two {π : O} (hπ : Irreducible π) :
    Nat.card (exactSet π 1 2) + 1 = residueCard O := by
  have h := card_exactSet_add (π := π) hπ (k := 1) (r := 0)
  simpa using h

theorem card_unitSet_two {π : O} (hπ : Irreducible π) :
    Nat.card (unitSet π 2) + residueCard O = residueCard O ^ 2 := by
  classical
  have hsplit : Nat.card (dvdSet π 1 2) + Nat.card (unitSet π 2) = Nat.card (Res O 2) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : Res O 2 => x ∈ dvdSet π 1 2))
  rw [card_res] at hsplit
  rw [card_dvdSet_two hπ] at hsplit
  omega

end Strata

/-! ## The families -/

section Families

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- Reading a level-2 stratum membership upstairs. -/
theorem dvd_of_mem_dvdSet {π : O} (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) {a : O}
    (h : (Ideal.Quotient.mk _ a : Res O N) ∈ dvdSet π k N) : π ^ k ∣ a :=
  (dvd_res_iff hπ hk a).1 h

/-- **LINEAR × RAMIFIED QUADRATIC, level 2.** Every class with `a₂` a unit, `a₁ ∈ 𝔪` and `a₀` of
exact valuation `1` is `{(1,1),(2,1)}`-decided. -/
theorem linRam_decided {π : O} (hπ : Irreducible π)
    (x : exactSet π 1 2) (y : dvdSet π 1 2) (z : unitSet π 2) :
    DecidedAt O 3 c3linRam 2 (![x.1, y.1, z.1] : Coeff O 3 2) := by
  intro b hb
  have hb0 : (Ideal.Quotient.mk _ (b 0) : Res O 2) = x.1 := congrFun hb 0
  have hb1 : (Ideal.Quotient.mk _ (b 1) : Res O 2) = y.1 := congrFun hb 1
  have hb2 : (Ideal.Quotient.mk _ (b 2) : Res O 2) = z.1 := congrFun hb 2
  have h0 : b 0 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have := (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 0)).1 (by rw [hb0]; exact x.2.1)
    simpa using this
  have h0' : b 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    refine x.2.2 ?_
    rw [← hb0]
    exact (dvd_res_iff hπ (k := 2) (N := 2) (by omega) (b 0)).2
      ((mem_maximalIdeal_pow_iff_dvd hπ 2 _).1 hmem)
  have h1 : b 1 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have := (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 1)).1 (by rw [hb1]; exact y.2)
    simpa using this
  have h2 : IsUnit (b 2) := by
    refine notMem_maximalIdeal.1 (fun hmem => z.2 ?_)
    show resPi π 2 ^ 1 ∣ z.1
    rw [← hb2]
    exact (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 2)).2
      (by simpa using (mem_maximalIdeal_iff_dvd hπ _).1 hmem)
  exact typeOf_linRam_of_residue h2 h1 h0 h0'

/-- **G-LINRAM.** `(q-1)² / q⁴ ≤ decidedDensity O 3 c3linRam`. -/
theorem gate_linRam_lower :
    ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4
      ≤ decidedDensity O 3 c3linRam := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hbound := decidedDensity_ge_of_inj (O := O) (n := 3) (N := 2) (σ := c3linRam)
    (A := (exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2))
    (fun p => ![p.1.1, p.2.1.1, p.2.2.1])
    (by
      rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext h2)))
    (fun p => linRam_decided hπ p.1 p.2.1 p.2.2)
  have hq2 : (2 : ℕ) ≤ residueCard O := two_le_residueCard O
  have hcards : Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2))
      = Nat.card (exactSet π 1 2) * (Nat.card (dvdSet π 1 2) * Nat.card (unitSet π 2)) := by
    rw [Nat.card_prod, Nat.card_prod]
  have he := card_exactSet_two (O := O) hπ
  have hd := card_dvdSet_two (O := O) hπ
  have hu := card_unitSet_two (O := O) hπ
  have hE : Nat.card (exactSet π 1 2) = residueCard O - 1 := by omega
  have hU : Nat.card (unitSet π 2) = residueCard O ^ 2 - residueCard O := by omega
  have hq1 : (1 : ℕ) ≤ residueCard O := by omega
  have hqq : residueCard O ≤ residueCard O ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcast : (Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2)) : ℝ)
      = ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ 2 := by
    rw [hcards, hd, hE, hU]
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqq]
    ring
  rw [hcast] at hbound
  refine le_trans (le_of_eq ?_) hbound
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [show (3 : ℕ) * 2 = 6 from rfl]
  field_simp

/-- **THREE LINEAR FACTORS, level 3 (deep).** The single class of `X(X-1)(X-π)`. -/
theorem split3_decided {π : O} (hπ : Irreducible π) :
    DecidedAt O 3 c3split 3 (proj O 3 3 ![0, π, -(1 + π)]) := by
  intro b hb
  have hd := proj3_dvd (O := O) hπ (n := 3) (N := 3) hb.symm
  refine typeOf_split3_of_deep hπ ?_ ?_ ?_
  · simpa using (hd 0)
  · simpa using (hd 1)
  · have := hd 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    have hid : b 2 + (1 + π) = b 2 - -(1 + π) := by ring
    rw [hid]; exact this

/-- **G-SPLIT3.** `1 / q⁹ ≤ decidedDensity O 3 c3split`, every `O`. -/
theorem gate_split3_lower : 1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h := decidedDensity_ge_of_decided (split3_decided hπ)
  simpa using h

/-! ### Linear × inert quadratic: one class, from the existence of an anisotropic pair -/

theorem exists_aniK (K : Type*) [Field K] [Finite K] : ∃ p : K × K, AniK p := by
  by_contra hcon
  have hempty : IsEmpty {p : K × K // AniK p} := ⟨fun p => hcon ⟨p.1, p.2⟩⟩
  have h0 : Nat.card {p : K × K // AniK p} = 0 := by
    rw [Nat.card_eq_zero]; exact Or.inl hempty
  have h := two_mul_card_aniK K
  rw [h0, mul_zero, zero_add] at h
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  nlinarith [h, h2]

/-- **LINEAR × INERT QUADRATIC, level 1.** -/
theorem linInert_decided (ρ β₀ β₁ : O) (hani : Anisotropic ![β₀, β₁]) :
    DecidedAt O 3 c3linInert 1 (proj O 3 1 ![-(ρ * β₀), β₀ - ρ * β₁, β₁ - ρ]) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  intro b hb
  have hd := proj3_dvd (O := O) hπ (n := 3) (N := 1) hb.symm
  have hmem : ∀ i : Fin 3, b i - (![-(ρ * β₀), β₀ - ρ * β₁, β₁ - ρ] : Fin 3 → O) i
      ∈ maximalIdeal O := by
    intro i
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    simpa using hd i
  refine typeOf_linInert_of_residue ρ β₀ β₁ hani ?_ ?_ ?_
  · have := hmem 2; simpa using this
  · have := hmem 1; simpa using this
  · have := hmem 0
    simp only [Matrix.cons_val_zero] at this
    have hid : b 0 + ρ * β₀ = b 0 - -(ρ * β₀) := by ring
    rw [hid]; exact this

/-- **G-LININERT (crude).** `1 / q³ ≤ decidedDensity O 3 c3linInert`, every `O`. -/
theorem gate_linInert_lower : 1 / (residueCard O : ℝ) ^ 3 ≤ decidedDensity O 3 c3linInert := by
  obtain ⟨p, hp⟩ := exists_aniK (ResidueField O)
  obtain ⟨β₀, hβ₀⟩ := IsLocalRing.residue_surjective (R := O) p.1
  obtain ⟨β₁, hβ₁⟩ := IsLocalRing.residue_surjective (R := O) p.2
  have hani : Anisotropic ![β₀, β₁] := by
    rw [anisotropic_iff_aniK, hβ₀, hβ₁]
    exact hp
  have h := decidedDensity_ge_of_decided (linInert_decided (O := O) 0 β₀ β₁ hani)
  simpa using h

end Families

end UniformityCheck
