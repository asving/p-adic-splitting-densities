/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.Counting

/-!
# UniformityCheck.RamCensus — the exact level-`N` count of the RAMIFIED classes

The RAM certificate of `Drainage.lean` says: at some centre `γ` the value `F(γ)` has EXACT ODD
valuation `2j+1` and the derivative `F'(γ)` has valuation `≥ j+1`. This file proves that the
level-`N` classes carrying that certificate with a FIXED `j` number exactly

    (q - 1) * q ^ (2N - 2j - 2)          (`card_ramSet`, stated at `N = 2j+2+r`)

by feeding the census lemma of `Counting.lean` two facts about the centre:

* **shift** (`RamAt_shift`): the certificate survives any move of the centre inside
  `γ + 𝔪 ^ (j+1)` — the recentring identity `F(γ+δ) = F(γ) + F'(γ)δ + δ²` moves the value by
  something of valuation `≥ 2j+2`;
* **uniqueness** (`RamAt_uniq`): it survives nothing else — a move by `δ` of valuation `m ≤ j`
  makes `v(F(γ+δ)) = 2m` EVEN, and an even exact valuation cannot carry an odd certificate.
  The same computation shows `j` itself is determined by the class.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing

/-! ## 1. Valuation helpers -/

section Val

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Exact divisibility pins the exponent. -/
theorem exact_val_unique (hπ : Irreducible π) {x : O} {s t : ℕ}
    (h1 : π ^ s ∣ x) (h2 : ¬ π ^ (s + 1) ∣ x) (h3 : π ^ t ∣ x) (h4 : ¬ π ^ (t + 1) ∣ x) :
    s = t := by
  have e1 := addVal_eq_of_dvd_not_dvd hπ h1 h2
  have e2 := addVal_eq_of_dvd_not_dvd hπ h3 h4
  rw [e1] at e2
  exact_mod_cast e2

/-- Below a failing divisibility there is an exact one. -/
theorem exists_exact_val (hπ : Irreducible π) {x : O} {k : ℕ} (h : ¬ π ^ k ∣ x) :
    ∃ m, m < k ∧ π ^ m ∣ x ∧ ¬ π ^ (m + 1) ∣ x := by
  obtain ⟨m, hm⟩ := exists_addVal_eq (ne_zero_of_not_dvd h)
  refine ⟨m, ?_, (pow_dvd_iff_le hπ hm m).2 le_rfl, fun hc => ?_⟩
  · by_contra hlt
    exact h ((pow_dvd_iff_le hπ hm k).2 (by omega))
  · exact absurd ((pow_dvd_iff_le hπ hm (m + 1)).1 hc) (by omega)

/-- A square never has odd exact valuation: `v(δ) = m` gives `v(δ²) = 2m`. -/
theorem not_dvd_sq (hπ : Irreducible π) {δ : O} {m : ℕ} (h : ¬ π ^ (m + 1) ∣ δ) :
    ¬ π ^ (2 * m + 1) ∣ δ ^ 2 := by
  intro hc
  refine h (pow_dvd_right_of_mul hπ (x := δ) (y := δ) (m := m) (n := m + 1) ?_ h)
  rw [show m + (m + 1) = 2 * m + 1 from by ring, ← pow_two]
  exact hc

end Val

/-! ## 2. The RAM certificate upstairs, and the two centre lemmas -/

section RamAt

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The RAM certificate at the centre `γ` with parameter `j`** (upstairs, on an honest
coefficient vector): `v(F(γ)) = 2j+1` exactly, and `v(F'(γ)) ≥ j+1`. -/
def RamAt (π : O) (j : ℕ) (a : Fin 2 → O) (γ : O) : Prop :=
  π ^ (2 * j + 1) ∣ qval a γ ∧ ¬ π ^ (2 * j + 2) ∣ qval a γ ∧ π ^ (j + 1) ∣ qder a γ

/-- **Shift.** The certificate survives any move of the centre inside `γ + 𝔪 ^ (j+1)`. -/
theorem RamAt_shift {j : ℕ} {a : Fin 2 → O} {γ γ' : O} (h : RamAt π j a γ)
    (hδ : π ^ (j + 1) ∣ (γ' - γ)) : RamAt π j a γ' := by
  obtain ⟨hv1, hv2, hd⟩ := h
  obtain ⟨d, hd'⟩ := hδ
  have hγ' : γ' = γ + π ^ (j + 1) * d := by linear_combination hd'
  set M : O := qder a γ * (π ^ (j + 1) * d) + (π ^ (j + 1) * d) ^ 2 with hM
  have hshift : qval a γ' = qval a γ + M := by
    rw [hγ', qval_shift a γ _, hM]; ring
  have hmid : π ^ (2 * j + 2) ∣ M := by
    rw [hM]
    refine dvd_add ?_ ?_
    · obtain ⟨e, he⟩ := hd
      exact ⟨e * d, by rw [he]; ring⟩
    · exact ⟨d ^ 2, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hshift]
    exact dvd_add hv1 (dvd_trans (pow_dvd_pow π (by omega)) hmid)
  · rw [hshift]
    intro hc
    refine hv2 ?_
    have hback : qval a γ = (qval a γ + M) - M := by ring
    rw [hback]
    exact dvd_sub hc hmid
  · have : qder a γ' = qder a γ + 2 * (π ^ (j + 1) * d) := by rw [hγ']; exact qder_shift a γ _
    rw [this]
    exact dvd_add hd ⟨2 * d, by ring⟩

/-- **Uniqueness.** Two RAM certificates on the same coefficient vector have the same parameter
and centres in the same coset of `𝔪 ^ (j+1)`. -/
theorem RamAt_uniq (hπ : Irreducible π) {j j' : ℕ} {a : Fin 2 → O} {γ γ' : O}
    (h : RamAt π j a γ) (h' : RamAt π j' a γ') : j = j' ∧ π ^ (j + 1) ∣ (γ' - γ) := by
  obtain ⟨hv1, hv2, hd⟩ := h
  -- first: the centres are close
  have hclose : π ^ (j + 1) ∣ (γ' - γ) := by
    by_contra hcon
    obtain ⟨m, hmlt, hm1, hm2⟩ := exists_exact_val hπ hcon
    set δ := γ' - γ with hδ
    have hγ' : γ' = γ + δ := by rw [hδ]; ring
    have hshift : qval a γ' = qval a γ + qder a γ * δ + δ ^ 2 := by
      rw [hγ']; exact qval_shift a γ δ
    have hmul : π ^ (2 * m + 1) ∣ qder a γ * δ := by
      have hq : π ^ (m + 1) ∣ qder a γ := dvd_trans (pow_dvd_pow π (by omega)) hd
      have hmm := mul_dvd_mul hq hm1
      rwa [← pow_add, show m + 1 + m = 2 * m + 1 from by ring] at hmm
    -- `v(F(γ')) = 2m`, which is even
    have hlow : π ^ (2 * m) ∣ qval a γ' := by
      rw [hshift]
      refine dvd_add (dvd_add (dvd_trans (pow_dvd_pow π (by omega)) hv1)
        (dvd_trans (pow_dvd_pow π (by omega)) hmul)) ?_
      obtain ⟨f, hf⟩ := hm1
      exact ⟨f ^ 2, by rw [hf]; ring⟩
    have hhigh : ¬ π ^ (2 * m + 1) ∣ qval a γ' := by
      rw [hshift]
      intro hc
      refine not_dvd_sq hπ hm2 ?_
      have : δ ^ 2 = (qval a γ + qder a γ * δ + δ ^ 2) - (qval a γ + qder a γ * δ) := by ring
      rw [this]
      exact dvd_sub hc (dvd_add (dvd_trans (pow_dvd_pow π (by omega)) hv1) hmul)
    have := exact_val_unique hπ h'.1 h'.2.1 hlow hhigh
    omega
  -- then: the parameters agree, because both read the same exact valuation at `γ'`
  refine ⟨?_, hclose⟩
  have hj := RamAt_shift ⟨hv1, hv2, hd⟩ hclose
  have hjj := exact_val_unique hπ hj.1 hj.2.1 h'.1 h'.2.1
  omega

end RamAt

/-! ## 3. The certificate downstairs, and the census -/

section Census

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- The RAM certificate as a property of the level-`N` CLASS, read through `readEquiv`. -/
def RamCert (π : O) (j N : ℕ) (γ : Res O N) (c : Coeff O 2 N) : Prop :=
  readEquiv γ c ∈ (exactSet π (2 * j + 1) N) ×ˢ (dvdSet π (j + 1) N)

/-- The set of level-`N` classes carrying a RAM certificate with parameter `j`. -/
def ramSet (π : O) (j N : ℕ) : Set (Coeff O 2 N) := {c | ∃ γ, RamCert π j N γ c}

/-- Downstairs and upstairs agree, inside the window. -/
theorem ramCert_iff (hπ : Irreducible π) {j N : ℕ} (hN : 2 * j + 2 ≤ N) (a : Fin 2 → O) (γ : O) :
    RamCert π j N (Ideal.Quotient.mk _ γ) (proj O 2 N a) ↔ RamAt π j a γ := by
  rw [RamCert, readEquiv_proj]
  simp only [Set.mem_prod, exactSet, dvdSet, Set.mem_setOf_eq]
  rw [dvd_res_iff hπ (by omega), dvd_res_iff hπ (by omega), dvd_res_iff hπ (by omega)]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- Outside the window the family is empty (nothing can have exact valuation `≥ N`). -/
theorem ramSet_eq_empty (hπ : Irreducible π) {j N : ℕ} (hN : N ≤ 2 * j + 1) :
    ramSet π j N = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false, ramSet, Set.mem_setOf_eq]
  rintro ⟨γ, hγ⟩
  obtain ⟨⟨h1, h2⟩, -⟩ := hγ
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl
  have hzN : (resPi π N) ^ N = 0 := by
    rw [resPi_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hπm N
  have hz : (resPi π N) ^ (2 * j + 1) = 0 := by
    rw [show 2 * j + 1 = N + (2 * j + 1 - N) from by omega, pow_add, hzN, zero_mul]
  rw [hz, zero_dvd_iff] at h1
  exact h2 (h1 ▸ dvd_zero _)

/-- **THE RAM CENSUS.** At level `N = 2j+2+r` exactly `(q-1) q ^ (2j+2r+2)` classes carry the
RAM certificate with parameter `j`; stated subtraction-free. -/
theorem card_ramSet (hπ : Irreducible π) (j r : ℕ) :
    Nat.card (ramSet π j (2 * j + 2 + r)) + residueCard O ^ (2 * j + 2 * r + 2)
      = residueCard O ^ (2 * j + 2 * r + 3) := by
  classical
  set N := 2 * j + 2 + r with hN
  have hm : j + 1 ≤ N := by omega
  -- the census lemma
  have hcard : Nat.card (ramSet π j N)
      = residueCard O ^ (j + 1) *
          Nat.card ((exactSet π (2 * j + 1) N) ×ˢ (dvdSet π (j + 1) N)) := by
    refine card_certSet hm _ (RamCert π j N) (fun γ c => Iff.rfl) ?_ ?_
    · -- shift
      intro γ γ' c hc hgg
      obtain ⟨a, rfl⟩ := proj_surjective O 2 N c
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ'
      rw [ramCert_iff hπ (by omega)] at hc ⊢
      exact RamAt_shift hc (dvd_sub_comm.1 ((resFactor_eq_iff_dvd hπ hm g' g).1 hgg))
    · -- uniqueness
      intro γ γ' c hc hc'
      obtain ⟨a, rfl⟩ := proj_surjective O 2 N c
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ'
      rw [ramCert_iff hπ (by omega)] at hc hc'
      exact (resFactor_eq_iff_dvd hπ hm g' g).2
        (dvd_sub_comm.1 (RamAt_uniq hπ hc hc').2)
  -- evaluate the two factors
  have hprod : Nat.card ((exactSet π (2 * j + 1) N) ×ˢ (dvdSet π (j + 1) N))
      = Nat.card (exactSet π (2 * j + 1) N) * Nat.card (dvdSet π (j + 1) N) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  have hdvd : Nat.card (dvdSet π (j + 1) N) = residueCard O ^ (j + 1 + r) := by
    have := card_dvdSet (π := π) hπ (k := j + 1) (r := j + 1 + r)
    rwa [show j + 1 + (j + 1 + r) = N from by omega] at this
  have hex : Nat.card (exactSet π (2 * j + 1) N) + residueCard O ^ r = residueCard O ^ (r + 1) := by
    have := card_exactSet_add (π := π) hπ (k := 2 * j + 1) (r := r)
    rwa [show 2 * j + 1 + r + 1 = N from by omega] at this
  rw [hcard, hprod, hdvd]
  have hsplit : residueCard O ^ (2 * j + 2 * r + 2)
      = residueCard O ^ (j + 1) * residueCard O ^ (j + 1 + r) * residueCard O ^ r := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpow : residueCard O ^ (j + 1) * (Nat.card (exactSet π (2 * j + 1) N)
      * residueCard O ^ (j + 1 + r)) + residueCard O ^ (2 * j + 2 * r + 2)
      = residueCard O ^ (j + 1) * residueCard O ^ (j + 1 + r)
          * (Nat.card (exactSet π (2 * j + 1) N) + residueCard O ^ r) := by
    rw [hsplit]; ring
  rw [hpow, hex, ← pow_add, ← pow_add]
  congr 1
  omega

end Census

end UniformityCheck
