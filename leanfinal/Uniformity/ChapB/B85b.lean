/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B85b — the `q = 3` witnesses with `e > 1` **and** `f > 1`

**Chapter B, NODE B.85 instances (iii)+(iv)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10),
ENV-C concrete. One signed declaration: `gate_ef_three` (a conjunction of the two instances).

*The instances.* `O := ℤ_[3]`, `π := 3`, key `φ = X² + 1` (`m = 2`, irreducible over `𝔽₃`),
window `N = 2`:

| | `f` | `a` | `μ` | `dev` | polygon | value | `n` |
|---|---|---|---|---|---|---|---|
| (iii) | `(X²+1)² − 3` | `![−2, 0, 2, 0]` | `2` | `(−3, 0, 1)` | side `(1,2)`, argmin `{0,2}`, `d = 1` | `⟨{(2,2)}⟩` | `4` |
| (iv) | `(X²+1)³ − 3` | `![−2, 0, 3, 0, 3, 0]` | `3` | `(−3, 0, 0, 1)` | side `(1,3)`, argmin `{0,3}`, `d = 1` | `⟨{(3,2)}⟩` | `6` |

The `q = 3` mirror of B.85 (i)+(ii): same genres, same values, all arithmetic recomputed
`3`-adically (`3 ∣ −3`, `9 ∤ −3`; `𝔽₃`-irreducibility of `X² + 1`). Both leaves have
`e = ℓ ∈ {2,3} > 1` **and** `f = m·d = 2 > 1` simultaneously, with `d = 1`, so both sit in D-3's
unconditional row — **no `B-BOX-1`**. Degree conservation: `e·f = 4` resp. `6 = deg f`.

*Development gaps.* `dev φ f j = 0` for `0 < j < μ`; the finite-height support is `{0, μ}` and
the read goes through the kit's `polygon_read_set`.

## The A-F.12 discharge — the height form

Exactly as at `q = 2`: the degree display `ℓ · 2 · deg ψ ≤ n` leaves `ℓ = 1, deg ψ = 2` open, and
the kit's `perim_height_bound` closes it uniformly in the window-class member:

```
npHgt φ gS 0 = u · deg ψ      (from ḡS = φ̄ ^ k, k ≥ 1, and purity at abscissa 0)
1 ≤ u · deg ψ ≤ npHgt φ f 0 = 1        ⟹      deg ψ = 1
```

— the SECOND disjunct at every `(u, ℓ, gS)`, `B-BOX-1`-free.

DEPENDS (direct): B.06 · B.08 · B.20 · B.30 · B.33 · B.35b · B.66 · B.66a · B.73 · B.75 · B.76 ·
**B.82** · `B83Kit` · landed `LocalData.lean` §6 · mathlib `PadicInt.prime_p`,
`PadicInt.residueField`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `EFF.W12.29`'s `σ(λ)` rows at `e ∈ {2,3}`, `f = 2` → **Lean theorem**, now at the
second prime; `HE6-T-BADKEY` → **Lean theorem**; `W12-ORACLE` → **executable regression**
retained.

SOURCE: `EFF.W12.29`; `EFF.HE3.33`; `EFF.HE6.52`; DECISION D-3;
`blueprint/CONVENTIONS_2026-08-15.md` GC-11.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private theorem hpi3 : Irreducible (3 : ℤ_[3]) := (PadicInt.prime_p (p := 3)).irreducible

/-! ### the shared key `φ = X² + X + 1` -/

private noncomputable abbrev kQ : Polynomial ℤ_[3] := X ^ 2 + 1

private theorem hkmon : kQ.Monic := by unfold kQ; monicity!
private theorem hkdeg : kQ.natDegree = 2 := by unfold kQ; compute_degree!
private theorem hkdegW : kQ.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree hkmon.ne_zero, hkdeg]; rfl

private theorem hkirr : Irreducible (kQ.map (IsLocalRing.residue ℤ_[3])) := by
  set e := PadicInt.residueField (p := 3) with he
  have hmap : (kQ.map (IsLocalRing.residue ℤ_[3])).map (e : ResidueField ℤ_[3] →+* ZMod 3)
      = X ^ 2 + 1 := by unfold kQ; simp
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hkmon.natDegree_map, hkdeg]; decide
  · intro x hx
    have h1 : ((kQ.map (IsLocalRing.residue ℤ_[3])).map
        (e : ResidueField ℤ_[3] →+* ZMod 3)).eval (e x)
        = e ((kQ.map (IsLocalRing.residue ℤ_[3])).eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom (e : ResidueField ℤ_[3] →+* ZMod 3) x
    rw [hmap, hx] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_zero] at h1
    revert h1
    generalize (e x) = y
    revert y
    decide

private theorem hkey : IsKey kQ := ⟨hkmon, by rw [hkdeg]; norm_num, hkirr⟩

private theorem hdegC : (C (-3 : ℤ_[3]) : Polynomial ℤ_[3]).degree < kQ.degree :=
  lt_of_le_of_lt Polynomial.degree_C_le (by rw [hkdegW]; decide)
private theorem hdeg0 : (0 : Polynomial ℤ_[3]).degree < kQ.degree := by
  rw [Polynomial.degree_zero, hkdegW]; exact WithBot.bot_lt_coe 2
private theorem hdeg1 : (1 : Polynomial ℤ_[3]).degree < kQ.degree := by
  rw [Polynomial.degree_one, hkdegW]; decide

private theorem hnpm2 : IsDiscreteValuationRing.addVal ℤ_[3] (-3 : ℤ_[3]) = ((1 : ℕ) : ℕ∞) :=
  GateKit.padic_addVal (p := 3) (k := 1) (a := -3) (by norm_num) (by norm_num) (by norm_num)

/-! ### instance (i) : the quartic `φ² − 2` -/

private noncomputable abbrev a4 : Fin 4 → ℤ_[3] := ![-2, 0, 2, 0]
private noncomputable abbrev f4 : Polynomial ℤ_[3] := Uniformity.Density.monicPoly a4

private theorem hf4deg : f4.natDegree = 4 := Uniformity.Density.monicPoly_natDegree a4
private theorem hf4mon : f4.Monic := Uniformity.Density.monicPoly_monic a4
private theorem hf4degmu : f4.natDegree = 2 * kQ.natDegree := by rw [hf4deg, hkdeg]

private theorem hf4eq : f4 = C (-3) + 0 * kQ + 1 * kQ ^ 2 := by
  simp [Uniformity.Density.monicPoly, f4, a4, kQ, Fin.sum_univ_four, map_ofNat]
  ring

private theorem hdev4 : dev kQ f4 0 = C (-3) ∧ dev kQ f4 1 = 0 ∧ dev kQ f4 2 = 1 :=
  GateKit.dev_three hkmon (by rw [hkdeg]; norm_num) hdegC hdeg0 hdeg1 hf4eq

private theorem hres4 : f4.map (IsLocalRing.residue ℤ_[3])
    = (kQ.map (IsLocalRing.residue ℤ_[3])) ^ 2 := by
  have hm2 : IsLocalRing.residue ℤ_[3] (-3) = 0 := by
    rw [map_neg]
    refine neg_eq_zero.2 (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hpi3.maximalIdeal_eq, Ideal.mem_span_singleton]
  rw [hf4eq, zero_mul, add_zero, one_mul, Polynomial.map_add, Polynomial.map_C, hm2,
    Polynomial.C_0, zero_add, Polynomial.map_pow]

private theorem hfin4 : ∀ j ∈ ({0, 2} : Finset ℕ),
    npHgt kQ f4 j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [npHgt, hdev4.1, GateKit.gaussVal_C, hnpm2]; norm_num
  · rw [npHgt, hdev4.2.2, show (1 : Polynomial ℤ_[3]) = C 1 from (Polynomial.C_1).symm,
      GateKit.gaussVal_C, GateKit.addVal_one hpi3]
    norm_num

private theorem htop4 : ∀ j, j ∉ ({0, 2} : Finset ℕ) → npHgt kQ f4 j = ⊤ := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  by_cases h1 : j = 1
  · subst h1
    rw [npHgt, hdev4.2.1]
    exact gaussVal_eq_top_iff.2 rfl
  · refine GateKit.npHgt_eq_top_of_lt hkmon (by rw [hkdeg]; norm_num) f4 ?_
    rw [hf4deg, hkdeg]
    omega

private theorem hB4 : ∀ j, j ≤ f4.natDegree → (npHgt kQ f4 j).toNat ≤ 1 := by
  intro j _
  by_cases hj : j ∈ ({0, 2} : Finset ℕ)
  · rw [hfin4 j hj]
    by_cases h : j = 0 <;> simp [h]
  · rw [htop4 j hj]; decide

private theorem hread4 : suppVal kQ f4 1 2 = ((2 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet kQ f4 1 2 ↔
      (j ∈ ({0, 2} : Finset ℕ) ∧ 2 * (if j = 0 then 1 else 0) + 1 * j = 2)) :=
  GateKit.polygon_read_set (n := 4) hf4deg (by decide) hfin4 htop4 (by norm_num)
    (M := 2) (by decide) (by decide)

private theorem hside4 : sideSet kQ f4 1 2 = {0, 2} := by
  ext j
  rw [hread4.2 j]
  constructor
  · rintro ⟨hj, _⟩; exact hj
  · intro hj
    refine ⟨hj, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> norm_num

private theorem hcard4 : 1 < (sideSet kQ f4 1 2).card := by rw [hside4]; decide

private theorem hsdeg4 : ∀ hne : (sideSet kQ f4 1 2).Nonempty, sideDeg kQ f4 1 2 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hside4]; decide)
      (by intro j hj; rw [hside4] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 2) (by rw [hside4]; decide)
      (by intro j hj; rw [hside4] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslope4 : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet kQ f4 u ℓ).card → u = 1 ∧ ℓ = 2 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ := GateKit.slope_bounds_of_le hkey hf4mon hf4degmu hℓ hcop hcard hB4
  rw [hf4deg] at hℓle
  have kill : ∀ (u ℓ M j₀ : ℕ), 0 < ℓ →
      (∀ j ∈ ({0, 2} : Finset ℕ), M ≤ ℓ * (if j = 0 then 1 else 0) + u * j) →
      (∃ j ∈ ({0, 2} : Finset ℕ), ℓ * (if j = 0 then 1 else 0) + u * j = M) →
      (∀ j ∈ ({0, 2} : Finset ℕ), ℓ * (if j = 0 then 1 else 0) + u * j = M → j = j₀) →
      (sideSet kQ f4 u ℓ).card ≤ 1 := by
    intro u ℓ M j₀ hl hle hmem huniq
    have hread := GateKit.polygon_read_set (n := 4) hf4deg (by decide) hfin4 htop4 hl
      (M := M) hle hmem
    exact Finset.card_le_one.2 fun a ha b hb => by
      obtain ⟨ha1, ha2⟩ := (hread.2 a).1 ha
      obtain ⟨hb1, hb2⟩ := (hread.2 b).1 hb
      rw [huniq a ha1 ha2, huniq b hb1 hb2]
  interval_cases ℓ
  · interval_cases u
    · exfalso; have := kill 0 1 0 2 (by norm_num) (by decide) (by decide) (by decide); omega
    · exfalso; have := kill 1 1 1 0 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exact ⟨rfl, rfl⟩
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 3 2 2 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 4 2 2 (by norm_num) (by decide) (by decide) (by decide); omega

private theorem hslopeFinset4 : slopeFinset (3 : ℤ_[3]) kQ f4 = {(1, 2)} := by
  ext p
  rw [mem_slopeFinset hkey hf4mon hf4degmu]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslope4 p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcard4⟩

private theorem hord4 : order1Type (3 : ℤ_[3]) kQ f4 = ⟨{(2, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 hkey hf4mon hf4degmu (by
    intro p hp hne
    rw [hslopeFinset4, Finset.mem_singleton] at hp
    subst hp
    exact hsdeg4 hne)
  rw [hslopeFinset4, hkdeg] at h
  rw [h]
  rfl

private theorem hterm4 : ¬ NeedsDescent (3 : ℤ_[3]) kQ f4 := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 hkey hf4mon hf4degmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslope4 u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg4 hne

private theorem hvis4 : Visible (3 : ℤ_[3]) kQ f4 2 := by
  refine ⟨0, ?_⟩
  rw [hdev4.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 3) (a := -3) (by norm_num) (by norm_num)

private theorem hnp4zero : npHgt kQ f4 0 = ((1 : ℕ) : ℕ∞) := by
  rw [npHgt, hdev4.1, GateKit.gaussVal_C, hnpm2]

private theorem hperim4 : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = f4.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (f4 - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure kQ gS u ℓ →
    ∀ hne : (sideSet kQ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kQ gS (sideMin kQ gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kQ), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kQ)ˣ, resPoly (3 : ℤ_[3]) kQ gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kQ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kQ.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  obtain ⟨hlo, hhi⟩ := GateKit.perim_height_bound hpi3 hkey (N := 2) hres4 hvis4 hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hψm hψi hc hnp4zero
  have he : u * ψ.natDegree = 1 := le_antisymm hhi hlo
  exact Nat.dvd_one.mp ⟨u, by rw [← he]; ring⟩

/-! ### instance (ii) : the sextic `φ³ − 2` -/

private noncomputable abbrev a6 : Fin 6 → ℤ_[3] := ![-2, 0, 3, 0, 3, 0]
private noncomputable abbrev f6 : Polynomial ℤ_[3] := Uniformity.Density.monicPoly a6

private theorem hf6deg : f6.natDegree = 6 := Uniformity.Density.monicPoly_natDegree a6
private theorem hf6mon : f6.Monic := Uniformity.Density.monicPoly_monic a6
private theorem hf6degmu : f6.natDegree = 3 * kQ.natDegree := by rw [hf6deg, hkdeg]

private theorem hf6eq : f6 = C (-3) + 0 * kQ + 0 * kQ ^ 2 + 1 * kQ ^ 3 := by
  simp [Uniformity.Density.monicPoly, f6, a6, kQ, Fin.sum_univ_six, map_ofNat]
  ring

private theorem hdev6 : dev kQ f6 0 = C (-3) ∧ dev kQ f6 1 = 0 ∧ dev kQ f6 2 = 0
    ∧ dev kQ f6 3 = 1 :=
  GateKit.dev_four hkmon (by rw [hkdeg]; norm_num) hdegC hdeg0 hdeg0 hdeg1 hf6eq

private theorem hres6 : f6.map (IsLocalRing.residue ℤ_[3])
    = (kQ.map (IsLocalRing.residue ℤ_[3])) ^ 3 := by
  have hm2 : IsLocalRing.residue ℤ_[3] (-3) = 0 := by
    rw [map_neg]
    refine neg_eq_zero.2 (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hpi3.maximalIdeal_eq, Ideal.mem_span_singleton]
  rw [hf6eq, zero_mul, add_zero, zero_mul, add_zero, one_mul, Polynomial.map_add,
    Polynomial.map_C, hm2, Polynomial.C_0, zero_add, Polynomial.map_pow]

private theorem hfin6 : ∀ j ∈ ({0, 3} : Finset ℕ),
    npHgt kQ f6 j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [npHgt, hdev6.1, GateKit.gaussVal_C, hnpm2]; norm_num
  · rw [npHgt, hdev6.2.2.2, show (1 : Polynomial ℤ_[3]) = C 1 from (Polynomial.C_1).symm,
      GateKit.gaussVal_C, GateKit.addVal_one hpi3]
    norm_num

private theorem htop6 : ∀ j, j ∉ ({0, 3} : Finset ℕ) → npHgt kQ f6 j = ⊤ := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  by_cases h1 : j = 1
  · subst h1; rw [npHgt, hdev6.2.1]; exact gaussVal_eq_top_iff.2 rfl
  by_cases h2 : j = 2
  · subst h2; rw [npHgt, hdev6.2.2.1]; exact gaussVal_eq_top_iff.2 rfl
  · refine GateKit.npHgt_eq_top_of_lt hkmon (by rw [hkdeg]; norm_num) f6 ?_
    rw [hf6deg, hkdeg]
    omega

private theorem hB6 : ∀ j, j ≤ f6.natDegree → (npHgt kQ f6 j).toNat ≤ 1 := by
  intro j _
  by_cases hj : j ∈ ({0, 3} : Finset ℕ)
  · rw [hfin6 j hj]
    by_cases h : j = 0 <;> simp [h]
  · rw [htop6 j hj]; decide

private theorem hread6 : suppVal kQ f6 1 3 = ((3 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet kQ f6 1 3 ↔
      (j ∈ ({0, 3} : Finset ℕ) ∧ 3 * (if j = 0 then 1 else 0) + 1 * j = 3)) :=
  GateKit.polygon_read_set (n := 6) hf6deg (by decide) hfin6 htop6 (by norm_num)
    (M := 3) (by decide) (by decide)

private theorem hside6 : sideSet kQ f6 1 3 = {0, 3} := by
  ext j
  rw [hread6.2 j]
  constructor
  · rintro ⟨hj, _⟩; exact hj
  · intro hj
    refine ⟨hj, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> norm_num

private theorem hcard6 : 1 < (sideSet kQ f6 1 3).card := by rw [hside6]; decide

private theorem hsdeg6 : ∀ hne : (sideSet kQ f6 1 3).Nonempty, sideDeg kQ f6 1 3 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hside6]; decide)
      (by intro j hj; rw [hside6] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 3) (by rw [hside6]; decide)
      (by intro j hj; rw [hside6] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslope6 : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet kQ f6 u ℓ).card → u = 1 ∧ ℓ = 3 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ := GateKit.slope_bounds_of_le hkey hf6mon hf6degmu hℓ hcop hcard hB6
  rw [hf6deg] at hℓle
  have kill : ∀ (u ℓ M j₀ : ℕ), 0 < ℓ →
      (∀ j ∈ ({0, 3} : Finset ℕ), M ≤ ℓ * (if j = 0 then 1 else 0) + u * j) →
      (∃ j ∈ ({0, 3} : Finset ℕ), ℓ * (if j = 0 then 1 else 0) + u * j = M) →
      (∀ j ∈ ({0, 3} : Finset ℕ), ℓ * (if j = 0 then 1 else 0) + u * j = M → j = j₀) →
      (sideSet kQ f6 u ℓ).card ≤ 1 := by
    intro u ℓ M j₀ hl hle hmem huniq
    have hread := GateKit.polygon_read_set (n := 6) hf6deg (by decide) hfin6 htop6 hl
      (M := M) hle hmem
    exact Finset.card_le_one.2 fun a ha b hb => by
      obtain ⟨ha1, ha2⟩ := (hread.2 a).1 ha
      obtain ⟨hb1, hb2⟩ := (hread.2 b).1 hb
      rw [huniq a ha1 ha2, huniq b hb1 hb2]
  interval_cases ℓ
  · interval_cases u
    · exfalso; have := kill 0 1 0 3 (by norm_num) (by decide) (by decide) (by decide); omega
    · exfalso; have := kill 1 1 1 0 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 2 2 0 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exact ⟨rfl, rfl⟩
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 4 3 3 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 5 3 3 (by norm_num) (by decide) (by decide) (by decide); omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso; have := kill 1 6 3 3 (by norm_num) (by decide) (by decide) (by decide); omega

private theorem hslopeFinset6 : slopeFinset (3 : ℤ_[3]) kQ f6 = {(1, 3)} := by
  ext p
  rw [mem_slopeFinset hkey hf6mon hf6degmu]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslope6 p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcard6⟩

private theorem hord6 : order1Type (3 : ℤ_[3]) kQ f6 = ⟨{(3, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 hkey hf6mon hf6degmu (by
    intro p hp hne
    rw [hslopeFinset6, Finset.mem_singleton] at hp
    subst hp
    exact hsdeg6 hne)
  rw [hslopeFinset6, hkdeg] at h
  rw [h]
  rfl

private theorem hterm6 : ¬ NeedsDescent (3 : ℤ_[3]) kQ f6 := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 hkey hf6mon hf6degmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslope6 u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg6 hne

private theorem hvis6 : Visible (3 : ℤ_[3]) kQ f6 2 := by
  refine ⟨0, ?_⟩
  rw [hdev6.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 3) (a := -3) (by norm_num) (by norm_num)

private theorem hnp6zero : npHgt kQ f6 0 = ((1 : ℕ) : ℕ∞) := by
  rw [npHgt, hdev6.1, GateKit.gaussVal_C, hnpm2]

private theorem hperim6 : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = f6.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (f6 - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure kQ gS u ℓ →
    ∀ hne : (sideSet kQ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kQ gS (sideMin kQ gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kQ), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kQ)ˣ, resPoly (3 : ℤ_[3]) kQ gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kQ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kQ.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  obtain ⟨hlo, hhi⟩ := GateKit.perim_height_bound hpi3 hkey (N := 2) hres6 hvis6 hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hψm hψi hc hnp6zero
  have he : u * ψ.natDegree = 1 := le_antisymm hhi hlo
  exact Nat.dvd_one.mp ⟨u, by rw [← he]; ring⟩

/-- **B.85 (iii)+(iv) — the `q = 3` witnesses with `e > 1` AND `f > 1`.** The level-2 class of
`![-2, 0, 2, 0]` over `ℤ_[3]` is decided at `⟨{(2,2)}⟩` (ramification 2, residue degree 2), and
the level-2 class of `![-2, 0, 3, 0, 3, 0]` at `⟨{(3,2)}⟩` (ramification 3, residue degree 2). -/
theorem gate_ef_three :
    Uniformity.Density.DecidedAt ℤ_[3] 4 ⟨{(2, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 4 2 ![-2, 0, 2, 0])
    ∧ Uniformity.Density.DecidedAt ℤ_[3] 6 ⟨{(3, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 6 2 ![-2, 0, 3, 0, 3, 0]) := by
  constructor
  · have h := decidedAt_of_leaf_certificate (O := ℤ_[3]) (π := (3 : ℤ_[3])) hpi3 (n := 4)
      (N := 2) (by norm_num) a4 hkey (μ := 2) (by norm_num) hres4 hvis4 hterm4 hperim4
    rwa [hord4] at h
  · have h := decidedAt_of_leaf_certificate (O := ℤ_[3]) (π := (3 : ℤ_[3])) hpi3 (n := 6)
      (N := 2) (by norm_num) a6 hkey (μ := 3) (by norm_num) hres6 hvis6 hterm6 hperim6
    rwa [hord6] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_ef_three
end AxCheck
