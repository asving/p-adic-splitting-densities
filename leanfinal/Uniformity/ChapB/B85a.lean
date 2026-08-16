/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B85a — the `q = 2` witnesses with `e > 1` **and** `f > 1`

**Chapter B, NODE B.85 instances (i)+(ii)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10),
ENV-C concrete. One signed declaration: `gate_ef_two` (a conjunction of the two instances).

*The instances.* `O := ℤ_[2]`, `π := 2`, key `φ = X² + X + 1` (`m = 2`), window `N = 2`:

| | `f` | `a` | `μ` | `dev` | polygon | value | `n` |
|---|---|---|---|---|---|---|---|
| (i) | `(X²+X+1)² − 2` | `![−1, 2, 3, 2]` | `2` | `(−2, 0, 1)` | side `(1,2)`, argmin `{0,2}`, `d = 1` | `⟨{(2,2)}⟩` | `4` |
| (ii) | `(X²+X+1)³ − 2` | `![−1, 3, 6, 7, 6, 3]` | `3` | `(−2, 0, 0, 1)` | side `(1,3)`, argmin `{0,3}`, `d = 1` | `⟨{(3,2)}⟩` | `6` |

These are the ramified-inert genres `leancheck` never reached: the single leaf has
`e = ℓ ∈ {2,3} > 1` **and** `f = m·d = 2 > 1` simultaneously, honestly (`d = 1`, so both sit in
D-3's unconditional `d = 1, ℓ ≥ 2` row — **no `B-BOX-1`**). Degree conservation: `e·f = 4`
resp. `6 = deg f`. The coprimality tooth (`HE6-T-BADKEY`) pays exactly at the slope enumeration:
`weight(0) = ℓ·1` equals `weight(μ) = μ·u` iff `ℓ = μ·u`, and `Nat.Coprime u ℓ` then forces
`u = 1, ℓ = μ`.

*Development gaps.* `dev φ f j = 0` for `0 < j < μ`, so the finite-height support is `{0, μ}`,
not a contiguous prefix; the kit's `polygon_read_set` is the read used here.

## The A-F.12 discharge — why the DEGREE display is not enough here, and what replaces it

The blueprint's degree display gives, uniformly in the window-class member `gT`,

```
ℓ · φ.natDegree · ψ.natDegree = gS.natDegree ≤ gT.natDegree = n
```

i.e. `ℓ · 2 · deg ψ ≤ 4` (resp. `≤ 6`). At the instance's own slope (`ℓ = 2`, resp. `ℓ = 3`)
that already gives `deg ψ = 1` — the blueprint's `n = 4, ℓ = 2, m = 2` and `n = 6, ℓ = 3, m = 2`
rows. But the clause quantifies over **every** `(u,ℓ)` and every monic divisor `gS ∣ gT`, and at
`ℓ = 1` the degree display alone leaves `deg ψ = 2` open (at `n = 4` that is the blueprint's
"`gS = gT` case"; at `n = 6` it is a genuine proper divisor of degree 4, which the `gS = gT`
reading does not cover).

The kit's `perim_height_bound` closes both at once, and is the honest form of the blueprint's
"admissible only at the transported purity" argument:

```
ḡS = φ̄ ^ k with k ≥ 1        ⟹  npHgt φ gS 0 ≥ 1
purity at abscissa 0          ⟹  ℓ · npHgt φ gS 0 = u · k = ℓ · (u · deg ψ)
B.33 superadditivity + B.35b  ⟹  u · k = suppVal φ gS ≤ suppVal φ gT ≤ ℓ · npHgt φ gT 0
B.76 npHgt_min_congr + hvis   ⟹  npHgt φ gT 0 = npHgt φ f 0 = 1
                              ⟹  1 ≤ u · deg ψ ≤ 1,  hence  deg ψ = 1
```

— the SECOND disjunct at every `(u, ℓ, gS)`, with no case analysis and no `B-BOX-1`.

DEPENDS (direct): B.06 · B.08 · B.20 · B.30 · B.33 · B.35b · B.66 · B.66a · B.73 · B.75 · B.76 ·
**B.82** · `B83Kit` · landed `LocalData.lean` §6 · mathlib `PadicInt.prime_p`,
`PadicInt.residueField`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `EFF.W12.29`'s `σ(λ)` rows at `e ∈ {2,3}`, `f = 2` → **Lean theorem** (B.82's TEETH
promise, discharged here); `HE6-T-BADKEY` (`EFF.HE6.52`) → **Lean theorem** (the coprimality
step is where a non-coprime pair would fail); `W12-ORACLE` → **executable regression** retained
(these degrees are outside `leancheck`'s `n ≤ 3` suite, so PARI is the only independent leg).

SOURCE: `EFF.W12.29`; `EFF.HE3.33`; `EFF.HE6.52`; DECISION D-3.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private theorem hpi2 : Irreducible (2 : ℤ_[2]) := (PadicInt.prime_p (p := 2)).irreducible

/-! ### the shared key `φ = X² + X + 1` -/

private noncomputable abbrev kQ : Polynomial ℤ_[2] := X ^ 2 + X + 1

private theorem hkmon : kQ.Monic := by unfold kQ; monicity!
private theorem hkdeg : kQ.natDegree = 2 := by unfold kQ; compute_degree!
private theorem hkdegW : kQ.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree hkmon.ne_zero, hkdeg]; rfl

private theorem hkirr : Irreducible (kQ.map (IsLocalRing.residue ℤ_[2])) := by
  set e := PadicInt.residueField (p := 2) with he
  have hmap : (kQ.map (IsLocalRing.residue ℤ_[2])).map (e : ResidueField ℤ_[2] →+* ZMod 2)
      = X ^ 2 + X + 1 := by unfold kQ; simp
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hkmon.natDegree_map, hkdeg]; decide
  · intro x hx
    have h1 : ((kQ.map (IsLocalRing.residue ℤ_[2])).map
        (e : ResidueField ℤ_[2] →+* ZMod 2)).eval (e x)
        = e ((kQ.map (IsLocalRing.residue ℤ_[2])).eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom (e : ResidueField ℤ_[2] →+* ZMod 2) x
    rw [hmap, hx] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_zero] at h1
    revert h1
    generalize (e x) = y
    revert y
    decide

private theorem hkey : IsKey kQ := ⟨hkmon, by rw [hkdeg]; norm_num, hkirr⟩

private theorem hdegC : (C (-2 : ℤ_[2]) : Polynomial ℤ_[2]).degree < kQ.degree :=
  lt_of_le_of_lt Polynomial.degree_C_le (by rw [hkdegW]; decide)
private theorem hdeg0 : (0 : Polynomial ℤ_[2]).degree < kQ.degree := by
  rw [Polynomial.degree_zero, hkdegW]; exact WithBot.bot_lt_coe 2
private theorem hdeg1 : (1 : Polynomial ℤ_[2]).degree < kQ.degree := by
  rw [Polynomial.degree_one, hkdegW]; decide

private theorem hnpm2 : IsDiscreteValuationRing.addVal ℤ_[2] (-2 : ℤ_[2]) = ((1 : ℕ) : ℕ∞) :=
  GateKit.padic_addVal (p := 2) (k := 1) (a := -2) (by norm_num) (by norm_num) (by norm_num)

/-! ### instance (i) : the quartic `φ² − 2` -/

private noncomputable abbrev a4 : Fin 4 → ℤ_[2] := ![-1, 2, 3, 2]
private noncomputable abbrev f4 : Polynomial ℤ_[2] := Uniformity.Density.monicPoly a4

private theorem hf4deg : f4.natDegree = 4 := Uniformity.Density.monicPoly_natDegree a4
private theorem hf4mon : f4.Monic := Uniformity.Density.monicPoly_monic a4
private theorem hf4degmu : f4.natDegree = 2 * kQ.natDegree := by rw [hf4deg, hkdeg]

private theorem hf4eq : f4 = C (-2) + 0 * kQ + 1 * kQ ^ 2 := by
  simp [Uniformity.Density.monicPoly, f4, a4, kQ, Fin.sum_univ_four, map_ofNat]
  ring

private theorem hdev4 : dev kQ f4 0 = C (-2) ∧ dev kQ f4 1 = 0 ∧ dev kQ f4 2 = 1 :=
  GateKit.dev_three hkmon (by rw [hkdeg]; norm_num) hdegC hdeg0 hdeg1 hf4eq

private theorem hres4 : f4.map (IsLocalRing.residue ℤ_[2])
    = (kQ.map (IsLocalRing.residue ℤ_[2])) ^ 2 := by
  have hm2 : IsLocalRing.residue ℤ_[2] (-2) = 0 := by
    rw [map_neg]
    refine neg_eq_zero.2 (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hpi2.maximalIdeal_eq, Ideal.mem_span_singleton]
  rw [hf4eq, zero_mul, add_zero, one_mul, Polynomial.map_add, Polynomial.map_C, hm2,
    Polynomial.C_0, zero_add, Polynomial.map_pow]

private theorem hfin4 : ∀ j ∈ ({0, 2} : Finset ℕ),
    npHgt kQ f4 j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [npHgt, hdev4.1, GateKit.gaussVal_C, hnpm2]; norm_num
  · rw [npHgt, hdev4.2.2, show (1 : Polynomial ℤ_[2]) = C 1 from (Polynomial.C_1).symm,
      GateKit.gaussVal_C, GateKit.addVal_one hpi2]
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

private theorem hslopeFinset4 : slopeFinset (2 : ℤ_[2]) kQ f4 = {(1, 2)} := by
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

private theorem hord4 : order1Type (2 : ℤ_[2]) kQ f4 = ⟨{(2, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi2 hkey hf4mon hf4degmu (by
    intro p hp hne
    rw [hslopeFinset4, Finset.mem_singleton] at hp
    subst hp
    exact hsdeg4 hne)
  rw [hslopeFinset4, hkdeg] at h
  rw [h]
  rfl

private theorem hterm4 : ¬ NeedsDescent (2 : ℤ_[2]) kQ f4 := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi2 hkey hf4mon hf4degmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslope4 u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg4 hne

private theorem hvis4 : Visible (2 : ℤ_[2]) kQ f4 2 := by
  refine ⟨0, ?_⟩
  rw [hdev4.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 2) (a := -2) (by norm_num) (by norm_num)

private theorem hnp4zero : npHgt kQ f4 0 = ((1 : ℕ) : ℕ∞) := by
  rw [npHgt, hdev4.1, GateKit.gaussVal_C, hnpm2]

private theorem hperim4 : ∀ gT : Polynomial ℤ_[2], gT.Monic →
    gT.natDegree = f4.natDegree →
    (∀ k, (2 : ℤ_[2]) ^ 2 ∣ (f4 - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[2], gS.Monic → gS ∣ gT → IsPure kQ gS u ℓ →
    ∀ hne : (sideSet kQ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kQ gS (sideMin kQ gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kQ), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kQ)ˣ, resPoly (2 : ℤ_[2]) kQ gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kQ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kQ.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  obtain ⟨hlo, hhi⟩ := GateKit.perim_height_bound hpi2 hkey (N := 2) hres4 hvis4 hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hψm hψi hc hnp4zero
  have he : u * ψ.natDegree = 1 := le_antisymm hhi hlo
  exact Nat.dvd_one.mp ⟨u, by rw [← he]; ring⟩

/-! ### instance (ii) : the sextic `φ³ − 2` -/

private noncomputable abbrev a6 : Fin 6 → ℤ_[2] := ![-1, 3, 6, 7, 6, 3]
private noncomputable abbrev f6 : Polynomial ℤ_[2] := Uniformity.Density.monicPoly a6

private theorem hf6deg : f6.natDegree = 6 := Uniformity.Density.monicPoly_natDegree a6
private theorem hf6mon : f6.Monic := Uniformity.Density.monicPoly_monic a6
private theorem hf6degmu : f6.natDegree = 3 * kQ.natDegree := by rw [hf6deg, hkdeg]

private theorem hf6eq : f6 = C (-2) + 0 * kQ + 0 * kQ ^ 2 + 1 * kQ ^ 3 := by
  simp [Uniformity.Density.monicPoly, f6, a6, kQ, Fin.sum_univ_six, map_ofNat]
  ring

private theorem hdev6 : dev kQ f6 0 = C (-2) ∧ dev kQ f6 1 = 0 ∧ dev kQ f6 2 = 0
    ∧ dev kQ f6 3 = 1 :=
  GateKit.dev_four hkmon (by rw [hkdeg]; norm_num) hdegC hdeg0 hdeg0 hdeg1 hf6eq

private theorem hres6 : f6.map (IsLocalRing.residue ℤ_[2])
    = (kQ.map (IsLocalRing.residue ℤ_[2])) ^ 3 := by
  have hm2 : IsLocalRing.residue ℤ_[2] (-2) = 0 := by
    rw [map_neg]
    refine neg_eq_zero.2 (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hpi2.maximalIdeal_eq, Ideal.mem_span_singleton]
  rw [hf6eq, zero_mul, add_zero, zero_mul, add_zero, one_mul, Polynomial.map_add,
    Polynomial.map_C, hm2, Polynomial.C_0, zero_add, Polynomial.map_pow]

private theorem hfin6 : ∀ j ∈ ({0, 3} : Finset ℕ),
    npHgt kQ f6 j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [npHgt, hdev6.1, GateKit.gaussVal_C, hnpm2]; norm_num
  · rw [npHgt, hdev6.2.2.2, show (1 : Polynomial ℤ_[2]) = C 1 from (Polynomial.C_1).symm,
      GateKit.gaussVal_C, GateKit.addVal_one hpi2]
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

private theorem hslopeFinset6 : slopeFinset (2 : ℤ_[2]) kQ f6 = {(1, 3)} := by
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

private theorem hord6 : order1Type (2 : ℤ_[2]) kQ f6 = ⟨{(3, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi2 hkey hf6mon hf6degmu (by
    intro p hp hne
    rw [hslopeFinset6, Finset.mem_singleton] at hp
    subst hp
    exact hsdeg6 hne)
  rw [hslopeFinset6, hkdeg] at h
  rw [h]
  rfl

private theorem hterm6 : ¬ NeedsDescent (2 : ℤ_[2]) kQ f6 := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi2 hkey hf6mon hf6degmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslope6 u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg6 hne

private theorem hvis6 : Visible (2 : ℤ_[2]) kQ f6 2 := by
  refine ⟨0, ?_⟩
  rw [hdev6.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 2) (a := -2) (by norm_num) (by norm_num)

private theorem hnp6zero : npHgt kQ f6 0 = ((1 : ℕ) : ℕ∞) := by
  rw [npHgt, hdev6.1, GateKit.gaussVal_C, hnpm2]

private theorem hperim6 : ∀ gT : Polynomial ℤ_[2], gT.Monic →
    gT.natDegree = f6.natDegree →
    (∀ k, (2 : ℤ_[2]) ^ 2 ∣ (f6 - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[2], gS.Monic → gS ∣ gT → IsPure kQ gS u ℓ →
    ∀ hne : (sideSet kQ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kQ gS (sideMin kQ gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kQ), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kQ)ˣ, resPoly (2 : ℤ_[2]) kQ gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kQ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kQ.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  obtain ⟨hlo, hhi⟩ := GateKit.perim_height_bound hpi2 hkey (N := 2) hres6 hvis6 hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hψm hψi hc hnp6zero
  have he : u * ψ.natDegree = 1 := le_antisymm hhi hlo
  exact Nat.dvd_one.mp ⟨u, by rw [← he]; ring⟩

/-- **B.85 (i)+(ii) — the `q = 2` witnesses with `e > 1` AND `f > 1`.** The level-2 class of
`![-1, 2, 3, 2]` over `ℤ_[2]` is decided at `⟨{(2,2)}⟩` (ramification 2, residue degree 2), and
the level-2 class of `![-1, 3, 6, 7, 6, 3]` at `⟨{(3,2)}⟩` (ramification 3, residue degree 2). -/
theorem gate_ef_two :
    Uniformity.Density.DecidedAt ℤ_[2] 4 ⟨{(2, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 4 2 ![-1, 2, 3, 2])
    ∧ Uniformity.Density.DecidedAt ℤ_[2] 6 ⟨{(3, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 6 2 ![-1, 3, 6, 7, 6, 3]) := by
  constructor
  · have h := decidedAt_of_leaf_certificate (O := ℤ_[2]) (π := (2 : ℤ_[2])) hpi2 (n := 4)
      (N := 2) (by norm_num) a4 hkey (μ := 2) (by norm_num) hres4 hvis4 hterm4 hperim4
    rwa [hord4] at h
  · have h := decidedAt_of_leaf_certificate (O := ℤ_[2]) (π := (2 : ℤ_[2])) hpi2 (n := 6)
      (N := 2) (by norm_num) a6 hkey (μ := 3) (by norm_num) hres6 hvis6 hterm6 hperim6
    rwa [hord6] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_ef_two
end AxCheck
