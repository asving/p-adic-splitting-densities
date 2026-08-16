/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B84b — the `q = 3` RAMIFIED gate

**Chapter B, NODE B.84 instance (ii)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10), ENV-C
concrete. One signed declaration: `gate_ram_three`.

*The instance* (blueprint's row (ii)): `O := ℤ_[3]`, `π := 3`, `a = ![3, 3]`, so
`f = monicPoly a = X² + 3X + 3` (Eisenstein at `3`); key `φ = X` (`m = 1`), `μ = 2`; `N = 2`.

The B.83 (ii) mirror at the second prime: same genre, same value `⟨{(2,1)}⟩`, every valuation
recomputed `3`-adically (`3 ∣ 3`, `9 ∤ 3`, `3 ∤ 1`).

| datum | value | how it is proved here |
|---|---|---|
| `φ = X` is a key | `GateKit.isKey_X` | |
| `f‾ = X‾ ^ 2` | `hresII` | `residue ℤ_[3] 3 = 0` |
| heights `(1, 1, 0)` | `hfinII` | B.15 `npHgt_X` + B.08 |
| only two-point side `(u,ℓ) = (1,2)` | `hslopeII` | B.42's bound (`ℓ ≤ 2`, `u ≤ 1`) + the kit's polygon read at `(0,1)`, `(1,1)`, `(1,2)` |
| `sideSet = {0,2}`, `sideDeg = 1`, `d = 1` | `hside12`/`hsdeg12` | `(2−0)/2 = 1` |
| `Visible π φ f 2` | `hvisII` | `¬ 3² ∣ 3` |
| `order1Type = ⟨{(2,1)}⟩` | `hordII` | `ℓ = 2`, one degree-1 residual factor, `m · deg ψ = 1` |

## The A-F.12 discharge, with this instance's arithmetic displayed

`m = φ.natDegree = 1`, `n = 2`; the blueprint's row (ii) parameters are `m = 1`, `ℓ = 2`,
`n = 2`, and the clause quantifies over every `ℓ`:

```
ℓ = 1 :  the FIRST disjunct fires outright — ℓ = 1 ∧ φ.natDegree = 1
ℓ ≥ 2 :  2 · deg ψ ≤ ℓ · 1 · deg ψ = gS.natDegree ≤ n = 2   ⟹   deg ψ = 1
```

`B-BOX-1`-free in both branches.

DEPENDS (direct): B.08 · B.15 · B.20 · B.30 · B.66 · B.66a · B.73 · B.75 · **B.82** · `B83Kit` ·
landed `LocalData.lean` §6 · mathlib `PadicInt.prime_p`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `HE-SIG` → **Lean theorem**; `W12-ORACLE` → **executable regression** retained;
with B.83 (ii) this row is GC-11's two-prime pair for the ramified genre.

SOURCE: `EFF.W12.29`; `blueprint/CONVENTIONS_2026-08-15.md` GC-11.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private noncomputable abbrev aR3 : Fin 2 → ℤ_[3] := ![3, 3]
private noncomputable abbrev fR3 : Polynomial ℤ_[3] := Uniformity.Density.monicPoly aR3

private theorem hpi3 : Irreducible (3 : ℤ_[3]) := (PadicInt.prime_p (p := 3)).irreducible

private theorem hfnormII : fR3 = X ^ 2 + C 3 * X + C 3 := by
  simp [Uniformity.Density.monicPoly, fR3, aR3, Fin.sum_univ_two]
  ring

private theorem hfdegII : fR3.natDegree = 2 := Uniformity.Density.monicPoly_natDegree aR3
private theorem hfmonII : fR3.Monic := Uniformity.Density.monicPoly_monic aR3
private theorem hfdegmuII : fR3.natDegree = 2 * (X : Polynomial ℤ_[3]).natDegree := by
  rw [hfdegII, Polynomial.natDegree_X]

private theorem hc0 : fR3.coeff 0 = 3 := by rw [hfnormII]; simp
private theorem hc1 : fR3.coeff 1 = 3 := by rw [hfnormII]; simp
private theorem hc2 : fR3.coeff 2 = 1 := by rw [hfnormII]; simp

private theorem hresII : fR3.map (IsLocalRing.residue ℤ_[3])
    = ((X : Polynomial ℤ_[3]).map (IsLocalRing.residue ℤ_[3])) ^ 2 := by
  have h3 : IsLocalRing.residue ℤ_[3] 3 = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [hpi3.maximalIdeal_eq, Ideal.mem_span_singleton]
  rw [hfnormII]
  simp [h3]

private theorem hfinII : ∀ j, j ≤ 2 →
    npHgt (X : Polynomial ℤ_[3]) fR3 j = ((if j = 2 then 0 else 1 : ℕ) : ℕ∞) := by
  intro j hj
  rw [npHgt_X]
  interval_cases j
  · rw [hc0, GateKit.padic_addVal (p := 3) (k := 1) (a := 3) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hc1, GateKit.padic_addVal (p := 3) (k := 1) (a := 3) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hc2, GateKit.padic_addVal (p := 3) (k := 0) (a := 1) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num

private theorem htopII : ∀ j, 2 < j → npHgt (X : Polynomial ℤ_[3]) fR3 j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt Polynomial.monic_X (by rw [Polynomial.natDegree_X]; norm_num)
    fR3 ?_
  rw [hfdegII, Polynomial.natDegree_X]; omega

private theorem hBII : ∀ j, j ≤ fR3.natDegree → (npHgt (X : Polynomial ℤ_[3]) fR3 j).toNat ≤ 1 := by
  intro j hj
  rw [hfdegII] at hj
  rw [hfinII j hj]
  by_cases h : j = 2 <;> simp [h]

-- the `(1,2)` side
private theorem hread12 : suppVal (X : Polynomial ℤ_[3]) fR3 1 2 = ((2 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet (X : Polynomial ℤ_[3]) fR3 1 2 ↔
      (j ≤ 2 ∧ 2 * (if j = 2 then 0 else 1) + 1 * j = 2)) :=
  GateKit.polygon_read (n := 2) (m := 2) hfdegII (by norm_num) hfinII htopII (by norm_num)
    (M := 2) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hside12 : sideSet (X : Polynomial ℤ_[3]) fR3 1 2 = {0, 2} := by
  ext j
  rw [hread12.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp_all
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hne12 : (sideSet (X : Polynomial ℤ_[3]) fR3 1 2).Nonempty := by
  rw [hside12]; exact ⟨0, by decide⟩

private theorem hcard12 : 1 < (sideSet (X : Polynomial ℤ_[3]) fR3 1 2).card := by
  rw [hside12]; decide

private theorem hsdeg12 : ∀ hne : (sideSet (X : Polynomial ℤ_[3]) fR3 1 2).Nonempty,
    sideDeg (X : Polynomial ℤ_[3]) fR3 1 2 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hside12]; decide)
      (by intro j hj; rw [hside12] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 2) (by rw [hside12]; decide)
      (by intro j hj; rw [hside12] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslopeII : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet (X : Polynomial ℤ_[3]) fR3 u ℓ).card → u = 1 ∧ ℓ = 2 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ :=
    GateKit.slope_bounds_of_le GateKit.isKey_X hfmonII hfdegmuII hℓ hcop hcard hBII
  rw [hfdegII] at hℓle
  interval_cases ℓ
  · interval_cases u
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 2) hfdegII (by norm_num) hfinII htopII
        (u := 0) (ℓ := 1) (by norm_num) (M := 0) (by intro j hj; exact Nat.zero_le _)
        ⟨2, by norm_num⟩
      have huniq : ∀ j ∈ sideSet (X : Polynomial ℤ_[3]) fR3 0 1, j = 2 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j
        · norm_num at hval
        · norm_num at hval
        · rfl
      have : (sideSet (X : Polynomial ℤ_[3]) fR3 0 1).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 2) hfdegII (by norm_num) hfinII htopII
        (u := 1) (ℓ := 1) (by norm_num) (M := 1)
        (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩
      have huniq : ∀ j ∈ sideSet (X : Polynomial ℤ_[3]) fR3 1 1, j = 0 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j
        · rfl
        · norm_num at hval
        · norm_num at hval
      have : (sideSet (X : Polynomial ℤ_[3]) fR3 1 1).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exact ⟨rfl, rfl⟩

private theorem hslopeFinsetII : slopeFinset (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) fR3 = {(1, 2)} := by
  ext p
  rw [mem_slopeFinset GateKit.isKey_X hfmonII hfdegmuII]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslopeII p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcard12⟩

private theorem hd1II : ∀ p ∈ slopeFinset (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) fR3,
    ∀ hne : (sideSet (X : Polynomial ℤ_[3]) fR3 p.1 p.2).Nonempty,
      sideDeg (X : Polynomial ℤ_[3]) fR3 p.1 p.2 hne = 1 := by
  intro p hp hne
  rw [hslopeFinsetII, Finset.mem_singleton] at hp
  subst hp
  exact hsdeg12 hne

private theorem hordII : order1Type (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) fR3 = ⟨{(2, 1)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 GateKit.isKey_X hfmonII hfdegmuII hd1II
  rw [hslopeFinsetII, Polynomial.natDegree_X] at h
  rw [h]
  rfl

private theorem htermII : ¬ NeedsDescent (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) fR3 := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 GateKit.isKey_X hfmonII hfdegmuII ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslopeII u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg12 hne

private theorem hvisII : Visible (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) fR3 2 := by
  refine ⟨0, ?_⟩
  rw [dev_X, Polynomial.coeff_C_zero, hc0]
  exact GateKit.padic_not_dvd (p := 3) (a := 3) (by norm_num) (by norm_num)

private theorem hperimII : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = fR3.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (fR3 - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure (X : Polynomial ℤ_[3]) gS u ℓ →
    ∀ hne : (sideSet (X : Polynomial ℤ_[3]) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt (X : Polynomial ℤ_[3]) gS (sideMin (X : Polynomial ℤ_[3]) gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField (X : Polynomial ℤ_[3])), ψ.Monic → Irreducible ψ →
        (∃ c : (resField (X : Polynomial ℤ_[3]))ˣ,
          resPoly (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ (X : Polynomial ℤ_[3]).natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS,
            (X : Polynomial ℤ_[3]).natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  -- the `ℓ = 1` branch is the FIRST disjunct outright
  rcases Nat.lt_or_ge ℓ 2 with hl1 | hl2
  · exact Or.inl ⟨by omega, Polynomial.natDegree_X⟩
  refine Or.inr (Or.inl ?_)
  letI : Field (resField (X : Polynomial ℤ_[3])) := instFieldResField GateKit.isKey_X
  have hbound := GateKit.perim_degree_bound hpi3 GateKit.isKey_X (N := 2) (by norm_num) hresII
    hgTm hdegT hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hc
  rw [Polynomial.natDegree_X, hfdegII] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 2 * 1 * ψ.natDegree ≤ ℓ * 1 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl2)
  omega

/-- **B.83 (ii) — the `q = 2` ramified gate.** The level-2 class of `![3, 3]` over `ℤ_[3]` is
decided at `⟨{(2,1)}⟩`: every monic quadratic lift of `X² + 2X + 2` mod `4` is totally ramified
with residue degree 1. -/
theorem gate_ram_three :
    Uniformity.Density.DecidedAt ℤ_[3] 2 ⟨{(2, 1)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 2 2 ![3, 3]) := by
  have h := decidedAt_of_leaf_certificate (O := ℤ_[3]) (π := (3 : ℤ_[3])) hpi3 (n := 2) (N := 2)
    (by norm_num) aR3 GateKit.isKey_X (μ := 2) (by norm_num) hresII hvisII htermII hperimII
  rwa [hordII] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_ram_three
end AxCheck
