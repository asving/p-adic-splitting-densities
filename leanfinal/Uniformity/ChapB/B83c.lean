/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B83c — the `q = 2` TWO-SLOPE gate (the A-F.1 pin's teeth)

**Chapter B, NODE B.83 instance (iii)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10), ENV-C
concrete. One signed declaration: `gate_linram_two`.

*The instance* (blueprint's row (iii)): `O := ℤ_[2]`, `π := 2`, `a = ![4, 2, 2]`, so
`f = monicPoly a = X³ + 2X² + 2X + 4`; key `φ = X` (`m = 1`), `μ = 3`; window `N = 3`. The value
is `leancheck`'s `N3CertLinRam` multiset `{(1,1),(2,1)}`, here produced by the general engine.

**⚠ This instance certifies the A-F.1 `sideMin` pin repair.** Its right side `(u,ℓ) = (1,2)` has
argmin `{1,3}`, so `sideMin = 1 ≠ 0`: under the retired abscissa-0 read the residual polynomial
at that side is `0` and the instance cannot fire at all. The repair is load-bearing here, not
decorative.

| datum | value | how it is proved here |
|---|---|---|
| `φ = X` is a key | `GateKit.isKey_X` | |
| `f‾ = X‾ ^ 3` | `hresIII` | `residue ℤ_[2] 2 = residue ℤ_[2] 4 = 0` |
| heights `(2, 1, 1, 0)` | `hfinIII` | B.15 `npHgt_X` + B.08 (`4 ∣ 4`, `8 ∤ 4`; `2 ∣ 2`, `4 ∤ 2`; `2 ∤ 1`) |
| two-point sides: `(1,1)` and `(1,2)` only | `hslopeIII` | B.42's bound (`ℓ ≤ 3`, `u ≤ 2`) + the kit's polygon read at each of the six coprime candidates |
| `(1,1)`: argmin `{0,1}`, `sideDeg = 1` | `hsideA`/`hsdegA` | `(1−0)/1 = 1` |
| `(1,2)`: argmin `{1,3}`, **`sideMin = 1`**, `sideDeg = 1` | `hsideB`/`hsdegB` | `(3−1)/2 = 1` |
| `¬ NeedsDescent` | `htermIII` | both residuals have degree 1 ⟹ separable |
| `Visible π φ f 3` | `hvisIII` | `¬ 2³ ∣ 4` |
| `order1Type = ⟨{(1,1),(2,1)}⟩` | `hordIII` | two slopes `ℓ = 1, 2`, one degree-1 residual factor each, `m · deg ψ = 1` |

## The A-F.12 discharge, with this instance's arithmetic displayed

The kit's `perim_degree_bound` gives, uniformly in the window-class member `gT`,

```
ℓ · φ.natDegree · ψ.natDegree = gS.natDegree ≤ gT.natDegree = f.natDegree = n
```

with `m = φ.natDegree = 1`, `n = 3`. Per the blueprint's ⚠, the `(1,1)` side takes the FIRST
disjunct and the `(1,2)` side the SECOND:

```
ℓ = 1 :  FIRST disjunct outright — ℓ = 1 ∧ φ.natDegree = 1
ℓ ≥ 2 :  2 · deg ψ ≤ ℓ · 1 · deg ψ ≤ 3   ⟹   deg ψ ≤ 1, and deg ψ ≥ 1, so deg ψ = 1
```

`B-BOX-1`-free in both branches.

DEPENDS (direct): B.08 · B.15 · B.20 · B.30 · B.66 · B.66a · B.73 · B.75 · **B.82** · `B83Kit` ·
landed `LocalData.lean` §6 · mathlib `PadicInt.prime_p`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `HE-SIG` (`EFF.HE3.52`) → **Lean theorem**; `W12-ORACLE` → **executable regression**
retained; `W12-SHAPE`'s decided `n = 3` two-slope row → **Lean theorem**; the A-F.1 pin repair →
**Lean theorem** (this instance could not fire under the abscissa-0 pin).

SOURCE: `EFF.W12.29`; `leancheck/UniformityCheck/N3CertLinRam.lean`
(`notes/N3_CHECK_2026-08-13.md` §13); `blueprint/CONVENTIONS_2026-08-15.md` GC-11.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private noncomputable abbrev aIII : Fin 3 → ℤ_[2] := ![4, 2, 2]
private noncomputable abbrev fIII : Polynomial ℤ_[2] := Uniformity.Density.monicPoly aIII

private theorem hpi2 : Irreducible (2 : ℤ_[2]) := (PadicInt.prime_p (p := 2)).irreducible

private theorem hfnormIII : fIII = X ^ 3 + C 2 * X ^ 2 + C 2 * X + C 4 := by
  simp [Uniformity.Density.monicPoly, fIII, aIII, Fin.sum_univ_three]
  ring

private theorem hfdegIII : fIII.natDegree = 3 := Uniformity.Density.monicPoly_natDegree aIII
private theorem hfmonIII : fIII.Monic := Uniformity.Density.monicPoly_monic aIII
private theorem hfdegmuIII : fIII.natDegree = 3 * (X : Polynomial ℤ_[2]).natDegree := by
  rw [hfdegIII, Polynomial.natDegree_X]

private theorem hc0 : fIII.coeff 0 = 4 := by rw [hfnormIII]; simp
private theorem hc1 : fIII.coeff 1 = 2 := by rw [hfnormIII]; simp
private theorem hc2 : fIII.coeff 2 = 2 := by rw [hfnormIII]; simp
private theorem hc3 : fIII.coeff 3 = 1 := by rw [hfnormIII]; simp

private theorem hresIII : fIII.map (IsLocalRing.residue ℤ_[2])
    = ((X : Polynomial ℤ_[2]).map (IsLocalRing.residue ℤ_[2])) ^ 3 := by
  have h2 : IsLocalRing.residue ℤ_[2] 2 = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [hpi2.maximalIdeal_eq, Ideal.mem_span_singleton]
  have h4 : IsLocalRing.residue ℤ_[2] 4 = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [hpi2.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact ⟨2, by norm_num⟩
  rw [hfnormIII]
  simp [h2, h4]

private theorem hfinIII : ∀ j, j ≤ 3 → npHgt (X : Polynomial ℤ_[2]) fIII j
    = ((if j = 0 then 2 else if j = 3 then 0 else 1 : ℕ) : ℕ∞) := by
  intro j hj
  rw [npHgt_X]
  interval_cases j
  · rw [hc0, GateKit.padic_addVal (p := 2) (k := 2) (a := 4) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hc1, GateKit.padic_addVal (p := 2) (k := 1) (a := 2) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hc2, GateKit.padic_addVal (p := 2) (k := 1) (a := 2) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hc3, GateKit.padic_addVal (p := 2) (k := 0) (a := 1) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num

private theorem htopIII : ∀ j, 3 < j → npHgt (X : Polynomial ℤ_[2]) fIII j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt Polynomial.monic_X (by rw [Polynomial.natDegree_X]; norm_num)
    fIII ?_
  rw [hfdegIII, Polynomial.natDegree_X]; omega

private theorem hBIII : ∀ j, j ≤ fIII.natDegree →
    (npHgt (X : Polynomial ℤ_[2]) fIII j).toNat ≤ 2 := by
  intro j hj
  rw [hfdegIII] at hj
  rw [hfinIII j hj]
  by_cases h0 : j = 0 <;> by_cases h3 : j = 3 <;> simp [h0, h3]

/-! ### the two sides -/

private theorem hreadA : suppVal (X : Polynomial ℤ_[2]) fIII 1 1 = ((2 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet (X : Polynomial ℤ_[2]) fIII 1 1 ↔
      (j ≤ 3 ∧ 1 * (if j = 0 then 2 else if j = 3 then 0 else 1) + 1 * j = 2)) :=
  GateKit.polygon_read (n := 3) (m := 3) hfdegIII (by norm_num) hfinIII htopIII (by norm_num)
    (M := 2) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hsideA : sideSet (X : Polynomial ℤ_[2]) fIII 1 1 = {0, 1} := by
  ext j
  rw [hreadA.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp_all
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hcardA : 1 < (sideSet (X : Polynomial ℤ_[2]) fIII 1 1).card := by
  rw [hsideA]; decide

private theorem hsdegA : ∀ hne : (sideSet (X : Polynomial ℤ_[2]) fIII 1 1).Nonempty,
    sideDeg (X : Polynomial ℤ_[2]) fIII 1 1 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hsideA]; decide)
      (by intro j hj; rw [hsideA] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 1) (by rw [hsideA]; decide)
      (by intro j hj; rw [hsideA] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hreadB : suppVal (X : Polynomial ℤ_[2]) fIII 1 2 = ((3 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet (X : Polynomial ℤ_[2]) fIII 1 2 ↔
      (j ≤ 3 ∧ 2 * (if j = 0 then 2 else if j = 3 then 0 else 1) + 1 * j = 3)) :=
  GateKit.polygon_read (n := 3) (m := 3) hfdegIII (by norm_num) hfinIII htopIII (by norm_num)
    (M := 3) (by intro j hj; interval_cases j <;> norm_num) ⟨1, by norm_num⟩

private theorem hsideB : sideSet (X : Polynomial ℤ_[2]) fIII 1 2 = {1, 3} := by
  ext j
  rw [hreadB.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp_all
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hcardB : 1 < (sideSet (X : Polynomial ℤ_[2]) fIII 1 2).card := by
  rw [hsideB]; decide

private theorem hsdegB : ∀ hne : (sideSet (X : Polynomial ℤ_[2]) fIII 1 2).Nonempty,
    sideDeg (X : Polynomial ℤ_[2]) fIII 1 2 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 1) (by rw [hsideB]; decide)
      (by intro j hj; rw [hsideB] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 3) (by rw [hsideB]; decide)
      (by intro j hj; rw [hsideB] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

/-! ### the slope enumeration -/

private theorem hslopeIII : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet (X : Polynomial ℤ_[2]) fIII u ℓ).card → (u = 1 ∧ ℓ = 1) ∨ (u = 1 ∧ ℓ = 2) := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ :=
    GateKit.slope_bounds_of_le GateKit.isKey_X hfmonIII hfdegmuIII hℓ hcop hcard hBIII
  rw [hfdegIII] at hℓle
  have kill : ∀ (u ℓ M j₀ : ℕ), 0 < ℓ →
      (∀ j, j ≤ 3 → M ≤ ℓ * (if j = 0 then 2 else if j = 3 then 0 else 1) + u * j) →
      (∃ j, j ≤ 3 ∧ ℓ * (if j = 0 then 2 else if j = 3 then 0 else 1) + u * j = M) →
      (∀ j, j ≤ 3 → ℓ * (if j = 0 then 2 else if j = 3 then 0 else 1) + u * j = M → j = j₀) →
      (sideSet (X : Polynomial ℤ_[2]) fIII u ℓ).card ≤ 1 := by
    intro u ℓ M j₀ hl hle hmem huniq
    have hread := GateKit.polygon_read (n := 3) (m := 3) hfdegIII (by norm_num) hfinIII htopIII
      hl (M := M) hle hmem
    exact Finset.card_le_one.2 fun a ha b hb => by
      obtain ⟨ha1, ha2⟩ := (hread.2 a).1 ha
      obtain ⟨hb1, hb2⟩ := (hread.2 b).1 hb
      rw [huniq a ha1 ha2, huniq b hb1 hb2]
  interval_cases ℓ
  · interval_cases u
    · exfalso
      have hle1 := kill 0 1 0 3 (by norm_num) (by intro j hj; exact Nat.zero_le _)
        ⟨3, by norm_num⟩ (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      have hle1 := kill 2 1 2 0 (by norm_num)
        (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩
        (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega
  · interval_cases u
    · exact absurd hcop (by decide)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd hcop (by decide)
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso
      have hle1 := kill 1 3 3 3 (by norm_num)
        (by intro j hj; interval_cases j <;> norm_num) ⟨3, by norm_num⟩
        (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega
    · exfalso
      have hle1 := kill 2 3 5 1 (by norm_num)
        (by intro j hj; interval_cases j <;> norm_num) ⟨1, by norm_num⟩
        (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega

private theorem hslopeFinsetIII :
    slopeFinset (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) fIII = {(1, 1), (1, 2)} := by
  ext p
  rw [mem_slopeFinset GateKit.isKey_X hfmonIII hfdegmuIII]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    rcases hslopeIII p.1 p.2 hℓ hcop hcard with ⟨hu, hl⟩ | ⟨hu, hl⟩ <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    · exact Or.inl ⟨hu, hl⟩
    · exact Or.inr ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨by norm_num, by norm_num, hcardA⟩
    · exact ⟨by norm_num, by norm_num, hcardB⟩

private theorem hd1III : ∀ p ∈ slopeFinset (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) fIII,
    ∀ hne : (sideSet (X : Polynomial ℤ_[2]) fIII p.1 p.2).Nonempty,
      sideDeg (X : Polynomial ℤ_[2]) fIII p.1 p.2 hne = 1 := by
  intro p hp hne
  rw [hslopeFinsetIII] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact hsdegA hne
  · exact hsdegB hne

private theorem hordIII :
    order1Type (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) fIII = ⟨{(1, 1), (2, 1)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi2 GateKit.isKey_X hfmonIII hfdegmuIII hd1III
  rw [hslopeFinsetIII, Polynomial.natDegree_X] at h
  rw [h]
  rfl

private theorem htermIII : ¬ NeedsDescent (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) fIII := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi2 GateKit.isKey_X hfmonIII hfdegmuIII ?_
  intro u ℓ hℓ hcop hcard hne
  rcases hslopeIII u ℓ hℓ hcop hcard with ⟨hu, hl⟩ | ⟨hu, hl⟩
  · subst hu; subst hl; exact hsdegA hne
  · subst hu; subst hl; exact hsdegB hne

private theorem hvisIII : Visible (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) fIII 3 := by
  refine ⟨0, ?_⟩
  rw [dev_X, Polynomial.coeff_C_zero, hc0]
  exact GateKit.padic_not_dvd (p := 2) (a := 4) (by norm_num) (by norm_num)

private theorem hperimIII : ∀ gT : Polynomial ℤ_[2], gT.Monic →
    gT.natDegree = fIII.natDegree →
    (∀ k, (2 : ℤ_[2]) ^ 3 ∣ (fIII - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[2], gS.Monic → gS ∣ gT → IsPure (X : Polynomial ℤ_[2]) gS u ℓ →
    ∀ hne : (sideSet (X : Polynomial ℤ_[2]) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt (X : Polynomial ℤ_[2]) gS (sideMin (X : Polynomial ℤ_[2]) gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField (X : Polynomial ℤ_[2])), ψ.Monic → Irreducible ψ →
        (∃ c : (resField (X : Polynomial ℤ_[2]))ˣ,
          resPoly (2 : ℤ_[2]) (X : Polynomial ℤ_[2]) gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ (X : Polynomial ℤ_[2]).natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS,
            (X : Polynomial ℤ_[2]).natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  rcases Nat.lt_or_ge ℓ 2 with hl1 | hl2
  · exact Or.inl ⟨by omega, Polynomial.natDegree_X⟩
  refine Or.inr (Or.inl ?_)
  letI : Field (resField (X : Polynomial ℤ_[2])) := instFieldResField GateKit.isKey_X
  have hbound := GateKit.perim_degree_bound hpi2 GateKit.isKey_X (N := 3) (by norm_num) hresIII
    hgTm hdegT hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hc
  rw [Polynomial.natDegree_X, hfdegIII] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 2 * 1 * ψ.natDegree ≤ ℓ * 1 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl2)
  omega

/-- **B.83 (iii) — the `q = 2` two-slope gate.** The level-3 class of `![4, 2, 2]` over `ℤ_[2]`
is decided at `⟨{(1,1),(2,1)}⟩` — a linear factor and a ramified quadratic. The right side has
`sideMin = 1`, so this firing is impossible under the retired abscissa-0 pin. -/
theorem gate_linram_two :
    Uniformity.Density.DecidedAt ℤ_[2] 3 ⟨{(1, 1), (2, 1)}⟩ 3
      (Uniformity.Density.proj ℤ_[2] 3 3 ![4, 2, 2]) := by
  have h := decidedAt_of_leaf_certificate (O := ℤ_[2]) (π := (2 : ℤ_[2])) hpi2 (n := 3) (N := 3)
    (by norm_num) aIII GateKit.isKey_X (μ := 3) (by norm_num) hresIII hvisIII htermIII hperimIII
  rwa [hordIII] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_linram_two
end AxCheck
