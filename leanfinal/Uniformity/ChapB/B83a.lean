/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B83a — the `q = 2` INERT gate

**Chapter B, NODE B.83 instance (i)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10), ENV-C
concrete. One signed declaration: `gate_inert_two`.

*The instance* (blueprint's row (i)): `O := ℤ_[2]`, `π := 2`, `a = ![3, 1]`, so
`f = monicPoly a = X² + X + 3`; key `φ = X² + X + 1` (`m = 2`), `μ = 1`; window `N = 2`.

| datum | value | how it is proved here |
|---|---|---|
| `f = φ + 2` | `hfeq` | `monicPoly` unfolded, `ring` |
| `f‾ = φ‾ ^ 1` | `hresI` | `residue ℤ_[2] 2 = 0` (`2 ∈ 𝔪`) |
| `φ‾` irreducible over `𝔽₂` | `hkirr` | no root, transported along `PadicInt.residueField` |
| `dev φ f = (2, 1)` | `hdevI` | B.06 `dev_unique`, via the kit's `dev_two` |
| heights `(1, 0, ⊤)` | `hnp0`/`hnp1`/`htopI` | B.08 exact divisibility (`2 ∣ 2`, `4 ∤ 2`) |
| only two-point side `(u,ℓ) = (1,1)` | `hslopeI` | B.42's bound (`ℓ ≤ 2`, `u ≤ 1`) + the kit's polygon read at each of `(0,1)`, `(1,1)`, `(1,2)`; `(0,2)` is not coprime |
| `sideSet = {0,1}`, `sideDeg = 1`, `d = 1` | `hside11`/`hsdeg11` | B.20 endpoints |
| `¬ NeedsDescent` | `htermI` | degree-1 residual ⟹ separable |
| `Visible π φ f 2` | `hvisI` | `¬ 2² ∣ 2` |
| `order1Type = ⟨{(1,2)}⟩` | `hordI` | B.66 on the step-3 finsets: one slope `ℓ = 1`, one residual factor of degree 1, `m · deg ψ = 2` |

## The A-F.12 discharge, with this instance's arithmetic displayed

`hperimI` closes B.82's re-signed `hperim` **uniformly in the window-class member** `gT`, not by
evaluating this instance's own polygon. The kit's `perim_degree_bound` supplies the display

```
ℓ · φ.natDegree · ψ.natDegree = gS.natDegree ≤ gT.natDegree = f.natDegree = n
```

and here `m = φ.natDegree = 2`, `n = 2`, so with `ℓ ≥ 1` and `deg ψ ≥ 1` (ψ monic irreducible):

```
2 ≤ 1 · 2 · 1 ≤ ℓ · 2 · deg ψ ≤ 2      ⟹      deg ψ = 1
```

— the SECOND disjunct, `B-BOX-1`-free, exactly as the blueprint's ⚠ says. Nothing about `gT`'s
factorization is used, and no `d ≥ 2` case ever arises.

DEPENDS (direct): B.06 · B.08 · B.20 · B.30 · B.66 · B.66a · B.73 · B.75 · **B.82** ·
`B83Kit` (the booked shared evaluation kit) · landed `LocalData.lean` §6 (the `ℤ_[2]` bundle) ·
mathlib `PadicInt.prime_p`, `PadicInt.residueField`, `PadicInt.pow_p_dvd_int_iff`,
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`.

**TEETH.** `HE-SIG` (`EFF.HE3.52`) → **Lean theorem** (this firing); `W12-ORACLE`
(0 bad / 41,923) → **executable regression** retained; `W12-SHAPE`'s decided `n = 2` inert row →
**Lean theorem**.

SOURCE: `EFF.W12.29` (the `σ(λ)` row `(1,2)`); `leancheck/UniformityCheck/N3InertExact.lean`
(the hand-cased calibration layer this reproduces through the general engine);
`blueprint/CONVENTIONS_2026-08-15.md` GC-11.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`** — inherited through B.82 ← B.79(b) ←
B.79(a) ← B.63 ← B.42, the 2026-08-16 owner-signed literature cite. No new axiom.
-/

set_option linter.style.longLine false

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private noncomputable abbrev aI : Fin 2 → ℤ_[2] := ![3, 1]
private noncomputable abbrev fI : Polynomial ℤ_[2] := Uniformity.Density.monicPoly aI
private noncomputable abbrev kI : Polynomial ℤ_[2] := X ^ 2 + X + 1

private theorem hpi : Irreducible (2 : ℤ_[2]) := (PadicInt.prime_p (p := 2)).irreducible

private theorem hkmon : kI.Monic := by unfold kI; monicity!
private theorem hkdeg : kI.natDegree = 2 := by unfold kI; compute_degree!
private theorem hkdegW : kI.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree hkmon.ne_zero, hkdeg]; rfl
private theorem hfdeg : fI.natDegree = 2 := Uniformity.Density.monicPoly_natDegree aI
private theorem hfmon : fI.Monic := Uniformity.Density.monicPoly_monic aI

private theorem hfnorm : fI = X ^ 2 + X + C 3 := by
  simp [Uniformity.Density.monicPoly, fI, aI, Fin.sum_univ_two]
  ring

private theorem hfeq : fI = C 2 + 1 * kI := by
  have h3 : (C 3 : Polynomial ℤ_[2]) = 1 + C 2 := by
    rw [← Polynomial.C_1, ← Polynomial.C_add]; norm_num
  rw [hfnorm, h3]
  unfold kI
  ring

private theorem hres2 : IsLocalRing.residue ℤ_[2] 2 = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  rw [hpi.maximalIdeal_eq, Ideal.mem_span_singleton]

private theorem hkirr : Irreducible (kI.map (IsLocalRing.residue ℤ_[2])) := by
  set e := PadicInt.residueField (p := 2) with he
  have hmap : (kI.map (IsLocalRing.residue ℤ_[2])).map (e : ResidueField ℤ_[2] →+* ZMod 2)
      = X ^ 2 + X + 1 := by unfold kI; simp
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hkmon.natDegree_map, hkdeg]; decide
  · intro x hx
    have h1 : ((kI.map (IsLocalRing.residue ℤ_[2])).map
        (e : ResidueField ℤ_[2] →+* ZMod 2)).eval (e x)
        = e ((kI.map (IsLocalRing.residue ℤ_[2])).eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom (e : ResidueField ℤ_[2] →+* ZMod 2) x
    rw [hmap, hx] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_zero] at h1
    revert h1
    generalize (e x) = y
    revert y
    decide

private theorem hkey : IsKey kI := ⟨hkmon, by rw [hkdeg]; norm_num, hkirr⟩

private theorem hresI : fI.map (IsLocalRing.residue ℤ_[2])
    = (kI.map (IsLocalRing.residue ℤ_[2])) ^ 1 := by
  rw [pow_one, hfeq]
  simp [Polynomial.map_add, hres2]

private theorem hdevI : dev kI fI 0 = C 2 ∧ dev kI fI 1 = 1 :=
  GateKit.dev_two hkmon (by rw [hkdeg]; norm_num)
    (lt_of_le_of_lt Polynomial.degree_C_le (by rw [hkdegW]; decide))
    (by rw [Polynomial.degree_one, hkdegW]; decide) hfeq


private theorem hfdegmu : fI.natDegree = 1 * kI.natDegree := by rw [hfdeg, hkdeg]

private theorem hnp0 : npHgt kI fI 0 = (1 : ℕ) := by
  rw [npHgt, hdevI.1, GateKit.gaussVal_C]
  refine Uniformity.Density.addVal_eq_of_dvd_not_dvd hpi (by simp) ?_
  intro h
  have h' : ((2:ℕ) : ℤ_[2]) ^ 2 ∣ ((2 : ℤ) : ℤ_[2]) := by push_cast; exact_mod_cast h
  rw [PadicInt.pow_p_dvd_int_iff] at h'
  norm_num at h'

private theorem hnp1 : npHgt kI fI 1 = (0 : ℕ) := by
  rw [npHgt, hdevI.2, show (1 : Polynomial ℤ_[2]) = C 1 from (Polynomial.C_1).symm,
    GateKit.gaussVal_C, GateKit.addVal_one hpi]
  rfl

private theorem htopI : ∀ j, 1 < j → npHgt kI fI j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt hkmon (by rw [hkdeg]; norm_num) fI ?_
  rw [hfdeg, hkdeg]; omega

private theorem hfinI : ∀ j, j ≤ 1 → npHgt kI fI j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  interval_cases j
  · rw [hnp0]; norm_num
  · rw [hnp1]; norm_num

private theorem hBI : ∀ j, j ≤ fI.natDegree → (npHgt kI fI j).toNat ≤ 1 := by
  intro j _
  by_cases h : j ≤ 1
  · interval_cases j
    · rw [hnp0]; decide
    · rw [hnp1]; decide
  · rw [htopI j (by omega)]; decide

-- the (1,1) side
private theorem hread11 : suppVal kI fI 1 1 = ((1 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet kI fI 1 1 ↔ (j ≤ 1 ∧ 1 * (if j = 0 then 1 else 0) + 1 * j = 1)) :=
  GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI (by norm_num)
    (M := 1) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hside11 : sideSet kI fI 1 1 = {0, 1} := by
  ext j
  rw [hread11.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hne11 : (sideSet kI fI 1 1).Nonempty := by rw [hside11]; exact ⟨0, by decide⟩

private theorem hcard11 : 1 < (sideSet kI fI 1 1).card := by rw [hside11]; decide

private theorem hsdeg11 : ∀ hne : (sideSet kI fI 1 1).Nonempty, sideDeg kI fI 1 1 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hside11]; decide)
      (by intro j hj; rw [hside11] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 1) (by rw [hside11]; decide)
      (by intro j hj; rw [hside11] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslopeI : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet kI fI u ℓ).card → u = 1 ∧ ℓ = 1 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ := GateKit.slope_bounds_of_le hkey hfmon hfdegmu hℓ hcop hcard hBI
  rw [hfdeg] at hℓle
  interval_cases ℓ
  · interval_cases u
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI
        (u := 0) (ℓ := 1) (by norm_num) (M := 0) (by intro j hj; exact Nat.zero_le _)
        ⟨1, by norm_num⟩
      have huniq : ∀ j ∈ sideSet kI fI 0 1, j = 1 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j
        · norm_num at hval
        · rfl
      have : (sideSet kI fI 0 1).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega
    · exact ⟨rfl, rfl⟩
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI
        (u := 1) (ℓ := 2) (by norm_num) (M := 1)
        (by intro j hj; interval_cases j <;> norm_num) ⟨1, by norm_num⟩
      have huniq : ∀ j ∈ sideSet kI fI 1 2, j = 1 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j
        · norm_num at hval
        · rfl
      have : (sideSet kI fI 1 2).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega


private theorem hslopeFinsetI : slopeFinset (2:ℤ_[2]) kI fI = {(1, 1)} := by
  ext p
  rw [mem_slopeFinset hkey hfmon hfdegmu]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslopeI p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcard11⟩

private theorem hd1I : ∀ p ∈ slopeFinset (2:ℤ_[2]) kI fI,
    ∀ hne : (sideSet kI fI p.1 p.2).Nonempty, sideDeg kI fI p.1 p.2 hne = 1 := by
  intro p hp hne
  rw [hslopeFinsetI, Finset.mem_singleton] at hp
  subst hp
  exact hsdeg11 hne

private theorem hordI : order1Type (2:ℤ_[2]) kI fI = ⟨{(1, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi hkey hfmon hfdegmu hd1I
  rw [hslopeFinsetI, hkdeg] at h
  rw [h]
  rfl

private theorem htermI : ¬ NeedsDescent (2:ℤ_[2]) kI fI := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi hkey hfmon hfdegmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslopeI u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg11 hne

private theorem hvisI : Visible (2:ℤ_[2]) kI fI 2 := by
  refine ⟨0, ?_⟩
  rw [hdevI.1, Polynomial.coeff_C_zero]
  intro h
  have h' : ((2:ℕ) : ℤ_[2]) ^ 2 ∣ ((2 : ℤ) : ℤ_[2]) := by push_cast; exact_mod_cast h
  rw [PadicInt.pow_p_dvd_int_iff] at h'
  norm_num at h'

private theorem hperimI : ∀ gT : Polynomial ℤ_[2], gT.Monic →
    gT.natDegree = fI.natDegree →
    (∀ k, (2:ℤ_[2]) ^ 2 ∣ (fI - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[2], gS.Monic → gS ∣ gT → IsPure kI gS u ℓ →
    ∀ hne : (sideSet kI gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kI gS (sideMin kI gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kI), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kI)ˣ, resPoly (2:ℤ_[2]) kI gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kI.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kI.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  letI : Field (resField kI) := instFieldResField hkey
  have hbound := GateKit.perim_degree_bound hpi hkey (N := 2) (by norm_num) hresI hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hc
  rw [hkdeg, hfdeg] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 1 * 2 * ψ.natDegree ≤ ℓ * 2 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hℓ)
  omega

theorem gate_inert_two :
    Uniformity.Density.DecidedAt ℤ_[2] 2 ⟨{(1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 2 2 ![3, 1]) := by
  have h := decidedAt_of_leaf_certificate (O := ℤ_[2]) (π := (2:ℤ_[2])) hpi (n := 2) (N := 2)
    (by norm_num) aI hkey (μ := 1) (by norm_num) hresI hvisI htermI hperimI
  rwa [hordI] at h


end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_inert_two
end AxCheck
