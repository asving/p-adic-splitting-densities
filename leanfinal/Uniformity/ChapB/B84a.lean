/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B82
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B84a — the `q = 3` INERT gate

**Chapter B, NODE B.84 instance (i)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10), ENV-C
concrete. One signed declaration: `gate_inert_three`.

*The instance* (blueprint's row (i)): `O := ℤ_[3]`, `π := 3`, `a = ![4, 0]`, so
`f = monicPoly a = X² + 4`; key `φ = X² + 1` (`m = 2`, irreducible over `𝔽₃`), `μ = 1`; window
`N = 2`. The value `⟨{(1,2)}⟩` coincides with B.83 (i)'s **by design** — same genre — while every
piece of arithmetic underneath is different (`𝔽₃`-irreducibility of `X² + 1`, `3`-adic heights,
`residueCard = 3`). That non-coincidence-proofing is GC-11's whole point: G.23's refuted count
law passed every `q = 2` check and died at `ℤ_[3]`.

| datum | value | how it is proved here |
|---|---|---|
| `f = φ + 3` | `hfeq` | `C 4 = 1 + C 3` |
| `f‾ = φ‾ ^ 1` | `hresI` | `residue ℤ_[3] 3 = 0` |
| `φ‾ = X² + 1` irreducible over `𝔽₃` | `hkirr` | no root: `0²+1 = 1`, `1²+1 = 2`, `2²+1 = 2` (`decide` on `ZMod 3`, transported along `PadicInt.residueField`) — the genuinely new leg the blueprint names |
| `dev φ f = (3, 1)` | `hdevI` | B.06 `dev_unique` via the kit's `dev_two` |
| heights `(1, 0, ⊤)` | `hfinI` | B.08 (`3 ∣ 3`, `9 ∤ 3`) |
| only two-point side `(u,ℓ) = (1,1)` | `hslopeI` | B.42's bound (`ℓ ≤ 2`, `u ≤ 1`) + the kit's polygon read |
| `sideSet = {0,1}`, `sideDeg = 1`, `d = 1` | `hside11`/`hsdeg11` | |
| `Visible π φ f 2` | `hvisI` | `¬ 3² ∣ 3` |
| `order1Type = ⟨{(1,2)}⟩` | `hordI` | `ℓ = 1`, one degree-1 residual factor, `m · deg ψ = 2` |

## The A-F.12 discharge, with this instance's arithmetic displayed

`m = φ.natDegree = 2`, `n = 2`, so with `ℓ ≥ 1` and `deg ψ ≥ 1`:

```
2 ≤ 1 · 2 · 1 ≤ ℓ · 2 · deg ψ = gS.natDegree ≤ gT.natDegree = n = 2   ⟹   deg ψ = 1
```

— the SECOND disjunct, uniform in the window-class member, `B-BOX-1`-free.

DEPENDS (direct): B.06 · B.08 · B.20 · B.30 · B.66 · B.66a · B.73 · B.75 · **B.82** · `B83Kit` ·
landed `LocalData.lean` §6 (the `ℤ_[3]` bundle, `residueCard_padicInt`) · mathlib
`PadicInt.prime_p`, `PadicInt.residueField`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `HE-SIG` → **Lean theorem**; `W12-ORACLE` → **executable regression** retained;
jointly with B.83 this node is the chapter's GC-11 two-prime obligation.

SOURCE: `EFF.W12.29`; `blueprint/CONVENTIONS_2026-08-15.md` GC-11's RATIONALE (the G.23
refutation at `ℤ_[3]`); `EFF.HE6.37` / `EFF.HE6R1.29`.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private noncomputable abbrev aJ : Fin 2 → ℤ_[3] := ![4, 0]
private noncomputable abbrev fJ : Polynomial ℤ_[3] := Uniformity.Density.monicPoly aJ
private noncomputable abbrev kJ : Polynomial ℤ_[3] := X ^ 2 + 1

private theorem hpi3 : Irreducible (3 : ℤ_[3]) := (PadicInt.prime_p (p := 3)).irreducible

private theorem hkmon : kJ.Monic := by unfold kJ; monicity!
private theorem hkdeg : kJ.natDegree = 2 := by unfold kJ; compute_degree!
private theorem hkdegW : kJ.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree hkmon.ne_zero, hkdeg]; rfl
private theorem hfdeg : fJ.natDegree = 2 := Uniformity.Density.monicPoly_natDegree aJ
private theorem hfmon : fJ.Monic := Uniformity.Density.monicPoly_monic aJ
private theorem hfdegmu : fJ.natDegree = 1 * kJ.natDegree := by rw [hfdeg, hkdeg]

private theorem hfnorm : fJ = X ^ 2 + C 4 := by
  simp [Uniformity.Density.monicPoly, fJ, aJ, Fin.sum_univ_two]

private theorem hfeq : fJ = C 3 + 1 * kJ := by
  have h4 : (C 4 : Polynomial ℤ_[3]) = C 3 + 1 := by
    rw [← Polynomial.C_1, ← Polynomial.C_add]; norm_num
  rw [hfnorm, h4]
  unfold kJ
  ring

private theorem hres3 : IsLocalRing.residue ℤ_[3] 3 = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  rw [hpi3.maximalIdeal_eq, Ideal.mem_span_singleton]

private theorem hkirr : Irreducible (kJ.map (IsLocalRing.residue ℤ_[3])) := by
  set e := PadicInt.residueField (p := 3) with he
  have hmap : (kJ.map (IsLocalRing.residue ℤ_[3])).map (e : ResidueField ℤ_[3] →+* ZMod 3)
      = X ^ 2 + 1 := by unfold kJ; simp
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hkmon.natDegree_map, hkdeg]; decide
  · intro x hx
    have h1 : ((kJ.map (IsLocalRing.residue ℤ_[3])).map
        (e : ResidueField ℤ_[3] →+* ZMod 3)).eval (e x)
        = e ((kJ.map (IsLocalRing.residue ℤ_[3])).eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom (e : ResidueField ℤ_[3] →+* ZMod 3) x
    rw [hmap, hx] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_zero] at h1
    revert h1
    generalize (e x) = y
    revert y
    decide

private theorem hkey : IsKey kJ := ⟨hkmon, by rw [hkdeg]; norm_num, hkirr⟩

private theorem hresI : fJ.map (IsLocalRing.residue ℤ_[3])
    = (kJ.map (IsLocalRing.residue ℤ_[3])) ^ 1 := by
  rw [pow_one, hfeq, one_mul, Polynomial.map_add, Polynomial.map_C, hres3, Polynomial.C_0,
    zero_add]

private theorem hdevI : dev kJ fJ 0 = C 3 ∧ dev kJ fJ 1 = 1 :=
  GateKit.dev_two hkmon (by rw [hkdeg]; norm_num)
    (lt_of_le_of_lt Polynomial.degree_C_le (by rw [hkdegW]; decide))
    (by rw [Polynomial.degree_one, hkdegW]; decide) hfeq

private theorem hnp0 : npHgt kJ fJ 0 = ((1 : ℕ) : ℕ∞) := by
  rw [npHgt, hdevI.1, GateKit.gaussVal_C]
  exact GateKit.padic_addVal (p := 3) (k := 1) (a := 3) (by norm_num) (by norm_num) (by norm_num)

private theorem hnp1 : npHgt kJ fJ 1 = ((0 : ℕ) : ℕ∞) := by
  rw [npHgt, hdevI.2, show (1 : Polynomial ℤ_[3]) = C 1 from (Polynomial.C_1).symm,
    GateKit.gaussVal_C, GateKit.addVal_one hpi3]
  rfl

private theorem htopI : ∀ j, 1 < j → npHgt kJ fJ j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt hkmon (by rw [hkdeg]; norm_num) fJ ?_
  rw [hfdeg, hkdeg]; omega

private theorem hfinI : ∀ j, j ≤ 1 → npHgt kJ fJ j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  interval_cases j
  · rw [hnp0]; norm_num
  · rw [hnp1]; norm_num

private theorem hBI : ∀ j, j ≤ fJ.natDegree → (npHgt kJ fJ j).toNat ≤ 1 := by
  intro j _
  by_cases h : j ≤ 1
  · interval_cases j
    · rw [hnp0]; decide
    · rw [hnp1]; decide
  · rw [htopI j (by omega)]; decide

private theorem hread11 : suppVal kJ fJ 1 1 = ((1 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet kJ fJ 1 1 ↔ (j ≤ 1 ∧ 1 * (if j = 0 then 1 else 0) + 1 * j = 1)) :=
  GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI (by norm_num)
    (M := 1) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hside11 : sideSet kJ fJ 1 1 = {0, 1} := by
  ext j
  rw [hread11.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hcard11 : 1 < (sideSet kJ fJ 1 1).card := by rw [hside11]; decide

private theorem hsdeg11 : ∀ hne : (sideSet kJ fJ 1 1).Nonempty, sideDeg kJ fJ 1 1 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hside11]; decide)
      (by intro j hj; rw [hside11] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 1) (by rw [hside11]; decide)
      (by intro j hj; rw [hside11] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslopeI : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet kJ fJ u ℓ).card → u = 1 ∧ ℓ = 1 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ := GateKit.slope_bounds_of_le hkey hfmon hfdegmu hℓ hcop hcard hBI
  rw [hfdeg] at hℓle
  interval_cases ℓ
  · interval_cases u
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI
        (u := 0) (ℓ := 1) (by norm_num) (M := 0) (by intro j hj; exact Nat.zero_le _)
        ⟨1, by norm_num⟩
      have huniq : ∀ j ∈ sideSet kJ fJ 0 1, j = 1 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j <;> revert hval <;> decide
      have : (sideSet kJ fJ 0 1).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega
    · exact ⟨rfl, rfl⟩
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso
      have hread := GateKit.polygon_read (n := 2) (m := 1) hfdeg (by norm_num) hfinI htopI
        (u := 1) (ℓ := 2) (by norm_num) (M := 1)
        (by intro j hj; interval_cases j <;> norm_num) ⟨1, by norm_num⟩
      have huniq : ∀ j ∈ sideSet kJ fJ 1 2, j = 1 := by
        intro j hj
        obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
        interval_cases j <;> revert hval <;> decide
      have : (sideSet kJ fJ 1 2).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
      omega

private theorem hslopeFinsetI : slopeFinset (3 : ℤ_[3]) kJ fJ = {(1, 1)} := by
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

private theorem hd1I : ∀ p ∈ slopeFinset (3 : ℤ_[3]) kJ fJ,
    ∀ hne : (sideSet kJ fJ p.1 p.2).Nonempty, sideDeg kJ fJ p.1 p.2 hne = 1 := by
  intro p hp hne
  rw [hslopeFinsetI, Finset.mem_singleton] at hp
  subst hp
  exact hsdeg11 hne

private theorem hordI : order1Type (3 : ℤ_[3]) kJ fJ = ⟨{(1, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 hkey hfmon hfdegmu hd1I
  rw [hslopeFinsetI, hkdeg] at h
  rw [h]
  rfl

private theorem htermI : ¬ NeedsDescent (3 : ℤ_[3]) kJ fJ := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 hkey hfmon hfdegmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslopeI u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdeg11 hne

private theorem hvisI : Visible (3 : ℤ_[3]) kJ fJ 2 := by
  refine ⟨0, ?_⟩
  rw [hdevI.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 3) (a := 3) (by norm_num) (by norm_num)

private theorem hperimI : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = fJ.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (fJ - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure kJ gS u ℓ →
    ∀ hne : (sideSet kJ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kJ gS (sideMin kJ gS u ℓ hne) = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kJ), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kJ)ˣ, resPoly (3 : ℤ_[3]) kJ gS u ℓ hne H₀ = c • ψ) →
        ((ℓ = 1 ∧ kJ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kJ.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  letI : Field (resField kJ) := instFieldResField hkey
  have hbound := GateKit.perim_degree_bound hpi3 hkey (N := 2) (by norm_num) hresI hgTm hdegT
    hcongT hℓ hcop hgSm hdvd hpure hne hH₀ hc
  rw [hkdeg, hfdeg] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 1 * 2 * ψ.natDegree ≤ ℓ * 2 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hℓ)
  omega

/-- **B.84 (i) — the `q = 3` inert gate.** The level-2 class of `![4, 0]` over `ℤ_[3]` is
decided at `⟨{(1,2)}⟩`: every monic quadratic lift of `X² + 4` mod `9` is inert. -/
theorem gate_inert_three :
    Uniformity.Density.DecidedAt ℤ_[3] 2 ⟨{(1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 2 2 ![4, 0]) := by
  have h := decidedAt_of_leaf_certificate (O := ℤ_[3]) (π := (3 : ℤ_[3])) hpi3 (n := 2) (N := 2)
    (by norm_num) aJ hkey (μ := 1) (by norm_num) hresI hvisI htermI hperimI
  rwa [hordI] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_inert_three
end AxCheck
