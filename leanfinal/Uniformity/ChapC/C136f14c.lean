/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136f14b

/-!
# Uniformity.ChapC.C136f14c — the anchored F1.4/F1.5 closure unit

This file supplies the fixed-grade absolute-read carry law and the honest weighted
anchored coefficient-convolution assembler left open by A-C.24'.  The terminal audit
keeps the resulting slot weights explicit and isolates the additional stationarity
premise needed to turn them into C.39's single constant scalar.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14c

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e1
open Uniformity.Density.Tower.C136l2e2 Uniformity.Density.Tower.C136l2e3
open Uniformity.Density.Tower.C136f14b

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

private theorem inner_floor (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]
  exact L.hκ

private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1
    (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx =
      dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

private theorem shift_spec (L : LevelDatum F H₀ hpin) (m : ℕ) :
    L.shift m < L.ℓ ∧ L.shift m * L.u ≡ m [MOD L.ℓ] := by
  have hex : ∃ b ∈ (↑(Finset.range L.ℓ) : Set ℕ), b * L.u % L.ℓ = m % L.ℓ :=
    (Uniformity.Density.Induction.class_sep_bij L.hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt m L.hℓ)
  have hnone : (List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ) ≠ none := by
    intro hn
    obtain ⟨b, hb, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    exact (List.find?_eq_none.mp hn b (List.mem_range.mpr hb)) (by simpa using hcong)
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : L.shift m = c := by rw [LevelDatum.shift, hc]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some hc), ?_⟩
  have hp := List.find?_some hc
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

private theorem shift_unique (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact Uniformity.Density.Induction.class_sep L.hcop hb hlt (hcong.trans hsp.symm)

/-- At an exact finite level height, the left endpoint is the canonical anchor plus the
integer offset used in `dv2FullReadPoly_eq_shift`. -/
private theorem sideMin_eq_shift_add (L : LevelDatum F H₀ hpin) {z : Polynomial O}
    {k : ℕ} (hk : dv2Hgt L z = (k : ℕ∞))
    (hne : (dvSideSet F z L.u L.ℓ).Nonempty) {Mz : ℕ}
    (hpz : dvHgt F z (dvSideMin F z L.u L.ℓ hne) = (Mz : ℕ∞)) :
    dvSideMin F z L.u L.ℓ hne = L.shift k +
      ((dvSideMin F z L.u L.ℓ hne - L.shift k) / L.ℓ) * L.ℓ := by
  have hon : DvOnSide F z L.u L.ℓ (dvSideMin F z L.u L.ℓ hne) :=
    dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)
  have hline : L.ℓ * Mz + L.u * dvSideMin F z L.u L.ℓ hne = k := by
    have h := hon.1.symm.trans hk
    rw [hpz] at h
    push_cast [nsmul_eq_mul] at h
    exact_mod_cast h
  have hsmod : dvSideMin F z L.u L.ℓ hne % L.ℓ = L.shift k := by
    refine shift_unique L (Nat.mod_lt _ L.hℓ) ?_
    calc
      (dvSideMin F z L.u L.ℓ hne % L.ℓ) * L.u
          ≡ dvSideMin F z L.u L.ℓ hne * L.u [MOD L.ℓ] :=
            (Nat.mod_modEq _ L.ℓ).mul_right L.u
      _ ≡ k [MOD L.ℓ] := by
        show (dvSideMin F z L.u L.ℓ hne * L.u) % L.ℓ = k % L.ℓ
        rw [← hline, Nat.mul_add_mod]
        simp [Nat.mul_comm]
  have hsle : L.shift k ≤ dvSideMin F z L.u L.ℓ hne := by
    rw [← hsmod]
    exact Nat.mod_le _ _
  have hdvd : L.ℓ ∣ dvSideMin F z L.u L.ℓ hne - L.shift k := by
    have hdiv := Nat.div_add_mod (dvSideMin F z L.u L.ℓ hne) L.ℓ
    exact ⟨dvSideMin F z L.u L.ℓ hne / L.ℓ, by rw [hsmod] at hdiv; omega⟩
  have hmul := Nat.div_mul_cancel hdvd
  omega

/-- The exact-height core of the absolute-read carry law. -/
theorem dv2FullRead_mul_of_eq (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {A B : Polynomial O} {ka kb δ : ℕ}
    (hA : dv2Hgt L A = (ka : ℕ∞)) (hB : dv2Hgt L B = (kb : ℕ∞))
    (hδ : L.shift ka + L.shift kb = L.shift (ka + kb) + L.ℓ * δ) :
    dv2FullRead L (ka + kb) (A * B) =
      AdjoinRoot.root L.r ^ δ * (dv2FullRead L ka A * dv2FullRead L kb B) := by
  classical
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, dv2Hgt, dvSupp_zero_eq_top F L.u L.hℓ] at hA
    exact ENat.coe_ne_top ka hA.symm
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, dv2Hgt, dvSupp_zero_eq_top F L.u L.hℓ] at hB
    exact ENat.coe_ne_top kb hB.symm
  have hAB0 : A * B ≠ 0 := mul_ne_zero hA0 hB0
  have hnA : (dvSideSet F A L.u L.ℓ).Nonempty := dvSideSet_nonempty F hA0 L.u L.hℓ
  have hnB : (dvSideSet F B L.u L.ℓ).Nonempty := dvSideSet_nonempty F hB0 L.u L.hℓ
  have hnAB : (dvSideSet F (A * B) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hAB0 L.u L.hℓ
  obtain ⟨MA, hpA⟩ := exists_pin F hnA
  obtain ⟨MB, hpB⟩ := exists_pin F hnB
  obtain ⟨MAB, hpAB⟩ := exists_pin F hnAB
  have hAB : dv2Hgt L (A * B) = (((ka + kb : ℕ) : ℕ∞)) := by
    change dvSupp F (A * B) L.u L.ℓ = ((ka + kb : ℕ) : ℕ∞)
    change dvSupp F A L.u L.ℓ = (ka : ℕ∞) at hA
    change dvSupp F B L.u L.ℓ = (kb : ℕ∞) at hB
    rw [C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ (inner_floor L) hA0 hB0,
      hA, hB, ← Nat.cast_add]
  let α := (dvSideMin F A L.u L.ℓ hnA - L.shift ka) / L.ℓ
  let β := (dvSideMin F B L.u L.ℓ hnB - L.shift kb) / L.ℓ
  let γ := (dvSideMin F (A * B) L.u L.ℓ hnAB - L.shift (ka + kb)) / L.ℓ
  have hminA : dvSideMin F A L.u L.ℓ hnA = L.shift ka + α * L.ℓ :=
    sideMin_eq_shift_add L hA hnA hpA
  have hminB : dvSideMin F B L.u L.ℓ hnB = L.shift kb + β * L.ℓ :=
    sideMin_eq_shift_add L hB hnB hpB
  have hminAB : dvSideMin F (A * B) L.u L.ℓ hnAB =
      L.shift (ka + kb) + γ * L.ℓ := sideMin_eq_shift_add L hAB hnAB hpAB
  have hminmul : dvSideMin F (A * B) L.u L.ℓ hnAB =
      dvSideMin F A L.u L.ℓ hnA + dvSideMin F B L.u L.ℓ hnB :=
    C133mh3.dvSideMin_mul hπ hh H₀ hpin L.hℓ (inner_floor L)
      hA0 hB0 hnA hnB hnAB
  have hγ : γ = δ + α + β := by
    rw [hminA, hminB, hminAB] at hminmul
    have hℓpos := L.hℓ
    have hδ' := hδ
    rw [Nat.mul_comm L.ℓ δ] at hδ'
    have hmul : γ * L.ℓ = (δ + α + β) * L.ℓ := by
      rw [Nat.add_mul, Nat.add_mul]
      omega
    exact Nat.eq_of_mul_eq_mul_right L.hℓ hmul
  have hsA := dv2FullReadPoly_eq_shift L hπ hA hnA hpA
  have hsB := dv2FullReadPoly_eq_shift L hπ hB hnB hpB
  have hsAB := dv2FullReadPoly_eq_shift L hπ hAB hnAB hpAB
  have hrmul := dv2Res_mul L hπ hh hA0 hB0
  let hexA : ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞) := ⟨hnA, MA, hpA⟩
  let hexB : ∃ (hne : (dvSideSet F B L.u L.ℓ).Nonempty) (M : ℕ),
      dvHgt F B (dvSideMin F B L.u L.ℓ hne) = (M : ℕ∞) := ⟨hnB, MB, hpB⟩
  let hexAB : ∃ (hne : (dvSideSet F (A * B) L.u L.ℓ).Nonempty) (M : ℕ),
      dvHgt F (A * B) (dvSideMin F (A * B) L.u L.ℓ hne) = (M : ℕ∞) :=
    ⟨hnAB, MAB, hpAB⟩
  have hresA : AdjoinRoot.mk L.r (dvResPoly F H₀ hpin A L.u L.ℓ hnA MA hpA) = dv2Res L A := by
    rw [dv2Res, dif_pos hexA]
    congr 1
    exact dvResPoly_congr F H₀ hpin rfl hnA hexA.choose hpA
      hexA.choose_spec.choose_spec
  have hresB : AdjoinRoot.mk L.r (dvResPoly F H₀ hpin B L.u L.ℓ hnB MB hpB) = dv2Res L B := by
    rw [dv2Res, dif_pos hexB]
    congr 1
    exact dvResPoly_congr F H₀ hpin rfl hnB hexB.choose hpB
      hexB.choose_spec.choose_spec
  have hresAB : AdjoinRoot.mk L.r
      (dvResPoly F H₀ hpin (A * B) L.u L.ℓ hnAB MAB hpAB) = dv2Res L (A * B) := by
    rw [dv2Res, dif_pos hexAB]
    congr 1
    exact dvResPoly_congr F H₀ hpin rfl hnAB hexAB.choose hpAB
      hexAB.choose_spec.choose_spec
  rw [dv2FullRead, hsAB, dv2FullRead, hsA, dv2FullRead, hsB,
    map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
    AdjoinRoot.mk_X, hresAB, hresA, hresB, hrmul, show
      (dvSideMin F (A * B) L.u L.ℓ hnAB - L.shift (ka + kb)) / L.ℓ = γ by rfl,
    show (dvSideMin F A L.u L.ℓ hnA - L.shift ka) / L.ℓ = α by rfl,
    show (dvSideMin F B L.u L.ℓ hnB - L.shift kb) / L.ℓ = β by rfl, hγ]
  simp only [pow_add]
  ring

/-- ★ The recorded L2E2 absolute-read carry law, now inhabited.  Strict-below reads
vanish; at two exact heights it is `dv2FullRead_mul_of_eq`. -/
theorem dv2FullReadCarryLaw : Dv2FullReadCarryLawStatement O := by
  intro π F hπ hh H₀ hpin L A B ka kb δ hka hkb hδ
  rcases eq_or_ne A 0 with rfl | hA0
  · have hz : dv2FullRead L ka (0 : Polynomial O) = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by rw [dv2Hgt_zero]; exact ENat.coe_lt_top ka)
    have hzsum : dv2FullRead L (ka + kb) (0 : Polynomial O) = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by rw [dv2Hgt_zero]; exact ENat.coe_lt_top (ka + kb))
    rw [zero_mul, hzsum, hz, zero_mul, mul_zero]
  rcases eq_or_ne B 0 with rfl | hB0
  · have hz : dv2FullRead L kb (0 : Polynomial O) = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by rw [dv2Hgt_zero]; exact ENat.coe_lt_top kb)
    have hzsum : dv2FullRead L (ka + kb) (0 : Polynomial O) = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by rw [dv2Hgt_zero]; exact ENat.coe_lt_top (ka + kb))
    rw [mul_zero, hzsum, hz, mul_zero, mul_zero]
  have hAfin : dv2Hgt L A ≠ ⊤ := by
    change dvSupp F A L.u L.ℓ ≠ ⊤
    exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hA0
  have hBfin : dv2Hgt L B ≠ ⊤ := by
    change dvSupp F B L.u L.ℓ ≠ ⊤
    exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hB0
  obtain ⟨KA, hKA'⟩ := ENat.ne_top_iff_exists.1 hAfin
  obtain ⟨KB, hKB'⟩ := ENat.ne_top_iff_exists.1 hBfin
  have hKA : dv2Hgt L A = (KA : ℕ∞) := hKA'.symm
  have hKB : dv2Hgt L B = (KB : ℕ∞) := hKB'.symm
  have hkaNat : ka ≤ KA := by rw [hKA] at hka; exact_mod_cast hka
  have hkbNat : kb ≤ KB := by rw [hKB] at hkb; exact_mod_cast hkb
  rcases hkaNat.eq_or_lt with rfl | hkaLt
  · rcases hkbNat.eq_or_lt with rfl | hkbLt
    · exact dv2FullRead_mul_of_eq L hπ hh hKA hKB hδ
    · have hAB : dv2Hgt L (A * B) = (((ka + KB : ℕ) : ℕ∞)) := by
        change dvSupp F (A * B) L.u L.ℓ = ((ka + KB : ℕ) : ℕ∞)
        change dvSupp F A L.u L.ℓ = (ka : ℕ∞) at hKA
        change dvSupp F B L.u L.ℓ = (KB : ℕ∞) at hKB
        rw [C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ (inner_floor L) hA0 hB0,
          hKA, hKB, ← Nat.cast_add]
      have hleft : dv2FullRead L (ka + kb) (A * B) = 0 :=
        dv2FullRead_eq_zero_of_lt L hπ (by rw [hAB]; exact_mod_cast Nat.add_lt_add_left hkbLt ka)
      have hright : dv2FullRead L kb B = 0 :=
        dv2FullRead_eq_zero_of_lt L hπ (by rw [hKB]; exact_mod_cast hkbLt)
      rw [hleft, hright, mul_zero, mul_zero]
  · have hAB : dv2Hgt L (A * B) = (((KA + KB : ℕ) : ℕ∞)) := by
      change dvSupp F (A * B) L.u L.ℓ = ((KA + KB : ℕ) : ℕ∞)
      change dvSupp F A L.u L.ℓ = (KA : ℕ∞) at hKA
      change dvSupp F B L.u L.ℓ = (KB : ℕ∞) at hKB
      rw [C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ (inner_floor L) hA0 hB0,
        hKA, hKB, ← Nat.cast_add]
    have hleft : dv2FullRead L (ka + kb) (A * B) = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by
        rw [hAB]
        exact_mod_cast Nat.add_lt_add_of_lt_of_le hkaLt hkbNat)
    have hright : dv2FullRead L ka A = 0 :=
      dv2FullRead_eq_zero_of_lt L hπ (by rw [hKA]; exact_mod_cast hkaLt)
    rw [hleft, hright, zero_mul, mul_zero]

/-! ## The anchored, weighted coefficient convolution -/

/-- The honest anchored convolution carrier.  Unlike ordinary polynomial
multiplication, every antidiagonal term retains the absolute-read carry belonging to
its two line heights. -/
noncomputable def dv2ResPolyAnchWeightedConv (L : LevelDatum F H₀ hpin)
    (Ψ g z : Polynomial O) (u₂ ℓ₂ : ℕ)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (Mg Mz : ℕ)
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞)) :
    Polynomial (AdjoinRoot L.r) :=
  open Classical in
  (Finset.range (dv2SideDeg L Ψ g u₂ ℓ₂ hng +
      dv2SideDeg L Ψ z u₂ ℓ₂ hnz + 1)).sum fun t =>
    Polynomial.C
      (∑ t₁ ∈ Finset.range (t + 1),
        if t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng ∧
            t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz then
          AdjoinRoot.root L.r ^
              L.cocycle (Mg - t₁ * u₂) (Mz - (t - t₁) * u₂) *
            ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁ *
              (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (t - t₁))
        else 0) * Polynomial.X ^ t

/-- ★ The anchored twin of L2E3's coefficient-convolution assembler.  Its premise and
conclusion retain the slot weights forced by `dv2FullReadCarryLaw`; no unweighted
normalization change is made. -/
theorem dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution
    (L : LevelDatum F H₀ hpin) {Ψ g z : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty)
    {Mg Mz Mgz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    (hpgz : dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz) = (Mgz : ℕ∞))
    (hdeg : dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz =
      dv2SideDeg L Ψ g u₂ ℓ₂ hng + dv2SideDeg L Ψ z u₂ ℓ₂ hnz)
    (hconv : ∀ t, t ≤ dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz →
      dv2FullRead L (Mgz - t * u₂)
          (dev Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂)) =
        ∑ t₁ ∈ Finset.range (t + 1),
          if t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng ∧
              t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz then
            AdjoinRoot.root L.r ^
                L.cocycle (Mg - t₁ * u₂) (Mz - (t - t₁) * u₂) *
              ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁ *
                (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (t - t₁))
          else 0) :
    dv2ResPolyAnch L Ψ (g * z) u₂ ℓ₂ hngz Mgz hpgz =
      dv2ResPolyAnchWeightedConv L Ψ g z u₂ ℓ₂ hng hnz Mg Mz hpg hpz := by
  classical
  apply Polynomial.ext
  intro t
  by_cases ht : t ≤ dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz
  · rw [dv2ResPolyAnch_coeff_of_le L hngz hpgz ht,
      dv2ResPolyAnchWeightedConv,
      Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
      if_pos (by rw [← hdeg]; exact Nat.lt_succ_of_le ht), hconv t ht]
  · rw [dv2ResPolyAnch_coeff_of_gt L hngz hpgz (by omega),
      dv2ResPolyAnchWeightedConv,
      Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
      if_neg (by rw [← hdeg]; omega)]

/-- A weighted convolution is an ordinary scalar multiple exactly when its slot
weights are stationary.  This is the terminal normalization interface exposed by the
anchored assembly. -/
theorem dv2ResPolyAnchWeightedConv_eq_C_mul_of_weight_stationary
    (L : LevelDatum F H₀ hpin) {Ψ g z : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Mg Mz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    {c : AdjoinRoot L.r}
    (hweight : ∀ t t₁, t₁ ≤ t →
      t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng →
      t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz →
      AdjoinRoot.root L.r ^
        L.cocycle (Mg - t₁ * u₂) (Mz - (t - t₁) * u₂) = c) :
    dv2ResPolyAnchWeightedConv L Ψ g z u₂ ℓ₂ hng hnz Mg Mz hpg hpz =
      Polynomial.C c * (dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg *
        dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz) := by
  classical
  apply Polynomial.ext
  intro t
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases ht : t < dv2SideDeg L Ψ g u₂ ℓ₂ hng +
      dv2SideDeg L Ψ z u₂ ℓ₂ hnz + 1
  · rw [dv2ResPolyAnchWeightedConv,
      Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_pos ht]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    by_cases hg₁ : t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng
    · by_cases hz₁ : t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz
      · rw [if_pos ⟨hg₁, hz₁⟩, hweight t t₁ ht₁t hg₁ hz₁]
      · rw [if_neg (fun h => hz₁ h.2),
          dv2ResPolyAnch_coeff_of_gt L hnz hpz (by omega), mul_zero, mul_zero]
    · rw [if_neg (fun h => hg₁ h.1),
        dv2ResPolyAnch_coeff_of_gt L hng hpg (by omega), zero_mul, mul_zero]
  · rw [dv2ResPolyAnchWeightedConv,
      Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg ht]
    symm
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun t₁ ht₁ => ?_
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    rcases Nat.lt_or_ge (dv2SideDeg L Ψ g u₂ ℓ₂ hng) t₁ with hg₁ | hg₁
    · rw [dv2ResPolyAnch_coeff_of_gt L hng hpg hg₁, zero_mul, mul_zero]
    · have hz₁ : dv2SideDeg L Ψ z u₂ ℓ₂ hnz < t - t₁ := by omega
      rw [dv2ResPolyAnch_coeff_of_gt L hnz hpz hz₁, mul_zero, mul_zero]

/-!
## Exact C.39 boundary

For the block/complement split the complement outer side has degree `0`.  Consequently
the weighted convolution above specializes at slot `t` to the carry

`root ^ L.cocycle (M₂' - t*u₂) (complementConst L f)`.

The re-signed C.39 scalar instead uses the base-slot carry

`root ^ L.cocycle M₂' (complementConst L f)`

at every coefficient.  `dv2ResPolyAnchWeightedConv_eq_C_mul_of_weight_stationary`
therefore identifies the exact remaining normalization obligation: equality of those
powers through the block side degree.  The enacted hypotheses give
`Nat.Coprime u₂ ℓ₂`, not `L.ℓ ∣ u₂`, and no landed theorem makes this inner cocycle
stationary under subtraction by `t*u₂`.  No theorem named `dv2ResPolyAnch_scalar` is
declared here without that supplier.
-/

/-! ## F1.5's formal adapter over the repaired carrier -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField
    (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- The landed F1.5 adapter, transposed without mathematical change to
`dv2ResPolyAnch`.  Thus C.38 fires immediately once the re-signed C.39 scalar identity
and its scalar nonvanishing are supplied. -/
theorem dv2ResPolyAnch_radical_eq_of_scalar (L : LevelDatum F H₀ hpin)
    {f Ψ : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
      (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞))
    {c : AdjoinRoot L.r} (hc : c ≠ 0)
    (hscalar : dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂ =
      Polynomial.C c *
        dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂') :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree =
        (dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂ ↔
        q ∣ dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂') := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  have hunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero).mpr hc)
  constructor
  · by_cases hQ : dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂' = 0
    · rw [hQ, mul_zero] at hscalar
      rw [hscalar, hQ]
    · rw [hscalar, Polynomial.natDegree_mul hunit.ne_zero hQ,
        Polynomial.natDegree_C, zero_add]
  · intro q _hqmonic _hqirr
    rw [hscalar, hunit.dvd_mul_left]

end Uniformity.Density.Tower.C136f14c

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14c.dv2FullRead_mul_of_eq
#print axioms Uniformity.Density.Tower.C136f14c.dv2FullReadCarryLaw
#print axioms Uniformity.Density.Tower.C136f14c.dv2ResPolyAnchWeightedConv
#print axioms Uniformity.Density.Tower.C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution
#print axioms Uniformity.Density.Tower.C136f14c.dv2ResPolyAnchWeightedConv_eq_C_mul_of_weight_stationary
#print axioms Uniformity.Density.Tower.C136f14c.dv2ResPolyAnch_radical_eq_of_scalar

end AxCheck
