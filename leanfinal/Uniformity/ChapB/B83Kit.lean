/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B06
import Uniformity.ChapB.B08
import Uniformity.ChapB.B30
import Uniformity.ChapB.B34
import Uniformity.ChapB.B35b
import Uniformity.ChapB.B66
import Uniformity.ChapB.B66a
import Uniformity.ChapB.B73
import Uniformity.ChapB.B75
import Uniformity.Density.Drainage
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapB.B83Kit — the §10 gate evaluation kit (booked shared helper)

**Chapter B, §10 support file.** *Not a DAG node and not a signed statement.* The blueprint
(`blueprint/CHAP-B_leaf_layer.md` §10, NODE B.83 PROOF, SIZE field) books this file explicitly:

> "the step-1–5 evaluation kit shared by (i)–(iv) is a private-helper candidate — if two files
> want the same helper, the orchestrator books it, RE-PLAN, never a silent copy"

and, at the A-F.12 ⚠ discharge step:

> "Size: ≈ 15 lines per gate file, shared helper candidate (the step-1–5 evaluation kit's
> sibling — if two files want it, the orchestrator books it, never a silent copy)."

Ten gate instances (B.83 a–d, B.84 a–d, B.85 a–b) want all of it, so it is booked here once,
in the private namespace `Uniformity.Density.Leaf.GateKit`, rather than copied ten times.

## What is in the kit

| name | what it does | node text it implements |
|---|---|---|
| `mem_sideSet_iff` | membership in B.16's `sideSet`, unfolded | step 3's finite argmin reads |
| `slope_bounds` | `1 < card (sideSet …)` ⟹ `ℓ ≤ n` and `u ≤ Hb` | step 3's "candidate-slope enumeration is finite by B.42's bound" |
| `separable_of_natDegree_one` | a degree-1 polynomial over a field is separable | step 4's "its derivative is a nonzero constant, a unit in `resField φ`" |
| `not_needsDescent_of_sideDeg_one` | `¬ NeedsDescent` from `sideDeg = 1` on every two-point side | step 4's conclusion |
| `resFactorFinset_eq_singleton` | B.66a's residual-factor supplier at a degree-1 residual | step 6's `order1Type` evaluation |
| `order1Type_of_sideDeg_one` | `order1Type π φ f = ⟨slopeFinset.val.map (fun p => (p.2, m))⟩` | step 6's "`order1Type` unfolded on the step-3 finsets" |
| `perim_degree_bound` | `ℓ · φ.natDegree · ψ.natDegree = gS.natDegree ≤ n`, UNIFORMLY in the window-class member | **the A-F.12 ⚠ discharge step, verbatim** |

`perim_degree_bound` is the A-F.12 display transcribed line for line: `gS.natDegree = k · m`
from unique factorization of `ḡT = φ̄ ^ μ` (which needs `0 < N`, supplied by the instance's
`hvis`); `ψ.natDegree = sideDeg` from B.30's `natDegree_resPoly` (with `c` a unit);
`ℓ · sideDeg = k` from the landed B.35b `sideDeg_of_pure`; and
`gS.natDegree ≤ gT.natDegree = n` from `Polynomial.natDegree_le_of_dvd` plus the class's degree
pin. The per-instance arithmetic (`m = 2, ℓ = 1, n = 2 ⟹ deg ψ ≤ 1`, …) is displayed in each
gate file, not here — the blueprint pins those numbers per instance.

## Trust boundary

Nothing here is a signed node statement, and nothing here is a definition: every declaration is
a theorem about the landed B.16/B.20/B.29/B.30/B.34/B.35b/B.66a/B.73 vocabulary, proved from it.
The one declaration whose *statement* deserves a read is `perim_degree_bound`, because it is the
uniform form of the gates' `hperim` obligation; its hypotheses are literally the binders of
B.80/B.82's re-signed `hperim` clause, so a mismatch would show up as a gate that does not
compile.

## Status

Sorry-free, axiom-free (Lean core only). No `axiom` is declared or consumed here — in particular
not the 2026-08-16 B.42 literature cite (the gates pick that up through B.80/B.82).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf.GateKit

open Polynomial IsLocalRing Uniformity.Density.Leaf Uniformity.Hensel
  IsDiscreteValuationRing

/-! ## 1. Two field-level helpers -/

theorem isCoprime_of_isUnit_right {R : Type*} [CommSemiring R] {x y : R} (hy : IsUnit y) :
    IsCoprime x y := by
  obtain ⟨u, rfl⟩ := hy
  exact ⟨0, ↑u⁻¹, by simp⟩

theorem separable_of_natDegree_one {K : Type*} [Field K] {p : Polynomial K}
    (h : p.natDegree = 1) : p.Separable := by
  have hc1 : p.coeff 1 ≠ 0 := by
    have : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 (by
      intro h0; rw [h0] at h; simp at h)
    rwa [Polynomial.leadingCoeff, h] at this
  have hd : derivative p = C (p.coeff 1) := by
    have hle : (derivative p).natDegree = 0 := by
      have := Polynomial.natDegree_derivative_le p
      omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hle, Polynomial.coeff_derivative]
    simp
  rw [Polynomial.separable_def, hd]
  exact isCoprime_of_isUnit_right (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hc1))

-- monic irreducible divisors of a degree-1 polynomial
theorem monic_irred_dvd_natDegree_one {K : Type*} [Field K] {R : Polynomial K}
    (hR : R.natDegree = 1) {ψ : Polynomial K} (hm : ψ.Monic) (hi : Irreducible ψ)
    (hd : ψ ∣ R) : ψ = R * C (R.leadingCoeff)⁻¹ := by
  have hR0 : R ≠ 0 := by intro h0; rw [h0] at hR; simp at hR
  have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hR0
  obtain ⟨v, hv⟩ := hd
  have hv0 : v ≠ 0 := by rintro rfl; rw [mul_zero] at hv; exact hR0 hv
  have hψ0 : ψ ≠ 0 := hm.ne_zero
  have hdegs : ψ.natDegree + v.natDegree = 1 := by
    rw [← hR, hv, Polynomial.natDegree_mul hψ0 hv0]
  have hψ1 : ψ.natDegree = 1 := by
    rcases Nat.eq_zero_or_pos ψ.natDegree with h0 | h1
    · exact absurd (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by
        have := hm.coeff_natDegree; rw [h0] at this
        intro hc; rw [hc] at this; exact zero_ne_one this)) : IsUnit (C (ψ.coeff 0)))
        (by rw [← Polynomial.eq_C_of_natDegree_eq_zero h0]; exact hi.not_isUnit)
    · omega
  have hv1 : v.natDegree = 0 := by omega
  have hvC : v = C v.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hv1]; exact Polynomial.eq_C_of_natDegree_eq_zero hv1
  have hlcv : R.leadingCoeff = v.leadingCoeff := by
    rw [hv, Polynomial.leadingCoeff_mul, hm.leadingCoeff, one_mul]
  calc ψ = ψ * C (R.leadingCoeff * R.leadingCoeff⁻¹) := by
        rw [mul_inv_cancel₀ hlc, Polynomial.C_1, mul_one]
    _ = (ψ * C R.leadingCoeff) * C R.leadingCoeff⁻¹ := by rw [Polynomial.C_mul, mul_assoc]
    _ = R * C R.leadingCoeff⁻¹ := by rw [hlcv, ← hvC, ← hv]


/-! ## 2. The polygon-evaluation helpers -/

section Arena

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem mem_sideSet_iff {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact this

/-- The slope bound of B.66a's `slopeSet_finite`, extracted. -/
theorem slope_bounds {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hcard : 1 < (sideSet φ f u ℓ).card) :
    ℓ ≤ f.natDegree ∧
      u ≤ (Finset.range (f.natDegree + 1)).sup (fun j => (npHgt φ f j).toNat) := by
  classical
  set n := f.natDegree with hn
  set Hb := (Finset.range (n + 1)).sup (fun j => (npHgt φ f j).toNat) with hHb
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have key : ∀ j j' : ℕ, j ∈ sideSet φ f u ℓ → j' ∈ sideSet φ f u ℓ → j < j' →
      ℓ ≤ n ∧ u ≤ Hb := by
    intro j j' hj hj' hlt
    have hjs : OnSide φ f u ℓ j := onSide_of_mem_sideSet hj
    have hj's : OnSide φ f u ℓ j' := onSide_of_mem_sideSet hj'
    obtain ⟨H, hH⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hjs)
    obtain ⟨H', hH'⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hj's)
    have heq : ℓ * H + u * j = ℓ * H' + u * j' := onSide_nat_eq hH.symm hH'.symm hjs hj's
    have hmod : j ≡ j' [MOD ℓ] := onSide_modEq hℓ hcop htop hjs hj's
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, Nat.mul_zero] at hk; omega
      · exact h0
    have hj'eq : j' = j + ℓ * k := by omega
    have hHk : H = H' + u * k := by
      have e1 : ℓ * H + u * j = ℓ * H' + u * (j + ℓ * k) := by rw [← hj'eq]; exact heq
      have e2 : ℓ * H = ℓ * (H' + u * k) := by nlinarith [e1]
      exact Nat.eq_of_mul_eq_mul_left hℓ e2
    have hjn : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (mem_sideSet_iff.mp hj).1
    have hj'n : j' < n + 1 := (mem_sideSet_iff.mp hj').1
    have hHle : H ≤ Hb := by
      have hcast : (npHgt φ f j).toNat = H := by rw [← hH]; exact ENat.toNat_coe H
      calc H = (npHgt φ f j).toNat := hcast.symm
        _ ≤ Hb := Finset.le_sup (f := fun j => (npHgt φ f j).toNat) hjn
    refine ⟨?_, ?_⟩
    · have : ℓ * 1 ≤ ℓ * k := Nat.mul_le_mul_left ℓ hk0
      omega
    · have : u * 1 ≤ u * k := Nat.mul_le_mul_left u hk0
      omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  rcases Nat.lt_or_ge a b with h | h
  · exact key a b ha hb h
  · exact key b a hb ha (by omega)

theorem not_needsDescent_of_sideDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    (h1 : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → 1 < (sideSet φ f u ℓ).card →
      ∀ hne : (sideSet φ f u ℓ).Nonempty, sideDeg φ f u ℓ hne = 1) :
    ¬ NeedsDescent π φ f := by
  letI : Field (resField φ) := instFieldResField hφ
  rintro ⟨u, ℓ, hne, H₀, hℓ, hcop, hcard, hH₀, hsep⟩
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have hd := (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀).1
  rw [h1 u ℓ hℓ hcop hcard hne] at hd
  exact hsep (separable_of_natDegree_one hd)

theorem resFactorFinset_eq_singleton (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {p : ℕ × ℕ} (hℓ : 0 < p.2) (hcop : Nat.Coprime p.1 p.2)
    (hne : (sideSet φ f p.1 p.2).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞))
    (hd1 : sideDeg φ f p.1 p.2 hne = 1) :
    ∃ ψ₀ : Polynomial (resField φ), ψ₀.natDegree = 1 ∧ resFactorFinset π φ f p = {ψ₀} := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have htop : suppVal φ f p.1 p.2 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg p.1 p.2)
  set R := resPoly π φ f p.1 p.2 hne H₀ with hRdef
  have hRdeg : R.natDegree = 1 := by
    rw [hRdef, (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀).1, hd1]
  have hR0 : R ≠ 0 := by intro h0; rw [h0] at hRdeg; simp at hRdeg
  refine ⟨R * C R.leadingCoeff⁻¹, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul_leadingCoeff_inv _ hR0]; exact hRdeg
  · have hmon : (R * C R.leadingCoeff⁻¹).Monic := Polynomial.monic_mul_leadingCoeff_inv hR0
    have hdg1 : (R * C R.leadingCoeff⁻¹).natDegree = 1 := by
      rw [Polynomial.natDegree_mul_leadingCoeff_inv _ hR0]; exact hRdeg
    have hirr : Irreducible (R * C R.leadingCoeff⁻¹) := by
      refine Polynomial.irreducible_of_degree_eq_one ?_
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdg1]; rfl
    -- the pinned data is unique: proof irrelevance for `hne`, `Nat.cast` injectivity for `H₀`
    have hpin : ∀ (hne' : (sideSet φ f p.1 p.2).Nonempty) (H₀' : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne') = (H₀' : ℕ∞) →
          resPoly π φ f p.1 p.2 hne' H₀' = R := by
      intro hne' H₀' h'
      have : hne' = hne := rfl
      subst this
      have : (H₀' : ℕ∞) = (H₀ : ℕ∞) := by rw [← h', hH₀]
      have : H₀' = H₀ := by exact_mod_cast this
      subst this
      rfl
    ext ψ
    rw [mem_resFactorFinset hπ hφ hf hdeg hℓ hcop, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hi, hdvd⟩
      exact monic_irred_dvd_natDegree_one hRdeg hm hi (hdvd hne H₀ hH₀)
    · rintro rfl
      refine ⟨hmon, hirr, fun hne' H₀' h' => ?_⟩
      rw [hpin hne' H₀' h']
      exact ⟨C R.leadingCoeff, by
        rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀
          (Polynomial.leadingCoeff_ne_zero.2 hR0), Polynomial.C_1, mul_one]⟩

/-- The pinned height at the left endpoint exists (is finite) for a key/monic instance. -/
theorem exists_H0 {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hne : (sideSet φ f u ℓ).Nonempty) :
    ∃ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := by
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have hmin : sideMin φ f u ℓ hne ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
  obtain ⟨H₀, hH₀⟩ := WithTop.ne_top_iff_exists.mp
    (npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hmin))
  exact ⟨H₀, hH₀.symm⟩

/-- **The order-1 datum when every side has residual degree 1.** -/
theorem order1Type_of_sideDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    (hd1 : ∀ p ∈ slopeFinset π φ f, ∀ hne : (sideSet φ f p.1 p.2).Nonempty,
      sideDeg φ f p.1 p.2 hne = 1) :
    order1Type π φ f
      = ⟨(slopeFinset π φ f).val.map (fun p => (p.2, φ.natDegree))⟩ := by
  classical
  refine Uniformity.FactorizationType.ext ?_
  rw [order1Type_data]
  change _ = Multiset.map (fun p : ℕ × ℕ => (p.2, φ.natDegree)) (slopeFinset π φ f).val
  rw [← Multiset.bind_singleton (β := ℕ × ℕ) (fun p : ℕ × ℕ => (p.2, φ.natDegree))
    (s := (slopeFinset π φ f).val)]
  refine Multiset.bind_congr ?_
  intro p hp
  have hp' : p ∈ slopeFinset π φ f := hp
  obtain ⟨hℓ, hcop, hcard⟩ := mem_slopeFinset_imp hp'
  have hne : (sideSet φ f p.1 p.2).Nonempty :=
    sideSet_nonempty hφ.monic hφ.pos hf hdeg p.1 p.2
  obtain ⟨H₀, hH₀⟩ := exists_H0 hφ hf hdeg hℓ hne
  obtain ⟨ψ₀, hψ₀deg, hψ₀⟩ :=
    resFactorFinset_eq_singleton hπ hφ hf hdeg hℓ hcop hne hH₀ (hd1 p hp' hne)
  rw [hψ₀]
  simp [hψ₀deg]

/-- **A-F.12's uniform perimeter bound.** -/
theorem perim_degree_bound (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {N : ℕ} (hN : 0 < N) {f : Polynomial O} {μ : ℕ}
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    {gT : Polynomial O} (hgTm : gT.Monic) (hdegT : gT.natDegree = f.natDegree)
    (hcong : ∀ k, π ^ N ∣ (f - gT).coeff k)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {gS : Polynomial O} (hgSm : gS.Monic) (hdvd : gS ∣ gT) (hpure : IsPure φ gS u ℓ)
    (hne : (sideSet φ gS u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞))
    {ψ : Polynomial (resField φ)}
    (hc : ∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) :
    ℓ * φ.natDegree * ψ.natDegree ≤ f.natDegree := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  -- step 1 — the class member reduces like `f`
  have hbar : gT.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ := by
    have hsub : (f - gT).map (IsLocalRing.residue O) = 0 := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact (dvd_pow_self π hN.ne').trans (hcong k)
    rw [Polynomial.map_sub, sub_eq_zero] at hsub
    rw [← hsub]; exact hres
  -- step 2 — the monic divisor's reduction is a power of the key's reduction
  have hprime : Prime (φ.map (IsLocalRing.residue O)) := hφ.irred.prime
  have hSdvd : gS.map (IsLocalRing.residue O) ∣ (φ.map (IsLocalRing.residue O)) ^ μ := by
    rw [← hbar]; exact Polynomial.map_dvd _ hdvd
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow hprime μ).1 hSdvd
  have hSbar : gS.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k :=
    Polynomial.eq_of_monic_of_associated (hgSm.map _) ((hφ.monic.map _).pow _) hassoc
  have hSdeg : gS.natDegree = k * φ.natDegree := by
    rw [natDegree_eq_of_map_eq hgSm hSbar, Polynomial.natDegree_pow,
      hφ.monic.natDegree_map (IsLocalRing.residue O)]
  -- step 3 — the residual degree is the side's residual degree
  have htop : suppVal φ gS u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hgSm hSdeg u ℓ)
  have hRdeg := (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀).1
  obtain ⟨c, hcψ⟩ := hc
  have hψdeg : ψ.natDegree = sideDeg φ gS u ℓ hne := by
    rw [← hRdeg, hcψ, Units.smul_def, Polynomial.smul_eq_C_mul,
      Polynomial.natDegree_C_mul (Units.ne_zero c)]
  -- step 4 — B.35b: `ℓ · sideDeg = k`
  have hpure' : ℓ * sideDeg φ gS u ℓ hne = k :=
    sideDeg_of_pure hφ.monic hφ.pos hgSm hSdeg hℓ hcop hpure hne
  -- step 5 — the divisor's degree is bounded by the class member's
  have hle : gS.natDegree ≤ f.natDegree := by
    rw [← hdegT]; exact Polynomial.natDegree_le_of_dvd hdvd hgTm.ne_zero
  calc ℓ * φ.natDegree * ψ.natDegree
      = (ℓ * sideDeg φ gS u ℓ hne) * φ.natDegree := by rw [hψdeg]; ring
    _ = gS.natDegree := by rw [hpure', hSdeg]
    _ ≤ f.natDegree := hle


/-! ## 3. The instance-evaluation kit — heights, developments, and the polygon read

These are the pieces the ten gate files use to *evaluate* the chapter's vocabulary on a
concrete coefficient vector: exhibited `φ`-adic developments (B.06's `dev_unique`, packaged at
the two/three/four-term shapes the §10 instances need — `μ ≤ 3` throughout), the constant-height
read, and the `ℕ`-valued polygon read that turns `suppVal`/`sideSet` into ordinary natural-number
arithmetic once the finite heights are known. -/

theorem gaussVal_C (a : O) : gaussVal (Polynomial.C a) = addVal O a := by
  rw [gaussVal]; simp

theorem addVal_one (hπ : Irreducible π) : addVal O (1 : O) = 0 := by
  refine Uniformity.Density.addVal_eq_of_dvd_not_dvd hπ (by simp) ?_
  intro h
  exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using h))

theorem one_le_natDegree_of_monic_irreducible {R : Type*} [CommRing R] [Nontrivial R]
    {ψ : Polynomial R} (hm : ψ.Monic) (hi : Irreducible ψ) : 1 ≤ ψ.natDegree := by
  by_contra h
  have h0 : ψ.natDegree = 0 := by omega
  rw [Polynomial.eq_one_of_monic_natDegree_zero hm h0] at hi
  exact not_irreducible_one hi

/-- A two-term `φ`-adic development, exhibited. -/
theorem dev_two {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f a₀ a₁ : Polynomial O} (h0 : a₀.degree < φ.degree) (h1 : a₁.degree < φ.degree)
    (hsum : f = a₀ + a₁ * φ) : dev φ f 0 = a₀ ∧ dev φ f 1 = a₁ := by
  have hbot : (0 : Polynomial O).degree < φ.degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.2 fun h => hφ.ne_zero (Polynomial.degree_eq_bot.1 h)
  have hdeg : ∀ j, ((fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁ else 0) j).degree
      < φ.degree := by
    intro j
    match j with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | (n + 2) => simpa using hbot
  have hs : ∑ j ∈ Finset.range 2,
      (fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁ else 0) j * φ ^ j = f := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [reduceIte, pow_zero, pow_one, mul_one, zero_add]
    exact hsum.symm
  have h := dev_unique hφ hd hdeg hs
  exact ⟨(h 0 (by norm_num)).symm, (h 1 (by norm_num)).symm⟩

/-- A three-term `φ`-adic development, exhibited. -/
theorem dev_three {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f a₀ a₁ a₂ : Polynomial O} (h0 : a₀.degree < φ.degree) (h1 : a₁.degree < φ.degree)
    (h2 : a₂.degree < φ.degree) (hsum : f = a₀ + a₁ * φ + a₂ * φ ^ 2) :
    dev φ f 0 = a₀ ∧ dev φ f 1 = a₁ ∧ dev φ f 2 = a₂ := by
  have hbot : (0 : Polynomial O).degree < φ.degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.2 fun h => hφ.ne_zero (Polynomial.degree_eq_bot.1 h)
  have hdeg : ∀ j, ((fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁
      else if j = 2 then a₂ else 0) j).degree < φ.degree := by
    intro j
    match j with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | 2 => simpa using h2
    | (n + 3) => simpa using hbot
  have hs : ∑ j ∈ Finset.range 3,
      (fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁
        else if j = 2 then a₂ else 0) j * φ ^ j = f := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [reduceIte, pow_zero, pow_one, mul_one, zero_add]
    exact hsum.symm
  have h := dev_unique hφ hd hdeg hs
  exact ⟨(h 0 (by norm_num)).symm, (h 1 (by norm_num)).symm, (h 2 (by norm_num)).symm⟩

/-- A four-term `φ`-adic development, exhibited. -/
theorem dev_four {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f a₀ a₁ a₂ a₃ : Polynomial O} (h0 : a₀.degree < φ.degree) (h1 : a₁.degree < φ.degree)
    (h2 : a₂.degree < φ.degree) (h3 : a₃.degree < φ.degree)
    (hsum : f = a₀ + a₁ * φ + a₂ * φ ^ 2 + a₃ * φ ^ 3) :
    dev φ f 0 = a₀ ∧ dev φ f 1 = a₁ ∧ dev φ f 2 = a₂ ∧ dev φ f 3 = a₃ := by
  have hbot : (0 : Polynomial O).degree < φ.degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.2 fun h => hφ.ne_zero (Polynomial.degree_eq_bot.1 h)
  have hdeg : ∀ j, ((fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁
      else if j = 2 then a₂ else if j = 3 then a₃ else 0) j).degree < φ.degree := by
    intro j
    match j with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | 2 => simpa using h2
    | 3 => simpa using h3
    | (n + 4) => simpa using hbot
  have hs : ∑ j ∈ Finset.range 4,
      (fun j : ℕ => if j = 0 then a₀ else if j = 1 then a₁
        else if j = 2 then a₂ else if j = 3 then a₃ else 0) j * φ ^ j = f := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [reduceIte, pow_zero, pow_one, mul_one, zero_add]
    exact hsum.symm
  have h := dev_unique hφ hd hdeg hs
  exact ⟨(h 0 (by norm_num)).symm, (h 1 (by norm_num)).symm, (h 2 (by norm_num)).symm,
    (h 3 (by norm_num)).symm⟩

/-- Past the development range the height is `⊤`. -/
theorem npHgt_eq_top_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) {j : ℕ} (h : f.natDegree < j * φ.natDegree) : npHgt φ f j = ⊤ := by
  rw [npHgt, dev_eq_zero_of_lt hφ hd f j h]
  exact gaussVal_eq_top_iff.2 rfl

private theorem cast_weight (ℓ k u j : ℕ) :
    ℓ • ((k : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * k + u * j : ℕ) : ℕ∞) := by
  push_cast [nsmul_eq_mul]
  ring

/-- **The polygon read, in `ℕ`.** `H` lists the finite heights at abscissae `0 … m`; every
abscissa past `m` has height `⊤`. `M` is the cleared support value, certified by the two
`ℕ`-side conditions. -/
theorem polygon_read {φ f : Polynomial O} {n m : ℕ} (hn : f.natDegree = n) (hm : m ≤ n)
    {H : ℕ → ℕ} (hfin : ∀ j, j ≤ m → npHgt φ f j = (H j : ℕ∞))
    (htop : ∀ j, m < j → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {M : ℕ}
    (hMle : ∀ j, j ≤ m → M ≤ ℓ * H j + u * j) (hMmem : ∃ j, j ≤ m ∧ ℓ * H j + u * j = M) :
    suppVal φ f u ℓ = (M : ℕ∞) ∧
      ∀ j, (j ∈ sideSet φ f u ℓ ↔ (j ≤ m ∧ ℓ * H j + u * j = M)) := by
  have htoptm : ∀ j, m < j → ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = ⊤ := by
    intro j hj
    rw [htop j hj]
    simp [nsmul_eq_mul, hℓ.ne']
  have hsupp : suppVal φ f u ℓ = (M : ℕ∞) := by
    rw [suppVal]
    refine le_antisymm ?_ ?_
    · obtain ⟨j₀, hj₀m, hj₀⟩ := hMmem
      refine le_trans (Finset.inf_le (b := j₀) (Finset.mem_range.2 (by omega))) ?_
      rw [hfin j₀ hj₀m, cast_weight, hj₀]
    · refine Finset.le_inf ?_
      intro j _
      by_cases hjm : j ≤ m
      · rw [hfin j hjm, cast_weight]
        exact_mod_cast hMle j hjm
      · rw [htoptm j (by omega)]; exact le_top
  refine ⟨hsupp, fun j => ?_⟩
  rw [mem_sideSet_iff]
  constructor
  · rintro ⟨hjlt, hon⟩
    rw [OnSide, hsupp] at hon
    by_cases hjm : j ≤ m
    · refine ⟨hjm, ?_⟩
      rw [hfin j hjm, cast_weight] at hon
      exact_mod_cast hon
    · rw [htoptm j (by omega)] at hon
      exact absurd hon (by simp)
  · rintro ⟨hjm, hval⟩
    refine ⟨by omega, ?_⟩
    rw [OnSide, hsupp, hfin j hjm, cast_weight, hval]

theorem sideMin_eq {φ f : Polynomial O} {u ℓ : ℕ} (hne : (sideSet φ f u ℓ).Nonempty) {a : ℕ}
    (hmem : a ∈ sideSet φ f u ℓ) (hle : ∀ j ∈ sideSet φ f u ℓ, a ≤ j) :
    sideMin φ f u ℓ hne = a :=
  le_antisymm (Finset.min'_le _ a hmem) (Finset.le_min' _ _ _ hle)

theorem sideMax_eq' {φ f : Polynomial O} {u ℓ : ℕ} (hne : (sideSet φ f u ℓ).Nonempty) {b : ℕ}
    (hmem : b ∈ sideSet φ f u ℓ) (hle : ∀ j ∈ sideSet φ f u ℓ, j ≤ b) :
    sideMax φ f u ℓ hne = b :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hmem)

/-- The height sup bound that feeds `slope_bounds`. -/
theorem slope_bounds_of_le {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) {u ℓ B : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hcard : 1 < (sideSet φ f u ℓ).card)
    (hB : ∀ j, j ≤ f.natDegree → (npHgt φ f j).toNat ≤ B) :
    ℓ ≤ f.natDegree ∧ u ≤ B := by
  obtain ⟨h1, h2⟩ := slope_bounds hφ hf hdeg hℓ hcop hcard
  exact ⟨h1, le_trans h2 (Finset.sup_le fun j hj => hB j (by
    have := Finset.mem_range.1 hj; omega))⟩

end Arena

/-! ## 4. The concrete-bundle helpers (`φ = X`, and `ℤ_[p]` arithmetic)

`isKey_X` is the `φ = X` half of the B.15 dictionary the `μ ≥ 2` instances use; the `Padic`
section reduces every divisibility/valuation obligation over `ℤ_[p]` to ordinary integer
arithmetic through mathlib's `PadicInt.pow_p_dvd_int_iff`, so `norm_num` can discharge it. -/

theorem isKey_X {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsKey (X : Polynomial O) := by
  refine ⟨Polynomial.monic_X, by rw [Polynomial.natDegree_X]; norm_num, ?_⟩
  rw [Polynomial.map_X]
  exact Polynomial.irreducible_X

section Padic
variable {p : ℕ} [Fact p.Prime]

theorem irreducible_padic : Irreducible ((p : ℕ) : ℤ_[p]) := (PadicInt.prime_p).irreducible

theorem padic_not_dvd {k : ℕ} {x : ℤ_[p]} {a : ℤ} (hx : x = ((a : ℤ) : ℤ_[p]))
    (h : ¬ ((p : ℤ) ^ k ∣ a)) : ¬ ((p : ℕ) : ℤ_[p]) ^ k ∣ x := by
  rw [hx, PadicInt.pow_p_dvd_int_iff]
  simpa using h

theorem padic_addVal {k : ℕ} {x : ℤ_[p]} {a : ℤ} (hx : x = ((a : ℤ) : ℤ_[p]))
    (h1 : (p : ℤ) ^ k ∣ a) (h2 : ¬ ((p : ℤ) ^ (k + 1) ∣ a)) :
    addVal ℤ_[p] x = (k : ℕ∞) := by
  refine Uniformity.Density.addVal_eq_of_dvd_not_dvd irreducible_padic ?_ (padic_not_dvd hx h2)
  rw [hx, PadicInt.pow_p_dvd_int_iff]
  simpa using h1


end Padic

end Uniformity.Density.Leaf.GateKit

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.GateKit.slope_bounds
#print axioms Uniformity.Density.Leaf.GateKit.not_needsDescent_of_sideDeg_one
#print axioms Uniformity.Density.Leaf.GateKit.order1Type_of_sideDeg_one
#print axioms Uniformity.Density.Leaf.GateKit.polygon_read
#print axioms Uniformity.Density.Leaf.GateKit.dev_four
#print axioms Uniformity.Density.Leaf.GateKit.padic_addVal
#print axioms Uniformity.Density.Leaf.GateKit.perim_degree_bound
end AxCheck
