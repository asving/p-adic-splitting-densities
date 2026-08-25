/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131ae
import Uniformity.ChapC.C131w
import Uniformity.ChapC.C130rp2
import Uniformity.ChapC.C26
import Uniformity.ChapC.C35

/-!
# Uniformity.ChapC.C131af — the af′ REVERSE plan, unit U-SIDE (stage 1)

**Chapter C, node group C.131af′/C.131ag′** — the reverse triangular-digit route of
`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` (unit U-SIDE, §3). This stage supplies the
locus SIDE-DATA pins that AF-3/AF-4 (U-HEART, extending this file at stage 2) and AF-6
(U-ASSEMBLE, `C131ag.lean`) consume: a locus member's cleared support is exactly `μ₂E₂`
(AF-1a), its left-endpoint height is pinned to `μ₂f₂u₂` (AF-1c) and its side degree to
`μ₂f₂` (AF-1d); and the two lattice-solving facts a finite cleared support needs (AF-2a/b).

## AF-1b is already landed — not redeclared here

The plan's AF-1b (`dvSideMin_eq_zero_of_isDvPure`) is byte-identical to the theorem ALREADY
landed at `Uniformity.Density.Tower.dvSideMin_eq_zero_of_isDvPure` (`C35.lean`, imported
above): `IsDvPure F g u ℓ → (hne) → dvSideMin F g u ℓ hne = 0`, proved by
`Nat.le_zero.mp (Finset.min'_le _ _ hpure.1)`. Re-declaring it under this file's namespace
would be pure duplication of committed work, so AF-1a/c/d below call the root-namespace
lemma directly (it is in scope via the `C35` import + `open
Uniformity.Density.Tower`) — a DEC2 plan-vs-corpus overlap, reported in
`runs/wave-b/verdict_USIDE.md`, not a gap.

## Status (this stage)

AF-1a/AF-1c/AF-1d/AF-2a/AF-2b: sorry-free. Footprint Lean-core only
(`propext, Classical.choice, Quot.sound`) — no cite anywhere in this stage (the declared
cite `fgmn_dv_exact_mul` only enters at AF-3, stage 2 / U-HEART, through
`composedKey_pow_mem_towerLocus`).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131af

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131ae Uniformity.Density.Tower.C131v

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## AF-1a — a locus member's cleared support is exactly `μ₂E₂` -/

/-- **AF-1a.** A member `f` of `towerLocus T μ₂` has `dvSupp F f T.u₂ T.e₂` EXACTLY
`μ₂E₂` (not merely `≥`, as `C131w.towerLocus_entry_floor` gives): the top abscissa
`μ₂e₂f₂` is on `f`'s own side (from `IsDvPure`'s right-endpoint clause) and its digit
there is `1` (the monic-at-full-degree computation, C.131v), pinning the height there to
`0` and hence the equality directly off `DvOnSide`. No `hπ` needed. -/
theorem towerLocus_dvSupp_eq (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O}
    (hf : f ∈ towerLocus T μ₂) :
    dvSupp F f T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := by
  obtain ⟨hmon, hdeg, hpure, -⟩ := hf
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have htopidx : f.natDegree / (F.e₁ * F.f₁) = μ₂ * T.e₂ * T.f₂ := by
    rw [hdeg, TowerDatum.D₂]
    rw [show μ₂ * (F.e₁ * F.f₁ * (T.e₂ * T.f₂)) = (μ₂ * T.e₂ * T.f₂) * (F.e₁ * F.f₁) by ring]
    exact Nat.mul_div_cancel _ hD
  have hdegeq : f.natDegree = (μ₂ * T.e₂ * T.f₂) * F.key.natDegree := by
    rw [hdeg, TowerDatum.D₂, F.hdeg]; ring
  have htop : dev F.key f (μ₂ * T.e₂ * T.f₂) = 1 :=
    dev_top_eq_one F.hmonic F.natDegree_key_pos (μ₂ * T.e₂ * T.f₂) f hmon hdegeq
  have hhgt0 : dvHgt F f (μ₂ * T.e₂ * T.f₂) = 0 := by
    show F.stageHeight (dev F.key f (μ₂ * T.e₂ * T.f₂)) = 0
    rw [htop]; exact stageHeight_one F
  have hmemtop : (μ₂ * T.e₂ * T.f₂) ∈ dvSideSet F f T.u₂ T.e₂ := by
    have h := hpure.2; rwa [htopidx] at h
  have hon : DvOnSide F f T.u₂ T.e₂ (μ₂ * T.e₂ * T.f₂) := dvOnSide_of_mem_dvSideSet hmemtop
  have heq := hon.1
  rw [hhgt0, smul_zero, zero_add] at heq
  rw [heq, TowerDatum.E₂]
  exact_mod_cast (by ring : T.u₂ * (μ₂ * T.e₂ * T.f₂) = μ₂ * (T.e₂ * T.f₂ * T.u₂))

/-! ## AF-1c — the locus left-endpoint height numeral -/

/-- **AF-1c.** A locus member's height at abscissa `0` (the left endpoint, `= 0` on the
side by `IsDvPure`/AF-1b) is pinned to `μ₂f₂u₂`: read off AF-1a's exact support via the
`DvOnSide` equation at `j = 0`, then cancel the `e₂`-smul (finite/`⊤` case split). -/
theorem towerLocus_dvHgt_zero_pin (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O}
    (hf : f ∈ towerLocus T μ₂) :
    dvHgt F f 0 = ((μ₂ * T.f₂ * T.u₂ : ℕ) : ℕ∞) := by
  have hsupp := towerLocus_dvSupp_eq T hf
  have hpure := hf.2.2.1
  have hmem : (0 : ℕ) ∈ dvSideSet F f T.u₂ T.e₂ := hpure.1
  have hon : DvOnSide F f T.u₂ T.e₂ 0 := dvOnSide_of_mem_dvSideSet hmem
  have heq := hon.1
  rw [hsupp] at heq
  rcases eq_or_ne (dvHgt F f 0) ⊤ with htop | hfin
  · exfalso
    rw [htop, C118a.smul_top_pos T.he₂, top_add] at heq
    exact (ENat.coe_ne_top _) heq
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hv] at heq ⊢
    have heqnat0 : ((μ₂ * T.E₂ : ℕ) : ℕ∞) = ((T.e₂ * v : ℕ) : ℕ∞) := by
      rw [heq]; push_cast [nsmul_eq_mul]; ring
    have heqnat' : μ₂ * T.E₂ = T.e₂ * v := by exact_mod_cast heqnat0
    have hval : v = μ₂ * T.f₂ * T.u₂ := by
      have hexp : μ₂ * T.E₂ = T.e₂ * (μ₂ * T.f₂ * T.u₂) := by rw [TowerDatum.E₂]; ring
      rw [hexp] at heqnat'
      exact (Nat.eq_of_mul_eq_mul_left T.he₂ heqnat').symm
    rw [hval]

/-! ## AF-1d — the locus side degree -/

/-- **AF-1d.** A locus member's side degree is `μ₂f₂`: the residual polynomial pinned by
`hp` (`dvSideMin = 0` via the landed AF-1b + AF-1c's numeral) equals `towerLabel T ^ μ₂`
(the locus's own residual clause), and C.26's `natDegree_dvResPoly` reads its degree
against `towerLabel_spec`'s `f₂`. -/
theorem towerLocus_dvSideDeg (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ}
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) :
    dvSideDeg F f T.u₂ T.e₂ hne = μ₂ * T.f₂ := by
  have hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = ((μ₂ * T.f₂ * T.u₂ : ℕ) : ℕ∞) := by
    rw [dvSideMin_eq_zero_of_isDvPure hf.2.2.1 hne]
    exact towerLocus_dvHgt_zero_pin T hf
  have hresC : dvResPoly F H₀ hpin f T.u₂ T.e₂ hne _ hp = (towerLabel T) ^ μ₂ :=
    hf.2.2.2 hne _ hp
  have hdegres := (natDegree_dvResPoly F hπ H₀ hpin T.he₂ T.hcop hne hp).1
  rw [hresC, (towerLabel_spec T hπ).1.natDegree_pow, (towerLabel_spec T hπ).2.2.1] at hdegres
  exact hdegres.symm

/-! ## AF-2a — a finite cleared support is attained -/

/-- **AF-2a.** If `dvSupp F g u ℓ` is finite (`= (W:ℕ∞)`), the infimum defining it is
attained at some abscissa `i`, and that `i` is on the side (finite height there, since an
infinite height would force the whole infimum to `⊤`). -/
theorem dvSideSet_nonempty_of_dvSupp_eq_coe {g : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {W : ℕ} (hW : dvSupp F g u ℓ = (W : ℕ∞)) :
    (dvSideSet F g u ℓ).Nonempty := by
  classical
  have hrne : (Finset.range (g.natDegree + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨i, hmem, hi⟩ := Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1)) hrne
    (fun j => ℓ • dvHgt F g j + (u * j : ℕ∞))
  have hival : dvSupp F g u ℓ = ℓ • dvHgt F g i + (u * i : ℕ∞) := hi
  have hfin : dvHgt F g i ≠ ⊤ := by
    intro htop
    rw [htop, C118a.smul_top_pos hℓ, top_add, hW] at hival
    exact (ENat.coe_ne_top _) hival
  exact ⟨i, Finset.mem_filter.mpr ⟨hmem, hival, hfin⟩⟩

/-! ## AF-2b — the on-line left endpoint of a support-`μ₂E₂` polynomial sits on the
`e₂`-lattice -/

/-- **AF-2b.** If `dvSupp F g T.u₂ T.e₂ = μ₂E₂` exactly, the side's left endpoint
`dvSideMin` is a multiple `T.e₂ * t₀` of `T.e₂` (`t₀ ≤ μ₂f₂`), and the height there is the
solved numeral `μ₂f₂u₂ − t₀u₂`. The `e₂ ∣ dvSideMin` step uses `T.hcop`
(`Nat.Coprime T.u₂ T.e₂`) via `Nat.Coprime.dvd_of_dvd_mul_left`. -/
theorem towerLattice_solve (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {g : Polynomial O}
    (hsupp : dvSupp F g T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞))
    (hne : (dvSideSet F g T.u₂ T.e₂).Nonempty) :
    ∃ t₀ ≤ μ₂ * T.f₂,
      dvSideMin F g T.u₂ T.e₂ hne = T.e₂ * t₀ ∧
      dvHgt F g (dvSideMin F g T.u₂ T.e₂ hne)
        = ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞) := by
  set s := dvSideMin F g T.u₂ T.e₂ hne with hsdef
  have hmem : s ∈ dvSideSet F g T.u₂ T.e₂ := Finset.min'_mem _ hne
  have hon : DvOnSide F g T.u₂ T.e₂ s := dvOnSide_of_mem_dvSideSet hmem
  have heq0 := hon.1
  have hfin : dvHgt F g s ≠ ⊤ := hon.2
  rw [hsupp] at heq0
  obtain ⟨H, hHeq⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hHeq] at heq0
  have heqnat0 : ((μ₂ * T.E₂ : ℕ) : ℕ∞) = ((T.e₂ * H + T.u₂ * s : ℕ) : ℕ∞) := by
    rw [heq0]; push_cast [nsmul_eq_mul]; ring
  have heqnat' : μ₂ * T.E₂ = T.e₂ * H + T.u₂ * s := by exact_mod_cast heqnat0
  have hdvdE : T.e₂ ∣ μ₂ * T.E₂ := ⟨μ₂ * T.f₂ * T.u₂, by rw [TowerDatum.E₂]; ring⟩
  have hdvdH : T.e₂ ∣ T.e₂ * H := ⟨H, rfl⟩
  have hdvd1 : T.e₂ ∣ T.u₂ * s := by
    have heqsub : T.u₂ * s = μ₂ * T.E₂ - T.e₂ * H := by omega
    rw [heqsub]; exact Nat.dvd_sub hdvdE hdvdH
  have hdvds : T.e₂ ∣ s := Nat.Coprime.dvd_of_dvd_mul_left T.hcop.symm hdvd1
  obtain ⟨t₀, ht₀⟩ := hdvds
  have hstep : T.e₂ * (μ₂ * T.f₂ * T.u₂) = T.e₂ * (H + T.u₂ * t₀) := by
    have h1 : T.e₂ * (μ₂ * T.f₂ * T.u₂) = μ₂ * T.E₂ := by rw [TowerDatum.E₂]; ring
    have h2 : T.e₂ * (H + T.u₂ * t₀) = T.e₂ * H + T.u₂ * s := by rw [ht₀]; ring
    rw [h1, h2]; exact heqnat'
  have hcore : μ₂ * T.f₂ * T.u₂ = H + T.u₂ * t₀ := Nat.eq_of_mul_eq_mul_left T.he₂ hstep
  have hu2pos : 0 < T.u₂ := by have := T.hfloor; omega
  have hYX : T.u₂ * t₀ ≤ T.u₂ * (μ₂ * T.f₂) := by
    have hcomm : μ₂ * T.f₂ * T.u₂ = T.u₂ * (μ₂ * T.f₂) := by ring
    omega
  have ht₀le : t₀ ≤ μ₂ * T.f₂ := Nat.le_of_mul_le_mul_left hYX hu2pos
  refine ⟨t₀, ht₀le, ht₀, ?_⟩
  have hcomm2 : T.u₂ * t₀ = t₀ * T.u₂ := Nat.mul_comm _ _
  have hHval : H = μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ := by omega
  rw [← hHeq, hHval]

/-! ## AF-3a — members of the same locus have equal ϖ-reads at every shared lattice point
(U-HEART, stage 2) -/

/-- **AF-3a.** Any two members of `towerLocus T μ₂` read identically, at every point
`t₀ ≤ μ₂f₂` of the shared `e₂`-lattice: both residual polynomials equal `towerLabel T ^ μ₂`
(the locus's own residual clause), so the extraction two-liner identifies their `t₀`-th
coefficients — which ARE the two ϖ-reads — with the same value. -/
theorem towerLocus_read_eq (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ : ℕ} {f f' : Polynomial O} (hf : f ∈ towerLocus T μ₂) (hf' : f' ∈ towerLocus T μ₂)
    {t₀ : ℕ} (ht₀ : t₀ ≤ μ₂ * T.f₂) :
    F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) (dev F.key f (T.e₂ * t₀))
      = F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) (dev F.key f' (T.e₂ * t₀)) := by
  have hstep : ∀ {g : Polynomial O}, g ∈ towerLocus T μ₂ →
      F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) (dev F.key g (T.e₂ * t₀))
        = (towerLabel T ^ μ₂).coeff t₀ := by
    intro g hg
    have hne : (dvSideSet F g T.u₂ T.e₂).Nonempty := ⟨0, hg.2.2.1.1⟩
    have hp : dvHgt F g (dvSideMin F g T.u₂ T.e₂ hne) = ((μ₂ * T.f₂ * T.u₂ : ℕ) : ℕ∞) := by
      rw [dvSideMin_eq_zero_of_isDvPure hg.2.2.1 hne]
      exact towerLocus_dvHgt_zero_pin T hg
    have hres : dvResPoly F H₀ hpin g T.u₂ T.e₂ hne (μ₂ * T.f₂ * T.u₂) hp = towerLabel T ^ μ₂ :=
      hg.2.2.2 hne _ hp
    have hdeg : dvSideDeg F g T.u₂ T.e₂ hne = μ₂ * T.f₂ := towerLocus_dvSideDeg T hπ hg hne
    have ht₀' : t₀ ≤ dvSideDeg F g T.u₂ T.e₂ hne := by rw [hdeg]; exact ht₀
    have hextract : (dvResPoly F H₀ hpin g T.u₂ T.e₂ hne (μ₂ * T.f₂ * T.u₂) hp).coeff t₀
        = F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
            (dev F.key g (dvSideMin F g T.u₂ T.e₂ hne + t₀ * T.e₂)) := by
      rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
        if_pos (Nat.lt_succ_of_le ht₀')]
    rw [dvSideMin_eq_zero_of_isDvPure hg.2.2.1 hne, zero_add, Nat.mul_comm t₀ T.e₂] at hextract
    rw [hres] at hextract
    exact hextract.symm
  rw [hstep hf, hstep hf']

/-! ## AF-3 — the perturbation strictly clears `μ₂E₂ + 1` (★ THE HEART, U-HEART) -/

/-- **AF-3, ★ THE HEART.** A locus member's perturbation against the reference power
`Φ₂^{μ₂}` (C.131ac′'s `composedKey_pow_mem_towerLocus`, the declared cite `fgmn_dv_exact_mul`'s
single entry point) clears `μ₂E₂ + 1` STRICTLY. Ultrametricity only gives the weak floor
`μ₂E₂`; if it were exact (not strict), the on-line abscissa AF-2a/AF-2b locate would force
the perturbation's OWN residual constant term to vanish — since both `f` and `Φ₂^{μ₂}` read
identically there (AF-3a) and ϖ-reads split additively across the perturbation's sum
decomposition (`C130rp2.twistRead_add_of_le`) — contradicting C.26's nonvanishing
(`natDegree_dvResPoly`, clause (iii)). -/
theorem dvSupp_sub_composedKey_pow (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 1 ≤ F.h) [Finite (ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O}
    (hf : f ∈ towerLocus T μ₂) :
    ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dvSupp F (f - composedKey T ^ μ₂) T.u₂ T.e₂ := by
  have hX : composedKey T ^ μ₂ ∈ towerLocus T μ₂ := composedKey_pow_mem_towerLocus T hπ hh hμ₂
  have hfsupp : dvSupp F f T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := towerLocus_dvSupp_eq T hf
  have hXsupp : dvSupp F (composedKey T ^ μ₂) T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) :=
    towerLocus_dvSupp_eq T hX
  have hmin : ((μ₂ * T.E₂ : ℕ) : ℕ∞) ≤ dvSupp F (f - composedKey T ^ μ₂) T.u₂ T.e₂ := by
    have h1 := C131w.dv2Hgt_add_min T hπ f (-(composedKey T ^ μ₂))
    rw [C131w.dv2Hgt_neg T hπ, ← sub_eq_add_neg] at h1
    have hbf : dv2Hgt (T.levelDatum hπ) f = dvSupp F f T.u₂ T.e₂ := rfl
    have hbX : dv2Hgt (T.levelDatum hπ) (composedKey T ^ μ₂)
        = dvSupp F (composedKey T ^ μ₂) T.u₂ T.e₂ := rfl
    have hbg : dv2Hgt (T.levelDatum hπ) (f - composedKey T ^ μ₂)
        = dvSupp F (f - composedKey T ^ μ₂) T.u₂ T.e₂ := rfl
    rw [hbf, hbX, hbg, hfsupp, hXsupp, min_self] at h1
    exact h1
  rcases hmin.lt_or_eq with hlt | heq
  · exact_mod_cast Order.add_one_le_of_lt hlt
  · exfalso
    have hne_g : (dvSideSet F (f - composedKey T ^ μ₂) T.u₂ T.e₂).Nonempty :=
      dvSideSet_nonempty_of_dvSupp_eq_coe T.he₂ heq.symm
    obtain ⟨t₀, ht₀, hsmin, hM⟩ := towerLattice_solve T heq.symm hne_g
    -- the deviation reads split: `dev Φ′ f s = dev Φ′ g s + dev Φ′ Φ₂^μ₂ s`
    have hdevsub : dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀)
        = dev F.key f (T.e₂ * t₀) - dev F.key (composedKey T ^ μ₂) (T.e₂ * t₀) :=
      C131v.dev_sub F.hmonic f (composedKey T ^ μ₂) (T.e₂ * t₀)
    have hfeq : dev F.key f (T.e₂ * t₀)
        = dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀)
          + dev F.key (composedKey T ^ μ₂) (T.e₂ * t₀) := by
      rw [hdevsub]; ring
    -- the perturbation's own digit sits at EXACTLY the solved height (AF-2b's `hM`)
    have hA : ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)
        ≤ F.stageHeight (dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀)) := by
      show ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)
        ≤ dvHgt F (f - composedKey T ^ μ₂) (T.e₂ * t₀)
      rw [← hsmin]; exact le_of_eq hM.symm
    -- `Φ₂^μ₂`'s digit clears the same height, from AF-1a + `Finset.inf_le`
    have hsdeg : T.e₂ * t₀ ≤ μ₂ * T.D₂ := by
      have h1 : T.e₂ * t₀ ≤ T.e₂ * (μ₂ * T.f₂) := Nat.mul_le_mul le_rfl ht₀
      have h2 : T.e₂ * (μ₂ * T.f₂) ≤ (F.e₁ * F.f₁) * (μ₂ * (T.e₂ * T.f₂)) := by
        have hD' : 1 ≤ F.e₁ * F.f₁ := by have := Nat.mul_pos F.he₁ F.hf₁; omega
        calc T.e₂ * (μ₂ * T.f₂) = 1 * (μ₂ * (T.e₂ * T.f₂)) := by ring
          _ ≤ (F.e₁ * F.f₁) * (μ₂ * (T.e₂ * T.f₂)) := Nat.mul_le_mul hD' le_rfl
      calc T.e₂ * t₀ ≤ T.e₂ * (μ₂ * T.f₂) := h1
        _ ≤ (F.e₁ * F.f₁) * (μ₂ * (T.e₂ * T.f₂)) := h2
        _ = μ₂ * T.D₂ := by rw [TowerDatum.D₂]; ring
    have hmemrange : T.e₂ * t₀ ∈ Finset.range ((composedKey T ^ μ₂).natDegree + 1) := by
      rw [Finset.mem_range, hX.2.1]; omega
    have hinf : dvSupp F (composedKey T ^ μ₂) T.u₂ T.e₂
        ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) (T.e₂ * t₀)
          + (T.u₂ * (T.e₂ * t₀) : ℕ∞) := Finset.inf_le hmemrange
    rw [hXsupp] at hinf
    have hB0 : ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)
        ≤ dvHgt F (composedKey T ^ μ₂) (T.e₂ * t₀) := by
      rcases eq_or_ne (dvHgt F (composedKey T ^ μ₂) (T.e₂ * t₀)) ⊤ with htop | hfin
      · rw [htop]; exact le_top
      · obtain ⟨Hx, hHx⟩ := ENat.ne_top_iff_exists.mp hfin
        rw [← hHx] at hinf ⊢
        rw [nsmul_eq_mul] at hinf
        have hinfnat : μ₂ * T.E₂ ≤ T.e₂ * Hx + T.u₂ * (T.e₂ * t₀) := by exact_mod_cast hinf
        have hE2 : μ₂ * T.E₂ = T.e₂ * (μ₂ * T.f₂ * T.u₂) := by rw [TowerDatum.E₂]; ring
        have hstep2 : T.e₂ * (μ₂ * T.f₂ * T.u₂) ≤ T.e₂ * (Hx + T.u₂ * t₀) := by
          rw [← hE2]
          calc μ₂ * T.E₂ ≤ T.e₂ * Hx + T.u₂ * (T.e₂ * t₀) := hinfnat
            _ = T.e₂ * (Hx + T.u₂ * t₀) := by ring
        have hcancel : μ₂ * T.f₂ * T.u₂ ≤ Hx + T.u₂ * t₀ :=
          Nat.le_of_mul_le_mul_left hstep2 T.he₂
        have ht₀u : t₀ * T.u₂ ≤ μ₂ * T.f₂ * T.u₂ := Nat.mul_le_mul ht₀ le_rfl
        have hcomm : t₀ * T.u₂ = T.u₂ * t₀ := Nat.mul_comm t₀ T.u₂
        have hknat : μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ ≤ Hx := by omega
        exact_mod_cast hknat
    have hB : ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)
        ≤ F.stageHeight (dev F.key (composedKey T ^ μ₂) (T.e₂ * t₀)) := by
      show ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)
        ≤ dvHgt F (composedKey T ^ μ₂) (T.e₂ * t₀)
      exact hB0
    have hadd0 := C130rp2.twistRead_add_of_le F hπ H₀ hpin hA hB
    rw [← hfeq] at hadd0
    have heqread := towerLocus_read_eq T hπ hf hX ht₀
    rw [heqread] at hadd0
    have hzero : F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
        (dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀)) = 0 := by
      have h3 : F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
            (dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀))
          + F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
            (dev F.key (composedKey T ^ μ₂) (T.e₂ * t₀))
          = 0 + F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
            (dev F.key (composedKey T ^ μ₂) (T.e₂ * t₀)) := by
        rw [zero_add]; exact hadd0.symm
      exact add_right_cancel h3
    have hcoeffz : (dvResPoly F H₀ hpin (f - composedKey T ^ μ₂) T.u₂ T.e₂ hne_g
        (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) hM).coeff 0 ≠ 0 :=
      (natDegree_dvResPoly F hπ H₀ hpin T.he₂ T.hcop hne_g hM).2
    have hcoeffval : (dvResPoly F H₀ hpin (f - composedKey T ^ μ₂) T.u₂ T.e₂ hne_g
        (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) hM).coeff 0
        = F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂)
            (dev F.key (f - composedKey T ^ μ₂) (T.e₂ * t₀)) := by
      rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_pos (by omega)]
      simp only [Nat.zero_mul, Nat.sub_zero, Nat.add_zero]
      rw [hsmin]
    rw [hcoeffval] at hcoeffz
    exact hcoeffz hzero

end Uniformity.Density.Tower.C131af

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

/-! ## AF-4 — the strict per-digit floor (U-HEART; = C.54(c), root namespace) -/

/-- **AF-4 (★ = C.54(c) strict node floor).** For a locus member `f ∈ towerLocus T μ₂` and
`j < μ₂`, the composed-key digit `dev Φ₂ f j` clears `(μ₂−j)E₂ + 1` STRICTLY: AF-3's `+1`
distributed per digit through C.131w′'s honest-digit ledger `dv2Hgt_dev_floor`, after
replacing `f`'s digit by the perturbation `g := f − Φ₂^{μ₂}`'s own (equal below `μ₂`, by
`dev_sub` + `dev_pow_self`'s Kronecker vanishing — C.131ae′'s own `hgdig` step, reused). -/
theorem Uniformity.Density.Tower.towerLocus_dev_strict_floor
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h) [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ}
    (hj : j < μ₂) :
    (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) := by
  set g : Polynomial O := f - composedKey T ^ μ₂ with hgdef
  have hcomposedKeyPos : 0 < (composedKey T).natDegree := by
    rw [C131v.composedKey_natDegree_mul T hπ]
    exact Nat.mul_pos (by have := T.hcomp; omega) F.natDegree_key_pos
  have hgdig : dev (composedKey T) f j = dev (composedKey T) g j := by
    have hsub := C131v.dev_sub (composedKey_monic T) f (composedKey T ^ μ₂) j
    have htop := dev_pow_self (composedKey_monic T) hcomposedKeyPos μ₂ j
    rw [if_neg (Nat.ne_of_lt hj)] at htop
    rw [hgdef, hsub, htop, sub_zero]
  rw [hgdig]
  have hfloor : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) g :=
    C131af.dvSupp_sub_composedKey_pow T hπ hh hμ₂ hf
  have hdev := C131w.dv2Hgt_dev_floor T hπ g.natDegree g le_rfl hfloor j
  have hnum : μ₂ * T.E₂ + 1 - j * T.E₂ = (μ₂ - j) * T.E₂ + 1 := by
    have hle : j * T.E₂ ≤ μ₂ * T.E₂ := Nat.mul_le_mul hj.le le_rfl
    have hsub2 : (μ₂ - j) * T.E₂ = μ₂ * T.E₂ - j * T.E₂ := Nat.sub_mul μ₂ j T.E₂
    omega
  rw [hnum] at hdev
  exact hdev

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvSupp_eq
#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvHgt_zero_pin
#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvSideDeg
#print axioms Uniformity.Density.Tower.C131af.dvSideSet_nonempty_of_dvSupp_eq_coe
#print axioms Uniformity.Density.Tower.C131af.towerLattice_solve
#print axioms Uniformity.Density.Tower.C131af.towerLocus_read_eq
#print axioms Uniformity.Density.Tower.C131af.dvSupp_sub_composedKey_pow
#print axioms Uniformity.Density.Tower.towerLocus_dev_strict_floor

end AxCheck
