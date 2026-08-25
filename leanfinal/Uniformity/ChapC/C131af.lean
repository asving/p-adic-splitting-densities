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

end Uniformity.Density.Tower.C131af

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvSupp_eq
#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvHgt_zero_pin
#print axioms Uniformity.Density.Tower.C131af.towerLocus_dvSideDeg
#print axioms Uniformity.Density.Tower.C131af.dvSideSet_nonempty_of_dvSupp_eq_coe
#print axioms Uniformity.Density.Tower.C131af.towerLattice_solve

end AxCheck
