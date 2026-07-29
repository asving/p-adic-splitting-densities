/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C5 `nsZ_free` [hard; pre-approved split C5a/C5b] — the (ns-null) mechanism
(MOVES 7216–7229 (i)/(iii)): construct Z_M explicitly from the block/height grid;
freeness via `hzc.inclusive_top`; rim leads never interior via `hzc.rim_sep`; the
ladder count from `hzc.slot0_grid`. THE ONE SUBSTANTIVE NEW PROOF of the C-layer.
This theorem also DISCHARGES `NsLumpFamily.slot0` at every presented instance.
REV 9 (Codex-8 crit 5): `IsLumpLocus` carries BOTH conjuncts — the explicit
construction sets `solve := fun _ _ => 0`, discharging the literal-zero conjunct. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem nsZ_free {H : History p F} (J : JetSetup H n N m) (hzc : ZCPack J)
    (M : ℕ) (hM : M₀ J ≤ M) (hMcap : M ≤ Mlev J N) :
    ∃ Z : Locus p m, AdmissibleZ (J.Sigma H.nodes.length) Z ∧
      IsLumpLocus J M Z ∧ M - M₀ J ≤ pinCount Z := by
  classical
  set Z : Locus p m := { pinned := fun c => decide (c ∈ interiorFreshIdx J M)
                         solve := fun _ _ => 0 } with hZdef
  refine ⟨Z, ?_, ?_, ?_⟩
  · -- AdmissibleZ: an interior-fresh coordinate is unpinned on Σ by inclusive_top
    intro c hc
    have hcmem : c ∈ interiorFreshIdx J M := by
      rw [hZdef] at hc; simpa using hc
    simp only [interiorFreshIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hcmem
    obtain ⟨hib, hfl, -⟩ := hcmem
    have hci : c ∈ interiorIdx J := by
      simp only [interiorIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hib
    have hIT := hzc.inclusive_top c hci
    have hnp : ¬ pinnedOnState J c := fun hp => absurd (hIT.mp hp) (not_le.mpr hfl)
    by_contra hcontra
    rw [Bool.not_eq_false] at hcontra
    exact hnp hcontra
  · -- IsLumpLocus: pins = interiorFreshIdx (via decide), values ≡ 0 by construction
    refine ⟨fun c => ?_, fun c _ f => rfl⟩
    rw [hZdef]
    simp only [decide_eq_true_eq]
  · -- ladder count: slot0_grid gives one interior-fresh block per height in (M₀,M]
    have hpc : pinCount Z = (interiorFreshIdx J M).card := by
      unfold pinCount
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hZdef, decide_eq_true_eq]
    rw [hpc]
    rcases le_or_gt M (M₀ J) with hle | hlt
    · simp [Nat.sub_eq_zero_of_le hle]
    · have hne : Nonempty (Fin m) := ⟨(hzc.slot0_grid M (le_of_lt hlt) hMcap).choose⟩
      rw [← Nat.card_Ioc (M₀ J) M]
      apply Finset.card_le_card_of_injOn
        (f := fun ht => if h : M₀ J ≤ ht ∧ ht ≤ Mlev J N
          then (hzc.slot0_grid ht h.1 h.2).choose else hne.some)
      · -- MapsTo
        intro a ha
        rw [Finset.mem_coe, Finset.mem_Ioc] at ha
        have hcond : M₀ J ≤ a ∧ a ≤ Mlev J N := ⟨le_of_lt ha.1, le_trans ha.2 hMcap⟩
        have hfa : (fun ht => if h : M₀ J ≤ ht ∧ ht ≤ Mlev J N
              then (hzc.slot0_grid ht h.1 h.2).choose else hne.some) a
            = (hzc.slot0_grid a hcond.1 hcond.2).choose := dif_pos hcond
        rw [Finset.mem_coe, hfa]
        obtain ⟨hbl, hht, hbase⟩ := (hzc.slot0_grid a hcond.1 hcond.2).choose_spec
        have hib : interiorBase J (hzc.slot0_grid a hcond.1 hcond.2).choose = true :=
          (Finset.mem_filter.mp hbl).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hib, ?_, ?_⟩
        · -- freshness: height > floor, else pinned would force M₀ ≥ height > M₀
          by_contra hcon
          push_neg at hcon
          have hpin : pinnedOnState J (hzc.slot0_grid a hcond.1 hcond.2).choose :=
            (hzc.inclusive_top _ hbl).mpr hcon
          have hle2 : ⌈heightOf J (hzc.slot0_grid a hcond.1 hcond.2).choose⌉₊ ≤ M₀ J := by
            unfold M₀
            apply Finset.le_sup (f := fun j => ⌈heightOf J j⌉₊)
              (b := (hzc.slot0_grid a hcond.1 hcond.2).choose)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hpin, hbase⟩
          rw [hht, Nat.ceil_natCast] at hle2
          omega
        · rw [hht]; exact_mod_cast ha.2
      · -- InjOn
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_Ioc] at ha hb
        have hca : M₀ J ≤ a ∧ a ≤ Mlev J N := ⟨le_of_lt ha.1, le_trans ha.2 hMcap⟩
        have hcb : M₀ J ≤ b ∧ b ≤ Mlev J N := ⟨le_of_lt hb.1, le_trans hb.2 hMcap⟩
        simp only [dif_pos hca, dif_pos hcb] at hab
        have hha := (hzc.slot0_grid a hca.1 hca.2).choose_spec.2.1
        have hhb := (hzc.slot0_grid b hcb.1 hcb.2).choose_spec.2.1
        rw [hab, hhb] at hha
        exact_mod_cast hha.symm

end LeanUrat.MovesT
