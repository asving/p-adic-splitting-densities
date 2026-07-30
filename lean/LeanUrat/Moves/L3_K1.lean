/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L0_GRg
import LeanUrat.Moves.LaurentOrd
import LeanUrat.Moves.ResVal

/-!
# Moves/L3_K1 — Lemma K1 at the lifted key `Φ̂` (D.5, MOVES ~2131-2142)

For every `Φ̂`-development `f = Σ_j B_j Φ̂^j` (with `B_j ∈ Ĉ`), the stage valuation `w(f)` equals
the attained slot minimum `min_j (w(B_j) + j·w(Φ̂))`, with `w(Φ̂) = e·h·g` (the `kw` of the
statement).

## Proof structure (per the MOVES §D.5 note)

* `≥` (ultrametric): `ResVal.w_sum_ge` — a finite-sum ultrametric lower bound from `hwult`.
* `w(Φ̂) = ehg`: `ResVal.w_Phat` — all present slots of the displayed `Φ`-development of `Φ̂`
  are tied at `ehg`, so `hK1` at `Φ` pins the weight.
* `=` (no cancellation below the minimum): `ResVal.minsum_facts` — any nonempty subsum of
  minimizing slots is nonzero of weight exactly `m`, with additive residuals.  The engine is
  `ResVal.key_no_cancel` (slot residuals `R(B_j)·z^{jm̂}·ψ(z)^j` of exact ψ-order `j`; no subsum
  relation `Σ_T R(a_j) = R(−1)·R(a_i)` can hold, by `LaurentOrd.GRf_priv`) — note the argument
  needs only `R(−1)² = 1`, never the sign of `R(−1)`.

## SYN-M5 record (2026-07-30, C1 cluster)

This file's ~400 lines of file-private engine (w_one … R_pow, w_sum_ge, GRf_priv, psiNotDvd,
w_Phat, cslot, key_no_cancel, minsum_facts) were the SOURCE OF TRUTH for the shared modules
`Moves/LaurentOrd.lean` + `Moves/ResVal.lean` (verbatim hoists; concordance:
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`) and are now consumed from there.
The 2026-07-26 census note (no `sorry` in the import cone) carries over: the shared modules
import exactly the previous inline-dep set `{L2_widthBound, L0_GRg, L3_liftResidual}`.
Public statement `L3_K1` byte-identical to the pre-migration file.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.Moves

open Polynomial LaurentOrd ResVal

section Core

theorem L3_K1 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) : K1At σ.w Φhat ((σ.e : ℤ) * σ.h * g) := by
  classical
  intro f B N hf hdev
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hg1 : 1 ≤ g := by have := hψ.natDegree_pos; omega
  obtain ⟨hMon, hDeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hMon.ne_zero
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := w_Phat σ ψ g hg1 Φhat hlift hΦne
  -- slot weights
  have hwa : ∀ j, B j ≠ 0 →
      σ.w (B j * Φhat ^ j) = σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro j hBj
    rw [σ.hwmul _ _ hBj (pow_ne_zero j hΦne), w_pow σ Φhat hΦne j, hwhat]
  -- the nonzero-slot set and the attained minimum
  set SN : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSNdef
  have hSNmem : ∀ j : ℕ, j ∈ SN ↔ j < N ∧ B j ≠ 0 := by
    intro j
    rw [hSNdef, Finset.mem_filter, Finset.mem_range]
  have hSNne : SN.Nonempty := by
    have hfs : (∑ j ∈ Finset.range N, B j * Φhat ^ j) ≠ 0 := hsum ▸ hf
    obtain ⟨j, hjr, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfs
    refine ⟨j, (hSNmem j).mpr ⟨Finset.mem_range.mp hjr, fun hBj => hjne ?_⟩⟩
    rw [hBj, zero_mul]
  obtain ⟨m, hmle, j₀, hj₀SN, hj₀eq⟩ :
      ∃ m : ℤ, (∀ j ∈ SN, m ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)) ∧
        ∃ j₀, j₀ ∈ SN ∧ m = σ.w (B j₀) + (j₀ : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    obtain ⟨j₁, hj₁, heq₁⟩ := Finset.exists_mem_eq_inf' hSNne
      (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g))
    exact ⟨SN.inf' hSNne (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)),
      fun j hj => Finset.inf'_le _ hj, j₁, hj₁, heq₁⟩
  have hSN_B : ∀ j ∈ SN, B j ≠ 0 := fun j hj => ((hSNmem j).mp hj).2
  -- minimizing and non-minimizing slots
  set Smin : Finset ℕ :=
    SN.filter (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) with hSminDef
  set Srest : Finset ℕ :=
    SN.filter (fun j => ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m)) with hSrestDef
  have hSminMem : ∀ j : ℕ, j ∈ Smin ↔
      j ∈ SN ∧ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m := by
    intro j
    rw [hSminDef, Finset.mem_filter]
  have hSrestMem : ∀ j : ℕ, j ∈ Srest ↔
      j ∈ SN ∧ ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) := by
    intro j
    rw [hSrestDef, Finset.mem_filter]
  have hj₀Smin : j₀ ∈ Smin := (hSminMem j₀).mpr ⟨hj₀SN, hj₀eq.symm⟩
  have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => hSN_B j ((hSminMem j).mp hj).1
  have hSminw : ∀ j ∈ Smin, σ.w (B j * Φhat ^ j) = m := by
    intro j hj
    rw [hwa j (hSminB j hj)]
    exact ((hSminMem j).mp hj).2
  obtain ⟨hminNe, hminW, -⟩ := minsum_facts σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg m
    Smin hSminB hSminw ⟨j₀, hj₀Smin⟩
  -- the development sum over the nonzero slots, split at the minimum
  have hfSN : f = ∑ j ∈ SN, B j * Φhat ^ j := by
    rw [hsum, hSNdef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x hx hax hBx
    exact hax (by rw [hBx, zero_mul])
  have hfd : f = (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) := by
    rw [hfSN, hSminDef, hSrestDef]
    exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
  -- w f = m
  have hwf : σ.w f = m := by
    rcases eq_or_ne (∑ j ∈ Srest, B j * Φhat ^ j) 0 with hr0 | hrne
    · rw [hfd, hr0, add_zero]
      exact hminW
    · have hwrest : m + 1 ≤ σ.w (∑ j ∈ Srest, B j * Φhat ^ j) := by
        refine w_sum_ge σ Srest _ (m + 1) ?_ hrne
        intro j hj haj
        have hjSN : j ∈ SN := ((hSrestMem j).mp hj).1
        have hBj : B j ≠ 0 := hSN_B j hjSN
        have h1 := hmle j hjSN
        have h2 : ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) := ((hSrestMem j).mp hj).2
        rw [hwa j hBj]
        omega
      have hfne' : (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 :=
        hfd ▸ hf
      have hge : m ≤ σ.w f := by
        rw [hfd]
        have h1 := σ.hwult _ _ hminNe hrne hfne'
        rw [hminW] at h1
        exact le_trans (le_min le_rfl (by omega)) h1
      by_contra hne
      have hgt : m < σ.w f := lt_of_le_of_ne hge (fun h => hne h.symm)
      have hnegne : -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrne
      have hfmin_eq : (∑ j ∈ Smin, B j * Φhat ^ j) = f + -(∑ j ∈ Srest, B j * Φhat ^ j) := by
        rw [hfd]; ring
      have hminne' : f + -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := hfmin_eq ▸ hminNe
      have h1 := σ.hwult f _ hf hnegne hminne'
      rw [← hfmin_eq, hminW, w_neg σ _ hrne] at h1
      have h3 : m < min (σ.w f) (σ.w (∑ j ∈ Srest, B j * Φhat ^ j)) := lt_min hgt (by omega)
      omega
  -- assemble SlotMinAttained
  refine ⟨?_, j₀, ?_, ?_, ?_⟩
  · intro j hjN hBj
    have hjSN : j ∈ SN := (hSNmem j).mpr ⟨hjN, hBj⟩
    rw [hwf]
    exact hmle j hjSN
  · exact ((hSNmem j₀).mp hj₀SN).1
  · exact hSN_B j₀ hj₀SN
  · rw [hwf]; exact hj₀eq

end Core

end LeanUrat.Moves
