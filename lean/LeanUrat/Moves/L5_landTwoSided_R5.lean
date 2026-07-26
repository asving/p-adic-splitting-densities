/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L0_GRg

/-!
# Moves/L5_landTwoSided — the increment landing, two-sided (D.8, MOVES ~2316-2371)

`StratumData σ ψ μ a Cdig N f ↔ LandingCylinderL σ ψ g μ a Cdig B N`.

## SCOPE (audit #5, MOVES_LEAN_SEMAUDIT5_2026-07-26, verdict FLAGGED-OK)
This unit is cleared only at its CONDITIONAL/LOCAL scope: FLAGGED-OK remains conditional
on the established abstract `Stage` residual laws (`StageCore σ`, and the DefsL objects
`LandingCylinderL`/`IsCarryChainL`/`CarryTransportL`); it does NOT certify the deferred
graded-localization provenance (`grRes`/`coeffLocSR` as the genuine initial form /
coefficient localization — the future-campaign boundary). Read within that scope only.

## Proof structure

Everything reduces to the RESIDUAL SUM IDENTITY (`resSum`, from K1(Φ̂/w) + D.1(e) +
the `minsum_facts` no-cancellation engine cribbed from `L3_K1`, where it is private):
`R(f) = Σ_{minimizing j<N} R(B_j)·z^{jm̂}·ψ^j`, `m̂ = −t·h·g`.
* (→): `ord_of_pattern` turns the stratum's pattern into the two ψ-order divisibilities
  of `Ranch`; `ordSum` (each anchored slot term ψ-free by `psiNotDvd`, distinct ψ-orders)
  reads the same order off the LEAST minimizing slot, so the two agree: μ = least slot —
  (BOX)+(VERTEX). (TRANSPORT): the carries are DEFINED as tail sums
  `carry j := Σ_{i∈[j,N)} (C_i − c_i)·ψ^{i−j}` (`carryFwd`); the chain recurrence is
  algebra (`carryFwd_succ`), and `carry 0 = 0` is exactly `resSum` + the anchor.
* (←): `m₀ = w(f)` by K1; the chain TELESCOPES (`chain_telescope`, using the recorded
  terminal no-overflow) to `Σ c_j ψ^j = Σ C_j ψ^j =: toLaurent Ranch`, which equals
  `z^{−a}R(f)` by `resSum`; `ordSum` gives `ord_ψ Ranch = μ`, and `pattern_of_ord`
  (Fact A on `Ranch/ψ^μ` + Fact B uniqueness) recovers the pattern clauses.

## HONEST GAP (one `sorry`): anchor exactness is NOT encoded in the cylinder

The reverse direction needs `Ranch.coeff 0 ≠ 0` (the `HasAnchorK` exactness clause,
i.e. `a = ord_z R(f)`), and NO clause of `LandingCylinderL` forces it: the cylinder
constrains `a` only through `c_j = T(jm̂ − a)·R(B_j)` and the chain, which force
`toLaurent Ranch = z^{−a}·R(f)` — i.e. only `a ≤ ord_z R(f)` (polynomiality of the
digit total), never equality. For any honest instance with true anchor `a₀` and digit
room (`⌊(deg Ranch₀ + Δ)/g⌋ < N`), the SHIFTED data `a := a₀ − Δ` (Δ > 0), `Cdig :=`
the canonical ψ-development of `z^Δ·Ranch₀`, satisfies every cylinder clause (the
m₀-clauses are `a`-free; the chain runs on the shifted anchored total) while
`StratumData` fails exactly at `Ranch.coeff 0 ≠ 0`. D.8's prose pins `a := ord_z R(f)`
as part of the STRATUM's data; the round-5 cylinder dropped that pin. The single
`sorry` below marks precisely this clause — proposed round-6 repair: add an
anchor-exactness clause to `LandingCylinderL` (e.g. `¬ X ∣ Σ_j Cdig j · ψ^j`).
Everything else, in BOTH directions, is proved below.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial

/-! ## Cribbed private helpers (verbatim from `L3_K1.lean`, where they are `private`) -/

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

private lemma w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

private lemma w_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : σ.w (-f) = σ.w f := by
  have hm1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, w_one σ] at h
    omega
  have h := σ.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  rw [h, hm1, zero_add]

private lemma w_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.w (f ^ n) = (n : ℤ) * σ.w f := by
  induction n with
  | zero => rw [pow_zero, w_one σ, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, σ.hwmul _ _ (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

private lemma R_one (σ : Stage p F) : σ.R (1 : Polynomial ℤ_[p]) = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : σ.R (1 : Polynomial ℤ_[p]) ≠ 0 := σ.hRne 1 one_ne_zero
  have key : σ.R (1 : Polynomial ℤ_[p]) * 1 = σ.R 1 * σ.R 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne key).symm

private lemma R_negone_sq (σ : Stage p F) : σ.R (-1 : Polynomial ℤ_[p]) * σ.R (-1) = 1 := by
  have h := σ.hRmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  rw [neg_mul_neg, one_mul, R_one σ] at h
  exact h.symm

private lemma R_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.R (-f) = σ.R (-1) * σ.R f := by
  have h := σ.hRmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  exact h

private lemma R_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.R (f ^ n) = (σ.R f) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact R_one σ
  | succ k ih =>
    have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
    rw [pow_succ, σ.hRmul (f ^ k) f hfk hf, ih, ← pow_succ]

private lemma w_sum_ge (σ : Stage p F)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro hm hsum
    simp only [Finset.sum_empty] at hsum
    exact absurd rfl hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ σ.w (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ σ.w (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        have hult := σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum
        calc m ≤ min (σ.w (a i)) (σ.w (∑ j ∈ T, a j)) := le_min h1 h2
          _ ≤ σ.w (a i + ∑ j ∈ T, a j) := hult

end Helpers

private theorem GRf_priv {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
    (hψz : ψ ≠ Polynomial.X) (c : ℕ → LaurentPolynomial K) (S : Finset ℕ) (hne : S.Nonempty)
    (hc : ∀ j ∈ S, c j ≠ 0 ∧ ¬ (Polynomial.toLaurent ψ ∣ c j)) :
    (∑ j ∈ S, c j * (Polynomial.toLaurent ψ) ^ j) ≠ 0 := by
  set P := Polynomial.toLaurent ψ with hP
  set m := S.min' hne with hm
  have hmmem : m ∈ S := S.min'_mem hne
  have hmle : ∀ j ∈ S, m ≤ j := fun j hj => S.min'_le j hj
  have hψ0 : ψ ≠ 0 := hψ.ne_zero
  have hP0 : P ≠ 0 := by
    rw [hP]
    intro h
    exact hψ0 (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  have hfact : (∑ j ∈ S, c j * P ^ j) = P ^ m * (∑ j ∈ S, c j * P ^ (j - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hpow : P ^ j = P ^ m * P ^ (j - m) := by
      rw [← pow_add]; congr 1; have := hmle j hj; omega
    rw [hpow]; ring
  have hrest : P ∣ (∑ j ∈ S.erase m, c j * P ^ (j - m)) := by
    refine Finset.dvd_sum (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    obtain ⟨hjm, hjS⟩ := hj
    have hlt : m < j := lt_of_le_of_ne (hmle j hjS) (Ne.symm hjm)
    exact (dvd_pow_self P (by omega : j - m ≠ 0)).mul_left (c j)
  have hsplit : (∑ j ∈ S, c j * P ^ (j - m))
      = c m * P ^ (m - m) + (∑ j ∈ S.erase m, c j * P ^ (j - m)) :=
    (Finset.add_sum_erase S (fun j => c j * P ^ (j - m)) hmmem).symm
  have hcofdvd : ¬ P ∣ (∑ j ∈ S, c j * P ^ (j - m)) := by
    intro hdvd
    rw [hsplit] at hdvd
    have hdvd2 : P ∣ c m * P ^ (m - m) := (dvd_add_left hrest).mp hdvd
    rw [Nat.sub_self, pow_zero, mul_one] at hdvd2
    exact (hc m hmmem).2 hdvd2
  have hcof0 : (∑ j ∈ S, c j * P ^ (j - m)) ≠ 0 := fun h => hcofdvd (h ▸ dvd_zero P)
  rw [hfact]
  exact mul_ne_zero (pow_ne_zero m hP0) hcof0

section Core

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

private theorem psiNotDvd (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ σ.R B) := by
  classical
  intro hdvd
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := L2_widthBound σ g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (σ.hRne B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact σ.hRne B hB hRB
  have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent Ranch := by
    have h := hdvd.mul_left (LaurentPolynomial.T (-a))
    rwa [hRB, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h
  obtain ⟨q, hq⟩ := hdvdR
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  have hkey : Ranch * Polynomial.X ^ n = ψ * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
  have hdiv : ψ ∣ Ranch * Polynomial.X ^ n := ⟨f', hkey⟩
  have hprime : Prime ψ := hψ.prime
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · have hle := Polynomial.natDegree_le_of_dvd h1 hRanch_ne
    omega
  · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)

private noncomputable def cslot (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (j : ℕ) :
    LaurentPolynomial ↥σ.K :=
  σ.R (B j) * LaurentPolynomial.T ((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))

private lemma key_no_cancel (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree)
    (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T) (hBi : B i ≠ 0) (hBT : ∀ j ∈ T, B j ≠ 0) :
    (∑ j ∈ T, σ.R (B j * Φhat ^ j)) ≠ σ.R (-1) * σ.R (B i * Φhat ^ i) := by
  intro heq
  have hTne0 : ∀ n : ℤ, (LaurentPolynomial.T n : LaurentPolynomial ↥σ.K) ≠ 0 :=
    fun n => (LaurentPolynomial.isUnit_T n).ne_zero
  have hRhat := L3_liftResidual σ ψ g Φhat hlift
  have hRa : ∀ j, B j ≠ 0 →
      σ.R (B j * Φhat ^ j) = cslot σ g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold cslot
    rw [σ.hRmul _ _ hBj (pow_ne_zero j hΦne), R_pow σ Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  have hBdeg' : ∀ j, B j ≠ 0 → (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
    intro j hBj
    have h := Polynomial.natDegree_lt_natDegree hBj (hdeg j)
    rwa [hDeg] at h
  have hc0 : ∀ j, B j ≠ 0 → cslot σ g B j ≠ 0 := by
    intro j hBj
    unfold cslot
    exact mul_ne_zero (σ.hRne _ hBj) (hTne0 _)
  have hcnd : ∀ j, B j ≠ 0 → ¬ (Polynomial.toLaurent ψ ∣ cslot σ g B j) := by
    intro j hBj hdvd
    unfold cslot at hdvd
    have h2 := hdvd.mul_right (LaurentPolynomial.T (-((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))))
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    exact psiNotDvd σ ψ g hg hmon hψ hψz (B j) hBj (hBdeg' j hBj) h2
  have hRm1 : σ.R (-1 : Polynomial ℤ_[p]) ≠ 0 := σ.hRne _ (neg_ne_zero.mpr one_ne_zero)
  have hc' : ∀ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j) ≠ 0 ∧
      ¬ (Polynomial.toLaurent ψ ∣
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · rw [if_pos rfl]
      refine ⟨neg_ne_zero.mpr (mul_ne_zero hRm1 (hc0 j hBi)), ?_⟩
      intro hdvd
      rw [dvd_neg] at hdvd
      have h2 := hdvd.mul_left (σ.R (-1))
      rw [← mul_assoc, R_negone_sq σ, one_mul] at h2
      exact hcnd j hBi h2
    · have hne : j ≠ i := by rintro rfl; exact hiT hjT
      rw [if_neg hne]
      exact ⟨hc0 j (hBT j hjT), hcnd j (hBT j hjT)⟩
  have hsum0 : (∑ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
        * Polynomial.toLaurent ψ ^ j) = 0 := by
    rw [Finset.sum_insert hiT, if_pos rfl]
    have hrest : (∑ j ∈ T,
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
          * Polynomial.toLaurent ψ ^ j)
        = ∑ j ∈ T, σ.R (B j * Φhat ^ j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hne : j ≠ i := by rintro rfl; exact hiT hj
      rw [if_neg hne, ← hRa j (hBT j hj)]
    rw [hrest, heq, hRa i hBi]
    ring
  exact GRf_priv ψ hψ hψz
    (fun j => if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
    (insert i T) ⟨i, Finset.mem_insert_self i T⟩ hc' hsum0

private lemma minsum_facts (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree) (m : ℤ) :
    ∀ S' : Finset ℕ, (∀ j ∈ S', B j ≠ 0) → (∀ j ∈ S', σ.w (B j * Φhat ^ j) = m) →
      S'.Nonempty →
      (∑ j ∈ S', B j * Φhat ^ j) ≠ 0 ∧ σ.w (∑ j ∈ S', B j * Φhat ^ j) = m ∧
        σ.R (∑ j ∈ S', B j * Φhat ^ j) = ∑ j ∈ S', σ.R (B j * Φhat ^ j) := by
  intro S'
  induction S' using Finset.induction with
  | empty => intro _ _ h; exact absurd h (by simp)
  | insert i T hiT ih =>
    intro hB' hw' _
    have hBi : B i ≠ 0 := hB' i (Finset.mem_insert_self i T)
    have hwi : σ.w (B i * Φhat ^ i) = m := hw' i (Finset.mem_insert_self i T)
    have hai : B i * Φhat ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦne)
    have hBT : ∀ j ∈ T, B j ≠ 0 := fun j hj => hB' j (Finset.mem_insert_of_mem hj)
    have hwT : ∀ j ∈ T, σ.w (B j * Φhat ^ j) = m := fun j hj => hw' j (Finset.mem_insert_of_mem hj)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [Finset.sum_insert (Finset.notMem_empty i), Finset.sum_empty, add_zero]
      exact ⟨hai, hwi, trivial⟩
    · obtain ⟨hsTne, hwsT, hRsT⟩ := ih hBT hwT hTne
      rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
      have hsne : B i * Φhat ^ i + (∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := by
        intro h0
        have hsTeq : (∑ j ∈ T, B j * Φhat ^ j) = -(B i * Φhat ^ i) :=
          eq_neg_of_add_eq_zero_right h0
        have hR1 : σ.R (∑ j ∈ T, B j * Φhat ^ j) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hsTeq, R_neg σ _ hai]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          (hRsT.symm.trans hR1)
      have hwge : m ≤ σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
        have h1 := σ.hwult _ _ hai hsTne hsne
        rw [hwi, hwsT, min_self] at h1
        exact h1
      rcases eq_or_lt_of_le hwge with hweq | hwlt
      · refine ⟨hsne, hweq.symm, ?_⟩
        rw [σ.hRadd _ _ hai hsTne hsne (by rw [hwi, hwsT]) (by rw [hwi]; exact hweq.symm), hRsT]
      · exfalso
        have hnegne : -(∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hsTne
        have haux : -(∑ j ∈ T, B j * Φhat ^ j) + (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j)
            = B i * Φhat ^ i := by ring
        have hlt' : σ.w (-(∑ j ∈ T, B j * Φhat ^ j))
            < σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
          rw [w_neg σ _ hsTne, hwsT]
          exact hwlt
        have hRlt := σ.hRlt _ _ hnegne hsne (by rw [haux]; exact hai) hlt'
        rw [haux, R_neg σ _ hsTne, hRsT] at hRlt
        have hfinal : (∑ j ∈ T, σ.R (B j * Φhat ^ j)) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hRlt, ← mul_assoc, R_negone_sq σ, one_mul]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          hfinal

/-! ## `w(Φ̂) = e·h·g`, extracted from `L3_K1` applied to the trivial development `Φ̂ = 1·Φ̂¹` -/

private lemma w_Phat_priv (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) :
    σ.w Φhat = (σ.e : ℤ) * σ.h * g := by
  classical
  have hg1 : 1 ≤ g := by have := hψ.natDegree_pos; omega
  have hndpos : 0 < Φhat.natDegree := by
    rw [hDeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hdegpos : (0 : WithBot ℕ) < Φhat.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hndpos
  have hbot : (⊥ : WithBot ℕ) < Φhat.degree := lt_of_le_of_lt bot_le hdegpos
  have hdev : IsDevelopment Φhat Φhat (fun j => if j = 1 then 1 else 0) 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = 1
      · subst hj
        simp only [reduceIte]
        rw [Polynomial.degree_one]
        exact hdegpos
      · simp only [if_neg hj]
        rw [Polynomial.degree_zero]
        exact hbot
    · intro j hj
      simp only [if_neg (by omega : ¬ j = 1)]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      simp
  obtain ⟨_, j₀, hj₀2, hj₀nz, hj₀eq⟩ :=
    L3_K1 σ ψ g hg hψ hψz hmon Φhat hlift Φhat (fun j => if j = 1 then 1 else 0) 2 hΦne hdev
  simp only [] at hj₀nz hj₀eq
  have hj₀1 : j₀ = 1 := by
    by_contra h
    exact hj₀nz (by simp only [if_neg h])
  subst hj₀1
  simp only [reduceIte] at hj₀eq
  rw [w_one σ] at hj₀eq
  rw [hj₀eq]
  push_cast
  ring

/-! ## The minimizing-slot predicate and the residual sum identity (★★) -/

/-- Slot `j` is a `w f`-minimizing slot of the development. -/
private abbrev IsMinSlot (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (j : ℕ) : Prop :=
  B j ≠ 0 ∧ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m

open Classical in
private lemma resSum (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hdev : IsDevelopment Φhat f B N) :
    σ.R f = ∑ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)),
      cslot σ g B j * Polynomial.toLaurent ψ ^ j := by
  classical
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hg1 : 1 ≤ g := by have := hψ.natDegree_pos; omega
  obtain ⟨hMon, hDeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hMon.ne_zero
  have hRhat := L3_liftResidual σ ψ g Φhat hlift
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g :=
    w_Phat_priv σ ψ g hg hψ hψz hmon Φhat hlift hΦne hDeg
  have hwa : ∀ j, B j ≠ 0 →
      σ.w (B j * Φhat ^ j) = σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro j hBj
    rw [σ.hwmul _ _ hBj (pow_ne_zero j hΦne), w_pow σ Φhat hΦne j, hwhat]
  have hRa : ∀ j, B j ≠ 0 →
      σ.R (B j * Φhat ^ j) = cslot σ g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold cslot
    rw [σ.hRmul _ _ hBj (pow_ne_zero j hΦne), R_pow σ Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  obtain ⟨hle, j₀, hj₀N, hj₀nz, hj₀eq⟩ :=
    L3_K1 σ ψ g hg hψ hψz hmon Φhat hlift f B N hf ⟨hdeg, hzero, hsum⟩
  have hj₀Smin : j₀ ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj₀N, hj₀nz, hj₀eq.symm⟩
  have hSminB : ∀ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)), B j ≠ 0 :=
    fun j hj => (Finset.mem_filter.mp hj).2.1
  have hSminw : ∀ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)),
      σ.w (B j * Φhat ^ j) = σ.w f := by
    intro j hj
    rw [hwa j (hSminB j hj)]
    exact (Finset.mem_filter.mp hj).2.2
  obtain ⟨hminNe, hminW, hminR⟩ := minsum_facts σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg
    B hdeg (σ.w f) ((Finset.range N).filter (IsMinSlot σ g B (σ.w f))) hSminB hSminw
    ⟨j₀, hj₀Smin⟩
  have hsplit : f = (∑ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)), B j * Φhat ^ j)
      + (∑ j ∈ (Finset.range N).filter (fun j => ¬ IsMinSlot σ g B (σ.w f) j),
          B j * Φhat ^ j) := by
    rw [hsum]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range N) _ _).symm
  have hRf_eq : σ.R f = ∑ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)),
      σ.R (B j * Φhat ^ j) := by
    rcases eq_or_ne (∑ j ∈ (Finset.range N).filter (fun j => ¬ IsMinSlot σ g B (σ.w f) j),
        B j * Φhat ^ j) 0 with hr0 | hrne
    · have hfeq : f = ∑ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)),
          B j * Φhat ^ j := by
        conv_lhs => rw [hsplit]
        rw [hr0, add_zero]
      exact (congrArg σ.R hfeq).trans hminR
    · have hwrest : σ.w f + 1 ≤ σ.w (∑ j ∈ (Finset.range N).filter
          (fun j => ¬ IsMinSlot σ g B (σ.w f) j), B j * Φhat ^ j) := by
        refine w_sum_ge σ _ _ (σ.w f + 1) ?_ hrne
        intro j hj haj
        have hBj : B j ≠ 0 := by
          intro h
          exact haj (by rw [h, zero_mul])
        have hjN : j < N := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hnc := (Finset.mem_filter.mp hj).2
        have h1 : σ.w f ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := hle j hjN hBj
        have h2 : σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) ≠ σ.w f := fun h => hnc ⟨hBj, h⟩
        rw [hwa j hBj]
        omega
      have hfne : (∑ j ∈ (Finset.range N).filter (IsMinSlot σ g B (σ.w f)), B j * Φhat ^ j)
          + (∑ j ∈ (Finset.range N).filter (fun j => ¬ IsMinSlot σ g B (σ.w f) j),
              B j * Φhat ^ j) ≠ 0 := by
        rw [← hsplit]; exact hf
      have hRlt := σ.hRlt _ _ hminNe hrne hfne (by rw [hminW]; omega)
      exact ((congrArg σ.R hsplit).trans hRlt).trans hminR
  rw [hRf_eq]
  exact Finset.sum_congr rfl (fun j hj => hRa j (hSminB j hj))

end Core

/-! ## Laurent → polynomial divisibility transfer, and the ψ-order of a slot-term sum -/

private lemma poly_dvd_of_laurent_dvd {K : Type*} [Field K] (ψ : Polynomial K)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic) (Q : Polynomial K) (k : ℕ)
    (hdvd : Polynomial.toLaurent ψ ^ k ∣ Polynomial.toLaurent Q) : ψ ^ k ∣ Q := by
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  have hkey : Q * Polynomial.X ^ n = ψ ^ k * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, map_pow, hq, mul_assoc, ← hf']
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  have hnotXn : ¬ (ψ ∣ Polynomial.X ^ n) := fun h => hnotdvdX (hψ.prime.dvd_of_dvd_pow h)
  clear hq
  induction k generalizing Q with
  | zero => exact one_dvd Q
  | succ k ih =>
    have hdvd1 : ψ ∣ Q * Polynomial.X ^ n := by
      rw [hkey]
      exact (dvd_pow_self ψ (Nat.succ_ne_zero k)).mul_right f'
    have hdvdQ : ψ ∣ Q := (hψ.prime.dvd_or_dvd hdvd1).resolve_right hnotXn
    obtain ⟨Q', hQ'⟩ := hdvdQ
    have hkey' : Q' * Polynomial.X ^ n = ψ ^ k * f' := by
      have h2 : ψ * (Q' * Polynomial.X ^ n) = ψ * (ψ ^ k * f') := by
        rw [← mul_assoc, ← hQ', hkey, pow_succ]
        ring
      exact mul_left_cancel₀ hψ.ne_zero h2
    have hres := ih Q' hkey'
    rw [hQ', show ψ ^ (k + 1) = ψ * ψ ^ k from by ring]
    exact mul_dvd_mul_left ψ hres

private lemma ordSum {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
    (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic) (Ranch : Polynomial K) (S : Finset ℕ)
    (c : ℕ → LaurentPolynomial K)
    (hc : ∀ j ∈ S, c j ≠ 0 ∧ ¬ (Polynomial.toLaurent ψ ∣ c j))
    (μ : ℕ) (hμS : μ ∈ S) (hleast : ∀ j ∈ S, μ ≤ j)
    (hR : Polynomial.toLaurent Ranch = ∑ j ∈ S, c j * Polynomial.toLaurent ψ ^ j) :
    ψ ^ μ ∣ Ranch ∧ ¬ ψ ^ (μ + 1) ∣ Ranch := by
  have hψ0 : ψ ≠ 0 := hψ.ne_zero
  have hP0 : Polynomial.toLaurent ψ ≠ 0 := by
    intro h
    exact hψ0 (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  constructor
  · apply poly_dvd_of_laurent_dvd ψ hψ hψz hmon Ranch μ
    rw [hR]
    exact Finset.dvd_sum
      (fun j hj => (pow_dvd_pow (Polynomial.toLaurent ψ) (hleast j hj)).mul_left (c j))
  · intro hcon
    have h1 : Polynomial.toLaurent ψ ^ (μ + 1) ∣ ∑ j ∈ S, c j * Polynomial.toLaurent ψ ^ j := by
      have h := map_dvd (Polynomial.toLaurent : Polynomial K →+* LaurentPolynomial K) hcon
      rwa [map_pow, hR] at h
    have herase : Polynomial.toLaurent ψ ^ (μ + 1)
        ∣ ∑ j ∈ S.erase μ, c j * Polynomial.toLaurent ψ ^ j := by
      refine Finset.dvd_sum (fun j hj => ?_)
      rw [Finset.mem_erase] at hj
      have hj1 : μ + 1 ≤ j := lt_of_le_of_ne (hleast j hj.2) (Ne.symm hj.1)
      exact (pow_dvd_pow (Polynomial.toLaurent ψ) hj1).mul_left (c j)
    have hcμ : c μ * Polynomial.toLaurent ψ ^ μ
        = (∑ j ∈ S, c j * Polynomial.toLaurent ψ ^ j)
          - ∑ j ∈ S.erase μ, c j * Polynomial.toLaurent ψ ^ j := by
      rw [← Finset.add_sum_erase S (fun j => c j * Polynomial.toLaurent ψ ^ j) hμS]
      ring
    have h2 : Polynomial.toLaurent ψ ^ (μ + 1) ∣ c μ * Polynomial.toLaurent ψ ^ μ := by
      rw [hcμ]
      exact dvd_sub h1 herase
    obtain ⟨q, hq⟩ := h2
    have hq2 : Polynomial.toLaurent ψ ^ μ * c μ
        = Polynomial.toLaurent ψ ^ μ * (Polynomial.toLaurent ψ * q) := by
      rw [mul_comm (Polynomial.toLaurent ψ ^ μ) (c μ), hq, pow_succ]
      ring
    have hfin : c μ = Polynomial.toLaurent ψ * q :=
      mul_left_cancel₀ (pow_ne_zero μ hP0) hq2
    exact (hc μ hμS).2 ⟨q, hfin⟩

/-! ## ψ-order ↔ pattern, for canonical developments -/

private lemma ord_of_pattern {K : Type*} [Field K] (ψ : Polynomial K)
    (Ranch : Polynomial K) (Cdig : ℕ → Polynomial K) (N μ : ℕ) (hμN : μ < N)
    (hdev : IsDevelopment ψ Ranch Cdig N)
    (hlow : ∀ j, j < μ → Cdig j = 0) (hne : Cdig μ ≠ 0) :
    ψ ^ μ ∣ Ranch ∧ ¬ ψ ^ (μ + 1) ∣ Ranch := by
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hψ0 : ψ ≠ 0 := by
    intro h
    have hd := hdeg μ
    rw [h, Polynomial.degree_zero] at hd
    exact not_lt_bot hd
  constructor
  · rw [hsum]
    refine Finset.dvd_sum (fun j hj => ?_)
    by_cases hjμ : j < μ
    · rw [hlow j hjμ, zero_mul]
      exact dvd_zero _
    · exact (pow_dvd_pow ψ (by omega)).mul_left (Cdig j)
  · intro hcon
    have hμmem : μ ∈ Finset.range N := Finset.mem_range.mpr hμN
    have herase : ψ ^ (μ + 1) ∣ ∑ j ∈ (Finset.range N).erase μ, Cdig j * ψ ^ j := by
      refine Finset.dvd_sum (fun j hj => ?_)
      rw [Finset.mem_erase] at hj
      obtain ⟨hjne, hjmem⟩ := hj
      by_cases hjμ : j < μ
      · rw [hlow j hjμ, zero_mul]
        exact dvd_zero _
      · exact (pow_dvd_pow ψ (by omega)).mul_left (Cdig j)
    have hcμ : Cdig μ * ψ ^ μ
        = Ranch - ∑ j ∈ (Finset.range N).erase μ, Cdig j * ψ ^ j := by
      rw [hsum, ← Finset.add_sum_erase (Finset.range N) (fun j => Cdig j * ψ ^ j) hμmem]
      ring
    have h2 : ψ ^ (μ + 1) ∣ Cdig μ * ψ ^ μ := by
      rw [hcμ]
      exact dvd_sub hcon herase
    obtain ⟨q, hq⟩ := h2
    have hq2 : ψ ^ μ * Cdig μ = ψ ^ μ * (ψ * q) := by
      rw [mul_comm (ψ ^ μ) (Cdig μ), hq, pow_succ]
      ring
    have hdvdC : ψ ∣ Cdig μ := ⟨q, mul_left_cancel₀ (pow_ne_zero μ hψ0) hq2⟩
    have hled := Polynomial.degree_le_of_dvd hdvdC hne
    exact absurd (hdeg μ) (not_lt.mpr hled)

private lemma pattern_of_ord {K : Type*} [Field K] (ψ : Polynomial K) (hmon : ψ.Monic)
    (hd1 : 1 ≤ ψ.natDegree) (Ranch : Polynomial K) (Cdig : ℕ → Polynomial K) (N μ : ℕ)
    (hdev : IsDevelopment ψ Ranch Cdig N)
    (hdvd : ψ ^ μ ∣ Ranch) (hnot : ¬ ψ ^ (μ + 1) ∣ Ranch) :
    (∀ j, j < μ → Cdig j = 0) ∧ Cdig μ ≠ 0 := by
  classical
  have hψ0 : ψ ≠ 0 := hmon.ne_zero
  have hbot : (⊥ : WithBot ℕ) < ψ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hψ0 (Polynomial.degree_eq_bot.mp h))
  obtain ⟨Q, hQ⟩ := hdvd
  obtain ⟨D', N', hdev'⟩ := L0_FactA_exists ψ hmon hd1 Q
  obtain ⟨hdeg', hzero', hsum'⟩ := hdev'
  have hdev'' : IsDevelopment ψ Ranch
      (fun j => if j < μ then 0 else D' (j - μ)) (μ + N') := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j < μ
      · simp only [if_pos hj]
        rw [Polynomial.degree_zero]
        exact hbot
      · simp only [if_neg hj]
        exact hdeg' (j - μ)
    · intro j hj
      simp only [if_neg (by omega : ¬ j < μ)]
      exact hzero' (j - μ) (by omega)
    · beta_reduce
      rw [hQ, hsum', Finset.mul_sum]
      symm
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le μ)
        (Nat.le_add_right μ N')]
      have hfirst : ∑ j ∈ Finset.Ico 0 μ, (if j < μ then 0 else D' (j - μ)) * ψ ^ j = 0 := by
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hjμ : j < μ := (Finset.mem_Ico.mp hj).2
        simp only [if_pos hjμ, zero_mul]
      rw [hfirst, zero_add, Finset.sum_Ico_eq_sum_range]
      have hNN : μ + N' - μ = N' := by omega
      rw [hNN]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [if_neg (by omega : ¬ μ + i < μ)]
      have hidx : μ + i - μ = i := by omega
      rw [hidx, pow_add]
      ring
  have huniq : ∀ j, Cdig j = (fun j => if j < μ then 0 else D' (j - μ)) j :=
    L0_FactB_unique ψ hmon Ranch hdev hdev''
  constructor
  · intro j hj
    rw [huniq j]
    simp only [if_pos hj]
  · rw [huniq μ]
    simp only [if_neg (lt_irrefl μ), Nat.sub_self]
    intro hD0
    apply hnot
    have hdvdQ : ψ ∣ Q := by
      rw [hsum']
      refine Finset.dvd_sum (fun i hi => ?_)
      by_cases hi0 : i = 0
      · rw [hi0, hD0, zero_mul]
        exact dvd_zero _
      · exact (dvd_pow_self ψ hi0).mul_left (D' i)
    obtain ⟨Q', hQ'⟩ := hdvdQ
    exact ⟨Q', by rw [hQ, hQ', pow_succ]; ring⟩

/-! ## The chain telescope -/

private lemma chain_telescope {K : Type*} [Field K] (ψ : Polynomial K)
    (cL : ℕ → LaurentPolynomial K) (Cdig : ℕ → Polynomial K) (carry : ℕ → LaurentPolynomial K)
    (hchain : IsCarryChainL ψ cL Cdig carry) (M : ℕ) :
    ∑ j ∈ Finset.range M, cL j * Polynomial.toLaurent ψ ^ j
      = (∑ j ∈ Finset.range M, Polynomial.toLaurent (Cdig j) * Polynomial.toLaurent ψ ^ j)
        + carry M * Polynomial.toLaurent ψ ^ M := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, zero_add]
    exact hchain.1.symm
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    have h := (hchain.2 M).2
    linear_combination h * (Polynomial.toLaurent ψ ^ M)

/-! ## The forward-direction transported data: anchored slot terms and tail-sum carries -/

section FwdData

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The anchored Laurent slot term `T(j·m̂ − a)·R(B_j)` (D.8's `c_j`). -/
private noncomputable def cAnchD (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (a : ℤ)
    (j : ℕ) : LaurentPolynomial ↥σ.K :=
  LaurentPolynomial.T ((j : ℤ) * (- σ.t * σ.h * g) - a) * σ.R (B j)

open Classical in
/-- The forward-direction slot-term witness: anchored terms on minimizing slots `< N`, else 0. -/
private noncomputable def cLfwd (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (a m : ℤ) (j : ℕ) : LaurentPolynomial ↥σ.K :=
  if j < N ∧ IsMinSlot σ g B m j then cAnchD σ g B a j else 0

/-- The forward-direction carry witness: the tail sums `Σ_{i∈[j,N)} (C_i − c_i)·ψ^{i−j}`. -/
private noncomputable def carryFwd (σ : Stage p F) (g : ℕ) (ψ : Polynomial ↥σ.K)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (a m : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) (j : ℕ) :
    LaurentPolynomial ↥σ.K :=
  ∑ i ∈ Finset.range (N - j),
    (Polynomial.toLaurent (Cdig (j + i)) - cLfwd σ g B N a m (j + i))
      * Polynomial.toLaurent ψ ^ i

private lemma cLfwd_of_ge (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (a m : ℤ) (j : ℕ) (hj : N ≤ j) : cLfwd σ g B N a m j = 0 := by
  unfold cLfwd
  rw [if_neg]
  rintro ⟨h1, -⟩
  omega

private lemma carryFwd_of_ge (σ : Stage p F) (g : ℕ) (ψ : Polynomial ↥σ.K)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (a m : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) (j : ℕ)
    (hj : N ≤ j) : carryFwd σ g ψ B N a m Cdig j = 0 := by
  unfold carryFwd
  rw [show N - j = 0 from by omega]
  simp

private lemma carryFwd_succ (σ : Stage p F) (g : ℕ) (ψ : Polynomial ↥σ.K)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (a m : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) (j : ℕ)
    (hjN : j < N) :
    carryFwd σ g ψ B N a m Cdig j
      = (Polynomial.toLaurent (Cdig j) - cLfwd σ g B N a m j)
        + Polynomial.toLaurent ψ * carryFwd σ g ψ B N a m Cdig (j + 1) := by
  unfold carryFwd
  have hNj : N - j = N - (j + 1) + 1 := by omega
  rw [hNj, Finset.sum_range_succ']
  have hs : ∀ i ∈ Finset.range (N - (j + 1)),
      (Polynomial.toLaurent (Cdig (j + (i + 1))) - cLfwd σ g B N a m (j + (i + 1)))
          * Polynomial.toLaurent ψ ^ (i + 1)
        = Polynomial.toLaurent ψ *
          ((Polynomial.toLaurent (Cdig (j + 1 + i)) - cLfwd σ g B N a m (j + 1 + i))
            * Polynomial.toLaurent ψ ^ i) := by
    intro i _
    rw [show j + (i + 1) = j + 1 + i from by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
  simp only [Nat.add_zero, pow_zero, mul_one]
  ring

end FwdData

/-! ## The main theorem -/

open Classical in
theorem L5_landTwoSided {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (μ : ℕ) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hμN : μ < N) (hdev : IsDevelopment Φhat f B N) (a : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) : StratumData σ ψ μ a Cdig N f ↔ LandingCylinderL σ ψ g μ a Cdig B N := by
  classical
  obtain ⟨hMon, hDeg⟩ := L3_liftMonic σ ψ g hgpos Φhat hlift
  have hΦne : Φhat ≠ 0 := hMon.ne_zero
  -- shared: K1 and the residual-sum identity over the minimizing-slot set `Smin`
  obtain ⟨hle, j₀, hj₀N, hj₀nz, hj₀eq⟩ :=
    L3_K1 σ ψ g hg hψ hψz hmon Φhat hlift f B N hf hdev
  replace hle : ∀ j, j < N → B j ≠ 0 →
      σ.w f ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := hle
  replace hj₀eq : σ.w f = σ.w (B j₀) + (j₀ : ℤ) * ((σ.e : ℤ) * σ.h * g) := hj₀eq
  have hres := resSum σ ψ g hg hmon hψ hψz Φhat hlift f hf B N hdev
  set Smin := (Finset.range N).filter (IsMinSlot σ g B (σ.w f)) with hSminDef
  have hj₀Smin : j₀ ∈ Smin :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj₀N, hj₀nz, hj₀eq.symm⟩
  have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => (Finset.mem_filter.mp hj).2.1
  have hSminw : ∀ j ∈ Smin, σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = σ.w f :=
    fun j hj => (Finset.mem_filter.mp hj).2.2
  have hSminN : ∀ j ∈ Smin, j < N := fun j hj =>
    Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  -- the anchored slot-term sum
  have hanch_sum : LaurentPolynomial.T (-a) * σ.R f
      = ∑ j ∈ Smin, cAnchD σ g B a j * Polynomial.toLaurent ψ ^ j := by
    rw [hres, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    unfold cAnchD cslot
    rw [show (j : ℤ) * (- σ.t * σ.h * g) - a
        = -a + (j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)) from by ring, LaurentPolynomial.T_add]
    ring
  -- ψ-freeness of the anchored slot terms on `Smin`
  have hcA_ne : ∀ j ∈ Smin, cAnchD σ g B a j ≠ 0
      ∧ ¬ (Polynomial.toLaurent ψ ∣ cAnchD σ g B a j) := by
    intro j hj
    have hBj : B j ≠ 0 := hSminB j hj
    have hBdeg : (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
      have h := Polynomial.natDegree_lt_natDegree hBj (hdev.1 j)
      rwa [hDeg] at h
    have hnd := psiNotDvd σ ψ g hg hmon hψ hψz (B j) hBj hBdeg
    constructor
    · unfold cAnchD
      exact mul_ne_zero (LaurentPolynomial.isUnit_T _).ne_zero (σ.hRne _ hBj)
    · intro hdvd
      apply hnd
      unfold cAnchD at hdvd
      have h2 := hdvd.mul_left (LaurentPolynomial.T (-((j : ℤ) * (- σ.t * σ.h * g) - a)))
      rwa [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
        one_mul] at h2
  constructor
  · -- FORWARD: stratum ⟹ cylinder
    rintro ⟨Ranch, ⟨hR0, hRfa⟩, hdevψ, hlow, hμne⟩
    have hTinv : LaurentPolynomial.T (-a) * σ.R f = Polynomial.toLaurent Ranch := by
      rw [hRfa, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
        LaurentPolynomial.T_zero, one_mul]
    have hordP := ord_of_pattern ψ Ranch Cdig N μ hμN hdevψ hlow hμne
    have hRanchL : Polynomial.toLaurent Ranch
        = ∑ j ∈ Smin, cAnchD σ g B a j * Polynomial.toLaurent ψ ^ j := by
      rw [← hTinv, hanch_sum]
    have hSne : Smin.Nonempty := ⟨j₀, hj₀Smin⟩
    have hordS := ordSum ψ hψ hψz hmon Ranch Smin (cAnchD σ g B a) hcA_ne
      (Smin.min' hSne) (Smin.min'_mem hSne) (fun j hj => Smin.min'_le j hj) hRanchL
    have hjμ : Smin.min' hSne = μ := by
      rcases lt_trichotomy (Smin.min' hSne) μ with h | h | h
      · exact absurd ((pow_dvd_pow ψ (by omega : Smin.min' hSne + 1 ≤ μ)).trans hordP.1)
          hordS.2
      · exact h
      · exact absurd ((pow_dvd_pow ψ (by omega : μ + 1 ≤ Smin.min' hSne)).trans hordS.1)
          hordP.2
    have hμSmin : μ ∈ Smin := hjμ ▸ Smin.min'_mem hSne
    have hμleast : ∀ j ∈ Smin, μ ≤ j := fun j hj => hjμ ▸ Smin.min'_le j hj
    refine ⟨σ.w f, hSminB μ hμSmin, hSminw μ hμSmin, ?_, ?_, ?_⟩
    · intro j hjN hBj
      exact hle j hjN hBj
    · intro j hjμ' hBj
      have h1 : σ.w f ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) :=
        hle j (by omega) hBj
      rcases eq_or_lt_of_le h1 with heq | hlt
      · exfalso
        have hjS : j ∈ Smin :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hBj, heq.symm⟩
        have := hμleast j hjS
        omega
      · exact hlt
    · -- the transported chain
      refine ⟨cLfwd σ g B N a (σ.w f), ?_, ?_, ?_⟩
      · intro j hjN
        constructor
        · rintro ⟨hBj, hwj⟩
          unfold cLfwd
          rw [if_pos ⟨hjN, hBj, hwj⟩]
          rfl
        · intro hnc
          unfold cLfwd
          rw [if_neg (fun hcond => hnc hcond.2)]
      · intro j hj
        exact cLfwd_of_ge σ g B N a (σ.w f) j hj
      · -- CarryTransportL via the tail-sum carries
        have hcLsum : ∑ j ∈ Finset.range N,
            cLfwd σ g B N a (σ.w f) j * Polynomial.toLaurent ψ ^ j
            = LaurentPolynomial.T (-a) * σ.R f := by
          rw [hanch_sum, hSminDef, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have hjN : j < N := Finset.mem_range.mp hj
          by_cases hc : IsMinSlot σ g B (σ.w f) j
          · rw [if_pos hc]
            unfold cLfwd
            rw [if_pos ⟨hjN, hc⟩]
          · rw [if_neg hc]
            unfold cLfwd
            rw [if_neg (fun hcond => hc hcond.2), zero_mul]
        have hDsum : ∑ i ∈ Finset.range N,
            Polynomial.toLaurent (Cdig i) * Polynomial.toLaurent ψ ^ i
            = Polynomial.toLaurent Ranch := by
          rw [hdevψ.2.2, map_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, map_pow])
        refine ⟨carryFwd σ g ψ B N a (σ.w f) Cdig, ⟨?_, ?_⟩, ?_⟩
        · -- carry 0 = 0
          unfold carryFwd
          simp only [Nat.sub_zero, Nat.zero_add, zero_add]
          calc ∑ i ∈ Finset.range N,
              (Polynomial.toLaurent (Cdig i) - cLfwd σ g B N a (σ.w f) i)
                * Polynomial.toLaurent ψ ^ i
              = (∑ i ∈ Finset.range N,
                  Polynomial.toLaurent (Cdig i) * Polynomial.toLaurent ψ ^ i)
                - ∑ i ∈ Finset.range N,
                  cLfwd σ g B N a (σ.w f) i * Polynomial.toLaurent ψ ^ i := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl (fun i _ => by ring)
            _ = 0 := by
                rw [hcLsum, hDsum, hTinv, sub_self]
        · -- the chain recurrence, all j
          intro j
          refine ⟨hdevψ.1 j, ?_⟩
          by_cases hjN : j < N
          · rw [carryFwd_succ σ g ψ B N a (σ.w f) Cdig j hjN]
            ring
          · rw [carryFwd_of_ge σ g ψ B N a (σ.w f) Cdig j (by omega),
              carryFwd_of_ge σ g ψ B N a (σ.w f) Cdig (j + 1) (by omega),
              cLfwd_of_ge σ g B N a (σ.w f) j (by omega), hdevψ.2.1 j (by omega), map_zero]
            ring
        · -- terminal
          intro j hj
          exact carryFwd_of_ge σ g ψ B N a (σ.w f) Cdig j hj
  · -- REVERSE: cylinder ⟹ stratum
    rintro ⟨m₀, hBμ, hvtx, hmin, hbox, cL, hpin, hcL0, carry, hchain, hterm⟩
    -- m₀ = w f
    have hm₀ : m₀ = σ.w f := by
      have h1 : m₀ ≤ σ.w f := by
        have := hmin j₀ hj₀N hj₀nz
        omega
      have h2 : σ.w f ≤ m₀ := by
        have := hle μ hμN hBμ
        omega
      omega
    subst hm₀
    -- the pinned slot terms coincide with the anchored terms on `Smin` (zero off it)
    have hcLsum : ∑ j ∈ Finset.range N, cL j * Polynomial.toLaurent ψ ^ j
        = LaurentPolynomial.T (-a) * σ.R f := by
      rw [hanch_sum, hSminDef, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjN : j < N := Finset.mem_range.mp hj
      by_cases hc : IsMinSlot σ g B (σ.w f) j
      · rw [if_pos hc, (hpin j hjN).1 ⟨hc.1, hc.2⟩]
        rfl
      · rw [if_neg hc, (hpin j hjN).2 hc, zero_mul]
    -- Ranch and its Laurent identity via the telescope
    set Ranch : Polynomial ↥σ.K := ∑ j ∈ Finset.range N, Cdig j * ψ ^ j with hRanchDef
    have htel := chain_telescope ψ cL Cdig carry hchain N
    rw [hterm N le_rfl, zero_mul, add_zero] at htel
    have hRL : Polynomial.toLaurent Ranch
        = ∑ i ∈ Finset.range N, Polynomial.toLaurent (Cdig i) * Polynomial.toLaurent ψ ^ i := by
      rw [hRanchDef, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, map_pow])
    have hRanchL : Polynomial.toLaurent Ranch = LaurentPolynomial.T (-a) * σ.R f := by
      rw [hRL, ← htel, hcLsum]
    have hRfa : σ.R f = LaurentPolynomial.T a * Polynomial.toLaurent Ranch := by
      rw [hRanchL, ← mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
        LaurentPolynomial.T_zero, one_mul]
    -- development data
    have hdig_zero : ∀ j, N ≤ j → Cdig j = 0 := by
      intro j hj
      have h := (hchain.2 j).2
      rw [hcL0 j hj, hterm j hj, hterm (j + 1) (by omega), mul_zero, add_zero, add_zero] at h
      exact Polynomial.toLaurent_injective (by rw [map_zero, ← h])
    have hdevψ : IsDevelopment ψ Ranch Cdig N :=
      ⟨fun j => (hchain.2 j).1, hdig_zero, hRanchDef⟩
    -- ψ-order of Ranch = μ via the anchored slot-term sum
    have hμSmin : μ ∈ Smin := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hμN, hBμ, hvtx⟩
    have hμleast : ∀ j ∈ Smin, μ ≤ j := by
      intro j hj
      by_contra h
      have hjμ : j < μ := by omega
      have hBj : B j ≠ 0 := hSminB j hj
      have hstrict := hbox j hjμ hBj
      have heq := hSminw j hj
      omega
    have hRanchS : Polynomial.toLaurent Ranch
        = ∑ j ∈ Smin, cAnchD σ g B a j * Polynomial.toLaurent ψ ^ j := by
      rw [hRanchL, hanch_sum]
    have hord := ordSum ψ hψ hψz hmon Ranch Smin (cAnchD σ g B a) hcA_ne μ hμSmin
      hμleast hRanchS
    obtain ⟨hlow, hμne⟩ :=
      pattern_of_ord ψ hmon (by omega) Ranch Cdig N μ hdevψ hord.1 hord.2
    refine ⟨Ranch, ⟨?_, hRfa⟩, hdevψ, hlow, hμne⟩
    -- HONEST GAP: anchor exactness `Ranch.coeff 0 ≠ 0` is NOT derivable from the cylinder.
    -- `LandingCylinderL` constrains `a` only through `c_j = T(jm̂ − a)·R(B_j)` and the chain,
    -- which force `toLaurent Ranch = z^{−a}·R(f)` — i.e. `a ≤ ord_z R(f)` (polynomiality),
    -- never `a = ord_z R(f)`. A shifted anchor `a := a₀ − Δ` with digits := the canonical
    -- ψ-development of `z^Δ·Ranch₀` satisfies every cylinder clause while this clause fails.
    -- See the file docstring for the countermodel sketch and the proposed round-6 repair.
    sorry

end LeanUrat.Moves
