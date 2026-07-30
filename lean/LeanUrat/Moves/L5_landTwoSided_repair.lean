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
import LeanUrat.Moves.LaurentOrd
import LeanUrat.Moves.ResVal

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

## CLOSED GAP (round-6 repair): anchor exactness supplied via the `hexact` hypothesis

The reverse direction needs `Ranch.coeff 0 ≠ 0` (the `HasAnchorK` exactness clause,
i.e. `a = ord_z R(f)`), and NO clause of `LandingCylinderL` forces it: the cylinder
constrains `a` only through `c_j = T(jm̂ − a)·R(B_j)` and the chain, which force
`toLaurent Ranch = z^{−a}·R(f)` — i.e. only `a ≤ ord_z R(f)` (polynomiality of the
digit total), never equality. For any honest instance with true anchor `a₀` and digit
room (`⌊(deg Ranch₀ + Δ)/g⌋ < N`), the SHIFTED data `a := a₀ − Δ` (Δ > 0), `Cdig :=`
the canonical ψ-development of `z^Δ·Ranch₀`, satisfies every cylinder clause (the
m₀-clauses are `a`-free; the chain runs on the shifted anchored total) while
`StratumData` fails exactly at `Ranch.coeff 0 ≠ 0`. D.8's prose pins `a := ord_z R(f)`
as part of the STRATUM's data; the round-5 cylinder dropped that pin. The round-6
repair (applied) supplies exactly this clause as the theorem hypothesis
`hexact : ¬ X ∣ Σ_j Cdig j · ψ^j`, which is `Ranch.coeff 0 ≠ 0` via
`Polynomial.X_dvd_iff` (see the reverse-direction closing step). There is NO `sorry`:
everything, in BOTH directions, is proved below.
-/

/-! ## SYN-M4 record (2026-07-30, C1 cluster)
The cribbed-from-L3_K1 private block (w_one … R_pow, w_sum_ge, GRf_priv, psiNotDvd,
cslot, key_no_cancel, minsum_facts — all statement-identical to the L3_K1 originals per
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`) and `poly_dvd_of_laurent_dvd` are deleted
in favor of `Moves/LaurentOrd.lean` + `Moves/ResVal.lean`. Two call-site equivalences:
(a) `w_Phat_priv` → `ResVal.w_Phat` drops the unused `hg hψ hψz hmon hDeg` extras
(SYN-E0 §3 VAR-H; `hg1` supplied from the in-scope derivation); (b)
`poly_dvd_of_laurent_dvd` now resolves to the LaurentOrd wrapper (binder-order variant
of `toLaurent_pow_dvd_transfer`). File-specific lemmas (IsMinSlot, resSum, ordSum,
ord_of_pattern, pattern_of_ord, chain_telescope, FwdData) stay. Public statement
`L5_landTwoSided` byte-identical. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial LaurentOrd ResVal

section Core

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

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
    w_Phat σ ψ g hg1 Φhat hlift hΦne
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
theorem L5_landTwoSided {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (μ : ℕ) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hμN : μ < N) (hdev : IsDevelopment Φhat f B N) (a : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) (hexact : ¬ Polynomial.X ∣ ∑ j ∈ Finset.range N, Cdig j * ψ ^ j) : StratumData σ ψ μ a Cdig N f ↔ LandingCylinderL σ ψ g μ a Cdig B N := by
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
          simp only [Nat.sub_zero, zero_add]
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
    -- REPAIR (round-6): anchor exactness is now supplied by the added hypothesis
    -- `hexact : ¬ X ∣ Σ_j Cdig j·ψ^j`. Since `Ranch := Σ_j Cdig j·ψ^j` (hRanchDef),
    -- `¬ X ∣ Ranch` is exactly `Ranch.coeff 0 ≠ 0` by `Polynomial.X_dvd_iff`.
    intro h0
    exact hexact (by simpa only [hRanchDef] using Polynomial.X_dvd_iff.mpr h0)

end LeanUrat.Moves
