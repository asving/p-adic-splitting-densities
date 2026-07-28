/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V2_readResidual
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_GRg

/-!
# HC1.V3_readLift — the recorded lift is the regrade's standard lift (blueprint §10, V3)

V′-KERNEL unit (blueprint §10.1; §10 Key Finding 1): the recorded lift
`IsReadLift σ ψ g e★ h★ Φ̂` is (†)-EQUAL-WEIGHT — its weights
`σ.w(t_k) = h★·(g−k)` give `e★·σ.w(t_k) + (e★k)·h★ = e★·h★·g` for every present
slot and for the leading slot, EXACTLY D.5's "EQUAL WEIGHTS" display (MOVES
2268–2269) transposed to wV — hence `IsReadLift` IS the standard-lift shape OF
THE REGRADED FRAME (wVPrev := σ.w, index (e★, h★)), and the D.5 residual
computation re-runs verbatim:

* the lift's read weight `wV(Φ̂) = e★·h★·g`;
* the D.5 residual display `RV(Φ̂) = T(m̂★)·(ψ as Laurent)`, `m̂★ = −t★·h★·g`
  (via the distinct-exponents sum `k − t★·h★·g`, MOVES 2270–2276);
* K1(Φ̂/wV): `wV(f) = min_m (wV(B_m) + m·e★h★g)` with attainment.

moves_ref: D.5 VERBATIM (MOVES 2253–2289 — the whole display re-runs at the
ReadFrame; the Lean pattern is L3_liftResidual + L3_K1).
deps: V2, the L3_digPrime_nonzero-analog at the same key (width < g: D.3(d)).
difficulty: medium.  E-phase: statement per §10.1, `sorry` body.

## P-phase proof structure (2026-07-28; the D.5 mirror at the ReadFrame)

The regrade is NOT a `Stage` (§10 Finding 3: `hS6b`/`hvalgrp` are unsatisfiable
at regrades for `σ.e > 1`), so `L3_liftResidual`/`L3_K1` cannot be cited — they
are MIRRORED over the partial pack `(wV, RV) = (childW σ σ.Φ e★ h★, V.D.Rv)`:

* `v3_decomp_sum` — the distinct-position monomial decomposition engine (the
  `L2_slotDecomp` `decomp_sum`, transposed; consumes `hRadd`/`hWjump`/`hRneg`).
* `v3_lift_core` — C2+C3 in ONE decomp_sum application: all lift slots are tied
  at weight `e★h★g` with residual monomials at the DISTINCT positions `D + k`,
  `D = −t★h★g` (Bézout `e★s★ + h★t★ = 1`), so `wV(Φ̂) = e★h★g` and
  `RV(Φ̂) = T(D)·ψ` in one stroke; the (S5)-preserved scalar of each slot is
  identified with `ψ_k` by matching `σ.R` monomials (hS5 ∧ IsReadLift).
* `v3_devForm` — RV of ANY `Φ`-development is the sum of its wV-minimizing slot
  residuals (V.hK1 + decomp_sum + hRlt); hence `v3_width`: on `Ĉ∖0` the RV
  support has width < g (`e★·pos = j − t★·wV`, slots `j < e★g`), hence
  `v3_psiNotDvd`: `ψ ∤ RV(B)` (the L3_digPrime_nonzero-analog at the same key).
* `v3_key_no_cancel`/`v3_minsum_facts` — the L3_K1 no-cancellation engine at
  `(Φ̂, wV, RV)` (simplified: the pack carries `hRneg`/`hWjump` outright, so no
  `R(−1)` bookkeeping); C4 assembles exactly as L3_K1's main body.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

section V3Kernel

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### Generic helpers (no stage data) -/

/-- Coefficient extraction: in a distinct-position sum of monomials, the coefficient at
`pos m` is exactly `c m` (mirror of the L2_slotDecomp helper). -/
private lemma v3_coeff_extract {ι : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset ι) (pos : ι → ℤ) (c : ι → A) (m : ι) (hm : m ∈ S)
    (hinj : ∀ j ∈ S, pos j = pos m → j = m) :
    (∑ j ∈ S, Finsupp.single (pos j) (c j)) (pos m) = c m := by
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single m
    (fun j hj hjm => by rw [Finsupp.single_apply, if_neg (fun h => hjm (hinj j hj h))])
    (fun h => absurd hm h)]
  rw [Finsupp.single_apply, if_pos rfl]

/-- **[dep `L0.GRf`, inlined verbatim]** In `K[z^{±1}]` with `ψ` irreducible, `ψ ≠ X`, a finite
sum `Σ_{j∈S} c_j·ψ^j` with each `c_j ≠ 0`, `ψ ∤ c_j` is nonzero. -/
private theorem v3_GRf {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
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

/-- **Degree domination of the top slot** (inlined verbatim from `L2_widthBound`'s
`dev_slot_bound`): in a `Φ`-development of `f` with `deg f < M·deg Φ`, every slot `j ≥ M`
is zero. -/
private lemma v3_dev_slot_bound (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic)
    (f : Polynomial ℤ_[p]) (Bd : ℕ → Polynomial ℤ_[p]) (N M : ℕ)
    (hdev : IsDevelopment Φ f Bd N) (hfdeg : f.natDegree < M * Φ.natDegree) :
    ∀ j, M ≤ j → Bd j = 0 := by
  classical
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  intro j hMj
  by_contra hBj
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  set S : Finset ℕ := (Finset.range N).filter (fun i => Bd i ≠ 0) with hSdef
  have hSmem : ∀ i, i ∈ S ↔ i < N ∧ Bd i ≠ 0 := by
    intro i; rw [hSdef, Finset.mem_filter, Finset.mem_range]
  have hjS : j ∈ S := by
    refine (hSmem j).mpr ⟨?_, hBj⟩
    by_contra hjN
    push_neg at hjN
    exact hBj (hzero j hjN)
  have hSne : S.Nonempty := ⟨j, hjS⟩
  have hJS : S.max' hSne ∈ S := S.max'_mem hSne
  set J := S.max' hSne with hJdef
  have hBJ : Bd J ≠ 0 := ((hSmem J).mp hJS).2
  have htJne : Bd J * Φ ^ J ≠ 0 := mul_ne_zero hBJ (pow_ne_zero J hΦ0)
  have hjJ : j ≤ J := S.le_max' j hjS
  have hsum2 : f = Bd J * Φ ^ J + ∑ i ∈ S.erase J, Bd i * Φ ^ i := by
    have h1 : ∑ i ∈ S, Bd i * Φ ^ i = ∑ i ∈ Finset.range N, Bd i * Φ ^ i := by
      rw [hSdef]
      exact Finset.sum_filter_of_ne (fun x _ hne hBx => hne (by rw [hBx, zero_mul]))
    rw [hsum, ← h1, ← Finset.add_sum_erase S _ hJS]
  have hdegJ : (Bd J * Φ ^ J).natDegree = (Bd J).natDegree + J * Φ.natDegree := by
    rw [Polynomial.natDegree_mul hBJ (pow_ne_zero J hΦ0), Polynomial.natDegree_pow]
  have hrest : (∑ i ∈ S.erase J, Bd i * Φ ^ i).degree < (Bd J * Φ ^ J).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff ?_).mpr ?_)
    · rw [Polynomial.degree_eq_natDegree htJne]
      exact WithBot.bot_lt_coe _
    · intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hiJ : i ≠ J := Finset.ne_of_mem_erase hi
      have hBi : Bd i ≠ 0 := ((hSmem i).mp hiS).2
      have htine : Bd i * Φ ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦ0)
      have hiltJ : i < J := lt_of_le_of_ne (S.le_max' i hiS) hiJ
      rw [Polynomial.degree_eq_natDegree htine, Polynomial.degree_eq_natDegree htJne]
      have hBideg : (Bd i).natDegree < Φ.natDegree :=
        Polynomial.natDegree_lt_natDegree hBi (hdeg i)
      have hnat : (Bd i * Φ ^ i).natDegree < (Bd J * Φ ^ J).natDegree := by
        rw [hdegJ, Polynomial.natDegree_mul hBi (pow_ne_zero i hΦ0), Polynomial.natDegree_pow]
        calc (Bd i).natDegree + i * Φ.natDegree
            < Φ.natDegree + i * Φ.natDegree := Nat.add_lt_add_right hBideg _
          _ = (i + 1) * Φ.natDegree := by ring
          _ ≤ J * Φ.natDegree := mul_le_mul_right' (by omega) _
          _ ≤ (Bd J).natDegree + J * Φ.natDegree := Nat.le_add_left _ _
      exact_mod_cast hnat
  have hdegf : f.degree = (Bd J * Φ ^ J).degree := by
    rw [hsum2]
    exact Polynomial.degree_add_eq_left_of_degree_lt hrest
  have hnatf : f.natDegree = (Bd J).natDegree + J * Φ.natDegree := by
    rw [← hdegJ]
    exact Polynomial.natDegree_eq_of_degree_eq hdegf
  have hle : M * Φ.natDegree ≤ f.natDegree := by
    rw [hnatf]
    calc M * Φ.natDegree ≤ J * Φ.natDegree := mul_le_mul_right' (le_trans hMj hjJ) _
      _ ≤ (Bd J).natDegree + J * Φ.natDegree := Nat.le_add_left _ _
  exact absurd hfdeg (not_lt.mpr hle)

/-! ### The (wV, RV) basics -/

variable {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}

/-- `wV 1 = 0`. -/
private lemma v3_wv_one (V : ReadFrame σ estar hstar sstar tstar) :
    childW σ σ.Φ estar hstar 1 = 0 := by
  have h := V.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `wV(−f) = wV f`. -/
private lemma v3_wv_neg (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) : childW σ σ.Φ estar hstar (-f) = childW σ σ.Φ estar hstar f := by
  have hm1 : childW σ σ.Φ estar hstar (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := V.hwmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, v3_wv_one V] at h
    omega
  have h := V.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  rw [h, hm1, zero_add]

/-- `wV(f^n) = n·wV f`. -/
private lemma v3_wv_pow (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) (n : ℕ) :
    childW σ σ.Φ estar hstar (f ^ n) = (n : ℤ) * childW σ σ.Φ estar hstar f := by
  induction n with
  | zero => rw [pow_zero, v3_wv_one V, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, V.hwmul _ _ (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-- `RV 1 = 1`. -/
private lemma v3_rv_one (V : ReadFrame σ estar hstar sstar tstar) :
    V.D.Rv (1 : Polynomial ℤ_[p]) = 1 := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have h := hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel₀ (hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm

/-- `RV(f^n) = RV(f)^n`. -/
private lemma v3_rv_pow (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) (n : ℕ) : V.D.Rv (f ^ n) = (V.D.Rv f) ^ n := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact v3_rv_one V
  | succ k ih =>
    rw [pow_succ, hRmul _ _ (pow_ne_zero k hf) hf, ih, ← pow_succ]

/-- Ultrametric finite-sum lower bound for `wV`. -/
private lemma v3_wv_sum_ge (V : ReadFrame σ estar hstar sstar tstar)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ childW σ σ.Φ estar hstar (a j))
    (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ childW σ σ.Φ estar hstar (∑ j ∈ S, a j) := by
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
      · have h1 : m ≤ childW σ σ.Φ estar hstar (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ childW σ σ.Φ estar hstar (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        have hult := V.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum
        calc m ≤ min (childW σ σ.Φ estar hstar (a i)) (childW σ σ.Φ estar hstar (∑ j ∈ T, a j)) :=
              le_min h1 h2
          _ ≤ childW σ σ.Φ estar hstar (a i + ∑ j ∈ T, a j) := hult

/-- **Slot monomial** (the S5-shape at the regrade): for `B ∈ C_Φ∖0`,
`RV(B·Φ^j) = single(−t★·σ.w(B) + j·s★, c)` with `c` a unit. -/
private lemma v3_slot_mono (V : ReadFrame σ estar hstar sstar tstar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hC : inC σ.Φ B) (j : ℕ) :
    ∃ c : (↥σ.K)ˣ,
      V.D.Rv (B * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w B + (j : ℤ) * sstar) ((c : ↥σ.K)) := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨c, hcR, hcV⟩ := V.D.hS5 B hB hC
  refine ⟨c, ?_⟩
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  rw [hRmul B (σ.Φ ^ j) hB (pow_ne_zero j hΦ0), v3_rv_pow V σ.Φ hΦ0 j, V.D.hRPhi, hcV,
    LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-- **Bézout position identity** at a wV-minimizing slot: `e★·pos = j − t★·γ`. -/
private lemma v3_epos (V : ReadFrame σ estar hstar sstar tstar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hC : inC σ.Φ B) (j : ℕ) (γ : ℤ)
    (hw : childW σ σ.Φ estar hstar (B * σ.Φ ^ j) = γ) :
    (estar : ℤ) * (- tstar * σ.w B + (j : ℤ) * sstar) = (j : ℤ) - tstar * γ := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hwm := V.hwmul B (σ.Φ ^ j) hB (pow_ne_zero j hΦ0)
  have hwp : childW σ σ.Φ estar hstar (σ.Φ ^ j) = (j : ℤ) * (hstar : ℤ) := by
    rw [v3_wv_pow V σ.Φ hΦ0 j, V.hwPhi]
  have hst := V.hStretch B hB hC
  have hmin : γ = (estar : ℤ) * σ.w B + (j : ℤ) * (hstar : ℤ) := by
    rw [← hw, hwm, hwp, hst]
  linear_combination tstar * hmin + (j : ℤ) * hbez

/-- **The distinct-position decomposition engine** (mirror of `L2_slotDecomp`'s
`decomp_sum` at the regrade pack): a finite sum of nonzero equal-`wV`-weight slots whose
`RV`-residuals are distinct-position monomials has `RV` additive across it, weight `γ`,
and is nonzero. -/
private lemma v3_decomp_sum (V : ReadFrame σ estar hstar sstar tstar)
    (γ : ℤ) (Tm : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → ↥σ.K) (S : Finset ℕ)
    (hT0 : ∀ j ∈ S, Tm j ≠ 0) (hTw : ∀ j ∈ S, childW σ σ.Φ estar hstar (Tm j) = γ)
    (hTR : ∀ j ∈ S, V.D.Rv (Tm j) = Finsupp.single (pos j) (c j)) (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) (hne : S.Nonempty) :
    V.D.Rv (∑ j ∈ S, Tm j) = ∑ j ∈ S, V.D.Rv (Tm j) ∧
      childW σ σ.Φ estar hstar (∑ j ∈ S, Tm j) = γ ∧ (∑ j ∈ S, Tm j) ≠ 0 := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  revert hT0 hTw hTR hc hinj hne
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _ _ _ hne; exact absurd hne (by simp)
  · intro a S' ha ih hT0 hTw hTR hc hinj _
    simp only [Finset.sum_insert ha]
    have hwta : childW σ σ.Φ estar hstar (Tm a) = γ := hTw a (Finset.mem_insert_self a S')
    have hTa0 : Tm a ≠ 0 := hT0 a (Finset.mem_insert_self a S')
    rcases S'.eq_empty_or_nonempty with hE | hE
    · subst hE; simp only [Finset.sum_empty, add_zero]; exact ⟨trivial, hwta, hTa0⟩
    obtain ⟨hRP, hwP, hP0⟩ := ih (fun j hj => hT0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTw j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hinj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hE
    have hMQ : V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j)
        = ∑ j ∈ insert a S', Finsupp.single (pos j) (c j) := by
      rw [Finset.sum_insert ha, hTR a (Finset.mem_insert_self a S'), hRP]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
    have hMval : ((V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j) : LaurentPolynomial ↥σ.K)
        : ℤ →₀ ↥σ.K) (pos a) = c a := by
      rw [hMQ]
      exact v3_coeff_extract (insert a S') pos c a (Finset.mem_insert_self a S')
        (fun j hj hpj => hinj j hj a (Finset.mem_insert_self a S') hpj)
    have hMne : V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j) ≠ 0 := by
      intro hz; rw [hz] at hMval
      exact hc a (Finset.mem_insert_self a S') hMval.symm
    have h3 : Tm a + ∑ j ∈ S', Tm j ≠ 0 := by
      intro hzero
      apply hMne
      have hxe : Tm a = -(∑ j ∈ S', Tm j) := eq_neg_of_add_eq_zero_left hzero
      rw [hxe, hRneg]; exact neg_add_cancel _
    have hge : γ ≤ childW σ σ.Φ estar hstar (Tm a + ∑ j ∈ S', Tm j) := by
      have h := V.hwult (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3
      rw [hwta, hwP, min_self] at h; exact h
    have h2 : childW σ σ.Φ estar hstar (Tm a + ∑ j ∈ S', Tm j) = γ := by
      refine le_antisymm ?_ hge
      by_contra hlt; push_neg at hlt
      exact hMne (hWjump (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3 (by rw [hwta, hwP])
        (by rw [hwta]; exact hlt))
    have h1 : V.D.Rv (Tm a + ∑ j ∈ S', Tm j) = V.D.Rv (Tm a) + ∑ j ∈ S', V.D.Rv (Tm j) := by
      rw [hRadd (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3 (hwta.trans hwP.symm)
        (h2.trans hwta.symm), hRP]
    exact ⟨h1, h2, h3⟩

/-! ### The development form of RV, width bound, and the ψ-∤ analog -/

/-- **RV of a development is its minimizing-slot residual sum** (the D.5/D.8 rerun engine at
the ReadFrame): for any `Φ`-development of `f ≠ 0`, `RV(f) = Σ_{j minimizing} RV(B_j·Φ^j)`,
with all minimizing slots nonzero of slot weight `wV f`. -/
private lemma v3_devForm (V : ReadFrame σ estar hstar sstar tstar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (f : Polynomial ℤ_[p]) (Bd : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hf : f ≠ 0) (hdev : IsDevelopment σ.Φ f Bd N) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ j ∈ S, j < N ∧ Bd j ≠ 0 ∧ inC σ.Φ (Bd j) ∧
        childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j) = childW σ σ.Φ estar hstar f) ∧
      V.D.Rv f = ∑ j ∈ S, V.D.Rv (Bd j * σ.Φ ^ j) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨hdegs, hzero, hsum⟩ := hdev
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  obtain ⟨hmle, j₀, hj₀N, hj₀nz, hj₀eq⟩ := V.hK1 f Bd N hf ⟨hdegs, hzero, hsum⟩
  have hwa : ∀ j, Bd j ≠ 0 →
      childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j)
        = childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) := by
    intro j hBj
    rw [V.hwmul _ _ hBj (pow_ne_zero j hΦ0), v3_wv_pow V σ.Φ hΦ0 j, V.hwPhi]
  set m := childW σ σ.Φ estar hstar f with hm
  set SN : Finset ℕ := (Finset.range N).filter (fun j => Bd j ≠ 0) with hSN
  have hSNmem : ∀ j, j ∈ SN ↔ j < N ∧ Bd j ≠ 0 := by
    intro j; rw [hSN, Finset.mem_filter, Finset.mem_range]
  set S : Finset ℕ := SN.filter
    (fun j => childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m) with hS
  set Srest : Finset ℕ := SN.filter
    (fun j => ¬ (childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m)) with hSrest
  have hSmem : ∀ j, j ∈ S ↔ (j < N ∧ Bd j ≠ 0) ∧
      childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m := by
    intro j; rw [hS, Finset.mem_filter, hSNmem]
  have hj₀S : j₀ ∈ S := (hSmem j₀).mpr ⟨⟨hj₀N, hj₀nz⟩, hj₀eq.symm⟩
  -- the per-slot facts on S
  have hSfacts : ∀ j ∈ S, j < N ∧ Bd j ≠ 0 ∧ inC σ.Φ (Bd j) ∧
      childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j) = m := by
    intro j hj
    obtain ⟨⟨hjN, hBj⟩, hcond⟩ := (hSmem j).mp hj
    exact ⟨hjN, hBj, hdegs j, by rw [hwa j hBj]; exact hcond⟩
  -- monomial data with a chosen scalar function
  have hmono : ∀ j, j ∈ S → ∃ cu : (↥σ.K)ˣ,
      V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) ((cu : ↥σ.K)) := by
    intro j hj
    exact v3_slot_mono V (Bd j) ((hSfacts j hj).2.1) (hdegs j) j
  have hcfun : ∀ j : ℕ, ∃ cc : ↥σ.K,
      (j ∈ S → cc ≠ 0 ∧ V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) cc) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨cu, hcu⟩ := hmono j hj
      exact ⟨(cu : ↥σ.K), fun _ => ⟨Units.ne_zero cu, hcu⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose cf hcspec using hcfun
  -- position injectivity on S (Bézout)
  have hinj : ∀ j ∈ S, ∀ k ∈ S,
      (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) = (- tstar * σ.w (Bd k) + (k : ℤ) * sstar) →
      j = k := by
    intro j hj k hk hpos
    have hej := v3_epos V hbez (Bd j) ((hSfacts j hj).2.1) (hdegs j) j m ((hSfacts j hj).2.2.2)
    have hek := v3_epos V hbez (Bd k) ((hSfacts k hk).2.1) (hdegs k) k m ((hSfacts k hk).2.2.2)
    have hjk : (j : ℤ) - tstar * m = (k : ℤ) - tstar * m := by
      rw [← hej, ← hek, hpos]
    have : (j : ℤ) = (k : ℤ) := by linarith
    exact_mod_cast this
  -- the decomposition over the minimizing slots
  obtain ⟨hRS, hWS, hne0⟩ := v3_decomp_sum V m (fun j => Bd j * σ.Φ ^ j)
    (fun j => - tstar * σ.w (Bd j) + (j : ℤ) * sstar) cf S
    (fun j hj => mul_ne_zero ((hSfacts j hj).2.1) (pow_ne_zero j hΦ0))
    (fun j hj => (hSfacts j hj).2.2.2)
    (fun j hj => (hcspec j hj).2)
    (fun j hj => (hcspec j hj).1)
    hinj ⟨j₀, hj₀S⟩
  -- split f into minimizing + rest
  have hfSN : f = ∑ j ∈ SN, Bd j * σ.Φ ^ j := by
    rw [hsum, hSN]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x hx hax hBx
    exact hax (by rw [hBx, zero_mul])
  have hfd : f = (∑ j ∈ S, Bd j * σ.Φ ^ j) + (∑ j ∈ Srest, Bd j * σ.Φ ^ j) := by
    rw [hfSN, hS, hSrest]
    exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
  refine ⟨S, ⟨j₀, hj₀S⟩, hSfacts, ?_⟩
  rcases eq_or_ne (∑ j ∈ Srest, Bd j * σ.Φ ^ j) 0 with hr0 | hrne
  · have hfeq : f = ∑ j ∈ S, Bd j * σ.Φ ^ j := by rw [hfd, hr0, add_zero]
    rw [hfeq]
    exact hRS
  · have hwrest : m + 1 ≤ childW σ σ.Φ estar hstar (∑ j ∈ Srest, Bd j * σ.Φ ^ j) := by
      refine v3_wv_sum_ge V Srest _ (m + 1) ?_ hrne
      intro j hj haj
      have hjSN : j ∈ SN := Finset.mem_of_mem_filter j hj
      obtain ⟨hjN, hBj⟩ := (hSNmem j).mp hjSN
      have hne' : ¬ (childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m) := by
        rw [hSrest, Finset.mem_filter] at hj
        exact hj.2
      have hge : m ≤ childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) :=
        hmle j hjN hBj
      rw [hwa j hBj]
      omega
    rw [hfd]
    rw [hRlt _ _ hne0 hrne (by rw [← hfd]; exact hf) (by rw [hWS]; omega)]
    exact hRS

/-- **Width bound at the regrade** (mirror of `L2_widthBound`): for `B ∈ Ĉ∖0`
(`natDegree B < e★·g·deg Φ`), the support of `RV(B)` fits in a window of width `g`. -/
private lemma v3_width (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (g : ℕ) (hg : 1 ≤ g) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBdeg : B.natDegree < estar * g * σ.Φ.natDegree) :
    ∃ a : ℤ, ∀ k ∈ (V.D.Rv B).support, a ≤ k ∧ k < a + g := by
  classical
  have hRvne : V.D.Rv B ≠ 0 := V.laws.2.1 B hB
  have hsupp_ne : (V.D.Rv B).support.Nonempty := Finsupp.support_nonempty_iff.mpr hRvne
  obtain ⟨Bd, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg B
  have hvanish : ∀ j, estar * g ≤ j → Bd j = 0 :=
    v3_dev_slot_bound σ.Φ σ.hmonic B Bd N (estar * g) hdev hBdeg
  obtain ⟨S, hSne, hSfacts, hRsum⟩ := v3_devForm V hbez B Bd N hB hdev
  have hjlt : ∀ j ∈ S, j < estar * g := by
    intro j hjS
    by_contra hge
    push_neg at hge
    exact (hSfacts j hjS).2.1 (hvanish j hge)
  -- choose the scalar function of the minimizing slots
  have hcfun : ∀ j : ℕ, ∃ cc : ↥σ.K, (j ∈ S →
      V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) cc) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨hjN, hBj, hinC, hwj⟩ := hSfacts j hj
      obtain ⟨cu, hcu⟩ := v3_slot_mono V (Bd j) hBj hinC j
      exact ⟨(cu : ↥σ.K), fun _ => hcu⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose cf hcf using hcfun
  have hsingles : V.D.Rv B
      = ∑ j ∈ S, Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j) := by
    rw [hRsum]
    exact Finset.sum_congr rfl (fun j hj => hcf j hj)
  -- pin each support point to a minimizing-slot position
  have hpin : ∀ x ∈ (V.D.Rv B).support, ∃ j ∈ S,
      x = - tstar * σ.w (Bd j) + (j : ℤ) * sstar := by
    intro x hx
    have hxne : ((V.D.Rv B : LaurentPolynomial ↥σ.K) : ℤ →₀ ↥σ.K) x ≠ 0 :=
      Finsupp.mem_support_iff.mp hx
    by_contra hnone
    push_neg at hnone
    apply hxne
    have happ : ((V.D.Rv B : LaurentPolynomial ↥σ.K) : ℤ →₀ ↥σ.K) x
        = ∑ j ∈ S, (Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j)
            : ℤ →₀ ↥σ.K) x := by
      rw [hsingles]
      exact Finsupp.finset_sum_apply S
        (fun j => (Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j)
          : ℤ →₀ ↥σ.K)) x
    rw [happ]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finsupp.single_apply, if_neg (fun h => (hnone j hj) h.symm)]
  -- pairwise width bound
  have hpair : ∀ x ∈ (V.D.Rv B).support, ∀ y ∈ (V.D.Rv B).support, x - y < (g : ℤ) := by
    intro x hx y hy
    obtain ⟨jx, hjxS, hxeq⟩ := hpin x hx
    obtain ⟨jy, hjyS, hyeq⟩ := hpin y hy
    obtain ⟨hjxN, hBjx, hinCx, hwx⟩ := hSfacts jx hjxS
    obtain ⟨hjyN, hBjy, hinCy, hwy⟩ := hSfacts jy hjyS
    have hex : (estar : ℤ) * x = (jx : ℤ) - tstar * childW σ σ.Φ estar hstar B := by
      rw [hxeq]; exact v3_epos V hbez (Bd jx) hBjx hinCx jx _ hwx
    have hey : (estar : ℤ) * y = (jy : ℤ) - tstar * childW σ σ.Φ estar hstar B := by
      rw [hyeq]; exact v3_epos V hbez (Bd jy) hBjy hinCy jy _ hwy
    have hdiff : (estar : ℤ) * (x - y) = (jx : ℤ) - (jy : ℤ) := by
      rw [mul_sub, hex, hey]; ring
    have he0 : (0 : ℤ) < (estar : ℤ) := by exact_mod_cast hee
    have hjxb : (jx : ℤ) < (estar : ℤ) * (g : ℤ) := by exact_mod_cast hjlt jx hjxS
    have hjyb : (0 : ℤ) ≤ (jy : ℤ) := by positivity
    have hlt : (estar : ℤ) * (x - y) < (estar : ℤ) * (g : ℤ) := by rw [hdiff]; omega
    by_contra hcon
    push_neg at hcon
    have hmul : (estar : ℤ) * (g : ℤ) ≤ (estar : ℤ) * (x - y) :=
      mul_le_mul_of_nonneg_left hcon (le_of_lt he0)
    omega
  refine ⟨(V.D.Rv B).support.min' hsupp_ne, ?_⟩
  intro k hk
  refine ⟨Finset.min'_le _ k hk, ?_⟩
  have hb := hpair k hk ((V.D.Rv B).support.min' hsupp_ne) (Finset.min'_mem _ hsupp_ne)
  linarith

/-- **The `L3_digPrime_nonzero`-analog at the same key** (mirror of `L2.psiNotDvd`):
`ψ ∤ RV(B)` for a nonzero below-`Φ̂`-width coefficient `B`. -/
private theorem v3_psiNotDvd (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hBdeg : B.natDegree < estar * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ V.D.Rv B) := by
  classical
  intro hdvd
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := v3_width V hee hbez g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (V.laws.2.1 B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact V.laws.2.1 B hB hRB
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

/-! ### The lift: monicity/degree, weight, and residual (C2 + C3) -/

/-- Mirror of `L3_liftMonic` at the read pair: the recorded lift is monic of degree
`e★·g·deg Φ`. -/
private lemma v3_lift_monic (hee : 1 ≤ estar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g) (Φhat : Polynomial ℤ_[p])
    (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = estar * g * σ.Φ.natDegree := by
  obtain ⟨tt, htt0, httk, hΦhat⟩ := hlift
  have hpowg_mon : (σ.Φ ^ (estar * g)).Monic := σ.hmonic.pow _
  have hpowg_ne : σ.Φ ^ (estar * g) ≠ 0 := hpowg_mon.ne_zero
  have hbpos : (⊥ : WithBot ℕ) < (σ.Φ ^ (estar * g)).degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hpowg_ne (Polynomial.degree_eq_bot.mp h))
  have hterm : ∀ k ∈ Finset.range g,
      (tt k * σ.Φ ^ (estar * k)).degree < (σ.Φ ^ (estar * g)).degree := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact hbpos
    · have hcoeff : ψ.coeff k ≠ 0 := fun h => htk (htt0 k h)
      have hlt : (tt k).degree < σ.Φ.degree := (httk k hk hcoeff).2.1
      have hpowk_ne : σ.Φ ^ (estar * k) ≠ 0 := (σ.hmonic.pow _).ne_zero
      have hprod_ne : tt k * σ.Φ ^ (estar * k) ≠ 0 := mul_ne_zero htk hpowk_ne
      have hA : (tt k).natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree htk hlt
      have hmn : estar * k + 1 ≤ estar * g := by
        have h1 : estar * (k + 1) ≤ estar * g := mul_le_mul_left' (by omega) estar
        have h2 : estar * (k + 1) = estar * k + estar := by ring
        omega
      rw [Polynomial.degree_eq_natDegree hprod_ne, Polynomial.degree_eq_natDegree hpowg_ne,
        Polynomial.natDegree_mul htk hpowk_ne, Polynomial.natDegree_pow,
        Polynomial.natDegree_pow, Nat.cast_lt]
      have h1 : (estar * k + 1) * σ.Φ.natDegree ≤ estar * g * σ.Φ.natDegree :=
        mul_le_mul_right' hmn _
      have h2 : (estar * k + 1) * σ.Φ.natDegree = estar * k * σ.Φ.natDegree + σ.Φ.natDegree := by
        ring
      have := σ.hdeg
      omega
  have hSdeg : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (estar * k)).degree
      < (σ.Φ ^ (estar * g)).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff hbpos]
    exact hterm
  refine ⟨?_, ?_⟩
  · rw [hΦhat]; exact hpowg_mon.add_of_left hSdeg
  · rw [hΦhat, Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_left_of_degree_lt hSdeg), Polynomial.natDegree_pow]

/-- **The lift core (C2 + C3 in one decomposition)**: all slots of the recorded lift are
tied at the read weight `e★h★g` with residual monomials at the distinct positions
`D + k`, `D = −t★h★g`; hence `Φ̂ ≠ 0`, `wV(Φ̂) = e★h★g`, and `RV(Φ̂) = T(D)·ψ`. -/
private lemma v3_lift_core (V : ReadFrame σ estar hstar sstar tstar)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hgdeg : ψ.natDegree = g) (hg1 : 1 ≤ g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    Φhat ≠ 0 ∧
      childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
      V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
        Polynomial.toLaurent ψ := by
  classical
  obtain ⟨hee, hhh, hcop, hbez, he1t, hsteep⟩ := hrp
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨tt, htt0, httk, hΦhat⟩ := hlift
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hcg : ψ.coeff g = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hgdeg] at h
  set W : ℤ := (estar : ℤ) * (hstar : ℤ) * (g : ℤ) with hW
  set D : ℤ := - tstar * (hstar : ℤ) * (g : ℤ) with hD
  set a : ℕ → Polynomial ℤ_[p] :=
    (fun k => if k < g then tt k * σ.Φ ^ (estar * k) else σ.Φ ^ (estar * g)) with ha
  have hag : a g = σ.Φ ^ (estar * g) := by
    rw [ha]; simp
  have hak : ∀ k, k < g → a k = tt k * σ.Φ ^ (estar * k) := by
    intro k hk; rw [ha]; simp [hk]
  have hsum : Φhat = ∑ k ∈ Finset.range (g + 1), a k := by
    rw [Finset.sum_range_succ]
    have hlt : ∀ k ∈ Finset.range g, a k = tt k * σ.Φ ^ (estar * k) := by
      intro k hk; rw [Finset.mem_range] at hk; exact hak k hk
    rw [hag, Finset.sum_congr rfl hlt, hΦhat, add_comm]
  set S : Finset ℕ := (Finset.range (g + 1)).filter (fun k => a k ≠ 0) with hS
  have hSmem : ∀ k, k ∈ S ↔ k < g + 1 ∧ a k ≠ 0 := by
    intro k; rw [hS, Finset.mem_filter, Finset.mem_range]
  have hgS : g ∈ S := by
    refine (hSmem g).mpr ⟨by omega, ?_⟩
    rw [hag]
    exact pow_ne_zero _ hΦ0
  have hpres : ∀ k, k < g → a k ≠ 0 → (tt k ≠ 0 ∧ ψ.coeff k ≠ 0) := by
    intro k hklt hakne
    have htne : tt k ≠ 0 := fun h => hakne (by rw [hak k hklt, h, zero_mul])
    exact ⟨htne, fun hc => htne (htt0 k hc)⟩
  -- the S5-preserved scalar of a present digit IS ψ_k (matching the σ.R monomials)
  have hscal : ∀ k, k < g → ψ.coeff k ≠ 0 →
      V.D.Rv (tt k) = LaurentPolynomial.C (ψ.coeff k) *
        LaurentPolynomial.T (- tstar * σ.w (tt k)) := by
    intro k hk hc
    obtain ⟨htne, htC, htw, htR⟩ := httk k hk hc
    obtain ⟨cu, hcuR, hcuV⟩ := V.D.hS5 (tt k) htne htC
    have hCeq : LaurentPolynomial.C ((cu : ↥σ.K)) = LaurentPolynomial.C (ψ.coeff k) :=
      mul_right_cancel₀ ((LaurentPolynomial.isUnit_T (- σ.t * σ.wPrev (tt k))).ne_zero)
        (by rw [← hcuR, ← htR])
    rw [hcuV, hCeq]
  -- slot residuals: monomials at the distinct positions D + k
  have hslotR : ∀ k ∈ S, V.D.Rv (a k) = Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · obtain ⟨htne, hcne⟩ := hpres k hklt hakne
      obtain ⟨-, htC, htw, -⟩ := httk k hklt hcne
      have hpos : - tstar * σ.w (tt k) + ((estar * k : ℕ) : ℤ) * sstar = D + (k : ℤ) := by
        rw [htw, hD]
        push_cast
        linear_combination (k : ℤ) * hbez
      rw [hak k hklt, hRmul (tt k) (σ.Φ ^ (estar * k)) htne (pow_ne_zero _ hΦ0),
        v3_rv_pow V σ.Φ hΦ0 (estar * k), V.D.hRPhi, hscal k hklt hcne,
        LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add, hpos,
        ← LaurentPolynomial.single_eq_C_mul_T]
    · have hkg : k = g := by omega
      subst hkg
      have hpos : ((estar * k : ℕ) : ℤ) * sstar = D + (k : ℤ) := by
        rw [hD]
        push_cast
        linear_combination (k : ℤ) * hbez
      rw [hag, v3_rv_pow V σ.Φ hΦ0 (estar * k), V.D.hRPhi, LaurentPolynomial.T_pow, hpos, hcg]
      rfl
  -- slot weights: all tied at W
  have hslotW : ∀ k ∈ S, childW σ σ.Φ estar hstar (a k) = W := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · obtain ⟨htne, hcne⟩ := hpres k hklt hakne
      obtain ⟨-, htC, htw, -⟩ := httk k hklt hcne
      rw [hak k hklt, V.hwmul _ _ htne (pow_ne_zero _ hΦ0), v3_wv_pow V σ.Φ hΦ0 (estar * k),
        V.hwPhi, V.hStretch (tt k) htne htC, htw, hW]
      push_cast
      ring
    · have hkg : k = g := by omega
      subst hkg
      rw [hag, v3_wv_pow V σ.Φ hΦ0 (estar * k), V.hwPhi, hW]
      push_cast
      ring
  -- scalar nonvanishing on S
  have hcS : ∀ k ∈ S, ψ.coeff k ≠ 0 := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · exact (hpres k hklt hakne).2
    · have hkg : k = g := by omega
      subst hkg
      rw [hcg]
      exact one_ne_zero
  -- position injectivity (positions are D + k)
  have hinj : ∀ j ∈ S, ∀ k ∈ S, (D + (j : ℤ)) = (D + (k : ℤ)) → j = k := by
    intro j _ k _ h
    have : (j : ℤ) = (k : ℤ) := by linarith
    exact_mod_cast this
  obtain ⟨hRS, hWS, hne0⟩ := v3_decomp_sum V W a (fun k => D + (k : ℤ)) (fun k => ψ.coeff k) S
    (fun k hk => ((hSmem k).mp hk).2) hslotW hslotR hcS hinj ⟨g, hgS⟩
  have hSsum : ∑ k ∈ S, a k = Φhat := by
    rw [hsum, hS]
    exact Finset.sum_filter_of_ne (fun x hx hax => hax)
  refine ⟨hSsum ▸ hne0, hSsum ▸ hWS, ?_⟩
  -- assemble RV(Φ̂) = T(D)·ψ
  have h1 : V.D.Rv Φhat = ∑ k ∈ S, Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    rw [← hSsum, hRS]
    exact Finset.sum_congr rfl hslotR
  have hext : ∑ k ∈ S, Finsupp.single (D + (k : ℤ)) (ψ.coeff k)
      = ∑ k ∈ Finset.range (g + 1), Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    refine Finset.sum_subset (by rw [hS]; exact Finset.filter_subset _ _) ?_
    intro k hkr hkS
    have hak0 : a k = 0 := by
      by_contra hakne
      exact hkS ((hSmem k).mpr ⟨Finset.mem_range.mp hkr, hakne⟩)
    have hklt : k < g := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hkr) with h | h
      · exact h
      · exfalso
        subst h
        rw [hag] at hak0
        exact pow_ne_zero _ hΦ0 hak0
    have hcoeff0 : ψ.coeff k = 0 := by
      by_contra hc
      have htne := (httk k hklt hc).1
      exact htne (by
        have := hak k hklt
        rw [this] at hak0
        rcases mul_eq_zero.mp hak0 with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ hΦ0))
    rw [hcoeff0, Finsupp.single_zero]
  have htL : Polynomial.toLaurent ψ
      = ∑ k ∈ Finset.range (g + 1),
          LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (k : ℤ) := by
    conv_lhs => rw [ψ.as_sum_range' (g + 1) (by rw [hgdeg]; omega)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow]
  rw [h1, hext, htL, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [show LaurentPolynomial.T D * (LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (k : ℤ))
        = LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (D + (k : ℤ)) from by
      rw [LaurentPolynomial.T_add]; ring,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-! ### The K1 no-cancellation engine at (Φ̂, wV, RV) (C4) -/

/-- The residual slot coefficient `c_j = RV(B_j)·z^{jD}` (`D = −t★h★g`), so that
`RV(B_j·Φ̂^j) = c_j·ψ(z)^j`. -/
private noncomputable def v3_cslot (V : ReadFrame σ estar hstar sstar tstar) (g : ℕ)
    (B : ℕ → Polynomial ℤ_[p]) (j : ℕ) : LaurentPolynomial ↥σ.K :=
  V.D.Rv (B j) * LaurentPolynomial.T ((j : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ)))

/-- **The no-cancellation engine** (mirror of L3_K1's `key_no_cancel`, simplified by the
pack's `hRneg`): no relation `Σ_{j∈T} RV(B_j Φ̂^j) = −RV(B_i Φ̂^i)` with `i ∉ T` can hold —
transported to the residual side it is a vanishing distinct-ψ-order sum, killed by
`v3_GRf` + `v3_psiNotDvd`. -/
private lemma v3_key_no_cancel (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hΦne : Φhat ≠ 0)
    (hRhat : V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
      Polynomial.toLaurent ψ)
    (hDeg : Φhat.natDegree = estar * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree)
    (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T) (hBi : B i ≠ 0) (hBT : ∀ j ∈ T, B j ≠ 0) :
    (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) ≠ - V.D.Rv (B i * Φhat ^ i) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  intro heq
  have hTne0 : ∀ n : ℤ, (LaurentPolynomial.T n : LaurentPolynomial ↥σ.K) ≠ 0 :=
    fun n => (LaurentPolynomial.isUnit_T n).ne_zero
  -- the residual slot identity RV(B_j Φ̂^j) = c_j ψ^j
  have hRa : ∀ j, B j ≠ 0 →
      V.D.Rv (B j * Φhat ^ j) = v3_cslot V g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold v3_cslot
    rw [hRmul _ _ hBj (pow_ne_zero j hΦne), v3_rv_pow V Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  have hBdeg' : ∀ j, B j ≠ 0 → (B j).natDegree < estar * g * σ.Φ.natDegree := by
    intro j hBj
    have h := Polynomial.natDegree_lt_natDegree hBj (hdeg j)
    rwa [hDeg] at h
  have hc0 : ∀ j, B j ≠ 0 → v3_cslot V g B j ≠ 0 := by
    intro j hBj
    unfold v3_cslot
    exact mul_ne_zero (hRne _ hBj) (hTne0 _)
  have hcnd : ∀ j, B j ≠ 0 → ¬ (Polynomial.toLaurent ψ ∣ v3_cslot V g B j) := by
    intro j hBj hdvd
    unfold v3_cslot at hdvd
    have h2 := hdvd.mul_right
      (LaurentPolynomial.T (-((j : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ)))))
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    exact v3_psiNotDvd V hee hbez ψ g hg hmon hψ hψz (B j) hBj (hBdeg' j hBj) h2
  -- the vanishing distinct-ψ-order sum forced by `heq`
  have hsum0 : (∑ j ∈ insert i T, v3_cslot V g B j * Polynomial.toLaurent ψ ^ j) = 0 := by
    rw [Finset.sum_insert hiT]
    have hrest : (∑ j ∈ T, v3_cslot V g B j * Polynomial.toLaurent ψ ^ j)
        = ∑ j ∈ T, V.D.Rv (B j * Φhat ^ j) :=
      Finset.sum_congr rfl (fun j hj => (hRa j (hBT j hj)).symm)
    rw [hrest, heq, hRa i hBi]
    ring
  refine v3_GRf ψ hψ hψz (v3_cslot V g B) (insert i T) ⟨i, Finset.mem_insert_self i T⟩
    ?_ hsum0
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hjT
  · exact ⟨hc0 j hBi, hcnd j hBi⟩
  · exact ⟨hc0 j (hBT j hjT), hcnd j (hBT j hjT)⟩

/-- **Minimizing-slot subsums are honest** (mirror of L3_K1's `minsum_facts`, simplified by
the pack's `hRneg`/`hWjump`): a nonempty sum of slot terms `B_j Φ̂^j`, all of `wV`-weight
exactly `m`, is nonzero of weight exactly `m`, with additive `RV`-residuals. -/
private lemma v3_minsum_facts (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hΦne : Φhat ≠ 0)
    (hRhat : V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
      Polynomial.toLaurent ψ)
    (hDeg : Φhat.natDegree = estar * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree) (m : ℤ) :
    ∀ S' : Finset ℕ, (∀ j ∈ S', B j ≠ 0) →
      (∀ j ∈ S', childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m) →
      S'.Nonempty →
      (∑ j ∈ S', B j * Φhat ^ j) ≠ 0 ∧
        childW σ σ.Φ estar hstar (∑ j ∈ S', B j * Φhat ^ j) = m ∧
        V.D.Rv (∑ j ∈ S', B j * Φhat ^ j) = ∑ j ∈ S', V.D.Rv (B j * Φhat ^ j) := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  intro S'
  induction S' using Finset.induction with
  | empty => intro _ _ h; exact absurd h (by simp)
  | insert i T hiT ih =>
    intro hB' hw' _
    have hBi : B i ≠ 0 := hB' i (Finset.mem_insert_self i T)
    have hwi : childW σ σ.Φ estar hstar (B i * Φhat ^ i) = m :=
      hw' i (Finset.mem_insert_self i T)
    have hai : B i * Φhat ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦne)
    have hBT : ∀ j ∈ T, B j ≠ 0 := fun j hj => hB' j (Finset.mem_insert_of_mem hj)
    have hwT : ∀ j ∈ T, childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m :=
      fun j hj => hw' j (Finset.mem_insert_of_mem hj)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [Finset.sum_insert (Finset.notMem_empty i), Finset.sum_empty, add_zero]
      exact ⟨hai, hwi, trivial⟩
    · obtain ⟨hsTne, hwsT, hRsT⟩ := ih hBT hwT hTne
      rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
      -- (a) the subsum cannot vanish (else Σ_T RV(a_j) = −RV(a_i), killed by no-cancel)
      have hsne : B i * Φhat ^ i + (∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := by
        intro h0
        have hsTeq : (∑ j ∈ T, B j * Φhat ^ j) = -(B i * Φhat ^ i) :=
          eq_neg_of_add_eq_zero_right h0
        have hR1 : (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) = - V.D.Rv (B i * Φhat ^ i) := by
          rw [← hRsT, hsTeq, hRneg]
        exact v3_key_no_cancel V hee hbez ψ g hg hmon hψ hψz Φhat hΦne hRhat hDeg B hdeg
          i T hiT hBi hBT hR1
      have hwge : m ≤ childW σ σ.Φ estar hstar
          (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
        have h1 := V.hwult _ _ hai hsTne hsne
        rw [hwi, hwsT, min_self] at h1
        exact h1
      rcases eq_or_lt_of_le hwge with hweq | hwlt
      · -- weight stays at m: hRadd gives residual additivity
        refine ⟨hsne, hweq.symm, ?_⟩
        rw [hRadd _ _ hai hsTne hsne (by rw [hwi, hwsT]) (by rw [hwi]; exact hweq.symm), hRsT]
      · -- (b) the weight cannot jump (hWjump forces the killed relation)
        exfalso
        have hjump := hWjump (B i * Φhat ^ i) (∑ j ∈ T, B j * Φhat ^ j) hai hsTne hsne
          (by rw [hwi, hwsT]) (by rw [hwi]; exact hwlt)
        have hfinal : (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) = - V.D.Rv (B i * Φhat ^ i) := by
          rw [← hRsT]
          exact eq_neg_of_add_eq_zero_right hjump
        exact v3_key_no_cancel V hee hbez ψ g hg hmon hψ hψz Φhat hΦne hRhat hDeg B hdeg
          i T hiT hBi hBT hfinal

end V3Kernel

/-- Unit V3: the recorded read-pair lift is the REGRADE's standard lift — equal
(†)-weights of all present slots (the D.5 EQUAL WEIGHTS display at wV), the D.5
residual display `RV(Φ̂) = T(−t★h★g)·ψ`, and K1 at (Φ̂, wV). -/
theorem V3_readLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hirr : Irreducible ψ)
    (hne : ψ ≠ Polynomial.X) (hdeg : ψ.natDegree = g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    (∀ tt : ℕ → Polynomial ℤ_[p],
        (∀ k, k < g → ψ.coeff k ≠ 0 →
          σ.w (tt k) = (hstar : ℤ) * ((g : ℤ) - (k : ℤ))) →
        ∀ k, k < g → ψ.coeff k ≠ 0 →
          (estar : ℤ) * σ.w (tt k) + ((estar : ℤ) * (k : ℤ)) * (hstar : ℤ)
            = (estar : ℤ) * (hstar : ℤ) * (g : ℤ)) ∧
    childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
    V.D.Rv Φhat
      = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
          Polynomial.toLaurent ψ ∧
    K1At (childW σ σ.Φ estar hstar) Φhat ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
  classical
  have hee : 1 ≤ estar := hrp.1
  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have hg1 : 1 ≤ g := by
    have := hirr.natDegree_pos
    omega
  obtain ⟨hΦne, hwhat, hRhat⟩ := v3_lift_core V hrp ψ g hmon hdeg hg1 Φhat hlift
  obtain ⟨hMon, hDeg⟩ := v3_lift_monic hee ψ g hg1 Φhat hlift
  refine ⟨?_, hwhat, hRhat, ?_⟩
  · -- C1: the D.5 EQUAL WEIGHTS display at wV
    intro tt htw k hk hc
    rw [htw k hk hc]
    ring
  · -- C4: Lemma K1 at (Φ̂, wV) — the L3_K1 main body, mirrored
    intro f B N hf hdev
    obtain ⟨hdegB, hzero, hsumf⟩ := hdev
    -- slot weights
    have hwa : ∀ j, B j ≠ 0 →
        childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B j) + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      intro j hBj
      rw [V.hwmul _ _ hBj (pow_ne_zero j hΦne), v3_wv_pow V Φhat hΦne j, hwhat]
    -- the nonzero-slot set and the attained minimum
    set SN : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSNdef
    have hSNmem : ∀ j : ℕ, j ∈ SN ↔ j < N ∧ B j ≠ 0 := by
      intro j
      rw [hSNdef, Finset.mem_filter, Finset.mem_range]
    have hSNne : SN.Nonempty := by
      have hfs : (∑ j ∈ Finset.range N, B j * Φhat ^ j) ≠ 0 := by rw [← hsumf]; exact hf
      obtain ⟨j, hjr, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfs
      refine ⟨j, (hSNmem j).mpr ⟨Finset.mem_range.mp hjr, fun hBj => hjne ?_⟩⟩
      rw [hBj, zero_mul]
    obtain ⟨m, hmle, j₀, hj₀SN, hj₀eq⟩ :
        ∃ m : ℤ, (∀ j ∈ SN, m ≤ childW σ σ.Φ estar hstar (B j)
            + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
          ∃ j₀, j₀ ∈ SN ∧ m = childW σ σ.Φ estar hstar (B j₀)
            + (j₀ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      obtain ⟨j₁, hj₁, heq₁⟩ := Finset.exists_mem_eq_inf' hSNne
        (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)))
      exact ⟨SN.inf' hSNne (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))),
        fun j hj => Finset.inf'_le _ hj, j₁, hj₁, heq₁⟩
    have hSN_B : ∀ j ∈ SN, B j ≠ 0 := fun j hj => ((hSNmem j).mp hj).2
    -- minimizing and non-minimizing slots
    set Smin : Finset ℕ := SN.filter
      (fun j => childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) with hSminDef
    set Srest : Finset ℕ := SN.filter
      (fun j => ¬ (childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m)) with hSrestDef
    have hSminMem : ∀ j : ℕ, j ∈ Smin ↔
        j ∈ SN ∧ childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m := by
      intro j
      rw [hSminDef, Finset.mem_filter]
    have hSrestMem : ∀ j : ℕ, j ∈ Srest ↔
        j ∈ SN ∧ ¬ (childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) := by
      intro j
      rw [hSrestDef, Finset.mem_filter]
    have hj₀Smin : j₀ ∈ Smin := (hSminMem j₀).mpr ⟨hj₀SN, hj₀eq.symm⟩
    have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => hSN_B j ((hSminMem j).mp hj).1
    have hSminw : ∀ j ∈ Smin, childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m := by
      intro j hj
      rw [hwa j (hSminB j hj)]
      exact ((hSminMem j).mp hj).2
    obtain ⟨hminNe, hminW, -⟩ := v3_minsum_facts V hee hbez ψ g hdeg hmon hirr hne Φhat hΦne
      hRhat hDeg B hdegB m Smin hSminB hSminw ⟨j₀, hj₀Smin⟩
    -- the development sum over the nonzero slots, split at the minimum
    have hfSN : f = ∑ j ∈ SN, B j * Φhat ^ j := by
      rw [hsumf, hSNdef]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro x hx hax hBx
      exact hax (by rw [hBx, zero_mul])
    have hfd : f = (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) := by
      rw [hfSN, hSminDef, hSrestDef]
      exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
    -- wV f = m
    have hwf : childW σ σ.Φ estar hstar f = m := by
      rcases eq_or_ne (∑ j ∈ Srest, B j * Φhat ^ j) 0 with hr0 | hrne
      · rw [hfd, hr0, add_zero]
        exact hminW
      · have hwrest : m + 1 ≤ childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j) := by
          refine v3_wv_sum_ge V Srest _ (m + 1) ?_ hrne
          intro j hj haj
          have hjSN : j ∈ SN := ((hSrestMem j).mp hj).1
          have hBj : B j ≠ 0 := hSN_B j hjSN
          have h1 := hmle j hjSN
          have h2 : ¬ (childW σ σ.Φ estar hstar (B j)
              + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) :=
            ((hSrestMem j).mp hj).2
          rw [hwa j hBj]
          omega
        have hfne' : (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfd]; exact hf
        have hge : m ≤ childW σ σ.Φ estar hstar f := by
          rw [hfd]
          have h1 := V.hwult _ _ hminNe hrne hfne'
          rw [hminW] at h1
          exact le_trans (le_min le_rfl (by omega)) h1
        by_contra hne'
        have hgt : m < childW σ σ.Φ estar hstar f := lt_of_le_of_ne hge (fun h => hne' h.symm)
        have hnegne : -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrne
        have hfmin_eq : (∑ j ∈ Smin, B j * Φhat ^ j)
            = f + -(∑ j ∈ Srest, B j * Φhat ^ j) := by
          rw [hfd]; ring
        have hminne' : f + -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfmin_eq]; exact hminNe
        have h1 := V.hwult f _ hf hnegne hminne'
        rw [← hfmin_eq, hminW, v3_wv_neg V _ hrne] at h1
        have h3 : m < min (childW σ σ.Φ estar hstar f)
            (childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j)) := lt_min hgt (by omega)
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

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V3_readLift
