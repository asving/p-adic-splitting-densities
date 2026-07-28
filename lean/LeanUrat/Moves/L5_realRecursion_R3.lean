/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L5_realRecursion — REAL recursion `𝒲_Ĉ = ⋃_{0≤j<eg}(𝒲 + j·h)` (D.9(a))

`moves_ref`: D.9(a) Lemma REAL recursion, MOVES ~2385-2387.

`Φhat` is the GENUINE standard lift (monic, degree `eg·deg Φ`, via the inline `lift_monic_deg`,
the not-yet-on-disk `L3.liftMonic`), so a coefficient `B ∈ C_Φhat` has a `Φ`-development with
strictly fewer than `eg` nonzero slots, and `hK1` gives `w B = min_j (w B_j + j·h)`.  A weight `W`
is achievable iff some slot `j < eg` and parent weight `ν ∈ weightSet` give `W − j·h = e·ν`
(single-slot realizers `hS6a`, exactness `hWS`).  The `L2.strideRule` dependency is not needed on
the residual side here (the weight recursion is purely valuation-theoretic).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- Fact A (inlined copy of the not-yet-built `L0.FactA_exists`): the `Φ`-adic development exists. -/
private theorem factA_exists {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) (f : Polynomial R) :
    ∃ (B : ℕ → Polynomial R) (N : ℕ), IsDevelopment Φ f B N := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have hz : Φ = 0 := Subsingleton.elim _ _
      rw [hz] at hd; simp at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  suffices H : ∀ n (g : Polynomial R), g.natDegree < n → ∃ B N, IsDevelopment Φ g B N by
    exact H (f.natDegree + 1) f (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro g hg; exact absurd hg (Nat.not_lt_zero _)
  | succ n IH =>
    intro g hg
    have hdiv : g %ₘ Φ + Φ * (g /ₘ Φ) = g := Polynomial.modByMonic_add_div g Φ
    have hqdev : ∃ B N, IsDevelopment Φ (g /ₘ Φ) B N := by
      rcases eq_or_ne (g /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (g.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ g.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (g /ₘ Φ).natDegree = g.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic g hΦ
        omega
    obtain ⟨B', N', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => g %ₘ Φ | k + 1 => B' k), N' + 1, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (g %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt g hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range N', B' k * Φ ^ (k + 1)) + (g %ₘ Φ) * Φ ^ 0 = g
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range N', B' k * Φ ^ (k + 1)) = (g /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      rw [e1]
      linear_combination hdiv

/-- `w 1 = 0` (nonzero idempotent under the valuation's additivity). -/
private lemma w_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w (Φ^j) = j·(w Φ)`. -/
private lemma w_pow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (j : ℕ) : σ.w (σ.Φ ^ j) = (j : ℤ) * σ.w σ.Φ := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact w_one σ
  | succ n ih =>
    rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n hΦ) hΦ, ih]
    push_cast; ring

/-- Upper bound on the degree of a partial `Φ`-adic development: if every coefficient is a proper
`Φ`-residue then `(∑_{k<n} B_k Φ^k).degree < n·deg Φ`. -/
private lemma partdeg {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (B : ℕ → Polynomial ℤ_[p]) (hB : ∀ k, (B k).degree < σ.Φ.degree) (n : ℕ) :
    (∑ k ∈ Finset.range n, B k * σ.Φ ^ k).degree < (↑(n * σ.Φ.natDegree) : WithBot ℕ) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_lt_of_le ih ?_
      exact_mod_cast (by nlinarith : n * σ.Φ.natDegree ≤ (n + 1) * σ.Φ.natDegree)
    · rcases eq_or_ne (B n) 0 with h0 | h0
      · simp only [h0, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
      · have hne : B n * σ.Φ ^ n ≠ 0 := mul_ne_zero h0 (pow_ne_zero n hΦ)
        rw [Polynomial.degree_eq_natDegree hne, Polynomial.natDegree_mul h0 (pow_ne_zero n hΦ),
            Polynomial.natDegree_pow]
        have hBn : (B n).natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree h0 (hB n)
        exact_mod_cast (by nlinarith [hBn] :
          (B n).natDegree + n * σ.Φ.natDegree < (n + 1) * σ.Φ.natDegree)

/-- The standard lift is monic of degree `eg·deg Φ` (the not-yet-on-disk `L3.liftMonic`). -/
private lemma lift_monic_deg {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift σ ψ g Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = σ.e * g * σ.Φ.natDegree := by
  obtain ⟨_hψmon, _hψdeg, tt, htt0, httne, hsum⟩ := hlift
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hP : (σ.Φ ^ (σ.e * g)).Monic := σ.hmonic.pow _
  have hPdeg : (σ.Φ ^ (σ.e * g)).natDegree = σ.e * g * σ.Φ.natDegree := by
    rw [Polynomial.natDegree_pow]
  have hQ : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)).degree
      < (↑(σ.e * g * σ.Φ.natDegree) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_)
    intro k hk
    rw [Finset.mem_range] at hk
    rcases eq_or_ne (tt k) 0 with h0 | h0
    · rw [h0, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have hcoeff : ψ.coeff k ≠ 0 := fun h => h0 (htt0 k h)
      have hinC : (tt k).degree < σ.Φ.degree := (httne k hk hcoeff).2.1
      have httnd : (tt k).natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree h0 hinC
      have hne : tt k * σ.Φ ^ (σ.e * k) ≠ 0 := mul_ne_zero h0 (pow_ne_zero _ hΦ)
      rw [Polynomial.degree_eq_natDegree hne, Polynomial.natDegree_mul h0 (pow_ne_zero _ hΦ),
          Polynomial.natDegree_pow]
      have hle1 : σ.e * k + 1 ≤ σ.e * g := by
        have h3 : σ.e * (k + 1) ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) (by omega)
        nlinarith [σ.he, h3]
      have h2 : (σ.e * k + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree :=
        Nat.mul_le_mul hle1 (le_refl σ.Φ.natDegree)
      exact_mod_cast (by nlinarith [httnd, h2] :
        (tt k).natDegree + σ.e * k * σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree)
  have hqlt : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)).degree < (σ.Φ ^ (σ.e * g)).degree := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hPdeg]; exact hQ
  refine ⟨?_, ?_⟩
  · rw [hsum]; exact hP.add_of_left hqlt
  · have hdeq : Φhat.degree = (σ.Φ ^ (σ.e * g)).degree := by
      rw [hsum]; exact Polynomial.degree_add_eq_left_of_degree_lt hqlt
    rw [Polynomial.natDegree_eq_of_degree_eq hdeq, hPdeg]

theorem L5_realRecursion {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (W : ℤ) : (∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Φhat B ∧ σ.w B = W) ↔ (∃ (j : ℕ), j < σ.e * g ∧ (W - (j : ℤ) * σ.h) ∈ (fun ν => (σ.e : ℤ) * ν) '' σ.weightSet) := by
  obtain ⟨hΦhatMon, hΦhatDeg⟩ := lift_monic_deg σ ψ g Φhat hlift
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hd : 1 ≤ σ.Φ.natDegree := σ.hdeg
  have hΦhat0 : Φhat ≠ 0 := hΦhatMon.ne_zero
  have hΦhatDeg' : Φhat.degree = (↑(σ.e * g * σ.Φ.natDegree) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦhat0, hΦhatDeg]
  constructor
  · rintro ⟨B, hBne, hBc, hBW⟩
    obtain ⟨Bfun, N, hdev⟩ := factA_exists σ.Φ σ.hmonic hd B
    have hslot := σ.hK1 B Bfun N hBne hdev
    obtain ⟨hdeg1, _hdeg2, hdeg3⟩ := hdev
    obtain ⟨_, j, hjN, hjnz, hjeq⟩ := hslot
    dsimp only at hjnz hjeq
    have hinCj : inC σ.Φ (Bfun j) := hdeg1 j
    have hjlt : j < σ.e * g := by
      classical
      have hjmem : j ∈ (Finset.range N).filter (fun k => Bfun k ≠ 0) := by
        rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hjN, hjnz⟩
      set S := (Finset.range N).filter (fun k => Bfun k ≠ 0) with hS
      have hSne : S.Nonempty := ⟨j, hjmem⟩
      obtain ⟨m, hmmem, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m :=
        ⟨S.max' hSne, S.max'_mem hSne, fun k hk => S.le_max' k hk⟩
      have hjm : j ≤ m := hmax j hjmem
      have hmrange : m < N := Finset.mem_range.mp (Finset.mem_filter.mp hmmem).1
      have hmnz : Bfun m ≠ 0 := (Finset.mem_filter.mp hmmem).2
      have hBsum : B = ∑ k ∈ Finset.range (m + 1), Bfun k * σ.Φ ^ k := by
        have hsub : Finset.range (m + 1) ⊆ Finset.range N := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        rw [hdeg3]
        refine (Finset.sum_subset hsub ?_).symm
        intro k hkt hks
        rw [Finset.mem_range] at hkt
        rw [Finset.mem_range] at hks
        have hz : Bfun k = 0 := by
          by_contra hc
          have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkt, hc⟩
          have hle : k ≤ m := hmax k hmem
          omega
        rw [hz, zero_mul]
      have hsplit : B = (∑ k ∈ Finset.range m, Bfun k * σ.Φ ^ k) + Bfun m * σ.Φ ^ m := by
        rw [hBsum, Finset.sum_range_succ]
      have hmdle : (↑(m * σ.Φ.natDegree) : WithBot ℕ) ≤ (Bfun m * σ.Φ ^ m).degree := by
        have hne : Bfun m * σ.Φ ^ m ≠ 0 := mul_ne_zero hmnz (pow_ne_zero m hΦ)
        rw [Polynomial.degree_eq_natDegree hne, Polynomial.natDegree_mul hmnz (pow_ne_zero m hΦ),
            Polynomial.natDegree_pow]
        exact_mod_cast Nat.le_add_left _ _
      have hlow : (∑ k ∈ Finset.range m, Bfun k * σ.Φ ^ k).degree < (Bfun m * σ.Φ ^ m).degree :=
        lt_of_lt_of_le (partdeg σ Bfun hdeg1 m) hmdle
      have hdegB : B.degree = (Bfun m * σ.Φ ^ m).degree := by
        rw [hsplit]; exact Polynomial.degree_add_eq_right_of_degree_lt hlow
      have hBltdeg : B.degree < (↑(σ.e * g * σ.Φ.natDegree) : WithBot ℕ) := by
        rw [← hΦhatDeg']; exact hBc
      have hchain : (↑(m * σ.Φ.natDegree) : WithBot ℕ) ≤ B.degree := by rw [hdegB]; exact hmdle
      have hmd : m * σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree := by
        have : (↑(m * σ.Φ.natDegree) : WithBot ℕ) < ↑(σ.e * g * σ.Φ.natDegree) :=
          lt_of_le_of_lt hchain hBltdeg
        exact_mod_cast this
      have hmlt : m < σ.e * g := by
        rcases lt_or_ge m (σ.e * g) with h | h
        · exact h
        · exfalso
          have : σ.e * g * σ.Φ.natDegree ≤ m * σ.Φ.natDegree :=
            Nat.mul_le_mul h (le_refl σ.Φ.natDegree)
          omega
      exact lt_of_le_of_lt hjm hmlt
    refine ⟨j, hjlt, σ.wPrev (Bfun j), σ.hWS (Bfun j) hjnz hinCj, ?_⟩
    show (σ.e : ℤ) * σ.wPrev (Bfun j) = W - (j : ℤ) * σ.h
    have hstretch := σ.hStretch (Bfun j) hjnz hinCj
    rw [σ.hwΦ] at hjeq
    linarith [hstretch, hjeq, hBW]
  · rintro ⟨j, hjlt, ν, hν, hνeq⟩
    have key : (σ.e : ℤ) * ν = W - (j : ℤ) * σ.h := hνeq
    have h1FQ : ((((1 : (↥σ.K)ˣ)) : ↥σ.K) : F) ∈ σ.FQ := by
      simpa using σ.FQ.one_mem
    obtain ⟨b₀, hb₀⟩ := σ.hS6a ν hν
    obtain ⟨b, hbne, hbc, hbw, _hbR⟩ := hb₀ 1 h1FQ
    refine ⟨b * σ.Φ ^ j, mul_ne_zero hbne (pow_ne_zero j hΦ), ?_, ?_⟩
    · show (b * σ.Φ ^ j).degree < Φhat.degree
      have hne : b * σ.Φ ^ j ≠ 0 := mul_ne_zero hbne (pow_ne_zero j hΦ)
      rw [hΦhatDeg', Polynomial.degree_eq_natDegree hne,
          Polynomial.natDegree_mul hbne (pow_ne_zero j hΦ), Polynomial.natDegree_pow]
      have hbd : b.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hbne hbc
      have h2 : (j + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree :=
        Nat.mul_le_mul (by omega) (le_refl σ.Φ.natDegree)
      exact_mod_cast (by nlinarith [hbd, h2] :
        b.natDegree + j * σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree)
    · have hstretch := σ.hStretch b hbne hbc
      rw [σ.hwmul b (σ.Φ ^ j) hbne (pow_ne_zero j hΦ), w_pow σ j, hstretch, hbw, σ.hwΦ]
      linarith [key]

end LeanUrat.Moves
