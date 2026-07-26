/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L0_FactA_exists

/-!
# Moves/L2 — Width bound (MOVES §D.3(d), ~2051-2055)

For `B ∈ Ĉ` (i.e. `deg B < e·g·deg Φ`), the residual `R(B)` is supported in a window of
`ℤ`-positions of width `< g`: `∃ a, support(R B) ⊆ [a, a+g)`.

Sketch: develop `B = Σ_{j<eg} B_j Φ^j` (Fact A, imported).  The residual `R(B)` is the sum of
the residuals of the slots `j` minimizing `w(B_jΦ^j)` (Lemma K1 = the `hK1` stage axiom, plus
the residual laws `hRadd`/`hRlt`: the minimizing residuals sit at pairwise distinct monomial
positions — `e·p_j = j − t·γ` — so no cancellation can occur, and the above-minimum slots are
ultrametrically invisible).  Each minimizing slot contributes a single monomial at position
`p_j = -t·wPrev(B_j) + s·j`, and nonzero slots satisfy `j < eg` by degree domination of the top
slot.  On the minimizing set `w(B_jΦ^j) = w(B) =: γ` is constant, so `p_j = (j - tγ)/e` (Bézout
`es+ht=1`); as `j` ranges over `[0, eg)` these positions span an interval of width `< g`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

/-- `R(1) = 1` (from the multiplicativity axiom `hRmul` plus `hRne`). -/
private lemma R_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) :
    σ.R (1 : Polynomial ℤ_[p]) = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  have hne : σ.R (1 : Polynomial ℤ_[p]) ≠ 0 := σ.hRne 1 one_ne_zero
  have key : σ.R (1 : Polynomial ℤ_[p]) * 1 = σ.R 1 * σ.R 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne key).symm

/-- `w(1) = 0` (from the additivity axiom `hwmul`). -/
private lemma w_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) :
    σ.w (1 : Polynomial ℤ_[p]) = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  linarith

/-- `R(Φ^n) = z^{s·n}` (i.e. `T (s·n)`); iterate `hRmul` and the pinned `R(Φ) = T s`. -/
private lemma R_pow_Phi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) :
    ∀ n : ℕ, σ.R (σ.Φ ^ n) = LaurentPolynomial.T (σ.s * (n : ℤ))
  | 0 => by
      rw [pow_zero, R_one σ, Nat.cast_zero, mul_zero]
      simp
  | (n + 1) => by
      have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
      have hpow : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ0
      rw [pow_succ, σ.hRmul _ _ hpow hΦ0, R_pow_Phi σ n, σ.hRΦ, ← LaurentPolynomial.T_add]
      congr 1
      push_cast; ring

/-- `w(Φ^n) = n·w(Φ)`; iterate `hwmul`. -/
private lemma w_pow_Phi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) :
    ∀ n : ℕ, σ.w (σ.Φ ^ n) = (n : ℤ) * σ.w σ.Φ
  | 0 => by
      rw [pow_zero, Nat.cast_zero, zero_mul]; exact w_one σ
  | (n + 1) => by
      have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
      have hpow : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ0
      rw [pow_succ, σ.hwmul _ _ hpow hΦ0, w_pow_Phi σ n]
      push_cast; ring

/-- **Stride rule (monomial form).** For `Bⱼ ≠ 0` in coefficient space, `R(Bⱼ·Φ^j)` is the single
monomial at position `p = -t·wPrev(Bⱼ) + s·j`. -/
private lemma strideMono {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F)
    (Bj : Polynomial ℤ_[p]) (hBj : Bj ≠ 0) (hmem : inC σ.Φ Bj) (j : ℕ) :
    (σ.R (Bj * σ.Φ ^ j)).support = {(-σ.t * σ.wPrev Bj + σ.s * (j : ℤ))} := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hpow : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ0
  obtain ⟨c, hc⟩ := σ.hS5 Bj hBj hmem
  rw [σ.hRmul _ _ hBj hpow, hc, R_pow_Phi σ j, mul_assoc, ← LaurentPolynomial.T_add,
    ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.support_single_ne_zero _ (Units.ne_zero c)]

/-- **Bézout position identity.** At a minimizing slot (`w(Bⱼ·Φ^j) = γ`), the stride position
`p = -t·wPrev(Bⱼ) + s·j` satisfies `e·p = j - t·γ`. -/
private lemma epos {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F)
    (Bj : Polynomial ℤ_[p]) (hBj : Bj ≠ 0) (hmem : inC σ.Φ Bj) (j : ℕ) (γ : ℤ)
    (hw : σ.w (Bj * σ.Φ ^ j) = γ) :
    (σ.e : ℤ) * (-σ.t * σ.wPrev Bj + σ.s * (j : ℤ)) = (j : ℤ) - σ.t * γ := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hpow : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ0
  have hwm : σ.w (Bj * σ.Φ ^ j) = σ.w Bj + σ.w (σ.Φ ^ j) := σ.hwmul _ _ hBj hpow
  have hwp : σ.w (σ.Φ ^ j) = (j : ℤ) * σ.w σ.Φ := w_pow_Phi σ j
  have hst : σ.w Bj = (σ.e : ℤ) * σ.wPrev Bj := σ.hStretch Bj hBj hmem
  have hΦw : σ.w σ.Φ = (σ.h : ℤ) := σ.hwΦ
  have hmin : γ = (σ.e : ℤ) * σ.wPrev Bj + (j : ℤ) * (σ.h : ℤ) := by
    rw [← hw, hwm, hwp, hst, hΦw]
  have hbez : (σ.e : ℤ) * σ.s + (σ.h : ℤ) * σ.t = 1 := σ.hbez
  linear_combination σ.t * hmin + (j : ℤ) * hbez

/-- **Degree domination of the top slot.** In a `Φ`-development of `f` with
`deg f < M·deg Φ`, every slot `j ≥ M` is zero: the largest nonzero slot `J` dominates the
degree of the sum (`deg f = deg B_J + J·deg Φ ≥ J·deg Φ`). -/
private lemma dev_slot_bound {p : ℕ} [Fact p.Prime] (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic)
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
  -- peel the top slot off the sum
  have hsum2 : f = Bd J * Φ ^ J + ∑ i ∈ S.erase J, Bd i * Φ ^ i := by
    have h1 : ∑ i ∈ S, Bd i * Φ ^ i = ∑ i ∈ Finset.range N, Bd i * Φ ^ i := by
      rw [hSdef]
      exact Finset.sum_filter_of_ne (fun x _ hne hBx => hne (by rw [hBx, zero_mul]))
    rw [hsum, ← h1, ← Finset.add_sum_erase S _ hJS]
  have hdegJ : (Bd J * Φ ^ J).natDegree = (Bd J).natDegree + J * Φ.natDegree := by
    rw [Polynomial.natDegree_mul hBJ (pow_ne_zero J hΦ0), Polynomial.natDegree_pow]
  -- all other slots have strictly smaller degree
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

/-- **Ultrametric lower bound for sums.** A nonzero sum of nonzero terms of weight `≥ c` has
weight `≥ c` (induction on the finset via `hwult`; vanishing partial sums are harmless). -/
private lemma w_sum_lower {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (t : ℕ → Polynomial ℤ_[p]) (c : ℤ) :
    ∀ s : Finset ℕ, (∀ j ∈ s, t j ≠ 0 ∧ c ≤ σ.w (t j)) → (∑ j ∈ s, t j) ≠ 0 →
      c ≤ σ.w (∑ j ∈ s, t j) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _ hne; simp at hne
  | cons a s ha IH =>
    intro hall hne
    rw [Finset.sum_cons] at hne ⊢
    obtain ⟨hta, hwa⟩ := hall a (Finset.mem_cons_self a s)
    have hall' : ∀ j ∈ s, t j ≠ 0 ∧ c ≤ σ.w (t j) :=
      fun j hj => hall j (Finset.mem_cons.mpr (Or.inr hj))
    rcases eq_or_ne (∑ j ∈ s, t j) 0 with hs0 | hs0
    · rw [hs0, add_zero]
      exact hwa
    · exact le_trans (le_min hwa (IH hall' hs0)) (σ.hwult (t a) _ hta hs0 hne)

/-- **Residual slot-decomposition.** Every support position of `R(B)` for `B ∈ Ĉ` comes from a
minimizing slot `j` of the Φ-development, with `j < e·g`, `w(Bⱼ·Φ^j) = w(B)`, and the position
lying in `support(R(Bⱼ·Φ^j))`. Fuses Fact A (development), Lemma K1 (the `hK1` axiom: the weight
is the attained slot minimum), the residual laws (`hRadd`/`hRlt`: minimizing residuals add — no
cancellation, since their monomial positions are pairwise distinct by the Bézout identity), and
the degree bound `j < eg` on nonzero slots. Faithful to MOVES §D.3(d). -/
private lemma slotDecomp {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F)
    (g : ℕ) (hg : 1 ≤ g) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ∀ k ∈ (σ.R B).support, ∃ (Bj : Polynomial ℤ_[p]) (j : ℕ),
      j < σ.e * g ∧ Bj ≠ 0 ∧ inC σ.Φ Bj ∧
        σ.w (Bj * σ.Φ ^ j) = σ.w B ∧ k ∈ (σ.R (Bj * σ.Φ ^ j)).support := by
  classical
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have he0 : (σ.e : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp σ.he
  have hm1ne : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hwm1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) hm1ne hm1ne
    rw [neg_one_mul, neg_neg, w_one σ] at h
    linarith
  -- Fact A: the Φ-adic development of B
  obtain ⟨Bdev, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg B
  obtain ⟨hdevdeg, hdevzero, hdevsum⟩ := hdev
  -- Lemma K1: w(B) is the attained minimum of the slot weights
  obtain ⟨hminle, hminex⟩ := σ.hK1 B Bdev N hB ⟨hdevdeg, hdevzero, hdevsum⟩
  obtain ⟨j₀, hj₀N, hj₀nz, hj₀eq⟩ := hminex
  set γ : ℤ := σ.w B with hγdef
  have hj₀nz' : Bdev j₀ ≠ 0 := hj₀nz
  have hj₀eq' : γ = σ.w (Bdev j₀) + (j₀ : ℤ) * σ.w σ.Φ := hj₀eq
  -- the nonzero slots, split into the minimizing and the above-minimum ones
  set nz : Finset ℕ := (Finset.range N).filter (fun j => Bdev j ≠ 0) with hnzdef
  have hnzsum : ∑ j ∈ nz, Bdev j * σ.Φ ^ j = ∑ j ∈ Finset.range N, Bdev j * σ.Φ ^ j := by
    rw [hnzdef]
    exact Finset.sum_filter_of_ne (fun x _ hne hBx => hne (by rw [hBx, zero_mul]))
  have h2 := Finset.sum_filter_add_sum_filter_not nz
    (fun j => σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ = γ) (fun j => Bdev j * σ.Φ ^ j)
  set minset : Finset ℕ := nz.filter (fun j => σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ = γ)
    with hminsetdef
  set restset : Finset ℕ := nz.filter (fun j => ¬(σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ = γ))
    with hrestsetdef
  have hminmem : ∀ j, j ∈ minset ↔
      j < N ∧ Bdev j ≠ 0 ∧ σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ = γ := by
    intro j
    rw [hminsetdef, Finset.mem_filter, hnzdef, Finset.mem_filter, Finset.mem_range, and_assoc]
  have hrestmem : ∀ j, j ∈ restset ↔
      j < N ∧ Bdev j ≠ 0 ∧ ¬(σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ = γ) := by
    intro j
    rw [hrestsetdef, Finset.mem_filter, hnzdef, Finset.mem_filter, Finset.mem_range, and_assoc]
  -- facts about minimizing slots
  have hmin_facts : ∀ j ∈ minset, Bdev j ≠ 0 ∧ inC σ.Φ (Bdev j) ∧
      (Bdev j * σ.Φ ^ j ≠ 0) ∧ σ.w (Bdev j * σ.Φ ^ j) = γ := by
    intro j hj
    obtain ⟨hjN, hjB, hjw⟩ := (hminmem j).mp hj
    have hinC : inC σ.Φ (Bdev j) := hdevdeg j
    refine ⟨hjB, hinC, mul_ne_zero hjB (pow_ne_zero j hΦ0), ?_⟩
    rw [σ.hwmul (Bdev j) (σ.Φ ^ j) hjB (pow_ne_zero j hΦ0), w_pow_Phi σ j]
    exact hjw
  -- facts about above-minimum slots
  have hrest_facts : ∀ j ∈ restset,
      (Bdev j * σ.Φ ^ j) ≠ 0 ∧ γ + 1 ≤ σ.w (Bdev j * σ.Φ ^ j) := by
    intro j hj
    obtain ⟨hjN, hjB, hjw⟩ := (hrestmem j).mp hj
    have hge : γ ≤ σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ := hminle j hjN hjB
    have hlt : γ < σ.w (Bdev j) + (j : ℤ) * σ.w σ.Φ :=
      lt_of_le_of_ne hge (fun h => hjw h.symm)
    refine ⟨mul_ne_zero hjB (pow_ne_zero j hΦ0), ?_⟩
    rw [σ.hwmul (Bdev j) (σ.Φ ^ j) hjB (pow_ne_zero j hΦ0), w_pow_Phi σ j]
    exact Int.add_one_le_iff.mpr hlt
  have hj₀min : j₀ ∈ minset := (hminmem j₀).mpr ⟨hj₀N, hj₀nz', hj₀eq'.symm⟩
  -- KEY INDUCTION: over any nonempty subset of the minimizing slots, the sum is nonzero of
  -- weight γ and its residual is the sum of the slot residuals (no cancellation: the slot
  -- residuals are monomials at pairwise distinct positions).
  have hmin_sum : ∀ s : Finset ℕ, s ⊆ minset → s.Nonempty →
      (∑ j ∈ s, Bdev j * σ.Φ ^ j) ≠ 0 ∧ σ.w (∑ j ∈ s, Bdev j * σ.Φ ^ j) = γ ∧
        σ.R (∑ j ∈ s, Bdev j * σ.Φ ^ j) = ∑ j ∈ s, σ.R (Bdev j * σ.Φ ^ j) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro _ hne; exact absurd hne Finset.not_nonempty_empty
    | cons a s ha IH =>
      intro hsub _
      have haM : a ∈ minset := hsub (Finset.mem_cons_self a s)
      have hsub' : s ⊆ minset := fun x hx => hsub (Finset.mem_cons.mpr (Or.inr hx))
      obtain ⟨hBa, hinCa, htane, hwta⟩ := hmin_facts a haM
      simp only [Finset.sum_cons]
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        simp only [Finset.sum_empty, add_zero]
        exact ⟨htane, hwta, trivial⟩
      · obtain ⟨hSne, hSw, hSR⟩ := IH hsub' hs
        -- the minimizing positions are pairwise distinct (Bézout identity)
        have hposne : ∀ j ∈ s, (-σ.t * σ.wPrev (Bdev j) + σ.s * (j : ℤ)) ≠
            (-σ.t * σ.wPrev (Bdev a) + σ.s * (a : ℤ)) := by
          intro j hj heqpos
          obtain ⟨hBj', hinCj', _, hwtj'⟩ := hmin_facts j (hsub' hj)
          have h1 := epos σ (Bdev j) hBj' hinCj' j γ hwtj'
          have h2' := epos σ (Bdev a) hBa hinCa a γ hwta
          rw [heqpos] at h1
          have hja' : (j : ℤ) = (a : ℤ) := by linarith
          have hja : j = a := by exact_mod_cast hja'
          exact ha (hja ▸ hj)
        -- the impossible identity: R(Σ_s) can never equal R(−(B_a Φ^a)) (support clash)
        have hcontra : ¬ (σ.R (∑ j ∈ s, Bdev j * σ.Φ ^ j) =
            σ.R ((-1) * (Bdev a * σ.Φ ^ a))) := by
          intro heq
          have hrw : (-1 : Polynomial ℤ_[p]) * (Bdev a * σ.Φ ^ a) = (-(Bdev a)) * σ.Φ ^ a := by
            ring
          have hnegBa : -(Bdev a) ≠ 0 := neg_ne_zero.mpr hBa
          have hinCnega : inC σ.Φ (-(Bdev a)) := by
            show (-(Bdev a)).degree < σ.Φ.degree
            rw [Polynomial.degree_neg]
            exact hinCa
          have hwn : σ.w (-(Bdev a)) = σ.w (Bdev a) := by
            have h := σ.hwmul (-1) (Bdev a) hm1ne hBa
            rw [neg_one_mul] at h
            rw [h, hwm1, zero_add]
          have hwPrev_neg : σ.wPrev (-(Bdev a)) = σ.wPrev (Bdev a) := by
            have hsa := σ.hStretch (Bdev a) hBa hinCa
            have hsn := σ.hStretch (-(Bdev a)) hnegBa hinCnega
            have hkey : (σ.e : ℤ) * σ.wPrev (-(Bdev a)) = (σ.e : ℤ) * σ.wPrev (Bdev a) := by
              rw [← hsn, ← hsa, hwn]
            exact mul_left_cancel₀ he0 hkey
          have hsupp : (σ.R ((-1 : Polynomial ℤ_[p]) * (Bdev a * σ.Φ ^ a))).support =
              {(-σ.t * σ.wPrev (Bdev a) + σ.s * (a : ℤ))} := by
            rw [hrw, strideMono σ (-(Bdev a)) hnegBa hinCnega a, hwPrev_neg]
          have hmem : (-σ.t * σ.wPrev (Bdev a) + σ.s * (a : ℤ)) ∈
              (σ.R (∑ j ∈ s, Bdev j * σ.Φ ^ j)).support := by
            rw [heq, hsupp]
            exact Finset.mem_singleton_self _
          rw [hSR] at hmem
          obtain ⟨j, hjs, hjmem⟩ := Finsupp.mem_support_finsetSum _ hmem
          obtain ⟨hBj', hinCj', _, _⟩ := hmin_facts j (hsub' hjs)
          rw [strideMono σ (Bdev j) hBj' hinCj' j] at hjmem
          exact hposne j hjs (Finset.mem_singleton.mp hjmem).symm
        by_cases hG0 : Bdev a * σ.Φ ^ a + ∑ j ∈ s, Bdev j * σ.Φ ^ j = 0
        · -- would force Σ_s = −(B_a Φ^a), clashing supports
          exfalso
          have hxy : (∑ j ∈ s, Bdev j * σ.Φ ^ j) = (-1) * (Bdev a * σ.Φ ^ a) := by
            linear_combination hG0
          exact hcontra (congrArg σ.R hxy)
        · by_cases hwG : γ < σ.w (Bdev a * σ.Φ ^ a + ∑ j ∈ s, Bdev j * σ.Φ ^ j)
          · -- would force R(Σ_s) = R(−(B_a Φ^a)) via hRlt, clashing supports
            exfalso
            have hne1 : (-1 : Polynomial ℤ_[p]) * (Bdev a * σ.Φ ^ a) ≠ 0 := by
              rw [neg_one_mul]
              exact neg_ne_zero.mpr htane
            have hw1a : σ.w ((-1 : Polynomial ℤ_[p]) * (Bdev a * σ.Φ ^ a)) = γ := by
              rw [σ.hwmul (-1) (Bdev a * σ.Φ ^ a) hm1ne htane, hwm1, hwta, zero_add]
            have hsum_eq : (-1 : Polynomial ℤ_[p]) * (Bdev a * σ.Φ ^ a) +
                (Bdev a * σ.Φ ^ a + ∑ j ∈ s, Bdev j * σ.Φ ^ j) =
                ∑ j ∈ s, Bdev j * σ.Φ ^ j := by ring
            have h := σ.hRlt ((-1) * (Bdev a * σ.Φ ^ a))
              (Bdev a * σ.Φ ^ a + ∑ j ∈ s, Bdev j * σ.Φ ^ j) hne1 hG0
              (by rw [hsum_eq]; exact hSne) (by rw [hw1a]; exact hwG)
            rw [hsum_eq] at h
            exact hcontra h
          · -- the good case: the weight stays at γ and the residuals add
            have hwmin := σ.hwult (Bdev a * σ.Φ ^ a) (∑ j ∈ s, Bdev j * σ.Φ ^ j)
              htane hSne hG0
            rw [hwta, hSw, min_self] at hwmin
            push_neg at hwG
            have hwG_eq : σ.w (Bdev a * σ.Φ ^ a + ∑ j ∈ s, Bdev j * σ.Φ ^ j) = γ :=
              le_antisymm hwG hwmin
            have hRG := σ.hRadd (Bdev a * σ.Φ ^ a) (∑ j ∈ s, Bdev j * σ.Φ ^ j)
              htane hSne hG0 (by rw [hwta, hSw]) (by rw [hwG_eq, hwta])
            exact ⟨hG0, hwG_eq, by rw [hRG, hSR]⟩
  -- split B into the minimizing part and the above-minimum part
  have hsplit : B = (∑ j ∈ minset, Bdev j * σ.Φ ^ j) + (∑ j ∈ restset, Bdev j * σ.Φ ^ j) := by
    calc B = ∑ j ∈ Finset.range N, Bdev j * σ.Φ ^ j := hdevsum
      _ = ∑ j ∈ nz, Bdev j * σ.Φ ^ j := hnzsum.symm
      _ = _ := h2.symm
  obtain ⟨hMne, hMw, hMR⟩ := hmin_sum minset (fun _ hx => hx) ⟨j₀, hj₀min⟩
  -- R(B) = the sum of the minimizing-slot residuals
  have hRB : σ.R B = ∑ j ∈ minset, σ.R (Bdev j * σ.Φ ^ j) := by
    by_cases hrest0 : (∑ j ∈ restset, Bdev j * σ.Φ ^ j) = 0
    · rw [hsplit, hrest0, add_zero]
      exact hMR
    · have hwrest : γ + 1 ≤ σ.w (∑ j ∈ restset, Bdev j * σ.Φ ^ j) :=
        w_sum_lower σ (fun j => Bdev j * σ.Φ ^ j) (γ + 1) restset hrest_facts hrest0
      have hBne' : (∑ j ∈ minset, Bdev j * σ.Φ ^ j) + (∑ j ∈ restset, Bdev j * σ.Φ ^ j) ≠ 0 := by
        rw [← hsplit]
        exact hB
      have hRlt' := σ.hRlt (∑ j ∈ minset, Bdev j * σ.Φ ^ j)
        (∑ j ∈ restset, Bdev j * σ.Φ ^ j) hMne hrest0 hBne' (by rw [hMw]; linarith)
      rw [hsplit, hRlt']
      exact hMR
  -- conclude
  intro k hk
  rw [hRB] at hk
  obtain ⟨j, hjmin, hjmem⟩ := Finsupp.mem_support_finsetSum _ hk
  obtain ⟨hBj, hinCj, _, hwtj⟩ := hmin_facts j hjmin
  have hjlt : j < σ.e * g := by
    by_contra hge
    push_neg at hge
    exact hBj (dev_slot_bound σ.Φ σ.hmonic B Bdev N (σ.e * g)
      ⟨hdevdeg, hdevzero, hdevsum⟩ hBdeg j hge)
  exact ⟨Bdev j, j, hjlt, hBj, hinCj, hwtj, hjmem⟩

theorem L2_widthBound {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (g : ℕ) (hg : 1 ≤ g) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) : ∃ a : ℤ, ∀ k ∈ (σ.R B).support, a ≤ k ∧ k < a + g := by
  classical
  have hLne : σ.R B ≠ 0 := σ.hRne B hB
  have hsupp_ne : (σ.R B).support.Nonempty := Finsupp.support_nonempty_iff.mpr hLne
  -- pairwise width bound: any two support positions differ by less than g
  have hpair : ∀ x ∈ (σ.R B).support, ∀ y ∈ (σ.R B).support, x - y < (g : ℤ) := by
    intro x hx y hy
    obtain ⟨Bx, jx, hjx, hBx, hmemx, hwx, hxin⟩ := slotDecomp σ g hg B hB hBdeg x hx
    obtain ⟨By, jy, hjy, hBy, hmemy, hwy, hyin⟩ := slotDecomp σ g hg B hB hBdeg y hy
    rw [strideMono σ Bx hBx hmemx jx, Finset.mem_singleton] at hxin
    rw [strideMono σ By hBy hmemy jy, Finset.mem_singleton] at hyin
    have hex : (σ.e : ℤ) * x = (jx : ℤ) - σ.t * σ.w B := by
      rw [hxin]; exact epos σ Bx hBx hmemx jx (σ.w B) hwx
    have hey : (σ.e : ℤ) * y = (jy : ℤ) - σ.t * σ.w B := by
      rw [hyin]; exact epos σ By hBy hmemy jy (σ.w B) hwy
    have hdiff : (σ.e : ℤ) * (x - y) = (jx : ℤ) - (jy : ℤ) := by rw [mul_sub, hex, hey]; ring
    have he0 : (0 : ℤ) < (σ.e : ℤ) := by exact_mod_cast σ.he
    have hjxb : (jx : ℤ) < (σ.e : ℤ) * (g : ℤ) := by exact_mod_cast hjx
    have hjyb : (0 : ℤ) ≤ (jy : ℤ) := by positivity
    have hlt : (σ.e : ℤ) * (x - y) < (σ.e : ℤ) * (g : ℤ) := by rw [hdiff]; omega
    by_contra hcon
    push_neg at hcon
    have hmul : (σ.e : ℤ) * (g : ℤ) ≤ (σ.e : ℤ) * (x - y) :=
      mul_le_mul_of_nonneg_left hcon (le_of_lt he0)
    omega
  refine ⟨(σ.R B).support.min' hsupp_ne, ?_⟩
  intro k hk
  refine ⟨Finset.min'_le _ k hk, ?_⟩
  have hb := hpair k hk ((σ.R B).support.min' hsupp_ne) (Finset.min'_mem _ hsupp_ne)
  linarith

end LeanUrat.Moves
