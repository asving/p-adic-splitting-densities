/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.HC1.T3_htChainWeight

/-!
# HC1.T4_slotMinHt — LST(i-b): the iterated slot minimum

moves_ref: MOVES 3738–3739 "w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y_{(b,l)} ≠ 0}
(the iterated slot-minimum)". deps: T3; Moves `hK1`/`L0_FactB_unique`. Stated in the
Moves `SlotMinAttained` attained form (E-phase convention; sInf on WithTop ℚ dodged).
difficulty: medium. hyp: none.

Proof route (escalation, 2026-07-28): everything rides the per-stage STRUCTURE FIELDS
(`hwmul`/`hwult`/`hK1`/`hStretch`/`hS6a`) plus the move cores' `w`/`wPrev` transport —
no spine `StageCoreL` persistence needed.
* generic stage-valuation lemmas (`w 1 = 0`, `w (−f) = w f`, the strict ultrametric,
  distinct-value sums);
* `digLift` is a genuine base realizer via the base pin + (S6a) (`≠ 0`, `inC Φ₀`,
  `wPrev = 0`);
* `qterm k c := digLift (y c)·p^l·∏_{r<k} Φ_r^{slot_r c}` with the mixed-radix degree
  bound `deg (qterm k c) < deg Φ_k`;
* THE INDUCTION (`slot_min_claim`): for a nonempty support-set sharing all slots at
  levels ≥ k, `∑ qterm k` is nonzero with ATTAINED `w_k`-minimum — base case: distinct
  p-levels have distinct `w₀`-values (no ties possible); step: regroup fiberwise by
  `slot k`, apply stage-k `hK1` on the development (nonzeroness via `L0_FactB_unique`
  against the zero development), then stretch to stage k+1;
* `T.HasSide` is constructed (w_smul from `gaussVal ≥ 0` + the T3 stretch chain), so
  `side_w` converts `wQ`, and T3 converts the top weight to `strTop·ht`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## A. Generic stage-valuation lemmas (from the structure fields alone) -/

private lemma t4_w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have hw := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at hw; omega

private lemma t4_w_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.w (f ^ n) = (n : ℤ) * σ.w f := by
  induction n with
  | zero => simp [t4_w_one]
  | succ n ih =>
    have hfn : f ^ n ≠ 0 := pow_ne_zero n hf
    rw [pow_succ, σ.hwmul _ _ hfn hf, ih]; push_cast; ring

private lemma t4_w_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.w (-f) = σ.w f := by
  have hm1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := by
    intro h; exact one_ne_zero (α := Polynomial ℤ_[p]) (by linear_combination -h)
  have hsq : σ.w ((-1 : Polynomial ℤ_[p]) * (-1)) = σ.w (-1) + σ.w (-1) :=
    σ.hwmul _ _ hm1 hm1
  rw [neg_one_mul, neg_neg] at hsq
  have hone := t4_w_one σ
  have hw1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by omega
  have : σ.w ((-1 : Polynomial ℤ_[p]) * f) = σ.w (-1) + σ.w f := σ.hwmul _ _ hm1 hf
  rw [neg_one_mul] at this
  rw [this, hw1, zero_add]

/-- The strict ultrametric: strictly smaller weight wins, and the sum cannot vanish. -/
private lemma t4_w_strict (σ : Stage p F) {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : σ.w f < σ.w g) : f + g ≠ 0 ∧ σ.w (f + g) = σ.w f := by
  have hne : f + g ≠ 0 := by
    intro h0
    have hfg : f = -g := eq_neg_of_add_eq_zero_left h0
    rw [hfg, t4_w_neg σ g hg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, ?_⟩
  have h1 : min (σ.w f) (σ.w g) ≤ σ.w (f + g) := σ.hwult f g hf hg hne
  have hgneg : (-g : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hg
  have h2 : min (σ.w (f + g)) (σ.w (-g)) ≤ σ.w f := by
    have hsum : f + g + -g = f := by ring
    have := σ.hwult (f + g) (-g) hne hgneg (by rw [hsum]; exact hf)
    rwa [hsum] at this
  rw [t4_w_neg σ g hg] at h2
  omega

/-- Sum over a finite set with pairwise DISTINCT weights: nonzero, weight = the attained min. -/
private lemma t4_w_sum_distinct (σ : Stage p F) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → Polynomial ℤ_[p]) :
    S.Nonempty → (∀ i ∈ S, f i ≠ 0) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → σ.w (f i) ≠ σ.w (f j)) →
    (∑ i ∈ S, f i) ≠ 0 ∧ ∃ i₀ ∈ S, σ.w (∑ i ∈ S, f i) = σ.w (f i₀) ∧
      ∀ i ∈ S, σ.w (f i₀) ≤ σ.w (f i) := by
  induction S using Finset.induction_on with
  | empty => intro h; exact absurd h (by simp)
  | @insert a s ha ih =>
    intro _ hne hdist
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      rw [Finset.sum_insert (Finset.notMem_empty a), Finset.sum_empty, add_zero]
      refine ⟨hne a (Finset.mem_insert_self a ∅), a, Finset.mem_insert_self a ∅, rfl, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with h | h
      · subst h; exact le_refl _
      · exact absurd h (Finset.notMem_empty i)
    · have hne' : ∀ i ∈ s, f i ≠ 0 := fun i hi => hne i (Finset.mem_insert_of_mem hi)
      have hdist' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ.w (f i) ≠ σ.w (f j) := fun i hi j hj =>
        hdist i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
      obtain ⟨hsne, i₀, hi₀, hw₀, hmin₀⟩ := ih hs hne' hdist'
      have hfa : f a ≠ 0 := hne a (Finset.mem_insert_self a s)
      have hai₀ : a ≠ i₀ := fun h => ha (h ▸ hi₀)
      have hd : σ.w (f a) ≠ σ.w (f i₀) :=
        hdist a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) hai₀
      rw [Finset.sum_insert ha]
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · -- the new element is the strict min
        have hlt' : σ.w (f a) < σ.w (∑ i ∈ s, f i) := by rw [hw₀]; exact hlt
        obtain ⟨hne2, hw2⟩ := t4_w_strict σ hfa hsne hlt'
        refine ⟨hne2, a, Finset.mem_insert_self a s, hw2, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with h | h
        · subst h; exact le_refl _
        · exact le_trans (le_of_lt hlt) (hmin₀ i h)
      · -- the old min survives
        have hlt' : σ.w (∑ i ∈ s, f i) < σ.w (f a) := by rw [hw₀]; exact hgt
        obtain ⟨hne2, hw2⟩ := t4_w_strict σ hsne hfa hlt'
        rw [add_comm (∑ i ∈ s, f i) (f a)] at hne2 hw2
        refine ⟨hne2, i₀, Finset.mem_insert_of_mem hi₀, by rw [hw2, hw₀], ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with h | h
        · subst h; exact le_of_lt hgt
        · exact hmin₀ i h

/-! ## B. gaussVal facts -/

private lemma t4_gaussVal_C_p : gaussVal (C (p : ℤ_[p])) = 1 := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  have hsupp : (C (p : ℤ_[p])).support = {0} := by rw [Polynomial.support_C hp0]
  unfold gaussVal
  have hne : (C (p : ℤ_[p])).support.Nonempty :=
    ⟨0, by rw [hsupp]; exact Finset.mem_singleton_self 0⟩
  rw [dif_pos hne]
  have hval : ((C (p : ℤ_[p])).support).inf' hne (fun i => (((C (p : ℤ_[p])).coeff i).valuation : ℤ))
      = (((C (p : ℤ_[p])).coeff 0).valuation : ℤ) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hsupp]; exact Finset.mem_singleton_self 0)
    · apply Finset.le_inf'
      intro b hb
      rw [hsupp, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval, coeff_C_zero, PadicInt.valuation_p, Nat.cast_one]

private lemma t4_gaussVal_one : gaussVal (1 : Polynomial ℤ_[p]) = 0 := by
  have h1 : (1 : ℤ_[p]) ≠ 0 := one_ne_zero
  have hsupp : (1 : Polynomial ℤ_[p]).support = {0} := by
    rw [← Polynomial.C_1, Polynomial.support_C h1]
  unfold gaussVal
  have hne : (1 : Polynomial ℤ_[p]).support.Nonempty :=
    ⟨0, by rw [hsupp]; exact Finset.mem_singleton_self 0⟩
  rw [dif_pos hne]
  have hval : ((1 : Polynomial ℤ_[p]).support).inf' hne (fun i => (((1 : Polynomial ℤ_[p]).coeff i).valuation : ℤ))
      = (((1 : Polynomial ℤ_[p]).coeff 0).valuation : ℤ) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hsupp]; exact Finset.mem_singleton_self 0)
    · apply Finset.le_inf'
      intro b hb
      rw [hsupp, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval, Polynomial.coeff_one_zero, PadicInt.valuation_one, Nat.cast_zero]

private lemma t4_gaussVal_nonneg (f : Polynomial ℤ_[p]) : 0 ≤ gaussVal f := by
  unfold gaussVal
  by_cases h : f.support.Nonempty
  · rw [dif_pos h]
    apply Finset.le_inf'
    intro b _
    exact Int.natCast_nonneg _
  · rw [dif_neg h]

/-! ## C. strAux, degree monotonicity, the stretch chain (T3's private apparatus, replicated) -/

private lemma t4_strAux_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    T.strAux (k + 1) = T.strAux k * (T.stg ⟨k, hk⟩).e := by
  have h : T.strAux (k + 1)
      = T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := rfl
  rw [h, dif_pos hk]

private lemma t4_strAux_pos (T : Tower p F) (k : ℕ) : 0 < T.strAux k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    by_cases hc : n < T.K + 1
    · rw [t4_strAux_succ T n hc]
      exact Nat.mul_pos ih (by have := (T.stg ⟨n, hc⟩).he; omega)
    · have h : T.strAux (n + 1)
          = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
      rw [h, dif_neg hc, mul_one]; exact ih

private lemma t4_strTop_eq (T : Tower p F) : T.strTop = T.strAux (T.K + 1) := by
  rw [t4_strAux_succ T T.K (Nat.lt_succ_self _)]; rfl

private lemma t4_degC_lt (σ : Stage p F) : (C (p : ℤ_[p])).degree < σ.Φ.degree := by
  rw [Polynomial.degree_C PadicInt.prime_p.ne_zero, Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one σ.hdeg

/-- Degree divisibility per move: `deg Φ_m ∣ deg Φ_{m+1}` (increment: `deg Φ̂ = e·g·deg Φ`;
recentering: degree unchanged). -/
private lemma t4_deg_dvd_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree ∣ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree := by
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.castSucc).Φ.natDegree ∣ (T.stg k.succ).Φ.natDegree
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [hkey, hdeg]
    exact ⟨(T.stg k.castSucc).e * g, by ring⟩
  | recenter cc tt core _ =>
    obtain ⟨_, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    rw [hΦ']
    have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
    have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
    have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt htt
    have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [hnd]

private lemma t4_deg_mono_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree ≤ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree :=
  Nat.le_of_dvd (by
    have := (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).hdeg; omega) (t4_deg_dvd_step T m hm)

private lemma t4_deg_le (T : Tower p F) (a : ℕ) :
    ∀ (b : ℕ) (hab : a ≤ b) (hbK : b < T.K + 1),
      (T.stg ⟨a, by omega⟩).Φ.natDegree ≤ (T.stg ⟨b, hbK⟩).Φ.natDegree := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have hnlt : n < T.K := by omega
    exact le_trans (ih hnK) (t4_deg_mono_step T n hnlt)

/-- The slot bound is exact: `slotBound r · deg Φ_r = deg Φ_{r+1}`. -/
private lemma t4_slotBound_mul (T : Tower p F) (r : Fin T.K) :
    T.slotBound r * (T.stg r.castSucc).Φ.natDegree = (T.stg r.succ).Φ.natDegree := by
  have hcs : (⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ : Fin (T.K + 1)) = r.castSucc := Fin.ext rfl
  have hsc : (⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ : Fin (T.K + 1)) = r.succ := Fin.ext rfl
  have hdvd := t4_deg_dvd_step T r.val r.isLt
  rw [hcs, hsc] at hdvd
  unfold Tower.slotBound
  exact Nat.div_mul_cancel hdvd

private lemma t4_stretch_step (T : Tower p F) (m : ℕ) (hm0 : m < T.K + 1) (hm1 : m + 1 < T.K + 1)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hcoef : B.degree < (T.stg ⟨m + 1, hm1⟩).Φ.degree) :
    (T.stg ⟨m + 1, hm1⟩).w B = ((T.stg ⟨m + 1, hm1⟩).e : ℤ) * (T.stg ⟨m, hm0⟩).w B := by
  have hm : m < T.K := by omega
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.succ).w B = ((T.stg k.succ).e : ℤ) * (T.stg k.castSucc).w B
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    rw [(T.stg k.succ).hStretch B hB hcoef, core.base.child_wPrev B]
  | recenter cc tt core _ =>
    obtain ⟨_, he', _, _, _, _, _, _, hw, _, _, _, _, _⟩ := core.base
    rw [hw B, he']; simp

private lemma t4_stretch_chain (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (r : ℕ) (hr : r < T.K + 1)
    (hcoef : ∀ mm : Fin (T.K + 1), r < mm.val → B.degree < (T.stg mm).Φ.degree) :
    ∀ (m : ℕ) (_ : r ≤ m) (hmK : m < T.K + 1),
      (T.strAux (r + 1) : ℤ) * (T.stg ⟨m, hmK⟩).w B
        = (T.strAux (m + 1) : ℤ) * (T.stg ⟨r, hr⟩).w B := by
  intro m hrm
  induction m, hrm using Nat.le_induction with
  | base => intro _; rfl
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have ihn : (T.strAux (r + 1) : ℤ) * (T.stg ⟨n, hnK⟩).w B
        = (T.strAux (n + 1) : ℤ) * (T.stg ⟨r, hr⟩).w B := ih hnK
    have hstep : (T.stg ⟨n + 1, hbK⟩).w B
        = ((T.stg ⟨n + 1, hbK⟩).e : ℤ) * (T.stg ⟨n, hnK⟩).w B :=
      t4_stretch_step T n hnK hbK B hB (hcoef ⟨n + 1, hbK⟩ (Nat.lt_succ_of_le hn))
    have hstrAux : T.strAux (n + 1 + 1) = T.strAux (n + 1) * (T.stg ⟨n + 1, hbK⟩).e := by
      have h : T.strAux (n + 1 + 1)
          = T.strAux (n + 1) * (if h : n + 1 < T.K + 1 then (T.stg ⟨n + 1, h⟩).e else 1) := rfl
      rw [h, dif_pos hbK]
    rw [hstep, hstrAux]; push_cast
    linear_combination ((T.stg ⟨n + 1, hbK⟩).e : ℤ) * ihn

/-- Coefficient-space elements of the BASE stage have their top-stage weight pinned by the
stage-0 weight: `strAux 1 · w_m(B) = strAux (m+1) · w₀(B)`. Two corollaries below. -/
private lemma t4_base_transport (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hcoef : B.degree < (T.stg 0).Φ.degree) (m : ℕ) (hmK : m < T.K + 1) :
    (T.strAux 1 : ℤ) * (T.stg ⟨m, hmK⟩).w B
      = (T.strAux (m + 1) : ℤ) * (T.stg ⟨0, Nat.succ_pos _⟩).w B := by
  have h0 : (0 : ℕ) < T.K + 1 := Nat.succ_pos _
  have hcoef' : ∀ mm : Fin (T.K + 1), 0 < mm.val → B.degree < (T.stg mm).Φ.degree := by
    intro mm _
    calc B.degree < (T.stg 0).Φ.degree := hcoef
    _ ≤ (T.stg mm).Φ.degree := by
        rw [Polynomial.degree_eq_natDegree (T.stg 0).hmonic.ne_zero,
            Polynomial.degree_eq_natDegree (T.stg mm).hmonic.ne_zero]
        have h := t4_deg_le T 0 mm.val (Nat.zero_le _) mm.isLt
        have hmm : (⟨mm.val, mm.isLt⟩ : Fin (T.K + 1)) = mm := Fin.ext rfl
        rw [hmm] at h
        exact_mod_cast h
  exact t4_stretch_chain T B hB 0 h0 hcoef' m (Nat.zero_le _) hmK

private lemma t4_transport_zero (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hcoef : B.degree < (T.stg 0).Φ.degree)
    (hw0 : (T.stg ⟨0, Nat.succ_pos _⟩).w B = 0) (m : ℕ) (hmK : m < T.K + 1) :
    (T.stg ⟨m, hmK⟩).w B = 0 := by
  have h := t4_base_transport T B hB hcoef m hmK
  rw [hw0, mul_zero] at h
  have hpos : (0 : ℤ) < (T.strAux 1 : ℤ) := by exact_mod_cast t4_strAux_pos T 1
  rcases mul_eq_zero.mp h with h1 | h1
  · omega
  · exact h1

private lemma t4_transport_nonneg (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hcoef : B.degree < (T.stg 0).Φ.degree)
    (hw0 : 0 ≤ (T.stg ⟨0, Nat.succ_pos _⟩).w B) (m : ℕ) (hmK : m < T.K + 1) :
    0 ≤ (T.stg ⟨m, hmK⟩).w B := by
  have h := t4_base_transport T B hB hcoef m hmK
  have hpos1 : (0 : ℤ) < (T.strAux 1 : ℤ) := by exact_mod_cast t4_strAux_pos T 1
  have hpos2 : (0 : ℤ) ≤ (T.strAux (m + 1) : ℤ) := by positivity
  nlinarith [mul_nonneg hpos2 hw0]

/-! ## D. `digLift` is a genuine base realizer (base pin + (S6a)) -/

private lemma t4_digLift_zero (T : Tower p F) : T.digLift 0 = 0 := by
  unfold Tower.digLift
  rw [dif_neg]
  rintro ⟨B, hB0, _, _, hR⟩
  have hzero : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := by
    ext; simp
  rw [hzero] at hR
  rw [map_zero, zero_mul] at hR
  exact (T.stg 0).hRne B hB0 hR

private lemma t4_digLift_spec (T : Tower p F) (v : ↥(T.stg 0).FQ) (hv : v ≠ 0) :
    T.digLift v ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift v) ∧ (T.stg 0).wPrev (T.digLift v) = 0 := by
  have h1ne : (1 : Polynomial ℤ_[p]) ≠ 0 := one_ne_zero
  have h1inC : inC (T.stg 0).Φ (1 : Polynomial ℤ_[p]) := by
    unfold inC
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree (T.stg 0).hmonic.ne_zero]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (T.stg 0).hdeg
  have hwPrev1 : (T.stg 0).wPrev 1 = 0 := by
    rw [T.base.1.1 1 h1ne, t4_gaussVal_one]
  have h0mem : (0 : ℤ) ∈ (T.stg 0).weightSet := by
    have := (T.stg 0).hWS 1 h1ne h1inC
    rwa [hwPrev1] at this
  have hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
      (T.stg 0).R B = LaurentPolynomial.C (⟨(v : F), (T.stg 0).hFQ_le v.2⟩ : ↥(T.stg 0).K) *
        LaurentPolynomial.T 0 := by
    set x : ↥(T.stg 0).K := ⟨(v : F), (T.stg 0).hFQ_le v.2⟩ with hx
    have hxne : x ≠ 0 := by
      intro h
      apply hv
      have hvF : (v : F) = 0 := congrArg Subtype.val h
      exact Subtype.ext hvF
    have hmem : (((Units.mk0 x hxne : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ := by
      rw [Units.val_mk0]
      exact v.2
    obtain ⟨B, hB0, hBinC, hBw, hBR⟩ := (T.stg 0).hS6a 0 h0mem (Units.mk0 x hxne) hmem
    refine ⟨B, hB0, hBinC, hBw, ?_⟩
    rw [hBR, Units.val_mk0]
    norm_num
  unfold Tower.digLift
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1, hex.choose_spec.2.2.1⟩

/-! ## E. The partial slot terms and their degree bound (mixed radix) -/

/-- `qterm k c = digLift(y c)·p^l·∏_{r<k} Φ_r^{slot_r c}` — the level-`k` partial term. -/
private noncomputable def qterm (T : Tower p F) (y : T.Coord → ↥(T.stg 0).FQ) (k : ℕ)
    (c : T.Coord) : Polynomial ℤ_[p] :=
  T.digLift (y c) * ((C (p : ℤ_[p])) ^ c.l *
    ∏ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k), (T.stg r).Φ ^ c.slot r)

private lemma t4_filter_zero (T : Tower p F) :
    (Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < 0)) = ∅ := by
  ext r; simp

private lemma t4_filter_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    (Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k + 1))
      = insert (⟨k, hk⟩ : Fin (T.K + 1))
          (Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k)) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

private lemma t4_kf_notmem (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    (⟨k, hk⟩ : Fin (T.K + 1)) ∉
      (Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k)) := by
  simp

private lemma t4_qterm_ne (T : Tower p F) (y : T.Coord → ↥(T.stg 0).FQ) (k : ℕ)
    (c : T.Coord) (hyc : y c ≠ 0) : qterm T y k c ≠ 0 := by
  unfold qterm
  have h1 := (t4_digLift_spec T (y c) hyc).1
  have h2 : ((C (p : ℤ_[p])) ^ c.l : Polynomial ℤ_[p]) ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Polynomial.C_eq_zero]; exact PadicInt.prime_p.ne_zero)
  have h3 : (∏ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
      (T.stg r).Φ ^ c.slot r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)
  exact mul_ne_zero h1 (mul_ne_zero h2 h3)

private lemma t4_qterm_succ (T : Tower p F) (y : T.Coord → ↥(T.stg 0).FQ) (k : ℕ)
    (hk : k < T.K + 1) (c : T.Coord) :
    qterm T y (k + 1) c = qterm T y k c * (T.stg ⟨k, hk⟩).Φ ^ c.slot ⟨k, hk⟩ := by
  unfold qterm
  rw [t4_filter_succ T k hk, Finset.prod_insert (t4_kf_notmem T k hk)]
  ring

/-- The mixed-radix degree bound: `deg Φ₀ + Σ_{r<k} slot_r·deg Φ_r ≤ deg Φ_k`. -/
private lemma t4_mixedRadix (T : Tower p F) (c : T.Coord) :
    ∀ (k : ℕ) (hk : k ≤ T.K),
      (T.stg 0).Φ.natDegree
        + ∑ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
            c.slot r * (T.stg r).Φ.natDegree
      ≤ (T.stg ⟨k, by omega⟩).Φ.natDegree := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [t4_filter_zero T, Finset.sum_empty, add_zero]
    exact le_refl _
  | succ k ih =>
    intro hk
    have hkK : k ≤ T.K := by omega
    have hklt : k < T.K := by omega
    have hkf : k < T.K + 1 := by omega
    rw [t4_filter_succ T k hkf, Finset.sum_insert (t4_kf_notmem T k hkf)]
    -- the slot bound at level k
    have hcast : ((⟨k, hklt⟩ : Fin T.K).castSucc : Fin (T.K + 1)) = ⟨k, hkf⟩ := Fin.ext rfl
    have hsucc : ((⟨k, hklt⟩ : Fin T.K).succ : Fin (T.K + 1)) = ⟨k + 1, by omega⟩ := Fin.ext rfl
    have hslt := c.slot_lt ⟨k, hklt⟩
    rw [hcast] at hslt
    have hbound := t4_slotBound_mul T ⟨k, hklt⟩
    rw [hcast, hsucc] at hbound
    have hstep : (c.slot ⟨k, hkf⟩ + 1) * (T.stg ⟨k, hkf⟩).Φ.natDegree
        ≤ (T.stg ⟨k + 1, by omega⟩).Φ.natDegree := by
      rw [← hbound]
      exact Nat.mul_le_mul_right _ hslt
    have hih := ih hkK
    calc (T.stg 0).Φ.natDegree
        + (c.slot ⟨k, hkf⟩ * (T.stg ⟨k, hkf⟩).Φ.natDegree
          + ∑ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
              c.slot r * (T.stg r).Φ.natDegree)
        = ((T.stg 0).Φ.natDegree
            + ∑ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
                c.slot r * (T.stg r).Φ.natDegree)
          + c.slot ⟨k, hkf⟩ * (T.stg ⟨k, hkf⟩).Φ.natDegree := by ring
      _ ≤ (T.stg ⟨k, by omega⟩).Φ.natDegree
          + c.slot ⟨k, hkf⟩ * (T.stg ⟨k, hkf⟩).Φ.natDegree := by
          exact Nat.add_le_add_right hih _
      _ = (c.slot ⟨k, hkf⟩ + 1) * (T.stg ⟨k, hkf⟩).Φ.natDegree := by ring
      _ ≤ (T.stg ⟨k + 1, by omega⟩).Φ.natDegree := hstep

/-- The degree bound for the level-`k` partial terms: `deg (qterm k c) < deg Φ_k`. -/
private lemma t4_qterm_deg (T : Tower p F) (y : T.Coord → ↥(T.stg 0).FQ) (k : ℕ)
    (hk : k ≤ T.K) (c : T.Coord) (hyc : y c ≠ 0) :
    (qterm T y k c).degree < (T.stg ⟨k, by omega⟩).Φ.degree := by
  obtain ⟨hdne, hdinC, _⟩ := t4_digLift_spec T (y c) hyc
  have hqne := t4_qterm_ne T y k c hyc
  have hCne : ((C (p : ℤ_[p])) ^ c.l : Polynomial ℤ_[p]) ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Polynomial.C_eq_zero]; exact PadicInt.prime_p.ne_zero)
  have hprodne : (∏ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
      (T.stg r).Φ ^ c.slot r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)
  -- natDegree of the term
  have hnd : (qterm T y k c).natDegree
      = (T.digLift (y c)).natDegree
        + ∑ r ∈ Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < k),
            c.slot r * (T.stg r).Φ.natDegree := by
    unfold qterm
    rw [Polynomial.natDegree_mul hdne (mul_ne_zero hCne hprodne),
        Polynomial.natDegree_mul hCne hprodne,
        Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero, zero_add,
        Polynomial.natDegree_prod _ _ (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)]
    congr 1
    exact Finset.sum_congr rfl (fun r _ => Polynomial.natDegree_pow _ _)
  have hdlt : (T.digLift (y c)).natDegree < (T.stg 0).Φ.natDegree :=
    Polynomial.natDegree_lt_natDegree hdne hdinC
  have hle := t4_mixedRadix T c k hk
  have hndlt : (qterm T y k c).natDegree < (T.stg ⟨k, by omega⟩).Φ.natDegree := by omega
  rw [Polynomial.degree_eq_natDegree hqne,
      Polynomial.degree_eq_natDegree (T.stg ⟨k, by omega⟩).hmonic.ne_zero]
  exact_mod_cast hndlt

private lemma t4_coord_ext {T : Tower p F} {c c' : T.Coord} (hl : c.l = c'.l)
    (hs : ∀ r, c.slot r = c'.slot r) : c = c' := by
  cases c; cases c'
  simp only [Tower.Coord.mk.injEq]
  exact ⟨hl, funext hs⟩

/-! ## F. THE INDUCTION — the iterated slot minimum on slot-prefix classes -/

/-- The tower induction (LST(i-b) core): for a nonempty set of nonzero-digit coordinates
sharing all slots at levels ≥ k, the sum of the level-k partial terms is NONZERO and its
stage-k weight is the ATTAINED minimum of the term weights. Base: distinct p-levels give
distinct stage-0 weights (strict ultrametric, no ties). Step: regroup fiberwise by the
level-k slot, apply stage-k `hK1` (nonzeroness via `L0_FactB_unique` against the zero
development), stretch to stage k+1. -/
private lemma t4_claim (T : Tower p F) (y : T.Coord → ↥(T.stg 0).FQ) :
    ∀ (k : ℕ) (hk : k < T.K + 1) (S : Finset T.Coord),
      S.Nonempty → (∀ c ∈ S, y c ≠ 0) →
      (∀ c ∈ S, ∀ c' ∈ S, ∀ r : Fin (T.K + 1), k ≤ r.val → c.slot r = c'.slot r) →
      (∑ c ∈ S, qterm T y k c) ≠ 0 ∧
      ∃ c₀ ∈ S, (T.stg ⟨k, hk⟩).w (∑ c ∈ S, qterm T y k c)
          = (T.stg ⟨k, hk⟩).w (qterm T y k c₀) ∧
        ∀ c ∈ S, (T.stg ⟨k, hk⟩).w (qterm T y k c₀) ≤ (T.stg ⟨k, hk⟩).w (qterm T y k c) := by
  classical
  intro k
  induction k with
  | zero =>
    intro hk S hS hne hshare
    -- the level-0 term weights are e₀·l — distinct across the class
    have hCp : (C (p : ℤ_[p])) ≠ 0 := by
      rw [Ne, Polynomial.C_eq_zero]; exact PadicInt.prime_p.ne_zero
    have hwq : ∀ c, y c ≠ 0 →
        (T.stg 0).w (qterm T y 0 c) = (c.l : ℤ) * ((T.stg 0).e : ℤ) := by
      intro c hyc
      obtain ⟨hdne, hdinC, hdw⟩ := t4_digLift_spec T (y c) hyc
      have hq : qterm T y 0 c = T.digLift (y c) * (C (p : ℤ_[p])) ^ c.l := by
        unfold qterm; rw [t4_filter_zero T, Finset.prod_empty, mul_one]
      have hwd : (T.stg 0).w (T.digLift (y c)) = 0 := by
        rw [(T.stg 0).hStretch _ hdne hdinC, hdw, mul_zero]
      have hwCp : (T.stg 0).w (C (p : ℤ_[p])) = ((T.stg 0).e : ℤ) := by
        rw [(T.stg 0).hStretch _ hCp (t4_degC_lt (T.stg 0)), T.base.1.1 _ hCp,
            t4_gaussVal_C_p, mul_one]
      rw [hq, (T.stg 0).hwmul _ _ hdne (pow_ne_zero _ hCp), hwd,
          t4_w_pow (T.stg 0) _ hCp, hwCp]
      ring
    have hdist : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' →
        (T.stg ⟨0, hk⟩).w (qterm T y 0 c) ≠ (T.stg ⟨0, hk⟩).w (qterm T y 0 c') := by
      intro c hc c' hc' hne' heq
      have heq' : (c.l : ℤ) * ((T.stg 0).e : ℤ) = (c'.l : ℤ) * ((T.stg 0).e : ℤ) := by
        rw [← hwq c (hne c hc), ← hwq c' (hne c' hc')]
        exact heq
      have hepos : (0 : ℤ) < ((T.stg 0).e : ℤ) := by exact_mod_cast (T.stg 0).he
      have hl : c.l = c'.l := by
        have h := mul_right_cancel₀ (by omega : ((T.stg 0).e : ℤ) ≠ 0) heq'
        exact_mod_cast h
      exact hne' (t4_coord_ext hl (fun r => hshare c hc c' hc' r (Nat.zero_le _)))
    exact t4_w_sum_distinct (T.stg ⟨0, hk⟩) S (qterm T y 0) hS
      (fun c hc => t4_qterm_ne T y 0 c (hne c hc)) hdist
  | succ k ih =>
    intro hk S hS hne hshare
    have hkK : k < T.K := by omega
    have hkf : k < T.K + 1 := by omega
    have hk1K : k + 1 ≤ T.K := by omega
    have hΦbot : (⊥ : WithBot ℕ) < (T.stg ⟨k, hkf⟩).Φ.degree :=
      bot_lt_iff_ne_bot.mpr (fun h => (T.stg ⟨k, hkf⟩).hmonic.ne_zero (Polynomial.degree_eq_bot.mp h))
    -- the fiber data
    have hmaps : ∀ c ∈ S, c.slot ⟨k, hkf⟩ ∈ Finset.range ((S.sup fun c => c.slot ⟨k, hkf⟩) + 1) := by
      intro c hc
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun c => c.slot ⟨k, hkf⟩) hc)
    -- (1) regroup fiberwise
    have hregroup : (∑ c ∈ S, qterm T y (k + 1) c)
        = ∑ j ∈ Finset.range ((S.sup fun c => c.slot ⟨k, hkf⟩) + 1),
            (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c) * (T.stg ⟨k, hkf⟩).Φ ^ j := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun c => qterm T y (k + 1) c)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      rw [t4_qterm_succ T y k hkf c, (Finset.mem_filter.mp hc).2]
    -- (2) the fiber coefficients are development coefficients
    have hBdeg : ∀ j, (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c).degree
        < (T.stg ⟨k, hkf⟩).Φ.degree := by
      intro j
      rcases (S.filter (fun c => c.slot ⟨k, hkf⟩ = j)).eq_empty_or_nonempty with hj | hj
      · rw [hj, Finset.sum_empty, Polynomial.degree_zero]
        exact hΦbot
      · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff hΦbot).mpr ?_)
        intro c hc
        exact t4_qterm_deg T y k (le_of_lt hkK) c (hne c (Finset.mem_of_mem_filter c hc))
    have hBzero : ∀ j, (S.sup fun c => c.slot ⟨k, hkf⟩) + 1 ≤ j →
        (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c) = 0 := by
      intro j hj
      have hempty : S.filter (fun c => c.slot ⟨k, hkf⟩ = j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro c hc heq
        have := Finset.le_sup (f := fun c => c.slot ⟨k, hkf⟩) hc
        omega
      rw [hempty, Finset.sum_empty]
    have hdev : IsDevelopment (T.stg ⟨k, hkf⟩).Φ (∑ c ∈ S, qterm T y (k + 1) c)
        (fun j => ∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c)
        ((S.sup fun c => c.slot ⟨k, hkf⟩) + 1) :=
      ⟨hBdeg, hBzero, hregroup⟩
    -- (3) the IH on each nonempty fiber
    have hfiber : ∀ j : ℕ, (S.filter (fun c => c.slot ⟨k, hkf⟩ = j)).Nonempty →
        (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c) ≠ 0 ∧
        ∃ c₀ ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j),
          (T.stg ⟨k, hkf⟩).w (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j), qterm T y k c)
              = (T.stg ⟨k, hkf⟩).w (qterm T y k c₀) ∧
            ∀ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j),
              (T.stg ⟨k, hkf⟩).w (qterm T y k c₀) ≤ (T.stg ⟨k, hkf⟩).w (qterm T y k c) := by
      intro j hj
      apply ih hkf _ hj
      · intro c hc; exact hne c (Finset.mem_of_mem_filter c hc)
      · intro c hc c' hc' r hr
        rcases eq_or_lt_of_le hr with hr' | hr'
        · have hreq : r = ⟨k, hkf⟩ := Fin.ext hr'.symm
          rw [hreq, (Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hc').2]
        · exact hshare c (Finset.mem_of_mem_filter c hc) c' (Finset.mem_of_mem_filter c' hc') r hr'
    -- (4) the development sum is nonzero (Fact B against the zero development)
    have hGne : (∑ c ∈ S, qterm T y (k + 1) c) ≠ 0 := by
      intro hG0
      have hzdev : IsDevelopment (T.stg ⟨k, hkf⟩).Φ (∑ c ∈ S, qterm T y (k + 1) c)
          (fun _ => 0) 0 := by
        refine ⟨fun j => ?_, fun j _ => rfl, ?_⟩
        · rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hG0, Finset.range_zero, Finset.sum_empty]
      have hall := L0_FactB_unique (T.stg ⟨k, hkf⟩).Φ (T.stg ⟨k, hkf⟩).hmonic _ hdev hzdev
      obtain ⟨cs, hcs⟩ := hS
      have hcj : cs ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = cs.slot ⟨k, hkf⟩) :=
        Finset.mem_filter.mpr ⟨hcs, rfl⟩
      exact (hfiber _ ⟨cs, hcj⟩).1 (hall _)
    -- (5) stage-k hK1 on the development
    obtain ⟨hmin_le, j₀, hj₀N, hBj₀ne, hmeq⟩ :=
      (T.stg ⟨k, hkf⟩).hK1 _ _ _ hGne hdev
    -- (6) the vertex fiber is nonempty; take its IH minimizer
    have hSj₀ : (S.filter (fun c => c.slot ⟨k, hkf⟩ = j₀)).Nonempty := by
      rcases (S.filter (fun c => c.slot ⟨k, hkf⟩ = j₀)).eq_empty_or_nonempty with h | h
      · exact absurd (by rw [h, Finset.sum_empty]) hBj₀ne
      · exact h
    obtain ⟨_, c₀, hc₀mem, hw₀, hmin₀⟩ := hfiber j₀ hSj₀
    have hc₀S : c₀ ∈ S := Finset.mem_of_mem_filter c₀ hc₀mem
    have hslotc₀ : c₀.slot ⟨k, hkf⟩ = j₀ := (Finset.mem_filter.mp hc₀mem).2
    -- (7) the term-weight recursion at stage k
    have hterm : ∀ c ∈ S, (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c)
        = (T.stg ⟨k, hkf⟩).w (qterm T y k c)
          + (c.slot ⟨k, hkf⟩ : ℤ) * (T.stg ⟨k, hkf⟩).w (T.stg ⟨k, hkf⟩).Φ := by
      intro c hc
      rw [t4_qterm_succ T y k hkf c,
          (T.stg ⟨k, hkf⟩).hwmul _ _ (t4_qterm_ne T y k c (hne c hc))
            (pow_ne_zero _ (T.stg ⟨k, hkf⟩).hmonic.ne_zero),
          t4_w_pow (T.stg ⟨k, hkf⟩) _ (T.stg ⟨k, hkf⟩).hmonic.ne_zero]
    -- (8) stage-k value of the whole sum = the c₀ term
    have hwG_k : (T.stg ⟨k, hkf⟩).w (∑ c ∈ S, qterm T y (k + 1) c)
        = (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c₀) := by
      have h1 : (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c₀)
          = (T.stg ⟨k, hkf⟩).w (qterm T y k c₀)
            + (j₀ : ℤ) * (T.stg ⟨k, hkf⟩).w (T.stg ⟨k, hkf⟩).Φ := by
        rw [hterm c₀ hc₀S, hslotc₀]
      have hmeq' : (T.stg ⟨k, hkf⟩).w (∑ c ∈ S, qterm T y (k + 1) c)
          = (T.stg ⟨k, hkf⟩).w (∑ c ∈ S.filter (fun c => c.slot ⟨k, hkf⟩ = j₀), qterm T y k c)
            + (j₀ : ℤ) * (T.stg ⟨k, hkf⟩).w (T.stg ⟨k, hkf⟩).Φ := hmeq
      rw [hmeq', hw₀, ← h1]
    -- (9) stage-k minimality over S
    have hmin_k : ∀ c ∈ S, (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c₀)
        ≤ (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c) := by
      intro c hc
      have hcj : c ∈ S.filter (fun c' => c'.slot ⟨k, hkf⟩ = c.slot ⟨k, hkf⟩) :=
        Finset.mem_filter.mpr ⟨hc, rfl⟩
      obtain ⟨hBjne, c₁, hc₁mem, hw₁, hmin₁⟩ := hfiber _ ⟨c, hcj⟩
      have hjN : c.slot ⟨k, hkf⟩ < (S.sup fun c => c.slot ⟨k, hkf⟩) + 1 :=
        Nat.lt_succ_of_le (Finset.le_sup (f := fun c => c.slot ⟨k, hkf⟩) hc)
      have hle : (T.stg ⟨k, hkf⟩).w (∑ c' ∈ S, qterm T y (k + 1) c')
          ≤ (T.stg ⟨k, hkf⟩).w
              (∑ c' ∈ S.filter (fun c' => c'.slot ⟨k, hkf⟩ = c.slot ⟨k, hkf⟩), qterm T y k c')
            + (c.slot ⟨k, hkf⟩ : ℤ) * (T.stg ⟨k, hkf⟩).w (T.stg ⟨k, hkf⟩).Φ :=
        hmin_le _ hjN hBjne
      rw [hwG_k] at hle
      have hle2 : (T.stg ⟨k, hkf⟩).w
          (∑ c' ∈ S.filter (fun c' => c'.slot ⟨k, hkf⟩ = c.slot ⟨k, hkf⟩), qterm T y k c')
          ≤ (T.stg ⟨k, hkf⟩).w (qterm T y k c) := by
        rw [hw₁]; exact hmin₁ c hcj
      rw [hterm c hc]
      linarith
    -- (10) stretch everything to stage k+1
    have hstep : ∀ f : Polynomial ℤ_[p], f ≠ 0 → f.degree < (T.stg ⟨k + 1, hk⟩).Φ.degree →
        (T.stg ⟨k + 1, hk⟩).w f = ((T.stg ⟨k + 1, hk⟩).e : ℤ) * (T.stg ⟨k, hkf⟩).w f :=
      fun f hf hd => t4_stretch_step T k hkf hk f hf hd
    have hGdeg : (∑ c ∈ S, qterm T y (k + 1) c).degree < (T.stg ⟨k + 1, hk⟩).Φ.degree := by
      have hΦbot1 : (⊥ : WithBot ℕ) < (T.stg ⟨k + 1, hk⟩).Φ.degree :=
        bot_lt_iff_ne_bot.mpr (fun h => (T.stg ⟨k + 1, hk⟩).hmonic.ne_zero (Polynomial.degree_eq_bot.mp h))
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff hΦbot1).mpr ?_)
      intro c hc
      exact t4_qterm_deg T y (k + 1) hk1K c (hne c hc)
    have hwt : ∀ c ∈ S, (T.stg ⟨k + 1, hk⟩).w (qterm T y (k + 1) c)
        = ((T.stg ⟨k + 1, hk⟩).e : ℤ) * (T.stg ⟨k, hkf⟩).w (qterm T y (k + 1) c) :=
      fun c hc => hstep _ (t4_qterm_ne T y (k + 1) c (hne c hc))
        (t4_qterm_deg T y (k + 1) hk1K c (hne c hc))
    refine ⟨hGne, c₀, hc₀S, ?_, ?_⟩
    · rw [hstep _ hGne hGdeg, hwt c₀ hc₀S, hwG_k]
    · intro c hc
      rw [hwt c₀ hc₀S, hwt c hc]
      have hepos : (0 : ℤ) ≤ ((T.stg ⟨k + 1, hk⟩).e : ℤ) := by positivity
      exact mul_le_mul_of_nonneg_left (hmin_k c hc) hepos

/-! ## G. The tower HAS a side valuation (`T.HasSide`, constructed from the top stage) -/

private lemma t4_hasSide (T : Tower p F) : T.HasSide := by
  classical
  refine ⟨⟨fun f => if f = 0 then ⊤ else ((T.stg (Fin.last T.K)).w f : WithTop ℤ),
    if_pos rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- w_ne_top
    intro f hf
    simp [if_neg hf]
  · -- w_neg
    intro f
    by_cases hf : f = 0
    · simp [hf]
    · rw [if_neg (neg_ne_zero.mpr hf), if_neg hf, t4_w_neg _ f hf]
  · -- w_add
    intro f g
    by_cases hfg : f + g = 0
    · rw [if_pos hfg]; exact le_top
    · by_cases hf : f = 0
      · subst hf; rw [if_pos rfl, zero_add] at *; simp
      · by_cases hg : g = 0
        · subst hg; rw [add_zero] at hfg ⊢; simp
        · rw [if_neg hf, if_neg hg, if_neg hfg]
          have := (T.stg (Fin.last T.K)).hwult f g hf hg hfg
          rw [← WithTop.coe_min]
          exact_mod_cast this
  · -- w_smul
    intro c f
    by_cases hcf : Polynomial.C c * f = 0
    · rw [if_pos hcf]; exact le_top
    · have hf : f ≠ 0 := right_ne_zero_of_mul hcf
      have hc : Polynomial.C c ≠ 0 := left_ne_zero_of_mul hcf
      rw [if_neg hf, if_neg hcf]
      have hmul := (T.stg (Fin.last T.K)).hwmul _ _ hc hf
      -- constants have nonnegative top weight
      have hCdeg : (Polynomial.C c).degree < (T.stg 0).Φ.degree := by
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        rw [Polynomial.degree_eq_natDegree (T.stg 0).hmonic.ne_zero]
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (T.stg 0).hdeg
      have h0lt : (0 : ℕ) < T.K + 1 := Nat.succ_pos _
      have hw0 : 0 ≤ (T.stg ⟨0, h0lt⟩).w (Polynomial.C c) := by
        have hstg0 : T.stg ⟨0, h0lt⟩ = T.stg 0 := rfl
        rw [hstg0, (T.stg 0).hStretch _ hc hCdeg, T.base.1.1 _ hc]
        have he0 : (0 : ℤ) ≤ ((T.stg 0).e : ℤ) := by positivity
        exact mul_nonneg he0 (t4_gaussVal_nonneg _)
      have hwK : 0 ≤ (T.stg ⟨T.K, Nat.lt_succ_self T.K⟩).w (Polynomial.C c) :=
        t4_transport_nonneg T _ hc hCdeg hw0 T.K (Nat.lt_succ_self T.K)
      have hwK' : 0 ≤ (T.stg (Fin.last T.K)).w (Polynomial.C c) := hwK
      have : (T.stg (Fin.last T.K)).w f ≤ (T.stg (Fin.last T.K)).w (Polynomial.C c * f) := by
        omega
      exact_mod_cast this
  · -- w_mul
    intro f g
    by_cases hf : f = 0
    · subst hf; rw [zero_mul, if_pos rfl]; exact le_top
    · by_cases hg : g = 0
      · subst hg; rw [mul_zero, if_pos rfl]; exact le_top
      · have hfg : f * g ≠ 0 := mul_ne_zero hf hg
        rw [if_neg hf, if_neg hg, if_neg hfg]
        have := (T.stg (Fin.last T.K)).hwmul f g hf hg
        rw [← WithTop.coe_add]
        exact_mod_cast le_of_eq this.symm
  · -- w_one
    rw [if_neg (one_ne_zero : (1 : Polynomial ℤ_[p]) ≠ 0), t4_w_one]
    rfl
  · -- the agreement spec
    intro f hf
    show (if f = 0 then (⊤ : WithTop ℤ) else (((T.stg (Fin.last T.K)).w f : ℤ) : WithTop ℤ))
        = (((T.topStage).w f : ℤ) : WithTop ℤ)
    rw [if_neg hf]
    rfl

/-! ## H. Main theorem -/

theorem T4_slotMinHt {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hfin : (Function.support y).Finite) (hsupp : ∀ c, y c ≠ 0 → T.blk c = b)
    (hne : T.slotCoeff b y ≠ 0) :
    ∃ c₀ : T.Coord, y c₀ ≠ 0 ∧ T.wQ (T.slotCoeff b y) = (T.ht c₀ : WithTop ℚ) ∧
      ∀ c : T.Coord, y c ≠ 0 → T.ht c₀ ≤ T.ht c := by
  classical
  have hlast : (⟨T.K, Nat.lt_succ_self T.K⟩ : Fin (T.K + 1)) = Fin.last T.K := rfl
  have hΦlne : (T.stg (Fin.last T.K)).Φ ≠ 0 := (T.stg (Fin.last T.K)).hmonic.ne_zero
  set S : Finset T.Coord := hfin.toFinset with hSdef
  have hmemS : ∀ c, c ∈ S ↔ y c ≠ 0 := by
    intro c
    rw [hSdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  -- (I) convert `slotCoeff` into the qterm Finset sum with the shared top-slot factor out
  have hterm : ∀ c ∈ S, T.digLift (y c) * T.mono c
      = qterm T y T.K c * (T.stg (Fin.last T.K)).Φ ^ b := by
    intro c hc
    have hyc : y c ≠ 0 := (hmemS c).mp hc
    have hblk : T.blk c = b := hsupp c hyc
    have huniv : (Finset.univ.filter (fun r : Fin (T.K + 1) => r.val < T.K + 1))
        = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro r _
      exact r.isLt
    have hq1 : qterm T y (T.K + 1) c = T.digLift (y c) * T.mono c := by
      unfold qterm Tower.mono
      rw [huniv, map_pow]
    have hq2 := t4_qterm_succ T y T.K (Nat.lt_succ_self T.K) c
    rw [hlast] at hq2
    rw [← hq1, hq2]
    have hb : c.slot (Fin.last T.K) = b := hblk
    rw [hb]
  have h1 : (∑ᶠ c ∈ {c : T.Coord | T.blk c = b}, T.digLift (y c) * T.mono c)
      = ∑ c ∈ S, T.digLift (y c) * T.mono c := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.mem_coe,
      hmemS c]
    constructor
    · rintro ⟨hblk, hne0⟩
      refine ⟨?_, hne0⟩
      intro hy0
      apply hne0
      rw [hy0, t4_digLift_zero T, zero_mul]
    · rintro ⟨hy, hne0⟩
      exact ⟨hsupp c hy, hne0⟩
  have hconv : T.slotCoeff b y
      = (∑ c ∈ S, qterm T y T.K c) * (T.stg (Fin.last T.K)).Φ ^ b := by
    rw [Tower.slotCoeff, h1, Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  -- (II) the support class is nonempty and shares the top slot
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exfalso
      apply hne
      rw [hconv, h, Finset.sum_empty, zero_mul]
    · exact h
  obtain ⟨hGne, c₀, hc₀S, hwG, hmin⟩ := t4_claim T y T.K (Nat.lt_succ_self T.K) S hSne
    (fun c hc => (hmemS c).mp hc)
    (fun c hc c' hc' r hr => by
      have hrl : r = Fin.last T.K := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
      rw [hrl]
      show T.blk c = T.blk c'
      rw [hsupp c ((hmemS c).mp hc), hsupp c' ((hmemS c').mp hc')])
  rw [hlast] at hwG hmin
  -- (III) top weight of slotCoeff = min term + b·wΦ, and the per-term ht identity
  have hwtot : (T.stg (Fin.last T.K)).w (T.slotCoeff b y)
      = (T.stg (Fin.last T.K)).w (qterm T y T.K c₀)
        + (b : ℤ) * (T.stg (Fin.last T.K)).w (T.stg (Fin.last T.K)).Φ := by
    rw [hconv, (T.stg (Fin.last T.K)).hwmul _ _ hGne (pow_ne_zero _ hΦlne),
        t4_w_pow _ _ hΦlne, hwG]
  have hq_ht : ∀ c ∈ S, ((T.stg (Fin.last T.K)).w (qterm T y T.K c) : ℚ)
      + (b : ℚ) * ((T.stg (Fin.last T.K)).w (T.stg (Fin.last T.K)).Φ : ℚ)
      = (T.strTop : ℚ) * T.ht c := by
    intro c hc
    have hyc : y c ≠ 0 := (hmemS c).mp hc
    obtain ⟨hdne, hdinC, hdw⟩ := t4_digLift_spec T (y c) hyc
    have h0lt : (0 : ℕ) < T.K + 1 := Nat.succ_pos _
    have hw0 : (T.stg ⟨0, h0lt⟩).w (T.digLift (y c)) = 0 := by
      have hstg0 : T.stg ⟨0, h0lt⟩ = T.stg 0 := rfl
      rw [hstg0, (T.stg 0).hStretch _ hdne hdinC, hdw, mul_zero]
    have hwtop0 : (T.stg (Fin.last T.K)).w (T.digLift (y c)) = 0 := by
      have h := t4_transport_zero T _ hdne hdinC hw0 T.K (Nat.lt_succ_self T.K)
      rw [hlast] at h
      exact h
    have hmononz : c.MonoNZ := by
      unfold Tower.Coord.MonoNZ Tower.mono
      exact mul_ne_zero
        (by rw [Ne, Polynomial.C_eq_zero]; exact pow_ne_zero _ PadicInt.prime_p.ne_zero)
        (Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero))
    have hmono_ne : T.mono c ≠ 0 := hmononz
    have hT3 := T3_htChainWeight T c hmononz
    have hsplit : (T.stg (Fin.last T.K)).w (T.digLift (y c) * T.mono c)
        = (T.stg (Fin.last T.K)).w (T.mono c) := by
      rw [(T.stg (Fin.last T.K)).hwmul _ _ hdne hmono_ne, hwtop0, zero_add]
    have hsplit2 : (T.stg (Fin.last T.K)).w (T.digLift (y c) * T.mono c)
        = (T.stg (Fin.last T.K)).w (qterm T y T.K c)
          + (b : ℤ) * (T.stg (Fin.last T.K)).w (T.stg (Fin.last T.K)).Φ := by
      rw [hterm c hc,
          (T.stg (Fin.last T.K)).hwmul _ _ (t4_qterm_ne T y T.K c hyc) (pow_ne_zero _ hΦlne),
          t4_w_pow _ _ hΦlne]
    have hzz : (T.stg (Fin.last T.K)).w (qterm T y T.K c)
        + (b : ℤ) * (T.stg (Fin.last T.K)).w (T.stg (Fin.last T.K)).Φ
        = (T.stg (Fin.last T.K)).w (T.mono c) := by
      rw [← hsplit2, hsplit]
    have hzzq : ((T.stg (Fin.last T.K)).w (qterm T y T.K c) : ℚ)
        + (b : ℚ) * ((T.stg (Fin.last T.K)).w (T.stg (Fin.last T.K)).Φ : ℚ)
        = (((T.stg (Fin.last T.K)).w (T.mono c) : ℤ) : ℚ) := by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℚ)) hzz
    rw [hzzq, hT3]
  -- (IV) strTop is positive; ht-minimality of c₀
  have hstpos : (0 : ℚ) < (T.strTop : ℚ) := by
    have h := t4_strAux_pos T (T.K + 1)
    rw [← t4_strTop_eq T] at h
    exact_mod_cast h
  have hht_min : ∀ c ∈ S, T.ht c₀ ≤ T.ht c := by
    intro c hc
    have h₀ := hq_ht c₀ hc₀S
    have h₁ := hq_ht c hc
    have hw_le : ((T.stg (Fin.last T.K)).w (qterm T y T.K c₀) : ℚ)
        ≤ ((T.stg (Fin.last T.K)).w (qterm T y T.K c) : ℚ) := by
      exact_mod_cast hmin c hc
    have h2 : (T.strTop : ℚ) * T.ht c₀ ≤ (T.strTop : ℚ) * T.ht c := by linarith
    exact le_of_mul_le_mul_left h2 hstpos
  -- (V) convert wQ through the constructed side valuation
  have hside := t4_hasSide T
  have hsw : T.side.w (T.slotCoeff b y)
      = (((T.stg (Fin.last T.K)).w (T.slotCoeff b y) : ℤ) : WithTop ℤ) :=
    T.side_w hside hne
  have hwQ : T.wQ (T.slotCoeff b y)
      = ((((T.stg (Fin.last T.K)).w (T.slotCoeff b y) : ℚ) / (T.strTop : ℚ) : ℚ) : WithTop ℚ) := by
    rw [Tower.wQ, hsw]
    rfl
  refine ⟨c₀, (hmemS c₀).mp hc₀S, ?_, ?_⟩
  · rw [hwQ]
    have hval : (((T.stg (Fin.last T.K)).w (T.slotCoeff b y) : ℚ) / (T.strTop : ℚ) : ℚ)
        = T.ht c₀ := by
      have h₀ := hq_ht c₀ hc₀S
      have htotq : ((T.stg (Fin.last T.K)).w (T.slotCoeff b y) : ℚ)
          = (T.strTop : ℚ) * T.ht c₀ := by
        rw [hwtot]
        push_cast
        linarith
      rw [htotq]
      field_simp
    rw [hval]
  · intro c hyc
    exact hht_min c ((hmemS c).mpr hyc)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T4_slotMinHt
