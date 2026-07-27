/-
XE.3 REFUTATION CERTIFICATE — 2026-07-27 (escalation prover, Fable)

This file machine-checks that the statement of `LeanUrat.MovesX.envelopeSqrt`
(unit XE.3, lean/LeanUrat/MovesX/XE3.lean) is FALSE as stated, confirming the
first prover's obstruction report.

Shape of the failure: the conclusion fixes c3', c4' > 0 BEFORE p, so at N = 1 it
forces frac(Undec 1) ≤ c3'·p^(−c4') → 0 as p → ∞ over primes. No hypothesis
lower-bounds detection speed p-uniformly at small N: the countermodel below
(one-node trees, threshold 1, cap 1, DetectedAt b N := 2 ≤ N, Dirac content at
the unit-discriminant point X² + X) satisfies ALL EIGHT tags of XE.3 verbatim,
yet frac(Undec 1) = 1 for every prime p.

The `example : XE3Statement := envelopeSqrt` line certifies that `XE3Statement`
is EXACTLY the Pi-type of the target theorem; `envelopeSqrt_statement_is_false`
then refutes it. Hence the `sorry` in XE3.lean can never be filled. The
countermodel ALSO satisfies the linear progress tag `X2ProgressP` (`PRp` below),
so the same instance refutes XE.2's `envelopeExp` statement as well
(`envelopeExp_statement_is_false`, with its own statement-match certificate).

NOT part of the corpus build. Verify with:
  cd lean && lake env lean notes/XE3_REFUTATION_2026-07-27.lean
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XE2
import LeanUrat.MovesX.XE3

namespace LeanUrat.MovesX
namespace XE3Refutation

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Polynomial

/-- The exact Pi-type of XE.3's `envelopeSqrt` (verbatim copy of the statement). -/
abbrev XE3Statement : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (BR : X2BridgeP n X) (AF : X2AffP n X K) (CP : X2CapP n X K)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (TL : X2TailsP n X K) (NS : NsNullP n X) (R : X3aRouteP n X K),
    ∃ c3' c4' : ℝ, 0 < c3' ∧ 0 < c4' ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3' * (p : ℝ) ^ (-(c4' * Real.sqrt N))

/-- STATEMENT-MATCH CERTIFICATE: the (currently `sorry`-bodied) `envelopeSqrt`
has exactly the type `XE3Statement`. This elaborates iff the types agree. -/
example : XE3Statement := envelopeSqrt

/-! ## The Dirac content -/

open Classical in
/-- Dirac mass at `x`, as a ℚ-valued content on sets. -/
noncomputable def dirac {α : Type} (x : α) (s : Set α) : ℚ :=
  if x ∈ s then 1 else 0

lemma dirac_of_mem {α : Type} {x : α} {s : Set α} (h : x ∈ s) : dirac x s = 1 :=
  if_pos h

lemma dirac_of_notMem {α : Type} {x : α} {s : Set α} (h : x ∉ s) : dirac x s = 0 :=
  if_neg h

lemma dirac_nonneg {α : Type} (x : α) (s : Set α) : 0 ≤ dirac x s := by
  unfold dirac; split <;> norm_num

lemma dirac_eq_zero_iff {α : Type} {x : α} {s : Set α} : dirac x s = 0 ↔ x ∉ s := by
  unfold dirac; split <;> simp_all

/-! ## The Dirac point: X² + X ∈ MonicBox 2 p, unit discriminant -/

variable (p : ℕ) [Fact p.Prime]

lemma degree_XsqX : ((X : Polynomial ℤ_[p]) ^ 2 + X).degree = 2 := by
  have h : (X : Polynomial ℤ_[p]).degree < ((X : Polynomial ℤ_[p]) ^ 2).degree := by
    rw [degree_X, degree_X_pow]
    exact_mod_cast Nat.one_lt_two
  rw [degree_add_eq_left_of_degree_lt h]
  exact_mod_cast degree_X_pow 2

noncomputable def f0 : MonicBox 2 p :=
  ⟨X ^ 2 + X,
    monic_X_pow_add (by rw [degree_X]; exact_mod_cast Nat.one_lt_two),
    natDegree_eq_of_degree_eq_some (degree_XsqX p)⟩

lemma discr_XsqX : ((X : Polynomial ℤ_[p]) ^ 2 + X).discr = 1 := by
  rw [discr_of_degree_eq_two (degree_XsqX p)]
  simp [coeff_X_pow, coeff_X]

lemma vdisc_f0 : vdisc (f0 p) = 0 := by
  unfold vdisc
  have h : ((f0 p).1).discr = 1 := discr_XsqX p
  rw [h, PadicInt.valuation_one]

lemma f0_notMem_discZero : f0 p ∉ discZero 2 p := by
  intro h
  have h' : ((f0 p).1).discr = 0 := h
  have h'' : ((X : Polynomial ℤ_[p]) ^ 2 + X).discr = 0 := h'
  rw [discr_XsqX p] at h''
  exact one_ne_zero h''

/-! ## The degenerate context: one-node trees, threshold 1, cap 1,
`DetectedAt b N := 2 ≤ N`, Dirac content at `f0`. -/

noncomputable def ctxD : XCtx 2 p where
  Branch _ := PUnit
  hist _ := []
  wf _ := ⟨fun i _ => i.elim0, by simp⟩
  root _ := PUnit.unit
  hist_root _ := rfl
  parent _ := none
  parent_hist := fun _ _ h => nomatch h
  parent_root _ := rfl
  reach := fun b => by cases b; exact Relation.ReflTransGen.refl
  children _ := ∅
  children_iff := fun b c => by simp
  complete _ := False
  nsTrack _ := False
  nsDec := fun _ => inferInstanceAs (Decidable False)
  capDetectable _ := True
  capDec := fun _ _ => inferInstanceAs (Decidable True)
  detCap _ := 1
  threshold _ := 1
  DetectedAt _ N := 2 ≤ N
  detectBranch := fun b _ _ N hN => by
    have h : 1 + 1 ≤ N := by simpa using hN
    omega
  Undec N := if N < 2 then Set.univ else ∅
  undec_spec := by
    intro f N
    by_cases h2 : N < 2
    · rw [if_pos h2]
      exact iff_of_false (fun h => h (Set.mem_univ f))
        (fun ⟨_, hall⟩ => by have := hall PUnit.unit rfl; omega)
    · rw [if_neg h2]
      exact iff_of_true (Set.notMem_empty f) ⟨inferInstance, fun _ _ => by omega⟩
  undec_antitone := by
    intro N M hNM f hf
    have hf' : f ∈ (if M < 2 then (Set.univ : Set (MonicBox 2 p)) else ∅) := hf
    show f ∈ (if N < 2 then (Set.univ : Set (MonicBox 2 p)) else ∅)
    by_cases hN2 : N < 2
    · rw [if_pos hN2]; exact Set.mem_univ f
    · rw [if_neg (by omega : ¬ M < 2)] at hf'
      exact absurd hf' (Set.notMem_empty f)
  nsIdx := PUnit
  nsCountable := inferInstance
  nsFiber _ := ∅
  nsCover := by
    intro f h
    obtain ⟨b, -, ν, hν, -⟩ := h
    exact absurd (show ν ∈ ([] : List (XNode 2)) from hν) (by simp)
  frac := dirac (f0 p)
  frac_univ := dirac_of_mem (Set.mem_univ _)
  frac_nonneg := fun s => dirac_nonneg _ s
  frac_mono := by
    intro s t hst
    by_cases h : f0 p ∈ s
    · rw [dirac_of_mem h, dirac_of_mem (hst h)]
    · rw [dirac_of_notMem h]; exact dirac_nonneg _ t
  frac_union_le := by
    intro s t
    by_cases hs : f0 p ∈ s
    · rw [dirac_of_mem hs, dirac_of_mem (Set.mem_union_left t hs)]
      have := dirac_nonneg (f0 p) t; linarith
    · by_cases ht : f0 p ∈ t
      · rw [dirac_of_mem ht, dirac_of_mem (Set.mem_union_right s ht), dirac_of_notMem hs]
        linarith
      · rw [dirac_of_notMem hs, dirac_of_notMem ht,
          dirac_of_notMem (fun h => ((Set.mem_union _ _ _).mp h).elim hs ht)]
        norm_num
  frac_iUnion_null := by
    intro s hs
    apply dirac_of_notMem
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact dirac_eq_zero_iff.mp (hs i) hi
  frac_inter_tendsto := by
    have hInter : (⋂ N, (if N < 2 then (Set.univ : Set (MonicBox 2 p)) else ∅)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro f hf
      have h2 := Set.mem_iInter.mp hf 2
      rw [if_neg (by omega)] at h2
      exact Set.notMem_empty f h2
    rw [hInter, dirac_of_notMem (Set.notMem_empty _)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    rw [if_neg (by omega), dirac_of_notMem (Set.notMem_empty _)]
  vdisc_le_tail := by
    intro D
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [dirac_of_mem (Set.mem_setOf_eq ▸ Or.inl (Nat.zero_le _))]
      have hpos : 0 < tailCount p 2 0 := by
        unfold tailCount
        haveI : Subsingleton (ZMod (p ^ 0)) := by
          rw [pow_zero]; infer_instance
        haveI : Nonempty {a : Fin 2 → ZMod (p ^ 0) //
            (polyOfCoeffs (ZMod (p ^ 0)) 2 a).discr = 0} :=
          ⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
        exact Nat.card_pos
      have h1 : (1 : ℚ) ≤ (tailCount p 2 0 : ℚ) := by exact_mod_cast hpos
      calc (1 : ℚ) ≤ (tailCount p 2 0 : ℚ) := h1
        _ = (tailCount p 2 0 : ℚ) / (p : ℚ) ^ (2 * 0) := by norm_num
    · have hnot : f0 p ∉ {f : MonicBox 2 p | D ≤ vdisc f ∨ f ∈ discZero 2 p} := by
        intro h
        simp only [Set.mem_setOf_eq] at h
        rcases h with h | h
        · rw [vdisc_f0] at h; omega
        · exact f0_notMem_discZero p h
      rw [dirac_of_notMem hnot]
      positivity

/-! ## Rfl-lemmas for the context fields -/

@[simp] lemma ctxD_hist {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    (ctxD p).hist b = [] := rfl

@[simp] lemma ctxD_threshold {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    (ctxD p).threshold b = 1 := rfl

@[simp] lemma ctxD_children {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    (ctxD p).children b = ∅ := rfl

@[simp] lemma ctxD_Undec (N : ℕ) :
    (ctxD p).Undec N = if N < 2 then Set.univ else ∅ := rfl

@[simp] lemma ctxD_frac (s : Set (MonicBox 2 p)) :
    (ctxD p).frac s = dirac (f0 p) s := rfl

@[simp] lemma ctxD_nsFiber (i : (ctxD p).nsIdx) : (ctxD p).nsFiber i = ∅ := rfl

@[simp] lemma capHB_ctxD {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    capHB (ctxD p) b = 1 :=
  if_pos trivial

@[simp] lemma isLeafB_ctxD {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    IsLeafB (ctxD p) b := rfl

@[simp] lemma nsFreeB_ctxD {f : MonicBox 2 p} (b : (ctxD p).Branch f) :
    NsFreeB (ctxD p) b := by
  intro ν hν
  exact absurd (show ν ∈ ([] : List (XNode 2)) from hν) (by simp)

@[simp] lemma tallEvent_ctxD (hstar : ℕ) : TallEvent (ctxD p) hstar = ∅ := by
  ext f
  simp only [TallEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨b, ν, hν, -⟩
  exact absurd (show ν ∈ ([] : List (XNode 2)) from hν) (by simp)

/-! ## The GMN index and the family -/

noncomputable def gmnD : GMNIndex 2 p where
  ind _ := 0
  inStratum _ H := H = []
  p2 := fun f _ => Nat.zero_le _

noncomputable def famD : XFamily 2 where
  ctx := fun p _ => ctxD p
  gmn := fun p _ => gmnD p
  gmnLink := fun p _ f b => rfl

@[simp] lemma famD_ctx (p : ℕ) [Fact p.Prime] : famD.ctx p = ctxD p := rfl

@[simp] lemma famD_gmn (p : ℕ) [Fact p.Prime] : famD.gmn p = gmnD p := rfl

@[simp] lemma gmnD_inStratum (f : MonicBox 2 p) (H : XHistory 2) :
    (gmnD p).inStratum f H ↔ H = [] := Iff.rfl

/-! ## The constants -/

def K2 : XConsts 2 where
  s := 0
  c0 := 0
  ccap := 1
  c0nonneg := le_refl 0
  ccapnonneg := zero_le_one
  cd := 1
  cd' := 1
  ch := 1
  ch' := 1
  cdpos := one_pos
  chpos := one_pos
  CT := 1
  cT := 1
  CTpos := one_pos
  cTpos := one_pos

@[simp] lemma K2_s : K2.s = 0 := rfl
@[simp] lemma K2_c0 : K2.c0 = 0 := rfl
@[simp] lemma K2_ccap : K2.ccap = 1 := rfl
@[simp] lemma K2_CT : K2.CT = 1 := rfl
@[simp] lemma K2_cT : K2.cT = 1 := rfl

/-! ## All eight hypothesis tags hold (plus PR, refuting XE.2 as well) -/

lemma AFp : X2AffP 2 famD K2 := by
  intro p _ f b hb
  simp [sumH]

lemma CPp : X2CapP 2 famD K2 := by
  intro p _ f b hb hdet
  show ((1 : ℕ) : ℚ) ≤ 1 * (1 + (sumH ((ctxD p).hist b) : ℚ))
  simp [sumH]

lemma ALp : X1aAlignP 2 famD ⟨true, false⟩ := by
  intro p _ f H hd hs
  have hH : H = [] := hs
  subst hH
  simp [dCert]

lemma WCp : WeightChargeFullP 2 famD K2 := by
  intro p _ f H hd hs
  have hH : H = [] := hs
  subst hH
  simp [countPop]

lemma TLp : X2TailsP 2 famD K2 := by
  intro p _ hstar
  simp only [famD_ctx, ctxD_frac, tallEvent_ctxD, K2_CT, K2_cT,
    dirac_of_notMem (Set.notMem_empty _)]
  push_cast
  positivity

lemma NSp : NsNullP 2 famD := by
  intro p _ i
  simp only [famD_ctx, ctxD_nsFiber, ctxD_frac]
  exact dirac_of_notMem (Set.notMem_empty _)

lemma BRp : X2BridgeP 2 famD := by
  intro p _ N
  constructor
  · -- clause 1: for N < 2 every f carries the witness branch; for N ≥ 2, Undec N = ∅
    intro f hf
    by_cases h2 : N < 2
    · refine Set.mem_union_right _ ?_
      exact ⟨PUnit.unit, isLeafB_ctxD p _, nsFreeB_ctxD p _, by simp; omega⟩
    · exfalso
      have hf' : f ∈ (if N < 2 then (Set.univ : Set (MonicBox 2 p)) else ∅) := hf
      rw [if_neg h2] at hf'
      exact Set.notMem_empty f hf'
  · -- clause 2: the no-witness piece is empty (witness for N < 2; Undec N = ∅ for N ≥ 2)
    have hempty : {f : MonicBox 2 p | f ∈ (famD.ctx p).Undec N ∧
        ¬ ∃ b : (famD.ctx p).Branch f,
            IsLeafB (famD.ctx p) b ∧ NsFreeB (famD.ctx p) b ∧
              N < (famD.ctx p).threshold b + capHB (famD.ctx p) b} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hf hno
      by_cases h2 : N < 2
      · exact hno ⟨PUnit.unit, isLeafB_ctxD p _, nsFreeB_ctxD p _, by simp; omega⟩
      · have hf' : f ∈ (if N < 2 then (Set.univ : Set (MonicBox 2 p)) else ∅) := hf
        rw [if_neg h2] at hf'
        exact Set.notMem_empty f hf'
    rw [hempty]
    exact dirac_of_notMem (Set.notMem_empty _)

lemma Rp : X3aRouteP 2 famD K2 := Or.inr ⟨ALp, WCp⟩

/-- The linear progress tag ALSO holds in the countermodel (so the countermodel
refutes XE.2's `envelopeExp` as well): for a fourth-piece branch with
`N < threshold + capHB = 2`, `cd·N − cd' = N − 1 ≤ 0 ≤ d_total` at N ≤ 1. -/
lemma PRp : X2ProgressP 2 famD K2 := by
  intro p _ f b N hb hN
  left
  have h2 : N < 2 := by
    have := hN
    simp only [famD_ctx, ctxD_threshold, capHB_ctxD] at this
    omega
  show (1 : ℚ) * N - 1 ≤ (dTotal ((ctxD p).hist b) : ℚ)
  have hd : (0 : ℚ) ≤ (dTotal ((ctxD p).hist b) : ℚ) := by positivity
  have hN1 : (N : ℚ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h2
  linarith

/-! ## The refutation -/

theorem envelopeSqrt_statement_is_false : ¬ XE3Statement := by
  intro h
  obtain ⟨c3, c4, hc3, hc4, hbound⟩ :=
    h 2 le_rfl famD K2 BRp AFp CPp ALp WCp TLp NSp Rp
  -- pick a prime p with c3^(1/c4) < p
  set x : ℝ := c3 ^ (c4⁻¹ : ℝ) with hxdef
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max 2 (⌈x⌉₊ + 1))
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : 2 ≤ p := le_trans (le_max_left _ _) hp_ge
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  -- the bound at N = 1
  have h1 := hbound p 1
  -- LHS: frac (Undec 1) = 1
  have hfrac : (famD.ctx p).frac ((famD.ctx p).Undec 1) = 1 := by
    simp only [famD_ctx, ctxD_Undec]
    rw [if_pos (by omega : (1 : ℕ) < 2)]
    exact dirac_of_mem (Set.mem_univ _)
  rw [hfrac] at h1
  have hsqrt : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_one, Real.sqrt_one]
  rw [hsqrt, mul_one] at h1
  push_cast at h1
  -- h1 : (1 : ℝ) ≤ c3 * p ^ (−c4)
  -- but p > x = c3^(1/c4) forces c3 < p^c4, i.e. c3 * p^(−c4) < 1
  have hpx : x < (p : ℝ) := by
    have hge : (⌈x⌉₊ + 1 : ℕ) ≤ p := le_trans (le_max_right _ _) hp_ge
    have hcast : ((⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge
    have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    push_cast at hcast
    linarith
  have hxnn : 0 ≤ x := Real.rpow_nonneg (le_of_lt hc3) _
  have hplt : c3 < (p : ℝ) ^ (c4 : ℝ) := by
    have hlt := Real.rpow_lt_rpow hxnn hpx hc4
    rwa [hxdef, Real.rpow_inv_rpow (le_of_lt hc3) (ne_of_gt hc4)] at hlt
  have hppos : (0 : ℝ) < (p : ℝ) ^ (c4 : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [Real.rpow_neg (le_of_lt hp0)] at h1
  have hlt1 : c3 * ((p : ℝ) ^ (c4 : ℝ))⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ hppos, one_mul]
    exact hplt
  linarith

/-- The exact Pi-type of XE.2's `envelopeExp` (verbatim copy of the statement). -/
abbrev XE2Statement : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (PR : X2ProgressP n X K) (BR : X2BridgeP n X) (AF : X2AffP n X K) (CP : X2CapP n X K)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (TL : X2TailsP n X K) (NS : NsNullP n X) (R : X3aRouteP n X K),
    ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N))

/-- STATEMENT-MATCH CERTIFICATE for XE.2's `envelopeExp`. -/
example : XE2Statement := envelopeExp

/-- Same countermodel, aimed at XE.2's `envelopeExp` statement (the exponential
envelope WITH the progress tag PR): also false. -/
theorem envelopeExp_statement_is_false : ¬ XE2Statement := by
  intro h
  obtain ⟨c3, c4, hc3, hc4, hbound⟩ :=
    h 2 le_rfl famD K2 PRp BRp AFp CPp ALp WCp TLp NSp Rp
  set x : ℝ := c3 ^ (c4⁻¹ : ℝ) with hxdef
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max 2 (⌈x⌉₊ + 1))
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : 2 ≤ p := le_trans (le_max_left _ _) hp_ge
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have h1 := hbound p 1
  have hfrac : (famD.ctx p).frac ((famD.ctx p).Undec 1) = 1 := by
    simp only [famD_ctx, ctxD_Undec]
    rw [if_pos (by omega : (1 : ℕ) < 2)]
    exact dirac_of_mem (Set.mem_univ _)
  rw [hfrac] at h1
  rw [Nat.cast_one, mul_one] at h1
  push_cast at h1
  have hpx : x < (p : ℝ) := by
    have hge : (⌈x⌉₊ + 1 : ℕ) ≤ p := le_trans (le_max_right _ _) hp_ge
    have hcast : ((⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge
    have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    push_cast at hcast
    linarith
  have hxnn : 0 ≤ x := Real.rpow_nonneg (le_of_lt hc3) _
  have hplt : c3 < (p : ℝ) ^ (c4 : ℝ) := by
    have hlt := Real.rpow_lt_rpow hxnn hpx hc4
    rwa [hxdef, Real.rpow_inv_rpow (le_of_lt hc3) (ne_of_gt hc4)] at hlt
  have hppos : (0 : ℝ) < (p : ℝ) ^ (c4 : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [Real.rpow_neg (le_of_lt hp0)] at h1
  have hlt1 : c3 * ((p : ℝ) ^ (c4 : ℝ))⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ hppos, one_mul]
    exact hplt
  linarith

/- Axiom audit: both refutations must show ONLY core axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular no `sorryAx`. -/
#print axioms envelopeSqrt_statement_is_false
#print axioms envelopeExp_statement_is_false

end XE3Refutation
end LeanUrat.MovesX
