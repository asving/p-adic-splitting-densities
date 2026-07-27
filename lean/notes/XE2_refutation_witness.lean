/-
XE.2 REFUTATION WITNESS (escalation prover, 2026-07-27).

CLAIM: the statement of `LeanUrat.MovesX.envelopeExp` (unit XE.2) is FALSE as stated.

Obstruction: the conclusion's quantifier order `∃ c3 c4, … ∀ p N` forces, at the FIXED
level N = 1, `frac (Undec 1) ≤ c3 · p^(−c4) → 0` as `p → ∞`.  But the nine hypotheses
degenerate at small N: with K.cd = K.cd' = K.ch = K.ch' = 1 the (X.2) progress
disjunction `cd·N − cd' ≤ dTotal ∨ ch·N − ch' ≤ maxH` is vacuous for N ≤ 1 (LHS ≤ 0),
and no other hypothesis bounds `frac (Undec 1)` below 1.

WITNESS FAMILY (n = 2): every f gets the root-only tree (Branch = Unit, hist = [],
children = ∅); threshold = 1, capDetectable, detCap = 1 (so threshold + capHB = 2 and
Undec N = univ for N < 2, ∅ for N ≥ 2); frac = the point mass at f₀ = X² + X, whose
discriminant is 1 (a unit at EVERY prime, so vdisc f₀ = 0 and f₀ ∉ discZero — making
`vdisc_le_tail` hold with room to spare).  Then frac (Undec 1) = 1 for every p, while
all nine kernel hypotheses hold.  `envelopeExp_statement_false` below derives False
from the verbatim ∀-closure of envelopeExp's statement.

This file is a NOTES artifact (not in the lake build graph).  Check with:
  cd lean && lake env lean notes/XE2_refutation_witness.lean
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX.XE2Refutation

open LeanUrat.MovesX Polynomial

set_option linter.style.longLine false
set_option linter.unusedVariables false

variable (p : ℕ) [Fact p.Prime]

/-! ## The atom: f₀ = X² + X, unit discriminant at every prime -/

noncomputable def f0 : MonicBox 2 p :=
  ⟨X ^ 2 + X, by monicity!, by compute_degree!⟩

lemma f0_discr : (f0 p).1.discr = 1 := by
  have hdeg : (X ^ 2 + X : Polynomial ℤ_[p]).degree = 2 := by compute_degree!
  show (X ^ 2 + X : Polynomial ℤ_[p]).discr = 1
  rw [discr_of_degree_eq_two hdeg]
  simp [coeff_X_pow]

lemma f0_not_discZero : f0 p ∉ discZero 2 p := by
  intro h
  have h1 : (f0 p).1.discr = 0 := h
  rw [f0_discr] at h1
  exact one_ne_zero h1

lemma f0_vdisc : vdisc (f0 p) = 0 := by
  unfold vdisc
  rw [f0_discr]
  exact PadicInt.valuation_one

/-! ## The point-mass content -/

noncomputable def frac0 (S : Set (MonicBox 2 p)) : ℚ :=
  @ite _ (f0 p ∈ S) (Classical.propDecidable _) 1 0

lemma frac0_of_mem {S : Set (MonicBox 2 p)} (h : f0 p ∈ S) : frac0 p S = 1 := if_pos h

lemma frac0_of_notMem {S : Set (MonicBox 2 p)} (h : f0 p ∉ S) : frac0 p S = 0 := if_neg h

lemma frac0_nonneg (S : Set (MonicBox 2 p)) : 0 ≤ frac0 p S := by
  unfold frac0; split <;> norm_num

lemma frac0_le_one (S : Set (MonicBox 2 p)) : frac0 p S ≤ 1 := by
  unfold frac0; split <;> norm_num

/-! ## The root-only context -/

noncomputable def ctx0 : XCtx 2 p where
  Branch _ := Unit
  hist _ := []
  wf b := ⟨fun i hi => by simp at hi, by simp⟩
  root _ := Unit.unit
  hist_root _ := rfl
  parent _ := none
  parent_hist b b' h := nomatch h
  parent_root _ := rfl
  reach b := Relation.ReflTransGen.refl
  children _ := ∅
  children_iff b c := by simp
  complete _ := True
  nsTrack _ := False
  nsDec := fun _ => instDecidableFalse
  capDetectable _ := True
  capDec := fun _ _ => instDecidableTrue
  detCap _ := 1
  threshold _ := 1
  DetectedAt _ N := 2 ≤ N
  detectBranch b hb hns N hN := by simpa using hN
  Undec N := { _f | N < 2 }
  undec_spec f N := by
    constructor
    · intro h
      have hN : ¬ (N < 2) := h
      exact ⟨inferInstance, fun b _ => by omega⟩
    · rintro ⟨-, h⟩ hf
      have h2 : 2 ≤ N := h Unit.unit rfl
      have hN : N < 2 := hf
      omega
  undec_antitone := by
    intro N M hNM f hf
    have : M < 2 := hf
    show N < 2
    omega
  nsIdx := Unit
  nsCountable := inferInstance
  nsFiber _ := ∅
  nsCover f h := by
    obtain ⟨b, -, ν, hν, -⟩ := h
    simp at hν
  frac := frac0 p
  frac_univ := frac0_of_mem p (Set.mem_univ _)
  frac_nonneg := frac0_nonneg p
  frac_mono := by
    intro s t hst
    by_cases h : f0 p ∈ s
    · rw [frac0_of_mem p h, frac0_of_mem p (hst h)]
    · rw [frac0_of_notMem p h]; exact frac0_nonneg p t
  frac_union_le := by
    intro s t
    by_cases hs : f0 p ∈ s
    · rw [frac0_of_mem p (Set.mem_union_left _ hs), frac0_of_mem p hs]
      have := frac0_nonneg p t; linarith
    · by_cases ht : f0 p ∈ t
      · rw [frac0_of_mem p (Set.mem_union_right _ ht), frac0_of_mem p ht]
        have := frac0_nonneg p s; linarith
      · rw [frac0_of_notMem p (fun h => h.elim hs ht), frac0_of_notMem p hs,
          frac0_of_notMem p ht]
        norm_num
  frac_iUnion_null := by
    intro s h
    apply frac0_of_notMem
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    have h1 := h i
    rw [frac0_of_mem p hi] at h1
    exact one_ne_zero h1
  frac_inter_tendsto := by
    have h0 : frac0 p (⋂ N, { _f : MonicBox 2 p | N < 2 }) = 0 :=
      frac0_of_notMem p (fun hmem => by simpa using Set.mem_iInter.mp hmem 2)
    rw [h0]
    apply tendsto_atTop_of_eventually_const (i₀ := 2)
    intro N hN
    exact frac0_of_notMem p (by simp; omega)
  vdisc_le_tail := by
    intro D
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · -- D = 0: LHS ≤ 1 ≤ tailCount p 2 0 / p^0
      have hcard : 0 < tailCount p 2 0 := by
        unfold tailCount
        haveI hsub : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
        haveI : NeZero (p ^ 0) := ⟨by simp⟩
        haveI : Nonempty {a : Fin 2 → ZMod (p ^ 0) // (polyOfCoeffs _ 2 a).discr = 0} :=
          ⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
        exact Nat.card_pos
      have h1 : (1 : ℚ) ≤ (tailCount p 2 0 : ℚ) := by exact_mod_cast hcard
      calc frac0 p _ ≤ 1 := frac0_le_one p _
        _ ≤ (tailCount p 2 0 : ℚ) / (p : ℚ) ^ (2 * 0) := by
            rw [Nat.mul_zero, pow_zero, div_one]; exact h1
    · -- D ≥ 1: the atom misses the event
      have hnot : f0 p ∉ {f : MonicBox 2 p | D ≤ vdisc f ∨ f ∈ discZero 2 p} := by
        intro hmem
        rcases hmem with h | h
        · rw [f0_vdisc] at h; omega
        · exact f0_not_discZero p h
      rw [frac0_of_notMem p hnot]
      positivity

/-! ## The trivial GMN index -/

def gmn0 : GMNIndex 2 p where
  ind _ := 0
  inStratum _ H := H = []
  p2 f hf := Nat.zero_le _

/-! ## The family and the constants -/

noncomputable def Xce : XFamily 2 where
  ctx p inst := @ctx0 p inst
  gmn p inst := @gmn0 p inst
  gmnLink p inst f b := rfl

def Kce : XConsts 2 where
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

/-! ## The nine hypotheses -/

theorem PRce : X2ProgressP 2 Xce Kce := by
  intro p _ f b N hb hN
  left
  have h2 : N < 2 := hN
  have hN1 : (N : ℚ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h2
  show (1 : ℚ) * N - 1 ≤ ((0 : ℕ) : ℚ)
  push_cast
  linarith

theorem BRce : X2BridgeP 2 Xce := by
  intro p _ N
  constructor
  · intro f hf
    have hN : N < 2 := hf
    exact Set.mem_union_right _
      ⟨Unit.unit, rfl, fun ν hν => not_false, hN⟩
  · apply frac0_of_notMem
    rintro ⟨hU, hno⟩
    have hN : N < 2 := hU
    exact hno ⟨Unit.unit, rfl, fun ν hν => not_false, hN⟩

theorem AFce : X2AffP 2 Xce Kce := by
  intro p _ f b hb
  show ((1 : ℕ) : ℚ) ≤ 1 + (0 : ℚ) * sumH []
  norm_num

theorem CPce : X2CapP 2 Xce Kce := by
  intro p _ f b hb hcap
  show ((1 : ℕ) : ℚ) ≤ (1 : ℚ) * (1 + sumH [])
  simp [sumH]

theorem ALce : X1aAlignP 2 Xce ⟨true, false⟩ := by
  intro p _ f H hd hs
  have hH : H = [] := hs
  subst hH
  show dCert ⟨true, false⟩ [] ≤ 0
  simp [dCert]

theorem WCce : WeightChargeFullP 2 Xce Kce := by
  intro p _ f H hd hs
  have hH : H = [] := hs
  subst hH
  show countPop [] .recT1 + countPop [] .t4 ≤ 0 * vdisc f
  simp [countPop]

theorem TLce : X2TailsP 2 Xce Kce := by
  intro p _ hstar
  have hempty : f0 p ∉ TallEvent (Xce.ctx p) hstar := by
    rintro ⟨b, ν, hν, -⟩
    have h' : ν ∈ ([] : XHistory 2) := hν
    simp at h'
  have h0 : (Xce.ctx p).frac (TallEvent (Xce.ctx p) hstar) = 0 :=
    frac0_of_notMem p hempty
  rw [h0]
  have hCT : Kce.CT = 1 := rfl
  rw [hCT]
  push_cast
  positivity

theorem NSce : NsNullP 2 Xce := by
  intro p _ i
  exact frac0_of_notMem p (fun h => h)

theorem Rce : X3aRouteP 2 Xce Kce := Or.inr ⟨ALce, WCce⟩

/-! ## The conclusion fails: frac (Undec 1) = 1 for every p -/

theorem conclusion_false :
    ¬ ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((Xce.ctx p).frac ((Xce.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N)) := by
  rintro ⟨c3, c4, hc3, hc4, H⟩
  -- pick a prime p with c3 + 1 ≤ p^c4
  have hev : ∀ᶠ x : ℝ in Filter.atTop, c3 + 1 ≤ x ^ c4 :=
    (tendsto_rpow_atTop hc4).eventually_ge_atTop (c3 + 1)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨q, hq₀, hq⟩ := Nat.exists_infinite_primes (max ⌈x₀⌉₊ 1)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqle : x₀ ≤ (q : ℝ) := by
    calc x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
      _ ≤ (q : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hq₀
  have hcp : c3 + 1 ≤ (q : ℝ) ^ c4 := hx₀ (q : ℝ) hqle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  -- frac (Undec 1) = 1
  have h1 : ((Xce.ctx q).frac ((Xce.ctx q).Undec 1) : ℚ) = 1 :=
    frac0_of_mem q (show (1 : ℕ) < 2 by omega)
  have h2 := H q 1
  rw [h1] at h2
  -- h2 : (1 : ℝ) ≤ c3 * q^(−(c4 · 1))
  have h3 : (1 : ℝ) ≤ c3 * (q : ℝ) ^ (-c4) := by
    have hcast : (((1 : ℚ) : ℝ)) = 1 := by norm_num
    rw [hcast] at h2
    simpa using h2
  rw [Real.rpow_neg hqpos.le, ← div_eq_mul_inv] at h3
  have hpow : (0 : ℝ) < (q : ℝ) ^ c4 := Real.rpow_pos_of_pos hqpos _
  have h4 : (q : ℝ) ^ c4 ≤ c3 := by
    have := (le_div_iff₀ hpow).mp h3
    linarith
  linarith

/-! ## envelopeExp's statement, refuted verbatim -/

theorem envelopeExp_statement_false :
    ¬ (∀ (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n),
        X2ProgressP n X K → X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N))) := by
  intro h
  exact conclusion_false
    (h 2 le_rfl Xce Kce PRce BRce AFce CPce ALce WCce TLce NSce Rce)

end LeanUrat.MovesX.XE2Refutation

#print axioms LeanUrat.MovesX.XE2Refutation.envelopeExp_statement_false
#print axioms LeanUrat.MovesX.XE2Refutation.conclusion_false
