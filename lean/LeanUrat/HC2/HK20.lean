/-
Unit HK-20  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-20.

INFORMAL STATEMENT (blueprint): "SideReads at read 1 (terminal): the Φ̂-development
(0, 2, 1) — clause (i)/(ii) at the recorded side; (iii) anchor of σ₁.R f (single-side
read — the ⚠ (iii) seam is FAITHFUL here); (iv) terminal `LandingKey ν₁ Φtop`
(existential Φnext — the last-read freedom); (v)/(vi) at ν₁ (vi's development is in
Φtop; concrete)."  deps: HK-16, HK-18.

E-PHASE RESOLUTIONS (recorded; inherited from HK-18):
* The development is (16, 2, 1), not "(0, 2, 1)" — HK-18 resolution R-1 (the primary
  quartic has no coherent read 1; the blueprint's own "minimal variant" branch is
  taken: fgate = Φ̂² + 2·Φ̂ + 16, adjacent side slots 0–1 at the steep pair (1, 3),
  γ₁ = 4, slot 2 strictly above at 6).
* σ₁ (HK-15, not on disk) is a parameter; its laws enter through the HK-16 hypothesis
  pack (htc : the transition record — child_key/child_wPrev/child_slotmin/…; hpin :
  the D.8 vertex pin, supplying the mfun ≡ 0 digit scalars clause (ii) reads; hw :
  the childW tie, computing σ₁.w on the concrete slots). hΦ := htc.base.child_key at
  the P-phase re-bind; here it is bound separately because `ν₁gate` consumes it.
* RATIFIED RE-KEY (2026-07-30): the pack's parent stage is `bStageP` (HK-13's base-pin
  re-dress), NOT the literal `U31.bStage` — `StageCoreL U31.bStage` is refutable
  (`reps = []` kills `reps_nonempty`/`p_is_rep`; `wPrev = bw`, `bw X = 1` kills
  `prevIaug`), and the pack must match HK-16's re-keyed conclusion conjuncts verbatim
  (they are BYTE-COPIES — an un-re-keyed pack would be undischargeable). w/R/Φ/(e,h,s,t)
  are byte-identical under the re-dress, so all recorded slot data are unchanged.
  Record: `HK13_bStageCoreP1a.lean` module header.
* Blueprint MANDATORY split rule (>100 proof lines ⇒ named seams): pre-executed —
  each SideReads conjunct is its own named declaration; (iv)+(vi) are ONE declaration
  because both read the SAME existential Φtop (the SideReads Φnext parameter: the
  last-read freedom is a single designation, not two).

DATA (hand-verified): child weights σ₁.w(C 16) = 4, σ₁.w(C 2) = 1, σ₁.w(1) = 0 (childW
at (1,3) over bw); side functional 1·w + j·3 = (4, 4, 6) — γ₁ = 4 exactly at the
stride slots 0, 1 (= s0 + k, k ≤ wSide/e = 1), digits pat ≡ 1 at position
T(−σ₁.t·σ₁.wPrev B) = T 0 (σ₁.t = 0 via Stage.he1t at σ₁.e = 1). Anchor: σ₁.R fgate
= R(C 16) + R(C 2)·R(Φ̂) = 1 + z (hRPhi: R(Φ̂) = T s₁ = z) = T 0·toLaurent(Ranch₁),
a₁ = 0, ord_{z−1}(z + 1) = 1 = μ₁ (char 2). Landing: ν₁ is recentering-species (HK-18
resolution R-2) — LandingKey's recentering leg wants the recorded lift to realize the
center: lift = polOM's choice on `RecenterLiftSpec ν₁` (nonempty: C 8 has σ₁.w = 3 =
σ₁.w Φ̂ and digit 1 = center₁ at position 0), Φtop := Φ̂ − ν₁.lift. Vertex read-off:
in Φtop-coordinates fgate = Φtop² + (2ℓ + 2)Φtop + (ℓ² + 2ℓ + 16) at ℓ := ν₁.lift, so
the μ₁ = 1 slot digit is digPrime(2ℓ + 2) = digPrime(C 2) = 1 (w(2ℓ) = 4 > 1 = w(C 2))
= vtx ν₁ (a = 0, m̂ = 0, vtxPoly = 1).

PROOF SKETCH (P-phase): clause (i)/(ii) by interval_cases over the three slots with hw
+ hpin (digit scalars) + he1t (t = 0); (iii) by the residual computation above through
htc.base + hpin + hRPhi-from-htc (the S5′ key residual is `child_dig_frame`/VertexPin
content at B := Φ̂? NO — R(Φ̂) = T s' is `ChildResData.hRPhi`, an HK-15 pin: if the
HK-16 pack under-supplies it, SURFACE per the K-4 seam rule — expected residue, noted);
(iv)+(vi) via polOM choice + Fact-B uniqueness in Φtop (monic quadratic);
(v) lift leg by `CanonPolicy.blind` (rfl-grade), canonRoot leg: unique root 1 of
z − 1. Difficulty hard-fable ~120 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK18
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.Moves.ResVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace HK20

open HK18

/-- The child (frame-1, key Φ̂ = fq) development of fgate: slot coefficients
(C 16, C 2, 1), window length 3 (HK-18 resolution R-1's corrected display of the
blueprint's "(0, 2, 1)"). -/
noncomputable def Bdev1 : ℕ → Polynomial ℤ_[2] :=
  fun j =>
    if j = 0 then Polynomial.C 16
    else if j = 1 then Polynomial.C 2
    else if j = 2 then 1
    else 0

/-! ### P-phase local toolkit (fq-coefficient facts; the child-stage restriction laws
`w_coeff`/`R_coeff` extract σ₁'s values on concrete coefficients from the HK-16 pack —
`child_slotmin` computes weights, the D.8 vertex pin computes residual digits). -/

private lemma fq_deg : U31.fq.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
  rfl

private lemma inC_fq_C (b : ℤ_[2]) : inC U31.fq (Polynomial.C b) := by
  show (Polynomial.C b).degree < U31.fq.degree
  rw [fq_deg]
  exact lt_of_le_of_lt degree_C_le (by norm_num)

private lemma bw_C16 : U31.bw (Polynomial.C (16 : ℤ_[2])) = 4 := by
  have h : (16 : ℤ_[2]) = 2 ^ 4 * 1 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul HK13R.ρ_one_ne]
  norm_num

private lemma bw_C8 : U31.bw (Polynomial.C (8 : ℤ_[2])) = 3 := by
  have h : (8 : ℤ_[2]) = 2 ^ 3 * 1 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul HK13R.ρ_one_ne]
  norm_num

/-- All base digits are 1: `digPrime` of a nonzero constant at the parent frame. -/
private lemma digPrime_one {b : ℤ_[2]} (hb : b ≠ 0) :
    bStageP.digPrime U31.ν₀.zbar (Polynomial.C b) = 1 := by
  show LaurentPolynomial.eval₂ U31.K2.subtype U31.ν₀.zbar (U31.bR (Polynomial.C b)) = 1
  rw [HK13R.bR_const hb]
  exact map_one _

/-- The child weight restricts to the parent weight on fq-coefficients (slot-0
self-development + the recorded slot-min law of the transition pack). -/
private lemma w_coeff (σ₁ : Stage 2 F4)
    (htc : TransitionCoreL bStageP σ₁ U31.fq 1 3 U31.ν₀.zbar)
    {B : Polynomial ℤ_[2]} (hB : B ≠ 0) (hin : inC U31.fq B) :
    σ₁.w B = U31.bw B := by
  have hdev : IsDevelopment U31.fq B (fun j => if j = 0 then B else 0) 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      · exact hin
      · rw [degree_zero, fq_deg]
        decide
    · intro j hj
      dsimp only
      rw [if_neg (by omega)]
    · rw [Finset.sum_range_one]
      dsimp only
      rw [if_pos rfl, pow_zero, mul_one]
  obtain ⟨hlb, j, hjlt, hnz, heq⟩ :=
    htc.base.child_slotmin B (fun j => if j = 0 then B else 0) 1 hB hdev
  have hj0 : j = 0 := by omega
  subst hj0
  have h := heq
  simp at h
  exact h

/-- The child residual of an fq-coefficient with parent digit 1 is 1 (the D.8 vertex
pin at `t' = 0`). -/
private lemma R_coeff (σ₁ : Stage 2 F4)
    (hpin : VertexPin bStageP σ₁ U31.fq U31.ν₀.zbar) (ht0 : σ₁.t = 0)
    {B : Polynomial ℤ_[2]} (hB : B ≠ 0) (hin : inC U31.fq B)
    (hdig : bStageP.digPrime U31.ν₀.zbar B = 1) :
    σ₁.R B = 1 := by
  obtain ⟨c', hR, hval⟩ := hpin B hB hin
  have hc1 : (c' : ↥σ₁.K) = 1 := by
    have h1 : ((c' : ↥σ₁.K) : F4) = ((1 : ↥σ₁.K) : F4) := by
      rw [hval, hdig, OneMemClass.coe_one]
    exact Subtype.ext h1
  rw [hR, hc1, map_one, one_mul, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero]

/-- `↥σ₁.K` has characteristic 2 (subfield of F4). -/
private lemma char_two (σ₁ : Stage 2 F4) : (2 : ↥σ₁.K) = 0 := by
  apply Subtype.ext
  show ((2 : ↥σ₁.K) : F4) = ((0 : ↥σ₁.K) : F4)
  push_cast
  exact CharTwo.two_eq_zero

/-- `X − C 1 = X + 1` at characteristic 2 — ν₁'s ψ in Ranch coordinates. -/
private lemma psi_eq (σ₁ : Stage 2 F4) :
    (Polynomial.X - Polynomial.C (1 : ↥σ₁.K)) = Polynomial.X + 1 := by
  have h2 : (1 : ↥σ₁.K) + 1 = 0 := by
    have h : (1 : ↥σ₁.K) + 1 = 2 := by norm_num
    rw [h, char_two σ₁]
  have hneg : -(1 : ↥σ₁.K) = 1 := neg_eq_of_add_eq_zero_left h2
  rw [sub_eq_add_neg, ← map_neg, hneg, Polynomial.C_1]

/-- Bdev1 IS fgate's development at the child key fq (the `ReadsOf` i = 1 witness
datum — the P-phase rewrites the key to σ₁.Φ through the transition record's
child_key). -/
theorem Bdev1_dev : IsDevelopment U31.fq fgate Bdev1 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold Bdev1
    split_ifs
    · rw [fq_deg]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [fq_deg]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [fq_deg]
      exact lt_of_le_of_lt degree_one_le (by norm_num)
    · rw [degree_zero, fq_deg]
      decide
  · intro j hj
    unfold Bdev1
    split_ifs with h1 h2 h3
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : Bdev1 0 = Polynomial.C 16 := rfl
    have h1 : Bdev1 1 = Polynomial.C 2 := rfl
    have h2 : Bdev1 2 = 1 := rfl
    rw [h0, h1, h2, fgate]
    ring

section

variable (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq)
  (htc : TransitionCoreL bStageP σ₁ U31.fq 1 3 U31.ν₀.zbar)
  (hpin : VertexPin bStageP σ₁ U31.fq U31.ν₀.zbar)
  (hw : ∀ f, f ≠ 0 → σ₁.w f = childW bStageP U31.fq 1 3 f)

include htc in
/-- SideReads clause (i), lower bound, at (ν₁gate σ₁ hΦ, Bdev1, 3): the read
functional `e·σ₁.w(B_j) + j·h` at the steep pair (1, 3) is ≥ γ₁ = 4 at every nonzero
slot. Byte-copy of the first (i) conjunct of `SideReads` at read 1. -/
theorem sideReads1_side_lb :
    ∀ j : ℕ, j < 3 → Bdev1 j ≠ 0 →
      (ν₁gate σ₁ hΦ).gam ≤ ((ν₁gate σ₁ hΦ).e : ℤ) * (ν₁gate σ₁ hΦ).σ.w (Bdev1 j)
        + (j : ℤ) * ((ν₁gate σ₁ hΦ).h : ℤ) := by
  intro j hj hBj
  show (4 : ℤ) ≤ ((1 : ℕ) : ℤ) * σ₁.w (Bdev1 j) + (j : ℤ) * ((3 : ℕ) : ℤ)
  interval_cases j
  · have hw : σ₁.w (Bdev1 0) = U31.bw (Polynomial.C (16 : ℤ_[2])) :=
      w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 16)
    rw [hw, bw_C16]
    norm_num
  · have hw : σ₁.w (Bdev1 1) = U31.bw (Polynomial.C (2 : ℤ_[2])) :=
      w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
    rw [hw, HK13R.bw_C2]
    norm_num
  · have hw : σ₁.w (Bdev1 2) = 0 := ResVal.w_one σ₁
    rw [hw]
    norm_num

/-- SideReads clause (i), equality slots are stride slots, at (ν₁gate σ₁ hΦ, Bdev1, 3):
equality (= 4) holds only at slots 0, 1 = s0 + k, k ≤ wSide/e = 1 (slot 2 sits at 6).
Byte-copy of the second (i) conjunct of `SideReads` at read 1. -/
theorem sideReads1_side_eq :
    ∀ j : ℕ, j < 3 → Bdev1 j ≠ 0 →
      ((ν₁gate σ₁ hΦ).e : ℤ) * (ν₁gate σ₁ hΦ).σ.w (Bdev1 j)
          + (j : ℤ) * ((ν₁gate σ₁ hΦ).h : ℤ) = (ν₁gate σ₁ hΦ).gam →
      ∃ k : ℕ, k ≤ (ν₁gate σ₁ hΦ).wSide / (ν₁gate σ₁ hΦ).e ∧
        j = (ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k ∧ (ν₁gate σ₁ hΦ).pat k ≠ 0 := by
  intro j hj hBj heq
  have heq' : ((1 : ℕ) : ℤ) * σ₁.w (Bdev1 j) + (j : ℤ) * ((3 : ℕ) : ℤ) = 4 := heq
  interval_cases j
  · exact ⟨0, (by norm_num : (0 : ℕ) ≤ 1 / 1), (by norm_num : (0 : ℕ) = 0 + 1 * 0),
      (one_ne_zero : (1 : ↥σ₁.K) ≠ 0)⟩
  · exact ⟨1, (by norm_num : (1 : ℕ) ≤ 1 / 1), (by norm_num : (1 : ℕ) = 0 + 1 * 1),
      (one_ne_zero : (1 : ↥σ₁.K) ≠ 0)⟩
  · have hw : σ₁.w (Bdev1 2) = 0 := ResVal.w_one σ₁
    rw [hw] at heq'
    norm_num at heq'

include htc hpin in
/-- SideReads clause (ii), DIGITS, at (ν₁gate σ₁ hΦ, Bdev1, 3): both stride
coefficients (C 16, C 2) are nonzero, ON the side, with monomial-unit residuals of
scalar pat k = 1 at position T(−σ₁.t·σ₁.wPrev B) (= T 0 at σ₁.t = 0; scalars via the
vertex pin `hpin`, mfun ≡ 0). Byte-copy of the (ii) conjunct of `SideReads` at
read 1. -/
theorem sideReads1_digits :
    ∀ k : ℕ, k ≤ (ν₁gate σ₁ hΦ).wSide / (ν₁gate σ₁ hΦ).e → (ν₁gate σ₁ hΦ).pat k ≠ 0 →
      Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k) ≠ 0 ∧
      ((ν₁gate σ₁ hΦ).e : ℤ) *
          (ν₁gate σ₁ hΦ).σ.w (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k))
          + (((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k : ℕ) : ℤ) *
            ((ν₁gate σ₁ hΦ).h : ℤ) = (ν₁gate σ₁ hΦ).gam ∧
      (ν₁gate σ₁ hΦ).σ.R (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k)) =
        LaurentPolynomial.C ((ν₁gate σ₁ hΦ).pat k) *
          LaurentPolynomial.T (- (ν₁gate σ₁ hΦ).σ.t *
            (ν₁gate σ₁ hΦ).σ.wPrev (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k))) := by
  intro k hk hpat'
  have ht0 : σ₁.t = 0 := σ₁.he1t htc.base.child_e
  have hk1 : k ≤ 1 := by
    rw [show (ν₁gate σ₁ hΦ).wSide = 1 from rfl, show (ν₁gate σ₁ hΦ).e = 1 from rfl] at hk
    omega
  interval_cases k
  · refine ⟨?_, ?_, ?_⟩
    · show Polynomial.C (16 : ℤ_[2]) ≠ 0
      exact Polynomial.C_ne_zero.mpr (by norm_num)
    · show ((1 : ℕ) : ℤ) * σ₁.w (Bdev1 (0 + 1 * 0)) + ((0 + 1 * 0 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) = 4
      have hw : σ₁.w (Bdev1 (0 + 1 * 0)) = U31.bw (Polynomial.C (16 : ℤ_[2])) :=
        w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 16)
      rw [hw, bw_C16]
      norm_num
    · have hgoal : σ₁.R (Bdev1 (0 + 1 * 0)) = LaurentPolynomial.C ((1 : ↥σ₁.K)) *
          LaurentPolynomial.T (- σ₁.t * σ₁.wPrev (Bdev1 (0 + 1 * 0))) := by
        have hR : σ₁.R (Bdev1 (0 + 1 * 0)) = 1 :=
          R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 16)
            (digPrime_one (by norm_num))
        rw [hR, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, map_one, one_mul]
      exact hgoal
  · refine ⟨?_, ?_, ?_⟩
    · show Polynomial.C (2 : ℤ_[2]) ≠ 0
      exact Polynomial.C_ne_zero.mpr HK13R.two_ne_zero'
    · show ((1 : ℕ) : ℤ) * σ₁.w (Bdev1 (0 + 1 * 1)) + ((0 + 1 * 1 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) = 4
      have hw : σ₁.w (Bdev1 (0 + 1 * 1)) = U31.bw (Polynomial.C (2 : ℤ_[2])) :=
        w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
      rw [hw, HK13R.bw_C2]
      norm_num
    · have hgoal : σ₁.R (Bdev1 (0 + 1 * 1)) = LaurentPolynomial.C ((1 : ↥σ₁.K)) *
          LaurentPolynomial.T (- σ₁.t * σ₁.wPrev (Bdev1 (0 + 1 * 1))) := by
        have hR : σ₁.R (Bdev1 (0 + 1 * 1)) = 1 :=
          R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
            (digPrime_one HK13R.two_ne_zero')
        rw [hR, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, map_one, one_mul]
      exact hgoal

include hΦ htc hpin in
/-- SideReads clause (iii), ANCHOR + ψ-ORDER, at read 1 (the single-side read — the
⚠ (iii) `σ.R f` seam is FAITHFUL here, per the blueprint): σ₁.R(window sum) =
T 0 · toLaurent(z + 1) anchors at (a₁, Ranch₁) = (0, z + 1), and ord_{z−1}(z+1) = 1
= μ₁ (char 2). Byte-copy of the (iii) conjunct of `SideReads` at read 1. -/
theorem sideReads1_anchor_ord :
    HasAnchorK ((ν₁gate σ₁ hΦ).σ.R
        (∑ j ∈ Finset.range 3, Bdev1 j * (ν₁gate σ₁ hΦ).σ.Φ ^ j))
      (ν₁gate σ₁ hΦ).a (ν₁gate σ₁ hΦ).Ranch ∧
    OrdPsiPoly (ν₁gate σ₁ hΦ).ψ (ν₁gate σ₁ hΦ).Ranch (ν₁gate σ₁ hΦ).μ := by
  constructor
  · -- ANCHOR: σ₁.R fgate = 1 + T 1 = T 0 · toLaurent (z + 1)
    have ht0 : σ₁.t = 0 := σ₁.he1t htc.base.child_e
    have hs1 : σ₁.s = 1 := by
      have hbez := σ₁.hbez
      rw [htc.base.child_e, htc.base.child_h, ht0] at hbez
      push_cast at hbez
      linarith
    have hwfq : σ₁.w U31.fq = 3 := by
      have h := σ₁.hwΦ
      rw [hΦ, htc.base.child_h] at h
      exact_mod_cast h
    have hw16 : σ₁.w (Polynomial.C (16 : ℤ_[2])) = 4 := by
      rw [w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 16), bw_C16]
    have hw2 : σ₁.w (Polynomial.C (2 : ℤ_[2])) = 1 := by
      rw [w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2),
        HK13R.bw_C2]
    have hBtne : Polynomial.C (2 : ℤ_[2]) * U31.fq ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') U31.fq_monic.ne_zero
    have hwBt : σ₁.w (Polynomial.C (2 : ℤ_[2]) * U31.fq) = 4 := by
      rw [σ₁.hwmul _ _ (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') U31.fq_monic.ne_zero,
        hw2, hwfq]
      norm_num
    have hbwfq : U31.bw U31.fq = 2 := U31.bw_eq HK13R.NF_θ_fq
    have hABne : Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq ≠ 0 := by
      intro h0
      have h16 : Polynomial.C (16 : ℤ_[2]) = -(Polynomial.C 2 * U31.fq) :=
        eq_neg_of_add_eq_zero_left h0
      have hw1 : U31.bw (Polynomial.C (16 : ℤ_[2])) = 4 := bw_C16
      have hmul : U31.bw (Polynomial.C (2 : ℤ_[2]) * U31.fq) = 3 := by
        rw [HK13R.bw_mul _ _ (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero')
          U31.fq_monic.ne_zero, HK13R.bw_C2, hbwfq]
        norm_num
      have hneg : U31.bw (-(Polynomial.C (2 : ℤ_[2]) * U31.fq))
          = U31.bw (Polynomial.C (2 : ℤ_[2]) * U31.fq) := ResVal.w_neg bStageP _ hBtne
      rw [h16, hneg, hmul] at hw1
      norm_num at hw1
    have hdev2 : IsDevelopment U31.fq (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq)
        (fun j => if j = 0 then Polynomial.C 16 else if j = 1 then Polynomial.C 2 else 0)
        2 := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        dsimp only
        split_ifs
        · rw [fq_deg]
          exact lt_of_le_of_lt degree_C_le (by norm_num)
        · rw [fq_deg]
          exact lt_of_le_of_lt degree_C_le (by norm_num)
        · rw [degree_zero, fq_deg]
          decide
      · intro j hj
        dsimp only
        split_ifs with h1 h2
        · exact absurd h1 (by omega)
        · exact absurd h2 (by omega)
        · rfl
      · rw [Finset.sum_range_succ, Finset.sum_range_one]
        norm_num
    obtain ⟨hlb2, j2, hj2, hnz2, heq2⟩ := htc.base.child_slotmin
      (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq)
      (fun j => if j = 0 then Polynomial.C 16 else if j = 1 then Polynomial.C 2 else 0)
      2 hABne hdev2
    have hwAB : σ₁.w (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq) = 4 := by
      interval_cases j2
      · have h' := heq2
        simp only [Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, one_mul, zero_mul,
          add_zero, reduceIte] at h'
        rw [h']
        exact bw_C16
      · have h' := heq2
        simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, reduceIte] at h'
        rw [if_neg (by norm_num : ¬(1 : ℕ) = 0)] at h'
        rw [h']
        have h2 : bStageP.w (Polynomial.C (2 : ℤ_[2])) = 1 := HK13R.bw_C2
        rw [h2]
        norm_num
    have hRA : σ₁.R (Polynomial.C (16 : ℤ_[2])) = 1 :=
      R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 16)
        (digPrime_one (by norm_num))
    have hRC2 : σ₁.R (Polynomial.C (2 : ℤ_[2])) = 1 :=
      R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
        (digPrime_one HK13R.two_ne_zero')
    have hRfq : σ₁.R U31.fq = LaurentPolynomial.T 1 := by
      have h := σ₁.hRΦ
      rw [hΦ, hs1] at h
      exact h
    have hRBt : σ₁.R (Polynomial.C (2 : ℤ_[2]) * U31.fq) = LaurentPolynomial.T 1 := by
      rw [σ₁.hRmul _ _ (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') U31.fq_monic.ne_zero,
        hRC2, hRfq, one_mul]
    have hRAB : σ₁.R (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq)
        = 1 + LaurentPolynomial.T 1 := by
      rw [σ₁.hRadd _ _ (Polynomial.C_ne_zero.mpr (by norm_num)) hBtne hABne
        (by rw [hw16, hwBt]) (by rw [hwAB, hw16]), hRA, hRBt]
    have hsplit : fgate = (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq)
        + U31.fq ^ 2 := by
      rw [fgate]
      ring
    have hwfq2 : σ₁.w (U31.fq ^ 2) = 6 := by
      rw [ResVal.w_pow σ₁ _ U31.fq_monic.ne_zero 2, hwfq]
      norm_num
    have hfgatene : fgate ≠ 0 := by
      rw [hsplit]
      intro h0
      have h1 : U31.fq ^ 2 = -(Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq) :=
        eq_neg_of_add_eq_zero_right h0
      have h2 : σ₁.w (U31.fq ^ 2)
          = σ₁.w (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq) := by
        rw [h1, ResVal.w_neg σ₁ _ hABne]
      rw [hwfq2, hwAB] at h2
      norm_num at h2
    have hRfgate : σ₁.R fgate = 1 + LaurentPolynomial.T 1 := by
      have h := σ₁.hRlt (Polynomial.C (16 : ℤ_[2]) + Polynomial.C 2 * U31.fq) (U31.fq ^ 2)
        hABne (pow_ne_zero 2 U31.fq_monic.ne_zero)
        (by rw [← hsplit]; exact hfgatene)
        (by rw [hwAB, hwfq2]; norm_num)
      rw [hsplit, h, hRAB]
    show HasAnchorK (σ₁.R (∑ j ∈ Finset.range 3, Bdev1 j * σ₁.Φ ^ j)) 0
      (Polynomial.X + 1 : Polynomial ↥σ₁.K)
    have hsum' : (∑ j ∈ Finset.range 3, Bdev1 j * σ₁.Φ ^ j) = fgate := by
      rw [hΦ]
      exact Bdev1_dev.2.2.symm
    rw [hsum', hRfgate]
    refine ⟨?_, ?_⟩
    · simp
    · rw [LaurentPolynomial.T_zero, one_mul, map_add, Polynomial.toLaurent_X,
        Polynomial.toLaurent_one]
      exact add_comm _ _
  · -- ORDER: ord_{z−1}(z+1) = 1 at characteristic 2
    have hord : OrdPsiPoly (Polynomial.X + 1 : Polynomial ↥σ₁.K) (Polynomial.X + 1) 1 := by
      constructor
      · rw [pow_one]
      · intro hdvd
        have hne : (Polynomial.X + 1 : Polynomial ↥σ₁.K) ≠ 0 := by
          have h := Polynomial.monic_X_add_C (1 : ↥σ₁.K)
          rw [Polynomial.C_1] at h
          exact h.ne_zero
        have h1 := Polynomial.natDegree_le_of_dvd hdvd hne
        rw [Polynomial.natDegree_pow] at h1
        have h2 : (Polynomial.X + 1 : Polynomial ↥σ₁.K).natDegree = 1 := by
          have h := Polynomial.natDegree_X_add_C (1 : ↥σ₁.K)
          rwa [Polynomial.C_1] at h
        rw [h2] at h1
        omega
    have hgoal : OrdPsiPoly (Polynomial.X - Polynomial.C (1 : ↥σ₁.K))
        (Polynomial.X + 1) 1 := by
      rw [psi_eq σ₁]
      exact hord
    exact hgoal

include hΦ htc hpin in
/-- SideReads clauses (iv) + (vi) jointly, at read 1 (TERMINAL — the last-read
freedom: Φnext is EXISTENTIAL, one designation shared by both clauses):
(iv) the recorded landing produces a key — `LandingKey (ν₁gate …) Φtop` (ν₁ is
recentering-species, HK-18 resolution R-2, so this is the recorded-lift realizer leg:
Φtop = Φ̂ − ν₁.lift);
(vi) VERTEX READ-OFF in Φtop-coordinates: any Φtop-development of the window sum
(= fgate) has its μ₁ = 1 slot digit equal to vtx ν₁ (= 1; digit of 2·lift + 2). -/
theorem sideReads1_terminal :
    ∃ Φtop : Polynomial ℤ_[2],
      LandingKey (ν₁gate σ₁ hΦ) Φtop ∧
      ∀ (Bh : ℕ → Polynomial ℤ_[2]) (Nh : ℕ),
        IsDevelopment Φtop (∑ j ∈ Finset.range 3, Bdev1 j * (ν₁gate σ₁ hΦ).σ.Φ ^ j) Bh Nh →
        (ν₁gate σ₁ hΦ).σ.digPrime (ν₁gate σ₁ hΦ).zbar (Bh (ν₁gate σ₁ hΦ).μ)
          = (ν₁gate σ₁ hΦ).vtx := by
  have ht0 : σ₁.t = 0 := σ₁.he1t htc.base.child_e
  have hwΦ' : σ₁.w σ₁.Φ = 3 := by
    have h := σ₁.hwΦ
    rw [htc.base.child_h] at h
    exact_mod_cast h
  -- the recentering realizer exists (C 8 at weight 3 with digit 1 = the center)
  have hex : ∃ tL, RecenterLiftSpec (ν₁aux σ₁ hΦ) tL := by
    refine ⟨Polynomial.C (8 : ℤ_[2]), ?_, Polynomial.C_ne_zero.mpr (by norm_num), ?_, ?_⟩
    · show (Polynomial.C (8 : ℤ_[2])).degree < σ₁.Φ.degree
      rw [hΦ]
      exact inC_fq_C 8
    · show σ₁.w (Polynomial.C (8 : ℤ_[2])) = σ₁.w σ₁.Φ
      rw [w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 8), bw_C8,
        hwΦ']
    · have hgoal : σ₁.R (Polynomial.C (8 : ℤ_[2]))
          = LaurentPolynomial.C ((1 : ↥σ₁.K)) * LaurentPolynomial.T 0 := by
        rw [R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr (by norm_num)) (inC_fq_C 8)
          (digPrime_one (by norm_num)), LaurentPolynomial.T_zero, map_one, one_mul]
      exact hgoal
  have hspec : RecenterLiftSpec (ν₁aux σ₁ hΦ) ((polOM 2 F4).liftOf (ν₁aux σ₁ hΦ)) := by
    classical
    show RecenterLiftSpec (ν₁aux σ₁ hΦ)
      (if h : ∃ tL, RecenterLiftSpec (ν₁aux σ₁ hΦ) tL then h.choose else 0)
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨hin, hℓne, hwℓ, hRℓ⟩ := hspec
  refine ⟨σ₁.Φ - (ν₁gate σ₁ hΦ).lift, ⟨fun _ => ⟨hin, hℓne, hwℓ, hRℓ, rfl⟩,
    fun hne => absurd rfl hne⟩, ?_⟩
  -- clause (vi): the vertex digit of ANY Φtop-development is 1
  intro Bh Nh hdev
  set L : Polynomial ℤ_[2] := (ν₁gate σ₁ hΦ).lift with hLdef
  -- retype the choice-spec conjuncts at L (defeq: L ≡ polOM's choice on ν₁aux)
  have hLne : L ≠ 0 := hℓne
  have hwL : σ₁.w L = σ₁.w σ₁.Φ := hwℓ
  set a : ℤ_[2] := L.coeff 1 with ha
  set b : ℤ_[2] := L.coeff 0 with hb
  have hLin : L.degree < U31.fq.degree := by
    have h' : L.degree < σ₁.Φ.degree := hin
    rwa [hΦ] at h'
  have hbwL : U31.bw L = 3 := by
    have h1 : σ₁.w L = U31.bw L := w_coeff σ₁ htc hLne hLin
    have h2 : σ₁.w L = 3 := by
      rw [hwL, hwΦ']
    rw [← h1]
    exact h2
  -- 4 ∣ a: the NF exponent 3 forces v₂(coeff 1 of θ L) ≥ 3, and θ scales slot 1 by 2
  obtain ⟨m, Q, hQ⟩ := HK13R.NF_exists (HK13R.θ_ne_zero hLne)
  have hm3 : m = 3 := by
    have h := U31.bw_eq hQ
    rw [hbwL] at h
    exact_mod_cast h.symm
  subst hm3
  have hcoeff1 : a * 2 = 8 * Q.coeff 1 := by
    have h := congrArg (fun q => Polynomial.coeff q 1) hQ.1
    simp only [HK13R.θ_coeff] at h
    rw [← C_pow, Polynomial.coeff_C_mul] at h
    rw [ha]
    calc L.coeff 1 * 2 = L.coeff 1 * 2 ^ 1 := by norm_num
      _ = 8 * Q.coeff 1 := by rw [h]; norm_num
  obtain ⟨q, hq⟩ : ∃ q : ℤ_[2], a = 4 * q := by
    refine ⟨Q.coeff 1, ?_⟩
    have h2 : (2 : ℤ_[2]) * a = 2 * (4 * Q.coeff 1) := by linear_combination hcoeff1
    exact mul_left_cancel₀ HK13R.two_ne_zero' h2
  -- the linear form of L
  have hndL : L.natDegree ≤ 1 := by
    have h2 : L.natDegree < 2 := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hLne]
      have hcast : U31.fq.degree = ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast fq_deg
      rw [← hcast]
      exact hLin
    omega
  have heqL : L = Polynomial.C a * X + Polynomial.C b := by
    rw [ha, hb]
    exact Polynomial.eq_X_add_C_of_natDegree_le_one hndL
  -- window sum = fgate; the development re-keys to fq − L
  have hsum' : (∑ j ∈ Finset.range 3, Bdev1 j * (ν₁gate σ₁ hΦ).σ.Φ ^ j) = fgate := by
    show (∑ j ∈ Finset.range 3, Bdev1 j * σ₁.Φ ^ j) = fgate
    rw [hΦ]
    exact Bdev1_dev.2.2.symm
  have hdev' : IsDevelopment (U31.fq - L) fgate Bh Nh := by
    have h := hdev
    rw [hsum', hΦ] at h
    exact h
  -- Φtop is monic quadratic
  have hmonΦt : (U31.fq - L).Monic := U31.fq_monic.sub_of_left hLin
  have hdegΦt : (U31.fq - L).degree = 2 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hLin, fq_deg]
  -- the canonical Φtop-development of fgate: (B0, B1, 1)
  set c1 : ℤ_[2] := 2 * a * b + 2 * a - a ^ 2 * (2 - a) with hc1
  set c0 : ℤ_[2] := b ^ 2 + 2 * b + 16 - a ^ 2 * (4 - b) with hc0
  set B0 : Polynomial ℤ_[2] := Polynomial.C c1 * X + Polynomial.C c0 with hB0
  set B1 : Polynomial ℤ_[2] := Polynomial.C 2 * L + Polynomial.C 2 + Polynomial.C (a ^ 2)
    with hB1
  have hcanon : IsDevelopment (U31.fq - L) fgate
      (fun j => if j = 0 then B0 else if j = 1 then B1 else if j = 2 then 1 else 0) 3 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      · rw [hdegΦt]
        have hd : B0.degree ≤ 1 := by
          rw [hB0]
          compute_degree
        exact lt_of_le_of_lt hd (by decide)
      · rw [hdegΦt]
        have hd : B1.degree ≤ 1 := by
          rw [hB1, heqL]
          compute_degree
        exact lt_of_le_of_lt hd (by decide)
      · rw [hdegΦt]
        exact lt_of_le_of_lt degree_one_le (by decide)
      · rw [degree_zero, hdegΦt]
        decide
    · intro j hj
      dsimp only
      split_ifs with h1 h2 h3
      · exact absurd h1 (by omega)
      · exact absurd h2 (by omega)
      · exact absurd h3 (by omega)
      · rfl
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      show fgate = B0 * (U31.fq - L) ^ 0 + B1 * (U31.fq - L) ^ 1 + 1 * (U31.fq - L) ^ 2
      rw [hB0, hB1, hc1, hc0, heqL, fgate, U31.fq]
      simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]
      ring
  have hBh1 : Bh 1 = B1 := by
    have h := L0_FactB_unique (U31.fq - L) hmonΦt fgate hdev' hcanon 1
    simpa using h
  -- the vertex digit: R(B1) = R(C 2) = 1 (the tail 2L + a² sits at weight ≥ 4 > 1)
  have hw2' : σ₁.w (Polynomial.C (2 : ℤ_[2])) = 1 := by
    rw [w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2),
      HK13R.bw_C2]
  have hL3 : σ₁.w L = 3 := by
    rw [w_coeff σ₁ htc hLne hLin, hbwL]
  have hrest : (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) ≠ 0 →
      4 ≤ σ₁.w (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) := by
    intro hne
    have hw2L : σ₁.w (Polynomial.C (2 : ℤ_[2]) * L) = 4 := by
      rw [σ₁.hwmul _ _ (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') hLne, hw2', hL3]
      norm_num
    by_cases ha0 : a = 0
    · have hz : Polynomial.C (a ^ 2) = 0 := by
        rw [ha0]
        norm_num
      rw [hz, add_zero, hw2L]
    · have ha2ne : (a ^ 2 : ℤ_[2]) ≠ 0 := pow_ne_zero 2 ha0
      have hq0 : q ≠ 0 := by
        intro h0
        apply ha0
        rw [hq, h0, mul_zero]
      have hbwa2 : (4 : ℤ) ≤ U31.bw (Polynomial.C (a ^ 2)) := by
        have ha2 : (a ^ 2 : ℤ_[2]) = 16 * q ^ 2 := by
          rw [hq]
          ring
        rw [ha2, map_mul, HK13R.bw_mul _ _ (Polynomial.C_ne_zero.mpr (by norm_num))
          (Polynomial.C_ne_zero.mpr (pow_ne_zero 2 hq0)), bw_C16]
        have h0 := U31.bw_const_nonneg (pow_ne_zero 2 hq0)
        linarith
      have hwa2 : (4 : ℤ) ≤ σ₁.w (Polynomial.C (a ^ 2)) := by
        rw [w_coeff σ₁ htc (Polynomial.C_ne_zero.mpr ha2ne) (inC_fq_C _)]
        exact hbwa2
      have hult := σ₁.hwult (Polynomial.C 2 * L) (Polynomial.C (a ^ 2))
        (mul_ne_zero (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') hLne)
        (Polynomial.C_ne_zero.mpr ha2ne) hne
      calc (4 : ℤ) = min 4 4 := by norm_num
        _ ≤ min (σ₁.w (Polynomial.C 2 * L)) (σ₁.w (Polynomial.C (a ^ 2))) := by
            rw [hw2L]
            exact min_le_min (le_refl 4) hwa2
        _ ≤ _ := hult
  have hB1split : B1 = Polynomial.C (2 : ℤ_[2]) + (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) := by
    rw [hB1]
    ring
  have hRB1 : σ₁.R B1 = 1 := by
    rw [hB1split]
    by_cases hrest0 : (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) = 0
    · rw [hrest0, add_zero]
      exact R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
        (digPrime_one HK13R.two_ne_zero')
    · have hne2 : Polynomial.C (2 : ℤ_[2]) + (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) ≠ 0 := by
        intro h0
        have h1 : (Polynomial.C 2 * L + Polynomial.C (a ^ 2)) = -(Polynomial.C (2 : ℤ_[2])) :=
          eq_neg_of_add_eq_zero_right h0
        have h2 := hrest hrest0
        rw [h1, ResVal.w_neg σ₁ _ (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero'), hw2'] at h2
        norm_num at h2
      have h := σ₁.hRlt (Polynomial.C (2 : ℤ_[2])) (Polynomial.C 2 * L + Polynomial.C (a ^ 2))
        (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') hrest0 hne2
        (by rw [hw2']; linarith [hrest hrest0])
      rw [h]
      exact R_coeff σ₁ hpin ht0 (Polynomial.C_ne_zero.mpr HK13R.two_ne_zero') (inC_fq_C 2)
        (digPrime_one HK13R.two_ne_zero')
  -- vtx ν₁ = 1
  have hXp1_monic : (Polynomial.X + 1 : Polynomial ↥σ₁.K).Monic := by
    have h := Polynomial.monic_X_add_C (1 : ↥σ₁.K)
    rwa [Polynomial.C_1] at h
  have hdeg1 : (Polynomial.X + 1 : Polynomial ↥σ₁.K).degree = 1 := by
    have h := Polynomial.degree_X_add_C (1 : ↥σ₁.K)
    rwa [Polynomial.C_1] at h
  have hvp : (ν₁gate σ₁ hΦ).vtxPoly = 1 := by
    have hdiv : (Polynomial.X + 1 : Polynomial ↥σ₁.K) /ₘ (Polynomial.X + 1) = 1 := by
      have h := Polynomial.mul_divByMonic_cancel_left (1 : Polynomial ↥σ₁.K) hXp1_monic
      rwa [mul_one] at h
    have hmod : (1 : Polynomial ↥σ₁.K) %ₘ (Polynomial.X + 1) = 1 := by
      refine (Polynomial.modByMonic_eq_self_iff hXp1_monic).mpr ?_
      rw [Polynomial.degree_one, hdeg1]
      decide
    have h0 : (ν₁gate σ₁ hΦ).vtxPoly
        = ((Polynomial.X + 1 : Polynomial ↥σ₁.K) /ₘ
            (Polynomial.X - Polynomial.C (1 : ↥σ₁.K)) ^ 1) %ₘ
          (Polynomial.X - Polynomial.C (1 : ↥σ₁.K)) := rfl
    rw [h0, psi_eq σ₁, pow_one, hdiv, hmod]
    rfl
  have hvtx : (ν₁gate σ₁ hΦ).vtx = 1 := by
    have hexp : (ν₁gate σ₁ hΦ).a - ((ν₁gate σ₁ hΦ).μ : ℤ) * (ν₁gate σ₁ hΦ).mhat = 0 := by
      have hmh : (ν₁gate σ₁ hΦ).mhat = 0 := by
        show -(ν₁gate σ₁ hΦ).t * ((ν₁gate σ₁ hΦ).h : ℤ) * ((ν₁gate σ₁ hΦ).g : ℤ) = 0
        have ht : (ν₁gate σ₁ hΦ).t = 0 := rfl
        rw [ht]
        ring
      have ha' : (ν₁gate σ₁ hΦ).a = 0 := rfl
      rw [ha', hmh, mul_zero, sub_zero]
    unfold Node.vtx
    rw [hvp, Polynomial.eval₂_one, mul_one, hexp, zpow_zero, Units.val_one]
  show (ν₁gate σ₁ hΦ).σ.digPrime (ν₁gate σ₁ hΦ).zbar (Bh 1) = (ν₁gate σ₁ hΦ).vtx
  rw [hBh1, hvtx]
  show LaurentPolynomial.eval₂ σ₁.K.subtype (ν₁gate σ₁ hΦ).zbar (σ₁.R B1) = 1
  rw [hRB1]
  exact map_one _

/-- SideReads clause (v), at read 1: ν₁ carries the polOM lift (rfl-grade via
`CanonPolicy.blind` — HK-18's aux-node pattern) and the canonical residue root
(z − 1 has the unique root 1 in F4). -/
theorem sideReads1_lifts :
    (ν₁gate σ₁ hΦ).lift = (polOM 2 F4).liftOf (ν₁gate σ₁ hΦ) ∧
    (((ν₁gate σ₁ hΦ).zbar : F4ˣ) : F4) = canonRoot (ν₁gate σ₁ hΦ) := by
  constructor
  · exact ((polOM 2 F4).blind (ν₁aux σ₁ hΦ) ((polOM 2 F4).liftOf (ν₁aux σ₁ hΦ))).symm
  · have hψim : ψImage (ν₁gate σ₁ hΦ) = Polynomial.X - Polynomial.C (1 : F4) := by
      show (Polynomial.X - Polynomial.C (1 : ↥σ₁.K)).map σ₁.K.subtype = _
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_one]
    have hroots : (ψImage (ν₁gate σ₁ hΦ)).roots = {1} := by
      rw [hψim]
      exact Polynomial.roots_X_sub_C 1
    show ((1 : F4ˣ) : F4) = canonRoot (ν₁gate σ₁ hΦ)
    unfold canonRoot
    rw [hroots]
    simp only [Multiset.toFinset_singleton, Finset.image_singleton, Finset.min_singleton,
      Units.val_one]
    exact (Equiv.symm_apply_apply (fieldEnum F4) 1).symm

end

end HK20

end LeanUrat.MovesJ
