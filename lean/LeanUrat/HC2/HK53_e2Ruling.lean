import Mathlib
import LeanUrat.HC2.HK11a_vertexTransport

/-!
# HK-53 — THE ν_{i+1}.e ≥ 2 RULING LEAF (Tier-1 item 2, hardest-first order 2026-08-08)
(ruling unit, 2026-08-08 wallclock 2026-08-02; agent: v9-e2-ruling)

## The parked question (HK-12 F4 / QUEUE_EXECUTION item-3 post-wave 1)

V9's four reopened sorries (`HC1/V9_K1nonrec.lean`: steep + corner legs of
`V9_K1nonrec`/`V9_E1box_nonrec`) stood mapped TRUE at `ν_{i+1}.e = 1` (supplier on disk:
`HK11a.readVertex_e1`/`readBox_e1`) and **FALSE-SUSPECT** at `ν_{i+1}.e ≥ 2` (compiled
obstruction: `HK52.hk52_v9_qform_reduction` — the stretch `σ_{i+1}.w B = e′·σV.w B` with
no `e′` in `strFrame(i+1)`).  The ν_{i+1}.e disposition was surfaced 2026-07-31 and never
adjudicated.  THIS LEAF IS THE RULING.  Numerics record:
`verification/hk53_e2_ruling_trace.py` (all asserted, green).

## THE RULING — the FALSE-SUSPECT mapping is RESCOPED to VACUITY-SUSPECT; neither
## pre-registered verdict survives; the compiled fence below is the decisive state

Traced at the HK23 carrier family (child pair (2,5) over `σV.w = bw`), the e′ ≥ 2
sub-perimeter turns out to be fenced BEFORE the vertex question is reached:

1. **The stride-congruence fence** (`digit_stride_dvd`, `width_sq_dvd`): at any node
   whose frame carries the (S-a) child stretch (`σ.e = ν.e = e′ ≥ 2`, `child_e`), the
   SideReads(i)+(ii) ties force every nonzero pattern digit to a stride index
   `k ≡ 0 (mod e′)` and `e′² ∣ wSide`.  (At the (2,5) gate: recorded sides of width 2 —
   HK23's `ν₁ram` shape — carry NO f: the tie `4·bw(B₀) = 4·bw(B₂) + 10` is a mod-4
   contradiction.  Lawful (2,5) sides have width 4 with the middle digit FORCED zero.)
2. **The below-window conspiracy fence** (`sideReads_belowWindow_tie`): at e′ ≥ 2 the
   σ-frame values `σ.w(B_j) + j·h` STRICTLY ASCEND along the read side (per-slot excess
   `(j−s0)·h·(e′−1)/e′ > 0` — the child-read transport of `V9_steepSide_frameDescent`'s
   tension), and clause (iii)'s anchored rendering `σ.R f = T(a)·Ranch` with ≥ 2 pattern
   digits (hpat0 + hOrd·hμ·hg) then REQUIRES a nonzero development slot STRICTLY BELOW
   the window (`j < s0`) tying the frame minimum — else `σ.R f` is a single (S5)
   monomial and (iii) is contradictory.
3. **The s0 = 0 kill** (`sideReads_unsat_e2_s0_zero`, `readsOf_e2_s0_zero_empty`): with
   `s0 = 0` there is nothing below the window — SideReads at an e′ ≥ 2 read is
   UNSATISFIABLE, and every coherent `ReadsOf` record whose non-recentering-parented
   child read has `e ≥ 2 ∧ s0 = 0` is CONTRADICTORY.  In particular the entire
   HK23-gate carrier family (`s0₁ = 0`) carries no f: `ReadsOf` is EMPTY there — the
   FALSE-SUSPECT countermodel plan (build ReadsOf on the H₂ram shape, HK-12 F4's
   "residual to a full refutation") is IMPOSSIBLE, not merely expensive.
4. **The vertex reduction on whatever survives** (`displayed_iff_lineZero`): on any
   e′ ≥ 2 record that DOES satisfy `ReadsOf` (necessarily s0 ≥ e′² with a below-window
   frame-tie conspiracy — arithmetically conceivable, construction OPEN), V9's displayed
   ℚ-form holds IFF the parent line vanishes at the vertex (`lineᵢ.at(μ·cwᵢ) = 0`).
   So the displayed statements are false ONLY on {e′ ≥ 2} ∩ {conspiracy inhabited} ∩
   {lineᵢ.at(μ·cwᵢ) ≠ 0} — plausibly empty.
5. **The corrected display — the re-key design, compiled** (`readVertex_stretch`,
   `readBox_stretch`): the honest all-e′ law is the displayed form at the NEXT frame's
   scale, `σ_{i+1}.w (B μ) = strFrame(i+2)·lineᵢ.at(μᵢ·cwᵢ)` — the OLD display's
   `strFrame(i+1)` is the pre-wave keying's scale (child keyed at the parent pair);
   under the ratified (S-a) keying the child weight is `ν_{i+1}.e`-stretched and the
   correct scale is `strFrame(i+2) = strFrame(i+1)·ν_{i+1}.e`.  Proved here at ALL e′
   from on-disk assets (`HK11a.sigmaV_vertexLaw` + `HK52.hk52_qform_stretch` + the
   γ-tie/slope-law arithmetic), same carried hypotheses as `readVertex_e1` (hσL,
   strict hsteep) MINUS `he'1`.  At e′ = 1 it IS the current display.

CONSEQUENCE FOR THE V9 SORRY CONE (display, not implementation): the four sorries STAND,
statements byte-unchanged.  Honest fill routes: e′ = 1 legs = the HK11a suppliers behind
the hsteep/hσL rulings (unchanged); e′ ≥ 2 legs = vacuity (this leaf's fence closes
`s0 = 0`; the ONE residual open lemma is the below-window conspiracy EXCLUSION: no
coherent ReadsOf record has a `j < s0` frame-min tie reproducing the anchored pattern at
an e′ ≥ 2 read — its exact shape is pinned by `sideReads_belowWindow_tie`).  NO re-key of
V9's statements is required for truth; if the corpus ever repopulates the e′ ≥ 2
perimeter (e.g. by weakening SideReads(iii)), the statements must move to the
strFrame(i+2) scale compiled here.  K1 vertex-pin consumers (`K1_readVertexPin*`,
U20a/b/c, U22-E2): unchanged, still waiting on the V9 fills.

Statements elsewhere BYTE-UNTOUCHED (this is a leaf; nothing imports it).  No new
axioms; all theorems Lean-core (#print axioms at EOF).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace HK53

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### §A — the e′ ≥ 2 side fence (node level; `hse`/`hsh` are `child_e`/`child_h`,
supplied at history level by the coherence leg — see §C) -/

/-- Slot-term weight: `σ.w (B·Φ^j) = σ.w B + j·σ.h`. -/
private lemma term_w (σ : Stage p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (j : ℕ) :
    σ.w (B * σ.Φ ^ j) = σ.w B + (j : ℤ) * (σ.h : ℤ) := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  rw [σ.hwmul B (σ.Φ ^ j) hB (pow_ne_zero _ hΦne), ResVal.w_pow σ σ.Φ hΦne j, σ.hwΦ]

/-- **The stride-congruence fence**: at a stage carrying the (S-a) child stretch
(`σ.e = ν.e ≥ 2` — `child_e` at a non-recentering-parented node), every nonzero
recorded pattern digit sits at a stride index divisible by `ν.e`: the SideReads(ii)
ties `e·σ.w(B_{s0+ek}) + (s0+ek)·h = γ` read through `hStretch` (`σ.w = e·wPrev` on
coefficients) give `e·(wPrev₀ − wPrev_k) = k·h`, and `gcd(e,h) = 1` forces `e ∣ k`. -/
theorem digit_stride_dvd (ν : Node p F) (hse : ν.σ.e = ν.e)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hdeg : ∀ j, (B j).degree < ν.σ.Φ.degree)
    (hsr : SideReads ν B Nd Φnext)
    (k : ℕ) (hk : k ≤ ν.wSide / ν.e) (hpk : ν.pat k ≠ 0) : ν.e ∣ k := by
  obtain ⟨hB0, hw0, -⟩ := hsr.2.1 0 (Nat.zero_le _) ν.hpat0
  obtain ⟨hBk, hwk, -⟩ := hsr.2.1 k hk hpk
  simp only [Nat.mul_zero, Nat.add_zero] at hB0 hw0
  have hstr0 : ν.σ.w (B ν.s0) = (ν.e : ℤ) * ν.σ.wPrev (B ν.s0) := by
    rw [ν.σ.hStretch _ hB0 (hdeg _), hse]
  have hstrk : ν.σ.w (B (ν.s0 + ν.e * k))
      = (ν.e : ℤ) * ν.σ.wPrev (B (ν.s0 + ν.e * k)) := by
    rw [ν.σ.hStretch _ hBk (hdeg _), hse]
  rw [hstr0] at hw0
  rw [hstrk] at hwk
  -- e·(wPrev₀ − wPrev_k) = k·h  (cancel one e from the e² difference)
  have hE : (ν.e : ℤ) ≠ 0 := by
    have h1 := ν.he
    exact_mod_cast Nat.pos_iff_ne_zero.mp (by omega)
  have hcancel : (ν.e : ℤ) * (ν.σ.wPrev (B ν.s0) - ν.σ.wPrev (B (ν.s0 + ν.e * k)))
      = (k : ℤ) * (ν.h : ℤ) := by
    apply mul_left_cancel₀ hE
    push_cast at hw0 hwk ⊢
    linear_combination hw0 - hwk
  have hdvdZ : (ν.e : ℤ) ∣ ((k * ν.h : ℕ) : ℤ) := by
    push_cast
    exact ⟨_, hcancel.symm⟩
  have hdvdN : ν.e ∣ k * ν.h := Int.ofNat_dvd.mp hdvdZ
  exact (Nat.Coprime.dvd_of_dvd_mul_right ν.hcop) hdvdN

/-- **The width fence**: `e′² ∣ wSide` — the top digit (`hpatTop`) sits at a stride
index divisible by `e′`, and `e′ ∣ wSide` already (hEdvd). -/
theorem width_sq_dvd (ν : Node p F) (hse : ν.σ.e = ν.e)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hdeg : ∀ j, (B j).degree < ν.σ.Φ.degree)
    (hsr : SideReads ν B Nd Φnext) : ν.e * ν.e ∣ ν.wSide := by
  have htop := digit_stride_dvd ν hse B Nd Φnext hdeg hsr (ν.wSide / ν.e) le_rfl ν.hpatTop
  obtain ⟨c, hc⟩ := ν.hEdvd
  obtain ⟨d, hd⟩ := htop
  have he0 : ν.e ≠ 0 := by have := ν.he; omega
  have hdivc : ν.wSide / ν.e = c := by rw [hc]; exact Nat.mul_div_cancel_left c (by omega)
  rw [hdivc] at hd
  exact ⟨d, by rw [hc, hd]; ring⟩

/-- **THE BELOW-WINDOW CONSPIRACY FENCE** (the ruling's compiled core): at a stage
carrying the (S-a) child stretch with `ν.e ≥ 2`, the SideReads clauses force a nonzero
development slot STRICTLY BELOW the window whose σ-frame value ties the window base's —

  ∃ j < s0,  B j ≠ 0  ∧  σ.w(B j) + j·h ≤ σ.w(B s0) + s0·h.

Mechanism: along the read side the σ-frame values strictly ascend (`e·Δframe =
ΔG + Δj·h·(e−1)` with ΔG ≥ 0 by clause (i)), so absent a below-window tie the frame
minimum of f's development is attained at `s0` ALONE; the residual laws (hRlt on the
split at `s0`, hRmul/`R_pow`/hRΦ/hS5) then render `σ.R f` a SINGLE monomial
`C(c)·T(m)`, while clause (iii)'s anchor `σ.R f = T(a)·Ranch` demands the ≥ 2-term
pattern (`Ranch.coeff 0 ≠ 0` and `deg Ranch ≥ μ·g ≥ 1` by hOrd/hμ/hg/hψ) — a
monomial-vs-two-term contradiction. -/
theorem sideReads_belowWindow_tie (ν : Node p F) (hse : ν.σ.e = ν.e) (hsh : ν.σ.h = ν.h)
    (he2 : 2 ≤ ν.e)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hdev : IsDevelopment ν.σ.Φ (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) B Nd)
    (hsr : SideReads ν B Nd Φnext) :
    ∃ j : ℕ, j < ν.s0 ∧ B j ≠ 0 ∧
      ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) ≤ ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ) := by
  classical
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ j < s0, B j ≠ 0 → frame(s0) < frame(j)
  have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
  obtain ⟨hanch, hord⟩ := hsr.2.2.1
  -- the window-base digit (k = 0 of clause (ii))
  obtain ⟨hB0, hw0, -⟩ := hsr.2.1 0 (Nat.zero_le _) ν.hpat0
  simp only [Nat.mul_zero, Nat.add_zero] at hB0 hw0
  have hs0Nd : ν.s0 < Nd := by
    by_contra hge
    exact hB0 (hdev.2.1 _ (not_lt.mp hge))
  -- Ranch is a genuine ≥ 2-term pattern: coeff 0 ≠ 0 and natDegree ≥ 1
  have hR0ne : ν.Ranch.coeff 0 ≠ 0 := hanch.1
  have hRanchNe : ν.Ranch ≠ 0 := fun h0 => hR0ne (by rw [h0, Polynomial.coeff_zero])
  have hRdeg : 1 ≤ ν.Ranch.natDegree := by
    have hle := Polynomial.natDegree_le_of_dvd hord.1 hRanchNe
    rw [Polynomial.natDegree_pow, ν.hψdeg] at hle
    have hμ1 := ν.hμ
    have hg1 := ν.hg
    have hμg : 1 ≤ ν.μ * ν.g := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  -- the frame values strictly ascend rightward of s0 (and hcon fences the left)
  have hframe : ∀ j : ℕ, j < Nd → B j ≠ 0 → j ≠ ν.s0 →
      ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ) < ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) := by
    intro j hjNd hBj hjne
    rcases lt_or_gt_of_ne hjne with hlt | hgt
    · exact hcon j hlt hBj
    · -- j > s0: e·(frame j − frame s0) = (G(j) − γ) + (e − 1)·(j − s0)·h ≥ 1
      have hGj := hsr.1.1 j hjNd hBj
      have hE1 : (1 : ℤ) ≤ (ν.e : ℤ) := by exact_mod_cast ν.he
      have hh1 : (1 : ℤ) ≤ (ν.h : ℤ) := by exact_mod_cast ν.hh
      have hjs : (ν.s0 : ℤ) < (j : ℤ) := by exact_mod_cast hgt
      have he2' : (2 : ℤ) ≤ (ν.e : ℤ) := by exact_mod_cast he2
      have hP : (1 : ℤ) ≤ ((ν.e : ℤ) - 1) * (((j : ℤ) - (ν.s0 : ℤ)) * (ν.h : ℤ)) := by
        have f1 : (1 : ℤ) ≤ (ν.e : ℤ) - 1 := by omega
        have f2 : (1 : ℤ) ≤ ((j : ℤ) - (ν.s0 : ℤ)) * (ν.h : ℤ) := by
          have : (1 : ℤ) ≤ (j : ℤ) - (ν.s0 : ℤ) := by omega
          nlinarith
        nlinarith
      have hexpand : (ν.e : ℤ) * ((ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ))
            - (ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ)))
          = ((ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) - ν.gam)
            + ((ν.e : ℤ) - 1) * (((j : ℤ) - (ν.s0 : ℤ)) * (ν.h : ℤ)) := by
        rw [← hw0]; ring
      have hpos : (1 : ℤ) ≤ (ν.e : ℤ) * ((ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ))
          - (ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ))) := by
        rw [hexpand]
        linarith
      by_contra hle
      push_neg at hle
      have hnp : (ν.e : ℤ) * ((ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ))
          - (ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by linarith)
      linarith
  -- the split of the window sum at s0
  set f : Polynomial ℤ_[p] := ∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j with hf
  have hfsplit : f = B ν.s0 * ν.σ.Φ ^ ν.s0
      + ∑ j ∈ (Finset.range Nd).erase ν.s0, B j * ν.σ.Φ ^ j := by
    rw [hf]
    exact (Finset.add_sum_erase _ _ (Finset.mem_range.mpr hs0Nd)).symm
  have hterm0ne : B ν.s0 * ν.σ.Φ ^ ν.s0 ≠ 0 := mul_ne_zero hB0 (pow_ne_zero _ hΦne)
  have hterm0w : ν.σ.w (B ν.s0 * ν.σ.Φ ^ ν.s0)
      = ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ) := by
    rw [term_w ν.σ _ hB0 ν.s0, hsh]
  -- f ≠ 0 (else the anchor forces Ranch = 0)
  have hfne : f ≠ 0 := by
    intro h0
    have hRf : ν.σ.R f = 0 := by rw [h0]; exact ν.σ.hR0
    rw [hRf] at hanch
    have h1 : (LaurentPolynomial.T (-ν.a) : LaurentPolynomial ↥ν.σ.K) * 0
        = LaurentPolynomial.T (-ν.a)
          * (LaurentPolynomial.T ν.a * Polynomial.toLaurent ν.Ranch) := by
      rw [← hanch.2]
    rw [mul_zero, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h1
    exact hRanchNe (Polynomial.toLaurent_injective (by rw [← h1, map_zero]))
  -- σ.R f = the single (S5) monomial of the window base
  have hRf_mono : ν.σ.R f = ν.σ.R (B ν.s0 * ν.σ.Φ ^ ν.s0) := by
    by_cases hrest : (∑ j ∈ (Finset.range Nd).erase ν.s0, B j * ν.σ.Φ ^ j) = 0
    · rw [hfsplit, hrest, add_zero]
    · have hrw : ν.σ.w (B ν.s0 * ν.σ.Φ ^ ν.s0)
          < ν.σ.w (∑ j ∈ (Finset.range Nd).erase ν.s0, B j * ν.σ.Φ ^ j) := by
        have hge : ν.σ.w (B ν.s0) + (ν.s0 : ℤ) * (ν.h : ℤ) + 1
            ≤ ν.σ.w (∑ j ∈ (Finset.range Nd).erase ν.s0, B j * ν.σ.Φ ^ j) := by
          refine ResVal.w_sum_ge ν.σ _ _ _ ?_ hrest
          intro j hj hne
          have hjNd : j < Nd := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
          have hjne : j ≠ ν.s0 := Finset.ne_of_mem_erase hj
          have hBj : B j ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
          have hstrict := hframe j hjNd hBj hjne
          rw [term_w ν.σ _ hBj j, hsh]
          linarith
        rw [hterm0w]
        linarith
      rw [hfsplit]
      exact ν.σ.hRlt _ _ hterm0ne hrest (by rw [← hfsplit]; exact hfne) hrw
  obtain ⟨c, hc⟩ := ν.σ.hS5 (B ν.s0) hB0 (hdev.1 _)
  have hRf_single : ν.σ.R f = LaurentPolynomial.C ((c : ↥ν.σ.K))
      * LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (B ν.s0) + (ν.s0 : ℤ) * ν.σ.s) := by
    rw [hRf_mono, ν.σ.hRmul _ _ hB0 (pow_ne_zero _ hΦne), ResVal.R_pow ν.σ _ hΦne,
      ν.σ.hRΦ, hc, LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add]
  -- the anchor equation: toLaurent Ranch = C c · T (m − a)
  set m : ℤ := - ν.σ.t * ν.σ.wPrev (B ν.s0) + (ν.s0 : ℤ) * ν.σ.s with hm
  have hanch2 : Polynomial.toLaurent ν.Ranch
      = LaurentPolynomial.C ((c : ↥ν.σ.K)) * LaurentPolynomial.T (m - ν.a) := by
    have h1 : Polynomial.toLaurent ν.Ranch
        = LaurentPolynomial.T (-ν.a)
          * (LaurentPolynomial.C ((c : ↥ν.σ.K)) * LaurentPolynomial.T m) := by
      have h0 : (LaurentPolynomial.T (-ν.a) : LaurentPolynomial ↥ν.σ.K)
          * (LaurentPolynomial.T ν.a * Polynomial.toLaurent ν.Ranch)
          = LaurentPolynomial.T (-ν.a)
            * (LaurentPolynomial.C ((c : ↥ν.σ.K)) * LaurentPolynomial.T m) := by
        rw [← hanch.2, ← hRf_single]
      rwa [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
        LaurentPolynomial.T_zero, one_mul] at h0
    rw [h1, ← mul_assoc, mul_comm (LaurentPolynomial.T (-ν.a)) (LaurentPolynomial.C _),
      mul_assoc, ← LaurentPolynomial.T_add,
      show -ν.a + m = m - ν.a by ring]
  -- monomial vs ≥ 2-term pattern: the contradiction
  have hcne : ((c : ↥ν.σ.K)) ≠ 0 := c.ne_zero
  by_cases hcase : ν.a ≤ m
  · -- m − a ≥ 0: Ranch IS a monomial of degree m − a; coeff 0 ≠ 0 forces degree 0
    set d : ℕ := (m - ν.a).toNat with hd
    have hdZ : ((d : ℕ) : ℤ) = m - ν.a := Int.toNat_of_nonneg (by omega)
    have hmono : Polynomial.toLaurent ν.Ranch
        = Polynomial.toLaurent (Polynomial.monomial d ((c : ↥ν.σ.K))) := by
      rw [hanch2, Polynomial.toLaurent_C_mul_T, hdZ]
    have hRanchEq : ν.Ranch = Polynomial.monomial d ((c : ↥ν.σ.K)) :=
      Polynomial.toLaurent_injective hmono
    have hcoeff0 := hR0ne
    rw [hRanchEq, Polynomial.coeff_monomial] at hcoeff0
    have hd0 : d = 0 := by
      by_contra hne
      exact hcoeff0 (by rw [if_neg hne])
    rw [hRanchEq, hd0] at hRdeg
    simp [Polynomial.natDegree_monomial] at hRdeg
  · -- m − a < 0: X^{a−m}·Ranch = C c, impossible (coeff 0 of LHS is 0, c ≠ 0)
    push_neg at hcase
    set k : ℕ := (ν.a - m).toNat with hk
    have hkZ : ((k : ℕ) : ℤ) = ν.a - m := Int.toNat_of_nonneg (by omega)
    have hk1 : 1 ≤ k := by omega
    have hprod : Polynomial.toLaurent ((Polynomial.X : Polynomial ↥ν.σ.K) ^ k * ν.Ranch)
        = Polynomial.toLaurent (Polynomial.C ((c : ↥ν.σ.K))) := by
      rw [map_mul, Polynomial.toLaurent_X_pow, hanch2, Polynomial.toLaurent_C,
        ← mul_assoc,
        mul_comm (LaurentPolynomial.T (k : ℤ)) (LaurentPolynomial.C ((c : ↥ν.σ.K))),
        mul_assoc, ← LaurentPolynomial.T_add, hkZ,
        show ν.a - m + (m - ν.a) = 0 by ring, LaurentPolynomial.T_zero, mul_one]
    have hpoly : (Polynomial.X : Polynomial ↥ν.σ.K) ^ k * ν.Ranch
        = Polynomial.C ((c : ↥ν.σ.K)) := Polynomial.toLaurent_injective hprod
    have hcoeff : ((Polynomial.X : Polynomial ↥ν.σ.K) ^ k * ν.Ranch).coeff 0 = 0 := by
      have hdvd : (Polynomial.X : Polynomial ↥ν.σ.K) ∣ Polynomial.X ^ k * ν.Ranch :=
        Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
      exact Polynomial.X_dvd_iff.mp hdvd
    rw [hpoly, Polynomial.coeff_C_zero] at hcoeff
    exact hcne hcoeff

/-- **The s0 = 0 kill**: at a window starting at slot 0 there is nothing below the
window — SideReads at an e′ ≥ 2 (S-a)-stretched read is UNSATISFIABLE. -/
theorem sideReads_unsat_e2_s0_zero (ν : Node p F) (hse : ν.σ.e = ν.e)
    (hsh : ν.σ.h = ν.h) (he2 : 2 ≤ ν.e) (hs0 : ν.s0 = 0)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hdev : IsDevelopment ν.σ.Φ (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) B Nd)
    (hsr : SideReads ν B Nd Φnext) : False := by
  obtain ⟨j, hj, -, -⟩ := sideReads_belowWindow_tie ν hse hsh he2 B Nd Φnext hdev hsr
  omega

/-! ### §B — the history-level fence: `ReadsOf` emptiness at s0 = 0, e′ ≥ 2 child reads -/

/-- **`ReadsOf` is EMPTY at every coherent record whose non-recentering-parented child
read has `e ≥ 2` and window base `s0 = 0`** — the HK23-gate carrier family shape.  The
`child_e`/`child_h` legs of the (S-a) transition supply the stretch keying; the s0 = 0
kill does the rest.  This is the compiled reason the HK-12 F4 "full refutation residual"
(a ReadsOf countermodel on the H₂ram shape) CANNOT be built. -/
theorem readsOf_e2_s0_zero_empty {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (he2 : 2 ≤ (H.nodes[i+1]'hi1).e)
    (hs0 : (H.nodes[i+1]'hi1).s0 = 0) : False := by
  obtain ⟨-, -, hcoh, hreads⟩ := h
  obtain ⟨-, σV, -, -, htcore⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  have hse : (H.nodes[i+1]'hi1).σ.e = (H.nodes[i+1]'hi1).e := htcore.base.child_e
  have hsh : (H.nodes[i+1]'hi1).σ.h = (H.nodes[i+1]'hi1).h := htcore.base.child_h
  obtain ⟨B, Nd, Φnext, hdev, -, hsr⟩ := hreads (i+1) hi1
  have hdev' : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ
      (∑ j ∈ Finset.range Nd, B j * (H.nodes[i+1]'hi1).σ.Φ ^ j) B Nd :=
    ⟨hdev.1, hdev.2.1, rfl⟩
  exact sideReads_unsat_e2_s0_zero _ hse hsh he2 hs0 B Nd Φnext hdev' hsr

/-! ### §C — the corrected all-e′ consumption shapes + the vertex iff-zero reduction
(the re-key design, compiled; private copies of HK11a's in-file arithmetic) -/

/-- `strFrame` recursion (private copy of the V9/HK11a lemma). -/
private lemma strFrame_succ' (H : History p F) (k : ℕ) (hk : k < H.nodes.length) :
    H.strFrame (k + 1) = H.strFrame k * (H.nodes[k]'hk).e := by
  unfold History.strFrame
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [List.map_append, List.prod_append, Option.toList_some, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- `strFrame` is positive (private copy of V9's `v9_strFrame_pos`). -/
private lemma strFrame_pos' (H : History p F) (i : ℕ) : 0 < H.strFrame i := by
  unfold History.strFrame
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨ν, -, hν0⟩ := List.mem_map.mp h0
  exact absurd hν0.symm (by have := ν.he; omega)

/-- The recorded side value at a child-width base index, child-stage scale (private
copy of HK11a's `lineAt_arith` — the K1_SAE γ-tie + slope-law + `hLineU` pattern). -/
private lemma lineAt_arith' {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hilen : i < H.nodes.length) (hi1 : i + 1 < H.nodes.length) (j : ℕ) :
    ((H.nodes[i]'hilen).gam : ℚ)
      - (j : ℚ) * (((H.nodes[i]'hilen).e : ℚ) * ((H.nodes[i]'hilen).h : ℚ)
          * ((H.nodes[i]'hilen).g : ℚ))
      = (H.strFrame (i+1) : ℚ)
        * (H.nodes[i]'hilen).line.at (j * (H.nodes[i]'hilen).childWidth) := by
  have hγ := hcoh.2.2.1 i hilen
  have hsl := hcoh.2.1 i hilen
  have hu := (H.nodes[i]'hilen).hLineU
  have hDw := (H.nodes[i]'hilen).hDwidth
  rw [strFrame_succ' H i hilen]
  simp only [Line.at, Node.childWidth] at hu ⊢
  push_cast at hγ hsl hu ⊢
  linear_combination hγ
    - ((H.strFrame i : ℚ) * (((H.nodes[i]'hilen).e : ℕ) : ℚ)) * hu
    + (((j : ℚ) * (((H.nodes[i]'hilen).e : ℕ) : ℚ) * (((H.nodes[i]'hilen).g : ℕ) : ℚ))
      - ((((H.nodes[i]'hilen).s0 : ℕ) : ℚ) + (((H.nodes[i]'hilen).wSide : ℕ) : ℚ))) * hsl

/-- **THE CORRECTED VERTEX DISPLAY — ALL e′** (the re-key design of the ruling): under
the (S-a) keying the vertex coefficient's child weight is the parent line's vertex value
at the NEXT frame's scale,

    `σ_{i+1}.w (B μᵢ) = strFrame(i+2) · lineᵢ.at(μᵢ·childWidthᵢ)`

(`strFrame(i+2) = strFrame(i+1)·ν_{i+1}.e` — the stretch absorbed into the scale).
Binders and carried hypotheses exactly `HK11a.readVertex_e1`'s MINUS `he'1`; at
`ν_{i+1}.e = 1` this IS V9's displayed form.  ⚠ NOT a V9 fill (V9 displays the
strFrame(i+1) scale); this is the statement the corpus re-keys TO if the e′ ≥ 2
perimeter is ever repopulated. -/
theorem readVertex_stretch {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+2) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  classical
  have hilen : i < H.nodes.length := by omega
  have hcoh := h.2.2.1
  obtain ⟨-, σV, hregV, -, htcore⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  obtain ⟨hBμne, hvertex, -⟩ :=
    HK11a.sigmaV_vertexLaw h i hi1 hsp hσL hsteep B Nd hdev σV hregV
  refine ⟨hBμne, ?_⟩
  have hin : inC (H.nodes[i+1]'hi1).σ.Φ (B ((H.nodes[i]'hilen).μ)) := hdev.1 _
  have hstretch := HK52.hk52_qform_stretch htcore _ hBμne hin
  have harith := lineAt_arith' hcoh i hilen hi1 (H.nodes[i]'hilen).μ
  have hsucc : H.strFrame (i+2) = H.strFrame (i+1) * (H.nodes[i+1]'hi1).e :=
    strFrame_succ' H (i+1) hi1
  rw [hstretch, hvertex, hsucc]
  push_cast
  linear_combination ((H.nodes[i+1]'hi1).e : ℚ) * harith

/-- **The corrected BOX display — all e′**: every slot strictly below the vertex weighs
strictly above the parent line at the NEXT frame's scale (the strict leg of the kernel
through the stretch; `ν_{i+1}.e ≥ 1` preserves the strict inequality). -/
theorem readBox_stretch {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (j : ℕ) (hjμ : j < (H.nodes[i]'(by omega)).μ) (hjne : B j ≠ 0) :
    (H.strFrame (i+2) : ℚ) *
        (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
      < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  classical
  have hilen : i < H.nodes.length := by omega
  have hcoh := h.2.2.1
  obtain ⟨-, σV, hregV, -, htcore⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  obtain ⟨-, -, hbox⟩ :=
    HK11a.sigmaV_vertexLaw h i hi1 hsp hσL hsteep B Nd hdev σV hregV
  have h1 := hbox j hjμ hjne
  have hin : inC (H.nodes[i+1]'hi1).σ.Φ (B j) := hdev.1 _
  have hstretch := HK52.hk52_qform_stretch htcore _ hjne hin
  have harith := lineAt_arith' hcoh i hilen hi1 j
  have hsucc : H.strFrame (i+2) = H.strFrame (i+1) * (H.nodes[i+1]'hi1).e :=
    strFrame_succ' H (i+1) hi1
  have he1 : (1 : ℤ) ≤ ((H.nodes[i+1]'hi1).e : ℤ) := by
    exact_mod_cast (H.nodes[i+1]'hi1).he
  have hZ : ((H.nodes[i+1]'hi1).e : ℤ)
        * ((H.nodes[i]'hilen).gam
          - (j : ℤ) * (((H.nodes[i]'hilen).e : ℤ) * ((H.nodes[i]'hilen).h : ℤ)
            * ((H.nodes[i]'hilen).g : ℤ)))
      < ((H.nodes[i+1]'hi1).σ.w (B j) : ℤ) := by
    rw [hstretch]
    have hepos : (0 : ℤ) < ((H.nodes[i+1]'hi1).e : ℤ) := by omega
    exact mul_lt_mul_of_pos_left h1 hepos
  have hQ : (((H.nodes[i+1]'hi1).e : ℚ))
        * (((H.nodes[i]'hilen).gam : ℚ)
          - (j : ℚ) * (((H.nodes[i]'hilen).e : ℚ) * ((H.nodes[i]'hilen).h : ℚ)
            * ((H.nodes[i]'hilen).g : ℚ)))
      < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by exact_mod_cast hZ
  rw [harith] at hQ
  rw [hsucc]
  calc ((H.strFrame (i+1) * (H.nodes[i+1]'hi1).e : ℕ) : ℚ) *
        (H.nodes[i]'hilen).line.at (j * (H.nodes[i]'hilen).childWidth)
      = (((H.nodes[i+1]'hi1).e : ℚ)) * ((H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'hilen).line.at (j * (H.nodes[i]'hilen).childWidth)) := by
        push_cast; ring
    _ < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := hQ

/-- **The vertex iff-zero reduction at e′ ≥ 2** (the exact residue of the FALSE-SUSPECT
mapping): on the kernel's perimeter (strict steepness + `StageCoreL`, e′ ≥ 2), V9's
DISPLAYED ℚ-form at the vertex holds IFF the parent line VANISHES there.  So the
displayed statements are false exactly on {e′ ≥ 2} ∩ {ReadsOf inhabited} ∩
{lineᵢ.at(μ·cwᵢ) ≠ 0} — and §A/§B fence the middle factor to below-window
conspiracies. -/
theorem displayed_iff_lineZero {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (he2 : 2 ≤ (H.nodes[i+1]'hi1).e)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    ((((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth))
      ↔ (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) = 0 := by
  classical
  have hilen : i < H.nodes.length := by omega
  obtain ⟨-, hcorrect⟩ := readVertex_stretch h i hi1 hsp hσL hsteep B Nd hdev hNd
  have hsucc : H.strFrame (i+2) = H.strFrame (i+1) * (H.nodes[i+1]'hi1).e :=
    strFrame_succ' H (i+1) hi1
  have hstrpos : (0 : ℚ) < (H.strFrame (i+1) : ℚ) := by
    exact_mod_cast strFrame_pos' H (i+1)
  have he2' : (2 : ℚ) ≤ ((H.nodes[i+1]'hi1).e : ℚ) := by exact_mod_cast he2
  rw [hsucc] at hcorrect
  push_cast at hcorrect
  constructor
  · intro hdisp
    -- strF(i+1)·L = strF(i+1)·e′·L  ⟹  strF(i+1)·(e′−1)·L = 0 ⟹ L = 0
    have hfac : (H.strFrame (i+1) : ℚ) * (((H.nodes[i+1]'hi1).e : ℚ) - 1)
        * (H.nodes[i]'hilen).line.at
            ((H.nodes[i]'hilen).μ * (H.nodes[i]'hilen).childWidth) = 0 := by
      linear_combination hdisp - hcorrect
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exfalso
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · linarith
    · exact h0
  · intro hzero
    have hzero' : (H.nodes[i]'hilen).line.at
        ((H.nodes[i]'hilen).μ * (H.nodes[i]'hilen).childWidth) = 0 := hzero
    linear_combination hcorrect
      + ((H.strFrame (i+1) : ℚ) * ((H.nodes[i+1]'hi1).e : ℚ)
        - (H.strFrame (i+1) : ℚ)) * hzero'

end HK53

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK53.digit_stride_dvd
#print axioms LeanUrat.MovesJ.HK53.width_sq_dvd
#print axioms LeanUrat.MovesJ.HK53.sideReads_belowWindow_tie
#print axioms LeanUrat.MovesJ.HK53.sideReads_unsat_e2_s0_zero
#print axioms LeanUrat.MovesJ.HK53.readsOf_e2_s0_zero_empty
#print axioms LeanUrat.MovesJ.HK53.readVertex_stretch
#print axioms LeanUrat.MovesJ.HK53.readBox_stretch
#print axioms LeanUrat.MovesJ.HK53.displayed_iff_lineZero
