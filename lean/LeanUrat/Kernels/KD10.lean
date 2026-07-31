/-
Kernels/KD10 — BP4-c7 E-phase skeleton for unit KD10 [NEW at REV 2, the F3
reroute]: `weightChargeFull_of_ladderCap` — ladder (KD6) + cap (KD7) +
REC-DISC (KD2) ⟹ WeightChargeFullP with s := 2·D(n)·c(n).  THE schedulable
X.1b discharge route — never needs a constant restart cap
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D (T-disc) + §4 KD10 + R7;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block: Q5 —
annotate the CL-2 record line at discharge time).

RECORDED RESOLUTIONS (statement transcription):
· REC-DISC (KD2's conclusion, `recentering_vdisc_pos`) is taken INLINE as
  the hypothesis `hrecdisc` — KD2 is a SIBLING-cluster unit whose file does
  not exist at this write; the statement shape below is KD2's verbatim
  (≥ 1 recentering-population node ⟹ 1 ≤ vdisc f).  When KD2 lands, the
  prover instantiates `hrecdisc` with it (no restatement needed).
· KD6's ladder and KD7's cap enter as their CONCLUSIONS (the ladder lemma
  is available as `kd6_ladder_count_le` over any `KeyWeightData`; the cap
  as the Prop `WeightCapP` — hypothesis `hcap`).
· "s := 2·D(n)·c(n)": `XConsts.s : ℕ` is existential data (risk R7 — the
  Lean Props only need SOME s), so the constant enters as the hypothesis
  `hs : 2·D·c ≤ (K.s : ℚ)` — any XConsts whose s dominates the ladder-cap
  product discharges the kernel.  The Q5-adjudicated CL-2 annotation
  ("actual discharge route = ladder-cap, not TRACK-COUNT") happens at
  discharge.
· `hc : 0 ≤ c` is required for the affine-bound monotonicity (the cap
  constant is nonnegative in every intended instantiation; KD7's
  `DifferentBudget.c1_nonneg` supplies it on the intended route).

deps: KD2 (inline premise — sibling cluster), KD6, KD7.
Consumer: KD5 (`x3aRoute_of_weightCharge_align` — the cl2_route face).
Sketch (blueprint verbatim): on a history with ≥ 1 recentering, vdisc ≥ 1
(REC-DISC), so #rec ≤ D·(w_final − w_init) ≤ D·w_final ≤ D·c·(1 + vdisc) ≤
2·D·c·vdisc ≤ s·vdisc; zero-recentering histories give count 0 ≤ anything;
cast the ℚ chain back to the ℕ statement of `WeightChargeFullP`.

Build: cd lean && lake build LeanUrat.Kernels.KD10
-/
import LeanUrat.Kernels.KD7

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

/-- KD10 (HEAD — blueprint-prescribed name `weightChargeFull_of_ladderCap`):
KeyWeightData ladder + weight cap + REC-DISC ⟹ X.1b's FULL burden
`MovesX.WeightChargeFullP` for any XConsts with s ≥ 2·D·c.  See the file
header for the recorded premise resolutions and the proof sketch. -/
theorem weightChargeFull_of_ladderCap {n : ℕ} (X : MovesX.XFamily n)
    (K : MovesX.XConsts n) (KW : KeyWeightData n) {c : ℚ} (hc : 0 ≤ c)
    (hcap : WeightCapP n X KW c)
    (hrecdisc : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
      (H : MovesX.XHistory n),
      f ∉ MovesX.discZero n p → (X.gmn p).inStratum f H →
      1 ≤ MovesX.countPop H MovesX.Pop.recT1 +
            MovesX.countPop H MovesX.Pop.t4 →
      1 ≤ MovesX.vdisc f)
    (hs : 2 * (KW.D : ℚ) * c ≤ (K.s : ℚ)) :
    MovesX.WeightChargeFullP n X K := by
  intro p hp f H hf hstrat
  rcases Nat.eq_zero_or_pos
      (MovesX.countPop H MovesX.Pop.recT1 + MovesX.countPop H MovesX.Pop.t4)
    with h0 | h1
  -- zero-recentering history: count 0 ≤ anything
  · simp only [h0]
    exact Nat.zero_le _
  -- ≥ 1 recentering: vdisc ≥ 1 (REC-DISC), then the ℚ chain
  · have hv : 1 ≤ MovesX.vdisc f := hrecdisc p f H hf hstrat h1
    have hvq : (1 : ℚ) ≤ (MovesX.vdisc f : ℚ) := by exact_mod_cast hv
    have hD : (0 : ℚ) ≤ (KW.D : ℚ) := Nat.cast_nonneg _
    have hDc : (0 : ℚ) ≤ (KW.D : ℚ) * c := mul_nonneg hD hc
    have hladder := kd6_ladder_count_le KW H
    have hcapH := hcap p f H hf hstrat
    have chain : ((MovesX.countPop H MovesX.Pop.recT1 +
          MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℚ) ≤
        (K.s : ℚ) * (MovesX.vdisc f : ℚ) := by
      calc ((MovesX.countPop H MovesX.Pop.recT1 +
              MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℚ)
          ≤ (KW.D : ℚ) * (KW.w H - KW.w []) := hladder
        _ ≤ (KW.D : ℚ) * KW.w H := by
            apply mul_le_mul_of_nonneg_left _ hD
            linarith [KW.w_nil_nonneg]
        _ ≤ (KW.D : ℚ) * (c * (1 + (MovesX.vdisc f : ℚ))) :=
            mul_le_mul_of_nonneg_left hcapH hD
        _ = ((KW.D : ℚ) * c) * (1 + (MovesX.vdisc f : ℚ)) := by ring
        _ ≤ ((KW.D : ℚ) * c) *
              ((MovesX.vdisc f : ℚ) + (MovesX.vdisc f : ℚ)) := by
            apply mul_le_mul_of_nonneg_left _ hDc
            linarith
        _ = (2 * (KW.D : ℚ) * c) * (MovesX.vdisc f : ℚ) := by ring
        _ ≤ (K.s : ℚ) * (MovesX.vdisc f : ℚ) := by
            apply mul_le_mul_of_nonneg_right hs
            linarith
    exact_mod_cast chain

end LeanUrat.Kernels
