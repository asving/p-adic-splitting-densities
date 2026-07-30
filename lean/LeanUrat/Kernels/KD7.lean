/-
Kernels/KD7 — BP4-c7 E-phase skeleton for unit KD7 [ATTEMPT]: the weight cap
via the different budget — w_final ≤ c(n)·(1 + v_p(disc f)) through (P2)'s
budget (L5fix Invariant-2).  THE DEEP OPEN CORE of the KD cluster
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D + §4 KD7; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

GATE SEQUENCING (REV 2, F5): the CM-first twin KD9 (sibling, python: fit
w_final against 1 + vdisc f, search super-linear growth — a finding refutes
every constant c(n) candidate) runs BEFORE any prover is assigned here.

RECORDED RESOLUTIONS (statement transcription):
· The KD7 TARGET is the named Prop `WeightCapP` below — the blueprint's
  "w_final ≤ c(n)·(1 + vdisc f)" verbatim over the KD6 carrier, per stratum
  history, off discZero (the (CD)-pinned population/guard genre of the
  MovesX kernel Props).
· (P2)'s consumable — v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ) — is typed
  at its ONLY in-corpus face: `GMNIndex.ind` with the `p2` law
  2·ind f ≤ vdisc f (MovesX/Defs.lean:205-209).  The named budget carrier
  `DifferentBudget` (⚑, Q4 hypothesis shape) bounds the key weight by
  c₁·(1 + ind f); the theorem transports it to `WeightCapP` through `p2`.
  The FINER leaf-different face (Σᵢ v_p(disc Lᵢ), L5fix Invariant-2) has NO
  vocabulary over `MonicBox` in any corpus — L5fix's carrier is its own; if
  the prover's attempt needs that finer face, THAT is the pre-declared
  fallback obstruction record ("the exact budget consumable that fails to
  be exhibited, not assumed" — MOVES 11166 via the blueprint).
· The ATTEMPT proper = exhibiting a `DifferentBudget` instance for the real
  key weight (the deep open core); the Lean head here is the typed
  transport, so the attempt surface is exactly the budget field.

deps: KD9 (CM gate — runs FIRST; sibling, python), KD6 (the carrier);
L5fix vocabulary (LeanUrat/L5fix.lean) — attempt material, not imported at
statement time (see the resolution above).
Consumers: KD10 (`weightChargeFull_of_ladderCap`).

Build: cd lean && lake build LeanUrat.Kernels.KD7
-/
import LeanUrat.Kernels.KD6

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

/-- KD7 (the TARGET Prop — blueprint display "w_final ≤ c(n)·(1 + vdisc f)"):
the key weight of every stratum history of f (off discZero) is capped
affinely in the discriminant depth. -/
def WeightCapP (n : ℕ) (X : MovesX.XFamily n) (KW : KeyWeightData n)
    (c : ℚ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (H : MovesX.XHistory n),
    f ∉ MovesX.discZero n p → (X.gmn p).inStratum f H →
      KW.w H ≤ c * (1 + (MovesX.vdisc f : ℚ))

/-- KD7 (⚑ the named budget carrier — the (P2) consumable at its typed
face): the key weight is bounded by c₁·(1 + ind f) per stratum history —
each unit of key-weight climb consumes a unit of the monotone (P2)/index
budget.  Exhibiting an instance for the real key weight IS the deep open
attempt; see the file header for the leaf-different-face fallback. -/
structure DifferentBudget (n : ℕ) (X : MovesX.XFamily n)
    (KW : KeyWeightData n) where
  c1 : ℚ
  c1_nonneg : 0 ≤ c1
  budget : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (H : MovesX.XHistory n),
    f ∉ MovesX.discZero n p → (X.gmn p).inStratum f H →
      KW.w H ≤ c1 * (1 + ((X.gmn p).ind f : ℚ))

/-- KD7 (HEAD — the typed transport): the named budget delivers the cap
with the SAME constant.  deps: `DifferentBudget`, `GMNIndex.p2`.  Sketch:
per (p, f, H): `B.budget` gives w H ≤ c₁·(1 + ind f); `(X.gmn p).p2` gives
2·ind f ≤ vdisc f off discZero, so ind f ≤ vdisc f (ℕ, ind ≥ 0); c₁ ≥ 0
makes the affine bound monotone; chain. -/
theorem kd7_weightCap_of_differentBudget {n : ℕ} (X : MovesX.XFamily n)
    (KW : KeyWeightData n) (B : DifferentBudget n X KW) :
    WeightCapP n X KW B.c1 := by
  sorry

end LeanUrat.Kernels
