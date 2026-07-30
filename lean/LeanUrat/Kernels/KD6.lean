/-
Kernels/KD6 — BP4-c7 E-phase skeleton for unit KD6 [ATTEMPT]: the weight
ladder — the named `KeyWeightData` carrier (D.10 DERIVED strict climb per
recentering; the (1/D(n))·ℤ lattice, the dnLattice duty) + the ladder lemma
#recenterings ≤ D(n)·(w_final − w_init)
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D (T-disc) + §4 KD6 + F3;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

STATUS FENCE (REV 2, F3 — binding): the ladder is NOT advertised as a
TRACK-COUNT route; its honest conclusion is vdisc-RELATIVE.  The KD6∘KD7
composition D(n)·c(n)·(1 + vdisc) GROWS with vdisc and CANNOT deliver the
ledger's constant-L `Cl7Kernel.track_restarts` face ((T-const) — open, no
prover assigned this campaign, risk R11, escalated cross-area to BP1).  The
schedulable consumer is KD10's WeightCharge discharge (s := 2·D(n)·c(n)).

GATE SEQUENCING (REV 2, F5): the CM-first twin KD9 (the python ladder/cap
probe: zero-ladder-gain recentering search + w_final vs 1 + vdisc fit) is a
SIBLING unit and runs BEFORE any prover is assigned here.

RECORDED RESOLUTIONS (⚑ carrier design — flagged for orchestrator
ratification per the blueprint's own "carrier design ⚑"):
· "per-node key weight" is typed as a HISTORY functional
  `w : XHistory n → ℚ` (the key weight of node data along the branch is
  p-free/f-free; per-node reads are the increments w (H ++ [ν]) − w H).
· "strict climb per recentering" is keyed to the FULL-burden populations
  `.recT1`/`.t4` (exactly the populations KD10's WeightChargeFullP
  charges), with climb quantum 1/D — the lattice makes "strict" = "≥ one
  lattice step" (the (1/D(n))·ℤ lattice as the ∃-ℤ field `lattice`).
· `mono` (no downhill steps at non-recentering nodes) is D.10's derived
  climb direction, needed for the telescoping.
· `w_nil_nonneg` (root key weight ≥ 0) is ADDED to the carrier: KD10's
  composition needs w_final − w_init ≤ w_final; part of the ⚑ ratification.

deps: KD9 (CM gate — runs FIRST; sibling, python); MovesX/Defs.lean
(`XHistory`, `XNode`, `Pop`, `popOf?`, `countPop`).
Consumers: KD7 (the cap over the same carrier), KD10 (the composition).
Fallback (blueprint verbatim): the typed carrier + the ladder lemma alone —
already useful, it converts the count into a weight-cap question.

Build: cd lean && lake build LeanUrat.Kernels.KD6
-/
import LeanUrat.MovesX.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

/-- KD6 (⚑ the named carrier `KeyWeightData` — blueprint-prescribed name):
the per-branch key-weight functional with lattice denominator D = D(n):
values in the (1/D)·ℤ lattice, never decreasing along a branch, climbing by
at least one lattice step 1/D at every recentering-population node
(`.recT1` or `.t4` — the FULL-burden populations).  D.10 DERIVED content +
the dnLattice duty, typed; see the file header for the recorded carrier
resolutions (⚑). -/
structure KeyWeightData (n : ℕ) where
  D : ℕ
  D_pos : 0 < D
  w : MovesX.XHistory n → ℚ
  w_nil_nonneg : 0 ≤ w []
  lattice : ∀ H : MovesX.XHistory n, ∃ z : ℤ, w H = (z : ℚ) / (D : ℚ)
  mono : ∀ (H : MovesX.XHistory n) (ν : MovesX.XNode n), w H ≤ w (H ++ [ν])
  climb : ∀ (H : MovesX.XHistory n) (ν : MovesX.XNode n),
    MovesX.popOf? ν = some MovesX.Pop.recT1 ∨
      MovesX.popOf? ν = some MovesX.Pop.t4 →
    w H + 1 / (D : ℚ) ≤ w (H ++ [ν])

/-- KD6 (HEAD — the ladder lemma): the recentering-population count is
bounded by D times the total key-weight climb:
#recT1(H) + #t4(H) ≤ D·(w_final − w_init).  deps: the carrier laws only.
Sketch: reverse list induction (`List.reverseRecOn`): at H ++ [ν],
`countPop` splits off the last node (List.filter append); a
recentering-population node adds 1 to the count and ≥ 1/D to w (`climb`);
any other node adds 0 and ≥ 0 (`mono`); telescope. -/
theorem kd6_ladder_count_le {n : ℕ} (KW : KeyWeightData n)
    (H : MovesX.XHistory n) :
    ((MovesX.countPop H MovesX.Pop.recT1 +
        MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℚ) ≤
      (KW.D : ℚ) * (KW.w H - KW.w []) := by
  sorry

end LeanUrat.Kernels
