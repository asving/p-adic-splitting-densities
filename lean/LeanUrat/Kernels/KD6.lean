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
KD9 PASSED 2026-07-30 (exit 0; P1: zero zero-gain recenterings over 735,744
+ 3,194,880 recentering members; P2: no super-linear cap growth, empirical
minimal c = 2/7 / 8/25; probe re-seal note: the empirical ladder weight has
zero gain AT THE KEY-CREATION node, so a real-engine instance of this
carrier needs a shifted functional, e.g. w = mu + (1/D)·#counted-nodes —
which the abstract carrier permits; see kd9_ladder_cap_probe.py header).

AS-BUILT (2026-07-30 prover pass): the ladder lemma is PROVED from the
carrier laws alone; `countKeyWeight` below is the compiled NON-VACUITY
witness for the ⚑ carrier (the count weight, D = 1) — it satisfies every
law trivially and therefore localizes the ENTIRE deep-open content of the
KD6∘KD7 route in KD7's budget field.

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

/-- `countPop` splits off a single appended node: the count grows by the
node's indicator.  (Private helper for the KD6 telescoping induction.) -/
private theorem countPop_append_singleton {n : ℕ} (H : MovesX.XHistory n)
    (ν : MovesX.XNode n) (c : MovesX.Pop) :
    MovesX.countPop (H ++ [ν]) c =
      MovesX.countPop H c + (if MovesX.popOf? ν = some c then 1 else 0) := by
  simp only [MovesX.countPop, List.filter_append, List.length_append,
    List.filter_singleton]
  by_cases h : MovesX.popOf? ν = some c
  · simp [h]
  · simp [h]

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
  have hD : (0 : ℚ) ≤ (KW.D : ℚ) := Nat.cast_nonneg _
  have hDne : (KW.D : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp KW.D_pos
  induction H using List.reverseRecOn with
  | nil => simp [MovesX.countPop]
  | append_singleton H ν ih =>
    rw [countPop_append_singleton, countPop_append_singleton]
    by_cases hpop : MovesX.popOf? ν = some MovesX.Pop.recT1 ∨
        MovesX.popOf? ν = some MovesX.Pop.t4
    · -- recentering-population node: count +1, weight climbs by ≥ 1/D
      have hclimb := KW.climb H ν hpop
      have hcnt : MovesX.countPop H MovesX.Pop.recT1 +
            (if MovesX.popOf? ν = some MovesX.Pop.recT1 then 1 else 0) +
          (MovesX.countPop H MovesX.Pop.t4 +
            (if MovesX.popOf? ν = some MovesX.Pop.t4 then 1 else 0)) =
          (MovesX.countPop H MovesX.Pop.recT1 +
            MovesX.countPop H MovesX.Pop.t4) + 1 := by
        rcases hpop with h | h <;> simp [h] <;> omega
      rw [hcnt]
      push_cast at ih ⊢
      calc (MovesX.countPop H MovesX.Pop.recT1 : ℚ) +
            (MovesX.countPop H MovesX.Pop.t4 : ℚ) + 1
          ≤ (KW.D : ℚ) * (KW.w H - KW.w []) + 1 := by linarith [ih]
        _ = (KW.D : ℚ) * (KW.w H + 1 / (KW.D : ℚ) - KW.w []) := by
            field_simp
            ring
        _ ≤ (KW.D : ℚ) * (KW.w (H ++ [ν]) - KW.w []) := by
            apply mul_le_mul_of_nonneg_left _ hD
            linarith [hclimb]
    · -- any other node: count unchanged, weight does not decrease
      rw [not_or] at hpop
      rw [if_neg hpop.1, if_neg hpop.2]
      have hmono := KW.mono H ν
      calc ((MovesX.countPop H MovesX.Pop.recT1 + 0 +
              (MovesX.countPop H MovesX.Pop.t4 + 0) : ℕ) : ℚ)
          = ((MovesX.countPop H MovesX.Pop.recT1 +
              MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℚ) := by push_cast; ring
        _ ≤ (KW.D : ℚ) * (KW.w H - KW.w []) := ih
        _ ≤ (KW.D : ℚ) * (KW.w (H ++ [ν]) - KW.w []) := by
            apply mul_le_mul_of_nonneg_left _ hD
            linarith [hmono]

/-- Non-vacuity witness for the ⚑ carrier (compiled record, part of the
ratification packet): the COUNT key weight w H := #recT1(H) + #t4(H)
inhabits `KeyWeightData` with lattice denominator D = 1 — every law holds
trivially.  Consequence recorded for the campaign: the carrier itself is
free; for THIS w the KD7 budget field `DifferentBudget.budget` IS the
population-vs-index charge, so the entire deep-open content of the ladder-
cap route lives in exhibiting the budget (KD7's obstruction record). -/
noncomputable def countKeyWeight (n : ℕ) : KeyWeightData n where
  D := 1
  D_pos := one_pos
  w H := ((MovesX.countPop H MovesX.Pop.recT1 +
      MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℚ)
  w_nil_nonneg := by positivity
  lattice H := ⟨((MovesX.countPop H MovesX.Pop.recT1 +
      MovesX.countPop H MovesX.Pop.t4 : ℕ) : ℤ), by push_cast; norm_num⟩
  mono H ν := by
    have h : MovesX.countPop H MovesX.Pop.recT1 +
          MovesX.countPop H MovesX.Pop.t4 ≤
        MovesX.countPop (H ++ [ν]) MovesX.Pop.recT1 +
          MovesX.countPop (H ++ [ν]) MovesX.Pop.t4 := by
      rw [countPop_append_singleton, countPop_append_singleton]
      split_ifs <;> omega
    exact_mod_cast h
  climb H ν hpop := by
    have h : MovesX.countPop H MovesX.Pop.recT1 +
          MovesX.countPop H MovesX.Pop.t4 + 1 ≤
        MovesX.countPop (H ++ [ν]) MovesX.Pop.recT1 +
          MovesX.countPop (H ++ [ν]) MovesX.Pop.t4 := by
      rw [countPop_append_singleton, countPop_append_singleton]
      rcases hpop with hh | hh <;> simp [hh]
    have hq : ((MovesX.countPop H MovesX.Pop.recT1 +
          MovesX.countPop H MovesX.Pop.t4 + 1 : ℕ) : ℚ) ≤
        ((MovesX.countPop (H ++ [ν]) MovesX.Pop.recT1 +
          MovesX.countPop (H ++ [ν]) MovesX.Pop.t4 : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at hq ⊢
    norm_num
    linarith

end LeanUrat.Kernels
