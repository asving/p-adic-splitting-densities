/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesS.N2PolyGeom

/-!
# SYN2-K2 — THE cl6 (PolyGeomLaws) INSTANCE-DISCHARGE PROBE at n = 2

Instance-tier discharge probe per `lean/notes/SYNTHESIS_PASS2_2026-07-31.md`
P2-C3(b) (unit SYN2-K2), executing the `BridgeKernels.cl6` row's Q6 record
("if the S-area proves it at the real pack, the row moves out").  CHARGE:
construct `Nonempty (MovesS.PolyGeomLaws n2T n2M n2RB)` with `tCount` := the
evaluated counts (≡ 1 at this instance).

## PROBE HISTORY + THE QUEUE-ITEM-10 REPAIR (dated record)

**PROBE VERDICT (2026-07-31, pre-repair): REFUTED AT THE AS-BUILT PACK.**
The compiled `n2_polyGeomLaws_isEmpty : IsEmpty (PolyGeomLaws n2T n2M n2RB)`
(this file's git history, commit a5270df's tree) exhibited the obstruction:
`scount_val` pins `countS` against the cell-fiber census at EVERY (e, τ, o) —
including the e ≠ 2 roster PADDING rows, whose cell fibers are EMPTY but whose
presentation `pgZero = pgDiv 0 1 0` carried `countS = 1` (the `pgDiv`
constructor pinned `countS := 1` uniformly).  At (e, o, q₀) = (1, 1, 2) the law
demanded 1 = 0.  The failure was value-law-invisible (`pgZero.val = 0` either
way) and confined to padding rows.

**M1-HYGIENE NOTE (2026-07-31): the compiled IsEmpty probe refuted the
PRE-REPAIR pack ONLY — the form with `pgZero.countS = 1` as built by the
uniform `pgDiv` constructor.**  Queue item 10 (Asvin sign-off 2026-07-31,
BRIDGE_ADJUDICATIONS_2026-07-30.md) executed the recorded repair in the same
commit that rewrites this leaf: `pgZero.countS := 0` in
`MovesS/N2PolyGeom.lean` — private, VAL-PRESERVING (`pgZero.val = 0` either
way; degree pins kept, `natDegree 0 = 0`), grep-verified consumer-free on
`countS`.  The refuted statement is not restatable at HEAD (the pack
definition changed), so the IsEmpty artifact lives in git history; this leaf
now carries the POSITIVE discharge.

**POST-REPAIR VERDICT (this file, compiled): the repaired pack SATISFIES the
count laws.**  `n2_countLaws_block2` (the confinement half, unchanged) shows
both count laws at the operative block-2 layer; `n2_polyGeomLaws_nonempty`
(NEW) assembles the FULL witness `Nonempty (PolyGeomLaws n2T n2M n2RB)` with
`tCount ≡ 1` from the repair companions `n2_tcount_val`/`n2_scount_val`
(N2PolyGeom.lean — the presentation constants are private there).  The
`BridgeKernels.cl6` row's pre-authorized "moves out" clause now has its
instance evidence: the final n = 2 wiring MAY instantiate `cl6` at the
repaired pack by this witness.

No sorries in this file; both artifacts are Lean-core.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open LeanUrat.MovesS

/-! ## The confinement half — both count laws HOLD at the block-2 layer
(unchanged from the pre-repair probe: block 2 never carried the failure) -/

/-- The block-2 cell fibers are singletons: `cellOut` is the identity on the
    three-cell carrier (`c.1 % 3 = c.1` below 3), so each roster outcome's
    fiber is exactly its own cell. -/
private lemma n2_cells_block2 (v : ℕ) (hv : v < 3) :
    n2M.cells 2 n2τ (show n2T.Out 2 n2τ from ⟨v, hv⟩)
      = {(show n2M.Cell 2 n2τ from ⟨v, hv⟩)} := by
  ext c
  simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
    Finset.mem_singleton]
  constructor
  · intro h
    have h1 : c.1 % 3 = v := congrArg Fin.val h
    have h2 : c.1 < 3 := c.2
    refine Fin.ext ?_
    change c.1 = v
    omega
  · rintro rfl
    refine Fin.ext ?_
    change v % 3 = v
    omega

/-- **SYN2-K2, the confinement half**: at the block-2 layer (THE operative
    layer — the three real roster rows o_K/o_spl/o_in) BOTH CL-6 count laws
    hold with the evaluated counts: `countT ≡ 1` is integer-valued at every
    q₀ (`tcount_val`'s shape with `tCount ≡ 1`), and `countS ≡ 1` equals the
    singleton cell-fiber census (`scount_val`'s shape).  [POST-REPAIR RE-RUN
    2026-07-31: still GREEN — the queue-item-10 `pgZero.countS := 0` repair
    touches only the e ≠ 2 padding rows, invisible here.] -/
theorem n2_countLaws_block2 (o : n2T.Out 2 n2τ) (q₀ : ℚ) :
    (n2RB.tgP 2 n2τ o).countT.eval q₀ = ((1 : ℕ) : ℚ) ∧
    (n2RB.tgP 2 n2τ o).countS.eval q₀
      = ∑ c ∈ n2M.cells 2 n2τ o,
          ((n2M.cellInst 2 n2τ c q₀ (n2M.cellLvl 2 n2τ c)).card : ℚ) := by
  rcases o with ⟨v, hv⟩
  constructor
  · -- countT ≡ 1 at each of the three roster rows (pgK/pgSpl/pgIn are all
    -- `pgDiv`, countT := 1).
    interval_cases v <;>
      · change (1 : Polynomial ℚ).eval q₀ = ((1 : ℕ) : ℚ)
        simp
  · rw [n2_cells_block2 v hv, Finset.sum_singleton]
    have hcard : (n2M.cellInst 2 n2τ (show n2M.Cell 2 n2τ from ⟨v, hv⟩) q₀
        (n2M.cellLvl 2 n2τ (show n2M.Cell 2 n2τ from ⟨v, hv⟩))).card = 1 :=
      Finset.card_singleton _
    rw [hcard]
    interval_cases v <;>
      · change (1 : Polynomial ℚ).eval q₀ = ((1 : ℕ) : ℚ)
        simp

/-! ## The positive half (queue item 10, 2026-07-31) — the FULL witness at the
repaired pack.  This replaces the pre-repair `n2_polyGeomLaws_isEmpty`
refutation (git history; see the M1-hygiene note in the header). -/

/-- **SYN2-K2 DISCHARGE, COMPILED (post-repair)**: the repaired n = 2 pack
    inhabits `PolyGeomLaws` — THE `BridgeKernels.cl6` instance evidence.
    `tCount ≡ 1` (every presentation carries the constant-1 `countT`);
    the value laws are the N2PolyGeom repair companions; the degree laws
    are free from `RatBurdens`' own degree pins (`degT_le/degS_le` against
    `tg_degT/tg_degS`), exactly as the `PolyGeomLaws` docstring records. -/
theorem n2_polyGeomLaws_nonempty : Nonempty (MovesS.PolyGeomLaws n2T n2M n2RB) :=
  ⟨{ tCount := fun _ _ _ _ => 1
     tcount_val := fun e τ o q₀ _ => n2_tcount_val e τ o q₀
     scount_val := fun e τ o q₀ _ _ => n2_scount_val e τ o q₀
     tcount_deg := fun e τ o =>
       (n2RB.tgP e τ o).degT_le.trans (le_of_eq (n2RB.tg_degT e τ o))
     scount_deg := fun e τ o =>
       (n2RB.tgP e τ o).degS_le.trans (le_of_eq (n2RB.tg_degS e τ o)) }⟩

end LeanUrat.MovesU
