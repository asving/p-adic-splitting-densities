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
evaluated counts (≡ 1 at this instance — every tg presentation is built by
`pgDiv`, whose `countT` is the constant 1, so `tcount_val`/`tcount_deg` and
`scount_deg` are free).

## PROBE VERDICT (2026-07-31): **REFUTED AT THE AS-BUILT PACK — the row does
## NOT move out.  The obstruction is compiled below (`n2_polyGeomLaws_isEmpty`),
## and it is exactly the "missing cell-count identity" the unit's permitted
## outcome anticipated.**

**The obstruction (the padding-row cell census).**  `scount_val` pins the
`countS` factor of EVERY roster row against the cell-fiber census
`∑ c ∈ cells e τ o, #cellInst`, at every pool, quantified over ALL (e, τ, o) —
including the roster PADDING rows: `n2T.Out ≡ Fin 3` at every layer, but at
e ≠ 2 the real roster is the single terminal (1,1) row at o = 0, with o = 1, 2
the duplicate padding outcomes ("the roster's duplicate outcomes carry no
mass", N2PolyGeom's `tgLow`), while `n2M.Cell (e ≠ 2) ≡ Fin 1` with
`cellOut ≡ 0`.  So the padding outcomes have EMPTY cell fibers (census 0), but
their presentation `pgZero = pgDiv 0 1 0` carries `countS = 1` (the `pgDiv`
constructor pins `countS := 1` uniformly).  At (e, o, q₀) = (1, 1, 2) — a REAL
operative level, e ∈ Icc 1 2 — the law demands 1 = 0: `PolyGeomLaws n2T n2M
n2RB` is EMPTY.  Note this failure is invisible to the VALUE laws:
`pgZero.val = 0` regardless (`num = 0`), so `tg_interp` and every downstream
evaluation are untouched — only CL-6's countS-vs-census pin sees it.

**Confinement (compiled below, `n2_countLaws_block2`).**  At the block-2 layer
— THE operative layer, where all three real roster rows and all the mass live —
both count laws HOLD: every fiber is the singleton cell of its outcome and
`countS ≡ 1` matches; `countT ≡ 1` is integer-valued at every pool (so the
"non-integer-valued pool evaluation" arm of the permitted outcome does NOT
fire).  The failure is EXACTLY the e ≠ 2 padding rows.

**The repair path (recorded for Q6's adjudication, NOT executed — `n2RB` is
as-built-ratified data; changing it is a definition-change event under the
standing authority, orchestrator's call):** give the padding presentation
`pgZero` the honest census factor `countS := 0` (a private, val-preserving
data change: `pgZero.val = 0` either way, `natDegree 0 = 0 ≤ 0` keeps the
degree pins, and no external consumer pins `tgP`'s `countS` — grep-verified
this probe).  After that repair the witness construction goes through with
`tCount ≡ 1`, and the cl6 row's pre-authorized "moves out" clause fires at the
final n = 2 wiring.  Until then the row is CARRIED, and the eventual wiring
MUST NOT instantiate `cl6` at the unrepaired pack (it would be asserting a
falsehood — this probe is the compiled fence).

SCOPE FENCE (the M1 soundness rule, BridgeN3b precedent): `n2_polyGeomLaws_isEmpty`
refutes the INSTANCE-tier proposition at the as-built (n2T, n2M, n2RB) only.
The generic `BridgeKernels.cl6` row (over abstract `C : UCarriers n`) and
`MovesV.polygeom_count_laws`'s theorem-under-burdens supply (whose `hSCount`
premise is exactly what fails here) are NOT refuted; no sorried universal is
negated.

No sorries in this file; both artifacts are Lean-core.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open LeanUrat.MovesS

/-! ## The confinement half — both count laws HOLD at the block-2 layer -/

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
    singleton cell-fiber census (`scount_val`'s shape).  The probe's failure
    is NOT here — it is confined to the e ≠ 2 padding rows
    (`n2_polyGeomLaws_isEmpty` below). -/
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

/-! ## The refutation half — the padding-row cell census -/

/-- **SYN2-K2 PROBE VERDICT, COMPILED**: `PolyGeomLaws n2T n2M n2RB` is EMPTY
    at the as-built n = 2 pack — the `cl6` row is NOT instance-dischargeable
    without the recorded `pgZero.countS` repair (header).  Witness site:
    (e, τ, o, q₀) = (1, (), o = 1, 2) — the block-1 PADDING outcome.  Its
    presentation `pgZero` carries `countS = 1`, but its cell fiber is empty
    (`n2M.Cell 1 ≡ Fin 1` with `cellOut ≡ 0 ≠ 1`), so `scount_val` demands
    1 = 0.  The failure is value-law-invisible (`pgZero.val = 0` either way)
    and confined to padding rows (`n2_countLaws_block2`). -/
theorem n2_polyGeomLaws_isEmpty :
    IsEmpty (MovesS.PolyGeomLaws n2T n2M n2RB) := by
  refine ⟨fun hPGL => ?_⟩
  have h2 : (2 : ℚ) ∈ n2M.Pools :=
    ⟨2, Nat.prime_two, 1, by rw [PNat.one_coe, pow_one]; norm_num⟩
  have hs := hPGL.scount_val 1 () (show n2T.Out 1 () from (1 : Fin 3)) 2 h2
    True.intro
  have hcells : n2M.cells 1 () (show n2T.Out 1 () from (1 : Fin 3)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hcmem
    simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq] at hcmem
    have hlt : c.1 < 1 := c.2
    have h01 : c.1 % 3 = 1 % 3 := congrArg Fin.val hcmem
    omega
  rw [hcells, Finset.sum_empty] at hs
  have hL : (n2RB.tgP 1 () (show n2T.Out 1 () from (1 : Fin 3))).countS.eval 2
      = 1 := by
    change (1 : Polynomial ℚ).eval 2 = 1
    simp
  exact one_ne_zero (hL.symm.trans hs)

end LeanUrat.MovesU
