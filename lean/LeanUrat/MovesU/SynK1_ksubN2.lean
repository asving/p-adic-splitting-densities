/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers
import LeanUrat.MovesS.N2Shape

/-!
# SYN2-K1 — the `cl11_ksub` ledger row DISCHARGED AT THE n = 2 INSTANCE

Instance-tier discharge probe per `lean/notes/SYNTHESIS_PASS2_2026-07-31.md`
P2-C3(a) (unit SYN2-K1), executing the row's own Q6 record
(`BridgeKernels.cl11_ksub`: "a finite roster check at the n = 2 real pack may
discharge it there").  Precedent: `menuWFT_holds` (DefsCarriers.lean) — the
same (K-SUB)/CL-13 family's well-formedness face proved structurally, whose
`cl13_wf` row was discharged rather than carried.

## VERDICT (2026-07-31): **DISCHARGED at the instance — `ksubM1C1T_n2` PROVED.**

The roster walk (`n2T`, N2Shape.lean): at the block-1 layer (and every layer
e ≠ 2) the single roster row `n2outT11` is terminal — `c = 0` refutes the
continuation premise.  At the block-2 layer: `o_K` is the (c = 1, m = 1) kcol
row (the claimed classification, by evaluation); `o_spl`'s members have size 1,
refuting the all-members-size-2 premise; `o_in` is terminal (`c = 0`).  So
"equal-e continuation rides exclusively in K_e's (c = 1, m = 1) rows" holds AT
THE REAL n = 2 ROSTER outright.

SCOPE (per the P2-C3(a) payoff line): the final n = 2 wiring supplies the
`cl11_ksub` row by THIS THEOREM; the generic `BridgeKernels` pack KEEPS the row
(its p-uniform/n-generic shape is unchanged — no fence event; the row's
docstring carries the discharge record).

No sorries in this file; Lean-core footprint.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open LeanUrat.MovesS

/-- SYN2-K1: the (K-SUB) m = 1 classification `KsubM1C1T` HOLDS at the real
    n = 2 table — the finite roster check anticipated by the `cl11_ksub` row's
    Q6 record.  Consumed by the final n = 2 wiring as the row's supply. -/
theorem ksubM1C1T_n2 : KsubM1C1T n2T := by
  intro e he τ o
  have he2 : e = 1 ∨ e = 2 := by
    rcases Finset.mem_Icc.mp he with ⟨h1, h2⟩
    omega
  rcases he2 with rfl | rfl
  · -- e = 1: the single layer row `n2outT11` is terminal (c = 0) — the
    -- continuation premise is refuted by evaluation.
    intro _ hc
    exact absurd rfl hc
  · -- e = 2: the three-outcome roster.
    rcases o with ⟨v, hv⟩
    interval_cases v
    · -- o_K: the kcol row IS (c, m) = (1, 1), by evaluation.
      exact fun _ _ => ⟨rfl, rfl⟩
    · -- o_spl: both members have size 1 — the all-members-size-2 premise is
      -- refuted at the head member.
      intro hall _
      have h1 : (1 : ℕ) = 2 :=
        hall ((n2T.odata 2 τ ⟨1, hv⟩).mem.head (n2T.odata 2 τ ⟨1, hv⟩).hm)
          (List.head_mem _)
      exact absurd h1 (by decide)
    · -- o_in: terminal (c = 0) — the continuation premise is refuted.
      intro _ hc
      exact absurd rfl hc

end LeanUrat.MovesU
