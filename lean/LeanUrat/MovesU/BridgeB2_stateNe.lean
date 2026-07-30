/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers

/-!
# IB-B2 — hStateNe DERIVATION ATTEMPT (bridge campaign BP1; front-runner ADJ unit)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (†4b) /
§4 group B (IB-B2) and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (Q3:
`hStateNe` RATIFIED as a `BridgePre` named premise, derivation attempt FIRST).

THE TARGET (the row the tautological roster's `instBiNe`/`blockDim_pos` need):
`∀ e ∈ Finset.Icc 1 n, Nonempty (C.T.State e)` — `HStateNe` below.

CHARGE: attempt derivation from the carried chain `C.chain` before giving up;
report which route closed.  INTERFACE AUDIT (executed 2026-07-30 by reading the
as-built §S corpus — the E-phase half of the attempt; the prover re-runs it):
* `MovesS.TableShape` (Defs.lean:66) carries `fin : ∀ e, Fintype (State e)` and
  NO nonemptiness field — verified;
* `C.chain.L : LedgerIV` (Defs.lean:210): every field (`xhd_sum` … `part1` …
  `ent_count_card`) quantifies over a GIVEN τ : State e — none forces existence;
* `C.chain.B : RS1Bundle` (Interfaces.lean:48): `βmeas`/`xrb`/`recursion_meas`/
  `rexact` are all τ-indexed families — same shape, no existence;
* `C.chain.pools_e0` (Interfaces.lean:138): yields `Nonempty (PoolHyp …)` at
  all-active prime pools, but `PoolHyp.Act : Finset (State e)` may be EMPTY
  (`act_spec` is vacuous over an empty state type — and an empty `State e` makes
  EVERY pool all-active, so the intersection guard does not bite);
* `C.MS.rep_ne` (Defs.lean:164): `Nonempty (Rep e τ)` only GIVEN a τ;
* `C.MS.boxpos`, `Sigmas`/`sig_exact`, `KsubM1C1T`/`MenuWFT`: box points /
  verdict multisets / τ-quantified laws — no State-existence content.
EXPECTED OUTCOME therefore: BLOCKED — no field of the carried pack forces
`Nonempty (State e)`.  The `sorry` below is the DERIVATION ATTEMPT the prover
owes (bounded repair, ≤ 3 routes beyond the audit), NOT an assertion of
derivability.  ON BLOCKED: the exact missing statement is `HStateNe n C`,
already ratified (Q3) as the `BridgePre.hStateNe` named premise (warrant: the
note's block table always contains the entrance state of block e — §S-RESUM's
roster is per-block nonempty by construction; MOVES ledger rows CL-5/CL-1
quantify over it); the prover then reports BLOCKED, this theorem is REMOVED in
the same commit that lands `BridgePre` (IB-F1) consuming the premise, and the
outcome goes to the campaign ledger.  The prover must NOT weaken the statement
or True-ify (statement fence).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- THE NAMED ROW (†4b): per-block state nonemptiness on the operative range —
    exactly the `BridgePre.hStateNe` premise (Q3-ratified), factored out so the
    derivation attempt, the `BridgePre` pack (IB-F1), and `bridgeRegData`'s
    `instBiNe`/`blockDim_pos` (IB-B8) all speak the same sentence. -/
def HStateNe (n : ℕ) (C : UCarriers n) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, Nonempty (C.T.State e)

/-- IB-B2 — THE DERIVATION ATTEMPT (expected BLOCKED; see the file header for
    the executed interface audit and the on-blocked disposition).  If any chain
    route closes this, `BridgePre` drops the `hStateNe` row and IB-F1 re-plans;
    if not, DELETE this declaration when IB-F1 lands the ratified premise. -/
theorem bridge_hStateNe_derivation {n : ℕ} (C : UCarriers n) : HStateNe n C :=
  sorry

end LeanUrat.MovesU
