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
`Nonempty (State e)`.  The E-phase skeleton's `sorry` was the DERIVATION
ATTEMPT the prover owed (bounded repair, ≤ 3 routes beyond the audit), NOT an
assertion of derivability.  ON BLOCKED: the exact missing statement is `HStateNe n C`,
already ratified (Q3) as the `BridgePre.hStateNe` named premise (warrant: the
note's block table always contains the entrance state of block e — §S-RESUM's
roster is per-block nonempty by construction; MOVES ledger rows CL-5/CL-1
quantify over it); the prover then reports BLOCKED, this theorem is REMOVED in
the same commit that lands `BridgePre` (IB-F1) consuming the premise, and the
outcome goes to the campaign ledger.  The prover must NOT weaken the statement
or True-ify (statement fence).

DERIVATION ATTEMPT EXECUTED (prover, 2026-07-30) — OUTCOME: BLOCKED.
Three routes probed beyond the recorded audit, all closed by reading the
as-built sources (never memory):
* ROUTE 1 — `C.chain.pools_e0` → `PoolHyp` (MovesS/Defs.lean:533): full field
  read.  `Act : Finset (T.State e)` with the iff `act_spec` — over an EMPTY
  `State e` the choice `Act = ∅` satisfies all seven fields: `act_spec`/
  `entry_ok`/`A_eval`/`inactive_vanish` quantify over members of `Act` or
  `State e` (vacuous), and `e0 : EscapeE0 A` (Defs.lean:524) holds at the
  empty-index matrix (`nonneg` vacuous; `escape` in the singleton function
  space `Act → ℚ`).  `Nonempty (PoolHyp …)` therefore forces NO state.
* ROUTE 2 — `C.chain.B : RS1Bundle` (Interfaces.lean:48): `βmeas`(via
  `RS1Meas`)/`xrb`/`recursion_meas`/`rexact` are all τ-INDEXED families or
  laws over a GIVEN τ; `nsNull` is a bare instance-supplied `Prop` (its own
  disclosure docstring).  No existential in `State e`.
* ROUTE 3 — `UCarriers.cl1` = `chain.legs_reg` at a base prime →
  `MovesS.RegP` (Defs.lean:618): definitionally `∀ e he, ∀ δ ∈
  consumedDeltas, Nonempty (PoolHyp …)` — reduces verbatim to ROUTE 1.
`LedgerIV` re-verified en passant (every field `xhd_sum` … `init_agg`
quantifies over a given τ).  Semantic reason the block is structural: a
`TableShape` with `State e := Empty` everywhere satisfies every carried
pack law vacuously, so `HStateNe` is not a consequence of `UCarriers` —
it is genuine per-instance content, exactly the Q3-ratified
`BridgePre.hStateNe` premise (landed, BridgeKernels.lean:127-129).
DISPOSITION EXECUTED: `bridge_hStateNe_derivation` DELETED per the recorded
on-blocked instruction; `HStateNe` (the shared sentence) remains — consumers:
`BridgePre.hStateNe` (IB-F1), `bridgeRegData`'s `hne` binder (IB-B8).
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

-- IB-B2 outcome record: `bridge_hStateNe_derivation` (the derivation attempt)
-- was DELETED per the recorded on-blocked disposition — see the file header's
-- DERIVATION ATTEMPT EXECUTED record for the three probed routes and the
-- structural countermodel sketch.  The ratified premise `BridgePre.hStateNe`
-- (BridgeKernels.lean) carries this sentence from here on.

end LeanUrat.MovesU
