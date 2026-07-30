/-
Kernels/KA8 — BP4-c7 E-phase skeleton for unit KA8: the δ > 1 transport —
ESCAPE(E0)/PoolHyp at the base-changed pools from the O_δ theory's own
instance, typed as a conditional over `consumedDeltas`
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A + §4 KA8; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block: Q4 — named hypothesis/carrier
shape only, never new fields on frozen structures).

RECORDED RESOLUTIONS (statement transcription):
· The blueprint's "EscapeE0 at the base-changed pool from the O_δ theory's
  own instance" is typed at the `PoolHyp` LEVEL — the full E0/ACT package
  `RegP`'s quantifier actually ranges over (`MovesS.RegP`,
  MovesS/Defs.lean:618: `Nonempty (PoolHyp …)` per (e, δ)); `PoolHyp`
  bundles Act/A/A_eval/inactive_vanish AND the `e0 : EscapeE0 A` field, so
  the PoolHyp-level transport is exactly the RegP-consumable form.
· The [2r]/(e2) identification (CONVENTION DELTA-ABS, MovesS/Defs.lean R17
  vicinity: the semantic pool index is the product along the base-change
  chain) is CARRIED as the single named field `transport` — a hypothesis in
  the Q4-sanctioned shape.  The prover's attempt is to DERIVE `transport`
  from the O_δ theory's own instance data ("typing the transport honestly",
  the blueprint's hard-fable label); fallback: the field stays a named
  hypothesis + obstruction record.
· δ quantification: `RegP` ranges over `δ ∈ consumedDeltas T F` (ℕ+, a
  multiplicative closure CONTAINING 1).  The base hypothesis `hbase` covers
  the δ = 1 pool p¹ (((1 : ℕ+) : ℕ) = 1 definitionally); `transport` covers
  the consumed δ with 1 < δ.

deps: KA1-KA5 (Kernels/E0Matrix.lean — the abstract escape layer the base
packages' `e0` fields are discharged through; NOT consumed by this
statement, hence not imported), MovesS/Defs.lean (`PoolHyp`, `RegP`,
`consumedDeltas`, `KmatHyp`, `ShapeFam`).
Consumers: `RegPin.detHyp`/`SolveSeam.*` sit downstream of RegP
(MovesU/DefsLedger.lean:536-676).

Build: cd lean && lake build LeanUrat.Kernels.KA8
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

/-- KA8 (⚑ the named transport carrier): the [2r]/(e2) pool-transport
hypothesis along one base prime p — for every block size e and every
CONSUMED base-change leg δ > 1, the O_δ theory's own instance turns the
base pool package (δ = 1, pool p) into a package at the base-changed pool
p^δ.  A NAMED hypothesis in the Q4-sanctioned shape (hypothesis/carrier
only); the derivation attempt from the O_δ instance data is the prover's
work, fallback pre-declared (file header). -/
structure PoolTransport {n : ℕ} (T : MovesS.TableShape n)
    (M : MovesS.MeasuredSide T) (RB : MovesS.RatBurdens T M) (p : ℕ)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e)
    (F : MovesS.ShapeFam T) where
  transport : ∀ e (he : e ∈ Finset.Icc 1 n) (δ : ℕ+),
    δ ∈ MovesS.consumedDeltas T F → 1 < (δ : ℕ) →
    Nonempty (MovesS.PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (1 : ℕ))) →
    Nonempty (MovesS.PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (δ : ℕ)))

/-- KA8 (the theorem): base pool packages at δ = 1 + the named transport ⟹
(REG-p), i.e. `MovesS.RegP` — the per-pool E0/ACT quantifier over δ = 1 AND
every consumed base-change leg pool p^δ.  deps: `PoolTransport` (above),
MovesS.Defs.  Sketch: intro e he δ hδ; case (δ : ℕ) = 1 vs 1 < (δ : ℕ)
(ℕ+ positivity leaves no third case); at δ = 1, `PNat.coe_eq_one_iff`
rewrites the pool to p¹ and `hbase` closes; at 1 < δ, `tr.transport … hδ …
(hbase e he)` closes. -/
theorem RegP_of_baseAndTransport {n : ℕ} (T : MovesS.TableShape n)
    (M : MovesS.MeasuredSide T) (RB : MovesS.RatBurdens T M) (p : ℕ)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e)
    (F : MovesS.ShapeFam T)
    (hbase : ∀ e (he : e ∈ Finset.Icc 1 n),
      Nonempty (MovesS.PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (1 : ℕ))))
    (tr : PoolTransport T M RB p hK F) :
    MovesS.RegP T M RB p hK F := by
  sorry

end LeanUrat.Kernels
