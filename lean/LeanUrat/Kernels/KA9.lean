/-
Kernels/KA9 — BP4-c4 E-phase skeleton for unit KA9, the det glue
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A closing paragraph + §4 KA9;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

KA9 `detHyp_of_escape_infinite`: ESCAPE(E0) at infinitely many prime pools ⟹
`MovesS.DetHyp` (the SYMBOLIC nonsingularity ∀ e, (1 − K_e).det ≠ 0), through
`e0_det_ne_zero` + the RatfuncEvalInfinite vanishing principle ("a rational
function vanishing at infinitely many prime evaluations is 0").

VERIFY-ONLY FINDING (the blueprint's own instruction "Verify what
Rs3DetSymbolic already states" executed this pass): `MovesS.rs3_det_symbolic`
(MovesS/Rs3DetSymbolic.lean:27) already PROVES a conclusion that is literally
the unfolding of the abbrev `MovesS.DetHyp T RB hK` (MovesS/Defs.lean:562),
from exactly the hypothesis surface below — the escape lives inside the
`PoolHyp` bundles' `e0` fields at the base-prime pools PP (infinitely many by
prime infinitude; cofinitely many all-active by `allActive_cofinite_primes`).
This unit is therefore GLUE: it re-keys that conclusion to the NAMED `DetHyp`
consumer face.  Expected proof: one application of `rs3_det_symbolic`.

RECORDED RESOLUTIONS (statement transcription):
· "EscapeE0 at infinitely many prime pools" is transcribed as the
  `rs3_det_symbolic` hypothesis surface verbatim (PP the base-prime pool set;
  per-pool `Nonempty (PoolHyp …)` at the all-active members, each carrying
  its `e0 : EscapeE0` leg) — the minimal resolution, introducing no new
  quantifier shape between the existing prover and the named consumer.
· New file (seams in MovesS are the blueprint's location hint, but no
  existing file may be modified — the glue lands here; default <UnitId>.lean
  naming since the §4 KA header's E0Matrix/E0Route files are matrix/route
  content).

deps: existing MovesS chain (Rs3DetSymbolic ⊃ EvalDet, E0DetNeZero,
AllActivePrimes, RatfuncEvalInfinite).
Build: cd lean && lake build LeanUrat.Kernels.KA9
-/
import LeanUrat.MovesS.Rs3DetSymbolic

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesS

variable {n : ℕ}

/-- KA9 `detHyp_of_escape_infinite` (det glue): per-pool packages (each
carrying ESCAPE(E0) in its `e0` field) at the all-active members of the
base-prime pool set PP — infinitely many pools, cofinitely many all-active —
imply the SYMBOLIC determinant hypothesis `MovesS.DetHyp` every solve
consumer carries.  deps: existing MovesS chain (`rs3_det_symbolic` =
e0_det_ne_zero + RatfuncEvalInfinite assembled).  Sketch: exactly
`rs3_det_symbolic RB hdc hK PP hsub hbase hact` — the conclusion of that
theorem is definitionally `DetHyp T RB hK`; this unit is the named re-key. -/
theorem detHyp_of_escape_infinite {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (PP : Set ℚ) (hsub : PP ⊆ M.Pools)
    (hbase : ∀ q₀, q₀ ∈ PP ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ))
    (hact : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PP ∩ allActivePools M,
      Nonempty (PoolHyp T M RB e (hK e he) q₀)) :
    DetHyp T RB hK := by
  exact rs3_det_symbolic RB hdc hK PP hsub hbase hact

end LeanUrat.Kernels
