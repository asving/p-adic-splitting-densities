# Quarantine — foreign session's Order0Capstone tail (2026-07-03)

`omDensity_tail_2026-07-03.lean.txt` is the tail a parallel (stale-context) session appended to
`LeanUrat/OM/Order0Capstone.lean` (lines 196-446 at the time of quarantine). Removed because:

1. **It contains an ARITHMETICALLY FALSE axiom** (`omDensity_tame_functionalEquation`, was line 403):
   from its own definitions, `omDensity(n=2) = q(q+2)/(q+1)`, and `R(1/q) ≠ R(q)` (at `q = 2`:
   `8/3 ≠ 5/6`) — asserting `IsPalindromic` for it makes the base inconsistent (exact sympy check,
   session 2026-07-03). Concreteness prevents falsification-by-instantiation, NOT arithmetic
   falsehood (the A11 lesson).
2. **Its density object is the wrong function**: `omDensity := Σ clusterCount(cellsOfShapeWF …)` uses
   the `clusterCount` per-node aggregation REFUTED by the engine reconciliation
   (`VACUITY_SIGMA_BLUEPRINT.md §2.6` D1-D4): e.g. `clusterCount(sepShape (2)) = 4/3` at `q = 2` vs
   the true stratum density `1/4`, and `4/3` for the provably-EMPTY p=2 split stratum. Non-degenerate
   (≠ 0) but incorrect. The engine-validated object is `Order0.rootCount`
   (`montes_order0_unconditional`, footprint pure Lean core).
3. It discards σ (`_σ`), reintroducing the O1 σ-vacuity.

Salvageable ideas already adopted into the plan: the pin-field/invariant architecture and the
enforcement audit of `notes/MONTES_ARCHITECTURE_REDESIGN.md` §3/§7. The tail's
`clusterCount_isRational` engine instantiation is fine as a theorem about that function and can be
resurrected for Phase B once `clusterCount`'s node form is corrected. The tail also had two compile
errors (stuck `decide` at :311, type mismatch at :352) and was never built — the false axiom never
entered any olean.

## BB3inf_2026-07-07.lean.txt (R5 Step 0)
Retired 2026-07-07. The old measure-route BB3 module: 3 axioms (`descend`, `descend_size_lt`,
`AX_GMN_IV_terminates`) + its theorems (`clusterVolume_rational_of_OM`, `T_BB3`, `T_BB1`,
`bb3CellCount_isRational`). Verified DEAD before retirement: imported only by the root
`LeanUrat.lean`, reached by NO count-native capstone (the `PadicMeasure`/`RatFn` "BB3inf." mentions
are docstrings, neither imports it). Tree axiom count 10 → 7. The remaining measure cone
(PadicMeasure ×5) + the Interface split (R5 Steps 1-3, 7→2) stay per notes/R5_REFACTOR_PLAN.md.
