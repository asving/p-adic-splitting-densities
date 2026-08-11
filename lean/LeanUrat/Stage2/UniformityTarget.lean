/-
# STAGE-2 ANCHOR — the general-degree uniformity target (STATEMENT ONLY)

**FENCE.** This file is the first artifact of stage two (the formalization of the
informal accepted corpus, 2026-08-10). It is NOT imported by any module of the
trusted capstone graph, and it contains exactly one `sorry` — the target theorem's
body — following the established E-phase precedent (HC1/MovesT campaigns: compiling
sorry-statements in fenced campaign files; the repo's zero-banked-sorries policy
governs the trusted corpus, which this file is outside of). `sorryAx` is expected
in THIS file and nowhere else.

**TRUST BOUNDARY — REVIEW REQUESTED.** Lean checks proofs, not statements; this
statement and the `RealInstanceAt` parameter bundle below are new formalized
statements and are flagged for Asvin's review BEFORE any unit targets them
(docs/PROJECT_STATE.md dated append #24).

**WHAT THE TARGET SAYS.** The informal theorem (accepted-text-complete at the
2-clean bar, PROJECT_STATE appends #14–#23): for every degree n and splitting
type σ of degree n there is ONE rational law — a pair of polynomials
(num, den) — such that at EVERY prime p (including wild), the density of monic
degree-n polynomials over ℤ_p with type σ equals num(p)/den(p). The existing
machine-checked capstone (`OM.RealInstanceV2.montes_unconditional`) is the
instance of this at the single real prime `M9.realP`, for the DECIDED (order-0)
density, conditional on the tame functional equation; the target below quantifies
the density tie over an arbitrary real instance family and states the full-density
version behind the exhaustiveness hypothesis, mirroring
`montes_unconditional_exhaustive`'s shape.

**PARAMETER PROVENANCE (S-0 ledger sources).** The `RealInstanceAt` bundle
packages, at an arbitrary prime, exactly the data the real instance supplies at
`M9.realP`: a counting model + Montes data + a density foundation with the honest
bridge (`hbridge` of `MontesV2.goal_theorem_montes`), plus the two standing
conditionalities as explicit hypotheses (the tame functional equation;
exhaustiveness for the full tie). Its realness conditions (that `model` counts
actual ℤ_p-polynomial factorizations — the analogue of the RealInstanceV2Gates)
are recorded as the `faithful` field, stated abstractly here and REVIEW-FLAGGED:
making `faithful` precise per prime is itself a stage-two unit
(mirroring `OM/RealInstanceV2Gates.lean`).
-/
import LeanUrat.MontesV2

namespace LeanUrat.Stage2

open LeanUrat LeanUrat.MontesV2 LeanUrat.CountingModel Polynomial Filter Topology

/-- The data of a real p-adic counting instance at prime `q`, degree `n`:
the abstract objects `MontesV2.goal_theorem_montes` consumes, bundled with the
faithfulness predicate tying the model to genuine ℤ_p counting.
REVIEW-FLAGGED: `faithful` is an abstract placeholder field here; the per-prime
realness gates (the general analogue of `OM/RealInstanceV2Gates.lean`) are a
named stage-two unit and must replace it before this bundle is consumed at
theorem strength. -/
structure RealInstanceAt (q n : ℕ) where
  /-- The counting model (as in `realM2` at the committed prime). -/
  model : CountingModel q n
  /-- The Montes data over the model (as in `realD2`). -/
  data : MontesDataV2 q n model
  /-- The tame density foundation (as in `realF2`). -/
  foundation : DensityFoundation
  /-- The honest measure-wall bridge of `goal_theorem_montes`. -/
  hbridge : ∀ σ : FactorizationType, ∀ q' : ℕ, 1 < q' →
    foundation.density n σ q' = ∑ T ∈ data.shapesOf σ, data.C T q'
  /-- REVIEW-FLAGGED realness placeholder: the model counts monic degree-`n`
  ℤ_p-polynomial factorizations at the prime `q` (the general
  `RealInstanceV2Gates` content). Stated as `True` pending the gates unit so
  that this file compiles as a pure statement anchor; any consumption of
  `RealInstanceAt` at theorem strength before the gates unit lands is
  ILLEGITIMATE and the docstring says so. -/
  faithful : True

/-- **THE STAGE-2 TARGET (the general-degree uniformity theorem, decided
density).** One rational law per (n, σ), valid at every prime
carrying a real instance, conditional per instance on the tame functional
equation — the general form of `montes_unconditional`'s conclusion. The full
(exhaustive) tie is `uniformity_target_exhaustive` below. -/
theorem uniformity_target
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (q : ℕ) (_ : 1 < q) (R : RealInstanceAt q n),
        TameFunctionalEquation R.foundation n σ →
          den.eval (q : ℚ) ≠ 0 ∧
          R.model.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  sorry

/-- **THE STAGE-2 TARGET, full density.** The same law ties the FULL density at
every instance additionally satisfying the exhaustiveness (drainage) hypothesis,
mirroring `montes_unconditional_exhaustive`: the undecided mass at depth `N`
vanishes as `N → ∞`. `undecidedCount` is the model's field, as at the committed
prime. -/
theorem uniformity_target_exhaustive
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (q : ℕ) (_ : 1 < q) (R : RealInstanceAt q n),
        TameFunctionalEquation R.foundation n σ →
        Filter.Tendsto
          (fun N => R.model.undecidedCount N / (q : ℚ) ^ (n * N))
          Filter.atTop (nhds 0) →
          den.eval (q : ℚ) ≠ 0 ∧
          R.model.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  sorry

end LeanUrat.Stage2

/- Statement revision note (2026-08-10, per Asvin's review): palindromicity
DROPPED from both targets — "it might be cleaner not to mention the
palindromicity at all and simply to prove uniformity at all primes"; the
palindromy content remains a capstone-level fact at the committed instance
(montes_unconditional) and is not part of the stage-2 target.

Statement-grain sign-off (2026-08-11, Asvin): the bare (e,f)-multiset
`FactorizationType` IS the intended target grain — "that is what we want to
prove"; finer invariants (e.g. discriminant exponents) are possible theorems
but deliberately deferred. The type definition is confirmed as reviewed. -/
