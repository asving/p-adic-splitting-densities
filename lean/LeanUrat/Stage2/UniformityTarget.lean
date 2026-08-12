/-
# STAGE-2 ANCHOR — the general-degree uniformity target (STATEMENT ONLY, rev. 2)

**FENCE.** This file is the target-statement anchor of stage two (the
formalization of the informal accepted corpus). It is NOT imported by any module
of the trusted capstone graph, and it contains exactly two `sorry`s — the two
target theorems' bodies — per the E-phase precedent (compiling sorry-statements
in fenced campaign files; the zero-banked-sorries policy governs the trusted
corpus, which this file is outside of). `sorryAx` is expected in THIS file and
nowhere else.

**REVISION 2 (2026-08-12, per the leansimp review D1/D6/D8, Asvin signed off).**
Revision 1's statements were FALSE-AS-STATED: they fixed (num, den) before
quantifying over q and a FREE instance bundle `RealInstanceAt q n`, whose
instances at the same q need not share a density. The fix, landed here: the
quantification is now over a `RealCountingFamily n` — one prime-indexed family
carrying a SINGLE shared shape menu and a SINGLE shared coefficient function,
with per-prime Montes data COHERENT with both (`shapes_coherent`,
`coefficient_coherent`), and `p.Prime` required. Within one family, the
decomposition theorem (`MontesV2.countingDensity_eq_sum_C`) pins each prime's
density to the shared data, so one law per family is the honest content.
The old rev-1 statements are preserved below in a comment for the record.

**THE REMAINING PLACEHOLDER (named, fenced).** `faithfulAt : True` still awaits
the realness gates (Unit 1 of the stage-two spec: the general analogue of
`OM/RealInstanceV2Gates.lean` — genuine monic-ℤ_p-box counting semantics, with
the same-prime uniqueness theorem as its safety check). UNTIL THAT UNIT LANDS,
NO PROOF UNIT MAY TARGET THESE STATEMENTS: with `faithfulAt` trivial, an
abstract family whose `coefficient` is not rational-in-q still defeats the law,
so the statements below are honest TARGETS only on the real family the gates
will pin. The docstring of `faithfulAt` carries the same warning at the use
site. (Per the review: strengthening `faithful` is necessary; the coherence
fields above are the other half, and both are now displayed.)

**WHAT THE TARGET SAYS.** For every degree n and type σ of degree n (the bare
(e,f)-multiset grain, signed off 2026-08-11), and every real counting family:
ONE rational law (num, den), den ≠ 0, such that at EVERY prime p the family's
decided density at p equals num(p)/den(p); the exhaustive variant ties the full
density behind per-prime drainage. The machine-checked capstone
(`OM.RealInstanceV2.montes_unconditional`) is the single-prime instance shape
this generalizes. Per review D8, no tame-functional-equation hypothesis
appears: the informal complete proof derives uniform rationality without it
(it was only ever palindromy's carrier, and palindromy was dropped from the
target 2026-08-10).
-/
import LeanUrat.MontesV2

namespace LeanUrat.Stage2

open LeanUrat LeanUrat.MontesV2 LeanUrat.CountingModel Polynomial Filter Topology

/-- **The canonical prime-indexed real counting family** (leansimp review D1).
One shared shape menu and one shared coefficient function across all primes;
per-prime counting models and Montes data coherent with both. This coherence is
what makes "one law for all primes" a well-posed claim: within a family, the
V2 decomposition theorem pins the density at p to `∑ T ∈ menu σ, coefficient T p`.
-/
structure RealCountingFamily (n : ℕ) where
  /-- The counting model at each prime (as `realM2` at the committed prime). -/
  modelAt : ∀ p : ℕ, Nat.Prime p → CountingModel p n
  /-- THE shared shape menu: the finite set of cluster shapes contributing to
  each type — one menu for all primes (p-independence is L5fix/GMN content). -/
  menu : FactorizationType → Finset ClusterShape
  /-- THE shared per-shape coefficient `C T (q)` as a function of the residue
  cardinality — one function for all primes. Its rationality-in-q is the
  cross-prime coefficient-uniformity theorem (review D6), NOT a field. -/
  coefficient : ClusterShape → ℕ → ℚ
  /-- The Montes data over each prime's model (as `realD2`). -/
  dataAt : ∀ p hp, MontesDataV2 p n (modelAt p hp)
  /-- Every prime's shape decomposition uses THE shared menu. -/
  shapes_coherent : ∀ p hp σ, (dataAt p hp).shapesOf σ = menu σ
  /-- Every prime's per-shape coefficients are THE shared coefficients. -/
  coefficient_coherent : ∀ p hp T, (dataAt p hp).C T = coefficient T
  /-- ⚠ PLACEHOLDER (Unit 1, the realness gates): the models count genuine
  monic degree-`n` ℤ_p-boxes. While this field is `True`, NO proof unit may
  target the theorems below (an abstract family with non-rational
  `coefficient` defeats them); the gates unit replaces this with the
  `GenuineZpCounting` predicate + the same-prime uniqueness theorem. -/
  faithfulAt : True

/-- **THE STAGE-2 TARGET (decided density), rev. 2.** One rational law per
(n, σ) and per real counting family, tying the decided density at EVERY prime
simultaneously — the general form of `montes_unconditional`'s conclusion, with
no tame hypothesis (review D8). FENCED until `faithfulAt` is real. -/
theorem uniformity_target
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry

/-- **THE STAGE-2 TARGET, full density, rev. 2.** The same law ties the full
density at every prime whose model additionally drains (undecided mass → 0),
mirroring `montes_unconditional_exhaustive`. FENCED until `faithfulAt` is real. -/
theorem uniformity_target_exhaustive
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        Filter.Tendsto
          (fun N => (F.modelAt p hp).undecidedCount N / (p : ℚ) ^ (n * N))
          Filter.atTop (nhds 0) →
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry

end LeanUrat.Stage2

/- ============================ STATEMENT HISTORY ============================

Rev. 1 (2026-08-10, superseded 2026-08-12 — the leansimp review found the
quantifier defect; Asvin signed off the revision): the targets quantified over
a FREE per-prime bundle after fixing (num, den):

  structure RealInstanceAt (q n : ℕ) where
    model : CountingModel q n
    data : MontesDataV2 q n model
    foundation : DensityFoundation
    hbridge : ∀ σ q', 1 < q' → foundation.density n σ q' = ∑ T ∈ data.shapesOf σ, data.C T q'
    faithful : True

  theorem uniformity_target (n hn σ hσ) :
      ∃ num den, den ≠ 0 ∧ ∀ q (_ : 1 < q) (R : RealInstanceAt q n),
        TameFunctionalEquation R.foundation n σ →
          den.eval q ≠ 0 ∧ R.model.countingDensity σ = num.eval q / den.eval q

  (+ the exhaustive variant). Defect: instances at the same q need not share a
  density, so ∃-before-∀ is defeated by adversarial instances. Also carried per
  review D8: the TameFunctionalEquation hypothesis is dropped in rev. 2 (it
  served palindromy only, which was dropped 2026-08-10), and the prime-power
  1 < q is replaced by Nat.Prime p in the realness data.

Statement-grain sign-off (2026-08-11, Asvin): the bare (e,f)-multiset
FactorizationType IS the intended target grain; finer invariants deferred.
=========================================================================== -/
