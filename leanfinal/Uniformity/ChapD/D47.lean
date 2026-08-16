/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D46

/-!
# Uniformity.ChapD.D47 — `CertFrame.nuIdx`, the totalized first-discrepancy height

**Chapter D, NODE D.47** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate
witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended). ENVIRONMENT:
as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`). One public declaration,
definitional.

*The first-discrepancy height, totalized.* For a certificate frame `F` (D.46), a coordinate
`j : ℕ` and a dividend `q : Dv`,

```
nuIdx F j q  :=  sInf {m : ℕ∞ | ∃ m' : ℕ, m = (m' : ℕ∞) ∧ F.grΔ m' j q ≠ 0}
```

is the corpus's `ν_j(q) := min{m : gr_m(Δ_j(q)) ≠ 0}` with the convention `min ∅ := +∞`
(`EFF.T4.12`, R1-m1's totalization). The set is the IMAGE in `ℕ∞` of the natural heights whose
assembled digit is nonzero, so `⊤` is never a member; `sInf ∅ = ⊤` in `ℕ∞` (mathlib's
`CompleteLattice (WithTop ℕ)` convention) is then exactly the corpus's `+∞` branch —
"`ν_j(q) = +∞` exactly when `Δ_j(q)` is identically zero", which in this packaging means every
`F.grΔ m j q = 0`.

## Why `ℕ∞` and not a disjunction

The totalization is the corpus's own move and it has a purpose downstream: it is what lets
D.49's LEMMA T4.2(a) be stated "without a disjunction" (`EFF.T4.12`). The untouched corollary
reads `(F.Θ j : ℕ∞) < F.nuIdx j F.fkey`, and the identically-zero case is carried by that same
inequality through `⊤` rather than by a separate clause. Every consumer of this definition
therefore works in `ℕ∞`, never in `ℕ` with a side condition.

## Faithfulness

**⚠ Trust-boundary definition** (parent CLAUDE.md trust boundary). Three points, none of them a
delta against the source:

* *the height index stays a natural.* `F.grΔ` is indexed by `m' : ℕ` (D.46's field); only the
  VALUE of `nuIdx` lives in `ℕ∞`. The existential `∃ m' : ℕ, m = (m' : ℕ∞) ∧ …` is what
  transports the `ℕ`-indexed nonvanishing condition into the `ℕ∞` lattice where the `sInf`
  and the `+∞` convention live — it is not an extra hypothesis.
* *`min` is spelled `sInf`, and that is the same number.* On a set of naturals viewed in `ℕ∞`
  the infimum is attained when the set is nonempty (`ℕ∞` is a complete linear order and the
  set is bounded below by `0`), so `sInf` agrees with the corpus's `min` on the nonempty
  branch and supplies `⊤ = +∞` on the empty one. Nothing here assumes the set is nonempty;
  that is D.49's business, where (FLOOR) supplies the lower bound.
* *no frame hypothesis is consumed.* `nuIdx` is defined for EVERY `j` (not only `j < F.μ₂`)
  and every `q : Dv` (not only members of `F.M`). The coordinate range and the membership
  condition enter at the theorems (D.49's `hj : j < F.μ₂`, D.50's `hf : F.fkey + g ∈ F.M`),
  which is where the corpus puts them.

**Flagged for human review** (definition faithfulness).

DEPENDS: D.46 (`CertFrame`, landed at `Uniformity.ChapD.D46`) · mathlib `ℕ∞` (`WithTop ℕ`) with
its `CompleteLattice`/`InfSet` instance. Nothing else; in particular no dependence on D.45's
`thresholdTheta` (the threshold enters only through the frame's own `Θ` field).

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
verbatim, with the blueprint's `namespace Uniformity.Density.Gauge` header restored (the
leanspec wrapper `LeanspecD` is a stub-side artifact; the landed namespace assignment is
`Uniformity.Density.Gauge`, GC-6.2). `noncomputable` is signed: `sInf` on `ℕ∞` is classical.

SOURCE: `EFF.T4.12` (R1-m1's totalization of `ν_j`, with `min ∅ := +∞` and the sentence "so the
equivalence in T4.2(a) can be stated without a disjunction").

**TEETH.** S8 PE1(2) → **D.49** (the attainment equivalence and its untouched corollary are
where this definition is scored); leg 4 of the D.66 gate runs the same three facts in `ℕ∞`,
this definition's codomain. Nothing to score at this node — it is a definition.

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, all written
inline as the declaration's own binders (no `variable` block, B.42 binder rule).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.47** The first-discrepancy height, totalized: `ν_j(q) := min{m : gr_m(Δ_j(q)) ≠ 0}`
with `min ∅ := +∞` (`EFF.T4.12`). The set is the image in `ℕ∞` of the natural heights carrying
a nonzero assembled digit, so mathlib's `sInf ∅ = ⊤` IS the corpus's `+∞` branch: `ν_j(q) = +∞`
exactly when every `grΔ m j q` vanishes. -/
noncomputable def CertFrame.nuIdx {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) (q : Dv) : ℕ∞ :=
  sInf {m : ℕ∞ | ∃ m' : ℕ, m = (m' : ℕ∞) ∧ F.grΔ m' j q ≠ 0}

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.nuIdx

end AxCheck
