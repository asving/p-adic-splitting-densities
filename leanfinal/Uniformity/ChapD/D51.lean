/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D48

/-!
# Uniformity.ChapD.D51 — LEMMA T4.2(c): the fully-exposed assembled-slot criterion

**Chapter D, NODE D.51** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate
witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended). ENVIRONMENT:
as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`; binders inline, no `variable`
block — B.42). One public declaration.

*The fully-exposed assembled-slot criterion.* If a canonical slot `σ` of coordinate `j` at height
`Θ_j` is **fully exposed** by a contribution with nonzero normalized digit — in the frame,
`ω_j σ = ξ` with `ξ ≠ 0` — then the coordinate is touched:

```
ω_j σ = ξ,  ξ ≠ 0   →   Touched j
```

and by D.49 (`touched_iff_nu_eq`, on the coordinate range) the floor is then attained there,
`ν_j(f_key) = Θ_j`. That attainment corollary is D.49's declaration applied to this one; it is
not restated here, so this file imports D.48 alone.

## The route (`EFF.T4.16`)

"Its normalized digit is nonzero, so the selected slot is a nonzero component … Distinct
canonical slots are separate components; hence `ω_j ≠ 0`." In Lean: `ω_j : Slot →₀ K`, and a
finitely supported function taking a nonzero value at `σ` is not the zero function —
`Finsupp.ne_iff`, whose `mpr` wants exactly the witness `⟨σ, _⟩`. "Distinct canonical slots are
separate components" is the corpus's justification for the slot index being a *coordinate* of the
digit at all; in the frame that is already built into `Slot →₀ K` and needs no argument.

## ⚠ The premise is ALL-PROVENANCE (`HYP.113`)

The ledger records this node as a **live conditional-theorem leg**, and the conditionality is in
the hypothesis `hexp`, not in the proof. Verbatim: "Uniqueness only among single-extraction
contributions does not discharge this premise: the exposure calculation must also exclude every
other term and every incoming carry or recarry from the slot."

The packaging is what makes that fence enforceable. `ω_j σ` is the value at `σ` of
`grΔ (Θ_j) j f_key`, and `grΔ`'s INSTANTIATION obligation (D.46, `EFF.T4.07`/`.08`) is COMPLETE
assembly — every branch, carry and recarry added *before* the graded component is taken. So the
equation `hexp : ω_j σ = ξ` is an equation against the fully assembled digit, and an instance
that proves it has, by construction, excluded every other provenance. A proof that only one
*single-extraction* contribution lands in the slot does not typecheck as `hexp`. **The full
burden therefore sits in proving the instance equation**, which is exactly where the corpus puts
it: D.54's R5-63A discharge, "YES at the sealed scope — `f₁ = 1`, `μ₂ = 2`, `2i_{t*} ≥ D′` — and
NO elsewhere". Nothing in this file discharges any instance.

`EFF.T4.08`'s full-exposure semantics ("the complete list of summands landing in that slot
consists of `ξ` alone, every provenance propagated") is thus rendered as equality against the
ASSEMBLED value rather than as a separate exposure predicate; that is the design choice of the
frame packaging and it is deliberate — a predicate would have to be instantiated too, and an
instantiation of a predicate can be weaker than the equation, whereas the equation cannot be
weaker than itself.

## Faithfulness

**No hypothesis is consumed beyond the two displayed.** In particular not `j < F.μ₂`, not
`fkey_mem`, not `floor`: the implication holds at every `j`, since it is a statement about one
`Finsupp` being nonzero. The coordinate range is needed only for the ATTAINMENT half, which is
D.49's `touched_iff_nu_eq` and carries its own `hj`. Omitting `hj` here strengthens the statement
and cannot weaken it.

**`ξ` is not eliminated.** The frozen signature keeps the named contribution `ξ` with `hexp`
and `hne` separate rather than collapsing to `ω_j σ ≠ 0`; the two forms are interderivable, and
the split form is kept because it is the shape the corpus's exposure calculations produce (a
computed value `ξ`, then a nonvanishing check on it). Both hypotheses are consumed.

**The converse is NOT claimed.** `Touched j` says the whole digit `ω_j` is nonzero; it does not
say any particular slot is exposed, and it certainly does not say a *named* slot is. The exact
converse at the level of the whole digit is D.52 (`omega_zero_iff_untouched`); there is no
slot-level converse anywhere in the chapter.

**No attainment statement for another member follows** — the standing fence of D.49/D.52 ⚠ (ii):
`ω_j` classifies the KEY-POWER witness only, so an exposed slot says nothing about whether
entry-driven content of some other member of `𝔐` attains `Θ_j`.

**No new definition** — nothing is added to the trust boundary beyond D.46/D.48's own flagged
definitions.

DEPENDS: D.48 (`CertFrame.omega`, `CertFrame.Touched`, landed at `Uniformity.ChapD.D48`) and
through it D.46 (`CertFrame`); D.49 for the attainment corollary, which is invoked at the
consumers rather than restated here · mathlib `Finsupp.ne_iff`, `Finsupp.coe_zero`,
`Pi.zero_apply`.

SOURCE: `EFF.T4.16` (R3-G1's replaced statement and proof; the conditionality "full exposure in
the sense of `EFF.T4.08` — an all-provenance premise, NOT single-extraction uniqueness");
`HYP.113`.

**TEETH.** S8 PE1(5) (r3 form) → **this Lean theorem** at frame level, with the instance burden
at D.54 and the retained regression in §12. Nothing is scored in this file; the `CertFrame`
inhabitation witness that makes the implication non-vacuous is D.68's census row (A-D.1
addition (v)).

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, written inline
as the declaration's own binders.

## Status

Sorry-free, axiom-free (Lean core only): `touched_of_exposed` is a PROVED theorem here, not the
leanspec `axiom` stub. It remains a CONDITIONAL theorem in the corpus's sense — `HYP.113`'s
all-provenance premise is its hypothesis `hexp`, discharged only by an instance.
-/

namespace Uniformity.Density.Gauge

/-- **D.51 — LEMMA T4.2(c): the fully-exposed assembled-slot criterion** (`EFF.T4.16`).  If a
canonical slot `σ` of coordinate `j` at height `Θ_j` carries a nonzero normalized digit —
`ω_j σ = ξ` with `ξ ≠ 0` — then `Touched j`, and by D.49 the floor is attained there.  The proof
is `Finsupp.ne_iff`: "its normalized digit is nonzero, so the selected slot is a nonzero
component … distinct canonical slots are separate components; hence `ω_j ≠ 0`".
⚠ The premise is ALL-PROVENANCE (`HYP.113`, a live conditional-theorem leg): "uniqueness only
among single-extraction contributions does not discharge this premise: the exposure calculation
must also exclude every other term and every incoming carry or recarry from the slot".  The
burden sits in proving the INSTANCE equation `ω_j σ = ξ` against the COMPLETE `grΔ` — D.46's
assembly obligation — which is where the corpus puts it (D.54's R5-63A discharge). -/
theorem CertFrame.touched_of_exposed {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {σ : Slot} {ξ : K}
    (hexp : (F.omega j) σ = ξ) (hne : ξ ≠ 0) : F.Touched j := by
  have hslot : (F.omega j) σ ≠ (0 : Slot →₀ K) σ := by
    simpa [hexp] using hne
  exact Finsupp.ne_iff.mpr ⟨σ, hslot⟩

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.touched_of_exposed

end AxCheck
