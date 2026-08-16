/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D48

/-!
# Uniformity.ChapD.D52 — LEMMA T4.2(d): the no-contribution criterion

**Chapter D, NODE D.52** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate
witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended). ENVIRONMENT:
as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`; binders inline, no `variable`
block — B.42). One public declaration.

*The no-contribution criterion.* `EFF.T4.17`'s clause (d) has two legs — "after complete
propagation, no summand of any provenance lands in any height-`Θ_j` slot of coordinate `j`", and
"the complete assembled contribution cancels" — and both conclude `ω_j = 0`. In D.46's frame the
two legs ARE the single equation `F.grΔ (F.Θ j) j F.fkey = 0`, because `grΔ`'s INSTANTIATION
obligation is complete assembly (every branch, carry and recarry added before the class is
taken, `EFF.T4.07`/`.08`). So at frame level the lemma is the definitional unfolding

```
ω_j = 0  ↔  ¬ Touched j
```

which is `not_not` on D.48's `Touched j := ω_j ≠ 0`.

## Why the content is a fence and not the proof

The eight-character proof is the point of the packaging, not a sign that the lemma is empty: the
two legs collapse into one equation **only because the frame demands complete assembly**, so all
of the corpus's work sits in the INSTANCE obligation of discharging that equation, exactly where
`EFF.T4.17` puts it. The two ⚠ warnings below are the r4 content (`HYP.114`), and they are
transcribed here rather than proved because neither is a statement about the frame.

**⚠ (i) — the exclusion is ALL-PROVENANCE.** "Absence of single-extraction sources alone does
not discharge the first hypothesis: the exclusion must cover every provenance named in
DEFINITION T4.1's assembly." Same instance burden as D.51's full-exposure premise: a proof that
no *single-extraction* branch lands in the slot proves nothing about `grΔ`, whose value is the
assembled digit.

**⚠ (ii) — NO attainment statement for another member follows.** "Entry-driven content may still
attain `Θ_j`." `ω_j` classifies the KEY-POWER witness only. The committed separator: at FR-M3's
`j = 0` the `W` member attains `Θ₀ = 10` through entry-driven content while `ω₀ = 0`
(`EFF.T4.19`, retained at D.53 and §12). This is the same fence that keeps D.49's equivalence
about `f_key` alone, and it is the reason the corpus records that consumers "invoke (d) only
through its cancellation leg (FR-M3's measured `ω₀ = 0`) and its no-other-member warning, never
through the no-source leg".

## Faithfulness

**No hypothesis is consumed** — not `j < F.μ₂`, not `fkey_mem`, not `floor`. Both sides are
definitional unfoldings of `F.omega j`, so the equivalence is total in `j`, including outside the
coordinate range where D.46's (FLOOR) says nothing. That is a strengthening relative to the
corpus's quantifier and it is safe: adding `hj` would only shrink the statement, and D.49 (which
DOES need the range) carries `hj` itself.

**`ω_j = 0` is vanishing of the whole `Slot →₀ K` digit**, i.e. of every canonical slot at height
`Θ_j` — not of one named slot. The named-slot sharpening is D.51's direction (a nonzero value at
one slot gives `Touched`); this lemma is its exact converse at the level of the whole finitely
supported function.

**No new definition** — nothing is added to the trust boundary beyond D.46/D.48's own flagged
definitions.

DEPENDS: D.48 (`CertFrame.omega`, `CertFrame.Touched`, landed at `Uniformity.ChapD.D48`) and
through it D.46 (`CertFrame`) · mathlib `not_not`, `ne_eq`. Nothing else — in particular not
D.47's `nuIdx` and not D.45's `thresholdTheta`.

SOURCE: `EFF.T4.17` (R4-G1's replaced clause (d): the all-provenance and cancellation legs, the
two warnings, and the record that consumers invoke (d) only through its cancellation leg and its
no-other-member warning, never through the no-source leg); `HYP.114`.

**TEETH.** S8 PE1(1); PE2 GT3 (FR-M3's measured `ω₀ = 0`) and GT6 (FAM-E/FAM-D no-overflow
controls) → retained regressions in §12. Nothing is scored in this file: the FR-M3 numerals are
gate D.66 leg 4's, and the `CertFrame` inhabitation witness that makes this equivalence
non-vacuous is D.68's census row (A-D.1 addition (v)).

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, written inline
as the declaration's own binders.

## Status

Sorry-free, axiom-free (Lean core only): `omega_zero_iff_untouched` is a PROVED theorem here, not
the leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.52 — LEMMA T4.2(d): the no-contribution criterion** (`EFF.T4.17`).  `ω_j = 0 ↔ ¬ Touched
j`: in D.46's frame the corpus's two legs — no summand of any provenance lands in a height-`Θ_j`
slot, or the complete assembled contribution cancels — are the single equation
`grΔ (Θ_j) j f_key = 0`, since complete assembly is `grΔ`'s instantiation obligation.
⚠ (i) absence of single-extraction sources alone does NOT discharge that equation: the exclusion
must cover every provenance in DEFINITION T4.1's assembly (`HYP.114`, the instance burden, as at
D.51).  ⚠ (ii) NO attainment statement for another member follows — entry-driven content may
still attain `Θ_j` (FR-M3's `W` member attains `Θ₀ = 10` while `ω₀ = 0`, `EFF.T4.19`). -/
theorem CertFrame.omega_zero_iff_untouched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : F.omega j = 0 ↔ ¬ F.Touched j := by
  simp only [CertFrame.Touched, ne_eq, not_not]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.omega_zero_iff_untouched

end AxCheck
