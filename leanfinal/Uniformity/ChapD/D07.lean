/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D01

/-!
# Uniformity.ChapD.D07 — `GaugeArena`, DECISION D-1's residue interface

**Chapter D, NODE D.07** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — A-D.1 corrected this node's SIGNATURE
DOCSTRING in place, rider R-2, because a stale carrier ID inside a docstring reaches
`leanfinal`; A-D.2's DECISION D-2 leaves the structure itself byte-unchanged). ENV-D2 + ENV-D3.
One signed declaration, definitional.

*The gauge arena (DECISION D-1's structure).* A **gauge arena** over a section
`N : NormSection G` with letter field `K` consists of:

* a height homomorphism `v : G →* Multiplicative ℤ`;
* the **exact-height** clause `v (n k) = ofAdd k` for every `k : ℤ` (`EFF.T1.01`'s "for every
  integer height `k`, `n̂₁(k) = x^{i(k)}π^{a(k)}` with `i(k)h + a(k)e₁ = k`" — the exponent
  identity is exactly what makes `n̂₁(k)` land at height `k`, abstracted);
* a residue homomorphism `res : v.ker →* Kˣ` on the value-zero subgroup.

Every §3 combination — `tau` (D.02), `varthetaEl`/`thetaEl` (D.04), the descending bracket, and
`chi` for two sections with the same `v` — lies in `v.ker` by exact-height arithmetic, so its
`K`-valued residue is defined. Those four membership facts and the `Kˣ`-valued telescope they
carry are D.08's (`mem_ker_div`, `varthetaEl_mem_ker`, `thetaEl_mem_ker`, `tau_mem_ker`,
`vartheta`, `theta`), not this node's: this file is the interface and nothing else.

## Faithfulness

**⚠ Mandatory, trust-boundary definition — this is the chapter's ONE structural repackaging
(DECISION D-1, honesty item D-H3), and it is formally STRONGER than its source.** Flagged for
the chapter cross-read (§13 item 2) and for chapter I's conjunct bookkeeping.

* *(i) the strength delta, stated.* The corpus's five C3 read clauses (`EFF.T1.03`) are
  **SITEWISE** — obligations "at each consumed B-law site" — and `EFF.T1.09`'s ϑ-membership is
  fenced per depth. This structure instead asserts hom-ness and `Kˣ`-membership on **all** of
  `v.ker`. The licence is that the two instances the corpus actually proves are genuine
  homomorphisms on their consumed arenas: at `i = 1` the arena is `⟨x^{e₁}/π^h⟩` with
  `res((x^{e₁}/π^h)^t) = η^t` (`EFF.T1.01`); at `i = 2` GENTOW2's γ-calculus proves the value-0
  Laurent monomials `x^i π^a Φ′^b` form exactly the group `⟨γ₁, γ₂⟩` with `res(γ₁(x₀)) = z₁`,
  `res(γ₂(x₀)) = z₂` (`EFF.GENTOW2.42`). At `i ≥ 3` **NO instance is claimed** — supplying this
  structure at depth IS the `(H-VARTHETA-RES)_i` hypothesis. The rejected alternative (sitewise
  multiplicativity hypotheses clause-by-clause on every consuming node) is recorded as viable
  in D-H3; it was rejected because it multiplies every §3/§6 signature by three to five
  hypothesis slots and makes the group-algebra layer unprovable as group algebra.
* *(ii) which direction the strength claim survives in.* Defect D-D12 (stage-0e gate,
  stop-the-line, machine-checked) refuted the EXISTENTIAL rendering of D-H3: `∃ A : GaugeArena
  G K N, A.v = v` is discharged by the trivial hom `1 : ker v →* Kˣ`, since this structure has
  no field tying `res` to an ambient residue map. **The structure itself is unaffected** —
  A-D.1's note and DECISION D-2 ground 2 both fix this — and D-H3's "formally stronger" claim
  holds for `GaugeArena` used as a **THEOREM HYPOTHESIS**, which is the only way this chapter
  uses it. A-D.2 restored the claim as a proved lemma at D.62
  (`hvarthetaRes_of_arena_agree`: an arena whose `res` agrees with a GIVEN ambient residue
  datum on the value-zero subgroup discharges the sitewise carrier); the agreement leg is
  exactly what the voided existential lacked. Consumers must take the hypothesis form, never
  the existential one.
* *(iii) what is NOT a field here.* The graded reads `R_{i+1,β}` at NONZERO grade are not
  fields of this structure — the arena covers only the value-zero residue algebra (τ/ϑ/χ). The
  positive-grade read obligations stay in D.29's `ReadBundle`, sitewise, exactly as `EFF.T1.03`
  states them. Likewise `exact_height` is a clause about `N`'s heights only; no valuation on
  `K`, no tower, and no finiteness enters (`K` is any field, ENV-D3 carries no finiteness —
  nothing in this chapter counts).

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: D.01 (`NormSection`, landed at `Uniformity.ChapD.D01`) · mathlib `MonoidHom.ker`
(`Subgroup`-valued) and `Multiplicative ℤ`. No landed node beyond D.01.

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
verbatim, with the blueprint's `namespace Uniformity.Density.Gauge` header restored (the
leanspec wrapper `LeanspecD` is a stub-side artifact; the landed namespace assignment is
`Uniformity.Density.Gauge`, GC-6.2). The declaration docstring is the blueprint SIGNATURE's, as
corrected in place by A-D.1 rider R-2 (`(H-VARTHETA-RES)_i` is **D.62** in the post-A-1
numbering, "D.67" pre-A-1) — a stale carrier ID inside a docstring is landed text, which is why
that one correction was applied rather than deferred to the renumbering sweep.

SOURCE: `EFF.T1.01`–`.03` (packaging per DECISION D-1: `.01`'s level-1 carrier with the
exact-height exponent identity, `.03`'s five sitewise C3 read clauses); `EFF.GENTOW2.42` (the
`i = 2` licence — the value-0 monomials are exactly `⟨γ₁, γ₂⟩` and `res` is multiplicative
there); `EFF.T1.09` (the depth fence that the `i ≥ 3` instantiation IS).

**TEETH.** None directly (a definition); its instances carry the batteries — D.17's
`levelOneArena` at level 1 and the §10 gates. The FAITHFULNESS items above are cross-read
obligations, not scorable teeth, which is exactly why §13 item 2 exists.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]` and `{K : Type*} [Field K]`, written
inline per the B.42 binder rule — this file has no `variable` block; `G`, `K` and `N` are the
structure's own explicit parameters, as signed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- DECISION D-1's residue interface. Instantiations: level 1 = D.17 (η-powers); level 2 =
GENTOW2's letter group `⟨γ₁, γ₂⟩` (`EFF.GENTOW2.42`, supplied by chapter C); depth `i ≥ 3` =
exactly the `(H-VARTHETA-RES)_i` conditionality (**D.62** = `HVarthetaRes`; "D.67" in the
pre-A-1 numbering) — supplying this structure at depth IS the hypothesis. FAITHFULNESS:
formally stronger than the sitewise clauses; see CHAP-D honesty item D-H3 and §13 item 2.
⚠ D-D12 (stage-0e gate, stop-the-line): the EXISTENTIAL form of that reading — D.62's
`HVarthetaRes` — is VACUOUS as signed; re-signed by the Display-A carrier adjudication unit as
DECISION D-2 / amendment A-D.2 (see §9's A-D.1 cross-reference stub). This structure itself is
unaffected. -/
structure GaugeArena (G : Type*) [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) where
  /-- The height homomorphism `v` of the arena: `EFF.T1.02`'s integer heights, multiplicatively
  spelled as `Multiplicative ℤ` so that `v` is a `MonoidHom`. -/
  v : G →* Multiplicative ℤ
  /-- The **exact-height** clause: the normalizer at height `k` really sits at height `k`
  (`EFF.T1.01`'s `i(k)h + a(k)e₁ = k`, abstracted). This is what puts every `τ`/`ϑ`/`Θ`
  combination in `v.ker` (D.08). -/
  exact_height : ∀ k : ℤ, v (N.n k) = Multiplicative.ofAdd k
  /-- The residue homomorphism on the value-zero subgroup, into `Kˣ`. DECISION D-1's
  packaging: formally stronger than `EFF.T1.03`'s sitewise clauses — see the module
  docstring's FAITHFULNESS item (i). -/
  res : MonoidHom.ker v →* Kˣ

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena
#print axioms Uniformity.Density.Gauge.GaugeArena.mk

end AxCheck
