/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E39
import Uniformity.ChapE.E40

/-!
# Uniformity.ChapE.E44 — `LadderObligations`: what chapter I receives from the σ-ladder

**Chapter E, NODE E.44** [def] (`blueprint/CHAP-E_sigma_ladder.md` §6, **RE-SIGNED at A-E.2,
2026-08-16 — field list BYTE-UNCHANGED**, and universe-repaired by A-E.1/E-D6), ENV-E2.

One `structure`, two fields, no proof obligation: the chapter-E obligations record bundles the §6
dispositions in one place so that chapter I has a single object to consume.

## The four §6 dispositions, and which of them is a field

| item | disposition | carrier here |
| --- | --- | --- |
| `(LB1)` (`EFF.T2.18`) | CARRIED-OPEN | field `lb1` — E.39's `LB1Carrier` |
| `(MP1)` (`EFF.T2.23`) | CARRIED-OPEN | field `mp1` — E.40's `MP1Carrier` |
| `(MP1′)` (`EFF.T2.25`) | **RETIRED** | **none, deliberately** |
| `(SEC-RANK)`, `(RISE)` (`EFF.T2.52`) | carrier hypotheses that fence nothing | none here |

`(MP1′)` *"denotes a consequence of the pins, not an obligation. No instance record carries it and
no ledger item fences it"* (`EFF.T2.25`). **Declaring a carrier for it would resurrect a retired
name**, so this file declares none — and the absence is not a matter of trust: gate (c) below
proves the record is EXACTLY the conjunction of its two fields, which fails the moment a third
appears. `(SEC-RANK)` and `(RISE)` are likewise absent as chapter-I conjuncts because the
acceptance record states each *"fences no read"* (`EFF.T2.52`); they live as E.12 interface fields
and E.35 hypotheses, where they are consumed locally.

## ⚠ RE-SIGN (A-E.2): the field list did not move, the record's CONTENT did

OM-4 FINDING 0 (`docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3; machine witness
`verification/om4_shadow_vacuity.lean`, `ladderObligations_shadow_trivial`) proved the
as-committed record trivially inhabitable — both of its fields were vacuous shadows, so the whole
bundle was provable from nothing and tracked no conditionality at all. A-E.2 fixed that **without
touching this file's signature**: the two carriers were re-signed at their full contentful records
(`BlockSuite` at E.39, `MidPeelEmission` at E.40), and `LadderObligations` is strengthened
*through them*. The pre-A-E.2 record is NAMED-AND-VOID for chapter-I consumption; a consumer or
discharge citing it is a defect.

Gate (d) makes the inheritance machine-visible in exactly the form the certificates come in: the
non-triviality of the re-signed carriers is certified as REFUTATIONS at concrete data
(`verification/om4_resign_nontriviality.lean` — `lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁`
over a real `SlotCarrier ℤ ℚ` with `B₁.F = X² + X + 1`; `mp1_resigned_not_trivial :
¬ MP1Carrier C₂ B₂` at key `X²`, `F = X⁴ − 5X² + 4`), and the gate transports each refutation to a
refutation of the RECORD. So this bundle is certified non-trivial at the same data, by projection,
with nothing imported from the verification files.

## ⚠ UNIVERSE SCOPE, DECLARED (A-E.1/E-D6; honesty E-12)

Both fields quantify over `RungInterface`, whose rank carrier `W` lives in a universe Lean cannot
quantify over inside a `Prop`. So the record is itself universe-scoped:
`LadderObligations.{uO, uK, uW}` bundles the two obligations **AT ONE `uW`**, and the explicit
`universe uO uK uW` plus the explicit `LB1Carrier.{uO, uK, uW}` / `MP1Carrier.{uO, uK, uW}`
spellings are mandatory, not stylistic — without them Lean reports *"declaration contains universe
level metavariables"* (the stage-0e hard error, one of the four A-E.1 repaired at E.24, E.39, E.40
and here). **Chapter I's row-disposition census must consume the universe parameter along with the
field list**: either its Display-A hypothesis field is universe-polymorphic
(`∀ {uW}, LadderObligations.{…, uW} C B`), or it instantiates at the one `uW` its capstone
instance uses and records that choice. Gate (a) exercises the binding pattern.

**This node PROVES nothing and DISCHARGES nothing.** Both obligations are OPEN; chapter I carries
them (Part V's two-gate ruling). `PROOF.` in the blueprint reads *definitional*, and that is what
lands.

DEPENDS: **E.39** (`leanfinal/Uniformity/ChapE/E39.lean` — `LB1Carrier`, itself over E.14 and
E.39a's `BlockSuite`), **E.40** (`leanfinal/Uniformity/ChapE/E40.lean` — `MP1Carrier`, over E.12
and its `MidPeelEmission`). Transitively E.10–E.12 supply the arena (`SlotCarrier`, `BlockData`).

SOURCE: `EFF.T2.44` (acceptance: *"The two open obligations and the HE3 supplier cap survive"*);
EFF-T2 §9 (the two-obligation census: `(LB1)` and `(MP1)` are the only open mathematical
obligations, distinguished there from the two carrier hypotheses that fence nothing);
`EFF.T2.25` (`(MP1′)` retired); `EFF.T2.52` (`(SEC-RANK)`/`(RISE)` fence no read); Part V (the
two-gate ruling this record feeds); blueprint amendments **A-E.2** (the semantic re-sign) and
**A-E.1/E-D6** (the universe repair).

TEETH: none of its own — bookkeeping. The teeth are the consumer's: chapter I's row-disposition
census consumes THIS field list as ground truth for the `(LB1)`/`(MP1)` Display-A conjuncts, which
is precisely why gate (c) pins the field list to exactly two.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, axiom-free: every declaration reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Transcribed declaration-for-declaration against the
signed A-E.2 SIGNATURE (`leanspec/Leanspec/ChapE.lean` §6): field names, field order, field types
and the universe spelling unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- E.12's three universes, bound explicitly (A-E.1/E-D6): `uW` occurs only inside
-- `RungInterface`, which both carrier `Prop`s quantify over, so this record must name it.
universe uO uK uW

/-- The chapter-E obligations record: what chapter I receives from the σ-ladder.
[A-E.2: binds the re-signed carriers; chapter I consumes the Display-A conjunct
`LB1 ∧ MP1` at THIS form only, universe-polymorphically (honesty E-12).]

`(MP1′)` is RETIRED (`EFF.T2.25`) and deliberately has NO field — declaring one would resurrect a
retired name. `(SEC-RANK)`/`(RISE)` fence no read (`EFF.T2.52`) and are E.12/E.35 data, not
chapter-I conjuncts. -/
structure LadderObligations {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop where
  -- [repaired: A-E.1/E-D6] both carriers instantiated at the record's own `uW`
  lb1 : LB1Carrier.{uO, uK, uW} C B
  mp1 : MP1Carrier.{uO, uK, uW} C B

/-! ## Gates (executed `example`s, not blueprint declarations)

**(a) The A-E.1/E-D6 binding pattern, at a consumer's shape.** A `Prop` that quantifies the record
with `uW` bound — chapter I's Display-A hypothesis field. The universe defect the amendment
repaired is invisible on the structure declaration itself and surfaces only here, so a regression
in the plumbing fails at this line.

**(b) Both projections are available in the Display-A shape.** `LB1 ∧ MP1` read off the record.

**(c) The record is EXACTLY the conjunction of its two fields — the field list, pinned.** The
right-to-left direction is the load-bearing one: it constructs the record from `LB1Carrier` and
`MP1Carrier` ALONE, so it fails the instant a third field is added. That is the machine check
behind two prose claims this file makes — that `(MP1′)` has no carrier here, and that
`(SEC-RANK)`/`(RISE)` are not chapter-I conjuncts. It is also the check that the record adds no
strength of its own beyond bundling.

**(d) The A-E.2 non-triviality is INHERITED, by projection.** The certificates in
`verification/om4_resign_nontriviality.lean` are refutations of the re-signed carriers at concrete
data; each transports to a refutation of the record. So the bundle is non-trivial wherever either
carrier is — and, contrapositively, the pre-A-E.2 record's provability-from-nothing cannot recur
while these fields stand. Stated as implications so that nothing is imported from the verification
files. -/

section Gate

-- (a) the E-D6 binding pattern at a consumer's shape.
example : Prop :=
  ∀ {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K) (B : BlockData C),
    LadderObligations.{uO, uK, uW} C B

-- (b) the Display-A conjunct, read off the record.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (h : LadderObligations.{uO, uK, uW} C B) :
    LB1Carrier.{uO, uK, uW} C B ∧ MP1Carrier.{uO, uK, uW} C B :=
  ⟨h.lb1, h.mp1⟩

-- (c) the field list is EXACTLY `lb1`, `mp1`: the record is the conjunction, both ways.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K)
    (B : BlockData C) :
    LadderObligations.{uO, uK, uW} C B ↔
      (LB1Carrier.{uO, uK, uW} C B ∧ MP1Carrier.{uO, uK, uW} C B) :=
  ⟨fun h => ⟨h.lb1, h.mp1⟩, fun h => ⟨h.1, h.2⟩⟩

-- (d) each carrier's certified non-triviality transports to the record.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (hlb1 : ¬ LB1Carrier.{uO, uK, uW} C B) :
    ¬ LadderObligations.{uO, uK, uW} C B :=
  fun h => hlb1 h.lb1

example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (hmp1 : ¬ MP1Carrier.{uO, uK, uW} C B) :
    ¬ LadderObligations.{uO, uK, uW} C B :=
  fun h => hmp1 h.mp1

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node. The type former asserts nothing about its fields, so the two fields are printed
alongside the former and its constructor. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LadderObligations
#print axioms Uniformity.Density.Ladder.LadderObligations.mk
#print axioms Uniformity.Density.Ladder.LadderObligations.lb1
#print axioms Uniformity.Density.Ladder.LadderObligations.mp1

end AxCheck
