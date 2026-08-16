/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E12

/-!
# Uniformity.ChapE.E39a — `BlockSuite`, the FULL S1.7A block suite `(LB1)` demands

**Chapter E, NODE E.39a** [structure] — the record half of NODE E.39 (`(LB1)`), signed by
amendment **A-E.2** (2026-08-16) and landed under the stub's own label
(`leanspec/Leanspec/ChapE.lean` §6, `E.39a [structure, signed at A-E.2]`). ENV-E2 (the carrier
arena: the bundle `O`, the label field `K`, a slot carrier `C : SlotCarrier O K` from E.10, a
block `B : BlockData C` from E.11, and a trigger interface `I : RungInterface C B` from E.12).

`(LB1)` (`EFF.T2.18`) is the level-one **clause-4 block-construction** obligation: every
level-one state whose clause-4 processing demands blocks — every state with at least two sides,
and every side whose residual is mixed — has the monic side and label blocks of S1.7A, *"with
their own full developments, single-side hulls, pure residuals, product identities, disjoint
exhaustive root partitions, and inherited continuation data"*. **`BlockSuite I` is exactly that
suite**, one field per `EFF.T2.17` display.

## ⚠ THIS FILE LANDS THE RECORD ONLY — `LB1Carrier` (E.39) IS RESCHEDULED

The carrier that quantifies this record,

    def LB1Carrier … (C : SlotCarrier O K) (B : BlockData C) : Prop :=
      ∀ I : RungInterface.{uO, uK, uW} C B,
        (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) → Nonempty (BlockSuite I)

is **NOT declared here**: its TRIGGER clause names `RungInterface.SepSide`, which is **NODE
E.14**'s declaration, and E.14 has not landed (`leanfinal/Uniformity/ChapE/` has no `E14.lean`;
`grep -rn SepSide leanfinal/Uniformity/` returns one prose mention in E.11 and no `def`). The
signed trigger is not weakened, not paraphrased, and not replaced by an inlined copy of
`SepSide` — E.39 waits for E.14 and then costs five lines, in its own `E39.lean`, importing this
module. Record: `leanfinal/notes/RESCHEDULE_E39_2026-08-16.md`.

## ⚠ RE-SIGN (A-E.2) — the committed shadow was MACHINE-REFUTED VACUOUS

The as-committed E.39 conclusion kept only the product identity and the degree sum,

    ∃ blocks : List (Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'),
      B.F = (blocks.map fun x => x.1.F).prod ∧
      (blocks.map fun x => x.1.F.natDegree).sum = B.F.natDegree

and was therefore provable **for every carrier, block and trigger interface, from nothing** — the
singleton **self-block** `[⟨B, I⟩]` satisfies it (OM-4 FINDING 0,
`docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3; machine witness
`verification/om4_shadow_vacuity.lean`, archived under `OM4Shadow.LB1CarrierVoided`). A trivially
true hypothesis tracks no conditionality, so the committed form was strictly NARROWER than
source — all the way to empty. The self-block refutation is mirrored as gate (b) below, so the
reason for the re-sign is machine-visible in this file; the pre-A-E.2 shadow is
NAMED-AND-VOIDED, and any consumer or discharge citing it is a defect.

Non-triviality of the re-signed record is certified in
`verification/om4_resign_nontriviality.lean` (`lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁` —
a real `SlotCarrier ℤ ℚ`, `B₁.F = X² + X + 1`, and a legal two-side trigger interface with unit
class weights: `hcount` + `hdegsum` + `hprod` would force a monic-linear integer factorization of
`X² + X + 1`, which does not exist, so the self-block and every recipe of its genre FAIL).

## Field ↔ display table (`EFF.T2.17`/`.18`, source-verified at A-E.2)

| field | source display |
| --- | --- |
| `blocks` | `EFF.T2.18` "own full developments … inherited continuation data"; `EFF.T2.28`: *"Every residual block `B_j` is a σ-block for the same carrier and satisfies the complete HE7.A input suite"* — "same carrier" is enforced by TYPE (`BlockData C`), the input suite by the paired `RungInterface` |
| `hprod` | `(SIDE-PROD)` `F = ∏_λ F_λ` · `(LABEL-PROD)` `F_λ = ∏_{r′} F_{λ,r′}` |
| `hdisj`, `hdegsum` | `EFF.T2.18` "disjoint exhaustive root partitions", in the master's shadow: pairwise coprimality over `Frac(O)` plus degree accounting |
| `hone` | `EFF.T2.18` "single-side hulls" |
| `hpure` | `(LABEL-PURE)` `R(F_{λ,r′}) = c·r′^k` — ONE residual class, of OWN multiplicity `k ≥ 1` |
| `hpure`'s `k ≥ 1` + E.12's laws | `(LABEL-OWN)` `k = ν/(e′·deg r′) ∈ ℤ_{≥1}`: with one side and one class, `hlen_sum` + `hresdeg` force `μ = k·e′·deg r′` |
| `hcoverLin`, `hcoverHi`, `hcount` | E.39's STATEMENT: *"for each side `p` and factor `q`, a `BlockData` … whose weight (degree) is `classCount`-compatible"* — both directions carried |
| `hthr` | `EFF.T2.18` "inherited continuation data" (threshold leg; the `(SEC-RANK)` continuation fields ride each block's own `RungInterface`, `EFF.T2.27`'s footing) |

## ⚠ THE PARENT-MULTIPLICITY NON-IMPORT (a fence, not an omission)

`hpure` demands the block's residual be pure of some multiplicity `k ≥ 1` **of its own**, and
deliberately does NOT tie `k` to the parent residual factorization's `m` — `EFF.T2.17`, verbatim:
*"No equality between `k_{λ,r′}` and `m_{λ,r′}` from the parent residual factorization is
assumed"* (rider r2 deleted r1's formula). E.17 records the same fence on the continuation
trichotomy's `k`. A future strengthening that adds `k = m` would be an amendment, not a repair.

## Honest residue, disclosed (blueprint's own ⚠, transcribed)

At a one-side SINGLE-class repeated state the suite can be the state itself, and the purity
fields live in E.12's **numerical shadow** — which by design does not tie interface numbers to
polynomials. Polynomial-level purity is what the instance discharge supplies (C.33/C.34, OM-4
§3.1); the carrier's non-vacuity is certified at the multi-side/multi-class triggers, which is
exactly where its TRIGGER fires. `(LB1)`'s terminal fate is REDUCES-TO (C.33 + C.34 + an E-side
discharge unit at the instance rows), with the contingent [GN15] Thm 2.3 cite on C.33's route
risk. **Nothing is discharged here**: this node states, it does not prove.

## ⚠ UNIVERSE SCOPE, DECLARED (A-E.1/E-D6; honesty E-12)

`BlockSuite` carries `RungInterface.{uO, uK, uW}` in two places (the `blocks` list and the
parameter `I`), so once quantified it is universe-SCOPED: `LB1Carrier.{uO, uK, uW}` will assert
the suite's existence for the interfaces whose rank carrier `W` lives in universe `uW`, not for
all interfaces at once — Lean cannot quantify over universes inside a `Prop`. This is a scoping
fact, not a strength change; chapter I consumes the carrier universe-polymorphically or records
its `uW` choice. The explicit `universe uO uK uW` + explicit `RungInterface.{uO, uK, uW}`
spelling is mandatory, not stylistic: without it Lean reports *"Failed to infer universe levels
in type of binder `I`"* (the stage-0e hard error the amendment repaired).

DEPENDS: E.10 (`SlotCarrier`), E.11 (`BlockData`, and its `IsCoprime`-over-`FractionRing O`
spelling, reused verbatim by `hdisj`), E.12 (`RungInterface`, `sides`/`linFac`/`hiFac`/
`classCount`/`classCountHi`, and the three-universe convention) · E.17 conceptually (the
continuation trichotomy this suite feeds; nothing is imported from it) · mathlib `List.Pairwise`,
`Multiset`, `Finset`, `Polynomial.map`, `FractionRing`, `IsCoprime`, `Sigma`.

SOURCE: `EFF.T2.18` (boxed `(LB1)`, the enumeration sentence, and the scoping paragraph:
*"Two level-one routes remain conditional, each where it is taken: the clause-4 route on `(LB1)`,
and the clause-5 peel at a recentered key on `(MP1)` … No level-one route is asserted
unconditional simpliciter"*); `EFF.T2.17` (the S1.7A displays, and the `k`/`m` non-import);
`EFF.T2.28` (the σ-block continuation shape — ⚠ OM-4 §1.1 cites this display as `EFF.T2.75`, a
merged-numbering slip: the quote is verbatim-correct, at `.28`); ledger Display A (the `(LB1)`
conjunct); blueprint amendment **A-E.2** (the re-sign) and **A-E.1/E-D6** (the universe repair).

TEETH: S7 mixed-residual and multi-side hostile cases → **signed non-applicability at level one**
(the corpus's own disposition — the obligation is OPEN); at level ≥ 2 the analogue is PROVED
content (ANNEX-LEMMA HE7-13′ = E.57), which is why the carrier is level-indexed by its
instantiation, not globally. The vacuity attack that killed the committed form is closed at the
record level and mirrored as gate (b).

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, axiom-free. Definitional node: every declaration reports at most the Lean-core
triple `{propext, Classical.choice, Quot.sound}`. Types checked field by field against the
signed A-E.2 SIGNATURE (field names, field order and every field's statement unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- E.12's three universes, bound explicitly (A-E.1/E-D6): `uW` occurs only inside
-- `RungInterface`'s body, so anything quantifying over an interface must name it.
universe uO uK uW

/-- **The FULL S1.7A block suite** over a trigger interface: the contentful record `(LB1)`
demands [signed at A-E.2]. Per-display fields (`EFF.T2.17`/`.18`): product identity,
disjointness/exhaustion shadow, own single-side hulls, pure residuals with `(LABEL-OWN)`
integrality, parent `classCount` compatibility (both directions), and inherited continuation
data (each block a σ-block for the SAME carrier — enforced by TYPE — with its own
`RungInterface`, i.e. the HE7.A input suite's numerical shadow, and the inherited threshold). -/
structure BlockSuite {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) where
  /-- the blocks, each with its own development (`BlockData.hdev` = `(LABEL-DEV)`) and its
  own carrier-hypothesis suite (`RungInterface` = the HE7.A input-suite shadow, incl. the
  `(SEC-RANK)` continuation fields). -/
  blocks : List (Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B')
  /-- `(SIDE-PROD)`·`(LABEL-PROD)`: the blocks multiply to `F`. -/
  hprod : B.F = (blocks.map fun x => x.1.F).prod
  /-- disjoint root partitions, master shadow: pairwise coprimality over the fraction
  field. -/
  hdisj : blocks.Pairwise fun x y =>
    IsCoprime (x.1.F.map (algebraMap O (FractionRing O)))
      (y.1.F.map (algebraMap O (FractionRing O)))
  /-- exhaustive root partitions, degree accounting. -/
  hdegsum : (blocks.map fun x => x.1.F.natDegree).sum = B.F.natDegree
  /-- own single-side hulls: every block is one-sided. -/
  hone : ∀ x ∈ blocks, ∃ p, x.2.sides = {p}
  /-- `(LABEL-PURE)` + `(LABEL-OWN)`, numerical shadow: the single side carries exactly ONE
  residual class, of some OWN multiplicity `k ≥ 1` (the interface laws then force
  `μ = k·e′·deg r′`, i.e. `(LABEL-OWN)` integrality).  NOT tied to the parent class
  multiplicity — `EFF.T2.17`: "No equality between `k` and `m` … is assumed". -/
  hpure : ∀ x ∈ blocks, ∀ p ∈ x.2.sides,
    (∃ (s : K) (k : ℕ), 1 ≤ k ∧ x.2.linFac p = {(s, k)} ∧ x.2.hiFac p = 0) ∨
    (∃ d k : ℕ, 1 ≤ k ∧ 2 ≤ d ∧ x.2.hiFac p = {(d, k)} ∧ x.2.linFac p = 0)
  /-- parent-`classCount` compatibility, cover direction: every parent `(side, class)` pair
  is realized by a block of exactly its recorded weight, one-sided at the parent's own
  slope datum, pure in the parent's class. -/
  hcoverLin : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p, ∃ x ∈ blocks,
    x.2.sides = {p} ∧ (∃ k : ℕ, 1 ≤ k ∧ x.2.linFac p = {(q.1, k)}) ∧
    x.1.F.natDegree = I.classCount p q
  hcoverHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p, ∃ x ∈ blocks,
    x.2.sides = {p} ∧ (∃ k : ℕ, 1 ≤ k ∧ x.2.hiFac p = {(q.1, k)}) ∧
    x.1.F.natDegree = I.classCountHi p q
  /-- parent-`classCount` compatibility, sort direction: every block's weight is one of the
  parent's recorded class weights. -/
  hcount : ∀ x ∈ blocks, ∃ p ∈ I.sides,
    (∃ q ∈ I.linFac p, x.1.F.natDegree = I.classCount p q) ∨
    (∃ q ∈ I.hiFac p, x.1.F.natDegree = I.classCountHi p q)
  /-- inherited continuation data: the threshold is inherited (the frame does not move). -/
  hthr : ∀ x ∈ blocks, x.1.T = B.T

/-! ## Gate (executed `example`s, not blueprint declarations)

Three things this definitional node can get wrong silently, checked here rather than asserted.

**(a) The E-D6 quantifier pattern elaborates.** The universe defect A-E.1 fired on is invisible
at a structure declaration and appears only at a `Prop` that quantifies over an interface. The
gate reproduces exactly `LB1Carrier`'s shape *minus its `SepSide` trigger* (the untranscribable
half — see the RESCHEDULE banner above), so a regression in the universe plumbing fails HERE.

**(b) The VOIDED shadow, mirrored: the singleton self-block.** OM-4 FINDING 0's first leg, in
one line — the committed conclusion (product identity + degree sum only) is satisfied by
`[⟨B, I⟩]` for EVERY carrier, block and interface, so it constrained nothing. This is why A-E.2
re-signed the node, and it is the standing lower bound on any future weakening: a proposal to
weaken `BlockSuite` must first show this witness fails the weakened form.

**(c) The re-signed record has bite where the shadow had none.** The empty suite `blocks = []`
also satisfied the voided conclusion whenever `F = 1`; under `BlockSuite` it is impossible as
soon as the parent records a single linear residual class, because `hcoverLin` demands a block
realizing it. Cover-direction teeth, machine-checked. -/

section Gate

-- (a) the E-D6 pattern: a `Prop` quantifying over an interface and its suite, `uW` bound.
example : Prop :=
  ∀ {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B), Nonempty (BlockSuite I)

-- (b) the voided shadow's conclusion, satisfied by the singleton self-block, always.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) :
    ∃ blocks : List (Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'),
      B.F = (blocks.map fun x => x.1.F).prod ∧
      (blocks.map fun x => x.1.F.natDegree).sum = B.F.natDegree :=
  ⟨[⟨B, I⟩], by simp, by simp⟩

-- (c) the re-signed record forbids the empty suite at any state carrying a linear class.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B} (S : BlockSuite I)
    {p : ℕ × ℕ} (hp : p ∈ I.sides) {q : K × ℕ} (hq : q ∈ I.linFac p) : S.blocks ≠ [] := by
  obtain ⟨x, hx, -⟩ := S.hcoverLin p hp q hq
  exact List.ne_nil_of_mem hx

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node. The structure former asserts nothing about its fields, so every field
carrying a display of the suite is printed one by one alongside the type former and its
constructor. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.BlockSuite
#print axioms Uniformity.Density.Ladder.BlockSuite.mk
#print axioms Uniformity.Density.Ladder.BlockSuite.blocks
#print axioms Uniformity.Density.Ladder.BlockSuite.hprod
#print axioms Uniformity.Density.Ladder.BlockSuite.hdisj
#print axioms Uniformity.Density.Ladder.BlockSuite.hdegsum
#print axioms Uniformity.Density.Ladder.BlockSuite.hone
#print axioms Uniformity.Density.Ladder.BlockSuite.hpure
#print axioms Uniformity.Density.Ladder.BlockSuite.hcoverLin
#print axioms Uniformity.Density.Ladder.BlockSuite.hcoverHi
#print axioms Uniformity.Density.Ladder.BlockSuite.hcount
#print axioms Uniformity.Density.Ladder.BlockSuite.hthr

end AxCheck
