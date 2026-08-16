/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E14
import Uniformity.ChapE.E39a

/-!
# Uniformity.ChapE.E39 — `(LB1)`: the level-one clause-4 block obligation, RE-SIGNED at A-E.2

**Chapter E, NODE E.39** [def] (`blueprint/CHAP-E_sigma_ladder.md` §6, **as RE-SIGNED by
amendment A-E.2, 2026-08-16**, and universe-repaired by A-E.1/E-D6), ENV-E2.

`(LB1)` (`EFF.T2.18`) is the level-one **clause-4 block-construction** obligation: every
level-one state whose clause-4 processing demands blocks — a state with at least two sides, or
a state with a side whose residual is mixed — has the monic side and label blocks of S1.7A,
*"with their own full developments, single-side hulls, pure residuals, product identities,
disjoint exhaustive root partitions, and inherited continuation data"*.

This file is the **carrier** — the `Prop` that quantifies E.39a's record. It is five lines of
transcription over two landed modules:

* the TRIGGER reads `RungInterface.SepSide` from **E.14** (`leanfinal/Uniformity/ChapE/E14.lean`,
  landed 2026-08-16): a side is separable, in the numerical shadow, when every residual
  multiplicity on it is `1`. The trigger fires at multi-side states (`1 < I.sides.card`) and at
  mixed states (`∃ p ∈ I.sides, ¬ I.SepSide p) `, and at NO one-side separable state —
  `EFF.T2.18`'s scoping, *"Clauses 1 and 2 are not [conditional]: their proofs run on the unsplit
  hull of `F` itself"*, honoured at E.16/E.41;
* the CONCLUSION is `Nonempty (BlockSuite I)` from **E.39a**
  (`leanfinal/Uniformity/ChapE/E39a.lean`, this session): the full S1.7A record, one field per
  `EFF.T2.17` display. Its field ↔ display table, the parent-multiplicity non-import fence, the
  vacuity mirror and the honest residue all live in that module's docstring and are not repeated
  here.

**This node PROVES nothing, and this is deliberate.** `LB1Carrier` is OPEN — a named capstone
hypothesis, one of Display A's two conjuncts (the other is `(MP1)` = E.40). **No chapter-E node
proves it**; chapter I carries it (Part V gate (b) or a discharge node), and its terminal fate is
REDUCES-TO (C.33 + C.34 + an E-side discharge unit at the instance rows), with the contingent
[GN15] Thm 2.3 cite on C.33's route risk. At level ≥ 2 the analogue is PROVED content
(ANNEX-LEMMA HE7-13′ = E.57) — which is why the carrier is level-indexed by its instantiation,
not globally.

## ⚠ RE-SIGN (A-E.2) — the committed shadow was MACHINE-REFUTED VACUOUS

The as-committed conclusion kept only the product identity and the degree sum, and was provable
for every carrier, block and interface **from nothing**: the singleton **self-block** `[⟨B, I⟩]`
satisfies it (OM-4 FINDING 0, `docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3; machine
witness `verification/om4_shadow_vacuity.lean`, archived under `OM4Shadow.LB1CarrierVoided`). A
trivially true hypothesis tracks no conditionality. A-E.2 strengthens the conclusion to the full
record with **names, binders and the TRIGGER byte-preserved**; the shadow is NAMED-AND-VOIDED and
any consumer or discharge citing it is a defect. The self-block refutation is mirrored as gate
(b) of E.39a; non-triviality of the re-signed carrier is certified in
`verification/om4_resign_nontriviality.lean` (`lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁` —
a real `SlotCarrier ℤ ℚ`, `B₁.F = X² + X + 1`, a legal two-side trigger interface with unit class
weights; `hcount` + `hdegsum` + `hprod` would force a monic-linear integer factorization of
`X² + X + 1`).

## ⚠ UNIVERSE SCOPE, DECLARED (A-E.1/E-D6; honesty E-12)

`LB1Carrier.{uO, uK, uW}` asserts the block-suite existence **for the interfaces whose rank
carrier `W` lives in universe `uW`** — not for all interfaces at once, since Lean cannot quantify
over universes inside a `Prop`. This is a scoping fact, not a strength change: at every
instantiation the consumer chooses `uW`, and the obligation is exactly `EFF.T2.18`'s at that
choice. **Chapter I must consume the carrier universe-polymorphically** (its hypothesis field is
`∀ {uW}, LB1Carrier.{…, uW} C B`), or instantiate at the one `uW` its capstone instance uses and
record that choice. Without the explicit `universe uO uK uW` and the explicit
`RungInterface.{uO, uK, uW}` spelling Lean reports *"Failed to infer universe levels in type of
binder `I`"* — the stage-0e hard error the amendment repaired.

DEPENDS: E.10–E.12 (the arena), **E.14** (`RungInterface.SepSide`, the trigger's mixed-side
half), **E.39a** (`BlockSuite`, the conclusion) · E.17 conceptually (the continuation trichotomy
that classifies *given* the blocks this obligation would supply).

SOURCE: `EFF.T2.18` (boxed `(LB1)`, the enumeration sentence, and the scoping paragraph:
*"Two level-one routes remain conditional, each where it is taken: the clause-4 route on `(LB1)`,
and the clause-5 peel at a recentered key on `(MP1)` … No level-one route is asserted
unconditional simpliciter"*); `EFF.T2.17` (the S1.7A displays the blocks must satisfy);
ledger Display A (the `(LB1)` conjunct); blueprint amendment **A-E.2** (the re-sign) and
**A-E.1/E-D6** (the universe repair).

TEETH: S7 mixed-residual and multi-side hostile cases → **signed non-applicability at level one**
(the corpus's own disposition — the obligation is OPEN and this node states it rather than
discharging it). The trigger is what makes that disposition checkable: a consumer that fires at a
one-side separable state gets nothing from this carrier.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, axiom-free. Definitional node: `LB1Carrier` reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Transcribed declaration-for-declaration against the
signed A-E.2 SIGNATURE (`leanspec/Leanspec/ChapE.lean` §6): binders, trigger and conclusion
unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- E.12's three universes, bound explicitly (A-E.1/E-D6): `uW` occurs only inside
-- `RungInterface`'s body, so this `Prop`'s `∀ I` binder must name it.
universe uO uK uW

/-- `(LB1)` (`EFF.T2.18`): the level-one clause-4 block suite exists — at the FULL S1.7A record
(`BlockSuite`, E.39a) [RE-SIGNED at A-E.2]. OPEN — a named capstone hypothesis; no chapter-E node
proves it. The as-committed conclusion (product identity + degree sum only) was machine-refuted
as a carrier (OM-4 FINDING 0, singleton self-block); it is archived in
`verification/om4_shadow_vacuity.lean` and VOID for chapter-I consumption. -/
def LB1Carrier {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ I : RungInterface.{uO, uK, uW} C B,
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (BlockSuite I)

/-! ## Gate (executed `example`s, not blueprint declarations)

**(a) The trigger is a real gate, not decoration.** At a one-side state whose every side is
separable — `EFF.T2.18`'s clause-1/2 perimeter, the states E.41 reads with no block hypothesis —
the trigger is FALSE, so `LB1Carrier` says nothing there. Machine-checked below rather than
asserted in prose; had the trigger been transcribed with `∧` for `∨`, or with the separability
polarity flipped, this example would fail.

**(b) The carrier is consumable in the shape chapter I needs.** Given the carrier and a state
that DOES trigger, a consumer extracts the suite. This is the Display-A consumption pattern, with
`uW` bound — the E-D6 universe defect would surface here. -/

section Gate

-- (a) a one-side separable state does not trigger `(LB1)`.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) (hone : I.sides.card = 1)
    (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ¬ (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) := by
  rintro (hcard | ⟨p, hp, hnp⟩)
  · omega
  · exact hnp (hsep p hp)

-- (b) the consumption pattern: at a multi-side state the carrier yields the suite.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (h : LB1Carrier.{uO, uK, uW} C B) (I : RungInterface.{uO, uK, uW} C B)
    (hmulti : 1 < I.sides.card) : Nonempty (BlockSuite I) :=
  h I (Or.inl hmulti)

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node: one `def`, printed. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LB1Carrier

end AxCheck
