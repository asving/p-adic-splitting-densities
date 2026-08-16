/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E12

/-!
# Uniformity.ChapE.E40 — `(MP1)`: the recentered-key mid-peel obligation, RE-SIGNED at A-E.2

**Chapter E, NODE E.40** [def] (`blueprint/CHAP-E_sigma_ladder.md` §6, **as RE-SIGNED by
amendment A-E.2, 2026-08-16**, and universe-repaired by A-E.1/E-D6), ENV-E2 (the carrier arena:
the bundle `O`, the label field `K`, a slot carrier `C : SlotCarrier O K` from E.10 and blocks
`B B' : BlockData C` from E.11; the interface is E.12's `RungInterface`).

`(MP1)` (`EFF.T2.23`) is the level-one **recentered-key** mid-chain-peel input suite: at every
level-one state whose current key is a RECENTERED key `Φ″ = Φ − Λ` dividing its represented
block, the quotient `G′` is a σ-block over the same carrier developed at the peeled key, with
`(MID-PEEL)`, the `(MID-MASS)` degree law, the S1.7 test data and the inherited frame, AND the
peeled key admits a certified orbit/`(e,f)` decomposition. That is `EFF.T2.23`'s **items 2–5**,
landed here as the record `MidPeelEmission` and quantified by the carrier `MP1Carrier`.

**This node PROVES nothing.** Both declarations are definitional: `MP1Carrier` is a named OPEN
capstone hypothesis, one of Display A's two conjuncts (the other is `(LB1)` = E.39), carried to
chapter I. The ORIGINAL-key peel is NOT this obligation (it is supplied by
HE6-PEEL-CONVENTION, a chapter-C row at E.22); the LEVEL-TWO analogue is discharged at E.42
(S1.8B). E.18 (`midPeel`) supplies the peel IDENTITY layer only and states none of items 2–5.

## ⚠ RE-SIGN (A-E.2) — the committed shadow was MACHINE-REFUTED VACUOUS

The as-committed E.40 conclusion,

    Nonempty (RungInterface.{uO, uK, uW} C B') ∧ ∃ e f : ℕ, e * f = C.D ∧ C.eC ∣ e ∧ C.fC ∣ f

was provable **for every carrier and block, from nothing** (OM-4 FINDING 0,
`docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3; machine witness
`verification/om4_shadow_vacuity.lean`, archived there under `OM4Shadow.MP1CarrierVoided`): the
interface conjunct by a fabricated one-side numerical-shadow interface (`mkTrivialInterface` —
nothing in E.12 ties the interface numbers to the polynomials), and the `(e,f)` conjunct by the
carrier's own pair through `C.hef`. A trivially true hypothesis tracks no conditionality, so the
committed form was strictly NARROWER than source. Amendment **A-E.2** re-signs the conclusion at
the full items-2–5 record; **names, parameter lists and the trigger hypotheses are
byte-preserved**, only the conclusion is strengthened. The vacuity of the `(e,f)` leg is mirrored
as gate (c) below, so the reason for the re-sign is machine-visible in this file. The pre-A-E.2
shadow is NAMED-AND-VOIDED: any consumer or discharge citing it is a defect.

Non-triviality of the re-signed form is certified in
`verification/om4_resign_nontriviality.lean` (`mp1_resigned_not_trivial : ¬ MP1Carrier C₂ B₂` —
key `X²`, `F = X⁴ − 5X² + 4`, legal recentering `Λ = 4`: the peeled key `X² − 4` is reducible
over `Frac(ℤ)`, so `hirr` is unsatisfiable and the fabricated-interface witness fails exactly
that field).

## What each field carries (`EFF.T2.23`'s enumeration, item by item)

* **item 2** — `(WINDOW)`/`(MID-PEEL)`/`(MID-MASS)`: `quot` (the quotient `G′` is a σ-block over
  the SAME carrier, enforced by TYPE), `hkey` (developed AT the peeled key), `hpeel`
  (`G = Φ̃ · G′`), `hmass` (`deg G′ = D(ν−1)`, cleared into `ℕ` as `deg G′ + D = deg G`);
* **items 3–4** — the full development with `(ACCOUNT)`, the S1.7 test assertions, and the
  occupied-height/lift/frame/origin/residual-degree data: `quot.hdev` (by TYPE) + `iface` (E.12's
  numerical-shadow record) + `hthr` (frame stability, `EFF.T2.61` (i)–(v): *"nothing about them
  moves when the key does"*). Honest residue, disclosed: `iface` lives in the numerical shadow
  and is instance-discharged via the RELATIVE S1.8C transport (`EFF.T2.61`; OM-4 §3.2);
* **item 5, THE OPEN CLAUSE** — `hirr`: `Φ″` irreducible over the base's fraction field, the
  hypothesis `EFF.T2.61` records as *"asserted nowhere, and the stated reason r4 declined
  HE6-PEEL-CONVENTION for that case"* (`EFF.T2.33`: *"a recentered `Φ″` does not inherit it"*);
  plus `hef`, the emission surface. Item 5 is dischargeable at instances only by the queued
  gate-(b) cite `recentered_key_emission` ([GN15] Thm 2.3 + eq (2.1); GMN Thm 2.11 — CHAP-I dated
  addendum 2026-08-16 (OM-4)) or a discharge node. **Nothing here consumes that cite**; this node
  is Lean-core.

## ⚠ `hef` ADDS NO STRENGTH — it is a read-off surface (gate (b))

`hef : B'.Φ.natDegree = C.eC * C.fC` is *derivable* from `B'.hΦdeg` and `C.hef` (`(DEG-EF)`), as
gate (b) below proves in one line; it is carried as a field only so that chapter I reads the
single orbit's pair off the record. No `FactorizationType` emission is imposed at the abstract
carrier — **GC-3's fence**: the dictionary `(e,f)` is never the ideal-theoretic pair, and
`typeOf` needs a DVR, which the schema's bare `CommRing O` does not carry. The `typeOf`-level
emission is exactly the queued cite's conclusion, consumed at instance rows.

## ⚠ UNIVERSE SCOPE, DECLARED (A-E.1/E-D6; honesty E-12)

`MidPeelEmission` carries a `RungInterface.{uO, uK, uW}` field, so `MP1Carrier.{uO, uK, uW}` is
the `EFF.T2.23` obligation **for the interfaces whose rank carrier `W` lives in universe `uW`** —
Lean cannot quantify over universes inside a `Prop`. This is a scoping fact, not a strength
change: at every instantiation the consumer chooses `uW`, and the obligation is exactly
`EFF.T2.23`'s at that choice. Chapter I must consume the carrier universe-polymorphically, or
record the one `uW` its instance uses. The explicit `universe uO uK uW` + the explicit
`RungInterface.{uO, uK, uW}` spelling is mandatory here, not stylistic: without it Lean reports
*"Failed to infer universe levels in type of binder"* / *"declaration `MP1Carrier` contains
universe level metavariables"* (the stage-0e hard error the amendment repaired).

## `(NO-IRR)`, and the one place irreducibility DOES appear

The `(NO-IRR)` fence (`EFF.T2.02` boxed REDLINE, `EFF.T2.43`/`.44`) forbids an irreducibility
hypothesis on the current key: `BlockData` has none, and none is added. `hirr` is not a breach —
it is an irreducibility assertion about the **peeled** key `B'.Φ`, stated as the record's own
OPEN clause (what `(MP1)` owes), never assumed of `B.Φ` and never available to any other node.

DEPENDS: E.10 (`SlotCarrier`, `D`/`eC`/`fC`/`hef`), E.11 (`BlockData`, `Φ`/`F`/`T`/`hΦdeg`),
E.12 (`RungInterface`, and the three-universe convention) · E.18 conceptually (the peel identity
layer this suite sits on; nothing is imported from it) · mathlib `Polynomial.map`,
`FractionRing`, `Irreducible`.

SOURCE: `EFF.T2.23` (boxed `(MP1)` + the quoted suite enumeration; the derivation's closing:
*"No pin proves the recentered level-one key's orbit/(e,f) item, so `(MP1)` remains open"*);
`EFF.T2.61` (what the S1.8C discharge does NOT give: *"It does not touch `(MP1)`. Peeling a
recentered level-one key still needs item 5 …"*; the frame clauses (i)–(v)); `EFF.T2.33`
(a recentered `Φ″` does not inherit irreducibility); ledger Display A (the `(MP1)` conjunct);
blueprint amendment **A-E.2** (the re-sign) and **A-E.1/E-D6** (the universe repair).

TEETH: S7 reducible/recentered-key boundary attacks → **signed non-applicability** (the corpus's
own disposition: the obligation is OPEN, and this node states it rather than discharging it).
The vacuity attack that killed the committed form is closed at the record level and mirrored as
gate (c).

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, axiom-free. Definitional node: every declaration reports at most the Lean-core
triple `{propext, Classical.choice, Quot.sound}`. Types checked field by field against the
signed A-E.2 SIGNATURE in `leanspec/Leanspec/ChapE.lean` §6 (field names, field order and every
field's statement unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- E.12's three universes, bound explicitly (A-E.1/E-D6): `uW` occurs only inside
-- `RungInterface`'s body, so a `Prop` quantifying over an interface must name it.
universe uO uK uW

/-- **The `(MID-PEEL)` input suite at a recentered level-one key** — items 2–5 of
`EFF.T2.23`'s enumeration, as a record over the parent block `B` and the recentered-key block
`B'` [signed at A-E.2]:

* item 2, `(WINDOW)`/`(MID-MASS)`: the quotient `G′` exists as a σ-block over the SAME carrier
  (`quot`), developed AT the peeled key (`hkey`), with the peel identity (`hpeel`), the degree
  law (`hmass`) and the inherited threshold (`hthr` — the frame does not move, S1.8C =
  `EFF.T2.61` (i)–(v));
* items 3–4, development/`(ACCOUNT)`/S1.7 test data + occupied-height, lift, frame, origin,
  residual-degree data: `quot`'s own `hdev` (by TYPE) + `iface` (the numerical-shadow record;
  REDUCES-TO the S1.8C transport at instances, RELATIVE — OM-4 §3.2);
* item 5, **THE OPEN CLAUSE** (`hirr` + `hef`): the peeled recentered key's certified
  orbit/`(e,f)` decomposition — `Φ″` irreducible ("asserted nowhere", `EFF.T2.61`), the single
  orbit carrying the frame's own pair. Dischargeable at instances only by the queued gate-(b)
  cite `recentered_key_emission` ([GN15] Thm 2.3 + eq (2.1); GMN Thm 2.11) or a discharge node.
  `hef` is the emission surface (derivable from `hΦdeg` + `C.hef`; carried so chapter I reads
  the pair off the record — the dictionary `(e,f)`, GC-3 fenced, never the ideal-theoretic
  pair). -/
structure MidPeelEmission {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} (B B' : BlockData C) where
  quot : BlockData C
  hkey : quot.Φ = B'.Φ                              -- the development is AT the peeled key
  hpeel : B.F = B'.Φ * quot.F                       -- (MID-PEEL)
  hmass : quot.F.natDegree + C.D = B.F.natDegree    -- (MID-MASS), degree law
  hthr : quot.T = B.T                               -- frame/origin: the frame does not move
  iface : RungInterface.{uO, uK, uW} C quot         -- items 3–4, numerical shadow
  /-- item 5, the cite-consuming clause: `Φ″` irreducible over the base's fraction field. -/
  hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O)))
  /-- item 5, the emission surface: the single orbit's `(e,f)` accounts for the full peeled
  degree at the carrier's `(DEG-EF)` data. -/
  hef : B'.Φ.natDegree = C.eC * C.fC

/-- `(MP1)` (`EFF.T2.23`): the level-one mid-chain-peel input suite at a RECENTERED key — at the
FULL items-2–5 record (`MidPeelEmission`) [RE-SIGNED at A-E.2]. OPEN — a named capstone
hypothesis; carried to chapter I. The as-committed conclusion (`Nonempty (RungInterface C B')` +
a divisibility-only `(e,f)` clause) was machine-refuted as a carrier (OM-4 FINDING 0, fabricated
interface); it is archived in `verification/om4_shadow_vacuity.lean` and VOID for chapter-I
consumption. -/
def MP1Carrier {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ (Λ : Polynomial O),                        -- the recentering increment
    Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ (B' : BlockData C),                      -- the block carrying the key Φ − Λ
      B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      Nonempty (MidPeelEmission.{uO, uK, uW} B B')

/-! ## Gate (executed `example`s, not blueprint declarations)

Three things this definitional node can get wrong silently, checked here rather than asserted.

**(a) The E-D6 quantifier pattern elaborates for the CARRIER itself.** `MP1Carrier` quantifies
over a `RungInterface` twice over (once inside `MidPeelEmission`, once through the outer `∀`);
the universe defect A-E.1 fired on is invisible at the structure and appears only at a `Prop`
that binds the carrier. The gate reproduces exactly a consumer's shape (chapter I's Display-A
field), so a regression in the universe plumbing fails HERE.

**(b) `hef` is a read-off surface, not extra strength.** `B'.hΦdeg` (`deg Φ = D`) and `C.hef`
(`(DEG-EF)`: `D = e_𝒞 f_𝒞`) already give the field's statement for EVERY block, so carrying it
cannot make the obligation harder than `EFF.T2.23`'s. Had `hef` been signed at a genuinely
stronger emission (an ideal-theoretic pair, or a `typeOf` value), this example would fail —
which is the GC-3 fence made machine-visible.

**(c) The VOIDED shadow's `(e,f)` clause, mirrored.** OM-4 FINDING 0's second leg, in one line:
the committed conclusion's `∃ e f, e * f = C.D ∧ C.eC ∣ e ∧ C.fC ∣ f` is provable from the
carrier alone, for every carrier — no block, no key, no recentering. That is why A-E.2 voided
it, and it is the standing lower bound on any future re-signing: a proposal to weaken this
carrier must first show the fabricated witnesses fail the weakened form. -/

section Gate

-- (a) the E-D6 pattern at the carrier: a `Prop` quantifying over `MP1Carrier`, `uW` bound.
example : Prop :=
  ∀ {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K) (B : BlockData C),
    MP1Carrier.{uO, uK, uW} C B

-- (b) `hef`'s statement is derivable for every block from `hΦdeg` + `(DEG-EF)`.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    (B' : BlockData C) : B'.Φ.natDegree = C.eC * C.fC :=
  B'.hΦdeg.trans C.hef

-- (c) the voided shadow's `(e,f)` conjunct: true of every carrier, from `C.hef` alone.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K) :
    ∃ e f : ℕ, e * f = C.D ∧ C.eC ∣ e ∧ C.fC ∣ f :=
  ⟨C.eC, C.fC, C.hef.symm, dvd_rfl, dvd_rfl⟩

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node. The structure former asserts nothing about its fields, so the fields carrying
the suite's content — the peel identity, the degree law, the frame, the interface, and item 5's
two clauses — are printed one by one alongside the type former, its constructor and the
carrier. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.MidPeelEmission
#print axioms Uniformity.Density.Ladder.MidPeelEmission.mk
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hkey
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hpeel
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hmass
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hthr
#print axioms Uniformity.Density.Ladder.MidPeelEmission.iface
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hirr
#print axioms Uniformity.Density.Ladder.MidPeelEmission.hef
#print axioms Uniformity.Density.Ladder.MP1Carrier

end AxCheck
