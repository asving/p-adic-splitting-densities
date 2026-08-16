/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E39
import Uniformity.ChapE.E40
import Uniformity.ChapE.E61

/-!
# Uniformity.ChapE.E24 — `HE7APackage` and `LadderSupply`: what chapter I receives

**Chapter E, NODE E.24** [def] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §4, PLACED after §6/§9
per the §12 re-order — it forward-references the obligation carriers and the indexed carriers).
ENV-E2. Universe-repaired by A-E.1/E-D6; the `lb1`/`mp1` fields bind the A-E.2 RE-SIGNED
carriers; the `vartheta` field binds the A-D.2 sitewise carrier through E.61's typed socket.

Two declarations, no proof obligation:

* `HE7APackage C B` — Display A's `HE7A[ACCOUNT, RES-DEG, nonempty, exhaust,
  root-continuation]` conjunct. The five clause families ARE the fields of E.12's
  `RungInterface` (`EFF.T2.39`'s five-family fence: the field list IS the fence), so the
  package is exactly the statement *"a rung interface exists for the block"*.
* `LadderSupply …` — the full chapter-E supply: the package, plus the two §6 obligation
  carriers `(LB1)`/`(MP1)`, plus §9's indexed deep-twist carrier at every `i ≥ 3`.

## ⚠ THE `vartheta` FIELD'S DATA THREADING — the one signature decision this node makes

The committed stub signs the last field as `vartheta : ∀ i ≥ 3, VarthetaRes i`, written when
E.61's socket was still the BLOCKED `structure VarthetaRes (i : ℕ) : Prop where supplied : True`.
E.61 was TYPED at the GC-13/GC-14 resolution (landed 2026-08-16) against chapter D's A-D.2
sitewise carrier, and its landed form carries the level-indexed instantiation data explicitly:

```
VarthetaRes G K L N v ρ q i   ↔   HVarthetaRes G K L N (v i) (ρ i) (q i)
```

E.61's own file records the resulting **consumer obligation** verbatim: *"E.24's
`LadderSupply.vartheta : ∀ i ≥ 3, VarthetaRes i` … must thread the same level data when they
land."* **That obligation is discharged here, by threading — the level data `(G, K_t, L, N, v, ρ,
q)` becomes a parameter block of `LadderSupply`.** The three alternatives were considered and
rejected, each for a recorded reason:

1. *quantify over the data inside the field* (`∀ {G} … ∀ i ≥ 3, VarthetaRes …`) — this asserts
   the carrier at an ARBITRARY ambient residue datum `ρ`, and the ρ-defeat is machine-shown at
   REAL tower exponents (`verification/om8_vartheta_deep.py` LEG D2; CHAP-I I.10's ARC NOTE:
   *"typing E.61's socket at anything but chapter C's canonical residue data leaves the conjunct
   undischargeable"*). A hypothesis nobody can ever discharge is a vacuous capstone, in the
   opposite direction from D-D12;
2. *bundle the data existentially* (`∃ data, ∀ i ≥ 3, …`) — precisely the fabricable shape
   defect D-D12 refuted (the trivial hom satisfies it), and precisely what E.61 and E.62 both
   refused;
3. *drop the field* — deletes a Display-A conjunct from the public conditionality. Not a
   spelling change; an owner-gate event in the wrong direction.

**Consumer obligation created (flagged, not patched here).** CHAP-I's I.10 signs its `ladder`
field as `∀ (O) [CommRing O] (K) [Field K] (C) (B), Ladder.LadderSupply C B`. When I.10 lands it
must also bind (or quantify over) the tower data block — the same choice E.61 forced here. I.10
is NOT landed in this tree, so no landed signature moves today. Nothing about the FIELD LIST
changes: the four field names `package`, `lb1`, `mp1`, `vartheta` and their order are the
blueprint's, unchanged, and gate (d) below proves the record is exactly their conjunction (so a
fifth field cannot be smuggled in later without that gate failing).

## ⚠ THE UNIVERSE PARAMETERS — what chapter I must spell

`HE7APackage.{uO, uK, uW}` is unchanged: `uW` is the universe of `RungInterface`'s `(SEC-RANK)`
rank carrier `W`, it occurs ONLY inside the `Prop`, and it is therefore NOT inferable from
`(C, B)` — A-E.1/E-D6's ruling, honesty item **E-12**. `LadderSupply.{uO, uK, uW, uG, uKt, uL}`
appends three MORE, for the threaded tower data — but those three are inferable, because `G`,
`K_t` and `L` are explicit arguments. So the E-12 disclosure is unchanged in substance: exactly
one universe (`uW`) is uninferable, and chapter I must either carry the conjunct
universe-polymorphically in it (preferred) or record its chosen `uW` as a declared scope.
**Not acceptable** (blueprint, verbatim): letting Lean pick silently, or collapsing `W := ℕ`
— `EFF.T2.52` licenses an instance to discharge `(SEC-RANK)` either way, so an `ℕ`-valued rank
carrier is a strength change. Gate (a) exhibits the consumption pattern with all six spelled.

## ⚠ WHAT THE CARRIERS MEAN — the I.10 consumption rule, honoured structurally

* `lb1` is E.39's **A-E.2 re-signed** `LB1Carrier` (concluding `Nonempty (BlockSuite I)`, the full
  S1.7A record), `mp1` is E.40's **A-E.2 re-signed** `MP1Carrier` (concluding
  `Nonempty (MidPeelEmission B B')`, `EFF.T2.23` items 2–5). The as-committed shadows were
  machine-refuted trivially inhabitable (OM-4 FINDING 0) and are NAMED-AND-VOIDED in
  `verification/om4_shadow_vacuity.lean`; they are not in scope in `leanfinal`, so this record
  cannot bind them even by accident.
* `vartheta` reaches chapter D's A-D.2 sitewise `HVarthetaRes` through E.61 — the voided
  existential `HVarthetaResVoided` is likewise out of scope here.
* Gates (b)/(c) EXTRACT each conjunct at its re-signed strength, so "the record delivers what
  chapter I is promised" is a term rather than a comment.

**This node discharges nothing.** `HE7APackage` is a hypothesis; `(LB1)`, `(MP1)` and
`(H-VARTHETA-RES)_i` are open (ledger rows HYP.41/42/57, status CARRY); no theorem below
concludes any of them.

**DEPENDS.** E.12 (`RungInterface`), E.39 (`LB1Carrier`), E.40 (`MP1Carrier`), E.61
(`VarthetaRes`, and through it chapter D's `HVarthetaRes`) — all imported, so every binding is a
checked term. E.62's `WFrame` is deliberately NOT a field: the blueprint's field list conjoins
the `𝒲` leg **at chapter I** ("E.61 (with E.62's 𝒲 conjunct at I)").

**SOURCE.** `EFF.T2.39` (the five-family fence — the field list IS the fence);
`spec/HYPOTHESIS_LEDGER.md` Display A (the `HE7A[…]` conjunct plus the `(LB1)`, `(MP1)`,
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` conjuncts); BRIEF E product clauses (1), (2), (4); CHAP-E
AMENDMENTS A-E.1 (E-D6, universes) and A-E.2 (the re-signed carriers); CHAP-D DECISION D-2 +
AMENDMENT A-D.2; CHAP-I NODE I.10's dated note of 2026-08-16 (the consumption rule).

**TEETH.** none (packaging); chapter I's gates re-fire the `n ≤ 2` slices against it.

**ENVIRONMENT.** ENV-E2.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Ladder

open Uniformity.Density.Gauge

-- E.12's three universes (A-E.1/E-D6: `uW` occurs only inside the `Prop`, so every declaration
-- quantifying over a `RungInterface` must bind it), plus three for E.61's threaded tower data.
universe uO uK uW uG uKt uL

/-- **E.24** [def] Display A's `HE7A[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]`
conjunct: the σ-ladder carrier suite holds for the block — packaged for chapter I's hypothesis
structure. The five clause families are the FIELDS of `RungInterface` (E.12), so the package is
the statement that such an interface exists.

⚠ `uW` is NOT inferable from `(C, B)` (A-E.1/E-D6, honesty E-12): it is the universe of the
`(SEC-RANK)` rank carrier, which occurs only inside this `Prop`. Consume
universe-polymorphically, or record the chosen `uW`; never collapse `W := ℕ`. -/
def HE7APackage {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  Nonempty (RungInterface.{uO, uK, uW} C B)

/-- **E.24** [def] The full chapter-E supply to chapter I: the `HE7A[…]` package, plus the §6
obligation carriers `(LB1)`/`(MP1)`, plus §9's indexed deep-twist carrier at every `i ≥ 3`.

[A-E.2] `lb1`/`mp1` bind the RE-SIGNED carriers (`Nonempty (BlockSuite I)` /
`Nonempty (MidPeelEmission B B')`); the pre-A-E.2 shadows are machine-refuted and VOID for
consumption. [A-D.2 / I.10 item 2] `vartheta` binds E.61's TYPED socket, hence chapter D's
sitewise `HVarthetaRes` at the GIVEN ambient residue datum `ρ i` — the level data
`(G, K_t, L, N, v, ρ, q)` is threaded as parameters, per E.61's recorded consumer obligation;
quantifying over it (undischargeable at arbitrary `ρ`) or bundling it existentially (fabricable,
D-D12) are both excluded. E.62's `𝒲` leg is conjoined at chapter I, not here.

A CARRIER RECORD: every field is an OPEN hypothesis (ledger HYP.41/42/57, status CARRY) and
nothing in this chapter discharges any of them. -/
structure LadderSupply {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) : Prop where
  package : HE7APackage.{uO, uK, uW} C B
  lb1 : LB1Carrier.{uO, uK, uW} C B                     -- E.39 (A-E.2 re-signed form)
  mp1 : MP1Carrier.{uO, uK, uW} C B                     -- E.40 (A-E.2 re-signed form)
  vartheta : ∀ i ≥ 3, VarthetaRes G Kt L N v ρ q i      -- E.61 (A-D.2 form; 𝒲 conjoined at I)

/-! ## Gate (executed `example`s, not blueprint declarations)

Four checks, all of them things this node could get wrong silently.

(a) **The consumption pattern elaborates, with every universe spelled.** The A-E.1/E-D6 defect is
invisible at a declaration and appears only at a `Prop` that quantifies over instantiations —
which is exactly chapter I's `ladder` field. Reproducing that shape here means a universe
regression fails in E.24's own file.

(b), (c) **The record delivers the re-signed carriers.** Each of the three carried conjuncts is
extracted at the strength the I.10 dated note fixes: `Nonempty (BlockSuite I)` at a triggering
interface, `Nonempty (MidPeelEmission B B')` at a legal recentering, and chapter D's SITEWISE
`HVarthetaRes` at a level `i ≥ 3`. Had `vartheta` been bound to a `True` placeholder or to the
voided existential, (c) would not typecheck.

(d) **The record is EXACTLY the conjunction of its four fields.** The blueprint's field list is
the public conditionality; this gate fails the moment a fifth field appears or one is dropped —
E.44's precedent gate, applied to the bundle chapter I actually consumes. -/

section Gate

-- (a) the E-D6 consumption pattern, at chapter I's shape, with all six universes explicit.
example {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) : Prop :=
  ∀ (O : Type uO) [CommRing O] (K : Type uK) [Field K]
    (C : SlotCarrier O K) (B : BlockData C),
    LadderSupply.{uO, uK, uW, uG, uKt, uL} C B G Kt L N v ρ q

-- the `HE7APackage` binding, as a unit test rather than a comment.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K)
    (B : BlockData C) :
    HE7APackage.{uO, uK, uW} C B ↔ Nonempty (RungInterface.{uO, uK, uW} C B) :=
  Iff.rfl

-- (b) the two §6 carriers, extracted at their A-E.2 strengths.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL}
    [Field L] [Algebra Kt L] {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    (S : LadderSupply.{uO, uK, uW, uG, uKt, uL} C B G Kt L N v ρ q)
    (I : RungInterface.{uO, uK, uW} C B) (hmulti : 1 < I.sides.card) :
    Nonempty (BlockSuite I) :=
  S.lb1 I (Or.inl hmulti)

example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL}
    [Field L] [Algebra Kt L] {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    (S : LadderSupply.{uO, uK, uW, uG, uKt, uL} C B G Kt L N v ρ q)
    (Λ : Polynomial O) (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree < C.D) (B' : BlockData C)
    (hB' : B'.Φ = B.Φ - Λ) (hdvd : B'.Φ ∣ B.F) :
    Nonempty (MidPeelEmission.{uO, uK, uW} B B') :=
  S.mp1 Λ hΛ hdeg B' hB' hdvd

-- (c) the §9 carrier, extracted at chapter D's A-D.2 SITEWISE form (I.10 item 2). The `≥ 3`
-- bound lives at this consumer, exactly as Display A writes it; E.61's socket is total in `i`.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL}
    [Field L] [Algebra Kt L] {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    (S : LadderSupply.{uO, uK, uW, uG, uKt, uL} C B G Kt L N v ρ q) (i : ℕ) (hi : 3 ≤ i) :
    HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
  (S.vartheta i hi).supplied

-- (d) the record is exactly its four fields — no more, no fewer.
example {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL}
    [Field L] [Algebra Kt L] {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} :
    LadderSupply.{uO, uK, uW, uG, uKt, uL} C B G Kt L N v ρ q ↔
      (HE7APackage.{uO, uK, uW} C B ∧ LB1Carrier.{uO, uK, uW} C B ∧
        MP1Carrier.{uO, uK, uW} C B ∧ ∀ i ≥ 3, VarthetaRes G Kt L N v ρ q i) :=
  ⟨fun S => ⟨S.package, S.lb1, S.mp1, S.vartheta⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node: the `def`, the structure former, its constructor and all four fields. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.HE7APackage
#print axioms Uniformity.Density.Ladder.LadderSupply
#print axioms Uniformity.Density.Ladder.LadderSupply.mk
#print axioms Uniformity.Density.Ladder.LadderSupply.package
#print axioms Uniformity.Density.Ladder.LadderSupply.lb1
#print axioms Uniformity.Density.Ladder.LadderSupply.mp1
#print axioms Uniformity.Density.Ladder.LadderSupply.vartheta

end AxCheck
