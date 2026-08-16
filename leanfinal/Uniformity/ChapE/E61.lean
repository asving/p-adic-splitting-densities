/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D63

/-!
# Uniformity.ChapE.E61 — `VarthetaRes`, the level-`i` `(H-VARTHETA-RES)_i` socket, TYPED

**Chapter E, NODE E.61** [def] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §9 — the
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers). ENV-E1 (plus chapter D's arena, imported).

This node is one of the chapter's four BLOCKED-UNTIL-RESOLUTION sockets (§12: E.51, E.57,
E.61, E.62), signed in the blueprint with a `supplied : True` placeholder and the standing
instruction that the field is TYPED at the orchestrator's GC-13/GC-14 resolution pass.
**That pass is executed here**, against the LANDED chapter-D carriers (chapter D complete,
2026-08-16): the socket's single field is chapter D's re-signed sitewise carrier
`Uniformity.Density.Gauge.HVarthetaRes` (`ChapD/D62.lean`), instantiated at the level-`i`
data.

## What the socket says

For a tower whose level-`j` height data is `(N, v j)`, whose level-`j` **ambient residue
datum** is `ρ j : ker (v j) →* Lˣ` (`L` the ambient residue field, `K` the level field
embedded in it), and whose level-`j` fixed use-height is `q j` (the corpus's `u_{j+1}`),

```
VarthetaRes G K L N v ρ q i   ↔   HVarthetaRes G K L N (v i) (ρ i) (q i)
```

i.e. `∀ s, ∃ (h : N.varthetaEl (q i) s ∈ ker (v i)) (u : Kˣ), ρ i ⟨_, h⟩ = algebraMap K L u`
— `EFF.T1.09`'s R9-2 display verbatim at level `i`: every ϑ-quotient
`n̂_i(u_{i+1})^s / n̂_i(s·u_{i+1})` has value zero and its ambient residue is (the image of) a
`K_i`-unit. The `Iff` above is machine-checked below, so the binding is a term, not a comment.

## ⚠ THE A-D.2 CONSUMPTION FENCE — why the socket is typed THIS way and no other

CHAP-I's NODE I.10 dated note (2026-08-16, the Display-A carrier adjudication) rules, item 2:
the `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` conjunct (ledger rows HYP.57/HYP.63) is consumed at the
**A-D.2 form only**, and *"when E.61's BLOCKED socket (`VarthetaRes i`, `supplied : True`) is
typed at the GC-13/GC-14 resolution, it must be typed against the A-D.2 sitewise carrier with
chapter C's/D's level-`i` instantiation data — typing it against the voided form (or leaving
an untyped `True`) would reintroduce a vacuous Display-A conjunct"*. Both failure modes are
excluded here:

* the pre-A-D.2 existential form `HVarthetaResVoided G K N v := ∃ A : GaugeArena G K N, A.v = v`
  was machine-REFUTED as a carrier (defect D-D12: inhabited by the trivial hom, provably
  equivalent to the exact-height fact). It is NOT in scope anywhere in `leanfinal` — the
  refutation record stays at `leanspec/Leanspec/ChapD.lean` §9 (named-and-voided) with
  `verification/om4_shadow_vacuity.lean` — so this socket cannot bind it even by accident;
* the `True` placeholder is gone: the field now carries chapter D's display.

Non-fabricability is chapter D's, inherited by the binding: with `ρ` GIVEN, the trivial-hom
trick dies, and the carrier is machine-certified FALSE at a concrete instance
(`verification/om4_resign_nontriviality.lean`: the ϑ-residue at `s = 2` is `−i ∉ image(ℚˣ)`)
and FALSE at REAL tower exponents under an adversarial `ρ` (`verification/om8_vartheta_deep.py`
LEG D2). So the socket tracks genuine conditionality: **nothing in this chapter discharges it**,
and (per the Part V owner ruling) its terminal disposition is chapter I's — DISCHARGE NODE or
LITERATURE CITE.

## The signature delta against the committed stub (honest record)

Committed stub (`leanspec/Leanspec/ChapE.lean` §9): `structure VarthetaRes (i : ℕ) : Prop`
with `supplied : True`, under a `-- BLOCKED: GC-13 resolution` header and the A-D.2 fence
comment. What the blueprint FROZE about it is the NAME, the INDEX, the single field's name,
and the consumption route (chapter I's Display-A block consumes `∀ i ≥ 3, VarthetaRes i`
through E.24's `LadderSupply`); the field's TYPE was explicitly left open. Landed here:

* name `VarthetaRes`, field name `supplied`, index `i : ℕ` as the LAST explicit argument — all
  as committed;
* **added**: the level-indexed instantiation data `(N, v, ρ, q)` as explicit parameters, in
  D.62's own spelling and argument order (`G`, `K`, `L` explicit, as `HVarthetaRes` has them).
  They are parameters and not existentially bundled fields ON PURPOSE: an `∃ data` wrapper is
  precisely the fabricable shape that D-D12 refuted.

**Consumer obligation created (flagged for the orchestrator, not patched here):** E.24's
`LadderSupply.vartheta : ∀ i ≥ 3, VarthetaRes i` and E.63's
`DeepTwistConjunct := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i` must thread the same level data
when they land; neither is landed in this tree yet, so no landed signature moves today. I.10's
`ladder` field consumes the carriers only THROUGH E.24, so chapter I is unaffected until E.24
lands.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (parent CLAUDE.md trust boundary; one definition).
Three recasts to check on the chapter cross-read:

* *the level data is a FAMILY, the carrier is per-rung.* `v ρ q : ℕ → …` supply every level's
  height map, ambient residue datum and use-height; the socket reads only index `i`. This
  matches D.62's `q`-is-a-parameter scope ("the level's fixed use-height") and D.63's fence
  that the HVR leg is per-rung while the `𝒲` leg is cumulative inside `Wle` — flattening
  either into the other is the conflation `EFF.T5.10` forbids.
* *one ambient field `L` for the whole ladder.* The family `ρ` lands all levels' residues in a
  single ambient `Lˣ` with a single `[Algebra K L]`; the corpus reads the level-`i` residues
  inside the ambient residue field of the tower, so this is the intended reading, but it IS a
  choice made here (a per-level `L i` would be the weaker, unusable-by-`Wle` alternative).
* *no `i ≥ 3` bound is built in.* Display A quantifies `∀ i ≥ 3` at the consumer (E.24 → I.10);
  the socket is total in `i`, exactly as D.63's conjunct is.

**⚠ ORIENTATION (GC-14).** The ϑ orientation is chapter D's canonical table, cited by anchor
(`EFF.GENTOW2 orientation records [supplied-by: chapter D, the GC-14 table]`); no content of
that table is restated here, and this node adjudicates nothing about it (honesty E-5).

**DEPENDS.** D.62 (`HVarthetaRes`, the A-D.2 re-signed form) and D.63 (`VarthetaWConjunct`,
the conjunct the socket plugs into) — both imported, so both bindings are checked terms.
E.33 (the exponent engine `coc`/`theta_telescope`) is the CONTENT of the ϑ-monomials whose
residues the carrier names; it is cited, not imported — the socket names D's display and
computes nothing.

**SOURCE.** `EFF.HE7.110` (R1-b's `ϑ_t` and its closing compatibility sentence);
`EFF.HE7.108`(iii) (the fixed letter-monomial residue, "depending on `(k,t)` and the
s-bookkeeping only, NOT on `C` or `ξ`"); `EFF.HE7.112` (the composite twist unit);
`EFF.T1.09` (the R9-2 fence and the displayed hypothesis, via D.62); ledger Display A (the
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` `∀ i ≥ 3` conjunct, rows HYP.57/HYP.63 — status CARRY);
GC-14 (the orientation table's ownership); CHAP-D DECISION D-2 + AMENDMENT A-D.2; CHAP-I
NODE I.10's dated note (the consumption rule).

**TEETH.** none, by design — `he7rannex_supp.py`'s disclosure (ii) (`ϑ_t, t ≥ 1` machine-
invisible at the level-3 family) is WHY this is a carried conjunct and not a discharged one.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only). Nothing is discharged: this file contains no theorem
concluding `VarthetaRes …` at any level.
-/

namespace Uniformity.Density.Ladder

open Uniformity.Density.Gauge

/-- **NODE E.61** — `(H-VARTHETA-RES)_i` (Display A, `∀ i ≥ 3`): the level-`i` deep-twist units
are the letter-monomial residues, read in the ambient residue field through the GIVEN level-`i`
ambient residue datum `ρ i`, and correctly oriented per chapter D's canonical ϑ table
[GC-14 anchor: `EFF.GENTOW2` orientation records, supplied-by chapter D].

**TYPED AT THE GC-13/GC-14 RESOLUTION** against the landed A-D.2 carrier: the field is
`HVarthetaRes` (D.62) at the level-`i` height data `(N, v i)`, ambient residue datum `ρ i` and
use-height `q i`. **Fence (A-D.2 / I.10 item 2):** the pre-A-D.2 existential form
`HVarthetaResVoided` is machine-refuted (D-D12) and is not in scope in `leanfinal`; a socket
left at `supplied : True`, or bound to that form, would be a vacuous Display-A conjunct. A
CARRIER — chapter E discharges nothing; terminal disposition is chapter I's. -/
structure VarthetaRes (G : Type*) [CommGroup G] (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (i : ℕ) : Prop where
  supplied : HVarthetaRes G K L N (v i) (ρ i) (q i)

/-- The binding, as a unit test rather than a comment: the socket at level `i` IS chapter D's
sitewise `(H-VARTHETA-RES)_i` at the level-`i` data (D.62, A-D.2 form). Nothing is discharged —
this is a shape statement at arbitrary supplied data. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {i : ℕ} :
    VarthetaRes G K L N v ρ q i ↔ HVarthetaRes G K L N (v i) (ρ i) (q i) :=
  ⟨fun h => h.supplied, fun h => ⟨h⟩⟩

/-- The consumption route, as a unit test: the socket family is a legal `HVR` slot of D.63's
`VarthetaWConjunct`, and plugged there it delivers exactly the A-D.2 sitewise leg alongside the
cumulative `𝒲` leg — `(H-VARTHETA-RES)_i ∧ ⋀_{3≤j≤i} W j`. This is the shape chapter I's
Display-A block consumes (through E.24); it asserts neither leg. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} (W : ℕ → Prop) (i : ℕ) :
    VarthetaWConjunct (fun j => VarthetaRes G K L N v ρ q j) W i ↔
      HVarthetaRes G K L N (v i) (ρ i) (q i) ∧ ∀ j, 3 ≤ j → j ≤ i → W j :=
  ⟨fun h => ⟨h.1.supplied, h.2⟩, fun h => ⟨⟨h.1⟩, h.2⟩⟩

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.VarthetaRes

end AxCheck
