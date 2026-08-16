/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D55
import Uniformity.ChapD.D62

/-!
# Uniformity.ChapD.D63 — `VarthetaWConjunct`, Display A's `∀ i ≥ 3` conjunct, assembled

**Chapter D, NODE D.63** [def] [fresh], *consumption* **RE-SIGNED at A-D.2 — signature
byte-unchanged* (`blueprint/CHAP-D_gauge_tchain.md` §9, amendment A-D.2 / DECISION D-2,
2026-08-16; amendments A-1 and A-D.1 also govern the chapter). ENV-D1. One signed declaration,
and it is a **CARRIER**.

*Display A's `∀ i ≥ 3` conjunct.* Over abstract rung-indexed families `HVR W : ℕ → Prop`,

```
VarthetaWConjunct HVR W i  :=  HVR i ∧ Wle W i        i.e.   (H-VARTHETA-RES)_i ∧ 𝒲_{≤i},
```

the name chapters E and I consume for the capstone conjunct at every `i ≥ 3`. The two families
are **two different conditional stacks on the same displays** (`EFF.T5.10`: the HVR fence is "a
SECOND conditional stack on the same displays and must not be conflated with `𝒲_{≤i}`"), which
is why the carrier is an explicit `∧` of two abstract families rather than one predicate.

The intended instantiation:

* `HVR i :=` **the A-D.2 sitewise `HVarthetaRes`** over the level-`i` height data `(N, v_i)`,
  the level-`i` **ambient residue datum** `ρ_i : ker v_i →* Lˣ`, and the level's fixed use-height
  `q_i = u_{i+1}` (D.62 as re-signed; instantiation data chapter C's);
* `W q := GentowW` at the level-`q` data (D.44), so `Wle W i = ⋀_{3≤q≤i}[GENTOW5-W(q)]` (D.55).

Both are exercised below as an `Iff.rfl` unit test, so the `ℕ → Prop` abstraction is checked
rather than asserted.

## ⚠ THE CONSUMPTION FENCE (A-D.2) — the reason this node was re-signed

`HVR` **must** be instantiated at the RE-SIGNED sitewise `HVarthetaRes`. The pre-A-D.2 carrier

```
HVarthetaResVoided G K N v := ∃ A : GaugeArena G K N, A.v = v          -- VOID
```

was machine-REFUTED (defect D-D12): the trivial hom `1 : ker v →* Kˣ` inhabits it, and
`hvarthetaResVoided_iff` proves it EQUIVALENT to the exact-height fact `∀ k, v (N.n k) = ofAdd k`.
Instantiated there, this very definition would have degenerated to *`Wle` plus height
bookkeeping* — chapter I would have carried a Display-A conjunct dischargeable by `⟨v, hv, 1⟩`.
**Any consumer or discharge instantiating `HVR` at `HVarthetaResVoided` is a defect.** The
blueprint's earlier parenthetical "(modulo D.62's disclosed delta)" is WITHDRAWN at A-D.2 — the
existential form had no delta to disclose, it was empty.

The refutation record stays machine-checked, but deliberately **not in this tree**: the voided
form and its two witnesses live at `leanspec/Leanspec/ChapD.lean` §9 (named-and-voided), with
`verification/om4_shadow_vacuity.lean` and the non-triviality countermodel
`verification/om4_resign_nontriviality.lean` (an exact-height instance — so the old trivializer
still fires against the VOIDED form there — whose ϑ-residue at `s = 2` is `−i ∉ image(ℚˣ)`, so
the re-signed carrier is FALSE at it and tracks genuine conditionality). D.62's landed file
states the same fence; this file imports the re-signed carrier and no other, which is the
strongest form the fence can take here: **the voided name is not in scope in `leanfinal` at
all**, so no consumer in this tree can instantiate it even by accident.

Standing refutation obligation (A-D.2): a proposal to weaken the `HVR` slot below the
sitewise-with-given-`ρ` form must first show the D-D12 witnesses fail against it — the vacuity
witnesses are the permanent lower bound on carrier strength.

## Terminal disposition — this chapter supplies the carrier, nothing else

Per the Part V owner ruling, the conjunct's terminal disposition in **chapter I** is
**DISCHARGE NODE or LITERATURE CITE**; chapter D supplies the carrier at exact ledger strength
and discharges neither leg. Concretely, in this tree there is:

* no theorem concluding `⊢ VarthetaWConjunct HVR W i` at any `i ≥ 3`, for any instantiation;
* no theorem concluding `⊢ Wle W i` at any `i ≥ 3` (D.55's non-discharge discipline,
  `EFF.T5.29`, ledger `HYP.63` CARRY);
* no theorem concluding `⊢ HVarthetaRes …` outright — D.62's only implication,
  `hvarthetaRes_of_arena_agree`, *consumes* an arena plus an ambient-agreement hypothesis
  (`hagree`), which is precisely the leg the voided existential form lacked.

The chapter-I consumption rule is recorded at I.10's Display-A block (dated note, 2026-08-16):
the `(H-VARTHETA-RES) ∧ 𝒲` conjunct is consumed at the A-D.2 form only.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one definition; parent CLAUDE.md trust boundary).
Three recasts against `EFF.T1.09` + `EFF.T3.22` + `EFF.T5.10/.13`, flagged for the chapter
cross-read:

* *both slots are abstract `ℕ → Prop` families, neither is baked in.* The corpus's conjunct
  names two specific families at chapter C's level-`i` data; abstracting them is what lets the
  conjunct be stated in chapter D without naming C's tower, and it is what makes the consumption
  fence a *contract* rather than a theorem — Lean cannot stop a consumer from instantiating
  `HVR` badly, so the fence above is stated at the node and the voided name is kept out of the
  tree. The intended instantiation is pinned as a unit test below.
* *the `∧` is the whole content, and the `i` index is shared.* `EFF.T5.10` says the HVR
  hypothesis rides **alongside** `𝒲_{≤i}` at the same rung; the definition applies both families
  at the same `i`, with no relation between them asserted. It is deliberately NOT `HVR i ∧ HVR
  (i-1) ∧ …`: the HVR fence is per-rung (D.62's `q` is the level's own use-height), whereas the
  `𝒲` leg is cumulative *inside* `Wle`. Flattening either into the other is the conflation
  `EFF.T5.10` forbids.
* *no `i ≥ 3` bound is built into the definition.* Display A quantifies `∀ i ≥ 3` at the
  consumer; the carrier is total in `i`, and at `i ≤ 2` the `𝒲` leg is empty (D.55's `Wle_two`),
  so the conjunct collapses to `HVR i` alone — machine-checked below at `i = 2`. That collapse is
  exactly the `n ≤ 2` slice the blueprint's TEETH row says chapter I's gates re-fire; it is a
  statement about the EMPTY conjunction and says nothing whatever at `i ≥ 3`.

**DEPENDS.** D.55 (`Wle`), D.62 (`HVarthetaRes`, the RE-SIGNED form) + D.44 for the intended `W`
(transitive through D.55, exercised in the `example`s below). Both are imported, so the intended
instantiation is a checked term and not a comment.

**PROOF.** definitional.

**SIZE.** 6 lines.

SOURCE: `EFF.T1.09` (the `(H-VARTHETA-RES)_i` display and its R9-2 fence), `EFF.T3.22` (the
`𝒲_{≤n}` conjunction), `EFF.T5.10` (the two stacked families, "alongside"), `EFF.T5.13` (the
cumulative hypothesis and its empty base); Display A's conjunct list
(`spec/HYPOTHESIS_LEDGER.md` capstone preview — the `∀ i ≥ 3` row; CONVENTIONS Part IV item 4's
sign-off surface names `(H-VARTHETA-RES)`/`𝒲` explicitly). Amendment A-D.2 / DECISION D-2 for
the consumption re-sign.

**TEETH.** none (a carrier); chapter I's gates re-fire the `n ≤ 2` slices where the conjunct is
empty. The checkable content in this file is the ABSENCE of any discharge, listed above.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only). Signature byte-unchanged from the leanspec stub
(`leanspec/Leanspec/ChapD.lean` §9, commit `d420f112`) modulo the namespace
(`Uniformity.Density.Gauge` per GC-6.2).
-/

namespace Uniformity.Density.Gauge

/-- **D.63** Display A's `∀ i ≥ 3` conjunct (`EFF.T1.09` + `EFF.T3.22` + `EFF.T5.10/.13`),
assembled: `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}`. A CARRIER — chapter D discharges neither leg; per the
Part V owner ruling the terminal disposition in chapter I is DISCHARGE NODE or LITERATURE CITE.
**CONSUMPTION FENCE (A-D.2):** `HVR` must be instantiated at the RE-SIGNED sitewise
`HVarthetaRes` (D.62) over the level-`i` ambient residue datum; the pre-A-D.2 existential form
`HVarthetaResVoided` degenerates this definition to `Wle` plus an exact-height fact (defect
D-D12, machine-refuted) and instantiating `HVR` there is a defect. -/
def VarthetaWConjunct (HVR W : ℕ → Prop) (i : ℕ) : Prop := HVR i ∧ Wle W i

/-- The intended instantiation (DEPENDS: D.62 as RE-SIGNED, D.55, D.44), as a unit test rather
than an assertion: at level-`j` height data `v j` with ambient residue datum `ρ j`, use-height
`q j`, arena `A j`, read `R j` and peel unit `w j`, the carrier unfolds to exactly
`(H-VARTHETA-RES)_i ∧ ⋀_{3≤q≤i}[GENTOW5-W(q)]`. Nothing is discharged: this is an `Iff.rfl`
about the shape of the conjunct at arbitrary supplied families. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {N : NormSection G} (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) (i : ℕ) :
    VarthetaWConjunct (fun j => HVarthetaRes G K L N (v j) (ρ j) (q j))
        (fun j => GentowW (A j) (q j) (R j) (w j)) i ↔
      HVarthetaRes G K L N (v i) (ρ i) (q i) ∧
        ∀ j, 3 ≤ j → j ≤ i → GentowW (A j) (q j) (R j) (w j) :=
  Iff.rfl

/-- The `n ≤ 2` slice, machine-checked (the blueprint's TEETH row): at `i = 2` the `𝒲` leg is the
EMPTY conjunction (D.55's `Wle_two`), so the conjunct carries the HVR leg alone. ⚠ This is a
statement about the empty range `3 ≤ q ≤ 2` and says NOTHING at `i ≥ 3`, where both legs are
live and neither is discharged anywhere in this chapter. -/
example (HVR W : ℕ → Prop) : VarthetaWConjunct HVR W 2 ↔ HVR 2 :=
  ⟨fun h => h.1, fun h => ⟨h, Wle_two W⟩⟩

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.VarthetaWConjunct

end AxCheck
