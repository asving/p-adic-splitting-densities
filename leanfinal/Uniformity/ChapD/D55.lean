/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D44

/-!
# Uniformity.ChapD.D55 — `Wle`, the cumulative hypothesis `𝒲_{≤i}`

**Chapter D, NODE D.55** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame (T5);
amendments A-1, A-D.1 govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag, so
the composed text is its signed text). ENV-D1 (the arithmetic arena: the predicate's own content
is a `ℕ`-range quantifier; nothing here is field- or polynomial-valued). Two signed
declarations, and the first is a **CARRIER**.

*The cumulative hypothesis.* For a rung-indexed family of laws `W : ℕ → Prop` — instantiated at
`[GENTOW5-W(q)]`, i.e. D.44's `GentowW` at chapter C's rung-`q` data —

```
Wle W i  :=  ∀ q, 3 ≤ q → q ≤ i → W q          i.e.   𝒲_{≤i} = ⋀_{3≤q≤i} [GENTOW5-W(q)],
```

with `Wle W 2` the EMPTY conjunction, trivially true (`EFF.T5.13`'s r4-G1 base repair).

## ⚠ THE NON-DISCHARGE DISCIPLINE — the reason this node exists

Transcribed verbatim (D-H5(2), `EFF.T5.29`):

> "Certification of the WI companion does not discharge these conjuncts from the frozen GENTOW5
> statements."

Ledger `HYP.63` carries `𝒲_{≤i}` with disposition **"CARRY — WI proves only the induction step,
not induction from empty base"**; the chapter's ledger interface lists the structural edge
`BP.D.55 → HYP.63` as a *disclosure, never a discharge*. **Nothing in this chapter, and nothing
in any chapter, discharges an instance of this predicate**; chapter I carries it (D.63), and
`EFF.T3.22`'s `𝒲_{≤n}` conjunction is this same predicate at the top rung.

The r1 form quoted above is the governing one. The stale opposite at source L299 (ledger
`HYP.100`) — physically present in the corpus, superseded — is **NOT transcribed**, here or
anywhere in `leanfinal`.

**Operationally, for a consumer:** the only way `Wle W i` may be used is by *extracting* a
conjunct from it (D.57's `wf_law_i`, `h i hi le_rfl`) or by *conjoining* it into a further
hypothesis (D.63's `∧`-shape, and D.62's `(H-VARTHETA-RES)_i` — "a SECOND conditional stack on
the same displays", `EFF.T5.10`, which must not be conflated with this one). A chapter-D
declaration of the form `⊢ Wle W i` at any `i ≥ 3` would be a defect, not a discharge.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one definition; parent CLAUDE.md trust boundary).
Four recasts against `EFF.T5.13`/`.29` and `EFF.T3.22`, all flagged for the chapter cross-read:

* *`W` is an arbitrary family `ℕ → Prop`, not `GentowW` applied to fixed data.* The corpus's
  conjuncts are `[GENTOW5-W(q)]` at chapter C's rung-`q` arena, read and peel unit — three data
  that vary with `q`. Abstracting the whole rung-`q` law to a single `Prop` is what lets the
  cumulative hypothesis be stated in chapter D without naming C's tower; the intended
  instantiation is pinned as an executable unit test below (`Wle_gentowW_intended`-shaped
  `example`), so the abstraction is checked, not merely asserted.
* *the bounds are `ℕ`-bounds and the base is `3`.* `3 ≤ q → q ≤ i` is exactly `⋀_{3≤q≤i}`; the
  rungs below 3 are outside the conjunction *by the corpus's own indexing* (rung 2 is
  `(WF-law₂)`, D.56, which is UNCONDITIONAL and supplied by GENTOW2-B″; rung 1 is the `ω₁`
  letter-power / WFRAME OPEN-2 fence and is not a `W`-conjunct at all).
* *emptiness is not special-cased.* `Wle W 2` holds because the range `3 ≤ q ≤ 2` is empty in
  `ℕ`, not because the definition branches at `i = 2`; the same argument gives `Wle W 0` and
  `Wle W 1`. The corpus names only `i = 2` (it is the base of T5's rung induction), so only that
  instance is signed — but the reader should know the triviality is the range's, and that this
  is precisely why the empty base **cannot** be inducted upward: `Wle W 2` supplies no conjunct
  to any `i ≥ 3` clause (the r4-G1 refutation, made structural).
* *no monotonicity/weakening lemma is supplied.* `Wle W i → Wle W j` for `j ≤ i` is true and
  one line, and is deliberately absent: the signature is two declarations, and every additional
  fact about the carrier is an invitation to use it as machinery rather than to carry it.

**DEPENDS.** D.44 (the intended instantiation of `W`; imported as `Uniformity.ChapD.D44` and
exercised in the `example` below — `GentowW` is *not* baked into the signature).

**PROOF.** `Wle_two`: `omega` kills `3 ≤ q ∧ q ≤ 2`.

SOURCE: `EFF.T3.22` (the `𝒲_{≤n}` display), `EFF.T5.13` (the cumulative hypothesis + the empty
base), `EFF.T5.29` (the non-discharge sentence + the superseded-but-physically-present
predecessor, `HYP.100`).

**TEETH.** T3 §8.3(4)/§8.4(5) and T5 §7 Pass 1(3)/Pass 2(5) (the conditionality lints) → the
def's shape plus §12's signed rows: the §13 routing table reads T3 §8.3(4)–(6) as **signed
non-applicability** precisely because "carriers D.55/D.59/D.60 never discharge", i.e. *no
discharge theorem exists to lint*. This file is that absence, machine-checkable: the only
theorem it contains is the empty-range base. The chapter census (D.68) `#check`s `Wle` at its
stated type — it is one of the six carrier definitions gate item (iii) names (D.44, D.55, D.59,
D.60, D.62, D.63).

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only): `Wle_two` is PROVED here, not the leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.55** `𝒲_{≤i}` (`EFF.T3.22`, `EFF.T5.13/.29`). CARRY (`HYP.63`); never discharged —
"Certification of the WI companion does not discharge these conjuncts from the frozen GENTOW5
statements" (the r1 form; the stale opposite at source L299 / `HYP.100` is NOT transcribed). -/
def Wle (W : ℕ → Prop) (i : ℕ) : Prop := ∀ q, 3 ≤ q → q ≤ i → W q

/-- **D.55** `𝒲_{≤2}` is the EMPTY conjunction (`EFF.T5.13`, the r4-G1 base repair): the range
`3 ≤ q ≤ 2` is empty in `ℕ`. It supplies no conjunct to any `i ≥ 3` clause — which is exactly
why the base cannot be inducted upward. -/
theorem Wle_two (W : ℕ → Prop) : Wle W 2 := by
  intro q h3 h2
  omega

/-- The intended instantiation (DEPENDS: D.44), as a unit test rather than an assertion: at
chapter C's rung-`q` data — arena `A q`, read `R q`, peel unit `w q` — the cumulative hypothesis
unfolds to the corpus's `⋀_{3≤q≤i} [GENTOW5-W(q)]`. Nothing is discharged: this is an `Iff.rfl`
about the shape of the conjunction, at an arbitrary supplied family. -/
example {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : ℕ → GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) (i : ℕ) :
    Wle (fun q => GentowW (A q) (q : ℤ) (R q) (w q)) i ↔
      ∀ q, 3 ≤ q → q ≤ i → GentowW (A q) (q : ℤ) (R q) (w q) :=
  Iff.rfl

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.Wle
#print axioms Uniformity.Density.Gauge.Wle_two

end AxCheck
