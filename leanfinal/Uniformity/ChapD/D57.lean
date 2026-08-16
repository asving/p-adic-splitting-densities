/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D55

/-!
# Uniformity.ChapD.D57 — `wf_law_i`, `(WF-lawᵢ)`: the higher rung RETAINS its hypothesis

**Chapter D, NODE D.57** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame
(T5); amendments A-1, A-D.1 and A-D.2 govern the chapter — none of them re-signs this node
(A-D.2 touches D.62/D.63 only), so the composed text is its signed text). ENV-D1 (the
arithmetic arena: the statement's own content is a `ℕ`-range quantifier; nothing here is field-
or polynomial-valued). One signed declaration.

*The higher rung.* For `i ≥ 3`:

```
Wle W i → W i          i.e.   𝒲_{≤i} ⟹ [GENTOW5-W(i)],
```

the rung-`i` law read off as the **LAST CONJUNCT** of the cumulative hypothesis (D.55's `Wle`,
`𝒲_{≤i} = ⋀_{3≤q≤i}[GENTOW5-W(q)]`). Transcribed (`EFF.T5.15`):

> "the new rung hypothesis is `[GENTOW5-W(i)]`; the earlier members remain the ambient
> induction history. The existence or certification of the companion note does not remove
> these hypotheses from the statement."

With `W i := GentowW` at the level-`i` data (D.44) the consequent unfolds to the boxed display
`𝒲_{≤i} ⟹ [u_i(β_t) = Θ_i(t)·w_i^{s_t}]`.

## ⚠ Why the triviality is the POINT

`h i hi le_rfl` is the whole proof, and that is the node's content, not an embarrassment about
it. The corpus's r1 repair **replaced a discharge claim by hypothesis-retention**; retention in
Lean *is* conjunct extraction. Anything stronger here — in particular a theorem deriving
`Wle W i → W (i+1)`, or `W i` from `Wle W 2` — would be the r4-G1-refuted "induction from empty
base" (D.55: `Wle W 2` is the EMPTY conjunction, so it supplies no conjunct to any `i ≥ 3`
clause). The file therefore contains exactly one implication, and it consumes its hypothesis.

**The two-scope split.** `(WF-law₂)` and `(WF-lawᵢ)` are two nodes — D.56 and this one — because
`EFF.T5.12`'s r1 split supersedes the base note's single unscoped law: at `i = 2` the law is
UNCONDITIONAL and **supplied** by chapter C (LEMMA GENTOW2-B″; D.56 declares nothing, by
signature), while at `i ≥ 3` it is reached only inside `𝒲_{≤i}`, through this theorem.

## ⚠ The stacked conditionality (`EFF.T5.14`), transcribed for consumers

Three layers ride the `i ≥ 3` display, and this theorem discharges NONE of them; it only names
the first:

1. **`𝒲_{≤i}`** — the hypothesis of this statement (D.55, ledger `HYP.63`, disposition CARRY).
2. **`(H-VARTHETA-RES)_i`** at every `i ≥ 3` use of `Θ_i(t)` — D.62's carrier (as RE-SIGNED at
   A-D.2 / DECISION D-2: the sitewise ambient-residue clause; the pre-A-D.2 existential form is
   VOID, defect D-D12). `EFF.T5.10` fences the two apart: it is "a SECOND conditional stack on
   the same displays and must not be conflated with `𝒲_{≤i}`". D.63 is the assembled `∧`.
3. **`(C3-ladder-nonvanishing)`** at every `w_i` site — typed into the bundles rather than
   carried as a side condition: D.29's and hence D.44's `w : Kˣ` (D-H6, `HYP.99`, the honest
   two-clause strengthening disclosed at D.56(1)/D.61(4)). Nothing in this file mentions `w`,
   because the abstraction `W : ℕ → Prop` hides the rung's data — see the faithfulness note.

Per-level suppliers for the `w`-sites are D.61's record: `i = 2` GENTOW2-B′(3)/B″; `i ≥ 3`
GENTOW5 S11.2's PROVED fixed-unit list, routed AROUND `𝒲_{≤i}` (and per-grade fixedness alone
does NOT prove (WF-law) — `EFF.T5.16`); `i = 1` NONE.

## Faithfulness

**⚠ Trust-boundary statement** (one theorem; parent CLAUDE.md trust boundary). Three recasts
against `EFF.T5.14`/`.15`, flagged for the chapter cross-read:

* *`W` is the same arbitrary family `ℕ → Prop` as D.55's, not `GentowW` at fixed data.* The
  corpus's `[GENTOW5-W(i)]` is a law about chapter C's rung-`i` arena, read and peel unit; the
  abstraction is what lets the retention statement be made in chapter D without naming C's
  tower. It is checked, not asserted: the `example` below instantiates `W` at D.44's `GentowW`
  and gets the corpus's implication `⋀_{3≤q≤i}[GENTOW5-W(q)] ⟹ [GENTOW5-W(i)]` by `Iff.rfl`-level
  unfolding.
* *`hi : 3 ≤ i` is genuinely used and genuinely necessary.* It is the `3 ≤ q` leg of `Wle`'s
  quantifier at `q := i`. Dropping it makes the statement FALSE (`Wle W 2 → W 2` fails at, e.g.,
  `W := fun _ => False`, since `Wle (fun _ => False) 2` holds by D.55's `Wle_two`) — so the
  hypothesis bound is not decoration, it is exactly the fence against the r4-G1 move. The
  scope-`i` restriction of the display to `i ≥ 3` is therefore structural here, not stylistic.
* *the conclusion is `W i`, the LAST conjunct — not `Wle W (i-1)`, not any weakening.* The
  corpus sentence says the earlier members "remain the ambient induction history"; accordingly
  this theorem CONSUMES `Wle W i` and returns only the top rung. It does not, and must not, come
  with a converse, a monotonicity lemma, or a step lemma `W i → Wle W i → Wle W (i+1)`: any of
  those turns the carrier into machinery, and the second is the shape the r1 repair removed.

**DEPENDS.** D.55 (`Wle`; imported as `Uniformity.ChapD.D55`) + D.44 for the intended `W`
(reached transitively through D.55's import and exercised in the `example` below — `GentowW` is
*not* baked into the signature).

**PROOF.** `h i hi le_rfl`.

**SIZE.** 6 lines.

SOURCE: `EFF.T5.14` (the boxed `(WF-lawᵢ)` implication and the three-layer conditionality;
`HYP.63`), `EFF.T5.15` (the supplier split and the certification-is-not-discharge sentence
quoted above), `EFF.T5.12` (the r1 two-scope split), `EFF.T5.10` (the HVR stack fence),
`EFF.T5.13`/`EFF.T3.22` (the cumulative hypothesis itself, via D.55).

**TEETH.** T5 §7 Pass 1(2), Pass 2(3), Pass 2(5) (conditionality + supplier-attribution lints)
→ §12's signed rows. As at D.55, the machine-checkable content of those lints is an ABSENCE:
this file's only theorem consumes `Wle W i` and no declaration anywhere in chapter D concludes
`⊢ Wle W i` at any `i ≥ 3`.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only): `wf_law_i` is PROVED here, not the leanspec `axiom`
stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.57** `(WF-lawᵢ)` (`EFF.T5.14`, `EFF.T5.15`): for `i ≥ 3` the rung-`i` law is the LAST
CONJUNCT of the cumulative hypothesis `𝒲_{≤i}`. The triviality is the POINT: the corpus's r1
repair replaced a discharge claim by hypothesis-retention, and hypothesis-retention in Lean is
conjunct extraction; anything more would be the r4-G1-refuted "induction from empty base".
Two further conditional layers ride the same displays and are NOT touched here:
`(H-VARTHETA-RES)_i` (D.62, `EFF.T5.10` — never to be conflated with `𝒲_{≤i}`) and
`(C3-ladder-nonvanishing)` at every `w_i` site (typed into D.29/D.44's `w : Kˣ`). -/
theorem wf_law_i (W : ℕ → Prop) (i : ℕ) (hi : 3 ≤ i) (h : Wle W i) : W i :=
  h i hi le_rfl

/-- The intended instantiation (DEPENDS: D.44), as a unit test rather than an assertion: at
chapter C's rung-`q` data — arena `A q`, read `R q`, peel unit `w q` — the retention statement
is the corpus's `⋀_{3≤q≤i} [GENTOW5-W(q)] ⟹ [GENTOW5-W(i)]`. Nothing is discharged: the
hypothesis is supplied by the caller and consumed. -/
example {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : ℕ → GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) (i : ℕ) (hi : 3 ≤ i)
    (h : ∀ q, 3 ≤ q → q ≤ i → GentowW (A q) (q : ℤ) (R q) (w q)) :
    GentowW (A i) (i : ℤ) (R i) (w i) :=
  wf_law_i (fun q => GentowW (A q) (q : ℤ) (R q) (w q)) i hi h

/-- The hypothesis bound is load-bearing, machine-checked: the `i ≥ 3` scope cannot be dropped,
because `Wle W 2` is the EMPTY conjunction (D.55's `Wle_two`) and supplies nothing. At
`W := fun _ => False` the unscoped statement `∀ i, Wle W i → W i` would give `False`. -/
example : Wle (fun _ => False) 2 ∧ ¬ (fun _ : ℕ => False) 2 :=
  ⟨Wle_two _, id⟩

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wf_law_i

end AxCheck
