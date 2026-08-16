/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D55
import Uniformity.ChapD.D59

/-!
# Uniformity.ChapD.D60 — `WfChain`, the `(G5-COND)`/`(WF-chain)` conditional consumer chain

**Chapter D, NODE D.60** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame (T5);
amendments A-1, A-D.1 govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag, so
the composed text is its signed text; A-D.2 touches D.62/D.63 only). ENV-D1 (the arithmetic
arena: the carrier's content is an indexed implication chain over `Fin 8`; nothing here is
field- or polynomial-valued). One signed declaration, and it is a **CARRIER**.

*`(G5-COND)`/`(WF-chain)`: the conditional consumer chain, as a carrier.* The corpus's eight
stations

> `𝒲_{≤n} ⟹ (a)@n ⟹ Corollary 6.4 ⟹ (b)@n ⟹ S11.1.1/S11.1.3 ⟹ (c)@n ⟹ (e)@n ⟹ the next
> automatic floor`

are carried as the chain-of-implications predicate over a station vector `P : Fin 8 → Prop`:

```
WfChain P  :=  ∀ k : Fin 7, P k.castSucc → P k.succ
```

— seven arrows between eight stations, with the vector instantiated by chapter C
(`P 0 := Wle W n` — D.55's cumulative hypothesis; `P 3 := WfIndex …`-content at clause (b) —
D.59's corrected-index display; the remaining stations are C's clause nodes, wired at the GC-13
resolution pass). D.55 and D.59 are imported for exactly that reason — they are the two
stations chapter D owns names for — and for nothing else: **this file instantiates no station,
and chapter I is the consumer of the assembled conditional.**

## The two transcription notes that travel with the carrier

1. **The hypothesis is DELIBERATELY the cumulative one** (`EFF.T5.30`). T5's display promotes
   the source's single-conjunct antecedent `[GENTOW5-W(n)]` to `𝒲_{≤n}` — "on the corrigendum's
   own instruction … **the one place T5's display is *stronger in hypothesis* than the raw
   source line**". The carrier uses the cumulative form. A consumer who reads station 0 as the
   single conjunct is reading the superseded line.
2. **The scope rows, with exactly two carve-outs** (`EFF.T5.31`; `EFF.T3.23`'s ride-list is the
   same content at T3 granularity). Clauses (a)/(b)/(c)/(e)'s listed conclusions ALL consume
   `𝒲_{≤n}`. The two things that do not:
   * "S11.1.2's numerical ρ-ladder remains unconditional floor arithmetic";
   * "a floor inequality explicitly included in the fixed datum remains independently
     available".

## The `w`-blind fence (`EFF.T3.23`, verbatim)

> *""w-blind" means invariant after the single-`w_i` geometric law has been proved. It does not
> construct that law from an arbitrary fixed per-grade family."*

That is: `w`-blindness of a station is a statement about what happens *downstream of* the
(WF-law), never a route to it. The route to the law is D.44's port family (supplied at `i = 2`
by chapter C, D.42/D.56) and nothing else; per-grade fixedness alone does NOT prove (WF-law)
(D.61's supplier record says so at the `i ≥ 3` row).

## What this node does NOT do

**No chapter-D node discharges a station** — that is the whole lint attached to this carrier
(T3 §8.3(4)/§8.4(5), T5 §7 Pass 1(3)). In particular:

* station 0 is `Wle W n`, and D.55 is explicit that nothing in any chapter discharges an
  instance of it (`HYP.63` CARRY; `EFF.T5.29`'s r1 non-discharge sentence, the stale opposite
  at source L299 / `HYP.100` NOT transcribed);
* `WfChain P` is an implication chain, not a proof of any `P k`: from it alone no station
  follows. Supplying `P 0` is chapter C's business at `i = 2` and open at `i ≥ 3`;
* the `(H-VARTHETA-RES)_i` stack (D.62) is a SECOND conditionality on the same displays
  (`EFF.T5.10`) and is NOT one of these eight stations — conflating the two is the error that
  §12's signed rows lint for.

## Faithfulness (trust boundary — this node introduces a public DEFINITION)

1. **Eight stations, seven arrows.** `Fin 8` for the station vector and `Fin 7` for the arrows,
   with `k.castSucc`/`k.succ` the adjacent pair, is a literal rendering of the displayed chain:
   the indices cannot slip, because `castSucc`/`succ` are the only two maps used and they differ
   by exactly one.
2. **`P` is arbitrary.** The predicate says nothing about what the stations ARE; the corpus's
   station reading is documentation here and instantiation data at the consumer. A carrier that
   pinned the stations would be asserting chapter C's clause statements in chapter D.
3. **The direction is fixed.** The chain runs `𝒲_{≤n} ⟹ … ⟹` the next automatic floor, i.e.
   from the hypothesis to the floor, never back; the def's shape `P k.castSucc → P k.succ`
   carries that direction structurally.

**DEPENDS.** D.55 (`Wle`, station 0), D.59 (`WfIndex`, the clause-(b) station content) — both
station content, both landed; no mathlib lemma is used (the declaration is definitional).

**PROOF.** definitional.

**SOURCE.** `EFF.T3.23` (the boxed `(G5-COND)`, the ride-list, and the `w`-blind fence quoted
above), `EFF.T5.30` (`(WF-chain)` + the strengthening note), `EFF.T5.31` (the four scope rows
and the two carve-outs).

**TEETH.** T3 §8.3(4)/§8.4(5), T5 §7 Pass 1(3) → §12 signed rows. A carrier has no executable
content: the lint is exactly that no chapter-D node discharges a station, and this file's
`#print axioms` block plus the absence of any `theorem` here is what makes that checkable.

**ENVIRONMENT.** ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only). One `def`, no theorem — by signature.
-/

namespace Uniformity.Density.Gauge

/-- **D.60** The `(G5-COND)`/`(WF-chain)` implication chain (`EFF.T3.23`, `EFF.T5.30/.31`):
the eight stations

```
𝒲_{≤n} ⟹ (a)@n ⟹ Cor 6.4 ⟹ (b)@n ⟹ S11.1.1/S11.1.3 ⟹ (c)@n ⟹ (e)@n ⟹ next automatic floor
```

carried as seven adjacent implications on a station vector `P : Fin 8 → Prop`.  Stations are
supplied by chapter C (`P 0 := Wle W n`, `P 3 := WfIndex …`-content at clause (b)); chapter I
consumes the assembled conditional.

⚠ **NO chapter-D node discharges a station.**  The antecedent is deliberately the CUMULATIVE
`𝒲_{≤n}`, not the source's single conjunct `[GENTOW5-W(n)]` (`EFF.T5.30`: the one place T5's
display is stronger in hypothesis than the raw source line).  Two carve-outs ride outside the
chain (`EFF.T5.31`): S11.1.2's numerical ρ-ladder, and a floor inequality explicitly included
in the fixed datum. -/
def WfChain (P : Fin 8 → Prop) : Prop := ∀ k : Fin 7, P k.castSucc → P k.succ

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.WfChain

end AxCheck
