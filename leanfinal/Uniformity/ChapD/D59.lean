/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D34a

/-!
# Uniformity.ChapD.D59 — `WfIndex`, the `(WF-index)` corrected-index residual display

**Chapter D, NODE D.59** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame (T5);
amendments A-1, A-D.1 govern). ENV-D3 (the residue-field arena: a bare `[Field K]`; nothing here
counts). One public declaration, and it is a **CARRIER**: the instances are chapter C's, and
consumption runs through D.60's chain under `Wle`. **No chapter-D node discharges it.**

*`(WF-index)`: the corrected-index residual-power carrier.* For a top rung `n`, level reads
`Rlev` (chapter C's `R_{j−1}(Φ_{n+1})`), residuals `ψ`, twist units `ω` and multiplicities `l`:

```
WfIndex Rlev ψ ω l n  :=  ∀ j, 2 ≤ j ≤ n+1 →
                            R_{j−1}(Φ_{n+1}) = (ψ_j^{(ω_{j−1})}) ^ (l_{j+1}⋯l_{n+1})
```

with the twist `ψ_j^{(ω_{j−1})} = wtwist (ω (j−1)) (ψ j)` of D.34, and the ω-assignment
`ω₁ =` S11.3's fixed letter-power unit, `ω₂ = w₂`, `ω_q = w_q` for `q ≥ 3`.

## The index correction, and why it is the whole point of the node

The display **as first written** demanded `w_{n+1}` at the top term, **exceeding the assumed
`𝒲_{≤n}`** — an off-by-one that would have consumed a conjunct outside the hypothesis. The
corrected index is `ω_{j−1}`, and the corrigendum's own fence is transcribed: "No display in T3
uses the superseded index `ψ_j^{(ω_j)}`", and neither does any D node. In this definition the
correction is **structural, not a side condition**: the twist unit is literally `ω (j - 1)`, so
the superseded form is not expressible without editing the definition. That is what the T3
§8.3(5)/§8.4(6) and T5 §7 Pass 1(4)/Pass 2(6) index lints ask for.

The `j = 2` leg is scoped to `ω₁`'s OWN letter-power form — "NOT via
`(C3-ladder-nonvanishing)` applied to a displayed `w₁`. Its identification with `w₁` is exactly
WFRAME OPEN-2; the `i = 1` display stays open with it" (`EFF.T5.09`). Correspondingly `ω` is an
arbitrary family `ℕ → Kˣ` here: **nothing in this file identifies `ω₁` with `w₁`**, and nothing
may.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one definition; parent CLAUDE.md trust boundary).
Four recasts, flagged for the chapter cross-read:

* *`j − 1` is `Nat` subtraction, and the truncation never bites.* The quantifier carries
  `2 ≤ j`, so `j − 1 ≥ 1` throughout and the corpus's `j−1` is the honest one. (The blame case
  `j = 0 ↦ 0 − 1 = 0` is outside the range by hypothesis.)
* *the empty product IS the top term.* At `j = n+1` the index set `Finset.Icc (n+2) (n+1)` is
  empty, so the exponent is `1` and the clause reads `R_n(Φ_{n+1}) = ψ_{n+1}^{(ω_n)}` — the top
  term at `ω_n`, which is precisely the corrected index the corrigendum installed in place of
  `w_{n+1}`. The `Icc` spelling is what makes this automatic rather than a case split.
* *`Rlev` is a bare family `ℕ → Polynomial K`.* The corpus writes `R_{j−1}(Φ_{n+1})`; the
  polynomial `Φ_{n+1}` is fixed by the top rung `n`, so it is absorbed into the family rather
  than carried as an argument. A supplier instantiating this carrier must supply the reads of
  ONE `Φ_{n+1}`; the definition cannot enforce that, which is a genuine (and disclosed)
  instantiation obligation on chapter C.
* *the outer `ψ₁` leg is absent by design.* The range starts at `j = 2`, so `ψ 1` never appears.
  That leg "is separately governed and UNNAMED" — T3 §8 deferred obligation 2,
  `[supplied-by: chapter C]` if GENTOW5's spec exposes it. Its absence here is the fence, not an
  oversight.

**ORIENTATION.** The twists are `wtwist` at the units `ω_{j−1}` — **no ϑ enters**. The index
correction is an `ω`-INDEX matter and is kept apart from D.06's ϑ-orientation rows; conflating
the two is exactly the T5 §7 Pass 1(4)/Pass 2(6) "twist-index mutant".

**DEPENDS.** D.34 (`wtwist`, imported as `Uniformity.ChapD.D34a`).

**PROOF.** definitional.

SOURCE: `EFF.T5.32` (the boxed `(WF-index)`, the `ω` assignment, and the corrigendum reason),
`EFF.T3.24` (`(G5-TWIST)` — T3's copy of the same display, with the `ψ_j`-carries list and the
`ψ₁` fence).

**TEETH.** T3 §8.3(5)/§8.4(6), T5 §7 Pass 1(4)/Pass 2(6) (the index lints) → the definition
fixes `j−1` structurally; §12. The chapter census (D.68) `#check`s this carrier at its stated
type — it is one of the six carrier definitions that gate item (iii) names.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open Polynomial

/-- **D.59** The clause-(b) corrected-index display (`EFF.T5.32` `(WF-index)`, `EFF.T3.24`
`(G5-TWIST)`):

```
∀ j, 2 ≤ j ≤ n+1 → R_{j−1}(Φ_{n+1}) = (ψ_j^{(ω_{j−1})}) ^ (l_{j+1}⋯l_{n+1}).
```

A **CARRIER**: instances are chapter C's; consumed under `Wle` per D.60's chain. The corrected
index is `ω_{j−1}` — the first-written `w_{n+1}` at the top term EXCEEDED the assumed `𝒲_{≤n}`,
and no display uses the superseded `ψ_j^{(ω_j)}`.  The `j = 2` leg rides `ω₁`'s own letter-power
form; its identification with `w₁` is WFRAME OPEN-2 and is NOT asserted here. -/
def WfIndex {K : Type*} [Field K] (Rlev : ℕ → Polynomial K) (ψ : ℕ → Polynomial K)
    (ω : ℕ → Kˣ) (l : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j ≤ n + 1 →
    Rlev (j - 1) = (wtwist (ω (j - 1)) (ψ j)) ^ (∏ k ∈ Finset.Icc (j + 1) (n + 1), l k)

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.WfIndex

end AxCheck
