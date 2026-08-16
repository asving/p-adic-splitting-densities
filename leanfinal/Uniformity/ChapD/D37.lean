/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D07
import Uniformity.ChapD.D08

/-!
# Uniformity.ChapD.D37 — `BoundaryReadPort`, the boundary-read port `(BR1)–(BR5)`

**Chapter D, NODE D.37** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, the telescope
port (T3); amendments A-1, A-D.1, A-D.2 govern — this node's SIGNATURE is unamended).
ENV-D2 + ENV-D3. One signed declaration.

*The boundary-read port.* Over an arena `A : GaugeArena G K N` at ladder step `q : ℤ` and
exponent `s : ℕ`, a **boundary-read port** carries the source-local read data of the group
element `N(q)^s`:

| field | corpus object (`EFF.T3.06`–`.11`) |
|---|---|
| `w : Kˣ` | the peel unit `w_i` |
| `ctR : K` | the peeled read `ct(R)` |
| **(BR1)** `br1` | `ctR = w^s` — the peel |
| `ctRQ : ℕ → K`, `expSupport : Finset ℕ` | the `Φ_i`-adic expansion reads and their support |
| **(BR2)** `br2` | `ctR = Σ_{j ∈ expSupport} ctRQ j` |
| **(BR3)** `br3` | positive-degree elimination: `∀ j ≠ 0, ctRQ j = 0` |
| `U : K`, `digit : K` | the per-grade factor `U_i(β_s)` and the coherent digit |
| **(BR4)** `br4` | `ctRQ 0 = U · digit` — the surviving constant coefficient factors |
| **(BR5)** `br5` | `digit = ϑ_{i,s}`, the evaluation against D.08's telescope |

## The fence IS the field list (transcribed as a NON-field)

`EFF.T3.11`: *"These are source-local residual-read hypotheses. **Neither the B-law nor a
one-`w_i` power law is included among them.**"* That fence is landed as the **absence** of any
such field: `BoundaryReadPort` has no B-law field, no `U = Θ·w^s` field, and no one-`w_i`
power-law field. Adding one is the §8.4(3) **"endpoint-as-input" mutant** — the whole point of
D.38 is that `U = Θ_N(s;q)·w_i^s` is *derived* from BR1–BR5 and never supplied, so a port that
carried the endpoint as a hypothesis would make D.38 a tautology and would silently reintroduce
the circularity T3's design note (§6 head) exists to prevent.

The same fence is why this port is a DIFFERENT, weaker, source-local interface than D.29's
`ReadBundle`: T3 deliberately does not consume T1's conditional B-law as a premise for
`[GENTOW5-W(i)]` (`EFF.T3.05`), and the two derivations of the same display — D.32 (bundle ⇒
B-law) and D.38 (port ⇒ B-law) — are kept apart on purpose.

## Faithfulness (trust boundary — this is a DEFINITION)

Two readings are made explicit, both the blueprint's own:

1. **BR2's `Σ_{j≥0}` is carried as an explicit `Finset` support.** The corpus's `Φ_i`-adic
   expansion is finite by degree, so an infinitely-indexed but finitely-supported sum is
   faithfully a `Finset ℕ`-indexed sum. `expSupport` is DATA, not a derived object: nothing
   here claims it is the actual support of `ctRQ` (BR3 only kills the positive-degree reads,
   and `0` need not lie in `expSupport` — D.38 has to *prove* it does, from `w` being a unit).
2. **BR4's "`Q₀` has exact grade `β_s`" is carried IN `br4`'s shape**, not as a separate
   grading hypothesis: the read factors through `U · digit` exactly when the grade is exact
   (the corpus's own reading). The exactness itself is the SUPPLIER's obligation when
   constructing a port, which is exactly the source-locality the fence above insists on.

**Flagged for human review** (definition faithfulness), per the repo trust boundary.

DEPENDS: D.07 (`GaugeArena`, and `NormSection` through it) · D.08 (`GaugeArena.vartheta`, the
`K`-valued telescope BR5 evaluates against) · mathlib `Finset`, `Finset.sum`, `Units`. No other
landed node.

**PROOF.** definitional (a `structure` IS its elaboration check).

SOURCE: `EFF.T3.06` (the port declaration: expansion + `ct`), `.07` (BR1, the peel and `w_i`),
`.08` (BR2, the expansion), `.09` (BR3), `.10` (BR4, the exact constant digit and `U_i(β_s)`),
`.11` (BR5 + the non-circularity fence).

**TEETH.** T3 §8.1(4) ("no conditional B-law input") and §8.4(3) ("endpoint-as-input mutant")
→ **the structure's field list IS the tooth** (no B-law field, no endpoint field); §12 carries
the signed rows. **Non-vacuity is NOT scored here**: `BoundaryReadPort` is inhabited for EVERY
arena, ladder step, exponent and unit, and that witness — whose `U` is FORCED to
`w^s·ϑ⁻¹ = Θ·w^s`, i.e. D.38's own conclusion, from the port axioms alone — is gate content
owned by **D.68** (A-D.1 item (v), which requires the landed census to carry it); duplicating
it here would put two copies of a gate row in the chapter, exactly as D.46 declines to
duplicate its own `CertFrame` witness. Gate D.67 runs the FRAME-C `U`/`ϑ` tables against D.38.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written
inline per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.37 — the boundary-read port `(BR1)–(BR5)`** (`EFF.T3.06`–`.11`): the source-local read
package of `N(q)^s` over an arena `A`, at ladder step `q` and exponent `s`.

⚠ **FENCE (`EFF.T3.11`, transcribed as a NON-field).** "These are source-local residual-read
hypotheses. **Neither the B-law nor a one-`w_i` power law is included among them.**" There is
no B-law field and no `U = Θ·w^s` field below, and adding one is the §8.4(3)
"endpoint-as-input" mutant: D.38 DERIVES the endpoint from BR1–BR5, and a port that supplied it
would make that theorem a tautology. -/
structure BoundaryReadPort {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) where
  /-- The peel unit `w_i` (`EFF.T3.07`). -/
  w : Kˣ
  /-- The peeled read `ct(R)` (`EFF.T3.06`). -/
  ctR : K
  /-- The `Φ_i`-adic expansion reads (`EFF.T3.08`). -/
  ctRQ : ℕ → K
  /-- The finite index set of the expansion — DATA, not the derived support of `ctRQ`; the
  corpus's `Σ_{j≥0}` is finite by degree (`EFF.T3.08`). -/
  expSupport : Finset ℕ
  /-- **(BR1)** the peel: `ct(R) = w^s` (`EFF.T3.07`). -/
  br1 : ctR = (w : K) ^ s
  /-- **(BR2)** the expansion: `ct(R) = Σ_{j ∈ expSupport} ctRQ j` (`EFF.T3.08`). -/
  br2 : ctR = ∑ j ∈ expSupport, ctRQ j
  /-- **(BR3)** positive-degree elimination (`EFF.T3.09`). -/
  br3 : ∀ j ≠ 0, ctRQ j = 0
  /-- The per-grade factor `U_i(β_s)` (`EFF.T3.10`). -/
  U : K
  /-- The coherent digit of the surviving constant coefficient (`EFF.T3.10`). -/
  digit : K
  /-- **(BR4)** the exact constant digit: `ctRQ 0 = U · digit`.  "`Q₀` has exact grade `β_s`" is
  carried in this field's SHAPE; the exactness is the supplier's obligation (`EFF.T3.10`). -/
  br4 : ctRQ 0 = U * digit
  /-- **(BR5)** evaluation against D.08's telescope: `digit = ϑ_{i,s}` (`EFF.T3.11`). -/
  br5 : digit = (A.vartheta q s : K)

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.BoundaryReadPort

end AxCheck
