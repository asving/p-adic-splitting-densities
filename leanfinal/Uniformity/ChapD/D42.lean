/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D42 — `(ABS-G2)`: the `i = 2` discharge, chapter C's port construction

**Chapter D, NODE D.42** [interface] [fresh — GC-13 placeholders]
(`blueprint/CHAP-D_gauge_tchain.md` §5, the read bundle and the B-law / T3's routing;
amendments A-1 and A-D.1 govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag,
so the composed text is its signed text; A-D.2 touches D.62/D.63 only). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none in
chapter D` and gives the reason verbatim: *"the conclusion is D.38 + D.35 applied to C's
instance; a D-side alias theorem would duplicate a name across the chapter boundary."*
Together with `PROOF. n/a (interface)`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`.

§12 rule 4 is the standing reason and it is mandatory: **"No stub for another chapter's
placeholder: the `[supplied-by: chapter C]` rows are NOT axiomatized in leanspec (axiomatizing
a supplier's theorem would fake the discharge — exactly the class of defect the honesty items
fence)."** The stage-0e stub gate held that line for this node by name (`leanspec/Leanspec/
ChapD.lean`: "**D.42** [interface] `(ABS-G2)` … NO Lean declaration in chapter D; per §12
rule 4 nothing is axiomatized here"), and this landed copy holds it: the file **imports nothing
and defines nothing**, so it cannot become a silent dependency of any proof, and no
`EFF.GENTOW2` fact acquires a Lean name here.

What the node *is*, then, is the instantiation record: which parameters T3's §3 absorption
binds, which chapter-D theorems are the D-side of the conclusion, what chapter C still owes,
and which fences travel with it.

## The instantiation (T3 §3, `EFF.T3.19`)

Fix `t < f₃`. The absorption binds

| parameter | value |
|---|---|
| the telescope length | `s = f₃ − t` |
| the step | `q = u₃` |
| the norm section | `N = n̂₂`, i.e. `N(q) = n̂₂(u₃)`, `N(sq) = n̂₂(su₃)` |
| the source's B-law-oriented unit | `ϑ_G2(t) := res(n̂₂(su₃) / n̂₂(u₃)^s) = Θ_N(s;u₃)` |
| the peel unit | `w = R_{3,k̄}(n̂₂(u₃))` |
| the per-grade factor | `U₂(β_t) = u(β_t)` |

The sentence that discharges `(BR1)`–`(BR5)` at this rung, quoted:

> "GENTOW2's expansion, peel, positive-degree elimination, exact-grade digit law, and
> root-evaluation calculation are **precisely (BR1)–(BR5)**."

Therefore `(T3-BR)` — the chapter-D theorem `BoundaryReadPort.t3_br` (D.38) — gives the closed
absorbed display, quoted:

> `s = f₃ − t`,
> `u(β_t) = ϑ_G2(t)·w^{f₃−t}`,
> `y^{f₃} − Σ_{t<f₃} ϑ_G2(t)·w^{f₃−t}·c_t·y^t = w^{f₃}P(y/w)`,
> `P(y) = y^{f₃} − Σ_{t<f₃} ϑ_G2(t)·c_t·y^t`.   `(ABS-G2)`

> "This absorbs GENTOW2-B″ and its factor-pattern invariance. **No value of `w` is required.**"

**CONDITIONALITY, transcribed:** *"Unconditional at the landed `i = 2` rung."*

## The chapter-D side of the conclusion — already landed, and NOT re-named here

Every D-side ingredient of `(ABS-G2)` is a theorem this chapter has already landed under its
own name; the interface adds nothing to them.

* the B-law line `u(β_t) = ϑ_G2(t)·w^{f₃−t}` is
  `Uniformity.Density.Gauge.BoundaryReadPort.t3_br` (D.38), `P.U = Θ(q,s)·w^s`, at `s := f₃−t`,
  `q := u₃` — a theorem about ANY `BoundaryReadPort`, hence about C's, once C builds one;
* the rescaling line `y^{f₃} − Σ ϑ_G2(t)w^{f₃−t}c_t y^t = w^{f₃}P(y/w)` is
  `Uniformity.Density.Gauge.wtwist_psi` (D.35) applied to the coefficient family
  `t ↦ ϑ_G2(t)·c_t`, whose right-hand side `w^{f₃}P(y/w)` is `wtwist w P` (D.34) at the signed
  `Kˣ`-inverse reading — `P` monic of `natDegree f₃`, so D.34's `natDegree` scalar is the
  corpus's `w^{deg P}`;
* the factor/root/separability half of "factor-pattern invariance" is D.34's transport package
  (`wtwist_monic`, `wtwist_coeff_zero`, `wtwist_irreducible`, `wtwist_separable`, `wtwist_eval`,
  `wtwist_mul`) — `(T3-ROUTE)`, stated once at D.34 and instantiated at D.41.

⚠ **This file does not compose them.** Composing them into a single named `(ABS-G2)` theorem is
exactly the D-side alias the SIGNATURE forbids, because the composite's hypothesis is C's port
instance; the orchestrator wires C's construction to D.38 at the GC-13 resolution pass.

## What chapter C owes (the placeholder)

The port instance — `EFF.GENTOW2.43 [supplied-by: chapter C]` (LEMMA GENTOW2-B″, whose proof
`.44` step (iv) consumes B′(3) = `EFF.GENTOW2.34 [supplied-by: chapter C]`) — constructing
`BoundaryReadPort (levelTwoArena) u₃ (f₃−t)` **per slot**, over `EFF.GENTOW2.42
[supplied-by: chapter C]`, the letter-group arena instance (D-H3(ii)).

⚠ `levelTwoArena` is **not a chapter-D name** and is not introduced here: chapter D declares the
abstract `GaugeArena` and `BoundaryReadPort` only (`levelOneArena`, D.17, is the level-1 arena
and is a different object). Guessing a chapter-C node ID or arena name would break the same
fence §12 rule 4 states; the placeholder IDs above are quoted, not resolved.

## ORIENTATION (blueprint block, transcribed)

`ϑ_G2` is D.06 row 3 = `varthetaG2` / `theta` — **the ANNOTATION IS the content here**: C's port
construction must land its digit clause in T1-orientation `vartheta` (that is `BR5`,
`digit = ϑ_{i,s}` = `A.vartheta q s`) and read its conclusion in GENTOW2-orientation (`theta`,
D.38's endpoint), the involution D.10 (`GaugeArena.theta_mul_vartheta`,
`GaugeArena.varthetaG2_eq`) mediating. A port built with the two orientations swapped is
well-typed and wrong; D.06's re-signed TEETH row carries the executable battery that catches it
(the wrong-orientation B-law fails at `s = 2`).

**DEPENDS.** D.38, D.35, D.10 · `EFF.GENTOW2.43 [supplied-by: chapter C]` ·
`EFF.GENTOW2.34 [supplied-by: chapter C]` · `EFF.GENTOW2.42 [supplied-by: chapter C]`.

**PROOF.** n/a (interface). **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T3.19` (the `(ABS-G2)` block, the BR-discharge sentence, the unconditionality
clause, `ϑ_G2(t) = Θ_N(s;u₃)`).

**TEETH.** T3 §8.3(1) (GENTOW2-B″ leg) → executable regression retained (§12); the landed
absorption append (T3 X29) → provenance note. §13's routing row reads this leg as "**executable
regression retained** + the D.42/D.44 interfaces (discharge is C's)".

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
