/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D56 — `(WF-law₂)`: the unconditional base rung of the w-frame

**Chapter D, NODE D.56** [interface] [fresh — GC-13 placeholders]
(`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame (T5); amendments A-1, A-D.1 and A-D.2
govern the chapter — none of them re-signs this node (A-D.2 touches D.62/D.63 only), so the
composed text is its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none in
chapter D` and gives the reason verbatim: *"the statement is `GentowW` at C's instance; D.44
named the predicate precisely so this row is a C-side term, not a D-side axiom."* Together
with `PROOF. n/a`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`.

§12 rule 4 is the standing reason and it is mandatory: **"No stub for another chapter's
placeholder: the `[supplied-by: chapter C]` rows are NOT axiomatized in leanspec
(axiomatizing a supplier's theorem would fake the discharge — exactly the class of defect the
honesty items fence)."** The stage-0e stub gate held that line for this node by name
(`leanspec/Leanspec/ChapD.lean`: "**D.56** [interface] … NO Lean declaration in chapter D —
D.44 named the predicate precisely so this row is a C-side term, not a D-side axiom", and the
gate's own summary lists "D.42, D.43, D.53, D.54, D.56 and D.61 declare nothing … and no
chapter-C/E/F node ID is guessed anywhere in this file"). This landed copy holds the same
line: the file **imports nothing and defines nothing**, so it cannot become a silent
dependency of any proof, and no `EFF.GENTOW2` fact acquires a Lean name here.

What the node *is*, then, is the supplier record for the base rung of the w-frame: which
display holds at `i = 2`, that it holds with **no** `𝒲` hypothesis, who supplies it, which
already-landed chapter-D route is its derivation, and which site obligation it discharges.

## The display: `(WF-law₂)`

At `i = 2`, for every slot `t < f₃`:

> `u₂(β_t) = Θ₂(t)·w₂^{f₃−t} = ϑ_{2,f₃−t}^{−1}·w₂^{f₃−t}`

— the base rung of T5's two-scope law split (`EFF.T5.12`; the r1 split supersedes the base
note's single unscoped law, which is why `(WF-law₂)` and `(WF-lawᵢ)` are two nodes here,
D.56 and D.57, and not one).

**UNCONDITIONAL — no `𝒲` hypothesis.** `𝒲_{≤2} = ⋀_{3≤q≤2}[GENTOW5-W(q)]` is the EMPTY
conjunction (D.55's `Wle W 2`, `EFF.T5.13`'s r4-G1 base repair), so the `i = 2` rung carries
no cumulative-hypothesis conjunct at all. ⚠ This is *not* an induction from the empty base:
the base rung is unconditional because chapter C **supplies** it, not because anything is
derived from the empty conjunction (the r4-G1-refuted move; see D.57's SIZE note and D.55's
`HYP.63` CARRY disposition).

## The supplier

**LEMMA GENTOW2-B″** — `EFF.GENTOW2.43 [supplied-by: chapter C]`, object-addressed at byte
span `33f86204` L729–738, *the same span the D.06 table's row-5 verification pins* (T5 ledger
item 2; ledger md5-8 `d4c8b885`, raw-span md5 `8978f8ba…`; both legs re-checked at EFF compile
time, `EFF.GENTOW2.25`). The supplier record is `EFF.T5.15`'s row, quoted: *"`i = 2`: LEMMA
GENTOW2-B″, unconditionally"*.

⚠ Neither the lemma nor its byte span is given a Lean name here or anywhere in chapter D.
The address is transcribed so that the GC-13 resolution pass can wire the row without
re-deriving it, and so that a consumer meets the provenance before reaching for the display.

## In D-terms: what chapter C constructs, and the landed D-side route

The D-side rendering of the row is: chapter C constructs

> `GentowW A₂ u₃ R₃ w₂`

— D.44's sitewise B-law predicate (`Uniformity.Density.Gauge.GentowW`, landed and green:
`∀ s : ℕ, R (N.n (s·q)) = (A.theta q s : K)·(w : K)^s`) at its level-2 arena, step `q = u₃`,
FGMN read `R₃`, peel unit `w₂`; the corpus's slot-indexed display is this predicate at
`s = f₃ − t` (D.44's faithfulness note 1: consumers reindex, the predicate is stated in the
exponent `s`).

**D.42's port route is the derivation**, and every step of it is already a landed chapter-D
theorem:

* C builds a `BoundaryReadPort A₂ u₃ (f₃−t)` per slot — `EFF.GENTOW2.43`, over the
  letter-group arena instance `EFF.GENTOW2.42`, both `[supplied-by: chapter C]`;
* `BoundaryReadPort.t3_br` (D.38) closes each port to `P.U = Θ(q,s)·(P.w)^s`;
* `gentowW_of_ports` (D.44) converts the port family into the predicate.

⚠ **This file composes nothing.** Composing the three into a named `i = 2` theorem is exactly
the D-side alias D.42's SIGNATURE forbids ("a D-side alias theorem would duplicate a name
across the chapter boundary"), because the composite's hypothesis is C's port instance.
`A₂`, `R₃`, `w₂` are the corpus's objects, not chapter-D names: chapter D declares the
abstract `GaugeArena`, `BoundaryReadPort` and `GentowW` only.

## The site obligation discharged here

`(C3-ladder-nonvanishing)` — the `w`-site nonvanishing obligation that rides at every `w_i`
use — is discharged at this rung by **GENTOW2-B′(3)/B″**, `EFF.GENTOW2.34 [supplied-by:
chapter C]` being the B′(3) leg: *"the discharge T1 r8 itself names at the accepted GENTOW2
site"* (`EFF.T5.09`).

Two things travel with that sentence and are recorded, not repaired:

1. **D-H6, the T5 two-clause staleness (`HYP.99`).** T5 pins T1 at r1–r10 and carries only
   `(C3-ladder-nonvanishing)`; T1 HEAD (r12) makes the gate two-clause — `(C3-read-codomain)`
   places `w_i ∈ K_i`, `(C3-ladder-nonvanishing)` makes it nonzero. The Lean bundle types
   `w : Kˣ` (D.29, and so D.44's `GentowW`), which carries BOTH clauses by construction: an
   honest strengthening, disclosed rather than silently absorbed, and the reason no clause of
   this row ever appears as a `w ≠ 0` side condition in chapter D.
2. **The per-level supplier split is D.61's record, not this node's.** `i = 2`:
   GENTOW2-B′(3)/B″ (here). `i ≥ 3`: GENTOW5 S11.2's PROVED fixed-unit list, routed AROUND
   `𝒲_{≤i}` — and per-grade fixedness alone does NOT prove (WF-law). `i = 1`: NONE.

## Who consumes this row

* **D.58** (`gentowW_realized`, `(WF-realized)`): its `i = 2` leg — `(WF-realized₂)` — is
  unconditional *via this instance*, i.e. the hypothesis `hW : GentowW A q R w` of the landed
  theorem is discharged at `i = 2` by C's GENTOW2-B″ term and by nothing in chapter D. At
  `i ≥ 3` the same theorem is reached only inside `Wle W i`, through D.57.
* **D.61** repeats the `i = 2` supplier row inside the full two-clause gate record; the two
  statements are the deliberate duplication the blueprint sanctions, not a second source.

## ORIENTATION

`Θ₂(t) = ϑ_{2,f₃−t}^{−1}` — **D.06 rows 1–2** (`D-THETA-TABLE`, the chapter's one canonical
copy of the orientation table; the reconciliation row 5 is the verification this display rests
on, and it is the same byte span cited above). In Lean names: `Θ₂(t)` is `A.theta u₃ (f₃−t)`,
T1's two-index `ϑ_{2,s}` is `A.vartheta u₃ s`, the two meet only through D.10's involution
`GaugeArena.theta_mul_vartheta`, and GENTOW2's single-argument `ϑ(t)` is `varthetaG2` (D.10,
row 1). A row-2/row-4 conflation — reading `Θ₂(t)` as `vartheta` at argument `t` instead of
`theta` at argument `f₃−t` — is well-typed and wrong; that is precisely the trap
`D-THETA-TABLE` exists to catch.

**DEPENDS.** D.44 · `EFF.GENTOW2.43 [supplied-by: chapter C]`,
`EFF.GENTOW2.34 [supplied-by: chapter C]` (B′(3), the nonvanishing leg).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T5.12` (the boxed `(WF-law₂)`, its unconditionality, and the r1 two-scope
split superseding the base's single unscoped law); `EFF.T5.15` (the supplier record:
"`i = 2`: LEMMA GENTOW2-B″, unconditionally"); `EFF.T5.09` (the `(C3-ladder-nonvanishing)`
discharge sentence and the staleness flag); `EFF.T5.13` (the empty `𝒲_{≤2}`).

**TEETH.** T5 §7 Pass 1(2)/Pass 2(3) → §12; gate D.67's orientation leg (the FRAME-C battery
scores the two orientations as numerically distinct, which is what makes the `Θ₂(t) =
ϑ_{2,f₃−t}^{−1}` reading above checkable rather than merely asserted).

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
