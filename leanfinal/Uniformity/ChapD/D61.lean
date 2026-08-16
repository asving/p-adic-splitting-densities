/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D61 — the `w`-site record: per-level nonvanishing suppliers, the two-clause gate, the avatar fences

**Chapter D, NODE D.61** [record] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame
(T5); amendments A-1, A-D.1 and A-D.2 govern the chapter — none of them re-signs this node
(A-D.2 touches D.62/D.63 only), so the composed text is its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none`,
`PROOF. n/a`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`; A-D.1's closing paragraph confirms it
("the five GC-13 interface nodes and the two `record` nodes still declare nothing"), and the
stage-0e stub gate held the line for this node by name (`leanspec/Leanspec/ChapD.lean`:
"**D.61** [record] … — NO Lean declaration", and the gate summary "D.42, D.43, D.53, D.54, D.56
and D.61 declare nothing … and no chapter-C/E/F node ID is guessed anywhere in this file"). §12
rule 4 is the standing reason: **the `[supplied-by: chapter C]` rows are NOT axiomatized in
this tree — axiomatizing a supplier's theorem would fake the discharge.** This landed copy holds
the same line: the file **imports nothing and defines nothing**, so it cannot become a silent
dependency of any proof, and no `EFF.GENTOW2`/`EFF.GENTOW5` fact acquires a Lean name here.

What the node *is*: the record every consumer of a `w`-site must read before using D.29's `w`,
D.44's `GentowW`, or any `(WF-law)` display. Five rows, transcribed.

## Row 1 — `i = 2`: the supplier is GENTOW2-B′(3)/B″

**LEMMA GENTOW2-B′(3)** is the per-grade-unit clause; **LEMMA GENTOW2-B″** is the single
slot-independent `w ∈ K₂ˣ` (`EFF.T5.09`; `EFF.GENTOW2.34` and `EFF.GENTOW2.43`, both
`[supplied-by: chapter C]` — placeholders exactly as at D.56, address transcribed there, not
re-derived here). The site obligation `(C3-ladder-nonvanishing)` is discharged at this rung by
that pair — *"the discharge T1 r8 itself names at the accepted GENTOW2 site"* (`EFF.T5.09`).

The rung-2 law itself, `(WF-law₂)`, is UNCONDITIONAL (`EFF.T5.12`; `𝒲_{≤2}` is D.55's empty
conjunction) and is D.56's row. ⚠ The duplication between D.56 and this row is deliberate and
blueprint-sanctioned: D.56 is the *law's* supplier record, this is the *`w`-site's*. They are
one source, quoted twice, not two sources.

## Row 2 — `i ≥ 3`: GENTOW5 S11.2's PROVED fixed-unit list, routed AROUND `𝒲_{≤i}`

Transcribed (`EFF.T5.09`, `EFF.T5.16`): *"the `s = 1` grade of that family is exactly the base
ladder read … A fixed `K_iˣ`-value is in particular nonzero"* — and the routing matters: the
nonvanishing supplier sits *"on S11.2's PROVED side of the fence, while the single-`w`
geometric law itself stays behind `𝒲_{≤i}`"*. So the `w`-site obligation at depth is met
WITHOUT `𝒲_{≤i}`; the law is not.

**⚠ The fence with teeth** (`EFF.T5.16`), verbatim:

> "Per-grade fixedness alone does not prove (WF-law). In particular, this note does not revive
> S11.2's withdrawn "w-blind" argument."

**A D/E/C node deriving `GentowW` from per-grade fixedness is a DEFECT, not a discharge.** The
same fence in T3's words (`EFF.T3.23`, carried at D.60): *""w-blind" means invariant after the
single-`w_i` geometric law has been proved. It does not construct that law from an arbitrary
fixed per-grade family."* In Lean terms: `GentowW A q R w` (D.44) may be obtained from a port
family (`gentowW_of_ports`, D.44) or supplied by chapter C; there is no route from "each grade
has *some* unit value" to "one `w` works at every grade", and no chapter-D declaration offers
one.

## Row 3 — `i = 1`: NONE

No supplier, because nothing needs one: **no `i = 1` instance of `(WF-w)`/`(WF-twist)`/
`(WF-psi)` is asserted anywhere** (`EFF.T5.09`). What rides at level 1 instead is S11.3's fixed
`z₁`-letter-power statement, which is D.59's `ω₁`: the `(WF-index)` carrier's `j = 2` leg is
scoped to `ω₁`'s OWN letter-power form — *"NOT via (C3-ladder-nonvanishing) applied to a
displayed `w₁`. Its identification with `w₁` is exactly WFRAME OPEN-2; the `i = 1` display stays
open with it"*. `ω₁ = w₁?` is therefore **OPEN**, and it is chapter I's ledger row, not a
chapter-D question (D.64 routes it; D.59 fences it). The outer `ψ₁` leg is separately governed
and UNNAMED (T3 §8 deferred obligation 2).

## Row 4 — the two-clause gate staleness (`HYP.99`, D-H6): disclosed and TYPED AWAY, not repaired

T5 pins T1 at r1–r10 and carries a ONE-clause gate, `(C3-ladder-nonvanishing)` (`w_i` is
nonzero). T1 HEAD (r12) makes the gate **two-clause**: `(C3-read-codomain)` places `w_i ∈ K_i`,
`(C3-ladder-nonvanishing)` makes it nonzero (`EFF.T5.09`'s staleness flag).

The Lean side types `w : Kˣ` — D.29's `ReadBundle.w` field, and hence D.44's `GentowW` and every
display downstream — which carries **BOTH clauses by construction**. That is the honest
strengthening direction: an instance must supply both, nothing is weakened, and no clause of
this gate ever appears as a `w ≠ 0` side condition anywhere in chapter D. The disclosure is the
point; the staleness itself is a **note-owner repair** (`EFF-T5` §8 item 2 = T5 OPEN-CALL 1) and
is **NOT executed here** — D.64 routes it, §12 records the disposition.

## Row 5 — the avatar fence (`EFF.T5.07`, `HYP.66`)

Transcribed verbatim:

> "«Cross-frame» means that `w_i` converts the multiplicative residual frame to the canonical
> residual frame. It does not identify `w_i` with a separately normalized uniformizer avatar."

**Live counterexample LW3** (`EFF.T5.28`): `w_av = 2 ≠ w₃ = 1` — the avatar and the ladder unit
genuinely differ at a realized frame, so the identification is not a harmless abuse of notation.
No chapter-D node mentions an avatar (`varpiSection`, D.19's sibling section `k ↦ ϖ^k`, is a
`NormSection` and not a claim about `w`); the fence exists for C/E consumers of D.29's `w`, and
the LW3 regression is retained in §12's signed rows.

## Reading notes

1. **Nothing in this record is discharged by chapter D.** Rows 1–2 are `[supplied-by: chapter
   C]`; row 3 is an OPEN identification routed to chapter I; row 4 is a note-owner repair; row 5
   is a fence on consumers. A fleet agent who finds a chapter-D node that appears to prove one
   of these rows has found a defect.
2. **The `𝒲_{≤i}` stack and the `(H-VARTHETA-RES)_i` stack are different stacks** (`EFF.T5.10`:
   "a SECOND conditional stack on the same displays and must not be conflated with `𝒲_{≤i}`").
   Row 2's routing is about the `w`-site obligation only; it says nothing about the HVR stack,
   whose carrier is D.62 at the A-D.2 / DECISION D-2 **re-signed sitewise** form (the pre-A-D.2
   existential form is VOID, defect D-D12) and whose assembled `∧` with `𝒲_{≤i}` is D.63.
3. **The non-discharge discipline of D.55 is in force here too** (`EFF.T5.29`, `HYP.63`, CARRY):
   nothing on this page discharges a `𝒲` conjunct, and row 2's "routed AROUND `𝒲_{≤i}`" is
   precisely a statement that the nonvanishing supplier does **not** touch the cumulative
   hypothesis — not that the hypothesis is met.

**DEPENDS.** D.29 (the `w : Kˣ` field the gate is typed into), D.44 (`GentowW`, the law rows 1–2
supply), D.55 (`Wle`, the hypothesis row 2 is routed around) · `EFF.GENTOW2.34/.43
[supplied-by: chapter C]` · `EFF.GENTOW5 [supplied-by: chapter C]` (the S11.2/S11.3 spans).
⚠ These are the node's *reading* dependencies: the file imports nothing, precisely so that the
record cannot be mistaken for a Lean derivation of anything it cites.

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T5.09` (the carry, the three supplier rows, the staleness flag, the `ω₁`
scoping), `EFF.T5.10` (the HVR stack fence), `EFF.T5.16` (the per-grade-fixedness fence and the
withdrawn "w-blind" argument), `EFF.T5.07` and `EFF.T5.28` (the avatar fence and LW3),
`HYP.63`/`HYP.66`/`HYP.99`/`HYP.100`.

**TEETH.** T5 §7 Pass 1(1)/(2)/(5)/(6), Pass 2(3)/(6) → §12 (the signed rows plus the retained
LW3 regression). The structural edges the ledger interface emits from this node are
`BP.D.61 → HYP.66` (the avatar fence) and `BP.D.61 → HYP.99` (the two-clause staleness) — both
DISCLOSURES, never discharges.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
