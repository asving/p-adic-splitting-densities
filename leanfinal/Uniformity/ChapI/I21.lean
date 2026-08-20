/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapI.I21 — `TypeOfFaithful`, THE TRUST BOUNDARY NAMED — **STATEMENT CARRIER**

**Chapter I, NODE I.21** [def] [fresh] (`blueprint/CHAP-I_capstone_conditionality.md` §7,
`### NODE I.21`; SIGNED twin `leanspec/Leanspec/ChapI.lean`, the `### NODE I.21` block,
lines 1076–1098).  **ENV-I1**.  Statement transcribed BYTE-FROZEN; re-namespaced only (GC-6.2).
Ledger `HYP.01` [CORE-SET] + `HYP.105`; GC-3's kept-apart rule.

## ⚠ DISPOSITION — READ THIS FIRST

`TypeOfFaithful` is a **statement carrier** (A-C.8.5) at its **STUB-STAGE SIGNED BODY**, the
literal placeholder `True`.  Nothing is asserted, nothing is proved.  No axiom declared, no cite
imported, no capstone statement asserted.

**THIS IS THE NODE THAT NAMES THE PROJECT'S TRUST BOUNDARY**, so what it does *not* do matters
more here than anywhere else in the chapter.  GC-3's KEPT-APART rule: **no chapter may silently
identify the gcd-engine `typeOf` API with the ideal-theoretic `(e, f)` API.**  A node needing that
identification must hypothesize THIS name or return `BLOCKED: HYP.01`.  Landing the carrier is
what makes the hypothesize-or-block choice expressible; it is **not** a step toward the
identification.

**BLOCKED-UNTIL-RESOLUTION (blueprint defect I-D12), AND STILL BLOCKED AT HEAD — with a sharpened
reason.**  Typing the body needs the **factor-field valuation-ring carrier**, the object B.56's
OPTIONAL repair route would build, and **it does not exist in the tree**.  OM-5 §3.1 sharpens
why this is structural rather than merely unbuilt: at every `d ≥ 2` leaf the order
`AdjoinRoot g` has residue field of degree `m < m·d`, hence **is never a DVR**, so that whole
region lies entirely OFF the monogenic-maximal locus that the landed
`Uniformity/Density/TypeOfFaithful.lean` reaches.  What IS landed there is HYP.01 on the
monogenic-maximal locus (`typeOf_eq_classical_of_isDiscreteValuationRing`,
`inertiaDegOf_eq_inertiaDeg'`, `ramIndexOf_eq_ramificationIdx'`), plus the hypothesis-free inert
leaf in `Density/TypeOfFaithfulInert.lean` — verified by `rg` at this commit.  **Neither reaches
the `d ≥ 2` region, and neither is this carrier.**

**Terminal fate, per Part V's two terminals:** a future discharge node OR a gate-(b) cite.
Explicitly open today.  **Audit row A-1 is the human leg** (I.22's ledger: *"`typeOf`
faithfulness — review I.21's statement against the classical `(e,f)` multiset; gate-(b)-adjacent,
human; **before any node hypothesizes `TypeOfFaithful`**"*).  That ordering is a real
precondition: **the first consumer to hypothesize this name triggers A-1**, and A-1 has not run.

## MANDATORY BINDER-VACUITY AUDIT (A-C.8.4; verdict committed before any proving)

**Verdict: NO BINDERS AT ALL · CONTENT-FREE CONCLUSION (signed placeholder, I-D12) · and the
frozen content is carried in the DOCSTRING, not the type — the sharpest disclosure in the
chapter.**

**(1) There are no hypotheses to audit.**  The signature is `TypeOfFaithful : Prop` — no degree
index, no instance bundle, no guard, no implication.  None of the four A-C.7 registry shapes
(C.111 unpinned field, C.94 self-loop, C.113 `Nonempty`-only, C.118 guarded `≠ ⊤`) can be
present.  Unlike I.05/I.06/I.07 there is not even an unused index.

**(2) The carrier as signed is PROVABLE and asserts NOTHING.**  `TypeOfFaithful` is `True`,
closed by `trivial`.  A consumer hypothesizing it has discharged NOTHING.

**(3) THE HAZARD SPECIFIC TO THIS NODE, stated plainly.**  Because the `Prop` is `True`, a
consumer could *prove* an obligation "under `TypeOfFaithful`" and the resulting theorem would be
unconditionally true — i.e. **the trust boundary is currently a boundary in name only, and
hypothesizing it neither costs nor buys anything.**  That is exactly the state the signature
freezes and discloses; it is why audit A-1 is ordered *before* any consumer, and why GC-3 makes
the alternative (`BLOCKED: HYP.01`) equally admissible.  I record it as the load-bearing finding
of I.21: **anyone reading a downstream theorem whose hypothesis list contains `TypeOfFaithful`
must read that hypothesis as vacuous until the body lands.**

**(4) WHAT IS FROZEN is the docstring's content, not the type.**  FROZEN HERE: **the name, the
locus (`disc ≠ 0`), and both APIs by name** — `typeOf`'s gcd multiset over the ORDER
`AdjoinRoot g`, versus the ideal-theoretic `(e, f)` multiset over the maximal order/DVR, in the
primed rank-form generation (`Ideal.ramificationIdx'` / `inertiaDeg'`), with `HYP.12`'s
ordering/normalization convention.  Since none of that is in the type, **the docstring is the
contract** and editing it is a signature change.

## Definitional choices made here (flagged for human review — this node most of all)

1. **Namespace** `Uniformity.Density`, flat (GC-6.2).  ⚠ **NAME/MODULE COINCIDENCE, deliberate
   and checked:** the constant `Uniformity.Density.TypeOfFaithful` shares its full name with the
   landed *module* `Uniformity/Density/TypeOfFaithful.lean`.  `rg` confirms no *declaration* of
   that name exists anywhere in `leanfinal/Uniformity/` (only the module and a docstring
   reference), so there is no clash; but a human should know the two are different objects and
   that the module does **not** prove the carrier.  The name is the signed one and I did not
   change it.
2. **Import** `Uniformity.Density.LocalData` only.  I deliberately did **not** import
   `Uniformity.Density.TypeOfFaithful`: the body needs no repo object, and importing the landed
   monogenic-maximal file next to this carrier would invite exactly the conflation GC-3 forbids.
3. **No gate.**  A `True`-bodied carrier has no non-vacuity content, and this is the one node
   where dressing a triviality as a certificate would be actively dangerous.
4. **No `set_option`** is needed (unlike I.05/I.06/I.07): there is no unused binder.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

-- The signed body is the bare `True` placeholder (the node is BLOCKED-UNTIL-RESOLUTION);
-- nothing about the two APIs is asserted, which is the point of GC-3's KEPT-APART rule.
/-- **THE TRUST BOUNDARY, NAMED** (ledger HYP.01 [CORE-SET] + HYP.105; GC-3's kept-apart rule):
`typeOf`'s gcd multiset (over the ORDER `AdjoinRoot g`) agrees on the `disc ≠ 0` locus with the
ideal-theoretic `(e, f)` multiset (over the maximal order/DVR), in the primed rank-form
generation. **NO chapter may silently identify the two APIs** (GC-3); a node needing the
identification hypothesizes THIS name or returns `BLOCKED: HYP.01`.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the bundle and monic
`f` with `disc f ≠ 0`, and equates `(typeOf f).data` with the maximal-order multiset via
`Ideal.ramificationIdx'`/`inertiaDeg'`. FROZEN HERE: name, locus, both APIs by name. -/
def TypeOfFaithful : Prop :=
  True

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.TypeOfFaithful
