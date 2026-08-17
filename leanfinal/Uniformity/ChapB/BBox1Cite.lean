/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.BBox1CiteStatement

/-!
# Uniformity.ChapB.BBox1Cite — the B-BOX-1 composite cite, DECLARED (gate-(b))

**The FOURTH landed literature-cite axiom.** `BBox1CiteStatement` — the signable `Prop`
pinned and machine-typed by OM-5's `BBox1CiteStatement.lean` (which also proves the wiring
`typeOf_leaf_of_cite`: this statement discharges B.61's carried `hBOX` at the
irreducible-residual leaf) — is here declared true by citation.

## Faithfulness entry (the composite, every ingredient named — OM-5 §3.2/§5)

* **Core (A), Montes literature at COVERS-ALL-O scope**: [FGMN] *J. Algebra* **427** (2015)
  30–75, **Thm 6.6**, and [GN15] **Thm 2.3 & eq. (2.1)** — the leaf dichotomy's `(e,f)`
  clause; the same source pair and scope verdict as the landed `exists_slope_factorization`
  (B.42), per `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`. ([GMN] Thm 1.19 + Cor 1.20 is the
  ℚ_p-scope display of the same content.)
* **Glue (B)/(C), classical valuation theory — NOT Montes-specific**: the unramified
  residue-degree bookkeeping connecting the Montes data to the order-level gcd; standard
  references **Serre, *Corps Locaux*, Ch. II** (unramified extensions and residue fields)
  and Neukirch, *Algebraic Number Theory*, Ch. II. Citable under the owner's category
  extension of 2026-08-17 ("Feel free to cite Serre's Corps Locaux or any other well
  established literature").
* **Leg (D)**: mathlib-tier, absorbed (mathlib-checkable content, no citation weight).
* **Statement locus.** The axiom is stated in landed vocabulary (`inertiaDegOf` + the
  order-level gcd) because the field-level statement is not typeable in this tree (no
  carrier — CHAP-I I.21); OM-5 §3.1 PROVED the box's region lies entirely off the
  monogenic-maximal locus, so no in-tree shortcut exists (the in-repo alternative is the
  B.62 norm-bridge unit, deliberately not taken per the owner's category extension).
* **Signature.** Owner: the 2026-08-17 category extension + the ratification-by-compile
  ruling (PROJECT_STATE append #84); the mechanical acceptance check is the chapter-I
  `#axiom_core`/`#axiom_reg` guards.

## Non-vacuity / consistency

* `verification/om5_bbox1_cert.gp`: **128 checks, 0 failures** — the leaf `(e,f) = (ℓ, m·d)`
  and `inertiaDegOf = m·d` at `d ≥ 2`, both primes, both characteristics, incl. the
  A-F.7-widened `ℓ = 1` region and wild `p ∣ ℓ` rows.
* The `hirr` hypothesis is NECESSARY (the multiplicity-`≥ 2` defeat `(x²−p)²` in the same
  battery), so the statement is fenced exactly where the sources are.
* The statement TYPES against the landed layer (its own module elaborates it), and its
  hypotheses are inhabited at the battery instances — not vacuously true.

Downstream: `typeOf_leaf_of_cite` now fires unconditionally; every consumer's
`#print axioms` shows `bBox1_cite` (the H-14 inheritance pattern). The strict-sweep
allowlist grows to `{exists_slope_factorization, fgmn_residual_mul, agnprw_termination,
bBox1_cite}` + Lean core.
-/

namespace Uniformity.Density.Leaf

/-- **B-BOX-1 `[cite:FGMN+GN15; Serre/Neukirch glue]` (gate (b), composite).** The signable
statement pinned by `BBox1CiteStatement.lean`, declared true by citation; the full composite
faithfulness entry is the module docstring. -/
axiom bBox1_cite : BBox1CiteStatement

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.bBox1_cite
end AxCheck
