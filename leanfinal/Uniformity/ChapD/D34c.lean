/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D34a

/-!
# Uniformity.ChapD.D34c — the factor-multiset correspondence: `wtwist` is multiplicative on monics

**Chapter D, NODE D.34** [def+lemma] [fresh], micro-node **D.34c**
(`blueprint/CHAP-D_gauge_tchain.md` §5; amendments A-1, A-D.1 govern). ENV-D3. The last third
of the **SPLIT MANDATED → 3** transport package of `wtwist` (D.34a):

* `wtwist_mul` — `wtwist w (P * Q) = wtwist w P * wtwist w Q` for monic `P`, `Q`.

## Why this is the factor-multiset clause

The corpus sentence is "the map `P(y) ↦ w^{deg P}P(y/w)` transports factorizations bijectively
and preserves degrees, multiplicities, irreducibility" (`EFF.T1.15`), and `EFF.T5.08`'s
"preserves … irreducible-factor degrees and multiplicities". Multiplicativity IS that clause in
its usable form: given a monic factorization `P = ∏ Pᵢ^{mᵢ}`, `wtwist_mul` (with D.34a's
`wtwist_monic`, which keeps every partial product monic, and D.34b's `wtwist_irreducible`)
pushes the twist through the product factor by factor, so the twisted factorization has the
same multiset of exponents and — by D.34a's degree clause — the same multiset of factor
degrees. The blueprint's own SIGNATURE names this micro-node exactly
"the factor-multiset correspondence `wtwist w (P*Q) = wtwist w P * wtwist w Q` for monic P Q".

**The monicity hypotheses are load-bearing here**, unlike at D.34b: the proof needs
`natDegree (P*Q) = natDegree P + natDegree Q` to split the normalizing scalar
`w^{deg(PQ)} = w^{deg P}·w^{deg Q}`, which is the blueprint's PROOF note "the monic
renormalization `w^{deg P}` is multiplicative BECAUSE degrees add". Over a field the additivity
also holds for any two nonzero polynomials, but the signed statement is the monic one and it is
landed as signed.

## Faithfulness

*One recast, flagged for the cross-read.* The corpus states a bijection of factorizations; the
Lean form is the multiplicativity identity on monic pairs. The bijection is the identity plus
the D.34b package (irreducibility both ways) plus D.34a (degrees, monicity) — no single signed
declaration of this chapter states the bijection itself, exactly as the blueprint's split
prescribes. Whoever consumes "transports factorizations bijectively" must assemble it from the
three micro-nodes; nothing here asserts it as a black box.

**DEPENDS.** D.34a (`wtwist`); mathlib `Polynomial.Monic.natDegree_mul`, `Polynomial.mul_comp`,
`Polynomial.smul_eq_C_mul`.

**PROOF.** `natDegree (P*Q) = natDegree P + natDegree Q` (monic), `(P*Q).comp r = P.comp r *
Q.comp r`, then `pow_add` and `ring` on the scalars written as `C`-multiplications.

SOURCE: `EFF.T1.15` (the transport sentence), `EFF.T3.18` (`(T3-ROUTE)`: "the monic factor
correspondence `r(Z) = δ^m r̂(Z/δ)`"), `EFF.T5.08` ("irreducible-factor degrees and
multiplicities").

**TEETH.** T3 §8.3(2) → Lean theorem, here and at D.34a/D.34b. **Honesty fence (D-H4(3)):**
"Turning factor data into a p-adic splitting type still requires the surrounding tower theorem"
(`EFF.T5.08`) — routed to chapter I / the 0d trust boundary (D.64), not proved anywhere in
chapter D.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open Polynomial

section Twist

variable {K : Type*} [Field K]

/-- **D.34c** The factor-multiset correspondence: the twist is multiplicative on monics
(`EFF.T1.15`, `EFF.T3.18`, `EFF.T5.08`).  The monic renormalization `w^{deg P}` is
multiplicative because degrees add. -/
theorem wtwist_mul (w : Kˣ) {P Q : Polynomial K} (hP : P.Monic) (hQ : Q.Monic) :
    wtwist w (P * Q) = wtwist w P * wtwist w Q := by
  rw [wtwist, wtwist, wtwist, hP.natDegree_mul hQ, Polynomial.mul_comp, pow_add,
    Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul,
    Polynomial.C_mul]
  ring

end Twist

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wtwist_mul

end AxCheck
