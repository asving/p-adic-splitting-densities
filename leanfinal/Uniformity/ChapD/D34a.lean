/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D34a — `wtwist`, the w-twist `(WF-twist)`, and its monic/degree clause

**Chapter D, NODE D.34** [def+lemma] [fresh], micro-node **D.34a**
(`blueprint/CHAP-D_gauge_tchain.md` §5, the read bundle and the B-law; amendments A-1, A-D.1
govern — A-D.1's in-place tag at D.34 is the `(w⁻¹ : K)` spelling repair D-D11). ENV-D3.
The node is **SPLIT MANDATED → 3**: this file carries the definition and the monic/degree/
constant-term clauses; `D34b` carries irreducibility, separability and the root map; `D34c`
carries the factor-multiset correspondence (multiplicativity on monics).

*The w-twist and its transport package.* For a unit `w : Kˣ` and a polynomial `P : K[y]`,

```
wtwist w P := w ^ (deg P) • P(y / w)
```

— the corpus's `P(y) ↦ w^{deg P}·P(y/w)`. Three signed declarations here:

* `wtwist` — the definition, body verbatim from the gate-verified stub.
* `wtwist_monic` — for monic `P`, the twist is monic **and** has the same `natDegree`.
* `wtwist_coeff_zero` — `(wtwist w P).coeff 0 = w^{deg P}·P.coeff 0`, which is the Lean form of
  the corpus's "preserves … a nonzero constant term" clause: the twisted constant term is a
  UNIT MULTIPLE of the original, hence nonzero exactly when the original is.

## The `w⁻¹` spelling (defect D-D11, A-D.1)

The blueprint's `(w⁻¹ : K)` is ambiguous between `((w : K))⁻¹` (the field inverse of the
coercion) and `((w⁻¹ : Kˣ) : K)` (the coercion of the group inverse). The two are equal, and
**A-D.1 signs the `Kˣ`-inverse reading** — it keeps the substituted term unit-valued (no
`field_simp` side goals) and makes D.41 clause 1 definitional. This file lands that reading.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one definition; parent CLAUDE.md trust boundary).
Two recasts against the sources, flagged for the chapter cross-read:

* *the degree scalar is `natDegree`, not `degree`.* The corpus writes `w^{deg P}` for `P` monic
  of degree `f`; the Lean scalar is `(w : K) ^ P.natDegree`, which agrees with it on every
  nonzero `P` and makes `wtwist w 0 = 0` rather than junk. Every consuming clause of this node
  is stated for `P` monic, where the two readings coincide.
* *"preserves a nonzero constant term" is landed as an identity, not as a nonvanishing claim.*
  `wtwist_coeff_zero` gives the exact constant term; the nonvanishing statement the corpus
  words is its immediate corollary (`w` is a unit), and is deliberately NOT a separate signed
  declaration — the signature list of the node has none.

**DEPENDS.** none inside chapter D (mathlib `Polynomial.comp`, `Polynomial.natDegree_comp`,
`Polynomial.leadingCoeff_comp`, `Polynomial.natDegree_C_mul_X` — the blueprint's DEPENDS field
names them "exact names at stub time"). This is one of the chapter's ten immediately fireable
nodes.

**PROOF.** The definition is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
(`LeanspecD.wtwist`) verbatim, with the landed namespace `Uniformity.Density.Gauge` (GC-6.2)
restored. Monic/degree: `natDegree (P.comp (C a * X)) = natDegree P` since `C a * X` has
`natDegree 1` (`a := (w⁻¹ : Kˣ) ≠ 0`), and the leading coefficient of the twist is
`w^f · 1 · (w⁻¹)^f = 1`. Constant term: `coeff 0 = eval 0`, and `(C a * X).eval 0 = 0`.

SOURCE: `EFF.T1.15` (the transport sentence: "The map `P(y) ↦ w^{deg P}P(y/w)` transports
factorizations bijectively and preserves degrees, multiplicities, irreducibility, and a nonzero
constant term"); `EFF.T3.18` (`(T3-ROUTE)`); `EFF.T5.05` (`(WF-twist)` — the same display);
`EFF.T5.08` ("Unit substitution preserves monicity, degree, irreducibility, nonzero constant
term, and irreducible-factor degrees and multiplicities"; its gate `(C3-ladder-nonvanishing)` is
carried here BY TYPE — the argument is `w : Kˣ`, not `w : K`).

**TEETH.** T3 §8.3(2) (HETOW clause (d): "separability/factor/root routing … fully supplied by
`(T3-ROUTE)`") → Lean theorem, at this node and at `D34b`/`D34c`; T5 §7 Pass 1(1) → §12.
**Honesty fence, repeated here per the node's own instruction (D-H4(3)):** "Turning factor data
into a p-adic splitting type still requires the surrounding tower theorem" (`EFF.T5.08`) — that
theorem is unnamed in both T1 and T3 and is routed to chapter I / the 0d trust boundary (node
D.64). Nothing in this file converts factor data into a splitting type.

ENVIRONMENT: ENV-D3 (the residue-field arena: a bare `[Field K]`, no finiteness — nothing here
counts).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open Polynomial

/-- **D.34** The w-twist `(WF-twist)`: `P(y) ↦ w^{deg P}·P(y/w)` (`EFF.T1.15`, `EFF.T3.18`,
`EFF.T5.05`).  The substituted scalar is the `Kˣ`-inverse `((w⁻¹ : Kˣ) : K)`, per A-D.1's
signed reading of defect D-D11. -/
noncomputable def wtwist {K : Type*} [Field K] (w : Kˣ) (P : Polynomial K) : Polynomial K :=
  (w : K) ^ P.natDegree • P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)

section Twist

variable {K : Type*} [Field K]

/-- The substitution polynomial `C w⁻¹ * X` has degree one — the fact that makes
`natDegree_comp` collapse. -/
private theorem natDegree_C_inv_mul_X (w : Kˣ) :
    (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X).natDegree = 1 :=
  Polynomial.natDegree_C_mul_X _ (Units.ne_zero _)

/-- Composition with `C w⁻¹ * X` does not move `natDegree`. -/
private theorem natDegree_comp_twist (w : Kˣ) (P : Polynomial K) :
    (P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_C_inv_mul_X, mul_one]

/-- **D.34a** The twist is monic of the same degree (`EFF.T5.08`: unit substitution preserves
monicity and degree). -/
theorem wtwist_monic (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    (wtwist w P).Monic ∧ (wtwist w P).natDegree = P.natDegree := by
  have hne : ((w : K)) ^ P.natDegree ≠ 0 := pow_ne_zero _ (Units.ne_zero w)
  have hlc : (P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)).leadingCoeff
      = ((w⁻¹ : Kˣ) : K) ^ P.natDegree := by
    rw [Polynomial.leadingCoeff_comp (by rw [natDegree_C_inv_mul_X]; exact one_ne_zero),
      hP.leadingCoeff, one_mul]
    congr 1
    simp
  refine ⟨?_, ?_⟩
  · rw [Polynomial.Monic.def, wtwist, Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, hlc, ← mul_pow]
    simp
  · rw [wtwist, Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hne, natDegree_comp_twist]

/-- **D.34a** The constant-term clause: the twist multiplies `coeff 0` by the unit `w^{deg P}`
(`EFF.T1.15`: "preserves … a nonzero constant term"). -/
theorem wtwist_coeff_zero (w : Kˣ) (P : Polynomial K) :
    (wtwist w P).coeff 0 = (w : K) ^ P.natDegree * P.coeff 0 := by
  rw [wtwist, Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, Polynomial.coeff_zero_eq_eval_zero]
  simp

end Twist

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wtwist
#print axioms Uniformity.Density.Gauge.wtwist_monic
#print axioms Uniformity.Density.Gauge.wtwist_coeff_zero

end AxCheck
