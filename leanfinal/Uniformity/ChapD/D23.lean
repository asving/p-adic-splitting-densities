/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Group.Embedding

/-!
# Uniformity.ChapD.D23 — `(C4-support)`: support transport under the JA conjugation

**Chapter D, NODE D.23** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4; amendments A-1
and A-D.1 govern — neither touches this node, so the SIGNATURE below is the one signed at
composition and re-stubbed at stage 0e in `leanspec/Leanspec/ChapD.lean`). ENV-D3 — the
residue-field arena: a bare field `K`, polynomials over it, nothing counted and no valuation.
One signed declaration.

*`(C4-support)`: support transport under the JA conjugation.* Let `K` be a field and
`H P Q : K[y]` nonzero with — **the inline hypothesis `(H-JA-RES-CONJ)`, exactly the corpus's
supplier interface, never proved here** — `H = y^ν * Q` and `P = C a * Q.comp (C b * y)` for
units `a b : Kˣ`. Then `H.support = ν + P.support` (elementwise shift of the `Finset`, written
as `Finset.map (addLeftEmbedding ν)`) and `H.natDegree = P.natDegree + ν`.

**The two C4 clauses are deliberately separate nodes with separate hypotheses.** "Neither the
polynomial identities nor their support consequences follow from `(C4-origin)` alone": D.22
carries `(C4-origin)` (the exponent identity `t_Def = ν − t_min` and its root-of-unity
criterion) and says nothing about supports; this node carries the support/degree transport and
consumes `(H-JA-RES-CONJ)` — the conjugation supplier — as the two INLINE polynomial identities
`hHQ`, `hPQ`. The corpus's T1 OPEN-CALL 2 (the conjugation supplier) routes to exactly these two
binders; nothing in chapter D discharges them.

**The R2-2 fence.** The withdrawn mutation R2-2 was the UNFENCED base support claim — "the
support of `H` transports to that of `P`" with no conjugation hypothesis supplied. That claim is
false (take `Q = y`, `H = y`, `P = y² `: no `a, b, ν` relate them), and it is the explicit
`hHQ`/`hPQ` pair that kills it here.

DEPENDS: mathlib only. The three consumed facts, as they actually exist at the v4.31.0 pin:
`Polynomial.coeff_X_pow_mul'` (the `ite` form of the `X^ν`-shift on coefficients — the blueprint
DEPENDS field names a `Polynomial.support_X_pow_mul`, which **does not exist** in this mathlib,
so the support shift is proved elementwise from the coefficient form), `Polynomial.natDegree_C_mul`,
`Polynomial.natDegree_comp`, `Polynomial.comp_C_mul_X_coeff`, `Polynomial.natDegree_X_pow_mul`.

**PROOF.** "Multiplication by `y^ν` translates support; multiplication by a unit and
substitution by a unit preserve it" (`EFF.T1.17`, verbatim). Concretely, three steps.

1. `Supp P = Supp Q`. Coefficientwise, `P.coeff n = a · (Q.coeff n · bⁿ)` — a unit multiple per
   degree, since `a` and `b` are units of a field — so `P.coeff n ≠ 0 ↔ Q.coeff n ≠ 0`.
2. `Supp H = ν + Supp Q`. `H.coeff n = if ν ≤ n then Q.coeff (n − ν) else 0`, so `n` is in the
   support exactly when `n = ν + m` for some `m ∈ Supp Q`.
3. Degrees add: `natDegree (X^ν * Q) = natDegree Q + ν` (`Q ≠ 0`), and
   `natDegree P = natDegree Q` because `natDegree (Q.comp (C b * X)) = natDegree Q · 1` and
   multiplying by the nonzero constant `a` does not move the degree.

**Redundant signed hypothesis, recorded not repaired.** `hH : H ≠ 0` is not consumed: `H ≠ 0`
already follows from `hQ` and `hHQ` over a domain. Signatures are frozen, so the binder stays
exactly as signed (a redundant antecedent only weakens the lemma's applicability, never its
truth); the `unusedVariables` linter is silenced at the declaration.

SOURCE: `EFF.T1.17` (the boxed `(C4-support)`, the named `(H-JA-RES-CONJ)` hypothesis displayed,
the non-consequence fence — "sole live C4-support after R2-2/R12-5/R13-2").

**TEETH.** T1 §4.2 check 3; §7 attacks 1 and 6 → **Lean theorem** (this node) + §12; the R2-2
withdrawal (the UNFENCED base support claim) is the mutation this node's explicit hypothesis
kills.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

-- `hH : H ≠ 0` is signed but not consumed (it follows from `hQ` and `hHQ`); the frozen
-- signature keeps it verbatim.
set_option linter.unusedVariables false in
/-- **D.23 — `(C4-support)`: support transport under the JA conjugation.** Under the inline
`(H-JA-RES-CONJ)` hypotheses `H = X^ν * Q` and `P = C a * Q.comp (C b * X)` (`a b : Kˣ`), the
support of `H` is the support of `P` shifted up by `ν`, and `H.natDegree = P.natDegree + ν`.
The conjugation identities are supplied, never proved here. -/
theorem c4_support {K : Type*} [Field K] {H P Q : Polynomial K} (hH : H ≠ 0) (hQ : Q ≠ 0)
    (a b : Kˣ) (ν : ℕ)
    (hHQ : H = Polynomial.X ^ ν * Q)
    (hPQ : P = Polynomial.C (a : K) * Q.comp (Polynomial.C (b : K) * Polynomial.X)) :
    H.support = P.support.map (addLeftEmbedding ν)
    ∧ H.natDegree = P.natDegree + ν := by
  -- Step 1: the conjugated polynomial has the same support as `Q` (unit scaling per degree).
  have hsuppP : P.support = Q.support := by
    ext n
    rw [Polynomial.mem_support_iff, Polynomial.mem_support_iff, hPQ,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
    simp [a.ne_zero, b.ne_zero]
  -- Step 3 (degree half): `natDegree P = natDegree Q`.
  have hnatP : P.natDegree = Q.natDegree := by
    rw [hPQ, Polynomial.natDegree_C_mul a.ne_zero, Polynomial.natDegree_comp,
      Polynomial.natDegree_C_mul b.ne_zero, Polynomial.natDegree_X, mul_one]
  refine ⟨?_, ?_⟩
  · -- Step 2: multiplication by `X^ν` translates the support by `ν`.
    rw [hsuppP]
    ext n
    rw [hHQ, Polynomial.mem_support_iff, Polynomial.coeff_X_pow_mul']
    simp only [Finset.mem_map, addLeftEmbedding_apply, Polynomial.mem_support_iff]
    constructor
    · intro h
      by_cases hle : ν ≤ n
      · exact ⟨n - ν, by simpa [hle] using h, by omega⟩
      · simp [hle] at h
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
  · rw [hnatP, hHQ, Polynomial.natDegree_X_pow_mul ν hQ]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.c4_support

end AxCheck
