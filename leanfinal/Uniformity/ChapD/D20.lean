/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D07

/-!
# Uniformity.ChapD.D20 — `(C1-general)`, the letter factorization

**Chapter D, NODE D.20** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1, A-D.2 govern — this node's SIGNATURE is unamended).
ENV-D2 + ENV-D3. One signed declaration.

*`(C1-general)`: the letter factorization.* In any gauge arena `A` over `(G, K, N)`, for
`a b c : G` of EQUAL height (`A.v a = A.v b = A.v c`), the three value-zero ratios

* `z  := res (a · c⁻¹)`,
* `η' := res (a · b⁻¹)`,
* `ρ  := res (b · c⁻¹)`

satisfy `z = η' · ρ`. Instantiated at `a := Φ_i^{e_{i+1}}`, `b := n̂_i(u_{i+1})`,
`c := π_{i+1}^{u_{i+1}}` — all of height `u_{i+1}` by `EFF.T1.02`'s stage typing — this is the
corpus's `z_{i+1} = η_{i+1}·ρ_i` (`EFF.T1.05`).

## The fence IS the tooth (transcribed, not softened)

Two corpus fences are transcribed here as the *absence* of any further declaration, and any
consumer that reads more out of this node than it states has committed the defect the R2-1
withdrawal killed:

1. **"No arbitrary-depth canonical-letter monomial assertion follows from the T1 carrier."**
   This lemma is three applications of `map_mul` on a residue homomorphism. It says nothing
   about whether the letters at depth `i` are monomials in `z₁, …, z_i`.
2. **`(C1-JA-specialization)`** — the specialization `ρ_i = J_i(z₁,…,z_i)` — requires the
   external `(H-JA-CONJ)_i`, which is an INLINE hypothesis of any consumer (honesty item
   D-H10). It is **not stated and not proved here**, and no `axiom` stands in for it.

T1 §7 attack 1 has no dedicated battery row for this node precisely because the fence, not a
numeric table, is what guards it (§12 carries the signed row).

## Faithfulness

The three membership side conditions are discharged by the private helper `mem_ker_of_v_eq`
(`A.v x = A.v y → x·y⁻¹ ∈ ker A.v`, one `map_mul`/`map_inv` step), spelled as explicit
arguments of the subtype anonymous constructors rather than left as tactic holes, per the
blueprint SIGNATURE's rider. The helper is private to this file because chapter D's shared
kernel-membership API is D.08's (`GaugeArena.mem_ker_div`), which this node does not depend on
— the blueprint's DEPENDS row for D.20 is D.07 alone, and the two proof terms are
propositionally (indeed definitionally, by proof irrelevance) interchangeable at every call
site.

DEPENDS: D.07 (`GaugeArena`, landed at `Uniformity.ChapD.D07`; `NormSection` reaches this file
through it) · mathlib `MonoidHom.ker`, `MonoidHom.mem_ker`, `map_mul`, `map_inv`. No other
landed node.

**PROOF.** `a·c⁻¹ = (a·b⁻¹)·(b·c⁻¹)` in a commutative group (`group`), and `res` is a
homomorphism on `ker v`, so `map_mul` closes it after `Subtype.ext`. This is `EFF.T1.05`
verbatim: "the three defining fractions have value zero, and residue multiplicativity gives
`z_{i+1} = η_{i+1}ρ_i`".

SOURCE: `EFF.T1.05` (the boxed `(C1-general)`, the R2-1 fence, and `(C1-JA-specialization)`);
`EFF.T1.04` (the definitions of `η_{i+1}`, `z_{i+1}`, and `z₁ := η`).

**TEETH.** T1 §7 attack 1 — no dedicated battery row; the fence above IS the tooth (a consumer
deriving depth-monomiality from this node alone is the defect the R2-1 withdrawal killed) →
§12 signed row.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written
inline per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- Kernel membership of a ratio of equal-height elements: one `map_mul`/`map_inv` step.
Private — chapter D's shared form of this fact is D.08's `GaugeArena.mem_ker_div`, on which
D.20 does not depend (blueprint DEPENDS: D.07 alone); the two proof terms are definitionally
interchangeable by proof irrelevance. -/
private theorem mem_ker_of_v_eq {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) {x y : G} (hxy : A.v x = A.v y) :
    x * y⁻¹ ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]

/-- **D.20 — `(C1-general)`, the letter factorization** (`EFF.T1.05`).  For three elements of
equal height, the residue of the outer ratio is the product of the residues of the two inner
ratios: at the stage triple `(Φ_i^{e_{i+1}}, n̂_i(u_{i+1}), π_{i+1}^{u_{i+1}})` this is
`z_{i+1} = η_{i+1}·ρ_i`.

⚠ **FENCE (R2-1, transcribed).** No arbitrary-depth canonical-letter monomial assertion
follows from this; the specialization `ρ_i = J_i(z₁,…,z_i)` `(C1-JA-specialization)` requires
the external `(H-JA-CONJ)_i`, an inline hypothesis of any consumer (D-H10), never stated or
proved here. -/
theorem GaugeArena.res_ratio_factor {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (a b c : G) (hab : A.v a = A.v b) (hbc : A.v b = A.v c) :
    A.res ⟨a * c⁻¹, mem_ker_of_v_eq A (hab.trans hbc)⟩
      = A.res ⟨a * b⁻¹, mem_ker_of_v_eq A hab⟩ * A.res ⟨b * c⁻¹, mem_ker_of_v_eq A hbc⟩ := by
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show a * c⁻¹ = a * b⁻¹ * (b * c⁻¹)
  group

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.res_ratio_factor

end AxCheck
