/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B29
import Uniformity.ChapB.B34

/-!
# Uniformity.ChapB.B37 — graded coprimality at a slope

**Chapter B, NODE B.37** [def] (`blueprint/CHAP-B_leaf_layer.md` §6, the two dissections),
ENV-C. One signed declaration, definitional.

*Graded coprimality at a slope.* Fix an order-1 key `φ`, `0 < ℓ`, `Nat.Coprime u ℓ`, and monic
`g, h` that are `(u,ℓ)`-pure (B.34) with heights `H_g, H_h` at abscissa `0`. The pair is
**`(u,ℓ)`-coprime** when the two residual polynomials are coprime in `(resField φ)[Y]`:
`IsCoprime (resPoly π φ g u ℓ _ H_g) (resPoly π φ h u ℓ _ H_h)`.

This is the hypothesis the graded successive-approximation engine of B.38–B.43 runs on — the
graded analogue of the landed Hensel engine's `IsCoprime g₀ h₀` on residue-field reductions
(`leanfinal/Uniformity/HenselFactorization.lean:393`), with the residue field `k` replaced by
`resField φ` and the reductions `g₀, h₀` by the residual polynomials of the common side.

Three shape choices, all forced by the API this predicate has to feed:

* **The heights and the `Nonempty` witnesses are existentially bound, not parameters.** B.29's
  `resPoly π φ g u ℓ h H₀` takes a proof `h : (sideSet φ g u ℓ).Nonempty` (B.18 supplies it) and
  a natural number `H₀` (the height at the side's left endpoint). Neither is determined by
  `π, φ, u, ℓ, g, h` *syntactically*, so a predicate with them free would not be a property of
  the pair. Both are in fact determined *semantically* — `H_g` by the clause
  `npHgt φ g 0 = (Hg : ℕ∞)` (an `ℕ∞` value has at most one `ℕ` preimage) and the witness by
  proof irrelevance — so the existential quantifier loses nothing and the consumer recovers the
  data by `obtain`.
* **Purity is part of the predicate**, not a side hypothesis: the residual polynomial of a
  non-pure `g` reads only the abscissa window `sideMin … sideMax`, and coprimality there says
  nothing about the factorization of `g` itself. B.34's `IsPure` is what makes the side the whole
  polygon, hence the residual polynomial the whole residual datum.
* **The height clause is stated at abscissa `0`, not at `sideMin φ g u ℓ hg'`.** Under `IsPure`
  the two agree (`OnSide … 0` puts `0` in `sideSet`, so `sideMin = 0`); abscissa `0` is the form
  the callers have (B.35's `hHf`/`hHg`, B.41's `hH₀`) and the form B.30's `resCoeff_eq_zero_iff`
  is instantiated at downstream.

DEPENDS: B.16 (`sideSet`) · B.18 (the `Nonempty` witnesses this quantifies over) · B.20
(`sideDeg`, inside `resPoly`) · B.29 (`resPoly`) · B.34 (`IsPure`); `npHgt` is B.11. Only B.29 and
B.34 are imported — they carry the rest.

**PROOF.** Definitional. Environment ENV-C (blueprint §0.1) = ENV-A + `[IsAdicComplete
(maximalIdeal O) O]` + `[Finite (ResidueField O)]`; neither instance is consumed by the
statement, so Lean's use-driven variable inclusion trims both and the elaborated signature is
`GradedCoprime : O → Polynomial O → ℕ → ℕ → Polynomial O → Polynomial O → Prop`, byte-identical
to the gate-verified `leanspec/Leanspec/ChapB.lean:614` stub. The ENV-C block is entered anyway,
so the environment matches the blueprint's declared one (the B.49/B.53c precedent).

## Faithfulness

The graded analogue of the landed engine's hypothesis `IsCoprime g₀ h₀` on residue-field
reductions (`HenselFactorization.lean:393`). The corpus's corresponding hypotheses are
`EFF.HE3.32`'s "`R_λ = Π_r r^{m_r}` (`r` irreducible over `K`)" — the factors of a residual that
is squarefree at `r` are pairwise coprime — and `docs/GMN_citations.md` Thm 1.19's
"pairwise-distinct monic irreducibles in `F_φ[y]`". Coprimality in `(resField φ)[Y]`, a PID, is
equivalent to having no common irreducible factor, which is that hypothesis verbatim.
**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

SOURCE: `docs/GMN_citations.md` Thm 1.15, Thm 1.19; `EFF.HE3.32`.

**TEETH.** Signed non-applicable (a definition).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Neither instance is
-- consumed by the statement; both are kept so the environment matches the blueprint's declared
-- ENV-C (the B.49/B.53c precedent), and Lean's use-driven inclusion trims them.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.37 — graded coprimality at a slope.** `GradedCoprime π φ u ℓ g h` : `g` and `h` are
`(u,ℓ)`-pure with coprime residual polynomials in `(resField φ)[Y]`. The heights at abscissa `0`
and the `Nonempty` witnesses B.29 needs are existentially bound; both are determined by the data
(the height by the `npHgt` clause, the witness by proof irrelevance). -/
def GradedCoprime (π : O) (φ : Polynomial O) (u ℓ : ℕ) (g h : Polynomial O) : Prop :=
  ∃ (Hg Hh : ℕ) (hg' : (sideSet φ g u ℓ).Nonempty) (hh' : (sideSet φ h u ℓ).Nonempty),
    npHgt φ g 0 = (Hg : ℕ∞) ∧ npHgt φ h 0 = (Hh : ℕ∞) ∧
    IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧
    IsCoprime (resPoly π φ g u ℓ hg' Hg) (resPoly π φ h u ℓ hh' Hh)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.GradedCoprime
end AxCheck
