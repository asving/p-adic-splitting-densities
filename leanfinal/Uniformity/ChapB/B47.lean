/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B25

/-!
# Uniformity.ChapB.B47 — the degree of a residual piece

**Chapter B, NODE B.47** (`blueprint/CHAP-B_leaf_layer.md` §6).  *The degree of a residual
piece.*  In the situation of B.41, if the residual polynomial's factor is `G = ψ ^ a` with `ψ`
monic of degree `d_ψ`, then the corresponding factor `g` has

```
g.natDegree = ℓ * m * a * d_ψ                     (m = φ.natDegree)
```

**This node is deliberately trivial.**  It exists so that the corpus's degree formula is *stated*
once, in the shape every consumer quotes, and no consumer has to unfold `natDegree_pow` inline.

## The repair `[repaired: A-F.4]` — the monicity hypothesis is load-bearing

The originally signed signature carried **no** hypothesis on `ψ`, and in that form the statement
is **FALSE**; it was machine-refuted at blueprint amendment A-F.4.  The reason is that
`resField φ = F[y]/(φ̄)` is a field only when `φ` is a key, and B.47 binds a *bare* `φ`: for
`O = ℤ_[2]`, `φ = X ^ 2`, the ring `resField φ = 𝔽₂[y]/(y ^ 2)` has nilpotents, and with
`ψ = C (AdjoinRoot.root φ̄) * X` (so `ψ ^ 2 = 0`), `a = 2`, `ℓ = 1` the hypothesis `hg` reads
`g.natDegree = 1 * 2 * 0 = 0` while the conclusion demands `g.natDegree = 1 * 2 * 2 * 1 = 4`.

The STATEMENT prose always said "`ψ` monic irreducible", so the repair only restores what the
prose asserted.  **Monicity alone suffices; irreducibility is NOT taken** — the proof runs through
`Polynomial.Monic.natDegree_pow`, which needs only `[Semiring R]`.  (The originally cited
`Polynomial.natDegree_pow` requires `[NoZeroDivisors (resField φ)]` at our pin, which is exactly
what a non-key `φ` denies.)

The signed hypotheses `u`, `ℓ` are part of the frozen signature: `u` is the slope numerator
carried for the consumer's benefit and is not used, and `ℓ` occurs only as the opaque factor that
is transported from `hg` to the conclusion.

DEPENDS: B.25 (`resField`, in the signature) · mathlib `Polynomial.Monic.natDegree_pow`.

**PROOF.** `(ψ ^ a).natDegree = a * ψ.natDegree` (`hψ.natDegree_pow`); rewrite into `hg` and
close by `ring`.

**SOURCE.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2, quoting [GN15] Thm 2.3:
"`deg g_{λ,ψ} = e_λ ord_ψ(R_{r+1,λ}(g)) deg ψ deg φ`" — exactly `ℓ * a * d_ψ * m`;
`docs/GMN_citations.md` Thm 1.19 / Cor 1.20; `EFF.HE3.32` (`|S_r| = D′ℓ deg r`, the same number
read as a class size).

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, all 5 `μ = 3` stage types) → executable
regression retained.

ENVIRONMENT: ENV-A.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- `u` (and the bare occurrence of `ℓ`) belong to the frozen signature; see the module docstring.
set_option linter.unusedVariables false in
/-- **B.47 — the degree of a residual piece.**  If the factor `g` cut out by the residual piece
`ψ ^ a` has degree `ℓ * m * (ψ ^ a).natDegree` with `m = φ.natDegree`, then — `ψ` being monic —
that degree is `ℓ * m * a * ψ.natDegree`.

`[repaired: A-F.4]`: `(hψ : ψ.Monic)` is required.  Without it the statement is false; see the
module docstring for the machine refutation. -/
theorem natDegree_of_residual_piece {φ : Polynomial O} {u ℓ : ℕ} {g : Polynomial O}
    {ψ : Polynomial (resField φ)} {a : ℕ} (hψ : ψ.Monic)
    (hg : g.natDegree = ℓ * φ.natDegree * (ψ ^ a).natDegree) :
    g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree := by
  rw [hg, hψ.natDegree_pow]
  ring

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.natDegree_of_residual_piece
end AxCheck
