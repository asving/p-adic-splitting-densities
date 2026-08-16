/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C21

/-!
# Uniformity.ChapC.C22 — `KeyFrame.twistRead`: the ϖ-read residue `γ_k·η^{−q(k)}`

**Chapter C, NODE C.22** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1**. One signed declaration, definitional.

C.21 landed the **`n(k)`-read** `γ_k(A) = res(A(θ)/n(k)(θ))`, the residue of `A` normalized by
the *slot* normalizer. The corpus's residual polynomials are not read against `n(k)` but against
the **ϖ-normalizer**, and `EFF.HE6.58`'s TERMINAL display records the exact ratio between the
two reads:

`res(A(ξ)/ϖ(ξ)^k) = ι_ξ(γ_k(A)) · η_ξ^{−q(k)}`,  `q(k) := twistExp F k` (C.15).

This node is that right-hand side, as an `O`-level object:
`twistRead F H₀ hpin k A := η⁻¹ ^ q(k) · slotRes F H₀ hpin k A` in `K = F.stageField H₀ hpin`.
**Every corpus residual polynomial reads through this**, starting with C.25's `R_λ`; `slotRes`
alone is never the residual coefficient.

## The sign is the `[r2]` correction, and it is not cosmetic

The exponent is **minus** `q(k)`. `EFF.HE6.15`'s `[r1]` reading had `+q(k)`, and it is refuted by
the `(2,2,3)` witness reproduced under TEETH below. Both readings agree exactly when `q(k) = 0`,
so the refutation needs a frame with `q(k) ≠ 0` — which is why the witness is MANDATORY and why
the gate carries it at both primes (GC-11's two-prime clause; C-H12's coincidence regime is the
reason a `q(k) = 0` row proves nothing about the sign).

## ⚠ FAITHFULNESS (definition-side, trust boundary)

Carried from the blueprint. The corpus **derives** this identity from ϖ itself
(`res(n(k)/ϖ^k) = η^{−q}`, the `EFF.HE6.13` RIDER's computation); here it is a **DEFINITION**,
because ϖ (`= x^{i₀}π^{a₀} ∈ K₀[x]`, with `a₀` possibly negative — `EFF.HE6.11`) is never
constructed in `leanfinal` and cannot be: only its exponent arithmetic `(i₀, q(k))` survives the
recast, which is exactly what `EFF.HE6.11` says is "all that is ever used". The definitional
content therefore has to be checked against the corpus by its consequences, not by unfolding, and
its one machine-checkable consequence is the `(2,2,3)` row below. A second, independent guard is
structural: C.24's span law characterizes the image of the read at every window, and a wrong sign
breaks that characterization at every **proper** window (at a full window the coset factor is
invisible, `η^{−q}·K^× = K^×`, which is why C.24's own fullness clause cannot see the sign).

## The two `letI`s are the signed text (defect D9)

`stageField H₀ hpin = AdjoinRoot (F.frameRes H₀ hpin)` has **no `Inv`** at this node's binders,
so `η⁻¹` does not elaborate as signed. `AdjoinRoot.instField` needs two things that are not in
scope: `Fact (Irreducible (F.frameRes H₀ hpin))` — supplied from the frame's own `hresirr` — and
a `Field` structure on the **base** `resField X`, supplied by B.25's `instFieldResField` keyed on
`IsKey X`, which no node proves. The gate-verified twin's cure (the two `letI`s plus the helper
`isKey_X`) is a blueprint declaration of this node and is what lands here. A consequence worth
naming: this makes `hpin` **genuinely used** in the body (through `hresirr H₀ hpin`), unlike at
C.03/C.19 where it is a correctness side condition on the numeral `H₀` only.

`isKey_X` is `private` here, as at C.04/C.12/C.19/C.44: `private` does not export, and the public
copy is C.14a's to land (at which point all five collapse into it). Repeating it is the standing
D9 pattern in this chapter, not a new decision.

## Alternatives deliberately not taken

Writing the twist as `η ^ (f₁ − q(k) % f₁)`-style positive powers would avoid the `Field`
instance, but it is **not** the same function: it presumes `η^{f₁} = 1`, which is false in `K`
(the letter is not a root of unity of that order — `η` generates `K` over `resField X`, and its
multiplicative order is `|K^×|`-divisible data the frame does not pin). The inverse is the honest
object, and paying for it with the two `letI`s is the twin's ruling.

**DEPENDS.** C.15 (`twistExp`) · C.19 (`stageLetter`) · C.21 (`slotRes`) · C.03 (`stageField`,
`frameRes`) · C.01 (`hresirr`) · B.01 (`IsKey`) / B.25 (`instFieldResField`, `resField`) — by
committed node ID (GC-13(b)). The single import is `Uniformity.ChapC.C21`, which pulls C.15,
C.16, C.17, C.19 (hence C.03, C.01, B.25) and the whole B chain.

**PROOF.** Definitional. The body is the gate-verified twin's verbatim (both `letI`s included).

SOURCE: `EFF.HE6.15` (the `[r2]` sign correction and its witness, verbatim); `EFF.HE6.58` (the
TERMINAL composed display); `EFF.HE6.13` RIDER (the fixed `η^q` ratio between the two reads).

**TEETH.** The `(2,2,3)` PE2-leg-B witness → **executable regression at §13 gate C.124**
(GC-11's MANDATORY row); it is not dischargeable at this node's binders, since an abstract
`KeyFrame O π` offers no numeral to `#guard` (the same D7 consequence recorded at C.15/C.17). The
values are EXECUTED in the twin's gate-hygiene block and are reproduced here for the record — at
`(e₁, f₁, h) = (2, 2, 3)` over `ℤ₃`, `k = 3`, `A = x`:

* `slotIdx 1 = 1` (`i₀ = 1`) and `slotIdx 3 = 1`, so `twistExp 3 = (1·3 − 1)/2 = 1`, i.e.
  `q(3) = 1` — the exponent is nonzero, which is what makes the row decide the sign;
* `slotWindow 3 = {0}` at that frame, and `A = x` reads `γ₃(x) = 1`;
* in `K = F₉ = F₃[T]/(T² − 2)`, `(2η)·η = 2η² = 4 = 1`, so `η⁻¹ = 2η`;
* hence `twistRead 3 x = η^{−1}·1 = 2η`, while the `[r1]` `+q` reading predicts `η`. **Refuted.**

⚠ **Honest divergence from the blueprint's FAITHFULNESS prose, found by the gate.** That prose
offers the `(2,2,1)` frame as a `q = 2` companion "where `q(k) = 0`". The executed rows show
`q(k) = 0` is *not* identical on that frame: `twistExp 1 = 0` but `twistExp 3 = 1` there
(`slotIdxN 2 1 1 = 1`; the twin's `#guard`s carry the ⚠ explicitly). Nothing about this node
changes — `q(k)` is `π`-independent arithmetic, so the `q = 2` frame supplies a genuine
`q(k) ≠ 0` row for GC-11's two-prime clause, which is the stronger reading anyway.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helper (stub-gate defect **D9**) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense — monic, of positive
degree, with irreducible reduction. B.25(b)'s `Field (resField φ)` is keyed on exactly this, and
`AdjoinRoot.instField` on `stageField` needs that base `Field`. C.04/C.12/C.19/C.44 each carry
their own copy for the same reason; `private` does not export, and the public copy is C.14a's.
`private`: a stub-side helper, not a blueprint node. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-! ### The signed declaration -/

/-- The ϖ-read residue `γ_k(A)·η^{−q(k)}` (`EFF.HE6.15` [r2]-corrected sign — **minus** `q`;
`EFF.HE6.58` TERMINAL). All corpus residual polynomials (`R_λ`, C.25) read through THIS, never
through the bare `n(k)`-read C.21.

**D9 (cured, from the gate-verified twin).** The two `letI`s supply the instances the signed
`⁻¹` needs and that this node's binders do not carry: the base `Field (resField X)` (B.25 keyed
on `isKey_X`) and `Fact (Irreducible (frameRes …))` (from the frame's `hresirr`). They also make
`hpin` genuinely used in the body. -/
noncomputable def KeyFrame.twistRead (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) (A : Polynomial O) : F.stageField H₀ hpin :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.twistRead

end AxCheck
