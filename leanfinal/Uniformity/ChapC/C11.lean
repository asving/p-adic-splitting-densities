/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C06
import Uniformity.ChapC.C09

/-!
# Uniformity.ChapC.C11 — `dv2Hgt`, `dv2Pin`, `dv2Supp`: the level-2 heights (THE tower recursion)

**Chapter C, NODE C.11** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Three signed declarations,
all definitional.

*The level-2 heights — the tower recursion.* For a level datum `L` over a frame `F` (C.09) and a
level-2 key `Ψ` (any monic polynomial of degree `D″`; C.13 supplies the canonical ones):

* `dv2Hgt L A := dvSupp F A L.u L.ℓ` — the **level-2 slot height** of a coefficient
  `A ∈ O[X]`: the level-1 cleared support of `A` *at the level's own side* `(L.u, L.ℓ)`.
* `dv2Pin L Ψ f j := dv2Hgt L (dev Ψ f j)` — the **level-2 pins** of `f`, i.e. the level-2
  heights of the `Ψ`-development coefficients (B.02's `dev`, now taken at the level-2 key).
* `dv2Supp L Ψ f u₂ ℓ₂ := inf_j (ℓ₂ • dv2Pin L Ψ f j + u₂·j)` — the **level-2 cleared support**,
  the `ℓ₂`-cleared value of the level-2 polygon's supporting line of slope `−u₂/ℓ₂`.

## The one line that is the whole node

`dv2Hgt L A = dvSupp F A L.u L.ℓ`. Read as an equality of *shapes* rather than of numbers, this
is the tower recursion, and it is the third turn of the crank C.06 documented as the second:

| level | height function | cleared support |
| --- | --- | --- |
| order 0 (chapter B) | `npHgt φ f j = gaussVal (dev φ f j)` (B.11) | `suppVal φ f u ℓ` (B.14) |
| stage (C.02) | — | `stageHeight F A = suppVal X A F.h F.e₁` |
| level 1 (C.06) | `dvHgt F f j = stageHeight F (dev F.key f j)` | `dvSupp F f u ℓ` |
| level 2 (here) | `dv2Pin L Ψ f j = dv2Hgt L (dev Ψ f j)` | `dv2Supp L Ψ f u₂ ℓ₂` |

Every row is `⟨previous level's cleared support⟩ ∘ dev` for the height, and B.14's
`inf_j (ℓ • height + u·j)` for the support. GC-2 forbids a new polygon carrier at each level and
this node obeys by SHAPE REUSE: nothing is constructed here, `dvSupp` is merely called at a
different side and its output fed to a different `dev`.

**C-H14 is discharged by construction, not by a lemma.** Every value above is `ℕ∞`: the level-1
support is an infimum of `ℕ`-linear forms in the coefficients' `addVal`s, and so is the level-2
support built on it. No `WithTop ℤ` fallback is ever reached, because *the normalizer offset never
appears as a subtraction* — the cleared pair `(u, ℓ)` carries it. That is exactly the mechanism
GC-2's ruling names through `EFF.HE6R1.13`(b): clearing the denominator is what turns the
translation identity into an `ℕ`-statement, and the price is that consumers must remember the
values are `ℓ`-cleared (a factor `L.ℓ`, resp. `ℓ₂`, larger than the corpus's rational heights).

## ⚠ Faithfulness — the recast, transcribed verbatim from the blueprint

**Mandatory, trust-boundary definition** (three definitions, no proof obligation; parent
CLAUDE.md trust boundary). The blueprint's own ⚠ FAITHFULNESS field reads:

> The corpus's `dv₂` is defined at level-2 POINTS (`dv₂(A(ξ))`, `EFF.HE6R1.18`); this definition
> is the cleared-support recast, and the statement tying the two — `dv2Hgt` computes the exact
> value at every root of every factor carrying the label — is §4's slot-exactness layer
> (C.25/C.26), NOT this definition. Consumers must depend on those lemmas, never on an assumed
> exactness of this `def`. The seam identity `dv2Hgt L (Ψ-const-coeff) = T₂`-family facts are
> C.14/§5 content.

Two consequences worth stating in the negative, since this file is what a consumer greps:

* **Nothing here says `dv2Hgt` is the valuation of anything.** It is an infimum over a finite
  index range of a `ℕ`-linear expression. That it *equals* `ℓ·dv₂(A(ξ))` at the roots `ξ` carrying
  the label is a theorem with hypotheses, and the hypotheses are C.25/C.26's, not this node's.
* **Nothing here says `dv2Hgt L (Ψ.coeff 0)` is the seam `L.seam`.** The seam identity is C.14's,
  and the `T₂`-family facts it feeds are §5's.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

## Three shape details, all copied rather than chosen

* **`dv2Hgt` does not mention `Ψ`.** The slot height of a coefficient is a level-1 quantity; the
  level-2 key enters only when the coefficient is produced as a `Ψ`-development term, which is
  `dv2Pin`'s job. This is why the blueprint signs `dv2Hgt` on a bare `Polynomial O` — it is the
  height function that C.25/C.26 will pin, and consumers that hold an arbitrary coefficient (not a
  development term) need it in that form.
* **The range bound.** `Finset.range (f.natDegree + 1)` is B.14's own bound, reused verbatim
  through C.06. Safe and convention-free for the same reason recorded at C.06: the
  `Ψ`-development is supported on `j ≤ deg f`, and the extra indices contribute `dev Ψ f j = 0`,
  whose height is `⊤`, the identity for `Finset.inf` on `ℕ∞`.
* **The `ℕ∞` coercion seam.** B.14 writes the linear term as `((u * j : ℕ) : ℕ∞)`; the A-C.1
  signature and the gate-verified twin both write `(u₂ * j : ℕ∞)`, i.e. the product of the two
  casts. The two are bridged by `Nat.cast_mul` and are NOT syntactically equal. The signed text is
  transcribed as signed — this is the same seam C.02 and C.06 already recorded, inherited here for
  the third time, and it is the seam every `dv2Supp` translation lemma (C.36 and its family) has
  to cross.

## The two slopes, which are different objects

`L.u`/`L.ℓ` (fields of the level datum, C.09) are the **level-1** side at which the level-2 slot
heights are read; `u₂`/`ℓ₂` (arguments of `dv2Supp`) are the **level-2** slope numerals of the
polygon being supported. They are never identified, and `dv2Supp L Ψ f L.u L.ℓ` is not a
distinguished instance of anything. The level-2 dictionary's own numerals (`L.keyDeg₂`, `L.seam`)
are C.09's and do not appear here.

**DEPENDS.** C.06 (`dvSupp`) · C.09 (`LevelDatum`, its `u`/`ℓ` fields) · B.02 (`dev`) — all by
committed node ID (GC-13(b)). The imports are `Uniformity.ChapC.C06` and `Uniformity.ChapC.C09`;
C.06 pulls C.01/C.02 and the B chain, C.09 pulls C.03.

**PROOF.** Definitional. The bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub
bodies (the §3 A-C.1 layer) verbatim.

SOURCE: `EFF.HE6R1.18` (the level-2 frame: `T₂ = 2λ`, "the level-2 layer over `K₂ = F_{p²}` is
fresh"); `EFF.HE6R1.13`(b) (the translation identity this shape makes stateable); GC-2 (three
objects at every level).

**TEETH.** Signed non-applicable at the definition; the exactness teeth live on C.25/C.26.
GC-11's numerics rider is likewise non-applicable here: this node states no arithmetic row, and
the `q = 2` / `q = 3` spot values for the level-2 polygon fire at blueprint §13 against C.25/C.26
and the §5 translation lemmas, not against these three `def`s.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The level-2 slot height of a coefficient: the level-1 support value at the side.
This equality of shapes IS the tower recursion (design note above). -/
noncomputable def dv2Hgt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : ℕ∞ :=
  dvSupp F A L.u L.ℓ

/-- The level-2 pins of `f` at the level-2 key `Ψ`: the level-2 slot heights of the
`Ψ`-development coefficients `dev Ψ f j` (B.02's `dev`, one level up). -/
noncomputable def dv2Pin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (j : ℕ) : ℕ∞ :=
  dv2Hgt L (dev Ψ f j)

/-- The level-2 cleared support `inf_j (ℓ₂·dv2Pin_j + u₂·j)` — B.14's shape at the level-2
polygon. The range bound mirrors B.14's, as C.06's does one level down. -/
noncomputable def dv2Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2Hgt
#print axioms Uniformity.Density.Tower.dv2Pin
#print axioms Uniformity.Density.Tower.dv2Supp

end AxCheck
