/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C02

/-!
# Uniformity.ChapC.C06 — `dvHgt`, `dvSupp`: the level polygon in the `dv`-normalization

**Chapter C, NODE C.06** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Two signed declarations, both
definitional.

**Ordering — stub-gate defect D12(i).** C.06 is HOISTED above C.05. The blueprint prints C.05
(`dvHgt_degenerate`, `dvSupp_degenerate`) before C.06, but C.05's statements CONSUME `dvHgt` and
`dvSupp`, which are DEFINED here; the gate (`leanspec/Leanspec/ChapC.lean`, D12(i)) records the
inversion and fixes the landed order as C.01 → C.02 → C.03 → C.04 → **C.06 → C.07** → C.05 → C.08.
That order is binding on the chapter roll-up too.

*The level polygon: heights and cleared support in the `dv`-normalization.* For a frame `F`
(C.01) and `f ∈ O[X]`:

* `dvHgt F f j := F.stageHeight (dev F.key f j)` — the **level height** of the `j`-th
  `Φ′`-development coefficient. This is `EFF.HE6.10`'s point set `{(j, dv(A_j))}` written
  closure-free: `dev F.key f j` is B.02's `A_j`, and `stageHeight` (C.02) is `dv` — B.14's cleared
  support at the frame's own side `(h, e₁)` over the order-0 key `X`.
* `dvSupp F f u ℓ := inf_j (ℓ • dvHgt F f j + u·j)` — the **cleared level support**, i.e. the
  `ℓ`-cleared value of the level polygon's supporting line of slope `−u/ℓ`.

## Why there is no new polygon type here (GC-2, D-1)

GC-2 forbids the tower to carry a new polygon carrier: every level's polygon is D-1's
three-object representation (support value / side set / residual) read at that level. C.06 is the
second turn of that crank and it is executed by SHAPE REUSE, not by construction:

| level | height function | cleared support |
| --- | --- | --- |
| order 0 (chapter B) | `npHgt φ f j = gaussVal (dev φ f j)` (B.11) | `suppVal φ f u ℓ` (B.14) |
| stage (C.02) | — | `stageHeight F A = suppVal X A F.h F.e₁` |
| level 1 (here) | `dvHgt F f j = stageHeight F (dev F.key f j)` | `dvSupp F f u ℓ` |

Read down the `dvHgt` column: B.11's height is `gaussVal ∘ dev`, and C.06's is
`stageHeight ∘ dev` — the SAME composite with the previous level's cleared support in place of
`gaussVal`. That substitution IS the tower recursion, and C.11's `dv2Hgt` performs it once more
with `dvSupp` in the slot. Every carrier stays `ℕ∞`; no `WithTop ℤ` fallback is ever reached
(C-H14), because every height is an infimum of `ℕ`-linear forms.

The degenerate check that this reuse is faithful at level 1 is C.05 (`dvHgt_degenerate`,
`dvSupp_degenerate`), the reconciliation GC-2 mandates: at `F.h = 0` (hence `F.e₁ = 1`)
`dvHgt F f j` IS `npHgt F.key f j` and `dvSupp F f u ℓ` IS `suppVal F.key f u ℓ`. C.05 is the
next node to land; nothing here anticipates it.

## Two shape details, both copied rather than chosen

* **The range bound.** `Finset.range (f.natDegree + 1)` is B.14's own bound, reused verbatim. It
  is safe and convention-free: the `Φ′`-development is supported on `j ≤ deg f / D′ ≤ deg f`, so
  the extra indices contribute `dev F.key f j = 0`, whose `stageHeight` is `⊤`, which is the
  identity for `Finset.inf` on `ℕ∞` and therefore cannot lower the infimum.
* **The `ℕ∞` coercion seam.** B.14 writes the linear term as `((u * j : ℕ) : ℕ∞)`; the A-C.1
  signature and the gate-verified twin both write `(u * j : ℕ∞)`, i.e. the product of the two
  casts. The two are bridged by `Nat.cast_mul` and are NOT syntactically equal. The signed text is
  transcribed as signed. This is the same seam C.02 recorded at `stageHeight_eq_inf`, and it is
  the seam C.05's `dvSupp_degenerate` has to cross.

**DEPENDS.** C.01 (`KeyFrame`) · C.02 (`KeyFrame.stageHeight`) · B.02 (`dev`) · B.11 · B.14
(the shape templates) — all by committed node ID (GC-13(b)). The import is
`Uniformity.ChapC.C02`, which pulls the rest of the chain.

**PROOF.** Definitional. The bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub
bodies (the §3 A-C.1 layer) verbatim.

SOURCE: `EFF.HE6.10` (verbatim: `F(Y) := Y^μ + Σ_j A_j(θ)Y^j`; `P(F) :=` lower hull of
`{(j, dv(A_j))}` — the hull replaced by the cleared support per D-1/GC-2); `EFF.HE3.31`'s `(★)`
one level up.

**TEETH.** Signed non-applicable (definitions; the level-polygon audits fire at C.08's length law
and at blueprint §13's gates).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `dv(A_j)` — the level heights of the `Φ′`-development (`EFF.HE6.10`). -/
noncomputable def dvHgt (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) : ℕ∞ :=
  F.stageHeight (dev F.key f j)

/-- The cleared level support `inf_j (ℓ·dv(A_j) + u·j)` — B.14's shape at the `dv`-level.
The range bound mirrors B.14's (`natDegree f + 1` is safe and convention-free). -/
noncomputable def dvSupp (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • dvHgt F f j + (u * j : ℕ∞))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dvHgt
#print axioms Uniformity.Density.Tower.dvSupp

end AxCheck
