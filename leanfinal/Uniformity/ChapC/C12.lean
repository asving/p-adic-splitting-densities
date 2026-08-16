/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C04
import Uniformity.ChapC.C09

/-!
# Uniformity.ChapC.C12 — `level2Field`, `card_level2Field`: the level-2 residue field `K₂`

**Chapter C, NODE C.12** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C3 (`[Finite (ResidueField O)]`,
`hπ` explicit). Two signed public declarations — the carrier and its count; the
`Field`/`Finite`/`finrank` clauses of the blueprint STATEMENT are carried by private companions
in this file, exactly as C.04 carries them one level down.

*The level-2 residue field.* For a level datum `L` over a frame `F` with a correct pin `H₀`:

* `level2Field L := AdjoinRoot L.r` — `K₂ = K(β)`, the `resField` pattern iterated a **second**
  time, now over the stage field `K = stageField F H₀ hpin` of C.03 rather than over
  `resField X`. `L.r` is C.09's residual factor, monic irreducible over `K`.
* `card_level2Field L hπ : Nat.card (level2Field L) = residueCard O ^ (F.f₁ * L.r.natDegree)` —
  the count, i.e. `|K₂| = Q^{f₁ d_r}`.

`EFF.HE6R1.18`'s audit row is the `(f₁, d_r) = (1, 2)` instance of the display: `K = F_p` because
`f₁ = 1`, `[K₂ : K] = d_r = 2`, hence `K₂ = F_{p²}`.

## Why this is an iterate and not a new construction (GC-7)

GC-7 is the law of the chapter: residue enlargement is the iterated CHAP-B `resField` pattern
(`resField φ = AdjoinRoot (φ.map (residue O))`), never an `IntermediateField` of an algebraic
closure, and the bundle `O` is fixed once. The tower of carriers that results is

| level | carrier | base | degree |
| --- | --- | --- | --- |
| order 0 | `resField X = AdjoinRoot (X.map (residue O))` | `ResidueField O` | `1` |
| stage (C.03) | `stageField F H₀ hpin = AdjoinRoot (frameRes F H₀ hpin)` | `resField X` | `F.f₁` |
| level 2 (here) | `level2Field L = AdjoinRoot L.r` | `stageField F H₀ hpin` | `L.r.natDegree` |

and the count multiplies down the right-hand column: `Q^1`, then `Q^{f₁}` (C.04), then
`Q^{f₁·d_r}` (this node). `level2Field` is an `abbrev`, not a `def`, because it must be
*transparent* to instance search — every `Algebra`/`Module`/`Field` instance a consumer needs on
`K₂` is an `AdjoinRoot` instance, and unfolding must be free.

## The proof: one power-basis step on top of C.04

`Module.natCard_eq_pow_finrank` over the base `K` reduces the count to two facts:

1. `Module.finrank K (level2Field L) = L.r.natDegree` — `AdjoinRoot.powerBasis`'s dimension, which
   is `L.r.natDegree`; the hypothesis it needs is `L.r ≠ 0`, supplied by `L.hrirr.ne_zero`.
2. `Nat.card K = residueCard O ^ F.f₁` — **C.04's public `card_stageField`, cited, not re-proved**.

`pow_mul` then turns `(Q^{f₁})^{d_r}` into `Q^{f₁ d_r}`. This is the blueprint's two-step PROOF
verbatim; step 1's *"field/finite instances from `L.hrirr` as in C.04 steps 1–2"* is the private
companion block below.

## D9, again — and why the helpers are re-declared rather than imported

`AdjoinRoot.powerBasis` needs a `Field` structure on the BASE, here `stageField F H₀ hpin`, and
that field structure needs (i) `Fact (Irreducible (frameRes F H₀ hpin))`, from the frame's
`hresirr`, and (ii) a `Field` on `resField X`, which B.25(b)'s `instFieldResField` supplies only
from `IsKey X` — the stub gate's defect **D9**. C.04 landed the cure, but landed it `private`
(deliberately: the public D9 cure belongs to whichever node the amendment set assigns it, and the
gate-verified twin puts a public `isKey_X` at the §4 header, which is C.15's neighbourhood, not
C.04's and not this node's). A private declaration is not importable, so `isKey_X` and
`fieldStageField` are re-declared here, byte-identical to C.04's, and likewise `private`. Private
names are module-mangled, so the two copies cannot collide when the chapter roll-up imports both.
When the public D9 cure lands, both copies become deletable in one edit — that is the whole cost
of the duplication, and it is recorded here so the edit is findable.

## `hπ`

`hπ : Irreducible π` is bound by ENV-C3 and by the signed signature. Unlike at C.04 it *is* used
here — not directly, but as the argument C.04's `card_stageField` demands (where it is in turn
unused; see C.04's note). So no linter suppression is needed at this node.

## What is NOT claimed

* **Nothing here says `L.r` is the residual of anything.** `level2Field` is `AdjoinRoot` of
  whichever monic irreducible the level datum carries; that this polynomial is the residual factor
  attached to a side of the level polygon is C.29's `HasLabel`, not this definition.
* **Nothing here gives `K₂` a distinguished generator over `resField X`.** The letter `β` of the
  informal display is `AdjoinRoot.root L.r`; the corresponding *stage* letter `η` is C.19, and the
  level-2 analogue is not signed at this node.

## ⚠ DEPTH-3 NOTE (transcribed; GC-7's medium-confidence leg)

The blueprint attaches this warning to the node and it is reproduced verbatim because it governs
§9's third-stage work, not this file:

> This is the depth-2 iterate. §9's third-stage nodes need the depth-3 iterate `AdjoinRoot r₃`
> over `level2Field`; no new mechanism, but nobody has elaborated a depth-3 `AdjoinRoot` tower in
> `leanfinal` — if the instance chain fails to elaborate at stub stage, GC-7's recorded fallback
> (a level structure carrying abstract `[Field K_r]` with a specified `Algebra` chain) triggers a
> DECISION block here. Flagged to §16.

Reporting one data point *for* that future decision, since this node is where it would be read:
the depth-2 chain elaborated here with no `maxSynthPendingDepth` change and no `set_option` of any
kind, and the `Field` companion `fieldLevel2Field` (depth-2 `AdjoinRoot.instField` over a
depth-1 `AdjoinRoot.instField` base) elaborated as well. That is evidence about depth 2 only; the
lakefile pins `maxSynthPendingDepth = 3`, so a depth-3 iterate is exactly where the pinned budget
could first bite.

**DEPENDS.** C.03 (`frameRes`, `stageField`) · C.04 (`card_stageField`, and the D9/field pattern)
· C.09 (`LevelDatum`, `hrirr`) · B.25 (`resField`, `instFieldResField`) · B.01 (`IsKey`) — all by
committed node ID (GC-13(b)). The imports are `Uniformity.ChapC.C04` and `Uniformity.ChapC.C09`.

**PROOF.** The blueprint's two steps, as above.

SOURCE: `EFF.HE6R1.18` (audit: *"`K₂ = K(β)` with `[K₂:K] = d_r = 2` and `K = F_p` (since
`f₁ = 1`), so `K₂ = F_{p²}` ✓"*); GC-7.

**TEETH.** The same `EFF.HE6R1.18` audit row as C.04, now at the C.12 iterate → **Lean theorem**
(`card_level2Field` is that row in general form: the row's `Q^{f₁ d_r} = p^{1·2} = p²` is the
statement at `f₁ = 1`, `d_r = 2`, `Q = p`); the numeric leg re-fires as an **executable
regression** at blueprint §13. GC-11's numerics rider: this node's arithmetic row is
`|K₂| = Q^{f₁ d_r}`, which is prime-free as stated and is therefore discharged at both `q = 2`
and `q = 3` by the *same* theorem; the §13 gates instantiate it at both primes (C.123's `q = 3`
frame and C.124's `q = 2` analogue), and nothing at this node needs a per-prime case.

ENVIRONMENT: ENV-C3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers (stub-gate defect **D9**; C.04's copies, re-declared — see the note above) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense. C.04's private copy,
re-declared because private declarations are not importable. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- The `Field` structure on the stage field `K`, i.e. the BASE of this node's `AdjoinRoot`.
C.04's private copy. A `@[reducible] noncomputable def`, not an `instance`, for B.25(b)'s reason
(an `instance` with the explicit non-class hypotheses `F`/`hpin` is rejected at our pin). -/
@[reducible] private noncomputable def fieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-! ### The signed carrier -/

/-- `K₂ = K(β)`, the second `AdjoinRoot` iterate (GC-7). -/
abbrev level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : Type _ :=
  AdjoinRoot L.r

/-! ### The `Field` / `finrank` / `Finite` clauses of the STATEMENT (private companions) -/

/-- **The `Field` clause of C.12's STATEMENT.** `K₂` is a field: `L.hrirr` supplies
`Fact (Irreducible L.r)` and `fieldStageField` the base field. Depth-2 `AdjoinRoot.instField`. -/
@[reducible] private noncomputable def fieldLevel2Field {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) : Field (level2Field L) :=
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  AdjoinRoot.instField

/-- **The `finrank` clause of C.12's STATEMENT.** `[K₂ : K] = d_r` — the power basis of `L.r` has
dimension `L.r.natDegree`. -/
private theorem finrank_level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
    Module.finrank (F.stageField H₀ hpin) (level2Field L) = L.r.natDegree := by
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  have hr0 : L.r ≠ 0 := L.hrirr.ne_zero
  rw [(AdjoinRoot.powerBasis hr0).finrank, AdjoinRoot.powerBasis_dim hr0]

/-- **The `Finite` clause of C.12's STATEMENT.** `K₂` is a finite-dimensional space over the
finite field `K`. -/
private theorem finite_level2Field {F : KeyFrame O π} [Finite (ResidueField O)] {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) : Finite (level2Field L) := by
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  haveI : Finite (F.stageField H₀ hpin) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [F.card_stageField hπ H₀ hpin]
    exact (pow_pos (residueCard_pos O) _).ne'
  have hr0 : L.r ≠ 0 := L.hrirr.ne_zero
  haveI : Module.Finite (F.stageField H₀ hpin) (level2Field L) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hr0).basis
  exact Module.finite_of_finite (F.stageField H₀ hpin)

/-! ### The signed count -/

/-- **C.12 — the level-2 residue field has `Q^{f₁ d_r}` elements.** `|K₂| = |K|^{d_r}` by the
power basis of `L.r`, and `|K| = Q^{f₁}` is C.04; `EFF.HE6R1.18`'s `K₂ = F_{p²}` is the
`(Q, f₁, d_r) = (p, 1, 2)` instance. -/
theorem card_level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) :
    Nat.card (level2Field L) = residueCard O ^ (F.f₁ * L.r.natDegree) := by
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  have hr0 : L.r ≠ 0 := L.hrirr.ne_zero
  haveI : Module.Finite (F.stageField H₀ hpin) (level2Field L) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hr0).basis
  have hfr : Module.finrank (F.stageField H₀ hpin) (level2Field L) = L.r.natDegree := by
    rw [(AdjoinRoot.powerBasis hr0).finrank, AdjoinRoot.powerBasis_dim hr0]
  rw [Module.natCard_eq_pow_finrank (K := F.stageField H₀ hpin), hfr,
    F.card_stageField hπ H₀ hpin, ← pow_mul]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.level2Field
#print axioms Uniformity.Density.Tower.card_level2Field

end AxCheck
