/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C01
import Uniformity.ChapB.B15

/-!
# Uniformity.ChapC.C02 — `stageHeight`, the stage height `dv` as a REUSE of B's cleared support

**Chapter C, NODE C.02** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level
frame and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Two signed
declarations — one definition, one companion unfold.

*The stage height.* For a frame `F` (C.01) and any `A ∈ O[X]`, the **stage height** is

  `stageHeight F A := suppVal X A F.h F.e₁ ∈ ℕ∞`

— literally B.14's cleared support value of the `X`-development of `A` at the frame's side
`(h, e₁)`. The companion `stageHeight_eq_inf` unfolds it to `EFF.HE6.10`'s display

  `dv(A) = min_i (e₁·v(a_i) + i·h)`

verbatim, `ℕ∞`-valued: at the order-0 key `X` the `X`-development is the coefficient list
(B.15's `dev_X`), so B.14's `inf_j (ℓ • npHgt X A j + u·j)` IS that minimum.

## Why this is a definition and not a construction (GC-2)

GC-2 mandates that the tower carry NO new polygon type: every level's polygon is D-1's three
objects (`suppVal`/`sideSet`/`resPoly`) read at that level's side. C.02 is the base case of
that mandate and it is executed literally — `stageHeight` is `suppVal` applied at the order-0
key, with no wrapper, no new carrier and no new arithmetic. The recursion this opens is
"a level's height function is the previous level's cleared support value": C.06's `dvHgt`
composes `stageHeight` with the `Φ′`-development, and C.11's level-2 height composes `dvSupp`
one step further. Every carrier stays `ℕ∞`, so the `WithTop ℤ` fallback flagged at C-H14 is
never reached (heights are infima of `ℕ`-linear forms at every level).

## The `ℕ∞` coercion seam

B.14 writes the linear term as `(u * j : ℕ)` cast into `ℕ∞`; the signed companion writes it as
`(F.h * i : ℕ∞)`, i.e. the product of the two casts. `Nat.cast_mul` is the bridge and it is the
only non-definitional content of the proof. This is recorded because the same seam recurs at
every level of the tower (C.06, C.11) and at the `slotIdx` heights of §4.

**DEPENDS.** C.01 (`KeyFrame`) · B.14 (`suppVal`) · B.15 (`dev_X`, `npHgt_X` — the
`X`-development is the coefficient list) — all by committed node ID (GC-13(b)). The imports are
`Uniformity.ChapC.C01` and `Uniformity.ChapB.B15`, which pull the rest of the chain.

**PROOF.** `stageHeight` is definitional. `stageHeight_eq_inf`: unfold `suppVal` and `npHgt`,
rewrite each `dev X A i` by B.15's `dev_X : dev X f j = C (f.coeff j)`, and split the cast of
the product by `Nat.cast_mul`.

SOURCE: `EFF.HE6.10` (the `dv` display, verbatim); GC-2 (the reuse mandate); `EFF.HE6R1.18`
(the audit `dv(ϖ(ξ)) = 1`, which consumes exactly this normalization).

**TEETH.** Signed non-applicable (a definition plus its own unfold; the `dv` audits fire at
C.05's degenerate reconciliation and at §13's gates).

ENVIRONMENT: ENV-C1 (`hπ` is needed only by consumers that read residues; no clause here does).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `dv(A) = min_i (e₁·v(a_i) + i·h)` (`EFF.HE6.10`), realised as B's `suppVal` at the
order-0 key `X` — GC-2's reuse, literal. -/
noncomputable def KeyFrame.stageHeight (F : KeyFrame O π) (A : Polynomial O) : ℕ∞ :=
  suppVal Polynomial.X A F.h F.e₁

/-- The companion unfold: `EFF.HE6.10`'s display `dv(A) = min_i (e₁·v(a_i) + i·h)`, read off
the order-0 development (B.15's `dev_X` says the `X`-development of `A` is its coefficient
list, so `npHgt X A i = gaussVal (C (A.coeff i))`). -/
theorem KeyFrame.stageHeight_eq_inf (F : KeyFrame O π) (A : Polynomial O) :
    F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun i => F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞)) := by
  simp only [KeyFrame.stageHeight, suppVal, npHgt, dev_X, Nat.cast_mul]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight
#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_eq_inf

end AxCheck
