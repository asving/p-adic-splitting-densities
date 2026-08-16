/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C06

/-!
# Uniformity.ChapC.C05 — the level-1 reconciliation: chapter C's level-1 instance IS chapter B

**Chapter C, NODE C.05** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Three signed public
declarations, exactly the three of the A-C.1 SIGNATURE block.

**Ordering — stub-gate defect D12(i).** The blueprint prints C.05 before C.06, but C.05's
statements CONSUME `dvHgt`/`dvSupp`, which are DEFINED at C.06. The gate
(`leanspec/Leanspec/ChapC.lean`, D12(i)) fixes the landed order as
C.01 → C.02 → C.03 → C.04 → **C.06 → C.07** → C.05 → C.08; this file imports
`Uniformity.ChapC.C06` accordingly. The blueprint's own DEPENDS list for this node is
C.01 · C.02 · C.06 · B.08 · B.11 · B.14 — no C.07 — so the import stops at C.06.

*The level-1 reconciliation (GC-2's mandated lemma).* Let `F` be a **degenerate** frame:
`F.h = 0`. Coprimality (`F.hcop : Nat.Coprime F.h F.e₁`) then forces `F.e₁ = 1`, so the frame's
`dv`-normalization `dv = e₁·v` collapses to `v` itself and the frame's slope `h/e₁` collapses to
`0`. At such a frame:

* `F.stageHeight A = gaussVal A` — the stage height IS B.07's Gauss valuation;
* `dvHgt F f j = npHgt F.key f j` — C.06's level heights ARE B.11's polygon heights;
* `dvSupp F f u ℓ = suppVal F.key f u ℓ` — C.06's cleared level support IS B.14's cleared support.

This is the seam CHAP-B H-1 names (`e₁ = 1, h = 0, dv = addVal, ϖ = π`, twist trivial), and it is
the only reason the degenerate frame is admitted into `KeyFrame` at all: C.01's `h` field carries
the docstring *"`h = 0` (forcing `e₁ = 1`) is the DEGENERATE frame, admitted so that C.05's
level-1 reconciliation is definitional; the corpus frame has `1 ≤ h`."* No downstream chapter-C
consumer fires a test key on it.

## Why `h = 0` is the whole hypothesis

`Nat.Coprime 0 n ↔ n = 1` (`Nat.coprime_zero_left`), so a single equation `F.h = 0` pins BOTH
frame numerals that enter `stageHeight`. There is no second hypothesis to supply and none is
signed: `F.f₁`, `F.key` and the key's irreducibility play no role, because `stageHeight` is
`suppVal` at the ORDER-0 key `X` — it never reads `F.key`. (`F.key` reappears only in clauses two
and three, and there only as the development key on both sides of the equation.)

## The two seams the proof crosses

* **`gaussVal (C a) = addVal O a`.** C.02's `stageHeight_eq_inf` presents the stage height as
  `inf_i (e₁ • gaussVal (C (A.coeff i)) + h·i)` (B.15's `dev_X` having already collapsed the
  order-0 development to the coefficient list). At `e₁ = 1, h = 0` that is
  `inf_i gaussVal (C (A.coeff i))`, and `gaussVal (C a)` is an `inf` over `range 1`, i.e.
  `addVal O a`. So the display becomes `inf_i addVal O (A.coeff i)`, which is `gaussVal A` by
  definition (B.07). Clause one is therefore an unfold, as the blueprint's "definitionally up to
  B.08's inf-identity" advertises — B.08's `gaussVal_range` is not needed here because both sides
  already range over `A.natDegree + 1`.
* **The `ℕ∞` coercion seam.** B.14 writes the linear term of `suppVal` as `((u * j : ℕ) : ℕ∞)`
  (one cast of a `ℕ`-product); the A-C.1-signed `dvSupp` (C.06) writes it as `(u * j : ℕ∞)`
  (a product of two casts). These are NOT syntactically equal; `Nat.cast_mul` bridges them.
  C.06's docstring flags this seam and names C.05 as the node that has to cross it — clause
  three's `simp only` does exactly that, and nothing else.

## DELTA — the fourth STATEMENT bullet is unsigned, and it is FALSE as written

The blueprint's STATEMENT prose lists a fourth clause,
`dvSideSet F f u ℓ = sideSet F.key f u ℓ`. It is **absent from the A-C.1 SIGNATURE block and
absent from the gate-verified twin** (`leanspec/Leanspec/ChapC.lean` axiomatises exactly
`KeyFrame.stageHeight_degenerate`, `dvHgt_degenerate`, `dvSupp_degenerate`), so it is not
transcribed. That omission is correct, not an oversight: the clause is refutable.

C.07's `DvOnSide` carries a conjunct B.16's `OnSide` does not — the finiteness guard
`dvHgt F f j ≠ ⊤`. Take `f = 0` and `ℓ = 1`, at ANY frame `F` (degeneracy is not even needed):

* every level height is `⊤` (`dev F.key 0 j = 0`, and `gaussVal 0 = ⊤`), so the guard fails at
  every abscissa and `dvSideSet F 0 u 1 = ∅`;
* on B's side `suppVal F.key 0 u 1 = ⊤` as well, and `OnSide` — an equation between two `⊤`s —
  HOLDS at `j = 0`, so `sideSet F.key 0 u 1 = {0}`.

`∅ ≠ {0}`. Any future re-signing of the fourth clause must either add the hypothesis `f ≠ 0`
(with a nonvanishing development at the side) or restate it as the inclusion
`dvSideSet ⊆ sideSet`. Recorded here rather than acted on: signatures are frozen and this node's
signed three are unaffected.

**DEPENDS.** C.01 (`KeyFrame`, the `hcop` field) · C.02 (`KeyFrame.stageHeight`,
`stageHeight_eq_inf`) · C.06 (`dvHgt`, `dvSupp`) · B.07 (`gaussVal`) · B.11 (`npHgt`) ·
B.14 (`suppVal`) · B.15 (`dev_X`, consumed inside C.02) — all by committed node ID (GC-13(b)).
The single import `Uniformity.ChapC.C06` pulls the whole chain.

**PROOF.** The blueprint's three steps:
1. `Nat.coprime_zero_left` turns `F.h = 0` into `F.e₁ = 1`; rewrite C.02's `stageHeight_eq_inf`
   with both, then `simp [gaussVal]` discharges `1 • gaussVal (C (A.coeff i)) + 0·i`.
2. Clause two is clause one at `A := dev F.key f j`, by `rfl`-level unfolding of `dvHgt`/`npHgt`
   (both are `⟨height⟩ ∘ dev F.key f`) — a term-mode application, no tactic.
3. Clause three rewrites clause two under the `Finset.inf` binder and crosses the coercion seam
   with `Nat.cast_mul`.

SOURCE: GC-2 (the ruling's verbatim demand: *"must state a reconciliation lemma identifying its
level-1 instance with B's `npHgt`/`suppVal` definitionally"*); CHAP-B H-1 (the seam:
`e₁ = 1, h = 0, dv = addVal, ϖ = π`, twist trivial).

**TEETH.** Signed non-applicable (an interface identity). The DELTA above is the one negative
datum this node produces and it is machine-checked, not asserted.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.05 (a) — the degenerate stage height is the Gauss valuation.** At `F.h = 0` (hence
`F.e₁ = 1` by the frame's coprimality field) the `dv`-normalization collapses:
`dv(A) = min_i v(a_i) = gaussVal A`. -/
theorem KeyFrame.stageHeight_degenerate (F : KeyFrame O π) (hh : F.h = 0)
    (A : Polynomial O) : F.stageHeight A = gaussVal A := by
  have he : F.e₁ = 1 := by
    have hcop := F.hcop
    rw [hh] at hcop
    exact (Nat.coprime_zero_left _).mp hcop
  rw [F.stageHeight_eq_inf A, hh, he]
  simp [gaussVal]

/-- **C.05 (b) — C.06's level heights ARE B.11's polygon heights** at a degenerate frame.
Both sides are `⟨height⟩ (dev F.key f j)`; clause (a) identifies the two heights. -/
theorem dvHgt_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (j : ℕ) :
    dvHgt F f j = npHgt F.key f j :=
  F.stageHeight_degenerate hh (dev F.key f j)

/-- **C.05 (c) — C.06's cleared level support IS B.14's cleared support** at a degenerate frame.
Clause (b) rewritten under the `Finset.inf`, plus `Nat.cast_mul` for the coercion seam
(`(u * j : ℕ∞)` in C.06 versus `((u * j : ℕ) : ℕ∞)` in B.14). -/
theorem dvSupp_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (u ℓ : ℕ) :
    dvSupp F f u ℓ = suppVal F.key f u ℓ := by
  simp only [dvSupp, suppVal, dvHgt_degenerate F hh, Nat.cast_mul]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_degenerate
#print axioms Uniformity.Density.Tower.dvHgt_degenerate
#print axioms Uniformity.Density.Tower.dvSupp_degenerate

end AxCheck
