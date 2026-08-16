/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E15
import Uniformity.ChapE.E47
import Uniformity.ChapE.E49

/-!
# Uniformity.ChapE.E67 — the `e > 1 ∧ f > 1` witness, EXECUTED

**Chapter E, NODE E.67** [gate] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §10, the executable
gates; GC-11's simultaneous-witness requirement). ENV-E1. The file signs NO new declaration — it
is executed `example`s over the landed defs and theorems of E.15/E.45/E.46/E.47/E.49.

**What GC-11 asks for here.** A gate battery that only ever exercises `e = 1` or `f = 1` cannot
catch an `e`/`f` transposition, nor a law that silently assumes one of the two invariants is
trivial. The witness must have BOTH components `> 1`, and it must sit INSIDE the certified
perimeter — not be invented for the gate. Both are met by the n = 8 frame's dictionary row 2:
`mu2Sigma .oneSideInert = ⟨{(4, 2)}⟩` (`EFF.HE7.58` row 2, `λ₂ ∈ ℤ` with `R₂` an irreducible
quadratic), a real member class of Q1's battery, with `e = 4 > 1` and `f = 2 > 1`.

**The same letter, reached the other way.** A level-2 frame with `d_r = 2` over the base
`(e₁, f₁) = (2, 1)` with `ℓ = 2` composes to `(e_𝒞, f_𝒞) = (e₁ℓ, f₁d_r) = (4, 2)`: the leaf
`⟨[(2,1)], (1,2)⟩` read at base `(2, 1)` (E.45's `EFF.HE7.48` display). So the witness is
produced by the ladder machinery, not just quoted from the table — the two routes agreeing is
the check.

## The checks

1. `LadderLeaf.ef` at the leaf and base above evaluates to `(4, 2)` — and both components are
   `> 1` (the GC-11 witness itself, stated as an inequality so a transposition to `(2, 4)` still
   passes but a collapse to `(8, 1)` or `(1, 8)` does not);
2. the dictionary's row 2 carries the same letter (`EFF.HE7.58`), so the witness is inside the
   certified perimeter;
3. `ladderSigma … .degree = 4·2 = 8`, the frame's `n` — fired both by `decide` and through
   E.46's `ladderSigma_degree`;
4. E.47's transport law at the same data (`ladderSigma_prepend`), fired both by `decide` and as
   the THEOREM applied and pushed through `.data`;
5. E.15's `ef_forcing` at `(a, b) = (4, 2)` with `e·f = 8` — the `(FUND)` forcing chain at the
   witness.

## ⚠ GC-11 GATE-SPELLING RIDER (A-E.1/E-D10), in force here

**No gate may `decide` an equation between σ-VALUES.** `Uniformity.FactorizationType`'s
`DecidableEq` is `Classical.decEq` (noncomputable, `Uniformity/Density/LocalData.lean`), so
`decide` gets stuck on `Classical.choice`. Check 4 — E.47's `ladderSigma_prepend` spot check — is
therefore stated on `.data` (`Multiset (ℕ × ℕ)`, a real instance), never on the σ-values
themselves. Unaffected and still directly decidable: degrees (`FactorizationType.degree`, ℕ) and
`Option`-valued dictionary rows (`mu2Sigma … = some ⟨…⟩` by `rfl`). A gate that `decide`s a bare
σ-equation is a stub-stage defect, not a tactic-choice problem.

No `native_decide` anywhere (repo policy).

**DEPENDS.** E.15 (`ef_forcing`), E.45 (`LadderLeaf`, `.ef`, `ladderSigma` — transitively),
E.46 (`ladderSigma_degree` — transitively), E.47 (`LadderLeaf.prepend`, `ladderSigma_prepend`),
E.49 (`mu2Sigma`, the dictionary rows). Imported as E.15 + E.47 + E.49, which cover all five.

**SOURCE.** `EFF.HE7.58` row 2 (`{(4,2)}` — a certified alphabet letter with `e, f > 1`); GC-11
(the CHAP-B §10 shape).

**TEETH.** Q1's `{(4,2)}` members (the letter occurs in the battery) → the gate re-fires the
value Lean-side. Retained regression: `verification/chapE_gate_ef.py`.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free: the file declares nothing, and every `example` closes by `decide`,
`rfl`, `norm_num`, or an application of a landed lemma.
-/

namespace Uniformity.Density.Ladder

open Uniformity

/-! ## Check 1 — the witness leaf composes to `(4, 2)`, both components `> 1` -/

/-- The level-2 frame `(e₁, f₁) = (2, 1)`, `ℓ = 2`, `d_r = 2`: the leaf `⟨[(2,1)], (1,2)⟩` read at
base `(2, 1)` composes to `(e_𝒞, f_𝒞) = (e₁ℓ, f₁d_r) = (2·2·1, 1·1·2) = (4, 2)` (E.45's
`EFF.HE7.48` display). -/
example : (LadderLeaf.mk [(2, 1)] (1, 2)).ef 2 1 = (4, 2) := by decide

/-- **The GC-11 simultaneous witness itself**: at that leaf BOTH invariants exceed 1. A battery
that never leaves `e = 1` or `f = 1` cannot score the `(e, f)` bookkeeping; this line is the one
that makes the frame admissible. -/
example : 1 < ((LadderLeaf.mk [(2, 1)] (1, 2)).ef 2 1).1
    ∧ 1 < ((LadderLeaf.mk [(2, 1)] (1, 2)).ef 2 1).2 := by decide

/-! ## Check 2 — the same letter is a certified dictionary row (inside the perimeter) -/

/-- `EFF.HE7.58` row 2 (`λ₂ ∈ ℤ`, `R₂` an irreducible quadratic) at the n = 8 frame: the value is
the letter `{(4, 2)}`. So the witness above is a REAL member class of Q1's battery, not a frame
invented for the gate. -/
example : mu2Sigma .oneSideInert = some ⟨{(4, 2)}⟩ := rfl

/-- The row's letter has both invariants `> 1`, read off the row rather than off the leaf — the
two routes to `(4, 2)` agree. -/
example : ((mu2Sigma .oneSideInert).map (fun σ => σ.data)) = some {(4, 2)} := rfl

/-- … and it is the only decided row of the n = 8 dictionary with `f > 1`: rows 1, 3, 4, 6 read
`{(8,1)}`, `{(4,1),(4,1)}`, so a gate built on them alone would never see `f > 1`. -/
example : mu2Sigma .oneSideHalf = some ⟨{(8, 1)}⟩ := rfl

example : mu2Sigma .oneSideSplit = some ⟨{(4, 1), (4, 1)}⟩ := rfl

/-! ## Check 3 — degree conservation at the witness: `4·2 = 8`, the frame's `n` -/

/-- The emission `{⟨[(2,1)], (1,2)⟩}` read at base `(2, 1)` has degree `4·2 = 8`. (`ℕ`-valued, so
directly decidable — the E-D10 rider does not bite.) -/
example : (ladderSigma 2 1 {LadderLeaf.mk [(2, 1)] (1, 2)}).degree = 8 := by decide

/-- The same value PREDICTED by E.46's degree law rather than computed: the degree is the
leaf-wise `e·f` sum at the same base. -/
example : (ladderSigma 2 1 {LadderLeaf.mk [(2, 1)] (1, 2)}).degree
    = (({LadderLeaf.mk [(2, 1)] (1, 2)} : Multiset LadderLeaf).map fun l =>
        (l.ef 2 1).1 * (l.ef 2 1).2).sum :=
  ladderSigma_degree 2 1 _

/-- … and the row's own degree, through E.49's GC-4 law: row 2's value has degree 8 too. -/
example : (⟨{(4, 2)}⟩ : Uniformity.FactorizationType).degree = 8 :=
  mu2Sigma_degree .oneSideInert _ rfl

/-! ## Check 4 — E.47's transport law at the same data (on `.data`, per the E-D10 rider) -/

/-- Leaf level: prepending the rung `(2, 1)` to the depth-0 leaf `⟨[], (1,2)⟩` is the same as
descending the base by that rung (`ℕ × ℕ`-valued, directly decidable). -/
example : (LadderLeaf.prepend (2, 1) (LadderLeaf.mk [] (1, 2))).ef 1 1
    = (LadderLeaf.mk [] (1, 2)).ef (1 * 2) (1 * 1) := by decide

/-- Leaf level again, PREDICTED by E.47's `LadderLeaf.ef_prepend` rather than computed. -/
example : (LadderLeaf.prepend (2, 1) (LadderLeaf.mk [] (1, 2))).ef 1 1
    = (LadderLeaf.mk [] (1, 2)).ef (1 * 2) (1 * 1) :=
  LadderLeaf.ef_prepend (2, 1) _ 1 1

/-- Dictionary level, the associativity spot check — **on `.data`, never between σ-values**
(A-E.1/E-D10): reading the emission with the rung recorded on the leaf equals reading it at the
base already multiplied by the rung. -/
example : (ladderSigma 2 1 (({LadderLeaf.mk [] (1, 2)} : Multiset LadderLeaf).map
      (LadderLeaf.prepend (2, 1)))).data
    = (ladderSigma (2 * 2) (1 * 1) {LadderLeaf.mk [] (1, 2)}).data := by decide

/-- The same identity obtained by FIRING E.47's theorem and pushing it through `.data` — no
decidability of σ-values is invoked anywhere in this proof term, which is exactly what the E-D10
rider asks a consumer of the law to do. -/
example : (ladderSigma 2 1 (({LadderLeaf.mk [] (1, 2)} : Multiset LadderLeaf).map
      (LadderLeaf.prepend (2, 1)))).data
    = (ladderSigma (2 * 2) (1 * 1) {LadderLeaf.mk [] (1, 2)}).data :=
  congrArg Uniformity.FactorizationType.data (ladderSigma_prepend 2 1 (2, 1) _)

/-- The transported emission is the WITNESS emission: both sides read `{(4, 2)}`, degree 8. So
check 4 is fired at the `e > 1 ∧ f > 1` letter and not at a degenerate one. -/
example : (ladderSigma (2 * 2) (1 * 1) {LadderLeaf.mk [] (1, 2)}).data = {(4, 2)} := by decide

/-! ## Check 5 — E.15's `(FUND)` forcing chain at the witness `(a, b) = (4, 2)` -/

/-- `ef_forcing` at `(a, b) = (4, 2)`, `e·f = 8 = a·b`: equality in `(FUND)` forces equality in
both local divisibilities, so the witness letter is pinned componentwise — an `(8, 1)`/`(4, 2)`
confusion at the same degree cannot survive the chain. -/
example : (4 : ℕ) = 4 ∧ (2 : ℕ) = 2 :=
  ef_forcing (by norm_num) (by norm_num) dvd_rfl dvd_rfl (by norm_num)

/-- The chain fired at the same degree with a DIFFERENT divisor pair, as the negative control on
its hypotheses: at `(a, b) = (2, 4)` the multiples `e = 4`, `f = 8` do NOT satisfy
`e·f = a·b` (`32 ≠ 8`), so the conclusion is not available — the `(FUND)` equality hypothesis is
load-bearing, not decoration. -/
example : ¬ ((4 : ℕ) * 8 = 2 * 4) := by decide

end Uniformity.Density.Ladder
