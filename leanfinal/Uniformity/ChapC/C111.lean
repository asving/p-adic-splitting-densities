/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108

/-!
# Uniformity.ChapC.C111 — Step 3: the fiber exponent, at the arithmetic shadow

**Chapter C, NODE C.111** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1 AT THE ARITHMETIC SHADOW; re-signed: A-C.2,
2026-08-16]` — the signed signature is transcribed VERBATIM from `leanspec/Leanspec/ChapC.lean`
(`ht_fiber_exponent_nonneg`), in its **re-signed** form.

## What was refuted, and what this node therefore is

The corpus's step 3 (`EFF.W12.85`) produces the fiber decomposition
`E_v(𝐑) ≃ U_v(𝐑) × ∏_{u child} C_{m_u}(s_u)` with `#U_v(𝐑) = Q ^ (B_v(N) − Σ_u D_u(N))` and
remarks that *"the exponent is a nonnegative integer"*.  The FROZEN signature tried to read
that remark as a property of the tree DATUM (hypotheses `hwf` + `hvis` only). That is false and
machine-refuted: `leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`, `c111_frozen_false`
— the tree data tie a child's previous-center depth `s_u` to nothing, so a child at `s = 0` has
`D = m(N−1)` while a steep polygon drives every `B` to `0`; per-node `HTNode.WF` does not
rescue it either (numeric leg `[C111]` of the certification, the WF-resistant instance).

Nonnegativity of the fiber exponent is a property of REALIZED nodes — it comes out of the
bijection, not out of arithmetic.  So the honest arithmetic shadow, which is what this node is,
**carries the per-node inequality as the hypothesis `hnode`** (discharged by the fleet's
multiplication bijection at realized nodes) and keeps as its own content the one thing that IS
arithmetic: the telescope over the parent map.  `hvis` was DROPPED as dead weight at the
re-sign (A-F.12 minimality: never instantiable content).

## What the statement says

Given, for EVERY node index `i`, that its children's clipped history counts fit inside its own
digit budget,

    Σ_{u : parent u = i} D_u(N) ≤ B_i(N)        (`hnode`),

the same holds in TOTAL, over the whole tree, with the root's `B` still on the right and the
root's `D` (which is never deflated) absent from the left:

    Σ_{u ≠ root} D_u(N) ≤ Σ_{v} B_v(N).

That total inequality is exactly the `hBD` hypothesis of C.112 (`ht_rec`), and it is what makes
the ℕ-subtraction in `htBranchCount`'s exponent genuine rather than clipped.  So the §11 chain
runs: the fleet's bijection ⟹ `hnode` at realized nodes ⟹ (this node) ⟹ `hBD` ⟹ C.112's
division-free `(HT-rec)`.

Index conventions, all C.108's: nodes are read totally as `t.nodes.getD i HTNode.default0` over
`List.range t.nodes.length`, the non-root indices are `(List.range t.nodes.length).drop 1`
(index `0` is the root), and `t.parent` is the parent map, read only on `1 … length − 1`.

## The proof, and where `hwf` is load-bearing

The content is a fiberwise regrouping of one ℕ-sum:

1. **The fibers of `parent` partition the non-root indices** (`sum_fiber_telescope` below, a
   list induction): for any list `R` whose `parent`-image lands in a NODUP list `L`,
   `Σ_{u ∈ R} f u = Σ_{i ∈ L} Σ_{u ∈ R, parent u = i} f u`.  Nodup-ness of `L` is what makes
   each `u` counted exactly once (the induction step's isolated term is
   `Σ_{i ∈ L} [parent x = i]·f x = f x`, which needs `parent x ∈ L` AND no repeats).
2. **`hwf` supplies the hypothesis of step 1**, and this is the only place it is used — but it
   is genuinely load-bearing, not decoration: `t.WF` says `parent u < u` for every non-root `u`,
   so `parent u < u < t.nodes.length` and every fiber lands in `List.range t.nodes.length`.
   Without it a node could parent-point out of range, its `D` would appear on the left of the
   conclusion but in NO fiber on the right, and the inequality would fail.
3. **Termwise comparison** (`List.sum_le_sum`) against `hnode`, one node index at a time.

`L = List.range t.nodes.length` is nodup by `List.nodup_range`; the non-root list is identified
as `List.range' 1 (length − 1)` (`List.range_eq_range'` + `List.drop_range'`) purely to read off
`1 ≤ u < length` for its members.

## What this node does NOT ship

Everything set-level in the blueprint's step-3 STATEMENT: the multiplication linearization
`(A_α) ↦ Σ_α A_α ∏_{β≠α} Ḡ_β` being an isomorphism at each weighted digit height (the W12-S2.1
mechanism = B.37–B.40's `GradedCoprime` engine at the weighted grading), the finite-window
multiplication bijection obtained by solving height by height, and the fiber decomposition
`E_v(𝐑) ≃ U_v(𝐑) × ∏_u C_{m_u}(s_u)` itself.  Those remain the BOOKED B.37–B.40
weighted-grading RE-PLAN, and they are what will DISCHARGE `hnode` — they are not asserted
here.  Note also the §16 faithfulness flag recorded at the blueprint node: in the factor
representation the simultaneity of the child coordinates is factorization uniqueness (landed
`monic_factorization_unique`), so the corpus's GENIND-1 / fracture-permanence consumption
(`HYP.121`) is discharged representation-side and is **NOT inherited** by this chain.

**DEPENDS.** C.108 (all carriers).  The blueprint's DEPENDS (C.109 · C.110 · B.37–B.40 ·
`monic_factorization_unique`) belong to the set-level assembly that the A-C.2 re-sign moved out
of the statement; the arithmetic shadow names none of them, which is why this node lands ahead
of C.109.

**SOURCE.** `EFF.W12.85` step 3 (verbatim, incl. the nonnegativity remark).

**TEETH.** 322 coprime-multiplication-rank tests → retained; they bite on the bijection that
discharges `hnode`, NOT on the telescope proved here.  The A-C.2 refutation
(`C111_C114_REFUTATION.lean.txt`) is this node's own standing tooth: it is what forbids
re-freezing the statement without `hnode`.

**ENVIRONMENT.** ENV-C3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

/-- **the fiber telescope.**  If every `p`-image of `R` lies in the NODUP list `L`, then summing
`f` over `R` is the same as summing, over `L`, the `f`-sums of the `p`-fibers.  (Stated over `ℕ`
because that is where §11's counts live; `L.Nodup` is essential — with repeats in `L` the
right-hand side over-counts.) -/
private theorem sum_fiber_telescope (L : List ℕ) (hL : L.Nodup) (p f : ℕ → ℕ) :
    ∀ R : List ℕ, (∀ u ∈ R, p u ∈ L) →
      (R.map f).sum
        = (L.map (fun i => ((R.filter (fun u => p u == i)).map f).sum)).sum := by
  intro R
  induction R with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hp
    have hx : p x ∈ L := hp x (List.mem_cons_self ..)
    have hxs : ∀ u ∈ xs, p u ∈ L := fun u hu => hp u (List.mem_cons_of_mem _ hu)
    -- the head contributes to exactly one fiber, the one indexed by `p x`
    have hstep : ∀ i : ℕ,
        (((x :: xs).filter (fun u => p u == i)).map f).sum
          = (if p x = i then f x else 0) + ((xs.filter (fun u => p u == i)).map f).sum := by
      intro i
      by_cases h : p x = i <;> simp [h]
    simp only [hstep]
    rw [List.sum_map_add, List.map_cons, List.sum_cons, ih hxs]
    congr 1
    -- `Σ_{i ∈ L} [p x = i]·f x = f x` — this is the step that consumes `L.Nodup`
    rw [← List.sum_toFinset _ hL]
    simp [hx]

/-- **NODE C.111 — step 3's arithmetic shadow (re-signed A-C.2).**  From the PER-NODE fiber
inequality `Σ_{u child of i} D_u(N) ≤ B_i(N)` at every node index, the TOTAL inequality
`Σ_{u ≠ root} D_u(N) ≤ Σ_v B_v(N)` — i.e. exactly C.112's `hBD`.  The per-node hypothesis is
what the corpus's fiber bijection supplies at realized nodes; the frozen hypothesis-free form is
machine-refuted (`C111_C114_REFUTATION.lean.txt`). -/
theorem ht_fiber_exponent_nonneg (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hnode : ∀ i, i < t.nodes.length →
      ((((List.range t.nodes.length).drop 1).filter (fun u => t.parent u == i)).map
        (fun u => (t.nodes.getD u HTNode.default0).D N)).sum
        ≤ (t.nodes.getD i HTNode.default0).B N) :
    (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum := by
  -- `hwf` (acyclicity: `parent u < u`) is exactly "every fiber lands in `range length`"
  have hmem : ∀ u ∈ (List.range t.nodes.length).drop 1,
      t.parent u ∈ List.range t.nodes.length := by
    intro u hu
    rw [List.range_eq_range', List.drop_range'] at hu
    simp only [List.mem_range'_1] at hu
    simp only [List.mem_range]
    exact lt_trans (hwf u (by omega) (by omega)) (by omega)
  rw [sum_fiber_telescope (List.range t.nodes.length) (List.nodup_range) t.parent
      (fun i => (t.nodes.getD i HTNode.default0).D N)
      ((List.range t.nodes.length).drop 1) hmem]
  refine List.sum_le_sum ?_
  intro i hi
  exact hnode i (List.mem_range.mp hi)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_fiber_exponent_nonneg

end AxCheck
