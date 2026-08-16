/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108

/-!
# Uniformity.ChapC.C112 — Step 4: `(HT-rec)` in division-free form

**Chapter C, NODE C.112** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1]` — the signed signature is transcribed VERBATIM
from `leanspec/Leanspec/ChapC.lean` (`ht_rec`), including the two binders the proof does not
read (`hQ`, `hwf`; signature fence, hence the local `linter.unusedVariables` suppression).

`[AUDITED: A-C.2 — NO re-sign.]` The audit's prediction, verified here: `ht_rec` carries its
inequality as the explicit hypothesis `hBD` and is pure algebra over the formula carrier, true
for arbitrary trees given `hBD` — the hypothesis-carrying discipline that the frozen C.111
lacked.  `hBD` is supplied by the re-signed C.111 (`ht_fiber_exponent_nonneg`, whose per-node
`hnode` the fleet discharges at realized nodes).

## What the statement says

The corpus's step-4 recursion (`EFF.W12.85`) is displayed with a division:

    #(v) = Q ^ (B_v(N)) · (∏_S S_{λ_{v,S}}(Q_i)) · κ_v · ∏_{u child} #(u) / Q ^ (D_u(N)),

each child contributing its own count deflated by its clipped history count `D_u(N)`.  Unrolled
over the whole tree the divisions telescope, and what survives is the identity this node states
— **with no division anywhere**, both sides in `ℕ`:

    htBranchCount Q census t N · Q ^ (Σ_{u ≠ root} D_u(N))
      = ∏_{v ∈ t} ( κ_v · (∏_{S ∈ v.sides} census (λ_{v,S})) · Q ^ (B_v(N)) ).

Term by term, against the C.108 carriers (all landed there):

* the index set is `List.range t.nodes.length` and every node read is
  `t.nodes.getD i HTNode.default0` — the total, index-encoded read of C.108's `HTTree`
  (`HTNode.default0` is junk, never data: it is reached only at out-of-range indices, which
  `List.range t.nodes.length` never produces);
* `v.B N = m_v·N − Σ_{j<m_v} ⌈P_v(j)⌉ − L_v` is the node's free digit budget and `v.D N =
  Σ_{j<m_v} max(N − ((m_v−j)s_v + 1), 0)` its clipped history count — both ℕ-subtraction, the
  C.53 clip discipline;
* `v.kappa` is the SIDE-TAGGED orbit factor `κ_v = ∏_{S,a} r_{v,S,a}!/∏_H r_{v,S,a,H}!` (the
  side tag is necessary: roots on different sides cannot be permuted), and
  `∏ p ∈ v.sides, census (v.sideType p.1 p.2)` is the per-side residual census `∏_S
  S_{λ_{v,S}}(Q_i)` — `census` abstracts C.107's `sideCensus (resField Φ)`, so this node is
  base-field-free;
* the `drop 1` on the left is the corpus's "the root is not deflated": only CHILDREN carry a
  `/Q ^ D_u`, so the root's `D` never appears.  `htBranchCount` (C.108) already carries that
  asymmetry in its exponent `Σ_v B_v(N) − Σ_{u ≠ root} D_u(N)`.

## Why the division-free form is the honest one, and where `hBD` comes from

`htBranchCount`'s exponent is an ℕ-subtraction.  If `Σ_{u ≠ root} D_u(N)` exceeded
`Σ_v B_v(N)` the subtraction would clip to `0` and the displayed count would be silently wrong
(too large), so the recursion is an identity only on the region where the exponent is genuine.
That region is exactly `hBD`, and this node takes it as a hypothesis rather than asserting it:
nonnegativity of the fiber exponent is not arithmetic, it is the content of the fiber bijection
(`EFF.W12.85`: `#U_v(𝐑) = Q ^ (B_v(N) − Σ_u D_u(N))`, "the exponent is a nonnegative integer"),
and the A-C.2 refutation (`C111_C114_REFUTATION.lean.txt`) showed that no amount of
well-formedness on the tree datum implies it.  C.111 supplies `hBD` from the PER-NODE
inequality `Σ_{u child of i} D_u(N) ≤ B_i(N)`, which the fleet discharges at realized nodes.

## The proof

Three moves, all in `ℕ`:

1. the right-hand product splits, `List.prod_map_mul`, into the orbit-times-census product and
   the pure `Q`-power product;
2. the `Q`-power product collapses to a single power of the total budget,
   `(l.map fun i => Q ^ f i).prod = Q ^ (l.map f).sum` (the local `prod_map_pow_eq_pow_sum`,
   a two-line list induction — there is no `List` twin of `Finset.prod_pow_eq_pow_sum` in
   mathlib);
3. on the left, `Q ^ (ΣB − ΣD) · Q ^ (ΣD) = Q ^ ((ΣB − ΣD) + ΣD) = Q ^ (ΣB)` by
   `Nat.sub_add_cancel hBD` — the ONE place `hBD` is consumed.

## What this node does NOT ship

The blueprint's step-4 STATEMENT also asserts concatenation-compatibility (child tuples
compose; unitriangular translations compose) and fracture-compatibility (factorization
uniqueness identifies the same cluster before and after sibling operations).  Those are
SET-LEVEL claims about the counted objects, not about the formula carrier, and they are the
fleet's proof content behind `ht_branch` (C.114) — which is **BLOCKED** at A-C.2 (both of its
count axioms machine-refuted as frozen; `C111_C114_REFUTATION.lean.txt`).  Nothing here
depends on them, and nothing here discharges them: this node is the arithmetic shadow of the
recursion and says so.

**DEPENDS.** C.108 (all carriers) · C.109/C.111 supply `hBD`'s realized form and the cell
counts the formula abstracts — as HYPOTHESIS suppliers, not as names in this statement, which
is why this node lands ahead of them.

**SOURCE.** `EFF.W12.85` step 4.

**TEETH.** DROP-KAPPA0 (370) + DROP-HISTORY-CENSUS (302) → retained (they kill the
κ-omission mutants); both bite at the `htBranchCount` carrier (C.108), which reads `kappa` and
the per-side censuses, and this identity transports them to the per-node product form.

**ENVIRONMENT.** ENV-C3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

/-- `(l.map fun i => a ^ f i).prod = a ^ (l.map f).sum` — the `List` twin of
`Finset.prod_pow_eq_pow_sum` (mathlib has the `Finset` and `Multiset` forms; this one is not
in the library at v4.31.0). -/
private theorem prod_map_pow_eq_pow_sum {ι : Type*} (a : ℕ) (l : List ι) (f : ι → ℕ) :
    (l.map (fun i => a ^ f i)).prod = a ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [pow_add, ih]

-- `hQ` and `hwf` are part of the A-C.1-signed signature and are kept VERBATIM (signature
-- fence) even though the proof does not consume them: the identity is pure algebra over the
-- formula carrier, true for an arbitrary base `Q` and an arbitrary tree, GIVEN `hBD`.
set_option linter.unusedVariables false in
/-- **NODE C.112 — `(HT-rec)`, step 4, division-free.**  Over the C.108 formula carrier, the
branch count deflated by the children's total clipped history equals the plain product of the
per-node factors `κ_v · (∏_S census λ_{v,S}) · Q ^ (B_v(N))`.  The corpus's per-child division
`#(u)/Q ^ (D_u(N))` telescopes; `hBD` (supplied by C.111) is what makes the ℕ-subtraction in
`htBranchCount`'s exponent genuine rather than clipped. -/
theorem ht_rec (Q : ℕ) (hQ : 2 ≤ Q) (census : FactorizationType → ℕ)
    (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hBD : (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum) :
    htBranchCount Q census t N
        * Q ^ (((List.range t.nodes.length).drop 1).map
            (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      = ((List.range t.nodes.length).map (fun i =>
          let v := t.nodes.getD i HTNode.default0
          v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N)).prod := by
  -- move 1+2: the per-node product splits, and its `Q`-part collapses to `Q ^ (Σ_v B_v N)`
  have hRHS :
      ((List.range t.nodes.length).map (fun i =>
          let v := t.nodes.getD i HTNode.default0
          v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N)).prod
        = ((List.range t.nodes.length).map (fun i =>
            let v := t.nodes.getD i HTNode.default0
            v.kappa * ∏ p ∈ v.sides, census (v.sideType p.1 p.2))).prod
          * Q ^ ((List.range t.nodes.length).map
              (fun i => (t.nodes.getD i HTNode.default0).B N)).sum := by
    rw [List.prod_map_mul, prod_map_pow_eq_pow_sum]
  -- move 3: `Q ^ (ΣB − ΣD) * Q ^ ΣD = Q ^ ΣB`, the one use of `hBD`
  rw [hRHS, htBranchCount, mul_assoc, ← pow_add, Nat.sub_add_cancel hBD]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_rec

end AxCheck
