/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108

/-!
# Uniformity.ChapC.C115 — specializations of `(HT-branch)`: depth zero, and the obstruction row

**Chapter C, NODE C.115** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3/C5**.  `[signed: A-C.1 at the depth-zero clause]` — `ht_depth_zero` is
transcribed VERBATIM from `leanspec/Leanspec/ChapC.lean`.

`[AUDITED: A-C.2 — NO re-sign.]` Verified as predicted: `ht_depth_zero` is a formula-level
identity over `htBranchCount` (both sides read the same node fields), true for an ARBITRARY
node — no set-level content, so the free-field disease behind the C.111/C.114 refutations
cannot reach it.  Tree-level INSTANTIATIONS (which say that some concrete polygon datum
realizes these numbers) inherit C.114's BLOCK; the clause itself stands.

## Clause (iii), the signed one: depth zero

`ht_depth_zero` is the former W-12.A display.  A one-node tree has no non-root `D_v` to deflate
and no internal orbit to account for, so `(HT-branch)` collapses to the single node's own
factor:

    htBranchCount Q census ⟨[v], _⟩ N = κ_v · (∏_{S ∈ v.sides} census λ_{v,S}) · Q ^ (B_v N).

Two things make this a real check rather than a tautology, and both are exactly the places the
formula could have been mis-transcribed: the `drop 1` in `htBranchCount`'s subtracted history
sum must make the ROOT's `D_v` disappear (it does — `[0].drop 1 = []`), and the residual
`Q ^ (B_v N − 0)` must not clip.  The parent map is irrelevant, which is why the signed
statement supplies the junk `fun _ => 0`.

## Clause (i), a fleet companion: the dated-obstruction row

The blueprint's clause (i) is the `H = (1)` then `SPLITEQ(2)` instance: `B_root = D_child =
2N − 5`, root census `S_{(1²)}(q) = q − 1`, leaf census `(q−1)(q−2)/2`, leaf exponent
`2N − 8`, giving `(q−1)·((q−1)(q−2)/2)·q^(2N−8)` — W12-L0's count.  Per the SIGNATURE, the spot
VALUES are §13's executed `htSpot`/`htSpotAlt` rows (the stub gate's D15 block, C.123/C.124's
tables) and the tree-level instantiations are the fleet's companions.  `ht_obstruction_instance`
is that companion, at the formula carrier, and it is scoped honestly:

* the four measured numbers enter as HYPOTHESES on the node data (`root.B N = 2N − 5`,
  `leaf.B N = 2N − 8`, `leaf.D N = 2N − 5`, and the two `κ·census` products).  This node does
  NOT prove that `S_{(1²)}(q) = q − 1` (a C.107 `sideCensus` spot value, §13's row) nor that
  any concrete polygon datum realizes `2N − 5` / `2N − 8` (that is the blocked tree-level
  instantiation);
* what IS proved is the arithmetic the corpus row actually turns on — that a two-node branch in
  which **the root's budget exactly absorbs the child's clipped history** (`B_root = D_child`)
  has total exponent equal to the LEAF's budget alone.  That is the `2N − 8` in the display, and
  it is the one step where a mis-placed `drop 1` (deflating the root instead of the child) would
  produce a different, wrong power of `q`;
* the ℕ-subtractions are the C.53 clip: the statement is true for every `N`, while the corpus's
  row is read at `N ≥ 4`, where `2N − 8` is the genuine value rather than the clip.

Clause (ii) (at multiplicity two `κ_v = 1`, and the exponents telescope to the `(q−1)^t`
factor) is W12-L0's recovery SHAPE; its `κ_v = 1` input is a per-instance orbit computation and
its telescope is C.112's `ht_rec` read at a chain — nothing is claimed for it here.

**DEPENDS.** C.108 (the carrier) · C.107 (the census `λ`-carrier the abstract `census` argument
stands for).  The blueprint also lists C.114, which is BLOCKED — it is needed only for the
tree-level instantiations, not for either statement below.

**SOURCE.** `EFF.W12.87` (the consumer sweep, verbatim rows: the discharge instance, W-12.A
restoration, W12-L0/L1 recovery, the cubic consumers).

**TEETH.** the audited `2N−5` / `2N−8` values → `ht_obstruction_instance` below (the Lean
theorem the blueprint's TEETH line calls for), plus §13's rows at `q = 2` AND `q = 3`.

**ENVIRONMENT.** ENV-C3/C5.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

/-- **NODE C.115 (iii) — the depth-zero specialization** (the former W-12.A display).  A
one-node tree: no non-root `D_v` is deflated and no internal orbit accumulates, so
`(HT-branch)` is the node's own factor `κ_v · (∏_S census λ_{v,S}) · Q ^ (B_v N)`. -/
theorem ht_depth_zero (Q : ℕ) (census : FactorizationType → ℕ) (v : HTNode) (N : ℕ) :
    htBranchCount Q census ⟨[v], fun _ => 0⟩ N
      = v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N := by
  simp [htBranchCount]

/-- **NODE C.115 (i), fleet companion — the dated-obstruction row at the formula carrier**
(`H = (1)` then `SPLITEQ(2)`; `EFF.W12.87`).  With the row's measured node data supplied as
hypotheses — root budget `2N − 5`, leaf budget `2N − 8`, leaf clipped history `2N − 5`, and the
two `κ·census` products `q − 1` and `(q−1)(q−2)/2` — `(HT-branch)` on the two-node branch is
`(q−1)·((q−1)(q−2)/2)·q^(2N−8)`, W12-L0's count.

The content is that `B_root = D_child` makes the total exponent the LEAF budget alone: this is
where a `drop 1` on the wrong end (deflating the root rather than the child) would show up as a
different power of `q`.  The census values themselves are §13's `htSpot` rows and the
realizability of the budgets by a concrete polygon datum is the tree-level instantiation, which
inherits C.114's BLOCK — neither is claimed here. -/
theorem ht_obstruction_instance (q N : ℕ) (census : FactorizationType → ℕ)
    (root leaf : HTNode)
    (hRB : root.B N = 2 * N - 5) (hLB : leaf.B N = 2 * N - 8)
    (hLD : leaf.D N = 2 * N - 5)
    (hRc : root.kappa * (∏ p ∈ root.sides, census (root.sideType p.1 p.2)) = q - 1)
    (hLc : leaf.kappa * (∏ p ∈ leaf.sides, census (leaf.sideType p.1 p.2))
      = (q - 1) * (q - 2) / 2) :
    htBranchCount q census ⟨[root, leaf], fun _ => 0⟩ N
      = (q - 1) * ((q - 1) * (q - 2) / 2) * q ^ (2 * N - 8) := by
  simp only [htBranchCount, List.length_cons, List.length_nil]
  norm_num [hRB, hLB, hLD, hRc, hLc, List.range_succ]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_depth_zero
#print axioms Uniformity.Density.Tower.ht_obstruction_instance

end AxCheck
