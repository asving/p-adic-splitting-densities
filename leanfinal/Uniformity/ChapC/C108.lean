/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B29
import Uniformity.ChapC.C107

/-!
# Uniformity.ChapC.C108 — the order-1 refinement tree and its node quantities

**Chapter C, NODE C.108** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT count
layer), **ENV-C3**.  The datum `(HT-rec)` / `(HT-branch)` / `(HT-global)` are stated over: a
finite refinement tree per repeated branch, each node carrying its multiplicity, its previous
center depth, its (ceiled) polygon and its per-side residual types, together with the three
node quantities `B_v`, `D_v`, `κ_v` and the two conservative/exact cells.

* `HTNode` — the node datum (`m_v`, `s_v`, `P_v` ceiled, `L_v`, `sides`, `sideType`, `kappa`).
* `HTNode.B v N = m·N − Σ_{j<m} ⌈P_v(j)⌉ − L_v` — the digit budget of the node cell.
* `HTNode.D v N = Σ_{j<m} max(N − ((m−j)s + 1), 0)` — the clipped history count.
* `HTTree` (+ `HTTree.WF`) — the index-encoded tree; `HTShape` — the level-0 shape.
* `conservativeCell m s` — `C_m(s) = {(a_j) : v(a_j) ≥ (m−j)s + 1}`, on `ℕ∞`-height data.
* `htCell π Φ v` — the EXACT node cell: pinned polygon plus prescribed per-side residual types.
* `htBranchCount`, `htGlobalCount` — the `(HT-branch)`/`(HT-global)` display arithmetic,
  machine-typed.  The laws that tie them to realization strata are C.114's, not this node's.

## The A-C.1 determinations transcribed here (signed; divergences from the prose STATEMENT)

1. **The tree is INDEX-ENCODED, not nested-inductive.**  `nodes : List HTNode` with
   `parent : ℕ → ℕ`, root `= 0`, and well-formedness `HTTree.WF t : ∀ i, 0 < i → i < length →
   parent i < i`.  The strict decrease is simultaneously acyclicity and a structural-recursion
   licence for every consumer; no nested inductive type is introduced (GC-4).
2. **`Pceil : ℕ → ℕ`, not `ℚ`.**  The polygon data is carried CEILED, which is the only form
   the count formulas read (`B_v` sums `⌈P_v(j)⌉`).  This keeps §11 `ℚ`-free, per the
   STATEMENT's own parenthetical; the un-ceiled argmin heights live in C.06/C.07's carriers and
   reach a node through `htCell`'s `npHgt` clause, which pins `npHgt Φ f j = (Pceil j : ℕ∞)`.
3. **`κ_v` is a DATA field, not a computed expression.**  The corpus's side-tagged factorial
   rule `κ_v = ∏_{S,a} r_{v,S,a}! / ∏_H r_{v,S,a,H}!` is the corpus's computation and is
   recorded in the field docstring; the count formulas consume the value.  **The side tag is
   MANDATORY** — roots lying on different sides of the node polygon cannot be permuted, so an
   untagged orbit factor is simply the wrong number.  C.116's manifest keeps the tag visible;
   the DROP-teeth guard it.
4. **`sides : Finset (ℕ × ℕ)` with `sideType : ℕ → ℕ → FactorizationType`** — a side is its
   cleared slope pair `(u, ℓ)`, and `sideType` is junk off `sides` (the junk-total discipline).
5. **`HTNode.D`'s clip is ℕ-subtraction.**  The STATEMENT writes `max(N − ((m−j)s + 1), 0)`;
   over `ℕ` truncated subtraction IS that max, which is the same discipline as C.53.  Nothing
   here may be read over `ℤ`.
6. **`HTNode.default0` and `Inhabited HTTree`** exist only so the index-encoded reads
   (`nodes.getD i`, `branches.getD i`) are total; they are junk defaults, never data.

## What is NOT encoded on `HTTree` (an honest scope note)

The STATEMENT's order-1 fence — *children are the repeated LINEAR factors on `e = 1` sides;
repeated factors of degree `> 1`, or on `e > 1` sides, are NOT children because they open
composite stages* — is **not** a field of `HTTree` here.  `HTTree.WF` is acyclicity alone.  The
fence is carried downstream by the realization predicate (C.114's `htRealizes`), where a child
is required to keep its parent's key DEGREE while recentering it — i.e. exactly "no degree
enlargement, hence no composite stage".  A reader must not infer from `HTTree.WF` that a
well-formed tree is order-1 admissible; that is a property of the realizing pair, not of the
combinatorial datum.

## What this node does NOT ship

No count law.  `htBranchCount`/`htGlobalCount` are DEFINITIONS of the display arithmetic; that
they compute the cardinalities of the realization strata is C.114 (`(HT-branch)`,
`(HT-global)`), and the depth-zero specialization is C.115.  The exact node-cell cardinality is
C.109.

**DEPENDS.** C.06/C.07 (polygon carriers, by shape) · C.107 (`residualTypeOf`, and
`FactorizationType`'s use as the value of `λ`) · landed `Coeff`/`proj` (consumed at C.109, not
here) · chapter B's `npHgt`/`sideSet`/`sideMin`/`resPoly`/`resField` (GC-2's literal reuse).

**PROOF.** Definitional.

**SOURCE.** `EFF.W12.83` (the setting, verbatim: the datum, `B_v`, `D_v`, `C_{m_v}(s_v)`, and
`(HT-orbit)` with the side-tag rationale and the `side_index` convention note).

**TEETH.** the N1 certificate's `side_index` grouping → the side tag is guarded by DROP-teeth
(C.116's manifest).

**ENVIRONMENT.** ENV-C3.

## Status

Definitional (no proof obligation).  Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **NODE C.108 — a node of the order-1 refinement tree.**  All of `EFF.W12.83`'s per-node
datum: multiplicity, previous center depth, ceiled polygon, integral-boundary count, the sides
with their residual types, and the side-tagged orbit factor. -/
structure HTNode where
  /-- multiplicity `m_v`. -/
  m : ℕ
  /-- previous center depth `s_v` (`0` at the root). -/
  s : ℕ
  /-- the exact polygon data, CEILED (`⌈P_v(j)⌉` — ℕ-computable from the cleared argmin). -/
  Pceil : ℕ → ℕ
  /-- the integral-boundary count `L_v`: the number of integral boundary positions, each of
  which prices one digit by the residual. -/
  L : ℕ
  /-- the sides `(u, ℓ)` of the node polygon (cleared slope pairs). -/
  sides : Finset (ℕ × ℕ)
  /-- the per-side residual types `λ_{v,S}` (junk off `sides`). -/
  sideType : ℕ → ℕ → FactorizationType
  /-- the SIDE-TAGGED orbit factor `κ_v = ∏_{S,a} r_{v,S,a}!/∏_H r_{v,S,a,H}!`, as data (the
  factorial rule is the corpus's computation; the side tag is NECESSARY — roots on different
  sides cannot be permuted). -/
  kappa : ℕ

/-- the junk default for the total index-encoded reads (`nodes.getD`); never data. -/
def HTNode.default0 : HTNode := ⟨0, 0, fun _ => 0, 0, ∅, fun _ _ => ⟨0⟩, 1⟩

/-- `B_v(N) = m·N − Σ_{j<m} ⌈P_v(j)⌉ − L_v` — the free digit budget of the node cell. -/
def HTNode.B (v : HTNode) (N : ℕ) : ℕ :=
  v.m * N - (∑ j ∈ Finset.range v.m, v.Pceil j) - v.L

/-- `D_v(N) = Σ_{j<m} max(N − ((m−j)s + 1), 0)` — the CLIP is ℕ-subtraction (C.53's
discipline). -/
def HTNode.D (v : HTNode) (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range v.m, (N - ((v.m - j) * v.s + 1))

/-- the index-encoded finite tree: node `0` is the root; `parent i < i` is well-formedness. -/
structure HTTree where
  /-- the nodes, indexed by position; index `0` is the root. -/
  nodes : List HTNode
  /-- the parent map; only its values on `1 … length − 1` are read. -/
  parent : ℕ → ℕ

/-- well-formedness: every non-root index has a strictly smaller parent (acyclicity, and the
structural-recursion licence for consumers). -/
def HTTree.WF (t : HTTree) : Prop :=
  ∀ i, 0 < i → i < t.nodes.length → t.parent i < i

/-- the conservative cell `C_m(s)` on `ℕ∞`-height data: `v(b_j) ≥ (m−j)s + 1`. -/
def conservativeCell (m s : ℕ) : Set (ℕ → ℕ∞) :=
  {P | ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ P j}

/-- the exact node cell on members: pinned polygon + prescribed per-side residual types.
(`π` explicit — it appears only in the membership predicate; the domain/UFD instances on
`resField Φ` are derivable from `IsKey Φ` via B.25's field structure at every consumer, and are
taken as binders here.) -/
def htCell (π : O) (Φ : Polynomial O) [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] (v : HTNode) :
    Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = v.m * Φ.natDegree ∧
    (∀ j, j ≤ v.m → npHgt Φ f j = (v.Pceil j : ℕ∞)) ∧
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → (u, ℓ) ∈ v.sides →
      ∀ (hne : (sideSet Φ f u ℓ).Nonempty) (H₀ : ℕ),
        npHgt Φ f (sideMin Φ f u ℓ hne) = (H₀ : ℕ∞) →
        residualTypeOf (resPoly π Φ f u ℓ hne H₀) = v.sideType u ℓ}

/-- `(HT-branch)`'s formula as arithmetic over the tree data: the per-node orbit factor times
the per-side censuses, times `Q` to the total digit budget net of the children's clipped
histories (the root's `D` is NOT subtracted — hence the `drop 1`). -/
noncomputable def htBranchCount (Q : ℕ) (census : FactorizationType → ℕ)
    (t : HTTree) (N : ℕ) : ℕ :=
  ((List.range t.nodes.length).map (fun i =>
      let v := t.nodes.getD i HTNode.default0
      v.kappa * ∏ p ∈ v.sides, census (v.sideType p.1 p.2))).prod
    * Q ^ ((((List.range t.nodes.length).map
          (fun i => (t.nodes.getD i HTNode.default0).B N)).sum)
        - (((List.range t.nodes.length).drop 1).map
          (fun i => (t.nodes.getD i HTNode.default0).D N)).sum)

instance : Inhabited HTTree := ⟨⟨[], fun _ => 0⟩⟩

/-- the level-0 shape: branches `(d_i, m_i, tree_i)` + the level-0 orbit factor `κ₀`. -/
structure HTShape where
  /-- one entry per level-0 branch: `(d_i, m_i, tree_i)`. -/
  branches : List (ℕ × ℕ × HTTree)
  /-- the level-0 side-tagged orbit factor `κ₀(T)`. -/
  kappa0 : ℕ

/-- `(HT-global)`'s formula (the branch censuses abstracted per branch).  A branch of
multiplicity `1` is unrepeated and contributes the plain `q^{d_i(N−1)}`; every repeated branch
contributes its tree's `(HT-branch)` count at base `Q_i = q^{d_i}`. -/
noncomputable def htGlobalCount (S : HTShape) (q : ℕ)
    (census : ℕ → FactorizationType → ℕ) (N : ℕ) : ℕ :=
  S.kappa0
    * ((List.range S.branches.length).map (fun i =>
        let b := S.branches.getD i (0, 0, default)
        if b.2.1 = 1 then q ^ (b.1 * (N - 1))
        else htBranchCount (q ^ b.1) (census i) b.2.2 N)).prod

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.HTNode
#print axioms Uniformity.Density.Tower.HTNode.mk
#print axioms Uniformity.Density.Tower.HTNode.default0
#print axioms Uniformity.Density.Tower.HTNode.B
#print axioms Uniformity.Density.Tower.HTNode.D
#print axioms Uniformity.Density.Tower.HTTree
#print axioms Uniformity.Density.Tower.HTTree.WF
#print axioms Uniformity.Density.Tower.conservativeCell
#print axioms Uniformity.Density.Tower.htCell
#print axioms Uniformity.Density.Tower.htBranchCount
#print axioms Uniformity.Density.Tower.HTShape
#print axioms Uniformity.Density.Tower.htGlobalCount

end AxCheck
