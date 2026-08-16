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
   reach a node through `htCell`'s `npHgt` clauses.  **[re-signed: A-C.2, 2026-08-16]** the
   original pin clause `npHgt Φ f j = (Pceil j : ℕ∞)` at EVERY `j ≤ m` contradicted the
   corpus's own three-way membership law (`EFF.W12.23`, quoted verbatim at B.16: *"`j` a
   VERTEX of `P`: `v(a_j) = P(j)` exactly …; `j` an on-side lattice point: `v(a_j) ≥ P(j)`,
   with `digit_{P(j)}(a_j)` = the residual coefficient `r_j` (**possibly zero**) …; every
   other `j < m`: … `v(a_j) ≥ ⌈P(j)⌉`"*).  The re-signed cell pins `≥ Pceil` everywhere and
   equality at `HTNode.IsVertex` positions only — which is exactly the three-way law in
   ceiled form, since at on-side lattice points and vertices `Pceil = P` while elsewhere
   `Pceil = ⌈P⌉`.  Certified: `verification/c109_ac2_cell_check.py` (the old pin makes the
   cell EMPTY on the char-2 double-root instance and breaks the `ℓ = 2` count; the new cell
   satisfies the count law on all 13 instances).  Full record: amendment A-C.2.
3. **`κ_v` is a DATA field, not a computed expression.**  The corpus's side-tagged factorial
   rule `κ_v = ∏_{S,a} r_{v,S,a}! / ∏_H r_{v,S,a,H}!` is the corpus's computation and is
   recorded in the field docstring; the count formulas consume the value.  **The side tag is
   MANDATORY** — roots lying on different sides of the node polygon cannot be permuted, so an
   untagged orbit factor is simply the wrong number.  C.116's manifest keeps the tag visible;
   the DROP-teeth guard it.
4. **`sides : Finset (ℕ × ℕ)` with `sideType : ℕ → ℕ → FactorizationType`** — a side is its
   cleared slope pair `(u, ℓ)`, and `sideType` is junk off `sides` (the junk-total discipline).
   **[A-C.2, 2026-08-16]** `L`, `sides` and the types' degrees are NOT free data in the
   corpus: `EFF.W12.83` *defines* `L_v = #{j < m_v : P_v(j) ∈ ℤ}` in the same display that
   defines `B_v`, and the census product ranges over the sides *of the polygon*
   (`∏_{S ⊂ P_v}`).  The frozen C.109 quantified over all `v : HTNode` and was machine-refuted
   (`C109_REFUTATION.lean.txt`).  The coherence is now the explicit predicate `HTNode.WF`
   below (monic top, ceiled-consistency, the `L` law, the sides law, the degree law), taken as
   an inline hypothesis by every count law.  Full record: amendment A-C.2.
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

/-! ### [A-C.2] the node polygon read off `Pceil` (chord tests, ℚ-free)

The lower convex hull of the ceiled points `{(j, ⌈P(j)⌉) : j ≤ m}` IS the polygon `P` (a
convex function `≥ P` that agrees with `P` at the vertices agrees with `P` everywhere —
the chord bound both ways), so all polygon reads below are ℕ-arithmetic on `Pceil`.
Certified against direct rational hull geometry on every instance of
`verification/c109_ac2_cell_check.py` (the `[ENC]` leg). -/

/-- **[A-C.2]** `OnHull v j` — the point `(j, ⌈P_v(j)⌉)` lies on the lower convex hull of the
ceiled points: on/below every bracketing chord.  Under `HTNode.WF`'s ceiled-consistency this
is exactly the corpus's "`P_v(j) ∈ ℤ`" — the integral boundary positions of
`EFF.W12.83`/`EFF.W12.23`, the positions whose height-`P_v(j)` digit is priced by the
residual. -/
def HTNode.OnHull (v : HTNode) (j : ℕ) : Prop :=
  ∀ i k : ℕ, i ≤ j → j ≤ k → k ≤ v.m →
    (k - i) * v.Pceil j ≤ (k - j) * v.Pceil i + (j - i) * v.Pceil k

/-- **[A-C.2]** `IsVertex v j` — `(j, ⌈P_v(j)⌉)` is a VERTEX of the hull: strictly below
every properly bracketing chord (the endpoints `j = 0, m` are vertices vacuously).
`IsVertex` implies `OnHull` (a point strictly above the hull sits on/above some proper
bracketing chord). -/
def HTNode.IsVertex (v : HTNode) (j : ℕ) : Prop :=
  ∀ i k : ℕ, i < j → j < k → k ≤ v.m →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k

/-- **[A-C.2]** the node-data twin of B.16's `OnSide`: abscissa `j` attains the
`(u, ℓ)`-cleared support minimum of the ceiled points. -/
def HTNode.NodeOnSide (v : HTNode) (u ℓ j : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ v.m → ℓ * v.Pceil j + u * j ≤ ℓ * v.Pceil i + u * i

/-- **[A-C.2]** the node-data twin of B.16's `sideSet`: the `(u, ℓ)`-support set of the
ceiled points.  For a genuine side this is exactly its lattice abscissae (`≥ 2` of them);
for any other direction it is the single supporting vertex. -/
noncomputable def HTNode.nodeSideSet (v : HTNode) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (v.m + 1)).filter (v.NodeOnSide u ℓ)

/-- **[A-C.2]** `IsSide v u ℓ` — `(u, ℓ)` is a genuine side of the node polygon: a cleared
slope pair whose support set has at least two points. -/
def HTNode.IsSide (v : HTNode) (u ℓ : ℕ) : Prop :=
  0 < ℓ ∧ Nat.Coprime u ℓ ∧ 2 ≤ (v.nodeSideSet u ℓ).card

/-- **[A-C.2]** the node-data twin of B.20's `sideDeg`: the side's residual degree
`(sideMax − sideMin)/ℓ`, junk `0` off the genuine sides. -/
noncomputable def HTNode.nodeSideDeg (v : HTNode) (u ℓ : ℕ) : ℕ :=
  ((v.nodeSideSet u ℓ).max.getD 0 - (v.nodeSideSet u ℓ).min.getD 0) / ℓ

open Classical in
/-- **[A-C.2] node well-formedness** — the corpus's implicit coherence of the node datum,
made explicit (`EFF.W12.83`'s own `L_v = #{j < m_v : P_v(j) ∈ ℤ}` display; `EFF.W12.23`'s
membership law; the census product over the sides *of the polygon*):
(i) the polygon ends at `(m, 0)` (the monic top of `EFF.W12.23`'s hull);
(ii) ceiled-consistency — `Pceil` is pointwise the CEILING of its own lower hull
(`Pceil j < chord + 1` for every bracketing chord);
(iii) the `L` law — `L = #{j < m : OnHull j}`;
(iv) the sides law — `sides` is exactly the genuine cleared side-slope set;
(v) the degree law — each side's type has total degree the side's residual degree.
Every count law of §11 takes `v.WF` as an inline hypothesis (amendment A-C.2; the frozen
C.109 without it is machine-refuted, `C109_REFUTATION.lean.txt`). -/
def HTNode.WF (v : HTNode) : Prop :=
  v.Pceil v.m = 0 ∧
  (∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ v.m → i < k →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k + (k - i)) ∧
  v.L = ((Finset.range v.m).filter v.OnHull).card ∧
  (∀ u ℓ : ℕ, ((u, ℓ) ∈ v.sides ↔ v.IsSide u ℓ)) ∧
  (∀ u ℓ : ℕ, (u, ℓ) ∈ v.sides → (v.sideType u ℓ).degree = v.nodeSideDeg u ℓ)

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
taken as binders here.)

**[re-signed: A-C.2, 2026-08-16]** the polygon pin is `EFF.W12.23`'s three-way membership law
in ceiled form: `npHgt ≥ Pceil` at every `j ≤ m` (the automatic ceiling; at on-side lattice
points the height-`P(j)` digit is the residual coefficient, POSSIBLY ZERO), with equality
exactly at the hull VERTICES.  The retired clause pinned equality at every `j`, which is
strictly smaller than the corpus cell whenever the polygon has a non-vertex position
(machine-certified divergence: `verification/c109_ac2_cell_check.py`, mutation M3). -/
def htCell (π : O) (Φ : Polynomial O) [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] (v : HTNode) :
    Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = v.m * Φ.natDegree ∧
    (∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j) ∧
    (∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞)) ∧
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
#print axioms Uniformity.Density.Tower.HTNode.OnHull
#print axioms Uniformity.Density.Tower.HTNode.IsVertex
#print axioms Uniformity.Density.Tower.HTNode.NodeOnSide
#print axioms Uniformity.Density.Tower.HTNode.nodeSideSet
#print axioms Uniformity.Density.Tower.HTNode.IsSide
#print axioms Uniformity.Density.Tower.HTNode.nodeSideDeg
#print axioms Uniformity.Density.Tower.HTNode.WF
#print axioms Uniformity.Density.Tower.HTTree
#print axioms Uniformity.Density.Tower.HTTree.WF
#print axioms Uniformity.Density.Tower.conservativeCell
#print axioms Uniformity.Density.Tower.htCell
#print axioms Uniformity.Density.Tower.htBranchCount
#print axioms Uniformity.Density.Tower.HTShape
#print axioms Uniformity.Density.Tower.htGlobalCount

end AxCheck
