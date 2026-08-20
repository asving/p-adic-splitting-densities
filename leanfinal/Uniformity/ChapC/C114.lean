/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108
import Uniformity.ChapC.C109
import Uniformity.ChapC.C115
import Uniformity.ChapB.B08
import Uniformity.ChapB.B09
import Uniformity.ChapB.B39b
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapC.C114 — TERMINAL SUPPLY: the count law (the A-C.3 carriers + the certified legs)

**Chapter C, NODE C.114** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1; RE-SIGNED: A-C.3, 2026-08-16 — the
realizes-refinement]`.

## WHICH FORM THIS FILE LANDS

**The A-C.3 RE-SIGN, not the A-C.1 freeze.**  The frozen forms of both count laws are
machine-refuted (`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`,
`c114_branch_frozen_false` / `c114_global_frozen_false`): the frozen stratum reads none of
`kappa`, `kappa0`, `s`, the non-root `sideType`s, nor child-completeness, while
`htBranchCount` / `htGlobalCount` read all of them.  A-C.2 withdrew them; A-C.3 re-signed
them after its own certification leg (`verification/c114_ac3_stratum_check.py`, 63 checks)
found the *designed* repair list insufficient in two further ways (findings **D5**, **D6**).

Every declaration below is transcribed BYTE-FROZEN from the A-C.3 re-signed leanspec twin
`leanspec/Leanspec/ChapC.lean` (the contract), re-namespaced `LeanspecC` →
`Uniformity.Density.Tower` and nothing else.

### Frozen-vs-re-sign discrepancy record (required by the unit charge)

* The blueprint node prose (`### NODE C.114`) displays `ht_global` with three `…` elisions
  (`hn : n = …`, `d_i`, `m_{σ i}`, `tree_{σ i}`, `(the eight branch-tree clauses at tree_i)`,
  `(instD instU instFin : …)`).  The node text itself declares the leanspec twin to be the
  contract for those elisions.  **The leanspec twin is what is transcribed here**; the
  elisions resolve to `S.branches.getD i (0, 0, default)` reads, the eight-clause `hbr`
  conjunction, and three separate instance-function binders.  No divergence in content.
* The blueprint SIGNATURE block writes the `htRealizes` cell clause with the trailing comment
  `-- subsumes the pins`; the leanspec twin has no comment there.  Cosmetic only.
* **A-C.3's findings D5 and D6 are authoritative over the frozen text** and are honoured:
  D5 = the `IsRepSystem` recentring clause (which *implies* A-C.2's designed `s`-pin, so the
  `s`-pin is NOT carried separately — see `repRecentring_gaussVal` below); D6 = per-node
  nonnegativity is FALSE at multi-child nodes, so `HTTree.NodeExponent` is CARRIED as `hnode`
  and never derived.

## A-C.7 FIVE-INSTANCE BINDER-VACUITY AUDIT — VERDICT (recorded BEFORE any proof)

Registry audited against (`blueprint/CHAP-C_tower_grammar.md` §A-C.8.4): (1) C.111 `hnode`,
an unpinned carrier field; (2) C.94, a self-loop trivializing an infinite relation; (3) C.113
`hne`, a `Nonempty` guard provable unconditionally; (4) C.118 `Visible₂`, an
implication-guarded `≠ ⊤` leaving the `⊤` stratum unguarded; (5) C.66, the low-degree purity
collapse.

**VERDICT: no fifth instance of the A-C.7 pattern.  Three DISCLOSED non-teeth (not
defects): `hfence`, `hroot`, and `hnode`-at-depth-0 — all three machine-recorded below.**

| binder | vacuity risk | verdict | sharpness witness |
|---|---|---|---|
| `hkappa : ∀ i < len, t.KappaRule i` | C.111 (unpinned `kappa`) — the ORIGINAL defect | **SHARP** | `kappaRule_one_node_iff`: on the refuting one-node family `⟨[vK k]⟩` the rule holds **iff `k = 1`**, so the `k = 2` member (which gave formula `2` against an equinumerous stratum) is excluded. Machine-checked below. |
| `hkappa0 : S.Kappa0Rule` | C.111, at level 0 | **SHARP** | `kappa0Rule_empty_iff`: on the refuting empty family `⟨[], k⟩` the rule holds **iff `k = 1`**. Machine-checked below; and at `k = 1` the conclusion is not merely silent but TRUE (`ht_global_empty_shape`). |
| `hR : IsRepSystem R Φ.natDegree` | "no `R` exists ⇒ the theorem is vacuous" (the new D5 clause) | **NON-VACUOUS, SATISFIABLE** | `exists_isRepSystem`: for every `0 < d` a rep system is CONSTRUCTED (digitwise, from a section of the residue map). Also non-trivial: `isRepSystem_empty_iff_of_pos` shows `R = ∅` fails for `0 < d`, so the clause is not implied. |
| `hcompl : t.ChildComplete` | C.113 (a clause carrying no content) | **CONTENTFUL at leaves too** | its second conjunct at a childless node forces `(v.sideType u 1).data.count (1, a) = 0` for every `e = 1` side and every `a ≥ 2` — i.e. a leaf may not have repeated linear residual factors. Not vacuous. |
| `hvis : t.WindowVisible N` | none (positive statement, no guard) | **SHARP** | it is the binder `ht_node_cell_card` consumes (`hvis`); without it the digit budget `B_v(N)` clips by ℕ-subtraction and the count is wrong. |
| `hcons : t.Conservative` | C.113 | **SHARP** (A-C.3 tooth) | `verification/c114_ac3_stratum_check.py`: dropping it gives stratum `0` against formula `1458`. |
| `hwf`, `hnodewf` | C.113 | **SHARP** (A-C.2 teeth) | the C.109 refutation record: the frozen `HTNode`-datum count without `WF` is refuted. |
| `hnode : t.NodeExponent N` | C.111 — the CARRIED clause | **SHARP where D6 bites; DISCLOSED trivial at depth 0** | `nodeExponent_of_one_node`: on ANY one-node tree it holds unconditionally (empty child sum). That is not a defect — D6's counterexamples (truth `243, 486, 128` vs formula `9, 108, 32`) are all multi-child, and there the clause is the fence. Recorded so it is not read as a tooth at depth 0. |
| `hfence : t.OrderOne` | C.113 | **NOT SHARP — DISCLOSED** (already flagged in the blueprint TEETH line: "a SCOPE fence with no truth tooth in the grid") | `orderOne_of_no_sides`: it holds vacuously on the whole refuting one-node family, so it separates nothing there. Retained because the source refuses to speak past it. |
| `hroot : 0 < t.nodes.length` | "typing clause or truth tooth?" | **NOT SHARP — DISCLOSED** | `ht_branch_empty_tree`: at `t.nodes = []` the conclusion is TRUE (both sides `1`), so dropping `hroot` would not falsify the statement. It is a scope/read clause (it makes `t.nodes.getD 0` a real node). Machine-checked below. |
| `hdistinct` (global) | C.113 | **SHARP** (A-C.3 tooth) | tooth `8` against formula `64` with two branches at one residue. |
| `hn`, `hkeys`, `hbr` (global) | none | pinning/relay clauses | `hn` pins the degree; `hbr` relays the eight branch clauses verbatim, so their audit rows above transfer. |
| instance binders (`IsAdicComplete`, `Finite`, `IsDomain`, `UniqueFactorizationMonoid`) | inert-existence | scope binders | they are what make `sideCensus` / `resPoly` well-formed; `IsDomain` and `UniqueFactorizationMonoid` are `Prop`-classes, so no instance-mismatch hazard in `htCell` reads. |

**Self-refutation attempt on the repair (the standing A-C.7 lesson).**  Three attacks were
run against the re-signed guards before proving anything:

1. *Re-run the A-C.2 geometries.* `⟨[vK 1]⟩` and `⟨[vK 2]⟩` (resp. `⟨[], 1⟩`, `⟨[], 2⟩`) are
   `rfl`-equinumerous in the stratum. The κ/κ₀-rules kill the `k = 2` members
   (`kappaRule_one_node_iff`, `kappa0Rule_empty_iff`), and at `k = 1` the branch conclusion is
   PROVED (`ht_branch_one_node`) and the global conclusion is PROVED
   (`ht_global_empty_shape`). The refutation family is dead in both directions: excluded where
   it was false, proved where it survives.
2. *Attack the D5 clause as an over-reach.* If `IsRepSystem` were unsatisfiable the re-sign
   would be a vacuity. `exists_isRepSystem` constructs one for every positive degree, so it is
   not.
3. *Attack `hkappa` as insufficient rather than excessive* (i.e. look for a SECOND κ-separated
   pair surviving the rule). Any two trees differing only in `kappa` cannot both satisfy
   `KappaRule` at the differing index: the rule is `kappa * A = B` with `A, B` determined by
   the OTHER fields, and `A ≠ 0` (a product of factorials), so `kappa` is uniquely determined
   by the rest of the tree — `kappa_unique_of_kappaRule` below, machine-checked. This closes
   the C.111 pattern for `kappa` in general, not just on the refuting family. The same
   argument closes `kappa0` (`kappa0_unique_of_kappa0Rule`).

## WHAT IS LANDED vs WHAT IS BLOCKED

**LANDED** (all Lean-core, zero `sorry`, zero new axioms): the fourteen A-C.3 carriers; the
three separation/subsumption legs of `leanspec/C114_AC3_SEPARATION.lean.txt` re-proved here
(`kappaRule_one_node_iff`, `kappa0Rule_empty_iff`, `repRecentring_gaussVal`); the two
κ-uniqueness lemmas; the `IsRepSystem` satisfiability construction; the `htRealizes`
one-node normal form; and the two count laws AT THE CERTIFIED DEGENERATE STRATA —
`ht_branch_one_node` (every one-node tree, at the FULL re-signed binder list) and
`ht_global_empty_shape`, plus `ht_branch_empty_tree`.

**BLOCKED** (recorded in `C114_BLOCKED_2026-08-20.md`, with the verbatim goals): the general
`ht_branch` and `ht_global`.  Mechanism, precisely: both need the corpus's **step-3 fiber
decomposition** — a bijection, at each node `v` of the tree, between the level-`N` classes of
`htCell`-members realizing the subtree at `v` and pairs (class at `v`, tuple of child
classes) — and NO landed node supplies it.  `ht_rec` (C.112) supplies only the division-free
ARITHMETIC telescope of the formula; `ht_fiber_exponent_nonneg` (C.111) supplies only its
exponent's nonnegativity; `ht_node_cell_card` (C.109) supplies only the SINGLE-node cell
count.  There is no subtree operation on `HTTree` and no `children`-indexed recursion
principle in the corpus, so the induction the proof needs cannot even be stated over the
landed carriers.  The blueprint's own PROOF line concedes this ("under `hnode` the fleet must
still supply it"); it is a missing lemma of theorem strength, not a repair.

## Blueprint position

**DEPENDS.** C.107–C.113 (+ C.109a through C.109).  **SOURCE.** `EFF.W12.83` (the displays,
the κ/κ₀ factorial rules, the `e = 1` child law, the order-≥2 fence); `.84` step 2 (D5, the
lift); `.85` steps 3–4 (D6, the refuted nonnegativity); `.86` step 6; `.87`.  **TEETH.**
`verification/c114_ac3_stratum_check.py` (63 checks, exit 0); machine separation
`leanspec/C114_AC3_SEPARATION.lean.txt`, re-proved here.
-/

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf Polynomial
open IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The A-C.3 tree-coherence carriers (byte-frozen from the leanspec twin)

DECISION D-C.3-CARRIER: the seven tree predicates and `IsRepSystem` are ANNEXED to this node
(exactly two consumers, both here, no independent statement content). -/

/-- [A-C.3] descendant (or equal) in the index-encoded tree, first-order via `parent^[k]`
(no recursion, so the subtree comparison below is a plain `Prop`). -/
def HTTree.IsDesc (t : HTTree) (i u : ℕ) : Prop :=
  u < t.nodes.length ∧ ∃ k : ℕ, t.parent^[k] u = i

open Classical in
/-- [A-C.3] the children of node `i`. -/
noncomputable def HTTree.children (t : HTTree) (i : ℕ) : Finset ℕ :=
  (Finset.range t.nodes.length).filter (fun u => 0 < u ∧ t.parent u = i)

/-- [A-C.3] **the COMPLETE HISTORY comparison**: the subtree at `u` in `t` is isomorphic to
the subtree at `u'` in `t'` — a bijection of descendant sets carrying root to root,
preserving node data, commuting with `parent`.  This is what `EFF.W12.83`'s κ-displays
group by (`r_{v,S,a,H}` counts children "carrying `H`"); stated first-order so no
nested-inductive history carrier is needed. -/
def HTTree.SameHist (t : HTTree) (u : ℕ) (t' : HTTree) (u' : ℕ) : Prop :=
  ∃ σ : ℕ → ℕ, σ u = u' ∧
    Set.BijOn σ {w | t.IsDesc u w} {w | t'.IsDesc u' w} ∧
    (∀ w, t.IsDesc u w →
      t'.nodes.getD (σ w) HTNode.default0 = t.nodes.getD w HTNode.default0) ∧
    (∀ w, t.IsDesc u w → w ≠ u → σ (t.parent w) = t'.parent (σ w))

open Classical in
/-- [A-C.3] **the `(HT-orbit)` κ-rule at tree level**, in DIVISION-FREE form (the C.112
precedent): `κ_v · ∏_H (r_{v,H})! = ∏_{(S,a)} (r_{v,S,a})!`, the history classes running
over `SameHist`-classes of `v`'s children and the groups over their `(side, multiplicity)`
classes.  `EFF.W12.83`: `κ_v = ∏_{S,a} r_{v,S,a}!/∏_H r_{v,S,a,H}!`.  `kappa` was a FREE
data field in the A-C.1 signature — that freedom is exactly the A-C.2 refutation. -/
noncomputable def HTTree.KappaRule (t : HTTree) (i : ℕ) : Prop :=
  (t.nodes.getD i HTNode.default0).kappa
      * ∏ c ∈ (t.children i).image
            (fun u => (t.children i).filter (fun u' => t.SameHist u t u')),
        Nat.factorial c.card
    = ∏ g ∈ (t.children i).image
            (fun u => (t.children i).filter (fun u' =>
              (t.nodes.getD u' HTNode.default0).s = (t.nodes.getD u HTNode.default0).s ∧
              (t.nodes.getD u' HTNode.default0).m = (t.nodes.getD u HTNode.default0).m)),
        Nat.factorial g.card

/-- [A-C.3] every node datum is `HTNode.WF` (A-C.2's coherence). -/
def HTTree.NodeWF (t : HTTree) : Prop :=
  ∀ i, i < t.nodes.length → (t.nodes.getD i HTNode.default0).WF

/-- [A-C.3] a non-root node is CONSERVATIVE for its own depth — `EFF.W12.83`: "the child
is the degree-`d_i` conservative node of multiplicity `m_u` and depth `s_u`", with
`C_{m}(s) = {(a_j) : v(a_j) ≥ (m−j)s + 1}`.  (Tooth: without it, the certified instance
has stratum 0 against formula 1458.) -/
def HTTree.Conservative (t : HTTree) : Prop :=
  ∀ i, 0 < i → i < t.nodes.length →
    ∀ j, j < (t.nodes.getD i HTNode.default0).m →
      ((t.nodes.getD i HTNode.default0).m - j) * (t.nodes.getD i HTNode.default0).s + 1
        ≤ (t.nodes.getD i HTNode.default0).Pceil j

open Classical in
/-- [A-C.3] **child-count-vs-type completeness** — `EFF.W12.83`: "Its children are
precisely the repeated linear factors `(Y−z)^{m_u}` on `e = 1` sides.  If the side has
slope `−s_u`, the child is the … node of multiplicity `m_u` and depth `s_u`."  Purely
combinatorial: each child sits at a slope that IS an `e = 1` side of its parent and has
multiplicity ≥ 2, and per side the child counts equal the type's repeated-linear
multiplicities. -/
noncomputable def HTTree.ChildComplete (t : HTTree) : Prop :=
  (∀ u, 0 < u → u < t.nodes.length →
      ((t.nodes.getD u HTNode.default0).s, 1)
          ∈ (t.nodes.getD (t.parent u) HTNode.default0).sides
        ∧ 2 ≤ (t.nodes.getD u HTNode.default0).m) ∧
  (∀ i, i < t.nodes.length → ∀ u a : ℕ,
      (u, 1) ∈ (t.nodes.getD i HTNode.default0).sides → 2 ≤ a →
      ((t.children i).filter (fun c =>
          (t.nodes.getD c HTNode.default0).s = u ∧
          (t.nodes.getD c HTNode.default0).m = a)).card
        = ((t.nodes.getD i HTNode.default0).sideType u 1).data.count (1, a))

/-- [A-C.3] the order-1 FENCE — `EFF.W12.83`: "Repeated factors of degree `> 1`, and
repeated factors on `e > 1` sides, open composite stages and are outside this order-1
statement."  A SCOPE clause: the certification found no truth tooth for it (reported, not
hidden), and it is retained because the source refuses to speak past it. -/
def HTTree.OrderOne (t : HTTree) : Prop :=
  ∀ i, i < t.nodes.length → ∀ u ℓ : ℕ,
    (u, ℓ) ∈ (t.nodes.getD i HTNode.default0).sides →
    ∀ p ∈ ((t.nodes.getD i HTNode.default0).sideType u ℓ).data, 2 ≤ p.2 → p.1 = 1 ∧ ℓ = 1

/-- [A-C.3] window visibility of every node (`EFF.W12.83`'s standing "window-visible
decided order-1 key"; `.86` step 5's `m_v s_v + 1 ≤ P_v(0) ≤ N − 1`). -/
def HTTree.WindowVisible (t : HTTree) (N : ℕ) : Prop :=
  ∀ i, i < t.nodes.length → ∀ j, j ≤ (t.nodes.getD i HTNode.default0).m →
    (t.nodes.getD i HTNode.default0).Pceil j < N

open Classical in
/-- [A-C.3, finding D6] the PER-NODE exponent inequality — `EFF.W12.85`'s
`#U_v(𝐑) = Q^{B_v(N)−Σ_u D_u(N)}`, "in particular, the exponent is a nonnegative integer".
The corpus derives it from the fiber bijection; the A-C.3 certification REFUTES the
derivation at multi-child nodes (`B_v − Σ_u D_u = −s(m_v² − Σ_u m_u²)/2 < 0` when the
children exhaust the node), so it is CARRIED, exactly as A-C.2 carries it at C.111. -/
noncomputable def HTTree.NodeExponent (t : HTTree) (N : ℕ) : Prop :=
  ∀ i, i < t.nodes.length →
    (∑ u ∈ t.children i, (t.nodes.getD u HTNode.default0).D N)
      ≤ (t.nodes.getD i HTNode.default0).B N

open Classical in
/-- [A-C.3] the level-0 orbit rule — `EFF.W12.83`: `κ₀(T) = ∏_{d,m} r_{d,m}!/∏_H r_{d,m,H}!`,
division-free, branch histories compared by tree isomorphism. -/
noncomputable def HTShape.Kappa0Rule (S : HTShape) : Prop :=
  S.kappa0 * ∏ c ∈ (Finset.range S.branches.length).image (fun i =>
        (Finset.range S.branches.length).filter (fun j =>
          (S.branches.getD j (0, 0, default)).1 = (S.branches.getD i (0, 0, default)).1 ∧
          (S.branches.getD j (0, 0, default)).2.1 = (S.branches.getD i (0, 0, default)).2.1 ∧
          HTTree.SameHist (S.branches.getD i (0, 0, default)).2.2 0
            (S.branches.getD j (0, 0, default)).2.2 0)),
      Nat.factorial c.card
    = ∏ g ∈ (Finset.range S.branches.length).image (fun i =>
        (Finset.range S.branches.length).filter (fun j =>
          (S.branches.getD j (0, 0, default)).1 = (S.branches.getD i (0, 0, default)).1 ∧
          (S.branches.getD j (0, 0, default)).2.1 = (S.branches.getD i (0, 0, default)).2.1)),
      Nat.factorial g.card

/-- [A-C.3] an assignment of the shape's branch SLOTS to the given keys, preserving
`(d, m)`.  The shape is LETTER-FREE, so with the letters (`Φb`) given the assignment is
still free — that freedom is precisely what `κ₀` counts, and without this `∃` the global
law is off by `κ₀` (tooth: 256 against 512). -/
def HTShape.IsSlotAssign (S : HTShape) (σ : ℕ → ℕ) : Prop :=
  Set.BijOn σ (Set.Iio S.branches.length) (Set.Iio S.branches.length) ∧
  ∀ i, i < S.branches.length →
    (S.branches.getD (σ i) (0, 0, default)).1 = (S.branches.getD i (0, 0, default)).1 ∧
    (S.branches.getD (σ i) (0, 0, default)).2.1 = (S.branches.getD i (0, 0, default)).2.1

/-- [A-C.3, finding D5] a SYSTEM OF REPRESENTATIVES of the degree-`< d` residue classes:
exactly one polynomial of degree `< d` in each class mod `π`.  `EFF.W12.84` step 2's
"Choose a lift `z̃`" made into data; the count is independent of the choice (certified). -/
def IsRepSystem (R : Set (Polynomial O)) (d : ℕ) : Prop :=
  (∀ r ∈ R, r.natDegree < d) ∧
  ∀ a : Polynomial O, a.natDegree < d →
    ∃! r : Polynomial O, r ∈ R ∧ (1 : ℕ∞) ≤ gaussVal (a - r)

/-- `f` realizes the tree `t` at the key `Φ`, with recentrings drawn from the
representative system `R`.  [RE-SIGNED: A-C.3 — the realizes-refinement.  Against the
A-C.2 form this ADDS: per-node `IsKey (K i)`; per-node CELL membership at the recentered
key (which subsumes the monic/degree/polygon clauses AND pins the non-root side TYPES —
tooth: 108 against formula 54 without it); the D5 representative recentring (which
subsumes A-C.2's designed `s`-pin); and sibling distinctness.] -/
def htRealizes (π : O) (Φ f : Polynomial O) (t : HTTree) (R : Set (Polynomial O)) : Prop :=
  ∃ (G K : ℕ → Polynomial O)
    (instD : ∀ i, IsDomain (resField (K i)))
    (instU : ∀ i, UniqueFactorizationMonoid (resField (K i))),
    K 0 = Φ ∧ G 0 = f ∧
    (∀ i, i < t.nodes.length → IsKey (K i)) ∧
    (∀ i, i < t.nodes.length →
      letI := instD i
      letI := instU i
      G i ∈ htCell π (K i) (t.nodes.getD i HTNode.default0)) ∧
    (∀ i, 0 < i → i < t.nodes.length →
      G i ∣ G (t.parent i) ∧
      (K i).natDegree = (K (t.parent i)).natDegree ∧
      (K i - K (t.parent i)).natDegree < (K i).natDegree ∧
      ∃ z ∈ R, gaussVal z = 0 ∧
        K (t.parent i) - K i
          = Polynomial.C (π ^ (t.nodes.getD i HTNode.default0).s) * z) ∧
    (∀ i i', 0 < i → 0 < i' → i < t.nodes.length → i' < t.nodes.length → i ≠ i' →
      t.parent i = t.parent i' →
      (t.nodes.getD i HTNode.default0).s = (t.nodes.getD i' HTNode.default0).s →
      gaussVal (K i - K i') = ((t.nodes.getD i HTNode.default0).s : ℕ∞))

/-! ## 2. Audit helpers (NOT part of the signed contract)

The two factorial products of the `(HT-orbit)` κ-rule, named so that the rule can be read as
`kappa * histProd = groupProd` and the C.111 "unpinned carrier field" pattern can be closed in
general: `histProd` is a product of factorials, hence positive, so `kappa` is DETERMINED by the
rest of the tree.  Same at level 0 for `kappa0`. -/

open Classical in
/-- audit helper: the LEFT factorial product of the κ-rule (the history-class factorials). -/
noncomputable def HTTree.kappaHistProd (t : HTTree) (i : ℕ) : ℕ :=
  ∏ c ∈ (t.children i).image
        (fun u => (t.children i).filter (fun u' => t.SameHist u t u')),
    Nat.factorial c.card

open Classical in
/-- audit helper: the RIGHT factorial product (the `(side, multiplicity)`-group factorials). -/
noncomputable def HTTree.kappaGroupProd (t : HTTree) (i : ℕ) : ℕ :=
  ∏ g ∈ (t.children i).image
        (fun u => (t.children i).filter (fun u' =>
          (t.nodes.getD u' HTNode.default0).s = (t.nodes.getD u HTNode.default0).s ∧
          (t.nodes.getD u' HTNode.default0).m = (t.nodes.getD u HTNode.default0).m)),
    Nat.factorial g.card

theorem HTTree.kappaRule_iff (t : HTTree) (i : ℕ) :
    t.KappaRule i ↔
      (t.nodes.getD i HTNode.default0).kappa * t.kappaHistProd i = t.kappaGroupProd i :=
  Iff.rfl

theorem HTTree.kappaHistProd_pos (t : HTTree) (i : ℕ) : 0 < t.kappaHistProd i :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- **`hkappa` leaves NO freedom in `kappa`** — the C.111 "unpinned carrier field" pattern
closed in general, not just on the refuting family.  If two orbit values both satisfy the
`(HT-orbit)` rule against the same tree data, they are equal: the rule reads node `i` only
through `.kappa`, and its left factorial product is positive. -/
theorem kappa_unique_of_kappaRule (t : HTTree) (i k : ℕ)
    (h : t.KappaRule i) (h' : k * t.kappaHistProd i = t.kappaGroupProd i) :
    (t.nodes.getD i HTNode.default0).kappa = k := by
  have h1 := (t.kappaRule_iff i).1 h
  exact Nat.eq_of_mul_eq_mul_right (t.kappaHistProd_pos i) (h1.trans h'.symm)

open Classical in
/-- audit helper: the LEFT factorial product of the level-0 κ₀-rule. -/
noncomputable def HTShape.kappa0HistProd (S : HTShape) : ℕ :=
  ∏ c ∈ (Finset.range S.branches.length).image (fun i =>
        (Finset.range S.branches.length).filter (fun j =>
          (S.branches.getD j (0, 0, default)).1 = (S.branches.getD i (0, 0, default)).1 ∧
          (S.branches.getD j (0, 0, default)).2.1 = (S.branches.getD i (0, 0, default)).2.1 ∧
          HTTree.SameHist (S.branches.getD i (0, 0, default)).2.2 0
            (S.branches.getD j (0, 0, default)).2.2 0)),
      Nat.factorial c.card

open Classical in
/-- audit helper: the RIGHT factorial product of the level-0 κ₀-rule. -/
noncomputable def HTShape.kappa0GroupProd (S : HTShape) : ℕ :=
  ∏ g ∈ (Finset.range S.branches.length).image (fun i =>
        (Finset.range S.branches.length).filter (fun j =>
          (S.branches.getD j (0, 0, default)).1 = (S.branches.getD i (0, 0, default)).1 ∧
          (S.branches.getD j (0, 0, default)).2.1 = (S.branches.getD i (0, 0, default)).2.1)),
      Nat.factorial g.card

theorem HTShape.kappa0Rule_iff (S : HTShape) :
    S.Kappa0Rule ↔ S.kappa0 * S.kappa0HistProd = S.kappa0GroupProd :=
  Iff.rfl

theorem HTShape.kappa0HistProd_pos (S : HTShape) : 0 < S.kappa0HistProd :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- **`hkappa0` leaves NO freedom in `kappa0`** (the level-0 twin of
`kappa_unique_of_kappaRule`). -/
theorem kappa0_unique_of_kappa0Rule (S : HTShape) (k : ℕ)
    (h : S.Kappa0Rule) (h' : k * S.kappa0HistProd = S.kappa0GroupProd) :
    S.kappa0 = k := by
  have h1 := S.kappa0Rule_iff.1 h
  exact Nat.eq_of_mul_eq_mul_right S.kappa0HistProd_pos (h1.trans h'.symm)

/-! ## 3. The A-C.3 separation legs (`leanspec/C114_AC3_SEPARATION.lean.txt`, re-proved here)

`C111_C114_REFUTATION.lean.txt` derives `False` from the FROZEN axioms using (1) the one-node
trees `⟨[vK 1]⟩`, `⟨[vK 2]⟩`, identical in every field the frozen stratum reads and differing
only in the formula-read `kappa`; and (2) the empty shapes `⟨[], 1⟩`, `⟨[], 2⟩`, the same
disease at `kappa0`.  The re-signed statements carry the `(HT-orbit)` rules as hypotheses, and
the two lemmas below show those hypotheses hold on the refuting instances EXACTLY when the
orbit factor is `1` — so both refutation arguments are cut at their first step. -/

/-- the κ-separating one-node family of `C111_C114_REFUTATION.lean.txt`, verbatim: the nodes
are identical in every field except the orbit factor `kappa`. -/
def vK (k : ℕ) : HTNode := ⟨0, 0, fun _ => 0, 0, ∅, fun _ _ => ⟨0⟩, k⟩

/-- a one-node tree has no children (whatever its `parent` field). -/
theorem children_of_one_node (v : HTNode) (p : ℕ → ℕ) :
    (HTTree.mk [v] p).children 0 = ∅ := by
  classical
  simp [HTTree.children]

/-- on a one-node tree the κ-rule says exactly `kappa = 1` (both factorial products are
empty). -/
theorem kappaRule_one_node_iff' (v : HTNode) (p : ℕ → ℕ) :
    (HTTree.mk [v] p).KappaRule 0 ↔ v.kappa = 1 := by
  classical
  have hch : (HTTree.mk [v] p).children 0 = ∅ := children_of_one_node v p
  simp only [HTTree.KappaRule, hch, Finset.image_empty, Finset.prod_empty, mul_one]
  constructor
  · intro h; simpa using h
  · intro h; simpa using h

/-- **the branch refutation geometry is separated**: the A-C.3 κ-rule holds at the root of
`⟨[vK k]⟩` exactly when `k = 1`, so `ht_branch`'s hypothesis `hkappa` fails at `k = 2` and the
equinumerous-strata argument of `c114_branch_frozen_false` never starts. -/
theorem kappaRule_one_node_iff (k : ℕ) :
    (HTTree.mk [vK k] fun _ => 0).KappaRule 0 ↔ k = 1 :=
  kappaRule_one_node_iff' (vK k) (fun _ => 0)

/-- **the global refutation geometry is separated**: the A-C.3 κ₀-rule holds at the EMPTY shape
exactly when `kappa0 = 1`, so `ht_global`'s hypothesis `hkappa0` fails at `k = 2` and
`c114_global_frozen_false`'s argument never starts. -/
theorem kappa0Rule_empty_iff (k : ℕ) : (HTShape.mk [] k).Kappa0Rule ↔ k = 1 := by
  classical
  simp [HTShape.Kappa0Rule]

/-- the same for an arbitrary shape with no branches. -/
theorem kappa0Rule_nil_iff (S : HTShape) (h : S.branches.length = 0) :
    S.Kappa0Rule ↔ S.kappa0 = 1 := by
  classical
  simp only [HTShape.Kappa0Rule, h, Finset.range_zero, Finset.image_empty, Finset.prod_empty,
    mul_one]

/-- **the D5 clause subsumes A-C.2's designed `s`-pin**: a recentring by `π ^ s` times a
representative of a NONZERO class has Gauss valuation exactly `s`.  This is why the designed
`s`-pin `gaussVal (K i − K (parent i)) = s_i` is NOT carried separately (A-F.12 minimality
applied with a proof rather than an assertion). -/
theorem repRecentring_gaussVal (hπ : Irreducible π) {z : Polynomial O} (hz : gaussVal z = 0)
    (s : ℕ) : gaussVal (Polynomial.C (π ^ s) * z) = (s : ℕ∞) := by
  rw [gaussVal_mul hπ, gaussVal_C_pow hπ, hz, add_zero]

/-- **the DISCLOSED non-tooth `hfence`**: `OrderOne` holds on the WHOLE refuting one-node
family, so it separates nothing there — the blueprint TEETH line's "a SCOPE fence with no
truth tooth in the grid", machine-recorded. -/
theorem orderOne_of_one_node_vK (k : ℕ) : (HTTree.mk [vK k] fun _ => 0).OrderOne := by
  intro i hi u l hmem
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  simp [vK] at hmem

/-- **the DISCLOSED depth-0 triviality of `hnode`**: on ANY one-node tree the per-node
exponent inequality holds unconditionally (the child sum is empty).  Not a defect — finding
D6's counterexamples are all multi-child — but recorded so `hnode` is not read as a tooth at
depth 0. -/
theorem nodeExponent_of_one_node (v : HTNode) (p : ℕ → ℕ) (N : ℕ) :
    (HTTree.mk [v] p).NodeExponent N := by
  classical
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  rw [children_of_one_node, Finset.sum_empty]
  exact Nat.zero_le _

/-! ## 4. `IsRepSystem` is satisfiable (finding D5's clause is not a vacuity) -/

/-- **the D5 clause is SATISFIABLE at every positive degree**: the level-1 block lifts
(`blockPoly` at `N = 1`) form a system of representatives of the degree-`< d` residue classes.
So `hR : IsRepSystem R Φ.natDegree` does not empty `ht_branch`. -/
private theorem one_le_gaussVal_sub_iff (hπ : Irreducible π) [Finite (ResidueField O)]
    {d : ℕ} {x y : Polynomial O} (hx : x.natDegree < d) (hy : y.natDegree < d) :
    (1 : ℕ∞) ≤ gaussVal (x - y) ↔
      proj O d 1 (fun i => x.coeff i) = proj O d 1 (fun i => y.coeff i) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ gaussVal (x - y) ↔ ∀ i, π ^ 1 ∣ (x - y).coeff i :=
    le_gaussVal_iff hπ
  simp only [Nat.cast_one] at h1
  rw [h1]
  constructor
  · intro h
    funext i
    show Ideal.Quotient.mk _ (x.coeff (i : ℕ)) = Ideal.Quotient.mk _ (y.coeff (i : ℕ))
    refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ 1 _).2 ?_)
    simpa [Polynomial.coeff_sub] using h (i : ℕ)
  · intro h i
    by_cases hi : i < d
    · have h2 : x.coeff i - y.coeff i ∈ (IsLocalRing.maximalIdeal O) ^ 1 :=
        Ideal.Quotient.eq.1 (congrFun h ⟨i, hi⟩)
      simpa [Polynomial.coeff_sub] using (mem_maximalIdeal_pow_iff_dvd hπ 1 _).1 h2
    · have hx0 : x.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hy0 : y.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [Polynomial.coeff_sub, hx0, hy0]

theorem exists_isRepSystem (hπ : Irreducible π) [Finite (ResidueField O)] {d : ℕ} (hd : 0 < d) :
    ∃ R : Set (Polynomial O), IsRepSystem R d := by
  classical
  refine ⟨Set.range (fun c : Coeff O d 1 => C109asm.blockPoly c), ?_, ?_⟩
  · rintro r ⟨c, rfl⟩
    exact C109asm.blockPoly_natDegree_lt hd c
  · intro a ha
    refine ⟨C109asm.blockPoly (proj O d 1 (fun i => a.coeff i)), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · rw [one_le_gaussVal_sub_iff hπ ha (C109asm.blockPoly_natDegree_lt hd _)]
      exact (C109asm.blockPoly_proj _).symm
    · rintro y ⟨⟨c, rfl⟩, hy⟩
      rw [one_le_gaussVal_sub_iff hπ ha (C109asm.blockPoly_natDegree_lt hd c),
        C109asm.blockPoly_proj c] at hy
      rw [hy]

/-- and it is not implied either: `R = ∅` FAILS at every positive degree, so the clause has
content. -/
theorem not_isRepSystem_empty {d : ℕ} (hd : 0 < d) :
    ¬ IsRepSystem (∅ : Set (Polynomial O)) d := by
  intro h
  obtain ⟨r, hr, -⟩ := h.2 0 (by simpa using hd)
  exact hr.1

/-! ## 5. The count laws at the certified degenerate strata

`ht_branch` and `ht_global` in general are BLOCKED (module docstring; record
`C114_BLOCKED_2026-08-20.md`).  What is PROVED here is each law at the stratum where the
A-C.2 refutation lived: the one-node tree and the empty shape.  The binder lists are the FULL
A-C.3 re-signed lists, byte-frozen, plus one scope equation (`hone` / `hnil`). -/

set_option linter.overlappingInstances false in
/-- transport of exact-cell membership along an equality of keys.  (The two instance pairs may
differ; `IsDomain` and `UniqueFactorizationMonoid` are `Prop`-classes, so after `subst` they
are proof-irrelevantly equal.) -/
theorem htCell_congr_key {Ψ Φ : Polynomial O} (h : Ψ = Φ)
    [IsDomain (resField Ψ)] [UniqueFactorizationMonoid (resField Ψ)]
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    (v : HTNode) (f : Polynomial O) :
    f ∈ htCell π Ψ v ↔ f ∈ htCell π Φ v := by
  subst h
  exact Iff.rfl

/-- the one-node normal form of the realization predicate: on a single-node tree `htRealizes`
is exactly membership in that node's exact cell (the recentring and sibling clauses are
vacuous, and `K 0 = Φ` collapses the key tower). -/
theorem htRealizes_one_node_iff {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    (v : HTNode) (p : ℕ → ℕ) (R : Set (Polynomial O)) (f : Polynomial O) :
    htRealizes π Φ f (HTTree.mk [v] p) R ↔ f ∈ htCell π Φ v := by
  constructor
  · rintro ⟨G, K, instD, instU, hK0, hG0, hkey, hcell, -, -⟩
    haveI := instD 0
    haveI := instU 0
    have h0 := hcell 0 (by simp)
    rw [← hG0]
    exact (htCell_congr_key hK0 v (G 0)).1 h0
  · intro hf
    refine ⟨fun _ => f, fun _ => Φ, fun _ => inferInstance, fun _ => inferInstance,
      rfl, rfl, fun i _ => hΦ, ?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      exact hf
    · intro i hi hi'
      simp only [List.length_singleton] at hi'
      omega
    · intro i i' hi hi' hlt hlt' hne _ _
      simp only [List.length_singleton] at hlt
      omega

set_option linter.unusedVariables false in
set_option linter.overlappingInstances false in
/-- **NODE C.114, `(HT-branch)` at the one-node stratum** — the A-C.3 re-signed statement,
byte-frozen, with the single scope equation `hone : t.nodes.length = 1`.  This is the `k = 1`
member of the family that refuted the A-C.1 freeze: `hkappa` forces `kappa = 1` there
(`kappaRule_one_node_iff`) and the conclusion is then TRUE. -/
theorem ht_branch_one_node [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)] [Finite (resField Φ)]
    (R : Set (Polynomial O)) (hR : IsRepSystem R Φ.natDegree)
    (t : HTTree) (N : ℕ) (hroot : 0 < t.nodes.length)
    (hwf : t.WF) (hnodewf : t.NodeWF) (hcons : t.Conservative)
    (hcompl : t.ChildComplete) (hfence : t.OrderOne) (hvis : t.WindowVisible N)
    (hkappa : ∀ i, i < t.nodes.length → t.KappaRule i)
    (hnode : t.NodeExponent N)
    (hone : t.nodes.length = 1) :
    Nat.card {c : Coeff O ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) N //
        ∃ a : Fin ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) → O,
          proj O ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) N a = c ∧
          htRealizes π Φ (monicPoly a) t R}
      = htBranchCount (Nat.card (resField Φ))
          (fun lam => sideCensus (resField Φ) lam) t N := by
  classical
  obtain ⟨tn, tp⟩ := t
  obtain ⟨v, rfl⟩ : ∃ v, tn = [v] := by
    match tn, hone with
    | [a], _ => exact ⟨a, rfl⟩
  -- the three per-node facts the cell count needs, plus `kappa = 1`
  have hk1 : v.kappa = 1 := (kappaRule_one_node_iff' v tp).1 (hkappa 0 (by simp))
  have hvWF : v.WF := hnodewf 0 (by simp)
  have hvis0 : ∀ j, j ≤ v.m → v.Pceil j < N := hvis 0 (by simp)
  show Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
      ∃ a : Fin (v.m * Φ.natDegree) → O,
        proj O (v.m * Φ.natDegree) N a = c ∧
        htRealizes π Φ (monicPoly a) (HTTree.mk [v] tp) R}
    = htBranchCount (Nat.card (resField Φ))
        (fun lam => sideCensus (resField Φ) lam) (HTTree.mk [v] tp) N
  have hstrat : Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
      ∃ a : Fin (v.m * Φ.natDegree) → O,
        proj O (v.m * Φ.natDegree) N a = c ∧
        htRealizes π Φ (monicPoly a) (HTTree.mk [v] tp) R}
      = Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
        ∃ a : Fin (v.m * Φ.natDegree) → O,
          proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    constructor
    · rintro ⟨a, ha, hr⟩
      exact ⟨a, ha, (htRealizes_one_node_iff hΦ v tp R _).1 hr⟩
    · rintro ⟨a, ha, hr⟩
      exact ⟨a, ha, (htRealizes_one_node_iff hΦ v tp R _).2 hr⟩
  -- `htBranchCount` never reads `parent`, so C.115's depth-zero value applies verbatim
  have hbc : htBranchCount (Nat.card (resField Φ)) (fun lam => sideCensus (resField Φ) lam)
      (HTTree.mk [v] tp) N
      = v.kappa * (∏ p ∈ v.sides, sideCensus (resField Φ) (v.sideType p.1 p.2))
        * Nat.card (resField Φ) ^ v.B N :=
    ht_depth_zero (Nat.card (resField Φ)) (fun lam => sideCensus (resField Φ) lam) v N
  rw [hstrat, ht_node_cell_card hπ hΦ v hvWF N hvis0, hbc, hk1]
  ring

set_option linter.unusedVariables false in
set_option linter.overlappingInstances false in
/-- **the DISCLOSED non-tooth `hroot`**: at the EMPTY tree the A-C.3 re-signed branch
conclusion is TRUE (both sides are `1`), so dropping `hroot` would not falsify the statement —
it is a scope/read clause, not a truth tooth. -/
theorem ht_branch_empty_tree [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)] [Finite (resField Φ)]
    (R : Set (Polynomial O)) (hR : IsRepSystem R Φ.natDegree)
    (t : HTTree) (N : ℕ) (hnil : t.nodes.length = 0) :
    Nat.card {c : Coeff O ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) N //
        ∃ a : Fin ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) → O,
          proj O ((t.nodes.getD 0 HTNode.default0).m * Φ.natDegree) N a = c ∧
          htRealizes π Φ (monicPoly a) t R}
      = htBranchCount (Nat.card (resField Φ))
          (fun lam => sideCensus (resField Φ) lam) t N := by
  classical
  obtain ⟨tn, tp⟩ := t
  obtain rfl : tn = [] := by
    match tn, hnil with
    | [], _ => rfl
  -- the read node is the junk default, of multiplicity `0`, so the coefficient box is a point
  have hm : (HTNode.default0).m * Φ.natDegree = 0 := by simp [HTNode.default0]
  haveI hE : IsEmpty (Fin ((HTNode.default0).m * Φ.natDegree)) := by
    rw [hm]; infer_instance
  haveI : Unique (Coeff O ((HTNode.default0).m * Φ.natDegree) N) := Pi.uniqueOfIsEmpty _
  show Nat.card {c : Coeff O ((HTNode.default0).m * Φ.natDegree) N //
      ∃ a : Fin ((HTNode.default0).m * Φ.natDegree) → O,
        proj O ((HTNode.default0).m * Φ.natDegree) N a = c ∧
        htRealizes π Φ (monicPoly a) (HTTree.mk [] tp) R}
    = htBranchCount (Nat.card (resField Φ))
        (fun lam => sideCensus (resField Φ) lam) (HTTree.mk [] tp) N
  -- every class is realized: all six `htRealizes` clauses are vacuous over the empty tree
  have hall : ∀ c : Coeff O ((HTNode.default0).m * Φ.natDegree) N,
      ∃ a : Fin ((HTNode.default0).m * Φ.natDegree) → O,
        proj O ((HTNode.default0).m * Φ.natDegree) N a = c ∧
        htRealizes π Φ (monicPoly a) (HTTree.mk [] tp) R := by
    intro c
    refine ⟨fun _ => 0, Subsingleton.elim _ _, ?_⟩
    exact ⟨fun _ => monicPoly (fun _ => (0 : O)), fun _ => Φ, fun _ => inferInstance,
      fun _ => inferInstance, rfl, rfl, by simp, by simp, by simp, by simp⟩
  have hcard : Nat.card {c : Coeff O ((HTNode.default0).m * Φ.natDegree) N //
      ∃ a : Fin ((HTNode.default0).m * Φ.natDegree) → O,
        proj O ((HTNode.default0).m * Φ.natDegree) N a = c ∧
        htRealizes π Φ (monicPoly a) (HTTree.mk [] tp) R} = 1 := by
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ?_⟩
    exact ⟨⟨default, hall default⟩⟩
  rw [hcard]
  simp [htBranchCount]

set_option linter.unusedVariables false in
set_option linter.overlappingInstances false in
/-- **NODE C.114, `(HT-global)` at the empty-shape stratum** — the A-C.3 re-signed statement,
byte-frozen, with the single scope equation `hnil : S.branches.length = 0`.  This is the
`k = 1` member of the family that refuted the A-C.1 global freeze: `hkappa0` forces
`kappa0 = 1` there (`kappa0Rule_empty_iff`) and the conclusion is then TRUE. -/
theorem ht_global_empty_shape [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    (hπ : Irreducible π)
    (S : HTShape) (Φb : ℕ → Polynomial O) (n N : ℕ)
    (hn : n = ((List.range S.branches.length).map
        (fun i => (S.branches.getD i (0, 0, default)).1
          * (S.branches.getD i (0, 0, default)).2.1)).sum)
    (hkeys : ∀ i, i < S.branches.length → IsKey (Φb i) ∧
        (Φb i).natDegree = (S.branches.getD i (0, 0, default)).1)
    (hdistinct : ∀ i j, i < S.branches.length → j < S.branches.length → i ≠ j →
        (Φb i).map (IsLocalRing.residue O) ≠ (Φb j).map (IsLocalRing.residue O))
    (R : ℕ → Set (Polynomial O))
    (hR : ∀ i, i < S.branches.length → IsRepSystem (R i) (Φb i).natDegree)
    (hbr : ∀ i, i < S.branches.length →
        (S.branches.getD i (0, 0, default)).2.2.WF ∧
        (S.branches.getD i (0, 0, default)).2.2.NodeWF ∧
        (S.branches.getD i (0, 0, default)).2.2.Conservative ∧
        (S.branches.getD i (0, 0, default)).2.2.ChildComplete ∧
        (S.branches.getD i (0, 0, default)).2.2.OrderOne ∧
        (S.branches.getD i (0, 0, default)).2.2.WindowVisible N ∧
        (∀ k, k < (S.branches.getD i (0, 0, default)).2.2.nodes.length →
          (S.branches.getD i (0, 0, default)).2.2.KappaRule k) ∧
        (S.branches.getD i (0, 0, default)).2.2.NodeExponent N)
    (hkappa0 : S.Kappa0Rule)
    (instD : ∀ i, IsDomain (resField (Φb i)))
    (instU : ∀ i, UniqueFactorizationMonoid (resField (Φb i)))
    (instFin : ∀ i, Finite (resField (Φb i)))
    (hnil : S.branches.length = 0) :
    Nat.card {c : Coeff O n N // ∃ a : Fin n → O, proj O n N a = c ∧
        ∃ σ : ℕ → ℕ, S.IsSlotAssign σ ∧
        ∃ G : ℕ → Polynomial O,
          monicPoly a = ∏ i ∈ Finset.range S.branches.length, G i ∧
          ∀ i, i < S.branches.length → (G i).Monic ∧
            (G i).map (IsLocalRing.residue O)
              = ((Φb i).map (IsLocalRing.residue O))
                  ^ (S.branches.getD (σ i) (0, 0, default)).2.1 ∧
            ((S.branches.getD (σ i) (0, 0, default)).2.1 = 1 ∨
              htRealizes π (Φb i) (G i)
                (S.branches.getD (σ i) (0, 0, default)).2.2 (R i))}
      = htGlobalCount S (residueCard O)
          (fun i lam => @sideCensus (resField (Φb i)) _ (instD i) (instU i) (instFin i) lam) N := by
  classical
  obtain ⟨sb, k0⟩ := S
  obtain rfl : sb = [] := by
    match sb, hnil with
    | [], _ => rfl
  have hn0 : n = 0 := by simpa using hn
  subst hn0
  haveI : Unique (Coeff O 0 N) := Pi.uniqueOfIsEmpty _
  -- `hkappa0` forces `kappa0 = 1` on the empty shape: the refuting `k = 2` member is excluded
  have hk0 : k0 = 1 := (kappa0Rule_nil_iff (HTShape.mk [] k0) rfl).1 hkappa0
  have hall : ∀ c : Coeff O 0 N,
      ∃ a : Fin 0 → O, proj O 0 N a = c ∧
        ∃ σ : ℕ → ℕ, (HTShape.mk [] k0).IsSlotAssign σ ∧
        ∃ G : ℕ → Polynomial O,
          monicPoly a = ∏ i ∈ Finset.range (HTShape.mk [] k0).branches.length, G i ∧
          ∀ i, i < (HTShape.mk [] k0).branches.length → (G i).Monic ∧
            (G i).map (IsLocalRing.residue O)
              = ((Φb i).map (IsLocalRing.residue O))
                  ^ ((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.1 ∧
            (((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.1 = 1 ∨
              htRealizes π (Φb i) (G i)
                ((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.2 (R i)) := by
    intro c
    refine ⟨fun _ => 0, Subsingleton.elim _ _, id, ?_, fun _ => 1, ?_, by simp⟩
    · refine ⟨?_, by simp⟩
      simp [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn]
    · simp [monicPoly]
  have hcard : Nat.card {c : Coeff O 0 N // ∃ a : Fin 0 → O, proj O 0 N a = c ∧
      ∃ σ : ℕ → ℕ, (HTShape.mk [] k0).IsSlotAssign σ ∧
      ∃ G : ℕ → Polynomial O,
        monicPoly a = ∏ i ∈ Finset.range (HTShape.mk [] k0).branches.length, G i ∧
        ∀ i, i < (HTShape.mk [] k0).branches.length → (G i).Monic ∧
          (G i).map (IsLocalRing.residue O)
            = ((Φb i).map (IsLocalRing.residue O))
                ^ ((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.1 ∧
          (((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.1 = 1 ∨
            htRealizes π (Φb i) (G i)
              ((HTShape.mk [] k0).branches.getD (σ i) (0, 0, default)).2.2 (R i))} = 1 := by
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ?_⟩
    exact ⟨⟨default, hall default⟩⟩
  rw [hcard]
  simp [htGlobalCount, hk0]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.HTTree.IsDesc
#print axioms Uniformity.Density.Tower.HTTree.children
#print axioms Uniformity.Density.Tower.HTTree.SameHist
#print axioms Uniformity.Density.Tower.HTTree.KappaRule
#print axioms Uniformity.Density.Tower.HTTree.NodeWF
#print axioms Uniformity.Density.Tower.HTTree.Conservative
#print axioms Uniformity.Density.Tower.HTTree.ChildComplete
#print axioms Uniformity.Density.Tower.HTTree.OrderOne
#print axioms Uniformity.Density.Tower.HTTree.WindowVisible
#print axioms Uniformity.Density.Tower.HTTree.NodeExponent
#print axioms Uniformity.Density.Tower.HTShape.Kappa0Rule
#print axioms Uniformity.Density.Tower.HTShape.IsSlotAssign
#print axioms Uniformity.Density.Tower.IsRepSystem
#print axioms Uniformity.Density.Tower.htRealizes
#print axioms Uniformity.Density.Tower.kappa_unique_of_kappaRule
#print axioms Uniformity.Density.Tower.kappa0_unique_of_kappa0Rule
#print axioms Uniformity.Density.Tower.children_of_one_node
#print axioms Uniformity.Density.Tower.kappaRule_one_node_iff
#print axioms Uniformity.Density.Tower.kappa0Rule_empty_iff
#print axioms Uniformity.Density.Tower.repRecentring_gaussVal
#print axioms Uniformity.Density.Tower.orderOne_of_one_node_vK
#print axioms Uniformity.Density.Tower.nodeExponent_of_one_node
#print axioms Uniformity.Density.Tower.exists_isRepSystem
#print axioms Uniformity.Density.Tower.not_isRepSystem_empty
#print axioms Uniformity.Density.Tower.htRealizes_one_node_iff
#print axioms Uniformity.Density.Tower.ht_branch_one_node
#print axioms Uniformity.Density.Tower.ht_branch_empty_tree
#print axioms Uniformity.Density.Tower.ht_global_empty_shape

end AxCheck
