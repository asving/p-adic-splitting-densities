# M07-sibjc — Problem brief: sibling independence (SIB) and multi-side Jacobian coupling (JC-multi) at the pinned canonical-tree instance

**Target obligation:** the hypothesis row `BK.sibjc` of the capstone kernel ledger —
`sibjc : @SibJcRows n p ⟨hp⟩ X F seam Tpin` at
`lean/LeanUrat/MovesU/BridgeKernels.lean:240`, with the structure `SibJcRows`
defined at `lean/LeanUrat/MovesU/DefsLedger.lean:389`. There is no `sorry`
token: this is a named hypothesis row of the capstone theorem chain, to be
either proved at the pinned instance or supported by a faithfulness-audited
literature citation. Date: 2026-07-31.

This brief is self-contained. It re-expands every project-internal name; the
reader is assumed to know p-adic fields, Newton polygons, MacLane–Okutsu–Montes
(OM) theory and Igusa-style p-adic volume computations, but nothing about this
repository.

---

## 1. Role in the project

The project formalizes a uniformity theorem: for each degree n and each
splitting type σ (a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n), the Haar
density of monic degree-n polynomials over ℤ_p whose splitting over ℚ_p has
type σ is given by one rational function R_σ(q) evaluated at q = p, uniformly
in p. The formal proof classifies polynomials by their canonical OM
factorization trees and computes the density of each tree-fiber as a product of
local factors over the tree's "read sites". The product formula needs two
count-exact laws about the classifier tree, called (SIB) and (JC-multi):

* **(SIB)** — at every branching vertex of the OM tree, the continuations of
  the several sibling branches are *exactly independent* (as counting measures
  at every finite level) conditional on the branching vertex's full digit-cell
  datum.
* **(JC-multi)** — at a read site whose Newton-polygon window has k ≥ 2 sides,
  the site's joint digit cell has conditional mass exactly the product of the
  per-side nominal volumes (equivalently: the union of the k per-side equation
  systems, over disjoint fresh-coordinate spans, cuts exactly the product
  codimension).

These two laws are consumed by the tree-fiber counting theorem (`MovesT.treeN`,
file `lean/LeanUrat/MovesT/E11_treeN.lean`) as explicit hypotheses; the row
`BK.sibjc` asserts them at the specific ("pinned") instance the capstone
constructs. Everything below unfolds the Lean statement to standard
mathematics.

---

## 2. The ambient objects

### 2.1 Boxes, charts, decoded polynomials

Fix a prime p, a degree n ≥ 2, and a level N ≥ 1. The **box** is

    Box p m := (Fin m → 𝔽_p),   with m := n·N

— the space of n·N base-p digits, of cardinality p^{nN}. A box point x encodes
a monic degree-n polynomial over ℤ_p known to precision p^N per coefficient:
the **decode** map is

    dec(x) := X^n + Σ_{i<n} C(coeff_i(x))·X^i ∈ ℤ_p[X],

where coeff_i(x) := Σ_{k<N} x(i·N + k)·p^k (each coefficient's N digits sit at
the chart positions i·N, …, i·N + N − 1; canonical Teichmüller-free lift). The
**level-0 chart** χ : Fin n → Fin (n·N) selects the digit position of each
coefficient's constant digit; at the pinned instance χ(i) = i·N. The **level-0
reduction** of x is

    redPoly χ x := z^n + Σ_{i<n} x(χ(i))·z^i ∈ 𝔽_p[z],

and for ḡ : Fin n → 𝔽_p the **root cell** is
rootCell χ ḡ := {x : x(χ(i)) = ḡ(i) ∀i} — the stratum "reduction mod p equals
the fixed monic ḡ".

### 2.2 Histories and nodes (OM chains)

A **node** ν is the record of one OM "window read": it carries a species
(root / increment / recentering), the current stage data σ (key polynomial Φ of
degree Dwidth, the current residue field K in the tower of finite extensions of
𝔽_p, developments), one Newton-polygon side with slope data (e, h) occupying
slots [s0, s0 + wSide], the residual polynomial ψ ∈ K[y] of degree g chosen on
that side, its multiplicity μ, the selected residue root z̄ ∈ K^×, an anchor
index a, the fixed on-side pattern digits, the side as a line in absolute
v_p-scale (`ν.line`, with a rational `slope`), and a recorded lift/center.
Proof fields force each recorded datum to carry its OM meaning.

A **history** H is a nonempty finite list of nodes forming one branch of the OM
tree (a MacLane chain: root read, then increments/recenterings). Standard
accumulated invariants: accE H := Π_r e_r, accF H := Π_r g_r over the reads of
H. The **τ-irr halting predicate** is

    IrrHalts H :⟺ accE(H)·accF(H) = (last node's childWidth)·(last node's μ)

(the accumulated ramification·residue product saturates the cluster degree —
the branch has isolated one irreducible p-adic factor with known (e, f)). The
**τ-ns (no-side) halting** of a realized branch is "the state is realized but
has no children" (see 2.3).

### 2.3 The canonical tree model (the pinned T)

A **tree model** T on the box is a pair of relations

    T.mem   : Option History → Box → Prop     (state realized at x)
    T.child : Option History → Node → Box → Prop  (next read at x)

subject to: the root (`none`, the empty chain) is realized at every x; a
one-node chain is realized iff its node is a root-child; a chain H.snoc ν is
realized iff H is realized and ν is a child of H at x; every realized chain is
coherent, realizable, and policy-canonical. **The pinned instance** is the
constructed canonical model (`MovesD/TreeCan.lean`, `canTreeModelN`):

    mem (some H) x ⟺ ReadsOf n (dec x) H ∧ Realizable H ∧ IsCanonPres H

— H is precisely an initial run of the OM factorization algorithm on dec(x),
with lifts pinned by a deterministic canonical policy `pol` (`canPolicy`,
lift-of-node rule blind to the recorded lift) and residue roots pinned to a
canonical enumeration. `child o ν x` is run-extension: the one-read extension
of o by ν is realized at x. (Caveat of record: the concrete `canPolicy` data is
a currently-`sorry`d designer item; the row is stated over the constructed
`TreePin` whose model fields are these `canTreeModelN p n N (canPolicy p)`.)

At the pinned instance the residue-field type parameter is F := 𝔽_p (the tower
fields live inside stage data).

### 2.4 Entrance states and their events

An **entrance state** es is one of three constructors:

* `.amb` — the ambient box; its event is all of Box;
* `.red ḡ ψ` — a level-0 reduction cell keyed by the reduction ḡ together with
  one irreducible factor ψ ∈ 𝔽_p[z] of ḡ (the track); its event is
  rootCell χ ḡ;
* `.st H` — a realized chain state; its event is stateEvent T (some H) =
  {x : T.mem (some H) x}.

Write entEvent T χ es for these events, and stOf es ∈ Option History for the
underlying state (`some H` for `.st H`, else `none`).

### 2.5 Cell assignments (the joint digit-cell layer)

A **cell datum** CA for the model T (`MovesT.CellData`) consists of:

* a finite type `Cell`;
* a joint read map `cellOf : EntSt → Box → Cell` with a locality bound
  (`cell_local`: cellOf es x depends only on digit positions below a level
  `cellLevel es` under a level map `levelOf`);
* a branch roster `branchSetOf : Cell → Finset Node`, with:
  - `child_cell` (at chain states, an **iff**): for x realizing H,
    ν ∈ branchSetOf (cellOf (.st H) x) ⟺ T.child (some H) ν x;
  - `child_root_sub` (at `.amb`, one inclusion): every root-child of x lies in
    branchSetOf (cellOf .amb x);
  - `child_cell_red` (at `.red`, one inclusion): on rootCell χ ḡ, membership in
    branchSetOf (cellOf (.red ḡ ψ) x) implies root-childhood at x;
  - `child_red_uniform`: root-child behavior is cellOf-(·red)-constant — two
    points of one `.red` cell have identical root-child sets;
* a per-site read map `branchCellOf : EntSt → Node → Box → Cell` with the sole
  law `branch_cell_joint`: branchCellOf es ν factors through cellOf es (equal
  joint cells give equal site-cell values).

A **cell assignment** (`MovesT.CellAssign`, relative to the chart χ and a track
accessor trackOf : Node → 𝔽_p[z]) is a CellData plus the covering field
`child_cover`: for every x in a root cell and every irreducible ψ with
multiplicity ≥ 2 in redPoly χ x, there exists a root child ν with trackOf ν = ψ
lying in branchSetOf (cellOf (.red ḡ ψ) x).

**Conditioning events.** For a cell value c:

    cellEventE  T CA χ es c   := {x ∈ entEvent es | cellOf es x = c}
    siteCellEvent T CA χ es ν c := {x ∈ entEvent es | branchCellOf es ν x = c}.

### 2.6 Prescribed-subtree continuation events (ContFiber)

Fix a site (o : Option History) and a child-root datum ν (root-species node if
o = none, a snoc-extension node otherwise); write childHist(o, ν) for the
extended one-longer chain. Given a set Tsub of histories, a leaf-verdict
assignment leafSpec : History → Option Vd (Vd = finite multisets of pairs
(E, F) ∈ ℕ²_{≥1}), and an ns-marker nsSpec : History → Prop, the event

    ContFiber T o ν hν Tsub leafSpec nsSpec ⊆ Box

holds at x iff:

1. Tsub is **exactly** the set of realized continuations: H' ∈ Tsub ⟺
   childHist(o,ν) is a prefix of H', x realizes H', and no intermediate proper
   prefix H'' (childHist ⪯ H'' ⪯ H', H'' ≠ H') halts (neither IrrHalts H'' nor
   ns-halts at x);
2. every maximal H' ∈ Tsub halts compatibly with the prescription: either
   IrrHalts H' with ¬nsSpec H' and leafSpec H' = the τ-irr verdict of H', or H'
   ns-halts at x (realized, no children) with ¬IrrHalts H', nsSpec H', and
   leafSpec H' = the τ-ns verdict;
3. no non-maximal H' ∈ Tsub halts.

In words: "branch ν's continuation realizes exactly the prescribed finite
subtree Tsub, with the prescribed leaf verdicts". In the laws below the
quantifier supplies Tsub, leafSpec, nsSpec with Tsub **finite**.

### 2.7 Side splits and multi-side sites

The per-read fresh-equation carrier is `FreshData p m`: a finite list of
clauses, each clause cl having a support ⊆ Fin m, a codimension codim ∈ ℕ, a
satisfaction predicate reading only its support, and the exact-count law
#{y supported on cl.support : cl.sat y}·p^codim = p^{|support|}; distinct
clauses of one FreshData have disjoint supports. `fd.mstar := Σ_cl codim`.

Given a cell c and fresh data fd, a **side split** ss (`MovesT.SideSplit`)
consists of: k ∈ ℕ; a side assignment sideOf : Node → Fin k such that every
side is hit by some member of branchSetOf c; a partition clausesOf : Fin k →
Finset Clause of the membership set of fd.clauses into pairwise-disjoint
groups; spans sideSpan : Fin k → Finset (Fin m), pairwise disjoint, containing
the supports of their side's clauses; a strictly monotone slope list
hullSlope : Fin k → ℚ; and the read-off law `hside_read`: every
ν ∈ branchSetOf c has ν.line.slope = hullSlope (sideOf ν). The **side
exponent** is sideExp ss j := (clausesOf j).card (the clause COUNT of side j).
A **multi-side site** is one with 2 ≤ ss.k (`IsMultiSideSite`).

---

## 3. The statement (the three laws)

The row is the following structure (Lean, verbatim from
`lean/LeanUrat/MovesU/DefsLedger.lean:389`; `TP` is the pinned `TreePin`, whose
fields `TP.pol`, `TP.Tm N`, `TP.chart N hN` are the canonical policy, the
canonical tree model at level N, and the chart of §2.1):

```lean
structure SibJcRows {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {seam : TreeSeam n p X F} (TP : TreePin n p X F seam) : Prop where
  sib : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf),
    MovesT.SibCount (TP.Tm N) CA.toCellData (TP.chart N hN)
  sib_at : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf)
    (es : MovesT.EntSt p (ZMod p) n) (ν₀ : MovesC.Node p (ZMod p))
    (c : CA.toCellData.Cell)
    (S : MovesC.Node p (ZMod p) → Set (MovesD.Box p (n * N))),
    2 ≤ (CA.toCellData.branchSetOf c).card →
    (∀ ν ∈ CA.toCellData.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | MovesT.ContFiber (TP.Tm N) (MovesT.stOf es) ν hν Tsub leafSpec nsSpec x}) ∨
      S ν = Set.univ) →
    MovesT.SibCountAt (TP.Tm N) CA.toCellData (TP.chart N hN) es ν₀ c S
  jc_multi : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf)
    (es : MovesT.EntSt p (ZMod p) n) (ν₀ : MovesC.Node p (ZMod p))
    (c : CA.toCellData.Cell) (fd : MovesC.FreshData p (n * N))
    (ss : MovesT.SideSplit (TP.Tm N) CA.toCellData c fd),
    MovesT.IsMultiSideSite (TP.Tm N) CA.toCellData c ss →
    MovesT.JCmultiAt (TP.Tm N) CA.toCellData (TP.chart N hN) es ν₀ ss
```

with the three consumed predicates (`lean/LeanUrat/MovesT/Defs.lean`):

```lean
def SibCount (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (es : EntSt p F n) (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEventE T CA χ es c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)

def SibCountAt (T …) (CA …) (χ …) (es : EntSt p F n) (ν₀ : Node p F) (c : CA.Cell)
    (S : Node p F → Set (Box p m)) : Prop :=
  Nat.card ↥(siteCellEvent T CA χ es ν₀ c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
      * (Nat.card ↥(siteCellEvent T CA χ es ν₀ c)) ^ ((CA.branchSetOf c).card - 1)
    = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(siteCellEvent T CA χ es ν₀ c ∩ S ν)

def JCmultiAt (T …) (CA …) (χ …) (es : EntSt p F n) (ν : Node p F) {c : CA.Cell}
    {fd : FreshData p m} (ss : SideSplit T CA c fd) : Prop :=
  Nat.card ↥(siteCellEvent T CA χ es ν c) * p ^ (∑ j : Fin ss.k, ss.sideExp j)
    = Nat.card ↥(entEvent T χ es)
```

**In standard language.** Writing Σ_c for the conditioning event (cellEventE
in `sib`, siteCellEvent in `sib_at`), m for the branch-roster size
(CA.branchSetOf c).card ≥ 2, and S_1, …, S_m for the prescribed-subtree (or
full) events of the roster members:

* (SIB): #(Σ_c ∩ S_1 ∩ … ∩ S_m) · #(Σ_c)^{m−1} = Π_j #(Σ_c ∩ S_j) — exact
  conditional independence of the sibling continuation events given the cell,
  in integer counts (the division-free form of
  μ(⋂ S_j │ Σ_c) = Π μ(S_j │ Σ_c)).
* (JC-multi): #(site cell event) · p^{Σ_j (clause count of side j)} =
  #(entrance event) — the site's exact cell has conditional mass p^{−E} where E
  is the total clause count of the side-split system.

**Quantifier structure (part of the statement).** All of N ≥ 1, trackOf, CA,
es, ν₀, c, S (and for `jc_multi` also fd, ss) are universally quantified, with
only the guards displayed above. In particular the laws are demanded for every
lawful cell assignment CA at the pinned model (not only a designated canonical
one), every entrance state es (compatible or not with c), and in `sib_at` /
`jc_multi` every node ν₀ (the site-read key of siteCellEvent).

---

## 4. What is already proved or recorded around this row

* `MovesT/S1_sibDefs.lean` `sibCount_pair_form` (PROVED): the m = 2
  specialization of SibCount is a formal reshape.
* `MovesT/S3_sibRoot.lean` `sib_root_instance` (PROVED): the `.amb`
  specialization of SibCount, stated under an extra hypothesis
  `RootCellsOf T CA χ` (ambient cells = exact reduction-cell partition:
  cellOf .amb x = cellOf .amb y ⟺ x, y agree at all chart positions).
* `MovesT/S2_sibFalse.lean` `sib_falsifier` (PROVED): there EXISTS a toy pair
  (T, CA) — a rigged two-child model with identical continuation events — for
  which SibCount FAILS. So the law is contentful: it cannot hold for arbitrary
  models; any proof must use the pinned model's structure.
* Consumption: `MovesT/E11_treeN.lean` (`treeN`) consumes SibCountAt and
  JCmultiAt as hypothesis rows quantified over the tree's own realized
  branching/multi-side sites, where a site ledger (`SiteLedger`, `MovesT/Defs`)
  additionally supplies: `presents` (the site's exact cell event equals a
  presented stratum-plus-fresh-system), `state_cell` (the child's state event
  equals the site's exact cell event), `hsplit_exp` (Σ_j sideExp j = fd.mstar),
  `spectator_sol` and `free` (the entrance locus is independent of the fresh
  coordinates). These ledger fields are NOT hypotheses of the `SibJcRows` row
  itself.
* Numerical evidence (`verification/CASE_SIB_SEALED_PREDICTIONS.md` +
  `case_sib_gate.py`, gate PASSED 2026-07-27, 32/32 sealed families exact):
  (L1) p = 5, n = 4, the branching root cell (4,3,3,4) with residual
  (z−1)²(z−2)², both branches continuing — the full 15,625-pair joint word law
  through depth-3 words is exactly uniform on the 14-pin cell (390,625
  members); the committed identity 78,125² = 15,625·390,625 is (SIB) at that
  site; (L2) p = 2 mixed-shape below-halt words, all 16 pairs exact; (L3)
  p = 5, n = 3 m = 3 depth-0 Hensel cell, all 125 cells exact. Perimeter:
  depth ≤ 3, n ≤ 4, m ≤ 3; no all-continuing mixed-shape cell exists at n ≤ 4.
* The mother-note statements and status: `lean/notes/MOVES_2026-07-24.md`
  §T.3 ((SIB), its gate record, and the recorded derivation stop) and the
  TREE-EXP proof consuming both laws (§T.4, lines ≈7280–7540). The recorded
  open kernel there: a stacked one-step joint-uniformity law ((SIB-STEP),
  typed as `MovesT.SibStep`, consumed by nothing yet) plus a cross-sibling
  mechanism at depth ≥ 1.
* Related typed-but-unproven neighbors in `MovesT/Defs.lean`: `SibCountShallow`
  (SIB restricted to non-`.st` entrances), `SibStep`, `PCI` (parent-context
  independence), and `JointStage`/`StageRealized` (the interleaved-filtration
  stage carrier). None is consumed by the capstone chain at HEAD.
* The per-branch (single-path) exact-count engine — the marginal law that each
  single branch's fresh read is exactly uniform on the conditioned cell — is
  the corpus's §C machinery. Its formalization is the HC-2 ladder
  (`lean/LeanUrat/HC2/`), partially proved and partially blocked at HEAD:
  U10a/U10b (floor transport/downset exactness along a chain) PROVED; U10c and
  the assembled per-step re-establishment `zc_step` BLOCKED on two designer
  seed laws (a normalization law plus a value-interior-exclusion law); U17a
  (lift swap at stage reconstruction) BLOCKED on a stage-transition hypothesis
  re-key; U21 (`readsOf_HV`) reduced to a single recorded vertex pin; U26
  (representative independence) deferred on a carried hypothesis; HK15 (a
  concrete gate child stage carrier σ₁ over 𝔽₄) is an unproved skeleton.

---

## 5. What a proof must deliver

Primary: the three fields of `SibJcRows` at the pinned instance — i.e. for
every level N ≥ 1, every track accessor, and every lawful cell assignment CA
over the canonical tree model `canTreeModelN p n N (canPolicy p)` with chart
χ(i) = i·N — as stated in §3, in exact integer-count form.

Acceptable partial deliverables (each must be stated as a precise standalone
lemma):

* a proof of any single field (`sib`, `sib_at`, or `jc_multi`) or of a
  restricted quantifier slice (e.g. fixed entrance species, bounded depth,
  m = 2), with the exact slice displayed;
* a reduction of any field to cleaner, independently checkable statements
  (about polynomials over ℤ_p/𝔽_p, not about this repository's carriers), with
  the reduction proved;
* a counterexample: an explicit lawful instantiation of the quantifiers at the
  pinned instance falsifying a field (this adjudicates as a statement repair,
  since the intended mathematical law is separately evidenced);
* a literature identification: a published statement matching a field's
  content precisely, with a faithfulness analysis (does the Lean row state
  MORE than the citation?).

Any proof must respect: the pinned model is the OM run relation of the decoded
polynomial (§2.3); all counting is exact (no measure limits); and the laws are
claimed at every finite level N simultaneously, with the conditioning events
possibly empty (both sides of each identity then vanish).
