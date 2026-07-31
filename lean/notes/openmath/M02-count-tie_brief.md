# M02-count-tie — problem brief (neutral, self-contained)

**Obligation:** the field `count_tie` of the hypothesis structure
`LeanUrat.MovesU.TreeSeam` (`lean/LeanUrat/MovesU/DefsLedger.lean:235`), to be
supplied at the project's concrete instance (the "bridge instance", described in
§4).  Informally: *for every complete finite certified decision tree T of the
canonical Okutsu–Montes classifier, and every working precision N at or above
T's decision threshold, the number of level-N coefficient classes assigned to T
equals p^{nN} times the (fixed) mass attached to T.*

This brief defines every object precisely.  It assumes familiarity with p-adic
fields, Newton polygons, Okutsu–Montes/MacLane theory, and Haar measure on
coefficient spaces — but no familiarity with this repository.

---

## 1. Mathematical setting

Fix a prime p and a degree n ≥ 1.  The ambient probability space is the set of
monic degree-n polynomials over ℤ_p, identified with ℤ_p^n (coefficient tuples)
carrying Haar measure.  Its level-N finite quotient is

- **the level-N box** `Box p n N := Fin n → ZMod (p^N)` — the p^{nN} classes of
  monic degree-n polynomials with coefficients mod p^N.  The class f denotes
  the polynomial X^n + Σ_{i<n} f_i X^i.  `boxProj` is reduction mod p^N (from
  level N′ ≥ N).

There is also a **digit box** `MovesD.Box p m := Fin m → ZMod p` (m single
base-p digits).  At working level N one uses m = n·N digits, and the two boxes
are identified by a fixed bijection `boxeq N : Box p n N ≃ MovesD.Box p (n·N)`
in the **coefficient-major layout**: digit slot i·N + k holds the k-th base-p
digit of coefficient i (`digitIdx n N i k := ⟨i·N + k, _⟩`,
DefsLedger.lean:289), pinned by the digit law

```lean
boxeq_digits : ∀ (N : ℕ) (f : Box p n N) (i : Fin n),
  f i = ∑ k : Fin N, ((boxeq N f (digitIdx n N i k)).val : ZMod (p ^ N))
          * (p : ZMod (p ^ N)) ^ (k : ℕ)
```

A **splitting type** of degree n is a multiset σ of pairs (e, f) with all
entries ≥ 1 and Σ e·f = n (`SplittingType n`, a subtype of `Multiset (ℕ × ℕ)`;
finitely many for each n).  For a monic degree-n g ∈ ℤ_p[X] with no repeated
irreducible factors, its splitting type is the multiset of
(ramification index, residue degree) of the irreducible factors.

## 2. The abstract interface the obligation is typed over

Three hypothesis structures (all in `MovesU/Defs.lean` and
`MovesU/DefsLedger.lean`); the obligation is a field of the third.

**(a) The classifier** — an abstract "decide the splitting type from finite
precision" device:

```lean
structure ClassifierSpec (n p : ℕ) where
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  trueType  : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ
  baseSection : BaseSection
```

`canonical N f = some σ` reads "the level-N class f is *decided*, with verdict
σ"; `none` reads "undecided at this precision".  `canonical_stable` demands
decisions persist under refinement.  Write

```lean
X.decided σ N := Nat.card {f : Box p n N // X.canonical N f = some σ}
```

**(b) The tree family with masses** — the measure side:

```lean
structure FiberSeries (n p : ℕ) (X : ClassifierSpec n p) where
  Tree : SplittingType n → Type          -- decision trees of verdict type σ
  mass : ∀ σ, Tree σ → ℝ≥0∞              -- μ(fiber T), one number per tree
  thr  : ∀ σ, Tree σ → ℕ                 -- T's decision threshold
  thrSlice : ∀ σ : SplittingType n, ℕ → Finset (Tree σ)
  mem_slice_iff : ∀ σ N T, T ∈ thrSlice σ N ↔ thr σ T ≤ N
  ...
```

(plus `DecidableEq` and the definitional `slice_exhausts`; the Finset type of
`thrSlice` encodes that only finitely many trees have threshold ≤ N).

**(c) The seam** — ties (a) to (b).  THE OBLIGATION IS ITS THIRD FIELD:

```lean
structure TreeSeam (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X) where
  treeOf : ∀ (σ : SplittingType n) (N : ℕ)
    (f : {f : Box p n N // X.canonical N f = some σ}), F.Tree σ
  thr_le : ∀ σ N f, F.thr σ (treeOf σ N f) ≤ N
  count_tie : ∀ (σ : SplittingType n) (N : ℕ) (T : F.Tree σ), F.thr σ T ≤ N →
    F.mass σ T * (p : ℝ≥0∞) ^ (n * N)
      = (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
          treeOf σ N f = T} : ℝ≥0∞)
```

In words: every decided class gets a canonical tree of threshold within the
deciding level, and — `count_tie` — **for every tree T and every N ≥ thr(T),
the number of level-N decided-σ classes assigned to T is exactly
mass(T)·p^{nN}.**  Note the quantifier: *all* T : F.Tree σ, *all* N ≥ thr(T);
the same `mass σ T` serves every N.

From these fields the corpus already derives the partition identity
(`TreeSeam.finiteness_stack`, proved):
decided_σ(N) = p^{nN} · Σ_{T : thr(T) ≤ N} mass(T).

At this abstract level `count_tie` is a hypothesis field — nothing to prove.
The obligation is to **supply it at the intended concrete instance**, described
next.  (A `TreePin` structure, DefsLedger.lean:344, pins the abstract
vocabulary to that instance; its fields are quoted below where relevant.)

## 3. The concrete instance ("the real classifier")

All objects below are constructed in the corpus (files cited).  The tree
vocabulary is the project's formalization of canonical Okutsu–Montes (OM)
factorization trees.

### 3.1 Histories, nodes, trees

A **node** (`MovesC.Node p F`, F = the residue field ZMod p) packages one
Newton-polygon side read of an ongoing OM computation: a line (slope), the
side's lattice width and length data (e, h, s0, wSide, Dwidth), a residual
multiplicity μ, a residual-field datum σ.K, etc.  A **history**
(`MovesC.History p F`) is a nonempty finite chain of nodes — one branch of an
OM computation, with internal numerical laws (slope strictly increasing along
the chain, slope·(e·frame·width) = h, width multiplicativity, a monic-lead law,
…) bundled as `Realizable`/lawfulness predicates.

A **complete finite canonical tree** is

```lean
structure VTree (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  chains : Set (History p F)         -- the branch set, prefix-closed, finite
  hfin : chains.Finite
  hne_nodes / hclosed : ...          -- nonempty chains; prefix-closure
  henV : Multiset Vd                 -- the Hensel payload: verdicts (1, g)
  hhen : ∀ v ∈ henV, ∃ g, 1 ≤ g ∧ v.1 = {(1, g)}
  leafV : History p F → Option Vd    -- leaf verdicts, exactly on maximal chains
  hleaf : ∀ H, (leafV H).isSome ↔ (H ∈ chains ∧ IsMaximalIn chains H)
  nsLeaf : History p F → Prop        -- the "no-side halt" marking on leaves
  hns_leaf : ∀ H, nsLeaf H → H ∈ chains ∧ IsMaximalIn chains H
```

Here `Vd` is a verdict — a multiset of (e, f) pairs with its degree Σe·f.  A
leaf is certified in one of two ways: **(τ-irr)** — the saturation equation
`IrrHalts H` (accumulated e times accumulated f equals width·μ at the last
node; a condition on H's node data alone, no polynomial input), verdict =
(accE, accF); or **(τ-ns)** — the computation halts because the current window
admits no polygon side (`NsHalts`, defined against the model below: the state
is realized and *no* child node is realized), verdict = μ copies of
(accE, accF), and the leaf carries the `nsLeaf` mark.  The tree's total verdict
is `VTree.typemult := Σ henV + Σ leaf verdicts`, and its **threshold** is

```lean
VTree.thr (Tr) (n) := Tr.hfin.toFinset.sup
  (fun H => (shapeOfH H n).Nshape ⊔ siteLevel n (some H)) ⊔ 1
```

— the join over branches of an explicit shape threshold and a per-site band
level, joined with 1 (so always ≥ 1).  `shapeOfH`/`Nshape`/`siteLevel` are
explicit numerical functions of the node data (MovesT/Defs.lean).

### 3.2 The tree model tower and the fiber

A **tree model** `TreeModel p F n N m pol` (working level N, m = n·N digits,
`pol` a canonicity policy fixing representative choices) is an abstract
structure with `mem : Option (History) → Box p m → Prop` (is this state
realized on this digit class?) and `child : Option (History) → Node → Box p m
→ Prop`, subject to five structural laws (mem is child-generated, etc.).  The
concrete instance is **the canonical model** (`MovesD/TreeCan.lean`):

```lean
canTreeModel ... (dec : Box p m → Polynomial ℤ_[p]) : TreeModel ... where
  mem  := fun o x => match o with
    | none => True | some H => memCan n pol dec H x
  child := fun o ν x => match o with
    | none   => ∃ h : ν.species = root, memCan n pol dec (rootHist ν h) x
    | some H => ∃ hν : ν.species ≠ root, memCan n pol dec (H.snoc ν hν) x
```

where `memCan ... H x` unfolds to `ReadsOf p F n (dec x) H ∧ Realizable H ∧
pol.IsCanonPres H` — "H is a lawful, canonically-presented run of the OM read
machine on the exact polynomial dec x".  The decode is
`canDec p n N x := X^n + Σ_{i<n} C(canCoeff i)·X^i` with
`canCoeff i = Σ_{k<N} digit(i·N+k)·p^k` — the truncated integer polynomial the
digit class denotes.  The pinned instance is `bridgeTm p n N :=
canTreeModelN p n N (canPolicy p)` (the policy datum `canPolicy` is a designer
obligation still held by `sorry` at HEAD; everything downstream is parametric
in it).  The **chart** `bridgeChart n N hN : Fin n → Fin (n·N)`, b ↦ b·N, marks
the level-0 digit slot of each coefficient; `redPoly χ x` is the mod-p
reduction read through the chart.

The **fiber** of a tree V at model T and chart χ — "x's canonical OM tree is
exactly V" — is graph equality (`VTree.fiberAt`, MovesT/Defs.lean:518):

```lean
def VTree.fiberAt (Tr : VTree p F) (T : TreeModel ...) (χ ...) (x : Box p m) : Prop :=
  (∀ H, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)) ∧            -- (i)
  (∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →                           -- (ii)
    ((IrrHalts H ∧ ¬ Tr.nsLeaf H ∧ Tr.leafV H = some (irrVerdictOf H)) ∨
     (NsHalts T (some H) x ∧ ¬ IrrHalts H ∧ Tr.nsLeaf H ∧
       Tr.leafV H = some (nsVerdictOf H)))) ∧
  Tr.henV = henPayload χ x ∧                                            -- (iii)
  (∀ H ∈ Tr.chains, ¬ IsMaximalIn Tr.chains H →                         -- (iv)
    ¬ IrrHalts H ∧ ¬ NsHalts T (some H) x) ∧
  ((Tr.typemult.map fun ef => ef.1 * ef.2).sum = n) ∧                    -- (v)
  (Tr.heads.val.map Tr.trackDeg = ... multiplicities of the repeated
     factors of redPoly χ x ...)                                        -- (vi)
```

Gloss: (i) V's branches are all and only the realized pruned runs on x;
(ii) every maximal branch is a certified leaf on x, τ-irr or τ-ns matching V's
marking and verdict; (iii) V's Hensel payload equals the payload read off x's
reduction (one verdict (1, g) per *simple* degree-g irreducible factor of
redPoly); (iv) interior branches don't halt; (v) total degree n; (vi) the
per-track leaf degrees match the repeated factors of the reduction with
multiplicity.  `Realizes T χ V := ∃ x, V.fiberAt T χ x`.

### 3.3 The instance's carrier, mass, classifier, and assignment

(All landed, sorry-free modulo the `canPolicy` designer data; files
`MovesU/BridgeD3/D4/D6/D7/D12/D17.lean`.)

```lean
def bridgeTree (n p) (σ) : Type :=                          -- F.Tree σ
  {V : MovesT.VTree p (ZMod p) // V.typemult = σ.1 ∧ RealizedSelf n p V}
-- RealizedSelf: V is realized at its own level bridgeLvl n V := max (V.thr n) 1

noncomputable def bridgeMass ... (V : VTree ...) : ℝ≥0∞ :=  -- F.mass σ
  (Nat.card {x : MovesD.Box p (n * max (V.thr n) 1) //
      V.fiberAt (Tm (max (V.thr n) 1)) (chart _ _) x} : ℝ≥0∞)
    / (p : ℝ≥0∞) ^ (n * max (V.thr n) 1)

-- F.thr σ T := (T.val).thr n   (bridgeThr, ≥ 1 always)

noncomputable def bridgeCanonical ... : ∀ N, Box p n N → Option (SplittingType n) :=
  fun N f => if hN : 0 < N then
    (if h : ∃ σ (T : bridgeTree n p σ), bridgeThr .. T ≤ N ∧
         (T.val).fiberAt (Tm N) (chart N hN) (boxeq N f)
     then some h.choose else none) else none

-- treeOf σ N f := the fibering tree canonical_pin's ∃ produces (choice; D17)
```

So at the instance: **decided = fibered by some carried tree within threshold**
(the classifier IS the tree-fibering verdict — "Architecture B"), the mass of a
tree is its *normalized fiber count at its own threshold level*, and
`count_tie` becomes a statement purely about fiber counts of complete finite
OM trees at the canonical model across precisions N ≥ thr.

Well-definedness of the verdict and of `treeOf` is already proved: two trees
fibering the same digit point are equal (`MovesT.vtree_eq_of_fiberAt`,
MovesT/F3_dictSum.lean, Lean-core), so the σ emitted is unique
(`bridgeSigma_eq_of_fiberAt`, BridgeD6).

## 4. What is already proved around the obligation

* **The per-level mass identity `MovesT.treeN`** (E11_treeN.lean:42, PROVED):
  at one working level N, for a tree Tr with **no ns-marked leaf**
  (`hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H`), given an injective chart, a cell
  assignment with root-cell laws, a site ledger L and recursion scaffold, the
  sibling-independence counting kernel (SIB) and the multi-side junction kernel
  (JC-multi) as hypotheses (these are separate open obligations of the
  project),
  `Nat.card {x : Box p (n*N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L = p ^ (n*N)`
  where `AofTr Tr L = n + Σ_{H ∈ chains} L.siteExp H` (the tree's total
  equation count).  Its ∀-closure is `TreeNStmt` (Defs §2.10).
* **For ns-marked trees the identity is replaced by a limit** (`treeN_ns`,
  E12_treeNns.lean, per the source note: "for (ns)-leaf trees the identity is
  REPLACED by the normalized capped bound … p^{−nN}·count → 0").
* **Cross-level stability is a named OPEN row**: `MovesT.treeN_stable`
  (E11_treeN.lean:113, `sorry`) asserting `TreeNStable` — for N ≥ Tr.thr n and
  any tower level N′ ≥ N, membership of x in the fiber at level N′ depends
  only on the digits below n·N (in the level-major layout).  The one
  consolidated open kernel behind it is `MovesT.ReadLocality`
  (ReadLocality.lean:111): a chart pin (`chart lands in the level-1 block`)
  plus `child_local` — for every cutoff N ≥ Tr.thr n, tower levels M, M′ ≥ N,
  every site (o, ν), and boxes agreeing on the first n·N digits, child at M ↔
  child at M′.  Derived surfaces already proved conditional on it:
  `stableInputs_of_readLocality` (TV_B2), `transferRow_of_readLocality`
  (BridgeD5: realization and fiber transfer across levels ≥ thr, through a
  compiled layout dressing `blockInterleave` between the coefficient-major and
  level-major digit labelings).  `canonical_stable` at the instance is routed
  through that transfer row (BridgeD8).
* **A compiled probe** (BridgeN3b_readLocality.lean) shows the locality law is
  NOT derivable from the abstract `TreeModel` interface alone (an explicit
  five-law model reading a beyond-window digit), and that at HEAD the concrete
  `bridgeTm` has no defining equations to prove it from until `canPolicy`
  lands; the recorded discharge path is to prove it from the `canTreeModel`
  construction (§3.2), whose reads go through `dec x`.
* **Slice finiteness** (`bridge_slice_finite`, PROVED): only finitely many
  carried trees have threshold ≤ N.
* A designed-but-unexecuted discharge chain is on record (units "IB-D20/D21",
  BRIDGE_BP1_INSTANCE_2026-07-30.md §4: D20 = a typed pack of
  CellAssign/SiteLedger/TreeScaffold suppliers at the pinned models; D21 =
  `count_tie` from `MovesT.treeN` + the SIB/JC rows + D20; "off the default
  path").

## 5. What a proof must deliver

The `count_tie` field at the instance of §3.3, i.e. for every splitting type
σ, every carried tree T (typemult σ, self-realized) and every N ≥ thr(T):

  #{ f ∈ Box p n N : bridgeCanonical N f = some σ and treeOf σ N f = T }
    = bridgeMass(T) · p^{nN}
    = #(level-thr(T) fiber of T) · p^{n(N − thr T)}.

Acceptable forms of resolution, in the project's standing discipline: a full
informal-rigorous proof from the note-level inputs; a reduction to sharply
stated open lemmas strictly weaker than the row (each with owner-level
content identified); a faithfulness-audited literature identification; or a
demonstration that the row as typed cannot hold at the intended instance,
with the exact failure isolated and (if possible) a minimal repair.  Any
appeal to the hypothesis rows named in §4 (SIB, JC-multi, ReadLocality) must
cite them as hypotheses, not treat them as proved.
