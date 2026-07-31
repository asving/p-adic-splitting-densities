# M03-read-locality — problem brief

**Obligation.** The single "level-locality" kernel hypothesis of a Lean formalization
of a density theorem for splitting types of degree-n polynomials over ℚ_p. The
formalization models the Okutsu–Montes (OM) classification of a monic degree-n
polynomial over ℤ_p as a tree of "reads" (Newton-polygon side readings with residual
data), truncates polynomials to finite p-adic precision, and needs ONE statement
saying: the tree's child relation, evaluated at any working precision, depends only
on a bounded initial block of coefficient digits. Everything else in the relevant
proof section is formally derived from this one row. The row is carried as a named
hypothesis (a Lean `structure` of type `Prop`); the task is to prove it, refute it,
or reduce it, AT THE INTENDED INSTANCE described below.

This brief is self-contained: it unfolds every project-internal definition to
standard mathematical language and quotes the Lean forms. Reader background assumed:
p-adic fields, Newton polygons, MacLane/Okutsu–Montes theory.

---

## 1. The objects

### 1.1 Digit boxes and the decode

Fix a prime p and a degree n ≥ 1. For a "working level" (precision) M ≥ 1, a **box**
is a function

    x : {0, 1, …, n·M − 1} → 𝔽_p        (Lean: `Box p (n*M) := Fin (n*M) → ZMod p`).

Boxes encode the first M base-p digits of the n non-leading coefficients of a monic
degree-n polynomial. Two slot layouts occur; they differ by a fixed bijection and
both appear below:

* **standard (level-major)** layout: slot c carries digit ⌊c/n⌋ of coefficient
  (c mod n); the "level-<N block" is the first n·N slots;
* **coefficient-major** layout: slot i·M + k carries digit k of coefficient i.

The **decode** (coefficient-major; Lean `MovesD.canDec`, `canCoeff`) sends a box to
the monic integral polynomial

    f_x := X^n + Σ_{i<n} a_i X^i ∈ ℤ_p[X],   a_i := Σ_{k<M} x(i·M + k) · p^k,

where the digit values in 𝔽_p are lifted to {0,…,p−1}. So f_x ranges exactly over
monic degree-n polynomials whose coefficients are truncated at p^M.

### 1.2 Read histories: the corpus's OM run objects

The corpus formalizes an OM classifier run as a **history**: a nonempty finite list
of **nodes** H = [ν₀, …, ν_k], where the first node (and only the first) has species
`root`. A **node** ν (Lean `MovesC.Node`) is a record carrying one Newton-polygon
side reading:

* a **stage** σ (the current frame): a key polynomial Φ ∈ ℤ_p[X], a valuation w on
  key-coefficients, a residue field K ⊆ F (F a fixed finite field; in the pinned
  instance F = 𝔽_p), a residual-image map R into Laurent polynomials over K, and
  bookkeeping (previous-level data, digit maps `digPrime`, etc.);
* the read side: coprime pair (e, h) with e, h ≥ 1 (slope h/e in the corpus's
  orientation), its canonical Bézout pair (s, t) with 0 ≤ t < e, left slot s0 ∈ ℕ,
  slot width `wSide` with e ∣ wSide, total side weight γ ∈ ℤ, side height u* ∈ ℚ,
  a line (support line of the side), an anchor a ∈ ℤ with e·a = s0 − t·γ;
* residual data: a pattern pat : ℕ → K with **pat 0 ≠ 0 and pat(wSide/e) ≠ 0 (laws
  of the record)**, the anchored residual R_anch = Σ_{k ≤ wSide/e} pat(k)·z^k, an
  irreducible monic ψ ∈ K[z] of degree g ≥ 1 with ord_ψ(R_anch) = μ ≥ 1 exactly,
  a root z̄ ∈ F^× of ψ, a lift polynomial, a residue center, block width
  Dwidth = deg Φ, and species (root / increment / recentering).

Three Prop-level conditions on histories (all **box-free**, i.e. they mention no
box):

* **HistoryCoherent H**: the root frame's key has degree 1; per node, the line's
  slope satisfies slope · (e · STR_i · Dwidth) = h where STR_i is the product of
  the e's of the first i nodes ("stretch"); the γ-tie
  γ = e·(STR_i·u*) + (s0+wSide)·h; and per adjacent pair, the child frame is the
  recorded transition of the parent (key lift or recentering, Bézout pair carried,
  s0' + wSide' ≤ μ of the parent, slopes strictly increase).
* **Realizable H**: every appended read passes the three transition-admissibility
  conditions (non-adjacent vertex strictly above the extended line; at adjacent
  reads the pattern lead equals the transported vertex value; span-entry
  inequalities). Quantified over adjacent pairs — vacuous for one-node histories.
* **IsCanonPres pol H** (for a **policy** pol, i.e. a deterministic per-node lift
  rule ν ↦ liftOf(ν) that never reads the node's own lift field): every node's lift
  field equals pol.liftOf(ν), and every node's z̄ equals the canonical
  (enumeration-least) root of its ψ in F.

### 1.3 The run predicate ReadsOf (the box-dependent part)

For f ∈ ℤ_p[X] and a history H (Lean `MovesJ.ReadsOf p F n f H`, HC2/Defs.lean:285):

    ReadsOf n f H  :=  f monic ∧ deg f = n ∧ HistoryCoherent H ∧
      for every read i < len H, there exist B : ℕ → ℤ_p[X], Nd, Φnext such that
        (a) IsDevelopment Φ_i f B Nd   — the Φ_i-adic development: deg B_j < deg Φ_i,
            B_j = 0 for j ≥ Nd, f = Σ_{j<Nd} B_j Φ_i^j  (Φ_i := the i-th node's key);
        (b) Φnext = the (i+1)-st node's key, whenever i+1 < len H;
        (c) SideReads ν_i B Nd Φnext, the per-read clause bundle:
            (i)  SIDE: for every j < Nd with B_j ≠ 0:  γ ≤ e·w(B_j) + j·h, with
                 equality ONLY at recorded stride slots j = s0 + e·k, k ≤ wSide/e,
                 pat k ≠ 0;
            (ii) DIGITS: at every stride slot with pat k ≠ 0:  B_{s0+e·k} ≠ 0,
                 e·w(B_{s0+e·k}) + (s0+e·k)·h = γ (exact valuation pin), and its
                 stage-residual is the monomial unit with scalar pat k at the forced
                 position;
            (iii) ANCHOR/ORDER: the recorded (a, R_anch) anchor the stage residual of
                 f's development sum, and ord_ψ(R_anch) = μ;
            (iv) LANDING: `LandingKey ν_i Φnext` — Φnext is the recorded read's
                 produced key (standard lift of (ψ, g) at the read's index, or the
                 recentered key);
            (v)  LIFT NORMALIZATION: ν_i.lift = polOM.liftOf ν_i (polOM = the
                 corpus's canonical policy realizer) and z̄ = the canonical root;
            (vi) VERTEX READ-OFF: for every development Bh of f in Φnext,
                 digPrime z̄ (Bh μ) equals the recorded transported vertex value.

Standard-math gloss: "H is a genuine OM run on f" — each recorded node's side is an
actual lower-Newton-polygon side of f's development in the current key with the
recorded slope, exact valuations, residual pattern, and normalized lifts.

### 1.4 The canonical tree model

For a policy pol and a decode dec (instantiated as dec = f_• above), the corpus
defines (Lean `MovesD.canTreeModel`, MovesD/TreeCan.lean — all structural laws
PROVED):

    memCan H x        := ReadsOf n (dec x) H ∧ Realizable H ∧ IsCanonPres pol H
    mem (none) x      := True                       (the root/empty chain)
    mem (some H) x    := memCan H x
    child (none)  ν x := ∃ (h : ν.species = root),  memCan [ν] x
    child (some H) ν x := ∃ (h : ν.species ≠ root), memCan (H ++ [ν]) x

`canTreeModelN p n M pol` is this model at working level m = n·M with dec = f_•
(coefficient-major). The **bridge instance** pins pol := `canPolicy p` (the intended
canonical lift policy; in Lean currently an opaque named obligation) and dresses the
model to the standard layout through the compiled slot bijection `blockInterleave`
(Lean `bridgeTmStd p n M`, MovesU/BridgeD5_transferRow.lean:147). The dressed chart
is `bridgeChartStd n M : b ↦ slot b` — coefficient b's digit-0 slot in the standard
layout.

Note the model is a **type-level interface** (Lean `MovesD.TreeModel`): any pair
(mem, child) satisfying five structural laws is a TreeModel. The obligation below is
stated over an abstract tower of TreeModels; its intended (and only planned)
instantiation is the canonical model just described.

### 1.5 Finite pruned trees and the threshold

A **VTree** (Lean `MovesT.VTree`) is a complete finite pruned classification tree:
a finite, prefix-closed set `chains` of histories (all nonempty as node-lists), a
multiset `henV` of verdicts for the level-0 unrepeated ("Hensel") factors, a leaf
verdict function `leafV` defined exactly on the maximal chains, and a marked subset
`nsLeaf` of leaves. (The set of chains may be empty; all fields then take their
trivial values.)

Its **threshold** (Lean `VTree.thr`, MovesT/Defs.lean:734):

    thr(Tr, n) := max(1, max_{H ∈ chains} max( Nshape(H), siteLevel(H) ))

where Nshape(H) := 1 + max over H's reads of ⌈intercept of the read's side line⌉
(an a-priori bound on the digit levels the shape constrains) and siteLevel(H) is the
analogous per-site band level. For the empty tree, thr = 1.

---

## 2. THE STATEMENT (the kernel row)

Lean source: `lean/LeanUrat/MovesT/ReadLocality.lean` (structure
`LeanUrat.MovesT.ReadLocality`). Parameters: p prime, F finite field, n, a policy
pol, a base level N₀, a **tower** of models and charts

    Tat : ∀ M ≥ N₀, TreeModel p F n M (n·M) pol       (one model per working level)
    χat : ∀ M ≥ N₀, ({0,…,n−1} → {0,…,n·M−1})          (per-level chart)

and a VTree Tr. The row asserts two fields. On-disk form (2026-07-31):

```lean
structure ReadLocality {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N' (h' : N₀ ≤ N'), Fin n → Fin (n * N'))
    (Tr : VTree p F) : Prop where
  chart_pin : ∀ (N' : ℕ) (h' : N₀ ≤ N') (b : Fin n), ((χat N' h' b : ℕ)) < n
  child_local : ∀ (N : ℕ), Tr.thr n ≤ N →
    ∀ (M : ℕ) (hM : N₀ ≤ M) (M' : ℕ) (hM' : N₀ ≤ M')
      (hNM : N ≤ M) (hNM' : N ≤ M')
      (o : Option (History p F)) (ν : Node p F)
      (x : Box p (n * M)) (x' : Box p (n * M')),
      (∀ c : Fin (n * N),
        x (Fin.castLE (Nat.mul_le_mul_left n hNM) c)
          = x' (Fin.castLE (Nat.mul_le_mul_left n hNM') c)) →
      ((Tat M hM).child o ν x ↔ (Tat M' hM').child o ν x')
```

**Corrected form (the statement to attack).** A ratification audit (2026-07-31,
"audit 1b") mandated two statement repairs, queued as sign-off item 7 and being
applied concurrently:

1. `chart_pin` becomes the exact digit-slot pin rather than the block bound: the
   chart at every level reads exactly coefficient b's digit-0 slot — in the standard
   layout, `(χat N' h' b : ℕ) = b`. (At the intended instance the chart is defined
   as that map, so this face is definitionally true there; the compiled gate is
   `bridgeChartStd_pin`.)
2. `child_local` gains the below-base guard `N₀ ≤ N` on the cutoff level N (all
   other quantifiers unchanged).

In standard language, the corrected `child_local` says:

> For every cutoff N with max(thr(Tr,n), N₀) ≤ N, all working levels M, M' ≥ N (both
> ≥ N₀, no order between them), **every** site (o, ν) — o an arbitrary history or
> the root, ν an arbitrary node — and all boxes x (level M), x' (level M') that
> agree on the level-<N block (the first n·N standard slots, i.e. digits 0…N−1 of
> every coefficient): ν is a child of o at x in the level-M model if and only if ν
> is a child of o at x' in the level-M' model.

The intended target instance is the ∀-closure over trees at the dressed bridge tower
(Lean `MovesU.BridgeReadLocality`, BridgeD5_transferRow.lean:179):

```lean
def BridgeReadLocality (n p : ℕ) [Fact p.Prime] : Prop :=
  ∀ V : MovesT.VTree p (ZMod p),
    MovesT.ReadLocality (N₀ := 1)
      (fun N' (_ : 1 ≤ N') => bridgeTmStd p n N')
      (fun N' (h : 1 ≤ N') => bridgeChartStd n N' h) V
```

i.e. N₀ = 1, F = 𝔽_p, models = the canonical run-extension models of §1.4 at the
pinned policy, charts = b ↦ slot b, quantified over ALL VTrees.

### The informal source claim

The row transcribes the working note's finite-level stability theorem ("TREE-N",
note lines 7559–7574): *"let T be complete finite realizable with all leaves
(τ-irr)/(τ-hen) … for every N ≥ thr(T): #{f mod p^N : T_can^τ(f) = T} = p^{nN} ·
μ(fiber T) — the fiber is a FINITE intersection of finite-level digit-cell
conditions … an exact union of level-N residue classes,"* with declared proof
inputs *"per site: the joint cell's literal system at its B(iii) level; per branch:
D4R.4's exact level-N realization; per leaf: TB-CAP's level-N_V cylinders."*

---

## 3. What is already proved / recorded around the row

* **Derived surfaces (proved conditional on the row).** `StableInputs` (fixed-level
  cylinder transfer; MovesT/TV_B2.lean, `stableInputs_of_readLocality`) and
  `TransferRow` (cross-level realization/fiber transfer at the bridge;
  MovesU/BridgeD5_transferRow.lean, `transferRow_of_readLocality`) are both formally
  derived from the row. The fiber-level stability statement `TreeNStable`
  (MovesT/Defs.lean:1624: for N ≥ thr(Tr), the tree fiber
  {x : Tr.fiberAt (Tat N') x} is invariant under changing x outside the level-<N
  block) is the note-faithful consumer, reached from the row through a proved
  transfer chain; the open theorem `treeN_stable` (MovesT/E11_treeN.lean, honest
  `sorry`) carries it.
* **The model side is constructed.** The canonical model's five structural laws,
  the decode's degree/monicity/reduction laws, and the membership prefix law are
  all proved (MovesD/TreeCan.lean). Only the policy value `canPolicy` (and its pin)
  remains an opaque named obligation.
* **Compiled facts from a prior probe** (MovesU/BridgeN3b_readLocality.lean, all
  Lean-core, no sorries):
  - `child_locality_not_interface_derivable`: the child-locality face is NOT a
    consequence of the five TreeModel interface laws alone (explicit interface
    countermodel at (n, N, N') = (2, 1, 2) whose child reads a beyond-window slot).
    So any proof must use the canonical model's defining equations.
  - The RAW coefficient-major bridge chart violates the old level-major
    `chart_pin` (`bridgeChart_levelMajor_chart_pin_false`), and equals the digit-0
    slot map (`bridgeChart_eq_digitIdx0`) — the source of the corrected chart face.
    The DRESSED chart satisfies both forms (`bridgeChartStd_pin`, compiled).
* **Non-vacuity witnesses in-corpus**: a full run witness (history + polynomial
  with `ReadsOf` proved) exists at an n = 2 inert node (HC2 unit `U31`,
  `gate_readsOf_inert2`); a ramified stage (e = 2 increment transition) is
  constructed in MovesD/R7_ramifiedForge.lean.
* **Ownership/status**: the row is the corpus's ONE named open locality hypothesis
  (owner tag HC-2/D4R0K); it has never been proved nor refuted in-corpus.

---

## 4. What a resolution must deliver

One of:

1. **Proof** of the corrected row at the intended instance (§1.4's canonical models,
   any policy, N₀ = 1, arbitrary VTree) — informal-rigorous mathematics is the
   deliverable; Lean transcription happens later. Partial credit: a proof for a
   restricted class of sites/trees with the restriction stated exactly.
2. **Refutation**: an explicit instance (tree, cutoff, levels, site, box pair)
   violating a face at the intended instance, with every claimed property of the
   witness justified from the definitions above.
3. **Reduction**: an equivalent or sufficient reformulation in cleaner standard
   mathematics (e.g. a precise statement about OM data of p-adically close
   polynomials), with both directions of the reduction argued.
4. **Literature identification**: a published statement matching the row (exact
   source, theorem number, hypotheses), with a faithfulness comparison — does the
   row claim MORE than the citation?

Any answer should treat the two faces (`chart_pin`, `child_local`) separately, and
should state explicitly at which instance (abstract tower vs canonical model vs
dressed bridge) it operates.
