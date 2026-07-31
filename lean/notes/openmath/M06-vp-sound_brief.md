# M06-vp-sound — Problem brief: soundness of the classifier's verdict (VP + VP-SOUND) at the pinned canonical-tree instance

**Target obligation:** the hypothesis row `BK.vp_sound` of the capstone kernel
ledger — `vp_sound : VPSound X` at
`lean/LeanUrat/MovesU/BridgeKernels.lean:235`, with the predicate `VPSound`
defined at `lean/LeanUrat/MovesU/Defs.lean:72`. There is no `sorry` token:
this is a named hypothesis row of the capstone theorem chain, to be either
proved at the pinned instance or supported by a faithfulness-audited
literature citation. Date: 2026-07-31.

This brief is self-contained. It re-expands every project-internal name; the
reader is assumed to know p-adic fields, Newton polygons, MacLane–Okutsu–Montes
(OM) theory and Hensel's lemma, but nothing about this repository.

---

## 1. Role in the project

The project formalizes a uniformity theorem: for each degree n and each
splitting type σ (a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n, entries
≥ 1), the natural density of monic degree-n polynomials over ℤ_p whose
factorization over ℚ_p has type σ — meaning the multiset of (ramification
index, residue degree) of the irreducible factors is σ — equals R_σ(p) for one
fixed rational function R_σ(q) ∈ ℚ(q), uniformly in p.

The formal proof runs a *classifier*: a deterministic procedure that reads a
polynomial's coefficients modulo p^N (for growing N) and, when it can certify
the factorization type from that finite datum, outputs a verdict σ; otherwise
it stays silent ("undecided"). The density of the decided-σ locus is computed
by tree-fiber counting and shown to converge to R_σ(p); the undecided locus is
shown (separately) to have vanishing density. To conclude that R_σ(p) is the
density of the *true* type-σ locus — not merely of the classifier's σ-verdict
locus — the chain needs exactly one soundness statement: **whenever the
classifier decides σ, the true type is σ**. That statement is this obligation.
The squeeze that consumes it is already proved
(`LeanUrat.MovesU.identification`, `lean/LeanUrat/MovesU/U11_identification.lean`):
from `VPSound X`, verdict-density → r, and undecided-density → 0, it derives
true-type-density → r by a two-sided counting sandwich. So the entire
"the computed density is the density of the actual splitting behaviour" leg
of the capstone rests on this one row.

---

## 2. The Lean statement (normative form)

### 2.1 The vocabulary it is typed in

Fix a prime p and a degree n ≥ 1. All Lean quotes are from
`lean/LeanUrat/MovesU/Defs.lean` unless marked otherwise.

```lean
def SplittingType (n : ℕ) : Type :=
  {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n}

abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

noncomputable def Box.toPoly {p n N : ℕ} (f : Box p n N) :
    Polynomial (ZMod (p ^ N)) :=
  X ^ n + ∑ i : Fin n, C (f i) * X ^ (i : ℕ)
```

In standard language: a *splitting type* is a multiset of pairs (e, f) of
positive integers with Σ e·f = n. The *level-N box* is the set of coefficient
tuples (a_0, …, a_{n−1}) ∈ (ℤ/p^N)^n, denoting the monic polynomial
x^n + a_{n−1}x^{n−1} + … + a_0 over ℤ/p^N; it carries `boxProj` (reduction
Box p n N' → Box p n N for N ≤ N', coefficientwise ℤ/p^{N'} → ℤ/p^N).

The classifier interface (`ClassifierSpec`, Defs.lean:62):

```lean
structure ClassifierSpec (n p : ℕ) where
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  trueType : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ
  baseSection : BaseSection
```

`canonical N f` is the classifier's verdict on the level-N class f (`none` =
undecided); `trueType N f` is the class's true-factorization-type field
(`none` = the type is not determined by the class); `canonical_stable` says a
verdict, once issued, persists under refinement of the class; `baseSection`
is a bookkeeping pin (the digit-section convention, fixed to Teichmüller at
the instance).

### 2.2 The row itself

```lean
-- Defs.lean:72
def VPSound {n p : ℕ} (X : ClassifierSpec n p) : Prop :=
  ∀ N (f : Box p n N) σ, X.canonical N f = some σ → X.trueType N f = some σ

-- BridgeKernels.lean:206/235 (row of the structure BridgeKernels, binders
-- (n C KC K7 p hp X F seam Tpin) as in the file)
  vp_sound : VPSound X
```

As a field of `BridgeKernels` the row is parametric in X. Parametrically it
is of course not provable (nothing ties `trueType` to `canonical` for an
arbitrary X); the obligation is its **discharge at the pinned instance**: the
final wiring (`lean/LeanUrat/MovesU/BridgeMk.lean`, "INTENDED FINAL WIRING")
instantiates

```
X := bridgeClassifierSpec n p (bridgeCanonical n p boxEquivD)
       (canonical_stable from IB-D8) (bridgeZfType)
```

so the actual mathematical statement is `VPSound` at the two concrete maps
described in §3 and §4 below.

---

## 3. The instance's true-type map (what `some σ` must mean)

`bridgeTrueType` (`lean/LeanUrat/MovesU/BridgeD9a_trueTypeDef.lean`) is defined
through the reading predicate `ZpReads`
(`lean/LeanUrat/MovesU/DefsLedger.lean:686`):

```lean
def ZpReads (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ)
    (f : Box p n N) (σ : SplittingType n) : Prop :=
  ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    g.map (PadicInt.toZModPow N) = f.toPoly → zf g = σ.1

noncomputable def bridgeTrueType (n p : ℕ) [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ) (f : Box p n N) :
    Option (SplittingType n) :=
  if h : ∃ σ, ZpReads n p zf N f σ then some h.choose else none
```

Here `zf` is instantiated at the ℤ_p-bridge's reading `zfType`, constrained by
the bridge law `ZpBridge.zf_factor` (DefsLedger.lean:721–731) to be **the true
factorization-type reading**: for monic g of degree n, `zfType g` is the
multiset of pairs (ramification index, residue degree) attached to the monic
irreducible-over-ℚ_p factors of g (project defs `MovesT.ramIdx`/`MovesT.resDeg`
read `Ideal.ramificationIdx`/`Ideal.inertiaDeg` of the maximal ideals through
`AdjoinRoot h`, `lean/LeanUrat/MovesT/Defs.lean:1107/1116`).

So, in standard language:

> **trueType N f = some σ** iff **every** monic degree-n polynomial
> g ∈ ℤ_p[x] whose coefficientwise reduction mod p^N is f has ℚ_p-factorization
> type σ (multiset of (e, f) over its irreducible factors).

Uniqueness of such σ (given that lifts exist, which they do for every class) is
already proved: `zpReads_unique_of_lift`
(`lean/LeanUrat/MovesU/BridgeD10_trueTypeLevel0.lean`). Consequently the row's
content at the instance is exactly:

> **(VP-SOUND at the instance.)** For every N, every level-N class f, and
> every splitting type σ: if `bridgeCanonical` decides σ on f at level N, then
> every monic degree-n lift g ∈ ℤ_p[x] of f has ℚ_p-factorization type σ.

---

## 4. The instance's classifier (what "decides σ" means)

`bridgeCanonical` (`lean/LeanUrat/MovesU/BridgeD7_canonical.lean`) is the
"tree-fibering verdict":

```lean
canonical N f := if hN : 0 < N then
  (if h : ∃ (σ : SplittingType n) (T : bridgeTree n p σ),
       bridgeThr n p σ T ≤ N ∧
       (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN)
         (boxeq N f)
   then some h.choose else none) else none
```

with the both-direction unfolding `bridgeCanonical_pin` already proved (same
file): `canonical N f = some σ` iff some carried σ-tree with threshold ≤ N
fibers at f's digit image. The ingredients:

* **The carried trees** (`bridgeTree`,
  `lean/LeanUrat/MovesU/BridgeD3_treeCarrier.lean:94`):
  `bridgeTree n p σ := {V : MovesT.VTree p (ZMod p) // V.typemult = σ.1 ∧
  RealizedSelf n p V}` — finite classification trees of verdict-type σ that
  are realized by at least one box point at their own working level.
  A `MovesT.VTree` (`lean/LeanUrat/MovesT/Defs.lean:487`) is a finite,
  prefix-closed set of "histories" (chains of Newton-polygon window reads:
  each node carries a side slope h/e, a residual-factor degree g, a
  multiplicity μ, recentering data, …), together with: a Hensel payload
  `henV` (one verdict {(1, g)} per simple degree-g irreducible factor of the
  mod-p reduction), a leaf-verdict assignment `leafV`, and a marked subset
  `nsLeaf` of leaves. `typemult` is the multiset union of all leaf verdicts
  plus the Hensel payload.

* **The leaf/halting semantics** (`lean/LeanUrat/MovesT/Defs.lean:179–241`),
  the project's three halting rules:
  - **(τ-hen)**: a simple (multiplicity-1) irreducible factor ψ of the mod-p
    reduction halts immediately with verdict {(1, deg ψ)} — carried in `henV`.
  - **(τ-irr)** `IrrHalts H`: a chain halts when its accumulated invariants
    saturate — accE(H)·accF(H) = (cluster degree at the last read), where
    accE = ∏ e_r and accF = ∏ g_r over the chain's reads (equivalently, the
    last read has residual multiplicity μ = 1). Verdict {(accE, accF)}. This
    is a function of the chain data alone.
  - **(τ-ns)** `NsHalts T (some H) x`: the chain's state is realized at the
    box point x and **no child read of that state is realized at x** — the
    "no side / empty Newton window" configuration (the cluster factor is
    exactly a key power Φ̂^μ as far as x can see). Verdict μ·{(E(Φ̂), F(Φ̂))}
    (μ copies of the key's accumulated pair), via `nsVerdictOf`. This is a
    function of the chain data **and of the level-N model at x**.

* **The fiber predicate** (`VTree.fiberAt`, `lean/LeanUrat/MovesT/Defs.lean:518`)
  says "the canonical τ-pruned classification tree of x is exactly Tr", six
  clauses: (i) Tr's chains are exactly the realized τ-pruned histories of x;
  (ii) every maximal chain halts, either (τ-irr) with the matching verdict and
  `¬ nsLeaf`, or (τ-ns) at x with the matching verdict and `nsLeaf`; (iii)
  Tr's Hensel payload equals x's (simple factors of the reduction); (iv)
  non-maximal chains do not halt; (v) Σ over `typemult` of e·f equals n; (vi)
  the per-track leaf-degree totals match the repeated-factor degrees of x's
  reduction. **Note that clause (ii) admits (τ-ns) leaves.**

* **The model and threshold**: `bridgeTm p n N`
  (`lean/LeanUrat/MovesU/BridgeD1_treeModelWire.lean:80`) is the level-N tree
  model — the OM engine's realized-state (`mem`) and realized-child (`child`)
  relations over the level-N box, built from the canonical digit-lift policy
  `MovesD.canPolicy` (Teichmüller-pinned). At HEAD the policy pair
  `canPolicy`/`canPolicy_pin` is a named designer obligation (data `sorry`,
  `lean/LeanUrat/MovesD/TreeCan.lean:485/492`): the run-extension semantics is
  fixed by the landed structure but the policy data is not final, so proofs
  about the instance either consume the pinned laws (`OffsetPPin`,
  `TreeModel`'s five structural laws — all landed) or must state any further
  model law they need as an explicit hypothesis. `bridgeThr σ T = T.thr n`
  (`VTree.thr`, MovesT/Defs.lean:734) is the tree's detection threshold: the
  max over its chains of the shape-computed read levels (a finite number
  computed from the tree's slopes/heights alone). `bridgeChart`/`boxEquivD`
  are coefficient-digit charts (bijections between the level-N box and the
  digit cube (ℤ/p)^{nN}); they carry no mathematical content beyond
  reindexing.

In fully standard language, the discharge target is:

> **Theorem (target).** Fix p, n, N ≥ 1 and a monic-coefficient class
> f ∈ (ℤ/p^N)^n. Suppose there is a splitting type σ and a finite canonical
> OM classification tree T of verdict-type σ — complete (all maximal branches
> halted by one of the three rules above, verdicts recorded), self-realizable,
> with detection threshold thr(T) ≤ N — such that the level-N OM run on f
> realizes exactly T (fiber clauses (i)–(vi)). Then **every** monic
> g ∈ ℤ_p[x] of degree n with g ≡ f (mod p^N) factors over ℚ_p with
> splitting type exactly σ.

---

## 5. What is already proved around it (corpus state at HEAD)

* **The consumer**: `identification` (U11) is fully proved from `VPSound X` +
  convergence hypotheses; nothing else consumes the row
  (`cl10_vpsound` in `DefsLedger.lean:791` is fed verbatim from `BK.vp_sound`
  by the proved assembly `bridgeCapstoneLedger`, BridgeMk.lean).
* **The classifier unfolding**: `bridgeCanonical_pin` (both directions) is
  proved, as are the verdict-type uniqueness inputs it uses
  (`bridgeSigma_eq_of_fiberAt`, BridgeD6).
* **The true-type unfolding**: `zpReads_forall_lift` (definitional),
  `zpReads_unique_of_lift` (one lift forces uniqueness of the read type), and
  the level-0 edge facts are proved (BridgeD10). Lifts exist at every level
  (`ZpBridge.lift_exists` is a bridge law; coefficientwise lifting is
  elementary).
* **Level stability**: `canonical_stable` at the instance is supplied by the
  transfer row (IB-D8 from IB-D5), itself reduced to the one open locality
  kernel (`MovesT.ReadLocality`, a separate census obligation, M03).
* **The mathematical note behind the row** (the project's frozen prose
  authority, `lean/notes/MOVES_2026-07-24.md` §T.1–T.2): the verdict-pin
  clauses (c1) (typing), (c2) (exactly-one-verdict), (c3-a) (partition) are
  discharged there; the finite-cap detection duty TB-CAP is **proved for
  (τ-hen)** (cap N = 1), **proved for (τ-irr)** conditional on the project's
  accepted Newton-polygon perimeter (the verdict class of a saturated branch
  is an exact finite union of level-N(η) residue classes, N(η) computed from
  shape/height data), and **refuted for (τ-ns) as literally stated** — the
  (τ-ns) class at a cell is a strictly decreasing intersection of cylinders
  (a pro-cylinder), not a finite union of level-N cylinders at any finite N;
  the note's amendment ((ns-lump)/(ns-null)) proves the (τ-ns) class has
  conditional measure zero. The note's partition display (§SQ.1, (NS-ROUTE))
  routes accordingly: decided-side trees are those with **every leaf
  (τ-irr)/(τ-hen)**, and "(NS-d): ns-leaf fibers lie in Undec(N) at EVERY N",
  accounted on the envelope side. The note declares VP-SOUND itself a
  citation obligation with two precisely displayed statements, (HEN-LIFT)
  (coprime Hensel lift of a simple reduction factor: unique monic lift,
  irreducible, unramified, (E,F) = (1, deg ψ)) and (OM-SAT) (a saturated
  (μ = 1) branch's certified cluster factor is irreducible with e = accE,
  f = accF — Ore/Montes certificate soundness).
* **Interface docstring** (Defs.lean:51–61): describes the intended verdict
  semantics as "`some σ` = complete finite realizable tree, all leaves
  (τ-irr)/(τ-hen), certified at level N (thr ≤ N)".
* **Supporting proved kernels**: the carry-algebra no-cancellation and
  level-detection spine used by finite-level determinacy arguments is proved
  in Lean (`CL12_ncl`, `CL13_lvlDet`, `lean/LeanUrat/HC1/`), with the
  countermodel probe for the no-cancellation universal closed BLOCKED
  (quarantined at `lean/quarantine/HC1_CL10_nclProbe_2026-07-31.lean.txt`).
* **External citation infrastructure**: the OM-theory import of the project is
  pinned verbatim to Guàrdia–Montes–Nart, *Newton polygons of higher order in
  algebraic number theory* (Trans. AMS 364 (2012), 361–416; arXiv:0807.2620v2)
  in `docs/GMN_citations.md`, including the order-r leaf dichotomy
  (Cor 3.8: a multiplicity-1 residual factor certifies an irreducible factor
  with e = e_1⋯e_r, f = f_0⋯f_r) and the f-complete-type notion (Def 3.9).
  One GMN axiom (theorem of the index) is already declared under the axiom
  policy; new literature axioms require a faithfulness entry
  (`docs/AXIOM_FAITHFULNESS.md`).

---

## 6. What a proof must deliver

Either:

1. **A discharge**: a proof of the target theorem of §4 covering *all three*
   leaf clauses as built (τ-hen, τ-irr, and τ-ns leaves are all admitted by
   the as-built `fiberAt`), for all N, f, σ — stated so that it can be
   consumed at `X := bridgeClassifierSpec …` with the designer-data caveat of
   §4 made explicit (any model law used beyond the landed structural laws must
   be displayed as a named hypothesis); **or**
2. **A precise reduction**: named lemmas (with exact statements) from which
   the discharge follows, each classified as project-provable or
   literature-citable, with exact citations (source, theorem number,
   hypotheses) and a faithfulness analysis — does the Lean row state *more*
   than the citation? — for every citation leg; **or**
3. **A refutation**: a concrete (N, f, σ, T) meeting the classifier's firing
   conditions at the instance together with two monic lifts of f of different
   ℚ_p-factorization types, with the failing clause identified — and the
   consequent adjudication need stated.

Any outcome must respect the statement fence: the row's type (`VPSound X`)
and the instance definitions may not be weakened to make the goal provable;
repairs to definitions are adjudication events, not prover moves.
