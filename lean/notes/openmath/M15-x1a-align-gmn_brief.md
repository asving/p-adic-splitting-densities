# M15-x1a-align-gmn — problem brief: the certified-increment alignment row `KT.cl15_align`

Neutral, self-contained problem brief. Audience: a mathematician fluent in p-adic
fields, Newton polygons, Okutsu–Montes/MacLane theory, and Igusa-style density
computations, with NO knowledge of this project's internal names. Every internal
name used below is re-expanded. This file states the problem and the surrounding
corpus facts only; it contains no proof attempts and no approach advice.

## 1. Where the obligation sits

The repository formalizes (in Lean 4) a uniformity theorem: for each "splitting
type" σ of degree n (the multiset of (ramification index, residue degree) pairs of
the ℚ_p-irreducible factors), there is ONE rational function R_σ ∈ ℚ(q) such that
for every prime p (satisfying an explicit regularity predicate) the density of
monic degree-n polynomials over ℤ_p with splitting type σ exists and equals
R_σ(p). The capstone Lean theorem (`theoremU`, file
`lean/LeanUrat/MovesU/U10_theoremU.lean`) is CONDITIONAL on a ledger of typed
hypothesis rows. This brief concerns exactly one row of that ledger:

```lean
-- lean/LeanUrat/MovesU/DefsLedger.lean, field of `structure UpstreamTyped`
cl15_align : MovesX.X1aAlignP n KC.XF ⟨true, false⟩
```

Here `KC.XF : MovesX.XFamily n` is a bundled per-prime family of data carried as a
parameter (defined below). In the capstone's signature the ledger is bound as
`KT : UpstreamTyped n KC`, so the row is referred to as `KT.cl15_align`.

## 2. The normative Lean statement, verbatim

All of the following is from `lean/LeanUrat/MovesX/Defs.lean` (namespace
`LeanUrat.MovesX`), which is sorry-free and axiom-free.

```lean
def X1aAlignP (n : ℕ) (X : XFamily n) (st : AlignState) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → dCert st H ≤ (X.gmn p).ind f
```

The obligation is this proposition at the state `st = ⟨true, false⟩`.

Supporting definitions, verbatim:

```lean
structure XNode (n : ℕ) where
  e : ℕ
  ell : ℕ
  h : ℕ
  s0 : ℕ
  u0 : ℕ
  sel : Option (ℕ × ℕ)
  isIncrement : Bool
  epos : 1 ≤ e
  hpos : 1 ≤ h
  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false

abbrev XHistory (n : ℕ) := List (XNode n)

def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

inductive Row | T1 | T2 | T3 | T4 | T5

def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3) else .T4

structure AlignState where
  inc : Bool
  recn : Bool

def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing && match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.recn)
    | .T2 => st.inc
    | _   => false

def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length

def MonicBox (n p : ℕ) [Fact p.Prime] : Type :=
  { f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n }

def discZero (n p : ℕ) [Fact p.Prime] : Set (MonicBox n p) := { f | f.1.discr = 0 }

noncomputable def vdisc {n p : ℕ} [Fact p.Prime] (f : MonicBox n p) : ℕ :=
  (f.1.discr).valuation

structure GMNIndex (n p : ℕ) [Fact p.Prime] where
  ind : MonicBox n p → ℕ
  inStratum : MonicBox n p → XHistory n → Prop
  p2 : ∀ f, f ∉ discZero n p → 2 * ind f ≤ vdisc f

structure XFamily (n : ℕ) where
  ctx : ∀ (p : ℕ) [Fact p.Prime], XCtx n p
  gmn : ∀ (p : ℕ) [Fact p.Prime], GMNIndex n p
  gmnLink :
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (ctx p).Branch f),
      (gmn p).inStratum f ((ctx p).hist b)
```

(`XCtx` is a large per-prime context bundling an abstract classification tree —
per-polynomial branch types with histories, roots, parents, finite children menus
— together with a finitely-additive normalized content `frac` on subsets of the
monic box. Its only role in this row is via `gmnLink`; the row itself never
mentions `ctx`. `Polynomial.discr` is mathlib's discriminant;
`PadicInt.valuation : ℤ_[p] → ℕ` is the p-adic valuation, with junk value 0 at 0,
which is why every statement carries the guard `f ∉ discZero`.)

Also relevant context (not hypotheses of the row): histories that arise from
branches of the `XCtx` tree satisfy a well-formedness predicate

```lean
structure HistWF (n : ℕ) (H : XHistory n) : Prop where
  termLast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true
  degProd  : ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod ≤ n
```

but `X1aAlignP` as stated does NOT assume `HistWF H` — it quantifies over every
`H` satisfying `inStratum f H`.

## 3. Translation to standard mathematics

**The carrier.** `MonicBox n p` = monic degree-n polynomials over ℤ_p;
`vdisc f` = v_p(disc f); the guard `f ∉ discZero` says disc f ≠ 0, i.e. (monic,
characteristic 0) f is separable over ℚ_p.

**Nodes and histories.** An `XNode` abstracts ONE refinement step of an
Okutsu–Montes / higher-order-Newton-polygon factorization procedure, recorded in
the engine's own ("raw", per-step frame) coordinates:

- (e, h) coprime, e, h ≥ 1: the step read a Newton-polygon side of slope −h/e
  (in the step's own coordinate frame);
- ℓ ≥ 1: the lattice length of that side — the side has horizontal length e·ℓ,
  height h·ℓ, and residual polynomial of degree ℓ;
- (s₀, u₀): the initial (left) endpoint of the side, so the side runs from
  (s₀, u₀ + hℓ) down to (s₀ + eℓ, u₀);
- `sel = some (g, μ)`: the step selected an irreducible factor of degree g with
  multiplicity μ of the degree-ℓ residual polynomial of the side and continues
  refining along it (the constraint μ·g ≤ ℓ); `sel = none`: terminal step;
- `isIncrement`: whether the step strictly increased the degree of the current
  key (approximating) polynomial — a "genuine increment", as opposed to a
  same-degree re-centering/refinement step. The coherence laws force: at
  ℓ = 1 with e ≥ 2 the step is an increment (`t2inc`, `t3inc`); at ℓ = 1 with
  e = 1 it is a re-centering (`t4rec`). At ℓ ≥ 2 both kinds occur.

A history `H` is the finite list of such node records along one root-to-leaf
path ("branch") of the classification tree of a fixed f.

**Rows.** Continuing nodes are classified: T1 (ℓ ≥ 2), T2 (ℓ = 1, e ≥ 2, h ≥ 2),
T3 (ℓ = 1, e ≥ 2, h = 1), T4 (ℓ = 1, e = 1); T5 = terminal. `certified ⟨true,
false⟩` is exactly: continuing AND ((row T1 AND isIncrement) OR row T2). Since
continuing T2 nodes are forced increments by `t2inc`, the certified population at
this state is precisely the T1/T2 INCREMENT nodes — the corpus calls
`⟨true, false⟩` the "certified-increment state". `dCert ⟨true, false⟩ H` is the
number of such nodes in H.

**The interface data.** `GMNIndex n p` is an interface (named after
Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
theory*, Trans. Amer. Math. Soc. 364 (2012) 361–416): a function
`ind : MonicBox n p → ℕ`, a relation `inStratum f H` ("f lies in the stratum of
polynomials whose classification produces the history H"), and the single law
`p2`: 2·ind(f) ≤ v_p(disc f) off the discriminant locus. Nothing else about
`ind`/`inStratum` is imposed by the type.

**The row, in words.** For the carried family: for every prime p, every monic
degree-n f over ℤ_p with disc f ≠ 0, and every history H whose stratum contains
f, the number of certified-increment nodes of H is at most ind(f).

**Status as a proposition.** Because `ind`/`inStratum` are interface fields, the
row is NOT a theorem about all `XFamily n` — e.g. a family with `ind ≡ 0` whose
`inStratum` admits a history with one certified node falsifies it (`p2` is
satisfiable with `ind ≡ 0`). It is a HYPOTHESIS about the intended instance. The
intended instance (documented across the corpus; the real-instance construction
is separate, unfinished work) is: `ind f` = the p-adic index of f — v_p of the
index of the equation order ℤ_p[x]/(f) in the maximal order of the étale algebra
ℚ_p[x]/(f); equivalently Σᵢ ind(Fᵢ) + Σ_{i<j} v_p(Res(Fᵢ, Fⱼ)) over the monic
irreducible factorization f = ∏ Fᵢ in ℤ_p[x] — and `inStratum f H` = "H is the
node ledger of a path of f's canonical Okutsu–Montes classification tree".

## 4. What is already proved in the corpus (machine-checked, Lean-core footprint)

Table/arithmetic layer (`lean/LeanUrat/MovesX/XA1–XA9`):
- `rowTotal` (XA1): the T1–T5 classification is total and exclusive, with the
  stated (ℓ, e, h, sel) characterizations.
- Region count: define the doubled per-side quantity
  `ind2 ν := ℓ(ehℓ + 1 − e − h)` at T1, `(e−1)(h−1)` at T2, `0` at T3/T4/T5.
  Then `ind2 ν = 2·|region(ν)|` where `region(ν)` is the set of lattice points
  (x, y) with s₀ < x ≤ s₀+eℓ, u₀ < y ≤ u₀+hℓ, h(x−s₀) + e(y−u₀) ≤ ehℓ
  (on-or-below the side), and for continuing T1/T2 nodes `1 ≤ ind2 ν`
  (XA9 `ind2Region`, via XA3/XA4/XA5/XA6/XA7). At T3/T4 the region is empty and
  `ind2 = 0` (XA8 `t34Zero`); the corpus documents this "0" as "no positive
  per-side bound recorded", never "the actual per-order index is 0".
- `cert_tf` (XB2): `certified ⟨true, false⟩` coincides with the
  "T1/T2-increment" population predicate; `dCertZero` (XB1): `dCert ≤ dTotal`.

Reduction layer (`lean/LeanUrat/MovesX/KE8.lean`), proved:

```lean
structure GmnOrderAccounting (n p : ℕ) [Fact p.Prime] (G : GMNIndex n p) where
  orderInd : MonicBox n p → ℕ → ℕ
  finsum_le : ∀ f : MonicBox n p, f ∉ discZero n p →
    ∀ R : Finset ℕ, ∑ r ∈ R, orderInd f r ≤ G.ind f
  place : ∀ (f : MonicBox n p) (H : XHistory n),
    Fin (dCert ⟨true, false⟩ H) → ℕ
  place_inj : ∀ (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → G.inStratum f H → Function.Injective (place f H)
  place_charged : ∀ (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → G.inStratum f H →
      ∀ j, 1 ≤ orderInd f (place f H j)

theorem x1aAlignInc_of_orderAccounting {n : ℕ} (X : XFamily n)
    (hacc : ∀ (p : ℕ) [Fact p.Prime],
      Nonempty (GmnOrderAccounting n p (X.gmn p))) :
    X1aAlignP n X ⟨true, false⟩
```

i.e. the row follows once, at every prime, the interface is refined by a
per-order accounting: a per-order contribution function whose finite partial sums
are dominated by `ind`, together with an injective placement of the certified
nodes of every stratum history into orders of contribution ≥ 1. The corpus
documents this carrier as designed to be inhabited from the Guàrdia–Montes–Nart
index machinery; NO instance of `GmnOrderAccounting` is constructed anywhere.

Consumers (proved, conditional on the row): `x1aChain` (XC1) — from the row plus
`p2`, every f in the depth-d stratum union has v_p(disc f) ≥ 2d;
`x3aRoute_of_weightCharge_align` (Kernels/KD5) — the row plus a separate
"weight-charge" hypothesis assemble a route disjunction consumed downstream;
XC3/XC4, XE2/XE3 (envelope estimates over the abstract family).

Separately, the repository has ONE declared axiom citing the same literature
area (`OM/Classifier.lean:1126`, `omReadValuation_lt_of_certLevel_fkeyed`): a
box-level (coefficients mod p^{N+1}) statement that on polynomials whose
discriminant valuation is < N, the valuations at the Newton-polygon hull
vertices and at the side columns read by the classifier are < N. It is keyed to
a different consumption site and does NOT discharge (nor is consumed by) this
row. The project's pinned bibliography for the Guàrdia–Montes–Nart papers is
`docs/GMN_citations.md`; the axiom policy (citation + faithfulness entry +
audit) is `docs/AXIOM_FAITHFULNESS.md`.

## 5. What a solution must deliver

One of:

(a) **Discharge at the intended instance.** A rigorous mathematical proof that
for every prime p and every monic separable degree-n f over ℤ_p, every
root-to-path ledger H of f's Okutsu–Montes classification tree satisfies
#(T1/T2-increment nodes of H) ≤ ind_p(f), with ind_p(f) the p-adic index defined
in §3 — stated so that it instantiates `X1aAlignP n X ⟨true, false⟩` (or
inhabits `GmnOrderAccounting` at every prime, which suffices by KE8). Any gap
must be an explicitly stated open lemma.

(b) **Literature identification.** A published statement (book/paper, theorem
number, hypotheses quoted) from which (a) follows, together with a faithfulness
analysis: exactly which part of the Lean row the citation covers, whether the
Lean row asserts MORE than the citation (quantifier ranges, coordinate
conventions, choice-dependence of any polygon data, the scope of `inStratum`),
and a precise statement of whatever residual is NOT covered.

(c) **Refutation.** A concrete (p, n, f, H) with H realizable as a
classification-tree ledger of f (under the intended instance semantics) and
#(certified-increment nodes of H) > ind_p(f).

Fine print a solution must respect: `dCert` counts T2 nodes through the
`st.inc` flag (they are increments by `t2inc`); T1 re-centerings
(isIncrement = false) are NOT counted at this state; the row has no `HistWF`
hypothesis, so either the instance's `inStratum` must be scoped to genuine
ledgers or the argument must not need well-formedness; `ind2` is a DOUBLED
per-side count (the factor 2 also appears independently in `p2`); and the
region convention includes lattice points ON the side (the "on-or-below" pin),
while excluding the initial column x = s₀ and the base row y = u₀.
