/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.PadicMeasure

/-!
# LeanUrat.Interface — the axiomatic interface ("stated hypotheses")

This module fixes the **axiomatization boundary** for the formalization of the Goal Theorem
(uniform rationality of `p`-adic factorization-type densities at all primes; see
`notes/HUMAN_PROOF.md`). The architecture is "formalize modulo stated hypotheses": everything that
is already in mathlib is *used* from mathlib and is **not** axiomatized here; everything that the
proof legitimately *cites* from the literature is encoded here as a `structure`/`class` carrying the
needed hypotheses, or as a named `axiom`, each with a doc-comment citing its justification.

The boundary, decided minimally (only what later lemmas actually consume):

* **From mathlib (NOT axiomatized).** Finite fields are perfect (`PerfectField.ofFinite`);
  every irreducible over a perfect field is separable (`PerfectField.separable_of_irreducible`);
  `Separable ↔ Squarefree` over a perfect field (`PerfectField.separable_iff_squarefree`);
  polynomial rings, unique factorization (`UniqueFactorizationMonoid`), `degreeLT` and its basis;
  Haar measure existence and valuations (`MeasureTheory`, `Valuation`); finite-field cardinality
  arithmetic. These are real mathlib objects; L1–L7 consume them directly.

* **Axiomatized here (legitimately cited).**
  1. The Guàrdia–Montes–Nart higher-order Okutsu–Montes (OM) structure, distilled to the three
     `p`-independent structural facts **(I)** finite-field residuals, **(II)** lattice Newton
     polygons, **(III)** finite repeated-factor descent (`notes/GMN_citations.md §0`).
  2. The `p`-adic factorization-density / cluster-tree-stratification measure foundations: the
     density `ρ(n,σ;q)`, the cluster-tree stratification, and the per-stratum Haar volume
     (`notes/HUMAN_PROOF.md §0`; cf. paper §2–4 / Igusa §7.4).

Everything in §1 below (the OM facts) is `p`-independent: GMN works over an arbitrary complete
discretely valued field, and the wild/inseparable case is the *generic* case, not an exception.
The *uniformity / rationality* consequences are **derived** (L2core / BB3-∞), never imported.
-/

namespace LeanUrat

open Polynomial MeasureTheory

/-! ## 0. Basic combinatorial data shared by the interface -/

/-- A **factorization shape** at a single OM node: a finitely-supported assignment `d ↦ r_d`
recording the number `r_d` of irreducible factors of degree `d ≥ 1` (counted with multiplicity).
The total degree is `∑ d • r_d`. This is the object L3 / BB3 counts (`notes/L3_proof.md §2.2`). -/
structure FactorizationShape where
  /-- `mult d` is the number of degree-`d` irreducible factors (with multiplicity). -/
  mult : ℕ → ℕ
  /-- Only finitely many degrees occur. -/
  support_finite : (Function.support mult).Finite

namespace FactorizationShape

/-- The total degree `∑_d d · r_d` of a shape. -/
noncomputable def totalDegree (sh : FactorizationShape) : ℕ :=
  ∑ d ∈ sh.support_finite.toFinset, d * sh.mult d

end FactorizationShape

/-! ## 1. The Guàrdia–Montes–Nart order-`r` OM structure (the single load-bearing import)

Source: **J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic number
theory*, Trans. Amer. Math. Soc. 364 (2012), 361–416 (arXiv:0807.2620v2)**. Pinned theorem numbers
are in `notes/GMN_citations.md`. We import *only* the three `p`-independent structural facts (I),
(II), (III); the uniformity consequence is derived, not imported. -/

/-- **GMN order-`r` OM type / cluster node**, carrying exactly the data the cluster recursion
consumes, with the three `p`-independent structural facts attached as fields.

The base residue field is `Fq` (the residue field `F_q` of the unramified `K/Q_p`). The fields of
this structure encode:

* **(I) finite-field residuals** (`GMN §2.1` tower, `Def 2.21`): the order-`r` residual polynomial
  lives in `Fr[y]` with `Fr` a *finite* field, of `p`-independent degree `f₀⋯f_{r-1} ∣ n` over
  `Fq`. This is the linchpin that lets the finite-field building block L3/BB3 apply verbatim at
  every order. Encoded by `[Field Fr] [Finite Fr]` and `residualDegree`.
* **(II) lattice Newton polygon** (`Def 2.3`, `Def 1.1`): the order-`r` polygon `N_r` is a
  principal/lattice object with `p`-independent combinatorics, recorded by `newtonVertices`
  (integer lattice vertices). This is what L4/BB1 consumes.
* **(III) repeated-factor descent** (`Cor 1.20 / 3.8`, `Lemma 3.11(3)`, `Thm 4.18 / Cor 4.19`): a
  multiplicity-1 residual factor is a leaf; a multiplicity-`≥2` factor descends; descent is
  triggered *exactly* by a non-separable residual and terminates at finite, `p`-independently
  bounded order. Encoded by `clusterSize` (strictly decreasing on descent) and `descentBound`. -/
structure OMType (Fq : Type*) [Field Fq] [Finite Fq] where
  /-- The OM/Montes order `r ≥ 0` of this node. -/
  order : ℕ
  /-- The cluster size `e ≤ n` carried at this node. -/
  clusterSize : ℕ
  /-- **(I)** The order-`r` residue field `F_r`. A *finite* field at every order (GMN §2.1). -/
  Fr : Type*
  /-- `F_r` is a field … -/
  [field_Fr : Field Fr]
  /-- … and is finite (the linchpin of fact (I)). -/
  [finite_Fr : Finite Fr]
  /-- The residue degree `f₀⋯f_{r-1}` of `F_r` over `F_q`, a `p`-independent divisor of `n`. -/
  residualDegree : ℕ
  /-- **(II)** The integer lattice vertices of the order-`r` Newton polygon `N_r` (fact (II)). -/
  newtonVertices : List (ℕ × ℕ)
  /-- **(III)** A `p`-independent bound on the descent depth from this node (GMN Thm 4.18 / Cor
  4.19): the OM descent of a separable polynomial terminates at finite, `p`-independently bounded
  order. -/
  descentBound : ℕ

attribute [instance] OMType.field_Fr OMType.finite_Fr

/-- **(III) — the descent trigger, GMN Lemma 3.11(3), stated as a clean interface predicate.**
Descent past order `r` is triggered **exactly** when some order-`r` residual polynomial
`R ∈ F_r[y]` is *non-separable* (equivalently, by finite-field perfectness, *non-squarefree*).

This is the precise locus that L3 counts as `Q_r^{d_r-1}`. We state it as the mathlib predicate
`¬ R.Separable`; the GMN content is that this predicate is the descent trigger, which we record as
the *definition* of `NeedsDescent`. (Citation: `notes/GMN_citations.md §2.3`, Lemma 3.11(3).) -/
def NeedsDescent {Fr : Type*} [Field Fr] (R : Fr[X]) : Prop := ¬ R.Separable

/-- **GMN order-`r` residual-coefficient equidistribution (M6), as a stated hypothesis.**
Fix an OM node `t`. On the Haar-conditioned cell realizing a given finite-slope side, the order-`r`
residual polynomial `R_r(g) ∈ F_r[y]` is **Haar-equidistributed over all monic degree-`d_r`
polynomials over `F_r`**: each fibre has the same conditional measure `|F_r|^{-d_r}`. This converts
L3's *counts* into L2core's *Haar volumes* at every order.

At order 1 this is L4/BB1 (proved exactly); at order `r` it is derived from the GMN order-`r`
coordinate description (`notes/M6_lemma.md`). We expose it as the conclusion the recursion uses: a
uniform conditional probability `condProb` on monic residuals, equal to `(card of the value set) /
|F_r|^{d_r}`. Citation: `notes/M6_lemma.md`; GMN `Def 2.20–2.21`, `Prop 3.5(4)`. -/
structure ResidualEquidistribution {Fq : Type*} [Field Fq] [Finite Fq] (t : OMType Fq) where
  /-- The residual degree `d_r` of the chosen side. -/
  residualSideDegree : ℕ
  /-- The conditional Haar probability that the order-`r` residual lands in a given set of
  monic residual values. -/
  condProb : Finset t.Fr → ℚ
  /-- **Equidistribution.** The conditional probability of any value set `S` of monic residuals
  is `#S / |F_r|^{d_r}` — the uniform measure on `𝔸^{d_r}(F_r)`, the *same* `p`-independent value
  at every prime (M6 conclusion (1)–(2)). -/
  uniform : ∀ S : Finset t.Fr,
    condProb S = (S.card : ℚ) / (Nat.card t.Fr : ℚ) ^ residualSideDegree

/-! ## 2. The `p`-adic factorization-density measure foundations

These encode the measure-theoretic objects of `notes/HUMAN_PROOF.md §0`: the projective/monic
factorization-type density `ρ(n,σ;q)` (an honest Haar **volume**, not a value-weighted integral),
the cluster-tree stratification, and the per-stratum Haar volume. Justification: `p`-adic density
foundations, cf. paper §2–4 / Igusa, *Local Zeta Functions* §7.4. We expose only what L1, L2core,
L6M4, M1 consume: that the density is a real number in `[0,1]`, that the stratification is a finite
partition by cluster-tree shape, and that the total mass is `1`. -/

/-- A **factorization type** `σ` of degree `n`: a multiset of pairs `(eᵢ, fᵢ)` (ramification /
residue data of the irreducible `p`-adic factors) with `∑ eᵢ fᵢ = n` (`notes/HUMAN_PROOF.md §0`). -/
structure FactorizationType where
  /-- The multiset of `(e, f)` pairs. -/
  data : Multiset (ℕ × ℕ)

/-- The degree `n = ∑ eᵢ fᵢ` of a factorization type. -/
def FactorizationType.degree (σ : FactorizationType) : ℕ :=
  (σ.data.map (fun p => p.1 * p.2)).sum

/-! ### `ClusterShape` — the cluster-tree / OM-type shape index (ENRICHED, decision 2b)

A **cluster-tree / OM-type shape** `T` is the index of the cluster recursion (a decorated
Okutsu–Montes tree). For the assembly (L6M4) it is used only as a *decidable index* carrying a
per-shape volume; its internal data is the decorated tree (nodes recorded as
`(order, clusterSize, residualDegree)`). Finitely many shapes contribute to each `(n, σ)` by L5fix
(GMN termination, `p`-independent bound). This object is **distinct** from `FactorizationType`: a
single type `σ` is realized by *many* shapes `T` (different root configurations), and the per-type
density is the multiplicity-weighted sum of per-shape volumes (`DensityFoundation.decomposition`).

**ENRICHED (decision 2b, faithful-by-construction).** Besides the count-native slot list `tree`
(unchanged: it carries the root `(order, clusterSize, residualDegree)` tuple read by
`M5.nodeSizeOf`/`M6.treeSize`/the decoder), the shape now carries the genuine per-node **cell data**
`cells : List ShapeCell`, so that the decoder reconstructs the REAL `MontesAxiom.CountCell` list
faithful-by-construction (NOT the lossy schematic reconstruction the bare `tree` slot would force —
cf. `OMSTEP_BLUEPRINT.md §6/§7.8`). The `tree` slot stays so the descent measure read-back
(`treeSize`/`nodeSizeOf` reading `tree.head.2.1`) and every `⟨tree⟩`-based size lemma are unchanged. -/
mutual
/-- A **cluster-tree / OM-type shape**: the count-native `tree` slot list PLUS the faithful per-node
cell payload `cells` (decision 2b). See the section comment above for the full discussion. -/
structure ClusterShape where
  /-- Count-native slot encoding of the decorated OM tree (root tuple `(order, clusterSize, dr)`
  followed by the concatenated child subtrees). Read by `M5.nodeSizeOf`/`M6.treeSize`. -/
  tree : List (ℕ × ℕ × ℕ)
  /-- **Faithful per-node cell payload** (decision 2b): the genuine `CountCell` data of every cell of
  this node, so the decoder is lossless. Empty for a leaf / order-0 shell. -/
  cells : List ShapeCell
/-- A faithful per-node OM **cell datum**: the genuine `MontesAxiom.CountCell` data of one OM cell —
the residual-stratum degree `dS`, the residue-extension degree `δ`, the lattice Newton-polygon face
`polygon`, and the descent children (each itself a `ClusterShape`). Mirrors `MontesAxiom.CountCell`
but lives upstream (in `Interface`) so the enriched `ClusterShape` can carry it; the down-stream M7
reader erases it back to a genuine `CountCell`. -/
structure ShapeCell where
  /-- residual-stratum degree `d_S`. -/
  dS : ℕ
  /-- residue-extension degree `δ`. -/
  δ : ℕ
  /-- the cell's lattice Newton-polygon face. -/
  polygon : L4.LatticePolygon
  /-- the descent children of this cell (each a strictly smaller cluster shape). -/
  children : List ClusterShape
end

/-- `DecidableEq` for the enriched (recursive, polygon-carrying) `ClusterShape`. The structural
`deriving` handler does not support recursion through `List` nor the function-typed fields of
`L4.LatticePolygon`, so the instance is supplied classically (a legitimate `Decidable` instance, not
an escape hatch). It is `noncomputable`; every consumer of shape-equality in the development is
already `noncomputable` (the sole exception, `Witness.trivCells`, is marked `noncomputable`). -/
noncomputable instance : DecidableEq ClusterShape := Classical.decEq _

/-- `DecidableEq` for `ShapeCell` (classical, as for `ClusterShape`). -/
noncomputable instance : DecidableEq ShapeCell := Classical.decEq _

/-- **The `p`-adic factorization-density foundations, as a stated-hypothesis interface.**

`q` is the residue cardinality (a prime power). `density n σ q` is the **monic/projective
factorization-type density** `α/ρ(n,σ;q)`: the Haar volume of the locus of degree-`n` forms of type
`σ`. The fields record exactly the measure-foundational facts L1/L6M4/M1 consume:

* `density_nonneg`: densities are nonnegative (Haar volumes), not value-weighted integrals
  (load-bearing: at `p=2`, `∫|disc| ≠ volume`; cf. `HUMAN_PROOF §0`).

(C1 docstring fix, `notes/MONTES_AUDIT.md`, 2026-07-02: earlier versions of this docstring advertised
`density_le_one` (densities in `[0,1]`) and `total_mass` (`∑_σ density = 1`) fields that the structure
does NOT carry. The structure is intentionally WEAK — it does not pin `density` to be a probability,
which is exactly why statements about a FREE `F : DensityFoundation` must never be axioms (see
`TameFunctionalEquation` below, the U1 lesson). If those fields are ever added, re-audit every `∀ F`
statement.)

Citation: `p`-adic density foundations, cf. paper §2–4 / Igusa §7.4; cluster-tree stratification
`notes/HUMAN_PROOF.md §0`, L1 `notes/HUMAN_PROOF.md §3`. -/
structure DensityFoundation where
  /-- The factorization-type density `ρ(n,σ;q)` (projective), a rational-valued Haar volume indexed
  by degree `n`, type `σ`, and residue cardinality `q`. -/
  density : (n : ℕ) → FactorizationType → (q : ℕ) → ℚ
  /-- The per-**shape** cluster volume `C_T(q)` — the object of the GMN/BB3-∞ boundary
  (`clusterVolume_rational`). Distinct from the per-type `density`. -/
  clusterVolume : ClusterShape → ℕ → ℚ
  /-- The finite set of cluster-tree shapes contributing to `(n, σ)` (finiteness & `p`-independence
  are L5fix / GMN termination, `notes/L5fix_complete.md`). -/
  shapes : (n : ℕ) → FactorizationType → Finset ClusterShape
  /-- The combinatorial multiplicity `m_T(·)` of a shape — a **polynomial** in `q` (a residue-
  configuration count over `P^1(F_q)`; that it is a *polynomial* in `q` is L3,
  `notes/L3_proof.md §2`). -/
  multiplicity : ClusterShape → Polynomial ℚ
  /-- **Structural decomposition (L1 Hensel-splitting + cluster-tree stratification).** The per-type
  density is the finite, multiplicity-weighted sum of per-**shape** cluster volumes. This is the
  honest measure-foundational / recursion-structure content; it is **NOT** a rationality claim
  (the multiplicities and volumes are arbitrary here). Combined with the per-shape rationality axiom
  `clusterVolume_rational`, L6M4 *derives* that the density is a uniform rational function of `q`.
  Citation: `notes/HUMAN_PROOF.md §3` (L1, splitting), §10 (L6M4 assembly). -/
  decomposition : ∀ (n : ℕ) (σ : FactorizationType), σ.degree = n → ∀ q : ℕ, 1 < q →
    density n σ q = ∑ T ∈ shapes n σ, (multiplicity T).eval (q : ℚ) * clusterVolume T q
  /-- Densities are nonnegative (Haar volumes). -/
  density_nonneg : ∀ n σ q, 0 ≤ density n σ q

/-- **The OM bridge (D1) — the per-shape cluster volume IS a GMN/OM cluster measure.**

This structure is the **structural bridge** (independent-verification defect D1) that ties the
abstract per-shape `clusterVolume` of a foundation `F` to the A0-faithful GMN/Okutsu–Montes cluster
measure of `LeanUrat.PadicMeasure`. It is STRUCTURAL — it asserts only that `F.clusterVolume` is
realized by the FIXED OM cluster measure `PadicMeasure.clusterMeasure` over a decoding
`decode : ClusterShape → OMShape` of the cluster-tree shapes — and is **NOT** a rationality claim.

Rationality is then a THEOREM (`clusterVolume_rational`, below): the FIXED OM cluster measure
`PadicMeasure.clusterMeasure` satisfies the Igusa/Denef cell-decomposition axiom
`PadicMeasure.AX_cellRecursion`, and the proved engine `OMInduction.clusterVol_isRational` (run on
the proved blocks `T_BB1`, `T_BB3`, `L5fix.selfLoop_geometric`) concludes it is a uniform rational
function of `q`. The conclusion is never assumed here; only the realization-as-OM-cluster-measure
(the genuine GMN cluster-tree-stratification content of `notes/BB3_infinity.md`) is.

**Separated out (2026-06-20).** The OM bridge was FACTORED OUT of `DensityFoundation` into this
separate structure so that the measure-free `DensityFoundation` (and the tame functional equation
stated about it) no longer drags `PadicMeasure.clusterMeasure` into the footprint. The only-Montes
Goal theorem (`MontesV2.goal_theorem_montes` — the V2 carrier of the canonical name since W4b,
2026-07-21; the old-`MontesData` sibling is in `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`)
routes rationality through the count-native `MontesDataV2.countingDensity_isRational` and never
references this bridge; the OLD `Goal.goal_theorem`
still consumes it (the measure route — kept for the historical derivation, NOT only-Montes).

**Soundness note (2026-06-19 fix, preserved).** The bridge ties `clusterVolume` to the SINGLE fixed
interface object `PadicMeasure.clusterMeasure` (the actual conditional p-adic Haar cluster volume),
not to a free per-foundation `clusterMeasure` field. With the fixed object, the bridge genuinely
records that `clusterVolume` IS the p-adic cluster measure the Igusa/Denef axiom factors.

Citation: GMN cluster-tree stratification + Igusa/Denef cell decomposition,
`notes/BB3_infinity.md` §4 / `notes/MINIMAL_PADIC_AXIOMS.md`. -/
structure OMBridge (F : DensityFoundation) where
  /-- The decoding of a cluster-tree shape `T` to its GMN order-`r` OM shape (the cluster-tree
  stratification: each `ClusterShape` is the data of a decorated OM tree node, decoded to an
  `OMShape` carrying the finite residue field / lattice polygon / residual). -/
  decode : ClusterShape → PadicMeasure.OMShape
  /-- **The bridge (structural, NOT a rationality claim).** The per-shape cluster volume equals the
  FIXED GMN/OM cluster measure `PadicMeasure.clusterMeasure` of the decoded shape, at every residue
  cardinality. This records that `clusterVolume` is a genuine p-adic cluster Haar measure (the object
  the Igusa/Denef cell-decomposition axiom factors), not an arbitrary function. -/
  clusterVolume_eq_measure :
    ∀ (T : ClusterShape) (q : ℕ), F.clusterVolume T q = PadicMeasure.clusterMeasure (decode T) q

/-! ## 3. The two cited `p`-independence axioms feeding the Goal Theorem

These are the two genuinely-external `p`-independence statements (the "G-A′" import of
`notes/BB3_infinity.md`, and the tame functional equation H-tame of `notes/HUMAN_PROOF.md §12`).
They are stated as named axioms with explicit citations so that the assembled Goal Theorem's
dependence on them is auditable. -/

/-- **(G-A′) Per-SHAPE cluster volume is a `p`-independent rational function of `q` — NOW A THEOREM.**
For every cluster-tree shape `T`, the per-shape cluster volume `C_T(q)` is represented by a single
`num/den ∈ ℚ(t)` at *every* prime power `q` (all `p`, wild included), at every OM order.

**Scope (the fix for the earlier vacuity bug):** this is about the per-**shape** volume
`F.clusterVolume T`, NOT the per-**type** density `F.density n σ`. The density's rationality is
**derived** from this theorem together with `DensityFoundation.decomposition` (the finite
multiplicity-weighted sum) in `L6M4.density_rational` — it is *not* assumed.

**DE-AXIOMATIZED (2026-06-18, soundness-repaired 2026-06-19; bridge separated 2026-06-20).** This
was an asserted `axiom` (the historical conclusion-shaped boundary); it is now a **THEOREM**, derived
from:
* the OM bridge `B : OMBridge F` fields `decode`/`clusterVolume_eq_measure` (the STRUCTURAL fact —
  GMN cluster-tree stratification — that `F.clusterVolume` is the FIXED genuine OM cluster Haar
  measure `PadicMeasure.clusterMeasure`, NOT a rationality claim). The bridge is now a SEPARATE
  argument (factored out of `DensityFoundation`), so only this OLD measure-route theorem carries it;
* the Igusa/Denef cell-decomposition axiom `PadicMeasure.AX_cellRecursion`, now stated about the FIXED
  objects `PadicMeasure.clusterMeasure`/`omPivot` (the load-bearing analytic boundary, a
  measure-FACTORIZATION identity — and CONSISTENT, witnessed by `PadicMeasure.clusterMeasureModel`,
  not a rationality claim);
* the proved engine `OMInduction.clusterVol_isRational` run on the proved blocks (`T_BB1`, `T_BB3`,
  `L5fix.selfLoop_geometric`, the `RatFn` closure lemmas) and the GMN structural axioms
  (`omCells`, `descend_size_lt`).

Rationality is therefore **never assumed**; it emerges only through the proved engine applied to the
measure-factorization axiom. NOTE: the count-native only-Montes path (since W4b 2026-07-21 the V2
spine: `MontesDataV2.C_isRational` / `MontesDataV2.countingDensity_isRational` in
`LeanUrat/MontesV2.lean`; the old `Decomposition.coeff_isRational` route is quarantined) does NOT
use this theorem and carries NONE of these measure
axioms. Citation: `notes/HUMAN_PROOF.md §8` (L2core / BB3-∞), `notes/BB3_infinity.md`,
`notes/MINIMAL_PADIC_AXIOMS.md`. -/
theorem clusterVolume_rational
    (F : DensityFoundation) (B : OMBridge F) :
    ∀ T : ClusterShape,
      ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
        ∀ q : ℕ, (1 < q) → (den.eval (q : ℚ) ≠ 0) ∧
          F.clusterVolume T q = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  intro T
  -- The decoded shape's FIXED OM cluster measure is a uniform rational function of `q`, by the proved
  -- engine run on the Igusa/Denef cell-decomposition axiom (`AX_cellRecursion`). This is exactly the
  -- `IsRationalFn` predicate of `RatFn`, whose unfolding is the existential below.
  obtain ⟨num, den, hden, h⟩ :=
    PadicMeasure.clusterMeasure_isRational_of_AX (B.decode T)
  refine ⟨num, den, hden, fun q hq => ?_⟩
  obtain ⟨hdenq, hval⟩ := h q hq
  -- Transport along the structural bridge `clusterVolume T q = clusterMeasure (decode T) q`.
  exact ⟨hdenq, by rw [B.clusterVolume_eq_measure T q, hval]⟩

/-- **Semantic palindromy of a rational function `num/den`.** `R := num/den` satisfies the
functional equation `R(1/x) = R(x)` at every `x ≠ 0` where both `R(x)` and `R(1/x)` are defined:
```
    ∀ x ≠ 0, den(x) ≠ 0 → den(1/x) ≠ 0 → num(1/x)/den(1/x) = num(x)/den(x).
```
This is the FAITHFUL, degree-robust encoding of `R(1/t) = R(t)`. The earlier coefficient-reversal
encoding `num.reverse * den = num * den.reverse` was DEGREE-BLIND: via `(reverse f).eval x =
x^(natDegree f)·f.eval(1/x)` it means `x^(deg num − deg den)·R(1/x) = R(x)`, i.e. genuine palindromy
only when `deg num = deg den` (weight-0); it wrongly REJECTS palindromic `R` of unequal reduced
degree (e.g. `t/(t²+1)`). Projective densities are weight-0, but that was nowhere enforced, so the
old clause was an unfaithful statement of the functional equation. (Statement-audit B1, 2026-06-15.) -/
def IsPalindromic (num den : Polynomial ℚ) : Prop :=
  ∀ x : ℚ, x ≠ 0 → den.eval x ≠ 0 → den.eval x⁻¹ ≠ 0 →
    num.eval x⁻¹ / den.eval x⁻¹ = num.eval x / den.eval x

/-- **(H-tame) The tame functional equation, as a `Prop`-valued PREDICATE** (the U1 soundness fix,
2026-07-02).

`TameFunctionalEquation F n σ` says: at tame primes `q > n` the density `F.density n σ` is represented
by a single *palindromic* rational function `R^{tame}_σ ∈ ℚ(t)`, `R^{tame}_σ(1/t) = R^{tame}_σ(t)`.
This is the paper's tame palindromic-weight machinery (§5), untouched by the Prop 5.3 failure; the
proofs use it only via "infinitely many tame `p`," sufficient for the `ℚ(t)` identity theorem (L7).

**HISTORY / WHY THIS IS A `def`, NOT AN `axiom` (U1, `notes/MONTES_AUDIT.md`).** This statement was
previously the GLOBAL AXIOM `tame_functionalEquation (F : DensityFoundation) : ∀ n σ, …` quantified
over an ARBITRARY `F`. That axiom was FALSE-AS-STATED (machine-checked `False`-witness: a legal `F`
with `density := fun _ _ q => q` satisfies every `DensityFoundation` field but is not palindromic —
the axiom then forces `x⁻¹ = x`), so every capstone that consumed it rested on an inconsistent base.
The mathematics (paper §5, Del Corso–Dvornicich (2000), Yin) is a true statement about the REAL
density `ρ`, not about an arbitrary `DensityFoundation.density`. The sound encoding is therefore:

* this PREDICATE, consumed as an explicit HYPOTHESIS `htame : TameFunctionalEquation F n σ` by the
  Goal theorems (`Goal.goal_theorem`, and since W4b 2026-07-21 the V2 carriers of the only-Montes
  names, `MontesV2.goal_theorem_montes` / `MontesV2.goal_theorem_via_montes`) —
  free-`F` statements carry it conditionally;
* (RETIRED, W4a 2026-07-21) the interim concrete NAMED-CITE axiom about the REAL count-native
  density (`OM.M9.realDensity_tame_functionalEquation`) that discharged `htame` for the OLD vacuous
  capstone is GONE with that capstone (blueprint D4; see
  `quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`) — the current capstone
  `RealInstanceV2.montes_unconditional` consumes this predicate as the explicit HYPOTHESIS
  `htameFE`, so the trusted base carries NO tame axiom;
* the coupled non-vacuity witness (`Witness.trivF_tame`) PROVES the predicate outright for the
  witness bundle (its density is the constant `1`), so the witness instance is now tame-axiom-free.

Citation: `notes/HUMAN_PROOF.md §12` (L7, H-tame); paper §5; Del Corso–Dvornicich (2000), Yin. -/
def TameFunctionalEquation (F : DensityFoundation) (n : ℕ) (σ : FactorizationType) : Prop :=
  ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
    (∀ q : ℕ, q.Prime → n < q → F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
    -- palindromy R(1/t) = R(t), in the FAITHFUL degree-robust semantic form (audit B1):
    IsPalindromic num den

end LeanUrat
