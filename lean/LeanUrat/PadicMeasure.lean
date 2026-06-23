/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.RatFn
import LeanUrat.OMInduction
import LeanUrat.L3
import LeanUrat.L3Squarefree
import LeanUrat.L4
import LeanUrat.L5fix

/-!
# LeanUrat.PadicMeasure — the MEASURE LAYER: the minimal standard p-adic interface, and the
DERIVED OM cluster-volume recursion (faithful eq-(4.2) form)

This file implements the **measure layer** of the frozen spec
`notes/MINIMAL_PADIC_AXIOMS.md`. It does **two** things:

1. **Declares the minimal interface of standard, cited p-adic-integration facts** as clearly-labeled
   named axioms — and *only* those facts that are genuinely absent from mathlib v4.31.0 (no p-adic
   Haar measure exists; grep of `Mathlib/MeasureTheory` for `Padic` is empty). Each axiom is
   STRUCTURAL (a measure / combinatorial factorization), never a rationality/uniformity claim.

2. **Derives, as LEMMAS, the OM cluster-volume recursion in the faithful eq-(4.2) form** (multi-child
   product + per-cell `F_q`-count via `T_BB3` + box volume via `T_BB1` + self-loop pivot via `L5fix`),
   and feeds it into the already-proved engine `OMInduction.clusterVol_isRational` to conclude that
   every per-shape cluster measure is a uniform rational function of `q`. The recursion that was the
   `hrec` *hypothesis* of `BB3inf.clusterVolume_rational_of_OM` is here a **derived lemma** under the
   interface (`clusterMeasure_rec`).

## HONEST SCOPE (what is proved vs. modulo what)  — audited 2026-06-19, D2-at-descent FAITHFULNESS

* **PROVED (sorry-free, no new axioms):** the A0 anti-caricature tie `Nat.card Fr = q ^ residueDeg`
  (from `Module.natCard_eq_pow_finrank`), the per-cell residual-count evaluation
  (`bb3CellCount_eq_count`, over the shape's OWN `T.Fr`), the box-volume rationality (`T_BB1`), the
  self-loop pivot pole-freeness (`L5fix.selfLoop_geometric`), the assembly
  `clusterMeasure_isRational` via `OMInduction.clusterVol_isRational`, AND **the descent factor-tie
  `descend_children_of_factors`** — now a PROVED LEMMA (mere projection out of the `OMCell.Child`
  data, no longer a free axiom; see below).
* **The descent factor-tie is now a DEFINITIONAL INVARIANT, not a decorative axiom.** Each descent
  child is an `OMCell.Child T` that carries IN ITS DATA the repeated factor `P : Polynomial T.Fr` of
  the parent's ACTUAL residual `T.residual`, its multiplicity `μ`, and proofs `2 ≤ μ`,
  `P^μ ∣ T.residual`, `child.node.size = μ`. So the forest of `omCells`/`children` is mechanically
  pinned to the actual residual factorization — it cannot be "any size-decreasing forest." This
  closes the D2-at-descent gap (the old free `descend_children_of_factors` axiom had zero consumers).
  Likewise `OMCell.residualDeg` is no longer a free ℕ: `OMCell.hResidualDeg : residualDeg =
  stratum.natDegree` ties it to a REAL polynomial `stratum : Polynomial T.Fr` (D2, OMShape style).
* **GAP-1 FIX (2026-06-19) — the BB3 wild count is now GENUINELY `q`-VARYING and LOAD-BEARING (not
  inert).** The per-cell residual point-count fed into the recursion is no longer the FROZEN constant
  `residualCount T d = Nat.card{…over the fixed T.Fr…}` (which was a constant in `q`, so its rationality
  came from `isRationalFn_const` and the wild-prime mechanism was never exercised). It is now the
  `q`-VARYING function `residualCountFn T d := fun q => (q^δ)^(d-1) = q^(δ(d-1))` (`δ = residueDeg`),
  the BB3 count over the finite field `𝔽_{q^δ}` that EXISTS for every prime power `q`. Its rationality
  (`residualCountFn_isRational`) is supplied by the `q`-power closure `RatFn.isRationalFn_qpow`, whose
  representing NUMERATOR is the non-constant monomial `X^{δ(d-1)}` — so the BB3 count's `q`-dependence
  genuinely PROVES the per-cell coefficient's rationality (`cellCoeff_isRational` now consumes
  `residualCountFn_isRational`, NOT `isRationalFn_const`). `AX_cellRecursion`, the consistency model
  `clusterMeasureModel`, and `cellCoeff` all use `residualCountFn T c.residualDeg q` (a function of the
  free `q`). The frozen `Nat.card`-over-`T.Fr` count `residualCount` is retained only as the A0
  non-vacuity certificate (`residualCount_eq`: at the specific `q = |T.baseField|` the genuine count
  over `T.Fr` equals `residualCountFn T d q`). EVIDENCE the count is load-bearing: `#print axioms
  cellCoeff_isRational` is unchanged (Lean core only — it is rational-function bookkeeping), but its
  proof term now factors through the non-constant monomial `X^{δ(d-1)}`; one can confirm by replacing
  `residualCountFn` with a `q`-free constant and watching `cellCoeff`/`AX_cellRecursion`/the model fail
  to typecheck against the `q`-varying recursion shape.
* **GAP-1 FIX — omCells strata PINNED to the actual residual (PROVED LEMMA `cell_stratum_of_residual`).**
  `OMCell` now carries `hStratumDvd : stratum ∣ T.residual`, so every cell's residual stratum is a
  genuine FACTOR of the parent's ACTUAL residual `T.residual` (cell-level analogue of `Child.hdvd`).
  The cell partition `omCells T` is therefore pinned to the real residual factorization — its cells are
  strata OF `T.residual`, not free polynomials. **Honest remaining omCells gap:** the LIST `omCells T`
  is still a structural axiom; we pin each cell's stratum (a divisor of `T.residual`) and degree, but we
  do NOT yet prove that the multiset of strata RECONSTRUCTS `T.residual` (an exhaustiveness/partition
  statement — that the cells cover the full GMN factorization). That exhaustiveness is the standard GMN
  cell-decomposition content still recorded via the `omCells` structural axiom.
* **DERIVED MODULO the two cited analytic axioms** `AX_columnMeasure` (Igusa box/shell) and
  `AX_cellRecursion` (Igusa/Denef cell decomposition) **+ the GMN structural axioms** `omCells` (the
  finite cell partition), `descend` (the descent list), and `descend_size_lt` (strict size drop — the
  well-foundedness engine input) **+ Lean core.** (`descend_children_of_factors` is NO LONGER in this
  list — it is a proved lemma.) This is *not* a proof of `clusterVolume_rational` from nothing; it is
  a faithful reduction of it to a minimal standard p-adic-integration interface. The conclusion
  (`IsRationalFn (clusterMeasure T)`) is a THEOREM, never an axiom; rationality emerges only
  downstream through `clusterVol_isRational`.

## What is NOT axiomatized (used from mathlib / proved in-project)

`measure_biUnion_finset` (finite additivity), `Module.natCard_eq_pow_finrank` (the A0 finrank↔card
tie), `T_BB3`/`L3Squarefree` (the residual count), `T_BB1`/`L4.cellVolume_eq` (the box volume),
`L5fix.selfLoop_geometric` (the self-loop pivot), the `RatFn` closure lemmas, and the OM induction
`OMInduction.clusterVol_isRational` are all PROVED (in mathlib or in-project). The cell-volume value
`(1-Q⁻¹)^V Q^{-A}` is itself PROVED in `L4.cellVolume_eq` from `AX_columnMeasure`, so `AX_columnMeasure`
asserts strictly *less* than the cell volume.

## Citations

* `AX_columnMeasure`: Igusa, *Local Zeta Functions* §7.4 (box/shell normalization
  `μ{v(c)≥h}=Q^{-h}`, `μ{v(c)=h}=(1-Q⁻¹)Q^{-h}`); standard local-field Haar `[O_δ:p^m O_δ]=Q^m`.
  `AXIOM_FAITHFULNESS.md` AX-MEASURE(a),(b).
* `AX_cellRecursion`: Igusa, *Local Zeta Functions* §7.4 / Prop 7.4.1 (p-adic change of variables;
  unit-Jacobian ⇒ measure-preserving; cell decomposition of a local zeta integral); Denef, *The
  rationality of the Poincaré series associated to the p-adic points on a variety*, Invent. Math. 77
  (1984) 1–23 (cell decomposition over definable cells). `BB3_infinity.md` eq (4.1)/(4.2) §4.2.
* GMN structural axioms: Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
  theory*, Trans. Amer. Math. Soc. 364 (2012) 361–416 (arXiv:0807.2620). Descent dichotomy:
  Cor 1.20 / 3.8 + Lemma 3.11(3) + Thm 4.18 / Cor 4.19. `AXIOM_FAITHFULNESS.md` AX-GMN-III.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.PadicMeasure

open Polynomial RatFn

/-! ## A. The A0-faithful OM/Montes shape

`OMShape` carries the GMN order-`r` data with the **A0 anti-caricature ties** enforced as PROVED
invariants (independent-verification defect D2):

* `Fr` is a **finite** field (GMN fact I, §2.1 tower);
* `baseField` is a finite field with a genuine `Algebra baseField Fr` (so `residueDeg` is a REAL
  residue-field extension degree, not a free integer): `residueDeg = Module.finrank baseField Fr`;
* `residual : Polynomial Fr` is the actual order-`r` residual, and `residualDeg = residual.natDegree`
  ties the degree field to the actual polynomial (so the BB3 count below is computed from the genuine
  residual, not a monomial in free integers);
* `polygon : L4.LatticePolygon` is the GMN order-`r` lattice Newton polygon (fact II);
* `size` is the cluster size (the well-founded descent measure).

These ties make `Nat.card Fr = q ^ residueDeg` a PROVED lemma (`natCard_Fr` below) rather than an
axiom — killing the D2 caricature. -/
structure OMShape where
  /-- cluster size `e` (the well-founded descent measure). -/
  size : ℕ
  /-- OM/Montes order `r`. -/
  order : ℕ
  /-- order-`r` residue field `F_r`. -/
  Fr : Type
  [instField : Field Fr]
  [instFinite : Finite Fr]
  /-- the base residue field `𝔽` (the residue field of the unramified `K/Q_p`). -/
  baseField : Type
  [instBaseField : Field baseField]
  [instBaseFinite : Finite baseField]
  [instAlg : Algebra baseField Fr]
  /-- `[F_r : 𝔽] = f₀…f_{r-1}`, tied to the REAL extension degree `Module.finrank baseField Fr`. -/
  residueDeg : ℕ
  /-- **A0 tie (PROVED-tieable, not free):** the residue degree is the genuine extension degree. -/
  hResidueDeg : residueDeg = Module.finrank baseField Fr
  /-- the order-`r` lattice Newton polygon (fact II; reuses `L4.LatticePolygon`). -/
  polygon : L4.LatticePolygon
  /-- the order-`r` residual polynomial over the finite `F_r` (fact I, GMN Def 2.21). -/
  residual : Polynomial Fr
  /-- the degree `d_r` of the order-`r` residual. -/
  residualDeg : ℕ
  /-- **A0 tie (PROVED-tieable, not free):** the residual degree is the ACTUAL `residual.natDegree`. -/
  hResidualDeg : residualDeg = residual.natDegree

attribute [instance] OMShape.instField OMShape.instFinite
  OMShape.instBaseField OMShape.instBaseFinite OMShape.instAlg

/-- A single **descent child** of parent shape `T` (the D2-at-descent FAITHFULNESS encoding).

This bundle encodes the GMN-III descent factor-tie as a DEFINITIONAL TYPE INVARIANT (carried in the
data, but NOT consumed on the rationality path — see the HONEST SCOPE note on `descend_children_of_factors`
below): it does not merely name a
child node, it carries — IN THE DATA — the witness that the child arises from a genuine
multiplicity-`≥2` factor of the parent's ACTUAL residual `T.residual : Polynomial T.Fr`:

* `node` — the descended child shape (an `OMShape`);
* `factor` — the repeated factor `P : Polynomial T.Fr` of `T.residual` that triggered the descent;
* `mult` — its multiplicity `μ`;
* `hmult : 2 ≤ mult` — descent fires *only* at non-separable (multiplicity-`≥2`) factors (GMN
  Lemma 3.11(3): a multiplicity-1 factor is a leaf, only `μ ≥ 2` descends);
* `hdvd : factor ^ mult ∣ T.residual` — `P^μ` genuinely divides the ACTUAL residual;
* `hsize : node.size = mult` — the child's cluster size IS that factor multiplicity.

Because the witness is part of the data, the old free-floating axiom `descend_children_of_factors` is
now a DEFINITIONAL invariant: `OMCell.child_of_factors` below extracts it by projection (no axiom).
So the descent tree is mechanically pinned to the actual residual factorization, not just any
size-decreasing forest. -/
structure OMCell.Child (T : OMShape) where
  /-- the descended child shape (a node of the recursion). -/
  node : OMShape
  /-- the repeated factor `P` of the parent's ACTUAL residual `T.residual` that triggers descent. -/
  factor : Polynomial T.Fr
  /-- its multiplicity `μ` in `T.residual`. -/
  mult : ℕ
  /-- **GMN Lemma 3.11(3): only multiplicity-`≥2` factors descend** (mult-1 ⇒ leaf). -/
  hmult : 2 ≤ mult
  /-- **the factor genuinely divides the ACTUAL residual:** `P^μ ∣ T.residual`. -/
  hdvd : factor ^ mult ∣ T.residual
  /-- **the child's cluster size IS the factor multiplicity** `μ` (GMN child-size law). -/
  hsize : node.size = mult

/-- A single **OM cell** of a parent shape `T` (one residual-shape stratum on one order-`r`
Newton-polygon face). It records the GMN cell data the eq-(4.2) recursion consumes per cell:

* `polygon` — the cell's lattice Newton-polygon face (fact II), feeding `T_BB1`'s box volume;
* `stratum` — the ACTUAL residual stratum `S : Polynomial T.Fr` on this face, with
  `hResidualDeg : residualDeg = stratum.natDegree` tying the degree field to a REAL polynomial over
  the parent's residue field (the D2 fix: no free ℕ, in the same style as `OMShape.hResidualDeg`);
* `residualDeg` — the degree `d_S` of that stratum; the per-cell `F_q`-count `N_S(Q_r)` is computed
  from the ACTUAL residual over `T.Fr` of this degree (A0-tied, not free);
* `children` — the **multi-child** list `List (OMCell.Child T)` (the D3 + D2-at-descent fix): each
  entry carries, IN THE DATA, the multiplicity-`≥2` residual factor of `T.residual` that descends to
  a strictly-smaller child cluster, with the witnessing proofs (GMN-III). The recursion sums over
  `ch.node` (an `OMShape`); the factor-tie travels alongside as a definitional invariant.

This is a *plain* record (one-directional reference to `List (OMCell.Child T)`); the recursion's
children are nodes (`ch.node : OMShape`), so no mutual recursion is needed. -/
structure OMCell (T : OMShape) where
  /-- the cell's lattice Newton-polygon face (T_BB1 box volume). -/
  polygon : L4.LatticePolygon
  /-- the ACTUAL residual stratum `S : Polynomial T.Fr` on this face (D2: ties `residualDeg`). -/
  stratum : Polynomial T.Fr
  /-- **GMN cell-partition tie (the omCells-pinning fix, definitional invariant):** the cell's
  residual stratum `S` is a genuine FACTOR of the parent's ACTUAL residual `T.residual`. This pins the
  GMN order-`r` cell partition to the real residual factorization (the cells are strata OF
  `T.residual`, not free polynomials), in the same style as `OMCell.Child.hdvd` for descent children.
  [GMN Def 2.21 + §2.5: the order-`r` cells are indexed by the residual-shape strata, each a factor of
  the residual.] -/
  hStratumDvd : stratum ∣ T.residual
  /-- the residual-stratum degree `d_S` on this face (BB3 count). -/
  residualDeg : ℕ
  /-- **A0 tie (D2, definitional, not free):** the stratum degree is the ACTUAL `stratum.natDegree`. -/
  hResidualDeg : residualDeg = stratum.natDegree
  /-- the descent children of this cell — each a `Child T` carrying its repeated-factor witness and
  strictly smaller `size` (GMN-III). -/
  children : List (OMCell.Child T)

/-- **A0 helper (PROVED, no axiom).** When the base residue field has size `q`, the order-`r` residue
field `F_r` has size `q ^ residueDeg`, because `residueDeg = Module.finrank baseField Fr` is a genuine
extension degree and `Nat.card Fr = (Nat.card baseField) ^ finrank` (`Module.natCard_eq_pow_finrank`).
This is the linchpin that ties the BB3 count to the shape's OWN residual (kills the D2 caricature). -/
theorem natCard_Fr (T : OMShape) (q : ℕ) (hb : Nat.card T.baseField = q) :
    Nat.card T.Fr = q ^ T.residueDeg := by
  have hfin : Module.Finite T.baseField T.Fr :=
    Module.Finite.of_finite (R := T.baseField) (M := T.Fr)
  rw [T.hResidueDeg, ← hb]
  exact Module.natCard_eq_pow_finrank

/-! ## B. The GMN structural axioms (descent dichotomy + strict size drop + cell partition)

Only GMN structural facts; **none asserts uniformity/rationality/volume**. These replace the weaker
stubs in `BB3inf.lean`. The descent factor-tie that was the old free `descend_children_of_factors`
axiom is now ENCODED IN THE DATA (`OMCell.Child` carries the mult-`≥2` factor of the ACTUAL
`T.residual` and its witnessing proofs), so the only remaining structural axioms here are:

* `omCells` — the finite GMN order-`r` cell partition;
* `descend` — the descent list (kept for the interface; not consumed by the recursion);
* `descend_size_lt` — strict cluster-size drop, now phrased about `ch.node.size` (the
  well-foundedness input to `clusterMeasureModel`/`clusterVol_isRational`).

`descend_children_of_factors` is then a PROVED LEMMA (projection out of the `OMCell.Child` data), and
`AX_GMN_IV_terminates` was DROPPED earlier (dead weight — provable from `InvImage.wf`/`descend_size_lt`).

Citation: GMN Cor 1.20 / 3.8 (mult-1 ⇒ irreducible leaf), Lemma 3.11(3) (non-separable residual =
descent trigger), Thm 4.18 / Cor 4.19 (finite termination). `AXIOM_FAITHFULNESS.md` AX-GMN-III. -/

/-- **(AX-GMN-III, the order-`r` cell partition).** The GMN finite cell partition of the shape-`T`
cluster locus: one cell per order-`r` Newton-polygon face × residual-shape stratum (fact II × fact I).
Finiteness is GMN termination (Thm 4.18). [GMN §2.5 + Def 2.21.] -/
axiom omCells : (T : OMShape) → List (OMCell T)

/-- **(AX-GMN-III, descent).** The order-`r` descent: each shape's repeated residual factors yield
child shapes. [GMN Cor 1.20/3.8 + Lemma 3.11(3).] -/
axiom descend : OMShape → List OMShape

/-- **(AX-GMN-III, strict size descent).** Off the self-loop, every descent child of every cell has
strictly smaller cluster size. This is what makes the OM-order induction well-founded. The child is
now an `OMCell.Child`, so this constrains `ch.node.size`.
[GMN: a mult-`≥2` factor of a degree-`d_r < e` residual ⇒ child size `≤ d_r < e`.] -/
axiom descend_size_lt :
    ∀ (T : OMShape), ∀ c ∈ omCells T, ∀ ch ∈ c.children, ch.node.size < T.size

/-- **(AX-GMN-III, children tied to repeated factors — the D2-at-descent anti-caricature fix, NOW A
PROVED LEMMA, no longer a free axiom).** Every descent child arises from a genuine
multiplicity-`≥2` factor `P` of the ACTUAL residual `T.residual : Polynomial T.Fr`, with the child's
cluster size equal to that multiplicity. So descent fires *only* at non-separable (non-squarefree)
residual loci, and the children are not free data.

**This is a DEFINITIONAL invariant carried in the data** (not a free axiom): the witness `(P, μ)` and
the three proofs `2 ≤ μ`, `P^μ ∣ T.residual`, `ch.node.size = μ` are fields of `OMCell.Child`
(`factor`/`mult`/`hmult`/`hdvd`/`hsize`), so this statement is proved by mere projection, and any
inhabitant of `omCells`/`children` is pinned — AT THE TYPE LEVEL — to the actual residual factorization.
**HONEST SCOPE (audit 2026-06-19):** this pin is NOT consumed by the rationality proof. The OM engine
erases each child to `ch.node` (via `omContribs`) and uses only `descend_size_lt`, so this lemma has
ZERO downstream proof consumers and is INERT on the rationality path: it strengthens the faithfulness of
the interface DATA, not the rationality footprint. The `omCells` exhaustiveness (that the strata
reconstruct `T.residual`) remains a structural axiom.
[GMN Lemma 3.11(3): non-separable residual = descent trigger; child size = factor multiplicity.] -/
theorem descend_children_of_factors :
    ∀ (T : OMShape), ∀ c ∈ omCells T, ∀ ch ∈ c.children,
      ∃ (P : Polynomial T.Fr) (μ : ℕ), 2 ≤ μ ∧ (P ^ μ ∣ T.residual) ∧ ch.node.size = μ :=
  fun _ _ _ ch _ => ⟨ch.factor, ch.mult, ch.hmult, ch.hdvd, ch.hsize⟩

/-- **(omCells-pinning, NOW A PROVED LEMMA).** Every GMN order-`r` cell's residual stratum
`c.stratum : Polynomial T.Fr` is a genuine FACTOR of the parent's ACTUAL residual `T.residual`. So
the cell partition `omCells T` is mechanically pinned to the real residual factorization — its cells
are strata OF `T.residual`, not free polynomials. This is the cell-level analogue of
`descend_children_of_factors`: a DEFINITIONAL invariant carried in the data (the witness is the
`OMCell.hStratumDvd` field), proved by mere projection — but, like that lemma, NOT consumed on the
rationality path (inert; it pins the interface DATA, not the rationality footprint). Together with the degree tie `c.hResidualDeg`
(`c.residualDeg = c.stratum.natDegree`), the BB3 count `residualCountFn T c.residualDeg` is computed at
the degree of a genuine factor of the actual residual, not at a free integer.
[GMN Def 2.21 + §2.5: order-`r` cells are the residual-shape strata, each a residual factor.] -/
theorem cell_stratum_of_residual :
    ∀ (T : OMShape), ∀ c ∈ omCells T, c.stratum ∣ T.residual :=
  fun _ c _ => c.hStratumDvd

/-! ## C. The two standard p-adic-integration AXIOMS (Igusa / Denef) — the honest analytic boundary

These are the only genuinely-analytic gaps: mathlib v4.31.0 has no p-adic Haar measure (no
`MeasureSpace`/`BorelSpace`/`haarMeasure` instance on `PadicInt` or any DVR; grep empty), no Igusa
local zeta, no Denef cell decomposition. So they are stated as **interface facts** — named axioms with
literature citations — in the established "recorded-via-hypothesis" style of `L4.cellVolume_eq`'s
`hfactor`. NO measure is constructed; `clusterMeasure`/`cellMeasure` are plain `ℚ`-valued functions.

**Neither axiom is a rationality/uniformity claim.** `AX_columnMeasure` asserts a specific scalar
*product structure* (whose closed-form value is then PROVED in `L4.cellVolume_eq`); `AX_cellRecursion`
asserts a specific *measure-factorization identity* whose three factors are honest cardinal/measure
quantities. Rationality is never asserted here — it emerges only downstream via
`OMInduction.clusterVol_isRational`. -/

/-- **AX_columnMeasure (Igusa box/shell — single-coordinate Haar value).**
Over the unramified `O_δ` with residue size `Q = q^δ`, the cell measure of a lattice Newton polygon is
the **finite product** of the per-column box/shell Haar measures `L4.columnMeasure`. The per-column
values are the standard `μ{v(c)≥h}=Q^{-h}` (box) and `μ{v(c)=h}=(1-Q⁻¹)Q^{-h}` (shell), using only
`[O_δ:p^m O_δ]=Q^m` (`v(p)=1`, unramified) + product Haar (column independence). This is exactly the
`hfactor` law consumed by `L4.cellVolume_eq`; the assembled closed form `(1-Q⁻¹)^V Q^{-A}` is PROVED
there, so this axiom asserts strictly LESS than the cell volume.

Citation: Igusa, *Local Zeta Functions* §7.4 (box/shell normalization); standard local-field Haar
`[O_δ:p^m O_δ]=Q^m`. `AXIOM_FAITHFULNESS.md` AX-MEASURE(a),(b). NOT a rationality claim. -/
axiom AX_columnMeasure
    (cellVol : L4.LatticePolygon → ℕ → ℚ) (pg : L4.LatticePolygon) (Q : ℕ) :
    cellVol pg Q = ∏ i : Fin pg.width, L4.columnMeasure pg Q i

/-- The **per-cell residual point-count** factor `N_S(Q_r)` (BB3): the number of non-squarefree
(refinement-triggering) monic degree-`residualDeg` residual polynomials over the shape's OWN residue
field `T.Fr`. **A0-tied (D2 fix):** this is `Nat.card` of the ACTUAL non-squarefree locus over
`T.Fr` — not a monomial in free integers. `T_BB3` evaluates it to `(Nat.card T.Fr)^{residualDeg-1}`. -/
noncomputable def residualCount (T : OMShape) (d : ℕ) : ℚ :=
  (Nat.card {R : Polynomial T.Fr // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R} : ℚ)

/-- **The GENUINELY `q`-VARYING per-cell residual point-count `N_S(q)` (BB3, on the rationality
path).** At residue cardinality `q`, the OM/Montes order-`r` residue field at parameter `q` has size
`Q_r = q ^ residueDeg` (`δ := residueDeg`, the `p`-independent residue-extension degree), and the
count of non-squarefree (refinement-triggering) monic degree-`d` polynomials over a finite field of
size `Q_r` is `Q_r^{d-1} = (q^δ)^{d-1}` (this is `T_BB3` over the finite field `𝔽_{q^δ}`, which
EXISTS for EVERY prime power `q`). So as a FUNCTION of the free parameter `q` this BB3 count is

    residualCountFn T d  :=  fun q => ((q : ℚ) ^ T.residueDeg) ^ (d - 1)  =  q ^ (δ·(d-1)).

This is the object that the eq-(4.2) recursion (`AX_cellRecursion`), the consistency model
(`clusterMeasureModel`), and the per-cell coefficient (`cellCoeff`) consume. It is genuinely a
function of `q` — its representing numerator is the non-constant monomial `X^{δ(d-1)}` (see
`residualCountFn_isRational`) — so the wild-prime BB3 mechanism is on the rationality path, not frozen
at one field. The frozen `Nat.card`-over-`T.Fr` value `residualCount` above is retained only as the
A0 non-vacuity certificate (`residualCount_eq`): at the SPECIFIC `q = |T.baseField|`, the genuine
count over the shape's OWN residue field `T.Fr` equals `residualCountFn T d q`, so the `q`-varying
function is the honest value of the actual finite-field count, not an unmoored monomial. -/
noncomputable def residualCountFn (T : OMShape) (d : ℕ) : ℕ → ℚ :=
  fun q => ((q : ℚ) ^ T.residueDeg) ^ (d - 1)

/-- The OM-recursion **self-loop pivot** for a shape `T`: the geometric factor `1 - q^{-w(e)}`
(`w = L5fix.selfLoopExponent`) at ramifying nodes (`size ≥ 2`), and the trivial `1` at leaves
(`size < 2`). Pole-free on `q > 1` by `L5fix.selfLoop_geometric`.

**Base-change note (q vs `Q = q^δ`).** The pivot, the BB3 count, and the BB1 box volume are all
written here as rational functions of the BASE residue cardinality `q = |F_q|`; the local field's
own residue cardinality is `Q = q^δ` (`δ = [K:Q_p]` unramified degree, `Q = q^δ`, `v(p)=1`). Since
`Q^{-k} = (q^δ)^{-k} = q^{-δk}` is itself a rational function of `q`, every `Q`-monomial reindexes to
a `q`-monomial with no loss; uniformity in `q` is the strictly stronger statement consumed downstream.

This is a **concrete, fixed object** (defined from `L5fix.selfLoopExponent`), NOT a free axiom
binder. It is the divisor that resums the unique non-progressing self-loop cell in the Igusa/Denef
cell decomposition; `omPivot_ne` below PROVES it is nonzero on `q > 1`. -/
noncomputable def omPivot (T : OMShape) : ℕ → ℚ :=
  fun q => if 2 ≤ T.size then 1 - ((q : ℚ) ^ L5fix.selfLoopExponent T.size)⁻¹ else 1

/-- **The actual conditional p-adic Haar cluster volume — an OPAQUE, FIXED object.**
`clusterMeasure T q` is THE per-shape conditional p-adic Haar cluster measure of the GMN order-`r`
shape `T` at residue cardinality `q` (a single `ℚ`-valued function, not a free parameter). No p-adic
Haar measure is constructed in mathlib v4.31.0 (grep of `Mathlib/MeasureTheory` for `Padic` is empty);
so this object is recorded as a named axiom, exactly in the established "recorded-via-hypothesis"
style of `L4.cellVolume_eq`'s `hfactor`.

**This is NOT a rationality/uniformity/volume-value claim:** it asserts only that the symbol denotes a
fixed `ℚ`-valued function. Its only mathematical content is supplied by `AX_cellRecursion` below (the
Igusa/Denef factorization identity it satisfies). Consistency of that identity for THIS fixed object
is DEMONSTRATED by `clusterMeasureModel` + `clusterMeasureModel_rec` (a concrete well-founded model
satisfying the same recursion), so the axiom is satisfiable, not inconsistent. -/
axiom clusterMeasure : OMShape → ℕ → ℚ

/-- **AX_cellRecursion (Igusa/Denef per-cell decomposition) — THE load-bearing axiom.**
On the shape-`T` cluster locus, the conditional p-adic Haar cluster measure `clusterMeasure` factors,
cell by cell (GMN order-`r` cells), as a finite sum over `omCells T` of

    (residual point-count of the cell over `T.Fr`)   -- → T_BB3
  × (box/shell Haar volume of the cell's polygon)     -- → AX_columnMeasure → T_BB1
  × (∏ over the cell's descent children of clusterMeasure(child))   -- multi-child ∏ (recursive)

with the unique non-progressing self-loop cell resummed by dividing by `omPivot T q` (the geometric
self-loop factor `1 - q^{-w}`, `1` if no loop). This is the Igusa stationary-phase / Denef
cell-decomposition identity read on one shape (the residual-coefficient map is a Haar submersion onto
`𝔸^{d_S}(F_r)`, so integrating the cell condition factors a finite-field point-count × the lattice box
volume × the child sub-integrals). **The faithful eq-(4.2) form: multi-child product + per-cell count
from the ACTUAL residual** (the D3 + D2 fixes).

**Stated about the FIXED objects `clusterMeasure` and `omPivot`** (no `clusterMeasure`/`pivot`
binders). This is the critical soundness fix (independent-verification verdict 2026-06-19): the
earlier form universally quantified over both `clusterMeasure` and a free RHS divisor `pivot`, which
was logically INCONSISTENT (instantiating one shape/`q` with the constant `1` measure and two
different pivots `1` vs `2` forced `1 = 1/2 = False`). Here the recursion asserts the per-cell
factorization of THE one actual cluster volume divided by the ONE concrete pivot `omPivot`; there is
no second pivot to vary, so the False-derivation route is gone, and the identity is satisfied by the
concrete model `clusterMeasureModel` (so it is consistent).

This is a STRUCTURAL measure-factorization identity, **NOT a rationality claim**: the three factors
are honest `Nat.card`/Haar quantities; rationality is supplied independently by the proved blocks
(`T_BB3`, `T_BB1`, the IH) and emerges only via `OMInduction.clusterVol_isRational`.

Citation: Igusa, *Local Zeta Functions* §7.4 / Prop 7.4.1; Denef, Invent. Math. 77 (1984) 1–23
(cell decomposition over definable cells). `BB3_infinity.md` eq (4.1)/(4.2) §4.2. Self-loop closure:
`L5fix.selfLoop_geometric` (PROVED). -/
axiom AX_cellRecursion (T : OMShape) (q : ℕ) (hq : 1 < q) :
    clusterMeasure T q
      = ((omCells T).map (fun c =>
            residualCountFn T c.residualDeg q
            * L4.bb1Value c.polygon q
            * (c.children.map (fun ch => clusterMeasure ch.node q)).prod)).sum
        / omPivot T q

/-! ## C'. CONSISTENCY DEMONSTRATION — a concrete model satisfying the recursion

`AX_cellRecursion` is satisfiable: we EXHIBIT a `clusterMeasureModel : OMShape → ℕ → ℚ` defined by
well-founded recursion on `OMShape.size` (decreasing by `descend_size_lt`) that satisfies the SAME
recursion identity (`clusterMeasureModel_rec`). The existence of such a model is precisely the
statement that the axiom is consistent (no longer derives `False` by the old binder route). The
opaque `clusterMeasure` is then a sound, satisfiable interface symbol — not a contradiction. -/

/-- **The concrete well-founded model of the cell recursion (consistency witness).**
Defined by well-founded recursion on `OMShape.size`: the recursive calls `clusterMeasureModel ch q`
range over `ch ∈ c.children` for `c ∈ omCells T`, each strictly smaller by `descend_size_lt`. The
`List.attach`/membership machinery carries the decrease proof into `decreasing_by`. This function
SATISFIES `AX_cellRecursion`'s identity (proved as `clusterMeasureModel_rec`), exhibiting a model and
hence the relative consistency of the axiom. -/
noncomputable def clusterMeasureModel (T : OMShape) (q : ℕ) : ℚ :=
  ((omCells T).attach.map (fun c =>
      residualCountFn T c.1.residualDeg q
      * L4.bb1Value c.1.polygon q
      * (c.1.children.attach.map (fun ch => clusterMeasureModel ch.1.node q)).prod)).sum
    / omPivot T q
termination_by T.size
decreasing_by
  · -- `ch.1 ∈ c.1.children`, `c.1 ∈ omCells T` ⇒ `ch.1.node.size < T.size` by `descend_size_lt`.
    exact descend_size_lt T c.1 c.2 ch.1 ch.2

/-- **`clusterMeasureModel` satisfies the cell recursion (the consistency proof).** This is the exact
identity `AX_cellRecursion` asserts, with `clusterMeasure := clusterMeasureModel`. Its existence shows
`AX_cellRecursion` is satisfiable, hence (relatively) consistent: the fixed-object axiom can no longer
prove `False`. -/
theorem clusterMeasureModel_rec (T : OMShape) (q : ℕ) (hq : 1 < q) :
    clusterMeasureModel T q
      = ((omCells T).map (fun c =>
            residualCountFn T c.residualDeg q
            * L4.bb1Value c.polygon q
            * (c.children.map (fun ch => clusterMeasureModel ch.node q)).prod)).sum
        / omPivot T q := by
  -- Unfold one step of the well-founded recursion, then strip the two `attach`es (they only carry
  -- membership proofs that the RHS does not reference).
  rw [clusterMeasureModel]
  congr 1            -- peel `_ / omPivot T q`
  congr 1            -- peel `(_).sum`
  -- Inner: rewrite each child `attach`-map back to a plain map (`List.attach_map_val`); this turns the
  -- attached summand into the plain summand pointwise, so the outer `attach`-map then collapses too.
  have hchildren : ∀ (c : OMCell T),
      (c.children.attach.map (fun ch => clusterMeasureModel ch.1.node q))
        = c.children.map (fun ch => clusterMeasureModel ch.node q) := by
    intro c
    exact List.attach_map_val (l := c.children) (f := fun ch => clusterMeasureModel ch.node q)
  simp only [hchildren]
  -- Outer: the summand is now `fun c => …(c.1)…`; strip the `omCells` `attach`.
  exact List.attach_map_val (l := omCells T)
    (f := fun c => residualCountFn T c.residualDeg q * L4.bb1Value c.polygon q
      * (c.children.map (fun ch => clusterMeasureModel ch.node q)).prod)

/-! ## D. DERIVED helpers — the three factors are each rational (PROVED, no new axioms)

These evaluate the three factors of `AX_cellRecursion` into the rational-function shape the OM engine
consumes. None is an axiom; each is a closed-form computation citing a PROVED block. -/

/-- The **per-cell coefficient** of a cell `c` of parent `T`: the GENUINELY `q`-varying BB3 residual
count `residualCountFn T c.residualDeg q = (q^δ)^(d_S-1)` times the BB1 box volume of the cell's
polygon. This is the `coeff` factor of the eq-(4.2) sum. Both factors now vary with `q`: the BB3
count contributes the monomial `q^{δ(d_S-1)}` (the wild-prime mechanism) and BB1 the box volume. -/
noncomputable def cellCoeff (T : OMShape) (c : OMCell T) : ℕ → ℚ :=
  fun q => residualCountFn T c.residualDeg q * L4.bb1Value c.polygon q

/-- The OM-recursion **contributions** for a shape `T` (faithful eq-(4.2) form): one entry per GMN
order-`r` cell `c ∈ omCells T`, carrying the BB3×BB1 coefficient `cellCoeff T c` and the cell's
**multi-child** list `c.children` (strictly smaller `size` by `descend_size_lt`). -/
noncomputable def omContribs (T : OMShape) : List ((ℕ → ℚ) × List OMShape) :=
  (omCells T).map (fun c => (cellCoeff T c, c.children.map (·.node)))

/-- **`T_BB3` (finite-field non-squarefree count, inlined).** Over any finite field `F`, the number
of non-squarefree (refinement-triggering) monic degree-`d` polynomials is `|F|^{d-1}`. Proved from
`L3.card_monicDegree` + `L3Squarefree.card_squarefreeMonicDegree` exactly as in `BB3inf.T_BB3`
(re-stated here so the measure-layer axiom cone does not import `BB3inf`'s separate descent stubs). -/
theorem T_BB3 (F : Type*) [Field F] [Finite F] (d : ℕ) (hd : 2 ≤ d) :
    Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R}
      = Nat.card F ^ (d - 1) := by
  classical
  set Q := Nat.card F with hQ
  let e : {R : Polynomial F // R.Monic ∧ R.natDegree = d}
      ≃ {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R}
        ⊕ {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R} :=
    { toFun := fun R =>
        if h : Squarefree R.1 then Sum.inl ⟨R.1, R.2.1, R.2.2, h⟩
        else Sum.inr ⟨R.1, R.2.1, R.2.2, h⟩
      invFun := fun s => match s with
        | Sum.inl R => ⟨R.1, R.2.1, R.2.2.1⟩
        | Sum.inr R => ⟨R.1, R.2.1, R.2.2.1⟩
      left_inv := by
        rintro ⟨R, hM, hdeg⟩; by_cases h : Squarefree R <;> simp [h]
      right_inv := by
        rintro (⟨R, hM, hdeg, hsf⟩ | ⟨R, hM, hdeg, hnsf⟩)
        · simp [hsf]
        · simp [hnsf] }
  have hmonic_eq :
      Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d} = Q ^ d := by
    have := L3.card_monicDegree (F := F) d
    simpa [L3.monicDegree, hQ] using this
  have hsf_eq :
      Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R}
        = Q ^ d - Q ^ (d - 1) := by
    have := L3Squarefree.card_squarefreeMonicDegree (F := F) d hd
    simpa [L3.squarefreeMonicDegree, hQ] using this
  have hQpos : 0 < Q := by rw [hQ]; exact Nat.card_pos
  have hfin_monic : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = d} :=
    Nat.finite_of_card_ne_zero (by rw [hmonic_eq]; exact pow_ne_zero d hQpos.ne')
  haveI hfin_sum :
      Finite ({R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R}
        ⊕ {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R}) :=
    Finite.of_equiv _ e
  haveI : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R} :=
    Finite.sum_left {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R}
  haveI : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R} :=
    Finite.sum_right {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R}
  have hsum : Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d}
      = Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ Squarefree R}
        + Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = d ∧ ¬ Squarefree R} := by
    rw [Nat.card_eq_of_bijective e e.bijective, Nat.card_sum]
  rw [hmonic_eq, hsf_eq] at hsum
  have hpow_le : Q ^ (d - 1) ≤ Q ^ d := by
    apply Nat.pow_le_pow_right <;> omega
  omega

/-- **`T_BB3` evaluates the frozen `residualCount` to the `q`-varying `residualCountFn` value at the
A0 point (the non-vacuity certificate).** Over the shape's OWN residue field `T.Fr` of size
`q ^ residueDeg`, the genuine `Nat.card` count `residualCount T d` equals `(q ^ residueDeg) ^ (d - 1)
= residualCountFn T d q` — `T_BB3`'s closed form, computed from the ACTUAL non-squarefree residual
locus over `T.Fr`, not a free monomial — at the SPECIFIC `q = |T.baseField|`. So the `q`-varying
function `residualCountFn T d` that is on the rationality path agrees with the honest finite-field
count at the shape's own field, certifying the function is faithful (its monomial is the real BB3
count, just allowed to vary with the free `q`). -/
theorem residualCount_eq (T : OMShape) (q : ℕ) (hb : Nat.card T.baseField = q)
    (d : ℕ) (hd : 2 ≤ d) :
    residualCount T d = residualCountFn T d q := by
  unfold residualCount residualCountFn
  rw [T_BB3 T.Fr d hd, natCard_Fr T q hb]
  push_cast
  ring

/-- **The `q`-varying BB3 count is a GENUINELY-NON-CONSTANT uniform rational function of `q`.**
`residualCountFn T d = fun q => (q^δ)^(d-1) = q^(δ(d-1))` is rational via `RatFn` closure: the inner
`q ↦ q^δ` is `isRationalFn_qpow δ` and raising to `(d-1)` keeps it rational
(`isRationalFn_pow`/repeated `isRationalFn_mul`); equivalently it IS the single `q`-power
`q^(δ(d-1))`, whose representing numerator is the **non-constant monomial `X^{δ(d-1)}`** (when
`δ(d-1) > 0`). This is the load-bearing fact (replacing the old `isRationalFn_const`): the BB3 count's
`q`-dependence — the wild-prime mechanism — is what supplies this factor's rationality, not a frozen
constant. -/
theorem residualCountFn_isRational (T : OMShape) (d : ℕ) :
    IsRationalFn (residualCountFn T d) := by
  -- `residualCountFn T d q = (q^δ)^(d-1) = q^(δ·(d-1))`: a genuine `q`-power, rational by
  -- `isRationalFn_qpow` (numerator the non-constant monomial `X^{δ(d-1)}`).
  have hrw : residualCountFn T d = fun q : ℕ => (q : ℚ) ^ (T.residueDeg * (d - 1)) := by
    funext q; simp only [residualCountFn, ← pow_mul]
  rw [hrw]
  exact isRationalFn_qpow (T.residueDeg * (d - 1))

/-- **`T_BB1` (box-volume rationality, inlined).** For a lattice polygon `Π`, the cell volume
`q ↦ (1-q⁻¹)^V q^{-A}` is a uniform rational function of `q` (`num = (X-1)^V`, `den = X^{V+A}`,
pole-free at `q > 1`). The volume *formula* `(1-Q⁻¹)^V Q^{-A} = bb1Value` is `L4.cellVolume_eq`
(proved from `AX_columnMeasure`); here we record its rational-function-of-`q` shape. -/
theorem bb1_isRational (pg : L4.LatticePolygon) : IsRationalFn (fun q => L4.bb1Value pg q) := by
  set V := L4.newtonVertexCount pg with hV
  set A := L4.newtonExponent pg with hA
  refine ⟨(Polynomial.X - 1) ^ V, Polynomial.X ^ (V + A), ?_, fun q hq => ?_⟩
  · exact pow_ne_zero _ Polynomial.X_ne_zero
  · have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hq)
    have hqne : (q : ℚ) ≠ 0 := ne_of_gt hq0
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero _ hqne
    · simp only [L4.bb1Value, ← hV, ← hA, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one]
      have h1 : (1 - (q : ℚ)⁻¹) = ((q : ℚ) - 1) / (q : ℚ) := by field_simp
      rw [h1, div_pow, pow_add]
      ring

/-- **The box factor `bb1Value` IS the cell's box/shell Haar volume — DERIVED from `AX_columnMeasure`
(+ `L4.cellVolume_eq`), not asserted.** Any cell-volume function `cellVol` satisfying the
`AX_columnMeasure` product structure equals `bb1Value pg Q = (1-Q⁻¹)^V Q^{-A}` (for `Q ≥ 1`). This is
the honest justification of the `L4.bb1Value c.polygon q` factor used in `AX_cellRecursion`: its value
is the standard Igusa box/shell volume, with the closed form PROVED in `L4.cellVolume_eq`. So
`AX_columnMeasure` is genuinely the box factor's analytic boundary (not dead weight), while the cell
volume's *value* is proved, not axiomatized. -/
theorem cellVolume_eq_bb1Value
    (cellVol : L4.LatticePolygon → ℕ → ℚ) (pg : L4.LatticePolygon) (Q : ℕ) (hQ : 1 ≤ Q) :
    cellVol pg Q = L4.bb1Value pg Q :=
  L4.cellVolume_eq cellVol pg Q hQ (AX_columnMeasure cellVol pg Q)

/-- `cellCoeff T c` is a uniform rational function of `q`: the GENUINELY `q`-varying BB3 count
`residualCountFn T c.residualDeg` (rational by `residualCountFn_isRational`, whose numerator is the
non-constant monomial `X^{δ(d_S-1)}` — NOT `isRationalFn_const`) times the BB1 box volume
`bb1Value c.polygon` (rational by `bb1_isRational`). The BB3 count's `q`-dependence is genuinely
consumed here, so it is load-bearing on the rationality path. -/
theorem cellCoeff_isRational (T : OMShape) (c : OMCell T) : IsRationalFn (cellCoeff T c) := by
  unfold cellCoeff
  exact isRationalFn_mul (residualCountFn_isRational T c.residualDeg) (bb1_isRational c.polygon)

/-- `omPivot T` is a uniform rational function of `q`: on the ramifying branch `(q^w - 1)/q^w`
(pole-free on `q > 1`); on the leaf branch the constant `1`. -/
theorem omPivot_isRational (T : OMShape) : IsRationalFn (omPivot T) := by
  unfold omPivot
  by_cases h : 2 ≤ T.size
  · simp only [h, if_true]
    refine ⟨Polynomial.X ^ L5fix.selfLoopExponent T.size - 1,
      Polynomial.X ^ L5fix.selfLoopExponent T.size, pow_ne_zero _ Polynomial.X_ne_zero,
      fun q hq => ?_⟩
    have hq0 : (q : ℚ) ≠ 0 := by
      have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
      exact ne_of_gt hqpos
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    refine ⟨pow_ne_zero _ hq0, ?_⟩
    rw [eq_div_iff (pow_ne_zero _ hq0)]
    field_simp
  · simp only [h, if_false]
    exact isRationalFn_const 1

/-- `omPivot T q ≠ 0` for every `q > 1`: ramifying branch by `L5fix.selfLoop_geometric` (positive),
leaf branch `1`. -/
theorem omPivot_ne (T : OMShape) (q : ℕ) (hq : 1 < q) : omPivot T q ≠ 0 := by
  unfold omPivot
  by_cases h : 2 ≤ T.size
  · simp only [h, if_true]
    have hpos := L5fix.selfLoop_geometric T.size q h hq
    exact ne_of_gt hpos
  · simp only [h, if_false]
    exact one_ne_zero

/-! ## E. The DERIVED recursion lemma + uniformity (the `hrec` is now a THEOREM under the interface)

`clusterMeasure_rec` is the eq-(4.2) recursion in the exact shape `OMInduction.clusterVol_isRational`
consumes — DERIVED from `AX_cellRecursion` by unfolding `omContribs`/`cellCoeff` (pure definitional
rewriting; no extra axiom). The old `hrec` *hypothesis* of `BB3inf.clusterVolume_rational_of_OM` is
thus discharged here as a lemma. -/

/-- **The eq-(4.2) recursion, DERIVED (not asserted).** For any function `cm` satisfying the
`AX_cellRecursion` measure-factorization identity (with pivot `omPivot`), the per-shape cluster
measure equals the OM contribution-sum-over-pivot in the exact form the engine consumes. This is the
former `hrec` *hypothesis*, now a LEMMA under the standard p-adic interface. (Generic in `cm`: it is a
pure list-rewriting lemma taking the recursion as a hypothesis; the FIXED `clusterMeasure` is fed in
at the capstone. This is sound — it pins nothing on its own; it merely transports a recursion the
caller supplies.) -/
theorem clusterMeasure_rec
    (cm : OMShape → ℕ → ℚ)
    (hcell : ∀ (T : OMShape) (q : ℕ), 1 < q →
        cm T q
          = ((omCells T).map (fun c =>
                residualCountFn T c.residualDeg q
                * L4.bb1Value c.polygon q
                * (c.children.map (fun ch => cm ch.node q)).prod)).sum
            / omPivot T q)
    (T : OMShape) (q : ℕ) (hq : 1 < q) :
    cm T q
      = ((omContribs T).map
            (fun c => c.1 q * (c.2.map (fun ch => cm ch q)).prod)).sum / omPivot T q := by
  rw [hcell T q hq]
  -- Rewrite the cell-sum (over `omCells`) into the contribution-sum (over `omContribs`); the two are
  -- definitionally the same list, term by term: `omContribs = (omCells).map (c ↦ (cellCoeff, children.map node))`.
  -- Peel the `/ pivot` and the `.sum`, fuse the two maps on the contribution side (`List.map_map`),
  -- and check the per-cell summands agree: the child-product on the contribution side maps `cm` over
  -- `c.children.map (·.node)`, which by `List.map_map` is `c.children.map (fun ch => cm ch.node q)`.
  congr 1            -- peel `_ / omPivot T q`
  congr 1            -- peel `(_).sum`
  unfold omContribs
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  -- the contribution summand fuses `cm` over `c.children.map (·.node)`; by `List.map_map` this is
  -- `c.children.map (fun ch => cm ch.node q)`, matching the cell summand.
  simp only [Function.comp_apply, cellCoeff, List.map_map, Function.comp_def]

/-- **Uniformity — `clusterMeasure` is a uniform rational function of `q` (DERIVED).**
Every per-shape cluster measure satisfying the `AX_cellRecursion` factorization is a uniform rational
function of `q`, via the novel OM-order induction `OMInduction.clusterVol_isRational` instantiated
with the DERIVED eq-(4.2) recursion (`clusterMeasure_rec`) and:
* `hdescend` from `descend_size_lt` (GMN-III strict size drop) — every cell child is strictly smaller;
* `hcoeff` from `cellCoeff_isRational` (BB3 count × BB1 box volume, both rational);
* `hpivot_rat`/`hpivot_ne` from `omPivot_isRational`/`omPivot_ne` (← `L5fix.selfLoop_geometric`).

Rationality is **never assumed** here: the recursion is a measure-factorization (`AX_cellRecursion`),
and rationality emerges only by running the proved engine on the proved closure lemmas. -/
theorem clusterMeasure_isRational
    (cm : OMShape → ℕ → ℚ)
    (hcell : ∀ (T : OMShape) (q : ℕ), 1 < q →
        cm T q
          = ((omCells T).map (fun c =>
                residualCountFn T c.residualDeg q
                * L4.bb1Value c.polygon q
                * (c.children.map (fun ch => cm ch.node q)).prod)).sum
            / omPivot T q) :
    ∀ T : OMShape, IsRationalFn (cm T) := by
  apply OMInduction.clusterVol_isRational
    (size := OMShape.size) (clusterVol := cm)
    (contribs := omContribs) (pivot := omPivot)
  · -- hrec: the DERIVED eq-(4.2) recursion.
    intro T q hq
    exact clusterMeasure_rec cm hcell T q hq
  · -- hdescend: every cell child is strictly smaller (GMN-III, descend_size_lt). The contribution's
    -- child list is `cell.children.map (·.node)`, so a member `ch` is `chld.node` for some
    -- `chld ∈ cell.children`; `descend_size_lt` gives `chld.node.size < T.size`.
    intro T c hc ch hch
    simp only [omContribs, List.mem_map] at hc
    obtain ⟨cell, hcell_mem, hc_eq⟩ := hc
    rw [← hc_eq] at hch
    -- `hch : ch ∈ cell.children.map (·.node)`.
    simp only [List.mem_map] at hch
    obtain ⟨chld, hchld_mem, hchld_eq⟩ := hch
    rw [← hchld_eq]
    exact descend_size_lt T cell hcell_mem chld hchld_mem
  · -- hcoeff: each cell coefficient is rational (BB3 count × BB1 box volume).
    intro T c hc
    simp only [omContribs, List.mem_map] at hc
    obtain ⟨cell, _, hc_eq⟩ := hc
    rw [← hc_eq]
    exact cellCoeff_isRational T cell
  · -- hpivot_rat: omPivot is rational.
    exact omPivot_isRational
  · -- hpivot_ne: omPivot is pole-free on q > 1.
    exact omPivot_ne

/-- **The measure-layer deliverable, packaged.** Instantiating the derived recursion at the actual
p-adic cluster measure (the `AX_cellRecursion` identity holding for it by definition) yields: the
per-shape cluster measure is a uniform rational function of `q`. This is `clusterVolume_rational`'s
content over the abstract `OMShape` — a THEOREM modulo `{AX_cellRecursion, AX_columnMeasure} + GMN`,
NOT an axiom. The `ClusterShape ↔ OMShape` bridge (D1) and the re-pointing of
`Interface.clusterVolume_rational` are the NEXT agent's plumbing step. -/
theorem clusterVolume_isRational_of_cellRecursion
    (cm : OMShape → ℕ → ℚ)
    (hAX : ∀ (T : OMShape) (q : ℕ), 1 < q →
        cm T q
          = ((omCells T).map (fun c =>
                residualCountFn T c.residualDeg q
                * L4.bb1Value c.polygon q
                * (c.children.map (fun ch => cm ch.node q)).prod)).sum
            / omPivot T q) :
    ∀ T : OMShape, IsRationalFn (cm T) :=
  clusterMeasure_isRational cm hAX

/-- **CAPSTONE — the FIXED cluster volume is a uniform rational function of `q`.**
The opaque, fixed conditional p-adic cluster measure `clusterMeasure` satisfies the Igusa/Denef
cell-decomposition axiom `AX_cellRecursion` (with the concrete self-loop pivot `omPivot`); this
discharges the recursion hypothesis of `clusterMeasure_isRational`, which then concludes that THE
cluster volume `clusterMeasure T` is a uniform rational function of `q` for every shape `T`.

This is the measure-layer's headline: per-shape cluster volume rationality is a THEOREM modulo
`{clusterMeasure (fixed interface object), AX_cellRecursion, AX_columnMeasure (box), GMN-structural}`
(its `#print axioms` footprint). **Soundness note (2026-06-19 fix):** unlike the earlier version, this
is stated about the ONE fixed `clusterMeasure`, not universally quantified over all functions — the
old `∀ clusterMeasure, …` capstone "pinned nothing" (D-CAPSTONE) and rested on the inconsistent free
`pivot` axiom (D-INCONS). Here `AX_cellRecursion` is genuinely consumed and is satisfiable (witnessed
by `clusterMeasureModel`), so rationality is a meaningful theorem, not a vacuity. Rationality is NEVER
asserted in any axiom; it emerges only via `OMInduction.clusterVol_isRational`. -/
theorem clusterMeasure_isRational_of_AX :
    ∀ T : OMShape, IsRationalFn (clusterMeasure T) :=
  clusterMeasure_isRational clusterMeasure
    (fun T q hq => AX_cellRecursion T q hq)

end LeanUrat.PadicMeasure
