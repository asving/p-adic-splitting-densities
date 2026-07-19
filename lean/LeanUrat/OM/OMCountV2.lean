/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MontesAxiom
import LeanUrat.RatFn
import LeanUrat.L4
import LeanUrat.OM.Order0
import LeanUrat.OM.Order0Capstone
import LeanUrat.OM.Order0Alpha

/-!
# OMCountV2 — Phase-B Layer C (PIN step R1): the corrected per-node counting recursion

**Provenance.** `notes/PIN_ARCHITECTURE_BLUEPRINT.md` §1.2–§1.3 (step R1, §3), with the R0
ERRATA (2026-07-04, BINDING) transcribed from the gated harness
`/workspace-vast/asving/tmp/phaseb_r0/harness.py` (69/69 exact rows in
`/workspace-vast/asving/tmp/phaseb_r0/results.txt`):

* **E1** — at a CLUSTER node the box exponent is `B = newtonExponent + Σ_F d_F − s`
  (`s` = the node's cluster size); the root keeps `B = newtonExponent + Σ_F d_F`.
* **E2** — faces carry a puncture flag: `avail₁ = Q − 1` on a genuine (strict-polygon /
  a₀-unit-conditioned) face, `avail₁ = Q` on an unpunctured face (the unconditioned root face of
  a full stratum and the all-descend rescale face of a cluster node). `FaceAssign.punctured`
  is the E2 extension of the PIN §1.2 field list (the PIN structures predate the erratum).
* **E3** — the cluster config census (strict polygons of rightmost slope `< 1` plus one-step
  rescale configs; slope-≥1 only inside the `countPivot` self-loop) is CLASSIFIER territory:
  it constrains which `NodeConfig`s the Phase-B classifier may emit, not the evaluator below.

**The two-function recursion** (PIN §1.2, D4 pivot placement):

    omCount T q      = Σ_{c ∈ configsOf T} m_cell(c,q) · q^{−B(c)} · ∏_{ch} omChildCount ch.shape (q^{δ·D})
    omChildCount T q = [same sum, with B(c) − treeSize T] / countPivot (treeSize T) q

The pivot argument is the node's OWN subtree size, evaluated at the node's base-changed `Q`
(both R0-pinned). `countPivot` is unchanged (`MontesAxiom.countPivot`, `L5fix.selfLoopExponent`).

**The V2 payload reader `configsOf`.** The current one-`CountCell`-per-factor payload encodes
ONE configuration per node (PIN D3): one shared polygon/face, one `(D, μ)` entry per factor-cell
(`μ` read back from the child-size slots: `μ·D = Σ child sizes`, `μ = 1` for a leaf cell), the
full face residual degree `d_F = Σ_cells μ·D`, and one `ChildData` per payload child with
`D` = the paired factor degree. Every payload-read face is GENUINE (punctured): the Phase-A
classifier emits only the a₀-unit-conditioned `sepShape` strata (SIGMA-1) and genuine
strict-polygon cluster faces (e.g. the slope-−1/2 family); unpunctured (root-unconditioned /
E2-rescale) faces enter only with the Phase-B classifier's richer emissions, through the
`punctured := false` menu case that `FaceAssign` already supports. `CountCell` is untouched;
the reader goes through the WF-guarded `M7.cellsOfShapeWF` (descent provable for EVERY shape,
identity on genuine emissions — the Phase-A A4 pattern).

**Compatibility (PIN D3, the required transfer lemma).** `omCount_sepShape_eq_rootCount`:
on the Phase-A menu the V2 evaluator IS `Order0.rootCount`, so every Phase-A theorem
(in particular `h_node0_proved`) transfers by rewriting.

**Gates run in this file** (audit §2 items 3/5/6/7; exact fractions vs `results.txt`):
CAL-p rows n=2 λ=(1,1)/(2) at q=2,3 and n=3 λ=(1,2) at q=2; the C1-fam cluster rows
(slope-−1/2 size-2 cluster family: 2/3 at q=2, 3/4 at q=3); positivity + correctly-empty
(gate 5); σ-separation 1/9 vs 1/3 at n=2, q=3 (gate 6); off-menu junk shapes (gate 7).

**m×C split (PIN §1.3)** stated on `omMenu` membership only (the honest scope: the split is
exact on one-configuration-per-node shapes; the current reader emits exactly one configuration,
and the R1 menu is the order-0 slice).

TODO (Phase-B / R3, banked): extend `omMenu` beyond the order-0 slice with classifier-emitted
deeper shapes (`typeOf`-keyed, GMNNodeEfLaw-shaped); at that point revisit the puncture reading
(E2 faces off the payload) and, if multi-configuration nodes appear, restate `omCount_eq_mul`'s
scope. The recursive (per-node-product) refinement of `omMultiplicity`/`omVolume` is deferred
with it — on the R1 menu both agree with the PIN §1.3 order-0 values.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.OMCountV2

open LeanUrat LeanUrat.MontesAxiom LeanUrat.RatFn Polynomial
open LeanUrat.OM LeanUrat.OM.Order0

/-! ## 1. The V2 configuration data (PIN §1.2 structures + the E2 puncture flag) -/

/-- **A face assignment** (PIN §1.2 `FaceAssign` + the E2 erratum flag): one Newton-polygon face
of one node configuration, carrying its residue-extension degree `δ`, its residual-shape multiset
`shape` (one `(D, μ)` entry per residual factor: degree `D`, multiplicity `μ`), its FULL residual
digit count `dF = Σ μ·D` (μ ≥ 2 factors included — R0-pinned convention), and the E2 puncture
flag (`punctured = true`: the linear pool is `Q − 1`; `false`: the unpunctured pool `Q` of the
unconditioned-root / rescale faces). Pure data; no payload. -/
structure FaceAssign where
  /-- residue-extension degree of this face. -/
  δ : ℕ
  /-- the `(D, μ)` residual-shape multiset on this face. -/
  shape : List (ℕ × ℕ)
  /-- the face's FULL residual digit count `d_F = Σ μ·D` (§2.6: `B = newtonExponent + Σ_F d_F`). -/
  dF : ℕ
  /-- E2 (R0 erratum): `true` = genuine face (`avail₁ = Q − 1`), `false` = unpunctured
  (unconditioned root / rescale) face (`avail₁ = Q`). -/
  punctured : Bool
  deriving DecidableEq

/-- **A descent-child datum** (PIN §1.2 `ChildData`): the child shape, the parent face's `δ`, and
the degree `D` of the paired (μ ≥ 2) residual factor — the child is evaluated at the base-changed
`q ↦ q^{δ·D}` (§2.6 last bullet). -/
structure ChildData where
  /-- the descent child (paired to a `μ ≥ 2` factor). -/
  shape : ClusterShape
  /-- parent face `δ_F`. -/
  δ : ℕ
  /-- degree of the paired factor (base change `q ↦ q^{δ·D}`). -/
  D : ℕ

/-- `DecidableEq` for `ChildData` (classical, as for the `ClusterShape` it carries). -/
noncomputable instance : DecidableEq ChildData := Classical.decEq _

/-- **A per-node configuration** (PIN §1.2 `NodeConfig`, the D3 unit): ONE entry per
(polygon × full residual-shape assignment) — the polygon, its faces, and the descent children. -/
structure NodeConfig where
  /-- the configuration's lattice Newton polygon. -/
  polygon : L4.LatticePolygon
  /-- the face assignments (one per finite-slope face). -/
  faces : List FaceAssign
  /-- the descent children of this configuration. -/
  children : List ChildData

/-- `DecidableEq` for `NodeConfig` (classical: `L4.LatticePolygon` carries function fields). -/
noncomputable instance : DecidableEq NodeConfig := Classical.decEq _

/-! ## 2. The choice-count polynomial of a face (the harness `NS`, per-(D,μ) symmetry) -/

/-- The degree-`d` residual-factor pool polynomial with the E2 puncture flag: punctured faces use
the Phase-A `Order0.availPoly` (`X − 1` at `d = 1`, necklace `M_d` at `d ≥ 2`); unpunctured faces
use the FULL linear pool `X` at `d = 1` (residue `0` allowed) and the same necklace at `d ≥ 2`. -/
noncomputable def poolPoly : Bool → ℕ → Polynomial ℚ
  | true, d => availPoly d
  | false, d => if d = 1 then Polynomial.X else necklacePoly d

/-- The multiplicity list of the degree-`d` factors of a face shape (the harness `mus`). -/
def faceMus (shape : List (ℕ × ℕ)) (d : ℕ) : List ℕ :=
  (shape.filter (fun p => p.1 == d)).map Prod.snd

/-- The per-degree symmetry factor: factors of equal degree AND equal multiplicity are
unordered among themselves — `∏_{μ} c_{d,μ}!` over the distinct multiplicities `μ` of the
degree-`d` factors (the harness `sym`; all-μ-equal-1 case: `k_d!`, the Phase-A convention). -/
def symFactor (shape : List (ℕ × ℕ)) (d : ℕ) : ℕ :=
  ((faceMus shape d).toFinset).prod (fun μ => ((faceMus shape d).count μ).factorial)

/-- **The face choice-count polynomial** (the harness `NS`, §2.6 `N_S`, `Order0.nodeChoicePoly`
generalized per-face): for each distinct factor degree `d`, `ff(pool_d, k_d)/sym_d` — ordered
distinct choices of the `k_d` degree-`d` factors from the pool, divided by the per-(d,μ)
symmetry factor. In the face variable `Q = q^δ`. -/
noncomputable def choicePoly (punctured : Bool) (shape : List (ℕ × ℕ)) : Polynomial ℚ :=
  ∏ d ∈ (shape.map Prod.fst).toFinset,
    Polynomial.C (1 / (symFactor shape d : ℚ))
      * ffPoly (poolPoly punctured d) ((shape.map Prod.fst).count d)

/-- On an all-multiplicity-1 shape the face choice polynomial is EXACTLY the Phase-A per-degree
`ff(avail_d, k_d)/k_d!` product (the `Order0.nodeChoicePoly` body): the μ-grouped symmetry factor
collapses to `k_d!`. This is the polynomial half of the D3 compatibility lemma. -/
theorem choicePoly_map_one (ds : List ℕ) :
    choicePoly true (ds.map (fun d => (d, 1)))
      = ∏ d ∈ ds.toFinset,
          Polynomial.C (1 / ((ds.count d).factorial : ℚ))
            * ffPoly (availPoly d) (ds.count d) := by
  have hfst : (ds.map (fun d => (d, 1))).map Prod.fst = ds := by
    rw [List.map_map]
    exact List.map_id'' (fun d => rfl) ds
  have hmus : ∀ d : ℕ, faceMus (ds.map (fun d => (d, 1))) d
      = List.replicate (ds.count d) 1 := by
    intro d
    unfold faceMus
    rw [List.filter_map, List.map_map]
    have hpred : ((fun p : ℕ × ℕ => p.1 == d) ∘ (fun d' : ℕ => (d', 1))) = (fun d' => d' == d) := rfl
    rw [hpred]
    have hsnd : (Prod.snd ∘ (fun d' : ℕ => ((d', 1) : ℕ × ℕ))) = fun _ => 1 := rfl
    rw [hsnd, List.map_const']
    congr 1
    rw [List.count_eq_countP, List.countP_eq_length_filter]
  unfold choicePoly
  rw [hfst]
  refine Finset.prod_congr rfl fun d hd => ?_
  have hk : ds.count d ≠ 0 := by
    rw [Ne, List.count_eq_zero]
    exact fun h => h (List.mem_toFinset.mp hd)
  have hsym : symFactor (ds.map (fun d => (d, 1))) d = (ds.count d).factorial := by
    unfold symFactor
    rw [hmus d, List.toFinset_replicate_of_ne_zero hk, Finset.prod_singleton,
      List.count_replicate_self]
  rw [hsym]
  rfl

/-! ## 3. The V2 payload reader `configsOf` -/

/-- The empty lattice polygon (width 0; the polygon slot of an empty-payload node). Its
`newtonExponent` is `0`. -/
def emptyPolygon : L4.LatticePolygon :=
  ⟨0, fun i => i.elim0, fun i => i.elim0⟩

theorem newtonExponent_emptyPolygon : L4.newtonExponent emptyPolygon = 0 := rfl

/-- The multiplicity `μ` of a payload cell's residual factor, read back from the child-size
slots (`childSize = μ·deg ψ` is the M5 encoder invariant, so `μ = (Σ child sizes)/dS`); `1` for
a leaf (childless) cell. Reader convention — meaningful on encoder/classifier-emitted payloads,
unconstrained on junk (gate 7). -/
def cellMult (c : CountCell) : ℕ :=
  if c.children.isEmpty then 1 else (c.children.map M5.nodeSizeOf).sum / c.dS

/-- The payload cell's contribution `μ·D` to the FULL face residual degree `d_F` (R0-pinned:
μ ≥ 2 factors count with multiplicity): `dS` for a leaf cell, the child-size sum (`= μ·dS`)
for a descent cell. -/
def cellResDeg (c : CountCell) : ℕ :=
  if c.children.isEmpty then c.dS else (c.children.map M5.nodeSizeOf).sum

/-- **The single configuration encoded by the current payload** (PIN D3: one-`CountCell`-per-factor
= ONE configuration): the shared polygon (head cell; all cells of one node share the selected
side), ONE genuine (punctured) face carrying the `(D, μ)` multiset and the full `d_F`, and one
`ChildData` per payload child (`D` = the paired factor degree `dS`). Read through the WF-guarded
`M7.cellsOfShapeWF` (descent provable for every shape; identity on genuine emissions). -/
noncomputable def configOf (T : ClusterShape) : NodeConfig :=
  { polygon := (((M7.cellsOfShapeWF T).head?).map CountCell.polygon).getD emptyPolygon
    faces := [{ δ := nodeDelta (M7.cellsOfShapeWF T)
                shape := (M7.cellsOfShapeWF T).map (fun c => (c.dS, cellMult c))
                dF := ((M7.cellsOfShapeWF T).map cellResDeg).sum
                punctured := true }]
    children := (M7.cellsOfShapeWF T).flatMap (fun c =>
      c.children.map (fun ch =>
        ({ shape := ch, δ := nodeDelta (M7.cellsOfShapeWF T), D := c.dS } : ChildData))) }

/-- **The V2 payload reader** (PIN §1.2): the configuration list of a node. The current payload
encodes exactly ONE configuration (D3); multi-configuration nodes arrive with the Phase-B
classifier emissions. Additive: `CountCell` untouched. -/
noncomputable def configsOf (T : ClusterShape) : List NodeConfig := [configOf T]

/-- **Strict descent through the reader**: every `ChildData` of every configuration of every
shape strictly decreases `M6.treeSize` — no axiom; the witness is carried by the
`M7.cellsOfShapeWF` filter (`cellsOfShapeWF_descend`). This is the termination input of
`omChildCount`. -/
theorem configsOf_descend :
    ∀ (T : ClusterShape), ∀ c ∈ configsOf T, ∀ ch ∈ c.children,
      M6.treeSize ch.shape < M6.treeSize T := by
  intro T c hc ch hch
  have hc' : c = configOf T := by
    simpa [configsOf] using hc
  subst hc'
  simp only [configOf, List.mem_flatMap, List.mem_map] at hch
  obtain ⟨cc, hcc, ch', hch', rfl⟩ := hch
  exact M7.cellsOfShapeWF_descend T cc hcc ch' hch'

/-! ## 4. The evaluator: `mCell`, `volExp`, `omChildCount`, `omCount` -/

/-- **The per-configuration choice count** `m_cell(c, q) = ∏_F N_{S_F}(q^{δ_F})` (§2.6): the
product over the faces of the face choice polynomial evaluated at the face variable `q^δ`. -/
noncomputable def mCell (c : NodeConfig) (q : ℕ) : ℚ :=
  (c.faces.map (fun F => (choicePoly F.punctured F.shape).eval ((q : ℚ) ^ F.δ))).prod

/-- **The ROOT-node box-volume exponent** `B(c) = newtonExponent(polygon) + Σ_F d_F` (§2.6; the
pure lattice exponent, NO `(1−q⁻¹)^V` factor — D2). At CLUSTER nodes the E1 erratum subtracts
the node's cluster size `s` (`omChildCount` below applies `volExp c − treeSize T`; ℕ-truncated,
nonnegative on genuine cluster shapes — the harness asserts `B ≥ 0` on all 69 gated rows). -/
def volExp (c : NodeConfig) : ℕ :=
  L4.newtonExponent c.polygon + (c.faces.map FaceAssign.dF).sum

/-- **The CLUSTER-node count** (PIN §1.2, D4: pivot HERE, never at the root; E1: the `− s`
cluster normalization). Evaluated at the node's base-changed `Q` (the caller passes `q^{δ·D}`);
the pivot argument is the node's OWN subtree size at that same `Q` (R0-pinned). Well-founded
recursion on `M6.treeSize` via `configsOf_descend` (structural recursion cannot see the payload
subterms through the `configsOf` reader — the sanctioned treeSize fallback; no descent axiom). -/
noncomputable def omChildCount (T : ClusterShape) (q : ℕ) : ℚ :=
  (((configsOf T).attach.map (fun c =>
      mCell c.1 q * ((q : ℚ) ^ (volExp c.1 - M6.treeSize T))⁻¹
        * (c.1.children.attach.map (fun ch =>
            omChildCount ch.1.shape (q ^ (ch.1.δ * ch.1.D)))).prod)).sum)
    / countPivot (M6.treeSize T) q
termination_by M6.treeSize T
decreasing_by exact configsOf_descend T c.1 c.2 ch.1 ch.2

/-- The `omChildCount` recursion-unfold lemma (the two `attach`es only carry membership proofs). -/
theorem omChildCount_rec (T : ClusterShape) (q : ℕ) :
    omChildCount T q
      = (((configsOf T).map (fun c =>
          mCell c q * ((q : ℚ) ^ (volExp c - M6.treeSize T))⁻¹
            * (c.children.map (fun ch =>
                omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum)
        / countPivot (M6.treeSize T) q := by
  rw [omChildCount]
  congr 1
  congr 1
  have hchildren : ∀ (c : NodeConfig),
      (c.children.attach.map (fun ch => omChildCount ch.1.shape (q ^ (ch.1.δ * ch.1.D))))
        = c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D))) := by
    intro c
    exact List.attach_map_val (l := c.children)
      (f := fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))
  simp only [hchildren]
  exact List.attach_map_val (l := configsOf T)
    (f := fun c => mCell c q * ((q : ℚ) ^ (volExp c - M6.treeSize T))⁻¹
      * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)

/-- **The ROOT count** (PIN §1.2, D4: NO pivot at the root, NO `− s`): the §2.6 boxed formula's
root case, children evaluated by the cluster recursion at the base-changed `q^{δ·D}`. -/
noncomputable def omCount (T : ClusterShape) (q : ℕ) : ℚ :=
  ((configsOf T).map (fun c =>
    mCell c q * ((q : ℚ) ^ volExp c)⁻¹
      * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum

/-! ## 5. The menu and the density -/

/-- **The σ-keyed Phase-B menu.** At R1 this IS the order-0 slice `sepShapesOf n σ`
(`Order0Capstone`); the Phase-B classifier waves extend it with the deeper decided shapes
(`typeOf T = σ` read off the payload — the `GMNNodeEfLaw` shape, never re-axiomatized over a
free `M5.OMType`). σ enters ONLY through the menu (the O1 lesson; gate 6 below). -/
noncomputable def omMenu (n : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  sepShapesOf n σ

/-- The order-0 slice of the menu is the Phase-A separable menu (definitional at R1). -/
theorem omMenu_order0 (n : ℕ) (σ : FactorizationType) : omMenu n σ = sepShapesOf n σ := rfl

/-- **The V2 density** (PIN §1.2): the σ-keyed menu sum of the corrected per-shape counts. -/
noncomputable def omDensityV2 (n : ℕ) (σ : FactorizationType) (q : ℕ) : ℚ :=
  ∑ T ∈ omMenu n σ, omCount T q

/-! ## 6. THE COMPATIBILITY LEMMA (PIN D3): the V2 evaluator restricts to `rootCount` -/

/-- On the `sepShape` payload the reader's face shape is the all-multiplicity-1 list of the
sorted parts. -/
theorem configShape_sepShape (n : ℕ) (lam : Nat.Partition n) :
    (M7.cellsOfShapeWF (sepShape n lam)).map (fun c => (c.dS, cellMult c))
      = (lam.parts.sort (· ≤ ·)).map (fun d => (d, 1)) := by
  rw [cellsOfShapeWF_sepShape, List.map_map]
  refine List.map_congr_left fun d _ => ?_
  simp [cellMult]

/-- The reader's face choice polynomial on the `sepShape` payload IS `Order0.nodeChoicePoly`. -/
theorem choicePoly_sepShape (n : ℕ) (lam : Nat.Partition n) :
    choicePoly true ((M7.cellsOfShapeWF (sepShape n lam)).map (fun c => (c.dS, cellMult c)))
      = nodeChoicePoly (M7.cellsOfShapeWF (sepShape n lam)) := by
  rw [configShape_sepShape, choicePoly_map_one]
  unfold nodeChoicePoly
  rw [dSList_sepShape]

/-- The reader's volume exponent on the `sepShape` payload IS `Order0.nodeVolumeExp` (leaf cells:
`cellResDeg = dS`, and the head polygon is the shared flat face). -/
theorem volExp_sepShape (n : ℕ) (lam : Nat.Partition n) :
    volExp (configOf (sepShape n lam)) = nodeVolumeExp (M7.cellsOfShapeWF (sepShape n lam)) := by
  unfold volExp configOf
  rw [cellsOfShapeWF_sepShape]
  cases hl : lam.parts.sort (· ≤ ·) with
  | nil =>
      simp [nodeVolumeExp, newtonExponent_emptyPolygon]
  | cons a l =>
      simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some,
        List.map_map, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
      unfold nodeVolumeExp
      simp only [dSList, List.map_cons, List.map_map, List.sum_cons]
      have h1 : (cellResDeg ∘ fun d => (⟨d, 1, flatFace n, []⟩ : CountCell)) = fun d => d := by
        funext d; rfl
      have h2 : ((fun c : CountCell => c.dS) ∘ fun d => (⟨d, 1, flatFace n, []⟩ : CountCell))
          = fun d => d := rfl
      rw [h1, h2]
      rfl

/-- **THE COMPATIBILITY LEMMA (PIN D3, REQUIRED).** On the Phase-A order-0 separable menu the
V2 evaluator equals the engine-validated `Order0.rootCount` — every Phase-A theorem (in
particular `h_node0_proved` and `montes_order0_unconditional`'s value tie) transfers to
`omCount` by REWRITING, not re-proving. Holds at every `q` and every `n` (including the
degenerate empty payload, where both sides are `1`). -/
theorem omCount_sepShape_eq_rootCount (n : ℕ) (lam : Nat.Partition n) (q : ℕ) :
    omCount (sepShape n lam) q
      = rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend (sepShape n lam) q := by
  classical
  -- RHS: the children product collapses on the childless menu payload
  rw [rootCount]
  have h1 : ((M7.cellsOfShapeWF (sepShape n lam)).map (fun c =>
      (c.children.map (fun ch =>
        clusterCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend ch q)).prod)).prod
      = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [sepShape_leaf n lam c hc]
    simp
  rw [h1, mul_one]
  -- LHS: unfold the singleton configuration
  rw [omCount]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  -- the reader's children list is empty on the childless payload
  have hflat : (configOf (sepShape n lam)).children = [] := by
    unfold configOf
    simp only
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    rw [sepShape_leaf n lam c hc, List.map_nil]
  rw [hflat]
  simp only [List.map_nil, List.prod_nil, mul_one]
  -- split the choice factor and the volume factor
  have hchoice : mCell (configOf (sepShape n lam)) q
      = (nodeChoicePolyQ (M7.cellsOfShapeWF (sepShape n lam))).eval (q : ℚ) := by
    unfold mCell configOf
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold nodeChoicePolyQ
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, choicePoly_sepShape]
  rw [hchoice, volExp_sepShape]

/-! ## 7. Rationality: the `comp (X^k)` closure and the recursion -/

/-- **Base-change closure of `IsRationalFn`** (PIN §1.2 "Base change"): if `f` is a uniform
rational function of `q` then so is `q ↦ f (q^k)` — representing fraction
`num.comp (X^k) / den.comp (X^k)` (`k = 0` degenerates to the constant `f 1`). This is the
engine addition that keeps the child terms rational IN THE ROOT `q`. -/
theorem isRationalFn_compQpow (k : ℕ) {f : ℕ → ℚ} (hf : IsRationalFn f) :
    IsRationalFn (fun q => f (q ^ k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using isRationalFn_const (f 1)
  · obtain ⟨num, den, hden, h⟩ := hf
    have hcast : ∀ q : ℕ, ((q ^ k : ℕ) : ℚ) = ((q : ℚ)) ^ k := by
      intro q; push_cast; ring
    refine ⟨num.comp (Polynomial.X ^ k), den.comp (Polynomial.X ^ k), ?_, fun q hq => ?_⟩
    · -- nonvanishing at 2^k > 1 forces the composed denominator to be nonzero
      intro h0
      have h2 : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
      apply (h (2 ^ k) h2).1
      have : (den.comp (Polynomial.X ^ k)).eval ((2 : ℕ) : ℚ) = 0 := by rw [h0]; simp
      rwa [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, ← hcast 2] at this
    · have hqk : 1 < q ^ k := Nat.one_lt_pow (by omega) (by omega)
      obtain ⟨hd, hv⟩ := h (q ^ k) hqk
      constructor
      · rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, ← hcast q]
        exact hd
      · show f (q ^ k) = (num.comp (Polynomial.X ^ k)).eval ((q : ℕ) : ℚ)
            / (den.comp (Polynomial.X ^ k)).eval ((q : ℕ) : ℚ)
        simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
        rw [hv, hcast q]

/-- Evaluation of a fixed polynomial at `q^k` is a uniform rational function of `q`
(`num := P.comp (X^k)`, `den := 1`). -/
theorem isRationalFn_polyEvalPow (P : Polynomial ℚ) (k : ℕ) :
    IsRationalFn (fun q : ℕ => P.eval ((q : ℚ) ^ k)) := by
  have heq : (fun q : ℕ => P.eval ((q : ℚ) ^ k))
      = fun q : ℕ => (P.comp (Polynomial.X ^ k)).eval (q : ℚ) := by
    funext q
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  rw [heq]
  exact isRationalFn_polyEval _

/-- The per-configuration choice count is a uniform rational function of `q` (a finite product
of fixed-polynomial evaluations at `q^δ`). -/
theorem mCell_isRational (c : NodeConfig) : IsRationalFn (fun q => mCell c q) := by
  have h := isRationalFn_listProd (c.faces.map (fun F => fun q : ℕ =>
      (choicePoly F.punctured F.shape).eval ((q : ℚ) ^ F.δ))) ?_
  · simpa [mCell, List.map_map, Function.comp_def] using h
  · intro f hf
    rw [List.mem_map] at hf
    obtain ⟨F, _, rfl⟩ := hf
    exact isRationalFn_polyEvalPow _ _

/-- **Rationality of the cluster-node count, in the ROOT `q`** (PIN §1.2 ⚠ subtlety): by
well-founded induction along the recursion — each child term `q ↦ omChildCount ch (q^{δD})` is
rational via `isRationalFn_compQpow` applied to the child's OWN rationality (comp inside the
induction, never after the fact), the pivot divisor is pole-free on `q > 1`
(`countPivot_isRational`/`countPivot_ne`). -/
theorem omChildCount_isRational (T : ClusterShape) :
    IsRationalFn (fun q => omChildCount T q) := by
  suffices h : ∀ (s : ℕ) (T : ClusterShape), M6.treeSize T = s →
      IsRationalFn (fun q => omChildCount T q) from h _ T rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro T hs
    have heq : (fun q => omChildCount T q)
        = fun q => (((configsOf T).map (fun c =>
            mCell c q * ((q : ℚ) ^ (volExp c - M6.treeSize T))⁻¹
              * (c.children.map (fun ch =>
                  omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum)
          / countPivot (M6.treeSize T) q := by
      funext q
      rw [omChildCount_rec]
    rw [heq]
    refine isRationalFn_div ?_ (countPivot_isRational _) (fun q hq => countPivot_ne _ q hq)
    have hsum := isRationalFn_listSum ((configsOf T).map (fun c => fun q : ℕ =>
        mCell c q * ((q : ℚ) ^ (volExp c - M6.treeSize T))⁻¹
          * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)) ?_
    · simpa [List.map_map, Function.comp_def] using hsum
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨c, hc, rfl⟩ := hf
      refine isRationalFn_mul (isRationalFn_mul (mCell_isRational c) (isRationalFn_invQpow _)) ?_
      have hprod := isRationalFn_listProd (c.children.map (fun ch => fun q : ℕ =>
          omChildCount ch.shape (q ^ (ch.δ * ch.D)))) ?_
      · simpa [List.map_map, Function.comp_def] using hprod
      · intro g hg
        rw [List.mem_map] at hg
        obtain ⟨ch, hch, rfl⟩ := hg
        have hlt : M6.treeSize ch.shape < s := hs ▸ configsOf_descend T c hc ch hch
        exact isRationalFn_compQpow _ (ih _ hlt ch.shape rfl)

/-- **Rationality of the root count** (no pivot, no induction: the children are cluster nodes). -/
theorem omCount_isRational (T : ClusterShape) : IsRationalFn (fun q => omCount T q) := by
  have heq : (fun q => omCount T q)
      = fun q => (((configsOf T).map (fun c =>
          mCell c q * ((q : ℚ) ^ volExp c)⁻¹
            * (c.children.map (fun ch =>
                omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum) := by
    funext q
    rw [omCount]
  rw [heq]
  have hsum := isRationalFn_listSum ((configsOf T).map (fun c => fun q : ℕ =>
      mCell c q * ((q : ℚ) ^ volExp c)⁻¹
        * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)) ?_
  · simpa [List.map_map, Function.comp_def] using hsum
  · intro f hf
    rw [List.mem_map] at hf
    obtain ⟨c, _, rfl⟩ := hf
    refine isRationalFn_mul (isRationalFn_mul (mCell_isRational c) (isRationalFn_invQpow _)) ?_
    have hprod := isRationalFn_listProd (c.children.map (fun ch => fun q : ℕ =>
        omChildCount ch.shape (q ^ (ch.δ * ch.D)))) ?_
    · simpa [List.map_map, Function.comp_def] using hprod
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨ch, _, rfl⟩ := hg
      exact isRationalFn_compQpow _ (omChildCount_isRational ch.shape)

/-- **Rationality of the V2 density**: the finite menu sum of rational per-shape counts. -/
theorem omDensityV2_isRational (n : ℕ) (σ : FactorizationType) :
    IsRationalFn (fun q => omDensityV2 n σ q) :=
  isRationalFn_finsetSum (omMenu n σ) (fun T q => omCount T q)
    (fun T _ => omCount_isRational T)

/-! ## 8. The m×C split (PIN §1.3, stated on `omMenu` membership only) -/

/-- **The explicit multiplicity polynomial** `m_T` (PIN §1.3): the product over the (root)
configuration's faces of the face choice polynomial comp'd into the ambient variable
(`X^δ`). Order-0 menu value: `nodeChoicePolyQ (M7.cellsOfShapeWF T)`. The recursive
per-node-product extension (children comp'd along the `δ·D` base-change chain) is deferred to
the wave that grows the menu past one-node shapes — on the R1 menu this IS the full tree
product. -/
noncomputable def omMultiplicity (T : ClusterShape) : Polynomial ℚ :=
  ((configsOf T).map (fun c =>
    (c.faces.map (fun F =>
      (choicePoly F.punctured F.shape).comp (Polynomial.X ^ F.δ))).prod)).prod

/-- **The volume factor** `C_T` (PIN §1.3): per configuration, the pure box volume `q^{−B}`
times the children's cluster counts (which carry their own pivots). Order-0 menu value:
`(q^n)⁻¹` (no pivot at the root — D4). -/
noncomputable def omVolume (T : ClusterShape) (q : ℕ) : ℚ :=
  ((configsOf T).map (fun c =>
    ((q : ℚ) ^ volExp c)⁻¹
      * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).prod

/-- **The m×C split** (PIN §1.3), stated ON `omMenu` MEMBERSHIP ONLY — the honest scope: the
split is exact on one-configuration-per-node shapes (the sum-over-configs and product-over-nodes
do not commute in general), and the R1 menu shapes are single-node single-configuration. -/
theorem omCount_eq_mul (n : ℕ) (σ : FactorizationType) :
    ∀ T ∈ omMenu n σ, ∀ q : ℕ, 1 < q →
      omCount T q = (omMultiplicity T).eval (q : ℚ) * omVolume T q := by
  intro T _ q _
  rw [omCount, omMultiplicity, omVolume]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one]
  rw [Polynomial.eval_list_prod, List.map_map]
  have hfaces : ((configOf T).faces.map (Polynomial.eval (q : ℚ) ∘ fun F =>
      (choicePoly F.punctured F.shape).comp (Polynomial.X ^ F.δ)))
      = (configOf T).faces.map (fun F =>
          (choicePoly F.punctured F.shape).eval ((q : ℚ) ^ F.δ)) := by
    refine List.map_congr_left fun F _ => ?_
    simp only [Function.comp_apply]
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hfaces]
  unfold mCell
  ring

/-! ## 9. Gate 3/5/6 — Lean evaluations vs the R0 table (`results.txt`, exact fractions) -/

/-- λ = (1) ⊢ 1. -/
def lam1 : Nat.Partition 1 := ⟨{1}, by intro i hi; simp at hi; omega, by simp⟩

/-- λ = (2) ⊢ 2 (the inert pattern). -/
def lam2 : Nat.Partition 2 := ⟨{2}, by intro i hi; simp at hi; omega, by simp⟩

/-- λ = (1,1) ⊢ 2 (the split pattern). -/
def lam11 : Nat.Partition 2 := ⟨{1, 1}, by intro i hi; simp at hi; omega, by decide⟩

/-- λ = (1,2) ⊢ 3. -/
def lam12 : Nat.Partition 3 := ⟨{1, 2}, by intro i hi; simp at hi; omega, by decide⟩

theorem lam1_sort : lam1.parts.sort (· ≤ ·) = [1] := by
  show ({1} : Multiset ℕ).sort (· ≤ ·) = [1]
  exact Multiset.sort_singleton 1 _

theorem lam2_sort : lam2.parts.sort (· ≤ ·) = [2] := by
  show ({2} : Multiset ℕ).sort (· ≤ ·) = [2]
  exact Multiset.sort_singleton 2 _

theorem lam11_sort : lam11.parts.sort (· ≤ ·) = [1, 1] := by
  show ((1 : ℕ) ::ₘ ({1} : Multiset ℕ)).sort (· ≤ ·) = [1, 1]
  rw [Multiset.sort_cons, Multiset.sort_singleton]
  intro b hb
  rw [Multiset.mem_singleton] at hb
  omega

theorem lam12_sort : lam12.parts.sort (· ≤ ·) = [1, 2] := by
  show ((1 : ℕ) ::ₘ ({2} : Multiset ℕ)).sort (· ≤ ·) = [1, 2]
  rw [Multiset.sort_cons, Multiset.sort_singleton]
  intro b hb
  rw [Multiset.mem_singleton] at hb
  omega

/-- The generic eval form of `omCount` on the order-0 menu (the `rootCount_sepShape_eval`
pattern, polynomial side — no finite-field instance needed): choice polynomial of the sorted
parts, evaluated at `q`, times `q^{−n}`. -/
theorem omCount_sepShape_eval_poly (n : ℕ) (hn : 0 < n) (lam : Nat.Partition n) (q : ℕ) :
    omCount (sepShape n lam) q
      = (∏ d ∈ (lam.parts.sort (· ≤ ·)).toFinset,
          Polynomial.C (1 / (((lam.parts.sort (· ≤ ·)).count d).factorial : ℚ))
            * ffPoly (availPoly d) ((lam.parts.sort (· ≤ ·)).count d)).eval (q : ℚ)
        * ((q : ℚ) ^ n)⁻¹ := by
  rw [omCount_sepShape_eq_rootCount, rootCount]
  have h1 : ((M7.cellsOfShapeWF (sepShape n lam)).map (fun c =>
      (c.children.map (fun ch =>
        clusterCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend ch q)).prod)).prod
      = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [sepShape_leaf n lam c hc]
    simp
  rw [h1, mul_one, nodeVolumeExp_sepShape n hn lam]
  congr 1
  unfold nodeChoicePolyQ
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, nodeDelta_sepShape, pow_one]
  unfold nodeChoicePoly
  rw [dSList_sepShape]

/-- `availPoly 1` evaluates to the punctured linear pool `x − 1`. -/
theorem availPoly_one_eval (x : ℚ) : (availPoly 1).eval x = x - 1 := by
  unfold availPoly
  rw [if_pos rfl]
  simp

/-- `availPoly 2` evaluates to the necklace count `(x² − x)/2`. -/
theorem availPoly_two_eval (x : ℚ) : (availPoly 2).eval x = (x ^ 2 - x) / 2 := by
  unfold availPoly necklacePoly
  rw [if_neg (by norm_num), Nat.Prime.divisors (by norm_num : Nat.Prime 2),
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)]
  push_cast
  ring

/-- **Gate 3 + gate 5 (positivity witness), CAL-p n=2 λ=(2) q=2** (`results.txt` row
"n=2 lam=(2,) q=2 … ref=1/4"): the inert quadratic stratum has certified density `1/4 > 0`. -/
theorem gate3_inert_q2 : omCount (sepShape 2 lam2) 2 = 1 / 4 := by
  rw [omCount_sepShape_eval_poly 2 (by norm_num) lam2 2, lam2_sort]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.prod_singleton,
    List.count_cons_self, List.count_nil, Nat.factorial]
  unfold ffPoly
  rw [Finset.prod_range_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Nat.cast_ofNat,
    availPoly_two_eval]
  norm_num

theorem gate5_positivity : 0 < omCount (sepShape 2 lam2) 2 := by
  rw [gate3_inert_q2]; norm_num

/-- **Gate 3 + gate 5 (correctly-empty case), CAL-p n=2 λ=(1,1) q=2** (`results.txt` row
"n=2 lam=(1, 1) a0-unit q=2 … ref=0"): the split stratum is genuinely EMPTY at `q = 2`
(`ff(q−1, 2) = 0` — any two distinct monic linears over `F₂` include `X`; SIGMA-1 honesty,
do NOT "fix"). -/
theorem gate5_empty : omCount (sepShape 2 lam11) 2 = 0 := by
  rw [omCount_sepShape_eval_poly 2 (by norm_num) lam11 2, lam11_sort]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    List.count_cons, List.count_nil]
  norm_num [ffPoly, Finset.prod_range_succ, availPoly_one_eval, Nat.factorial]

/-- **Gate 3/6, CAL-p n=2 λ=(1,1) q=3** (`results.txt`: ref=1/9). -/
theorem gate3_split_q3 : omCount (sepShape 2 lam11) 3 = 1 / 9 := by
  rw [omCount_sepShape_eval_poly 2 (by norm_num) lam11 3, lam11_sort]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    List.count_cons, List.count_nil]
  norm_num [ffPoly, Finset.prod_range_succ, availPoly_one_eval, Nat.factorial]

/-- **Gate 3/6, CAL-p n=2 λ=(2) q=3** (`results.txt`: ref=1/3). -/
theorem gate3_inert_q3 : omCount (sepShape 2 lam2) 3 = 1 / 3 := by
  rw [omCount_sepShape_eval_poly 2 (by norm_num) lam2 3, lam2_sort]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.prod_singleton,
    List.count_cons_self, List.count_nil, Nat.factorial]
  unfold ffPoly
  rw [Finset.prod_range_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    availPoly_two_eval]
  norm_num

/-- **Gate 3, CAL-p n=3 λ=(1,2) q=2** (`results.txt`: ref=1/8) — a two-degree face. -/
theorem gate3_mixed_q2 : omCount (sepShape 3 lam12) 2 = 1 / 8 := by
  rw [omCount_sepShape_eval_poly 3 (by norm_num) lam12 2, lam12_sort]
  rw [show ([1, 2] : List ℕ).toFinset = {1, 2} by rfl]
  rw [Finset.prod_insert (by norm_num), Finset.prod_singleton]
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  norm_num [ffPoly, Finset.prod_range_one, availPoly_one_eval, availPoly_two_eval,
    Nat.factorial]

/-- **Gate 6 (σ-separation, O1).** Two DIFFERENT degree-2 factorization types with DIFFERENT
certified values at `q = 3`: split `ff(2,2)/2!·3⁻² = 1/9` vs inert `M₂(3)·3⁻² = 1/3` (the
order-0 witness of PIN §2 gate 6; `results.txt` rows n=2 q=3). σ enters through the menu, and
distinct types key distinct per-shape values — a σ-discarding regression fails this gate. -/
theorem gate6_sigma_separation :
    unramType 2 lam11 ≠ unramType 2 lam2
      ∧ omCount (sepShape 2 lam11) 3 ≠ omCount (sepShape 2 lam2) 3 := by
  constructor
  · intro h
    have := congrArg (fun σ => σ.data) h
    simp only [unramType] at this
    have h2 : ((1, 2) : ℕ × ℕ) ∈ ({(1, 1), (1, 1)} : Multiset (ℕ × ℕ)) := by
      rw [show ({(1, 1), (1, 1)} : Multiset (ℕ × ℕ)) = lam11.parts.map (fun d => (1, d)) by rfl,
        this]
      simp [lam2]
    simp at h2
  · rw [gate3_split_q3, gate3_inert_q3]
    norm_num

/-! ### The cluster gate (gate 3, ONE cluster case — the slope-−1/2 family) -/

/-- The slope-−1/2 lattice face (vertices `(0,1)–(2,0)`): width 2, ceiling heights
`⌈1⌉ = ⌈1/2⌉ = 1`, single lattice vertex at column 0. `newtonExponent = 2`. -/
def halfFace : L4.LatticePolygon :=
  ⟨2, fun _ => 1, fun i => decide (i.val = 0)⟩

theorem newtonExponent_halfFace : L4.newtonExponent halfFace = 2 := by
  unfold L4.newtonExponent halfFace
  simp

/-- **The size-2 ramified cluster of the slope-−1/2 family** (the R0 harness
`slope_half_leaf`): order 1, cluster size 2, one genuine (punctured) face of slope −1/2 with a
single linear residual factor. -/
def halfCluster : ClusterShape :=
  ⟨[(1, 2, 1)], [⟨1, 1, halfFace, []⟩]⟩

theorem cellsOfShapeWF_halfCluster :
    M7.cellsOfShapeWF halfCluster = [⟨1, 1, halfFace, []⟩] := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · rfl
  · intro c hc ch hch
    have hc' : c = ⟨1, 1, halfFace, []⟩ := by
      simpa [M7.cellsOfShape, halfCluster] using hc
    subst hc'
    simp at hch

theorem treeSize_halfCluster : M6.treeSize halfCluster = 2 := rfl

/-- The single configuration the reader extracts from `halfCluster`. -/
def halfConfig : NodeConfig :=
  { polygon := halfFace
    faces := [{ δ := 1, shape := [(1, 1)], dF := 1, punctured := true }]
    children := [] }

theorem configsOf_halfCluster : configsOf halfCluster = [halfConfig] := by
  show [configOf halfCluster] = [halfConfig]
  unfold configOf halfConfig
  rw [cellsOfShapeWF_halfCluster]
  rfl

/-- The face choice polynomial of the cluster's single linear factor evaluates to the punctured
pool `x − 1`. -/
theorem choicePoly_halfCluster_eval (x : ℚ) :
    (choicePoly true [((1 : ℕ), (1 : ℕ))]).eval x = x - 1 := by
  unfold choicePoly symFactor faceMus
  norm_num [ffPoly, Finset.prod_range_one, Nat.factorial]
  rw [show poolPoly true 1 = availPoly 1 from rfl]
  simp [availPoly_one_eval]

theorem mCell_halfConfig (q : ℕ) : mCell halfConfig q = (q : ℚ) - 1 := by
  unfold mCell halfConfig
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [choicePoly_halfCluster_eval, pow_one]

theorem volExp_halfConfig : volExp halfConfig = 3 := by
  unfold volExp halfConfig
  simp [newtonExponent_halfFace]

/-- **Gate 3, THE CLUSTER CASE — the slope-−1/2 family at `q = 2`** (`results.txt` row
"[C1-fam] size-2 cluster ram family q=2 vs engine beta_2[(2,1)] anchor: ref=2/3"): exercises
the E1 `−s` cluster normalization (`B = 2 + 1 − 2 = 1`) AND the D4 cluster-only pivot
(`countPivot 2 = 1 − q⁻²`): `(q−1)/q / (1−q⁻²) = q/(q+1) = 2/3` at `q = 2`. -/
theorem gate3_cluster_q2 : omChildCount halfCluster 2 = 2 / 3 := by
  rw [omChildCount_rec, configsOf_halfCluster]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    treeSize_halfCluster, mCell_halfConfig, volExp_halfConfig,
    show halfConfig.children = [] from rfl, List.prod_nil, mul_one]
  rw [show MontesAxiom.countPivot 2 2 = 3 / 4 by
    unfold MontesAxiom.countPivot L5fix.selfLoopExponent
    norm_num]
  norm_num

/-- **Gate 3, the cluster case at `q = 3`** (`results.txt`: "C1-fam … q=3 … ref=3/4"). -/
theorem gate3_cluster_q3 : omChildCount halfCluster 3 = 3 / 4 := by
  rw [omChildCount_rec, configsOf_halfCluster]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    treeSize_halfCluster, mCell_halfConfig, volExp_halfConfig,
    show halfConfig.children = [] from rfl, List.prod_nil, mul_one]
  rw [show MontesAxiom.countPivot 2 3 = 8 / 9 by
    unfold MontesAxiom.countPivot L5fix.selfLoopExponent
    norm_num]
  norm_num

/-! ## 10. Gate 7 — falsifiability: off-menu shapes are NOT constrained -/

/-- A junk shape: the `sepShape 1 (1)` TREE slot with an EMPTY payload. -/
def junkEmptyPayload : ClusterShape := ⟨[(0, 1, 1)], []⟩

/-- `omCount` of the empty-payload junk shape is the empty-product `1` — NOT a density of
anything. -/
theorem gate7_junk_value : omCount junkEmptyPayload 2 = 1 := by
  have hcs : M7.cellsOfShapeWF junkEmptyPayload = [] := by
    rw [M7.cellsOfShapeWF_eq_of_descend]
    · rfl
    · intro c hc
      simp [M7.cellsOfShape, junkEmptyPayload] at hc
  rw [omCount]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hchild : (configOf junkEmptyPayload).children = [] := by
    unfold configOf
    rw [hcs]
    rfl
  have hm : mCell (configOf junkEmptyPayload) 2 = 1 := by
    unfold mCell configOf
    rw [hcs]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold choicePoly
    simp
  have hv : volExp (configOf junkEmptyPayload) = 0 := by
    unfold volExp configOf
    rw [hcs]
    rfl
  rw [hchild, hm, hv]
  simp

/-- **Gate 7 (falsifiability of ∀-shape statements).** Two `ClusterShape`s with the SAME
count-native tree slot but DIFFERENT payloads get DIFFERENT `omCount` values (`1/2` on the
genuine `sepShape 1 (1)` vs the empty-product `1` on the junk payload): `omCount` off the menu
is a free-payload read, constrained by NOTHING. Every ∀-shape claim about `omCount` must carry
the `omMenu` restriction (or the WF/emission guard) — the menu guard is load-bearing; a claim
quantified over raw `ClusterShape` is falsified by payload surgery like this one. -/
theorem gate7_menu_guard_load_bearing :
    (sepShape 1 lam1).tree = junkEmptyPayload.tree
      ∧ omCount (sepShape 1 lam1) 2 ≠ omCount junkEmptyPayload 2 := by
  constructor
  · rfl
  · rw [gate7_junk_value]
    rw [omCount_sepShape_eval_poly 1 (by norm_num) lam1 2, lam1_sort]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.prod_singleton,
      List.count_cons_self, List.count_nil, Nat.factorial]
    norm_num [ffPoly, Finset.prod_range_one, availPoly_one_eval]

end LeanUrat.OM.OMCountV2

