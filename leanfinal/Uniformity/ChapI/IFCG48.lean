/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG47

/-!
# Uniformity.ChapI.IFCG48 — UNIT CTS: the deep-wild OM tower step
(`CellTypeScalingAt D` at `D ≥ 2`): the provable fringe, the faithful-cite
reduction wiring, and the consumer instantiations

Stage CTS of the cone census (design record `runs/wave-c/verdict_CTS.md`; the fence is
DTR's verdict `runs/wave-c/verdict_DTR.md`).  DTR (IFCG47) isolated the ONE open
pointwise Prop of the full-span/dd territory — `CellTypeScalingAt D` — and proved it at
`D = 1`.  This file works the `D ≥ 2` face.  Map:

* **§0** the `D = 0` witness (`cellTypeScalingAt_zero`) — completes the depth interval.
* **§1** the RAW cite surface (`DeepWildTypeScalingStatement`, stated NOT asserted) +
  the wiring (`cellTypeScaling_of_cite`): the signed cite fires the COMPLETE pointwise
  law by composing with the machine-checked `D = 0, 1` witnesses.
* **§2** the Eisenstein valuation bridge: `eis_addVal_algebraMap` (the `e(K'/K) = e'`
  scaling), `eis_addVal_norm` (the `f(K'/K) = 1` norm identity), and
  `eis_addVal_norm_tower` (★★★ THE TOWER MASTER IDENTITY: `addVal_O ∘ norm_O =
  addVal_{O'} ∘ norm_{O'}` on ANY free `O'`-algebra, via mathlib's `Algebra.norm_norm`).
* **§3** the tower `(e, f)` reads: `normValues`/`inertiaDegOf` invariance through an
  order iso, the `finrank` degree law, the per-factor `(e, f) ↦ (e'·e, f)` scaling.
* **§4** THE MULTISET REDUCTION (`typeOf_eq_scaleType_of_rel`): the factor
  correspondence — equal inertia gcd + `e'`-scaled degree per matched pair — fires the
  full type-scaling read.  No lattice/box hypotheses consumed at this layer.
* **§5** the CORRESPONDENCE cite surface (`FactorCorrespondenceAt D`, the strictly
  smaller trusted statement) + the reduction to the named Prop
  (`cellTypeScalingAt_of_factorCorrespondence`) and to the raw surface.
* **§6** the consumer sockets: the decision-transport iff at every depth from either
  cite surface (`transport_decidedAt_iff_of_cite`/`_of_correspondence` — the
  face/centre assembly's entry point on the composite-mass census front) and the
  `D = 2` supplies for ER4's dd terms (`cellTypeScalingAt_two_of_cite`/`_of_corr…`).

Every declaration in this file is PURE LEAN CORE (`#print axioms` block at the end):
no cite is consumed anywhere; the two cite statements are staged, never asserted.

## THE PROPOSED GATE-(b) CITE — faithfulness entry DRAFT (stated, NOT asserted)

**Proposed statement — two surfaces, the owner signs ONE:**

1. RAW surface: `axiom …deep_wild_type_scaling : DeepWildTypeScalingStatement` (§1) —
   exactly DTR's named Prop, quantified over `D ≥ 2`.
2. CORRESPONDENCE surface (recommended — strictly smaller trusted content):
   `axiom …deep_wild_factor_correspondence : ∀ D, 2 ≤ D → FactorCorrespondenceAt D`
   (§5).  The Lean-core reduction `deepWildTypeScaling_of_correspondence` then yields
   surface 1, so every consumer fires either way; with surface 2 all `(e, f)`/type
   bookkeeping stays machine-checked and ONLY the factor matching is trusted.

**Sources (print-read to pin exact theorem numbering at declaration time):** the
Montes/Okutsu induction step — the Theorem of the Polygon + the Theorem of the
Residual Polynomial and the induced factor correspondence along a key extension:
J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic number
theory*, Trans. AMS 364 (2012) 361–416 (order-`r` induction, §§1–3); companion
dictionary anchor: FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427
(2015) — the corpus's standing FGMN dictionary at C66b; repo PDF
`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`.

**Dictionary (corpus ↔ source):**
* `eisKey π w e' = X^{e'} + C (w·π)` ↔ a degree-`e'` key polynomial attached to the
  one-sided slope `−1/e'` polygon side (Eisenstein: totally ramified step
  `e(K'/K) = e'`, `f(K'/K) = 1` — `eis_residueCard` pins `q' = q`).
* `devT (eisKey π w e') D g` ↔ the `φ`-adic development digits of `g` reduced into
  `O' = O[x]/(φ)` — the second-order transform carrier.
* the full-span lattice + `alphaBox` divisibilities ↔ the cell: `g` `φ`-regular with
  its order-2 data strictly inside the deep recentred box (raw purity at `h = 1`).
* `Multiset.Rel (fun h H => inertiaDegOf h = inertiaDegOf H ∧ h.natDegree = e' * H.natDegree)
  (monicFactors g) (monicFactors (devT …))` ↔ the OM bijection between the monic
  irreducible `O`-factors of `g` and the monic irreducible `O'`-factors of the
  transform, with multiplicity, each matched pair carrying `e(L/K) = e'·e(L/K')`,
  `f(L/K) = f(L/K')`.

**Scope caveats (the signing read must adjudicate these):**
1. *Order vs. field.*  The relation is on the ORDERS' gcd reads (`inertiaDegOf` = gcd
   of `addVal ∘ norm` over `O[x]/(h)`), deliberately NOT an order isomorphism: OM
   matches the FIELDS `L ≅ L'` over `K'`, and the orders `O[x]/(h)`, `O'[Y]/(H)` need
   not be isomorphic.  The classical `f(L/K) = f(L'/K')` implies the gcd equality only
   through the reading "`inertiaDegOf` = the true residue degree", which holds for any
   order with fraction field `L` (its value semigroup generates `ℤ`, so the gcd of the
   norm-valuations is exactly `f`).  That reading is NOT formalized; it is part of the
   trusted surface.  (§3's iso-based lemmas are the machine-checked SPECIAL case, not
   the cite's route.)
2. *Multiplicity / inseparability.*  The Rel matches factors WITH multiplicity, over
   ALL monic `g` in the cell — including inseparable/repeated-factor `g` (`devT` is NOT
   multiplicative, so `g = h²` does not formally force a doubled transform factor).
   The classical sources state the correspondence for separable (often squarefree) `g`.
   The signing read must either confirm the cell hypotheses exclude/handle this fringe
   at `D ≥ 2` or add an explicit separability hypothesis to the axiom — in which case
   the named Prop's consumers must thread it (a statement-shape decision, owner gate).
   NOTE: this caveat applies equally to the RAW surface (DTR's Prop quantifies over the
   same `g`); it is not introduced by the correspondence form.
3. *Sufficiency only.*  The cite asserts the correspondence FOR cells satisfying the
   lattice/box hypotheses; no converse, no exhaustiveness over cells is claimed.

## Honest scope (the exact remainder)

`FactorCorrespondenceAt D` at `D ≥ 2` (equivalently, per §5's reduction: the named
Prop `CellTypeScalingAt D` at `D ≥ 2`) is the surviving open mathematics of this
territory — the deep-wild OM tower step proper.  Also OPEN, out of this unit's scope:
the `ZcURLim` census assemblies that consume §6's sockets (the face/centre partition
summation — `PowerFullSpanLaw` at composite mass, ER4's `ZcURLim (e1DdDecFam σ)`
limits).  Nothing is weakened; whatever this file does not prove survives as the
exact named remainder above.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG48

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique powerSector)
open Uniformity.Density.IFCG39 (powerSector_data eisKey eisKey_monic eisKey_natDegree
  devT devT_coeff devT_monic reassT reassT_monic devT_reassT reassT_devT
  eis_root_pow_dvd_mk_iff eis_root_pow)
open Uniformity.Density.IFCG43 (cellTransport cellTransport_apply cellTransport_symm_apply)
open Uniformity.Density.IFCG47 (scaleType scaleType_data scaleType_degree scaleType_one
  scaleType_scaleType scaleType_injective CellTypeScalingAt CellTypeScaling
  cellTypeScalingAt_one transport_decidedAt_iff)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the trivial-depth completion: `D = 0` -/

section DepthZero

/-- The empty factorization of `1` (kit): `monicFactors 1 = 0`. -/
private theorem monicFactors_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : monicFactors (1 : Polynomial R) = 0 :=
  monicFactors_eq ⟨fun g hg => absurd hg (Multiset.notMem_zero g), Multiset.prod_zero⟩

/-- The type of the constant `1` is the empty multiset (kit). -/
private theorem typeOf_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : typeOf (1 : Polynomial R) = ⟨0⟩ := by
  apply FactorizationType.ext
  rw [typeOf_data, monicFactors_one]
  simp

/-- ★ **The depth-0 witness**: at `D = 0` the block is the constant `1`, the transform
is the constant `1`, and both types are the empty multiset — `CellTypeScalingAt 0`
holds trivially.  (Zero census weight; it completes the depth interval so that the
deep-wild cite at `D ≥ 2` fires the FULL pointwise law `CellTypeScaling`.) -/
theorem cellTypeScalingAt_zero : CellTypeScalingAt 0 := by
  intro O _ _ _ _ _ π w hπ hw e' he' _ _ g hg hdeg hlat hbox
  have he'' : 0 < e' := by omega
  have hg1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp (by omega)
  subst hg1
  have hdevT : devT (eisKey π w e') 0 (1 : Polynomial O) = 1 := by
    have h1 : dev (eisKey π w e') (1 : Polynomial O) 0 = 1 := by
      show (1 : Polynomial O) %ₘ eisKey π w e' = 1
      refine (Polynomial.modByMonic_eq_self_iff (eisKey_monic he'')).mpr ?_
      rw [Polynomial.degree_one]
      exact Polynomial.natDegree_pos_iff_degree_pos.mp
        (by rw [eisKey_natDegree he'']; omega)
    rw [devT, Finset.range_one, Finset.sum_singleton, h1, map_one, pow_zero, mul_one,
      Polynomial.C_1]
  rw [hdevT, typeOf_one, typeOf_one]
  apply FactorizationType.ext
  rw [scaleType_data]
  simp

end DepthZero

/-! ## §1 — THE PROPOSED CITE (stated, NOT asserted) and the complete-law wiring -/

section CiteStatement

/-- **THE PROPOSED GATE-(b) CITE STATEMENT — stated, NOT asserted** (the OM-5 /
`BBox1CiteStatement` staging pattern): the deep-wild OM tower step at every depth
`D ≥ 2` — exactly DTR's named Prop, quantified over the census-relevant depths.
Elaborating this file machine-checks that the proposed statement TYPES against the
landed layer; **nothing here asserts it**.  Until the owner signs it as an `axiom`,
every consumer takes `DeepWildTypeScalingStatement` as an explicit hypothesis.  The
faithfulness draft (sources, dictionary, scope caveats) is in this file's module
docstring and the review-queue row. -/
def DeepWildTypeScalingStatement : Prop := ∀ D : ℕ, 2 ≤ D → CellTypeScalingAt D

/-- ★★ **THE WIRING**: the proposed cite fires the COMPLETE pointwise scaling law —
every depth, every complete DVR, uniform in `q, e', D` — by composing with the
machine-checked `D = 0` (this file) and `D = 1` (DTR's IFCG47) witnesses.  A future
owner-signed `axiom` of type `DeepWildTypeScalingStatement` makes this fire
unconditionally, with the axiom name visible in every downstream `#print axioms`. -/
theorem cellTypeScaling_of_cite (hcite : DeepWildTypeScalingStatement) :
    CellTypeScaling := by
  intro D
  match D with
  | 0 => exact cellTypeScalingAt_zero
  | 1 => exact cellTypeScalingAt_one
  | (n + 2) => exact hcite (n + 2) (by omega)

end CiteStatement

/-! ## §2 — the Eisenstein valuation bridge (the ramified norm-transport legs) -/

section EisValuation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π c : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π c e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]
  [Finite (ResidueField O)] [Finite (ResidueField (AdjoinRoot (eisKey π c e')))]

open Uniformity.Density.IFCG43 (eis_root_irreducible)

/-- ★ **The ramified valuation transport** (the Eisenstein analogue of IFCG32's
`addVal_map_of_irreducible`, which is unusable here because `algebraMap π = unit·α^{e'}`
is NOT irreducible): along the totally ramified structure map the valuation scales by
exactly `e'` — the `e`-multiplicativity of the tower step, in `addVal` form.  Uniform in
`q, e'`, instance-parametric (no completeness consumed). -/
theorem eis_addVal_algebraMap (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') (z : O) :
    IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))
      (algebraMap O (AdjoinRoot (eisKey π c e')) z)
      = e' • IsDiscreteValuationRing.addVal O z := by
  have he'' : 0 < e' := by omega
  have hα : Irreducible (AdjoinRoot.root (eisKey π c e')) := eis_root_irreducible hπ hc he'
  have hcu : IsUnit c := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmem => hc ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, (IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))).map_zero,
      (IsDiscreteValuationRing.addVal O).map_zero, nsmul_eq_mul, ENat.mul_top]
    exact_mod_cast (by omega : e' ≠ 0)
  -- the image of the uniformizer has valuation exactly `e'`
  have hπ' : IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))
      (algebraMap O (AdjoinRoot (eisKey π c e')) π) = ((e' : ℕ) : ℕ∞) := by
    have h1 : (AdjoinRoot.root (eisKey π c e')) ^ e'
        = algebraMap O (AdjoinRoot (eisKey π c e')) (-c)
          * algebraMap O (AdjoinRoot (eisKey π c e')) π := by
      rw [eis_root_pow he'', ← map_neg, ← neg_mul, map_mul]
    have h2 := congrArg (IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))) h1
    rw [IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hα,
      IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2
        ((hcu.neg).map (algebraMap O (AdjoinRoot (eisKey π c e')))),
      zero_add, nsmul_eq_mul, mul_one] at h2
    exact h2.symm
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hπ
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2
      (u.isUnit.map (algebraMap O (AdjoinRoot (eisKey π c e')))),
    zero_add, IsDiscreteValuationRing.addVal_pow, hπ',
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 u.isUnit, zero_add,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ,
    nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  exact mul_comm _ _

/-- The constant coefficient of the Eisenstein key (kit; IFCG47's private replica). -/
private theorem eisKey_coeff_zero (he' : 0 < e') : (eisKey π c e').coeff 0 = c * π := by
  show (Polynomial.X ^ e' + Polynomial.C (c * π)).coeff 0 = c * π
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = e'),
    Polynomial.coeff_C, if_pos rfl, zero_add]

/-- ★★ **The `f(K'/K) = 1` norm identity**: the valuation over `O` of the norm from the
recentring ring equals the valuation over `O'` — the residue-degree triviality of the
totally ramified step, in the exact `normValues` currency of `typeOf`.  (The inertia
`f`-data of the tower step cancels; the `e`-data lives in `eis_addVal_algebraMap`'s
`e'`-scaling and in the degree bookkeeping `scaleType_degree`.)  Mechanism: `N(α) =
±c·π` (CN-19) has valuation exactly `1 = addVal α`, and every element is `u·α^j`. -/
theorem eis_addVal_norm (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') (y : AdjoinRoot (eisKey π c e')) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O y)
      = IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e')) y := by
  have he'' : 0 < e' := by omega
  have hα : Irreducible (AdjoinRoot.root (eisKey π c e')) := eis_root_irreducible hπ hc he'
  have hcu : IsUnit c := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmem => hc ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  haveI : Module.Finite O (AdjoinRoot (eisKey π c e')) :=
    (AdjoinRoot.powerBasis' (eisKey_monic he'')).finite
  haveI : Module.Free O (AdjoinRoot (eisKey π c e')) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (eisKey_monic he'')).basis
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Algebra.norm_zero, (IsDiscreteValuationRing.addVal O).map_zero,
      (IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))).map_zero]
  -- the norm of the root has valuation exactly `1`
  have hNα : IsDiscreteValuationRing.addVal O
      (Algebra.norm O (AdjoinRoot.root (eisKey π c e'))) = (1 : ℕ∞) := by
    rw [Uniformity.Density.norm_adjoinRoot_root (eisKey_monic he'')
        (by rw [eisKey_natDegree he'']; omega),
      eisKey_coeff_zero he'', IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 ((isUnit_one.neg).pow _),
      zero_add, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 hcu, zero_add,
      IsDiscreteValuationRing.addVal_uniformizer hπ]
  obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hα
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map (Algebra.norm O)),
    zero_add, IsDiscreteValuationRing.addVal_pow, hNα,
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 u.isUnit, zero_add,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hα]

/-- ★★★ **THE TOWER MASTER IDENTITY** (M3): for ANY free algebra `A` over the
recentring ring `O' = AdjoinRoot (eisKey π c e')` (the OM tower top — `A = O'[Y]/(H)`
for a deep-wild factor `H` is the intended instance), the `O`-valuation of the `O`-norm
agrees with the `O'`-valuation of the `O'`-norm: mathlib's norm transitivity
`Algebra.norm_norm` composed with the landed `f(K'/K) = 1` identity `eis_addVal_norm`.
This is the exact transport that makes the `normValues` currency of `typeOf` (the gcd
read `inertiaDegOf`) INVARIANT across the Eisenstein tower step — the `e`-data of the
step lives in the degree bookkeeping alone (`scaleType_degree`, `finrank` tower law).
Uniform in `q, e'`; no completeness, domain, or finiteness assumption on `A`. -/
theorem eis_addVal_norm_tower (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') {A : Type*} [CommRing A] [Algebra O A]
    [Algebra (AdjoinRoot (eisKey π c e')) A]
    [IsScalarTower O (AdjoinRoot (eisKey π c e')) A]
    [Module.Free (AdjoinRoot (eisKey π c e')) A] (z : A) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O z)
      = IsDiscreteValuationRing.addVal (AdjoinRoot (eisKey π c e'))
          (Algebra.norm (AdjoinRoot (eisKey π c e')) z) := by
  have he'' : 0 < e' := by omega
  haveI : Module.Free O (AdjoinRoot (eisKey π c e')) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (eisKey_monic he'')).basis
  rw [← Algebra.norm_norm (R := O) (S := AdjoinRoot (eisKey π c e')) (a := z)]
  exact eis_addVal_norm hπ hc he' (Algebra.norm (AdjoinRoot (eisKey π c e')) z)

end EisValuation

/-! ## §3 — the tower `(e, f)` reads: `normValues`, `inertiaDegOf`, `efPair` across
the Eisenstein step (the per-factor content of the OM correspondence, machine-checked) -/

section TowerReads

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π c : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π c e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]

-- NOTE: the `Finite (ResidueField ·)` instances are NOT section variables here — the
-- lemmas that consume the master identity take them explicitly (they inherit them from
-- §2's `eis_root_irreducible` fence), while the pure-bookkeeping lemmas
-- (`natDegree_eq_of_algEquiv`, `efPair_eq_scale`) genuinely need none, and §4/§5's
-- reduction chain must stay synthesizable from exactly `CellTypeScalingAt`'s binders.

/-- ★★ (f-leg) **`normValues` is invariant across the tower step**: if the order
`O[x]/(h)` is `O`-algebra isomorphic to the recentred order `O'[Y]/(H)`, the two
norm-valuation sets — the exact currency in which `typeOf` reads `f` — coincide.
Mechanism: the iso preserves `O`-norms (`Algebra.norm_eq_of_algEquiv`) and the master
identity `eis_addVal_norm_tower` converts `O`-norm valuations to `O'`-norm valuations. -/
theorem normValues_eq_of_algEquiv
    [Finite (ResidueField O)] [Finite (ResidueField (AdjoinRoot (eisKey π c e')))]
    (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') {H : Polynomial (AdjoinRoot (eisKey π c e'))} (hH : H.Monic)
    {h : Polynomial O} (ψ : AdjoinRoot h ≃ₐ[O] AdjoinRoot H) :
    normValues h = normValues H := by
  haveI : Module.Free (AdjoinRoot (eisKey π c e')) (AdjoinRoot H) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hH).basis
  ext k
  constructor
  · rintro ⟨hk, x, hx, hval⟩
    refine ⟨hk, ψ x, fun h0 => hx (ψ.injective (by rw [h0, map_zero])), ?_⟩
    rw [← eis_addVal_norm_tower hπ hc he' (ψ x), Algebra.norm_eq_of_algEquiv ψ x]
    exact hval
  · rintro ⟨hk, y, hy, hval⟩
    refine ⟨hk, ψ.symm y, fun h0 => hy ?_, ?_⟩
    · rw [← ψ.apply_symm_apply y, h0, map_zero]
    · have h1 : Algebra.norm O (ψ.symm y : AdjoinRoot h) = Algebra.norm O y := by
        rw [← Algebra.norm_eq_of_algEquiv ψ (ψ.symm y), ψ.apply_symm_apply]
      rw [h1, eis_addVal_norm_tower hπ hc he' y]
      exact hval

/-- (f-leg, gcd form) `inertiaDegOf` — the `f` of the `typeOf` read — is invariant
across the tower step: it is a function of `normValues` alone. -/
theorem inertiaDegOf_eq_of_algEquiv
    [Finite (ResidueField O)] [Finite (ResidueField (AdjoinRoot (eisKey π c e')))]
    (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    {H : Polynomial (AdjoinRoot (eisKey π c e'))} (hH : H.Monic)
    {h : Polynomial O} (ψ : AdjoinRoot h ≃ₐ[O] AdjoinRoot H) :
    inertiaDegOf h = inertiaDegOf H := by
  unfold inertiaDegOf normDivisors
  rw [normValues_eq_of_algEquiv hπ hc he' hH ψ]

/-- (e-leg) **the degree scales by exactly `e'`** across the tower iso — the `finrank`
tower law `[L : K] = [L : K'] · [K' : K]` through the `O`-algebra iso of the orders.
(No Eisenstein data consumed: pure rank bookkeeping through the free tower.) -/
theorem natDegree_eq_of_algEquiv (he' : 2 ≤ e')
    {H : Polynomial (AdjoinRoot (eisKey π c e'))} (hH : H.Monic)
    {h : Polynomial O} (hh : h.Monic)
    (ψ : AdjoinRoot h ≃ₐ[O] AdjoinRoot H) :
    h.natDegree = e' * H.natDegree := by
  have he'' : 0 < e' := by omega
  haveI : Module.Free O (AdjoinRoot (eisKey π c e')) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (eisKey_monic he'')).basis
  haveI : Module.Free (AdjoinRoot (eisKey π c e')) (AdjoinRoot H) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hH).basis
  have h1 : Module.finrank O (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis' hh).finrank]; rfl
  have h2 : Module.finrank O (AdjoinRoot (eisKey π c e')) = e' := by
    rw [(AdjoinRoot.powerBasis' (eisKey_monic he'')).finrank]
    exact eisKey_natDegree he''
  have h3 : Module.finrank (AdjoinRoot (eisKey π c e')) (AdjoinRoot H) = H.natDegree := by
    rw [(AdjoinRoot.powerBasis' hH).finrank]; rfl
  have h4 : Module.finrank O (AdjoinRoot (eisKey π c e'))
        * Module.finrank (AdjoinRoot (eisKey π c e')) (AdjoinRoot H)
      = Module.finrank O (AdjoinRoot H) :=
    Module.finrank_mul_finrank O (AdjoinRoot (eisKey π c e')) (AdjoinRoot H)
  have h5 : Module.finrank O (AdjoinRoot h) = Module.finrank O (AdjoinRoot H) :=
    ψ.toLinearEquiv.finrank_eq
  rw [← h1, h5, ← h4, h2, h3]

/-- ★★ **THE PER-FACTOR `(e, f)` SCALING, bookkeeping form**: equal inertia gcd
(f-leg) + `e'`-scaled degree (e-leg) force `efPair h = (e'·e_H, f_H)` — exactly
`scaleType`'s member map.  Pure arithmetic: `e = deg/f` and `f ∣ deg` (the gcd
recognition `inertiaDegOf_dvd_natDegree` over the recentring ring). -/
theorem efPair_eq_scale {H : Polynomial (AdjoinRoot (eisKey π c e'))} (hH : H.Monic)
    (hHd : 0 < H.natDegree) {h : Polynomial O}
    (hf : inertiaDegOf h = inertiaDegOf H) (hdeg : h.natDegree = e' * H.natDegree) :
    efPair h = (e' * (efPair H).1, (efPair H).2) := by
  simp only [efPair, ramIndexOf]
  rw [hf, hdeg, Nat.mul_div_assoc e' (inertiaDegOf_dvd_natDegree hH hHd)]

/-- ★★★ (M4, assembled) **the OM correspondence's per-factor content, order form**:
an `O`-algebra iso of the orders `O[x]/(h) ≃ₐ[O] O'[Y]/(H)` forces the exact
`(e, f) ↦ (e'·e, f)` scaling of the `typeOf` member — every read machine-checked
(no cite consumed). -/
theorem efPair_scaled_of_algEquiv
    [Finite (ResidueField O)] [Finite (ResidueField (AdjoinRoot (eisKey π c e')))]
    (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    {H : Polynomial (AdjoinRoot (eisKey π c e'))} (hH : H.Monic) (hHd : 0 < H.natDegree)
    {h : Polynomial O} (hh : h.Monic)
    (ψ : AdjoinRoot h ≃ₐ[O] AdjoinRoot H) :
    efPair h = (e' * (efPair H).1, (efPair H).2) :=
  efPair_eq_scale hH hHd (inertiaDegOf_eq_of_algEquiv hπ hc he' hH ψ)
    (natDegree_eq_of_algEquiv he' hH hh ψ)

end TowerReads

/-! ## §4 — THE MULTISET REDUCTION: the factor correspondence fires the type-scaling
read.  The remaining open content of `CellTypeScalingAt D` at `D ≥ 2` is EXACTLY the
correspondence (§5); every `(e, f)` read is machine-checked here. -/

section Reduction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π c : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π c e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]

/-- A monic irreducible has positive degree (kit). -/
private theorem natDegree_pos_of_monic_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {g : Polynomial R} (hg : g.Monic) (hirr : Irreducible g) : 0 < g.natDegree := by
  by_contra hcon
  have h1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp (by omega)
  rw [h1] at hirr
  exact hirr.not_isUnit isUnit_one

/-- ★★★ **THE MULTISET REDUCTION**: the OM factor correspondence — matched factors
with equal inertia gcd (f-leg) and `e'`-scaled degree (e-leg) — fires the full
type-scaling read `typeOf g = scaleType e' (typeOf G)`, for ANY monic `g` over `O`
and monic `G` over the recentring ring.  The lattice/box hypotheses of the named Prop
play NO role at this layer: they are consumed only in PROVING the correspondence
(the deep-wild OM tower content, §5's named remainder). -/
theorem typeOf_eq_scaleType_of_rel {g : Polynomial O}
    {G : Polynomial (AdjoinRoot (eisKey π c e'))} (hG : G.Monic)
    (hrel : Multiset.Rel
      (fun h H => inertiaDegOf h = inertiaDegOf H ∧ h.natDegree = e' * H.natDegree)
      (monicFactors g) (monicFactors G)) :
    typeOf g = scaleType e' (typeOf G) := by
  apply FactorizationType.ext
  rw [scaleType_data, typeOf_data, typeOf_data, Multiset.map_map]
  refine Multiset.rel_eq.mp (Multiset.rel_map.mpr (hrel.mono ?_))
  intro h hhmem H hHmem hr
  obtain ⟨hf, hdeg⟩ := hr
  have hHm := ((monicFactors_spec hG).1 H hHmem).1
  have hHirr := ((monicFactors_spec hG).1 H hHmem).2
  have hHd : 0 < H.natDegree := natDegree_pos_of_monic_irreducible hHm hHirr
  show efPair h = (e' * (efPair H).1, (efPair H).2)
  exact efPair_eq_scale hHm hHd hf hdeg

end Reduction

/-! ## §5 — THE NAMED REMAINDER, CORRESPONDENCE FORM: the exact open content -/

section Correspondence

/-- **THE OM FACTOR CORRESPONDENCE at depth `D`** — the exact remaining open content
of `CellTypeScalingAt D`: under precisely the named Prop's hypotheses (full-span
lattice + deep box), the monic irreducible factors of `g` over `O` are matched — as a
multiset relation — with the monic irreducible factors of the transform over the
recentring ring, each matched pair `(h, H)` carrying the two tower reads
`inertiaDegOf h = inertiaDegOf H` (the `f`-leg: `f(K'/K) = 1`) and
`natDegree h = e' · natDegree H` (the `e`-leg: `e(K'/K) = e'`).  §4's reduction shows
this — and nothing more — is what the deep-wild cite must supply: every `(e, f)` read
downstream of the correspondence is machine-checked (§2–§4). -/
def FactorCorrespondenceAt (D : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π w : O, Irreducible π → IsLocalRing.residue O w ≠ 0 →
  ∀ e' : ℕ, 2 ≤ e' →
  ∀ [IsDomain (AdjoinRoot (eisKey π w e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))],
  ∀ g : Polynomial O, g.Monic → g.natDegree = e' * D →
    (∀ j, j < e' * D → π ^ ((e' * D - j + (e' - 1)) / e') ∣ g.coeff j) →
    (∀ t, t < D → (AdjoinRoot.root (eisKey π w e')) ^ (e' * (D - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') g t)) →
    Multiset.Rel
      (fun h H => inertiaDegOf h = inertiaDegOf H ∧ h.natDegree = e' * H.natDegree)
      (monicFactors g) (monicFactors (devT (eisKey π w e') D g))

/-- ★★★ **THE REDUCTION OF THE NAMED PROP**: the correspondence fires
`CellTypeScalingAt D` — at EVERY depth, uniformly in `q, e', D`.  With this, the
deep-wild remainder of DTR's decision transport is exactly `FactorCorrespondenceAt D`
at `D ≥ 2`: strictly weaker than the named Prop's raw form, since all type/`(e, f)`
bookkeeping is discharged by §2–§4's machine-checked transport. -/
theorem cellTypeScalingAt_of_factorCorrespondence {D : ℕ}
    (hFC : FactorCorrespondenceAt D) : CellTypeScalingAt D := by
  intro O _ _ _ _ _ π w hπ hw e' he' _ _ g hg hdeg hlat hbox
  have he'' : 0 < e' := by omega
  have hkeyd : 0 < (eisKey π w e').natDegree := by
    rw [eisKey_natDegree he'']
    omega
  have hdeg' : g.natDegree = (eisKey π w e').natDegree * D := by
    rw [eisKey_natDegree he'']
    exact hdeg
  obtain ⟨hGm, _⟩ := devT_monic (eisKey_monic he'') hkeyd hg hdeg'
  exact typeOf_eq_scaleType_of_rel hGm (hFC O π w hπ hw e' he' g hg hdeg hlat hbox)

/-- The correspondence cite (the strictly smaller trusted surface) fires the SAME
gate-(b) statement as §1's raw form: a signed correspondence axiom at `D ≥ 2` yields
`DeepWildTypeScalingStatement`, hence (through §1's wiring) the COMPLETE pointwise
law `CellTypeScaling`. -/
theorem deepWildTypeScaling_of_correspondence
    (hcorr : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D) :
    DeepWildTypeScalingStatement :=
  fun D hD => cellTypeScalingAt_of_factorCorrespondence (hcorr D hD)

end Correspondence

/-! ## §6 — CONSUMER SOCKETS: what the signed cite fires (either surface) -/

section Consumers

open Uniformity.Density.IFCG44 (alphaBox)

-- NOTE (ER4's universe fence, third contact): the named Prop quantifies `O : Type`
-- (ZcURLim's convention), so its consumers live in a `{O : Type}` section.
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π w : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- ★★ **THE TRANSPORT SOCKET, cite form** — the assembly unit's entry point: with the
gate-(b) cite signed (either surface), DTR's decision-transport iff fires at EVERY
depth `D` — no `CellTypeScalingAt` premise survives.  This is the exact statement the
face/centre partition assembly consumes on the composite-mass `PowerFullSpanLaw`
census front. -/
theorem transport_decidedAt_iff_of_cite (hcite : DeepWildTypeScalingStatement)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {D N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  transport_decidedAt_iff (cellTypeScaling_of_cite hcite D) hπ hw he' hDN hF hbox σ'

/-- The same socket from the CORRESPONDENCE surface (the strictly smaller trusted
statement of §5). -/
theorem transport_decidedAt_iff_of_correspondence
    (hcorr : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {D N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  transport_decidedAt_iff_of_cite (deepWildTypeScaling_of_correspondence hcorr)
    hπ hw he' hDN hF hbox σ'

end Consumers

section DdSupply

/-- ★ **The `D = 2` supply for ER4's dd terms** (`e1DdDecFam σ`: mass 4, `e' = 2`,
`D = 2`, key `X² − bπ`) — the exact depth instance the order-2 census families consume,
from either cite surface.  (The `ZcURLim (e1DdDecFam σ)` limits themselves additionally
need the face/centre partition assembly — a separate unit; this is the pointwise leg.) -/
theorem cellTypeScalingAt_two_of_cite (hcite : DeepWildTypeScalingStatement) :
    CellTypeScalingAt 2 :=
  hcite 2 (le_refl 2)

/-- The `D = 2` supply from the correspondence surface. -/
theorem cellTypeScalingAt_two_of_correspondence
    (hcorr : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D) :
    CellTypeScalingAt 2 :=
  deepWildTypeScaling_of_correspondence hcorr 2 (le_refl 2)

end DdSupply

end Uniformity.Density.IFCG48

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.IFCG48.cellTypeScalingAt_zero
#print axioms Uniformity.Density.IFCG48.cellTypeScaling_of_cite
#print axioms Uniformity.Density.IFCG48.eis_addVal_algebraMap
#print axioms Uniformity.Density.IFCG48.eis_addVal_norm
#print axioms Uniformity.Density.IFCG48.eis_addVal_norm_tower
#print axioms Uniformity.Density.IFCG48.normValues_eq_of_algEquiv
#print axioms Uniformity.Density.IFCG48.inertiaDegOf_eq_of_algEquiv
#print axioms Uniformity.Density.IFCG48.natDegree_eq_of_algEquiv
#print axioms Uniformity.Density.IFCG48.efPair_eq_scale
#print axioms Uniformity.Density.IFCG48.efPair_scaled_of_algEquiv
#print axioms Uniformity.Density.IFCG48.typeOf_eq_scaleType_of_rel
#print axioms Uniformity.Density.IFCG48.cellTypeScalingAt_of_factorCorrespondence
#print axioms Uniformity.Density.IFCG48.deepWildTypeScaling_of_correspondence
#print axioms Uniformity.Density.IFCG48.transport_decidedAt_iff_of_cite
#print axioms Uniformity.Density.IFCG48.transport_decidedAt_iff_of_correspondence
#print axioms Uniformity.Density.IFCG48.cellTypeScalingAt_two_of_cite
#print axioms Uniformity.Density.IFCG48.cellTypeScalingAt_two_of_correspondence
end AxCheck
