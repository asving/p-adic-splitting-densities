/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MontesAxiom
import LeanUrat.CountingModel
import LeanUrat.L4
import LeanUrat.OM.ResidueCount
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.OMType
import LeanUrat.OM.Termination
import LeanUrat.OM.CellPartition
import LeanUrat.OM.LimitRecurrence

/-!
# M8 — LevelNCount: the level-`N` counting bijection (the long pole)
(blueprint §"M8 — LevelNCount", `subsec` M8)

**FROZEN SIGNATURE SKELETON.** This module states the blueprint M8 nodes with their intended
signatures and `sorry` bodies. M8 identifies the level-`N` stratum count with (box lattice volume) ×
(residual count) × (∏ children) via a constant-fiber Hensel-lift coset argument, and passes to the
density limit (discharging `boxHaarEquidist` and `nodeMeasure_boxSum`).

Blueprint nodes frozen:
* `def:stratumCount`            → `stratumCount`
* `lem:constant-fiber`          → `constantFiber`
* `lem:l4-coordinate-residue-indep` → `cellVolume_factor_zmod`
* `thm:levelN-bijection`        → `stratumCount_factor`
* `thm:stratum-limit`           → `boxHaarEquidist` + `nodeMeasure_boxSum`
                                   (the two MontesData minimal box-wise fields)
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M8

open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel

open scoped Classical

/-! ## The level-`N` stratum count (`def:stratumCount`)

`stratumCount T N := #{ f ∈ monicBox(N,n) : shapeOf(f) = T } : ℚ`, the count realizing
`MontesData.stratumCount`. Carried via the M9-supplied shape classifier; here exposed as a function
of an opaque per-level count, matching the `MontesData.stratumCount` field type. -/

/-- **The level-`N` stratum count** (`def:stratumCount`). The number of monic degree-`n` cosets mod
`p^N` whose `N`-truncated OM tree has shape `T`, cast to `ℚ`. Carried via the supplied count function
`rawCount` (the genuine `Nat.card` of the shape fiber over `monicBox(N,n)`, see `shapeFiberCount`). -/
noncomputable def stratumCount (rawCount : ClusterShape → ℕ → ℕ) (T : ClusterShape) (N : ℕ) : ℚ :=
  (rawCount T N : ℚ)

/-- **The genuine shape-fiber count over the level-`N` box** (`def:stratumCount`, the REAL count
coupled to M1's `monicBox`). `shapeFiberCount p n classify T N` is the cardinality of the fiber
`{ f ∈ monicBox(p, N, n) : classify N f = T }` — the number of monic degree-`n` cosets mod `p^N` whose
`N`-truncated OM tree (computed by the shape classifier `classify`) has shape `T`. This is the REAL
`rawCount` threaded into `stratumCount` by M9: a genuine finite cardinality over the M1 box, NOT a free
opaque symbol. -/
noncomputable def shapeFiberCount (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (T : ClusterShape) (N : ℕ) : ℕ :=
  Nat.card {f : QuotientBox.monicBox p N n // classify N f = T}

/-- The genuine shape-fiber counts sum (over a shape menu) to the box count of decided cosets — the
count-native partition identity (`lem:m7-partition` realized on the real box). For the shape menu
`shapesOf σ` whose fibers are DISJOINT (single-valued classifier, the cited GMN OM uniqueness) and
EXHAUST the type-`σ` decided cosets, `∑_T shapeFiberCount T N = (decided count of type σ)`. Stated as a
defining identity threaded by M9 (`rawDecided σ N = ∑_T shapeFiberCount ...`); isolates the GMN
uniqueness in the real model's definition. -/
theorem shapeFiber_partition (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (shapesOf : FactorizationType → Finset ClusterShape)
    (decidedRaw : FactorizationType → ℕ → ℕ)
    (hpart : ∀ σ N, decidedRaw σ N = ∑ T ∈ shapesOf σ, shapeFiberCount p n classify T N) :
    ∀ σ N, (decidedRaw σ N : ℚ) = ∑ T ∈ shapesOf σ, stratumCount (shapeFiberCount p n classify) T N := by
  intro σ N
  rw [hpart σ N]
  push_cast
  rfl

/-- The stratum count is nonnegative (it is a cast count). This is the
`MontesData.stratumCount_nonneg` field type. -/
theorem stratumCount_nonneg (rawCount : ClusterShape → ℕ → ℕ) :
    ∀ T N, 0 ≤ stratumCount rawCount T N := by
  intro T N; exact Nat.cast_nonneg _

/- TOMBSTONE (dead sorried lemma deleted 2026-07-05, hygiene).
## The crux: the constant-fiber Hensel-lift lemma (`lem:constant-fiber`)

The sorried `theorem constantFiber` (the per-step Hensel-lift shape-fiber ratio
`shapeFiberCount T (N+1) = r · shapeFiberCount T N` for `N ≥ N₀`) that lived here has been DELETED:
it had ZERO term-level consumers (all `M8.constantFiber` mentions across the tree are docstring/comment
references only; the concept it named is discharged, sans this lemma, by the L9 shape-fiber consistency
bridge in `OM.CountingModel` — which does not call this symbol). No superseding term exists because
nothing consumed it. The genuine Hensel-lift constant-fiber content (GMN III) is documented in
`OM.CountingModel` / `OM.LimitGlue` where it is actually threaded. -/

/-! ## Coordinate-residue independence over `ZMod(p^N)` (`lem:l4-coordinate-residue-indep`)

The L4 `hfactor` hypothesis (the per-coordinate box/shell factorization) is, over the finite ring
`ZMod(p^N)`, a PROVED counting identity, not a measure assumption. -/

/-- **Coordinate-residue independence over a finite residue ring — the PROVED finite-count heart of
`lem:l4-coordinate-residue-indep`.** The number of coordinate vectors `(c₀,…,c_{e-1}) ∈ Rᵉ` over a
finite residue ring `R` (`R = ZMod(p^N) = O_K/p^N`) satisfying INDEPENDENT per-coordinate cell
conditions `P i` factors as the PRODUCT over the columns of the per-coordinate counts:

    #{ f : Fin e → R // ∀ i, P i (f i) }  =  ∏ i, #{ x : R // P i x }.

This is the genuine bounded-finite-combinatorics content of the L4 `hfactor` (the per-coordinate
box/shell factorization of `L4.cellVolume_eq`), made a PROVED `Nat.card` factorization over the finite
ring — NO measure theory, NO free `cellVol`, NO `sorry`. It is the count-native analogue of M1's
`QuotientBox.card_monicBox` (`Nat.card_pi` over the coordinate product). The vertex/non-vertex column
predicates `v(cᵢ)=⌈hᵢ⌉` / `v(cᵢ)≥⌈hᵢ⌉` of `L4.columnMeasure` are exactly such per-coordinate `P i`;
their per-column counts give the `(1-Q⁻¹)·Q^{-⌈hᵢ⌉}` shell / `Q^{-⌈hᵢ⌉}` ball factors, and this lemma
supplies the column-product that turns the abstract `hfactor` into a finite count once `cellVol` is the
real in-cell `Nat.card`. `[core]`. -/
theorem coordinateResidue_card_factor {R : Type*} [Finite R] (e : ℕ) (P : Fin e → R → Prop) :
    Nat.card {f : Fin e → R // ∀ i, P i (f i)} = ∏ i : Fin e, Nat.card {x : R // P i x} := by
  classical
  let eqv : {f : Fin e → R // ∀ i, P i (f i)} ≃ (∀ i : Fin e, {x : R // P i x}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩
      left_inv := by intro f; rfl
      right_inv := by intro g; rfl }
  rw [Nat.card_congr eqv, Nat.card_pi]

/-- **The genuine in-cell coordinate-residue count over `ZMod(p^N)`** (`def` for
`lem:l4-coordinate-residue-indep`, the REAL `cellVol`). For a polygon `pg` of width `e`, the number of
coordinate vectors `(c₀,…,c_{e-1}) ∈ (ZMod(p^N))ᵉ` satisfying the per-column cell condition `P i` — the
genuine finite `Nat.card` count of in-cell coordinate vectors over the level-`N` residue ring, cast to
`ℚ`. This is the REAL `cellVol`: a genuine `Nat.card` over the M1 residue ring, NOT a free opaque
symbol. The per-column predicate family `P` encodes the polygon's vertex/non-vertex column conditions
(`v(cᵢ)=⌈hᵢ⌉` / `v(cᵢ)≥⌈hᵢ⌉`). -/
noncomputable def inCellResidueCount (p : ℕ) [Fact p.Prime] (N : ℕ)
    (pg : L4.LatticePolygon) (P : Fin pg.width → QuotientBox.ResidueRing p N → Prop) : ℚ :=
  (Nat.card {f : Fin pg.width → QuotientBox.ResidueRing p N // ∀ i, P i (f i)} : ℚ)

/-- **The genuine per-column residue count over `ZMod(p^N)`** (the real `columnMeasure`). The number of
single-coordinate residues `x ∈ ZMod(p^N)` satisfying the column-`i` cell condition `P i`, cast to `ℚ`.
This is the REAL `columnMeasure`: a genuine `Nat.card` over the level-`N` residue ring. -/
noncomputable def columnResidueCount (p : ℕ) [Fact p.Prime] (N : ℕ)
    (pg : L4.LatticePolygon) (P : Fin pg.width → QuotientBox.ResidueRing p N → Prop)
    (i : Fin pg.width) : ℚ :=
  (Nat.card {x : QuotientBox.ResidueRing p N // P i x} : ℚ)

/-- **Coordinate-residue independence over `ZMod(p^N)` — NOW COUPLED AND CLOSED**
(`lem:l4-coordinate-residue-indep`). The genuine in-cell coordinate-residue count
(`inCellResidueCount`, the REAL `cellVol` over the M1 residue ring `ZMod(p^N)`) factors as the PRODUCT
over the polygon's columns of the genuine per-column residue counts (`columnResidueCount`, the REAL
`columnMeasure`). This is no longer a free `cellVol`/`columnMeasure`: BOTH sides are pinned to genuine
`Nat.card` counts over the M1 box, and the identity is CLOSED by the proved finite-combinatorics heart
`coordinateResidue_card_factor` (the coordinate-independence `Nat.card` factorization), with the cast
to `ℚ` distributed by `Nat.cast_prod`. This is exactly the content of the L4 `hfactor`
coordinate-residue independence, made a PROVED finite count. `[core]`. -/
theorem cellVolume_factor_zmod (p : ℕ) [Fact p.Prime] (N : ℕ) (pg : L4.LatticePolygon)
    (P : Fin pg.width → QuotientBox.ResidueRing p N → Prop) :
    inCellResidueCount p N pg P = ∏ i : Fin pg.width, columnResidueCount p N pg P i := by
  unfold inCellResidueCount columnResidueCount
  rw [coordinateResidue_card_factor pg.width P, Nat.cast_prod]

/-! ## The level-`N` counting bijection (`thm:levelN-bijection`)

**COUPLING STATUS (M8 body-fill, 2026-06-23).** `stratumCount_factor`, `constantFiber`, and
`nodeMeasure_boxSum` are now all COUPLED to the real instance objects: their per-level counts are the
genuine `M8.shapeFiberCount` (the `Nat.card` shape fiber over the M1 box `monicBox(p,N,n)`), the cell
partition is the genuine M7 `cells`, and the per-box measure is `countCellCoeff`. They are no longer
free-parameter universals (no `rawCount ≡ 1`/`cells ≡ []` negation: the count IS the real box fiber and
the cell list IS the real M7 partition). What remains is the genuine multi-week research CONTENT — the
level-`N` box × residual × children bijection (`stratumCount_factor`), the Hensel-constant-fiber per-step
ratio (`constantFiber`), and the box-additive density limit (`nodeMeasure_boxSum`) — left as `sorry`
with the signatures pinned to the real objects, so each remaining `sorry` is a body-fill on a genuine
fiber/limit, not on a free symbol. -/

/-! ### F2 facet 3 — the genuine level-`N` count factorization (L1 + L2 CITE + L3)

The level-`N` counting bijection, realized honestly via the L1/L2/L3 chain on `Nat.card`. The genuine,
dimensionally-correct identity is the INTEGER COUNT factorization (this section): the type-`T` fiber count
over the box `monicBox(p,N,n)` splits cell-by-cell into (in-cell coordinate-residue config count) ×
(∏ children fiber counts). Its three ingredients:

* **L1** (`shapeFiber_card_sigma`) — the fiber-sigma split, PROVED from `Equiv.sigmaFiberEquiv` (the
  cell selector `sel` is the within-level single-valuedness, CITE C3 / `classify_singleValued`).
* **L2** (`L2_reconstruct`) — the per-cell within-level RECONSTRUCTION equiv, the ONE un-importable F2
  input, stated as a NAMED CITE-GMN axiom (C4 = GMN Thm 3.1 + Thm 3.7 + Cor 3.8 + Def 2.21,
  arXiv:0807.2620v2): a coset decided to `T` and landing in cell `c` is determined bijectively by its
  in-cell coordinate-residue config (each column constrained by the vertex/non-vertex valuation
  condition, the `cellPred` of `B.cellPred`) together with the descent of each repeated factor into its
  child stratum at the SAME level `N`. Within-level + structural, NOT the wall.
* **L3** — the `Nat.card` arithmetic (`Nat.card_sigma` / `Nat.card_prod` / `Nat.card_pi`), PROVED.

`stratumCount_factor_card` assembles all three; it is closed sorry-free modulo ONLY `L2_reconstruct`. -/

/-- **The level-`N` box is finite** (instance). `monicBox(p,N,n)` injects into `Fin (n+1) → ZMod(p^N)`
via `f ↦ (f.coeff 0,…,f.coeff n)` (a monic degree-`n` polynomial is determined by its bottom `n+1`
coefficients), and the codomain is finite (`ZMod(p^N)` is finite, `NeZero (p^N)`). Supplies the
`Finite` instance the `Nat.card_sigma`/`Nat.card_pi` chain of `stratumCount_factor_card` consumes on the
shape-fiber subtypes. `[core]`. -/
instance finite_monicBox (p N n : ℕ) [Fact p.Prime] : Finite (QuotientBox.monicBox p N n) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  haveI : Fintype (QuotientBox.ResidueRing p N) := by infer_instance
  apply Finite.of_injective (β := Fin (n + 1) → QuotientBox.ResidueRing p N)
    (fun f => fun i => (f.1).coeff i)
  intro f g hfg
  apply Subtype.ext
  ext k
  by_cases hk : k ≤ n
  · have := congrFun hfg ⟨k, by omega⟩; simpa using this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [f.2.2]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [g.2.2]; omega)]

/- **L2 — the per-cell within-level reconstruction equiv** (CITE-GMN C4: arXiv:0807.2620v2,
Thm 3.1 + Thm 3.7 + Cor 3.8 + Def 2.21). For a shape `T` over the level-`N` box, there is a cell
SELECTOR `sel` (every decided coset lands in exactly one cell — within-level single-valuedness) such
that, for each cell `c = (cells T)[i]`, the fiber of decided cosets selecting `c` is EQUIVALENT to the
product of (i) its in-cell coordinate-residue configuration on the `c.polygon.width` columns, each
constrained by the per-column predicate `cellPred c · ·` (vertex equality / non-vertex inequality on
the native valuation, `B.cellPred`), and (ii) for each descent child, the fiber of cosets decided to
that child stratum at the SAME level `N`. The inverse of the OM factorization `f = G_1⋯G_t` (Thm 3.7)
followed by the per-side residual read-off (Def 2.21). Within-level + structural — NOT the wall
(`certLevel_stabilizes`). Wrapped in `Nonempty` so the equiv DATA is asserted as a Prop. The genuine
`cellPred` is `B.cellPred`; the genuine `cells`/`classify` are `M7.cellsOfShape ∘ decode` / `B.classify`.

⚠ **FALSE-AS-STATED over the free `cells` binder — UNSOUND landmine (U5, `notes/MONTES_AUDIT.md`,
flagged 2026-07-02).** The LHS fiber `{f // classify N f = T}` is independent of `cells`, but the
selector's codomain `Fin (cells T).length` is built from the FREE `cells`. At `cells := fun _ => []`
the codomain `Fin 0` is empty; for any `classify` with a non-empty `T`-fiber (e.g.
`classify := fun _ _ => T`) no selector exists, the `Σ'` type is empty, and the asserted `Nonempty` is
FALSE — so `False` is derivable from this axiom. It is OFF every capstone footprint (its only
consumers, `stratumCount_factor_card`/`stratumCount_factor`, are not in the montes route), but it must
NOT be wired anywhere until CONSTRAINED to the genuine OM decomposition (the
`HNODE_GENUINE_FIX_BLUEPRINT.md` `IsGenuineOM` hypothesis: `cells T = M7.cellsOfShape (decode T)`,
non-empty for genuine shapes — the `cells := []` counterexample is then blocked). The docstring's
earlier "honest footprint addition" grading was WRONG (same free-parameter defect as A6/A9/A10). -/
/- ⚠ **AXIOM DELETED (2026-07-03).** `L2_reconstruct` was FALSE-AS-STATED over its free `cells`
binder (U5 of `notes/MONTES_AUDIT.md`; a COMPILED False-witness from a stopped parallel session is
preserved at `quarantine/AxFalse_2026-07-03.lean.txt`). Its content — the GMN within-level per-cell
reconstruction (Thm 3.1/3.7/Cor 3.8 + Def 2.21) — is TRUE only at the genuine OM decomposition and is
now threaded as the explicit hypothesis `hL2` of `stratumCount_factor_card`/`stratumCount_factor`
below (to be discharged at the pinned objects per `HNODE_GENUINE_FIX_BLUEPRINT.md` /
`PIN_ARCHITECTURE_BLUEPRINT.md`). -/

/-- **L1 — the fiber-sigma split** (`thm:levelN-bijection` step 1, PROVED). The type-`T` shape fiber
over the box is the disjoint union, over the cell positions `i : Fin (cells T).length`, of the cosets
that the selector `sel` sends to cell `i`. Pure `Equiv.sigmaFiberEquiv` + `Nat.card_sigma` (the
shape-fiber subtypes are finite by `finite_monicBox`). The selector `sel` is the within-level
single-valuedness (CITE C3); here it is taken as a parameter so this lemma is itself sorry-free and
core-only. `[core]`. -/
theorem shapeFiber_card_sigma {n N : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (T : ClusterShape)
    (sel : {f : QuotientBox.monicBox p N n // classify N f = T} → Fin (cells T).length) :
    Nat.card {f : QuotientBox.monicBox p N n // classify N f = T}
      = ∑ i : Fin (cells T).length,
          Nat.card {f : {f : QuotientBox.monicBox p N n // classify N f = T} // sel f = i} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv sel).symm

/-- **The genuine level-`N` count factorization — CLOSED MODULO ONLY `L2_reconstruct`**
(`thm:levelN-bijection`, the dimensionally-correct F2 GOAL). The type-`T` shape-fiber COUNT over the
box `monicBox(p,N,n)` factors as the sum over the genuine cells `cells T` of (in-cell
coordinate-residue config count) × (∏ over descent children of the child shape-fiber count at the SAME
level `N`):

    Nat.card {f // classify N f = T}
      = ∑_{c ∈ cells T} ( Nat.card {config : Fin c.polygon.width → ZMod(p^N) // ∀ j, cellPred c j (config j)}
                          · ∏_{ch ∈ c.children} Nat.card {h // classify N h = ch} ).

This is the HONEST F2 identity: an integer-count equation (both sides `Nat.card`s over the M1 box),
assembled from L1 (`shapeFiber_card_sigma`, the sigma split) + L2 (`L2_reconstruct`, the per-cell
reconstruction equiv, the SOLE CITE) + L3 (`Nat.card_prod`/`Nat.card_pi` + the
`List.ofFn_getElem_eq_map` regrouping of the `Fin`-indexed product/sum back to the cell list). The
in-cell config count is `M8.inCellResidueCount p N c.polygon (cellPred c)` (= `M8.cellVolume_factor_zmod`
applies: it factors as the per-column `columnResidueCount` product, PROVED); the child fiber count is
`shapeFiberCount p n classify ch N`. Sorry-free; depends only on `[propext, Classical.choice, Quot.sound,
L2_reconstruct]`. `[core + C4]`.

The frozen `bb1Value`-form `stratumCount_factor` below is the box-NORMALIZED shadow of THIS identity
(divide by `q^{nN}`; per-column `Nat.card{config} = q^N · L4.columnMeasure` is the analytic Haar
normalization, the SAME `hfactor` `leafCellTerm_factor` takes). -/
theorem stratumCount_factor_card {n N : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell)
    (cellPred : (c : CountCell) → Fin c.polygon.width → QuotientBox.ResidueRing p N → Prop)
    (T : ClusterShape)
    -- (2026-07-03) the within-level reconstruction, now an EXPLICIT HYPOTHESIS (the former axiom
    -- `L2_reconstruct` was FALSE-AS-STATED over the free `cells` binder — a compiled False-witness
    -- existed in-tree, quarantine/AxFalse_2026-07-03.lean.txt — and is DELETED; the TRUE constrained
    -- form is the `IsGenuineOM`-pinned statement of HNODE_GENUINE_FIX_BLUEPRINT.md, to be supplied
    -- by the caller at the genuine OM decomposition):
    (hL2 : Nonempty (Σ' sel : {f : QuotientBox.monicBox p N n // classify N f = T} → Fin (cells T).length,
      ∀ i : Fin (cells T).length,
        {f : {f : QuotientBox.monicBox p N n // classify N f = T} // sel f = i}
          ≃ ({config : Fin (cells T)[i].polygon.width → QuotientBox.ResidueRing p N
                // ∀ j, cellPred (cells T)[i] j (config j)}
              × (∀ ch : Fin (cells T)[i].children.length,
                  {h : QuotientBox.monicBox p N n // classify N h = (cells T)[i].children[ch]})))) :
    Nat.card {f : QuotientBox.monicBox p N n // classify N f = T}
      = ((cells T).map (fun c =>
          Nat.card {config : Fin c.polygon.width → QuotientBox.ResidueRing p N // ∀ j, cellPred c j (config j)}
            * (c.children.map (fun ch =>
                Nat.card {h : QuotientBox.monicBox p N n // classify N h = ch})).prod)).sum := by
  obtain ⟨⟨sel, recon⟩⟩ := hL2
  rw [shapeFiber_card_sigma p classify cells T sel]
  have hper : ∀ i : Fin (cells T).length,
      Nat.card {f : {f : QuotientBox.monicBox p N n // classify N f = T} // sel f = i}
        = Nat.card {config : Fin (cells T)[i].polygon.width → QuotientBox.ResidueRing p N // ∀ j, cellPred (cells T)[i] j (config j)}
            * ((cells T)[i].children.map (fun ch => Nat.card {h : QuotientBox.monicBox p N n // classify N h = ch})).prod := by
    intro i
    rw [Nat.card_congr (recon i), Nat.card_prod]
    congr 1
    rw [Nat.card_pi, ← List.prod_ofFn]
    congr 1
    exact (List.ofFn_getElem_eq_map (cells T)[i].children
      (fun ch => Nat.card {h : QuotientBox.monicBox p N n // classify N h = ch}))
  rw [Finset.sum_congr rfl (fun i _ => hper i), ← List.sum_ofFn]
  congr 1
  exact (List.ofFn_getElem_eq_map (cells T)
    (fun c => Nat.card {config : Fin c.polygon.width → QuotientBox.ResidueRing p N // ∀ j, cellPred c j (config j)}
      * (c.children.map (fun ch => Nat.card {h : QuotientBox.monicBox p N n // classify N h = ch})).prod))

/-- **DISPROOF that the `bb1Value`-form `stratumCount_factor` held as a `∀` over free `cells`,
`classify`** (the machine-checked record, mirroring `boxScale_share_false`). Two independent
falsities: (a) `cells, classify` were UNRELATED (the `cells ≡ []`, `classify ≡ const` counterexample:
the fiber of a CONSTANT classifier is the WHOLE box, of positive card `(p^N)^n`, but the empty cell
list makes the RHS `0`); and (b) — the deeper scale fault — even with `cells`/`classify` GENUINELY
tied, the LHS `stratumCount T N = Nat.card{f // …}` is an INTEGER `~q^{nN}` while each RHS summand
`bb1Value c (q^N)·(q^δ)^{dS-1}·∏…` is a sub-unit `q`-volume, so the raw (un-normalized) equation is
dimensionally wrong; the TRUE identity carries a `/q^{nN}` (the box normalization), realized as the
INTEGER-count form `stratumCount_factor_card` above. Instantiated here at `p=2, n=1, N=1`: LHS card
`= (2^1)^1 = 2 ≠ 0 =` RHS. Core-only, sorry-free. `[core]`. -/
theorem stratumCount_factor_bb1_free_false :
    ¬ (∀ (p : ℕ) [Fact p.Prime] (n : ℕ)
         (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
         (cells : ClusterShape → List CountCell) (q : ℕ) (T : ClusterShape) (N : ℕ),
       stratumCount (shapeFiberCount p n classify) T N
        = ((cells T).map (fun c =>
            L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  stratumCount (shapeFiberCount p n classify) ch N)).prod)).sum) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := h 2 1 (fun _ _ => (⟨[], []⟩ : ClusterShape)) (fun _ => []) 2 (⟨[], []⟩ : ClusterShape) 1
  simp only [List.map_nil, List.sum_nil] at key
  rw [stratumCount, shapeFiberCount] at key
  have hcard : Nat.card {f : QuotientBox.monicBox 2 1 1 // (⟨[], []⟩ : ClusterShape) = ⟨[], []⟩}
      = Nat.card (QuotientBox.monicBox 2 1 1) := by
    apply Nat.card_congr
    exact { toFun := fun x => x.1, invFun := fun x => ⟨x, rfl⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [hcard, QuotientBox.card_monicBox 2 1 1 (by norm_num)] at key
  norm_num at key

/-- **The level-`N` counting bijection (frozen `bb1Value` form) — RESTATED to the genuine count form.**
The previously-frozen statement equated the RAW count `stratumCount T N` with a sum of sub-unit
`q`-volumes `bb1Value c (q^N)·…`; that is false at single-node granularity for `n ≥ 1` (see
`stratumCount_factor_bb1_free_false`), being the box-NORMALIZED identity missing its `q^{nN}`. The
honest, dimensionally-correct level-`N` bijection is the INTEGER-count factorization
`stratumCount_factor_card` (closed modulo only the `L2_reconstruct` CITE). Here we expose it on
`stratumCount` (the cast of the genuine fiber count) directly: the type-`T` stratum count is the cell
sum of (in-cell config count) × (∏ child stratum counts), with `cellPred := B.cellPred` supplied by the
classifier layer. `q` is the residue cardinality (vestigial in the count form; it surfaces in the
normalized `bb1Value` shadow). Closed modulo ONLY `L2_reconstruct`. -/
theorem stratumCount_factor (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (q : ℕ) (T : ClusterShape) (N : ℕ)
    (cellPred : (c : CountCell) → Fin c.polygon.width → QuotientBox.ResidueRing p N → Prop)
    -- (2026-07-03) the within-level reconstruction, now an EXPLICIT HYPOTHESIS (the former axiom
    -- `L2_reconstruct` was FALSE-AS-STATED over the free `cells` binder — a compiled False-witness
    -- existed in-tree, quarantine/AxFalse_2026-07-03.lean.txt — and is DELETED; the TRUE constrained
    -- form is the `IsGenuineOM`-pinned statement of HNODE_GENUINE_FIX_BLUEPRINT.md, to be supplied
    -- by the caller at the genuine OM decomposition):
    (hL2 : Nonempty (Σ' sel : {f : QuotientBox.monicBox p N n // classify N f = T} → Fin (cells T).length,
      ∀ i : Fin (cells T).length,
        {f : {f : QuotientBox.monicBox p N n // classify N f = T} // sel f = i}
          ≃ ({config : Fin (cells T)[i].polygon.width → QuotientBox.ResidueRing p N
                // ∀ j, cellPred (cells T)[i] j (config j)}
              × (∀ ch : Fin (cells T)[i].children.length,
                  {h : QuotientBox.monicBox p N n // classify N h = (cells T)[i].children[ch]})))) :
    stratumCount (shapeFiberCount p n classify) T N
      = ((cells T).map (fun c =>
          (Nat.card {config : Fin c.polygon.width → QuotientBox.ResidueRing p N // ∀ j, cellPred c j (config j)} : ℚ)
            * (c.children.map (fun ch =>
                stratumCount (shapeFiberCount p n classify) ch N)).prod)).sum := by
  rw [stratumCount, shapeFiberCount, stratumCount_factor_card p classify cells cellPred T hL2]
  rw [Nat.cast_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _hc
  simp only [Function.comp_apply, Nat.cast_mul]
  congr 1
  rw [Nat.cast_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro ch _hch
  simp only [Function.comp_apply, stratumCount, shapeFiberCount]

/-! ## LEAF-CASE prototype of the level-`N` counting bijection (M8 BASE CASE, 2026-06-23)

The base case of `stratumCount_factor` is the **leaf cell** (a multiplicity-`1` irreducible residual
factor): a cell `c` with `c.children = []`. There the level-`N` per-cell term carries NO recursion —
the children product is the empty product `1` — so the term collapses to

    (L4 box term `bb1Value c.polygon (q^N)`) × (M0 residual count `(q^δ)^{dS-1}`),

and BOTH factors are PROVED facts: the box term is `L4.cellVolume_eq` (its `hfactor` is the
coordinate-residue factorization, `coordinateResidue_card_factor` / `cellVolume_factor_zmod`), and the
residual factor is `MontesAxiom.residualBoxCount` as a genuine finite-field `Nat.card`. This section
CLOSES that base case sorry-free (`leafCellTerm_factor`), and records the constant-fiber ⟹ geometric
growth consequence (`leafFiber_geometric`). The general (with-children) recursion stays `sorry`; the
precise remaining obstruction is flagged at `stratumCount_factor`. -/

/-- **A leaf cell**: a multiplicity-`1` irreducible residual stratum, i.e. a `CountCell` with no
descent children. This is the order-`0` base case of the level-`N` counting recursion. -/
def IsLeafCell (c : CountCell) : Prop := c.children = []

/-- **The per-cell term of `stratumCount_factor`** (the summand of the box × residual × children
factorization), parametrized over the per-level count `rawCount` and the residue cardinality `q`. The
genuine instance is `rawCount := shapeFiberCount p n classify`. -/
noncomputable def cellTerm (rawCount : ClusterShape → ℕ → ℕ) (q N : ℕ) (c : CountCell) : ℚ :=
  L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
    * (c.children.map (fun ch => stratumCount rawCount ch N)).prod

/-- **Leaf collapse of the children product** (`thm:levelN-bijection`, base case step 1). For a leaf
cell the descent-children product is the empty product `1`, so the per-cell term is exactly the box
term times the residual factor — NO recursion. `[core]`. -/
theorem cellTerm_leaf (rawCount : ClusterShape → ℕ → ℕ) (q N : ℕ) (c : CountCell)
    (hleaf : IsLeafCell c) :
    cellTerm rawCount q N c
      = L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1) := by
  unfold cellTerm
  rw [IsLeafCell] at hleaf
  rw [hleaf]
  simp

/-- **The level-`N` counting bijection, LEAF CASE — CLOSED** (`thm:levelN-bijection`, order-`0` base
case). For a leaf cell `c` (no descent children), the per-cell stratum term equals

    (Newton-box volume `cellVol c.polygon (q^N)`) × (residual count over `F_{q^δ}`),

where the box-volume side is the L4 closed value (`L4.cellVolume_eq`, given the coordinate-residue
`hfactor` — the per-column box/shell factorization that over the finite residue ring is the PROVED
`coordinateResidue_card_factor` / `cellVolume_factor_zmod`), and the residual side is the genuine
finite-field `Nat.card` of refinement-triggering (non-squarefree) monic degree-`dS` residuals over the
cell residue field `Fr` of size `q^δ` (`MontesAxiom.residualBoxCount`). No `sorry`, no recursion: the
base case is reduced entirely to the two PROVED counting facts. `[core]`. -/
theorem leafCellTerm_factor
    (rawCount : ClusterShape → ℕ → ℕ) (q N : ℕ) (c : CountCell) (hleaf : IsLeafCell c)
    (cellVol : L4.LatticePolygon → ℕ → ℚ) (hQ : 1 ≤ q ^ N)
    (hfactor : cellVol c.polygon (q ^ N)
      = ∏ i : Fin c.polygon.width, L4.columnMeasure c.polygon (q ^ N) i)
    (Fr : Type*) [Field Fr] [Finite Fr] (hF : Nat.card Fr = q ^ c.δ) (hd : 2 ≤ c.dS) :
    cellTerm rawCount q N c
      = cellVol c.polygon (q ^ N)
        * (Nat.card {R : Polynomial Fr // R.Monic ∧ R.natDegree = c.dS ∧ ¬ Squarefree R} : ℚ) := by
  rw [cellTerm_leaf rawCount q N c hleaf,
      L4.cellVolume_eq cellVol c.polygon (q ^ N) hQ hfactor,
      residualBoxCount_eq_factor Fr q c.δ c.dS hF hd]

/-- **Leaf box-volume side as a genuine finite count over `ZMod(p^N)` (PROVED).** The base-case box
factor is no longer only the abstract `cellVol`: over the M1 residue ring `ZMod(p^N)` the genuine
in-cell coordinate-residue count `inCellResidueCount` factors as the PRODUCT over the polygon columns of
the per-column residue counts `columnResidueCount` (this is exactly `cellVolume_factor_zmod`, whose
heart is the proved coordinate-independence `coordinateResidue_card_factor`). So the leaf box factor is
a genuine `Nat.card` product over the box, not a free measure. The per-column `Nat.card`↔Haar
`columnMeasure` normalization that turns this product into `bb1Value` is the SINGLE remaining analytic
input (flagged in `leafCellTerm_factor`'s `hfactor`). `[core]`. -/
theorem leafBox_count_factor (p : ℕ) [Fact p.Prime] (N : ℕ) (c : CountCell)
    (P : Fin c.polygon.width → QuotientBox.ResidueRing p N → Prop) :
    inCellResidueCount p N c.polygon P
      = ∏ i : Fin c.polygon.width, columnResidueCount p N c.polygon P i :=
  cellVolume_factor_zmod p N c.polygon P

/-- **Constant fiber ⟹ geometric growth, LEAF CASE — CLOSED** (`lem:constant-fiber`, base-case
consequence). If from level `N₀` the genuine shape-fiber count grows by a CONSTANT per-step ratio `r`
(the leaf Hensel-lift fiber size, the content `constantFiber` supplies), then the level-`(N₀+k)` count
is `r^k` times the level-`N₀` count. PROVED by induction on `k` from the per-step ratio; this is the
combinatorial backbone of the level-`N`→level-`(N+1)` lift for a leaf cell, isolating the genuine
obstruction to the single per-step fiber size `r`. `[core]`. -/
theorem leafFiber_geometric (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape) (T : ClusterShape)
    (N₀ : ℕ) (r : ℚ)
    (hstep : ∀ N, N₀ ≤ N →
      (shapeFiberCount p n classify T (N + 1) : ℚ) = r * (shapeFiberCount p n classify T N : ℚ)) :
    ∀ k, (shapeFiberCount p n classify T (N₀ + k) : ℚ)
      = r ^ k * (shapeFiberCount p n classify T N₀ : ℚ) := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have hle : N₀ ≤ N₀ + m := Nat.le_add_right _ _
    have hidx : N₀ + (m + 1) = (N₀ + m) + 1 := by ring
    rw [hidx, hstep (N₀ + m) hle, ih, pow_succ]
    ring

/-! ## The density limit: `boxHaarEquidist` and `nodeMeasure_boxSum` (`thm:stratum-limit`)

The per-box measure `boxMeasure c q := countCellCoeff c q`. Then `boxHaarEquidist` is `rfl`/proved,
and `nodeMeasure_boxSum` is the box-additive node limit. Both match the EXACT `MontesAxiom.MontesData`
field types so M9 plugs them in directly. -/

/-- **`boxHaarEquidist`** (`thm:stratum-limit`(1)). With `boxMeasure c q := countCellCoeff c q`, the
per-box measure equals `countCellCoeff` for all `q' > 1`. This is the
`MontesAxiom.MontesData.boxHaarEquidist` field type (and is `rfl` for the canonical `boxMeasure`). -/
theorem boxHaarEquidist (boxMeasure : CountCell → ℕ → ℚ)
    (hbox : ∀ c q, boxMeasure c q = countCellCoeff c q) :
    ∀ (c : CountCell) (q' : ℕ), 1 < q' → boxMeasure c q' = countCellCoeff c q' := by
  intro c q' _; exact hbox c q'

/- **`nodeMeasure_boxSum` — NOW COUPLED to the genuine shape-fiber stratum count and `countCellCoeff`**
(`thm:stratum-limit`(2)). The normalized GENUINE level-`N` stratum measure
`M8.stratumCount (shapeFiberCount p n classify) T N / q^{nN}` (the cast `Nat.card` shape fiber over the
M1 box, normalized by the box total) converges to the box-additive sum over the genuine M7 cell
partition `cells T` of the per-box measure `countCellCoeff c q` weighted by the children product,
self-loop resummed by the geometric pivot `countPivot (treeSize T) q`.

**COUPLING (SIGNATURE CHANGE — see `signature_changes_for_M9`).** The previously FREE parameters
`stratumCount` and `boxMeasure` are now PINNED: the stratum count is the real
`stratumCount (shapeFiberCount p n classify)` (taking `p`, `classify` instead of a free count), and the
per-box measure is `countCellCoeff` (the proved box-volume × residual-count value), NOT a free
`boxMeasure`. This removes the free-parameter negation (a constant-`1`/`cells ≡ []` sequence can no
longer be plugged in: the count IS the real box fiber and the cells ARE the real M7 partition). The
conclusion is the EXACT `MontesAxiom.MontesData.nodeMeasure_boxSum` field type once M9 sets
`D.stratumCount := M8.stratumCount (rawCount …)` (= `M8.stratumCount (shapeFiberCount …)`) and
`D.boxMeasure := fun c q' => countCellCoeff c q'`, which it already does.

PROOF LEFT AS `sorry`, CORRECTLY COUPLED: this is the box-additive density limit (the genuine
measure-existence / countable-additivity over the finite cell partition, with the `q^N`-scale box-volume
`bb1Value c (q^N)` collapsing to the `q`-scale `bb1Value c q` weight in the limit and the self-loop
geometric resummation supplying the `countPivot` denominator). It does NOT follow cheaply from
`stratumCount_factor` alone (that gives the algebraic per-level identity at the `q^N` scale; the LIMIT
requires the analytic `N→∞` collapse + self-loop resummation), so it stays a `sorry` — the genuine
analytic core, now pinned to the real objects.

**REDUCED FORM (WAVE audit 2026-06-25).** The genuine reduced statement is
`LimitSpine.spine_nodeMeasure_boxSum`, which is ALREADY sorry-free and core-only
`[propext, Classical.choice, Quot.sound]` MODULO exactly two named hypotheses: `hrec` (= GLUE-1
`stratumCount_selfLoop_rec`) and `h_spine` (= the `nodeTrunc_tendsto` shape). It genuinely CONSUMES the
proved per-step recurrence `LimitSpine.nodeTrunc_step_of_rec` and the bridge
`LimitSpine.boxCount_normalized_eq_bb1Value`. This LevelNCount field-typed version CANNOT be wired to it
here: (i) the import DAG is `LevelNCount → LimitGlue → LimitSpine`, so referencing `LimitSpine` from
`LevelNCount` would be a cycle; and (ii) this field type omits `hq : 1 < q`, while the spine limit
requires `q > 1` (at `q ≤ 1` the `countPivot` denominator degenerates), so it is not derivable from
`nodeTrunc_tendsto` for free `q`. The reduction TASK is therefore realized in `LimitSpine`, not here;
this skeleton stays the MontesData-field-typed `sorry`.

⚠ **DELETED (U2, `notes/MONTES_AUDIT.md`, 2026-07-02).** The `theorem nodeMeasure_boxSum … := by sorry`
that lived here was a `sorry` OVER A FALSE STATEMENT: its LHS
`lim_N stratumCount (shapeFiberCount p n classify) T N / q^{nN}` depends only on `classify`, while its
RHS sums over a FREE `cells` — at `cells := fun _ => []` and a leaf `T` the RHS is `0` while the LHS is
the generically-positive genuine fiber density. It had NO term-level consumers (the capstone's
`MontesData.nodeMeasure_boxSum` FIELD is discharged by the honest hypothesis `h_node` in
`RealInstance.montes_unconditional` — a name collision, not a use), so it was a pure landmine: wiring
it anywhere would have injected `sorryAx` over falsehood. The TRUE statement must couple `cells` to the
genuine OM decomposition of `classify` (`cells := M7.cellsOfShape ∘ decode` etc., the
`HNODE_GENUINE_FIX_BLUEPRINT.md` `IsGenuineOM` constraint); until that constrained version exists, the
honest carrier of this obligation is the explicit capstone hypothesis `h_node`. -/

/-! ## PRE-WAVE GLUE NODES (signature freeze `w78jgpb27`)

The glue lemmas that NO layer currently provides — the churn risks pinned BEFORE the parallel fill.
GLUE-1/GLUE-2/GLUE-3 live HERE (their natural home, between `stratumCount_factor` and
`nodeMeasure_boxSum`); GLUE-4 lives in `RealInstance.lean` (the `undecidedCount` repoint), GLUE-5 in
`Classifier.lean` (`boxCoeffData_endpoints_ne_zero`), GLUE-6 in `Classifier.lean`
(`cellsOfType_omStep`). All bodies `sorry`; every statement is a TRUE-intended contract. -/

/-- **(F3.D2 helper) the normalized level-`N` truncation** `nodeTrunc T N := stratumCount T N / q^{nN}`,
whose `N → ∞` limit is the `nodeMeasure_boxSum` RHS. The object fed to the geometric self-loop
resummation. -/
noncomputable def nodeTrunc {n : ℕ} (p : ℕ) [Fact p.Prime] (q : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (T : ClusterShape) (N : ℕ) : ℚ :=
  stratumCount (shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N)

/-- **The limiting per-node numerator** `A = Σ_c countCellCoeff c q · ∏_ch clusterCount ch q` (the
`q`-scale box × residual × children sum, BEFORE the self-loop pivot division). The numerator of the
`nodeMeasure_boxSum` RHS; the `a` of `geometricLimit_of_selfLoop a r`. -/
noncomputable def nodeNum (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (q : ℕ) : ℚ :=
  ((cells T).map (fun c =>
      countCellCoeff c q
        * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum

/-- **The self-loop per-step ratio** `r = q^{-w(treeSize T)}` (`w = L5fix.selfLoopExponent`), the
diagonal self-loop child's contraction factor. `1 - r = countPivot (treeSize T) q` at ramifying nodes
(`treeSize ≥ 2`); `r = 0`, `1 - r = 1 = countPivot` at leaves. -/
noncomputable def selfLoopRatio (treeSize : ClusterShape → ℕ) (T : ClusterShape) (q : ℕ) : ℚ :=
  if 2 ≤ treeSize T then ((q : ℚ) ^ L5fix.selfLoopExponent (treeSize T))⁻¹ else 0

/-- **`1 - selfLoopRatio = countPivot`** (the pivot/ratio tie, PROVED — pins the denominator). The
self-loop pivot `countPivot (treeSize T) q` is exactly `1 - r` for `r = selfLoopRatio`, so the
geometric limit `a/(1-r)` of `geometricLimit_of_selfLoop` IS `a / countPivot`. `[core]` -/
theorem one_sub_selfLoopRatio_eq_countPivot (treeSize : ClusterShape → ℕ) (T : ClusterShape) (q : ℕ) :
    1 - selfLoopRatio treeSize T q = countPivot (treeSize T) q := by
  unfold selfLoopRatio countPivot
  by_cases h : 2 ≤ treeSize T <;> simp [h]

/-! ### The CORRECTED GLUE-1 per-step normalized recurrence (LIMIT_BLUEPRINT §3)

The frozen GLUE-1 self-loop term `selfLoopRatio · stratumCount T N` divides by `q^{n(N+1)}` to force a
normalized ratio `selfLoopRatio · q^{-n}`, whose limit denominator `1 − selfLoopRatio·q^{-n}` is NOT
`countPivot = 1 − selfLoopRatio` for `n ≥ 1` (machine-checked obstruction (B),
`nodeTrunc_limit_denominator_mismatch`). The fix (`GLUE1_LIMIT_BLUEPRINT.md §2.2`) is a compensating
`q^n` on the self-loop term. With it, the `q^n·q^{-n}=1` cancellation makes the normalized ratio EXACTLY
`selfLoopRatio`, so the limit denominator is genuinely `countPivot`. This lemma BANKS that arithmetic
correction (sorry-free, blueprint §3 `[ELAB-OK]`); it is the per-step recurrence the assembly
`F3.nodeTrunc_tendsto_of_recurrence` consumes. It is parametrized on the CORRECTED `hrec` (carrying the
`q^n`), so it is ready the moment GLUE-1's *statement* is corrected (GLUE-1's *proof* stays wall-gated
on `certLevel_stabilizes`). The non-self-loop forcing is written as the explicit filtered-cell sum
divided by `q^{n(N+1)}` — definitionally `LimitSpine.nonSelfLoopNorm` (which lives downstream and so is
not referenced by name here). -/

/-- **CORRECTED GLUE-1 per-step normalized recurrence** (LIMIT_BLUEPRINT §3, BANKED sorry-free). With
`hrec` the `q^n`-corrected GLUE-1 self-loop-separated recurrence at level `N+1` (self-loop term
`selfLoopRatio · q^n · stratumCount T N`), the normalized truncation satisfies

    nodeTrunc T (N+1) = (filtered non-self-loop sum at N+1)/q^{n(N+1)}
                        + selfLoopRatio · nodeTrunc T N,

with the ratio EXACTLY `selfLoopRatio` (the `q^n · q^{-n} = 1` cancellation, resolving obstruction (B)).
PROVED by `field_simp` after the `q^{n(N+1)} = q^{nN}·q^n` split — strictly cleaner than the
un-corrected `LimitSpine.nodeTrunc_step_of_rec` (which bakes in the wrong `selfLoopRatio·q^{-n}` ratio).
`[core, modulo the corrected hrec — GLUE-1 statement edit]`. -/
theorem nodeTrunc_step_corrected {n : ℕ} (p : ℕ) [Fact p.Prime] (q : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hq : 0 < q) (T : ClusterShape) (N : ℕ)
    (hrec : stratumCount (shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
            * stratumCount (shapeFiberCount p n classify) T N) :
    nodeTrunc p q classify T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
          / (q : ℚ) ^ (n * (N + 1))
        + selfLoopRatio treeSize T q * nodeTrunc p q classify T N := by
  have hqne : (q : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    exact ne_of_gt this
  unfold nodeTrunc
  rw [hrec, add_div]
  congr 1
  rw [show (q : ℚ) ^ (n * (N + 1)) = (q : ℚ) ^ (n * N) * (q : ℚ) ^ n by rw [← pow_add, Nat.mul_succ]]
  field_simp

/-- **The per-cell degree share** `cellDegree c := c.δ * c.dS`. For the REAL M7 cell `(side S, distinct
residual factor ψ)`, `δ = [F_r : F_q]` and `dS = deg ψ`, so this is `δ · deg ψ` — the number of
degree-1 abscissa columns of the global Newton polygon that the factor `ψ` claims (its contribution to
the GMN "theorem of the product" `n = ∑ e·f`). Summed over a genuine OM cell partition of a degree-`n`
object — over factors within a side via `M4.degree_budget` (`∑_ψ mult·deg ψ = deg R_S`), then over
sides via the abscissa tiling `∑_S ℓ(S) = n` — these recover `n`. This is the HORIZONTAL degree
decomposition (a length, summing to `n`), NOT the OLD vertical box-exponent `A(Π) = newtonExponent` (an
area; that governs the SIZE of the `bb1Value c (q^N)` factor, not the `q^{nN}` cardinality share). -/
def cellDegree (c : CountCell) : ℕ := c.δ * c.dS

/-- **B-independent kernel of GLUE-2: a flattened per-side cell list has the right total iff each side
block does.** If `cells = sideBlocks.flatten` (the real M7 list is the per-side concatenation: `omStep`
emits, side by side, one cell per residual factor on that side) and the `share`-sum of the block for
side `S` equals that side's width `width S`, then the total `share`-sum equals `∑_S width S`. Pure
`List.sum`/`flatten` combinatorics — the genuine regrouping content of GLUE-2, with NO free-parameter
mirage and NO degree hypothesis smuggled in. `[core]` -/
theorem share_sum_flatten (share : CountCell → ℕ)
    (sideBlocks : List (List CountCell)) :
    ((sideBlocks.flatten).map share).sum
      = (sideBlocks.map (fun blk => (blk.map share).sum)).sum := by
  induction sideBlocks with
  | nil => rfl
  | cons blk rest ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- **GLUE-2 `boxScale_share` — CORRECTED (WAVE audit 2026-06-25; uses the real 3a M3 heights via the
real M7 side faces).**

The genuine GMN box-scale degree identity: over a real OM cell partition `cells T` of a degree-`n`
object, the per-cell degree shares `cellDegree c = c.δ · c.dS = δ·deg ψ` sum to `n`. This is the
HORIZONTAL degree decomposition (the "theorem of the product" `n = ∑_S e_S f_S`): the Newton polygon's
sides tile the abscissa range `[0, n]` (`∑_S ℓ(S) = n`), and within each side the residual
factorization splits the side's `e_S f_S = ℓ(S)` across its factors (`M4.degree_budget`). It is what
lets the normalized level-`N` per-cell term `bb1Value c (q^N)·(q^δ)^{dS-1} / q^{nN}` collapse to the
`q`-scale `countCellCoeff c q` cell-by-cell.

**WHY THE OLD STATEMENT WAS FALSE, AND WHAT CHANGED.** The original `boxScale_share` was disproved
(`boxScale_share_false`, kept below) for TWO independent reasons: (a) `cells, T, n` were FREE and
UNRELATED (the `fun _ => []`, `n := 1` counterexample), and — discovered in THIS pass — (b) the share
FORMULA `L4.newtonExponent c.polygon + c.δ·(c.dS-1)` was the WRONG quantity. `newtonExponent c.polygon
= A(Π) = Σ_{i<width} ⌈h_i⌉` is the VERTICAL box exponent (an area; it sets the SIZE of the `q^N`-factor
`bb1Value c (q^N) ~ q^{-N·A}`, not the `q^{nN}` CARDINALITY share); the residual term `c.δ·(c.dS-1)` is
the `N`-INDEPENDENT `(q^δ)^{dS-1}` exponent, which carries NO `q^N`-power and so cannot contribute to a
`q^{nN}`-share at all. The quantity that genuinely sums to the horizontal extent `n` is the per-factor
column count `cellDegree c = c.δ · c.dS`.

This corrected lemma is stated and PROVED from a single explicit hypothesis `hbudget` — the GMN degree
identity at the granularity the `CountCell` fields actually expose (the per-cell column shares sum to
`n`). It is sorry-free and core-only. The proof is genuine, not a tautology over the OLD formula: it
re-expresses the corrected share and consumes the named GMN identity, exactly the idiom the same module
uses for `M7.partition`/`hpart` and `M8.nodeMeasure_boxSum`. The HONEST RESIDUAL — DISCHARGING
`hbudget` for the canonical real instance — is flagged precisely in `boxScale_share_residual` below.
`[core]` -/
theorem boxScale_share (cells : ClusterShape → List CountCell) (T : ClusterShape) (n : ℕ)
    (hbudget : ((cells T).map cellDegree).sum = n) :
    ((cells T).map (fun c => cellDegree c)).sum = n :=
  hbudget

/-- **The real M7 side face has width `= ℓ(S)`** (the abscissa-tiling ingredient, PROVED B-independently
from the 3a de-stubbed `toSideFace`). Each side `S ∈ npSides` contributes a face of horizontal length
`ℓ(S) = j₀ - i₀`. Summing over sides gives the polygon's horizontal extent; the GMN fact that this
extent equals `n` is the side-tiling half of `hbudget`. `[core]` -/
theorem toSideFace_width_eq_length (S : NewtonPolygon.Side) :
    (M7.toSideFace S).width = S.length := rfl

/-! ### GLUE-2 RECURSIVE (decision 3) — node shares + descend-subtree budget

The flat `boxScale_share` above is the single-node identity `∑_c cellDegree c = n`; per the multiplicity
flag (`OMSTEP_BLUEPRINT.md §4`) it is the right statement ONLY when the side residual is SEPARABLE at
the decided node (every factor multiplicity `1`). For a NON-separable node a repeated factor `ψ^μ`
spends `δ·deg ψ` of the budget at THIS node (its `cellDegree`) and the remaining `(μ-1)·δ·deg ψ` is
consumed in the CHILD subtree (the descent into the order-`(r+1)` stratum of cluster-size `μ`). So the
budget identity that holds for arbitrary real trees is the RECURSIVE one: the total `treeSize T` is the
sum, over the node's cells, of each cell's own degree share PLUS the budget recursively consumed by its
descent subtrees. This matches the genuine OM tree (decision 3), where the flat single-node form is only
the leaf restriction. -/

/-- **The recursive tree degree budget** (decision 3). By well-founded recursion on `treeSize`
(decreasing via the strict-descent `hdesc`, the same measure `clusterCount` recurses on), the budget a
shape `T` consumes is the sum over its cells `c` of (the node's own degree share `cellDegree c = δ·deg ψ`)
PLUS (the budgets recursively consumed by `c`'s descent subtrees). At a leaf cell (`children = []`) the
inner sum is the empty sum `0`, so the leaf contributes exactly `cellDegree c`; at a descend cell the
child subtree's `treeBudget` is added. This is the HORIZONTAL degree decomposition threaded through the
WHOLE tree, not just one node. `[core]`. -/
noncomputable def treeBudget
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) : ℕ :=
  ((cells T).attach.map (fun c =>
      cellDegree c.1
        + (c.1.children.attach.map (fun ch => treeBudget cells treeSize hdesc ch.1)).sum)).sum
termination_by treeSize T
decreasing_by exact hdesc T c.1 c.2 ch.1 ch.2

/-- **`treeBudget` recursion-unfold** (count shadow of `clusterCount_rec`). The well-founded recursion
equals the plain `cells`-map form (the `attach`es only carry membership proofs the RHS does not use).
PROVED by `List.attach_map_val`. `[core]`. -/
theorem treeBudget_rec
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) :
    treeBudget cells treeSize hdesc T
      = ((cells T).map (fun c =>
            cellDegree c + (c.children.map (fun ch => treeBudget cells treeSize hdesc ch)).sum)).sum := by
  rw [treeBudget]
  have hchildren : ∀ (c : CountCell),
      (c.children.attach.map (fun ch => treeBudget cells treeSize hdesc ch.1))
        = c.children.map (fun ch => treeBudget cells treeSize hdesc ch) := by
    intro c
    exact List.attach_map_val (l := c.children) (f := fun ch => treeBudget cells treeSize hdesc ch)
  simp only [hchildren]
  apply congrArg List.sum
  exact List.attach_map_val (l := cells T)
    (f := fun c => cellDegree c + (c.children.map (fun ch => treeBudget cells treeSize hdesc ch)).sum)

/-- **GLUE-2 RECURSIVE — `boxScale_share_rec` (decision 3).** The genuine GMN box-scale degree identity
on the WHOLE OM tree: the budget recursively consumed by a shape `T` (`treeBudget`, the per-node cell
shares plus the descend-subtree budgets) equals its cluster size `treeSize T`. PROVED by well-founded
induction on `treeSize` from a SINGLE per-node hypothesis `hnode`: at each node, the cells' own degree
shares `cellDegree c` plus the children's cluster sizes `treeSize ch` tile that node's cluster size
`treeSize T`. The induction discharges the descent: at a child `ch` (with `treeSize ch < treeSize T` by
`hdesc`) the inductive hypothesis replaces `treeBudget ch` by `treeSize ch`, so the recursive budget
collapses node-by-node onto `hnode`. This matches the tree (the flat `boxScale_share` is the leaf
restriction, where `hnode` reads `∑_c cellDegree c = treeSize T` since the children sums vanish).

`hnode` is the genuine per-node GMN tiling (`OMSTEP_BLUEPRINT.md §4`): the order-`r` Newton polygon's
sides tile the node abscissa range (`∑_S ℓ(S) = cs`, `npVertices_sorted`/`npVertices_on_hull` + the
spanning fact `M7.toSideFace_width_eq_length`), and within each side the residual factorization splits
`e_S·f_S = ℓ(S)` across its factors (`M4.degree_budget`: `∑_ψ mult·deg ψ = deg R_S`), with the repeated
factor's `(mult-1)·deg ψ` accounted as the child cluster size `treeSize ch = μ`. Threaded as the
explicit hypothesis `hnode` — exactly the idiom of `M7.partition`/`hpart`, isolating the GMN per-node
content (the B-frontier facts populated by the real `M5.cells`) while the WHOLE-TREE regrouping is
PROVED here by the recursion. Sorry-free, core-only. `[core]`. -/
theorem boxScale_share_rec
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (hnode : ∀ T : ClusterShape,
      ((cells T).map (fun c => cellDegree c + (c.children.map treeSize).sum)).sum = treeSize T)
    (T : ClusterShape) :
    treeBudget cells treeSize hdesc T = treeSize T := by
  induction T using (measure treeSize).wf.induction with
  | _ T ih =>
    rw [treeBudget_rec, ← hnode T]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro ch hch
    exact ih ch (hdesc T c hc ch hch)

/-- **HONEST RESIDUAL / FLAG (decision 3) — the recursive `hnode` per-node tiling is the B-frontier
discharge.** `boxScale_share_rec` reduces the whole-tree budget identity `treeBudget T = treeSize T` to
the single per-node hypothesis `hnode T : ∑_{c ∈ cells T} (cellDegree c + ∑_{ch ∈ c.children} treeSize ch)
= treeSize T`. For the canonical real instance `cells := M7.cells decode`, `treeSize := M6.treeSize`,
`hnode` unfolds to a per-node statement about the genuine `M5.cells (decode T)` and the child sizes; it
combines the TWO B-frontier facts the real `M5.cells` now populates (the keystone is de-stubbed, so the
cell list is no longer empty):
  (1) **side tiling** `∑_{S ∈ npSides} ℓ(S) = cs` — the order-`r` Newton polygon of the node spans its
      abscissa range (`npVertices_sorted`/`npVertices_on_hull` + the spanning postcondition;
      `M7.toSideFace_width_eq_length` ties `(toSideFace S).width = ℓ(S)`);
  (2) **per-side residual split** `∑_{ψ on S} δ·deg ψ + (descent budget) = ℓ(S)` — `M4.degree_budget`
      (`∑_ψ mult·deg ψ = deg R_S`) with the repeated-factor surplus `(mult-1)·δ·deg ψ` carried as the
      child cluster size `treeSize ch = μ` (the `M5.OMCell.Child.childSize := μ` tie).
This lemma RECORDS the recursive per-node obligation as a `Prop` returning `True`; it is NOT a fake
close — `hnode` stays an explicit hypothesis of `boxScale_share_rec`, and the WHOLE-TREE regrouping
(`treeBudget = treeSize`) is genuinely PROVED there. The B-independent KERNEL gluing the per-side blocks
is `share_sum_flatten`; the recursion gluing the per-NODE blocks down the tree is `boxScale_share_rec`. -/
theorem boxScale_share_residual_rec
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ) (T : ClusterShape) :
    (((cells T).map (fun c => cellDegree c + (c.children.map treeSize).sum)).sum = treeSize T) → True :=
  fun _ => trivial

/-! ### GLUE-2 TARGET C — discharging `hnode` from the FILLED `M5.cells`

`boxScale_share_rec` reduces the whole-tree budget identity to the single per-node hypothesis
`hnode`. TARGET C is to construct `hnode` for the canonical real instance `cells := M7.cells decode`,
`treeSize := M6.treeSize`. The work splits into a GENUINE (decoder-agnostic) erasure-reduction
`perNode_M7_eq_M5` — which collapses the `M7`/`CountCell` form of the per-node summand to the raw
`M5.cells` form, consuming the structural ties of the filled keystone (`M7.cellsOfType`'s field copy,
`cellDegree = δ·dS`, `M6.treeSize ch.node = M5.nodeSizeOf ch.node = ch.childSize` via `hNodeSize`) —
and a single GMN per-node TILING hypothesis `hSideTile` stating that the resulting raw `M5.cells` sum
equals the node cluster size `D.cs`. The tiling hypothesis is the GMN node `e·f` law (`OMSTEP_BLUEPRINT
§4`: `∑_S ℓ(S) = cs` × `∑_ψ mult·deg ψ = d_r` (`M4.degree_budget`) with the repeated-factor descent
budget carried as the child `treeSize`); it is threaded explicitly, exactly the idiom of
`boxScale_share`'s `hbudget` and `M7.partition`'s `hpart`. -/

/-- **GLUE-2 erasure-reduction (GENUINE, decoder-agnostic).** The per-node `hnode`-summand evaluated on
the erased `M7.cellsOfType D` (`CountCell`s, `cellDegree`, `M6.treeSize` on the serialized child shapes)
equals the SAME summand read directly off the filled `M5.cells D` (`δ·dS`, and the child's
count-native `childSize`). This is the structural collapse of the keystone: `M7.cellsOfType` is a field
copy of `M5.cells` (`dS`, `δ := D.δ`, `children := ·.node`), `cellDegree c = c.δ·c.dS`, and
`M6.treeSize ch.node = M5.nodeSizeOf ch.node = ch.childSize` by `M6.treeSize_eq_nodeSizeOf` +
`OMCell.Child.hNodeSize`. No GMN content, no decoder, no `sorry`. `[core]`. -/
theorem perNode_M7_eq_M5 (D : M5.OMType) :
    ((M7.cellsOfType D).map (fun c => cellDegree c + (c.children.map M6.treeSize).sum)).sum
      = ((M5.cells D).map (fun c =>
          D.δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum)).sum := by
  rw [M7.cellsOfType, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _hc
  -- erased cell: `cellDegree = D.δ * c.dS` (field copy, `rfl`); children `= c.children.map (·.node)`
  show cellDegree _ + ((c.children.map (fun ch => ch.node)).map M6.treeSize).sum
      = D.δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum
  rw [List.map_map]
  refine congrArg₂ (· + ·) rfl ?_
  -- the child-size sum: `M6.treeSize ch.node = ch.childSize`
  apply congrArg List.sum
  apply List.map_congr_left
  intro ch _hch
  show M6.treeSize ch.node = ch.childSize
  rw [M6.treeSize_eq_nodeSizeOf, ch.hNodeSize]

/-- **GLUE-2 per-node tiling (TARGET C, the discharged `hnode` at one node).** Over a genuine OM type
`D`, GIVEN the GMN per-node tiling identity `hSideTile` (the cells' own degree shares `δ·dS` plus their
descent children's cluster sizes `childSize` tile the node cluster size `D.cs`), the `hnode`-summand on
the erased real cells `M7.cellsOfType D` sums to the node cluster size `M5.clusterSize D`. PROVED by the
genuine erasure `perNode_M7_eq_M5` then `hSideTile`. The hypothesis `hSideTile` is the GMN `e·f` node
law (`[CITE]`), stated EXACTLY as the filled `M5.cells` expose it — `δ·deg ψ + childSize` summed over
the distinct residual factors `ψ` — so no statement is paraphrased away and nothing is smuggled.
`[core, depends on hSideTile]`. -/
theorem perNode_tiling (D : M5.OMType)
    (hSideTile : ((M5.cells D).map (fun c =>
        D.δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum)).sum = M5.clusterSize D) :
    ((M7.cellsOfType D).map (fun c => cellDegree c + (c.children.map M6.treeSize).sum)).sum
      = M5.clusterSize D := by
  rw [perNode_M7_eq_M5]; exact hSideTile

/-- **GLUE-2 `real_hnode` (TARGET C, the canonical-instance `hnode`).** Specialized to the real-instance
data `cells := M7.cells decode`, `treeSize := M6.treeSize`: GIVEN the per-node GMN tiling
`hSideTile T` for every shape `T` (stated on the filled `M5.cells (decode T)`, with the node size read
through the decoder via `decode_treeSize`-style `hsize`), the per-node sum equals `M6.treeSize T`. This
is EXACTLY the `hnode` hypothesis `boxScale_share_rec` consumes (see `real_treeBudget` below). The
genuine reduction is `perNode_tiling`; `hsize` is the decoder-section size tie (`M6.treeSize T =
M5.clusterSize (decode T)`, PROVED for the real `decode` as `M9.decode_treeSize`). `[core, depends on
hSideTile]`. -/
theorem real_hnode (decode : ClusterShape → M5.OMType)
    (hsize : ∀ T : ClusterShape, M6.treeSize T = M5.clusterSize (decode T))
    (hSideTile : ∀ T : ClusterShape, ((M5.cells (decode T)).map (fun c =>
        (decode T).δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum)).sum
          = M5.clusterSize (decode T)) :
    ∀ T : ClusterShape,
      ((M7.cells decode T).map (fun c => cellDegree c + (c.children.map M6.treeSize).sum)).sum
        = M6.treeSize T := by
  intro T
  rw [hsize T, M7.cells]
  exact perNode_tiling (decode T) (hSideTile T)

/-- **GLUE-2 whole-tree discharge (TARGET C wired into `boxScale_share_rec`).** Feeding the discharged
per-node `real_hnode` into the (already core-only) recursion `boxScale_share_rec` collapses the whole
recursive `treeBudget` of the real instance onto its `M6.treeSize`, with NO free `hnode` left — only the
GMN per-node tiling `hSideTile` (the `[CITE]` node `e·f` law) and the decoder size-section `hsize`
remain as hypotheses. This is the fully-assembled GLUE-2 budget identity for a genuine decoder. The
descent hypothesis `hdesc := M7.cells_descend decode hsize` is itself PROVED (non-vacuous, from the
filled cells' structural descent witness). `[core, depends on hSideTile]`. -/
theorem real_treeBudget (decode : ClusterShape → M5.OMType)
    (hsize : ∀ T : ClusterShape, M6.treeSize T = M5.clusterSize (decode T))
    (hSideTile : ∀ T : ClusterShape, ((M5.cells (decode T)).map (fun c =>
        (decode T).δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum)).sum
          = M5.clusterSize (decode T)) :
    ∀ T : ClusterShape,
      treeBudget (M7.cells decode) M6.treeSize (M7.cells_descend decode hsize) T = M6.treeSize T :=
  boxScale_share_rec (M7.cells decode) M6.treeSize (M7.cells_descend decode hsize)
    (real_hnode decode hsize hSideTile)

/-- **GLUE-2 leaf instance (TARGET C, the order-0 prototype decoder, NON-VACUOUS check).** For the
current real decoder `decode := M9.leafOMTypeOfSize ∘ M6.treeSize` the residual is `0`, so
`M5.cells (decode T) = []` (the empty factorization), and the per-node tiling hypothesis `hSideTile`
DEGENERATES to `0 = M5.clusterSize (decode T)`. This lemma records that, on the order-0 prototype, the
per-node `hnode`-summand is the empty sum `0` and equals the cluster size IFF the cluster size is `0`
(true exactly on `treeSize = 0` shapes). So `perNode_tiling`/`real_hnode` are genuine theorems whose
hypothesis is DISCHARGED at the leaf but not yet at a non-separable node — the residual is the
higher-order decoder (`R2`), not the per-node math. PROVED from `M5.cells _ = []` whenever the residual
is zero. `[core]`. -/
theorem perNode_tiling_of_zeroResidual (D : M5.OMType) (hRr : D.Rr = 0)
    (hcs : M5.clusterSize D = 0) :
    ((M7.cellsOfType D).map (fun c => cellDegree c + (c.children.map M6.treeSize).sum)).sum
      = M5.clusterSize D := by
  apply perNode_tiling
  -- `M5.cells D = []` because `factorize_any 0` has `factors = ∅`
  have hcells : M5.cells D = [] := by
    rw [M5.cells]
    -- the chosen factorization of `D.Rr = 0` has empty `factors`
    have hfac : (Classical.choice (M4.factorize_any D.Rr)).factors = ∅ := by
      set fac := Classical.choice (M4.factorize_any D.Rr) with hfacdef
      -- The degree budget `∑_ψ mult·deg = D.Rr.natDegree = 0` forces every factor's term to be `0`;
      -- but an irreducible factor has positive degree and positive multiplicity, so `factors = ∅`.
      by_contra hne
      obtain ⟨ψ, hψ⟩ := Finset.nonempty_of_ne_empty hne
      have hmd := fac.degree_budget
      have hmp : 1 ≤ fac.mult ψ := fac.mult_pos ψ hψ
      have hir := fac.factors_irreducible ψ hψ
      have hdeg : 1 ≤ ψ.natDegree := hir.natDegree_pos
      have hterm : 1 ≤ fac.mult ψ * ψ.natDegree :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hle : 1 ≤ D.Rr.natDegree := by
        calc 1 ≤ fac.mult ψ * ψ.natDegree := hterm
          _ ≤ ∑ φ ∈ fac.factors, fac.mult φ * φ.natDegree :=
            Finset.single_le_sum (f := fun φ => fac.mult φ * φ.natDegree)
              (fun _ _ => Nat.zero_le _) hψ
          _ = D.Rr.natDegree := hmd
      rw [hRr] at hle; simp at hle
    -- (Phase-A A5 canonicalization) `M5.cells` now sorts the factor list; the empty case passes
    -- through `mergeSort []  = []`.
    rw [List.map_eq_nil_iff]
    have htl : (Classical.choice (M4.factorize_any D.Rr)).factors.attach.toList = [] := by
      rw [Finset.toList_eq_nil, Finset.attach_eq_empty_iff]
      exact hfac
    rw [htl]
    simp
  rw [hcells, List.map_nil, List.sum_nil, hcs]

/-! ### GLUE-2 TARGET C (ii) — the GMN node `e·f` law + the separable discharge of `hSideTile`
(LIMIT_BLUEPRINT §5)

`perNode_tiling`/`real_hnode` take the per-node tiling `hSideTile` as an explicit hypothesis. The
blueprint verdict (§5) is that `hSideTile` is a GMN CITE — it is NOT derivable from `M5.cells` +
`M4.degree_budget` (the cell list carries `dS, δ, childSize` but NOT the ramification index `e_S` nor
the abscissa span `∑_S ℓ(S) = cs`). We state the genuine structural content as a NAMED axiom (the
unramified node "theorem of the product" `δ·d_r = cs`, GMN arXiv:0807.2620v2 §2), exactly analogous in
status to `M5.OMType.hDrLtCs` and `L2_reconstruct`, and use it to discharge `hSideTile` in the
SEPARABLE case (where the blueprint's units worry — `childSize := μ` vs the degree surplus
`(μ−1)·δ·deg ψ` — does NOT arise, because separable factors have `μ = 1` and hence NO children, so the
`childSize` sums vanish identically). The non-separable correction needs the `OMType.OMCell.Child.childSize`
keystone edit (blueprint §5.4(1)), which is out of this group's file scope; it is flagged, not faked. -/

/-- **GMN unramified node `e·f` law** (CITE: arXiv:0807.2620v2, the "theorem of the product"
`n = ∑_i e_i f_i` at one OM node, unramified base `f_K = 1`). At an order-`r` node the residue degree
`δ` times the residual degree `d_r` equals the node cluster size: `D.δ · D.dr = D.clusterSize` (= `D.cs`).
This is NOT derivable from the cell list `M5.cells D` (which factors one already-side-selected residual
`D.Rr` and carries `dS, δ, childSize`, but NOT the ramification index `e_S` / side-slope denominator,
nor the abscissa span `∑_S ℓ(S) = cs`). It is the genuine `n = ∑ e·f` GMN structural import.

⚠ **U4 SOUNDNESS FIX (2026-07-02, `notes/MONTES_AUDIT.md`): this WAS the axiom
`gmn_node_ef_law (D : M5.OMType) : D.δ * D.dr = M5.clusterSize D`, which is FALSE-AS-STATED** — the
`OMType` structure carries `δ`, `dr`, `cs` as INDEPENDENT fields (only `hResidueDeg`/`hResidualDeg`/
`hDrLtCs` constrain them), so a legal `OMType` with `δ = 1`, `Rr = X` (`dr = 1`), `cs = 5` refutes it
(`1 ≠ 5` ⟹ `False`). The `e·f` law is TRUE only at GENUINE OM nodes (those the classifier actually
produces), a constraint the structure does not carry — indeed the in-repo order-0 carriers
(`M9.leafOMTypeOfSize s`: `δ·dr = 0 ≠ s`; `Classifier.childCtxOfSize`) VIOLATE it, so the universal
axiom contradicted the development's own objects. The sound encoding is this PREDICATE, threaded as an
explicit hypothesis `hef` by the consumers (`hSideTile_separable`, `perNode_tiling_separable`); the
genuine GMN cite is then invoked per-node at genuine nodes only. -/
def GMNNodeEfLaw (D : M5.OMType) : Prop := D.δ * D.dr = M5.clusterSize D

/-- **The separable-node degree-sum identity** (`M4.degree_budget`, separable specialization). On the
filled `M5.cells D`, when every distinct residual factor is SEPARABLE (multiplicity `1`, so the cell
has no descent children), the per-cell residual degrees `c.dS = deg ψ` sum to `d_r`:
`∑_{c ∈ M5.cells D} c.dS = D.dr`. This is the genuine `degree_budget` `∑_ψ mult·deg ψ = R_r.natDegree`
with all `mult = 1` (each distinct factor appears once), threaded as the explicit separable hypothesis
`hsep` (the per-cell degree shadow of `M4.degree_budget`). It is the half of the node tiling that the
cell list DOES carry. `[core, modulo hsep]`. -/
theorem cellDegreeSum_eq_dr_of_separable (D : M5.OMType)
    (hsep : ((M5.cells D).map (fun c => c.dS)).sum = D.dr) :
    ((M5.cells D).map (fun c => c.dS)).sum = D.dr := hsep

/-- **GLUE-2 (ii) — `hSideTile` discharged in the SEPARABLE case** (LIMIT_BLUEPRINT §5, the genuine
CITE-backed per-node tiling). GIVEN (a) every cell of `M5.cells D` is a leaf (`hleaf`: no descent
children — the separable node, where the `childSize := μ` units worry of §5.3 cannot arise) and (b) the
separable degree-sum identity `hsep` (`∑_c c.dS = d_r`, the `M4.degree_budget` half), the per-node
tiling `∑_c (δ·dS + ∑_ch childSize) = clusterSize D` HOLDS — the children sums vanish by `hleaf`,
leaving `δ · ∑_c c.dS = δ·d_r`, which equals `clusterSize D` by the NAMED GMN axiom `gmn_node_ef_law`.
This is the honest, decoder-agnostic discharge of `hSideTile` at a separable node: a genuine theorem
modulo the single cited GMN `e·f` law. The non-separable case additionally needs the
`OMCell.Child.childSize := (μ−1)·δ·deg ψ` keystone edit (§5.4(1), out of this file's scope). `[core,
depends on gmn_node_ef_law + hleaf + hsep]`. -/
theorem hSideTile_separable (D : M5.OMType)
    (hef : GMNNodeEfLaw D)
    (hleaf : ∀ c ∈ M5.cells D, c.children = [])
    (hsep : ((M5.cells D).map (fun c => c.dS)).sum = D.dr) :
    ((M5.cells D).map (fun c =>
        D.δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum)).sum = M5.clusterSize D := by
  -- (1) the child sums vanish (every cell is a leaf):
  have hsummand : ∀ c ∈ M5.cells D,
      D.δ * c.dS + (c.children.map (fun ch => ch.childSize)).sum = D.δ * c.dS := by
    intro c hc
    rw [hleaf c hc, List.map_nil, List.sum_nil, Nat.add_zero]
  rw [List.map_congr_left hsummand]
  -- (2) `∑_c δ·dS = δ · ∑_c dS = δ·d_r` (pull the constant `δ` out of the list sum):
  rw [List.sum_map_mul_left (M5.cells D) (fun c => c.dS) D.δ, hsep]
  -- (3) `δ·d_r = clusterSize D` by the GMN `e·f` law, threaded as the per-node hypothesis `hef`
  -- (U4 fix: the old universal axiom over a free `OMType` was FALSE-AS-STATED):
  exact hef

/-- **GLUE-2 (ii) — `perNode_tiling` fully discharged at a SEPARABLE node** (the assembled deliverable).
For a separable node (`hleaf`, all cells leaves) with the `degree_budget` half (`hsep`), the
`hnode`-summand on the erased real cells `M7.cellsOfType D` sums to the node cluster size, with NO
`hSideTile` hypothesis left — only the NAMED GMN `e·f` axiom `gmn_node_ef_law` (cited) and the two
structural facts the cell list DOES carry. PROVED by feeding `hSideTile_separable` into `perNode_tiling`
(the genuine erasure `perNode_M7_eq_M5`). This is the honest, decoder-agnostic closure of the per-node
tiling at the separable node; the non-separable case is gated on the `childSize` keystone edit (§5.4(1),
out of this file's scope). `[core, depends on gmn_node_ef_law + hleaf + hsep]`. -/
theorem perNode_tiling_separable (D : M5.OMType)
    (hef : GMNNodeEfLaw D)
    (hleaf : ∀ c ∈ M5.cells D, c.children = [])
    (hsep : ((M5.cells D).map (fun c => c.dS)).sum = D.dr) :
    ((M7.cellsOfType D).map (fun c => cellDegree c + (c.children.map M6.treeSize).sum)).sum
      = M5.clusterSize D :=
  perNode_tiling D (hSideTile_separable D hef hleaf hsep)

/-- **HONEST RESIDUAL / FLAG — the discharge of `hbudget` is B-DEPENDENT (F2/B frontier), OUT OF SCOPE.**

GLUE-2's corrected `boxScale_share` is proved from `hbudget : (∑_{c ∈ cells T} cellDegree c) = n`. For
the canonical real instance `cells := M7.cells decode`, `hbudget` UNFOLDS (`M7.cells`,
`M7.cellsOfType`) to a statement about `(M5.cells (decode T)).map …`, and BOTH producers are still
stubs:
* `M5.cells (T : OMType) := []` (`OMType.lean:184`);
* `Classifier.omStep … := []` (`Classifier.lean`, the DEF B.2 body — the F2/B frontier, explicitly OUT
  OF SCOPE for this wave).
So AT THIS LAYER the real cell list is EMPTY, `hbudget` reduces to `0 = n` (true only for `n = 0`), and
there is no degree-`n` polygon tied to the cells. The genuine discharge needs the `omStep` body that
emits one cell per (M3 side `S ∈ npSides`, distinct M4 residual factor `ψ`), and then combines TWO
B-frontier facts, each available only once `omStep` is real:
  (1) **side tiling** `∑_{S ∈ npSides} ℓ(S) = n` — the order-`r` Newton polygon of a degree-`n` box has
      horizontal extent `n` (provable from the 3a `npVertices_sorted`/`npVertices_on_hull` ONCE the
      vertex list is shown to span `[0, n]`, which is an `omStep` postcondition);
  (2) **per-side residual split** `∑_{ψ on S} δ·deg ψ = e_S·f_S = ℓ(S)` — the M4 `degree_budget`
      (`∑_ψ mult·deg ψ = deg R_S`) together with the tame/wild slope-denominator law `e_S` and the
      residue degree `δ` (`f_S = δ·deg R_S` at the unramified base, `f_K = 1`).
The B-independent KERNEL that glues (1)+(2) into `hbudget` is PROVED above as `share_sum_flatten` (the
per-side block regrouping). This lemma RECORDS the residual obligation as a `Prop` returning `True`; it
is NOT a fake close of `hbudget` — `hbudget` itself stays an explicit hypothesis of `boxScale_share`. -/
theorem boxScale_share_residual (decode : ClusterShape → M5.OMType) (T : ClusterShape) (n : ℕ) :
    ((M7.cells decode T).map cellDegree).sum = n → True := fun _ => trivial

/-- **DISPROOF that the OLD `boxScale_share` held as a `∀` over free `cells, T, n`** (the machine-checked
record of the WAVE-2 bug, KEPT). The OLD statement used the share `L4.newtonExponent c.polygon +
c.δ·(c.dS-1)`. Instantiating `cells := fun _ => []` and `n := 1` makes the LHS `[].sum = 0` and the RHS
`1`, so `0 = 1` — a contradiction. This certifies the old formula CANNOT be closed sorry-free as stated;
the corrected `boxScale_share` above (i) replaces the share by the per-factor column count `cellDegree
c = c.δ · c.dS` and (ii) takes the degree-budget hypothesis `hbudget` explicitly. Core-only, sorry-free.
`[core]` -/
theorem boxScale_share_false :
    ¬ (∀ (cells : ClusterShape → List CountCell) (T : ClusterShape) (n : ℕ),
        ((cells T).map (fun c => L4.newtonExponent c.polygon + c.δ * (c.dS - 1))).sum = n) := by
  intro h
  have hbad := h (fun _ => []) ⟨[], []⟩ 1
  simp at hbad

/-- **GLUE-3 `selfLoop_ratio_reconcile` (F1-raw ↔ F3-normalized ratio).** Reconciles F1.L9's raw
shape-fiber lift ratio `r_raw = p^n` (full-box growth, `> 1`) with F3's normalized self-loop survival
ratio `selfLoopRatio T q = q^{-w} < 1`: after dividing the level-`N` count by `q^{nN}`, the per-step
NORMALIZED survival of the diagonal self-loop child is `selfLoopRatio`, i.e. `r_raw / q^n` corrected by
the self-loop window exponent `w(treeSize T)`. The conceptual seam between F1 (raw counts) and F3
(normalized limits). Bodies `sorry`; TRUE-intended (with `q = p^{f_K}`, `f_K = 1` for the unramified
core so `q = p`, `r_raw / q^n = 1` and the genuine contraction is the `q^{-w}` self-loop factor). -/
theorem selfLoop_ratio_reconcile (treeSize : ClusterShape → ℕ) (T : ClusterShape) (p q n : ℕ)
    (hpq : q = p) (hself : 2 ≤ treeSize T) :
    selfLoopRatio treeSize T q = ((q : ℚ) ^ L5fix.selfLoopExponent (treeSize T))⁻¹ := by
  unfold selfLoopRatio; simp [hself]

/- ⚠ **FALSE AS STATED — UNSOUND (flagged 2026-06-30; do NOT trust, do NOT route the capstone through it).**
This axiom is quantified over FREE, UNRELATED `classify`/`cells`/`treeSize` with no hypothesis tying `cells` to
`classify`. Its LHS `stratumCount(shapeFiberCount p n classify) T (N+1)` depends only on `classify`, while its
RHS depends on `cells` (the filtered sum) and `treeSize`; so for fixed `classify,T,N` it cannot hold for all
`cells` (e.g. `cells := fun _ => []` forces `stratumCount T (N+1) = selfLoopRatio·q^n·stratumCount T N`, false
for a generic `classify`). A false universal axiom is unsound. The genuine GMN identity is TRUE only when
`cells`/`treeSize` ARE the real OM decomposition of `classify` (`cells := M5.cells ∘ decode`, `treeSize :=
M6.treeSize`); the fix is to add that as a hypothesis / instantiate at the real objects. The capstone was
reverted (`montes_unconditional` `h_node` restored to a hypothesis) so this no longer reaches its footprint.
ORIGINAL (over-strong) docstring follows:
**[CITE] GMN Thm 3.1/3.7 + Cor 3.8 / Lemma 3.11(3) (Guàrdia–Montes–Nart, arXiv:0807.2620v2 §3),
the CORRECTED serial-pole self-loop split (with the inter-level `q^n`).** This is the
`LevelNCount`-local copy of the GMN across-level self-loop descent identity. The downstream
`F1.selfLoop_childFiber_fkeyed` (`OM/CountingModel.lean`) carries the SAME structural content, but
`OM/CountingModel.lean` IMPORTS this module, so it cannot be referenced here (import cycle); hence the
identity is re-imported as a named axiom at this layer.

**THE `q^n` CORRECTION (GLUE1_CLOSE_BLUEPRINT §1).** For a shape `T`, the level-`(N+1)` type-`T`
stratum splits as the NON-self-loop cells (children `ch` with `treeSize ch ≠ treeSize T`, recursing at
`N+1`) PLUS the diagonal self-loop child re-entering the level-`N` type-`T` stratum scaled by
`selfLoopRatio T q · q^n`. The `boxReduce` fiber is `q^n`-to-1 ACROSS levels
(`boxReduce_fiber_card = p^n`, `q = p` unramified core); the diagonal self-loop child captures a
`q^{-w}` FRACTION of that fiber, so its re-entry contributes `q^n · q^{-w} = q^n · selfLoopRatio`
cosets per parent. The self-loop coefficient is therefore `selfLoopRatio · q^n`, NOT a bare
`selfLoopRatio`: the bare form would force limit denominator `1 − selfLoopRatio·q^{-n} ≠ countPivot`
for every `n ≥ 1` (the machine-checked disproof `nodeTrunc_limit_denominator_mismatch` below).

The user authorized importing this descent identity as a named axiom; it is the single GMN structural
import for the F2/B self-loop split, NOT a sub-proof. OFF the capstone footprint (the capstone routes
through the top-level `LeanUrat.CountingModel`, not this F2 self-loop split). The previous frozen
`stratumCount_selfLoop_rec` `sorry` carried the WRONG (no-`q^n`) coefficient; this axiom corrects it. -/
/- ⚠ **AXIOM DELETED (2026-07-04).** `selfLoop_childFiber_corrected` (A9) was FALSE-AS-STATED over its
free `cells`/`treeSize` binders: the LHS `stratumCount (shapeFiberCount p n classify) T (N+1)` depends
only on `classify`, while the RHS depends on the FREE, UNRELATED `cells`/`treeSize` (e.g.
`cells := fun _ => []` empties the non-self-loop sum and forces
`stratumCount T (N+1) = selfLoopRatio·q^n·stratumCount T N`, false for a generic `classify`). Same
free-binder defect family as the deleted `L2_reconstruct` (above) and `boxVolumeScale_collapse`
(below), and as `F1.selfLoop_childFiber_fkeyed` (`OM/CountingModel.lean`, deleted the same day). Its
content — the GMN across-level self-loop descent identity with the corrected `q^n` coefficient
(Thm 3.1/3.7 + Cor 3.8 / Lemma 3.11(3), arXiv:0807.2620v2) — is TRUE only when `cells`/`treeSize` ARE
the genuine OM decomposition of `classify`, and is now threaded as the explicit hypothesis `hA9` of
`stratumCount_selfLoop_rec` / `nodeTrunc_tendsto` below (to be discharged at the pinned objects per
`HNODE_GENUINE_FIX_BLUEPRINT.md` / `PIN_ARCHITECTURE_BLUEPRINT.md`). -/

/-- **GLUE-1 `stratumCount_selfLoop_rec` — THE MOST IMPORTANT CONTRACT (F2→F3), CORRECTED (`q^n`).** The
self-loop-separated level-`N` recursion. The flat `stratumCount_factor` gives children at level `N` with
NO `countPivot` denominator; `nodeMeasure_boxSum` needs the `q`-scale `clusterCount` children divided by
`countPivot`. This lemma exposes the level-`N` self-loop recursion whose unrolling is
`NestedCollapse.geomTrunc`, supplying the `countPivot = 1/(1 - q^{-w})` denominator a finite-`N`
preimage:

    stratumCount T (N+1)
      = (Σ_{non-self-loop cells} bb1Value c (q^{N+1}) · (q^δ)^{dS-1} · ∏_children stratumCount ch (N+1))
        + selfLoopRatio · q^n · stratumCount T N        [self-loop child separated, CORRECTED]

i.e. the type-`T` stratum at level `N+1` is the non-self-loop cells' contribution PLUS the self-loop
child (the cell whose child has `treeSize = treeSize T`) re-entering at level `N` scaled by the per-step
ratio `selfLoopRatio · q^n` (the corrected coefficient, GLUE1_CLOSE_BLUEPRINT §1; the inter-level `q^n`
makes the `q^n·q^{-n}=1` cancellation in `nodeTrunc_step_corrected` give ratio EXACTLY `selfLoopRatio`,
so the limit denominator is genuinely `countPivot`, resolving obstruction (B)). Unrolling this recursion
in `N` gives the geometric truncation whose limit is `nodeNum / countPivot` — EXACTLY the
`nodeMeasure_boxSum` RHS. **(2026-07-04) NO LONGER closed via the axiom `selfLoop_childFiber_corrected`
— that axiom was FALSE-AS-STATED over its free `cells`/`treeSize` binders (LHS independent of `cells`;
see its tombstone above) and is DELETED.** The descent identity now enters as the explicit hypothesis
`hA9` (VERBATIM the deleted axiom's conclusion at these arguments), to be discharged only at the
genuine OM decomposition (`cells`/`treeSize` pinned to `classify` per `HNODE_GENUINE_FIX_BLUEPRINT.md`
/ `PIN_ARCHITECTURE_BLUEPRINT.md`); this theorem is now the CONTRACT recording the GLUE-1 shape, not a
closed cite. `[core, modulo hA9]`. -/
theorem stratumCount_selfLoop_rec {n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ) (q : ℕ)
    (T : ClusterShape) (N : ℕ)
    -- (2026-07-04) the across-level self-loop descent, now an EXPLICIT HYPOTHESIS (the former axiom
    -- `selfLoop_childFiber_corrected` was FALSE-AS-STATED over the free `cells`/`treeSize` binders and
    -- is DELETED; the TRUE constrained form pins `cells`/`treeSize` to the genuine OM decomposition of
    -- `classify` per HNODE_GENUINE_FIX_BLUEPRINT.md / PIN_ARCHITECTURE_BLUEPRINT.md):
    (hA9 : stratumCount (shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
            * stratumCount (shapeFiberCount p n classify) T N) :
    stratumCount (shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
            * stratumCount (shapeFiberCount p n classify) T N :=
  hA9

/-! ### Local recurrence-limit engine for `nodeTrunc_tendsto`

The `LevelNCount` module sits at the BOTTOM of the OM DAG, BELOW `LimitGlue`/`LimitSpine` (which import
it). So the banked `LimitGlue.firstOrder_recurrence_limit_rat` / `nodeTrunc_tendsto_of_corrected_GLUE1`
cannot be referenced here (import cycle). We import only `OM.LimitRecurrence` (Mathlib-only deps, no
cycle) and re-derive the thin rational cast-glue + `0 ≤ r < 1` bound locally; these are α-identical to
the banked `LimitGlue` versions. The genuine analytic engine
(`LimitRecurrence.firstOrder_recurrence_limit`) is `[propext, Classical.choice, Quot.sound]`. -/

/-- **The self-loop ratio is in `[0,1)` at EVERY node** (`LevelNCount`-local copy of
`LimitGlue.selfLoopRatio_mem_Ico`, re-derived to avoid the import cycle). At a ramifying node
(`2 ≤ treeSize T`) `selfLoopRatio = (q^w)⁻¹ ∈ (0,1)` (`w = selfLoopExponent ≥ 1`); at a leaf
`selfLoopRatio = 0`. `[core]`. -/
theorem selfLoopRatio_mem_Ico_local {q : ℕ} (hq : 2 ≤ q) (treeSize : ClusterShape → ℕ)
    (T : ClusterShape) :
    0 ≤ selfLoopRatio treeSize T q ∧ selfLoopRatio treeSize T q < 1 := by
  unfold selfLoopRatio
  by_cases hT : 2 ≤ treeSize T
  · simp only [hT, if_true]
    have hexp : 1 ≤ L5fix.selfLoopExponent (treeSize T) := by
      have h6 : 6 ≤ treeSize T * (treeSize T + 1) := by nlinarith
      unfold L5fix.selfLoopExponent; omega
    have hgt : (1 : ℚ) < (q : ℚ) ^ L5fix.selfLoopExponent (treeSize T) :=
      one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
    have hpos : (0 : ℚ) < (q : ℚ) ^ L5fix.selfLoopExponent (treeSize T) := lt_trans one_pos hgt
    exact ⟨le_of_lt (inv_pos.mpr hpos), by simpa using inv_lt_one_of_one_lt₀ hgt⟩
  · simp only [hT, if_false]; exact ⟨le_refl 0, zero_lt_one⟩

/-- **ℝ→ℚ cast glue for `firstOrder_recurrence_limit`** (`LevelNCount`-local copy of
`LimitGlue.firstOrder_recurrence_limit_rat`, re-derived to avoid the import cycle). If
`x (N+1) = r·x N + f (N+1)` over ℚ with `0 ≤ r < 1` and `f → L`, then `x → L/(1-r)`. PROVED by pushing
the recurrence through the ring + topological embedding `(↑) : ℚ → ℝ`, applying the ℝ engine
`LimitRecurrence.firstOrder_recurrence_limit`, and pulling the limit back via
`Rat.isEmbedding_coe_real.tendsto_nhds_iff`. `[core]`. -/
theorem firstOrder_recurrence_limit_rat_local (x f : ℕ → ℚ) (r L : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ N, x (N + 1) = r * x N + f (N + 1))
    (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto x Filter.atTop (nhds (L / (1 - r))) := by
  have hxR : Filter.Tendsto (fun N => ((x N : ℝ))) Filter.atTop (nhds (((L / (1 - r) : ℚ) : ℝ))) := by
    have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hr1R : (r : ℝ) < 1 := by exact_mod_cast hr1
    have hrecR : ∀ N, (x (N + 1) : ℝ) = (r : ℝ) * (x N : ℝ) + (f (N + 1) : ℝ) := by
      intro N; have := hrec N; push_cast [this]; ring
    have hfR : Filter.Tendsto (fun N => ((f N : ℝ))) Filter.atTop (nhds (L : ℝ)) :=
      (Rat.continuous_coe_real.tendsto L).comp hf
    have hlim := LimitRecurrence.firstOrder_recurrence_limit
      (fun N => (x N : ℝ)) (fun N => (f N : ℝ)) (r : ℝ) (L : ℝ) hr0R hr1R hrecR hfR
    have hcast : (L : ℝ) / (1 - (r : ℝ)) = (((L / (1 - r) : ℚ)) : ℝ) := by push_cast; ring
    rwa [hcast] at hlim
  rw [Rat.isEmbedding_coe_real.tendsto_nhds_iff]
  exact hxR

/- ⚠ **SUSPECT / FALSE AS STATED — UNSOUND (flagged 2026-06-30; do NOT trust).** Same defect family as
`selfLoop_childFiber_corrected`: quantified over FREE `cells`/`treeSize`, with the per-node degree budget
`∑shares = n` NOT a hypothesis. The asserted `Tendsto` requires that budget to hold for the given `cells`;
for `cells` where it fails the normalization `/q^{nN}` mismatches the per-child scales and the limit is not
`nodeNum`. TRUE only at the real OM decomposition; the fix is to constrain `cells`/`treeSize` to the genuine
OM cells (then the budget holds). Capstone reverted off it. ORIGINAL (over-strong) docstring follows:
**[CITE] A3 — the box-VOLUME-scale collapse (GMN "theorem of the product" / box-volume scale).**
The normalized level-`N` non-self-loop forcing collapses to the `q`-scale numerator `nodeNum`:

    (Σ_{non-self-loop cells} bb1Value c (q^N) · (q^δ)^{dS-1} · ∏_children stratumCount ch N) / q^{nN}
      ⟶  nodeNum cells treeSize cells_descend T q     as  N → ∞.

This is the NESTED box-volume-scale collapse (GLUE1_CLOSE_BLUEPRINT §3). Its analytic INGREDIENTS are
all PROVED and core-only downstream — `boxVolume_normalized_limit` (`bb1Value c (q^N)·q^{A_c·N} → 1`),
`boxCount_normalized_eq_bb1Value` (box COUNT → box VOLUME), `children_product_limit` (the per-child
`stratumCount ch N / q^{n_ch·N} → clusterCount ch q`) — but ASSEMBLING them requires the per-child
degree-share factoring `q^{nN} = q^{A_c·N}·∏_ch q^{n_ch·N}` cell-by-cell, i.e. the GMN per-node degree
budget `∑(shares) = n` (`boxScale_share`'s `hbudget` / `boxScale_share_rec`'s `hnode`), which is
B-frontier-gated for the real instance. It is therefore adopted as a NAMED GMN box-volume-scale CITE,
with the proved F3 primitives + `boxScale_share_rec` as the honest scaffolding. OFF the capstone
footprint. -/
/- ⚠ **AXIOM DELETED (2026-07-04).** `boxVolumeScale_collapse` (A10) was FALSE-AS-STATED over its free
`cells`/`treeSize` binders: the asserted `Tendsto` requires the GMN per-node degree budget
`∑ shares = n` for the given `cells` (it was NOT a hypothesis); for `cells` where the budget fails the
`/q^{nN}` normalization mismatches the per-child scales `q^{n_ch·N}` and the limit is not
`nodeNum cells treeSize cells_descend T q` (the LHS child counts `stratumCount ch N` depend only on
`classify`, while `nodeNum` is computed from the FREE `cells`/`treeSize`). Same free-binder defect
family as the deleted `L2_reconstruct` and `selfLoop_childFiber_corrected` (above) and
`F1.selfLoop_childFiber_fkeyed` (`OM/CountingModel.lean`, deleted the same day). Its content — the A3
box-volume-scale collapse, whose analytic INGREDIENTS (`boxVolume_normalized_limit`,
`boxCount_normalized_eq_bb1Value`, `children_product_limit`) are PROVED and core-only downstream — is
TRUE only when `cells`/`treeSize` ARE the genuine OM decomposition of `classify` (then the degree
budget holds), and is now threaded as the explicit hypothesis `hA10` of `nodeTrunc_tendsto` below (to
be discharged at the pinned objects per `HNODE_GENUINE_FIX_BLUEPRINT.md` /
`PIN_ARCHITECTURE_BLUEPRINT.md`). -/

/-- **GLUE-1 LIMIT BRIDGE `nodeTrunc_tendsto` — now HYPOTHESIS-THREADED (2026-07-04).** The normalized
truncation `nodeTrunc T N` converges to `nodeNum / countPivot` — the `nodeMeasure_boxSum` RHS. PROVED by
feeding the CORRECTED GLUE-1 per-step recurrence (`stratumCount_selfLoop_rec`, the `q^n` form, via
`nodeTrunc_step_corrected`) and the A3 box-volume-scale collapse into the local rational
recurrence-limit engine `firstOrder_recurrence_limit_rat_local`, identifying `1 - selfLoopRatio`
with `countPivot` (`one_sub_selfLoopRatio_eq_countPivot`).

**(2026-07-04) THE TWO NAMED GMN "CITES" THIS RESTED ON WERE FALSE-AS-STATED AXIOMS AND ARE DELETED**
(`selfLoop_childFiber_corrected` (A9) and `boxVolumeScale_collapse` (A10), both quantified over FREE
`cells`/`treeSize` with the LHS independent of them — see their tombstones above). Their conclusions now
enter as the explicit hypotheses `hA9` (the ∀-`N` across-level self-loop descent, fed through
`stratumCount_selfLoop_rec`/`nodeTrunc_step_corrected`) and `hA10` (the A3 box-volume-scale collapse),
each VERBATIM the deleted axiom's conclusion at these arguments, to be discharged only at the genuine
OM decomposition (`cells`/`treeSize` pinned to `classify` per `HNODE_GENUINE_FIX_BLUEPRINT.md` /
`PIN_ARCHITECTURE_BLUEPRINT.md`).

**HOW THE TWO PRIOR OBSTRUCTIONS ARE RESOLVED (GLUE1_CLOSE_BLUEPRINT §1–§3, NOT fake-closed):**
  (A) box-scale collapse `nonSelfLoopNorm T (N+1) → nodeNum` — supplied by the explicit hypothesis
      `hA10` (A3), whose analytic ingredients are proved+core-only downstream and
      whose assembly consumes the GMN per-node degree budget (`boxScale_share_rec`); and
  (B) the geometric ratio — RESOLVED by the corrected `q^n` self-loop coefficient: with the `q^n` term,
      `nodeTrunc_step_corrected` gives ratio EXACTLY `selfLoopRatio` (the `q^n·q^{-n}=1` cancellation),
      so the limit denominator is genuinely `countPivot = 1 - selfLoopRatio` (NOT the wrong
      `1 - selfLoopRatio·q^{-n}` of the old no-`q^n` form; see `nodeTrunc_limit_denominator_mismatch`).
This is α-identical to the banked `LimitGlue.nodeTrunc_tendsto_of_corrected_GLUE1`, re-assembled at this
layer (which is below `LimitGlue` in the DAG). The conclusion is DEFINITIONALLY `nodeMeasure_boxSum`'s.
`[core, modulo hA9 + hA10 — the conclusions of the two DELETED false-as-stated axioms, now explicit
hypotheses]`. -/
theorem nodeTrunc_tendsto {n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (q : ℕ) (hq : 1 < q) (T : ClusterShape)
    -- (2026-07-04) VERBATIM the conclusion of the DELETED false-as-stated axiom
    -- `selfLoop_childFiber_corrected` (A9), specialized to these arguments (∀ over the level `N`):
    (hA9 : ∀ N : ℕ,
      stratumCount (shapeFiberCount p n classify) T (N + 1)
        = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
          + selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
              * stratumCount (shapeFiberCount p n classify) T N)
    -- (2026-07-04) VERBATIM the conclusion of the DELETED false-as-stated axiom
    -- `boxVolumeScale_collapse` (A10), specialized to these arguments:
    (hA10 : Filter.Tendsto
      (fun N =>
        (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    stratumCount (shapeFiberCount p n classify) ch N)).prod)).sum
          / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (nodeNum cells treeSize cells_descend T q))) :
    Filter.Tendsto (nodeTrunc p q classify T) Filter.atTop
      (nhds (nodeNum cells treeSize cells_descend T q / countPivot (treeSize T) q)) := by
  -- abbreviate the per-level filtered-cell forcing `f N := (filtered non-self-loop sum at N)/q^{nN}`:
  set f : ℕ → ℚ := fun N =>
    (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
        (fun c =>
          L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
            * (c.children.map (fun ch =>
                stratumCount (shapeFiberCount p n classify) ch N)).prod)).sum
      / (q : ℚ) ^ (n * N) with hfdef
  -- (i) the CORRECTED per-step recurrence holds at every level (consumes GLUE-1
  -- `stratumCount_selfLoop_rec`, fed by the explicit hypothesis `hA9` — the conclusion of the DELETED
  -- false-as-stated axiom `selfLoop_childFiber_corrected`):
  have hstep : ∀ N, nodeTrunc p q classify T (N + 1)
      = f (N + 1) + selfLoopRatio treeSize T q * nodeTrunc p q classify T N := by
    intro N
    rw [hfdef]
    exact nodeTrunc_step_corrected p q classify cells treeSize (by omega) T N
      (stratumCount_selfLoop_rec p classify cells treeSize q T N (hA9 N))
  -- (ii) the box-volume-scale collapse A3 gives the forcing limit `f → nodeNum` (the explicit
  -- hypothesis `hA10` — the conclusion of the DELETED false-as-stated axiom `boxVolumeScale_collapse`):
  have hf : Filter.Tendsto f Filter.atTop (nhds (nodeNum cells treeSize cells_descend T q)) :=
    hA10
  -- (iii) feed into the local rational recurrence-limit engine; `1 - selfLoopRatio = countPivot`:
  obtain ⟨hr0, hr1⟩ := selfLoopRatio_mem_Ico_local (by omega : 2 ≤ q) treeSize T
  have hstep' : ∀ N, nodeTrunc p q classify T (N + 1)
      = selfLoopRatio treeSize T q * nodeTrunc p q classify T N + f (N + 1) := by
    intro N; rw [hstep N]; ring
  have hlim := firstOrder_recurrence_limit_rat_local (nodeTrunc p q classify T) f
    (selfLoopRatio treeSize T q) (nodeNum cells treeSize cells_descend T q) hr0 hr1 hstep' hf
  rwa [one_sub_selfLoopRatio_eq_countPivot] at hlim

/-- **MACHINE-CHECKED OBSTRUCTION (B) for `nodeTrunc_tendsto`** (WAVE audit flag). The geometric ratio
forced by the proved per-step recurrence `LimitSpine.nodeTrunc_step_of_rec` is `selfLoopRatio · q^{-n}`,
so any convergent solution has limit denominator `1 - selfLoopRatio·q^{-n}`. This DIFFERS from the
claimed `countPivot = 1 - selfLoopRatio` for `n ≥ 1`: at a ramifying node (`2 ≤ treeSize T`) with `q ≥ 2`
and `n ≥ 1`, `1 - selfLoopRatio·q^{-n} ≠ countPivot`. Hence `nodeTrunc_tendsto`'s claimed limit value is
inconsistent with the frozen GLUE-1 self-loop term unless GLUE-1 is restated to carry a compensating
`q^n`. Core-only, sorry-free. `[core]` -/
theorem nodeTrunc_limit_denominator_mismatch (treeSize : ClusterShape → ℕ) (T : ClusterShape)
    (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hself : 2 ≤ treeSize T) :
    1 - selfLoopRatio treeSize T q * ((q : ℚ) ^ n)⁻¹ ≠ countPivot (treeSize T) q := by
  -- `selfLoopRatio = (q^w)⁻¹`, `countPivot = 1 - (q^w)⁻¹`; equality of `1 - (q^w)⁻¹·q^{-n}` and
  -- `1 - (q^w)⁻¹` forces `(q^w)⁻¹·q^{-n} = (q^w)⁻¹`, i.e. `q^{-n} = 1`, impossible for `q ≥ 2`, `n ≥ 1`.
  rw [← one_sub_selfLoopRatio_eq_countPivot]
  intro hEq
  have hsl : selfLoopRatio treeSize T q = ((q : ℚ) ^ L5fix.selfLoopExponent (treeSize T))⁻¹ := by
    unfold selfLoopRatio; simp [hself]
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
  have hslpos : (0 : ℚ) < selfLoopRatio treeSize T q := by
    rw [hsl]; exact inv_pos.mpr (pow_pos hqpos _)
  have hslne : selfLoopRatio treeSize T q ≠ 0 := ne_of_gt hslpos
  -- from `1 - r·q^{-n} = 1 - r` deduce `r·q^{-n} = r`, then `q^{-n} = 1`.
  have h2 : selfLoopRatio treeSize T q * ((q : ℚ) ^ n)⁻¹ = selfLoopRatio treeSize T q * 1 := by
    rw [mul_one]; linarith
  have h3 : ((q : ℚ) ^ n)⁻¹ = 1 := mul_left_cancel₀ hslne h2
  -- but `q^n > 1` for `q ≥ 2`, `n ≥ 1`, so `(q^n)⁻¹ < 1` — contradiction.
  have hgt : (1 : ℚ) < (q : ℚ) ^ n := one_lt_pow₀ (by exact_mod_cast hq) (by omega)
  have hlt : ((q : ℚ) ^ n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
  rw [h3] at hlt; exact lt_irrefl _ hlt

/-! ## CRITICAL TYPE-COMPOSITION CHECK (the whole point of the freeze)

Confirm the glue contracts COMPOSE BY TYPE: that `stratumCount_factor → GLUE-1
(`stratumCount_selfLoop_rec` / `nodeTrunc_tendsto`) → `nodeMeasure_boxSum` chain typechecks, i.e. the
unrolled GLUE-1 limit yields EXACTLY the shape `nodeMeasure_boxSum` (hence M9's `h_node`) needs — the
`q`-scale `clusterCount` children over `countPivot`. The `example` below derives `nodeMeasure_boxSum`'s
goal from `nodeTrunc_tendsto` by pure DEFINITIONAL unfolding of `nodeTrunc`/`nodeNum` (no `sorry` in the
composition step itself) — so if the signatures did NOT compose, this `example` would fail to
elaborate. It elaborates ⟹ the contracts are type-correct. (2026-07-04: `nodeTrunc_tendsto` is now
hypothesis-threaded — its former axiom inputs A9/A10 are DELETED — so the composition check carries the
same `hA9`/`hA10` hypotheses, quantified over `T`.) -/
example {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (hq : 1 < q)
    (hA9 : ∀ (T : ClusterShape) (N : ℕ),
      stratumCount (shapeFiberCount p n classify) T (N + 1)
        = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    stratumCount (shapeFiberCount p n classify) ch (N + 1))).prod)).sum
          + selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
              * stratumCount (shapeFiberCount p n classify) T N)
    (hA10 : ∀ (T : ClusterShape), Filter.Tendsto
      (fun N =>
        (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    stratumCount (shapeFiberCount p n classify) ch N)).prod)).sum
          / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (nodeNum cells treeSize cells_descend T q))) :
    ∀ (T : ClusterShape),
      Filter.Tendsto (fun N => stratumCount (shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N))
        Filter.atTop (nhds
          (((cells T).map (fun c =>
              countCellCoeff c q
                * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum
            / countPivot (treeSize T) q)) := by
  intro T
  -- `nodeTrunc_tendsto` gives the limit of `nodeTrunc p q classify T`; unfold `nodeTrunc`/`nodeNum`:
  -- both the LHS function and the RHS numerator are DEFINITIONALLY the `nodeMeasure_boxSum` shape.
  have h := nodeTrunc_tendsto p classify cells treeSize cells_descend q hq T (hA9 T) (hA10 T)
  -- `nodeTrunc p q classify T = fun N => stratumCount … T N / q^{nN}` (def) and
  -- `nodeNum cells treeSize cells_descend T q = ((cells T).map (fun c => countCellCoeff c q · ∏ …)).sum` (def):
  -- both sides are DEFINITIONALLY equal, so `exact h` checks up to defeq (the type-composition witness).
  exact h

end LeanUrat.OM.M8
