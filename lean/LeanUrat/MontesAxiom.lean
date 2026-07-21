/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.RatFn
import LeanUrat.OMInduction
import LeanUrat.NestedCollapse
import LeanUrat.L3
import LeanUrat.L3Squarefree
import LeanUrat.L4
import LeanUrat.L5fix
import LeanUrat.CountingModel

/-!
# LeanUrat.MontesAxiom — M1 (the ONE imported axiom) as PURE-COUNTING node factorization + C1, C2

This module states the single imported assumption of `notes/DECOMP_BLUEPRINT.tex` §2 (`ax:montes`,
"Montes count-multiplicativity over the OM tree"), faithfully and as the *only* axiom in the
counting-model decomposition. It is the count/measure shadow of GMN (arXiv:0807.2620: Thm 3.1/3.7,
Cor 3.8, Lemma 3.11(3), Thm 4.18). **M1 imports COMBINATORIAL/COUNTING content only — never
rationality, uniformity, or `p`-independence**; those are DERIVED (formerly `Decomposition.lean`).

## W4b RETIREMENT (2026-07-21) — the `MontesData` packaging is QUARANTINED

The M1 packaging `structure MontesData` and its derived namespace (`C`, `C_rec`,
`nodeMultiplicativity`, `stratum_tendsto_C`, `shapesOf_finite`, `decidedCount_eq_sum`,
`discriminantTail_tendsto`, `undecidedVanishes`, `countingDensity_is_decided_limit`) are RETIRED to
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt` (blueprint
`notes/M9_REBASE_BLUEPRINT_2026-07-19.md`, W4b): its `boxMeasure`/`boxHaarEquidist`/
`nodeMeasure_boxSum` fields hard-pinned every instance to the numerically-REFUTED per-node box-sum
coefficient shape (blueprint §1, defects D1–D6), and after W4a it had NO non-quarantined instance
left. The abstract-coefficient replacement is `LeanUrat.MontesV2.MontesDataV2`
(`LeanUrat/MontesV2.lean`); the trivial degree-0 witness is ported there (`Witness.trivD2`).

What REMAINS in this module are the shared PURE-COUNTING engine primitives (all PROVED, no axiom),
consumed by the OM modules and the ported Witness: `CountCell`, `countCellCoeff`, `countPivot`
(+ their rationality/nonvanishing lemmas), the box-wise proved blocks (`boxVolume_eq`,
`residualBoxCount`, `residualBoxCount_eq_factor`), the standalone recursion `clusterCount`
(+ `clusterCount_rec`, `clusterCount_boxSum`), and the C1/C2 records (`RescaleC1`,
`ResidualEquidistributionC2`). The M1 prose below is kept as the HISTORICAL record of what the
retired structure said.

## The 2026-06-20 re-architecture (only-Montes footprint)

The per-shape coefficient `C_T(q)` is now built ENTIRELY out of counting blocks — NO reference to the
old opaque-Haar `PadicMeasure.clusterMeasure` or the Igusa/Denef `PadicMeasure.AX_cellRecursion`. M1's
`nodeMultiplicativity` is restated as the **pure-counting per-node factorization** (the faithful
eq-(4.2) count shadow):

    stratum count factor  =  (residual-config count over F_{q^δ}, = T_BB3 = (q^δ)^{dS-1})
                           ×  (Newton-box count, = T_BB1 q-power = bb1Value polygon q)
                           ×  ∏_children  C_child,
    with the self-loop/depth resummed by the geometric LIMIT (the `1/(1 - q^{-w(s)})` pivot).

`C_T` is `DEFINED` from these blocks by a well-founded recursion on `treeSize` (decreasing via the M1
field `cells_descend` — the strict-descent count shadow). Its rationality is then DERIVED through the
GENERIC engine `OMInduction.clusterVol_isRational` instantiated over `ClusterShape` directly — so the
footprint of the rationality/decomposition path is `{Lean core} ∪ {M1 MontesData fields}`, with NO
`clusterMeasure`, NO `AX_cellRecursion`, NO `PadicMeasure.omCells`, NO `PadicMeasure.descend_size_lt`.

C2 (residual equidistribution) is BUNDLED honestly inside the count-factorization: the `(q^δ)^{dS-1}`
factor of `countCellCoeff` is exactly the residual-equidistribution count (the `T_BB3` value); there
is no separate measure claim.

## What M1 says (three clauses, blueprint `ax:montes`)

`M1` is packaged as a `structure MontesData` carrying:

1. **`partition`** (`ax:partition`): for each `N` the level-`N` strata `S_T^{(N)}` PARTITION the decided
   degree-`n` monic polynomials, i.e. the decided count of type `σ` is the sum over shapes `T` with
   `type(T) = σ` of the stratum counts.
2. **`nodeMultiplicativity`** (`ax:multiplicativity`): the normalized stratum limit `C_T(q)` EXISTS
   and equals the per-node COUNT factorization `(T_BB3 count) × (T_BB1 box) × ∏_children C_child`, the
   self-loop geometric-summed (the `MontesData.C` recursion). This is GMN count-multiplicativity; it
   asserts NO rationality and NO measure value — only the count factorization. C2 is bundled inside.
3. **`cells_descend` + `finiteTermination`** (`ax:dichotomy`): off the unique self-loop, every descent
   child has STRICTLY SMALLER cluster `treeSize` (the strict-descent count shadow — the well-founded
   descent measure), and descent terminates with `treeSize ≤ n` (`≤ n` leaves).

## The honest caveats C1, C2 (blueprint §6 (C1), (C2)) — stated SEPARATELY / bundled honestly

* **C1 — the self-loop rescale exponent `w(s) = s(s+1)/2 − 1`** (`lem:rescale`). NOW PROVED to BE the
  Newton-box count's q-power, `= blockExponent s − 1` (the within-block box × Vandermonde rescale of
  `NestedCollapse`), an elementary lattice-count identity (`RescaleC1.selfLoopExponent_eq_blockExponent_sub_one`).
* **C2 — residual equidistribution / submersion** (`ax:multiplicativity`'s analytic clause): bundled
  honestly as the `(q^δ)^{dS-1}` residual count inside `countCellCoeff` (the `T_BB3` value). The
  separate `ResidualEquidistributionC2` re-export is kept as the order-`r` equidistribution statement.

## Status

The M1 structure and the C1/C2 inputs are STATEMENTS (the count-multiplicativity hypotheses); the
DERIVED content (`MontesData.C` rationality, the decomposition identity, `UndecidedVanishes`) is
PROVED in `Decomposition.lean`/`CountingModel.lean`. No rationality is asserted anywhere in M1/C1/C2.
The genuine `p`-adic count realizing a `MontesData` is the un-constructed measure foundation.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MontesAxiom

open LeanUrat CountingModel RatFn

/-! ## The pure-counting per-node cell datum (the count shadow of `PadicMeasure.OMCell`) -/

/-- **A pure-counting OM cell** (the count shadow of `PadicMeasure.OMCell`, native to `ClusterShape`).
One residual-shape stratum on one order-`r` Newton-polygon face, recording exactly the counting data
the eq-(4.2) per-node factorization consumes — with NO reference to the opaque Haar measure:

* `dS` — the residual-stratum degree `d_S` (the `T_BB3` count is over a degree-`d_S` residual);
* `δ` — the residue-extension degree (so the residual count is over `F_{q^δ}`, `T_BB3 = (q^δ)^{d_S-1}`);
* `polygon` — the cell's lattice Newton-polygon face, feeding the `T_BB1` box count (`L4.bb1Value`);
* `children` — the multi-child descent list `List ClusterShape`, each strictly smaller (`cells_descend`).

This bundles C2 honestly: the `(q^δ)^{d_S-1}` factor IS the residual-equidistribution count. -/
structure CountCell where
  /-- residual-stratum degree `d_S` (the `T_BB3` count is over a degree-`d_S` residual). -/
  dS : ℕ
  /-- residue-extension degree `δ` (the residual count is over `F_{q^δ}`). -/
  δ : ℕ
  /-- the cell's lattice Newton-polygon face (the `T_BB1` box count). -/
  polygon : L4.LatticePolygon
  /-- the descent children of this cell (each strictly smaller cluster `treeSize`, GMN-III). -/
  children : List ClusterShape

/-! ## The count-native cell coefficient and self-loop pivot

These are the pure-counting analogues of `PadicMeasure.cellCoeff`/`PadicMeasure.omPivot`, built only
from the proved blocks `T_BB3` (residual count `(q^δ)^{dS-1}`), `T_BB1` (box count `L4.bb1Value`), and
the `L5fix` self-loop exponent. No opaque Haar object appears. -/

/-- **The count-native per-cell coefficient** `(q^δ)^{dS-1} · bb1Value polygon q`: the residual count
over `F_{q^δ}` (`T_BB3`, = the C2 residual-equidistribution count) times the Newton-box count (`T_BB1`,
`L4.bb1Value`). The `coeff` factor of the eq-(4.2) per-node sum. -/
noncomputable def countCellCoeff (c : CountCell) : ℕ → ℚ :=
  fun q => ((q : ℚ) ^ c.δ) ^ (c.dS - 1) * L4.bb1Value c.polygon q

/-- **The count-native self-loop pivot** for a cluster of `treeSize s`: the geometric factor
`1 − q^{-w(s)}` (`w = L5fix.selfLoopExponent`) at ramifying nodes (`s ≥ 2`), the trivial `1` at leaves
(`s < 2`). This is the closed-form value of the geometric self-loop sum (the `1/(1-r)` resummation of
`NestedCollapse.geometricLimit_of_selfLoop`). Pole-free on `q > 1` by `L5fix.selfLoop_geometric`. -/
noncomputable def countPivot (s : ℕ) : ℕ → ℚ :=
  fun q => if 2 ≤ s then 1 - ((q : ℚ) ^ L5fix.selfLoopExponent s)⁻¹ else 1

/-! ### The three factors are each rational (PROVED, no clusterMeasure / AX_cellRecursion) -/

/-- The `T_BB1` box count `q ↦ (1-q⁻¹)^V q^{-A}` is a uniform rational function of `q`. Re-proved
inline (the `PadicMeasure.bb1_isRational` content) so the count path does NOT import `PadicMeasure`. -/
theorem bb1Value_isRational (pg : L4.LatticePolygon) : IsRationalFn (fun q => L4.bb1Value pg q) := by
  set V := L4.newtonVertexCount pg with hV
  set A := L4.newtonExponent pg with hA
  refine ⟨(Polynomial.X - 1) ^ V, Polynomial.X ^ (V + A), ?_, fun q hq => ?_⟩
  · exact pow_ne_zero _ Polynomial.X_ne_zero
  · have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero _ hqne
    · simp only [L4.bb1Value, ← hV, ← hA, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one]
      have h1 : (1 - (q : ℚ)⁻¹) = ((q : ℚ) - 1) / (q : ℚ) := by field_simp
      rw [h1, div_pow, pow_add]
      ring

/-- The residual count `q ↦ (q^δ)^{dS-1} = q^{δ(dS-1)}` is a uniform rational function of `q` (its
representing numerator is the non-constant monomial `X^{δ(dS-1)}` — the BB3 wild-prime mechanism, NOT
a constant). This is the count shadow of `PadicMeasure.residualCountFn_isRational`. -/
theorem residualCount_isRational (δ d : ℕ) :
    IsRationalFn (fun q : ℕ => ((q : ℚ) ^ δ) ^ (d - 1)) := by
  have hrw : (fun q : ℕ => ((q : ℚ) ^ δ) ^ (d - 1)) = fun q : ℕ => (q : ℚ) ^ (δ * (d - 1)) := by
    funext q; rw [← pow_mul]
  rw [hrw]
  exact isRationalFn_qpow (δ * (d - 1))

/-- `countCellCoeff c` is a uniform rational function of `q`: the residual count `(q^δ)^{dS-1}`
(rational by `residualCount_isRational`, numerator the non-constant monomial `X^{δ(dS-1)}`) times the
`T_BB1` box count `bb1Value polygon` (rational by `bb1Value_isRational`). -/
theorem countCellCoeff_isRational (c : CountCell) : IsRationalFn (countCellCoeff c) := by
  unfold countCellCoeff
  exact isRationalFn_mul (residualCount_isRational c.δ c.dS) (bb1Value_isRational c.polygon)

/-- `countPivot s` is a uniform rational function of `q`: ramifying branch `(q^w - 1)/q^w` (pole-free
on `q > 1`), leaf branch the constant `1`. -/
theorem countPivot_isRational (s : ℕ) : IsRationalFn (countPivot s) := by
  unfold countPivot
  by_cases h : 2 ≤ s
  · simp only [h, if_true]
    refine ⟨Polynomial.X ^ L5fix.selfLoopExponent s - 1,
      Polynomial.X ^ L5fix.selfLoopExponent s, pow_ne_zero _ Polynomial.X_ne_zero,
      fun q hq => ?_⟩
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    refine ⟨pow_ne_zero _ hq0, ?_⟩
    rw [eq_div_iff (pow_ne_zero _ hq0)]
    field_simp
  · simp only [h, if_false]
    exact isRationalFn_const 1

/-- `countPivot s q ≠ 0` for every `q > 1`: ramifying branch by `L5fix.selfLoop_geometric` (positive),
leaf branch `1`. -/
theorem countPivot_ne (s : ℕ) (q : ℕ) (hq : 1 < q) : countPivot s q ≠ 0 := by
  unfold countPivot
  by_cases h : 2 ≤ s
  · simp only [h, if_true]
    exact ne_of_gt (L5fix.selfLoop_geometric s q h hq)
  · simp only [h, if_false]
    exact one_ne_zero

/-! ## The BOX-WISE measure-theoretic primitives — what is PROVED vs the minimal axiom

The 2026-06-21 box-wise refactor decomposes the per-node count factorization into four pieces. THREE
of them are GENUINELY PROVED here (lemmas, NOT fields/axioms):

* **box-volume `T_BB1`** — the Newton-box counting/Haar volume of one cell `= (1-q⁻¹)^V·q^{-A}`, an
  honest lattice count (`L4.cellVolume_eq`, re-exposed below as `boxVolume_eq`);
* **residual-config count `T_BB3`** — the finite-field count of the refinement-triggering residual
  configurations over `F_{q^δ}` is `(q^δ)^{dS-1}` (proved below as `residualBoxCount` directly from
  the squarefree count `L3Squarefree.card_squarefreeMonicDegree`, an honest finite-field count);
* **box-additivity** — the cluster measure is the finite SUM over the cell partition of per-box
  measures, self-loop resummed by the pivot (proved as `clusterCount_boxSum` / `clusterCount_rec`,
  pure `List.sum` arithmetic).

The FOURTH piece — that the abstract per-box `p`-adic Haar volume EQUALS this proved
box-volume×residual-count, and that the node measure is box-additive (the measure exists) — is the
SINGLE minimal irreducible measure axiom (`MontesData.boxHaarEquidist` + `MontesData.nodeMeasure_boxSum`,
the box-Haar normalization + C2 residual equidistribution). It is the genuine measure-wall content;
its RHS factors are the proved lemmas, only the *identification* with the Haar volume is assumed. -/

/-- **Box-volume `T_BB1`, re-exposed as a box-wise lemma (PROVED).** For a Newton-box (lattice polygon)
`pg` and residue size `Q`, the Newton-box counting/Haar volume `cellVol pg Q` — given the cited
per-coordinate box/shell factorization `hfactor` (the only measure input of BB1, `notes/L4_proof.md
§0`, an `[O_δ : p^m O_δ] = Q^m` lattice count) — equals the closed lattice value `bb1Value pg Q =
(1-Q⁻¹)^{V(pg)}·Q^{-A(pg)}`. This is exactly `L4.cellVolume_eq`; we re-state it as the box-wise volume
primitive consumed by `countCellCoeff`. PROVED (`[core]`). -/
theorem boxVolume_eq
    (cellVol : L4.LatticePolygon → ℕ → ℚ) (pg : L4.LatticePolygon) (Q : ℕ) (hQ : 1 ≤ Q)
    (hfactor : cellVol pg Q = ∏ i : Fin pg.width, L4.columnMeasure pg Q i) :
    cellVol pg Q = L4.bb1Value pg Q :=
  L4.cellVolume_eq cellVol pg Q hQ hfactor

/-- **Residual-config count `T_BB3` over the box (PROVED).** Over the residue field `F` of size
`Q = q^δ` of one cell, the number of refinement-triggering (non-squarefree) monic degree-`dS`
residual configurations is `Q^{dS-1} = (q^δ)^{dS-1}` — the residual-equidistribution count that is the
`(q^δ)^{dS-1}` factor of `countCellCoeff`. PROVED here directly from the honest finite-field counts
`L3.card_monicDegree` (`#monic = Q^{dS}`) and `L3Squarefree.card_squarefreeMonicDegree`
(`#squarefree = Q^{dS} - Q^{dS-1}`), so the box-wise residual count is a GENUINE finite-field count,
not a free monomial. This is the `T_BB3` value (cf. `PadicMeasure.T_BB3`), inlined so the count path
needs only the light `L3`/`L3Squarefree`. `[core]`. -/
theorem residualBoxCount (F : Type*) [Field F] [Finite F] (dS : ℕ) (hd : 2 ≤ dS) :
    Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R}
      = Nat.card F ^ (dS - 1) := by
  classical
  set Q := Nat.card F with hQ
  let e : {R : Polynomial F // R.Monic ∧ R.natDegree = dS}
      ≃ {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R}
        ⊕ {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R} :=
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
      Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS} = Q ^ dS := by
    have := L3.card_monicDegree (F := F) dS
    simpa [L3.monicDegree, hQ] using this
  have hsf_eq :
      Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R}
        = Q ^ dS - Q ^ (dS - 1) := by
    have := L3Squarefree.card_squarefreeMonicDegree (F := F) dS hd
    simpa [L3.squarefreeMonicDegree, hQ] using this
  have hQpos : 0 < Q := by rw [hQ]; exact Nat.card_pos
  have hfin_monic : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = dS} :=
    Nat.finite_of_card_ne_zero (by rw [hmonic_eq]; exact pow_ne_zero dS hQpos.ne')
  haveI hfin_sum :
      Finite ({R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R}
        ⊕ {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R}) :=
    Finite.of_equiv _ e
  haveI : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R} :=
    Finite.sum_left {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R}
  haveI : Finite {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R} :=
    Finite.sum_right {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R}
  have hsum : Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS}
      = Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ Squarefree R}
        + Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R} := by
    rw [Nat.card_eq_of_bijective e e.bijective, Nat.card_sum]
  rw [hmonic_eq, hsf_eq] at hsum
  have hpow_le : Q ^ (dS - 1) ≤ Q ^ dS := by
    apply Nat.pow_le_pow_right <;> omega
  omega

/-- **The residual-equidistribution count value is the `(q^δ)^{dS-1}` factor (PROVED tie).** When the
cell's residue field `F` has size `q^δ` (`Nat.card F = q^δ`), the proved finite-field residual count
`residualBoxCount` is exactly the `(q^δ)^{dS-1}` factor that `countCellCoeff` uses. So the residual
factor of `countCellCoeff` is a GENUINE finite-field count, not a free monomial. `[core]`. -/
theorem residualBoxCount_eq_factor (F : Type*) [Field F] [Finite F] (q δ dS : ℕ)
    (hF : Nat.card F = q ^ δ) (hd : 2 ≤ dS) :
    (Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R} : ℚ)
      = ((q : ℚ) ^ δ) ^ (dS - 1) := by
  rw [residualBoxCount F dS hd, hF]
  push_cast
  ring

/-! ## The standalone pure-counting cluster recursion `clusterCount`

`clusterCount` is the eq-(4.2) per-node count factorization as a STANDALONE well-founded recursion
over the raw count data (`cells`, `treeSize`) plus the strict-descent hypothesis. Defining it before
`MontesData` lets the M1 field `nodeMultiplicativity` reference it directly (the count-limit equals
this defined recursion), so `C_T` is a genuine recursively-defined function of counts — NEVER an
opaque carried symbol. -/

/-- **The standalone pure-counting cluster volume `clusterCount cells treeSize h_descend T q`.**

By well-founded recursion on `treeSize` (decreasing via the strict-descent hypothesis `hdesc`), this
is the faithful eq-(4.2) count factorization:

    clusterCount T q = ( Σ_{cells c} countCellCoeff c q · ∏_{ch} clusterCount ch q ) / countPivot (treeSize T) q

i.e. `(T_BB3 residual count) × (T_BB1 box count) × ∏_children`, the self-loop resummed by the geometric
pivot. Built ENTIRELY from counting blocks (`countCellCoeff` = `T_BB3 × T_BB1`, `countPivot` = the
`L5fix` self-loop geometric limit) — NO opaque Haar measure. -/
noncomputable def clusterCount
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (q : ℕ) : ℚ :=
  ((cells T).attach.map (fun c =>
      countCellCoeff c.1 q
        * (c.1.children.attach.map (fun ch => clusterCount cells treeSize hdesc ch.1 q)).prod)).sum
    / countPivot (treeSize T) q
termination_by treeSize T
decreasing_by exact hdesc T c.1 c.2 ch.1 ch.2

/-- **The `clusterCount` recursion-unfold lemma** (count shadow of `clusterMeasureModel_rec`). The
well-founded recursion equals the plain `cells`-map form (the two `attach`es only carry membership
proofs the RHS does not reference). Proved by `List.attach_map_val`. -/
theorem clusterCount_rec
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (q : ℕ) :
    clusterCount cells treeSize hdesc T q
      = ((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize hdesc ch q)).prod)).sum
        / countPivot (treeSize T) q := by
  rw [clusterCount]
  congr 1            -- peel `_ / countPivot _ q`
  congr 1            -- peel `(_).sum`
  have hchildren : ∀ (c : CountCell),
      (c.children.attach.map (fun ch => clusterCount cells treeSize hdesc ch.1 q))
        = c.children.map (fun ch => clusterCount cells treeSize hdesc ch q) := by
    intro c
    exact List.attach_map_val (l := c.children)
      (f := fun ch => clusterCount cells treeSize hdesc ch q)
  simp only [hchildren]
  exact List.attach_map_val (l := cells T)
    (f := fun c => countCellCoeff c q
      * (c.children.map (fun ch => clusterCount cells treeSize hdesc ch q)).prod)

/-! ### Box-additivity (PROVED): the cluster measure is the per-box sum over the cell partition

`clusterCount T q = (Σ over the cell partition of per-box measures) / countPivot`. This is the
counting-additivity of the measure over the finite cell partition (`List.sum`/`Finset.sum`), self-loop
resummed by the geometric pivot. It is PROVED arithmetic, not a measure assumption: it merely re-views
the `clusterCount` recursion as a sum over boxes. -/

/-- **Box-additivity, abstract form (PROVED).** If a per-box measure `m : CountCell → ℚ` agrees with
`countCellCoeff · q · ∏_children` on every cell of `T` — i.e. on each box it is the box-volume ×
residual-count times the children product — then `clusterCount T q` is the finite SUM of those per-box
measures over the cell partition, divided by the self-loop pivot. Pure `List.sum` arithmetic
(`List.map_congr_left` + `clusterCount_rec`); `[core]`. -/
theorem clusterCount_boxSum
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (q : ℕ)
    (m : CountCell → ℚ)
    (hm : ∀ c ∈ cells T, m c
        = countCellCoeff c q * (c.children.map (fun ch => clusterCount cells treeSize hdesc ch q)).prod) :
    clusterCount cells treeSize hdesc T q
      = ((cells T).map m).sum / countPivot (treeSize T) q := by
  rw [clusterCount_rec cells treeSize hdesc T q]
  congr 1
  congr 1
  exact (List.map_congr_left hm).symm

/-! ## (RETIRED, W4b 2026-07-21) M1 `structure MontesData` + its namespace

The `MontesData` structure (shape menu, stratum counts, partition, the box-wise
`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` fields, tails) and its derived namespace
(`C`, `C_rec`, `nodeMultiplicativity`, `stratum_tendsto_C`, `shapesOf_finite`,
`decidedCount_eq_sum`, `discriminantTail_tendsto`, `undecidedVanishes`,
`countingDensity_is_decided_limit`) formerly lived here. They are RETIRED VERBATIM to
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt` (blueprint W4b — see the module header).
The V2 replacement is `LeanUrat.MontesV2.MontesDataV2` (abstract per-shape coefficient `C` +
`C_isRational` + `stratum_tendsto_C`), whose real instance is `OM.RealInstanceV2.realD2` and whose
trivial witness is `Witness.trivD2`. -/

/-! ## C1 — the self-loop rescale exponent `w(s)` and ratio `r(s)`, PROVED as the box q-power

Stated SEPARATELY from M1: M1 gives the existence of the self-loop; C1 supplies the precise rescale
ratio `r(s) = Q^{-w(s)}`, `w(s) = s(s+1)/2 − 1`, NOW PROVED to be the Newton-box count's q-power
`= blockExponent s − 1` (the within-block box × Vandermonde rescale of `NestedCollapse`). -/

/-- **C1: the per-level self-similar rescale exponent and ratio (`lem:rescale`).** For a size-`s`
self-loop at residue cardinality `Q`, the single-block rescale ratio is `r(s) = Q^{-w(s)}` with
`w(s) = s(s+1)/2 − 1`. `w` reuses `L5fix.selfLoopExponent`. -/
structure RescaleC1 where
  /-- The rescale exponent `w(s)`, tied to the existing `L5fix.selfLoopExponent`. -/
  w : ℕ → ℕ
  /-- `w` IS `s ↦ s(s+1)/2 − 1` (`L5fix.selfLoopExponent`). -/
  hw : w = L5fix.selfLoopExponent
  /-- The single-block rescale ratio `r(s, Q) = Q^{-w(s)}` at residue cardinality `Q`. -/
  r : ℕ → ℕ → ℚ
  /-- `r` IS the `Q`-power `Q^{-w(s)}`. -/
  hr : ∀ s Q, r s Q = ((Q : ℚ) ^ w s)⁻¹

namespace RescaleC1

/-- The first values of `w`: `w 2 = 2`, `w 3 = 5`, `w 4 = 9` (blueprint `eq:rfactor`). PROVED. -/
theorem w_values (C : RescaleC1) : C.w 2 = 2 ∧ C.w 3 = 5 ∧ C.w 4 = 9 := by
  rw [C.hw]; refine ⟨?_, ?_, ?_⟩ <;> (unfold L5fix.selfLoopExponent; norm_num)

/-- **C1 self-loop pivot positivity.** For `s ≥ 2`, `q ≥ 2`, the self-loop pivot `1 − r(s,q) > 0`. -/
theorem pivot_pos (C : RescaleC1) (s q : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) :
    (0 : ℚ) < 1 - C.r s q := by
  rw [C.hr s q, C.hw]
  exact L5fix.selfLoop_geometric s q hs hq

/-- **C1 PROVED — the rescale exponent IS the within-block box q-power minus the unit.**

`w(s) = L5fix.selfLoopExponent s = s(s+1)/2 − 1` equals `NestedCollapse.blockExponent s − 1`, where
`blockExponent s = s + C(s,2)` is the within-block box × Vandermonde rescale exponent (the `T_BB1` box
q-power for a size-`s` self-loop block). So C1 is a PROVED elementary lattice-count identity, not a
free symbol: the self-loop pivot exponent is the box exponent minus one (the one unit subtracted is the
self-loop's own no-progress weight). Pure `Nat.choose`/`omega` arithmetic — `[core]`. -/
theorem selfLoopExponent_eq_blockExponent_sub_one (s : ℕ) :
    L5fix.selfLoopExponent s = NestedCollapse.blockExponent s - 1 := by
  -- blockExponent s = s + s.choose 2 = s + s(s-1)/2 = s(s+1)/2; selfLoopExponent s = s(s+1)/2 - 1.
  unfold L5fix.selfLoopExponent NestedCollapse.blockExponent
  rw [Nat.choose_two_right]
  -- goal: s * (s + 1) / 2 - 1 = (s + s * (s - 1) / 2) - 1
  have hkey : s * (s + 1) / 2 = s + s * (s - 1) / 2 := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; rfl
    · -- for s ≥ 1: s*(s-1) = s*s - s, and s + s*(s-1)/2 = (2s + s*(s-1))/2 = s*(s+1)/2
      have h1 : s * (s - 1) = s * s - s := by
        rw [Nat.mul_sub_one]
      have hs1 : 1 ≤ s := hs
      -- multiply-free: show 2 * (s + s*(s-1)/2) = 2 * (s*(s+1)/2) via divisibility
      have hdvd1 : 2 ∣ s * (s - 1) := by
        have := Nat.even_mul_pred_self s
        exact (even_iff_two_dvd).mp this
      have hdvd2 : 2 ∣ s * (s + 1) := by
        have := Nat.even_mul_succ_self s
        exact (even_iff_two_dvd).mp this
      have e1 : 2 * (s + s * (s - 1) / 2) = 2 * s + s * (s - 1) := by
        rw [Nat.mul_add, Nat.mul_div_cancel' hdvd1]
      have e2 : 2 * (s * (s + 1) / 2) = s * (s + 1) := Nat.mul_div_cancel' hdvd2
      have e3 : 2 * s + s * (s - 1) = s * (s + 1) := by
        rw [h1]
        have : s ≤ s * s := Nat.le_mul_of_pos_left s hs
        cases s with
        | zero => rfl
        | succ k => ring_nf; omega
      omega
  rw [hkey]

end RescaleC1

/-! ## C2 — residual equidistribution / submersion (blueprint flag C2)

The residual-equidistribution content is BUNDLED honestly inside the count-factorization (the
`(q^δ)^{dS-1}` factor of `countCellCoeff` IS the `T_BB3` residual count). The separate re-export below
keeps the order-`r` equidistribution statement, reusing the existing `LeanUrat.ResidualEquidistribution`. -/

/-- **C2: residual equidistribution / submersion (`ax:multiplicativity`, analytic clause).** -/
def ResidualEquidistributionC2 {Fq : Type*} [Field Fq] [Finite Fq] (t : OMType Fq) : Type _ :=
  ResidualEquidistribution t

/-- C2 re-export of the uniform-measure conclusion: any value set has conditional probability
`#S / |F_r|^{d}`. -/
theorem ResidualEquidistributionC2.uniform_eq {Fq : Type*} [Field Fq] [Finite Fq]
    {t : OMType Fq} (E : ResidualEquidistributionC2 t) (S : Finset t.Fr) :
    E.condProb S = (S.card : ℚ) / (Nat.card t.Fr : ℚ) ^ E.residualSideDegree :=
  E.uniform S

end LeanUrat.MontesAxiom
