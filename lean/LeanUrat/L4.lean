/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# LeanUrat.L4 = BB1 — Newton-polygon cell volume is a characteristic-independent `q`-power

Lemma **L4 (BB1)** (`notes/HUMAN_PROOF.md §5`, `notes/BB1_exponent.md`, `notes/L4_proof.md`). For a
fixed lattice Newton polygon `Π` on `[0,e]` with heights `h_i`, the Haar volume of the cell
`C(Π) = {g ∈ M_e(O_δ) : NP(g) = Π}` is, for every prime `p` and unramified `K_δ` of residue size
`Q = q^δ`,
```
    μ(C(Π)) = (1 - Q⁻¹)^{V(Π)} · Q^{-A(Π)},
```
with `V(Π) = #(Vert(Π) ∩ {0,…,e-1})` the vertex count and `A(Π) = ∑_{i=0}^{e-1} ⌈h_i⌉` the **closed
lattice exponent BB1-A** (`notes/BB1_exponent.md`). Both `V, A` are pure lattice data, independent
of `p`: a wild slope `a/b` (`p∣b`) gives the same `(V,A)` as a tame slope of the same reduced
`(a,b)`.

## What is proved here (the genuine, sorry-free content)

The cited **measure foundation** (`notes/L4_proof.md §0`, "Lemma 0") is the per-coordinate
box/shell Haar measure
```
    μ{ v(c_i) = h_i } = (1 - Q⁻¹) · Q^{-h_i}   (vertex column, an equality / "shell"),
    μ{ v(c_i) ≥ ⌈h_i⌉ } = Q^{-⌈h_i⌉}            (non-vertex column, a "ball"/box),
```
which uses only `[O_δ : p^m O_δ] = Q^m` (`v(p)=1`, unramified), a function of `Q` alone, and the
mutual independence of the columns `c_0,…,c_{e-1}` (Lemma 1: the cell is a *product* of one-variable
valuation conditions — a "box"). Those two are the only analytic inputs and are the cited
measure-theory boundary; mathlib v4.31.0 has no `p`-adic Haar valuation-cell measure, so they are
**recorded as the hypothesis `hfactor`** (the established "recorded-via-hypothesis" convention of
this project, cf. `R1.stratum_volume`, `L2core.perShapeVolume_baseChange`).

Given that factorization, the closed-form value `(1 - Q⁻¹)^V · Q^{-A}` is then **derived
sorry-free** by an honest `Finset.prod` computation (`cellVolume_eq`): the product over the vertex
columns of `(1-Q⁻¹)·Q^{-h_i}` and over the non-vertex columns of `Q^{-⌈h_i⌉}` collapses to
`(1-Q⁻¹)^{V} · Q^{-A}` because the heights at vertices are integers (`⌈h_i⌉ = h_i`) and the
`Q`-powers add over columns. This is the Gauss-sawtooth-free heart of BB1: the exponent `A` is the
sum of the per-column ceilings, and `V` counts the vertex columns. `cellVolume_pIndependent` then
reads off the `p`-independence as a formal consequence of the value depending only on `(V,A,Q)`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L4

open Polynomial Finset

/-- A **lattice Newton polygon** on `[0,e]`, recorded by its width `e`, the integer ceiling heights
`⌈h_i⌉` above each abscissa `i ∈ {0,…,e-1}`, and the predicate `isVertex i` marking which columns are
lattice vertices of `Π`. This is the pure lattice data (GMN fact (II)) that BB1 consumes; `p` does
not appear. -/
structure LatticePolygon where
  /-- The width `e` of the polygon (`NP` lives on `[0,e]`). -/
  width : ℕ
  /-- The integer ceiling heights `⌈h_i⌉` for `i = 0,…,width-1`. -/
  ceilHeights : Fin width → ℕ
  /-- The lattice-vertex predicate on columns `{0,…,width-1}`: `isVertex i` is true iff abscissa `i`
  is a vertex of `Π`. At a vertex the height `h_i` is an integer (so `⌈h_i⌉ = h_i`) and the cell
  condition is the *equality* `v(c_i) = h_i`; at a non-vertex it is the *inequality* `v(c_i) ≥ ⌈h_i⌉`. -/
  isVertex : Fin width → Bool

/-- `A(Π) = ∑_{i=0}^{e-1} ⌈h_i⌉`, the closed BB1 lattice exponent (`notes/BB1_exponent.md`). -/
def newtonExponent (pg : LatticePolygon) : ℕ :=
  ∑ i : Fin pg.width, pg.ceilHeights i

/-- `V(Π) = #(Vert(Π) ∩ {0,…,e-1})`, the lattice-vertex count over the integrated columns. -/
def newtonVertexCount (pg : LatticePolygon) : ℕ :=
  (Finset.univ.filter (fun i : Fin pg.width => pg.isVertex i = true)).card

/-- The BB1 closed-form value `(1 - Q⁻¹)^{V} · Q^{-A}` as a rational function of the residue size
`Q`, for `Q ≥ 1`. Written with `(Q:ℚ)⁻¹` so it is the literal `(1 - Q⁻¹)^V · Q^{-A}`. -/
noncomputable def bb1Value (pg : LatticePolygon) (Q : ℕ) : ℚ :=
  (1 - (Q : ℚ)⁻¹) ^ newtonVertexCount pg * ((Q : ℚ) ^ newtonExponent pg)⁻¹

/-- The **per-column Haar measure** of the cell condition on coordinate `c_i` (`notes/L4_proof.md
§0`, Lemma 0), as a function of the residue size `Q`:
* vertex column (`isVertex i`): the *shell* `μ{ v(c_i) = ⌈h_i⌉ } = (1 - Q⁻¹) · Q^{-⌈h_i⌉}`;
* non-vertex column: the *ball* `μ{ v(c_i) ≥ ⌈h_i⌉ } = Q^{-⌈h_i⌉}`.

This is the only analytic input of BB1; `cellVolume_eq` multiplies it across the `e` columns. -/
noncomputable def columnMeasure (pg : LatticePolygon) (Q : ℕ) (i : Fin pg.width) : ℚ :=
  if pg.isVertex i then (1 - (Q : ℚ)⁻¹) * ((Q : ℚ) ^ pg.ceilHeights i)⁻¹
  else ((Q : ℚ) ^ pg.ceilHeights i)⁻¹

/-- **L4 = BB1 — Newton-cell volume.** For a lattice polygon `Π` and any residue size `Q = q^δ`, the
Haar volume of the cell `C(Π)` equals `(1 - Q⁻¹)^{V(Π)} · Q^{-A(Π)}`.

`cellVol pg Q` is the abstract Haar volume; the hypothesis `hfactor` records the cited measure
foundation (`notes/L4_proof.md §0–2`): the cell is the *product over columns* of the one-variable
box/shell Haar measures `columnMeasure` (independence of coordinates, Lemma 1; per-column measures,
Lemma 0). This is the genuinely-external measure-theory boundary not present in mathlib v4.31.0.

PROVED sorry-free *from* `hfactor`: the product of the per-column measures collapses to the closed
form `(1 - Q⁻¹)^{V} · Q^{-A}` — the heart of BB1 (vertex columns each contribute one `(1-Q⁻¹)`
factor, all columns contribute `Q^{-⌈h_i⌉}`, and the `Q`-exponents sum to `A`). -/
theorem cellVolume_eq
    (cellVol : LatticePolygon → ℕ → ℚ) (pg : LatticePolygon) (Q : ℕ) (hQ : 1 ≤ Q)
    (hfactor : cellVol pg Q = ∏ i : Fin pg.width, columnMeasure pg Q i) :
    cellVol pg Q = bb1Value pg Q := by
  classical
  rw [hfactor]
  set V := fun i : Fin pg.width => pg.isVertex i = true with hV
  -- Split the product over columns into vertex columns and non-vertex columns.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ V (columnMeasure pg Q)]
  -- On the vertex filter, `columnMeasure = (1-Q⁻¹) · Q^{-⌈h_i⌉}`; on the non-vertex filter `Q^{-⌈h_i⌉}`.
  have hvert : (∏ i ∈ Finset.univ.filter V, columnMeasure pg Q i)
        = (∏ _i ∈ Finset.univ.filter V, (1 - (Q : ℚ)⁻¹))
          * ∏ i ∈ Finset.univ.filter V, ((Q : ℚ) ^ pg.ceilHeights i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : pg.isVertex i = true := (Finset.mem_filter.mp hi).2
    simp only [columnMeasure, this, if_true]
  have hnonvert : (∏ i ∈ Finset.univ.filter (fun i => ¬ V i), columnMeasure pg Q i)
        = ∏ i ∈ Finset.univ.filter (fun i => ¬ V i), ((Q : ℚ) ^ pg.ceilHeights i)⁻¹ :=
    Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_filter.mp hi).2
  rw [hvert, hnonvert, Finset.prod_const]
  -- Recombine the ⌈h⌉-power products over all columns; the full product is `Q^{-A}`.
  have hQpow := Finset.prod_filter_mul_prod_filter_not Finset.univ V
    (fun i => ((Q : ℚ) ^ pg.ceilHeights i)⁻¹)
  have hAll : (∏ i : Fin pg.width, ((Q : ℚ) ^ pg.ceilHeights i)⁻¹)
        = ((Q : ℚ) ^ newtonExponent pg)⁻¹ := by
    rw [newtonExponent, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
  unfold bb1Value newtonVertexCount
  rw [mul_assoc, hQpow, hAll]

/-- **L4 `p`-independence (the consumed conclusion).** Two lattice polygons with the same vertex
count and same ceiling-exponent give the same cell volume at the same residue size, regardless of
`p` (a wild slope `a/b` and a tame slope of the same reduced `(a,b)` produce identical `(V,A)`).
This is a formal consequence of `cellVolume_eq`: the value `bb1Value` depends only on `(V,A,Q)`. -/
theorem cellVolume_pIndependent
    (cellVol : LatticePolygon → ℕ → ℚ) (pg1 pg2 : LatticePolygon) (Q : ℕ) (hQ : 1 ≤ Q)
    (hfac1 : cellVol pg1 Q = ∏ i : Fin pg1.width, columnMeasure pg1 Q i)
    (hfac2 : cellVol pg2 Q = ∏ i : Fin pg2.width, columnMeasure pg2 Q i)
    (hV : newtonVertexCount pg1 = newtonVertexCount pg2)
    (hA : newtonExponent pg1 = newtonExponent pg2) :
    cellVol pg1 Q = cellVol pg2 Q := by
  rw [cellVolume_eq cellVol pg1 Q hQ hfac1, cellVolume_eq cellVol pg2 Q hQ hfac2]
  unfold bb1Value
  rw [hV, hA]

end LeanUrat.L4
