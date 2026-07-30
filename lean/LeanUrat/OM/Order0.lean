/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MontesAxiom
import LeanUrat.RatFn
import LeanUrat.L4

/-!
# Order0 — the CORRECTED per-node coefficient (engine-reconciled, Phase-A Wave 1)

**Provenance (`notes/VACUITY_SIGMA_BLUEPRINT.md` §2.6–§2.7, 2026-07-02).** The per-node coefficient
semantics of `MontesAxiom.clusterCount` / `countCellCoeff` were found NOT to match the genuine
p-adic stratum densities (defects D1–D6 of §2.6: the `(q^δ)^{dS−1}` factor is the aggregate — not
per-cell — residual count; `bb1Value` already integrates over on-face residual values, so pairing it
with any residual count double-counts; the per-node aggregation must be a CHOICE-COUNT × volume
product, not a sum over factor-cells; and the self-loop pivot belongs to cluster nodes only, never
the root). The corrected form was extracted from the validated engine (`om_density_engine.py`,
BCFG-exact through `n = 6`) and verified EXACT by brute force on every tested stratum (all 14
order-0 separable `(q, n, λ)` cells for `q ∈ {2,3,5}`, `n ∈ {2,3}`; a non-generic slope-`−1/2`
stratum; a non-flat `n = 4` face with per-residual-shape resolution).

This module is a PURE ADDITION (§2.7 architecture decision): the corrected machinery lives here, on
top of the existing payload (`MontesAxiom.CountCell`), and the old `clusterCount` path is left in
place (its per-node semantics documented wrong for multi-cell nodes) until Phase B retires it. The
Phase-A capstone `montes_order0` consumes `rootCount` below on CHILDLESS (separable order-0) shapes.

**The corrected root-node value** (for a node with cell list `cells T`, all cells sharing the
single selected side/polygon and the residue-extension degree `δ`):

    rootCount T q = N(cells T)(q^δ) · q^{−B(cells T)} · ∏_cells ∏_children clusterCount …

* `N(cells)(Q) = ∏_d ff(avail_d(Q), k_d)/k_d!` — the residual CHOICE COUNT: unordered choices of
  `k_d` DISTINCT degree-`d` monic irreducible residual factors, `k_d` = the multiplicity of `d` in
  the payload's `dS`-multiset; `avail_1 = Q − 1` (the face-punctured linear pool), `avail_d = M_d(Q)`
  (the necklace count) for `d ≥ 2`. For the order-0 separable shape of pattern λ this is exactly
  `m_λ(Q) = ∏_d C(M_d(Q), mult_d λ)` up to the `avail_1` convention (numeric gate §2.6).
* `B(cells) = newtonExponent(polygon) + Σ_c dS` — the PER-CONFIGURATION box-volume exponent (the
  polygon's lattice exponent PLUS one `q`-digit per residual coefficient; NO `(1 − q⁻¹)^V` factor —
  that factor arises only when integrating over the residual choices, which here are COUNTED).
* NO `countPivot` division at the root (D4): the geometric self-loop resummation belongs to the
  descent-conditioned cluster nodes (the `β_e` fixpoint), where `clusterCount` correctly applies it.
* Children are still evaluated by the OLD cluster recursion at the parent `q` — DEAD for the
  Phase-A childless shapes; the base-changed `q^{δ·D}` child evaluation is the Phase-B obligation.

Rationality of `rootCount` on childless shapes is PROVED below (`rootCount_isRational_of_leaf`):
the choice count is the evaluation of an explicitly-constructed polynomial, the volume is an inverse
`q`-power, and the children product collapses to `1`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.Order0

open LeanUrat LeanUrat.MontesAxiom RatFn Polynomial

/-! ## The necklace / choice-count polynomials -/

/-- **The necklace polynomial** `M_d(X) = (1/d)·Σ_{e ∣ d} μ(e)·X^{d/e}`. At a prime power `Q` its
value is the number of monic irreducible degree-`d` polynomials over `F_Q` (Gauss; the in-repo
finite-field count is `L3Gauss.gauss_necklace_count`); at EVERY natural `Q` it is the number of
aperiodic necklaces of length `d` over `Q` letters (nonnegativity/integrality at all `Q` is the
`OM/Necklace.lean` module's obligation, not needed for rationality). -/
noncomputable def necklacePoly (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / (d : ℚ)) *
    ∑ e ∈ d.divisors, Polynomial.C ((ArithmeticFunction.moebius e : ℤ) : ℚ) * Polynomial.X ^ (d / e)

/-- **The degree-`d` residual-factor pool polynomial** on a genuine face: `X − 1` at `d = 1` (the
face endpoint coefficient is a unit, so the linear residual factor `y − c` has `Q − 1` choices —
the punctured-pool convention validated in §2.6 D6) and the necklace `M_d` for `d ≥ 2`. -/
noncomputable def availPoly (d : ℕ) : Polynomial ℚ :=
  if d = 1 then Polynomial.X - 1 else necklacePoly d

/-- Falling-factorial polynomial `ff(P, k) = ∏_{i < k} (P − i)` — the ordered distinct-choice
numerator. -/
noncomputable def ffPoly (P : Polynomial ℚ) (k : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range k, (P - Polynomial.C (i : ℚ))

/-- The `dS`-multiset of a cell list (as a `List ℕ`): one entry per cell — for the Phase-A payload
(one cell per distinct residual factor, `dS` = the factor degree) this is the factor-degree pattern
λ of the node's residual. -/
def dSList (cells : List CountCell) : List ℕ := cells.map (fun c => c.dS)

/-- **The per-node residual CHOICE-COUNT polynomial** (in the base-`Q = q^δ` variable):
`∏_{d ∈ pattern} ff(avail_d, k_d)/k_d!` — for each distinct degree `d` with multiplicity `k_d` in
the `dS`-multiset, the number of UNORDERED choices of `k_d` distinct degree-`d` monic irreducible
residual factors. This is the engine's `CFG`/`shape_count_nonzero` and §2.6's `N_S`. -/
noncomputable def nodeChoicePoly (cells : List CountCell) : Polynomial ℚ :=
  ∏ d ∈ (dSList cells).toFinset,
    Polynomial.C (1 / (Nat.factorial ((dSList cells).count d) : ℚ)) *
      ffPoly (availPoly d) ((dSList cells).count d)

/-- The node's residue-extension degree `δ`, read off the head cell (`1` on the empty list; all
cells of one node share `δ`). -/
def nodeDelta (cells : List CountCell) : ℕ := ((cells.head?).map (fun c => c.δ)).getD 1

/-- The choice-count polynomial in the AMBIENT variable `q`: `nodeChoicePoly` composed with
`X^δ` (the residual choices live over `F_{q^δ}`). Still a genuine polynomial in `q`. -/
noncomputable def nodeChoicePolyQ (cells : List CountCell) : Polynomial ℚ :=
  (nodeChoicePoly cells).comp (Polynomial.X ^ nodeDelta cells)

/-- **The per-configuration box-volume exponent** `B = newtonExponent(polygon) + Σ_c dS` (§2.6):
the polygon's lattice exponent (the off-face coefficient constraints) PLUS one `q`-digit per
residual coefficient (each of the `Σ dS` on-face residual digits refines its coefficient ball by
one power of `q`). The polygon is read off the head cell (all cells of one node share the single
selected side). `B = 0` on the empty cell list. -/
def nodeVolumeExp (cells : List CountCell) : ℕ :=
  match cells with
  | [] => 0
  | c :: rest => L4.newtonExponent c.polygon + (dSList (c :: rest)).sum

/-! ## The corrected root-node coefficient -/

/-- **The corrected root-node coefficient** (§2.6 boxed formula, root case): CHOICE COUNT (at
`Q = q^δ`) × per-configuration volume `q^{−B}` × the descent-children product. NO pivot at the root
(D4). On childless (order-0 separable) shapes the children product is `1` and this is exactly
`m_λ(q^δ) · q^{−B}` — verified EXACT against brute force on every §2.6 stratum. -/
noncomputable def rootCount (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (q : ℕ) : ℚ :=
  (nodeChoicePolyQ (cells T)).eval (q : ℚ)
    * ((q : ℚ) ^ nodeVolumeExp (cells T))⁻¹
    * ((cells T).map (fun c =>
        (c.children.map (fun ch => clusterCount cells treeSize hdesc ch q)).prod)).prod

/-! ## Rationality -/

/-- Evaluation of a fixed polynomial is a uniform rational function of `q` (`num := P`, `den := 1`). -/
theorem isRationalFn_polyEval (P : Polynomial ℚ) : IsRationalFn (fun q => P.eval (q : ℚ)) :=
  ⟨P, 1, one_ne_zero, fun _ _ => ⟨by simp, by simp⟩⟩

/-- The inverse `q`-power `q ↦ (q^B)⁻¹` is a uniform rational function (`num := 1`, `den := X^B`). -/
theorem isRationalFn_invQpow (B : ℕ) : IsRationalFn (fun q => ((q : ℚ) ^ B)⁻¹) := by
  refine ⟨1, Polynomial.X ^ B, pow_ne_zero _ Polynomial.X_ne_zero, fun q hq => ?_⟩
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_⟩
  · simp only [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ hqne
  · simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [inv_eq_one_div]

/-- **Rationality of the corrected root coefficient on CHILDLESS shapes** (the Phase-A /
`montes_order0` case: every payload cell is a leaf). The children product collapses to `1`; what
remains is polynomial-evaluation × inverse-`q`-power. -/
theorem rootCount_isRational_of_leaf (cells : ClusterShape → List CountCell)
    (treeSize : ClusterShape → ℕ)
    (hdesc : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) (hleaf : ∀ c ∈ cells T, c.children = []) :
    IsRationalFn (fun q => rootCount cells treeSize hdesc T q) := by
  have heq : (fun q => rootCount cells treeSize hdesc T q)
      = fun (q : ℕ) => (nodeChoicePolyQ (cells T)).eval (q : ℚ)
          * ((q : ℚ) ^ nodeVolumeExp (cells T))⁻¹ := by
    funext q
    rw [rootCount]
    have h1 : ((cells T).map (fun c =>
        (c.children.map (fun ch => clusterCount cells treeSize hdesc ch q)).prod)).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      rw [hleaf c hc]
      rfl
    rw [h1, mul_one]
  rw [heq]
  exact isRationalFn_mul (isRationalFn_polyEval _) (isRationalFn_invQpow _)

end LeanUrat.OM.Order0
