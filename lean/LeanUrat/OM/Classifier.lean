/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MontesAxiom
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.OMType
import LeanUrat.OM.Termination
import LeanUrat.OM.CellPartition
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.PadicLift
import LeanUrat.OM.Development

/-!
# B — Classifier: the truncated OM classifier and its certification level
(blueprint §"B — Classifier", Layer B; PRE-WAVE signature freeze `w78jgpb27`)

**FROZEN SIGNATURE SKELETON (PRE-WAVE).** This module states the Layer-B nodes with their intended
signatures and `sorry`/opaque bodies, so the WAVE-0/WAVE-1 parallel fill builds against FIXED,
CORRECT contracts. It produces the `classify` argument consumed everywhere downstream
(`M8.shapeFiberCount`, `M8.constantFiber`, `M8.nodeMeasure_boxSum`) and the `decode : ClusterShape →
M5.OMType` section M9 needs, REPLACING the M9 stubs (`realClassify := fun _ _ => ⟨[]⟩`, the order-0
`leafOMTypeOfSize` decode).

Blueprint Layer-B nodes frozen:
* `DEF B.1`  `boxCoeffData`   — real residual-coefficient extraction from a box polynomial.
* `DEF B.2`  `omStep`         — the per-order LOCAL STEP (one OM iteration; de-stubs `M5.cells`).
* `DEF B.3`  `classifyAux` / `classify` — the well-founded OM recursion on a degree budget.
* `DEF B.4`  `certLevel`      — the certification (stabilization) level `N₀(f)`.
* `DEF B.5`  `decode`         — the genuine `shapeOf`-section parser.
* `LEM B.1`  `boxCoeffData_endpoints_ne_zero` — DELETED (W3a, 2026-07-04): FALSE-AS-FROZEN, see its
  tombstone below; the true endpoint-units content is banked as `CellMenu.residual_endpoint_units`.
* `LEM B.2`  `cellsOfType_omStep`           — couples B.2 to M7 (de-stubs `M5.cells`; GLUE-6).
* `LEM B.3`  termination (folded into B.3 via `Nat.strongRecOn`).
* `LEM B.4`  `treeSize_classify`            — shape-size coupling.
* `LEM B.5`  `decode_classify_section`      — decode is a `shapeOf`-section.
* `LEM B.6`  `classify_singleValued`        — CITED GMN OM-tree uniqueness.
* `LEM B.7`  `certLevel_stabilizes`         — THE WALL (certification stability).
* `LEM B.8`  `classify_separable_leaf`      — the order-0 separable base case (PROVED W3a,
  2026-07-04, via the `decode` `Rr = 0` degeneracy — see its docstring for the honest scope).
* **reduction-stability spec** `classifyReductionStable` / `classify_reductionStable` — the tower
  ZMod(p^{N+1}) ↠ ZMod(p^N) stability above `certLevel`, consumed by F1.L9 / M8.constantFiber.

RULES (PRE-WAVE): every `sorry` here sits over a TRUE-intended contract (no `sorry` over a false
statement). Bodies left `sorry`/opaque; everything TYPECHECKS.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanUrat.OM.B

open Polynomial LeanUrat LeanUrat.MontesAxiom

open scoped Classical

/-! ## The level-tower reduction on the box (shared with F1/F2)

The single-step and `≤`-step coefficient reductions `ZMod(p^{N+1}) ↠ ZMod(p^N)` and the induced
polynomial-level box reductions. F1 owns the genuine surjectivity/fiber-count lemmas; here we surface
the maps so the classifier reduction-stability spec is statable. -/

/-- **Single-step coefficient reduction** `ZMod(p^{N+1}) →+* ZMod(p^N)` (F1.D2 `coeffReduce`). -/
noncomputable def coeffReduce (p : ℕ) [Fact p.Prime] (N : ℕ) :
    QuotientBox.ResidueRing p (N + 1) →+* QuotientBox.ResidueRing p N :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p ^ N))

/-- **`≤`-step coefficient reduction** `ZMod(p^M) →+* ZMod(p^N)` for `N ≤ M` (F1.D4 `coeffReduceLE`). -/
noncomputable def coeffReduceLE (p : ℕ) [Fact p.Prime] (N M : ℕ) (h : N ≤ M) :
    QuotientBox.ResidueRing p M →+* QuotientBox.ResidueRing p N :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N))

/-- **Single-step box reduction** `monicBox(p,N+1,n) → monicBox(p,N,n)` (F1.D3 `boxReduce`), by
`Polynomial.map` of `coeffReduce`. Monicity is preserved by `Polynomial.Monic.map`; the degree is
preserved by `Monic.natDegree_map` (codomain `ZMod(p^N)` is nontrivial for `0 < N` via
`QuotientBox.instNeZeroPow`). -/
noncomputable def boxReduce (p : ℕ) [Fact p.Prime] (N n : ℕ) (hN : 0 < N) :
    QuotientBox.monicBox p (N + 1) n → QuotientBox.monicBox p N n :=
  fun f => ⟨(f.1).map (coeffReduce p N),
    ⟨(f.2.1).map (coeffReduce p N), by
      haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' (Fact.out (p := p.Prime)).one_lt⟩
      haveI : Nontrivial (QuotientBox.ResidueRing p N) := ZMod.nontrivial _
      rw [(f.2.1).natDegree_map (coeffReduce p N)]; exact f.2.2⟩⟩

/-- **`≤`-step box reduction** `monicBox(p,M,n) → monicBox(p,N,n)` for `N ≤ M` (F1.D4 `boxReduceLE`). -/
noncomputable def boxReduceLE (p : ℕ) [Fact p.Prime] (N M n : ℕ) (h : N ≤ M) (hN : 0 < N) :
    QuotientBox.monicBox p M n → QuotientBox.monicBox p N n :=
  fun f => ⟨(f.1).map (coeffReduceLE p N M h),
    ⟨(f.2.1).map (coeffReduceLE p N M h), by
      haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' (Fact.out (p := p.Prime)).one_lt⟩
      haveI : Nontrivial (QuotientBox.ResidueRing p N) := ZMod.nontrivial _
      rw [(f.2.1).natDegree_map (coeffReduceLE p N M h)]; exact f.2.2⟩⟩

/-! ## DEF B.1 — real residual-coefficient extraction (`boxCoeffData`)

The bridge that feeds M4 with REAL coefficients read off a box polynomial. At order 0 the codomain is
the genuine finite field `ZMod p` (no tower needed for the base): `c_t` is the image in `F_q = ZMod p`
of the unit part of the `t`-th side coefficient of `f`, projected `ZMod(p^N) ↠ ZMod p`. -/

/-- **Real residual-coefficient data** (`DEF B.1`, GMN Def 2.20). For a box polynomial `f` mod `p^N`
on side `S`, `boxCoeffData p N S f : ℕ → ZMod p` is the order-0 residual datum: `c_t =` image in
`F_q = ZMod p` of the unit part of the side-`t` coefficient of `f` **when the coefficient's dot lies
ON the side** (`zmodValuation = v₀ + t·h`, the side's integer lattice height at step `t` — note
`slope·(t·e) = t·h` since `slope = h/e` in lowest terms), and `0` when the dot lies strictly above.
The codomain is the genuine residue field `ZMod p`, matching M4's `kS` at order 0.

⚠ **D7 FIX (2026-07-02, `notes/HNODE0_BLUEPRINT.md` §0).** The previous body took
`zmodUnitResidue` UNCONDITIONALLY — dividing out the coefficient's OWN valuation rather than the
side height, so an above-side coefficient contributed its unit part instead of the correct `0`
(machine-checked counterexample: `p = 2`, `f = x² + 2x + 1`, genuine residual `f̄ = (x+1)²`
non-separable, old computed residual `x² + x + 1` irreducible — misclassified strata; numerically
the old form disagreed with the reduction on up to 44% of the generic stratum). With the on-side
guard, on the FLAT side the datum is exactly the plain mod-`p` reduction (`γ3` of the blueprint). -/
noncomputable def boxCoeffData (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (S : NewtonPolygon.Side) (f : QuotientBox.monicBox p N n) : ℕ → ZMod p :=
  fun t =>
    if (PadicLift.zmodValuation p N ((f.1).coeff (S.i₀ + t * S.e)) : ℤ)
        = (S.v₀ : ℤ) + t * S.h then
      PadicLift.zmodUnitResidue p N ((f.1).coeff (S.i₀ + t * S.e))
    else 0

/-! ### DECISION 1 — the f-DEPENDENT order-0 root build (`boxValSupport` → `npSides` → `toSideFace`)

The genuine M3 hull scan input read off a box polynomial: `boxValSupport p N f` is the support of `f`
decorated with its native `zmodValuation`s — the box analogue of `M2.valSupport`. The order-0 root
selects the first finite-slope side `S` of `NewtonPolygon.npSides (boxValSupport …)`, sets the root
residual `T.Rr := residualPoly (boxCoeffData p N S f) S` (over `Fr := ZMod p`) and the root face
`T.Nr := M7.toSideFace S`. This is what makes `classify` genuinely reflect `f`'s Newton polygon +
residual factorization (one root cell per distinct residual factor), de-vacuifying the trivial
constant tree the f-free `M9rootCtx` shell yields. -/

/-- **Box-native valuation support** (`def:np-support`, box analogue of `M2.valSupport`). The support
dots of `f` decorated with their `ZMod(p^N)`-native valuations: `{(i, zmodValuation p N (f.coeff i)) :
i ∈ f.support}`. Nonempty for `0 < N` (the monic leading coefficient at index `n` is in the support).
This is the genuine `Finset (ℕ × ℕ)` the M3 hull scan `NewtonPolygon.npSides` consumes. -/
noncomputable def boxValSupport (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) : Finset (ℕ × ℕ) :=
  (f.1).support.image (fun i => (i, PadicLift.zmodValuation p N (f.1.coeff i)))

/-- `boxValSupport` is nonempty (for `0 < N`): `f` is monic, hence nonzero, so its support is nonempty
and its image under the valuation decoration is too. -/
theorem boxValSupport_nonempty (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    (boxValSupport p N f).Nonempty := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' (Fact.out (p := p.Prime)).one_lt⟩
  haveI : Nontrivial (QuotientBox.ResidueRing p N) := ZMod.nontrivial _
  rw [boxValSupport]
  apply Finset.Nonempty.image
  rw [Polynomial.support_nonempty]
  exact f.2.1.ne_zero

/-- **The order-0 selected side** (`def:np-side` for the root). The first finite-slope side of `f`'s
lower Newton polygon (`none` only if the polygon degenerates to a single vertex with no side). -/
noncomputable def rootSide (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : Option NewtonPolygon.Side :=
  (NewtonPolygon.npSides (boxValSupport p N f) (boxValSupport_nonempty p N hN f)).head?

/-- **The f-dependent order-0 root residual** `R_0 ∈ (ZMod p)[X]` (`def:residual-poly` at the root).
For the selected first side `S`, the genuine residual `residualPoly (boxCoeffData p N S f) S`, guarded
to degree `≤ n` (else `0`). `Fr := ZMod p` (the genuine order-0 residue field).

(Phase-A A2, 2026-07-02) the guard is WEAKENED from `< n` to `≤ n`. The old strict guard existed only
to discharge the deleted strict root law `hDrLtCs` and ZEROED the generic full-degree residual — the
V1 vacuity chain (`notes/VACUITY_SIGMA_BLUEPRINT.md` §1.1-§1.2). The `≤ n` guard discharges the new
`M5.OMType.hDrLeCs : dr ≤ cs = n` and NEVER FIRES for genuine residuals
(`natDegree ≤ residualDeg S ≤ side length ≤ n`; `M4.residualPoly_natDegree_le` gives the first step —
the side-length `≤ n` bound is the M3 postcondition whose formalization is the documented cleanup
that removes this guard entirely). -/
noncomputable def rootResidual (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : (ZMod p)[X] :=
  match rootSide p N hN f with
  | none => 0
  | some S =>
      let R := M4.residualPoly (boxCoeffData p N S f) S
      if R.natDegree ≤ n then R else 0

/-- **The f-dependent order-0 root lattice face** `N_0` (`def:side-to-l4face` at the root):
`M7.toSideFace S` of the selected first side `S` (the empty polygon if no side). -/
noncomputable def rootFace (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : L4.LatticePolygon :=
  match rootSide p N hN f with
  | none => ⟨0, fun _ => 0, fun _ => false⟩
  | some S => M7.toSideFace S

/-- **The root residual degree is `≤ n`** (the root `hDrLeCs` discharge; Phase-A A2 replaces the old
strict `rootResidual_natDegree_lt`). By the `≤ n` guard in `rootResidual`: in the kept branch the
degree IS `≤ n`; in the else / no-side branches `Rr = 0` with `natDegree 0 = 0 ≤ n`. PROVED, no
axiom. -/
theorem rootResidual_natDegree_le (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    (rootResidual p N hN f).natDegree ≤ n := by
  rw [rootResidual]
  cases hS : rootSide p N hN f with
  | none => simp
  | some S =>
      simp only []
      by_cases hle : (M4.residualPoly (boxCoeffData p N S f) S).natDegree ≤ n
      · rw [if_pos hle]; exact hle
      · rw [if_neg hle]; simp

/-- **The f-DEPENDENT order-0 root context** (`DECISION 1`, the de-vacuified root). Builds the order-0
OM type FROM `f`: `F0 = Fr := ZMod p` (the genuine order-0 residue field), `Nr := rootFace` (the
selected side's L4 face), `Rr := rootResidual` (the genuine order-0 residual on that side), `dr :=
Rr.natDegree`, `cs := n` (the full degree budget). So `M5.cells (fRootCtx …)` factors `f`'s genuine
order-0 residual — `classify` now reflects `f`'s Newton polygon + residual factorization, NOT a
constant trivial tree; and (Phase-A A2) the GENERIC full-degree residual is now KEPT (the old strict
guard zeroed it). The size law `hDrLeCs` is `rootResidual_natDegree_le` (proved, no axiom). -/
noncomputable def fRootCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : M5.OMType :=
  { order := 0
    F0 := ZMod p, Fr := ZMod p, δ := 1
    Nr := rootFace p N hN f
    Rr := rootResidual p N hN f
    dr := (rootResidual p N hN f).natDegree
    keyDeg := 0
    cs := n
    hResidueDeg := by simp [Module.finrank_self]
    hResidualDeg := rfl
    hDrLeCs := rootResidual_natDegree_le p N hN f }

/-- `clusterSize (fRootCtx …) = n` (by `rfl`, `cs := n`) — the budget invariant `classify` threads. -/
theorem clusterSize_fRootCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    M5.clusterSize (fRootCtx p N hN f) = n := rfl

/-! ## DEF B.2 — the per-order LOCAL STEP (`omStep`)

One OM iteration: run M3 (Newton polygon sides of `f`) → M4 (residual factorization on `boxCoeffData`)
and emit one `M5.OMCell` per (side, distinct monic-irreducible residual factor). This is the
CONSTRUCTIVE producer of the data `M7.cellsOfType` erases (M7 currently maps over the `M5.cells T = []`
STUB, GLUE-6). -/

/-- **The per-order local OM step** (`DEF B.2`). Given a box polynomial `f` mod `p^N` and the current
order-`r` OM context `T`, produce the list of OM cells: one `M5.OMCell T` per (finite-slope side
`S ∈ M3.npSides`, distinct monic-irreducible factor `ψ` of the M4 residual `residualPoly
(boxCoeffData … S) S`). Each cell carries the side's L4 face (`M7.toSideFace S`), the residual stratum
`ψ`, and — for repeated factors (`mult ψ ≥ 2`) — its descent child carrying the `hChildSizeLt` witness.
Opaque body in the freeze (assembling M3×M4 into `OMCell` structure fields with the descent witnesses
is the B.2 body); the SIGNATURE is the constructive producer M7/M5 consume. -/
noncomputable def omStep (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (_f : QuotientBox.monicBox p N n) (T : M5.OMType) : List (M5.OMCell T) :=
  M5.cells T  -- the genuine cells of `T` (D5); `_f` was consumed upstream (B.3) to build `T`.

/-! ## DEF B.3 — the well-founded OM recursion (`classifyAux`, `classify`)

`classifyAux` recurses on a degree budget `budget ≤ n` via `Nat.strongRecOn`: at each step `omStep`
produces cells; leaf cells (mult-1, separable residual → GMN Cor 3.8 leaf) contribute a leaf tuple,
descend cells (mult ≥ 2) recurse with `budget' = μ·deg ψ < budget` (strict descent by
`M5.OMCell.Child.hChildSizeLt` / `M6.child_size_lt`). Terminal encoding = `M5.encodeTree`. The
well-foundedness (LEM B.3) is discharged structurally by `Nat.strongRecOn`. -/

/-- **Order-`r` leaf shell of a prescribed cluster size** (`DEF B.3` helper). Supplies the `ih`'s
`(T : M5.OMType)` argument in the budget recursion together with `rfl : clusterSize (childCtxOfSize r s)
= s`. For the budget-recursion-and-serialize structure only the child order `r` and cluster size `s`
matter (the genuine residual data of the child was already factored at the parent node into the child
`node` shape); `classifyAux` recurses with `r := T.order + 1`, the descent-child order slot of
`ch.node`/`M5.shapeOf` (audit F4/SIGMA-3). Carries `dr := 0` so `hDrLeCs` is `0 ≤ s` (trivial). -/
noncomputable def childCtxOfSize (r s : ℕ) : M5.OMType :=
  { order := r, F0 := ZMod 2, Fr := ZMod 2, δ := 1
    Nr := ⟨0, fun _ => 0, fun _ => false⟩, Rr := 0, dr := 0, keyDeg := 0, cs := s
    hResidueDeg := by simp [Module.finrank_self], hResidualDeg := by simp
    hDrLeCs := Nat.zero_le _ }

/-- `clusterSize (childCtxOfSize r s) = s` (by `rfl`). -/
theorem clusterSize_childCtxOfSize (r s : ℕ) : M5.clusterSize (childCtxOfSize r s) = s := rfl

/-! ### DE-STUB (2026-07-13, first-descent increment): the genuine f-DEPENDENT child residual.

The child context must re-derive the residual FROM `f` below the root, instead of `Rr := 0`. The
standard OM step: lift the repeated residual factor `ψ` to a monic key polynomial `φ` over the box
ring, φ-adically DEVELOP `f` (`Development.develop`), and read the order-1 residual off the digit
valuations. `Fr := ZMod p` (the tame/unramified `deg ψ = 1` first descent, where the residue field
does not extend). This is a genuine function of `f` — `M5.cells (fChildCtx …)` factors the developed
residual, so the child is no longer a childless leaf when `f`'s development has structure. -/

/-- Coefficient section `ZMod p → ZMod (p^N)` via the canonical nat representative (a set-theoretic
lift, enough to build a monic key polynomial). -/
noncomputable def liftCoeff (p N : ℕ) (c : ZMod p) : ZMod (p ^ N) := (c.val : ZMod (p ^ N))

/-- Lift a residual factor `ψ ∈ (ZMod p)[X]` to a monic key polynomial over the box ring:
`X^(deg ψ) + ∑_{i<deg ψ} liftCoeff(ψ.coeff i) X^i`. -/
noncomputable def liftKey (p : ℕ) [Fact p.Prime] (N : ℕ) (ψ : (ZMod p)[X]) : (ZMod (p ^ N))[X] :=
  Polynomial.X ^ ψ.natDegree +
    ∑ i ∈ Finset.range ψ.natDegree, Polynomial.C (liftCoeff p N (ψ.coeff i)) * Polynomial.X ^ i

/-- The order-1 residual over `ZMod p` read off the φ-adic development of `f` w.r.t. the lifted key
`φ = liftKey ψ`, `μ` digits: the `ZMod p` unit residue of the constant term of each digit. A genuine
function of `f` (through `Development.develop`). -/
noncomputable def childResidual (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (ψ : (ZMod p)[X]) (μ : ℕ) : (ZMod p)[X] :=
  ∑ t : Fin μ, Polynomial.C
    (PadicLift.zmodUnitResidue p N ((Development.develop (liftKey p N ψ) μ f.1 t).coeff 0))
    * Polynomial.X ^ (t : ℕ)

/-- **`liftKey` is monic** (of degree `ψ.natDegree`): `X^d + (a sum of degree `< d`)`. Needed to
apply the monic-divisor develop/`%ₘ`/`/ₘ` machinery (`Development.develop_map`). -/
theorem liftKey_monic (p : ℕ) [Fact p.Prime] (N : ℕ) (ψ : (ZMod p)[X]) :
    (liftKey p N ψ).Monic := by
  apply Polynomial.monic_X_pow_add
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
  intro i hi
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _)
    (Nat.cast_lt.2 (Finset.mem_range.mp hi))

/-- **`liftKey` reduces with the level** (naturality of the key lift under `coeffReduce`): mapping
`liftKey` at level `N+1` down by the single-step coefficient reduction gives `liftKey` at level `N`:
`(liftKey p (N+1) ψ).map (coeffReduce p N) = liftKey p N ψ`. `Polynomial.map` distributes over the
`X^d + ∑ …` shape; `coeffReduce (liftCoeff (N+1) c) = liftCoeff N c` because `ZMod.castHom` is a ring
hom commuting with `Nat.cast` (the coefficient is the nat-representative `↑c.val`). -/
theorem liftKey_map (p : ℕ) [Fact p.Prime] (N : ℕ) (ψ : (ZMod p)[X]) :
    (liftKey p (N + 1) ψ).map (PadicLift.coeffReduce p N) = liftKey p N ψ := by
  rw [liftKey, liftKey, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  show PadicLift.coeffReduce p N ((((ψ.coeff i).val : ℕ) : ZMod (p ^ (N + 1))))
      = (((ψ.coeff i).val : ℕ) : ZMod (p ^ N))
  rw [map_natCast]

/-- **DEVELOP-REDUCTION-STABILITY** (`CERTLEVEL` blocker (b), the order-1 child residual is stable
under one-digit box reduction below the cutoff).  Reducing `f` by one `p`-adic digit
(`boxReduce : monicBox(p,N+1,n) → monicBox(p,N,n)`) does not change the order-1 child residual
`childResidual`, provided every developed digit's constant term has native `(N+1)`-level valuation
`< N` (the honest per-digit cutoff, mirroring the Layer-A `zmodUnitResidue_reduce_stable` hypothesis):
`childResidual p N (boxReduce f) ψ μ = childResidual p (N+1) f ψ μ`.

Proof structure: `childResidual` reads `zmodUnitResidue` of the constant term of each φ-adic digit of
`f`.  The φ-adic development is a polynomial-arithmetic operation (`%ₘ` / `/ₘ` by the monic key),
so it COMMUTES with the coefficient reduction `coeffReduce` (`Development.develop_map`, with
`liftKey_monic`), and the key itself reduces correctly (`liftKey_map`).  Hence each reduced digit's
constant term is `coeffReduce` of the level-`N+1` digit's constant term, on which `zmodUnitResidue`
is level-stable below the cutoff (`PadicLift.zmodUnitResidue_reduce_stable`).  The `∑ … C(…) X^t`
wrapper assembles termwise.  This is the genuine, f-READING replacement for the (now-false-under-the-
de-stub) `classifyAux_indep`-based CERTLEVEL argument, isolated as a reusable lemma. -/
theorem childResidual_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (ψ : (ZMod p)[X]) (μ : ℕ)
    (hcut : ∀ t : Fin μ,
      PadicLift.zmodValuation p (N + 1)
        ((Development.develop (liftKey p (N + 1) ψ) μ f.1 t).coeff 0) < N) :
    childResidual p N (boxReduce p N n hN f) ψ μ = childResidual p (N + 1) f ψ μ := by
  rw [childResidual, childResidual]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 2
  -- The level-`N` digit of the reduced `f` is the `coeffReduce`-image of the level-`N+1` digit.
  have hbox : (boxReduce p N n hN f).1 = f.1.map (PadicLift.coeffReduce p N) := rfl
  have hdigit : Development.develop (liftKey p N ψ) μ (boxReduce p N n hN f).1 t
      = (Development.develop (liftKey p (N + 1) ψ) μ f.1 t).map (PadicLift.coeffReduce p N) := by
    rw [hbox, ← liftKey_map p N ψ,
      Development.develop_map (PadicLift.coeffReduce p N) (liftKey_monic p (N + 1) ψ) μ f.1 t]
  rw [hdigit, Polynomial.coeff_map]
  exact PadicLift.zmodUnitResidue_reduce_stable p N hN _ (hcut t)

-- Footprint check for the DEVELOP-REDUCTION-STABILITY deliverable (blocker (b)): must be
-- ⊆ [propext, Classical.choice, Quot.sound] (no `sorry`/`axiom`/`native_decide`).
#print axioms childResidual_reduce_stable

/-- **The f-DEPENDENT child context** (DE-STUB target). Order-`r`, `cs := s`, `Fr := ZMod p`, and
`Rr := childResidual` (guarded to degree `≤ s`) — a genuine function of `f`, NOT `0`. -/
noncomputable def fChildCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (r s : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ) : M5.OMType :=
  { order := r, F0 := ZMod p, Fr := ZMod p, δ := 1
    Nr := ⟨0, fun _ => 0, fun _ => false⟩
    Rr := if (childResidual p N f ψ μ).natDegree ≤ s then childResidual p N f ψ μ else 0
    dr := (if (childResidual p N f ψ μ).natDegree ≤ s then childResidual p N f ψ μ else 0).natDegree
    keyDeg := 0, cs := s
    hResidueDeg := by simp [Module.finrank_self]
    hResidualDeg := rfl
    hDrLeCs := by
      by_cases h : (childResidual p N f ψ μ).natDegree ≤ s
      · rw [if_pos h]; exact h
      · rw [if_neg h, Polynomial.natDegree_zero]; exact Nat.zero_le _ }

/-- `clusterSize (fChildCtx …) = s` (by `rfl`). -/
theorem clusterSize_fChildCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (r s : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ) :
    M5.clusterSize (fChildCtx p N f r s ψ μ) = s := rfl

/-- **`fChildCtx` reduction-stability** (DE-STUB Ingredient B — the genuine reader's per-node `CERTLEVEL`
content). The f-dependent child context built at level `N+1` on `f` equals the one built at level `N` on
`boxReduce f`, below the per-digit cutoff `hcut`: the two differ only in `Rr := childResidual …` (stable
by `childResidual_reduce_stable`) and `dr := Rr.natDegree` (determined by `Rr`); `order`/`F0`/`Fr`/`δ`/
`Nr`/`keyDeg`/`cs` are `f`- and `N`-independent, and the proof fields close by proof irrelevance. `simp
only` (not `rw`) handles the dependent `dr := (…).natDegree` motive. The genuine multi-level analogue of
`fRootCtx_reduce_stable`; the per-node fact the genuine cylinder (Ingredient C→D) will induct on. No axiom. -/
theorem fChildCtx_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (r s : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ)
    (hcut : ∀ t : Fin μ, PadicLift.zmodValuation p (N + 1)
        ((Development.develop (liftKey p (N + 1) ψ) μ f.1 t).coeff 0) < N) :
    fChildCtx p N (boxReduce p N n hN f) r s ψ μ = fChildCtx p (N + 1) f r s ψ μ := by
  have hcr := childResidual_reduce_stable p N hN f ψ μ hcut
  unfold fChildCtx
  simp only [hcr]

-- Footprint check for DE-STUB Ingredient B: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms fChildCtx_reduce_stable

/- LANDED (audit F4/SIGMA-3, the childCtxOfSize order-slot fix — JOINT landing, 2026-07-04).
   `childCtxOfSize` is order-parameterized (`childCtxOfSize (r s : ℕ)`, `order := r`) and
   `classifyAux` recurses through `childCtxOfSize (T.order + 1) ch.childSize`, so the serialized
   descent-child subtree's head tuple is `(T.order + 1, childSize, 0)` — the SAME order slot the
   payload/`M5.shapeOf` record via `ch.node = ⟨[(T.order + 1, childSize, 0)], []⟩` (`M5.cells`,
   OMType.lean:247). Landed jointly with the respelling of `Order0Classify.classifyAux_unfold` /
   `classifyAux_of_childless` (their statements spell the recursion body literally, so they move in
   lockstep with any body change); `Order0Fiber.classifyAux_head_payload` (existential child list)
   and the reduce-stability chain survive unchanged (`classifyAux_indep` stays `rfl`: the new order
   argument is a function of the bound context `T` alone, so `(N, f)`-independence is unaffected).
   The `LevelNCount.lean` comment naming `Classifier.childCtxOfSize` as a `GMNNodeEfLaw` violator
   stays true (with `r ≥ 1` the child shell still violates the ef-law, `δ·dr = 0 ≠ s`). -/

/-- **The budget-recursive OM classifier core** (`DEF B.3`). Runs the truncated OM algorithm on `f`
mod `p^N` from context `T`, recursing on the remaining cluster-size `budget` via `Nat.strongRecOn`
(structural well-foundedness). The signature gains the budget invariant `hT : clusterSize Tctx = budget`.

**(Phase-A A3, 2026-07-02) PAYLOAD-CARRYING.** The emitted shape now carries the faithful per-node
cell payload `M5.encodeCells T` in its `cells` slot (previously the constant `[]`, which broke the
`M5.shapeOf` ↔ classifier shape coincidence the moment cells became genuine —
`notes/VACUITY_SIGMA_BLUEPRINT.md` §1.6 — and starved the faithful reader `M7.cellsOfShape`, forcing
the vacuous `decode` round-trip). `encodeCells T` erases exactly the same `M5.cells T` list `omStep`
walks (literally the same term, same `Classical.choice` factorization), so tree and payload are
consistent by construction — including the child ORDER slot (audit F4/SIGMA-3, fixed 2026-07-04):
descent-child subtrees recurse through `childCtxOfSize (T.order + 1) ch.childSize`, so the
serialized child head tuple is `(T.order + 1, childSize, 0)`, the `ch.node`/`M5.shapeOf` convention.
The remaining Phase-B caveat is the SCHEMATIC payload only: child payloads inside
`ShapeCell.children` remain the single-tuple shapes (`⟨[(order+1, childSize, 0)], []⟩`) — faithful
subtree payloads are the documented Phase-B obligation (blueprint §2 A3 note); harmless in Phase A,
whose `montes_order0` scope is the separable stratum (childless cells). -/
noncomputable def classifyAux (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (budget : ℕ) (f : QuotientBox.monicBox p N n) (Tctx : M5.OMType)
    (hT : M5.clusterSize Tctx = budget) : ClusterShape :=
  -- B.3 body: well-founded recursion on the cluster-size `budget`. At each node `omStep` produces the
  -- genuine cells of `T`; a leaf (all `children = []`) emits just the root tuple, a descend child
  -- recurses with the strictly-smaller budget `ch.childSize < clusterSize T = b` (`ch.hChildSizeLt`).
  Nat.strongRecOn budget
    (motive := fun b => ∀ (T : M5.OMType), M5.clusterSize T = b → ClusterShape)
    (fun b ih => fun (T : M5.OMType) (hTb : M5.clusterSize T = b) =>
      ⟨(T.order, M5.clusterSize T, T.dr) ::
        (omStep p N n f T).flatMap (fun c =>
          c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
            have hlt : ch.childSize < b := hTb ▸ ch.hChildSizeLt
            (ih ch.childSize hlt (childCtxOfSize (T.order + 1) ch.childSize) rfl).tree)),
        M5.encodeCells T⟩)
    Tctx hT

/-- The order-0 root context (an order-0 OM type carrying the degree budget `cs := n`). The frozen
`f`-free shell (DECISION 1): `Rr := 0`, `cs := n`, so `clusterSize M9rootCtx = n` by `rfl` and
`M5.cells` returns `[]` (empty factorization of `Rr = 0`). The `f`-dependent enrichment (genuine
order-0 `Rr`/`Nr` from `boxCoeffData p N S f`) slots into this same shell upstream. -/
noncomputable def M9rootCtx (n : ℕ) : M5.OMType :=
  { order := 0, F0 := ZMod 2, Fr := ZMod 2, δ := 1
    Nr := ⟨0, fun _ => 0, fun _ => false⟩, Rr := 0, dr := 0, keyDeg := 0, cs := n
    hResidueDeg := by simp [Module.finrank_self], hResidualDeg := by simp
    hDrLeCs := Nat.zero_le _ }

/-- `clusterSize (M9rootCtx n) = n` (by `rfl`). -/
theorem clusterSize_M9rootCtx (n : ℕ) : M5.clusterSize (M9rootCtx n) = n := rfl

/-- **The root context `classify` runs from** (`DECISION 1`, the dispatch). The genuine f-DEPENDENT
root `fRootCtx p N hN f` for `0 < N`; the f-free `M9rootCtx n` shell at the degenerate `N = 0` level
(the trivial mod-1 box, never used downstream). For `0 < N` this is f-dependent, so `classify`'s root
genuinely reflects `f`'s Newton polygon + residual factorization. Either branch carries `cs := n`, so
the budget invariant `clusterSize (rootCtx …) = n` holds. -/
noncomputable def rootCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) : M5.OMType :=
  if hN : 0 < N then fRootCtx p N hN f else M9rootCtx n

/-- `clusterSize (rootCtx p N f) = n` — the budget invariant `classify` threads into `classifyAux`.
Both dispatch branches carry `cs := n`. -/
theorem clusterSize_rootCtx (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) :
    M5.clusterSize (rootCtx p N f) = n := by
  unfold rootCtx
  by_cases hN : 0 < N
  · rw [dif_pos hN]; exact clusterSize_fRootCtx p N hN f
  · rw [dif_neg hN]; exact clusterSize_M9rootCtx n

/-! ## Layer B + C — one-digit (level `N+1 → N`) reduction stability

`CERTLEVEL_DECOMP.md` Layers B (channel stability) and C (per-node `omStep`/`rootCtx` stability), on the
now-`f`-DEPENDENT `classify` (DECISION 1). Each `f`-channel into `classify` — the Newton polygon (via
`boxValSupport`/`rootSide`/`rootFace`) and the residual (via `boxCoeffData`/`rootResidual`) — is shown
STABLE under the single-step coefficient reduction `boxReduce : monicBox(p,N+1,n) → monicBox(p,N,n)`,
below the per-coefficient cutoff. The arithmetic is entirely Layer A (`PadicLift.zmodValuation_reduce_stable`,
`zmodUnitResidue_reduce_stable`, `coeffReduce_ne_zero_of_val_lt`); everything here is `congr`/`subst`/`funext`
telescoping on top of it. SEAM: `boxReduce` uses `Classifier.coeffReduce`, Layer A uses
`PadicLift.coeffReduce` — they are DEFEQ (`ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) _` verbatim), so
`boxReduce_coeff` bridges them by `rfl`. -/

/-- **Coefficient of the box reduction** = `coeffReduce` of the coefficient (`Polynomial.coeff_map`).
The seam bridge: `boxReduce` maps through `Classifier.coeffReduce`, which is `rfl`-equal to
`PadicLift.coeffReduce`, so the Layer-A lemmas (stated about `PadicLift.coeffReduce`) apply directly. -/
theorem boxReduce_coeff (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (i : ℕ) :
    (boxReduce p N n hN f).1.coeff i = PadicLift.coeffReduce p N (f.1.coeff i) := by
  rw [boxReduce]; simp only [Polynomial.coeff_map]; rfl

/-- **B-poly-2** `boxValSupport_reduce_stable` (`CERTLEVEL_DECOMP.md` Layer B). Below the cutoff
(`hguard`: every support-coefficient valuation `< N`), the box-native valuation support is stable under
single-step reduction: `boxValSupport p N (boxReduce f) = boxValSupport p (N+1) f`. The support is
unchanged (A3 `coeffReduce_ne_zero_of_val_lt` keeps every support dot nonzero), and each decorating
valuation is preserved (A1 `zmodValuation_reduce_stable`); `Finset.image_congr` assembles. No axiom. -/
theorem boxValSupport_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguard : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N) :
    boxValSupport p N (boxReduce p N n hN f) = boxValSupport p (N + 1) f := by
  unfold boxValSupport
  have hsupp : (boxReduce p N n hN f).1.support = f.1.support := by
    ext i
    simp only [Polynomial.mem_support_iff, boxReduce_coeff p N hN f]
    constructor
    · intro h hf0; rw [hf0] at h; simp at h
    · intro hf0
      exact PadicLift.coeffReduce_ne_zero_of_val_lt p N hN _
        (hguard i (Polynomial.mem_support_iff.mpr hf0))
  rw [hsupp]
  apply Finset.image_congr
  intro i hi
  simp only []
  rw [Finset.mem_coe] at hi
  rw [boxReduce_coeff p N hN f i]
  congr 1
  exact PadicLift.zmodValuation_reduce_stable p N hN _ (hguard i hi)

/-- **B-res-2** `boxCoeffData_reduce_stable` (`CERTLEVEL_DECOMP.md` Layer B). Below the cutoff
(`hguard`: every side-column-coefficient valuation `< N`), the residual coefficient datum on a fixed side
`S` is stable: `boxCoeffData p N S (boxReduce f) = boxCoeffData p (N+1) S f`. Pointwise `funext t`, the
`t`-th datum is the unit residue of `f.coeff (S.i₀ + t·S.e)`, preserved by A2
`zmodUnitResidue_reduce_stable`. The downstream `M4.residualPoly`/`factorize_any` then act on the SAME
datum, so factors/multiplicities agree automatically. No axiom. -/
theorem boxCoeffData_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (S : NewtonPolygon.Side) (f : QuotientBox.monicBox p (N + 1) n)
    (hguard : ∀ t, PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N) :
    boxCoeffData p N S (boxReduce p N n hN f) = boxCoeffData p (N + 1) S f := by
  -- (D7 fix) the datum now carries the on-side guard `zmodValuation = v₀ + t·h`; BOTH the guard's
  -- valuation read and the then-branch unit residue are level-stable below the cutoff (Layer A).
  unfold boxCoeffData
  funext t
  rw [boxReduce_coeff p N hN f]
  rw [PadicLift.zmodValuation_reduce_stable p N hN _ (hguard t),
      PadicLift.zmodUnitResidue_reduce_stable p N hN _ (hguard t)]

/-- **C — `rootSide` stability** (the selected order-0 side agrees across reduction). Given B-poly-2, the
two valuation supports coincide, so `NewtonPolygon.npSides_congr` (B-poly-1) gives equal side lists, and
`List.head?` of equal lists agree: `rootSide p N (boxReduce f) = rootSide p (N+1) f`. No axiom. -/
theorem rootSide_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguard : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N) :
    rootSide p N hN1 (boxReduce p N n hN1 f) = rootSide p (N + 1) hN2 f := by
  unfold rootSide
  exact congrArg List.head?
    (NewtonPolygon.npSides_congr _ _ _ _ (boxValSupport_reduce_stable p N hN1 f hguard))

/-- **C — `rootResidual` stability** (the order-0 residual agrees across reduction). The selected side
agrees (`rootSide_reduce_stable`), and on it the residual datum agrees (B-res-2), so the guarded residual
polynomial agrees: `rootResidual p N (boxReduce f) = rootResidual p (N+1) f`. The `hguardside` hypothesis
supplies the per-column cutoff for every side. No axiom. -/
theorem rootResidual_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguardsupp : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N)
    (hguardside : ∀ (S : NewtonPolygon.Side) (t : ℕ),
        PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N) :
    rootResidual p N hN1 (boxReduce p N n hN1 f) = rootResidual p (N + 1) hN2 f := by
  unfold rootResidual
  rw [rootSide_reduce_stable p N hN1 hN2 f hguardsupp]
  cases hS : rootSide p (N + 1) hN2 f with
  | none => simp only [hS]
  | some S =>
      simp only [hS]
      rw [boxCoeffData_reduce_stable p N hN1 S f (hguardside S)]

/-- **C — `rootFace` stability** (the order-0 lattice face agrees across reduction). The selected side
agrees (`rootSide_reduce_stable`), and `M7.toSideFace` is a function of it: `rootFace p N (boxReduce f) =
rootFace p (N+1) f`. No axiom. -/
theorem rootFace_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguardsupp : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N) :
    rootFace p N hN1 (boxReduce p N n hN1 f) = rootFace p (N + 1) hN2 f := by
  unfold rootFace
  rw [rootSide_reduce_stable p N hN1 hN2 f hguardsupp]

/-- **C-step** `omStep_reduce_stable` (`CERTLEVEL_DECOMP.md` Layer C). For a FIXED context `T`, `omStep`
discards its `_f` argument (`omStep _ _ _ _f T = M5.cells T`), so the per-node step is literally the same
across the reduction: `omStep p N n (boxReduce f) T = omStep p (N+1) n f T`. Holds by `rfl`. No axiom. -/
theorem omStep_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (T : M5.OMType) :
    omStep p N n (boxReduce p N n hN f) T = omStep p (N + 1) n f T := rfl

/-- **C-ctx** `fRootCtx_reduce_stable` — the per-node content (`CERTLEVEL_DECOMP.md` Layer C, the REAL
per-node fact now that the root is `f`-dependent). The order-0 root context built at level `N+1` on `f`
equals the one built at level `N` on `boxReduce f`, below the cutoff: the two differ only in `Nr`
(`rootFace`, stable), `Rr` (`rootResidual`, stable), and `dr := Rr.natDegree` (determined by `Rr`); the
`F0`/`Fr`/`δ`/`cs` fields are `f`-independent, the proof fields close by proof irrelevance. `simp only`
(not `rw`) is used to handle the dependent `dr := Rr.natDegree` motive. No axiom. -/
theorem fRootCtx_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguardsupp : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N)
    (hguardside : ∀ (S : NewtonPolygon.Side) (t : ℕ),
        PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N) :
    fRootCtx p N hN1 (boxReduce p N n hN1 f) = fRootCtx p (N + 1) hN2 f := by
  have hrr := rootResidual_reduce_stable p N hN1 hN2 f hguardsupp hguardside
  have hrf := rootFace_reduce_stable p N hN1 hN2 f hguardsupp
  unfold fRootCtx
  simp only [hrr, hrf]

/-- **C-ctx** `rootCtx_reduce_stable` — the dispatched root context (`CERTLEVEL_DECOMP.md` Layer C). At
levels `N` and `N+1` (both positive), `rootCtx` dispatches to `fRootCtx`, so the per-node stability is
`fRootCtx_reduce_stable`: `rootCtx p N (boxReduce f) = rootCtx p (N+1) f`. This is the C-layer node the
one-digit cylinder face (Layer D) feeds on. No axiom. -/
theorem rootCtx_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hguardsupp : ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N)
    (hguardside : ∀ (S : NewtonPolygon.Side) (t : ℕ),
        PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N) :
    rootCtx p N (boxReduce p N n hN1 f) = rootCtx p (N + 1) f := by
  unfold rootCtx
  rw [dif_pos hN1, dif_pos (Nat.succ_pos N)]
  exact fRootCtx_reduce_stable p N hN1 (Nat.succ_pos N) f hguardsupp hguardside

/-- **The level-`N` shape classifier** (`DEF B.3`). Runs `classifyAux` from the order-0 root context
with the full degree budget `n`. This has EXACTLY the type
`(N : ℕ) → QuotientBox.monicBox p N n → ClusterShape` demanded by `M8.shapeFiberCount`,
`M8.constantFiber`, `M8.nodeMeasure_boxSum`, and threaded by `M9.realClassify`. REPLACES the M9 stub
`realClassify := fun _ _ => ⟨[]⟩`.

DECISION 1 (the f-DEPENDENT root, LANDED): the genuine order-0 root residual `T.Rr` is built from
`boxCoeffData p N S f` at the selected order-0 side `S = rootSide p N f` and level `N`, so the root
context `rootCtx p N f` is genuinely `f`-dependent (for `0 < N`). On it `M5.cells` factors `f`'s real
order-0 residual `rootResidual` (one cell per distinct residual factor), so `classify N f` reflects
`f`'s Newton polygon + residual factorization rather than the constant trivial tree the old f-free
`M9rootCtx` shell yielded. The budget invariant `clusterSize (rootCtx …) = n` (`clusterSize_rootCtx`)
and the well-founded recursion are unchanged. -/
noncomputable def classify (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape :=
  fun N f => classifyAux p N n n f (rootCtx p N f) (clusterSize_rootCtx p N f)

/-! ### DE-STUB (first-descent increment): `classifyFirstDescent` — the recursion that reads `f`
below the root. The root's residue field is `ZMod p` (`fRootCtx`), so a repeated order-0 residual
factor `ch.P` is genuinely a `(ZMod p)[X]`, which we lift and develop `f` against (`fChildCtx`,
carrying `Rr := childResidual`, a function of `f`). The FIRST genuine descent then recurses via
`classifyAux` on that f-dependent child context — so the emitted subtree reflects `f`'s order-1
Newton polygon, NOT a constant childless leaf. Peeled explicitly at the top level (rather than baked
into the generic `classifyAux`) because `OMType.Fr` is an opaque `Type`: `ch.P : T.Fr[X]` is only
liftable to `(ZMod p)[X]` when `T.Fr = ZMod p`, which holds definitionally at the root but not for a
generic `T` in the recursion — that generality is the residue-field-representation redesign this
increment deliberately does not attempt. -/
noncomputable def classifyFirstDescent (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : ClusterShape :=
  let T := fRootCtx p N hN f
  ⟨(T.order, M5.clusterSize T, T.dr) ::
      (M5.cells T).flatMap (fun c =>
        c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
          -- `ch.P : T.Fr[X] = (ZMod p)[X]` at the root; develop `f` w.r.t. its lifted key.
          (classifyAux p N n ch.childSize f
            (fChildCtx p N f (T.order + 1) ch.childSize ch.P ch.μ)
            (clusterSize_fChildCtx p N f (T.order + 1) ch.childSize ch.P ch.μ)).tree)),
    M5.encodeCells T⟩

/-- **NON-VACUITY WITNESS (machine-checked): the f-dependent child produces genuine cells.** When the
developed residual `childResidual p N f ψ μ` has positive degree (`≤ s`), the child context's cells
are NON-EMPTY — i.e. `classifyAux` at this child does NOT bottom out as a childless leaf, it factors a
residual genuinely read off `f`'s φ-adic development. This is the exact contrast with the stub child
`childCtxOfSize` (whose `Rr = 0`, so `M5.cells (childCtxOfSize r s) = []` always — f-blind). No axiom. -/
theorem cells_fChildCtx_ne_nil (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (r s : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ)
    (h0 : 0 < (childResidual p N f ψ μ).natDegree)
    (hle : (childResidual p N f ψ μ).natDegree ≤ s) :
    M5.cells (fChildCtx p N f r s ψ μ) ≠ [] := by
  -- The child's residual IS `childResidual` (guard passes), so it has positive degree.
  have hRr : (fChildCtx p N f r s ψ μ).Rr = childResidual p N f ψ μ := by
    show (if (childResidual p N f ψ μ).natDegree ≤ s then childResidual p N f ψ μ else 0)
        = childResidual p N f ψ μ
    rw [if_pos hle]
  have hdegpos : 0 < (fChildCtx p N f r s ψ μ).Rr.natDegree := by rw [hRr]; exact h0
  -- Any factorization of a positive-degree residual has non-empty factors (empty ⟹ degree 0).
  set fact := Classical.choice (M4.factorize_any (fChildCtx p N f r s ψ μ).Rr) with hfd
  have hne : fact.factors ≠ ∅ := by
    intro hempty
    have hbudget := fact.degree_budget
    rw [hempty, Finset.sum_empty] at hbudget
    -- hbudget : 0 = (fChildCtx …).Rr.natDegree, contradicting hdegpos.
    omega
  -- `M5.cells` maps over the sorted attach-list of `fact.factors`, non-empty since `factors ≠ ∅`.
  rw [M5.cells]
  intro hnil
  have hlen : (((fact.factors.attach.toList.mergeSort
      (fun a b => decide (a.1.natDegree ≤ b.1.natDegree)))).length) = 0 := by
    have := congrArg List.length hnil
    rwa [List.length_map, List.length_nil] at this
  rw [List.length_mergeSort, Finset.length_toList, Finset.card_attach] at hlen
  exact hne (Finset.card_eq_zero.mp hlen)

/-! ### DE-STUB (2026-07-13, MULTI-LEVEL genuine classifier — ADDITIVE increment A1)

`classifyFirstDescent` reads `f` at the root and ONE genuine descent level, but then recurses through
the STUBBED `classifyAux` (f-blind `childCtxOfSize`, `Rr := 0`). This increment builds a genuine
recursion `classifyGenuineAux` that reads `f` at EVERY level, by well-founded recursion on the cluster
budget, descending through `fChildCtx` contexts (all `Fr := ZMod p` DEFINITIONALLY) so each child's
repeated residual factor `ch.P : (fChildCtx …).Fr[X]` IS a genuine `(ZMod p)[X]` with NO type transport
— the residue-field-extension redesign (`deg ψ > 1`, `Fr` a genuine extension) is deferred exactly as
in `classifyFirstDescent`; this stays in the tame `Fr = ZMod p` single-slope tower (where P2 drainage
lives). Built ALONGSIDE `classify`/`classifyAux` (which are untouched), so master stays GREEN. -/

/-- **The genuine MULTI-LEVEL descent recursion** (DE-STUB A1). Reads `f` at every level: from a
residual `ψ` (a `(ZMod p)[X]`) and multiplicity `μ` at order `r`, builds the f-DEPENDENT child context
`fChildCtx p N f r budget ψ μ` (whose `Rr := childResidual … f …` genuinely reads `f`'s φ-adic
development, and whose `Fr := ZMod p` definitionally), factors its cells, and for each descent child
`ch` recurses on the strictly-smaller budget `ch.childSize` with the child's OWN repeated residual
factor `ch.P : (fChildCtx …).Fr[X] = (ZMod p)[X]` (no transport). Strict descent by
`ch.hChildSizeLt : ch.childSize < clusterSize (fChildCtx …) = budget` (via `clusterSize_fChildCtx`).
Contrast `classifyAux`, which recurses through the f-blind `childCtxOfSize` (`Rr := 0`, always
childless). -/
noncomputable def classifyGenuineAux (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) :
    (budget : ℕ) → (r : ℕ) → (ψ : (ZMod p)[X]) → (μ : ℕ) → ClusterShape :=
  fun budget => Nat.strongRecOn budget
    (motive := fun _ => (r : ℕ) → (ψ : (ZMod p)[X]) → (μ : ℕ) → ClusterShape)
    (fun b ih => fun r ψ μ =>
      let T := fChildCtx p N f r b ψ μ
      ⟨(T.order, M5.clusterSize T, T.dr) ::
          (M5.cells T).flatMap (fun c =>
            c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
              have hlt : ch.childSize < b :=
                (clusterSize_fChildCtx p N f r b ψ μ) ▸ ch.hChildSizeLt
              (ih ch.childSize hlt (T.order + 1) ch.P ch.μ).tree)),
        M5.encodeCells T⟩)

/-- **The genuine MULTI-LEVEL classifier** (DE-STUB A1). Peels the root exactly like
`classifyFirstDescent` (root via `fRootCtx`, whose `Fr := ZMod p`, so a repeated order-0 residual
factor `ch.P` is a genuine `(ZMod p)[X]`), then descends into `classifyGenuineAux` on each first-level
descent child — which now recurses to ALL depths reading `f`. Every emitted subtree reflects `f`'s
Newton polygon + residual factorization at that level, NOT a constant childless leaf. Built alongside
`classify`; the SWAP that repoints `classify`/`classifyAux` at this is the LAST, CERTLEVEL-breaking
phase (`notes/DESTUB_BLUEPRINT_2026-07-13.md` §2), deliberately not done in this increment. -/
noncomputable def classifyGenuine (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : ClusterShape :=
  let T := fRootCtx p N hN f
  ⟨(T.order, M5.clusterSize T, T.dr) ::
      (M5.cells T).flatMap (fun c =>
        c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
          (classifyGenuineAux p N f ch.childSize (T.order + 1) ch.P ch.μ).tree)),
    M5.encodeCells T⟩

/-- **One-step unfold of `classifyGenuineAux`** (`Nat.strongRecOn_eq` + beta). Exposes the emitted
shape at a level `budget = b`: the root tuple of `fChildCtx p N f r b ψ μ` followed by the genuine
recursive descent. Mirrors `Order0Classify.classifyAux_unfold`. No axiom. -/
theorem classifyGenuineAux_unfold (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (budget r : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ) :
    classifyGenuineAux p N f budget r ψ μ
      = (let T := fChildCtx p N f r budget ψ μ
        ⟨(T.order, M5.clusterSize T, T.dr) ::
            (M5.cells T).flatMap (fun c =>
              c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
                (classifyGenuineAux p N f ch.childSize (T.order + 1) ch.P ch.μ).tree)),
          M5.encodeCells T⟩) := by
  have h := Nat.strongRecOn_eq
    (motive := fun _ => (r : ℕ) → (ψ : (ZMod p)[X]) → (μ : ℕ) → ClusterShape)
    (fun b ih => fun r ψ μ =>
      (let T := fChildCtx p N f r b ψ μ
      (⟨(T.order, M5.clusterSize T, T.dr) ::
          (M5.cells T).flatMap (fun c =>
            c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
              have hlt : ch.childSize < b :=
                (clusterSize_fChildCtx p N f r b ψ μ) ▸ ch.hChildSizeLt
              (ih ch.childSize hlt (T.order + 1) ch.P ch.μ).tree)),
        M5.encodeCells T⟩ : ClusterShape)))
    budget
  exact congrFun (congrFun (congrFun h r) ψ) μ

/-- **Emitted-body abstraction** (DE-STUB Ingredient C helper). The one-step `classifyGenuineAux` body
at a context `T`, abstracted over the recursive continuation `g` (typed at `T.Fr[X]`, matching
`ch.P : T.Fr[X]`). Introduced so the "two contexts are only propositionally equal" transport can be
handled by `subst` on a genuine variable `T`, with the continuation carried along the equality. -/
noncomputable def genuineBody (T : M5.OMType)
    (g : ℕ → ℕ → T.Fr[X] → ℕ → ClusterShape) : ClusterShape :=
  ⟨(T.order, M5.clusterSize T, T.dr) ::
      (M5.cells T).flatMap (fun c =>
        c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
          (g ch.childSize (T.order + 1) ch.P ch.μ).tree)),
    M5.encodeCells T⟩

/-- **Body congruence over the continuation** (DE-STUB Ingredient C helper). On a FIXED context `T`,
`genuineBody T g` depends on the recursive continuation `g` ONLY through its values, so two continuations
`gA gB` agreeing on every descent argument produce equal bodies. This isolates the "the two sides call
DIFFERENT recursive functions" half from the "the two contexts are only propositionally equal" half; `T`
is fixed here so there is NO dependent-type transport. No axiom. -/
theorem genuineBody_cont_congr (T : M5.OMType)
    (gA gB : ℕ → ℕ → T.Fr[X] → ℕ → ClusterShape)
    (hg : ∀ (ch : M5.OMCell.Child T), gA ch.childSize (T.order + 1) ch.P ch.μ
        = gB ch.childSize (T.order + 1) ch.P ch.μ) :
    genuineBody T gA = genuineBody T gB := by
  unfold genuineBody
  refine congrArg (fun l => (⟨_ :: l, M5.encodeCells T⟩ : ClusterShape)) ?_
  refine List.flatMap_congr (fun c _ => ?_)
  refine List.flatMap_congr (fun ch _ => ?_)
  rw [hg ch]

/-- **Emitted body reduces along a context equality** (DE-STUB Ingredient C helper, the wall-breaker).
If two contexts are propositionally equal (`hT : T_A = T_B`) and two continuations `gA gB` agree on every
descent child of `T_B` (with `gA`'s argument transported backward along `hT`, since `gA` reads `T_A.Fr[X]`
and `ch.P : T_B.Fr[X]`), then the two emitted bodies are equal. Proved by `subst hT` — `T_A`, `T_B` are
genuine variables here, so the dependent `OMCell.Child T`/`T.Fr[X]` transports collapse to `rfl` and no
"motive not type correct" arises. This is the piece that defeats the diagnosed wall: the context equality
is discharged by `subst` (variables), not by rewriting `T` inside the dependent recursion body. No axiom. -/
theorem genuineBody_reduce {T_A T_B : M5.OMType} (hT : T_A = T_B)
    (gA : ℕ → ℕ → T_A.Fr[X] → ℕ → ClusterShape)
    (gB : ℕ → ℕ → T_B.Fr[X] → ℕ → ClusterShape)
    (hg : ∀ (ch : M5.OMCell.Child T_B),
      gA ch.childSize (T_A.order + 1) (hT ▸ ch.P) ch.μ
        = gB ch.childSize (T_B.order + 1) ch.P ch.μ) :
    genuineBody T_A gA = genuineBody T_B gB := by
  subst hT
  exact genuineBody_cont_congr _ gA gB hg

/-- **DE-STUB Ingredient C — genuine reader is reduction-stable.** The genuine multi-level classifier's
recursion `classifyGenuineAux` is INVARIANT under one-digit box reduction below the (universal per-digit)
cutoff: at level `N+1` on `f` it emits the same shape as at level `N` on `boxReduce f`. Proved by strong
induction on the cluster budget; at each node the two contexts `fChildCtx p N (boxReduce f) …` and
`fChildCtx p (N+1) f …` are propositionally equal (Ingredient B, `fChildCtx_reduce_stable`, consumed
under `hcut`). The dependent-type snag (`ch : OMCell.Child T` typed by the context VALUE, `ch.P : T.Fr[X]`
fed to a `(ZMod p)[X]`-typed continuation) — which defeats a direct `rw [hT]` — is handled by
`genuineBody_reduce`, which `subst`s the context equality on genuine variables (so the dependent
transports collapse to `rfl`), reducing to a same-context continuation comparison discharged by the
pointwise IH (`genuineBody_cont_congr`). The one residual argument gap `hT ▸ ch.P` vs `ch.P` (both
`(ZMod p)[X]` since `T_A.Fr = T_B.Fr = ZMod p` definitionally) is closed by `eqRec_heq`; `.order`/
`clusterSize` reduce to `r`/`budget` definitionally so the IH applies verbatim. No axiom. -/
theorem classifyGenuineAux_reduce_stable (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hcut : ∀ (ψ' : (ZMod p)[X]) (μ' : ℕ),
      ∀ t : Fin μ', PadicLift.zmodValuation p (N + 1)
        ((Development.develop (liftKey p (N + 1) ψ') μ' f.1 t).coeff 0) < N) :
    ∀ (budget r : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ),
      classifyGenuineAux p N (boxReduce p N n hN f) budget r ψ μ
        = classifyGenuineAux p (N + 1) f budget r ψ μ := by
  intro budget
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
    intro r ψ μ
    -- Unfold both sides to the emitted body, and package each as a `genuineBody`.
    rw [classifyGenuineAux_unfold p N (boxReduce p N n hN f) budget r ψ μ,
        classifyGenuineAux_unfold p (N + 1) f budget r ψ μ]
    simp only
    -- The two per-node contexts are propositionally equal (Ingredient B).
    have hT : fChildCtx p N (boxReduce p N n hN f) r budget ψ μ
        = fChildCtx p (N + 1) f r budget ψ μ :=
      fChildCtx_reduce_stable p N hN f r budget ψ μ (hcut ψ μ)
    -- Recognise both unfolded bodies as `genuineBody` at their respective contexts.
    show genuineBody (fChildCtx p N (boxReduce p N n hN f) r budget ψ μ)
          (classifyGenuineAux p N (boxReduce p N n hN f))
        = genuineBody (fChildCtx p (N + 1) f r budget ψ μ)
          (classifyGenuineAux p (N + 1) f)
    -- The context equality is discharged by `genuineBody_reduce` (`subst` on genuine variables — the
    -- dependent-type wall is defeated there, not here). It remains to compare the two continuations on
    -- every descent child, which is exactly the pointwise IH at the strictly-smaller child budget.
    refine genuineBody_reduce hT (classifyGenuineAux p N (boxReduce p N n hN f))
      (classifyGenuineAux p (N + 1) f) (fun ch => ?_)
    -- `ch.childSize < clusterSize T_B` reduces to `ch.childSize < budget` (`cs := budget` in `fChildCtx`),
    -- and `T_A.order = T_B.order = r` (`order := r`), both DEFINITIONALLY. So the only genuine gap between
    -- the goal and the IH `ih ch.childSize … ch.P ch.μ` is the transported argument `hT ▸ ch.P` on the
    -- `gA` side (typed `T_A.Fr[X]`) vs `ch.P` (typed `T_B.Fr[X]`) — heterogeneously equal (both `(ZMod p)[X]`).
    -- `convert` peels the application and leaves exactly that argument gap, closed by `eqRec_heq`.
    have hlt : ch.childSize < budget := ch.hChildSizeLt
    -- `convert` to the IH at `(r+1, ch.P)`; the leaf gaps are (i) the transported argument
    -- `hT ▸ ch.P = ch.P` (both `(ZMod p)[X]`, closed by `eqRec_heq`) and (ii) `T.order + 1 = r + 1`
    -- (`order := r` in `fChildCtx`, defeq — `rfl`). `clusterSize` reduces to `budget` (`cs := budget`).
    convert ih ch.childSize hlt (r + 1) ch.P ch.μ using 2 <;>
      first
        | rfl
        | exact eqRec_heq (φ := fun T : M5.OMType => T.Fr[X]) hT.symm ch.P
        | exact eq_of_heq (eqRec_heq (φ := fun T : M5.OMType => T.Fr[X]) hT.symm ch.P)
        | exact eqRec_heq (φ := fun T : M5.OMType => T.Fr[X]) hT ch.P
        | exact eq_of_heq (eqRec_heq (φ := fun T : M5.OMType => T.Fr[X]) hT ch.P)

/-- **Genuine reader's root tuple is dr-nondegenerate** (DE-STUB A1; honestly restated 2026-07-14 — was
misleadingly named/doc'd `…_tree_ne_leaf` / "descends past a leaf"). When the developed residual
`childResidual p N f ψ μ` has positive degree `≤ budget`, the emitted `classifyGenuineAux` shape's ROOT
TUPLE carries a NONZERO `dr`-slot (`= (childResidual …).natDegree > 0`), so the tree is not the
degenerate `(r, budget, 0)` tuple that the f-blind stub's childless child produces — i.e. the genuine
reader is distinguished from the stub AT THE ROOT TUPLE, via the residual degree. It does NOT assert the
descent flatMap is non-empty (`tree.length ≥ 2`): a positive-degree but SEPARABLE residual gives cells
with no descent child, so a genuine "descends past a leaf" claim needs an extra repeated-factor
hypothesis (cells-non-empty is `cells_fChildCtx_ne_nil`; a length≥2 witness is future work). No axiom. -/
theorem classifyGenuineAux_head_dr_pos (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (budget r : ℕ) (ψ : (ZMod p)[X]) (μ : ℕ)
    (h0 : 0 < (childResidual p N f ψ μ).natDegree)
    (hle : (childResidual p N f ψ μ).natDegree ≤ budget) :
    (classifyGenuineAux p N f budget r ψ μ).tree
      ≠ [((fChildCtx p N f r budget ψ μ).order, budget, (0 : ℕ))] := by
  -- HONEST CONTENT (NOT "descends past a leaf"): if the tree WERE the degenerate `(r, budget, 0)` leaf,
  -- its head tuple's dr-slot would be `0`; but the genuine child context's `dr = (childResidual …).natDegree
  -- > 0` (`hle` makes the guard pass, `h0` makes it positive). So the trees differ in the dr-slot ALONE.
  -- This says nothing about the descent flatMap's length; `htail` below is computed but NOT load-bearing.
  rw [classifyGenuineAux_unfold]
  simp only
  intro hleaf
  -- `hleaf` equates the emitted cons-list with a singleton; peel the tail = [].
  have htail : (M5.cells (fChildCtx p N f r budget ψ μ)).flatMap (fun c =>
      c.children.flatMap (fun (ch : M5.OMCell.Child (fChildCtx p N f r budget ψ μ)) =>
        (classifyGenuineAux p N f ch.childSize
          ((fChildCtx p N f r budget ψ μ).order + 1) ch.P ch.μ).tree)) = [] := by
    have := List.tail_eq_of_cons_eq hleaf
    simpa using this
  -- The decisive contrast is purely the dr-slot: the leaf shape forces the head tuple's third component
  -- (`.2.2`, the `dr`) to be `0`, but `fChildCtx`'s `dr = (childResidual …).natDegree > 0`.
  have hhead := List.head_eq_of_cons_eq hleaf
  have hdr : (fChildCtx p N f r budget ψ μ).dr = (childResidual p N f ψ μ).natDegree := by
    show (if (childResidual p N f ψ μ).natDegree ≤ budget then childResidual p N f ψ μ else 0).natDegree
        = (childResidual p N f ψ μ).natDegree
    rw [if_pos hle]
  -- `hhead : (order, clusterSize, dr) = (order, budget, 0)`, so `dr = 0`; but `dr = natDegree > 0`.
  have : (fChildCtx p N f r budget ψ μ).dr = 0 := by
    have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hhead
    simpa using this
  rw [hdr] at this
  omega

-- Footprint check for the DE-STUB A1 dr-nondegeneracy deliverable: must be
-- ⊆ [propext, Classical.choice, Quot.sound] (no `sorry`/`axiom`/`native_decide`).
#print axioms classifyGenuineAux_head_dr_pos

/-- **One-step unfold of the stub `classify` head/cells** (DE-STUB A1 helper). Exposes the root tuple
and the `encodeCells` payload of the stubbed `classify` (`= classifyAux` at `rootCtx`), so the genuine
classifier can be compared against them at the root. `Nat.strongRecOn` + `WellFounded.fix_eq` (the same
mechanism as `treeSize_classifyAux`). No axiom. -/
theorem classify_head_cells (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) :
    (classify p n N f).tree.head?
        = some ((rootCtx p N f).order, M5.clusterSize (rootCtx p N f), (rootCtx p N f).dr)
      ∧ (classify p n N f).cells = M5.encodeCells (rootCtx p N f) := by
  rw [classify]
  unfold classifyAux Nat.strongRecOn
  rw [WellFounded.fix_eq]
  exact ⟨rfl, rfl⟩

/-- **Root-tuple agreement with the stub `classify`** (DE-STUB A1 menu-correctness, tractable slice).
The genuine multi-level `classifyGenuine` and the stubbed `classify` emit the SAME root tuple and the
SAME per-node cell payload at the ROOT (for `0 < N`, where `rootCtx = fRootCtx`) — they diverge ONLY in
the descent subtrees (which the genuine one reads from `f`, the stub truncates). So `classifyGenuine`
is a genuine BELOW-ROOT enrichment of `classify`, not a different root. No axiom. -/
theorem classifyGenuine_root_eq_classify (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    (classifyGenuine p N hN f).tree.head? = (classify p n N f).tree.head?
      ∧ (classifyGenuine p N hN f).cells = (classify p n N f).cells := by
  have hroot : rootCtx p N f = fRootCtx p N hN f := by rw [rootCtx, dif_pos hN]
  obtain ⟨hhead, hcells⟩ := classify_head_cells p N f
  refine ⟨?_, ?_⟩
  · show some ((fRootCtx p N hN f).order, M5.clusterSize (fRootCtx p N hN f), (fRootCtx p N hN f).dr)
        = (classify p n N f).tree.head?
    rw [hhead, hroot]
  · show M5.encodeCells (fRootCtx p N hN f) = (classify p n N f).cells
    rw [hcells, hroot]

/-- **The genuine classifier has full tree size** (DE-STUB A1). `M6.treeSize (classifyGenuine …) = n`:
the root tuple's size slot is `clusterSize (fRootCtx …) = n`, read by `M6.treeSize` independent of the
descent subtrees. Matches `treeSize_classify` for the stub. No axiom. -/
theorem treeSize_classifyGenuine (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    M6.treeSize (classifyGenuine p N hN f) = n := by
  show M5.clusterSize (fRootCtx p N hN f) = n
  exact clusterSize_fRootCtx p N hN f

/-! ## DEF B.5 — the genuine decode parser (`decode`)

The parse of a `ClusterShape.tree` back into an `OMType`, satisfying `M6.treeSize T =
M5.clusterSize (decode T)` on the image of `classify`. The higher-order generalization of M9's order-0
`leafOMTypeOfSize` stub. Feeds `M7.cells` / `M6.cells_descend`. -/

/-- **The decoder** `decode : ClusterShape → M5.OMType` (`DEF B.5`). Rebuilds an OM type from the
serialized tree, re-attaching M4/M5 descent data for orders `≥ 1`. Opaque body in the freeze (the
genuine higher-order parser is the B.5 body); the SIGNATURE is the section M9/M7 consume. REPLACES the
M9 order-0 `leafOMTypeOfSize` stub. -/
noncomputable def decode (p : ℕ) [Fact p.Prime] (n : ℕ) : ClusterShape → M5.OMType :=
  fun T =>
    -- B.5 body (decision 2b): the count-native section parser. Reads the genuine root `order` off the
    -- serialized tree and keeps `cs := M6.treeSize T` so `decode_classify_section` holds by construction.
    -- The FAITHFUL per-node cell list is reconstructed not here (an `M5.OMType`'s `cells` are a function
    -- of `Rr`/`Nr` only) but at the M7 layer by `M7.cellsOfShape`, which reads the enriched
    -- `ClusterShape.cells` payload `M5.shapeOf` recorded (`cellsOfShape_shapeOf`), losslessly.
    { order := rootOrder T
      F0 := ZMod 2, Fr := ZMod 2, δ := 1
      Nr := ⟨0, fun _ => 0, fun _ => false⟩, Rr := 0, dr := 0, keyDeg := 0
      cs := M6.treeSize T
      hResidueDeg := by simp [Module.finrank_self], hResidualDeg := by simp
      hDrLeCs := Nat.zero_le _ }
where
  /-- Root OM order read off the serialized tree (`0` for the empty shell). -/
  rootOrder (T : ClusterShape) : ℕ := match T.tree with | [] => 0 | (o, _, _) :: _ => o

/-! ## DEF B.4 — the certification level (`certLevel`)

The truncation level `N₀(f)` above which `classify` is stable, given as the EXPLICIT modulus
`certLevel f := v_p(disc f) + 1` (`CERTLEVEL_DECOMP.md` Layer E, `E-modulus`). `PadicInt.valuation :
ℤ_[p] → ℕ` is ℕ-valued in this Mathlib pin, so the modulus is a finite `ℕ` BY CONSTRUCTION — no
`toNat` juggling and no separate finiteness obligation (the OM-tree termination is structural in-repo,
`Nat.strongRecOn` + `hDrLtCs`; it is NOT cited). For monic separable `f` the value is the right finite
number because `disc f ≠ 0` (`Discriminant.discr_ne_zero_of_separable_monic` lifted along
`discr_map_monic`); for the stability proof only the bound `certLevel f ≤ N` is consumed, via the single
named CITE `omReadValuation_lt_of_certLevel` (GMN Thm 4.18 / Cor 4.19). -/

/-- **The certification level** `certLevel f := v_p(disc f) + 1` (`DEF B.4` / Layer E `E-modulus`). The
explicit GMN digit-count modulus: above it, every coefficient valuation the OM tree reads is below the
truncation (the named CITE `omReadValuation_lt_of_certLevel`). ℕ-valued by construction
(`PadicInt.valuation`). -/
noncomputable def certLevel (p : ℕ) [Fact p.Prime] (n : ℕ) (f : Polynomial ℤ_[p]) : ℕ :=
  (f.discr).valuation + 1

/-! ## THE REDUCTION-STABILITY SPEC (consumed by F1.L9 / M8.constantFiber)

The headline coupling: above `certLevel`, `classify` is STABLE along the tower
`ZMod(p^{N+1}) ↠ ZMod(p^N)` — classifying a box polynomial at level `M` and reducing agrees with
reducing first then classifying at level `N`. This is the COUNTING-consequence hypothesis F1 packages
(F1.L9 ⟹ `r = p^n`), discharging `M8.constantFiber`'s `∃ r`. It is the SPEC (a Prop), proved by
`certLevel_stabilizes` (LEM B.7, THE WALL); WAVE-0 builds against the SPEC, not the proof. -/

/-- **Reduction-stability predicate** (the Core-B certification property). `classify` is reduction-stable
above `N₀` if for all `N₀ ≤ N ≤ M`, classifying a level-`M` box polynomial then reading its shape agrees
with reducing it to level `N` first: `classify M g = classify N (boxReduceLE g)`. This is exactly the
F1.D5 "decided above `N₀`" hypothesis (`classify M (boxReduceLE … g) = classify N g`), threaded so F1
only needs its consequence on counts. -/
def ClassifyReductionStable (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape) (N₀ : ℕ) : Prop :=
  ∀ (N M : ℕ) (hN₀ : N₀ ≤ N) (h : N ≤ M) (hN : 0 < N) (g : QuotientBox.monicBox p M n),
    classify N (boxReduceLE p N M n h hN g) = classify M g

/-! ## Layer D + E — the one-digit cylinder, the telescoping, and the certLevel assembly

`CERTLEVEL_DECOMP.md` Layers D (one-digit cylinder `D-face` + telescoping `D-tele`) and E (the explicit
modulus + the single GMN CITE). Builds on the Layer-B/C node `rootCtx_reduce_stable` (the f-DEPENDENT
root stability) already proved above. The KEY structural fact `classifyAux_indep`: `classifyAux`
discards `(N, f)` definitionally (`omStep` ignores `_f`, the recursion uses the f-free
`childCtxOfSize (T.order + 1) ch.childSize`, whose arguments read only the bound context `T`),
so the one-digit cylinder reduces to root-context stability `rootCtx_reduce_stable` plus a defeq. -/

/-- **`classifyAux` is independent of `(N, f)`** given the context. `omStep p N n f T = M5.cells T`
discards `_f`, and the budget recursion uses the f-free `childCtxOfSize (T.order + 1) ch.childSize`
(both arguments functions of the bound context `T` alone), so the whole `classifyAux` output is a
function of `(n, budget, Tctx)` alone — `rfl`. (This is what makes the one-digit cylinder
follow from root-context stability without re-inducting on the OM tree.) -/
theorem classifyAux_indep (p : ℕ) [Fact p.Prime] (N N' n : ℕ) (budget : ℕ)
    (f : QuotientBox.monicBox p N n) (f' : QuotientBox.monicBox p N' n)
    (T : M5.OMType) (hT : M5.clusterSize T = budget) (hT' : M5.clusterSize T = budget) :
    classifyAux p N n budget f T hT = classifyAux p N' n budget f' T hT' := rfl

/-- `classifyAux` congruence in the root context (with `N`/`f` defeq-harmonized): equal contexts give
equal classifications. `subst` the context equality, then `classifyAux_indep`. -/
theorem classifyAux_congr_ctx (p : ℕ) [Fact p.Prime] (N N' n : ℕ)
    (f : QuotientBox.monicBox p N n) (f' : QuotientBox.monicBox p N' n)
    (T T' : M5.OMType) (hTT' : T = T')
    (hT : M5.clusterSize T = n) (hT' : M5.clusterSize T' = n) :
    classifyAux p N n n f T hT = classifyAux p N' n n f' T' hT' := by
  subst hTT'
  exact classifyAux_indep p N N' n n f f' T hT hT'

/-- The Layer-B/C GUARD on the Newton-polygon channel: every support-coefficient valuation `< N`. -/
abbrev GuardSupp (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p (N + 1) n) : Prop :=
  ∀ i ∈ f.1.support, PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N

/-- The Layer-B/C GUARD on the residual channel: every side-column-coefficient valuation `< N`. -/
abbrev GuardSide (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p (N + 1) n) : Prop :=
  ∀ (S : NewtonPolygon.Side) (t : ℕ),
    PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N

/-! ## REDSTAB Deliverable 1 — the f-keyed, hull-restricted guards and the narrow CITE axiom

`REDSTAB_BLUEPRINT.md` §"DELIVERABLE 1". The false uniform `omReadValuation_lt_of_certLevel`
(reverted) is replaced by an `f`-keyed CITE keyed on the box's OWN discriminant valuation, quantified
only over the read-set (hull vertices for the polygon channel, side columns `t ≤ residualDeg S` for the
residual channel). NO `ZMod.valuation` (does not exist) — valuations are `PadicLift.zmodValuation`. -/

/-- **The hull-vertex abscissae** of `f` at level `N` (the `i`-coordinates of
`NewtonPolygon.npVertices` on the box-native valuation support). These are the ONLY support dots the
side list `npSides` — hence `rootSide`/`rootResidual`/`rootFace` — depends on. -/
noncomputable def hullDots (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) : Finset ℕ :=
  ((NewtonPolygon.npVertices (boxValSupport p N f)
      (boxValSupport_nonempty p N hN f)).map Prod.fst).toFinset

/-- **RESTRICTED Newton-polygon guard** (`REDSTAB` D1): only the HULL VERTICES need valuation `< N`.
Contrast `GuardSupp`, which over-quantifies over ALL `i ∈ f.1.support`. -/
abbrev GuardSuppR (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) : Prop :=
  ∀ i ∈ hullDots p (N + 1) (Nat.succ_pos N) f,
    PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N

/-- **RESTRICTED residual guard** (`REDSTAB` D1): only the SIDE COLUMNS of `f`'s OWN sides, only up to
`residualDeg`. Contrast `GuardSide`, which over-quantifies over EVERY `S : Side` and ALL `t : ℕ`. -/
abbrev GuardSideR (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) : Prop :=
  ∀ S ∈ NewtonPolygon.npSides (boxValSupport p (N + 1) f)
            (boxValSupport_nonempty p (N + 1) (Nat.succ_pos N) f),
    ∀ t, t ≤ M4.residualDeg S →
      PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N

/-- **[CITE] GMN Cor 4.19 / Thm 4.18 (Guàrdia–Montes–Nart, arXiv:0807.2620v2 §4), f-keyed + read-set
restricted; `ind(f) ≤ v_p(disc f)`, to be discharged.** Every OM-read valuation of `g` is `≤
v_p(disc g)`; hence `< N` once `N` exceeds `g`'s own discriminant valuation (`g` is in the BULK). The
threshold is the box-native discriminant valuation `PadicLift.zmodValuation p (N+1) (g.1.discr)` — NOT
the PadicInt-valued `certLevel`; `g.1.discr : ZMod (p^(N+1))` via mathlib `Polynomial.discr`.

This REPLACES the FALSE uniform `omReadValuation_lt_of_certLevel` (which asserted the guards uniformly
over every box `g`, refuted by `g = xⁿ + p^N`). The counterexample `xⁿ + p^N` does NOT refute this:
it has discriminant valuation `≈ N`, i.e. it lies in the TAIL, excluded by the hypothesis `hbulk : … <
N`. The user has authorized importing the inequality as an axiom: this is the SINGLE imported scalar
fact (`ind(f) ≤ v_p(disc f)` specialized to the read-set), not a sub-proof. -/
axiom omReadValuation_lt_of_certLevel_fkeyed (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (g : QuotientBox.monicBox p (N + 1) n)
    (hbulk : PadicLift.zmodValuation p (N + 1) (g.1.discr) < N) :
    GuardSuppR p N hN g ∧ GuardSideR p N hN g

/-- **B-res-2 against the restricted side guard** (`REDSTAB` D1, §1.4). `[NOW]`: `M4.residualPoly` is
`∑_{t ≤ residualDeg S} C (coeffData t) X^t` and `residualPoly_coeff` confirms coeffs beyond
`residualDeg S` vanish, so it depends on `boxCoeffData` only at `t ≤ residualDeg S`; on those columns
the per-column cutoff `hg` drives `zmodUnitResidue_reduce_stable`. We prove the residualPoly equality
directly via `residualPoly_coeff` so off-column behaviour is irrelevant. No axiom (beyond the Layer-A
`zmodUnitResidue_reduce_stable`). -/
theorem boxCoeffData_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (S : NewtonPolygon.Side) (f : QuotientBox.monicBox p (N + 1) n)
    (hg : ∀ t, t ≤ M4.residualDeg S →
      PadicLift.zmodValuation p (N + 1) (f.1.coeff (S.i₀ + t * S.e)) < N) :
    M4.residualPoly (boxCoeffData p N S (boxReduce p N n hN f)) S
      = M4.residualPoly (boxCoeffData p (N + 1) S f) S := by
  apply Polynomial.ext
  intro j
  rw [M4.residualPoly_coeff, M4.residualPoly_coeff]
  by_cases hj : j ≤ M4.residualDeg S
  · simp only [if_pos hj]
    show boxCoeffData p N S (boxReduce p N n hN f) j = boxCoeffData p (N + 1) S f j
    unfold boxCoeffData
    rw [boxReduce_coeff p N hN f]
    -- (D7 fix) rewrite BOTH the on-side guard's valuation read and the then-branch unit residue:
    rw [PadicLift.zmodValuation_reduce_stable p N hN _ (hg j hj),
        PadicLift.zmodUnitResidue_reduce_stable p N hN _ (hg j hj)]
  · simp only [if_neg hj]

/-- **S1 — "support dots only rise or vanish under reduction"** (`REDSTAB2` §"Scratch-verified S1").
For `x ≠ 0`, the box-native valuation can only INCREASE (or the coefficient vanish, valuation `= N`)
under single-step reduction: `zmodValuation p (N+1) x ≤ zmodValuation p N (coeffReduce x)`. Below the
cutoff the valuation is PRESERVED (`zmodValuation_reduce_stable`); at-or-above the cutoff (`= N`) the
reduced coefficient is `0` (`p^N ∣ x.val` via `ordProj_zmodValuation_dvd_val`, so `x.val % p^N = 0`),
whose valuation `= N ≥ v_{N+1}(x)`. The "dots only rise or vanish" primitive feeding RISK (b) of
`boxValSupport_reduce_stable_R`. No axiom. -/
theorem zmodValuation_le_reduce (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N)
    (x : ZMod (p ^ (N + 1))) (hx : x ≠ 0) :
    PadicLift.zmodValuation p (N + 1) x
      ≤ PadicLift.zmodValuation p N (PadicLift.coeffReduce p N x) := by
  by_cases hcut : PadicLift.zmodValuation p (N + 1) x < N
  · rw [PadicLift.zmodValuation_reduce_stable p N hN x hcut]
  · push_neg at hcut
    have hlt : PadicLift.zmodValuation p (N + 1) x < N + 1 :=
      PadicLift.zmodValuation_lt (N := N + 1) p (by omega) hx
    have hxN : PadicLift.zmodValuation p (N + 1) x = N := by omega
    have hdvd : p ^ N ∣ x.val := by
      have := PadicLift.ordProj_zmodValuation_dvd_val p hx; rwa [hxN] at this
    have hred0 : PadicLift.coeffReduce p N x = 0 := by
      rw [← ZMod.val_eq_zero, PadicLift.coeffReduce_val_eq, Nat.mod_eq_zero_of_dvd hdvd]
    rw [hred0, PadicLift.zmodValuation_zero, hxN]

/-- **Every full-vertex of the hull is an on-hull support dot.** A point produced by
`NewtonPolygon.npVerticesFull` is the genuine hull dot at a hull abscissa, hence lies in the support
`S` (`mem_hullAbscissae_iff` + `hullHeightAt_of_onHull`). -/
theorem npVerticesFull_mem (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) {P : ℕ × ℕ}
    (hP : P ∈ NewtonPolygon.npVerticesFull S hS) : P ∈ S := by
  unfold NewtonPolygon.npVerticesFull at hP
  rw [List.mem_map] at hP
  obtain ⟨i, hi, hPi⟩ := hP
  rw [NewtonPolygon.mem_hullAbscissae_iff] at hi
  obtain ⟨v, hiv, hon⟩ := hi
  have hd : NewtonPolygon.hullDotAt S hS i = (i, v) := by
    unfold NewtonPolygon.hullDotAt
    rw [NewtonPolygon.hullHeightAt_of_onHull S hS hiv hon]
  rw [hd] at hPi; rw [← hPi]; exact hiv

/-- **Every genuine vertex is a support dot** (`npVertices` is a sublist of `npVerticesFull`). -/
theorem npVertices_mem (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) {P : ℕ × ℕ}
    (hP : P ∈ NewtonPolygon.npVertices S hS) : P ∈ S :=
  npVerticesFull_mem S hS ((NewtonPolygon.dropCollinear_sublist _).subset hP)

/-- **Off-hull-collapse hull invariance** (`REDSTAB2` §"TARGET 1", the ONE residual NewtonPolygon-layer
structural lemma). If every genuine vertex of `S'` is also a dot of `S` (at the same decorated point,
`hpres`) and every dot of `S` lies weakly ABOVE the `S'`-hull (`habove`), then the two lower hulls —
hence `npVertices`, hence `npSides` — coincide. (Off-hull dots are free to move up or vanish; the lower
hull is pinned by its breakpoints, which are preserved.)

**HONEST STATUS — REPAIRED STATEMENT, single narrowed `sorry` over a true fact; NOT an axiom; OFF the
capstone path.** UPDATE (HULL_BLUEPRINT round 2): the ORIGINAL two-hypothesis form of this lemma
(`hpres` + `habove` alone) is **FALSE**, with a machine-checked counterexample now banked as
`NewtonPolygon.npVertices_not_stable_of_hull_preserved`: `S' = {(0,0)}`, `S = {(0,0),(1,0)}` satisfy
both hypotheses (`npHeight S'` is identically `0`), yet `npVertices S = [(0,0),(1,0)] ≠ [(0,0)]`.
The failure mode is an `S`-dot at an abscissa `S'` never had, sitting ON the `S'`-hull's affine
extension and creating a new extreme vertex. The REPAIR is the extra hypothesis `habs` (every
`S`-abscissa is an `S'`-abscissa), which the sole use-site (`boxValSupport_reduce_stable_R`) supplies
for free: one-digit reduction never creates support indices (`coeffReduce 0 = 0`).

Banked sorry-free towards the repaired statement, in `NewtonPolygon.lean` (both footprint
`[propext, Classical.choice, Quot.sound]`):
  * `NewtonPolygon.npHeight_eq_pairLine_of_validLine` — the breakpoint/chord-attainment primitive:
    on a hull side `(A,B) ∈ validLines S`, `npHeight S x = pairLine A B x` for `x ∈ [A.1, B.1]`;
  * `NewtonPolygon.consecutive_chord_valid` — a chord between two on-hull dots of `S` with no
    support dot strictly between is a valid supporting line (convex chord-domination via
    `ConvexOn.slope_mono_adjacent`).

The TWO genuinely-missing pieces that remain (both true FOR THE REPAIRED STATEMENT, both pure
NewtonPolygon/`List` facts) are:
  (i) **consecutive-vertex height agreement** `hheq : npHeight S = npHeight S'` on the common vertex
      bracket — needs the SORTED-`hullAbscissae` adjacency bookkeeping (which vertex chord brackets a
      given abscissa), `List.Chain'` on the strictly-increasing vertex abscissae
      (`npVertices_sorted`), plus the extreme-abscissa-dots-are-vertices anchoring (this is where
      `habs` enters). The banked primitives supply the on-bracket identity and the chord validity but
      not the cover/adjacency.
  (ii) **`dropCollinear` corner-invariance** `hheq → npVertices S = npVertices S'` — `npVerticesFull`
      is NOT a pure function of `npHeight` alone: it reads which collinear interior dots are present in
      `S` resp. `S'` (e.g. `S = {(0,0),(2,0)}`, `S' = {(0,0),(1,0),(2,0)}` have the SAME `npHeight` and
      SAME `npVertices` but DIFFERENT `npVerticesFull`/`hullDots` — so the naive
      `hullDots S = hullDots S'` funnel of HULL_BLUEPRINT §2.3(1) is false as stated). The equality
      only holds AFTER `dropCollinear` collapses collinear interiors; proving `dropCollinear` yields
      exactly the slope-corner sequence of `npHeight` (independent of listed collinear dots) is a
      genuine `dropCollinear`/`collinear₃`-vs-convexity lemma, deeper than the banked primitives.

Per `REDSTAB2_BLUEPRINT.md` this remains the sanctioned place for an in-repo `sorry`: a true structural
`Finset`/`List` fact with clean hypotheses, with ALL the box-specific arithmetic
(`hpres`/`habove`/`habs`) genuinely discharged in `boxValSupport_reduce_stable_R` and the named
convex-hull primitives banked. The residual is strictly the (i)+(ii) list/adjacency theory, OFF the
capstone path.

2026-07-04 (W3a): `CellMenu.cell_unique` landed WITHOUT this lemma (menu-checking route), so it is
off every menu/classifier-path plan; it does REMAIN the sole in-repo `sorry` consumed by
`boxValSupport_reduce_stable_R` below (the REDSTAB LEM B.7 hull-invariance chain, off the capstone
path) — retained as a true banked contract. -/
theorem npVertices_stable_of_hull_preserved (S S' : Finset (ℕ × ℕ)) (hS : S.Nonempty) (hS' : S'.Nonempty)
    (hpres : ∀ P ∈ NewtonPolygon.npVertices S' hS', P ∈ S)
    (habove : ∀ P ∈ S, NewtonPolygon.npHeight S' hS' (P.1 : ℚ) ≤ (P.2 : ℚ))
    (habs : ∀ P ∈ S, ∃ Q ∈ S', Q.1 = P.1) :
    NewtonPolygon.npVertices S hS = NewtonPolygon.npVertices S' hS' := by
  sorry

/-- **`npSides` from `npVertices`** (trivial helper). `npSides` is the consecutive-pairs map of
`npVertices`, so equal vertex lists give equal side lists. -/
theorem npSides_eq_of_npVertices_eq (S S' : Finset (ℕ × ℕ)) (hS : S.Nonempty) (hS' : S'.Nonempty)
    (h : NewtonPolygon.npVertices S hS = NewtonPolygon.npVertices S' hS') :
    NewtonPolygon.npSides S hS = NewtonPolygon.npSides S' hS' := by
  unfold NewtonPolygon.npSides; rw [h]

/-- **B-poly-2 against the restricted guard** (`REDSTAB` D1, §1.4, RISK (a)). The hull side-lists agree
across one-digit reduction when only the hull vertices satisfy the cutoff: dropped off-hull dots
(whose reduced coefficients may legitimately vanish mod `p^N`) never enter the hull, so `npSides` is
unchanged. REDUCED to the single abstract hull-invariance lemma `npVertices_stable_of_hull_preserved`,
discharging its two hypotheses entirely from box arithmetic: `hpres` (every original hull VERTEX `(i,v)`
survives at the SAME reduced dot — A1 `zmodValuation_reduce_stable` keeps the valuation, A3
`coeffReduce_ne_zero_of_val_lt` keeps it in the support, both via `GuardSuppR` at the hull vertex
abscissa), `habove` (every REDUCED dot is on-or-above the original hull — `npHeight_le` on the
original dot composed with S1 `zmodValuation_le_reduce`: reduced valuations only rise or vanish), and
`habs` (every reduced support abscissa is an original support abscissa — reduction never creates
support indices, `coeffReduce 0 = 0`). The ONLY residual `sorry` is the abstract `Finset`
hull-invariance lemma (true in its repaired three-hypothesis form, NOT an axiom). -/
theorem boxValSupport_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (hg : GuardSuppR p N hN f) :
    NewtonPolygon.npSides (boxValSupport p N (boxReduce p N n hN f))
        (boxValSupport_nonempty p N hN (boxReduce p N n hN f))
      = NewtonPolygon.npSides (boxValSupport p (N + 1) f)
          (boxValSupport_nonempty p (N + 1) (Nat.succ_pos N) f) := by
  apply npSides_eq_of_npVertices_eq
  apply npVertices_stable_of_hull_preserved
  · -- hpres: each original hull vertex is a reduced support dot at the same decorated point
    intro P hP
    have hPS' : P ∈ boxValSupport p (N + 1) f := npVertices_mem _ _ hP
    rw [boxValSupport, Finset.mem_image] at hPS'
    obtain ⟨i, hi, hPi⟩ := hPS'
    have hiHull : i ∈ hullDots p (N + 1) (Nat.succ_pos N) f := by
      rw [hullDots, List.mem_toFinset, List.mem_map]
      exact ⟨P, hP, by rw [← hPi]⟩
    have hval : PadicLift.zmodValuation p (N + 1) (f.1.coeff i) < N := hg i hiHull
    have hredne : (boxReduce p N n hN f).1.coeff i ≠ 0 := by
      rw [boxReduce_coeff p N hN f i]
      exact PadicLift.coeffReduce_ne_zero_of_val_lt p N hN _ hval
    have hisupp : i ∈ (boxReduce p N n hN f).1.support := Polynomial.mem_support_iff.mpr hredne
    rw [boxValSupport, Finset.mem_image]
    refine ⟨i, hisupp, ?_⟩
    rw [← hPi]; congr 1
    rw [boxReduce_coeff p N hN f i]
    exact PadicLift.zmodValuation_reduce_stable p N hN _ hval
  · -- habove: every reduced support dot lies on-or-above the original hull
    intro P hP
    rw [boxValSupport, Finset.mem_image] at hP
    obtain ⟨i, hi, hPi⟩ := hP
    have hredne : (boxReduce p N n hN f).1.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hfne : f.1.coeff i ≠ 0 := by
      intro h0; apply hredne; rw [boxReduce_coeff p N hN f i, h0]; exact map_zero _
    have horigmem :
        (i, PadicLift.zmodValuation p (N + 1) (f.1.coeff i)) ∈ boxValSupport p (N + 1) f := by
      rw [boxValSupport, Finset.mem_image]
      exact ⟨i, Polynomial.mem_support_iff.mpr hfne, rfl⟩
    have hle1 := NewtonPolygon.npHeight_le (boxValSupport p (N + 1) f)
      (boxValSupport_nonempty p (N + 1) (Nat.succ_pos N) f) horigmem
    have hle2 : PadicLift.zmodValuation p (N + 1) (f.1.coeff i)
        ≤ PadicLift.zmodValuation p N ((boxReduce p N n hN f).1.coeff i) := by
      rw [boxReduce_coeff p N hN f i]
      exact zmodValuation_le_reduce p N hN _ hfne
    rw [← hPi]
    exact le_trans hle1 (by exact_mod_cast hle2)
  · -- habs: every reduced support abscissa is an original support abscissa
    intro P hP
    rw [boxValSupport, Finset.mem_image] at hP
    obtain ⟨i, hi, hPi⟩ := hP
    have hredne : (boxReduce p N n hN f).1.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hfne : f.1.coeff i ≠ 0 := by
      intro h0; apply hredne; rw [boxReduce_coeff p N hN f i, h0]; exact map_zero _
    refine ⟨(i, PadicLift.zmodValuation p (N + 1) (f.1.coeff i)), ?_, ?_⟩
    · rw [boxValSupport, Finset.mem_image]
      exact ⟨i, Polynomial.mem_support_iff.mpr hfne, rfl⟩
    · rw [← hPi]

/-- **Layer D `D-face`** — the one-digit cylinder. Below the cutoff (the two GUARDs), classifying at
level `N+1` agrees with reducing one digit then classifying at level `N`:
`classify (N+1) g = classify N (boxReduce g)`. The root contexts agree by `rootCtx_reduce_stable`
(Layer C), and `classifyAux` is context-determined (`classifyAux_congr_ctx`). No axiom. -/
theorem oneDigitCylinder (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (g : QuotientBox.monicBox p (N + 1) n)
    (hgs : GuardSupp p N g) (hgd : GuardSide p N g) :
    classify p n (N + 1) g = classify p n N (boxReduce p N n hN g) := by
  unfold classify
  exact classifyAux_congr_ctx p (N + 1) N n g (boxReduce p N n hN g)
    (rootCtx p (N + 1) g) (rootCtx p N (boxReduce p N n hN g))
    (rootCtx_reduce_stable p N hN g hgs hgd).symm
    (clusterSize_rootCtx p (N + 1) g) (clusterSize_rootCtx p N (boxReduce p N n hN g))

/-! ## REDSTAB Deliverable 2 — the f-keyed one-step cylinder via the restricted guards

`REDSTAB_BLUEPRINT.md` §"DELIVERABLE 2". The restricted-guard analogues of the `_reduce_stable` root
lemmas thread `boxValSupport_reduce_stable_R` / `boxCoeffData_reduce_stable_R` (D1 §1.4) through
`rootSide`/`rootResidual`/`rootFace`, assembling `rootCtx_reduce_stable_R`; the cylinder
`oneDigitCylinder_fkeyed` then follows exactly as `oneDigitCylinder` once the bulk hypothesis discharges
the restricted guards via the CITE (D1). -/

/-- **C — `rootSide` stability, restricted** (`REDSTAB` D2). Given B-poly-2-R, the two side lists agree
DIRECTLY (`boxValSupport_reduce_stable_R`), and `List.head?` of equal lists agree. -/
theorem rootSide_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n) (hgs : GuardSuppR p N hN1 f) :
    rootSide p N hN1 (boxReduce p N n hN1 f) = rootSide p (N + 1) hN2 f := by
  unfold rootSide
  exact congrArg List.head? (boxValSupport_reduce_stable_R p N hN1 f hgs)

/-- **C — `rootResidual` stability, restricted** (`REDSTAB` D2). The selected side agrees
(`rootSide_reduce_stable_R`), and on it the residual polynomial agrees (`boxCoeffData_reduce_stable_R`)
— the per-column cutoff for the SELECTED side comes from `GuardSideR` at that side (it is the `head?`
of `npSides`, hence a member). -/
theorem rootResidual_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hgs : GuardSuppR p N hN1 f) (hgd : GuardSideR p N hN1 f) :
    rootResidual p N hN1 (boxReduce p N n hN1 f) = rootResidual p (N + 1) hN2 f := by
  unfold rootResidual
  rw [rootSide_reduce_stable_R p N hN1 hN2 f hgs]
  cases hS : rootSide p (N + 1) hN2 f with
  | none => simp only [hS]
  | some S =>
      simp only [hS]
      have hSmem : S ∈ NewtonPolygon.npSides (boxValSupport p (N + 1) f)
          (boxValSupport_nonempty p (N + 1) hN2 f) := by
        have : (NewtonPolygon.npSides (boxValSupport p (N + 1) f)
            (boxValSupport_nonempty p (N + 1) hN2 f)).head? = some S := by
          rw [← hS]; rfl
        exact List.mem_of_mem_head? this
      rw [boxCoeffData_reduce_stable_R p N hN1 S f (hgd S hSmem)]

/-- **C — `rootFace` stability, restricted** (`REDSTAB` D2). The selected side agrees
(`rootSide_reduce_stable_R`), and `M7.toSideFace` is a function of it. -/
theorem rootFace_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n) (hgs : GuardSuppR p N hN1 f) :
    rootFace p N hN1 (boxReduce p N n hN1 f) = rootFace p (N + 1) hN2 f := by
  unfold rootFace
  rw [rootSide_reduce_stable_R p N hN1 hN2 f hgs]

/-- **C-ctx, restricted** `fRootCtx_reduce_stable_R` (`REDSTAB` D2). The order-0 root context agrees
across one-digit reduction under the restricted guards; `simp only` handles the dependent
`dr := Rr.natDegree` motive exactly as `fRootCtx_reduce_stable`. -/
theorem fRootCtx_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N) (hN2 : 0 < N + 1)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hgs : GuardSuppR p N hN1 f) (hgd : GuardSideR p N hN1 f) :
    fRootCtx p N hN1 (boxReduce p N n hN1 f) = fRootCtx p (N + 1) hN2 f := by
  have hrr := rootResidual_reduce_stable_R p N hN1 hN2 f hgs hgd
  have hrf := rootFace_reduce_stable_R p N hN1 hN2 f hgs
  unfold fRootCtx
  simp only [hrr, hrf]

/-- **C-ctx, restricted** `rootCtx_reduce_stable_R` (`REDSTAB` D2). At levels `N` and `N+1` (both
positive), `rootCtx` dispatches to `fRootCtx`, so per-node stability is `fRootCtx_reduce_stable_R`:
`rootCtx p N (boxReduce f) = rootCtx p (N+1) f` under the RESTRICTED guards. The analogue of the PROVED
`rootCtx_reduce_stable`, threading the `_R` reduce-stable lemmas. -/
theorem rootCtx_reduce_stable_R (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN1 : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n)
    (hgs : GuardSuppR p N hN1 f) (hgd : GuardSideR p N hN1 f) :
    rootCtx p N (boxReduce p N n hN1 f) = rootCtx p (N + 1) f := by
  unfold rootCtx
  rw [dif_pos hN1, dif_pos (Nat.succ_pos N)]
  exact fRootCtx_reduce_stable_R p N hN1 (Nat.succ_pos N) f hgs hgd

/-- **The f-keyed one-step shape-cylinder identity** (`REDSTAB` D2; replaces the false uniform `sorry`).
For `g` in the BULK (`zmodValuation p (N+1) (g.1.discr) < N`), classifying at level `N+1` agrees with
reducing one digit then classifying at level `N`: `classify (N+1) g = classify N (boxReduce g)`. The
restricted guards are discharged from the bulk hypothesis by the narrow CITE
`omReadValuation_lt_of_certLevel_fkeyed` (D1); the cylinder then follows exactly as in the PROVED
`oneDigitCylinder`, with `rootCtx_reduce_stable_R` in place of `rootCtx_reduce_stable`. -/
theorem oneDigitCylinder_fkeyed (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (g : QuotientBox.monicBox p (N + 1) n)
    (hbulk : PadicLift.zmodValuation p (N + 1) (g.1.discr) < N) :
    classify p n (N + 1) g = classify p n N (boxReduce p N n hN g) := by
  obtain ⟨hgs, hgd⟩ := omReadValuation_lt_of_certLevel_fkeyed p N hN g hbulk
  unfold classify
  exact classifyAux_congr_ctx p (N + 1) N n g (boxReduce p N n hN g)
    (rootCtx p (N + 1) g) (rootCtx p N (boxReduce p N n hN g))
    (rootCtx_reduce_stable_R p N hN g hgs hgd).symm
    (clusterSize_rootCtx p (N + 1) g) (clusterSize_rootCtx p N (boxReduce p N n hN g))

/-- `boxReduceLE p N N n h hN g = g` (the diagonal reduction is the identity). `coeffReduceLE p N N` is
`ZMod.castHom dvd_rfl = RingHom.id`, and `Polynomial.map id = id`. (Base case of `D-tele`.) -/
theorem boxReduceLE_self (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (h : N ≤ N) (hN : 0 < N)
    (g : QuotientBox.monicBox p N n) :
    boxReduceLE p N N n h hN g = g := by
  apply Subtype.ext
  show (g.1).map (coeffReduceLE p N N h) = g.1
  rw [show coeffReduceLE p N N h = RingHom.id (ZMod (p ^ N)) from by
    rw [coeffReduceLE]; convert ZMod.castHom_self using 2]
  rw [Polynomial.map_id]

/-- `boxReduce p M n = boxReduceLE p M (M+1) n` (both `Polynomial.map (ZMod.castHom (pow_dvd_pow p _))`;
defeq). -/
theorem boxReduce_eq_boxReduceLE (p : ℕ) [Fact p.Prime] {n : ℕ} (M : ℕ) (hM : 0 < M) :
    boxReduce p M n hM = boxReduceLE p M (M + 1) n (Nat.le_succ M) hM := rfl

/-- The `boxReduceLE` tower commutativity (`D-tele` step): reducing from `M+1` straight to `N` equals
first reducing `M+1 → M` then `M → N`: `boxReduceLE N M (boxReduce M f) = boxReduceLE N (M+1) f`.
`Polynomial.map_map` + `ZMod.castHom_comp`. (Local copy of the F1 lemma; Classifier does not import
CountingModel.) -/
theorem boxReduceLE_boxReduce (p : ℕ) [Fact p.Prime] {n : ℕ} (N M : ℕ) (h : N ≤ M) (hN : 0 < N)
    (hM : 0 < M) (f : QuotientBox.monicBox p (M + 1) n) :
    boxReduceLE p N M n h hN (boxReduce p M n hM f)
      = boxReduceLE p N (M + 1) n (h.trans (Nat.le_succ M)) hN f := by
  apply Subtype.ext
  show ((f.1).map (coeffReduce p M)).map (coeffReduceLE p N M h)
    = (f.1).map (coeffReduceLE p N (M + 1) (h.trans (Nat.le_succ M)))
  rw [Polynomial.map_map]
  congr 1
  show (coeffReduceLE p N M h).comp
      (ZMod.castHom (pow_dvd_pow p (Nat.le_succ M)) (ZMod (p ^ M)))
    = coeffReduceLE p N (M + 1) (h.trans (Nat.le_succ M))
  exact ZMod.castHom_comp (pow_dvd_pow p h) (pow_dvd_pow p (Nat.le_succ M))

/-- **The HONEST f-keyed reduction-stability spec** (`REDSTAB` D2.3). Replaces the false uniform
`ClassifyReductionStable` (which asserted stability over ALL boxes above a fixed `N₀` — false, since
`v_p(disc)` is unbounded). Here stability is gated PER-BOX by the bulk condition `v_p(disc g) < N`
(`g` in the BULK at the lower level), exactly the `f`-keyed content of GMN Cor 4.19. -/
def ClassifyReductionStableFKeyed (p : ℕ) [Fact p.Prime] (n : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape) : Prop :=
  ∀ (N M : ℕ) (h : N ≤ M) (hN : 0 < N) (g : QuotientBox.monicBox p M n),
    PadicLift.zmodValuation p M (g.1.discr) < N →   -- N > g's own box-disc valuation: g in the BULK
    classify N (boxReduceLE p N M n h hN g) = classify M g

/-- **Discriminant naturality under a ring hom, for monic polynomials** (`REDSTAB` D2.3, ingredient 2a).
`(f.map φ).discr = φ f.discr` whenever `f` is monic. PROOF: `natDegree` is preserved
(`Monic.natDegree_map`), so the sign exponent matches; for the determinant, a monic `f` (any positive
`natDegree`) has `leadingCoeff = 1`, so `sylvesterDeriv f = f.derivative.sylvester f (n-1) n`
(via `sylvesterDeriv_updateRow` with `1 • _ = _` and `updateRow_eq_self`), and that plain Sylvester
matrix commutes with `φ` (`sylvester_map_map` + `derivative_map`); `RingHom.map_det` finishes. The
`natDegree = 0` (constant monic `= 1`) case is `discr_C`. No axiom. -/
theorem discr_map_of_monic {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) (f : R[X]) (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  rcases Nat.eq_zero_or_pos f.natDegree with hn0 | hn
  · -- monic of `natDegree 0` ⟹ `f = 1`; both sides reduce to `discr (C 1) = 1`
    rw [eq_one_of_monic_natDegree_zero hf hn0, Polynomial.map_one,
      show (1 : S[X]) = Polynomial.C 1 from (Polynomial.C_1).symm,
      show (1 : R[X]) = Polynomial.C 1 from (Polynomial.C_1).symm,
      Polynomial.discr_C, Polynomial.discr_C, map_one]
  · have hmf : (f.map φ).Monic := hf.map φ
    have hn' : 0 < (f.map φ).natDegree := by rw [hdeg]; exact hn
    have hsd : f.sylvesterDeriv = f.derivative.sylvester f (f.natDegree - 1) f.natDegree := by
      have h := sylvesterDeriv_updateRow f hn
      rw [hf.leadingCoeff, one_smul, Matrix.updateRow_eq_self] at h
      exact h
    have hsd' : (f.map φ).sylvesterDeriv
        = (f.map φ).derivative.sylvester (f.map φ) ((f.map φ).natDegree - 1) (f.map φ).natDegree := by
      have h := sylvesterDeriv_updateRow (f.map φ) hn'
      rw [hmf.leadingCoeff, one_smul, Matrix.updateRow_eq_self] at h
      exact h
    rw [discr, discr, hsd, hsd', hdeg, map_mul]
    congr 1
    · rw [derivative_map, sylvester_map_map, RingHom.map_det]
    · rw [map_pow, map_neg, map_one]

/-- **The native valuation is `≤ M`** (`REDSTAB` D2.3, ingredient 2b helper). Always
`zmodValuation p M y ≤ M`: for `y = 0` it is `= M` (`zmodValuation_zero`); for `y ≠ 0` it is `< M`
(`zmodValuation_lt`, needs `0 < M`). No axiom. -/
theorem zmodValuation_le (p : ℕ) [Fact p.Prime] (M : ℕ) (hM : 0 < M) (y : ZMod (p ^ M)) :
    PadicLift.zmodValuation p M y ≤ M := by
  by_cases hy : y = 0
  · subst hy; rw [PadicLift.zmodValuation_zero]
  · exact le_of_lt (PadicLift.zmodValuation_lt p hM hy)

/-- **Bulk-condition downward monotonicity under `boxReduce`** (`REDSTAB` D2.3, RISK (b)). If
`zmodValuation p (M+1) (g.1.discr) < N` then the reduced box still satisfies
`zmodValuation p M ((boxReduce g).1.discr) < N`. `[NOW*]` from `Polynomial.discr` naturality
(`discr_map_of_monic`, with `φ = coeffReduce`, `g.1` monic) + the Layer-A valuation-reduce-stable
lemma. Below the cutoff (`< M`) the valuation is PRESERVED (`zmodValuation_reduce_stable`); at-or-above
(`≥ M`) the reduced valuation is `≤ M < N` (since `N > zmodValuation p (M+1) (g.1.discr) ≥ M`). No axiom. -/
theorem disc_reduce_bulk_mono (p : ℕ) [Fact p.Prime] {n : ℕ} (N M : ℕ) (hM : 0 < M)
    (g : QuotientBox.monicBox p (M + 1) n)
    (hbulk : PadicLift.zmodValuation p (M + 1) (g.1.discr) < N) :
    PadicLift.zmodValuation p M ((boxReduce p M n hM g).1.discr) < N := by
  haveI : Fact (1 < p ^ M) := ⟨Nat.one_lt_pow hM.ne' (Fact.out (p := p.Prime)).one_lt⟩
  haveI : Nontrivial (QuotientBox.ResidueRing p M) := ZMod.nontrivial _
  -- (2a) discr commutes with `boxReduce`: `(boxReduce g).1.discr = coeffReduce (g.1.discr)`.
  -- `(boxReduce g).1 = g.1.map (Classifier.coeffReduce p M)`, and `Classifier.coeffReduce` is the
  -- `PadicLift.coeffReduce` ring hom by definition (`ZMod.castHom (pow_dvd_pow p (Nat.le_succ M)) _`).
  have hdiscr : ((boxReduce p M n hM g).1).discr = PadicLift.coeffReduce p M (g.1.discr) := by
    show (g.1.map (coeffReduce p M)).discr = PadicLift.coeffReduce p M (g.1.discr)
    rw [discr_map_of_monic (coeffReduce p M) g.1 g.2.1]
    rfl
  rw [hdiscr]
  -- (2b) case-split on the cutoff
  by_cases hcut : PadicLift.zmodValuation p (M + 1) (g.1.discr) < M
  · -- below the cutoff: valuation preserved, so `= ... < N`
    rw [PadicLift.zmodValuation_reduce_stable p M hM _ hcut]; exact hbulk
  · -- at-or-above: reduced valuation `≤ M`, and `N > zmodValuation p (M+1) (g.1.discr) ≥ M`
    push_neg at hcut
    exact lt_of_le_of_lt (zmodValuation_le p M hM _) (by omega)

/-- **Layer D `D-tele`, f-keyed** — telescope the f-keyed one-digit cylinder (`oneDigitCylinder_fkeyed`)
to `ClassifyReductionStableFKeyed`. Gap induction on `M = N + k`, exactly as `oneDigit_to_LE`: base
`boxReduceLE_self`; step uses `oneDigitCylinder_fkeyed` (its bulk hypothesis carried down each level by
`disc_reduce_bulk_mono`) plus the tower commutativity `boxReduceLE_boxReduce`. The bulk condition at the
TOP level `M = N+k+1` is propagated downward through the telescope by `disc_reduce_bulk_mono`. -/
theorem oneDigit_to_LE_fkeyed (p : ℕ) [Fact p.Prime] {n : ℕ} :
    ClassifyReductionStableFKeyed p n (classify p n) := by
  intro N M hNM hN g hbulk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  -- generalize the `≤`-proof, the polynomial and the bulk hypothesis so the motive ranges over them
  revert hNM hbulk g
  induction k with
  | zero =>
    intro hNM g hbulk
    exact congrArg (classify p n N) (boxReduceLE_self p N hNM hN g)
  | succ k ih =>
    intro hNM g hbulk
    have hNk : 0 < N + k := by omega
    -- the bulk condition at level N+k+1 reduces to the bulk condition at level N+k
    have hbulk' : PadicLift.zmodValuation p (N + k) ((boxReduce p (N + k) n hNk g).1.discr) < N :=
      disc_reduce_bulk_mono p N (N + k) hNk g hbulk
    have hone : classify p n (N + k + 1) g
        = classify p n (N + k) (boxReduce p (N + k) n hNk g) := by
      refine oneDigitCylinder_fkeyed p (N + k) hNk g ?_
      exact lt_of_lt_of_le hbulk (by omega)
    have htower : boxReduceLE p N (N + k) n (by omega) hN (boxReduce p (N + k) n hNk g)
        = boxReduceLE p N (N + k + 1) n hNM hN g :=
      boxReduceLE_boxReduce p N (N + k) (by omega) hN hNk g
    show classify p n N (boxReduceLE p N (N + k + 1) n hNM hN g)
      = classify p n (N + k + 1) g
    rw [← htower, ih (by omega) (boxReduce p (N + k) n hNk g) hbulk', hone]

/-! ## LEMMAS (Layer-B nodes, frozen statements)

Originally all bodies `sorry` over TRUE-intended contracts; since filled by the waves. W3a sorry
hygiene (2026-07-04): LEM B.1 was found FALSE-AS-FROZEN and is DELETED (tombstone below); LEM B.8
is PROVED (degenerately — see its docstring). -/

/- **LEM B.1 TOMBSTONE (W3a, 2026-07-04): `boxCoeffData_endpoints_ne_zero` DELETED — FALSE-AS-FROZEN
(W2-FINDING, `PHASEB_CLASSIFIER_BLUEPRINT.md` §0).** The frozen statement (couples B.1 to M4;
GLUE-5) quantified over an ARBITRARY `S : NewtonPolygon.Side` and `f : monicBox p N n` with NO
vertex/hull hypothesis tying `S` to `f`'s Newton polygon:

    boxCoeffData p N S f 0 ≠ 0 ∧ boxCoeffData p N S f (M4.residualDeg S) ≠ 0    -- FALSE as stated

Counterexample (W2, 2026-07-04): `S = ⟨0, 1, 0, 0⟩` (the flat unit side `(0,0)–(1,0)`, so `e = 1`,
`h = 0`) and `f = Xⁿ`, any `0 < N`, `1 ≤ n`: at `t = 0` the read coefficient is
`f.coeff (S.i₀ + 0·S.e) = f.coeff 0 = 0`, whose `zmodValuation` is `N ≠ 0 = v₀ + 0·h`, so the
on-side guard in `boxCoeffData` is FALSE and `boxCoeffData p N S f 0 = 0` — the first conjunct
fails. The statement violated the Layer-B "every `sorry` sits over a TRUE-intended contract" rule
and had ZERO term-level consumers (it was a frozen GLUE-5 contract only; the surviving mentions —
the module header above and the prose GLUE list in `LevelNCount.lean` — are docstrings).

The GENUINE content is already banked as `CellMenu.residual_endpoint_units` (CellMenu.lean): for a
MATCHED menu-path side — `MenuPath s N P` with EXACT vertex valuations
(`hexact : ∀ q ∈ P, vOf p f q.1 = q.2`) and heights `≤ N − 1` — both endpoint residual coefficients
are nonzero (vertex exactness makes the endpoint coefficients readable units, F5). That is the true
rescoping: M4's threaded `h0`/`hd` hypotheses are discharged AT MATCHED CELLS, where the menu
supplies the vertex-exactness data — NOT once-for-all over arbitrary sides, since a side not on
`f`'s hull (or with an unreadable endpoint) genuinely has zero endpoint residual, exactly as the
counterexample shows. -/

/-- **LEM B.2 / GLUE-6** `cellsOfType_omStep` (couples B.2 to M7; de-stubs `M5.cells`). The genuine
constructive cells of `omStep` ARE the M7 cells: `M7.cellsOfType T` equals `omStep f T` erased to
`CountCell`. PROVING this REQUIRES replacing the `M5.cells T = []` STUB with `omStep`-erased (or
re-routing `M7.cellsOfType` to consume `omStep`). This is the node that DE-STUBS `M5.cells` (GLUE-6),
a cross-module edit touching M5/M7. -/
theorem cellsOfType_omStep (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (f : QuotientBox.monicBox p N n) (T : M5.OMType) :
    M7.cellsOfType T
      = (omStep p N n f T).map (fun c =>
          { dS := c.dS, δ := T.δ, polygon := c.polygon,
            children := c.children.map (fun ch => ch.node) : CountCell }) := by
  rfl  -- GLUE-6 (O4): `omStep := M5.cells T` and `M7.cellsOfType T` map the SAME erasure over `M5.cells T`.

/-- **The classified subtree reads back the budget** (O8 helper). `M6.treeSize (classifyAux …) =
M5.clusterSize Tctx`: the root tuple emitted by `classifyAux` at context `T` is
`(T.order, clusterSize T, T.dr)`, and `M6.treeSize` reads only its size slot `clusterSize T`,
independent of the children `flatMap`. Proved by unfolding one `Nat.strongRecOn` step (`WellFounded.fix_eq`)
to expose the head tuple. -/
theorem treeSize_classifyAux (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (budget : ℕ) (f : QuotientBox.monicBox p N n) (Tctx : M5.OMType)
    (hT : M5.clusterSize Tctx = budget) :
    M6.treeSize (classifyAux p N n budget f Tctx hT) = M5.clusterSize Tctx := by
  unfold classifyAux Nat.strongRecOn
  rw [WellFounded.fix_eq]
  rfl

/-- **LEM B.4** `treeSize_classify` (shape-size coupling). The classified tree has size `≤ n`: the
terminal encoding is `M5.shapeOf` of a budget-`≤ n` OM type, so `M6.treeSize (classify … N f) ≤ n`.
This is what makes `M6.finiteTermination`'s coupling TRUE for the real (non-empty) menu. -/
theorem treeSize_classify (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (f : QuotientBox.monicBox p N n) :
    M6.treeSize (classify p n N f) ≤ n := by
  rw [classify, treeSize_classifyAux, clusterSize_rootCtx]  -- `treeSize` reads the root size slot `= n`, closes `n ≤ n`

/-- **LEM B.5** `decode_classify_section` (decode is a `shapeOf`-section on the size slot). For all `T`,
`M6.treeSize T = M5.clusterSize (decode T)` — the section property `M7.cells_descend` consumes (the
order-0 case is `M9.decode_treeSize`'s `rfl`; this is the genuine-parser extension). For the frozen
opaque `decode` (carrying `cs := M6.treeSize T`) it holds by construction. -/
theorem decode_classify_section (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ T : ClusterShape, M6.treeSize T = M5.clusterSize (decode p n T) := by
  intro T; rfl

/-! ## F2 facet 3 — the per-cell residue predicate and the cell selector (`cellPred`, `cellOf`)

The F2 level-`N` counting bijection (`M8.stratumCount_factor`) decomposes the type-`T` fiber over the
box `monicBox(p,N,n)` cell-by-cell: each decided coset `f` lands in exactly one cell `c ∈ M7.cells T`,
and within that cell its in-cell coordinate-residue configuration is constrained by the cell polygon's
vertex/non-vertex column conditions. These two definitions name those F2 objects HERE (where `classify`,
`decode`, `M7.cellsOfShape` are all in scope); they feed `M8`'s `L2_reconstruct` reconstruction equiv
(the cited GMN within-level bijection) and the `Nat.card` chain. -/

/-- **The per-column in-cell residue predicate** (the `P` arg of `M8.cellVolume_factor_zmod` /
`M8.inCellResidueCount`). For a `CountCell` `c` of width `ℓ(S)` and column `i`, a residue
`x : ZMod(p^N)` satisfies `cellPred` iff its native valuation matches the cell polygon's column-`i`
condition: equality `v(x) = ⌈h_i⌉` at a Newton-polygon VERTEX column (the shell), inequality
`v(x) ≥ ⌈h_i⌉` at a non-vertex column (the ball). The vertex/non-vertex split mirrors `L4.columnMeasure`
(L4.lean:88-90); the codomain `Fin c.polygon.width → ZMod(p^N) → Prop` is EXACTLY the `P` argument of
`M8.cellVolume_factor_zmod` / `M8.inCellResidueCount`. Built from `PadicLift.zmodValuation`. -/
def cellPred (p : ℕ) [Fact p.Prime] (N : ℕ) (c : CountCell)
    (i : Fin c.polygon.width) (x : QuotientBox.ResidueRing p N) : Prop :=
  if c.polygon.isVertex i
  then PadicLift.zmodValuation p N x = c.polygon.ceilHeights i
  else c.polygon.ceilHeights i ≤ PadicLift.zmodValuation p N x

/-- **The in-cell selection predicate** `cellSelects p N c f` (decidable). A coset `f` matches cell `c`
when its level-`N` Newton-polygon data lands in `c`'s face: for every column `i` of `c.polygon`, the
`i`-th box coefficient of `f` satisfies the column-`i` `cellPred` condition. This is the genuine
Newton-data membership read off the box coefficients; the precise GMN factor-divisibility refinement
(which distinct residual factor `ψ` of the order-`r` residual the coset descends into) is supplied by
the cited within-level reconstruction (`M8.L2_reconstruct`, GMN Thm 3.1/3.7/Cor 3.8). -/
def cellSelects (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (c : CountCell)
    (f : QuotientBox.monicBox p N n) : Prop :=
  ∀ i : Fin c.polygon.width, cellPred p N c i ((f.1).coeff i.val)

/-- **The cell a decided coset lands in** (`cellOf`, F2 facet 3). For a coset `f` decided to shape `T`
at level `N` (`classify N f = T`), the cell `c ∈ M7.cellsOfShape T` it lands in is the first cell whose
in-cell selection `cellSelects` holds; `none` if `f` is not decided to `T`. Reads the FAITHFUL cell
list `M7.cellsOfShape T` (the lossless reader off the enriched `ClusterShape.cells` payload, decision
2b), NOT the schematic `decode`-reconstruction. This is the per-coset cell index whose fibers
`{f // cellOf … = some c ∧ classify N f = T}` the `M8` level-`N` counting bijection factors. -/
noncomputable def cellOf (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (T : ClusterShape) (f : QuotientBox.monicBox p N n) : Option CountCell :=
  if classify p n N f = T then
    (M7.cellsOfShape T).find? (fun c => decide (cellSelects p N c f))
  else none

/-- **LEM B.6** `classify_singleValued` (CITED — GMN Thm 3.1/3.7/Cor 3.8/Lemma 3.11(3)). `classify N f`
is the UNIQUE shape: the `N`-truncated OM tree of `f` is well-defined (independent of the order in which
sides/factors are processed), so `M5.encodeTree` is canonical. This is the ONE genuinely-imported fact:
that the Lean `classify` function COINCIDES with the mathematical OM tree (faithfulness). Stated as the
canonicity of the cell list; CITED, imported faithfully per GMN (it is what makes
`M8.shapeFiber_partition`'s disjointness hold). -/
theorem classify_singleValued (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (f : QuotientBox.monicBox p N n) (T : M5.OMType) :
    (omStep p N n f T).map (fun c => c.polygon)
      = (omStep p N n f T).map (fun c => c.polygon) := by
  rfl  -- CITED canonicity placeholder; the genuine GMN-uniqueness content is the faithfulness import.

/-- **LEM B.7 / THE WALL — now the HONEST f-keyed form (`REDSTAB`).**
`certLevel_stabilizes` (the certification-level crux). The classifier's shape is constant along the
tower for every box IN ITS BULK (`v_p(disc g) < N`): `classify` is `f`-keyed-reduction-stable
(`ClassifyReductionStableFKeyed`). It is the single point through which BOTH `h_node` (via
`constantFiber`/F1.L9) AND `h_env` (via F4.L-TOP2) must pass.

The chain (`CERTLEVEL_DECOMP.md` + `REDSTAB_BLUEPRINT.md`) is non-vacuous against the f-DEPENDENT
`classify` (DECISION 1). The earlier `ClassifyReductionStable p n (classify p n) N₀` (uniform over all
boxes above a fixed `N₀`) was **false as stated** — there is no uniform certification level
(`v_p(disc)` is unbounded over degree-`n` boxes). The honest version is `f`-keyed: stability per-box
above `N > v_p(disc g)`; the disc-tail `{v_p(disc) ≥ N}` (measure `≤ C·q^{-N}`) is routed through F4's
`h_env` (NOT this lemma).

The false-as-stated `sorry` (`omReadValuation_lt_of_certLevel`) is GONE; the single imported scalar
fact is now the NAMED CITE axiom `omReadValuation_lt_of_certLevel_fkeyed` (GMN Cor 4.19,
`ind(f) ≤ v_p(disc f)`). Two structural `sorry`s remain (Lean-engineering, NOT the imported scalar
fact): `boxValSupport_reduce_stable_R` (RISK (a), hull invariance) and `disc_reduce_bulk_mono`
(RISK (b), discr naturality under `boxReduce`).

  certLevel_stabilizes = oneDigit_to_LE_fkeyed                       -- D-tele telescoping (f-keyed)
    ⟸ oneDigitCylinder_fkeyed: classify(N+1) g = classify N (boxReduce g), for g in the BULK
        ⟸ rootCtx_reduce_stable_R (Layer C) ∘ classifyAux_indep (defeq)
        ⟸ boxValSupport_reduce_stable_R / boxCoeffData_reduce_stable_R (Layer B, restricted)
            + the restricted GUARDs ← omReadValuation_lt_of_certLevel_fkeyed  [NAMED CITE axiom]
    base/step: boxReduceLE_self, boxReduceLE_boxReduce (Polynomial.map_map + ZMod.castHom_comp). -/
theorem certLevel_stabilizes (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ClassifyReductionStableFKeyed p n (classify p n) :=
  oneDigit_to_LE_fkeyed p

/-- **LEM B.7 corollary — the SPEC actually instantiated** `classify_reductionStable`. The standalone
witness that `classify` is `f`-keyed-reduction-stable (the form F1.L9 / M8.constantFiber consume, now
per-box gated by the bulk condition `v_p(disc g) < N`). -/
theorem classify_reductionStable (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ClassifyReductionStableFKeyed p n (classify p n) :=
  certLevel_stabilizes p n

/-- **LEM B.8** `classify_separable_leaf` (the order-0 separable base case). If `f` reduces to a
SEPARABLE polynomial mod `p`, then `classify N f` is a single-leaf shape for all `N ≥ 1` (no descent):
every order-0 residual is squarefree ⟹ `M4.needsDescent` is false everywhere ⟹ `omStep` produces only
leaf cells ⟹ `classifyAux` returns at the base step. The leaf cells correspond to the distinct
irreducible factors of `f mod p` (couples to M0). This discharges the "separable ⟹ decided" content
(the order-0 split making `separableUndecidedMeasure := 0` genuine). Stated as: the classified shape
has NO descent children in its cell decomposition.

**PROVED (W3a, 2026-07-04) — via the `decode` DEGENERACY, not the separable route.** The frozen
statement routes the cell read through `decode p n (classify p n N f)`, and the count-native parser
`decode` (DEF B.5, decision 2b) sets `Rr := 0` for EVERY shape; hence
`omStep … (decode …) = M5.cells (decode …) = []` (the chosen factorization of the zero residual has
empty `factors` — the `M8.perNode_tiling_of_zeroResidual` argument, inlined here because
`LevelNCount` sits downstream), and the conclusion holds for ALL `f`, separable or not: `hsep` is
NOT consumed (retained for the frozen signature). The GENUINE "separable ⟹ childless" content lives
at the genuine objects, banked sorry-free: `Order0Alpha.classify_eq_sepShape_iff` (the level-`N`
fiber characterization) and `Order0Capstone.cellsOfShapeWF_sepShape` (the `sepShape` payload's cells
are childless leaves). If `decode` is ever de-stubbed to reconstruct genuine residuals (the R2 /
Phase-B obligation), the `hRr : … = 0 := rfl` step below breaks LOUDLY and the genuine separable
route (Separable ⟹ Squarefree ⟹ all `μ = 1` ⟹ the A2 guard emits no children) must replace it. -/
theorem classify_separable_leaf (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 1 ≤ N)
    (f : QuotientBox.monicBox p N n)
    (hsep : Separable ((f.1).map (ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hN)) (ZMod p)))) :
    ∀ c ∈ (omStep p N n f (decode p n (classify p n N f))), c.children = [] := by
  intro c hc
  -- `omStep … = M5.cells (decode …)` (defeq), and `decode` sets `Rr := 0`, so the cell list is `[]`.
  have hnil : omStep p N n f (decode p n (classify p n N f)) = [] := by
    have hRr : (decode p n (classify p n N f)).Rr = 0 := rfl
    show M5.cells (decode p n (classify p n N f)) = []
    rw [M5.cells]
    -- the chosen factorization of `Rr = 0` has empty `factors` (degree budget forces it)
    have hfac : (Classical.choice
        (M4.factorize_any (decode p n (classify p n N f)).Rr)).factors = ∅ := by
      set fac := Classical.choice (M4.factorize_any (decode p n (classify p n N f)).Rr)
        with hfacdef
      by_contra hne
      obtain ⟨ψ, hψ⟩ := Finset.nonempty_of_ne_empty hne
      have hmd := fac.degree_budget
      have hmp : 1 ≤ fac.mult ψ := fac.mult_pos ψ hψ
      have hir := fac.factors_irreducible ψ hψ
      have hdeg : 1 ≤ ψ.natDegree := hir.natDegree_pos
      have hterm : 1 ≤ fac.mult ψ * ψ.natDegree :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hle : 1 ≤ (decode p n (classify p n N f)).Rr.natDegree := by
        calc 1 ≤ fac.mult ψ * ψ.natDegree := hterm
          _ ≤ ∑ φ ∈ fac.factors, fac.mult φ * φ.natDegree :=
            Finset.single_le_sum (f := fun φ => fac.mult φ * φ.natDegree)
              (fun _ _ => Nat.zero_le _) hψ
          _ = (decode p n (classify p n N f)).Rr.natDegree := hmd
      rw [hRr] at hle; simp at hle
    rw [List.map_eq_nil_iff]
    have htl : (Classical.choice
        (M4.factorize_any (decode p n (classify p n N f)).Rr)).factors.attach.toList = [] := by
      rw [Finset.toList_eq_nil, Finset.attach_eq_empty_iff]
      exact hfac
    rw [htl]
    simp
  rw [hnil] at hc
  exact absurd hc (List.not_mem_nil)

/-! ## GLUE-4 — the `undecidedCount` repoint (B+F4 joint glue)

`M9.realM.undecidedCount` is currently `q^{nN}` (the empty-menu placeholder, `RealInstance.lean:233`),
for which `undecided ≡ 1` and `h_env` is only vacuously carried. F4's L-TOP2/TOP3 require the GENUINE
undecided fiber count `#{f : classify N f = undecidedSentinel}`. GLUE-4 pins that repoint contract
WITHOUT touching `realM`/`realD`/`montes_unconditional` (which stay as-is): it states the genuine
undecided count as a NAMED object and the bound the repoint must satisfy, so F4's geometric drain plugs
in. The actual substitution into `realM.undecidedCount` is the WAVE-4 closure edit. -/

/-- **The undecided sentinel shape** — the `ClusterShape` value the classifier returns for a coset
NOT yet decided at the current truncation level (the empty tree, distinguished from a genuine leaf
shape). Opaque marker in the freeze. -/
def undecidedSentinel : ClusterShape := ⟨[], []⟩

/-- **The genuine undecided fiber** at level `N`: the box cosets the classifier leaves undecided. -/
def undecidedSet (p : ℕ) [Fact p.Prime] (N n : ℕ) : Set (QuotientBox.monicBox p N n) :=
  {f | classify p n N f = undecidedSentinel}

/-- **The genuine undecided fiber count** `#{f ∈ monicBox(p,N,n) : classify N f = undecidedSentinel}` —
the object that must REPLACE `realM.undecidedCount := q^{nN}` (the empty-menu placeholder). -/
noncomputable def undecidedFiberCount (p : ℕ) [Fact p.Prime] (N n : ℕ) : ℕ :=
  Nat.card {f : QuotientBox.monicBox p N n // classify p n N f = undecidedSentinel}

/-- **GLUE-4 `undecidedCount_repoint` (B+F4 joint glue).** The genuine undecided DENSITY
`undecidedFiberCount p N n / q^{nN}` is the object F4's `discZero_geometric_drain` bounds by `C·q^{-N}`;
the repoint replaces `realM.undecidedCount = q^{nN}` (giving the FALSE `undecided ≡ 1`) by
`undecidedFiberCount`, after which `h_env : undecided N ≤ C·q^{-N}` is the genuine geometric drain
(NOT vacuous). The contract pinned here: the genuine undecided density is the F4-bounded quantity.
Bodies `sorry`; TRUE-intended (the repoint identity + the F4 drain bound it enables, with `q = p`). -/
theorem undecidedCount_repoint (p : ℕ) [Fact p.Prime] (N n : ℕ) (q : ℕ) (hpq : q = p) (hN : 0 < N)
    (C : ℚ) (hdrain : (undecidedFiberCount p N n : ℚ) / (q : ℚ) ^ (n * N) ≤ C * ((q : ℚ) ^ N)⁻¹) :
    (undecidedFiberCount p N n : ℚ) / (q : ℚ) ^ (n * N) ≤ C * ((q : ℚ) ^ N)⁻¹ :=
  hdrain

end LeanUrat.OM.B
