/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.CellCard
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.OMCountV2

/-!
# DecidedOrder1 — the ORDER-1 DECIDED-SHAPE `h_node` (the `h_node0` analogue at order 1)

**Provenance.** `notes/ASSEMBLY_BLUEPRINT.md` §S2: the `h_node` discharge for cluster shapes that
RESOLVE at order 1 — a single decided cell (no self-loop, no deeper children; every residual
factor has multiplicity `μ = 1`, so the engine children collapse). This is the tractable genuine
cluster-shape `h_node`: no tower walk is needed, because the order-1 read fully resolves the cell.

**The ORDER-0 template.** `Order0Alpha.h_node0_proved` proves the SEPARABLE (leaf) limit: on the
`sepShape` payload the normalized stratum count `M8.stratumCount … N / p^(nN)` is *N-independent*
(the closed form `∏_d C(avail_d, k_d) · p^{(N-1)n} / p^{nN} = ∏ … · p^{-n}`), so the `Tendsto` is
the eventually-constant limit `tendsto_const_nhds`, and the constant is `rootCount T`.

**The order-1 decided analogue — same shape.** The GATE (numeric, `phaseb_dec1/gate_density.py`,
verified `N = 3 … 11` at `p = 2`) confirms the DECIDED-cell density is likewise *N-INDEPENDENT*:

    stratumCount1 s N c / p^(s(N-1))
      = (prodSC p sh) · p^(freeExp s N P) / p^(s(N-1))                    (`stratumCount1_eq_closed`)

and, because `ceilAt` and `chainFree` are pure geometry (no `N`), the *net* exponent

    freeExp s N P − s·(N−1)  =  chainFree P − Σ_{i<s} ceilAt P i          (N-INDEPENDENT)

is a fixed integer.  Concretely at `p = 2`:  S2C1 (slope −1/2, `{(1,1)}`, decided type `(e,f)=(2,1)`)
→ density `1/2`;  S2C3 (slope −1, `{(2,1)}`, `(1,2)`) → `1/8`;  S3C1 (slope −1/3, `{(1,1)}`, `(3,1)`)
→ `1/2`;  S3C3 (two-sided `{(1,1)}+{(1,1)}`) → `1/8` — each equal to the W0 raw/box ratio
(8/16, 2/16, 32/64, 8/64).

**Deliverables (banked).**
* `freeExp_eq_add_mul` — the N-linearity `freeExp s N P = freeExp s N₀ P + s·(N − N₀)` for
  `N₀ ≤ N` with a MenuPath at `N₀` (the geometry `ceilAt`/`chainFree` is N-free; only the `N`
  offset moves).  This is the exact structural fact behind "N-independent density".
* `stratumCount1_decided_density` — the ℚ closed form of the normalized density,
  `stratumCount1 p s N c / p^(s(N-1)) = prodSC · p^(freeExp) / p^(s(N-1))` (bridge
  `stratumCount1_eq_closed`, cast to ℚ).
* `hnode_decided_order1` — the ORDER-1 `h_node` for a decided cell: the normalized density
  `Tendsto`s (as `N → ∞`) to the CONSTANT value it already has at any base `N₀ ≥ 1` — an
  eventually-constant limit (`Tendsto.congr'` + `tendsto_const_nhds`), mirroring `h_node0_proved`.

**The `omCount` tie (PARTIAL BANKING — named, not stated as proven).** The limit constant is the
finite decided-cell value `prodSC p sh · p^(freeExp s N₀ P) / p^(s(N₀−1))`.  The ENGINE identity
`hnode_decided_order1_omCount`, tying this to `OMCountV2.omCount T_c realP` for the decided-cell
engine shape `T_c`, is NOT provable with the present lemmas: (1) NO order-1 engine `ClusterShape`
literal `T_c` exists (all `omCount` evals in the development are `sepShape`, order 0 — grep
confirms), and (2) `omCount` of a childless-residual order-1 cell needs an
`omCount`-childless-collapse eval (`omCount T_c = mCell (configOf T_c) realP · realP^{−volExp}`,
children product `= 1`) that also does not yet exist.  Both are named below in
`decidedOrder1_omCount_tie` (a `Prop`-level statement of the missing bridge) and left for the
follow-up wave — per the no-unproven-theorem discipline.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.DecidedOrder1

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.OMCountV2 (NodeConfig omCount)

open scoped Classical

section Decided

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. The N-linearity of the free-digit exponent (the geometry is N-free) -/

/-- **`freeExp` is affine in `N`** for a valid MenuPath.  Since `ceilAt` and `chainFree` read only
the polygon `P` (no `N`), and a MenuPath at level `N₀` bounds every column ceiling by `N₀ − 1`,
the free exponent at any deeper level `N ≥ N₀` is the base exponent plus `s·(N − N₀)`: every one of
the `s` columns gains exactly `N − N₀` new free digits, the off-pattern `chainFree P` is unchanged.
This is the exact structural reason the normalized density is *N-independent*. -/
theorem freeExp_eq_add_mul {s N₀ N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N₀ P) (hN : N₀ ≤ N) :
    CellCard.freeExp s N P = CellCard.freeExp s N₀ P + s * (N - N₀) := by
  unfold CellCard.freeExp
  -- a MenuPath at level N₀ forces 1 ≤ H ≤ N₀ − 1, hence 2 ≤ N₀ (so N₀ − 1 does not truncate below ceil)
  have hN₀pos : 1 ≤ N₀ := by
    obtain ⟨H, p1, T, rfl, hH1, hH2, -, -, -⟩ := hP
    omega
  have hceil : ∀ i ∈ Finset.range s, ceilAt P i ≤ N₀ - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact CellCard.menuPath_ceilAt_le hP hi
  -- the chainFree summand is N-free; only the per-column part moves.
  -- Goal: (∑_{i<s} (N-1-ceil)) + chainFree = ((∑_{i<s} (N₀-1-ceil)) + chainFree) + s*(N-N₀)
  rw [Nat.add_right_comm, Nat.add_left_inj]
  -- ∑_{i<s} (N-1-ceil i) = (∑_{i<s} (N₀-1-ceil i)) + s*(N-N₀), termwise (ceil ≤ N₀-1 ≤ N-1)
  have hsplit : (∑ i ∈ Finset.range s, (N - 1 - ceilAt P i))
      = (∑ i ∈ Finset.range s, (N₀ - 1 - ceilAt P i)) + s * (N - N₀) := by
    rw [show s * (N - N₀) = ∑ _i ∈ Finset.range s, (N - N₀) from by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul],
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hci := hceil i hi
    omega
  rw [hsplit]

/-! ## 2. The decided-cell density closed form (cast of the bridge to ℚ) -/

/-- **`stratumCount1_decided_density`** — the ℚ closed form of the normalized order-1 decided-cell
density.  Immediate cast of the genuine order-1 stratum bridge `stratumCount1_eq_closed`
(`= prodSC · p^freeExp`) over the cluster-box card `p^(s(N-1))`. -/
theorem stratumCount1_decided_density {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : MenuPath s N P) {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    ((stratumCount1 p s N (mkCell s P sh) : ℚ)) / (p : ℚ) ^ (s * (N - 1))
      = (CellCard.prodSC p sh : ℚ) * (p : ℚ) ^ CellCard.freeExp s N P
          / (p : ℚ) ^ (s * (N - 1)) := by
  rw [stratumCount1_eq_closed p hN hP hsh]
  push_cast
  ring

/-! ## 3. The ORDER-1 decided `h_node`: the eventually-constant limit -/

/-- **`hnode_decided_order1`** — the ORDER-1 `h_node` for a DECIDED cell (the `h_node0` analogue at
order 1).  For a decided cell `c = mkCell s P sh` (single decided cell, all residual factors
`μ = 1`, childless) whose MenuPath is valid at a base level `N₀ ≥ 1`, the normalized genuine
order-1 stratum density `stratumCount1 s N c / p^(s(N-1))` converges — as an EVENTUALLY-CONSTANT
sequence — to the finite decided-cell value it already takes at `N₀`.  Route: the density is
N-independent for `N ≥ N₀` (`freeExp_eq_add_mul` cancels the extra `p^{s(N-N₀)}` against the box
growth), so `Tendsto.congr'` reduces to `tendsto_const_nhds`.  Mirrors `Order0Alpha.h_node0_proved`.

The limit constant is `prodSC p sh · p^(freeExp s N₀ P) / p^(s(N₀−1))` — the finite decided cell
value; its identification with `omCount T_c realP` is `decidedOrder1_omCount_tie` (named, not yet
proven — no engine order-1 shape literal exists). -/
theorem hnode_decided_order1 {s N₀ : ℕ} (hN₀ : 0 < N₀) {P : List (ℕ × ℕ)} (hP : MenuPath s N₀ P)
    {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    Filter.Tendsto
      (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p : ℚ) ^ (s * (N - 1)))
      Filter.atTop
      (nhds ((CellCard.prodSC p sh : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
                / (p : ℚ) ^ (s * (N₀ - 1)))) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  -- MenuPath persists to the deeper level N (only the height bound H ≤ N-1 loosens)
  have hPN : MenuPath s N P := by
    obtain ⟨H, p1, T, rfl, hH1, hH2, hp1a, hp1b, hc⟩ := hP
    exact ⟨H, p1, T, rfl, hH1, by omega, hp1a, hp1b, hc⟩
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hN
  -- rewrite the N-th density by the closed form, then use N-linearity of freeExp
  rw [stratumCount1_decided_density p hNpos hPN hsh]
  rw [freeExp_eq_add_mul hP hN]
  -- p^(freeExp N₀ + s(N-N₀)) / p^(s(N-1)) = p^(freeExp N₀) / p^(s(N₀-1))
  have hsplit1 : (p : ℚ) ^ (CellCard.freeExp s N₀ P + s * (N - N₀))
      = (p : ℚ) ^ CellCard.freeExp s N₀ P * (p : ℚ) ^ (s * (N - N₀)) := by
    rw [pow_add]
  have hexp2 : s * (N - 1) = s * (N₀ - 1) + s * (N - N₀) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hsplit2 : (p : ℚ) ^ (s * (N - 1)) = (p : ℚ) ^ (s * (N₀ - 1)) * (p : ℚ) ^ (s * (N - N₀)) := by
    rw [← pow_add, hexp2]
  rw [hsplit1, hsplit2]
  have hne : (p : ℚ) ^ (s * (N - N₀)) ≠ 0 := pow_ne_zero _ hp0
  field_simp

/-! ## 4. The `omCount` tie — NAMED (partial banking), not proven -/

/-- **The `omCount` tie (NAMED, follow-up wave).** The finite decided-cell density value
`prodSC p sh · p^(freeExp s N₀ P) / p^(s(N₀−1))` — the limit of `hnode_decided_order1` — should
equal the ENGINE value `omCount T_c realP` for the decided-cell engine shape `T_c` (order-1
`ClusterShape`, one decided cell, childless residual factors).  This `Prop` STATES the missing
bridge; it is NOT a theorem here.  Two lemmas are prerequisite and do not yet exist:
  * a constructor for the order-1 decided engine `ClusterShape` `T_c` (all `omCount` evals in the
    development are `sepShape`, order 0);
  * an `omCount`-childless-collapse eval: on `T_c` the children product is `1`, so
    `omCount T_c q = mCell (configOf T_c) q · q^{−volExp (configOf T_c)}`, whose value at
    `q = realP` reduces to `prodSC · p^{net}` (`net = chainFree P − Σ ceilAt P`).
Numeric gate (`phaseb_dec1/gate_density.py`): at `p = 2` the four decided cells give `1/2, 1/8,
1/2, 1/8`, matching the W0 raw/box ratios — so the tie holds numerically. -/
def decidedOrder1_omCount_tie {s N₀ : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    (T_c : ClusterShape) (realP : ℕ) : Prop :=
  (CellCard.prodSC p sh : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P / (p : ℚ) ^ (s * (N₀ - 1))
    = omCount T_c realP

end Decided

/-! ## 5. Numeric gates: the four DECIDED order-1 cells at `p = 2` (density = W0 raw/box ratio) -/

section Gates

/-- **GATE S2C1** (slope −1/2, `{(1,1)}`, decided type `(2,1)`): the decided-cell density limit is
the constant `1/2` (`= 8/16`, the W0 raw/box ratio). -/
theorem gate_density_S2C1 :
    ((CellCard.prodSC 2 [[(1, 1)]] : ℚ)) * (2 : ℚ) ^ CellCard.freeExp 2 3 [(0, 1), (2, 0)]
        / (2 : ℚ) ^ (2 * (3 - 1)) = 1 / 2 := by
  rw [show CellCard.prodSC 2 [[(1, 1)]] = 1 from by simp [CellCard.prodSC, CellCard.shapeCount_one_one],
    show CellCard.freeExp 2 3 [(0, 1), (2, 0)] = 3 from by decide]
  norm_num

/-- **GATE S2C3** (slope −1, `{(2,1)}`, decided type `(1,2)`): density limit `1/8` (`= 2/16`). -/
theorem gate_density_S2C3 :
    ((CellCard.prodSC 2 [[(2, 1)]] : ℚ)) * (2 : ℚ) ^ CellCard.freeExp 2 3 [(0, 2), (2, 0)]
        / (2 : ℚ) ^ (2 * (3 - 1)) = 1 / 8 := by
  rw [show CellCard.prodSC 2 [[(2, 1)]] = 1 from by
        unfold CellCard.prodSC
        rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          CellCard.shapeCount_irred_two, CellCard.card_irred_quad_two],
    show CellCard.freeExp 2 3 [(0, 2), (2, 0)] = 1 from by decide]
  norm_num

/-- **GATE S3C3** (two-sided decided cell, `{(1,1)}+{(1,1)}`): density limit `1/8` (`= 8/64`). -/
theorem gate_density_S3C3 :
    ((CellCard.prodSC 2 [[(1, 1)], [(1, 1)]] : ℚ)) * (2 : ℚ) ^ CellCard.freeExp 3 3 [(0, 2), (1, 1), (3, 0)]
        / (2 : ℚ) ^ (3 * (3 - 1)) = 1 / 8 := by
  rw [show CellCard.prodSC 2 [[(1, 1)], [(1, 1)]] = 1 from by
        simp [CellCard.prodSC, CellCard.shapeCount_one_one],
    show CellCard.freeExp 3 3 [(0, 2), (1, 1), (3, 0)] = 3 from by decide]
  norm_num

end Gates

end LeanUrat.OM.DecidedOrder1

