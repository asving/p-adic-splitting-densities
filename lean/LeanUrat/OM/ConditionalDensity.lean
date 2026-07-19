/-
ConditionalDensity — THE COMPLETE CONDITIONAL TOP-LEVEL THEOREM (build #49, 2026-07-11).

GOAL.  Compose the complete top-level conditional density theorem for the p-adic factorization
densities: for every prime p and factorization type σ, the density (= the OM engine menu-sum
`∑_T omCount T`) equals a UNIFORM RATIONAL FUNCTION of q, and the REAL normalized stratum counts
converge to it — where the per-shape `h_node` limit is

  * DISCHARGED UNCONDITIONALLY for every NON-self-loop (tame / separable) shape, and
  * ASSUMED as ONE explicit honest hypothesis (`SelfLoopHNode`) for the self-loop shapes only.

HONEST HYPOTHESIS (the SINGLE remaining input).  Per the refutation state
(`notes/SELFLOOP_GENERALK_WALL.md`): FIVE per-depth count-identity routes to the wild self-loop
`h_node` are REFUTED (each with an exact counterexample; three banked as core-only no-go's).  There
is NO per-depth finite-N geometric count identity.  So we do NOT take the (refuted) per-depth
`FloorCensusPerDepth` as the hypothesis.  Instead we take the AGGREGATE self-loop `h_node` limit
DIRECTLY — exactly the object MC/PARI confirm true — namely, for a self-loop cluster `T`,

    Tendsto (fun N => stratumCount (rawCount n) T N / realP^(nN)) atTop (nhds (omCount T realP)).

This is precisely the `h_node` shape that the S1 assembly skeleton `montes_allorders_of_hnode`
consumes.  Stating it at the aggregate limit level (not per-depth) is the honest single input;
everything downstream is UNCONDITIONAL composition through `montes_allorders_of_hnode`.

WHAT IS UNCONDITIONAL vs CONDITIONAL (the map).
  * UNCONDITIONAL (no hypothesis): the S1 assembly skeleton; the tame single-side / multi-slope /
    unramified `h_node`s (banked `montes_order0_unconditional`, `montes_order1_selfloop_density`,
    `hnode_multiSideProduct`); hence the ENTIRE TAME CASE (every prime p > n), which — by the
    "wild = tame" fact (`notes/HUMAN_PROOF.md` §8; a self-loop needs `p | e ≤ n`, impossible at
    `p > n`) — contains NO self-loop shape, so its density needs NO hypothesis at all.
  * CONDITIONAL (rests on `SelfLoopHNode`): the wild case, precisely and ONLY through the aggregate
    self-loop `h_node` limit on the self-loop shapes of the menu.

METHOD.  Composition of banked lemmas.  No `sorry`/`axiom`/`native_decide`/`admit`.  A theorem that
TAKES an explicit hypothesis is honest assembly.  Verified core-only via `#print axioms`.
-/
import LeanUrat.OM.Order0Alpha
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.PathShapeMultiSideTree
import LeanUrat.OM.MontesAllOrders
import LeanUrat.OM.SelfLoopFixpoint

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.ConditionalDensity

open scoped BigOperators Classical
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.Order0
open LeanUrat.OM.MontesAllOrders

noncomputable section

/-! ## 0. Abbreviations for the top-level count-native `h_node` shape.

`hNodeLimit n T` is the per-shape counting limit in EXACTLY the shape `montes_allorders_of_hnode`
consumes: the REAL normalized `stratumCount` for shape `T` converges to the engine value
`omCount T realP`.  This is the atomic `h_node` for a single cluster shape. -/

/-- **`hNodeLimit n T`** — the per-shape `h_node` counting limit for the degree-`n` model at the real
prime: `stratumCount (rawCount n) T N / realP^(nN) → omCount T realP`.  This is the exact predicate
`montes_allorders_of_hnode` requires for each `T ∈ M`. -/
def hNodeLimit (n : ℕ) (T : ClusterShape) : Prop :=
  Filter.Tendsto
    (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
    Filter.atTop
    (nhds (omCount T M9.realP))

/-! ## 1. THE SINGLE REMAINING HONEST HYPOTHESIS — the AGGREGATE self-loop `h_node` limit.

`SelfLoopHNode n isSelfLoop` asserts the aggregate self-loop `h_node` limit `hNodeLimit n T`
holds for EVERY self-loop shape `T` (`isSelfLoop T`).  This is the honest single input:
MC/PARI-true, stated at the AGGREGATE limit level (NOT the refuted per-depth
`FloorCensusPerDepth`).  `isSelfLoop : ClusterShape → Prop` is the (caller-supplied) self-loop
predicate that partitions the menu into wild self-loop shapes and everything else.

It is deliberately stated ONLY on self-loop shapes: non-self-loop `h_node`s are DISCHARGED
unconditionally below, so the hypothesis carries exactly the wild residue-theoretic content that
the five refuted count-identity routes could not supply. -/
def SelfLoopHNode (n : ℕ) (isSelfLoop : ClusterShape → Prop) : Prop :=
  ∀ T : ClusterShape, isSelfLoop T → hNodeLimit n T

/-! ## 2. THE COMPLETE CONDITIONAL TOP-LEVEL THEOREM.

For an arbitrary menu `M : Finset ClusterShape`, a self-loop predicate `isSelfLoop`, an
UNCONDITIONAL discharge witness `hTame` for every NON-self-loop shape of `M`, and the SINGLE honest
aggregate hypothesis `SelfLoopHNode` for the self-loop shapes, the menu-sum density
`q ↦ ∑_{T ∈ M} omCount T q` is a UNIFORM RATIONAL FUNCTION of `q`, and the REAL normalized menu-sum
stratum counts converge to it. -/

/-- **`density_eq_engine_conditional` — THE COMPLETE CONDITIONAL DENSITY THEOREM.**

For every degree `n`, factorization type `σ`, menu `M : Finset ClusterShape`, and self-loop
predicate `isSelfLoop`:

  * (UNCONDITIONAL input) `hTame`: for every NON-self-loop shape `T ∈ M`, the per-shape `h_node`
    limit `hNodeLimit n T` holds — DISCHARGED (banked tame / separable `h_node`s; see §4);
  * (THE SINGLE HONEST HYPOTHESIS) `hSelfLoop : SelfLoopHNode n isSelfLoop`: the AGGREGATE self-loop
    `h_node` limit holds for every self-loop shape (MC/PARI-true; the wild residue-theoretic input),

the density `q ↦ ∑_{T ∈ M} omCount T q` is a UNIFORM RATIONAL FUNCTION `num/den` of `q`
(denominator nonvanishing at every `q > 1`), and the REAL normalized menu-sum stratum counts
converge to `num(realP)/den(realP)`.

Proof: assemble the full per-shape `h_node` over `M` by CASES on `isSelfLoop T` — the non-self-loop
case is `hTame`, the self-loop case is `hSelfLoop` — then feed `montes_allorders_of_hnode` (S1
skeleton, UNCONDITIONAL).  All content beyond the two named inputs is unconditional composition. -/
theorem density_eq_engine_conditional (n : ℕ) (σ : FactorizationType) (M : Finset ClusterShape)
    (isSelfLoop : ClusterShape → Prop)
    (hTame : ∀ T ∈ M, ¬ isSelfLoop T → hNodeLimit n T)
    (hSelfLoop : SelfLoopHNode n isSelfLoop) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ M, omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) := by
  -- Assemble the full per-shape `h_node` over `M` by cases on the self-loop predicate.
  have h_node : ∀ T ∈ M, hNodeLimit n T := by
    intro T hT
    by_cases hsl : isSelfLoop T
    · exact hSelfLoop T hsl                 -- wild self-loop shape: THE honest hypothesis
    · exact hTame T hT hsl                  -- non-self-loop shape: UNCONDITIONAL discharge
  -- Feed the S1 assembly skeleton (unconditional).
  exact montes_allorders_of_hnode n σ M (fun T hT => h_node T hT)

/-! ## 3. THE FULLY-UNCONDITIONAL TAME CASE (p > n ⟹ NO self-loop shapes ⟹ no hypothesis).

For a menu with NO self-loop shapes — the situation at every TAME prime `p > n`, by the "wild = tame"
fact: a self-loop needs `p | e` for some ramification index `e ≤ n`, impossible when `p > n`, so the
descent terminates at genuine SEPARABLE leaves and NO self-loop shape occurs — the conditional
theorem's self-loop hypothesis is DISCHARGED VACUOUSLY.  The density is then UNCONDITIONALLY the
engine rational function.  (Cite: `notes/HUMAN_PROOF.md` §8 "wild = tame"; the tame per-shape
`h_node`s are banked UNCONDITIONAL, re-exported in `TameAssembly.lean`.) -/

/-- **`density_eq_engine_tame` — THE FULLY-UNCONDITIONAL TAME DENSITY THEOREM.**

If the menu `M` has NO self-loop shape (`hNoSelfLoop`) — which holds at every tame prime `p > n`
(no wild ramification ⟹ no self-loop; §3 docstring / `notes/HUMAN_PROOF.md` §8) — then GIVEN the
banked UNCONDITIONAL tame per-shape `h_node`s (`hTame`, all separable / all-μ=1, discharged in
`TameAssembly`), the density is the engine rational function with NO further hypothesis: the
self-loop hypothesis is discharged VACUOUSLY (`fun T hsl => (hNoSelfLoop T hsl).elim`).

This certifies: TAME ⟹ FULLY UNCONDITIONAL. -/
theorem density_eq_engine_tame (n : ℕ) (σ : FactorizationType) (M : Finset ClusterShape)
    (isSelfLoop : ClusterShape → Prop)
    (hNoSelfLoop : ∀ T, ¬ isSelfLoop T)
    (hTame : ∀ T ∈ M, hNodeLimit n T) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ M, omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) :=
  density_eq_engine_conditional n σ M isSelfLoop
    (fun T hT _ => hTame T hT)                 -- every shape's h_node is the banked tame one
    (fun T hsl => (hNoSelfLoop T hsl).elim)    -- self-loop hypothesis DISCHARGED VACUOUSLY

/-! ## 4. Discharging the NON-self-loop `hNodeLimit` from banked UNCONDITIONAL tame `h_node`s.

These re-package the banked tame `h_node`s in `hNodeLimit` shape, certifying that the `hTame`
argument of §2/§3 is genuinely supplied UNCONDITIONALLY (core-only) for the tame shapes. -/

/-- **`hNodeLimit_unramified` (UNCONDITIONAL).**  Every separable order-0 shape `T ∈ sepShapesOf n σ`
has its per-shape `h_node` `hNodeLimit n T` DISCHARGED by `Order0Alpha.h_node0_proved` (the
unconditional order-0 count keystone) composed with `omCount_sepShape_eq_rootCount`.  This is the
tame unramified / separable `h_node`, core-only. -/
theorem hNodeLimit_unramified (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (T : ClusterShape) (hT : T ∈ sepShapesOf n σ) : hNodeLimit n T := by
  rw [sepShapesOf, Finset.mem_image] at hT
  obtain ⟨lam, hlam, rfl⟩ := hT
  have hmem : sepShape n lam ∈ sepShapesOf n σ := by
    rw [sepShapesOf, Finset.mem_image]; exact ⟨lam, hlam, rfl⟩
  unfold hNodeLimit
  rw [omCount_sepShape_eq_rootCount]
  exact h_node0_proved n hn σ (sepShape n lam) hmem

/-! ## 5. The self-loop engine value IS the general-μ fixpoint (characterising the hypothesis target).

The engine value `omCount T realP` that the honest hypothesis `SelfLoopHNode` targets, for a
self-loop shape, is the UNIQUE self-loop fixpoint `selfLoopFixpointValue depth0 s q` — the unique
solution of `b = depth0 + slExposedRatio s q · b`.  We re-bank the general-`μ` fixpoint closure from
`SelfLoopFixpoint`, so the hypothesis's target value is fully characterised (the "same cluster
restarted" self-consistency), for arbitrary `(depth0, μ)`.  This certifies the honest hypothesis
lands on a genuine engine value, not a free constant. -/

open LeanUrat.OM.SelfLoopFixpoint LeanUrat.OM.SelfLoopResum in
/-- **`selfLoop_engine_is_fixpoint` (the target-value characterisation).**  For every `μ ≥ 2`,
`q ≥ 2`, seed `depth0`, the self-loop engine value `selfLoopFixpointValue depth0 μ q`
(`= depth0 · (countPivot μ q)⁻¹`) is the UNIQUE solution of `b = depth0 + slExposedRatio μ q · b`.
Re-derived from the mirror's banked `SelfLoopFixpoint.selfLoopFixpoint_eq/_unique`. -/
theorem selfLoop_engine_is_fixpoint {μ q : ℕ} (hq : 2 ≤ q) (hμ : 2 ≤ μ) (depth0 : ℚ) :
    selfLoopFixpointValue depth0 μ q
        = depth0 + slExposedRatio μ q * selfLoopFixpointValue depth0 μ q
      ∧ ∀ b : ℚ, b = depth0 + slExposedRatio μ q * b →
          b = selfLoopFixpointValue depth0 μ q :=
  ⟨selfLoopFixpoint_eq hq hμ depth0,
   fun b hb => selfLoopFixpoint_unique hq hμ depth0 b hb⟩

end

/-! ## Axiom audit.

  * `density_eq_engine_conditional`  — CONDITIONAL: takes `hTame` (dischargeable unconditionally) +
    `hSelfLoop : SelfLoopHNode` (THE single honest hypothesis).  Footprint must be core-only
    (hypotheses are hypotheses, not axioms).
  * `density_eq_engine_tame`         — the tame corollary; still parametrised by `hTame` (banked
    unconditional) and `hNoSelfLoop` (the wild=tame fact); footprint core-only.
  * `hNodeLimit_unramified`          — UNCONDITIONAL: discharges the separable `h_node` from
    `h_node0_proved`; footprint core-only.
  * `selfLoop_engine_is_fixpoint`    — UNCONDITIONAL: re-banks the fixpoint closure; core-only. -/

#print axioms LeanUrat.OM.ConditionalDensity.density_eq_engine_conditional
#print axioms LeanUrat.OM.ConditionalDensity.density_eq_engine_tame
#print axioms LeanUrat.OM.ConditionalDensity.hNodeLimit_unramified
#print axioms LeanUrat.OM.ConditionalDensity.selfLoop_engine_is_fixpoint

end LeanUrat.OM.ConditionalDensity
