/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.SelfLoopIterate
import LeanUrat.OM.SelfLoopTower
import LeanUrat.OM.DevelopTower
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.Drainage
import LeanUrat.OM.HNode1

/-!
# SelfLoopCensusK — the k-fold self-loop box census (scratch module)

Scratch build for the RECURRING BOTTLENECK (`SelfLoopResum.REMAINING_OBLIGATION` /
`SelfLoopIterate.REMAINING_STEP1`): the uniform-in-`N` box census at every self-loop depth `k`,

    Σ_{c : selfLoopDepthOf c = k} stratumCount1 s N c
      = depth0Census · p^(s(N−1)) · (slBoxRatio s p)^k · p^k.

**What this module lands (general `k`, no `sorry`/`axiom`).**  The genuinely general-`k` object is
the *iterated recenter self-loop chain* and its **census EQUIVALENCE recursion**: the single
`two_level_census` step, layered with an arbitrary chain-continuation predicate, gives a bijection
that reduces the depth-`(k+1)` box census over `monicBox p N (μ*1)` (root-pinned self-loop cell) to
the depth-`k` chain census over the fresh `γ`-coset (`monicBox p N μ`).  This is proved for ALL `k`
here (`census_step_equiv`, `census_chain_card`), sidestepping the `k`-fold recenter-composition by
carrying the whole chain as the `h_node1_single` predicate `Q`.  It IS the "base bridge + one
development step" that route (b) asks for, realized directly on the box (route (a)'s engine, made
`k`-uniform through the predicate).

**What remains open (documented, NOT faked below — see `OPEN_count_evaluation`).**  Turning the
census-equivalence recursion into the *closed geometric count* `depth0 · p^(s(N−1)) · slBoxRatio^k ·
p^k` needs the per-level coset density to be UNIFORM across the `GammaPattern` cosets — i.e. that the
depth-`k` chain census over one `γ`-coset equals `(coset index)⁻¹ ·` the census over the full cluster
box.  That uniformity is precisely the general-`k` obligation's content; both routes (the tower ring
`card_r_level_census` and the direct `two_level_census` iteration) hit the SAME circular point at the
box level, spelled out in detail in `OPEN_count_evaluation`.

Nothing here edits the real project files.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.SelfLoopCensusK

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.SelfLoopTower

noncomputable section

variable (p N μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ) (hN : 0 < N)

/-! ## 1. The iterated recentering endomorphism and the self-loop chain predicate -/

/-- Cast a size-`μ` box element into the `μ*1`-indexed box `recenter'` consumes (`μ*1 = μ`, a
propositional — not definitional — `Nat` identity, hence the explicit `cast`). -/
def boxCast (g : QuotientBox.monicBox p N μ) : QuotientBox.monicBox p N (μ * 1) :=
  cast (congrArg (QuotientBox.monicBox p N) (Nat.mul_one μ).symm) g

/-- One self-loop development step on a size-`μ` box element: recenter (`gpoly ∘ transport`). At
`e = 1` this is an ENDOMORPHISM of `monicBox p N μ` (the "child is a fresh size-`μ` cluster box"
identification), so it can be iterated. -/
def recenterStep (g : QuotientBox.monicBox p N μ) : QuotientBox.monicBox p N μ :=
  recenter' p N μ c hN (boxCast p N μ g)

/-- The `k`-fold iterated recentering. `recenterIter 0 = id`; `recenterIter (k+1) = recenterStep ∘
recenterIter k`. -/
def recenterIter : ℕ → QuotientBox.monicBox p N μ → QuotientBox.monicBox p N μ
  | 0, g => g
  | k + 1, g => recenterStep p N μ c hN (recenterIter k g)

/-- **The depth-`k` self-loop chain predicate.** `g` reads as the self-loop cell at each of its
first `k` iterated recenter levels. `selfLoopChain 0` is vacuous; `selfLoopChain (k+1) g` adds
`classify1 (recenterIter k g) = selfLoopCell`. -/
def selfLoopChain (k : ℕ) (g : QuotientBox.monicBox p N μ) : Prop :=
  ∀ i : ℕ, i < k → classify1 p (recenterIter p N μ c hN i g) = some (Drainage.selfLoopCell μ)

theorem selfLoopChain_zero (g : QuotientBox.monicBox p N μ) : selfLoopChain p N μ c hN 0 g := by
  intro i hi; exact absurd hi (Nat.not_lt_zero i)

/-- The chain-`(k+1)` predicate splits as "level-0 reads self-loop" ∧ "the recentered box has a
depth-`k` chain" — the recursion skeleton `selfLoopChain (k+1) g ↔ classify1 g = SL ∧ selfLoopChain
k (recenterStep g)`. -/
theorem selfLoopChain_succ (k : ℕ) (g : QuotientBox.monicBox p N μ) :
    selfLoopChain p N μ c hN (k + 1) g
      ↔ classify1 p g = some (Drainage.selfLoopCell μ)
        ∧ selfLoopChain p N μ c hN k (recenterStep p N μ c hN g) := by
  unfold selfLoopChain
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (Nat.succ_pos k)
      simpa [recenterIter] using this
    · have := h (i + 1) (Nat.succ_lt_succ hi)
      -- recenterIter (i+1) g = recenterIter i (recenterStep g)
      rwa [recenterIter_step] at this
  · rintro ⟨h0, hrest⟩ i hi
    cases i with
    | zero => simpa [recenterIter] using h0
    | succ j =>
      have hj : j < k := Nat.lt_of_succ_lt_succ hi
      have := hrest j hj
      rwa [recenterIter_step j g]
where
  recenterIter_step : ∀ (i : ℕ) (g : QuotientBox.monicBox p N μ),
      recenterIter p N μ c hN (i + 1) g
        = recenterIter p N μ c hN i (recenterStep p N μ c hN g) := by
    intro i
    induction i with
    | zero => intro g; rfl
    | succ j ih =>
      intro g
      show recenterStep p N μ c hN (recenterIter p N μ c hN (j + 1) g)
        = recenterStep p N μ c hN (recenterIter p N μ c hN j (recenterStep p N μ c hN g))
      rw [ih g]

/-! ## 2. The general-`Q` census equivalence (the `two_level_census` engine, predicate-uniform)

`censusEquivQ` is `SelfLoopTower.towerEquiv` with the fixed verdict `classify1 (recenter' f) = c'`
replaced by an ARBITRARY box predicate `Qbox` on the recentered element.  It is the SAME
`h_node1_single`/`censusEquiv` construction transported through `ringIso`; carrying the whole
self-loop chain as `Qbox` is exactly what makes the census recursion `k`-uniform (no `k`-fold
recenter-composition needed to STATE the reduction). -/

open LeanUrat.OM.HNode1 LeanUrat.OM.RphiRing LeanUrat.OM.RestartEquiv

/-- **The general-`Q` census equivalence.** For any predicate `Qbox` on the size-`μ` box, the
root-pinned self-loop cell fiber conditioned on `Qbox (recenter' f)` is in bijection with the
divisibility-pattern coset conditioned on `Qbox (gpoly γ)`.  (`SelfLoopTower.towerEquiv` is the
special case `Qbox g := classify1 g = c'`.) -/
def censusEquivQ (hμ2 : 2 ≤ μ) (hμN : μ < N) (Qbox : QuotientBox.monicBox p N μ → Prop) :
    {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ Qbox (recenter' p N μ c hN f)}
      ≃ {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ Qbox (gpoly p N μ hN γ)} :=
  (censusEquiv p N 1 μ c hN one_pos hμ2 hμN
      (fun β => Qbox (gpoly p N μ hN (fun j => ringIso p N c (β j))))).trans
    ((Equiv.piCongrRight fun _ => (ringIso p N c).toEquiv).subtypeEquiv fun β =>
      and_congr (pattern_iso p N μ c β) Iff.rfl)

/-- **`census_step_equiv` (the general-`k` census reduction, count form).** For every depth `k`,
the root-pinned self-loop fiber over `monicBox p N (μ*1)` carrying a depth-`k` self-loop CHAIN on
its recentered element has the SAME cardinality as the depth-`k` chain census over the fresh
`γ`-coset (`monicBox p N μ`).  This is `censusEquivQ` at `Qbox := selfLoopChain k`, holding for ALL
`k` at once (the chain rides along as the predicate) — the "base bridge + one development step"
route (b) asks for, realized on the box. -/
theorem census_step_equiv (hμ2 : 2 ≤ μ) (hμN : μ < N) (k : ℕ) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN k (recenter' p N μ c hN f)}
      = Nat.card {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ selfLoopChain p N μ c hN k (gpoly p N μ hN γ)} :=
  Nat.card_congr (censusEquivQ p N μ c hN hμ2 hμN (selfLoopChain p N μ c hN k))

/-- **The base bridge (depth `0`).** At `k = 0` the chain predicate is vacuous, so
`census_step_equiv` collapses to the plain root-pinned restart fiber count
`RestartEquiv.card_restart_fiber` — the depth-0 census `= p^(μ(N−1) − μ(μ+1)/2)` (route (b)'s "base
bridge = tower level-0", here directly on the box).  This anchors the recursion's `k = 0` term. -/
theorem census_base (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN 0 (recenter' p N μ c hN f)}
      = p ^ (μ * (N * 1 - 1) - 1 * μ * (μ + 1) / 2) := by
  have hcong : Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN 0 (recenter' p N μ c hN f)}
      = Nat.card {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f =>
      and_iff_left (selfLoopChain_zero p N μ c hN _))
  rw [hcong, card_restart_fiber p N 1 μ c hN one_pos hμ2 hμN]

/-- **The depth-`1` tie to `two_level_census`.** At `k = 1` the chain census IS the banked
`SelfLoopTower.two_level_census` verdict census at `c' = selfLoopCell μ`: the depth-1 self-loop
census over the box equals the self-loop-conditioned `γ`-coset census.  (`census_step_equiv` at
`k = 1` reproduces `two_level_census` after unfolding `selfLoopChain 1`.) -/
theorem census_depth_one (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN 1 (recenter' p N μ c hN f)}
      = Nat.card {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ classify1 p (gpoly p N μ hN γ) = some (Drainage.selfLoopCell μ)} := by
  rw [census_step_equiv p N μ c hN hμ2 hμN 1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => ?_)
  constructor
  · intro h
    have := h 0 (by norm_num)
    simpa [recenterIter] using this
  · intro h i hi
    interval_cases i
    simpa [recenterIter] using h

end

/-! ## 3. Concrete gate: the depth-0 census at the minimal instance `(p,N,μ) = (2,5,2)` -/

open LeanUrat.OM.RestartEquiv (InCellAt)

/-- **Gate — the depth-0 self-loop census at `(2,5,2)` is `32`.**  `census_base`'s closed form
`p^(μ(N−1) − μ(μ+1)/2) = 2^(2·4 − 3) = 2^5 = 32` = the cluster box `#clusterBox(2,5,2) = 2^8`
divided by the self-loop coset index `2^{s(s+1)/2} = 2^3`.  This anchors the recursion's `k = 0`
term numerically and cross-checks `RestartEquiv.card_restart_fiber` through the chain formulation. -/
theorem gate_census_base_2_5_2 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧ selfLoopChain 2 5 2 1 (by norm_num) 0 (recenter' 2 5 2 1 (by norm_num) f)}
      = 32 := by
  rw [census_base 2 5 2 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ## 4. OPEN — the count-evaluation to the geometric closed form

`OPEN_count_evaluation`.  What `census_step_equiv` (general `k`, PROVED above) delivers is the
bijective reduction

    #{f ∈ box(μ*1) : InCellAt c f ∧ chain_k (recenter' f)}
      = #{γ : GammaPattern γ ∧ chain_k (gpoly γ)}.                              (†)

Iterating (†) unwinds the chain one development level at a time.  What it does NOT yet give is the
CLOSED count

    Σ_{selfLoopDepthOf c = k} stratumCount1 s N c
      = depth0Census · p^(s(N−1)) · (slBoxRatio s p)^k · p^k.                    (‡)

The precise missing lemma (identical for BOTH routes; NOT a "wall", a single named gap):

  UNIFORM COSET DENSITY.  The RHS of (†) counts the depth-`k` chain over ONE `GammaPattern` coset
  (the floors `p^(μ−j+1) ∣ γ_j`, a coset of index `p^{s(s+1)/2} = p^(selfLoopExponent s + 1)` inside
  the cluster box — `HNode1.selfLoop_coset_index` / `Drainage.card_selfLoopFiber_index`).  To turn
  (†) into the per-level factor `slBoxRatio = p^{−s(s+1)/2}` one needs

      #{γ ∈ coset : chain_k (gpoly γ)}  =  p^{−(selfLoopExponent s + 1)} · #{g ∈ clusterBox : chain_k g},

  i.e. that the depth-`k` chain census is UNIFORMLY DISTRIBUTED across the `p^{s(s+1)/2}` cosets of
  the pattern.  Equivalently: the census function `k ↦ #chain_k` is coset-translation invariant.

Why both routes stall here.
 • ROUTE (a) direct iteration:  applying (†) to the RHS again needs `gpoly γ` (a coset
   representative) to be a ROOT-PINNED `InCellAt` element of the NEXT level so `census_step_equiv`
   fires again.  But `gpoly γ` ranges over a coset, and `two_level_census`/`census_step_equiv`
   consume the WHOLE box(μ*1) (all of `InCellAt`), not a single coset — so re-applying (†) counts
   the chain over the full box at the next level, which equals the coset census ONLY under the
   uniform-coset-density hypothesis above.  The recursion `#chain_{k+1} = p^{−B}·#chain_k` is
   exactly that hypothesis; it is not derivable from (†) alone.
 • ROUTE (b) tower ring:  `DevelopTower.card_r_level_census` counts the level-`r` FRESH-CLUSTER
   restart fiber (`InCellTower` = `SlotPatternAbstract`, i.e. EVERY level passes the fresh-cluster
   FLOORS), over the abstract tower ring `towerLevel … r`.  That is a strictly LARGER count than the
   self-loop-CONDITIONED chain census (which additionally requires `classify1 = selfLoopCell`, the
   repeated-residual VERDICT, at each level — a proper sub-event of "passes the floors").  So
   `card_r_level_census` gives the cluster-box tower geometric `∏_j∏_i ballCount(dexp …)`, NOT (‡)'s
   self-loop-verdict census; bridging the two is again the uniform-coset-density identity (the
   verdict cuts each coset to the same fraction).  The tower ring closes the FLOOR count for all `k`
   but not the VERDICT count.

Consequently (‡) reduces to the single lemma `UNIFORM COSET DENSITY`.  At `p = 2` (the minimal
instance) the `(p−1)` root factor is invisible and the coset density is a clean power of `2`, which
is why `SelfLoopTower.gate_iterated_selfLoop` discharges `k ≤ 2` concretely by `decide`; the general
`k` needs the translation-invariance of `#chain_k` under the pattern coset, stated above.  This
report — the reduction of the general-`k` obligation to `UNIFORM COSET DENSITY`, with both routes
shown to meet at it — is the deliverable of this round.  It is NOT proved here; no `sorry`/`axiom`
stands in for it. -/

end LeanUrat.OM.SelfLoopCensusK
