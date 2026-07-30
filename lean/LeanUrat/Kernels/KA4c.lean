/-
Kernels/KA4c — BP4-c7 E-phase skeleton for unit KA4c [ATTEMPT]: the ROUTE-E0
seam — the note-shaped theorem "X.3-drain ⟹ per-pool escape" (the CL-4
consumer edge, MOVES 12180-12187) (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2,
§3.A ROUTE 2 + §4 KA4c + R10; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

⚑ INTERFACE FLAG + THE PRE-DECLARED FALLBACK (R10): the blueprint warns the
drain embedding may need CL-5's identification (the nine inputs) "in a form no
corpus yet types", and pre-declares the fallback: the NAMED identification
hypothesis.  Per the campaign rule "do not let a prover improvise the
identification", this file TYPES that identification UP FRONT as the
structure `DrainIdent` below; the prover's attempt is to CONSTRUCT a
`DrainIdent` instance at the real pool from the SeriesData/XCtx vocabulary —
if that stalls, the sharpened obstruction record documents which field
resists and `DrainIdent` stays a named hypothesis (deliverable either way).

RECORDED RESOLUTIONS (statement transcription):
· "BlockDrain derived from a SeriesData/XCtx-level a.e.-termination
  hypothesis at the pool": the a.e.-termination hypothesis is typed as the
  two null legs of X.3's route — `frac (InfTree C) = 0` (the route's own (a)
  leg) and `frac (⋃ i, nsFiber i) = 0` (the (ns-null) leg, fed from
  `NsNullP` through the countable-union glue `ka4c_nsFiberUnion_null`).
· "BlockDrain's μ is the still-in-block conditional mass": typed as the
  `DrainIdent` fields — `stillIn τ k` the still-in-block-after-k event of
  the pool entered at state τ; `mass_eq` the NORMALIZED conditional-mass
  identification frac(stillIn τ k) = frac(stillIn τ 0) · blockMass A k τ
  (`entry_pos` makes the normalization well-posed); `neverExit_subset` the
  blueprint's "the never-exit event embeds in InfTree ∪ nsFibers" verbatim.
· `mass_tendsto` (content along the nested family) mirrors the ratified
  XCtx field genre `frac_inter_tendsto` (MovesX/Defs.lean) — the box content
  has no general countable additivity, so the monotone-convergence law along
  THIS family is part of the identification, not derivable at the interface.

deps: KA4b (`escape_of_drain`, Kernels/E0Route.lean — built, sorried) +
MovesX.XCtx (MovesX/Defs.lean).  GATE NOTE: no CM gate is assigned to KA4c;
its risk R10 is handled by the pre-typed fallback above.
Consumers: the CL-4 X.3 ⟹ E0 edge (makes E0's X.3-conditionality a
machine-checked implication at the identified kernel; the δ > 1 pools
transport per [2r] through the sibling unit KA8).

Build: cd lean && lake build LeanUrat.Kernels.KA4c
-/
import LeanUrat.Kernels.E0Route
import LeanUrat.MovesX.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Matrix

/-! ## The typed identification (⚑ — the named CL-5-genre hypothesis, R10) -/

/-- KA4c (⚑ the NAMED identification hypothesis, pre-typed per R10): the
process-to-kernel identification tying the ℚ-matrix mass functional
`blockMass A` (Kernels/E0Route.lean, KA4a) to the XCtx-level still-in-block
events at one pool.

Fields: `stillIn τ k` = the still-in-block-after-k event entered at active
state τ; `nested` (one more step only shrinks it); `entry_pos` (the entry
event has positive content — the conditional normalization is well-posed);
`mass_eq` (THE identification: blockMass is the still-in-block NORMALIZED
conditional mass — the semantic statement KA4a deliberately left out of the
abstract interface); `neverExit_subset` (the never-exit event embeds in
InfTree ∪ nsFibers — blueprint §3.A ROUTE 2 verbatim); `mass_tendsto` (box
content converges along the nested family — the `frac_inter_tendsto` genre).

The prover's ATTEMPT is to construct this from SeriesData/XCtx at the real
pool; fallback (pre-declared): it stays a named hypothesis + obstruction
record. -/
structure DrainIdent (n p : ℕ) [Fact p.Prime] (C : MovesX.XCtx n p)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) where
  stillIn : ι → ℕ → Set (MovesX.MonicBox n p)
  nested : ∀ τ k, stillIn τ (k + 1) ⊆ stillIn τ k
  entry_pos : ∀ τ, 0 < C.frac (stillIn τ 0)
  mass_eq : ∀ τ k,
    (C.frac (stillIn τ k) : ℝ) = (C.frac (stillIn τ 0) : ℝ) * blockMass A k τ
  neverExit_subset : ∀ τ,
    (⋂ k, stillIn τ k) ⊆ MovesX.InfTree C ∪ (⋃ i, C.nsFiber i)
  mass_tendsto : ∀ τ,
    Filter.Tendsto (fun k => C.frac (stillIn τ k)) Filter.atTop
      (nhds (C.frac (⋂ k, stillIn τ k)))

/-! ## The countable-union glue (NsNullP feeds the ns leg) -/

/-- KA4c (glue): the ns-fiber union is null when every fiber is (the form
`NsNullP` delivers per prime).  deps: XCtx's `nsCountable` +
`frac_iUnion_null` + `frac_mono`.  Sketch: `Countable nsIdx` gives an
ℕ-indexed surjection (or the index is empty); reindex the union and apply
`frac_iUnion_null`; `frac_mono` + `frac_nonneg` close the comparison. -/
theorem ka4c_nsFiberUnion_null {n p : ℕ} [Fact p.Prime] (C : MovesX.XCtx n p)
    (hnull : ∀ i, C.frac (C.nsFiber i) = 0) :
    C.frac (⋃ i, C.nsFiber i) = 0 := by
  haveI : Countable C.nsIdx := C.nsCountable
  rcases isEmpty_or_nonempty C.nsIdx with hE | hNE
  · /- ⚑ BLOCKED CORNER (sharpened obstruction record, owner: BP4 orchestrator).
    With `nsIdx` EMPTY the union is `∅` and the goal is `frac ∅ = 0` from NO
    hypotheses (`hnull` is vacuous) — underivable at the XCtx interface: the
    frac laws (univ/nonneg/mono/union_le/iUnion_null/inter_tendsto) all admit
    the countermodel `frac ≡ 1` (iUnion_null vacuous since no set has frac 0),
    whose only reality-tie is `vdisc_le_tail` at the degenerate n.  The corpus
    precedent (XG3.lean:31) derives `frac ∅ = 0` by `frac_mono` into the null
    `discZero` via XF10's `discZeroNull` — which REQUIRES `2 ≤ n`, a hypothesis
    this fenced statement does not carry.  Missing law, either of:
    (i) a `frac_empty : frac ∅ = 0` XCtx field / derived lemma, or
    (ii) `2 ≤ n` on this statement (then import XF10 and anchor on discZero), or
    (iii) `Nonempty C.nsIdx` on this statement.
    The consumers are UNAFFECTED: `blockDrain_of_drainIdent` takes the union
    nullity as a hypothesis, and `escape_of_x3drain` (below) inlines the glue
    anchored on its own null `InfTree` leg — both fully proved. -/
    sorry
  · obtain ⟨e, he⟩ : ∃ e : ℕ → C.nsIdx, Function.Surjective e :=
      exists_surjective_nat _
    have hunion : (⋃ i, C.nsFiber i) = ⋃ k, C.nsFiber (e k) :=
      (he.iUnion_comp _).symm
    rw [hunion]
    exact C.frac_iUnion_null _ (fun k => hnull (e k))

/-! ## KA4c — the seam theorems -/

/-- KA4c (the drain leg): the identification + the a.e.-termination null legs
⟹ BLOCK DRAIN at the pool.  deps: `DrainIdent`, KA4a lemmas.  Sketch: fix τ;
`frac (⋂ k, stillIn τ k) = 0` from `neverExit_subset` + `frac_mono` +
`frac_union_le` + the two null hypotheses + `frac_nonneg`; `mass_tendsto`
then sends frac (stillIn τ k) → 0 in ℚ; cast along `Rat.cast : ℚ → ℝ`
(continuous/inducing), divide by the positive entry content via `mass_eq` —
blockMass A k τ → 0; blockMass ≥ 0 (from `mass_eq` + `frac_nonneg` +
`entry_pos`), so the ℝ-ciInf is 0 (`ciInf` of a nonneg sequence tending
to 0). -/
theorem blockDrain_of_drainIdent {n p : ℕ} [Fact p.Prime]
    {C : MovesX.XCtx n p} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (ID : DrainIdent n p C A)
    (hInf : C.frac (MovesX.InfTree C) = 0)
    (hns : C.frac (⋃ i, C.nsFiber i) = 0) :
    BlockDrain A := by
  intro τ
  -- The never-exit event is null: embed in `InfTree ∪ ⋃ nsFiber` and squeeze.
  have hnull : C.frac (⋂ k, ID.stillIn τ k) = 0 := by
    refine le_antisymm ?_ (C.frac_nonneg _)
    calc C.frac (⋂ k, ID.stillIn τ k)
        ≤ C.frac (MovesX.InfTree C ∪ ⋃ i, C.nsFiber i) :=
          C.frac_mono _ _ (ID.neverExit_subset τ)
      _ ≤ C.frac (MovesX.InfTree C) + C.frac (⋃ i, C.nsFiber i) :=
          C.frac_union_le _ _
      _ = 0 := by rw [hInf, hns]; ring
  -- The ℚ-valued still-in content tends to 0 along the nested family.
  have htend : Filter.Tendsto (fun k => C.frac (ID.stillIn τ k))
      Filter.atTop (nhds (0 : ℚ)) := by
    have h := ID.mass_tendsto τ
    rwa [hnull] at h
  -- Cast to ℝ along the continuous `Rat.cast`.
  have htendR : Filter.Tendsto (fun k => (C.frac (ID.stillIn τ k) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    have h := (Rat.continuous_coe_real.tendsto (0 : ℚ)).comp htend
    simpa [Function.comp_def] using h
  -- Divide by the positive entry content via `mass_eq`.
  have hcpos : (0 : ℝ) < (C.frac (ID.stillIn τ 0) : ℝ) := by
    exact_mod_cast ID.entry_pos τ
  have hbm : Filter.Tendsto (fun k => blockMass A k τ) Filter.atTop
      (nhds (0 : ℝ)) := by
    have h := htendR.const_mul ((C.frac (ID.stillIn τ 0) : ℝ))⁻¹
    rw [mul_zero] at h
    refine h.congr (fun k => ?_)
    rw [ID.mass_eq τ k, inv_mul_cancel_left₀ hcpos.ne']
  -- blockMass is nonneg (mass_eq + frac_nonneg + entry_pos).
  have hbmnn : ∀ k, (0 : ℝ) ≤ blockMass A k τ := by
    intro k
    have h0 : (0 : ℝ) ≤ (C.frac (ID.stillIn τ 0) : ℝ) * blockMass A k τ := by
      rw [← ID.mass_eq τ k]
      exact_mod_cast C.frac_nonneg _
    nlinarith [hcpos, h0]
  -- The ℝ-ciInf of a nonneg sequence tending to 0 is 0.
  refine le_antisymm ?_ (le_ciInf hbmnn)
  have hbdd : BddBelow (Set.range fun k => blockMass A k τ) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact hbmnn k
  exact ge_of_tendsto' hbm (fun k => ciInf_le hbdd k)

/-- KA4c (THE note-shaped seam, the CL-4 consumer edge — "X.3-drain ⟹
per-pool escape", MOVES 12180-12187): at any prime p and any pool matrix A
identified with the XCtx process by a `DrainIdent`, X.3's two null legs
(InfTree null — the route's own (a) leg; ns-null — `NsNullP`, unit KE1's
target) force ESCAPE(E0) at the pool.  deps: `blockDrain_of_drainIdent`,
`ka4c_nsFiberUnion_null`, KA4b (`escape_of_drain`).  Sketch: instantiate
`NsNullP` at p, glue the union, drain, then KA4b with nonneg +
substochastic.  This machine-checks E0's X.3-conditionality at the
identified kernel; δ > 1 pools transport per [2r] via the sibling KA8. -/
theorem escape_of_x3drain {n : ℕ} (X : MovesX.XFamily n) (p : ℕ)
    [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (ID : DrainIdent n p (X.ctx p) A)
    (hnn : ∀ i j, 0 ≤ A i j) (hsub : SubStochastic A)
    (hInf : (X.ctx p).frac (MovesX.InfTree (X.ctx p)) = 0)
    (hns : MovesX.NsNullP n X) :
    MovesS.EscapeE0 A := by
  -- The ns-union is null: Option-reindex the countable union, anchoring the
  -- `none` bucket on the NULL InfTree leg (dodges the `frac ∅` corner — the
  -- Option index is nonempty regardless of `nsIdx`).
  have hns' : (X.ctx p).frac (⋃ i, (X.ctx p).nsFiber i) = 0 := by
    haveI : Countable (X.ctx p).nsIdx := (X.ctx p).nsCountable
    obtain ⟨e, he⟩ :
        ∃ e : ℕ → Option (X.ctx p).nsIdx, Function.Surjective e :=
      exists_surjective_nat _
    set g : Option (X.ctx p).nsIdx → Set (MovesX.MonicBox n p) :=
      fun o => o.elim (MovesX.InfTree (X.ctx p)) (X.ctx p).nsFiber with hg
    have hgnull : ∀ o, (X.ctx p).frac (g o) = 0 := by
      intro o
      cases o with
      | none => simpa [hg] using hInf
      | some i => simpa [hg] using hns p i
    have hcover : (⋃ i, (X.ctx p).nsFiber i) ⊆ ⋃ k, g (e k) := by
      rw [he.iUnion_comp g]
      exact Set.iUnion_subset (fun i => Set.subset_iUnion g (some i))
    refine le_antisymm ?_ ((X.ctx p).frac_nonneg _)
    calc (X.ctx p).frac (⋃ i, (X.ctx p).nsFiber i)
        ≤ (X.ctx p).frac (⋃ k, g (e k)) := (X.ctx p).frac_mono _ _ hcover
      _ = 0 := (X.ctx p).frac_iUnion_null _ (fun k => hgnull (e k))
  -- Drain, then KA4b.
  exact escape_of_drain hnn hsub (blockDrain_of_drainIdent ID hInf hns')

end LeanUrat.Kernels
