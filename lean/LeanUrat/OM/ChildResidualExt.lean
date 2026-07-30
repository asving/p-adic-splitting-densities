/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.DevelopmentExt
import LeanUrat.OM.OrderTwoContext

/-!
# `ChildResidualExt` — the `resField[X]`-valued child residual over `O″` (P9, WAVE 1)

**SCAFFOLDING toward the order-≥2 residue-field-EXTENSION reader.** Wave 1 of the P9 subsystem
(`uniform-rationality/notes/ORDER2_READER_BLUEPRINT_2026-07-14.md` §1). This file states
`childResidualExt`, the `resField[X]`-valued replacement for `Classifier.childResidual` (which is
`(ZMod p)[X]`-valued and pinned to `Fr = ZMod p`), and proves the well-formedness that is available
now: its degree bound.

## What this file lands (core-only, no `sorry`/`axiom`)

* `resUnitResidue : O″ → resField` — the residue reader (blueprint §2b). For `x : O″` with `p`-adic
  valuation `v = pval_Oring x`, divide out `p^v` (choosing a witness `u` with `x = p^v · u` from
  `x ∈ span{p^v}`) then reduce mod `p` (`resHom u`). This is the extension analogue of
  `PadicLift.zmodUnitResidue`. Per the blueprint it is a "modest composition, NOT one of the two hard
  lemmas". **HONEST SCOPE:** the witness `u` is only determined modulo `Ann(p^v)`, so `resUnitResidue`
  is *defined* (total) but its being the CANONICAL unit residue — i.e. independent of the witness
  choice, matching the abstract Montes residual — is part of the wave-2 faithfulness target, NOT
  claimed here. Wave 1 uses it only as a total `O″ → resField` reader.
* `childResidualExt : resField[X]` — reads `resUnitResidue` of the constant term of each `O″`-digit of
  the developed box element (`developExt` against a monic key `Φ : O″[X]`), assembled as
  `∑ t : Fin μ, C (resUnitResidue (digit t).coeff 0) · X^t`. The `resField[X]`-valued mirror of
  `Classifier.childResidual`.
* `childResidualExt_degree` / `childResidualExt_natDegree_lt` — the well-formedness degree bounds:
  `degree < μ`, and `natDegree < μ` for `0 < μ` (so it fits a cluster-size budget `≤ μ - 1`, exactly
  as `childResidual`'s `∑ … C(…) X^t` shape does). Proved via `Polynomial.degree_sum_fin_lt`.

## What this file DELIBERATELY does NOT do (open, gating — wave 2+)

* It does NOT prove `childResidualExt` reads `f`'s genuine order-`r` residual — that is `OPEN TARGET
  B.2` in `DevelopmentExt.lean` (the residual-faithfulness identification, the gating new math).
* It does NOT take a genuine base-changed `f` over `O″`; the key `Φ : O″[X]` here is an arbitrary
  monic — wiring the running key `Φ = liftKeyExt … Ψ` (Lemma A, sibling file) and the base-changed
  box element `O″Box` (blueprint §1a) into a recursion `classifyGenuineExtAux` is wave 2 (blueprint
  §3). The degree bound proved here is field-agnostic and holds for ANY monic `Φ` and box element.
* `resUnitResidue`'s witness-independence / genuine-unit-residue characterization is NOT proved.

Discipline: no `sorry`/`axiom`/`native_decide`. Imports `DevelopmentExt` + `OrderTwoContext`
READ-ONLY (and through them `Development`/`UnramifiedBase`); NEVER edits any existing file (two-stream
contention rule).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.ChildResidualExt

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The residue reader `resUnitResidue : O″ → resField`

`resHom : O″ → resField` reduces mod `p` (kills `span{p}`). To read a genuine unit residue we first
divide out the `p`-adic valuation `pval_Oring x`, using a chosen witness of `x ∈ span{p^{pval x}}`
(`UnramifiedBase.mem_span_p_pow_pval`), then reduce that witness mod `p`. -/

/-- A chosen witness `u : O″` with `x = p^{pval x} · u`, from `x ∈ span{p^{pval x}}`
(`mem_span_p_pow_pval` + `Ideal.mem_span_singleton'`). Choice-dependent (the witness is unique only
mod `Ann(p^{pval x})`); used to DEFINE `resUnitResidue`. Its canonicity is a wave-2 target. -/
def pvalWitness (hgm : g.Monic) (hN : 0 < N) (x : UnramifiedBase.Oring p N g) :
    UnramifiedBase.Oring p N g :=
  Classical.choose <| (Ideal.mem_span_singleton'.mp (UnramifiedBase.mem_span_p_pow_pval p N g x))

theorem pvalWitness_spec (hgm : g.Monic) (hN : 0 < N) (x : UnramifiedBase.Oring p N g) :
    (pvalWitness p N g hgm hN x) * (((p : ℕ) : UnramifiedBase.Oring p N g) ^
        (UnramifiedBase.pval_Oring p N g x)) = x :=
  Classical.choose_spec <|
    (Ideal.mem_span_singleton'.mp (UnramifiedBase.mem_span_p_pow_pval p N g x))

/-- **The residue reader** `resUnitResidue : O″ → resField` (blueprint §2b). Reduce mod `p`
(`resHom`) the `p^{pval}`-normalized part of `x`. The extension analogue of
`PadicLift.zmodUnitResidue`. **Scope:** total and lands in `resField`; witness-independence /
genuine-unit-residue characterization is a wave-2 target (see file docstring). -/
def resUnitResidue (hgm : g.Monic) (hN : 0 < N) (x : UnramifiedBase.Oring p N g) :
    UnramifiedBase.resField p N g hN :=
  UnramifiedBase.resHom p N g hgm hN (pvalWitness p N g hgm hN x)

/-! ## WAVE 2, Goal 1: `resUnitResidue` canonicity (witness-independence)

`resUnitResidue` is defined via the choice-dependent `pvalWitness`. Below we prove it is in fact
well-defined *independently of the witness choice* for `x ≠ 0`: any `u` with `u · p^{pval x} = x`
gives the same `resHom u`. This hardens the reader's output map (blueprint §2b: `resUnitResidue`
is the residue reader; wave-1 left its canonicity as a target — here PROVED for `x ≠ 0`).

**The `x = 0` boundary is genuinely non-canonical** and is NOT claimed: at `x = 0` the valuation is
`N`, `p^N = 0`, and every `u` is a witness, so `resHom u` ranges over all of `resField`. The honest
canonicity statement is therefore *for `x ≠ 0`* (equivalently `pval x < N`), which is exactly the
regime the Montes residual reader uses (a residual coefficient read at a lattice point off the
polygon is `0`, handled by the guard, never by `resUnitResidue` of `0`). -/

open UnramifiedBase in
/-- `span{p^N} = ⊥` since `p^N = 0` (`isNilpotent_natCast_p`). -/
theorem span_p_pow_N_eq_bot (hN : 0 < N) :
    Ideal.span {((p : ℕ) : Oring p N g) ^ N} = (⊥ : Ideal (Oring p N g)) := by
  rw [isNilpotent_natCast_p p N g hN, Ideal.span_singleton_eq_bot]

open UnramifiedBase in
/-- `pval x = N ↔ x = 0`: the top valuation is attained only at `0` (since `span{p^N} = ⊥`). -/
theorem pval_eq_N_iff (hN : 0 < N) (x : Oring p N g) :
    pval_Oring p N g x = N ↔ x = 0 := by
  constructor
  · intro h
    have hmem := mem_span_p_pow_pval p N g x
    rwa [h, span_p_pow_N_eq_bot p N g hN, Ideal.mem_bot] at hmem
  · intro h; subst h; exact pval_zero p N g

open UnramifiedBase in
/-- For `x ≠ 0`, the valuation is strictly below `N` (`pval x < N`). -/
theorem pval_lt_N_of_ne_zero (hN : 0 < N) {x : Oring p N g} (hx : x ≠ 0) :
    pval_Oring p N g x < N :=
  lt_of_le_of_ne (pval_le p N g x) (fun h => hx ((pval_eq_N_iff p N g hN x).mp h))

open UnramifiedBase in
/-- `p^j ≠ 0` for `j < N`: the filtration ideal `span{p^j}` has card `(p^{deg g})^{N-j} > 1`, so it
is nontrivial (`card_span_p_pow`), hence `p^j ≠ 0`. -/
theorem p_pow_ne_zero_of_lt (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) {j : ℕ} (hj : j < N) :
    ((p : ℕ) : Oring p N g) ^ j ≠ 0 := by
  haveI := finite_Oring p N g hgm hN
  intro h0
  have hcard := card_span_p_pow p N g hgm hN hm hgirr j (le_of_lt hj)
  rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hcard
  have hbot : Nat.card (⊥ : Ideal (Oring p N g)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]; exact ⟨inferInstance, ⟨0⟩⟩
  rw [hbot] at hcard
  have : 1 < (p ^ g.natDegree) ^ (N - j) :=
    Nat.one_lt_pow (by omega) (Nat.one_lt_pow hm.ne' hp.out.one_lt)
  omega

open UnramifiedBase in
/-- If `w · p^v = 0` and `v < N`, then `w ∈ span{p}` (`w` is a nonunit). If `w` were a unit
(`isUnit_iff_notMem`), then `p^v = w⁻¹·(w·p^v) = 0`, contradicting `p^v ≠ 0` for `v < N`. -/
theorem mem_span_p_of_mul_p_pow_eq_zero (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)]
    {w : Oring p N g} {v : ℕ} (hv : v < N)
    (hw : w * ((p : ℕ) : Oring p N g) ^ v = 0) :
    w ∈ Ideal.span {((p : ℕ) : Oring p N g)} := by
  by_contra hmem
  have hunit : IsUnit w := (isUnit_iff_notMem p N g hgm hN hm hgirr w).mpr hmem
  exact p_pow_ne_zero_of_lt p N g hgm hN hm hgirr hv (hunit.mul_right_eq_zero.mp hw)

open UnramifiedBase in
/-- **Witness-independence of the unit residue** (for `x ≠ 0`). Any two witnesses `u₁ u₂` with
`uᵢ · p^{pval x} = x` reduce to the SAME residue `resHom u₁ = resHom u₂`. The difference satisfies
`(u₁ - u₂)·p^{pval x} = 0` with `pval x < N`, so `u₁ - u₂ ∈ span{p} = ker resHom`. -/
theorem resHom_witness_indep (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)]
    {x : Oring p N g} (hx : x ≠ 0) {u₁ u₂ : Oring p N g}
    (h1 : u₁ * ((p : ℕ) : Oring p N g) ^ (pval_Oring p N g x) = x)
    (h2 : u₂ * ((p : ℕ) : Oring p N g) ^ (pval_Oring p N g x) = x) :
    resHom p N g hgm hN u₁ = resHom p N g hgm hN u₂ := by
  have hdiff : (u₁ - u₂) * ((p : ℕ) : Oring p N g) ^ (pval_Oring p N g x) = 0 := by
    rw [sub_mul, h1, h2, sub_self]
  have hker : u₁ - u₂ ∈ RingHom.ker (resHom p N g hgm hN) := by
    rw [ker_resHom_eq_span_p]
    exact mem_span_p_of_mul_p_pow_eq_zero p N g hgm hN hm hgirr
      (pval_lt_N_of_ne_zero p N g hN hx) hdiff
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at hker

open UnramifiedBase in
/-- **`resUnitResidue` equals the residue of ANY witness** (for `x ≠ 0`) — the canonicity
statement. The choice-dependent `pvalWitness` may be replaced by any `u` with `u·p^{pval x} = x`;
so `resUnitResidue x` is well-defined independently of the witness. Core-only. -/
theorem resUnitResidue_eq_of_witness (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)]
    {x : Oring p N g} (hx : x ≠ 0) {u : Oring p N g}
    (hu : u * ((p : ℕ) : Oring p N g) ^ (pval_Oring p N g x) = x) :
    resUnitResidue p N g hgm hN x = resHom p N g hgm hN u :=
  resHom_witness_indep p N g hgm hN hm hgirr hx (pvalWitness_spec p N g hgm hN x) hu

-- Footprint check (Goal 1): must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms resUnitResidue_eq_of_witness

/-! ## The `resField[X]`-valued child residual -/

/-- **`childResidualExt`** — the `resField[X]`-valued replacement for `Classifier.childResidual`.
Reads `resUnitResidue` of the constant term of each `O″`-development digit of the box element `h`
against a monic key `Φ : O″[X]`, `μ` digits, assembled into a `resField[X]`:

`∑ t : Fin μ, C (resUnitResidue ((developExt Φ μ h t).coeff 0)) · X^t`.

The extension mirror of `childResidual p N f ψ μ`, now valued in the genuine extension field
`resField = F_{p^{deg g}}` rather than `ZMod p`.

**Scope (wave 1):** `Φ` and `h` are arbitrary (a monic key and a box element over `O″`); this file
does NOT tie `Φ = liftKeyExt … Ψ` (Lemma A) nor `h` to a base-changed `f` (blueprint §1a/§3), and
does NOT certify the output IS `f`'s order-`r` residual (`OPEN TARGET B.2`). What IS proved is the
degree bound below. -/
def childResidualExt (hgm : g.Monic) (hN : 0 < N) (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) : (UnramifiedBase.resField p N g hN)[X] :=
  ∑ t : Fin μ, Polynomial.C
    (resUnitResidue p N g hgm hN ((DevelopmentExt.developExt p N g Φ μ h t).coeff 0))
    * Polynomial.X ^ (t : ℕ)

/-! ## Well-formedness: the degree bound -/

/-- **Degree bound** (well-formedness): `degree (childResidualExt … μ …) < μ`. The residual is
`∑ t : Fin μ, C (…) · X^t`, so `Polynomial.degree_sum_fin_lt` applies directly. This holds for ANY
monic key `Φ` and box element `h` (field-agnostic; it is a fact about the `∑ C(…) X^t` shape, not
about faithfulness). -/
theorem childResidualExt_degree (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    (childResidualExt p N g hgm hN Φ μ h).degree < (μ : WithBot ℕ) :=
  Polynomial.degree_sum_fin_lt _

/-- **`natDegree` form of the degree bound** for `0 < μ`: `natDegree (childResidualExt … μ …) < μ`,
i.e. the residual fits within `μ - 1`. Mirrors the cluster-size-budget shape of `childResidual`
(`Rr` guarded to degree `≤ s`). -/
theorem childResidualExt_natDegree_lt (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (hμ : 0 < μ)
    (h : (UnramifiedBase.Oring p N g)[X]) :
    (childResidualExt p N g hgm hN Φ μ h).natDegree < μ := by
  by_cases h0 : childResidualExt p N g hgm hN Φ μ h = 0
  · rw [h0, Polynomial.natDegree_zero]; exact hμ
  · have hdeg := childResidualExt_degree p N g hgm hN Φ μ h
    rwa [Polynomial.degree_eq_natDegree h0, Nat.cast_lt] at hdeg

/-- The residual is `0` at `μ = 0` (empty sum) — the boundary consistency check. -/
theorem childResidualExt_zero (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (h : (UnramifiedBase.Oring p N g)[X]) :
    childResidualExt p N g hgm hN Φ 0 h = 0 := by
  rw [childResidualExt, Fin.sum_univ_zero]

-- Footprint check: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms childResidualExt_natDegree_lt

/-! ## WAVE 2, Goal 2: the ext reduce-stability transport (CERTLEVEL layer, additive core)

The extension analogue of `Classifier.childResidual_reduce_stable` (build #58's per-node CERTLEVEL
content). `childResidual_reduce_stable` proves `childResidual` is stable under one-digit box
reduction below the per-digit cutoff, gluing three facts: (i) the key reduces
(`liftKey_map`), (ii) the φ-adic development commutes with the coefficient-reduction hom
(`Development.develop_map`), and (iii) `zmodUnitResidue` is stable under that hom below the cutoff
(`zmodUnitResidue_reduce_stable`). The termwise `∑ C(…) X^t` assembly is what glues (ii)+(iii).

**Scope, stated honestly.** For the `O″` reader the concrete "one-digit box reduction" would be a
ring hom `Oring(p, N+1, g') → Oring(p, N, g)` between DIFFERENT base rings (the key `g` lives over
`ZMod(p^N)`, so a level drop changes the base ring itself). No such level-reduction hom exists in
the repo, and building it (with `g'.map coeffReduce = g` bookkeeping) is a separate engineering wave
— it is NOT built here. What IS proved additively is the reusable transport CORE:
`childResidualExt` transports along ANY base ring hom `θ : Oring(p,N₁,g₁) → Oring(p,N₂,g₂)` and
compatible residue-field hom `φ`, GIVEN the per-digit `resUnitResidue`-compatibility hypothesis
`hcompat` (the exact cutoff-guarded analogue of (iii) that the CERTLEVEL layer must supply for its
concrete `θ`). This is the (ii)+assembly half — the develop-transport (`develop_map`) plus the
termwise sum congruence — with (iii) abstracted as the hypothesis it will be discharged by. Once the
concrete `Oring` level-reduction hom + its `resUnitResidue`-stability land (a later wave), the
concrete `childResidualExt_reduce_stable` is an immediate instance of this lemma. -/

open UnramifiedBase DevelopmentExt in
/-- **`childResidualExt` transport under a base ring hom** (the additive CERTLEVEL core, Goal 2).
For base rings `O₁ = Oring(p,N₁,g₁)`, `O₂ = Oring(p,N₂,g₂)`, a ring hom `θ : O₁ →+* O₂` and a
residue-field hom `φ : resField₁ →+* resField₂`, a monic key `Φ : O₁[X]` and box element `h : O₁[X]`,
given the per-digit `resUnitResidue`-compatibility `hcompat` (the cutoff-guarded analogue of
`zmodUnitResidue_reduce_stable`), the child residual transports:

`childResidualExt(O₂; Φ.map θ, μ, h.map θ) = (childResidualExt(O₁; Φ, μ, h)).map φ`.

Proof: `Polynomial.map` distributes over `∑ C(…) X^t`; each transported digit is `θ` of the original
digit (`Development.develop_map`, monicity of `Φ`), so its constant term is `θ` of the original
constant term; `hcompat` supplies the residue-hom compatibility termwise. Core-only. -/
theorem childResidualExt_transport
    (N₁ N₂ : ℕ) (g₁ : (ZMod (p ^ N₁))[X]) (g₂ : (ZMod (p ^ N₂))[X])
    (hgm₁ : g₁.Monic) (hN₁ : 0 < N₁) (hgm₂ : g₂.Monic) (hN₂ : 0 < N₂)
    (θ : Oring p N₁ g₁ →+* Oring p N₂ g₂)
    (φ : resField p N₁ g₁ hN₁ →+* resField p N₂ g₂ hN₂)
    (Φ : (Oring p N₁ g₁)[X]) (hΦ : Φ.Monic) (μ : ℕ) (h : (Oring p N₁ g₁)[X])
    (hcompat : ∀ t : Fin μ,
      resUnitResidue p N₂ g₂ hgm₂ hN₂ (θ ((developExt p N₁ g₁ Φ μ h t).coeff 0))
        = φ (resUnitResidue p N₁ g₁ hgm₁ hN₁ ((developExt p N₁ g₁ Φ μ h t).coeff 0))) :
    childResidualExt p N₂ g₂ hgm₂ hN₂ (Φ.map θ) μ (h.map θ)
      = (childResidualExt p N₁ g₁ hgm₁ hN₁ Φ μ h).map φ := by
  rw [childResidualExt, childResidualExt, Polynomial.map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  have hdigit : developExt p N₂ g₂ (Φ.map θ) μ (h.map θ) t
      = (developExt p N₁ g₁ Φ μ h t).map θ := by
    rw [developExt_def, developExt_def]
    exact (Development.develop_map θ hΦ μ h t).symm
  rw [hdigit, Polynomial.coeff_map]
  exact hcompat t

-- Footprint check (Goal 2): must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms childResidualExt_transport

/-! ## WAVE 2, Goal 3 — OPEN TARGET B.2 (residual-faithfulness): the PRECISE obstruction

**Goal 3 was ATTEMPTED and does NOT close. It is stated here as a documented open TARGET with NO
`sorry` and NO build obligation.** B.2 asks to prove that the `O″`-development digit constant-terms,
reduced via `resUnitResidue`, ARE the genuine Montes order-`r` residual coefficients of `f` over
`resField` — i.e. that `childResidualExt` is a FAITHFUL reader. The precise obstruction, found by
auditing the repo's residual infrastructure, is:

**There is no object in the repo for `childResidualExt` to be proved EQUAL to.** The only abstract
"Montes residual" is `M4.residualPoly (coeffData) S` (`ResidualPolynomial.lean`), and its coefficient
datum is a FREE OPAQUE parameter: `M4.residualCoeff coeffData _S t := coeffData t` — a bare function
`coeffData : ℕ → kS` with NO defining equation tying it to `Development.develop`, to `f`'s
coefficients, or to `PadicInt.unitCoeff` (the docstring at `residualCoeff` calls the genuine
`unitCoeff/toZMod` plumbing "opaque in the skeleton"). So a statement "`childResidualExt … =
residualPoly (someCoeffData) S`" is either vacuous (pick `coeffData := t ↦ resUnitResidue(digit t)`,
making it `rfl`-true but content-free) or unprovable (against an independently-specified
`coeffData`, which does not exist).

**No order-0/1 precedent exists to port up, either.** Even at `Fr = ZMod p`, the repo uses TWO
DISTINCT reader functions that are NEVER proved equal:
  * `Classifier.boxCoeffData` (`Classifier.lean:120`) reads `zmodUnitResidue` of `f`'s RAW
    coefficients at the polygon-side abscissae `S.i₀ + t·S.e`, feeding `M4.residualPoly` — this is
    the order-0 root residual reader.
  * `Classifier.childResidual` (`Classifier.lean:295`) reads `zmodUnitResidue` of the φ-adic
    DEVELOPMENT-digit constant terms — this is the deeper (order-1) reader `childResidualExt` mirrors.
There is NO theorem `childResidual … = residualPoly (boxCoeffData …) …` (a develop-digit ↔
side-coefficient bridge) anywhere in the repo. The blueprint states this exactly (§2 Lemma B point 1):
the residual-correctness at `Fr = ZMod p` is "asserted via the `boxCoeffData`/`residualPoly`
construction … and … has NO proof for the extension `Fr`."

**Precisely the missing lemma.** To make B.2 provable, one must FIRST supply, over `resField`, an
independent definition of the order-`r` residual as a function of `f` (the Montes residual polynomial
`R_r`, e.g. via a `PadicInt.unitCoeff`-style unit-part-at-a-lattice-point construction on the
`O″`-development), and prove it agrees with the abstract `residualPoly` skeleton — the
`develop`-digit ↔ residual-coefficient identity. That identity is ABSENT even at order 0/1; supplying
it at order `r` over the extension is the ~300+-line gating research result. Until it exists, there
is no faithful-reader claim to discharge, so `childResidualExt` is HONESTLY only a well-formed
`resField[X]`-valued function of `f` (degree bound, canonical output map, transport core — all proved
above), NOT a certified residual reader.

**What Goal 3 DID land** (the tractable sub-parts of the wave-2 goals, all built above, core-only):
Goal 1 (`resUnitResidue` canonicity, `resUnitResidue_eq_of_witness`) hardens the reader's OUTPUT map;
Goal 2 (`childResidualExt_transport`) is the reusable CERTLEVEL transport core. Neither claims
faithfulness. The docstrings throughout this file and `DevelopmentExt.lean`'s `OPEN TARGET B.2`
remain accurate: the reader is NOT yet faithful. -/

end

end LeanUrat.OM.ChildResidualExt
