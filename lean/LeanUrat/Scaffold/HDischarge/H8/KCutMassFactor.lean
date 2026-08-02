/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.KCutReduce
import LeanUrat.MovesU.DefsLedger

/-! # H8-C2 `KCutMassFactor.lean` — (K-CUT-m-factor): THE FACTORWISE MASS LAW

Blueprint: `lean/blueprints/HDISCHARGE_H8.md` §4 Wave 7 (specced 2026-08-05 at
the KCUT pass, finding 4; statements compile-probed green at b08b6dd,
`/tmp/openmath/H8_wave7_probe.lean`).  Statements below are VERBATIM from that
probe; this unit lands them and proves the derivation theorem.

## What is and is NOT claimed (the honesty display)

* `kcut_reduce`'s `mass_eq` row ties `W`/`weight` to the tree mass only through
  the AGGREGATE product — compensating factors satisfy it [KCUT pass finding
  4].  `KCutMassFactor` is the STRICTLY STRONGER factorwise law: both mass
  rows factor through the CONCRETE H8-B3 carriers (`ShallowData`/`BlockDeriv`)
  by SLOT-INDEPENDENT functions `shMass`/`blkMass`, and the tree mass
  factorizes along the concrete extraction (`shallowDataOf`/`blockDerivOf`
  over `minEnts`) — SLOT-dependent compensation is killed (weights cannot
  depend on the abstract slot separately from `dcar`); compensation across
  distinct `BlockDeriv` values remains possible until `blkMass` is identified
  with the measured semantics [round-2 pass finding 3].
* The structure is an UNPINNED assumption package: supplying an instance —
  identifying `shMass`/`blkMass` with the MEASURED semantics (shallow mass;
  grammar weight at the transported pool) — is OWNER-ROW work ((H7)/sibjc
  TREE-EXP rows + [2r]/CL-8 + O-1/O-3), never this unit's.  The block-side
  measured reading is typed at unit H8-C3 (K-CUT-K1-tie, `KCutK1Tie.lean` —
  landed; itself an unpinned interface).  NOTHING here
  discharges a seam field.
* `massFactor_mass_eq` IS proved (sorry-free): factorwise ⇒ the aggregate
  `mass_eq` row, i.e. any `KCutMassFactor` instance supplies `kcut_reduce`/
  `toCutData`'s `mass_eq` binder verbatim.  Proof = the conformance rows
  (`shIdx_eq`, `cutBlk_car`) + `shallowDataOf_ents` + the multiplicative
  `sum_ent` analogue (`KCutReKeys.prod_ent`, added here as the blueprint
  predicts), identifying each factor over the ownership partition.

Deps: H8-C1 (`KCutReduce`: `KCutReKeys` + conformance + `sum_ent` pattern),
H8-B3 (`CutExtract`, through C1: `ShallowData`/`BlockDeriv`/`shallowDataOf`/
`blockDerivOf`/`shallowDataOf_ents`), H8-D0 (`CutDefs`: `minEnts`). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- H8-C2 (K-CUT-m-factor): THE FACTORWISE MASS LAW. -/
structure KCutMassFactor {n : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E) where
  shMass : ShallowData p F → ℝ≥0∞
  blkMass : BlockDeriv p F → ℝ≥0∞
  W_factor : ∀ Ŝ : R.ShL, R.W Ŝ = shMass (R.shape Ŝ)
  weight_factor : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (D : R.Deriv Ŝ i),
    R.weight Ŝ i D = blkMass (R.dcar Ŝ i D)
  mass_factor : ∀ (σ : LeanUrat.MovesU.SplittingType n) (T : Fb.Tree σ),
    Fb.mass σ T
      = shMass (shallowDataOf (R.real σ T) E)
        * ∏ ε ∈ minEnts (R.real σ T) E, blkMass (blockDerivOf (R.real σ T) E ε)

namespace KCutReKeys

variable {n : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
  {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}

/-- The multiplicative `sum_ent` analogue (the blueprint-named derivation
ingredient): the enumeration rows make each `ent Ŝ` a bijective enumeration of
the entrance list, so slot products equal entrance-set products. -/
theorem prod_ent {M : Type*} [CommMonoid M] (R : KCutReKeys Fb E)
    (Ŝ : R.ShL) (f : History p F → M) :
    ∏ i : Fin (R.k Ŝ), f (R.ent Ŝ i) = ∏ ε ∈ (R.shape Ŝ).ents, f ε := by
  classical
  have himg : (Finset.univ : Finset (Fin (R.k Ŝ))).image (R.ent Ŝ)
      = (R.shape Ŝ).ents := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro ε hε
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hε
      exact R.ent_mem Ŝ i
    · rw [Finset.card_image_of_injective _ (R.ent_inj Ŝ), Finset.card_univ,
        Fintype.card_fin]
      exact le_of_eq (R.k_card Ŝ).symm
  calc ∏ i : Fin (R.k Ŝ), f (R.ent Ŝ i)
      = ∏ ε ∈ (Finset.univ : Finset (Fin (R.k Ŝ))).image (R.ent Ŝ), f ε :=
        (Finset.prod_image fun i _ j _ h => R.ent_inj Ŝ h).symm
    _ = ∏ ε ∈ (R.shape Ŝ).ents, f ε := by rw [himg]

end KCutReKeys

/-- H8-C2 consumption display: factorwise ⇒ the aggregate `mass_eq` row. -/
theorem massFactor_mass_eq {n : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E) (MF : KCutMassFactor R)
    (σ : LeanUrat.MovesU.SplittingType n) (T : Fb.Tree σ) :
    Fb.mass σ T
      = R.W (R.shIdx σ T) * ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i) := by
  classical
  -- the shape leg: `W` factors through the concrete shallow extraction
  have hshape : R.shape (R.shIdx σ T) = shallowDataOf (R.real σ T) E :=
    R.shIdx_eq σ T
  have hents : (R.shape (R.shIdx σ T)).ents = minEnts (R.real σ T) E := by
    rw [hshape, shallowDataOf_ents]
  have hW : R.W (R.shIdx σ T) = MF.shMass (shallowDataOf (R.real σ T) E) := by
    rw [MF.W_factor (R.shIdx σ T), hshape]
  -- the block leg: each slot factor IS the extraction factor at its entrance,
  -- and the slot product regroups to the `minEnts` product via `prod_ent`
  have hblk : ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i)
      = ∏ ε ∈ minEnts (R.real σ T) E,
          MF.blkMass (blockDerivOf (R.real σ T) E ε) := by
    calc ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i)
        = ∏ i, MF.blkMass (blockDerivOf (R.real σ T) E (R.ent (R.shIdx σ T) i)) :=
          Finset.prod_congr rfl fun i _ =>
            (MF.weight_factor (R.shIdx σ T) i (R.cutBlk σ T i)).trans
              (congrArg MF.blkMass (R.cutBlk_car σ T i))
      _ = ∏ ε ∈ (R.shape (R.shIdx σ T)).ents,
            MF.blkMass (blockDerivOf (R.real σ T) E ε) :=
          R.prod_ent (R.shIdx σ T)
            (fun ε => MF.blkMass (blockDerivOf (R.real σ T) E ε))
      _ = ∏ ε ∈ minEnts (R.real σ T) E,
            MF.blkMass (blockDerivOf (R.real σ T) E ε) := by rw [hents]
  rw [MF.mass_factor σ T, hW, hblk]

end LeanUrat.Scaffold.HDischarge.H8
