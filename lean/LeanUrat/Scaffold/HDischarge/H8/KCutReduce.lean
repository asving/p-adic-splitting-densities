/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.Lemma33
import LeanUrat.Scaffold.HDischarge.H8.CutSeam
import LeanUrat.Scaffold.HDischarge.H8.CutExtract
import LeanUrat.Scaffold.HDischarge.H8.SiteExpCut

/-! # H8-C1 `KCutReduce.lean` — the display bridge: B3-extraction + typed seam
re-keys → `CutData` → the K1 regroup [re-scoped at review finding C-5]

## E-PHASE RECORD (no verbatim statement existed to transcribe)

The blueprint (`lean/blueprints/HDISCHARGE_H8.md` §4 Wave 3, H8-C1) pins NO
verbatim statement — it mandates a unit-local E-phase "against H8-B3's carriers
+ BP_V's `SolveSeam`/`series_tie` wiring when BP_V unfreezes".  Both gates are
now open: H8-B3 (`CutExtract.lean`, design (a)) is landed, and BP_V has
unfrozen (`lean/blueprints/BP_V.md`; `SolveSeam` with its `series_tie` field is
typed at `MovesU/DefsLedger.lean`, consumed through `Scaffold/ValueSide/`).
This file IS the unit's E-phase, per the compile-probe rule — exactly as H8-B3
shipped its own.  Shape per the C-5 fix: GIVEN H8-B3's landed extraction AND
the TYPED re-keys of the three seam fields (binder-listed data/hypotheses, NOT
opaque Props), CONSTRUCT the `CutData` instance and conclude
`seriesSum_cut_conv`'s regroup — the ABSTRACT CONVOLUTION FORM of Step 18's
K1 (the exact instantiated form is open unit H8-C3; KCUT pass finding 7).

## What is and is NOT claimed (the honesty display)

* `KCutReKeys` + the three binder rows of `kcut_reduce` are the TYPED re-key
  targets named in `CutSeam.lean`'s BINDING DISPLAY RULE.  They are UNPINNED
  named assumptions — supplying an instance is the OWNER rows' work
  ((K-CUT-s): CTS-M(i)/(iii)/CL-13; (K-CUT-g): D-14 + CU-3 + REL.2, the
  charge-(vi) arc; (K-CUT-m): TREE-EXP + [2r]/CL-8 + O-1/O-3), never this
  unit's.  NOTHING here discharges a seam field.
* (K-CUT-s): `supplyDec` is HONESTLY DISPLAYED as CLASSICALLY VACUOUS
  (`Classical.dec` satisfies it for EVERY predicate) and CONSUMED BY NO PROOF
  in this file — a registration row, NOT a consuming face of (K-CUT-s)
  [KCUT pass finding 1]; the shape/entrance supply rows (`ShL`…`ent_mem`) are
  where the family data actually enters.  The full decidable-from-`CellData`
  characterization of `E` stays wholly with its owners.
* NON-CONSUMPTION HONESTY [KCUT pass finding 2]: `kcut_reduce` does NOT
  consume H8-B3's `cutOf`/`cut_injective` — the consumer-side forward map is
  RE-ASSUMED (`shIdx`/`cutBlk`) with conformance rows (`shIdx_eq`/
  `cutBlk_car`), and consumer-level injectivity rides the ASSUMED
  `graft_cut`.  (H8-B3's proved forward half constrains these rows through
  the conformance equations but does not supply them.)
* (K-CUT-g) = `graft`/`graft_cut`/`cut_graft`: the graft function + the two
  inverse laws (the `cut` Equiv's missing half — H8-B3 proved the forward map
  and its injectivity; surjectivity-with-inverse is exactly graft
  completeness, G-2's open channel).
* (K-CUT-m) = `mass_eq` (+ the `W`/`weight` data rows): the AGGREGATE product
  identity ONLY — `W`/`weight` are otherwise arbitrary functions, and
  compensating factors can satisfy the aggregate equation [KCUT pass finding
  4].  The FACTORWISE law is typed + derivation-proved at unit H8-C2
  (K-CUT-m-factor, `KCutMassFactor.lean` — landed; itself an unpinned
  owner-row interface), blueprint §4 Wave 7.
* The realization row `real`, the verdict map `vOf`, and the keying
  `verdict_key` are UNCONDITIONED assumptions — no realizability,
  completeness, canonicity, faithfulness, or injectivity condition is imposed
  [KCUT pass finding 5]; their faithful form rides the TREE-N/[3t] seam.
  The countability rows `ctblS`/`ctblD` are DIRECT assumptions (the
  transported clause; H8-B3's `cutFamily_countable` transports countability
  of a SOURCE family, it does not supply these rows).
* The conclusion is `seriesSum_cut_conv`'s regroup verbatim at the constructed
  instance — the ABSTRACT CONVOLUTION FORM of Step 18's K1, NOT its exact
  instantiated form [KCUT pass finding 7]: no (e_i, τ_i, δ_i) entrance lists,
  no transported pool q^δ, no grammar block totals appear; that exact-form
  tie is typed + derivation-proved at unit H8-C3 (K-CUT-K1-tie,
  `KCutK1Tie.lean` — landed; itself an unpinned owner-row interface),
  blueprint §4 Wave 7.  The onward tie
  to `SolveSeam.series_tie`'s `Rval` (the solve-side value) is BP_V/M04-side
  work, NOT landed here.  The one-line `RootHyps` `h8_kcut` extension is
  ORCHESTRATOR-owned (shared edit across the nine leads) — flagged, not
  landed.

Deps: H8-B1 (`SiteExpCut`, the count-form (†) sibling display — imported,
unconsumed by the series form), H8-B2 (`CutSeam`, the bare-Prop seam whose
typed re-keys these rows are), H8-B3 (`CutExtract`, consumed:
`ShallowData`/`BlockDeriv`/`shallowDataOf`/`blockDerivOf`/`ShallowData.σ0`/
`BlockDeriv.verdict`/`typemult_cut`), H8-A3 (`Lemma33`: `CutData` +
`seriesSum_cut_conv`), BP_V (E-phase gate only). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- THE TYPED SEAM RE-KEYS, extraction side (binder-listed data/hypotheses per
the C-5 re-scope; every row is an UNPINNED named assumption owned by its seam
row — see the module docstring's owner map).  `Fb` is the [3t] series carrier;
`E` the entrance predicate; the fields tie `Fb`'s abstract trees to H8-B3's
concrete extraction over `VTree p F` at the SAME prime `p`. -/
structure KCutReKeys {n p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) (E : History p F → Prop) where
  /-- (K-CUT-s) REGISTRATION ROW ONLY [KCUT pass finding 1]: CLASSICALLY
  VACUOUS (`Classical.dec` satisfies it for every `E`) and CONSUMED BY NO
  PROOF in this file — it does NOT constitute a consuming face of (K-CUT-s),
  whose cell-data supply stays wholly with the owner rows
  CTS-M(i)/(iii)/CL-13. -/
  supplyDec : ∀ H : History p F, Decidable (E H)
  /-- the [3t] ↦ MovesT realization: each abstract type-σ tree realizes as a
  concrete `VTree` (TREE-N/[3t] seam territory). -/
  real : ∀ σ, Fb.Tree σ → VTree p F
  /-- the verdict of a splitting type (the consumer keys it to `vmap`'s
  reading; the tie is owner-row work). -/
  vOf : LeanUrat.MovesU.SplittingType n → Multiset (ℕ × ℕ)
  /-- verdict keying: a type-σ tree realizes with `typemult` = the σ verdict. -/
  verdict_key : ∀ σ (T : Fb.Tree σ), (real σ T).typemult = vOf σ
  /-- the shallow shape family (index type). -/
  ShL : Type
  /-- countability of the shape family — the TRANSPORTED clause (H8-B3 header
  honesty note: not a type-level fact of the raw carriers). -/
  ctblS : Countable ShL
  /-- each shape index carries concrete H8-B3 shallow data. -/
  shape : ShL → ShallowData p F
  /-- block count per shape. -/
  k : ShL → ℕ
  k_card : ∀ Ŝ, k Ŝ = (shape Ŝ).ents.card
  /-- an enumeration of each shape's entrance list. -/
  ent : ∀ Ŝ, Fin (k Ŝ) → History p F
  ent_inj : ∀ Ŝ, Function.Injective (ent Ŝ)
  ent_mem : ∀ Ŝ i, ent Ŝ i ∈ (shape Ŝ).ents
  /-- per-slot block-derivation types. -/
  Deriv : ∀ Ŝ : ShL, Fin (k Ŝ) → Type
  /-- countability of each slot family — transported clause, as `ctblS`. -/
  ctblD : ∀ Ŝ i, Countable (Deriv Ŝ i)
  /-- each abstract derivation carries concrete H8-B3 block data (design (a)). -/
  dcar : ∀ Ŝ i, Deriv Ŝ i → BlockDeriv p F
  /-- (K-CUT-m) data half: the measured shallow mass per shape. -/
  W : ShL → ℝ≥0∞
  /-- (K-CUT-m) data half: the measured block weight per slot. -/
  weight : ∀ Ŝ i, Deriv Ŝ i → ℝ≥0∞
  /-- the cut, shape leg: which shape a tree cuts to. -/
  shIdx : ∀ σ, Fb.Tree σ → ShL
  /-- CONFORMANCE: the assigned shape IS H8-B3's extraction `Ŝ(real T)`. -/
  shIdx_eq : ∀ σ T, shape (shIdx σ T) = shallowDataOf (real σ T) E
  /-- the cut, block leg: the slot contents a tree cuts to. -/
  cutBlk : ∀ σ (T : Fb.Tree σ) (i : Fin (k (shIdx σ T))), Deriv (shIdx σ T) i
  /-- CONFORMANCE: each assigned slot IS H8-B3's extraction `D_ε(real T)` at
  the enumerated entrance. -/
  cutBlk_car : ∀ σ T i, dcar (shIdx σ T) i (cutBlk σ T i)
    = blockDerivOf (real σ T) E (ent (shIdx σ T) i)

namespace KCutReKeys

variable {n : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
  {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}

/-- The enumeration rows make each `ent Ŝ` a bijective enumeration of the
entrance list, so slot sums equal entrance-set sums. -/
theorem sum_ent {M : Type*} [AddCommMonoid M] (R : KCutReKeys Fb E)
    (Ŝ : R.ShL) (f : History p F → M) :
    ∑ i : Fin (R.k Ŝ), f (R.ent Ŝ i) = ∑ ε ∈ (R.shape Ŝ).ents, f ε := by
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
  calc ∑ i : Fin (R.k Ŝ), f (R.ent Ŝ i)
      = ∑ ε ∈ (Finset.univ : Finset (Fin (R.k Ŝ))).image (R.ent Ŝ), f ε :=
        (Finset.sum_image fun i _ j _ h => R.ent_inj Ŝ h).symm
    _ = ∑ ε ∈ (R.shape Ŝ).ents, f ε := by rw [himg]

/-- CUT COMPATIBILITY, derived (not a row): the cut of any type-σ tree is
verdict-compatible — σ₀ of its shape plus its slot verdicts is the σ verdict.
Proof = H8-B3's `typemult_cut` conformance + the keying rows; this is the
lemma that lets the cut land in `CutData.cut`'s constrained target. -/
theorem cut_compat (R : KCutReKeys Fb E) (σ : LeanUrat.MovesU.SplittingType n)
    (T : Fb.Tree σ) :
    (R.shape (R.shIdx σ T)).σ0
      + ∑ i, (R.dcar (R.shIdx σ T) i (R.cutBlk σ T i)).verdict = R.vOf σ := by
  classical
  have hshape : R.shape (R.shIdx σ T) = shallowDataOf (R.real σ T) E :=
    R.shIdx_eq σ T
  have hsum : ∑ i, (R.dcar (R.shIdx σ T) i (R.cutBlk σ T i)).verdict
      = ∑ ε ∈ minEnts (R.real σ T) E, (blockDerivOf (R.real σ T) E ε).verdict := by
    have h2 : (R.shape (R.shIdx σ T)).ents = minEnts (R.real σ T) E := by
      rw [hshape, shallowDataOf_ents]
    calc ∑ i, (R.dcar (R.shIdx σ T) i (R.cutBlk σ T i)).verdict
        = ∑ i, (blockDerivOf (R.real σ T) E (R.ent (R.shIdx σ T) i)).verdict :=
          Finset.sum_congr rfl fun i _ =>
            congrArg BlockDeriv.verdict (R.cutBlk_car σ T i)
      _ = ∑ ε ∈ (R.shape (R.shIdx σ T)).ents,
            (blockDerivOf (R.real σ T) E ε).verdict :=
          R.sum_ent (R.shIdx σ T)
            (fun ε => (blockDerivOf (R.real σ T) E ε).verdict)
      _ = ∑ ε ∈ minEnts (R.real σ T) E,
            (blockDerivOf (R.real σ T) E ε).verdict := by rw [h2]
  calc (R.shape (R.shIdx σ T)).σ0
        + ∑ i, (R.dcar (R.shIdx σ T) i (R.cutBlk σ T i)).verdict
      = (shallowDataOf (R.real σ T) E).σ0
        + ∑ ε ∈ minEnts (R.real σ T) E,
            (blockDerivOf (R.real σ T) E ε).verdict := by rw [hshape, hsum]
    _ = (R.real σ T).typemult := (typemult_cut (R.real σ T) E).symm
    _ = R.vOf σ := R.verdict_key σ T

/-- The verdict-compatible decomposition tuples of type σ — `CutData.cut`'s
target, in re-key vocabulary. -/
def CompatTuple (R : KCutReKeys Fb E)
    (σ : LeanUrat.MovesU.SplittingType n) : Type :=
  {x : Σ Ŝ : R.ShL, ∀ i : Fin (R.k Ŝ), R.Deriv Ŝ i //
    (R.shape x.1).σ0 + ∑ i, (R.dcar x.1 i (x.2 i)).verdict = R.vOf σ}

/-- THE CUT FUNCTION (forward half, derived from H8-B3's extraction through
the conformance rows; lands in the constrained target via `cut_compat`). -/
def cutFun (R : KCutReKeys Fb E) (σ : LeanUrat.MovesU.SplittingType n)
    (T : Fb.Tree σ) : R.CompatTuple σ :=
  ⟨⟨R.shIdx σ T, R.cutBlk σ T⟩, R.cut_compat σ T⟩

/-- **THE `CutData` INSTANCE** — the C-5 bridge: H8-B3's extraction (through
the conformance rows) + the (K-CUT-g) graft rows + the (K-CUT-m) mass row
assemble M04 Lemma 3.3's typed hypothesis.  The graft/mass rows are the typed
seam re-keys, binder-listed here exactly as the re-scope demands. -/
noncomputable def toCutData (R : KCutReKeys Fb E)
    (graft : ∀ σ, R.CompatTuple σ → Fb.Tree σ)
    (graft_cut : ∀ σ (T : Fb.Tree σ), graft σ (R.cutFun σ T) = T)
    (cut_graft : ∀ σ (x : R.CompatTuple σ), R.cutFun σ (graft σ x) = x)
    (mass_eq : ∀ σ (T : Fb.Tree σ), Fb.mass σ T
      = R.W (R.shIdx σ T) * ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i)) :
    CutData Fb (Multiset (ℕ × ℕ)) where
  vOf := R.vOf
  ShL := R.ShL
  ctblS := R.ctblS
  k := R.k
  W := R.W
  σ0 := fun Ŝ => (R.shape Ŝ).σ0
  Deriv := R.Deriv
  ctblD := R.ctblD
  dverdict := fun Ŝ i D => (R.dcar Ŝ i D).verdict
  weight := R.weight
  cut := fun σ => ⟨R.cutFun σ, graft σ, graft_cut σ, cut_graft σ⟩
  mass_eq := fun σ T => mass_eq σ T

/-- The block totals in re-key vocabulary (definitionally `CutData.blockTotal`
at the constructed instance — see `toCutData_blockTotal`). -/
noncomputable def blockTotal (R : KCutReKeys Fb E) (Ŝ : R.ShL)
    (i : Fin (R.k Ŝ)) (v : Multiset (ℕ × ℕ)) : ℝ≥0∞ :=
  ∑' D : {D : R.Deriv Ŝ i // (R.dcar Ŝ i D).verdict = v}, R.weight Ŝ i D.1

/-- Consumption-form conformance: the re-key block total IS the instance's
`CutData.blockTotal`. -/
theorem toCutData_blockTotal (R : KCutReKeys Fb E)
    (graft : ∀ σ, R.CompatTuple σ → Fb.Tree σ)
    (graft_cut : ∀ σ (T : Fb.Tree σ), graft σ (R.cutFun σ T) = T)
    (cut_graft : ∀ σ (x : R.CompatTuple σ), R.cutFun σ (graft σ x) = x)
    (mass_eq : ∀ σ (T : Fb.Tree σ), Fb.mass σ T
      = R.W (R.shIdx σ T) * ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i))
    (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (v : Multiset (ℕ × ℕ)) :
    (R.toCutData graft graft_cut cut_graft mass_eq).blockTotal Ŝ i v
      = R.blockTotal Ŝ i v := rfl

end KCutReKeys

/-- **H8-C1 DISPLAY THEOREM** — the K1 regroup in the ABSTRACT CONVOLUTION
FORM of Step 18's K1 [downgraded at KCUT pass finding 7: the conclusion
carries no (e_i, τ_i, δ_i) entrance lists, no transported pool q^δ, and no
grammar block totals — the exact instantiated Step-18 form is OPEN unit
H8-C3 (K-CUT-K1-tie)]: GIVEN the extraction-side re-keys `R` and the
binder-listed (K-CUT-g)/(K-CUT-m) typed re-keys, the σ fiber series IS the
shallow convolution of the ABSTRACT block totals (`W`/`weight` tied only by
the aggregate `mass_eq`; factorwise law = open H8-C2).  Proof: construct the
`CutData` instance (`KCutReKeys.toCutData`) and fire H8-A3's
`seriesSum_cut_conv`.  RESIDUAL CONDITIONALITY = precisely the displayed
binder rows (ALL of `R`'s fields — carriers, conformance, countability,
realization/keying, `supplyDec` — plus `graft`/`graft_cut`/`cut_graft`/
`mass_eq`), each an UNPINNED named assumption owned per the module
docstring's owner map; nothing is discharged here. -/
theorem kcut_reduce {n : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E)
    (graft : ∀ σ, R.CompatTuple σ → Fb.Tree σ)
    (graft_cut : ∀ σ (T : Fb.Tree σ), graft σ (R.cutFun σ T) = T)
    (cut_graft : ∀ σ (x : R.CompatTuple σ), R.cutFun σ (graft σ x) = x)
    (mass_eq : ∀ σ (T : Fb.Tree σ), Fb.mass σ T
      = R.W (R.shIdx σ T) * ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i))
    (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : R.ShL, R.W Ŝ *
          ∑' vt : {vt : Fin (R.k Ŝ) → Multiset (ℕ × ℕ) //
              (R.shape Ŝ).σ0 + ∑ i, vt i = R.vOf σ},
            ∏ i, R.blockTotal Ŝ i (vt.1 i) :=
  seriesSum_cut_conv (R.toCutData graft graft_cut cut_graft mass_eq) σ

end LeanUrat.Scaffold.HDischarge.H8
