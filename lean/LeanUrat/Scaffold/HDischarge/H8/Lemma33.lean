/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D8_pathOrder
import LeanUrat.MovesU.Defs

/-! # H8-A3 `Lemma33.lean` — abstract M04 Lemma 3.3 over the [3t] `FiberSeries` carrier

`CutData` (the (‡)+(†) seam package at FULL-DATA granularity, §1.1 of the H8
blueprint), the per-slot `blockTotal`, and the two regrouping theorems
`seriesSum_cut` / `seriesSum_cut_conv`.  Statements VERBATIM from
`lean/blueprints/HDISCHARGE_H8.md` §4, Wave 1 block "H8-A3 Lemma33.lean".

G-7 NOTE (from the blueprint): tsum in `ℝ≥0∞` is defined over ARBITRARY index
types — neither theorem needs countability of `V` or of the verdict-tuple
index; the `ctblS`/`ctblD` fields are carried for the CONSUMER's sake. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

universe u

/-! ## Generic helpers (prover-added; no mathematical content beyond ENNReal Tonelli) -/

/-- Tonelli factorization of a finite product of `ℝ≥0∞` tsums over a Pi type:
`∑'_{g : Π i, α i} ∏_i w_i(g_i) = ∏_i ∑'_{a : α i} w_i(a)`.  Induction on `Fin k`
via `Fin.consEquiv`; unconditional in `ℝ≥0∞` (G-7: no countability needed). -/
private lemma tsum_pi_prod : ∀ (k : ℕ) (α : Fin k → Type u) (w : ∀ i, α i → ℝ≥0∞),
    ∑' g : ∀ i, α i, ∏ i, w i (g i) = ∏ i, ∑' a : α i, w i a := by
  intro k
  induction k with
  | zero =>
    intro α w
    have h1 : ∀ g : ∀ i : Fin 0, α i, (∏ i, w i (g i)) = (1 : ℝ≥0∞) := fun g => by simp
    rw [tsum_congr h1, tsum_eq_single (fun i : Fin 0 => i.elim0)
      (fun b' hb' => absurd (funext fun i => i.elim0) hb')]
    simp
  | succ m ih =>
    intro α w
    calc ∑' g : ∀ i, α i, ∏ i, w i (g i)
        = ∑' x : α 0 × ∀ i : Fin m, α i.succ, ∏ i, w i ((Fin.consEquiv α) x i) :=
          ((Fin.consEquiv α).tsum_eq (fun g => ∏ i, w i (g i))).symm
      _ = ∑' x : α 0 × ∀ i : Fin m, α i.succ, w 0 x.1 * ∏ i : Fin m, w i.succ (x.2 i) := by
          refine tsum_congr fun x => ?_
          rw [Fin.prod_univ_succ]
          simp [Fin.consEquiv]
      _ = ∑' a : α 0, ∑' b : ∀ i : Fin m, α i.succ, w 0 a * ∏ i : Fin m, w i.succ (b i) :=
          ENNReal.tsum_prod'
      _ = ∑' a : α 0, w 0 a * ∑' b : ∀ i : Fin m, α i.succ, ∏ i : Fin m, w i.succ (b i) :=
          tsum_congr fun a => ENNReal.tsum_mul_left
      _ = (∑' a : α 0, w 0 a) * ∑' b : ∀ i : Fin m, α i.succ, ∏ i : Fin m, w i.succ (b i) :=
          ENNReal.tsum_mul_right
      _ = (∑' a : α 0, w 0 a) * ∏ i : Fin m, ∑' d : α i.succ, w i.succ d :=
          congrArg (fun z => (∑' a : α 0, w 0 a) * z) (ih (fun i => α i.succ) (fun i => w i.succ))
      _ = ∏ i, ∑' a : α i, w i a := (Fin.prod_univ_succ (fun i => ∑' a : α i, w i a)).symm

/-- A predicate on a sigma type restricts fiberwise: `{x : Σ a, G a // P x} ≃ Σ a, {g // P ⟨a, g⟩}`. -/
private def sigmaSubtypeShuffle {A : Type*} {G : A → Type*} (P : (Σ a, G a) → Prop) :
    {x : Σ a, G a // P x} ≃ Σ a, {g : G a // P ⟨a, g⟩} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The verdict tuple of a compatible derivation tuple (the grouping map for
`seriesSum_cut_conv`). -/
private def verdictTuple {k : ℕ} {V : Type*} {D : Fin k → Type*}
    (dv : ∀ i, D i → V) (P : (Fin k → V) → Prop)
    (g : {g : ∀ i, D i // P (fun i => dv i (g i))}) : {vt : Fin k → V // P vt} :=
  ⟨fun i => dv i (g.1 i), g.2⟩

/-- The fiber of `verdictTuple` over `vt` is the Pi of the slotwise verdict fibers. -/
private def fiberPiEquiv {k : ℕ} {V : Type*} (D : Fin k → Type*)
    (dv : ∀ i, D i → V) (P : (Fin k → V) → Prop) (vt : {vt : Fin k → V // P vt}) :
    {g : {g : ∀ i, D i // P (fun i => dv i (g i))} // verdictTuple dv P g = vt}
      ≃ ∀ i, {d : D i // dv i d = vt.1 i} where
  toFun gf i := ⟨gf.1.1 i, congrFun (congrArg Subtype.val gf.2) i⟩
  invFun h :=
    ⟨⟨fun i => (h i).1, by
        show P (fun i => dv i ((h i).1))
        rw [show (fun i => dv i ((h i).1)) = vt.1 from funext fun i => (h i).2]
        exact vt.2⟩,
      Subtype.ext (funext fun i => (h i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group a compatibility-constrained Pi-tsum by verdict tuple and Tonelli-factor
each fiber (the abstract core of `seriesSum_cut_conv`). -/
private lemma tsum_subtype_pi_group {k : ℕ} {V : Type*} (D : Fin k → Type*)
    (dv : ∀ i, D i → V) (w : ∀ i, D i → ℝ≥0∞) (P : (Fin k → V) → Prop) :
    ∑' g : {g : ∀ i, D i // P (fun i => dv i (g i))}, ∏ i, w i (g.1 i)
      = ∑' vt : {vt : Fin k → V // P vt},
          ∏ i, ∑' d : {d : D i // dv i d = vt.1 i}, w i d.1 := by
  refine Eq.trans ((Equiv.sigmaFiberEquiv (verdictTuple dv P)).tsum_eq
    (fun g => ∏ i, w i (g.1 i))).symm ?_
  refine Eq.trans (ENNReal.tsum_sigma' _) ?_
  refine tsum_congr fun vt => ?_
  refine Eq.trans ?_ (tsum_pi_prod _ _ (fun i (d : {d : D i // dv i d = vt.1 i}) => w i d.1))
  exact (fiberPiEquiv D dv P vt).tsum_eq (fun h => ∏ i, w i ((h i).1))

/-! ## The verbatim H8-A3 block (blueprint §4, Wave 1) -/

/-- THE (K-CUT) SEAM DATA over the [3t] series carrier: a countable FULL-DATA
shallow-layer family, per-slot block-derivation types, and the weight-preserving
cut equivalence — M04 Lemma 3.3's hypothesis, typed.  `V` is the verdict monoid
(corpus instance: `Multiset (ℕ × ℕ)` via `VTree.typemult`).  GRANULARITY: §1.1
(full-data; the height-forgotten resummation is CL-17(ii)/W17ii, NOT here). -/
structure CutData {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) (V : Type*) [AddCommMonoid V] where
  vOf : LeanUrat.MovesU.SplittingType n → V
  ShL : Type
  ctblS : Countable ShL
  k : ShL → ℕ
  W : ShL → ℝ≥0∞
  σ0 : ShL → V
  Deriv : (Ŝ : ShL) → Fin (k Ŝ) → Type
  ctblD : ∀ Ŝ i, Countable (Deriv Ŝ i)
  dverdict : ∀ Ŝ i, Deriv Ŝ i → V
  weight : ∀ Ŝ i, Deriv Ŝ i → ℝ≥0∞
  /-- the EXACTLY-ONE decomposition, BOTH directions (an `Equiv`: cut ∘ graft =
  id ∧ graft ∘ cut = id), verdict-compatible fibers only. -/
  cut : ∀ σ, Fb.Tree σ ≃
    {x : Σ Ŝ : ShL, ∀ i : Fin (k Ŝ), Deriv Ŝ i //
      σ0 x.1 + ∑ i, dverdict x.1 i (x.2 i) = vOf σ}
  /-- weight preservation μ(fiber T) = W(Ŝ)·∏ᵢ weight(Dᵢ) — the row's (†). -/
  mass_eq : ∀ σ (T : Fb.Tree σ),
    Fb.mass σ T = W ((cut σ T).1.1) * ∏ i, weight _ i (((cut σ T).1.2) i)

/-- The per-slot block total B_{e_i,τ_i}(v) := Σ_{D : verdict D = v} weight D. -/
noncomputable def CutData.blockTotal {n p : ℕ}
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    (CD : CutData Fb V) (Ŝ : CD.ShL) (i : Fin (CD.k Ŝ)) (v : V) : ℝ≥0∞ :=
  ∑' D : {D : CD.Deriv Ŝ i // CD.dverdict Ŝ i D = v}, CD.weight Ŝ i D.1

/-- M04 LEMMA 3.3, Lean form, step 1: regroup the fiber series along the cut. -/
theorem seriesSum_cut {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    (CD : CutData Fb V) (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : CD.ShL, CD.W Ŝ *
          ∑' g : {g : ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
              CD.σ0 Ŝ + ∑ i, CD.dverdict Ŝ i (g i) = CD.vOf σ},
            ∏ i, CD.weight Ŝ i (g.1 i) := by
  classical
  calc Fb.seriesSum σ
      = ∑' T : Fb.Tree σ,
          CD.W ((CD.cut σ T).1.1) * ∏ i, CD.weight ((CD.cut σ T).1.1) i ((CD.cut σ T).1.2 i) :=
        tsum_congr fun T => CD.mass_eq σ T
    _ = ∑' x : {x : Σ Ŝ : CD.ShL, ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
            CD.σ0 x.1 + ∑ i, CD.dverdict x.1 i (x.2 i) = CD.vOf σ},
          CD.W x.1.1 * ∏ i, CD.weight x.1.1 i (x.1.2 i) :=
        (CD.cut σ).tsum_eq (fun x => CD.W x.1.1 * ∏ i, CD.weight x.1.1 i (x.1.2 i))
    _ = ∑' y : Σ Ŝ : CD.ShL, {g : ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
            CD.σ0 Ŝ + ∑ i, CD.dverdict Ŝ i (g i) = CD.vOf σ},
          CD.W y.1 * ∏ i, CD.weight y.1 i (y.2.1 i) :=
        (sigmaSubtypeShuffle (fun x : Σ Ŝ : CD.ShL, ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i =>
            CD.σ0 x.1 + ∑ i, CD.dverdict x.1 i (x.2 i) = CD.vOf σ)).tsum_eq
          (fun y => CD.W y.1 * ∏ i, CD.weight y.1 i (y.2.1 i))
    _ = ∑' Ŝ : CD.ShL, ∑' g : {g : ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
            CD.σ0 Ŝ + ∑ i, CD.dverdict Ŝ i (g i) = CD.vOf σ},
          CD.W Ŝ * ∏ i, CD.weight Ŝ i (g.1 i) :=
        ENNReal.tsum_sigma' _
    _ = ∑' Ŝ : CD.ShL, CD.W Ŝ * ∑' g : {g : ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
            CD.σ0 Ŝ + ∑ i, CD.dverdict Ŝ i (g i) = CD.vOf σ},
          ∏ i, CD.weight Ŝ i (g.1 i) :=
        tsum_congr fun Ŝ => ENNReal.tsum_mul_left

/-- M04 LEMMA 3.3, Lean form, step 2: group by verdict tuple + Tonelli-factor —
the SHALLOW CONVOLUTION of the block totals (the K1 regroup Step 18 consumes). -/
theorem seriesSum_cut_conv {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    [DecidableEq V] (CD : CutData Fb V) (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : CD.ShL, CD.W Ŝ *
          ∑' vt : {vt : Fin (CD.k Ŝ) → V //
              CD.σ0 Ŝ + ∑ i, vt i = CD.vOf σ},
            ∏ i, CD.blockTotal Ŝ i (vt.1 i) := by
  classical
  rw [seriesSum_cut CD σ]
  refine tsum_congr fun Ŝ => congrArg (fun z => CD.W Ŝ * z) ?_
  exact tsum_subtype_pi_group (CD.Deriv Ŝ) (CD.dverdict Ŝ) (CD.weight Ŝ)
    (fun vt => CD.σ0 Ŝ + ∑ i, vt i = CD.vOf σ)

end LeanUrat.Scaffold.HDischarge.H8
