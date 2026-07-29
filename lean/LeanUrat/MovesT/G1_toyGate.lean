/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.MovesC.C0_digitSystemMass

/-! # T-G1 `toy_treeExp_gate` [split G1a/G1b] — the two pinned toy carriers (§T-G1's
REV-8 full-roster tables) + the gate battery (DO-3). GATE ARCHITECTURE (REV 2, Fable
GAP-6): finite surrogate + hand bridge; no `by decide` on `Set`/`History`-quantified
Props.

E-PHASE RECORD (DO-1, honest census): the six HISTORY pins reduce to THREE distinct
`Node` literals — the REV-8 tables' data columns coincide across carriers
(tAν₁ = tBν₁ =: `toyHead`; tAνa = tBνc =: `toyLeafA`; tAνb = tBνd =: `toyLeafB`).
Every DATA field is the table's literal. Proof-field census per literal: all
arithmetic/species/ψ/pattern/anchor/line fields PROVED (`norm_num`/`decide`-genre,
incl. the ψ-order walk via the char-2 identity); the ONE remaining sorry per literal
is `hDwidth : Dwidth = σ.Φ.natDegree` — it reads the σ pin `toyStage`, whose
construction (the level-0 stage of polTriv's run, K = ZMod 2 as `⊤`) is the standing
G1b-genre obligation below (`toyStage`; cf. the built 600-line `bStage : Stage 2 F4`
precedent, HC2/U31 — a genuine sub-project, honestly OPEN). The model/CA proof
fields and the gate battery are G1a/G1b obligations, sorried with the DAY-ONE duty
recorded: if `fiberAt`/`SibCount` over-strengthen, these toys die first. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! #### toyStage proof infrastructure (P-phase fill, 2026-07-29): TRANSPORT of the
BUILT `LeanUrat.MovesJ.U31.bStage : Stage 2 F4` (the HC2/U31 (1,1)-diagonal Gauss
stage at Φ = X — the 600-line precedent the docstring below cites) along the
coefficient-field isomorphism `↥K2 ≃+* ↥(⊤ : Subfield (ZMod 2))`. The w-side laws
(hwmul/hwult/hvalgrp/hK1/hStretch/hWS) copy VERBATIM — the valuation `bw` is
unchanged; the R-side laws push through the induced Laurent-ring isomorphism `ΛT`.
Helper defs/lemmas only; no blueprint statement is touched. -/
section ToyStageTransport

open LeanUrat.MovesJ.U31 in
private lemma ρ₁_bij : Function.Bijective (ρ₁ : ZMod 2 →+* ↥K2) := by
  refine ⟨ρ₁.injective, fun x => ?_⟩
  obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp x.2
  exact ⟨z, Subtype.ext hz⟩

open LeanUrat.MovesJ.U31 in
/-- the two-element coefficient isomorphism `↥K2 ≃+* ↥(⊤ : Subfield (ZMod 2))`. -/
private noncomputable def κT : ↥K2 ≃+* ↥(⊤ : Subfield (ZMod 2)) :=
  (RingEquiv.ofBijective ρ₁ ρ₁_bij).symm.trans Subfield.topEquiv.symm

open LeanUrat.MovesJ.U31 in
/-- the induced Laurent-polynomial ring isomorphism. -/
private noncomputable def ΛT :
    LaurentPolynomial ↥K2 ≃+* LaurentPolynomial ↥(⊤ : Subfield (ZMod 2)) :=
  AddMonoidAlgebra.mapRingEquiv ℤ κT

private lemma ΛT_apply (x : LaurentPolynomial ↥LeanUrat.MovesJ.U31.K2) :
    ΛT x = AddMonoidAlgebra.mapRingHom ℤ (κT : ↥LeanUrat.MovesJ.U31.K2 →+* _) x := by
  rw [show (AddMonoidAlgebra.mapRingHom ℤ (κT : ↥LeanUrat.MovesJ.U31.K2 →+* _))
      = ΛT.toRingHom from (AddMonoidAlgebra.toRingHom_mapRingEquiv κT).symm]
  rfl

private lemma ΛT_C_T (c : ↥LeanUrat.MovesJ.U31.K2) (k : ℤ) :
    ΛT (LaurentPolynomial.C c * LaurentPolynomial.T k)
      = LaurentPolynomial.C (κT c) * LaurentPolynomial.T k := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
    ΛT_apply, AddMonoidAlgebra.mapRingHom_single]
  rfl

private lemma ΛT_T (k : ℤ) :
    ΛT (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  have h := ΛT_C_T 1 k
  rw [map_one] at h
  simpa using h

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
/-- `bStage`'s residual laws, restated at the `bw`/`bR`/`K2` phrasing (term-level
defeq — `bStage`'s fields ARE these values). -/
private lemma bR0' : bR 0 = 0 := bStage.hR0

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bRne' : ∀ f, f ≠ 0 → bR f ≠ 0 := bStage.hRne

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bRmul' : ∀ f g, f ≠ 0 → g ≠ 0 → bR (f * g) = bR f * bR g := bStage.hRmul

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bRadd' : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → bw f = bw g →
    bw (f + g) = bw f → bR (f + g) = bR f + bR g := bStage.hRadd

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bRlt' : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → bw f < bw g →
    bR (f + g) = bR f := bStage.hRlt

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bRX' : bR Polynomial.X = LaurentPolynomial.T 1 := bStage.hRΦ

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bS5' : ∀ B, B ≠ 0 → inC Polynomial.X B →
    ∃ c : (↥K2)ˣ, bR B = LaurentPolynomial.C (c : ↥K2)
      * LaurentPolynomial.T (-(0 : ℤ) * bw B) := bStage.hS5

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bS6a' : ∀ ν : ℤ, ν ∈ bStage.weightSet →
    ∃ b : (↥K2)ˣ, ∀ c : (↥K2)ˣ, ((c : ↥K2) : F4) ∈ K2 →
      ∃ B, B ≠ 0 ∧ inC Polynomial.X B ∧ bw B = ν ∧
        bR B = LaurentPolynomial.C ((c * b : (↥K2)ˣ) : ↥K2)
          * LaurentPolynomial.T (-(0 : ℤ) * ν) := bStage.hS6a

open LeanUrat.MovesJ LeanUrat.MovesJ.U31 in
private lemma bS6b' : ∀ (ν : ℤ) (a : (↥K2)ˣ), bw Polynomial.X < ν →
    ∃ B, B ≠ 0 ∧ inC Polynomial.X B ∧ bw B = ν ∧
      bR B = LaurentPolynomial.C (a : ↥K2)
        * LaurentPolynomial.T (-(0 : ℤ) * ν) := bStage.hS6b

end ToyStageTransport

/-- the level-0 stage of `polTriv`'s run over K = ZMod 2 — OPEN construction
obligation (the `bStage` precedent: Gauss valuation + residual apparatus, HC2/U31).
The §T-G1 read-surface obligation is `card ↥toyStage.K = 2` (`toyStage_card` below). -/
noncomputable def toyStage : Stage 2 (ZMod 2) :=
  open LeanUrat.MovesJ.U31 in
  { e := 1, h := 1, s := 1, t := 0,
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num, hbez := by norm_num,
    he1t := fun _ => rfl,
    Φ := Polynomial.X,
    hmonic := monic_X,
    hdeg := le_of_eq natDegree_X.symm,
    w := bw, wPrev := bw,
    K := ⊤, FQ := ⊤, hFQ_le := le_rfl,
    R := fun f => ΛT (bR f),
    hwmul := bStage.hwmul,
    hwult := bStage.hwult,
    hvalgrp := bStage.hvalgrp,
    hwΦ := bStage.hwΦ,
    hStretch := bStage.hStretch,
    hR0 := by rw [bR0', map_zero],
    hRne := fun f hf h0 =>
      bRne' f hf (ΛT.injective (h0.trans (map_zero ΛT).symm)),
    hRmul := fun f g hf hg => by rw [bRmul' f g hf hg, map_mul],
    hRadd := fun f g hf hg hfg hw hw' => by rw [bRadd' f g hf hg hfg hw hw', map_add],
    hRlt := fun f g hf hg hfg hlt => by rw [bRlt' f g hf hg hfg hlt],
    hRΦ := by rw [bRX', ΛT_T],
    hK1 := bStage.hK1,
    hS5 := fun B hB hin => by
      obtain ⟨c, hc⟩ := bS5' B hB hin
      refine ⟨Units.map (κT : ↥K2 →+* _).toMonoidHom c, ?_⟩
      rw [hc, ΛT_C_T]
      rfl,
    reps := [], hreps := by simp,
    Tvec := [], hTvec := rfl,
    weightSet := bStage.weightSet,
    hWS := bStage.hWS,
    hS6a := fun ν hν => by
      obtain ⟨b, hb⟩ := bS6a' ν hν
      refine ⟨Units.map (κT : ↥K2 →+* _).toMonoidHom b, fun c _hc => ?_⟩
      obtain ⟨B, hB, hin, hw, hR⟩ :=
        hb (Units.map (κT.symm : ↥(⊤ : Subfield (ZMod 2)) →+* ↥K2).toMonoidHom c)
          (SetLike.coe_mem _)
      refine ⟨B, hB, hin, hw, ?_⟩
      rw [hR, ΛT_C_T]
      congr 2
      rw [Units.val_mul, map_mul]
      congr 1
      exact κT.apply_symm_apply _,
    hS6b := fun ν a hν => by
      obtain ⟨B, hB, hin, hw, hR⟩ :=
        bS6b' ν (Units.map (κT.symm : ↥(⊤ : Subfield (ZMod 2)) →+* ↥K2).toMonoidHom a) hν
      refine ⟨B, hB, hin, hw, ?_⟩
      rw [hR, ΛT_C_T]
      congr 2
      exact κT.apply_symm_apply _ }

/-- the ONE non-literal pin's displayed read-surface obligation (§T-G1). -/
theorem toyStage_card : Nat.card ↥toyStage.K = 2 := by
  rw [show toyStage.K = (⊤ : Subfield (ZMod 2)) from rfl,
    Nat.card_congr Subfield.topEquiv.toEquiv, Nat.card_zmod]

/-- the char-2 identity in the stage's residue field (a subfield of ZMod 2). -/
theorem toyK_two_eq_zero : (2 : ↥toyStage.K) = 0 := by
  have h : (1 + 1 : ↥toyStage.K) = 0 := by
    apply Subtype.ext
    push_cast
    decide
  calc (2 : ↥toyStage.K) = 1 + 1 := by norm_num
  _ = 0 := h

theorem toyK_two_poly : (2 : Polynomial ↥toyStage.K) = 0 := by
  have h2 : (2 : Polynomial ↥toyStage.K) = Polynomial.C (2 : ↥toyStage.K) :=
    Eq.symm (Polynomial.C_ofNat 2)
  rw [h2, toyK_two_eq_zero, map_zero]

/-- `X - C 1 = X + 1` in char 2. -/
theorem toyK_X_sub_C : (X - Polynomial.C 1 : Polynomial ↥toyStage.K) = X + 1 := by
  have h1 : (Polynomial.C (1 : ↥toyStage.K) : Polynomial ↥toyStage.K) = 1 := map_one _
  rw [h1]
  linear_combination -toyK_two_poly

/-- `(X + 1)² = 1 + X²` in char 2. -/
theorem toyK_add_sq : ((X + 1 : Polynomial ↥toyStage.K)) ^ 2 = 1 + X ^ 2 := by
  linear_combination X * toyK_two_poly

/-- `(X − C 1)² = 1 + X²` — the head's ψ-order identity. -/
theorem toyK_head_ord : (X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ 2 = 1 + X ^ 2 := by
  rw [toyK_X_sub_C]
  exact toyK_add_sq

/-- `(X − C 1)¹ = 1 + X` — the leaves' ψ-order identity. -/
theorem toyK_leaf_ord : (X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ 1 = 1 + X := by
  rw [pow_one, toyK_X_sub_C]
  ring

/-- **the HEAD node literal** (tAν₁ = tBν₁ — the REV-8 table column): root species,
(e,h,s,t) = (1,1,1,0), (g,μ) = (1,2), (s0,wSide,Dwidth) = (0,2,1), line ⟨3,1⟩,
u* = 1, γ = 3, ψ = X − C 1, pat = (1,0,1), Ranch = 1 + X². -/
noncomputable def toyHead : Node 2 (ZMod 2) :=
  { species := ReadSpecies.root, σ := toyStage,
    e := 1, h := 1, s := 1, t := 0, g := 1, μ := 2, a := 0,
    s0 := 0, wSide := 2, Dwidth := 1,
    line := ⟨3, 1⟩, ustar := 1, gam := 3,
    zbar := 1, center := 1, lift := Polynomial.X,
    ψ := X - Polynomial.C 1,
    pat := fun k => if k = 1 then 0 else 1,
    Ranch := 1 + X ^ 2,
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num,
    hbez := by norm_num, hbezCanon := by norm_num,
    hg := le_refl 1, hμ := by norm_num, hEdvd := one_dvd 2,
    hDwidth := by
      rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
        Polynomial.natDegree_X],
    hψmonic := monic_X_sub_C 1, hψdeg := natDegree_X_sub_C 1,
    hψirr := irreducible_X_sub_C 1,
    hRanch := by
      norm_num [Finset.sum_range_succ],
    hpat0 := by norm_num,
    hpatTop := by norm_num,
    hAnchor := by norm_num,
    hLineU := by norm_num [Line.at],
    hOrd := by
      constructor
      · exact toyK_head_ord.dvd
      · intro hdvd
        have hne : (1 + X ^ 2 : Polynomial ↥toyStage.K) ≠ 0 := by
          rw [← toyK_head_ord]
          exact pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero 1)
        have hle := Polynomial.natDegree_le_of_dvd hdvd hne
        have h3 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (2 + 1)).natDegree = 3 := by
          rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
        have h2' : (1 + X ^ 2 : Polynomial ↥toyStage.K).natDegree ≤ 2 := by
          apply le_trans (Polynomial.natDegree_add_le _ _)
          simp
        omega,
    hzbarRoot := by simp,
    hspecInc := by intro h; simp at h,
    hspecRec := by intro h; simp at h,
    hspecRecCenter := by intro h; simp at h }

/-- **the LEAF-a node literal** (tAνa = tBνc): recentering species, h = 2,
line ⟨4,2⟩, u* = 2, γ = 4, μ = 1, wSide = 1, pat ≡ 1, Ranch = 1 + X. -/
noncomputable def toyLeafA : Node 2 (ZMod 2) :=
  { species := ReadSpecies.recentering, σ := toyStage,
    e := 1, h := 2, s := 1, t := 0, g := 1, μ := 1, a := 0,
    s0 := 0, wSide := 1, Dwidth := 1,
    line := ⟨4, 2⟩, ustar := 2, gam := 4,
    zbar := 1, center := 1, lift := Polynomial.X,
    ψ := X - Polynomial.C 1,
    pat := fun _ => 1,
    Ranch := 1 + X,
    he := le_refl 1, hh := by norm_num, hcop := by norm_num,
    hbez := by norm_num, hbezCanon := by norm_num,
    hg := le_refl 1, hμ := le_refl 1, hEdvd := one_dvd 1,
    hDwidth := by
      rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
        Polynomial.natDegree_X],
    hψmonic := monic_X_sub_C 1, hψdeg := natDegree_X_sub_C 1,
    hψirr := irreducible_X_sub_C 1,
    hRanch := by
      norm_num [Finset.sum_range_succ],
    hpat0 := one_ne_zero,
    hpatTop := one_ne_zero,
    hAnchor := by norm_num,
    hLineU := by norm_num [Line.at],
    hOrd := by
      constructor
      · exact toyK_leaf_ord.dvd
      · intro hdvd
        have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
          rw [← toyK_leaf_ord]
          exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
        have hle := Polynomial.natDegree_le_of_dvd hdvd hne
        have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
          rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
        have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
          apply le_trans (Polynomial.natDegree_add_le _ _)
          simp
        omega,
    hzbarRoot := by simp,
    hspecInc := by intro h; simp at h,
    hspecRec := fun _ => ⟨rfl, rfl⟩,
    hspecRecCenter := fun _ => ⟨rfl, by simp⟩ }

/-- **the LEAF-b node literal** (tAνb = tBνd): as leaf a with h = 3, line ⟨6,3⟩,
u* = 3, γ = 6. -/
noncomputable def toyLeafB : Node 2 (ZMod 2) :=
  { species := ReadSpecies.recentering, σ := toyStage,
    e := 1, h := 3, s := 1, t := 0, g := 1, μ := 1, a := 0,
    s0 := 0, wSide := 1, Dwidth := 1,
    line := ⟨6, 3⟩, ustar := 3, gam := 6,
    zbar := 1, center := 1, lift := Polynomial.X,
    ψ := X - Polynomial.C 1,
    pat := fun _ => 1,
    Ranch := 1 + X,
    he := le_refl 1, hh := by norm_num, hcop := by norm_num,
    hbez := by norm_num, hbezCanon := by norm_num,
    hg := le_refl 1, hμ := le_refl 1, hEdvd := one_dvd 1,
    hDwidth := by
      rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
        Polynomial.natDegree_X],
    hψmonic := monic_X_sub_C 1, hψdeg := natDegree_X_sub_C 1,
    hψirr := irreducible_X_sub_C 1,
    hRanch := by
      norm_num [Finset.sum_range_succ],
    hpat0 := one_ne_zero,
    hpatTop := one_ne_zero,
    hAnchor := by norm_num,
    hLineU := by norm_num [Line.at],
    hOrd := by
      constructor
      · exact toyK_leaf_ord.dvd
      · intro hdvd
        have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
          rw [← toyK_leaf_ord]
          exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
        have hle := Polynomial.natDegree_le_of_dvd hdvd hne
        have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
          rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
        have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
          apply le_trans (Polynomial.natDegree_add_le _ _)
          simp
        omega,
    hzbarRoot := by simp,
    hspecInc := by intro h; simp at h,
    hspecRec := fun _ => ⟨rfl, rfl⟩,
    hspecRecCenter := fun _ => ⟨rfl, by simp⟩ }

-- the blueprint's table names, bound to the three literals
noncomputable abbrev tAν₁ := toyHead
noncomputable abbrev tAνa := toyLeafA
noncomputable abbrev tAνb := toyLeafB
noncomputable abbrev tBν₁ := toyHead
noncomputable abbrev tBνc := toyLeafA
noncomputable abbrev tBνd := toyLeafB

theorem toyHead_root : ChildRoot none toyHead := rfl

theorem toyLeafA_nonroot : toyLeafA.species ≠ ReadSpecies.root := by
  intro h; simp [toyLeafA] at h

theorem toyLeafB_nonroot : toyLeafB.species ≠ ReadSpecies.root := by
  intro h; simp [toyLeafB] at h

/-- the six HISTORY pins (DO-1) via `oneNode`/`snoc`. -/
noncomputable def tA1 : History 2 (ZMod 2) := oneNode toyHead toyHead_root
noncomputable def tA2a : History 2 (ZMod 2) := tA1.snoc toyLeafA toyLeafA_nonroot
noncomputable def tA2b : History 2 (ZMod 2) := tA1.snoc toyLeafB toyLeafB_nonroot
noncomputable def tB1 : History 2 (ZMod 2) := tA1
noncomputable def tB2c : History 2 (ZMod 2) := tA2a
noncomputable def tB2d : History 2 (ZMod 2) := tA2b

/-! #### pin-distinctness / snoc-decomposition proof infrastructure (P-phase fill;
private helpers only — no blueprint statement touched). -/
section ToyPinHelpers

private lemma hist_ext {H H' : History 2 (ZMod 2)} (h : H.nodes = H'.nodes) :
    H = H' := by
  obtain ⟨n, hne, hri⟩ := H
  obtain ⟨n', hne', hri'⟩ := H'
  subst h
  rfl

private lemma head_ne_leafA : toyHead ≠ toyLeafA := fun h => by
  have h2 : ReadSpecies.root = ReadSpecies.recentering := congrArg Node.species h
  exact absurd h2 (by decide)

private lemma head_ne_leafB : toyHead ≠ toyLeafB := fun h => by
  have h2 : ReadSpecies.root = ReadSpecies.recentering := congrArg Node.species h
  exact absurd h2 (by decide)

private lemma leafA_ne_leafB : toyLeafA ≠ toyLeafB := fun h => by
  have h2 : (2 : ℕ) = 3 := congrArg Node.h h
  omega

private lemma tA1_nodes : tA1.nodes = [toyHead] := rfl
private lemma tA2a_nodes : tA2a.nodes = [toyHead, toyLeafA] := rfl
private lemma tA2b_nodes : tA2b.nodes = [toyHead, toyLeafB] := rfl

private lemma tA1_ne_tA2a : tA1 ≠ tA2a := fun h => by
  have h2 : (1 : ℕ) = 2 :=
    congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) h
  omega

private lemma tA1_ne_tA2b : tA1 ≠ tA2b := fun h => by
  have h2 : (1 : ℕ) = 2 :=
    congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) h
  omega

private lemma tA2a_ne_tA2b : tA2a ≠ tA2b := fun h => by
  have h2 : ([toyHead, toyLeafA] : List (Node 2 (ZMod 2)))
      = [toyHead, toyLeafB] := congrArg History.nodes h
  simp only [List.cons.injEq, and_true, true_and] at h2
  exact leafA_ne_leafB h2

private lemma snoc_ne_tA1 (H : History 2 (ZMod 2)) (ν : Node 2 (ZMod 2))
    (hν : ν.species ≠ ReadSpecies.root) : H.snoc ν hν ≠ tA1 := fun h => by
  have h2 : H.nodes.length + 1 = 1 := by
    have := congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) h
    simpa [History.snoc, tA1_nodes] using this
  have h3 : H.nodes = [] := List.length_eq_zero_iff.mp (by omega)
  exact H.nonempty h3

private lemma snoc_eq_two {H : History 2 (ZMod 2)} {ν a b : Node 2 (ZMod 2)}
    {hν : ν.species ≠ ReadSpecies.root}
    (h : (H.snoc ν hν).nodes = [a, b]) : H.nodes = [a] ∧ ν = b := by
  have h1 : H.nodes ++ [ν] = [a] ++ [b] := h
  have h2 := List.append_inj' h1 rfl
  exact ⟨h2.1, by simpa using h2.2⟩

private lemma snoc_eq_tA2a_iff {H : History 2 (ZMod 2)} {ν : Node 2 (ZMod 2)}
    {hν : ν.species ≠ ReadSpecies.root} :
    H.snoc ν hν = tA2a ↔ (H = tA1 ∧ ν = toyLeafA) := by
  constructor
  · intro h
    obtain ⟨hH, hν'⟩ := snoc_eq_two
      (show (H.snoc ν hν).nodes = [toyHead, toyLeafA] from congrArg History.nodes h)
    exact ⟨hist_ext (hH.trans tA1_nodes.symm), hν'⟩
  · rintro ⟨h1, h2⟩
    refine hist_ext ?_
    show H.nodes ++ [ν] = tA2a.nodes
    rw [congrArg History.nodes h1, h2]
    rfl

private lemma snoc_eq_tA2b_iff {H : History 2 (ZMod 2)} {ν : Node 2 (ZMod 2)}
    {hν : ν.species ≠ ReadSpecies.root} :
    H.snoc ν hν = tA2b ↔ (H = tA1 ∧ ν = toyLeafB) := by
  constructor
  · intro h
    obtain ⟨hH, hν'⟩ := snoc_eq_two
      (show (H.snoc ν hν).nodes = [toyHead, toyLeafB] from congrArg History.nodes h)
    exact ⟨hist_ext (hH.trans tA1_nodes.symm), hν'⟩
  · rintro ⟨h1, h2⟩
    refine hist_ext ?_
    show H.nodes ++ [ν] = tA2b.nodes
    rw [congrArg History.nodes h1, h2]
    rfl

end ToyPinHelpers

/-- the toy cell alphabet (IP-2: `deriving DecidableEq`). -/
inductive ToyCell | rootC | winC | splitC | junk
  deriving DecidableEq

instance : Fintype ToyCell :=
  ⟨⟨{.rootC, .winC, .splitC, .junk}, by decide⟩, fun c => by cases c <;> decide⟩

/-! ### carrier A tables (REV 6/7 pins: winC guards read ψ AND the reduction coords;
cellLevel = 4) -/

open Classical in
noncomputable def toyMemA : Option (History 2 (ZMod 2)) → Box 2 9 → Prop
  | none, _ => True
  | some H, x => (H = tA1 ∨ H = tA2a ∨ H = tA2b) ∧
      x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0

open Classical in
noncomputable def toyChildA :
    Option (History 2 (ZMod 2)) → Node 2 (ZMod 2) → Box 2 9 → Prop
  | none, ν, x => ν = toyHead ∧ x 0 = 0 ∧ x 1 = 0 ∧
      x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0
  | some H, ν, x => H = tA1 ∧ (ν = toyLeafA ∨ ν = toyLeafB) ∧ toyMemA (some tA1) x

open Classical in
noncomputable def toyModel : TreeModel 2 (ZMod 2) 2 3 9 polTriv where
  mem := toyMemA
  child := toyChildA
  root_mem := fun _ => trivial
  mem_single := by
    intro ν h1 x
    constructor
    · rintro ⟨hH | hH | hH, hd⟩
      · have hν : ν = toyHead := by
          have h2 : [ν] = [toyHead] := congrArg History.nodes hH
          simpa using h2
        exact ⟨hν, hd⟩
      · exfalso
        have h2 : (1 : ℕ) = 2 :=
          congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) hH
        omega
      · exfalso
        have h2 : (1 : ℕ) = 2 :=
          congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) hH
        omega
    · rintro ⟨hν, hd⟩
      exact ⟨Or.inl (hist_ext (by rw [show ((⟨[ν], h1.1, h1.2⟩ : History 2 (ZMod 2))).nodes = [ν] from rfl, hν]; rfl)), hd⟩
  mem_snoc := by
    intro H ν hν x
    constructor
    · rintro ⟨hH | hH | hH, hd⟩
      · exact absurd hH (snoc_ne_tA1 H ν hν)
      · obtain ⟨h1, h2⟩ := snoc_eq_tA2a_iff.mp hH
        exact ⟨⟨Or.inl h1, hd⟩, h1, Or.inl h2, ⟨Or.inl rfl, hd⟩⟩
      · obtain ⟨h1, h2⟩ := snoc_eq_tA2b_iff.mp hH
        exact ⟨⟨Or.inl h1, hd⟩, h1, Or.inr h2, ⟨Or.inl rfl, hd⟩⟩
    · rintro ⟨⟨-, hd⟩, h1, hν2, -⟩
      rcases hν2 with h2 | h2
      · exact ⟨Or.inr (Or.inl (snoc_eq_tA2a_iff.mpr ⟨h1, h2⟩)), hd⟩
      · exact ⟨Or.inr (Or.inr (snoc_eq_tA2b_iff.mpr ⟨h1, h2⟩)), hd⟩
  mem_realizable := by sorry
  -- [G1b split (REV 8, Codex-7 #4d): `mem_realizable`'s node-level legs are walked
  --  lawful at the tables; the TRANSITION legs are the DISCLOSED §6 obligation row]

open Classical in
noncomputable def toyCellA : EntSt 2 (ZMod 2) 2 → Box 2 9 → ToyCell
  | .amb, x => if x 0 = 0 ∧ x 1 = 0 then .rootC else .junk
  | .red _ ψ, x => if ψ = Polynomial.X ∧ x 0 = 0 ∧ x 1 = 0
      ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0
      then .winC else .junk
  | .st H, x => if H = tA1 ∧ toyMemA (some tA1) x then .splitC else .junk

open Classical in
noncomputable def toyBranchA : ToyCell → Finset (Node 2 (ZMod 2))
  | .rootC => {toyHead}
  | .winC => {toyHead}
  | .splitC => {toyLeafA, toyLeafB}
  | .junk => ∅

open Classical in
noncomputable def toyCA : CellData 2 (ZMod 2) 2 3 9 polTriv toyModel where
  Cell := ToyCell
  hCellFin := inferInstance
  cellOf := toyCellA
  cellLevel := fun _ => 4
  levelOf := levelIdx (n := 2)
  cell_local := by
    intro es x x' h
    have h0 := h 0 (by decide); have h1 := h 1 (by decide)
    have h2 := h 2 (by decide); have h3 := h 3 (by decide)
    have h4 := h 4 (by decide); have h5 := h 5 (by decide)
    cases es <;> simp only [toyCellA, toyMemA, h0, h1, h2, h3, h4, h5]
  branchSetOf := toyBranchA
  child_cell := by
    intro H ν x hmem
    obtain ⟨hH, hd⟩ := hmem
    rcases hH with h1 | h1 | h1
    · subst h1
      have hcell : toyCellA (.st tA1) x = ToyCell.splitC := by
        simp only [toyCellA]
        rw [if_pos ⟨trivial, Or.inl rfl, hd⟩]
      rw [hcell]
      simp only [toyBranchA, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hν, -⟩
        exact hν
      · intro hν
        exact ⟨rfl, hν, Or.inl rfl, hd⟩
    · subst h1
      have hcell : toyCellA (.st tA2a) x = ToyCell.junk := by
        simp only [toyCellA]
        rw [if_neg (fun hc => tA1_ne_tA2a hc.1.symm)]
      rw [hcell]
      simp only [toyBranchA, Finset.notMem_empty, iff_false]
      rintro ⟨hc, -, -⟩
      exact tA1_ne_tA2a hc.symm
    · subst h1
      have hcell : toyCellA (.st tA2b) x = ToyCell.junk := by
        simp only [toyCellA]
        rw [if_neg (fun hc => tA1_ne_tA2b hc.1.symm)]
      rw [hcell]
      simp only [toyBranchA, Finset.notMem_empty, iff_false]
      rintro ⟨hc, -, -⟩
      exact tA1_ne_tA2b hc.symm
  child_root_sub := by
    rintro ν x ⟨hν, hd⟩
    subst hν
    have hcell : toyCellA .amb x = ToyCell.rootC := by
      simp only [toyCellA]
      rw [if_pos ⟨hd.1, hd.2.1⟩]
    rw [hcell]
    simp [toyBranchA]
  child_cell_red := by
    intro χ g ψ ν x hx hν
    by_cases hguard : ψ = Polynomial.X ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
        ∧ x 4 = 0 ∧ x 5 = 0
    · have hcell : toyCellA (.red g ψ) x = ToyCell.winC := by
        simp only [toyCellA]
        rw [if_pos hguard]
      rw [hcell] at hν
      simp only [toyBranchA, Finset.mem_singleton] at hν
      exact ⟨hν, hguard.2⟩
    · have hcell : toyCellA (.red g ψ) x = ToyCell.junk := by
        simp only [toyCellA]
        rw [if_neg hguard]
      rw [hcell] at hν
      simp [toyBranchA] at hν
  -- [REV 8 RE-FENCE (Codex-7 #1): the toys instantiate the DATA layer `CellData`
  --  ONLY — `child_cover` FAILS on both carriers at g = (1,0) (deliberately partial;
  --  disclosed at §2.9/§6 and the §5 W4-1 row)]

/-! ### carrier B tables -/

open Classical in
noncomputable def toyMemB : Option (History 2 (ZMod 2)) → Box 2 9 → Prop
  | none, _ => True
  | some H, x =>
      (H = tB1 ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0)
    ∨ ((H = tB2c ∨ H = tB2d) ∧
        x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0)

open Classical in
noncomputable def toyChildB :
    Option (History 2 (ZMod 2)) → Node 2 (ZMod 2) → Box 2 9 → Prop
  | none, ν, x => ν = toyHead ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0
  | some H, ν, x => H = tB1 ∧ (ν = toyLeafA ∨ ν = toyLeafB) ∧
      toyMemB (some tB1) x ∧ x 3 = 0 ∧ x 4 = 0

open Classical in
noncomputable def toyModelB : TreeModel 2 (ZMod 2) 2 3 9 polTriv where
  mem := toyMemB
  child := toyChildB
  root_mem := fun _ => trivial
  mem_single := by
    intro ν h1 x
    constructor
    · rintro (⟨hH, hd⟩ | ⟨hH, hd⟩)
      · have hν : ν = toyHead := by
          have h2 : [ν] = [toyHead] := congrArg History.nodes hH
          simpa using h2
        exact ⟨hν, hd⟩
      · exfalso
        rcases hH with hH | hH
        · have h2 : (1 : ℕ) = 2 :=
            congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) hH
          omega
        · have h2 : (1 : ℕ) = 2 :=
            congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) hH
          omega
    · rintro ⟨hν, hd⟩
      exact Or.inl ⟨hist_ext (by rw [show ((⟨[ν], h1.1, h1.2⟩ : History 2 (ZMod 2))).nodes = [ν] from rfl, hν]; rfl), hd⟩
  mem_snoc := by
    intro H ν hν x
    constructor
    · rintro (⟨hH, -⟩ | ⟨hH, hx0, hx1, hx2, hx3, hx4⟩)
      · exact absurd hH (snoc_ne_tA1 H ν hν)
      · rcases hH with hH | hH
        · obtain ⟨h1, h2⟩ := snoc_eq_tA2a_iff.mp hH
          exact ⟨Or.inl ⟨h1, hx0, hx1, hx2⟩,
            h1, Or.inl h2, Or.inl ⟨rfl, hx0, hx1, hx2⟩, hx3, hx4⟩
        · obtain ⟨h1, h2⟩ := snoc_eq_tA2b_iff.mp hH
          exact ⟨Or.inl ⟨h1, hx0, hx1, hx2⟩,
            h1, Or.inr h2, Or.inl ⟨rfl, hx0, hx1, hx2⟩, hx3, hx4⟩
    · rintro ⟨hm, h1, hν2, -, hx3, hx4⟩
      have hd : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
        rcases hm with ⟨-, hd⟩ | ⟨habs, -⟩
        · exact hd
        · exfalso
          rcases habs with habs | habs
          · exact tA1_ne_tA2a (h1.symm.trans habs)
          · exact tA1_ne_tA2b (h1.symm.trans habs)
      rcases hν2 with h2 | h2
      · exact Or.inr ⟨Or.inl (snoc_eq_tA2a_iff.mpr ⟨h1, h2⟩),
          hd.1, hd.2.1, hd.2.2, hx3, hx4⟩
      · exact Or.inr ⟨Or.inr (snoc_eq_tA2b_iff.mpr ⟨h1, h2⟩),
          hd.1, hd.2.1, hd.2.2, hx3, hx4⟩
  mem_realizable := by sorry

open Classical in
noncomputable def toyCellB : EntSt 2 (ZMod 2) 2 → Box 2 9 → ToyCell
  | .amb, x => if x 0 = 0 ∧ x 1 = 0 then .rootC else .junk
  | .red _ ψ, x => if ψ = Polynomial.X ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0
      then .winC else .junk
  | .st H, x => if H = tB1 ∧ x 3 = 0 ∧ x 4 = 0 then .splitC else .junk

open Classical in
noncomputable def toyBranchB : ToyCell → Finset (Node 2 (ZMod 2))
  | .rootC => {toyHead}
  | .winC => {toyHead}
  | .splitC => {toyLeafA, toyLeafB}
  | .junk => ∅

open Classical in
noncomputable def toyCAB : CellData 2 (ZMod 2) 2 3 9 polTriv toyModelB where
  Cell := ToyCell
  hCellFin := inferInstance
  cellOf := toyCellB
  cellLevel := fun _ => 4
  levelOf := levelIdx (n := 2)
  cell_local := by
    intro es x x' h
    have h0 := h 0 (by decide); have h1 := h 1 (by decide)
    have h2 := h 2 (by decide); have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    cases es <;> simp only [toyCellB, h0, h1, h2, h3, h4]
  branchSetOf := toyBranchB
  child_cell := by
    intro H ν x hmem
    have hHcase : H = tB1 ∨ H = tB2c ∨ H = tB2d := by
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rcases hHcase with h1 | h1 | h1
    · subst h1
      have hd : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
        rcases hmem with ⟨-, hd⟩ | ⟨habs, -⟩
        · exact hd
        · exfalso
          rcases habs with habs | habs
          · exact tA1_ne_tA2a habs
          · exact tA1_ne_tA2b habs
      by_cases hg : x 3 = 0 ∧ x 4 = 0
      · have hcell : toyCellB (.st tB1) x = ToyCell.splitC := by
          simp only [toyCellB]
          rw [if_pos ⟨trivial, hg.1, hg.2⟩]
        rw [hcell]
        simp only [toyBranchB, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hν, -⟩
          exact hν
        · intro hν
          exact ⟨rfl, hν, Or.inl ⟨rfl, hd⟩, hg.1, hg.2⟩
      · have hcell : toyCellB (.st tB1) x = ToyCell.junk := by
          simp only [toyCellB]
          rw [if_neg (fun hc => hg ⟨hc.2.1, hc.2.2⟩)]
        rw [hcell]
        simp only [toyBranchB, Finset.notMem_empty, iff_false]
        rintro ⟨-, -, -, hx3, hx4⟩
        exact hg ⟨hx3, hx4⟩
    · subst h1
      have hcell : toyCellB (.st tB2c) x = ToyCell.junk := by
        simp only [toyCellB]
        rw [if_neg (fun hc => tA1_ne_tA2a hc.1.symm)]
      rw [hcell]
      simp only [toyBranchB, Finset.notMem_empty, iff_false]
      rintro ⟨hc, -⟩
      exact tA1_ne_tA2a hc.symm
    · subst h1
      have hcell : toyCellB (.st tB2d) x = ToyCell.junk := by
        simp only [toyCellB]
        rw [if_neg (fun hc => tA1_ne_tA2b hc.1.symm)]
      rw [hcell]
      simp only [toyBranchB, Finset.notMem_empty, iff_false]
      rintro ⟨hc, -⟩
      exact tA1_ne_tA2b hc.symm
  child_root_sub := by
    rintro ν x ⟨hν, hx0, hx1, hx2⟩
    subst hν
    have hcell : toyCellB .amb x = ToyCell.rootC := by
      simp only [toyCellB]
      rw [if_pos ⟨hx0, hx1⟩]
    rw [hcell]
    simp [toyBranchB]
  child_cell_red := by
    intro χ g ψ ν x hx hν
    by_cases hguard : ψ = Polynomial.X ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0
    · have hcell : toyCellB (.red g ψ) x = ToyCell.winC := by
        simp only [toyCellB]
        rw [if_pos hguard]
      rw [hcell] at hν
      simp only [toyBranchB, Finset.mem_singleton] at hν
      exact ⟨hν, hguard.2⟩
    · have hcell : toyCellB (.red g ψ) x = ToyCell.junk := by
        simp only [toyCellB]
        rw [if_neg hguard]
      rw [hcell] at hν
      simp [toyBranchB] at hν

/-! ### the trees, the DO-2 plumbing, and the gate battery (G1a/G1b obligations) -/

/-! #### tree/ledger proof infrastructure (P-phase fill; private helpers only). -/
section ToyTreeHelpers

private lemma tA1_prefix_tA2a : tA1.IsPrefixOf tA2a := ⟨[toyLeafA], rfl⟩
private lemma tA1_prefix_tA2b : tA1.IsPrefixOf tA2b := ⟨[toyLeafB], rfl⟩

private lemma tA2a_not_prefix_tA2b : ¬ tA2a.IsPrefixOf tA2b := fun h =>
  tA2a_ne_tA2b (hist_ext (h.eq_of_length rfl))

private lemma tA2b_not_prefix_tA2a : ¬ tA2b.IsPrefixOf tA2a := fun h =>
  tA2a_ne_tA2b (hist_ext (h.eq_of_length rfl)).symm

private lemma tA2a_not_prefix_tA1 : ¬ tA2a.IsPrefixOf tA1 := fun h => by
  have h2 : (2 : ℕ) ≤ 1 := h.length_le
  omega

private lemma tA2b_not_prefix_tA1 : ¬ tA2b.IsPrefixOf tA1 := fun h => by
  have h2 : (2 : ℕ) ≤ 1 := h.length_le
  omega

private lemma prefix_of_tA1 {H' : History 2 (ZMod 2)} (h : H'.IsPrefixOf tA1) :
    H' = tA1 := by
  have hlen : H'.nodes.length ≤ 1 := by
    have h2 := h.length_le
    rwa [tA1_nodes, List.length_singleton] at h2
  have hpos : H'.nodes ≠ [] := H'.nonempty
  have hpos' : 0 < H'.nodes.length := List.length_pos_iff.mpr hpos
  exact hist_ext (h.eq_of_length (by rw [tA1_nodes, List.length_singleton]; omega))

private lemma prefix_of_two {H' : History 2 (ZMod 2)} {a b : Node 2 (ZMod 2)}
    (h : H'.nodes <+: [a, b]) : H'.nodes = [a] ∨ H'.nodes = [a, b] := by
  have hlen : H'.nodes.length ≤ 2 := by simpa using h.length_le
  have hpos : 0 < H'.nodes.length := List.length_pos_iff.mpr H'.nonempty
  have heq := List.prefix_iff_eq_take.mp h
  have h12 : H'.nodes.length = 1 ∨ H'.nodes.length = 2 := by omega
  rcases h12 with h1 | h1
  · left; rw [heq, h1]; rfl
  · right; rw [heq, h1]; rfl

/-- the {x0, x1} reduction locus (the root-cell system). -/
private noncomputable def rootLocus : Locus 2 9 :=
  ⟨fun c => decide ((c : ℕ) < 2), fun _ _ => 0⟩

/-- the {x0…x5} state locus (carrier A's one-node state system). -/
private noncomputable def stateLocus : Locus 2 9 :=
  ⟨fun c => decide ((c : ℕ) < 6), fun _ _ => 0⟩

/-- the codim-1 zero clause at coordinate `i`. -/
private noncomputable def zeroClause (i : Fin 9) : LevelClause 2 9 where
  support := {i}
  codim := 1
  sat := fun x => x i = 0
  dep := fun x y h => by rw [h i (Finset.mem_singleton_self i)]
  count := by
    have h1 : Nat.card {y : Fin 9 → ZMod 2 //
        y i = 0 ∧ ∀ c ∉ ({i} : Finset (Fin 9)), y c = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · constructor
        intro a b
        apply Subtype.ext; funext c
        by_cases hc : c = i
        · subst hc; rw [a.2.1, b.2.1]
        · rw [a.2.2 c (by simp [hc]), b.2.2 c (by simp [hc])]
      · exact ⟨⟨fun _ => 0, rfl, fun _ _ => rfl⟩⟩
    rw [h1, one_mul, Finset.card_singleton]

/-- the head's {x2…x5} 4-clause window system. -/
private noncomputable def windowFresh : FreshData 2 9 where
  clauses := [zeroClause 2, zeroClause 3, zeroClause 4, zeroClause 5]
  disj := by
    have hd : ∀ i j : Fin 9, i ≠ j →
        Disjoint (zeroClause i).support (zeroClause j).support := by
      intro i j hij
      simpa [zeroClause] using hij
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.pairwise_singleton _ _)))
    all_goals
      intro cl hcl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
    · rcases hcl with h | h | h <;> subst h <;> exact hd _ _ (by decide)
    · rcases hcl with h | h <;> subst h <;> exact hd _ _ (by decide)
    · subst hcl; exact hd _ _ (by decide)

/-- the leaves' empty fresh system (mstar 0). -/
private noncomputable def emptyFresh : FreshData 2 9 := ⟨[], List.Pairwise.nil⟩

private lemma rootLocus_iff (x : Box 2 9) :
    rootLocus.IsSolution x ↔ (x 0 = 0 ∧ x 1 = 0) := by
  constructor
  · intro h
    exact ⟨h 0 rfl, h 1 rfl⟩
  · rintro ⟨h0, h1⟩ i hi
    fin_cases i
    · exact h0
    · exact h1
    all_goals exact absurd hi (by decide)

private lemma stateLocus_iff (x : Box 2 9) :
    stateLocus.IsSolution x ↔
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · intro h
    exact ⟨h 0 rfl, h 1 rfl, h 2 rfl, h 3 rfl, h 4 rfl, h 5 rfl⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i hi
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    all_goals exact absurd hi (by decide)

private lemma windowFresh_iff (x : Box 2 9) :
    windowFresh.sat x ↔ (x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · intro h
    exact ⟨h (zeroClause 2) (by simp [windowFresh]),
      h (zeroClause 3) (by simp [windowFresh]),
      h (zeroClause 4) (by simp [windowFresh]),
      h (zeroClause 5) (by simp [windowFresh])⟩
  · rintro ⟨h2, h3, h4, h5⟩ cl hcl
    simp only [windowFresh, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hcl
    rcases hcl with h | h | h | h <;> subst h
    · exact h2
    · exact h3
    · exact h4
    · exact h5

private lemma rootCell_iff (x : Box 2 9) :
    x ∈ rootCell toyχ toyG ↔ (x 0 = 0 ∧ x 1 = 0) := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ b
    fin_cases b
    · exact h0
    · exact h1

end ToyTreeHelpers

open Classical in
noncomputable def toyTreeA : VTree 2 (ZMod 2) where
  chains := {tA1, tA2a, tA2b}
  hfin := ((Set.finite_singleton tA2b).insert tA2a).insert tA1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by
    intro H hH H' hpre hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH ⊢
    rcases hH with h | h | h <;> subst h
    · exact Or.inl (prefix_of_tA1 hpre)
    · rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafA] from hpre) with h | h
      · exact Or.inl (hist_ext (h.trans tA1_nodes.symm))
      · exact Or.inr (Or.inl (hist_ext (h.trans tA2a_nodes.symm)))
    · rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafB] from hpre) with h | h
      · exact Or.inl (hist_ext (h.trans tA1_nodes.symm))
      · exact Or.inr (Or.inr (hist_ext (h.trans tA2b_nodes.symm)))
  henV := ∅
  hhen := by simp
  leafV := fun H =>
    if H = tA2a then some (irrVerdictOf tA2a)
    else if H = tA2b then some (irrVerdictOf tA2b) else none
  hleaf := by
    intro H
    constructor
    · intro hsome
      by_cases h2a : H = tA2a
      · subst h2a
        refine ⟨Or.inr (Or.inl rfl), ?_⟩
        intro H' hH' hpre
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH'
        rcases hH' with h | h | h <;> subst h
        · exact absurd hpre tA2a_not_prefix_tA1
        · rfl
        · exact absurd hpre tA2a_not_prefix_tA2b
      · by_cases h2b : H = tA2b
        · subst h2b
          refine ⟨Or.inr (Or.inr rfl), ?_⟩
          intro H' hH' hpre
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH'
          rcases hH' with h | h | h <;> subst h
          · exact absurd hpre tA2b_not_prefix_tA1
          · exact absurd hpre tA2b_not_prefix_tA2a
          · rfl
        · rw [if_neg h2a, if_neg h2b] at hsome
          exact absurd hsome (by simp)
    · rintro ⟨hmem, hmax⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> subst h
      · exact absurd (hmax tA2a (Or.inr (Or.inl rfl)) tA1_prefix_tA2a).symm
          tA1_ne_tA2a
      · rw [if_pos rfl]; rfl
      · rw [if_neg (Ne.symm tA2a_ne_tA2b), if_pos rfl]; rfl
  nsLeaf := fun _ => False
  hns_leaf := by simp

open Classical in
noncomputable def toyTreeB : VTree 2 (ZMod 2) where
  chains := {tB1, tB2c, tB2d}
  hfin := ((Set.finite_singleton tB2d).insert tB2c).insert tB1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by
    intro H hH H' hpre hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH ⊢
    rcases hH with h | h | h <;> subst h
    · exact Or.inl (prefix_of_tA1 hpre)
    · rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafA] from hpre) with h | h
      · exact Or.inl (hist_ext (h.trans tA1_nodes.symm))
      · exact Or.inr (Or.inl (hist_ext (h.trans tA2a_nodes.symm)))
    · rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafB] from hpre) with h | h
      · exact Or.inl (hist_ext (h.trans tA1_nodes.symm))
      · exact Or.inr (Or.inr (hist_ext (h.trans tA2b_nodes.symm)))
  henV := ∅
  hhen := by simp
  leafV := fun H =>
    if H = tB2c then some (irrVerdictOf tB2c)
    else if H = tB2d then some (irrVerdictOf tB2d) else none
  hleaf := by
    intro H
    constructor
    · intro hsome
      by_cases h2a : H = tB2c
      · subst h2a
        refine ⟨Or.inr (Or.inl rfl), ?_⟩
        intro H' hH' hpre
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH'
        rcases hH' with h | h | h <;> subst h
        · exact absurd hpre tA2a_not_prefix_tA1
        · rfl
        · exact absurd hpre tA2a_not_prefix_tA2b
      · by_cases h2b : H = tB2d
        · subst h2b
          refine ⟨Or.inr (Or.inr rfl), ?_⟩
          intro H' hH' hpre
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH'
          rcases hH' with h | h | h <;> subst h
          · exact absurd hpre tA2b_not_prefix_tA1
          · exact absurd hpre tA2b_not_prefix_tA2a
          · rfl
        · rw [if_neg h2a, if_neg h2b] at hsome
          exact absurd hsome (by simp)
    · rintro ⟨hmem, hmax⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> subst h
      · exact absurd (hmax tB2c (Or.inr (Or.inl rfl)) tA1_prefix_tA2a).symm
          tA1_ne_tA2a
      · rw [if_pos rfl]; rfl
      · rw [if_neg (show tB2d ≠ tB2c from Ne.symm tA2a_ne_tA2b), if_pos rfl]; rfl
  nsLeaf := fun _ => False
  hns_leaf := by simp

/-- DO-2: the carrier-B SideSplit literal (k = 2, slopes 2/3, spans {3}/{4}). -/
noncomputable def toySplitB : SideSplit toyModelB toyCAB ToyCell.splitC
    ((⟨fun _ => false, fun _ _ => 0⟩ : Locus 2 9),
      (⟨[], List.Pairwise.nil⟩ : FreshData 2 9)).2 := by
  classical
  exact
    { k := 2
      sideOf := fun ν => if ν = toyLeafB then (1 : Fin 2) else 0
      side_ne := by
        intro j
        fin_cases j
        · exact ⟨toyLeafA, Finset.mem_insert_self _ _, if_neg leafA_ne_leafB⟩
        · exact ⟨toyLeafB, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
            if_pos rfl⟩
      clausesOf := fun _ => ∅
      hpartition := by
        constructor
        · ext cl
          simp only [Set.mem_iUnion, Finset.coe_empty, Set.mem_empty_iff_false,
            exists_false, Set.mem_setOf_eq, false_iff]
          exact List.not_mem_nil
        · intro i j hij
          simp [Function.onFun]
      sideSpan := fun j => if j = 0 then ({3} : Finset (Fin 9)) else {4}
      hspan_disj := by
        have h : ∀ i j : Fin 2, i ≠ j →
            Disjoint (if i = 0 then ({3} : Finset (Fin 9)) else {4})
              (if j = 0 then ({3} : Finset (Fin 9)) else {4}) := by decide
        exact fun i j hij => h i j hij
      hsupport := by
        intro j cl hcl
        exact absurd hcl (Finset.notMem_empty cl)
      hullSlope := fun j => if j = 0 then (2 : ℚ) else 3
      hslope := by
        have h : ∀ i j : Fin 2, i < j →
            (if i = 0 then (2 : ℚ) else 3) < (if j = 0 then (2 : ℚ) else 3) := by
          decide
        exact fun i j hij => h i j hij
      hside_read := by
        intro ν hν
        have hν' : ν = toyLeafA ∨ ν = toyLeafB := by
          have h2 : ν ∈ ({toyLeafA, toyLeafB} : Finset (Node 2 (ZMod 2))) := hν
          simpa using h2
        rcases hν' with h | h <;> subst h
        · rw [if_neg leafA_ne_leafB, if_pos rfl]
          rfl
        · rw [if_pos rfl, if_neg (by decide)]
          rfl }

noncomputable def toyHcrA : ChildRoot none toyHead := toyHead_root

/-- DO-2: the carrier-A root decomposition (t = 1). -/
noncomputable def toyTracksA : RootSplitData toyTreeA toyG where
  t := 1
  trackChains := fun _ => {tA1, tA2a, tA2b}
  hpart := by
    constructor
    · exact Set.iUnion_const _
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  headOf := fun _ => toyHead
  hhead := by
    intro i H hH
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
    rcases hH with h | h | h <;> subst h <;> rfl
  hinj := fun i j _ => Subsingleton.elim i j
  hne := fun _ => ⟨tA1, by simp⟩
  hcov := fun _ => ⟨toyHead_root, Set.mem_insert _ _⟩

/-! #### ledger proof infrastructure (P-phase fill; private helpers only). -/
section ToyLedgerHelpers

private lemma memA_tA1_iff (x : Box 2 9) : toyMemA (some tA1) x ↔
    (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · rintro ⟨-, hd⟩; exact hd
  · intro hd; exact ⟨Or.inl rfl, hd⟩

private lemma memA_tA2a_iff (x : Box 2 9) : toyMemA (some tA2a) x ↔
    (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · rintro ⟨-, hd⟩; exact hd
  · intro hd; exact ⟨Or.inr (Or.inl rfl), hd⟩

private lemma memA_tA2b_iff (x : Box 2 9) : toyMemA (some tA2b) x ↔
    (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · rintro ⟨-, hd⟩; exact hd
  · intro hd; exact ⟨Or.inr (Or.inr rfl), hd⟩

private lemma cellA_red_winC_iff (x : Box 2 9) :
    toyCellA (.red toyG Polynomial.X) x = ToyCell.winC ↔
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  by_cases hd : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0
  · rw [show toyCellA (.red toyG Polynomial.X) x = ToyCell.winC from if_pos ⟨rfl, hd⟩]
    exact iff_of_true rfl hd
  · rw [show toyCellA (.red toyG Polynomial.X) x = ToyCell.junk from
      if_neg (fun hc => hd hc.2)]
    exact iff_of_false (by simp) hd

private lemma cellA_st_tA1_splitC_iff (x : Box 2 9) :
    toyCellA (.st tA1) x = ToyCell.splitC ↔
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  by_cases hd : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0
  · rw [show toyCellA (.st tA1) x = ToyCell.splitC from
      if_pos ⟨rfl, Or.inl rfl, hd⟩]
    exact iff_of_true rfl hd
  · rw [show toyCellA (.st tA1) x = ToyCell.junk from
      if_neg (fun hc => hd hc.2.2)]
    exact iff_of_false (by simp) hd

private lemma presents_tA1 : SitePresents toyModel toyCA toyχ
    (EntSt.red toyG Polynomial.X) ToyCell.winC rootLocus windowFresh := by
  constructor
  · ext x
    constructor
    · rintro ⟨hroot, hcell⟩
      have hd := (cellA_red_winC_iff x).mp hcell
      exact ⟨(rootLocus_iff x).mpr ⟨hd.1, hd.2.1⟩,
        (windowFresh_iff x).mpr
          ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩⟩
    · rintro ⟨hsol, hsat⟩
      have h01 := (rootLocus_iff x).mp hsol
      have h25 := (windowFresh_iff x).mp hsat
      exact ⟨(rootCell_iff x).mpr h01, (cellA_red_winC_iff x).mpr
        ⟨h01.1, h01.2, h25.1, h25.2.1, h25.2.2.1, h25.2.2.2⟩⟩
  · ext x
    constructor
    · intro h
      exact (rootLocus_iff x).mpr ((rootCell_iff x).mp h)
    · intro h
      exact (rootCell_iff x).mpr ((rootLocus_iff x).mp h)

private lemma presents_split : SitePresents toyModel toyCA toyχ
    (EntSt.st tA1) ToyCell.splitC stateLocus emptyFresh := by
  constructor
  · ext x
    constructor
    · rintro ⟨hst, hcell⟩
      exact ⟨(stateLocus_iff x).mpr ((cellA_st_tA1_splitC_iff x).mp hcell),
        fun cl hcl => by simp [emptyFresh] at hcl⟩
    · rintro ⟨hsol, -⟩
      have hd := (stateLocus_iff x).mp hsol
      exact ⟨(memA_tA1_iff x).mpr hd, (cellA_st_tA1_splitC_iff x).mpr hd⟩
  · ext x
    constructor
    · intro h
      exact (stateLocus_iff x).mpr ((memA_tA1_iff x).mp h)
    · intro h
      exact (memA_tA1_iff x).mpr ((stateLocus_iff x).mp h)

private lemma state_cell_tA1 : stateEvent toyModel (some tA1)
    = cellEventE toyModel toyCA toyχ (EntSt.red toyG Polynomial.X) ToyCell.winC := by
  ext x
  constructor
  · intro h
    have hd := (memA_tA1_iff x).mp h
    exact ⟨(rootCell_iff x).mpr ⟨hd.1, hd.2.1⟩, (cellA_red_winC_iff x).mpr hd⟩
  · rintro ⟨-, hcell⟩
    exact (memA_tA1_iff x).mpr ((cellA_red_winC_iff x).mp hcell)

private lemma state_cell_tA2a : stateEvent toyModel (some tA2a)
    = cellEventE toyModel toyCA toyχ (EntSt.st tA1) ToyCell.splitC := by
  ext x
  constructor
  · intro h
    have hd := (memA_tA2a_iff x).mp h
    exact ⟨(memA_tA1_iff x).mpr hd, (cellA_st_tA1_splitC_iff x).mpr hd⟩
  · rintro ⟨-, hcell⟩
    exact (memA_tA2a_iff x).mpr ((cellA_st_tA1_splitC_iff x).mp hcell)

private lemma state_cell_tA2b : stateEvent toyModel (some tA2b)
    = cellEventE toyModel toyCA toyχ (EntSt.st tA1) ToyCell.splitC := by
  ext x
  constructor
  · intro h
    have hd := (memA_tA2b_iff x).mp h
    exact ⟨(memA_tA1_iff x).mpr hd, (cellA_st_tA1_splitC_iff x).mpr hd⟩
  · rintro ⟨-, hcell⟩
    exact (memA_tA2b_iff x).mpr ((cellA_st_tA1_splitC_iff x).mp hcell)

end ToyLedgerHelpers

/-- DO-2: the carrier-A site ledger (head ↦ the {x2…x5} 4-clause window system;
leaves ↦ mstar 0). -/
noncomputable def toyLedgerA : SiteLedger toyTreeA toyModel toyCA toyχ := by
  classical
  exact
    { sys := fun H =>
        if H = tA1 then (rootLocus, windowFresh) else (stateLocus, emptyFresh)
      cellAt := fun H => if H = tA1 then ToyCell.winC else ToyCell.splitC
      parentSt := fun H =>
        if H = tA1 then EntSt.red toyG Polynomial.X else EntSt.st tA1
      hparent := by
        intro H hH
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl]
          exact rfl
        · rw [if_neg (Ne.symm tA1_ne_tA2a)]
          exact ⟨tA1_prefix_tA2a, rfl, Or.inl rfl⟩
        · rw [if_neg (Ne.symm tA1_ne_tA2b)]
          exact ⟨tA1_prefix_tA2b, rfl, Or.inl rfl⟩
      presents := by
        intro H hH
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl, if_pos rfl]
          exact presents_tA1
        · rw [if_neg (Ne.symm tA1_ne_tA2a), if_neg (Ne.symm tA1_ne_tA2a),
            if_neg (Ne.symm tA1_ne_tA2a)]
          exact presents_split
        · rw [if_neg (Ne.symm tA1_ne_tA2b), if_neg (Ne.symm tA1_ne_tA2b),
            if_neg (Ne.symm tA1_ne_tA2b)]
          exact presents_split
      sides := fun _ => 1
      hsides := fun _ _ => le_rfl
      state_cell := by
        intro H hH h1
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl]
          exact state_cell_tA1
        · rw [if_neg (Ne.symm tA1_ne_tA2a), if_neg (Ne.symm tA1_ne_tA2a)]
          exact state_cell_tA2a
        · rw [if_neg (Ne.symm tA1_ne_tA2b), if_neg (Ne.symm tA1_ne_tA2b)]
          exact state_cell_tA2b
      splitAt := fun H hH h2 => absurd h2 (by omega)
      hsplit_k := fun H hH h2 => absurd h2 (by omega)
      free := by
        intro H hH cl hcl cIdx hsup
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl] at hcl ⊢
          simp only [windowFresh, List.mem_cons, List.not_mem_nil, or_false] at hcl
          rcases hcl with h | h | h | h <;> subst h <;>
            (have hc := Finset.mem_singleton.mp hsup; subst hc; rfl)
        · rw [if_neg (Ne.symm tA1_ne_tA2a)] at hcl
          simp [emptyFresh] at hcl
        · rw [if_neg (Ne.symm tA1_ne_tA2b)] at hcl
          simp [emptyFresh] at hcl
      freshCoords := fun H =>
        if H = tA1 then ({2, 3, 4, 5} : Finset (Fin 9)) else ∅
      hfresh := by
        intro H hH cl hcl cIdx hsup
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl] at hcl ⊢
          simp only [windowFresh, List.mem_cons, List.not_mem_nil, or_false] at hcl
          rcases hcl with h | h | h | h <;> subst h <;>
            (have hc := Finset.mem_singleton.mp hsup; subst hc; decide)
        · rw [if_neg (Ne.symm tA1_ne_tA2a)] at hcl
          simp [emptyFresh] at hcl
        · rw [if_neg (Ne.symm tA1_ne_tA2b)] at hcl
          simp [emptyFresh] at hcl
      hcard := by
        intro H hH
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl]
          rfl
        · rw [if_neg (Ne.symm tA1_ne_tA2a), if_neg (Ne.symm tA1_ne_tA2a)]
          rfl
        · rw [if_neg (Ne.symm tA1_ne_tA2b), if_neg (Ne.symm tA1_ne_tA2b)]
          rfl }

open Classical in
/-- DO-2: the τ-emission verdict map on carrier A. -/
noncomputable def toyVdict :
    Option (History 2 (ZMod 2)) → Box 2 9 → Option Vd :=
  fun o x =>
    match o with
    | none => none
    | some H =>
        if toyMemA (some H) x ∧ (H = tA2a ∨ H = tA2b)
        then some (irrVerdictOf H) else none

/-! ### the gate battery (DO-3 — G1a decide surrogates + G1b bridges, all OPEN) -/

/-! #### fiber proof infrastructure (P-phase fill; private helpers only). -/
section ToyFiberHelpers

private lemma not_irrHalts_tA1 : ¬ IrrHalts tA1 := by
  rintro ⟨-, h⟩
  have h2 : (1 : ℕ) = 2 := h
  omega

private lemma irrHalts_tA2a : IrrHalts tA2a := ⟨tA2a.nonempty, rfl⟩

private lemma irrHalts_tA2b : IrrHalts tA2b := ⟨tA2b.nonempty, rfl⟩

private lemma not_nsHalts_tA1 {x : Box 2 9}
    (hx : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) :
    ¬ NsHalts toyModel (some tA1) x := by
  rintro ⟨-, hnone⟩
  exact hnone toyLeafA ⟨rfl, Or.inl rfl, ⟨Or.inl rfl, hx⟩⟩

private lemma nsHalts_iff_digits (H : History 2 (ZMod 2)) {x : Box 2 9}
    (hx : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) :
    NsHalts toyModel (some H) x ↔ (H = tA2a ∨ H = tA2b) := by
  constructor
  · rintro ⟨⟨hmem, -⟩, hnone⟩
    rcases hmem with h | h | h
    · exact absurd ⟨h, Or.inl rfl, ⟨Or.inl rfl, hx⟩⟩ (hnone toyLeafA)
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    refine ⟨⟨?_, hx⟩, ?_⟩
    · rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro ν ⟨h1, -, -⟩
      rcases h with h2 | h2
      · exact tA1_ne_tA2a (h1.symm.trans h2)
      · exact tA1_ne_tA2b (h1.symm.trans h2)

private lemma memA_some_iff {x : Box 2 9}
    (hx : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0)
    (H : History 2 (ZMod 2)) :
    toyMemA (some H) x ↔ (H = tA1 ∨ H = tA2a ∨ H = tA2b) :=
  ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

private lemma redPoly_toy {x : Box 2 9} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    redPoly toyχ x = Polynomial.X ^ 2 := by
  show Polynomial.X ^ 2
      + ∑ b : Fin 2, Polynomial.C (x (toyχ b)) * Polynomial.X ^ (b : ℕ)
    = Polynomial.X ^ 2
  rw [Fin.sum_univ_two, show x (toyχ 0) = 0 from h0, show x (toyχ 1) = 0 from h1]
  simp

private lemma nf_toy {x : Box 2 9} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    UniqueFactorizationMonoid.normalizedFactors (redPoly toyχ x)
      = 2 • ({Polynomial.X} : Multiset (Polynomial (ZMod 2))) := by
  rw [redPoly_toy h0 h1, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible Polynomial.irreducible_X,
    Polynomial.Monic.normalize_eq_self Polynomial.monic_X]

private lemma henPayload_toy {x : Box 2 9} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    henPayload toyχ x = 0 := by
  have hdeg : henDegrees toyχ x = 0 := by
    unfold henDegrees
    rw [nf_toy h0 h1, Multiset.toFinset_nsmul _ 2 (by norm_num),
      Multiset.toFinset_singleton, Finset.filter_singleton, if_neg ?_]
    · rfl
    · rw [Multiset.count_nsmul, Multiset.count_singleton_self]
      omega
  unfold henPayload
  rw [hdeg]
  rfl

open Classical in
private lemma htfA : toyTreeA.hfin.toFinset
    = ({tA1, tA2a, tA2b} : Finset (History 2 (ZMod 2))) := by
  ext H
  simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
  exact Iff.rfl

open Classical in
private lemma leafVA_tA1 : toyTreeA.leafV tA1 = none := by
  show (if tA1 = tA2a then some (irrVerdictOf tA2a)
    else if tA1 = tA2b then some (irrVerdictOf tA2b) else none) = none
  rw [if_neg tA1_ne_tA2a, if_neg tA1_ne_tA2b]

open Classical in
private lemma leafVA_tA2a : toyTreeA.leafV tA2a = some (irrVerdictOf tA2a) := by
  show (if tA2a = tA2a then some (irrVerdictOf tA2a)
    else if tA2a = tA2b then some (irrVerdictOf tA2b) else none)
    = some (irrVerdictOf tA2a)
  rw [if_pos rfl]

open Classical in
private lemma leafVA_tA2b : toyTreeA.leafV tA2b = some (irrVerdictOf tA2b) := by
  show (if tA2b = tA2a then some (irrVerdictOf tA2a)
    else if tA2b = tA2b then some (irrVerdictOf tA2b) else none)
    = some (irrVerdictOf tA2b)
  rw [if_neg (Ne.symm tA2a_ne_tA2b), if_pos rfl]

open Classical in
private lemma typemultA_sum :
    (toyTreeA.typemult.map fun ef => ef.1 * ef.2).sum = 2 := by
  rw [show toyTreeA.typemult = (Multiset.map Subtype.val toyTreeA.henV).sum
      + ∑ H ∈ toyTreeA.hfin.toFinset, ((toyTreeA.leafV H).elim 0 Subtype.val)
    from rfl]
  rw [htfA, Finset.sum_insert (by simp [tA1_ne_tA2a, tA1_ne_tA2b]),
    Finset.sum_insert (by simp [tA2a_ne_tA2b]), Finset.sum_singleton,
    leafVA_tA1, leafVA_tA2a, leafVA_tA2b]
  decide

open Classical in
private lemma headsA : toyTreeA.heads = ({tA1} : Finset (History 2 (ZMod 2))) := by
  rw [show toyTreeA.heads
      = toyTreeA.hfin.toFinset.filter (fun H => H.nodes.length = 1) from rfl,
    htfA, Finset.filter_insert, if_pos (show tA1.nodes.length = 1 from rfl),
    Finset.filter_insert, if_neg (show ¬ tA2a.nodes.length = 1 by
      rw [tA2a_nodes]; simp),
    Finset.filter_singleton, if_neg (show ¬ tA2b.nodes.length = 1 by
      rw [tA2b_nodes]; simp)]
  simp

open Classical in
private lemma trackDegA_tA1 : toyTreeA.trackDeg tA1 = 2 := by
  unfold VTree.trackDeg
  rw [htfA, Finset.sum_insert (by simp [tA1_ne_tA2a, tA1_ne_tA2b]),
    Finset.sum_insert (by simp [tA2a_ne_tA2b]), Finset.sum_singleton,
    if_pos (show tA1.IsPrefixOf tA1 from List.prefix_refl _),
    if_pos tA1_prefix_tA2a, if_pos tA1_prefix_tA2b,
    leafVA_tA1, leafVA_tA2a, leafVA_tA2b]
  decide

private lemma trackRHS {x : Box 2 9} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    ((UniqueFactorizationMonoid.normalizedFactors (redPoly toyχ x)).toFinset.filter
        (fun ψ => 2 ≤ Multiset.count ψ
          (UniqueFactorizationMonoid.normalizedFactors (redPoly toyχ x)))).val.map
      (fun ψ => Multiset.count ψ
        (UniqueFactorizationMonoid.normalizedFactors (redPoly toyχ x))
          * ψ.natDegree) = {2} := by
  rw [nf_toy h0 h1, Multiset.toFinset_nsmul _ 2 (by norm_num),
    Multiset.toFinset_singleton, Finset.filter_singleton,
    if_pos (by rw [Multiset.count_nsmul, Multiset.count_singleton_self])]
  simp [Multiset.count_nsmul, Polynomial.natDegree_X]

private lemma max_tA2a :
    IsMaximalIn ({tA1, tA2a, tA2b} : Set (History 2 (ZMod 2))) tA2a := by
  intro H' hH' hpre
  rcases (show H' = tA1 ∨ H' = tA2a ∨ H' = tA2b from hH') with h | h | h <;> subst h
  · exact absurd hpre tA2a_not_prefix_tA1
  · rfl
  · exact absurd hpre tA2a_not_prefix_tA2b

private lemma max_tA2b :
    IsMaximalIn ({tA1, tA2a, tA2b} : Set (History 2 (ZMod 2))) tA2b := by
  intro H' hH' hpre
  rcases (show H' = tA1 ∨ H' = tA2a ∨ H' = tA2b from hH') with h | h | h <;> subst h
  · exact absurd hpre tA2b_not_prefix_tA1
  · exact absurd hpre tA2b_not_prefix_tA2a
  · rfl

/-- **the carrier-A fiber characterization**: the tree fiber IS the {x0…x5 = 0}
digit stratum (the census set — N(fiberA) = 8 = 2^{9−6}). -/
private lemma fiberA_iff (x : Box 2 9) :
    toyTreeA.fiberAt toyModel toyχ x ↔
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · intro h
    exact ((h.1 tA1).mp (Or.inl rfl)).2.1.2
  · intro hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- clause (i)
      intro H
      constructor
      · intro hH
        rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
        · exact ⟨tA1.nonempty, ⟨Or.inl rfl, hx⟩,
            fun H' hp hne hnn => absurd (prefix_of_tA1 hp) hne⟩
        · refine ⟨tA2a.nonempty, ⟨Or.inr (Or.inl rfl), hx⟩, ?_⟩
          intro H' hp hne hnn
          rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafA] from hp)
            with h | h
          · have hH' : H' = tA1 := hist_ext (h.trans tA1_nodes.symm)
            subst hH'
            exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
          · exact absurd (hist_ext (h.trans tA2a_nodes.symm)) hne
        · refine ⟨tA2b.nonempty, ⟨Or.inr (Or.inr rfl), hx⟩, ?_⟩
          intro H' hp hne hnn
          rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafB] from hp)
            with h | h
          · have hH' : H' = tA1 := hist_ext (h.trans tA1_nodes.symm)
            subst hH'
            exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
          · exact absurd (hist_ext (h.trans tA2b_nodes.symm)) hne
      · rintro ⟨hne, ⟨hmem, -⟩⟩
        exact hmem.1
    · -- clause (ii)
      intro H hH hmax
      rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
      · exact absurd (hmax tA2a (Or.inr (Or.inl rfl)) tA1_prefix_tA2a).symm
          tA1_ne_tA2a
      · exact Or.inl ⟨irrHalts_tA2a, fun hf => hf, leafVA_tA2a⟩
      · exact Or.inl ⟨irrHalts_tA2b, fun hf => hf, leafVA_tA2b⟩
    · -- clause (iii)
      rw [henPayload_toy hx.1 hx.2.1]
      rfl
    · -- clause (iv)
      intro H hH hnmax
      rcases (show H = tA1 ∨ H = tA2a ∨ H = tA2b from hH) with h | h | h <;> subst h
      · exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
      · exact absurd max_tA2a hnmax
      · exact absurd max_tA2b hnmax
    · -- clause (v)
      exact typemultA_sum
    · -- clause (vi)
      rw [trackRHS hx.1 hx.2.1, headsA]
      simp [trackDegA_tA1]

end ToyFiberHelpers

theorem toy_gate :
    (Nat.card ↥{x | toyTreeA.fiberAt toyModel toyχ x}) * 2 ^ 6 = 2 ^ 9 := by
  have hset : {x : Box 2 9 | toyTreeA.fiberAt toyModel toyχ x}
      = {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0} :=
    Set.ext fiberA_iff
  rw [hset]
  have hcard : Nat.card ↥{x : Box 2 9 |
      x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0} = 8 := by
    have hs : {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
        = {x : Box 2 9 | stateLocus.IsSolution x} :=
      Set.ext fun x => (stateLocus_iff x).symm
    rw [hs]
    have hmass : stateLocus.mass = 2 ^ (9 - stateLocus.numPinned) :=
      LeanUrat.MovesC.C0_digitSystemMass stateLocus
    rw [show stateLocus.numPinned = 6 from by decide] at hmass
    norm_num at hmass
    exact hmass
  rw [hcard]
  norm_num

/-! #### SIB/E5 proof infrastructure (P-phase fill; private helpers only). -/
section ToySibHelpers

private lemma cellA_amb_ne_splitC (x : Box 2 9) :
    toyCellA .amb x ≠ ToyCell.splitC := by
  by_cases h : x 0 = 0 ∧ x 1 = 0
  · rw [show toyCellA .amb x = ToyCell.rootC from if_pos h]
    simp
  · rw [show toyCellA .amb x = ToyCell.junk from if_neg h]
    simp

private lemma cellA_red_ne_splitC (g : Fin 2 → ZMod 2) (ψ : Polynomial (ZMod 2))
    (x : Box 2 9) : toyCellA (.red g ψ) x ≠ ToyCell.splitC := by
  by_cases h : ψ = Polynomial.X ∧ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
      ∧ x 4 = 0 ∧ x 5 = 0
  · rw [show toyCellA (.red g ψ) x = ToyCell.winC from if_pos h]
    simp
  · rw [show toyCellA (.red g ψ) x = ToyCell.junk from if_neg h]
    simp

private lemma cellA_st_ne_splitC {H : History 2 (ZMod 2)} (hH : H ≠ tA1)
    (x : Box 2 9) : toyCellA (.st H) x ≠ ToyCell.splitC := by
  rw [show toyCellA (.st H) x = ToyCell.junk from if_neg (fun hc => hH hc.1)]
  simp

private lemma ncard_empty : Nat.card ↥(∅ : Set (Box 2 9)) = 0 := Nat.card_of_isEmpty

/-- x-transport of `ContFiber` between two members of the digit stratum (every
box-dependence of the toy's `ContFiber` factors through the pinned digits). -/
private lemma contFiber_transport {ν : Node 2 (ZMod 2)}
    {hν : ChildRoot (some tA1) ν} {Tsub : Set (History 2 (ZMod 2))}
    {leafSpec : History 2 (ZMod 2) → Option Vd}
    {nsSpec : History 2 (ZMod 2) → Prop} {x x' : Box 2 9}
    (hx : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0)
    (hx' : x' 0 = 0 ∧ x' 1 = 0 ∧ x' 2 = 0 ∧ x' 3 = 0 ∧ x' 4 = 0 ∧ x' 5 = 0)
    (h : ContFiber toyModel (some tA1) ν hν Tsub leafSpec nsSpec x) :
    ContFiber toyModel (some tA1) ν hν Tsub leafSpec nsSpec x' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro H'
    rw [h1 H']
    exact and_congr Iff.rfl (and_congr
      ((memA_some_iff hx H').trans (memA_some_iff hx' H').symm)
      (forall_congr' fun H'' => imp_congr_right fun _ =>
        imp_congr_right fun _ => imp_congr_right fun _ =>
          and_congr Iff.rfl (not_congr
            ((nsHalts_iff_digits H'' hx).trans (nsHalts_iff_digits H'' hx').symm))))
  · intro H' hm hmax
    rcases h2 H' hm hmax with ⟨hi, hn, hl⟩ | ⟨hns, hni, hn, hl⟩
    · exact Or.inl ⟨hi, hn, hl⟩
    · exact Or.inr ⟨(nsHalts_iff_digits H' hx').mpr
        ((nsHalts_iff_digits H' hx).mp hns), hni, hn, hl⟩
  · intro H' hm hnmax
    exact ⟨(h3 H' hm hnmax).1, fun hns => (h3 H' hm hnmax).2
      ((nsHalts_iff_digits H' hx).mpr ((nsHalts_iff_digits H' hx').mp hns))⟩

end ToySibHelpers

theorem toy_sib : SibCount toyModel toyCA toyχ := by
  classical
  intro es c S hbr hS
  cases c with
  | rootC =>
    exfalso
    have h2 : (2 : ℕ) ≤ ({toyHead} : Finset (Node 2 (ZMod 2))).card := hbr
    rw [Finset.card_singleton] at h2
    omega
  | winC =>
    exfalso
    have h2 : (2 : ℕ) ≤ ({toyHead} : Finset (Node 2 (ZMod 2))).card := hbr
    rw [Finset.card_singleton] at h2
    omega
  | junk =>
    exfalso
    have h2 : (2 : ℕ) ≤ (∅ : Finset (Node 2 (ZMod 2))).card := hbr
    simp at h2
  | splitC =>
    have hmemA : toyLeafA ∈ toyCA.branchSetOf ToyCell.splitC :=
      Finset.mem_insert_self _ _
    have hmemB : toyLeafB ∈ toyCA.branchSetOf ToyCell.splitC :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcard2 : (toyCA.branchSetOf ToyCell.splitC).card = 2 := by
      have h2 : ({toyLeafA, toyLeafB} : Finset (Node 2 (ZMod 2))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using leafA_ne_leafB),
          Finset.card_singleton]
      exact h2
    have hzero := ncard_empty
    have hEdich : cellEventE toyModel toyCA toyχ es ToyCell.splitC = ∅ ∨
        (es = .st tA1 ∧ cellEventE toyModel toyCA toyχ es ToyCell.splitC
          = {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}) := by
      cases es with
      | amb =>
        left
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨-, hcell⟩
        exact cellA_amb_ne_splitC x hcell
      | red g ψ =>
        left
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨-, hcell⟩
        exact cellA_red_ne_splitC g ψ x hcell
      | st H =>
        by_cases hH : H = tA1
        · subst hH
          right
          refine ⟨rfl, ?_⟩
          ext x
          constructor
          · rintro ⟨-, hcell⟩
            exact (cellA_st_tA1_splitC_iff x).mp hcell
          · intro hx
            exact ⟨(memA_tA1_iff x).mpr hx, (cellA_st_tA1_splitC_iff x).mpr hx⟩
        · left
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨-, hcell⟩
          exact cellA_st_ne_splitC hH x hcell
    rcases hEdich with hE | ⟨hes, hE⟩
    · rw [hE, Set.empty_inter, hzero, zero_mul]
      symm
      apply Finset.prod_eq_zero hmemA
      rw [Set.empty_inter]
      exact hzero
    · subst hes
      have hdichS : ∀ ν, ν ∈ toyCA.branchSetOf ToyCell.splitC →
          ({x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
              ∩ S ν
            = {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
          ∨ {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
              ∩ S ν = ∅) := by
        intro ν hν
        rcases hS ν hν with ⟨hνcr, Tsub, ls, ns, hfin, hSν⟩ | hSν
        · by_cases hne : ({x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
              ∧ x 4 = 0 ∧ x 5 = 0} ∩ S ν).Nonempty
          · left
            obtain ⟨x₀, hx₀D, hx₀S⟩ := hne
            apply Set.Subset.antisymm Set.inter_subset_left
            intro x hx
            refine ⟨hx, ?_⟩
            rw [hSν] at hx₀S ⊢
            exact contFiber_transport hx₀D hx hx₀S
          · right
            exact Set.not_nonempty_iff_eq_empty.mp hne
        · rw [hSν]
          left
          exact Set.inter_univ _
      rw [hE, hcard2]
      have hbiInter : (⋂ ν ∈ toyCA.branchSetOf ToyCell.splitC, S ν)
          = S toyLeafA ∩ S toyLeafB := by
        show (⋂ ν ∈ ({toyLeafA, toyLeafB} : Finset (Node 2 (ZMod 2))), S ν) = _
        rw [Finset.set_biInter_insert, Finset.set_biInter_singleton]
      have hprod : (∏ ν ∈ toyCA.branchSetOf ToyCell.splitC,
            Nat.card ↥({x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
              ∧ x 4 = 0 ∧ x 5 = 0} ∩ S ν))
          = Nat.card ↥({x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
              ∧ x 4 = 0 ∧ x 5 = 0} ∩ S toyLeafA)
            * Nat.card ↥({x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
              ∧ x 4 = 0 ∧ x 5 = 0} ∩ S toyLeafB) := by
        show (∏ ν ∈ ({toyLeafA, toyLeafB} : Finset (Node 2 (ZMod 2))), _) = _
        rw [Finset.prod_insert (by simpa using leafA_ne_leafB),
          Finset.prod_singleton]
      rw [hbiInter, hprod, Set.inter_inter_distrib_left]
      rcases hdichS toyLeafA hmemA with ha | ha <;>
        rcases hdichS toyLeafB hmemB with hb | hb <;> rw [ha, hb] <;>
        simp [hzero, Set.inter_empty, Set.empty_inter, Set.inter_self, pow_one]

theorem toy_vdict_nonconstant : ∃ o x o' x', toyVdict o x ≠ toyVdict o' x' := by
  refine ⟨none, fun _ => 0, some tA2a, fun _ => 0, ?_⟩
  have h1 : toyVdict none (fun _ => 0) = none := rfl
  have h2 : toyVdict (some tA2a) (fun _ => 0) = some (irrVerdictOf tA2a) := by
    classical
    show (if toyMemA (some tA2a) (fun _ => 0) ∧ (tA2a = tA2a ∨ tA2a = tA2b)
        then some (irrVerdictOf tA2a) else none) = some (irrVerdictOf tA2a)
    rw [if_pos ⟨⟨Or.inr (Or.inl rfl), rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩]
  rw [h1, h2]
  simp

theorem toy_fiber_ne : ∃ x, toyTreeA.fiberAt toyModel toyχ x :=
  ⟨fun _ => 0, (fiberA_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! #### E5 proof infrastructure (P-phase fill; private helpers only). -/
section ToyE5Helpers

/-- the carrier-A per-track SubFiber characterization: the one-track event IS the
digit stratum. -/
private lemma subFiberA_iff (x : Box 2 9) :
    SubFiber toyModel ({tA1, tA2a, tA2b} : Set (History 2 (ZMod 2))) toyHead toyHcrA
      toyTreeA.leafV toyTreeA.nsLeaf x ↔
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0) := by
  constructor
  · intro h
    exact (((h.1 tA1).mp (Or.inl rfl)).2.1).2
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · intro H'
      constructor
      · intro hH'
        rcases (show H' = tA1 ∨ H' = tA2a ∨ H' = tA2b from hH') with h | h | h <;>
          subst h
        · exact ⟨List.prefix_refl _, ⟨Or.inl rfl, hx⟩,
            fun H'' hp1 hp2 hne => absurd (prefix_of_tA1 hp2) hne⟩
        · refine ⟨tA1_prefix_tA2a, ⟨Or.inr (Or.inl rfl), hx⟩, ?_⟩
          intro H'' hp1 hp2 hne
          rcases prefix_of_two (show H''.nodes <+: [toyHead, toyLeafA] from hp2)
            with h | h
          · have hH'' : H'' = tA1 := hist_ext (h.trans tA1_nodes.symm)
            subst hH''
            exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
          · exact absurd (hist_ext (h.trans tA2a_nodes.symm)) hne
        · refine ⟨tA1_prefix_tA2b, ⟨Or.inr (Or.inr rfl), hx⟩, ?_⟩
          intro H'' hp1 hp2 hne
          rcases prefix_of_two (show H''.nodes <+: [toyHead, toyLeafB] from hp2)
            with h | h
          · have hH'' : H'' = tA1 := hist_ext (h.trans tA1_nodes.symm)
            subst hH''
            exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
          · exact absurd (hist_ext (h.trans tA2b_nodes.symm)) hne
      · rintro ⟨-, hmem, -⟩
        exact hmem.1
    · intro H' hH' hmax
      rcases (show H' = tA1 ∨ H' = tA2a ∨ H' = tA2b from hH') with h | h | h <;>
        subst h
      · exact absurd (hmax tA2a (Or.inr (Or.inl rfl)) tA1_prefix_tA2a).symm
          tA1_ne_tA2a
      · exact Or.inl ⟨irrHalts_tA2a, fun hf => hf, leafVA_tA2a⟩
      · exact Or.inl ⟨irrHalts_tA2b, fun hf => hf, leafVA_tA2b⟩
    · intro H' hH' hnmax
      rcases (show H' = tA1 ∨ H' = tA2a ∨ H' = tA2b from hH') with h | h | h <;>
        subst h
      · exact ⟨not_irrHalts_tA1, not_nsHalts_tA1 hx⟩
      · exact absurd max_tA2a hnmax
      · exact absurd max_tA2b hnmax

private lemma card_digits : Nat.card ↥{x : Box 2 9 |
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0} = 8 := by
  have hs : {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
      = {x : Box 2 9 | stateLocus.IsSolution x} :=
    Set.ext fun x => (stateLocus_iff x).symm
  rw [hs]
  have hmass : stateLocus.mass = 2 ^ (9 - stateLocus.numPinned) :=
    LeanUrat.MovesC.C0_digitSystemMass stateLocus
  rw [show stateLocus.numPinned = 6 from by decide] at hmass
  norm_num at hmass
  exact hmass

private lemma card_rootCell : Nat.card ↥(rootCell toyχ toyG) = 128 := by
  have hs : rootCell toyχ toyG = {x : Box 2 9 | rootLocus.IsSolution x} :=
    Set.ext fun x => (rootCell_iff x).trans (rootLocus_iff x).symm
  rw [hs]
  have hmass : rootLocus.mass = 2 ^ (9 - rootLocus.numPinned) :=
    LeanUrat.MovesC.C0_digitSystemMass rootLocus
  rw [show rootLocus.numPinned = 2 from by decide] at hmass
  norm_num at hmass
  exact hmass

end ToyE5Helpers

theorem toy_e5_instance :
    Nat.card ↥{x | toyTreeA.fiberAt toyModel toyχ x}
        * (Nat.card ↥(rootCell toyχ toyG)) ^ 1 * 2 ^ 2
      = 2 ^ 9 * Nat.card ↥(rootCell toyχ toyG ∩
          trackEvent toyTreeA toyModel toyTracksA ⟨0, Nat.zero_lt_one⟩ toyHcrA) := by
  have hset : {x : Box 2 9 | toyTreeA.fiberAt toyModel toyχ x}
      = {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0} :=
    Set.ext fiberA_iff
  have htrack : rootCell toyχ toyG
        ∩ trackEvent toyTreeA toyModel toyTracksA ⟨0, Nat.zero_lt_one⟩ toyHcrA
      = {x : Box 2 9 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0} := by
    ext x
    constructor
    · rintro ⟨-, hsub⟩
      exact (subFiberA_iff x).mp hsub
    · intro hx
      exact ⟨(rootCell_iff x).mpr ⟨hx.1, hx.2.1⟩, (subFiberA_iff x).mpr hx⟩
  rw [hset, htrack, card_digits, card_rootCell]
  norm_num

theorem toy_henflip_unrealizable :
    ¬ Realizes toyModel toyχ
      (toyTreeA.withHenV {henVerdict 1 le_rfl}
        (by intro w hw; exact ⟨1, le_rfl, by simpa using Multiset.mem_singleton.mp hw ▸ rfl⟩)) := by
  rintro ⟨x, hfib⟩
  have hx := ((hfib.1 tA1).mp (Or.inl rfl)).2.1.2
  have h3 := hfib.2.2.1
  rw [henPayload_toy hx.1 hx.2.1] at h3
  have h3' : ({henVerdict 1 le_rfl} : Multiset Vd) = 0 := h3
  have hc : (1 : ℕ) = 0 := by simpa using congrArg Multiset.card h3'
  omega

theorem toy_jcmulti_site :
    JCmultiAt toyModelB toyCAB toyχ (.st tB1) ToyCell.splitC toySplitB := by
  sorry

theorem toy_state_cell :
    stateEvent toyModel (some tA2a)
      = cellEventE toyModel toyCA toyχ (EntSt.red toyG Polynomial.X)
          ToyCell.splitC := by
  sorry

/-- records 5+7's gate — the SEPARATE 𝔽₄-type carrier (§0 record #7's two-node
K-card instance; the history pin is its own OPEN construction, `twoNodeKcardH`). -/
noncomputable def twoNodeKcardH : History 2 (ZMod 2) := by sorry

theorem toy_v8_wchain : ¬ HistLawful 2 toyN twoNodeKcardH := by
  sorry

/-- record 9's gate — the p = 3 one-node monic-slot instance (own carrier). -/
noncomputable def oneNodePatH : History 3 (ZMod 3) := by sorry

theorem toy_v8_monic : ¬ HistLawful 3 toyN3 oneNodePatH := by
  sorry

end LeanUrat.MovesT
