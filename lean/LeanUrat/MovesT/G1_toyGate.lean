/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.HC2.U31_gateReadsOf

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

open Classical in
noncomputable def toyTreeA : VTree 2 (ZMod 2) where
  chains := {tA1, tA2a, tA2b}
  hfin := ((Set.finite_singleton tA2b).insert tA2a).insert tA1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by sorry
  henV := ∅
  hhen := by simp
  leafV := fun H =>
    if H = tA2a then some (irrVerdictOf tA2a)
    else if H = tA2b then some (irrVerdictOf tA2b) else none
  hleaf := by sorry
  nsLeaf := fun _ => False
  hns_leaf := by simp

open Classical in
noncomputable def toyTreeB : VTree 2 (ZMod 2) where
  chains := {tB1, tB2c, tB2d}
  hfin := ((Set.finite_singleton tB2d).insert tB2c).insert tB1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by sorry
  henV := ∅
  hhen := by simp
  leafV := fun H =>
    if H = tB2c then some (irrVerdictOf tB2c)
    else if H = tB2d then some (irrVerdictOf tB2d) else none
  hleaf := by sorry
  nsLeaf := fun _ => False
  hns_leaf := by simp

/-- DO-2: the carrier-B SideSplit literal (k = 2, slopes 2/3, spans {3}/{4}). -/
noncomputable def toySplitB : SideSplit toyModelB toyCAB ToyCell.splitC
    ((⟨fun _ => false, fun _ _ => 0⟩ : Locus 2 9),
      (⟨[], List.Pairwise.nil⟩ : FreshData 2 9)).2 := by
  sorry

noncomputable def toyHcrA : ChildRoot none toyHead := toyHead_root

/-- DO-2: the carrier-A root decomposition (t = 1). -/
noncomputable def toyTracksA : RootSplitData toyTreeA toyG where
  t := 1
  trackChains := fun _ => {tA1, tA2a, tA2b}
  hpart := by sorry
  headOf := fun _ => toyHead
  hhead := by sorry
  hinj := fun i j _ => Subsingleton.elim i j
  hne := fun _ => ⟨tA1, by simp⟩
  hcov := by sorry

/-- DO-2: the carrier-A site ledger (head ↦ the {x2…x5} 4-clause window system;
leaves ↦ mstar 0). -/
noncomputable def toyLedgerA : SiteLedger toyTreeA toyModel toyCA toyχ := by
  sorry

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

theorem toy_gate :
    (Nat.card ↥{x | toyTreeA.fiberAt toyModel toyχ x}) * 2 ^ 6 = 2 ^ 9 := by
  sorry

theorem toy_sib : SibCount toyModel toyCA toyχ := by
  sorry

theorem toy_vdict_nonconstant : ∃ o x o' x', toyVdict o x ≠ toyVdict o' x' := by
  sorry

theorem toy_fiber_ne : ∃ x, toyTreeA.fiberAt toyModel toyχ x := by
  sorry

theorem toy_e5_instance :
    Nat.card ↥{x | toyTreeA.fiberAt toyModel toyχ x}
        * (Nat.card ↥(rootCell toyχ toyG)) ^ 1 * 2 ^ 2
      = 2 ^ 9 * Nat.card ↥(rootCell toyχ toyG ∩
          trackEvent toyTreeA toyModel toyTracksA ⟨0, Nat.zero_lt_one⟩ toyHcrA) := by
  sorry

theorem toy_henflip_unrealizable :
    ¬ Realizes toyModel toyχ
      (toyTreeA.withHenV {henVerdict 1 le_rfl}
        (by intro w hw; exact ⟨1, le_rfl, by simpa using Multiset.mem_singleton.mp hw ▸ rfl⟩)) := by
  sorry

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
