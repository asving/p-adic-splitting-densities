/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C02
import Uniformity.ChapC.C20
import Uniformity.ChapC.C21
import Uniformity.ChapH.H53

/-!
# Uniformity.ChapC.C23 — `KeyFrame.slotRes_ne_zero`: the slot lemma, nonvanishing half

**Chapter C, NODE C.23** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge
layer; the A-C.1 amendment set governs). **ENV-C1′** = ENV-C1 + `hπ` (the blueprint's ENV-C3
minus finiteness: `Finite (ResidueField O)` enters only through consumers, so it is *not* bound
here). One signed declaration.

LEMMA HE6-0″, value-and-residue half. Let `A ∈ O[X]` with `deg A < D′ = e₁f₁`, and suppose the
stage height `F.stageHeight A` is *attained* at the finite value `k`. Then C.21's normalized slot
residue does not vanish:

`F.slotRes H₀ hpin k A ≠ 0`   in `K = F.stageField H₀ hpin`.

This is the nonvanishing that every downstream residual read rests on: it is what makes C.24's
image characterization land in `K^×` rather than in `K`, and it is the "no cancellation at the
attaining slot" step reused verbatim at C.28, C.32, C.46 and the §7 seam.

## The proof, in the blueprint's two steps

**Step 1 — the attaining slot exists and lies in the class.** `stageHeight A` is by C.02 the
`Finset.inf` of the slot costs `e₁·v(a_j) + jh` over `j ≤ deg A`; a `Finset.inf` over a nonempty
range is *attained*, at some `j` (`Finset.exists_mem_eq_inf`). Since the value `k` is finite, so
is `v(a_j) =: v`, and `e₁v + jh = k` in `ℕ` (`slot_value_nat`, the private `ℕ∞ → ℕ` descent).
C.20's `stageHeight_class` then pins the class, `jh ≡ k (mod e₁)`, and C.16's `slotIdx_unique`
identifies `j % e₁ = slotIdx k`; writing `t := j / e₁` gives `j = slotIdx k + e₁t` with `t < f₁`
(from `deg A < e₁f₁`) and `(slotIdx k + e₁t)h ≤ k`, i.e. **`t ∈ slotWindow k`** (C.17).

**Step 2 — the digit at that slot is nonzero.** The digit index C.21 reads at `t` is
`(k − (slotIdx k + e₁t)h)/e₁`, which by step 1 is exactly `v`, the *exact* valuation of `a_j`.
B.22's `digAt_eq_zero_iff` says `digAt π v (a_j) = 0 ↔ π^{v+1} ∣ a_j`, and `π^{v+1} ∤ a_j` because
`addVal (a_j) = v` (`addVal_le_iff_dvd` with `hπ.addVal_pow` — the one place `hπ` is consumed).

**Step 3 — the power basis kills the sum.** Suppose `slotRes … = 0`. Extend the window
coefficients by `0` off `slotWindow k ⊆ range f₁` (`Finset.sum_subset`); the vanishing becomes
`Σ_{t < f₁} algebraMap (l t) · η^t = 0` with `η = F.stageLetter H₀ hpin`. H.53's
`eta_independent` — "the machine form of `{1, η, …, η^{f₁−1}}` is a `resField X`-basis of `K`" —
concludes `l t = 0` for **every** `t`, in particular at the attaining `t`, contradicting step 2
(the outer `algebraMap` is injective, being a field hom). H.53's two side conditions are
discharged by the two private lemmas below.

## Divergences and private helpers (none is a blueprint node; GC-6.5)

* **`isKey_X` re-declared `private`.** C.04/C.12/C.19/C.21/C.44 each carry their own copy
  (defect **D9**'s cure) because private declarations are not importable; it is what names the
  base `Field (resField X)` instance, without which `K` has no field structure and H.53 does not
  apply. Retires to a public `isKey_X` when C.14a lands — a RE-PLAN item, not a silent addition.
* **`slot_value_nat`.** The `ℕ∞`-to-`ℕ` descent of the attaining slot's cost equation. Bureaucratic
  but load-bearing: `addVal (a_j) = ⊤` is excluded precisely because `e₁ > 0` makes
  `e₁ • ⊤ + jh = ⊤ ≠ k`.
* **`finrank_stageField` / `natDegree_minpoly_stageLetter`.** H.53's hypotheses in this frame:
  `[K : resField X] = f₁` (C.04's clause, `private` there — hence re-proved here off
  `AdjoinRoot.powerBasis` and C.01's `hresirr`) and `deg (minpoly η) = [K : resField X]` (the
  power-basis generator is the letter, `AdjoinRoot.powerBasis_gen`).
* **the "moreover" sentence is NOT a second declaration.** The blueprint's STATEMENT adds
  *"the `t`-th coefficient is nonzero iff slot `slotIdx k + e₁t` attains the minimum"*; the signed
  SIGNATURE carries only the `≠ 0` clause, and rightly so — the coefficient IS `digAt π ((k −
  (slotIdx k + e₁t)h)/e₁) (a_{slotIdx k + e₁t})` **by C.21's definition**, so the iff is B.22's
  `digAt_eq_zero_iff` read at that slot and nothing new is signed. Both halves of the iff appear
  inside this proof (step 2 is the ⇐ direction at the attaining slot).

**DEPENDS.** C.02 (`stageHeight`, unfolded through `suppVal` and B.15's `npHgt_X` to the
`Finset.inf` form) · C.16 (`slotIdx`, `slotIdx_unique`) ·
C.17 (`slotWindow`) · C.19 (power basis: `stageLetter`) · C.20 (`stageHeight_class`) ·
C.21 (`slotRes`, the object) · B.22/B.24 (`digAt`, `digAt_eq_zero_iff`) · B.08/B.15 (`addVal`
plumbing, `npHgt_X`) · **H.53** (`eta_independent`, instantiated at `(resField X, stageField F)`
through C.19's basis) — by committed node ID (GC-13(b)). Mathlib:
`Finset.exists_mem_eq_inf`, `Finset.sum_subset`, `Fin.sum_univ_eq_sum_range`,
`AdjoinRoot.powerBasis`, `PowerBasis.natDegree_minpoly`, `ENat.ne_top_iff_exists`.

**SOURCE.** `EFF.HE6.15` (LEMMA HE6-0″: exactness + nonvanishing, with the two hypothesis roles
verbatim); `EFF.HE6.58` (the corrected `γ` this instantiates).

**TEETH.** `HE6R1-T-BASIS` (`EFF.HE6R1.29`: at `γ₀ = −γ₁ ≠ 0` NO cancellation) → **Lean theorem**,
step 3 above, at the C.12 iterate level for `β`; the executable regression is retained separately
(§13).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- The attaining slot's data, in `ℕ`. -/
private theorem slot_value_nat (F : KeyFrame O π) {A : Polynomial O} {i k : ℕ}
    (hval : F.e₁ • addVal O (A.coeff i) + ((i * F.h : ℕ) : ℕ∞) = (k : ℕ∞)) :
    ∃ v : ℕ, addVal O (A.coeff i) = (v : ℕ∞) ∧ F.e₁ * v + i * F.h = k := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ, addVal O (A.coeff i) = (v : ℕ∞) := by
    rcases eq_or_ne (addVal O (A.coeff i)) ⊤ with h | h
    · exfalso
      rw [h, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add] at hval
      exact (ENat.coe_ne_top k) hval.symm
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
      exact ⟨m, hm.symm⟩
  refine ⟨v, hv, ?_⟩
  rw [hv] at hval
  have hcast : ((F.e₁ * v + i * F.h : ℕ) : ℕ∞)
      = F.e₁ • ((v : ℕ) : ℕ∞) + ((i * F.h : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  exact_mod_cast hcast.trans hval

/-- `[K : resField X] = f₁` (C.04's clause, `private` there). -/
private theorem finrank_stageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Module.finrank (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) = F.f₁ := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨hirr, hdeg⟩ := F.hresirr H₀ hpin
  have hψ0 : F.frameRes H₀ hpin ≠ 0 := hirr.ne_zero
  rw [(AdjoinRoot.powerBasis hψ0).finrank, AdjoinRoot.powerBasis_dim hψ0]
  exact hdeg

/-- The letter generates: `deg (minpoly η) = [K : resField X]`. -/
private theorem natDegree_minpoly_stageLetter (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
    (minpoly (resField (Polynomial.X : Polynomial O)) (F.stageLetter H₀ hpin)).natDegree
      = Module.finrank (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  have hψ0 : F.frameRes H₀ hpin ≠ 0 := (F.hresirr H₀ hpin).1.ne_zero
  have hgen : (AdjoinRoot.powerBasis hψ0).gen = F.stageLetter H₀ hpin :=
    AdjoinRoot.powerBasis_gen hψ0
  rw [← hgen, (AdjoinRoot.powerBasis hψ0).natDegree_minpoly,
    (AdjoinRoot.powerBasis hψ0).finrank]

theorem KeyFrame.slotRes_ne_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {A : Polynomial O} {k : ℕ} (hA : A.natDegree < F.e₁ * F.f₁)
    (hht : F.stageHeight A = (k : ℕ∞)) :
    F.slotRes H₀ hpin k A ≠ 0 := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  -- ## Step 1 — the attaining slot
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  obtain ⟨j, hjmem, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (A.natDegree + 1)) Finset.nonempty_range_add_one
      (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞))
  rw [hinf, hjeq] at hht
  obtain ⟨v, hvval, hv⟩ :=
    slot_value_nat F (A := A) (i := j) (k := k) (by rw [Nat.mul_comm]; exact hht)
  have hjlt : j < F.e₁ * F.f₁ :=
    lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)) hA
  have hcls : j % F.e₁ = F.slotIdx k := by
    refine F.slotIdx_unique (Nat.mod_lt _ F.he₁) ?_
    calc (j % F.e₁) * F.h ≡ j * F.h [MOD F.e₁] := (Nat.mod_modEq j F.e₁).mul_right F.h
      _ ≡ k [MOD F.e₁] :=
          F.stageHeight_class (A := A) (i := j) (k := k)
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem))
            (by rw [Nat.mul_comm] at hht; exact_mod_cast hht)
  have hsplit : F.slotIdx k + F.e₁ * (j / F.e₁) = j := by
    rw [← hcls]; exact Nat.mod_add_div j F.e₁
  have htf : j / F.e₁ < F.f₁ :=
    (Nat.div_lt_iff_lt_mul F.he₁).mpr (by rw [Nat.mul_comm]; exact hjlt)
  have hmem : j / F.e₁ ∈ F.slotWindow k := by
    rw [KeyFrame.slotWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨htf, by rw [hsplit]; omega⟩
  -- ## Step 2 — the digit at that slot is nonzero
  have hdigidx : (k - j * F.h) / F.e₁ = v := by
    have hkj : k - j * F.h = F.e₁ * v := by omega
    rw [hkj, Nat.mul_div_cancel_left _ F.he₁]
  have hpow : ∀ m : ℕ, π ^ m ∣ A.coeff j ↔ (m : ℕ∞) ≤ addVal O (A.coeff j) := by
    intro m
    rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  have hdvd : π ^ v ∣ A.coeff j := (hpow v).mpr (by rw [hvval])
  have hdig : digAt π v (A.coeff j) ≠ 0 := by
    rw [Ne, digAt_eq_zero_iff hπ hdvd]
    intro hcon
    rw [hpow, hvval] at hcon
    exact absurd (by exact_mod_cast hcon : v + 1 ≤ v) (by omega)
  -- ## Step 3 — the power basis kills the sum
  intro hzero
  set l : ℕ → resField (Polynomial.X : Polynomial O) := fun t =>
    if t ∈ F.slotWindow k then
      algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
        (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
          (A.coeff (F.slotIdx k + F.e₁ * t)))
    else 0 with hl
  have hsub : F.slotWindow k ⊆ Finset.range F.f₁ := Finset.filter_subset _ _
  have hG0 : ∑ i : Fin F.f₁,
      algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) (l (i : ℕ))
        * F.stageLetter H₀ hpin ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun t => algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) (l t)
        * F.stageLetter H₀ hpin ^ t) F.f₁]
    rw [← Finset.sum_subset hsub (fun x _ hx => by simp [hl, hx])]
    rw [← hzero, KeyFrame.slotRes]
    exact Finset.sum_congr rfl (fun x hx => by simp [hl, hx])
  have hf : F.f₁ = Module.finrank (resField (Polynomial.X : Polynomial O))
      (F.stageField H₀ hpin) := (finrank_stageField F H₀ hpin).symm
  have hint : IsIntegral (resField (Polynomial.X : Polynomial O)) (F.stageLetter H₀ hpin) :=
    AdjoinRoot.isIntegral_root (F.hresirr H₀ hpin).1.ne_zero
  have hall := Uniformity.Density.Induction.eta_independent
    (natDegree_minpoly_stageLetter F H₀ hpin) hint hf (fun i : Fin F.f₁ => l (i : ℕ)) hG0
  have hlt : l (j / F.e₁) = 0 := hall ⟨j / F.e₁, htf⟩
  rw [hl] at hlt
  simp only [if_pos hmem, hsplit, hdigidx] at hlt
  exact hdig ((injective_iff_map_eq_zero _).mp
    (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))).injective _ hlt)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotRes_ne_zero

end AxCheck
