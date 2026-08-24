/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C08
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C109
import Uniformity.ChapC.C131w

/-!
# Uniformity.ChapC.C131y — C.72 faithful band

**Chapter C, NODE C.131y′ — C.72 faithful band**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §3.9 and §5, row C.131y′).

This file proves the residual stability lemma `dv2Res_add_deep`: adding a summand whose
level-two height is strictly greater than the finite height of the leading summand leaves
its coherent level-two residual read unchanged.  Together with C.131w′'s `shadow_floor`
and C.131x′'s strict height equality, this gives C.72's signed faithful-band theorem.

The proof is uncapped and uses the definitions from C.22/C.25/C.38a directly.  A strict
global `dv2Hgt` inequality makes the perturbation strictly deeper at every coefficient
consulted by `dvResPoly`; `twistRead_add_deep` then fixes each residual coefficient.

## Status

Sorry-free and axiom-free (Lean core only); no exact-multiplicativity cite is consumed.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131y

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131t Uniformity.Density.Tower.C131w

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — height and slot-read stability off ties -/

section Height

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- `-1` has valuation zero. -/
private theorem addVal_neg_one : addVal O (-1 : O) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.2 isUnit_one.neg

/-- The coefficient valuation does not see negation. -/
theorem addVal_neg (x : O) : addVal O (-x) = addVal O x := by
  have hneg : (-x : O) = (-1 : O) * x := by ring
  rw [hneg, IsDiscreteValuationRing.addVal_mul, addVal_neg_one, zero_add]

/-- The Gauss height does not see negation. -/
theorem gaussVal_neg (a : Polynomial O) : gaussVal (-a) = gaussVal a := by
  have hdeg : (-a).natDegree = a.natDegree := Polynomial.natDegree_neg a
  simp only [gaussVal, hdeg]
  refine Finset.inf_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_neg, addVal_neg]

/-- `suppVal` does not see negation. -/
theorem suppVal_neg (hφ : φ.Monic) (a : Polynomial O) :
    suppVal φ (-a) u ℓ = suppVal φ a u ℓ := by
  have hdeg : (-a).natDegree = a.natDegree := Polynomial.natDegree_neg a
  simp only [suppVal, hdeg]
  refine Finset.inf_congr rfl fun j _ => ?_
  congr 1
  congr 1
  show gaussVal (dev φ (-a) j) = gaussVal (dev φ a j)
  rw [C131w.dev_neg hφ, gaussVal_neg]

/-- Ultrametric equality off ties for cleared support values. -/
theorem suppVal_add_eq_left_of_lt (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) (u : ℕ) {a b : Polynomial O}
    (h : suppVal φ a u ℓ < suppVal φ b u ℓ) :
    suppVal φ (a + b) u ℓ = suppVal φ a u ℓ := by
  have h1 : suppVal φ a u ℓ ≤ suppVal φ (a + b) u ℓ := by
    have hmin := min_suppVal_le_suppVal_add hφ hd hℓ u a b
    rwa [min_eq_left h.le] at hmin
  have hnegb : suppVal φ (-b) u ℓ = suppVal φ b u ℓ := suppVal_neg hφ b
  have heq : a + b + -b = a := by ring
  have h2 : suppVal φ (a + b) u ℓ ≤ suppVal φ a u ℓ := by
    by_contra hcon
    push Not at hcon
    have hb' : suppVal φ a u ℓ < suppVal φ (-b) u ℓ := by rwa [hnegb]
    have hmin2 := min_suppVal_le_suppVal_add hφ hd hℓ u (a + b) (-b)
    rw [heq] at hmin2
    exact absurd hmin2 (not_le.mpr (lt_min hcon hb'))
  exact le_antisymm h2 h1

end Height

/-- A stage height is unchanged by adding a strictly deeper polynomial. -/
theorem stageHeight_add_eq_left_of_lt (F : KeyFrame O π) {A B : Polynomial O}
    (h : F.stageHeight A < F.stageHeight B) :
    F.stageHeight (A + B) = F.stageHeight A :=
  suppVal_add_eq_left_of_lt Polynomial.monic_X (by simp) F.he₁ F.h h

/-- A fixed `F.key`-development height is unchanged by a strictly deeper digit. -/
theorem dvHgt_add_eq_left_of_lt (F : KeyFrame O π) {A B : Polynomial O} {j : ℕ}
    (h : dvHgt F A j < dvHgt F B j) :
    dvHgt F (A + B) j = dvHgt F A j := by
  show F.stageHeight (dev F.key (A + B) j) = F.stageHeight (dev F.key A j)
  rw [dev_add_of_monic F.hmonic]
  exact stageHeight_add_eq_left_of_lt F h

/-! ### Slot reads -/

private theorem digAt_index_spec (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
        + (F.slotIdx k + F.e₁ * t) * F.h = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have hmem := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact hmem.2
  have hdvd : F.e₁ ∣ k - (F.slotIdx k + F.e₁ * t) * F.h := by
    refine (Nat.modEq_iff_dvd' hle).mp ?_
    calc
      (F.slotIdx k + F.e₁ * t) * F.h
          = F.slotIdx k * F.h + F.e₁ * (t * F.h) := by ring
      _ ≡ F.slotIdx k * F.h + 0 [MOD F.e₁] :=
        Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr ⟨t * F.h, rfl⟩)
      _ = F.slotIdx k * F.h := by ring
      _ ≡ k [MOD F.e₁] := (F.slotIdx_spec k).2
  rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hle]

private theorem gaussVal_C (c : O) : gaussVal (Polynomial.C c) = addVal O c := by
  rw [gaussVal, Polynomial.natDegree_C, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_C_zero]

private theorem nsmul_top_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr hn.ne']

private theorem dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

private theorem addVal_coeff_of_stageHeight_lt (F : KeyFrame O π) {B : Polynomial O}
    {k pos q : ℕ} (hspec : F.e₁ * q + pos * F.h = k)
    (hk : (k : ℕ∞) < F.stageHeight B) :
    ((q + 1 : ℕ) : ℕ∞) ≤ addVal O (B.coeff pos) := by
  have hstep : F.stageHeight B
      ≤ F.e₁ • addVal O (B.coeff pos) + (F.h * pos : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    by_cases hposle : pos ≤ B.natDegree
    · have hle := Finset.inf_le
          (f := fun i => F.e₁ • gaussVal (Polynomial.C (B.coeff i))
            + (F.h * i : ℕ∞))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hposle))
      rwa [gaussVal_C] at hle
    · have hz : B.coeff pos = 0 := B.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, addVal_zero, nsmul_top_pos F.he₁, top_add]
      exact le_top
  have hlt : (k : ℕ∞)
      < F.e₁ • addVal O (B.coeff pos) + (F.h * pos : ℕ∞) :=
    lt_of_lt_of_le hk hstep
  rcases eq_or_ne (addVal O (B.coeff pos)) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hv] at hlt ⊢
    have hcast : F.e₁ • ((v : ℕ) : ℕ∞) + (F.h : ℕ∞) * (pos : ℕ∞)
        = ((F.e₁ * v + F.h * pos : ℕ) : ℕ∞) := by
      push_cast [nsmul_eq_mul]
      ring
    rw [hcast] at hlt
    have hnat : k < F.e₁ * v + F.h * pos := by exact_mod_cast hlt
    rw [Nat.mul_comm pos F.h] at hspec
    have hqv : F.e₁ * q < F.e₁ * v := by
      have : F.e₁ * q + pos * F.h < F.e₁ * v + F.h * pos := by
        calc
          F.e₁ * q + pos * F.h = F.e₁ * q + F.h * pos := by ring
          _ = k := hspec
          _ < F.e₁ * v + F.h * pos := hnat
      omega
    have : q < v := Nat.lt_of_mul_lt_mul_left hqv
    exact_mod_cast (by omega : q + 1 ≤ v)

/-- `slotRes` at height `k` ignores an additive summand of stage height strictly above `k`. -/
theorem slotRes_add_deep (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {A B : Polynomial O} {k : ℕ}
    (hk : (k : ℕ∞) < F.stageHeight B) :
    F.slotRes H₀ hpin k (A + B) = F.slotRes H₀ hpin k A := by
  rw [KeyFrame.slotRes, KeyFrame.slotRes]
  refine Finset.sum_congr rfl fun t ht => ?_
  set q := (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁
  set pos := F.slotIdx k + F.e₁ * t
  have hspec : F.e₁ * q + pos * F.h = k := digAt_index_spec F k t ht
  have hb : ((q + 1 : ℕ) : ℕ∞) ≤ addVal O (B.coeff pos) :=
    addVal_coeff_of_stageHeight_lt F hspec hk
  have hdvd : π ^ (q + 1) ∣ B.coeff pos := dvd_of_le_addVal hπ hb
  have hdig : digAt π q (A.coeff pos) = digAt π q ((A + B).coeff pos) := by
    refine C109asm.digAt_congr hπ ?_
    have heq : (A + B).coeff pos - A.coeff pos = B.coeff pos := by
      rw [Polynomial.coeff_add]
      ring
    rw [heq]
    exact hdvd
  rw [hdig]

/-- `twistRead` at height `k` ignores an additive summand of stage height strictly above `k`. -/
theorem twistRead_add_deep (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {A B : Polynomial O} {k : ℕ}
    (hk : (k : ℕ∞) < F.stageHeight B) :
    F.twistRead H₀ hpin k (A + B) = F.twistRead H₀ hpin k A := by
  rw [KeyFrame.twistRead, KeyFrame.twistRead, slotRes_add_deep F hπ H₀ hpin hk]

/-! ## Part 2 — support and side stability -/

/-- A development height does not see negation. -/
theorem dvHgt_neg (F : KeyFrame O π) (A : Polynomial O) (j : ℕ) :
    dvHgt F (-A) j = dvHgt F A j := by
  show F.stageHeight (dev F.key (-A) j) = F.stageHeight (dev F.key A j)
  rw [C131w.dev_neg F.hmonic]
  exact suppVal_neg Polynomial.monic_X (dev F.key A j)

/-- The fixed-coordinate development height is ultrametric. -/
theorem dvHgt_add_min (F : KeyFrame O π) (A B : Polynomial O) (j : ℕ) :
    min (dvHgt F A j) (dvHgt F B j) ≤ dvHgt F (A + B) j := by
  show min (F.stageHeight (dev F.key A j)) (F.stageHeight (dev F.key B j))
    ≤ F.stageHeight (dev F.key (A + B) j)
  rw [dev_add_of_monic F.hmonic]
  exact min_suppVal_le_suppVal_add Polynomial.monic_X (by simp) F.he₁ F.h _ _

/-- Development digits above the polynomial's degree have top stage height. -/
theorem dvHgt_eq_top_of_natDegree_lt (F : KeyFrame O π) (A : Polynomial O) {j : ℕ}
    (hj : A.natDegree < j) : dvHgt F A j = ⊤ := by
  have hj' : A.natDegree < j * F.key.natDegree := by
    have hkey := F.natDegree_key_pos
    nlinarith
  rw [dvHgt, dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos A j hj',
    KeyFrame.stageHeight_zero]

/-- The support infimum lies below the weighted height at every abscissa, including those
past the defining finite range (where the development digit has top height). -/
theorem dvSupp_le_term (F : KeyFrame O π) (A : Polynomial O) (u : ℕ) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (j : ℕ) :
    dvSupp F A u ℓ ≤ ℓ • dvHgt F A j + (u * j : ℕ∞) := by
  by_cases hj : j ≤ A.natDegree
  · unfold dvSupp
    exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [dvHgt_eq_top_of_natDegree_lt F A (by omega), nsmul_top_pos hℓ, top_add]
    exact le_top

private theorem dvTerm_add_min (F : KeyFrame O π) (A B : Polynomial O)
    (u ℓ j : ℕ) :
    min (ℓ • dvHgt F A j + (u * j : ℕ∞))
        (ℓ • dvHgt F B j + (u * j : ℕ∞))
      ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by
  have hmin := dvHgt_add_min F A B j
  rcases le_total (dvHgt F A j) (dvHgt F B j) with hab | hba
  · rw [min_eq_left hab] at hmin
    calc
      min (ℓ • dvHgt F A j + (u * j : ℕ∞))
          (ℓ • dvHgt F B j + (u * j : ℕ∞))
          ≤ ℓ • dvHgt F A j + (u * j : ℕ∞) := min_le_left _ _
      _ ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by gcongr
  · rw [min_eq_right hba] at hmin
    calc
      min (ℓ • dvHgt F A j + (u * j : ℕ∞))
          (ℓ • dvHgt F B j + (u * j : ℕ∞))
          ≤ ℓ • dvHgt F B j + (u * j : ℕ∞) := min_le_right _ _
      _ ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by gcongr

/-- Adding a summand of strictly larger support leaves the support unchanged. -/
theorem dvSupp_add_eq_left_of_lt (F : KeyFrame O π) {A B : Polynomial O}
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) (h : dvSupp F A u ℓ < dvSupp F B u ℓ) :
    dvSupp F (A + B) u ℓ = dvSupp F A u ℓ := by
  have hfinite : dvSupp F A u ℓ ≠ ⊤ := ne_top_of_lt h
  obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_inf
    (Finset.range (A.natDegree + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => ℓ • dvHgt F A j + (u * j : ℕ∞))
  have hcoord : dvHgt F A j₀ < dvHgt F B j₀ := by
    have hterm : ℓ • dvHgt F A j₀ + (u * j₀ : ℕ∞)
        < ℓ • dvHgt F B j₀ + (u * j₀ : ℕ∞) := by
      calc
        ℓ • dvHgt F A j₀ + (u * j₀ : ℕ∞) = dvSupp F A u ℓ := hj₀.symm
        _ < dvSupp F B u ℓ := h
        _ ≤ ℓ • dvHgt F B j₀ + (u * j₀ : ℕ∞) := dvSupp_le_term F B u hℓ j₀
    have hoff : (u * j₀ : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    exact lt_of_nsmul_lt_nsmul_right ℓ ((ENat.add_lt_add_iff_right hoff).mp hterm)
  have hu : dvSupp F (A + B) u ℓ ≤ dvSupp F A u ℓ := by
    calc
      dvSupp F (A + B) u ℓ
          ≤ ℓ • dvHgt F (A + B) j₀ + (u * j₀ : ℕ∞) :=
        dvSupp_le_term F (A + B) u hℓ j₀
      _ = ℓ • dvHgt F A j₀ + (u * j₀ : ℕ∞) := by
        rw [dvHgt_add_eq_left_of_lt F hcoord]
      _ = dvSupp F A u ℓ := hj₀.symm
  have hl : dvSupp F A u ℓ ≤ dvSupp F (A + B) u ℓ := by
    unfold dvSupp
    refine Finset.le_inf fun j hj => ?_
    have hA := dvSupp_le_term F A u hℓ j
    have hB := (le_of_lt h).trans (dvSupp_le_term F B u hℓ j)
    exact (le_min hA hB).trans (dvTerm_add_min F A B u ℓ j)
  exact le_antisymm hu hl

private theorem dvOnSide_of_mem {F : KeyFrame O π} {A : Polynomial O} {u ℓ j : ℕ}
    (hj : j ∈ dvSideSet F A u ℓ) : DvOnSide F A u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (A.natDegree + 1)).filter
    (DvOnSide F A u ℓ) from hj)).2

private theorem mem_dvSideSet_of_dvOnSide {F : KeyFrame O π} {A : Polynomial O}
    {u ℓ j : ℕ} (hj : DvOnSide F A u ℓ j) : j ∈ dvSideSet F A u ℓ := by
  classical
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hj⟩
  by_contra hdeg
  exact hj.2 (dvHgt_eq_top_of_natDegree_lt F A (by omega))

private theorem coord_lt_of_onSide_of_deep (F : KeyFrame O π) {A B : Polynomial O}
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {m j : ℕ}
    (hval : dvSupp F A u ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B u ℓ) (hj : DvOnSide F A u ℓ j) :
    dvHgt F A j < dvHgt F B j := by
  have hterm : ℓ • dvHgt F A j + (u * j : ℕ∞)
      < ℓ • dvHgt F B j + (u * j : ℕ∞) := by
    calc
      ℓ • dvHgt F A j + (u * j : ℕ∞) = (m : ℕ∞) := hj.1.symm.trans hval
      _ < dvSupp F B u ℓ := hdeep
      _ ≤ ℓ • dvHgt F B j + (u * j : ℕ∞) := dvSupp_le_term F B u hℓ j
  exact lt_of_nsmul_lt_nsmul_right ℓ
    ((ENat.add_lt_add_iff_right (ENat.coe_ne_top (u * j))).mp hterm)

/-- A strictly deeper perturbation leaves the complete level-one side set unchanged. -/
theorem dvSideSet_add_deep (F : KeyFrame O π) {A B : Polynomial O}
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {m : ℕ}
    (hval : dvSupp F A u ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B u ℓ) :
    dvSideSet F (A + B) u ℓ = dvSideSet F A u ℓ := by
  classical
  have hsupp : dvSupp F (A + B) u ℓ = (m : ℕ∞) :=
    (dvSupp_add_eq_left_of_lt F u hℓ (hval.trans_lt hdeep)).trans hval
  ext j
  constructor
  · intro hj
    have honSum := dvOnSide_of_mem hj
    have hcoord : dvHgt F (A + B) j < dvHgt F (-B) j := by
      rw [dvHgt_neg]
      exact coord_lt_of_onSide_of_deep F u hℓ hsupp hdeep honSum
    have hheight : dvHgt F A j = dvHgt F (A + B) j := by
      have hadd := dvHgt_add_eq_left_of_lt F hcoord
      have hpoly : A + B + -B = A := by ring
      rwa [hpoly] at hadd
    refine mem_dvSideSet_of_dvOnSide ⟨?_, ?_⟩
    · rw [hheight]
      exact hval.trans (hsupp.symm.trans honSum.1)
    · rw [hheight]
      exact honSum.2
  · intro hj
    have honA := dvOnSide_of_mem hj
    have hcoord := coord_lt_of_onSide_of_deep F u hℓ hval hdeep honA
    have hheight := dvHgt_add_eq_left_of_lt F hcoord
    refine mem_dvSideSet_of_dvOnSide ⟨?_, ?_⟩
    · rw [hheight]
      exact hsupp.trans (hval.symm.trans honA.1)
    · rw [hheight]
      exact honA.2

/-! ## Part 3 — residual-polynomial stability -/

private theorem min'_congr {s t : Finset ℕ} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst t
  congr

private theorem max'_congr {s t : Finset ℕ} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.max' hs = t.max' ht := by
  subst t
  congr

private theorem dvOnSide_nat_eq {F : KeyFrame O π} {u ℓ : ℕ}
    {A : Polynomial O} {j j' H H' : ℕ}
    (hH : dvHgt F A j = (H : ℕ∞)) (hH' : dvHgt F A j' = (H' : ℕ∞))
    (hj : DvOnSide F A u ℓ j) (hj' : DvOnSide F A u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have e : ℓ • (H : ℕ∞) + (u * j : ℕ∞)
      = ℓ • (H' : ℕ∞) + (u * j' : ℕ∞) := by
    rw [← hH, ← hH', ← hj.1, hj'.1]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞)
      = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

/-- A finite support has a nonempty side set. -/
theorem dvSideSet_nonempty_of_dvSupp_eq_coe (F : KeyFrame O π) (A : Polynomial O)
    (u : ℕ) {ℓ m : ℕ} (hℓ : 0 < ℓ) (hval : dvSupp F A u ℓ = (m : ℕ∞)) :
    (dvSideSet F A u ℓ).Nonempty := by
  obtain ⟨j, hjmem, hj⟩ := Finset.exists_mem_eq_inf
    (Finset.range (A.natDegree + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun i => ℓ • dvHgt F A i + (u * i : ℕ∞))
  have hfinite : dvHgt F A j ≠ ⊤ := by
    intro htop
    have hterm : ℓ • dvHgt F A j + (u * j : ℕ∞) = ⊤ := by
      rw [htop, nsmul_top_pos hℓ, top_add]
    have : (m : ℕ∞) = ⊤ := hval.symm.trans (hj.trans hterm)
    exact ENat.coe_ne_top m this
  exact ⟨j, mem_dvSideSet_of_dvOnSide ⟨by simpa [dvSupp] using hj, hfinite⟩⟩

private theorem read_height_lt_of_deep {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {A B : Polynomial O} {m M : ℕ}
    (hval : dvSupp F A L.u L.ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B L.u L.ℓ)
    (hne : (dvSideSet F A L.u L.ℓ).Nonempty)
    (hpinM : dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞))
    {t : ℕ} (ht : t < dvSideDeg F A L.u L.ℓ hne + 1) :
    ((M - t * L.u : ℕ) : ℕ∞)
      < dvHgt F B (dvSideMin F A L.u L.ℓ hne + t * L.ℓ) := by
  let jmin := dvSideMin F A L.u L.ℓ hne
  let jmax := dvSideMax F A L.u L.ℓ hne
  let d := dvSideDeg F A L.u L.ℓ hne
  have hminmem : jmin ∈ dvSideSet F A L.u L.ℓ := Finset.min'_mem _ _
  have hmaxmem : jmax ∈ dvSideSet F A L.u L.ℓ := Finset.max'_mem _ _
  have hminon : DvOnSide F A L.u L.ℓ jmin := dvOnSide_of_mem hminmem
  have hmaxon : DvOnSide F A L.u L.ℓ jmax := dvOnSide_of_mem hmaxmem
  obtain ⟨Hmax, hHmax⟩ : ∃ Hmax : ℕ, dvHgt F A jmax = (Hmax : ℕ∞) := by
    rcases ENat.ne_top_iff_exists.mp hmaxon.2 with ⟨Hmax, hh⟩
    exact ⟨Hmax, hh.symm⟩
  have hle : jmin ≤ jmax := Finset.min'_le _ _ hmaxmem
  have hlen := dvSideLen_eq F L.hℓ L.hcop hne
  have hmaxeq : jmax = jmin + L.ℓ * d := by
    change jmax - jmin = L.ℓ * d at hlen
    omega
  have hsideeq : L.ℓ * M + L.u * jmin = L.ℓ * Hmax + L.u * jmax :=
    dvOnSide_nat_eq hpinM hHmax hminon hmaxon
  have hMeq : M = Hmax + L.u * d := by
    have hmul : L.ℓ * M = L.ℓ * (Hmax + L.u * d) := by
      rw [hmaxeq] at hsideeq
      nlinarith
    simpa [d] using Nat.eq_of_mul_eq_mul_left L.hℓ hmul
  have htu : t * L.u ≤ M := by
    have htd : t ≤ d := by change t < d + 1 at ht; omega
    rw [hMeq]
    calc
      t * L.u ≤ d * L.u := Nat.mul_le_mul_right L.u htd
      _ = L.u * d := by ring
      _ ≤ Hmax + L.u * d := Nat.le_add_left _ _
  have hmNat : m = L.ℓ * M + L.u * jmin := by
    have he : (m : ℕ∞) = L.ℓ • (M : ℕ∞) + (L.u * jmin : ℕ∞) := by
      rw [← hval, hminon.1, hpinM]
    have he' : ((m : ℕ) : ℕ∞) = ((L.ℓ * M + L.u * jmin : ℕ) : ℕ∞) := by
      simpa [nsmul_eq_mul] using he
    exact ENat.coe_inj.mp he'
  let k := M - t * L.u
  let j := jmin + t * L.ℓ
  have hweighted : L.ℓ * k + L.u * j = m := by
    dsimp [k, j]
    rw [hmNat]
    have hmul_le : L.ℓ * (t * L.u) ≤ L.ℓ * M := Nat.mul_le_mul_left L.ℓ htu
    have hcross : L.ℓ * (t * L.u) = L.u * (t * L.ℓ) := by ring
    rw [Nat.mul_sub_left_distrib, Nat.mul_add]
    calc
      (L.ℓ * M - L.ℓ * (t * L.u)) + (L.u * jmin + L.u * (t * L.ℓ))
          = (L.ℓ * M - L.ℓ * (t * L.u)) +
              (L.u * jmin + L.ℓ * (t * L.u)) := by rw [hcross]
      _ = (L.ℓ * M - L.ℓ * (t * L.u) + L.ℓ * (t * L.u)) + L.u * jmin := by
        ac_rfl
      _ = L.ℓ * M + L.u * jmin := by rw [Nat.sub_add_cancel hmul_le]
  have hterm : (m : ℕ∞)
      < L.ℓ • dvHgt F B j + (L.u * j : ℕ∞) :=
    hdeep.trans_le (dvSupp_le_term F B L.u L.hℓ j)
  have hweighted' : L.ℓ • (k : ℕ∞) + (L.u * j : ℕ∞) = (m : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    exact_mod_cast hweighted
  rw [← hweighted'] at hterm
  have hsmul : L.ℓ • (k : ℕ∞) < L.ℓ • dvHgt F B j :=
    (ENat.add_lt_add_iff_right (ENat.coe_ne_top (L.u * j))).mp hterm
  exact lt_of_nsmul_lt_nsmul_right L.ℓ hsmul

/-- The normalized level residual polynomial is unchanged by a strictly deeper additive
perturbation. -/
theorem dvResPoly_add_deep {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A B : Polynomial O} {m : ℕ}
    (hval : dvSupp F A L.u L.ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B L.u L.ℓ)
    (hne : (dvSideSet F A L.u L.ℓ).Nonempty)
    (hne' : (dvSideSet F (A + B) L.u L.ℓ).Nonempty)
    {M M' : ℕ}
    (hpinM : dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞))
    (hpinM' : dvHgt F (A + B) (dvSideMin F (A + B) L.u L.ℓ hne') = (M' : ℕ∞)) :
    dvResPoly F H₀ hpin (A + B) L.u L.ℓ hne' M' hpinM'
      = dvResPoly F H₀ hpin A L.u L.ℓ hne M hpinM := by
  have hset := dvSideSet_add_deep F L.u L.hℓ hval hdeep
  have hmin : dvSideMin F (A + B) L.u L.ℓ hne'
      = dvSideMin F A L.u L.ℓ hne := min'_congr hset hne' hne
  have hmax : dvSideMax F (A + B) L.u L.ℓ hne'
      = dvSideMax F A L.u L.ℓ hne := max'_congr hset hne' hne
  have hdeg : dvSideDeg F (A + B) L.u L.ℓ hne'
      = dvSideDeg F A L.u L.ℓ hne := by
    rw [dvSideDeg, dvSideDeg, hmin, hmax]
  have hminmem : dvSideMin F A L.u L.ℓ hne ∈ dvSideSet F A L.u L.ℓ :=
    Finset.min'_mem _ _
  have hcoord := coord_lt_of_onSide_of_deep F L.u L.hℓ hval hdeep
    (dvOnSide_of_mem hminmem)
  have hheight := dvHgt_add_eq_left_of_lt F hcoord
  have hMM : M' = M := by
    rw [hmin, hheight] at hpinM'
    exact_mod_cast hpinM'.symm.trans hpinM
  subst M'
  rw [dvResPoly, dvResPoly, hdeg, hmin]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [dev_add_of_monic F.hmonic, twistRead_add_deep F hπ H₀ hpin
    (read_height_lt_of_deep L hval hdeep hne hpinM (Finset.mem_range.mp ht))]

/-! ## Part 4 — coherent-read stability and C.72 -/

set_option maxHeartbeats 1000000 in
/-- **NODE C.131y′ (`Cnv16`).** If `A` has finite level-two height `m` and `B` is
strictly deeper, the coherent level-two residual read of `A + B` equals that of `A`. -/
theorem dv2Res_add_deep {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A B : Polynomial O} {m : ℕ}
    (hval : dv2Hgt L A = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dv2Hgt L B) :
    dv2Res L (A + B) = dv2Res L A := by
  classical
  change dvSupp F A L.u L.ℓ = (m : ℕ∞) at hval
  change (m : ℕ∞) < dvSupp F B L.u L.ℓ at hdeep
  have hne : (dvSideSet F A L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty_of_dvSupp_eq_coe F A L.u L.hℓ hval
  have hset := dvSideSet_add_deep F L.u L.hℓ hval hdeep
  have hne' : (dvSideSet F (A + B) L.u L.ℓ).Nonempty := by
    simpa only [hset] using hne
  have hminmem : dvSideMin F A L.u L.ℓ hne ∈ dvSideSet F A L.u L.ℓ :=
    Finset.min'_mem _ _
  have hminon : DvOnSide F A L.u L.ℓ (dvSideMin F A L.u L.ℓ hne) :=
    dvOnSide_of_mem hminmem
  obtain ⟨M, hpinM⟩ : ∃ M : ℕ,
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞) := by
    rcases ENat.ne_top_iff_exists.mp hminon.2 with ⟨M, hM⟩
    exact ⟨M, hM.symm⟩
  have hmin : dvSideMin F (A + B) L.u L.ℓ hne'
      = dvSideMin F A L.u L.ℓ hne := min'_congr hset hne' hne
  have hcoord := coord_lt_of_onSide_of_deep F L.u L.hℓ hval hdeep hminon
  have hheight := dvHgt_add_eq_left_of_lt F hcoord
  have hpinM' : dvHgt F (A + B) (dvSideMin F (A + B) L.u L.ℓ hne')
      = (M : ℕ∞) := by
    rw [hmin, hheight]
    exact hpinM
  let hexA : ∃ (hneA : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hneA) = (M₀ : ℕ∞) := ⟨hne, M, hpinM⟩
  let hexAB : ∃ (hneAB : (dvSideSet F (A + B) L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F (A + B) (dvSideMin F (A + B) L.u L.ℓ hneAB) = (M₀ : ℕ∞) :=
    ⟨hne', M, hpinM'⟩
  rw [dv2Res, dv2Res, dif_pos hexAB, dif_pos hexA]
  congr 1
  exact dvResPoly_add_deep L hπ hval hdeep hexA.choose hexAB.choose
    hexA.choose_spec.choose_spec hexAB.choose_spec.choose_spec

/-- ★ **NODE C.131y′ — C.72 `shadow_faithful_band`.** Below the discrepancy floor,
the shadow digit has exactly the honest digit's height and coherent residual read. -/
theorem shadow_faithful_band {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂)
    {m : ℕ} (hm : m < T.theta μ₂ j)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j) := by
  let A := dev (composedKey T) f j
  let B := shadowDev T f j - dev (composedKey T) f j
  change dv2Hgt (T.levelDatum hπ) A = (m : ℕ∞) at hval
  have hfloor : (T.theta μ₂ j : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) B :=
    shadow_floor T hπ hh hf hj
  have hstrict : (m : ℕ∞) < dv2Hgt (T.levelDatum hπ) B := by
    exact (by exact_mod_cast hm : (m : ℕ∞) < (T.theta μ₂ j : ℕ∞)).trans_le hfloor
  have hstrictA : dv2Hgt (T.levelDatum hπ) A < dv2Hgt (T.levelDatum hπ) B :=
    hval.trans_lt hstrict
  have hadd : A + B = shadowDev T f j := by
    dsimp [A, B]
    ring
  constructor
  · rw [← hadd]
    exact (dv2Hgt_add_eq_left_of_lt T hπ A B hstrictA).trans hval
  · rw [← hadd]
    exact dv2Res_add_deep (T.levelDatum hπ) hπ hval hstrict

end Uniformity.Density.Tower.C131y

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131y.gaussVal_neg
#print axioms Uniformity.Density.Tower.C131y.addVal_neg
#print axioms Uniformity.Density.Tower.C131y.suppVal_neg
#print axioms Uniformity.Density.Tower.C131y.suppVal_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131y.stageHeight_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131y.dvHgt_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131y.slotRes_add_deep
#print axioms Uniformity.Density.Tower.C131y.twistRead_add_deep
#print axioms Uniformity.Density.Tower.C131y.dvHgt_neg
#print axioms Uniformity.Density.Tower.C131y.dvHgt_add_min
#print axioms Uniformity.Density.Tower.C131y.dvHgt_eq_top_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C131y.dvSupp_le_term
#print axioms Uniformity.Density.Tower.C131y.dvSupp_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131y.dvSideSet_add_deep
#print axioms Uniformity.Density.Tower.C131y.dvSideSet_nonempty_of_dvSupp_eq_coe
#print axioms Uniformity.Density.Tower.C131y.dvResPoly_add_deep
#print axioms Uniformity.Density.Tower.C131y.dv2Res_add_deep
#print axioms Uniformity.Density.Tower.C131y.shadow_faithful_band

end AxCheck
