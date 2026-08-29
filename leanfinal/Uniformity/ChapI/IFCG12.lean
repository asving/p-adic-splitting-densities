/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG11
import Uniformity.ChapC.C133h0leg
import Uniformity.ChapC.C130in

/-!
# Uniformity.ChapI.IFCG12 — the residual bridge, PROVED; the kernel and THE COVER, FIRED

This file closes the exhaustion kernel's residual bridge
`IFCG11.StrictRecentredFactorSideStatement`: every positive-degree monic factor of a
strictly recentred polynomial retains a genuine side above the frame floor.  With the
bridge landed, IFCG11's `recentredClusterDegreeExhaustion_of_factorSide` fires IFCG9's
kernel and IFCG10's assembled strong finite genre cover — the campaign's stop line.

The proof deviates from the dissection route: no C.33 dissection of the factor is needed.

* **Secant lemma** (§2, Lean-core).  If `g`'s `Φ′`-development has finite height `A₀` at
  index `0` and drops strictly below the floor line to some index `b ≥ 1`
  (`B + H·b < A₀`, `H := (e₁f₁)·h` the floor coefficient), then `g` has a genuine
  above-floor side: maximize the drop ratio `(A₀ − hgt y)/y` over the finite support,
  reduce the maximizing fraction to lowest terms `(u, ℓ)`; both `0` and the maximizer land
  in `dvSideSet F g u ℓ`, so `dvSideDeg` is positive by C.08's exact spacing law.
* **Last-side lemma** (§3, Lean-core).  Strict recentring plus the monic top digit
  (`dev_top_eq_one`, `stageHeight_one`) produce an above-floor coprime direction at which
  `dvSideMax F f = deg f / (e₁f₁)` — the polygon's final side, the whole reason the strict
  floor forces every dissection to spend the entire degree above floor.
* **Unfenced `dvSideMax` additivity** (§4).  Theorem M (`C133mh3.dvSideMax_mul`) at
  `0 < F.h`; at the degenerate `F.h = 0` frame the C133h0leg dictionary
  (`dvSideSet_eq_sideSet`) transports B.43's order-1 `sideMin`/`sideDeg` product laws, and
  the dv-level length law rebuilds the `sideMax` sum.  The bridge quantifies over ALL
  frames, so the degenerate leg is mandatory.
* **The bridge** (§5).  For monic `f = g·w` with `deg g > 0`: if `dvHgt F g 0 = ⊤` then
  `F.key ∣ g ∣ f`, contradiction; otherwise additivity at `f`'s last side pins
  `b := dvSideMax g ≥ 1` (since `w`'s side cap is `≤ deg w/(e₁f₁) ≤ m − 1`), the on-side
  equation against the index-`0` term gives the strict drop, and the secant lemma fires.

Fired in §6: the kernel, THE COVER (`finiteGenreCoverAt_strong_all`, ★★★), and the
`m ≤ 4` count recoveries (the cubic mass-3 and quartic mass-4 exhaustive gates).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG12

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.IFCG5 Uniformity.Density.IFCG9 Uniformity.Density.IFCG10
open Uniformity.Density.IFCG11

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## §1 — kit -/

/-- Positive scalar times `⊤` in `ℕ∞`. -/
theorem nsmul_top_of_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  rw [nsmul_eq_mul]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr hn.ne')

/-- Finite-height development term as a single `ℕ`-cast. -/
theorem term_coe {F : KeyFrame O π} {f : Polynomial O} {j A : ℕ} (ℓ u : ℕ)
    (hA : dvHgt F f j = (A : ℕ∞)) :
    ℓ • dvHgt F f j + (u * j : ℕ∞) = ((ℓ * A + u * j : ℕ) : ℕ∞) := by
  rw [hA, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]

/-- `ENat.toNat` reads a known finite value. -/
theorem toNat_of_eq_coe {x : ℕ∞} {n : ℕ} (h : x = (n : ℕ∞)) : x.toNat = n := by
  subst h; simp

/-- Every frame admits a pin: the key's `sideMin` height is finite. -/
theorem exists_pin (F : KeyFrame O π) : ∃ H₀ : ℕ, F.Pin H₀ := by
  have hfin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide F.he₁ (C133h0leg.suppVal_key_ne_top' F)
      (onSide_of_mem_sideSet (Finset.min'_mem _ F.hne))
  obtain ⟨H₀, hH₀⟩ := ENat.ne_top_iff_exists.mp hfin
  exact ⟨H₀, hH₀.symm⟩

/-- **Key escape.**  A `⊤` height at development index `0` means the zeroth digit
(`g %ₘ F.key`) vanishes, i.e. `F.key ∣ g`. -/
theorem key_dvd_of_dvHgt_zero_eq_top {F : KeyFrame O π} {g : Polynomial O}
    (h : dvHgt F g 0 = ⊤) : F.key ∣ g := by
  have hdev : dev F.key g 0 = 0 := by
    by_contra hne
    exact (F.stageHeight_ne_top hne) h
  have hmod : g %ₘ F.key = 0 := hdev
  exact (Polynomial.modByMonic_eq_zero_iff_dvd F.hmonic).mp hmod

/-! ## §2 — the secant lemma -/

/-- **The secant lemma.**  A strictly-above-floor secant from index `0` to some index
`b ≥ 1` of `g`'s dv-polygon forces a genuine above-floor side. -/
theorem hasGenuineAboveFloorSide_of_secant {F : KeyFrame O π} {g : Polynomial O}
    {b A₀ B : ℕ} (hb1 : 1 ≤ b)
    (hA : dvHgt F g 0 = (A₀ : ℕ∞)) (hB : dvHgt F g b = (B : ℕ∞))
    (hdrop : B + (F.e₁ * F.f₁) * F.h * b < A₀) :
    HasGenuineAboveFloorSide F g := by
  classical
  set H : ℕ := (F.e₁ * F.f₁) * F.h with hHdef
  -- the finite support of positive indices
  set S : Finset ℕ := (Finset.range (g.natDegree + 1)).filter
    (fun y => 1 ≤ y ∧ dvHgt F g y ≠ ⊤) with hSdef
  have hbS : b ∈ S := by
    have hble : b ≤ g.natDegree := by
      by_contra hlt
      have htop := C131y.dvHgt_eq_top_of_natDegree_lt F g (j := b) (by omega)
      rw [hB] at htop
      exact (ENat.coe_ne_top B) htop
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      hb1, by rw [hB]; exact ENat.coe_ne_top B⟩
  -- the drop ratio, maximized over the support
  set ρ : ℕ → ℚ := fun y => ((A₀ : ℚ) - ((dvHgt F g y).toNat : ℚ)) / (y : ℚ) with hρdef
  obtain ⟨y', hyS, hymax⟩ := S.exists_max_image ρ ⟨b, hbS⟩
  have hy1 : 1 ≤ y' := (Finset.mem_filter.mp hyS).2.1
  have hytop : dvHgt F g y' ≠ ⊤ := (Finset.mem_filter.mp hyS).2.2
  obtain ⟨B', hBy'⟩ := ENat.ne_top_iff_exists.mp hytop
  have hBy : dvHgt F g y' = (B' : ℕ∞) := hBy'.symm
  -- ratio values
  have hρb : ρ b = ((A₀ : ℚ) - (B : ℚ)) / (b : ℚ) := by
    simp only [hρdef, toNat_of_eq_coe hB]
  have hρy : ρ y' = ((A₀ : ℚ) - (B' : ℚ)) / (y' : ℚ) := by
    simp only [hρdef, toNat_of_eq_coe hBy]
  have hbposQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb1
  have hyposQ : (0 : ℚ) < (y' : ℚ) := by exact_mod_cast hy1
  -- the maximizer's ratio is strictly above the floor
  have hHb : (H : ℚ) < ρ b := by
    rw [hρb, lt_div_iff₀ hbposQ]
    have hQ : (B : ℚ) + (H : ℚ) * (b : ℚ) < (A₀ : ℚ) := by exact_mod_cast hdrop
    linarith
  have hHy : (H : ℚ) < ρ y' := lt_of_lt_of_le hHb (hymax b hbS)
  have hstarQ : (H : ℚ) * (y' : ℚ) < (A₀ : ℚ) - (B' : ℚ) := by
    rw [hρy, lt_div_iff₀ hyposQ] at hHy
    linarith
  have hstarN : B' + H * y' < A₀ := by
    have h1 : ((B' + H * y' : ℕ) : ℚ) < ((A₀ : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast h1
  have hBA : B' < A₀ := by omega
  set Δ : ℕ := A₀ - B' with hΔdef
  have hΔ : B' + Δ = A₀ := by omega
  have hΔgt : H * y' < Δ := by omega
  -- reduce the maximizing fraction to lowest terms
  set d : ℕ := Nat.gcd Δ y' with hddef
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right Δ (by omega)
  set u : ℕ := Δ / d with hudef
  set ℓ : ℕ := y' / d with hldef
  have hu : u * d = Δ := Nat.div_mul_cancel (Nat.gcd_dvd_left Δ y')
  have hl : ℓ * d = y' := Nat.div_mul_cancel (Nat.gcd_dvd_right Δ y')
  have hcop : Nat.Coprime u ℓ := Nat.coprime_div_gcd_div_gcd hdpos
  have hlpos : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h
    · rw [h0, Nat.zero_mul] at hl; omega
    · exact h
  have hfloor : ℓ * H < u := by
    have h1 : (ℓ * H) * d < u * d := by
      calc (ℓ * H) * d = H * (ℓ * d) := by ring
        _ = H * y' := by rw [hl]
        _ < Δ := hΔgt
        _ = u * d := hu.symm
    exact Nat.lt_of_mul_lt_mul_right h1
  -- the cleared support at the maximizing direction
  have hsupple : dvSupp F g u ℓ ≤ ((ℓ * A₀ : ℕ) : ℕ∞) := by
    have h1 := C131y.dvSupp_le_term F g u hlpos 0
    rw [term_coe ℓ u hA] at h1
    simpa using h1
  have hsuppge : ((ℓ * A₀ : ℕ) : ℕ∞) ≤ dvSupp F g u ℓ := by
    unfold dvSupp
    refine Finset.le_inf fun j hj => ?_
    by_cases htopj : dvHgt F g j = ⊤
    · rw [htopj, nsmul_top_of_pos hlpos, top_add]
      exact le_top
    · obtain ⟨Bj, hBj⟩ := ENat.ne_top_iff_exists.mp htopj
      rw [term_coe ℓ u hBj.symm, Nat.cast_le]
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have hBjA : Bj = A₀ := by
          have h2 : (Bj : ℕ∞) = (A₀ : ℕ∞) := by rw [hBj, hA]
          exact_mod_cast h2
        rw [hBjA]
        omega
      · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨hj, hjpos, htopj⟩
        have hmax := hymax j hjS
        have hρj : ρ j = ((A₀ : ℚ) - (Bj : ℚ)) / (j : ℚ) := by
          simp only [hρdef, toNat_of_eq_coe hBj.symm]
        have hjQ : (0 : ℚ) < (j : ℚ) := by exact_mod_cast hjpos
        rw [hρj, hρy, div_le_div_iff₀ hjQ hyposQ] at hmax
        -- hmax : (A₀ - Bj) * y' ≤ (A₀ - B') * j
        have hgoalQ : (ℓ : ℚ) * A₀ ≤ (ℓ : ℚ) * Bj + (u : ℚ) * j := by
          have hyd : (y' : ℚ) = (ℓ : ℚ) * d := by exact_mod_cast hl.symm
          have hΔd : (A₀ : ℚ) - (B' : ℚ) = (u : ℚ) * (d : ℚ) := by
            have h4 : ((Δ : ℕ) : ℚ) = (u : ℚ) * d := by exact_mod_cast hu.symm
            rw [← h4, hΔdef, Nat.cast_sub hBA.le]
          have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hdpos
          have h2 : (((A₀ : ℚ) - Bj) * ℓ) * d ≤ ((u : ℚ) * j) * d := by
            calc (((A₀ : ℚ) - Bj) * ℓ) * d = ((A₀ : ℚ) - Bj) * ((ℓ : ℚ) * d) := by ring
              _ = ((A₀ : ℚ) - Bj) * y' := by rw [hyd]
              _ ≤ ((A₀ : ℚ) - (B' : ℚ)) * j := hmax
              _ = ((u : ℚ) * d) * j := by rw [hΔd]
              _ = ((u : ℚ) * j) * d := by ring
          have h3 := le_of_mul_le_mul_right h2 hdQ
          linarith
        exact_mod_cast hgoalQ
  have hsupp : dvSupp F g u ℓ = ((ℓ * A₀ : ℕ) : ℕ∞) := le_antisymm hsupple hsuppge
  -- both endpoints of the secant sit on the side
  have hmem0 : 0 ∈ dvSideSet F g u ℓ := by
    apply C130nv2.mem_dvSideSet_of_dvOnSide
    refine ⟨?_, by rw [hA]; exact ENat.coe_ne_top A₀⟩
    rw [hsupp, term_coe ℓ u hA]
    norm_num
  have hmemy : y' ∈ dvSideSet F g u ℓ := by
    apply C130nv2.mem_dvSideSet_of_dvOnSide
    refine ⟨?_, hytop⟩
    rw [hsupp, term_coe ℓ u hBy, Nat.cast_inj]
    have huy : u * y' = ℓ * Δ := by
      calc u * y' = u * (ℓ * d) := by rw [hl]
        _ = ℓ * (u * d) := by ring
        _ = ℓ * Δ := by rw [hu]
    calc ℓ * A₀ = ℓ * (B' + Δ) := by rw [hΔ]
      _ = ℓ * B' + ℓ * Δ := by ring
      _ = ℓ * B' + u * y' := by rw [huy]
  -- positive side degree
  have hne : (dvSideSet F g u ℓ).Nonempty := ⟨0, hmem0⟩
  refine ⟨u, ℓ, hlpos, hcop, hfloor, hne, ?_⟩
  refine Nat.pos_of_ne_zero fun hz => ?_
  have hlen := dvSideLen_eq F hlpos hcop hne
  rw [dvSideLen, hz, Nat.mul_zero] at hlen
  have hymax' : y' ≤ dvSideMax F g u ℓ hne := Finset.le_max' _ _ hmemy
  have hminle : dvSideMin F g u ℓ hne ≤ 0 := Finset.min'_le _ _ hmem0
  omega

/-! ## §3 — the last side of a strictly recentred polynomial -/

/-- **The last-side lemma.**  A strictly recentred monic `f` not divisible by the key has
an above-floor coprime direction whose side reaches the full top index `deg f / (e₁f₁)`. -/
theorem exists_lastSide_direction {F : KeyFrame O π} {f : Polynomial O}
    (hf : f.Monic) (hkey : ¬ F.key ∣ f) (hrec : StrictlyRecentredAboveFloor F f)
    (hdeg : 0 < f.natDegree) :
    ∃ u₀ ℓ₀ : ℕ, 0 < ℓ₀ ∧ Nat.Coprime u₀ ℓ₀ ∧
      ℓ₀ * ((F.e₁ * F.f₁) * F.h) < u₀ ∧
      ∃ hne : (dvSideSet F f u₀ ℓ₀).Nonempty,
        dvSideMax F f u₀ ℓ₀ hne = f.natDegree / (F.e₁ * F.f₁) := by
  classical
  set E : ℕ := F.e₁ * F.f₁ with hEdef
  set H : ℕ := E * F.h with hHdef
  have hEpos : 0 < E := Nat.mul_pos F.he₁ F.hf₁
  obtain ⟨m, hm⟩ := hrec.1
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact h
  have hmdiv : f.natDegree / E = m := by
    rw [hm]; exact Nat.mul_div_cancel_left m hEpos
  -- the monic top digit has height zero
  have hdegkey : f.natDegree = m * F.key.natDegree := by
    rw [F.hdeg, ← hEdef, hm, Nat.mul_comm]
  have htop : dvHgt F f m = 0 := by
    rw [dvHgt, dev_top_eq_one F.hmonic F.natDegree_key_pos hf hmpos hdegkey]
    exact C131ae.stageHeight_one F
  have htop' : dvHgt F f m = ((0 : ℕ) : ℕ∞) := by rw [htop]; simp
  -- support strictly left of the top index
  set S : Finset ℕ := (Finset.range m).filter (fun x => dvHgt F f x ≠ ⊤) with hSdef
  have hS0 : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0top : dvHgt F f 0 = ⊤ := by
      by_contra hne
      have h0S : (0 : ℕ) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmpos, hne⟩
      rw [hemp] at h0S
      exact absurd h0S (by simp)
    exact hkey (key_dvd_of_dvHgt_zero_eq_top h0top)
  -- minimize the height-to-top ratio
  set ρ : ℕ → ℚ := fun x => ((dvHgt F f x).toNat : ℚ) / ((m : ℚ) - (x : ℚ)) with hρdef
  obtain ⟨x', hxS, hxmin⟩ := S.exists_min_image ρ hS0
  have hxm : x' < m := Finset.mem_range.mp (Finset.mem_filter.mp hxS).1
  have hxtop : dvHgt F f x' ≠ ⊤ := (Finset.mem_filter.mp hxS).2
  obtain ⟨A', hAx'⟩ := ENat.ne_top_iff_exists.mp hxtop
  have hAx : dvHgt F f x' = (A' : ℕ∞) := hAx'.symm
  -- strict recentring at the minimizer
  have hrecx := hrec.2 x' (by rw [hmdiv]; exact hxm)
  rw [hmdiv, hAx] at hrecx
  have hrecN : H * (m - x') < A' := by exact_mod_cast hrecx
  -- reduce the last-side fraction to lowest terms
  set d : ℕ := Nat.gcd A' (m - x') with hddef
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right A' (by omega)
  set u₀ : ℕ := A' / d with hudef
  set ℓ₀ : ℕ := (m - x') / d with hldef
  have hu : u₀ * d = A' := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hl : ℓ₀ * d = m - x' := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime u₀ ℓ₀ := Nat.coprime_div_gcd_div_gcd hdpos
  have hlpos : 0 < ℓ₀ := by
    rcases Nat.eq_zero_or_pos ℓ₀ with h0 | h
    · rw [h0, Nat.zero_mul] at hl; omega
    · exact h
  have hfloor : ℓ₀ * H < u₀ := by
    have h1 : (ℓ₀ * H) * d < u₀ * d := by
      calc (ℓ₀ * H) * d = H * (ℓ₀ * d) := by ring
        _ = H * (m - x') := by rw [hl]
        _ < A' := hrecN
        _ = u₀ * d := hu.symm
    exact Nat.lt_of_mul_lt_mul_right h1
  have hupos : 0 < u₀ := by omega
  -- the cleared support at the last-side direction
  have hmle : m ≤ f.natDegree := by
    calc m = 1 * m := (Nat.one_mul m).symm
      _ ≤ E * m := Nat.mul_le_mul_right m hEpos
      _ = f.natDegree := hm.symm
  have hsupple : dvSupp F f u₀ ℓ₀ ≤ ((ℓ₀ * 0 + u₀ * m : ℕ) : ℕ∞) := by
    have h1 := C131y.dvSupp_le_term F f u₀ hlpos m
    rwa [term_coe ℓ₀ u₀ htop'] at h1
  have hsuppge : ((ℓ₀ * 0 + u₀ * m : ℕ) : ℕ∞) ≤ dvSupp F f u₀ ℓ₀ := by
    unfold dvSupp
    refine Finset.le_inf fun j hj => ?_
    by_cases htopj : dvHgt F f j = ⊤
    · rw [htopj, nsmul_top_of_pos hlpos, top_add]
      exact le_top
    · obtain ⟨Aj, hAj⟩ := ENat.ne_top_iff_exists.mp htopj
      rw [term_coe ℓ₀ u₀ hAj.symm, Nat.cast_le]
      rcases lt_trichotomy j m with hjm | hjm | hjm
      · -- j < m : the minimizer beats the ratio at j
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, htopj⟩
        have hmin := hxmin j hjS
        have hρx : ρ x' = ((A' : ℚ)) / ((m : ℚ) - (x' : ℚ)) := by
          simp only [hρdef, toNat_of_eq_coe hAx]
        have hρj : ρ j = ((Aj : ℚ)) / ((m : ℚ) - (j : ℚ)) := by
          simp only [hρdef, toNat_of_eq_coe hAj.symm]
        have hdx : (0 : ℚ) < (m : ℚ) - (x' : ℚ) := by
          have hq : (x' : ℚ) < (m : ℚ) := by exact_mod_cast hxm
          linarith
        have hdj : (0 : ℚ) < (m : ℚ) - (j : ℚ) := by
          have hq : (j : ℚ) < (m : ℚ) := by exact_mod_cast hjm
          linarith
        rw [hρx, hρj, div_le_div_iff₀ hdx hdj] at hmin
        -- hmin : A' * ((m:ℚ) - j) ≤ Aj * ((m:ℚ) - x')
        have hgoalQ : (u₀ : ℚ) * m ≤ (ℓ₀ : ℚ) * Aj + (u₀ : ℚ) * j := by
          have hAd : (A' : ℚ) = (u₀ : ℚ) * (d : ℚ) := by exact_mod_cast hu.symm
          have hLd : ((m : ℚ) - (x' : ℚ)) = (ℓ₀ : ℚ) * (d : ℚ) := by
            rw [show (m : ℚ) - (x' : ℚ) = ((m - x' : ℕ) : ℚ) from (Nat.cast_sub hxm.le).symm]
            exact_mod_cast hl.symm
          have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hdpos
          have h2 : ((u₀ : ℚ) * ((m : ℚ) - j)) * d ≤ ((Aj : ℚ) * ℓ₀) * d := by
            calc ((u₀ : ℚ) * ((m : ℚ) - j)) * d = ((u₀ : ℚ) * d) * ((m : ℚ) - j) := by ring
              _ = (A' : ℚ) * ((m : ℚ) - j) := by rw [hAd]
              _ ≤ (Aj : ℚ) * ((m : ℚ) - (x' : ℚ)) := hmin
              _ = (Aj : ℚ) * ((ℓ₀ : ℚ) * d) := by rw [hLd]
              _ = ((Aj : ℚ) * ℓ₀) * d := by ring
          have h3 := le_of_mul_le_mul_right h2 hdQ
          linarith
        have hcast : ((u₀ * m : ℕ) : ℚ) ≤ ((ℓ₀ * Aj + u₀ * j : ℕ) : ℚ) := by
          push_cast; linarith
        have := (Nat.cast_le (α := ℚ)).mp hcast
        omega
      · -- j = m : the endpoint term
        subst hjm
        have hAj0 : Aj = 0 := by
          have h2 : (Aj : ℕ∞) = ((0 : ℕ) : ℕ∞) := by rw [hAj, htop']
          exact_mod_cast h2
        rw [hAj0]
      · -- j > m : the linear part alone dominates
        have h2 : u₀ * m ≤ u₀ * j := Nat.mul_le_mul_left u₀ hjm.le
        omega
  have hsupp : dvSupp F f u₀ ℓ₀ = ((ℓ₀ * 0 + u₀ * m : ℕ) : ℕ∞) :=
    le_antisymm hsupple hsuppge
  -- the top index sits on the side
  have hmemm : m ∈ dvSideSet F f u₀ ℓ₀ := by
    apply C130nv2.mem_dvSideSet_of_dvOnSide
    refine ⟨?_, by rw [htop']; exact ENat.coe_ne_top 0⟩
    rw [hsupp, term_coe ℓ₀ u₀ htop']
  refine ⟨u₀, ℓ₀, hlpos, hcop, hfloor, ⟨m, hmemm⟩, ?_⟩
  rw [hmdiv]
  apply le_antisymm
  · apply Finset.max'_le
    intro j hjmem
    obtain ⟨heq, hfin⟩ := dvOnSide_of_mem_dvSideSet hjmem
    obtain ⟨Aj, hAj⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [hsupp, term_coe ℓ₀ u₀ hAj.symm] at heq
    have hN : ℓ₀ * 0 + u₀ * m = ℓ₀ * Aj + u₀ * j := by exact_mod_cast heq
    exact Nat.le_of_mul_le_mul_left (by omega) hupos
  · exact Finset.le_max' _ _ hmemm

/-! ## §4 — `dvSideMax` additivity, unfenced in the frame height -/

/-- **`dvSideMax` additivity at every frame.**  Theorem M's clause at `0 < F.h`
(`C133mh3.dvSideMax_mul`); the degenerate `F.h = 0` leg through the C133h0leg dictionary
and B.43's order-1 product laws. -/
theorem dvSideMax_mul_all (hπ : Irreducible π) {F : KeyFrame O π}
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMax F (g * z) u ℓ hngz = dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz := by
  rcases Nat.eq_zero_or_pos F.h with hh0 | hh
  · -- the degenerate frame: through the C133h0leg dictionary into the order-1 laws
    have hu : 0 < u := by
      have h0 : ℓ * ((F.e₁ * F.f₁) * F.h) = 0 := by rw [hh0]; ring
      omega
    have hik : IsKey F.key := C133h0leg.isKey_key F hh0
    have hkeypos : 0 < F.key.natDegree := F.natDegree_key_pos
    have htg : suppVal F.key g u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero F.hmonic hkeypos hg
    have htz : suppVal F.key z u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero F.hmonic hkeypos hz
    have htgz : suppVal F.key (g * z) u ℓ ≠ ⊤ :=
      suppVal_ne_top_of_ne_zero F.hmonic hkeypos (mul_ne_zero hg hz)
    have hSg := C133h0leg.dvSideSet_eq_sideSet F hh0 hℓ htg
    have hSz := C133h0leg.dvSideSet_eq_sideSet F hh0 hℓ htz
    have hSgz := C133h0leg.dvSideSet_eq_sideSet F hh0 hℓ htgz
    have hngB : (sideSet F.key g u ℓ).Nonempty := hSg ▸ hng
    have hnzB : (sideSet F.key z u ℓ).Nonempty := hSz ▸ hnz
    have hngzB : (sideSet F.key (g * z) u ℓ).Nonempty := hSgz ▸ hngz
    obtain ⟨Hg, hHg⟩ := exists_sideMin_height hℓ htg hngB
    obtain ⟨Hz, hHz⟩ := exists_sideMin_height hℓ htz hnzB
    have hminB := sideMin_mul_gen' hπ hik hu hℓ hcop rfl htg htz hngB hnzB hHg hHz hngzB
    have hdegB := sideDeg_mul_gen' hπ hik hu hℓ hcop rfl htg htz hngB hnzB hHg hHz hngzB
    have e1 : dvSideMin F (g * z) u ℓ hngz
        = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz := by
      rw [C133h0leg.dvSideMin_eq_sideMin F hh0 hℓ htgz hngz hngzB,
        C133h0leg.dvSideMin_eq_sideMin F hh0 hℓ htg hng hngB,
        C133h0leg.dvSideMin_eq_sideMin F hh0 hℓ htz hnz hnzB]
      exact hminB
    have e2 : dvSideDeg F (g * z) u ℓ hngz
        = dvSideDeg F g u ℓ hng + dvSideDeg F z u ℓ hnz := by
      rw [C133h0leg.dvSideDeg_eq_sideDeg F hh0 hℓ htgz hngz hngzB,
        C133h0leg.dvSideDeg_eq_sideDeg F hh0 hℓ htg hng hngB,
        C133h0leg.dvSideDeg_eq_sideDeg F hh0 hℓ htz hnz hnzB]
      exact hdegB
    have L1 := dvSideLen_eq F hℓ hcop hngz
    have L2 := dvSideLen_eq F hℓ hcop hng
    have L3 := dvSideLen_eq F hℓ hcop hnz
    rw [dvSideLen] at L1 L2 L3
    have m1 : dvSideMin F (g * z) u ℓ hngz ≤ dvSideMax F (g * z) u ℓ hngz :=
      Finset.min'_le _ _ (Finset.max'_mem _ hngz)
    have m2 : dvSideMin F g u ℓ hng ≤ dvSideMax F g u ℓ hng :=
      Finset.min'_le _ _ (Finset.max'_mem _ hng)
    have m3 : dvSideMin F z u ℓ hnz ≤ dvSideMax F z u ℓ hnz :=
      Finset.min'_le _ _ (Finset.max'_mem _ hnz)
    have hdist : ℓ * dvSideDeg F (g * z) u ℓ hngz
        = ℓ * dvSideDeg F g u ℓ hng + ℓ * dvSideDeg F z u ℓ hnz := by
      rw [e2, Nat.mul_add]
    omega
  · exact C133mh3.dvSideMax_mul hπ hh H₀ hpin hℓ hcop hfloor hg hz hng hnz hngz

/-! ## §5 — the bridge -/

/-- **The residual bridge, core form.**  Every positive-degree monic factor of a strictly
recentred monic `f` (with `¬ F.key ∣ f`) has a genuine above-floor side. -/
theorem monicFactorsHaveAboveFloorSide_of_strictlyRecentred (hπ : Irreducible π)
    {F : KeyFrame O π} {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (hrec : StrictlyRecentredAboveFloor F f) :
    MonicFactorsHaveAboveFloorSide F f := by
  intro g w hg hw hprod hgpos
  subst hprod
  have hEpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  -- key escape: the zeroth digit of `g` is nonzero
  have hg0 : dvHgt F g 0 ≠ ⊤ := by
    intro htop
    exact hkey ((key_dvd_of_dvHgt_zero_eq_top htop).trans ⟨w, rfl⟩)
  obtain ⟨A₀, hA₀⟩ := ENat.ne_top_iff_exists.mp hg0
  -- degrees
  have hdegmul : (g * w).natDegree = g.natDegree + w.natDegree :=
    Polynomial.natDegree_mul hg.ne_zero hw.ne_zero
  have hdegpos : 0 < (g * w).natDegree := by omega
  -- the last side of the recentred product
  obtain ⟨u₀, ℓ₀, hℓ₀, hcop₀, hfloor₀, hneF, hmaxF⟩ :=
    exists_lastSide_direction hf hkey hrec hdegpos
  -- additivity of the side maximum at that direction
  obtain ⟨H₀, hpin⟩ := exists_pin F
  have hng : (dvSideSet F g u₀ ℓ₀).Nonempty := dvSideSet_nonempty F hg.ne_zero u₀ hℓ₀
  have hnw : (dvSideSet F w u₀ ℓ₀).Nonempty := dvSideSet_nonempty F hw.ne_zero u₀ hℓ₀
  have hadd := dvSideMax_mul_all hπ H₀ hpin hℓ₀ hcop₀ hfloor₀ hg.ne_zero hw.ne_zero
    hng hnw hneF
  -- the cofactor's cap is one short of the full top index
  obtain ⟨k, hk⟩ := hrec.1
  have hkdiv : (g * w).natDegree / (F.e₁ * F.f₁) = k := by
    rw [hk]; exact Nat.mul_div_cancel_left k hEpos
  have hwcap : dvSideMax F w u₀ ℓ₀ hnw ≤ w.natDegree / (F.e₁ * F.f₁) :=
    le_natDegree_div_of_mem_dvSideSet F (Finset.max'_mem _ hnw)
  have hwlt : w.natDegree / (F.e₁ * F.f₁) < k := by
    have hlt : w.natDegree < (F.e₁ * F.f₁) * k := by omega
    rw [Nat.div_lt_iff_lt_mul hEpos, Nat.mul_comm k (F.e₁ * F.f₁)]
    exact hlt
  have hb1 : 1 ≤ dvSideMax F g u₀ ℓ₀ hng := by
    rw [hkdiv] at hmaxF
    omega
  -- the on-side equation at `g`'s side maximum, against the index-0 term
  set b : ℕ := dvSideMax F g u₀ ℓ₀ hng with hbdef
  obtain ⟨hbeq, hbfin⟩ := dvOnSide_of_mem_dvSideSet (Finset.max'_mem _ hng)
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp hbfin
  have hNle : ℓ₀ * B + u₀ * b ≤ ℓ₀ * A₀ + u₀ * 0 := by
    have hle0 := C131y.dvSupp_le_term F g u₀ hℓ₀ 0
    rw [term_coe ℓ₀ u₀ hA₀.symm, hbeq, term_coe ℓ₀ u₀ hB.symm] at hle0
    exact_mod_cast hle0
  have hdrop : B + (F.e₁ * F.f₁) * F.h * b < A₀ := by
    have h2 : ℓ₀ * ((F.e₁ * F.f₁) * F.h * b) < u₀ * b := by
      have hb0 : 0 < b := hb1
      calc ℓ₀ * ((F.e₁ * F.f₁) * F.h * b) = (ℓ₀ * ((F.e₁ * F.f₁) * F.h)) * b := by ring
        _ < u₀ * b := mul_lt_mul_of_pos_right hfloor₀ hb0
    have h3 : ℓ₀ * (B + (F.e₁ * F.f₁) * F.h * b) < ℓ₀ * A₀ := by
      calc ℓ₀ * (B + (F.e₁ * F.f₁) * F.h * b)
          = ℓ₀ * B + ℓ₀ * ((F.e₁ * F.f₁) * F.h * b) := by ring
        _ < ℓ₀ * B + u₀ * b := by omega
        _ ≤ ℓ₀ * A₀ := by omega
    exact Nat.lt_of_mul_lt_mul_left h3
  exact hasGenuineAboveFloorSide_of_secant hb1 hA₀.symm hB.symm hdrop

/-- ★ **THE RESIDUAL BRIDGE** — `IFCG11.StrictRecentredFactorSideStatement` holds. -/
theorem strictRecentredFactorSide : StrictRecentredFactorSideStatement := by
  intro O _ _ _ _ π hπ F f hf hkey hrec
  exact monicFactorsHaveAboveFloorSide_of_strictlyRecentred hπ hf hkey hrec

/-! ## §6 — the kernel and THE COVER, fired -/

/-- ★★ **THE EXHAUSTION KERNEL** — IFCG9's
`RecentredClusterDegreeExhaustionStatement` holds: strict recentring forces every C.33
dissection to spend the whole degree above the floor. -/
theorem recentredClusterDegreeExhaustion : RecentredClusterDegreeExhaustionStatement :=
  recentredClusterDegreeExhaustion_of_factorSide strictRecentredFactorSide

/-- ★★★ **THE STRONG FINITE GENRE COVER** (the campaign's stop line, unconditional):
EXHAUSTIVE ∧ DISJOINT ∧ DECREASING over the strong carrier. -/
theorem finiteGenreCoverAt_strong_all :
    StrongCoverExhaustive ∧ StrongCoverDisjoint ∧ ∀ m : ℕ, DecreasingGenreBankAt m :=
  finiteGenreCoverAt_strong_of_factorSide strictRecentredFactorSide

/-- The exhaustive clause alone, unconditional. -/
theorem strongCoverExhaustive_all : StrongCoverExhaustive :=
  finiteGenreCoverAt_strong_all.1

set_option maxRecDepth 4000 in
/-- **The cubic count, kernel-checked**: the official residue-pattern count at total `3`
is `5` — IFC6's five cubic types.  (The quartic analogue `rpCount 4 = 11` is recorded by
IFCG0's `#eval` regression; kernel `decide` on the `Sym`-grid count is intractable at
`n = 4`, exactly as IFCG0's comment predicts, so it is NOT declared here.) -/
theorem rpCount_cubic : IFCG0.rpCount 3 = 5 := by decide

/-- **Cubic count recovery (mass 3).**  Every recentred monic above-floor context of mass
`3` strong-realizes a member of the precomputed mass-`3` bank — the bank whose residue
patterns are IFC6's five cubic types (`rpCount_cubic` above). -/
theorem strongCover_cubic
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (π : O) (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) (f : Polynomial O)
    (hf : f.Monic) (hkey : ¬ F.key ∣ f) (hrec : StrictlyRecentredAboveFloor F f)
    (hm : f.natDegree = (F.e₁ * F.f₁) * 3) :
    ∃ (S : ClusterSkeleton 3) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      S ∈ genreSkeletonFinset 3 ∧ StrongRealizesSkeletonAt F H₀ hpin S num blocks :=
  strongCoverExhaustive_all O π hπ F hh H₀ hpin f hf hkey hrec 3 hm

/-- **Quartic count recovery (mass 4).**  Every recentred monic above-floor context of
mass `4` strong-realizes a member of the precomputed mass-`4` bank — the bank whose
residue patterns are blueprint §8's eleven quartic rows (`rpCount 4 = 11`, the recorded
IFCG0 `#eval` regression; see `rpCount_cubic`'s docstring for why the quartic count
equality is not kernel-decided). -/
theorem strongCover_quartic
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (π : O) (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) (f : Polynomial O)
    (hf : f.Monic) (hkey : ¬ F.key ∣ f) (hrec : StrictlyRecentredAboveFloor F f)
    (hm : f.natDegree = (F.e₁ * F.f₁) * 4) :
    ∃ (S : ClusterSkeleton 4) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      S ∈ genreSkeletonFinset 4 ∧ StrongRealizesSkeletonAt F H₀ hpin S num blocks :=
  strongCoverExhaustive_all O π hπ F hh H₀ hpin f hf hkey hrec 4 hm

end Uniformity.Density.IFCG12

end

/-! ## AXCHECK FOOTER -/

#print axioms Uniformity.Density.IFCG12.hasGenuineAboveFloorSide_of_secant
#print axioms Uniformity.Density.IFCG12.exists_lastSide_direction
#print axioms Uniformity.Density.IFCG12.dvSideMax_mul_all
#print axioms Uniformity.Density.IFCG12.strictRecentredFactorSide
#print axioms Uniformity.Density.IFCG12.recentredClusterDegreeExhaustion
#print axioms Uniformity.Density.IFCG12.finiteGenreCoverAt_strong_all
#print axioms Uniformity.Density.IFCG12.rpCount_cubic
#print axioms Uniformity.Density.IFCG12.strongCover_cubic
#print axioms Uniformity.Density.IFCG12.strongCover_quartic
