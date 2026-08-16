/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115
import Uniformity.ChapH.H117
import Uniformity.ChapB.B59a

/-!
# Uniformity.ChapH.H115b — the α shear is ONTO (H.115 clause ii)

**Chapter H, NODE H.115, SPLIT b** (`blueprint/CHAP-H_general_induction.md` §17.2, the
blueprint's mandated split H.115a/H.115b/H.115c).

`alphaChild_surjective` — at a realized slope `k` and a nonzero residue `z`, every
window-`(N − m k)` cluster state is the α child of some α(k, z) state.

## The construction, in one line

Reverse the shear.  Given a child lift `b` (degree `m`, coefficients in `𝔪`) and the pinned
centre `ŵ = resSect O z`, put

* `alphaFrame b ŵ = (monicPoly b).comp (X − C ŵ)` — undo the recentring;
* `alphaParent π b k ŵ = (alphaFrame b ŵ).scaleRoots (π ^ k)` — undo the scaling.

Then `alphaParent`'s recentring is EXACTLY `C (π ^ (m k)) * monicPoly b`
(`alphaParent_recentre`), which is clause (i)'s conclusion read backwards, and the parent's
coefficients are `(alphaFrame b ŵ).coeff j · π ^ (k (m − j))` — all in `𝔪`, so the parent is a
cluster state.

## The four obligations of `IsAlphaState`, and where each is discharged

1. **non-drain** — `alphaParent_addVal_coeff_zero`: the constant coefficient has valuation
   EXACTLY `m k ≤ N − 1`, because `(alphaFrame b ŵ).coeff 0 = (monicPoly b).eval (−ŵ)` reduces
   to `(−z) ^ m ≠ 0` (here `z ≠ 0` is load-bearing, and only here and in the polygon step).
2. **the content** — `betaContent c k = m * k`, by H.108's infimum: every visible term
   `resOrd (c j) + j k` already dominates the monic top term `m k`.
3. **the child event** — `HasChildAt π c m k z` through H.109's conservativity
   `hasChildAt_of_exists`, read at the constructed lift pair, where the recentring is the
   explicit product above.
4. **not CS** — `not_isCSState_of_alphaParent`.  This is the only geometric step.  The
   parent's polygon is the SINGLE side from `(0, m k)` to `(m, 0)`: at `(u, ℓ)` with
   `u ≠ k ℓ` the supporting line touches one endpoint only, so `sideDeg = 0` and the residual
   polynomial is a nonzero constant, which no `ψ ^ μ` divides; at `(u, ℓ) = (k, 1)` (forced by
   `Nat.Coprime u ℓ`) B.59a's digit identity `resPoly_X_eq_map_of_scaleRoots` computes the
   residual polynomial as the reduction of `alphaFrame b ŵ`, namely `(Y − z) ^ m`, whose
   irreducible factors are all of degree `1` — and `IsCSState` demands a block
   `2 ≤ ℓ * deg ψ = deg ψ`.

Clause (i) (`alphaChild_spec`, in `ChapH/H115.lean`) then identifies the child of the
constructed parent with `d`: two monic developments equal after multiplication by the nonzero
`π ^ (m k)` are equal.

Steps 3–8 are packaged as `exists_isAlphaState_of_alphaParent` (§4) — *any* state carried by a
coefficient vector whose monic development is `alphaParent π b k (resSect O z)` is an α(k, z)
state with child the class of `b` — because H.115c's fibre count parametrizes the fibre by the
same inverse shear and must read it off the SAME lemma, not a copy.

DEPENDS: H.115a (`resSect`, `alphaChild`, `alphaChild_spec`), H.117 (`sideMax_le_natDegree`),
H.112 (`exists_proj_eq`, `coeff_recentre_top`), H.111 (`IsAlphaState`), H.110 (`IsCSState`),
H.109 (`HasChildAt`, `hasChildAt_of_exists`), H.108 (`betaContent`), H.107 (`resOrd`) ·
CHAP-B B.15 (`npHgt_X`), B.16 (`sideSet`), B.20 (`sideMin`/`sideMax`/`sideDeg`), B.29
(`resPoly`), B.30 (`natDegree_resPoly`), B.34 (`IsPure`), B.59a
(`resPoly_X_eq_map_of_scaleRoots`) · mathlib `Polynomial.scaleRoots`,
`Polynomial.comp_C_mul_X_coeff`, `Prime.dvd_of_dvd_pow`.

**ENVIRONMENT — ENV-H17** + `π` explicit, every binder INLINE.  No `[Finite]` (clause (ii)
does not count).

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

section Parent

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## 1. The inverse shear: from a child lift to a parent frame -/

/-- **The un-scaled parent frame.**  Undo the recentring `y ↦ y + ŵ` of the child
development. -/
noncomputable def alphaFrame {m : ℕ} (b : Fin m → O) (ŵ : O) : Polynomial O :=
  (monicPoly b).comp (X - C ŵ)

theorem alphaFrame_monic {m : ℕ} (b : Fin m → O) (ŵ : O) : (alphaFrame b ŵ).Monic :=
  (monicPoly_monic b).comp (monic_X_sub_C ŵ) (by simp)

theorem alphaFrame_natDegree {m : ℕ} (b : Fin m → O) (ŵ : O) :
    (alphaFrame b ŵ).natDegree = m := by
  rw [alphaFrame, natDegree_comp, monicPoly_natDegree, natDegree_X_sub_C, mul_one]

/-- **The parent frame.**  Undo the scaling `y ↦ π ^ k y` as well: `scaleRoots` multiplies the
`j`-th coefficient by `(π ^ k) ^ (m − j)`, which is precisely the α digit pattern. -/
noncomputable def alphaParent (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) : Polynomial O :=
  (alphaFrame b ŵ).scaleRoots (π ^ k)

theorem alphaParent_monic (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).Monic :=
  (monic_scaleRoots_iff _).2 (alphaFrame_monic b ŵ)

theorem alphaParent_natDegree (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).natDegree = m := by
  rw [alphaParent, natDegree_scaleRoots, alphaFrame_natDegree]

theorem alphaParent_coeff (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) (j : ℕ) :
    (alphaParent π b k ŵ).coeff j = (alphaFrame b ŵ).coeff j * (π ^ k) ^ (m - j) := by
  rw [alphaParent, coeff_scaleRoots, alphaFrame_natDegree]

/-- **The inverse shear is a shear.**  The parent frame's recentring at the pinned pair is
exactly `π ^ (m k) ·` the child's monic development — clause (i)'s conclusion, backwards. -/
theorem alphaParent_recentre (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).comp (C (π ^ k) * (X + C ŵ)) = C (π ^ (m * k)) * monicPoly b := by
  have hstep : (alphaParent π b k ŵ).comp (C (π ^ k) * X)
      = C ((π ^ k) ^ m) * alphaFrame b ŵ := by
    refine Polynomial.ext fun j => ?_
    rw [comp_C_mul_X_coeff, alphaParent_coeff, coeff_C_mul]
    by_cases hj : j ≤ m
    · rw [mul_assoc, ← pow_add, show m - j + j = m from by omega]
      ring
    · have hz : (alphaFrame b ŵ).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [alphaFrame_natDegree]; omega)
      rw [hz, zero_mul, zero_mul, mul_zero]
  have hq : (C (π ^ k) * X).comp (X + C ŵ) = C (π ^ k) * (X + C ŵ) := by
    simp [mul_comp]
  have hinner : (alphaFrame b ŵ).comp (X + C ŵ) = monicPoly b := by
    rw [alphaFrame, Polynomial.comp_assoc]
    have : (X - C ŵ).comp (X + C ŵ) = (X : Polynomial O) := by
      simp [sub_comp]
    rw [this, comp_X]
  calc (alphaParent π b k ŵ).comp (C (π ^ k) * (X + C ŵ))
      = ((alphaParent π b k ŵ).comp (C (π ^ k) * X)).comp (X + C ŵ) := by
        rw [Polynomial.comp_assoc, hq]
    _ = (C ((π ^ k) ^ m) * alphaFrame b ŵ).comp (X + C ŵ) := by rw [hstep]
    _ = C (π ^ (m * k)) * monicPoly b := by
        rw [mul_comp, C_comp, hinner, ← pow_mul, Nat.mul_comm k m]

/-! ## 2. The parent's reduction and its valuation profile -/

/-- **The reduction of the parent frame.**  With every child coordinate in `𝔪` the child's
development reduces to `Y ^ m`, so the un-scaled parent frame reduces to `(Y − z) ^ m` — the
α residual polynomial, before any polygon apparatus is invoked. -/
theorem alphaFrame_map_residue {m : ℕ} {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O)
    (ŵ : O) :
    (alphaFrame b ŵ).map (residue O) = (X - C (residue O ŵ)) ^ m := by
  have hmb : (monicPoly b).map (residue O) = (X : Polynomial (ResidueField O)) ^ m := by
    rw [monicPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum]
    have hz : ∀ i : Fin m, (C (b i) * X ^ (i : ℕ)).map (residue O) = 0 := by
      intro i
      have : residue O (b i) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hb i)
      rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, this, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero, add_zero]
  rw [alphaFrame, Polynomial.map_comp, hmb, Polynomial.map_sub, map_X, map_C, pow_comp, X_comp]

/-- **The parent frame's constant coefficient is a UNIT** — this is where `z ≠ 0` enters.  Its
reduction is `(−z) ^ m`. -/
theorem alphaFrame_coeff_zero_not_dvd {π : O} (hπ : Irreducible π) {m : ℕ}
    {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0)
    {ŵ : O} (hŵ : residue O ŵ = z) : ¬ π ∣ (alphaFrame b ŵ).coeff 0 := by
  intro hdvd
  have hmem : (alphaFrame b ŵ).coeff 0 ∈ maximalIdeal O := by
    have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 ((alphaFrame b ŵ).coeff 0)).2
      (by rwa [pow_one])
    rwa [pow_one] at this
  have h0 : residue O ((alphaFrame b ŵ).coeff 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hmap : residue O ((alphaFrame b ŵ).coeff 0) = (-z) ^ m := by
    rw [← coeff_map, alphaFrame_map_residue hb ŵ, hŵ, coeff_zero_eq_eval_zero]
    simp
  rw [hmap] at h0
  exact hz (neg_eq_zero.1 (pow_eq_zero_iff' .. |>.1 h0).1)

/-- The parent's polygon point at abscissa `j` sits on or above the line of slope `−k` through
`(m, 0)`. -/
theorem alphaParent_npHgt_ge {π : O} (hπ : Irreducible π) {m : ℕ} (b : Fin m → O) (k : ℕ)
    (ŵ : O) (j : ℕ) :
    (((m - j) * k : ℕ) : ℕ∞) ≤ npHgt X (alphaParent π b k ŵ) j := by
  rw [npHgt_X, ← Uniformity.Hensel.pow_dvd_iff_le_addVal hπ, alphaParent_coeff]
  exact Dvd.dvd.mul_left (dvd_of_eq (by rw [← pow_mul, Nat.mul_comm k (m - j)])) _

/-- The parent's polygon point at abscissa `0` is EXACTLY `(0, m k)`. -/
theorem alphaParent_npHgt_zero {π : O} (hπ : Irreducible π) {m : ℕ} {b : Fin m → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0) (k : ℕ) {ŵ : O}
    (hŵ : residue O ŵ = z) :
    npHgt X (alphaParent π b k ŵ) 0 = ((m * k : ℕ) : ℕ∞) := by
  have hco : (alphaParent π b k ŵ).coeff 0 = (alphaFrame b ŵ).coeff 0 * π ^ (m * k) := by
    rw [alphaParent_coeff, Nat.sub_zero, ← pow_mul, Nat.mul_comm k m]
  have hunit : IsDiscreteValuationRing.addVal O ((alphaFrame b ŵ).coeff 0) = 0 := by
    by_contra hne
    refine alphaFrame_coeff_zero_not_dvd hπ hb hz hŵ ?_
    have h1 : ((1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal O ((alphaFrame b ŵ).coeff 0) := by
      exact_mod_cast Order.one_le_iff_ne_zero.2 hne
    have h2 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ
      (a := (alphaFrame b ŵ).coeff 0) (n := 1)).2 h1
    rwa [pow_one] at h2
  rw [npHgt_X, hco, AddValuation.map_mul, hunit, zero_add, hπ.addVal_pow]

/-- The parent's polygon point at abscissa `m` is EXACTLY `(m, 0)` — the monic top. -/
theorem alphaParent_npHgt_natDegree (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    npHgt X (alphaParent π b k ŵ) m = 0 := by
  have h1 : (alphaParent π b k ŵ).coeff m = 1 := by
    have := (alphaParent_monic π b k ŵ).coeff_natDegree
    rwa [alphaParent_natDegree] at this
  rw [npHgt_X, h1, AddValuation.map_one]

/-! ## 3. The parent state is not a CS state -/

/-- `X` is an order-1 key.  `private` in C.12/C.19/H.117 and `private` does not export, so it is
re-derived here (three lines, same proof). -/
private theorem isKeyX {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

private theorem enat_smul_nat (ℓ t : ℕ) : ℓ • ((t : ℕ) : ℕ∞) = ((ℓ * t : ℕ) : ℕ∞) := by
  simp [nsmul_eq_mul]

private theorem enat_smul_mono {ℓ : ℕ} {x y : ℕ∞} (h : x ≤ y) : ℓ • x ≤ ℓ • y := by
  simp only [nsmul_eq_mul]
  gcongr

/-- **The one geometric step.**  A cluster state carried by a parent frame is never CS: its
polygon is the single side from `(0, m k)` to `(m, 0)`, whose only repeated residual factor is
the LINEAR `Y − z`, and `IsCSState` demands a block of size `ℓ · deg ψ ≥ 2`. -/
theorem not_isCSState_of_alphaParent {π : O} (hπ : Irreducible π) {m N k : ℕ}
    {z : ResidueField O} (hk : 1 ≤ k) (hz : z ≠ 0)
    {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O) {ŵ : O} (hŵ : residue O ŵ = z)
    {c : ClusterState O m N} {a : Fin m → O} (ha : proj O m N a = c.1)
    (hfa : monicPoly a = alphaParent π b k ŵ) : ¬ IsCSState π c := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKeyX
  intro hCS
  obtain ⟨u, ℓ, hne, H₀, hℓ, hcop, hpin, ψ, hψ, hblock, hdvd⟩ := hCS.2 a ha
  -- the polygon profile of the lift, transported through `hfa`
  have hdeg : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have hnp0 : npHgt X (monicPoly a) 0 = ((m * k : ℕ) : ℕ∞) := by
    rw [hfa]; exact alphaParent_npHgt_zero hπ hb hz k hŵ
  have hnpge : ∀ j, (((m - j) * k : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) j := by
    intro j; rw [hfa]; exact alphaParent_npHgt_ge hπ b k ŵ j
  have hnpm : npHgt X (monicPoly a) m = 0 := by
    rw [hfa]; exact alphaParent_npHgt_natDegree π b k ŵ
  have hrange : ∀ j ∈ sideSet X (monicPoly a) u ℓ, j ≤ m := by
    intro j hj
    have hj' : j ∈ Finset.filter (OnSide X (monicPoly a) u ℓ)
      (Finset.range ((monicPoly a).natDegree + 1)) := hj
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj').1
    omega
  have hmem0 : (0 : ℕ) ∈ Finset.range ((monicPoly a).natDegree + 1) :=
    Finset.mem_range.2 (Nat.succ_pos _)
  have hmemm : m ∈ Finset.range ((monicPoly a).natDegree + 1) :=
    Finset.mem_range.2 (by omega)
  -- the cleared support value is finite (B.30's side condition)
  have htop : suppVal X (monicPoly a) u ℓ ≠ ⊤ := by
    have hle : suppVal X (monicPoly a) u ℓ
        ≤ ℓ • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞) := Finset.inf_le hmem0
    rw [hnp0, enat_smul_nat] at hle
    refine ne_top_of_le_ne_top ?_ hle
    rw [← Nat.cast_add]
    exact ENat.coe_ne_top _
  rcases lt_trichotomy u (ℓ * k) with hcase | hcase | hcase
  · -- SLOPE TOO FLAT: the supporting line touches only the monic top `(m, 0)`
    have hone : ∀ j ∈ sideSet X (monicPoly a) u ℓ, j = m := by
      intro j hj
      by_contra hjm
      have hjlt : j < m := lt_of_le_of_ne (hrange j hj) hjm
      have hon : OnSide X (monicPoly a) u ℓ j := onSide_of_mem_sideSet hj
      have hinf : suppVal X (monicPoly a) u ℓ
          ≤ ℓ • npHgt X (monicPoly a) m + ((u * m : ℕ) : ℕ∞) := Finset.inf_le hmemm
      rw [← hon, hnpm] at hinf
      have hchain : ((ℓ * ((m - j) * k) + u * j : ℕ) : ℕ∞)
          ≤ ((ℓ * 0 + u * m : ℕ) : ℕ∞) := by
        calc ((ℓ * ((m - j) * k) + u * j : ℕ) : ℕ∞)
            = ℓ • ((((m - j) * k : ℕ)) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := by
              rw [enat_smul_nat]; push_cast; ring
          _ ≤ ℓ • npHgt X (monicPoly a) j + ((u * j : ℕ) : ℕ∞) :=
              add_le_add (enat_smul_mono (hnpge j)) le_rfl
          _ ≤ ℓ • ((0 : ℕ) : ℕ∞) + ((u * m : ℕ) : ℕ∞) := by simpa using hinf
          _ = ((ℓ * 0 + u * m : ℕ) : ℕ∞) := by rw [enat_smul_nat]; push_cast; ring
      have hnat : ℓ * ((m - j) * k) + u * j ≤ ℓ * 0 + u * m := by exact_mod_cast hchain
      have hR : u * j + u * (m - j) = u * m := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (le_of_lt hjlt)]
      have hL : ℓ * ((m - j) * k) + u * j = u * j + (ℓ * k) * (m - j) := by ring
      rw [hL, Nat.mul_zero, Nat.zero_add, ← hR] at hnat
      have h3 := Nat.le_of_mul_le_mul_right (Nat.add_le_add_iff_left.mp hnat) (by omega)
      omega
    have hsd : sideDeg X (monicPoly a) u ℓ hne = 0 := by
      have hmx : sideMax X (monicPoly a) u ℓ hne = sideMin X (monicPoly a) u ℓ hne := by
        rw [sideMax, sideMin, hone _ (Finset.max'_mem _ hne), hone _ (Finset.min'_mem _ hne)]
      rw [sideDeg, hmx, Nat.sub_self, Nat.zero_div]
    obtain ⟨hrd, hc0⟩ := natDegree_resPoly hπ isKeyX hℓ hcop htop hne hpin
    have hRne : resPoly π X (monicPoly a) u ℓ hne H₀ ≠ 0 := fun hzz => hc0 (by simp [hzz])
    have hpow := Polynomial.natDegree_le_of_dvd hdvd hRne
    rw [Polynomial.natDegree_pow, hrd, hsd] at hpow
    have : ψ.natDegree = 0 := by omega
    rw [this] at hblock
    omega
  · -- THE SIDE ITSELF: coprimality forces `ℓ = 1`, `u = k`, and the residual is `(Y − z) ^ m`
    have hℓ1 : ℓ = 1 := by
      have hg : Nat.gcd u ℓ = 1 := hcop
      have hdvdℓ : ℓ ∣ Nat.gcd u ℓ := Nat.dvd_gcd ⟨k, hcase⟩ dvd_rfl
      rw [hg] at hdvdℓ
      exact Nat.dvd_one.mp hdvdℓ
    subst hℓ1
    have huk : u = k := by omega
    subst huk
    -- the cleared support value, exactly
    have hsupp : suppVal X (monicPoly a) u 1 = ((m * u : ℕ) : ℕ∞) := by
      refine le_antisymm ?_ ?_
      · have hle : suppVal X (monicPoly a) u 1
            ≤ (1 : ℕ) • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞) := Finset.inf_le hmem0
        rw [hnp0, enat_smul_nat] at hle
        simpa using hle
      · refine Finset.le_inf ?_
        intro j hj
        have hjm : j ≤ m := by
          have := Finset.mem_range.1 hj
          omega
        calc ((m * u : ℕ) : ℕ∞) = ((1 * ((m - j) * u) + u * j : ℕ) : ℕ∞) := by
              have : (m - j) + j = m := by omega
              congr 1
              calc m * u = ((m - j) + j) * u := by rw [this]
                _ = 1 * ((m - j) * u) + u * j := by ring
          _ = (1 : ℕ) • ((((m - j) * u : ℕ)) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := by
              rw [enat_smul_nat]; push_cast; ring
          _ ≤ (1 : ℕ) • npHgt X (monicPoly a) j + ((u * j : ℕ) : ℕ∞) :=
              add_le_add (enat_smul_mono (hnpge j)) le_rfl
    -- both endpoints are on the side, so the frame is `(u,1)`-pure and `sideMin = 0`
    have hon0 : OnSide X (monicPoly a) u 1 0 := by
      show (1 : ℕ) • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞) = _
      rw [hnp0, enat_smul_nat, hsupp]
      simp
    have honm : OnSide X (monicPoly a) u 1 m := by
      show (1 : ℕ) • npHgt X (monicPoly a) m + ((u * m : ℕ) : ℕ∞) = _
      rw [hnpm, hsupp]
      simp [Nat.mul_comm]
    have hpure : IsPure X (monicPoly a) u 1 := by
      refine ⟨hon0, ?_⟩
      rw [natDegree_X, Nat.div_one, hdeg]
      exact honm
    have hmemS0 : (0 : ℕ) ∈ sideSet X (monicPoly a) u 1 :=
      Finset.mem_filter.2 ⟨hmem0, hon0⟩
    have hmin0 : sideMin X (monicPoly a) u 1 hne = 0 :=
      Nat.le_zero.mp (Finset.min'_le _ _ hmemS0)
    rw [hmin0] at hpin
    -- B.59a's digit identity: the residual polynomial IS the reduction of the parent frame
    have hres := resPoly_X_eq_map_of_scaleRoots (π := π) (g := monicPoly a)
      (G := alphaFrame b ŵ) hπ (monicPoly_monic a)
      (by rw [alphaFrame_natDegree, hdeg]) (by rw [hfa]; rfl) hpure hne hpin
    rw [alphaFrame_map_residue hb ŵ, hŵ] at hres
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      at hres
    set φ := AdjoinRoot.of ((X : Polynomial O).map (residue O)) with hφ
    -- an irreducible with a square dividing `(Y − z) ^ m` is linear
    have hψdvd : ψ ∣ (X - C (φ z)) ^ m := by
      refine dvd_trans (dvd_pow_self ψ two_ne_zero) ?_
      rw [← hres]
      exact hdvd
    have hprime : Prime ψ := hψ.prime
    have hlin : ψ ∣ (X - C (φ z)) := hprime.dvd_of_dvd_pow hψdvd
    have hne0 : (X - C (φ z) : Polynomial (resField (X : Polynomial O))) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero _
    have := Polynomial.natDegree_le_of_dvd hlin hne0
    rw [Polynomial.natDegree_X_sub_C] at this
    omega
  · -- SLOPE TOO STEEP: the supporting line touches only the left endpoint `(0, m k)`
    have hone : ∀ j ∈ sideSet X (monicPoly a) u ℓ, j = 0 := by
      intro j hj
      by_contra hj0
      have hjm : j ≤ m := hrange j hj
      have hon : OnSide X (monicPoly a) u ℓ j := onSide_of_mem_sideSet hj
      have hinf : suppVal X (monicPoly a) u ℓ
          ≤ ℓ • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞) := Finset.inf_le hmem0
      rw [← hon, hnp0] at hinf
      have hchain : ((ℓ * ((m - j) * k) + u * j : ℕ) : ℕ∞)
          ≤ ((ℓ * (m * k) + u * 0 : ℕ) : ℕ∞) := by
        calc ((ℓ * ((m - j) * k) + u * j : ℕ) : ℕ∞)
            = ℓ • ((((m - j) * k : ℕ)) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := by
              rw [enat_smul_nat]; push_cast; ring
          _ ≤ ℓ • npHgt X (monicPoly a) j + ((u * j : ℕ) : ℕ∞) :=
              add_le_add (enat_smul_mono (hnpge j)) le_rfl
          _ ≤ ℓ • ((m * k : ℕ) : ℕ∞) + ((u * 0 : ℕ) : ℕ∞) := hinf
          _ = ((ℓ * (m * k) + u * 0 : ℕ) : ℕ∞) := by rw [enat_smul_nat]; push_cast; ring
      have hnat : ℓ * ((m - j) * k) + u * j ≤ ℓ * (m * k) + u * 0 := by exact_mod_cast hchain
      have hL1 : ℓ * ((m - j) * k) + (ℓ * k) * j = ℓ * (m * k) := by
        have hmj : (m - j) + j = m := by omega
        calc ℓ * ((m - j) * k) + (ℓ * k) * j = (ℓ * k) * ((m - j) + j) := by ring
          _ = ℓ * (m * k) := by rw [hmj]; ring
      rw [Nat.mul_zero, Nat.add_zero, ← hL1] at hnat
      have h3 := Nat.le_of_mul_le_mul_right (Nat.add_le_add_iff_left.mp hnat)
        (Nat.pos_of_ne_zero hj0)
      omega
    have hsd : sideDeg X (monicPoly a) u ℓ hne = 0 := by
      have hmx : sideMax X (monicPoly a) u ℓ hne = sideMin X (monicPoly a) u ℓ hne := by
        rw [sideMax, sideMin, hone _ (Finset.max'_mem _ hne), hone _ (Finset.min'_mem _ hne)]
      rw [sideDeg, hmx, Nat.sub_self, Nat.zero_div]
    obtain ⟨hrd, hc0⟩ := natDegree_resPoly hπ isKeyX hℓ hcop htop hne hpin
    have hRne : resPoly π X (monicPoly a) u ℓ hne H₀ ≠ 0 := fun hzz => hc0 (by simp [hzz])
    have hpow := Polynomial.natDegree_le_of_dvd hdvd hRne
    rw [Polynomial.natDegree_pow, hrd, hsd] at hpow
    have : ψ.natDegree = 0 := by omega
    rw [this] at hblock
    omega

/-! ## 4. The inverse shear, packaged -/

/-- The parent's coefficient vector, read off `alphaParent_coeff`: the `i`-th coordinate is the
`i`-th coefficient of the un-scaled frame times `(π ^ k) ^ (m − i)`. -/
theorem coeff_eq_of_monicPoly_eq_alphaParent {π : O} {m k : ℕ} {b : Fin m → O} {ŵ : O}
    {a : Fin m → O} (hfa : monicPoly a = alphaParent π b k ŵ) (i : Fin m) :
    a i = (alphaFrame b ŵ).coeff (i : ℕ) * (π ^ k) ^ (m - (i : ℕ)) := by
  have h1 : (monicPoly a).coeff (i : ℕ) = a i := by simpa using monicPoly_coeff_lt a i.isLt
  rw [← h1, hfa, alphaParent_coeff]

/-- Every coordinate of the parent's coefficient vector lies in `𝔪`: at `1 ≤ k` the factor
`(π ^ k) ^ (m − i)` is a positive power of `π` for every `i < m`. -/
theorem mem_maximalIdeal_of_monicPoly_eq_alphaParent {π : O} (hπ : Irreducible π) {m k : ℕ}
    (hk : 1 ≤ k) {b : Fin m → O} {ŵ : O} {a : Fin m → O}
    (hfa : monicPoly a = alphaParent π b k ŵ) (i : Fin m) : a i ∈ maximalIdeal O := by
  have hdvd : π ∣ a i := by
    rw [coeff_eq_of_monicPoly_eq_alphaParent hfa i]
    refine Dvd.dvd.mul_left ?_ _
    rw [← pow_mul]
    exact dvd_pow_self π (Nat.mul_ne_zero (by omega) (by have := i.isLt; omega))
  have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 (a i)).2 (by rwa [pow_one])
  rwa [pow_one] at h

/-- **The inverse shear lands in the α locus.**  If the state `c` is carried by a coefficient
vector `a` whose monic development is the parent frame `alphaParent π b k (resSect O z)` of a
child lift `b` with all coordinates in `𝔪`, then `c` IS an α(k, z) state and its α child is the
class of `b`.

This is the whole construction behind clause (ii); it is stated separately so that H.115c's
fibre count reads the same parametrization.  The four `IsAlphaState` obligations are discharged
as listed in the module docstring, and clause (i) (`alphaChild_spec`) identifies the child. -/
theorem exists_isAlphaState_of_alphaParent {π : O} (hπ : Irreducible π) {m N k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1)
    (hz : z ≠ 0) {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O) {a : Fin m → O}
    (hfa : monicPoly a = alphaParent π b k (resSect O z)) {c : ClusterState O m N}
    (hc : c.1 = proj O m N a) :
    ∃ h : IsAlphaState π c k z, (alphaChild π c h).1 = proj O m (N - m * k) b := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hm0 : 0 < m := by omega
  have hmkN : m * k + 1 ≤ N := by omega
  have hπdvd : ∀ x : O, x ∈ maximalIdeal O → π ∣ x := by
    intro x hx
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h
  set ŵ : O := resSect O z with hŵdef
  have hŵ : residue O ŵ = z := residue_resSect O z
  have hproj : proj O m N a = c.1 := hc.symm
  have hacoeff : ∀ i : Fin m,
      a i = (alphaFrame b ŵ).coeff (i : ℕ) * (π ^ k) ^ (m - (i : ℕ)) :=
    coeff_eq_of_monicPoly_eq_alphaParent hfa
  have hcval : ∀ (j : ℕ) (hj : j < m),
      c.1 ⟨j, hj⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨j, hj⟩) := by
    intro j hj
    rw [← hproj]
    rfl
  -- STEP 3: the recentring at the pinned pair is the child's development, scaled
  have hrec : (monicPoly a).comp (C (π ^ k) * (X + C ŵ)) = C (π ^ (m * k)) * monicPoly b := by
    rw [hfa]; exact alphaParent_recentre π b k ŵ
  -- STEP 4: non-drain (this is where `z ≠ 0` pins the constant coefficient's valuation)
  have hG0 : a ⟨0, hm0⟩ = (alphaFrame b ŵ).coeff 0 * π ^ (m * k) := by
    have h := hacoeff ⟨0, hm0⟩
    simpa [Nat.sub_zero, ← pow_mul, Nat.mul_comm k m] using h
  have hnd : ¬ IsDrainState c := by
    intro hdr
    have h0 : c.1 ⟨0, hm0⟩ = 0 := hdr hm0
    rw [hcval 0 hm0] at h0
    have hdvdN : π ^ N ∣ a ⟨0, hm0⟩ :=
      (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : π ^ (m * k + 1) ∣ a ⟨0, hm0⟩ := dvd_trans (pow_dvd_pow π hmkN) hdvdN
    rw [hG0, pow_succ, mul_comm ((alphaFrame b ŵ).coeff 0) (π ^ (m * k))] at h1
    exact alphaFrame_coeff_zero_not_dvd hπ hb hz hŵ
      ((mul_dvd_mul_iff_left (pow_ne_zero (m * k) hπ0)).1 h1)
  -- STEP 5: the capped content is the monic top term
  have hD : betaContent c k = m * k := by
    refine le_antisymm (betaContent_le_mul c k) ?_
    refine Finset.le_inf' _ _ ?_
    intro j _
    by_cases hjm : j < m
    · rw [dif_pos hjm]
      have hle : (m - j) * k ≤ N :=
        le_trans (Nat.mul_le_mul_right k (Nat.sub_le m j)) (by omega)
      have hdvdj : π ^ ((m - j) * k) ∣ a ⟨j, hjm⟩ := by
        rw [hacoeff ⟨j, hjm⟩]
        exact Dvd.dvd.mul_left (dvd_of_eq (by rw [← pow_mul, Nat.mul_comm k (m - j)])) _
      have hge : (m - j) * k ≤ resOrd (c.1 ⟨j, hjm⟩) := by
        rw [hcval j hjm]
        exact (resOrd_ge_iff hπ hle (a ⟨j, hjm⟩)).2 hdvdj
      have hsum : (m - j) * k + j * k = m * k := by
        have hmj : (m - j) + j = m := by omega
        calc (m - j) * k + j * k = ((m - j) + j) * k := by ring
          _ = m * k := by rw [hmj]
      omega
    · rw [dif_neg hjm]
  -- STEP 6: the full-multiplicity child event
  have hchild : HasChildAt π c m k z := by
    refine hasChildAt_of_exists hπ hN hnd hm hk hz a ŵ hproj hŵ ?_ ?_ ?_
    · intro j
      rw [hD, hrec, coeff_C_mul]
      exact Dvd.intro _ rfl
    · intro j hj
      rw [hD, hrec, coeff_C_mul, monicPoly_coeff_lt b hj, pow_succ]
      exact mul_dvd_mul_left _ (hπdvd _ (hb ⟨j, hj⟩))
    · rw [hD, hrec, coeff_C_mul]
      have htop : (monicPoly b).coeff m = 1 := by
        have h := (monicPoly_monic b).coeff_natDegree
        rwa [monicPoly_natDegree] at h
      rw [htop, mul_one]
      intro hdd
      rw [pow_succ] at hdd
      have hdd' : π ^ (m * k) * π ∣ π ^ (m * k) * 1 := by rwa [mul_one]
      exact hπ.not_isUnit
        (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero (m * k) hπ0)).1 hdd'))
  -- STEP 7: not CS, hence an α state
  have hcs : ¬ IsCSState π c := not_isCSState_of_alphaParent hπ hk hz hb hŵ hproj hfa
  refine ⟨⟨hnd, hcs, hchild⟩, ?_⟩
  -- STEP 8: clause (i) identifies the child of the witness with the class of `b`
  obtain ⟨b', -, hb'fac, hb'proj⟩ :=
    alphaChild_spec hπ hm hN c ⟨hnd, hcs, hchild⟩ a hproj
  have hCne : (C (π ^ (m * k)) : Polynomial O) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using pow_ne_zero (m * k) hπ0
  have hbb : monicPoly b' = monicPoly b := mul_left_cancel₀ hCne (hb'fac.symm.trans hrec)
  have hb'b : b' = b := by
    refine funext fun i => ?_
    have h1 := monicPoly_coeff_lt b' i.isLt
    have h2 := monicPoly_coeff_lt b i.isLt
    rw [hbb] at h1
    simpa using h1.symm.trans h2
  rw [← hb'proj, hb'b]

end Parent

/-! ## 5. H.115 (clause ii) — the shear is ONTO -/

/-- **H.115 (clause ii).** The shear is ONTO the full window-`(N−mk)` state space.

The witness is the inverse shear of §1 applied to a child lift with coordinates in `𝔪`; the
four `IsAlphaState` obligations are discharged as listed in the module docstring, and clause
(i) (`alphaChild_spec`) identifies the child of the witness with the given state. -/
theorem alphaChild_surjective {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) (hz : z ≠ 0) :
    ∀ d : ClusterState O m (N - m * k),
      ∃ (c : ClusterState O m N) (h : IsAlphaState π c k z), alphaChild π c h = d := by
  classical
  intro d
  -- STEP 1: a child lift with every coordinate in `𝔪`
  have hlift : ∀ i : Fin m, ∃ y : O, y ∈ maximalIdeal O ∧
      Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)) y = d.1 i := fun i =>
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (d.2 i)
  choose b hb hbd using hlift
  have hbproj : proj O m (N - m * k) b = d.1 := funext hbd
  -- STEP 2: the parent frame and its coefficient vector
  obtain ⟨a, hfa⟩ := exists_monicPoly_eq (alphaParent_monic π b k (resSect O z))
    (alphaParent_natDegree π b k (resSect O z))
  have hamem : ∀ i : Fin m, a i ∈ maximalIdeal O :=
    mem_maximalIdeal_of_monicPoly_eq_alphaParent hπ hk hfa
  -- STEPS 3–8: the packaged inverse shear
  obtain ⟨h, hch⟩ := exists_isAlphaState_of_alphaParent hπ hm hN hk hw hz hb hfa
    (c := ⟨proj O m N a, fun i => Ideal.mem_map_of_mem _ (hamem i)⟩) rfl
  exact ⟨_, h, Subtype.ext (hch.trans hbproj)⟩

end Uniformity.Density.Induction

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaFrame
#print axioms Uniformity.Density.Induction.alphaParent
#print axioms Uniformity.Density.Induction.alphaParent_recentre
#print axioms Uniformity.Density.Induction.alphaFrame_map_residue
#print axioms Uniformity.Density.Induction.alphaParent_npHgt_zero
#print axioms Uniformity.Density.Induction.not_isCSState_of_alphaParent
#print axioms Uniformity.Density.Induction.coeff_eq_of_monicPoly_eq_alphaParent
#print axioms Uniformity.Density.Induction.mem_maximalIdeal_of_monicPoly_eq_alphaParent
#print axioms Uniformity.Density.Induction.exists_isAlphaState_of_alphaParent
#print axioms Uniformity.Density.Induction.alphaChild_surjective

end AxCheck
