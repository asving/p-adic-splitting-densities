/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115c
import Uniformity.ChapH.H116

/-!
# Uniformity.ChapH.H116bR — the β re-planting machinery (H.116b support)

**Chapter H, NODE H.116 SPLIT b, support module** (`blueprint/CHAP-H_general_induction.md`
§17.2; the blueprint's mandated split H.116a/H.116b).  This module builds the machinery for
`betaExtract_fiber_card` (H.116b, the per-genre equicardinal-fibre theorem): the
RE-PLANTING construction certified by
`verification/openmath/OM2_h116b_replant_cert.py` (2026-08-16, 68/68, both rings).

## The construction being formalized (certification steps C1–C4)

* **C1 (planted factor).**  A child lift `b` (degree `μ`, coordinates in `𝔪`) at slope `k`
  and pinned centre `ẑ` plants as `alphaParent π b k ẑ` — H.115b's inverse shear, REUSED:
  monic of degree `μ`, reduction `X ^ μ`, and at EVERY frame `(k', w')` its coefficients
  carry `π ^ (μ * min k k')`, with the divided reduction b-INDEPENDENT and of UNIT constant
  term whenever `(k', z') ≠ (k, z)`.
* **C2 (peel).**  Every lift of a non-drain state with a `(μ, k, z)`-child factors EXACTLY
  as `monicPoly a = alphaParent π b k ẑ * Q` with `proj b` the `betaChild` class — the
  `%ₘ`-degree argument on top of H.116's clause-(i) machinery.
* **C3 (replant).**  Swap `b` for a lift of a TARGET child state and remultiply.
* **C4 (genre transport).**  The swapped state keeps the child SET, all contents, and the
  drain/full-child status: the two frames agree ONE DIGIT PAST the content at every slope,
  because the planted difference carries `π ^ (μ * min k k' + 1)` at every frame.

This module lands the layers of C1–C4 that are pure frame arithmetic (no polygon API):

* §1 the frame-transfer layer: divisibility of frame coefficients ⟺ the graded
  divisibility `π ^ s ∣ aⱼ · π ^ (k j)` of the development coefficients (both directions of
  the substitution `X ↦ X + w` are triangular — H.115c's `pow_dvd_coeff_comp_X_add_C`);
* §2 the content characterization: `betaContent c k` is THE exact frame-divisibility level
  of any lift at any centre (non-drain), and `k * μ ≤ betaContent c k` under a child event;
* §3 the planted-factor frame profiles (C1) — divisibility, the difference one digit
  deeper, the reduction `X ^ μ`, and the unit constant term at foreign frames;
* §4 the exact peel (C2);
* §5 the single-child replant and its genre transport (C3–C4, the frame-arithmetic legs).

## What is NOT here (still owed to H.116b)

* the `¬ IsCSState` transport for the replanted state (side data + `resPoly` of the swap
  agree — certification check G; needs the ChapB polygon API);
* the fibre COUNT itself.  **FINDING (certification D3, refuted with witnesses):** the
  naive stability — "two exact planted presentations of `≡ π^N`-lifts, shifted by the same
  `Δ`, stay `≡ π^N`" — is FALSE in same-slope multi-child genres (the two planted
  sub-lattices carry a genuine syzygy; gauge of size `q^4` in the census cell), so
  injectivity of the replant map does NOT follow from presentation stability.  The measured
  facts (battery E1/E2): the fibres ARE equicardinal per `(L, D)`-with-`z` and the
  canonical-lift replant IS a bijection; the counting proof must run through the raw
  presentation space with constant presentation-multiplicity.  Recorded in the unit note.

DEPENDS: H.108 (`betaContent`, `IsDrainState`, `betaContent_le`, `betaContent_le_of_lt`,
`betaContent_le_mul`), H.107 (`resOrd_ge_iff`, `resOrd_le`, `mem_maximalIdeal_pow_iff_dvd_of_irr`),
H.109 (`HasChildAt`), H.115 (`resSect`, `recFrame`), H.115b (`alphaParent`, `alphaFrame`,
`alphaParent_coeff`, `alphaParent_recentre`, `alphaFrame_coeff_zero_not_dvd`,
`alphaFrame_map_residue`), H.115c (`pow_dvd_coeff_comp_X_add_C`, `comp_recentre_injective`,
`proj_eq_iff_pow_dvd`), H.116 (`betaChild_spec`, `monicFactor_congr_of_pow_dvd_sub`,
`monicPoly_map_residue`), H.116h (via H.116) · landed `monicPoly`, `proj`,
`exists_monicPoly_eq`, `monicPoly_coeff_lt` · mathlib `Polynomial.comp_C_mul_X_coeff`,
`Polynomial.comp_assoc`, `Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`,
`Finset.exists_mem_eq_inf'`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` where H.116's spec is consumed + `π`
explicit, every binder INLINE.

## TEETH (GC-8)

`verification/openmath/OM2_h116b_replant_cert.py` (68/68): §1–§2 are exercised by every
factorization/content read of checks B/C; §3 is check F verbatim (the three-case profile,
`w_{k'} = μ·min(k,k')`, b-independence, unit constants); §4 is check B (exact factorization,
margin ≥ N+3 at every tested lift); §5 is check C (replant lands in the fibre with the child
set EXACTLY `L`).

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The frame-transfer layer -/

section Transfer

variable {O : Type*} [CommRing O]

/-- Recentring factors through the scaling: `f (t(X + w)) = (f (tX))(X + w)`. -/
theorem comp_recentre_eq_comp_comp (f : Polynomial O) (t w : O) :
    f.comp (C t * (X + C w)) = (f.comp (C t * X)).comp (X + C w) := by
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [mul_comp, C_comp, X_comp]

/-- **The frame-transfer iff.**  Uniform `π ^ s`-divisibility of the frame coefficients is
exactly the graded divisibility `π ^ s ∣ f.coeff j * π ^ (k * j)` of the development —
the shift `X ↦ X + w` is triangular in BOTH directions (H.115c's mechanism), so it moves
nothing across the level. -/
theorem pow_dvd_coeff_recentre_iff {π : O} {s : ℕ} (f : Polynomial O) (k : ℕ) (w : O) :
    (∀ j, π ^ s ∣ (f.comp (C (π ^ k) * (X + C w))).coeff j) ↔
      ∀ j, π ^ s ∣ f.coeff j * π ^ (k * j) := by
  have hmono : Monotone (fun _ : ℕ => s) := monotone_const
  have hscale : ∀ j, (f.comp (C (π ^ k) * X)).coeff j = f.coeff j * π ^ (k * j) := by
    intro j
    rw [comp_C_mul_X_coeff, ← pow_mul]
  constructor
  · intro h j
    have hback : f.comp (C (π ^ k) * X)
        = (f.comp (C (π ^ k) * (X + C w))).comp (X + C (-w)) := by
      rw [comp_recentre_eq_comp_comp, Polynomial.comp_assoc]
      have hid : (X + C w).comp (X + C (-w)) = (X : Polynomial O) := by
        simp only [add_comp, X_comp, C_comp, map_neg]
        ring
      rw [hid, comp_X]
    have := pow_dvd_coeff_comp_X_add_C (n := fun _ => s) hmono h (-w) j
    rw [← hback, hscale j] at this
    exact this
  · intro h j
    have hfw : ∀ i, π ^ s ∣ (f.comp (C (π ^ k) * X)).coeff i := by
      intro i
      rw [hscale i]
      exact h i
    have := pow_dvd_coeff_comp_X_add_C (n := fun _ => s) hmono hfw w j
    rwa [← comp_recentre_eq_comp_comp] at this

/-- Every frame coefficient carries the scaling grade: `π ^ (k * j) ∣ (f-frame).coeff j`,
for ANY `f` and ANY centre. -/
theorem pow_mul_dvd_coeff_recentre {π : O} (f : Polynomial O) (k : ℕ) (w : O) (j : ℕ) :
    π ^ (k * j) ∣ (f.comp (C (π ^ k) * (X + C w))).coeff j := by
  have hmono : Monotone (fun i : ℕ => k * i) := fun i i' h => Nat.mul_le_mul_left k h
  have hbase : ∀ i, π ^ (k * i) ∣ (f.comp (C (π ^ k) * X)).coeff i := by
    intro i
    rw [comp_C_mul_X_coeff, ← pow_mul]
    exact Dvd.intro_left _ rfl
  have := pow_dvd_coeff_comp_X_add_C (n := fun i => k * i) hmono hbase w j
  rwa [← comp_recentre_eq_comp_comp] at this

end Transfer

/-! ## 2. The content is the exact frame level -/

section Content

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The content divides every frame coefficient**, at any lift and ANY centre (the content
is centre-free).  The `j < m` legs are H.107's representative transport under H.108's
infimum; the monic top is `betaContent_le_mul`. -/
theorem pow_content_dvd_coeff_recentre {π : O} (hπ : Irreducible π) {m N : ℕ}
    (c : ClusterState O m N) (k : ℕ) {a : Fin m → O} (ha : proj O m N a = c.1) (w : O) :
    ∀ j, π ^ betaContent c k ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j := by
  rw [pow_dvd_coeff_recentre_iff]
  intro j
  rcases lt_trichotomy j m with hj | hj | hj
  · have hcj : c.1 ⟨j, hj⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨j, hj⟩) :=
      (congrFun ha ⟨j, hj⟩).symm
    have hres : π ^ resOrd (c.1 ⟨j, hj⟩) ∣ a ⟨j, hj⟩ := by
      have h1 : resOrd (c.1 ⟨j, hj⟩) ≤ N := resOrd_le _
      have h2 := (resOrd_ge_iff hπ h1 (a ⟨j, hj⟩)).1
      rw [← hcj] at h2
      exact h2 le_rfl
    have hle : betaContent c k ≤ resOrd (c.1 ⟨j, hj⟩) + j * k := betaContent_le_of_lt c k hj
    have hkj : k * j = j * k := Nat.mul_comm k j
    have hsplit : π ^ betaContent c k ∣ π ^ resOrd (c.1 ⟨j, hj⟩) * π ^ (k * j) := by
      rw [← pow_add]
      exact pow_dvd_pow π (by omega)
    refine hsplit.trans ?_
    rw [monicPoly_coeff_lt a hj]
    exact mul_dvd_mul_right hres _
  · have htop : (monicPoly a).coeff j = 1 := by
      have h := (monicPoly_monic a).coeff_natDegree
      rw [monicPoly_natDegree] at h
      rw [hj]; exact h
    rw [htop, one_mul, hj]
    have hkm : k * m = m * k := Nat.mul_comm k m
    exact pow_dvd_pow π (by have := betaContent_le_mul c k; omega)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega), zero_mul]
    exact dvd_zero _

/-- **The content is EXACT** on a non-drain state: one more power of `π` fails at some frame
coefficient (at any lift, ANY centre).  The failing abscissa is where H.108's infimum is
attained. -/
theorem not_pow_content_succ_dvd_coeff_recentre {π : O} (hπ : Irreducible π) {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N) (h0 : ¬ IsDrainState c) (k : ℕ)
    {a : Fin m → O} (ha : proj O m N a = c.1) (w : O) :
    ¬ ∀ j, π ^ (betaContent c k + 1) ∣
      ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  rw [pow_dvd_coeff_recentre_iff]
  intro hall
  -- the infimum is attained
  obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (m + 1))
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun j => if h : j < m then resOrd (c.1 ⟨j, h⟩) + j * k else m * k)
  have hDdef : betaContent c k
      = if h : j₀ < m then resOrd (c.1 ⟨j₀, h⟩) + j₀ * k else m * k := hj₀
  by_cases hj₀m : j₀ < m
  · rw [dif_pos hj₀m] at hDdef
    -- the non-drain bound kills the invisible case
    have hDle : betaContent c k ≤ N - 1 := betaContent_le hm hN c h0 k
    have hrOle : resOrd (c.1 ⟨j₀, hj₀m⟩) ≤ N := resOrd_le _
    have hrOlt : resOrd (c.1 ⟨j₀, hj₀m⟩) < N := by omega
    -- exactness of `resOrd` below the window
    have hcj : c.1 ⟨j₀, hj₀m⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨j₀, hj₀m⟩) :=
      (congrFun ha ⟨j₀, hj₀m⟩).symm
    have hnd : ¬ π ^ (resOrd (c.1 ⟨j₀, hj₀m⟩) + 1) ∣ a ⟨j₀, hj₀m⟩ := by
      intro hdvd
      have hle1 : resOrd (c.1 ⟨j₀, hj₀m⟩) + 1 ≤ N := by omega
      have h2 := (resOrd_ge_iff hπ hle1 (a ⟨j₀, hj₀m⟩)).2 hdvd
      rw [← hcj] at h2
      omega
    -- cancel the scaling grade
    have hj₀dvd := hall j₀
    rw [monicPoly_coeff_lt a hj₀m, hDdef] at hj₀dvd
    refine hnd ?_
    have hkj : k * j₀ = j₀ * k := Nat.mul_comm k j₀
    have hcan : π ^ (resOrd (c.1 ⟨j₀, hj₀m⟩) + 1) * π ^ (k * j₀)
        ∣ a ⟨j₀, hj₀m⟩ * π ^ (k * j₀) := by
      refine dvd_trans (dvd_of_eq ?_) hj₀dvd
      rw [← pow_add]
      congr 1
      omega
    exact (mul_dvd_mul_iff_right (pow_ne_zero (k * j₀) hπ0)).1 hcan
  · rw [dif_neg hj₀m] at hDdef
    have hj₀eq : j₀ = m := by
      have := Finset.mem_range.1 hj₀mem
      omega
    have htop : (monicPoly a).coeff j₀ = 1 := by
      have h := (monicPoly_monic a).coeff_natDegree
      rw [monicPoly_natDegree] at h
      rw [hj₀eq]; exact h
    have hj₀dvd := hall j₀
    rw [htop, one_mul, hDdef, hj₀eq] at hj₀dvd
    -- `π ^ (m k + 1) ∣ π ^ (k m)` forces `π` a unit
    have hkm : π ^ (m * k) * π ∣ π ^ (m * k) * 1 := by
      rw [mul_one, ← pow_succ]
      refine hj₀dvd.trans (dvd_of_eq ?_)
      rw [Nat.mul_comm]
    exact hπ.not_isUnit
      (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero (m * k) hπ0)).1 hkm))

/-- **The content characterization.**  A level that divides the whole frame and fails one
digit higher IS the content — at any lift, any centre, on a non-drain state.  This is the
transport workhorse: it computes `betaContent` of a CONSTRUCTED state from a factorization
of one of its lifts. -/
theorem betaContent_eq_of_recentre_exact {π : O} (hπ : Irreducible π) {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N) (h0 : ¬ IsDrainState c) (k : ℕ)
    {a : Fin m → O} (ha : proj O m N a = c.1) (w : O) {D : ℕ}
    (h1 : ∀ j, π ^ D ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j)
    (h2 : ¬ ∀ j, π ^ (D + 1) ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j) :
    betaContent c k = D := by
  rcases lt_trichotomy (betaContent c k) D with h | h | h
  · exact absurd (fun j => (pow_dvd_pow π (by omega : betaContent c k + 1 ≤ D)).trans (h1 j))
      (not_pow_content_succ_dvd_coeff_recentre hπ hm hN c h0 k ha w)
  · exact h
  · exact absurd (fun j => (pow_dvd_pow π (by omega : D + 1 ≤ betaContent c k)).trans
      (pow_content_dvd_coeff_recentre hπ c k ha w j)) h2

/-- **The child multiplicity sits under the content**: `k * μ ≤ betaContent c k` whenever a
`(μ, k, z)`-child exists — abscissa `μ` carries the scaling grade `π ^ (k μ)` and is exactly
at the content (H.109's third clause, read at the pinned lift pair). -/
theorem mul_le_betaContent {π : O} {m N μ k : ℕ} {z : ResidueField O}
    {c : ClusterState O m N} (h : HasChildAt π c μ k z) :
    k * μ ≤ betaContent c k := by
  by_contra hlt
  obtain ⟨-, -, -, hall⟩ := h
  obtain ⟨-, -, c3⟩ := hall (classSect O m N c.1) (resSect O z)
    (proj_classSect O m N c.1) (residue_resSect O z)
  refine c3 ?_
  refine (pow_dvd_pow π (by omega : betaContent c k + 1 ≤ k * μ)).trans ?_
  exact pow_mul_dvd_coeff_recentre (monicPoly (classSect O m N c.1)) k (resSect O z) μ

end Content

/-! ## 3. The planted factor and its frame profiles (C1) -/

section Planted

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The exponent bookkeeping of the planted profiles: at abscissa `j ≤ μ` the planted
coefficient grade `k (μ − j) + k' j` dominates the profile floor `μ · min k k'`. -/
private theorem min_mul_le_grade {k k' μ j : ℕ} (hj : j ≤ μ) :
    μ * min k k' ≤ k * (μ - j) + k' * j := by
  rcases Nat.le_total k k' with h | h
  · rw [Nat.min_eq_left h]
    calc μ * k = k * (μ - j) + k * j := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hj, Nat.mul_comm]
      _ ≤ k * (μ - j) + k' * j := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_right j h) _
  · rw [Nat.min_eq_right h]
    calc μ * k' = k' * (μ - j) + k' * j := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hj, Nat.mul_comm]
      _ ≤ k * (μ - j) + k' * j := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right (μ - j) h) _

/-- **The planted factor reduces to `X ^ μ`** — every sub-top coefficient carries a positive
power of `π` from the shear grading, so no `𝔪`-condition on `b` is consulted. -/
theorem alphaParent_map_residue {π : O} (hπ : Irreducible π) {μ : ℕ} (b : Fin μ → O)
    {k : ℕ} (hk : 1 ≤ k) (ŵ : O) :
    (alphaParent π b k ŵ).map (residue O) = X ^ μ := by
  have hπm : residue O π = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 π).2 (by rw [pow_one])
    rwa [pow_one] at this
  refine Polynomial.ext fun j => ?_
  rw [coeff_map, coeff_X_pow, alphaParent_coeff]
  rcases lt_trichotomy j μ with hj | hj | hj
  · rw [if_neg (Nat.ne_of_lt hj), map_mul, map_pow, map_pow, hπm,
      zero_pow (by omega : k ≠ 0), zero_pow (by omega : μ - j ≠ 0), mul_zero]
  · have htop : (alphaFrame b ŵ).coeff j = 1 := by
      have h := (alphaFrame_monic b ŵ).coeff_natDegree
      rw [alphaFrame_natDegree] at h
      rw [hj]; exact h
    rw [if_pos hj, htop, hj, Nat.sub_self, pow_zero, mul_one, map_one]
  · rw [if_neg (by omega : ¬ j = μ),
      coeff_eq_zero_of_natDegree_lt (by rw [alphaFrame_natDegree]; omega), zero_mul, map_zero]

/-- **The planted profile (C1, divisibility).**  At EVERY frame `(k', w')` the planted factor's
coefficients carry `π ^ (μ * min k k')` — the certified `w_{k'}(P) = μ · min(k, k')` law,
lower-bound half, centre-free. -/
theorem pow_min_dvd_coeff_recentre_alphaParent {π : O} {μ : ℕ} (b : Fin μ → O)
    (k : ℕ) (ŵ : O) (k' : ℕ) (w' : O) :
    ∀ j, π ^ (μ * min k k') ∣
      ((alphaParent π b k ŵ).comp (C (π ^ k') * (X + C w'))).coeff j := by
  rw [pow_dvd_coeff_recentre_iff]
  intro j
  by_cases hj : j ≤ μ
  · rw [alphaParent_coeff, ← pow_mul]
    refine dvd_trans (pow_dvd_pow π (min_mul_le_grade hj)) ?_
    rw [pow_add]
    exact mul_dvd_mul (dvd_mul_left _ _) dvd_rfl
  · rw [coeff_eq_zero_of_natDegree_lt
      (by rw [alphaParent_natDegree]; omega), zero_mul]
    exact dvd_zero _

/-- **The planted difference is one digit deeper (C4's engine).**  Two planted factors whose
lifts differ coordinatewise in `𝔪` have frames agreeing to `π ^ (μ * min k k' + 1)` at EVERY
frame `(k', w')` — the b-INDEPENDENCE of the planted profile, one digit past the floor.  This
is what transports the whole child/content structure across a re-planting. -/
theorem pow_min_succ_dvd_coeff_recentre_alphaParent_sub {π : O} (hπ : Irreducible π)
    {μ : ℕ} {b b' : Fin μ → O} (hbb : ∀ i, b' i - b i ∈ maximalIdeal O)
    (k : ℕ) (ŵ : O) (k' : ℕ) (w' : O) :
    ∀ j, π ^ (μ * min k k' + 1) ∣
      (((alphaParent π b' k ŵ) - (alphaParent π b k ŵ)).comp
        (C (π ^ k') * (X + C w'))).coeff j := by
  have hπd : ∀ x : O, x ∈ maximalIdeal O → π ∣ x := by
    intro x hx
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h
  -- the frame difference of the two planted factors, coefficientwise
  have hcoeff : ∀ j, ((alphaParent π b' k ŵ) - (alphaParent π b k ŵ)).coeff j
      = (alphaFrame b' ŵ - alphaFrame b ŵ).coeff j * (π ^ k) ^ (μ - j) := by
    intro j
    rw [coeff_sub, coeff_sub, alphaParent_coeff, alphaParent_coeff, sub_mul]
  -- `π` divides every coefficient of the un-scaled frame difference
  have hframe : ∀ i, π ∣ (alphaFrame b' ŵ - alphaFrame b ŵ).coeff i := by
    have he : alphaFrame b' ŵ - alphaFrame b ŵ
        = (monicPoly b' - monicPoly b).comp (X + C (-ŵ)) := by
      rw [alphaFrame, alphaFrame, ← sub_comp]
      congr 1
      rw [map_neg, sub_eq_add_neg]
    have hmb : ∀ i, π ^ 1 ∣ (monicPoly b' - monicPoly b).coeff i := by
      intro i
      rw [pow_one, coeff_sub]
      rcases lt_trichotomy i μ with hi | hi | hi
      · rw [monicPoly_coeff_lt b' hi, monicPoly_coeff_lt b hi]
        exact hπd _ (hbb ⟨i, hi⟩)
      · have h1 := (monicPoly_monic b').coeff_natDegree
        have h2 := (monicPoly_monic b).coeff_natDegree
        rw [monicPoly_natDegree] at h1 h2
        rw [hi, h1, h2, sub_self]
        exact dvd_zero _
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
          coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega), sub_self]
        exact dvd_zero _
    intro i
    have := pow_dvd_coeff_comp_X_add_C (n := fun _ => 1) monotone_const hmb (-ŵ) i
    rw [← he, pow_one] at this
    exact this
  rw [pow_dvd_coeff_recentre_iff]
  intro j
  by_cases hj : j ≤ μ
  · rw [hcoeff j, ← pow_mul]
    obtain ⟨y, hy⟩ := hframe j
    rw [hy, mul_assoc, mul_assoc]
    rw [pow_succ']
    refine mul_dvd_mul dvd_rfl ?_
    refine dvd_trans (pow_dvd_pow π (min_mul_le_grade hj)) ?_
    rw [pow_add]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left _ dvd_rfl) y
  · have hz : (alphaFrame b' ŵ - alphaFrame b ŵ).coeff j = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
      rw [alphaFrame_natDegree, alphaFrame_natDegree]
      omega
    rw [hcoeff j, hz, zero_mul, zero_mul]
    exact dvd_zero _

/-- Scaling the roots by `0` keeps only the top coefficient: a MONIC polynomial becomes
`X ^ natDegree`. -/
private theorem monic_scaleRoots_zero {R : Type*} [CommRing R] {G : Polynomial R}
    (hG : G.Monic) : G.scaleRoots 0 = X ^ G.natDegree := by
  refine Polynomial.ext fun j => ?_
  rw [coeff_scaleRoots, coeff_X_pow]
  rcases lt_trichotomy j G.natDegree with hj | hj | hj
  · rw [if_neg (Nat.ne_of_lt hj), zero_pow (by omega : G.natDegree - j ≠ 0), mul_zero]
  · rw [if_pos hj, hj, Nat.sub_self, pow_zero, mul_one]
    exact hG.coeff_natDegree
  · rw [if_neg (by omega : ¬ j = G.natDegree), coeff_eq_zero_of_natDegree_lt hj, zero_mul]

/-- `π ^ (E + 1)` never divides `π ^ E * U` when `U` is a unit (nonzero residue). -/
private theorem not_pow_succ_dvd_pow_mul {π : O} (hπ : Irreducible π) (E : ℕ) {U : O}
    (hU : residue O U ≠ 0) : ¬ π ^ (E + 1) ∣ π ^ E * U := by
  intro hdvd
  have hcan : π ^ E * π ∣ π ^ E * U := by
    rw [← pow_succ]
    exact hdvd
  have hd : π ∣ U := (mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).1 hcan
  refine hU (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
  have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 U).2 (by rwa [pow_one])
  rwa [pow_one] at this

/-- **The planted profile (C1, the unit constant at every FOREIGN frame).**  When
`(k', z') ≠ (k, z)` (both residues nonzero), the planted factor's frame at `(k', w')` has
constant coefficient of EXACT grade `μ * min k k'` — the divided reduction has a unit
constant term (`(z' − z) ^ μ`, `z' ^ μ` or `(−z) ^ μ` in the three slope cases), so the
planted factor contributes NO child event and no content beyond its floor at any foreign
frame.  This is the certification battery's check F, unit-constant leg. -/
theorem coeff_zero_recentre_alphaParent_not_dvd {π : O} (hπ : Irreducible π) {μ : ℕ}
    {b : Fin μ → O} (hb : ∀ i, b i ∈ maximalIdeal O) {k : ℕ} {ŵ : O}
    {z : ResidueField O} (hŵ : residue O ŵ = z) (hz : z ≠ 0) {k' : ℕ} {w' : O}
    {z' : ResidueField O} (hw' : residue O w' = z') (hz' : z' ≠ 0)
    (hzz : ¬ (k' = k ∧ z' = z)) :
    ¬ π ^ (μ * min k k' + 1) ∣
      ((alphaParent π b k ŵ).comp (C (π ^ k') * (X + C w'))).coeff 0 := by
  have hπm : residue O π = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 π).2 (by rw [pow_one])
    rwa [pow_one] at this
  -- the constant frame coefficient is the evaluation at `π ^ k' * w'`
  have hc0 : ((alphaParent π b k ŵ).comp (C (π ^ k') * (X + C w'))).coeff 0
      = (alphaParent π b k ŵ).eval (π ^ k' * w') := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    congr 1
    simp
  -- the residue-field reduction of the alphaFrame
  have hfr : (alphaFrame b ŵ).map (residue O) = (X - C z) ^ μ := by
    rw [alphaFrame_map_residue hb ŵ, hŵ]
  -- generic scaleRoots eval identity, at `s = π ^ k'` (shallow) or `s = π ^ k` (steep)
  rcases lt_trichotomy k' k with hklt | hkeq | hkgt
  · -- STRICTLY SHALLOWER frame `k' < k`: split the shear as `π ^ k' * π ^ (k - k')`
    have h1 : alphaParent π b k ŵ
        = ((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).scaleRoots (π ^ k') := by
      rw [alphaParent, show (π : O) ^ k = π ^ (k - k') * π ^ k' from by
        rw [← pow_add]; congr 1; omega, scaleRoots_mul]
    have heval : (alphaParent π b k ŵ).eval (π ^ k' * w')
        = (π ^ k') ^ μ * ((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).eval w' := by
      rw [h1]
      have h2 := scaleRoots_eval₂_mul (RingHom.id O) w' (π ^ k')
        (p := (alphaFrame b ŵ).scaleRoots (π ^ (k - k')))
      simp only [eval₂_id, RingHom.id_apply] at h2
      rw [h2, natDegree_scaleRoots, alphaFrame_natDegree]
    have hUres : residue O (((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).eval w') ≠ 0 := by
      have hmapev : residue O (((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).eval w')
          = (((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).map (residue O)).eval z' := by
        rw [← hw', Polynomial.eval_map, eval₂_at_apply]
      have hmap : ((alphaFrame b ŵ).scaleRoots (π ^ (k - k'))).map (residue O) = X ^ μ := by
        have hlc : residue O (alphaFrame b ŵ).leadingCoeff ≠ 0 := by
          rw [(alphaFrame_monic b ŵ).leadingCoeff, map_one]
          exact one_ne_zero
        rw [map_scaleRoots _ _ (residue O) hlc]
        rw [map_pow, hπm, zero_pow (by omega : k - k' ≠ 0)]
        rw [monic_scaleRoots_zero ((alphaFrame_monic b ŵ).map (residue O))]
        congr 1
        rw [natDegree_map_eq_iff.2 (by
          rw [(alphaFrame_monic b ŵ).leadingCoeff, map_one]; exact Or.inl one_ne_zero),
          alphaFrame_natDegree]
      rw [hmapev, hmap]
      simp only [eval_pow, eval_X]
      exact pow_ne_zero μ hz'
    rw [hc0, heval, ← pow_mul,
      show μ * min k k' = k' * μ from by rw [Nat.min_eq_right (by omega), Nat.mul_comm]]
    exact not_pow_succ_dvd_pow_mul hπ (k' * μ) hUres
  · -- the SAME slope: the shift centre differs by a UNIT and the reduction is `(z'-z) ^ μ`
    subst hkeq
    have hzne : z' ≠ z := fun h => hzz ⟨rfl, h⟩
    have heval : (alphaParent π b k' ŵ).eval (π ^ k' * w')
        = (π ^ k') ^ μ * (alphaFrame b ŵ).eval w' := by
      rw [alphaParent]
      have h2 := scaleRoots_eval₂_mul (RingHom.id O) w' (π ^ k') (p := alphaFrame b ŵ)
      simp only [eval₂_id, RingHom.id_apply] at h2
      rw [h2, alphaFrame_natDegree]
    have hUres : residue O ((alphaFrame b ŵ).eval w') ≠ 0 := by
      have hmapev : residue O ((alphaFrame b ŵ).eval w')
          = ((alphaFrame b ŵ).map (residue O)).eval z' := by
        rw [← hw', Polynomial.eval_map, eval₂_at_apply]
      rw [hmapev, hfr]
      simp only [eval_pow, eval_sub, eval_X, eval_C]
      intro hcon
      exact hzne (sub_eq_zero.1 (pow_eq_zero_iff' .. |>.1 hcon).1)
    rw [hc0, heval, ← pow_mul,
      show μ * min k' k' = k' * μ from by rw [Nat.min_self, Nat.mul_comm]]
    exact not_pow_succ_dvd_pow_mul hπ (k' * μ) hUres
  · -- STRICTLY STEEPER frame `k < k'`: the eval point drops into `𝔪`
    have heval : (alphaParent π b k ŵ).eval (π ^ k' * w')
        = (π ^ k) ^ μ * (alphaFrame b ŵ).eval (π ^ (k' - k) * w') := by
      rw [show (π : O) ^ k' * w' = π ^ k * (π ^ (k' - k) * w') from by
        rw [← mul_assoc, ← pow_add]; congr 2; omega, alphaParent]
      have h2 := scaleRoots_eval₂_mul (RingHom.id O) (π ^ (k' - k) * w') (π ^ k)
        (p := alphaFrame b ŵ)
      simp only [eval₂_id, RingHom.id_apply] at h2
      rw [h2, alphaFrame_natDegree]
    have hUres : residue O ((alphaFrame b ŵ).eval (π ^ (k' - k) * w')) ≠ 0 := by
      have hmapev : residue O ((alphaFrame b ŵ).eval (π ^ (k' - k) * w'))
          = ((alphaFrame b ŵ).map (residue O)).eval (residue O (π ^ (k' - k) * w')) := by
        rw [Polynomial.eval_map, eval₂_at_apply]
      have hr : residue O (π ^ (k' - k) * w') = 0 := by
        rw [map_mul, map_pow, hπm, zero_pow (by omega : k' - k ≠ 0), zero_mul]
      rw [hmapev, hfr, hr]
      simp only [eval_pow, eval_sub, eval_X, eval_C, zero_sub]
      intro hcon
      exact hz (neg_eq_zero.1 (pow_eq_zero_iff' .. |>.1 hcon).1)
    rw [hc0, heval, ← pow_mul,
      show μ * min k k' = k * μ from by rw [Nat.min_eq_left (by omega), Nat.mul_comm]]
    exact not_pow_succ_dvd_pow_mul hπ (k * μ) hUres

end Planted

end Uniformity.Density.Induction

/-! ## Axiom footprint (stages 1–2: §1–§3) -/

section AxCheck

#print axioms Uniformity.Density.Induction.comp_recentre_eq_comp_comp
#print axioms Uniformity.Density.Induction.pow_dvd_coeff_recentre_iff
#print axioms Uniformity.Density.Induction.pow_mul_dvd_coeff_recentre
#print axioms Uniformity.Density.Induction.pow_content_dvd_coeff_recentre
#print axioms Uniformity.Density.Induction.not_pow_content_succ_dvd_coeff_recentre
#print axioms Uniformity.Density.Induction.betaContent_eq_of_recentre_exact
#print axioms Uniformity.Density.Induction.mul_le_betaContent
#print axioms Uniformity.Density.Induction.alphaParent_map_residue
#print axioms Uniformity.Density.Induction.pow_min_dvd_coeff_recentre_alphaParent
#print axioms Uniformity.Density.Induction.pow_min_succ_dvd_coeff_recentre_alphaParent_sub
#print axioms Uniformity.Density.Induction.coeff_zero_recentre_alphaParent_not_dvd

end AxCheck
