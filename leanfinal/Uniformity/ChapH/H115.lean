/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H100
import Uniformity.ChapH.H112
import Uniformity.Density.Transport

/-!
# Uniformity.ChapH.H115 — the canonical lift pair, and the α-shear transport (N-2b)

**Chapter H, AMENDMENT A-H.5 §1 + NODE H.115** [def+theorem]
(`blueprint/CHAP-H_general_induction.md` §17.2, re-signed 2026-08-16 by A-H.5).

## What A-H.5 changed, in one paragraph

The committed clause (i) of `alphaChild_spec` quantified the CENTRE `w` over a residue class
(`∀ a w, proj a = c.1 → residue w = z → …`) while the child is a function of the class alone.
That was REFUTED (`verification/openmath/OM2_h115_h116_centre_shift_refutation.py`, exit 0): a
Taylor shift of the centre by `d ∈ 𝔪` moves the extracted child by `μ · d ∈ 𝔪 ∖ 𝔪²`, and the
child is read at a window `≥ 2`.  DECISION D-H17.3 pins the centre IN THE DEF: `resSect` is a
section of `residue`, `classSect` a section of `proj` (H.100's `Finite`-free
`proj_surjective'`), and `recFrame` the recentred frame read at that pinned lift pair.
Clause (i) keeps the `∀ a` (class-lift) binder — a strengthening beyond the battery's tested
point, licensed by H.109's `pow_dvd_coeff_comp_sub` (`π ^ N` for ANY recentring, hence the FULL
child window `N − m k`) — and drops the `∀ w` (centre) binder, for which H.109's budget is only
`pow_succ_dvd_coeff_shift`'s ONE digit.

* `resSect` / `residue_resSect` — the pinned centre (the pattern machine-checked at
  `leancheck/UniformityCheck/N3Recur.lean`);
* `classSect` / `proj_classSect` — the pinned class lift;
* `recFrame` — the recentred frame of a CLASS at the pinned lift pair;
* `divPow` / `divPow_spec` — exact division by `π ^ n`, totalized (junk `0` off the locus);
* `alphaChild` (def half, REAL BODY) — the recentred, content-divided, window-truncated child;
* `alphaChild_spec` (clause i) — at the canonical centre and at EVERY lift of the class the
  recentring factors EXACTLY as `π ^ (m k) ·` a monic development lifting the child.

Clauses (ii) (`alphaChild_surjective`) and (iii) (`card_alphaFiber`) are the blueprint's
mandated splits H.115b/H.115c and land in their own files.

## The arithmetic of clause (i), in three lines

On an α state H.112's `alpha_content` reads the capped content off the event: `D = m k`, with
`1 ≤ k` and `m k ≤ N − 1`.  H.109's `HasChildAt` then hands over, at EVERY lift pair, both
`π ^ (m k) ∣ g.coeff j` (all `j`) and `π ^ (m k + 1) ∣ g.coeff j` (`j < m`), where
`g = (monicPoly a).comp (C (π ^ k) * (X + C ŵ))`.  So `b j := divPow π (m k) (g.coeff j)` has
every coordinate in `𝔪`, and `g = C (π ^ (m k)) * monicPoly b` because at `j = m` the top
coefficient is `(π ^ k) ^ m` on the nose (H.112's `coeff_recentre_top`) and above `m` there is
nothing (H.112's `natDegree_recentre`).  Lift-independence at the child window is
`pow_dvd_coeff_comp_sub`: two lifts of one class give `π ^ N ∣ (g − g').coeff j`, so their
digit vectors differ by `π ^ (N − m k)` — the full child window.

DEPENDS: H.100 (`proj_surjective'`), H.106 (`ClusterState`), H.107
(`mem_maximalIdeal_pow_iff_dvd_of_irr`), H.108 (`betaContent`), H.109 (`HasChildAt`,
`pow_dvd_coeff_comp_sub`), H.111 (`IsAlphaState`), H.112 (`alpha_content`, `natDegree_recentre`,
`coeff_recentre_top`) · landed `monicPoly`, `proj`, `residue`, `monicPoly_coeff_lt`
(`Uniformity/Density/Transport.lean`) · mathlib `Function.surjInv`,
`IsLocalRing.residue_surjective`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `π` explicit, every binder INLINE.  No `[Finite]`
(clause (i) does not count).

## TEETH (GC-8)

Battery `P1(d) alpha fibres exact+onto, all (k,z) slices` of
`verification/openmath/OM2_genindb_battery.py`.  **The teeth cover the PINNED map only**
(LESSON L-BATT): the battery's `extract_child` recentres at `RB.lift_res(z)` — a function of the
residue alone, i.e. exactly `resSect` — so `P1(d)` certifies the canonical-centre extraction and
says nothing about any other centre.  The standing regression that the refuted `∀ w` reading
stays out is `verification/openmath/OM2_h115_h116_centre_shift_refutation.py` (exit 0 =
refuted).  The `#guard`s below reproduce the exponent bookkeeping the extraction rests on.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. A-H.5 §1 — the canonical lift pair and the pinned frame -/

/-- **A-H.5 §1.** The pinned centre: a section of the residue map, a function of the residue
alone — the Lean counterpart of the battery's `RB.lift_res(z)`. -/
noncomputable def resSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ResidueField O → O :=
  Function.surjInv IsLocalRing.residue_surjective

theorem residue_resSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (x : ResidueField O) : residue O (resSect O x) = x :=
  Function.surjInv_eq _ x

/-- **A-H.5 §1.** The pinned class lift: a section of `proj`, inverting H.100's
`proj_surjective'`. -/
noncomputable def classSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) : Coeff O m N → (Fin m → O) :=
  Function.surjInv (proj_surjective' O m N)

theorem proj_classSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) (c : Coeff O m N) : proj O m N (classSect O m N c) = c :=
  Function.surjInv_eq _ c

/-- **A-H.5 §1.** The recentred frame of a CLASS at the pinned lift pair — the object both
child extractions read. -/
noncomputable def recFrame {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : Coeff O m N) (k : ℕ) (z : ResidueField O) : Polynomial O :=
  (monicPoly (classSect O m N c)).comp (C (π ^ k) * (X + C (resSect O z)))

/-- **A-H.5 §2.** Exact division by `π ^ n`, totalized (junk `0` off the divisibility
locus). -/
noncomputable def divPow {O : Type*} [CommRing O] (π : O) (n : ℕ) (x : O) : O :=
  letI : Decidable (π ^ n ∣ x) := Classical.dec _
  if h : π ^ n ∣ x then h.choose else 0

theorem divPow_spec {O : Type*} [CommRing O] {π : O} {n : ℕ} {x : O} (h : π ^ n ∣ x) :
    x = π ^ n * divPow π n x := by
  unfold divPow
  rw [dif_pos h]
  exact h.choose_spec

/-! ## 2. The α digit vector of a lift pair -/

/-- The α digit vector of the lift pair `(a, w)`: the recentred frame's coefficients divided by
`π ^ (m k)`.  `alphaChild`'s body is this vector at the PINNED pair, projected to the child
window. -/
noncomputable def alphaDigits {O : Type*} [CommRing O] [IsDomain O] (π : O) {m : ℕ}
    (a : Fin m → O) (w : O) (k : ℕ) : Fin m → O :=
  fun j => divPow π (m * k) (((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff (j : ℕ))

/-- **The α factorization at one lift pair.**  If the recentred frame is `π ^ (m k)`-divisible
throughout and `π ^ (m k + 1)`-divisible below the top, then the divided frame is the monic
development of the α digit vector, whose coordinates all lie in `𝔪`.

This is the whole content of clause (i) at a FIXED lift pair; the class-lift binder is handled
separately by `alphaDigits_proj_congr`. -/
theorem alphaFactor {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m k : ℕ} (a : Fin m → O) (w : O)
    (h1 : ∀ j, π ^ (m * k) ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j)
    (h2 : ∀ j < m, π ^ (m * k + 1) ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j) :
    (∀ i, alphaDigits π a w k i ∈ maximalIdeal O) ∧
      (monicPoly a).comp (C (π ^ k) * (X + C w))
        = C (π ^ (m * k)) * monicPoly (alphaDigits π a w k) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set g : Polynomial O := (monicPoly a).comp (C (π ^ k) * (X + C w)) with hg
  -- every coefficient is `π ^ (m k)` times its digit
  have hdig : ∀ j : ℕ, g.coeff j = π ^ (m * k) * divPow π (m * k) (g.coeff j) := fun j =>
    divPow_spec (h1 j)
  refine ⟨fun i => ?_, ?_⟩
  · -- membership: cancel `π ^ (m k)` from `π ^ (m k + 1) ∣ π ^ (m k) * digit`
    have hi := h2 (i : ℕ) i.isLt
    rw [hdig (i : ℕ), pow_succ] at hi
    have hcan : π ∣ divPow π (m * k) (g.coeff (i : ℕ)) :=
      (mul_dvd_mul_iff_left (pow_ne_zero (m * k) hπ0)).1 hi
    have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 (alphaDigits π a w k i)).2
      (by rwa [pow_one])
    rwa [pow_one] at this
  · refine Polynomial.ext fun j => ?_
    rw [coeff_C_mul]
    rcases lt_trichotomy j m with hj | hj | hj
    · rw [monicPoly_coeff_lt _ hj]
      exact hdig j
    · have hlead : (monicPoly (alphaDigits π a w k)).coeff j = 1 := by
        have h' := (monicPoly_monic (alphaDigits π a w k)).coeff_natDegree
        rw [monicPoly_natDegree] at h'
        rw [hj]; exact h'
      rw [hlead, mul_one, hj, hg, coeff_recentre_top hπ0 a k w, ← pow_mul, Nat.mul_comm k m]
    · have hL : g.coeff j = 0 := by
        refine coeff_eq_zero_of_natDegree_lt ?_
        rw [hg, natDegree_recentre hπ0]; omega
      have hR : (monicPoly (alphaDigits π a w k)).coeff j = 0 := by
        refine coeff_eq_zero_of_natDegree_lt ?_
        rw [monicPoly_natDegree]; omega
      rw [hL, hR, mul_zero]

/-- **The class-lift leg (A-H.5 §4's `∀ a`).**  Two lifts of the same level-`N` class have α
digit vectors agreeing at the FULL child window `N − m k`: H.109's `pow_dvd_coeff_comp_sub`
gives `π ^ N` for any recentring, and dividing by `π ^ (m k)` leaves `π ^ (N − m k)`. -/
theorem alphaDigits_proj_congr {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {m N k : ℕ} (hw : m * k ≤ N)
    {a a' : Fin m → O} (haa : proj O m N a = proj O m N a') (w : O)
    (h1 : ∀ j, π ^ (m * k) ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j)
    (h1' : ∀ j, π ^ (m * k) ∣ ((monicPoly a').comp (C (π ^ k) * (X + C w))).coeff j) :
    proj O m (N - m * k) (alphaDigits π a w k) = proj O m (N - m * k) (alphaDigits π a' w k) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  refine funext fun i => ?_
  -- the two recentred frames agree mod `π ^ N`
  have hN : π ^ N ∣ (((monicPoly a).comp (C (π ^ k) * (X + C w)))
      - ((monicPoly a').comp (C (π ^ k) * (X + C w)))).coeff (i : ℕ) :=
    pow_dvd_coeff_comp_sub hπ haa (C (π ^ k) * (X + C w)) (i : ℕ)
  rw [coeff_sub, divPow_spec (h1 (i : ℕ)), divPow_spec (h1' (i : ℕ)), ← mul_sub] at hN
  -- split `π ^ N = π ^ (m k) * π ^ (N − m k)` and cancel
  have hsplit : π ^ N = π ^ (m * k) * π ^ (N - m * k) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at hN
  have hdvd : π ^ (N - m * k) ∣ alphaDigits π a w k i - alphaDigits π a' w k i :=
    (mul_dvd_mul_iff_left (pow_ne_zero (m * k) hπ0)).1 hN
  exact Ideal.Quotient.eq.2
    ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ (N - m * k) _).2 hdvd)

/-! ## 3. H.115 (def half) — the α child at the pinned lift pair -/

set_option linter.unusedVariables false in
/-- **H.115 (def half — REAL BODY, A-H.5 §2).** The recentred, content-divided,
window-truncated α child, extracted at the PINNED lift pair.  α needs no factorization (the
divided frame is already monic), so the child is an explicit division of `recFrame`.  The
subtype guard totalizes the α-membership `b i ∈ 𝔪` without hiding it: clause (i) is FALSE
whenever the junk branch fires, so the membership stays an obligation of clause (i).

`h` is the domain guard and the inference handle for the implicit `{k}`, `{z}`; it is unused in
the body (B77a precedent for the linter silencing). -/
noncomputable def alphaChild {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : IsAlphaState π c k z) : ClusterState O m (N - m * k) :=
  let b : Fin m → O := fun j => divPow π (m * k) ((recFrame π c.1 k z).coeff (j : ℕ))
  letI : Decidable (∀ i, proj O m (N - m * k) b i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)))) :=
    Classical.dec _
  if hb : ∀ i, proj O m (N - m * k) b i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)))
    then ⟨proj O m (N - m * k) b, hb⟩
    else ⟨fun _ => 0, fun _ => Ideal.zero_mem _⟩

/-- The def body, read as the α digit vector at the pinned lift pair (definitional). -/
theorem alphaChild_body {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N k : ℕ} {z : ResidueField O} (c : ClusterState O m N) :
    (fun j : Fin m => divPow π (m * k) ((recFrame π c.1 k z).coeff (j : ℕ)))
      = alphaDigits π (classSect O m N c.1) (resSect O z) k := rfl

/-! ## 4. H.115 (clause i) — the spec, at the pinned centre and at every class lift -/

/-- **H.115 (clause i) [RE-SIGNED: A-H.5 §4].** The extraction is what it says: AT THE
CANONICAL CENTRE `resSect O z` and at every lift `a` of the class, the recentred polynomial is
EXACTLY `π ^ (m k) ·` a monic cluster development lifting the child.

The committed `∀ (a) (w), … residue O w = z → …` form was REFUTED (a centre shift by `d ∈ 𝔪`
moves the child by `m · d ∈ 𝔪 ∖ 𝔪²` while the child is read at window `N − m k ≥ 2`).  At
`a := classSect O m N c.1` this statement is exactly the battery's `extract_child` semantics;
the surviving `∀ a` is licensed by `pow_dvd_coeff_comp_sub`, not by teeth. -/
theorem alphaChild_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O} (hm : 2 ≤ m)
    (hN : 1 ≤ N) (c : ClusterState O m N) (h : IsAlphaState π c k z) :
    ∀ a : Fin m → O, proj O m N a = c.1 →
      ∃ b : Fin m → O, (∀ i, b i ∈ maximalIdeal O) ∧
        (monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C (resSect O z)))
          = Polynomial.C (π ^ (m * k)) * monicPoly b ∧
        proj O m (N - m * k) b = (alphaChild π c h).1 := by
  intro a ha
  obtain ⟨hD, hk, hwin⟩ := alpha_content hπ hm hN h
  obtain ⟨-, -, -, hall⟩ := h.2.2
  have hres : residue O (resSect O z) = z := residue_resSect O z
  -- the divisibility clauses, at an arbitrary lift and at the pinned one
  have hclause : ∀ a' : Fin m → O, proj O m N a' = c.1 →
      (∀ j, π ^ (m * k) ∣
          ((monicPoly a').comp (C (π ^ k) * (X + C (resSect O z)))).coeff j) ∧
        (∀ j < m, π ^ (m * k + 1) ∣
          ((monicPoly a').comp (C (π ^ k) * (X + C (resSect O z)))).coeff j) := by
    intro a' ha'
    obtain ⟨c1, c2, -⟩ := hall a' (resSect O z) ha' hres
    rw [hD] at c1 c2
    exact ⟨c1, c2⟩
  obtain ⟨h1, h2⟩ := hclause a ha
  obtain ⟨h1c, h2c⟩ := hclause (classSect O m N c.1) (proj_classSect O m N c.1)
  obtain ⟨hmem, hfac⟩ := alphaFactor hπ a (resSect O z) h1 h2
  refine ⟨alphaDigits π a (resSect O z) k, hmem, hfac, ?_⟩
  -- the def's junk branch never fires: the pinned digit vector is in `𝔪` coordinatewise
  obtain ⟨hmemc, -⟩ := alphaFactor hπ (classSect O m N c.1) (resSect O z) h1c h2c
  have hguard : ∀ i, proj O m (N - m * k)
      (fun j : Fin m => divPow π (m * k) ((recFrame π c.1 k z).coeff (j : ℕ))) i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k))) := by
    intro i
    rw [alphaChild_body]
    exact Ideal.mem_map_of_mem _ (hmemc i)
  rw [show (alphaChild π c h).1
      = proj O m (N - m * k)
        (fun j : Fin m => divPow π (m * k) ((recFrame π c.1 k z).coeff (j : ℕ))) from by
    simp only [alphaChild, dif_pos hguard], alphaChild_body]
  exact alphaDigits_proj_congr hπ (by omega) (ha.trans (proj_classSect O m N c.1).symm)
    (resSect O z) h1 h1c

end Uniformity.Density.Induction

/-! ## 5. TEETH — the exponent bookkeeping of the shear, reproduced

The battery's `P1(d)` reads, per `(k, z)` slice, an ONTO map from the α slice to the window-`(N
− m k)` state space with every fibre of size `Q ^ (k · c(m))`, `c(m) = m (m − 1) / 2`.  Clause
(i) is the extraction identity behind it; what the numerals below pin is the arithmetic the
identity rests on — the content is `m k`, the child window is `N − m k ≥ 1`, and the fibre
exponent recomposes against H.106's child census to the α-locus exponent of H.114:

`k · c(m) + m (N − m k − 1) = m (N − 1) − k · c(m+1)`.

The plan is the battery's own `part1` plan (`(q, m, N)` rows) crossed with its realized slopes
`k` (`1 ≤ k`, `m k ≤ N − 1`). -/

section NumericAlphaShear

private def clusterCN (m : ℕ) : ℕ := m * (m - 1) / 2

private def alphaPlan : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)]

private def realizedK (m N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)

-- `c(m) = m (m − 1) / 2` and `c(m+1) = m (m + 1) / 2`, as ℕ-exact binomials
#guard (List.range 8).all fun m => clusterCN m == Nat.choose m 2
#guard (List.range 8).all fun m => clusterCN (m + 1) == Nat.choose (m + 1) 2

-- the transport identity: fibre exponent + child census exponent = α-locus exponent
#guard alphaPlan.all fun p =>
  (realizedK p.2.1 p.2.2).all fun k =>
    k * clusterCN p.2.1 + p.2.1 * (p.2.2 - p.2.1 * k - 1)
      == p.2.1 * (p.2.2 - 1) - k * clusterCN (p.2.1 + 1)

-- the child window is never degenerate on a realized slope
#guard alphaPlan.all fun p => (realizedK p.2.1 p.2.2).all fun k => 1 ≤ p.2.2 - p.2.1 * k

-- the α content is `m k`, and it sits strictly inside the window
#guard alphaPlan.all fun p => (realizedK p.2.1 p.2.2).all fun k => p.2.1 * k ≤ p.2.2 - 1

-- the battery's largest live slice: `q = 2, m = 3, N = 6`, slopes `k ∈ {1}`
#guard realizedK 3 6 == [1]
#guard realizedK 2 6 == [1, 2]

end NumericAlphaShear

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.resSect
#print axioms Uniformity.Density.Induction.residue_resSect
#print axioms Uniformity.Density.Induction.classSect
#print axioms Uniformity.Density.Induction.proj_classSect
#print axioms Uniformity.Density.Induction.recFrame
#print axioms Uniformity.Density.Induction.divPow
#print axioms Uniformity.Density.Induction.divPow_spec
#print axioms Uniformity.Density.Induction.alphaDigits
#print axioms Uniformity.Density.Induction.alphaFactor
#print axioms Uniformity.Density.Induction.alphaDigits_proj_congr
#print axioms Uniformity.Density.Induction.alphaChild
#print axioms Uniformity.Density.Induction.alphaChild_body
#print axioms Uniformity.Density.Induction.alphaChild_spec

end AxCheck
