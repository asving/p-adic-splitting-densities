/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115
import Uniformity.ChapH.H109
import Uniformity.ChapH.H116h

/-!
# Uniformity.ChapH.H116 — the β extraction at the capped window (N-2c), def half

**Chapter H, NODE H.116** (`blueprint/CHAP-H_general_induction.md` §17.2, re-signed 2026-08-16 by
AMENDMENT A-H.5; DECISION D-H17.2's window-as-argument design unaffected).

`betaChild π c h M` is the `(μ, k, z)`-child of a state read at an EXPLICIT window `M`, extracted
at the PINNED lift pair (A-H.5 §1: `classSect O m N c.1` and `resSect O z`, through `recFrame`).
Unlike α — a division formula, `ChapH/H115.lean` — β needs a FACTORIZATION, so the body is a
DEFINITION BY DESCRIPTION: the child state whose lift `b` (degree `μ`, coefficients in `𝔪`)
exhibits the pinned frame's `π ^ D`-factorization, `D = betaContent c k`.

## What this file lands, and what it does NOT

LANDED (this file):

* `betaChild` — the def half, REAL BODY, signature byte-identical to the re-signed stub;
* `exists_dividedFrame_at` / `exists_dividedFrame` — the frame divided by `π ^ D` EXISTS and has
  the child's digit profile: coefficients in `𝔪` below `μ`, a UNIT at `μ` (H.109's three clauses),
  at ANY class lift and at the pinned one;
* `exists_residue_split` — the divided frame's REDUCTION is `X ^ μ ·` a cofactor with nonzero
  constant term, and the pair is Bézout-coprime (explicit Bézout: `u = C u₀ + X · u.divX` with
  `u₀ ≠ 0` gives `(−C u₀⁻¹ · u.divX) · X + C u₀⁻¹ · u = 1`);
* `monicPoly_map_residue` — a cluster development reduces to `X ^ μ`;
* `monicFactor_congr_of_pow_dvd_sub` — PROOF 1b, fixed-centre uniqueness in quantitative form;
* **`betaChild_spec` — CLAUSE (i), statement byte-identical to the A-H.5 re-signed stub.**

`betaExtract_fiber_card` (clause ii) is NOT in this file.

## The former blocker, and how it was removed

The blueprint's PROOF step 1a routed existence through `exists_monic_factorization_finset`, whose
hypothesis is `f.Monic`; so does `Uniformity.Hensel.exists_monic_factorization`, the two-factor
form.  The divided frame is monic exactly when `D = m k`, i.e. only when EVERY root has valuation
`≥ k`, so the generic β frame is NOT monic.  Machine-checked witness, still reproduced as
`#guard`s in §5 below: `O = ℤ₅`, `f = (x − 5)(x − 25) ^ 2` (`a = (−3125, 875, −55)`, all in `𝔪`,
so a genuine `ClusterState O 3 7`), `k = 2`, `z = 1`, `μ = 2`.  There `D = 5` while `m k = 6`, the
pinned frame is `15625 Y ^ 3 + 12500 Y ^ 2`, and the divided frame is `5 Y ^ 3 + 4 Y ^ 2` — LEADING
COEFFICIENT `5`, a non-unit; the factorization the lemma must produce is `Y ^ 2 · (5 Y + 4)`.

The missing input was:

> Let `R` be a complete local ring, `f : R[X]` (NOT assumed monic), and
> `f.map (residue R) = g₀ * h₀` with `g₀` MONIC and `IsCoprime g₀ h₀`.  Then `f = g * h` with
> `g` monic, `g.natDegree = g₀.natDegree`, `g.map (residue R) = g₀`, `h.map (residue R) = h₀`.

Hensel's lemma in the form that has Weierstrass preparation as its special case; not in mathlib
(pinned v4.31 `Mathlib/RingTheory/Henselian.lean` has the root form only and lists this one in
its own `## TODO`).  It is now LANDED as `Uniformity.Hensel.exists_monic_factorization_of_monic_left`
in **`ChapH/H116h.lean`** (HELPER NODE H.116h), by generalizing `HenselFactorization.lean`'s three
Newton helpers to a non-monic `h₀` with the total degree carried as an explicit budget.

## The proof of clause (i), in one paragraph

**1a EXISTENCE.**  `exists_dividedFrame_at` (any lift, pinned centre) → `exists_residue_split`
→ H.116h's non-monic Hensel → `exists_monicPoly_eq` turns the monic degree-`μ` factor into a
coefficient vector `b`, whose entries are in `𝔪` because the factor reduces to `X ^ μ`.  At the
PINNED lift this witnesses the description's branch condition, so `betaChild` is on its real
branch.  **1b UNIQUENESS AT A FIXED CENTRE.**  `monicFactor_congr_of_pow_dvd_sub` runs the
residual Bézout obstruction one digit at a time: the arbitrary lift's frame and the pinned frame
agree to `π ^ N` (H.109's `pow_dvd_coeff_comp_sub`), hence their `π ^ D`-quotients agree to
`π ^ (N − D)` (`D ≤ N − 1` by H.108's `betaContent_le` on a non-drain state), and then the two
monic degree-`μ` factors agree to `π ^ (N − D)` — which IS equality of the child classes at the
child window.

DEPENDS: H.106 (`ClusterState`), H.108 (`betaContent`, `IsDrainState`, `betaContent_le`), H.109
(`HasChildAt`, `pow_dvd_coeff_comp_sub`, `recCoeffZ`), H.115 / A-H.5 §1 (`resSect`, `classSect`,
`recFrame`, `residue_resSect`, `proj_classSect`), H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`),
**H.116h** (`exists_monic_factorization_of_monic_left`, `degree_sub_lt_of_monic_of_natDegree_eq`)
· landed `monicPoly`, `proj`, `exists_monicPoly_eq`, `monicPoly_coeff_lt` · mathlib
`Polynomial.C_dvd_iff_dvd_coeff`, `Polynomial.X_pow_dvd_iff`, `Polynomial.X_mul_divX_add`,
`Polynomial.eq_zero_of_dvd_of_degree_lt`, `IsCoprime.pow_left`, `IsCoprime.dvd_of_dvd_mul_right`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` + `π` explicit, every binder INLINE.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. H.116 (def half) — the β child by description at the pinned lift pair -/

set_option linter.unusedVariables false in
/-- **H.116 (def half — REAL BODY, A-H.5 §3).** The `(μ, k, z)`-child of a state, read at an
EXPLICIT window `M` (DECISION D-H17.2: the window is an argument, so genre-level statements avoid
dependent-index casts; the genuine child is at `M = N − betaContent c k`).

Unlike α (a division formula) β needs a FACTORIZATION, so the body is a DEFINITION BY DESCRIPTION
at the pinned centre: the child state whose lift `b` (degree `μ`, coefficients in `𝔪`) exhibits
the pinned frame's `π ^ D`-factorization.  Its two obligations are node-side: EXISTENCE and
UNIQUENESS AT A FIXED CENTRE.  Until existence is proved the description sits on its junk branch
and clause (i) is false — nothing is smuggled past the `if`. -/
noncomputable def betaChild {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) {m N μ k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) (M : ℕ) : ClusterState O μ M :=
  letI : Decidable (∃ d : ClusterState O μ M, ∃ (b : Fin μ → O) (H' : Polynomial O),
        (∀ i, b i ∈ maximalIdeal O) ∧
        recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ M b = d.1) := Classical.dec _
  if hb : ∃ d : ClusterState O μ M, ∃ (b : Fin μ → O) (H' : Polynomial O),
        (∀ i, b i ∈ maximalIdeal O) ∧
        recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ M b = d.1
    then hb.choose
    else ⟨fun _ => 0, fun _ => Ideal.zero_mem _⟩

/-! ## 2. The divided frame, and its digit profile -/

section Divided

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The frame divided by `π ^ D`, with the child's digit profile — AT ANY LIFT of the class.**
H.109's three clauses, read at the lift pair `(a, resSect O z)`: the frame is `π ^ D`-divisible
throughout, `π ^ (D+1)`-divisible below `μ`, and NOT `π ^ (D+1)`-divisible at `μ`.  So the divided
frame exists over `O` and its coefficients lie in `𝔪` below `μ` and are UNITS at `μ`.

The centre stays PINNED at `resSect O z` (A-H.5); only the class lift is quantified, which is the
leg `HasChildAt`'s own `∀`-lift clause licenses. -/
theorem exists_dividedFrame_at {π : O} (hπ : Irreducible π) {m N μ k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) (a : Fin m → O)
    (ha : proj O m N a = c.1) :
    ∃ G : Polynomial O,
      (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z))) = C (π ^ betaContent c k) * G ∧
      (∀ j < μ, G.coeff j ∈ maximalIdeal O) ∧ G.coeff μ ∉ maximalIdeal O := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  obtain ⟨-, -, -, hall⟩ := h
  obtain ⟨c1, c2, c3⟩ := hall a (resSect O z) ha (residue_resSect O z)
  -- the three clauses, at the lift pair `(a, resSect O z)`
  set F : Polynomial O := (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z))) with hF
  have c1' : ∀ j, π ^ betaContent c k ∣ F.coeff j := c1
  have c2' : ∀ j < μ, π ^ (betaContent c k + 1) ∣ F.coeff j := c2
  have c3' : ¬ π ^ (betaContent c k + 1) ∣ F.coeff μ := c3
  -- the frame is `C (π ^ D)`-divisible, so the divided frame exists
  have hCdvd : (C (π ^ betaContent c k) : Polynomial O) ∣ F :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).2 c1'
  obtain ⟨G, hG⟩ := hCdvd
  have hcoeff : ∀ j, F.coeff j = π ^ betaContent c k * G.coeff j := by
    intro j
    rw [hG, coeff_C_mul]
  -- `π` divides the divided coefficients below `μ`, and does not at `μ`
  have hmem : ∀ x : O, π ∣ x → x ∈ maximalIdeal O := by
    intro x hx
    have h1 := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).2 (by rwa [pow_one])
    rwa [pow_one] at h1
  have hdvd : ∀ x : O, x ∈ maximalIdeal O → π ∣ x := by
    intro x hx
    have h1 := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h1
  refine ⟨G, hG, fun j hj => hmem _ ?_, fun hcon => c3' ?_⟩
  · have h2 := c2' j hj
    rw [hcoeff j, pow_succ] at h2
    exact (mul_dvd_mul_iff_left (pow_ne_zero (betaContent c k) hπ0)).1 h2
  · rw [hcoeff μ, pow_succ]
    exact mul_dvd_mul_left _ (hdvd _ hcon)

/-- **The frame divided by `π ^ D`, at the PINNED lift pair.**  `exists_dividedFrame_at` read at
`classSect O m N c.1` — `recFrame` is exactly that composite, by definition. -/
theorem exists_dividedFrame {π : O} (hπ : Irreducible π) {m N μ k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) :
    ∃ G : Polynomial O, recFrame π c.1 k z = C (π ^ betaContent c k) * G ∧
      (∀ j < μ, G.coeff j ∈ maximalIdeal O) ∧ G.coeff μ ∉ maximalIdeal O :=
  exists_dividedFrame_at hπ c h (classSect O m N c.1) (proj_classSect O m N c.1)

/-- **The residue-level split.**  The divided frame reduces to `X ^ μ ·` a cofactor with NONZERO
constant term, and that pair is Bézout-coprime — the residue-level datum every Hensel split
consumes.  The Bézout witness is explicit: writing `u = C u₀ + X · u.divX` with `u₀ ≠ 0`,
`(−C u₀⁻¹ · u.divX) · X + C u₀⁻¹ · u = 1`. -/
theorem exists_residue_split {G : Polynomial O} {μ : ℕ}
    (hlt : ∀ j < μ, G.coeff j ∈ maximalIdeal O) (htop : G.coeff μ ∉ maximalIdeal O) :
    ∃ u : Polynomial (ResidueField O), G.map (residue O) = X ^ μ * u ∧ u.coeff 0 ≠ 0 ∧
      IsCoprime (X ^ μ : Polynomial (ResidueField O)) u := by
  classical
  have hvanish : ∀ j < μ, (G.map (residue O)).coeff j = 0 := by
    intro j hj
    rw [coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hlt j hj)
  obtain ⟨u, hu⟩ : (X : Polynomial (ResidueField O)) ^ μ ∣ G.map (residue O) :=
    Polynomial.X_pow_dvd_iff.2 hvanish
  have hu0 : u.coeff 0 ≠ 0 := by
    have hcm : (G.map (residue O)).coeff μ = u.coeff 0 := by
      rw [hu]
      simpa using Polynomial.coeff_X_pow_mul u μ 0
    rw [coeff_map] at hcm
    intro hz
    exact htop (Ideal.Quotient.eq_zero_iff_mem.1 (hcm.trans hz))
  refine ⟨u, hu, hu0, IsCoprime.pow_left ?_⟩
  refine ⟨-(C (u.coeff 0)⁻¹ * u.divX), C (u.coeff 0)⁻¹, ?_⟩
  have hsplit : X * u.divX + C (u.coeff 0) = u := X_mul_divX_add u
  have hinv : C (u.coeff 0)⁻¹ * C (u.coeff 0) = (1 : Polynomial (ResidueField O)) := by
    rw [← C_mul, inv_mul_cancel₀ hu0, map_one]
  linear_combination (-(C (u.coeff 0)⁻¹)) * hsplit + hinv

/-! ## 2b. PROOF 1b — uniqueness at a FIXED centre -/

/-- **A cluster development reduces to `X ^ μ`.**  A monic degree-`μ` development whose
coefficient vector lies in `𝔪` has residue reduction exactly `X ^ μ` — the residue-level left
factor every β split is taken along. -/
theorem monicPoly_map_residue {μ : ℕ} {b : Fin μ → O} (hb : ∀ i, b i ∈ maximalIdeal O) :
    (monicPoly b).map (residue O) = X ^ μ := by
  refine Polynomial.ext fun j => ?_
  rw [coeff_map, coeff_X_pow]
  rcases lt_trichotomy j μ with hj | hj | hj
  · rw [monicPoly_coeff_lt b hj, if_neg (Nat.ne_of_lt hj)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hb _)
  · have h1 : (monicPoly b).coeff j = 1 := by
      have h2 := (monicPoly_monic b).coeff_natDegree
      rw [monicPoly_natDegree] at h2
      rw [hj]; exact h2
    rw [h1, if_pos hj, map_one]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      if_neg (by omega), map_zero]

/-- **PROOF 1b — FIXED-CENTRE UNIQUENESS, in its quantitative form.**  Two monic degree-`μ` left
factors whose products agree to level `π ^ s` agree to level `π ^ s` themselves, provided one of
them reduces to `X ^ μ` and the other's cofactor is residually coprime to `X ^ μ`.

The mechanism is the residual Bézout obstruction run ONE DIGIT AT A TIME.  If `A − A' = π ^ t · δ`
and `B − B' = π ^ t · ε`, then `π ^ (t+1) ∣ A B − A' B'` forces `δ̄ · B̄ + X ^ μ · ε̄ = 0` in the
residue polynomial ring.  Coprimality gives `X ^ μ ∣ δ̄`; monicity of `A, A'` at the SAME degree
gives `deg δ < μ`; the two together give `δ̄ = 0`, hence `X ^ μ · ε̄ = 0` and `ε̄ = 0` — one more
digit on BOTH corrections.  This is H.102's `InjOn` route, stated so that it also covers the
CLASS-lift leg: the two factorizations need not be of the same polynomial, only of polynomials
agreeing to level `π ^ s`. -/
theorem monicFactor_congr_of_pow_dvd_sub {π : O} (hπ : Irreducible π) {μ : ℕ}
    {A A' B B' : Polynomial O} (hA : A.Monic) (hA' : A'.Monic)
    (hAd : A.natDegree = μ) (hA'd : A'.natDegree = μ)
    (hA'r : A'.map (residue O) = X ^ μ)
    (hcop : IsCoprime (X ^ μ : Polynomial (ResidueField O)) (B.map (residue O)))
    {s : ℕ} (hs : ∀ j, π ^ s ∣ (A * B - A' * B').coeff j) :
    ∀ j, π ^ s ∣ (A - A').coeff j := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmem : ∀ x : O, π ∣ x → residue O x = 0 := by
    intro x hx
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have h1 := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).2 (by rwa [pow_one])
    rwa [pow_one] at h1
  have hdvdof : ∀ x : O, residue O x = 0 → π ∣ x := by
    intro x hx
    have h1 := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1
      (by rw [pow_one]; exact Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rwa [pow_one] at h1
  -- the difference of two monic degree-`μ` polynomials drops degree
  have hABdeg : (A - A').degree < (μ : WithBot ℕ) := by
    have h1 := Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hA hA'
      (hAd.trans hA'd.symm)
    rwa [hAd] at h1
  have key : ∀ t, t ≤ s →
      (∀ j, π ^ t ∣ (A - A').coeff j) ∧ (∀ j, π ^ t ∣ (B - B').coeff j) := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨fun j => by simp, fun j => by simp⟩
    | succ t ih =>
      intro hts
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨δ, hδ⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ t) (A - A')).2 h1
      obtain ⟨ε, hε⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ t) (B - B')).2 h2
      have hid : A * B - A' * B' = C (π ^ t) * (δ * B + A' * ε) := by
        linear_combination B * hδ + A' * hε
      have hdvd : ∀ j, π ∣ (δ * B + A' * ε).coeff j := by
        intro j
        have h4 : π ^ (t + 1) ∣ (A * B - A' * B').coeff j :=
          dvd_trans (pow_dvd_pow π hts) (hs j)
        rw [hid, coeff_C_mul, pow_succ] at h4
        exact (mul_dvd_mul_iff_left (pow_ne_zero t hπ0)).1 h4
      -- the residual Bézout obstruction
      have hres : (δ.map (residue O)) * (B.map (residue O))
          + (X : Polynomial (ResidueField O)) ^ μ * (ε.map (residue O)) = 0 := by
        have h5 : (δ * B + A' * ε).map (residue O) = 0 := by
          refine Polynomial.ext fun j => ?_
          rw [coeff_map, coeff_zero]
          exact hmem _ (hdvd j)
        rwa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hA'r] at h5
      have hdvdδ : (X : Polynomial (ResidueField O)) ^ μ ∣ δ.map (residue O) :=
        hcop.dvd_of_dvd_mul_right ⟨-(ε.map (residue O)), by linear_combination hres⟩
      have hδdeg : δ.degree < (μ : WithBot ℕ) := by
        rw [Polynomial.degree_lt_iff_coeff_zero]
        intro n hn
        have h6 : (A - A').coeff n = 0 :=
          coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hABdeg (by exact_mod_cast hn))
        have h7 : π ^ t * δ.coeff n = 0 := by
          rw [← coeff_C_mul, ← hδ]; exact h6
        exact (mul_eq_zero.1 h7).resolve_left (pow_ne_zero t hπ0)
      have hδz : δ.map (residue O) = 0 := by
        refine Polynomial.eq_zero_of_dvd_of_degree_lt hdvdδ ?_
        rw [degree_X_pow]
        exact lt_of_le_of_lt degree_map_le hδdeg
      have hεz : ε.map (residue O) = 0 := by
        have h8 : (X : Polynomial (ResidueField O)) ^ μ * (ε.map (residue O)) = 0 := by
          rw [hδz] at hres; simpa using hres
        exact (mul_eq_zero.1 h8).resolve_left (pow_ne_zero μ X_ne_zero)
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have h9 : π ∣ δ.coeff j := by
          refine hdvdof _ ?_
          have h10 := congrArg (fun p => Polynomial.coeff p j) hδz
          simpa [coeff_map] using h10
        rw [show (A - A').coeff j = π ^ t * δ.coeff j from by rw [hδ, coeff_C_mul], pow_succ]
        exact mul_dvd_mul_left _ h9
      · have h9 : π ∣ ε.coeff j := by
          refine hdvdof _ ?_
          have h10 := congrArg (fun p => Polynomial.coeff p j) hεz
          simpa [coeff_map] using h10
        rw [show (B - B').coeff j = π ^ t * ε.coeff j from by rw [hε, coeff_C_mul], pow_succ]
        exact mul_dvd_mul_left _ h9
  exact (key s le_rfl).1

end Divided

/-! ## 3. H.116 (clause i) — the spec, at the pinned centre and at every class lift -/

/-- **H.116 (clause i) [RE-SIGNED: A-H.5 §4].** The extraction factors every lift of the class
AT THE CANONICAL CENTRE `resSect O z`: recentred = `π^D ·` (monic degree-`μ` cluster lift of the
child) `×` (co-factor), exactly.

The committed `∀ (a) (w), … residue O w = z → …` form was REFUTED: at `O = ℤ₅`,
`f = (x−5)²(x−10)` (`m = 3, N = 6, k = 1, z = 1, μ = 2`, so `D = 3`, window 3) the centres
`w = 1` and `w = 6` give the children `(0, 0)` and `(25, 10)` mod `5³`, each the UNIQUE monic
degree-`μ` factor with coefficients in `𝔪` at its centre.  `∀ a` survives (H.109's
`pow_dvd_coeff_comp_sub` + H.102's `InjOn` at window `N − D`).

PROOF, as booked at the node.  **1a EXISTENCE** — `exists_dividedFrame_at` divides the recentred
frame by `π ^ D` exactly; `exists_residue_split` reads its reduction as `X ^ μ ·` a cofactor with
nonzero constant term, Bézout-coprime to `X ^ μ`; `H116h`'s
`Uniformity.Hensel.exists_monic_factorization_of_monic_left` lifts that split over complete `O`
— the NON-MONIC Hensel form, which is what the divided frame needs (it is monic only when
`D = m k`).  **1b UNIQUENESS AT A FIXED CENTRE** — `monicFactor_congr_of_pow_dvd_sub`, run at
`s = N − D`: the arbitrary lift's frame and the pinned frame agree to `π ^ N`
(`pow_dvd_coeff_comp_sub`), so after dividing by `π ^ D` they agree to `π ^ (N − D)`, and the
monic degree-`μ` factors then agree to `π ^ (N − D)` — which is exactly equality of the child
CLASSES at the child window. -/
theorem betaChild_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m N μ k : ℕ} {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) (h0 : ¬ IsDrainState c) :
    ∀ a : Fin m → O, proj O m N a = c.1 →
      ∃ (b : Fin μ → O) (H' : Polynomial O), (∀ i, b i ∈ maximalIdeal O) ∧
        (monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C (resSect O z)))
          = Polynomial.C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ (N - betaContent c k) b
          = (betaChild π c h (N - betaContent c k)).1 := by
  classical
  -- the content is VISIBLE in the window (H.108), so `D + (N − D) = N` on the nose
  have hm1 : 1 ≤ m := by omega
  have hDN : betaContent c k ≤ N - 1 := betaContent_le hm1 hN c h0 k
  have hDsum : betaContent c k + (N - betaContent c k) = N := by omega
  -- STEP 1a: the split, at an ARBITRARY lift of the class, at the pinned centre
  have split : ∀ a : Fin m → O, proj O m N a = c.1 →
      ∃ (b : Fin μ → O) (H' : Polynomial O), (∀ i, b i ∈ maximalIdeal O) ∧
        (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
          = C (π ^ betaContent c k) * (monicPoly b * H') ∧
        IsCoprime (X ^ μ : Polynomial (ResidueField O)) (H'.map (residue O)) := by
    intro a ha
    obtain ⟨G, hGeq, hGlt, hGtop⟩ := exists_dividedFrame_at hπ c h a ha
    obtain ⟨u, hu, -, hucop⟩ := exists_residue_split hGlt hGtop
    obtain ⟨g, H', hgm, hGgh, hgd, hgr, hH'r⟩ :=
      Uniformity.Hensel.exists_monic_factorization_of_monic_left (monic_X_pow μ) hucop hu
    obtain ⟨b, hbeq⟩ := Uniformity.Density.exists_monicPoly_eq hgm
      (by rw [hgd, natDegree_X_pow])
    refine ⟨b, H', ?_, ?_, ?_⟩
    · intro i
      have hc : g.coeff (i : ℕ) = b i := by rw [← hbeq, monicPoly_coeff_lt b i.isLt]
      have hz0 : residue O (g.coeff (i : ℕ)) = 0 := by
        have h10 := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hgr
        simp only [coeff_map, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt)] at h10
        exact h10
      rw [← hc]
      exact Ideal.Quotient.eq_zero_iff_mem.1 hz0
    · rw [hGeq, hbeq, hGgh]
    · rw [hH'r]; exact hucop
  -- the description's branch condition is MET: the pinned split witnesses it
  obtain ⟨b₀, H₀, hb₀mem, hb₀eq, -⟩ := split (classSect O m N c.1) (proj_classSect O m N c.1)
  have hb : ∃ d : ClusterState O μ (N - betaContent c k), ∃ (b : Fin μ → O) (H' : Polynomial O),
      (∀ i, b i ∈ maximalIdeal O) ∧
      recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b * H') ∧
      proj O μ (N - betaContent c k) b = d.1 :=
    ⟨⟨proj O μ (N - betaContent c k) b₀, fun i => Ideal.mem_map_of_mem _ (hb₀mem i)⟩,
      b₀, H₀, hb₀mem, hb₀eq, rfl⟩
  have hbval : betaChild π c h (N - betaContent c k) = hb.choose := by
    simp only [betaChild, dif_pos hb]
  obtain ⟨b₁, H₁, hb₁mem, hb₁eq, hb₁proj⟩ := hb.choose_spec
  -- STEP 1b: the class-lift leg, through fixed-centre uniqueness at level `π ^ (N − D)`
  intro a ha
  obtain ⟨ba, Ha, hbamem, hbaeq, hbacop⟩ := split a ha
  refine ⟨ba, Ha, hbamem, hbaeq, ?_⟩
  rw [hbval, ← hb₁proj]
  have hπN : π ^ N = π ^ betaContent c k * π ^ (N - betaContent c k) := by
    rw [← pow_add, hDsum]
  have hdiff : ∀ j, π ^ (N - betaContent c k) ∣
      (monicPoly ba * Ha - monicPoly b₁ * H₁).coeff j := by
    intro j
    have h1 : π ^ N ∣ ((monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
        - (monicPoly (classSect O m N c.1)).comp (C (π ^ k) * (X + C (resSect O z)))).coeff j :=
      pow_dvd_coeff_comp_sub hπ (ha.trans (proj_classSect O m N c.1).symm) _ j
    rw [hbaeq, show (monicPoly (classSect O m N c.1)).comp (C (π ^ k) * (X + C (resSect O z)))
        = C (π ^ betaContent c k) * (monicPoly b₁ * H₁) from hb₁eq, ← mul_sub, coeff_C_mul,
      hπN] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 h1
  have huniq := monicFactor_congr_of_pow_dvd_sub hπ (monicPoly_monic ba) (monicPoly_monic b₁)
    (monicPoly_natDegree ba) (monicPoly_natDegree b₁) (monicPoly_map_residue hb₁mem)
    hbacop hdiff
  refine funext fun i => ?_
  refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ _ _).2 ?_)
  have h3 := huniq (i : ℕ)
  rwa [coeff_sub, monicPoly_coeff_lt ba i.isLt, monicPoly_coeff_lt b₁ i.isLt] at h3

end Uniformity.Density.Induction

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.betaChild
#print axioms Uniformity.Density.Induction.exists_dividedFrame_at
#print axioms Uniformity.Density.Induction.exists_dividedFrame
#print axioms Uniformity.Density.Induction.exists_residue_split
#print axioms Uniformity.Density.Induction.monicPoly_map_residue
#print axioms Uniformity.Density.Induction.monicFactor_congr_of_pow_dvd_sub
#print axioms Uniformity.Density.Induction.betaChild_spec

end AxCheck

/-! ## 5. The FORMER-BLOCKER witness, reproduced as numerals

The blueprint's PROOF step 1a routed existence through `exists_monic_factorization_finset`, whose
hypothesis is `f.Monic`.  The divided frame is monic exactly when `D = m k`.  The cell below is a
genuine β state where `D < m k`, so the cited lemma cannot fire — which is WHY clause (i) now runs
through H.116h's non-monic Hensel form instead.  The cell is retained as a standing regression on
that design choice; the arithmetic is reproduced with H.109's own recentring model `recCoeffZ`
(same expansion, ℤ-valued).

`O = ℤ₅`, `f = (x − 5)(x − 25) ^ 2 = x ^ 3 − 55 x ^ 2 + 875 x − 3125`, so `m = 3`, take `N = 7`;
every coefficient lies in `𝔪` (the state is a genuine `ClusterState`), the roots are `5, 25, 25`.
At `k = 2`, `z = 1` the two roots `25` collide: `μ = 2`.  Content
`D = min(5 + 0, 3 + 2, 1 + 4, 3·2) = 5 < 6 = m k`. -/

section BlockerWitness

/-- `a = (−3125, 875, −55)` — the coefficient vector of `(x − 5)(x − 25) ^ 2`. -/
private def aBeta : ℕ → ℤ := fun i => if i = 0 then -3125 else if i = 1 then 875 else -55

/-- `v₅` of a nonzero integer, bounded by the window. -/
private def val5 (cap : ℕ) (x : ℤ) : ℕ :=
  ((List.range (cap + 1)).filter fun t => decide (x % (5 ^ t) = 0)).foldl max 0

-- the state is a genuine cluster state: every coefficient is in `𝔪` (valuation ≥ 1)
#guard (List.range 3).all fun i => 1 ≤ val5 7 (aBeta i)

-- the capped content at `k = 2` is `D = 5`, strictly below `m k = 6`
#guard [val5 7 (aBeta 0) + 0 * 2, val5 7 (aBeta 1) + 1 * 2, val5 7 (aBeta 2) + 2 * 2, 3 * 2]
  == [5, 5, 5, 6]

-- the pinned frame `f (5 ^ 2 (Y + 1)) = 15625 Y ^ 3 + 12500 Y ^ 2` (H.109's recentring model)
#guard (List.range 4).map (recCoeffZ 3 2 5 1 aBeta)
  == [0, 0, 12500, 15625]

-- the child pattern at `μ = 2`: `π ^ (D+1) = 5 ^ 6` divides the coefficients below `2` and not at `2`
#guard (List.range 2).all fun j =>
  recCoeffZ 3 2 5 1 aBeta j % (5 ^ 6) == 0
#guard ¬ (recCoeffZ 3 2 5 1 aBeta 2 % (5 ^ 6) == 0)
#guard recCoeffZ 3 2 5 1 aBeta 2 % (5 ^ 5) == 0

-- THE FORMER BLOCKER: the divided frame is `5 Y ^ 3 + 4 Y ^ 2` — leading coefficient `5`, NOT a
-- unit, so `exists_monic_factorization{,_finset}` (both require `f.Monic`) cannot be applied to it
#guard (List.range 4).map (fun j =>
    recCoeffZ 3 2 5 1 aBeta j / (5 ^ 5)) == [0, 0, 4, 5]
#guard ¬ ((recCoeffZ 3 2 5 1 aBeta 3 / (5 ^ 5)) == 1)

-- the factorization H.116h's non-monic Hensel form produces at this cell:
-- `5 Y ^ 3 + 4 Y ^ 2 = Y ^ 2 · (5 Y + 4)`, with `Y ^ 2` monic of degree `μ = 2`
#guard ([(0 : ℤ), 1, 2, -1, 5]).all fun y =>
  5 * y ^ 3 + 4 * y ^ 2 == y ^ 2 * (5 * y + 4)

end BlockerWitness
