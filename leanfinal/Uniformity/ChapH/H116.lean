/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115
import Uniformity.ChapH.H109

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
* `exists_dividedFrame` — the frame divided by `π ^ D` EXISTS and has the child's digit profile:
  coefficients in `𝔪` below `μ`, a UNIT at `μ` (H.109's three clauses at the pinned lift pair);
* `exists_residue_split` — the divided frame's REDUCTION is `X ^ μ ·` a cofactor with nonzero
  constant term, and the pair is Bézout-coprime (explicit Bézout: `u = C u₀ + X · u.divX` with
  `u₀ ≠ 0` gives `(−C u₀⁻¹ · u.divX) · X + C u₀⁻¹ · u = 1`).

**NOT LANDED — `betaChild_spec` (clause i) is BLOCKED**, and the block is a MISSING LEMMA, not a
defect of the statement.  The blueprint's PROOF step 1a ("exactness of the factorization is
`exists_monic_factorization_finset` over complete `O` on the divided lift") does not apply: that
lemma — and `Uniformity.Hensel.exists_monic_factorization`, the two-factor form — requires
`f.Monic`, and the divided frame is monic exactly when `D = m k`, i.e. only when EVERY root has
valuation `≥ k`.  The generic β frame is NOT monic.  Machine-checked witness, reproduced as
`#guard`s in §4 below: `O = ℤ₅`, `f = (x − 5)(x − 25) ^ 2` (`a = (−3125, 875, −55)`, all in `𝔪`,
so a genuine `ClusterState O 3 7`), `k = 2`, `z = 1`, `μ = 2`.  There `D = 5` while `m k = 6`, the
pinned frame is `15625 Y ^ 3 + 12500 Y ^ 2`, and the divided frame is `5 Y ^ 3 + 4 Y ^ 2` — LEADING
COEFFICIENT `5`, a non-unit.  Its residue reduction is `4 Y ^ 2 = Y ^ μ · 4`, so
`exists_residue_split` fires and the factorization it asks for DOES exist here
(`5 Y ^ 3 + 4 Y ^ 2 = Y ^ 2 · (5 Y + 4)`); what is missing is the general lifting theorem.

**The exact missing input**, stated so a later node can take it as its goal:

> Let `R` be a complete local ring, `f : R[X]` (NOT assumed monic), and
> `f.map (residue R) = g₀ * h₀` with `g₀` MONIC and `IsCoprime g₀ h₀`.  Then `f = g * h` with
> `g` monic, `g.natDegree = g₀.natDegree`, `g.map (residue R) = g₀`, `h.map (residue R) = h₀`.

This is Hensel's lemma in the form that has Weierstrass preparation as its special case
(`h₀` a nonzero constant).  It is **not in mathlib** (checked 2026-08-16 against the pinned
v4.31 tree: `Mathlib/RingTheory/Henselian.lean` carries only the root form and lists the
factorization form in its own `## TODO`; no Weierstrass preparation for polynomials anywhere),
and it is not in this repo: `Uniformity/HenselFactorization.lean` and `Uniformity/MultiHensel.lean`
prove only the MONIC-`f` forms.  The Newton iteration there generalizes (the correction step needs
`δ̄ h̄ + ḡ ε̄ = error` with `deg δ̄ < deg ḡ`, which monicity of `ḡ` alone supplies), but its three
helper lemmas (`exists_solve_field`, `exists_solve_mod`, `exists_solve_step`) are all stated with
BOTH factors monic, so the generalization is a node of its own, not a transcription step.

DEPENDS: H.106 (`ClusterState`), H.108 (`betaContent`, `IsDrainState`), H.109 (`HasChildAt`,
`recCoeffZ`), H.115 / A-H.5 §1 (`resSect`, `classSect`, `recFrame`, `residue_resSect`,
`proj_classSect`), H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`) · landed `monicPoly`, `proj` ·
mathlib `Polynomial.C_dvd_iff_dvd_coeff`, `Polynomial.X_pow_dvd_iff`,
`Polynomial.X_mul_divX_add`, `IsCoprime.pow_left`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` + `π` explicit, every binder INLINE.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
`betaChild_spec` (clause i) and `betaExtract_fiber_card` (clause ii) are NOT in this file.
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

/-- **The frame divided by `π ^ D`, with the child's digit profile.**  H.109's three clauses, read
at the PINNED lift pair `(classSect O m N c.1, resSect O z)`: the frame is `π ^ D`-divisible
throughout, `π ^ (D+1)`-divisible below `μ`, and NOT `π ^ (D+1)`-divisible at `μ`.  So the divided
frame exists over `O` and its coefficients lie in `𝔪` below `μ` and are UNITS at `μ`.

This is the input the missing Hensel form (module docstring) consumes; nothing downstream of it
is claimed here. -/
theorem exists_dividedFrame {π : O} (hπ : Irreducible π) {m N μ k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) :
    ∃ G : Polynomial O, recFrame π c.1 k z = C (π ^ betaContent c k) * G ∧
      (∀ j < μ, G.coeff j ∈ maximalIdeal O) ∧ G.coeff μ ∉ maximalIdeal O := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  obtain ⟨-, -, -, hall⟩ := h
  obtain ⟨c1, c2, c3⟩ := hall (classSect O m N c.1) (resSect O z) (proj_classSect O m N c.1)
    (residue_resSect O z)
  -- the three clauses, read at the pinned frame (`recFrame` is that composite, by definition)
  have c1' : ∀ j, π ^ betaContent c k ∣ (recFrame π c.1 k z).coeff j := c1
  have c2' : ∀ j < μ, π ^ (betaContent c k + 1) ∣ (recFrame π c.1 k z).coeff j := c2
  have c3' : ¬ π ^ (betaContent c k + 1) ∣ (recFrame π c.1 k z).coeff μ := c3
  -- the frame is `C (π ^ D)`-divisible, so the divided frame exists
  have hCdvd : (C (π ^ betaContent c k) : Polynomial O) ∣ recFrame π c.1 k z :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).2 c1'
  obtain ⟨G, hG⟩ := hCdvd
  have hcoeff : ∀ j, (recFrame π c.1 k z).coeff j = π ^ betaContent c k * G.coeff j := by
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

end Divided

end Uniformity.Density.Induction

/-! ## 3. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.betaChild
#print axioms Uniformity.Density.Induction.exists_dividedFrame
#print axioms Uniformity.Density.Induction.exists_residue_split

end AxCheck

/-! ## 4. The BLOCKER witness, reproduced as numerals

The blueprint's PROOF step 1a routes existence through `exists_monic_factorization_finset`, whose
hypothesis is `f.Monic`.  The divided frame is monic exactly when `D = m k`.  The cell below is a
genuine β state where `D < m k`, so the cited lemma cannot fire; the arithmetic is reproduced with
H.109's own recentring model `recCoeffZ` (same expansion, ℤ-valued).

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

-- THE BLOCKER: the divided frame is `5 Y ^ 3 + 4 Y ^ 2` — leading coefficient `5`, NOT a unit,
-- so `exists_monic_factorization{,_finset}` (both require `f.Monic`) cannot be applied to it
#guard (List.range 4).map (fun j =>
    recCoeffZ 3 2 5 1 aBeta j / (5 ^ 5)) == [0, 0, 4, 5]
#guard ¬ ((recCoeffZ 3 2 5 1 aBeta 3 / (5 ^ 5)) == 1)

-- the factorization the missing lemma must produce DOES exist at this cell:
-- `5 Y ^ 3 + 4 Y ^ 2 = Y ^ 2 · (5 Y + 4)`, with `Y ^ 2` monic of degree `μ = 2`
#guard ([(0 : ℤ), 1, 2, -1, 5]).all fun y =>
  5 * y ^ 3 + 4 * y ^ 2 == y ^ 2 * (5 * y + 4)

end BlockerWitness
