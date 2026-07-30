/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L3_DIV

/-!
# HC1.D7_digD_mul — the DIG homomorphism (the TWISTED law, anchors on both sides)

moves_ref: MOVES 1385–1400 (§B2⁵.1, the aligned digit and the carry rule) + 2305–2315
(Lemma DIV(iii): dig′(R_dev) = dig′(B)·dig′(B″), the ψ-adic division identity — the
proof engine, on disk as `L3_DIV`). deps: DefsD (`cmul` IS the cocycle product:
`(x*y) τ = Σ x ρ · y (τ−ρ) · z̄^carryExp` — checked), Moves `L3_DIV` (clean, verified
on disk). difficulty: medium.

## The note's display (MOVES 1385–1396, quoted)

For B with absolute data (a(B), R_anch(B)) at the increment side (e, h, ψ): write
a(B) = e·q(B) + ρ(B), 0 ≤ ρ(B) < e, and

  DIG(B) := ( ρ(B) , z̄^{q(B)}·[R_anch(B)] ) ∈ (ℤ/e) × F_{r+1}ˣ ;

with κ := ⌊(ρ(B) + ρ(B″))/e⌋ ∈ {0, 1},

  ρ(R_dev) = ρ(B) + ρ(B″) − e·κ,   z̄-part(R_dev) = z̄^{κ}·z̄-part(B)·z̄-part(B″),

i.e. DIG is a homomorphism into the group (ℤ/e) ⋉_{z̄} F_{r+1}ˣ — the TWISTED target
(the central extension by the carry cocycle), NOT plain multiplicativity. *Proof:* the
ψ_r-adic division identity of B2′.3(iii) applied to the ALIGNED absolute residuals
(the z-offsets now included on both sides; the (P6) absolute vectors make the
alignment well-defined), plus the anchor addition. [MOVES 1390–1400]

## REV (adjudication 2026-07-28): the anchors ride explicitly

The E-phase statement carried the digit shapes as bare `IsMonomialUnit` hypotheses, so
the three anchors were free choice-data tied only through the field-level identity
dig′(R_dev) = dig′(B)·dig′(B″). Against that statement the DIG law is underdetermined:
with d := (a(B) + a(B″)) − a(R_dev) the free anchor discrepancy, the stated equation
holds iff `e_b ∣ d ∧ z̄^{d − d/e_b} = 1` — the prover's re-derived counterexample
condition (the pass-6/7 counterexample that forced the twist, MOVES 1388). Adjudicated
restatement: the (S5)-monomial hypotheses now carry their z-offsets EXPLICITLY
("the z-offsets now included on both sides") and the remainder's hypothesis is pinned
at the SUM anchor kB + kB″ ("plus the anchor addition", MOVES 1400 — in consumption
this is the (P6) absolute bookkeeping: position additivity from DIV's exact remainder
weight at weight-pinned positions). The conclusion is unchanged: the twisted
homomorphism law against `cmul`, the cocycle product `DefsD.CarryAlg` already carries.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- A Laurent monomial `c·zᵏ` with `c ≠ 0` determines its exponent and scalar uniquely
(single-support). Used to pin the choice-extracted data inside `digD`. -/
private lemma mono_unit_eq {K : Type*} [Field K] {c₁ c₂ : K} {k₁ k₂ : ℤ}
    (hc₁ : c₁ ≠ 0)
    (h : LaurentPolynomial.C c₁ * LaurentPolynomial.T k₁
        = LaurentPolynomial.C c₂ * LaurentPolynomial.T k₂) :
    k₁ = k₂ ∧ c₁ = c₂ := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : Finsupp.single k₁ c₁ = Finsupp.single k₂ c₂ := h
  rw [Finsupp.single_eq_single_iff] at h'
  rcases h' with ⟨hk, hc⟩ | ⟨h0, _⟩
  · exact ⟨hk, hc⟩
  · exact absurd h0 hc₁

/-- `digD` computed on a known monomial `σ.R B = C c · T k`: the `u_{k mod e_b}`-homogeneous
generator with the ALIGNED scalar `c·z̄^{(k − (k mod e_b))/e_b}`. -/
private lemma digD_eq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) (c : (↥σ.K)ˣ) (k : ℤ)
    (h : σ.R B = LaurentPolynomial.C (c : ↥σ.K) * LaurentPolynomial.T k) :
    σ.digD zbar e_b B
      = dOf ((k : ZMod e_b))
          (((c : ↥σ.K) : F) *
            ((zbar ^ ((k - (((k : ZMod e_b)).val : ℤ)) / (e_b : ℤ)) : Fˣ) : F)) := by
  have hmono : IsMonomialUnit (σ.R B) := ⟨c, k, h⟩
  obtain ⟨hk, hc⟩ :=
    mono_unit_eq (Units.ne_zero hmono.choose)
      (hmono.choose_spec.choose_spec.symm.trans h)
  unfold Stage.digD
  rw [dif_pos hmono, hk, hc]

/-- The cocycle product on homogeneous generators (the D2 computation, directly from
`cmul`): `dOf ρ x ⋆ dOf ρ' y = dOf (ρ+ρ') (x·y·z̄^{carryExp ρ ρ'})`. -/
private lemma cmul_dOf {F : Type*} [Field F] {e : ℕ} [NeZero e] (zbar : Fˣ)
    (ρ ρ' : ZMod e) (x y : F) :
    cmul zbar (dOf ρ x) (dOf ρ' y)
      = dOf (ρ + ρ') (x * y * (zbar : F) ^ carryExp ρ ρ') := by
  funext τ
  simp only [cmul, dOf]
  rw [Finset.sum_eq_single ρ]
  · rw [Pi.single_eq_same]
    by_cases hτ : τ = ρ + ρ'
    · subst hτ
      rw [add_sub_cancel_left, Pi.single_eq_same, Pi.single_eq_same]
    · have hne : τ - ρ ≠ ρ' := by
        intro h
        rw [sub_eq_iff_eq_add] at h
        exact hτ (h.trans (add_comm ρ' ρ))
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hτ, mul_zero, zero_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

/-- The alignment-quotient carry identity: dividing out `e` AFTER adding two aligned
positions costs exactly the `carryExp` cocycle — `⌊(k+k')/e⌋ = ⌊k/e⌋ + ⌊k'/e⌋ + κ`. -/
private lemma quot_add_carry (e : ℕ) [NeZero e] (k k' : ℤ) :
    (k + k' - ((((k + k' : ℤ) : ZMod e)).val : ℤ)) / (e : ℤ)
      = (k - (((k : ZMod e)).val : ℤ)) / (e : ℤ)
        + (k' - (((k' : ZMod e)).val : ℤ)) / (e : ℤ)
        + (carryExp ((k : ZMod e)) ((k' : ZMod e)) : ℤ) := by
  have he0 : (0 : ℤ) < (e : ℤ) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne e))
  have hene : (e : ℤ) ≠ 0 := ne_of_gt he0
  have e1 : (e : ℤ) * (k / (e : ℤ)) + k % (e : ℤ) = k := Int.mul_ediv_add_emod k (e : ℤ)
  have e2 : (e : ℤ) * (k' / (e : ℤ)) + k' % (e : ℤ) = k' := Int.mul_ediv_add_emod k' (e : ℤ)
  have ha0 : 0 ≤ k % (e : ℤ) := Int.emod_nonneg k hene
  have ha1 : k % (e : ℤ) < (e : ℤ) := Int.emod_lt_of_pos k he0
  have hb0 : 0 ≤ k' % (e : ℤ) := Int.emod_nonneg k' hene
  have hb1 : k' % (e : ℤ) < (e : ℤ) := Int.emod_lt_of_pos k' he0
  rw [ZMod.val_intCast, ZMod.val_intCast, ZMod.val_intCast]
  have hq1 : (k - k % (e : ℤ)) / (e : ℤ) = k / (e : ℤ) := by
    have hnum : k - k % (e : ℤ) = (e : ℤ) * (k / (e : ℤ)) := by linarith
    rw [hnum, Int.mul_ediv_cancel_left _ hene]
  have hq2 : (k' - k' % (e : ℤ)) / (e : ℤ) = k' / (e : ℤ) := by
    have hnum : k' - k' % (e : ℤ) = (e : ℤ) * (k' / (e : ℤ)) := by linarith
    rw [hnum, Int.mul_ediv_cancel_left _ hene]
  rw [hq1, hq2]
  have hs : (k + k') % (e : ℤ) = (k % (e : ℤ) + k' % (e : ℤ)) % (e : ℤ) :=
    Int.add_emod k k' (e : ℤ)
  by_cases hc : (e : ℤ) ≤ k % (e : ℤ) + k' % (e : ℤ)
  · -- the carry fires: κ = 1
    have hcn : e ≤ ((k : ZMod e)).val + ((k' : ZMod e)).val := by
      have h := hc
      rw [← ZMod.val_intCast (n := e) k, ← ZMod.val_intCast (n := e) k'] at h
      exact_mod_cast h
    have hcε : carryExp ((k : ZMod e)) ((k' : ZMod e)) = 1 := by
      simp [carryExp, hcn]
    have hval : (k + k') % (e : ℤ) = k % (e : ℤ) + k' % (e : ℤ) - (e : ℤ) := by
      rw [hs]
      have h9 : (k % (e : ℤ) + k' % (e : ℤ) - (e : ℤ)) % (e : ℤ)
          = k % (e : ℤ) + k' % (e : ℤ) - (e : ℤ) :=
        Int.emod_eq_of_lt (by linarith) (by linarith)
      calc (k % (e : ℤ) + k' % (e : ℤ)) % (e : ℤ)
          = (k % (e : ℤ) + k' % (e : ℤ) - (e : ℤ) + (e : ℤ) * 1) % (e : ℤ) := by ring_nf
        _ = (k % (e : ℤ) + k' % (e : ℤ) - (e : ℤ)) % (e : ℤ) := by
              rw [Int.add_mul_emod_self_left]
        _ = _ := h9
    have hnum : k + k' - (k + k') % (e : ℤ)
        = (e : ℤ) * (k / (e : ℤ) + k' / (e : ℤ) + 1) := by
      rw [hval]; ring_nf; linarith
    rw [hnum, Int.mul_ediv_cancel_left _ hene, hcε]
    push_cast; ring
  · -- no carry: κ = 0
    have hcn : ¬ (e ≤ ((k : ZMod e)).val + ((k' : ZMod e)).val) := by
      intro hle
      apply hc
      have h := hle
      have h' : ((e : ℕ) : ℤ) ≤ ((((k : ZMod e)).val : ℤ) + (((k' : ZMod e)).val : ℤ)) := by
        exact_mod_cast h
      rw [ZMod.val_intCast, ZMod.val_intCast] at h'
      exact h'
    have hcε : carryExp ((k : ZMod e)) ((k' : ZMod e)) = 0 := by
      simp [carryExp, hcn]
    have hval : (k + k') % (e : ℤ) = k % (e : ℤ) + k' % (e : ℤ) := by
      rw [hs]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    have hnum : k + k' - (k + k') % (e : ℤ)
        = (e : ℤ) * (k / (e : ℤ) + k' / (e : ℤ)) := by
      rw [hval]; ring_nf; linarith
    rw [hnum, Int.mul_ediv_cancel_left _ hene, hcε]
    push_cast; ring

/-- Unit D7 (REV, adjudication 2026-07-28): the TWISTED DIG homomorphism law. For
monomial-shaped coefficients of the lift space `C_Φ̂` whose (S5) hypotheses carry their
z-offsets explicitly — `R B = c·zᵏ`, `R B″ = c″·zᵏ″` — and whose monic-division
remainder `B·B″ = Q·Φ̂ + R_dev` carries the ADDED anchor — `R R_dev = c_R·z^{k+k″}` —
the DIG map is multiplicative into the carry algebra at the birth index:

  `digD R_dev = cmul zbar (digD B) (digD B″)`,

`cmul` the cocycle product of `DefsD` (positions add WITH the carry; the aligned
scalars multiply twisted by `z̄^κ`). Proof route: the ψ-adic division identity
(`L3_DIV` = MOVES Lemma DIV(iii)) forces the scalar law `c_R = c·c″` at the added
anchor; the alignment quotient is exactly `carryExp` (`quot_add_carry`). -/
theorem D7_digD_mul {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat)
    (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0)
    (e_b : ℕ) [NeZero e_b]
    (B B'' Rdev Q : Polynomial ℤ_[p]) (hB : B ≠ 0) (hB'' : B'' ≠ 0)
    (hBd : B.natDegree < σ.e * g * σ.Φ.natDegree)
    (hB''d : B''.natDegree < σ.e * g * σ.Φ.natDegree)
    (hdiv : B * B'' = Q * Φhat + Rdev)
    (hRd : Rdev.natDegree < σ.e * g * σ.Φ.natDegree)
    (cB cB'' cR : (↥σ.K)ˣ) (kB kB'' : ℤ)
    (h5B : σ.R B = LaurentPolynomial.C (cB : ↥σ.K) * LaurentPolynomial.T kB)
    (h5B'' : σ.R B'' = LaurentPolynomial.C (cB'' : ↥σ.K) * LaurentPolynomial.T kB'')
    (h5R : σ.R Rdev = LaurentPolynomial.C (cR : ↥σ.K) * LaurentPolynomial.T (kB + kB'')) :
    σ.digD zbar e_b Rdev = cmul zbar (σ.digD zbar e_b B) (σ.digD zbar e_b B'') := by
  -- the ψ-adic division identity (Lemma DIV(iii)): dig′(R_dev) = dig′(B)·dig′(B″)
  obtain ⟨-, -, hdig⟩ :=
    L3_DIV σ ψ g hg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd hB''d Rdev Q hdiv hRd
  -- evaluate the three monomial digits
  have hdB : σ.digPrime zbar B = ((cB : ↥σ.K) : F) * ((zbar ^ kB : Fˣ) : F) := by
    rw [Stage.digPrime, h5B, LaurentPolynomial.eval₂_C_mul_T]
    rfl
  have hdB'' : σ.digPrime zbar B'' = ((cB'' : ↥σ.K) : F) * ((zbar ^ kB'' : Fˣ) : F) := by
    rw [Stage.digPrime, h5B'', LaurentPolynomial.eval₂_C_mul_T]
    rfl
  have hdR : σ.digPrime zbar Rdev
      = ((cR : ↥σ.K) : F) * ((zbar ^ (kB + kB'') : Fˣ) : F) := by
    rw [Stage.digPrime, h5R, LaurentPolynomial.eval₂_C_mul_T]
    rfl
  -- the scalar law at the added anchor: c_R = c·c″ (cancel the common z̄-power)
  have hcR : ((cR : ↥σ.K) : F) = ((cB : ↥σ.K) : F) * ((cB'' : ↥σ.K) : F) := by
    apply mul_right_cancel₀ (Units.ne_zero (zbar ^ (kB + kB'')))
    rw [← hdR, hdig, hdB, hdB'', zpow_add, Units.val_mul]
    ring
  -- assemble in the carry algebra
  rw [digD_eq σ zbar e_b B cB kB h5B, digD_eq σ zbar e_b B'' cB'' kB'' h5B'',
    digD_eq σ zbar e_b Rdev cR (kB + kB'') h5R, cmul_dOf,
    quot_add_carry e_b kB kB'']
  have hpos : (((kB + kB'') : ℤ) : ZMod e_b) = ((kB : ZMod e_b) + (kB'' : ZMod e_b)) := by
    push_cast
    ring
  rw [hpos, hcR]
  congr 1
  -- the aligned-scalar identity: split the z̄-powers and regroup
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    zpow_add₀ (Units.ne_zero zbar), zpow_add₀ (Units.ne_zero zbar), zpow_natCast]
  ring

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D7_digD_mul
