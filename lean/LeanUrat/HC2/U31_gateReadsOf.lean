/-
Unit U31.gate_readsOf_inert2  (HC-2 campaign, E-phase — rev 2, audit GAP-4: the
`ReadsOf` NON-VACUITY ANCHOR; FIRST E/P block with U27/U30)
moves_ref: at U27's root-only inert history H₀ (p = 2, n = 2), a CONCRETE monic
quadratic f (the inert gate's polynomial — the P-phase pins the exact instance from the
W1/realF2 gate data) with `ReadsOf 2 F4 2 f H₀` PROVED by an explicit development
witness — axiom- and seed-free.
PURPOSE: D4's `SideReads` body is an E-phase transcription; if the transcription
over-strengthens (flagged risk: clause (iii)'s `σ.R f` anchor), `ReadsOf` is EMPTY,
U19–U24 become vacuously true, and the W4-1 `eligible` seam dies silently — this gate
converts that silent death into a day-one failure.
deps: D4.  difficulty: medium.  hypothesis_fields: none.

PROOF ROUTE (P-phase, escalation): the base stage is INSTANTIATED here from scratch —
the (1,1)-diagonal Gauss stage at Φ = X over the prime subfield K₂ ≅ 𝔽₂ of F4.
Everything is transported through the ring hom θ : f(X) ↦ f(2X): the stage weight is
the 2-adic content exponent of θ f (normal form θ f = (C 2)^m · Q with Q ≢ 0 mod 2),
and the residual is the mod-2 reduction of the cofactor Q. Multiplicativity of w and R
is then PURE ALGEBRA (𝔽₂[X] is a domain); at p = 2 every unit digit is 1, so all
(S5)/(S6) digit bookkeeping collapses. The pinned concrete instance is the inert
quadratic IN STAGE COORDINATES, f = X² + 2X + 4 (= 4·g(X/2) for g = X² + X + 1, the
standard inert quadratic at p = 2: its roots −1 ± √−3 generate the unramified quadratic
extension of ℚ₂). Its root read has side (e,h) = (1,1) on slots 0..2, γ = 2, residual
pattern (1,1,1), R_anch = ψ = z² + z + 1 irreducible of degree g = 2 with ord_ψ = μ = 1.

VISIBILITY NOTE (2026-07-28, U27 restate+prove round): a dozen helper lemmas
(`ρ_eq_zero_iff`, `θ_C`, `bw_eq`, `is_const`, `NF_const`, `bw_const_nonneg`, `dev_coeff`,
`coherent_H₀`, `sideReads_ν₀`, `fq_monic`, `fq_natDegree`) were de-privatized — statements
byte-unchanged — so U27's concrete seed/JetSetup construction can reuse this file's
concrete history `H₀`/`ν₀`, its landing-key witness, and the base-stage valuation facts.

N-4 GATE STATUS (2026-07-28, sign-off round → REMEDIATION ROUND same day): `SideReads`
gained the ADDITIVE clause (vi) VERTEX READ-OFF (Defs; §9 F-3). Per F-3(c) the gate
RE-RUN with the clause is MANDATORY — it was QUEUED at the sign-off sitting and is now
EXECUTED (this file, remediation round): `sideReads_ν₀`'s clause-(vi) leg is PROVED along
exactly the queued sketch (Fact-B uniqueness of `fq`-adic developments gives `Bh 1 = 1`;
`vtx ν₀ = 1`), via `L0_FactB_unique`. The gate is again sorry-free and Lean-core:
`readsOf_fq`/`gate_readsOf_inert2` are UNCONDITIONAL — the clause-(vi) transcription is
NOT over-strengthened at the concrete witness (the GAP-4 adjudication passed). The
landing-key leg had been EXTRACTED to the standalone PROVED `landingKey_ν₀` so U27's
consumption (its `landing_ν₀`) stayed sorry-free throughout.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L0_FactB_unique

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace U31

/-! ### The residue field K₂ ≅ 𝔽₂ inside F4, and the digit map ρ : ℤ_[2] →+* ↥K₂ -/

/-- The prime-field embedding 𝔽₂ = ZMod 2 → F4. -/
noncomputable def ρ₀ : ZMod 2 →+* F4 := ZMod.castHom dvd_rfl F4

/-- The base residue field: the image of 𝔽₂ in F4. -/
noncomputable def K2 : Subfield F4 := ρ₀.fieldRange

/-- 𝔽₂ → ↥K₂, the range restriction of `ρ₀`. -/
noncomputable def ρ₁ : ZMod 2 →+* ↥K2 where
  toFun z := ⟨ρ₀ z, RingHom.mem_fieldRange.mpr ⟨z, rfl⟩⟩
  map_one' := by ext; exact map_one ρ₀
  map_mul' x y := by ext; exact map_mul ρ₀ x y
  map_zero' := by ext; exact map_zero ρ₀
  map_add' x y := by ext; exact map_add ρ₀ x y

/-- The digit map: reduction mod 2 into the base residue field. -/
noncomputable def ρ : ℤ_[2] →+* ↥K2 := ρ₁.comp PadicInt.toZMod

private lemma ρ₁_injective : Function.Injective ρ₁ := ρ₁.injective

lemma ρ_eq_zero_iff (x : ℤ_[2]) : ρ x = 0 ↔ (2 : ℤ_[2]) ∣ x := by
  have h1 : ρ x = ρ₁ (PadicInt.toZMod x) := rfl
  rw [h1, map_eq_zero_iff ρ₁ ρ₁_injective, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  norm_num

private lemma ρ_two : ρ (2 : ℤ_[2]) = 0 := (ρ_eq_zero_iff 2).mpr dvd_rfl

/-- Every element of K₂ is 0 or 1. -/
private lemma K2_cases (x : ↥K2) : x = 0 ∨ x = 1 := by
  obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp x.2
  have hz2 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hz2 z with h | h
  · left; ext; rw [← hz, h, map_zero]; rfl
  · right; ext; rw [← hz, h, map_one]; rfl

private lemma K2_ne_zero_eq_one {x : ↥K2} (hx : x ≠ 0) : x = 1 :=
  (K2_cases x).resolve_left hx

private lemma K2_unit_eq_one (a : (↥K2)ˣ) : (a : ↥K2) = 1 :=
  K2_ne_zero_eq_one a.ne_zero

private lemma K2_two : (2 : ↥K2) = 0 := by
  apply Subtype.ext
  show ((2 : ↥K2) : F4) = ((0 : ↥K2) : F4)
  push_cast
  exact CharTwo.two_eq_zero

/-! ### The transport hom θ : f(X) ↦ f(2X) and the 2-adic normal form -/

/-- The transport ring hom `f(X) ↦ f(2X)` on ℤ₂[X]. -/
noncomputable def θ : Polynomial ℤ_[2] →+* Polynomial ℤ_[2] := eval₂RingHom C (C 2 * X)

private lemma θ_apply (f : Polynomial ℤ_[2]) : θ f = eval₂ C (C 2 * X) f := rfl

lemma θ_C (b : ℤ_[2]) : θ (C b) = C b := by
  rw [θ_apply, eval₂_C]

private lemma θ_X : θ X = C 2 * X := by
  rw [θ_apply, eval₂_X]

private lemma θ_coeff (f : Polynomial ℤ_[2]) (n : ℕ) :
    (θ f).coeff n = f.coeff n * 2 ^ n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, add_mul]
  | monomial i a =>
      rw [θ_apply, eval₂_monomial, mul_pow, ← C_pow, ← mul_assoc, ← C_mul,
        coeff_monomial, coeff_C_mul, coeff_X_pow]
      by_cases h : n = i
      · subst h; simp
      · simp [h, Ne.symm h]

private lemma two_ne_zero' : (2 : ℤ_[2]) ≠ 0 := by norm_num

private lemma θ_ne_zero {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : θ f ≠ 0 := by
  intro h
  apply hf
  ext n
  have := congrArg (fun q => Polynomial.coeff q n) h
  simp only [θ_coeff, coeff_zero] at this
  have h2n : (2 : ℤ_[2]) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero'
  rcases mul_eq_zero.mp this with h' | h'
  · simpa using h'
  · exact absurd h' h2n

/-- 2-adic NORMAL FORM of a polynomial: `P = (C 2)^m · Q` with `Q` not ≡ 0 mod 2. -/
def NF (P : Polynomial ℤ_[2]) (m : ℕ) (Q : Polynomial ℤ_[2]) : Prop :=
  P = (C 2) ^ m * Q ∧ Q.map ρ ≠ 0

private lemma map_ρ_eq_zero_iff (P : Polynomial ℤ_[2]) :
    P.map ρ = 0 ↔ C (2 : ℤ_[2]) ∣ P := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have := congrArg (fun q => Polynomial.coeff q i) h
    simp only [coeff_map, coeff_zero] at this
    exact (ρ_eq_zero_iff _).mp this
  · intro h
    ext i
    rw [coeff_map, coeff_zero]
    exact_mod_cast (ρ_eq_zero_iff _).mpr (h i)

private lemma map_ρ_pow2_mul {k : ℕ} (hk : k ≠ 0) (Q : Polynomial ℤ_[2]) :
    (((C 2) ^ k * Q : Polynomial ℤ_[2])).map ρ = 0 := by
  rw [Polynomial.map_mul, Polynomial.map_pow, map_C, ρ_two, map_zero, zero_pow hk, zero_mul]

private lemma C2_pow_ne_zero (m : ℕ) : ((C 2 : Polynomial ℤ_[2])) ^ m ≠ 0 :=
  pow_ne_zero _ (C_ne_zero.mpr two_ne_zero')

/-- Cancellation: `(C 2)^a x = (C 2)^b y` with `a ≤ b` gives `x = (C 2)^(b-a) y`. -/
private lemma cancel_C2 {a b : ℕ} {x y : Polynomial ℤ_[2]} (hab : a ≤ b)
    (h : (C 2) ^ a * x = (C 2) ^ b * y) : x = (C 2) ^ (b - a) * y := by
  apply mul_left_cancel₀ (C2_pow_ne_zero a)
  rw [h, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- Scalar cancellation in ℤ₂. -/
private lemma cancel_two {a b : ℕ} {x y : ℤ_[2]} (hab : a ≤ b)
    (h : 2 ^ a * x = 2 ^ b * y) : x = 2 ^ (b - a) * y := by
  apply mul_left_cancel₀ (pow_ne_zero a two_ne_zero')
  rw [h, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- The normal exponent dominates any power-of-2 factorization exponent. -/
private lemma NF_dominates {P : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]}
    (h : NF P m Q) {k : ℕ} {S : Polynomial ℤ_[2]} (heq : P = (C 2) ^ k * S) : k ≤ m := by
  by_contra hkm
  push_neg at hkm
  have hQ : Q = (C 2) ^ (k - m) * S := cancel_C2 (le_of_lt hkm) (h.1.symm.trans heq)
  exact h.2 (hQ ▸ map_ρ_pow2_mul (by omega) S)

private lemma NF_unique {P : Polynomial ℤ_[2]} {m m' : ℕ} {Q Q' : Polynomial ℤ_[2]}
    (h : NF P m Q) (h' : NF P m' Q') : m = m' ∧ Q = Q' := by
  have h1 : m' ≤ m := NF_dominates h h'.1
  have h2 : m ≤ m' := NF_dominates h' h.1
  have hm : m = m' := le_antisymm h2 h1
  subst hm
  refine ⟨rfl, ?_⟩
  have := h.1.symm.trans h'.1
  exact mul_left_cancel₀ (C2_pow_ne_zero m) this

private lemma NF_exists {P : Polynomial ℤ_[2]} (hP : P ≠ 0) : ∃ m Q, NF P m Q := by
  have hirr : Irreducible (C (2 : ℤ_[2])) :=
    (prime_C_iff.mpr (by simpa using PadicInt.prime_p (p := 2))).irreducible
  obtain ⟨n, b, hnb, heq⟩ := WfDvdMonoid.max_power_factor hP hirr
  exact ⟨n, b, heq, fun h0 => hnb ((map_ρ_eq_zero_iff b).mp h0)⟩

/-! ### The stage valuation and residual, by choice against the normal form -/

open Classical in
/-- Weight function: the normal 2-exponent (junk 0 on non-representable input). -/
noncomputable def wA (P : Polynomial ℤ_[2]) : ℤ :=
  if h : ∃ mQ : ℕ × Polynomial ℤ_[2], NF P mQ.1 mQ.2 then (h.choose.1 : ℤ) else 0

open Classical in
/-- Residual function: mod-2 reduction of the normal cofactor, as a Laurent polynomial. -/
noncomputable def RA (P : Polynomial ℤ_[2]) : LaurentPolynomial ↥K2 :=
  if h : ∃ mQ : ℕ × Polynomial ℤ_[2], NF P mQ.1 mQ.2 then (h.choose.2.map ρ).toLaurent else 0

private lemma wA_eq {P : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]} (h : NF P m Q) :
    wA P = m := by
  have hex : ∃ mQ : ℕ × Polynomial ℤ_[2], NF P mQ.1 mQ.2 := ⟨(m, Q), h⟩
  rw [wA, dif_pos hex]
  exact congrArg (fun k : ℕ => (k : ℤ)) (NF_unique hex.choose_spec h).1

private lemma RA_eq {P : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]} (h : NF P m Q) :
    RA P = (Q.map ρ).toLaurent := by
  have hex : ∃ mQ : ℕ × Polynomial ℤ_[2], NF P mQ.1 mQ.2 := ⟨(m, Q), h⟩
  rw [RA, dif_pos hex]
  rw [(NF_unique hex.choose_spec h).2]

/-- The stage valuation `w f = min_j (v₂(a_j) + j)`, realized as the normal exponent of θf. -/
noncomputable def bw (f : Polynomial ℤ_[2]) : ℤ := wA (θ f)

/-- The stage residual `R f = [f]·T^{−w f}`, realized as the reduced normal cofactor of θf. -/
noncomputable def bR (f : Polynomial ℤ_[2]) : LaurentPolynomial ↥K2 := RA (θ f)

lemma bw_eq {f : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]}
    (h : NF (θ f) m Q) : bw f = m := wA_eq h

private lemma bR_eq {f : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]}
    (h : NF (θ f) m Q) : bR f = (Q.map ρ).toLaurent := RA_eq h

/-! ### Concrete normal forms -/

private lemma map_ρ_one_ne : ((1 : Polynomial ℤ_[2])).map ρ ≠ 0 := by
  rw [Polynomial.map_one]
  exact one_ne_zero

private lemma NF_θ_one : NF (θ 1) 0 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [map_one, pow_zero, one_mul]

private lemma NF_θ_C2 : NF (θ (C 2)) 1 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [θ_C, pow_one, mul_one]

private lemma NF_θ_C4 : NF (θ (C 4)) 2 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [θ_C, mul_one, ← C_pow]
  norm_num

private lemma NF_θ_C2pow (n : ℕ) : NF (θ (C (2 ^ n))) n 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [θ_C, mul_one, ← C_pow]

private lemma map_ρ_X_ne : ((X : Polynomial ℤ_[2])).map ρ ≠ 0 := by
  rw [Polynomial.map_X]
  exact X_ne_zero

private lemma NF_θ_X : NF (θ X) 1 X := by
  refine ⟨?_, map_ρ_X_ne⟩
  rw [θ_X, pow_one]

/-- The pinned concrete quadratic: `f = X² + 2X + 4`, the inert instance in stage scale. -/
noncomputable def fq : Polynomial ℤ_[2] := X ^ 2 + C 2 * X + C 4

/-- Its normal cofactor upstairs: `X² + X + 1` over ℤ₂. -/
noncomputable def q₁ : Polynomial ℤ_[2] := X ^ 2 + X + 1

/-! ### fq is monic quadratic (hoisted above `sideReads_ν₀` at the N-4 gate re-run, which
consumes both through Fact-B; statements byte-unchanged) -/

lemma fq_monic : fq.Monic := by
  unfold fq
  monicity!

lemma fq_natDegree : fq.natDegree = 2 := by
  unfold fq
  compute_degree!

private lemma map_ρ_q₁ : q₁.map ρ = X ^ 2 + X + 1 := by
  rw [q₁, Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]

private lemma XXone_ne_zero {L : Type*} [Field L] : (X ^ 2 + X + 1 : Polynomial L) ≠ 0 := by
  intro h
  have := congrArg (fun q => Polynomial.coeff q 0) h
  simp at this

private lemma NF_θ_fq : NF (θ fq) 2 q₁ := by
  constructor
  · rw [fq, map_add, map_add, map_pow, map_mul, θ_X, θ_C, θ_C, q₁]
    have h4 : (C (4 : ℤ_[2])) = C 2 ^ 2 := by rw [← C_pow]; norm_num
    rw [h4]
    ring
  · rw [map_ρ_q₁]
    exact XXone_ne_zero

/-! ### The stage laws -/

private lemma bw_mul (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0) :
    bw (f * g) = bw f + bw g := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hfg : NF (θ (f * g)) (mf + mg) (P * Q) := by
    constructor
    · rw [map_mul, hP.1, hQ.1, pow_add]; ring
    · rw [Polynomial.map_mul]
      exact mul_ne_zero hP.2 hQ.2
  rw [bw_eq hfg, bw_eq hP, bw_eq hQ]
  push_cast
  ring

private lemma bR_mul (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0) :
    bR (f * g) = bR f * bR g := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hfg : NF (θ (f * g)) (mf + mg) (P * Q) := by
    constructor
    · rw [map_mul, hP.1, hQ.1, pow_add]; ring
    · rw [Polynomial.map_mul]
      exact mul_ne_zero hP.2 hQ.2
  rw [bR_eq hfg, bR_eq hP, bR_eq hQ, Polynomial.map_mul, map_mul]

private lemma bw_ult (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (bw f) (bw g) ≤ bw (f + g) := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  obtain ⟨m, S, hS⟩ := NF_exists (θ_ne_zero hfg)
  rw [bw_eq hP, bw_eq hQ, bw_eq hS]
  rcases le_total mf mg with hle | hle
  · have heq : θ (f + g) = (C 2) ^ mf * (P + (C 2) ^ (mg - mf) * Q) := by
      rw [map_add, hP.1, hQ.1, mul_add, ← mul_assoc, ← pow_add]
      congr 3
      omega
    have := NF_dominates hS heq
    have hminf : min (mf : ℤ) (mg : ℤ) = (mf : ℤ) := min_eq_left (by exact_mod_cast hle)
    rw [hminf]
    exact_mod_cast this
  · have heq : θ (f + g) = (C 2) ^ mg * ((C 2) ^ (mf - mg) * P + Q) := by
      rw [map_add, hP.1, hQ.1, mul_add, ← mul_assoc, ← pow_add]
      congr 3
      omega
    have := NF_dominates hS heq
    have hming : min (mf : ℤ) (mg : ℤ) = (mg : ℤ) := min_eq_right (by exact_mod_cast hle)
    rw [hming]
    exact_mod_cast this

private lemma bR_add (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (hw : bw f = bw g) (hwadd : bw (f + g) = bw f) :
    bR (f + g) = bR f + bR g := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  obtain ⟨m, S, hS⟩ := NF_exists (θ_ne_zero hfg)
  have hmfg : mg = mf := by
    have h1 := hw
    rw [bw_eq hP, bw_eq hQ] at h1
    exact_mod_cast h1.symm
  have hm : m = mf := by
    have h1 := hwadd
    rw [bw_eq hS, bw_eq hP] at h1
    exact_mod_cast h1
  rw [hmfg] at hQ
  rw [hm] at hS
  have heq : θ (f + g) = (C 2) ^ mf * (P + Q) := by
    rw [map_add, hP.1, hQ.1, mul_add]
  have hSPQ : S = P + Q := by
    have := hS.1.symm.trans heq
    exact mul_left_cancel₀ (C2_pow_ne_zero mf) this
  rw [bR_eq hS, bR_eq hP, bR_eq hQ, hSPQ, Polynomial.map_add, map_add]

private lemma bR_lt (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (hw : bw f < bw g) : bR (f + g) = bR f := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hmm : mf < mg := by
    have := hw
    rw [bw_eq hP, bw_eq hQ] at this
    exact_mod_cast this
  have hNF : NF (θ (f + g)) mf (P + (C 2) ^ (mg - mf) * Q) := by
    constructor
    · rw [map_add, hP.1, hQ.1, mul_add, ← mul_assoc, ← pow_add]
      congr 3
      omega
    · rw [Polynomial.map_add, map_ρ_pow2_mul (by omega) Q, add_zero]
      exact hP.2
  rw [bR_eq hNF, bR_eq hP, Polynomial.map_add, map_ρ_pow2_mul (by omega) Q, add_zero]

private lemma bR_zero : bR 0 = 0 := by
  have hno : ¬ ∃ mQ : ℕ × Polynomial ℤ_[2], NF (θ 0) mQ.1 mQ.2 := by
    rintro ⟨⟨m, Q⟩, hQ1, hQ2⟩
    rw [map_zero] at hQ1
    have hQ0 : Q = 0 := by
      rcases mul_eq_zero.mp hQ1.symm with h | h
      · exact absurd h (C2_pow_ne_zero m)
      · exact h
    rw [hQ0, Polynomial.map_zero] at hQ2
    exact hQ2 rfl
  rw [bR, RA, dif_neg hno]

private lemma bR_ne (f : Polynomial ℤ_[2]) (hf : f ≠ 0) : bR f ≠ 0 := by
  obtain ⟨m, Q, hQ⟩ := NF_exists (θ_ne_zero hf)
  rw [bR_eq hQ]
  intro h
  exact hQ.2 (map_eq_zero_iff _ Polynomial.toLaurent_injective |>.mp h)

private lemma bw_X : bw X = 1 := bw_eq NF_θ_X

private lemma bR_X : bR X = LaurentPolynomial.T 1 := by
  rw [bR_eq NF_θ_X, Polynomial.map_X, Polynomial.toLaurent_X]

private lemma bw_one : bw 1 = 0 := bw_eq NF_θ_one

private lemma bw_C2 : bw (C 2) = 1 := bw_eq NF_θ_C2

private lemma bw_C4 : bw (C 4) = 2 := bw_eq NF_θ_C4

private lemma toLaurent_map_one : (((1 : Polynomial ℤ_[2])).map ρ).toLaurent = 1 := by
  rw [Polynomial.map_one, Polynomial.toLaurent_one]

private lemma bR_one : bR 1 = 1 := by rw [bR_eq NF_θ_one, toLaurent_map_one]

private lemma bR_C2 : bR (C 2) = 1 := by rw [bR_eq NF_θ_C2, toLaurent_map_one]

private lemma bR_C4 : bR (C 4) = 1 := by rw [bR_eq NF_θ_C4, toLaurent_map_one]

private lemma bw_C2pow (n : ℕ) : bw (C (2 ^ n)) = n := bw_eq (NF_θ_C2pow n)

private lemma bR_C2pow (n : ℕ) : bR (C (2 ^ n)) = 1 := by
  rw [bR_eq (NF_θ_C2pow n), toLaurent_map_one]

/-- Constants: development-slot polynomials at Φ = X. -/
lemma is_const {B : Polynomial ℤ_[2]} (h : B.degree < (X : Polynomial ℤ_[2]).degree) :
    B = C (B.coeff 0) := by
  by_cases hB : B = 0
  · rw [hB]; simp
  · have h1 : B.natDegree < (X : Polynomial ℤ_[2]).natDegree :=
      Polynomial.natDegree_lt_natDegree hB h
    rw [natDegree_X] at h1
    exact Polynomial.eq_C_of_natDegree_le_zero (by omega)

/-- Normal form of a nonzero constant: `C b = (C 2)^m · C u` with `ρ u ≠ 0`. -/
lemma NF_const {b : ℤ_[2]} (hb : b ≠ 0) :
    ∃ (m : ℕ) (u : ℤ_[2]), NF (C b) m (C u) ∧ ρ u ≠ 0 := by
  obtain ⟨m, Q, hQ⟩ := NF_exists (C_ne_zero.mpr hb)
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hQ.2
    rw [h, Polynomial.map_zero]
  have hdeg : Q.degree ≤ 0 := by
    have h1 := congrArg Polynomial.degree hQ.1
    rw [degree_C hb, degree_mul, degree_pow, degree_C two_ne_zero'] at h1
    simp only [smul_zero, zero_add] at h1
    exact le_of_eq h1.symm
  have hQC : Q = C (Q.coeff 0) := eq_C_of_degree_le_zero hdeg
  refine ⟨m, Q.coeff 0, ⟨by rw [← hQC]; exact hQ.1, by rw [← hQC]; exact hQ.2⟩, ?_⟩
  intro h0
  apply hQ.2
  rw [hQC, map_C, h0, map_zero]

/-- The constant's stage residual is 1 (all p = 2 digits are 1). -/
private lemma bR_const {b : ℤ_[2]} (hb : b ≠ 0) : bR (C b) = 1 := by
  obtain ⟨m, u, hNF, hu⟩ := NF_const hb
  have hNFθ : NF (θ (C b)) m (C u) := by rw [θ_C]; exact hNF
  rw [bR_eq hNFθ, map_C]
  have : ρ u = 1 := K2_ne_zero_eq_one hu
  rw [this, Polynomial.toLaurent_C, map_one]

lemma bw_const_nonneg {b : ℤ_[2]} (hb : b ≠ 0) : 0 ≤ bw (C b) := by
  obtain ⟨m, u, hNF, _⟩ := NF_const hb
  have hNFθ : NF (θ (C b)) m (C u) := by rw [θ_C]; exact hNF
  rw [bw_eq hNFθ]
  exact_mod_cast Nat.zero_le m

/-! ### Development coefficients at Φ = X, and the K1 law -/

lemma dev_coeff {f : Polynomial ℤ_[2]} {B : ℕ → Polynomial ℤ_[2]} {N : ℕ}
    (hd : IsDevelopment (X : Polynomial ℤ_[2]) f B N) :
    ∀ j, f.coeff j = if j < N then (B j).coeff 0 else 0 := by
  obtain ⟨hdeg, hz, hsum⟩ := hd
  intro j
  have hBC : ∀ i, B i = C ((B i).coeff 0) := fun i => is_const (hdeg i)
  rw [hsum]
  rw [finset_sum_coeff]
  have hterm : ∀ i, (B i * X ^ i).coeff j = if j = i then (B i).coeff 0 else 0 := by
    intro i
    rw [hBC i, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_C_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq (Finset.range N) j (fun i => (B i).coeff 0)]
  simp only [Finset.mem_range]

private lemma bK1 : K1At bw (X : Polynomial ℤ_[2]) (bw X) := by
  rw [bw_X]
  intro f B N hf hd
  have hcoeff := dev_coeff hd
  obtain ⟨m, S, hS⟩ := NF_exists (θ_ne_zero hf)
  have hwf : bw f = m := bw_eq hS
  -- the coefficient identity: f.coeff j * 2^j = 2^m * S.coeff j
  have hkey : ∀ j, f.coeff j * 2 ^ j = 2 ^ m * S.coeff j := by
    intro j
    have := congrArg (fun q => Polynomial.coeff q j) hS.1
    simp only [θ_coeff] at this
    rw [this, ← C_pow, coeff_C_mul]
  have hBC : ∀ i, B i = C ((B i).coeff 0) := fun i => is_const (hd.1 i)
  -- per-slot lower bound
  have hbound : ∀ j, j < N → B j ≠ 0 → (m : ℤ) ≤ bw (B j) + (j : ℤ) * 1 := by
    intro j hj hBj
    have hbj : (B j).coeff 0 ≠ 0 := by
      intro h0
      exact hBj (by rw [hBC j, h0, map_zero])
    obtain ⟨mj, u, hNFj, hu⟩ := NF_const hbj
    have hNFθj : NF (θ (B j)) mj (C u) := by rw [hBC j, θ_C]; exact hNFj
    rw [bw_eq hNFθj]
    have hfj : f.coeff j = (B j).coeff 0 := by rw [hcoeff j, if_pos hj]
    have hbu : (B j).coeff 0 = 2 ^ mj * u := by
      have h1 := congrArg (fun q => Polynomial.coeff q 0) hNFj.1
      simp only [← C_pow, ← C_mul, coeff_C_zero] at h1
      exact h1
    -- 2^(mj+j) * u = 2^m * S.coeff j
    have hid : 2 ^ (mj + j) * u = 2 ^ m * S.coeff j := by
      have h1 := hkey j
      rw [hfj, hbu] at h1
      rw [← h1, pow_add]
      ring
    by_contra hcon
    push_neg at hcon
    have hlt : mj + j < m := by
      have : (mj : ℤ) + (j : ℤ) < (m : ℤ) := by linarith
      exact_mod_cast this
    have hu2 : u = 2 ^ (m - (mj + j)) * S.coeff j := cancel_two (le_of_lt hlt) hid
    apply hu
    rw [hu2, map_mul, map_pow, ρ_two, zero_pow (by omega), zero_mul]
  constructor
  · exact fun j hj hBj => hwf ▸ hbound j hj hBj
  · -- attainment
    have hSne : S.map ρ ≠ 0 := hS.2
    have hex : ∃ j, ρ (S.coeff j) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hSne
      refine Polynomial.ext fun i => ?_
      rw [coeff_map, coeff_zero]
      exact hall i
    obtain ⟨j, hj⟩ := hex
    have hSj : S.coeff j ≠ 0 := fun h => hj (by rw [h, map_zero])
    have hfj_ne : f.coeff j ≠ 0 := by
      intro h0
      have := hkey j
      rw [h0, zero_mul] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact pow_ne_zero _ two_ne_zero' h
      · exact hSj h
    have hjN : j < N := by
      by_contra hge
      push_neg at hge
      exact hfj_ne (by rw [hcoeff j, if_neg (by omega)])
    have hBj : B j ≠ 0 := by
      intro h0
      apply hfj_ne
      rw [hcoeff j, if_pos hjN, h0, coeff_zero]
    refine ⟨j, hjN, hBj, ?_⟩
    -- exactness at j
    have hbj : (B j).coeff 0 ≠ 0 := by
      intro h0
      exact hBj (by rw [hBC j, h0, map_zero])
    obtain ⟨mj, u, hNFj, hu⟩ := NF_const hbj
    have hNFθj : NF (θ (B j)) mj (C u) := by rw [hBC j, θ_C]; exact hNFj
    have hfj : f.coeff j = (B j).coeff 0 := by rw [hcoeff j, if_pos hjN]
    have hbu : (B j).coeff 0 = 2 ^ mj * u := by
      have h1 := congrArg (fun q => Polynomial.coeff q 0) hNFj.1
      simp only [← C_pow, ← C_mul, coeff_C_zero] at h1
      exact h1
    have hid : 2 ^ (mj + j) * u = 2 ^ m * S.coeff j := by
      have h1 := hkey j
      rw [hfj, hbu] at h1
      rw [← h1, pow_add]
      ring
    have hle : (m : ℤ) ≤ (mj : ℤ) + (j : ℤ) := by
      have h2 := hbound j hjN hBj
      rw [bw_eq hNFθj] at h2
      linarith
    have hle' : m ≤ mj + j := by exact_mod_cast hle
    have heq : m = mj + j := by
      by_contra hne
      have hlt : m < mj + j := by omega
      have hSj2 : S.coeff j = 2 ^ (mj + j - m) * u := cancel_two (le_of_lt hlt) hid.symm
      apply hj
      rw [hSj2, map_mul, map_pow, ρ_two, zero_pow (by omega), zero_mul]
    show bw f = bw (B j) + (j : ℤ) * 1
    rw [hwf, bw_eq hNFθj, heq]
    push_cast
    ring

/-! ### The base stage -/

private lemma inC_C {b : ℤ_[2]} : inC (X : Polynomial ℤ_[2]) (C b) := by
  show (C b).degree < (X : Polynomial ℤ_[2]).degree
  rw [degree_X]
  exact lt_of_le_of_lt degree_C_le (by norm_num)

private lemma bS5 : ∀ B : Polynomial ℤ_[2], B ≠ 0 → inC (X : Polynomial ℤ_[2]) B →
    ∃ c : (↥K2)ˣ, bR B = LaurentPolynomial.C (c : ↥K2) *
      LaurentPolynomial.T (- (0 : ℤ) * bw B) := by
  intro B hB hin
  refine ⟨1, ?_⟩
  have hBC : B = C (B.coeff 0) := is_const hin
  have hb : B.coeff 0 ≠ 0 := fun h => hB (by rw [hBC, h, map_zero])
  rw [hBC, bR_const hb]
  rw [neg_zero, zero_mul, LaurentPolynomial.T_zero, Units.val_one, map_one, one_mul]

/-- **The base stage**: the (1,1)-diagonal Gauss stage at Φ = X over K₂. -/
noncomputable def bStage : Stage 2 F4 where
  e := 1
  h := 1
  s := 1
  t := 0
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  he1t := fun _ => rfl
  Φ := X
  hmonic := monic_X
  hdeg := le_of_eq natDegree_X.symm
  w := bw
  wPrev := bw
  K := K2
  FQ := K2
  hFQ_le := le_rfl
  R := bR
  hwmul := bw_mul
  hwult := bw_ult
  hvalgrp := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[2], f ≠ 0 ∧ g ≠ 0 ∧ bw f - bw g = n} := by
      refine ⟨C 2, 1, C_ne_zero.mpr two_ne_zero', one_ne_zero, ?_⟩
      rw [bw_C2, bw_one, sub_zero]
    have : n = n • (1 : ℤ) := by simp
    rw [this]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure h1) n
  hwΦ := by rw [bw_X]; norm_num
  hStretch := fun B hB _ => by push_cast; ring
  hR0 := bR_zero
  hRne := bR_ne
  hRmul := bR_mul
  hRadd := bR_add
  hRlt := bR_lt
  hRΦ := bR_X
  hK1 := bK1
  hS5 := bS5
  reps := []
  hreps := by simp
  Tvec := []
  hTvec := rfl
  weightSet := Set.Ici 0
  hWS := fun B hB hin => by
    have hBC : B = C (B.coeff 0) := is_const hin
    have hb : B.coeff 0 ≠ 0 := fun h => hB (by rw [hBC, h, map_zero])
    rw [hBC]
    exact bw_const_nonneg hb
  hS6a := by
    intro ν hν
    refine ⟨1, fun c _ => ?_⟩
    refine ⟨C (2 ^ ν.toNat), C_ne_zero.mpr (pow_ne_zero _ two_ne_zero'), inC_C, ?_, ?_⟩
    · rw [bw_C2pow, Int.toNat_of_nonneg hν]
    · rw [bR_C2pow, K2_unit_eq_one (c * 1), map_one, neg_zero, zero_mul,
        LaurentPolynomial.T_zero, one_mul]
  hS6b := by
    intro ν a hν
    have hν0 : (0 : ℤ) ≤ ν := le_trans (by rw [bw_X]; norm_num) (le_of_lt hν)
    refine ⟨C (2 ^ ν.toNat), C_ne_zero.mpr (pow_ne_zero _ two_ne_zero'), inC_C, ?_, ?_⟩
    · rw [bw_C2pow, Int.toNat_of_nonneg hν0]
    · rw [bR_C2pow, K2_unit_eq_one a, map_one, neg_zero, zero_mul,
        LaurentPolynomial.T_zero, one_mul]

/-! ### The residual pattern ψ = z² + z + 1 over K₂, and its canonical root in F4 -/

/-- The inert read's residual polynomial over the base residue field. -/
noncomputable def ψ₂ : Polynomial ↥K2 := X ^ 2 + X + 1

private lemma ψ₂_monic : ψ₂.Monic := by
  unfold ψ₂
  monicity!

private lemma ψ₂_natDegree : ψ₂.natDegree = 2 := by
  unfold ψ₂
  compute_degree!

private lemma ψ₂_ne_zero : ψ₂ ≠ 0 := ψ₂_monic.ne_zero

private lemma ψ₂_eval_ne (x : ↥K2) : ψ₂.eval x ≠ 0 := by
  rcases K2_cases x with h | h <;> subst h <;>
    simp only [ψ₂, eval_add, eval_pow, eval_X, eval_one]
  · norm_num
  · rw [one_pow]
    intro h
    have h2 : (1 : ↥K2) + 1 + 1 = (2 : ↥K2) + 1 := by ring
    rw [h2, K2_two, zero_add] at h
    exact one_ne_zero h

private lemma ψ₂_coeff_zero : ψ₂.coeff 0 = 1 := by
  unfold ψ₂
  simp [coeff_add, coeff_X_pow, coeff_one]

private lemma ψ₂_coeff_one : ψ₂.coeff 1 = 1 := by
  unfold ψ₂
  simp [coeff_add, coeff_X_pow, coeff_one]

private lemma ψ₂_irr : Irreducible ψ₂ := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := Polynomial.isUnit_iff_degree_eq_zero.mp hu
    have hnd : ψ₂.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq hd)
    rw [ψ₂_natDegree] at hnd
    omega
  · intro a b hab
    have hane : a ≠ 0 := fun h => ψ₂_ne_zero (by rw [hab, h, zero_mul])
    have hbne : b ≠ 0 := fun h => ψ₂_ne_zero (by rw [hab, h, mul_zero])
    have hdeg : a.natDegree + b.natDegree = 2 := by
      rw [← natDegree_mul hane hbne, ← hab, ψ₂_natDegree]
    rcases Nat.eq_zero_or_pos a.natDegree with ha0 | hapos
    · left
      have haC : a = C (a.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq ha0)
      have hc : a.coeff 0 ≠ 0 := fun h => hane (by rw [haC, h, map_zero])
      rw [haC, isUnit_C]
      exact isUnit_iff_ne_zero.mpr hc
    rcases Nat.eq_zero_or_pos b.natDegree with hb0 | hbpos
    · right
      have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hb0)
      have hc : b.coeff 0 ≠ 0 := fun h => hbne (by rw [hbC, h, map_zero])
      rw [hbC, isUnit_C]
      exact isUnit_iff_ne_zero.mpr hc
    exfalso
    have ha1 : a.natDegree = 1 := by omega
    have hc1 : a.coeff 1 ≠ 0 := by
      have hlead := Polynomial.leadingCoeff_ne_zero.mpr hane
      rwa [Polynomial.leadingCoeff, ha1] at hlead
    have haXC : a = C (a.coeff 1) * X + C (a.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq ha1)
    set r : ↥K2 := -(a.coeff 0) / (a.coeff 1) with hr
    have har : a.eval r = 0 := by
      rw [haXC]
      simp only [eval_add, eval_mul, eval_C, eval_X]
      rw [hr]
      field_simp
      ring
    have := ψ₂_eval_ne r
    apply this
    rw [hab, eval_mul, har, zero_mul]

/-! ### A root of ψ₂ in F4 and the canonical residue root -/

private lemma exists_root : ∃ ω : F4, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F4ˣ)
  have hcard : Nat.card F4ˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have horder : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hg3 : (g : F4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← horder, pow_orderOf_eq_one, Units.val_one]
  have hgne : (g : F4) ≠ 1 := by
    intro h
    have h1 : g = 1 := Units.ext h
    rw [h1, orderOf_one] at horder
    omega
  refine ⟨g, ?_⟩
  have hfac : ((g : F4) - 1) * ((g : F4) ^ 2 + (g : F4) + 1) = (g : F4) ^ 3 - 1 := by ring
  have hzero : ((g : F4) - 1) * ((g : F4) ^ 2 + (g : F4) + 1) = 0 := by
    rw [hfac, hg3, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hgne
  · exact h

private lemma root_ne_zero {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

private lemma Ψmap_eq : ψ₂.map K2.subtype = (X ^ 2 + X + 1 : Polynomial F4) := by
  rw [ψ₂, Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]

private lemma Ψmap_ne : ψ₂.map K2.subtype ≠ 0 := by
  rw [Ψmap_eq]
  exact XXone_ne_zero

private lemma root_eval₂ {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) :
    Polynomial.eval₂ K2.subtype ω ψ₂ = 0 := by
  rw [eval₂_eq_eval_map, Ψmap_eq, eval_add, eval_add, eval_pow, eval_X, eval_one]
  exact hω

private lemma ord_ψ₂ : OrdPsiPoly ψ₂ ψ₂ 1 := by
  constructor
  · rw [pow_one]
  · intro hdvd
    have h1 := Polynomial.natDegree_le_of_dvd hdvd ψ₂_ne_zero
    rw [Polynomial.natDegree_pow, ψ₂_natDegree] at h1
    omega

/-! ### The root node constructor -/

/-- The root-read node of the inert quadratic, parametric in the residue root. -/
noncomputable def mkNode (z : F4ˣ)
    (hz : Polynomial.eval₂ K2.subtype ((z : F4ˣ) : F4) ψ₂ = 0) : Node 2 F4 where
  species := ReadSpecies.root
  σ := bStage
  e := 1
  h := 1
  s := 1
  t := 0
  g := 2
  μ := 1
  a := 0
  s0 := 0
  wSide := 2
  Dwidth := 1
  line := ⟨2, 1⟩
  ustar := 0
  gam := 2
  zbar := z
  center := 0
  lift := 0
  ψ := ψ₂
  pat := fun _ => 1
  Ranch := ψ₂
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := by norm_num
  hμ := le_refl 1
  hEdvd := one_dvd 2
  hDwidth := natDegree_X.symm
  hψmonic := ψ₂_monic
  hψdeg := ψ₂_natDegree
  hψirr := ψ₂_irr
  hRanch := by
    show ψ₂ = ∑ k ∈ Finset.range 3, (Polynomial.C (1 : ↥K2) * (X : Polynomial ↥K2) ^ k)
    have hbody : ∀ k : ℕ, (Polynomial.C (1 : ↥K2) * (X : Polynomial ↥K2) ^ k) = X ^ k := by
      intro k
      rw [map_one, one_mul]
    rw [Finset.sum_congr rfl (fun k _ => hbody k)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, ψ₂]
    ring
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (2 : ℚ) - 1 * (((0 + 2) * 1 : ℕ) : ℚ) = 0
    norm_num
  hOrd := ord_ψ₂
  hzbarRoot := hz
  hspecInc := by intro h; simp at h
  hspecRec := by intro h; simp at h
  hspecRecCenter := by intro h; simp at h

/-- The auxiliary node carrying SOME root (the cyclic-group witness). -/
noncomputable def νaux : Node 2 F4 :=
  mkNode (Units.mk0 exists_root.choose (root_ne_zero exists_root.choose_spec))
    (by exact root_eval₂ exists_root.choose_spec)

/-- THE canonical residue root of the inert read (`canonRoot` of the aux node — a
function of (σ, ψ) only, so it agrees definitionally across all `mkNode` instances). -/
noncomputable def r₀ : F4 := canonRoot νaux

/-- Value-abstracted extractor for the `canonRoot` selector shape: if the selector input is
a coe (never ⊥) and the property holds at every possible coe value, it holds at the read
result. Stated over an ARBITRARY input so no `Finset.min`/instance elaboration happens here. -/
private lemma recBot_lift (P : F4 → Prop) (x : WithBot (Fin (Nat.card F4)))
    (hne : ∃ j : Fin (Nat.card F4), x = j)
    (hx : ∀ j : Fin (Nat.card F4), x = j → P ((fieldEnum F4).symm j)) :
    P (WithBot.recBotCoe 0 (fun j => (fieldEnum F4).symm j) x) := by
  obtain ⟨j, rfl⟩ := hne
  exact hx j rfl

private lemma r₀_prop : r₀ ^ 2 + r₀ + 1 = 0 := by
  classical
  have hr : r₀ = canonRoot νaux := rfl
  rw [hr]
  unfold canonRoot
  refine recBot_lift (fun y => y ^ 2 + y + 1 = 0) _ ?_ ?_
  · -- the min is a genuine value: the root Finset is nonempty
    apply Finset.min_of_nonempty
    refine ⟨fieldEnum F4 exists_root.choose, Finset.mem_image_of_mem _ ?_⟩
    refine Multiset.mem_toFinset.mpr ?_
    refine (mem_roots ?_).mpr ?_
    · show ψ₂.map K2.subtype ≠ 0
      exact Ψmap_ne
    · show (ψ₂.map K2.subtype).eval exists_root.choose = 0
      rw [Ψmap_eq, eval_add, eval_add, eval_pow, eval_X, eval_one]
      exact exists_root.choose_spec
  · intro j hj
    have hjmem := Finset.mem_of_min hj
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hjmem
    rw [← hxe, Equiv.symm_apply_apply]
    have hx' := Multiset.mem_toFinset.mp hx
    have hxr : (ψ₂.map K2.subtype).eval x = 0 := (mem_roots Ψmap_ne).mp hx'
    rw [Ψmap_eq, eval_add, eval_add, eval_pow, eval_X, eval_one] at hxr
    exact hxr

private lemma r₀_ne : r₀ ≠ 0 := root_ne_zero r₀_prop

/-- **The node**: the root read of the inert quadratic with the CANONICAL residue root. -/
noncomputable def ν₀ : Node 2 F4 :=
  mkNode (Units.mk0 r₀ r₀_ne) (by
    show Polynomial.eval₂ K2.subtype r₀ ψ₂ = 0
    exact root_eval₂ r₀_prop)

private lemma canonRoot_ν₀ : canonRoot ν₀ = r₀ := rfl

/-! ### The history -/

/-- The root-only inert history. -/
noncomputable def H₀ : History 2 F4 where
  nodes := [ν₀]
  nonempty := by simp
  root_iff := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact iff_of_true rfl rfl

lemma coherent_H₀ : HistoryCoherent H₀ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj
    show (X : Polynomial ℤ_[2]).natDegree = 1
    exact natDegree_X
  · intro i hi
    have hi1 : i < 1 := hi
    have hi0 : i = 0 := by omega
    subst hi0
    show (1 : ℚ) * (((1 : ℕ) : ℚ) * ((H₀.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ)) = ((1 : ℕ) : ℚ)
    have hstr : H₀.strFrame 0 = 1 := rfl
    rw [hstr]
    norm_num
  · intro i hi
    have hi1 : i < 1 := hi
    have hi0 : i = 0 := by omega
    subst hi0
    show (((2 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₀.strFrame 0 : ℕ) : ℚ) * (0 : ℚ))
      + (((0 + 2 : ℕ)) : ℚ) * ((1 : ℕ) : ℚ)
    have hstr : H₀.strFrame 0 = 1 := rfl
    rw [hstr]
    norm_num
  · intro i hi
    have h1 : i + 1 < 1 := hi
    exact absurd h1 (by omega)

/-! ### The classifier-run witness (SideReads at the node) -/

/-- The Φ-adic development of `fq` at the key X. -/
noncomputable def Bdev : ℕ → Polynomial ℤ_[2] :=
  fun j => if j = 0 then C 4 else if j = 1 then C 2 else if j = 2 then 1 else 0

private lemma Bdev_dev : IsDevelopment (X : Polynomial ℤ_[2]) fq Bdev 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [degree_X]
    unfold Bdev
    split_ifs
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_one_le (by norm_num)
    · rw [degree_zero]; exact bot_lt_iff_ne_bot.mpr (by norm_num)
  · intro j hj
    unfold Bdev
    split_ifs with h1 h2 h3
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : Bdev 0 = C 4 := rfl
    have h1 : Bdev 1 = C 2 := rfl
    have h2 : Bdev 2 = 1 := rfl
    rw [h0, h1, h2, fq]
    ring

private lemma Bdev_w : bw (Bdev 0) = 2 ∧ bw (Bdev 1) = 1 ∧ bw (Bdev 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show bw (C 4) = 2; exact bw_C4
  · show bw (C 2) = 1; exact bw_C2
  · show bw 1 = 0; exact bw_one

/-- The landing-key witness at ν₀, STANDALONE (extracted at N-4, statement and proof
byte-unchanged from the former clause-(iv) bullet, so U27's consumption stays sorry-free
while the clause-(vi) gate re-run is queued). -/
lemma landingKey_ν₀ : LandingKey ν₀ fq := by
  constructor
  · intro h
    exact ReadSpecies.noConfusion h
  · intro _
    refine ⟨fun k => if k = 0 then C 4 else if k = 1 then C 2 else 0, ?_, ?_, ?_⟩
    · intro k hk
      match k with
      | 0 =>
          have hk' : ψ₂.coeff 0 = 0 := hk
          rw [ψ₂_coeff_zero] at hk'
          exact absurd hk' one_ne_zero
      | 1 =>
          have hk' : ψ₂.coeff 1 = 0 := hk
          rw [ψ₂_coeff_one] at hk'
          exact absurd hk' one_ne_zero
      | (n+2) => rfl
    · intro k hk hne
      have hk2 : k < 2 := hk
      interval_cases k
      · refine ⟨?_, inC_C, ?_, ?_⟩
        · show (C (4:ℤ_[2])) ≠ 0
          exact C_ne_zero.mpr (by norm_num)
        · show bw (C 4) = ((1 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
          rw [bw_C4]; norm_num
        · have hgoal : bR (C 4) = (LaurentPolynomial.C (ψ₂.coeff 0)) *
              (LaurentPolynomial.T (- (0 : ℤ) * bw (C 4)) : LaurentPolynomial ↥K2) := by
            rw [bR_C4, ψ₂_coeff_zero, map_one, neg_zero, zero_mul,
              LaurentPolynomial.T_zero, one_mul]
          exact hgoal
      · refine ⟨?_, inC_C, ?_, ?_⟩
        · show (C (2:ℤ_[2])) ≠ 0
          exact C_ne_zero.mpr two_ne_zero'
        · show bw (C 2) = ((1 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
          rw [bw_C2]; norm_num
        · have hgoal : bR (C 2) = (LaurentPolynomial.C (ψ₂.coeff 1)) *
              (LaurentPolynomial.T (- (0 : ℤ) * bw (C 2)) : LaurentPolynomial ↥K2) := by
            rw [bR_C2, ψ₂_coeff_one, map_one, neg_zero, zero_mul,
              LaurentPolynomial.T_zero, one_mul]
          exact hgoal
    · show fq = X ^ (1 * 2) + ∑ k ∈ Finset.range 2,
        (if k = 0 then C 4 else if k = 1 then C 2 else 0) * X ^ (1 * k)
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [fq]
      ring

lemma sideReads_ν₀ : SideReads ν₀ Bdev 3 fq := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- (i) lower bound
    intro j hj hBj
    show (2 : ℤ) ≤ ((1 : ℕ) : ℤ) * bw (Bdev j) + (j : ℤ) * ((1 : ℕ) : ℤ)
    interval_cases j
    · rw [Bdev_w.1]; norm_num
    · rw [Bdev_w.2.1]; norm_num
    · rw [Bdev_w.2.2]; norm_num
  · -- (i) equality slots are stride slots
    intro j hj hBj heq
    refine ⟨j, ?_, ?_, ?_⟩
    · show j ≤ 2 / 1
      omega
    · show j = 0 + 1 * j
      omega
    · show (1 : ↥K2) ≠ 0
      exact one_ne_zero
  · -- (ii) digits
    intro k hk hpat
    have hk2 : k ≤ 2 := by
      have : k ≤ 2 / 1 := hk
      omega
    constructor
    · -- nonzero
      interval_cases k
      · show Bdev (0 + 1 * 0) ≠ 0
        show (C (4:ℤ_[2])) ≠ 0
        exact C_ne_zero.mpr (by norm_num)
      · show Bdev (0 + 1 * 1) ≠ 0
        show (C (2:ℤ_[2])) ≠ 0
        exact C_ne_zero.mpr two_ne_zero'
      · show Bdev (0 + 1 * 2) ≠ 0
        show (1 : Polynomial ℤ_[2]) ≠ 0
        exact one_ne_zero
    constructor
    · -- on the side
      interval_cases k
      · show ((1 : ℕ) : ℤ) * bw (Bdev (0 + 1 * 0)) + (((0 + 1 * 0 : ℕ)) : ℤ) * ((1 : ℕ) : ℤ) = 2
        show ((1 : ℕ) : ℤ) * bw (C 4) + (((0 : ℕ)) : ℤ) * ((1 : ℕ) : ℤ) = 2
        rw [bw_C4]; norm_num
      · show ((1 : ℕ) : ℤ) * bw (C 2) + (((1 : ℕ)) : ℤ) * ((1 : ℕ) : ℤ) = 2
        rw [bw_C2]; norm_num
      · show ((1 : ℕ) : ℤ) * bw 1 + (((2 : ℕ)) : ℤ) * ((1 : ℕ) : ℤ) = 2
        rw [bw_one]; norm_num
    · -- residual digit
      interval_cases k
      · have hgoal : bR (C 4) = (LaurentPolynomial.C (1 : ↥K2)) *
            (LaurentPolynomial.T (- (0 : ℤ) * bw (C 4)) : LaurentPolynomial ↥K2) := by
          rw [bR_C4, map_one, neg_zero, zero_mul, LaurentPolynomial.T_zero, one_mul]
        exact hgoal
      · have hgoal : bR (C 2) = (LaurentPolynomial.C (1 : ↥K2)) *
            (LaurentPolynomial.T (- (0 : ℤ) * bw (C 2)) : LaurentPolynomial ↥K2) := by
          rw [bR_C2, map_one, neg_zero, zero_mul, LaurentPolynomial.T_zero, one_mul]
        exact hgoal
      · have hgoal : bR 1 = (LaurentPolynomial.C (1 : ↥K2)) *
            (LaurentPolynomial.T (- (0 : ℤ) * bw 1) : LaurentPolynomial ↥K2) := by
          rw [bR_one, map_one, neg_zero, zero_mul, LaurentPolynomial.T_zero, one_mul]
        exact hgoal
  · -- (iii) anchor
    show HasAnchorK (bR (∑ j ∈ Finset.range 3, Bdev j * X ^ j)) 0 ψ₂
    have hsum : (∑ j ∈ Finset.range 3, Bdev j * X ^ j) = fq := Bdev_dev.2.2.symm
    rw [hsum]
    constructor
    · rw [ψ₂_coeff_zero]
      exact one_ne_zero
    · rw [bR_eq NF_θ_fq, map_ρ_q₁, LaurentPolynomial.T_zero, one_mul]
      rfl
  · -- (iii) ψ-order
    show OrdPsiPoly ψ₂ ψ₂ 1
    constructor
    · rw [pow_one]
    · intro hdvd
      have h1 := Polynomial.natDegree_le_of_dvd hdvd ψ₂_ne_zero
      rw [Polynomial.natDegree_pow, ψ₂_natDegree] at h1
      omega
  · -- (iv) landing key (extracted standalone at N-4 — see `landingKey_ν₀`)
    exact landingKey_ν₀
  · -- (v) polOM lift
    have hno : ¬ ∃ tL, RecenterLiftSpec ν₀ tL := by
      rintro ⟨tL, _, htne, _, hR⟩
      have hzero : (LaurentPolynomial.C ((0 : ↥K2))) *
          (LaurentPolynomial.T (0 : ℤ) : LaurentPolynomial ↥K2) = 0 := by
        rw [map_zero, zero_mul]
      exact bR_ne tL htne (hR.trans hzero)
    show ν₀.lift = (polOM 2 F4).liftOf ν₀
    have hlift : (polOM 2 F4).liftOf ν₀ = 0 := by
      classical
      show (if h : ∃ tL, RecenterLiftSpec ν₀ tL then h.choose else 0) = 0
      rw [dif_neg hno]
    rw [hlift]
    rfl
  · -- (v) canonical root
    show r₀ = canonRoot ν₀
    exact canonRoot_ν₀.symm
  · -- (vi) VERTEX READ-OFF [N-4 GATE RE-RUN, EXECUTED 2026-07-28 remediation round —
    -- blueprint §9 F-3(c)'s MANDATORY re-proof, discharged exactly along the queued
    -- sketch: Fact-B uniqueness of Φ-adic developments at the key `fq` gives `Bh 1 = 1`,
    -- so `digPrime zbar (Bh 1) = eval₂ (bR 1) = 1`; and `vtx ν₀ = z̄^(a − μ·m̂)·vtxPoly(z̄)
    -- = z̄⁰·((ψ₂ /ₘ ψ₂¹) %ₘ ψ₂)(z̄) = 1` (a = 0, t = 0 ⟹ m̂ = 0; 1 %ₘ ψ₂ = 1 at
    -- deg ψ₂ = 2). The concrete witness DISCHARGES the clause: NOT over-strengthened.
    intro Bh Nh hdev
    -- the recorded window sum IS fq, so Bh is a development of fq at the key fq
    have hdev' : IsDevelopment fq fq Bh Nh := by
      have hdev2 : IsDevelopment fq
          (∑ j ∈ Finset.range 3, Bdev j * (X : Polynomial ℤ_[2]) ^ j) Bh Nh := hdev
      rwa [← Bdev_dev.2.2] at hdev2
    have hfq_deg : fq.degree = 2 := by
      rw [Polynomial.degree_eq_natDegree fq_monic.ne_zero, fq_natDegree]
      rfl
    -- the canonical development: fq = 0·fq⁰ + 1·fq¹
    have hcanon : IsDevelopment fq fq (fun j => if j = 1 then 1 else 0) 2 := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = 1
        · simp only [hj, if_pos]
          rw [hfq_deg]
          exact lt_of_le_of_lt degree_one_le (by norm_num)
        · simp only [if_neg hj]
          rw [degree_zero, hfq_deg]
          decide
      · intro j hj
        have hj1 : j ≠ 1 := by omega
        simp [hj1]
      · rw [Finset.sum_range_succ, Finset.sum_range_one]
        norm_num
    -- Fact B (`L0_FactB_unique`): the vertex slot of ANY development is the canonical one
    have hBh1 : Bh 1 = 1 := by
      have h := L0_FactB_unique fq fq_monic fq hdev' hcanon 1
      simpa using h
    -- the transported vertex value is 1
    have hψ₂_deg : ψ₂.degree = 2 := by
      rw [Polynomial.degree_eq_natDegree ψ₂_ne_zero, ψ₂_natDegree]
      rfl
    have hvp : ν₀.vtxPoly = 1 := by
      have hdiv : ψ₂ /ₘ ψ₂ = 1 := by
        have h := Polynomial.mul_divByMonic_cancel_left (1 : Polynomial ↥K2) ψ₂_monic
        rwa [mul_one] at h
      have hmod : (1 : Polynomial ↥K2) %ₘ ψ₂ = 1 := by
        refine (Polynomial.modByMonic_eq_self_iff ψ₂_monic).mpr ?_
        rw [Polynomial.degree_one, hψ₂_deg]
        decide
      have h0 : ν₀.vtxPoly = (ψ₂ /ₘ ψ₂ ^ 1) %ₘ ψ₂ := rfl
      rw [h0, pow_one, hdiv, hmod]
      rfl
    have hexp : ν₀.a - (ν₀.μ : ℤ) * ν₀.mhat = 0 := by
      have hmh : ν₀.mhat = 0 := by
        show -ν₀.t * (ν₀.h : ℤ) * (ν₀.g : ℤ) = 0
        have ht : ν₀.t = 0 := rfl
        rw [ht]
        ring
      have ha : ν₀.a = 0 := rfl
      rw [ha, hmh, mul_zero, sub_zero]
    have hvtx : ν₀.vtx = 1 := by
      unfold Node.vtx
      rw [hvp, Polynomial.eval₂_one, mul_one, hexp, zpow_zero, Units.val_one]
    show ν₀.σ.digPrime ν₀.zbar (Bh 1) = ν₀.vtx
    rw [hBh1, hvtx]
    show LaurentPolynomial.eval₂ K2.subtype ν₀.zbar (bR 1) = 1
    rw [bR_one]
    exact map_one _

/-! ### ReadsOf -/

private lemma readsOf_fq : ReadsOf 2 F4 2 fq H₀ := by
  refine ⟨fq_monic, fq_natDegree, coherent_H₀, ?_⟩
  intro i hi
  have hi1 : i < 1 := hi
  have hi0 : i = 0 := by omega
  subst hi0
  refine ⟨Bdev, 3, fq, ?_, ?_, ?_⟩
  · show IsDevelopment (X : Polynomial ℤ_[2]) fq Bdev 3
    exact Bdev_dev
  · intro h1
    have h2 : (1 : ℕ) < 1 := h1
    exact absurd h2 (by omega)
  · show SideReads ν₀ Bdev 3 fq
    exact sideReads_ν₀

end U31

/-- GATE: `ReadsOf` is INHABITED on concrete order-0 data — the root-only inert history
at p = 2, n = 2, with a concrete monic quadratic run on it. -/
theorem gate_readsOf_inert2 :
    ∃ (H₀ : History 2 F4) (f : Polynomial ℤ_[2]),
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ReadsOf 2 F4 2 f H₀ := by
  refine ⟨U31.H₀, U31.fq, rfl, ?_, U31.readsOf_fq⟩
  intro h0
  exact ⟨rfl, rfl, rfl⟩

end LeanUrat.MovesJ
