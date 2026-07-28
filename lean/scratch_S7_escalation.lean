/- ESCALATION SCRATCH for HC1.S7_childPin (2026-07-28). Not part of the build. -/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSvii_R4
import LeanUrat.Moves.L5_recVV_R4
import LeanUrat.Moves.L2_keyResidualPow

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! Units-of-Laurent arithmetic (as in MovesGr/L2_coeffLoc_v2, re-derived: those are private). -/

private lemma tUnit_val' (R : Type*) [CommRing R] (a : ℤ) :
    ((tUnit R a : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T a := rfl

private lemma tUnit_mul' (R : Type*) [CommRing R] (a b : ℤ) :
    tUnit R a * tUnit R b = tUnit R (a + b) := by
  apply Units.ext
  show LaurentPolynomial.T a * LaurentPolynomial.T b = LaurentPolynomial.T (a + b)
  rw [LaurentPolynomial.T_add]

private lemma tUnit_zero' (R : Type*) [CommRing R] : tUnit R 0 = 1 := by
  apply Units.ext
  show LaurentPolynomial.T 0 = 1
  rw [LaurentPolynomial.T_zero]

private lemma tUnit_inv' (R : Type*) [CommRing R] (a : ℤ) :
    (tUnit R a)⁻¹ = tUnit R (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tUnit_mul', add_neg_cancel, tUnit_zero']

private lemma tUnit_zpow' (R : Type*) [CommRing R] (n : ℤ) : ∀ m : ℤ,
    (tUnit R n) ^ m = tUnit R (n * m) := by
  intro m
  induction m using Int.induction_on with
  | zero => rw [mul_zero, zpow_zero, tUnit_zero']
  | succ k ih => rw [zpow_add_one, ih, tUnit_mul']; congr 1; ring
  | pred k ih => rw [zpow_sub_one, ih, tUnit_inv', tUnit_mul']; congr 1; ring

/-! The weight-detecting evaluation (L2_coeffLoc_v2's Ein/Eout, re-derived). -/

private noncomputable def Ein (σ : Stage p F) :
    LaurentPolynomial ↥σ.K →+* LaurentPolynomial ↥σ.K :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (tUnit ↥σ.K (σ.e : ℤ))

private noncomputable def Eout (σ : Stage p F) :
    LTwo ↥σ.K →+* LaurentPolynomial ↥σ.K :=
  LaurentPolynomial.eval₂ (Ein σ) (tUnit ↥σ.K σ.t)

private lemma Ein_apply (σ : Stage p F) (y : LaurentPolynomial ↥σ.K) :
    Ein σ y = LaurentPolynomial.eval₂ LaurentPolynomial.C (tUnit ↥σ.K (σ.e : ℤ)) y := rfl

private lemma Eout_apply (σ : Stage p F) (y : LTwo ↥σ.K) :
    Eout σ y = LaurentPolynomial.eval₂ (Ein σ) (tUnit ↥σ.K σ.t) y := rfl

private lemma Eout_grRes (σ : Stage p F) {B : Polynomial ℤ_[p]} (hB0 : B ≠ 0)
    (hBC : inC σ.Φ B) :
    ∃ c : (↥σ.K)ˣ, Eout σ (σ.grRes B) = LaurentPolynomial.C (c : ↥σ.K) ∧
      σ.R B = LaurentPolynomial.C (c : ↥σ.K) * LaurentPolynomial.T (- σ.t * σ.wPrev B) := by
  obtain ⟨c, hc⟩ := σ.hS5 B hB0 hBC
  refine ⟨c, ?_, hc⟩
  have hgr : σ.grRes B = LaurentPolynomial.C (σ.R B) * LaurentPolynomial.T (σ.w B) := rfl
  rw [hgr, hc, Eout_apply, LaurentPolynomial.eval₂_C_mul_T, Ein_apply,
    LaurentPolynomial.eval₂_C_mul_T]
  simp only [tUnit_zpow', tUnit_val']
  rw [σ.hStretch B hB0 hBC, mul_assoc, ← LaurentPolynomial.T_add]
  have h0 : (σ.e : ℤ) * (- σ.t * σ.wPrev B) + σ.t * ((σ.e : ℤ) * σ.wPrev B) = 0 := by ring
  rw [h0, LaurentPolynomial.T_zero, mul_one]

private lemma coeffLoc_le (σ : Stage p F) :
    σ.coeffLocSR ≤ Subring.comap (Eout σ)
      (LaurentPolynomial.C : ↥σ.K →+* LaurentPolynomial ↥σ.K).range := by
  refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
  · rintro x ⟨B, hB0, hBC, rfl⟩
    obtain ⟨c, hc, -⟩ := Eout_grRes σ hB0 hBC
    exact Subring.mem_comap.mpr (RingHom.mem_range.mpr ⟨_, hc.symm⟩)
  · rintro x ⟨i, u, hu, rfl⟩
    obtain ⟨hr0, hrC⟩ := σ.hreps (σ.reps.get i) (List.get_mem _ _)
    obtain ⟨c, hc, -⟩ := Eout_grRes σ hr0 hrC
    have hu' : (u : LTwo ↥σ.K) = σ.grRes (σ.reps.get i) := hu
    have hval : Eout σ (u : LTwo ↥σ.K)
        = LaurentPolynomial.C (c : ↥σ.K) := by rw [hu']; exact hc
    refine Subring.mem_comap.mpr (RingHom.mem_range.mpr
      ⟨((c⁻¹ : (↥σ.K)ˣ) : ↥σ.K), ?_⟩)
    have h2 : LaurentPolynomial.C ((c⁻¹ : (↥σ.K)ˣ) : ↥σ.K)
        * LaurentPolynomial.C (c : ↥σ.K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h1 : LaurentPolynomial.C (c : ↥σ.K)
        * Eout σ ((u⁻¹ : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) = 1 := by
      rw [← hval, ← map_mul, Units.mul_inv, map_one]
    exact left_inv_eq_right_inv h2 h1

private lemma Ein_eq_mapDomainRingHom (σ : Stage p F) :
    Ein σ = AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    have hb : (AddMonoidAlgebra.single (0 : ℤ) r : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.C r := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
    have h00 : (AddMonoidHom.mulLeft (σ.e : ℤ)) 0 = (0 : ℤ) := mul_zero _
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, h00,
      hb, Ein_apply, LaurentPolynomial.eval₂_C]
  · intro m
    have hb1 : (AddMonoidAlgebra.single m (1 : ↥σ.K) : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.T m := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    have h0m : (AddMonoidHom.mulLeft (σ.e : ℤ)) m = (σ.e : ℤ) * m := rfl
    have hb2 : (AddMonoidAlgebra.single ((σ.e : ℤ) * m) (1 : ↥σ.K) : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.T ((σ.e : ℤ) * m) := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, h0m,
      hb1, hb2, Ein_apply, LaurentPolynomial.eval₂_T, tUnit_zpow', tUnit_val']

/-- CoeffLocLaw conjunct (a) holds for EVERY stage, from bare `Stage` laws
(hS5 + hStretch + hreps + he) — L2_coeffLoc_v2's proved leg, restated openly. -/
private lemma coeffLocLaw_sub (σ : Stage p F) :
    ∀ ℓ : LaurentPolynomial ↥σ.K, LaurentPolynomial.C ℓ ∈ σ.coeffLocSR →
      ∃ d : ↥σ.K, ℓ = LaurentPolynomial.C d := by
  intro ℓ hℓ
  have hmem := coeffLoc_le σ hℓ
  rw [Subring.mem_comap, RingHom.mem_range] at hmem
  obtain ⟨d0, hd0⟩ := hmem
  have hEC : Eout σ (LaurentPolynomial.C ℓ) = Ein σ ℓ := by
    rw [Eout_apply, LaurentPolynomial.eval₂_C]
  have hd : Ein σ ℓ = LaurentPolynomial.C d0 := by rw [← hEC, ← hd0]
  have hs0 : (AddMonoidAlgebra.single (0 : ℤ) d0 : LaurentPolynomial ↥σ.K)
      = LaurentPolynomial.C d0 := by
    rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
  have hinj : Function.Injective (⇑(AddMonoidHom.mulLeft (σ.e : ℤ))) := by
    intro a b hab
    have he : (σ.e : ℤ) ≠ 0 :=
      Int.natCast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp σ.he)
    exact mul_left_cancel₀ he hab
  have hinj2 : Function.Injective
      (⇑(AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)))) := by
    intro x y hxy
    refine AddMonoidAlgebra.mapDomain_injective hinj ?_
    simpa [AddMonoidAlgebra.mapDomainRingHom_apply] using hxy
  have h4 : (AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ))) ℓ
      = (AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)))
          (AddMonoidAlgebra.single (0 : ℤ) d0) := by
    rw [← Ein_eq_mapDomainRingHom, hd, hs0, Ein_apply, LaurentPolynomial.eval₂_C]
  exact ⟨d0, by rw [hinj2 h4, hs0]⟩

/-! ## Conjunct (b): every K′-constant lies in the child coefficient localization.

NEW ROUTE (the first prover declared this leg open): the child rep list contains the
OUTGOING KEY `σ.Φ` (child_reps), whose child parent-scale weight is `σ.h ≥ 1`
(child_wPrev + hwΦ) — a rep of strictly POSITIVE weight. So `k` copies of it reach any
weight above the (S6b′) threshold; an (S6b′) realizer with scalar `d·c_Φ^k` at weight
`k·σ.h`, times the k-th power of the σ.Φ rep-unit INVERSE (a coeffLocSR generator),
is exactly `C (C d)`. Uses only σ'.hS6b, σ'.hS5, σ'.hreps, σ'.hStretch + the
transition record — no construction data. -/

private lemma cUnit_val (K : Type*) [CommRing K] (c : Kˣ) :
    ((Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom c :
      (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = LaurentPolynomial.C (c : K) := rfl

/-- `C (C dd) · (C (C cc · T m) · T w)^n = C (C (dd·cc^n) · T (n·m)) · T (n·w)` — the
outer-cancel identity used by conjunct (b), abstract form. -/
private lemma CT_cancel (K : Type*) [Field K] (dd cc : K) (m w : ℤ) (n : ℕ) :
    (LaurentPolynomial.C (LaurentPolynomial.C dd) : LTwo K) *
      ((LaurentPolynomial.C (LaurentPolynomial.C cc * LaurentPolynomial.T m) *
        LaurentPolynomial.T w) ^ n)
    = LaurentPolynomial.C (LaurentPolynomial.C (dd * cc ^ n) *
        LaurentPolynomial.T ((n : ℤ) * m)) * LaurentPolynomial.T ((n : ℤ) * w) := by
  calc (LaurentPolynomial.C (LaurentPolynomial.C dd) : LTwo K) *
        ((LaurentPolynomial.C (LaurentPolynomial.C cc * LaurentPolynomial.T m) *
          LaurentPolynomial.T w) ^ n)
      = LaurentPolynomial.C (LaurentPolynomial.C dd) *
          (LaurentPolynomial.C ((LaurentPolynomial.C cc * LaurentPolynomial.T m) ^ n) *
            LaurentPolynomial.T ((n : ℤ) * w)) := by
        rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]
    _ = LaurentPolynomial.C (LaurentPolynomial.C dd) *
          (LaurentPolynomial.C (LaurentPolynomial.C (cc ^ n) *
            LaurentPolynomial.T ((n : ℤ) * m)) * LaurentPolynomial.T ((n : ℤ) * w)) := by
        rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]
    _ = LaurentPolynomial.C (LaurentPolynomial.C dd *
          (LaurentPolynomial.C (cc ^ n) * LaurentPolynomial.T ((n : ℤ) * m))) *
            LaurentPolynomial.T ((n : ℤ) * w) := by
        rw [← mul_assoc, ← map_mul]
    _ = LaurentPolynomial.C (LaurentPolynomial.C (dd * cc ^ n) *
          LaurentPolynomial.T ((n : ℤ) * m)) * LaurentPolynomial.T ((n : ℤ) * w) := by
        rw [← mul_assoc, ← map_mul]

private lemma coeffLocLaw_sup (σ σ' : Stage p F) {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
    {zbar : Fˣ} (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    ∀ d : ↥σ'.K, LaurentPolynomial.C (LaurentPolynomial.C d) ∈ σ'.coeffLocSR := by
  intro d
  by_cases hd : d = 0
  · subst hd
    simp only [map_zero]
    exact σ'.coeffLocSR.zero_mem
  -- the outgoing key is a child rep of parent-scale weight σ.h ≥ 1
  have hΦmem : σ.Φ ∈ σ'.reps := by
    rw [tc.base.child_reps]; exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨i₀, hi₀⟩ := List.get_of_mem hΦmem
  obtain ⟨hΦne, hΦC⟩ := σ'.hreps σ.Φ hΦmem
  obtain ⟨cΦ, hcΦ⟩ := σ'.hS5 σ.Φ hΦne hΦC
  have hνΦ : σ'.wPrev σ.Φ = (σ.h : ℤ) := by rw [tc.base.child_wPrev, σ.hwΦ]
  -- the σ.Φ rep-unit
  set uin : (LaurentPolynomial ↥σ'.K)ˣ :=
    (Units.map (LaurentPolynomial.C : ↥σ'.K →+* LaurentPolynomial ↥σ'.K).toMonoidHom cΦ)
      * tUnit ↥σ'.K (- σ'.t * σ'.wPrev σ.Φ) with huin
  set u : (LTwo ↥σ'.K)ˣ :=
    (Units.map (LaurentPolynomial.C :
        LaurentPolynomial ↥σ'.K →+* LTwo ↥σ'.K).toMonoidHom uin)
      * tUnit (LaurentPolynomial ↥σ'.K) (σ'.w σ.Φ) with hu
  have huval : (u : LTwo ↥σ'.K)
      = LaurentPolynomial.C (LaurentPolynomial.C (cΦ : ↥σ'.K)
          * LaurentPolynomial.T (- σ'.t * σ'.wPrev σ.Φ))
        * LaurentPolynomial.T (σ'.w σ.Φ) := rfl
  have hgru : IsGrUnit σ' (σ'.reps.get i₀) u := by
    show (u : LTwo ↥σ'.K) = σ'.grRes (σ'.reps.get i₀)
    rw [hi₀, huval, Stage.grRes, hcΦ]
  -- the rep-unit inverse is a coeffLocSR generator
  have hxmem : ((u⁻¹ : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) ∈ σ'.coeffLocSR :=
    Subring.subset_closure (Or.inr ⟨i₀, u, hgru, rfl⟩)
  -- the weight window: k·σ.h clears the (S6b′) threshold
  set θ : ℤ := σ'.wPrev σ'.Φ with hθ
  set k : ℕ := θ.toNat + 1 with hk
  have hν : θ < (k : ℤ) * σ'.wPrev σ.Φ := by
    rw [hνΦ]
    have h1 : (1 : ℤ) ≤ (σ.h : ℤ) := by exact_mod_cast σ.hh
    have h2 : θ < (k : ℤ) := by
      calc θ ≤ (θ.toNat : ℤ) := Int.self_le_toNat θ
        _ < (θ.toNat : ℤ) + 1 := by omega
        _ = (k : ℤ) := by rw [hk]; push_cast; ring
    calc θ < (k : ℤ) := h2
      _ = (k : ℤ) * 1 := (mul_one _).symm
      _ ≤ (k : ℤ) * (σ.h : ℤ) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
  -- the (S6b′) realizer with scalar d·cΦ^k
  obtain ⟨B, hB0, hBC, hwB, hRB⟩ :=
    σ'.hS6b ((k : ℤ) * σ'.wPrev σ.Φ) (Units.mk0 d hd * cΦ ^ k) hν
  have hgmem : σ'.grRes B ∈ σ'.coeffLocSR :=
    Subring.subset_closure (Or.inl ⟨B, hB0, hBC, rfl⟩)
  -- the value identity: grRes B = C (C d) · u^k
  have hwB' : σ'.w B = (σ'.e : ℤ) * ((k : ℤ) * σ'.wPrev σ.Φ) := by
    rw [σ'.hStretch B hB0 hBC, hwB]
  have hwΦ' : σ'.w σ.Φ = (σ'.e : ℤ) * σ'.wPrev σ.Φ := σ'.hStretch σ.Φ hΦne hΦC
  have haval : ((Units.mk0 d hd * cΦ ^ k : (↥σ'.K)ˣ) : ↥σ'.K) = d * (cΦ : ↥σ'.K) ^ k := by
    simp
  have harg1 : - σ'.t * ((k : ℤ) * σ'.wPrev σ.Φ) = (k : ℤ) * (- σ'.t * σ'.wPrev σ.Φ) := by
    ring
  have harg2 : (σ'.e : ℤ) * ((k : ℤ) * σ'.wPrev σ.Φ)
      = (k : ℤ) * ((σ'.e : ℤ) * σ'.wPrev σ.Φ) := by ring
  have hE : σ'.grRes B
      = LaurentPolynomial.C (LaurentPolynomial.C d) * ((u ^ k : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) := by
    rw [Units.val_pow_eq_pow_val, huval, Stage.grRes, hRB, hwB', hwΦ', CT_cancel,
      haval, harg1, harg2]
  have hfinal : LaurentPolynomial.C (LaurentPolynomial.C d)
      = σ'.grRes B * (((u⁻¹ : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K)) ^ k := by
    rw [hE, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow,
      mul_inv_cancel, Units.val_one, mul_one]
  rw [hfinal]
  exact Subring.mul_mem _ hgmem (Subring.pow_mem _ hxmem k)

theorem S7_scratch (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    ((e' : ℤ) * σ'.s + (h' : ℤ) * σ'.t = 1 ∧ (e' = 1 → σ'.t = 0)) ∧
    (∀ B : Polynomial ℤ_[p], B ≠ 0 → inC Φhat B →
      ∃ c' : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C ((c' : ↥σ'.K)) *
        LaurentPolynomial.T (- σ'.t * σ.w B)) ∧
    CoeffLocLaw σ' := by
  obtain ⟨mfun, hdig⟩ := tc.child_dig_frame
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- Bézout at the child read indices
    rw [← tc.base.child_e, ← tc.base.child_h]; exact σ'.hbez
  · -- (P2) e' = 1 pinning
    intro h1; exact σ'.he1t (tc.base.child_e.trans h1)
  · -- (S5′): child digits are monomial units at the forced positions
    intro B hB0 hBC
    obtain ⟨c', hc', -⟩ := hdig B hB0 hBC
    exact ⟨c', hc'⟩
  · -- CoeffLocLaw (a): (L^coeff)₀ ⊆ K′
    exact coeffLocLaw_sub σ'
  · -- CoeffLocLaw (b): (L^coeff)₀ ⊇ K′
    exact coeffLocLaw_sup σ σ' tc
  · -- CoeffLocLaw (c): the z′-pin — OBSTRUCTION (escalation pass, 2026-07-28).
    -- Decoding the clause (units pinned by value via `IsGrUnit`; `zvar = T 1`): a witness
    -- `(zv, u)` has value
    --   C (C (∏ᵢ cᵢ^{vᵢ}) · T (−σ'.t·N + σ'.s·v₂)) · T (σ'.e·N + σ'.h·v₂),
    -- with `N := Σᵢ vᵢ·σ'.wPrev(repᵢ)` and `cᵢ` the child hS5 scalars of `σ'.reps`.
    -- Equality with `C (T 1)` forces (det [[e',h'],[−t',s']] = hbez = 1) the UNIQUE
    -- solution `(N, v₂) = (−h', e')`, leaving exactly:
    --   (⋆)  ∃ v : Σᵢ vᵢ·σ'.wPrev(repᵢ) = −h'  ∧  ∏ᵢ cᵢ^{vᵢ} = 1.
    -- The weight leg of (⋆) is always solvable: the transported vector b := (parent Tvec
    -- exponents, σ.t) has Σ b·ν = (1 − σ.t·σ.h) + σ.t·σ.h = 1 (parent tvec_unit decodes to
    -- Σ aᵢ·σ.wPrev(uᵢ) = σ.s + hStretch), so v₀ := −h'·b reaches −h'. But its scalar is
    -- S^{−h'} with S := ∏ cᵢ^{bᵢ}, and via `child_dig_frame` + the parent scalar laws
    -- (∏ dᵢ^{aᵢ} = 1 from tvec_unit, digPrime cancellation) one gets S = z̄^E with
    --   E := Σⱼ bⱼ·mfun(σ.w uⱼ) + σ.t·mfun(σ.h)
    -- — LITERALLY the same uncontrolled frame twist as the dual-audited S8 obstruction
    -- (S8_childS6.lean: TvecUnitLaw σ' ⟺ z̄^{σ'.s·E} = 1); here (⋆) ⟺ z̄^{h'·E} ∈ the
    -- subgroup reachable by weight-0 rep vectors. `mfun : ℤ → ℤ` is only existentially
    -- supplied with unpinned values, `σ'` carries only bare `Stage` laws, and no other
    -- hypothesis touches the rep scalars. Same honest fix, UPSTREAM: pin `child_dig_frame`'s
    -- `mfun` (the D.7(vi) z̄-normalization) or record the z′-pin/T′-law as transition data.
    -- NOTE (this pass, machine-checked above): conjuncts (a) AND (b) are both provable —
    -- (b) via σ'.hS6b at weight k·σ.h ≥ threshold+1 against the σ.Φ rep-unit inverse —
    -- so the S7 wall is EXACTLY (⋆), nothing else.
    sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.coeffLocLaw_sub
#print axioms LeanUrat.HC1.coeffLocLaw_sup
