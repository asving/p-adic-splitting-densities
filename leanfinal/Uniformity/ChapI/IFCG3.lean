/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG1
import Uniformity.ChapH.H115
import Uniformity.ChapI.IFC7
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapI.IFCG3 — [A0G4 2026-08-28] the generic rescale loop + the scalar
fixed-point solver (nodes A0G-RS + A0G-FP)

**Uniform-a0 campaign, NODES A0G-RS and A0G-FP**
(`docs/in-progress/A0_GENERAL_2026-08-28.md` §§3.2, 5 and the §6 rows).

## Node A0G-RS — the generic rescale loop

The size-`m` all-at-one-point rational cluster substitutes `X = πY`. This file builds the
degree-generic version of that substitution:

* `scaleVecN π f` — the coefficient vector of `F_f(X/π)·π^m`, i.e. `(monicPoly f).scaleRoots π`
  in vector form (`monicPoly_scaleVecN_eq_scaleRoots`); typeOf-diagonal via the LANDED
  `typeOf_scaleRoots` (`typeOf_scaleVecN`);
* `loopVecN π d` — `scaleVecN` applied to a canonical lift of a mixed-precision box element
  `d : IFCG1.MBoxN O m M` (the just-landed A0G-CV bank); its class-level INJECTIVITY
  (`loopVecN_inj`) and `DecidedAt`-transport (`decidedAt_of_loopVecN`);
* `loopMapN γ π d` — `loopVecN` composed with the LANDED `shiftVecN` recentring at a lift of
  the residue centre `γ`; **the generic loop bijection**: `loopMapN_inj` is injective in BOTH
  `γ` and `d` simultaneously, in EVERY residue characteristic (no wild-prime exclusion) — the
  γ-recovery uses a characteristic-free polynomial-evaluation argument
  (`addC_pow_injective`), not binomial-coefficient inversion, which is what would fail at
  wild primes;
* the two weight formulas of A0 plan §3.2: `kappaLoop m = m(m−1)/2` (the coefficient-loss
  exponent, a direct restatement of `IFCG1.card_MBoxN`'s excess exponent) and
  `bigTLoop m = m(m+1)/2` (the full-box exponent), with the arithmetic identity
  `bigTLoop_eq_kappaLoop_add` and the cardinality identity `loopVecN_weight` (the
  subtraction-free form of "the full-box loop weight is `q^(1−T_m)`"); machine pins at
  `m = 2, 3, 4`, and `bigTLoop_three_eq_five_recovery` states the recovery of IFC7's hard-coded
  `q^{-5}` step as the `m = 3` instance (`1 − T_3 = -5`).

## Node A0G-FP — the generic scalar fixed-point solver

`decidedDensity_ge_of_step` generalizes `IFC7.density_ge_of_step` from the hard-coded shift `3`
and exponent `5` to an arbitrary shift `s` and exponent `d > 0`, at an arbitrary degree `n`
(already generic in `GenuineDensity.decidedSeq_tendsto`). `decidedDensity_eq_of_step_eq`
strengthens the conclusion to an EQUALITY when the step hypothesis itself is an equality — "the
direct equality at the decided-density limit" the row asks for. `fixedPoint_unique` is the
underlying pure-algebra uniqueness fact for the scalar recurrence `D = b + y·D`. **No
`DrainageAt` appears anywhere in this section**; denominator positivity comes only from
`q ≥ 2` (`two_le_residueCard`) and `d > 0`.

**⚠ TRUST BOUNDARY.** Every `theorem`/`def` here is NEW and flagged for the standing review;
zero `sorry` intended, zero new axiom; AxCheck footer expects Lean core only. No landed file is
touched; every landed name (`IFCG1.*`, `IFC7.resOut`/`mk_resOut`, `Induction.resSect`,
`Hensel.*`, `GenuineDensity.*`, `TypeOfInvariance.typeOf_scaleRoots`) is consumed as-is.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG3

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.IFCG1
open Uniformity.Density.Induction (resSect residue_resSect)
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Hensel (mem_coeffIdeal sub_mem_coeffIdeal_maximalIdeal_iff)

/-! ## §1 The exponents `κ_m`, `T_m` (A0 plan §3.2) -/

section Exponents

/-- **The coefficient-loss exponent** `κ_m = m(m−1)/2`. -/
def kappaLoop (m : ℕ) : ℕ := m * (m - 1) / 2

/-- **The full-box loop exponent** `T_m = m(m+1)/2`. -/
def bigTLoop (m : ℕ) : ℕ := m * (m + 1) / 2

theorem kappaLoop_eq_sum (m : ℕ) : kappaLoop m = ∑ i ∈ Finset.range m, i :=
  (Finset.sum_range_id m).symm

theorem bigTLoop_eq_sum (m : ℕ) : bigTLoop m = ∑ i ∈ Finset.range (m + 1), i := by
  rw [Finset.sum_range_id]
  unfold bigTLoop
  rw [show m + 1 - 1 = m from by omega, Nat.mul_comm (m + 1) m]

theorem kappaLoop_zero : kappaLoop 0 = 0 := by decide
theorem kappaLoop_two : kappaLoop 2 = 1 := by decide
theorem kappaLoop_three : kappaLoop 3 = 3 := by decide
theorem kappaLoop_four : kappaLoop 4 = 6 := by decide

theorem bigTLoop_two : bigTLoop 2 = 3 := by decide
theorem bigTLoop_three : bigTLoop 3 = 6 := by decide
theorem bigTLoop_four : bigTLoop 4 = 10 := by decide

/-- **`T_m = κ_m + m`** — the full-box exponent counts the conditional loss PLUS the one extra
choice of common residue centre. -/
theorem bigTLoop_eq_kappaLoop_add (m : ℕ) : bigTLoop m = kappaLoop m + m := by
  rw [bigTLoop_eq_sum, kappaLoop_eq_sum, Finset.sum_range_succ]

/-- **`κ_m + T_m = m²`** — the arithmetic fact behind `loopVecN_weight`. -/
theorem kappaLoop_add_bigTLoop (m : ℕ) : kappaLoop m + bigTLoop m = m * m := by
  rw [bigTLoop_eq_kappaLoop_add]
  have h2 : kappaLoop m * 2 = m * (m - 1) := by
    rw [kappaLoop_eq_sum]; exact Finset.sum_range_id_mul_two m
  rcases m with _ | m
  · decide
  · have hm1 : (m + 1) - 1 = m := by omega
    rw [hm1] at h2
    nlinarith [h2]

/-- **The gate recovery**: at `m = 3`, `1 − T_3 = -5` — IFC7's hard-coded exponent. -/
theorem bigTLoop_three_recovery : (1 : ℤ) - (bigTLoop 3 : ℤ) = -5 := by
  rw [bigTLoop_three]; norm_num

end Exponents

/-! ## §2 The scale step: `scaleVecN`, `loopVecN`, injectivity, `DecidedAt`-transport -/

section LoopVec

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The bare rescale**: `X = πY` on a coefficient vector, no box/precision structure. -/
def scaleVecN {m : ℕ} (π : O) (f : Fin m → O) : Fin m → O :=
  fun i => π ^ (m - (i : ℕ)) * f i

theorem monicPoly_scaleVecN_eq_scaleRoots {m : ℕ} (π : O) (f : Fin m → O) :
    monicPoly (scaleVecN π f) = (monicPoly f).scaleRoots π := by
  have hmonic : ((monicPoly f).scaleRoots π).Monic := (monic_scaleRoots_iff π).2 (monicPoly_monic f)
  have hdeg : ((monicPoly f).scaleRoots π).natDegree = m := by
    rw [natDegree_scaleRoots]; exact monicPoly_natDegree f
  obtain ⟨a, ha⟩ := exists_monicPoly_eq hmonic hdeg
  have hveq : scaleVecN π f = a := by
    funext i
    have h1 : a i = ((monicPoly f).scaleRoots π).coeff (i : ℕ) := by
      rw [← ha]; exact (monicPoly_coeff_lt a i.isLt).symm
    show π ^ (m - (i : ℕ)) * f i = a i
    rw [h1, coeff_scaleRoots, monicPoly_natDegree, monicPoly_coeff_lt f i.isLt]
    ring
  rw [hveq, ha]

/-- **Diagonal fact**: the rescale loop preserves `typeOf` — the direct consumption of the
landed `typeOf_scaleRoots`. -/
theorem typeOf_scaleVecN {π : O} (hπ : Irreducible π) {m : ℕ} (f : Fin m → O) :
    typeOf (monicPoly (scaleVecN π f)) = typeOf (monicPoly f) := by
  rw [monicPoly_scaleVecN_eq_scaleRoots]
  have h := typeOf_scaleRoots hπ (monicPoly_monic f) 1
  rwa [pow_one] at h

/-- Congruence mod `π` of the coefficients forces the same residue-field reduction of the
`monicPoly`s — the general engine behind every γ-recovery / decidedness-transport below. -/
theorem map_residue_monicPoly_congr {π : O} (hπ : Irreducible π) {n : ℕ} {a a' : Fin n → O}
    (h : ∀ i : Fin n, π ∣ (a' i - a i)) :
    Polynomial.map (residue O) (monicPoly a') = Polynomial.map (residue O) (monicPoly a) := by
  rw [← sub_mem_coeffIdeal_maximalIdeal_iff]
  refine mem_coeffIdeal.2 (fun k => ?_)
  rw [coeff_sub]
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [monicPoly_coeff_lt a' hk, monicPoly_coeff_lt a hk]
    exact (mem_maximalIdeal_iff_dvd hπ _).2 (h ⟨k, hk⟩)
  · subst hk
    have h1 := (monicPoly_monic a').coeff_natDegree
    have h2 := (monicPoly_monic a).coeff_natDegree
    rw [monicPoly_natDegree] at h1 h2
    rw [h1, h2, sub_self]
    exact Ideal.zero_mem _
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega), sub_self]
    exact Ideal.zero_mem _

variable [Finite (ResidueField O)]

/-- **The generic mixed-precision rescale loop vector**: `loopVecN π d` extracts the box
element `d : MBoxN O m M` (the just-landed IFCG1 CV bank) through a canonical lift and rescales
it. -/
def loopVecN {m M : ℕ} (π : O) (d : MBoxN O m M) : Fin m → O :=
  scaleVecN π (fun i => resOut (d i))

theorem typeOf_loopVecN {π : O} (hπ : Irreducible π) {m M : ℕ} (d : MBoxN O m M) :
    typeOf (monicPoly (loopVecN π d)) = typeOf (monicPoly (fun i : Fin m => resOut (d i))) :=
  typeOf_scaleVecN hπ _

theorem mkBoxN_resOut_self {m M : ℕ} (d : MBoxN O m M) :
    mkBoxN (O := O) m M (fun i => resOut (d i)) = d := by
  funext i; exact mk_resOut (d i)

/-- The cancellation lemma underlying both `loopVecN_inj` and `decidedAt_of_loopVecN`: two
rescaled vectors congruent mod `π^(M+m)` come from box records congruent mod the box's own
precision profile. -/
theorem mkBoxN_eq_of_scaleVecN_congr {π : O} (hπ : Irreducible π) {m M : ℕ} {f g : Fin m → O}
    (h : ∀ i : Fin m, π ^ (M + m) ∣ (scaleVecN π g i - scaleVecN π f i)) :
    mkBoxN (O := O) m M f = mkBoxN m M g := by
  refine (mkBoxN_eq_iff_dvd hπ).2 (fun i => ?_)
  have hi := i.isLt
  have heqexp : π ^ (M + m) = π ^ (m - (i : ℕ)) * π ^ (M + (i : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  have hstep : π ^ (m - (i : ℕ)) * π ^ (M + (i : ℕ)) ∣ π ^ (m - (i : ℕ)) * (g i - f i) := by
    rw [← heqexp, mul_sub]
    exact h i
  exact (mul_dvd_mul_iff_left (pow_ne_zero (m - (i : ℕ)) hπ.ne_zero)).mp hstep

/-- **The generic loop bijection, scale-only part**: `loopVecN` is injective on box classes. -/
theorem loopVecN_inj {π : O} (hπ : Irreducible π) {m M : ℕ} :
    Function.Injective (fun d : MBoxN O m M => proj O m (M + m) (loopVecN π d)) := by
  intro d d' hdd'
  have hdvd := (proj_eq_iff_dvd hπ _ _).1 hdd'
  have heq := mkBoxN_eq_of_scaleVecN_congr hπ (f := fun i => resOut (d i))
    (g := fun i => resOut (d' i)) (fun i => hdvd i)
  rwa [mkBoxN_resOut_self, mkBoxN_resOut_self] at heq

/-- **`DecidedAt`-transport across the rescale loop**: a `σ`-decided level-`M` box class
rescales to a `σ`-decided level-`(M+m)` class. -/
theorem decidedAt_of_loopVecN {π : O} (hπ : Irreducible π) {m M : ℕ} {d : MBoxN O m M}
    {σ : FactorizationType} (hM : DecidedAt O m σ M (mtruncN (O := O) m M d)) :
    DecidedAt O m σ (M + m) (proj O m (M + m) (loopVecN π d)) := by
  refine decidedAt_of_congr hπ (fun b hb => ?_)
  have hfac : ∀ i : Fin m, π ^ (m - (i : ℕ)) ∣ b i := by
    intro i
    have hi := i.isLt
    have h1 : π ^ (m - (i : ℕ)) ∣ π ^ (M + m) := pow_dvd_pow π (by omega)
    have h3 : π ^ (m - (i : ℕ)) ∣ loopVecN π d i := ⟨resOut (d i), rfl⟩
    have h2 := dvd_add (h1.trans (hb i)) h3
    rwa [sub_add_cancel] at h2
  choose f hf using hfac
  have hbf : b = scaleVecN π f := by
    funext i; rw [hf i]; rfl
  have hbox : mkBoxN (O := O) m M f = d := by
    have hcong : ∀ i : Fin m,
        π ^ (M + m) ∣ (scaleVecN π (fun i => resOut (d i)) i - scaleVecN π f i) := by
      intro i
      have hbi := hb i
      rw [hbf] at hbi
      exact dvd_sub_comm.mp hbi
    have heq := mkBoxN_eq_of_scaleVecN_congr hπ hcong
    rwa [mkBoxN_resOut_self] at heq
  have hprojf : proj O m M f = mtruncN (O := O) m M d := by
    rw [← hbox, mtruncN_mkBoxN]
  have hσ : typeOf (monicPoly f) = σ := hM f hprojf
  rw [hbf, monicPoly_scaleVecN_eq_scaleRoots]
  have hty := typeOf_scaleRoots hπ (monicPoly_monic f) 1
  rwa [pow_one, hσ] at hty

end LoopVec

/-! ## §3 The full loop map: recentre-then-scale, the generic bijection -/

section LoopMap

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The generic rescale loop, WITH the choice of residue centre**: recentre at (a lift of)
`γ`, then rescale. This is the honest generalisation of IFC7's `loopMap`. -/
def loopMapN {m M : ℕ} (γ : ResidueField O) (π : O) (d : MBoxN O m M) : Fin m → O :=
  shiftVecN (loopVecN π d) (resSect O γ)

theorem typeOf_loopMapN {π : O} (hπ : Irreducible π) {m M : ℕ} (γ : ResidueField O)
    (d : MBoxN O m M) :
    typeOf (monicPoly (loopMapN γ π d)) = typeOf (monicPoly (fun i : Fin m => resOut (d i))) := by
  unfold loopMapN
  rw [typeOf_shiftVecN, typeOf_loopVecN hπ]

/-- **Characteristic-free γ-recovery**: `(X+Cγ)^m = (X+Cγ')^m` forces `γ = γ'` in ANY field, via
a single polynomial evaluation — no binomial-coefficient inversion (which is what would fail at
a residue characteristic dividing `m`). -/
theorem addC_pow_injective {K : Type*} [Field K] {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun δ : K => (X + C δ) ^ m) := by
  intro γ γ' h
  simp only at h
  have heval := congrArg (Polynomial.eval (-γ)) h
  simp only [eval_pow, eval_add, eval_X, eval_C] at heval
  have h0 : (-γ + γ : K) = 0 := by ring
  rw [h0, zero_pow hm.ne'] at heval
  have hz : (-γ + γ' : K) ^ m = 0 := heval.symm
  have hgz : (-γ + γ' : K) = 0 := (pow_eq_zero_iff hm.ne').1 hz
  linear_combination -hgz

/-- The bare scale loop's residue-field reduction is exactly `X^m` — every coordinate is
divisible by `π`. -/
theorem map_residue_monicPoly_loopVecN {π : O} (hπ : Irreducible π) {m M : ℕ}
    (d : MBoxN O m M) :
    Polynomial.map (residue O) (monicPoly (loopVecN π d)) = X ^ m := by
  have hz : ∀ i : Fin m, π ∣ (loopVecN π d i - (0 : Fin m → O) i) := by
    intro i
    have hi := i.isLt
    have hi1 : m - (i : ℕ) ≠ 0 := by omega
    simp only [Pi.zero_apply, sub_zero]
    exact (dvd_pow_self π hi1).mul_right (resOut (d i))
  have hcongr := map_residue_monicPoly_congr hπ hz
  rw [show (monicPoly (0 : Fin m → O)) = X ^ m from by unfold monicPoly; simp,
    Polynomial.map_pow, Polynomial.map_X] at hcongr
  exact hcongr

/-- The full loop map's residue-field reduction is exactly `(X + Cγ)^m`. -/
theorem map_residue_monicPoly_loopMapN {π : O} (hπ : Irreducible π) {m M : ℕ}
    (γ : ResidueField O) (d : MBoxN O m M) :
    Polynomial.map (residue O) (monicPoly (loopMapN γ π d)) = (X + C γ) ^ m := by
  unfold loopMapN
  rw [monicPoly_shiftVecN, Polynomial.map_comp, map_residue_monicPoly_loopVecN hπ,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, residue_resSect, X_pow_comp]

/-- **THE GENERIC LOOP BIJECTION** (A0G-RS's headline): `loopMapN` is injective jointly in the
residue centre `γ` AND the box `d`, at every degree `m ≥ 1`, over every complete DVR with
finite residue field, in EVERY residue characteristic (no wild-prime exclusion). -/
theorem loopMapN_inj {π : O} (hπ : Irreducible π) {m M : ℕ} (hm : 0 < m) :
    Function.Injective (fun p : ResidueField O × MBoxN O m M =>
      proj O m (M + m) (loopMapN p.1 π p.2)) := by
  rintro ⟨γ, d⟩ ⟨γ', d'⟩ h
  simp only at h
  have hdvd := (proj_eq_iff_dvd hπ _ _).1 h
  have hmod1 : ∀ i : Fin m, π ∣ (loopMapN γ' π d' i - loopMapN γ π d i) := by
    intro i
    have h1 : (1 : ℕ) ≤ M + m := by omega
    have h2 := (pow_dvd_pow π h1).trans (hdvd i)
    rwa [pow_one] at h2
  have hresidue := map_residue_monicPoly_congr hπ hmod1
  rw [map_residue_monicPoly_loopMapN hπ, map_residue_monicPoly_loopMapN hπ] at hresidue
  have hγ : γ = γ' := (addC_pow_injective hm hresidue).symm
  subst hγ
  have hdvd2 : ∀ i : Fin m, π ^ (M + m) ∣ (loopVecN π d' i - loopVecN π d i) := by
    intro i
    have h1 := dvd_shiftVecN_sub (n := m) (d := π ^ (M + m))
      (a := loopMapN γ π d) (a' := loopMapN γ π d') (-(resSect O γ)) hdvd
    have h2 := h1 i
    have eL : shiftVecN (loopMapN γ π d) (-(resSect O γ)) i = loopVecN π d i := by
      show shiftVecN (shiftVecN (loopVecN π d) (resSect O γ)) (-(resSect O γ)) i = loopVecN π d i
      rw [shiftVecN_add, add_neg_cancel, shiftVecN_zero]
    have eR : shiftVecN (loopMapN γ π d') (-(resSect O γ)) i = loopVecN π d' i := by
      show shiftVecN (shiftVecN (loopVecN π d') (resSect O γ)) (-(resSect O γ)) i = loopVecN π d' i
      rw [shiftVecN_add, add_neg_cancel, shiftVecN_zero]
    rwa [eL, eR] at h2
  have hd : d = d' := loopVecN_inj hπ ((proj_eq_iff_dvd hπ _ _).2 hdvd2)
  simp [hd]

/-- `DecidedAt`-transport for the full loop map (shift-then-scale composition of the two
transports already proved). -/
theorem decidedAt_of_loopMapN {π : O} (hπ : Irreducible π) {m M : ℕ} {γ : ResidueField O}
    {d : MBoxN O m M} {σ : FactorizationType}
    (hM : DecidedAt O m σ M (mtruncN (O := O) m M d)) :
    DecidedAt O m σ (M + m) (proj O m (M + m) (loopMapN γ π d)) := by
  have hDecScale : DecidedAt O m σ (M + m) (proj O m (M + m) (loopVecN π d)) :=
    decidedAt_of_loopVecN hπ hM
  refine decidedAt_of_congr hπ (fun b hb => ?_)
  set w := resSect O γ with hw
  have hb' : ∀ i : Fin m, π ^ (M + m) ∣ (shiftVecN b (-w) i - loopVecN π d i) := by
    intro i
    have h1 := dvd_shiftVecN_sub (n := m) (d := π ^ (M + m))
      (a := loopMapN γ π d) (a' := b) (-w) hb
    have h2 := h1 i
    have eL : shiftVecN (loopMapN γ π d) (-w) i = loopVecN π d i := by
      show shiftVecN (shiftVecN (loopVecN π d) w) (-w) i = loopVecN π d i
      rw [shiftVecN_add, add_neg_cancel, shiftVecN_zero]
    rwa [eL] at h2
  have hσ : typeOf (monicPoly (shiftVecN b (-w))) = σ :=
    hDecScale (shiftVecN b (-w)) ((proj_eq_iff_dvd hπ _ _).2 hb').symm
  have hbeq : b = shiftVecN (shiftVecN b (-w)) w := by
    rw [shiftVecN_add, neg_add_cancel, shiftVecN_zero]
  rw [hbeq, typeOf_shiftVecN, hσ]

end LoopMap

/-! ## §4 The two weight formulas -/

section Weights

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The coefficient-loss restatement**: direct corollary/renaming of `IFCG1.card_MBoxN`. -/
theorem card_MBoxN_kappaLoop (m M : ℕ) :
    Nat.card (MBoxN O m M) = residueCard O ^ (m * M + kappaLoop m) :=
  card_MBoxN m M

/-- **The conditional weight restatement**: direct corollary/renaming of
`IFCG1.card_preimage_mtruncN_eq`. -/
theorem card_preimage_mtruncN_kappaLoop (m M : ℕ) (S : Set (Coeff O m M)) :
    Nat.card ((mtruncN (O := O) m M) ⁻¹' S) = Nat.card S * residueCard O ^ (kappaLoop m) :=
  card_preimage_mtruncN_eq m M S

/-- The scale-loop's image (mod `π^(M+m)`) has EXACTLY the mixed-box cardinality — the
cardinality consequence of `loopVecN_inj`. -/
theorem card_range_loopVecN {π : O} (hπ : Irreducible π) (m M : ℕ) :
    Nat.card (Set.range (fun d : MBoxN O m M => proj O m (M + m) (loopVecN π d)))
      = residueCard O ^ (m * M + kappaLoop m) := by
  rw [Nat.card_range_of_injective (loopVecN_inj hπ), card_MBoxN]
  rfl

/-- **THE FULL-BOX LOOP WEIGHT** (A0 plan §3.2, subtraction-free form): the scale-loop's image,
weighted by `q^{T_m}`, equals the ambient level-`(M+m)` box — exactly "the full-box loop weight
is `q^{1-T_m}`" with no negative exponents. -/
theorem loopVecN_weight {π : O} (hπ : Irreducible π) (m M : ℕ) :
    Nat.card (Set.range (fun d : MBoxN O m M => proj O m (M + m) (loopVecN π d)))
      * residueCard O ^ (bigTLoop m) = residueCard O ^ (m * (M + m)) := by
  rw [card_range_loopVecN hπ, ← pow_add]
  congr 1
  have hsq : kappaLoop m + bigTLoop m = m * m := kappaLoop_add_bigTLoop m
  have hdist : m * (M + m) = m * M + m * m := by ring
  omega

end Weights

/-! ## §5 The generic scalar fixed-point solver (node A0G-FP) -/

section FixedPoint

/-- **Uniqueness of the scalar fixed point** (pure algebra, A0G-FP's "uniqueness" gate): the
affine recurrence `D = b + y·D` has at most one solution once `y ≠ 1`. -/
theorem fixedPoint_unique {y b D D' : ℝ} (hy : y ≠ 1) (hD : D = b + y * D)
    (hD' : D' = b + y * D') : D = D' := by
  have h : (1 - y) * D = (1 - y) * D' := by nlinarith [hD, hD']
  have h1y : (1 : ℝ) - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  exact mul_left_cancel₀ h1y h

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The generic scalar-recurrence LOWER-BOUND solver**: generalizes `IFC7.density_ge_of_step`
from the hard-coded shift `3`/exponent `5` to an arbitrary shift `s` and exponent `d > 0`, at an
arbitrary degree `n`. **No `DrainageAt` anywhere**; denominator positivity from `q ≥ 2` and
`d > 0` alone. -/
theorem decidedDensity_ge_of_step {n : ℕ} {σ : FactorizationType} {s d : ℕ} (hd : 0 < d)
    {bs : ℕ → ℝ} {b : ℝ} (hb : Filter.Tendsto bs Filter.atTop (nhds b))
    (hstep : ∀ M, bs M + ((residueCard O : ℝ) ^ d)⁻¹ * decidedSeq O n σ M
      ≤ decidedSeq O n σ (M + s)) :
    b * (residueCard O : ℝ) ^ d / ((residueCard O : ℝ) ^ d - 1) ≤ decidedDensity O n σ := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hqd : (1 : ℝ) < (residueCard O : ℝ) ^ d := one_lt_pow₀ (by linarith) hd.ne'
  have hL : Filter.Tendsto (fun M => decidedSeq O n σ (M + s)) Filter.atTop
      (nhds (decidedDensity O n σ)) :=
    (decidedSeq_tendsto (O := O) n σ).comp (Filter.tendsto_add_atTop_nat s)
  have hR : Filter.Tendsto (fun M => bs M + ((residueCard O : ℝ) ^ d)⁻¹ * decidedSeq O n σ M)
      Filter.atTop (nhds (b + ((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ)) :=
    hb.add ((decidedSeq_tendsto (O := O) n σ).const_mul _)
  have hfix : b + ((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ ≤ decidedDensity O n σ :=
    le_of_tendsto_of_tendsto' hR hL hstep
  have hpos : (0 : ℝ) < (residueCard O : ℝ) ^ d := by linarith
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (residueCard O : ℝ) ^ d - 1)]
  have h2 : (((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ) * (residueCard O : ℝ) ^ d
      = decidedDensity O n σ := by field_simp
  have h3 := mul_le_mul_of_nonneg_right hfix hpos.le
  rw [add_mul, h2] at h3
  linarith

/-- **The generic scalar-recurrence EQUALITY solver** (A0G-FP's "direct equality at the
decided-density limit" gate): if the step is an EXACT recurrence, `decidedDensity` equals the
fixed point on the nose. -/
theorem decidedDensity_eq_of_step_eq {n : ℕ} {σ : FactorizationType} {s d : ℕ} (hd : 0 < d)
    {bs : ℕ → ℝ} {b : ℝ} (hb : Filter.Tendsto bs Filter.atTop (nhds b))
    (hstep : ∀ M, bs M + ((residueCard O : ℝ) ^ d)⁻¹ * decidedSeq O n σ M
      = decidedSeq O n σ (M + s)) :
    decidedDensity O n σ = b * (residueCard O : ℝ) ^ d / ((residueCard O : ℝ) ^ d - 1) := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hqd : (1 : ℝ) < (residueCard O : ℝ) ^ d := one_lt_pow₀ (by linarith) hd.ne'
  have hL : Filter.Tendsto (fun M => decidedSeq O n σ (M + s)) Filter.atTop
      (nhds (decidedDensity O n σ)) :=
    (decidedSeq_tendsto (O := O) n σ).comp (Filter.tendsto_add_atTop_nat s)
  have hR : Filter.Tendsto (fun M => bs M + ((residueCard O : ℝ) ^ d)⁻¹ * decidedSeq O n σ M)
      Filter.atTop (nhds (b + ((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ)) :=
    hb.add ((decidedSeq_tendsto (O := O) n σ).const_mul _)
  have hR' : Filter.Tendsto (fun M => decidedSeq O n σ (M + s)) Filter.atTop
      (nhds (b + ((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ)) :=
    hR.congr hstep
  have hfix : b + ((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ = decidedDensity O n σ :=
    tendsto_nhds_unique hR' hL
  have hpos : (0 : ℝ) < (residueCard O : ℝ) ^ d := by linarith
  have h3 := congrArg (· * (residueCard O : ℝ) ^ d) hfix
  simp only [add_mul] at h3
  have h2 : (((residueCard O : ℝ) ^ d)⁻¹ * decidedDensity O n σ) * (residueCard O : ℝ) ^ d
      = decidedDensity O n σ := by field_simp
  rw [h2] at h3
  rw [eq_div_iff (by linarith : (residueCard O : ℝ) ^ d - 1 ≠ 0)]
  linarith [h3]

end FixedPoint

end Uniformity.Density.IFCG3

end

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.IFCG3.bigTLoop_eq_kappaLoop_add
#print axioms Uniformity.Density.IFCG3.kappaLoop_add_bigTLoop
#print axioms Uniformity.Density.IFCG3.bigTLoop_three_recovery
#print axioms Uniformity.Density.IFCG3.monicPoly_scaleVecN_eq_scaleRoots
#print axioms Uniformity.Density.IFCG3.typeOf_scaleVecN
#print axioms Uniformity.Density.IFCG3.map_residue_monicPoly_congr
#print axioms Uniformity.Density.IFCG3.typeOf_loopVecN
#print axioms Uniformity.Density.IFCG3.mkBoxN_eq_of_scaleVecN_congr
#print axioms Uniformity.Density.IFCG3.loopVecN_inj
#print axioms Uniformity.Density.IFCG3.decidedAt_of_loopVecN
#print axioms Uniformity.Density.IFCG3.typeOf_loopMapN
#print axioms Uniformity.Density.IFCG3.addC_pow_injective
#print axioms Uniformity.Density.IFCG3.map_residue_monicPoly_loopMapN
#print axioms Uniformity.Density.IFCG3.loopMapN_inj
#print axioms Uniformity.Density.IFCG3.decidedAt_of_loopMapN
#print axioms Uniformity.Density.IFCG3.card_range_loopVecN
#print axioms Uniformity.Density.IFCG3.loopVecN_weight
#print axioms Uniformity.Density.IFCG3.fixedPoint_unique
#print axioms Uniformity.Density.IFCG3.decidedDensity_ge_of_step
#print axioms Uniformity.Density.IFCG3.decidedDensity_eq_of_step_eq

end AxCheck
