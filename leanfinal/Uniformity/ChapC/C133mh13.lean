/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C133mh3
import Uniformity.ChapC.C133mh12
import Mathlib

/-!
# Uniformity.ChapC.C133mh13 — `[MH13 2026-08-28]`: Theorem C (placement/maximality, degree-pinned)

**Node MH.13 = the maximality half of F1.H3** (source of truth:
`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §2 "Theorem C (placement/maximality — the
BlockFrontier clause, DEGREE-PINNED)" ~line 302; proof plan §6.2 ~line 812). Named inputs:
**MH.2/MH.3** (Theorem M, landed unconditional in `C133mh3.lean`: `dvSideDeg_mul`,
`dvResPoly_mul_gen` with τ = 1) + **MH.12** (`C133mh12.lean`: defect-vanishing,
no-far-primes, Gauss descent) + mathlib PID/UFD arithmetic over `FractionRing O`.

## The statement (resolution record against the signed A-C.20 shapes)

* The degree-pinned label `HasLabel′ L fS' := HasLabel L fS' ∧ D′ ∣ fS'.natDegree` is
  transcribed VERBATIM from the signed A-C.20 competitor shape
  (`C35.lean:169-171` / `BlockFrontier`, `C35.lean:280-282`): the two hypotheses
  `hlab : HasLabel L fS'` and `hpinned : (F.e₁ * F.f₁) ∣ fS'.natDegree`. The pin is NOT
  optional — doc §7 refutes the unpinned form.
* `P`/`Q`/`W` hypotheses are §2's clause list verbatim (P monic pure `D′ ∣ deg`,
  `R(P) = r ^ m`, `m ≥ 1`; Q monic pure `D′ ∣ deg`, `r ∤ R(Q)` — "R(Q) = s with r ∤ s"
  is transcribed with `s := R(Q)` itself; W monic point-sided `dvSideDeg = 0`).
  Residual pins are carried as hypotheses in `HasLabel`'s own `(hne₂, M₀, hpin₂)` shape.
* **Honest note on consumption**: `Squarefree f` and the P-clauses are carried per §2 but
  NOT consumed by this proof. The proof strengthens §6.2's assembly: instead of the
  squarefree `∏ᵢ qᵢ` distinct-prime factorization, it shows `fS'.map` is COPRIME to
  `(Q * W).map` over `K₀ = FractionRing O` (no common irreducible: any common prime
  Gauss-descends to a monic `q' ∣ fS'`, which §6.1/M force non-far with `r ∣ R(q')`,
  killing both the `Q` leg (`r ∤ R(Q)`) and the `W` leg (point side)); then
  `IsCoprime.dvd_of_dvd_mul_right` + monic `map_dvd_map` descent give `fS' ∣ P` with
  multiplicities handled by coprimality. Statement unchanged from §2 (hypotheses may be
  unconsumed; none is weakened).

Sorry-free; axiom footprint Lean-core (see the AxCheck footer).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Tower.C133mh13

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — private plumbing (standing D9 convention, as in C133mh3/C133mh0) -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

/-- Pin existence: the side-min abscissa of a nonempty side has FINITE level height
(`DvOnSide`'s second conjunct is exactly the finiteness guard, C.07). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 (dvOnSide_of_mem' (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-! ## Part 1 — the per-prime core (§6.2's bullet-list input, one monic factor at a time) -/

/-- ★ **MH.13 per-prime core (§6.2, "qᵢ is not far … and `R(qᵢ) = τ'·r^{aᵢ}`, aᵢ ≥ 1").**
A monic factor `q` of positive degree inside a monic, `(u,ℓ)`-pure, `D′`-divisible product
`q * w` whose exact level residual is `L.r ^ m` has (i) a NON-POINT `(u,ℓ)`-side
(`dvSideDeg ≠ 0`, from MH.12's no-far-primes) and (ii) residual divisible by `L.r`
(from the τ = 1 mixed law `C133mh3.dvResPoly_mul_gen` inside `q * w` plus the prime-power
divisor analysis in `K[Z]`, `K` the stage field). -/
theorem dvSideDeg_ne_zero_and_r_dvd_of_factor
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {q w : Polynomial O} (hq : q.Monic) (hw : w.Monic)
    (hpure : IsDvPure F (q * w) L.u L.ℓ)
    (hdeg : (F.e₁ * F.f₁) ∣ (q * w).natDegree)
    (hnx : (dvSideSet F (q * w) L.u L.ℓ).Nonempty) {Mx m : ℕ}
    (hpinx : dvHgt F (q * w) (dvSideMin F (q * w) L.u L.ℓ hnx) = (Mx : ℕ∞))
    (hxres : dvResPoly F H₀ hpin (q * w) L.u L.ℓ hnx Mx hpinx = L.r ^ m)
    (hqpos : 0 < q.natDegree)
    (hnq : (dvSideSet F q L.u L.ℓ).Nonempty) {Mq : ℕ}
    (hpinq : dvHgt F q (dvSideMin F q L.u L.ℓ hnq) = (Mq : ℕ∞)) :
    dvSideDeg F q L.u L.ℓ hnq ≠ 0 ∧
      L.r ∣ dvResPoly F H₀ hpin q L.u L.ℓ hnq Mq hpinq := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hfloor' : L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
    have h := L.hκ; rw [mul_assoc] at h; exact h
  -- (i) `q` is not far (§6.1 no-far-primes, contradiction form)
  have hside : dvSideDeg F q L.u L.ℓ hnq ≠ 0 :=
    C133mh12.not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos hπ hh H₀ hpin
      L.hℓ L.hcop hfloor' hq hw hpure hdeg hnq hqpos
  refine ⟨hside, ?_⟩
  -- (ii) the τ = 1 mixed law inside `q * w`: `R(q) · R(w) = L.r ^ m`
  have hnw : (dvSideSet F w L.u L.ℓ).Nonempty := dvSideSet_nonempty F hw.ne_zero L.u L.hℓ
  obtain ⟨Mw, hpinw⟩ := exists_pin F hnw
  have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop hfloor'
    hq.ne_zero hw.ne_zero hnq hnw hnx hpinq hpinw hpinx
  have hdvdpow : dvResPoly F H₀ hpin q L.u L.ℓ hnq Mq hpinq ∣ L.r ^ m :=
    ⟨dvResPoly F H₀ hpin w L.u L.ℓ hnw Mw hpinw, by rw [← hmul]; exact hxres.symm⟩
  -- `R(q)` is a NONUNIT divisor of the prime power `L.r ^ m` (its degree is the side degree)
  have hdegR : (dvResPoly F H₀ hpin q L.u L.ℓ hnq Mq hpinq).natDegree
      = dvSideDeg F q L.u L.ℓ hnq :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hnq hpinq).1
  have hnonunit : ¬ IsUnit (dvResPoly F H₀ hpin q L.u L.ℓ hnq Mq hpinq) := fun hu =>
    hside (by rw [← hdegR]; exact Polynomial.natDegree_eq_zero_of_isUnit hu)
  have hrprime : Prime L.r := L.hrirr.prime
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hrprime m).mp hdvdpow
  rcases Nat.eq_zero_or_pos i with h0 | hipos
  · exact absurd (associated_one_iff_isUnit.mp (by simpa [h0] using hassoc)) hnonunit
  · exact (dvd_pow_self L.r hipos.ne').trans hassoc.symm.dvd

/-! ## Part 1b — descent/leg stage lemmas (private; the §6.2 case analysis, one leg each) -/

/-- The strict floor `ℓ·(D′·h) < u`, re-associated from `LevelDatum.hκ`'s `ℓ·D′·h < u`. -/
private theorem floor_assoc {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  have h := L.hκ; rw [mul_assoc] at h; exact h

/-- §6.2's Gauss-descent packaging: an irreducible `q₀` over `K₀ = FractionRing O` dividing
the image of a monic `x` descends to a monic `q'` over `O` of positive degree that divides
EVERY `y` whose image `q₀` divides (monic `map_dvd_map` descent through the normalization
`q₀ ~ q₀ · C(lc q₀)⁻¹` and MH.12's `exists_monic_map_eq_of_dvd_map`). -/
private theorem exists_monic_descent {x : Polynomial O} (hx : x.Monic)
    {q₀ : Polynomial (FractionRing O)} (hq₀irr : Irreducible q₀)
    (hq₀x : q₀ ∣ x.map (algebraMap O (FractionRing O))) :
    ∃ q' : Polynomial O, q'.Monic ∧ 0 < q'.natDegree ∧
      ∀ y : Polynomial O, q₀ ∣ y.map (algebraMap O (FractionRing O)) → q' ∣ y := by
  have hq₀0 : q₀ ≠ 0 := hq₀irr.ne_zero
  have hlc : q₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₀0
  have hCu : IsUnit (Polynomial.C q₀.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc))
  obtain ⟨cu, hcu⟩ := hCu
  have hassoc : Associated q₀ (q₀ * Polynomial.C q₀.leadingCoeff⁻¹) := ⟨cu, by rw [hcu]⟩
  have hqmmon : (q₀ * Polynomial.C q₀.leadingCoeff⁻¹).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv hq₀0
  obtain ⟨q', hq'mon, hq'map⟩ := C133mh12.exists_monic_map_eq_of_dvd_map hx hqmmon
    (hassoc.symm.dvd.trans hq₀x)
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  refine ⟨q', hq'mon, ?_, fun y hy =>
    (Polynomial.map_dvd_map (algebraMap O (FractionRing O)) hinj hq'mon).mp
      (by rw [hq'map]; exact hassoc.symm.dvd.trans hy)⟩
  have h1 : (q₀ * Polynomial.C q₀.leadingCoeff⁻¹).natDegree = q₀.natDegree := by
    rw [Polynomial.natDegree_mul hq₀0 (fun hC => inv_ne_zero hlc (Polynomial.C_eq_zero.mp hC)),
      Polynomial.natDegree_C, add_zero]
  have hdegq : q'.natDegree = q₀.natDegree := by
    rw [← hq'mon.natDegree_map (algebraMap O (FractionRing O)), hq'map, h1]
  rw [hdegq]
  by_contra hnpos
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp (Nat.eq_zero_of_not_pos hnpos)
  exact hq₀irr.not_isUnit (hc ▸ Polynomial.isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr fun hc0 => hq₀0 (by rw [← hc, hc0, map_zero])))

/-- §6.2's `Q`-leg: a monic `q'` whose residual `L.r` divides cannot divide the monic `Q`
whose residual `L.r` does NOT divide — the τ = 1 mixed law inside `Q = q' * wQ` propagates
`L.r ∣ R(q')` into `L.r ∣ R(Q)`. -/
private theorem q_leg_false
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Q q' : Polynomial O} (hQmon : Q.Monic) (hq'mon : q'.Monic)
    (hnQ : (dvSideSet F Q L.u L.ℓ).Nonempty) {MQ : ℕ}
    (hpinQ : dvHgt F Q (dvSideMin F Q L.u L.ℓ hnQ) = (MQ : ℕ∞))
    (hQres : ¬ L.r ∣ dvResPoly F H₀ hpin Q L.u L.ℓ hnQ MQ hpinQ)
    (hnq' : (dvSideSet F q' L.u L.ℓ).Nonempty) {Mq' : ℕ}
    (hpinq' : dvHgt F q' (dvSideMin F q' L.u L.ℓ hnq') = (Mq' : ℕ∞))
    (hrdvd : L.r ∣ dvResPoly F H₀ hpin q' L.u L.ℓ hnq' Mq' hpinq')
    (hq'Q : q' ∣ Q) : False := by
  obtain ⟨wQ, hwQ⟩ := hq'Q
  have hwQmon : wQ.Monic := hq'mon.of_mul_monic_left (hwQ ▸ hQmon)
  subst hwQ
  have hnwQ : (dvSideSet F wQ L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hwQmon.ne_zero L.u L.hℓ
  obtain ⟨MwQ, hpinwQ⟩ := exists_pin F hnwQ
  have hmulQ := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop (floor_assoc L)
    hq'mon.ne_zero hwQmon.ne_zero hnq' hnwQ hnQ hpinq' hpinwQ hpinQ
  refine hQres ?_
  rw [hmulQ]
  exact hrdvd.mul_right _

/-- §6.2's `W`-leg: a monic `q'` with a NON-POINT `(u,ℓ)`-side cannot divide the
point-sided monic `W` — side-degree additivity (Theorem M clause 2) inside `W = q' * wW`. -/
private theorem w_leg_false
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {W q' : Polynomial O} (hWmon : W.Monic) (hq'mon : q'.Monic)
    (hnW : (dvSideSet F W L.u L.ℓ).Nonempty)
    (hWpt : dvSideDeg F W L.u L.ℓ hnW = 0)
    (hnq' : (dvSideSet F q' L.u L.ℓ).Nonempty)
    (hside : dvSideDeg F q' L.u L.ℓ hnq' ≠ 0)
    (hq'W : q' ∣ W) : False := by
  obtain ⟨wW, hwW⟩ := hq'W
  have hwWmon : wW.Monic := hq'mon.of_mul_monic_left (hwW ▸ hWmon)
  subst hwW
  have hnwW : (dvSideSet F wW L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hwWmon.ne_zero L.u L.hℓ
  have haddW := C133mh3.dvSideDeg_mul hπ hh H₀ hpin L.hℓ L.hcop (floor_assoc L)
    hq'mon.ne_zero hwWmon.ne_zero hnq' hnwW hnW
  rw [hWpt] at haddW
  exact hside (by omega)

/-! ## Part 2 — ★ Theorem C (placement/maximality, the BlockFrontier clause) -/

/-- ★ **MH.13 = Theorem C (doc §2, DEGREE-PINNED; the maximality half of F1.H3).**
`f` monic squarefree splits as `P * Q * W` with `P` monic pure `D′`-divisible of exact
residual `L.r ^ m` (`m ≥ 1`), `Q` monic pure `D′`-divisible with `L.r ∤ R(Q)`, and `W`
monic with a POINT `(u,ℓ)`-side. Then every degree-pinned labelled divisor of `f`
(`HasLabel L fS'` AND `(F.e₁ * F.f₁) ∣ fS'.natDegree` — the signed A-C.20 competitor
shape, `C35.lean:280-282`) divides `P`. -/
theorem theoremC_placement
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {f P Q W : Polynomial O}
    (hf : f.Monic) (hsq : Squarefree f) (hsplit : f = P * Q * W)
    (hPmon : P.Monic) (hPpure : IsDvPure F P L.u L.ℓ)
    (hPdeg : (F.e₁ * F.f₁) ∣ P.natDegree)
    (hnP : (dvSideSet F P L.u L.ℓ).Nonempty) {MP m : ℕ}
    (hpinP : dvHgt F P (dvSideMin F P L.u L.ℓ hnP) = (MP : ℕ∞))
    (hm : 0 < m)
    (hPres : dvResPoly F H₀ hpin P L.u L.ℓ hnP MP hpinP = L.r ^ m)
    (hQmon : Q.Monic) (hQpure : IsDvPure F Q L.u L.ℓ)
    (hQdeg : (F.e₁ * F.f₁) ∣ Q.natDegree)
    (hnQ : (dvSideSet F Q L.u L.ℓ).Nonempty) {MQ : ℕ}
    (hpinQ : dvHgt F Q (dvSideMin F Q L.u L.ℓ hnQ) = (MQ : ℕ∞))
    (hQres : ¬ L.r ∣ dvResPoly F H₀ hpin Q L.u L.ℓ hnQ MQ hpinQ)
    (hWmon : W.Monic)
    (hnW : (dvSideSet F W L.u L.ℓ).Nonempty)
    (hWpt : dvSideDeg F W L.u L.ℓ hnW = 0)
    {fS' : Polynomial O}
    (hlab : HasLabel L fS') (hpinned : (F.e₁ * F.f₁) ∣ fS'.natDegree)
    (hdvd : fS' ∣ f) :
    fS' ∣ P := by
  classical
  obtain ⟨hSmon, hSpos, hSpure, hnS, MS, hpinS, mS, hmS, hSres⟩ := hlab
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  -- STEP 1 (the §6.2 placement, coprime form): `fS'.map` has no common prime with `(Q*W).map`
  have hcopS : IsCoprime (fS'.map (algebraMap O (FractionRing O)))
      ((Q * W).map (algebraMap O (FractionRing O))) := by
    refine isCoprime_of_dvd _ _
      (fun h0 => (hSmon.map (algebraMap O (FractionRing O))).ne_zero h0.1) ?_
    intro z hznu hz0 hzS hzQW
    obtain ⟨q₀, hq₀irr, hq₀z⟩ := WfDvdMonoid.exists_irreducible_factor
      (mem_nonunits_iff.mp hznu) hz0
    obtain ⟨q', hq'mon, hq'pos, htransfer⟩ :=
      exists_monic_descent hSmon hq₀irr (hq₀z.trans hzS)
    obtain ⟨wS, hwS⟩ := htransfer fS' (hq₀z.trans hzS)
    have hwSmon : wS.Monic := hq'mon.of_mul_monic_left (hwS ▸ hSmon)
    subst hwS
    have hnq' : (dvSideSet F q' L.u L.ℓ).Nonempty :=
      dvSideSet_nonempty F hq'mon.ne_zero L.u L.hℓ
    obtain ⟨Mq', hpinq'⟩ := exists_pin F hnq'
    obtain ⟨hside, hrdvd⟩ := dvSideDeg_ne_zero_and_r_dvd_of_factor hπ hh L hq'mon hwSmon
      hSpure hpinned hnS hpinS hSres hq'pos hnq' hpinq'
    have hq₀QW : q₀ ∣ Q.map (algebraMap O (FractionRing O))
        * W.map (algebraMap O (FractionRing O)) := by
      rw [← Polynomial.map_mul]; exact hq₀z.trans hzQW
    rcases hq₀irr.prime.2.2 _ _ hq₀QW with hcase | hcase
    · exact q_leg_false hπ hh L hQmon hq'mon hnQ hpinQ hQres hnq' hpinq' hrdvd
        (htransfer Q hcase)
    · exact w_leg_false hπ hh L hWmon hq'mon hnW hWpt hnq' hside (htransfer W hcase)
  -- STEP 2 (assembly): `fS'.map ∣ P.map * (Q*W).map`, coprimality places it inside `P.map`
  have hPQW : P.map (algebraMap O (FractionRing O))
      * (Q * W).map (algebraMap O (FractionRing O))
      = f.map (algebraMap O (FractionRing O)) := by
    rw [← Polynomial.map_mul, ← mul_assoc, ← hsplit]
  have hmapdvd : fS'.map (algebraMap O (FractionRing O))
      ∣ P.map (algebraMap O (FractionRing O))
        * (Q * W).map (algebraMap O (FractionRing O)) := by
    rw [hPQW]
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c.map (algebraMap O (FractionRing O)), by rw [hc, Polynomial.map_mul]⟩
  -- STEP 3 (monic descent of the conclusion): `fS' ∣ P` over `O`
  exact (Polynomial.map_dvd_map (algebraMap O (FractionRing O)) hinj hSmon).mp
    (hcopS.dvd_of_dvd_mul_right hmapdvd)

end Uniformity.Density.Tower.C133mh13

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh13.dvSideDeg_ne_zero_and_r_dvd_of_factor
#print axioms Uniformity.Density.Tower.C133mh13.theoremC_placement

end AxCheck
