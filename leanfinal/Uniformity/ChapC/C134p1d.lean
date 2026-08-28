/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134p1
import Uniformity.ChapC.C131aa
import Uniformity.ChapC.C26
import Uniformity.ChapB.B04

/-!
# Uniformity.ChapC.C134p1d — the C.13-representative dictionary: P1 CLOSED [P1D 2026-08-28]

**[P1D 2026-08-28]** (`runs/wave-c/verdict_P1U.md`'s P1 section): the citation-grade
premise `IsTestKey L Ψ → IsMuKey L Ψ` (Guàrdia--Nart, *Genetics of polynomials over
local fields*, Contemp. Math. 637, Lemma 3.1(3)) is **PROVED OUTRIGHT** —
`isMuKey_of_isTestKey`, Lean-core, no new axiom.  P1U's route (a), completed: the
planned `AX-GN-REPKEY` cite is retired before declaration.

## The dictionary (per `IsMuKey` conjunct)

`C134dv2g.IsMuKey L Ψ = Ψ.Monic ∧ MuMinimal L Ψ ∧ MuPrime L Ψ`.  Against C.13's five
test-key clauses:

1. **Monic — DEFINITIONAL.**  `IsTestKey`'s clause 1 is the conjunct.
2. **μ-minimality — PROVED (`muMinimal_of_isTestKey`).**  The degree count: if `Ψ ∣µ g`
   for a nonzero `g`, the landed forward bridge (`C134p1.not_muDvd_of_residual_notdvd`,
   contrapositive) forces `L.r ∣ R(g)`; C.26's teeth give `R(g) ≠ 0` (nonzero constant
   term) and `deg R(g) = dvSideDeg(g)`; but a `g` of degree `< deg Ψ = D′·ℓ·d` has every
   nonzero development digit at abscissa `< ℓ·d` (B.04), so `dvSideDeg(g) < d = deg L.r`
   — and `L.r` cannot divide a nonzero polynomial of smaller degree.  Positivity
   `0 < deg Ψ` is clause 2 + the frame numerals.
3. **μ-primality — PROVED (`muPrime_of_isTestKey`), Parts 5–8.**  The head
   (`residual_dvd_or_of_muDvd_mul`): `Ψ ∣µ g·z` pushes to `L.r ∣ R(g)·R(z)` by Theorem M
   clause 3 (`C133mh3.dvResPoly_mul_gen`), and `L.r` is prime in `K[y]` (`L.hrirr` + the
   `EuclideanDomain → PID → UFD` chain).  The **residual lift** `L.r ∣ R(g) → Ψ ∣µ g`
   (`muDvd_of_residual_dvd` — the substance of GN Lemma 3.1(3) / FGMN's residual-ideal
   classification) is proved by the S2 `C130kp1.S2MuDvd_of_normRes_dvd` remainder
   mechanism, frame-generic: the μ-cofactor is the LITERAL quotient `g /ₘ Ψ`, the value
   comparison of `g %ₘ Ψ` against `Ψ·(g /ₘ Ψ)` splits into the landed ultrametric cases,
   the excluded branches die on clause 2's degree count, and the TIE branch is settled by
   the new `V`-line read (`lineRes`, Part 8: additive by C130rp2's read additivity, and
   equal to `dvResPoly · Xᵟ` by C26-style slot bookkeeping).

## What lands (all sorry-free, ALL Lean-core — the AxCheck footer is the record)

* `natDegree_pos_of_isTestKey` — clause 2 → `0 < deg Ψ`.
* `not_residual_dvd_of_natDegree_lt` — ★ the degree count: below the recipe degree the
  level residual cannot be `L.r`-divisible.
* `residual_dvd_of_muDvd` — P2's contrapositive, packaged for consumers.
* `muMinimal_of_isTestKey` — ★ the μ-minimality conjunct, PROVED.
* `residual_dvd_or_of_muDvd_mul` — ★ the primality head, PROVED.
* `muPrime_of_residualLift` — μ-primality from an abstract residual lift (kept: it
  documents the exact narrow leg a cite WOULD have had to supply).
* `isMuKey_of_isTestKey_of_muPrime` / `isMuKey_of_isTestKey_of_residualLift` — the
  assembly, factored through the (now discharged) leg.
* `muDvd_of_residual_dvd` — ★★ the residual lift, PROVED (Part 8).
* `muPrime_of_isTestKey` — ★★ the μ-primality conjunct, PROVED.
* `isMuKey_of_isTestKey` — ★★ **P1 CLOSED**: the exact statement P1U drafted as the
  `isMuKey_of_isTestKey` axiom, as a THEOREM (no `exists_dvDissection`, no cite).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`not_residual_dvd_of_natDegree_lt` (the degree-count statement),
`muDvd_of_residual_dvd` (the backward-translation statement), and
`isMuKey_of_isTestKey` (the P1 statement itself, now load-bearing for DV2G's F1.3–F1.6
chain).

DEPENDS: C134p1 (`not_muDvd_of_residual_notdvd`) · C134dv2g (`MuDvd`/`MuMinimal`/
`MuPrime`/`IsMuKey`, `muDvd_zero`) · C133mh3 (`dvResPoly_mul_gen`) · C.26
(`natDegree_dvResPoly`) · C.34 (`dvSideSet_nonempty`) · B.04 (`dev_eq_zero_of_lt`) ·
C.13 (`IsTestKey`) · C.09 (`LevelDatum`) · mathlib (`natDegree_le_of_dvd`,
`UniqueFactorizationMonoid.irreducible_iff_prime` through `EuclideanDomain (K[y])`).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C134p1d

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C134dv2g Uniformity.Density.Tower.C134p1
open Uniformity.Density.Tower.C130s6

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — private plumbing (the standing local-twin convention:
C.04/C.12/C.26/C.47/C.80/C.97/C133mh1/C133mh3) -/

private theorem inner_floor (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]
  exact L.hκ

private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1
    (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

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

/-! ## Part 1 — clause dictionary, the definitional legs -/

/-- Clause 2 of `IsTestKey` + the frame numerals: the recipe degree is positive. -/
theorem natDegree_pos_of_isTestKey (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨ : IsTestKey L Ψ) : 0 < Ψ.natDegree := by
  rw [hΨ.2.1, LevelDatum.keyDeg₂]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) L.hℓ) L.hrdeg

/-! ## Part 2 — ★ the degree count -/

/-- ★ **The degree count**: a nonzero polynomial of degree below the recipe degree
`D″ = D′·ℓ·d` cannot have `L.r`-divisible level residual.  Its development abscissae stop
below `ℓ·d` (B.04), so the side degree — which is EXACTLY the residual degree, C.26 —
stays below `d = deg L.r`, while `L.r ∣ R(g)` with `R(g) ≠ 0` (C.26's nonzero constant
term) would force `deg R(g) ≥ d`. -/
theorem not_residual_dvd_of_natDegree_lt (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {g : Polynomial O} (hdeg : g.natDegree < L.keyDeg₂)
    (hng : (dvSideSet F g L.u L.ℓ).Nonempty) (Mg : ℕ)
    (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞)) :
    ¬ L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg := by
  intro hdvd
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  obtain ⟨hRdeg, hR0⟩ := natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hng hpg
  have hRne : dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg ≠ 0 := fun h0 =>
    hR0 (by rw [h0, Polynomial.coeff_zero])
  have hdle : L.r.natDegree ≤ (dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hRne
  -- the side's right endpoint carries a nonzero digit, so it sits below `ℓ·d`
  have hmem : dvSideMax F g L.u L.ℓ hng ∈ dvSideSet F g L.u L.ℓ := Finset.max'_mem _ _
  have hon := dvOnSide_of_mem_dvSideSet hmem
  have hdev : dev F.key g (dvSideMax F g L.u L.ℓ hng) ≠ 0 := by
    intro h0
    apply hon.2
    rw [dvHgt, h0, C118a.stageHeight_zero]
  have hDpos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  have hjb : dvSideMax F g L.u L.ℓ hng * F.key.natDegree ≤ g.natDegree := by
    by_contra hlt
    exact hdev (dev_eq_zero_of_lt F.hmonic hDpos g _ (lt_of_not_ge hlt))
  have hlt2 : dvSideMax F g L.u L.ℓ hng < L.ℓ * L.r.natDegree := by
    have h1 : (F.e₁ * F.f₁) * dvSideMax F g L.u L.ℓ hng ≤ g.natDegree := by
      rw [F.hdeg] at hjb
      rw [Nat.mul_comm]
      exact hjb
    have h2 : g.natDegree < (F.e₁ * F.f₁) * (L.ℓ * L.r.natDegree) := by
      rw [LevelDatum.keyDeg₂] at hdeg
      calc g.natDegree < F.e₁ * F.f₁ * L.ℓ * L.r.natDegree := hdeg
        _ = (F.e₁ * F.f₁) * (L.ℓ * L.r.natDegree) := by ring
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h2)
  have hsdeg : dvSideDeg F g L.u L.ℓ hng < L.r.natDegree := by
    rw [dvSideDeg]
    refine (Nat.div_lt_iff_lt_mul L.hℓ).mpr ?_
    calc dvSideMax F g L.u L.ℓ hng - dvSideMin F g L.u L.ℓ hng
        ≤ dvSideMax F g L.u L.ℓ hng := Nat.sub_le _ _
      _ < L.ℓ * L.r.natDegree := hlt2
      _ = L.r.natDegree * L.ℓ := Nat.mul_comm _ _
  rw [hRdeg] at hdle
  omega

/-! ## Part 3 — MuDvd pushes to residual divisibility (P2's contrapositive, packaged) -/

/-- P2's bridge, contrapositive form: μ-divisibility by a test key forces
`L.r`-divisibility of the level residual. -/
theorem residual_dvd_of_muDvd (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ g : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hng : (dvSideSet F g L.u L.ℓ).Nonempty) (Mg : ℕ)
    (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞))
    (hdvd : MuDvd L Ψ g) :
    L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg := by
  by_contra hnd
  exact C134p1.not_muDvd_of_residual_notdvd L hπ hh hΨ hng Mg hpg hnd hdvd

/-! ## Part 4 — ★ μ-minimality, PROVED -/

/-- ★ **The μ-minimality conjunct of `IsMuKey`, PROVED for every test key** — no cite.
Any nonzero `g` of degree `< deg Ψ` that `Ψ` μ-divides would carry an `L.r`-divisible
residual (Part 3) of degree `< deg L.r` (Part 2): impossible. -/
theorem muMinimal_of_isTestKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    MuMinimal L Ψ := by
  refine ⟨natDegree_pos_of_isTestKey L hΨ, fun g hg hdeg hdvd => ?_⟩
  have hng : (dvSideSet F g L.u L.ℓ).Nonempty := dvSideSet_nonempty F hg L.u L.hℓ
  obtain ⟨Mg, hpg⟩ := exists_pin F hng
  have hr := residual_dvd_of_muDvd L hπ hh hΨ hng Mg hpg hdvd
  have hdeg' : g.natDegree < L.keyDeg₂ := by
    rw [← hΨ.2.1]
    exact hdeg
  exact not_residual_dvd_of_natDegree_lt L hπ hdeg' hng Mg hpg hr

/-! ## Part 5 — ★ the primality head, PROVED -/

/-- ★ **The primality head, PROVED**: if the test key μ-divides a product of nonzero
factors, its prescribed residual `L.r` divides one factor's level residual.  Theorem M
clause 3 turns `L.r ∣ R(g·z)` into `L.r ∣ R(g)·R(z)`, and `L.r` is prime in `K[y]`
(irreducible by `L.hrirr`; `K[y]` is a UFD through `EuclideanDomain → PID`). -/
theorem residual_dvd_or_of_muDvd_mul (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ g z : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g L.u L.ℓ).Nonempty)
    (hnz : (dvSideSet F z L.u L.ℓ).Nonempty) (Mg Mz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z L.u L.ℓ hnz) = (Mz : ℕ∞))
    (hdvd : MuDvd L Ψ (g * z)) :
    L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg ∨
      L.r ∣ dvResPoly F H₀ hpin z L.u L.ℓ hnz Mz hpz := by
  have hgz : g * z ≠ 0 := mul_ne_zero hg hz
  have hngz : (dvSideSet F (g * z) L.u L.ℓ).Nonempty := dvSideSet_nonempty F hgz L.u L.hℓ
  obtain ⟨Mgz, hpgz⟩ := exists_pin F hngz
  have hr : L.r ∣ dvResPoly F H₀ hpin (g * z) L.u L.ℓ hngz Mgz hpgz :=
    residual_dvd_of_muDvd L hπ hh hΨ hngz Mgz hpgz hdvd
  have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop (inner_floor L)
    hg hz hng hnz hngz hpg hpz hpgz
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hprime : Prime L.r := UniqueFactorizationMonoid.irreducible_iff_prime.mp L.hrirr
  refine hprime.2.2 _ _ ?_
  rw [← hmul]
  exact hr

/-! ## Part 6 — μ-primality from the residual lift (the reduction; the lift itself is
Part 8's theorem) -/

/-- **The reduction**: the residual lift `L.r ∣ R(g) → Ψ ∣µ g` (for nonzero `g`, at every
side witness and finite pin) is the ONLY content of μ-primality beyond Part 5.  Kept in
factored form as the record of the exact narrow leg the retired cite would have supplied;
Part 8's `muDvd_of_residual_dvd` discharges it. -/
theorem muPrime_of_residualLift (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hlift : ∀ g : Polynomial O, g ≠ 0 →
      ∀ (hng : (dvSideSet F g L.u L.ℓ).Nonempty) (Mg : ℕ)
        (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞)),
        L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg → MuDvd L Ψ g) :
    MuPrime L Ψ := by
  intro g z hdvd
  rcases eq_or_ne g 0 with rfl | hg
  · exact Or.inl (muDvd_zero L)
  rcases eq_or_ne z 0 with rfl | hz
  · exact Or.inr (muDvd_zero L)
  have hng : (dvSideSet F g L.u L.ℓ).Nonempty := dvSideSet_nonempty F hg L.u L.hℓ
  have hnz : (dvSideSet F z L.u L.ℓ).Nonempty := dvSideSet_nonempty F hz L.u L.hℓ
  obtain ⟨Mg, hpg⟩ := exists_pin F hng
  obtain ⟨Mz, hpz⟩ := exists_pin F hnz
  rcases residual_dvd_or_of_muDvd_mul L hπ hh hΨ hg hz hng hnz Mg Mz hpg hpz hdvd
    with h | h
  · exact Or.inl (hlift g hg hng Mg hpg h)
  · exact Or.inr (hlift z hz hnz Mz hpz h)

/-! ## Part 7 — ★ the assembly -/

/-- ★ **The assembly**: `IsTestKey → IsMuKey`, modulo EXACTLY the μ-primality conjunct.
Monic is clause 1; μ-minimality is Part 4's theorem.  A narrow cite (or future proof) of
`MuPrime L Ψ` for test keys closes P1 through this theorem. -/
theorem isMuKey_of_isTestKey_of_muPrime (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hprime : MuPrime L Ψ) : IsMuKey L Ψ :=
  ⟨hΨ.1, muMinimal_of_isTestKey L hπ hh hΨ, hprime⟩

/-- ★ The assembly through the even-narrower residual-lift leg. -/
theorem isMuKey_of_isTestKey_of_residualLift (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hlift : ∀ g : Polynomial O, g ≠ 0 →
      ∀ (hng : (dvSideSet F g L.u L.ℓ).Nonempty) (Mg : ℕ)
        (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞)),
        L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg → MuDvd L Ψ g) :
    IsMuKey L Ψ :=
  isMuKey_of_isTestKey_of_muPrime L hπ hh hΨ (muPrime_of_residualLift L hπ hh hΨ hlift)

/-! ## Part 8 — ★★ the residual lift, PROVED: the cite dies

The backward translation `L.r ∣ R(g) → Ψ ∣µ g` — P1U's route (a), completed.  The
mechanism is the S2 `C130kp1.S2MuDvd_of_normRes_dvd` remainder pattern, frame-generic:
the μ-cofactor is the LITERAL quotient `g /ₘ Ψ`, the value comparison of the remainder
`g %ₘ Ψ` against `Ψ·(g /ₘ Ψ)` splits into the landed ultrametric cases, every excluded
branch dies on Part 2's degree count, and the one genuinely new tool is the `V`-line
read `lineRes` (the grade-line residual: additive by C130rp2's read additivity at a
common height floor, and equal to `dvResPoly · Xᵟ` by C26-style slot bookkeeping),
which settles the TIE branch. -/

private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx =
      dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

/-- The support at the left endpoint pin: `W(z) = ℓ·M + u·jmin` as a `ℕ`-numeral. -/
private theorem dvSupp_eq_line {u ℓ : ℕ} {z : Polynomial O}
    (hne : (dvSideSet F z u ℓ).Nonempty) {Mz : ℕ}
    (hpz : dvHgt F z (dvSideMin F z u ℓ hne) = (Mz : ℕ∞)) :
    dvSupp F z u ℓ = ((ℓ * Mz + u * dvSideMin F z u ℓ hne : ℕ) : ℕ∞) := by
  have hon : DvOnSide F z u ℓ (dvSideMin F z u ℓ hne) :=
    dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)
  rw [hon.1, hpz]
  push_cast [nsmul_eq_mul]
  ring

/-- Cross-polynomial `ℓ`-congruence of slots on a common value line (C.08's
`dvOnSide_modEq` pattern, freed from the single-polynomial binder). -/
private theorem line_modEq {u ℓ a b c d : ℕ} (hcop : Nat.Coprime u ℓ)
    (h : ℓ * a + u * b = ℓ * c + u * d) : b ≡ d [MOD ℓ] := by
  have hZ : (ℓ : ℤ) * (a : ℤ) + (u : ℤ) * (b : ℤ)
      = (ℓ : ℤ) * (c : ℤ) + (u : ℤ) * (d : ℤ) := by exact_mod_cast h
  have hdvd : (ℓ : ℤ) ∣ (u : ℤ) * ((d : ℤ) - (b : ℤ)) := ⟨(a : ℤ) - (c : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

private theorem mem_dvSideSet_of_dvOnSide' {z : Polynomial O} {u ℓ j : ℕ}
    (h : DvOnSide F z u ℓ j) : j ∈ dvSideSet F z u ℓ := by
  classical
  have hj : j ≤ z.natDegree := by
    by_contra hlt
    exact h.2 (C131y.dvHgt_eq_top_of_natDegree_lt F z (lt_of_not_ge hlt))
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hj, h⟩

/-- **The `V`-line read**, based at slot `j₀` with height `N₀`: the residual read along
the full line `ℓ·H + u·j = ℓ·N₀ + u·j₀`, truncated at the height floor `t ≤ N₀/u`. -/
private noncomputable def lineRes (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (z : Polynomial O) (u ℓ j₀ N₀ : ℕ) : Polynomial (F.stageField H₀ hpin) :=
  (Finset.range (N₀ / u + 1)).sum fun t =>
    Polynomial.C (F.twistRead H₀ hpin (N₀ - t * u) (dev F.key z (j₀ + t * ℓ)))
      * Polynomial.X ^ t

private theorem lineRes_coeff (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (z : Polynomial O) (u ℓ j₀ N₀ t : ℕ) :
    (lineRes F H₀ hpin z u ℓ j₀ N₀).coeff t
      = if t < N₀ / u + 1
        then F.twistRead H₀ hpin (N₀ - t * u) (dev F.key z (j₀ + t * ℓ))
        else 0 := by
  rw [lineRes, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]

/-- Cast extraction for the weighted line term (`≤` form). -/
private theorem nat_of_line_le {ℓ u j H V : ℕ}
    (h : ((V : ℕ) : ℕ∞) ≤ ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)) :
    V ≤ ℓ * H + u * j := by
  have hcast : ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)
      = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [hcast] at h
  exact_mod_cast h

/-- Cast extraction for the weighted line term (`<` form). -/
private theorem nat_of_line_lt {ℓ u j H V : ℕ}
    (h : ((V : ℕ) : ℕ∞) < ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)) :
    V < ℓ * H + u * j := by
  have hcast : ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)
      = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [hcast] at h
  exact_mod_cast h

/-- Every digit on or above a value floor prices its line height (the coefficientwise
height floor for the line read). -/
private theorem line_height_le {u ℓ : ℕ} (hℓ : 0 < ℓ) {z : Polynomial O}
    {j₀ N₀ V : ℕ} (hline : V = ℓ * N₀ + u * j₀)
    (hV : ((V : ℕ) : ℕ∞) ≤ dvSupp F z u ℓ) (t : ℕ) :
    ((N₀ - t * u : ℕ) : ℕ∞) ≤ F.stageHeight (dev F.key z (j₀ + t * ℓ)) := by
  have hterm := C131y.dvSupp_le_term F z u hℓ (j₀ + t * ℓ)
  have hcomb := le_trans hV hterm
  rcases eq_or_ne (dvHgt F z (j₀ + t * ℓ)) ⊤ with htop | hne
  · have hgoal : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ⊤ := htop
    rw [hgoal]
    exact le_top
  · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hH] at hcomb
    have hnat : V ≤ ℓ * H + u * (j₀ + t * ℓ) := nat_of_line_le hcomb
    have hkey : ℓ * N₀ ≤ ℓ * (H + u * t) := by
      have he : u * (j₀ + t * ℓ) = u * j₀ + ℓ * (u * t) := by ring
      have h2 : ℓ * (H + u * t) = ℓ * H + ℓ * (u * t) := by ring
      omega
    have hle : N₀ ≤ H + u * t := Nat.le_of_mul_le_mul_left hkey hℓ
    have hfin : N₀ - t * u ≤ H := by
      have hc : t * u = u * t := Nat.mul_comm t u
      omega
    have hstage : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ((H : ℕ) : ℕ∞) := hH.symm
    rw [hstage]
    exact_mod_cast hfin

/-- Line-read additivity at a common value floor (C130rp2's read additivity, applied
digitwise through B32a's linear development). -/
private theorem lineRes_add (hπ : Irreducible π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {x y : Polynomial O} {j₀ N₀ V : ℕ} (hline : V = ℓ * N₀ + u * j₀)
    (hVx : ((V : ℕ) : ℕ∞) ≤ dvSupp F x u ℓ) (hVy : ((V : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ) :
    lineRes F H₀ hpin (x + y) u ℓ j₀ N₀
      = lineRes F H₀ hpin x u ℓ j₀ N₀ + lineRes F H₀ hpin y u ℓ j₀ N₀ := by
  rw [lineRes, lineRes, lineRes, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dev_add_of_monic F.hmonic, C130rp2.twistRead_add_of_le F hπ H₀ hpin
    (line_height_le hℓ hline hVx t) (line_height_le hℓ hline hVy t),
    Polynomial.C_add, add_mul]

/-- The read of an off-side line slot vanishes: strictly-above digits are invisible at
the line height (C130rp2's `twistRead_eq_zero_of_lt`). -/
private theorem line_read_eq_zero_of_not_onSide (hπ : Irreducible π) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) {z : Polynomial O} {j₀ N₀ : ℕ}
    (hV : dvSupp F z u ℓ = ((ℓ * N₀ + u * j₀ : ℕ) : ℕ∞)) {t : ℕ} (ht : t * u ≤ N₀)
    (hoff : ¬ DvOnSide F z u ℓ (j₀ + t * ℓ)) :
    F.twistRead H₀ hpin (N₀ - t * u) (dev F.key z (j₀ + t * ℓ)) = 0 := by
  refine C130rp2.twistRead_eq_zero_of_lt F hπ H₀ hpin ?_
  rcases eq_or_ne (dvHgt F z (j₀ + t * ℓ)) ⊤ with htop | hne
  · have hgoal : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ⊤ := htop
    rw [hgoal]
    exact ENat.coe_lt_top _
  · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hne
    have hstrict : dvSupp F z u ℓ < ℓ • dvHgt F z (j₀ + t * ℓ) + (u * (j₀ + t * ℓ) : ℕ∞) :=
      lt_of_le_of_ne (C131y.dvSupp_le_term F z u hℓ (j₀ + t * ℓ))
        (fun heq => hoff ⟨heq, hne⟩)
    rw [hV, ← hH] at hstrict
    have hnat : ℓ * N₀ + u * j₀ < ℓ * H + u * (j₀ + t * ℓ) := nat_of_line_lt hstrict
    have hkey : ℓ * N₀ < ℓ * (H + u * t) := by
      have he : u * (j₀ + t * ℓ) = u * j₀ + ℓ * (u * t) := by ring
      have h2 : ℓ * (H + u * t) = ℓ * H + ℓ * (u * t) := by ring
      omega
    have hlt : N₀ < H + u * t := Nat.lt_of_mul_lt_mul_left hkey
    have hfin : N₀ - t * u < H := by
      have hc : t * u = u * t := Nat.mul_comm t u
      omega

    have hstage : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ((H : ℕ) : ℕ∞) := hH.symm
    rw [hstage]
    exact_mod_cast hfin

/-- ★ **The line read IS the shifted residual polynomial**: based anywhere on the value
line at or left of the side, `lineRes = R(z) · X^δ` with `δ` the slot offset to the
side's left endpoint. -/
private theorem lineRes_eq_shift (hπ : Irreducible π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hu : 0 < u) {z : Polynomial O}
    (hne : (dvSideSet F z u ℓ).Nonempty) {Mz : ℕ}
    (hpz : dvHgt F z (dvSideMin F z u ℓ hne) = (Mz : ℕ∞)) {j₀ N₀ : ℕ}
    (hj₀le : j₀ ≤ dvSideMin F z u ℓ hne)
    (hdvdℓ : ℓ ∣ dvSideMin F z u ℓ hne - j₀)
    (hlineEq : ℓ * N₀ + u * j₀ = ℓ * Mz + u * dvSideMin F z u ℓ hne) :
    lineRes F H₀ hpin z u ℓ j₀ N₀
      = dvResPoly F H₀ hpin z u ℓ hne Mz hpz
          * Polynomial.X ^ ((dvSideMin F z u ℓ hne - j₀) / ℓ) := by
  classical
  set jm := dvSideMin F z u ℓ hne with hjm
  set sd := dvSideDeg F z u ℓ hne with hsd
  set δ := (jm - j₀) / ℓ with hδdef
  have hδ : jm = j₀ + δ * ℓ := by
    have h : δ * ℓ = jm - j₀ := by
      rw [hδdef]
      exact Nat.div_mul_cancel hdvdℓ
    omega
  have hN₀ : N₀ = Mz + u * δ := by
    have hexp : u * jm = u * j₀ + ℓ * (u * δ) := by rw [hδ]; ring
    rw [hexp] at hlineEq
    have h2 : ℓ * N₀ = ℓ * (Mz + u * δ) := by
      have h3 : ℓ * (Mz + u * δ) = ℓ * Mz + ℓ * (u * δ) := by ring
      omega
    exact Nat.eq_of_mul_eq_mul_left hℓ h2
  have hV : dvSupp F z u ℓ = ((ℓ * N₀ + u * j₀ : ℕ) : ℕ∞) := by
    rw [dvSupp_eq_line hne hpz, hlineEq]
  -- the length law pins `jmax = jmin + ℓ·sd` and `Mz = Hmax + u·sd`
  have hmaxmem : dvSideMax F z u ℓ hne ∈ dvSideSet F z u ℓ := Finset.max'_mem _ _
  have hminle : jm ≤ dvSideMax F z u ℓ hne := Finset.min'_le _ _ hmaxmem
  have hlen : dvSideMax F z u ℓ hne - jm = ℓ * sd := by
    have h := dvSideLen_eq F hℓ hcop hne
    rw [dvSideLen] at h
    exact h
  have hjmax : dvSideMax F z u ℓ hne = jm + ℓ * sd := by omega
  have honmax := dvOnSide_of_mem_dvSideSet hmaxmem
  obtain ⟨Hmax, hHmax⟩ := ENat.ne_top_iff_exists.1 honmax.2
  have hmaxline : ℓ * Mz + u * jm = ℓ * Hmax + u * dvSideMax F z u ℓ hne := by
    have h1 : dvSupp F z u ℓ
        = ((ℓ * Hmax + u * dvSideMax F z u ℓ hne : ℕ) : ℕ∞) := by
      rw [honmax.1, ← hHmax]
      push_cast [nsmul_eq_mul]
      ring
    have h2 := (dvSupp_eq_line hne hpz).symm.trans h1
    exact_mod_cast h2
  have hMzfloor : u * sd ≤ Mz := by
    rw [hjmax] at hmaxline
    have hexp : u * (jm + ℓ * sd) = u * jm + ℓ * (u * sd) := by ring
    rw [hexp] at hmaxline
    have h2 : ℓ * Mz = ℓ * (Hmax + u * sd) := by
      have h3 : ℓ * (Hmax + u * sd) = ℓ * Hmax + ℓ * (u * sd) := by ring
      omega
    have := Nat.eq_of_mul_eq_mul_left hℓ h2
    omega
  have hTδ : δ + sd ≤ N₀ / u := by
    refine (Nat.le_div_iff_mul_le hu).mpr ?_
    calc (δ + sd) * u = u * sd + u * δ := by ring
      _ ≤ Mz + u * δ := by omega
      _ = N₀ := hN₀.symm
  -- the residual degree
  have hRdeg : (dvResPoly F H₀ hpin z u ℓ hne Mz hpz).natDegree = sd :=
    (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hpz).1
  refine Polynomial.ext fun s => ?_
  rw [lineRes_coeff, Polynomial.coeff_mul_X_pow']
  by_cases hsδ : δ ≤ s
  · rw [if_pos hsδ]
    set t := s - δ with htdef
    have hst : s = δ + t := by omega
    by_cases hts : t ≤ sd
    · -- the on-window band: both sides read the same slot at the same height
      have hsT : s < N₀ / u + 1 := by omega
      rw [if_pos hsT]
      have hRcoeff : (dvResPoly F H₀ hpin z u ℓ hne Mz hpz).coeff t
          = F.twistRead H₀ hpin (Mz - t * u) (dev F.key z (jm + t * ℓ)) := by
        rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
          if_pos (Nat.lt_succ_of_le hts)]
      rw [hRcoeff]
      have hslot : j₀ + s * ℓ = jm + t * ℓ := by
        rw [hδ, hst]
        ring
      have hheight : N₀ - s * u = Mz - t * u := by
        have hsu : s * u = u * δ + t * u := by rw [hst]; ring
        rw [hsu, hN₀]
        omega
      rw [hslot, hheight]
    · -- past the side's right endpoint: both sides vanish
      have hRzero : (dvResPoly F H₀ hpin z u ℓ hne Mz hpz).coeff t = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [hRdeg]
        omega
      rw [hRzero]
      by_cases hsT : s < N₀ / u + 1
      · rw [if_pos hsT]
        have hsu : s * u ≤ N₀ :=
          le_trans (Nat.mul_le_mul_right u (Nat.lt_succ_iff.mp hsT))
            (Nat.div_mul_le_self N₀ u)
        refine line_read_eq_zero_of_not_onSide hπ hℓ hV hsu ?_
        intro hon
        have hmem := mem_dvSideSet_of_dvOnSide' hon
        have hle : j₀ + s * ℓ ≤ dvSideMax F z u ℓ hne := Finset.le_max' _ _ hmem
        rw [hjmax] at hle
        have hslot : j₀ + s * ℓ = jm + t * ℓ := by
          rw [hδ, hst]
          ring
        rw [hslot] at hle
        have : t ≤ sd := by
          have h2 : t * ℓ ≤ ℓ * sd := by omega
          have h3 : ℓ * t ≤ ℓ * sd := by rw [Nat.mul_comm ℓ t]; exact h2
          exact Nat.le_of_mul_le_mul_left h3 hℓ
        omega
      · rw [if_neg hsT]
  · -- left of the side's left endpoint: both sides vanish
    rw [if_neg hsδ]
    have hsT : s < N₀ / u + 1 := by omega
    rw [if_pos hsT]
    have hsu : s * u ≤ N₀ :=
      le_trans (Nat.mul_le_mul_right u (Nat.lt_succ_iff.mp hsT))
        (Nat.div_mul_le_self N₀ u)
    refine line_read_eq_zero_of_not_onSide hπ hℓ hV hsu ?_
    intro hon
    have hmem := mem_dvSideSet_of_dvOnSide' hon
    have hle : jm ≤ j₀ + s * ℓ := Finset.min'_le _ _ hmem
    rw [hδ] at hle
    have hlt : s * ℓ < δ * ℓ :=
      (Nat.mul_lt_mul_right hℓ).mpr (lt_of_not_ge hsδ)
    omega

/-- ★ **The tie transfer**: at a three-way value tie `W(x) = W(y) = W(x+y)`, a prime
residual factor with nonzero constant term dividing `R(x+y)` and `R(y)` divides `R(x)`.
The line read is additive and equals the shifted residual on each summand, and `p`
coprime to `X` strips the shifts. -/
private theorem residual_dvd_left_of_tie (hπ : Irreducible π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hu : 0 < u)
    {p : Polynomial (F.stageField H₀ hpin)} (hpirr : Irreducible p) (hp0 : p.coeff 0 ≠ 0)
    {x y : Polynomial O}
    (hnx : (dvSideSet F x u ℓ).Nonempty) (hny : (dvSideSet F y u ℓ).Nonempty)
    (hnxy : (dvSideSet F (x + y) u ℓ).Nonempty)
    {Mx My Mxy : ℕ}
    (hpx : dvHgt F x (dvSideMin F x u ℓ hnx) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hny) = (My : ℕ∞))
    (hpxy : dvHgt F (x + y) (dvSideMin F (x + y) u ℓ hnxy) = (Mxy : ℕ∞))
    (hVy : dvSupp F y u ℓ = dvSupp F x u ℓ)
    (hVxy : dvSupp F (x + y) u ℓ = dvSupp F x u ℓ)
    (hdy : p ∣ dvResPoly F H₀ hpin y u ℓ hny My hpy)
    (hdxy : p ∣ dvResPoly F H₀ hpin (x + y) u ℓ hnxy Mxy hpxy) :
    p ∣ dvResPoly F H₀ hpin x u ℓ hnx Mx hpx := by
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  set jx := dvSideMin F x u ℓ hnx with hjx
  set jy := dvSideMin F y u ℓ hny with hjy
  set jxy := dvSideMin F (x + y) u ℓ hnxy with hjxy
  -- the three ℕ line equations
  have hLx := dvSupp_eq_line hnx hpx
  have hLy := dvSupp_eq_line hny hpy
  have hLxy := dvSupp_eq_line hnxy hpxy
  have hEy : ℓ * My + u * jy = ℓ * Mx + u * jx := by
    have h := (hLy.symm.trans hVy).trans hLx
    exact_mod_cast h
  have hExy : ℓ * Mxy + u * jxy = ℓ * Mx + u * jx := by
    have h := (hLxy.symm.trans hVxy).trans hLx
    exact_mod_cast h
  -- the common base point of the line: `j₀ = jx % ℓ`, `N₀` its height
  set j₀ := jx % ℓ with hj₀
  set N₀ := Mx + u * (jx / ℓ) with hN₀
  have hlineX : ℓ * N₀ + u * j₀ = ℓ * Mx + u * jx := by
    have h1 : ℓ * (Mx + u * (jx / ℓ)) + u * (jx % ℓ)
        = ℓ * Mx + u * (ℓ * (jx / ℓ) + jx % ℓ) := by ring
    rw [hN₀, hj₀, h1, Nat.div_add_mod]
  -- slot congruences: everything sits on one residue class mod ℓ
  have hmody : jy % ℓ = j₀ := by
    have h := line_modEq hcop hEy
    exact h.trans rfl
  have hmodxy : jxy % ℓ = j₀ := by
    have h := line_modEq hcop hExy
    exact h.trans rfl
  have hmodx : jx % ℓ = j₀ := rfl
  -- per-summand base data
  have hbase : ∀ (jz : ℕ), jz % ℓ = j₀ → j₀ ≤ jz ∧ ℓ ∣ jz - j₀ := by
    intro jz hz
    constructor
    · rw [← hz]
      exact Nat.mod_le jz ℓ
    · refine ⟨jz / ℓ, ?_⟩
      have := Nat.div_add_mod jz ℓ
      omega
  obtain ⟨hj₀x, hdx⟩ := hbase jx hmodx
  obtain ⟨hj₀y, hdy'⟩ := hbase jy hmody
  obtain ⟨hj₀xy, hdxy'⟩ := hbase jxy hmodxy
  have hlineY : ℓ * N₀ + u * j₀ = ℓ * My + u * jy := hlineX.trans hEy.symm
  have hlineXY : ℓ * N₀ + u * j₀ = ℓ * Mxy + u * jxy := hlineX.trans hExy.symm
  -- the three shifted-residual readings of the line read
  have hSx := lineRes_eq_shift (H₀ := H₀) (hpin := hpin) hπ hℓ hcop hu hnx hpx
    hj₀x hdx hlineX
  have hSy := lineRes_eq_shift (H₀ := H₀) (hpin := hpin) hπ hℓ hcop hu hny hpy
    hj₀y hdy' hlineY
  have hSxy := lineRes_eq_shift (H₀ := H₀) (hpin := hpin) hπ hℓ hcop hu hnxy hpxy
    hj₀xy hdxy' hlineXY
  -- additivity at the common value
  set V := ℓ * N₀ + u * j₀ with hVdef
  have hVX : ((V : ℕ) : ℕ∞) ≤ dvSupp F x u ℓ := by
    rw [hLx]
    exact le_of_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hlineX)
  have hVY : ((V : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ := by
    rw [hLy]
    exact le_of_eq (congrArg (fun n : ℕ => (n : ℕ∞)) (hlineX.trans hEy.symm))
  have hadd := lineRes_add (H₀ := H₀) (hpin := hpin) hπ hℓ (V := V) hVdef hVX hVY
  -- p divides the x-line read
  have hdivsum : p ∣ lineRes F H₀ hpin (x + y) u ℓ j₀ N₀ := by
    rw [hSxy]
    exact Dvd.dvd.mul_right hdxy _
  have hdivy : p ∣ lineRes F H₀ hpin y u ℓ j₀ N₀ := by
    rw [hSy]
    exact Dvd.dvd.mul_right hdy _
  have hdivx : p ∣ lineRes F H₀ hpin x u ℓ j₀ N₀ := by
    have h : lineRes F H₀ hpin x u ℓ j₀ N₀
        = lineRes F H₀ hpin (x + y) u ℓ j₀ N₀ - lineRes F H₀ hpin y u ℓ j₀ N₀ := by
      rw [hadd]
      ring
    rw [h]
    exact dvd_sub hdivsum hdivy
  -- strip the X-power: p is prime with nonzero constant term
  rw [hSx] at hdivx
  have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr
  rcases hprime.2.2 _ _ hdivx with h | h
  · exact h
  · exfalso
    have hX : p ∣ Polynomial.X := hprime.dvd_of_dvd_pow h
    obtain ⟨c, hc⟩ := hX
    rcases (Polynomial.irreducible_X (R := F.stageField H₀ hpin)).isUnit_or_isUnit hc
      with hup | huc
    · exact hpirr.1 hup
    · obtain ⟨r, hr, hcr⟩ := Polynomial.isUnit_iff.mp huc
      apply hp0
      have hcoeff : (Polynomial.X : Polynomial (F.stageField H₀ hpin)).coeff 0
          = p.coeff 0 * r := by
        rw [hc, ← hcr, Polynomial.coeff_mul_C]
      rw [Polynomial.coeff_X_zero] at hcoeff
      rcases mul_eq_zero.mp hcoeff.symm with h0 | h0
      · exact h0
      · exact absurd h0 hr.ne_zero

/-- ★★ **The residual lift, PROVED — P1's backward translation, frame-generic** (the
S2 `C130kp1.S2MuDvd_of_normRes_dvd` mechanism at the level valuation): if the test key's
prescribed residual divides `R(a)`, the key μ-divides `a`, with the LITERAL quotient
`a /ₘ Ψ` as μ-cofactor.  The tie branch is the line-read transfer; every other branch is
the landed ultrametric bank plus Part 2's degree count. -/
theorem muDvd_of_residual_dvd (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    {a : Polynomial O} (ha : a ≠ 0)
    (hna : (dvSideSet F a L.u L.ℓ).Nonempty) (Ma : ℕ)
    (hpa : dvHgt F a (dvSideMin F a L.u L.ℓ hna) = (Ma : ℕ∞))
    (hdvd : L.r ∣ dvResPoly F H₀ hpin a L.u L.ℓ hna Ma hpa) :
    MuDvd L Ψ a := by
  classical
  have hu : 0 < L.u := lt_of_le_of_lt (Nat.zero_le _) L.hκ
  have hΨm : Ψ.Monic := hΨ.1
  have hΨd : 0 < Ψ.natDegree := natDegree_pos_of_isTestKey L hΨ
  have hΨne1 : Ψ ≠ 1 := fun h1 => by simp [h1] at hΨd
  -- below the recipe degree the hypothesis is impossible
  by_cases hsmall : a.natDegree < Ψ.natDegree
  · exact absurd hdvd (not_residual_dvd_of_natDegree_lt L hπ (hΨ.2.1 ▸ hsmall) hna Ma hpa)
  have hge : Ψ.natDegree ≤ a.natDegree := le_of_not_gt hsmall
  set r := a %ₘ Ψ with hrdef
  set q := a /ₘ Ψ with hqdef
  have hab : r + Ψ * q = a := Polynomial.modByMonic_add_div a Ψ
  have hq0 : q ≠ 0 := by
    intro h0
    have hdlt := (Polynomial.divByMonic_eq_zero_iff hΨm).mp h0
    have := Polynomial.natDegree_lt_natDegree ha hdlt
    omega
  have hΨq0 : Ψ * q ≠ 0 := mul_ne_zero hΨm.ne_zero hq0
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- exact division: the quotient is the witness outright
    have haq : Ψ * q = a := by rw [← hab, hr0, zero_add]
    refine ⟨q, Or.inl ⟨?_, ?_⟩⟩
    · rw [haq, sub_self, dvSupp_zero_eq_top F L.u L.hℓ]
      exact Ne.lt_top (dvSupp_ne_top_of_ne_zero F L.u L.ℓ ha)
    · rw [haq]
  · -- the remainder is live: compare its value against the quotient term's
    have hdegr : r.natDegree < Ψ.natDegree := Polynomial.natDegree_modByMonic_lt a hΨm hΨne1
    have hnr : (dvSideSet F r L.u L.ℓ).Nonempty := dvSideSet_nonempty F hr0 L.u L.hℓ
    have hnΨq : (dvSideSet F (Ψ * q) L.u L.ℓ).Nonempty :=
      dvSideSet_nonempty F hΨq0 L.u L.hℓ
    obtain ⟨Mr, hpr⟩ := exists_pin F hnr
    obtain ⟨MΨq, hpΨq⟩ := exists_pin F hnΨq
    -- the reusable kill: `L.r ∣ R(r)` is impossible below the recipe degree
    have hkill : ¬ L.r ∣ dvResPoly F H₀ hpin r L.u L.ℓ hnr Mr hpr :=
      not_residual_dvd_of_natDegree_lt L hπ (hΨ.2.1 ▸ hdegr) hnr Mr hpr
    rcases lt_trichotomy (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ)
      with hlt | htie | hgt
    · -- the remainder undercuts: `a ∼µ r`, so `L.r ∣ R(r)` — killed
      exfalso
      have heqa : dvSupp F a L.u L.ℓ = dvSupp F r L.u L.ℓ := by
        rw [← hab]
        exact dvSupp_add_eq_of_lt F L.hℓ hlt
      have hMuE : MuEquiv L a r := by
        refine Or.inl ⟨?_, heqa⟩
        have hsub : a - r = Ψ * q := by rw [← hab]; ring
        rw [hsub, heqa]
        exact hlt
      have hReq := C134p1.dvResPoly_eq_of_muEquiv L hπ hMuE hna hnr hpa hpr
      exact hkill (hReq ▸ hdvd)
    · -- the TIE
      have hVa : dvSupp F r L.u L.ℓ ≤ dvSupp F a L.u L.ℓ := by
        have h := min_dvSupp_le_dvSupp_add (u := L.u) F L.hℓ r (Ψ * q)
        rw [hab, ← htie, min_self] at h
        exact h
      rcases eq_or_lt_of_le hVa with heqa | hlta
      · -- full tie: the line-read transfer forces `L.r ∣ R(r)` — killed
        exfalso
        have hnΨ : (dvSideSet F Ψ L.u L.ℓ).Nonempty :=
          dvSideSet_nonempty F hΨm.ne_zero L.u L.hℓ
        have hnq : (dvSideSet F q L.u L.ℓ).Nonempty := dvSideSet_nonempty F hq0 L.u L.hℓ
        obtain ⟨MΨ, hpΨ⟩ := exists_pin F hnΨ
        obtain ⟨Mq, hpq⟩ := exists_pin F hnq
        have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop (inner_floor L)
          hΨm.ne_zero hq0 hnΨ hnq hnΨq hpΨ hpq hpΨq
        have hdΨq : L.r ∣ dvResPoly F H₀ hpin (Ψ * q) L.u L.ℓ hnΨq MΨq hpΨq := by
          rw [hmul, dvResPoly_testKey hπ L hΨ hnΨ MΨ hpΨ]
          exact Dvd.intro _ rfl
        have hnsum : (dvSideSet F (r + Ψ * q) L.u L.ℓ).Nonempty := by
          rw [hab]
          exact hna
        obtain ⟨Ms, hps⟩ := exists_pin F hnsum
        have hdsum : L.r ∣ dvResPoly F H₀ hpin (r + Ψ * q) L.u L.ℓ hnsum Ms hps := by
          rw [dvResPoly_congr F H₀ hpin hab hnsum hna hps hpa]
          exact hdvd
        have hVsum : dvSupp F (r + Ψ * q) L.u L.ℓ = dvSupp F r L.u L.ℓ := by
          rw [hab]
          exact heqa.symm
        exact hkill (residual_dvd_left_of_tie hπ L.hℓ L.hcop hu L.hrirr L.hr0
          hnr hnΨq hnsum hpr hpΨq hps htie.symm hVsum hdΨq hdsum)
      · -- tie with cancellation: `Ψ ∣µ r` outright — killed by the forward bridge
        exfalso
        have hMuDvdr : MuDvd L Ψ r := by
          refine ⟨-q, Or.inl ⟨?_, ?_⟩⟩
          · have hsub : r - Ψ * -q = a := by rw [mul_neg, sub_neg_eq_add, hab]
            rw [hsub]
            exact hlta
          · rw [mul_neg, dvSupp_neg]
            exact htie
        exact hkill (residual_dvd_of_muDvd L hπ hh hΨ hnr Mr hpr hMuDvdr)
    · -- the quotient term undercuts: it IS the initial part — the witness fires
      have heqa : dvSupp F a L.u L.ℓ = dvSupp F (Ψ * q) L.u L.ℓ := by
        rw [← hab, add_comm]
        exact dvSupp_add_eq_of_lt F L.hℓ hgt
      refine ⟨q, Or.inl ⟨?_, heqa⟩⟩
      have hsub : a - Ψ * q = r := by rw [← hab]; ring
      rw [hsub, heqa]
      exact hgt

/-! ## Part 9 — ★★ P1 CLOSED: `IsTestKey → IsMuKey` is a THEOREM -/

/-- ★★ **The μ-primality conjunct, PROVED** — the residual lift discharges Part 6's
hypothesis, so the GN Lemma 3.1(3) cite is not needed. -/
theorem muPrime_of_isTestKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    MuPrime L Ψ :=
  muPrime_of_residualLift L hπ hh hΨ fun _g hg hng Mg hpg hdvd =>
    muDvd_of_residual_dvd L hπ hh hΨ hg hng Mg hpg hdvd

/-- ★★ **P1, CLOSED OUTRIGHT**: every level-2 test key is an FGMN key polynomial for the
level valuation — `IsTestKey L Ψ → IsMuKey L Ψ` as a theorem, Lean-core, no cite.  This
is exactly the statement P1U drafted as the `isMuKey_of_isTestKey` axiom. -/
theorem isMuKey_of_isTestKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    IsMuKey L Ψ :=
  isMuKey_of_isTestKey_of_muPrime L hπ hh hΨ (muPrime_of_isTestKey L hπ hh hΨ)

end Uniformity.Density.Tower.C134p1d

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134p1d.natDegree_pos_of_isTestKey
#print axioms Uniformity.Density.Tower.C134p1d.not_residual_dvd_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C134p1d.residual_dvd_of_muDvd
#print axioms Uniformity.Density.Tower.C134p1d.muMinimal_of_isTestKey
#print axioms Uniformity.Density.Tower.C134p1d.residual_dvd_or_of_muDvd_mul
#print axioms Uniformity.Density.Tower.C134p1d.muPrime_of_residualLift
#print axioms Uniformity.Density.Tower.C134p1d.isMuKey_of_isTestKey_of_muPrime
#print axioms Uniformity.Density.Tower.C134p1d.isMuKey_of_isTestKey_of_residualLift
#print axioms Uniformity.Density.Tower.C134p1d.muDvd_of_residual_dvd
#print axioms Uniformity.Density.Tower.C134p1d.muPrime_of_isTestKey
#print axioms Uniformity.Density.Tower.C134p1d.isMuKey_of_isTestKey

end AxCheck
