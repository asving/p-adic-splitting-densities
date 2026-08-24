/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131aa
import Uniformity.ChapC.C66b
import Uniformity.ChapC.C47
import Uniformity.ChapC.C51

/-!
# Uniformity.ChapC.C131ac — exact powers and `composedKey_pow_mem_towerLocus`

**Chapter C, NODE C.131ac′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md`, §4.3 (E3) and §5).

The exact-power half of the dv-graded engine's exact side, and its first consumer.  The
gate-(b) cite `fgmn_dv_exact_mul` (C66b — FGMN, J. Algebra 427 (2015), Thm 2.8 +
Cor 4.12(3)) supplies ONE multiplication; the induction to powers is a THEOREM here
(`fgmn_dv_exact_pow`, the name C66b's docstring reserves), exactly as the blueprint
mandates: side witnesses come from purity's own left endpoint, finite pins from
`DvOnSide`'s finiteness conjunct, and witness-independence from the fact that `dvSideMin`
is a definition and a finite `ℕ∞` pin is unique (`dvResPoly_eq_of_eq`).

The headline is C.52's Step 1 (`EFF.GENTOW1.20`), stated at the C52-record signature:
`Φ₂^{μ₂} ∈ towerLocus T μ₂` — the composed key's power lies on the locus it fences.  Its
four `towerLocus` conjuncts are discharged by C.47 (monicity, degree), C.131aa′
(`isTestKey_isDvPure`), the power theorem, and C.131ab′ (`dvResPoly_testKey`) feeding the
exact residual power `towerLabel T ^ μ₂`.

## Axiom discipline

`fgmn_dv_exact_mul` is a DECLARED literature cite (allowlist member 7, C66b), not a new
axiom.  Declarations consuming it — `fgmn_dv_exact_pow`, `isDvPure_pow`,
`dvResPoly_pow_exact`, `composedKey_pow_mem_towerLocus` — show it in their footprint BY
DESIGN.  The two witness utilities (`exists_dvHgt_pin`, `dvResPoly_eq_of_eq`) are
Lean-core.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The finite pin exists on any nonempty side.**  The side minimum is a member
(`Finset.min'_mem`), and `DvOnSide`'s second conjunct makes its height finite, hence a
numeral.  (C.48 and C.118b inline this argument; it is exported here because the power
induction needs it at every stage.) -/
theorem exists_dvHgt_pin {F : KeyFrame O π} {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  have hminmem : dvSideMin F f u ℓ hne ∈ dvSideSet F f u ℓ := Finset.min'_mem _ _
  have hfin : dvHgt F f (dvSideMin F f u ℓ hne) ≠ ⊤ :=
    (dvOnSide_of_mem_dvSideSet hminmem).2
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hfin
  exact ⟨M, hM.symm⟩

/-- **Witness-independence of the normalized residual.**  `dvResPoly` depends on its side
witness and pin only through the polynomial: `hne` is a `Prop` (proof-irrelevant), and a
finite pin is unique because `ℕ → ℕ∞` is injective.  This is the blueprint's
"witness-independence follows because `dvSideMin` is a definition and equality to a finite
natural pin is unique", packaged once.  (C.118b's `dvResPoly_congr` is a DIFFERENT
statement — congruence of the polynomial modulo a cap — hence the distinct name.) -/
theorem dvResPoly_eq_of_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {f f' : Polynomial O} (hff' : f = f') {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) (hne' : (dvSideSet F f' u ℓ).Nonempty)
    {M M' : ℕ} (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞))
    (hp' : dvHgt F f' (dvSideMin F f' u ℓ hne') = (M' : ℕ∞)) :
    dvResPoly F H₀ hpin f u ℓ hne M hp = dvResPoly F H₀ hpin f' u ℓ hne' M' hp' := by
  subst hff'
  obtain rfl : M = M' := by exact_mod_cast hp.symm.trans hp'
  rfl

/-- ★ **NODE C.131ac′ (E3, combined form): exact powers of a pure polynomial.**  If `g` is
monic, `(u, ℓ)`-pure at the frame's dv-carrier, and satisfies the gate fences (positive
coprime slope above the frame floor, `D′ ∣ deg g > 0`), then for every `0 < n` the power
`g^n` is `(u, ℓ)`-pure and EVERY normalized residual read of `g^n` is the `n`-th power of
`g`'s.  Induction on `n` through the gate-(b) cite `fgmn_dv_exact_mul` (C66b): side
witnesses at each stage come from purity's left endpoint `0 ∈ dvSideSet`, pins from
`exists_dvHgt_pin`.  **Carries the cite in its footprint by design.** -/
theorem fgmn_dv_exact_pow {F : KeyFrame O π} (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {g : Polynomial O} (hg : g.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hpos : 0 < g.natDegree)
    (hpg : IsDvPure F g u ℓ) {n : ℕ} (hn : 0 < n)
    (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)) :
    IsDvPure F (g ^ n) u ℓ ∧
      ∀ (hneN : (dvSideSet F (g ^ n) u ℓ).Nonempty) (M : ℕ)
        (hpN : dvHgt F (g ^ n) (dvSideMin F (g ^ n) u ℓ hneN) = (M : ℕ∞)),
        dvResPoly F H₀ hpin (g ^ n) u ℓ hneN M hpN
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero =>
    constructor
    · simpa using hpg
    · intro hneN M hpN
      rw [dvResPoly_eq_of_eq (by simp : g ^ (0 + 1) = g) hneN hne hpN hp]
      simp
  | succ k ih =>
    obtain ⟨hpureK, hresK⟩ := ih
    -- stage witnesses for `g ^ (k+1)`: the left endpoint of its pure side, and its pin
    have hgk : (g ^ (k + 1)).Monic := hg.pow (k + 1)
    have hneK : (dvSideSet F (g ^ (k + 1)) u ℓ).Nonempty := ⟨0, hpureK.1⟩
    obtain ⟨MK, hpK⟩ := exists_dvHgt_pin hneK
    -- the gate fences at `g ^ (k+1)`
    have hdgK : F.e₁ * F.f₁ ∣ (g ^ (k + 1)).natDegree := by
      rw [hg.natDegree_pow]
      exact hdg.mul_left (k + 1)
    have hposK : 0 < (g ^ (k + 1)).natDegree := by
      rw [hg.natDegree_pow]
      exact Nat.mul_pos (Nat.succ_pos k) hpos
    -- ONE multiplication through the cite
    have hmul := fgmn_dv_exact_mul hπ H₀ hpin hgk hg hℓ hcop hfloor hdgK hdg hposK hpos
      hpureK hpg
    have hstep : g ^ (k + 1 + 1) = g ^ (k + 1) * g := pow_succ g (k + 1)
    refine ⟨by rw [hstep]; exact hmul.1, ?_⟩
    intro hneN M hpN
    have hneMul : (dvSideSet F (g ^ (k + 1) * g) u ℓ).Nonempty := ⟨0, hmul.1.1⟩
    obtain ⟨MM, hpM⟩ := exists_dvHgt_pin hneMul
    calc dvResPoly F H₀ hpin (g ^ (k + 1 + 1)) u ℓ hneN M hpN
        = dvResPoly F H₀ hpin (g ^ (k + 1) * g) u ℓ hneMul MM hpM :=
          dvResPoly_eq_of_eq hstep hneN hneMul hpN hpM
      _ = dvResPoly F H₀ hpin (g ^ (k + 1)) u ℓ hneK MK hpK
            * dvResPoly F H₀ hpin g u ℓ hne M₀ hp :=
          hmul.2 hneK hne hneMul MK M₀ MM hpK hp hpM
      _ = dvResPoly F H₀ hpin g u ℓ hne M₀ hp ^ (k + 1)
            * dvResPoly F H₀ hpin g u ℓ hne M₀ hp := by
          rw [hresK hneK MK hpK]
      _ = dvResPoly F H₀ hpin g u ℓ hne M₀ hp ^ (k + 1 + 1) := (pow_succ _ (k + 1)).symm

/-- **E3, purity projection (`isDvPure_pow`):** `dv`-purity is closed under positive powers
at the gate fences.  **Carries the cite.** -/
theorem isDvPure_pow {F : KeyFrame O π} (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {g : Polynomial O} (hg : g.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hpos : 0 < g.natDegree)
    (hpg : IsDvPure F g u ℓ) {n : ℕ} (hn : 0 < n) :
    IsDvPure F (g ^ n) u ℓ := by
  have hne : (dvSideSet F g u ℓ).Nonempty := ⟨0, hpg.1⟩
  obtain ⟨M₀, hp⟩ := exists_dvHgt_pin hne
  exact (fgmn_dv_exact_pow hπ H₀ hpin hg hℓ hcop hfloor hdg hpos hpg hn hne M₀ hp).1

/-- **E3, residual projection (`dvResPoly_pow_exact`):** every normalized residual read of
`g^n` is the `n`-th power of `g`'s, at arbitrary side witnesses and pins on both sides.
**Carries the cite.** -/
theorem dvResPoly_pow_exact {F : KeyFrame O π} (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {g : Polynomial O} (hg : g.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hpos : 0 < g.natDegree)
    (hpg : IsDvPure F g u ℓ) {n : ℕ} (hn : 0 < n)
    (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
    (hneN : (dvSideSet F (g ^ n) u ℓ).Nonempty) (M : ℕ)
    (hpN : dvHgt F (g ^ n) (dvSideMin F (g ^ n) u ℓ hneN) = (M : ℕ∞)) :
    dvResPoly F H₀ hpin (g ^ n) u ℓ hneN M hpN
      = dvResPoly F H₀ hpin g u ℓ hne M₀ hp ^ n :=
  (fgmn_dv_exact_pow hπ H₀ hpin hg hℓ hcop hfloor hdg hpos hpg hn hne M₀ hp).2 hneN M hpN

/-- ★ **C.52 Step 1 (`EFF.GENTOW1.20`): the composed key's power lies on the locus it
fences,** `Φ₂^{μ₂} ∈ towerLocus T μ₂`.  Monicity and degree are C.47's; purity of `Φ₂` is
C.131aa′'s `isTestKey_isDvPure`; the exact residual `towerLabel T ^ μ₂` is C.131ab′'s
`dvResPoly_testKey` raised through `fgmn_dv_exact_pow`.  The gate fences hold at the
composed key: `hfloor` is C.42's node floor `T.hfloor` reassociated, and
`D′ ∣ deg Φ₂ = D′·e₂·f₂ > 0`.  **Carries the cite.** -/
theorem composedKey_pow_mem_towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂) :
    composedKey T ^ μ₂ ∈ towerLocus T μ₂ := by
  classical
  have hTest : IsTestKey (T.levelDatum hπ) (composedKey T) := composedKey_isTestKey T hπ hh
  have hmonic : (composedKey T).Monic := composedKey_monic T
  have hpure : IsDvPure F (composedKey T) T.u₂ T.e₂ :=
    isTestKey_isDvPure (T.levelDatum hπ) hTest
  -- the dictionary numeral: `keyDeg₂ = D₂` (C.48's pattern)
  have hD2 : (T.levelDatum hπ).keyDeg₂ = T.D₂ := by
    have hr : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
    rw [LevelDatum.keyDeg₂, hr, show (T.levelDatum hπ).ℓ = T.e₂ from rfl, TowerDatum.D₂]
    ring
  -- the gate fences at the composed key
  have hfloor' : T.e₂ * ((F.e₁ * F.f₁) * F.h) < T.u₂ := by
    rw [← Nat.mul_assoc]
    exact T.hfloor
  have hdg : F.e₁ * F.f₁ ∣ (composedKey T).natDegree :=
    ⟨(T.levelDatum hπ).ℓ * (T.levelDatum hπ).r.natDegree, by
      rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂]; ring⟩
  have hpos : 0 < (composedKey T).natDegree := by
    rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (T.levelDatum hπ).hℓ)
      (T.levelDatum hπ).hrdeg
  -- the base witness and pin for `Φ₂` itself
  have hne₀ : (dvSideSet F (composedKey T) T.u₂ T.e₂).Nonempty := ⟨0, hpure.1⟩
  obtain ⟨M₀b, hp₀b⟩ := exists_dvHgt_pin hne₀
  have hpow := fgmn_dv_exact_pow hπ H₀ hpin hmonic T.he₂ T.hcop hfloor' hdg hpos hpure
    hμ₂ hne₀ M₀b hp₀b
  -- the exact residual of the base key is the tower label (C.131ab′)
  have hR : dvResPoly F H₀ hpin (composedKey T) T.u₂ T.e₂ hne₀ M₀b hp₀b
      = towerLabel T := dvResPoly_testKey hπ (T.levelDatum hπ) hTest hne₀ M₀b hp₀b
  refine ⟨hmonic.pow μ₂, ?_, hpow.1, ?_⟩
  · rw [hmonic.natDegree_pow, composedKey_natDegree T hπ, hD2]
  · intro hne M₀ hp
    rw [hpow.2 hne M₀ hp, hR]

end Uniformity.Density.Tower

/-! ## Axiom footprint — the two utilities are Lean-core; the four exact-power
declarations carry the DECLARED gate-(b) cite `fgmn_dv_exact_mul` by design -/

section AxCheck

#print axioms Uniformity.Density.Tower.exists_dvHgt_pin
#print axioms Uniformity.Density.Tower.dvResPoly_eq_of_eq
#print axioms Uniformity.Density.Tower.fgmn_dv_exact_pow
#print axioms Uniformity.Density.Tower.isDvPure_pow
#print axioms Uniformity.Density.Tower.dvResPoly_pow_exact
#print axioms Uniformity.Density.Tower.composedKey_pow_mem_towerLocus

end AxCheck
