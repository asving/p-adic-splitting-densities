/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh3
import Uniformity.ChapC.C133mh10
import Uniformity.ChapC.C35

/-!
# Uniformity.ChapC.C133mh11 — `[MH11 2026-08-28]`: Theorem B, dv one-slope split uniqueness

**Node MH.11 = plan row F1.H2** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §2 "Theorem B
(uniqueness — F1.H2, completeness-free, Newton-free)"; proof plan §5, unblocked by the landed
Theorem M root `C133mh3.m1TwistProductLaw`).

**Mechanism (per the §9 table): M-forced exponent match + degree pigeonhole — NO filtration
induction.**  Same §1 pack, no completeness: `g` monic pure with `D′ ∣ deg g`; two splits
`g = a·b = a'·b'` with `a, a'` monic pure carrying exact residuals `R(a) = r^m`, `R(a') = r^m'`
(`m, m' ≥ 1`) and `b, b'` monic whose residuals are NOT divisible by `r` (∀-pin forms).  Then
`a' = a` and `b' = b`.  NOT assumed (all derived): purity of `b, b'`, degrees of `a', b'`, any
relation between `m` and `m'`.

* **(B2, exponent match)** Theorem M clause 3 (`C133mh3.dvResPoly_mul_gen`, τ = 1) on both
  splits: `R(g) = r^m·R(b) = r^{m'}·R(b')` with `r ∤ R(b)`, `r ∤ R(b')`; the landed residual
  Bézout uniqueness (`C133mh10.dvResidualBezout_unique`) forces `m' = m` (and `R(b') = R(b)`).
* **(B1, defect-vanishing)** M clause 2 (`dvSideMax_mul`) + the landed C.35 caps
  (`dvSideMax_eq_of_isDvPure` on the pure factor, `le_natDegree_div_of_mem_dvSideSet` on the
  cofactor) + `D′ ∣ deg g` force `D′·(deg x/D′) = deg x` for the pure factor of EITHER split —
  the summed-slack pigeonhole `P ≤ A → Q ≤ B → P + Q = A + B → P = A` seals both leaks at once.
  With the pure degree law (`natDegree_div_eq_of_isDvPure`) and the C.26 degree law
  (`natDegree_dvResPoly` + `Monic.natDegree_pow`): `deg a = D′·ℓ·m·d_r = deg a'`.
* **(B3, pigeonhole)** If `a' ≠ a`: `δ := a' − a ≠ 0`, `ε := b − b' ≠ 0`, and `a·ε = δ·b'`.
  M clause 3 on this single polynomial: `r^m·R(ε) = R(δ)·R(b')`; `r ∤ R(b')` and coprimality
  (`Irreducible.coprime_iff_not_dvd`, as in C133mh10) give `r^m ∣ R(δ)`, so
  `m·d_r ≤ deg R(δ) = sideDeg(δ)`.  But `D′·ℓ·sideDeg(δ) ≤ D′·sideMax(δ) ≤ deg δ < deg a
  = D′·ℓ·m·d_r` (equal-degree monics cancel at the top), so `sideDeg(δ) < m·d_r` — absurd.

## Statement-fence resolutions (recorded per the charge)

* The "§1 pack" is carried as `L : LevelDatum F H₀ hpin` (C.09) plus `hπ : Irreducible π` and
  `hh : 0 < F.h`; `L.hκ` IS the doc's strict floor `ℓ·(D′·F.h) < u` up to `mul_assoc` (§1).
* The `∀`-pin complement form for `b, b'` is byte-parallel to the signed C.34 complement clause
  (the conclusion shape of `block_pair_self_of_dvResPoly_eq_pow`):
  `∀ hne M₀ hp, ¬ L.r ∣ dvResPoly F H₀ hpin b L.u L.ℓ hne M₀ hp`.
* The exact residuals for `a, a'` are in the `HasLabel` ∃-pin shape (C.29) with the exponent
  explicit: `∃ hne M₀ hp, dvResPoly F H₀ hpin a L.u L.ℓ hne M₀ hp = L.r ^ m` — by C.25's
  junk-total design any other pin witness reads the same residual (`dvResPoly_pin_congr` below),
  so ∃-pin and ∀-pin are equivalent here; the ∃-form matches the signed `HasLabel`.
* `g.Monic` is NOT a hypothesis (derivable from `hab`, `ha`, `hb`); `hgpure`/`hgd` are the §2
  hypotheses on `g`.  `hm : 0 < m`, `hm' : 0 < m'` are §2's fences, carried verbatim (the
  degree pigeonhole happens to close without them; they are kept for statement fidelity).

## Status

Sorry-free; footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh11

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — D9 plumbing (private; re-declared per the standing convention at
C.04/C.12/C.26/C.47/C133mh3) -/

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

/-! ## Part 1 — pin plumbing (private) -/

/-- Every nonzero polynomial admits a full side pin: nonempty side set and a finite
`ℕ`-valued height at the side minimum (C.34's `dvSideSet_nonempty` + `DvOnSide`'s
finiteness conjunct at `Finset.min'_mem`). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} (hf : f ≠ 0)
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ (hne : (dvSideSet F f u ℓ).Nonempty) (M : ℕ),
      dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  have hne := dvSideSet_nonempty F hf u hℓ
  have hmem : dvSideMin F f u ℓ hne ∈ dvSideSet F f u ℓ := Finset.min'_mem _ _
  have hfin : dvHgt F f (dvSideMin F f u ℓ hne) ≠ ⊤ := (dvOnSide_of_mem_dvSideSet hmem).2
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hfin
  exact ⟨hne, M, hM.symm⟩

/-- C.25's junk-total pin irrelevance, across a polynomial equality: `dvResPoly` reads the
same value at ANY two pins of equal polynomials (the numeral is forced by `ENat.coe` injectivity,
the proofs by proof irrelevance). -/
private theorem dvResPoly_pin_congr {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {u ℓ : ℕ} {f f' : Polynomial O} (hff : f = f')
    {hne : (dvSideSet F f u ℓ).Nonempty} {hne' : (dvSideSet F f' u ℓ).Nonempty}
    {M M' : ℕ} (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞))
    (hp' : dvHgt F f' (dvSideMin F f' u ℓ hne') = (M' : ℕ∞)) :
    dvResPoly F H₀ hpin f u ℓ hne M hp = dvResPoly F H₀ hpin f' u ℓ hne' M' hp' := by
  subst hff
  have hMM : M = M' := by
    have h := hp.symm.trans hp'
    exact_mod_cast h
  subst hMM
  rfl

/-! ## Part 2 — (B1) defect-vanishing (private) -/

/-- The summed-slack pigeonhole: two lower slacks whose sum is tight are both tight. -/
private theorem linear_pigeon {P Q A B : ℕ} (h3 : P ≤ A) (h4 : Q ≤ B)
    (hsum : P + Q = A + B) : P = A := by omega

/-- **(B1) — the competitor's degree is pinned.**  In a monic split `x·y` of a `D′`-divisible-
degree pure product, purity of `x` forces `D′·(deg x/D′) = deg x` (i.e. `D′ ∣ deg x`):
`dvSideMax` additivity (M clause 2) + the C.35 caps + the summed-slack pigeonhole. -/
private theorem mul_sideMax_degree_pin (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {x y : Polynomial O} (hx : x.Monic) (hy : y.Monic)
    (hxpure : IsDvPure F x u ℓ) (hxypure : IsDvPure F (x * y) u ℓ)
    (hdvd : (F.e₁ * F.f₁) ∣ (x * y).natDegree) :
    (F.e₁ * F.f₁) * (x.natDegree / (F.e₁ * F.f₁)) = x.natDegree := by
  have hxne := dvSideSet_nonempty F hx.ne_zero u hℓ
  have hyne := dvSideSet_nonempty F hy.ne_zero u hℓ
  have hxyne := dvSideSet_nonempty F (hx.mul hy).ne_zero u hℓ
  have hadd := C133mh3.dvSideMax_mul hπ hh H₀ hpin hℓ hcop hfloor
    hx.ne_zero hy.ne_zero hxne hyne hxyne
  have hxy_eq : dvSideMax F (x * y) u ℓ hxyne = (x * y).natDegree / (F.e₁ * F.f₁) :=
    dvSideMax_eq_of_isDvPure hxypure hxyne
  have hx_eq : dvSideMax F x u ℓ hxne = x.natDegree / (F.e₁ * F.f₁) :=
    dvSideMax_eq_of_isDvPure hxpure hxne
  have hy_le : dvSideMax F y u ℓ hyne ≤ y.natDegree / (F.e₁ * F.f₁) :=
    le_natDegree_div_of_mem_dvSideSet F (Finset.max'_mem _ _)
  have hdegadd : (x * y).natDegree = x.natDegree + y.natDegree := hx.natDegree_mul hy
  have hexact : (F.e₁ * F.f₁) * ((x * y).natDegree / (F.e₁ * F.f₁)) = (x * y).natDegree :=
    Nat.mul_div_cancel' hdvd
  have h3 : (F.e₁ * F.f₁) * (x.natDegree / (F.e₁ * F.f₁)) ≤ x.natDegree := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have h4 : (F.e₁ * F.f₁) * dvSideMax F y u ℓ hyne ≤ y.natDegree :=
    calc (F.e₁ * F.f₁) * dvSideMax F y u ℓ hyne
        ≤ (F.e₁ * F.f₁) * (y.natDegree / (F.e₁ * F.f₁)) := Nat.mul_le_mul le_rfl hy_le
      _ ≤ y.natDegree := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hsum : (F.e₁ * F.f₁) * (x.natDegree / (F.e₁ * F.f₁))
      + (F.e₁ * F.f₁) * dvSideMax F y u ℓ hyne = x.natDegree + y.natDegree := by
    rw [← Nat.mul_add, ← hx_eq, ← hadd, hxy_eq, hexact, hdegadd]
  exact linear_pigeon h3 h4 hsum

/-- The exact degree of a pure factor with exact residual `r^m` and pinned degree:
`deg x = D′·(ℓ·(m·d_r))` — the pure degree law (C.35) composed with the C.26 degree law. -/
private theorem natDegree_of_pure_pow {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {x : Polynomial O} (hxpure : IsDvPure F x L.u L.ℓ)
    {hne : (dvSideSet F x L.u L.ℓ).Nonempty} {M : ℕ}
    (hp : dvHgt F x (dvSideMin F x L.u L.ℓ hne) = (M : ℕ∞)) {m : ℕ}
    (hres : dvResPoly F H₀ hpin x L.u L.ℓ hne M hp = L.r ^ m)
    (hpinned : (F.e₁ * F.f₁) * (x.natDegree / (F.e₁ * F.f₁)) = x.natDegree) :
    x.natDegree = (F.e₁ * F.f₁) * (L.ℓ * (m * L.r.natDegree)) := by
  have hdiv : x.natDegree / (F.e₁ * F.f₁) = L.ℓ * dvSideDeg F x L.u L.ℓ hne :=
    natDegree_div_eq_of_isDvPure L.hℓ L.hcop hxpure hne
  have hdeg := (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne hp).1
  rw [hres, L.hrmonic.natDegree_pow] at hdeg
  calc x.natDegree = (F.e₁ * F.f₁) * (x.natDegree / (F.e₁ * F.f₁)) := hpinned.symm
    _ = (F.e₁ * F.f₁) * (L.ℓ * dvSideDeg F x L.u L.ℓ hne) := by rw [hdiv]
    _ = (F.e₁ * F.f₁) * (L.ℓ * (m * L.r.natDegree)) := by rw [← hdeg]

/-! ## Part 3 — ★ Theorem B -/

set_option linter.unusedVariables false in
/-- ★ **Theorem B (uniqueness — F1.H2, node MH.11): `dv_oneSlope_split_unique`.**
Completeness-free, Newton-free.  §1 pack (`L`, `hπ`, `hh`); `g` monic pure with `D′ ∣ deg g`;
`g = a·b = a'·b'` with `a, a'` monic pure with exact residuals `R(a) = r^m`, `R(a') = r^{m'}`
(`m, m' ≥ 1`, ∃-pin forms), `b, b'` monic with residuals not divisible by `r` (∀-pin forms).
Then `a' = a` and `b' = b`.  Purity of `b, b'`, the degrees of `a', b'`, and `m' = m` are
all DERIVED, not assumed. -/
theorem dv_oneSlope_split_unique {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {g a b a' b' : Polynomial O}
    (hgpure : IsDvPure F g L.u L.ℓ) (hgd : (F.e₁ * F.f₁) ∣ g.natDegree)
    (hab : g = a * b) (hab' : g = a' * b')
    (ha : a.Monic) (hb : b.Monic) (ha' : a'.Monic) (hb' : b'.Monic)
    (hapure : IsDvPure F a L.u L.ℓ) (ha'pure : IsDvPure F a' L.u L.ℓ)
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hares : ∃ (hne : (dvSideSet F a L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F a (dvSideMin F a L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin a L.u L.ℓ hne M₀ hp = L.r ^ m)
    (ha'res : ∃ (hne : (dvSideSet F a' L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F a' (dvSideMin F a' L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin a' L.u L.ℓ hne M₀ hp = L.r ^ m')
    (hbres : ∀ (hne : (dvSideSet F b L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F b (dvSideMin F b L.u L.ℓ hne) = (M₀ : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b L.u L.ℓ hne M₀ hp)
    (hb'res : ∀ (hne : (dvSideSet F b' L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F b' (dvSideMin F b' L.u L.ℓ hne) = (M₀ : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b' L.u L.ℓ hne M₀ hp) :
    a' = a ∧ b' = b := by
  obtain ⟨hne_a, M_a, hp_a, hres_a⟩ := hares
  obtain ⟨hne_a', M_a', hp_a', hres_a'⟩ := ha'res
  subst hab
  -- hab' : a * b = a' * b'
  have hfloor : L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
    rw [← mul_assoc]; exact L.hκ
  obtain ⟨hne_b, M_b, hp_b⟩ := exists_pin F hb.ne_zero L.u L.hℓ
  obtain ⟨hne_b', M_b', hp_b'⟩ := exists_pin F hb'.ne_zero L.u L.hℓ
  obtain ⟨hne_g, M_g, hp_g⟩ := exists_pin F (ha.mul hb).ne_zero L.u L.hℓ
  obtain ⟨hne_g', M_g', hp_g'⟩ := exists_pin F (ha'.mul hb').ne_zero L.u L.hℓ
  -- (B2) Theorem M clause 3 on both splits, matched through the shared product
  have hM1 := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop hfloor
    ha.ne_zero hb.ne_zero hne_a hne_b hne_g hp_a hp_b hp_g
  have hM2 := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop hfloor
    ha'.ne_zero hb'.ne_zero hne_a' hne_b' hne_g' hp_a' hp_b' hp_g'
  have hkey : L.r ^ m * dvResPoly F H₀ hpin b L.u L.ℓ hne_b M_b hp_b
      = L.r ^ m' * dvResPoly F H₀ hpin b' L.u L.ℓ hne_b' M_b' hp_b' := by
    rw [← hres_a, ← hres_a', ← hM1, ← hM2]
    exact dvResPoly_pin_congr hab' hp_g hp_g'
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  obtain ⟨hmm, -⟩ := C133mh10.dvResidualBezout_unique
    (R := L.r ^ m * dvResPoly F H₀ hpin b L.u L.ℓ hne_b M_b hp_b)
    L.hrmonic L.hrdeg rfl (hbres hne_b M_b hp_b) hkey (hb'res hne_b' M_b' hp_b')
  -- (B1) both pure factors get their degrees pinned to D′·ℓ·(exponent·d_r)
  have hpin_a : (F.e₁ * F.f₁) * (a.natDegree / (F.e₁ * F.f₁)) = a.natDegree :=
    mul_sideMax_degree_pin hπ hh H₀ hpin L.hℓ L.hcop hfloor ha hb hapure hgpure hgd
  have hg'pure : IsDvPure F (a' * b') L.u L.ℓ := by rw [← hab']; exact hgpure
  have hg'd : (F.e₁ * F.f₁) ∣ (a' * b').natDegree := by rw [← hab']; exact hgd
  have hpin_a' : (F.e₁ * F.f₁) * (a'.natDegree / (F.e₁ * F.f₁)) = a'.natDegree :=
    mul_sideMax_degree_pin hπ hh H₀ hpin L.hℓ L.hcop hfloor ha' hb' ha'pure hg'pure hg'd
  have hdeg_a : a.natDegree = (F.e₁ * F.f₁) * (L.ℓ * (m * L.r.natDegree)) :=
    natDegree_of_pure_pow L hπ hapure hp_a hres_a hpin_a
  have hdeg_a' : a'.natDegree = (F.e₁ * F.f₁) * (L.ℓ * (m' * L.r.natDegree)) :=
    natDegree_of_pure_pow L hπ ha'pure hp_a' hres_a' hpin_a'
  have hdeg_eq : a'.natDegree = a.natDegree := by rw [hdeg_a', hdeg_a, hmm]
  -- (B3) the degree pigeonhole on δ = a' − a
  have ha'a : a' = a := by
    by_contra hne0
    have hδne : a' - a ≠ 0 := sub_ne_zero.mpr hne0
    have hεne : b - b' ≠ 0 := by
      intro h0
      apply hne0
      have hbb : b = b' := sub_eq_zero.mp h0
      have h := hab'
      rw [hbb] at h
      exact (mul_right_cancel₀ hb'.ne_zero h).symm
    have hprod : a * (b - b') = (a' - a) * b' := by
      rw [mul_sub, sub_mul, hab']
    obtain ⟨hne_ε, M_ε, hp_ε⟩ := exists_pin F hεne L.u L.hℓ
    obtain ⟨hne_δ, M_δ, hp_δ⟩ := exists_pin F hδne L.u L.hℓ
    obtain ⟨hne_p, M_p, hp_p⟩ := exists_pin F (mul_ne_zero ha.ne_zero hεne) L.u L.hℓ
    obtain ⟨hne_q, M_q, hp_q⟩ := exists_pin F (mul_ne_zero hδne hb'.ne_zero) L.u L.hℓ
    have hM3 := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop hfloor
      ha.ne_zero hεne hne_a hne_ε hne_p hp_a hp_ε hp_p
    have hM4 := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop hfloor
      hδne hb'.ne_zero hne_δ hne_b' hne_q hp_δ hp_b' hp_q
    have hkey2 : L.r ^ m * dvResPoly F H₀ hpin (b - b') L.u L.ℓ hne_ε M_ε hp_ε
        = dvResPoly F H₀ hpin (a' - a) L.u L.ℓ hne_δ M_δ hp_δ
          * dvResPoly F H₀ hpin b' L.u L.ℓ hne_b' M_b' hp_b' := by
      rw [← hres_a, ← hM3, ← hM4]
      exact dvResPoly_pin_congr hprod hp_p hp_q
    have hcop2 : IsCoprime (L.r ^ m) (dvResPoly F H₀ hpin b' L.u L.ℓ hne_b' M_b' hp_b') :=
      (L.hrirr.coprime_iff_not_dvd.mpr (hb'res hne_b' M_b' hp_b')).pow_left
    have hdvdδ : L.r ^ m ∣ dvResPoly F H₀ hpin (a' - a) L.u L.ℓ hne_δ M_δ hp_δ :=
      hcop2.dvd_of_dvd_mul_right ⟨_, hkey2.symm⟩
    have hRδspec := natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne_δ hp_δ
    have hRδne : dvResPoly F H₀ hpin (a' - a) L.u L.ℓ hne_δ M_δ hp_δ ≠ 0 := by
      intro h0
      exact hRδspec.2 (by rw [h0]; simp)
    -- the lower bound: m·d_r ≤ sideDeg(δ)
    have hlow : m * L.r.natDegree ≤ dvSideDeg F (a' - a) L.u L.ℓ hne_δ := by
      have hd := Polynomial.natDegree_le_of_dvd hdvdδ hRδne
      rwa [L.hrmonic.natDegree_pow, hRδspec.1] at hd
    -- the upper bound chain: D′·ℓ·sideDeg(δ) ≤ deg δ < deg a = D′·ℓ·m·d_r
    have hcap : dvSideMax F (a' - a) L.u L.ℓ hne_δ ≤ (a' - a).natDegree / (F.e₁ * F.f₁) :=
      le_natDegree_div_of_mem_dvSideSet F (Finset.max'_mem _ _)
    have hlen' : L.ℓ * dvSideDeg F (a' - a) L.u L.ℓ hne_δ
        ≤ dvSideMax F (a' - a) L.u L.ℓ hne_δ := by
      have h : dvSideMax F (a' - a) L.u L.ℓ hne_δ - dvSideMin F (a' - a) L.u L.ℓ hne_δ
          = L.ℓ * dvSideDeg F (a' - a) L.u L.ℓ hne_δ := dvSideLen_eq F L.hℓ L.hcop hne_δ
      omega
    have hdeq : a'.degree = a.degree := by
      rw [Polynomial.degree_eq_natDegree ha'.ne_zero,
        Polynomial.degree_eq_natDegree ha.ne_zero, hdeg_eq]
    have hdlt : (a' - a).degree < a.degree := by
      have h := Polynomial.degree_sub_lt hdeq ha'.ne_zero
        (by rw [ha'.leadingCoeff, ha.leadingCoeff])
      rwa [hdeq] at h
    have hdnat : (a' - a).natDegree < a.natDegree :=
      Polynomial.natDegree_lt_natDegree hδne hdlt
    have hchain : (F.e₁ * F.f₁) * (L.ℓ * dvSideDeg F (a' - a) L.u L.ℓ hne_δ)
        < (F.e₁ * F.f₁) * (L.ℓ * (m * L.r.natDegree)) := by
      calc (F.e₁ * F.f₁) * (L.ℓ * dvSideDeg F (a' - a) L.u L.ℓ hne_δ)
          ≤ (F.e₁ * F.f₁) * dvSideMax F (a' - a) L.u L.ℓ hne_δ :=
            Nat.mul_le_mul le_rfl hlen'
        _ ≤ (F.e₁ * F.f₁) * ((a' - a).natDegree / (F.e₁ * F.f₁)) :=
            Nat.mul_le_mul le_rfl hcap
        _ ≤ (a' - a).natDegree := by
            rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
        _ < a.natDegree := hdnat
        _ = (F.e₁ * F.f₁) * (L.ℓ * (m * L.r.natDegree)) := hdeg_a
    have h1 : L.ℓ * dvSideDeg F (a' - a) L.u L.ℓ hne_δ < L.ℓ * (m * L.r.natDegree) :=
      Nat.lt_of_mul_lt_mul_left hchain
    have h2 : dvSideDeg F (a' - a) L.u L.ℓ hne_δ < m * L.r.natDegree :=
      Nat.lt_of_mul_lt_mul_left h1
    omega
  refine ⟨ha'a, ?_⟩
  have h := hab'
  rw [ha'a] at h
  exact (mul_left_cancel₀ ha.ne_zero h).symm

end Uniformity.Density.Tower.C133mh11

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh11.dv_oneSlope_split_unique

end AxCheck
