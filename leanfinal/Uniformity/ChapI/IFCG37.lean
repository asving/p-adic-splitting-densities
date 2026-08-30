/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapB.B35c
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B41b
import Uniformity.ChapB.B59a
import Uniformity.ChapI.IFCG34
import Uniformity.ChapI.IFCG35

/-!
# Uniformity.ChapI.IFCG37 — UNIT RIS: `ResidualInertiaSupply` DISCHARGED

**The one open leaf leg closed.** IFCG35 reduced the residual-irreducible leaf law at
every `(e', d)` to the single named Prop `ResidualInertiaSupply` (B-BOX-1 at the
x-frame): a monic x-pure block with IRREDUCIBLE side residual `ψ` of degree `d` has
`d ∣ inertiaDegOf g'` for every monic factor `g'`.  This file PROVES it, Lean-core +
the previously landed cites only, via IFCG32's norm-descent machinery at the unramified
extension `O' := AdjoinRoot ψ̃` (`ψ̃` a monic key lift of `ψ`):

1. **Step I** (`irreducible_of_pure_of_resPoly_irreducible`): a monic pure block with
   irreducible side residual is itself IRREDUCIBLE — any monic split makes
   `resPoly_mul_of_pure` (B.35c) split the irreducible residual.  So
   `monicFactors g = {g}` and the target is `d ∣ inertiaDegOf g`.
2. **Step II** (the transport): the whole x-frame polygon/residual apparatus
   (`dev`/`gaussVal`/`npHgt`/`suppVal`/`OnSide`/`sideSet`/`sideDeg`/`IsPure` and the
   digit polynomial) transports along ANY ring map `h` with `Irreducible (h π)` —
   instantiated at `h = algebraMap O O'` (with `resEmb`) and `h = tau β` (with
   `resTau`).
3. **Step III**: over `O'` the residual splits, `R.map ε = ∏_{β ∈ keyRoots}(X − C β)`
   (IFCG29's full-splitting `card_keyRoots`/`nodup_keyRoots`).
4. **Step IV**: B.63's pinned dissection (private there; re-derived here) factors
   `g.map A = ∏_β G_β` along the split residual; each `G_β` has LINEAR residual, hence
   is irreducible by Step I again; `C.map (tau β)` (`C := G_{β₀}`) is a monic
   irreducible factor with residual `X − C β`, so UFD-matching pins
   `C.map (tau β) = G_β` and `tauProd hψ̃ C = g.map A` — IFCG32's `hGmap`.
5. **Step V**: `normValues_descent` + `dvd_inertiaDegOf_of_mem_normDivisors` give
   `d ∣ inertiaDegOf g`.

Wiring: `residualInertiaSupply` (THE supply), the leaf laws `ResidualLeafLaw e' d` for
ALL `e' > 0, d > 0` unconditionally, and ER4's `E1IrrLeafDecision` (the `(2,2)`
instance) with its type22/type41 census rows.

Axiom budget: Lean core + (through IFCG35's spanning machinery only) the owner-signed
B.42 cite.  The core supply theorem itself must be LEAN-CORE.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG37

open IsLocalRing Polynomial
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG27
open Uniformity.Density.IFCG29
open Uniformity.Density.IFCG32 (addVal_map_of_irreducible normValues_descent
  dvd_inertiaDegOf_of_mem_normDivisors)

attribute [local instance] Classical.propDecidable

/-! ## §0 — supply: the x-frame kit -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The canonical key `X` (private copy of the B83Kit/IFCG35 idiom). -/
theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

private theorem mem_sideSet_iff' {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact this

private theorem min'_congr' {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

private theorem max'_congr' {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst h; rfl

/-- `resPoly` respects equality of the polynomial (the `Nonempty` argument is a proof). -/
private theorem resPoly_congr (π : O) (φ : Polynomial O) {p q : Polynomial O} (hpq : p = q)
    {u ℓ H₀ : ℕ} (hnep : (sideSet φ p u ℓ).Nonempty) (hneq : (sideSet φ q u ℓ).Nonempty) :
    resPoly π φ p u ℓ hnep H₀ = resPoly π φ q u ℓ hneq H₀ := by
  subst hpq; rfl

end Kit

/-! ## §1 — the x-frame digit polynomial: `resPoly` over the residue field -/

section XRes

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The x-frame digit polynomial**: the side residual read over `ResidueField O`
itself (rather than `resField X`).  `resPoly π X g u ℓ hne H₀` is its image under
B.59a's identification `resFieldXEquiv` — `resPoly_x_frame` below. -/
def xres (π : O) (g : Polynomial O) (u ℓ : ℕ) (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty)
    (H₀ : ℕ) : Polynomial (IsLocalRing.ResidueField O) :=
  ∑ k ∈ Finset.range (sideDeg (X : Polynomial O) g u ℓ hne + 1),
    Polynomial.C (digAt π (H₀ - u * k)
      (g.coeff (sideMin (X : Polynomial O) g u ℓ hne + ℓ * k)))
      * Polynomial.X ^ k

/-- The residual coefficient at the key `X` is the digit of the coefficient, pushed
along `resFieldXEquiv` (B.15's `dev_X` + B.59a's `digPoly_C`). -/
theorem resCoeff_x_frame (π : O) (g : Polynomial O) (u ℓ : ℕ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) (H₀ k : ℕ) :
    resCoeff π (X : Polynomial O) g u ℓ hne H₀ k
      = resFieldXEquiv O
          (digAt π (H₀ - u * k) (g.coeff (sideMin (X : Polynomial O) g u ℓ hne + ℓ * k))) := by
  rw [resCoeff, dev_X, resMk, digPoly_C, AdjoinRoot.mk_C]
  rfl

/-- **The x-frame normal form of the residual**: `resPoly = (xres).map resFieldXEquiv`. -/
theorem resPoly_x_frame (π : O) (g : Polynomial O) (u ℓ : ℕ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) (H₀ : ℕ) :
    resPoly π (X : Polynomial O) g u ℓ hne H₀
      = (xres π g u ℓ hne H₀).map
          (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O)) := by
  rw [resPoly]
  unfold xres
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    RingEquiv.coe_toRingHom]
  rw [resCoeff_x_frame]

/-- Irreducibility of the x-frame residual reads off the digit polynomial. -/
theorem irreducible_resPoly_x_iff {π : O} {g : Polynomial O} {u ℓ : ℕ}
    {hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty} {H₀ : ℕ} :
    Irreducible (resPoly π (X : Polynomial O) g u ℓ hne H₀)
      ↔ Irreducible (xres π g u ℓ hne H₀) := by
  rw [resPoly_x_frame]
  have hmap : (xres π g u ℓ hne H₀).map
        (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O))
      = Polynomial.mapEquiv (resFieldXEquiv O) (xres π g u ℓ hne H₀) := rfl
  rw [hmap]
  exact MulEquiv.irreducible_iff (Polynomial.mapEquiv (resFieldXEquiv O))

/-- `xres` has the side degree and, at a pure block, is monic. -/
theorem xres_natDegree_monic {π : O} (hπ : Irreducible π) {u ℓ : ℕ} (_hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt (X : Polynomial O) g (sideMin (X : Polynomial O) g u ℓ hne) = (H₀ : ℕ∞)) :
    (xres π g u ℓ hne H₀).natDegree = sideDeg (X : Polynomial O) g u ℓ hne
      ∧ (xres π g u ℓ hne H₀).Monic := by
  have hinj : Function.Injective
      (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O)) :=
    (resFieldXEquiv O).injective
  have hX1 : (X : Polynomial O).natDegree = 1 := Polynomial.natDegree_X
  have hdeg0 : g.natDegree
      = (g.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
    rw [hX1]; simp
  have htf : suppVal (X : Polynomial O) g u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hpure]; exact ENat.coe_ne_top _
  have hRdeg : (resPoly π (X : Polynomial O) g u ℓ hne H₀).natDegree
      = sideDeg (X : Polynomial O) g u ℓ hne :=
    (natDegree_resPoly hπ isKey_X hℓ hcop htf hne hH).1
  have hxdeg : (xres π g u ℓ hne H₀).natDegree = sideDeg (X : Polynomial O) g u ℓ hne := by
    rw [← hRdeg, resPoly_x_frame, Polynomial.natDegree_map_eq_of_injective hinj]
  refine ⟨hxdeg, ?_⟩
  -- the residual polynomial of the pure block is monic (B.63's derivation)
  have hmin : sideMin (X : Polynomial O) g u ℓ hne = 0 := sideMin_of_pure hpure hne
  have hdl : ℓ * sideDeg (X : Polynomial O) g u ℓ hne
      = g.natDegree / (X : Polynomial O).natDegree :=
    sideDeg_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hℓ hcop hpure hne
  have hdl' : ℓ * sideDeg (X : Polynomial O) g u ℓ hne = g.natDegree := by
    rw [hX1, Nat.div_one] at hdl; exact hdl
  have hgdegd : g.natDegree
      = ℓ * sideDeg (X : Polynomial O) g u ℓ hne * (X : Polynomial O).natDegree := by
    rw [hX1, Nat.mul_one, hdl']
  rw [hmin] at hH
  have hHd : H₀ = u * sideDeg (X : Polynomial O) g u ℓ hne :=
    height_eq_of_pure isKey_X.monic isKey_X.pos hg hgdegd hℓ hcop hpure hne hH
  have hRmonic : (resPoly π (X : Polynomial O) g u ℓ hne H₀).Monic := by
    show (resPoly π (X : Polynomial O) g u ℓ hne H₀).coeff
      (resPoly π (X : Polynomial O) g u ℓ hne H₀).natDegree = 1
    rw [hRdeg, resPoly_coeff_of_pure hπ isKey_X.monic isKey_X.pos hg hgdegd hℓ hcop hpure hne
      H₀ (sideDeg (X : Polynomial O) g u ℓ hne), hHd, Nat.sub_self,
      dev_top isKey_X.monic isKey_X.pos hg
        (μ := ℓ * sideDeg (X : Polynomial O) g u ℓ hne) hgdegd,
      resMk_one hπ]
  have hlc := Polynomial.leadingCoeff_map_of_injective hinj (xres π g u ℓ hne H₀)
  have h1 : (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O))
      ((xres π g u ℓ hne H₀).leadingCoeff) = 1 := by
    rw [← hlc, ← resPoly_x_frame]
    exact hRmonic
  exact hinj (h1.trans (map_one
    (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O))).symm)

end XRes

/-! ## §2 — THE TRANSPORT: the x-frame polygon along a `π`-faithful ring map -/

section Transport

variable {O₁ : Type*} [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁]
variable {O₂ : Type*} [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂]
variable {h : O₁ →+* O₂} {π : O₁}

/-- A ring map carrying one irreducible to an irreducible is injective. -/
theorem injective_of_irreducible_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) :
    Function.Injective h := by
  intro a b hab
  by_contra hnab
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hnab
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hab0 hπ
  have hz : h (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [hw, map_mul, map_pow] at hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact (w.isUnit.map h).ne_zero h1
  · exact pow_ne_zero n hπ₂.ne_zero h2

/-- `npHgt` at `X` transports: the polygon heights are coefficient valuations, and the
valuation is preserved (B.15's `npHgt_X` + IFCG32's `addVal_map_of_irreducible`). -/
theorem npHgt_X_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) (f : Polynomial O₁) (j : ℕ) :
    npHgt (X : Polynomial O₂) (f.map h) j = npHgt (X : Polynomial O₁) f j := by
  rw [npHgt_X, npHgt_X, Polynomial.coeff_map]
  exact addVal_map_of_irreducible h hπ hπ₂ _

/-- `suppVal` at `X` transports (monic `f` pins the degree range). -/
theorem suppVal_X_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) {f : Polynomial O₁}
    (hf : f.Monic) (u ℓ : ℕ) :
    suppVal (X : Polynomial O₂) (f.map h) u ℓ = suppVal (X : Polynomial O₁) f u ℓ := by
  unfold suppVal
  rw [hf.natDegree_map h]
  exact Finset.inf_congr rfl fun j _ => by rw [npHgt_X_map hπ hπ₂]

/-- `OnSide` at `X` transports. -/
theorem onSide_X_map_iff (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) {f : Polynomial O₁}
    (hf : f.Monic) (u ℓ j : ℕ) :
    OnSide (X : Polynomial O₂) (f.map h) u ℓ j ↔ OnSide (X : Polynomial O₁) f u ℓ j := by
  simp only [OnSide, npHgt_X_map hπ hπ₂, suppVal_X_map hπ hπ₂ hf]

/-- `sideSet` at `X` transports — an equality of `Finset ℕ`. -/
theorem sideSet_X_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) {f : Polynomial O₁}
    (hf : f.Monic) (u ℓ : ℕ) :
    sideSet (X : Polynomial O₂) (f.map h) u ℓ = sideSet (X : Polynomial O₁) f u ℓ := by
  ext j
  rw [mem_sideSet_iff', mem_sideSet_iff', hf.natDegree_map h]
  exact and_congr_right fun _ => onSide_X_map_iff hπ hπ₂ hf u ℓ j

/-- `sideMin`/`sideMax`/`sideDeg` transport. -/
theorem sideData_X_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) {f : Polynomial O₁}
    (hf : f.Monic) (u ℓ : ℕ) (hne₁ : (sideSet (X : Polynomial O₁) f u ℓ).Nonempty)
    (hne₂ : (sideSet (X : Polynomial O₂) (f.map h) u ℓ).Nonempty) :
    sideMin (X : Polynomial O₂) (f.map h) u ℓ hne₂ = sideMin (X : Polynomial O₁) f u ℓ hne₁
      ∧ sideMax (X : Polynomial O₂) (f.map h) u ℓ hne₂ = sideMax (X : Polynomial O₁) f u ℓ hne₁
      ∧ sideDeg (X : Polynomial O₂) (f.map h) u ℓ hne₂ = sideDeg (X : Polynomial O₁) f u ℓ hne₁ := by
  have hset := sideSet_X_map hπ hπ₂ hf u ℓ
  have hmin : sideMin (X : Polynomial O₂) (f.map h) u ℓ hne₂
      = sideMin (X : Polynomial O₁) f u ℓ hne₁ := min'_congr' hset _ _
  have hmax : sideMax (X : Polynomial O₂) (f.map h) u ℓ hne₂
      = sideMax (X : Polynomial O₁) f u ℓ hne₁ := max'_congr' hset _ _
  exact ⟨hmin, hmax, by unfold sideDeg; rw [hmin, hmax]⟩

/-- `IsPure` at `X` transports. -/
theorem isPure_X_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) {f : Polynomial O₁}
    (hf : f.Monic) {u ℓ : ℕ} (hpure : IsPure (X : Polynomial O₁) f u ℓ) :
    IsPure (X : Polynomial O₂) (f.map h) u ℓ := by
  obtain ⟨h0, h1⟩ := hpure
  refine ⟨(onSide_X_map_iff hπ hπ₂ hf u ℓ 0).mpr h0, ?_⟩
  have hq : (f.map h).natDegree / (X : Polynomial O₂).natDegree
      = f.natDegree / (X : Polynomial O₁).natDegree := by
    rw [hf.natDegree_map h, Polynomial.natDegree_X, Polynomial.natDegree_X]
  rw [hq]
  exact (onSide_X_map_iff hπ hπ₂ hf u ℓ _).mpr h1

/-- The `π`-power divisibilities transport (both directions). -/
theorem pow_dvd_map_iff (hπ : Irreducible π) (hπ₂ : Irreducible (h π)) (k : ℕ) (x : O₁) :
    (h π) ^ k ∣ h x ↔ π ^ k ∣ x := by
  constructor
  · intro hd
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
    have hkn : k ≤ n := by
      have hd2 : (h π) ^ k ∣ (h π) ^ n := by
        have hd1 : (h π) ^ k ∣ h ↑w * (h π) ^ n := by
          have hx : h x = h ↑w * (h π) ^ n := by rw [hw, map_mul, map_pow]
          rwa [hx] at hd
        exact (w.isUnit.map h).dvd_mul_left.mp hd1
      exact (pow_dvd_pow_iff hπ₂.ne_zero hπ₂.not_isUnit).mp hd2
    refine dvd_trans (pow_dvd_pow π hkn) ?_
    rw [hw]
    exact Dvd.intro_left _ rfl
  · rintro ⟨y, rfl⟩
    exact ⟨h y, by rw [map_mul, map_pow]⟩

/-- **The digit transports** along the residue-level map (B.22's `digAt_eq`). -/
theorem digAt_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π))
    (ε : IsLocalRing.ResidueField O₁ →+* IsLocalRing.ResidueField O₂)
    (hε : ∀ a : O₁, ε (IsLocalRing.residue O₁ a) = IsLocalRing.residue O₂ (h a))
    (k : ℕ) (x : O₁) :
    digAt (h π) k (h x) = ε (digAt π k x) := by
  by_cases hd : π ^ k ∣ x
  · obtain ⟨y, rfl⟩ := hd
    rw [digAt_eq hπ rfl, digAt_eq hπ₂ (show h (π ^ k * y) = (h π) ^ k * h y by
      rw [map_mul, map_pow]), hε]
  · have hd2 : ¬ (h π) ^ k ∣ h x := fun hcon => hd ((pow_dvd_map_iff hπ hπ₂ k x).mp hcon)
    unfold digAt
    rw [dif_neg hd2, dif_neg hd, map_zero]

/-- **THE TRANSPORT of the x-frame digit polynomial**: `xres` of the pushed block is
the `ε`-image of `xres`. -/
theorem xres_map (hπ : Irreducible π) (hπ₂ : Irreducible (h π))
    (ε : IsLocalRing.ResidueField O₁ →+* IsLocalRing.ResidueField O₂)
    (hε : ∀ a : O₁, ε (IsLocalRing.residue O₁ a) = IsLocalRing.residue O₂ (h a))
    {f : Polynomial O₁} (hf : f.Monic) (u ℓ : ℕ)
    (hne₁ : (sideSet (X : Polynomial O₁) f u ℓ).Nonempty)
    (hne₂ : (sideSet (X : Polynomial O₂) (f.map h) u ℓ).Nonempty) (H₀ : ℕ) :
    xres (h π) (f.map h) u ℓ hne₂ H₀ = (xres π f u ℓ hne₁ H₀).map ε := by
  obtain ⟨hmin, -, hdeg⟩ := sideData_X_map hπ hπ₂ hf u ℓ hne₁ hne₂
  unfold xres
  rw [Polynomial.map_sum, hdeg, hmin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coeff_map, digAt_map hπ hπ₂ ε hε]

end Transport

/-! ## §3 — STEP I: a pure block with irreducible residual is irreducible -/

section Irred

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The side degree of a residual-irreducible block is positive. -/
theorem sideDeg_pos_of_resPoly_irreducible (hπ : Irreducible π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt (X : Polynomial O) g (sideMin (X : Polynomial O) g u ℓ hne) = (H₀ : ℕ∞))
    (hirr : Irreducible (resPoly π (X : Polynomial O) g u ℓ hne H₀)) :
    0 < sideDeg (X : Polynomial O) g u ℓ hne := by
  classical
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  by_contra hd0
  have hd0' : sideDeg (X : Polynomial O) g u ℓ hne = 0 := by omega
  have hdeg0 : g.natDegree
      = (g.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
    rw [Polynomial.natDegree_X]; simp
  have htf : suppVal (X : Polynomial O) g u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hpure]; exact ENat.coe_ne_top _
  obtain ⟨hRdeg, hR0⟩ := natDegree_resPoly hπ isKey_X hℓ hcop htf hne hH
  rw [hd0'] at hRdeg
  have hC : resPoly π (X : Polynomial O) g u ℓ hne H₀
      = Polynomial.C ((resPoly π (X : Polynomial O) g u ℓ hne H₀).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hRdeg
  refine hirr.not_isUnit ?_
  rw [hC]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hR0)

/-- ★ **STEP I — the block itself is irreducible.**  A monic x-pure block whose side
residual is irreducible admits no nontrivial monic split: `resPoly_mul_of_pure` (B.35c)
would split the irreducible residual into two positive-degree monic factors. -/
theorem irreducible_of_pure_of_resPoly_irreducible (hπ : Irreducible π) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt (X : Polynomial O) g (sideMin (X : Polynomial O) g u ℓ hne) = (H₀ : ℕ∞))
    (hirr : Irreducible (resPoly π (X : Polynomial O) g u ℓ hne H₀)) :
    Irreducible g := by
  classical
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hd := sideDeg_pos_of_resPoly_irreducible hπ hℓ hcop hg hpure hne hH hirr
  have hX1 : (X : Polynomial O).natDegree = 1 := Polynomial.natDegree_X
  have hdeg0 : g.natDegree
      = (g.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
    rw [hX1]; simp
  have hdl : ℓ * sideDeg (X : Polynomial O) g u ℓ hne
      = g.natDegree / (X : Polynomial O).natDegree :=
    sideDeg_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hℓ hcop hpure hne
  have hgdeg : g.natDegree = ℓ * sideDeg (X : Polynomial O) g u ℓ hne := by
    rw [hX1, Nat.div_one] at hdl; omega
  have hgdegpos : 0 < g.natDegree := by
    rw [hgdeg]; exact Nat.mul_pos hℓ hd
  constructor
  · intro hunit
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b heq
    by_contra hcon
    obtain ⟨hna, hnb⟩ := not_or.mp hcon
    exfalso
    -- leading coefficients multiply to 1; normalize the split to monic factors
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      have hg' := congrArg Polynomial.leadingCoeff heq
      rw [Polynomial.leadingCoeff_mul] at hg'
      rw [← hg']; exact hg
    set a' := Polynomial.C b.leadingCoeff * a with ha'
    set b' := Polynomial.C a.leadingCoeff * b with hb'
    have ha'm : a'.Monic := by
      show a'.leadingCoeff = 1
      rw [ha', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, mul_comm]
      exact hlc
    have hb'm : b'.Monic := by
      show b'.leadingCoeff = 1
      rw [hb', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact hlc
    have heq' : g = a' * b' := by
      rw [ha', hb']
      calc g = Polynomial.C 1 * g := by rw [map_one, one_mul]
        _ = Polynomial.C (a.leadingCoeff * b.leadingCoeff) * (a * b) := by rw [hlc, ← heq]
        _ = (Polynomial.C b.leadingCoeff * a) * (Polynomial.C a.leadingCoeff * b) := by
            rw [Polynomial.C_mul]; ring
    have hXdvd : (X : Polynomial O).natDegree ∣ g.natDegree := by
      rw [hX1]; exact one_dvd _
    obtain ⟨hne₁, hne₂, hp₁, hp₂, hadd, -⟩ :=
      isPure_of_monic_factor hπ isKey_X hu hℓ hcop hg ha'm hb'm hXdvd heq' hpure hne
    -- height pins on the three pure blocks
    have hda0 : a'.natDegree
        = (a'.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
      rw [hX1]; simp
    have hdb0 : b'.natDegree
        = (b'.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
      rw [hX1]; simp
    have htfa : suppVal (X : Polynomial O) a' u ℓ ≠ ⊤ := by
      rw [suppVal_of_pure isKey_X.monic isKey_X.pos ha'm hda0 hp₁]; exact ENat.coe_ne_top _
    have htfb : suppVal (X : Polynomial O) b' u ℓ ≠ ⊤ := by
      rw [suppVal_of_pure isKey_X.monic isKey_X.pos hb'm hdb0 hp₂]; exact ENat.coe_ne_top _
    have hntopa : npHgt (X : Polynomial O) a' 0 ≠ ⊤ := npHgt_ne_top_of_onSide hℓ htfa hp₁.1
    have hntopb : npHgt (X : Polynomial O) b' 0 ≠ ⊤ := npHgt_ne_top_of_onSide hℓ htfb hp₂.1
    obtain ⟨Ha, hHa⟩ := WithTop.ne_top_iff_exists.mp hntopa
    obtain ⟨Hb, hHb⟩ := WithTop.ne_top_iff_exists.mp hntopb
    have hHad : Ha = u * sideDeg (X : Polynomial O) a' u ℓ hne₁ :=
      height_eq_of_pure isKey_X.monic isKey_X.pos ha'm hda0 hℓ hcop hp₁ hne₁ hHa.symm
    have hHbd : Hb = u * sideDeg (X : Polynomial O) b' u ℓ hne₂ :=
      height_eq_of_pure isKey_X.monic isKey_X.pos hb'm hdb0 hℓ hcop hp₂ hne₂ hHb.symm
    have hmin : sideMin (X : Polynomial O) g u ℓ hne = 0 := sideMin_of_pure hpure hne
    rw [hmin] at hH
    have hH0d : H₀ = u * sideDeg (X : Polynomial O) g u ℓ hne :=
      height_eq_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hℓ hcop hpure hne hH
    have hH0eq : H₀ = Ha + Hb := by rw [hH0d, hHad, hHbd, ← hadd]; ring
    -- residual multiplicativity at the split (B.35c)
    have hXdvda : (X : Polynomial O).natDegree ∣ a'.natDegree := by
      rw [hX1]; exact one_dvd _
    have hXdvdb : (X : Polynomial O).natDegree ∣ b'.natDegree := by
      rw [hX1]; exact one_dvd _
    have hnefg : (sideSet (X : Polynomial O) (a' * b') u ℓ).Nonempty :=
      sideSet_nonempty_gen _ _ _ _
    have hmul : resPoly π (X : Polynomial O) (a' * b') u ℓ hnefg (Ha + Hb)
        = resPoly π (X : Polynomial O) a' u ℓ hne₁ Ha
          * resPoly π (X : Polynomial O) b' u ℓ hne₂ Hb :=
      resPoly_mul_of_pure hπ isKey_X hu hℓ hcop ha'm hb'm hXdvda hXdvdb hp₁ hp₂
        hHa.symm hHb.symm hne₁ hne₂ hnefg
    -- transfer the irreducibility to the product and split it
    rw [hH0eq] at hirr
    have hirr' : Irreducible (resPoly π (X : Polynomial O) (a' * b') u ℓ hnefg (Ha + Hb)) := by
      subst heq'
      exact hirr
    rw [hmul] at hirr'
    rcases hirr'.isUnit_or_isUnit rfl with hua | hub
    · -- a unit residual forces `a' = 1`, so `a` is a unit
      have hdega : (resPoly π (X : Polynomial O) a' u ℓ hne₁ Ha).natDegree
          = sideDeg (X : Polynomial O) a' u ℓ hne₁ :=
        (natDegree_resPoly hπ isKey_X hℓ hcop htfa hne₁
          (by rw [sideMin_of_pure hp₁ hne₁]; exact hHa.symm)).1
      have h0 : sideDeg (X : Polynomial O) a' u ℓ hne₁ = 0 := by
        rw [← hdega]
        exact Polynomial.natDegree_eq_zero_of_isUnit hua
      have hdla : ℓ * sideDeg (X : Polynomial O) a' u ℓ hne₁
          = a'.natDegree / (X : Polynomial O).natDegree :=
        sideDeg_of_pure isKey_X.monic isKey_X.pos ha'm hda0 hℓ hcop hp₁ hne₁
      have ha'0 : a'.natDegree = 0 := by
        rw [hX1, Nat.div_one, h0, Nat.mul_zero] at hdla
        exact hdla.symm
      have ha'1 : Polynomial.C b.leadingCoeff * a = 1 := by
        rw [← ha']
        exact Polynomial.eq_one_of_monic_natDegree_zero ha'm ha'0
      exact hna (IsUnit.of_mul_eq_one (Polynomial.C b.leadingCoeff) (by rw [mul_comm]; exact ha'1))
    · -- symmetric: `b' = 1`, so `b` is a unit
      have hdegb : (resPoly π (X : Polynomial O) b' u ℓ hne₂ Hb).natDegree
          = sideDeg (X : Polynomial O) b' u ℓ hne₂ :=
        (natDegree_resPoly hπ isKey_X hℓ hcop htfb hne₂
          (by rw [sideMin_of_pure hp₂ hne₂]; exact hHb.symm)).1
      have h0 : sideDeg (X : Polynomial O) b' u ℓ hne₂ = 0 := by
        rw [← hdegb]
        exact Polynomial.natDegree_eq_zero_of_isUnit hub
      have hdlb : ℓ * sideDeg (X : Polynomial O) b' u ℓ hne₂
          = b'.natDegree / (X : Polynomial O).natDegree :=
        sideDeg_of_pure isKey_X.monic isKey_X.pos hb'm hdb0 hℓ hcop hp₂ hne₂
      have hb'0 : b'.natDegree = 0 := by
        rw [hX1, Nat.div_one, h0, Nat.mul_zero] at hdlb
        exact hdlb.symm
      have hb'1 : Polynomial.C a.leadingCoeff * b = 1 := by
        rw [← hb']
        exact Polynomial.eq_one_of_monic_natDegree_zero hb'm hb'0
      exact hnb (IsUnit.of_mul_eq_one (Polynomial.C a.leadingCoeff) (by rw [mul_comm]; exact hb'1))

/-- The monic factor multiset of the block is the singleton `{g}`. -/
theorem monicFactors_of_pure_of_resPoly_irreducible (hπ : Irreducible π) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt (X : Polynomial O) g (sideMin (X : Polynomial O) g u ℓ hne) = (H₀ : ℕ∞))
    (hirr : Irreducible (resPoly π (X : Polynomial O) g u ℓ hne H₀)) :
    monicFactors g = {g} := by
  have hgi := irreducible_of_pure_of_resPoly_irreducible hπ hu hℓ hcop hg hpure hne hH hirr
  refine monicFactors_eq ⟨fun p hp => ?_, by simp⟩
  rw [Multiset.mem_singleton] at hp
  subst hp
  exact ⟨hg, hgi⟩

/-- Step I at a LINEAR residual — the dissection blocks' instance. -/
theorem irreducible_of_pure_of_resPoly_linear (hπ : Irreducible π) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {p : Polynomial O} (hp : p.Monic)
    (hpure : IsPure (X : Polynomial O) p u ℓ)
    (hne : (sideSet (X : Polynomial O) p u ℓ).Nonempty) {H₀ : ℕ}
    (hH0 : npHgt (X : Polynomial O) p 0 = (H₀ : ℕ∞))
    {c : resField (X : Polynomial O)}
    (hres : resPoly π (X : Polynomial O) p u ℓ hne H₀ = Polynomial.X - Polynomial.C c) :
    Irreducible p := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  refine irreducible_of_pure_of_resPoly_irreducible hπ hu hℓ hcop hp hpure hne
    (H₀ := H₀) ?_ ?_
  · rw [sideMin_of_pure hpure hne]; exact hH0
  · rw [hres]; exact Polynomial.irreducible_X_sub_C c

end Irred

/-! ## §4 — the pinned dissection (B.63's private engine, re-derived) -/

section Dissection

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O]

/-- **The pinned dissection** (B.63 §1, re-derived verbatim: `Finset.induction` over
B.41b's graded Hensel factorization).  A monic pure `f` whose residual is a product of
pairwise-coprime monic irreducibles dissects into monic pure blocks with residual
polynomial EQUAL to the prescribed factors. -/
theorem exists_pinned_dissection (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) :
    ∀ s : Finset (Polynomial (resField φ)),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) →
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) →
      ∀ f : Polynomial O, f.Monic → φ.natDegree ∣ f.natDegree → IsPure φ f u ℓ →
      ∀ (hne : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), npHgt φ f 0 = (H₀ : ℕ∞) →
      resPoly π φ f u ℓ hne H₀ = ∏ ψ ∈ s, ψ →
      ∃ G : Polynomial (resField φ) → Polynomial O,
        f = ∏ ψ ∈ s, G ψ ∧
        (∀ ψ ∈ s, (G ψ).Monic ∧ IsPure φ (G ψ) u ℓ ∧
          (G ψ).natDegree = ℓ * φ.natDegree * ψ.natDegree ∧
          npHgt φ (G ψ) 0 = ((u * ψ.natDegree : ℕ) : ℕ∞) ∧
          ∀ hne' : (sideSet φ (G ψ) u ℓ).Nonempty,
            resPoly π φ (G ψ) u ℓ hne' (u * ψ.natDegree) = ψ) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ f hf hfd hpure hne H₀ hH₀ hres
    have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
      (Nat.div_mul_cancel hfd).symm
    have htf : suppVal φ f u ℓ ≠ ⊤ := by
      rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hpure]; exact ENat.coe_ne_top _
    have hfmin : sideMin φ f u ℓ hne = 0 := sideMin_of_pure hpure hne
    have hHf : npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := by rw [hfmin]; exact hH₀
    have hRdeg : (resPoly π φ f u ℓ hne H₀).natDegree = sideDeg φ f u ℓ hne :=
      (natDegree_resPoly hπ hφ hℓ hcop htf hne hHf).1
    have hsd : sideDeg φ f u ℓ hne = 0 := by
      rw [← hRdeg, hres, Finset.prod_empty, Polynomial.natDegree_one]
    have hdl : ℓ * sideDeg φ f u ℓ hne = f.natDegree / φ.natDegree :=
      sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hpure hne
    have hf0 : f.natDegree = 0 := by
      rw [hfdeg0, ← hdl, hsd, Nat.mul_zero, Nat.zero_mul]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hf hf0, Finset.prod_empty]
    · intro ψ hψ; simp at hψ
  | insert ψ₀ s' hψ₀ ih =>
    intro hmon hpc f hf hfd hpure hne H₀ hH₀ hres
    have hψ₀mem : ψ₀ ∈ insert ψ₀ s' := Finset.mem_insert_self _ _
    have hψ₀m : ψ₀.Monic := (hmon ψ₀ hψ₀mem).1
    have hHm : (∏ ψ ∈ s', ψ).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun ψ hψ => (hmon ψ (Finset.mem_insert_of_mem hψ)).1
    have hGH : IsCoprime ψ₀ (∏ ψ ∈ s', ψ) :=
      IsCoprime.prod_right fun ψ hψ =>
        hpc ψ₀ hψ₀mem ψ (Finset.mem_insert_of_mem hψ) fun hcon => hψ₀ (hcon ▸ hψ)
    have hprod : ∃ c : (resField φ)ˣ, resPoly π φ f u ℓ hne H₀
        = Polynomial.C (c : resField φ) * (ψ₀ * ∏ ψ ∈ s', ψ) := by
      refine ⟨1, ?_⟩
      rw [hres, Finset.prod_insert hψ₀]
      simp
    obtain ⟨g, h, hgm, hhm, hfgh, hgdeg, hhdeg, hgp, hhp, -, hgH, hhH, hgres, hhres⟩ :=
      exists_graded_factorization hπ hφ hu hℓ hcop hf hfd hpure hH₀ hne hψ₀m hHm hGH hprod
    have hhd : φ.natDegree ∣ h.natDegree := ⟨ℓ * (∏ ψ ∈ s', ψ).natDegree, by
      rw [hhdeg]; ring⟩
    have hhne : (sideSet φ h u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    obtain ⟨G', hG'prod, hG'props⟩ :=
      ih (fun ψ hψ => hmon ψ (Finset.mem_insert_of_mem hψ))
        (fun ψ hψ χ hχ hne' =>
          hpc ψ (Finset.mem_insert_of_mem hψ) χ (Finset.mem_insert_of_mem hχ) hne')
        h hhm hhd hhp hhne (u * (∏ ψ ∈ s', ψ).natDegree) hhH (hhres hhne)
    refine ⟨fun ψ => if ψ = ψ₀ then g else G' ψ, ?_, ?_⟩
    · have hFeq : ∀ ψ ∈ s', (if ψ = ψ₀ then g else G' ψ) = G' ψ := by
        intro ψ hψ
        have hnem : ψ ≠ ψ₀ := fun hcon => hψ₀ (hcon ▸ hψ)
        simp [hnem]
      rw [Finset.prod_insert hψ₀, if_pos rfl, hfgh, hG'prod]
      exact congrArg (g * ·) (Finset.prod_congr rfl fun ψ hψ => (hFeq ψ hψ).symm)
    · intro ψ hψ
      rcases Finset.mem_insert.1 hψ with rfl | hψ'
      · simp only []
        exact ⟨hgm, hgp, hgdeg, hgH, hgres⟩
      · have hnem : ψ ≠ ψ₀ := fun hcon => hψ₀ (hcon ▸ hψ')
        simp only [if_neg hnem]
        exact hG'props ψ hψ'

end Dissection

/-! ## §5 — the residual key: the monic lift of the irreducible residual -/

section KeyLift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Every monic polynomial over the residue field lifts to a monic polynomial of the
same degree. -/
theorem exists_monic_lift (R : Polynomial (IsLocalRing.ResidueField O)) (hR : R.Monic) :
    ∃ ψt : Polynomial O, ψt.Monic ∧ ψt.map (IsLocalRing.residue O) = R
      ∧ ψt.natDegree = R.natDegree := by
  have hlift : R ∈ Polynomial.lifts (IsLocalRing.residue O) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => IsLocalRing.residue_surjective (R.coeff i)
  obtain ⟨ψt, hmap, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hR
  refine ⟨ψt, hmon, hmap, ?_⟩
  rw [← hmap, hmon.natDegree_map]

end KeyLift

/-! ## §6 — ★★ the conjugate-orbit factorization at the residual key -/

section CoreEngine

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {ψt : Polynomial O}
  [IsDomain (AdjoinRoot ψt)] [IsDiscreteValuationRing (AdjoinRoot ψt)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot ψt)) (AdjoinRoot ψt)]
  [Finite (ResidueField (AdjoinRoot ψt))]

/-- ★★ **THE CONJUGATE-ORBIT FACTORIZATION**: a monic x-pure block `g` whose x-frame
digit residual LIFTS to the key `ψt` base-changes, over `AdjoinRoot ψt`, to the FULL
conjugate orbit `tauProd hkey C` of a single monic degree-`ℓ` factor.  Mechanism: the
residual splits into the `deg ψt` distinct linear factors indexed by `keyRoots`
(IFCG29); the pinned dissection factors `g.map A` along them; each block is irreducible
(Step I at the linear residual); the conjugates of the `β₀`-block are matched to the
blocks by their residuals in the UFD `(AdjoinRoot ψt)[x]`. -/
theorem exists_tauProd_factorization (hkey : IsKey ψt) {π : O} (hπ : Irreducible π)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {g : Polynomial O} (hg : g.Monic) (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH0 : npHgt (X : Polynomial O) g 0 = (H₀ : ℕ∞))
    (hψtmap : ψt.map (IsLocalRing.residue O) = xres π g u ℓ hne H₀) :
    ∃ C : Polynomial (AdjoinRoot ψt), C.Monic ∧ C.natDegree = ℓ ∧
      g.map (algebraMap O (AdjoinRoot ψt)) = tauProd hkey C := by
  classical
  letI : Field (resField (X : Polynomial (AdjoinRoot ψt))) := instFieldResField isKey_X
  -- ## M1: the block transports to the unramified extension
  have hπ' : Irreducible (algebraMap O (AdjoinRoot ψt) π) :=
    irreducible_algebraMap_adjoinRoot hkey hπ
  have hg'm : (g.map (algebraMap O (AdjoinRoot ψt))).Monic := hg.map _
  have hp' : IsPure (X : Polynomial (AdjoinRoot ψt)) (g.map (algebraMap O (AdjoinRoot ψt))) u ℓ :=
    isPure_X_map hπ hπ' hg hpure
  have hne' : (sideSet (X : Polynomial (AdjoinRoot ψt))
      (g.map (algebraMap O (AdjoinRoot ψt))) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  have hH0' : npHgt (X : Polynomial (AdjoinRoot ψt))
      (g.map (algebraMap O (AdjoinRoot ψt))) 0 = (H₀ : ℕ∞) := by
    rw [npHgt_X_map hπ hπ']; exact hH0
  have hxres' : xres (algebraMap O (AdjoinRoot ψt) π) (g.map (algebraMap O (AdjoinRoot ψt)))
        u ℓ hne' H₀
      = (xres π g u ℓ hne H₀).map (resEmb hkey) :=
    xres_map hπ hπ' (resEmb hkey) (fun a => resEmb_residue hkey a) hg u ℓ hne hne' H₀
  -- ## M2: the residual splits into the distinct linear factors indexed by `keyRoots`
  have hResSplit : (xres π g u ℓ hne H₀).map (resEmb hkey)
      = ((keyRoots hkey).map fun β => Polynomial.X - Polynomial.C β).prod := by
    have hmonK : ((ψt.map (IsLocalRing.residue O)).map (resEmb hkey)).Monic :=
      (hkey.monic.map _).map _
    have hcard : ((ψt.map (IsLocalRing.residue O)).map (resEmb hkey)).roots.card
        = ((ψt.map (IsLocalRing.residue O)).map (resEmb hkey)).natDegree := by
      rw [(hkey.monic.map _).natDegree_map, hkey.monic.natDegree_map]
      exact card_keyRoots hkey
    have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonK hcard
    rw [← hψtmap]
    exact hprod.symm
  -- the resPoly of the pushed block is the product of the distinct monic linears
  set ι : IsLocalRing.ResidueField (AdjoinRoot ψt)
      →+* resField (X : Polynomial (AdjoinRoot ψt)) :=
    (resFieldXEquiv (AdjoinRoot ψt) : IsLocalRing.ResidueField (AdjoinRoot ψt)
      →+* resField (X : Polynomial (AdjoinRoot ψt))) with hιdef
  have hιinj : Function.Injective ι := (resFieldXEquiv (AdjoinRoot ψt)).injective
  set s : Finset (Polynomial (resField (X : Polynomial (AdjoinRoot ψt)))) :=
    (keyRoots hkey).toFinset.image
      (fun β => Polynomial.X - Polynomial.C (ι β)) with hsdef
  have hlinj : ∀ β ∈ (keyRoots hkey).toFinset, ∀ γ ∈ (keyRoots hkey).toFinset,
      Polynomial.X - Polynomial.C (ι β) = Polynomial.X - Polynomial.C (ι γ) → β = γ := by
    intro β _ γ _ hab
    have hC : Polynomial.C (ι β) = Polynomial.C (ι γ) := sub_right_injective hab
    exact hιinj (Polynomial.C_injective hC)
  have hres' : resPoly (algebraMap O (AdjoinRoot ψt) π) (X : Polynomial (AdjoinRoot ψt))
        (g.map (algebraMap O (AdjoinRoot ψt))) u ℓ hne' H₀
      = ∏ ψβ ∈ s, ψβ := by
    rw [resPoly_x_frame, hxres', hResSplit, hsdef]
    rw [Finset.prod_image hlinj, Finset.prod_eq_multiset_prod]
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_keyRoots hkey)]
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun β _ => ?_
    rw [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- ## M3: the pinned dissection along the split residual
  have hmon : ∀ ψβ ∈ s, ψβ.Monic ∧ Irreducible ψβ := by
    intro ψβ hψβ
    rw [hsdef] at hψβ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hψβ
    exact ⟨Polynomial.monic_X_sub_C _, Polynomial.irreducible_X_sub_C _⟩
  have hpair : ∀ ψβ ∈ s, ∀ χ ∈ s, ψβ ≠ χ → IsCoprime ψβ χ := by
    intro ψβ hψβ χ hχ hnee
    rw [hsdef] at hψβ hχ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hψβ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hχ
    have hβγ : ι β - ι γ ≠ 0 := by
      intro hcon
      exact hnee (by rw [sub_eq_zero.mp hcon])
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr hβγ)
  obtain ⟨G, hGprod, hGprops⟩ :=
    exists_pinned_dissection hπ' isKey_X hu hℓ hcop s hmon hpair
      (g.map (algebraMap O (AdjoinRoot ψt))) hg'm
      (by rw [Polynomial.natDegree_X]; exact one_dvd _) hp' hne' H₀ hH0' hres'
  -- the per-root block data (linear residual: degrees collapse to `ℓ` and heights to `u`)
  have hblock : ∀ β ∈ (keyRoots hkey).toFinset,
      (G (Polynomial.X - Polynomial.C (ι β))).Monic
      ∧ IsPure (X : Polynomial (AdjoinRoot ψt)) (G (Polynomial.X - Polynomial.C (ι β))) u ℓ
      ∧ (G (Polynomial.X - Polynomial.C (ι β))).natDegree = ℓ
      ∧ npHgt (X : Polynomial (AdjoinRoot ψt)) (G (Polynomial.X - Polynomial.C (ι β))) 0
          = ((u : ℕ) : ℕ∞)
      ∧ ∀ hneb : (sideSet (X : Polynomial (AdjoinRoot ψt))
            (G (Polynomial.X - Polynomial.C (ι β))) u ℓ).Nonempty,
          resPoly (algebraMap O (AdjoinRoot ψt) π) (X : Polynomial (AdjoinRoot ψt))
              (G (Polynomial.X - Polynomial.C (ι β))) u ℓ hneb u
            = Polynomial.X - Polynomial.C (ι β) := by
    intro β hβ
    have hmem : Polynomial.X - Polynomial.C (ι β) ∈ s := by
      rw [hsdef]; exact Finset.mem_image_of_mem _ hβ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hGprops _ hmem
    have hdeg1 : (Polynomial.X - Polynomial.C (ι β)).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    refine ⟨h1, h2, ?_, ?_, ?_⟩
    · rw [h3, hdeg1, Polynomial.natDegree_X, Nat.mul_one, Nat.mul_one]
    · rw [hdeg1, Nat.mul_one] at h4; exact h4
    · intro hneb
      have h6 := h5 hneb
      rw [hdeg1, Nat.mul_one] at h6
      exact h6
  -- ## M4: the `β₀`-block and the conjugate matching
  set β₀ : IsLocalRing.ResidueField (AdjoinRoot ψt) :=
    IsLocalRing.residue (AdjoinRoot ψt) (AdjoinRoot.root ψt) with hβ₀def
  have hβ₀ : β₀ ∈ keyRoots hkey := residue_root_mem_keyRoots hkey
  have hβ₀' : β₀ ∈ (keyRoots hkey).toFinset := Multiset.mem_toFinset.mpr hβ₀
  obtain ⟨hCm, hCp, hCdeg, hCH, hCres⟩ := hblock β₀ hβ₀'
  refine ⟨G (Polynomial.X - Polynomial.C (ι β₀)), hCm, hCdeg, ?_⟩
  -- each conjugate of the `β₀`-block IS the `β`-block
  have hconj : ∀ β ∈ (keyRoots hkey).toFinset,
      (G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom
        = G (Polynomial.X - Polynomial.C (ι β)) := by
    intro β hβmem
    have hβk : β ∈ keyRoots hkey := Multiset.mem_toFinset.mp hβmem
    have hfix : (tau hkey β).toRingHom (algebraMap O (AdjoinRoot ψt) π)
        = algebraMap O (AdjoinRoot ψt) π := (tau hkey β).commutes π
    have hτπ : Irreducible ((tau hkey β).toRingHom (algebraMap O (AdjoinRoot ψt) π)) := by
      rw [hfix]; exact hπ'
    have hneC : (sideSet (X : Polynomial (AdjoinRoot ψt))
        (G (Polynomial.X - Polynomial.C (ι β₀))) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hneCb : (sideSet (X : Polynomial (AdjoinRoot ψt))
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) u ℓ).Nonempty :=
      sideSet_nonempty_gen _ _ _ _
    -- the digit polynomial of the `β₀`-block is the linear at `β₀`
    have hxC : xres (algebraMap O (AdjoinRoot ψt) π)
        (G (Polynomial.X - Polynomial.C (ι β₀))) u ℓ hneC u
        = Polynomial.X - Polynomial.C β₀ := by
      have h5 := hCres hneC
      rw [resPoly_x_frame] at h5
      have hrhs : (Polynomial.X - Polynomial.C β₀).map ι
          = Polynomial.X - Polynomial.C (ι β₀) := by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact Polynomial.map_injective ι hιinj (h5.trans hrhs.symm)
    -- ...so the conjugate's digit polynomial is the linear at `β` (tau-equivariance)
    have hmap := xres_map (h := (tau hkey β).toRingHom)
      (π := algebraMap O (AdjoinRoot ψt) π) hπ' hτπ (resTau hkey β)
      (fun a => resTau_residue hkey β a) hCm u ℓ hneC hneCb u
    rw [hfix, hxC] at hmap
    have hxCb : xres (algebraMap O (AdjoinRoot ψt) π)
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) u ℓ hneCb u
        = Polynomial.X - Polynomial.C β := by
      rw [hmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hβ₀def,
        resTau_apply_of_mem hkey hβk]
    have hCbres : resPoly (algebraMap O (AdjoinRoot ψt) π) (X : Polynomial (AdjoinRoot ψt))
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) u ℓ hneCb u
        = Polynomial.X - Polynomial.C (ι β) := by
      rw [resPoly_x_frame, hxCb]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    have hCbH : npHgt (X : Polynomial (AdjoinRoot ψt))
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) 0
        = ((u : ℕ) : ℕ∞) := by
      rw [npHgt_X_map (h := (tau hkey β).toRingHom)
        (π := algebraMap O (AdjoinRoot ψt) π) hπ' hτπ]
      exact hCH
    have hCbirr : Irreducible
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) :=
      irreducible_of_pure_of_resPoly_linear hπ' hu hℓ hcop (hCm.map _)
        (isPure_X_map hπ' hτπ hCm hCp) hneCb hCbH hCbres
    -- the conjugate divides the block product
    have hmemβ₀ : Polynomial.X - Polynomial.C (ι β₀) ∈ s := by
      rw [hsdef]; exact Finset.mem_image_of_mem _ hβ₀'
    have hCdvd : G (Polynomial.X - Polynomial.C (ι β₀))
        ∣ g.map (algebraMap O (AdjoinRoot ψt)) := by
      rw [hGprod]
      exact Finset.dvd_prod_of_mem G hmemβ₀
    have hCbdvd : (G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom
        ∣ ∏ ψβ ∈ s, G ψβ := by
      have h2 := Polynomial.map_dvd (tau hkey β).toRingHom hCdvd
      rw [map_tau_map_algebraMap hkey β g] at h2
      rwa [hGprod] at h2
    -- UFD matching: it equals one of the blocks, and the residual pins WHICH one
    have hCbprime : Prime
        ((G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hCbirr
    obtain ⟨ψγ, hψγmem, hdvdγ⟩ := hCbprime.exists_mem_finset_dvd hCbdvd
    obtain ⟨γ, hγmem, hγeq⟩ := Finset.mem_image.mp (by rw [hsdef] at hψγmem; exact hψγmem)
    rw [← hγeq] at hdvdγ
    obtain ⟨hGγm, hGγp, -, hGγH, hGγres⟩ := hblock γ hγmem
    have hneGγ : (sideSet (X : Polynomial (AdjoinRoot ψt))
        (G (Polynomial.X - Polynomial.C (ι γ))) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hGγirr : Irreducible (G (Polynomial.X - Polynomial.C (ι γ))) :=
      irreducible_of_pure_of_resPoly_linear hπ' hu hℓ hcop hGγm hGγp hneGγ hGγH
        (hGγres hneGγ)
    have heqγ : (G (Polynomial.X - Polynomial.C (ι β₀))).map (tau hkey β).toRingHom
        = G (Polynomial.X - Polynomial.C (ι γ)) :=
      Polynomial.eq_of_monic_of_associated (hCm.map _) hGγm
        (hCbirr.associated_of_dvd hGγirr hdvdγ)
    have hResEq : Polynomial.X - Polynomial.C (ι β) = Polynomial.X - Polynomial.C (ι γ) := by
      rw [← hCbres, ← hGγres hneGγ]
      exact resPoly_congr _ _ heqγ hneCb hneGγ
    have hβγ : β = γ := hlinj β hβmem γ hγmem hResEq
    rw [heqγ, hβγ]
  -- ## conclusion: the conjugate product is the block product
  rw [hGprod, hsdef, Finset.prod_image hlinj]
  unfold tauProd
  exact Finset.prod_congr rfl fun β hβ => (hconj β hβ).symm

end CoreEngine

/-! ## §6b — ★★★ THE CORE: `d ∣ inertiaDegOf g` at the residual-irreducible block -/

section Core

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE RESIDUAL-INERTIA THEOREM at the x-frame** (B-BOX-1's content, PROVED):
a monic x-pure block of slope `u/ℓ` with irreducible side residual of degree `d` has
`d ∣ inertiaDegOf g`.  Mechanism: base change to the unramified extension by a monic
key lift of the residual, dissect along the split residual, recognize the conjugate
orbit, and descend the norm valuations (IFCG32 LEG A). -/
theorem sideDeg_dvd_inertiaDegOf (hπ : Irreducible π) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure (X : Polynomial O) g u ℓ)
    (hne : (sideSet (X : Polynomial O) g u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt (X : Polynomial O) g (sideMin (X : Polynomial O) g u ℓ hne) = (H₀ : ℕ∞))
    (hirr : Irreducible (resPoly π (X : Polynomial O) g u ℓ hne H₀)) :
    sideDeg (X : Polynomial O) g u ℓ hne ∣ inertiaDegOf g := by
  classical
  -- degree and side-degree pins over the base
  have hd := sideDeg_pos_of_resPoly_irreducible hπ hℓ hcop hg hpure hne hH hirr
  have hX1 : (X : Polynomial O).natDegree = 1 := Polynomial.natDegree_X
  have hdeg0 : g.natDegree
      = (g.natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree := by
    rw [hX1]; simp
  have hdl : ℓ * sideDeg (X : Polynomial O) g u ℓ hne
      = g.natDegree / (X : Polynomial O).natDegree :=
    sideDeg_of_pure isKey_X.monic isKey_X.pos hg hdeg0 hℓ hcop hpure hne
  have hgdeg : g.natDegree = ℓ * sideDeg (X : Polynomial O) g u ℓ hne := by
    rw [hX1, Nat.div_one] at hdl; exact hdl.symm
  have hgpos : 0 < g.natDegree := by rw [hgdeg]; exact Nat.mul_pos hℓ hd
  -- the digit polynomial, its irreducibility, and its monic key lift
  obtain ⟨hRdeg, hRmon⟩ := xres_natDegree_monic hπ hu hℓ hcop hg hpure hne hH
  have hRirr : Irreducible (xres π g u ℓ hne H₀) := irreducible_resPoly_x_iff.mp hirr
  obtain ⟨ψt, hψtm, hψtmap, hψtdeg⟩ := exists_monic_lift (xres π g u ℓ hne H₀) hRmon
  have hkey : IsKey ψt :=
    ⟨hψtm, by rw [hψtdeg, hRdeg]; exact hd, by rw [hψtmap]; exact hRirr⟩
  -- the unramified extension's ENV-C instances (IFCG32's cascade)
  letI i1 : IsDomain (AdjoinRoot ψt) := keyIsDomain hkey
  letI i2 : IsDiscreteValuationRing (AdjoinRoot ψt) := adjoinRoot_isDVR hkey
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot ψt)) (AdjoinRoot ψt) :=
    adjoinRoot_isAdicComplete hkey
  letI i4 : Finite (ResidueField (AdjoinRoot ψt)) := adjoinRoot_finite_residueField hkey
  -- the conjugate-orbit factorization
  have hmin : sideMin (X : Polynomial O) g u ℓ hne = 0 := sideMin_of_pure hpure hne
  rw [hmin] at hH
  obtain ⟨C, hCm, hCdeg, hGmap⟩ :=
    exists_tauProd_factorization hkey hπ hu hℓ hcop hg hpure hne hH hψtmap
  -- descent of the norm valuations (IFCG32 LEG A) and the gcd arithmetic
  have hCpos : 0 < C.natDegree := by rw [hCdeg]; exact hℓ
  have hnv : (normValues g).Nonempty := normValues_nonempty hg hgpos
  have hdmem : sideDeg (X : Polynomial O) g u ℓ hne ∈ normDivisors g := by
    refine ⟨hd, fun k hk => ?_⟩
    obtain ⟨v, hv, rfl⟩ := normValues_descent hkey hCm hCpos hg hGmap k hk
    rw [hψtdeg, hRdeg]
    exact dvd_mul_right _ v
  exact dvd_inertiaDegOf_of_mem_normDivisors hnv hdmem

end Core

/-! ## §7 — ★★★ THE SUPPLY and the leaf laws at every `(e', d)` -/

section Supply

/-- ★★★ **`ResidualInertiaSupply` HOLDS** — the one open leaf leg of IFCG35, closed. -/
theorem residualInertiaSupply : Uniformity.Density.IFCG35.ResidualInertiaSupply := by
  intro O _ _ _ _ _ π hπ u ℓ hu hℓ hcop g hg hpure hne H₀ hH hirr g' hg'
  have hfac := monicFactors_of_pure_of_resPoly_irreducible hπ hu hℓ hcop hg hpure hne hH hirr
  rw [hfac, Multiset.mem_singleton] at hg'
  subst hg'
  exact sideDeg_dvd_inertiaDegOf hπ hu hℓ hcop hg hpure hne hH hirr

/-- ★★★ **The residual-irreducible leaf law holds at EVERY `(e', d)`** — IFCG35's
`residualLeafLaw_of_supply` fired with the supply. -/
theorem residualLeafLaw_all {e' d : ℕ} (he' : 0 < e') (hd : 0 < d) :
    Uniformity.Density.IFCG35.ResidualLeafLaw e' d :=
  Uniformity.Density.IFCG35.residualLeafLaw_of_supply residualInertiaSupply he' hd

end Supply

/-! ## §8 — the ER4 wiring: `E1IrrLeafDecision` (the `(2,2)` instance) and the rows -/

section ER4

open Uniformity.Density.Induction
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  NPVisibleAt classNPSupport_le_apply le_classNPSupport)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq)
open Uniformity.Density.IFCG24 (mem_stratum_X_pow_iff coneRemainderCount)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG34
open Uniformity.Density.IFCG35 (classResidualPoly classResidualPoly_eq
  decidedAt_of_spanning_leaf)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The E1 class-polygon package (private copy of IFCG34's bank). -/
private theorem e1_class_bank' {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e1Box O K) :
    classNPSupport c 1 2 = 4 ∧ NPAttains c 1 2 0 ∧ NPAttains c 1 2 4
      ∧ NPVisibleAt c 1 2 ∧ c ∈ levelZeroStratum O 4 K (X ^ 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e1Box_iff c).1 hc
  have hnp0 : npHeight c 0 = 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : 2 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : 1 ≤ npHeight c 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
    exact h2
  have hnp3 : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact h3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  have hsup : classNPSupport c 1 2 = 4 := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c 1 2 (show (0 : ℕ) ≤ 4 by norm_num)
      rw [hnp0] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · omega
      · omega
      · omega
      · omega
  have hAt0 : NPAttains c 1 2 0 := ⟨by omega, by rw [hnp0, hsup]⟩
  have hAt4 : NPAttains c 1 2 4 := ⟨le_refl 4, by rw [hnp4, hsup]⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  have hstr : c ∈ levelZeroStratum O 4 K (X ^ 4) := by
    refine (mem_stratum_X_pow_iff (by omega) c).2 ?_
    intro i
    fin_cases i
    · exact le_of_le_of_eq (by norm_num) h0.symm
    · exact le_trans (by norm_num) h1
    · exact h2
    · exact h3
  exact ⟨hsup, hAt0, hAt4, hvis, hstr⟩

/-- The lift-side data of a spanning face (private copy of IFCG35's bank). -/
private theorem spanning_side_data' {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    (hm0 : 0 < m) (he' : 0 < e')
    {c : Coeff O m K} (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m)
    (hvis : NPVisibleAt c h e') {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ hne : (sideSet X (monicPoly a) h e').Nonempty,
      sideMin X (monicPoly a) h e' hne = 0 ∧ sideMax X (monicPoly a) h e' hne = m
        ∧ suppVal X (monicPoly a) h e' ≠ ⊤ := by
  obtain ⟨hOn0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis h0 ha
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hmm ha
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have h0mem : (0 : ℕ) ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  refine ⟨⟨0, h0mem⟩, ?_, ?_, htop⟩
  · unfold sideMin
    exact Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  · unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') ⟨0, h0mem⟩
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega

end ER4

section ER4Fire

open Uniformity.Density.Induction
open Uniformity.Density.IFCG22 (classCoeffVal NPAttains NPVisibleAt)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq)
open Uniformity.Density.IFCG24 (coneRemainderCount)
open Uniformity.Density.IFCG34
open Uniformity.Density.IFCG35 (classResidualPoly classResidualPoly_eq
  decidedAt_of_spanning_leaf)

/-- ★★★ **The spanning leaf decision, UNCONDITIONAL** — IFCG35's
`decidedAt_of_spanning_leaf` with its leaf premise discharged by the supply: a stratum
class whose face `h/e'` spans `[0, m]` (`m = e'·d`, coprime, visible) with IRREDUCIBLE
class residual is decided `⟨{(e', d)}⟩`, for EVERY `(e', d)`. -/
theorem decidedAt_of_spanning_irr {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {e' d : ℕ} (hd0 : 0 < d)
    {π : O} (hπ : Irreducible π) {m K h : ℕ} (hm0 : 0 < m) (hh : 0 < h)
    (he' : 0 < e') (hcop : Nat.Coprime h e') (hd : m = e' * d)
    {c : Coeff O m K} (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    (hirr : Irreducible (classResidualPoly π c h e')) :
    DecidedAt O m ⟨{(e', d)}⟩ K c :=
  decidedAt_of_spanning_leaf (residualLeafLaw_all he' hd0) hπ hm0 hh he' hcop hd hstr
    h0 hmm hvis hirr

/-- ★★★ **`E1IrrLeafDecision` HOLDS** — ER4's named open leaf (the `ℓ = 2, deg ψ = 2`
instance of B-BOX-1) is the `(2,2)` instance of the leaf law, now unconditional: every
irreducible-residual E1 class is decided `{(2,2)}`. -/
theorem e1IrrLeafDecision : Uniformity.Density.IFCG34.E1IrrLeafDecision := by
  intro O _ _ _ _ _ K hK π hπ c hc
  obtain ⟨hcE1, a₀, ha₀, hirr₀⟩ := hc
  obtain ⟨hsup, hAt0, hAt4, hvis, hstr⟩ := e1_class_bank' hK hcE1
  -- the class residual is irreducible: read it off the box's witness lift
  have hirrC : Irreducible (classResidualPoly π c 1 2) := by
    obtain ⟨hne₀, hmin₀, hmax₀, htop₀⟩ :=
      spanning_side_data' hπ (by norm_num) (by norm_num) hAt0 hAt4 hvis ha₀
    have hntop : npHgt X (monicPoly a₀) (sideMin X (monicPoly a₀) 1 2 hne₀) ≠ ⊤ :=
      npHgt_ne_top_of_onSide (by norm_num) htop₀
        (onSide_of_mem_sideSet (Finset.min'_mem _ hne₀))
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
    have hw' : ((w : ℕ) : ℕ∞) = npHgt X (monicPoly a₀) (sideMin X (monicPoly a₀) 1 2 hne₀) :=
      hw
    have hcrp := classResidualPoly_eq hπ (by norm_num) hvis ha₀ hne₀ hw'.symm
    rw [hcrp]
    -- the left height is 2 (the box pins `v₀ = 2` exactly, below the window)
    have h0v : resOrd (c 0) = 2 := ((mem_e1Box_iff c).1 hcE1).1
    have hcv : classCoeffVal c ⟨0, by norm_num⟩ = 2 := h0v
    have hvis0 : classCoeffVal c ⟨0, by norm_num⟩ < K := by omega
    have hnp := npHgt_monicPoly_eq hπ ha₀ (by norm_num : (0 : ℕ) < 4) hvis0
    rw [hmin₀, hnp, hcv] at hw'
    have hw2 : w = 2 := by exact_mod_cast hw'
    rw [hw2]
    exact hirr₀
  exact decidedAt_of_spanning_leaf (residualLeafLaw_all (by norm_num) (by norm_num)) hπ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hstr
    hAt0 hAt4 hvis hirrC

/-- ★ The irreducible sector is FULLY `{(2,2)}`-decided — unconditional. -/
theorem decided_inter_e1Irr {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    decidedSet O 4 type22 K ∩ e1IrrBox π K = e1IrrBox π K :=
  Uniformity.Density.IFCG34.decided_inter_e1Irr_of_leaf e1IrrLeafDecision hK hπ

/-- ★ The `{(4,1)}` alternative is EMPTY on the irreducible sector — unconditional. -/
theorem decided41_inter_e1Irr {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    decidedSet O 4 type41 K ∩ e1IrrBox π K = (∅ : Set (Coeff O 4 K)) :=
  Uniformity.Density.IFCG34.decided41_inter_e1Irr_of_leaf e1IrrLeafDecision hK hπ

/-- ★★ ER4's type22 census row, its leaf premise DISCHARGED. -/
theorem coneRemainderCount_four_type22 {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type22 M
      = Nat.card (e1IrrBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 type22 (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) :=
  Uniformity.Density.IFCG34.coneRemainderCount_four_type22_of_leaf e1IrrLeafDecision hπ M

/-- ★★ ER4's type41 census row, its leaf premise DISCHARGED: the `{(4,1)}` count is
PURELY the double-root recursion term. -/
theorem coneRemainderCount_four_type41 {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type41 M
      = Nat.card ((decidedSet O 4 type41 (M + 4) ∩ e1DdBox π (M + 4))
          : Set (Coeff O 4 (M + 4))) :=
  Uniformity.Density.IFCG34.coneRemainderCount_four_type41_of_leaf e1IrrLeafDecision hπ M

end ER4Fire

end Uniformity.Density.IFCG37

end

/-! ## AXCHECK FOOTER — the core chain must be Lean core `{propext, Classical.choice,
Quot.sound}`; the leaf-law wiring may additionally inherit ONLY the owner-signed B.42
cite through IFCG35's spanning machinery. -/

section AxCheck
#print axioms Uniformity.Density.IFCG37.exists_tauProd_factorization
#print axioms Uniformity.Density.IFCG37.sideDeg_dvd_inertiaDegOf
#print axioms Uniformity.Density.IFCG37.residualInertiaSupply
#print axioms Uniformity.Density.IFCG37.residualLeafLaw_all
#print axioms Uniformity.Density.IFCG37.irreducible_of_pure_of_resPoly_irreducible
#print axioms Uniformity.Density.IFCG37.decidedAt_of_spanning_irr
#print axioms Uniformity.Density.IFCG37.e1IrrLeafDecision
#print axioms Uniformity.Density.IFCG37.decided_inter_e1Irr
#print axioms Uniformity.Density.IFCG37.decided41_inter_e1Irr
#print axioms Uniformity.Density.IFCG37.coneRemainderCount_four_type22
#print axioms Uniformity.Density.IFCG37.coneRemainderCount_four_type41
end AxCheck
