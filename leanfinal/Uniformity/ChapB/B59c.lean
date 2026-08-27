/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B35c
import Uniformity.ChapB.B59a
import Uniformity.ChapC.C27

/-!
# Uniformity.ChapB.B59c — the frame key's scalar residual polynomial (**[I1/MRFIX, 2026-08-27]**)

**Filename note.** The charge (`docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md`, the
`[MRFIX 2026-08-27]` INTERFACE I1 section) asked for this node at `B59b.lean`; that name is
already the landed B.59 contract (`irreducible_map_iff_irreducible_resPoly`, consumed by
`B60.lean`). This file is `B59c` instead — the next free slot in the same `φ = X`
residual-to-reduction family (`B59a` = the digit identity at integral slope; `B59b` = its
irreducibility contract; this file = both, at the *fractional* slope `h/e₁` a `KeyFrame`
carries).

*The interface.* `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md`'s INTERFACE I1 is the open
gap between B.29's `resPoly` (read in `resField X`) and the scalar digit polynomial `ψ` that the
ramified-exactness document's SPREAD 3–4 argument actually manipulates (read in
`IsLocalRing.ResidueField O`). The four obligations, verbatim from the doc:

1. `sideMin = 0`, `sideMax = Φ'.natDegree`, `sideDeg = f₁` at the frame key;
2. the non-`rfl` pin `hpin : npHgt X Φ' (sideMin ...) = ((h*f₁ : ℕ) : ℕ∞)`, from P2
   (`Uniformity.ChapC.C27.isPure_addVal_coeff_zero`, `C27.lean:164-171`) and B.15's `npHgt_X`;
3. coefficientwise identification of `resPoly`'s coefficients with the scalar digits
   `digAt π (h*(f₁-b)) (Φ'.coeff (e₁*b))`, via B35c's `resPoly_coeff_of_pure`
   (`B35c.lean:84-105`), B.15's `dev_X`, B.25/B.23-24's `resMk`/`digPoly`/`digAt` unfolding, and
   B.59a's `resFieldXEquiv`/`resFieldXEquiv_coe`;
4. transport of `Irreducible` and `natDegree = f₁` along that identification, from a
   `KeyFrame.hresirr`-shaped hypothesis (`C01.lean:98-100`) to the scalar polynomial.

This file states and proves all four as reusable chapter-B facts about the raw hypotheses a
`KeyFrame` packages (`he₁ hf₁ hcop hmonic hdeg hpure hne hresirr`), *without* importing
`Uniformity.ChapC.C01`'s `KeyFrame` structure itself — a `ChapC` consumer instantiates the
final theorem by passing `F.he₁ F.hf₁ F.hcop F.hmonic F.hdeg F.hpure F.hne F.hresirr` directly,
literal field for literal hypothesis.

**Reverse dependency, flagged.** This file imports `Uniformity.ChapC.C27` for the single fact
P2 (`isPure_addVal_coeff_zero`), which is stated generically for any monic `g` and `IsPure X g h
e` and does not depend on chapter C's `KeyFrame`; it happens to be filed in a chapter-C module.
No `ChapC` file imports this one, so no cycle is created, but the direction is atypical for this
corpus and is called out for review rather than silently taken.

DEPENDS: B.15 (`dev_X`, `npHgt_X`) · B.29 (`resPoly`) · B.30 (`natDegree_resPoly`, via B35c) ·
B.34 (`IsPure`) · B35c (`resPoly_coeff_of_pure`) · B.59a (`digPoly_C`, `resFieldXEquiv`,
`resFieldXEquiv_coe`) · `Uniformity.ChapC.C27.isPure_addVal_coeff_zero` (P2) · mathlib
`Nat.mul_sub`, `Nat.eq_of_mul_eq_mul_left`, `ENat.ne_top_iff_exists`, `Polynomial.mapEquiv`,
`MulEquiv.irreducible_iff`.

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## A cancellation lemma for `ℕ∞`, needed by obligation 2 -/

private theorem nsmul_eq_top_of_pos' {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  cases n with
  | zero => omega
  | succ k => rw [succ_nsmul]; exact WithTop.add_top _

/-- If `n • x = ↑(n*c)` in `ℕ∞` with `n > 0`, then `x = ↑c`. The cancellation step P2's
consequence needs: `x` cannot be `⊤` (else the left side is `⊤`, not a finite cast), so `x` is
some `↑m`, and `n*m = n*c` in `ℕ` cancels `n`. -/
private theorem eq_of_nsmul_eq_cast_mul {n c : ℕ} (hn : 0 < n) {x : ℕ∞}
    (hx : n • x = ((n * c : ℕ) : ℕ∞)) : x = (c : ℕ∞) := by
  rcases eq_or_ne x ⊤ with hT | hT
  · rw [hT, nsmul_eq_top_of_pos' hn] at hx
    exact absurd hx.symm (ENat.coe_ne_top _)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hT
    rw [← hm] at hx ⊢
    rw [nsmul_eq_mul] at hx
    have hnm : n * m = n * c := by exact_mod_cast hx
    exact_mod_cast Nat.eq_of_mul_eq_mul_left hn hnm

/-! ## Obligation 1 — the side geometry at the frame key -/

/-- **I1, obligation 1.** At a `(h,e₁)`-pure `Φ'` (in the `KeyFrame` sense, degree `e₁*f₁`), the
`X`-adic polygon's side runs from `0` to `Φ'.natDegree`, with residual degree `f₁`. -/
theorem frameKey_sideGeometry {Φ' : Polynomial O} {e₁ f₁ h : ℕ} (he₁ : 0 < e₁)
    (hdeg : Φ'.natDegree = e₁ * f₁) (hpure : IsPure X Φ' h e₁)
    (hne : (sideSet X Φ' h e₁).Nonempty) :
    sideMin X Φ' h e₁ hne = 0 ∧ sideMax X Φ' h e₁ hne = Φ'.natDegree ∧
      sideDeg X Φ' h e₁ hne = f₁ := by
  classical
  have hstart : OnSide X Φ' h e₁ 0 := hpure.1
  have hend : OnSide X Φ' h e₁ Φ'.natDegree := by
    have h2 := hpure.2
    rwa [Polynomial.natDegree_X, Nat.div_one] at h2
  have hmem0 : (0 : ℕ) ∈ sideSet X Φ' h e₁ := by
    have : (0 : ℕ) ∈ Finset.filter (OnSide X Φ' h e₁) (Finset.range (Φ'.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), hstart⟩
    exact this
  have hmemn : Φ'.natDegree ∈ sideSet X Φ' h e₁ := by
    have : Φ'.natDegree ∈ Finset.filter (OnSide X Φ' h e₁) (Finset.range (Φ'.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), hend⟩
    exact this
  have hmin : sideMin X Φ' h e₁ hne = 0 := Nat.le_zero.mp (Finset.min'_le _ _ hmem0)
  have hmax : sideMax X Φ' h e₁ hne = Φ'.natDegree := by
    refine le_antisymm ?_ (Finset.le_max' _ _ hmemn)
    have hmem : sideMax X Φ' h e₁ hne ∈ sideSet X Φ' h e₁ := Finset.max'_mem _ _
    have hmem' : sideMax X Φ' h e₁ hne ∈
        Finset.filter (OnSide X Φ' h e₁) (Finset.range (Φ'.natDegree + 1)) := hmem
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hmem').1)
  refine ⟨hmin, hmax, ?_⟩
  rw [sideDeg, hmax, hmin, Nat.sub_zero, hdeg, Nat.mul_div_cancel_left f₁ he₁]

/-! ## Obligation 2 — the non-`rfl` pin `H₀ = h·f₁` -/

/-- **I1, obligation 2.** The height pin at the frame key's `sideMin`: `H₀ := h*f₁` is the
*value* `npHgt X Φ' (sideMin ...)` takes, derived from P2
(`Uniformity.ChapC.C27.isPure_addVal_coeff_zero`) and B.15's `npHgt_X` — not by `rfl`. -/
theorem frameKey_hpin {Φ' : Polynomial O} (hmonic : Φ'.Monic) {e₁ f₁ h : ℕ} (he₁ : 0 < e₁)
    (hdeg : Φ'.natDegree = e₁ * f₁) (hpure : IsPure X Φ' h e₁)
    (hne : (sideSet X Φ' h e₁).Nonempty) :
    npHgt X Φ' (sideMin X Φ' h e₁ hne) = ((h * f₁ : ℕ) : ℕ∞) := by
  have hmin := (frameKey_sideGeometry he₁ hdeg hpure hne).1
  rw [hmin, npHgt_X]
  have hP2 := Uniformity.Density.Tower.isPure_addVal_coeff_zero hmonic hpure
  have hnat : h * Φ'.natDegree = e₁ * (h * f₁) := by rw [hdeg]; ring
  rw [hnat] at hP2
  exact eq_of_nsmul_eq_cast_mul he₁ hP2

/-! ## The scalar residual polynomial `ψ` -/

/-- **`ψ` of the ramified-exactness document's SPREAD 4**: the scalar-digit polynomial
`Σ_{b=0}^{f₁} [Φ'.coeff (e₁*b)]_{h*(f₁-b)} y^b ∈ (ResidueField O)[y]`, read directly off `Φ'`
without passing through `resField X`. -/
noncomputable def frameResidualPoly (π : O) (Φ' : Polynomial O) (h e₁ f₁ : ℕ) :
    Polynomial (IsLocalRing.ResidueField O) :=
  ∑ b ∈ Finset.range (f₁ + 1),
    Polynomial.C (digAt π (h * (f₁ - b)) (Φ'.coeff (e₁ * b))) * Polynomial.X ^ b

/-- Auxiliary: `X` is an order-1 key (B.01's `IsKey`), needed to invoke B.30's
`natDegree_resPoly`. Reproduces the local pattern already landed at `B63.lean:337`. -/
private theorem isKey_X : IsKey (X : Polynomial O) :=
  ⟨monic_X, by rw [Polynomial.natDegree_X]; omega, by
    rw [Polynomial.map_X]; exact Polynomial.irreducible_X⟩

/-- Auxiliary: at the frame key, `suppVal X Φ' h e₁ ≠ ⊤` — immediate from the finite pin. -/
private theorem frameKey_suppVal_ne_top {Φ' : Polynomial O} (hmonic : Φ'.Monic) {e₁ f₁ h : ℕ}
    (he₁ : 0 < e₁) (hdeg : Φ'.natDegree = e₁ * f₁) (hpure : IsPure X Φ' h e₁)
    (hne : (sideSet X Φ' h e₁).Nonempty) : suppVal X Φ' h e₁ ≠ ⊤ := by
  intro heq
  have hle : suppVal X Φ' h e₁ ≤ e₁ • npHgt X Φ' 0 + ((h * 0 : ℕ) : ℕ∞) :=
    Finset.inf_le (f := fun j => e₁ • npHgt X Φ' j + ((h * j : ℕ) : ℕ∞))
      (Finset.mem_range.mpr (Nat.succ_pos _))
  have hmin := (frameKey_sideGeometry he₁ hdeg hpure hne).1
  have hpin0 : npHgt X Φ' 0 = ((h * f₁ : ℕ) : ℕ∞) := hmin ▸ frameKey_hpin hmonic he₁ hdeg hpure hne
  rw [heq, hpin0] at hle
  simp only [Nat.mul_zero, Nat.cast_zero, add_zero, nsmul_eq_mul] at hle
  exact (ENat.coe_ne_top (e₁ * (h * f₁))) (top_le_iff.mp hle)

/-- Auxiliary: at the frame key, `(resPoly π X Φ' h e₁ hne (h*f₁)).natDegree = f₁` — B.30's
`natDegree_resPoly` specialised via obligation 1's `sideDeg = f₁`. -/
private theorem frameKey_natDegree_resPoly (hπ : Irreducible π) {Φ' : Polynomial O}
    (hmonic : Φ'.Monic) {e₁ f₁ h : ℕ} (he₁ : 0 < e₁) (hdeg : Φ'.natDegree = e₁ * f₁)
    (hcop : Nat.Coprime h e₁) (hpure : IsPure X Φ' h e₁) (hne : (sideSet X Φ' h e₁).Nonempty)
    (hpin : npHgt X Φ' (sideMin X Φ' h e₁ hne) = ((h * f₁ : ℕ) : ℕ∞)) :
    (resPoly π X Φ' h e₁ hne (h * f₁)).natDegree = f₁ := by
  have htop := frameKey_suppVal_ne_top hmonic he₁ hdeg hpure hne
  have hsd := (frameKey_sideGeometry he₁ hdeg hpure hne).2.2
  exact (natDegree_resPoly hπ isKey_X he₁ hcop htop hne hpin).1.trans hsd

/-! ## Obligation 3 — the coefficientwise identification -/

-- `hf₁ : 0 < f₁` is carried to match the `KeyFrame` field it is instantiated from
-- (`F.hf₁`), but this coefficientwise identity holds without it (even at `f₁ = 0`), so it is
-- not consumed here.
set_option linter.unusedVariables false in
/-- **I1, obligation 3.** At `H₀ := h*f₁`, `resPoly`'s `b`-th coefficient (in `resField X`) is
the image, under `resFieldXEquiv O`, of the scalar digit `[Φ'.coeff (e₁*b)]_{h*(f₁-b)}` — for
*every* `b : ℕ`, no `b ≤ f₁` guard needed. Consequently `resPoly` is literally `ψ` pushed
forward along the coefficient-field identification. -/
theorem frameKey_resPoly_eq_map (hπ : Irreducible π) {Φ' : Polynomial O} (hmonic : Φ'.Monic)
    {e₁ f₁ h : ℕ} (he₁ : 0 < e₁) (hf₁ : 0 < f₁) (hdeg : Φ'.natDegree = e₁ * f₁)
    (hcop : Nat.Coprime h e₁) (hpure : IsPure X Φ' h e₁) (hne : (sideSet X Φ' h e₁).Nonempty)
    (hpin : npHgt X Φ' (sideMin X Φ' h e₁ hne) = ((h * f₁ : ℕ) : ℕ∞)) :
    resPoly π X Φ' h e₁ hne (h * f₁) =
      (frameResidualPoly π Φ' h e₁ f₁).map (resFieldXEquiv O) := by
  have hcoeff : ∀ b, (resPoly π X Φ' h e₁ hne (h * f₁)).coeff b
      = (resFieldXEquiv O) (digAt π (h * (f₁ - b)) (Φ'.coeff (e₁ * b))) := by
    intro b
    have h1 := resPoly_coeff_of_pure hπ (monic_X (R := O))
      (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) hmonic (n := e₁ * f₁)
      (by rw [hdeg, Polynomial.natDegree_X, Nat.mul_one]) he₁ hcop hpure hne (h * f₁) b
    rw [h1, dev_X, ← Nat.mul_sub]
    show AdjoinRoot.mk ((X : Polynomial O).map (residue O))
        (digPoly π (h * (f₁ - b)) (Polynomial.C (Φ'.coeff (e₁ * b)))) = _
    rw [digPoly_C, AdjoinRoot.mk_C]
    exact (DFunLike.congr_fun (resFieldXEquiv_coe O) _).symm
  have hnd := frameKey_natDegree_resPoly hπ hmonic he₁ hdeg hcop hpure hne hpin
  refine Polynomial.ext fun b => ?_
  have hfc : (frameResidualPoly π Φ' h e₁ f₁).coeff b
      = if b < f₁ + 1 then digAt π (h * (f₁ - b)) (Φ'.coeff (e₁ * b)) else 0 := by
    unfold frameResidualPoly
    rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  rw [Polynomial.coeff_map, hfc]
  by_cases hb : b < f₁ + 1
  · rw [if_pos hb]; exact hcoeff b
  · rw [if_neg hb, map_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hnd]; omega)

/-! ## Obligation 4 — transporting `Irreducible` and `natDegree = f₁` -/

/-- **I1, obligation 4 — the full interface.** From a `KeyFrame.hresirr`-shaped hypothesis
(`C01.lean:98-100`, literally `F.hresirr` at the call site) plus the frame data, `ψ`
(`frameResidualPoly`) is irreducible of degree `f₁`. This is the theorem an eventual
`Uniformity.ChapC` consumer applies to `F.he₁ F.hf₁ F.hcop F.hmonic F.hdeg F.hpure F.hne
F.hresirr` to discharge INTERFACE I1. -/
theorem frameKey_scalarResidual_irreducible (hπ : Irreducible π) {Φ' : Polynomial O}
    (hmonic : Φ'.Monic) {e₁ f₁ h : ℕ} (he₁ : 0 < e₁) (hf₁ : 0 < f₁)
    (hdeg : Φ'.natDegree = e₁ * f₁) (hcop : Nat.Coprime h e₁) (hpure : IsPure X Φ' h e₁)
    (hne : (sideSet X Φ' h e₁).Nonempty)
    (hresirr : ∀ H₀ : ℕ, npHgt X Φ' (sideMin X Φ' h e₁ hne) = (H₀ : ℕ∞) →
      Irreducible (resPoly π X Φ' h e₁ hne H₀) ∧
        (resPoly π X Φ' h e₁ hne H₀).natDegree = f₁) :
    Irreducible (frameResidualPoly π Φ' h e₁ f₁) ∧
      (frameResidualPoly π Φ' h e₁ f₁).natDegree = f₁ := by
  have hpin := frameKey_hpin hmonic he₁ hdeg hpure hne
  obtain ⟨hirr, -⟩ := hresirr (h * f₁) hpin
  have heq := frameKey_resPoly_eq_map hπ hmonic he₁ hf₁ hdeg hcop hpure hne hpin
  rw [heq, ← Polynomial.mapEquiv_apply] at hirr
  refine ⟨(MulEquiv.irreducible_iff (Polynomial.mapEquiv (resFieldXEquiv O))).mp hirr, ?_⟩
  have hnd := frameKey_natDegree_resPoly hπ hmonic he₁ hdeg hcop hpure hne hpin
  rw [heq] at hnd
  rwa [Polynomial.natDegree_map_eq_of_injective
      (f := (resFieldXEquiv O : ResidueField O →+* resField (X : Polynomial O)))
      (RingEquiv.injective _)] at hnd

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.frameKey_sideGeometry
#print axioms Uniformity.Density.Leaf.frameKey_hpin
#print axioms Uniformity.Density.Leaf.frameKey_resPoly_eq_map
#print axioms Uniformity.Density.Leaf.frameKey_scalarResidual_irreducible
end AxCheck
