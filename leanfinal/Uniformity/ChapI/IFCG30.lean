/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG28
import Uniformity.ChapB.B33
import Uniformity.ChapB.B41b
import Uniformity.ChapI.IFCG16
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapI.IFCG30 — [XHS 2026-08-30] the x-frame coprime-residual block split

Stage XHS of the cone census (design record `runs/wave-c/verdict_XHS.md`).  CRL
(`IFCG26`) and WFR (`IFCG28`) converged on ONE named missing Hensel input: the x-frame
block split along a coprime factorization of the side residual (WFR's fence item 3;
C133mh `theoremA`'s x-frame sibling) and the x-frame unit-part Hensel coprime split
(CRL's fence item 3, `f̄ = X̄^μ·ū`).  Both fences claim corpus absence.  **The graded
half of that claim is FALSE**: `Uniformity.Density.Leaf.exists_graded_factorization`
(**B.41**, `ChapB/B41b.lean`, landed, Lean-core) is the one-slope coprime-residual split
at EVERY order-1 key — and `X` is an `IsKey`.  B41b sat off both consumers' import paths
(they import `ChapB.B42` only); C133mh14's own docstring calls Theorem A's conclusion
"B.41-shaped".  This file lands the x-frame instantiations, the class-level packaging,
and the consumer firings:

* **§1 ★ `exists_xframe_block_split`** (Lean-core): a monic `(u,ℓ)`-pure `f` at the
  x-frame whose side residual factors as `unit · (G · H)` with `G, H` monic coprime
  splits `f = g · h` LEVEL-EXACTLY: degrees `ℓ·deg G / ℓ·deg H`, both factors
  `(u,ℓ)`-pure, left heights `u·deg G / u·deg H`, and each factor carries EXACTLY its
  residual (`resPoly g = G`, `resPoly h = H`, ∀-pin form).  Proof: B.41 at `φ := X`.
  This is `C133mh14.TheoremAStatement`'s x-frame sibling (`F.e₁·F.f₁ ⇝ 1`,
  `dv* ⇝` the B-chapter x-frame reads).
* **§2 ★★ `exists_class_block_split`** (Lean-core): the CLASS-LEVEL split below the
  frame floor — a class `c` with a visible `(u,ℓ)` side attained at `0` and `m`
  (class-pure) whose class residual (read off ONE reference lift; class data by WFR §3's
  `resPoly_monicPoly_eq`) factors coprimely splits EVERY lift with the same `G, H` and
  the §1 pins.  Consumes WFR §3 verbatim, exactly as IFCG28 §3 was built for.
* **§3 ★ `exists_unitPart_factorization`** (Lean-core): CRL's fence statement verbatim —
  `f̄ = X̄^μ · ū` with `ū(0) ≠ 0` lifts to `f = g · h`, `ḡ = X̄^μ`, `h̄ = ū`, degrees
  pinned.  Proof: `IsCoprime (X^μ) ū` from `ū(0) ≠ 0` + the landed exact Hensel
  `Uniformity.Hensel.exists_monic_factorization`.  Plus
  `unitPart_factorization_level_exact` (IFCG16 §6 at the pair `(X̄^μ, ū)`): the strand
  split is stable mod `𝔪^N` under mod-`𝔪^N` perturbation of `f` — the strand's class
  is class data.
* **§4 ★★ `wideFace_refinement_of_stratum`** (Lean core + EXACTLY the signed B.42 cite):
  WFR's wide-face refinement law, fired at visible-corner stratum classes — a stratum
  class (`f̄ = X̄^m`) with visible corner, a visible class face `(u,ℓ)`, and class
  residual `G · H` coprime refines EVERY lift as `monicPoly a = g · h · R` with `g, h`
  monic `(u,ℓ)`-pure of degrees `ℓ·deg G / ℓ·deg H` carrying residuals EXACTLY `G, H`,
  and `R` monic (the other slopes' blocks).  Mechanism: B.42 clauses 5/6 dissect and tie
  the residual, WFR §3 transports the class factorization, §1 splits the block.
* **§5 ★ the polygon transfer across a unit-corner cofactor** (Lean-core):
  `suppVal_mul_unitCorner` / `onSide_mul_unitCorner_iff` — for `u > 0` and a cofactor
  `h` with `h(0)` a UNIT, `suppVal X (g·h) = suppVal X g` and the on-side abscissae
  agree exactly.  The weighted-Gauss multiplicativity at a flat cofactor: B.33 is the
  `≥` half; the `≤` half and the side identity are the first-minimal-index argument at
  the corner pair — `u > 0` prices every positive `h`-abscissa one level deeper, so the
  corner term alone carries the minimal valuation.
* **§6 ★★★ `fracFaceForcesRamStatement_holds`**: **IFCG23 §7's literal open Prop
  `FracFaceForcesRamStatement` is CLOSED** — arbitrary classes, general face position.
  Mechanism: §3 splits off the strand `g` with `ḡ = X̄^μ` (on-stratum by construction);
  §5 transfers the two class-face points from the lift to the strand; IFCG26 §2's
  Hensel heart splits off the pure factor; IFCG23's purity forcing reads off
  `e' ∣ ramIndexOf`.  This retires IFCG26's honest-fence item 1 ("the off-stratum
  statement is the named residue") and CRL/WFR's shared fence line 3/4.

## Axiom fence

§§1–3 and §5 are Lean core.  §4 and §6 consume exactly ONE extra axiom: the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42 — §6 inherits
it through IFCG26 §2's Hensel heart).  The C.33 (r = 1) cites do NOT occur; no ChapC
import.  Zero sorries at landing.

## The honest fence (what stays open after this file)

1. ~~CRL's off-stratum `FracFaceForcesRamStatement`~~ **CLOSED (§6)**.
2. The invisible-corner wide-face cells (`v₀ ≥ K`): §4 gates on corner visibility
   (B.42's `dev ≠ 0`); the class-level X-strip is WFR's fence item 2, another unit's.
3. The LEAF DECISION of the refined blocks (a pure block with IRREDUCIBLE residual of
   degree `≥ 2`): B.63's perimeter supply — untouched by this unit, as scoped.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG30

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classCoeffVal_exact exists_npAttains)
open Uniformity.Density.IFCG26 (mem_sideSet_of_onSide onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG28 (resPoly_monicPoly_eq)

attribute [local instance] Classical.propDecidable

/-! ## §0 — supply: the linear key, coprimality of `X^μ` with a unit-part -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- Over a field, `X^μ` is coprime to any polynomial with nonzero constant term
(the explicit Bézout pair from the `divX` decomposition). -/
theorem isCoprime_X_pow_of_coeff_zero_ne_zero {F : Type*} [Field F]
    {U : Polynomial F} (hU0 : U.coeff 0 ≠ 0) (μ : ℕ) :
    IsCoprime (X ^ μ : Polynomial F) U := by
  refine IsCoprime.pow_left ?_
  have hc : Polynomial.C (U.coeff 0)⁻¹ * Polynomial.C (U.coeff 0) = (1 : Polynomial F) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hU0, Polynomial.C_1]
  refine ⟨-(Polynomial.C (U.coeff 0)⁻¹ * U.divX), Polynomial.C (U.coeff 0)⁻¹, ?_⟩
  have h1 : U.divX * X + Polynomial.C (U.coeff 0) = U := Polynomial.divX_mul_X_add U
  linear_combination (-(Polynomial.C (U.coeff 0)⁻¹)) * h1 + hc

end Supply

/-! ## §1 — ★ the x-frame block split (B.41 at the linear key `X`) -/

section BlockSplit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- ★ **XHS — the x-frame coprime-residual block split** (`C133mh14.TheoremAStatement`'s
x-frame sibling; the named missing statement of the CRL/WFR fences): a monic
`(u,ℓ)`-pure `f` at the x-frame whose side residual polynomial factors as
`unit · (G · H)` with `G, H` monic coprime splits `f = g · h` level-exactly — degrees
`ℓ·deg G / ℓ·deg H`, both factors `(u,ℓ)`-pure with pinned left heights, each carrying
EXACTLY its prescribed residual (∀-pin form).  Proof: the landed Lean-core B.41
(`exists_graded_factorization`) at `φ := X`. -/
theorem exists_xframe_block_split {π : O} (hπ : Irreducible π) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O} (hf : f.Monic)
    (hpure : IsPure X f u ℓ) {H₀ : ℕ} (hH₀ : npHgt X f 0 = (H₀ : ℕ∞))
    (hne : (sideSet X f u ℓ).Nonempty)
    {G H : Polynomial (resField (X : Polynomial O))}
    (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hres : ∃ c : (resField (X : Polynomial O))ˣ,
      resPoly π X f u ℓ hne H₀
        = Polynomial.C (c : resField (X : Polynomial O)) * (G * H)) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = ℓ * G.natDegree ∧ h.natDegree = ℓ * H.natDegree ∧
      IsPure X g u ℓ ∧ IsPure X h u ℓ ∧ GradedCoprime π X u ℓ g h ∧
      npHgt X g 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
      npHgt X h 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
      (∀ hg' : (sideSet X g u ℓ).Nonempty,
        resPoly π X g u ℓ hg' (u * G.natDegree) = G) ∧
      (∀ hh' : (sideSet X h u ℓ).Nonempty,
        resPoly π X h u ℓ hh' (u * H.natDegree) = H) := by
  have hfd : (X : Polynomial O).natDegree ∣ f.natDegree := by
    rw [Polynomial.natDegree_X]
    exact one_dvd _
  obtain ⟨g, h, hg, hh, hgh, hgd, hhd, hgp, hhp, hgc, hgH, hhH, hgres, hhres⟩ :=
    exists_graded_factorization hπ isKey_X hu hℓ hcop hf hfd hpure hH₀ hne hG hH hGH hres
  refine ⟨g, h, hg, hh, hgh, ?_, ?_, hgp, hhp, hgc, hgH, hhH, hgres, hhres⟩
  · rw [hgd, Polynomial.natDegree_X, mul_one]
  · rw [hhd, Polynomial.natDegree_X, mul_one]

end BlockSplit

/-! ## §2 — ★★ the class-level split below the frame floor -/

section ClassSplit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **XHS — the CLASS-LEVEL x-frame block split** (the charge's literal statement):
a class `c` with a VISIBLE `(u,ℓ)` side attained at `0` and `m` (class-pure below the
frame floor) whose class residual polynomial — read off ONE reference lift `a₀`, class
data by WFR §3's `resPoly_monicPoly_eq` — factors as `G · H` with `G, H` monic coprime
splits EVERY lift `a` of `c` as `monicPoly a = g · h` with the §1 pins and THE SAME
residual factors `G, H`.  Lean-core. -/
theorem exists_class_block_split {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ)
    (h0 : NPAttains c u ℓ 0) (hm : NPAttains c u ℓ m)
    {a₀ : Fin m → O} (ha₀ : proj O m K a₀ = c)
    (hne₀ : (sideSet X (monicPoly a₀) u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X (monicPoly a₀) (sideMin X (monicPoly a₀) u ℓ hne₀) = (H₀ : ℕ∞))
    {G H : Polynomial (resField (X : Polynomial O))}
    (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hres : resPoly π X (monicPoly a₀) u ℓ hne₀ H₀ = G * H)
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ monicPoly a = g * h ∧
      g.natDegree = ℓ * G.natDegree ∧ h.natDegree = ℓ * H.natDegree ∧
      IsPure X g u ℓ ∧ IsPure X h u ℓ ∧
      npHgt X g 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
      npHgt X h 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
      (∀ hg' : (sideSet X g u ℓ).Nonempty,
        resPoly π X g u ℓ hg' (u * G.natDegree) = G) ∧
      (∀ hh' : (sideSet X h u ℓ).Nonempty,
        resPoly π X h u ℓ hh' (u * H.natDegree) = H) := by
  -- STEP 1: every lift of the class-pure side is (u,ℓ)-pure (IFCG26 §1's bridge).
  obtain ⟨hO0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ hℓ hvis h0 ha
  obtain ⟨hOm, -⟩ := onSide_monicPoly_of_npAttains hπ hℓ hvis hm ha
  have hpure : IsPure X (monicPoly a) u ℓ := by
    refine ⟨hO0, ?_⟩
    have hidx : (monicPoly a).natDegree / (X : Polynomial O).natDegree = m := by
      rw [monicPoly_natDegree, Polynomial.natDegree_X, Nat.div_one]
    rw [hidx]
    exact hOm
  -- STEP 2: the lift's left height is pinned and finite below the floor.
  have hnea : (sideSet X (monicPoly a) u ℓ).Nonempty :=
    sideSet_nonempty_gen X (monicPoly a) u ℓ
  have hmina : sideMin X (monicPoly a) u ℓ hnea = 0 := sideMin_of_pure hpure hnea
  have hfin : npHgt X (monicPoly a) 0 ≠ ⊤ := by
    intro htop
    have h9 : ℓ • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) u ℓ := hO0
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0),
      top_add, hsupp] at h9
    exact (ENat.coe_ne_top _) h9.symm
  obtain ⟨Ha, hHa⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hHa0 : npHgt X (monicPoly a) 0 = ((Ha : ℕ) : ℕ∞) := hHa.symm
  have hHamin : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hnea)
      = ((Ha : ℕ) : ℕ∞) := by
    rw [hmina]
    exact hHa0
  -- STEP 3: WFR §3 transports the class residual factorization to the lift `a`.
  obtain ⟨hHeq, hreq⟩ := resPoly_monicPoly_eq hπ hℓ hvis ha₀ ha hne₀ hnea hH₀ hHamin
  -- STEP 4: fire the §1 block split at the lift.
  obtain ⟨g, h, hg, hh, hgh, hgd, hhd, hgp, hhp, -, hgH, hhH, hgres, hhres⟩ :=
    exists_xframe_block_split hπ hu hℓ hcop (monicPoly_monic a) hpure hHa0 hnea hG hH hGH
      ⟨1, by rw [← hreq, hres, Units.val_one, Polynomial.C_1, one_mul]⟩
  exact ⟨g, h, hg, hh, hgh, hgd, hhd, hgp, hhp, hgH, hhH, hgres, hhres⟩

end ClassSplit

/-! ## §3 — ★ the unit-part Hensel split (CRL's fence statement) -/

section UnitPart

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- ★ **XHS — the x-frame unit-part Hensel coprime split** (CRL's fence item 3,
verbatim): a monic `f` with `f̄ = X̄^μ · ū`, `ū(0) ≠ 0`, factors compatibly —
`f = g · h` with `g, h` monic, `ḡ = X̄^μ`, `h̄ = ū`, degrees pinned.  Proof: the
residue-level coprimality `IsCoprime (X^μ) ū` + the landed exact Hensel
(`Uniformity.Hensel.exists_monic_factorization`).  Lean-core. -/
theorem exists_unitPart_factorization {f : Polynomial O} (hf : f.Monic) {μ : ℕ}
    {U : Polynomial (ResidueField O)} (hU : U.Monic) (hU0 : U.coeff 0 ≠ 0)
    (hres : f.map (residue O) = X ^ μ * U) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue O) = X ^ μ ∧ h.map (residue O) = U ∧
      g.natDegree = μ ∧ h.natDegree = U.natDegree := by
  have hcop : IsCoprime (X ^ μ : Polynomial (ResidueField O)) U :=
    isCoprime_X_pow_of_coeff_zero_ne_zero hU0 μ
  obtain ⟨g, h, hg, hh, hgh, hgr, hhr, hgd, hhd⟩ :=
    Uniformity.Hensel.exists_monic_factorization_dvr O hf (Polynomial.monic_X_pow μ)
      hU hcop hres
  refine ⟨g, h, hg, hh, hgh, hgr, hhr, ?_, hhd⟩
  rw [hgd, Polynomial.natDegree_X_pow]

/-- The unit-part split is LEVEL-EXACT (IFCG16 §6's finite-precision Hensel uniqueness
at the coprime pair `(X̄^μ, ū)`): two monic strand/unit-part pairs with the same
reductions whose products agree mod `𝔪^N` agree factorwise mod `𝔪^N` — the strand's
level-`N` class is a function of `f`'s level-`N` class.  Lean-core. -/
theorem unitPart_factorization_level_exact {π : O} (hπ : Irreducible π) {N : ℕ}
    (hN : 1 ≤ N) {g g' h h' : Polynomial O}
    (hg : g.Monic) (hg' : g'.Monic) (hh : h.Monic) (hh' : h'.Monic)
    {μ : ℕ} {U : Polynomial (ResidueField O)} (hU0 : U.coeff 0 ≠ 0)
    (hgr : g.map (residue O) = X ^ μ) (hgr' : g'.map (residue O) = X ^ μ)
    (hhr : h.map (residue O) = U) (hhr' : h'.map (residue O) = U)
    (hprod : g * h - g' * h' ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ N)) :
    g - g' ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ N) ∧
      h - h' ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ N) := by
  have hcop : IsCoprime (g.map (residue O)) (h.map (residue O)) := by
    rw [hgr, hhr]
    exact isCoprime_X_pow_of_coeff_zero_ne_zero hU0 μ
  have hdegg : g'.natDegree = g.natDegree := by
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq hg' hgr',
      Uniformity.Hensel.natDegree_eq_of_map_eq hg hgr]
  have hdegh : h'.natDegree = h.natDegree := by
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq hh' hhr',
      Uniformity.Hensel.natDegree_eq_of_map_eq hh hhr]
  exact Uniformity.Density.IFCG16.factor_sub_mem_of_mul_sub_mem hπ hN hg hg' hh hh'
    hdegg hdegh (hgr'.trans hgr.symm) (hhr'.trans hhr.symm) hcop hprod

end UnitPart

/-! ## §4 — ★★ the wide-face refinement law at visible-corner stratum classes -/

section WideFace

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **XHS — the wide-face refinement law** (WFR's fence item 3, fired at
visible-corner stratum classes): a stratum class (`f̄ = X̄^m`) with VISIBLE corner
(`v₀ < K`), a visible class NP face of slope `u/ℓ`, and class-side residual factoring
as `G · H` with `G, H` monic coprime (read off a reference lift — class data by WFR §3)
refines EVERY lift as `monicPoly a = g · h · R`: `g, h` monic `(u,ℓ)`-pure of degrees
`ℓ·deg G / ℓ·deg H` with pinned left heights carrying residuals EXACTLY `G` and `H`,
`R` monic (the other slopes' blocks).  Consumes B.42 (clauses 5/6) + WFR §3 + §1. -/
theorem wideFace_refinement_of_stratum {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ}
    (hm0 : 0 < m) (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {c : Coeff O m K} (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (hcorner : classCoeffVal c ⟨0, hm0⟩ < K)
    (hface : ClassNPFace c u ℓ) (hvis : NPVisibleAt c u ℓ)
    {a₀ : Fin m → O} (ha₀ : proj O m K a₀ = c)
    (hne₀ : (sideSet X (monicPoly a₀) u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X (monicPoly a₀) (sideMin X (monicPoly a₀) u ℓ hne₀) = (H₀ : ℕ∞))
    {G H : Polynomial (resField (X : Polynomial O))}
    (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hres : resPoly π X (monicPoly a₀) u ℓ hne₀ H₀ = G * H)
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ g h R : Polynomial O, g.Monic ∧ h.Monic ∧ R.Monic ∧
      monicPoly a = g * h * R ∧
      g.natDegree = ℓ * G.natDegree ∧ h.natDegree = ℓ * H.natDegree ∧
      IsPure X g u ℓ ∧ IsPure X h u ℓ ∧
      npHgt X g 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
      npHgt X h 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
      (∀ hg' : (sideSet X g u ℓ).Nonempty,
        resPoly π X g u ℓ hg' (u * G.natDegree) = G) ∧
      (∀ hh' : (sideSet X h u ℓ).Nonempty,
        resPoly π X h u ℓ hh' (u * H.natDegree) = H) := by
  -- STEP 0: the lift's stratum reduction and the visible corner.
  have hfres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hstr a ha
  have hdev : dev X (monicPoly a) 0 ≠ 0 := by
    rw [dev_X]
    intro hC
    have hc0 : (monicPoly a).coeff 0 = 0 := by simpa using hC
    rw [monicPoly_coeff_lt a hm0] at hc0
    obtain ⟨-, hnd⟩ := classCoeffVal_exact hπ ha hcorner
    exact hnd (by rw [hc0]; exact dvd_zero _)
  -- STEP 1: B.42 dissects the lift (the ONE cite consumption).
  have hdeg0 : 0 < (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hm0
  obtain ⟨s, F, hs1, hs2, hs3, hprod, hs5, hs6⟩ :=
    exists_slope_factorization (μ := (monicPoly a).natDegree) hπ isKey_X
      (monicPoly_monic a) hdeg0 (by rw [Polynomial.map_X]; exact hfres) hdev
  -- STEP 2: the class face puts `(u, ℓ)` in the slope set.
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  obtain ⟨hOi, hsupp⟩ := onSide_monicPoly_of_npAttains hπ hℓ hvis hAi ha
  obtain ⟨hOj, -⟩ := onSide_monicPoly_of_npAttains hπ hℓ hvis hAj ha
  have hid : i ≤ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hAi.1
  have hjd : j ≤ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hAj.1
  have hmem : (u, ℓ) ∈ s := by
    refine (hs5 u ℓ hℓ hcop).1 ?_
    exact Finset.one_lt_card.mpr
      ⟨i, mem_sideSet_of_onSide hid hOi, j, mem_sideSet_of_onSide hjd hOj, by omega⟩
  -- STEP 3: the block at `(u, ℓ)` and its data.
  obtain ⟨hFm, hFpure, hFdvd, -, -⟩ := hs3 (u, ℓ) hmem
  -- STEP 4a: the lift's height at its sideMin is pinned and finite.
  have hnea : (sideSet X (monicPoly a) u ℓ).Nonempty :=
    sideSet_nonempty_gen X (monicPoly a) u ℓ
  have hfina : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hnea) ≠ ⊤ := by
    intro htop
    have hOmin : OnSide X (monicPoly a) u ℓ (sideMin X (monicPoly a) u ℓ hnea) :=
      onSide_of_mem_sideSet (Finset.min'_mem _ _)
    have h9 : ℓ • npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hnea)
        + ((u * sideMin X (monicPoly a) u ℓ hnea : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) u ℓ := hOmin
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0),
      top_add, hsupp] at h9
    exact (ENat.coe_ne_top _) h9.symm
  obtain ⟨Ha, hHa⟩ := WithTop.ne_top_iff_exists.mp hfina
  have hHamin : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hnea)
      = ((Ha : ℕ) : ℕ∞) := hHa.symm
  -- STEP 4b: the block is pure, so its left height at 0 is pinned and finite.
  have hneF : (sideSet X (F (u, ℓ)) u ℓ).Nonempty :=
    sideSet_nonempty_gen X (F (u, ℓ)) u ℓ
  have hFdeg0 : (F (u, ℓ)).natDegree
      = ((F (u, ℓ)).natDegree / (X : Polynomial O).natDegree) * (X : Polynomial O).natDegree :=
    (Nat.div_mul_cancel hFdvd).symm
  have hFtop : suppVal X (F (u, ℓ)) u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure Polynomial.monic_X (by simp) hFm hFdeg0 hFpure]
    exact ENat.coe_ne_top _
  have hminF : sideMin X (F (u, ℓ)) u ℓ hneF = 0 := sideMin_of_pure hFpure hneF
  have hfinF : npHgt X (F (u, ℓ)) 0 ≠ ⊤ := by
    intro htop
    have h9 : ℓ • npHgt X (F (u, ℓ)) 0 + ((u * 0 : ℕ) : ℕ∞)
        = suppVal X (F (u, ℓ)) u ℓ := hFpure.1
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0),
      top_add] at h9
    exact hFtop h9.symm
  obtain ⟨HF, hHF⟩ := WithTop.ne_top_iff_exists.mp hfinF
  have hHF0 : npHgt X (F (u, ℓ)) 0 = ((HF : ℕ) : ℕ∞) := hHF.symm
  have hHFmin : npHgt X (F (u, ℓ)) (sideMin X (F (u, ℓ)) u ℓ hneF)
      = ((HF : ℕ) : ℕ∞) := by
    rw [hminF]
    exact hHF0
  -- STEP 5: B.42 clause 6 ties the block's residual to the lift's; WFR §3 transports
  -- the class factorization to the lift.
  obtain ⟨cu, hcu⟩ := hs6 (u, ℓ) hmem hnea hneF Ha HF hHamin hHFmin
  obtain ⟨-, hreq⟩ := resPoly_monicPoly_eq hπ hℓ hvis ha₀ ha hne₀ hnea hH₀ hHamin
  have h2 : resPoly π X (monicPoly a) u ℓ hnea Ha = G * H := by
    rw [← hreq, hres]
  have h3 : G * H
      = Polynomial.C ((cu : resField (X : Polynomial O)))
        * resPoly π X (F (u, ℓ)) u ℓ hneF HF := h2.symm.trans hcu
  -- STEP 6: §1 splits the block along the transported coprime factorization.
  obtain ⟨g, h, hg, hh, hgh, hgd, hhd, hgp, hhp, -, hgH, hhH, hgres, hhres⟩ :=
    exists_xframe_block_split hπ hu hℓ hcop hFm hFpure hHF0 hneF hG hH hGH
      ⟨cu⁻¹, by
        rw [h3, ← mul_assoc, ← Polynomial.C_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Polynomial.C_1, one_mul]⟩
  refine ⟨g, h, ∏ p ∈ s.erase (u, ℓ), F p, hg, hh,
    Polynomial.monic_prod_of_monic _ _
      (fun p hp => (hs3 p (Finset.mem_of_mem_erase hp)).1),
    ?_, hgd, hhd, hgp, hhp, hgH, hhH, hgres, hhres⟩
  rw [hprod, ← Finset.mul_prod_erase s F hmem, hgh]

end WideFace

/-! ## §5 — the polygon transfer across a unit-corner cofactor -/

section Transfer

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- ℕ∞ division helper: `ℓ·n + 1 ≤ ℓ·v` forces `n + 1 ≤ v`. -/
private theorem succ_le_of_cast_le_nsmul {v : ℕ∞} {ℓ n : ℕ}
    (h : ((ℓ * n + 1 : ℕ) : ℕ∞) ≤ ℓ • v) : ((n + 1 : ℕ) : ℕ∞) ≤ v := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · exact le_top
  · obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hv
    have hw' : ((w : ℕ) : ℕ∞) = v := hw
    rw [← hw'] at h ⊢
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] at h
    rw [Nat.cast_le]
    have h2 : ℓ * n < ℓ * w := by omega
    exact Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left h2)

/-- Every abscissa (including those beyond the degree) is weighted-above the support. -/
private theorem suppVal_le_weighted {u ℓ : ℕ} (hℓ : 0 < ℓ) (f : Polynomial O) (j : ℕ) :
    suppVal X f u ℓ ≤ ℓ • npHgt X f j + ((u * j : ℕ) : ℕ∞) := by
  rcases Nat.lt_or_ge f.natDegree j with hj | hj
  · have h1 : npHgt X f j = ⊤ := by
      rw [npHgt_X, Polynomial.coeff_eq_zero_of_natDegree_lt hj,
        IsDiscreteValuationRing.addVal_zero]
    rw [h1, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0), top_add]
    exact le_top
  · have hS : suppVal X f u ℓ = (Finset.range (f.natDegree + 1)).inf
        (fun t => ℓ • npHgt X f t + ((u * t : ℕ) : ℕ∞)) := rfl
    rw [hS]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))

/-- The x-frame support of a monic polynomial is finite (the monic point caps it). -/
private theorem suppVal_ne_top_of_monic {u ℓ : ℕ} (hℓ : 0 < ℓ) {f : Polynomial O}
    (hf : f.Monic) : suppVal X f u ℓ ≠ ⊤ := by
  have h1 := suppVal_le_weighted (u := u) hℓ f f.natDegree
  have h2 : npHgt X f f.natDegree = 0 := by
    rw [npHgt_X, hf.coeff_natDegree, IsDiscreteValuationRing.addVal_one]
  rw [h2, smul_zero, zero_add] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1

/-- **The exact-height transfer** (the first-minimal-index argument at the corner pair):
at an on-side abscissa of `g`, multiplying by a cofactor with UNIT corner (`h(0)` a
unit) does not move the height — every off-corner term of the product coefficient is
one level deeper because `u > 0` prices every positive `h`-abscissa. -/
private theorem npHgt_mul_of_onSide {π : O} (hπ : Irreducible π) {g h : Polynomial O}
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hh0 : IsUnit (h.coeff 0))
    {S : ℕ} (hS : suppVal X g u ℓ = (S : ℕ∞)) {j : ℕ} (hOj : OnSide X g u ℓ j) :
    npHgt X (g * h) j = npHgt X g j := by
  have hOj' : ℓ • npHgt X g j + ((u * j : ℕ) : ℕ∞) = ((S : ℕ) : ℕ∞) := by
    rw [← hS]
    exact hOj
  have hfin : npHgt X g j ≠ ⊤ := by
    intro htop
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0),
      top_add] at hOj'
    exact (ENat.coe_ne_top S) hOj'.symm
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hn' : ((n : ℕ) : ℕ∞) = npHgt X g j := hn
  have hSn : ℓ * n + u * j = S := by
    rw [← hn', nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at hOj'
    exact Nat.cast_inj.mp hOj'
  have hvg : IsDiscreteValuationRing.addVal O (g.coeff j) = (n : ℕ∞) := by
    rw [← npHgt_X, ← hn']
  have hdj : π ^ n ∣ g.coeff j :=
    (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 (by rw [hvg])
  have hndj : ¬ π ^ (n + 1) ∣ g.coeff j := by
    intro hdvd
    have h2 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hdvd
    rw [hvg, Nat.cast_le] at h2
    omega
  -- every off-corner term is one level deeper
  have hrest : ∀ pq ∈ (Finset.antidiagonal j).erase (j, 0),
      π ^ (n + 1) ∣ g.coeff pq.1 * h.coeff pq.2 := by
    intro pq hpq
    obtain ⟨hne', hmem⟩ := Finset.mem_erase.mp hpq
    obtain ⟨p, q⟩ := pq
    have hsum : p + q = j := Finset.mem_antidiagonal.mp hmem
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h0
      · exfalso
        apply hne'
        have hpj : p = j := by omega
        subst hpj
        rfl
      · exact h0
    have hwb := suppVal_le_weighted (u := u) hℓ g p
    rw [hS] at hwb
    have harith : ℓ * n + 1 + u * p ≤ S := by
      have h3 : u * p + u ≤ u * j := by
        have h4 : p + 1 ≤ j := by omega
        calc u * p + u = u * (p + 1) := by ring
          _ ≤ u * j := Nat.mul_le_mul (le_refl u) h4
      omega
    have h4 : ((ℓ * n + 1 : ℕ) : ℕ∞) + ((u * p : ℕ) : ℕ∞)
        ≤ ℓ • npHgt X g p + ((u * p : ℕ) : ℕ∞) := by
      refine le_trans ?_ hwb
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr (by omega)
    have h5 := (ENat.add_le_add_iff_right (ENat.coe_ne_top _)).1 h4
    have h6 := succ_le_of_cast_le_nsmul h5
    have h7 : π ^ (n + 1) ∣ g.coeff p := by
      refine (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 ?_
      rw [← npHgt_X]
      exact h6
    exact h7.mul_right _
  have hmem0 : ((j, 0) : ℕ × ℕ) ∈ Finset.antidiagonal j :=
    Finset.mem_antidiagonal.mpr (add_zero j)
  have hsplit : ∑ pq ∈ (Finset.antidiagonal j).erase (j, 0), g.coeff pq.1 * h.coeff pq.2
      + g.coeff j * h.coeff 0 = (g * h).coeff j := by
    rw [Polynomial.coeff_mul]
    exact Finset.sum_erase_add _ _ hmem0
  have hd1 : π ^ n ∣ (g * h).coeff j := by
    rw [← hsplit]
    refine dvd_add (Finset.dvd_sum fun pq hpq => ?_) (hdj.mul_right _)
    exact (pow_dvd_pow π (Nat.le_succ n)).trans (hrest pq hpq)
  have hd2 : ¬ π ^ (n + 1) ∣ (g * h).coeff j := by
    intro hdvd
    have h8 : π ^ (n + 1) ∣ g.coeff j * h.coeff 0 := by
      have h9 : g.coeff j * h.coeff 0 = (g * h).coeff j
          - ∑ pq ∈ (Finset.antidiagonal j).erase (j, 0), g.coeff pq.1 * h.coeff pq.2 := by
        rw [← hsplit]
        ring
      rw [h9]
      exact dvd_sub hdvd (Finset.dvd_sum hrest)
    obtain ⟨w, hw⟩ := hh0.exists_right_inv
    have h10 : g.coeff j = g.coeff j * h.coeff 0 * w := by
      rw [mul_assoc, hw, mul_one]
    exact hndj (by rw [h10]; exact h8.mul_right w)
  rw [npHgt_X, npHgt_X, Uniformity.Density.IFCG23.addVal_eq_of_pow_dvd_not_dvd hπ hd1 hd2]
  exact hvg.symm

/-- ★ **The support transfer across a unit-corner cofactor**: for `u > 0`, multiplying a
monic `g` by any `h` whose constant coefficient is a UNIT leaves the x-frame support
value unchanged — the weighted Gauss multiplicativity at a flat cofactor (B.33 is the
`≥` half; the `≤` half is the corner-pair exactness above). -/
theorem suppVal_mul_unitCorner {π : O} (hπ : Irreducible π) {g h : Polynomial O}
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hg : g.Monic) (hh0 : IsUnit (h.coeff 0)) :
    suppVal X (g * h) u ℓ = suppVal X g u ℓ := by
  obtain ⟨S, hS'⟩ := WithTop.ne_top_iff_exists.mp
    (suppVal_ne_top_of_monic (u := u) hℓ hg)
  have hS : suppVal X g u ℓ = ((S : ℕ) : ℕ∞) := hS'.symm
  obtain ⟨j, hjmem⟩ := sideSet_nonempty_gen X g u ℓ
  have hOj : OnSide X g u ℓ j := onSide_of_mem_sideSet hjmem
  have hHeq := npHgt_mul_of_onSide hπ hu hℓ hh0 hS hOj
  have hge : suppVal X g u ℓ ≤ suppVal X (g * h) u ℓ := by
    have h1 := suppVal_add_le_suppVal_mul hπ Polynomial.monic_X (by simp) hℓ u g h
    exact le_trans le_self_add h1
  have hle : suppVal X (g * h) u ℓ ≤ ((S : ℕ) : ℕ∞) := by
    have h2 := suppVal_le_weighted (u := u) hℓ (g * h) j
    rw [hHeq] at h2
    have h3 : ℓ • npHgt X g j + ((u * j : ℕ) : ℕ∞) = ((S : ℕ) : ℕ∞) := by
      rw [← hS]
      exact hOj
    rwa [h3] at h2
  rw [hS]
  exact le_antisymm hle (by rw [← hS]; exact hge)

/-- ★ **The side transfer across a unit-corner cofactor**: for `u > 0`, the on-side
abscissae of `g · h` at slope `(u, ℓ)` are EXACTLY those of `g` whenever `h`'s corner is
a unit — the polygon's negative part does not see the unit cofactor.  This is the named
missing leg of CRL's off-stratum program (IFCG26's honest fence, item 1). -/
theorem onSide_mul_unitCorner_iff {π : O} (hπ : Irreducible π) {g h : Polynomial O}
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hg : g.Monic) (hh0 : IsUnit (h.coeff 0))
    (j : ℕ) : OnSide X (g * h) u ℓ j ↔ OnSide X g u ℓ j := by
  obtain ⟨S, hS'⟩ := WithTop.ne_top_iff_exists.mp
    (suppVal_ne_top_of_monic (u := u) hℓ hg)
  have hS : suppVal X g u ℓ = ((S : ℕ) : ℕ∞) := hS'.symm
  have hsupp := suppVal_mul_unitCorner (u := u) (ℓ := ℓ) hπ hu hℓ hg hh0
  constructor
  · intro hO
    have hO' : ℓ • npHgt X (g * h) j + ((u * j : ℕ) : ℕ∞) = ((S : ℕ) : ℕ∞) := by
      rw [← hS, ← hsupp]
      exact hO
    have hfin : npHgt X (g * h) j ≠ ⊤ := by
      intro htop
      rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0),
        top_add] at hO'
      exact (ENat.coe_ne_top S) hO'.symm
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hn' : ((n : ℕ) : ℕ∞) = npHgt X (g * h) j := hn
    have hSn : ℓ * n + u * j = S := by
      rw [← hn', nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at hO'
      exact Nat.cast_inj.mp hO'
    by_contra hng
    -- strictness at the corner: `j` misses `g`'s side by at least one level
    have hwj := suppVal_le_weighted (u := u) hℓ g j
    rw [hS] at hwj
    have hstrict : ((S + 1 : ℕ) : ℕ∞) ≤ ℓ • npHgt X g j + ((u * j : ℕ) : ℕ∞) := by
      rcases lt_or_eq_of_le hwj with hlt | heq
      · have h1 := Order.add_one_le_of_lt hlt
        rwa [← Nat.cast_one, ← Nat.cast_add] at h1
      · exact absurd (show OnSide X g u ℓ j by
          show ℓ • npHgt X g j + ((u * j : ℕ) : ℕ∞) = suppVal X g u ℓ
          rw [hS]
          exact heq.symm) hng
    -- every antidiagonal term is one level deeper than `n`
    have hall : ∀ pq ∈ Finset.antidiagonal j,
        π ^ (n + 1) ∣ g.coeff pq.1 * h.coeff pq.2 := by
      intro pq hmem
      obtain ⟨p, q⟩ := pq
      have hsum : p + q = j := Finset.mem_antidiagonal.mp hmem
      rcases Nat.eq_zero_or_pos q with rfl | hqpos
      · -- the corner pair rides the strictness
        have hpj : p = j := by omega
        subst hpj
        have h4 : ((ℓ * n + 1 : ℕ) : ℕ∞) + ((u * p : ℕ) : ℕ∞)
            ≤ ℓ • npHgt X g p + ((u * p : ℕ) : ℕ∞) := by
          refine le_trans ?_ hstrict
          rw [← Nat.cast_add]
          exact Nat.cast_le.mpr (by omega)
        have h5 := (ENat.add_le_add_iff_right (ENat.coe_ne_top _)).1 h4
        have h6 := succ_le_of_cast_le_nsmul h5
        have h7 : π ^ (n + 1) ∣ g.coeff p := by
          refine (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 ?_
          rw [← npHgt_X]
          exact h6
        exact h7.mul_right _
      · -- positive `h`-abscissa is priced by `u > 0`
        have hwb := suppVal_le_weighted (u := u) hℓ g p
        rw [hS] at hwb
        have harith : ℓ * n + 1 + u * p ≤ S := by
          have h3 : u * p + u ≤ u * j := by
            have h4 : p + 1 ≤ j := by omega
            calc u * p + u = u * (p + 1) := by ring
              _ ≤ u * j := Nat.mul_le_mul (le_refl u) h4
          omega
        have h4 : ((ℓ * n + 1 : ℕ) : ℕ∞) + ((u * p : ℕ) : ℕ∞)
            ≤ ℓ • npHgt X g p + ((u * p : ℕ) : ℕ∞) := by
          refine le_trans ?_ hwb
          rw [← Nat.cast_add]
          exact Nat.cast_le.mpr (by omega)
        have h5 := (ENat.add_le_add_iff_right (ENat.coe_ne_top _)).1 h4
        have h6 := succ_le_of_cast_le_nsmul h5
        have h7 : π ^ (n + 1) ∣ g.coeff p := by
          refine (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 ?_
          rw [← npHgt_X]
          exact h6
        exact h7.mul_right _
    have hdvd : π ^ (n + 1) ∣ (g * h).coeff j := by
      rw [Polynomial.coeff_mul]
      exact Finset.dvd_sum hall
    have h8 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hdvd
    rw [← npHgt_X, ← hn', Nat.cast_le] at h8
    omega
  · intro hO
    have hHeq := npHgt_mul_of_onSide hπ hu hℓ hh0 hS hO
    show ℓ • npHgt X (g * h) j + ((u * j : ℕ) : ℕ∞) = suppVal X (g * h) u ℓ
    rw [hHeq, hsupp]
    exact hO

end Transfer

/-! ## §6 — ★★★ the CLOSURE of IFCG23 §7's `FracFaceForcesRamStatement` -/

section Closure

/-- ★★★ **XHS — `FracFaceForcesRamStatement` HOLDS** (IFCG23 §7's literal open Prop,
arbitrary classes, general face position): a visible class NP face of fractional slope
`h/e'` (`e' ≥ 2`, coprime) ANYWHERE on the polygon of ANY class forces a monic
irreducible factor with `e' ∣ ramIndexOf` in every lift.  Mechanism: the unit-part
split (§3) puts the strand `g` (`ḡ = X̄^μ`) on the stratum; the §5 side transfer moves
the two face points from the lift to the strand (the unit cofactor is invisible to the
polygon's negative part); IFCG26 §2's Hensel heart splits off the pure factor; IFCG23's
purity forcing reads off the ramification.  Footprint: Lean core + exactly the signed
B.42 cite (inherited through IFCG26 §2). -/
theorem fracFaceForcesRamStatement_holds :
    Uniformity.Density.IFCG23.FracFaceForcesRamStatement := by
  intro O _ _ _ _ _ m N sh e' he' hcop c hface hvis a ha
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have he'0 : 0 < e' := by omega
  have hsh : 0 < sh := by
    rcases Nat.eq_zero_or_pos sh with rfl | hpos
    · exfalso
      have h1 : e' = 1 := by
        have h2 := hcop
        rwa [Nat.coprime_zero_left] at h2
      omega
    · exact hpos
  -- the two class-face points are lift-`OnSide` (IFCG26 §1, no stratum hypothesis)
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  obtain ⟨hOfi, -⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAi ha
  obtain ⟨hOfj, -⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAj ha
  -- the unit-part split of the lift (§3 at the reduction's `X`-multiplicity)
  have hfm : (monicPoly a).Monic := monicPoly_monic a
  have hf0 : (monicPoly a).map (residue O) ≠ 0 := (hfm.map (residue O)).ne_zero
  obtain ⟨U, hU, hUnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    ((monicPoly a).map (residue O)) hf0 0
  rw [Polynomial.C_0, sub_zero] at hU hUnd
  have hUm : U.Monic := (Polynomial.monic_X_pow _).of_mul_monic_left
    (by rw [← hU]; exact hfm.map (residue O))
  have hU0 : U.coeff 0 ≠ 0 := by
    intro h0
    exact hUnd (Polynomial.X_dvd_iff.mpr h0)
  obtain ⟨g, w, hgm, hwm, hgw, hgr, hwr, hgd, hwd⟩ :=
    exists_unitPart_factorization hfm hUm hU0 hU
  -- the cofactor's corner is a unit
  have hw0 : IsUnit (w.coeff 0) := by
    have h1 : residue O (w.coeff 0) = U.coeff 0 := by
      rw [← hwr, Polynomial.coeff_map]
    by_contra hnu
    have h2 : w.coeff 0 ∈ maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    exact hU0 (by rw [← h1]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h2)
  -- transfer both face points across the split (§5)
  rw [hgw] at hOfi hOfj
  have hOgi : OnSide X g sh e' i :=
    (onSide_mul_unitCorner_iff hπ hsh he'0 hgm hw0 i).1 hOfi
  have hOgj : OnSide X g sh e' j :=
    (onSide_mul_unitCorner_iff hπ hsh he'0 hgm hw0 j).1 hOfj
  have htop : suppVal X g sh e' ≠ ⊤ := suppVal_ne_top_of_monic he'0 hgm
  -- `j` lies within the strand's degree range (its height is finite on the side)
  have hjd : j ≤ g.natDegree := by
    by_contra hgt
    have h1 : npHgt X g j = ⊤ := by
      rw [npHgt_X, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        IsDiscreteValuationRing.addVal_zero]
    have h2 : e' • npHgt X g j + ((sh * j : ℕ) : ℕ∞) = suppVal X g sh e' := hOgj
    rw [h1, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast he'0.ne' : (e' : ℕ∞) ≠ 0),
      top_add] at h2
    exact htop h2.symm
  -- the strand is on-stratum; IFCG26 §2's Hensel heart splits off the pure factor
  have hgres : g.map (residue O) = X ^ g.natDegree := by
    rw [hgr, hgd]
  obtain ⟨FF, RR, hFFm, hRRm, hFFp, hFFd, hFR⟩ :=
    Uniformity.Density.IFCG26.exists_pure_factor_of_two_point_side hπ hgm hgres hsh he'0
      hcop hij hjd hOgi hOgj htop
  obtain ⟨g', hg'⟩ := Uniformity.Density.IFCG26.exists_mem_monicFactors hFFm hFFd
  refine ⟨g', ?_,
    Uniformity.Density.IFCG23.dvd_ramIndexOf_of_isPure hπ he'0 hcop hFFm hFFp hg'⟩
  rw [hgw, hFR, monicFactors_mul (hFFm.mul hRRm) hwm, monicFactors_mul hFFm hRRm]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hg')))

end Closure

end Uniformity.Density.IFCG30

end

/-! ## AXCHECK FOOTER — §§1–3 expect Lean core `{propext, Classical.choice, Quot.sound}`;
§4 expects Lean core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG30.isCoprime_X_pow_of_coeff_zero_ne_zero
#print axioms Uniformity.Density.IFCG30.exists_xframe_block_split
#print axioms Uniformity.Density.IFCG30.exists_class_block_split
#print axioms Uniformity.Density.IFCG30.exists_unitPart_factorization
#print axioms Uniformity.Density.IFCG30.unitPart_factorization_level_exact
#print axioms Uniformity.Density.IFCG30.wideFace_refinement_of_stratum
#print axioms Uniformity.Density.IFCG30.suppVal_mul_unitCorner
#print axioms Uniformity.Density.IFCG30.onSide_mul_unitCorner_iff
#print axioms Uniformity.Density.IFCG30.fracFaceForcesRamStatement_holds
