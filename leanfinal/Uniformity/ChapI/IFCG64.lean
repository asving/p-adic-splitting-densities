/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG36
import Uniformity.ChapI.IFCG62

/-!
# Uniformity.ChapI.IFCG64 — UNIT MFL: the mixed-frame instruments — the `(h, 1)`
cell/box/count layer at the base ring, and the compositum cell transport

**UNIT MFL** (wave C, 2026-08-31; design record `runs/wave-c/verdict_MFL.md`).
EFR (`IFCG62`) re-based the census master's row 2 onto the per-frame laws
`MixedFaceLaw m h e' d σ` over the kernel-decided `mixedFrames m` and recorded the
exact per-axis missing legs: the compositum `cellTransport` and the per-frame
decision transports.  This file lands the constructible part:

* **§1 THE `(h, 1)` CELLS**: `slopeCellDec` (the general-`h` replay of IFCG51's
  `eisCellDec`), the exact centre decomposition of the `d = 1` frame carriers
  (`mixedFace_one_eq_biUnion`, `card_mixedFace_one_eq_sum`).
* **§2 THE `(h, 1)` BOX CHARACTERIZATION** (the count instrument, count-first per
  EFR's consumption note): the σ-decided cell IS `slopeBox ∩ decidedSet` at the BASE
  ring — the lattice `h(m−j) ≤ e'·v_j` plus the `k` pinned class digits at heights
  `h(k−t)` reading `(X − ζ̄)^k`'s coefficients — via the landed `h`-general pins
  (`fullSpan_pins`/`fullSpan_raw_dvd`, `minFaceAt_of_lattice`) and the general-target
  digit reading (`xres_eq_iff_digits_target`), read on classes by DBL's digit engine
  (`resDig_mk`, `resOrd_eq_iff_resDig`).  Plus the exact box count
  (`card_slopeBox`) — a pure `q`-monomial at every level.
* **§3 THE SCALE CALCULUS**: `unramScaleType` (`(e, f) ↦ (e, d·f)`, the unramified
  tower step's bookkeeping) and its composition with IFCG47's `scaleType`.
* **§4 ★ THE COMPOSITUM CELL TRANSPORT** (EFR's named missing instrument #1):
  `compCellTransport : Coeff O (e'·d·k) N ≃ Coeff O₂ k (e'·N)` over the tower
  `O → O₁ = AdjoinRoot φ → O₂ = AdjoinRoot (eisKey (algebraMap π) c₁ e')` — the
  `κ`-adic dev digits (any monic degree-`e'·d` key) read through the mixed lattice's
  bi-polynomial coordinates; level scales by exactly `e'`, count base by `q ↦ q^d`
  (`card_coeff_compositum`).  The INBOUND congruence is EFR's
  `compositum_root_pow_dvd_mk_iff` at `w = e'·N` (the exponent
  `(e'N + e' − 1 − i)/e' = N` exactly); the outbound is dev additivity plus
  `α₂^{e'} ∣ π₁`.

## Honesty fence

NO `MixedFaceLaw` fires here at a live frame, and the census master is NOT
recomputed: the per-frame decision transports are the OM tower steps at slope `h/e'`
and at the unramified stage — the same cite-genre content that the `(1, 1)` frame
consumed as the staged `FactorCorrespondenceAt` (row 1).  CN2's landed criterion
(`decidedAt_of_eisenstein_face`, IFCG23) is denominator-`= m` only and does not cover
the `(3,4,1)` frame (`e' = 4 < 8 = m`).  This file's content is exactly the
constructible remainder EFR named; the surviving open set per axis is recorded in
`runs/wave-c/verdict_MFL.md`.

## Axiom fence

Everything here is construction + counting over landed Lean-core material; expected
footprint: pure Lean core `{propext, Classical.choice, Quot.sound}` on every
declaration.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG64

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le)
open Uniformity.Density.IFCG24 (npHeight_coe card_setOf_le_resOrd card_pi_set)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG27 (adjoinRoot_isDVR adjoinRoot_maximalIdeal_eq
  adjoinRoot_isAdicComplete adjoinRoot_finite_residueField residueCard_adjoinRoot)
open Uniformity.Density.IFCG29 (irreducible_algebraMap_adjoinRoot)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_unique classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos)
open Uniformity.Density.IFCG36 (resDig resDig_mk card_setOf_resDig
  resOrd_eq_iff_resDig)
open Uniformity.Density.IFCG37 (xres resPoly_x_frame)
open Uniformity.Density.IFCG38 (classResidualPoly_monic)
open Uniformity.Density.IFCG39 (eisKey eisKey_monic eisKey_natDegree
  eis_root_pow_dvd_mk_iff devT reassT devT_coeff devT_monic devT_reassT reassT_devT
  reassT_monic)
open Uniformity.Density.IFCG43 (eis_recentring_stack compositum_recentring_stack)
open Uniformity.Density.IFCG44 (fullSpan_pins fullSpan_raw_dvd fullSpan_corner
  minFaceAt_of_lattice)
open Uniformity.Density.IFCG47 (scaleType scaleType_data scaleType_degree
  scaleType_injective scaleType_one)
open Uniformity.Density.IFCG62 (mixedFace MixedFaceLaw mixedFrames
  mem_mixedFrames_iff xres_eq_iff_digits_target xres_eq_psi_pow_iff_digits
  compositum_root_pow_dvd_mk_iff unram_pow_dvd_mk_iff)

-- No kernel-`decide` occurs in this file (IFCG62's frame censuses are upstream), so
-- the file-wide classical instance is safe (IFCG51's convention).
attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply) -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- The residual centre is pinned by equal powers (IFCG51's private
`residual_pow_inj`, replica). -/
private theorem residual_pow_inj {ζ ζ' : resField (X : Polynomial O)} {k : ℕ}
    (hk : 1 ≤ k)
    (h : (Polynomial.X - Polynomial.C ζ) ^ k = (Polynomial.X - Polynomial.C ζ') ^ k) :
    ζ = ζ' := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have h1 := congrArg (Polynomial.eval ζ) h
  rw [Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C,
    sub_self, zero_pow (by omega : k ≠ 0)] at h1
  have h2 : ζ - ζ' = 0 := pow_eq_zero_iff (by omega : k ≠ 0) |>.mp h1.symm
  have h3 : ζ - ζ' + ζ' = 0 + ζ' := by rw [h2]
  rwa [sub_add_cancel, zero_add] at h3

/-- Exact disjoint-union count over a finite index set (IFCG51's private replica). -/
private theorem ncard_biUnion_eq {α ι : Type*} [Finite α] (s : Finset ι)
    (f : ι → Set α)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hcons : (⋃ i ∈ Finset.cons a s ha, f i) = f a ∪ ⋃ i ∈ s, f i := by
        rw [Finset.cons_eq_insert, Finset.set_biUnion_insert]
      rw [hcons, Finset.sum_cons]
      have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hdisj a (Finset.mem_cons_self a s) i
          (Finset.mem_cons_of_mem hi) (by rintro rfl; exact ha hi)
      rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
      congr 1
      exact ih fun i hi j hj hij =>
        hdisj i (Finset.mem_cons_of_mem hi) j (Finset.mem_cons_of_mem hj) hij

end Kit

/-! ## §1 — the `(h, 1)` cells and the centre decomposition of the `d = 1` frame
carriers -/

section SlopeCells

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The σ-decided slope cell** at face `(h, e')`, residual centre `ζ`, multiplicity
`k`: the general-`h` replay of IFCG51's `eisCellDec` (which is the `h = 1` instance).
These tile the `(h, 1)` mixed-frame carriers over the nonzero centres. -/
def slopeCellDec (π : O) (m h e' k N : ℕ) (ζ : resField (X : Polynomial O))
    (σ : FactorizationType) : Set (Coeff O m N) :=
  {c | MinFaceAt c h e'
    ∧ classResidualPoly π c h e' = (Polynomial.X - Polynomial.C ζ) ^ k
    ∧ DecidedAt O m σ N c}

/-- ★ **THE CENTRE DECOMPOSITION** of the `(h, 1)` frame carrier: `mixedFace` at
`d = 1` is EXACTLY the union of the slope cells over the nonzero centres — a linear
monic irreducible with nonzero constant term is `X − ζ`, `ζ ≠ 0`, and conversely. -/
theorem mixedFace_one_eq_biUnion (π : O) {m h e' k N : ℕ}
    (hk : k = m / (e' * 1)) (σ : FactorizationType) :
    mixedFace π m h e' 1 N σ
      = ⋃ ζ ∈ {ζ : resField (X : Polynomial O) | ζ ≠ 0},
          slopeCellDec π m h e' k N ζ σ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  subst hk
  ext c
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨hF, ⟨ψ, hψm, hψi, hψd, hψ0, hres⟩, hdec⟩
    obtain ⟨a, ha⟩ : ∃ a, ψ = Polynomial.X + Polynomial.C a :=
      ⟨ψ.coeff 0, hψm.eq_X_add_C hψd⟩
    have ha0 : a ≠ 0 := by
      intro h0
      apply hψ0
      rw [ha, h0]
      simp
    refine ⟨-a, neg_ne_zero.mpr ha0, hF, ?_, hdec⟩
    rw [hres]
    congr 1
    rw [ha, map_neg, sub_neg_eq_add]
  · rintro ⟨ζ, hζ0, hF, hres, hdec⟩
    refine ⟨hF, ⟨Polynomial.X - Polynomial.C ζ, Polynomial.monic_X_sub_C ζ,
      Polynomial.irreducible_X_sub_C ζ, Polynomial.natDegree_X_sub_C ζ, ?_, hres⟩,
      hdec⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact neg_ne_zero.mpr hζ0

/-- Distinct centres give disjoint slope cells (prime-power rigidity of the
residual). -/
theorem slopeCellDec_disjoint (π : O) {m h e' k N : ℕ} (hk : 1 ≤ k)
    {ζ ζ' : resField (X : Polynomial O)} (hne : ζ ≠ ζ') (σ : FactorizationType) :
    Disjoint (slopeCellDec π m h e' k N ζ σ) (slopeCellDec π m h e' k N ζ' σ) := by
  rw [Set.disjoint_left]
  rintro c ⟨-, hres, -⟩ ⟨-, hres', -⟩
  exact hne (residual_pow_inj hk (hres.symm.trans hres'))

/-- ★ **THE CENTRE-SUM COUNT**: the `(h, 1)` frame-carrier count is the exact sum of
the `q − 1` slope-cell counts, at every level. -/
theorem card_mixedFace_one_eq_sum (π : O) {m h e' k N : ℕ}
    (hk : k = m / (e' * 1)) (hk1 : 1 ≤ k) (σ : FactorizationType)
    [Fintype (ResidueField O)] :
    Nat.card (mixedFace π m h e' 1 N σ)
      = ∑ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          Nat.card (slopeCellDec π m h e' k N (resFieldXEquiv O y) σ) := by
  classical
  have hunion : mixedFace π m h e' 1 N σ
      = ⋃ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          slopeCellDec π m h e' k N (resFieldXEquiv O y) σ := by
    rw [mixedFace_one_eq_biUnion π hk σ]
    ext c
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ζ, hζ0, hc⟩
      refine ⟨(resFieldXEquiv O).symm ζ, ?_, ?_⟩
      · intro h0
        apply hζ0
        have h1 : resFieldXEquiv O ((resFieldXEquiv O).symm ζ) = ζ :=
          (resFieldXEquiv O).apply_symm_apply ζ
        rw [← h1, h0, map_zero]
      · rw [(resFieldXEquiv O).apply_symm_apply ζ]
        exact hc
    · rintro ⟨y, hy0, hc⟩
      refine ⟨resFieldXEquiv O y, ?_, hc⟩
      intro h0
      apply hy0
      refine (resFieldXEquiv O).injective ?_
      rw [map_zero]
      exact h0
  have hdisj : ∀ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
      ∀ y' ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0), y ≠ y' →
        Disjoint (slopeCellDec π m h e' k N (resFieldXEquiv O y) σ)
          (slopeCellDec π m h e' k N (resFieldXEquiv O y') σ) := by
    intro y _ y' _ hne
    exact slopeCellDec_disjoint π hk1
      (fun hcon => hne ((resFieldXEquiv O).injective hcon)) σ
  rw [hunion, Nat.card_coe_set_eq, ncard_biUnion_eq _ _ hdisj]
  exact Finset.sum_congr rfl fun y _ => (Nat.card_coe_set_eq _).symm

end SlopeCells

/-! ## §2 — the `(h, 1)` box characterization at the base ring (the count
instrument): the σ-decided slope cell IS a digit-pinned lattice box intersected with
the decided set — no ring transport -/

section SlopeBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private
replica). -/
private theorem mem_sideSet_iff' {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · intro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩
    exact this

/-- IFCG39/44's representation supply (IFCG51's private replica): on a minimal face
the canonical class residual IS every lift's side residual, with the side set, finite
support and height data exported. -/
private theorem resPoly_rep {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ (hne : (sideSet X (monicPoly a) h e').Nonempty) (H₀ : ℕ),
      npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) = (H₀ : ℕ∞)
      ∧ suppVal X (monicPoly a) h e' ≠ ⊤
      ∧ classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne H₀ := by
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  have hilt : i < m := lt_of_lt_of_le hij hAj.1
  obtain ⟨hOni, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAi ha
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have himem : i ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := ⟨i, himem⟩
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) := hw
  exact ⟨hne, w, hw'.symm, htop,
    classResidualPoly_eq hπ he' hvis ha hne hw'.symm⟩

/-- ★ **THE `h`-GENERAL LATTICE PINS** (IFCG51's `lattice_pins` at every coprime
slope): at frame `(h, e')` the raw lattice (`h(m − j) ≤ e'·v_j`) with EXACT corner
(`v_0 = h·D`, `e'·D = m`) reconstructs the minimal face AND pins the residual degree
to `D`. -/
theorem slope_lattice_pins {π : O} (hπ : Irreducible π) {m K h e' D : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e')
    (hfull : e' * D = m) (hmK : m ≤ K) (hm0 : 0 < m)
    {c : Coeff O m K}
    (hlat : ∀ j : Fin m, h * (m - (j : ℕ)) ≤ e' * resOrd (c j))
    (hcorner : resOrd (c ⟨0, hm0⟩) = h * D) :
    MinFaceAt c h e' ∧ (classResidualPoly π c h e').natDegree = D := by
  have he'' : 0 < e' := by omega
  have hF : MinFaceAt c h e' :=
    minFaceAt_of_lattice hh1 hhe hcop hfull hmK hm0 hlat hcorner
  refine ⟨hF, ?_⟩
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  have hnd := natDegree_resPoly hπ isKey_X he'' hcop htop hne hH₀
  rw [hcrp, hnd.1]
  have hsup : classNPSupport c h e' = h * m := minFaceAt_support hF
  obtain ⟨hh1', hhe', hcop', hface, hAm, hvis⟩ := hF
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  -- sideMax = m (the monic attainment, transported to the lift)
  obtain ⟨hOnm, hsuppm⟩ := onSide_monicPoly_of_npAttains hπ he'' hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  -- the class attains at 0 (exact corner)
  have hnp0 : npHeight c 0 = h * D := by
    have h5 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
      simpa using npHeight_coe c ⟨0, hm0⟩
    rw [h5, hcorner]
  have hA0 : NPAttains c h e' 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [hsup, hnp0, Nat.mul_zero, Nat.add_zero, ← hfull]
    ring
  obtain ⟨hOn0, -⟩ := onSide_monicPoly_of_npAttains hπ he'' hvis hA0 ha
  have h0mem : (0 : ℕ) ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hmin0 : sideMin X (monicPoly a) h e' hne = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  -- sideDeg = (m − 0)/e' = D
  unfold sideDeg
  rw [hmax, hmin0, Nat.sub_zero, ← hfull, Nat.mul_div_cancel_left D he'']

/-- **The `(h, 1)` slope box** at centre `y`, multiplicity `k`: the raw lattice
`h(e'k − j) ≤ e'·v_j` together with the `k` pinned class digits at the `e'`-divisible
slots — the digit at height `h(k − t)` of coordinate `e'·t` reads the `t`-th
coefficient of `(X − y)^k`.  A pure valuation/digit condition: no face or residual
language. -/
def slopeBox (π : O) (h e' k N : ℕ) (y : ResidueField O) :
    Set (Coeff O (e' * k) N) :=
  {c | (∀ j : Fin (e' * k), h * (e' * k - (j : ℕ)) ≤ e' * resOrd (c j))
    ∧ ∀ (j : Fin (e' * k)) (t : ℕ), t < k → (j : ℕ) = e' * t →
        resDig π (h * (k - t)) (c j)
          = ((Polynomial.X - Polynomial.C y) ^ k).coeff t}

/-- ★★ **THE `(h, 1)` BOX CHARACTERIZATION** (the count instrument, at the BASE
ring): the σ-decided slope cell IS `slopeBox ∩ decidedSet` — forward by the landed
`h`-general side pins + the general-target digit reading, backward by the lattice
reconstruction + the exact corner from the nonzero pinned digit.  EFR's count-first
route: the `(h, 1)` carrier count needs NO ring transport; only the decision is
tower-shaped. -/
theorem slopeCellDec_eq_box_inter {π : O} (hπ : Irreducible π) {h e' k N : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hk1 : 1 ≤ k)
    (hmN : e' * k ≤ N) {y : ResidueField O} (hy : y ≠ 0) (σ : FactorizationType) :
    slopeCellDec π (e' * k) h e' k N (resFieldXEquiv O y) σ
      = slopeBox π h e' k N y ∩ decidedSet O (e' * k) σ N := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have he'' : 0 < e' := by omega
  have hm0 : 0 < e' * k := Nat.mul_pos he'' (by omega)
  have hhkN : ∀ t : ℕ, h * (k - t) < N := by
    intro t
    have h1 : h * (k - t) ≤ h * k := Nat.mul_le_mul (le_refl h) (by omega)
    have h2 : h * k < e' * k := Nat.mul_lt_mul_of_lt_of_le hhe (le_refl k) (by omega)
    omega
  -- the RingHom coercion of the frame equivalence, and its pow-map identity
  have hmapy : ((Polynomial.X - Polynomial.C y) ^ k).map
        (resFieldXEquiv O : ResidueField O →+* resField (X : Polynomial O))
      = (Polynomial.X - Polynomial.C (resFieldXEquiv O y)) ^ k := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  ext c
  constructor
  · rintro ⟨hF, hres, hdec⟩
    obtain ⟨a, ha⟩ := proj_surjective O (e' * k) N c
    have hdegres : (classResidualPoly π c h e').natDegree = k := by
      rw [hres, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
    have hfull' : e' * (classResidualPoly π c h e').natDegree = e' * k := by
      rw [hdegres]
    obtain ⟨hne, hmin0, hsdeg, hnpz, hcrp⟩ := fullSpan_pins hπ hF hfull' ha
    rw [hdegres] at hsdeg hcrp
    -- the xres normal form of the residual
    have hxres : xres π (monicPoly a) h e' hne (h * k)
        = (Polynomial.X - Polynomial.C y) ^ k := by
      have hmaps : (xres π (monicPoly a) h e' hne (h * k)).map
            (resFieldXEquiv O : ResidueField O →+* resField (X : Polynomial O))
          = ((Polynomial.X - Polynomial.C y) ^ k).map
            (resFieldXEquiv O : ResidueField O →+* resField (X : Polynomial O)) := by
        rw [hmapy, ← resPoly_x_frame, ← hcrp, hres]
      exact Polynomial.map_injective _ (resFieldXEquiv O).injective hmaps
    have hdig := (xres_eq_iff_digits_target (monicPoly_monic a)
      (by rw [monicPoly_natDegree]) hne hmin0 hsdeg
      ((Polynomial.monic_X_sub_C y).pow k)
      (by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
        Nat.mul_one])).mp hxres
    refine ⟨⟨fun j => minFaceAt_min hF j, ?_⟩, hdec⟩
    rintro j t ht hjt
    have hcj : c j = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a j) := by
      rw [← ha]
      rfl
    have haj : (monicPoly a).coeff (e' * t) = a j := by
      rw [← hjt]
      exact monicPoly_coeff_lt a j.isLt
    rw [hcj, resDig_mk hπ (hhkN t), ← haj]
    exact hdig t ht
  · rintro ⟨⟨hlat, hpins⟩, hdec⟩
    -- the exact corner from the lattice floor + the nonzero pinned digit
    have hc00 : ((Polynomial.X - Polynomial.C y) ^ k).coeff 0 = (-y) ^ k := by
      rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply,
        Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
    have hcorner : resOrd (c ⟨0, hm0⟩) = h * k := by
      have hge : h * k ≤ resOrd (c ⟨0, hm0⟩) := by
        have h1 := hlat ⟨0, hm0⟩
        simp only [Nat.sub_zero] at h1
        have h2 : e' * (h * k) ≤ e' * resOrd (c ⟨0, hm0⟩) := by
          calc e' * (h * k) = h * (e' * k) := by ring
            _ ≤ e' * resOrd (c ⟨0, hm0⟩) := h1
        exact Nat.le_of_mul_le_mul_left h2 he''
      have hpin0 := hpins ⟨0, hm0⟩ 0 (by omega) (by simp)
      rw [Nat.sub_zero] at hpin0
      refine (resOrd_eq_iff_resDig hπ (hhkN 0) _).mpr ⟨?_, ?_⟩
      · rw [Nat.sub_zero]
        exact hge
      · rw [Nat.sub_zero, hpin0, hc00]
        exact pow_ne_zero k (neg_ne_zero.mpr hy)
    obtain ⟨hF, hdegk⟩ := slope_lattice_pins hπ hh1 hhe hcop rfl hmN hm0 hlat hcorner
    obtain ⟨a, ha⟩ := proj_surjective O (e' * k) N c
    have hfull' : e' * (classResidualPoly π c h e').natDegree = e' * k := by
      rw [hdegk]
    obtain ⟨hne, hmin0, hsdeg, hnpz, hcrp⟩ := fullSpan_pins hπ hF hfull' ha
    rw [hdegk] at hsdeg hcrp
    -- the digit pins on the lift
    have hdig : ∀ t, t < k → digAt π (h * (k - t)) ((monicPoly a).coeff (e' * t))
        = ((Polynomial.X - Polynomial.C y) ^ k).coeff t := by
      intro t ht
      have hlt : e' * t < e' * k := by
        have h1 : e' * (t + 1) ≤ e' * k := Nat.mul_le_mul (le_refl e') (by omega)
        have h2 : e' * (t + 1) = e' * t + e' := by ring
        omega
      have hpin := hpins ⟨e' * t, hlt⟩ t ht rfl
      have hcj : c ⟨e' * t, hlt⟩
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨e' * t, hlt⟩) := by
        rw [← ha]
        rfl
      rw [hcj, resDig_mk hπ (hhkN t)] at hpin
      rwa [monicPoly_coeff_lt a hlt]
    have hxres := (xres_eq_iff_digits_target (monicPoly_monic a)
      (by rw [monicPoly_natDegree]) hne hmin0 hsdeg
      ((Polynomial.monic_X_sub_C y).pow k)
      (by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
        Nat.mul_one])).mpr hdig
    refine ⟨hF, ?_, hdec⟩
    rw [hcrp, resPoly_x_frame, hxres, hmapy]

/-- ★ **THE `(h, 1)` BOX COUNT** — the digit-pinned lattice box is an EXACT
`q`-monomial at every level: `q^(mN − Σ_j ⌈h(m−j)/e'⌉ − k)` (`m = e'k`; each of the
`m` coordinates is free above its lattice floor, and the `k` digit pins cost one
`q`-power each).  With `slopeCellDec_eq_box_inter` this reduces the `(h, 1)`
frame-carrier count entirely to the decided-set intersection. -/
theorem card_slopeBox {π : O} (hπ : Irreducible π) {h e' k N : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hk1 : 1 ≤ k) (hmN : e' * k ≤ N)
    (y : ResidueField O) :
    Nat.card (slopeBox π h e' k N y)
      = residueCard O
          ^ (e' * k * N
              - ((∑ j ∈ Finset.range (e' * k),
                  (h * (e' * k - j) + (e' - 1)) / e') + k)) := by
  classical
  have he'' : 0 < e' := by omega
  have hm0 : 0 < e' * k := Nat.mul_pos he'' (by omega)
  have hhkN : h * k < N := by
    have h2 : h * k < e' * k := Nat.mul_lt_mul_of_lt_of_le hhe (le_refl k) (by omega)
    omega
  -- the ceiling floors, and their two bounds
  set b : ℕ → ℕ := fun j => (h * (e' * k - j) + (e' - 1)) / e' with hb
  have hble : ∀ j, b j ≤ h * k := by
    intro j
    have h1 : h * (e' * k - j) + (e' - 1) ≤ h * (e' * k) + (e' - 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul (le_refl h) (by omega)) _
    have h2 : (h * (e' * k) + (e' - 1)) / e' = h * k := by
      have h3 : h * (e' * k) = e' * (h * k) := by ring
      rw [h3, Nat.mul_add_div he'', Nat.div_eq_of_lt (by omega), Nat.add_zero]
    calc b j ≤ (h * (e' * k) + (e' - 1)) / e' := Nat.div_le_div_right h1
      _ = h * k := h2
  have hbdvd : ∀ t, t < k → b (e' * t) = h * (k - t) := by
    intro t ht
    have h1 : e' * k - e' * t = e' * (k - t) := by
      have h2 : e' * (k - t) + e' * t = e' * k := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    have h3 : h * (e' * (k - t)) = e' * (h * (k - t)) := by ring
    rw [hb]
    show (h * (e' * k - e' * t) + (e' - 1)) / e' = h * (k - t)
    rw [h1, h3, Nat.mul_add_div he'', Nat.div_eq_of_lt (by omega), Nat.add_zero]
  -- the per-coordinate sets
  set S : Fin (e' * k) → Set (Res O N) := fun j =>
    if e' ∣ (j : ℕ)
    then {x : Res O N | h * (k - (j : ℕ) / e') ≤ resOrd x
        ∧ resDig π (h * (k - (j : ℕ) / e')) x
            = ((Polynomial.X - Polynomial.C y) ^ k).coeff ((j : ℕ) / e')}
    else {x : Res O N | (h * (e' * k - (j : ℕ)) + (e' - 1)) / e' ≤ resOrd x}
    with hS
  -- the box is the coordinate product of the `S j`
  have hbox : slopeBox π h e' k N y = {c : Coeff O (e' * k) N | ∀ j, c j ∈ S j} := by
    ext c
    constructor
    · rintro ⟨hlat, hpins⟩ j
      by_cases hdvd : e' ∣ (j : ℕ)
      · have hjt : (j : ℕ) = e' * ((j : ℕ) / e') := (Nat.mul_div_cancel' hdvd).symm
        have ht : (j : ℕ) / e' < k := by
          have h1 : e' * ((j : ℕ) / e') < e' * k := by
            rw [← hjt]
            exact j.isLt
          exact Nat.lt_of_mul_lt_mul_left h1
        rw [hS]
        simp only [if_pos hdvd, Set.mem_setOf_eq]
        refine ⟨?_, hpins j ((j : ℕ) / e') ht hjt⟩
        have h1 := hlat j
        have h2 : e' * k - (j : ℕ) = e' * (k - (j : ℕ) / e') := by
          have h3 : e' * (k - (j : ℕ) / e') + e' * ((j : ℕ) / e') = e' * k := by
            rw [← Nat.mul_add]
            congr 1
            omega
          omega
        rw [h2] at h1
        have h4 : e' * (h * (k - (j : ℕ) / e')) ≤ e' * resOrd (c j) := by
          calc e' * (h * (k - (j : ℕ) / e')) = h * (e' * (k - (j : ℕ) / e')) := by ring
            _ ≤ e' * resOrd (c j) := h1
        exact Nat.le_of_mul_le_mul_left h4 he''
      · rw [hS]
        simp only [if_neg hdvd, Set.mem_setOf_eq]
        have h1 := hlat j
        have h2 : (h * (e' * k - (j : ℕ)) + (e' - 1)) / e' < resOrd (c j) + 1 := by
          rw [Nat.div_lt_iff_lt_mul he'']
          have h3 : (resOrd (c j) + 1) * e' = e' * resOrd (c j) + e' := by ring
          rw [h3]
          generalize hA : h * (e' * k - (j : ℕ)) = A at h1 ⊢
          generalize hB : e' * resOrd (c j) = B at h1 ⊢
          omega
        omega
    · intro hall
      constructor
      · intro j
        have h1 := hall j
        by_cases hdvd : e' ∣ (j : ℕ)
        · rw [hS] at h1
          simp only [if_pos hdvd, Set.mem_setOf_eq] at h1
          have h2 : e' * k - (j : ℕ) = e' * (k - (j : ℕ) / e') := by
            have hjt : (j : ℕ) = e' * ((j : ℕ) / e') := (Nat.mul_div_cancel' hdvd).symm
            have h3 : e' * (k - (j : ℕ) / e') + e' * ((j : ℕ) / e') = e' * k := by
              rw [← Nat.mul_add]
              congr 1
              have ht : (j : ℕ) / e' < k := by
                have h4 : e' * ((j : ℕ) / e') < e' * k := by
                  rw [← hjt]
                  exact j.isLt
                exact Nat.lt_of_mul_lt_mul_left h4
              omega
            omega
          rw [h2]
          calc h * (e' * (k - (j : ℕ) / e')) = e' * (h * (k - (j : ℕ) / e')) := by ring
            _ ≤ e' * resOrd (c j) := Nat.mul_le_mul (le_refl e') h1.1
        · rw [hS] at h1
          simp only [if_neg hdvd, Set.mem_setOf_eq] at h1
          have h2 := Nat.div_add_mod (h * (e' * k - (j : ℕ)) + (e' - 1)) e'
          have h3 : (h * (e' * k - (j : ℕ)) + (e' - 1)) % e' < e' := Nat.mod_lt _ he''
          have h4 : e' * ((h * (e' * k - (j : ℕ)) + (e' - 1)) / e')
              ≤ e' * resOrd (c j) := Nat.mul_le_mul (le_refl e') h1
          generalize hA : h * (e' * k - (j : ℕ)) = A at h2 h3 h4 ⊢
          generalize hB : e' * resOrd (c j) = B at h4 ⊢
          generalize hC : e' * ((A + (e' - 1)) / e') = C at h2 h4
          omega
      · rintro j t ht hjt
        have h1 := hall j
        have hdvd : e' ∣ (j : ℕ) := ⟨t, hjt⟩
        rw [hS] at h1
        simp only [if_pos hdvd, Set.mem_setOf_eq] at h1
        have h5 : (j : ℕ) / e' = t := by
          rw [hjt]
          exact Nat.mul_div_cancel_left t he''
        rw [h5] at h1
        exact h1.2
  -- the per-coordinate counts
  have hfac : ∀ j : Fin (e' * k),
      Nat.card (S j)
        = residueCard O ^ (N - (b (j : ℕ) + if e' ∣ (j : ℕ) then 1 else 0)) := by
    intro j
    by_cases hdvd : e' ∣ (j : ℕ)
    · have hjt : (j : ℕ) = e' * ((j : ℕ) / e') := (Nat.mul_div_cancel' hdvd).symm
      have ht : (j : ℕ) / e' < k := by
        have h1 : e' * ((j : ℕ) / e') < e' * k := by
          rw [← hjt]
          exact j.isLt
        exact Nat.lt_of_mul_lt_mul_left h1
      have hbj : b (j : ℕ) = h * (k - (j : ℕ) / e') := by
        have h1 := hbdvd ((j : ℕ) / e') ht
        rw [← hjt] at h1
        exact h1
      have hv : h * (k - (j : ℕ) / e') < N := by
        have h1 : h * (k - (j : ℕ) / e') ≤ h * k :=
          Nat.mul_le_mul (le_refl h) (Nat.sub_le k ((j : ℕ) / e'))
        omega
      rw [hS]
      simp only [if_pos hdvd]
      rw [card_setOf_resDig hπ hv, hbj]
    · have hbj : b (j : ℕ) ≤ N := le_trans (hble _) (by omega)
      rw [hS]
      simp only [if_neg hdvd]
      rw [card_setOf_le_resOrd hbj]
      congr 1
  -- assemble: product of monomials, exponent bookkeeping
  rw [hbox, card_pi_set, Finset.prod_congr rfl (fun j _ => hfac j),
    Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j => N - (b j + if e' ∣ j then 1 else 0)) (e' * k)]
  -- Σ (N − (b_j + δ_j)) = mN − (Σ b_j + k)
  have hδsum : ∑ j ∈ Finset.range (e' * k), (if e' ∣ j then 1 else 0) = k := by
    have hfilter : (Finset.range (e' * k)).filter (fun j => e' ∣ j)
        = (Finset.range k).image (fun t => e' * t) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hjm, t, rfl⟩
        exact ⟨t, Nat.lt_of_mul_lt_mul_left hjm, rfl⟩
      · rintro ⟨t, htk, rfl⟩
        refine ⟨?_, ⟨t, rfl⟩⟩
        have h1 : e' * (t + 1) ≤ e' * k := Nat.mul_le_mul (le_refl e') (by omega)
        have h2 : e' * (t + 1) = e' * t + e' := by ring
        omega
    rw [← Finset.card_filter, hfilter,
      Finset.card_image_of_injective _ (fun a b hab =>
        Nat.eq_of_mul_eq_mul_left he'' hab),
      Finset.card_range]
  have hble' : ∀ j ∈ Finset.range (e' * k),
      b j + (if e' ∣ j then 1 else 0) ≤ N := by
    intro j _
    have h1 := hble j
    by_cases hdvd : e' ∣ j
    · rw [if_pos hdvd]
      omega
    · rw [if_neg hdvd]
      omega
  have hsplit : ∑ j ∈ Finset.range (e' * k),
        (N - (b j + if e' ∣ j then 1 else 0))
      + ∑ j ∈ Finset.range (e' * k), (b j + if e' ∣ j then 1 else 0)
      = e' * k * N := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ j ∈ Finset.range (e' * k),
        N - (b j + if e' ∣ j then 1 else 0)
          + (b j + if e' ∣ j then 1 else 0) = N := by
      intro j hj
      exact Nat.sub_add_cancel (hble' j hj)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Nat.mul_comm]
  have hbsum : ∑ j ∈ Finset.range (e' * k), (b j + if e' ∣ j then 1 else 0)
      = (∑ j ∈ Finset.range (e' * k), b j) + k := by
    rw [Finset.sum_add_distrib, hδsum]
  rw [hbsum] at hsplit
  exact Nat.eq_sub_of_add_eq hsplit

/-- ★★★ **THE `(h, 1)` COUNT ENDPOINT**: the frame carrier's count at every level is
the sum over the `q − 1` residual centres of the DECIDED digit-pinned box counts at
the BASE ring — the `(h, 1)` axis's count layer, complete and transport-free.  What
remains for the `(h, 1)` frame law is exactly the decision leg (the OM tower step at
slope `h/e'`), never the count. -/
theorem card_mixedFace_one_eq_box_sum {π : O} (hπ : Irreducible π) {h e' k N : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hk1 : 1 ≤ k)
    (hmN : e' * k ≤ N) (σ : FactorizationType) [Fintype (ResidueField O)] :
    Nat.card (mixedFace π (e' * k) h e' 1 N σ)
      = ∑ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          Nat.card ((slopeBox π h e' k N y ∩ decidedSet O (e' * k) σ N)
            : Set (Coeff O (e' * k) N)) := by
  classical
  have he'' : 0 < e' := by omega
  have hk : k = e' * k / (e' * 1) := by
    rw [Nat.mul_one, Nat.mul_div_cancel_left k he'']
  rw [card_mixedFace_one_eq_sum π hk hk1 σ]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
  rw [slopeCellDec_eq_box_inter hπ hh1 hhe hcop hk1 hmN hy0 σ]

end SlopeBox

/-! ## §3 — the unramified scale calculus: the `(e, f) ↦ (e, d·f)` bookkeeping of the
unramified tower stage, and the composed `(1, d)`-frame tower map -/

section UnramScale

/-- **The `d`-unramified scaled type**: each `(e, f)` member becomes `(e, d·f)` — the
classical tower multiplicativity `e(L/K) = e(L/K')·e(K'/K)`, `f(L/K) =
f(L/K')·f(K'/K)` along an UNRAMIFIED step `e(K'/K) = 1`, `f(K'/K) = d` (the residual
root field `𝔽_{q^d}`: `residueCard O₁ = q^d` by IFCG27's cascade). -/
def unramScaleType (d : ℕ) (σ : FactorizationType) : FactorizationType :=
  ⟨σ.data.map fun p => (p.1, d * p.2)⟩

theorem unramScaleType_data (d : ℕ) (σ : FactorizationType) :
    (unramScaleType d σ).data = σ.data.map fun p => (p.1, d * p.2) := rfl

/-- Degree scales by exactly `d` — the level/degree bookkeeping of the unramified
stage. -/
theorem unramScaleType_degree (d : ℕ) (σ : FactorizationType) :
    (unramScaleType d σ).degree = d * σ.degree := by
  unfold FactorizationType.degree
  rw [unramScaleType_data, Multiset.map_map]
  have h1 : ((fun p : ℕ × ℕ => p.1 * p.2) ∘ fun p : ℕ × ℕ => (p.1, d * p.2))
      = fun p : ℕ × ℕ => d * (p.1 * p.2) := by
    funext p
    show p.1 * (d * p.2) = d * (p.1 * p.2)
    ring
  rw [h1, ← Multiset.sum_map_mul_left]

@[simp] theorem unramScaleType_one (σ : FactorizationType) :
    unramScaleType 1 σ = σ := by
  apply FactorizationType.ext
  rw [unramScaleType_data]
  have h1 : (fun p : ℕ × ℕ => (p.1, 1 * p.2)) = id := by
    funext p
    simp
  rw [h1, Multiset.map_id]

/-- Unramified scaling is injective at `d > 0`. -/
theorem unramScaleType_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (unramScaleType d) := by
  intro σ τ h
  apply FactorizationType.ext
  have hinj : Function.Injective fun p : ℕ × ℕ => (p.1, d * p.2) := by
    intro p q hpq
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hpq
    exact Prod.ext h1 (Nat.eq_of_mul_eq_mul_left hd h2)
  have hdata : σ.data.map (fun p : ℕ × ℕ => (p.1, d * p.2))
      = τ.data.map (fun p : ℕ × ℕ => (p.1, d * p.2)) := by
    rw [← unramScaleType_data, ← unramScaleType_data, h]
  exact Multiset.map_injective hinj hdata

/-- The two tower stages COMMUTE: ramification scales the first coordinate, inertia
the second. -/
theorem scaleType_unramScaleType_comm (e' d : ℕ) (σ : FactorizationType) :
    scaleType e' (unramScaleType d σ) = unramScaleType d (scaleType e' σ) := by
  apply FactorizationType.ext
  rw [scaleType_data, unramScaleType_data, unramScaleType_data, scaleType_data,
    Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  rfl

/-- ★ **THE `(h, d)`-FRAME TOWER TYPE MAP**: the composed bookkeeping of the mixed
tower `O → O₁ = AdjoinRoot φ → O₂` — inertia by `d` at the unramified stage, then
ramification by `e'` at the Eisenstein stage: `(e, f) ↦ (e'·e, d·f)`. -/
def towerScaleType (e' d : ℕ) (σ : FactorizationType) : FactorizationType :=
  scaleType e' (unramScaleType d σ)

theorem towerScaleType_degree (e' d : ℕ) (σ : FactorizationType) :
    (towerScaleType e' d σ).degree = e' * (d * σ.degree) := by
  rw [towerScaleType, scaleType_degree, unramScaleType_degree]

@[simp] theorem towerScaleType_one_one (σ : FactorizationType) :
    towerScaleType 1 1 σ = σ := by
  rw [towerScaleType, unramScaleType_one, scaleType_one]

/-- The composed tower map is injective at `e', d > 0` — the lever that lets ONE
pointwise tower law drive BOTH directions of a mixed-frame decision transport. -/
theorem towerScaleType_injective {e' d : ℕ} (he' : 0 < e') (hd : 0 < d) :
    Function.Injective (towerScaleType e' d) :=
  (scaleType_injective he').comp (unramScaleType_injective hd)

end UnramScale

/-! ## §4 — ★ THE COMPOSITUM CELL TRANSPORT (EFR's named missing instrument): the
unramified-stage transport, and its composition with IFCG43's Eisenstein-stage
transport over the tower -/

section UnramTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Level equality on classes IS `ϖ^N`-divisibility of the difference (IFCG43's
private replica). -/
private theorem res_mk_eq_iff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {N : ℕ} {x y : R} :
    Ideal.Quotient.mk ((maximalIdeal R) ^ N) x
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) y
      ↔ ϖ ^ N ∣ x - y := by
  rw [Ideal.Quotient.eq]
  exact mem_pow_maximalIdeal_iff hϖ N _

/-- Class-equal coefficient vectors have `ϖ^N`-divisible monic-block differences at
EVERY slot (IFCG43's private replica). -/
private theorem pow_dvd_monicPoly_sub_coeff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {n N : ℕ}
    {a a' : Fin n → R} (h : proj R n N a = proj R n N a') (l : ℕ) :
    ϖ ^ N ∣ (monicPoly a - monicPoly a').coeff l := by
  rw [Polynomial.coeff_sub]
  rcases lt_trichotomy l n with hl | hl | hl
  · rw [monicPoly_coeff_lt a hl, monicPoly_coeff_lt a' hl]
    have hcl : Ideal.Quotient.mk ((maximalIdeal R) ^ N) (a ⟨l, hl⟩)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) (a' ⟨l, hl⟩) :=
      congrFun h ⟨l, hl⟩
    exact (res_mk_eq_iff hϖ).mp hcl
  · have h1 : (monicPoly a).coeff l = 1 := by
      have h2 := (monicPoly_monic a).coeff_natDegree
      rw [monicPoly_natDegree] at h2
      rw [hl]
      exact h2
    have h2 : (monicPoly a').coeff l = 1 := by
      have h3 := (monicPoly_monic a').coeff_natDegree
      rw [monicPoly_natDegree] at h3
      rw [hl]
      exact h3
    rw [h1, h2, sub_self]
    exact dvd_zero _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [monicPoly_natDegree]; exact hl),
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [monicPoly_natDegree]; exact hl), sub_self]
    exact dvd_zero _

/-- A monic polynomial of degree `n` is `monicPoly` of its own low coefficient vector
(IFCG43's private replica). -/
private theorem monicPoly_coeff_self {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} {f : Polynomial R} (hf : f.Monic)
    (hn : f.natDegree = n) : monicPoly (fun i : Fin n => f.coeff i.1) = f := by
  classical
  have hlead : f.coeff n = 1 := by rw [← hn]; exact hf.coeff_natDegree
  refine Polynomial.ext fun m => ?_
  rcases lt_trichotomy m n with h | h | h
  · rw [monicPoly_coeff_lt _ h]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).coeff n = 1 := by
      have h2 := (monicPoly_monic (fun i : Fin n => f.coeff i.1)).coeff_natDegree
      rwa [monicPoly_natDegree] at h2
    rw [h, h1, hlead]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree = n :=
      monicPoly_natDegree _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree < m),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m)]

/-- Scalar multiples pass through monic division (`smul_modByMonic`'s quotient
companion; mathlib has the remainder half only). -/
private theorem smul_divByMonic {R : Type*} [CommRing R] [IsDomain R]
    {q : Polynomial R} (hq : q.Monic) (c : R)
    (p : Polynomial R) : (c • p) /ₘ q = c • (p /ₘ q) := by
  have h1 : (c • p) %ₘ q + q * ((c • p) /ₘ q) = c • p :=
    Polynomial.modByMonic_add_div (c • p) q
  have h2 : p %ₘ q + q * (p /ₘ q) = p := Polynomial.modByMonic_add_div p q
  have h3 : c • (p %ₘ q) + q * (c • (p /ₘ q)) = c • p := by
    rw [mul_smul_comm, ← smul_add, h2]
  rw [Polynomial.smul_modByMonic] at h1
  have h4 : q * ((c • p) /ₘ q) = q * (c • (p /ₘ q)) := by
    have h5 := h1.trans h3.symm
    exact add_left_cancel h5
  exact mul_left_cancel₀ hq.ne_zero h4

/-- ★ **The development is `O`-linear in scalars**: `dev φ (c • f) j = c • dev φ f j`
(both halves of monic division are, and `dev` is their iterate). -/
private theorem dev_smul {φ : Polynomial O} (hφ : φ.Monic) (c : O) :
    ∀ (f : Polynomial O) (j : ℕ), dev φ (c • f) j = c • dev φ f j := by
  intro f j
  induction j generalizing f with
  | zero => exact Polynomial.smul_modByMonic c f
  | succ j ih =>
      show dev φ ((c • f) /ₘ φ) j = _
      rw [smul_divByMonic hφ]
      exact ih _

/-- ★ **THE DEVELOPMENT PRESERVES COEFFICIENT DIVISIBILITY**: if `π^t` divides every
coefficient of `g`, it divides every coefficient of every `φ`-adic digit of `g`. -/
private theorem dvd_dev_coeff {φ : Polynomial O} (hφ : φ.Monic) {π : O} {t : ℕ}
    {g : Polynomial O} (hg : ∀ l, π ^ t ∣ g.coeff l) (j l : ℕ) :
    π ^ t ∣ (dev φ g j).coeff l := by
  have hC : Polynomial.C (π ^ t) ∣ g := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    exact hg
  obtain ⟨Q, hQ⟩ := hC
  have hsmul : g = (π ^ t) • Q := by
    rw [hQ, Polynomial.smul_eq_C_mul]
  rw [hsmul, dev_smul hφ, Polynomial.coeff_smul, smul_eq_mul]
  exact dvd_mul_right _ _

variable {φ : Polynomial O} {π : O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- **The unramified transform vector**: the `O₁`-coordinates of the `φ`-adic dev
transform of the monic block with coefficient vector `a` (`O₁ = AdjoinRoot φ`). -/
def unramDevVec (φ : Polynomial O) (k : ℕ) (a : Fin (φ.natDegree * k) → O) :
    Fin k → AdjoinRoot φ :=
  fun j => (devT φ k (monicPoly a)).coeff j.1

/-- **The unramified reassembly vector**: the `O`-coordinates of the reassembled block
of the monic `O₁`-polynomial with coefficient vector `b`. -/
def unramReassVec (φ : Polynomial O) (hφ : φ.Monic) (k : ℕ)
    (b : Fin k → AdjoinRoot φ) : Fin (φ.natDegree * k) → O :=
  fun i => (reassT φ hφ k (monicPoly b)).coeff i.1

/-- ★ **Outbound level exactness at the unramified stage**: level-`N` classes transport
to level-`N` classes — the level does NOT scale (`e(K'/K) = 1`), and the digit read is
coefficientwise (`unram_pow_dvd_mk_iff`). -/
private theorem unramDevVec_congr (hφ : IsKey φ) (hπ : Irreducible π) {k N : ℕ}
    {a a' : Fin (φ.natDegree * k) → O}
    (h : proj O (φ.natDegree * k) N a = proj O (φ.natDegree * k) N a') :
    proj (AdjoinRoot φ) k N (unramDevVec φ k a)
      = proj (AdjoinRoot φ) k N (unramDevVec φ k a') := by
  haveI : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  funext j
  refine (res_mk_eq_iff hπ₁).mpr ?_
  -- the digit difference is the digit of the difference, coefficientwise divisible
  have hsub : dev φ (monicPoly a) j.1 - dev φ (monicPoly a') j.1
      = dev φ (monicPoly a - monicPoly a') j.1 := by
    have hadd := dev_add_of_monic hφ.monic (monicPoly a - monicPoly a')
      (monicPoly a') j.1
    rw [sub_add_cancel] at hadd
    rw [hadd]
    ring
  have hdvd : ∀ l, π ^ N ∣ (dev φ (monicPoly a - monicPoly a') j.1).coeff l :=
    fun l => dvd_dev_coeff hφ.monic
      (fun l' => pow_dvd_monicPoly_sub_coeff hπ h l') j.1 l
  have hdeg : (dev φ (monicPoly a - monicPoly a') j.1).degree
      < ((φ.natDegree : ℕ) : WithBot ℕ) := by
    have h1 := degree_dev_lt hφ.monic hφ.pos (monicPoly a - monicPoly a') j.1
    rwa [Polynomial.degree_eq_natDegree hφ.monic.ne_zero] at h1
  have hmk := (unram_pow_dvd_mk_iff hφ.monic hdeg N).mpr
    (fun l _ => hdvd l)
  show (algebraMap O (AdjoinRoot φ) π) ^ N
    ∣ (devT φ k (monicPoly a)).coeff j.1 - (devT φ k (monicPoly a')).coeff j.1
  rw [devT_coeff _ (le_of_lt j.isLt), devT_coeff _ (le_of_lt j.isLt), ← map_sub, hsub]
  exact hmk

/-- ★ **Inbound level exactness at the unramified stage**: level-`N` `O₁`-classes
transport back to level-`N` `O`-classes (the canonical representatives of
`π^N`-congruent coefficients are `π^N`-congruent, coefficientwise). -/
private theorem unramReassVec_congr (hφ : IsKey φ) (hπ : Irreducible π) {k N : ℕ}
    {b b' : Fin k → AdjoinRoot φ}
    (h : proj (AdjoinRoot φ) k N b = proj (AdjoinRoot φ) k N b') :
    proj O (φ.natDegree * k) N (unramReassVec φ hφ.monic k b)
      = proj O (φ.natDegree * k) N (unramReassVec φ hφ.monic k b') := by
  haveI : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  -- every slot's representative difference is `π^N`-divisible, coefficientwise
  have hrep : ∀ j : ℕ, ∀ l, π ^ N
      ∣ (AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b).coeff j)
          - AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b').coeff j)).coeff l := by
    intro j l
    have hcl : (algebraMap O (AdjoinRoot φ) π) ^ N
        ∣ (monicPoly b).coeff j - (monicPoly b').coeff j :=
      (res_mk_eq_iff hπ₁).mp (by
        have h1 := pow_dvd_monicPoly_sub_coeff hπ₁ h j
        rw [Polynomial.coeff_sub] at h1
        exact (res_mk_eq_iff hπ₁).mpr h1)
    obtain ⟨y, hy⟩ := hcl
    obtain ⟨Y, hY⟩ := AdjoinRoot.mk_surjective y
    have hmkY : (monicPoly b).coeff j - (monicPoly b').coeff j
        = AdjoinRoot.mk φ (Polynomial.C (π ^ N) * Y) := by
      rw [hy, ← hY, map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.algebraMap_eq]
    have hmbm : AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b).coeff j)
          - AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b').coeff j)
        = (Polynomial.C (π ^ N) * Y) %ₘ φ := by
      rw [← map_sub, hmkY, AdjoinRoot.modByMonicHom_mk]
    rw [hmbm, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic,
      Polynomial.coeff_smul, smul_eq_mul]
    exact dvd_mul_right _ _
  funext i
  refine (res_mk_eq_iff hπ).mpr ?_
  show π ^ N ∣ (reassT φ hφ.monic k (monicPoly b)).coeff i.1
    - (reassT φ hφ.monic k (monicPoly b')).coeff i.1
  have hdiff : reassT φ hφ.monic k (monicPoly b) - reassT φ hφ.monic k (monicPoly b')
      = ∑ j ∈ Finset.range (k + 1),
          (AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b).coeff j)
            - AdjoinRoot.modByMonicHom hφ.monic ((monicPoly b').coeff j)) * φ ^ j := by
    rw [reassT, reassT, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← Polynomial.coeff_sub, hdiff, Polynomial.finsetSum_coeff]
  refine Finset.dvd_sum fun j _ => ?_
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum fun uv _ => ?_
  exact Dvd.dvd.mul_right (hrep j uv.1) _

/-- The exact round trip on canonical lifts (outbound then inbound). -/
private theorem unramReassVec_unramDevVec (hφ : IsKey φ) (k : ℕ)
    (a : Fin (φ.natDegree * k) → O) :
    unramReassVec φ hφ.monic k (unramDevVec φ k a) = a := by
  have hdeg : (monicPoly a).natDegree = φ.natDegree * k := monicPoly_natDegree a
  have hmon := devT_monic (φ := φ) (k := k) hφ.monic hφ.pos (monicPoly_monic a) hdeg
  have hfun : monicPoly (unramDevVec φ k a) = devT φ k (monicPoly a) :=
    monicPoly_coeff_self hmon.1 hmon.2
  have hlt : (monicPoly a).natDegree < (k + 1) * φ.natDegree := by
    rw [hdeg, Nat.add_mul, Nat.one_mul, Nat.mul_comm φ.natDegree k]
    have := hφ.pos
    omega
  funext i
  show (reassT φ hφ.monic k (monicPoly (unramDevVec φ k a))).coeff i.1 = a i
  rw [hfun, reassT_devT hφ.monic hφ.pos hlt]
  exact monicPoly_coeff_lt a i.isLt

/-- The exact round trip on canonical lifts (inbound then outbound). -/
private theorem unramDevVec_unramReassVec (hφ : IsKey φ) (k : ℕ)
    (b : Fin k → AdjoinRoot φ) :
    unramDevVec φ k (unramReassVec φ hφ.monic k b) = b := by
  have hre := reassT_monic (φ := φ) hφ.monic hφ.pos (monicPoly_monic b)
    (monicPoly_natDegree b)
  have hfun : monicPoly (unramReassVec φ hφ.monic k b) = reassT φ hφ.monic k (monicPoly b) :=
    monicPoly_coeff_self hre.1 hre.2
  funext j
  show (devT φ k (monicPoly (unramReassVec φ hφ.monic k b))).coeff j.1 = b j
  rw [hfun, devT_reassT hφ.monic hφ.pos (le_of_eq (monicPoly_natDegree b))]
  exact monicPoly_coeff_lt b j.isLt

/-- ★★ **THE UNRAMIFIED CELL TRANSPORT**: the `φ`-adic dev-transform bijection DESCENDS
to the finite coefficient boxes at the UNRAMIFIED stage — level-`N` classes of monic
degree-`(deg φ)·k` blocks over `O` correspond exactly to level-`N` classes of monic
degree-`k` blocks over `O₁ = AdjoinRoot φ`.  The level is UNCHANGED (`e(K'/K) = 1`,
against IFCG43's `N ↦ e'·N` at the Eisenstein stage); the count base reindexes
`q ↦ q^{deg φ}` (`residueCard_adjoinRoot`).  Uniform in `q, φ, k, N`, every complete
DVR. -/
noncomputable def unramCellTransport (hφ : IsKey φ) (hπ : Irreducible π) (k N : ℕ) :
    Coeff O (φ.natDegree * k) N ≃ Coeff (AdjoinRoot φ) k N where
  toFun x := proj (AdjoinRoot φ) k N
    (unramDevVec φ k (proj_surjective O (φ.natDegree * k) N x).choose)
  invFun y := proj O (φ.natDegree * k) N
    (unramReassVec φ hφ.monic k (proj_surjective (AdjoinRoot φ) k N y).choose)
  left_inv := fun x => by
    have ha : proj O (φ.natDegree * k) N
        (proj_surjective O (φ.natDegree * k) N x).choose = x :=
      (proj_surjective O (φ.natDegree * k) N x).choose_spec
    have hb : proj (AdjoinRoot φ) k N
        (proj_surjective (AdjoinRoot φ) k N
          (proj (AdjoinRoot φ) k N
            (unramDevVec φ k
              (proj_surjective O (φ.natDegree * k) N x).choose))).choose
        = proj (AdjoinRoot φ) k N
            (unramDevVec φ k (proj_surjective O (φ.natDegree * k) N x).choose) :=
      (proj_surjective (AdjoinRoot φ) k N _).choose_spec
    have h1 := unramReassVec_congr (π := π) hφ hπ hb
    rw [unramReassVec_unramDevVec hφ k _] at h1
    exact h1.trans ha
  right_inv := fun y => by
    have hb : proj (AdjoinRoot φ) k N
        (proj_surjective (AdjoinRoot φ) k N y).choose = y :=
      (proj_surjective (AdjoinRoot φ) k N y).choose_spec
    have ha : proj O (φ.natDegree * k) N (proj_surjective O (φ.natDegree * k) N
        (proj O (φ.natDegree * k) N (unramReassVec φ hφ.monic k
          (proj_surjective (AdjoinRoot φ) k N y).choose))).choose
        = proj O (φ.natDegree * k) N (unramReassVec φ hφ.monic k
            (proj_surjective (AdjoinRoot φ) k N y).choose) :=
      (proj_surjective O (φ.natDegree * k) N _).choose_spec
    have h1 := unramDevVec_congr (π := π) hφ hπ ha
    rw [unramDevVec_unramReassVec hφ k _] at h1
    exact h1.trans hb

/-- ★ The unramified transport is computed on ANY lift by the transform vector. -/
theorem unramCellTransport_apply (hφ : IsKey φ) (hπ : Irreducible π) (k N : ℕ)
    (a : Fin (φ.natDegree * k) → O) :
    unramCellTransport hφ hπ k N (proj O (φ.natDegree * k) N a)
      = proj (AdjoinRoot φ) k N (unramDevVec φ k a) :=
  unramDevVec_congr hφ hπ
    (proj_surjective O (φ.natDegree * k) N
      (proj O (φ.natDegree * k) N a)).choose_spec

/-- ★ The inverse unramified transport is computed on ANY lift by the reassembly. -/
theorem unramCellTransport_symm_apply (hφ : IsKey φ) (hπ : Irreducible π) (k N : ℕ)
    (b : Fin k → AdjoinRoot φ) :
    (unramCellTransport hφ hπ k N).symm (proj (AdjoinRoot φ) k N b)
      = proj O (φ.natDegree * k) N (unramReassVec φ hφ.monic k b) :=
  unramReassVec_congr hφ hπ
    (proj_surjective (AdjoinRoot φ) k N (proj (AdjoinRoot φ) k N b)).choose_spec

end UnramTransport

section CompositumTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE COMPOSITUM CELL TRANSPORT** (EFR's named missing instrument for the
`(1, d)` axis): over the mixed tower
`O → O₁ = AdjoinRoot φ → O₂ = AdjoinRoot (eisKey (algebraMap π) c₁ e')`, level-`N`
classes of monic degree-`(deg φ)·(e'·k)` blocks over `O` correspond exactly to
level-`e'·N` classes of monic degree-`k` blocks over the COMPOSITUM — the unramified
stage's transport (level fixed, `q ↦ q^{deg φ}`) composed with IFCG43's Eisenstein
stage (level `N ↦ e'·N`, `q` fixed).  Uniform in `q, φ, π, c₁, e', k, N`, every
complete DVR. -/
noncomputable def compCellTransport {φ : Polynomial O} (hφ : IsKey φ) {π : O}
    (hπ : Irreducible π) [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)] {c₁ : AdjoinRoot φ}
    (hc₁ : IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0) {e' : ℕ} (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [IsDiscreteValuationRing
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [Finite (ResidueField (AdjoinRoot φ))]
    [Finite (ResidueField (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))]
    (k N : ℕ) :
    Coeff O (φ.natDegree * (e' * k)) N
      ≃ Coeff (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) k (e' * N) :=
  haveI : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  (unramCellTransport hφ hπ (e' * k) N).trans
    (Uniformity.Density.IFCG43.cellTransport
      (irreducible_algebraMap_adjoinRoot hφ hπ) hc₁ he' k N)

/-- ★ **THE COMPOSITUM COUNT TRANSPORT**: the transport carries every cell set to a set
of the SAME cardinality — the counting content of "the mixed dev-transform carries
cells to cells". -/
theorem compCellTransport_card_image {φ : Polynomial O} (hφ : IsKey φ) {π : O}
    (hπ : Irreducible π) [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)] {c₁ : AdjoinRoot φ}
    (hc₁ : IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0) {e' : ℕ} (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [IsDiscreteValuationRing
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [Finite (ResidueField (AdjoinRoot φ))]
    [Finite (ResidueField (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))]
    (k N : ℕ) (S : Set (Coeff O (φ.natDegree * (e' * k)) N)) :
    Nat.card ((compCellTransport hφ hπ hc₁ he' k N) '' S) = Nat.card S :=
  Nat.card_image_of_injective (compCellTransport hφ hπ hc₁ he' k N).injective S

/-- ★ **THE COMPOSITUM BOX COUNT**: the recentred level-`e'·N` box over the compositum
counts `q^{d·k·e'·N}` (`d = deg φ`) — the `(1, d)` axis's normalization: the base is
`q^d` (unramified inertia) and the level is `e'·N` (Eisenstein ramification), so the
total exponent matches the base-ring box `q^{(d·e'·k)·N}` EXACTLY.  (This is the
bookkeeping identity the `(1, d)` frame sum consumes: no `q`-power is created or lost
by the mixed transport.) -/
theorem card_coeff_compositum {φ : Polynomial O} (hφ : IsKey φ) {π : O}
    (hπ : Irreducible π) [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)] {c₁ : AdjoinRoot φ}
    (hc₁ : IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0) {e' : ℕ} (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [IsDiscreteValuationRing
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [IsAdicComplete
      (maximalIdeal (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
    [Finite (ResidueField (AdjoinRoot φ))]
    [Finite (ResidueField (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))]
    (k N : ℕ) :
    Nat.card (Coeff (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))
        k (e' * N))
      = Nat.card (Coeff O (φ.natDegree * (e' * k)) N) := by
  obtain ⟨i1, i2, i3, i4, hAC, hcard, hK⟩ := compositum_recentring_stack hφ hπ hc₁ he'
  rw [card_coeff, card_coeff, hcard, ← pow_mul]
  congr 1
  ring

end CompositumTransport

end Uniformity.Density.IFCG64

end

section AxCheck
#print axioms Uniformity.Density.IFCG64.slopeCellDec
#print axioms Uniformity.Density.IFCG64.mixedFace_one_eq_biUnion
#print axioms Uniformity.Density.IFCG64.slopeCellDec_disjoint
#print axioms Uniformity.Density.IFCG64.card_mixedFace_one_eq_sum
#print axioms Uniformity.Density.IFCG64.slope_lattice_pins
#print axioms Uniformity.Density.IFCG64.slopeCellDec_eq_box_inter
#print axioms Uniformity.Density.IFCG64.card_slopeBox
#print axioms Uniformity.Density.IFCG64.card_mixedFace_one_eq_box_sum
#print axioms Uniformity.Density.IFCG64.unramScaleType_degree
#print axioms Uniformity.Density.IFCG64.unramScaleType_injective
#print axioms Uniformity.Density.IFCG64.scaleType_unramScaleType_comm
#print axioms Uniformity.Density.IFCG64.towerScaleType_degree
#print axioms Uniformity.Density.IFCG64.towerScaleType_injective
#print axioms Uniformity.Density.IFCG64.unramCellTransport
#print axioms Uniformity.Density.IFCG64.unramCellTransport_apply
#print axioms Uniformity.Density.IFCG64.unramCellTransport_symm_apply
#print axioms Uniformity.Density.IFCG64.compCellTransport
#print axioms Uniformity.Density.IFCG64.compCellTransport_card_image
#print axioms Uniformity.Density.IFCG64.card_coeff_compositum
end AxCheck
