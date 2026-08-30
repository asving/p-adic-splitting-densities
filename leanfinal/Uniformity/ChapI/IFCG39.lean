/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapB.B22
import Uniformity.ChapB.B32a
import Uniformity.ChapB.B39b
import Uniformity.ChapI.IFCG35
import Uniformity.ChapI.IFCG37
import Uniformity.ChapI.IFCG38

/-!
# Uniformity.ChapI.IFCG39 — [PSL 2026-08-30] the power sector: the recentring key,
the Eisenstein target ring, and the dev-transform reduction to smaller mass

Stage PSL of the cone census (design record `runs/wave-c/verdict_PSL.md`).  After
RECUR (`IFCG35`) the census front carries `PowerSectorLaw m σ` — the fractional
recentring arm of the remainder trichotomy: carrier classes whose minimal-face class
residual is a PROPER prime power `ψ^k` (`k ≥ 2`).  This file builds the second-order
Montes step for that sector at the x-frame:

* **§1 the canonical power data.**  `powerSector_data`: every power-sector class
  carries a unique face `(h, e')` with `e' ≥ 2`, a MONIC irreducible `ψ` with
  `ψ(0) ≠ 0`, and an exact equality `classResidualPoly = ψ ^ k`; the bookkeeping
  `e'·k·(deg ψ) ≤ m` gives the STRICT MASS DROP `2·k ≤ m`.
* **§2 the recentring key.**  `xKey π ψt h e' = Σ_i ψt_i·π^{h(d−i)}·X^{e'i}` — the
  x-frame composed key: the lift of `ψ` homogenized along the slope `h/e'`.  It is
  monic of degree `e'·d`, pure of slope `h/e'`, with x-frame residual exactly `ψ̄`,
  hence IRREDUCIBLE (`xKey_irreducible`, via IFCG37's Step I) — uniformly in
  `q, h, e', d`, every complete DVR.  (ChapC records generic irreducibility of its
  `composedKey` as absent; at the census x-frame it is now a theorem.)
* **§3 the Eisenstein target ring.**  At the `(h, d) = (1, 1)` sub-sector the key is
  `eisKey π c e' = X^{e'} + c·π` and `O' := AdjoinRoot (eisKey)` is a COMPLETE DVR,
  totally ramified of degree `e'` over `O`: the ramified analogue of the Quarry/IFCG27
  cascade (`eis_isDomain/isLocalRing/isDVR/isAdicComplete/finite_residueField`), with
  `residueCard O' = residueCard O` and `𝔪^K·O' = 𝔪'^{e'K}`.  The coordinate lattice
  `eis_root_pow_dvd_mk_iff` pins `α^w ∣ mk P ↔ π^{⌈(w−i)/e'⌉} ∣ P_i`.
* **§4 the recentring map.**  `devT φ k f = Σ_j mk(dev φ f j)·T^j` — the φ-adic
  development read over `AdjoinRoot φ` — with inverse `reassT` (the canonical
  representatives): a degree-graded bijection between monic degree-`D·k` polynomials
  over `O` and monic degree-`k` polynomials over `O'` (`devT_monic`, `reassT_monic`,
  `devT_reassT`, `reassT_devT`), at EVERY monic key.
* **§5 level exactness (the fScale bookkeeping).**  `devT_sub_root_pow_dvd` /
  `reassT_sub_pi_pow_dvd`: blocks congruent coefficientwise mod `π^N` over `O`
  correspond to transforms congruent coefficientwise mod `α^{e'·N}` over `O'`, BOTH
  directions — the finite level scales by exactly the ramification index (B.10's
  `dev_congr` composed with the lattice at `w = e'·N`).

## Honest scope (the exact surviving open set toward `PowerSectorLaw m σ`)

This file lands the sector's second-order Montes INSTRUMENTS unconditionally; the
sector law itself survives as the composite of four named legs, all now stated
against landed apparatus (see `runs/wave-c/verdict_PSL.md` for the full fence):
1. the residual-box transfer criterion at the face — C110's translate-residual
   criterion at `e' ≥ 2`: pure slope-`h/e'` block has residual `ψ^k` ⟺ its transform
   lies in the deep recentred box over `O'` (the binomial-triangular digit
   computation; §3's lattice + §4's transform are its ready coordinates);
2. the face-indexed cell decomposition of the power sector and the level-exact count
   identity (`powerSectorCount` = the recentred cell counts over `O'`, via §5);
3. the `ZcURLim` closure: the recentred families consume the strictly-smaller-mass
   laws INSTANTIATED AT `O'` — legal exactly because §3 proves `O'` is a complete DVR
   with finite residue field and UNCHANGED `residueCard` (the ∀-DVR uniformity of the
   law families pays here, `q' = q`);
4. the general-face (`d ≥ 2`) compositum: the unramified extension step (the landed
   IFCG27/29 cascade at the residual key) composed with THIS file's Eisenstein step —
   the two-step tower under the `xKey`.
The `eScale` type-descent Prop rides with leg 1–2 and is deferred to that unit.

## Axiom fence

The §2 key, the §3 ring cascade + lattice, and the §4–§5 transform apparatus are
PURE Lean core.  §1's power data inherits at most the owner-signed B.42 cite through
the landed IFCG26/28/38 transports on the `classResidualPoly` chain (the file's
AxCheck footer prints the ground truth).  The C.33 cites must NOT occur.  Zero
sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG39

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG35 (MinFaceAt classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos minFaceAt_unique minFaceAt_support
  powerSector powerSectorCount PowerSectorLaw remainderCarrier)
open Uniformity.Density.IFCG37 (xres resPoly_x_frame irreducible_resPoly_x_iff
  xres_natDegree_monic irreducible_of_pure_of_resPoly_irreducible exists_monic_lift)
open Uniformity.Density.IFCG38 (classResidualPoly_monic)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG27 (isPrecomplete_of_basis)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private copy). -/
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

/-- The canonical representative of an `AdjoinRoot` element has degree `< deg φ`. -/
private theorem degree_modByMonicHom_lt {φ : Polynomial O} (hφ : φ.Monic)
    (x : AdjoinRoot φ) :
    (AdjoinRoot.modByMonicHom hφ x).degree < φ.degree := by
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective x
  rw [← hQ, AdjoinRoot.modByMonicHom_mk]
  exact Polynomial.degree_modByMonic_lt Q hφ

/-- **Adic completeness transfers down a cofinal power**: if `J ^ k = I` with `k ≥ 1`,
then `I`-adic completeness of a module gives `J`-adic completeness (the two filtrations
are interleaved: `J^{kn} = I^n ≤ J^n`). -/
private theorem isAdicComplete_of_pow_eq {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} {k : ℕ} (hk : 0 < k) (hIJ : J ^ k = I)
    (h : IsAdicComplete I M) : IsAdicComplete J M := by
  have hpow : ∀ n : ℕ, (J ^ (k * n) : Ideal R) = I ^ n := fun n => by
    rw [pow_mul, hIJ]
  have hle : ∀ n : ℕ, (I ^ n : Ideal R) ≤ J ^ n := fun n => by
    rw [← hpow n]
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n hk)
  haveI hH : IsHausdorff J M := ⟨fun x hx => by
    -- Hausdorff: `⋂ J^n ≤ ⋂ I^n = 0`
    refine h.haus x fun n => ?_
    have h1 := hx (k * n)
    have h2 : ((J ^ (k * n) : Ideal R) • ⊤ : Submodule R M)
        = ((I ^ n : Ideal R) • ⊤ : Submodule R M) := by rw [hpow n]
    rwa [h2] at h1⟩
  haveI hPre : IsPrecomplete J M := ⟨fun {f} hf => by
    -- Precomplete: the `I`-limit of the subsequence `n ↦ f (k·n)` is a `J`-limit
    obtain ⟨L, hL⟩ := h.prec (f := fun n => f (k * n)) (fun {m n} hmn => by
      have h1 := hf (Nat.mul_le_mul_left k hmn)
      have h2 : ((J ^ (k * m) : Ideal R) • ⊤ : Submodule R M)
          = ((I ^ m : Ideal R) • ⊤ : Submodule R M) := by rw [hpow m]
      rwa [h2] at h1)
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD ((J ^ n : Ideal R) • ⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_left n hk)
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left (hle n)) (hL n))⟩
  exact IsAdicComplete.mk

end Kit

/-! ## §1 — the canonical power data and the mass drop -/

section PowerData

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The representation supply** (IFCG38's private block, replicated): on a minimal
face the canonical class residual IS every lift's side residual, with the side set,
finite support and height data exported (WFR §3 through `classResidualPoly_eq`). -/
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

/-- **The minimal-face degree bookkeeping**: `e' · deg(classResidualPoly) ≤ m` — the
residual's degree is the side degree of any lift, and the face spans at most `[0, m]`
(the monic point caps the abscissae). -/
private theorem classResidualPoly_natDegree_bound {π : O} (hπ : Irreducible π)
    {m K h e' : ℕ} {c : Coeff O m K} (hF : MinFaceAt c h e') :
    e' * (classResidualPoly π c h e').natDegree ≤ m := by
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hH₀
  rw [hcrp, hnd.1]
  unfold sideDeg
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  rw [hmax]
  calc e' * ((m - sideMin X (monicPoly a) h e' hne) / e')
      = ((m - sideMin X (monicPoly a) h e' hne) / e') * e' := Nat.mul_comm _ _
    _ ≤ m - sideMin X (monicPoly a) h e' hne := Nat.div_mul_le_self _ _
    _ ≤ m := Nat.sub_le _ _

/-- ★ **The canonical power-sector data**: unique face `(h, e')` with `e' ≥ 2`, a monic
irreducible `ψ` with nonzero constant term, an EXACT prime-power residual
`classResidualPoly = ψ ^ k` with `k ≥ 2`, and the degree bookkeeping
`e'·(k·deg ψ) ≤ m`. -/
theorem powerSector_data {m : ℕ} (σ : FactorizationType) {π : O} (hπ : Irreducible π)
    {M : ℕ} {c : Coeff O m (M + m)} (hc : c ∈ powerSector O π m σ M) :
    ∃ (h e' k : ℕ) (ψ : Polynomial (resField (X : Polynomial O))),
      MinFaceAt c h e' ∧ 2 ≤ e' ∧ ψ.Monic ∧ Irreducible ψ ∧ ψ.coeff 0 ≠ 0
        ∧ 2 ≤ k ∧ classResidualPoly π c h e' = ψ ^ k
        ∧ 1 ≤ ψ.natDegree ∧ e' * (k * ψ.natDegree) ≤ m := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨-, h, e', hF, -, ψ₀, k, hψ₀irr, hk, hassoc⟩ := hc
  -- the monic normalization of `ψ₀`
  have hψ₀ne : ψ₀ ≠ 0 := hψ₀irr.ne_zero
  have hlcu : IsUnit (Polynomial.C ψ₀.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hψ₀ne)))
  have hψm : (ψ₀ * Polynomial.C ψ₀.leadingCoeff⁻¹).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv hψ₀ne
  set ψ : Polynomial (resField (X : Polynomial O)) :=
    ψ₀ * Polynomial.C ψ₀.leadingCoeff⁻¹ with hψdef
  have hassocψ : Associated ψ₀ ψ := ⟨hlcu.unit, by rw [IsUnit.unit_spec]⟩
  have hψirr : Irreducible ψ := hassocψ.irreducible hψ₀irr
  -- the `Associated → =` upgrade through monicity (IFCG38's idiom)
  have heq : classResidualPoly π c h e' = ψ ^ k :=
    Polynomial.eq_of_monic_of_associated (classResidualPoly_monic hπ hF) (hψm.pow k)
      (hassoc.trans (Associated.pow_pow hassocψ))
  have hpos := classResidualPoly_natDegree_pos hπ hF
  -- degree positivity of `ψ`
  have hd1 : 1 ≤ ψ.natDegree := by
    by_contra hcon
    have h0 : ψ.natDegree = 0 := by omega
    have h1 : ψ = 1 := (Polynomial.Monic.natDegree_eq_zero hψm).mp h0
    rw [h1] at hψirr
    exact hψirr.not_isUnit isUnit_one
  -- the constant term through the prime power
  have hc0 : ψ.coeff 0 ≠ 0 := by
    intro h0
    apply hpos.2
    rw [heq, ← Polynomial.constantCoeff_apply, map_pow,
      Polynomial.constantCoeff_apply, h0, zero_pow (by omega : k ≠ 0)]
  -- the face bookkeeping
  have he'2 : 2 ≤ e' := by
    have h1 := hF.1
    have h2 := hF.2.1
    omega
  have hbound := classResidualPoly_natDegree_bound hπ hF
  rw [heq, Polynomial.natDegree_pow] at hbound
  exact ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hc0, hk, heq, hd1, hbound⟩

/-- ★ **THE MASS DROP**: the residual multiplicity — the mass of the recentred
recursion — is at most `m / 2`, strictly below the sector's own mass. -/
theorem powerSector_mass_drop {m : ℕ} (σ : FactorizationType) {π : O}
    (_hπ : Irreducible π) {M : ℕ} {c : Coeff O m (M + m)}
    (_hc : c ∈ powerSector O π m σ M) {h e' k : ℕ}
    {ψ : Polynomial (resField (X : Polynomial O))} (_hF : MinFaceAt c h e')
    (he' : 2 ≤ e') (hd : 1 ≤ ψ.natDegree) (hk : 2 ≤ k)
    (hle : e' * (k * ψ.natDegree) ≤ m) : 2 * k ≤ m ∧ k < m := by
  have h1 : 2 * k ≤ e' * (k * ψ.natDegree) := by
    calc 2 * k = 2 * (k * 1) := by rw [Nat.mul_one]
      _ ≤ e' * (k * ψ.natDegree) := Nat.mul_le_mul he' (Nat.mul_le_mul (le_refl k) hd)
  have h2 : 2 * k ≤ m := le_trans h1 hle
  exact ⟨h2, by omega⟩

end PowerData

/-! ## §2 — the recentring key at the x-frame -/

section XKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The x-frame composed key**: the monic lift `ψt` of the residual, homogenized
along the slope `h/e'` — `Σ_i ψt_i · π^{h(d−i)} · X^{e'·i}`, `d = deg ψt`. -/
def xKey (π : O) (ψt : Polynomial O) (h e' : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.range (ψt.natDegree + 1),
    Polynomial.C (ψt.coeff i * π ^ (h * (ψt.natDegree - i))) * Polynomial.X ^ (e' * i)

variable {π : O} {ψt : Polynomial O} {h e' : ℕ}

/-- The coefficients of the key: the value at `j` is the lattice read when `j = e'·i`
for some `i ≤ d`, and `0` otherwise. -/
theorem xKey_coeff (he' : 0 < e') (j : ℕ) :
    (xKey π ψt h e').coeff j
      = if hj : ∃ i, i ≤ ψt.natDegree ∧ j = e' * i then
          ψt.coeff hj.choose * π ^ (h * (ψt.natDegree - hj.choose))
        else 0 := by
  classical
  rw [xKey, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split
  · rename_i hj
    obtain ⟨hile, hjeq⟩ := hj.choose_spec
    rw [Finset.sum_eq_single hj.choose]
    · rw [if_pos hjeq, mul_one]
    · intro i' _ hne
      rw [if_neg, mul_zero]
      intro hcon
      exact hne (Nat.eq_of_mul_eq_mul_left he' (hcon.symm.trans hjeq))
    · intro hcon
      exact absurd (Finset.mem_range.mpr (by omega)) hcon
  · rename_i hj
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_neg, mul_zero]
    intro hcon
    exact hj ⟨i, by omega, hcon⟩

/-- The lattice coefficients of the key. -/
theorem xKey_coeff_mul (he' : 0 < e') {i : ℕ} (hi : i ≤ ψt.natDegree) :
    (xKey π ψt h e').coeff (e' * i) = ψt.coeff i * π ^ (h * (ψt.natDegree - i)) := by
  rw [xKey_coeff he']
  have hj : ∃ i', i' ≤ ψt.natDegree ∧ e' * i = e' * i' := ⟨i, hi, rfl⟩
  rw [dif_pos hj]
  obtain ⟨h1, h2⟩ := hj.choose_spec
  have : hj.choose = i := (Nat.eq_of_mul_eq_mul_left he' h2).symm
  rw [this]

/-- Off the `e'`-lattice (and above the top) the key's coefficients vanish. -/
theorem xKey_coeff_off (he' : 0 < e') {j : ℕ}
    (hj : ¬ ∃ i, i ≤ ψt.natDegree ∧ j = e' * i) : (xKey π ψt h e').coeff j = 0 := by
  rw [xKey_coeff he', dif_neg hj]

theorem xKey_monic (hψ : ψt.Monic) (_hd : 0 < ψt.natDegree) (he' : 0 < e') :
    (xKey π ψt h e').Monic ∧ (xKey π ψt h e').natDegree = e' * ψt.natDegree := by
  have htop : (xKey π ψt h e').coeff (e' * ψt.natDegree) = 1 := by
    rw [xKey_coeff_mul he' (le_refl _), Nat.sub_self, Nat.mul_zero, pow_zero, mul_one,
      ← Polynomial.leadingCoeff, hψ.leadingCoeff]
  have hle : (xKey π ψt h e').natDegree ≤ e' * ψt.natDegree := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have hi' := Finset.mem_range.mp hi
    exact Nat.mul_le_mul_left e' (by omega : i ≤ ψt.natDegree)
  have hmon : (xKey π ψt h e').Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hle htop
  refine ⟨hmon, le_antisymm hle (Polynomial.le_natDegree_of_ne_zero ?_)⟩
  rw [htop]
  exact one_ne_zero

/-- A residually nonzero element is a unit (kit). -/
private theorem isUnit_of_residue_ne_zero {x : O}
    (hx : IsLocalRing.residue O x ≠ 0) : IsUnit x := by
  by_contra hcon
  exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr hcon)))

/-- The valuation of a lattice coefficient is at least the line height, with equality
at the residually-visible slots. -/
private theorem xKey_addVal_lattice (hπ : Irreducible π) {i : ℕ} (hi : i ≤ ψt.natDegree)
    (he' : 0 < e') :
    ((h * (ψt.natDegree - i) : ℕ) : ℕ∞)
      ≤ IsDiscreteValuationRing.addVal O ((xKey π ψt h e').coeff (e' * i))
    ∧ (IsLocalRing.residue O (ψt.coeff i) ≠ 0 →
        IsDiscreteValuationRing.addVal O ((xKey π ψt h e').coeff (e' * i))
          = ((h * (ψt.natDegree - i) : ℕ) : ℕ∞)) := by
  rw [xKey_coeff_mul he' hi, IsDiscreteValuationRing.addVal_mul,
    addVal_pow_uniformizer hπ]
  constructor
  · exact le_add_self
  · intro hres
    rw [IsDiscreteValuationRing.addVal_eq_zero_iff.2 (isUnit_of_residue_ne_zero hres),
      zero_add]

/-- The key is PURE of slope `h/e'` (one side, spanning `[0, e'd]`). -/
theorem xKey_isPure (hπ : Irreducible π) (hψ : ψt.Monic) (hd : 0 < ψt.natDegree)
    (_hh : 0 < h) (he' : 0 < e')
    (hψ0 : IsLocalRing.residue O (ψt.coeff 0) ≠ 0) :
    IsPure (Polynomial.X : Polynomial O) (xKey π ψt h e') h e'
      ∧ npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e') 0
          = ((h * ψt.natDegree : ℕ) : ℕ∞) := by
  have hgdeg : (xKey π ψt h e').natDegree = e' * ψt.natDegree :=
    (xKey_monic (π := π) (h := h) hψ hd he').2
  -- the height at `0` is exactly `h·d`
  have h0eq : npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e') 0
      = ((h * ψt.natDegree : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    have hv := (xKey_addVal_lattice (π := π) (ψt := ψt) (h := h)
      hπ (Nat.zero_le _) he').2 hψ0
    rw [Nat.mul_zero] at hv
    rw [hv, Nat.sub_zero]
  -- the term function of the side `h/e'` at `0` and at the top
  have hterm0 : e' • npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e') 0
      + ((h * 0 : ℕ) : ℕ∞) = ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞) := by
    rw [h0eq, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_zero, Nat.cast_zero, add_zero]
    exact Nat.cast_inj.mpr (by ring)
  have htermtop : e' • npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e')
      (e' * ψt.natDegree) + ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞)
      = ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞) := by
    have htopc : (xKey π ψt h e').coeff (e' * ψt.natDegree) = 1 := by
      rw [xKey_coeff_mul he' (le_refl _), Nat.sub_self, Nat.mul_zero, pow_zero,
        mul_one, ← Polynomial.leadingCoeff, hψ.leadingCoeff]
    rw [npHgt_X, htopc, IsDiscreteValuationRing.addVal_eq_zero_iff.2 isUnit_one,
      smul_zero, zero_add]
  -- the lower bound at every abscissa
  have hbound : ∀ j ∈ Finset.range ((xKey π ψt h e').natDegree + 1),
      ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞)
        ≤ e' • npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e') j
            + ((h * j : ℕ) : ℕ∞) := by
    intro j _
    by_cases hlat : ∃ i, i ≤ ψt.natDegree ∧ j = e' * i
    · obtain ⟨i, hi, rfl⟩ := hlat
      have hlow := (xKey_addVal_lattice (π := π) (ψt := ψt) (h := h) hπ hi he').1
      rw [npHgt_X]
      have hkey : ((e' * (h * (ψt.natDegree - i)) : ℕ) : ℕ∞)
          ≤ e' • IsDiscreteValuationRing.addVal O ((xKey π ψt h e').coeff (e' * i)) := by
        rw [nsmul_eq_mul, Nat.cast_mul]
        exact mul_le_mul_right hlow _
      have hsum : ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞)
          = ((e' * (h * (ψt.natDegree - i)) : ℕ) : ℕ∞) + ((h * (e' * i) : ℕ) : ℕ∞) := by
        rw [← Nat.cast_add]
        refine Nat.cast_inj.mpr ?_
        obtain ⟨d', hd'⟩ : ∃ d', ψt.natDegree = i + d' := ⟨ψt.natDegree - i, by omega⟩
        rw [hd', (by omega : i + d' - i = d')]
        ring
      rw [hsum]
      exact add_le_add hkey (le_refl _)
    · have hcz : (xKey π ψt h e').coeff j = 0 := xKey_coeff_off he' hlat
      rw [npHgt_X, hcz, AddValuation.map_zero]
      have htp : e' • (⊤ : ℕ∞) = ⊤ := by
        rw [nsmul_eq_mul]
        exact WithTop.mul_top (Nat.cast_ne_zero.mpr he'.ne')
      rw [htp, top_add]
      exact le_top
  -- the support value is the line value
  have hsupp : suppVal (Polynomial.X : Polynomial O) (xKey π ψt h e') h e'
      = ((h * (e' * ψt.natDegree) : ℕ) : ℕ∞) := by
    rw [suppVal]
    refine le_antisymm ?_ (Finset.le_inf hbound)
    have h0mem : 0 ∈ Finset.range ((xKey π ψt h e').natDegree + 1) :=
      Finset.mem_range.mpr (by omega)
    exact le_of_le_of_eq (Finset.inf_le h0mem) hterm0
  refine ⟨⟨?_, ?_⟩, h0eq⟩
  · show e' • npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e') 0
      + ((h * 0 : ℕ) : ℕ∞) = suppVal (Polynomial.X : Polynomial O) (xKey π ψt h e') h e'
    rw [hterm0, hsupp]
  · show e' • npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e')
        ((xKey π ψt h e').natDegree / (Polynomial.X : Polynomial O).natDegree)
      + ((h * ((xKey π ψt h e').natDegree / (Polynomial.X : Polynomial O).natDegree)
          : ℕ) : ℕ∞)
      = suppVal (Polynomial.X : Polynomial O) (xKey π ψt h e') h e'
    rw [Polynomial.natDegree_X, Nat.div_one, hgdeg, htermtop, hsupp]

/-- The side data of the key: `sideMin = 0`, `sideMax = e'·d`, `sideDeg = d`. -/
theorem xKey_sideData (hπ : Irreducible π) (hψ : ψt.Monic) (hd : 0 < ψt.natDegree)
    (hh : 0 < h) (he' : 0 < e')
    (hψ0 : IsLocalRing.residue O (ψt.coeff 0) ≠ 0)
    (hne : (sideSet (Polynomial.X : Polynomial O) (xKey π ψt h e') h e').Nonempty) :
    sideMin (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne = 0
      ∧ sideMax (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne
          = e' * ψt.natDegree
      ∧ sideDeg (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne
          = ψt.natDegree := by
  have hgdeg : (xKey π ψt h e').natDegree = e' * ψt.natDegree :=
    (xKey_monic (π := π) (h := h) hψ hd he').2
  obtain ⟨⟨hOn0, hOntop⟩, -⟩ := xKey_isPure hπ hψ hd hh he' hψ0
  rw [Polynomial.natDegree_X, Nat.div_one, hgdeg] at hOntop
  have h0mem : 0 ∈ sideSet (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have htopmem : e' * ψt.natDegree
      ∈ sideSet (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' :=
    mem_sideSet_iff'.mpr ⟨by rw [hgdeg]; omega, hOntop⟩
  have hmin : sideMin (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne = 0 := by
    unfold sideMin
    exact Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  have hmax : sideMax (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne
      = e' * ψt.natDegree := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ _ htopmem)
    have hmem := Finset.max'_mem (sideSet (Polynomial.X : Polynomial O)
      (xKey π ψt h e') h e') hne
    obtain ⟨hlt, -⟩ := mem_sideSet_iff'.mp hmem
    rw [hgdeg] at hlt
    omega
  refine ⟨hmin, hmax, ?_⟩
  unfold sideDeg
  rw [hmin, hmax, Nat.sub_zero]
  exact Nat.mul_div_cancel_left _ he'

/-- The x-frame residual of the key IS the residual `ψ̄` it lifts. -/
theorem xKey_xres (hπ : Irreducible π) (hψ : ψt.Monic) (hd : 0 < ψt.natDegree)
    (hh : 0 < h) (he' : 0 < e')
    (hψ0 : IsLocalRing.residue O (ψt.coeff 0) ≠ 0)
    (hne : (sideSet (Polynomial.X : Polynomial O) (xKey π ψt h e') h e').Nonempty) :
    xres π (xKey π ψt h e') h e' hne (h * ψt.natDegree)
      = ψt.map (IsLocalRing.residue O) := by
  obtain ⟨hmin, -, hdeg⟩ := xKey_sideData hπ hψ hd hh he' hψ0 hne
  rw [xres, hmin, hdeg]
  have hRHS : ψt.map (IsLocalRing.residue O)
      = ∑ t ∈ Finset.range (ψt.natDegree + 1),
          Polynomial.C ((ψt.map (IsLocalRing.residue O)).coeff t) * Polynomial.X ^ t := by
    conv_lhs => rw [Polynomial.as_sum_range' (ψt.map (IsLocalRing.residue O))
      (ψt.natDegree + 1) (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
    simp only [Polynomial.C_mul_X_pow_eq_monomial]
  rw [hRHS]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ ψt.natDegree := by
    have := Finset.mem_range.mp ht
    omega
  congr 1
  rw [Polynomial.coeff_map]
  have hsub : h * ψt.natDegree - h * t = h * (ψt.natDegree - t) := by
    obtain ⟨d', hd'⟩ : ∃ d', ψt.natDegree = t + d' := ⟨ψt.natDegree - t, by omega⟩
    rw [hd', Nat.mul_add, (by omega : t + d' - t = d')]
    omega
  rw [Nat.zero_add, hsub, xKey_coeff_mul he' ht']
  exact congrArg Polynomial.C (digAt_eq hπ (mul_comm _ _))

/-- ★★ **THE KEY IS IRREDUCIBLE** — uniformly in `q, h, e', d`, every complete DVR:
IFCG37's Step I fires on the pure block with irreducible residual.  (This is the
x-frame instance of the composed-key irreducibility ChapC records as generically
absent.) -/
theorem xKey_irreducible [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (hπ : Irreducible π) (hψ : ψt.Monic) (hd : 0 < ψt.natDegree)
    (hh : 0 < h) (he' : 0 < e') (hcop : Nat.Coprime h e')
    (hψirr : Irreducible (ψt.map (IsLocalRing.residue O)))
    (hψ0 : IsLocalRing.residue O (ψt.coeff 0) ≠ 0) :
    Irreducible (xKey π ψt h e') := by
  have hne := sideSet_nonempty_gen (Polynomial.X : Polynomial O) (xKey π ψt h e') h e'
  obtain ⟨hpure, hH0⟩ := xKey_isPure hπ hψ hd hh he' hψ0
  obtain ⟨hmin, -, -⟩ := xKey_sideData hπ hψ hd hh he' hψ0 hne
  have hH : npHgt (Polynomial.X : Polynomial O) (xKey π ψt h e')
      (sideMin (Polynomial.X : Polynomial O) (xKey π ψt h e') h e' hne)
        = ((h * ψt.natDegree : ℕ) : ℕ∞) := by
    rw [hmin]
    exact hH0
  have hirr : Irreducible (resPoly π (Polynomial.X : Polynomial O) (xKey π ψt h e')
      h e' hne (h * ψt.natDegree)) := by
    rw [irreducible_resPoly_x_iff, xKey_xres hπ hψ hd hh he' hψ0 hne]
    exact hψirr
  exact irreducible_of_pure_of_resPoly_irreducible hπ hh he' hcop
    (xKey_monic (π := π) (h := h) hψ hd he').1 hpure hne hH hirr

end XKey

/-! ## §3 — the Eisenstein target ring (the `(h, d) = (1, 1)` sub-sector) -/

section Eisenstein

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The Eisenstein recentring key** at a unit `c`: `X^{e'} + c·π`. -/
def eisKey (π c : O) (e' : ℕ) : Polynomial O :=
  Polynomial.X ^ e' + Polynomial.C (c * π)

variable {π c : O} {e' : ℕ}

theorem eisKey_monic (he' : 0 < e') : (eisKey π c e').Monic :=
  Polynomial.monic_X_pow_add_C _ he'.ne'

theorem eisKey_natDegree (_he' : 0 < e') : (eisKey π c e').natDegree = e' := by
  rw [eisKey, Polynomial.natDegree_X_pow_add_C]

/-- The Eisenstein key is the `(h, d) = (1, 1)` composed key. -/
theorem eisKey_eq_xKey (_he' : 0 < e') :
    eisKey π c e' = xKey π (Polynomial.X + Polynomial.C c) 1 e' := by
  rw [xKey, Polynomial.natDegree_X_add_C, Finset.sum_range_succ, Finset.sum_range_one]
  have hc0 : (Polynomial.X + Polynomial.C c).coeff 0 = c := by simp
  have hc1 : (Polynomial.X + Polynomial.C c).coeff 1 = 1 := by
    simp
  rw [hc0, hc1, eisKey]
  norm_num
  ring

/-- ★ Irreducibility of the Eisenstein key (from `xKey_irreducible`). -/
theorem eisKey_irreducible [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e') :
    Irreducible (eisKey π c e') := by
  rw [eisKey_eq_xKey (by omega : 0 < e')]
  refine xKey_irreducible hπ (Polynomial.monic_X_add_C c)
    (by rw [Polynomial.natDegree_X_add_C]; exact Nat.one_pos) (by omega) (by omega)
    (Nat.coprime_one_left e') ?_ ?_
  · rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    have hsub : (Polynomial.X + Polynomial.C (IsLocalRing.residue O c))
        = Polynomial.X - Polynomial.C (-(IsLocalRing.residue O c)) := by
      rw [map_neg, sub_neg_eq_add]
    rw [hsub]
    exact Polynomial.irreducible_X_sub_C _
  · simpa using hc

/-- The root relation: `α^{e'} = −(c·π)` in `AdjoinRoot (eisKey π c e')`. -/
theorem eis_root_pow (_he' : 0 < e') :
    (AdjoinRoot.root (eisKey π c e')) ^ e'
      = - algebraMap O (AdjoinRoot (eisKey π c e')) (c * π) := by
  have h0 : AdjoinRoot.mk (eisKey π c e') (eisKey π c e') = 0 := AdjoinRoot.mk_self
  rw [eisKey] at h0
  rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h0
  rw [AdjoinRoot.algebraMap_eq]
  exact eq_neg_of_add_eq_zero_left h0

/-! ### the reduction at the root: `O' → k`, kernel `(α)` -/

/-- **The reduction-at-the-root map** `O' →+* ResidueField O`: `α ↦ 0`, `a ↦ ā` — the
Eisenstein constant term lies in the maximal ideal, so the evaluation is legal. -/
private noncomputable def eisRes (hπ : Irreducible π) (he' : 0 < e') :
    AdjoinRoot (eisKey π c e') →+* IsLocalRing.ResidueField O :=
  AdjoinRoot.lift (IsLocalRing.residue O) 0 (by
    rw [eisKey, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      zero_pow he'.ne', zero_add]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ c
      ((IsLocalRing.mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit))))

private theorem eisRes_mk (hπ : Irreducible π) (he' : 0 < e') (P : Polynomial O) :
    eisRes (c := c) hπ he' (AdjoinRoot.mk (eisKey π c e') P)
      = IsLocalRing.residue O (P.coeff 0) := by
  unfold eisRes
  rw [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero]

private theorem eisRes_algebraMap (hπ : Irreducible π) (he' : 0 < e') (a : O) :
    eisRes (c := c) hπ he' (algebraMap O (AdjoinRoot (eisKey π c e')) a)
      = IsLocalRing.residue O a := by
  unfold eisRes
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

private theorem eisRes_root (hπ : Irreducible π) (he' : 0 < e') :
    eisRes (c := c) hπ he' (AdjoinRoot.root (eisKey π c e')) = 0 := by
  unfold eisRes
  rw [AdjoinRoot.lift_root]

private theorem eisRes_surjective (hπ : Irreducible π) (he' : 0 < e') :
    Function.Surjective (eisRes (c := c) (π := π) hπ he') := by
  intro y
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := O) y
  exact ⟨algebraMap O (AdjoinRoot (eisKey π c e')) a, by rw [eisRes_algebraMap]; exact ha⟩

/-- The base uniformizer lands in `(α)`: `π = −c⁻¹·α^{e'}`. -/
private theorem eis_algebraMap_pi_mem (_hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') :
    algebraMap O (AdjoinRoot (eisKey π c e')) π
      ∈ Ideal.span {AdjoinRoot.root (eisKey π c e')} := by
  obtain ⟨u, hu⟩ := isUnit_of_residue_ne_zero hc
  have h1 : algebraMap O (AdjoinRoot (eisKey π c e')) π
      = - algebraMap O (AdjoinRoot (eisKey π c e')) ((u⁻¹ : Oˣ) : O)
          * (AdjoinRoot.root (eisKey π c e')) ^ e' := by
    rw [eis_root_pow he', neg_mul_neg, ← map_mul]
    congr 1
    rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
  rw [h1, (by omega : e' = (e' - 1) + 1), pow_succ, ← mul_assoc]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **The kernel of the reduction at the root is exactly `(α)`.** -/
private theorem eis_ker_eisRes (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') :
    RingHom.ker (eisRes (c := c) (π := π) hπ he')
      = Ideal.span {AdjoinRoot.root (eisKey π c e')} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [RingHom.mem_ker, eisRes_mk] at hx
    have hdvd : π ∣ P.coeff 0 := by
      have hmem : P.coeff 0 ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.mp hx
      rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, hb⟩ := hdvd
    obtain ⟨Q, hQ⟩ : (Polynomial.X : Polynomial O) ∣ (P - Polynomial.C (P.coeff 0)) := by
      rw [Polynomial.X_dvd_iff]
      simp
    have hP : P = Polynomial.C (P.coeff 0) + Polynomial.X * Q := by
      rw [← hQ]; ring
    rw [hP, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, hb, map_mul]
    refine Ideal.add_mem _ ?_
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    exact Ideal.mul_mem_right _ _ (eis_algebraMap_pi_mem hπ hc he')
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact eisRes_root hπ he'

/-- **`(α)` is maximal**: the reduction at the root is onto the residue field. -/
private theorem eis_span_root_isMaximal (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') :
    (Ideal.span {AdjoinRoot.root (eisKey π c e')}).IsMaximal := by
  rw [← eis_ker_eisRes (c := c) hπ hc he']
  exact RingHom.ker_isMaximal_of_surjective _ (eisRes_surjective hπ he')

/-! ### the coordinate lattice -/

private theorem eisKey_degree (he' : 0 < e') : (eisKey π c e').degree = (e' : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (eisKey_monic he').ne_zero, eisKey_natDegree he']

/-- Degree-bounded representatives are unique below the key degree (kit). -/
private theorem eis_eq_zero_of_mk_eq_zero (he' : 0 < e') {P : Polynomial O}
    (hP : P.degree < (e' : ℕ)) (h0 : AdjoinRoot.mk (eisKey π c e') P = 0) :
    P = 0 := by
  by_contra hne
  exact AdjoinRoot.mk_ne_zero_of_degree_lt (eisKey_monic he') hne
    (by rw [eisKey_degree he']; exact hP) h0

/-- The monomial fold: `mk (X^n) = mk (C ((−cπ)^{n/e'})) · α^{n % e'}`. -/
private theorem eis_mk_X_pow (he' : 0 < e') (n : ℕ) :
    AdjoinRoot.mk (eisKey π c e') (Polynomial.X ^ n)
      = AdjoinRoot.mk (eisKey π c e') (Polynomial.C ((-(c * π)) ^ (n / e')))
        * (AdjoinRoot.root (eisKey π c e')) ^ (n % e') := by
  have h1 : AdjoinRoot.mk (eisKey π c e') (Polynomial.C ((-(c * π)) ^ (n / e')))
      = (- algebraMap O (AdjoinRoot (eisKey π c e')) (c * π)) ^ (n / e') := by
    rw [show AdjoinRoot.mk (eisKey π c e') (Polynomial.C ((-(c * π)) ^ (n / e')))
        = algebraMap O (AdjoinRoot (eisKey π c e')) ((-(c * π)) ^ (n / e')) from rfl,
      map_pow, map_neg]
  rw [map_pow, AdjoinRoot.mk_X, h1]
  conv_lhs => rw [← Nat.div_add_mod n e']
  rw [pow_add, pow_mul, eis_root_pow he']

/-- The uniformizer through the key: `π = (−u⁻¹)·α^{e'}` with `u` the unit of `c`. -/
private theorem eis_algebraMap_pi (he' : 0 < e') (u : Oˣ) (hu : (u : O) = c) :
    algebraMap O (AdjoinRoot (eisKey π c e')) π
      = - algebraMap O (AdjoinRoot (eisKey π c e')) ((u⁻¹ : Oˣ) : O)
          * (AdjoinRoot.root (eisKey π c e')) ^ e' := by
  rw [eis_root_pow he', neg_mul_neg, ← map_mul]
  congr 1
  subst hu
  rw [← mul_assoc, Units.inv_mul, one_mul]

/-- ★ **The coordinate lattice** (instance-free): for `P` of degree `< e'`,
`α^w ∣ mk P ⟺ π^{⌈(w−i)/e'⌉} ∣ P_i` for every `i < e'` — the exact valuation
read of the power basis.  The ceiling is `(w + e' − 1 − i) / e'` (which is `0` for
`i ≥ w`). -/
theorem eis_root_pow_dvd_mk_iff (_hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') {P : Polynomial O}
    (hP : P.degree < (e' : ℕ)) (w : ℕ) :
    (AdjoinRoot.root (eisKey π c e')) ^ w ∣ AdjoinRoot.mk (eisKey π c e') P
      ↔ ∀ i < e', π ^ ((w + e' - 1 - i) / e') ∣ P.coeff i := by
  have hPnat : P.natDegree < e' := by
    rcases eq_or_ne P 0 with rfl | hne
    · rw [Polynomial.natDegree_zero]
      exact he'
    · have h1 := hP
      rw [Polynomial.degree_eq_natDegree hne] at h1
      exact_mod_cast h1
  constructor
  · -- ⇒ : fold the shifted block to its canonical representative and read the digits
    rintro ⟨y, hy⟩
    have hQmk : AdjoinRoot.mk (eisKey π c e')
        (AdjoinRoot.modByMonicHom (eisKey_monic he') y) = y :=
      AdjoinRoot.mk_leftInverse (eisKey_monic he') y
    set Q : Polynomial O := AdjoinRoot.modByMonicHom (eisKey_monic he') y with hQdef
    have hQdeg : Q.degree < (e' : ℕ) := by
      have h2 := degree_modByMonicHom_lt (eisKey_monic he') y
      rwa [eisKey_degree he'] at h2
    have hQnat : Q.natDegree < e' := by
      rcases eq_or_ne Q 0 with h0 | hne
      · rw [h0, Polynomial.natDegree_zero]
        exact he'
      · have h1 := hQdeg
        rw [Polynomial.degree_eq_natDegree hne] at h1
        exact_mod_cast h1
    set R : Polynomial O := ∑ j ∈ Finset.range e',
      Polynomial.C (Q.coeff j * (-(c * π)) ^ ((w + j) / e'))
        * Polynomial.X ^ ((w + j) % e') with hRdef
    have hmkP : AdjoinRoot.mk (eisKey π c e') P
        = AdjoinRoot.mk (eisKey π c e') (Polynomial.X ^ w * Q) := by
      rw [map_mul, map_pow, AdjoinRoot.mk_X, hQmk]
      exact hy
    have hmkR : AdjoinRoot.mk (eisKey π c e') (Polynomial.X ^ w * Q)
        = AdjoinRoot.mk (eisKey π c e') R := by
      conv_lhs => rw [Polynomial.as_sum_range' Q e' hQnat, Finset.mul_sum]
      rw [hRdef, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h5 : (Polynomial.X : Polynomial O) ^ w
            * Polynomial.monomial j (Q.coeff j)
          = Polynomial.C (Q.coeff j) * Polynomial.X ^ (w + j) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        ring
      have hL : AdjoinRoot.mk (eisKey π c e')
            (Polynomial.C (Q.coeff j) * Polynomial.X ^ (w + j))
          = AdjoinRoot.mk (eisKey π c e') (Polynomial.C (Q.coeff j))
            * (AdjoinRoot.mk (eisKey π c e')
                (Polynomial.C ((-(c * π)) ^ ((w + j) / e')))
              * (AdjoinRoot.root (eisKey π c e')) ^ ((w + j) % e')) := by
        rw [map_mul, eis_mk_X_pow he' (w + j)]
      have hR : AdjoinRoot.mk (eisKey π c e')
            (Polynomial.C (Q.coeff j * (-(c * π)) ^ ((w + j) / e'))
              * Polynomial.X ^ ((w + j) % e'))
          = AdjoinRoot.mk (eisKey π c e') (Polynomial.C (Q.coeff j))
            * (AdjoinRoot.mk (eisKey π c e')
                (Polynomial.C ((-(c * π)) ^ ((w + j) / e')))
              * (AdjoinRoot.root (eisKey π c e')) ^ ((w + j) % e')) := by
        rw [Polynomial.C_mul, map_mul, map_mul,
          map_pow (AdjoinRoot.mk (eisKey π c e')) Polynomial.X ((w + j) % e'),
          AdjoinRoot.mk_X, mul_assoc]
      rw [h5, hL, hR]
    have hRdeg : R.degree < (e' : ℕ) := by
      rw [hRdef]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j _
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast Nat.mod_lt _ he'
    have hPR : P = R := by
      have h0 : AdjoinRoot.mk (eisKey π c e') (P - R) = 0 := by
        rw [map_sub, hmkP, hmkR, sub_self]
      have hdeg2 : (P - R).degree < (e' : ℕ) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hP hRdeg)
      exact sub_eq_zero.mp (eis_eq_zero_of_mk_eq_zero he' hdeg2 h0)
    intro i _
    rw [hPR, hRdef, Polynomial.finsetSum_coeff]
    refine Finset.dvd_sum fun j hj => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hij : i = (w + j) % e'
    · rw [if_pos hij, mul_one]
      have hle : (w + e' - 1 - i) / e' ≤ (w + j) / e' := by
        have hdm := Nat.div_add_mod (w + j) e'
        have hlt : (w + e' - 1 - i) / e' < (w + j) / e' + 1 := by
          rw [Nat.div_lt_iff_lt_mul he']
          have h6 : ((w + j) / e' + 1) * e' = e' * ((w + j) / e') + e' := by ring
          have hj' : j < e' := Finset.mem_range.mp hj
          omega
        omega
      have h7 : (-(c * π)) ^ ((w + j) / e')
          = (-c) ^ ((w + j) / e') * π ^ ((w + j) / e') := by
        rw [← mul_pow, neg_mul]
      rw [h7]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (pow_dvd_pow π hle) _) _
    · rw [if_neg hij, mul_zero]
      exact dvd_zero _
  · -- ⇐ : divide monomial by monomial through the fold
    intro hdvd
    rw [Polynomial.as_sum_range' P e' hPnat, map_sum]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i < e' := Finset.mem_range.mp hi
    obtain ⟨b, hb⟩ := hdvd i hi'
    have h5 : Polynomial.monomial i (P.coeff i)
        = Polynomial.C (P.coeff i) * Polynomial.X ^ i :=
      (Polynomial.C_mul_X_pow_eq_monomial).symm
    rw [h5, hb, map_mul, map_pow, AdjoinRoot.mk_X]
    have h6 : AdjoinRoot.mk (eisKey π c e')
          (Polynomial.C (π ^ ((w + e' - 1 - i) / e') * b))
        = (algebraMap O (AdjoinRoot (eisKey π c e')) π) ^ ((w + e' - 1 - i) / e')
          * algebraMap O (AdjoinRoot (eisKey π c e')) b := by
      rw [show AdjoinRoot.mk (eisKey π c e')
            (Polynomial.C (π ^ ((w + e' - 1 - i) / e') * b))
          = algebraMap O (AdjoinRoot (eisKey π c e'))
              (π ^ ((w + e' - 1 - i) / e') * b) from rfl, map_mul, map_pow]
    obtain ⟨u, hu⟩ := isUnit_of_residue_ne_zero hc
    rw [h6, eis_algebraMap_pi he' u hu, mul_pow, ← pow_mul]
    have hwle : w ≤ e' * ((w + e' - 1 - i) / e') + i := by
      have hdm := Nat.div_add_mod (w + e' - 1 - i) e'
      have hmod : (w + e' - 1 - i) % e' < e' := Nat.mod_lt _ he'
      omega
    refine dvd_trans (pow_dvd_pow (AdjoinRoot.root (eisKey π c e')) hwle) ?_
    rw [pow_add]
    exact mul_dvd_mul ((dvd_mul_left _ _).mul_right _) (dvd_refl _)

/-! ### the cascade: `AdjoinRoot (eisKey)` is a complete DVR, totally ramified -/

theorem eis_isDomain [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e') :
    IsDomain (AdjoinRoot (eisKey π c e')) :=
  (Ideal.Quotient.isDomain_iff_prime (Ideal.span {eisKey π c e'})).mpr
    ((Ideal.span_singleton_prime (eisKey_monic (by omega : 0 < e')).ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (eisKey_irreducible hπ hc he')))

theorem eis_isLocalRing (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') : IsLocalRing (AdjoinRoot (eisKey π c e')) := by
  have he'' : 0 < e' := by omega
  haveI : Module.Finite O (AdjoinRoot (eisKey π c e')) :=
    (eisKey_monic he'').finite_adjoinRoot
  haveI : Algebra.IsIntegral O (AdjoinRoot (eisKey π c e')) :=
    Algebra.IsIntegral.of_finite O _
  refine IsLocalRing.of_unique_max_ideal
    ⟨Ideal.span {AdjoinRoot.root (eisKey π c e')},
      eis_span_root_isMaximal hπ hc he'', fun M hM => ?_⟩
  -- `M` contracts to `𝔪` by integrality, so `π ∈ M`, so `α^{e'} = −cπ ∈ M`, so `α ∈ M`
  have hcomap : (M.comap (algebraMap O (AdjoinRoot (eisKey π c e')))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hpiM : algebraMap O (AdjoinRoot (eisKey π c e')) π ∈ M := by
    have hpi : π ∈ M.comap (algebraMap O (AdjoinRoot (eisKey π c e'))) := by
      rw [IsLocalRing.eq_maximalIdeal hcomap]
      exact (IsLocalRing.mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
    exact hpi
  have hpow : (AdjoinRoot.root (eisKey π c e')) ^ e' ∈ M := by
    rw [eis_root_pow he'']
    exact neg_mem (by rw [map_mul]; exact Ideal.mul_mem_left _ _ hpiM)
  have hroot : AdjoinRoot.root (eisKey π c e') ∈ M :=
    hM.isPrime.mem_of_pow_mem e' hpow
  have hle : Ideal.span {AdjoinRoot.root (eisKey π c e')} ≤ M := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hroot
  exact ((eis_span_root_isMaximal hπ hc he'').eq_of_le hM.ne_top hle).symm

theorem eis_maximalIdeal_eq (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') [IsLocalRing (AdjoinRoot (eisKey π c e'))] :
    maximalIdeal (AdjoinRoot (eisKey π c e'))
      = Ideal.span {AdjoinRoot.root (eisKey π c e')} :=
  (IsLocalRing.eq_maximalIdeal (eis_span_root_isMaximal hπ hc (by omega))).symm

/-- The root is nonzero (its `e'`-th power is a unit multiple of `π ≠ 0`). -/
private theorem eis_root_ne_zero (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey π c e'))] :
    AdjoinRoot.root (eisKey π c e') ≠ 0 := by
  have he'' : 0 < e' := by omega
  have hinj : Function.Injective (algebraMap O (AdjoinRoot (eisKey π c e'))) := by
    rw [AdjoinRoot.algebraMap_eq]
    refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
    rw [Polynomial.degree_eq_natDegree (eisKey_monic he'').ne_zero, eisKey_natDegree he'']
    exact_mod_cast (show e' ≠ 0 by omega)
  intro h0
  have h1 := eis_root_pow (π := π) (c := c) he''
  rw [h0, zero_pow he''.ne'] at h1
  have h2 : algebraMap O (AdjoinRoot (eisKey π c e')) (c * π) = 0 := by
    have h3 := h1.symm
    rwa [neg_eq_zero] at h3
  have h4 : (c * π : O) = 0 := hinj (by rw [h2, map_zero])
  exact mul_ne_zero (isUnit_of_residue_ne_zero hc).ne_zero hπ.ne_zero h4

theorem eis_isDVR [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey π c e'))]
    [IsLocalRing (AdjoinRoot (eisKey π c e'))] :
    IsDiscreteValuationRing (AdjoinRoot (eisKey π c e')) := by
  have hnotfield : ¬ IsField (AdjoinRoot (eisKey π c e')) := by
    intro hf
    have h1 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [eis_maximalIdeal_eq hπ hc he'] at h1
    exact eis_root_ne_zero hπ hc he' (by rwa [Ideal.span_singleton_eq_bot] at h1)
  refine ((IsDiscreteValuationRing.TFAE (AdjoinRoot (eisKey π c e')) hnotfield).out 4 0).mp ?_
  rw [eis_maximalIdeal_eq hπ hc he']
  exact ⟨⟨AdjoinRoot.root (eisKey π c e'), rfl⟩⟩

/-- Total ramification: `𝔪^K · O' = 𝔪'^{e'·K}`. -/
theorem eis_map_pow_maximalIdeal (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsLocalRing (AdjoinRoot (eisKey π c e'))] (K : ℕ) :
    ((maximalIdeal O) ^ K).map (algebraMap O (AdjoinRoot (eisKey π c e')))
      = (maximalIdeal (AdjoinRoot (eisKey π c e'))) ^ (e' * K) := by
  have he'' : 0 < e' := by omega
  have hcu : IsUnit c := isUnit_of_residue_ne_zero hc
  rw [eis_maximalIdeal_eq hπ hc he', hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
    (by rw [← pow_mul] : (AdjoinRoot.root (eisKey π c e')) ^ (e' * K)
      = ((AdjoinRoot.root (eisKey π c e')) ^ e') ^ K),
    eis_root_pow he'']
  -- `(−algebraMap(cπ))^K` is the unit `((−1)·algebraMap c)^K` times `algebraMap (π^K)`
  have h2 : (- algebraMap O (AdjoinRoot (eisKey π c e')) (c * π)) ^ K
      = ((- 1 : AdjoinRoot (eisKey π c e'))
          * algebraMap O (AdjoinRoot (eisKey π c e')) c) ^ K
        * algebraMap O (AdjoinRoot (eisKey π c e')) (π ^ K) := by
    rw [map_pow, map_mul]
    ring
  obtain ⟨U, hU⟩ := ((isUnit_one.neg.mul
    (hcu.map (algebraMap O (AdjoinRoot (eisKey π c e'))))).pow K)
  refine le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ?_)
    (Ideal.span_singleton_le_span_singleton.mpr ?_)
  · -- `(−algebraMap(cπ))^K ∣ algebraMap (π^K)`
    refine ⟨((U⁻¹ : (AdjoinRoot (eisKey π c e'))ˣ) : AdjoinRoot (eisKey π c e')), ?_⟩
    rw [h2, ← hU, mul_comm ((U : AdjoinRoot (eisKey π c e'))), mul_assoc,
      Units.mul_inv, mul_one]
  · -- `algebraMap (π^K) ∣ (−algebraMap(cπ))^K`
    refine ⟨((U : (AdjoinRoot (eisKey π c e'))ˣ) : AdjoinRoot (eisKey π c e')), ?_⟩
    rw [h2, ← hU, mul_comm]

theorem eis_isAdicComplete [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey π c e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))] :
    IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π c e')))
      (AdjoinRoot (eisKey π c e')) := by
  have he'' : 0 < e' := by omega
  haveI : Module.Finite O (AdjoinRoot (eisKey π c e')) :=
    (eisKey_monic he'').finite_adjoinRoot
  -- `𝔪'^{e'} = 𝔪·O'` — total ramification at `K = 1`
  have hcof : (maximalIdeal (AdjoinRoot (eisKey π c e'))) ^ e'
      = (maximalIdeal O).map (algebraMap O (AdjoinRoot (eisKey π c e'))) := by
    have h1 := eis_map_pow_maximalIdeal hπ hc he' 1
    rw [pow_one, Nat.mul_one] at h1
    exact h1.symm
  refine isAdicComplete_of_pow_eq he'' hcof ?_
  rw [IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal O) (AdjoinRoot (eisKey π c e')) :=
    isPrecomplete_of_basis (AdjoinRoot.powerBasis' (eisKey_monic he'')).basis _
  exact IsAdicComplete.mk

/-- **The residue-field equivalence**: reduction at the root identifies `k' = k`
(the extension is totally ramified). -/
private noncomputable def eisResidueEquiv (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsLocalRing (AdjoinRoot (eisKey π c e'))] :
    ResidueField (AdjoinRoot (eisKey π c e')) ≃+* ResidueField O := by
  have he'' : 0 < e' := by omega
  have hker : maximalIdeal (AdjoinRoot (eisKey π c e'))
      = RingHom.ker (eisRes (c := c) (π := π) hπ he'') := by
    rw [eis_maximalIdeal_eq hπ hc he', ← eis_ker_eisRes (c := c) hπ hc he'']
  exact (Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (eisRes_surjective hπ he''))

theorem eis_finite_residueField [Finite (ResidueField O)] (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsLocalRing (AdjoinRoot (eisKey π c e'))] :
    Finite (ResidueField (AdjoinRoot (eisKey π c e'))) :=
  Finite.of_equiv _ (eisResidueEquiv hπ hc he').symm.toEquiv

/-- The extension is totally ramified: the residue cardinality is UNCHANGED. -/
theorem eis_residueCard [Finite (ResidueField O)] (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey π c e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]
    [Finite (ResidueField (AdjoinRoot (eisKey π c e')))] :
    residueCard (AdjoinRoot (eisKey π c e')) = residueCard O :=
  Nat.card_congr (eisResidueEquiv hπ hc he').toEquiv

end Eisenstein

/-! ## §4 — the recentring map: the dev transform and its inverse -/

section DevTransform

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The dev transform** (the recentring map): the `φ`-adic development of `f`, read
over `O' = AdjoinRoot φ` — `Σ_{j ≤ k} mk(dev φ f j) · T^j`. -/
def devT (φ : Polynomial O) (k : ℕ) (f : Polynomial O) :
    Polynomial (AdjoinRoot φ) :=
  ∑ j ∈ Finset.range (k + 1),
    Polynomial.C (AdjoinRoot.mk φ (dev φ f j)) * Polynomial.X ^ j

/-- **The reassembly** (the inverse): the canonical degree-`< D` representatives of the
coefficients, against the powers of `φ`. -/
def reassT (φ : Polynomial O) (hφ : φ.Monic) (k : ℕ)
    (G : Polynomial (AdjoinRoot φ)) : Polynomial O :=
  ∑ j ∈ Finset.range (k + 1),
    (AdjoinRoot.modByMonicHom hφ (G.coeff j)) * φ ^ j

variable {φ : Polynomial O} {k : ℕ}

/-- `1 ≠ 0` in `AdjoinRoot φ` for a key of positive degree (kit). -/
private theorem adjoinRoot_one_ne_zero (_hφ : φ.Monic) (hD : 0 < φ.natDegree) :
    (1 : AdjoinRoot φ) ≠ 0 := by
  intro h1
  have h2 : φ ∣ 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_one]
    exact h1
  have h3 := Polynomial.natDegree_le_of_dvd h2 one_ne_zero
  rw [Polynomial.natDegree_one] at h3
  omega

theorem devT_coeff (f : Polynomial O) {j : ℕ} (hj : j ≤ k) :
    (devT φ k f).coeff j = AdjoinRoot.mk φ (dev φ f j) := by
  classical
  rw [devT, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro i _ hne
    rw [if_neg (fun hcon => hne hcon.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_range.mpr (by omega)) hcon

/-- The transform has degree at most `k` (kit). -/
private theorem devT_natDegree_le (f : Polynomial O) : (devT φ k f).natDegree ≤ k := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact le_trans (Polynomial.natDegree_monomial_le _)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- The transform of a monic block of degree `D·k` is monic of degree `k`. -/
theorem devT_monic (hφ : φ.Monic) (hD : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) (hdeg : f.natDegree = φ.natDegree * k) :
    (devT φ k f).Monic ∧ (devT φ k f).natDegree = k := by
  have htop : (devT φ k f).coeff k = 1 := by
    rw [devT_coeff f (le_refl k),
      dev_top (μ := k) hφ hD hf (by rw [hdeg, Nat.mul_comm]), map_one]
  have hmon : (devT φ k f).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ (devT_natDegree_le f) htop
  refine ⟨hmon,
    le_antisymm (devT_natDegree_le f) (Polynomial.le_natDegree_of_ne_zero ?_)⟩
  rw [htop]
  exact adjoinRoot_one_ne_zero hφ hD

theorem devT_reassT (hφ : φ.Monic) (hD : 0 < φ.natDegree)
    {G : Polynomial (AdjoinRoot φ)} (hG : G.natDegree ≤ k) :
    devT φ k (reassT φ hφ k G) = G := by
  have hdig : ∀ j < k + 1,
      AdjoinRoot.modByMonicHom hφ (G.coeff j) = dev φ (reassT φ hφ k G) j :=
    dev_unique hφ hD (fun j => degree_modByMonicHom_lt hφ (G.coeff j)) rfl
  refine Polynomial.ext fun j => ?_
  by_cases hj : j ≤ k
  · rw [devT_coeff _ hj, ← hdig j (by omega)]
    exact AdjoinRoot.mk_leftInverse hφ (G.coeff j)
  · rw [not_le] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (devT_natDegree_le _) hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hG hj)]

theorem reassT_devT (hφ : φ.Monic) (hD : 0 < φ.natDegree) {f : Polynomial O}
    (hdeg : f.natDegree < (k + 1) * φ.natDegree) :
    reassT φ hφ k (devT φ k f) = f := by
  have h1 : ∀ j ∈ Finset.range (k + 1),
      AdjoinRoot.modByMonicHom hφ ((devT φ k f).coeff j) * φ ^ j
        = dev φ f j * φ ^ j := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [devT_coeff f hj', AdjoinRoot.modByMonicHom_mk,
      (Polynomial.modByMonic_eq_self_iff hφ).mpr (degree_dev_lt hφ hD f j)]
  rw [reassT, Finset.sum_congr rfl h1, sum_dev_eq hφ hD f hdeg]

/-- The reassembly of a monic degree-`k` polynomial is monic of degree `D·k`. -/
theorem reassT_monic (hφ : φ.Monic) (hD : 0 < φ.natDegree)
    {G : Polynomial (AdjoinRoot φ)} (hG : G.Monic) (hGdeg : G.natDegree = k) :
    (reassT φ hφ k G).Monic ∧ (reassT φ hφ k G).natDegree = φ.natDegree * k := by
  -- the top representative is `1`
  have hone : (1 : Polynomial O) %ₘ φ = 1 :=
    (Polynomial.modByMonic_eq_self_iff hφ).mpr
      (by rw [Polynomial.degree_one]
          exact Polynomial.natDegree_pos_iff_degree_pos.mp hD)
  have hak : AdjoinRoot.modByMonicHom hφ (G.coeff k) = 1 := by
    have h1 : G.coeff k = 1 := by
      rw [← hGdeg]
      exact hG.coeff_natDegree
    rw [h1, show (1 : AdjoinRoot φ) = AdjoinRoot.mk φ 1 from (map_one _).symm,
      AdjoinRoot.modByMonicHom_mk, hone]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the reassembly is `1`
    have h2 : reassT φ hφ 0 G = 1 := by
      rw [reassT, Finset.sum_range_one, pow_zero, mul_one, hak]
    rw [h2]
    exact ⟨Polynomial.monic_one, by rw [Polynomial.natDegree_one, Nat.mul_zero]⟩
  · -- `k ≥ 1`: top term `φ^k`, the tail strictly below
    have hsplit : reassT φ hφ k G
        = (∑ j ∈ Finset.range k, AdjoinRoot.modByMonicHom hφ (G.coeff j) * φ ^ j)
          + φ ^ k := by
      rw [reassT, Finset.sum_range_succ, hak, one_mul]
    have hkD : 0 < k * φ.natDegree := Nat.mul_pos hk hD
    have ha : ∀ x : AdjoinRoot φ,
        (AdjoinRoot.modByMonicHom hφ x).natDegree ≤ φ.natDegree - 1 := by
      intro x
      by_cases hx : AdjoinRoot.modByMonicHom hφ x = 0
      · rw [hx, Polynomial.natDegree_zero]
        omega
      · have h3 := Polynomial.natDegree_lt_natDegree hx (degree_modByMonicHom_lt hφ x)
        omega
    have htail : (∑ j ∈ Finset.range k,
        AdjoinRoot.modByMonicHom hφ (G.coeff j) * φ ^ j).natDegree
          ≤ k * φ.natDegree - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      have hj' : j < k := Finset.mem_range.mp hj
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h4 : (φ ^ j).natDegree = j * φ.natDegree := hφ.natDegree_pow j
      have h5 : j * φ.natDegree ≤ (k - 1) * φ.natDegree :=
        Nat.mul_le_mul (by omega) (le_refl _)
      have h6 : (k - 1) * φ.natDegree = k * φ.natDegree - φ.natDegree := by
        rw [Nat.sub_mul, Nat.one_mul]
      have h7 := ha (G.coeff j)
      have h8 : φ.natDegree ≤ k * φ.natDegree := Nat.le_mul_of_pos_left _ hk
      rw [h4]
      omega
    have hmono : (φ ^ k).Monic := hφ.pow k
    have hdlt : (∑ j ∈ Finset.range k,
        AdjoinRoot.modByMonicHom hφ (G.coeff j) * φ ^ j).degree < (φ ^ k).degree := by
      have h9 : (φ ^ k).degree = ((k * φ.natDegree : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hmono.ne_zero, hφ.natDegree_pow]
      rw [h9]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast lt_of_le_of_lt htail (by omega)
    rw [hsplit]
    refine ⟨Polynomial.Monic.add_of_right hmono hdlt, ?_⟩
    rw [Polynomial.natDegree_add_eq_right_of_degree_lt hdlt, hφ.natDegree_pow,
      Nat.mul_comm]

end DevTransform

/-! ## §5 — level exactness of the recentring map (the fScale bookkeeping) -/

section LevelExact

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {π c : O} {e' k : ℕ}

/-- ★ **Level exactness, outbound**: coefficientwise congruence mod `π^N` of blocks
over `O` transports to coefficientwise congruence mod `α^{e'·N}` of their transforms
over `O' = AdjoinRoot (eisKey)` — the level scales by EXACTLY the ramification `e'`
(B.10's `dev_congr` composed with the coordinate lattice at `w = e'·N`, where the
ceiling collapses to `N` at every slot `i < e'`). -/
theorem devT_sub_root_pow_dvd (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') {N : ℕ} {f f' : Polynomial O}
    (h : ∀ l, π ^ N ∣ (f - f').coeff l) {j : ℕ} (hj : j ≤ k) :
    (AdjoinRoot.root (eisKey π c e')) ^ (e' * N)
      ∣ (devT (eisKey π c e') k f - devT (eisKey π c e') k f').coeff j := by
  have hDpos : 0 < (eisKey π c e').natDegree := by
    rw [eisKey_natDegree he']
    exact he'
  have hPdeg : (dev (eisKey π c e') f j - dev (eisKey π c e') f' j).degree
      < ((e' : ℕ) : WithBot ℕ) := by
    have h1 := degree_dev_lt (eisKey_monic he') hDpos f j
    have h2 := degree_dev_lt (eisKey_monic he') hDpos f' j
    rw [eisKey_degree he'] at h1 h2
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
  rw [Polynomial.coeff_sub, devT_coeff f hj, devT_coeff f' hj, ← map_sub,
    eis_root_pow_dvd_mk_iff hπ hc he' hPdeg (e' * N)]
  intro i hi
  have hexp : (e' * N + e' - 1 - i) / e' = N := by
    have h2 : e' * N + e' - 1 - i = e' * N + (e' - 1 - i) := by
      generalize e' * N = A
      omega
    rw [h2, Nat.mul_add_div he']
    have h4 : (e' - 1 - i) / e' = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hexp]
  exact dev_congr hπ (eisKey_monic he') h j i

/-- ★ **Level exactness, inbound**: coefficientwise congruence mod `α^{e'·N}` of
transforms descends to coefficientwise congruence mod `π^N` of the reassemblies —
the inverse bookkeeping (the lattice's forward read on canonical representatives). -/
theorem reassT_sub_pi_pow_dvd (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 0 < e') {N : ℕ}
    {G G' : Polynomial (AdjoinRoot (eisKey π c e'))}
    (h : ∀ j, (AdjoinRoot.root (eisKey π c e')) ^ (e' * N) ∣ (G - G').coeff j)
    (l : ℕ) :
    π ^ N ∣ (reassT (eisKey π c e') (eisKey_monic he') k G
      - reassT (eisKey π c e') (eisKey_monic he') k G').coeff l := by
  have hsub : reassT (eisKey π c e') (eisKey_monic he') k G
      - reassT (eisKey π c e') (eisKey_monic he') k G'
      = ∑ j ∈ Finset.range (k + 1),
          (AdjoinRoot.modByMonicHom (eisKey_monic he') ((G - G').coeff j))
            * (eisKey π c e') ^ j := by
    rw [reassT, reassT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_mul, Polynomial.coeff_sub, map_sub]
  rw [hsub, Polynomial.finsetSum_coeff]
  refine Finset.dvd_sum fun j _ => ?_
  -- the canonical representative of an `α^{e'N}`-divisible element has
  -- `π^N`-divisible coefficients (the lattice, forward)
  have hdeg : (AdjoinRoot.modByMonicHom (eisKey_monic he')
      ((G - G').coeff j)).degree < ((e' : ℕ) : WithBot ℕ) := by
    have h1 := degree_modByMonicHom_lt (eisKey_monic he') ((G - G').coeff j)
    rwa [eisKey_degree he'] at h1
  have hrep : ∀ i, π ^ N ∣ (AdjoinRoot.modByMonicHom (eisKey_monic he')
      ((G - G').coeff j)).coeff i := by
    have hdvd : (AdjoinRoot.root (eisKey π c e')) ^ (e' * N)
        ∣ AdjoinRoot.mk (eisKey π c e')
            (AdjoinRoot.modByMonicHom (eisKey_monic he') ((G - G').coeff j)) := by
      rw [AdjoinRoot.mk_leftInverse (eisKey_monic he') ((G - G').coeff j)]
      exact h j
    rw [eis_root_pow_dvd_mk_iff hπ hc he' hdeg (e' * N)] at hdvd
    intro i
    rcases lt_or_ge i e' with hi | hi
    · have hexp : (e' * N + e' - 1 - i) / e' = N := by
        have h2 : e' * N + e' - 1 - i = e' * N + (e' - 1 - i) := by
          generalize e' * N = A
          omega
        rw [h2, Nat.mul_add_div he']
        have h4 : (e' - 1 - i) / e' = 0 := Nat.div_eq_of_lt (by omega)
        omega
      have h5 := hdvd i hi
      rwa [hexp] at h5
    · have h5 : ((e' : ℕ) : WithBot ℕ) ≤ (i : WithBot ℕ) := by exact_mod_cast hi
      rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg h5)]
      exact dvd_zero _
  exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp
    (Dvd.dvd.mul_right ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hrep) _) l

end LevelExact

/-! ## §6 — the dd (2,2) instance: ER4's recentring ring -/

section DdInstance

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Anti-drift pin: ER4's order-2 recentring key `X² − bπ` (the E1 double-root
sector, IFCG34's record) IS the Eisenstein key at `c = −b`. -/
theorem eisKey_dd (π b : O) :
    eisKey π (-b) 2 = Polynomial.X ^ 2 - Polynomial.C (b * π) := by
  rw [eisKey, neg_mul, map_neg, ← sub_eq_add_neg]

/-- ★ **The (2,2) test**: the dd recentring ring `O[X]/(X² − bπ)` (`b` residually
nonzero) is a COMPLETE DVR with finite residue field of UNCHANGED cardinality — a
legal instantiation point for every ∀-DVR law family, at the SAME `q`.  The whole
§3 stack fires at `e' = 2` (CN5's incremental `haveI` telescope). -/
theorem dd_recentring_stack (π b : O) (hπ : Irreducible π)
    (hb : IsLocalRing.residue O b ≠ 0) :
    ∃ (_ : IsDomain (AdjoinRoot (eisKey π (-b) 2)))
      (_ : IsLocalRing (AdjoinRoot (eisKey π (-b) 2)))
      (_ : IsDiscreteValuationRing (AdjoinRoot (eisKey π (-b) 2)))
      (_ : Finite (ResidueField (AdjoinRoot (eisKey π (-b) 2)))),
      IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π (-b) 2)))
          (AdjoinRoot (eisKey π (-b) 2))
      ∧ residueCard (AdjoinRoot (eisKey π (-b) 2)) = residueCard O := by
  have hb' : IsLocalRing.residue O (-b) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact hb
  have he2 : (2 : ℕ) ≤ 2 := le_refl 2
  haveI hdom : IsDomain (AdjoinRoot (eisKey π (-b) 2)) := eis_isDomain hπ hb' he2
  haveI hloc : IsLocalRing (AdjoinRoot (eisKey π (-b) 2)) := eis_isLocalRing hπ hb' he2
  haveI hdvr : IsDiscreteValuationRing (AdjoinRoot (eisKey π (-b) 2)) :=
    eis_isDVR hπ hb' he2
  haveI hfin : Finite (ResidueField (AdjoinRoot (eisKey π (-b) 2))) :=
    eis_finite_residueField hπ hb' he2
  exact ⟨hdom, hloc, hdvr, hfin, eis_isAdicComplete hπ hb' he2,
    eis_residueCard hπ hb' he2⟩

end DdInstance

end Uniformity.Density.IFCG39

section AxCheck
#print axioms Uniformity.Density.IFCG39.powerSector_data
#print axioms Uniformity.Density.IFCG39.powerSector_mass_drop
#print axioms Uniformity.Density.IFCG39.xKey_xres
#print axioms Uniformity.Density.IFCG39.xKey_irreducible
#print axioms Uniformity.Density.IFCG39.eisKey_irreducible
#print axioms Uniformity.Density.IFCG39.eis_root_pow_dvd_mk_iff
#print axioms Uniformity.Density.IFCG39.eis_isDomain
#print axioms Uniformity.Density.IFCG39.eis_isLocalRing
#print axioms Uniformity.Density.IFCG39.eis_maximalIdeal_eq
#print axioms Uniformity.Density.IFCG39.eis_isDVR
#print axioms Uniformity.Density.IFCG39.eis_map_pow_maximalIdeal
#print axioms Uniformity.Density.IFCG39.eis_isAdicComplete
#print axioms Uniformity.Density.IFCG39.eis_finite_residueField
#print axioms Uniformity.Density.IFCG39.eis_residueCard
#print axioms Uniformity.Density.IFCG39.devT_monic
#print axioms Uniformity.Density.IFCG39.reassT_monic
#print axioms Uniformity.Density.IFCG39.devT_reassT
#print axioms Uniformity.Density.IFCG39.reassT_devT
#print axioms Uniformity.Density.IFCG39.devT_sub_root_pow_dvd
#print axioms Uniformity.Density.IFCG39.reassT_sub_pi_pow_dvd
#print axioms Uniformity.Density.IFCG39.eisKey_dd
#print axioms Uniformity.Density.IFCG39.dd_recentring_stack
end AxCheck
