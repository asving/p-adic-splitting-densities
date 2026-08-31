/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG61
import Uniformity.ChapI.IFCG66

/-!
# Uniformity.ChapI.IFCG67 — [DPN 2026-08-31] THE DEPTH PIN: the resultant valuation
of a pure face block against a steep cofactor is `h·d·(m − e'·d)` — machine-checked,
splitting-field-free, and fired into LSF's pinned-depth couplings

Unit DPN (design record `runs/wave-c/verdict_DPN.md`).  TBT (IFCG59) derived — but could
not machine-check — the ladder constant of the sub-face count: for the two-block split
`g·R` at a sub-face frame (`g` the `(h,e')`-pure face block of degree `e'·d`, `R` the
steep cofactor of degree `r = m − e'·d`), `v(Res(g, R)) = h·d·r`.  LSF (IFCG66) named it
THE DEPTH PIN — discharge pointer 1, the keystone of `SubfaceFrameLaw` — and proposed
route (a): the weighted-Leibniz Sylvester bound with `e'`-cleared integer weights.  This
file lands exactly that route:

* **§1 THE DETERMINANT PIN (lift side, any domain).**  Mathlib's `sylvester` is
  column-blocked (left block: `n` columns of the steep factor, band `r`; right block:
  `r` columns of the face block, band `n`).  Every Leibniz permutation `σ` satisfies the
  COLUMN TELESCOPE `Σ_c (offset(c) + band(c) − σ(c)) = n·r` (blockwise, after trading
  `Σ σ(c)` for `Σ c`), so cone-shaped coefficient weights (`e'·w ≥ h·(band − k)` at
  in-band position `k`) force every term's `e'`-cleared weight `≥ h·n·r` —
  `pow_dvd_resultant_of_cones`.  With the steep bounds STRICT, a term dodges the `+1`
  excess only if every steep column sits at its monic point, which FORCES `σ` to be the
  block-flip permutation `sylFlip` (an injective self-map of `Fin r` above the diagonal
  is the identity), whose term is `sign · (corner)^r` exactly — so the exact corner
  (`v(g₀) = h·d`, `π` prime) pins `¬ π^{h·d·r + 1} ∣ Res` —
  `not_pow_succ_dvd_resultant_of_cones`.  No splitting fields, no norm, no ceilings:
  divisibility and ℕ arithmetic only.
* **§2 ★★★ THE CLASS-LEVEL PIN** (`mixDepth_eq_of_cones`): on the lift-free depth
  instrument, purity + exact corner + strict steepness (all read through the windowed
  valuation `resOrd`) pin `mixDepth π c₁ c₂ = h·d·r` below the window — the exact key
  the census sockets consume.
* **§3 THE FRAME INSTANTIATION.**  `cone_data_of_isPure` converts B.34's lift-side
  `IsPure` (the polygon = one face, on-side at BOTH endpoints — so the exact corner is
  free) into the class-side cone data; `subface_depth_pin` re-runs LSF's pinned
  transport and appends THE PIN: every sub-face leaf cell lift splits with
  `mixDepth = h·d·(m − e'·d)` (below the window) — TBT's ladder constant, now a theorem.
* **§4 THE COUPLINGS FIRED.**  `natCard_pairNbhd_of_cones` (the `q^v` fiber law at the
  KNOWN `v`), `decidedAt_mulClass_of_cones` (the decidedness transfer at the shifted
  level, drainage premises carried honestly), `subface_cluster_law` (the leaf composite:
  every sub-face cell pair carries clusters of size EXACTLY `q^{h·d·(m−e'·d)}`), and the
  witness-frame regression (`m = 5`: pinned depths `{1, 3}` at the two frames).

## THE HONEST FENCE

NOT proved here (unchanged from LSF's discharge pointers 2–4): the STEEP CENSUS
(`SteepLaw`-to-be, the decided-`τ` count in the strict cone), the DRAINAGE premise
(shifted-level decidedness of the factor classes — consumed here as explicit
hypotheses of `decidedAt_mulClass_of_cones`), and the image characterization (which
box × census pairs land in `subfaceCell`).  `SubfaceFrameLaw` itself is NOT fired —
the pin closes its keystone, not its census legs.

## Axiom fence (machine-exact at landing)

§§1–2 and the abstract couplings are PURE Lean core `{propext, Classical.choice,
Quot.sound}`.  The §3/§4 leaf forms additionally inherit EXACTLY the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, through
LSF's `subface_transport_pinned` — never re-consumed).  The C.33 cites,
`AX_cellRecursion`, and `sorryAx` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG67

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal classCoeffVal_le le_classCoeffVal_iff_dvd
  classCoeffVal_exact resOrd_mk_eq)
open Uniformity.Density.IFCG23 (addVal_eq_of_pow_dvd_not_dvd)
open Uniformity.Density.IFCG41 (classRes classRes_proj mixDepth mixDepth_le mixDepth_dvd
  le_mixDepth mk_pow_dvd_mk_iff)
open Uniformity.Density.IFCG61 (mixDepth_eq_iff)
open Uniformity.Density.IFCG42 (pairNbhd natCard_pairNbhd_of_mixDepth
  decidedAt_mulClass_of_mixDepth)
open Uniformity.Density.IFCG35 (MinFaceAt classResidualPoly)
open Uniformity.Density.IFCG57 (leafSubSector)
open Uniformity.Density.IFCG66 (subface_transport_pinned class_strict_cone_of_side_singleton
  subFrames subfaceCell SubfaceFrameLaw subFrames_five_witness mem_subFrames_iff)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit: the Sylvester entry readers, the block-flip permutation, and the
per-column weights

Mathlib's `sylvester f g m n` (here `f` = the face block `monicPoly a₁` at size `n`,
`g` = the steep cofactor `monicPoly a₂` at size `r`) is COLUMN-blocked: the left block
(`Fin n`, offset `j₁`, band `r`) carries `g`'s coefficients ascending, the right block
(`Fin r`, offset `j₁`, band `n`) carries `f`'s. -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O]

/-- The coefficient of `monicPoly` at the degree abscissa is `1` (the monic point). -/
private theorem monicPoly_coeff_deg {k : ℕ} (a : Fin k → O) :
    (monicPoly a).coeff k = 1 := by
  have h := (monicPoly_monic a).coeff_natDegree
  rwa [monicPoly_natDegree] at h

/-- Divisibility passes through the Leibniz sign (`ℤˣ`-smul is `±`). -/
private theorem dvd_sign_zsmul {x y : O} (ε : ℤˣ) (h : y ∣ x) : y ∣ ε • x := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [Units.smul_def, Units.val_one, one_zsmul]; exact h
  · rw [Units.smul_def, Units.val_neg, Units.val_one, neg_zsmul, one_zsmul]
    exact dvd_neg.mpr h

variable {n r : ℕ} (a₁ : Fin n → O) (a₂ : Fin r → O)

/-- Left-block entry reader: column `castAdd r j₁` carries the STEEP coefficients
`(monicPoly a₂).coeff (i − j₁)` on the band `j₁ ≤ i ≤ j₁ + r`. -/
private theorem syl_left (i : Fin (n + r)) (j₁ : Fin n) :
    sylvester (monicPoly a₁) (monicPoly a₂) n r i (Fin.castAdd r j₁)
      = if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + r)
          then (monicPoly a₂).coeff ((i : ℕ) - (j₁ : ℕ)) else 0 := by
  simp only [sylvester, Matrix.of_apply, Fin.addCases_left]

/-- Right-block entry reader: column `natAdd n j₁` carries the FACE coefficients
`(monicPoly a₁).coeff (i − j₁)` on the band `j₁ ≤ i ≤ j₁ + n`. -/
private theorem syl_right (i : Fin (n + r)) (j₁ : Fin r) :
    sylvester (monicPoly a₁) (monicPoly a₂) n r i (Fin.natAdd n j₁)
      = if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + n)
          then (monicPoly a₁).coeff ((i : ℕ) - (j₁ : ℕ)) else 0 := by
  simp only [sylvester, Matrix.of_apply, Fin.addCases_right]

/-- **The block-flip permutation** — the unique minimal Leibniz term: every steep
column at its monic point (row `j₁ + r`), every face column at its corner (row `j₁`). -/
private def sylFlip (n r : ℕ) : Equiv.Perm (Fin (n + r)) :=
  finAddFlip.trans (finCongr (Nat.add_comm r n))

private theorem sylFlip_castAdd (j₁ : Fin n) :
    (sylFlip n r (Fin.castAdd r j₁) : ℕ) = r + (j₁ : ℕ) := by
  simp only [sylFlip, Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply,
    Fin.val_cast, Fin.val_natAdd]

private theorem sylFlip_natAdd (j₁ : Fin r) :
    (sylFlip n r (Fin.natAdd n j₁) : ℕ) = (j₁ : ℕ) := by
  simp [sylFlip, finAddFlip_apply_natAdd]

variable (σ : Equiv.Perm (Fin (n + r)))

/-- The per-column weight, left (steep) block: the supplied steep weight at the in-band
position, `0` at the monic point (or nominally out of band, where the entry vanishes). -/
private def wtL (w₂ : Fin r → ℕ) (j₁ : Fin n) : ℕ :=
  if hk : (σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ) < r
    then w₂ ⟨(σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ), hk⟩ else 0

/-- The per-column weight, right (face) block. -/
private def wtR (w₁ : Fin n → ℕ) (j₁ : Fin r) : ℕ :=
  if hk : (σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ) < n
    then w₁ ⟨(σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ), hk⟩ else 0

variable {π : O} {w₁ : Fin n → ℕ} {w₂ : Fin r → ℕ}

/-- Weighted divisibility of the left-block entries (unconditional: out-of-band and
monic-point entries are divisible trivially). -/
private theorem dvd_entry_L (hd₂ : ∀ j, π ^ w₂ j ∣ a₂ j) (j₁ : Fin n) :
    π ^ wtL σ w₂ j₁
      ∣ sylvester (monicPoly a₁) (monicPoly a₂) n r (σ (Fin.castAdd r j₁)) (Fin.castAdd r j₁) := by
  rw [syl_left]
  by_cases hband : (σ (Fin.castAdd r j₁) : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + r)
  · rw [if_pos hband]
    rw [Set.mem_Icc] at hband
    by_cases hk : (σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ) < r
    · rw [wtL, dif_pos hk, monicPoly_coeff_lt a₂ hk]
      exact hd₂ _
    · have hkr : (σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ) = r := by omega
      rw [wtL, dif_neg hk, pow_zero, hkr, monicPoly_coeff_deg]
  · rw [if_neg hband]
    exact dvd_zero _

/-- Weighted divisibility of the right-block entries. -/
private theorem dvd_entry_R (hd₁ : ∀ j, π ^ w₁ j ∣ a₁ j) (j₁ : Fin r) :
    π ^ wtR σ w₁ j₁
      ∣ sylvester (monicPoly a₁) (monicPoly a₂) n r (σ (Fin.natAdd n j₁)) (Fin.natAdd n j₁) := by
  rw [syl_right]
  by_cases hband : (σ (Fin.natAdd n j₁) : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + n)
  · rw [if_pos hband]
    rw [Set.mem_Icc] at hband
    by_cases hk : (σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ) < n
    · rw [wtR, dif_pos hk, monicPoly_coeff_lt a₁ hk]
      exact hd₁ _
    · have hkr : (σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ) = n := by omega
      rw [wtR, dif_neg hk, pow_zero, hkr, monicPoly_coeff_deg]
  · rw [if_neg hband]
    exact dvd_zero _

variable {h e' : ℕ}

/-- The slack bound, left block: in band, the `e'`-cleared weight dominates `h` times
the distance to the monic point. -/
private theorem slack_bound_L (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) ≤ e' * w₂ j)
    (j₁ : Fin n) (hlo : (j₁ : ℕ) ≤ (σ (Fin.castAdd r j₁) : ℕ))
    (hhi : (σ (Fin.castAdd r j₁) : ℕ) ≤ (j₁ : ℕ) + r) :
    h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)) ≤ e' * wtL σ w₂ j₁ := by
  by_cases hk : (σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ) < r
  · rw [wtL, dif_pos hk]
    have hb := hb₂ ⟨(σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ), hk⟩
    have harith : (j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)
        = r - ((σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ)) := by omega
    rw [harith]
    exact hb
  · have hz : (j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ) = 0 := by omega
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _

/-- The STRICT slack bound, left block: with the steep bounds strict, every in-band
left column OFF its monic point carries a `+1` excess. -/
private theorem slack_bound_L_strict (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) + 1 ≤ e' * w₂ j)
    (j₁ : Fin n) (hlo : (j₁ : ℕ) ≤ (σ (Fin.castAdd r j₁) : ℕ))
    (hlt : (σ (Fin.castAdd r j₁) : ℕ) < (j₁ : ℕ) + r) :
    h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)) + 1 ≤ e' * wtL σ w₂ j₁ := by
  have hk : (σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ) < r := by omega
  rw [wtL, dif_pos hk]
  have hb := hb₂ ⟨(σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ), hk⟩
  have harith : (j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)
      = r - ((σ (Fin.castAdd r j₁) : ℕ) - (j₁ : ℕ)) := by omega
  rw [harith]
  exact hb

/-- The slack bound, right block. -/
private theorem slack_bound_R (hb₁ : ∀ j : Fin n, h * (n - (j : ℕ)) ≤ e' * w₁ j)
    (j₁ : Fin r) (hlo : (j₁ : ℕ) ≤ (σ (Fin.natAdd n j₁) : ℕ))
    (hhi : (σ (Fin.natAdd n j₁) : ℕ) ≤ (j₁ : ℕ) + n) :
    h * ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ)) ≤ e' * wtR σ w₁ j₁ := by
  by_cases hk : (σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ) < n
  · rw [wtR, dif_pos hk]
    have hb := hb₁ ⟨(σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ), hk⟩
    have harith : (j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ)
        = n - ((σ (Fin.natAdd n j₁) : ℕ) - (j₁ : ℕ)) := by omega
    rw [harith]
    exact hb
  · have hz : (j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ) = 0 := by omega
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _

/-- **THE COLUMN TELESCOPE**: over any in-band permutation the total slack is exactly
`n·r` — trade `Σ σ(c)` for `Σ c` (`σ` is a bijection), then both structured sums
collapse blockwise. -/
private theorem sum_slack_blocks
    (hbL : ∀ j₁ : Fin n, (σ (Fin.castAdd r j₁) : ℕ) ≤ (j₁ : ℕ) + r)
    (hbR : ∀ j₁ : Fin r, (σ (Fin.natAdd n j₁) : ℕ) ≤ (j₁ : ℕ) + n) :
    (∑ j₁ : Fin n, ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
      + (∑ j₁ : Fin r, ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ))) = n * r := by
  set P := n * r with hP
  -- (1) pointwise: slack + σ = offset + band, summed per block
  have hL : (∑ j₁ : Fin n, ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
      + (∑ j₁ : Fin n, (σ (Fin.castAdd r j₁) : ℕ)) = ∑ j₁ : Fin n, ((j₁ : ℕ) + r) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j₁ _ => Nat.sub_add_cancel (hbL j₁)
  have hR : (∑ j₁ : Fin r, ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ)))
      + (∑ j₁ : Fin r, (σ (Fin.natAdd n j₁) : ℕ)) = ∑ j₁ : Fin r, ((j₁ : ℕ) + n) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j₁ _ => Nat.sub_add_cancel (hbR j₁)
  -- (2) the σ-sums rejoin to the full value sum, which is the identity's
  have hσ : (∑ j₁ : Fin n, (σ (Fin.castAdd r j₁) : ℕ))
      + (∑ j₁ : Fin r, (σ (Fin.natAdd n j₁) : ℕ)) = ∑ j : Fin (n + r), (j : ℕ) := by
    rw [← Fin.sum_univ_add (f := fun j : Fin (n + r) => ((σ j : ℕ)))]
    exact Equiv.sum_comp σ (fun j => (j : ℕ))
  -- (3) the identity's value sum, blockwise
  have hid : ∑ j : Fin (n + r), (j : ℕ)
      = (∑ j₁ : Fin n, (j₁ : ℕ)) + (∑ j₁ : Fin r, (n + (j₁ : ℕ))) := by
    rw [Fin.sum_univ_add (f := fun j : Fin (n + r) => (j : ℕ))]
    simp
  -- (4) the structured sums, expanded
  have e1 : ∑ j₁ : Fin n, ((j₁ : ℕ) + r) = (∑ j₁ : Fin n, (j₁ : ℕ)) + P := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hP]
  have e2 : ∑ j₁ : Fin r, ((j₁ : ℕ) + n) = (∑ j₁ : Fin r, (j₁ : ℕ)) + P := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hP, Nat.mul_comm]
  have e3 : ∑ j₁ : Fin r, (n + (j₁ : ℕ)) = P + (∑ j₁ : Fin r, (j₁ : ℕ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hP, Nat.mul_comm]
  omega

end Kit

/-! ## §1 — THE DETERMINANT PIN (lift side): the weighted-Leibniz Sylvester bound -/

section DetPin

variable {O : Type*} [CommRing O] [IsDomain O] {π : O} {h e' n r : ℕ}
  {a₁ : Fin n → O} {a₂ : Fin r → O}

/-- **Per-term bound (weak)**: every Leibniz term of the pinned Sylvester determinant is
divisible by `π^{u·r}` (`h·n = e'·u`): out-of-band terms vanish; in-band terms carry
total `e'`-cleared weight `≥ h·(telescope) = h·n·r`. -/
private theorem term_dvd {u : ℕ} (he' : 0 < e') (hu : h * n = e' * u)
    {w₁ : Fin n → ℕ} {w₂ : Fin r → ℕ}
    (hd₁ : ∀ j, π ^ w₁ j ∣ a₁ j) (hd₂ : ∀ j, π ^ w₂ j ∣ a₂ j)
    (hb₁ : ∀ j : Fin n, h * (n - (j : ℕ)) ≤ e' * w₁ j)
    (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) ≤ e' * w₂ j)
    (σ : Equiv.Perm (Fin (n + r))) :
    π ^ (u * r) ∣ ∏ j, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j := by
  by_cases hzero : ∃ j : Fin (n + r), sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hz : ∏ i, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hz]
    exact dvd_zero _
  · have hnz : ∀ j : Fin (n + r), sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j ≠ 0 :=
      fun j hj => hzero ⟨j, hj⟩
    -- nonvanishing entries force every column in band
    have hbL : ∀ j₁ : Fin n, (j₁ : ℕ) ≤ (σ (Fin.castAdd r j₁) : ℕ)
        ∧ (σ (Fin.castAdd r j₁) : ℕ) ≤ (j₁ : ℕ) + r := by
      intro j₁
      by_contra hcon
      refine hnz (Fin.castAdd r j₁) ?_
      rw [syl_left]
      exact if_neg fun hmem => hcon (Set.mem_Icc.mp hmem)
    have hbR : ∀ j₁ : Fin r, (j₁ : ℕ) ≤ (σ (Fin.natAdd n j₁) : ℕ)
        ∧ (σ (Fin.natAdd n j₁) : ℕ) ≤ (j₁ : ℕ) + n := by
      intro j₁
      by_contra hcon
      refine hnz (Fin.natAdd n j₁) ?_
      rw [syl_right]
      exact if_neg fun hmem => hcon (Set.mem_Icc.mp hmem)
    -- the weighted divisibility of the whole term, blockwise
    have hdvd : π ^ ((∑ j₁ : Fin n, wtL σ w₂ j₁) + (∑ j₁ : Fin r, wtR σ w₁ j₁))
        ∣ ∏ j, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j := by
      rw [Fin.prod_univ_add
        (f := fun j : Fin (n + r) => sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j),
        pow_add]
      refine mul_dvd_mul ?_ ?_
      · rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun j₁ _ => dvd_entry_L a₁ a₂ σ hd₂ j₁
      · rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun j₁ _ => dvd_entry_R a₁ a₂ σ hd₁ j₁
    refine dvd_trans (pow_dvd_pow π ?_) hdvd
    -- the arithmetic: u·r ≤ total weight, by the telescope + the slack bounds
    have hsum := sum_slack_blocks σ (fun j₁ => (hbL j₁).2) (fun j₁ => (hbR j₁).2)
    have hsplit : h * (n * r)
        = (∑ j₁ : Fin n, h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
          + (∑ j₁ : Fin r, h * ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ))) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Nat.mul_add, hsum]
    have hle : (∑ j₁ : Fin n, h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
          + (∑ j₁ : Fin r, h * ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ)))
        ≤ (∑ j₁ : Fin n, e' * wtL σ w₂ j₁) + (∑ j₁ : Fin r, e' * wtR σ w₁ j₁) :=
      Nat.add_le_add
        (Finset.sum_le_sum fun j₁ _ => slack_bound_L σ hb₂ j₁ (hbL j₁).1 (hbL j₁).2)
        (Finset.sum_le_sum fun j₁ _ => slack_bound_R σ hb₁ j₁ (hbR j₁).1 (hbR j₁).2)
    have hjoin : (∑ j₁ : Fin n, e' * wtL σ w₂ j₁) + (∑ j₁ : Fin r, e' * wtR σ w₁ j₁)
        = e' * ((∑ j₁ : Fin n, wtL σ w₂ j₁) + (∑ j₁ : Fin r, wtR σ w₁ j₁)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Nat.mul_add]
    have hkey : h * (n * r) = e' * (u * r) := by rw [← Nat.mul_assoc, hu, Nat.mul_assoc]
    refine Nat.le_of_mul_le_mul_left ?_ he'
    omega

/-- ★★ **THE LOWER BOUND** — the `≥` half of the depth pin, over any domain, any `π`:
cone-shaped coefficient weights (`e'·w₁ ≥ h·(distance to the monic point)` on the face
block, likewise `w₂` on the cofactor) force `π^{u·r} ∣ Res` at the pinned sizes, where
`u` is the `e'`-cleared corner value (`h·n = e'·u`). -/
theorem pow_dvd_resultant_of_cones {u : ℕ} (he' : 0 < e') (hu : h * n = e' * u)
    {w₁ : Fin n → ℕ} {w₂ : Fin r → ℕ}
    (hd₁ : ∀ j, π ^ w₁ j ∣ a₁ j) (hd₂ : ∀ j, π ^ w₂ j ∣ a₂ j)
    (hb₁ : ∀ j : Fin n, h * (n - (j : ℕ)) ≤ e' * w₁ j)
    (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) ≤ e' * w₂ j) :
    π ^ (u * r) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n r := by
  rw [show Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n r
      = (sylvester (monicPoly a₁) (monicPoly a₂) n r).det from rfl, Matrix.det_apply]
  exact Finset.dvd_sum fun σ _ => dvd_sign_zsmul _ (term_dvd he' hu hd₁ hd₂ hb₁ hb₂ σ)

/-- **Per-term bound (strict)**: with the steep bounds STRICT, every Leibniz term OFF
the block-flip permutation carries an extra `π`: either some steep column is off its
monic point (the `+1` excess), or all are — and then an injective above-diagonal
self-map of `Fin r` forces `σ = sylFlip`. -/
private theorem term_dvd_strict {u : ℕ} (hu : h * n = e' * u)
    {w₁ : Fin n → ℕ} {w₂ : Fin r → ℕ}
    (hd₁ : ∀ j, π ^ w₁ j ∣ a₁ j) (hd₂ : ∀ j, π ^ w₂ j ∣ a₂ j)
    (hb₁ : ∀ j : Fin n, h * (n - (j : ℕ)) ≤ e' * w₁ j)
    (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) + 1 ≤ e' * w₂ j)
    {σ : Equiv.Perm (Fin (n + r))} (hne : σ ≠ sylFlip n r) :
    π ^ (u * r + 1) ∣ ∏ j, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j := by
  have hb₂w : ∀ j : Fin r, h * (r - (j : ℕ)) ≤ e' * w₂ j := fun j => by
    have := hb₂ j; omega
  by_cases hzero : ∃ j : Fin (n + r), sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hz : ∏ i, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hz]
    exact dvd_zero _
  · have hnz : ∀ j : Fin (n + r), sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j ≠ 0 :=
      fun j hj => hzero ⟨j, hj⟩
    have hbL : ∀ j₁ : Fin n, (j₁ : ℕ) ≤ (σ (Fin.castAdd r j₁) : ℕ)
        ∧ (σ (Fin.castAdd r j₁) : ℕ) ≤ (j₁ : ℕ) + r := by
      intro j₁
      by_contra hcon
      refine hnz (Fin.castAdd r j₁) ?_
      rw [syl_left]
      exact if_neg fun hmem => hcon (Set.mem_Icc.mp hmem)
    have hbR : ∀ j₁ : Fin r, (j₁ : ℕ) ≤ (σ (Fin.natAdd n j₁) : ℕ)
        ∧ (σ (Fin.natAdd n j₁) : ℕ) ≤ (j₁ : ℕ) + n := by
      intro j₁
      by_contra hcon
      refine hnz (Fin.natAdd n j₁) ?_
      rw [syl_right]
      exact if_neg fun hmem => hcon (Set.mem_Icc.mp hmem)
    by_cases hex : ∃ j₁ : Fin n, (σ (Fin.castAdd r j₁) : ℕ) < (j₁ : ℕ) + r
    · -- a steep column off its monic point: the strict excess fires
      have hdvd : π ^ ((∑ j₁ : Fin n, wtL σ w₂ j₁) + (∑ j₁ : Fin r, wtR σ w₁ j₁))
          ∣ ∏ j, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j := by
        rw [Fin.prod_univ_add
          (f := fun j : Fin (n + r) => sylvester (monicPoly a₁) (monicPoly a₂) n r (σ j) j),
          pow_add]
        refine mul_dvd_mul ?_ ?_
        · rw [← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_dvd_prod_of_dvd _ _ fun j₁ _ => dvd_entry_L a₁ a₂ σ hd₂ j₁
        · rw [← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_dvd_prod_of_dvd _ _ fun j₁ _ => dvd_entry_R a₁ a₂ σ hd₁ j₁
      refine dvd_trans (pow_dvd_pow π ?_) hdvd
      obtain ⟨j₀, hj₀⟩ := hex
      have hsum := sum_slack_blocks σ (fun j₁ => (hbL j₁).2) (fun j₁ => (hbR j₁).2)
      have hsplit : h * (n * r)
          = (∑ j₁ : Fin n, h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
            + (∑ j₁ : Fin r, h * ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Nat.mul_add, hsum]
      have hltL : (∑ j₁ : Fin n, h * ((j₁ : ℕ) + r - (σ (Fin.castAdd r j₁) : ℕ)))
          < ∑ j₁ : Fin n, e' * wtL σ w₂ j₁ :=
        Finset.sum_lt_sum (fun i _ => slack_bound_L σ hb₂w i (hbL i).1 (hbL i).2)
          ⟨j₀, Finset.mem_univ j₀, by
            have := slack_bound_L_strict σ hb₂ j₀ (hbL j₀).1 hj₀
            omega⟩
      have hleR : (∑ j₁ : Fin r, h * ((j₁ : ℕ) + n - (σ (Fin.natAdd n j₁) : ℕ)))
          ≤ ∑ j₁ : Fin r, e' * wtR σ w₁ j₁ :=
        Finset.sum_le_sum fun j₁ _ => slack_bound_R σ hb₁ j₁ (hbR j₁).1 (hbR j₁).2
      have hjoin : (∑ j₁ : Fin n, e' * wtL σ w₂ j₁) + (∑ j₁ : Fin r, e' * wtR σ w₁ j₁)
          = e' * ((∑ j₁ : Fin n, wtL σ w₂ j₁) + (∑ j₁ : Fin r, wtR σ w₁ j₁)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Nat.mul_add]
      have hkey : h * (n * r) = e' * (u * r) := by rw [← Nat.mul_assoc, hu, Nat.mul_assoc]
      refine Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left (a := e') ?_)
      omega
    · -- every steep column at its monic point forces σ = sylFlip: contradiction
      exfalso
      have hleft : ∀ j₁ : Fin n, (σ (Fin.castAdd r j₁) : ℕ) = (j₁ : ℕ) + r := by
        intro j₁
        have h1 := (hbL j₁).2
        have h2 : ¬ (σ (Fin.castAdd r j₁) : ℕ) < (j₁ : ℕ) + r := fun hc => hex ⟨j₁, hc⟩
        omega
      -- the face rows live strictly below r
      have hφlt : ∀ j₁ : Fin r, (σ (Fin.natAdd n j₁) : ℕ) < r := by
        intro j₁
        by_contra hge'
        have hge : r ≤ (σ (Fin.natAdd n j₁) : ℕ) := by omega
        have hlt : (σ (Fin.natAdd n j₁) : ℕ) - r < n := by
          have := (σ (Fin.natAdd n j₁)).isLt
          omega
        have hrow : (σ (Fin.castAdd r ⟨(σ (Fin.natAdd n j₁) : ℕ) - r, hlt⟩) : ℕ)
            = ((σ (Fin.natAdd n j₁) : ℕ) - r) + r :=
          hleft ⟨(σ (Fin.natAdd n j₁) : ℕ) - r, hlt⟩
        have heq : σ (Fin.castAdd r ⟨(σ (Fin.natAdd n j₁) : ℕ) - r, hlt⟩)
            = σ (Fin.natAdd n j₁) := by
          apply Fin.ext
          rw [hrow]
          omega
        have hcol := σ.injective heq
        have hv1 : ((Fin.castAdd r ⟨(σ (Fin.natAdd n j₁) : ℕ) - r, hlt⟩ : Fin (n + r)) : ℕ)
            = (σ (Fin.natAdd n j₁) : ℕ) - r := rfl
        have hv2 : ((Fin.natAdd n j₁ : Fin (n + r)) : ℕ) = n + (j₁ : ℕ) := rfl
        have hv3 := congrArg Fin.val hcol
        omega
      -- the above-diagonal injective self-map of Fin r is the identity
      have hψinj : Function.Injective
          (fun j₁ : Fin r => (⟨(σ (Fin.natAdd n j₁) : ℕ), hφlt j₁⟩ : Fin r)) := by
        intro x y hxy
        simp only [Fin.mk.injEq] at hxy
        have h2 := σ.injective (Fin.ext hxy)
        have h3 : n + (x : ℕ) = n + (y : ℕ) := congrArg Fin.val h2
        exact Fin.ext (by omega)
      have hψbij := Finite.injective_iff_bijective.mp hψinj
      have hsumψ : (∑ j₁ : Fin r,
            ((⟨(σ (Fin.natAdd n j₁) : ℕ), hφlt j₁⟩ : Fin r) : ℕ))
          = ∑ j₁ : Fin r, (j₁ : ℕ) :=
        Equiv.sum_comp (Equiv.ofBijective _ hψbij) (fun x : Fin r => (x : ℕ))
      have hall := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin r) (_ : i ∈ Finset.univ) => (hbR i).1)).mp hsumψ.symm
      apply hne
      apply Equiv.ext
      intro c
      induction c using Fin.addCases with
      | left j₁ =>
        apply Fin.ext
        rw [hleft j₁, sylFlip_castAdd]
        omega
      | right j₁ =>
        apply Fin.ext
        rw [sylFlip_natAdd]
        exact (hall j₁ (Finset.mem_univ j₁)).symm

/-- The block-flip term is the pure corner power: every steep column contributes its
monic `1`, every face column its corner coefficient `a₁ 0`. -/
private theorem prod_sylFlip (hn : 0 < n) :
    ∏ j, sylvester (monicPoly a₁) (monicPoly a₂) n r (sylFlip n r j) j
      = a₁ ⟨0, hn⟩ ^ r := by
  rw [Fin.prod_univ_add
    (f := fun j : Fin (n + r) => sylvester (monicPoly a₁) (monicPoly a₂) n r (sylFlip n r j) j)]
  have hL : ∀ j₁ : Fin n,
      sylvester (monicPoly a₁) (monicPoly a₂) n r (sylFlip n r (Fin.castAdd r j₁))
        (Fin.castAdd r j₁) = 1 := by
    intro j₁
    rw [syl_left, sylFlip_castAdd,
      if_pos (Set.mem_Icc.mpr ⟨by omega, by omega⟩)]
    have hidx : r + (j₁ : ℕ) - (j₁ : ℕ) = r := by omega
    rw [hidx, monicPoly_coeff_deg]
  have hR : ∀ j₁ : Fin r,
      sylvester (monicPoly a₁) (monicPoly a₂) n r (sylFlip n r (Fin.natAdd n j₁))
        (Fin.natAdd n j₁) = a₁ ⟨0, hn⟩ := by
    intro j₁
    rw [syl_right, sylFlip_natAdd,
      if_pos (Set.mem_Icc.mpr ⟨le_refl _, by omega⟩)]
    have hidx : (j₁ : ℕ) - (j₁ : ℕ) = 0 := by omega
    rw [hidx, monicPoly_coeff_lt a₁ hn]
  rw [Finset.prod_congr rfl fun j₁ _ => hL j₁, Finset.prod_congr rfl fun j₁ _ => hR j₁,
    Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- ★★ **THE EXACTNESS** — the `¬(v+1)` half of the depth pin: with the steep bounds
STRICT and the face corner EXACT (`π^u ∥ a₁ 0`, `π` prime), the Sylvester determinant
is NOT divisible by `π^{u·r + 1}` — the block-flip term `± (a₁ 0)^r` sits at valuation
exactly `u·r` and every other term is strictly deeper. -/
theorem not_pow_succ_dvd_resultant_of_cones (hπ : Prime π) {u : ℕ}
    (he' : 0 < e') (hn : 0 < n) (hu : h * n = e' * u)
    {w₁ : Fin n → ℕ} {w₂ : Fin r → ℕ}
    (hd₁ : ∀ j, π ^ w₁ j ∣ a₁ j) (hd₂ : ∀ j, π ^ w₂ j ∣ a₂ j)
    (hb₁ : ∀ j : Fin n, h * (n - (j : ℕ)) ≤ e' * w₁ j)
    (hb₂ : ∀ j : Fin r, h * (r - (j : ℕ)) + 1 ≤ e' * w₂ j)
    (hnd : ¬ π ^ (u + 1) ∣ a₁ ⟨0, hn⟩) :
    ¬ π ^ (u * r + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n r := by
  intro hdvd
  rw [show Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n r
      = (sylvester (monicPoly a₁) (monicPoly a₂) n r).det from rfl, Matrix.det_apply,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (sylFlip n r))] at hdvd
  -- the erased sum is strictly deeper
  have hrest : π ^ (u * r + 1)
      ∣ ∑ σ ∈ Finset.univ.erase (sylFlip n r),
          Equiv.Perm.sign σ • ∏ i, sylvester (monicPoly a₁) (monicPoly a₂) n r (σ i) i :=
    Finset.dvd_sum fun σ hσ => dvd_sign_zsmul _
      (term_dvd_strict hu hd₁ hd₂ hb₁ hb₂ (Finset.ne_of_mem_erase hσ))
  -- so the flip term inherits the divisibility
  have hτ : π ^ (u * r + 1)
      ∣ Equiv.Perm.sign (sylFlip n r)
          • ∏ i, sylvester (monicPoly a₁) (monicPoly a₂) n r (sylFlip n r i) i := by
    have h2 := dvd_sub hdvd hrest
    rwa [add_sub_cancel_right] at h2
  rw [prod_sylFlip hn] at hτ
  -- strip the sign
  have hpow : π ^ (u * r + 1) ∣ a₁ ⟨0, hn⟩ ^ r := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (sylFlip n r)) with hs | hs <;>
      rw [hs, Units.smul_def] at hτ
    · rwa [Units.val_one, one_zsmul] at hτ
    · rw [Units.val_neg, Units.val_one, neg_zsmul, one_zsmul] at hτ
      exact dvd_neg.mp hτ
  -- the exact corner: a₁ 0 = π^u · (unit mod π), so (a₁ 0)^r ∥ π^{u·r}
  have hwu : u ≤ w₁ ⟨0, hn⟩ := by
    have hb := hb₁ ⟨0, hn⟩
    have hz : (((⟨0, hn⟩ : Fin n) : ℕ)) = 0 := rfl
    rw [hz, Nat.sub_zero, hu] at hb
    exact Nat.le_of_mul_le_mul_left hb he'
  obtain ⟨cu, hcu⟩ : π ^ u ∣ a₁ ⟨0, hn⟩ := (pow_dvd_pow π hwu).trans (hd₁ ⟨0, hn⟩)
  have hπcu : ¬ π ∣ cu := fun hc =>
    hnd (by rw [hcu, pow_succ]; exact mul_dvd_mul_left _ hc)
  have hkey : π ∣ cu ^ r := by
    have h1 : a₁ ⟨0, hn⟩ ^ r = π ^ (u * r) * cu ^ r := by
      rw [hcu, mul_pow, ← pow_mul]
    rw [h1, pow_succ] at hpow
    exact (mul_dvd_mul_iff_left (pow_ne_zero (u * r) hπ.ne_zero)).mp hpow
  exact hπcu (hπ.dvd_of_dvd_pow hkey)

end DetPin

/-! ## §2 — ★★★ THE CLASS-LEVEL PIN: `mixDepth = h·d·r` on the depth instrument -/

section ClassPin

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★★ **THE DEPTH PIN** (class form, lift-free hypotheses): a face-block class `c₁`
(purity `h·(e'd − j) ≤ e'·resOrd(c₁ j)` with EXACT corner `resOrd(c₁ 0) = h·d`) against
a steep class `c₂` (`h·(r − j) < e'·resOrd(c₂ j)` — `subface_cofactor_class`'s output
shape) has mixing depth EXACTLY `h·d·r` below the window.  This is TBT's ladder
constant `v(Res(g, R)) = h·d·(m − e'·d)`, machine-checked. -/
theorem mixDepth_eq_of_cones {π : O} (hπ : Irreducible π) {h e' d r N : ℕ}
    (he' : 0 < e') (hd0 : 0 < d) (hr : 0 < r) (hN : h * d * r < N)
    (c₁ : Coeff O (e' * d) N) (c₂ : Coeff O r N)
    (hpure : ∀ j : Fin (e' * d), h * (e' * d - (j : ℕ)) ≤ e' * resOrd (c₁ j))
    (hcorner : resOrd (c₁ ⟨0, Nat.mul_pos he' hd0⟩) = h * d)
    (hsteep : ∀ j : Fin r, h * (r - (j : ℕ)) < e' * resOrd (c₂ j)) :
    mixDepth π c₁ c₂ = h * d * r := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective O (e' * d) N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O r N c₂
  subst ha₁
  subst ha₂
  -- the windowed valuations are honest lift weights
  have hd₁ : ∀ j, π ^ (resOrd (proj O (e' * d) N a₁ j)) ∣ a₁ j := fun j =>
    (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
  have hd₂ : ∀ j, π ^ (resOrd (proj O r N a₂ j)) ∣ a₂ j := fun j =>
    (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
  -- the exact corner descends to the lift
  have hvis : classCoeffVal (proj O (e' * d) N a₁) ⟨0, Nat.mul_pos he' hd0⟩ < N := by
    show resOrd (proj O (e' * d) N a₁ ⟨0, Nat.mul_pos he' hd0⟩) < N
    rw [hcorner]
    have hle : h * d ≤ h * d * r := Nat.le_mul_of_pos_right _ hr
    omega
  obtain ⟨-, hndc⟩ := classCoeffVal_exact hπ rfl hvis
  rw [show classCoeffVal (proj O (e' * d) N a₁) ⟨0, Nat.mul_pos he' hd0⟩ = h * d
    from hcorner] at hndc
  -- the two §1 halves at the pinned frame
  have hu : h * (e' * d) = e' * (h * d) := by ring
  have hAdvd : π ^ (h * d * r)
      ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) (e' * d) r :=
    pow_dvd_resultant_of_cones he' hu hd₁ hd₂ (fun j => hpure j)
      (fun j => le_of_lt (hsteep j))
  have hBnd : ¬ π ^ (h * d * r + 1)
      ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) (e' * d) r :=
    not_pow_succ_dvd_resultant_of_cones hπ.prime he' (Nat.mul_pos he' hd0) hu hd₁ hd₂
      (fun j => hpure j) (fun j => by have := hsteep j; omega) hndc
  -- assemble on the class instrument
  rw [mixDepth_eq_iff hN]
  refine ⟨?_, ?_⟩
  · rw [classRes_proj]
    exact (mk_pow_dvd_mk_iff hπ (le_of_lt hN) _).mpr hAdvd
  · rw [classRes_proj]
    intro hcon
    exact hBnd ((mk_pow_dvd_mk_iff hπ (by omega) _).mp hcon)

end ClassPin

/-! ## §3 — THE FRAME INSTANTIATION: from `IsPure` to the class cones, and the leaf pin -/

section FrameData

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The monic point has height `0` (IFCG66's private replica). -/
private theorem npHgt_monic_top {g : Polynomial O} (hg : g.Monic) :
    npHgt X g g.natDegree = 0 := by
  rw [npHgt_X, hg.coeff_natDegree]
  exact IsDiscreteValuationRing.addVal_one

/-- A monic polynomial's cleared support value is finite (IFCG66's private replica). -/
private theorem suppVal_ne_top_of_monic {g : Polynomial O} (hg : g.Monic) (u ℓ : ℕ) :
    suppVal X g u ℓ ≠ ⊤ := by
  have hle : suppVal X g u ℓ ≤ ℓ • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  rw [npHgt_monic_top hg, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

/-- ★ **From purity to the class cones**: B.34's `IsPure` (single face of slope `h/e'`,
on-side at BOTH endpoints) yields the §2 hypotheses for the canonical class of the
coefficient vector — the coefficientwise purity cone AND the exact corner
`resOrd = h·d` (the corner is on the polygon, so `IsPure` carries it for free). -/
theorem cone_data_of_isPure {π : O} (hπ : Irreducible π) {g : Polynomial O}
    (hgm : g.Monic) {h e' d : ℕ} (he' : 0 < e') (hd0 : 0 < d)
    (hgp : IsPure X g h e') (hdeg : g.natDegree = e' * d) {N : ℕ} (hdN : h * d < N) :
    (∀ j : Fin (e' * d),
        h * (e' * d - (j : ℕ))
          ≤ e' * resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j))
      ∧ resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) ⟨0, Nat.mul_pos he' hd0⟩)
          = h * d := by
  -- the two endpoint on-side facts, at the aligned abscissae
  have hOn0 : OnSide X g h e' 0 := hgp.1
  have hOnTop : OnSide X g h e' (e' * d) := by
    have hidx : g.natDegree / (X : Polynomial O).natDegree = e' * d := by
      rw [natDegree_X, Nat.div_one, hdeg]
    have h2 := hgp.2
    rwa [hidx] at h2
  have htop : suppVal X g h e' ≠ ⊤ := suppVal_ne_top_of_monic hgm h e'
  -- the top height vanishes
  have hHtop : npHgt X g (e' * d) = ((0 : ℕ) : ℕ∞) := by
    have := npHgt_monic_top hgm
    rw [hdeg] at this
    simpa using this
  -- the corner height, extracted to ℕ and pinned to h·d by the two-point equation
  obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide he' htop hOn0)
  have hkey : e' * w + h * 0 = e' * 0 + h * (e' * d) :=
    onSide_nat_eq hw.symm hHtop hOn0 hOnTop
  have hwval : w = h * d := by
    have hr : h * (e' * d) = e' * (h * d) := by ring
    rw [hr] at hkey
    have : e' * w = e' * (h * d) := by omega
    exact Nat.eq_of_mul_eq_mul_left he' this
  -- the corner's exact divisibility pair on the coefficient
  have haddval : IsDiscreteValuationRing.addVal O (g.coeff 0) = ((h * d : ℕ) : ℕ∞) := by
    have h1 : npHgt X g 0 = ((h * d : ℕ) : ℕ∞) := by rw [← hw, hwval]
    rwa [npHgt_X] at h1
  have hdvd0 : π ^ (h * d) ∣ g.coeff 0 :=
    (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 (by rw [haddval])
  have hnd0 : ¬ π ^ (h * d + 1) ∣ g.coeff 0 := by
    intro hcon
    have h2 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hcon
    rw [haddval] at h2
    exact absurd (by exact_mod_cast h2) (by omega)
  constructor
  · -- the purity cone, coordinatewise
    intro j
    by_cases hvis : resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j) < N
    · -- visible: the class read is the exact lift valuation, on or above the face line
      obtain ⟨hdvj, hndj⟩ := classCoeffVal_exact hπ
        (a := fun i : Fin (e' * d) => g.coeff (i : ℕ)) rfl hvis
      have haddj : IsDiscreteValuationRing.addVal O (g.coeff (j : ℕ))
          = ((resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j) : ℕ) : ℕ∞) :=
        addVal_eq_of_pow_dvd_not_dvd hπ hdvj hndj
      have hHj : npHgt X g (j : ℕ)
          = ((resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j) : ℕ) : ℕ∞) := by
        rw [npHgt_X, haddj]
      -- the support inequality at abscissa j, lowered to ℕ
      have hle : suppVal X g h e' ≤ e' • npHgt X g (j : ℕ) + ((h * (j : ℕ) : ℕ) : ℕ∞) := by
        rw [suppVal]
        exact Finset.inf_le (Finset.mem_range.mpr (by rw [hdeg]; omega))
      have hsupp : suppVal X g h e' = ((h * (e' * d) : ℕ) : ℕ∞) := by
        have h2 : e' • npHgt X g (e' * d) + ((h * (e' * d) : ℕ) : ℕ∞)
            = suppVal X g h e' := hOnTop
        rw [hHtop] at h2
        simpa using h2.symm
      rw [hsupp, hHj] at hle
      have hnat : h * (e' * d)
          ≤ e' * resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j) + h * (j : ℕ) := by
        have h3 : ((h * (e' * d) : ℕ) : ℕ∞)
            ≤ ((e' * resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j)
                + h * (j : ℕ) : ℕ) : ℕ∞) := by
          push_cast
          simpa [nsmul_eq_mul] using hle
        exact_mod_cast h3
      have hbridge : h * (e' * d - (j : ℕ)) + h * (j : ℕ) = h * (e' * d) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    · -- saturated window: the face line sits below e'·N outright
      have hcap := resOrd_le (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j)
      have heq : resOrd (proj O (e' * d) N (fun i => g.coeff (i : ℕ)) j) = N := by omega
      rw [heq]
      have c1 : h * (e' * d - (j : ℕ)) ≤ h * (e' * d) :=
        Nat.mul_le_mul_left h (Nat.sub_le _ _)
      have c2 : h * (e' * d) = e' * (h * d) := by ring
      have c3 : e' * (h * d) ≤ e' * N := Nat.mul_le_mul_left e' (le_of_lt hdN)
      omega
  · -- the exact corner on the class
    exact resOrd_mk_eq hπ (le_of_lt hdN) hdvd0 (Or.inr hnd0)

end FrameData

section LeafPin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE SUB-FACE DEPTH PIN** (the leaf composite — TBT's ladder constant, LSF's
discharge pointer 1, CLOSED): every lift of a sub-face leaf cell at minimal face
`(h, e')` splits as LSF's pinned transport `monicPoly a = g · R`, and the canonical
classes of the two factors sit at mixing depth EXACTLY `h·d·(m − e'·d)` whenever the
depth is below the window. -/
theorem subface_depth_pin {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ (g R : Polynomial O) (d : ℕ), monicPoly a = g * R ∧ g.Monic ∧ R.Monic
      ∧ IsPure X g h e' ∧ 0 < d ∧ g.natDegree = e' * d ∧ e' * d < m
      ∧ typeOf g = ⟨{(e', d)}⟩ ∧ R.natDegree = m - e' * d
      ∧ σ.data = (e', d) ::ₘ (typeOf R).data
      ∧ (classResidualPoly π c h e').natDegree = d
      ∧ (h * d * (m - e' * d) < M + m →
          mixDepth π (proj O (e' * d) (M + m) (fun i => g.coeff (i : ℕ)))
            (proj O R.natDegree (M + m) (fun i => R.coeff (i : ℕ)))
            = h * d * (m - e' * d)) := by
  obtain ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata, hcrpd, hside⟩ :=
    subface_transport_pinned hπ hm0 hc hF ha
  refine ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata, hcrpd,
    fun hwin => ?_⟩
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have he' : 0 < e' := by omega
  have hr0 : 0 < R.natDegree := by omega
  -- the window bound at the R-degree coordinates
  have hwin' : h * d * R.natDegree < M + m := by rw [hRdeg]; exact hwin
  have hdN : h * d < M + m := by
    have h1 : h * d ≤ h * d * R.natDegree := Nat.le_mul_of_pos_right _ hr0
    omega
  -- the face-block cone data
  obtain ⟨hpure, hcorner⟩ := cone_data_of_isPure hπ hgm he' hd0 hgpure hgd hdN
  -- the steep cone (LSF's class-side strict cone)
  have hrN : R.natDegree ≤ M + m := by omega
  have hsteep := fun j => class_strict_cone_of_side_singleton hπ hRm hhe hside hrN j
  -- fire the class pin at r := R.natDegree, then rename the value
  have hpin := mixDepth_eq_of_cones hπ he' hd0 hr0 hwin'
    (proj O (e' * d) (M + m) (fun i => g.coeff (i : ℕ)))
    (proj O R.natDegree (M + m) (fun i => R.coeff (i : ℕ)))
    hpure hcorner hsteep
  have hval : h * d * R.natDegree = h * d * (m - e' * d) := by rw [hRdeg]
  exact hpin.trans hval

end LeafPin

/-! ## §4 — THE COUPLINGS FIRED: the `q^v` fiber law and the decidedness transfer at
the KNOWN depth, and the witness-frame regression -/

section Couplings

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★ **THE `q^v` FIBER LAW AT THE PINNED DEPTH** (CSL's cluster socket fired): a
face-block/steep pair at the cone frame has pair neighborhood of size EXACTLY
`q^{h·d·r}` below half the window — the sub-face count's cluster size, at the KNOWN
depth. -/
theorem natCard_pairNbhd_of_cones {π : O} (hπ : Irreducible π) {h e' d r N : ℕ}
    (he' : 0 < e') (hd0 : 0 < d) (hr : 0 < r) (hN : 2 * (h * d * r) + 1 ≤ N)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hpure : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) N a₁ j))
    (hcorner : resOrd (proj O (e' * d) N a₁ ⟨0, Nat.mul_pos he' hd0⟩) = h * d)
    (hsteep : ∀ j : Fin r, h * (r - (j : ℕ)) < e' * resOrd (proj O r N a₂ j)) :
    Nat.card (pairNbhd π N (h * d * r) a₁ a₂) = residueCard O ^ (h * d * r) :=
  natCard_pairNbhd_of_mixDepth hπ hN (Or.inl (Nat.mul_pos he' hd0).ne')
    (mixDepth_eq_of_cones hπ he' hd0 hr (by omega) _ _ hpure hcorner hsteep)

/-- ★★ **THE DECIDEDNESS TRANSFER AT THE PINNED DEPTH** (the drainage-shaped socket,
premises carried HONESTLY): factors decided at the `h·d·r`-shifted level make the
product class decided at full level.  The two shifted-decidedness premises are LSF's
named drainage remainder — this theorem is the coupling, not their discharge. -/
theorem decidedAt_mulClass_of_cones [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) {h e' d r N : ℕ}
    (he' : 0 < e') (hd0 : 0 < d) (hr : 0 < r) (hN : 2 * (h * d * r) + 1 ≤ N)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O} {σ₁ σ₂ : FactorizationType}
    (hpure : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) N a₁ j))
    (hcorner : resOrd (proj O (e' * d) N a₁ ⟨0, Nat.mul_pos he' hd0⟩) = h * d)
    (hsteep : ∀ j : Fin r, h * (r - (j : ℕ)) < e' * resOrd (proj O r N a₂ j))
    (hdec₁ : DecidedAt O (e' * d) σ₁ (N - h * d * r)
      (proj O (e' * d) (N - h * d * r) a₁))
    (hdec₂ : DecidedAt O r σ₂ (N - h * d * r) (proj O r (N - h * d * r) a₂)) :
    DecidedAt O (e' * d + r) ⟨σ₁.data + σ₂.data⟩ N
      (mulClass (proj O (e' * d) N a₁) (proj O r N a₂)) :=
  decidedAt_mulClass_of_mixDepth hπ hN (Or.inl (Nat.mul_pos he' hd0).ne')
    (mixDepth_eq_of_cones hπ he' hd0 hr (by omega) _ _ hpure hcorner hsteep)
    hdec₁ hdec₂

end Couplings

section LeafCouplings

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE SUB-FACE CLUSTER LAW** (the leaf composite): every lift of a sub-face
leaf cell splits per LSF's pinned transport, and the factor pair carries a pair
neighborhood of size EXACTLY `q^{h·d·(m − e'·d)}` below half the window — the
`q^v`-cluster granularity of the per-frame count, at the now-KNOWN uniform depth. -/
theorem subface_cluster_law {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ (g R : Polynomial O) (d : ℕ), monicPoly a = g * R ∧ g.Monic ∧ R.Monic
      ∧ 0 < d ∧ g.natDegree = e' * d ∧ e' * d < m ∧ typeOf g = ⟨{(e', d)}⟩
      ∧ R.natDegree = m - e' * d ∧ σ.data = (e', d) ::ₘ (typeOf R).data
      ∧ (classResidualPoly π c h e').natDegree = d
      ∧ (2 * (h * d * (m - e' * d)) + 1 ≤ M + m →
          Nat.card (pairNbhd π (M + m) (h * d * (m - e' * d))
              (fun i : Fin (e' * d) => g.coeff (i : ℕ))
              (fun i : Fin R.natDegree => R.coeff (i : ℕ)))
            = residueCard O ^ (h * d * (m - e' * d))) := by
  obtain ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata, hcrpd, hpin⟩ :=
    subface_depth_pin hπ hm0 hc hF ha
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have he' : 0 < e' := by omega
  exact ⟨g, R, d, heq, hgm, hRm, hd0, hgd, hdm, htyg, hRdeg, hdata, hcrpd,
    fun hwin2 => natCard_pairNbhd_of_mixDepth hπ hwin2
      (Or.inl (Nat.mul_pos he' hd0).ne') (hpin (by omega))⟩

/-- **The witness-frame depth table** (regression, kernel-decided): at LSC's
hand-checked witness `m = 5`, `σ = {(4,1), (1,1)}`, the two admissible frames
`(1,4,1)` and `(3,4,1)` carry pinned depths `h·d·(m − e'·d) ∈ {1, 3}`. -/
theorem witness_frame_depths :
    (subFrames 5 ⟨{(4, 1), (1, 1)}⟩).image
        (fun p => p.1 * p.2.2 * (5 - p.2.1 * p.2.2)) = {1, 3} := by
  rw [subFrames_five_witness]
  decide

/-- **The witness-frame pin** (regression, end-to-end): at `m = 5`, minimal face
`(h, 4)`, the transport block is forced to `d = 1` and the mixing depth of the factor
pair is EXACTLY `h` — the first open frames' ladder constant, concretely. -/
theorem subface_depth_pin_witness {π : O} (hπ : Irreducible π) {M : ℕ}
    {c : Coeff O 5 (M + 5)} (hc : c ∈ leafSubSector O π 5 ⟨{(4, 1), (1, 1)}⟩ M)
    {h : ℕ} (hF : MinFaceAt c h 4) {a : Fin 5 → O} (ha : proj O 5 (M + 5) a = c)
    (hwin : h < M + 5) :
    ∃ (g R : Polynomial O), monicPoly a = g * R ∧ g.natDegree = 4 ∧ R.natDegree = 1
      ∧ mixDepth π (proj O 4 (M + 5) (fun i => g.coeff (i : ℕ)))
          (proj O R.natDegree (M + 5) (fun i => R.coeff (i : ℕ))) = h := by
  obtain ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata, hcrpd, hpin⟩ :=
    subface_depth_pin hπ (by omega) hc hF ha
  have hd1 : d = 1 := by omega
  subst hd1
  have hpin' := hpin (by omega)
  have hval : h * 1 * (5 - 4 * 1) = h := by omega
  exact ⟨g, R, heq, by omega, by omega, hpin'.trans hval⟩

end LeafCouplings

end Uniformity.Density.IFCG67

end

/-! ## AXCHECK FOOTER — §§1–2 and the abstract couplings expect PURE Lean core
`{propext, Classical.choice, Quot.sound}`; the §3/§4 leaf forms additionally inherit
EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, through LSF's transport).
The C.33 cites, `AX_cellRecursion`, and `sorryAx` must NOT occur. -/
#print axioms Uniformity.Density.IFCG67.pow_dvd_resultant_of_cones
#print axioms Uniformity.Density.IFCG67.not_pow_succ_dvd_resultant_of_cones
#print axioms Uniformity.Density.IFCG67.mixDepth_eq_of_cones
#print axioms Uniformity.Density.IFCG67.cone_data_of_isPure
#print axioms Uniformity.Density.IFCG67.subface_depth_pin
#print axioms Uniformity.Density.IFCG67.natCard_pairNbhd_of_cones
#print axioms Uniformity.Density.IFCG67.decidedAt_mulClass_of_cones
#print axioms Uniformity.Density.IFCG67.subface_cluster_law
#print axioms Uniformity.Density.IFCG67.witness_frame_depths
#print axioms Uniformity.Density.IFCG67.subface_depth_pin_witness
