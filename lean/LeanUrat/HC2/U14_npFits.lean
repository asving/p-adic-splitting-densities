/-
Unit U14.NP_fits  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: §C C.2 "N(H,Z) := 1 + the largest BASE level occurring among the coordinates of
T(H,Z)'s equations"; MovesD W4-4 (NP-ID) — THIS UNIT IS NP-ID's ⊆ direction.
deps: U3 (supports ⊆ band), MovesD `bandS`/`NPband` (shape-level band replica), the Defs
addendum `inFreshBandC` (the raw-coordinate band mirror).
difficulty: medium-hard (the htH ↔ bandS arithmetic).
hypothesis_fields: none beyond PrefSet membership.
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U3_freshBand
import LeanUrat.MovesD.D6d_htShape
import LeanUrat.MovesD.D6e_prevRimShape
import LeanUrat.MovesD.D7b_floorShape
import LeanUrat.MovesD.D7c_slotValShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ### Shape-side box confinement: every rim threshold fits the degree-`n` box.

These are pure-shape facts (no history, no policy) powered by the `ShapeWF` certificate
`P.2`.  The chain `(s0_r + wSide_r)·D_r ≤ n` is the shape mirror of W1's "ℓ_r ≤ n": it
descends the window/width chain (`root_box`, `window`, `dchain`, `gmu`, `edvd`) so that the
rim threshold `prevRimS n (r+1) = μ_r·childWidthS_r` never exceeds `n`.  Needed to place a
band coordinate's base index inside `Finset.range n` (the box `NPband` sups over). -/

/-- Box invariant: the window span times the frame width fits the box at every read. -/
private lemma boxInv {n : ℕ} (P : Shape n) :
    ∀ (r : ℕ) (hr : r < (P : ShapePrefix).reads.length),
      (((P : ShapePrefix).reads[r]'hr).s0 + ((P : ShapePrefix).reads[r]'hr).wSide)
        * ((P : ShapePrefix).reads[r]'hr).Dwidth ≤ n := by
  intro r
  induction r with
  | zero =>
    intro hr
    have hD : ((P : ShapePrefix).reads[0]'hr).Dwidth = 1 := P.2.dchain0 hr
    have hbox : ((P : ShapePrefix).reads[0]'hr).s0 + ((P : ShapePrefix).reads[0]'hr).wSide ≤ n :=
      P.2.root_box hr
    rw [hD, Nat.mul_one]; exact hbox
  | succ k ih =>
    intro hr
    have hk : k < (P : ShapePrefix).reads.length := by omega
    have ihk := ih hk
    have hwin := P.2.window k hr
    have hdc := P.2.dchain k hr
    have hgmu := P.2.gmu k hk
    have hed := P.2.edvd k hk
    -- goal: (s0_{k+1} + wSide_{k+1}) * Dwidth_{k+1} ≤ n
    rw [hdc]
    -- childWidthS_k = e_k * g_k * Dwidth_k
    have hcw : ((P : ShapePrefix).reads[k]'hk).childWidthS
        = ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).g
            * ((P : ShapePrefix).reads[k]'hk).Dwidth := rfl
    -- e_k * len_k = wSide_k
    have hlen : ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).len
        = ((P : ShapePrefix).reads[k]'hk).wSide := by
      show ((P : ShapePrefix).reads[k]'hk).e
          * (((P : ShapePrefix).reads[k]'hk).wSide / ((P : ShapePrefix).reads[k]'hk).e)
          = ((P : ShapePrefix).reads[k]'hk).wSide
      exact Nat.mul_div_cancel' hed
    -- (s0_{k+1}+wSide_{k+1}) * childWidthS_k ≤ μ_k * childWidthS_k
    have s1 : (((P : ShapePrefix).reads[k+1]'hr).s0 + ((P : ShapePrefix).reads[k+1]'hr).wSide)
          * ((P : ShapePrefix).reads[k]'hk).childWidthS
        ≤ ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS :=
      Nat.mul_le_mul hwin (le_refl _)
    -- μ_k * childWidthS_k ≤ wSide_k * Dwidth_k
    have s2 : ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS
        ≤ ((P : ShapePrefix).reads[k]'hk).wSide * ((P : ShapePrefix).reads[k]'hk).Dwidth := by
      have e1 : ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS
          = ((P : ShapePrefix).reads[k]'hk).e
              * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
              * ((P : ShapePrefix).reads[k]'hk).Dwidth := by rw [hcw]; ring
      have e2 : ((P : ShapePrefix).reads[k]'hk).e
            * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
          ≤ ((P : ShapePrefix).reads[k]'hk).wSide := by
        calc ((P : ShapePrefix).reads[k]'hk).e
                * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
              ≤ ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).len :=
                Nat.mul_le_mul (le_refl _) hgmu
          _ = ((P : ShapePrefix).reads[k]'hk).wSide := hlen
      rw [e1]
      exact Nat.mul_le_mul e2 (le_refl _)
    -- wSide_k * Dwidth_k ≤ (s0_k + wSide_k) * Dwidth_k
    have s3 : ((P : ShapePrefix).reads[k]'hk).wSide * ((P : ShapePrefix).reads[k]'hk).Dwidth
        ≤ (((P : ShapePrefix).reads[k]'hk).s0 + ((P : ShapePrefix).reads[k]'hk).wSide)
            * ((P : ShapePrefix).reads[k]'hk).Dwidth :=
      Nat.mul_le_mul (Nat.le_add_left _ _) (le_refl _)
    exact le_trans s1 (le_trans s2 (le_trans s3 ihk))

/-- The rim threshold `μ_k · childWidthS_k` fits the box. -/
private lemma muWidth_le {n : ℕ} (P : Shape n) (k : ℕ)
    (hk : k < (P : ShapePrefix).reads.length) :
    ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS ≤ n := by
  have hbox := boxInv P k hk
  have hgmu := P.2.gmu k hk
  have hed := P.2.edvd k hk
  have hcw : ((P : ShapePrefix).reads[k]'hk).childWidthS
      = ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).g
          * ((P : ShapePrefix).reads[k]'hk).Dwidth := rfl
  have hlen : ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).len
      = ((P : ShapePrefix).reads[k]'hk).wSide := by
    show ((P : ShapePrefix).reads[k]'hk).e
        * (((P : ShapePrefix).reads[k]'hk).wSide / ((P : ShapePrefix).reads[k]'hk).e)
        = ((P : ShapePrefix).reads[k]'hk).wSide
    exact Nat.mul_div_cancel' hed
  have e1 : ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS
      = ((P : ShapePrefix).reads[k]'hk).e
          * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
          * ((P : ShapePrefix).reads[k]'hk).Dwidth := by rw [hcw]; ring
  have e2 : ((P : ShapePrefix).reads[k]'hk).e
        * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
      ≤ ((P : ShapePrefix).reads[k]'hk).wSide := by
    calc ((P : ShapePrefix).reads[k]'hk).e
            * (((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ)
          ≤ ((P : ShapePrefix).reads[k]'hk).e * ((P : ShapePrefix).reads[k]'hk).len :=
            Nat.mul_le_mul (le_refl _) hgmu
      _ = ((P : ShapePrefix).reads[k]'hk).wSide := hlen
  have s2 : ((P : ShapePrefix).reads[k]'hk).μ * ((P : ShapePrefix).reads[k]'hk).childWidthS
      ≤ ((P : ShapePrefix).reads[k]'hk).wSide * ((P : ShapePrefix).reads[k]'hk).Dwidth := by
    rw [e1]; exact Nat.mul_le_mul e2 (le_refl _)
  have s3 : ((P : ShapePrefix).reads[k]'hk).wSide * ((P : ShapePrefix).reads[k]'hk).Dwidth
      ≤ (((P : ShapePrefix).reads[k]'hk).s0 + ((P : ShapePrefix).reads[k]'hk).wSide)
          * ((P : ShapePrefix).reads[k]'hk).Dwidth :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (le_refl _)
  exact le_trans s2 (le_trans s3 hbox)

/-- Every rim threshold sits inside the degree-`n` box (`prevRimS n i ≤ n`). -/
private lemma prevRimS_le {n : ℕ} (P : Shape n) (i : ℕ) :
    (P : ShapePrefix).prevRimS n i ≤ n := by
  cases i with
  | zero => exact le_refl n
  | succ k =>
    show ((P : ShapePrefix).reads[k]?).elim n (fun R => R.μ * R.childWidthS) ≤ n
    by_cases hklt : k < (P : ShapePrefix).reads.length
    · rw [List.getElem?_eq_getElem hklt]
      simpa using muWidth_le P k hklt
    · rw [List.getElem?_eq_none (not_lt.mp hklt)]
      exact le_refl n

/-! ### Shape-side level bound: every band coordinate's level is `< Nshape`.

Replica of L9s's private `band_lt_Nshape` (unexported): the level is `≤` the K1-chain
height, which the band caps at the descending line value `≤` its intercept, and
`Nshape = 1 + max_r ⌈intercept_r⌉₊`. -/

/-- Every element of a `ℕ`-list is `≤` the list's `foldr max 0`. -/
private lemma le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

/-- Every band coordinate at read `r` sits strictly below the shape bound `Nshape`. -/
private lemma band_lt_Nshape (P : ShapePrefix) (n r : ℕ) (c : Coord)
    (hr : r < P.reads.length) (hb : P.bandS n r c) : c.1 < P.Nshape := by
  have hget : P.reads[r]? = some (P.reads[r]'hr) := List.getElem?_eq_getElem hr
  set R := P.reads[r]'hr with hR
  unfold ShapePrefix.bandS at hb
  obtain ⟨-, -, h3⟩ := hb
  rw [hget] at h3
  simp only [Option.elim_some] at h3
  have hhtEq : P.htS r c
      = (c.1 : ℚ) + (Finset.range r).sum (fun m => (P.innerslotS m c.2 : ℚ) * P.kappaS m) := rfl
  have hht : (c.1 : ℚ) ≤ P.htS r c := by
    rw [hhtEq]
    have hsum : (0 : ℚ) ≤ (Finset.range r).sum
        (fun m => (P.innerslotS m c.2 : ℚ) * P.kappaS m) := by
      apply Finset.sum_nonneg
      intro m _
      apply mul_nonneg (by positivity)
      unfold ShapePrefix.kappaS
      rcases P.reads[m]? with _ | R'
      · simp
      · simp only [Option.elim_some]; positivity
    linarith
  have hslope : (0 : ℚ) ≤ (P.lineS r).slope := by
    have hs : (P.lineS r).slope
        = (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ)) := by
      unfold ShapePrefix.lineS; rw [hget]; rfl
    rw [hs]; positivity
  have hatx : (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth)
      = (P.lineS r).intercept
        - (P.lineS r).slope * (((c.2 / R.Dwidth) * R.Dwidth : ℕ) : ℚ) := rfl
  have hq : (c.1 : ℚ) ≤ (P.lineS r).intercept := by
    have hchain : (c.1 : ℚ) ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth) :=
      le_trans hht h3
    rw [hatx] at hchain
    have hprod : (0 : ℚ)
        ≤ (P.lineS r).slope * (((c.2 / R.Dwidth) * R.Dwidth : ℕ) : ℚ) :=
      mul_nonneg hslope (by positivity)
    linarith
  have h4a : c.1 ≤ ⌈(P.lineS r).intercept⌉.toNat := by
    have hz : (c.1 : ℤ) ≤ ⌈(P.lineS r).intercept⌉ := by
      exact_mod_cast le_trans hq (Int.le_ceil _)
    simpa using Int.toNat_le_toNat hz
  have hmem : ⌈(P.lineS r).intercept⌉.toNat ∈
      (List.range P.reads.length).map (fun s => ⌈(P.lineS s).intercept⌉.toNat) :=
    List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
  have h4b := le_foldr_max _ _ hmem
  unfold ShapePrefix.Nshape
  omega

/-! ### The unit theorems. -/

/-- NP-ID ⊆: for a shape-matched member, every fresh-band coordinate's level is bounded by
the SHAPE's band bound — `NPband` dominates the history's constrained levels (the band
levels are shape-pinned through `MatchesHist`'s line data). -/
theorem NP_fits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {H : History p F} {pol : CanonPolicy p F} {P : Shape n}
    (hH : H ∈ PrefSet n pol P) :
    ∀ (i : ℕ) (hi : i < H.nodes.length) (c : Coord),
      inFreshBandC H n i (H.nodes[i]'hi) c →
      c.1 + 1 ≤ (P : ShapePrefix).NPband n := by
  classical
  obtain ⟨hP, hcoh, -, -, -⟩ := hH
  intro i hi c hband
  have hlen : H.nodes.length = (P : ShapePrefix).reads.length := hP.choose
  have hi' : i < (P : ShapePrefix).reads.length := by omega
  -- Transfer the raw-coordinate history band to the shape band (conjunct-wise, cf. D8).
  have hiff : inFreshBandC H n i (H.nodes[i]'hi) c ↔ (P : ShapePrefix).bandS n i c := by
    unfold inFreshBandC ShapePrefix.bandS
    rw [htH_shape hP i c, floorH_shape hcoh hP i c.2, prevRim_shape hP i,
      slotVal_shape hcoh hP i hi hi' c.2, List.getElem?_eq_getElem hi']
    simp only [Option.elim_some]
  have hbandS : (P : ShapePrefix).bandS n i c := hiff.mp hband
  -- Level bound and base-index bound place `c` in the box `NPband` sups over.
  have hc1 : c.1 < (P : ShapePrefix).Nshape := band_lt_Nshape (P : ShapePrefix) n i c hi' hbandS
  have hc2 : c.2 < n := by
    have h1 : c.2 < H.prevRim n i := hband.1
    rw [prevRim_shape hP i] at h1
    exact lt_of_lt_of_le h1 (prevRimS_le P i)
  have hmem : c ∈ (Finset.range (P : ShapePrefix).Nshape ×ˢ Finset.range n).filter
      (fun c => ∃ r < (P : ShapePrefix).reads.length, (P : ShapePrefix).bandS n r c) := by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨hc1, hc2⟩, ⟨i, hi', hbandS⟩⟩
  have hle : c.1 ≤ ((Finset.range (P : ShapePrefix).Nshape ×ˢ Finset.range n).filter
      (fun c => ∃ r < (P : ShapePrefix).reads.length, (P : ShapePrefix).bandS n r c)).sup
      (fun c => c.1) := Finset.le_sup hmem
  unfold ShapePrefix.NPband
  omega

/-- Box form (C.2's "N ≥ N(H,Z)" largeness at the shape bound): at `N ≥ NPband`, every
constructed fresh support coordinate has base level `< N` — the system fits the box. -/
theorem NP_fits_box {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n N : ℕ} {H : History p F} {pol : CanonPolicy p F} {P : Shape n}
    (hH : H ∈ PrefSet n pol P) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hNP : (P : ShapePrefix).NPband n ≤ N) :
    ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses,
      ∀ c ∈ cl.support, (boxChart n N c).1 + 1 ≤ N := by
  intro i hi cl hcl c hc
  -- U3: the constructed support lies in the band; the raw-coordinate mirror is the same formula.
  have hband : inFreshBandC H n i (H.nodes[i]'hi) (boxChart n N c) :=
    mkFresh_band H n N S vOf i hi cl hcl c hc
  -- U14 (NP_fits) at the box coordinate, then the shape bound `NPband ≤ N`.
  exact le_trans (NP_fits hH i hi (boxChart n N c) hband) hNP

end LeanUrat.MovesJ
