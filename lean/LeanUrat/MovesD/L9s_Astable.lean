/-
Unit L9s.A_stable  (MovesD campaign, E-phase)  [AUX]
informal: A(P̂, n, N) is N-stable above the shape height bound (the note's "a priori shape
bound … available but not needed" — HERE it IS needed, to make A′ N-free).
deps: Defs.
sketch: band coordinates satisfy ℓ ≤ htS ≤ line value ≤ intercept < Nshape, so levels in
[Nshape, N) contribute nothing; filter congruence on the grid split.
difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n N : ℕ}

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

/-- **The height-bound mechanism** (L9s): every band coordinate at read `r` sits strictly
below the a-priori shape bound `Nshape`. In coordinates: the level `c.1` is `≤` the
K1-chain height `htS r c` (the offset sum is nonnegative), which the band caps at the
descending line value `≤` the line's intercept; since `Nshape = 1 + max_r ⌈intercept_r⌉₊`,
the level is `< Nshape`. [DE-PRIVATIZED 2026-07-29 (visibility-only, no statement
change): consumed by MovesT T-D7 `np_id` (the adjudicated round-3 repair — the ⊆ leg
routes fresh_band → band_shape → this bound; recorded in MovesT/MANIFEST.json).] -/
lemma band_lt_Nshape (P : ShapePrefix) (n r : ℕ) (c : Coord)
    (hr : r < P.reads.length) (hb : P.bandS n r c) : c.1 < P.Nshape := by
  have hget : P.reads[r]? = some (P.reads[r]'hr) := List.getElem?_eq_getElem hr
  set R := P.reads[r]'hr with hR
  -- Extract the band's upper-edge conjunct.
  unfold ShapePrefix.bandS at hb
  obtain ⟨-, -, h3⟩ := hb
  rw [hget] at h3
  simp only [Option.elim_some] at h3
  -- (1) The K1-chain height dominates the level: `c.1 ≤ htS r c`.
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
  -- (2) The line has nonnegative slope.
  have hslope : (0 : ℚ) ≤ (P.lineS r).slope := by
    have hs : (P.lineS r).slope
        = (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ)) := by
      unfold ShapePrefix.lineS; rw [hget]; rfl
    rw [hs]; positivity
  -- (3) A descending line value never exceeds its intercept.
  have hatx : (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth)
      = (P.lineS r).intercept
        - (P.lineS r).slope * (((c.2 / R.Dwidth) * R.Dwidth : ℕ) : ℚ) := rfl
  -- Chain: `c.1 ≤ htS ≤ line value ≤ intercept`.
  have hq : (c.1 : ℚ) ≤ (P.lineS r).intercept := by
    have hchain : (c.1 : ℚ) ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth) :=
      le_trans hht h3
    rw [hatx] at hchain
    have hprod : (0 : ℚ)
        ≤ (P.lineS r).slope * (((c.2 / R.Dwidth) * R.Dwidth : ℕ) : ℚ) :=
      mul_nonneg hslope (by positivity)
    linarith
  -- (4) Turn the rational intercept bound into `c.1 < Nshape`.
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

/-- A-stability above the shape height bound: A(n, N) = A′(n) whenever Nshape ≤ N. -/
theorem A_stable {P : Shape n} (hN : (P : ShapePrefix).Nshape ≤ N) :
    (P : ShapePrefix).A n N = (P : ShapePrefix).A' n := by
  unfold ShapePrefix.A' ShapePrefix.A
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hc2⟩, hb⟩
    exact ⟨⟨band_lt_Nshape (P : ShapePrefix) n r c hr hb, hc2⟩, hb⟩
  · rintro ⟨⟨hc1, hc2⟩, hb⟩
    exact ⟨⟨lt_of_lt_of_le hc1 hN, hc2⟩, hb⟩

end LeanUrat.MovesD
