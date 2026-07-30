/-
Unit XA.7a latSlice  [PROVED, no sorry, core axioms only]
moves_ref: (IND)'s region as column blocks (slice above rectangle; stride vertices
absorbed). deps: Defs. difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The block index `(x - s0 - 1) / e = k` is exactly membership of `x` in the `k`-th
stride column `(s0 + k·e, s0 + (k+1)·e]`. -/
private lemma block_iff (s0 e k x : ℕ) (he : 1 ≤ e) (hx : s0 < x) :
    (x - s0 - 1) / e = k ↔ (s0 + k * e < x ∧ x ≤ s0 + (k + 1) * e) := by
  have h1 := Nat.le_div_iff_mul_le (k := e) (x := k) (y := x - s0 - 1) he
  have h2 := Nat.div_lt_iff_lt_mul (k := e) (x := x - s0 - 1) (y := k + 1) he
  omega

/-- Translating a point out of the `k`-th column and above the `(ℓ-1-k)`-row block sends
the local (ℓ=1) segment constraint to the global (ℓ) segment constraint. -/
private lemma tri_equiv (s0 u0 e h ell k x y : ℕ) (hkl : k < ell)
    (hx : s0 + k * e < x) (hy : u0 + (ell - 1 - k) * h < y) :
    (h * (x - (s0 + k * e)) + e * (y - (u0 + (ell - 1 - k) * h)) ≤ e * h ↔
      h * (x - s0) + e * (y - u0) ≤ e * h * ell) := by
  obtain ⟨d1, hd1⟩ : ∃ d1, x = s0 + k * e + d1 := ⟨x - (s0 + k * e), by omega⟩
  obtain ⟨d2, hd2⟩ : ∃ d2, y = u0 + (ell - 1 - k) * h + d2 := ⟨y - (u0 + (ell - 1 - k) * h), by omega⟩
  have e1 : x - (s0 + k * e) = d1 := by omega
  have e2 : y - (u0 + (ell - 1 - k) * h) = d2 := by omega
  have e3 : x - s0 = k * e + d1 := by omega
  have e4 : y - u0 = (ell - 1 - k) * h + d2 := by omega
  rw [e1, e2, e3, e4]
  have hexp : h * (k * e + d1) + e * ((ell - 1 - k) * h + d2)
      = (h * d1 + e * d2) + (h * (k * e) + e * ((ell - 1 - k) * h)) := by ring
  have hIell : e * h * ell = e * h + (h * (k * e) + e * ((ell - 1 - k) * h)) := by
    have hsum : 1 + k + (ell - 1 - k) = ell := by omega
    calc e * h * ell = e * h * (1 + k + (ell - 1 - k)) := by rw [hsum]
      _ = e * h + (h * (k * e) + e * ((ell - 1 - k) * h)) := by ring
  rw [hexp, hIell]
  omega

/-- In the `k`-th column, the global segment constraint pins the height below the top of
the `(ℓ-1-k)`-block's slice: `y ≤ u0 + (ℓ-1-k)·h + h`. -/
private lemma ybound (s0 u0 e h ell k x y : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hkl : k < ell)
    (hx : s0 + k * e < x) (htri : h * (x - s0) + e * (y - u0) ≤ e * h * ell) :
    y ≤ u0 + (ell - 1 - k) * h + h := by
  obtain ⟨d1, hd1⟩ : ∃ d1, x = s0 + k * e + (d1 + 1) := ⟨x - (s0 + k * e) - 1, by omega⟩
  have e3 : x - s0 = k * e + (d1 + 1) := by omega
  rw [e3] at htri
  have key : e * (y - u0) < e * ((ell - k) * h) := by
    have hexp : h * (k * e + (d1 + 1)) = h * (k * e) + h * d1 + h := by ring
    have hIell : e * h * ell = e * ((ell - k) * h) + h * (k * e) := by
      have hsum : (ell - k) + k = ell := by omega
      calc e * h * ell = e * h * ((ell - k) + k) := by rw [hsum]
        _ = e * ((ell - k) * h) + h * (k * e) := by ring
    omega
  have hlt := Nat.lt_of_mul_lt_mul_left key
  have hid2 : (ell - 1 - k) * h + h = (ell - k) * h := by
    have he1 : (ell - 1 - k) + 1 = ell - k := by omega
    calc (ell - 1 - k) * h + h = ((ell - 1 - k) + 1) * h := by ring
      _ = (ell - k) * h := by rw [he1]
  omega

/-- The `k`-th column of the (ℓ) region splits as a rectangle of `e·(ℓ-1-k)·h` low points
plus a translated copy of the (ℓ=1) region. -/
private lemma fiber_card (s0 u0 e h ell k : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hk : k < ell) :
    (Finset.filter (fun q : ℕ × ℕ => (q.1 - s0 - 1) / e = k) (p1Region s0 u0 e h ell)).card
      = (p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card + e * ((ell - 1 - k) * h) := by
  set Fk := Finset.filter (fun q : ℕ × ℕ => (q.1 - s0 - 1) / e = k) (p1Region s0 u0 e h ell) with hFk
  have hkexp : (k + 1) * e = k * e + e := by ring
  have hle : (k + 1) * e ≤ e * ell := by
    rw [Nat.mul_comm e ell]; exact Nat.mul_le_mul_right e (by omega)
  -- rectangle: the low points of the column, triangle constraint automatic
  have hStepB : Finset.filter (fun q => q.2 ≤ u0 + (ell - 1 - k) * h) Fk
      = Finset.Ioc (s0 + k * e) (s0 + (k + 1) * e) ×ˢ Finset.Ioc u0 (u0 + (ell - 1 - k) * h) := by
    ext q
    simp only [hFk, Finset.mem_filter, p1Region, Finset.mem_product, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, htri⟩, hblk⟩, hyB⟩
      exact ⟨(block_iff s0 e k q.1 he hx1).mp hblk, hy1, hyB⟩
    · rintro ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
      have hx1 : s0 < q.1 := by omega
      have hle2 : (ell - 1 - k) * h ≤ h * ell := by
        rw [Nat.mul_comm h ell]; exact Nat.mul_le_mul_right h (by omega)
      have hid : h * ((k + 1) * e) + e * ((ell - 1 - k) * h) = e * h * ell := by
        have hsum : (k + 1) + (ell - 1 - k) = ell := by omega
        calc h * ((k + 1) * e) + e * ((ell - 1 - k) * h)
            = e * h * ((k + 1) + (ell - 1 - k)) := by ring
          _ = e * h * ell := by rw [hsum]
      have htri : h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell := by
        calc h * (q.1 - s0) + e * (q.2 - u0)
            ≤ h * ((k + 1) * e) + e * ((ell - 1 - k) * h) := by gcongr <;> omega
          _ = e * h * ell := hid
      exact ⟨⟨⟨⟨⟨hx1, (by omega : q.1 ≤ s0 + e * ell)⟩, hylo,
               (by omega : q.2 ≤ u0 + h * ell)⟩, htri⟩,
             (block_iff s0 e k q.1 he hx1).mpr ⟨hxlo, hxhi⟩⟩, hyhi⟩
  -- slice: the high points of the column = translated (ℓ=1) region
  have hStepC : Finset.filter (fun q => ¬ q.2 ≤ u0 + (ell - 1 - k) * h) Fk
      = p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1 := by
    ext q
    simp only [hFk, Finset.mem_filter, p1Region, Finset.mem_product, Finset.mem_Ioc, mul_one]
    constructor
    · rintro ⟨⟨⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, htri⟩, hblk⟩, hyB⟩
      have hint := (block_iff s0 e k q.1 he hx1).mp hblk
      have hylo : u0 + (ell - 1 - k) * h < q.2 := by omega
      exact ⟨⟨⟨hint.1, (by omega : q.1 ≤ s0 + k * e + e)⟩, hylo,
               ybound s0 u0 e h ell k q.1 q.2 he hh hk hint.1 htri⟩,
             (tri_equiv s0 u0 e h ell k q.1 q.2 hk hint.1 hylo).mpr htri⟩
    · rintro ⟨⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩, htri_tk⟩
      have hx1 : s0 < q.1 := by omega
      have hle3 : (ell - 1 - k) * h + h ≤ h * ell := by
        have he1 : (ell - 1 - k) + 1 = ell - k := by omega
        calc (ell - 1 - k) * h + h = ((ell - 1 - k) + 1) * h := by ring
          _ = (ell - k) * h := by rw [he1]
          _ ≤ ell * h := Nat.mul_le_mul_right h (by omega)
          _ = h * ell := Nat.mul_comm ell h
      exact ⟨⟨⟨⟨⟨hx1, (by omega : q.1 ≤ s0 + e * ell)⟩,
               (by omega : u0 < q.2), (by omega : q.2 ≤ u0 + h * ell)⟩,
              (tri_equiv s0 u0 e h ell k q.1 q.2 hk hxlo hylo).mp htri_tk⟩,
             (block_iff s0 e k q.1 he hx1).mpr ⟨hxlo, (by omega : q.1 ≤ s0 + (k + 1) * e)⟩⟩,
             (by omega : ¬ q.2 ≤ u0 + (ell - 1 - k) * h)⟩
  have hsplit : Fk.card
      = (Finset.filter (fun q => q.2 ≤ u0 + (ell - 1 - k) * h) Fk).card
        + (Finset.filter (fun q => ¬ q.2 ≤ u0 + (ell - 1 - k) * h) Fk).card :=
    (Finset.card_filter_add_card_filter_not (s := Fk) (fun q => q.2 ≤ u0 + (ell - 1 - k) * h)).symm
  rw [hsplit, hStepB, hStepC, Finset.card_product, Nat.card_Ioc, Nat.card_Ioc]
  have h1 : s0 + (k + 1) * e - (s0 + k * e) = e := by omega
  have h2 : u0 + (ell - 1 - k) * h - u0 = (ell - 1 - k) * h := by omega
  rw [h1, h2]
  exact Nat.add_comm _ _

theorem latSlice (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) :
    (p1Region s0 u0 e h ell).card =
      ∑ k ∈ Finset.range ell,
        ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card
          + e * ((ell - 1 - k) * h)) := by
  have hmaps : Set.MapsTo (fun q : ℕ × ℕ => (q.1 - s0 - 1) / e)
      (↑(p1Region s0 u0 e h ell)) (↑(Finset.range ell)) := by
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_range, p1Region, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc] at hq ⊢
    rw [Nat.div_lt_iff_lt_mul he]
    have hc : e * ell = ell * e := Nat.mul_comm e ell
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact fiber_card s0 u0 e h ell k he hh hk

end LeanUrat.MovesX
