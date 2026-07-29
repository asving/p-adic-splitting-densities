/-  MovesV unit V6-3b `blk2_census` (NINE POINTS C20) — the m₂ outcome census:
    quadratics y² + wy + u over (u, w) ∈ Fˣ × F classified split/inert/double
    (the V6-1c divisibility predicate); the (iv)-REP (D2)-EMPTY face is
    discharged-by-typing (the count sets don't mention t).
    SCOPE RECORD (round-4 ratification, boundary-record rule — accuracy over
    strength): `blk2_census` proves (i) the SPLIT count = Tsplit exactly, and
    (ii) the rc=0 count = Tinert (the right disjunct) via the three moment
    identities — it does NOT separately identify the DOUBLE class as its own
    conjunct (Tdbl is pinned only through the k-moment, 2·split = (q−1)(q−2),
    and the total); a three-conjunct restatement is open V6 work, not claimed.
    The nine-point roster and the campaign's "178 exact checks" remain
    EXTERNAL EVIDENCE — not cited by, and certifying nothing in, this file. -/
import LeanUrat.MovesV.V6_a1census

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

open Finset

def isRoot2 {F : Type*} [Field F] [DecidableEq F] (w u r : F) : Bool :=
  decide (r ^ 2 + w * r + u = 0)

/-- (y−r)² = y² + wy + u: the char-free double test. -/
def isDbl2 {F : Type*} [Field F] [DecidableEq F] (w u r : F) : Bool :=
  decide (w = -(2 * r) ∧ u = r ^ 2)

open Classical in
noncomputable def quadClassCount (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (rc : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : F × F => p.1 ≠ 0 ∧
    (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = rc)).card

/-- A monic quadratic has at most two roots (char-free). -/
private lemma isRoot2_card_le_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (w u : F) : (Finset.univ.filter (fun r : F => isRoot2 w u r)).card ≤ 2 := by
  by_contra h
  rw [not_le, Finset.two_lt_card_iff] at h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRoot2, decide_eq_true_eq] at ha hb hc
  have e1 : a + b + w = 0 := by
    have h' : (a - b) * (a + b + w) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hab
    · exact h''
  have e2 : a + c + w = 0 := by
    have h' : (a - c) * (a + c + w) = 0 := by linear_combination ha - hc
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hac
    · exact h''
  exact hbc (by linear_combination e1 - e2)

/-- Σ over (u,w)∈Fˣ×F of the root-count equals |Fˣ|². -/
private lemma blk2_sumk_geom (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card)
      = (Finset.univ.filter (fun x : F => x ≠ 0)).card
          * (Finset.univ.filter (fun x : F => x ≠ 0)).card := by
  rw [show (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card)
      = ((Finset.univ.filter (fun p : F × F => p.1 ≠ 0)).sigma
          (fun p => Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r))).card
      from (Finset.card_sigma _ _).symm]
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun a _ => (a.2, a.2 + a.1.2))
      (fun b _ => ⟨(-(b.1 * b.2), b.2 - b.1), b.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨u, w⟩, r⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, isRoot2,
      decide_eq_true_eq] at ha
    obtain ⟨hu, hr⟩ := ha
    have hfac : u = -(r * (r + w)) := by linear_combination hr
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩ <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro h; apply hu; rw [hfac, h]; ring
    · intro h; apply hu; rw [hfac, show r + w = 0 from h]; ring
  · rintro ⟨x, y⟩ hb
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hx, hy⟩ := hb
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact neg_ne_zero.mpr (mul_ne_zero hx hy)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRoot2, decide_eq_true_eq]
      ring
  · rintro ⟨⟨u, w⟩, r⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, isRoot2,
      decide_eq_true_eq] at ha
    obtain ⟨hu, hr⟩ := ha
    have hu' : u = -(r * (r + w)) := by linear_combination hr
    simp only [add_sub_cancel_left, hu']
  · rintro ⟨x, y⟩ hb
    change ((x, x + (y - x)) : F × F) = (x, y)
    simp only [Prod.mk.injEq, true_and]
    ring

/-- Σ over (u,w)∈Fˣ×F of the ordered-distinct-root-pair count equals |Fˣ|(|Fˣ|−1). -/
private lemma blk2_sumkk_geom (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).offDiag.card)
      = (Finset.univ.filter (fun x : F => x ≠ 0)).offDiag.card := by
  rw [show (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).offDiag.card)
      = ((Finset.univ.filter (fun p : F × F => p.1 ≠ 0)).sigma
          (fun p => (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).offDiag)).card
      from (Finset.card_sigma _ _).symm]
  refine Finset.card_bij' (fun a _ => a.2)
      (fun b _ => ⟨(b.1 * b.2, -(b.1 + b.2)), b⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨u, w⟩, ⟨r, s⟩⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag,
      isRoot2, decide_eq_true_eq] at ha
    obtain ⟨hu, hr, hs, hrs⟩ := ha
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, hrs⟩ <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro h; apply hu; have hu2 : u = -(r * (r + w)) := by linear_combination hr
      rw [hu2, h]; ring
    · intro h; apply hu; have hu2 : u = -(s * (s + w)) := by linear_combination hs
      rw [hu2, h]; ring
  · rintro ⟨x, y⟩ hb
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hx, hy, hxy⟩ := hb
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mul_ne_zero hx hy
    · rw [Finset.mem_offDiag]
      refine ⟨?_, ?_, hxy⟩ <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRoot2, decide_eq_true_eq]
      · ring
      · ring
  · rintro ⟨⟨u, w⟩, ⟨r, s⟩⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag,
      isRoot2, decide_eq_true_eq] at ha
    obtain ⟨hu, hr, hs, hrs⟩ := ha
    have hw' : w = -(r + s) := by
      have hz : (r - s) * (r + s + w) = 0 := by linear_combination hr - hs
      have hzz : r + s + w = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd (sub_eq_zero.mp h) hrs
        · exact h
      linear_combination hzz
    have hu' : u = r * s := by rw [hw'] at hr; linear_combination hr
    simp only [hu', hw']
  · rintro ⟨x, y⟩ hb
    rfl

theorem blk2_census (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (quadClassCount F 2 : ℚ) = Tsplit.eval q ∧
    ((quadClassCount F 1 : ℚ) = Tinert.eval q + Tdbl.eval q ∨
     (quadClassCount F 0 : ℚ) = Tinert.eval q) := by
  set n := Fintype.card F with hn
  have hn2 : 1 < n := Fintype.one_lt_card
  -- root-count bound at each (u,w)
  have hle : ∀ p : F × F, (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card ≤ 2 :=
    fun p => isRoot2_card_le_two p.2 p.1
  -- pointwise decompositions (using k ≤ 2)
  have hpt : ∀ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
      (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card
        = (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 1 then 1 else 0)
          + 2 * (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 2 then 1 else 0) := by
    intro p _
    have h := hle p
    set c := (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card with hc
    interval_cases c <;> decide
  have hptdiff : ∀ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
      (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).offDiag.card
        = 2 * (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 2 then 1 else 0) := by
    intro p _
    have h := hle p
    rw [Finset.offDiag_card]
    set c := (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card with hc
    interval_cases c <;> decide
  have hpt1 : ∀ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
      (1 : ℕ) = (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 0 then 1 else 0)
          + (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 1 then 1 else 0)
          + (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = 2 then 1 else 0) := by
    intro p _
    have h := hle p
    set c := (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card with hc
    interval_cases c <;> decide
  -- quadClassCount as a sum of indicators over Fˣ×F
  have hQ : ∀ rc : ℕ, quadClassCount F rc =
      ((Finset.univ.filter (fun p : F × F => p.1 ≠ 0)).filter
        (fun p => (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = rc)).card := by
    intro rc
    unfold quadClassCount
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hN : ∀ rc : ℕ, quadClassCount F rc
      = ∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
          (if (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card = rc then 1 else 0) := by
    intro rc
    rw [hQ rc, Finset.card_filter]
  -- combine pointwise with sum identities
  have esumk : (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).card)
      = quadClassCount F 1 + 2 * quadClassCount F 2 := by
    rw [hN 1, hN 2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt
  have esumkk : (∑ p ∈ Finset.univ.filter (fun p : F × F => p.1 ≠ 0),
        (Finset.univ.filter (fun r : F => isRoot2 p.2 p.1 r)).offDiag.card)
      = 2 * quadClassCount F 2 := by
    rw [hN 2, Finset.mul_sum]
    exact Finset.sum_congr rfl hptdiff
  have ecard : (Finset.univ.filter (fun p : F × F => p.1 ≠ 0)).card
      = quadClassCount F 0 + quadClassCount F 1 + quadClassCount F 2 := by
    rw [Finset.card_eq_sum_ones, hN 0, hN 1, hN 2, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt1
  -- geometry of Fˣ×F
  have hPprod : (Finset.univ.filter (fun p : F × F => p.1 ≠ 0))
      = (Finset.univ.filter (fun x : F => x ≠ 0)) ×ˢ Finset.univ := by
    ext ⟨u, w⟩
    simp [Finset.mem_product, Finset.mem_filter]
  have vcardP : (Finset.univ.filter (fun p : F × F => p.1 ≠ 0)).card
      = (Finset.univ.filter (fun x : F => x ≠ 0)).card * n := by
    rw [hPprod, Finset.card_product, Finset.card_univ]
  -- the three ℕ moment identities
  have hAnat : 2 * quadClassCount F 2 = (Finset.univ.filter (fun x : F => x ≠ 0)).offDiag.card :=
    esumkk.symm.trans (blk2_sumkk_geom F)
  have hBnat : quadClassCount F 1 + 2 * quadClassCount F 2
      = (Finset.univ.filter (fun x : F => x ≠ 0)).card * (Finset.univ.filter (fun x : F => x ≠ 0)).card :=
    esumk.symm.trans (blk2_sumk_geom F)
  have hCnat : quadClassCount F 0 + quadClassCount F 1 + quadClassCount F 2
      = (Finset.univ.filter (fun x : F => x ≠ 0)).card * n := ecard.symm.trans vcardP
  -- transport to ℚ
  have hMn : (Finset.univ.filter (fun x : F => x ≠ 0)).card = n - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hcast : ((n - 1 : ℕ) : ℚ) = q - 1 := by
    rw [Nat.cast_sub (by omega), hq, Nat.cast_one]
  have hM : ((Finset.univ.filter (fun x : F => x ≠ 0)).card : ℚ) = q - 1 := by
    rw [hMn, hcast]
  have hOD : ((Finset.univ.filter (fun x : F => x ≠ 0)).offDiag.card : ℚ) = (q - 1) * (q - 2) := by
    rw [Finset.offDiag_card, hMn,
      Nat.cast_sub (Nat.le_mul_of_pos_left _ (show 0 < n - 1 by omega)), Nat.cast_mul, hcast]
    ring
  have e1 : 2 * (quadClassCount F 2 : ℚ) = (q - 1) * (q - 2) := by
    rw [← hOD]; exact_mod_cast hAnat
  have e2 : (quadClassCount F 1 : ℚ) + 2 * (quadClassCount F 2 : ℚ) = (q - 1) * (q - 1) := by
    rw [← hM]; exact_mod_cast hBnat
  have e3 : (quadClassCount F 0 : ℚ) + (quadClassCount F 1 : ℚ) + (quadClassCount F 2 : ℚ)
      = (q - 1) * q := by
    rw [← hM, ← hq]; exact_mod_cast hCnat
  -- closed forms of the roster polynomials
  have hTsplit : Tsplit.eval q = 1 / 2 * ((q - 1) * (q - 2)) := by
    simp only [Tsplit, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hTinert : Tinert.eval q = 1 / 2 * (q * (q - 1)) := by
    simp only [Tinert, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one]
  refine ⟨?_, Or.inr ?_⟩
  · rw [hTsplit]; linear_combination e1 / 2
  · rw [hTinert]; linear_combination e3 - e2 + (1 / 2) * e1

end LeanUrat.MovesV
