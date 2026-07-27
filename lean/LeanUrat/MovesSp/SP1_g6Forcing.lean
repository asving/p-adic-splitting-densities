/-
Unit Sp.g6Forcing — moves_ref: "(G6) TERMINAL RULE: selection = ⊥ iff W = 1.
[A W = 1 window forces the whole side datum — e = ℓ = 1, s₀′ = a = 0, λ = {(1,1)},
no flanks —]".
sketch: s0 + e·ℓ ≤ 1 with e, ℓ ≥ 1 pins e = ℓ = 1, s0 = 0; a = 0/1 = 0; Σ gμ = 1
with positive parts pins λ singleton (1,1); flanks: compositions of span 0; sel by
(G6)→. Multiset step: induction/`Multiset.sum_eq_zero` on the erase.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- A list of positive naturals summing to `0` is empty (flank of span 0). -/
private theorem list_nil_of_sum_zero {l : List ℕ} (hpos : ∀ x ∈ l, 1 ≤ x)
    (hsum : l.sum = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons h t =>
    have h1 : 1 ≤ h := hpos h (by simp)
    rw [List.sum_cons] at hsum
    exact absurd hsum (by omega)

/-- A residual partition whose weights `Σ g·μ = 1` with all parts positive is the
singleton `{(1,1)}` (the (G4)/`WellTyped` forcing at W = 1). -/
private theorem lam_singleton {lam : Multiset (ℕ × ℕ)}
    (hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2)
    (hsum : (lam.map fun gm => gm.1 * gm.2).sum = 1) : lam = {(1, 1)} := by
  -- each mapped weight is ≥ 1
  have hmpos : ∀ x ∈ lam.map fun gm => gm.1 * gm.2, 1 ≤ x := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨gm, hgm, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hpos gm hgm
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- card ≤ sum = 1
  have hub : Multiset.card lam ≤ 1 := by
    have hcs := Multiset.card_nsmul_le_sum hmpos
    rw [hsum, Multiset.card_map] at hcs
    simpa using hcs
  -- nonempty, so card = 1
  have hne : lam ≠ 0 := by rintro rfl; simp at hsum
  have hcard : Multiset.card lam = 1 := by
    have := Multiset.card_pos.mpr hne
    omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hcard
  rw [Multiset.map_singleton, Multiset.sum_singleton] at hsum
  -- hsum : a.1 * a.2 = 1
  have hae : a = (1, 1) :=
    Prod.ext_iff.mpr ⟨Nat.eq_one_of_mul_eq_one_right hsum, Nat.eq_one_of_mul_eq_one_left hsum⟩
  rw [hae]

theorem w1_forces {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
    (hW : s.W = 1) : s.e = 1 ∧ s.ell = 1 ∧ s.s0 = 0 ∧ s.a = 0 ∧ s.lam = {(1,1)} ∧
    s.lflank = [] ∧ s.rflank = [] ∧ s.sel = none := by
  obtain ⟨⟨_, _, _, he, hell, hlampos⟩,
    ⟨⟨hlpos, hlsum⟩, hspan, hrpos⟩, hg2, _, ⟨hlamsum, _⟩, hg6⟩ := hc
  -- (G1) span at W = 1: s0 + e·ℓ + rflank.sum = 1, with e·ℓ ≥ 1
  rw [hW, show s.wraw = s.e * s.ell from rfl] at hspan
  have hpos : 0 < s.e * s.ell := Nat.mul_pos he hell
  have hcore : s.s0 = 0 ∧ s.e * s.ell = 1 ∧ s.rflank.sum = 0 := by omega
  obtain ⟨hs0, hmul, hrsum⟩ := hcore
  have hee : s.e = 1 := Nat.eq_one_of_mul_eq_one_right hmul
  have helle : s.ell = 1 := Nat.eq_one_of_mul_eq_one_left hmul
  -- (G2) anchor a = ⌊s0/e⌋ = 0
  have ha : s.a = 0 := by rw [hg2, hs0, Nat.zero_div]
  -- flanks: compositions of span 0 are empty
  have hlflank : s.lflank = [] := list_nil_of_sum_zero hlpos (hlsum.trans hs0)
  have hrflank : s.rflank = [] := list_nil_of_sum_zero hrpos hrsum
  -- (G6) selection ⊥ at W = 1
  have hsel : s.sel = none := hg6.mpr hW
  -- (G4) residual weights sum to ℓ = 1 ⇒ λ = {(1,1)}
  have hlam : s.lam = {(1, 1)} := lam_singleton hlampos (hlamsum.trans helle)
  exact ⟨hee, helle, hs0, ha, hlam, hlflank, hrflank, hsel⟩

end LeanUrat.MovesSp
