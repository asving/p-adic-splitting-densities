/-
Unit Sp.fullForcing — moves_ref: "(i) At each fixed (tag, D, w, W) there is AT
MOST ONE full letter: μ = W with (B4)'s g·μ ≤ ℓ and (B3)'s a + ℓ ≤ W forces
g = 1, ℓ = W, a = 0, λ = {(1, W)} …; then (B3)'s s₀′ + w′ ≤ W with w′ = e·ℓ = e·W
forces e = 1 and s₀′ = 0 …, by (G1) both flanks empty, by (G3) slots {0, …, W}".
sketch: sel = (1, W): (B4) W ≤ ℓ; (B3) a + ℓ ≤ W ⇒ ℓ = W, a = 0; λ: member (1, W)
with Σ = W ⇒ erase has sum 0 & positive parts ⇒ singleton (`Multiset.cons_erase`
+ sum_eq_zero); (B3) s0 + e·W ≤ W, e ≥ 1, W ≥ 1 ⇒ e = 1, s0 = 0; (G1) flanks span
0; (G3). difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem full_forces {n} {s : Species} (hc : Coherent s)
    (hb : Budget n s) (hf : IsFull s) : s.e = 1 ∧ s.ell = s.W ∧ s.a = 0 ∧ s.s0 = 0 ∧
    s.lam = {(1, s.W)} ∧ s.lflank = [] ∧ s.rflank = [] ∧
    s.slots = Finset.Icc 0 s.W := by
  -- Unpack coherence and budget.
  obtain ⟨hWT, hA, _hG2, hC, hD, _hG6⟩ := hc
  obtain ⟨_hDpos, _hwpos, hW, he, _hellpos, hlam_pos⟩ := hWT
  obtain ⟨hcomp, hG1sum, hG1r⟩ := hA
  obtain ⟨hG1lpos, hG1lsum⟩ := hcomp
  obtain ⟨hG3slot, _hG3d⟩ := hC
  obtain ⟨hG4sum, hG4sel⟩ := hD
  obtain ⟨_hbD, _hbw, hB3, hB4, _hB5⟩ := hb
  obtain ⟨hB3a, hB3b, _hB3c, _hB3d⟩ := hB3
  -- `IsFull` as the raw selection equation.
  have hf' : s.sel = some (1, s.W) := hf
  -- (B4) with the full letter: 1·W ≤ ℓ.
  have hB4' : (1 : ℕ) * s.W ≤ s.ell := hB4 (1, s.W) hf'
  -- (B3) `a + ℓ ≤ W` together with the above pins ℓ = W and a = 0.
  have hell_eq : s.ell = s.W := by omega
  have ha : s.a = 0 := by omega
  -- (B3) `s₀ + w′ ≤ W` with w′ = e·ℓ = e·W and e,W ≥ 1 forces e = 1, s₀ = 0.
  unfold Species.wraw at hB3a
  rw [hell_eq] at hB3a
  have hle : s.e * s.W ≤ s.W := by omega
  have hge : s.W ≤ s.e * s.W := Nat.le_mul_of_pos_left s.W he
  have heW : s.e * s.W = s.W := le_antisymm hle hge
  have he_eq : s.e = 1 := Nat.eq_of_mul_eq_mul_right hW (by rw [heW, one_mul])
  have hs0 : s.s0 = 0 := by omega
  -- The λ-multiset: (1,W) is a member, and it carries all the sum ℓ = W.
  have hmem : (1, s.W) ∈ s.lam := hG4sel (1, s.W) hf'
  obtain ⟨r, hr⟩ : ∃ r, s.lam = (1, s.W) ::ₘ r :=
    ⟨s.lam.erase (1, s.W), (Multiset.cons_erase hmem).symm⟩
  have hrsum : (Multiset.map (fun gm : ℕ × ℕ => gm.1 * gm.2) r).sum = 0 := by
    have h := hG4sum
    rw [hr, hell_eq, Multiset.map_cons, Multiset.sum_cons] at h
    omega
  have hr0 : r = 0 := by
    by_contra hne
    obtain ⟨gm, hgm⟩ := Multiset.exists_mem_of_ne_zero hne
    have hgmlam : gm ∈ s.lam := by rw [hr]; exact Multiset.mem_cons_of_mem hgm
    obtain ⟨hg1, hg2⟩ := hlam_pos gm hgmlam
    have hpos : 0 < gm.1 * gm.2 := Nat.mul_pos hg1 hg2
    have hin : gm.1 * gm.2 ∈ Multiset.map (fun gm : ℕ × ℕ => gm.1 * gm.2) r :=
      Multiset.mem_map_of_mem _ hgm
    have hle0 : gm.1 * gm.2 ≤ 0 := by
      calc gm.1 * gm.2
          ≤ (Multiset.map (fun gm : ℕ × ℕ => gm.1 * gm.2) r).sum :=
            Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hin
        _ = 0 := hrsum
    omega
  have hlam : s.lam = {(1, s.W)} := by rw [hr, hr0]; rfl
  -- (G1): both flanks are compositions of a zero span, hence empty.
  have hlf : s.lflank = [] := by
    have hs0lf : s.lflank.sum = 0 := by rw [hG1lsum, hs0]
    rcases hl : s.lflank with _ | ⟨x, xs⟩
    · rfl
    · exfalso
      have hx : 1 ≤ x := hG1lpos x (by rw [hl]; simp)
      rw [hl, List.sum_cons] at hs0lf
      omega
  have hwraw : s.wraw = s.W := by simp only [Species.wraw, he_eq, hell_eq, one_mul]
  have hrf : s.rflank = [] := by
    have hs0rf : s.rflank.sum = 0 := by rw [hwraw, hs0] at hG1sum; omega
    rcases hl : s.rflank with _ | ⟨x, xs⟩
    · rfl
    · exfalso
      have hx : 1 ≤ x := hG1r x (by rw [hl]; simp)
      rw [hl, List.sum_cons] at hs0rf
      omega
  -- (G3): the slot set collapses to {0,…,W}.
  have hslots : s.slots = Finset.Icc 0 s.W := by
    rw [hG3slot, ha, hell_eq, zero_add]
  exact ⟨he_eq, hell_eq, ha, hs0, hlam, hlf, hrf, hslots⟩

end LeanUrat.MovesSp
