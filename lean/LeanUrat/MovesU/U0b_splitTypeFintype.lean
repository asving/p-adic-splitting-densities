/-
Unit U0b.splitTypeFintype  (MovesU campaign)  [support]
moves_ref: "For each splitting type σ of degree n (a multiset of pairs (e_i, f_i)
           with Σ e_i·f_i = n)" (SQ.4)
deps: Defs ONLY; imported BY DefsLedger — the gap-7 circularity fix (D11).
sketch: entries (e,f) have e·f ≤ n so e,f ≤ n and card σ ≤ n: embed into the
        multisets over (Finset.range (n+1) ×ˢ Finset.range (n+1)) of card ≤ n
        (`Multiset`-bounded / `Set.Finite.fintype` route, classical OK); nonempty
        via ⟨{(n,1)}⟩. Needed by every `∑ σ` (rs4_checksum, (BOX-N), U10).
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesU.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- `SplittingType n` is a subtype of `Multiset (ℕ × ℕ)`, so equality is decidable
    (the E-phase DecidableEq obligation — needed by U9's `Finset.univ.erase σ`). -/
instance instSplittingTypeDecEq (n : ℕ) : DecidableEq (SplittingType n) :=
  inferInstanceAs (DecidableEq {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n})

/-- Every entry `(e, f)` of a degree-`n` splitting type has both coordinates ≤ n:
    each entry contributes a product `e·f ≥ 1` to the sum `= n`, so `e·f ≤ n`, and
    `e ≤ e·f`, `f ≤ e·f` (both coordinates ≥ 1). -/
private theorem splittingType_entry_le {n : ℕ} (σ : SplittingType n) {x : ℕ × ℕ}
    (hx : x ∈ σ.1) : x.1 ≤ n ∧ x.2 ≤ n := by
  obtain ⟨h1, h2⟩ := σ.2.1 x hx
  have hmem : x.1 * x.2 ∈ σ.1.map (fun x => x.1 * x.2) := Multiset.mem_map.2 ⟨x, hx, rfl⟩
  have hle : x.1 * x.2 ≤ n := by
    have := Multiset.le_sum_of_mem hmem
    rwa [σ.2.2] at this
  exact ⟨le_trans (le_mul_of_one_le_right (Nat.zero_le _) h2) hle,
         le_trans (le_mul_of_one_le_left (Nat.zero_le _) h1) hle⟩

/-- A degree-`n` splitting type has at most `n` entries: each entry contributes a
    product `≥ 1` to the sum `= n`. -/
private theorem splittingType_card_le {n : ℕ} (σ : SplittingType n) :
    Multiset.card σ.1 ≤ n := by
  have hmap : ∀ y ∈ σ.1.map (fun x => x.1 * x.2), 1 ≤ y := by
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := σ.2.1 x hx
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hcard := Multiset.card_nsmul_le_sum hmap
  simp only [Multiset.card_map, σ.2.2, nsmul_eq_mul, mul_one] at hcard
  exact hcard

/-- The splitting types of degree n form a Fintype: entries are bounded by n and the
    multiset has card ≤ n (each entry contributes ≥ 1 to the sum). P-phase target.
    Injects into the count-vectors `{x ∈ range(n+1)²} → Fin (n+1)`: every entry lies
    in `range(n+1)²` (`splittingType_entry_le`) and every count is ≤ card ≤ n
    (`splittingType_card_le`), and a multiset with support in a finite set is determined
    by its counts there. -/
noncomputable instance instSplittingTypeFintype (n : ℕ) : Fintype (SplittingType n) := by
  classical
  refine Fintype.ofInjective
    (fun (σ : SplittingType n)
        (t : {x : ℕ × ℕ // x ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1)}) =>
      (⟨Multiset.count t.1 σ.1, by
        have := le_trans (Multiset.count_le_card t.1 σ.1) (splittingType_card_le σ)
        omega⟩ : Fin (n + 1))) ?_
  intro σ σ' h
  apply Subtype.ext
  refine Multiset.ext.mpr fun a => ?_
  by_cases ha : a ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1)
  · have hval := congrFun h ⟨a, ha⟩
    exact congrArg Fin.val hval
  · have hn1 : a ∉ σ.1 := by
      intro hmem
      obtain ⟨hb1, hb2⟩ := splittingType_entry_le σ hmem
      exact ha (by simp only [Finset.mem_product, Finset.mem_range]; omega)
    have hn2 : a ∉ σ'.1 := by
      intro hmem
      obtain ⟨hb1, hb2⟩ := splittingType_entry_le σ' hmem
      exact ha (by simp only [Finset.mem_product, Finset.mem_range]; omega)
    rw [Multiset.count_eq_zero.2 hn1, Multiset.count_eq_zero.2 hn2]

/-- Nonemptiness for n ≥ 1: the totally ramified type {(n, 1)} witnesses. -/
theorem splittingType_nonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (SplittingType n) :=
  ⟨⟨{(n, 1)},
    fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; exact ⟨hn, le_refl 1⟩,
    by simp⟩⟩

end LeanUrat.MovesU
