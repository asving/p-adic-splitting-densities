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

/-- The splitting types of degree n form a Fintype: entries are bounded by n and the
    multiset has card ≤ n (each entry contributes ≥ 1 to the sum). P-phase target. -/
noncomputable instance instSplittingTypeFintype (n : ℕ) : Fintype (SplittingType n) :=
  sorry

/-- Nonemptiness for n ≥ 1: the totally ramified type {(n, 1)} witnesses. -/
theorem splittingType_nonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (SplittingType n) :=
  sorry

end LeanUrat.MovesU
