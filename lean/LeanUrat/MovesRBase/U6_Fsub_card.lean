/-
Unit U6  (MovesR base layer)  [Fsub_card; blueprint R6, FINDING-1 REPAIR]
moves_ref: "F_m is THE subfield of order p^m" — the CARD FACT half of the display.
deps: Defs (U1). difficulty: hard (wave-3 fleet).
sketch: `Fsub p m` is the root set of the separable polynomial `X^{p^m} − X` in the
algebraically closed `Kbar p`: `galois_poly_separable` + root counting (splits with
`p^m` distinct roots); membership `x ^ p ^ m = x` is definitional in `Fsub`.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U6: `|F_m| = p^m` — the order fact making `Fsub p m` THE subfield of order
`p^m` (blueprint D1, finding-1 repair: the card fact is part of the display). -/
theorem Fsub_card (m : ℕ+) : Nat.card ↥(Fsub p m) = p ^ (m : ℕ) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hm0 : (m : ℕ) ≠ 0 := m.pos.ne'
  have hq1 : 1 < p ^ (m : ℕ) := Nat.one_lt_pow hm0 hp1
  set P : (Kbar p)[X] := X ^ (p ^ (m : ℕ)) - X with hP
  have hPne : P ≠ 0 := hP ▸ FiniteField.X_pow_card_sub_X_ne_zero (Kbar p) hq1
  have hdeg : P.natDegree = p ^ (m : ℕ) :=
    hP ▸ FiniteField.X_pow_card_sub_X_natDegree_eq (Kbar p) hq1
  have hchar : ((p ^ (m : ℕ) : ℕ) : Kbar p) = 0 := by
    push_cast
    rw [CharP.cast_eq_zero (Kbar p) p, zero_pow hm0]
  have hderiv : Polynomial.derivative P = -1 := by
    rw [hP, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X,
      hchar, map_zero, zero_mul, zero_sub]
  have hsep : P.Separable := by
    rw [Polynomial.separable_def, hderiv]
    exact isCoprime_one_right.neg_right
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcardroots : Multiset.card P.roots = p ^ (m : ℕ) := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, hdeg]
  have hnodup : P.roots.Nodup := Polynomial.nodup_roots hsep
  have hset : (Fsub p m : Set (Kbar p)) = (P.roots.toFinset : Set (Kbar p)) := by
    ext x
    simp only [SetLike.mem_coe, Fsub, RingHom.mem_eqLocusField, RingHom.id_apply,
      iterateFrobenius_def, Multiset.mem_toFinset,
      Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
    rw [hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  calc Nat.card ↥(Fsub p m)
      = Nat.card ↥((Fsub p m : Set (Kbar p))) := by rw [SetLike.coe_sort_coe]
    _ = (Fsub p m : Set (Kbar p)).ncard := Nat.card_coe_set_eq _
    _ = (P.roots.toFinset : Set (Kbar p)).ncard := by rw [hset]
    _ = P.roots.toFinset.card := Set.ncard_coe_finset _
    _ = Multiset.card P.roots := Multiset.toFinset_card_of_nodup hnodup
    _ = p ^ (m : ℕ) := hcardroots

end MovesRBase
