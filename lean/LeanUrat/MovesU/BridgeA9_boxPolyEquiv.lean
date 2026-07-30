/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.OM.QuotientBox

/-!
# IB-A9 — (†2) `boxPolyEquiv : Box p n N ≃ monicBox p N n` at positive levels

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.2 (†2) /
§4 group A (IB-A9, pre-approved split A9a/A9b).

INFORMAL STATEMENT: for 0 < N the coefficient box `Box p n N = Fin n → ZMod (p^N)`
IS the monic degree-n polynomial box `QuotientBox.monicBox p N n`, via
`f ↦ Box.toPoly f = X^n + Σ_i C (f i) X^i` forward and coefficient read
`g ↦ fun i => g.coeff i` backward.  AT N = 0 THE EQUIV IS FALSE (IB-A8,
`BridgeA8_level0Edge.lean`: the monic box is empty, the coefficient box a
singleton) — hence the `0 < N` guard, the same guard discipline as
`TreePin.chart` (round-3 CRITICAL 1).

DEPS: IB-A8 (edge documentation only — no import-level dependency on its
statements).

PROOF SKETCH (blueprint §3.2):
* A9a `boxToPoly_mem_monicBox`: nontriviality of `ZMod (p^N)` from p prime,
  N ≥ 1 (`Fact (1 < p ^ N)` via `Nat.one_lt_pow`); the sum `Σ_i C (f i) X^i` has
  degree < n (each summand degree ≤ i < n), so `(monic_X_pow n).add_of_left` +
  `degree_add_eq_left_of_degree_lt` give Monic and natDegree = n — replay
  `OM.QuotientBox.card_monicBox`'s `hdeg` block (QuotientBox.lean:44–51) at the
  explicit-sum presentation.
* A9b `left_inv`: coefficient extraction — for i < n,
  `(Box.toPoly f).coeff i = f i` (`coeff_X_pow` kills the X^n head at i ≠ n;
  `Polynomial.finset_sum_coeff` + `coeff_C_mul` + `coeff_X_pow` isolate the i-th
  summand).
* A9b `right_inv`: for g monic of natDegree n, `X^n + Σ_i C (g.coeff i) X^i = g`
  by `Polynomial.ext`: above n both sides vanish (`coeff_eq_zero_of_natDegree_lt`),
  at n the head reads `g.Monic.leadingCoeff`, below n the sum reproduces
  `g.coeff i`.

TRANSCRIPTION RESOLUTIONS (recorded): (i) the forward and backward maps are
PINNED IN THE DEFINITION (toFun := `Box.toPoly`, invFun := coefficient read) so
the (†2) spec "f ↦ Box.toPoly f" survives the skeleton — only the side proofs
and the two inverse laws are sorried; (ii) A9a is packaged as ONE conjunctive
lemma `boxToPoly_mem_monicBox` ("toPoly lands in monicBox"), exactly the
subtype witness the record literal consumes; (iii) `[Fact p.Prime]` is carried
(nontriviality of `ZMod (p^N)` needs p^N > 1; it also serves `monicBox`'s
section context).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- IB-A9a — `Box.toPoly` lands in the monic degree-n box at positive levels:
    `X^n + Σ_i C (f i) X^i` is monic of natDegree n over the (nontrivial for
    0 < N, p prime) ring `ZMod (p^N)`. -/
theorem boxToPoly_mem_monicBox (p n N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : Box p n N) :
    (Box.toPoly f).Monic ∧ (Box.toPoly f).natDegree = n := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' (Fact.out : p.Prime).one_lt⟩
  have hdlt : (∑ i : Fin n, C (f i) * X ^ (i : ℕ)).degree
      < (X ^ n : (ZMod (p ^ N))[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i _ => ?_
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr i.isLt)
  constructor
  · exact (monic_X_pow n).add_of_left hdlt
  · exact natDegree_eq_of_degree_eq_some
      ((degree_add_eq_left_of_degree_lt hdlt).trans (degree_X_pow n))

/-- Proof-layer helper for the two inverse laws (guard-free): below the head,
    the polynomial read's coefficients are the box coordinates —
    `(Box.toPoly f).coeff i = f i` for `i < n`. -/
theorem boxToPoly_coeff_lt (p n N : ℕ) (f : Box p n N) (i : Fin n) :
    (Box.toPoly f).coeff (i : ℕ) = f i := by
  simp only [Box.toPoly, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt),
    finsetSum_coeff, coeff_C_mul, mul_ite, mul_one, mul_zero, zero_add,
    Fin.val_eq_val, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- IB-A9b — (†2) THE LEVEL-N DICTIONARY: the coefficient box IS the monic
    polynomial box, `f ↦ Box.toPoly f` forward, coefficient read backward.
    Guarded to 0 < N (IB-A8: FALSE at N = 0). -/
noncomputable def boxPolyEquiv (p n N : ℕ) [Fact p.Prime] (hN : 0 < N) :
    Box p n N ≃ OM.QuotientBox.monicBox p N n where
  toFun f := ⟨Box.toPoly f, boxToPoly_mem_monicBox p n N hN f⟩
  invFun g := fun i => g.1.coeff (i : ℕ)
  left_inv := fun f => funext fun i => boxToPoly_coeff_lt p n N f i
  right_inv := fun g => Subtype.ext (by
    change Box.toPoly (fun i : Fin n => g.1.coeff (i : ℕ)) = g.1
    have hmb := boxToPoly_mem_monicBox p n N hN (fun i : Fin n => g.1.coeff (i : ℕ))
    ext k
    rcases lt_trichotomy k n with hk | hk | hk
    · exact boxToPoly_coeff_lt p n N _ ⟨k, hk⟩
    · rw [hk]
      have h1 : (Box.toPoly fun i : Fin n => g.1.coeff (i : ℕ)).coeff n = 1 := by
        have h := hmb.1.coeff_natDegree
        rwa [hmb.2] at h
      have h2 : g.1.coeff n = 1 := by
        have h := g.2.1.coeff_natDegree
        rwa [g.2.2] at h
      rw [h1, h2]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hmb.2]; exact hk),
          coeff_eq_zero_of_natDegree_lt (by rw [g.2.2]; exact hk)])

end LeanUrat.MovesU
