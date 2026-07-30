/-
Unit U2  (MovesR base layer)
moves_ref: "nested base changes then compose LITERALLY as subrings" (subfield half).
deps: Defs (U1). difficulty: medium.
sketch: x ^ p^d = x ∧ d ∣ m ⇒ x ^ p^m = x (iterate the d-th Frobenius m/d times;
`iterateFrobenius_add`/`pow_pow` bookkeeping).
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- If `x ^ a = x` in a monoid, then `x ^ (a ^ k) = x` for every `k` (iterate the
    relation `k` times: `x ^ a ^ (k+1) = (x ^ a ^ k) ^ a = x ^ a = x`). -/
private lemma pow_pow_eq_self {M : Type*} [Monoid M] {x : M} {a : ℕ} (hx : x ^ a = x) :
    ∀ k : ℕ, x ^ (a ^ k) = x
  | 0 => by rw [pow_zero, pow_one]
  | k + 1 => by rw [pow_succ, pow_mul, pow_pow_eq_self hx k, hx]

/-- U2: `F_d ≤ F_m` for `d ∣ m` — the subfield-lattice nesting. -/
theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m := by
  obtain ⟨k, hk⟩ := h
  subst hk
  intro x hx
  simp only [Fsub, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply] at hx ⊢
  rw [PNat.mul_coe, pow_mul]
  exact pow_pow_eq_self hx (k : ℕ)

end MovesRBase
