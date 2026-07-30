/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# IB-A10 — (†3a) the ℕ-level base-p digit-sum identity

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.2 (†3,
composite (a)) / §4 group A (IB-A10).

INFORMAL STATEMENT: for v < p^N, summing the base-p digits back up recovers v:
`Σ_{k<N} ((v / p^k) % p) · p^k = v` — the finite positional system, stated
`Nat.digits`-free via div/mod exactly as the blueprint prescribes ("the two
composites reduce to (a) …").  This is the arithmetic core of IB-A11's
`boxEquivD` (†3) and of the `boxeq_digits` law (†3b), which is composite (a)
read in `ZMod (p^N)`.

DEPS: — (leaf unit; consumed by IB-A11).

PROOF SKETCH (blueprint: "strong induction on N or `Nat.sub_mod_eq_zero`-style
telescoping; Mathlib `Nat.sum_range_succ` + `Nat.div_add_mod`"): induction on N
generalizing v.  N = 0: v < 1 forces v = 0, empty sum.  N+1: split off the k = 0
term with `Finset.sum_range_succ'` (v % p), rewrite the shifted summand via
`pow_succ` + `Nat.div_div_eq_div_mul` to p · (digit k of v/p), pull the factor
out (`Finset.mul_sum`), apply the IH at v/p (v/p < p^N from v < p^{N+1};
the p = 0 case is vacuous at N+1 since v < 0^{N+1} = 0), and close with
`Nat.mod_add_div` (v % p + p·(v/p) = v).

TRANSCRIPTION RESOLUTIONS (recorded): (i) "Σ_{k<N}" is transcribed as
`∑ k ∈ Finset.range N`; (ii) NO primality/positivity hypothesis on p is carried
— the identity is degenerately true at p = 0 (hv is vacuous for N > 0, and
forces v = 0 at N = 0) and at p = 1 (v = 0, all digits 0); IB-A11 applies it at
prime p.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-A10 — (†3a): base-p digit reconstruction below p^N,
    `Σ_{k<N} ((v / p^k) % p) · p^k = v`. -/
theorem digitSum_eq (p N v : ℕ) (hv : v < p ^ N) :
    ∑ k ∈ Finset.range N, ((v / p ^ k) % p) * p ^ k = v := by
  induction N generalizing v with
  | zero =>
    have hv0 : v = 0 := Nat.lt_one_iff.mp (by simpa using hv)
    simp [hv0]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      simp at hv
    · have hv' : v / p < p ^ N := by
        rw [Nat.div_lt_iff_lt_mul hp]
        exact lt_of_lt_of_eq hv (pow_succ p N)
      have hstep : ∀ k, v / p ^ (k + 1) = (v / p) / p ^ k := fun k => by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      calc ∑ k ∈ Finset.range (N + 1), ((v / p ^ k) % p) * p ^ k
          = (∑ k ∈ Finset.range N, ((v / p ^ (k + 1)) % p) * p ^ (k + 1))
              + ((v / p ^ 0) % p) * p ^ 0 := Finset.sum_range_succ' _ N
        _ = (∑ k ∈ Finset.range N, (((v / p) / p ^ k) % p) * p ^ k) * p + v % p := by
            rw [Finset.sum_mul]
            congr 1
            · exact Finset.sum_congr rfl fun k _ => by
                rw [hstep k, pow_succ, ← mul_assoc]
            · simp
        _ = (v / p) * p + v % p := by rw [ih (v / p) hv']
        _ = v := by rw [mul_comm, Nat.div_add_mod]

end LeanUrat.MovesU
