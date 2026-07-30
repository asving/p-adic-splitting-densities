/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger
import LeanUrat.MovesU.BridgeA10_digitSum

/-!
# IB-A11 — (†3) `boxEquivD : Box p n N ≃ MovesD.Box p (n·N)` + the (†3b) digit law

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.2 (†3)/(†3b)
/ §4 group A (IB-A11, pre-approved split A11a equiv / A11b law).

INFORMAL STATEMENT: for 0 < N the level-N coefficient box `Box p n N` IS the
MovesT/MovesD digit box `MovesD.Box p (n·N)` by base-p digits, laid out through
`digitIdx n N i k = ⟨i·N + k, _⟩` (DefsLedger.lean:289): the (i,k) slot carries
the k-th base-p digit of `(f i).val`.  Forward `boxToDigits`: slot j reads digit
(j % N) of coefficient (j / N).  Inverse `digitsToBox`:
`f i := Σ_k (d (digitIdx i k)) · p^k` in `ZMod (p^N)`.  LAW (†3b)
`boxEquivD_digits`: `f i = Σ_k ((boxEquivD N f (digitIdx n N i k)).val : ZMod (p^N)) · p^k`
— EXACTLY the `TreePin.boxeq_digits` field shape (DefsLedger.lean:351–354) at
`boxeq := boxEquivD`, i.e. composite (a) = IB-A10 read in `ZMod (p^N)`
("`push_cast` after the ℕ-level identity").

DEPS: IB-A10 (`digitSum_eq`, the ℕ-level core).

PROOF SKETCH (blueprint §3.2):
* `left_inv` (digitsToBox ∘ boxToDigits = id): funext i; the slot reads are
  digits of v := (f i).val — at j = digitIdx n N i k the index arithmetic gives
  j / N = i (`Nat.mul_add_div`, k < N) and j % N = k (`Nat.mul_add_mod`); the
  `(· : ZMod p).val` round-trip is the digit itself (`ZMod.val_natCast` +
  `Nat.mod_eq_of_lt`, digit < p); then IB-A10's `digitSum_eq` at v < p^N
  (`ZMod.val_lt`, `NeZero (p^N)` from p prime) and `ZMod.natCast_val`/
  `ZMod.val_cast_of_lt` close `(Σ digits : ZMod (p^N)) = f i` after `push_cast`.
* `right_inv` (boxToDigits ∘ digitsToBox = id): funext j; write j = i·N + k;
  the ℕ-value of `digitsToBox d i` is the digit sum Σ_k (d _).val · p^k < p^N
  (each (d _).val < p), so its `ZMod.val` is that sum, and digit EXTRACTION of a
  digit sum returns the (j % N)-th digit (div/mod telescoping — the (b)
  composite of (†3); split the sum below/at/above k with `Finset.sum_range` +
  `Nat.add_mul_div_left`/`Nat.add_mul_mod_self_left`).
* `boxEquivD_digits`: pointwise restatement of `left_inv` at i — `congrFun`
  the inverse law; the RHS IS `digitsToBox (boxToDigits f) i` definitionally.

TRANSCRIPTION RESOLUTIONS (recorded): (i) the forward/inverse maps are PINNED
IN THE DEFINITION (standalone defs `boxToDigits`/`digitsToBox`, wired as
toFun/invFun) so (†3)'s layout spec survives the skeleton — only the inverse
laws + the (†3b) law are sorried; (ii) `[Fact p.Prime]` is carried on all
declarations (matching `TreePin`'s section context; mathematically only 0 < p
is load-bearing — the equiv is FALSE at p = 0); (iii) the (†3b) statement
carries the same `0 < N` guard as the equiv it reads (the `TreePin.boxeq_digits`
field quantifies over all N over an ALL-N `boxeq` family; IB-D18's assembly
supplies the N = 0 leg from `box0_unique`-side triviality, outside this unit's
scope).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-A11 forward map — (†3)'s digit read: slot j of the digit box carries the
    (j % N)-th base-p digit of coefficient (j / N). -/
noncomputable def boxToDigits (p n N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : Box p n N) : MovesD.Box p (n * N) :=
  fun j =>
    ((((f ⟨(j : ℕ) / N, (Nat.div_lt_iff_lt_mul hN).mpr j.isLt⟩).val
        / p ^ ((j : ℕ) % N)) % p : ℕ) : ZMod p)

/-- IB-A11 inverse map — (†3)'s reconstruction:
    `f i := Σ_k (d (digitIdx i k)) · p^k` in `ZMod (p^N)`. -/
noncomputable def digitsToBox (p n N : ℕ) [Fact p.Prime]
    (d : MovesD.Box p (n * N)) : Box p n N :=
  fun i => ∑ k : Fin N,
    ((d (digitIdx n N i k)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (k : ℕ)

/-- Proof-layer helper (consumed by IB-A12's (†3c) as well): the forward read at
    the (i,k) `digitIdx` slot IS the k-th base-p digit of coefficient i —
    the index arithmetic `(i·N + k)/N = i`, `(i·N + k)%N = k` made explicit. -/
theorem boxToDigits_digitIdx (p n N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : Box p n N) (i : Fin n) (k : Fin N) :
    boxToDigits p n N hN f (digitIdx n N i k)
      = ((((f i).val / p ^ (k : ℕ)) % p : ℕ) : ZMod p) := by
  have hdiv : ((digitIdx n N i k : ℕ)) / N = (i : ℕ) := by
    change ((i : ℕ) * N + (k : ℕ)) / N = (i : ℕ)
    rw [mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt k.isLt, add_zero]
  have hmod : ((digitIdx n N i k : ℕ)) % N = (k : ℕ) := by
    change ((i : ℕ) * N + (k : ℕ)) % N = (k : ℕ)
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
  have harg : (⟨(digitIdx n N i k : ℕ) / N,
      (Nat.div_lt_iff_lt_mul hN).mpr (digitIdx n N i k).isLt⟩ : Fin n) = i :=
    Fin.ext hdiv
  unfold boxToDigits
  rw [hmod, harg]

/-- Proof-layer helper: the (†3) left-inverse law — reconstruction after digit
    read is the identity (composite (a), IB-A10, read in `ZMod (p^N)`). -/
theorem digitsToBox_boxToDigits (p n N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : Box p n N) : digitsToBox p n N (boxToDigits p n N hN f) = f := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  funext i
  have hv : (f i).val < p ^ N := ZMod.val_lt _
  have hterm : ∀ k : Fin N,
      (((boxToDigits p n N hN f (digitIdx n N i k)).val : ℕ) : ZMod (p ^ N))
          * (p : ZMod (p ^ N)) ^ (k : ℕ)
        = ((((f i).val / p ^ (k : ℕ) % p) * p ^ (k : ℕ) : ℕ) : ZMod (p ^ N)) := by
    intro k
    rw [boxToDigits_digitIdx p n N hN f i k, ZMod.val_natCast,
        Nat.mod_mod_of_dvd _ dvd_rfl]
    push_cast
    ring
  calc digitsToBox p n N (boxToDigits p n N hN f) i
      = ∑ k : Fin N, ((((f i).val / p ^ (k : ℕ) % p) * p ^ (k : ℕ) : ℕ) : ZMod (p ^ N)) :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = (((f i).val : ℕ) : ZMod (p ^ N)) := by
        rw [Fin.sum_univ_eq_sum_range
              (fun k => ((((f i).val / p ^ k % p) * p ^ k : ℕ) : ZMod (p ^ N))) N,
            ← Nat.cast_sum, digitSum_eq p N (f i).val hv]
    _ = f i := by simp [ZMod.natCast_val, ZMod.cast_id]

/-- IB-A11a — (†3) THE DIGIT DICTIONARY: the level-N coefficient box IS the
    MovesD digit box at m = n·N, by base-p digits through the `digitIdx` layout.
    Guarded to 0 < N (same discipline as (†2)/`TreePin.chart`). -/
noncomputable def boxEquivD (p n N : ℕ) [Fact p.Prime] (hN : 0 < N) :
    Box p n N ≃ MovesD.Box p (n * N) where
  toFun := boxToDigits p n N hN
  invFun := digitsToBox p n N
  left_inv := digitsToBox_boxToDigits p n N hN
  right_inv := by
    intro d
    have hp : p.Prime := Fact.out
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
    have hcard : Fintype.card (Box p n N) = Fintype.card (MovesD.Box p (n * N)) := by
      rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card,
          Fintype.card_fin, Fintype.card_fin, ← pow_mul, Nat.mul_comm N n]
    have hbij : Function.Bijective (boxToDigits p n N hN) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Function.LeftInverse.injective (digitsToBox_boxToDigits p n N hN), hcard⟩
    obtain ⟨f, rfl⟩ := hbij.surjective d
    rw [digitsToBox_boxToDigits p n N hN f]

/-- IB-A11b — LAW (†3b), the `TreePin.boxeq_digits` field shape at
    `boxeq := boxEquivD`: every coefficient is the base-p digit sum of its own
    slot reads — composite (a) (IB-A10) read in `ZMod (p^N)`. -/
theorem boxEquivD_digits (p n N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (f : Box p n N) (i : Fin n) :
    f i = ∑ k : Fin N,
      ((boxEquivD p n N hN f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ) :=
  (congrFun (digitsToBox_boxToDigits p n N hN f) i).symm

end LeanUrat.MovesU
