import Mathlib

/-!
# Counting totally split monic cubics over a finite field

A vector `c : Fin 3 → K` encodes the monic cubic `X ^ 3 + c 2 * X ^ 2 + c 1 * X + c 0`, so the
monic cubics over a finite field `K` with `q = Nat.card K` elements form a set of size `q ^ 3`.
This file counts the *totally split* shape `Split3`: three DISTINCT linear factors,
`c = split3Coeff r s t` for pairwise distinct `r, s, t`.

The main result `six_mul_card_split3` is `6 * #{c | Split3 c} + 3 * q ^ 2 = q ^ 3 + 2 * q`, i.e.
there are `q * (q - 1) * (q - 2) / 6 = q.choose 3` such cubics — the subtraction-free form keeps
the statement valid and division-free over every finite field, including characteristics 2 and 3.

The proof does not count ordered triples and divide by six. Instead it exhibits a bijection

  `{c | Split3 c} ≃ {u : Finset K | #u = 3}`,   `c ↦ cubicRoots K c`

whose inverse sends `{r, s, t}` to `split3Coeff r s t`. Both directions rest on two algebraic
facts valid over any field:

* `eval_split3Coeff`: the cubic attached to `split3Coeff r s t` is literally
  `(X - r) * (X - s) * (X - t)`, so `cubicRoots K (split3Coeff r s t) = {r, s, t}`
  (`cubicRoots_split3Coeff`) — this gives surjectivity, and `Finset.card_eq_three` supplies the
  `3`-element subsets;
* `eq_split3Coeff_of_roots` (**root recovery**): if a monic cubic `c` has three distinct roots
  `y, z, w` then `c = split3Coeff y z w`. Two distinct roots force the quotient-quadratic
  relation `split3_two_root_rel`; two such relations force `c 2 = -(y + z + w)`, and back
  substitution gives `c 1` and `c 0`. This gives injectivity: the root set determines `c`.

The count of `3`-element subsets is `Fintype.card_finset_len` (`= q.choose 3`), and the ℕ-level
bookkeeping converting `q.choose 3` to the subtraction-free target is `six_mul_choose_three`,
proved by induction from `two_mul_choose_two_add`.
-/

namespace UniformityCheck

open Finset

/-- The coefficient vector of `(X - r)(X - s)(X - t)`, i.e.
`X³ - (r+s+t) X² + (rs+rt+st) X - rst`. -/
def split3Coeff {K : Type*} [Field K] (r s t : K) : Fin 3 → K :=
  ![-(r * s * t), r * s + r * t + s * t, -(r + s + t)]

/-- The level-0 family "three DISTINCT linear factors". -/
def Split3 {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ r s t : K, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ c = split3Coeff r s t

section Algebra

variable {K : Type*} [Field K] {c : Fin 3 → K}

/-- The monic cubic attached to `split3Coeff r s t` really is `(X - r)(X - s)(X - t)`. -/
theorem eval_split3Coeff (r s t y : K) :
    y ^ 3 + split3Coeff r s t 2 * y ^ 2 + split3Coeff r s t 1 * y + split3Coeff r s t 0
      = (y - r) * (y - s) * (y - t) := by
  simp only [split3Coeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Two distinct roots of a monic cubic satisfy the quotient-quadratic relation. -/
theorem split3_two_root_rel {y z : K} (hyz : y ≠ z)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0) :
    y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1 = 0 := by
  have h : (y - z) * (y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1) = 0 := by
    linear_combination hy - hz
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hyz
  · exact h

/-- **Root recovery.** Three distinct roots determine every coefficient of a monic cubic:
the cubic is forced to be `(X - y)(X - z)(X - w)`. -/
theorem eq_split3Coeff_of_roots {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c = split3Coeff y z w := by
  have hA := split3_two_root_rel hyz hy hz
  have hB := split3_two_root_rel hyw hy hw
  have h2 : c 2 = -(y + z + w) := by
    have h : (z - w) * (y + z + w + c 2) = 0 := by linear_combination hA - hB
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hzw
    · linear_combination h
  have h1 : c 1 = y * z + y * w + z * w := by linear_combination hA - (y + z) * h2
  have h0 : c 0 = -(y * z * w) := by linear_combination hy - y ^ 2 * h2 - y * h1
  funext i
  fin_cases i
  · simpa [split3Coeff] using h0
  · simpa [split3Coeff] using h1
  · simpa [split3Coeff] using h2

end Algebra

section Count

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- The set of roots in `K` of the monic cubic `X³ + c 2 X² + c 1 X + c 0`. -/
def cubicRoots (c : Fin 3 → K) : Finset K :=
  {y | y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0}

variable {K}

@[simp] theorem mem_cubicRoots {c : Fin 3 → K} {y : K} :
    y ∈ cubicRoots K c ↔ y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0 := by
  simp [cubicRoots]

theorem cubicRoots_split3Coeff (r s t : K) : cubicRoots K (split3Coeff r s t) = {r, s, t} := by
  ext y
  simp only [mem_cubicRoots, eval_split3Coeff, mul_eq_zero, sub_eq_zero, Finset.mem_insert,
    Finset.mem_singleton, or_assoc]

/-- The root set is a bijection from totally split monic cubics onto the `3`-element subsets
of `K`: surjective because `{r, s, t}` is the root set of `(X - r)(X - s)(X - t)`, injective
by root recovery (`eq_split3Coeff_of_roots`). -/
theorem card_split3 : Nat.card {c : Fin 3 → K // Split3 c} = (Fintype.card K).choose 3 := by
  have hmaps : ∀ x : {c : Fin 3 → K // Split3 c}, #(cubicRoots K x.1) = 3 := by
    rintro ⟨c, r, s, t, hrs, hrt, hst, rfl⟩
    rw [cubicRoots_split3Coeff]
    exact Finset.card_eq_three.mpr ⟨r, s, t, hrs, hrt, hst, rfl⟩
  have hbij : Function.Bijective (fun x : {c : Fin 3 → K // Split3 c} =>
      (⟨cubicRoots K x.1, hmaps x⟩ : {u : Finset K // #u = 3})) := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ hx
      simp only [Subtype.mk.injEq] at hx
      obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := hc
      rw [cubicRoots_split3Coeff] at hx
      have hr : r ∈ cubicRoots K c' := by rw [← hx]; simp
      have hs : s ∈ cubicRoots K c' := by rw [← hx]; simp
      have ht : t ∈ cubicRoots K c' := by rw [← hx]; simp
      rw [mem_cubicRoots] at hr hs ht
      exact Subtype.ext (eq_split3Coeff_of_roots hrs hrt hst hr hs ht).symm
    · rintro ⟨u, hu⟩
      obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := Finset.card_eq_three.mp hu
      exact ⟨⟨split3Coeff r s t, ⟨r, s, t, hrs, hrt, hst, rfl⟩⟩,
        Subtype.ext (cubicRoots_split3Coeff r s t)⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_finset_len]

end Count

theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (n + 1).choose 2 = n + n.choose 2 := by rw [Nat.choose_succ_succ]; simp
    rw [h2]
    zify at ih ⊢
    linear_combination ih

theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 + 3 * n ^ 2 = n ^ 3 + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by rw [Nat.choose_succ_succ]
    have h2 := two_mul_choose_two_add n
    rw [h3]
    zify at ih h2 ⊢
    linear_combination ih + 3 * h2

/-- **#{monic cubics with three distinct roots in `K`} = q(q-1)(q-2)/6**, subtraction-free. -/
theorem six_mul_card_split3 (K : Type*) [Field K] [Finite K] :
    6 * Nat.card {c : Fin 3 → K // Split3 c} + 3 * Nat.card K ^ 2
      = Nat.card K ^ 3 + 2 * Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [card_split3, Nat.card_eq_fintype_card]
  exact six_mul_choose_three _

/-! ### Numeric sanity checks

Brute-force enumeration over `ZMod q` for `q = 2, 3, 5` (run 2026-08-13): `#{c | Split3 c}` is
`0, 1, 10`, matching `q.choose 3 = 0, 1, 10` and the theorem
`6 * 0 + 3 * 2 ^ 2 = 12 = 2 ^ 3 + 2 * 2`, `6 * 1 + 3 * 3 ^ 2 = 33 = 3 ^ 3 + 2 * 3`,
`6 * 10 + 3 * 5 ^ 2 = 135 = 5 ^ 3 + 2 * 5`. The `#guard_msgs` wrappers make these checks
build-time assertions rather than comments. -/
section Numeric

/-- `Split3` is decidable over a finite field: the existential ranges over `K ^ 3`. -/
local instance {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    DecidablePred (Split3 : (Fin 3 → K) → Prop) := fun c =>
  decidable_of_iff (∃ r s t : K, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ c = split3Coeff r s t) Iff.rfl

/-- info: 0 -/
#guard_msgs in
#eval #{c : Fin 3 → ZMod 2 | Split3 c}

/-- info: 1 -/
#guard_msgs in
#eval #{c : Fin 3 → ZMod 3 | Split3 c}

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- info: 10 -/
#guard_msgs in
#eval #{c : Fin 3 → ZMod 5 | Split3 c}

end Numeric

#print axioms UniformityCheck.six_mul_card_split3

end UniformityCheck
