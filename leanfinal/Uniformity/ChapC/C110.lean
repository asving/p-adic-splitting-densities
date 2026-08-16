/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C110 — Step 2: transfer at one repeated linear root

**Chapter C, NODE C.110** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1; split → 2]`.

Clause 1 of the split, landed here:

* `ht_conservative_card` — the conservative cell `C_a(k) = {(b_j) : v(b_j) ≥ (a−j)k + 1}` has
  `#C_a(k) = Q ^ D_u(N)` at general block degree `d`, where `Q = q ^ d`; the `d·Σ` shape of the
  exponent IS that `Q = q ^ d` clearing.

## What the statement says, term by term

The counted objects are level-`N` coefficient classes `c : Coeff O (a·d) N`
(`Coeff O n N = Fin n → O ⧸ 𝔪 ^ N`, landed in `Uniformity/Density/LocalData.lean`) that admit
an integral lift `b : Fin (a·d) → O` whose `i`-th entry has valuation at least
`(a − i/d)·k + 1`.  The index arithmetic `i / d` is the BLOCK read: the `a·d` scalar
coordinates are grouped into `a` consecutive blocks of length `d`, block `j` being the
coefficient vector of the degree-`< d` development coefficient `b_j`, and the conservative
bound is constant on a block.  So the constraint really is `v(b_j) ≥ (a − j)k + 1` for
`j < a`, stated coordinatewise.

The count is `q ^ (d · ∑_{j<a} (N − ((a−j)k + 1)))`.  Two disciplines are visible in that
exponent and both are load-bearing:

* the summand `N − ((a−j)k + 1)` is **ℕ-subtraction**, i.e. the C.53 CLIP `max(·, 0)`: when the
  conservative bound `(a−j)k + 1` lies at or beyond the window `N`, that block contributes the
  single zero class, not a negative exponent.  This is exactly the "including when conservative
  bounds lie beyond the window" clause of the STATEMENT, and it is where `card_res_ge` splits
  into its two cases;
* the leading `d ·` is the block clearing `Q = q ^ d`: each of the `a` blocks carries `d` scalar
  coordinates subject to the same bound.

## Proof route (the three moves)

1. **The lift is coordinatewise.**  `∃ b, proj b = c ∧ ∀ i, bound i ≤ v(b i)` is equivalent to
   `∀ i, ∃ x, mk x = c i ∧ bound i ≤ v(x)` — one direction reads off `congrFun`, the other
   chooses a lift per coordinate.  So the counted subtype is a Π of one-coordinate subtypes
   (`Equiv.subtypePiEquivPi`), and `Nat.card_pi` turns the count into a product.
2. **One coordinate: `#{r : O ⧸ 𝔪 ^ N | r has a lift of valuation ≥ m} = q ^ (N − m)`**
   (`card_res_ge`).  For `m ≤ N` the set is the range of `x ↦ [x·π ^ m]`, an additive map with
   kernel `𝔪 ^ (N−m)`, so the count is `#(O ⧸ 𝔪 ^ (N−m)) = q ^ (N−m)` by `card_res`.  For
   `N ≤ m` every such class is `0` and the count is `1 = q ^ 0` — the clip.
3. **Regrouping.**  `∑_{i < a·d} g(i / d) = d · ∑_{j < a} g j` (`sum_range_mul_div`), by
   induction on `a` with `Nat.mul_add_div`.

Nothing in clause 1 needs `π` beyond `Irreducible π`, and nothing needs completeness or a key:
it is pure valuation bookkeeping in the coefficient box.

**DEPENDS.** C.108 (the `D_v` quantity whose value this is) · landed `card_coeff`/`card_res`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.84` step 2 (verbatim).

**TEETH.** the certificate's 300 translation-rank tests → retained; §13 fires one translate at
each prime.

**ENVIRONMENT.** ENV-C3.

## Status

Clause 1 (`ht_conservative_card`) is sorry-free, axiom-free (Lean core only).
Clause 2 (`ht_transfer_residual_iff`) is NOT in this file — see the node's status record.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Valuation bookkeeping in one coordinate -/

private theorem le_addVal_iff_pow_dvd (hπ : Irreducible π) (m : ℕ) (x : O) :
    ((m : ℕ) : ℕ∞) ≤ addVal O x ↔ π ^ m ∣ x := by
  rw [← hπ.addVal_pow m]
  exact addVal_le_iff_dvd

private theorem mem_pow_maximalIdeal_iff (hπ : Irreducible π) (m : ℕ) (x : O) :
    x ∈ (IsLocalRing.maximalIdeal O) ^ m ↔ π ^ m ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

section Counting

variable [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
/-- The level-`N` classes with a lift of valuation `≥ m`, when `N ≤ m`: only the zero class.
This is the CLIP branch — the conservative bound lies at or beyond the window. -/
private theorem card_res_ge_of_le (hπ : Irreducible π) {N m : ℕ} (h : N ≤ m) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  have hzero : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r = 0 := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_maximalIdeal_iff hπ]
      exact dvd_trans (pow_dvd_pow _ h) ((le_addVal_iff_pow_dvd hπ m x).1 hx)
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  have hone : Nat.card {r : Res O N // r = 0} = 1 := by simp
  rw [Nat.sub_eq_zero_of_le h, pow_zero, ← hone]
  exact Nat.card_congr (Equiv.subtypeEquivRight hzero)

/-- The level-`N` classes with a lift of valuation `≥ m`, when `m ≤ N`: `q ^ (N − m)` of them —
the range of the additive map `x ↦ [x·π ^ m]`, whose kernel is `𝔪 ^ (N−m)`. -/
private theorem card_res_ge_of_ge (hπ : Irreducible π) {N m : ℕ} (h : m ≤ N) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  classical
  set μ : O →+ Res O N :=
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)).toAddMonoidHom.comp
      (AddMonoidHom.mulRight (π ^ m)) with hμ
  have hμ_apply : ∀ x : O, μ x = Ideal.Quotient.mk _ (x * π ^ m) := fun _ => rfl
  have hrange : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r ∈ Set.range μ := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      obtain ⟨y, rfl⟩ := (le_addVal_iff_pow_dvd hπ m x).1 hx
      exact ⟨y, by rw [hμ_apply]; ring_nf⟩
    · rintro ⟨y, rfl⟩
      refine ⟨y * π ^ m, rfl, ?_⟩
      exact (le_addVal_iff_pow_dvd hπ m _).2 ⟨y, by ring⟩
  have hker : μ.ker = ((IsLocalRing.maximalIdeal O) ^ (N - m)).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, hμ_apply, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_toAddSubgroup]
    rw [mem_pow_maximalIdeal_iff hπ, mem_pow_maximalIdeal_iff hπ]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hid : π ^ (N - m) * c * π ^ m = π ^ N * c := by
        rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]
      have hsplit : x * π ^ m = (π ^ (N - m) * c) * π ^ m := by rw [hid]; exact hc
      exact mul_right_cancel₀ (pow_ne_zero m hπ.ne_zero) hsplit
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]⟩
  have hcard : Nat.card (Set.range μ) = Nat.card (O ⧸ μ.ker) :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange μ).toEquiv).symm
  have hq : Nat.card (O ⧸ μ.ker) = residueCard O ^ (N - m) := by
    rw [hker]
    exact card_res (O := O) (N - m)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hrange), hcard, hq]

/-- **One coordinate, both branches.**  `#{r : O ⧸ 𝔪 ^ N | r lifts to valuation ≥ m}
= q ^ (N − m)`, the subtraction being the ℕ-clip. -/
private theorem card_res_ge (hπ : Irreducible π) (N m : ℕ) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  rcases le_total m N with h | h
  · exact card_res_ge_of_ge hπ h
  · exact card_res_ge_of_le hπ h

end Counting

/-! ### The block regrouping -/

/-- `∑_{i < a·d} g(i / d) = d · ∑_{j < a} g j` — the `Q = q ^ d` clearing, as ℕ-arithmetic. -/
private theorem sum_range_mul_div (d : ℕ) (hd : 0 < d) (g : ℕ → ℕ) (a : ℕ) :
    ∑ i ∈ Finset.range (a * d), g (i / d) = d * ∑ j ∈ Finset.range a, g j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hsplit : (a + 1) * d = a * d + d := by ring
    rw [hsplit, Finset.sum_range_add, ih, Finset.sum_range_succ, Nat.mul_add]
    congr 1
    have hconst : ∀ i ∈ Finset.range d, g ((a * d + i) / d) = g a := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hdiv : (a * d + i) / d = a := by
        rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hi', Nat.add_zero]
      rw [hdiv]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### NODE C.110, clause 1 — the conservative-cell count -/

-- The signed hypothesis `hk : 0 < k` is kept (frozen signature) but is not consumed: the count
-- is valuation bookkeeping and degenerates correctly at `k = 0` (every block bound is `1`).
set_option linter.unusedVariables false in
/-- **NODE C.110 (clause 1) — `#C_a(k) = Q ^ D_u(N)` at block degree `d`.**

The level-`N` coefficient classes admitting an integral lift that satisfies the conservative
bounds `v(b_j) ≥ (a−j)k + 1` (read blockwise through `i / d`) number exactly
`q ^ (d · ∑_{j<a} (N − ((a−j)k + 1)))`, the summand being ℕ-subtracted (the C.53 clip), so the
identity holds **at every finite window, including when conservative bounds lie beyond it**. -/
theorem ht_conservative_card (hπ : Irreducible π) [Finite (ResidueField O)]
    (d a k N : ℕ) (hd : 0 < d) (hk : 0 < k) :
    Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), (((a - i.1 / d) * k + 1 : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = residueCard O ^ (d * ∑ j ∈ Finset.range a, (N - ((a - j) * k + 1))) := by
  classical
  -- the coordinatewise bound, and the one-coordinate predicate it induces
  set M : Fin (a * d) → ℕ := fun i => (a - i.1 / d) * k + 1 with hM
  set R : Fin (a * d) → Res O N → Prop := fun i r =>
    ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((M i : ℕ) : ℕ∞) ≤ addVal O x with hR
  -- 1. the lift may be chosen coordinatewise
  have hiff : ∀ c : Coeff O (a * d) N,
      (∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), ((M i : ℕ) : ℕ∞) ≤ addVal O (b i))
        ↔ ∀ i : Fin (a * d), R i (c i) := by
    intro c
    constructor
    · rintro ⟨b, hb, hval⟩ i
      exact ⟨b i, congrFun hb i, hval i⟩
    · intro h
      choose x hx hval using h
      exact ⟨x, funext hx, hval⟩
  -- 2. the count is a product over coordinates
  have e2 : {c : Coeff O (a * d) N // ∀ i, R i (c i)}
      ≃ (∀ i : Fin (a * d), {r : Res O N // R i r}) := Equiv.subtypePiEquivPi
  have hstep : Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), ((M i : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = ∏ i : Fin (a * d), residueCard O ^ (N - M i) := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans e2), Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => card_res_ge hπ N (M i)
  rw [hstep, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ i : Fin (a * d), (N - M i)
      = ∑ i ∈ Finset.range (a * d), (fun j => N - ((a - j) * k + 1)) (i / d) :=
    Fin.sum_univ_eq_sum_range (fun i => N - ((a - i / d) * k + 1)) (a * d)
  rw [hsum, sum_range_mul_div d hd (fun j => N - ((a - j) * k + 1)) a]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_conservative_card

end AxCheck
