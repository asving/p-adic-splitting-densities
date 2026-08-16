/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F07 — `CarryCocycle`: W-9 clauses (i)+(ii) as a structure

**Chapter F, NODE F.07** [def] (`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1 +
`[NeZero E] [Field K]`. `EFF.GRTJC.89` clauses (i)/(ii), byte-verbatim in the spec: the
`Kˣ`-valued 2-cocycle identity with its `{0,1}`-valued integer shadow.

**Kind inversion, disclosed (blueprint FAITHFULNESS):** the corpus PROVES (i)/(ii) from the
GRTJC stack (W-6/W-7/W-8 + `(MULT-B)|gr` + `(DMULT-w)`); F carries them as structure FIELDS,
so the corpus conditionality is carried by instantiation, never silently discharged. An
instance of `CarryCocycle` at a concrete site is exactly "W-9's conclusion holds there".

**Below the contract line** [added: A-W.2, unit OM-9 — certified by
`verification/openmath/om9_weld_cert.py` LEG C over every enumerated cocycle at
`E ∈ {2,3,4}`, `|Kˣ| ∈ {2,3,4}` before proving]: three elementary consequences of the
cocycle identity that F.08's unit laws and F.10b's power basis consume — the degenerate rows
are constant (`c_zero_left`/`c_zero_right`) and the first row/column agree (`c_one_comm`,
the telescoped identity `c(1,k)/c(k,1) = c(1,k+1)/(c(k+1,1))` forced constant `= 1` by
successor induction).

Signatures byte-identical to the stage-0e gate. Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- A carry cocycle over `ZMod E` (`EFF.GRTJC.89` clauses (i)/(ii)): the `Kˣ`-valued
2-cocycle with its `{0,1}`-valued integer shadow. -/
structure CarryCocycle (E : ℕ) [NeZero E] (K : Type*) [Field K] where
  c : ZMod E → ZMod E → Kˣ
  δ : ZMod E → ZMod E → ℕ
  cocycle : ∀ a b d, c a b * c (a + b) d = c b d * c a (b + d)
  δ_le_one : ∀ a b, δ a b ≤ 1
  δ_cocycle : ∀ a b d, δ a b + δ (a + b) d = δ b d + δ a (b + d)

namespace CarryCocycle

variable {E : ℕ} [NeZero E] {K : Type*} [Field K] (cc : CarryCocycle E K)

/-- [A-W.2, below the contract line] The zero column is constant: `c a 0 = c 0 0`.
From the cocycle identity at `(a, 0, 0)`. -/
theorem c_zero_right (a : ZMod E) : cc.c a 0 = cc.c 0 0 := by
  have h := cc.cocycle a 0 0
  rw [add_zero, zero_add] at h
  exact mul_right_cancel h

/-- [A-W.2, below the contract line] The zero row is constant: `c 0 b = c 0 0`.
From the cocycle identity at `(0, 0, b)`. -/
theorem c_zero_left (b : ZMod E) : cc.c 0 b = cc.c 0 0 := by
  have h := cc.cocycle 0 0 b
  rw [add_zero, zero_add] at h
  exact (mul_right_cancel h).symm

/-- [A-W.2, below the contract line] First row = first column: `c 1 k = c k 1`. The ratio
`s k := c 1 k / c k 1` is invariant under `k ↦ k + 1` (the cocycle identity at `(1, k, 1)`)
and `s 1 = 1`; successor reaches all of `ZMod E`. Certified over every cocycle at `E ≤ 4`
before proving (om9_weld_cert.py LEG C3). -/
theorem c_one_comm (k : ZMod E) : cc.c 1 k = cc.c k 1 := by
  -- the successor step, valid at every j
  have step : ∀ j : ZMod E, cc.c 1 j / cc.c j 1 = cc.c 1 (j + 1) / cc.c (j + 1) 1 := by
    intro j
    have h := cc.cocycle 1 j 1
    -- h : c 1 j * c (1+j) 1 = c j 1 * c 1 (j+1)
    rw [add_comm 1 j] at h
    rw [div_eq_div_iff_mul_eq_mul]
    exact h.trans (mul_comm _ _)
  -- propagate from the base s 1 = 1 along ℕ-successors
  have chain : ∀ n : ℕ, cc.c 1 (1 + (n : ZMod E)) / cc.c (1 + (n : ZMod E)) 1 = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Nat.cast_succ, ← add_assoc, ← step (1 + (m : ZMod E))]
        exact ih
  -- every k is 1 + ((k - 1).val : ZMod E)
  have hk : 1 + (((k - 1).val : ℕ) : ZMod E) = k := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact add_sub_cancel 1 k
  have h := chain (k - 1).val
  rw [hk] at h
  exact div_eq_one.mp h

end CarryCocycle

end Uniformity.Density.Weld
