/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapC.C93 — threshold arithmetic: the `HYP.82` census made formal, clause (i)

**Chapter C, NODE C.93** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §9; signed at
A-C.1, `leanspec/Leanspec/ChapC.lean` `tower_first_live` — landed here at the signed signature
VERBATIM, by unit OM-7, 2026-08-16). ENV-C5: `ℕ` only.

*Clause (i), the threshold arithmetic*: a depth-`r` tower with a live top problem `μ_r ≥ 2`
and proper levels (`l_i ≥ 2` for `1 ≤ i ≤ r`) needs

    n = D_r · μ_r ≥ 2^(r+1)      (D_r = ∏_{i=1..r} l_i, properness telescoped),

so depth 1 first lives at `n = 4`, depth 2 at `n ≥ 8` (C.31's bound), depth 3 at `n ≥ 16`,
depth 4 at `n = 32` — and the bound is SHARP: the all-`2` tower with `μ_r = 2` attains it
(`tower_first_live_sharp` below; the S4 witness `u = 5, 21, 85, 341`, `n = 32`, is exactly
minimal). Exhaustive numeric certification: `verification/openmath/om7_cert.py` LEG F
(27,300 tuples, 0 bad; tooth T-TOW: the strengthened bound `2^(r+2)` fails on the witness).

*Clause (ii), the census `#check` suite* (items (1)–(5) + (6)(β) = the named §6/§8/§9
theorems; (6)(α) at depth 3 = C.90/C.91's scope; depth ≥ 4 claimed by NO node) is the
`C93Census` block of `leanspec/Leanspec/ChapC.lean` and lands in `leanfinal` only when the
named items themselves land — the census names are fleet-owned and NOT duplicated here.
The `n ≥ 8` open remainder is exactly the ledger's box family
(HYP.67–71/78–80/142/143/144-BOX-2); this node adds no conjunct and discharges none of it.

DEPENDS: none (arithmetic). SOURCE: `EFF.GENTOW5.20` (verbatim); C-H4's disposition table;
ledger HYP.82; CHAP-I NODE I.07 (`GenhnTow1At`, the carrier this node's name serves).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

-- `hr : 1 ≤ r` is part of the A-C.1-signed signature and is kept VERBATIM (signature fence)
-- even though the proof does not consume it (the bound holds at `r = 0` too).
set_option linter.unusedVariables false in
/-- **C.93 (i), the `[GENHN-TOW-1]` first-live threshold** (ledger HYP.82; signed signature
verbatim from `leanspec/Leanspec/ChapC.lean` A-C.1): a depth-`r` tower with proper levels
`l_i ≥ 2` and a live top problem `μ_r ≥ 2` has `n = D·μ_r ≥ 2^(r+1)`. -/
theorem tower_first_live (r μr : ℕ) (hr : 1 ≤ r) (hμ : 2 ≤ μr) (l : ℕ → ℕ)
    (hl : ∀ i, 1 ≤ i → i ≤ r → 2 ≤ l i) (D : ℕ) (hD : D = ∏ i ∈ Finset.Icc 1 r, l i) :
    2 ^ (r + 1) ≤ D * μr := by
  have hD2 : 2 ^ r ≤ D := by
    subst hD
    calc 2 ^ r = ∏ _i ∈ Finset.Icc 1 r, 2 := by
          rw [Finset.prod_const, Nat.card_Icc]
          simp
      _ ≤ ∏ i ∈ Finset.Icc 1 r, l i :=
          Finset.prod_le_prod' fun i hi =>
            hl i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  calc 2 ^ (r + 1) = 2 ^ r * 2 := by ring
    _ ≤ D * μr := Nat.mul_le_mul hD2 hμ

/-- **Sharpness**: the all-`2` tower with `μ_r = 2` attains the threshold exactly — depth 2
first lives at `n = 8`, depth 3 at `16`, depth 4 at `32` (the S4 witness is minimal). -/
theorem tower_first_live_sharp (r : ℕ) :
    (∏ _i ∈ Finset.Icc 1 r, 2) * 2 = 2 ^ (r + 1) := by
  rw [Finset.prod_const, Nat.card_Icc, ← pow_succ]
  simp

-- The depth first-live table, instance-checked (om7_cert.py LEG F3):
example : 2 ^ (1 + 1) = 4 := by norm_num
example : 2 ^ (2 + 1) = 8 := by norm_num
example : 2 ^ (3 + 1) = 16 := by norm_num
example : 2 ^ (4 + 1) = 32 := by norm_num

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.tower_first_live
#print axioms Uniformity.Density.Tower.tower_first_live_sharp

end AxCheck
