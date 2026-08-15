/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H07

/-!
# Uniformity.ChapH.H11 — the R4/A2 witness: an UNOCCUPIED height

**Chapter H, NODE H.11** (`blueprint/CHAP-H_general_induction.md` §3). At the genre datum
`(Q, e₁, f₁, μ, h) = (2, 3, 1, 2, 2)` the `dv`-height `m = 1` is **not** occupied (H.07): there is
no pair `(i, a)` of naturals with `i < 3` and `i·2 + 3·a = 1`. The unique solution over `ℤ` is
`i = 2, a = −1` — an unattainable normalizer exponent — so the sealed universal *"one `K`-digit
slot per **integer** `dv`-height"* is false.

`D′h = keyDeg · h = 3 · 1 · 2 = 6 > 1`, so the witness sits strictly inside the region the
terminal scope of H.10 withdraws; the two are consistent.

DEPENDS: H.01 (`GenreDatum`), H.07 (`Occupied`).

SOURCE: `EFF.GENHN.09`, the A2 obstruction record transcribed verbatim: *"The counterexample is
correct. For `(e_1,f_1,h,m)=(3,1,2,1)`, the unique normalizer exponent is `a=-1`, so neither an
integral normalizer nor a variable `K`-slot exists at height `1`. … the displayed universal
assertion "one `K`-digit slot per integer `dv`-height" is false. … no admissible repair can be
supplied under the stated constraint."*

**⚠ WHY THIS NODE EXISTS** (blueprint). Same reason as H.06: a withdrawn universal is only
*checkable* if its counterexample is landed, and `EFF.GENHN.09`'s TEETH field is explicit that no
battery row could produce it (every row has `f₁ = 1` and every consumed pin sits at `dv > D′h`).

**⚠ THE NODE MUST NOT BE GENERALIZED** (blueprint). "No `m ≤ D′h` is occupied" would be FALSE at
this very datum: `m = 0` is occupied (`i = a = 0`) and `m = 2` is occupied (`i = 1, a = 0`). The
statement is a single witness and stays one.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The A2/R4 witness datum `(Q; e₁, f₁, μ; h) = (2; 3, 1, 2; 2)`. -/
def genreA2witness : GenreDatum where
  Q := 2
  e₁ := 3
  f₁ := 1
  μ := 2
  h := 2
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

/-- **NODE H.11.** The `dv`-height `m = 1` is NOT occupied at the A2/R4 witness datum: no natural
pair `(i, a)` with `i < 3` solves `i·2 + 3·a = 1` (over `ℤ` the unique solution is `i = 2`,
`a = −1`). This refutes the sealed "one `K`-digit slot per integer `dv`-height". -/
theorem not_occupied_genreA2witness : ¬ genreA2witness.Occupied 1 := by
  rintro ⟨i, a, hi, ha⟩
  simp only [genreA2witness] at hi ha
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.genreA2witness
#print axioms Uniformity.Density.Induction.not_occupied_genreA2witness

end AxCheck
