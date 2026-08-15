/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H51

/-!
# Uniformity.ChapH.H57 — the wrap exponent `W(t)`

**Chapter H, NODE H.57** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer).

Powers of a class representative wrap through `θ^{e₁} = (unit lift)·π^{h}`, and the corpus records
the bookkeeping as a cocycle `n(u₂)^r = n(r·u₂)·(x^{e₁}/π^{h})^{W}` with the **wrap count**
`W = ⌊r·i / e₁⌋`. This node lands that bookkeeping **at the exponent level only**:

* `wrap_div_mod` — the division identity `r*i = (r*i % e) + e*(r*i / e)` together with
  `r*i % e < e`, i.e. `W := r*i / e` is the wrap count and `i(r·M) := r*i % e` the wrapped class;
* `wrap_height` — its height consequence: if a slot has height `M = i*h + e*a`, then the `r`-th
  power sits at `r*M = (r*i % e)*h + e*(r*a + W*h)`, i.e. in class `r*i % e` with valuation
  coefficient `r*a + W*h`.

DEPENDS: H.51 (the class bookkeeping mod `e₁`, cited for context) · mathlib `Nat.mod_add_div`,
`Nat.mod_lt`.

**SOURCE.** `EFF.GENHN.28` (*"Products wrap through `θ^{e₁} = (unit lift)·π^h`:
`n(κ)^t = ẑ^{fl}·n(tκ)` with the explicit integer `fl` = the wrap count — W-9's cocycle,
literal"*); `EFF.GENHN.42` (the HETOW erratum: *"`n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)}`
with `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`"*); `EFF.GENHN.81`'s APPLICATION, whose own verification paragraph
re-derives `e₁(r·a(u₂) − a(r u₂)) = −e₁ W(t) h` — two independent derivations agreeing.

**⚠ SCOPE FENCE.** Chapter H reproduces the **arithmetic only**. The step from this exponent
identity to the carrier-level statement `res(n(u₂)^r / n(r u₂)) = η^{W}` needs the carrier and is a
hypothesis of the consumer; stating a cocycle identity in `K` here would be a `W-9` consumption,
which §8 forbids (H.51's fence).

**ARITHMETIC AUDIT** (blueprint, recomputed): `(e, h, i, a) = (3, 2, 2, 1)`, `M = 7`; `r = 2` gives
`r*i = 4`, `4 % 3 = 1`, `W = 1`, and `2*7 = 14 = 1*2 + 3*(2*1 + 1*2)` ✓; `r = 3` gives `W = 2` and
`21 = 0 + 3*(3 + 4)` ✓. `(e, h, i, a) = (2, 1, 1, 3)`, `M = 7`, `r = 3`: `W = 1` and
`21 = 1*1 + 2*(9 + 1)` ✓.

**PROOF.** (1) `wrap_div_mod`: `(Nat.mod_add_div _ _).symm` and `Nat.mod_lt _ he`. (2)
`wrap_height`: substitute `M`, then multiply the division identity `r*i % e + e*(r*i / e) = r*i`
through by `h` and rearrange with `ring`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **H.57 (a) — the wrap decomposition.** `W := r*i / e` is the wrap count and `r*i % e < e` the
wrapped residue class. -/
theorem wrap_div_mod (r i e : ℕ) (he : 0 < e) :
    r * i = r * i % e + e * (r * i / e) ∧ r * i % e < e :=
  ⟨(Nat.mod_add_div (r * i) e).symm, Nat.mod_lt _ he⟩

/-- The height bookkeeping behind the wrap: if `i·h + e·a = M` then
`r·M = (r·i % e)·h + e·(r·a + W·h)` with `W = r·i / e`. -/
theorem wrap_height {i a M h e r : ℕ} (he : 0 < e) (hM : i * h + e * a = M) :
    r * M = (r * i % e) * h + e * (r * a + (r * i / e) * h) := by
  subst hM
  have hd : r * i % e + e * (r * i / e) = r * i := Nat.mod_add_div (r * i) e
  calc r * (i * h + e * a)
      = (r * i % e + e * (r * i / e)) * h + e * (r * a) := by rw [hd]; ring
    _ = (r * i % e) * h + e * (r * a + (r * i / e) * h) := by ring

section AxCheck
#print axioms Uniformity.Density.Induction.wrap_div_mod
#print axioms Uniformity.Density.Induction.wrap_height
end AxCheck

end Uniformity.Density.Induction
