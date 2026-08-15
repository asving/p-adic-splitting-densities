/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H85 — the `dv`-parity separation at `e₁ = 2`

**Chapter H, NODE H.85** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). At
`e₁ = 2` the root has `v(θ) = h/2` with `h` odd, so the two slots contributing to
`dv(a·x + b) = min(2 v(a) + h, 2 v(b))` sit in *different parity classes*: `2 v(a) + h` is odd and
`2 v(b)` is even. Hence they are never equal (`dv_parity_ne`), the minimum is attained at a
unique coordinate, and the ultrametric inequality `v(A(θ)) ≥ min(...)` is an **equality**.

This is the `e₁ = 2` specialization of H.52's general-`e₁` slot separation (there by coprimality
of `h` and `e₁`; here by parity, which is that argument at `e₁ = 2`). `dv_parity_min_unique`
records the resulting dichotomy: the min *is* one of the two slots, and — via the strict
inequality supplied by `dv_parity_ne` — exactly one.

**⚠ WELD-FREE, AND THE SPEC SAYS SO TWICE.** `EFF.GENH4.19`'s DERIVATION: *"**No weld-corpus
lemma is consumed** — the note's own claim, and the proof bears it out."* And `EFF.GENH4.05`'s
division of consumption: *"the slot geometry and no-cancellation are RE-PROVED elementarily
below"*. This file honours that: it cites no `W-8`, `W-9` or `JC-LOAD`, and imports nothing from
the weld corpus — the whole content is `Odd h` plus `ℕ`-arithmetic. (The one weld face in the
corpus is `GENHN-4` layer 1 at `μ ≥ 3`, `HYP.148`, which has no node — honesty item H-5(3).)

**Arithmetic audit (recomputed).** `h = 1`, `v_a = 3`, `v_b = 3`: slots `7` and `6`, min `6`,
attained only at `b` ✓. `h = 3`, `v_a = 0`, `v_b = 5`: slots `3` and `10`, min `3`, attained only
at `a` ✓. There is no `(h, v_a, v_b)` with the two slots equal, since one is odd and one even ✓.

DEPENDS: H.52 (the general-`e₁` slot separation; this is its `e₁ = 2` specialization by parity).
Both statements are `ℕ`-arithmetic and self-contained, so nothing is imported from it.

SOURCE: `EFF.GENH4.19` (`LEMMA GENH4-2`(E), verbatim: *"`v(A(θ)) = min(v(a) + h/2, v(b))` EXACTLY
— the min is uniquely attained (`2v(a)+h` odd, `2v(b)` even: distinct parities, no ties) … This is
JC-LOAD's no-cancellation warrant holding BY PARITY — elementary, hence not consumed"*);
`EFF.GENIND.68` (*"`dv`-arithmetic: `dv(a·x + b) = min(2v(a) + h, 2v(b))` (the root has
`v = h/2`); `2v(b)` is even, `2v(a)+h` odd — distinct parities, no ties, one slot per integer
`dv`"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The parity separation.** At odd `h`, the slot value `2 v(a) + h` (odd) can never equal the
slot value `2 v(b)` (even): the two `dv`-slots of `a·x + b` lie in different parity classes, so
there are no ties. -/
theorem dv_parity_ne {h va vb : ℕ} (hh : Odd h) : 2 * va + h ≠ 2 * vb := by
  obtain ⟨j, hj⟩ := hh
  subst hj
  omega

/-- **The min is attained at a single slot.** Since the two slots are never equal
(`dv_parity_ne`), one of them is strictly smaller, and `min (2 v(a) + h) (2 v(b))` equals that
one — so the ultrametric bound on `dv(a·x + b)` is an equality. -/
theorem dv_parity_min_unique {h va vb : ℕ} (hh : Odd h) :
    min (2 * va + h) (2 * vb) = 2 * va + h ∨ min (2 * va + h) (2 * vb) = 2 * vb := by
  rcases (dv_parity_ne (h := h) (va := va) (vb := vb) hh).lt_or_gt with hlt | hlt
  · exact Or.inl (min_eq_left hlt.le)
  · exact Or.inr (min_eq_right hlt.le)

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.dv_parity_ne
#print axioms Uniformity.Density.Induction.dv_parity_min_unique

end AxCheck
