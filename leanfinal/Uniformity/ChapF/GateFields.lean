/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.GateFields — §10's shared construction block: the table-built `F₄`, `F₉`

**Chapter F, §10 construction block** (`blueprint/CHAP-F_weld_layer.md` §10, the paragraph
"Field constructions — THE FALLBACK FIRED; the table-built fields are the form of record"
*[repaired: A-W.1/F-D6, executed 2026-08-16]*). This file signs **no blueprint declaration**:
it holds the two gate-local finite fields the F.29 and F.30 gate batteries share, and nothing
else. Its declarations are gate carriers, not chapter-F mathematics — no consumer outside
`Uniformity.ChapF.F29`/`Uniformity.ChapF.F30` may import them as content.

**Why tables and not `AdjoinRoot`.** The committed blueprint displayed
`F₄ := AdjoinRoot (X² + X + 1 : (ZMod 2)[X])` and `F₉ := AdjoinRoot (X² + 1 : (ZMod 3)[X])`.
`AdjoinRoot` is a quotient of a polynomial ring and carries **no** `DecidableEq`/`Fintype`
instance, so **no `decide` gate can fire on it at all** — a hard absence, not a "resists" case.
Under §10's own pre-authorization ("a private table-built field instance below the gate in the
same file") the gates run on the tables below. The `AdjoinRoot` spellings remain the
mathematical identification of the two fields (and are what a *proof* about `F₄`/`F₉` would
use); they are not gate carriers. **`native_decide` appears nowhere** in this file or in either
gate (axiom census).

**Why these two fields and not `F₂`/`F₃` alone** (GC-11's coincidence-regime discipline; the
arena note of §10). Two degeneracies stalk this chapter's numerics: (i) over `F₂` the unit group
is trivial, so every character check silently passes (F.06 — promoted to a theorem there); (ii)
on involution geographies (`ξ² = 1`) the corrected Σ-map and the WRONG boxed map coincide — 468
sealed rows hid the defect that way (SL-INVREC 218/218). So the character content runs at
`q = 2` on `F₄` (generator of order 3 — non-involution) and at `q = 3` on `F₉` (generator of
order 4 — non-involution), with `F₂`-triviality and involution instances kept as explicit
NEGATIVE controls inside the gates. `e > 1 ∧ f > 1` witness: `E = 2` with `F₄/F₂` (f = 2) and
the same shape at `F₉/F₃`.

Each field carries its own construction certificates below its table (card, generator order,
non-involution), so a table typo cannot pass silently.

## Status

Sorry-free, `native_decide`-free; the certificates are `decide`d `example`s.
-/

namespace Uniformity.Density.Weld

/-! ## Gate-local field `F4 = (ZMod 2)[θ]/(θ² − θ − 1)`, carrier `ZMod 2 × ZMod 2` -/

/-- Gate-local: the four-element field, table-built (NOT a blueprint declaration). -/
def F4 : Type := ZMod 2 × ZMod 2

namespace F4

instance : DecidableEq F4 := inferInstanceAs (DecidableEq (ZMod 2 × ZMod 2))
instance : Fintype F4 := inferInstanceAs (Fintype (ZMod 2 × ZMod 2))
instance : Inhabited F4 := inferInstanceAs (Inhabited (ZMod 2 × ZMod 2))
instance : Zero F4 := ⟨(0, 0)⟩
instance : One F4 := ⟨(1, 0)⟩
instance : Add F4 := ⟨fun x y => ((x.1 + y.1 : ZMod 2), (x.2 + y.2 : ZMod 2))⟩
instance : Neg F4 := ⟨fun x => ((-x.1 : ZMod 2), (-x.2 : ZMod 2))⟩
/-- `θ² = θ + 1`. -/
instance : Mul F4 :=
  ⟨fun x y => ((x.1 * y.1 + x.2 * y.2 : ZMod 2), (x.1 * y.2 + x.2 * y.1 + x.2 * y.2 : ZMod 2))⟩

instance commRing : CommRing F4 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  zero_mul := by decide
  mul_zero := by decide

/-- `x⁻¹ = x^(q−2) = x²` on `F₄`; `0⁻¹ = 0`. -/
instance : Field F4 :=
  { commRing with
    inv := fun x => x * x
    nnqsmul := _
    qsmul := _
    exists_pair_ne := ⟨0, 1, by decide⟩
    mul_inv_cancel := by decide
    inv_zero := by decide }

/-- `ω = θ`, of multiplicative order 3 — the NON-involution character at `q = 2`. -/
def omega : F4ˣ := ⟨(0, 1), (1, 1), by decide, by decide⟩

-- construction certificates: `Fintype.card F₄ = 4` and the order-3 (non-involution) witness
example : Fintype.card F4 = 4 := by decide
example : omega ^ 3 = 1 := by decide
example : omega ≠ 1 := by decide
example : omega ^ 2 ≠ 1 := by decide

end F4

/-! ## Gate-local field `F9 = (ZMod 3)[θ]/(θ² + 1)`, carrier `ZMod 3 × ZMod 3` -/

/-- Gate-local: the nine-element field, table-built (NOT a blueprint declaration). -/
def F9 : Type := ZMod 3 × ZMod 3

namespace F9

instance : DecidableEq F9 := inferInstanceAs (DecidableEq (ZMod 3 × ZMod 3))
instance : Fintype F9 := inferInstanceAs (Fintype (ZMod 3 × ZMod 3))
instance : Inhabited F9 := inferInstanceAs (Inhabited (ZMod 3 × ZMod 3))
instance : Zero F9 := ⟨(0, 0)⟩
instance : One F9 := ⟨(1, 0)⟩
instance : Add F9 := ⟨fun x y => ((x.1 + y.1 : ZMod 3), (x.2 + y.2 : ZMod 3))⟩
instance : Neg F9 := ⟨fun x => ((-x.1 : ZMod 3), (-x.2 : ZMod 3))⟩
/-- `θ² = −1`. -/
instance : Mul F9 :=
  ⟨fun x y => ((x.1 * y.1 - x.2 * y.2 : ZMod 3), (x.1 * y.2 + x.2 * y.1 : ZMod 3))⟩

instance commRing : CommRing F9 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  zero_mul := by decide
  mul_zero := by decide

/-- `x⁻¹ = x^(q−2) = x⁷` on `F₉`; `0⁻¹ = 0`. -/
instance : Field F9 :=
  { commRing with
    inv := fun x => x * x * x * x * x * x * x
    nnqsmul := _
    qsmul := _
    exists_pair_ne := ⟨0, 1, by decide⟩
    mul_inv_cancel := by decide
    inv_zero := by decide }

/-- `i = θ`, of multiplicative order 4 — the NON-involution character at `q = 3`. -/
def iUnit : F9ˣ := ⟨(0, 1), (0, -1), by decide, by decide⟩

-- construction certificates: `Fintype.card F₉ = 9` and the order-4 (non-involution) witness
example : Fintype.card F9 = 9 := by decide
example : iUnit ^ 4 = 1 := by decide
example : iUnit ^ 2 ≠ 1 := by decide

end F9

end Uniformity.Density.Weld
