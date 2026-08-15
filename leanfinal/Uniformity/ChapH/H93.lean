/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H93 — `A1Cell`, `(A1)`-admissible family data

**Chapter H, NODE H.93** (`blueprint/CHAP-H_general_induction.md` §13; source `EFF.GENIND.30`,
`LEMMA GENIND-0`'s objects, plus `EFF.GENIND.60`'s OPEN-CALL 3). *`(A1)`-admissible family data,
WITH the σ-label clause.*

An `(A1)`-admissible family over a parameter dimension `r` is a finite list of **cells**; each
cell carries a shifted product of arithmetic progressions in `ℕ ^ r` (offsets and strides), an
exponent form affine with strictly positive integer coefficients, a `q`-independent coefficient,
an affine visibility form, **and a splitting-type label `σ : FactorizationType`**.

The σ-label field is W-12's r4 STRENGTHENING of `(A1)`: the corpus states `GENIND-0`'s closure
claim for the *pre-r4* predicate and carries the strengthened version as OPEN-CALL 3.  Carrying
the field here (and proving closure for the strengthened predicate at H.94) discharges the open
call **for the Lean development only** — nothing here edits a frozen note.

Definitional, no proof obligation beyond the `stride_pos` / `expCoeff_pos` field *types*.

DEPENDS: landed `Uniformity.FactorizationType`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- One cell of an `(A1)`-admissible family: a shifted product of arithmetic progressions in `ℕ ^ r`
with an affine positive-coefficient exponent, an affine visibility form, a coefficient, and a
σ-label.  **The σ-label field is W-12's r4 STRENGTHENING of `(A1)`** — see the note. -/
structure A1Cell (r : ℕ) where
  /-- Per-coordinate offset. -/
  offset : Fin r → ℕ
  /-- Per-coordinate stride (positive). -/
  stride : Fin r → ℕ
  stride_pos : ∀ i, 0 < stride i
  /-- The exponent's positive coefficients and constant. -/
  expCoeff : Fin r → ℕ
  expCoeff_pos : ∀ i, 0 < expCoeff i
  expConst : ℕ
  /-- The visibility form. -/
  visCoeff : Fin r → ℕ
  visConst : ℕ
  /-- The family's `q`-independent coefficient. -/
  coeff : ℕ
  /-- **The σ-label** (W-12 r4). -/
  σ : FactorizationType

/-- The parameter locus of a cell: the shifted product of arithmetic progressions. -/
def A1Cell.locus {r : ℕ} (C : A1Cell r) : Set (Fin r → ℕ) :=
  {p | ∀ i, ∃ t : ℕ, p i = C.offset i + C.stride i * t}

/-- The cell's exponent at a parameter point. -/
def A1Cell.exp {r : ℕ} (C : A1Cell r) (p : Fin r → ℕ) : ℕ :=
  C.expConst + ∑ i, C.expCoeff i * p i

/-- An `(A1)`-admissible family is a finite list of cells. -/
def A1Family (r : ℕ) : Type := List (A1Cell r)

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.A1Cell
#print axioms Uniformity.Density.Induction.A1Cell.locus
#print axioms Uniformity.Density.Induction.A1Cell.exp
#print axioms Uniformity.Density.Induction.A1Family

end AxCheck
