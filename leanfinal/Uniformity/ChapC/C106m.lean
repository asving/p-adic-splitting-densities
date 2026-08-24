/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C97
import Uniformity.ChapC.C98
import Uniformity.ChapC.C99r
import Uniformity.ChapC.C102gt
import Uniformity.ChapC.C105

/-!
# Uniformity.ChapC.C106m — Chapter C, NODE C.106, the §10 GENTOW2 supply manifest

Unit C106. The signed node (`leanspec/Leanspec/ChapC.lean`, `section C106Manifest`,
~line 3851) is a documentation `#check` suite over exactly ten already-signed names:
`gentow2_Bpp`/C.99, `theta_letter_valued` (C.99's γ-calculus companion axiom, no separate
node number), `gentow2_Bp`/C.100, `gentow2_B`/C.101, `s2Witness`/C.97,
`shear_onesided_iff`/C.98, `letter_formula`/C.102, `gentow2_A`/C.103, `repoRead`/C.104,
`wconj_invariants`/C.105.

## Verdict: PARTIAL, honest — 7 of 10 checked, 3 recorded as open (not 2)

The dispatch note for this unit states two HOLD rows (C.100, C.102). Re-checked here against
the corpus (`rg` on every one of the ten names, below) and against the two units that most
recently touched these nodes (`C99r.lean`'s A-C.12 re-sign landing and `C102gt.lean`'s GTB
verdict): **three** names have no leanfinal declaration, not two — `theta_letter_valued`
is a second, independently-blocked axiom bundled inside NODE C.99's own leanspec block
(`ChapC.lean:2483-2499`), distinct from `gentow2_Bpp` in the same block. C.99's row is only
half-landed. This file reports that discrepancy rather than silently matching the dispatch
note's count.

Per name:

* `gentow2_Bpp` (C.99) — **LANDED**, `C99r.lean`, `Uniformity.Density.Tower.C99r` (A-C.12
  re-sign, full landing, Lean core only).
* `theta_letter_valued` (C.99 companion) — **HOLD, `OPEN-LETTERS`**. No leanfinal
  declaration anywhere (`rg -n "theta_letter_valued" Uniformity/` outside prose: none). Per
  `C99r.lean`'s own note: needs the γ-recursion / exponent-lattice dictionary (published
  Def 3.12, §3.3), in neither `FGMNCalculus` nor any landed carrier — "NOT ATTEMPTED, stays
  BLOCKED."
* `gentow2_Bp` (C.100) — **HOLD, `OPEN-EVAL-ISO`**. No leanfinal declaration
  (`C99gt.lean`'s verdict, re-checked against the A-C.11 re-signed statement still current
  in `leanspec/Leanspec/ChapC.lean:2505-2518`): no class field ties the signed `ρ` to the
  canonical evaluation map `k(L2) ≅ F₃`.
* `gentow2_B` (C.101) — **LANDED**, `C99r.lean`, `Uniformity.Density.Tower.C99r` (A-C.12
  re-sign, full landing, Lean core only).
* `s2Witness` (C.97) — **LANDED**, `C97.lean`, `Uniformity.Density.Tower`.
* `shear_onesided_iff` (C.98) — **LANDED**, `C98.lean`, `Uniformity.Density.Tower`.
* `letter_formula` (C.102) — **HOLD, `OPEN-EVAL-ISO` + `OPEN-LETTERS`**. No leanfinal
  declaration (`C102gt.lean`'s verdict; the class's only `letterZ` field is nonvanishing,
  no law connecting it to `ρ`/`AdjoinRoot.root T.ψ₂`; unchanged by A-C.12, which touched
  only C.99/C.101/C.103).
* `gentow2_A` (C.103) — **LANDED**, `C99r.lean`, `Uniformity.Density.Tower.C99r` (A-C.12
  re-sign supplied the missing `coeff 0 ≠ 0` antecedent that blocked it at GTB; now a full
  landing, Lean core only).
* `repoRead` (C.104) — **LANDED**, `C102gt.lean`, `Uniformity.Density.Tower` (byte-identical
  `def`, no proof obligation).
* `wconj_invariants` (C.105) — **LANDED**, `C105.lean`, `Uniformity.Density.Tower`.

## Disposition

The signed manifest is an unconditional flat list of ten `#check`s; there is no signed
provision for a partial form. Emitting all ten verbatim would not build: `theta_letter_valued`,
`gentow2_Bp`, and `letter_formula` name no leanfinal declaration, so `#check @name` on them is
an *unknown identifier* elaboration error, not a checkable-but-false statement — there is
nothing to weaken or paper over. Per the honesty discipline (never assert a subset as if it
were the signed whole; C.105gt.lean's own prior verdict on this exact node made the same
call when zero of ten were landed), this file:

1. `#check`s the seven declarations that exist, each commented with its source node and file
   (below) — a real, LANDED partial assembly, not a placeholder.
2. Leaves the three HOLD names as commented-out `#check` lines with their exact audited gap
   tag, so the manifest's full ten-row shape stays visible and no gap is silently dropped
   (the C.116 precedent for a manifest row that cannot be checked: comment, name the reason,
   do not delete the row).
3. Does NOT declare the node "landed" — seven of ten checked is not the signed C.106.

## DEPENDS

C.97 (`s2Witness`) · C.98 (`shear_onesided_iff`) · C.99r (`gentow2_Bpp`, `gentow2_B`,
`gentow2_A`, the A-C.12 re-sign landings of C.99/C.101/C.103) · C.102gt (`repoRead`) · C.105
(`wconj_invariants`).

## Status

Documentation node, partial. No new `Prop`, no proof obligation, no `sorry`, no new axiom,
no `unsafe`, no statement weakening. The seven `#check`s below elaborate declarations whose
own axiom footprints are Lean core only (printed in their home files); nothing here adds to
that footprint.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Tower.C99r

section C106Manifest

-- C.97, LANDED (`C97.lean`, `Uniformity.Density.Tower`)
#check @s2Witness

-- C.98, LANDED (`C98.lean`, `Uniformity.Density.Tower`)
#check @shear_onesided_iff

-- C.99, LANDED (`C99r.lean`, `Uniformity.Density.Tower.C99r`, A-C.12 re-sign)
#check @gentow2_Bpp

-- C.99 companion — HOLD, `OPEN-LETTERS`: no leanfinal declaration (γ-recursion /
-- exponent-lattice dictionary, published Def 3.12 §3.3, not in `FGMNCalculus` or any
-- landed carrier). See `C99r.lean`'s note above `recipe3`.
-- #check @theta_letter_valued

-- C.100 — HOLD, `OPEN-EVAL-ISO`: no leanfinal declaration (no class field ties the signed
-- `ρ` to the canonical evaluation map `k(L2) ≅ F₃`). See `C99gt.lean`.
-- #check @gentow2_Bp

-- C.101, LANDED (`C99r.lean`, `Uniformity.Density.Tower.C99r`, A-C.12 re-sign)
#check @gentow2_B

-- C.102 — HOLD, `OPEN-EVAL-ISO` + `OPEN-LETTERS`: the class's only `letterZ` field is
-- nonvanishing; no law connects it to `ρ`/`AdjoinRoot.root T.ψ₂`. See `C102gt.lean`.
-- #check @letter_formula

-- C.103, LANDED (`C99r.lean`, `Uniformity.Density.Tower.C99r`, A-C.12 re-sign)
#check @gentow2_A

-- C.104, LANDED (`C102gt.lean`, `Uniformity.Density.Tower`)
#check @repoRead

-- C.105, LANDED (`C105.lean`, `Uniformity.Density.Tower`)
#check @wconj_invariants

end C106Manifest

end Uniformity.Density.Tower
