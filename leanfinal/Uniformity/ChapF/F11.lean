/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F07

/-!
# Uniformity.ChapF.F11 — `CarrySite`, `GenhnBox2`: `GENHN-BOX-2` at ledger strength (HYP.148)

**Chapter F, NODE F.11** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1.
**Display-A supply node (2 of 2).** Transcribed from HYP.148 (CARRY) and GENHN's own
dependency ledger: "GRTJC W-6..W-9 + JC-LOAD/W-8 are consumed at LEMMA GENHN-4 layer 1
(μ ≥ 3) — the ONE weld face inside a count law, disclosed (GENHN-BOX-2); elsewhere
frame-only"; pricing: "the count laws at μ ≥ 3 stand on one accepted weld face."

Scope pins carried in the statement: the `μ ≥ 3` guard is in the `Prop` (below it the site
owes nothing weld-side); first live degree `n = 6` is chapter I's index on the conjunct
field (F does not carry `n`); **clause (iv) is structurally absent** (not consumed at
layer 1 — `EFF.GRTJC.89`'s four-supply table, row (iv): "NOT CONSUMED"). NOT inherited by
the σ chain (HE3 L1293) and NOT by the tower leg (GENTOW5 L157).

**CARRIED, not proved.** The discharge route is HYP.149 = WELD-ZERO, **pending at
clean-pass 1 of 2** (honesty F-2) — nothing here consumes or anticipates it. Concrete site
instances are chapter-H/C stage objects (GC-13); no F node constructs one.

Signatures byte-identical to the stage-0e gate (including the non-instance-implicit
`∃ (h : NeZero s.E)` binder, which serves as the local instance for `CarryCocycle s.E K`).
Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- A composite-stage CARRY SITE at multiplicity `μ`: the stage's carry bookkeeping as an
abstract indexed family. Instances are chapter-H/C stage objects (GC-13). -/
structure CarrySite (K : Type*) [Field K] where
  E : ℕ
  hE : 1 ≤ E
  μ : ℕ
  carry : ZMod E → ZMod E → K   -- the stage's own carry table (site data)

-- The named binder `∃ (h : NeZero s.E)` is the SIGNED signature (stage-0e gate: it serves
-- as the local instance for `CarryCocycle s.E K`); the unused-variable linter is silenced
-- rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `GENHN-BOX-2` at ledger strength (HYP.148): at `μ ≥ 3` the site's carry bookkeeping is
realized by a carry cocycle's twisted algebra — W-9 clauses (i)–(iii), clause (iv) absent.
CARRIED, not proved; chapter I's `n ≥ 6`-indexed conjunct field. -/
def GenhnBox2 {K : Type*} [Field K] (s : CarrySite K) : Prop :=
  3 ≤ s.μ → ∃ (h : NeZero s.E) (cc : CarryCocycle s.E K),
    ∀ a b, (cc.c a b : K) = s.carry a b

end Uniformity.Density.Weld
