/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F14

/-!
# Uniformity.ChapF.F17 — `SigmaLedgerLaw`: THEOREM SL-1's Σ-properties package

**Chapter F, NODE F.17** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §6), ENV-F1.
THEOREM SL-1 at corpus scope (`EFF.SIGMALAW.05`), carried as the interface the abstract core
instantiates: at every shared-below junction at level `m + 1`, for every supported slot `j`
and every on-line level-`m` object `A` at weight `β_j` (gap rows included with **no**
correction term — LEMMA SL-L1's load-bearing gap clause, `EFF.SIGMALAW.04`), the ledger
identity `Prnt_j(A) = u_j · Σ_m(R_m v(A))` holds with `u_j =
z_m^{−k_j·A_m}·ε_m(β_j)·U_m(β_j)` slot-constant, and `Σ_m` is a ring automorphism by the
`(EC-q)` eigen-coefficient law (`EFF.SIGMALAW.07`). Grade: **ACCEPTED 2/2 + CERTIFIED**
(`EFF.SIGMALAW.11` — six of six commit pins verified — and `.01`).

**What this `def` is and is not.** `SigmaLedgerLaw` packages exactly the three Σ-properties
the corollaries consume — injective, fixes `1`, multiplicative (F.15's `hmul` and F.16's
`hinj`/`h1`, at junction scope). SL-1's full quantifier lives at the C-side junction
instance, whose data (levels, letters `z_q`, characters, evaluators `H_q`/`P_q`) is tower
content: `EFF.SIGMALAW.03/.04 [supplied-by: chapter C]`. That instance is
**BLOCKED: GC-13** and is deliberately NOT stubbed as provable anywhere; only this carrier
declaration lands. *[repaired: A-W.1 bookkeeping]* the signed docstring's trailing "stub as
axiom with header per §12" is STRUCK — the carrier is a real `def`, per §12(b).

**The statement fence (the wrong-map lesson, `EFF.SIGMALAW.02`).** No F or C node may define
`Σ_m` as the bare interior twist σ′ (`z_q ↦ θ_q z_q`). The only sanctioned definition is the
corrected composite of the per-level twists by `ξ_q = χ_{q−1}^{γ_q}·z_{q−1}^{−e_{q−1}A_{q−1}}`
(F.18's `xiChar`); σ′ coincides with `Σ_m` exactly on involution geographies (SL-INVREC
218/218), which is why it survived 468 sealed rows, and the two machine-witnessed
non-involution separators are the refutation of record.

**DEPENDS, at GC-13(a) landed names** *[repaired: A-W.1 cross-chapter note 1]*: E.45/E.46
have landed (`Uniformity/ChapE/E45.lean`, `E46.lean`), so the E-side citation is
`Uniformity.Density.Ladder.ladderSigma` and `…ladderSigma_degree`. Per DECISION D-F3 **no F
signature references either name** — SIGMALAW has no σ-valued output, so a Lean dependency
would be manufactured; this is a citation-form upgrade only, and this file therefore does not
import chapter E.

*[repaired: A-W.1/F-D1]* `J.Σmap` → `J.sigmaMap` (three occurrences; F.14's field name).

Teeth: the sealed battery (6,970 samples, all preregistered families GREEN, all six teeth
rows CAUGHT) + SL-INVREC 218/218 — RECORDED at source; F.30 fires the `ξ₂ = θ₂⁻¹`
degeneration numerically. Signature byte-identical to the stage-0e gate
(`leanspec/Leanspec/ChapF.lean`, LeanspecF).
-/

namespace Uniformity.Density.Weld

/-- SL-1's Σ-properties package: what the corollaries consume from the corpus theorem. -/
def SigmaLedgerLaw {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) : Prop :=
  Function.Injective J.sigmaMap ∧ J.sigmaMap 1 = 1 ∧
    ∀ x y, J.sigmaMap (x * y) = J.sigmaMap x * J.sigmaMap y

end Uniformity.Density.Weld
