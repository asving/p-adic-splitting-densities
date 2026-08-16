/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F14
import Mathlib.Tactic.FieldSimp

/-!
# Uniformity.ChapF.F15 — SL-C1's core: the slot constant cancels and `δ = ρ / Σ(ρ)`

**Chapter F, NODE F.15** [lemma] (`blueprint/CHAP-F_weld_layer.md` §6), ENV-F1. COROLLARY
SL-C1 (`EFF.SIGMALAW.08`, "δ_j = ρ_j / Σ_m(ρ_j)"), transcribed at the abstraction of F.14's
`LedgerJunction`, with E10 #5's four-line derivation as the proof: both prints factor
through the slot constant `u j` by `hledger`, `u j` cancels — "which is the point of its
being slot-constant" — and what is left is `(ρ·x/x) · Σ(x)/Σ(ρx) = ρ/Σ(ρ)`.

**The two statement fences of this node.**

* The `hmul` hypothesis is PER-PAIR (`Σ (ρ·x) = Σ ρ · Σ x` for this one pair), not "`Σ` is a
  ring automorphism". The automorphism property is the `(EC-q)` perimeter's content
  (`EFF.SIGMALAW.07`, the hostile-pass-derived law) and lives at F.17's instance level;
  taking it per-pair keeps this abstract lemma exactly as strong as the derivation needs.
* The `δ_j` normalization is the MULTIPLIED form `(Prnt j C · (ρ·x)) / (Prnt j P · x)`, not a
  division tower — it avoids `0/0` junk while staying literally equivalent on these
  hypotheses. Do not "simplify" it back.

*[repaired: A-W.1/F-D1]* `J.Σmap` → `J.sigmaMap` (F.14's field, part of the type) and the two
non-vanishing binders `hΣx`/`hΣρ` → `hSigmax`/`hSigmarho` (binder names only). The `Σ` of the
source's `(Σ-LEDGER)` display stays `Σ` in prose.

Was an `axiom` stub at stage 0e; PROVED here. The teeth are SL-DELTA (1,414 leak-free rows
keying the element identity directly), RECORDED at source; the abstract instance re-fires at
F.30. Signature byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`,
LeanspecF).
-/

namespace Uniformity.Density.Weld

/-- SL-C1's core (`EFF.SIGMALAW.08`): at a ledger junction, the slot constant `u j` cancels
out of the ledger ratio, which therefore equals `ρ / Σ(ρ)` — depending on the reads only
through the unit `ρ` relating them. -/
theorem LedgerJunction.delta_eq {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) (j : ι) (C P : α) (ρ : Kˣ)
    (hx : J.read j C ≠ 0) (hP : J.read j P = (ρ : K) * J.read j C)
    (hmul : J.sigmaMap ((ρ : K) * J.read j C)
      = J.sigmaMap (ρ : K) * J.sigmaMap (J.read j C))
    (hSigmax : J.sigmaMap (J.read j C) ≠ 0) (hSigmarho : J.sigmaMap (ρ : K) ≠ 0) :
    (J.Prnt j C * ((ρ : K) * J.read j C)) / (J.Prnt j P * J.read j C)
      = (ρ : K) / J.sigmaMap (ρ : K) := by
  have hu : ((J.u j : Kˣ) : K) ≠ 0 := (J.u j).ne_zero
  have hPrntC : J.Prnt j C = (J.u j : K) * J.sigmaMap (J.read j C) := J.hledger j C
  have hPrntP : J.Prnt j P
      = (J.u j : K) * (J.sigmaMap (ρ : K) * J.sigmaMap (J.read j C)) := by
    rw [J.hledger j P, hP, hmul]
  rw [hPrntC, hPrntP]
  field_simp

end Uniformity.Density.Weld
