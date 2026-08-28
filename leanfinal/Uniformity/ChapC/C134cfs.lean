/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh15

/-!
# Uniformity.ChapC.C134cfs — `[CFS 2026-08-28]`: the C.35 BlockFrontier-family
unconditionalization sweep (UNIT CFS)

The dv-graded one-slope Hensel engine closed F1.H3 tonight:
`C133mh15.blockFrontier_of_context : BlockContext L f → BlockFrontier L f`
(footprint: Lean core + the allowlisted C.33 dissection cite `exists_dvDissection`).
This file lands the unconditional forms of every corpus row that carried a
`BlockFrontier`-shaped hypothesis and is a genuine projection of the engine's export.

## Rows landed here (the engine-application set)

* **F1.1 `blockFactor_spec`** — the signed four-conjunct companion of C.35
  (`leanspec/Leanspec/ChapC.lean:1608-1613`), conclusion BYTE-AS-IS, fired from
  `BlockContext` through `C133mh15.blockFrontier_of_context` +
  `blockFactor_spec_of_frontier` (`C35.lean:310-320`).  **Binder delta vs the signed
  form: ONE extra hypothesis `hh : 0 < F.h`** — the engine's frame-nondegeneracy
  entry (the `h = 0` degenerate frame is formally admitted by `KeyFrame`, C01.lean:84-86,
  and is NOT excluded by `LevelDatum.hκ`, which `h = 0` satisfies vacuously); the
  corpus frame has `1 ≤ h` (C01 docstring).  Recorded, not hidden: this is the honest
  unconditional twin, superseding the carried-`hfr` packaging form
  `blockFactor_spec_of_frontier` for every `BlockContext` consumer.
* **Projections** `hasLabel_blockFactor`, `blockFactor_dvd`, `blockDeg_eq`, `mult₂_pos` —
  the four clauses as consumer-facing reads.  `blockDeg_eq` is the RIDER-DISCHARGED twin
  of the landed re-signed C.64 (`C150rb1.lean:135-141` / `C64.blockDeg_eq_resigned`,
  amendment A-C.10): the `hlab`/`hdvd` riders those forms thread are now produced from
  `hctx` alone, which is exactly the `read_form` demand of
  `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md:51`.
* **Rider supplier** `keyDeg₁_dvd_blockFactor_natDegree` — the `D′ ∣ deg (blockFactor L f)`
  rider (the A-C.20 degree pin), read off the frontier witness via
  `blockFactor_eq_of_frontier`.

## Consistency note (why landing `blockDeg_eq` from bare `hctx` is NOT the refuted law)

`C64.blockDegEq_false` and `C67.multiplicity_tie` refuted the naked degree law for the
pre-A-C.20 LEAKY selector (`blockFactorLeaky`/`mult₂Leaky` — `C64.lean:78`, closed-form
statement, and `C67.lean:243` pin the LEAKY choice).  The A-C.20 re-signed `blockFactor`
is degree-pinned (`(F.e₁ * F.f₁) ∣ natDegree` inside the selector), and at the very
`(s2Frame, L₀, g₀)` probe the engine now produces a labelled QUADRATIC block inside the
cubic (`2 = 2·1` holds).  The refutation records stand, against the leaky pair only.

## Rows recorded BLOCKED-BECAUSE (do-not-force; exact missing premise per row)

The exported `BlockFrontier` is existence + maximality + the `D′` rider ONLY — the
engine's internal split data (complement factor, its non-`r`-divisible residual, the
point-sided below/other-slope product) is deliberately dropped at the export.  Hence:

* **F1.2 `block_complement_notdvd`** (leanspec:1614-1622): needs an exported
  context-split theorem (F1.H1 consumer form: `f = blockFactor · g₂ · Wf` with
  `¬ r ∣ dvResPoly g₂` and `Wf` point-sided) — the data lives INSIDE
  `C133mh14.blockFrontier_of_context_of_theoremA`'s proof (steps 3-6) but is not exported.
* **F1.3 `dv2Supp_translation`**: needs F1.2 + the no-interaction lemma
  (`dv2Pin_mul_complement`, plan sizing 70-120 lines).
* **F1.4 `dv2ResPoly_scalar`**, **F1.5 `dv2ResPoly_radical_eq`**: need F1.3 (+ cocycle
  telescope resp. unit cancellation).
* **F1.6 `mult₂_readable`**, **F1.7 `dv2_length_sum`**: need F1.3 resp. F1.6.
* **F1.8 `level2_peel`**: needs F1.1-F1.2 + C.61 (the C.27→C.59 chain, still open).
* **signed C.34 `exists_dv_residual_dissection`** (leanspec:1562-1580; conditional
  carrier `exists_dv_residual_dissection_of_frontier`, `C34.lean:278`): its `hex` leg
  needs Theorem A at the bare pure `g`, whose entry rider `(F.e₁ * F.f₁) ∣ g.natDegree`
  (`C133mh14.lean:269`) is ABSENT from the signed premises (and genuinely can fail for
  pure `g` — C35b's labelled cubic); its `hsep` leg (uniqueness of the split at pure `g`)
  has NO landed supplier — `C133mh13.theoremC_placement` proves maximality inside a
  squarefree `BlockContext` `f`, not two-split separation at a bare pure `g`.

## Out of scope (different frontier family)

`towerLocus_fibration_of_frontier` (`C53.lean:312`) carries `BudgetBoxRead` — the
C.52/C.53 budget-box frontier, closed separately by the dv-engine chain
(`towerLocus_iff_budget`); not a `BlockFrontier` carrier.

No carriers exist outside chapter C (`ChapA/B/D/E/G` grep: prose mentions only, E23/E51).

## Status

Sorry-free.  Axiom footprint of every theorem below: Lean core
`{propext, Classical.choice, Quot.sound}` + the allowlisted cite
`Uniformity.Density.Tower.exists_dvDissection` (inherited once, through
`C133mh15.blockFrontier_of_context`).  No new axiom; no statement edits to landed files.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C134cfs

open Polynomial IsLocalRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-! ## Row F1.1 — the signed `blockFactor_spec`, unconditional (modulo `hh`) -/

/-- ★ **Row F1.1 — NODE C.35's signed `blockFactor_spec`, UNCONDITIONAL.**  The signed
four-conjunct conclusion (leanspec `ChapC.lean:1608-1613`, byte-as-is) fires from
`BlockContext` alone through the dv-graded one-slope Hensel engine
(`C133mh15.blockFrontier_of_context`) and the landed packaging
(`blockFactor_spec_of_frontier`).  Binder delta vs the signed form: the single extra
hypothesis `hh : 0 < F.h` (frame nondegeneracy; see header). -/
theorem blockFactor_spec {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f ∧ 0 < mult₂ L f :=
  blockFactor_spec_of_frontier L hπ (C133mh15.blockFrontier_of_context L hπ hh hctx)

/-! ## The four clauses as consumer-facing projections -/

/-- Clause 1: the block is genuinely `(λ, r)`-labelled, from the context alone. -/
theorem hasLabel_blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    HasLabel L (blockFactor L f) :=
  (blockFactor_spec L hπ hh hctx).1

/-- Clause 2: the block divides `f`, from the context alone. -/
theorem blockFactor_dvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    blockFactor L f ∣ f :=
  (blockFactor_spec L hπ hh hctx).2.1

/-- Clause 3 = **the rider-discharged C.64 `blockDeg_eq`**: the exact block degree law
from the context alone.  Supersedes threading the `hlab`/`hdvd` riders of the landed
re-signed form (`C150rb1.lean:135` / `C64.blockDeg_eq_resigned`) for every
`BlockContext` consumer, and meets GC13's `read_form` demand
(`GC13_BRIDGE_PLAN_2026-08-25.md:51`).  NOT the refuted naked law: that record
(`C64.blockDegEq_false`) is against the pre-A-C.20 LEAKY selector — see header. -/
theorem blockDeg_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f :=
  (blockFactor_spec L hπ hh hctx).2.2.1

/-- Clause 4: positive multiplicity, from the context alone. -/
theorem mult₂_pos {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    0 < mult₂ L f :=
  (blockFactor_spec L hπ hh hctx).2.2.2

/-! ## The A-C.20 degree-pin rider, supplied from the context -/

/-- **The `D′ ∣ deg` rider supplier**: the block's degree is divisible by
`D′ = e₁f₁`, from the context alone — the exact rider that the protected-shape
consumers (re-signed C.64, C.48's template) thread as `hdvd`.  Read off the frontier
witness via the choice pin `blockFactor_eq_of_frontier`. -/
theorem keyDeg₁_dvd_blockFactor_natDegree {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    (F.e₁ * F.f₁) ∣ (blockFactor L f).natDegree := by
  obtain ⟨fS, hlab, hdvdf, hdeg, hmax⟩ := C133mh15.blockFrontier_of_context L hπ hh hctx
  rw [blockFactor_eq_of_frontier L hlab hdeg hdvdf hmax]
  exact hdeg

end Uniformity.Density.Tower.C134cfs

/-! ## AxCheck footer — every footprint must be Lean core + (at most) the allowlisted
`exists_dvDissection` cite -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134cfs.blockFactor_spec
#print axioms Uniformity.Density.Tower.C134cfs.hasLabel_blockFactor
#print axioms Uniformity.Density.Tower.C134cfs.blockFactor_dvd
#print axioms Uniformity.Density.Tower.C134cfs.blockDeg_eq
#print axioms Uniformity.Density.Tower.C134cfs.mult₂_pos
#print axioms Uniformity.Density.Tower.C134cfs.keyDeg₁_dvd_blockFactor_natDegree

end AxCheck
