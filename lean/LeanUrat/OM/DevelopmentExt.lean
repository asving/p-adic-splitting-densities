/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Development
import LeanUrat.OM.UnramifiedBase

/-!
# `DevelopmentExt` — the φ-adic development over the UNRAMIFIED base ring `O″ = Oring` (P9, WAVE 1)

**SCAFFOLDING toward the order-≥2 residue-field-EXTENSION reader.** This is wave 1 of the P9
subsystem characterized in `uniform-rationality/notes/ORDER2_READER_BLUEPRINT_2026-07-14.md`; it is
NOT a finished reader and does NOT yet certify that anything read off the `O″`-development is `f`'s
genuine order-`≥2` residual (that faithfulness identification is the gating new-math target — see
`OPEN TARGET B.2` at the bottom of this file, and it is NOT built here).

## What this file DOES land (all core-only, no `sorry`/`axiom`)

`Development.develop` is already generic over *any* `CommRing` (see `LeanUrat/OM/Development.lean`),
so developing a polynomial over the level-N unramified base ring `O″ = UnramifiedBase.Oring p N g`
against a monic key `Φ : O″[X]` is literally `Development.develop Φ k h`. This file:

* `developExt` — a thin *named specialization* fixing the coefficient ring to `O″`, carrying the
  intent (φ-adic development of a box element `h : O″[X]` against a monic key `Φ : O″[X]`, `k`
  digits). Definitionally `Development.develop Φ k h`; it exists so downstream `O″`-reader code
  names the extension development explicitly rather than re-specializing `develop` at each site.
* `developExt_digit_degree` / `developExt_digit_natDegree` — the per-digit degree bounds transported
  to `O″` (degree `< Φ.degree`).
* `developExt_reassemble` — the reassembly `∑ j, developExt … j * Φ ^ j = h` for degree-bounded `h`.
* **`developExt_resHom_natural`** — the `O″`-development residue-naturality lemma (the analogue of
  `Development.develop_map` for the residue hom `resHom : O″ → resField`). This is Lemma B's *bare
  transport instance*: developing over `O″` then reducing mod `p` equals developing over the residue
  field `resField` of the reduced data. Proved as a direct instance of `Development.develop_map` at
  `f := resHom` (monicity of `Φ` supplies the `develop_map` hypothesis). It is EASY per the
  blueprint (§2 Lemma B, "the bare `develop_map` instance is EASY (~10 lines)").

## What this file DELIBERATELY does NOT do (the gating open content — wave 2+)

The residue-naturality lemma transports *digits*; it says NOTHING about the reduced digits BEING the
Montes order-`r` residual over the extension field. That identification —
"`resUnitResidue (digit.coeff 0)` computes the genuine order-`r` residual coefficient `R_r ∈
resField[X]`" — is the actual order-2 mathematics (blueprint §2 Lemma B point 1, budgeted 300+
lines, "the gating research result"). It is stated here ONLY as a doc target (`OPEN TARGET B.2`),
with no `sorry` and no proof obligation entering the build. Likewise the Teichmüller/Hensel key lift
(`liftKeyExt`, Lemma A) lives in a sibling file and is NOT consumed here.

Discipline: no `sorry`/`axiom`/`native_decide`. Imports `Development` + `UnramifiedBase` READ-ONLY;
this file NEVER edits `Development.lean`/`OMType.lean`/`Classifier.lean`/`UnramifiedBase.lean` (the
two-stream contention rule, `TWO_STREAM_INTERACTION_BLUEPRINT_2026-07-15.md` §2).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.DevelopmentExt

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The named `O″`-development

`O″ = UnramifiedBase.Oring p N g`. The development is the generic `Development.develop` at this
coefficient ring; `developExt` fixes it and carries intent, nothing more. -/

/-- **The φ-adic development over the unramified base ring `O″ = Oring p N g`.** For a monic key
`Φ : O″[X]` and a box element `h : O″[X]`, the first `k` φ-adic digits of `h` over `O″`. Definitionally
`Development.develop Φ k h` (the generic development at coefficient ring `O″`); named so the
order-`≥2` extension reader refers to "the `O″`-development" as a first-class object.

This is scaffolding: developing over `O″` (residue field `resField = F_{p^{deg g}}`) is what an
order-`≥2` Montes node must do INSTEAD of developing the original `f` over `ZMod (p^N)`. -/
def developExt (Φ : (UnramifiedBase.Oring p N g)[X]) (k : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    Fin k → (UnramifiedBase.Oring p N g)[X] :=
  Development.develop Φ k h

theorem developExt_def (Φ : (UnramifiedBase.Oring p N g)[X]) (k : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) :
    developExt p N g Φ k h = Development.develop Φ k h := rfl

/-! ## Digit degree bounds over `O″` (transported from `Development`) -/

/-- Each `O″`-development digit has degree strictly below `Φ.degree` (needs `O″` nontrivial, which
holds for `0 < g.natDegree`, `0 < N`; supplied as a typeclass hypothesis so the lemma is reusable
independent of how nontriviality is discharged). -/
theorem developExt_digit_degree [Nontrivial (UnramifiedBase.Oring p N g)]
    {Φ : (UnramifiedBase.Oring p N g)[X]} (hΦ : Φ.Monic) (k : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) (j : Fin k) :
    (developExt p N g Φ k h j).degree < Φ.degree :=
  Development.develop_digit_degree hΦ k h j

/-- `natDegree` form of the digit degree bound over `O″`. -/
theorem developExt_digit_natDegree [Nontrivial (UnramifiedBase.Oring p N g)]
    {Φ : (UnramifiedBase.Oring p N g)[X]} (hΦ : Φ.Monic) (hm0 : 0 < Φ.natDegree) (k : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) (j : Fin k) :
    (developExt p N g Φ k h j).natDegree < Φ.natDegree :=
  Development.develop_digit_natDegree hΦ hm0 k h j

/-- **Reassembly over `O″`**: for `h` of `natDegree < k · Φ.natDegree`, the first `k` `O″`-digits
reassemble to `h`. Transported from `Development.develop_reassemble`. -/
theorem developExt_reassemble {Φ : (UnramifiedBase.Oring p N g)[X]} (hΦ : Φ.Monic) (k : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) (hh : h.natDegree < k * Φ.natDegree) :
    ∑ j : Fin k, developExt p N g Φ k h j * Φ ^ (j : ℕ) = h :=
  Development.develop_reassemble hΦ k h hh

/-! ## Lemma B (bare instance): the `O″`-development residue-naturality lemma

The residue hom `resHom : O″ → resField` reduces mod `p`. Developing over `O″` then reducing equals
developing over `resField` of the reduced data. Direct instance of `Development.develop_map`. -/

/-- **`O″`-development residue naturality** (Lemma B, bare transport instance). For a monic key
`Φ : O″[X]`, mapping the `j`-th `O″`-digit of `h` down the residue hom `resHom : O″ → resField`
equals the `j`-th `(Φ.map resHom)`-adic digit of `h.map resHom` over the residue field:

`(developExt … Φ k h j).map resHom = Development.develop (Φ.map resHom) k (h.map resHom) j`.

This is the extension analogue of `Development.develop_map` at `f := resHom p N g hgm hN`, and holds
for exactly the same reason (`%ₘ`/`/ₘ` by a monic commute with `Polynomial.map`). It is the
*transport* half of the order-2 Lemma B; it does NOT by itself certify that the reduced digits are
`f`'s residual (see `OPEN TARGET B.2`). Core-only. -/
theorem developExt_resHom_natural (hgm : g.Monic) (hN : 0 < N)
    {Φ : (UnramifiedBase.Oring p N g)[X]} (hΦ : Φ.Monic) (k : ℕ)
    (h : (UnramifiedBase.Oring p N g)[X]) (j : Fin k) :
    (developExt p N g Φ k h j).map (UnramifiedBase.resHom p N g hgm hN)
      = Development.develop (Φ.map (UnramifiedBase.resHom p N g hgm hN)) k
          (h.map (UnramifiedBase.resHom p N g hgm hN)) j := by
  rw [developExt_def]
  exact Development.develop_map (UnramifiedBase.resHom p N g hgm hN) hΦ k h j

-- Footprint check: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms developExt_resHom_natural

/-! ## OPEN TARGET B.2 — residual-faithfulness identification (GATING NEW MATH, NOT built)

The reader (`ChildResidualExt.childResidualExt`) reads `resUnitResidue (digit.coeff 0)` off the
`O″`-development digits. To make it a genuine READER — i.e. to know it computes the Montes order-`r`
residual `R_r ∈ resField[X]` of `f` over the extension `resField`, not merely SOME `resField[X]` — one
needs, on TOP of the transport lemma above, the identification

  developExt-digit-constant-terms, reduced mod `p`, equal the abstract order-`r` residual coefficients
  (the `resField`-analogue of the `Fr = ZMod p` order-0/order-1 residual-correctness the project
  currently only ASSERTS via `boxCoeffData`/`residualPoly`, and which has NO proof for the extension
  `resField`).

Per the blueprint (§2 Lemma B, point 1) this is the true order-2 content, budgeted at 300+ lines and
flagged as the gating research risk. It is intentionally left as a documented target here (no `sorry`,
no build obligation). It is what wave 2 must supply for the ext reader to be called faithful. -/

end

end LeanUrat.OM.DevelopmentExt
