/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.OMType
import LeanUrat.OM.UnramifiedBase

/-!
# `OrderTwoContext` — the residue-field-EXTENSION OM-context TYPE (INTERFACE STUB ONLY)

**INTERFACE STUB ONLY.** The `M5.OMType` built here, `fChildCtxExt`, has `Rr := 0` and `dr := 0`
(content-free, EXACTLY like the old f-blind `Classifier.childCtxOfSize` stub — `Rr := 0`). It is
**NOT an order-2 reader** and **reads NOTHING from `f`.** It only surfaces the one structural fact
that a residue-field-EXTENSION context — one whose top residue field `Fr` is a *genuine field*
`UnramifiedBase.resField p N g` of cardinality `p^{deg g}`, an honest degree-`deg g` extension of
`ZMod p`, rather than `ZMod p` itself — is *constructible as an `M5.OMType`* (its proof obligations
`hResidueDeg`, `hResidualDeg`, `hDrLeCs` all discharge for the extension `Fr`).

The actual order-`≥ 2` genuine reader (`childResidualExt`, the `resField[X]`-valued replacement for
`Classifier.childResidual`, wired into a SEPARATE `classifyGenuineExtAux` recursion) needs the two
new-math lemmas characterized in
`uniform-rationality/notes/ORDER2_READER_BLUEPRINT_2026-07-14.md`
(a Teichmüller/Hensel lift `ψ : Fr[X] → g : (ZMod p^N)[X]` with `ḡ` irreducible, and an
`O″`-development residue-naturality analogue of `Development.develop_map`). Those lemmas, and the
reader, **do not exist yet.**

Why this leaf is deliberately kept OFF `Classifier.lean`: the current genuine reader
`Classifier.classifyGenuineAux` develops the ORIGINAL `f` against `liftKey ψ` at every depth with
`Fr := ZMod p` fixed DEFINITIONALLY (its `ch.P : (fChildCtx …).Fr[X]` is a `(ZMod p)[X]` with no
type transport). Faithfulness of `classifyGenuine` therefore holds only at ORDER `≤ 1` (single-slope
tame tower, `Fr = ZMod p`). The genuine order-`≥ 2` Montes descent needs the residue-field-EXTENSION
reader, a LARGE NEW SUBSYSTEM — not a slice of `Classifier`. This module imports ONLY `OMType` +
`UnramifiedBase` (never `Classifier`), keeping the new build edge off the widely-imported
`Classifier`.

The ONE genuine content of this leaf is `card_Fr_fChildCtxExt`: the extension field has the right
cardinality `p^{deg g}` (via `UnramifiedBase.card_resField`).

Discipline: no `sorry`/`axiom`/`native_decide`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.OrderTwoContext

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## Instance helpers for the extension residue field `Fr := resField p N g`

`resField p N g hN = AdjoinRoot (gbar p N g hN)` over `ZMod p`. To carry it as `M5.OMType.Fr` we
need it as a genuine `Field` (from `ḡ` irreducible, `AdjoinRoot.instField`) and `Finite` (from its
finite cardinality `p^{deg g}`), plus the finrank tie for `hResidueDeg`. The `Field`/`Algebra`
instances resolve CANONICALLY once `Fact (Irreducible ḡ)` is in scope (so the module structure
`Module.finrank` sees is the native `AdjoinRoot` one — the `hResidueDeg` obligation and the finrank
lemma below then share the same instance chain, avoiding a `CommRing`/`Field` diamond). -/

/-- The extension residue field `Fr` is `Finite` (card `p^{deg g}` is nonzero), under
`Fact (Irreducible ḡ)`. Provided as a local instance-supplier for the OMType `finite_Fr` field. -/
theorem finite_resField (hgm : g.Monic) (hN : 0 < N)
    [Fact (Irreducible (UnramifiedBase.gbar p N g hN))]
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN)) :
    Finite (UnramifiedBase.resField p N g hN) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpos : 0 < p ^ g.natDegree := pow_pos hp.out.pos _
  exact Nat.finite_of_card_ne_zero
    (by rw [UnramifiedBase.card_resField p N g hgm hN hgirr]; exact hpos.ne')

/-- **The A0 tie for the extension `Fr`**: `Module.finrank (ZMod p) (resField …) = g.natDegree`.
`resField = AdjoinRoot ḡ` with `ḡ` of degree `g.natDegree` over the field `ZMod p`, so its power
basis has dimension `ḡ.natDegree = g.natDegree` (`PowerBasis.finrank` on `AdjoinRoot.powerBasis`).
This is the fact that discharges `OMType.hResidueDeg` when we set `δ := g.natDegree`,
`F0 := ZMod p`. -/
theorem finrank_resField (hgm : g.Monic) (hN : 0 < N)
    [Fact (Irreducible (UnramifiedBase.gbar p N g hN))] :
    Module.finrank (ZMod p) (UnramifiedBase.resField p N g hN) = g.natDegree := by
  have hne : (UnramifiedBase.gbar p N g hN) ≠ 0 := (UnramifiedBase.monic_gbar p N g hgm hN).ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne)]
  change (UnramifiedBase.gbar p N g hN).natDegree = g.natDegree
  exact UnramifiedBase.natDegree_gbar p N g hgm hN

/-! ## The residue-field-EXTENSION context (INTERFACE STUB — `Rr := 0`, reads nothing) -/

/-- **INTERFACE STUB ONLY** — the residue-field-EXTENSION OM-context TYPE.

`M5.OMType` with `F0 := ZMod p`, `Fr := UnramifiedBase.resField p N g` (a *genuine field* of card
`p^{deg g}`, an honest degree-`deg g` extension of `ZMod p`), order `r`, cluster size `s`, and
extension degree `δ := g.natDegree = [Fr : F₀]` (the composite residue degree, carried through
`hResidueDeg` via the finrank tie).

`Rr := 0` and `dr := 0` — **content-free, EXACTLY like the old `childCtxOfSize` stub.** This is
**NOT an order-2 reader** and **reads NOTHING from `f`.** It only witnesses that the extension-field
context is *constructible as an `M5.OMType`*. The genuine reader (`childResidualExt`) does not exist
yet — see `ORDER2_READER_BLUEPRINT_2026-07-14.md`.

Note on `δ`: `hResidueDeg` requires `δ = finrank (ZMod p) Fr`, and `finrank (ZMod p) resField
= g.natDegree` (`finrank_resField`), so `δ := g.natDegree` is the honest, dischargeable value at
this single unramified level. A general tower-composite `[F_r : F_p] = ∏ deg` would only be produced
by a genuine multi-level extension reader; keeping `δ` faithful to the finrank here is deliberate —
an inflated `δ` would break `hResidueDeg`. -/
def fChildCtxExt (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN)) : M5.OMType :=
  haveI : Fact (Irreducible (UnramifiedBase.gbar p N g hN)) := ⟨hgirr⟩
  -- With `Fact (Irreducible ḡ)` in scope, `Field`/`Algebra` on `resField = AdjoinRoot ḡ` resolve
  -- canonically (native `AdjoinRoot` chain), so the `hResidueDeg` finrank matches `finrank_resField`.
  letI : Finite (UnramifiedBase.resField p N g hN) := finite_resField p N g hgm hN hgirr
  { order := r
    F0 := ZMod p
    Fr := UnramifiedBase.resField p N g hN
    δ := g.natDegree
    Nr := ⟨0, fun _ => 0, fun _ => false⟩
    Rr := 0
    dr := 0
    keyDeg := 0
    cs := s
    hResidueDeg := (finrank_resField p N g hgm hN).symm
    hResidualDeg := by simp
    hDrLeCs := Nat.zero_le _ }

/-- `clusterSize (fChildCtxExt …) = s` (by `rfl`, `cs := s`). Matches the budget-invariant shape of
`childCtxOfSize`; carried here only so the stub is a drop-in OM-context shape at the type level. -/
theorem clusterSize_fChildCtxExt (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN)) :
    M5.clusterSize (fChildCtxExt p N g r s hgm hN hgirr) = s := rfl

/-- **THE ONE GENUINE CONTENT**: the extension context's residue field `Fr` has the right
cardinality, `Nat.card Fr = p ^ g.natDegree`.

This is the honest fact the interface stub surfaces — that a residue-field EXTENSION (a genuine
finite field of card `p^{deg g}`, not `ZMod p`) *is* the top field of a constructible `M5.OMType`.
Proved via `UnramifiedBase.card_resField`. (Everything else about `fChildCtxExt` is content-free:
`Rr := 0`, reads nothing from `f`.)

The card is `p ^ g.natDegree`, matching `δ = g.natDegree = finrank (ZMod p) Fr`. A tower-composite
card `p ^ (∏ deg)` across several extension levels is what only a genuine multi-level extension
reader would produce; a single-level stub has exactly this `p ^ deg g`. -/
theorem card_Fr_fChildCtxExt (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN)) :
    Nat.card (fChildCtxExt p N g r s hgm hN hgirr).Fr = p ^ g.natDegree :=
  UnramifiedBase.card_resField p N g hgm hN hgirr

-- Footprint check: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms card_Fr_fChildCtxExt

end

end LeanUrat.OM.OrderTwoContext
