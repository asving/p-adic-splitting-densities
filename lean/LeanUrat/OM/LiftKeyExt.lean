/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.UnramifiedBase

/-!
# `LiftKeyExt` — Lemma A: the key lift `resField[X] → O″[X]` (P9, WAVE 1, surjInv/Hensel route)

**Lemma A of the order-≥2 reader subsystem** (`ORDER2_READER_BLUEPRINT_2026-07-14.md` §2 Lemma A).
`Classifier.liftKey` lifts `ψ ∈ (ZMod p)[X]` to `(ZMod (p^N))[X]` coefficientwise by the trivial
nat-representative section. The extension reader instead needs to lift a monic residual factor
`Ψ ∈ resField[X]` (coefficients in the EXTENSION residue field `resField = O″/(p) = F_{p^{deg g}}`)
to a monic key `O″[X]` that reduces back to `Ψ`.

## Route (blueprint §2 Lemma A, the LIKELY-cheaper "surjInv/Hensel" route)

Lift each coefficient by ANY set-section of the surjection `resHom : O″ → resField`
(`UnramifiedBase.resHom_surjective` + `Function.surjInv`), and take `X^d` for the leading term so
monicity and the degree tie are free. `liftKeyExt_reduces` then follows coefficientwise from
`resHom (resSection c) = c` (`surjInv_eq`) together with `Monic.as_sum` for the monic `Ψ`. The
non-multiplicative section is fine here: the only property the reader needs is that the reduction
recovers `Ψ` (which this gives), NOT Teichmüller multiplicativity (the HARD route, avoided —
blueprint §2, "the Teichmüller route needs the Witt iso first and is HARD (500+ lines) — avoid
unless multiplicativity is later required").

## What lands (core-only, no `sorry`/`axiom`)

* `resSection : resField → O″` — a chosen set-section of `resHom` (`resHom ∘ resSection = id`).
* `liftKeyExt : resField[X] → O″[X]` — `X^(deg Ψ) + ∑_{i<deg Ψ} C (resSection (Ψ.coeff i)) · X^i`.
* `liftKeyExt_monic` — `(liftKeyExt Ψ).Monic` (by `monic_X_pow_add`, as for `liftKey`).
* `liftKeyExt_natDegree` — `(liftKeyExt Ψ).natDegree = Ψ.natDegree`.
* **`liftKeyExt_reduces`** — `(liftKeyExt Ψ).map resHom = Ψ` for MONIC `Ψ` (the `resHom`-analogue of
  `Classifier.liftKey_map`; the genuine content of Lemma A on the surjInv route). Requires `Ψ` monic
  so `Monic.as_sum` puts it in the matching `X^d + ∑ C(coeff) X^i` shape.

## Honest scope

This is the surjInv route: the section is a bare right-inverse, so `liftKeyExt` is NOT
multiplicative and NOT the Teichmüller lift. That is exactly the blueprint's chosen route
(multiplicativity is not needed for the reader). What is NOT built here: wiring `liftKeyExt` into
`childResidualExt` / `classifyGenuineExtAux` (the recursion is wave 2, blueprint §3), and the
residual-faithfulness identification (`OPEN TARGET B.2` in `DevelopmentExt.lean`).

Discipline: no `sorry`/`axiom`/`native_decide`. Imports `UnramifiedBase` READ-ONLY; edits no
existing file (two-stream contention rule).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.LiftKeyExt

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The set-section `resField → O″` of `resHom` -/

/-- A chosen set-section of the residue surjection `resHom : O″ → resField`, via
`Function.surjInv` of `UnramifiedBase.resHom_surjective`. Right-inverse only (`resHom ∘ resSection =
id`, `resSection_spec`); NOT a ring hom, NOT multiplicative — the surjInv/Hensel route (blueprint §2
Lemma A), which suffices for the reader (no Teichmüller multiplicativity needed). -/
def resSection (hgm : g.Monic) (hN : 0 < N) :
    UnramifiedBase.resField p N g hN → UnramifiedBase.Oring p N g :=
  Function.surjInv (UnramifiedBase.resHom_surjective p N g hgm hN)

/-- `resHom (resSection c) = c`: the section is a right-inverse (`Function.surjInv_eq`). -/
@[simp] theorem resSection_spec (hgm : g.Monic) (hN : 0 < N)
    (c : UnramifiedBase.resField p N g hN) :
    UnramifiedBase.resHom p N g hgm hN (resSection p N g hgm hN c) = c :=
  Function.surjInv_eq (UnramifiedBase.resHom_surjective p N g hgm hN) c

/-! ## The key lift `liftKeyExt : resField[X] → O″[X]` -/

/-- **Lemma A: the key lift.** Lift a residual factor `Ψ ∈ resField[X]` to a monic key over the
unramified base ring `O″ = Oring p N g`:
`X^(deg Ψ) + ∑_{i<deg Ψ} C (resSection (Ψ.coeff i)) · X^i`. Extension analogue of
`Classifier.liftKey` (there over the trivial nat-representative section `ZMod p → ZMod (p^N)`; here
over the surjInv section `resField → O″`). -/
def liftKeyExt (hgm : g.Monic) (hN : 0 < N) (Ψ : (UnramifiedBase.resField p N g hN)[X]) :
    (UnramifiedBase.Oring p N g)[X] :=
  Polynomial.X ^ Ψ.natDegree +
    ∑ i ∈ Finset.range Ψ.natDegree,
      Polynomial.C (resSection p N g hgm hN (Ψ.coeff i)) * Polynomial.X ^ i

/-- **`liftKeyExt` is monic** (of degree `Ψ.natDegree`): `X^d + (a sum of degree < d)`. Same
`monic_X_pow_add` argument as `Classifier.liftKey_monic`. -/
theorem liftKeyExt_monic (hgm : g.Monic) (hN : 0 < N) (Ψ : (UnramifiedBase.resField p N g hN)[X]) :
    (liftKeyExt p N g hgm hN Ψ).Monic := by
  apply Polynomial.monic_X_pow_add
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
  intro i hi
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _)
    (Nat.cast_lt.2 (Finset.mem_range.mp hi))

/-- The lifted sum tail has degree `< Ψ.natDegree` (extracted for reuse). -/
theorem liftKeyExt_tail_degree_lt (hgm : g.Monic) (hN : 0 < N)
    (Ψ : (UnramifiedBase.resField p N g hN)[X]) :
    (∑ i ∈ Finset.range Ψ.natDegree,
        Polynomial.C (resSection p N g hgm hN (Ψ.coeff i)) * Polynomial.X ^ i).degree
      < (Ψ.natDegree : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
  intro i hi
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _)
    (Nat.cast_lt.2 (Finset.mem_range.mp hi))

/-- **`liftKeyExt` preserves the degree**: `(liftKeyExt Ψ).natDegree = Ψ.natDegree`. From the
`X^d + (deg < d)` shape (`natDegree_X_pow_add`-style, via the tail bound). Needs `O″` nontrivial
(`degree_X_pow` collapses over the trivial ring); supplied as a typeclass hypothesis, discharged for
`0 < g.natDegree`, `0 < N` via `UnramifiedBase.nontrivial_Oring`. -/
theorem liftKeyExt_natDegree [Nontrivial (UnramifiedBase.Oring p N g)] (hgm : g.Monic) (hN : 0 < N)
    (Ψ : (UnramifiedBase.resField p N g hN)[X]) :
    (liftKeyExt p N g hgm hN Ψ).natDegree = Ψ.natDegree := by
  rw [liftKeyExt]
  have hlt : (∑ i ∈ Finset.range Ψ.natDegree,
        Polynomial.C (resSection p N g hgm hN (Ψ.coeff i)) * Polynomial.X ^ i).degree
      < (Polynomial.X ^ Ψ.natDegree : (UnramifiedBase.Oring p N g)[X]).degree := by
    rw [Polynomial.degree_X_pow]
    exact liftKeyExt_tail_degree_lt p N g hgm hN Ψ
  refine Polynomial.natDegree_eq_of_degree_eq_some ?_
  rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]

/-- **`liftKeyExt_reduces`** (the genuine content of Lemma A on the surjInv route): mapping the lift
down the residue hom `resHom` recovers `Ψ`, for MONIC `Ψ`:
`(liftKeyExt Ψ).map resHom = Ψ`.

Proof: `Polynomial.map` distributes over the `X^d + ∑ C(resSection cᵢ) X^i` shape; each
`resHom (resSection cᵢ) = cᵢ` (`resSection_spec`); the result is `X^d + ∑ C(Ψ.coeff i) X^i`, which
equals `Ψ` for monic `Ψ` (`Monic.as_sum`). The `resHom`-analogue of `Classifier.liftKey_map`. -/
theorem liftKeyExt_reduces (hgm : g.Monic) (hN : 0 < N)
    {Ψ : (UnramifiedBase.resField p N g hN)[X]} (hΨ : Ψ.Monic) :
    (liftKeyExt p N g hgm hN Ψ).map (UnramifiedBase.resHom p N g hgm hN) = Ψ := by
  rw [liftKeyExt, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  have hmapsum : (∑ i ∈ Finset.range Ψ.natDegree,
        (Polynomial.C (resSection p N g hgm hN (Ψ.coeff i)) * Polynomial.X ^ i).map
          (UnramifiedBase.resHom p N g hgm hN))
      = ∑ i ∈ Finset.range Ψ.natDegree, Polynomial.C (Ψ.coeff i) * Polynomial.X ^ i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      resSection_spec]
  rw [hmapsum]
  exact (Monic.as_sum hΨ).symm

-- Footprint check: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms liftKeyExt_reduces

end

end LeanUrat.OM.LiftKeyExt
