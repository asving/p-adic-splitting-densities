/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D13

/-!
# Uniformity.ChapD.D16 — `Wfloor`, the level-1 telescope exponent

**Chapter D, NODE D.16** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1 gauge
layer; amendments A-1 and A-D.1 govern — neither re-signs this node, so the SIGNATURE below is
the one signed at composition and re-stubbed at stage 0e in `leanspec/Leanspec/ChapD.lean`, whose
`Wfloor` body is reused here byte-for-byte). ENV-D1 — the arithmetic arena: pure `ℕ`/`ℤ`, no `O`,
no polynomials. One signed declaration.

*The level-1 telescope exponent.* `Wfloor e₁ h u₂ f₂ t := (f₂ − t) * iexp e₁ h u₂ / e₁ : ℕ` — the
corpus's `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` (`EFF.T1.10`). **A definition only.** The law it exists for,
`ϑ_{1,f₂−t} = η^{W(t)}` — "the exponent has the displayed positive sign" — is NODE D.18, and is
NOT asserted here; this node contributes nothing but the arithmetic of the exponent.

## Reading the three index conventions (they are easy to conflate, so they are spelled)

* `u₂ : ℤ` — a HEIGHT, hence integral, and fed to D.13's `iexp`. Consumers that carry `u₂ : ℕ`
  (D.28 does) must supply the cast `(u₂ : ℤ)`; that is defect D-D7(i), repaired at D.28's
  signature and recorded here at the definition it bites.
* `f₂ t : ℕ` — the SLOT indices. The definition is written in `t`, but the corpus's telescope
  runs in `s := f₂ − t`: `Wfloor` is the `t`-keyed spelling of the `s`-keyed floor
  `⌊s·i(u₂)/e₁⌋`. The two frames below execute exactly that reconciliation (the `s`-table and the
  `t`-table of the same frame, reversed against each other).
* `ℕ`-subtraction. `f₂ − t` is the corpus's `s = f₂ − t ≥ 0`, and every consumer has `t < f₂` in
  scope, so the truncation branch `t ≥ f₂` (where `f₂ − t = 0` and hence `Wfloor = 0`) is JUNK
  that no lemma of this chapter reads. Noted rather than fenced by a hypothesis: the blueprint
  signs the definition total.

## The A-D.1 gate-writing rider, honoured in the executed frames below

`iexp` is NOT `decide`-reducible (defect D-D1, recorded at its source in D.13: `(h : ZMod e₁)⁻¹`
unfolds to `ZMod.inv`, which routes through `Nat.gcdA`/`Nat.xgcd` and does not kernel-reduce), so
`Wfloor` inherits that: **a bare `decide` on any row mentioning `Wfloor` is a compile error, not
a style choice.** Both frames below therefore reduce before they decide —

* the `h = 1` frame (D.65 leg 1, `e₁ = 2, u₂ = 3, f₂ = 3`) through D.13's PROVED `iexp_one`;
* the `h > 1` frame FRAME-H2 (D.66 leg 5, `e₁ = 3, h = 2, u₂ = 1, f₂ = 4`) through D.13's PROVED
  `iexp_eq_of_inv` with the inverse `c = 2` supplied as DATA and its defining equation
  `((2 : ℕ) : ZMod 3) * 2 = 1` decided inline.

FRAME-H2 is the chapter's ONLY `Wfloor` table with `i(u₂) ≠ 1` (here `i(1) = 2`), which is what
makes it — and not the `h = 1` frame — able to kill the misindexed-telescope mutant in the case
where the step is not a single unit. No `native_decide` anywhere.

DEPENDS: D.13 (`iexp`, `iexp_one`, `iexp_eq_of_inv`). No mathlib lemma: the node is definitional.

SOURCE: `EFF.T1.10` (`W(t) = ⌊(f₂−t)i(u₂)/e₁⌋`, `ϑ_{1,f₂−t} = η^{W(t)}`, "The exponent has the
displayed positive sign").

**TEETH.** the wrong-sign tooth → D.18 (the law) + gates D.65/D.66; the misindexed-telescope
tooth → the slot table, executed below at both frames.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only). **Flagged for human review** (definition faithfulness;
parent CLAUDE.md trust boundary): the three index conventions above are the whole content of this
node, and Lean checks none of them.
-/

namespace Uniformity.Density.Gauge

/-- **D.16 — the level-1 telescope exponent.** `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` (`EFF.T1.10`).
`u₂` is a height (hence `ℤ`); `f₂`, `t` are slot indices, and `f₂ - t` is `ℕ`-subtraction — the
corpus's `s = f₂ − t ≥ 0`, whose truncation branch `t ≥ f₂` is junk no consumer reads.  The law
`ϑ_{1,f₂−t} = η^{W(t)}` is D.18, not this node. -/
def Wfloor (e₁ h : ℕ) (u₂ : ℤ) (f₂ t : ℕ) : ℕ := (f₂ - t) * iexp e₁ h u₂ / e₁

end Uniformity.Density.Gauge

/-! ## The executed frames (A-D.1 gate-writing rider: `simp only [...]; decide`, never bare) -/

section Frames

open Uniformity.Density.Gauge

/-- D.65 leg 1, the `s`-keyed floor at `e₁ = 2, h = 1, u₂ = 3`: `⌊s·i(3)/2⌋ = (0,0,1,1)`. -/
example : (List.range 4).map (fun s => s * iexp 2 1 3 / 2) = [0, 0, 1, 1] := by
  simp only [iexp_one]; decide

/-- D.65 leg 1, the same table through `Wfloor` at `f₂ = 3` — the `t`-keyed spelling, so the
`s`-table read backwards from `s = f₂ − t`. -/
example : (List.range 3).map (fun t => Wfloor 2 1 3 3 t) = [1, 1, 0] := by
  simp only [Wfloor, iexp_one]; decide

/-- D.66 leg 5, FRAME-H2 (`e₁ = 3, h = 2, u₂ = 1, f₂ = 4`) — the chapter's only `Wfloor` table
with `i(u₂) ≠ 1` (`i(1) = 2` here), reduced through `iexp_eq_of_inv` because `h > 1`. -/
example : (List.range 4).map (fun t => Wfloor 3 2 1 4 t) = [2, 2, 1, 0] := by
  simp only [Wfloor,
    iexp_eq_of_inv 3 2 2 (by decide : ((2 : ℕ) : ZMod 3) * (2 : ZMod 3) = 1)]
  decide

/-- FRAME-H2's non-unit step, isolated: `i(u₂) = 2`, which is what the table above is scoring. -/
example : iexp 3 2 1 = 2 := by
  simp only [iexp_eq_of_inv 3 2 2 (by decide : ((2 : ℕ) : ZMod 3) * (2 : ZMod 3) = 1)]
  decide

end Frames

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.Wfloor

end AxCheck
