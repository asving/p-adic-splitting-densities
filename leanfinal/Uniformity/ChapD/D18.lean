/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D08
import Uniformity.ChapD.D16
import Uniformity.ChapD.D17

/-!
# Uniformity.ChapD.D18 — `(C2-level-1)`: the level-1 telescope is an explicit `η`-power

**Chapter D, NODE D.18** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1, A-D.2 govern). ENV-D1 + ENV-D3. One signed declaration
(the leanspec stub signs it as an `axiom`; it is PROVED here), plus the file-local FRAME-C
battery that executes it.

*The level-1 telescope is an explicit `η`-power.* In the level-1 arena (D.17), for a height
`u₂ : ℤ` and a telescope length `s : ℕ`,

  `(levelOneArena e₁ h he hcop η).vartheta u₂ s = η ^ (s · i(u₂) / e₁)`

with `/` the FLOOR division of `ℕ`. **"The exponent has the displayed positive sign"**
(`EFF.T1.10`, transcribed as stated) — the wrong-sign mutation is the tooth, and it is scored
below and again at gates D.65/D.66.

The slot-indexed form of the blueprint STATEMENT, `ϑ_{1,f₂−t} = η^{W(t)}` with D.16's
`W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`, is `levelOneArena_vartheta` at `s := f₂ − t` followed by unfolding
`Wfloor`; it is scored as an `example` below rather than given a second public name, because
the signature freeze signs exactly one declaration for this node.

## Why the floor appears (the arithmetic content)

`varthetaEl u₂ s = n̂(u₂)^s · n̂(s·u₂)⁻¹` has exponent-lattice `x`-coordinate
`s·i(u₂) − i(s·u₂)`, and D.13's `i` is a REDUCED residue: `i(s·u₂) = (s·i(u₂)) mod e₁`
(proved inline from the definition `i(k) = (k·h⁻¹ mod e₁).val` — this step needs only
`0 < e₁`, not coprimality). Hence the `x`-coordinate is `e₁·⌊s·i(u₂)/e₁⌋`, the kernel
generator `(e₁, −h)` is hit exactly `⌊s·i(u₂)/e₁⌋` times, and D.17's `res : (i,a) ↦ η^{i/e₁}`
returns `η` to that power — "reducing `s·i(u₂)` modulo `e₁` yields the floor count"
(`EFF.T1.10`'s verbatim derivation).

DEPENDS: D.08 (`GaugeArena.vartheta`) · D.13 (`iexp`, and `iexp_one` for the frames) ·
D.16 (`Wfloor`, the slot-indexed spelling) · D.17 (`levelOneSection`, `levelOneArena`), all
landed under `Uniformity.ChapD` · mathlib `ZMod.val_mul`, `ZMod.val_natCast`,
`Nat.mod_mul_mod`, `Nat.div_add_mod`, `Int.mul_ediv_cancel_left`, `zpow_natCast`.

**PROOF.** 1. `hcoord`: the `x`-coordinate of `toAdd (varthetaEl u₂ s)` is
`↑(s·i(u₂)) − ↑(i(s·u₂))` (`toAdd_mul`/`toAdd_inv`/`toAdd_pow` on the `Multiplicative (ℤ × ℤ)`
lattice, then `push_cast`/`ring`). 2. `hmod`: `i(s·u₂) = (s·i(u₂)) mod e₁` — unfold `iexp`,
`push_cast` the `ℤ`-product into `ZMod e₁`, then `ZMod.val_mul` + `ZMod.val_natCast` +
`Nat.mod_mul_mod`; `NeZero e₁` comes from `he`. 3. `hsplit`: `a − a mod e₁ = e₁·(a / e₁)` in
`ℤ`, from `Nat.div_add_mod` cast with `Nat.cast_add`/`Nat.cast_mul` only (`push_cast` must NOT
be used here — it would rewrite `↑(a / e₁)` into `↑a / ↑e₁` and lose the `ℕ`-floor). 4. The
`res` application is definitional (`change`), then `Int.mul_ediv_cancel_left` cancels `e₁` and
`zpow_natCast` reconciles the `ℤ`-exponent of `res` with the `ℕ`-exponent of the statement.
⚠ `hcop` is NOT consumed by the proof — it is carried because `levelOneArena`'s signature
demands it (its `res` field needs it); this is faithful, not a weakening.

SOURCE: `EFF.T1.10` (the boxed `(C2-level-1)` `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}` + the `W(t)`
display).

**ORIENTATION.** T1 two-index (D.06 row 2). The GENTOW2-orientation value at this instance is
the INVERSE `η^{−W(t)}`; a consumer wanting GENTOW2's `ϑ(t)` reads `varthetaG2` (D.10), NEVER
this lemma with a silent sign flip.

**TEETH.** T1 §4.2 check 2 (positive-wrap sign; exact coefficient equality) → **Lean theorem**
(this node). The gauge-naive and wrong-sign teeth are EXECUTED ROWS: the FRAME-C block below
runs the `η`-power table through the actual arena at `p = 5`, and gates D.65/D.66 run it at
both primes. FRAME-C is where D.06's committed `ϑ = (1,1,2,2,4)` comes from — D.06 assembles
that table from THIS node's formula, so the rows below are the missing leg that ties the
committed table to the arena-level telescope it is supposed to be.

ENVIRONMENT: ENV-D1 + ENV-D3 (`{K : Type*} [Field K]`, `η : Kˣ`, written inline per the B.42
binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only). The theorem is PROVED here, not the leanspec `axiom`
stub; every frame leg is an executed `decide`.
-/

namespace Uniformity.Density.Gauge

/-- **D.18 — `(C2-level-1)`, the level-1 telescope as an explicit `η`-power** (`EFF.T1.10`):
`ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}`.  The exponent has the DISPLAYED POSITIVE SIGN and the division is
`ℕ`-floor.  ORIENTATION: T1 two-index (D.06 row 2) — the GENTOW2 value is the inverse, read
through `varthetaG2` (D.10) and never by flipping a sign here. -/
theorem levelOneArena_vartheta (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (s : ℕ) :
    (levelOneArena e₁ h he hcop η).vartheta u₂ s = η ^ (s * iexp e₁ h u₂ / e₁) := by
  have hcoord : (Multiplicative.toAdd ((levelOneSection e₁ h).varthetaEl u₂ s)).1
      = ((s * iexp e₁ h u₂ : ℕ) : ℤ) - ((iexp e₁ h ((s : ℤ) * u₂) : ℕ) : ℤ) := by
    simp only [NormSection.varthetaEl, levelOneSection, toAdd_mul, toAdd_inv, toAdd_pow,
      toAdd_ofAdd, Prod.fst_add, Prod.fst_neg, Prod.smul_fst]
    push_cast
    ring
  have hmod : iexp e₁ h ((s : ℤ) * u₂) = (s * iexp e₁ h u₂) % e₁ := by
    haveI : NeZero e₁ := ⟨he.ne'⟩
    simp only [iexp]
    push_cast
    rw [mul_assoc, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hsplit : ((s * iexp e₁ h u₂ : ℕ) : ℤ) - (((s * iexp e₁ h u₂) % e₁ : ℕ) : ℤ)
      = (e₁ : ℤ) * ((s * iexp e₁ h u₂ / e₁ : ℕ) : ℤ) := by
    have h1 : ((e₁ * (s * iexp e₁ h u₂ / e₁) + (s * iexp e₁ h u₂) % e₁ : ℕ) : ℤ)
        = ((s * iexp e₁ h u₂ : ℕ) : ℤ) := by
      rw [Nat.div_add_mod]
    rw [Nat.cast_add, Nat.cast_mul] at h1
    linarith
  have hne : (e₁ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr he.ne'
  change η ^ ((Multiplicative.toAdd ((levelOneSection e₁ h).varthetaEl u₂ s)).1 / (e₁ : ℤ))
      = η ^ (s * iexp e₁ h u₂ / e₁)
  rw [hcoord, hmod, hsplit, Int.mul_ediv_cancel_left _ hne, zpow_natCast]

end Uniformity.Density.Gauge

/-! ## The slot-indexed form, and the executed FRAME-C battery

The blueprint STATEMENT's second clause (`ϑ_{1,f₂−t} = η^{W(t)}`) is the theorem at
`s := f₂ − t` with D.16's `Wfloor` unfolded — an `example`, not a second public name, because
the node signs exactly one declaration.

FRAME-C is `p = 5`, `e₁ = 2`, `h = 1`, `η = 2`, `u₂ = 1`, `f₃ = 5` (`EFF.T3.29`). This is the
frame whose `ϑ` table D.06 ASSEMBLES from the formula above; the rows here run the SAME table
through the actual `levelOneArena`, which is the leg that ties D.06's committed data to the
telescope it claims to be. A-D.1 gate-writing rider (defect D-D1: `ZMod.inv` does not
kernel-reduce): every row that mentions `iexp` reduces through D.13's `iexp_one` BEFORE
deciding — `simp only [...]; decide`, never a bare `decide`. -/

section Frames

open Uniformity.Density.Gauge

/-- The blueprint STATEMENT's slot-indexed clause: `ϑ_{1,f₂−t} = η^{W(t)}` with D.16's
`W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`.  ⚠ `f₂ - t` is `ℕ`-subtraction on BOTH sides, so the truncation
branch `t ≥ f₂` matches too (both sides read `s = 0`, value `η^0 = 1`). -/
example (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) {K : Type*} [Field K] (η : Kˣ)
    (u₂ : ℤ) (f₂ t : ℕ) :
    (levelOneArena e₁ h he hcop η).vartheta u₂ (f₂ - t) = η ^ Wfloor e₁ h u₂ f₂ t := by
  rw [levelOneArena_vartheta, Wfloor]

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- FRAME-C's letter `η = 2 ∈ 𝔽₅ˣ`, with its inverse `3` (`2·3 = 6 = 1` in `𝔽₅`). -/
private def gate18eta : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

/-- FRAME-C's arena telescope, in `𝔽₅` rather than `𝔽₅ˣ`: `ϑ_{1,s} = 2^{⌊s·i(1)/2⌋}` at
`e₁ = 2, h = 1, u₂ = 1`.  This is D.18 applied, and it is what the rows below score. -/
private theorem gate18val (s : ℕ) :
    (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 s : (ZMod 5)ˣ)
      : ZMod 5) = (2 : ZMod 5) ^ (s * iexp 2 1 1 / 2) := by
  rw [levelOneArena_vartheta, Units.val_pow_eq_pow_val]
  rfl

/-- **The FRAME-C telescope table, through the arena.** `ϑ_{1,s} = (1,1,2,2,4)` on `s = 0…4` —
`EFF.T3.29`'s committed `ϑ`, and D.06's `gate06vartheta`, now derived from `levelOneArena`
instead of assembled from the exponent formula by hand. -/
example : (List.range 5).map (fun s =>
    (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 s : (ZMod 5)ˣ)
      : ZMod 5)) = [1, 1, 2, 2, 4] := by
  simp only [gate18val, iexp_one]
  decide

/-- FINDING D-F2's bottom slot, through the arena: the slot `t = 0` reads `s = f₃ = 5`, one
step beyond `EFF.T3.29`'s committed range, and the arena gives `ϑ_{1,5} = 2^{⌊5/2⌋} = 4`. -/
example : (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 5 : (ZMod 5)ˣ)
    : ZMod 5) = 4 := by
  simp only [gate18val, iexp_one]
  decide

/-- **The endpoints, through the arena** — D.09 at FRAME-C: `ϑ_{1,0} = ϑ_{1,1} = 1`, which the
`η`-power formula must reproduce (`⌊0/2⌋ = ⌊1/2⌋ = 0`). -/
example : (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 0 : (ZMod 5)ˣ)
      : ZMod 5) = 1 ∧
    (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 1 : (ZMod 5)ˣ)
      : ZMod 5) = 1 := by
  simp only [gate18val, iexp_one]
  decide

/-- **The GAUGE-NAIVE tooth, killed** (`EFF.T1.45`; the mutant that takes the telescope to be
trivial, `ϑ ≡ 1`): at FRAME-C, `ϑ_{1,2} = 2 ≠ 1`.  The telescope is a genuine obstruction and
the gauge cannot be dropped. -/
example : (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 2 : (ZMod 5)ˣ)
    : ZMod 5) ≠ 1 := by
  simp only [gate18val, iexp_one]
  decide

/-- **The WRONG-SIGN tooth, killed** (`EFF.T1.45`; the mutant that reads `ϑ_{1,s} = η^{−W}`
where `EFF.T1.10` displays `η^{+W}`).  The mutant's claim, stated multiplicatively so that no
`ZMod.inv` is needed (defect D-D1), is `ϑ_{1,s}·η^{W(s)} = 1`; at FRAME-C `s = 2` that reads
`ϑ_{1,2}·2 = 1`, and the true value gives `2·2 = 4 ≠ 1`.  Note this leg needs `W(s) ≠ 0`, so
`s = 2` is the FIRST slot at which the sign is observable — at `s ∈ {0,1}` the two signs agree
(D.09's endpoints), which is the whole reason the top slot is the safe anchor. -/
example : (((levelOneArena 2 1 (by norm_num) (by decide) gate18eta).vartheta 1 2 : (ZMod 5)ˣ)
    : ZMod 5) * (2 : ZMod 5) ^ (2 * iexp 2 1 1 / 2) ≠ 1 := by
  simp only [gate18val, iexp_one]
  decide

end Frames

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.levelOneArena_vartheta

end AxCheck
