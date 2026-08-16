/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C16
import Uniformity.ChapH.H57

/-!
# Uniformity.ChapC.C41 — `slotIdx_add`, `twistExp_add`, `twistExp_nsmul`: the wrap cocycle

**Chapter C, NODE C.41** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys
and the tower bridges; the A-C.1 amendment set governs). **ENV-C1** *[A-C.1 re-tag per defect
**D7**: ENV-C5 → ENV-C1, stated over `KeyFrame`, which binds the DVR telescope; see C.15's
rider]*. Three signed declarations, all arithmetic on the frame's gauge exponents. This is
HETOW-12, the **wrap cocycle**: the failure of the slot index `i(·)` to be additive is the
`{0,1}`-valued wrap `wrap(a,b) = (i(a) + i(b))/e₁`, and that same wrap is exactly the defect by
which the twist exponent `Q(·) = twistExp` *over*-shoots additivity.

* `KeyFrame.slotIdx_add F a b` — clause (i), slot half: `i(a) + i(b) = i(a+b) + e₁·wrap(a,b)`
  **and** `wrap(a,b) ≤ 1`. Both halves are one fact: `i(a) + i(b)` is a solution of the
  congruence for `a + b` that lives in `[0, 2e₁)`, so it is `i(a+b)` plus at most one full lap.
* `KeyFrame.twistExp_add F a b` — clause (i), twist half: `Q(a+b) = Q(a) + Q(b) + wrap(a,b)`.
  The cocycle identity proper: `Q` is additive up to the same `wrap`.
* `KeyFrame.twistExp_nsmul F u₂ f₂ t ht` — clause (ii), the telescoped form at the multiple
  `(f₂−t)·u₂` that §6 actually consumes: `Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t)` with
  `W(t) = (f₂−t)·i(u₂)/e₁`, H.57's wrap exponent. Not proved by iterating `twistExp_add`
  `(f₂−t)` times — that would accumulate `(f₂−t)−1` separate wraps — but in one step from the
  same mechanism at the scaled slot `(f₂−t)·i(u₂)`, whose single wrap IS `W(t)`.

`W(t)` is the exponent C.43's corrected composed key carries (`chat_t := lift(c_t·η^{W(t)})`);
this node supplies its arithmetic, nothing about the key.

## Why the congruence argument, and where it is allowed to run

Every clause is an instance of one move: *a candidate slot, reduced mod `e₁`, IS the slot*. C.16
licenses it in the only usable direction — `slotIdx_unique`: any `i < e₁` with `i·h ≡ k (mod e₁)`
equals `slotIdx F k`. So for (i), `s := i(a) + i(b)` satisfies `s·h ≡ a + b` (add the two
congruences of `slotIdx_spec`), hence `s % e₁ = i(a+b)`, and `Nat.mod_add_div` splits `s` into
`i(a+b) + e₁·(s/e₁)`; `s < 2e₁` from the two range bounds gives `s/e₁ ≤ 1`. For (ii) the same
with `s := (f₂−t)·i(u₂)`, whose congruence is `slotIdx_spec u₂` scaled by `(f₂−t)`. **C.15's
bodies are never unfolded here** — the module's standing rule (C.16's own docstring: consumers
cite the spec, never the `List.find?`), and the reason `F.hcop` does not appear by name in any
proof below: it is already spent inside `slotIdx_spec`.

The twist halves then need no new congruence at all. They are `twistExp_spec` (C.16(iii),
`i₀·k = i(k) + e₁·Q(k)`) applied at the three arguments, added, and cancelled: from
`i₀·(a+b) = i₀·a + i₀·b` one gets `i(a+b) + e₁·Q(a+b) = (i(a) + i(b)) + e₁(Q(a) + Q(b))`, and the
slot half rewrites the bracket to `i(a+b) + e₁·wrap`. Cancelling `i(a+b)` and then the factor
`e₁` (`Nat.eq_of_mul_eq_mul_left`, at `F.he₁`) is the whole proof. Note that this is where
`0 < e₁` is load-bearing: at `e₁ = 0` the statements would say nothing, and `KeyFrame.he₁` is
what rules that out.

**A ℕ-subtraction caveat, resolved.** `(f₂ − t)` is truncated subtraction, and `Q` is defined
(C.15) through a truncated subtraction of its own. Neither truncates here: `ht : t < f₂` makes
`f₂ − t` the honest difference, and C.16(iii) is exactly the theorem that C.15's inner
subtraction `i₀·k − i(k)` is exact. Every `/` below is ℕ-division and is *meant* to floor — the
wrap and `W(t)` are floors by definition.

## What is signed here, and what is not

The blueprint STATEMENT's clause (ii) displays **two** identities,
`(f₂−t)·i(u₂) = i((f₂−t)u₂) + e₁·W(t)` (slot) and `Q((f₂−t)u₂) = (f₂−t)Q(u₂) + W(t)` (twist).
The SIGNATURE signs only the twist one. The slot one is therefore **not** a declaration here —
signatures are frozen and a node may not grow one — but it is not lost either: it is the `hdiv`
step inside `twistExp_nsmul`'s proof, and a consumer needing it re-derives it in three lines from
`slotIdx_unique` + `wrap_div_mod` exactly as done below. (Same disposition C.16 gave its own
unsigned clauses (iv) and (v).)

`ht : t < f₂` is **not consumed by the proof**. The identity holds for every `r := f₂ − t`
including `r = 0` (both sides are `0`, since `i(0) = 0` and `Q(0) = 0`), so the hypothesis is a
scope fence inherited from the display `t < f₂`, not a proof obligation. It is kept verbatim
because the signature is frozen; the `unusedVariables` linter is silenced at that declaration for
exactly this reason, and the silencing is scoped `… in` to the one theorem.

## Divergence from the blueprint SIGNATURE

None. All three statements are the gate-verified twin `leanspec/Leanspec/ChapC.lean`'s verbatim
(the twin carries them as `axiom`s in the gate; here they land as theorems with the same types).
In particular the twin's `(f₂ - t) * F.slotIdx u₂ / F.e₁` is read with `*` and `/` left-associated
— `((f₂ - t) * F.slotIdx u₂) / F.e₁` — which is the blueprint's `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`, and
is the only reading under which the identity is true (`(f₂−t)·⌊i(u₂)/e₁⌋` is identically `0`,
since `i(u₂) < e₁`).

**Neighbour check (C.31).** C.31's A-C.1-re-signed `hjump : 2 ≤ ℓ * dr` does **not** reach this
node: nothing in C.41's three statements or their proofs mentions a jump, a multiplicity, or
`ℓ`/`dr`; the only hypotheses in play are `KeyFrame`'s own `he₁` and (inside C.16) `hcop`. No
re-signature is inherited.

**DEPENDS.** C.15 (`slotIdx`, `twistExp`) · C.16 (`slotIdx_spec`, `slotIdx_unique`,
`twistExp_spec` — the ONLY route to any property of C.15's bodies) · H.57 (`wrap_div_mod`, used
verbatim at the `(f₂−t)·i(u₂)` split; its companion `wrap_height` is the *height* form, consumed
by C.43/C.47, not here) — by committed node ID (GC-13(b)). Imports: `Uniformity.ChapC.C16`
(which pulls C.15, C.01 and the B chain) and `Uniformity.ChapH.H57` (the H §8 slot slice only,
never the ChapH roll-up — §0.2's rule against re-creating the backward arc H-14 removed; H.57
itself imports only H.51, which C.16 already carries).

**PROOF.** The blueprint's three-step PROOF field, followed exactly, with step 3 taking its
stated second option ("or directly H.57's `wrap_div_mod`") rather than the induction on `f₂ − t`:
the one-step route is shorter and, more importantly, avoids the false intermediate that iterating
(i) would suggest, namely that the wraps at the `(f₂−t)` summands are individually `W(t)`.

SOURCE: `EFF.HETOW.12` (LEMMA HETOW-12, the two displays verbatim, plus the frame-X audit);
`EFF.HETOW.11` (`Q(k) = ⌊i₀k/e₁⌋`, the identification with C.15's `twistExp`, which is C.16(iii)).

**TEETH.** `EFF.HETOW.12`'s frame-X audit (`i(3) = 1`, `W(0) = 1`, `W(1) = 0`) → **executable
regression at §13**; the identity leg of the 2026-08-10 run (`k = 1..60` per frame) → retained
there. Neither is dischargeable against the abstract `KeyFrame O π` of this node's binders — the
D7 consequence recorded at C.15 — but frame X is a *numeral* frame, so its rows are mirrored at
the bottom of this file as bare `#guard`s on the closed forms that frame X forces. Frame X is
`p = 3, e₁ = 2, f₁ = 1, h = 1, η = 2, u₂ = 3` (`EFF.T1.33`), with `f₂ = 2` read off the audit's
own `W(0)/W(1)` pair; at `e₁ = 2, h = 1` clause (ii) of C.16 gives `i(k) = k % 2` (since
`k % 2 < 2` and `(k % 2)·1 ≡ k`), hence `i₀ = 1` and `Q(k) = (k − k % 2)/2 = k / 2`. Those two
closed forms — not the abstract bodies — are what the `#guard`s evaluate. This is a `q = 3` row;
GC-11's `q = 2` companion for the gauge layer is §13's `(1,2)`-genre frame, not this node's.

ENVIRONMENT: ENV-C1 (post-D7).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Induction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.41 (i), slot half — the wrap decomposition.** `i(a) + i(b) = i(a+b) + e₁·wrap(a,b)` with
`wrap(a,b) := (i(a) + i(b))/e₁ ≤ 1`: the slot index is additive up to at most one lap of the
`e₁`-cycle.  Proof: `i(a) + i(b)` solves the congruence for `a + b` (C.16(i), added) and lies in
`[0, 2e₁)`, so C.16(ii) identifies its residue with `i(a+b)`. -/
theorem KeyFrame.slotIdx_add (F : KeyFrame O π) (a b : ℕ) :
    F.slotIdx a + F.slotIdx b
      = F.slotIdx (a + b) + F.e₁ * ((F.slotIdx a + F.slotIdx b) / F.e₁) ∧
    (F.slotIdx a + F.slotIdx b) / F.e₁ ≤ 1 := by
  obtain ⟨hlta, hca⟩ := F.slotIdx_spec a
  obtain ⟨hltb, hcb⟩ := F.slotIdx_spec b
  set s := F.slotIdx a + F.slotIdx b with hs
  -- `s·h ≡ a + b (mod e₁)`: the two congruences of C.16(i), added.
  have hcong : s * F.h ≡ a + b [MOD F.e₁] := by
    have h := hca.add hcb
    simpa [hs, add_mul] using h
  -- hence `s % e₁` IS the slot of `a + b` (C.16(ii)).
  have hmod : s % F.e₁ = F.slotIdx (a + b) :=
    F.slotIdx_unique (Nat.mod_lt _ F.he₁)
      (((Nat.mod_modEq s F.e₁).mul_right F.h).trans hcong)
  refine ⟨?_, ?_⟩
  · rw [← hmod]
    exact (Nat.mod_add_div s F.e₁).symm
  · -- `s < 2e₁` from the two range bounds, so at most one lap.
    have h2 : s < F.e₁ * 2 := by omega
    exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul h2)

/-- **C.41 (i), twist half — the cocycle identity.**
`Q(a+b) = Q(a) + Q(b) + wrap(a,b)`.  Proof: expand C.16(iii) at `a`, `b` and `a+b` inside
`i₀·(a+b) = i₀·a + i₀·b`, rewrite the resulting `i(a) + i(b)` by the slot half, and cancel
`i(a+b)` and then the factor `e₁` (legal at `F.he₁`). -/
theorem KeyFrame.twistExp_add (F : KeyFrame O π) (a b : ℕ) :
    F.twistExp (a + b)
      = F.twistExp a + F.twistExp b + (F.slotIdx a + F.slotIdx b) / F.e₁ := by
  obtain ⟨hsum, -⟩ := F.slotIdx_add a b
  -- abstract the wrap, so that the rewrite by `hsum` cannot reach inside its own numerator
  set w := (F.slotIdx a + F.slotIdx b) / F.e₁ with hw
  refine Nat.eq_of_mul_eq_mul_left F.he₁ ?_
  refine Nat.add_left_cancel (n := F.slotIdx (a + b)) ?_
  calc F.slotIdx (a + b) + F.e₁ * F.twistExp (a + b)
      = F.slotIdx 1 * (a + b) := (F.twistExp_spec (a + b)).symm
    _ = F.slotIdx 1 * a + F.slotIdx 1 * b := by ring
    _ = (F.slotIdx a + F.e₁ * F.twistExp a) + (F.slotIdx b + F.e₁ * F.twistExp b) := by
        rw [← F.twistExp_spec a, ← F.twistExp_spec b]
    _ = (F.slotIdx a + F.slotIdx b) + (F.e₁ * F.twistExp a + F.e₁ * F.twistExp b) := by ring
    _ = (F.slotIdx (a + b) + F.e₁ * w)
          + (F.e₁ * F.twistExp a + F.e₁ * F.twistExp b) := by rw [hsum]
    _ = F.slotIdx (a + b) + F.e₁ * (F.twistExp a + F.twistExp b + w) := by ring

set_option linter.unusedVariables false in
/-- **C.41 (ii) — the telescoped wrap at a multiple** (H.57's wrap exponent).
`Q((f₂−t)·u₂) = (f₂−t)·Q(u₂) + W(t)` with `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`.  This is the form C.43's
corrected composed key consumes (`chat_t = lift(c_t·η^{W(t)})`).

Proof: the scaled slot `(f₂−t)·i(u₂)` solves the congruence for `(f₂−t)·u₂` (C.16(i) scaled), so
C.16(ii) makes its residue `i((f₂−t)u₂)` and H.57's `wrap_div_mod` splits it as
`i((f₂−t)u₂) + e₁·W(t)`; then C.16(iii) at `(f₂−t)u₂` and at `u₂` (scaled), cancelled as in the
twist half above.

`ht : t < f₂` is a scope fence, not a proof obligation — see the module docstring; the linter
silencing above is scoped to this declaration and records that. -/
theorem KeyFrame.twistExp_nsmul (F : KeyFrame O π) (u₂ f₂ t : ℕ) (ht : t < f₂) :
    F.twistExp ((f₂ - t) * u₂)
      = (f₂ - t) * F.twistExp u₂ + (f₂ - t) * F.slotIdx u₂ / F.e₁ := by
  have hcong : ((f₂ - t) * F.slotIdx u₂) * F.h ≡ (f₂ - t) * u₂ [MOD F.e₁] := by
    have h := ((F.slotIdx_spec u₂).2).mul_left (f₂ - t)
    simpa [mul_assoc] using h
  have hmod : ((f₂ - t) * F.slotIdx u₂) % F.e₁ = F.slotIdx ((f₂ - t) * u₂) :=
    F.slotIdx_unique (Nat.mod_lt _ F.he₁)
      (((Nat.mod_modEq _ F.e₁).mul_right F.h).trans hcong)
  -- the UNSIGNED slot half of clause (ii), via H.57's `wrap_div_mod`
  have hdiv : (f₂ - t) * F.slotIdx u₂
      = F.slotIdx ((f₂ - t) * u₂) + F.e₁ * ((f₂ - t) * F.slotIdx u₂ / F.e₁) := by
    rw [← hmod]
    exact (wrap_div_mod (f₂ - t) (F.slotIdx u₂) F.e₁ F.he₁).1
  set W := (f₂ - t) * F.slotIdx u₂ / F.e₁ with hW
  refine Nat.eq_of_mul_eq_mul_left F.he₁ ?_
  refine Nat.add_left_cancel (n := F.slotIdx ((f₂ - t) * u₂)) ?_
  calc F.slotIdx ((f₂ - t) * u₂) + F.e₁ * F.twistExp ((f₂ - t) * u₂)
      = F.slotIdx 1 * ((f₂ - t) * u₂) := (F.twistExp_spec _).symm
    _ = (f₂ - t) * (F.slotIdx 1 * u₂) := by ring
    _ = (f₂ - t) * (F.slotIdx u₂ + F.e₁ * F.twistExp u₂) := by rw [F.twistExp_spec u₂]
    _ = (f₂ - t) * F.slotIdx u₂ + F.e₁ * ((f₂ - t) * F.twistExp u₂) := by ring
    _ = (F.slotIdx ((f₂ - t) * u₂) + F.e₁ * W) + F.e₁ * ((f₂ - t) * F.twistExp u₂) := by
        rw [hdiv]
    _ = F.slotIdx ((f₂ - t) * u₂) + F.e₁ * ((f₂ - t) * F.twistExp u₂ + W) := by ring

end Uniformity.Density.Tower

/-! ## `EFF.HETOW.12`'s frame-X audit, as `#guard`s

Frame X is `p = 3, e₁ = 2, f₁ = 1, h = 1, η = 2, u₂ = 3` with `f₂ = 2`.  At `e₁ = 2, h = 1`,
C.16(ii) forces the closed forms `i(k) = k % 2` and `Q(k) = k / 2`, and the rows below are those
closed forms evaluated — **numeral mirrors of the audit, not statements about the abstract
declarations above** (an abstract `KeyFrame O π` supplies no numeral to `#guard`; the D7
consequence recorded at C.15). -/

section FrameXAudit

/-! `i(3) = 1`. -/
#guard (3 % 2 : ℕ) = 1

/-! `W(0) = ⌊(f₂ − 0)·i(u₂)/e₁⌋ = ⌊2·1/2⌋ = 1` and `W(1) = ⌊1·1/2⌋ = 0`. -/
#guard ((2 - 0) * (3 % 2) / 2 : ℕ) = 1
#guard ((2 - 1) * (3 % 2) / 2 : ℕ) = 0

/-! `twistExp_nsmul` at frame X, both `t`: `Q(2·3) = 2·Q(3) + W(0)` is `3 = 2 + 1`, and
`Q(1·3) = 1·Q(3) + W(1)` is `1 = 1 + 0`. -/
#guard ((2 - 0) * 3 / 2 : ℕ) = (2 - 0) * (3 / 2) + (2 - 0) * (3 % 2) / 2
#guard ((2 - 1) * 3 / 2 : ℕ) = (2 - 1) * (3 / 2) + (2 - 1) * (3 % 2) / 2

/-! The cocycle at frame X on the audit's own arguments: `i(3) + i(3) = i(6) + 2·wrap`,
`wrap = 1`, and `Q(6) = Q(3) + Q(3) + 1`. -/
#guard (3 % 2 + 3 % 2 : ℕ) = 6 % 2 + 2 * ((3 % 2 + 3 % 2) / 2)
#guard ((3 % 2 + 3 % 2) / 2 : ℕ) = 1
#guard (6 / 2 : ℕ) = 3 / 2 + 3 / 2 + (3 % 2 + 3 % 2) / 2

end FrameXAudit

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_add
#print axioms Uniformity.Density.Tower.KeyFrame.twistExp_add
#print axioms Uniformity.Density.Tower.KeyFrame.twistExp_nsmul

end AxCheck
