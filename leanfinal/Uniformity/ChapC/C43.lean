/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C15
import Uniformity.ChapC.C19
import Uniformity.ChapC.C41
import Uniformity.ChapC.C42

/-!
# Uniformity.ChapC.C43 — `wrapExp`, `composedKey`: the wrap-corrected composed key `Φ₂`

**Chapter C, NODE C.43** [def] [fresh] [signed: A-C.1; **defect D19 RESOLVED** via C.14a's
`stageLiftO`, the RE-PLAN merge executed] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys
and the tower bridges, node at line 2784; twin `leanspec/Leanspec/ChapC.lean:1661-1677`; the A-C.1
amendment set governs). **ENV-C1**. **Two signed declarations**, both definitional.

Over a frame `F` (C.01) pinned at `H₀` (C.03) with a tower datum `T` (C.42), write
`Φ′ = F.key`, `η = F.stageLetter H₀ hpin` (C.19), `i(k) = F.slotIdx k` (C.15) and
`L_M(·) = F.stageLiftO H₀ hpin M (·)` (C.14a). `EFF.HETOW.13`'s TERMINAL display is

```
Φ₂ = Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)}) · Φ′^{e₂t},   c_t := −(ψ₂.coeff t),
W(t) := ⌊(f₂−t)·i(u₂)/e₁⌋.
```

* `wrapExp T t` — the **wrap exponent** `W(t)`, C.41(ii)'s.
* `composedKey T` — the display itself: the level-2 key `Φ₂`, of degree `D₂ = (e₁f₁)(e₂f₂)`
  (C.42's `TowerDatum.D₂`), and the object every §7 statement of this chapter is written at.

## Why the wrap correction is in the body, and what dies without it

The gauge-naive key — the same display with `lift(c_t)` in place of `L_{(f₂−t)u₂}(c_t·η^{W(t)})`,
i.e. no `η^{W(t)}` factor — is **DEAD**, and not by a margin that a reader can eyeball:
`EFF.HETOW.14`'s counter-instance at frame X has naive key `Φ′² + 3xΦ′ + 54` with Newton data
`σ = {(4,1)}` and corrected key `Φ′² + 3xΦ′ + 108` with `σ = {(2,2)}` — two *different* level-2
grammars, from constant terms differing by exactly the wrap factor `η^{W(0)} = 2`. The correction
is a factor of 2 in one coefficient and it moves the whole classification. This is why `wrapExp`
is a separate named definition rather than an inlined `/`-expression: C.46's residue computation
has to cancel it against `η^{−Q((f₂−t)u₂)}` by name, through C.41(ii).

The identification of `wrapExp` with the wrap exponent occurring in C.41's cocycle is
**definitional** — `KeyFrame.twistExp_nsmul`'s right-hand summand `(f₂ − t) * F.slotIdx u₂ / F.e₁`
is `wrapExp T t` unfolded — and the unfolding check below records it as an `example`, so a later
edit to either term breaks a compile rather than silently desynchronizing the two nodes.

## The sign convention (a two-negation site; read this before reading the body)

The corpus writes the inner residual as `ψ₂ = Z^{f₂} − Σ_{t<f₂} c_t Z^t`, so `c_t = −(ψ₂.coeff t)`
— the display's coefficients are the **negatives** of Lean's `Polynomial.coeff`. The body therefore
contains two independent minus signs, and they are not redundant:

* the inner `- T.ψ₂.coeff t` **is** `c_t` (the convention above), sitting inside the lift's
  argument together with the wrap factor, exactly as `L_{(f₂−t)u₂}(c_t·η^{W(t)})` demands;
* the outer `F.key ^ (T.e₂ * T.f₂) - (…).sum` is the display's own leading minus.

Dropping either one, or moving the inner minus outside the lift, changes the object: `stageLiftO`
is `ℕ`-height-indexed and additive only through its digit read, so `L_M(−c) = −L_M(c)` is not
available as a rewriting identity at this node (it is a statement about `stageCoord`'s linearity,
which no landed lemma supplies). The transcription is verbatim from the signed twin.

## What D19 was, and why the def is TOTAL

Stub-gate defect **D19**: chapter C's carrier `KeyFrame` (C.01) and chapter H's `GenreDatum`
(H.01) do not match (`GenreDatum` demands `hQ : 2 ≤ Q`, `hh : 1 ≤ h`, `hkey : 2 ≤ e₁f₁`,
`hmul : 2 ≤ μ`; `KeyFrame` has no `Q`, no `μ`, no `2 ≤ e₁f₁`, and deliberately admits `h = 0`), so
the lift `L_M` this display is written in was not constructible from anything landed and the node
was **UNSIGNABLE**. The RE-PLAN merge — one shared packaging helper for C.14 and C.43 — was
executed as **NODE C.14a**, whose `KeyFrame.stageLiftO` carries **no** proof fields: the corpus
preconditions (`1 ≤ F.h`, `2 ≤ F.e₁ * F.f₁`) sit on the height/residue THEOREMS (C.46's
`composedKey_slot_residue`, C.47's `composedKey_isTestKey`), which consume H.55/H.56 through
C.14a's reconciliation. That is deliberate and it is what makes `composedKey T` a function of `T`
alone: had the perimeter ridden in the term, two occurrences of the composed key carrying
different proofs would be syntactically distinct objects, and every §7 statement would inherit the
distinction.

## Trust-boundary notes (⚠ new definitions, flagged for human review)

**Both declarations are TOTAL and junk-defaulting outside the corpus perimeter**; neither asserts
anything, and nothing in this file may be read as a promise about values.

1. `wrapExp` is an `ℕ`-division. At binders where C.16's congruence machinery does not apply it is
   simply the floor of whatever `slotIdx` returned; `slotIdx` is itself C.15's junk-`0`-defaulting
   solve (`List.find?`-with-`getD 0`), so `W(t)` inherits that junk. C.41's `twistExp_nsmul` — the
   only statement about this quantity — is proved at the frame and is what consumers cite.
2. `composedKey`'s digits are, since the **2026-08-16 `stageCoord` REPAIR at C.14a**, honest:
   `stageLiftO` reads the letter-basis coordinate `KeyFrame.stageCoord` (an invariant of its
   argument, pinned by `KeyFrame.sum_stageCoord`), not a `Classical.choice` preimage. Before that
   repair no equation about `L_M(c)`'s residue could be either proved or refuted, and C.46's
   statement — the one theorem that pins THIS body — would have been unprovable in principle. The
   one remaining choice inside the display is `resLift`'s (a genuine section of
   `IsLocalRing.residue`, where no canonical preimage exists); `resLift_spec` is the only fact
   about it any consumer may use.
3. The `(i, a)`-solve inside `stageLiftO` is `slotIdx`-driven, so at heights `M = (f₂−t)u₂` where
   the congruence `i·h ≡ M [MOD e₁]` is unavailable the summand is junk. C.16's `slotIdx_spec` is
   what makes it honest, and it is cited by C.46/C.47, never here.

**Nothing about degree, monicity or test-key status is claimed at this node.** `Φ₂` is monic of
degree `D₂` and is an `IsTestKey` at C.44's `levelDatum` — that is C.47
(`composedKey_isTestKey`), which carries `(hh : 1 ≤ F.h)` and `Irreducible π`.

## Divergences from the blueprint text, recorded

* **The pin binder is `F.Pin H₀`**, as the signed SIGNATURE writes it (C.14a landed the
  abbreviation under A-C.1(c)), not the spelled-out `npHgt … = (H₀ : ℕ∞)` that C.03/C.42/C.44 use
  — those predate C.14a's landing. The two are the same `Prop` and `TowerDatum F H₀ hpin` accepts
  either; this file matches the SIGNATURE, as C.56a does.
* **No `open Uniformity.Density.Leaf`.** C.44 and C.56a carry it for the `resField`/`IsKey`
  vocabulary their bodies name; this file names none of it, so the open would be dead.
* **No `isKey_X` copy.** The D9 private-helper pattern (C.04/C.12/C.19/C.22/C.44) is needed only
  where a `Field (resField X)` instance must be produced by hand; `composedKey` produces no
  instance — every field-side object it touches arrives ready-made from `stageLiftO` and
  `stageLetter`.

**DEPENDS.** C.14a (`KeyFrame.Pin`, `KeyFrame.stageLiftO` — the D19 resolution) · C.15
(`KeyFrame.slotIdx`) · C.19 (`KeyFrame.stageLetter`) · C.41 (`KeyFrame.twistExp_nsmul`, the wrap
cocycle `W(t)` is read against) · C.42 (`TowerDatum`) · C.01/C.03 (`KeyFrame`, `stageField`,
through those imports) · **H.54–H.56** (reached ONLY through the C.14a packaging, per GC-5/H-14) —
all by committed node ID (GC-13(b)). Mathlib: `Finset.range`, `Finset.sum`, `Polynomial`.

**PROOF.** definitional (both declarations).

**SOURCE.** `EFF.HETOW.13` (the display + the `(LIFT)`-construction gloss and its residue claim
`c·η^{−Q(k)}`, verbatim; CHAIN-KEY TERMINAL); `EFF.GENTOW1.06` (the same pin from the consumer
side, with the nine-site manifest); `EFF.HETOW.14` (the `54` vs `108` counter-instance that kills
the gauge-naive form); `EFF.HETOW.12` (the wrap exponent `W(t)`, via C.41).

**TEETH.** Both of the blueprint's teeth are routed elsewhere by the blueprint itself: the
supp-leg check ("corrected-key slot residues = minpoly(β) at each frame: X: `Z²+2Z+2`; Z/W:
`Z²+3Z+4`") is a **Lean theorem at C.46** plus an executable regression, and the naive/corrected
`54` vs `108` pair is a **§13 gate row** (a `q = 3` frame; the `q = 2` twin is any `η = 1` frame,
where naive and corrected coincide — the gate documents WHY that row cannot distinguish, C-H12's
coincidence discipline). Neither is dischargeable at these binders: an abstract `KeyFrame O π`
with an abstract `TowerDatum` supplies no numeral (the D7 consequence recorded at C.15). The
**local substitute** is the three unfolding `example`s below, which pin the shape a numeral row
would pin — the leading exponent `e₂f₂`; the per-`t` height `(f₂−t)u₂` and slot exponent `e₂t`
moving in *opposite* directions as `t` grows; the wrap factor sitting INSIDE the lift's argument
next to `c_t`; and `wrapExp`'s coincidence with C.41's cocycle term. An `e₂ ↔ f₂` swap, a
`t ↔ f₂−t` transposition, or a wrap factor migrating outside the lift cannot survive them.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations -/

/-- **C.43(a) — the wrap exponent** `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` (C.41(ii)), the gauge correction
the composed key's `t`-th lift argument carries.

Definitionally the summand appearing in C.41's `KeyFrame.twistExp_nsmul`, which is the only
statement about it (`Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t)`); see the unfolding check below. Junk
wherever C.15's `slotIdx` is junk. -/
def wrapExp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (t : ℕ) : ℕ :=
  (T.f₂ - t) * F.slotIdx T.u₂ / F.e₁

/-- **NODE C.43 — the wrap-corrected composed key `Φ₂`,** `EFF.HETOW.13`'s TERMINAL display:

```
Φ₂ = Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)}) · Φ′^{e₂t},   c_t = −(ψ₂.coeff t).
```

`L_M` is C.14a's `KeyFrame.stageLiftO` (defect D19's resolution: the exact-height-`M` lift of a
stage-field element, TOTAL — the corpus preconditions `1 ≤ h`, `2 ≤ e₁f₁` ride on C.46/C.47, not
on the term). The inner minus is the corpus's sign convention `c_t = −(ψ₂.coeff t)`, the outer one
is the display's; see the module docstring, since the two must not be collapsed.

**The wrap factor `η^{W(t)}` is not optional.** Without it this is the gauge-naive key, refuted at
`EFF.HETOW.14` (frame X: `Φ′² + 3xΦ′ + 54`, `σ = {(4,1)}` — versus the corrected
`Φ′² + 3xΦ′ + 108`, `σ = {(2,2)}`).

Monicity, `natDegree = T.D₂` and `IsTestKey (T.levelDatum hπ)` are **not** claimed here: they are
C.47 (`composedKey_isTestKey`), which carries `Irreducible π` and `1 ≤ F.h`. -/
noncomputable def composedKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Polynomial O :=
  F.key ^ (T.e₂ * T.f₂)
    - (Finset.range T.f₂).sum fun t =>
        F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))
          * F.key ^ (T.e₂ * t)

end Uniformity.Density.Tower

/-! ## Unfolding checks — the display's shape at `f₂ = 1, 2`, and `wrapExp` against C.41

`example`s, not declarations: the local substitute for the numeral rows §13 and C.46 own (see the
module docstring's TEETH). Together they pin the leading exponent, the two per-`t` exponents and
their opposite directions of travel, the position of the wrap factor, and the identification of
`wrapExp` with C.41's cocycle term. -/

section UnfoldingChecks

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `wrapExp` **IS** C.41(ii)'s wrap exponent: the cocycle `Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t)`
holds with `W(t) := wrapExp T t` *by definitional unfolding* — this `example` is C.41's
`twistExp_nsmul` applied unchanged, and it is what keeps the two nodes from drifting apart. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (t : ℕ) (ht : t < T.f₂) :
    F.twistExp ((T.f₂ - t) * T.u₂)
      = (T.f₂ - t) * F.twistExp T.u₂ + wrapExp T t :=
  F.twistExp_nsmul T.u₂ T.f₂ t ht

/-- `f₂ = 1`: the single flavour `t = 0`. The leading term is `Φ′^{e₂}`, the one lift sits at
height `u₂` (not `e₂u₂`, not `u₂/e₂`), its argument is `c₀·η^{W(0)}`, and no `Φ′`-power multiplies
it (`Φ′^{e₂·0} = 1`). -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (h2 : T.f₂ = 1) :
    composedKey T
      = F.key ^ T.e₂
        - F.stageLiftO H₀ hpin T.u₂
            (- T.ψ₂.coeff 0 * F.stageLetter H₀ hpin ^ wrapExp T 0) := by
  rw [composedKey, h2, Finset.sum_range_one]
  simp

/-- `f₂ = 2`: the two flavours travel in opposite directions. As `t` goes `0 → 1` the lift height
drops by `u₂` (from `2u₂` to `u₂`) while the `Φ′`-exponent rises by `e₂` (from `0` to `e₂`), and
the digit read moves from `ψ₂.coeff 0` to `ψ₂.coeff 1` with its own wrap `W(1)`. A
`t ↔ f₂−t` transposition would exchange the two heights and cannot survive this. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (h2 : T.f₂ = 2) :
    composedKey T
      = F.key ^ (T.e₂ * 2)
        - (F.stageLiftO H₀ hpin (2 * T.u₂)
              (- T.ψ₂.coeff 0 * F.stageLetter H₀ hpin ^ wrapExp T 0)
            + F.stageLiftO H₀ hpin T.u₂
                (- T.ψ₂.coeff 1 * F.stageLetter H₀ hpin ^ wrapExp T 1)
              * F.key ^ T.e₂) := by
  rw [composedKey, h2, Finset.sum_range_succ, Finset.sum_range_one]
  simp

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.wrapExp
#print axioms Uniformity.Density.Tower.composedKey

end AxCheck
