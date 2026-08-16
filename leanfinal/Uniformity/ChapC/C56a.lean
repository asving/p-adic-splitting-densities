/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C42
import Uniformity.ChapC.C44
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C56a — `k2Coord`, `n2Exp`, `k2DigitLift`: the base-resolved K₂-digit lift

**Chapter C, NODE C.56a** [def] [fresh] [signed: A-C.1] (`blueprint/CHAP-C_tower_grammar.md` §8,
lines 3455–3516; twin `leanspec/Leanspec/ChapC.lean:1827-1855`). **ENV-C1.** Three declarations,
all definitional; no theorem.

The node was split out of C.56 by the **A-7 SCC repair** — C.84's `DeepTower` lift entry pointed
at the pre-split parent *theorem* node, closing a cycle — so `k2DigitLift` now has its own node
and both C.56 and C.84/C.85 point here.

This is `EFF.GENTOW1.27`'s **`.62` TERMINAL display**, the object that the composed refine
`Φ₂⁺ := Φ₂ − lift(s; λ)` subtracts:

```
lift(s; m) := Σ_{r<f₁} Σ_{t<f₂} d_{r,t} · n̂₂(m − Δ(r,t)) · x^{e₁r} · Φ′^{e₂t},
Δ(r,t) := e₁e₂h·r + e₂u₂·t,      n̂₂(m) = π^{a₀} x^i Φ′^b  (i < e₁, b < e₂).
```

* `k2Coord T s t` — the `t`-th `K`-coordinate of `s ∈ K₂ = AdjoinRoot (towerLabel T)` in the
  `β`-basis, read off a chosen `AdjoinRoot.mk`-preimage.
* `n2Exp T m` — the two-step `n̂₂`-solve returning `(a₀, i, b)`: C.83's `towerSolve` at `(u₂, e₂)`
  for `b`, then C.15's `slotIdx` on the reduced height `m' = (m − b·u₂)/e₂` for `(i, a₀)`.
* `k2DigitLift T s m` — the display itself, with the base RE-SOLVED per flavor `(r, t)`.

**The frozen fixed-base display is DEAD.** Its compensating `π`-exponent goes non-integer at
seam-live heights — the FR-A machine counter-instance `11/2 ∉ ℤ` (`EFF.GENTOW5.17`). What is
landed here is the corrected per-flavor re-solve: the argument of `n2Exp` carries the flavor
offset `Δ(r, t)`, so each summand solves its own class equation.

## Trust-boundary notes (⚠ new definitions, flagged for human review)

`k2Coord` is a **section, not an invariant**, and both it and `n2Exp` are **junk-total**:

1. `k2Coord` reads `((AdjoinRoot.mk_surjective s).choose).coeff t`. Different preimages of the
   same class differ by a multiple of `towerLabel T`, so the value is not determined by `s` alone
   at `t ≥ f₂`, and the `choose` is not guaranteed to have degree `< f₂`. No downstream statement
   may assert an equation about `k2Coord` in isolation. `k2DigitLift` reads it only for
   `t < T.f₂`.

   **⚠ OPEN DEFECT, inherited from what C.14a's `stageCoord` used to be.** This was "exactly
   C.14a's `stageCoord` situation one level up" — and that one turned out to be a defect, not a
   convention: C.14's audit (`ChapC/C14.lean`, the ⚠ DEFECT section) showed that an opaque
   `Classical.choice` representative has no degree bound, so the reconstruction identity
   `Σ_{t < f₂} k2Coord(s,t)·β^t = s` is neither provable nor refutable, and no residue clause
   about the resulting lift can pin it either. C.14a's read was **repaired on 2026-08-16** — it is
   now the `AdjoinRoot.powerBasis` coordinate (`KeyFrame.stagePB`), with the reconstruction
   identity landed as `KeyFrame.sum_stageCoord` — so the `F.stageCoord …` factor of the digit
   below is now honest. `k2Coord` is **not** yet: it wants the same cure at `towerLabel T`'s power
   basis over `K = F.stageField H₀ hpin`. Recorded for the fleet; out of this node's scope, and
   nothing landed asserts an equation about `k2Coord`.
2. `n2Exp` is built from two junk-`0`-defaulting solves (C.15's `slotIdx`, C.83's `towerSolve`,
   both `List.find?`-with-`getD 0`). It returns the intended `(a₀, i, b)` exactly when the class
   equation `e₁e₂a₀ + ie₂h + bu₂ = m` is solvable; `T.hcop`/`F.hcop` guarantee solvability of the
   two congruences, and `a₀ ≥ 0` (i.e. the ℕ-subtractions are honest) needs `m > E₂` through the
   audited inequality `E₂ ≥ (e₁−1)e₂h + (e₂−1)u₂ + 1`. **Neither the range clauses `i < e₁`,
   `b < e₂` nor the height equation is proved at this node** — per C.15's and C.83's standing
   convention the SPEC is the consumers' business (C.16 at the frame, C.16-at-`(u₂,e₂)` at the
   inner rung), and C.56's `refine_invariants` is where `m > E₂` enters as `hslope`.

Consequently the `deg lift < D₂` sentence (frozen, and it STANDS) is **not** a theorem of this
file: it is a clause of C.56(i), where the range facts are available.

## Divergences from the blueprint text, recorded

* **`resLift` is NOT re-declared here.** The blueprint's C.14a block calls `resLift` "a private
  helper of this file", which would have forced a D9-pattern local copy (as `isKey_X` is copied at
  C.04/C.12/C.19/C.22/C.44). Landed C.14a **overrode that prose and made `resLift` public**,
  citing this very node: "the blueprint's OWN signature for `C.56a`'s `k2DigitLift` writes
  `resLift (F.stageCoord …)` in the body of a declaration in another file, and Lean's `private` is
  not importable." A local copy is therefore not merely redundant but *illegal*: it would be a
  second declaration named `Uniformity.Density.Tower.resLift`. The signed body is used verbatim
  against C.14a's public one.
* **The pin binder is `F.Pin H₀`**, as the signed signature writes it (C.14a landed the
  abbreviation under A-C.1(c)), not the spelled-out `npHgt … = (H₀ : ℕ∞)` of C.03/C.42/C.44. The
  two are the same `Prop` and `TowerDatum F H₀ hpin` accepts either; this file matches the
  SIGNATURE.

**DEPENDS.** C.01 (`KeyFrame`) · C.03 (`stageField`) · C.14a (`Pin`, `stageCoord`, `resLift`) ·
C.15/C.16 (`slotIdx` and its spec, the latter at the consumers) · C.28 (the class-solve pattern) ·
C.42 (`TowerDatum`) · C.44 (`towerLabel`) · C.83 (`towerSolve`) — all by committed node ID.
H.51/H.52 (two-step class separation) and H.54–H.56 (base-level digit realization, per C-H5)
are the *supply* for the consumers' spec clauses, not for these bodies.

**PROOF.** Definitional. The range / `a₀ ≥ 0` arithmetic (`omega` from `T.hfloor`) belongs to the
consuming nodes, as recorded above.

**SOURCE.** `EFF.GENTOW1.27` (the setting + the `.62` TERMINAL lift display, verbatim; the
`a₀ ≥ 0` audit); `EFF.GENTOW1.53`-region and `EFF.GENTOW5.17` (the S3 correction's provenance and
the FR-A counter-instance).

**TEETH.** The blueprint routes C.56a's tooth — the FR-A verification `n̂₂(14−3)·Φ₁ = 3⁵xΦ₁` plus
fixed-base non-existence — to an **executable regression + a §13 row, shared with C.84's**. It is
not dischargeable here: `n2Exp` reads a `KeyFrame` and a `TowerDatum`, so a numeral row needs
§13's gate frames (C.123/C.124), exactly as C.15's `slotIdx` table, C.17's window rows and C.22's
`(2,2,3)` witness are all routed there. The **local substitute** is the three unfolding `example`s
below (`f₁ = f₂ = 1`; `f₁ = 2, f₂ = 1`; `f₁ = 1, f₂ = 2`), which pin the two things a numeral row
would pin about the *shape*: that `Δ(r, t) = e₁e₂h·r + e₂u₂·t` (so `Δ(0,0) = 0` and each leg
carries its own offset), and that `r` indexes the `β`-digit read (`stageCoord`) while `t` indexes
the `K₂`-coordinate (`k2Coord`) — an `r ↔ t` transposition, or an `e₁ ↔ e₂` swap in the exponent
offsets, cannot survive them.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The `t`-th `K`-coordinate of a `K₂`-element in the `β`-basis: read off a chosen
`AdjoinRoot.mk`-preimage of `s`, so a **section, not an invariant** (junk-stable; see the module
docstring). `k2DigitLift` reads it only at `t < T.f₂`, the basis range. -/
noncomputable def k2Coord {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (t : ℕ) :
    F.stageField H₀ hpin :=
  (((AdjoinRoot.mk_surjective s).choose).coeff t)

/-- The `n̂₂`-exponent solve at height `m`: the triple `(a₀, i, b)` with
`n̂₂(m) = π^{a₀} x^i Φ′^b`, i.e. `e₁e₂a₀ + i·e₂h + b·u₂ = m` with `i < e₁`, `b < e₂`.

Two steps, both junk-`0`-defaulting and hence TOTAL (D6's discipline): C.83's `towerSolve` at
`(u₂, e₂)` gives `b`; the reduced height `m' = (m − b·u₂)/e₂` then goes through C.15's frame solve
for `i = slotIdx m'` and `a₀ = (m' − i·h)/e₁`. The range clauses and the height equation are the
consumers' business (C.16 and its `(u₂, e₂)` instance), never this body's. -/
noncomputable def n2Exp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : ℕ × ℕ × ℕ :=
  let b := towerSolve T.u₂ T.e₂ m
  let m' := (m - b * T.u₂) / T.e₂
  ((m' - F.slotIdx m' * F.h) / F.e₁, F.slotIdx m', b)

/-- **NODE C.56a — the base-resolved K₂-digit lift**, `EFF.GENTOW1.27`'s `.62` TERMINAL display:

```
lift(s; m) = Σ_{r<f₁} Σ_{t<f₂} d_{r,t} · n̂₂(m − Δ(r,t)) · x^{e₁r} · Φ′^{e₂t},
Δ(r,t) = e₁e₂h·r + e₂u₂·t.
```

The digit `d_{r,t}` is `resLift (stageCoord (k2Coord T s t) r)` — the `K₂`-coordinate at `t`, its
`F_Q`-digit at `r`, lifted to `O` by C.14a's residue section. The base **RE-SOLVES per flavor**:
`n2Exp` is applied to the shifted height `m − Δ(r, t)`, not to a fixed `m`. The frozen fixed-base
variant is DEAD (its compensating `π`-exponent is non-integral at seam-live heights — FR-A's
`11/2 ∉ ℤ`). -/
noncomputable def k2DigitLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (m : ℕ) : Polynomial O :=
  ∑ r ∈ Finset.range F.f₁, ∑ t ∈ Finset.range T.f₂,
    Polynomial.C
        (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r)
          * π ^ (n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1)
      * Polynomial.X
          ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1 + F.e₁ * r)
      * F.key ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2 + T.e₂ * t)

end Uniformity.Density.Tower

/-! ## Unfolding checks — the flavor offsets at `(f₁, f₂) = (1,1), (2,1), (1,2)`

`example`s, not declarations: the local substitute for the FR-A numeral row that §13 owns (see the
module docstring's TEETH). Together they pin `Δ(r, t) = e₁e₂h·r + e₂u₂·t` on both legs and fix
which index feeds which coordinate read. -/

section UnfoldingChecks

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `(f₁, f₂) = (1, 1)`: the single flavor `(r, t) = (0, 0)` has `Δ = 0` and no exponent offsets —
the lift is the bare normalizer `n̂₂(m)` scaled by the one digit. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (s : AdjoinRoot (towerLabel T)) (m : ℕ) (h1 : F.f₁ = 1) (h2 : T.f₂ = 1) :
    k2DigitLift T s m
      = Polynomial.C
            (resLift (F.stageCoord H₀ hpin (k2Coord T s 0) 0) * π ^ (n2Exp T m).1)
          * Polynomial.X ^ (n2Exp T m).2.1
          * F.key ^ (n2Exp T m).2.2 := by
  rw [k2DigitLift, h1, h2]
  simp

/-- `(f₁, f₂) = (2, 1)`: the `r`-leg. The second flavor shifts the height by exactly `e₁e₂h` and
raises the `x`-exponent by exactly `e₁`, leaving the `Φ′`-exponent alone; the digit it reads is the
`r = 1` `β`-digit of the SAME `K₂`-coordinate `k2Coord T s 0`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (s : AdjoinRoot (towerLabel T)) (m : ℕ) (h1 : F.f₁ = 2) (h2 : T.f₂ = 1) :
    k2DigitLift T s m
      = (Polynomial.C
              (resLift (F.stageCoord H₀ hpin (k2Coord T s 0) 0) * π ^ (n2Exp T m).1)
            * Polynomial.X ^ (n2Exp T m).2.1
            * F.key ^ (n2Exp T m).2.2)
        + (Polynomial.C
              (resLift (F.stageCoord H₀ hpin (k2Coord T s 0) 1)
                * π ^ (n2Exp T (m - F.e₁ * T.e₂ * F.h)).1)
            * Polynomial.X ^ ((n2Exp T (m - F.e₁ * T.e₂ * F.h)).2.1 + F.e₁)
            * F.key ^ (n2Exp T (m - F.e₁ * T.e₂ * F.h)).2.2) := by
  rw [k2DigitLift, h1, h2, Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- `(f₁, f₂) = (1, 2)`: the `t`-leg. The second flavor shifts the height by exactly `e₂u₂` and
raises the `Φ′`-exponent by exactly `e₂`, leaving the `x`-exponent alone; the digit it reads is the
`r = 0` `β`-digit of the OTHER `K₂`-coordinate `k2Coord T s 1`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (s : AdjoinRoot (towerLabel T)) (m : ℕ) (h1 : F.f₁ = 1) (h2 : T.f₂ = 2) :
    k2DigitLift T s m
      = (Polynomial.C
              (resLift (F.stageCoord H₀ hpin (k2Coord T s 0) 0) * π ^ (n2Exp T m).1)
            * Polynomial.X ^ (n2Exp T m).2.1
            * F.key ^ (n2Exp T m).2.2)
        + (Polynomial.C
              (resLift (F.stageCoord H₀ hpin (k2Coord T s 1) 0)
                * π ^ (n2Exp T (m - T.e₂ * T.u₂)).1)
            * Polynomial.X ^ (n2Exp T (m - T.e₂ * T.u₂)).2.1
            * F.key ^ ((n2Exp T (m - T.e₂ * T.u₂)).2.2 + T.e₂)) := by
  rw [k2DigitLift, h1, h2, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_one]
  simp

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.k2Coord
#print axioms Uniformity.Density.Tower.n2Exp
#print axioms Uniformity.Density.Tower.k2DigitLift

end AxCheck
