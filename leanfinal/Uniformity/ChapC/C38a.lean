/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C11

/-!
# Uniformity.ChapC.C38a — the `dv2`-side cluster: level-2 sides as argmin data

**Chapter C, NODE C.38a** [def, RE-PLAN'd helper cluster] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5, booked inside NODE C.38's SIGNATURE block: *"The
`dv2ResPoly` + `dv2SideSet` companion cluster is hereby the booked NODE C.38a (the §15 RE-PLAN
executed; full defs at the node's leanspec twin)"*; amendment A-C.1(e) records the node-count
bump 128 → 129 and the census `+1 def`). The signed bodies are the gate-verified twin at
`leanspec/Leanspec/ChapC.lean:1504-1546`. ENV-C2.

*Level-2 sides as argmin data.* The cluster mirrors C.07 shape for shape, one level up, with
C.11's `dv2Pin`/`dv2Supp` in place of C.06's `dvHgt`/`dvSupp` — the fourth turn of the crank
C.06 and C.11 already documented as the second and third:

| level | on-side predicate | side set | endpoints, degree |
| --- | --- | --- | --- |
| 0 (B.16/B.20) | `OnSide φ f u ℓ j` | `sideSet` | `sideMin`/`sideMax`/`sideDeg` |
| 1 (C.07) | `DvOnSide F f u ℓ j` | `dvSideSet` | `dvSideMin`/`dvSideMax`/`dvSideDeg` |
| 2 (here) | `Dv2OnSide L Ψ f u₂ ℓ₂ j` | `dv2SideSet` | `dv2SideMin`/`dv2SideMax`/`dv2SideDeg` |

D-1/GC-2 still forbid a polygon carrier, so a level-2 side is not a geometric object: it is the
argmin `Finset` of the `ℕ`-linear form whose infimum defines `dv2Supp` (C.11), and the side's
numerals are that `Finset`'s `min'`, `max'`, and their gap divided by `ℓ₂`.

## What this file lands, and what it does NOT (clause split, recorded)

NODE C.38a's signed twin has **seven** declarations in two independent halves:

* **clause 1 — the side geometry (LANDED HERE):** `Dv2OnSide`, `dv2SideSet`, `dv2SideMin`,
  `dv2SideMax`, `dv2SideDeg`. These call only C.11's `dv2Supp`/`dv2Pin`, both landed
  (`C11.lean`), so they are transcribable today. They are what C.55 (`towerLocus_depth3_floor`),
  C.64 (`mult₂_readable`), C.65 (`dv2_length_sum`) and C.68 (`dv2Pin_translation_interior`)
  consume — none of those four statements mentions the residual half — so this is not an orphan
  landing.
* **clause 2 — the residual read (NOT LANDED; blocked):** `dv2Res` and `dv2ResPoly`. `dv2Res L A`
  is by its A-C.1 determination *"`A`'s own `dvResPoly` evaluated at the letter `β`"*
  (`AdjoinRoot.mk L.r`), and `dvResPoly` is **NODE C.25**, which has no file in
  `leanfinal/Uniformity/ChapC/` (`grep -rn dvResPoly leanfinal/Uniformity/` finds only a prose
  mention in `C09.lean`; there is no `C25.lean`). `dvResPoly` is a public node `def`, not a
  private helper, so it may not be re-declared locally under the standing D9 pattern — that would
  fork the definition. **RESCHEDULE C.38a clause 2 behind C.25.** The reschedule record is
  `leanfinal/notes/RESCHEDULE_C38a_clause2_2026-08-16.md`; the node is **not** complete until
  clause 2 lands in this file. Downstream of clause 2 and therefore also waiting: C.38
  (`dv2ResPoly_radical_eq`), C.39 (`γg`, `pinHeight`, `dv2ResPoly_scalar`), and §10's `repoRead`
  (C.104's `repoRead := dv2Res`).

## Shape details, copied rather than chosen

* **Two slopes, again.** `L.u`/`L.ℓ` (C.09 fields) are the **level-1** side at which the level-2
  slot heights are read, and are consumed inside `dv2Pin`; `u₂`/`ℓ₂` are the **level-2** slope
  numerals of the polygon being supported. C.11's warning carries over verbatim: they are never
  identified, and `dv2SideSet L Ψ f L.u L.ℓ` is not a distinguished instance of anything.
* **The finiteness guard is inherited from C.07, not from B.16.** `Dv2OnSide` is a CONJUNCTION:
  the (C.07-orientation) equation `dv2Supp = ℓ₂ • dv2Pin j + u₂·j` **and** `dv2Pin L Ψ f j ≠ ⊤`.
  As at level 1, the guard keeps vacuous abscissae off the side; here `dv2Pin L Ψ f j = ⊤` is
  exactly `dvSupp F (dev Ψ f j) L.u L.ℓ = ⊤`, which C.117's file docstring records as holding
  precisely when `dev Ψ f j = 0`. Consequence, stated in the negative because it is what a
  consumer will trip on: `dv2SideSet` is **not** the argmin of `dv2Supp` — it is the argmin
  intersected with the finite-pin locus, and the two differ at `f = 0`.
* **The equation orientation.** Written `dv2Supp = ⟨form⟩`, i.e. C.07's orientation, not B.16's
  `⟨form⟩ = suppVal`. Transcribed as signed; consumers rewriting across levels need `Eq.symm`.
* **The range bound.** `Finset.range (f.natDegree + 1)` — the same range `dv2Supp` (C.11) takes
  its `inf` over, so the filter cannot miss an attaining abscissa. B.16's bound, inherited
  through C.07 and C.11.
* **The `ℕ∞` coercion seam, for the fourth time.** The linear term is written `(u₂ * j : ℕ∞)`,
  the product of the two casts, matching C.11's `dv2Supp` body syntactically (so `Dv2OnSide`'s
  equation can be compared against `dv2Supp`'s defining `inf` without a `Nat.cast_mul` step).
* **Decidability.** `Dv2OnSide` is `Prop`-valued and not decidable, so `dv2SideSet` filters under
  `open Classical in`, exactly as `dvSideSet` (C.07) and `sideSet` (B.16) do; this is why the
  whole cluster from `dv2SideSet` down is `noncomputable`.
* **Truncated subtraction and division.** `max − min` is `ℕ`-truncated and `/ ℓ₂` is `ℕ`-floored.
  `min ≤ max` always (both are members of the same `Finset`); `ℓ₂ ∣ max − min` is the level-2
  analogue of C.08's spacing law and is **not** proved anywhere in the chapter — no signed
  consumer needs it, and `dv2SideDeg` is floored regardless. At `ℓ₂ = 0` the division floors to
  `0`; no signed consumer passes `ℓ₂ = 0` (C.38/C.39/C.64/C.68 all carry `0 < ℓ₂`, C.55 carries
  `0 < ℓ₃`).
* **No `dv2SideLen`.** Unlike C.07 (whose `dvSideLen` was the D5 stub-side determination), the
  signed C.38a twin declares no length. The `Σ dv2SideLen = mult₂` form that appears in C.65's
  prose is explicitly *"the fleet's argmin-partition corollary — recorded"*, i.e. unsigned; C.65's
  signed statement uses `dv2SideMax` alone. Nothing is added here.

**DEPENDS.** C.11 (`dv2Pin`, `dv2Supp`) · C.09 (`LevelDatum`) · C.07 · B.16 · B.20 (the shape
templates) — all by committed node ID (GC-13(b)). The import is `Uniformity.ChapC.C11`, which
pulls C.06/C.09 and through them C.01/C.02/C.03 and the B chain.

**PROOF.** Definitional (with `Classical` decidability for the filter, as in C.07/B.16). The
bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub bodies verbatim.

SOURCE: `EFF.HE6R1.13`(b)/(c) (the above-seam sides whose translation and radical clauses C.37 and
C.38 state — this cluster is the carrier those statements are written against); GC-2 (the argmin
representation at every level, D-1's three-object polygon).

**TEETH.** Signed non-applicable (definitions). The level-2 side numerals are audited numerically
at blueprint §13's frame gates and are the subject of C.64/C.65's exactness statements.

ENVIRONMENT: ENV-C2.

## Status

Clause 1 of 2. Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.38a (a) — the on-side predicate at the `dv₂`-level.** The abscissa `j` attains the
cleared level-2 support at slope `−u₂/ℓ₂`, AND its level-2 pin is finite. C.07's `DvOnSide` one
level up; the second conjunct is the same vacuous-abscissa guard (see the file docstring). -/
def Dv2OnSide {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ j : ℕ) : Prop :=
  dv2Supp L Ψ f u₂ ℓ₂ = ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞) ∧ dv2Pin L Ψ f j ≠ ⊤

/-- **C.38a (b) — the on-side abscissae of the level-2 polygon, as a `Finset`.** Filtered out of
the same uniform range `Finset.range (f.natDegree + 1)` over which `dv2Supp` (C.11) takes its
`inf`, with `Classical` decidability for the `Prop`-valued `Dv2OnSide`. -/
noncomputable def dv2SideSet {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (fun j => Dv2OnSide L Ψ f u₂ ℓ₂ j)

/-- **C.38a (c) — the level-2 side's left endpoint.** PE3 F-1's index `m₁`-carrier: C.39's
`pinHeight` reads the pin here. -/
noncomputable def dv2SideMin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideSet L Ψ f u₂ ℓ₂).min' h

/-- **C.38a (d) — the level-2 side's right endpoint.** C.65 bounds it by `mult₂`. -/
noncomputable def dv2SideMax {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideSet L Ψ f u₂ ℓ₂).max' h

/-- **C.38a (e) — the level-2 side's residual degree** `L_{λ₂}/ℓ₂`: the horizontal length divided
by `ℓ₂`, floored (see the docstring's truncation note). This is the numeral C.38's degree clause
equates across the block projection, and clause 2's `dv2ResPoly` sums to it. -/
noncomputable def dv2SideDeg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideMax L Ψ f u₂ ℓ₂ h - dv2SideMin L Ψ f u₂ ℓ₂ h) / ℓ₂

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Dv2OnSide
#print axioms Uniformity.Density.Tower.dv2SideSet
#print axioms Uniformity.Density.Tower.dv2SideMin
#print axioms Uniformity.Density.Tower.dv2SideMax
#print axioms Uniformity.Density.Tower.dv2SideDeg

end AxCheck
