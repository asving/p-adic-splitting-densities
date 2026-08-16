/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C06

/-!
# Uniformity.ChapC.C07 — the `dv`-side cluster: level sides as argmin data

**Chapter C, NODE C.07** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Six signed declarations, all
definitional, landed as one public cluster (the B.16/B.20 precedent, and D5's instruction).

**Ordering — stub-gate defect D12(i).** C.06 and C.07 are HOISTED above C.05: the landed order is
C.01 → C.02 → C.03 → C.04 → **C.06 → C.07** → C.05 → C.08.

*Level sides as argmin data.* Mirroring B.16/B.20 shape for shape, one level up, with C.06's
`dvHgt`/`dvSupp` in place of B.11's `npHgt` and B.14's `suppVal`:

| chapter B (order 0) | chapter C (level 1) |
| --- | --- |
| `OnSide φ f u ℓ j` (B.16 a) | `DvOnSide F f u ℓ j` |
| `sideSet φ f u ℓ` (B.16 b) | `dvSideSet F f u ℓ` |
| `sideMin` (B.20 a) | `dvSideMin` |
| `sideMax` (B.20 b) | `dvSideMax` |
| `sideDeg` (B.20 c) | `dvSideDeg` |
| — (no landed `sideLen`) | `dvSideLen` (D5, stub-side determination) |

The side of slope `−u/ℓ` is `EFF.HE6.10`'s side "of dv-slope `λ = u/ℓ` in lowest terms and length
`L_λ = ℓd_λ`". D-1/GC-2 forbid a polygon carrier, so a side is not a geometric object here: it is
the argmin `Finset` of the `ℕ`-linear form whose infimum defines `dvSupp`, and the side's numerals
are that `Finset`'s `min'`, `max'`, and their gap. C.08 supplies the arithmetic that makes the
numerals behave (`ℓ ∣ dvSideLen`, hence `dvSideLen = ℓ * dvSideDeg` exactly); nothing here
anticipates it.

## Two places where C.07 is NOT a literal copy of B.16/B.20

* **`DvOnSide` carries a finiteness guard that `OnSide` does not.** B.16's `OnSide` is the bare
  equation `ℓ • npHgt φ f j + u·j = suppVal φ f u ℓ`. The A-C.1-signed `DvOnSide` is a
  CONJUNCTION: the (orientation-flipped) equation **and** `dvHgt F f j ≠ ⊤`. The guard is
  load-bearing, not decoration — it is what keeps vacuous abscissae (`dev F.key f j = 0`, height
  `⊤`) off the side, which is precisely what C.08's mod-`ℓ` spacing argument needs in order to
  subtract heights in `ℕ`. The price is that the level-1 reconciliation is NOT an equality of side
  sets: at `f = 0, ℓ = 1` (any frame) every level height is `⊤`, so `dvSideSet F 0 u 1 = ∅` while
  `sideSet F.key 0 u 1 = {0}` — B's `OnSide` is satisfied there by `⊤ = ⊤`. This refutes the
  unsigned fourth prose bullet of C.05's STATEMENT; the counterexample is recorded in C05.lean's
  DELTA block, and the signed SIGNATUREs of both nodes are unaffected.
* **The equation is written in the opposite orientation.** B.16 writes `⟨form⟩ = suppVal`; the
  signed `DvOnSide` writes `dvSupp = ⟨form⟩`. Transcribed as signed. Consumers rewriting between
  the two levels need `Eq.symm`; it is not a defect, just a seam to know about.

## `dvSideLen` — stub-side determination D5

C.07's blueprint SIGNATURE block ends with the comment *"`dvSideMax`, `dvSideLen`, `dvSideDeg`
analogous (one file, one public cluster per B.20 precedent)"* and declares none of them, while
C.08/C.25/C.26/C.55 consume them. B.20's landed cluster is `sideMin`/`sideMax`/`sideDeg` — there
is **no landed `sideLen`** to copy (B.20 states the length identity as `sideMax_eq`, not as a
definition). The gate (`leanspec/Leanspec/ChapC.lean`, D5) therefore determined
`dvSideLen := dvSideMax - dvSideMin`, the only reading under which C.08(b)
`dvSideLen = ℓ * dvSideDeg` is the B.20(d) analogue, and A-C.1 adopted that text as signed. It is
transcribed here as adopted. Note the consequence: `dvSideDeg` and `dvSideLen` are independently
defined (`(max − min)/ℓ` and `max − min`), so the two are related only by C.08's exactness lemma,
not definitionally.

## Shape details, copied rather than chosen

* **The range bound.** `Finset.range (f.natDegree + 1)` — the same range `dvSupp` (C.06) takes its
  `inf` over, so the filter cannot miss an attaining abscissa. B.16's bound verbatim.
* **Decidability.** `DvOnSide` is `Prop`-valued and not decidable, so `dvSideSet` filters under
  `open Classical in`, exactly as B.16's `sideSet` does; this is why the whole cluster from
  `dvSideSet` down is `noncomputable`.
* **The `Nonempty` argument.** `dvSideMin`/`dvSideMax` take `Finset.min'`/`max'`'s nonemptiness
  proof explicitly, as B.20 does, and `dvSideDeg`/`dvSideLen` thread the same proof through. The
  chapter-C analogue of B.18's `sideSet_nonempty` (which discharges it) is not a §3 node.
* **Truncated subtraction and division.** `max − min` is `ℕ`-truncated and `/ ℓ` is `ℕ`-floored.
  Both are exact on the intended inputs by C.08 (`min ≤ max` because both are members of the same
  `Finset`; `ℓ ∣ max − min` by the mod-`ℓ` spacing law). At `ℓ = 0` the division floors to `0`;
  no signed consumer passes `ℓ = 0` (C.08 and C.09 both carry `0 < ℓ`).

**DEPENDS.** C.06 (`dvHgt`, `dvSupp`) · B.16 · B.20 (the shape templates) — all by committed node
ID (GC-13(b)). The import is `Uniformity.ChapC.C06`.

**PROOF.** Definitional (with `Classical` decidability for the filter, as in B.16). The bodies are
the gate-verified `leanspec/Leanspec/ChapC.lean` stub bodies (the §3 A-C.1 layer) verbatim.

SOURCE: `EFF.HE6.10` ("sides have dv-slope `λ = u/ℓ` in lowest terms and length `L_λ = ℓd_λ`");
GC-2 (the argmin representation, D-1's three-object polygon).

**TEETH.** Signed non-applicable (definitions). The side numerals are audited numerically at
blueprint §13's frame gates and proved exact at C.08.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.07 (a) — the on-side predicate at the `dv`-level.** The abscissa `j` attains the cleared
level support at slope `−u/ℓ`, AND its level height is finite. The second conjunct has no B.16
counterpart; it is what keeps vacuous abscissae off the side (see the file docstring). -/
def DvOnSide (F : KeyFrame O π) (f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) ∧ dvHgt F f j ≠ ⊤

/-- **C.07 (b) — the on-side abscissae, as a `Finset`.** Filtered out of the same uniform range
`Finset.range (f.natDegree + 1)` over which `dvSupp` takes its `inf`, with `Classical`
decidability for the `Prop`-valued `DvOnSide` (B.16's `sideSet`, one level up). -/
noncomputable def dvSideSet (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (fun j => DvOnSide F f u ℓ j)

/-- **C.07 (c) — the side's left endpoint** (`EFF.HE3.14`'s `j₀`, one level up). -/
noncomputable def dvSideMin (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).min' h

-- D5: the blueprint says "dvSideMax, dvSideLen, dvSideDeg analogous (one file, one public cluster
-- per B.20 precedent)" and declares none of them, while C.08/C.25/C.26/C.55 consume them. B.20's
-- landed cluster is `sideMin`/`sideMax`/`sideDeg` — there is NO landed `sideLen`, so `dvSideLen`
-- below has no template and is the gate's stub-side determination, adopted as signed text at
-- A-C.1.
/-- **C.07 (d) — the side's right endpoint.** -/
noncomputable def dvSideMax (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).max' h

/-- **C.07 (e) — the side's residual degree** `d_λ`: the horizontal length divided by `ℓ`. The
`ℕ`-division is exact on the intended inputs by C.08's spacing law; it is floored here. -/
noncomputable def dvSideDeg (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  (dvSideMax F f u ℓ h - dvSideMin F f u ℓ h) / ℓ

/-- **C.07 (f) — the side's horizontal length** `L_λ`. **Stub-side determination (D5):** no
landed `sideLen` exists to copy; this is the only reading under which C.08(b)
`dvSideLen = ℓ * dvSideDeg` is the B.20(d) analogue. -/
noncomputable def dvSideLen (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  dvSideMax F f u ℓ h - dvSideMin F f u ℓ h

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DvOnSide
#print axioms Uniformity.Density.Tower.dvSideSet
#print axioms Uniformity.Density.Tower.dvSideMin
#print axioms Uniformity.Density.Tower.dvSideMax
#print axioms Uniformity.Density.Tower.dvSideDeg
#print axioms Uniformity.Density.Tower.dvSideLen

end AxCheck
