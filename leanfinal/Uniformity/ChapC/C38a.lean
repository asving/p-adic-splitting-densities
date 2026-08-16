/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C11
import Uniformity.ChapC.C25

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

## The cluster's two halves

NODE C.38a's signed twin has **seven** declarations in two independent halves, all landed here:

* **the side geometry:** `Dv2OnSide`, `dv2SideSet`, `dv2SideMin`, `dv2SideMax`, `dv2SideDeg` —
  the table above. These call only C.11's `dv2Supp`/`dv2Pin`. They are what C.55
  (`towerLocus_depth3_floor`), C.64 (`mult₂_readable`), C.65 (`dv2_length_sum`) and C.68
  (`dv2Pin_translation_interior`) consume; none of those four statements mentions the residual
  half.
* **the residual read:** `dv2Res` and `dv2ResPoly` — the `K₂`-valued half. This is what C.38
  (`dv2ResPoly_radical_eq`), C.39 (`γg := dv2Res L (f /ₘ blockFactor L f)`,
  `dv2ResPoly_scalar`) and §10's `repoRead := dv2Res` (C.104) consume.

**Landing history.** The two halves were committed separately (`ac84a745`, then this file's
second landing) because `dvResPoly` — NODE C.25, which `dv2Res` calls — had no file in
`leanfinal/Uniformity/ChapC/` at the start of the wave-7 slot. C.25 landed mid-slot at commit
`495eb769`, and the residual half went in against it. The interim reschedule record
`leanfinal/notes/RESCHEDULE_C38a_clause2_2026-08-16.md` is therefore **superseded** and is kept
only for the C.25-fanout scheduling table it carries.

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

## The residual half: three things the `def`s do NOT say

* **`dv2Res` is a `dif`, and its `else` branch is junk `0`, not a value.** The A-C.1
  determination reads *"`dv2Res A` is the coherent `K₂`-read: `A`'s own `dvResPoly` evaluated at
  the letter `β` (`AdjoinRoot.mk L.r`)"*. To call `dvResPoly` at all one needs C.25's two
  arguments — a nonempty level-1 side set for `A` at the level's own side `(L.u, L.ℓ)`, and a
  natural number `M₀` witnessing that the `dvSideMin` pin is finite — so the body branches on the
  existence of that pair and returns `0` when it fails. This is B.28's junk-0 discipline, the
  same one C.25's own `twistRead` calls rely on, and it is what makes the read **total** so that
  `γg` (C.39) and `repoRead` (C.104) can be stated without carrying side conditions. Consumers
  must not read `dv2Res L A = 0` as "the residue vanishes": off the pinned locus it means "not
  pinned". The A-C.1 determination is signed, so this is transcription, not a choice made here.
* **`Exists.choose`, so the witnesses are non-canonical.** The `then` branch feeds
  `h.choose`/`h.choose_spec.choose`/`h.choose_spec.choose_spec` into `dvResPoly`. `h.choose` is a
  proof of a `Prop` (`Finset.Nonempty`) and so is irrelevant, but `M₀ := h.choose_spec.choose` is
  data, pinned only up to the equation `dvHgt F A (dvSideMin F A L.u L.ℓ h.choose) = (M₀ : ℕ∞)`.
  That equation determines `M₀` uniquely (`Nat.cast` is injective on `ℕ∞`), so the value is in
  fact canonical — but only *provably* so, via a lemma nobody has stated. Anything rewriting
  under `dv2Res` needs that uniqueness step; it is not definitional.
* **`dv2ResPoly` sums to `dv2SideDeg`, not to the side's length.** The index range is
  `Finset.range (dv2SideDeg … + 1)` with the `t`-th coefficient read at abscissa
  `dv2SideMin + t·ℓ₂` — C.25's shape one level up, with `dv2Res` in place of `twistRead`. The
  claim that its `natDegree` is `dv2SideDeg` (i.e. that the top coefficient is nonzero) is C.26's
  analogue and is **not** a §5 node; C.38's degree clause compares two `natDegree`s and does not
  need it.

**DEPENDS.** C.11 (`dv2Pin`, `dv2Supp`) · C.09 (`LevelDatum`, its `u`/`ℓ`/`r` fields) · C.07
(`dvSideSet`, `dvSideMin`) · C.06 (`dvHgt`) · C.25 (`dvResPoly`) · B.02 (`dev`) · B.16 · B.20
(the shape templates) — all by committed node ID (GC-13(b)). The imports are
`Uniformity.ChapC.C11` and `Uniformity.ChapC.C25`, which between them pull C.06/C.07/C.09/C.22
and through them C.01/C.02/C.03 and the B chain.

**PROOF.** Definitional (with `Classical` decidability for the filter, as in C.07/B.16). The
bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub bodies verbatim.

SOURCE: `EFF.HE6R1.13`(b)/(c) (the above-seam sides whose translation and radical clauses C.37 and
C.38 state — this cluster is the carrier those statements are written against); GC-2 (the argmin
representation at every level, D-1's three-object polygon).

**TEETH.** Signed non-applicable (definitions). The level-2 side numerals are audited numerically
at blueprint §13's frame gates and are the subject of C.64/C.65's exactness statements.

ENVIRONMENT: ENV-C2.

## Status

NODE C.38a COMPLETE (all seven signed declarations). Sorry-free, axiom-free (Lean core only).
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

/-- **C.38a (f) — the coherent `K₂`-residue read of one coefficient**: its own level residual
polynomial (C.25's `dvResPoly`, taken at the level's own side `(L.u, L.ℓ)`) evaluated at the
letter `β`, i.e. mapped through `AdjoinRoot.mk L.r`. Junk `0` off the pinned locus, so the read
is total — see the docstring: `dv2Res L A = 0` means "not pinned", NOT "residue vanishes". -/
noncomputable def dv2Res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : AdjoinRoot L.r :=
  open Classical in
  if h : ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M₀ : ℕ∞)
  then AdjoinRoot.mk L.r
    (dvResPoly F H₀ hpin A L.u L.ℓ h.choose h.choose_spec.choose h.choose_spec.choose_spec)
  else 0

/-- **C.38a (g) — the level-2 residual polynomial over `K₂`** (C.25 one level up, assembled from
the per-slot coherent reads): `Σ_{t ≤ d₂} C (dv2Res L (dev Ψ f (j₁ + t·ℓ₂))) · X^t`, with
`j₁ := dv2SideMin` and `d₂ := dv2SideDeg`. This is the object C.38's radical clause and C.39's
scalar identity are stated about. -/
noncomputable def dv2ResPoly {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (dv2Res L (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)))
      * Polynomial.X ^ t

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Dv2OnSide
#print axioms Uniformity.Density.Tower.dv2SideSet
#print axioms Uniformity.Density.Tower.dv2SideMin
#print axioms Uniformity.Density.Tower.dv2SideMax
#print axioms Uniformity.Density.Tower.dv2SideDeg
#print axioms Uniformity.Density.Tower.dv2Res
#print axioms Uniformity.Density.Tower.dv2ResPoly

end AxCheck
