/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D06
import Uniformity.ChapD.D08

/-!
# Uniformity.ChapD.D10 — the orientation involution, `K`-valued, and the GENTOW2 alias

**Chapter D, NODE D.10** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern). ENV-D2 + ENV-D3. Three signed
declarations: the involution, the row-1 alias, and the alias's defining lemma (the leanspec
stub signs the two lemmas as `axiom`s; both are PROVED here).

*The orientation involution and the GENTOW2 alias (T3 §8.1 check 2 as a Lean lemma).*

* (i) `A.theta q s * A.vartheta q s = 1` — the `K`-valued inversion. This is D.06's group
  identity `thetaEl_mul_varthetaEl` pushed through the arena's residue hom `A.res`, and it is
  the ONE place where the two orientations of the four-way table meet (D.32/D.33, D.58 and
  gate D.67 all cancel their telescopes slotwise through it).
* (ii) the slot-indexed alias `varthetaG2 A q f t := A.theta q (f − t)` — GENTOW2's
  single-argument unit (anchor `D-THETA-TABLE`, D.06 **row 1**): its argument is the SLOT `t`,
  its value the INVERSE-orientation telescope at `s = f − t`. The defining lemma
  `varthetaG2 A q f t = (A.vartheta q (f − t))⁻¹` is what a consumer reads when it wants row 1
  in terms of T1's two-index `ϑ_{i,s}`.

⚠ **The subtraction `f − t` is `ℕ`-truncated**, deliberately and harmlessly: the alias is only
ever read at slots `t < f` (D.06's `t < f₃`), and at `t ≥ f` it degenerates to
`A.theta q 0 = 1`, which is the same value the honest `s = 0` endpoint carries (D.09). No node
consumes it outside the slot range.

## Why the alias is a REAL name (sanctioned GC-6.5 exception)

Three public declarations where GC-6.5 would default to one. The exception is scoped to
exactly `varthetaG2` and its defining lemma: the D.06 table **mandates that row 1 have a Lean
name** so that chapters C, E and F can cite the reference object without restating its
definition in their own words — restating it is precisely the append-#54 trap ("a sign error
no battery catches"). `theta` alone will not do: it is indexed by the telescope length `s`,
not by the slot `t`, and the whole content of row 1 is the reindexing `s = f − t`.

DEPENDS: D.06 (`NormSection.thetaEl_mul_varthetaEl`, the group inversion) · D.08
(`GaugeArena.vartheta`, `GaugeArena.theta`, the membership lemmas), both landed under
`Uniformity.ChapD` · mathlib `map_mul`, `map_one`, `Subtype.ext`, `eq_inv_of_mul_eq_one_left`.

**PROOF.** (i) `← map_mul` collapses the two residues to one, and the resulting kernel element
`⟨thetaEl q s, _⟩ * ⟨varthetaEl q s, _⟩` is `1` by `Subtype.ext` of D.06's identity; `map_one`
finishes. (ii) the alias is definitional; its lemma is `eq_inv_of_mul_eq_one_left` applied to
(i) at `s = f − t`.

SOURCE: `EFF.T3.04` (+ its §8.1 check 2, "recurrence/inverse orientation");
`EFF.GENTOW2.25`/`.41` (the single-argument convention and the `s := f₃ − t` reindexing).

**ORIENTATION.** the involution itself — D.06 rows 1–3 made a theorem. Row 1 (`varthetaG2`,
GENTOW2) and row 4 (GENTOW5-A1's `theta_t` = `vartheta` at argument `t`, NOT `f−t`) are
RECIPROCAL and numerically distinct; D.06's landed FRAME-C battery scores the distinctness
(`gate06varthetaG2 5 2 ≠ gate06A1theta 2`, and the reflection is not the identity either at
`t = 1`/`t = 4` — finding D-F3), so a silent swap of the two rows now fails a `decide`.

**TEETH.** T3 §8.4(4) "inverse-orientation mutant" → **Lean theorem** (this node); T1 §4.2
check 5 (the full orientation tooth) → D.06/D.10/D.32/D.33; executed at gate D.67 leg 4 and,
already landed, at D.06's FRAME-C battery. Nothing is scored inside this file: it is algebra
over an abstract field, which admits no `decide`.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` and
`{N : NormSection G}`, written inline per the B.42 binder rule — this file has no `variable`
block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.10 — the orientation involution, `K`-valued** (`EFF.T3.04`, T3 §8.1 check 2):
`Θ_N(s;q)·ϑ_N(s;q) = 1`.  The `K`-valued form of D.06's group identity, and the ONE site where
the two rows of the orientation table meet.  ORIENTATION: the involution itself — D.06
rows 1–3 made a theorem. -/
theorem GaugeArena.theta_mul_vartheta {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    A.theta q s * A.vartheta q s = 1 := by
  have h : (⟨N.thetaEl q s, A.thetaEl_mem_ker q s⟩ : MonoidHom.ker A.v)
      * ⟨N.varthetaEl q s, A.varthetaEl_mem_ker q s⟩ = 1 :=
    Subtype.ext (N.thetaEl_mul_varthetaEl q s)
  rw [GaugeArena.theta, GaugeArena.vartheta, ← map_mul, h, map_one]

/-- **D.10 — GENTOW2's single-argument slot-indexed ϑ** (anchor `D-THETA-TABLE`, D.06 **row
1**; `EFF.GENTOW2.25`/`.41`): `ϑ(t) = Θ(f−t)`.  The argument is the SLOT `t`, the value the
INVERSE-orientation telescope at length `s = f − t`.  ⚠ `f − t` is `ℕ`-truncated; the alias is
read only at `t < f`.  ORIENTATION: D.06 row 1 = rows 2/3 at the reflected index — NOT row 4
(GENTOW5-A1's `theta_t`, which is `vartheta` at argument `t`). -/
noncomputable def GaugeArena.varthetaG2 {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (f t : ℕ) : Kˣ := A.theta q (f - t)

/-- **D.10 — the defining lemma of the row-1 alias**: `ϑ_{G2}(t) = ϑ_{i,f−t}⁻¹`, i.e. GENTOW2's
unit is the INVERSE of T1's two-index telescope read at the reflected index (`EFF.T3.04`'s
`(T1-THETA)`).  A consumer wanting GENTOW2's `ϑ(t)` reads THIS, never `vartheta` with a silent
sign flip.  ORIENTATION: the reindexing itself. -/
theorem GaugeArena.varthetaG2_eq {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (f t : ℕ) :
    A.varthetaG2 q f t = (A.vartheta q (f - t))⁻¹ :=
  eq_inv_of_mul_eq_one_left (A.theta_mul_vartheta q (f - t))

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.theta_mul_vartheta
#print axioms Uniformity.Density.Gauge.GaugeArena.varthetaG2
#print axioms Uniformity.Density.Gauge.GaugeArena.varthetaG2_eq

end AxCheck
