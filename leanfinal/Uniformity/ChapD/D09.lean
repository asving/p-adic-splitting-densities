/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D08

/-!
# Uniformity.ChapD.D09 — the top-slot anchor `ϑ_{i,0} = ϑ_{i,1} = 1`, `K`-valued

**Chapter D, NODE D.09** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern). ENV-D2 + ENV-D3. Two signed declarations,
both PROVED theorems here (the leanspec stub signs both as `axiom`s).

*The top-slot anchor (T3 §8.1 check 1; GENTOW2's `ϑ(f₃−1) = 1`).* For an arena
`A : GaugeArena G K N` (D.07) and any height `q : ℤ`:

* `A.vartheta q 0 = 1` — the height-zero normalization `n̂(0) = 1` (D.01's
  `(C2-zero-normalizer)`) read through `A.res`;
* `A.vartheta q 1 = 1` — the one-step telescope is empty, `n̂(q)¹·n̂(1·q)⁻¹ = 1`.

Since `theta = vartheta⁻¹` (D.10's involution), **the same endpoints hold in BOTH
orientations** (`1⁻¹ = 1`), which is exactly why the top slot (`t = f_{i+1}−1`, i.e. `s = 1`)
is the safe normalization anchor of the whole four-way orientation table: it is the one index
where a silent orientation swap cannot be detected, so it is the one index at which the table
may be pinned without prejudging the swap. See the anchor `D-THETA-TABLE` (D.06) — its
FRAME-C battery scores this pair, `ϑ_{G2}(f₃−1) = ϑ_1 = Θ_1 = 1`, as arithmetic.

DEPENDS: D.05 (`NormSection.varthetaEl_zero`, `NormSection.varthetaEl_one`, the group-level
endpoints) · D.08 (`GaugeArena.vartheta`, `GaugeArena.varthetaEl_mem_ker`), both landed under
`Uniformity.ChapD` · mathlib `map_one`, `Subtype.ext`.

**PROOF.** Push `A.res` through D.05's endpoint identities: the subtype element
`⟨N.varthetaEl q 0, _⟩ : MonoidHom.ker A.v` is `1` by `Subtype.ext` (the underlying group
element is `1`, and the kernel's unit has underlying element `1`), so `map_one A.res` closes
it; likewise at `s = 1`. No new mathematical content beyond D.05 — this node is D.05 under the
residue hom, which is the only form the consumers (D.32/D.33, the gates) can use.

SOURCE: `EFF.T3.03` (`ϑ_N(0;q) = ϑ_N(1;q) = 1`); `EFF.GENTOW2.41` ("`κ̄ = β_{f₃−1}` means
`ϑ(f₃−1) = res(n̂₂(u₃)/n̂₂(u₃)¹) = 1` — the top-slot normalization … T3 checks at its §8.1
item 1"); `EFF.T1.10` (`ϑ_{i,0} = ϑ_{i,1} = 1`).

**ORIENTATION.** BOTH (they agree at `s ∈ {0,1}`; D.06's anchor paragraph). This is the one
node of §3 whose statement is orientation-free, and the docstrings say so rather than picking
a row of the table.

**TEETH.** T3 §8.1(1) → **Lean theorem** (this node); executed at gate D.67 and, already
landed, at D.06's FRAME-C battery (`gate06varthetaG2 5 4 = 1 ∧ gate06vartheta 1 = 1 ∧
gate06theta 1 = 1`). Nothing is scored inside this file: it is algebra over an abstract field,
which admits no `decide`.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` and
`{N : NormSection G}`, written inline per the B.42 binder rule — this file has no `variable`
block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.09 — the telescope endpoint `ϑ_{i,0} = 1`, `K`-valued** (`EFF.T3.03`, `EFF.T1.10`):
`A.vartheta q 0 = 1`.  ORIENTATION: both — `theta q 0 = 1` follows from D.10's involution and
`1⁻¹ = 1`. -/
theorem GaugeArena.vartheta_zero {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) : A.vartheta q 0 = 1 := by
  have h : (⟨N.varthetaEl q 0, A.varthetaEl_mem_ker q 0⟩ : MonoidHom.ker A.v) = 1 :=
    Subtype.ext (N.varthetaEl_zero q)
  rw [GaugeArena.vartheta, h, map_one]

/-- **D.09 — the top-slot anchor `ϑ_{i,1} = 1`, `K`-valued** (`EFF.GENTOW2.41`'s
`ϑ(f₃−1) = 1`, at `s = f₃ − (f₃−1) = 1`): `A.vartheta q 1 = 1`.  This is THE normalization
anchor of the four-way orientation table (D.06): both orientations agree here, so pinning the
table at the top slot does not prejudge the orientation.  ORIENTATION: both. -/
theorem GaugeArena.vartheta_one {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) : A.vartheta q 1 = 1 := by
  have h : (⟨N.varthetaEl q 1, A.varthetaEl_mem_ker q 1⟩ : MonoidHom.ker A.v) = 1 :=
    Subtype.ext (N.varthetaEl_one q)
  rw [GaugeArena.vartheta, h, map_one]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.vartheta_zero
#print axioms Uniformity.Density.Gauge.GaugeArena.vartheta_one

end AxCheck
