/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapD.D31 — `(C3-dictionary)`: the coherent/multiplicative digit dictionary

**Chapter D, NODE D.31** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5; amendments A-1
and A-D.1 govern — neither touches this node, so the SIGNATURE below is the one signed at
composition and re-stubbed at stage 0e in `leanspec/Leanspec/ChapD.lean`). ENV-D3 — the
residue-field arena: a bare field `K`, no valuation, nothing counted. One signed declaration.

*`(C3-dictionary)`.* For `Γ c : K` and a unit `ϑ : Kˣ`: `Γ = c · ϑ ↔ c = Γ · ϑ⁻¹` — the
coherent/multiplicative digit dictionary `Γ_t = c_t^{mult}·ϑ_{i,s}`,
`c_t^{mult} = Γ_t·ϑ_{i,s}^{−1}`. **Stated as an iff so neither orientation can be consumed
without the other being available**: a consumer that holds only the coherent digit and a
consumer that holds only the multiplicative digit get the same lemma, and no downstream node can
quietly use one direction while the other is unavailable.

**Why `ϑ : Kˣ` and not `ϑ : K` with a side condition.** `EFF.T1.09`'s conditionality is exactly
"`ϑ_{i,s}` must be a `K_i`-unit"; the `Kˣ` argument IS that condition, discharged by
construction at the call site rather than carried as a hypothesis. At depth `i ≥ 3` supplying it
is `(H-VARTHETA-RES)_i` — chapter D's carrier node D.62, governed by AMENDMENT A-D.2 / DECISION
D-2, which this node does not consume and must not be read as discharging.

**ORIENTATION (the inverse-orientation tooth's site).** The dictionary pairs GENTOW2-orientation
`ϑ(t)`-values with T1's `ϑ_{i,s}` per the ϑ four-way orientation table (anchor `D-THETA-TABLE`,
node D.06). Consumers must pass the CORRECT unit: T1's `vartheta` at `s = f − t`, i.e.
`varthetaG2⁻¹`. Nothing in this node's statement can detect a wrong-orientation argument — it is
true for every unit — so the orientation obligation is the CALLER's, and the executable trap for
it is gate D.67's FRAME-C battery, not this lemma.

DEPENDS: none (field algebra; `Units.mul_inv_cancel_right` / `Units.inv_mul_cancel_right`).

**PROOF.** Both directions substitute and cancel the unit: `c·ϑ·ϑ⁻¹ = c` and `Γ·ϑ⁻¹·ϑ = Γ`.

SOURCE: `EFF.T1.11` (the boxed `(C3-dictionary)`; the conditionality "`ϑ_{i,s}` must be a
`K_i`-unit under `EFF.T1.09`"); `EFF.T3.05` (`(T1-DICT)`, with T3's fence "T3 does NOT cite that
conditional conclusion [the B-law] as a premise" — respected here: this node is dictionary-only
and mentions no read, no telescope and no `Θ`).

**TEETH.** T1 §4.2 checks 2 and 5; the inverse-orientation tooth → D.06/D.10 + gate D.67.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.31 — `(C3-dictionary)`.** For a unit `ϑ : Kˣ`, the coherent digit `Γ` and the
multiplicative digit `c` determine each other: `Γ = c * ϑ ↔ c = Γ * ϑ⁻¹`. The iff is the signed
form, so a consumer of either orientation automatically has the other. The caller owes the
orientation of `ϑ` (D.06's table); the lemma itself holds for every unit. -/
theorem dict_iff {K : Type*} [Field K] (Γ c : K) (ϑ : Kˣ) :
    Γ = c * ϑ ↔ c = Γ * (ϑ⁻¹ : Kˣ) := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.dict_iff

end AxCheck
