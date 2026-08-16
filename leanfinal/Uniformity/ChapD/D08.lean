/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D05
import Uniformity.ChapD.D07

/-!
# Uniformity.ChapD.D08 — the `K`-valued telescope `vartheta` / `theta` and its recursion

**Chapter D, NODE D.08** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the
abstract cocycle arena; amendments A-1, A-D.1, A-D.2 govern — A-D.1/SD-1 re-signed the
membership-lemma names, FOUR of them, all PROVED and never `axiom`s). ENV-D2 + ENV-D3.
Seven signed declarations: four kernel-membership facts, two telescope definitions, one
recursion lemma.

*The `K`-valued telescope.* For an arena `A : GaugeArena G K N` (D.07):

* (i) every §3 combination is value-zero — `varthetaEl N q s ∈ A.v.ker` by exact-height
  arithmetic (`v((n q)^s · (n (s·q))⁻¹) = ofAdd (s·q − s·q) = 1`), and likewise `thetaEl` and
  `tau`; so the `Kˣ`-valued residues
  `A.vartheta q s := A.res ⟨N.varthetaEl q s, _⟩` and `A.theta q s := A.res ⟨N.thetaEl q s, _⟩`
  are defined;
* (ii) the residue recursion `(C2-recursion)`, `K`-half:
  `A.vartheta q (s+1) = A.vartheta q s * A.res ⟨N.tau (s·q) q, _⟩` — D.05's group identity
  pushed through the hom `A.res`.

## The four membership lemmas are PROVED, by design (A-D.1 / stub-side note SD-1)

`mem_ker_div` is the engine (equal heights ⟹ the ratio is value-zero); the other three are
its `varthetaEl` / `thetaEl` / `tau` instances. They are consumed INSIDE the `def` bodies of
`vartheta` and `theta` — an `axiom` (or a tactic hole) there would put a stub inside a
definition, so the whole node would carry it in every downstream footprint. The name
`tau_mem_ker` is the A-D.1 gate correction of the originally-signed `tauEl_mem_ker`: D.02's
cocycle is `tau`, and `tauEl` names nothing.

## Faithfulness

No new mathematical content beyond D.05 and D.07: this node is `A.res` applied to already-proved
group identities, plus the arithmetic that licenses the application. In particular
**this file is value-zero algebra only** (D.07 FAITHFULNESS (ii)): the positive-grade read
obligations `R_{i+1,β}` are D.29's `ReadBundle`, sitewise, not this node's — the split is the
blueprint's and is deliberate.

DEPENDS: D.02 (`NormSection.tau`) · D.04 (`NormSection.varthetaEl`, `NormSection.thetaEl`) ·
D.05 (`NormSection.varthetaEl_succ`, the group-level recursion) · D.07 (`GaugeArena`), all
landed under `Uniformity.ChapD` · mathlib `MonoidHom.ker`, `Multiplicative.ofAdd`,
`ofAdd_nsmul`, `ofAdd_add`.

**PROOF.** 1. Membership: `map_mul` / `map_pow` / `map_inv` on `A.v`, then `A.exact_height`
three times, then the `ofAdd` exponents cancel (`ofAdd_nsmul` / `ofAdd_add` + `simp`).
2. Recursion: `A.res` is a `MonoidHom`, so `map_mul` reduces the goal to the `Subgroup`
coercion bookkeeping `⟨varthetaEl q (s+1), _⟩ = ⟨varthetaEl q s, _⟩ * ⟨tau (s·q) q, _⟩`, which
is `Subtype.ext` of D.05's `varthetaEl_succ`. The four membership bodies are the gate-verified
`leanspec/Leanspec/ChapD.lean` stub bodies verbatim, with the landed namespace restored.

SOURCE: `EFF.T1.09` (the residue-level `(C2-vartheta)`); `EFF.T1.10` (the residue recursion);
`EFF.T3.03`.

**ORIENTATION.** `vartheta` = T1 two-index (D.06 row 2's `ϑ_{i,s}`); `theta` = the B-law
orientation (D.06 rows 2–3). The canonical four-way table is D.06, anchor `D-THETA-TABLE`.

**TEETH.** T3 §8.1(2) → **Lean theorem** (this node's recursion). T1 §4.2 checks 5/8/9 (the
read-bundle sites) guard D.29's bundle, NOT this node — the split is deliberate, per the
FAITHFULNESS note above. Nothing is scored inside this file: it is algebra over an abstract
field, which admits no `decide`; the numeric telescope tables run at D.06 and the §10 gates.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` and
`{N : NormSection G}`, written inline per the B.42 binder rule — this file has no `variable`
block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.08 — the membership engine.** Two elements of EQUAL height have a value-zero ratio,
so `A.res` applies to it. Every §3 combination (`tau`, `varthetaEl`, `thetaEl`, and D.12's
`chi` for two sections with the same `v`) is such a ratio. PROVED, not `axiom`: it is consumed
inside the `def` bodies below (A-D.1 / note SD-1). -/
theorem GaugeArena.mem_ker_div {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) {x y : G} (h : A.v x = A.v y) : x * y⁻¹ ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

/-- **D.08 — `varthetaEl` is value-zero**: `v((n q)^s·(n (s·q))⁻¹) = ofAdd (s·q − s·q) = 1`
by `exact_height` (`EFF.T1.09`). -/
theorem GaugeArena.varthetaEl_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    N.varthetaEl q s ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.varthetaEl, map_mul, map_inv, map_pow, A.exact_height,
    A.exact_height, ← ofAdd_nsmul]
  simp

/-- **D.08 — `thetaEl` is value-zero**: the same computation as `varthetaEl_mem_ker` with the
two factors exchanged (the inverse orientation, D.06 rows 2–3). -/
theorem GaugeArena.thetaEl_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    N.thetaEl q s ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.thetaEl, map_mul, map_inv, map_pow, A.exact_height,
    A.exact_height, ← ofAdd_nsmul]
  simp

/-- **D.08 — the cocycle is value-zero**: `v(n a · n b · (n (a+b))⁻¹) = ofAdd (a + b − (a+b))
= 1` (`EFF.T1.08`). ⚠ NAME: A-D.1 gate correction of the originally-signed `tauEl_mem_ker` —
D.02's cocycle is `tau`, so `tauEl` names nothing. -/
theorem GaugeArena.tau_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (a b : ℤ) :
    N.tau a b ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.tau, map_mul, map_mul, map_inv, A.exact_height,
    A.exact_height, A.exact_height]
  simp [← ofAdd_add]

/-- **D.08 — the `K`-valued telescope, T1 orientation** (`EFF.T1.09` `(C2-vartheta)`):
`ϑ_{i,s} = res(n̂(q)^s / n̂(s·q))`.  ORIENTATION: T1 two-index (D.06 row 2's `ϑ_{i,s}`). -/
noncomputable def GaugeArena.vartheta {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) : Kˣ :=
  A.res ⟨N.varthetaEl q s, A.varthetaEl_mem_ker q s⟩

/-- **D.08 — the `K`-valued telescope, B-law (inverse) orientation** (`EFF.T3.04` `(T1-THETA)`,
`EFF.T1.14` `(C3-Theta)`): `Θ_N(s;q) = res(n̂(s·q) / n̂(q)^s)`.  ORIENTATION: the inverse of
`vartheta` (D.06 rows 2–3); the involution itself is D.10. -/
noncomputable def GaugeArena.theta {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) : Kˣ :=
  A.res ⟨N.thetaEl q s, A.thetaEl_mem_ker q s⟩

/-- **D.08 — the residue recursion `(C2-recursion)`, `K`-half** (`EFF.T1.10`, `EFF.T3.03`):
`ϑ_{s+1} = ϑ_s · res(τ(s·q, q))`.  The `τ`-factor stands on the RIGHT and its arguments are
`(s·q, q)` in that order — D.05's wrong-sign discipline (T1 §4.2 check 2) carried through
`A.res`.  ORIENTATION: T1 two-index. -/
theorem GaugeArena.vartheta_succ {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    A.vartheta q (s + 1) = A.vartheta q s * A.res ⟨N.tau (s * q) q, A.tau_mem_ker (s * q) q⟩ := by
  rw [GaugeArena.vartheta, GaugeArena.vartheta, ← map_mul]
  exact congrArg A.res (Subtype.ext (N.varthetaEl_succ q s))

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.mem_ker_div
#print axioms Uniformity.Density.Gauge.GaugeArena.varthetaEl_mem_ker
#print axioms Uniformity.Density.Gauge.GaugeArena.thetaEl_mem_ker
#print axioms Uniformity.Density.Gauge.GaugeArena.tau_mem_ker
#print axioms Uniformity.Density.Gauge.GaugeArena.vartheta
#print axioms Uniformity.Density.Gauge.GaugeArena.theta
#print axioms Uniformity.Density.Gauge.GaugeArena.vartheta_succ

end AxCheck
