/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D08
import Uniformity.ChapD.D29

/-!
# Uniformity.ChapD.D32 — `(C3-Theta)`/`(C3-B-law)`: the B-law from the read bundle

**Chapter D, NODE D.32** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5, the read
bundle and the B-law; amendments A-1, A-D.1, A-D.2 govern — none of them touches this node, so
the SIGNATURE below is the one signed at composition and re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`). ENV-D2 + ENV-D3. One signed declaration.

*The B-law from the bundle.* Over a bundle `B : ReadBundle A q` (D.29) define the **per-grade
unit read** `u_B(s) := B.R (N.n (s·q))` — T5's `u_i(β_t) := R_{i+1,β_t}(n̂_i(s_t u_{i+1}))`,
`EFF.T5.11`. Then for every `s : ℕ`

  `u_B(s) = Θ(s) · w^s`,

and in slot-indexed form with `s = f_{i+1} − t` this reads `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`.
The grade bookkeeping `β_t = (f_{i+1}−t)·κ̄_i` is carried in the SLOT indexing at the consumer
(D.33, D.58, D.62), not as a separate Lean object — that is `(C3-slot-grade)`, and it is why
this node's only index is the exponent `s`.

## ORIENTATION ⚠

**The B-law direction of D.06's B-law block: `FGMN = u · repo`, never the inverse.** The factor
that appears is `A.theta` (D.08's `Θ`, D.06 rows 2–3 — the inverse-telescope orientation), NOT
`A.vartheta`. `EFF.T1.14`'s own derivation is phrased as "ladder multiplicativity gives
`R(N^s) = w^s`; scalar covariance … invert the telescope"; the inversion is performed HERE, once,
so that no consumer is left holding an un-inverted `ϑ` to flip on its own. A consumer wanting the
`ϑ` orientation goes through D.10's involution (`theta_mul_vartheta`) — that is exactly what D.33
does, and D.33 is the one place both orientations meet.

## Why this is a theorem and not a bundle field

D.29 carries `EFF.T1.03`'s five site clauses; it does NOT carry the B-law. The B-law is a
two-line consequence of three of those clauses plus §3's group-level telescope, and keeping it a
theorem is what makes D.29's countermodels bite: a packaging that asserted `u_B(s) = Θ(s)w^s` as
a field would be satisfied by reads that violate scalar covariance off the ladder. The
derivation below uses `ladder_mult` and `scalar_cov` and nothing else (`read_n` is not needed —
it is `ladder_mult` at `s = 1`, D.29's recorded D-D14).

## Faithfulness

No new mathematical content beyond D.04/D.08 and the bundle's own fields: the entire proof is
the group identity `n(sq) = n(q)^s · Θ_el(q,s)` (D.04's `thetaEl` definition rearranged, valid in
any commutative group) pushed through the two multiplicativity clauses. The one substantive
modelling choice is upstream, at D.29 — that `w` is typed in `Kˣ`, so the statement needs no
`w ≠ 0` hypothesis (D-H6).

DEPENDS: D.04 (`NormSection.thetaEl`) · D.08 (`GaugeArena.thetaEl_mem_ker`, `GaugeArena.theta`) ·
D.29 (`ReadBundle`, its `ladder_mult` and `scalar_cov` fields), all landed under
`Uniformity.ChapD` (the import of D.08 pulls D.04 through D.05; the import of D.29 pulls D.07) ·
mathlib `MonoidHom.ker`, `Units`, `mul_comm`. D.10's involution is deliberately NOT a dependency
— this node produces the `Θ` orientation directly.

**PROOF.** 1. `n(s·q) = n(q)^s · Θ_el(q,s)` in `G`: unfold `NormSection.thetaEl` and `group`
(the ladder power commutes past its own inverse). 2. `Θ_el(q,s) ∈ ker v` is D.08's
`thetaEl_mem_ker`, so `scalar_cov` applies at `X := n(q)^s`, `g := ⟨Θ_el(q,s), _⟩`, giving
`R(n(sq)) = R(n(q)^s) · res g`. 3. `R(n(q)^s) = w^s` is `ladder_mult`; `res ⟨Θ_el(q,s), _⟩` is
D.08's `A.theta q s` by definitional unfolding (`rfl`). 4. `mul_comm` puts the display in the
signed order `Θ·w^s`. This is `EFF.T1.14`'s derivation run FORWARDS — stated in the `Θ`
orientation with no inversion step left to the consumer.

SOURCE: `EFF.T1.14` (the boxed `(C3-Theta)`, `(C3-slot-grade)`, `(C3-B-law)`); `EFF.T3.14` (the
SAME algebra from port hypotheses — D.38's deliberate duplication, see its ⚠); `EFF.T5.14`
(the consequent that D.62 fires this node into); `EFF.T5.11` (`u_i(β_t)`, the per-grade unit
read this node's LHS spells).

**TEETH.** T1 §4.2 check 5 + the inverse-orientation tooth → **Lean theorem** (this node);
gate D.67's `U(s) = Θ_s w^s` numeric leg scores the same display against a concrete bundle.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]`,
`{N : NormSection G}`, written inline per the B.42 binder rule — this file has no `variable`
block; `A` and `q` are implicit, `B` and `s` explicit, as signed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.32 — `(C3-Theta)`/`(C3-B-law)`: the B-law from the bundle** (`EFF.T1.14`). The
per-grade unit read `u_B(s) = B.R (N.n (s·q))` factors as `Θ(s)·w^s`; in slot-indexed form
with `s = f_{i+1} − t` this is `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`.
⚠ ORIENTATION: the B-law direction of D.06 (`FGMN = u · repo`), never the inverse — the factor
is `A.theta`, and the inversion `EFF.T1.14` leaves to "invert the telescope" is performed here,
once. The `ϑ` orientation is reached through D.10's involution (D.33). -/
theorem ReadBundle.blaw {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (s : ℕ) :
    B.R (N.n (s * q)) = (A.theta q s : K) * (B.w : K) ^ s := by
  calc B.R (N.n ((s : ℤ) * q))
      = B.R ((N.n q) ^ s
          * ((⟨N.thetaEl q s, A.thetaEl_mem_ker q s⟩ : MonoidHom.ker A.v) : G)) := by
        congr 1
        change N.n ((s : ℤ) * q) = (N.n q) ^ s * N.thetaEl q s
        rw [NormSection.thetaEl, mul_comm (N.n ((s : ℤ) * q)) ((N.n q ^ s)⁻¹),
          mul_inv_cancel_left]
    _ = B.R ((N.n q) ^ s) * (A.res ⟨N.thetaEl q s, A.thetaEl_mem_ker q s⟩ : K) :=
        B.scalar_cov _ _
    _ = (B.w : K) ^ s * (A.theta q s : K) := by rw [B.ladder_mult s]; rfl
    _ = (A.theta q s : K) * (B.w : K) ^ s := mul_comm _ _

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.ReadBundle.blaw

end AxCheck
