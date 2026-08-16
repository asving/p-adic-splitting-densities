/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D02
import Uniformity.ChapD.D04

/-!
# Uniformity.ChapD.D05 — the telescope endpoints and recursion, at group level

**Chapter D, NODE D.05** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — this node's signature is unamended).
ENV-D2. Three public declarations (the recursion plus its two endpoints, same file — the
STATEMENT displays all three and the gate-verified stub signs all three).

*Telescope endpoints and recursion `(C2-recursion)`/`(T1-TEL)`, group level.* For a normalizer
section `N` (D.01), a ladder step `q : ℤ` and `s : ℕ`:

  `ϑ_0 = 1`,  `ϑ_1 = 1`,  `ϑ_{s+1} = ϑ_s · τ(s·q, q)`,

where `ϑ_s = varthetaEl N q s = n(q)^s·n(sq)⁻¹` is D.04's T1-orientation telescope and `τ` is
D.02's normalizer cocycle. This node is the GROUP-LEVEL half of `EFF.T1.10`'s boxed
`(C2-recursion)`; the residue half (`res` applied through D.07's interface, giving the
`Kˣ`-valued `ϑ_{i,s}`) is D.08, and the `ϑ_0 = ϑ_1 = 1` normalization anchor reappears
residue-side at D.09.

## ORIENTATION

**T1 two-index (D.06 row 1)** — anchor `D-THETA-TABLE`, the GC-14 canonical copy; this file
states its convention and does not restate the table. Two consequences the recursion pins:

* *the `τ`-factor is on the RIGHT of the product.* `ϑ_{s+1} = ϑ_s·τ(sq,q)`, and its arguments
  are `(s·q, q)` in that order — the step height first, the ladder step second. T1 §4.2
  check 2 (positive-wrap / wrong-sign) is the discipline this guards: a mutant that writes
  `τ(q, sq)` survives on a commutative `G` but a mutant that writes `ϑ_{s+1} = τ(sq,q)·ϑ_{s+1}`
  or flips the telescope orientation does not, because `varthetaEl` (not `thetaEl`) is the
  object being recursed.
* *the endpoints are orientation-free.* `ϑ_0 = ϑ_1 = 1` holds in BOTH orientations, since
  `1⁻¹ = 1` (D.06's top-slot anchor paragraph); that is why the same two facts anchor the
  GENTOW2 slot convention at `t = f₃−1` and the T1 convention at `s ∈ {0,1}`.

## Faithfulness

**⚠ Trust-boundary transcription.** Three points, flagged for the chapter cross-read:

* *`s : ℕ` and the cast are the source's quantifier.* `EFF.T3.03` quantifies "For `s ≥ 0`",
  D.04 carries that as `s : ℕ`, and the recursion's `N.tau (s * q) q` reads `↑s * q : ℤ` —
  the only cast in the file, discharged once by `push_cast; ring` (`((s+1 : ℕ) : ℤ)·q =
  ↑s·q + q`). No lemma here is stated at negative `s`, and none is needed: the telescope is
  built upward from `s = 0`.
* *this is the group half ONLY.* No `res`, no `Kˣ`, no arena: `EFF.T1.10`'s residue statement
  `ϑ_{i,s+1} = ϑ_{i,s}·res(τ_i(su_{i+1},u_{i+1}))` is D.08, obtained by pushing D.07's
  `res` monoid hom through THESE identities. Landing the group half abstractly is DECISION
  D-1's licence (honesty item D-H3): level 1 (§4), the `i = 2` GENTOW2 instance and the
  depth-`i ≥ 3` conditional layer are then instances of one theorem.
* *the endpoints are separately public.* `varthetaEl_zero` consumes D.01's `n_zero` (through
  `(0 : ℕ)·q = 0`); `varthetaEl_one` consumes nothing but `pow_one`/`one_mul` and the group
  axioms. They are landed as named theorems rather than left as `simp` corollaries so that
  D.09 and the §10 gates cite a name.

DEPENDS: D.01 (`NormSection`, `n_zero`), D.02 (`NormSection.tau`), D.04
(`NormSection.varthetaEl`) — all landed at `Uniformity.ChapD.D01/D02/D04`.

**PROOF.** The blueprint's, executed. 1. `varthetaEl q 0 = (n q)^0·(n 0)⁻¹ = 1` by `pow_zero`,
the cast arithmetic `((0 : ℕ) : ℤ)·q = 0` and `N.n_zero`. 2. `varthetaEl q 1 = n q·(n q)⁻¹ = 1`
by `pow_one` and `one_mul` on the cast height. 3. Recursion: after the cast rewrite
`((s+1 : ℕ) : ℤ)·q = ↑s·q + q` (`push_cast; ring`) and `pow_succ`, both sides are
`n(q)^s·n(q)·n(↑s·q + q)⁻¹` — the RHS's `n(↑s·q)⁻¹` meets D.02's `τ`-numerator `n(↑s·q)`
adjacently, so `group` (no commutativity needed) closes it. This is the corpus derivation
"Factor `N(u)^{s+1}/N((s+1)u)` through `N(su)`" (`EFF.T1.10`).

SOURCE: `EFF.T1.10` (the boxed `(C2-recursion)`: `ϑ_{i,0} = ϑ_{i,1} = 1`,
`ϑ_{i,s+1} = ϑ_{i,s}·res(τ_i(su_{i+1},u_{i+1}))` — this node is its group-level half; the
residue half is D.08); `EFF.T3.03` (`(T1-TEL)`, the abstract `ϑ_N(s;q)` telescope).

**TEETH.** T3 §8.1(1) (endpoints) and §8.1(2) (recurrence) → Lean theorems (this node) +
executable at gates D.65–D.67; T1 §4.2 check 2 (positive-wrap / wrong-sign) → the recursion's
`τ`-factor is on the RIGHT of the product, the sign discipline that check guards.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule —
this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only). All three are PROVED theorems here, not the leanspec
`axiom` stubs.
-/

namespace Uniformity.Density.Gauge

/-- Telescope endpoint `ϑ_{i,0} = 1` (`EFF.T1.10` `(C2-recursion)`; consumes D.01's
`(C2-zero-normalizer)`).  ORIENTATION: T1 two-index (D.06 row 1) — but the endpoints agree in
both orientations. -/
theorem NormSection.varthetaEl_zero {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) :
    N.varthetaEl q 0 = 1 := by
  simp [NormSection.varthetaEl, N.n_zero]

/-- Telescope endpoint `ϑ_{i,1} = 1` (`EFF.T1.10` `(C2-recursion)`).  ORIENTATION: T1
two-index (D.06 row 1); this is the top-slot anchor `ϑ(f₃−1) = 1` of `EFF.GENTOW2.41` read at
`s = 1`. -/
theorem NormSection.varthetaEl_one {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) :
    N.varthetaEl q 1 = 1 := by
  simp [NormSection.varthetaEl]

/-- The telescope recursion `(C2-recursion)` / `(T1-TEL)` at group level:
`ϑ_{s+1} = ϑ_s·τ(sq, q)` (`EFF.T1.10`, `EFF.T3.03`).  The `τ`-factor stands on the RIGHT and
its arguments are `(s·q, q)` in that order — the wrong-sign discipline of T1 §4.2 check 2.
ORIENTATION: T1 two-index (D.06 row 1). -/
theorem NormSection.varthetaEl_succ {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.varthetaEl q (s + 1) = N.varthetaEl q s * N.tau (s * q) q := by
  have hcast : ((s + 1 : ℕ) : ℤ) * q = (s : ℤ) * q + q := by push_cast; ring
  simp only [NormSection.varthetaEl, NormSection.tau, hcast, pow_succ]
  group

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.varthetaEl_zero
#print axioms Uniformity.Density.Gauge.NormSection.varthetaEl_one
#print axioms Uniformity.Density.Gauge.NormSection.varthetaEl_succ

end AxCheck
