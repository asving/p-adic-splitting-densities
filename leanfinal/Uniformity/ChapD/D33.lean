/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D10
import Uniformity.ChapD.D32

/-!
# Uniformity.ChapD.D33 — `(C3-canonical-read)`: the telescopes cancel slotwise

**Chapter D, NODE D.33** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5, the read
bundle and the B-law; amendments A-1, A-D.1, A-D.2 govern — none of them touches this node, so
the SIGNATURE below is the one signed at composition and re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`). ENV-D2 + ENV-D3. One signed declaration.

*`(C3-canonical-read)` and the three-reads cancellation.* Over a bundle `B : ReadBundle A q`
(D.29) and the dictionary (D.31): for slot `t < f` with `s := f − t` and coherent digit
`Γ_t = c_t·ϑ_{i,s}` (`ϑ := A.vartheta q s`), the per-grade unit read `u_B(s) = B.R (N.n (s·q))`
meets the coherent digit and the two telescopes cancel slotwise:

  `u_B(s) · Γ_t = c_t · w^s`.

That is the canonical read: `u_B(s)·Γ_t = w^s·Θ(s)·c_t·ϑ_{i,s}` by the B-law (D.32), and
`Θ(s)·ϑ_{i,s} = 1` by the involution (D.10), leaving `c_t·w^s`. Assembled over the slots this
is `(C3-three-reads)`: the residual `y^f − Σ_t u_B(f−t)·Γ_t·y^t` equals
`y^f − Σ_t c_t·w^{f−t}·y^t`, i.e. `(WF-psi)`'s display `w^f·ψ(y/w)` for `ψ = y^f − Σ c_t y^t`.
**The assembly is NOT this node** — the polynomial identity is D.35's `wtwist_psi` over D.58's
residual; this node proves exactly the COEFFICIENT identity `u_B(f−t)·Γ_t = c_t·w^{f−t}`, and
nothing downstream may read the display off it without the assembling node.

## ORIENTATION ⚠

**This is the ONE place both orientations meet**, and they meet through D.10's involution
`GaugeArena.theta_mul_vartheta` — never through a hand-written sign flip. D.32's B-law produces
`A.theta` (the inverse-telescope orientation, D.06 rows 2–3); the coherent digit carries
`A.vartheta` (T1's two-index `ϑ_{i,s}`, D.06 row 2); the product of the two is `1` because D.10
says so. A consumer that wants GENTOW2's single-argument `ϑ(t)` goes through D.10's
`varthetaG2_eq`, not through this statement.

D.06's warning, repeated verbatim, because this node is where a wrong direction would first
become invisible:

> **THE B-LAW DIRECTION — separate, and NOT to be conflated with the Θ/ϑ inversion.**
> `u(β) := R_{3,β}(n̂₂(β̂))` is an FGMN-side read of a repo-side object, and direction (3) of
> `LEMMA GENTOW2-B′` reads **`FGMN = u·repo`**, i.e. `R_{3,β}(g) = u(β)·digit(g)` — **NOT the
> inverse** (`EFF.GENTOW2.34`'s orientation record; the r2 F3 finding exists because a fallback
> clause once wrote the inverse convention). T1's `(C3-B-law)` `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`
> and T3's `(ABS-G2)` `u(β_t) = ϑ_{G2}(t)·w^{f₃−t}` agree in that orientation — all three sides
> consistent, and D.33 states the Lean form in exactly it.

## The slot indexing, and why `ht : t < f` is carried but not used

The grade bookkeeping `β_t = (f−t)·κ̄` is carried in the SLOT indexing at the consumer
(`(C3-slot-grade)`, D.32's note), so the only index this node's algebra sees is the exponent
`s = f − t`. The `ℕ`-truncated subtraction `f - t` is therefore harmless *as algebra*: the
identity holds for every `f t : ℕ`, including `t ≥ f` where `f - t = 0` and both sides are `c`.
`ht : t < f` is nevertheless part of the SIGNATURE and is kept: it is the domain on which the
slot reading `Γ_t = c_t·ϑ_{i,f−t}` is meaningful, and dropping it would let a consumer pass a
truncated grade and still typecheck. The hypothesis fences the READING, not the proof. The file
therefore carries `set_option linter.unusedVariables false in` on the one declaration — the
D.21/D.23/D.25b precedent, signature kept byte-exact.

## Faithfulness

No new mathematical content beyond D.32 and D.10: the proof is the B-law rewrite, `ring`, and
one `Units` cancellation. In particular this node does **not** discharge the bundle — D-H4(1)
stands: "T1 does not prove `u(β_t) = Θ(t)w^{f₃−t}` and does not import general factor-pattern
preservation into the pinned GENTOW2-B span" (`EFF.T1.31`, NON-IMPORTS A7). The B-law here is
proved FROM the read-bundle fields; INSTANTIATING those fields is somebody else's theorem
(chapter C at `i = 2` — D.42; `[GENTOW5-W(i)]`-conditional at `i ≥ 3` — D.44/D.62). At depth
`i ≥ 3` the scalars `ϑ_{i,s}`, `Θ_i(t)`, `c_tϑ` are `K_i`-scalars **only under
`(H-VARTHETA-RES)_i`** (D.67); the `Kˣ`-typing of `A.vartheta` carries that condition by type
and does not discharge it.

DEPENDS: D.08 (`GaugeArena.theta`, `GaugeArena.vartheta`) · D.10
(`GaugeArena.theta_mul_vartheta`, the involution) · D.32 (`ReadBundle.blaw`) · D.31
(`dict_iff`, the dictionary) — D.31 is consumed at the STATEMENT level only, in the reading of
the second factor as the coherent digit `Γ_t = c_t·ϑ`, so it is not imported: the Lean content
of the substitution is the literal product `c * (A.vartheta q (f - t) : K)`. The import of D.10
pulls D.06/D.08; the import of D.32 pulls D.29 (hence D.07). mathlib: `Units.val_mul`,
`Units.val_one`, `ring`.

**PROOF.** The blueprint's: D.32 + D.10's `theta_mul_vartheta` (`Units.val`-cast bookkeeping);
`ring`. "At the corrected key, `Γ_t = c_t ϑ` and `Θ = ϑ^{−1}` cancel slotwise" (`EFF.T1.15`,
verbatim).

SOURCE: `EFF.T1.15` (the boxed `(C3-canonical-read)` and `(C3-three-reads)`: the multiplicative
residual `ψ_{i+1}(y)`, coherent digits `(c_t ϑ_{i,f_{i+1}−t})`, canonical residual `ψ^{(w_i)}`);
`EFF.T5.18` (the same cancellation, T5's `Γ_t u_i(β_t) = c_t w_i^{s_t}` — D.63 is its
packaging); `EFF.T1.31` SPAN PIN 2 (`ψ₃^{(w)} = w^{f₃}ψ₃(y/w)` — supplied to GENTOW2's A7 span
by D.58 + this node).

**TEETH.** T1 §4.2 checks 5, 8, 9 + the inverse-orientation tooth → **Lean theorem** (this
node); gate D.67. T1 §4.2 check 5's full orientation tooth is scored across D.06/D.10/D.32/this
node plus gate D.65 leg 3 (all three `μ = 3` entries).

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]`,
`{N : NormSection G}`, written inline per the B.42 binder rule — this file has no `variable`
block; `A` and `q` are implicit, `B`, `f`, `t`, `ht`, `c` explicit, as signed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

-- `ht : t < f` is signed but not consumed: the cancellation is exponent-only algebra, valid at
-- every `f t : ℕ`, while `ht` fences the SLOT READING of the second factor. Kept, not removed.
set_option linter.unusedVariables false in
/-- **D.33 — `(C3-canonical-read)`: the telescopes cancel slotwise** (`EFF.T1.15`,
`EFF.T5.18`). For slot `t < f` with `s = f − t` and the coherent digit `Γ_t = c·ϑ_{i,s}`, the
per-grade unit read `u_B(s) = B.R (N.n (s·q))` satisfies `u_B(s)·Γ_t = c·w^s`.
⚠ ORIENTATION: the ONE place both orientations meet — the B-law (D.32) supplies `A.theta`, the
coherent digit carries `A.vartheta`, and they cancel by D.10's involution, never by a hand
sign flip. The B-law direction is `FGMN = u·repo` (D.06's warning, repeated in this file's
module docstring), and this statement is its Lean form.
⚠ This is the COEFFICIENT identity only; assembling `y^f − Σ_t u_B(f−t)·Γ_t·y^t = w^f·ψ(y/w)`
is D.35/D.58. -/
theorem ReadBundle.canonical_coeff {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (f t : ℕ) (ht : t < f) (c : K) :
    B.R (N.n ((f - t : ℕ) * q)) * (c * (A.vartheta q (f - t) : K))
      = c * (B.w : K) ^ (f - t) := by
  have hinv : (A.theta q (f - t) : K) * (A.vartheta q (f - t) : K) = 1 := by
    rw [← Units.val_mul, A.theta_mul_vartheta q (f - t), Units.val_one]
  rw [B.blaw (f - t)]
  calc (A.theta q (f - t) : K) * (B.w : K) ^ (f - t) * (c * (A.vartheta q (f - t) : K))
      = c * (B.w : K) ^ (f - t)
          * ((A.theta q (f - t) : K) * (A.vartheta q (f - t) : K)) := by ring
    _ = c * (B.w : K) ^ (f - t) := by rw [hinv, mul_one]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.ReadBundle.canonical_coeff

end AxCheck
