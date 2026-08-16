/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D10
import Uniformity.ChapD.D35
import Uniformity.ChapD.D44

/-!
# Uniformity.ChapD.D58 — `(WF-realized)`: the realized-residual cancellation

**Chapter D, NODE D.58** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §8, the w-frame
(T5); amendments A-1, A-D.1 and A-D.2 govern the chapter — none of them re-signs this node
(A-D.2 touches D.62/D.63 only), so the SIGNATURE below is the composition-time one, re-stubbed
at stage 0e in `leanspec/Leanspec/ChapD.lean`). ENV-D2 + ENV-D3. One signed declaration.

*`(WF-realized)`.* Given the sitewise B-law `GentowW A q R w` (D.44) and digits
`c : Fin f → K` under the **coherent recipe** `Γ_t = c_t·ϑ_{i,s_t}` (`EFF.T5.18`: "Whenever
the relevant (WF-law) equality is available"), the read coefficients cancel slotwise,

> `R (N.n (s_t·q)) · (c_t · ϑ_{i,s_t}) = c_t · w^{s_t}`,  `s_t = f − t`

(D.33's shape, now sourced from `GentowW` rather than from a `ReadBundle`), and hence the
assembled residual equals the twist:

> `y^f − Σ_{t<f} R(N.n(s_t·q))·Γ_t·y^t = wtwist w (y^f − Σ_{t<f} c_t·y^t)`,

i.e. `R_ν(Φ_{i+1}) = ψ_{i+1}^{(w_i)}` at the coefficient level. This file is the ASSEMBLY that
D.33's docstring defers to ("the polynomial identity is D.35's `wtwist_psi` over D.58's
residual") and that D.35's docstring anticipates ("the target of D.58's slotwise
cancellation").

## The scope split, transcribed — the conditionality lives OUTSIDE this theorem

`hW` is a hypothesis. Nothing here supplies it, and the two rungs get it from different
places (`EFF.T5.19`'s two-arrow display, `EFF.T5.20`'s supplier attribution):

* **`i = 2` — `(WF-realized₂)`, unconditional.** `hW` is chapter C's landed GENTOW2-B″
  instance, `EFF.GENTOW2.43 [supplied-by: chapter C]`, recorded at D.56 with D.42's port route
  (`BoundaryReadPort.t3_br`, D.38, plus `gentowW_of_ports`, D.44) as its derivation. No `𝒲`
  hypothesis enters: `𝒲_{≤2}` is the empty conjunction (D.55's `Wle W 2`, `EFF.T5.13`).
* **`i ≥ 3` — `(WF-realizedᵢ)`, twice conditional.** The display is
  `𝒲_{≤i} ⟹ (WF-law)ᵢ ⟹ R_{ν_i}(Φ_{i+1}) = ψ_{i+1}^{(w_i)}`: D.57 (`Wle W i → W i`) extracts
  the last conjunct, and only then does this theorem fire. Riding on top of that, and NOT to
  be conflated with it (`EFF.T5.10`: "a SECOND conditional stack on the same displays"), every
  `i ≥ 3` use of `Θ_i(t)`/`ϑ_{i,s}` as a `K_i`-scalar carries `(H-VARTHETA-RES)_i` (D.62), and
  every `w_i` site carries `(C3-ladder-nonvanishing)` — the latter typed away by `w : Kˣ`
  (D.29/D.44, D-H6), the former NOT: the `Kˣ`-typing of `A.vartheta` carries the residue
  condition by type and does not discharge it (D.33's faithfulness note, restated because this
  node is the one that assembles those scalars into a polynomial).

The supplier attribution is `EFF.T5.20`, quoted: *"T1 supplies the dictionary and the final
cancellation. GENTOW2-B″ supplies the unconditional `i = 2` B-law. At `i ≥ 3`,
`[GENTOW5-W(i)]` supplies the sitewise B-law only within the displayed cumulative
hypothesis."* — which is exactly this node's dependency shape: D.10/D.34/D.35 are the T1 side
(landed here), `hW` is the supplier side (a hypothesis).

## Faithfulness (trust boundary)

1. **No new mathematics beyond D.33 + D.35.** The coefficient leg is D.33's cancellation with
   `B.blaw` replaced by `hW` — same two ingredients, the B-law rewrite and D.10's involution
   `Units`-cast — and the assembly leg is a `Finset.sum_congr` into `wtwist_psi`. The proof
   introduces no case split, no nonvanishing side condition, and no `Polynomial` lemma beyond
   D.35's.
2. **The `ℕ`-truncated exponent is honest.** Every occurrence of the length is the same
   `ℕ`-subtraction `f - (t : ℕ)` on both sides, with `t : Fin f`, so `t < f` always holds and
   the truncation is never reached; the statement's exponent is `f - t` in `ℕ` (the ascription
   `(f - (t : ℕ) : ℕ)` inside `N.n`'s argument is what keeps the ladder index a coerced
   `ℕ`-difference rather than an `ℤ`-difference, matching `GentowW`'s `N.n (s * q)`).
3. **`R` is an arbitrary function `G → K`**, evaluated only at the ladder points, exactly as at
   D.44: nothing here asserts that `R` is a residue read of anything, and nothing constrains it
   off the ladder. The digit family `c` is arbitrary too — the coherent recipe `Γ_t = c_t·ϑ` is
   *written into the statement* (the literal product `c t * (A.vartheta q (f - t) : K)`), not
   imposed on `c`.
4. **This node discharges no instance.** As at D.44: converting a supplied law into a
   polynomial identity is not building the law. Chapter D never exhibits `hW` at `i ≥ 3`.

**DEPENDS.** D.10 (`GaugeArena.theta_mul_vartheta`, the involution) · D.34 (`wtwist`, reaching
this file through D.35's import of D34a) · D.35 (`wtwist_psi`, the assembly) · D.44
(`GentowW`, the hypothesis; its import pulls D.37/D.38, hence D.08/D.01). mathlib:
`Units.val_mul`, `Units.val_one`, `Finset.sum_congr`, `ring`.

**PROOF** (the blueprint's, in two steps). 1. *Coefficientwise*: `hW` at `s = f − t`, then
`Θ·ϑ = 1` (D.10) — "Substituting (WF-law) into `Γ_t u_i(β_t)` cancels
`ϑ_{i,s_t}ϑ_{i,s_t}^{−1} = 1`, leaving `c_t w_i^{s_t}` — exactly the coefficient of `y^t` in
(WF-psi)" (`EFF.T5.18`, verbatim). 2. *Assemble* with D.35's `wtwist_psi`.

**SOURCE.** `EFF.T5.18` (the corollary and the boxed `(WF-realized₂)`), `EFF.T5.19` (the boxed
`(WF-realizedᵢ)` two-arrow form), `EFF.T5.20` (the supplier attribution quoted above);
`EFF.T1.15`/`EFF.T1.31` SPAN PIN 2 for the T1 side of the same identity
(`ψ₃^{(w)} = w^{f₃}ψ₃(y/w)`, supplied to GENTOW2's A7 span by this node together with D.33).

**ORIENTATION.** The cancellation site — both orientations meet here, and they meet through
D.10, exactly as at D.33: `hW`/`GentowW` produces `A.theta` (D.06 rows 2–3, the B-law
orientation), the coherent digit carries `A.vartheta` (D.06 row 2, T1's two-index `ϑ_{i,s}`),
and their product is `1` because `GaugeArena.theta_mul_vartheta` says so — never by a
hand-written sign flip. A statement with the two orientations swapped is well-typed and wrong;
gate D.67's FRAME-C `U·ϑ = w^s` identity is this cancellation's numeric shadow.

**TEETH.** T5 §7 Pass 1(2)/Pass 2(2) → **Lean theorem** (this node); gate D.67.

**ENVIRONMENT.** ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]`,
`{N : NormSection G}` written inline per the B.42 binder rule — this file has no `variable`
block; `A`, `q`, `R`, `w` implicit, `hW`, `f`, `c` explicit, as signed).

## Status

Sorry-free, axiom-free (Lean core only): `gentowW_realized` is PROVED here, not the leanspec
`axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.58 — `(WF-realized)`: the realized-residual cancellation** (`EFF.T5.18`–`.20`).
Under the sitewise B-law `GentowW A q R w` (D.44) and the coherent digit recipe
`Γ_t = c_t·ϑ_{i,f−t}`, the assembled residual equals the `w`-twist of the bare residual:

```
y^f − Σ_{t<f} R(N.n((f−t)q))·(c_t·ϑ_{i,f−t})·y^t  =  wtwist w (y^f − Σ_{t<f} c_t·y^t)
```

— `R_ν(Φ_{i+1}) = ψ_{i+1}^{(w_i)}` at the coefficient level.

⚠ **The conditionality is in `hW`, not in this theorem.** At `i = 2` the hypothesis is
chapter C's GENTOW2-B″ instance, unconditionally (D.56); at `i ≥ 3` it is reached only from
`Wle W i` through D.57, and the `Θ_i`-scalars additionally carry `(H-VARTHETA-RES)_i` (D.62),
a SECOND stack that must not be conflated with `𝒲_{≤i}`.
⚠ ORIENTATION: `hW` supplies `A.theta`, the digit carries `A.vartheta`, and they cancel by
D.10's involution — never by a hand sign flip. -/
theorem gentowW_realized {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (hW : GentowW A q R w) (f : ℕ) (c : Fin f → K) :
    (Polynomial.X ^ f
      - ∑ t : Fin f, Polynomial.C
          (R (N.n ((f - (t : ℕ) : ℕ) * q)) * (c t * (A.vartheta q (f - (t : ℕ)) : K)))
          * Polynomial.X ^ (t : ℕ))
    = wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ)) := by
  -- Step 1 (D.33's cancellation, now from `hW`): the slotwise coefficient identity.
  have hcoeff : ∀ t : Fin f,
      R (N.n ((f - (t : ℕ) : ℕ) * q)) * (c t * (A.vartheta q (f - (t : ℕ)) : K))
        = c t * (w : K) ^ (f - (t : ℕ)) := by
    intro t
    have hinv : (A.theta q (f - (t : ℕ)) : K) * (A.vartheta q (f - (t : ℕ)) : K) = 1 := by
      rw [← Units.val_mul, A.theta_mul_vartheta q (f - (t : ℕ)), Units.val_one]
    rw [hW (f - (t : ℕ))]
    calc (A.theta q (f - (t : ℕ)) : K) * (w : K) ^ (f - (t : ℕ))
            * (c t * (A.vartheta q (f - (t : ℕ)) : K))
        = c t * (w : K) ^ (f - (t : ℕ))
            * ((A.theta q (f - (t : ℕ)) : K) * (A.vartheta q (f - (t : ℕ)) : K)) := by ring
      _ = c t * (w : K) ^ (f - (t : ℕ)) := by rw [hinv, mul_one]
  -- Step 2 (D.35): the rewritten coefficients are exactly `wtwist_psi`'s.
  simp only [hcoeff]
  rw [wtwist_psi]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.gentowW_realized

end AxCheck
