/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL27_reductionInterface
import LeanUrat.HC1.CL11_posUniq

/-!
# HC1.CL12_nclAssembly — NCL: the ℤ_[p] assembly (BP5 CL-12, display (10))

**Unit CL-12** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4,
REWRITTEN at REVISION 2, findings 4/5/9 — the interface work lives in CL-27; this
unit is application-sized). **GATED on CL-10's clean outcome** (countermodel-first;
risk R-1): no prover works this unit before the CL-10 probe completes — if CL-10
finds a cancellation, this statement is FALSE as stated and R6 escalates to
adjudication (window-guard (i-b) / NCL as a named pack law / re-fence).

**Informal statement (display (10) — NCL, no-cancellation at a level).** For a
digit assignment `y ≠ 0` supported inside the (finite) level set `levelSet b γ`:
`T.slotCoeff b y = Σ_{c ∈ supp y} digLift(y c)·mono c ≠ 0`. Mathematically: the
mixed-radix p/Φ-adic development with unit digits has no nonzero kernel — THE one
genuinely new lemma of the R6 closure (T4/C1 take `slotCoeff ≠ 0` as a hypothesis;
T8's BijOn runs on a subgroup, dodging kernel-triviality).

**Proof sketch (the §3.2 REVISION-2 factor-out route; all vocabulary CL-27's).**
`l_min :=` the least p-exponent over `supp y` (finite — `levelSet_finite'`;
NONEMPTY since `y ≠ 0`). `slotCoeff_factor` + IsDomain cancellation
(`C_p_pow_ne`, `mul_ne_zero_iff` in `ℤ_[p][x]`) reduce (10) to the cofactor
`Σ_c digLift(y c)·C(p^{l c − l_min})·∏Φ^{s c} ≠ 0`. Apply `red` (a ring hom —
transports sums/products): the `l c > l_min` terms die (`red_p_pow_zero`); the
survivors — at least one, `l_min` is attained — have DISTINCT slot vectors
(`coord_eq_of_ht_l_eq`: same block b, same height γ, same level l_min ⇒ equal, so
distinct survivors have distinct slot vectors; the top slot is constantly b).
The reduced sum is `Σ_c d̄_c·∏_r Φ̄_r^{s_c(r)}` with `d̄_c = red (digLift (y c)) ≠ 0`
(`red_digLift_ne`), `deg d̄_c < deg Φ̄₀` (`red_digLift_deg` — degree may drop, R-2),
`Φ̄_r` monic of the EXACT degrees (`red_monic_deg`, `red_ratio_law`). Close with
`CL11_posUniq` at `K₀ = 𝔽_p = ZMod p`: nonemptiness from the attained `l_min`;
`0 < deg Φ̄₀` from `(T.stg 0).hdeg` + `red_monic_deg`. The cofactor is ≠ 0 because
its red-image is ≠ 0.

**E-phase resolutions recorded.**
* Display (10) is stated on FULL-DOMAIN digit assignments with level-set support
  (`∃ c, y c ≠ 0` + `∀ c, y c ≠ 0 → c ∈ levelSet b γ`) — the ŷ-extension form,
  matching the CL-10 probe's shape EXACTLY (`CL10_nclProbe.lean` states the
  negation of this statement's instance; the probe file records the same
  resolution). No `hfin` hypothesis: level sets are finite (T7's
  `levelSet_finite'`), so the support is automatically finite.
* SPLIT RULE (CL-12a/b) NOT exercised at E-phase: the finsum bookkeeping is already
  carried by CL-27(c)'s `slotCoeff_factor`. If it resists there, the prover emits
  CL-12a (sum normalization) / CL-12b (the application) per the blueprint.
* T9 itself is NOT imported: its kernel reaches this unit only through CL-27(d)'s
  `coord_eq_of_ht_l_eq`.

**Deps.** CL-10 (gate), CL-11, CL-27 (, T9 via CL-27(d)). difficulty: hard-fable.
Size: ~60. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **CL-12 (display (10), NCL)**: no cancellation at a level — a nonzero digit
assignment supported inside one level set has nonzero slot coefficient (uniqueness
of the mixed-radix p/Φ-adic development with unit digits). GATED on CL-10. -/
theorem CL12_ncl {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hne : ∃ c : T.Coord, y c ≠ 0)
    (hsupp : ∀ c : T.Coord, y c ≠ 0 → c ∈ T.levelSet b γ) :
    T.slotCoeff b y ≠ 0 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL12_ncl
