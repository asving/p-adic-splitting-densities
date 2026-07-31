/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL10_nclProbe — NCL countermodel attempt (BP5 CL-10, GATE unit)

**Unit CL-10** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
display (10); risk R-1). COUNTERMODEL-FIRST GATE: this probe MUST COMPLETE before any
CL-11 (𝔽_p[x] positional uniqueness) or CL-12 (NCL assembly) work starts — NCL is a
universal that could conceivably fail, and the corpus's own history is circumstantial
evidence of dodging (T4/C1 take `slotCoeff ≠ 0` as a HYPOTHESIS; T8's BijOn is built
from a SUBGROUP A, deliberately avoiding kernel-triviality of `typComposite`).

**The target universal (display (10), NCL — no-cancellation at a level).** For y ≠ 0
supported inside the (finite) level set `levelSet b γ`:
`T.slotCoeff b y = Σ_{c ∈ supp y} digLift(y c) · mono c ≠ 0`.
Mathematically: uniqueness of the mixed-radix p/Φ-adic development with unit digits.

**CHARGE (the probe body, sorry slot).** Try to FALSIFY (10): find distinct
same-height bounded coordinates c ≠ c′ in one block (equal ht forces different l when
the slot vectors differ, since κ > 0 — verify) and digits a, b with
`digLift a · mono c + digLift b · mono c′ = 0`, or a longer cancelling combination —
or prove a small decidable instance rules it out. ATTACK THE MOD-p REDUCTION'S WEAK
POINT (risk R-2): `digLift` has gaussVal 0 (SOME coefficient is a unit) but its mod-p
reduction's degree may DROP, and could in principle interact across DIFFERENT
x-degree blocks.

**SEALED PREDICTION (blueprint §3.2 + §5 R-1).** NO countermodel exists: NCL is
believed TRUE, with the factor-out proof plan on record (CL-27's reduction interface:
factor C(p^{l_min}) inside the domain ℤ_[p][x], reduce the cofactor through
`Polynomial.map PadicInt.toZMod`, survivors have distinct slot vectors by T9(b)'s
numeric kernel, close with CL-11's positional uniqueness). Expected outcome: BLOCKED
+ a "mechanism survey: none found" report naming the exact algebraic fact that blocks
each attempted cancellation. If a countermodel IS found: automatic R-1 escalation —
leg (i-b) FAILS at packE (a two-level y with a cancelling lower level), the R6 file's
POSITIVE FINDING is wrong at its "(i-b) transports from T4" step, and R6 returns to
adjudication (fallbacks: window-guard (i-b), NCL as a named pack law, or re-fence).

**Deps.** none (runs first; parallel with CL-27). BLOCKS CL-11, CL-12.

**E-phase resolutions recorded.**
* The probe states the ŷ-extension form of (10) directly on full-domain digit
  assignments with level-set support: for such y, `slotCoeff b y` equals the display's
  `Σ_{c ∈ supp} digLift(y c)·mono c` (off-support block-b terms contribute
  `digLift 0 = 0`), so a witness here IS a counterexample to (10) as CL-12 will state
  it. Support inside one level set keeps the finsum honest (`levelSet_finite'`).
* Ambient fixed at the standard gate instance (p = 2, F = GaloisField 2 2) — the
  blueprint does not pin it; note p = 2 makes the two-term cancellation shape
  `digLift a · mono c = digLift b · mono c′` additive. If the survey isolates an
  odd-p-only mechanism, report BLOCKED-with-artifact; retargeting is an orchestrator
  statement change.
* No negation of a live statement is compiled here: NCL itself is NOT yet declared in
  the live tree (CL-12 will state it), so this probe coexists with nothing.

difficulty: hard-fable (analysis unit — no required theorem). Size: report +
optional ≤60-line certificate. PERMITTED OUTCOME: BLOCKED + mechanism survey.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The CL-10 probe** (countermodel attempt against NCL, display (10)): a tower,
block, height, and NONZERO digit assignment supported inside the level set whose slot
coefficient polynomial CANCELS to 0. Sealed prediction: FALSE (no witness exists) —
the expected deliverable is the mechanism-survey report, not a proof. A proof here
kills the CL-11/CL-12/CL-13/CL-14 spine and escalates R6 per risk R-1. -/
theorem CL10_ncl_countermodel_attempt :
    ∃ (T : Tower 2 (GaloisField 2 2)) (b : ℕ) (γ : ℚ)
      (y : T.Coord → ↥(T.stg 0).FQ),
      (∃ c : T.Coord, y c ≠ 0) ∧
      (∀ c : T.Coord, y c ≠ 0 → c ∈ T.levelSet b γ) ∧
      T.slotCoeff b y = 0 := by
  sorry

/-!
## MECHANISM SURVEY: none found (CL-10 as-built record, 2026-07-30)

**Verdict: BLOCKED (sealed prediction upheld).** No countermodel exists; the sorry
above is believed UNFILLABLE (the statement is believed false — CL-12 proves the
universal it negates). Every attempted cancellation mechanism is blocked by a named
algebraic fact, each PROVED at HEAD or delivered by CL-27/CL-11/CL-12:

**M-A (same-l two-term cancellation inside one level set).** Seek c ≠ c′ in
`levelSet b γ` with `c.l = c′.l` and `digLift a · mono c = − digLift b · mono c′`.
BLOCKED BEFORE THE DIGITS EVEN ENTER: within one level set, distinct coordinates
have distinct slot vectors (equal slots + equal height forces equal `l` by
cancelling `Σ slot·κ` in `ht = l + Σ slot·κ`, then `Coord` ext gives `c = c′`);
distinct slot vectors have distinct base indices (T9(b)'s mixed-radix kernel
`mr_inj_top`, digit bounds = `slot_lt`); and `deg Φ₀ ∣ baseIdx` (the degree chain
`t4_deg_dvd_step`), so the two terms occupy DISJOINT x-degree windows
`[baseIdx, baseIdx + deg Φ₀)` — `deg (digLift) < deg Φ₀` (`digLift_deg`) pins each
term inside its window. Terms in disjoint windows cannot cancel.

**M-B (cross-l cancellation, the p-adic channel).** Coordinates with the same slot
vector but different `l` share a degree window and DO interact in `ℤ_[p][x]` — but
they cannot share a level set (`ht` differs by `l − l′ ≠ 0`), so the probe's
level-set support forbids the pair outright. For mixed families with distinct slot
vectors AND distinct `l`: factor `C(p^{l_min})` (CL-27 `slotCoeff_factor`; domain +
`C_p_pow_ne`), reduce the cofactor mod p (`red`): all `l > l_min` terms die
(`red_p_pow_zero`), the `l = l_min` survivors keep UNIT digits — `gaussVal (digLift) = 0`
via the base pin `T.base.1.1` (`gaussVal_digLift_zero`), so some coefficient is a
`ℤ_[p]`-unit and survives `toZMod` (`red_digLift_ne`). Vanishing of the survivor
layer is then M-C, blocked below. Exact blocking facts: `red (C (p^k)) = 0 ⟺ k ≥ 1`;
`gaussVal (digLift y) = 0`.

**M-C (mod-p cancellation across x-degree blocks — the header's flagged weak point,
risk R-2).** Over `𝔽_p[x]` the reduced digit degree may genuinely DROP, and the
probe charge asks whether dropped digits can interact across degree blocks. NO: each
reduced term `d̄_c · ∏ Φ̄_r^{s_r}` still lies in the window
`[Σ s_r·deg Φ̄_r, Σ s_r·deg Φ̄_r + deg Φ̄₀)` — the LOWER edge because the reduced keys
are monic of EXACT degree (`red_monic_deg`, resting on the exact ratio law
`t4_slotBound_mul`, which holds for EVERY tower move), the UPPER edge because
`deg d̄ < deg Φ̄₀` (`red_digLift_deg` — an upper bound survives the drop). Distinct
slot vectors give distinct window bases (mixed-radix), all multiples of `deg Φ̄₀`
(degree-divisibility chain), so the windows are DISJOINT: a degree drop moves a term
lower WITHIN its own window, never into a neighbor. The cross-block interaction
channel would need a NON-exact ratio `deg Φ_{r+1} < slotBound_r · deg Φ_r`, refuted
by `t4_slotBound_mul` (increment: `deg Φ̂ = e·g·deg Φ`, L3_liftMonic; recentering:
degree unchanged). CL-11's positional uniqueness packages exactly this.

**M-D (p = 2 sign collapse).** At p = 2 the two-term cancellation is additive
(−1 = 1). No purchase: M-A/M-B/M-C are valuation/degree-theoretic and
characteristic-agnostic; signs never enter.

**M-E (digit-carry interference).** `digLift` is NOT additive (the carry
`digLift(a+b) − digLift a − digLift b` has base weight ≥ 1 — C2_TYPa's `carry_wall`),
but NCL's sum never adds two digits AT THE SAME coordinate (the finsum runs over the
coordinate set); carries cannot arise. No purchase.

**Compiled-instance option declined.** A decidable-instance certificate would need a
compiled `Tower 2 (GaloisField 2 2)` (the CL-01a/b/c portfolio, a separate ~400-line
unit, itself expected BLOCKED); the universal CL-12 is the stronger certificate and
lands in this same cluster. Per the no-coexistence ruling, nothing negation-shaped is
compiled here; once CL-12 lands, this probe file records a believed-false sorried ∃
and should be QUARANTINED by the orchestrator (flagged in the prover report).
-/

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL10_ncl_countermodel_attempt
