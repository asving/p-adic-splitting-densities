/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Tactic.Common

/-!
# Uniformity.ChapH.H50 — the tower thresholds `n ≥ 8` and `n ≥ 16`

**Chapter H, NODE H.50** (`blueprint/CHAP-H_general_induction.md` §7). Two degree thresholds:

* `tower_needs_eight` — a stage's own read admits a composite opening (a TOWER event) only if the
  stage multiplicity satisfies `μ ≥ 4` (H.03 applied *inside* the stage), so with `e₁f₁ ≥ 2` a
  tower forces `n ≥ (e₁f₁)·μ ≥ 2·4 = 8`;
* `depth_three_needs_sixteen` — a THIRD stage forces `μ₁ ≥ e₂f₂μ₂ ≥ 2·4 = 8` and hence
  `n ≥ D′·μ₁ ≥ 2·8 = 16`, i.e. it is `GENHN-T(a)` applied twice.

DEPENDS: H.03 (for the "inside the stage" reading of the hypothesis `4 ≤ μ`; the Lean statements
below are self-contained arithmetic and import nothing from chapter H).

SOURCE: `EFF.GENHN.16` (`LEMMA GENHN-T(a)`, verbatim: *"a stage's own read admits a composite
opening (a TOWER event) iff the stage multiplicity satisfies `μ ≥ 4` (GENIND.A(IV) applied inside
the stage); hence towers exist at degree `n` iff `n ≥ (e₁f₁)·μ ≥ 2·4 = 8`. `n = 8 = 2·2·2` is the
first live instance … `n = 4..7` are tower-free"*); `EFF.GENHN.18`'s `[r3]` R1 arithmetic,
verbatim: *"a third stage forces `μ₁ ≥ e₂f₂μ₂ ≥ 8`, hence `n ≥ D′μ₁ ≥ 16`"*.

**⚠ THE "iff" IS AN "only if" HERE.** `GENHN-T(a)` states an iff; the *realization* half (that the
`n = 8` genre `(2,1,4)` exists with positive opening locus, exhibited by the machine witness
`GN-TOWER`) is geometric and is **not** a node of this chapter. What is proved here is the
NECESSITY direction — the direction the conditionality bookkeeping consumes (`n ≤ 7` tower-free
⟹ `[GENHN-TOW-1]` is empty there). `EFF.GENHN.16`'s corrected proof display (`R4 F-5`: read
`(T−c)²`, not `(T²−c)²`) belongs to the realization half and is reproduced nowhere in chapter H;
its own TEETH field records that the machine witness was right while that display was stale.

**Arithmetic audit** (recomputed): `2·4 = 8` ✓, with `n = 8 = 2·2·2` the minimal factorization
(`e₁f₁ = 2`, `μ = 4`, inner `(e₂f₂, μ₂) = (2,2)`); depth 3 gives `2·4 = 8 ≤ μ₁` and `2·8 = 16 ≤ n`
✓. The two constants `8` and `16` are the chapter's degree-range boundaries (depth 2 exhausts the
tower genres at `n ∈ {8, …, 15}`; the iterated depth-`≥ 3` composition starts at `n ≥ 16`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.50 (i), `GENHN-T(a)`, necessity.** A tower event needs a stage multiplicity `μ ≥ 4`
(H.03 inside the stage) on top of the stage's own `e·f ≥ 2`, so the ambient degree `n`, which is
at least `e·f·μ`, is at least `8`. -/
theorem tower_needs_eight {e f μ n : ℕ} (hef : 2 ≤ e * f) (hμ : 4 ≤ μ) (hn : e * f * μ ≤ n) :
    8 ≤ n :=
  -- `2 * 4 ≤ (e * f) * μ ≤ n`, and `2 * 4` is `8`.
  Nat.le_trans (Nat.mul_le_mul hef hμ) hn

/-- **NODE H.50 (ii), the depth-3 threshold.** A third stage applies clause (i) inside the second:
`μ₁ ≥ e₂f₂·μ₂ ≥ 8`, and then `n ≥ D·μ₁ ≥ 2·8 = 16`. -/
theorem depth_three_needs_sixteen {D μ₁ e₂ f₂ μ₂ n : ℕ} (hD : 2 ≤ D) (h2 : 2 ≤ e₂ * f₂)
    (hμ₂ : 4 ≤ μ₂) (h1 : e₂ * f₂ * μ₂ ≤ μ₁) (hn : D * μ₁ ≤ n) : 16 ≤ n :=
  -- clause (i) inside the second stage, then `2 * 8 ≤ D * μ₁ ≤ n` with `2 * 8 = 16`.
  Nat.le_trans (Nat.mul_le_mul hD (tower_needs_eight h2 hμ₂ h1)) hn

end Uniformity.Density.Induction

/-! ## Numeric gate — the two thresholds are TIGHT, and the sub-threshold range is empty.
`#guard` fails elaboration when the proposition evaluates to `false`, so these are build-time
checks. First: no `(e·f, μ)` with `e·f ≥ 2`, `μ ≥ 4` has product `< 8` (scanned over
`e·f, μ ≤ 12`), and the product `8` is attained (`(2,4)`). Second: the depth-3 minimum `16` is
attained at `D = 2`, `μ₁ = 8`, `(e₂f₂, μ₂) = (2,4)`. -/

section NumericGate

/-! No product below the threshold, over the scanned box. -/
#guard (List.range 13).all fun a => (List.range 13).all fun m =>
  !(2 ≤ a && 4 ≤ m) || 8 ≤ a * m

/-! The threshold `8` is attained, so it cannot be raised. -/
#guard 2 * 4 == 8

/-! Depth 3: `μ₁ ≥ 8` and `D · μ₁ ≥ 16`, attained at `(D, μ₁) = (2, 8)`. -/
#guard 2 * (2 * 4) == 16

/-! `n = 4, …, 7` are tower-free: no admissible `(e·f, μ)` fits under `8`. -/
#guard [4, 5, 6, 7].all fun n => (List.range (n + 1)).all fun a => (List.range (n + 1)).all fun m =>
  !(2 ≤ a && 4 ≤ m) || !(a * m ≤ n)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.tower_needs_eight
#print axioms Uniformity.Density.Induction.depth_three_needs_sixteen

end AxCheck
