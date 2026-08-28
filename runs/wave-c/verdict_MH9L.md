# VERDICT — UNIT MH9L, 2026-08-28

## Overall

**COMPLETE — ALL NINE NODES LANDED, ZERO HOLES.**
`leanfinal/Uniformity/ChapC/C133mh9.lean` (new file, ~2000 lines, header `[MH9L 2026-08-28]`,
namespace `Uniformity.Density.Tower.C133mh9`) transcribes the full MH9M discharge.  The file
is sorry-free; every AxCheck footprint is exactly `[propext, Classical.choice, Quot.sound]`
— **`theoremA` consumes NO cite**.  Verified via
`lake env lean Uniformity/ChapC/C133mh9.lean` (zero errors, zero warnings) and
`lake build Uniformity.ChapC.C133mh9` (green, 8759 jobs).  No landed file was edited;
the only repo changes are `C133mh9.lean`, this verdict, and the scratch probe
`leanfinal/scratch/mh9_probe.lean`.

**Theorem A — the engine's FINAL node — is now an unconditional Lean-core theorem.**

## Per-node status (verdict_MH9M.md §4's list)

1. **`dvLinePoly` + `dvLinePoly_coeff`** — LANDED (MH9M.1's displayed definition verbatim;
   plus helpers `natDegree_dvLinePoly_le`, `dvLinePoly_zero`).
2. **`dvLinePoly_dvWindowLift`** — LANDED (packages `C133mh5.twistRead_dvWindowLift`
   coefficientwise; hypotheses `hfull` + `ψ.natDegree < A`).
3. **`dvLinePoly_mul_of_isDvPure` (Law AMR)** — LANDED, MH9M.2's exact statement and route:
   the `W(z) > d` branch by strict pricing on both sides (new private strict slot floor
   `lt_dvHgt_of_succ_le_dvSupp`); at `W(z) = d`, `dev_mul_conv_split` at
   `J = j₀ + nℓ, K = Mp + M − nu`, carry diagonal by `carry_term_floor`, off-pair mains by
   `read_kill`, ℓ-grid reindex, surviving pairs by `C133mh3.m1TwistProductLaw` (TW-δ absorbs
   `η^δ` inside the landed root — no separate δ handling needed here).
4. **`lemmaS : C133mh5.LemmaSStatement O`** — LANDED, the signed shape (C133mh5.lean:830)
   discharged BY NAME.  `j₀` built via Euler (`Nat.ModEq.pow_totient` — uniform, no `ℓ = 1`
   split); genuine `Mc/MU/MV` decompositions; MH9M.3's fullness chain; the stage-field
   Bézout solve on `Ebar := dvLinePoly j₀ Mc (a+b) e`; AMR at `(p₂,U)`/`(p₁,V)`;
   `le_dvSupp_succ_of_lineReads_eq_zero` closes at `c + 1`.
5. **`dvSupp_sub_succ_of_same_residual`** — LANDED (equal grade-`w` line reads contract the
   difference; general two-polynomial form).
6. **`monic_of_dvGradedLimit`** — LANDED (OPEN-MH9-LIMIT-MONIC closed: separatedness via
   `gaussVal_of_shifted_dvSupp` + `gaussVal_le_addVal_coeff` + `addVal_eq_top_iff`).
7. **`eq_zero_of_forall_dvSupp`** — LANDED (`gaussVal_eq_top_iff` route).
8. **`isDvPure_one` / `dvHgt_one_zero` / `dvResPoly_one`** (+ helper `dvSupp_one`) — LANDED
   (OPEN-MH9-UNIT-BRANCH closed; `C133mh0.twistRead_one` through the singleton side).
9. **★ `theoremA : C133mh14.TheoremAStatement O`** — LANDED, the signed shape
   (C133mh14.lean:264) discharged BY NAME, MH9M.4's seven steps:
   unit branches `(1,g)`/`(g,1)` via node 8; side-lift initialization with node 5's equal
   base-line reads (`hreads0`: on-grid = residual coefficients through
   `lineRead_eq_dvResPoly_coeff` + `dvResPoly_mul_gen`; off-grid = 0 through
   `lineRead_eq_zero_offgrid`); the iteration as an 11-conjunct invariant pack
   (`TAInv`, reducible private def) advanced by `lemmaS` + M4 and packaged as a
   `Nat.rec` subtype sequence (Classical choice on the step ∃, tail bounds by defeq);
   `C133mh8.exists_dvGradedLimit` on both windows; node 6 monicity; late-iterate M4
   transfer (`dv_pure_add_of_lt'`, a `subst` wrapper) with ∀-pin residuals via
   `dvResPoly_pin_congr`; node 7 exactness `g = P₁P₂`.

## The four named opens — all closed

* **OPEN-MH9-PRIVATE-PRICING** — closed by Part 0: byte-identical private re-declarations
  of C133mh3's `carry_term_floor`, `read_kill`, `modKey_term_floor(_succ)`,
  `pair_line_le/lt`, `dvResPoly_coeff_of_le/gt`, `exists_key_height_lt`,
  `natDegree_dev_lt_frame`, the ℕ∞ weight readers; C133mh5's `dev_finsetSum`; C133mh14's
  `exists_pin`; each credited to its source in the docstring.
* **OPEN-MH9-LIMIT-MONIC** — node 6.
* **OPEN-MH9-UNIT-BRANCH** — node 8 + the two explicit branches in node 9.
* **OPEN-MH9-UNIVERSAL-PIN** — private `dvResPoly_pin_congr` (C133mh11's precedent,
  re-declared; cast-injectivity + proof irrelevance).

## Statement fence audit

* `C133mh5.LemmaSStatement` and `C133mh14.TheoremAStatement` are consumed **by name,
  byte-as-is** — never restated, never weakened.
* Law AMR's statement is the verdict §1 display verbatim (window `A + deg R(p)`, heights
  `Mp + M`, hypotheses `j₀ < ℓ`, `0 < A`, `u(A−1) ≤ M`, degree window `ℓ(A·D′)`, support
  floor `ℓM + uj₀`).
* No landed `.lean` file edited; `C133h0leg.lean` untouched; no git ops.

## The payoff (smoke-tested)

`leanfinal/scratch/mh9_probe.lean` (green):

    example ... (hctx : BlockContext L f) : BlockFrontier L f :=
      C133mh14.blockFrontier_of_context_of_theoremA hπ hh L hctx C133mh9.theoremA

The signed `BlockFrontier` now fires from `BlockContext` with **no carried hypothesis**;
the only non-Lean-core name in that composed footprint remains mh14's allowlisted C.33
cite `exists_dvDissection`.  F1.H3 is closed UNCONDITIONALLY at the Theorem A leg.

## Notes for the orchestrator

* File is ~2000 lines (above the 600–1000 estimate): the OPEN-MH9-PRIVATE-PRICING copy
  bank (~450 lines) and the full three-branch Theorem A assembly (~600 lines) account for
  the growth; all copies are credited, none is new mathematics.
* `set_option maxHeartbeats 1600000` on nodes 3, 4, 9 (the 1600000 convention).
* One new tiny arithmetic lemma beyond the verdict's list: the private `line_arith`
  (the grade-line pricing identity) and `lt_dvHgt_of_succ_le_dvSupp` (strict companion of
  C130rp2's `le_dvHgt_of_le_dvSupp`) — both Part 0b glue, Lean-core.
* Repair log: three genuine fix rounds total — `Nat.ModEq.cancel_left_of_coprime`
  argument order (`hcop.symm`), a missing `u·j₀ < w₂` bound in Lemma S's decomposition
  omegas, and a `← hdeg` rewrite that hit an index expression (replaced by a forward
  rewrite).  `Nat.exists_mul_emod_eq_one_of_coprime` and `self_eq_add_left` do not exist
  in the pinned mathlib — replaced by `Nat.ModEq.pow_totient` and an `add_right_cancel`
  pattern respectively.
