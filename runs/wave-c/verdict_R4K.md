# UNIT R4K verdict — the rung-4 KEY LIFT lands whole and FIRES: the keystone tower side is COMPLETE (2026-08-31)

**Status: COMPLETE — ★★ the deepTwist bank's tower side is inhabited to rung 4 = the
LAST landed key of the keystone tower; at this witness genre the tower side is
COMPLETE.**
`leanfinal/Uniformity/ChapI/I10RungLift4.lean` (NEW, ~440 lines, namespace
`Uniformity.Density.Tower.I10rl4`) — 0 errors, 0 warnings, **0 `sorry`**; all **16**
printed footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified
per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift4.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10RungLift4` — Build completed
successfully, 8861 jobs), and aggregator (`Uniformity/ChapI.lean` + the one sanctioned
import line, exit 0).  Cite ledger: **empty** — every input is landed repo content.
**Zero repair rounds: the file compiled on the first attempt** (the only edit after
first compile was 2 deprecation renames `eval_finset_sum → eval_finsetSum`).

## STATUS FIRST — the three charged data, and what the campaign had already landed

W3P's forecast named the rung-4 remainder as (1) the μ₅ coefficient layer = "C136e0's
declared D4-13..16 gap", (2) the level-5 key with its exact μ₅ grade, (3) the μ₆
slopes.  Finding on arrival: **the D4 campaign (C136e1/C136e2, units D4B/D4C) had
ALREADY landed the entire μ₅ operator layer** — `s2Mu5Coeff`/`s2Mu5GradedRes`/
`s2Mu5NormRes` + full add/mul/grade banks, the leaf `s2Mu5Leaf := g16 − Λ` (monic,
degree 16, exact μ₅ grade **171**, normalized residual **X + 1**), the μ₅ key
predicates (D4-13..16), and the calculus `s2Mu5_calculus_nonempty` at `(1,1,171)`.
So this unit's genuinely new content is exactly the DICTIONARY between that landed
layer and the abstract rung-3 pack, plus the fire:

| datum | statement landed | mechanism |
|---|---|---|
| **W-b analogue** | `s2_nextSupp3_eq_dv4Supp` (for EVERY `f`): `nextSupp C₃ P₃ f = dv4Supp … f 171 1`; then `s2_nextSupp3_leaf : nextSupp C₃ P₃ (s2Mu5Leaf) = 171` | the rung-3 carrier's support is `dv3Supp` by W3P's landed dictionary (`s2_nextSupp_eq_dv3Supp`), `dv4Pin = dv3Supp ∘ dev g16` definitionally, range truncation by the inf-range twin; the leaf grade is the landed `s2Mu5Leaf_exactGrade` through `S2Mu5ExactGrade_iff_dv4Supp`.  As W3P forecast: CHEAPER than rung 3 (dv4Supp already landed) |
| **W-c analogue** | `s2Mu5Coeff_eq_wcoeff3` (under a `dv4Supp` floor): `s2Mu5Coeff β f t = wcoeff C₃ P₃ β f t` — and hence ★ `s2_nextRead3_eq_mu5GradedRes`: the rung-3 iterated read IS the landed μ₅ graded residual **as a POLYNOMIAL** (at `ℓ₅ = 1` there is NO slot dilation — contrast W3P's `X ↦ X²` at rung 2); `s2_mu5GradedRes_leaf : … = X + 1`; `s2_eval_one_nextRead3_leaf : eval 1 (…) = 0` (char-2 tooth) | the new engine is `eval_one_nextRead_eq_mu4` — **the μ₄ eval-1 read bridge**: `eval 1 (nextRead s2Carrier s2Key m g) = eval 1 (s2Mu4GradedRes m g)` under a `dv3Supp` floor.  The rung-2 read's ℓ = 2 dilation is invisible to eval-1: parity reindex `j = m % 2 + 2t` via `Finset.sum_nbij'` (all five side goals `omega`), against a floor-form twin of WCC's private `s2Mu4Coeff_eq_wcoeff` (the exact-grade hypothesis relaxed to the cleared-support floor its proof actually uses) |
| **μ₆ slopes** | fired as `(u₆, ℓ₆) = (172, 1)`, honesty pin `s2Rung4_slope_floor : u₆ = kgrade₅ + 1` (rfl) | **NO landed μ₆ table exists (no `dv5` layer anywhere), and per the [G5F 2026-08-28] record none should**: `(1,1,171)` is TERMINAL operator data — the leaf is the last key.  `(172,1) = (171+1, 1)` is the strict-floor refinement pattern, the exact genre of [G5F]'s own `(171,1) = (170+1, 1)`.  Packaging data only; no μ₆ anti-drift tie is claimed |

**Honesty ruling: all three data are landed with no weakening; nothing non-plumbing
surfaced.**  The one forecast correction: W3P's "D4-13..16 gap" had closed upstream
before this unit ran — the honest new work was the two dictionary bridges, exactly the
W3P recipe one rung up.

## ★★ THE FIRE

* `s2RungLift4 : RungLift (s2Rung3Pack) (fld 2) 172 1 := RungLift.ofRootF1 …` — key
  `s2Mu5Leaf` (monic, degree 16 = the f′ = 1 fence `1·16` EXACTLY), exact iterated
  grade `171` (W-b), root `1 ≠ 0` of the residual `X + 1` (W-c), `gcd 171 1 = 1`,
  strict floor `1·171 < 172`; next ring `fld 2` ITSELF (f′ = 1 again — third rung in a
  row with no ring growth).
* `s2LiftAt4 := liftAtOfRootF1 …` and `s2Rung4PackAt := s2LiftAt4.next` — ★ the rung-4
  pack at the keystone: slopes `(172,1)`, key `s2Mu5Leaf`, grade `171`, ring `fld 2` —
  all four pinned by `rfl` (`s2Rung4PackAt_u/ell/key/kgrade`).
* Anti-drift: `s2Rung4_kgrade_is_leaf_mu5_grade : S2Mu5ExactGrade (kgrade) (key)` — the
  fired grade IS the tower's own μ₅ table value at the fired key (C136e1's
  `s2Mu5Leaf_exactGrade`, consumed at the pack projections).
* `s2_towerPacks_rung4` — **`towerPacks` reaches rung 4 at index 2**: any step supplier
  extending the two S2 lifts (`step (s2Rung2PackAt) = s2LiftAt3`,
  `step (s2Rung3PackAt) = s2LiftAt4`).
* Banks: `s2_rungLift4_nonempty`, `s2Rung4Pack`, `s2_rung4_pack_nonempty`;
  ★★ `s2_rung4_wcoeff_mul` — the level-5→6 weighted convolution law fires through the
  landed rung-4 pack; `s2Rung5Carrier := nextCarrier (s2Rung4Pack)` — the rung-5
  CARRIER exists unconditionally (the "4+").

## ★ Coverage at the keystone (the charge's starred question)

The keystone's arising depth is 4/5 and **the bank's tower side is now COMPLETE at
this witness genre**:

| rung | key | slopes | grade | landed by |
|---|---|---|---|---|
| 2 | `g8` | `(85, 2)` | 42 | W3P (WCC carrier + W-a) |
| 3 | `g16` | `(171, 1)` | 170 | W3P fire |
| 4 | `s2Mu5Leaf = g16 − Λ` | `(172, 1)` | 171 | **this unit** |

Every landed key of the depth-four chain tail and its terminal [G5F] refinement now
carries a rung pack, and `towerPacks` reaches all of them.  **The bank still needs
NOTHING at this witness genre on the tower side**: there is no rung-5 key in the
source to lift (the `(1,1,171)` refinement is terminal per [G5F]; the leaf is where
the keystone factor separates), and the rung-5 carrier already exists unconditionally.
What remains adjacent (out of scope, unchanged from RL3 §7): the carrier→calculus
spine bridge legs (`PrevGrade` at f′ ≥ 2, the `CarrierReadLaw` tie) — realization-side,
not tower-side.

## New statements flagged for the standing review

`s2Mu5Coeff_eq_wcoeff3`, `s2_nextRead3_eq_mu5GradedRes`, `s2_mu5GradedRes_leaf`,
`s2_eval_one_nextRead3_leaf`, `s2_nextSupp3_eq_dv4Supp`, `s2_nextSupp3_leaf`,
`s2RungLift4`, `s2LiftAt4`, `s2Rung4PackAt` (+ 4 rfl-pins),
`s2Rung4_kgrade_is_leaf_mu5_grade`, `s2Rung4_slope_floor`, `s2_towerPacks_rung4`,
`s2_rungLift4_nonempty`, `s2Rung4Pack`, `s2_rung4_pack_nonempty`, `s2Rung5Carrier`,
`s2_rung4_wcoeff_mul` — all supplier-side below the signed surface.  Local twins
flagged for the standing dedup: the `wcoeff` guard pair (7th corpus repetition),
W3P's `nextSupp_eq_inf_range` (2nd), and the floor form
`s2Mu4Coeff_eq_wcoeff_of_le` of WCC's private dictionary (candidate: relax WCC's
private twin in place and delete both copies).

## Verification + repair log

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift4.lean`;
  FINAL: exit 0, 0 errors, 0 warnings, `grep -c sorry` = 0; AxChk **16/16** Lean-core;
  `lake build Uniformity.ChapI.I10RungLift4` — Build completed successfully (8861
  jobs); aggregator `Uniformity/ChapI.lean` exit 0 after the one import line.
* Repairs: **ZERO rounds** — first-attempt compile.  (All defeq bets held: pushCarrier
  read ≡ `eval 1 ∘ nextRead`, `P₃.key ≡ g16`, `dv4Pin ≡ dv3Supp ∘ dev g16`,
  proof-irrelevant defeq of `s2Rung3PackAt.pack` with `s2Rung3Pack` at the bundled
  wrapper.)  Post-compile edit: 2 deprecation renames only.
* Footprint: `leanfinal/Uniformity/ChapI/I10RungLift4.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed file
  edited; IFCG61 untouched; no git operations.
