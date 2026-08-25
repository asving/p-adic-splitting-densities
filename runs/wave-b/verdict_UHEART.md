# Unit U-HEART verdict (af′ REVERSE plan, `docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3)

## U-HEART — LANDED (stage 2, extends `C131af.lean`)

Three theorems landed, extending `leanfinal/Uniformity/ChapC/C131af.lean` (U-SIDE's file,
which built green and was left untouched at stage 1):

* `Uniformity.Density.Tower.C131af.towerLocus_read_eq` (AF-3a) — any two members of
  `towerLocus T μ₂` read identically at every point `t₀ ≤ μ₂f₂` of the shared `e₂`-lattice:
  both residual polynomials equal `towerLabel T ^ μ₂` (the locus's own residual clause), so
  the extraction two-liner (`Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` unfolded against
  `dvResPoly`) identifies their `t₀`-th coefficients — the two ϖ-reads — with the same value.
  Lean-core only, as planned (no cite in this stage).
* `Uniformity.Density.Tower.C131af.dvSupp_sub_composedKey_pow` (AF-3, ★ THE HEART) — a locus
  member's perturbation `f − Φ₂^{μ₂}` against the C.131ac′ reference clears `μ₂E₂ + 1`
  STRICTLY. Proof exactly per the plan's script: ultrametricity (`C131w.dv2Hgt_add_min` +
  `dv2Hgt_neg`) gives the weak floor `μ₂E₂`; case split on strict-vs-exact; in the exact
  case, AF-2a/AF-2b (U-SIDE) locate the perturbation's on-line abscissa `s = e₂t₀` and its
  exact height; `C130rp2.twistRead_add_of_le` splits the ϖ-read of `f`'s digit into the
  perturbation's plus the reference's; AF-3a forces `f`'s read to equal the reference's
  read at that point; algebra (`add_right_cancel`) forces the perturbation's own read to be
  `0`; but C.26's `natDegree_dvResPoly` clause (iii) says the perturbation's residual
  constant term is nonzero at that exact abscissa — contradiction. Carries the cite
  `fgmn_dv_exact_mul` (C66b), inherited through `composedKey_pow_mem_towerLocus`
  (C.131ac′), exactly the single entry point the plan discloses.
* `Uniformity.Density.Tower.towerLocus_dev_strict_floor` (AF-4, ★ = C.54(c) strict node
  floor, root namespace per the plan) — for `f ∈ towerLocus T μ₂` and `j < μ₂`, the
  composed-key digit `dev Φ₂ f j` clears `(μ₂−j)E₂ + 1` strictly. Proof: `dev Φ₂ f j =
  dev Φ₂ g j` for the perturbation `g` (C.131ae′'s own `hgdig` block, reused verbatim:
  `C131v.dev_sub` + `dev_pow_self`'s Kronecker vanishing since `j ≠ μ₂`), then
  `C131w.dv2Hgt_dev_floor` pushes AF-3's `μ₂E₂+1` floor down to `(μ₂−j)E₂+1` on `dev Φ₂ g j`
  (numeral identity via `Nat.sub_mul` + `omega`). Same cite footprint as AF-3 (inherited,
  not re-consumed independently — both entries trace to the same single
  `composedKey_pow_mem_towerLocus` call inside AF-3).

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C131af.lean` — exit 0, zero errors, zero
`sorry`, zero new `axiom`. `lake build Uniformity.ChapC.C131af Uniformity.ChapC.C131ag` —
8744 jobs, green (the one linter note reported is pre-existing, from U-SIDE's stage-1
`show`-vs-`change` style point at line 73, not from this unit's additions).

```text
'Uniformity.Density.Tower.C131af.towerLocus_read_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C131af.dvSupp_sub_composedKey_pow' depends on axioms:
  [propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul]
'Uniformity.Density.Tower.towerLocus_dev_strict_floor' depends on axioms:
  [propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul]
```

Exactly the plan's predicted footprint (§3, U-HEART acceptance clause): AF-3a Lean-core;
AF-3/AF-4 carry EXACTLY `fgmn_dv_exact_mul` on top of Lean-core, inherited via
`composedKey_pow_mem_towerLocus` — the declared C66b cite (allowlist member, faithfulness
entry in `docs/AXIOM_FAITHFULNESS.md` under "`fgmn_dv_exact_mul` (C66b, declared
2026-08-24)"), not a new axiom.

## Deviations from the plan's proof sketch (bookkeeping, not mathematical)

* Two small omega-visibility gaps, both from nonlinear atoms that omega cannot relate
  without an explicit bridging fact (omega treats `a*b` and `b*a` as distinct opaque atoms
  unless a commutativity equation is supplied): (1) inside AF-3's height-cancellation case
  split, added `have hcomm : t₀ * T.u₂ = T.u₂ * t₀ := Nat.mul_comm t₀ T.u₂` immediately
  before the closing `omega`. No other repair needed — the rest of the ~230-line addition
  (AF-3a, AF-3, AF-4) compiled on the first attempt against the DEC2 elaboration check's
  pinned bridges and lemma signatures.
* `Nat.mul_le_mul` (general monotonicity, `a≤b → c≤d → a*c≤b*d`) was used uniformly in
  place of guessing `Nat.mul_le_mul_left`/`_right`'s exact mathlib argument order, to avoid
  name/signature drift; this is a robustness choice, not a mathematical deviation.

## Scope discipline

Only `leanfinal/Uniformity/ChapC/C131af.lean` (U-SIDE's file, extended per the plan's
stage-2 assignment) and this verdict were written. Did not touch `leanspec/`, roll-ups,
`C131ag.lean` (U-ARITH's file), or any PK12-owned file (`C130fg`/`pk`/`s17`/`s18`/`vw`). No
`git commit` taken. U-ASSEMBLE (extending `C131ag.lean` with AF-6a/AF-6b) and U-FEED
(`C123r2.lean`) are next in the plan's sequencing and are NOT started here.
