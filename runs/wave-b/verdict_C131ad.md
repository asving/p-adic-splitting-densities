# Verdict — unit C131ad (NODE C.131ad′)

**LANDED.**

## File

`leanfinal/Uniformity/ChapC/C131ad.lean` (new; no other file touched).

## The two node deliverables

* `Uniformity.Density.Tower.C131ad.boxMonomial_coeff_floor` — the box monomial coefficient
  floor: every scalar coefficient of every canonical `F.key`-digit of
  `C c · xᵃ · Φ′ᵇ · Φ₂ʲ` clears `gridWeight T v a b j` at its own grid position, for any
  certified valuation floor `(v : ℕ∞) ≤ addVal O c`.  Total in `a`, `b`, `j` (no box-range
  hypothesis needed — stronger than the C.52 consumer requires).
* `Uniformity.Density.Tower.C131ad.dvAbove_boxMonomial` — C.52's Step 0 carrier:
  `DvAbove F (C c * X^a * F.key^b * composedKey T^j) T.u₂ T.e₂ ((gridWeight T v a b j : ℕ) : ℕ∞)`
  under the same `hv`, via C.131u′'s bridge (only the proved direction of §3.7).

Both are stated purely in landed vocabulary (`DvAbove` = C.52's, `gridWeight`/`slotOffset` =
C.50's, `dev` = B.02's, `wtCoeff`/`WT` = C.131a′'s) — no redefinitions.

## Supply lemmas landed alongside (all in namespace `Uniformity.Density.Tower.C131ad`)

`le_WT_sum`, `le_WT_C_mul_X_pow`, `le_WT_C_C`, `wtCoeff_add_shift`, `wtCoeff_le_paid`,
`natDegree_X_pow_sub_key_le`, `carryTerm` (def), `eval_carryTerm`, `le_WT_carryTerm`,
`carryTerm_coeff_natDegree_le`, `carryStep` (def), `eval_carryStep`, `le_WT_carryStep`,
`carryStep_coeff_natDegree_lt`, `dev_coeff_floor_of_WT_floor`, **`dev_coeff_floor`**
(the carry-down erasure: any two-variable lift with `w ≤ WT` has every scalar coefficient
of every `F.key`-digit of its evaluation above `w` — reusable beyond the box monomial),
`le_WT_K_T_pow`, **`eval_K_T`** (`(K_T T).eval F.key = composedKey T` — reusable),
`le_WT_box_monomial`, `le_WT_boxLift`, `eval_boxLift`.

## Proof route (why no census machinery was needed)

Lift the box monomial to `C (C c·xᵃ)·Yᵇ·(K_T T)ʲ` (weight ≥ grid weight by `WT_mul` +
`WT_K_T`), then descend on the inner-degree excess: each `carryStep` removes the top inner
monomial of every outer coefficient via the x-carry split
`x^(D′+n)·Yᵇ = (x^(D′)−Φ′)·xⁿ·Yᵇ + xⁿ·Y^(b+1)` — tail branch priced by `xCarry_tail_floor`
(C.131d′–e′), paid branch by `xCarry_branch_WT_exact` + the node floor `u₂ ≥ e₂D′h`; once
in-grid, digits = coefficients (C.127 `dev_eval_eq_coeff`), and C.131u′'s
`dvAbove_of_forall_coeff_floor` converts.  No tags, no `K_T`-coordinate recarry: stays
inside the declared deps C.131c′–j′ + u′ (plus landed C.127), and does not overlap the
in-flight C.131n′ (F9/F10 recarry arithmetic) or unassigned C.131o′ (tagged census F11).

Note: C.131h′–j′ (the K_T-division ledger) turned out not to be needed — the carry-down
replaces it for this node.  Deps consumed: C.131a′–g′ (via C131a/C131d/C131f), C.131u′,
C.127, C.47 (`composedKey_natDegree`, via `eval_K_T`), B.05 (`sum_dev_eq`).

## Verification

```
cd leanfinal && lake env lean Uniformity/ChapC/C131ad.lean
```

Run 2026-08-24: zero errors, zero warnings, zero `sorry`; all 23 `#print axioms` lines
report exactly `[propext, Classical.choice, Quot.sound]` (Lean core only).

## Honesty notes

* `hv : (v : ℕ∞) ≤ addVal O c` is the value-blind form; `v = 0` always satisfies it, and at
  `c = 0` the box monomial is `0` and the conclusion is trivially true — the theorem is a
  floor, not a nonvanishing claim.
* `hπ : Irreducible π` is carried (needed by `WT_K_T` and `composedKey_natDegree`).
* New defs `carryTerm`/`carryStep` are internal engine machinery consumed only inside this
  file's proofs; the node's public statements use landed vocabulary exclusively.
