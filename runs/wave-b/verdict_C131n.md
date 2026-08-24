# Unit C131n verdict

File: `leanfinal/Uniformity/ChapC/C131n.lean` (Chapter C, NODES C.131n′–o′, per
`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.7 and §5).

## C.131n′ — LANDED

F9 (`recarry_price`) with all order hypotheses visible, the guarded decomposition, the
explicit no-truncation lemma (finding #7), and the exact cancellation; F10
(`recarry_moves_up` / `recarry_never_down` / `recarry_moves_up_one` /
`recarry_step_zero`), stated over an arbitrary commutative ring as thin public wrappers
on C.127's landed generic `devQ` API (`devQ_mul_pow`, `devQ_mul_pow_of_lt` — reused, not
redefined); the tie `devQ_eq_quotDigit` (+ `quotIter_divByMonic_comm`) making C.131h′'s
ledger F6–F8 available at C.71 `devQ` coordinates; and the arbitrary-floor ledger
`quotIter_floor_of_le` / `quotDigit_floor_of_le` (F8 generalized off the exact multiple
`μE₂`, needed for forward feeding).

Declarations: `recarry_decomp`, `recarry_no_truncation`, `recarry_cancel`,
`theta_le_floor_add_paid`, `recarry_price`, `recarry_step_zero`, `recarry_moves_up_one`,
`recarry_moves_up`, `recarry_never_down`, `quotIter_divByMonic_comm`,
`devQ_eq_quotDigit`, `quotIter_floor_of_le`, `quotDigit_floor_of_le`.

## C.131o′ — SUPPLY (F11 parameterized; concrete instantiation blocked, see below)

The census floor is landed **parameterized over the tagged census**: `PaidFloor T base t`
is §2.6's pricing invariant (`WT ≥ base + paid·δ`); its transport is proved through every
census move (`xCarryStep_paidFloor` — both x-carry branches at the pre-carry base;
`paidFloor_preserve` — tail multiplication; `paidFloor_transport`(+`_digit`) — the
F9+F10+F6 splice: absorbing `j−j′` key factors keeps the invariant at the new ledger
base); and the two floor conclusions are proved:

* ★ `census_floor` — any finite tagged census at coordinate `j` with all tags ≥ 1 and the
  invariant at base `(μ₂−j)E₂` has erased weight ≥ `Θ_j = T.theta μ₂ j`;
* ★ `census_digit_floor` — an entry census at base `μ₂E₂`, all tags paid, keeps the `Θ_j`
  floor at every ledger digit `j ≤ μ₂` of its erased sum (forward feeding).

Supporting: `paidFloor_mono`, `le_WT_eraseTagged`, `theta_le_WT_of_paidFloor`.

**Precise missing object for the unparameterized F11:** the tagged-census discrepancy
normal form (with its erasure/semantic identification, v2 Cnv13) — the same object named
missing by `runs/wave-b/verdict_C131u.md`; it is node C.131v′'s deliverable (unit C131v,
in flight). No statement about `shadowDev T f j − dev (composedKey T) f j` is claimed
here; C.131w′ (`shadow_floor`) is the intended splice point of `census_floor` with
Cnv13 + Cnv11.

## Verification

From `leanfinal/` (C131h's olean was built first: `lake build Uniformity.ChapC.C131h`):

```text
lake env lean Uniformity/ChapC/C131n.lean
```

Exit code 0, zero warnings. All 23 `#print axioms` lines are Lean-core only
(`propext`, `Classical.choice`, `Quot.sound`; the pure-ℕ lemmas less). No `sorry`, no
new axiom, no `unsafe`. New definition: `PaidFloor` only (hypothesis-side invariant
carrier, documented in the module docstring).
