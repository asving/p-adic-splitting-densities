# Unit U-SIDE verdict (af′ REVERSE plan, `docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3)

## U-SIDE — LANDED (stage 1 of `C131af.lean`)

Five locus side-data lemmas landed in the new file `leanfinal/Uniformity/ChapC/C131af.lean`
(namespace `Uniformity.Density.Tower.C131af`), exactly the plan's AF-1a/AF-1c/AF-1d/AF-2a/AF-2b:

* `towerLocus_dvSupp_eq` (AF-1a) — a locus member's cleared support is EXACTLY `μ₂E₂` (not
  merely the `≥` that `C131w.towerLocus_entry_floor` gives): top-abscissa digit `= 1`
  (monic-at-full-degree, C.131v) pins the height there to `0`, and `IsDvPure`'s right
  endpoint turns the `DvOnSide` inequality into an equation directly — no `hπ` needed.
* `towerLocus_dvHgt_zero_pin` (AF-1c) — the left-endpoint height is pinned to `μ₂f₂u₂`,
  read off AF-1a's exact support via the `DvOnSide` equation at `j = 0` and an `e₂`-smul
  cancellation (finite/`⊤` case split, `Nat.eq_of_mul_eq_mul_left`).
* `towerLocus_dvSideDeg` (AF-1d) — the side degree is `μ₂f₂`, via C.26's
  `natDegree_dvResPoly` fed the residual clause (`= towerLabel T ^ μ₂`) and
  `towerLabel_spec`'s degree-`f₂` clause. Used `(towerLabel_spec T hπ).1.natDegree_pow`
  (the `Monic.natDegree_pow` form) rather than `Polynomial.natDegree_pow`, since the stage
  field's `Field`/`NoZeroDivisors` instance is `private` (`C04.lean`'s `fieldStageField`)
  and not in scope here — the monic route needs no ring-instance side condition at all.
* `dvSideSet_nonempty_of_dvSupp_eq_coe` (AF-2a) — a finite cleared support is attained
  (`Finset.exists_mem_eq_inf`), and the attaining abscissa is on-side (finite height there).
* `towerLattice_solve` (AF-2b) — the on-line left endpoint of a support-`μ₂E₂` polynomial
  sits on the `e₂`-lattice (`dvSideMin = e₂·t₀`, `t₀ ≤ μ₂f₂`), height solved to
  `μ₂f₂u₂ − t₀u₂`. The `e₂ ∣ dvSideMin` step used `T.hcop` via
  `Nat.Coprime.dvd_of_dvd_mul_left T.hcop.symm`.

## Plan-vs-corpus finding: AF-1b already landed, not redeclared

The plan's AF-1b (`dvSideMin_eq_zero_of_isDvPure`) is **byte-identical** to a theorem
already committed at `Uniformity.Density.Tower.dvSideMin_eq_zero_of_isDvPure`
(`C35.lean`, one of U-SIDE's own imports) — same name, same signature, same one-line proof
(`Nat.le_zero.mp (Finset.min'_le _ _ hpure.1)`). Re-declaring it under the `C131af`
namespace would have been pure duplication, so AF-1a/AF-1c/AF-1d call the root-namespace
lemma directly (in scope via `open Uniformity.Density.Tower`). This is reported per the
DEC2 plan-vs-corpus overlap discipline, not treated as a gap.

## One name-lookup correction (not a mathematical finding)

The plan's proof sketch for `towerLattice_solve` names `Nat.dvd_sub'` (mathlib convention);
this Lean/mathlib pin does not have that lemma — the available one is `Nat.dvd_sub`
(`k ∣ m → k ∣ n → k ∣ m - n`, no prime). Used that instead; no other deviation from the
plan's step script.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C131af.lean` — exit 0, zero errors, zero
`sorry`.

```text
'Uniformity.Density.Tower.C131af.towerLocus_dvSupp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C131af.towerLocus_dvHgt_zero_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C131af.towerLocus_dvSideDeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C131af.dvSideSet_nonempty_of_dvSupp_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C131af.towerLattice_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only — **no cite consumed** (as the plan predicts for this stage; the declared
cite `fgmn_dv_exact_mul` first enters at AF-3, U-HEART's stage-2 extension of this same
file, through `composedKey_pow_mem_towerLocus`).

## Scope discipline

Only `leanfinal/Uniformity/ChapC/C131af.lean` (new file, this unit's plan-assigned file)
and this verdict were written. No edit to `leanspec/`, any existing `Uniformity/` file, or
any roll-up. U-ARITH's file (`C131ag.lean`) was not touched. No `git commit`.
