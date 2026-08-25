# verdict_UARITH — af′ reverse plan, unit U-ARITH

**Node:** AF-5a / AF-5b (`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3, unit U-ARITH).
**File:** `leanfinal/Uniformity/ChapC/C131ag.lean` (new, stage 1 — U-ASSEMBLE extends it later
with AF-6a/AF-6b; not touched here).
**Build:** `cd leanfinal && lake env lean Uniformity/ChapC/C131ag.lean` — exit 0, zero errors,
zero `sorry`, zero new `axiom`.

## Delivered

* `Uniformity.Density.Tower.C131ag.budgetFloor_le_of_succ_le` (AF-5a, pure `ℕ`): for
  `0 < d` and `X + 1 ≤ d * v + w`,
  `(if X < w then 0 else (X - w + d - 1) / d + (if (X - w) % d == 0 then 1 else 0)) ≤ v`
  — `budgetFloor`'s ceiling-plus-tie display, in its own spelling, bounded by any `v` clearing
  the strict floor. `#print axioms` → `[propext, Quot.sound]`.
* `Uniformity.Density.Tower.C131ag.budgetFloor_le_addVal_of_wtCoeff` (AF-5b, the `ℕ∞`
  wrapper): `((μ₂ - j) * T.E₂ + 1 : ℕ∞) ≤ wtCoeff T c a b → (budgetFloor T μ₂ j a b : ℕ∞) ≤
  addVal O c`. `#print axioms` → `[propext, Classical.choice, Quot.sound]` (the `Classical.choice`
  comes from the ambient `ENat`/`IsDiscreteValuationRing` instances, not from any new axiom or
  cite — this unit's mathematical content is Lean-core).

Both signatures match `SIG_AF5a`/`SIG_AF5b` in `leanfinal/scratch/DEC2_check.lean` byte-for-byte
(mod. the `theorem`-vs-`def Prop` wrapper), so no drift from the plan's elaboration check.

## Proof notes

* **AF-5a** is proved directly by case split on `X < w`, never handing the pinned `omega` a
  combined mod/div goal (the known incompleteness genre): every division/mod fact is
  discharged first via `Nat.div_add_mod`, `Nat.mul_add_div`, `Nat.div_eq_of_lt`, with `omega`
  only ever closing purely linear residues (and, in the `(X-w)%d ≠ 0` branch, only after an
  explicit `ring`-proved `hmul : d * ((X-w)/d + 1) = d * ((X-w)/d) + d` — without it `omega`
  cannot relate the two nonlinear atoms `d * ((X-w)/d + 1)` and `d * ((X-w)/d)`, which is
  exactly the failure mode hit on the first compile attempt here). The whole `hkey` case split
  is copied from the already-landed `C52.budgetFloor_le_iff` (same arithmetic, there embedded
  in an iff against `gridWeight`); AF-5a factors it out as a bare `ℕ` lemma with `X` generic
  (no `μ₂,j` order hypothesis needed, since `budgetFloor`'s body is literally this display at
  `X := (μ₂-j)*T.E₂`, per BRIDGE 5 in `DEC2_check.lean`).
* **AF-5b** unfolds `wtCoeff` and `slotOffset` (both plain non-recursive `def`s, unfoldable by
  `rw` in this codebase — same move as `C131ae.budgetFloor_wtCoeff_bound`), converts the `⊤`
  case by `le_top`, and in the finite case reduces to AF-5a by `exact_mod_cast` casting; the
  final `budgetFloor T μ₂ j a b ≤ v` term produced by `budgetFloor_le_of_succ_le hposE hle'`
  unifies with the goal purely by the implicit-argument inference off `hposE`/`hle'`'s types
  (never needing to unfold `budgetFloor` itself during elaboration — confirms BRIDGE 5's `rfl`
  claim empirically, not just by inspection).
* Two attempts total: first compile failed only on the missing `hmul` step (bounded repair,
  1 round); no other issues.

## Scope discipline

Only `leanfinal/Uniformity/ChapC/C131ag.lean` (new) and this verdict were written. Did not
touch `leanspec/`, roll-ups, `C131af.lean` (U-SIDE's file, run in parallel), or any other
unit's file. No `git commit` taken.
