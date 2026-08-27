# verdict_MNV5 — node M3-NV5 (μ₃ valuation packaging)

**File:** `leanfinal/Uniformity/ChapC/C132nv5.lean` (node tag `[M3-NV5, 2026-08-27]`)

## Outcome: honest partial, not the full unconditional packaging

The μ₂ precedent `s2AddVal₂` (`C130nv5.lean:124-235`) packages `s2Hgt₂` into a genuine
`AddValuation (Polynomial O) (WithTop ℤ)` via `AddValuation.of`, whose `hmul` field requires
`∀ x y, f (x*y) = f x + f y` — fully unconditional, no side hypothesis. That worked at μ₂
because `s2Hgt₂_mul` is itself unconditional (C130nv3), discharging its internal side-set data
via C.34's `dvSideSet_nonempty` for ANY nonzero polynomial.

At μ₃, the just-landed `s2Hgt₃_mul` (`C132nv4.lean:117-127`) is **conditional**: it carries
four extra hypotheses (`hng`, `hnz` — side-set nonemptiness for each factor — and `hHg`,
`hHz` — finite-pin witnesses), because no μ₃-level analogue of `dvSideSet_nonempty` (an
unconditional `(dv2SideSet L Φ₂ g 21 2).Nonempty` for every nonzero `g`) has been proved yet
(C132nv4's own honesty note confirms this is out of scope for that node too).

**Blocking hypothesis, precisely:** an unconditional
`∀ {g : Polynomial O}, g ≠ 0 → (dv2SideSet L Φ₂ g 21 2).Nonempty`-style theorem at the μ₃
`dv2SideSet` level. Until landed, `s2Hgt₃` cannot instantiate `AddValuation.of`'s `hmul`.

## What was landed instead

* `s2Hgt₃_one_eq_zero` — the `h1`-shape bridging tooth (`s2Hgt₃ 1 = 0`), genuinely new (M3-NV1
  did not land an `s2Hgt₃_one`, unlike μ₂'s `s2Hgt₂_one`). Proved directly from `dev Φ₂ 1 0 = 1`
  (degree-0 competitor reduction) and `dv2Hgt L 1 = 0` (transported from `s2Hgt₂_one` across
  `s2Hgt₂_eq_dv2Hgt`).
* `s2AddVal₃_of_unconditional_mul` — the conditional packaging: a `noncomputable def` taking
  the missing unconditional `hmul` as an explicit hypothesis and producing the genuine
  `AddValuation (Polynomial O) (WithTop ℤ)` from it plus the three already-unconditional
  fields (`s2Hgt₃_zero`, `s2Hgt₃_one_eq_zero`, `s2Hgt₃_add_ge`). Records the gap precisely in
  the hypothesis's type; forces nothing.
* `s2AddVal₃_of_unconditional_mul_apply` — anti-drift restriction pin (`rfl`), mirroring
  `s2AddVal₂_apply`.

## NV-6 (fraction-field extension): deferred

No consumer in the M3-RP0 row inputs needs it (the μ₂ precedent's RP0 analogue,
`C130rp0.lean` Part 7, ties `S2ExactGrade`/`S2AboveGrade` to the packaged `AddValuation` only
via the `_apply` restriction identity, never via `Valuation.extendToLocalization`). More
fundamentally, `extendToLocalization` needs an actual unconditional valuation to extend, and
none exists yet at μ₃ (only the conditional packaging above). Recorded as an open follow-on
once the blocking hypothesis is discharged; not attempted here.

## Verification

`lake env lean Uniformity/ChapC/C132nv5.lean` from `leanfinal/` — builds clean.

```
'Uniformity.Density.Tower.C132nv5.s2Hgt₃_one_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv5.s2AddVal₃_of_unconditional_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv5.s2AddVal₃_of_unconditional_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry`, zero new axiom, Lean-core footprint only. Statement of `s2Hgt₃` (C132nv1) and
`s2Hgt₃_mul` (C132nv4) untouched — this node only adds new declarations in `C132nv5.lean`.
No roll-up, leanspec, or existing file touched.
