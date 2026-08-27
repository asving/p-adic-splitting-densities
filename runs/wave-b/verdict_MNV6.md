# verdict_MNV6 — node M3-NV6 (μ₃ `dv2SideSet` nonemptiness gap, closed)

**File:** `leanfinal/Uniformity/ChapC/C132nv6.lean` (node tag `[M3-NV6, 2026-08-27]`)

## Outcome: gap closed, no new hypothesis, no vacuity

M3-NV5 (`runs/wave-b/verdict_MNV5.md`) identified the precise blocking hypothesis for packaging
`s2Hgt₃` as a genuine `AddValuation`: an unconditional
`∀ {g}, g ≠ 0 → (dv2SideSet L Φ₂ g 21 2).Nonempty`, the μ₃ analogue of C.34's
`dvSideSet_nonempty`. This node proves it and assembles the full unconditional packaging.

**Why the gap closes with no new mathematics (the charge's honesty fence, checked):** the worry
was that two-level finiteness might secretly need `Dv2ResSurv`-style content (the μ₂-residual
survival fact, scoped to degree-`<4` coefficients at M3-NV3). It does not. `Dv2ResSurv` is about
the EXACT VALUE of a digit-PRODUCT's reduced development — needed only when multiplying two
already-located side digits. Mere nonemptiness only needs: a nonzero `f` has *some* nonzero
`Ψ`-development digit, and that digit has *finite* level-2 height. Finiteness of `dv2Pin L Ψ f j`
for `dev Ψ f j ≠ 0` unfolds definitionally to `dvSupp F (dev Ψ f j) L.u L.ℓ`, finite by
`C130s6.dvSupp_ne_top_of_ne_zero` — a fact with **no degree restriction at all**. So C.34's
`dvSideSet_nonempty` mechanism (nonzero digit exists ⟹ finite height ⟹ finite-range inf attained
⟹ `0 < ℓ` excludes the `⊤`-height escape) transcribes verbatim one level up.

## What lands

* `dv2SideSet_nonempty` — the generic μ₃ analogue of C.34's `dvSideSet_nonempty`: for any level
  datum `L`, monic positive-degree level-2 key `Ψ`, side `(u₂, ℓ₂)` with `0 < ℓ₂`, and nonzero
  `f`, `(dv2SideSet L Ψ f u₂ ℓ₂).Nonempty`.
* `s2_dv2SideSet_nonempty_at_21` — instantiated at S2's `Φ₂ = s2DepthTwoKeyAt h2 hq 2`,
  `(u₂,ℓ₂) = (21,2)`.
* `s2Hgt₃_mul_unconditional` — the charge's target: `s2Hgt₃ (g·z) = s2Hgt₃ g + s2Hgt₃ z` for
  every NONZERO `g, z`, firing C132nv4's conditional `s2Hgt₃_mul` through the fact above and the
  **already-generic** finite-pin existence `C132nv2.exists_dv2SideMin_height` (no new proof
  needed for the "(b)" half of the charge — it was already landed, unconditionally, at NV-2).
* `s2Hgt₃_mul_all` — folds in C132nv4's `s2Hgt₃_zero_mul`/`s2Hgt₃_mul_zero` to get the fully
  unconditional `∀ x y, s2Hgt₃ (x*y) = s2Hgt₃ x + s2Hgt₃ y`, exactly `AddValuation.of`'s `hmul`.
* `s2AddVal₃` — **the genuine, UNCONDITIONAL `AddValuation (Polynomial O) (WithTop ℤ)`
  instance**: C132nv5's conditional `s2AddVal₃_of_unconditional_mul` fired at `s2Hgt₃_mul_all`.
  This is no longer a conditional packaging — the blocking gap C132nv5 recorded is closed.
* `s2AddVal₃_apply` — anti-drift restriction pin (`rfl`-based via
  `s2AddVal₃_of_unconditional_mul_apply`): `s2AddVal₃ A = s2Hgt₃ A`.

## Verification

`lake env lean Uniformity/ChapC/C132nv6.lean` from `leanfinal/` — builds clean, zero `sorry`,
zero warnings. (Dependencies `C132nv4`/`C132nv5` were only `lake env lean`-checked before, not
`.olean`-built; both were built via `lake build Uniformity.ChapC.C132nv4 Uniformity.ChapC.C132nv5`
first, green, before checking this node.)

```
'Uniformity.Density.Tower.C132nv6.dv2SideSet_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv6.s2_dv2SideSet_nonempty_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv6.s2Hgt₃_mul_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv6.s2Hgt₃_mul_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv6.s2AddVal₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv6.s2AddVal₃_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry`, zero new axiom, Lean-core footprint only. Statements of `s2Hgt₃` (C132nv1),
`s2Hgt₃_mul` (C132nv4), `s2AddVal₃_of_unconditional_mul` (C132nv5), `dv2SideSet`/`dv2SideMin`/
`Dv2OnSide` (C132nv2) untouched — this node only adds new declarations in `C132nv6.lean`. No
roll-up, leanspec, or existing file touched.

## Follow-on note

NV-6 (fraction-field extension via `Valuation.extendToLocalization`), which C132nv5 deferred
pending this exact gap, is now unblocked in principle (an unconditional `AddValuation` object
now exists to extend) but is a separate task, not attempted here per the original scope
("only if a later point consumer needs it").
