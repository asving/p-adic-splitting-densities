# Verdict — unit NV56: S2-source plan nodes NV-5/NV-6

Date: 2026-08-24 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, rows NV-5
"additive valuation packaging (CORE 4/4)" and NV-6 "fraction-field extension". File created
(the ONLY file touched): `leanfinal/Uniformity/ChapC/C130nv5.lean` (24 public declarations;
not added to `Uniformity/ChapC.lean` or any roll-up).

## NV-5 (additive valuation packaging) — LANDED

`s2AddVal₁`, `s2AddVal₂ : AddValuation (Polynomial O) (WithTop ℤ)` via mathlib's
`AddValuation.of`, assembled entirely from the landed C130nv/C130s6/C130nv3 law banks
(`_zero`, a new `_one_eq_zero` cast-tooth, `_add_ge`, and the ★ product laws `s2Hgt₁_mul` /
`s2Hgt₂_mul`) — no restatement, no new hypothesis. `WithTop ℤ` gets mathlib's generic
`LinearOrderedAddCommGroupWithTop` instance for free.

## NV-6 (fraction-field extension) — LANDED, no divergence needed

Repackaged multiplicatively (`s2Val₁`, `s2Val₂ : Valuation (Polynomial O)
(Multiplicative (WithTop ℤ)ᵒᵈ)` via `AddValuation.toValuation`); mathlib's generic instance
`[LinearOrderedAddCommGroupWithTop α] → LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ)`
supplies exactly the value-group shape `Valuation.extendToLocalization` needs, so the
"wrong shape" risk flagged in the brief did **not** materialize — no bespoke bridge, no
scope divergence. The submonoid hypothesis (`nonZeroDivisors (Polynomial O) ≤
v.supp.primeCompl`) reduces to the landed finiteness laws `s2Hgt₁_ne_top`/`s2Hgt₂_ne_top`
via `s2Val₁_eq_zero_iff`/`s2Val₂_eq_zero_iff` (proved through `AddValuation.supp`/
`Valuation.supp`, never comparing the two ambients' `0`/`⊤` literals directly — that route
hit a real trap, see below). Extended to `E = FractionRing (Polynomial O)` via
`Valuation.extendToLocalization` (`s2EVal₁`, `s2EVal₂`), converted back
(`AddValuation.ofValuation`) to `s2AddEVal₁`, `s2AddEVal₂ : AddValuation
(FractionRing (Polynomial O)) (WithTop ℤ)`. ★ **The PIN** (`s2AddEVal₁_algebraMap` /
`s2AddEVal₂_algebraMap`): the extension composed with `algebraMap (Polynomial O)
(FractionRing (Polynomial O))` equals the original `s2Hgt₁`/`s2Hgt₂`, on the nose, from
mathlib's `extendToLocalization_apply_map_apply` — exactly NP-0's consumer law. Two teeth
(`s2AddEVal₁_X`, `s2AddEVal₂_one`) reproduce landed table values through the extension.

## One real trap (recorded, not a divergence)

`AddValuation R Γ₀` is definitionally `Valuation R (Multiplicative Γ₀ᵒᵈ)` and
`toValuation`/`ofValuation` are `Equiv.refl`, so it is tempting to compare the two
ambients' zero/top literals by naive `rfl`/`rw`. That fails: `(0 : Multiplicative Γ₀ᵒᵈ)`
unfolds through a deep instance chain (`LinearOrderedCommMonoidWithZero (Multiplicative
αᵒᵈ)`'s `zero` field) that plain `rw`/`rfl` does not see through, producing a bogus
residual goal (`s2Hgt₁ A = 0 ↔ s2Hgt₁ A = ⊤`) instead of closing. Fix: route every
zero/top crossing through `Valuation.mem_supp_iff` / `AddValuation.mem_supp_iff` (which
each compare a valuation's value to its OWN ambient's `0`/`⊤`, never cross-type), bridged
by one `show` at the `Ideal`/`supp` level (genuinely `rfl`-defeq, unlike the zero literal).

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130nv5.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry); 24 `#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]`
(Lean-core only). `lake build Uniformity.ChapC.C130nv5` — success (8739 jobs; olean
available to successors, in particular NP-0). No git commit (per brief); dependency closure
(`lake build Uniformity.ChapC.C130nv3`) rebuilt clean beforehand (8738 jobs).
