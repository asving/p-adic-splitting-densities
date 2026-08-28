# Verdict: MH.4 — Corollary M-monic (the monic-residual law)

**Status: LANDED, unconditional, zero `sorry`, Lean-core axiom footprint.**

## What was asked

Transcribe Corollary M-monic (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §3.5, node
MH.4 of §9's table) into a new file `leanfinal/Uniformity/ChapC/C133mh4.lean`: for monic
`(u,ℓ)`-pure `g` with `D′ := F.e₁ * F.f₁` dividing `g.natDegree`, (a) the left-side height
pin `M₀ = u · dvSideDeg`, and (b) the level residual `dvResPoly … g …` is itself `Monic`
(B.41's `hcu1` twin, one level up).

## What landed

File: `leanfinal/Uniformity/ChapC/C133mh4.lean` (new; 169 lines; namespace
`Uniformity.Density.Tower.C133mh4`).

Two theorems, both fully proved (no `sorry`, no new `axiom`):

1. `dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure` — clause 1: `M₀ = u * dvSideDeg F g u ℓ hne`.
2. `dvResPoly_monic_of_isDvPure` — clause 2 (the headline): `(dvResPoly F H₀ hpin g u ℓ hne
   M₀ hp).Monic`.

Both carry the doc's exact hypothesis set: `F : KeyFrame O π`, `g.Monic`, `0 < g.natDegree`,
`0 < ℓ`, `Nat.Coprime u ℓ`, `IsDvPure F g u ℓ`, `F.e₁ * F.f₁ ∣ g.natDegree`, side-nonempty
`hne`, and the pin `hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)`; clause 2 additionally
carries `Irreducible π` and `0 < F.h` (needed for `twistRead_one`).

**AxCheck** (`lake env lean Uniformity/ChapC/C133mh4.lean`, exit 0):
```
'Uniformity.Density.Tower.C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh4.dvResPoly_monic_of_isDvPure' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Lean-core only, both declarations, zero `sorryAx`.

## Proof route (mirrors B.35c's order-0 `height_eq_of_pure` / B.41b's `hRfmonic`)

Order-0's `IsPure` packages both endpoints as raw `OnSide` equations; order-1's `IsDvPure`
(C.29) packages them as Finset membership instead (the extra finiteness conjunct `DvOnSide`
carries), so the raw on-side equations are first extracted via `dvOnSide_of_mem_dvSideSet`
(C.35). Then: `dvSideMin = 0` and `dvSideMax = deg g / D′ = ℓ·dvSideDeg` (C.35's endpoint
lemmas) give `deg g = dvSideMax · F.key.natDegree`, so `dev F.key g dvSideMax = 1`
(`dev_top`, B.13a) and hence `dvHgt F g dvSideMax = F.stageHeight 1 = 0` (`stageHeight_one`,
C131ae). Combining the two on-side equations at `j = 0` and `j = dvSideMax` in `ℕ∞` and
clearing the `ℓ`-scaling gives `M₀ = u·dvSideDeg`. For monicity: `natDegree_dvResPoly`
(C.26) gives `natDegree (dvResPoly …) = dvSideDeg`; unfolding `Polynomial.Monic`/
`leadingCoeff` to a bare coefficient goal and evaluating `dvResPoly`'s defining sum
(`Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`) at `t = dvSideDeg` lands exactly on the
top digit `dev F.key g dvSideMax = 1` read at height `M₀ - dvSideDeg·u = 0`, which is `1` by
`twistRead_one` (C133mh0's MH.0c remainder).

## Named inputs consumed (all pre-existing, none modified)

- `Uniformity.ChapC.C133mh0`: `twistRead_one` (MH.0c remainder), transitively `C131ae.stageHeight_one`.
- `Uniformity.ChapC.C35`: `IsDvPure`, `dvSideMin_eq_zero_of_isDvPure`, `dvSideMax_eq_of_isDvPure`,
  `natDegree_div_eq_of_isDvPure`, `dvOnSide_of_mem_dvSideSet`; transitively C.26
  `natDegree_dvResPoly`, C.25 `dvResPoly`, C.29 `IsDvPure`/`HasLabel`, C.07 side cluster.
- `Uniformity.ChapB.B13a`: `dev_top`.
- `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` (transitively imported, `HenselFactorization.lean`).

**Not imported/consumed: `C133mh3` (MH.3).** Per the doc's `[MHFIX 2026-08-27]` closing note
to §3.5, once Theorem M's clause 3 is `τ = 1` identically for all nonzero inputs (which MH.3
already establishes), MH.4's own role shrinks to exactly the monicity/value pair proved here
— a fact about a single polynomial `g`, not a product — so no product-law dependency is
needed inside this file. (MH.3 is what a downstream Theorem-A assembly would combine this
corollary with; that assembly is out of MH.4's scope.)

## Opens / notes

- None. Both theorems are unconditional and fully discharged; no `sorry`, no BLOCKED-BECAUSE.
- `hgpos : 0 < g.natDegree` is carried on both theorems (faithful to the doc's stated
  hypothesis list) but is not actually needed by either proof; `set_option
  linter.unusedVariables false in` is used per-declaration to suppress the resulting lint,
  matching this codebase's standing convention for intentionally-carried-but-unused
  hypotheses (e.g. C25's `hpin₂`).
- No existing file was edited; no `git` operations performed.
