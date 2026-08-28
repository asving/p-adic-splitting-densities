# VERDICT — UNIT MH14T (nodes MH.14-transport + MH.15-shape) — LANDED

**Date:** 2026-08-28 · **File:** `leanfinal/Uniformity/ChapC/C133mh14.lean` (386 lines, new; no existing file touched)
**Charge:** assemble §8's `BlockFrontier` from `BlockContext`, carrying Theorem A as the ONE
explicit hypothesis (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §8 ~line 966, §2 ~line 250).

## Status: PROVED, zero sorry, build green

`lake env lean Uniformity/ChapC/C133mh14.lean` clean; scoped `lake build
Uniformity.ChapC.C133mh14` completed successfully (olean landed, 8757 jobs).

## Landed declarations (namespace `Uniformity.Density.Tower.C133mh14`)

| decl | content | axiom footprint |
|---|---|---|
| `dvSideDeg_mul_prod_eq_zero` | point sides are stable under `below · ∏` products (M clause 2 `C133mh3.dvSideDeg_mul`, `Finset` induction anchored at `below` so the empty product never needs a side law for `1`) | Lean core |
| `residual_transport` | ★ MH.14 (§8 step 3): `f = G · Wf` with `Wf := D.below · ∏_{p ≠ (L.u,L.ℓ)} D.factor p` monic and POINT-sided (X1 `C133mh8.otherSlope_pointSide` on each other-slope factor via `D.hdistinct` + `D.hbelow` + M clause 2); τ = 1 law (`C133mh3.dvResPoly_mul_gen`) gives `R(f) = R(G)·R(Wf)` with `R(Wf)` a unit (degree = side degree = 0, constant coeff ≠ 0 by `natDegree_dvResPoly`), hence `L.r ∣ R(f) → L.r ∣ R(G)` at every pin | Lean core |
| `TheoremAStatement` | Theorem A's exact §2 statement as a Prop-def, **byte-identical body** (diff-checked) to the machine-checked shape elaboration `MHENS.EngineExistenceStatement` (`scratch/MHENS_probe.lean:71-94`) | Lean core |
| `blockFrontier_of_context_of_theoremA` | ★ MH.15 (§8 steps 1–6): `BlockContext L f` + `hA : TheoremAStatement O` ⟹ `BlockFrontier L f` (both signed shapes consumed byte-as-is from `C35.lean`; never redeclared) | Lean core + `exists_dvDissection` |

## Cite discipline (as the unit charge prescribed)

**`exists_dvDissection` (`C33Cite.lean:76`, allowlisted GN15 Thm 2.3 + FGMN arXiv-v3 Thm 6.6)
is carried by exactly ONE declaration: `blockFrontier_of_context_of_theoremA`** — the expected
and correct footprint for the dissection consumer. The transport pair and the statement shape
are Lean-core. `fgmn_dvDissection_factor_eq` is NOT consumed.

## Theorem A pinning record (transcribed, never weakened)

Pinned per the probe shape (recorded in the module header): strict floor
`ℓ * ((F.e₁*F.f₁) * F.h) < u` (MHDISP-corrected form); `hpin : F.Pin H₀` (definitionally
`LevelDatum`'s raw `npHgt` pin, `C14a.lean:214`); clause-2 degrees as
`ℓ * (F.e₁*F.f₁) * natDegree`; clause-4 heights as `ℕ∞`-casts; clause-5 exact residuals in
∀-PIN form (C.25 junk-total design, same convention as the signed Theorem B clause).

## Associativity/commutation bookkeeping (§8 step 6 vs `theoremC_placement`)

`theoremC_placement`'s `hsplit : f = P * Q * W` parses `(P*Q)*W`; the §8 factorization
`f = G·Wf`, `G = g₁·g₂` composes to `f = (g₁·g₂)·Wf` — definitionally the required shape at
`P := g₁`, `Q := g₂`, `W := Wf`; the witness divisibility `g₁ ∣ f` re-associates once
(`mul_assoc`). One repo-relevant Lean lesson: `f` cannot be `rw`-rewritten in goals mentioning
`D : DvDissection F f` (motive failure through the structure's implicit argument) — all
transports go through `Eq.trans`/`calc` and two `subst`-based congr helpers
(`dvSideDeg_eq_zero_congr`, `dvResPoly_congr`).

## What this closes / what remains

F1.H3's assembly shape is CLOSED MODULO Theorem A: when MH.5/MH.7/MH.9 land
`TheoremAStatement O` as a theorem, `blockFrontier_of_context_of_theoremA` discharges `hA` in
one application, and the landed `blockFactor_spec_of_frontier` (`C35.lean:310`) then yields all
four `blockFactor_spec` clauses. Theorem A itself remains OPEN (MH.5 clause lemmas, MH.7,
MH.9), as does MH.1→MH.2/MH.3's transcription root for M — none of that is claimed here.
