# Verdict DWC — deep witness campaign decomposer

**Date:** 2026-08-28  
**Verdict:** **GO — extend S2 to depth four, with a proper μ4 step and a μ5 refinement.**

## Tower chosen

Keep the S2 tower and its landed proper key `C132rp10b.g8`.  Extend the proper tower to
stage four with the documented worked row `(e4,f4,u4)=(2,1,85)`, so
`Dcum 3=8`, `Dcum 4=16`, and the depth-three μ4 calculus has triple `(2,1,85)` and builds
the degree-16 `keyAt 4`.

At depth four, do **not** use the naive proper μ5 row `(2,1,341)` for MP1: normalized
existence would have degree 32, while an exact recentering of the degree-16 block key must
remain degree 16; `2∤341` also repeats the landed odd-grade warning.  Use the refinement
calculus `(e',f',u')=(1,1,171)` instead.  It has the tight floor `170<171`, recipe degree
`1*1*16=16`, and no preceding-group divisibility obstruction.  This is operator data, not a
fifth proper `DeepTower` stage, and its source/GN admissibility is a stop-line gate.

The mass-two input is planned as `leaf^2`, where the refinement leaf is
`keyAt 4 - chainNormBelow 4 171`.  The certified normalizer row is
`towerNorm 3 171=(1,1,[1,1,1])`, hence degree `15<16`; the target mass equation is
`16+16=32`.  This gives a genuine candidate `Λ≠0` and `leaf∣leaf^2`, subject to the named
Lean residual and GN-binding nodes.

## Campaign size and gates

The blueprint contains **69 formalization nodes**, each scoped to 30–60 minutes.

Stop-line gates:

1. Land actual GN principal-slope and slope-residual operators.
2. Add selected completed-factor and base-change-to-`O[x]` binding.
3. Re-sign `GNCitePayload`/`RecenterStep` with those bindings before payload construction.
4. Re-sign WLE's scratch exporter as genuinely per-level: its current fixed-triple total
   calculus family cannot combine `(2,1,85)` at depth three with `(1,1,171)` at depth four.
5. Promote one shared owner-attached deep-level record for WLE calculus/wiring,
   `CanonicalGeneratorDescent`, and the calculus-to-canonical-letter equality.
6. Confirm `(1,1,171)` is a source-faithful GN refinement and is not treated as a proper
   fifth tower stage.
7. Compile anti-cook falsifiers for zero reads, arbitrary residuals, bare-carrier
   calculus extraction.
8. Land the Lean numeral/normalizer pins after the Python certificate.
9. Prove the mass-two input keyfree after fraction-field mapping.
10. Enforce GCW-6: no public unwired depth-four witness may land.

**Single highest-risk node:** `C4` — the GN analytic binding at `g=leaf^2`: actual principal
slope membership, equality with the actual slope residual, multiplicity one of `X+1`, and
identification/descent of the theorem-selected completed factor to the exact `leaf`.

## Numeric certificate

`python3 verification/dwc_tower_cert.py` exits 0 and prints the stage parameters, three
floor rows, both new normalizer rows, the unique live deep index `[3]`, and the mass/input
counts.

Full blueprint:
`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md`.

No landed `.lean` or leanspec file was edited.  No git commit was made.
