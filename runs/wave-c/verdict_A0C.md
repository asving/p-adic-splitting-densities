# VERDICT — UNIT A0C: the five cubic value theorems (2026-08-28)

**HEADLINE: A0-CUBIC IS CLOSED.** All five `IFC6.CubicValueLaw` instances are PROVED, the
reduction socket fired, and the capstone field `a0` at `n = 3` is landed UNCONDITIONALLY:

```
Uniformity.Density.IFC7.decidedSliceAt_three : DecidedSliceAt 3
-- axioms: [propext, Classical.choice, Quot.sound]   (Lean core ONLY — not even a cite)
```

File: `leanfinal/Uniformity/ChapI/IFC7.lean` (~2450 lines, NEW; zero `sorry`, zero new
axiom, no landed file touched — every landed name consumed as-is).  Verified:
`lake env lean Uniformity/ChapI/IFC7.lean` — zero errors; the 12-line AxCheck footer
prints Lean core only for every headline declaration.

## The five-law table

`q = residueCard O`, `Φ = q⁴+q³+q²+q+1` (so `(q−1)Φ = q⁵−1`).  Every row holds for the
GENUINE density over EVERY complete DVR with finite residue field — both characteristics,
wild primes (`p = 2` for `(2,1)`, `p = 3` for `(3,1)`) included.

| type | value | numeric cert | Lean |
|---|---|---|---|
| `c3split` `(1,1)³` | `q³(q²−q+1)/(6(q+1)Φ)` | PASS (4 legs) | **PROVED** (`cubicValueLaw_split`, via `sharp_split` + squeeze) |
| `c3linInert` `(1,1)(1,2)` | `q³(q²+q+1)/(2(q+1)Φ)` | PASS | **PROVED** (`cubicValueLaw_linInert`) |
| `c3inert` `(1,3)` | `q³(q+1)/(3Φ)` | PASS | **PROVED** (`cubicValueLaw_inert`) |
| `c3linRam` `(1,1)(2,1)` | `q(q³+q+1)/((q+1)Φ)` | PASS | **PROVED** (`cubicValueLaw_linRam`) |
| `c3ram` `(3,1)` | `(q²+1)/Φ` | PASS | **PROVED** (`cubicValueLaw_ram`) |

These are COROLLARY HM3.D's rationals (`spec/EFF-HMENU3.md` `.17`) exactly — G61's
"lower bounds, NOT the densities" honesty rider is now RETIRED BY PROOF: the densities
themselves are Lean theorems (`IFC7.genuineDensity_three_exact`).

## Numeric certification (examples-first; ran BEFORE any Lean)

`verification/a0c_cubic_cert.py` (+ committed output `a0c_cubic_cert_output.txt`):
**38 checks, 0 failures** across four decorrelated legs:

* **A (symbolic, sympy)** — Σ = 1; the self-similar stratum recursion (derived
  independently for this unit) is satisfied by the closed forms as a fixed point — this
  is the identity the Lean proof follows; `E[#roots] = q/(q+1)`; the `q = 2, 3` blueprint
  anchors `(4/93, 28/93, 8/31, 22/93, 5/31)` / `(63/968, 351/968, 36/121, 93/484, 10/121)`;
  transcription tie against `verification/padic_types.monic_cubic_pred` at `q = 2..40`;
  G61's transcribed bounds stay below the targets.
* **B (exact `F_q` strata)** — brute-force residue factorization-shape counts at
  `q = 2, 3, 5, 7` match the five strata formulas.
* **C (exhaustive finite level)** — every coefficient class classified by the repo's exact
  integer oracle: `p = 2` through level 8 (16.7M classes), `p = 3` level 5, `p = 5`
  level 3; max deviation from the closed forms shrinks monotonically to `7.4e-4`.
* **D (decorrelated PARI)** — `gp` `nfinit([f,[p]])`/`idealprimedec` (knows nothing of the
  recursion), first calibrated against the LEAN-PROVED `n = 2` values, then 4000 samples
  per prime at `p = 2, 3, 5, 7`: every cell within 4σ, zero stray shapes.

## Proof architecture (the squeeze + the fixed-point loop; all in IFC7.lean)

1. **Sharp lower bounds suffice** — `totalMass_three` (H97b, landed: the five genuine
   densities sum to 1) + the rational identity Σ targets = 1 + the `n = 3` drainage tie
   `genuineDensity_three_eq_decidedDensity` (H97b) turn five sharp LOWER bounds into five
   equalities.  No upper-bound machinery anywhere.
2. **Each sharp bound is ONE fixed-point step**, no infinite tower: for each type,
   `decidedSeq (M+3) ≥ b_σ(M) + q⁻⁵·decidedSeq M`, passed to the limit
   (`decidedSeq_tendsto`) and solved.  The decided families realizing the step:
   * *level-1 bases* (separable reductions): `coeffFactor`-preimages of the landed level-1
     certificates — `inert3_decided`, `linInert_decided_res`, and the NEW
     `split3_decided_res` (G.55 + G.60's never-before-consumed `Split3` census);
   * *recentred Newton-polygon bases* (cube reductions): H97r2's E/L/R certificates placed
     at EVERY residue centre γ (G.61d/e had used γ = 0 only — exactly why their bounds
     weren't sharp);
   * *DBL bases* (reduction `(X−r̄)²(X−s̄)`): Hensel-peeled linear factor
     (`decidedAt_of_peel_decided`, H97r4) × a quadratic part that is either directly
     Eisenstein or a π-rescale of an `n = 2` decided class — consuming the LANDED exact
     `n = 2` values (G.46/G.47) as the inner tower, closed form and all;
   * *the loop* (cube reduction, recentred coefficients in `π³O × π²O × πO`): the
     π-rescale of an ARBITRARY level-`M` decided class through H97r3's mixed-precision
     `MBox` — the exact mirror of the landed sharp UNDECIDED count
     `card_undecidedTriple_sharp` (same q⁴ fibre, opposite direction).
3. The landed invariance kit carries everything: `typeOf_shift`/`typeOf_shiftVec`
   (translation), `typeOf_extract`/`typeOf_scaleRoots` (scaling), `cubeCoeff_injective`
   (centre recovery), `peel_congr`/root-uniqueness (DBL injectivity), `dvdSet`/`exactSet`
   digit cards (G.14), G.60 censuses, `card_preimage_mtrunc`/`card_preimage_coeffFactor`.

Execution: skeleton-first (40 sorries, statements compiled before any proof), then four
parallel forks filled §2 (cube families), §3 (residue shape tags), §5 (quadratic parts),
§6 (level-1 bases) while the orchestrator proved §0/§1 (kit), §4 (DBL core: assembly,
decidedness, injectivity via the unit-cofactor root-uniqueness argument), §7 (the five
step inequalities), §8–§10 (limits, squeeze, laws).  Compile-verified after every
increment.

## What fires downstream

* `IFC6.decidedSliceAt_three_of_values` consumed with all five laws ⇒
  `decidedSliceAt_three : DecidedSliceAt 3` — the capstone field `a0` at `n = 3`, the
  literal degree-3 slice of `UniformityStatementDecided`.  Together with the landed
  `DecidedSliceAt 2` (I.02 gate) and `n = 1` (Gates), the uniformity theorem's
  decided-value law now holds at `n = 1, 2, 3` UNCONDITIONALLY, Lean-core.
* `genuineDensity_three_exact` supersedes G61's `lowers_three` as the citable degree-3
  statement (G61 remains true and untouched).

## a0 at `n ≥ 4`: what this unit teaches (map row update)

The architecture GENERALIZES per degree; no new mechanism is needed, only per-degree
supply.  At degree `n` the loop stratum is the rescale box `(πⁿ, …, π)·O`, loop factor
`q^(1 − n(n+1)/2)` (`= q⁻⁵` at `n = 3` ✓), and the base strata are indexed by the residue
factorization shapes with per-factor sub-towers consuming the EXACT values at degrees
`< n` — exactly how this file consumed G.46/G.47.  The missing degree-4 inputs are:
(i) `c4*` type defs + `typeOf_four_cases` (G.52/53-analogues), (ii) the H97-analogue
drainage/`totalMass_four` (the undecided-side loop at the same rescale box), (iii) the
degree-4 residue censuses (G.60-analogue: quartic shape counts over `F_q`), (iv) NP
certificates for the new Newton-polygon leaves (slopes 1/4, 3/4, and the slope-1/2
Artin–Schreier atom — the wild `p = 2` leaf that `cert_crosschecks.py` §9 already
certifies numerically as `q/(q+1)`), and (v) quadratic×quadratic Hensel products (the
peel generalized from linear cofactors to the coprime-factor lemma
`typeOf_of_residual_coprime`, landed).  IFC7 is the template; (iv)–(v) are the only
genuinely new proof genres.

## Files

* `leanfinal/Uniformity/ChapI/IFC7.lean` — NEW, the unit's Lean content (⚠ trust
  boundary: every statement NEW, flagged for standing review; consumption-only of landed
  names; placement adjudicated ChapI since it fires IFC6's socket and imports ChapG/ChapH
  upward only).
* `verification/a0c_cubic_cert.py`, `verification/a0c_cubic_cert_output.txt` — the
  four-leg numeric certification (38/38).
* `leanfinal/scratch/a0c_assembly.lean` — prototype scratch (kept per scratch convention).
* No landed or leanspec file modified (verified: `git status` shows no tracked-file
  changes from this unit); no commits made (unit ran under "no git ops").

## Review queue rows (for the standing review)

1. `IFC7.CubicValueLaw`-instances' STATEMENTS are IFC6's (already queued as CHA rows); the
   new value-bearing statements here are `genuineDensity_three_exact` and the five
   `sharp_*` — check the five rationals against EFF.HMENU3.17 (they are byte-matched to
   the cert script's table, which is 4-leg certified).
2. `split3_decided_res` is the one NEW level-1 certificate (G.55 + G.60 assembly).
3. The `⟨(1,1) ::ₘ σ'.data⟩ = c3linRam/c3linInert/c3split` identities are definitional
   (accepted by `rfl`/defeq) — no multiset reordering hides there.
