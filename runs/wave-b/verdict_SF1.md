# Verdict — unit SF1: AMBIENT SPLIT re-type of `S2SourceFrontier`

Date: 2026-08-24 · Node 1 of the corrected S2-source campaign
(`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §2, §5, §6 rows SF-1..SF-4)
Files edited (sanctioned, and ONLY these): `leanfinal/Uniformity/ChapC/C130s17.lean`,
`leanfinal/Uniformity/ChapC/C130s18.lean`.

## What changed — C130s17.lean (the bundle + conditionals)

1. **`SplitNodePointSource` (NEW, general depth, C130s17 namespace)** — plan §2's REQUIRED
   CORRECTION as a structure: C130k's `NodePointSource` byte-parallel EXCEPT the four
   evaluation fields (`coeffHom : O →+* E`, `coord : Point → E`, `valueOn : ℕ → E → WithTop ℤ`,
   `pointHgt_eval`) now land in a separate valued ambient `E` (bare `Field E`, NO
   `Algebra Kt E`, NO map `E → L`); letters/reads (`ambientLetter`, `psi_root`,
   `canonicalRead`) stay in `L` with `[Algebra Kt L]`.  Companions at the split typing
   (verbatim ports of landed C130pt/C130st defs): `legalPoint`, `legalPoint_mem`,
   `stageCarrier`.  C130k/C130fg themselves are untouched (out of sanction; plan SF-3).
2. **`S2SourceFrontier` RE-TYPED** to `(E : Type uE) [Field E] (L : Type uL) [Field L]
   [Algebra Kt L]` with `node : SplitNodePointSource (L := L) (S2DepthTwo h2 hq) E …`; the
   three CC-6 table ties, `fgmn`/`fgmnLaws`, `grade_compat`, `letter_compat` unchanged in
   shape.  `h2 hq` made implicit inside the `S2SourceFrontier` namespace (dot-notation fix).
3. **`S2SourceFrontier.LegacyEvaluation` (NEW, QUARANTINED)** — exactly U13's refuted
   single-ambient evaluation half (L-valued `coeffHom`/`coord`/`valueOn` + 4 valuation laws
   + `pointHgt_eval` against the split node's `pointHgt`).  Documented as uninhabitable at
   S2 (the U13 char-2 contradiction transplants verbatim).  `withLegacy` rebuilds the legacy
   `NodePointSource` from split node + `ev`.
4. **Conditional constructors updated**: `toChainRealization`, `calculusNonempty`,
   `realizedInput`, `s2RealizedInput` now take the extra explicit `ev : S.LegacyEvaluation`
   (the packaging into the still-un-split `ChainRealization` needs it; empty at S2, so these
   are packaging shapes with the vacuity CONCENTRATED in one named argument).  `point`,
   `point_mem`, `thresholdZ/Nat`, the four reads, and `stageTwo_view` are `ev`-FREE on the
   split node.  Repository side (`s2RepositoryRealization` + 4 pins), `S2InputData`,
   `toArisingCore`, `s2InputPolynomial*`, `s2ArisingCore`: byte-untouched.
5. **Module + structure docstrings**: U13 refutation recorded (dated, with the derivation
   chain), the re-type dated 2026-08-24, and the old vacuity caveat REPLACED by the
   corrected conditionality statement (split bundle = campaign target, not claimed
   inhabited, no longer char-2-refutable; `ev` = the explicit empty-at-S2 residual until
   SF-3 re-types the carrier).

## The NON-VACUITY tooth (plan SF-4)

* `s2EvalHom : O →+* FractionRing (Polynomial O)` (constants through `Polynomial.C`),
  `s2EvalCoord` = the rational-function variable `X`, `s2EvalHom_injective`.
* ★ `s2Eval_C_two_ne_zero : (2:O) ≠ 0 → eval₂ s2EvalHom s2EvalCoord (C 2) ≠ 0` — the EXACT
  slot U13's refuter fired on (in the old typing this evaluation was FORCED to `0` by char 2
  of the single ambient, giving `IsEmpty`); provably nonzero at the probe, so the char-2
  derivation cannot replay against the re-typed bundle.  S2-pin example via `h2.ne_zero`.
* An `example` elaborating the ambient PAIR at the probe:
  `S2SourceFrontier h2 hq (FractionRing (Polynomial O)) ((S2DepthTwo h2 hq).fld 2)`.
* NOT claimed: any inhabitant of `S2SourceFrontier` (that is the campaign, plan §6).

## What changed — C130s18.lean (socket applications)

`universe` += `uE`.  §4 S2Gate and §AuditS2: premise re-typed to
`(S : S2SourceFrontier h2 hq E L) (ev : S.LegacyEvaluation)`; every `S.s2RealizedInput` /
`S.toChainRealization` becomes `(S.s2RealizedInput ev)` / `(S.toChainRealization ev)` in
`s2_ladder_socket_application`, `s2_deepTwist_socket_application`, the end-to-end refinement
`example`, and `s2_arenaAgreement_not_uniform`.  `s2ArisingCore_r/_i` pins unchanged.
Module docstring item 2 + §4/§AuditS2 headers carry the corrected conditionality; general
sections (§0–§3, §5 audit, §6 lint) byte-untouched.

## Verification

* `lake env lean Uniformity/ChapC/C130s17.lean` — CLEAN (0 errors, 0 warnings, 0 sorry);
  40 `#print axioms` rows, all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* `lake env lean Uniformity/ChapC/C130s18.lean` — CLEAN; 28 rows, Lean-core only.
* `lake build Uniformity.ChapC` — Build completed successfully (8803 jobs).
* `lake build Uniformity.ChapI` — Build completed successfully (8710 jobs).
* s18's documented non-swallowing grep-tooth re-run: no output, rg exit 1 (PASS).
* `git status`: only the two sanctioned files modified.  No sorry / axiom / unsafe added.

## Flags for the orchestrator

* `leanfinal/scratch/U13_probe.lean` (NOT in build targets, NOT edited — outside sanction):
  its node-level certificate `no_s2_node_source` still elaborates (C130k untouched), but the
  frontier-level `no_s2_source_frontier` now has an arity mismatch against the re-typed
  bundle — as it must (the refuted typing no longer exists).  SF-0's impossibility landing
  should pin the certificate at the historical typing in its diagnostic module.
* `SplitNodePointSource`/`legalPoint`/`stageCarrier` are deliberate verbatim ports of
  C130k/C130pt/C130st decls at the split typing, living in the C130s17 namespace; the SF-3
  consumer ripple should unify them with the carrier-skeleton originals when
  `NodePointSource`/`ChainRealization` are themselves re-typed (removing `LegacyEvaluation`
  and the `ev` arguments end-to-end).
