# MOVES Lean census 1 — 2026-07-26

Census of every `.lean` file in `lean/LeanUrat/Moves/` except `Defs.lean` (45 files:
the 32 safe fan-out units per `MANIFEST.json`, the 12 round-3 `_R3` units on disk per
`MANIFEST_R3.json`, and `DefsT.lean`).

Method, per file:
- **compiles**: `cd lean && lake env lean LeanUrat/Moves/<file>` (sequential; the 16
  modules imported by other units were `lake build`-pre-compiled so imports resolve;
  prebuild exit 0, "Build completed successfully (8575 jobs)").
- **sorries (grep)**: `grep -c sorry <file>` — counts LINES containing the string
  `sorry`, including doc comments. **sorry warns** is the compiler's count of
  "declaration uses 'sorry'" diagnostics = the number of declarations with a real
  `sorry` (0 means the file is genuinely sorry-free).
- **fence**: the MANIFEST statement string searched verbatim in the file at a
  declaration position (line start, followed by ` :=`). `ok*` = statement found
  token-identical but line-wrapped (NOT byte-identical; whitespace-only difference,
  displayed below). `_R3` files are fenced against `MANIFEST_R3.json` (their
  statements are not in `MANIFEST.json`).

| file | compiles | time | sorries (grep) | sorry warns | fence | manifest unit |
|---|---|---|---|---|---|---|
| DefsT.lean | yes | 5s | 1 | 0 | n/a (defs file, no manifest entry) | — (—) |
| L0_FactA_exists.lean | yes | 5s | 0 | 0 | ok* (line-wrapped) | L0.FactA_exists (MANIFEST.json) |
| L0_FactB_unique.lean | yes | 5s | 0 | 0 | ok | L0.FactB_unique (MANIFEST.json) |
| L0_GRa.lean | yes | 5s | 0 | 0 | ok | L0.GRa (MANIFEST.json) |
| L0_GRb.lean | yes | 4s | 0 | 0 | ok | L0.GRb (MANIFEST.json) |
| L0_GRc.lean | yes | 5s | 0 | 0 | ok | L0.GRc (MANIFEST.json) |
| L0_GRd.lean | yes | 4s | 0 | 0 | ok | L0.GRd (MANIFEST.json) |
| L0_GRe.lean | yes | 5s | 0 | 0 | ok | L0.GRe (MANIFEST.json) |
| L0_GRf.lean | yes | 5s | 0 | 0 | ok | L0.GRf (MANIFEST.json) |
| L0_GRg.lean | yes | 5s | 0 | 0 | ok | L0.GRg (MANIFEST.json) |
| L1_baseWeight_R3.lean | yes | 5s | 3 | 1 | ok | L1.baseWeight (MANIFEST_R3.json) |
| L1_gaussVal.lean | yes | 4s | 0 | 0 | ok | L1.gaussVal (MANIFEST.json) |
| L2_P6ii_R3.lean | yes | 5s | 0 | 0 | ok* (line-wrapped) | L2.P6ii (MANIFEST_R3.json) |
| L2_anchorCong.lean | yes | 5s | 0 | 0 | ok | L2.anchorCong (MANIFEST.json) |
| L2_iaugRecenter.lean | yes | 5s | 0 | 0 | ok | L2.iaugRecenter (MANIFEST.json) |
| L2_iaugRoot.lean | yes | 4s | 0 | 0 | ok | L2.iaugRoot (MANIFEST.json) |
| L2_iaugStep.lean | yes | 5s | 2 | 1 | ok | L2.iaugStep (MANIFEST.json) |
| L2_keyResidualPow.lean | yes | 4s | 0 | 0 | ok | L2.keyResidualPow (MANIFEST.json) |
| L2_psiNotDvd_R3.lean | yes | 5s | 0 | 0 | ok | L2.psiNotDvd (MANIFEST_R3.json) |
| L2_strideRule.lean | yes | 5s | 0 | 0 | ok | L2.strideRule (MANIFEST.json) |
| L2_widthBound.lean | yes | 6s | 0 | 0 | ok | L2.widthBound (MANIFEST.json) |
| L3_DIV.lean | yes | 5s | 0 | 0 | ok | L3.DIV (MANIFEST.json) |
| L3_K1.lean | yes | 6s | 2 | 0 | ok | L3.K1 (MANIFEST.json) |
| L3_digPrime_nonzero.lean | yes | 5s | 0 | 0 | ok | L3.digPrime_nonzero (MANIFEST.json) |
| L3_liftExists.lean | yes | 4s | 0 | 0 | ok | L3.liftExists (MANIFEST.json) |
| L3_liftMonic.lean | yes | 5s | 0 | 0 | ok* (line-wrapped) | L3.liftMonic (MANIFEST.json) |
| L3_liftResidual.lean | yes | 7s | 0 | 0 | ok | L3.liftResidual (MANIFEST.json) |
| L3_liftWeight.lean | yes | 5s | 0 | 0 | ok | L3.liftWeight (MANIFEST.json) |
| L4_TRANSi_R3.lean | yes | 6s | 0 | 0 | ok | L4.TRANSi (MANIFEST_R3.json) |
| L4_TRANSii.lean | yes | 5s | 0 | 0 | ok | L4.TRANSii (MANIFEST.json) |
| L4_TRANSiii_R3.lean | yes | 12s | 0 | 0 | ok | L4.TRANSiii (MANIFEST_R3.json) |
| L4_TRANSiv.lean | yes | 5s | 0 | 0 | ok | L4.TRANSiv (MANIFEST.json) |
| L4_TRANSv_R3.lean | yes | 4s | 0 | 0 | ok | L4.TRANSv (MANIFEST_R3.json) |
| L4_TRANSviii_b_R3.lean | yes | 5s | 2 | 1 | ok | L4.TRANSviii_b (MANIFEST_R3.json) |
| L5_landBox.lean | yes | 6s | 0 | 0 | ok | L5.landBox (MANIFEST.json) |
| L5_landTransport_R3.lean | yes | 5s | 3 | 1 | ok | L5.landTransport (MANIFEST_R3.json) |
| L5_landVertex.lean | yes | 7s | 1 | 0 | ok | L5.landVertex (MANIFEST.json) |
| L5_landVertexDigit.lean | yes | 5s | 4 | 1 | ok | L5.landVertexDigit (MANIFEST.json) |
| L5_realCofin_R3.lean | yes | 5s | 0 | 0 | ok | L5.realCofin (MANIFEST_R3.json) |
| L5_realConclusion.lean | yes | 4s | 0 | 0 | ok | L5.realConclusion (MANIFEST.json) |
| L5_realDomination_R3.lean | yes | 5s | 0 | 0 | ok | L5.realDomination (MANIFEST_R3.json) |
| L5_realRecursion_R3.lean | yes | 6s | 0 | 0 | ok | L5.realRecursion (MANIFEST_R3.json) |
| L6_ledgerCount.lean | yes | 5s | 0 | 0 | ok | L6.ledgerCount (MANIFEST.json) |
| L6_moveAffineBij.lean | yes | 5s | 0 | 0 | ok | L6.moveAffineBij (MANIFEST.json) |
| L6_moveReduceCommute_R3.lean | yes | 4s | 4 | 1 | ok | L6.moveReduceCommute (MANIFEST_R3.json) |

## Summary

- **45/45 files compile** (`lake env lean`, exit 0, zero errors; only linter/deprecation
  warnings in 10 files). Longest: L4_TRANSiii_R3 at 12s; all others 4-7s.
- **6 files carry exactly one real `sorry` each** (compiler `declaration uses sorry`):
  - safe-32 fan-out (MANIFEST.json): `L2_iaugStep.lean` (reducible case, flagged in-file
    as manifest-level), `L5_landVertexDigit.lean` (private core pending the open-dep
    content; its "deps still open" doc comment is now STALE — L3_K1 and L5_landVertex
    are on disk and sorry-free).
  - R3 (MANIFEST_R3.json): `L1_baseWeight_R3.lean`, `L4_TRANSviii_b_R3.lean`,
    `L5_landTransport_R3.lean` (header says REFUTED AS STATED; honest sorry),
    `L6_moveReduceCommute_R3.lean` (see below).
  All other grep hits are doc comments (DefsT, L3_K1, L5_landVertex are genuinely
  sorry-free).
- **Fence: 0 semantic breaks.** 41/44 manifest statements found byte-identical at the
  declaration site. 3 are token-identical but line-wrapped (whitespace-only, shown
  below): `L0_FactA_exists.lean`, `L3_liftMonic.lean`, `L2_P6ii_R3.lean`. `DefsT.lean`
  has no manifest statement entry (defs-only file, fence n/a).
- **L6_moveReduceCommute_R3.lean fences the manifest statement verbatim but also
  contains `L6_moveReduceCommute_statement_false`, a machine-checked disproof of the
  statement's universal closure** (at p=2, Phat=X, f=1, N=1, M=0 the target ZMod(2^0)
  is trivial and clause 1 demands bottom < bottom). Its single `sorry` sits exactly on the
  M=0 branch and is unfixable as stated; the file provides the fully proven
  `L6_moveReduceCommute_of_one_le` (adds `1 ≤ M`) as the candidate replacement pending
  manifest sign-off.

## The three line-wrapped fences (whitespace-only diffs)

Each is the manifest statement with newline+indent inserted (token stream unchanged;
elaborates to the same statement):

1. `L0_FactA_exists.lean` — wrapped after `(hΦ : Φ.Monic)` and after the colon.
2. `L3_liftMonic.lean` — wrapped after `(σ : Stage p F)`, `(Φhat : Polynomial ℤ_[p])`,
   and the colon.
3. `L2_P6ii_R3.lean` — wrapped after the colon.

## Run details

- Date: 2026-07-26. Sequential `lake env lean LeanUrat/Moves/<file>`, per-file timeout
  900s (none hit). Pre-step: `lake build` of the 16 unit modules imported by other
  units (exit 0, "Build completed successfully (8575 jobs)") so `lake env lean` could
  resolve inter-unit imports; the compile column is still the per-file `lake env lean`
  result.
- The `sorries (grep)` column is the literally requested `grep -c sorry` (line count,
  includes comments); `sorry warns` is the ground-truth compiler count.
- Files present vs MANIFEST.json: exactly the 32 cleared safe-32 units exist as
  round-2 files; the other 29 MANIFEST.json units exist only as `_R3` repairs (12 of
  the 29 R3 units are on disk so far), per the MANIFEST_R3.json concurrency note.
