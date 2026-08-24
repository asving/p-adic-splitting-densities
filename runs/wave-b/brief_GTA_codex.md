# Unit GTA (codex relaunch) — GENTOW2 nodes C.99, C.100, C.101

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign (the Fable
original died silently to API errors with no disk output — you own the node now). Repo
root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(mathlib v4.31.0, built). Verify per-file with `lake env lean <file>` from inside
leanfinal/; module builds like `lake build Uniformity.ChapC.C130pk` are fine; NEVER bare
`lake build`.

## Read first
1. docs/PROJECT_STATE.md.
2. The proof source: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md — the sections proving
   B″/B′/B (C.99/C.100/C.101), with the [Q1]–[Q10] loci. Numbering caution:
   docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md §2 maps [Q] labels → published
   loci → class fields; docs/in-progress/FGMN_ADJUDICATION_2026-08-24.md §2 fixes the
   index/grade dictionary.
3. The SIGNED statements: leanspec/Leanspec/ChapC.lean — `gentow2_Bpp` (C.99, ~L2447),
   `gentow2_Bp` + `gentow2_Bp_unit_iff` (C.100, ~L2474 — RE-SIGNED 2026-08-24 per
   A-C.11/Q6 to `(hdeg : g.natDegree < T.D₂)`, old `hfree` DELETED; use the re-signed form
   verbatim), `gentow2_B` (C.101, ~L2496+). READ-ONLY.
4. The landed class twin your theorems are typed against:
   leanfinal/Uniformity/ChapC/C130pk.lean (`FGMNCalculus` + `chainNorm` + `thetaRatio`) +
   runs/wave-b/verdict_CC16.md. Sibling verdicts runs/wave-b/verdict_GTB.md and
   verdict_GTC.md record blocks their units hit (C.103's missing antecedent, OPEN-DICT
   gaps) — read them so you recognize the same genre quickly if C.99/C.100/C.101 hit one.

## Your nodes
Land leanfinal theorem twins of the three signed statements (byte-identical modulo
axiom→theorem, namespace, and CC-16's sanctioned universe substitution), proved from the
class fields per the proof doc, conditional on the signed `[I : FGMNCalculus ...]` binder.
NOTE GTB's finding genre: if a signed statement omits an antecedent its source proof uses,
that node is BLOCKED with the quoted source line — never bridge the gap silently.

## Deliverable
ONE new file leanfinal/Uniformity/ChapC/C99gt.lean (house style of C64.lean; docstring
"Chapter C, NODES C.99–C.101 (GENTOW2 B″/B′/B)"). `#print axioms` for every declaration —
Lean-core expected (the class hypothesis carries conditionality; no cite).

## Rules
NO sorry/new axioms/unsafe/statement weakening. `rg` every name. Do NOT touch roll-ups,
leanspec/, or other units' files (in flight: C131ae.lean, C78adj.lean, C130vw.lean [CC-12],
and unit AE7 editing leanspec ChapE). Do NOT git commit. Write runs/wave-b/verdict_GTA.md
(per-node LANDED/BLOCKED, declarations, verification command).
