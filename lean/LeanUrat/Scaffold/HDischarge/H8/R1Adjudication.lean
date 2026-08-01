/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-! # H8-R1 (documentary) — O-11 §8 charge (vi) adjudication record

**Unit**: H8-R1, `lean/blueprints/HDISCHARGE_H8.md` §2.5 + unit table
("(documentary) | O-11 §8 charge (vi) adjudication | — | Codex run").
**This file contains NO declarations** — it is the durable record of a
documentary adjudication. Nothing here proves, discharges, or retires
anything; per §2.5, "this unit only ever RECORDS an adjudication of
already-on-file content."

## Execution record (2026-08-01)

Fresh-context Codex run per §2.5's execution spec (quote-and-classify;
fix nothing, prove nothing). Codex v0.145.0, model gpt-5.6-sol,
read-only sandbox, session id `019fbe5b-7495-7bb1-abe4-767df9645229`;
raw transcript excerpted below. Pasted inputs (exact spans):

* DOC-0 (definitions preamble — the names (K-CUT-1/2/g)/(BDY) the charge
  uses): `lean/blueprints/HDISCHARGE_H8.md` §1 member map (lines 79–142).
* DOC-A = (a): T-6's own §T-ASSEMBLY text, §T.4 TREE-EXP —
  `lean/notes/MOVES_2026-07-24.md` lines 7425–7612.
* DOC-B = (b): MOVES §S.2 (CUT-WD) block incl. the ROUTING law —
  `lean/notes/MOVES_2026-07-24.md` lines 12057–12099.
* DOC-C = (c): D-14 + CU-3 statements, verbatim —
  `docs/MATH_COMPLETION_TREE_2026-08-01.md` lines 981–988 and 1209–1211.
* DOC-D1/D2 = (d): the (H8) §3.1 row (`docs/ROOT_ASSEMBLY_2026-08-02.md`
  line 1473) + the (‡) consumer form (M04 §5.4 as quoted at blueprint §0).

The two questions were billed separately per the charge.

## Verdicts (Codex, verbatim)

```
VERDICT (vi-a): FAIL
VERDICT (vi-b-1): NO
VERDICT (vi-b-2): NO
```

**(vi-a) FAIL** — "does D-14 + CU-3 demonstrably imply (K-CUT-1/2/g) as
displayed?": D-14 classified CORRESPONDENCE CLAIM / GAP ("states digit
locality for whether a lawful site is read; it contains no displayed
derivation excluding overlapping ownership, unowned reads, or multiple
shallow decompositions. Its OPEN status also precludes treating it as a
demonstrated input."); CU-3 classified CORRESPONDENCE CLAIM ("displays
no derivation from that package to any cut property"); all four probed
exclusions (overlapping ownership / unowned read / two decompositions /
graft completeness) classified GAP. This matches G-2's own analysis —
the expected verdict.

**(vi-b-1) NO (headline), with the per-step split**: given the fenced
entrance-predicate supply (itself classified "CORRESPONDENCE CLAIM,
explicitly fenced — cited not proved", exactly as DOC-B's own fence
displays it), Codex classified (CUT-1) DEMONSTRATED IMPLICATION,
(CUT-2) DEMONSTRATED IMPLICATION, (BDY) DEMONSTRATED IMPLICATION, and
(CUT-3) DEMONSTRATED IMPLICATION "only for the shallow shape". The
headline NO has two named residues: (i) ROUTING classified
CORRESPONDENCE CLAIM ("asserted as a law and as 'excluded by
construction'; no construction-level derivation is displayed"); (ii)
consumer-level decomposition-data uniqueness classified GAP ("DOC-B
defines only Ŝ(T), not the block-derivation extraction maps or
injectivity of the complete cut data ... it demonstrates the
ownership-level portion and (BDY), but not all of (K-CUT-1) at the
consumer's required bijection level"). NOTE vs §2.5's expectation
("expected YES for the combinatorial legs"): the combinatorial legs ARE
individually classified demonstrated — the NO lands exactly on the (1b)
bijection level, i.e. blueprint finding C-1's already-priced H8-B3
CONSTRUCTION layer, plus the ROUTING display. No new mathematical
content was found missing beyond what §1/§2 already price.

**(vi-b-2) NO** — "no on-file display derives graft completeness":
"DOC-B contains only tree-to-cut assignment and ownership reasoning,
not compatible-data-to-tree grafting." The honest residue, as expected;
(K-CUT-g) stays hypothesis-grade (`VTreeCutSeam.graft_complete`,
H8-B2's owner table).

## Disposition (the §2.5 PRE-REGISTERED rule, applied)

"Only outcome (vi-a) = PASS retires the row into [V] debts per the
ROOT's named route." (vi-a) = FAIL ⇒ **NO retirement**. The (H8) =
(K-CUT) row PERSISTS; the O-11 r3 serving map "CUT-WD ← D-14 + CU-3"
may NOT be re-pointed as a demonstrated implication; the §6 RE-SCOPE
display governs the ROOT sync — executing that ROOT edit is unit H8-R2
(orchestrator), NOT this unit. The expected outcome ("(vi-a) FAIL,
(vi-b) split") is realized, with the (vi-b-1) headline stricter than
predicted at the consumer-bijection level as recorded above.
-/

namespace LeanUrat.Scaffold.HDischarge.H8.R1
-- Documentary unit: intentionally empty. See the module docstring.
end LeanUrat.Scaffold.HDischarge.H8.R1
