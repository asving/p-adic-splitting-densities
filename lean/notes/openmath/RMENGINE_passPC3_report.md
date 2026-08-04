# RMENGINE pass PC3 report (Codex, round 3 — the first acceptance attempt) — 2026-08-04

Object: lean/notes/openmath/RMENGINE_2026-08-08.md at r2 (423b399).
Charge: /tmp/openmath/RMENGINE_PC3_charge.txt (124,175 chars; appendices: the r2 note, both round-2 reports, [IL3] S4.1 slice).
Raw stream: /tmp/openmath/rmengine_pc3_out.jsonl. Extracted agent messages verbatim below.

---

I’ll audit the committed r2 text read-only, including an independent normalized keyword census and the exact 8835d20→423b399 diff. I’ll treat execution limits as notes and make no fixes.

=====MSG-BREAK=====

1. > “on the T-scope (all reads below the top non-degenerate)”

   **JUSTIFICATION GAP.** This headline gloss is stale: amended T-scope also includes \(d₀=1\) with arbitrary \(e_i\ge1\), including degenerate flat reads. The formal T-scope displays are consistent, so this is a scope-description defect rather than a theorem failure.

2. > “every ‘only/never/nothing/free/self-contained/automatic’ claim of this note, enumerated”

   **JUSTIFICATION GAP.** The table remains literally non-exhaustive. For example, L-LEX says it is “consumed by nothing,” and the DAG repeats “L-LEX … consumed by nothing,” but no C-row covers that dependency claim. Likewise, “then \(\lambda_{l-1}\in\mathbb Z\) automatically” and the automatic on-grid qualifiers are not explicitly represented. Thus the recurring charter defect is not dead.

3. > “The only statement changes are the T-scope/T-class STRENGTHENING … and the L-LEX regrade to remark”

   **JUSTIFICATION GAP.** C28 is too narrow against the recorded r1 changes: the text also changed the \(v=0\) statement to L-VNZ, corrected COR-A’s \(n=1,2\) scope, introduced L-GRID’s empty-case conclusion, and regraded the floor-form pool identification. These are mathematically proper repairs, but the claimed exhaustive statement-diff description is not literally true. The r2 regrade-versus-weakening wording itself is otherwise cured.

4. > “DIGIT-SPLIT … stated and proved there for ALL α, β of degree < d₀ with no primitivity hypothesis”

   **NOTE.** Appendix C confirms this exactly. The corrected citation is faithful; primitivity is used only to ensure the normalized L-child is nonzero. Rows C23–C27 also agree with their body claims and bases.

5. > “every S2–S7 display is byte-identical to 8835d20 except the L-NORM citation parenthetical”

   **NOTE.** Exact repository/diff verification was unavailable because the command launcher failed for lack of `bubblewrap`. The supplied text shows no mathematical r2 alteration, but byte identity could not be independently executed.

RMENGINE-PC3 FINDINGS: 0 critical, 3 gaps
VERDICT: GAPS-ONLY
