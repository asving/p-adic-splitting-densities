# BATCH_CONFIRM_CODEX — the 2026-07-28 definition-change round

*(Codex confirmation pass over the batch of Lean definition/statement changes made
under Asvin's definition-change authority, base marker `db323cc`. Mechanical runner
job: assemble the diff + both blueprints' §9 FRONTIER sections + the note excerpts
they cite, hand to Codex as an adversarial confirmer, record the verdict. Codex does
NOT fix anything and does NOT re-derive proofs — it only checks that each changed
statement matches its drafted justification and does not silently strengthen/weaken
relative to the cited MOVES displays.)*

## Scope of this pass

- **Diff basis:** `git diff db323cc -- lean/LeanUrat/HC1/ lean/LeanUrat/HC2/`
  (38 tracked files changed, 1744 insertions / 590 deletions) **plus** an addendum
  of the 8 brand-new untracked HC1 files that `git diff` against a commit does not
  surface (`DefsChild.lean`, `S11a_coreTransport.lean`, `S9a_stageLiteral.lean`,
  `S9b_childWeightSet.lean`, `S9c_coreAssembly.lean`, `S9d_pinVerify.lean`,
  `S9r_childR.lean`, `S9w_residualLaws.lean`) — these are the HC1 §9.5 "S9
  decomposition" units and are squarely in scope of the same batch.
- **Justifications:** the full §9 FRONTIER sections of both blueprints —
  `lean/notes/HC1_LEAN_BLUEPRINT_2026-07-28.md` §9 (lines 1163–1613, incl. the
  §9.8 sign-off queue table and the §9.9 EXECUTION RECORD) and
  `lean/notes/HC2_LEAN_BLUEPRINT_2026-07-28.md` §9–§10 (lines 1318–1642, incl. the
  §10 "NOTE ROUND — EXECUTED" record).
- **Note excerpts:** every `MOVES <a>–<b>` line range either §9 section cites by
  number, pulled verbatim (± 2 lines context) from `lean/notes/MOVES_2026-07-24.md`:
  3743–3745, 3648–3651, 2148–2165, 2395–2418, 2464–2465, 2672–2718, 2583–2671,
  3984–3988.
- **Items checked:** HC1 sign-off queue F-1..F-6 + the S9 decomposition (one item);
  HC2 note-round N-1..N-6 + K2, K3, D5-fence. 16 items total.
- Assembled prompt: `/tmp/leanaudit_batch/prompt.txt` (~340 KB, 5351 lines). Run:
  `codex exec --skip-git-repo-check --sandbox danger-full-access` (model
  `gpt-5.6-sol`), detached via `nohup`/`disown`, polled to completion (~single pass,
  no retry needed). Full transcript: `/tmp/leanaudit_batch/verdict.txt`.

## Verdict

**12 CONFIRM, 4 REJECT** — rejected: **N-1, N-4, K3, S9 decomposition**.

| id | verdict | reason |
|---|---|---|
| F-1 | CONFIRM | — |
| F-2 | CONFIRM | — |
| F-3 | CONFIRM | — |
| F-4 | CONFIRM | — |
| F-5 | CONFIRM | — |
| F-6 | CONFIRM | — |
| N-1 | **REJECT** | §9's F-1 draft requires the compiled negation witness for the retired `hcoh`-keyed theorem to land beside the re-keyed `U1`/`keys_exist_of_run` unit ("the assigned prover lands the compiled negation witness beside the re-keyed unit ... so the refutation is durable"); HC2 §10's own execution record for N-1 admits it is only "queued" as future fleet duty ("hcoh-keyed form retired; negation-witness fleet duty queued") — the draft's requirement was not executed in this batch. |
| N-2 | CONFIRM | — |
| N-3 | CONFIRM | — |
| N-4 | **REJECT** | §9's F-3 draft makes the U31 non-vacuity gate re-run **mandatory** ("NON-VACUITY GATE RE-RUN MANDATORY: U31's concrete inert-2 run must be RE-PROVED with clause (vi) in place"); HC2 §10's execution record for N-4 instead defers it ("U31 gate re-run queued-fleet (gate temporarily sorryAx-conditional — recorded)") — the mandated re-proof did not happen in this batch. |
| N-5 | CONFIRM | — |
| N-6 | CONFIRM | — |
| K2 | CONFIRM | — |
| K3 | **REJECT** | `presentNorm_polOM` is left resting on `OmUniqHyp`, which the batch's own execution record calls "conditionally refuted" ("caveat recorded: itself conditionally refuted — wave-4 decides the final uniqueness form"); the guarded `U18` result the note actually pins is being carried by a hypothesis flagged as possibly false, risking vacuity/narrowing beyond what the note's setting argues. |
| D5-fence | CONFIRM | — |
| S9 decomposition | **REJECT** | §9.5 bills `S9w` as "the one genuinely new algebra block" (HARD) delivering `hR0/hRne/hRadd/hRlt/hRmul` + `w_strict/w_jump/R_neg` "via D7's cmul law + `L3_DIV` — the carry-exact product." In the actual files, those laws are instead bundled as **fields of the `ChildResData` spec** in `DefsChild.lean`; `S9r_childR`'s `Nonempty ChildResData` is the real (still-`sorry`) hard construction, and `S9w_residualLaws` merely projects the fields out of the chosen witness (one-line `rw [hcR]; exact hne.some.hR0` etc. for all of hR0/hRne/hRadd/hRlt/hRmul/hRneg) — verified directly against the file text. The "genuinely new algebra" the draft assigned to S9w never lands there; it is relocated into S9r's open sorry, with S9w reduced to cosmetic projection. (Note: HC1 §9.9's own execution record partially discloses this — "S9w_residualLaws = ... nine projections PROVED through the choice" — so this is a scoping/billing mismatch against the §9.5 *draft*, not an undisclosed change against the *execution record*.) |

## Runner's spot-check of the four rejections

Independently re-checked against the assembled materials (not a re-run of Codex,
just confirming the cited text exists as quoted):
- **N-1**: HC2 blueprint §9 F-1 text and §10 N-1 entry both confirm the quoted
  language verbatim — the mismatch is real (draft says "lands beside"; execution
  record says "queued").
- **N-4**: HC2 blueprint §9 F-3 "(c) NON-VACUITY GATE RE-RUN MANDATORY" and §10 N-4
  "gate temporarily sorryAx-conditional" both confirmed verbatim — real mismatch.
- **K3**: HC2 §10 K3 entry's "conditionally refuted" language confirmed verbatim.
  This caveat is *disclosed* by the applier (not hidden), so it is better read as a
  flagged open risk the batch is knowingly carrying, rather than a silent violation
  of the confirmation charge — worth tracking but softer than N-1/N-4.
- **S9 decomposition**: confirmed by reading `DefsChild.lean` / `S9r_childR.lean` /
  `S9w_residualLaws.lean` directly — `ChildResData` does carry `hR0/hRne/hRmul/
  hRadd/hRlt/hRneg` as structure fields, and `S9w_residualLaws`'s proofs of those
  are one-line projections (`hne.some.hR0`, etc.) from `S9r`'s `Nonempty
  ChildResData` witness. The underlying fact Codex cites is accurate; whether it
  counts as a batch defect vs. a legitimate spec-then-witness refactor (S9's
  decomposition explicitly carried no separate sign-off entry per §9.8) is a
  judgment call for the human adjudicator.

## Disposition

Two rejections (N-1, N-4) are **hard mismatches**: the §9 draft imposed an explicit
requirement (durable negation witness; mandatory gate re-run) that the execution
record itself admits was deferred rather than executed — these should go back to
the fleet queue as still-open obligations, not "done." The other two (K3, S9
decomposition) are **disclosed risk items** already visible in the batch's own
execution records — real, worth tracking, but not silent violations of the
confirmation charge in the same sense.

No item was found where the Lean statement text contradicts or silently weakens
the quoted MOVES note excerpts themselves (F-1 through F-6, N-2/N-3/N-5/N-6, K2,
D5-fence all confirmed clean on that axis).

Artifacts retained: `/tmp/leanaudit_batch/{prompt.txt,verdict.txt,full_diff.txt,
diffstat_real.txt,hc1_sec9.txt,hc2_sec9.txt,note_excerpts.txt,
new_files_addendum.txt,charge.txt}` (scratch; not committed).
