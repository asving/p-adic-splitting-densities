# Unit NS7R (codex HIGH) — the NS7Termination leanspec/leanfinal reconciliation re-sign

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Projects:
leanspec/ (signed statements — your amendment target) + leanfinal/ (landed corpus,
READ-ONLY for you except nothing). `lake env lean <file>` from the project dir; NEVER
bare `lake build`.

## The finding you are fixing (CHFD, 2026-08-26)

runs/wave-b/verdict_CHFD.md + docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md (ns7
row): leanspec still signs `NS7Termination` (I.01) with a `True` body, while leanfinal
has already typed the redrafted descent assertion (leanfinal/Uniformity/ChapI/I01.lean:
132-140 wraps it) and declared + consumed the C.94 cite `agnprw_termination`
(leanfinal/Uniformity/ChapC/C94.lean:107-121; the cite is allowlist member 3 in
docs/PROJECT_STATE.md §3). The signed body and the landed body have DRIFTED.

## The charge

Enact the reconciliation amendment (next free A-I number — grep leanspec/Leanspec/
ChapI.lean and docs/REVIEW_QUEUE_2026-08-26.md; A-I.3 is taken): re-sign leanspec I.01
`NS7Termination`'s BODY at the leanfinal-landed redraft (`NS7TerminationStatementR`'s
shape — find it, read docs/AXIOM_FAITHFULNESS.md's agnprw_termination entry and the
A-C.6 redraft record), following A-I.3's amendment style exactly (dated comment,
strikethrough-preserved old text if the convention does that, gate examples updated).
ONLY the I.01 body changes; every other leanspec statement byte-unchanged. Consumer
audit: `CapstoneHypotheses`' ns7 field and the §4 gate examples must re-elaborate; run
`lake env lean Leanspec/ChapI.lean` (exit 0) and `lake build Leanspec.ChapI` if feasible.
Add the amendment row to docs/REVIEW_QUEUE_2026-08-26.md Tier 2 (top), noting the cite
linkage (C.94/agnprw_termination — this row is ALSO a Tier-1-adjacent cite row for the
owner's read).

## Deliverables

leanspec/Leanspec/ChapI.lean (the one-body amendment) + the review-queue row +
runs/wave-b/verdict_NS7R.md (LANDED/BLOCKED, files, AxChk/gate evidence). No commits.
Do NOT touch leanfinal/ (a μ₃ unit is writing ChapC concurrently), roll-ups, or any
other leanspec file.
