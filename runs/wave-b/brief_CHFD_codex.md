# Unit CHFD (codex HIGH) — the CapstoneHypotheses field-list decomposition

You are a decomposer unit in the p-adic-splitting-densities campaign. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean projects: leanfinal/
(landed corpus) and leanspec/ (signed; READ-ONLY for you). Lean 4.31.0 + mathlib,
pre-built; `lake env lean <file>` from the project dir; NEVER bare `lake build`.

## Context

A-I.3 (2026-08-26) typed the I.10a/b sockets and all four capstone-assembly theorems
landed Lean-core (`leanfinal/Uniformity/ChapI/I10_I15_I18.lean`): `UniformityStatement`
now reduces to INHABITING `CapstoneHypotheses n`. The block is OPEN — no longer provably
empty, not yet inhabited. The campaign needs the definitive supply map.

## The charge

Enumerate EVERY field of `CapstoneHypotheses` (read the structure in
leanspec/Leanspec/ChapI.lean AND its landed twin in
leanfinal/Uniformity/ChapI/I10_I15_I18.lean — they must agree; report any drift as a
stop-the-line finding) and for each field produce the supply row:

1. What the field demands, restated precisely (unfold the definitional layers: I.01–I.03,
   I.05–I.07, I.21 defs live in leanfinal/Uniformity/ChapI/I01.lean…I21.lean).
2. What the landed corpus already supplies (search seriously: the S2 socket teeth in
   C130sg.lean; the menu/base-case machinery of chapter G; chapter H's induction;
   chapter D/E gauges; cite candidates in docs/PROJECT_STATE.md §3). file:line evidence.
3. The GAP: exactly what is missing, which chapter/campaign supplies it (the μ₃ campaign
   docs/in-progress/MU3_CAMPAIGN_2026-08-26.md; the blockers plan
   BLOCKERS_PLAN_2026-08-26.md; the H.116b4 map H116B4_MAP_2026-08-26.md; or a NEW
   named campaign), and honest sizing (30–60 min transcription / multi-node / research-open).
4. Special rows: the five I-D12 `True` bodies (NS7Termination = the C.94 AGNPRW Thm 5.6
   cite — its redraft `NS7TerminationStatementR` is machine-safe and ready to declare;
   locate it and specify the declaration node), the `jd0`/`genhnBox2` placeholders, the
   `w1` debt (read A-I.1's ruling in leanspec ChapI), and `a0`/`a1` at n ≥ 3.

Then: the DAG — which fields block which, the minimal path to `CapstoneHypotheses 2`
(the first non-trivial n; the S2 instance's natural home) vs general n, and a
fleet-ready node table for the first wave of suppliers.

KNOWN CONSTRAINT: a concurrent unit (AMND) is amending leanspec ChapC consumer statements
(hprev fence, chainNorm re-index) — read its brief runs/wave-b/brief_AMND_codex.md so
your rows anticipate the amended forms; do not touch any file it owns.

## Deliverables (write INCREMENTALLY)

1. docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md — the field table + DAG + node plan.
2. leanfinal/scratch/CHFD_probe.lean — elaboration probes for any load-bearing claim
   (e.g. that a landed supplier's type matches a field's demand). Zero sorry, zero axiom,
   exit 0.
3. runs/wave-b/verdict_CHFD.md — ≤2 pages.

## Rules

READ-ONLY outside your three deliverables. No leanspec edits (you are not an amendment
unit — if a field looks wrongly signed, record it as a finding, do not fix). No commits.
file:line evidence for every supply claim; never trust a bare name-grep (comment-strip or
`#print axioms`).
