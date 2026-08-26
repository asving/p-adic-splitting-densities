# Unit MRAMX (FABLE, math-first) — completion-free ramified level-1 norm exactness

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. You are a MATH unit:
rigorous informal mathematics fit to the landed corpus, NOT Lean-first (optional probe
allowed). Rigor paramount; unproven steps become named OPEN lemmas.

## The problem (BLOCKED mechanism 2 of docs/in-progress/BLOCKERS_PLAN_2026-08-26.md)

General C.27's second mechanism: **ramified level-1 exactness at `AdjoinRoot F.key`,
completion-free, including initial-determinant noncancellation** (the B53b analogue one
level up; the plan prices it at 285–485 Lean lines). The companion mechanism (the
norm↔resultant quotient symmetry) is ALREADY probe-proved and being landed by a concurrent
transcription unit (BW1) — consume its statements as named interfaces
(leanfinal/scratch/DEC4_check.lean:42-131), do not re-prove them. The honest contract from
the plan: ramified exactness SUPPLIES scalar principal-ideal membership; quotient symmetry
TRANSFERS it (the bare norm-nonzero implication was refuted — do not resurrect it).

## Read (in order)

1. docs/in-progress/BLOCKERS_PLAN_2026-08-26.md — the C.27 section IN FULL +
   runs/wave-b/verdict_DEC4R.md + runs/wave-b/verdict_AC15C27.md (the two-mechanism
   diagnosis; the ell=1 rider chain that already closed).
2. leanfinal/Uniformity/ChapB/B53a.lean, B53b.lean, B53c.lean — the unramified/level-0
   pattern you are generalizing (B53c's step-2 weighted-determinant computation is the
   model; the plan's "initial-determinant noncancellation" names its ramified analogue).
3. leanfinal/Uniformity/ChapC/C27x.lean:77-82 — the landed diagnosis of what arbitrary-C
   C.27 additionally needs (factor-label heredity, order-2 no-cancellation) — OUT OF SCOPE
   for you except to fence: your exactness statement must not silently assume them.
4. leanfinal/scratch/DEC4_check.lean (the probes + their honest scoping).

## Method

State the exactness theorem precisely FIRST (which module, which filtration, what "exact"
means at level 1 under ramification, the noncancellation lemma as its own statement). Then
the proof, completion-free (the corpus discipline: no passage to completions — check how
B53b avoids it and generalize that route). Examples-first where the determinant computation
is unclear: a small ramified instance (e.g. Eisenstein key over ℤ₂) computed exactly in a
short cert script (verification/ramx_cert.py — NEW file) before the general argument.

## Deliverables (write INCREMENTALLY to disk)

1. docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md — the theorem + rigorous proof (or
   partials + named OPEN gaps) + a formalization-trivial node decomposition wired to the
   plan's C.27 rows.
2. Optional: verification/ramx_cert.py + log; optional leanfinal/scratch/MRAMX_probe.lean.
3. runs/wave-b/verdict_MRAMX.md (≤2 pages).

No git commits. No edits outside your deliverables. Final message ≤25 lines; detail on disk.
