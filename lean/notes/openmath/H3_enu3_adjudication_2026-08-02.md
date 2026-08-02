# EN-U3 adjudication — route (a) REFUTED BY FALSIFIER; no attempt warranted (mop-up batch, 2026-08-02)

**Unit:** HDISCHARGE_H3 §3.3/§4 EN-U3 — "(E-N) route (a), prove the redundancy:
*if a level-N box x fibers (working level N) a decided ns-free tree T, then
thr(T) ≤ N*" — phase-B open-math attempt, **blocked-by: G-EN-1 = no-hit**.

**Gate outcome (the adjudicating falsifier, unit EN-U2):** G-EN-1 = **HIT**, on
record at `verification/logs/h3_en_falsifier_2026-08-01.log` (JSON at
`verification/results/h3_en_falsifier_results.json`). Every probed
configuration hit: p ∈ {2,3} × n ∈ {2,3} × N ≤ 5 (N ≤ 4 at p=3,n=3) — 19/19
configs, **1354 recorded counterexample boxes** (decided ns-free trees with
thr(T) > N), min margin −9 (p=2, n=3, N=5 and p=3, n=3, N=4). All four
calibration/validation gates inside the run PASSED (PARI oracle, hand-worked
instances, Eisenstein family, 224-box depth-1 tie), and the absorption audit
found tree-record witnesses for 1354/1354 hits.

**Consequence per the blueprint's own criterion (HDISCHARGE_H3 §3.3, verbatim
genre):** "A G-EN-1 hit forces route (b)'s absorption verification and
PERMANENTLY fences route (a)." The redundancy statement is FALSE as stated at
every probed (p, n) including n = 2 — so EN-U3 is **RETIRED — REFUTED**, not
blocked-pending: no proof attempt is warranted, at ~4 attempts or any number.
The blueprint's own verdict ("route (a) is genuinely open at EVERY n",
falsifier-guided only, never a scheduled dependency of the retirement) is
CONFIRMED in the strong direction; the (E-N) discharge burden sits ENTIRELY
on route (b) (EN-U1 walk → EN-U5 row rewrite, VC discipline — doc-target,
owned by the revision workflows, NOT this batch).

**Typed falsifier target (chartered, not executed here):** per EN-U4's
docstring (`Scaffold/HDischarge/H3/EnCarrier.lean`), a hit lands as a compiled
`¬ ENRedundancyAt …` at the instance. Building the `TreeModel`/`VTree`
transcription of a hit box (e.g. the p=2, n=2, N=1 hit) is a DATA unit of the
route-a-refutation-witness class — chartered as follow-on, owner: whoever
lands the presented-model instance layer; the numeric record above is the
standing evidence meanwhile.

**W-3 flag re-surfaced (route-b relevance):** the absorption audit's second
pass records that the semantic(type)/operational(tree) decided-at-N readings
DIVERGE on concrete boxes (77/420 n = 2 hits census-TYPE-decided at N) —
exactly walk duty W-3's genre (envelope must be DETECTED-at-N-defined or
route (b) fails at that site). Routed to the EN-U1/EN-U5 owner.
