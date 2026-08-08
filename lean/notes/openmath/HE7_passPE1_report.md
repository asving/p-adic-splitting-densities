# HE7 passPE1 — hostile verification report (fresh context, zero prior stake)

**VERDICT: PENDING (skeleton — run in progress).**

Target: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` at HEAD (r1 complete at
2970615; seal 1956151, verdict 4c42f9d, r1 commits aafb481/d58680e/2970615).
First hostile pass on this note; prime surface per HE7-BOX-1 = the r1 text +
LEMMAS HE6R1-1/2/3 (never attacked).

Protocol: quote-and-classify, fix nothing. Classes: CRITICAL / GAP / MINOR.

## Findings

(pending)

## Clean charges

(pending)

## Machine leg (integrity)

- Runner md5 `he7_checks.py`: worktree = HEAD = seal 1956151 = r1 2970615 =
  `688adbe88447b570104e379b1fa11cd5` — matches §S11's displayed pin
  `688adbe88447`. Artifacts `he7_checks_output.txt` `b2d095a2556a...`,
  `he7_checks_results.json` `f5bedab2ecda...` — match §S11. Supp runner
  `he7r1_supp.py` md5 `24ece42e453865b4ebb1835007037fe4` at HEAD.
- Isolated re-run: sandbox `/tmp/he7_pe1_sandbox` (committed artifacts
  untouched), full transitive import closure copied at HEAD. IN PROGRESS.

## Fresh route (disclosed)

Chosen route (differs from all prior routes — the sealed 1,587-member battery,
HE6R1's 682-member l=1/d_r=2 battery, r1's 8-member peel leg): a NEW
constructed family at the coverage hole HE7-BOX-5 itself names as unexercised —
**a peel at mu2 = 3**, i.e. degree n = 12 (mu = 6, first machine contact of the
level-2 read at n >= 10), with an independently written reader (slot-min,
polygon, twisted residual implemented fresh from §S1/§S3 text, no import of
he6/he7 code) and PARI `factorpadic` as sigma oracle; includes twist-live
lambda2 odd cells. IN PROGRESS.

## Grade

(pending)
