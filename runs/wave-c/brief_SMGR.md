# UNIT SMGR — Smith tails: GR-7b-0R first (remainder envelope/normal form), then I+/II+

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

The chapter-H research step H.116b4's restricted-Smith core is documented in
docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md (post-MSFIX/MSM2 state; codex-verified
ACCEPT-WITH-GAPS, runs/wave-b/verdict_* records). The equal-slope case is PROVED. The
corrected opens, recorded at §7 and the node table (~line 507 onward):

- **OPEN GR-7b-0R (remainder envelope/normal form)** — starting from U2R, construct the
  genre envelope and normal form for `πF_p rem(EQ, P_p)` (Newton polygons of remainders).
  This GATES the other two.
- **OPEN GR-7b-I+ (cofactor assignment combinatorics, r > 0)** — extend GR-7b-I0
  (β_t(V) = C2 partial sums at r = 0, proved via suffix weights + deadline Hall matching)
  to r > 0.
- **OPEN GR-7b-II+ (cofactor witness minors)** — use the U2R/GR-7b-0R normal form to
  produce the witness minors.

## Your charge

1. READ the doc in full, with special care for: U2R's exact statement, the r = 0 proofs
   you are extending (GR-7b-I0's Hall matching), the §7 genre analysis, and the
   ACCEPT-WITH-GAPS verdict's listed gaps (runs/wave-b/ — grep SMITH/VSMITH).
2. ATTACK GR-7b-0R first. Before any general proof: run an example battery (the existing
   instrument is runs/wave-b/h116b4_battery.py — extend it, don't fork it) computing the
   remainder Newton polygons across the doc's genre table; read the normal form OFF the
   table, then prove it. (Examples-first is this repo's standing method: derive the
   proof's case split from observed genres.)
3. With 0R landed (or honestly partial), attempt I+ and II+ in that order; each
   independently valuable.
4. Numerics: every new general claim gets a numeric certificate — extend
   h116b4_battery.py or add `verification/smgr_cert.py` (python3; sympy available in your
   sandbox). State the exact parameters swept and the count of cases checked.

## Deliverables

- Dated `[SMGR 2026-08-28]` section APPENDED to
  docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md: proofs written to the doc's rigor
  standard (every step justified; explicit lemma statements; the doc's own notation).
  Update the §7/node-table OPEN rows in place ONLY by appending status markers
  (`[SMGR: PROVED/PARTIAL/BLOCKED]`) — do not rewrite history.
- `runs/wave-c/verdict_SMGR.md`: per-item status (GR-7b-0R / I+ / II+), each claim
  labeled PROVED / PARTIAL (with the exact remaining gap as an open lemma) /
  BLOCKED-BECAUSE; certificate run summary.

## Rules

No git commits. Rigor is paramount: a pattern verified on the battery is a CONJECTURE
until proved generally — label it so. Honest partials beat papered gaps. The owner's own
paper is never citable; published cites need precise theorem numbers.
