# Verdict — unit RQ: OWNER REVIEW QUEUE compiled

Date: 2026-08-26. Charge: compile the consolidated owner review queue scattered across
~30 unit verdicts into a single document, organized by priority for a human with
limited time. Read-only sweep; two deliverables only, no commit.

## Deliverables

* `docs/REVIEW_QUEUE_2026-08-26.md` — the queue, three tiers (cite transcriptions /
  amendments to signed statements / new general statements), plus a carried-forward
  list of PACKAGING_ROUTE's open review-list rows.
* This file.

## Coverage stats

| source | swept | found |
|---|---|---|
| `docs/CITE_REVIEW_LIST.md` | full read (20 lines, 2 base rows + 1 dated addendum row) | 3 cite items (Tier 1, rows 1–3) |
| `runs/wave-b/verdict_*.md` | **106 of 106** (105 present at sweep start; `verdict_PK12.md` landed mid-sweep on 2026-08-26 and was folded in — see below). `runs/wave-a/` checked too: only `brief_E2.md`/`brief_F2.md` exist, no `verdict_*.md` (pre-dates the verdict convention; not swept as verdicts) | 33 files matched `grep -il -E "review\|flagged\|owner\|human"`, each read in full context (`-B2 -A8` around every hit, or the whole file where short). A second pass grepped `trust.boundary`, `sign-off`, `secondary.check`, `owner.gate`, `adjudicat` — 11 more file-hits, all either already covered by the first pass's content or genuinely nothing-new (pure BLOCKED-status reports: `C130A`, `C130B`, `GTA`, `GTC`, `RB1`, `RB3`, `N6`, `UASM`, `CCUR`, `XSC`, `DEC1` — checked individually, only DEC1's C.63 fork and stop-the-line finding were review-worthy and are captured) |
| Amendment tags `[A-C.10..16]`, `[A-E.7]`, `[A-I.2]`, `[SG-0]`, `[PK-*]` | `rg` over `leanspec/` + `leanfinal/Uniformity/` for each tag family, plus the three standing adjudication docs they point to (`FGMN_ADJUDICATION_2026-08-24.md`, `GENTOW2_ADJUDICATION_2026-08-24.md`, `COR412_ADJUDICATION_2026-08-25.md`) | all 7 named A-C amendments (.10–.16) + A-E.7 + A-I.2 + SG-0 + PK-1..7 confirmed and detailed — 11 amendment rows in Tier 2, spanning ~25 leanfinal/leanspec files |
| `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` | full read; the review-list rows are §6 (not §5 as the charge said — §5 is the node plan; §6, immediately after, is "Review-list rows (flagged, not fixed here)") | 4 rows, all carried into the queue verbatim-summarized |

## Judgment calls made

1. **`verdict_PK12.md` folded in.** It appeared in `runs/wave-b/` partway through this
   sweep (dated 2026-08-26, i.e. today) and fully enacts PK-1/PK-2 of the packaging
   route (folding in PK-3..6 per its own scope note), landing the first UNCONDITIONAL
   `Nonempty (FGMNCalculus …)` instance — a material update to both the Tier 2 SG-0/PK
   row and two Tier 3 rows (SG01's conditional discharge, U15's scratch proposal). Both
   were rewritten in place rather than left stale; the superseded content is kept
   visible (marked "superseded by PK12") rather than deleted, since SG01's emptiness
   theorems and U15's scratch shapes are still named review targets in their own right.
2. **`docs/AXIOM_FAITHFULNESS.md` not re-swept.** It is the repo's standing
   trusted-axiom audit (per this repo's CLAUDE.md) and carries four older entries still
   tagged "DRAFT — PENDING ASVIN REVIEW" (dated 2026-07-30/31), but it is not one of the
   four named sources in the charge and predates the current CITE_REVIEW_LIST protocol.
   Flagged as a one-line pointer at the end of Tier 1 rather than fully re-derived, so it
   isn't silently dropped, without expanding scope beyond the charge.
3. **CCUR's 73-row BLOCKED/READY/DESIGN census, XSC's I.10 fire-ban catalog, and GTA's
   three-node BLOCKED table** were read but excluded as queue rows: they are internal
   work-triage / already-standing design gates with nothing new landed that asks for a
   review decision (as opposed to a to-do item for the next proving unit). Where a
   BLOCKED table's content later became a Tier 2 amendment (e.g. GTC/GTB's `theta_dictionary`
   → A-C.12's HOLD row) it is cross-referenced there instead of duplicated.
4. **Tier 3 scope** followed the charge's own examples (NV-2's expansion, survival
   cores, `dev_mul_conv_split`, `s2_key_irreducible`) rather than the literal string
   "flagged for human review" — NV-2/NV-3 don't use that exact phrase but are the
   charge's own worked examples of the genre, so they're included with the same
   per-file grouping as the units that do use the phrase.

## Not independently re-verified

RQ did not re-run any `lake build`, re-check any `#print axioms`, or re-read any cited
PDF page. Every claim in the two deliverables is a located-and-organized restatement of
what the swept verdicts/amendment comments/adjudication docs already assert; the
queue's job is findability, not re-verification.
