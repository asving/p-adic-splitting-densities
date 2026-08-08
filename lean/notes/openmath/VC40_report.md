# VC40 — end-to-end verification pass on ROOT REVISION 39 + [RMG-c1] (@24ef527)

**Verifier:** Codex gpt-5.6-sol, reasoning effort HIGH (fresh context,
adversarial charge; session/thread `019fe04b-ff19-79b3-9d01-27a92c41dd5f`;
raw event stream `/tmp/openmath/vc40_out.jsonl`, agent messages reproduced
verbatim below). Charge: `VC40_charge_2026-08-08.txt` (this directory),
834,906 bytes, frozen-history trim per ROOT §45 + checklist rule 7. Launch
07:34 UTC, turn completed 07:41 UTC (≈7 min); usage: 373,885 input tokens
(+22,016 cached), 9,482 output (8,021 reasoning).
**Verdict as filed: NOT-CONFIRMED — 0 critical / 17 gaps.**

## ADJUDICATION (orchestrator, quote-by-quote against the pinned text)

Every quote was re-grepped against the pinned ROOT (24ef527 = HEAD,
whitespace-normalized where the quote wraps). Result: **14 document gaps
CONFIRMED, 1 charge-appendix gap CONFIRMED-AS-CHARGE-DEFECT, 2 findings
REJECTED AS MISQUOTES** (quoted text exists nowhere in the pinned document).

**Class A — the uncorrected arc-count sites (3 gaps, findings 1–3): ALL
CONFIRMED.** [RMG-c1] corrected the 12-pass/zero-critical arc figures at the
§0 standing-paragraph site (the dated in-place bracket at ROOT ~line 1839,
which correctly displays 14 passes / 2 round-1 criticals) — but THREE other
own-voice sites written by the r40 fold carry the superseded figures with NO
correction:
  - §3.2 end-to-end row (line 3517): "the 12-pass arc with zero critical
    findings ever" — CONFIRMED (1 hit).
  - §6 dispatch bracket (line 5056): "the 12-pass arc, zero critical
    findings ever" — CONFIRMED.
  - §44.(ii) Q1 bracket (line 11420): "12 hostile passes with zero critical
    findings ever." — CONFIRMED.
  (The §45.(i) occurrence at line 11988 is INSIDE the faithful [RMG] block
  paste — correct-as-dated per the charge's [RMG-c1] rule, properly NOT
  flagged by the auditor.) These are exactly charge item (iii)'s "no grade
  inflated" — the [RMG-c1] ripple was incomplete.

**Class B — the incorporation-convention (rule-8) class, FOURTH recurrence
(11 gaps, findings 4–5, 8–16): ALL CONFIRMED.** Bare [RMG] or [ILN] tokens
in new r40 text outside the declared full-paste sites (the convention's
dagger rule; the VC37 4-gap / VC38 8-gap / VC39 4-gap lineage):
  - F4 "the [RMG] pastes" (§0 standing paragraph, inside the [RMG-c1]
    bracket itself) — 1 hit ✓
  - F5 "the [RMG] ledger block's" (§6 corpus-law bracket) — 1 hit ✓
  - F8 "extended at r40 with the [RMG] block; dagger [RMG]† elsewhere"
    (§45 opening summary) — 1 hit ✓ (the sentence declares the dagger rule
    while itself bare; the exact VC39-gap-4 pattern)
  - F9 "never a silent rewrite; the pasted [ILN] blocks are token-frozen"
    (§45 opening summary) — 1 hit ✓
  - F10 "recorded in the [RMG] ledger block" (§45.(ii)) — ✓
  - F11 "the pasted [ILN] blocks are token-frozen ledger pastes and are NOT
    edited" (§45.(ii)) — 1 hit ✓
  - F12 "Declared at the §6 r40 bracket with the [RMG] ledger cite"
    (§45.(v)) — 1 hit ✓
  - F13/F14/F15 disposition-table cells r40-2/r40-3/r40-6 ("the [RMG]
    ledger block (applied" / "the [RMG] block's COR-A clause" / "the [RMG]
    block's corpus-law clause") — each 1 hit ✓ (table cells expressly carry
    the dagger under the convention)
  - F16 "(unit ROOT r40; the [RMG] fold)" (§45 bookkeeping) — 1 hit ✓
  A fresh line census finds 14 lines with an un-daggered [RMG] token outside
  ":="-block heads and [RMG-c1] mentions — the r40b cure batch should run
  its own full sweep rather than cure only the filed sites.

**Class C — charge-appendix defect (1 gap, finding 17): CONFIRMED AS A
CHARGE DEFECT, not a document defect.** APPENDIX B.4's PROJECT_STATE slice
was keyed by a substring heuristic ("Q1"+"closed") that matched a false site
(line 1044, "hRes-Q1") instead of the actual Q1-closed bracket (line 1334,
"**[2026-08-04 (campaign 2026-08-08): Q1 IS CLOSED — THEOREM RM-GEN ..."),
so the pasted slice showed unrelated material and item (v)'s consistency
claim was unverifiable from the self-contained input. The VC35-gap-2 /
checklist-rule-3 class ("never trust a grep pattern for wording you didn't
verify") — charged to the charge-builder; cure = pin the correct slice
(PROJECT_STATE@24ef527 lines ~1330-1345) in the VC40b charge.

**REJECTED — findings 6 and 7 (misquotes).** Quoted passages "The pasted
[ILN] block and the queue text below remain byte-unchanged" and "the pasted
[ILN] block stays token-frozen" exist NOWHERE in the pinned document
(verified by whitespace-normalized full-text search), and the four §44.(ii)
r40 brackets contain ZERO [ILN] tokens of any form (grep of all four hunk
ranges: only [RMG]† and PID† appear). The nearest real sentences live in §45
and are already covered by findings 9/11. Both findings are contested and
removed from the cure queue; adjudicated tally: **0 critical / 15 gaps (14
document + 1 charge)**.

**Cures owed (r40b batch + VC40b micro pass, per the VC38/VC39 precedent —
NOT executed by this unit):** (1) three dated arc-count correction brackets
at the §3.2 row / §6 dispatch bracket / §44.(ii) Q1 bracket sites (flawed
text preserved, [RMG-c1] figures displayed); (2) dagger brackets (or
orchestrator-direct dagger errata per the r37b precedent) at the eleven
confirmed convention sites, plus the fold unit's own full bare-token sweep;
(3) the corrected PROJECT_STATE slice pinned into the VC40b charge. The
acceptance citation REMAINS at REVISION 38 + r39b (VC39+VC39b) until VC40b
lands. This adjudication never self-confirms.

## NOTES from the run (not findings)

- The auditor's sandbox launcher was unavailable (known: bubblewrap broken
  for Codex on this host); per standing disclosure (a) it audited entirely
  from the pinned transcripts — the division-of-labor design working as
  intended.
- Zero mathematical findings; zero criticals; the [RMG] 154-token identity,
  the [ILN] byte-identity, the census transcripts, the sorry census, the
  re-anchoring displays, and the roster recount all passed without comment.

---

## THE RAW REPORT (verbatim, all agent messages from the JSONL stream)

### Message 1 (preamble)

I'll audit the pinned revision's operative sites, correction propagation,
census arithmetic, and inherited charge constraints. I'll treat the pasted
frozen-history evidence as authoritative and use local read-only checks only
where the pinned objects are available.

### Message 2 (interim)

The read-only launcher is unavailable, so I'm applying the charge's
execution-environment rule and treating that as a note. The pasted text
itself exposes several operative acceptance-count and incorporation-
convention surfaces; I'm cross-checking those against the correction and
prior convention before fixing the finding count.

### Message 3 (findings)

1. [GAP] Uncorrected arc total in the §3.2 operative row
   QUOTE: "the 12-pass arc with zero critical findings ever"
   DIAGNOSIS: This is ROOT's own voice, not a faithful [RMG] paste, and it omits [RMG-c1]'s correction to 14 passes with two round-1 criticals. It violates charge item (iii).

2. [GAP] Uncorrected arc total in the §6 dispatch bracket
   QUOTE: "the 12-pass arc, zero critical findings ever"
   DIAGNOSIS: This operative assertion repeats both superseded figures without the correction, contrary to [RMG-c1] and charge item (iii).

3. [GAP] Uncorrected arc total in the §44.(ii) Q1 bracket
   QUOTE: "12 hostile passes with zero critical findings ever."
   DIAGNOSIS: The dated bracket speaks in ROOT's own voice outside a faithful paste and does not carry the 14-pass/two-critical correction required by [RMG-c1].

4. [GAP] Bare [RMG] token in the §0 correction prose
   QUOTE: "the [RMG] pastes"
   DIAGNOSIS: This §0 standing paragraph is not one of the three declared [RMG] full-paste sites. The token must read [RMG]† under charge item (ii).

5. [GAP] Bare [RMG] citation in §6
   QUOTE: "the [RMG] ledger block's"
   DIAGNOSIS: The corpus-law bracket cites the accepted result outside a full-paste site without the dagger, violating the incorporation convention.

6. [GAP] Bare [ILN] citation in the §44.(ii) section-head bracket
   QUOTE: "The pasted [ILN] block and the queue text below remain byte-unchanged."
   DIAGNOSIS: Section 44.(ii) is not an [ILN] full-paste site. This new bracket must use [ILN]† under charge item (ii).

7. [GAP] Bare [ILN] citation in the §44.(ii) Q1 bracket
   QUOTE: "the pasted [ILN] block stays token-frozen"
   DIAGNOSIS: This second §44.(ii) reference likewise occurs outside a full paste and lacks the required dagger.

8. [GAP] Bare [RMG] citation in the §45 revision summary
   QUOTE: "extended at r40 with the [RMG] block; dagger [RMG]† elsewhere"
   DIAGNOSIS: The sentence declares the dagger rule while itself using a bare [RMG] token outside the §45.(i) paste site.

9. [GAP] Bare [ILN] citation in the §45 revision summary
   QUOTE: "never a silent rewrite; the pasted [ILN] blocks are token-frozen"
   DIAGNOSIS: This summary is not one of the four [ILN] full-paste sites, so the reference must carry †.

10. [GAP] Bare [RMG] citation in §45.(ii)
    QUOTE: "recorded in the [RMG] ledger block"
    DIAGNOSIS: Section 45.(ii) is not an [RMG] paste site. The ledger-block citation violates charge item (ii).

11. [GAP] Bare [ILN] citation in §45.(ii)
    QUOTE: "the pasted [ILN] blocks are token-frozen ledger pastes and are NOT edited"
    DIAGNOSIS: The COR-A discussion cites [ILN] outside a full-paste site without the required dagger.

12. [GAP] Bare [RMG] citation in §45.(v)
    QUOTE: "Declared at the §6 r40 bracket with the [RMG] ledger cite"
    DIAGNOSIS: The corpus-law record is not a full-paste site and must use [RMG]†.

13. [GAP] Bare [RMG] token in disposition row r40-2
    QUOTE: "the [RMG] ledger block"
    DIAGNOSIS: The incorporation convention explicitly assigns dagger citations to table cells; this cell lacks it.

14. [GAP] Bare [RMG] token in disposition row r40-3
    QUOTE: "the [RMG] block's COR-A clause"
    DIAGNOSIS: This disposition-table citation must read [RMG]† under charge item (ii).

15. [GAP] Bare [RMG] token in disposition row r40-6
    QUOTE: "the [RMG] block's corpus-law clause"
    DIAGNOSIS: This is another table-cell citation outside a full paste without the required dagger.

16. [GAP] Bare [RMG] token in the bookkeeping record
    QUOTE: "The commit closing this revision is its unit of record (unit ROOT r40; the [RMG] fold)."
    DIAGNOSIS: The inherited incorporation-convention sweep covers the new bookkeeping text; this history citation must use [RMG]†.

17. [GAP] PROJECT_STATE consistency claim lacks the promised pinned evidence
    QUOTE: "docs/PROJECT_STATE.md was checked for consistency with its standing 2026-08-04 Q1-closed bracket and NOT edited"
    DIAGNOSIS: Appendix B.4 is labeled as that bracket's neighborhood but reproduces unrelated earlier PROJECT_STATE material and never displays the Q1-closed/[RMG-c1] passage. Charge item (v) therefore cannot be verified from the self-contained input.

NOTES: The local read-only command launcher failed before repository access. Per standing disclosure (a), this execution limitation is not a finding; census, identity, and footprint adjudication used the pinned transcripts.

VC40 FINDINGS: 0 critical, 17 gaps
VERDICT: NOT-CONFIRMED
