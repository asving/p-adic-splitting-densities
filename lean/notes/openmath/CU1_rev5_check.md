# CU-1 rev 5 — narrow gap-check (hostile, fresh context, 2026-07-31)

**Charge.** Read ONLY `CU1_phaseB_verifybrief_rev5.md` (standalone). The rev-4
gap-check left exactly ONE open item: the F-4 residual — a map/prose
contradiction between §2 scope note (3) (which at rev 4 still read "Lemma R is
consumed ONLY in this remark and in §4's canonicity remark") and map row 6
(which records THREE consumption sites, the third being the §4 split's
terminal bullet). Verify the rev-5 clause closes it; spot-check the three
nearest confirmed sections (§3 base/step; §4 split; CU-1-SURJ/§8) for
breakage. Quote-and-classify; fix nothing. Verdict: GAPS-CLOSED | GAPS-REMAIN.

## 1. The single open item (F-4 residual) — CLOSED

**What rev 5 was owed** (§0-R5 disposition, line 76): "§2 scope note (3): the
parenthetical now lists all THREE sites — the remark itself, §4's canonicity
remark, and the §4 split's terminal bullet (consumption of Lemma R's displayed
NON-claim 'Cons_f constrains no terminal field') — matching row 6's location
column."

**What the text now says** — §2 scope note (3), lines 358–363:

> "(Lemma R is consumed ONLY in this remark, in §4's canonicity remark, and at
> the §4 split's terminal bullet — where its displayed NON-claim 'Cons_f
> constrains no terminal field' warrants the terminal routing (row 6's third
> site, P2 F-4; prose matched to the map at rev 5); it produces nothing — V27
> findings 2a/6b.)"

**The map row it must match** — row 6, line 634:

> "§2 scope note (3) + §4 canonicity remark + §4 split's terminal bullet (the
> displayed NON-claim 'Cons_f constrains no terminal field', cited as the
> warrant for the terminal routing — third site recorded at rev 4, P2 F-4) —
> produces and identifies NOTHING" · status "PROVED (O-2a)".

**Check.** The scope note's "ONLY" now quantifies over exactly the map row's
three-site list: (1) the scope-note remark itself = row 6's "§2 scope note
(3)"; (2) §4's canonicity remark; (3) the §4 split's terminal bullet, with the
identical displayed NON-claim named as the consumed content. The
produces-nothing rider is present in both. The rev-4 contradiction (a global
"ONLY ... two sites" prose claim against a three-site map record) no longer
exists. **CLOSED.**

**Site-reality cross-checks (standalone, within the document):**

- The third site exists as claimed: the split's terminal bullet (lines
  577–579) reads "Terminal machine records (sel = ⊥) correspond to NO GMN
  child — Cons_f constrains no terminal field (Lemma R's displayed
  non-claim); the verdict-carrying terminal seam is CU-2t's unit". This is a
  consumption of the displayed non-claim, exactly what row 6's location
  column records. Consistent.
- Row 31's location column (line 659) carries the cross-record: "§4 split's
  terminal bullet (Cons_f constrains no terminal field — the home
  definition's displayed non-constraint line, shared with row 6's non-claim)".
  Consistent with both row 6 and the scope note; the §0-R5 claim "rows 6 and
  31 already carried the correct record at rev 4; map untouched" is
  internally coherent (both rows attribute the third-site recording to rev 4,
  P2 F-4/F-2).
- No fourth Lemma-R site surfaces anywhere in §§1–5: §3 mentions Lemma R only
  as a non-use assertion (step 3(d): "Lemma R is NOWHERE invoked in this
  match"), and ADEQ's construction display uses "Lemma R's recovery formulas
  USED AS DEFINITIONS" — under the brief's standing (V27 6b-repaired)
  accounting, formulas-as-definitions is not a consumption of the lemma; the
  lemma's result is consumed only at the canonicity remark. The scope note's
  "ONLY" survives a full-document scan.

**One adjacent clause examined and NOT classified as a finding** (recorded for
transparency, since it is the nearest candidate for a repeat of the same
contradiction class): ADEQ's proof ends "Canonicity remark (the ONLY Lemma R
use): the constructed chain is recoverable from (f, Θ) ..." (line 556). Read
globally, "the ONLY Lemma R use" would collide with the three-site record.
But the parenthetical sits INSIDE Corollary CU-1-ADEQ's proof, before its ∎;
the split (with the terminal bullet) is a separate displayed block after the
proof; and the terminal bullet consumes a displayed NON-claim, not the
recovery statement. Under the natural proof-local scoping — "within this
corollary's checks, this remark is the only place the lemma is used" — there
is no contradiction, and the text is byte-stable from rev 2/3/4 (two hostile
passes plus the rev-4 breakage spot-check of §4 accepted it). NO FINDING.

## 2. Spot-check A — §3 base/step (nearest confirmed section 1): NO BREAKAGE

- Rev 5 claims §§1–3 byte-stable except the §2 scope-note clause; §3 contains
  no rev-5-touched text and none of its citations depend on the repaired
  clause.
- Base k = 0 (lines 367–378): consumed inputs as bracketed — (c0) [row 31],
  §1.4 root definitions [row 18, whose location column includes the base-k=0
  site added at rev 4], (P-ROOT) [row 19], (D3) [row 4]. No REALIZED claim at
  the empty history, matching clause (i)'s k = 0 reading. Consistent.
- Base k = 1 item 3's root non-saturation route (record-only; τ-hen excluded
  by a₀ ≥ 2) matches row 18's location column verbatim.
- Step preamble's IH-legality fact ((C4) restricts to prefixes) is row 31's
  declared load-bearing fact, with the home quantifier-shape warrant
  displayed. Step 2's width tie is exactly the §8-item-2 chain: OL-2(b)
  [row 2] + (FR≡) [row 21] + WGEO(c) [row 13], with WGEO's hypothesis
  supplied by the IH's REALIZED, as row 13/the text claim. Step 3(a) is
  record-only (no Theorem 2(B) — row 5 confirms "NOT consumed in the step").
- N-freeness holds on inspection: no sentence of the base or step consumes a
  working level, box, or decode; D-14/REAL≡/f_N/(N\*-MAJ) appear only in
  CU-1-LVL (rows 15, 16, 22 say "CU-1-LVL only" — matches the text).

## 3. Spot-check B — §4 split (nearest confirmed section 2): NO BREAKAGE

- Four bullets: μ ≥ 2 (ADEQ), μ = 1 (routed to O5triple B/D(b) at displayed
  conditionality), sel = ⊥ (terminal — the row-6/31 non-claim site, now
  matched by the §2 prose), a₀ = 1 (hen-leaf routing, rev-4 F-5). The μ ≥ 2 /
  μ = 1 split over children of non-complete types is exhaustive (μ ≥ 1
  always) and disjoint, as displayed; terminals are excluded from the child
  domain by the non-claim; the a₀ = 1 case is displayed as OUTSIDE the
  split's domain and routed to the same O5triple target. No route consumed
  as an input; routing-only status matches row 23 ("no clause of any proof
  here consumes it").
- Minor note, NO FINDING (gloss class, byte-stable from rev 4 and outside
  rev 5's edit set): the split's closing summary sentence "every
  irreducible-factor slot of f — depth-0 hen leaves included — is covered by
  exactly one of CU-1-ADEQ (interior) or O5triple's Theorems B/D(b)" (lines
  597–600) uses "irreducible-factor slot" loosely — the precise displayed
  claims immediately above (children-domain exhaustive/disjoint + hen-leaf
  routing) quantify over children and hen leaves, not over a defined "slot"
  domain, and interior μ ≥ 2 children are not single-factor slots. The
  precise claims carry the content; the summary is gloss. Recorded, not
  classified.

## 4. Spot-check C — CU-1-SURJ / §8 (nearest confirmed section 3): NO BREAKAGE

- SURJ's dependency accounting (lines 611–620): construction/realization =
  ∀-instances of CU-1 + ADEQ; walk clause = ∀-instance of CU-1-LVL with the
  bundle "rows 7–11, 15–18, 22, 30". §8 item 9 (line 833) lists the identical
  row set. Rows 7–11, 15–18, 22, 30 all exist in the §5 map and their
  location columns name SURJ/LVL where the sentence claims (row 30 explicitly
  carries "SURJ's walk clause (inside LVL's bundle)"; row 17 carries "inside
  D-14"). Consistent.
- Non-claims displayed (no leaf statement, no box beyond f_N, no tree
  object) match §6/R-5 and the §5 exhaustiveness paragraph.

## 5. Consistency of the rev-5 bookkeeping itself

- §0-R5 (line 76) records the one finding, the one repair site, and churn
  class "location fix (one clause); map untouched" — matching what the text
  actually shows (the map rows are dated to rev 4 in their own annotations;
  the only rev-5-marked text in §§1–5 is the scope-note clause's "prose
  matched to the map at rev 5").
- The closing lineage block (lines 844–859) claims "rev 5, like revs 3/4,
  adds no input and no mechanism — the one clause re-displays in prose a
  consumption site the map already carried": true on inspection; no new gate
  owed under the brief's own falsifier-accounting rule (§7.4), and VERIFIED
  is correctly NOT claimed (status stays ZERO-CRITICAL-PASS-2 pending
  acceptance).

## Findings

- CRITICAL ERRORS: none.
- JUSTIFICATION GAPS: none. (Two examined candidates — ADEQ's proof-local
  "the ONLY Lemma R use" and the split's "irreducible-factor slot" summary
  gloss — recorded above as NO-FINDING notes: both byte-stable pre-rev-5
  text outside this check's owed item, both coherent under their natural
  local readings, neither a map/prose contradiction.)

## VERDICT: GAPS-CLOSED

The single rev-4 residual (F-4: the Lemma-R scope-note/map contradiction) is
repaired exactly as §0-R5 states — §2 scope note (3) now lists the same three
sites, with the same non-claim content, as map row 6 — and the three nearest
confirmed sections show no breakage from the repair.
