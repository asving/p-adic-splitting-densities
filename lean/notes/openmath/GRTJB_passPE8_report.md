# GRTJB-PE8 — hostile verification pass on the post-r7 J-B tree-junction note (SIXTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD**
(repo HEAD `35d37ba`; the note byte-identical to its r7 blob — verified
`diff` of `4c4ee56:…GRTJB_PROOF_2026-08-08.md` vs the working file = 0 lines),
i.e. r0 (sealed 7f6759d) + r1 (4c97649, 46f9452) + r2 (67bf0c4, 888e293) +
r3 (8acb2d1, 87c553d) + r4 (ae0acdf) + r5 (f9f104e) + r6 (4607824) +
**r7 (4c4ee56, +190/−16, note-only)**.
**Scripts re-run (all four):** `grt_jb_checks.py` · `grt_jb_printwalk.py` ·
`grt_jb_printwalk2.py` · `grt_jb_r1_levelcensus.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion, keep verifying;
honesty defects graded; fences are part of the statement). Pass date
2026-08-06 (wallclock; 2026-08-08 campaign). All seven prior reports
(PE1–PE7, incl. the PE1 outage partial) and the r7 diff read in full before
judgment. This is the EIGHTH hostile reader and the SIXTH acceptance
attempt; a clean pass here would START the 2-clean count.

---

## §0. VERDICT

**0 CRITICAL, 0 JUSTIFICATION GAPS, 1 MINOR.**

    GRTJB-PE8 FINDINGS: 0 critical, 0 gaps, 1 minor / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

The r7 diff's mathematics is EXACT end-to-end: both directions of the m = 1
equivalence re-derive from the note's own displays and were independently
machine-confirmed on a WIDER box than PE7's (340 read data, 0
counterexamples); the disclosed second conjunct was re-read from committed
source at every cited line number and its redundancy re-derived; all twelve
[r7] brackets land where the round block says; the arc-accounting system is
consistent at HEAD (strike census 83 exact, all 16 hashes resolve, all four
authoritative surfaces say seven passes / seven rounds / JB-PE8 next /
counter 0/2). The one finding is a quotation-form defect inside the r7
round block itself: its F-1 bullet attributes to "both [r6, m-1] brackets"
a quoted string that appears byte-for-byte at NEITHER site (a fusion of the
two sites' different wordings) — semantically exact, sources preserved
under strikes in place, but a misquotation on a live record surface in the
round named THE WORDING-HYGIENE ROUND (F-1 below).

---

## §1. MACHINE LEGS (all four instruments, this pass's own re-runs)

Run order checks → printwalk → printwalk2 → levelcensus (the census reads
`grt_jb_checks_results.json`; walker2 reads the walker's JSON).

| leg | exit | stdout vs committed `_output.txt` | headline figures |
|---|---|---|---|
| `grt_jb_checks.py` | 0 | **0-line diff** (elapsed 0.7s reproduced) | 18 families GREEN, TOTAL samples 6700, 0 violations; JB-CREAD scored 104 / boundary 21 / v=0 0 / R=0 0; teeth 4×3 caught; byte census 22-of-25 true + 3 empty (`{}`) |
| `grt_jb_printwalk.py` | 0 | **0-line diff** | PW-ID 38, PW-WALK 84, PW-REASM 84, PW-DIV 84, PW-XFRAME 72, all GREEN; TOTAL 458; LEG-A walks 84 (79 predicted + 5 small=True extras), byte-unequal junctions 12 |
| `grt_jb_printwalk2.py` | 0 | **0-line diff** | GREEN; TOTAL 100 = PW2-XFRAME 45 + PW2-DEGEN 27 + PW2-RECON 28; 4 chain-divergent rows leg-B-not-claimable |
| `grt_jb_r1_levelcensus.py` | 0 | **0-line diff** | roster boundary 13 (m=1 0, m=2 10, m=3 3), roster scored 56, scope-outs 0; cross-check 13 + chamber 8 = 21 = sealed census field |

`git diff -- verification/` **EMPTY** and `git status --short verification/`
empty after all four re-runs (every regenerated JSON byte-identical,
including `elapsed_s`). **md5s at their sealed values, computed fresh:**
`grt_jb_checks.py` `55f4911eaddd8524fd91368b30ed71bd` ·
`grt_jb_printwalk.py` `f53e23e8d1c79f084a1e34eee857e37c` ·
`grt_jb_printwalk2.py` `6c6318f7fc6570a2d454389b38441329` ·
`grt_jb_r1_levelcensus.py` `2bcb44fdbf839d367f0e11033a5d3fd7` — all four
matching the note's citations (L582, L587–589, L2410, L2839). Figures vs
the note spot-checked: §7.1 headline (6,700 / 104 / 21), the [r2, G2-7]
decomposition 104 = 66 + 38 with 66 = 56 + 2 + 8 (census output roster
scored 56 ✓), the walker split 458 = 362 + 96, walker2's 45/27/28, and the
F1 READOUT geography (10 boundary rows at m = 2, 3 at m = 3, 0 at m = 1) —
all EXACT. **Machine legs 4/4, nothing NOT-RUN.**

---

## §2. CHARGE 1 — the r7 diff, line by line

**(a) The equivalence display's two directions — RE-DERIVED BOTH,
independently.** The display (§0M column (b), duplicated in content at §5's
[r7, PE7 F-1] bracket): at m = 1, for every read datum (e₀, h₀, g₀),
{V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁ exactly, 𝒲₁ = {e₀a + h₀j : a ≥ 0, 0 ≤ j ≤ P₀−1}.

* (⊇) — the §5 four-line theorem at m = 1, re-derived from scratch:
  V = e₀a + h₀j ⇒ V ≡ j·h₀ (mod e₀) ⇒ s := (ℓ₀V) mod e₀ = j mod e₀ ≤ j
  (ℓ₀h₀ ≡ 1 mod e₀) ⇒ V − s·h₀ = e₀a + (j − s)h₀ ≥ 0 and ≡ 0 (mod e₀)
  ⇒ u := (V − s·h₀)/e₀ ≥ 0. Exact.
* (⊆) — the j := s decomposition, re-derived: for V ≥ 0, e₀ | (V − s·h₀)
  (from ℓ₀h₀ ≡ 1; the integrality is derivable in-note from the s_m^wt
  notation block's "least x ∈ [0, e_{m−1}) with (V − x·h_{m−1}) ≡ 0"
  display, §5), so V = s·h₀ + u·e₀ with u = u(V); u ≥ 0 gives V ∈ 𝒲₁ via
  a := u, j := s, and j ≤ e₀ − 1 ≤ P₀ − 1 needs exactly g₀ ≥ 1 (P₀ = e₀g₀
  per the note's own abbreviation, L549/L1750; g ≥ 1 the class pin). Exact.
* Decorrelated machine check, DIFFERENT box than PE7's (e₀ ≤ 9, h₀ ≤ 11
  coprime, g₀ ≤ 5, every V ∈ [0, 400)): **340 read data, 0 counterexamples**
  to the equivalence (PE7's box was e ≤ 6 / h ≤ 8 / g ≤ 3 / V < 150, 96
  read data — reproduced as a strict sub-box of mine).
* The bracket's transcription of PE7's figures (96 read data, all coprime
  (e₀,h₀) with e₀ ≤ 6, h₀ ≤ 8, g₀ ≤ 3, every V ∈ [0,150), 0
  counterexamples, `GRTJB_passPE7_report.md` §2 F-1, commit aa9b603)
  checked verbatim against the PE7 report. EXACT, correctly attributed,
  as-of pin present.

**(b) The conjunct re-read vs `grt_jb_checks.py` L283 — VERIFIED FROM
SOURCE, every cited line number exact.** L283 is (byte-for-byte)
`if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):`, nested under L280's
`if q <= L:` with `L = GJA.shared_upto(T, G)` (L260). The redundancy
arithmetic re-derived independently from committed source: `GmnLeg` L211
(`grt_weld_probe.py`) is `self.RANK = len(levels)`; `gmn_from_tower`
L456–459 builds `levels` over `range(T.NR)`, so RANK = T.NR; the harness
(`iterlawn_pe_reimpl.py` L255) sets `self.NR = len(reads); self.n =
self.NR − 1`, so RANK = n+1; the loop (L261) runs `q in range(0,
qcap_of(T,G)+1)` with `qcap_of = min(T.n, shared_upto+1) ≤ n` (L210–213).
Hence q+1 ≤ n+1 = RANK identically on the loop domain — the conjunct is
REDUNDANT, exactly as disclosed. Every `jb_shear_vtx` caller builds G via
`GWP.gmn_from_tower(T)` (L743/780/803/827/886/904), so RANK = T.NR at every
run, including the QO n = 0 shapes (NR = 1, qcap = 0, q+1 = 1 ≤ 1). The
effective (d3) gate is the single conjunct q ≤ shared_upto; `shared_upto`'s
`break` (grt_ja_checks.py L155–163) gives prefix contiguity, so q ≤ L ⟺
`P≤q` — the coverage claims ("the gate IS the fence", "the IND leg covers
the full re-fenced range") stand.

**(c) The four m-3 sites — ALL FOUR VERIFIED IN PLACE, and the site
universe checked independently.** ⟨n3⟩ (L320–327, the full transcription,
with the `q + 1 <= G.RANK` string byte-exact incl. spacing), the §3 machine
bracket (L1701–1704), §7.1's JB-SHEAR row (L2422), the r6 round block's
MACHINE clause (L1123–1126) — each carries the parenthetical + [r7, PE7
m-3, commit aa9b603] + a ⟨n3⟩ pointer. My own sweep of every
assertion-transcription phrase (`tie assertions` / `the code's assertions`
/ `jb_shear_vtx`) finds NO fifth transcription site; the remaining
`q ≤ shared_upto` mentions (row 11 (f), the claims-table JB-VTX row, §1's
r6/F-1 bracket, the S-STATUS records, etc.) are coverage claims warranted
by ⟨n3⟩'s "every coverage claim reading this cell stands unchanged" —
extensionally true since the conjunct is identically true. (Observation,
not scored: the three summary parentheticals write the conjunct `q+1 <=
G.RANK` without the code's inner spaces; each defers to ⟨n3⟩, which is
byte-exact, for the full transcription.)

**(d) m-2 — verified.** JB-BOX-2's [r5, F-3] bracket now reads "…is
~~exactly~~ **[r7, PE7 m-2 — …]** lattice MEMBERSHIP…" (L2305–2309), the
strike surgical (adverb only), the pointer to column (b) correct, the
surrounding operative content (holds by definition at deg f < deg Φ_{q+1},
not established off it) untouched — as PE7 verified and r7 claims. My
whole-note sweep of `membership`/`MEMBERSHIP` (44 live hits) finds no
FOURTH live necessity-overstating site: rows 4/12's cells say "open residue
= MEMBERSHIP" (the claim shape the post-r7 canonical JB-BOX-2 text itself
retains, read through column (b)'s corrected legend); the r5 round block's
"strictly smaller" (L1040) is a dated record explicitly re-annotated by the
r6 m-1 bullet + its [r7, F-1] bracket.

**(e) F-1's two strikes and the replacement relation — verified at both
sites.** Both [r6, m-1] non-equivalence spans struck (§0M column (b),
L203–204; §5 SCOPE, L2035–2036); the replacement (sufficiency always;
converse INSTANCE-DEPENDENT — EQUIVALENT at m = 1, containment possibly
strict at m ≥ 2, strictness UNPROVED either way in general) is stated
identically at both sites and matches PE7's recommendation with PE6's
qualifier restored. "Direction conservative both before and after" and
"nothing anywhere consumes non-equivalence" — checked: the only external
quoter of these cells ([WM]) pinned the r5 text (pre-non-equivalence), per
the WELDMASTER PE2 record; frontier stays FOUR; no fence/census/grade/
identity moved anywhere in the diff (every hunk is bracket-annotation,
parenthetical, or arc record — confirmed hunk by hunk).

**(f) The r7 round block + S-STATUS transcriptions of PE7 — all checked
against the PE7 report:** "closed the re-derivation complement (every §1–§7
body vein … seven readers)" ✓ verbatim-faithful; "the one gap is r6-BRED"
✓; grade string 0C+1G+2m ✓; "12 re-fence surfaces", "598,500 … REPRODUCED",
"r5-figure unrecoverability at both cited sources" ✓ all in PE7. The ONE
defect found in the entire diff is the fused quotation in the F-1 bullet —
F-1 below.

---

## §3. CHARGE 2 — the arc-accounting system at HEAD

* **S-STATUS chain:** six struck blocks (r1…r6) + [r7] CURRENT
  ("supersedes the six struck lines" — count verified). [r7] says seven
  passes / seven rounds / counter 0/2 / JB-PE8 next / instruments
  byte-frozen / the one new machine figure attributed to PE7.
* **Round blocks:** r1–r7 present; the r7 block's three dispositions match
  the diff exactly; its closer says JB-PE8 next. The r6 block's closer
  ("JB-PE7 … next") stands unstruck as a dated round record — the
  convention every prior pass accepted (r5's block reads the same way).
* **§7.3 CONSUMES bullet (L2611–2617):** three struck generations + [r7]
  "seven hostile passes run, seven repair rounds applied; JB-PE8 is the
  next acceptance attempt" ✓.
* **Footer dating record (L2996–3020):** the r6 entry's Arc line struck;
  [r7] entry present, arc string PE1(1C+9G) → … → PE7(0C+1G+2m) → r7 →
  JB-PE8, counter 0/2 ✓. All four authoritative "next" surfaces (L135,
  L1238, L2617, L3020) say JB-PE8; every other "next acceptance attempt"
  string is struck or inside a dated round block.
* **Strike census:** 168 `~~` tokens at HEAD − 2 backticked literals
  (L860/L862) = 166 = **83 spans**, toggle-parse clean (0 odd-count
  paragraphs, checked mechanically) — exactly r7's "83 (77 + 6 r7)"; the
  pre-r7 blob has 156 tokens, so r7 added exactly 12 tokens = 6 spans, and
  the six enumerate correctly (r6 S-STATUS wrap; §0M col (b) span; §5 SCOPE
  span; JB-BOX-2 "exactly"; §7.3 [r6] counter clause; footer r6 Arc line).
* **Bracket count:** exactly **12 `[r7` brackets** ✓ the commit's claim.
* **Hashes:** all 16 arc hashes (85a8dc9 · 4c97649 · 46f9452 · 67bf0c4 ·
  888e293 · 2fd271e · 8acb2d1 · 87c553d · 38c4754 · ae0acdf · 39e16ee ·
  f9f104e · ca39044 · 4607824 · aa9b603 · 7f6759d) resolve to commits;
  per-pass grade strings verified against the report headlines (PE1 1C+9G,
  PE2 0C+7G, PE3 0C+8G, PE4 0C+8G, PE5 0C+5G, PE6 0C+2G+1m, PE7 0C+1G+2m).
* **Diff arithmetic:** +190/−16, note-only (1 file in the commit stat) ✓.

**Consistent as a system. No finding.**

---

## §4. CHARGE 3 — the seven reports' unnumbered observations, swept

Every explicitly-unnumbered observation across PE1–PE7 traced to a
disposition at HEAD:

* PE1 §6's repair list — all items landed (r1) and re-verified by PE2. PE1
  item "future passes should quote 'identical except elapsed_s'" — moot
  this pass (0-line diffs, elapsed reproduced). The PE1 PARTIAL's internal
  slip (§D3 "Finding 4" for 3) — archived, non-authoritative, nothing rides.
* PE2's L274 wording observation — fixed at r2 as `[r2, hygiene]` (recorded
  in the r2 block's "findings NOT requiring an edit" list, L807–815); its
  small=True pool-content observation — recorded there too; PE3 confirmed
  the quoted counts unaffected.
* PE3's hull_sides "loose wording" — the (c) lattice-data sentence stands
  scoped (realized side); its structural chain_eq observation — the note
  discloses the divisor byte-equality at the G2-2 mechanism paragraph
  (still present); its "re-grep accounting worth auditing next round" —
  audited by PE4 (its F-series), closed by the JB-BOX-6 rule.
* PE5's meta-observations (shrinking finding sizes; PE4's F-5 paraphrase
  disease did not recur) — informational, nothing to absorb.
* PE6's remaining observation content was absorbed as PE7 charges.
* PE7's one residual disclosure — the 598,500 record's 300/300/300
  chain-split is not stated in PE6 §1 (80 nonnegative solutions exist) and
  is not in the note's parameter list either; the note's "parameters
  disclosed there" therefore still needs PE7's "first natural
  parameterization" reading to replay exactly. PE7 graded this a
  disclosure, not a finding; nothing changed; it stands at the same grade.
  Nothing rides on the figure (the four-line theorem carries the
  discharge). NOT re-graded.

**Nothing dangles at finding grade.**

---

## §5. CHARGE 4 — decorrelated re-derivation (my choice: the §5 four-line
theorem, general m, plus a concrete probe of the m ≥ 2 converse)

* **The four-line theorem re-derived step by step** from the r4 lattice
  definition and the [RMG] S2.1 constants: (1) e_{m−1} | E_m and
  e_{m−1} | Γ_l for l ≤ m−2 (t = m−1 in the ∏), Γ_{m−1} = γ_m ≡ h_{m−1}
  (mod e_{m−1}) with γ_m ≥ h_{m−1} ≥ 1 (γ₁ = h₀; γ_m = e_{m−1}w_{m−1}Φ_{m−1}
  + h_{m−1} at m ≥ 2) ✓; (2) V ≡ j_{m−1}h_{m−1}, s^wt(V) = j_{m−1} mod
  e_{m−1} ≤ j_{m−1} ✓; (3) the discard chain is term-wise ≥ 0 ✓; (4)
  integrality from (2) ✓. EXACT — this is also the (⊇) direction at every m.
* **The m ≥ 2 converse probed concretely** (read-only, /tmp-free, in-pass):
  at reads (e₀,h₀,g₀) = (2,1,1), (e₁,h₁,g₁) = (2,1,1): γ₁ = 1, w₁Φ₁ = 2,
  γ₂ = 5, E₂ = 4, Γ₀ = 2, Γ₁ = 5, P₀ = P₁ = 2, so 𝒲₂ = ℤ_{≥0} \ {1, 3},
  while u(V) = (V − (V mod 2))/2 ≥ 0 for EVERY V ≥ 0 — containment STRICT
  at this instance (V = 1 the witness). At e₀ = 1 instances 𝒲₂ = ℤ_{≥0}
  and the containment is EQUALITY. So the converse is exactly
  INSTANCE-DEPENDENT at m = 2, as the r7 text says; both r7 claims
  ("possibly strict at m ≥ 2", "strictness UNPROVED either way in general")
  are TRUE as written (nothing in the note or the reports proves either
  universal, and both universals are in fact false). (Observation, not
  scored: a future round could display a two-line strict instance and
  replace "possibly strict … UNPROVED either way" with the settled
  instance-dependent record; the current wording is honest and
  conservative.)

---

## §6. FINDINGS

### F-1 — MINOR (honesty/quotation form; charge 1(f)). The r7 round block's F-1 bullet quotes, as the assertion of "both [r6, m-1] brackets", a string that appears byte-for-byte at NEITHER site

r7 round block, F-1 bullet (LIVE, L1190–1192):

> Both [r6, m-1] brackets asserted the carried membership hypothesis is
> "per-instance a logically STRONGER hypothesis than the proviso, not an
> equivalent (or weaker one)" — an affirmative non-equivalence claim …

The two struck sources (both still displayed in place under their strikes):

* §0M column (b) (L203–204): "per-instance a logically STRONGER hypothesis
  **than the proviso**, not an equivalent" — no "or weaker one".
* §5 SCOPE (L2035–2036): "per-instance a logically STRONGER hypothesis,
  not an equivalent **or weaker one**" — no "than the proviso".

The quoted string is a fusion of the two (site A's "than the proviso" +
site B's "or weaker one", parenthesized), so the quotation reproduces
neither bracket byte-for-byte, and per-site each attributed clause is
byte-false. Semantic content is exact (the union of what the two sites
asserted), both originals remain recoverable in place, and nothing
downstream consumes the quote — but it sits on a live record surface, in
quotation marks, in the round whose own theme (and whose m-3 fix) is
byte-faithful transcription; the arc's standing discipline (verbatim pins;
quote-with-unit-and-commit) makes quotation marks a byte-fidelity claim.
Mechanism note: PE7's own F-1 header used the site-A string as the quote
for "both brackets"; r7 inherited that composite framing and extended it.
Classification: **MINOR** — no operative content, fence, grade or census
is touched; the cure is one bullet's quote split per site (or the
parenthetical marked as editorial).

---

## §7. What was checked and found clean (so the next pass need not re-open it)

(a) r7 diff hunk-by-hunk: every insertion/deletion accounted for above; no
identity display, fence, census, grade, or instrument was touched. (b) The
equivalence display (both directions, by hand + decorrelated wider-box
probe 340/0). (c) The L283 conjunct: byte-exact transcription at ⟨n3⟩ and
the m-3 bullet; redundancy re-derived from four committed source sites;
caller audit (RANK = T.NR everywhere `jb_shear_vtx` runs). (d) m-3
site-universe completeness (no fifth transcription site). (e) m-2 in place;
no fourth live necessity-overstating membership site. (f) Arc accounting as
a system: S-STATUS ×7, round blocks ×7, CONSUMES, footer, strike census 83
(166/2 outside backticks, toggle-clean, +6 exactly r7's), 12 [r7] brackets,
16 hashes, per-pass grades vs report headlines, all four "next" surfaces =
JB-PE8. (g) Machine legs 4/4 bit-identical (§1), md5s sealed, verification/
untouched, figures vs the note exact. (h) The seven reports' unnumbered
observations all dispositioned or standing benign (§4).

## §8. Pass hygiene

Nothing was edited outside this report file. The four re-runs regenerated
every committed artifact byte-identically (`git diff -- verification/`
empty; only `__pycache__` written by the interpreter). The note is
byte-identical to the r7 blob at HEAD. This report is the pass's only
artifact; committed alone.

    GRTJB-PE8 FINDINGS: 0 critical, 0 gaps, 1 minor / VERDICT: NOT CLEAN
    acceptance counter stays 0/2
