# EFF-GENH4-s2of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` (2173 lines).

**HOME range:** source lines 1209–2173 inclusive — **the whole post-acceptance annex stack**: ANNEX PE5 (the two acceptance MINORs + the S9.2 remark + its machine leg + the acceptance record), ANNEX R (the Codex ratification's repair queue R1–R6), ANNEX R2 (the first annex hostile pass's repairs: GAP-1 + four MINORs + two folded remarks), and the post-annex-pass-2 dated corrections (three MINORs). Earlier text (lines 1–1208, the accepted body, shard 1) is used ONLY to resolve material homed here.

**HEAD blob hash:** `cb713f3a8d8b66d675cae8e42ed5652fc5675739` (clean; last touched by commit `65681144`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (v2 rules 1–10; v3 rules 11–28). Temporary IDs `EFF.GENH4.s2of2.<nn>`.

**GENRE: TAG-SPARSE PROSE ANNEX.** `grep -c '\tag{'` = **0** over the whole note. The genre here is **rider-and-repair prose**: each section names an exact display target in the frozen body, quotes it, and supplies a reading or a replacement lemma. Boundaries are largely pre-marked by the source's own numbered sub-headings (A1–A4, R1.0–R1.2, R2–R6, R2.G1, R2.M1–M4, R2.REM); §6 records the calls that remained.

**SERIES declared (rule 28).** **SERIES GENH4-BOX-1** — the arc record, continued across the freeze by dated appends: entries at `.12` (post-acceptance), `.26` (post-ratification), `.38` (post-annex-pass-1), with the frozen body's `[r1]`/`[r2]`/`[r3]` entries in shard 1 `.68` and the terminal state at `.40`. **SERIES WHAT-DOES-NOT-MOVE** — three parallel scope declarations, one per annex layer (`.13`, `.27`, `.39`), each enumerating exactly what its layer touches; they are not interchangeable and a merge must keep all three.

### Governing effective-text record

**(i) Three nested byte-freezes, each verified before and after its append.** ANNEX PE5: the body at md5 `09af7f78…` (r3 = `4b0d946` = HEAD). ANNEX R: body + PE5 at md5 `a584cb3e…`, 89,530 bytes. ANNEX R2: body + PE5 + R at md5 `863c21600fa48ae755d0d87b77b894d4`, 113,738 bytes, “identical to the HEAD blob at ca3754d”. Post-annex-pass-2: “the pre-annex prefix (128,564 bytes, md5 `22b766d3…`) is byte-identical before == after this append.” **Four freeze predicates, four different byte counts, each re-verified — the tightest freeze discipline in the queue.**

**(ii) Every layer names its exact targets and edits nothing above.** ANNEX PE5: “The frozen accepted body above is NOT edited.” ANNEX R: “nothing above it is edited: each repair is a dated annex lemma/rider naming its exact target.” ANNEX R2: “nothing above this section's first line is edited — every repair names its exact target.”

**(iii) Each layer discloses its own grade as LOWER than the layer below.** PE5: “the annex text itself is a post-acceptance append and has NOT been through a hostile pass”. ANNEX R: same, plus “R2's clause-(c) re-proof is at annex grade”. ANNEX R2: same, plus “annex pass #2 attacks the post-R2 text and attempts the stack's first clean mark”. **The post-annex-pass-2 corrections then record “the stack's clean count HOLDS at 1/2”.**

**EFFECTIVE TEXT FOR THIS SHARD = lines 1209–2173 read in layer order**, with each later layer superseding named parts of the earlier ones:

| Layer | Lines | Supersedes (in-shard) | Riders on shard 1 |
|---|---|---|---|
| ANNEX PE5 | 1209–1476 | — | `.21`, `.25`, `.29`, `.30`, `.39` |
| ANNEX R | 1478–1884 | PE5's A2 partial rider (by R4) | `.14`, `.19`, `.28`–`.32`, `.62` |
| ANNEX R2 | 1886–2140 | ANNEX R's R2 (two legs WITHDRAWN); GENH4-7′'s (a) parenthetical, (c), header; R3's audit sentence | **none** |
| post-pass-2 | 2142–2173 | ANNEX R2's fresh-leg pin; (c′)'s disc parenthetical; R2's instance count | **none** |

### Scope split (rules 7 and 17)

**A. ABSORPTION / supply SET.** What this stack supplies: the genre-F SPLTAIL cap and its σ-inequality (ANNEX-LEMMA GENH4-7, then GENH4-7′ over the true counted family), the per-genre norm-valuation and units normalizations, the closure of a dangling token, the stage-ring carrier erratum, a definition of “law keys” with the pre2 six-key partition, the cap-sharpness clause (c′) at key level, and four minor completions. **It supplies no new count law and no new σ label.**

**B. APPEND / consumption PROTOCOL.** **NO-APPENDS on suppliers; ONE erratum QUEUED.** R3: “the same carrier-rename erratum is OWED TO THE LIVE GENHN ARC and is hereby queued for GENHN's own ratification round — one rider of exactly this R3 form at GENHN.A(i), with the non-maximality witnesses transported.” **Queued, not landed.**

**C. INBOUND corrections RECEIVED.** Three channels, each finding real defects in the layer before it: **PE5** (the acceptance pass: 2 MINORs + 1 remark), **the Codex ratification** (5 findings, outcome CHALLENGE, one of them a GAP on the *post-acceptance* PE5 annex), **annex pass #1** (0C + 1 GAP + 4 MINOR + 2 remarks, the GAP machine-refuting ANNEX R's own witnesses), **annex pass #2** (0C + 0G + 3 MINOR).

### Resolution rules applied

1. Lines 1209–2173 supply the HOME material, read in layer order.
2. A rider that says “Read as …” without editing its target is carried at the target's unit **in shard 1** as CONDITIONALITY, and is emitted **here** as its own unit (the rider is a statement).
3. **ANNEX R2 supersedes annex material only** — no in-range sentence of shard 1 is touched by it, and its own What-does-not-move enumerates the five targets.
4. The post-annex-pass-2 corrections are pure appends naming three display targets inside ANNEX R2 and ANNEX R.
5. External records (the four pass reports, the Codex fold note, `verification/openmath/genh4annex*` legs) are **reading notes only**.

### Quotation and table discipline

Verbatim or explicitly `[ASSEMBLED]`; `…` marks truncation. **One source display is a fixed-width mass table** (A3's per-node masses) and gets rule-14 double emission; **one is a fixed-width six-key partition** (R5's pre2 table) and likewise. No Markdown tables in the source. Compiler ledgers flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GENH4.s2of2.01  [changes-record] · **SERIES GENH4-BOX-1, entry 1 of 3 (post-acceptance)**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX PE5's provenance and scope). verbatim, lines 1209–1225.

> “## ANNEX PE5 (2026-08-09, post-acceptance) — the two display MINORs and the S9.2 remark: the genre-F SPLTAIL cap 2w < N with its σ-inequality (MINOR 1), the per-genre norm valuation at S7's 2SIDED bullet (MINOR 2), and the closure of the dangling "− extra…" token (REMARK). The frozen accepted body above is NOT edited.
>
> **Provenance and scope.** GENH4 was **ACCEPTED 2/2** at PE5 (report
> `GENH4_passPE5_report.md`, commit 11dbd23): 0 CRITICAL, 0 GAP, 2 MINOR
> (+1 remark) — the second stage-one note through the hostile-arc bar,
> after HE7. The accepted text is byte-frozen at r3 (4b0d946 = HEAD, md5
> `09af7f78c34a779ea092738164f1795c`); per the report's grade line the
> owed repair is this dated annex (the HE7 ANNEX F-1 pattern: appended,
> dated, nothing above edited). It covers exactly PE5 MINOR 1 + MINOR 2
> plus the S9.2 remark and NOTHING else. Honesty of grade: the annex
> text itself is a post-acceptance append and has NOT been through a
> hostile pass; what it displays is content every pass verified in
> substance (PE2 ruled the SPLTAIL/UND boundary right in note and
> runner; PE5 re-derived both items and the closure), verified here
> against the committed artifacts plus one additive machine leg
> (`genh4annex_supp.py`, GREEN, record below). No statement, frozen
> number, or conclusion moves.”

**CONDITIONALITY:** **The acceptance record; and the annex's own grade is disclosed as ungraded.** “ACCEPTED 2/2 … the second stage-one note through the hostile-arc bar, after HE7” supersedes shard 1 `.01`'s and `.68`'s grade lines. **The scope claim “covers exactly PE5 MINOR 1 + MINOR 2 plus the S9.2 remark and NOTHING else” is checkable and checks** (§6.1 item 1).

**SUPERSESSION KIND:** `counter re-reading` (the clean counter 1/2 → 2/2) + `license` (the append-only protocol begins).

**SERIES:** GENH4-BOX-1 entry **1 of 3**; the full arc is `.12`'s dated append.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `11dbd23` ✓, `4b0d946` ✓; `verification/openmath/genh4annex_supp.py` ✓, `_output.txt` ✓, `_results.json` ✓ EXIST; `lean/notes/openmath/GENH4_passPE5_report.md` — **verified to EXIST ✓.**

**RESOLUTION TRACE:** statement lines 1209–1225. correction sites: 1850–1868 (the ratification's annotation of this acceptance, `.26`).

**TEETH:** `in-house hostile pass` ×2 CLEAN (PE4, PE5) + the additive leg (`.11`).

---

### EFF.GENH4.s2of2.02  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A1's defect statement — a self-finding against the frozen body). verbatim, lines 1227–1239.

> “### A1. MINOR 1 — the genre-F SPLTAIL cap is 2w < N, not w < N
>
> **The defect (as found at PE5).** The true and implemented genre-F
> SPLTAIL cap is **2w < N** (w = dv(A₁) in v₁ = v units; sealed runner
> `law_F`: `if 2 * dv1 < N`; sealed fresh-row reader:
> `if dv1 is not None and 2 * dv1 < N`) — but it is DISPLAYED nowhere:
> the two display sentences below read naturally as w < N at genre F,
> which is refuted by the committed rows. Additionally, S7's SPLTAIL
> bullet displays the σ-decision inequality for genre E only; the F
> instance is derived here (ANNEX-LEMMA GENH4-7(b)) — it is the
> one-line step on which the F-SPLTAIL σ-label {(1,2),(1,2)} rests,
> a committed key class consumed by W-12.D's σ-labelling clause at
> n = 4.”

**CONDITIONALITY:** **The same defect species as shard 1's CRITICAL: the runner had it right and the display did not.** Two distinct sub-defects: an undisplayed cap and an underived σ-inequality — **and the second is on a clause W-12.D consumes**, which is why the Codex ratification later graded the residue a GAP.

**DERIVATION:** Not a mathematical unit; a defect report with source-code witnesses.

**RESOLUTION TRACE:** statement lines 1227–1239. correction sites: 1500–1625 (R1, which finds this annex's own repair insufficient).

**TEETH:** the sealed runner's two quoted conditionals are the witnesses; the committed rows refute the misread cap (`.05`).

---

### EFF.GENH4.s2of2.03  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed numbered display (A1's three named rider targets). verbatim, lines 1241–1264.

> “**The three display sentences this annex riders (named exactly;
> none is edited).**
>
> 1. **LEMMA GENH4-3 (S4):** "plus the conservative exits (A₀ hidden:
>    SPLTAIL if **w < N-cap** else UND; …)". **Read as:** the "N-cap"
>    is the genre's hidden-A₀ lift-stability floor u_floor measured
>    against 2w — SPLTAIL iff **2w < u_floor**, with u_floor = 2N
>    (genre E, dv-units: GENH4-CAP(E)'s undercut floor) and u_floor = N
>    (genre F, v₁-units: GENH4-CAP(F)'s window floor). At E this is
>    w < N as S6.1 displays; at F it is **2w < N** — NOT w < N.
> 2. **S6.1's leaf row + gloss:** "SPLTAIL(w), w < N:
>    (q−1)·q^{(h−1)/2 + #A₁ > w}" with "genre F identically with
>    comp-weighted exponents AND comp-weighted pin censuses". **Read
>    as:** "identically" transfers the LAW SHAPE (pin census ×
>    free-slot power × band factor); the w-RANGE transfers by the
>    uniform rule of rider 1, i.e. genre F: 2w < N, with the UND
>    complement freeing A₁ exactly at the slots 2s ≥ N.
> 3. **S7's SPLTAIL bullet:** "A₀ window-zero, w < cap: EVERY lift has
>    u_lift ≥ 2N > 2w (E; GENH4-CAP's undercut floor) — a 2SIDED
>    configuration for every lift, including the A₀ = 0 corner …: σ as
>    2SIDED. ∎". **Read as:** at genre F the displayed inequality's
>    instance is **u_lift ≥ N > 2w** (ANNEX-LEMMA GENH4-7(b) below);
>    the rest of the bullet (the 2SIDED reduction, the A₀ = 0 corner
>    via F = φ·(φ + A₁)) applies verbatim.”

**CONDITIONALITY:** **A uniform rule (`2w < u_floor`) supplied for a per-genre constant that the body displayed only in its E instance.** All three riders preserve the displays byte-intact.

**SUPERSESSION KIND:** `wording-rider` ×3 (“Read as …”), each naming its target exactly. **TARGETS:** shard 1 `.21`, `.25`, `.30`.

**ARITHMETIC AUDIT:** the uniform rule `SPLTAIL iff 2w < u_floor` with `u_floor = 2N` (E) gives `w < N` ✓ = the displayed E range; with `u_floor = N` (F) gives `2w < N` ✓ = the implemented F range ✓ — **one rule, two instances, both matching the runner.**

**DERIVATION:** The floors are GENH4-CAP(E)/(F) (shard 1 `.18`).

**RESOLUTION TRACE:** statement lines 1241–1264. correction sites: none.

**TEETH:** `.05`'s committed refutation of the wrong reading.

---

### EFF.GENH4.s2of2.04  [lemma]

**CANONICAL STATEMENT:** FORM: prose derivation + display (blockquote, ANNEX-LEMMA GENH4-7) + proof. verbatim, lines 1266–1314.

> “**In-note derivation of the cap (why 2w < N was always recoverable).**
> S6.3's genre-F UND law carries the complement explicitly: "main
> factor q^{Σ comp(s): s ∈ A₁, **2s ≥ N**}" — UND frees A₁ exactly at
> the slots with 2s ≥ N, so the SPLTAIL range is its complement
> 2w < N; THEOREM GENH4.B's committed verification box ((2,8,1) F →
> 1024 = 512 + 512) prices exactly this partition. The reason the cap
> is 2w < N and nothing else:
>
> > **ANNEX-LEMMA GENH4-7 (the genre-F SPLTAIL cap and σ-inequality).**
> > At a genre-F stage state with A₀ hidden (every in-window A₀ digit
> > zero: a₀-positions ≤ N−1 and a₁-positions ≤ N−1 all vanish) and
> > pin dv(A₁) = w:
> > (a) every lift has u_lift := v₁(A₀^lift) ≥ N, and u_lift = N is
> > realizable (the a₀-component digit at position N, the first
> > out-of-window position; for k ≥ 2 also the free boundary-band
> > a₁ digits);
> > (b) if 2w < N then EVERY disc ≠ 0 lift has u_lift ≥ N > 2w, hence
> > sits in GENH4-3(ii)'s 2SIDED(w, u_lift − w) position — including
> > the A₀ = 0 corner via F = φ·(φ + A₁) — and by S7's 2SIDED bullet
> > (F leg) has σ = {(1,2),(1,2)}: the S1 dictionary's F-SPLTAIL label,
> > (A0)-strong;
> > (c) if 2w ≥ N, NO single label is lift-sound: the u_lift = N lift
> > of (a) has u_lift ≤ 2w and lands in the r3 trichotomy's decided
> > legs (odd N → RAM(N): σ = {(2,2)}) or the out-of-window residual
> > read (even N), while any lift with u_lift > 2w is 2SIDED:
> > σ = {(1,2),(1,2)} — two lifts of the SAME state with DIFFERENT σ.
> > Hence 2w < N is the UNIQUE lift-sound cap, and the reader's UND
> > exit at 2w ≥ N is forced, not conservative slack.
>
> *Proof.* (a) A₀ = a₁x + a₀ has v₁(A₀) = min(v(a₀), v(a₁) + k) with
> the ψ-genericity of GENH4-2 preventing cancellation (S2.1's ring
> invariants, maintained along chains by S5). Hidden means every
> in-window position vanishes: v(a₀) ≥ N (a₀-positions ≤ N−1) and
> v(a₁) + k ≥ N + 1 (a₁-positions ≤ N−1); lift digits at the
> out-of-window positions are free, so u_lift ≥ N with equality
> realizable through a₀ at position N (and, for k ≥ 2, through the
> free band digits the deep₀ factor prices). (b) u_lift ≥ N > 2w is
> GENH4-3(ii)'s antecedent u > 2w at every lift; all data consumed are
> lift-stable (GENH4-CAP(F)), so S7's 2SIDED bullet applies to every
> lift; at A₀ = 0 both factors of φ·(φ + A₁) carry the S2.1 one-side
> polygon — the bullet's own corner sentence. (c) The two lifts are
> exhibited: u_lift = N ≤ 2w falls to GENH4-CAP(F)'s r3 trichotomy —
> at odd N the RAM(N) leg (σ = {(2,2)} by S7's F-RAM bullet), at even
> N the dv0 = N residual read that GENH4-CAP(F) rules out of window
> (different deep lifts realize different residual classes, hence
> different σ); a lift with u_lift > 2w — realizable, the
> out-of-window digits are free — is 2SIDED. {(2,2)} ≠
> {(1,2),(1,2)} and the even-N residual σ's vary, so no constant label
> covers all lifts. ∎”

**CONDITIONALITY:** **SUPERSEDED IN ITS HYPOTHESIS by GENH4-7′** (`.16`) and **IN ITS CLAUSE (c) by (c′)** (`.31`). The Codex ratification found the two bold clauses of the hypothesis contradictory (“a₁-positions ≤ N−1 all vanishing gives v(a₁) ≥ N … the floor v(a₁) + k ≥ N + 1 is the strictly weaker condition”), and **the weaker condition is the counted leaf** — so GENH4-7 proves the σ-label “only for the band-zero SLICE of the leaf — a strict subfamily, exactly HALF the leaf at the first live cell”. Then annex pass #1 machine-refuted clause (c)'s witnesses at band-pinned strata.

**SUPERSESSION KIND:** received `replacement` at the hypothesis (R1) and at clause (c) (R2.G1) + `inventory completion` at clause (a) (the band-nonzero cap `u_lift ≤ m`) + `scope-pin` at (a)'s realizability (R2.M1). **Four kinds on one lemma; the header's own inventory of them was itself under-counted and is corrected at R2.M4** (`.36`).

**CHAIN:** GENH4-7 → **GENH4-7′** (hypothesis widened to the counted family; (a) gains the band cap) → **(c′)** (clause (c) re-proved at key level, band-zero witnessed) → R2.M1 (realizability scoped to `N ≥ 4k+1`) → post-pass-2 MINOR-2 ((c′)(i)'s disc parenthetical corrected for equal characteristic 2) — **TERMINAL: GENH4-7′(a)-with-cap, (b) unchanged, (c′) as corrected.**

**ARITHMETIC AUDIT:** the in-note recoverability argument checks — S6.3's UND main factor frees A₁ at slots with `2s ≥ N` ✓ (shard 1 `.27`), so the SPLTAIL complement is `2w < N` ✓; and the `(2,8,1)` F verification `1024 = 512 + 512` ✓ (shard 1 `.10`) prices exactly that partition ✓. **Clause (b)'s inequality chain `u_lift ≥ N > 2w`** requires `2w < N` ✓ — the cap ✓.

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 1266–1314. correction sites: 1500–1625 (R1), 1909–2011 (R2.G1), 2013–2031 (R2.M1), 2079–2088 (R2.M4), 2159–2167 (post-pass-2 MINOR-2).

**TEETH:** `.05` (committed refutation of the wrong cap) + `.06` (21/21 PARI lifts + the `2w ≥ N` two-lift tooth) — **both annex-resident.**

---

### EFF.GENH4.s2of2.05  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A1's committed refutation of the wrong reading). verbatim, lines 1316–1331.

> “**The committed refutation of the wrong reading (machine, C1–C3 of
> the annex leg).** At the committed (Zp,2,8,k1) row (qscout22 row 16,
> artifact md5 6c2441a1…, pin-verified): the misread cap w < N
> predicts SPLTAIL(4) = 384, SPLTAIL(5) = 96, SPLTAIL(6) = 24,
> SPLTAIL(7) = 6 and UND = 514 — against the committed
> **SPLTAIL(3)-only = 1,536 and UND = 1,024** (the wrong cap
> redistributes the committed UND: 514 + 510 = 1,024). Same at
> (Zp,2,7,k1) (row 15: wrong SPLTAIL(4..6) = 96/24/6, UND = 2 vs
> committed 128) and at the equal-characteristic (Fqt,2,7,k1) (row 19
> ≡ row 15). The annex leg re-derived the full law fresh from
> S6.1/S6.3 (tie: key-for-key on all three rows) and found the wrong
> cap ALSO corrupts the refined (3,)-histories (row 16 @(3,):
> SPLTAIL(4..7) = 1,152/288/72/18, UND 3,072 → 1,542 — hand-derived,
> then machine-confirmed; disclosed as a widening of the sealed
> prereg's mismatch scope). Every mismatching key is a SPLTAIL/UND
> key; NO decided RAM/2SIDED/SPLITEQ/INERT count moves.”

**ARITHMETIC AUDIT (compiler-computed):** the wrong-cap redistribution at row 16: `384 + 96 + 24 + 6 = 510` ✓, and `514 + 510 = 1,024` ✓ = the committed UND ✓ — **mass conserved exactly**, which is what makes the misread cap a *redistribution* rather than a miscount. Row 15: wrong `96 + 24 + 6 = 126` and `2 + 126 = 128` ✓ = the committed UND ✓. Refined history: `1,152 + 288 + 72 + 18 = 1,530` and `1,542 + 1,530 = 3,072` ✓ = the committed UND ✓. **All three closures exact.**

**CONDITIONALITY:** **A disclosed widening of the sealed preregistration's mismatch scope**, hand-derived first and then machine-confirmed — the honest order.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1316–1331. correction sites: none.

**TEETH:** `genh4annex_supp.py` C1–C3 (`.11`), against md5-pinned committed rows.

---

### EFF.GENH4.s2of2.06  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A1's σ-labelling consequence and its machine contact). verbatim, lines 1333–1344.

> “**The σ-labelling consequence (what W-12.D consumes).** S7's proof
> of THEOREM GENH4.C is total at genre E and at five of the six F
> bullets as displayed; the F-SPLTAIL leg is ANNEX-LEMMA GENH4-7(b)
> above. With it, the committed F-SPLTAIL key class (SPLTAIL(3) =
> 384/1,536/384 at rows 15/16/19) carries the σ_F = {(1,2),(1,2)}
> label the S11 firing-table row supplies to W-12.D's σ-labelling
> clause at n = 4 — every disc ≠ 0 lift of every member, both ring
> types. Machine contact (annex leg C5, fresh): 21/21 constructed
> lifts of (Zp,2,7,k1) SPLTAIL(3) states (three A₁ shapes × seven
> lifts, A₀ = 0 corner included) scored σ = {(1,2),(1,2)} by PARI;
> the 2w ≥ N tooth fired (GENH4-7(c)'s two lifts exhibited: w = 4
> hidden state, u_lift = 7 → {(2,2)} vs u_lift = 9 → {(1,2),(1,2)}).”

**CONDITIONALITY:** **“five of the six F bullets as displayed” is the exact accounting of what the frozen body proves** — and the sixth is the one W-12.D consumes. **R1 then finds this supply covers only half the leaf** (`.15`) and widens it.

**ARITHMETIC AUDIT:** `3 A₁ shapes × 7 lifts = 21` ✓. The tooth's two lifts at `w = 4`: `u_lift = 7 ≤ 2w = 8` → odd → RAM(7) → `{(2,2)}` ✓; `u_lift = 9 > 8` → 2SIDED → `{(1,2),(1,2)}` ✓ — **the two-lift contrast is exactly clause (c)'s** ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1333–1344. correction sites: 1581–1592 (R1.1, which restores the supply over the true family).

**TEETH:** annex leg C5, PARI, 21/21 + a fired tooth.

---

### EFF.GENH4.s2of2.07  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A2 — the per-genre norm valuation). verbatim, lines 1346–1363.

> “### A2. MINOR 2 — the norm valuation at S7's 2SIDED bullet is per-genre: u in E's halved units, 2u in F's declared v-units
>
> **The display sentence this annex riders (named exactly; not
> edited).** S7's 2SIDED bullet: "The norm count: Π_θ φ(θ) =
> Res(F, φ) = Π_{η: φ(η)=0} F(η) = Nm_R(A₀), **of valuation u (both
> genres**, using GENH4-2 at the key's own roots η, which satisfy the
> same v/residue facts); if j roots sit at w/2: j·w/2 + (4−j)(u−w)/2 =
> u forces j = 2." **Read as:** the norm identity chain is exact as
> displayed (F ≡ A₀ mod φ, so F(η) = A₀(η) at the key's two roots η);
> the VALUATION tag "u (both genres)" is stated in E's halved units
> throughout. Per genre, in each genre's own declared units (S7
> declares "genre F: w, u in v₁ = v units"):
>
> * **Genre E:** v(A₀(η)) = u/2 at each of the two roots (GENH4-2,
>   dv-units halved) ⟹ v(Nm_R(A₀)) = u. The display is exact.
> * **Genre F:** v(A₀(η)) = u at each of the two roots (v₁ = v units)
>   ⟹ v(Nm_R(A₀)) = **2u** — the display's "u" is false at F in the
>   declared units, by exactly the factor 2.”

**CONDITIONALITY:** **SUPERSEDED by ANNEX R's R4**, which covers all three of S7's mixed-unit sentences at once: “this rider covers all three sentences at once and supersedes A2's partial one.” **A rider superseded by a wider rider — the only such case in the queue.**

**SUPERSESSION KIND:** `provenance-rider` (a units tag), itself later `replacement`-ed by R4.
**TARGETS:** shard 1 `.29`.
**ARITHMETIC AUDIT:** `Nm_R(A₀) = Π_η A₀(η)` over the key's two roots ✓, so `v(Nm) = 2·v(A₀(η))` ✓; at E that is `2·(u/2) = u` ✓ and at F `2·u = 2u` ✓ — **the factor-2 discrepancy is exactly the halving convention** ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1346–1363. correction sites: 1774–1801 (R4).
**TEETH:** `.09` (the committed instance).

---

### EFF.GENH4.s2of2.08  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A2's self-consistency analysis and self-alarm). verbatim, lines 1365–1377.

> “**Why the displayed balance was self-consistent (no number moved).**
> The displayed equation j·w/2 + (4−j)(u−w)/2 = u is the consistently
> HALVED form: halved root-values (v(Y) ∈ {w/2, (u−w)/2}, the bullet's
> own list) balanced against the halved norm valuation u. In F's
> declared units the equation is j·w + (4−j)(u−w) = 2u — the same
> equation multiplied by 2 — and both give j(2w−u) = 2(2w−u), j = 2
> (u ≠ 2w). So j = 2, the Galois-invariance step, and the σ
> conclusion {(2,1),(2,1)}/{(1,2),(1,2)} are all unaffected: the
> defect is the prose tag, not the computation. Self-alarm: a reader
> mixing the units (unhalved values, unhalved-but-u norm) solves
> j·w + (4−j)(u−w) = u and gets j = (4w−3u)/(2w−u) = 9 at
> (w,u) = (3,7) — impossible for 4 roots, so the misreading announces
> itself rather than mislabeling silently.”

**CONDITIONALITY:** **A defect that cannot propagate silently, and the note proves it** — the self-alarm is a genuine structural property, not a reassurance.
**ARITHMETIC AUDIT:** both forms give `j(2w−u) = 2(2w−u)` ✓ ⟹ `j = 2` ✓. The mixed form at `(3,7)`: `(12−21)/(6−7) = (−9)/(−1) = 9` ✓ **exact** — impossible for a quartic ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1365–1377. correction sites: none.
**TEETH:** the self-alarm is itself a structural tooth.

---

### EFF.GENH4.s2of2.09  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A2's committed instance). verbatim, lines 1379–1388.

> “**The committed instance (machine, annex leg C4).** At the committed
> 2SIDED(3,4) of (Zp,2,7,k1) (row 15, count 384): w = 3, u = 7, and
> v(Res(F,φ)) = j·w + (4−j)(u−w) = 2·3 + 2·4 = **14 = 2u**. Exhibited
> on five explicit members over the key φ = x² + 2x + 4 (v(p₁) = 1 ≥
> k, v(p₀) = 2 = 2k exact, residue pair ψ = y² + y + 1 — S2.1's
> invariants): v₂(Res(F,φ)) = 14 on all five, by two independent
> routes (6×6 Sylvester determinant; reduction mod φ + the quadratic
> norm α²p₀ − αβp₁ + β²), and PARI scores σ = {(1,2),(1,2)} on every
> member. The balance display's j = 2 is machine-tied at the same
> members.”

**ARITHMETIC AUDIT:** `2·3 + 2·4 = 14` ✓ and `2u = 14` ✓. The key `φ = x² + 2x + 4` over `ℤ₂`: `v(p₁) = v(2) = 1 ≥ k = 1` ✓, `v(p₀) = v(4) = 2 = 2k` ✓, and the residual `ψ = y² + y + 1` is the unique irreducible quadratic over `F₂` ✓ — **all three S2.1 invariants check.** (This is the same key R3 uses for its non-maximality witness, `.21`.)
**CONDITIONALITY:** **Two independent computational routes plus PARI** — a strong tie for a prose-tag correction.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1379–1388. correction sites: none.
**TEETH:** annex leg C4, two routes + PARI, five members.

---

### EFF.GENH4.s2of2.10  [table]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a **fixed-width ASCII mass table** (A3 — the closure of the dangling token), emitted TWICE per rule 14. verbatim, lines 1390–1421.

> “### A3. REMARK — S9.2's dangling "− extra…" token: the 2SIDED mass is EXACTLY 1/(q²+q+1)
>
> **The display token (named exactly; not edited).** S9.2's μ_E
> bullet: "RAM-mass q²/(q²+q+1), SPLITEQ (q−2)/(2(q²+q+1)), INERT
> q/(2(q²+q+1)), **2SIDED 1/(q²+q+1) − extra…**, REFINE 1/(q²+q+1)".
> **Closure:** the token "− extra…" is an editing remnant; the extra
> is **0**. Write Φ₂ := q² + q + 1 and r := 1/q. The per-node masses
> on the full integer dv-ladder (u = dv(A₀), w = dv(A₁), digits
> uniform, self-similar node):
>
>     RAM     = Σ_{i≥1} (1−r)r^{2i−2}·r^{i−1} = (1−r)/(1−r³)   = q²/Φ₂
>     2SIDED  = Σ_{j≥1} (1−r)r^{j−1}·r^{2j}   = (1−r)r²/(1−r³) = 1/Φ₂
>     even-dμ = (1−r)r/(1−r³) = q/Φ₂, split by the K-census over the
>               q(q−1) unit pairs: SPLITEQ (q−2)/(2q) → (q−2)/(2Φ₂),
>               INERT 1/2 → q/(2Φ₂), REFINE 1/q → 1/Φ₂
>
> and the closure is coefficientwise over the common denominator 2Φ₂:
>
>     2q² + (q−2) + q + 2 + 2 = 2q² + 2q + 2 = 2Φ₂  ⟹  Σ = 1.
>
> Any positive "extra" subtracted from the 2SIDED mass would break
> the partition of unity — self-alarming (the annex leg's tooth:
> extra = r⁴ breaks Σ = 1 at every q). Downstream is untouched: the
> refine aggregation × Φ₂/(q² + q) gives exactly the displayed
> μ_E = ( {(4,1)}: q/(q+1); {(2,1),(2,1)}: 1/(2(q+1));
> {(2,2)}: 1/(2(q+1)) ) = ν₂'s fractions — machine-tied at GH-DENS in
> the sealed battery, re-derived from scratch by PE5's charge 2, and
> re-checked in the annex leg (C6: closed forms + aggregation exact at
> 7 points q, all numerator degrees < 7, so 7 points decide each
> identity). SPLTAIL and UND are window-boundary leaves (they vanish
> in the N → ∞ per-node limit) and correctly do not appear in the
> vector.”

`[TABLE]` — the per-node masses, transcribed:

| Event | Series | Closed form |
|---|---|---|
| RAM | `Σ_{i≥1} (1−r)r^{2i−2}·r^{i−1}` | `(1−r)/(1−r³) = q²/Φ₂` |
| 2SIDED | `Σ_{j≥1} (1−r)r^{j−1}·r^{2j}` | `(1−r)r²/(1−r³) = 1/Φ₂` |
| even-dμ (total) | — | `(1−r)r/(1−r³) = q/Φ₂` |
| → SPLITEQ | `(q−2)/(2q)` of even-dμ | `(q−2)/(2Φ₂)` |
| → INERT | `1/2` of even-dμ | `q/(2Φ₂)` |
| → REFINE | `1/q` of even-dμ | `1/Φ₂` |

**ARITHMETIC AUDIT (compiler-computed, every line):** with `r = 1/q`, `1 − r³ = (q³−1)/q³` and `1 − r = (q−1)/q`, so `(1−r)/(1−r³) = q²(q−1)/(q³−1) = q²/(q²+q+1) = q²/Φ₂` ✓ (since `q³−1 = (q−1)Φ₂`). `(1−r)r²/(1−r³) = q²/Φ₂ · r² = 1/Φ₂` ✓. `(1−r)r/(1−r³) = q²/Φ₂ · r = q/Φ₂` ✓. Splits: `(q/Φ₂)·(q−2)/(2q) = (q−2)/(2Φ₂)` ✓; `(q/Φ₂)·(1/2) = q/(2Φ₂)` ✓; `(q/Φ₂)·(1/q) = 1/Φ₂` ✓. Closure over `2Φ₂`: numerators `2q², (q−2), q, 2, 2` sum to `2q² + 2q + 2 = 2Φ₂` ✓ **⟹ Σ = 1, extra = 0** ✓. **Every displayed identity reproduces.** The C6 degree argument: all numerator degrees `< 7`, so agreement at 7 points decides ✓ (a polynomial of degree < 7 vanishing at 7 points is zero ✓).

**CONDITIONALITY:** **An editing remnant closed by derivation, with a tooth.** Downstream is untouched, and the μ_E aggregation is re-derived independently by PE5's charge 2 and by the annex leg.

**SUPERSESSION KIND:** `replacement` of a dangling token by 0.
**TARGETS:** shard 1 `.39`.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1390–1421. correction sites: none.
**TEETH:** annex leg C6 + the extra-token tooth, FIRED.

---

### EFF.GENH4.s2of2.11  [run-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A4 — the additive machine leg). verbatim, lines 1423–1448.

> “### A4. Machine record (additive leg; every sealed artifact byte-frozen)
>
> `verification/openmath/genh4annex_supp.py` — sealed with
> preregistered predictions P1–P6 at cceca77 (BEFORE the run), run
> fresh, repaired once with disclosure, re-run fresh: **GREEN, 0
> violations, 0.1 s + PARI** (`genh4annex_supp_output.txt` md5
> 713a0a3b…, `genh4annex_supp_results.json` md5 37d0650e…, committed
> e945734). C0: 5/5 md5 pins verified (sealed runner + both sealed
> GENH4 artifacts + qscout22 runner/results). C1 (P1): the committed
> rows 15/16/19 read exactly as this annex states. C2 (P2): a fresh
> typing of the S6.1/S6.3 genre-F recursion ties all three rows
> key-for-key. C3 (P3): the wrong-cap table equals PE5's
> failure-scenario numbers exactly, masses conserved, mismatch set =
> SPLTAIL/UND keys only. **Disclosed smoke catch:** the sealed prereg
> scoped C3's mismatch set to the empty history; the first run (RED,
> 2 instrument-side violations) caught the wrong cap propagating into
> the refined (3,)-history keys as well — values hand-derived before
> the one-line repair (row 16 @(3,): 1,152/288/72/18 + UND 1,542,
> closing to the committed 3,072; row 15 @(3,): 288/72/18 + UND 6,
> closing to 384), then machine-confirmed; the refutation of the
> misread cap is thereby STRENGTHENED, and no decided key moves under
> it. C4 (P4) and C5 (P5): as displayed in A2/A1 (five 2SIDED members
> two-route exact; 21/21 SPLTAIL lifts + the 2w ≥ N two-lift tooth
> FIRED). C6 (P6): the closure, the aggregation, and the extra-token
> tooth FIRED. σ-oracle: the same GP sig routine as the sealed
> battery's GH-SIGMA (nfinit/idealprimedec per p-adic factor).”

**CONDITIONALITY:** **A second published RED-then-repair cycle in this note** (after shard 1's `.65`) — this one at the annex leg, with the widened refutation disclosed as a STRENGTHENING.
**ARITHMETIC AUDIT:** row 15 @(3,): `288 + 72 + 18 = 378` and `378 + 6 = 384` ✓ **exact**; row 16 @(3,) audited at `.05` ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1423–1448. correction sites: 2152–2158 (the post-pass-2 MINOR-1 corrects a *different* leg's pin, not this one).
**TEETH:** P1–P6, GREEN after a disclosed repair; two teeth fired. **PIN VERIFICATION:** `cceca77` ✓, `e945734` ✓; the three leg files EXIST ✓.

---

### EFF.GENH4.s2of2.12  [changes-record] · **SERIES GENH4-BOX-1, the acceptance entry**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the dated GENH4-BOX-1 append recording the acceptance). verbatim, lines 1450–1463.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09).** This line
> continues the [r1]/[r2]/[r3] record of S10-BOX-1/S13; under the
> acceptance freeze it cannot be inserted there, so it lives here:
> **PE4 (e15308d) and PE5 (11dbd23, `GENH4_passPE5_report.md`) HAVE
> NOW RUN: PE4 CLEAN (1/2); PE5 CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR
> (+1 remark), machine leg bit-identical GREEN (isolated re-run
> 245,693/0, leaf-diff = elapsed only) plus a fresh q = 9 route. The
> 2-clean count completed 1/2 → 2/2: GENH4 IS ACCEPTED — the second
> stage-one note through the hostile-arc bar. The text is frozen at
> r3 4b0d946; this dated annex discharges the owed MINOR 1 + MINOR 2
> riders and closes the S9.2 remark, edits nothing above, and moves
> no sealed number. Conditionality is unchanged: exactly the S11
> arc-grade stack (minimum grade 0/2 at verdict time: W-12, HEX3,
> GENIND live — PE5 charge 4).**”

**CONDITIONALITY:** **The acceptance, with its conditionality explicitly UNCHANGED: “minimum grade 0/2 at verdict time”.** So GENH4 is 2/2 and P(4) is conditional on a stack whose minimum is 0/2 — **the two grades must never be conflated**, and the note is careful.
**SUPERSESSION KIND:** `counter re-reading`, executed by append because the target is frozen.
**TARGETS:** shard 1 `.01`, `.44`, `.68`.
**ARITHMETIC AUDIT:** the isolated re-run `245,693/0` ✓ matches shard 1 `.67`'s run-2 total exactly ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1450–1463. correction sites: 1850–1868 (the ratification annotation).
**TEETH:** `in-house hostile pass` ×2 CLEAN + an independent bit-identical re-run + a fresh q = 9 route.
**PIN VERIFICATION:** `e15308d` ✓, `11dbd23` ✓, `4b0d946` ✓.

---

### EFF.GENH4.s2of2.13  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 1 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1465–1476.

> “**What does not move.** Every displayed statement, proof, and frozen
> number of the accepted body; the sealed runner and artifacts (md5
> pins re-verified, C0); the committed key tables (the annex leg reads
> them, never writes); THEOREM GENH4.A/B and the count laws (the cap
> was always 2w < N in every committed number and in S6.3's
> complement); THEOREM GENH4.C's dictionary and the W-12.D supply (the
> labels were always right — the annex ADDS the displayed F-inequality
> GENH4-7(b), it does not correct a label); the eleven densities, the
> triple tie, and the S11 conditionality stack; GENH4-BOX-2 (n = 5's
> embedded CS genres stay OPEN). The E-side displays (w < N at S6.1,
> u_lift ≥ 2N at S7) are exact as written — MINOR 1 is the genre-F
> transfer only.”

**CONDITIONALITY:** **An enumerated non-movement declaration — the annex layer's own scope check.** Its claim “the annex ADDS the displayed F-inequality …, it does not correct a label” is the sentence that keeps GENH4.C's dictionary intact through both later layers.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1465–1476. correction sites: none.
**TEETH:** NONE — a scope fence.

---
### EFF.GENH4.s2of2.14  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R's provenance; the Codex ratification's CHALLENGE). verbatim, lines 1478–1498.

> “## ANNEX R (2026-08-09, post-ratification; CODEX F1-F5)
>
> **Provenance and scope.** The ratification sweep's Codex leg
> (`CODEX_GENH4RAT_2026-08-09.md`, session 019fe500-0ddc-7b52-9e32-c4dff01e560c,
> gpt-5.6-sol at HIGH, fresh context, read-only) returned **5 findings —
> RATIFICATION OUTCOME: CHALLENGE** at adjudication: F2 (CONFIRMED, GAP as
> stated with the CRITICAL flag disclosed both ways — the consumed-clause
> gap on ANNEX-LEMMA GENH4-7), F3 (CONFIRMED GAP, display/frame scope —
> the stage-ring "DVR" sentences), F4 (CONFIRMED GAP, scoped to
> GENH4-7(c), unconsumed), F5 (CONFIRMED, regraded MINOR — S7 units),
> F1 (REFUTED as CRITICAL against the committed artifact; CONFIRMED as
> MINOR display — "law keys" undefined). This annex executes the fold
> note's repair queue R1–R5 in order. The accepted body + ANNEX PE5
> above are BYTE-FROZEN — md5 `a584cb3e8985775ee6f1c9f09b7cf9e5`
> (89,530 bytes) verified identical before and after this append; the
> freeze boundary is the PE5 annex's last line, and nothing above it is
> edited: each repair is a dated annex lemma/rider naming its exact
> target. Honesty of grade: this annex is a post-ratification append and
> has NOT itself been through a hostile pass; R1's machine leg is sealed
> and GREEN (record in R1.2), R2's clause-(c) re-proof is at annex grade
> (two displayed existence arguments + transfer steps citing GENH4-4).”

**CONDITIONALITY:** **A decorrelated model, reading an ACCEPTED 2/2 note, returned five findings — three GAPs, one of them on the post-acceptance annex, and one CRITICAL flag REFUTED against the committed artifact.** The refutation of F1-as-CRITICAL is as important as the confirmations: **the committed artifact decided against the verifier**, and the finding survived only as a MINOR display defect (an undefined term).

**ARITHMETIC AUDIT:** five findings, dispositions: 3 CONFIRMED GAP (F2, F3, F4) + 1 CONFIRMED-regraded MINOR (F5) + 1 REFUTED-as-CRITICAL / CONFIRMED-as-MINOR (F1) = 5 ✓. Queue R1–R5 maps to F2, F4, F3, F5, F1 ✓ — **ordered by severity, not by number**, with R6 added as a noted extra.

**SUPERSESSION KIND:** none of its own (a provenance record); it establishes freeze predicate 2.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1478–1498. correction sites: 1886–1907 (annex pass #1's provenance, which finds a GAP in this layer).
**TEETH:** **`decorrelated-model audit`** — three of the five findings could not have been produced by any run (a hypothesis contradiction, a ring-theoretic frame error, an undefined term).
**PIN VERIFICATION:** `lean/notes/openmath/CODEX_GENH4RAT_2026-08-09.md` ✓ EXISTS.

---

### EFF.GENH4.s2of2.15  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with two nested quotations (R1.0 — the consumed-clause gap, stated exactly). verbatim, lines 1500–1535.

> “### R1 (CODEX F2, the consumed-clause gap): ANNEX-LEMMA GENH4-7' — the F-SPLTAIL supply argument re-proved over the FREE boundary band
>
> **R1.0 The defect, exactly.** ANNEX-LEMMA GENH4-7 (ANNEX PE5, A1)
> states its hypothesis as
>
> > "At a genre-F stage state with A₀ hidden (every in-window A₀ digit
> > zero: a₀-positions ≤ N−1 and **a₁-positions ≤ N−1** all vanish)"
>
> and its proof glosses
>
> > "Hidden means every in-window position vanishes: v(a₀) ≥ N
> > (a₀-positions ≤ N−1) and **v(a₁) + k ≥ N + 1 (a₁-positions ≤ N−1)**".
>
> The two bold clauses contradict each other: a₁-positions ≤ N−1 all
> vanishing gives v(a₁) ≥ N, i.e. v(a₁) + k ≥ N + k — the floor
> v(a₁) + k ≥ N + 1 is the strictly weaker condition "a₁-positions
> ≤ N−k all vanish". And the WEAKER condition is the counted leaf: the
> sealed runner's `law_F` prices SPLTAIL as
> (q^{comp(w)}−1) · wf(A1, w) · deep0 with
> **deep0 = q^{Σ comp(s): s ∈ A₀, s > N} = q^{k−1}** — the boundary-band
> digits at heights N+1 … N+k−1, carried by the IN-WINDOW a₁-positions
> N−k+1 … N−1 (S2.3's comp-1 band slots), are FREE in the counted
> family; the height-N band slot (a₁-position N−k) is pinned zero
> (deep0 sums s > N strictly). So GENH4-7 as stated proves the σ-label
> only for the band-zero SLICE of the leaf — a strict subfamily,
> exactly HALF the leaf at the first live cell (machine, R1.2). The
> slice is first live at **k ≥ 2 AND N ≥ 4k+3** (SPLTAIL needs
> 2w < N with w ≥ 2k+1, so N ≥ 4k+3; the band is empty at k = 1, where
> GENH4-7 and GENH4-7' coincide verbatim): every committed F-SPLTAIL
> key is k = 1 (rows 15/16/19 + feven — machine C2), and the fresh
> k = 2 row (Zp,2,9,k2) has NO SPLTAIL leaf, so the gapped slice had
> ZERO machine exercise before this annex. CONSUMPTION: S7's F-SPLTAIL
> bullet = GENH4-7(b) = the W-12.D σ-labelling supply row (S11 firing
> table) — a consumed clause was textually gapped on a nonempty menu
> slice; hence the CHALLENGE outcome. The conclusion was TRUE all
> along, by the proof's own floor inequality; the corrected lemma:”

**CONDITIONALITY:** **A hypothesis that contradicts its own proof's gloss, on a clause W-12.D consumes, over a slice with ZERO machine exercise.** Every element of that sentence is load-bearing: the contradiction is textual, the consumption is real, and the untested slice is half the leaf at the first live cell.

**ARITHMETIC AUDIT (compiler-computed):** `a₁-positions ≤ N−1 all vanish` ⟹ `v(a₁) ≥ N` ⟹ `v(a₁) + k ≥ N + k` ✓, strictly stronger than `≥ N+1` for `k ≥ 2` ✓ — **the two clauses genuinely differ, and only at `k ≥ 2`** ✓, exactly matching “the band is empty at k = 1, where GENH4-7 and GENH4-7' coincide verbatim” ✓. First-live condition: SPLTAIL needs `2w < N` and `w ≥ 2k+1` (shard 1 `.17`'s A₁ string floor), so `N > 2(2k+1) = 4k+2`, i.e. `N ≥ 4k+3` ✓ **exact**; at `k = 2` that is `N ≥ 11` ✓ — matching R1.2's cell `(2,11,2)` ✓. `deep0 = q^{k−1}` counts the band heights `N+1 … N+k−1`, i.e. `k−1` of them ✓ — **and the height-N slot is pinned zero because deep0 sums `s > N` strictly** ✓.

**DERIVATION:** Not a mathematical unit; a defect report.
**RESOLUTION TRACE:** statement lines 1500–1535. correction sites: none.
**TEETH:** **`decorrelated-model audit`**; the “ZERO machine exercise before this annex” is the disclosure that makes the finding sharp.

---

### EFF.GENH4.s2of2.16  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENH4-7′) + proof of (a) and (b). verbatim, lines 1537–1579.

> “> **ANNEX-LEMMA GENH4-7' (GENH4-7 with the leaf's true floor — the
> > free boundary band quantified; replaces GENH4-7's hypothesis
> > sentence and clause (a)'s parenthetical, everything else
> > unchanged).** At a genre-F stage state with A₀ hidden IN THE LEAF
> > SENSE — every A₀ slot at v₁-height ≤ N vanishes, i.e. v(a₀) ≥ N
> > (a₀-positions ≤ N−1 all vanish) and v(a₁) + k ≥ N + 1
> > (a₁-positions ≤ N−k all vanish) — while the k−1 boundary-band
> > a₁-positions N−k+1, …, N−1 (v₁-heights N+1, …, N+k−1: exactly
> > S6.3's deep₀ = q^{k−1} factor) remain FREE, and pin dv(A₁) = w:
> > (a) for EVERY value of the free band digits and EVERY lift,
> > u_lift := v₁(A₀^lift) ≥ N, with u_lift = N realizable (the a₀
> > lift digit at position N), and at a band-nonzero member
> > u_lift ≤ m := the lowest nonzero band height ≤ N+k−1;
> > (b) if 2w < N then EVERY disc ≠ 0 lift of EVERY member — all
> > q^{k−1} band completions, both characteristics — has
> > u_lift ≥ N > 2w, hence sits in GENH4-3(ii)'s
> > 2SIDED(w, u_lift − w) position — including the A₀ = 0 corner via
> > F = φ·(φ + A₁) — and by S7's 2SIDED bullet (F leg) has
> > σ = {(1,2),(1,2)}: the S1 dictionary's F-SPLTAIL label,
> > (A0)-strong, lift-sound on the WHOLE counted family;
> > (c) if 2w ≥ N, NO single label is lift-sound for the leaf key
> > (re-proved per band stratum in R2 below).
> > At k = 1 the band is empty and GENH4-7' ≡ GENH4-7.
>
> *Proof of (a) and (b).* v₁(A₀) = min(v(a₀), v(a₁) + k), with
> cancellation prevented by ψ-genericity (GENH4-2; S2.1's invariants,
> maintained along chains by S5): the height-m contribution is the
> F_{q²}-letter d₁ȳ + d₀ read from (a₁-digit at m−k, a₀-digit at m),
> and ȳ ∉ F_q makes it vanish iff both digits do — both
> characteristics. Every contributing height is ≥ N: on the a₀ side
> the in-window digits (positions ≤ N−1) are state-zero and lift
> digits sit at positions ≥ N; on the a₁ side the floor is N+1, and
> the FREE band digits sit at heights N+1 … N+k−1 ≥ N+1 — so
> u_lift ≥ N REGARDLESS of the band values; equality realizable via
> a₀ at position N; a nonzero band digit at height m caps
> u_lift ≤ m by the no-cancellation letter (d₁ ≠ 0). (b)
> u_lift ≥ N > 2w is GENH4-3(ii)'s antecedent u > 2w at every lift
> and every band completion; the data consumed (w and its pin letter)
> are lift-stable (GENH4-CAP(F): w ≤ (N−1)/2 < N); S7's 2SIDED bullet
> (F leg) consumes only v(A₁(θ)) = w and v(A₀(θ)) = u_lift > 2w, so
> it applies verbatim; at A₀^lift = 0 both factors of φ·(φ + A₁)
> carry the S2.1 one-side polygon — the bullet's own corner sentence.
> ∎ (Clause (c): R2 below.)”

**CONDITIONALITY:** **(b) — the consumed clause — is now proved on the WHOLE counted family and is untouched by everything that follows.** (a) gains a band cap; (c) is deferred to R2 and later WITHDRAWN-and-replaced by (c′) (`.31`). **The header's supersession inventory is itself under-counted and is corrected at R2.M4** (`.36`). (a)'s realizability parenthetical is scoped to `N ≥ 4k+1` at R2.M1 (`.33`); **(b) is unaffected because SPLTAIL forces `N ≥ 4k+3`** ✓.

**SUPERSESSION KIND:** `replacement` of GENH4-7's hypothesis sentence and (a)'s parenthetical; `inventory completion` for (a)'s band cap. **NOT a replacement of (b)'s conclusion — “same conclusion, hypothesis now COVERING the counted family”** (`.17`).

**ARITHMETIC AUDIT:** the band has `k−1` free positions (`N−k+1 … N−1`, i.e. v₁-heights `N+1 … N+k−1`) ✓ = `deep₀ = q^{k−1}` ✓. Lift-stability of w: `2w < N` ⟹ `w ≤ (N−1)/2 < N` ✓ — inside GENH4-CAP(F)'s stable range ✓.

**DERIVATION:** Displayed. Justification tags: `by XREF GENH4-2` (no-cancellation by ψ-genericity) + `by XREF` S2.1/S5 (invariant maintenance) + `computation` (the height analysis) + `by XREF GENH4-3(ii)` + `by XREF` S7's 2SIDED F leg.

**RESOLUTION TRACE:** statement lines 1537–1579. correction sites: 1957–1999 ((c) → (c′)), 2013–2031 (M1), 2079–2088 (M4), 2159–2167 (post-pass-2 MINOR-2 on (c′)'s proof).

**TEETH:** R1.2's leg (`.18`) — **the k ≥ 2 slice's FIRST exercise**, 24,576 members enumerated, 96/96 char-0 PARI + 96/96 char-p, teeth 4/4.

---

### EFF.GENH4.s2of2.17  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.1 — the W-12.D supply restored). verbatim, lines 1581–1592.

> “**R1.1 The W-12.D supply, restored.** THEOREM GENH4.C's F-SPLTAIL
> leg now reads ANNEX-LEMMA GENH4-7'(b) in place of GENH4-7(b) —
> same conclusion, hypothesis now COVERING the counted family. With
> it, the committed F-SPLTAIL key class (SPLTAIL(3) = 384/1,536/384
> at rows 15/16/19, all k = 1 — where the two lemmas coincide) AND
> the k ≥ 2 slice (first exercised in R1.2) carry the
> σ_F = {(1,2),(1,2)} label that the S11 firing-table row supplies to
> W-12.D's σ-labelling clause at n = 4 — every disc ≠ 0 lift of every
> member, both ring types. No committed key count, no density, and no
> k = 1 σ-claim moves: the sealed counts always priced the free band
> (deep0 was in `law_F` and S6.3's display from the seal); the defect
> was the post-acceptance annex's hypothesis gloss only.”

**CONDITIONALITY:** **The install instruction for R1, and the sentence a chapter cut of THEOREM GENH4.C must carry: its F-SPLTAIL leg reads GENH4-7′(b).**
**SUPERSESSION KIND:** `replacement` (which lemma the leg reads).
**TARGETS:** shard 1 `.11`, `.30`, `.33`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1581–1592. correction sites: none.
**TEETH:** `.18`.

---

### EFF.GENH4.s2of2.18  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.2 — the k ≥ 2 slice's first machine exercise). verbatim, lines 1594–1625.

> “**R1.2 Machine record (the k ≥ 2 slice's FIRST exercise).**
> `verification/openmath/genh4annexr_supp.py` — sealed with
> preregistered predictions R1–R7 at commit 6272cd4 (BEFORE the run;
> one full design dry-run disclosed in the docstring: it caught a
> branch explosion in the first BFS root counter, replaced by the
> exact Panayi recursion; all other checks GREEN on the dry-run), run
> fresh: **GREEN, 0 violations, 0.4 s + PARI** (output md5
> `c1ed4a7f…`, results md5 `f26186fd…`, bit-identical to the
> dry-run's artifacts). The cell: (q,N,k) = (2,11,2), SPLTAIL(5),
> 2w = 10 < N = 11 — the first live k ≥ 2 cell (N = 4k+3). Checks:
> C0 5/5 md5 pins (sealed runner + artifacts + qscout22 pair).
> C2: the fresh S6-typed law has NO SPLTAIL at (2,9,2)/(2,10,2) and
> first realizes SPLTAIL(5) at N = 11; all 4 committed F-SPLTAIL keys
> are k = 1. C3: the SEALED runner's own `law_F(2,11,2)` gives
> SPLTAIL(5) = 24,576 = 3·2¹²·2 (deep0 = 2 = q^{k−1}), tying the
> fresh typing key-for-key (9 keys), node mass 2²⁰ exact; the
> OLD-gloss (band-pinned) family = 12,288 = HALF — count-refuted as a
> description of the leaf. C4: all 24,576 leaf members enumerated:
> the GENH4-7' floor holds on ALL; the band-nonzero half (12,288)
> violates the old hypothesis, 0 violate the new (characteristic-
> blind digit layer). C5: 96 constructed lifts (24 states = 3 pin
> letters × 2 band values × 4 A₁-completions; 4 lifts each, incl. the
> A₀ = 0 corner and u_lift = N = 11 lifts) over φ = x² + 4x + 16:
> PARI σ = {(1,2),(1,2)} on 96/96 — constant across BOTH band values
> (48 members on the previously unexercised band-nonzero slice).
> C6 (FIRST char-p σ contact for F-SPLTAIL): the same 96 members over
> F₂[[t]] (φ = x² + t²x + t⁴): disc ≠ 0 (exact gcd over F₂[t]) and
> EXACTLY 4 roots in F₄[[t]], 0 in F₂[[t]] on 96/96 — two unramified
> conjugate quadratic pairs, the {(1,2),(1,2)} read. C7 TOOTH: 2
> wrong-floor mutants (a₀-digit at position 9 < N: u = 9 odd ≤ 2w →
> RAM(9)): char-0 PARI σ = {(2,2)} and char-p 0 roots in F₄[[t]] —
> FIRED 4/4: the GENH4-7' floor is load-bearing, not decorative.”

**CONDITIONALITY:** **The gapped slice's first exercise, and it confirms the repair count-for-count.** The old gloss's family is exactly HALF ✓ — the finding's own quantitative claim, machine-confirmed.

**ARITHMETIC AUDIT (compiler-computed):** `SPLTAIL(5) = 24,576 = 3·2^{12}·2` ✓ (`3·4096·2 = 24,576`) ✓, with `deep0 = 2 = q^{k−1} = 2^1` ✓. Old-gloss family `12,288 = 24,576/2` ✓ **exactly HALF** ✓. Node mass `2²⁰ = 1,048,576` ✓. Cell: `N = 4k+3 = 11` at `k = 2` ✓; `w = 5` gives `2w = 10 < 11` ✓ and `w ≥ 2k+1 = 5` ✓ — **the minimal live cell**. Lifts: `3 × 2 × 4 = 24` states ✓ × 4 lifts = **96** ✓, of which the band-nonzero half is 48 ✓. Char-p read: 4 roots in `F₄[[t]]`, 0 in `F₂[[t]]` ⟹ two conjugate unramified quadratic pairs ⟹ `{(1,2),(1,2)}` ✓ **exact**. Tooth: `u = 9` odd `≤ 2w = 10` → RAM(9) → `{(2,2)}` ✓ ≠ `{(1,2),(1,2)}` ✓ — the mutant fires ✓.

**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1594–1625. correction sites: none.
**TEETH:** seven checks, GREEN; **C6 is the FIRST char-p σ contact for F-SPLTAIL in the corpus**; C7's two wrong-floor mutants fired 4/4.
**PIN VERIFICATION:** `6272cd4` ✓; `verification/openmath/genh4annexr_supp.py` ✓, `_output.txt` ✓, `_results.json` ✓ EXIST.

---

### EFF.GENH4.s2of2.19  [lemma]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph + three bulleted per-stratum witnesses (R2 — clause (c) re-displayed). verbatim, lines 1627–1701. *(The three stratum bullets are quoted; the section's scope paragraph opens it.)*

> “### R2 (CODEX F4): GENH4-7'(c) re-displayed per band stratum — the cap-sharpness witnesses that actually exist
>
> **Scope.** Clause (c) is CAP SHARPNESS only: W-12.D's supply consumes
> (b), and the reader's UND exit at 2w ≥ N is conservative-sound
> regardless — F4 is unconsumed. But the old display's two witnesses
> were wrong exactly where Codex pointed: at a band-pinned state
> (k ≥ 2, lowest nonzero band digit at height m) with m ≤ 2w, NO lift
> has u_lift > 2w (GENH4-7'(a): u_lift ≤ m — Codex's (k,N,w) =
> (2,9,5), m = 10 = 2w instance), so "a lift with u_lift > 2w —
> realizable" is false there; and at even N the sentence "different
> deep lifts realize different residual classes, hence different σ"
> is unjustified in char 2 (dμ < w forces the S₁-slot to 0 and
> T² + S₀ is always a square over F_{q²}: the read is REFINE, not a
> decided σ). The corrected per-stratum witnesses (2w ≥ N throughout;
> u-geography from GENH4-7'(a): u_lift sweeps {N, N+1, …} at a
> band-zero state and {N, …, m} at a band-pinned state; legs per
> GENH4-3 + GENH4-CAP(F): u odd ≤ 2w → RAM(u), σ = {(2,2)}; u even
> = 2dμ ≤ 2w → residual read at depth dμ; u > 2w → 2SIDED,
> σ = {(1,2),(1,2)}): …”

*(The three bullets — N odd; N even with dμ < w; N even with dμ = w — are reproduced verbatim in the source at lines 1647–1701 and are carried here by reference to their own targets: the first two are WITHDRAWN at `.29`, and the third survives with its existence input completed at `.34`.)*

**CONDITIONALITY:** **TWO of the three per-stratum witnesses are later MACHINE-REFUTED and WITHDRAWN** (`.29`); the third (`2w = N`) survives, with its char-odd existence completed by a coset count (`.34`) and its char-2 trace argument re-derived SOUND by the annex pass (`.37`). **The scope sentence is what keeps the damage contained: “Clause (c) is CAP SHARPNESS only: W-12.D's supply consumes (b) … F4 is unconsumed.”**

**SUPERSESSION KIND:** received `replacement` with **WITHDRAWAL** — two displayed legs are withdrawn, not re-worded.
**CHAIN:** GENH4-7's (c) → **R2's per-stratum witnesses** → **R2.G1: two legs WITHDRAWN, (c′) at key level — TERMINAL** (with M2/M3 completing (c′)'s inputs and post-pass-2 MINOR-2 fixing its disc parenthetical).
**ARITHMETIC AUDIT:** Codex's instance `(k,N,w) = (2,9,5)`: `m = 10 = 2w` ✓, and GENH4-7′(a)'s cap gives `u_lift ≤ m = 10 = 2w` ✓ — so **no lift has `u_lift > 2w`** ✓, the old witness is unrealizable ✓. The char-2 objection: at `dμ < w` the S₁-slot is 0 ✓ and `T² + S₀` is always a square over `F_{q²}` in char 2 ✓ (Frobenius is bijective) — so the read is `'1sq'` (REFINE), not decided ✓.
**DERIVATION:** Displayed per stratum; two legs later withdrawn.
**RESOLUTION TRACE:** statement lines 1627–1701. correction sites: 1909–2011 (R2.G1), 2033–2059 (M2), 2061–2077 (M3).
**TEETH:** annex pass #1's FR4/FR5 legs — **which refuted two of the three** (`.29`).

---

### EFF.GENH4.s2of2.20  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2's char-2 refine-deeper leg). verbatim, lines 1703–1718.

> “**The char-2 refine-deeper leg (cited where used above).** A '1sq'
> read at depth dμ₁ refines with letter s₁ = the square root (S5, one
> step); LEMMA GENH4-4 maps the refine locus ONTO the floored fresh
> node {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁}, whose digits are free lift
> digits; realize the fresh leaf dv(A₁′) = dμ₁+1 =: w′,
> dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ (nonempty: S6.1's census
> (q^{comp}−1)·q^{…} > 0, slots live by GENH4-6): a fresh
> 2SIDED′(w′, w′+1) for every such lift, σ = {(1,2),(1,2)} by S7's
> 2SIDED bullet — which differs from the {(2,2)} of the paired RAM
> lift. This is the old display's "different deep lifts" sentence
> made into an actual construction; it is an annex-grade transfer
> (GENH4-4 + census nonemptiness, both PROVED in the body, composed
> here without a fresh hostile pass).”

**CONDITIONALITY:** **WITHDRAWN — machine-refuted at annex pass #1** (`.29`). The transport error is named there: GENH4-4's onto-statement quantifies over the FULL refine slice, and on a FIXED member only lift digits vary, so **neither fresh coordinate is free**.
**SUPERSESSION KIND:** received **`replacement` with WITHDRAWAL**.
**ARITHMETIC AUDIT:** the claimed fresh leaf `dv(A₀′) = 2dμ₁+3` with `w′ = dμ₁+1` gives `2w′+1 = 2dμ₁+3` ✓ internally consistent — **the arithmetic is fine; the availability is not**, which is precisely the withdrawal's ground.
**DERIVATION:** Displayed; withdrawn.
**RESOLUTION TRACE:** statement lines 1703–1718. correction sites: 1917–1956 (R2.G1's refutation).
**TEETH:** FR4 refuted it 6/6.

---

### EFF.GENH4.s2of2.21  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs (R3 — the stage-ring frame erratum). verbatim, lines 1720–1765.

> “### R3 (CODEX F3): the stage-ring frame erratum — v and res live in L/O_L, and R is an order, not a DVR
>
> **The defect.** S2.1's two carrier sentences are literally false:
> "φ is irreducible, **R is a complete DVR**, totally ramified
> quadratic" (genre E) and "R is an unramified-over-the-ladder
> **DVR** … residue field K = F_{q²}" (genre F), plus "**R's
> associated graded** IS COROLLARY W-9's twisted algebra".
> R = Ô[x]/(φ) = Ô[θ] is the NON-MAXIMAL order O[θ] at genre F for
> every k ≥ 1 and at genre E for every h ≥ 3. Witnesses: (Codex's, at
> this note's own A2 key φ = x² + 2x + 4 over ℤ₂) R/2R ≅ F₂[ε]/(ε²),
> not F₄ — R has nilpotents mod 2, its maximal-ideal residue field is
> F₂, and θ/2 (which generates the integral closure) is not in R;
> (the fold note's, genre E h ≥ 3) m_R = (π, θ) is non-principal: a
> generator γ would have v(γ) ∈ ℤ ∪ (h/2 + ℤ); at v(γ) = 1,
> θ/γ = c + dθ would need v(c) = h/2 − 1 ∉ ℤ, impossible, and at
> v(γ) = h/2, π/γ has v = 1 − h/2 < 0. R = O_L holds exactly at
> genre E, h = 1 (the Eisenstein case) — nowhere else in this note's
> range (F entries have k ≥ 1).
>
> **The restated frame (where every consumed fact is true).** Let
> L := Frac(R) = base(θ) — φ is irreducible over the base in both
> genres (E: the one-side polygon; F: the residual ψ irreducible) —
> and O_L its valuation ring, which IS a complete DVR. Define
> **v := v_L restricted** (normalized on the base) and read every
> residue in O_L/m_L. Then, exactly as S2.1's bullets display:
> genre E: e(L/base) = 2, f = 1, v(θ) = h/2, value group ½ℤ,
> O_L/m_L = F_q, res(θ²π^{−h}) = z; genre F: e = 1, f = 2, v(θ) = k,
> value group ℤ, O_L/m_L = F_{q²} = F_q(ȳ), res(θπ^{−k}) = ȳ a root
> of ψ. The gr sentence re-aims at **gr(O_L)** (one K-line per
> dv-height — W-9's twisted algebra); R ⊆ O_L, and every graded READ
> the note performs (the leading digit of an evaluated element at its
> v-height) happens in gr(O_L).
>
> **Consumption audit (why nothing downstream moves).** The note never
> uses R's ring-theoretic structure — it uses only v(A(θ)) and
> res(A(θ)/normalizer) of EVALUATED elements A(θ) ∈ O[θ] ⊆ O_L:
> GENH4-2's ultrametric/parity proof, S3's twisted-normalizer
> residues, S5's carry computation, S7's resolvent chain, and S0's
> DULEMMA disclosure (which needs only v's multiplicativity — true
> for v_L) all run in L/O_L verbatim; the censuses and count laws are
> digit-coordinate counts on O[x]-coefficients and never touch R at
> all. No count, no σ conclusion, no density moves. RIDERED (named
> exactly, not edited): S2.1's E bullet's "R is a complete DVR",
> S2.1's F bullet's "R is an unramified-over-the-ladder DVR", and
> S2.1's "R's associated graded IS …" sentence — each read with
> R's v/residue/graded data interpreted as O_L's, per this erratum.”

**CONDITIONALITY:** **A literally false carrier claim, with two explicit witnesses, and a consumption audit showing nothing downstream moves.** Its audit sentence is itself riddered at R2.REM (`.37`): S7's Y-trichotomy “runs in the quartic root field base(θ_F), not in L = Frac(R)”.
**SUPERSESSION KIND:** `provenance-rider` on three named sentences (the carrier is re-homed; no datum changes).
**TARGETS:** shard 1 `.14` (three sentences), and by audit `.19`, `.20`, `.23`, `.28`, `.05`.
**ARITHMETIC AUDIT:** both witnesses re-derived at shard 1 `.14` ✓ (`R/2R ≅ F₂[ε]/(ε²)` from `θ² ≡ 0 mod 2`; the non-principality valuation argument). `R = O_L` exactly at genre E `h = 1` ✓ (Eisenstein).
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1720–1765. correction sites: 2092–2099 (R2.REM Remark 1).
**TEETH:** NONE — a frame erratum; **`decorrelated-model audit`** is the finding's disposition.

---

### EFF.GENH4.s2of2.22  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R3's queued transport obligation). verbatim, lines 1767–1772.

> “**Transport obligation, QUEUED (not executed here).** GENHN.A(i)
> states the same "stage ring is a DVR with residue field F_{q^{f₁}}"
> sentence at general (e₁, f₁); the same carrier-rename erratum is
> OWED TO THE LIVE GENHN ARC and is hereby queued for GENHN's own
> ratification round — one rider of exactly this R3 form at
> GENHN.A(i), with the non-maximality witnesses transported.”

**CONDITIONALITY:** **An outbound erratum, QUEUED and not landed** — header predicate B's second governing quote. **Cross-note check: GENIND's §S9.3 GENHN bullet records exactly this as one of three queued GENHN errata (“A(i) transport ← Codex-GENH4 F3”), and GENIND's dated supplier-movement record then reports E3 EXECUTED @ `46bf675`** (GENIND shard 3 `.26`) — **so the queued obligation WAS discharged at the source, and GENH4 (frozen) does not record it.**
**SUPERSESSION KIND:** none of GENH4's own; an outbound queued erratum.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1767–1772. correction sites: none here; discharged externally at GENHN `46bf675` (recorded in GENIND shard 3).
**TEETH:** NONE.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(i)` — count **11**.

---

### EFF.GENH4.s2of2.23  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs with an ASCII table (R4 — the S7 units-normalization rider). verbatim, lines 1774–1801.

> “### R4 (CODEX F5): the S7 units-normalization rider (supersedes ANNEX A2's partial rider)
>
> **The defect.** S7 mixes valuation conventions inside one section:
> the opening display "v(A₁(θ)) = w/2, v(A₀(θ)) = u/2 EXACTLY" and
> the 2SIDED/INERT bullets ("v(Y) ∈ {w/2, (u−w)/2}"; "v(Y) = dμ/2")
> are E-halved forms, flatly contradicting the section's own
> declaration "genre F: w, u in v₁ = v units" — while the RAM
> bullet's F-leg "v(Y) = u/2" is ALREADY a true-unit statement
> (u odd, so u/2 half-integral: that is the ramification read).
> ANNEX A2 repaired only the norm tag between them.
>
> **The rider (one normalization sentence + the F table).** ALL
> displayed valuation equations in S7's trichotomy bullets are stated
> in genre E's halved (dv/2) units; their genre-F true-unit
> (v₁ = v) instances are:
>
>     opening:  v(A₁(θ)) = w,  v(A₀(θ)) = u
>     RAM:      v(Y) = u/2            (as displayed -- already true-unit)
>     2SIDED:   v(Y) ∈ {w, u−w}
>     INERT:    v(Y) = dμ, normalizer n₂ = π^{dμ}
>
> Every σ conclusion is invariant under the rescaling: polygon shapes,
> parities, and denominator reads are scale-blind; the INERT residue
> step is computed against n₂ = π^{dμ} (S3), correct in true units;
> the 2SIDED norm balance is A2's analysis, whose halved and unhalved
> forms give the same j = 2. Same defect species as A2's norm tag,
> which PE5 graded MINOR; this rider covers all three sentences at
> once and supersedes A2's partial one.”

`[TABLE]` — the genre-F true-unit instances (rule 14's second emission):

| S7 display | E-halved form (as displayed) | Genre-F true-unit instance |
|---|---|---|
| opening | `v(A₁(θ)) = w/2`, `v(A₀(θ)) = u/2` | `v(A₁(θ)) = w`, `v(A₀(θ)) = u` |
| RAM | `v(Y) = u/2` | `v(Y) = u/2` (already true-unit) |
| 2SIDED | `v(Y) ∈ {w/2, (u−w)/2}` | `v(Y) ∈ {w, u−w}` |
| INERT | `v(Y) = dμ/2` | `v(Y) = dμ`, `n₂ = π^{dμ}` |

**CONDITIONALITY:** **A rider that supersedes an earlier rider** — the only such case in this queue. Its scope-invariance claim (“Every σ conclusion is invariant under the rescaling”) is what keeps `.11`'s dictionary intact.
**SUPERSESSION KIND:** `replacement` (of A2's partial rider) + `wording-rider` (on all of S7's displays).
**TARGETS:** shard 1 `.28`, `.29`, `.31`, `.32`; supersedes `s2of2.07`.
**ARITHMETIC AUDIT:** the RAM F-leg `v(Y) = u/2` is already true-unit because `u` odd makes `u/2` half-integral, which IS the ramification read ✓ — **the one bullet that needed no rescaling, correctly identified.** Scale-invariance: multiplying all valuations by 2 preserves polygon shapes, denominators and parities ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1774–1801. correction sites: none.
**TEETH:** NONE — a normalization rider; `.09`'s committed instance is its nearest tie.

---

### EFF.GENH4.s2of2.24  [table]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs with a **fixed-width six-key partition table** (R5 — “law keys” defined and the pre2 remainder displayed), emitted TWICE per rule 14. verbatim, lines 1803–1839.

> “### R5 (CODEX F1): "law keys" defined + the pre2 row's full six-key partition displayed
>
> **The defect.** P-2 ("481 law-key checks") and P-3 ("law keys
> EXACTLY {…}") use the term "law keys" WITHOUT DEFINITION and
> display no remainder, inviting the partition misreading the
> verifier made (summing the four displayed keys to 655,360 ≠ 2²⁰ and
> filing a census contradiction).
>
> **The definition.** "Law keys" = the keys of kind in the sealed
> runner's `LAW_KINDS = ('RAM4', 'G2', 'FULL', 'SUB', 'E', 'F')`
> (genh4_checks.py line 299) — the kinds whose counts this note's S6
> laws predict and `cmp_tables` compares. Non-law kinds (the order-1
> strata: vertices and order-1 tails, tied instead through the W-12.A
> transcription in GH-JSONTIE) are counted in the same tables but are
> not "law keys".
>
> **The full pre2 partition (committed row, machine C1).** The
> committed `genh4_checks_results.json` pre2 row (Zp,2,11,pre=(1,2))
> partitions its 2²⁰ = 1,048,576 members EXACTLY into SIX keys:
>
>     RAM4(9)                    = 524,288   (law kind)
>     G2(5,'2')                  =  65,536   (law kind)
>     E-RAM(21)                  =  32,768   (law kind)
>     E-UND                      =  32,768   (law kind)
>     VTX((0,10),(1,7),(4,0))    = 131,072   = 2^17  (non-law: vertex)
>     L1TAIL                     = 262,144   = 2^18  (non-law: order-1
>                                                     B0-hidden tail)
>     Σ                          = 1,048,576 = 2^20  EXACT
>
> P-3's sentence displayed the four law-kind keys, exactly right as a
> law-key statement; the remainder 393,216 is the two non-law strata,
> both FORCED by the pre2 floored box (chain (1,2): floors
> v(B_j) ≥ 9, 7, 5, 3; free digits 2+4+6+8 = 20): the two-side vertex
> v(B₀) = 10 exact ∧ v(B₁) = 7 exact prices 1·2³·2⁶·2⁸ = 2¹⁷, and
> the B₀-hidden level-1 tail v(B₀) ≥ 11 prices 2^{4+6+8} = 2¹⁸ —
> hand-derived in the fold note and machine-tied here (C1). No census
> contradiction; no machine number was ever wrong.”

`[TABLE]` — the pre2 six-key partition (rule 14's second emission):

| Key | Count | Kind |
|---|---|---|
| `RAM4(9)` | 524,288 = 2¹⁹ | law |
| `G2(5,'2')` | 65,536 = 2¹⁶ | law |
| `E-RAM(21)` | 32,768 = 2¹⁵ | law |
| `E-UND` | 32,768 = 2¹⁵ | law |
| `VTX((0,10),(1,7),(4,0))` | 131,072 = 2¹⁷ | non-law (vertex) |
| `L1TAIL` | 262,144 = 2¹⁸ | non-law (order-1 B₀-hidden tail) |
| **Σ** | **1,048,576 = 2²⁰** | **EXACT** |

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `524,288 + 65,536 + 32,768 + 32,768 + 131,072 + 262,144 = 1,048,576 = 2²⁰` ✓ **exact.** The four law keys sum to `655,360` ✓ = the verifier's figure ✓, and the remainder `1,048,576 − 655,360 = 393,216 = 2¹⁷ + 2¹⁸` ✓ **exact.** The floored box: chain `(1,2)` gives floors `v(B_j) ≥ 9, 7, 5, 3` for `j = 0,1,2,3`, so free digits `(11−9) + (11−7) + (11−5) + (11−3) = 2+4+6+8 = 20` ✓ **exact.** The vertex pricing `1·2³·2⁶·2⁸ = 2¹⁷` ✓ (B₀ and B₁ pinned exact, B₂ and B₃ free at 6 and 8, plus 3 from B₁'s freedom above 7 — consistent with the displayed factors) ✓. The tail pricing `2^{4+6+8} = 2¹⁸` ✓. **Every number in the partition reproduces.**

**CONDITIONALITY:** **A CRITICAL flag REFUTED against the committed artifact, surviving only as an undefined term.** The definition is pinned to a source line (`genh4_checks.py line 299`).
**SUPERSESSION KIND:** `inventory completion` (a definition and a remainder supplied; no number moves).
**TARGETS:** shard 1 `.62`.
**DERIVATION:** Displayed + machine-tied at C1.
**RESOLUTION TRACE:** statement lines 1803–1839. correction sites: none.
**TEETH:** the annex-R leg's C1, tying the committed row.

---

### EFF.GENH4.s2of2.25  [scope-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R6 — the `(GENH4-2)` cite's scope). verbatim, lines 1841–1848.

> “### R6 (noted, the fold queue's R5): the "(GENH4-2)" cite at the key's own roots
>
> S7's 2SIDED bullet cites "(GENH4-2) at the key's own roots η".
> GENH4-2 is stated for development coordinates; its PROOF applies
> verbatim at any θ with the two facts S7 displays ((E) v(η) = h/2;
> (F) v(η) = k with res(ηπ^{−k}) a root of ψ) — the cite is to the
> proof, not the stated scope. Half-line closure of the
> orchestrator's own noted nit; no consumer moves.”

**CONDITIONALITY:** A scope license. **Note the provenance: “the orchestrator's own noted nit”, i.e. a finding neither the verifier nor a run produced.**
**SUPERSESSION KIND:** `license` (a cite is licensed beyond a lemma's stated scope, with the reason).
**TARGETS:** shard 1 `.19`, `.29`.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1841–1848. correction sites: 2092–2099 (R2.REM Remark 1 cites it).
**TEETH:** NONE.

---

### EFF.GENH4.s2of2.26  [changes-record] · **SERIES GENH4-BOX-1, entry 2 of 3 (post-ratification)**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1850–1868.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09, post-
> ratification).** Continuing the [r1]/[r2]/[r3]/PE4/PE5 record under
> the acceptance freeze: **the Codex ratification pass HAS NOW RUN
> (CODEX_GENH4RAT_2026-08-09.md, gpt-5.6-sol at HIGH, fresh context) —
> outcome CHALLENGE: 5 findings, adjudicated 1 REFUTED-as-classified
> (F1 → MINOR display), 2 GAP (F2 consumed-clause on the
> post-acceptance ANNEX PE5's GENH4-7; F3 frame), 1 GAP scoped to the
> unconsumed clause (c) (F4), 1 MINOR (F5). The ACCEPTED 2/2 grade
> stands ANNOTATED by the fold note pending Asvin's read; THIS ANNEX R
> applies the full repair queue R1–R5 (+ the noted R6): GENH4-7'
> re-proves the W-12.D F-SPLTAIL supply over the true leaf (the free
> boundary band), with the k ≥ 2 slice machine-exercised for the
> FIRST time (genh4annexr_supp.py: GREEN, 0 violations; 96/96 char-0
> PARI σ + 96/96 char-p root-count σ + 24,576 members enumerated +
> teeth 4/4). Any future hostile pass on this note attacks the
> post-ANNEX-R text; ANNEX R itself has NOT been through a hostile
> pass. Conditionality is otherwise unchanged: exactly the S11
> arc-grade stack, plus the GENHN.A(i) transport erratum QUEUED to
> the live GENHN arc (R3).**”

**CONDITIONALITY:** **“The ACCEPTED 2/2 grade stands ANNOTATED by the fold note pending Asvin's read”** — an acceptance neither revoked nor clean, awaiting an owner decision. **This is OPEN-CALL 1's object.**
**SUPERSESSION KIND:** `as-of scoping` on the acceptance (annotated, not revoked).
**TARGETS:** shard 1 `.01`; `s2of2.12`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1850–1868. correction sites: 2105–2127 (entry 3).
**TEETH:** `.18`.

---

### EFF.GENH4.s2of2.27  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 2 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1870–1884.

> “**What does not move (ANNEX R).** Every displayed statement, proof,
> and frozen number of the accepted body and of ANNEX PE5's A1–A4
> except the three rider targets named in R3/R4 and GENH4-7's
> hypothesis sentence (superseded by GENH4-7', conclusion identical);
> the sealed runner and all committed artifacts (md5 pins re-verified,
> C0); every committed key count incl. the pre2 six-key partition (R5
> displays it, C1 machine-ties it); THEOREM GENH4.A/B and the count
> laws (the free band was always priced — deep0 in `law_F` and S6.3
> from the seal); THEOREM GENH4.C's dictionary and the W-12.D supply
> (the label was always right; R1 widens the PROOF's stated family to
> the counted one); the eleven densities, the triple tie, and the S11
> conditionality stack; GENH4-BOX-2 (n = 5's embedded CS genres stay
> OPEN). The E-side displays are exact as written throughout — every
> ANNEX R item is genre-F (R1/R2), frame (R3), units (R4), or display
> (R5/R6) scope.”

**CONDITIONALITY:** **An enumerated non-movement declaration with an exception list of exactly four items.** Its closing taxonomy — every item is genre-F, frame, units or display — is the layer's own scope proof.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1870–1884. correction sites: none.
**TEETH:** NONE.

---
### EFF.GENH4.s2of2.28  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R2's provenance — the first annex hostile pass). verbatim, lines 1886–1907.

> “## ANNEX R2 (2026-08-09, post-annex-pass-1)
>
> **Provenance and scope.** The first hostile annex pass
> (`GENH4_annexpass_report.md`, commits 6cb147b → fed3cff → a8dec16,
> fresh context, quote-and-classify) returned **NOT CLEAN at annex
> scope: 0 CRITICAL + 1 GAP + 4 MINOR + 2 remarks** — the
> annex-acceptance count stays 0/2. The GAP (GAP-1) machine-refutes
> ANNEX R's R2 clause-(c) witnesses at band-pinned strata; the
> consumed surface (GENH4-7'(b), the W-12.D F-SPLTAIL supply) survived
> the pass's full hostile re-derivation plus two fresh cells. This
> annex lands the owed repairs. The body + ANNEX PE5 + ANNEX R above
> are BYTE-FROZEN: md5 `863c21600fa48ae755d0d87b77b894d4`
> (113,738 bytes, identical to the HEAD blob at ca3754d) verified
> before and after this append; nothing above this section's first
> line is edited — every repair names its exact target. Machine
> support: the annex-pass fresh leg
> `verification/openmath/genh4annexpass_fresh.py` (md5 `f044c491…`,
> output `bf8f94f5…`, results `71535780…`, committed at fed3cff;
> GREEN, 0 violations) — its FR4/FR5 checks are the adjudication legs
> cited below; no new computation was needed. Honesty of grade: ANNEX
> R2 itself has NOT been through a hostile pass; annex pass #2 attacks
> the post-R2 text and attempts the stack's first clean mark.”

**CONDITIONALITY:** **The consumed surface SURVIVED a full hostile re-derivation plus two fresh cells; what fell was the unconsumed cap-sharpness clause.** That separation — consumed survives, unconsumed falls — is the pass's most important structural result. **The results md5 `71535780…` is corrected to `7153578c…` by the post-annex-pass-2 MINOR-1** (`.41`).

**SUPERSESSION KIND:** none of its own (a provenance record); establishes freeze predicate 3.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1886–1907. correction sites: 2152–2158 (MINOR-1, the pin transcription).
**TEETH:** `in-house hostile pass` at annex scope, with a committed fresh leg.
**PIN VERIFICATION:** `6cb147b` ✓, `fed3cff` ✓, `a8dec16` ✓, `ca3754d` ✓; `verification/openmath/genh4annexpass_fresh.py` ✓ (+ output ✓, results ✓) EXIST; `lean/notes/openmath/GENH4_annexpass_report.md` — **verified to EXIST ✓.**

---

### EFF.GENH4.s2of2.29  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with two quoted refuted displays and the machine refutation (R2.G1's finding half). verbatim, lines 1909–1936.

> “### R2.G1 (GAP-1): the N-even band-pinned leg and the refine-deeper leg of R2 are WITHDRAWN — machine-refuted; clause (c) restated at the key level
>
> **The refuted displays, quoted.** R2's N-even dμ < w bullet claimed,
> at band-pinned strata with m ≤ 2w:
>
> > "u = N residual read at depth dμ < w (S₁-slot 0): char ≠ 2 decided
> > ≠ {(2,2)} as above; char 2: '1sq' → one refine step."
>
> and the refine-deeper leg claimed:
>
> > "LEMMA GENH4-4 maps the refine locus ONTO the floored fresh node
> > {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁}, whose digits are free lift
> > digits; realize the fresh leaf dv(A₁′) = dμ₁+1 =: w′,
> > dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ …: a fresh 2SIDED′(w′, w′+1) for
> > every such lift, σ = {(1,2),(1,2)} … Clause (c) is thereby
> > re-established at the key level in every stratum."
>
> Both are FALSE as within-stratum claims. Machine (FR4): at
> (q,N,k) = (2,10,2), UND key, band-pinned stratum m = 11, w = 7,
> dμ = 5 < w — squarely inside the quoted bullet — the 6 refine-path
> u = 10 lifts read PARI σ = {(2,2)} on 6/6 against the displayed
> fresh 2SIDED′(6,7) σ = {(1,2),(1,2)}; all 24 band-pinned lifts
> across (2,8,2) and (2,10,2) read {(2,2)} — those two strata are
> σ-CONSTANT, with no within-stratum differing pair at all. At
> (2,8,2) (N = 8 ≤ 4k) the quoted "u = N residual read" does not even
> exist: both height-8 components sit below the GENH4-1F entry
> budgets (b₀@8 < v(β₀) ≥ 4k+1 = 9; b₁@6 < v(β₁) ≥ 3k+1 = 7), so
> every in-family lift has u = 9 = m → RAM(9) → {(2,2)}.”

**CONDITIONALITY:** **A MACHINE REFUTATION of a displayed annex argument, with PARI σ on 6/6 and 24/24.** The two strata are σ-CONSTANT — not merely un-witnessed but provably without a within-stratum differing pair.

**ARITHMETIC AUDIT (compiler-computed):** at `(2,8,2)`: `v(β₀) ≥ 4k+1 = 9` ✓ and `v(β₁) ≥ 3k+1 = 7` ✓ (shard 1 `.15`'s budgets), so the height-8 letter's components sit at a₀-position 8 `< 9` ✓ and a₁-position `8−k = 6 < 7` ✓ — **both below budget, so the height-8 slot is structurally zero** ✓ and `u = 9 = m` ✓ → odd, `≤ 2w` → RAM(9) → `{(2,2)}` ✓. At `(2,10,2)`: `m = 11`, `w = 7`, `2w = 14 ≥ m` ✓ so GENH4-7′(a)'s cap `u_lift ≤ m = 11 < 14` holds ✓ — **no lift reaches `u > 2w`** ✓, exactly the refutation.

**DERIVATION:** Not a mathematical unit; a refutation with machine legs.
**RESOLUTION TRACE:** statement lines 1909–1936. correction sites: none.
**TEETH:** **FR4** — PARI σ 6/6 and 24/24; a **`decorrelated-model audit` executed as a machine refutation**, the strongest combination in the queue.

---

### EFF.GENH4.s2of2.30  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R2.G1's transport-error diagnosis). verbatim, lines 1938–1956.

> “**Why the within-stratum route cannot work (the transport error,
> displayed).** GENH4-4's onto-the-fresh-node statement quantifies
> over the FULL refine slice — all in-window digits free. On a FIXED
> member only LIFT digits vary, and neither fresh coordinate is free:
>
> * **dv(A₁′) is FORCED, not free.** In equal characteristic the
>   '1sq' root s₁ = √S₀ lies in F_q, the refine carry C = 0 and the
>   2w_re term dies: dv(A₁′) = w. In mixed characteristic the +2w_re
>   revival forces dv(A₁′) = dμ+1. Either way the A₁′ string is
>   key-pinned, never at the display's free disposal.
> * **dv(A₀′) is CAPPED by the surviving band letter.** The height-m
>   band letter's ȳ-component d₁ ≠ 0 survives the refine
>   substitution: at (2,10,2), λ = ŝ²π¹⁰ + ŝπ⁵A₁ contributes the
>   height-10 kill plus terms at heights ≥ 12 only — no correction
>   reaches height 11 — so dv(A₀′) = 11 is forced; 11 odd ≤ 2w →
>   RAM(11) → σ = {(2,2)}, exactly the FR4 read. Wherever the band
>   caps u′ ≤ m < 2dμ+3, the displayed fresh leaf dv(A₀′) = 2dμ+3 is
>   unrealizable in both characteristics.”

**CONDITIONALITY:** **A quantifier-transport error named precisely: a full-slice ONTO statement applied to a fixed member.** This is the same species of error the corpus has now seen three times (GENIND's `M★ < N` from a lower bound; GENIND's ONTO-without-unit-pivots; here). **LEMMA GENH4-4 itself is untouched** (shard 1 `.09`).
**ARITHMETIC AUDIT:** at `(2,10,2)`, `dμ = 5`, so the displayed fresh leaf would need `dv(A₀′) = 2dμ+3 = 13`, but the band caps `u′ ≤ m = 11 < 13` ✓ — **unrealizable** ✓. And `11` odd `≤ 2w = 14` → RAM(11) → `{(2,2)}` ✓ matching FR4 ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1938–1956. correction sites: none.
**TEETH:** FR4.

---

### EFF.GENH4.s2of2.31  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, GENH4-7′(c′)) + proof. verbatim, lines 1957–1999.

> “> **(c′)** If 2w ≥ N, NO single label is lift-sound for the leaf
> > KEY. Witnesses live at the key's band-zero members — which every
> > leaf key contains (deep0's band sweep includes the zero value; at
> > k = 1 the whole key is band-zero) — and are shape-only where
> > 2w > N:
> > (i) if 2w > N: let u₀ := the least odd height ≥ max(N, 4k+1);
> > then u₀ ≤ 2w (N odd ≥ 4k+1: u₀ = N ≤ 2w; N even ≥ 4k+2:
> > u₀ = N+1 ≤ 2w since 2w > N with both even; N ≤ 4k: u₀ = 4k+1
> > ≤ 2w−1 since w ≥ 2k+1, S2.3), and the two lifts of one band-zero
> > member — the a₀ digit at height u₀ alone (u = u₀ odd ≤ 2w →
> > RAM(u₀) → σ = {(2,2)}) and the a₀ digit at height 2w+1 alone
> > (u = 2w+1 > 2w → 2SIDED(w, w+1) → σ = {(1,2),(1,2)}) — differ,
> > both characteristics, no residual read consulted;
> > (ii) if 2w = N: a u > 2w lift (2SIDED, σ = {(1,2),(1,2)}) against
> > an inert continuation at the separable u = 2w read (σ = {(1,4)})
> > at SOME member of the key — existence by the completed coset
> > count (R2.M2 below) in char odd and by R2's trace argument
> > (pass-verified sound, R2.REM) in char 2.
> > NO within-stratum pair is claimed at band-pinned strata with
> > m ≤ 2w: such strata can be σ-constant (the FR4 pair of strata
> > read {(2,2)} on 24/24), and the key-level conclusion rides the
> > band-zero stratum of the same key — cross-stratum contrast, which
> > is what cap-uniqueness consumes.”

**CONDITIONALITY:** **The repaired clause, at KEY level with band-zero witnesses and an explicit non-claim at band-pinned strata.** Its `(i)` leg is **shape-only** (“no residual read consulted”), which is what makes it characteristic-blind; its `(ii)` leg needs an existence input supplied by M2 (char odd) and R2's trace argument (char 2, pass-verified). **UNCONSUMED — see `.32`.** Its proof's disc parenthetical is corrected by the post-annex-pass-2 MINOR-2 (`.42`).

**SUPERSESSION KIND:** `replacement` of clause (c) and of R2's per-stratum witness display.
**TARGETS:** `s2of2.04`(c), `s2of2.19`.

**ARITHMETIC AUDIT (compiler-computed, on (i)'s three cases):** `N odd ≥ 4k+1`: `u₀ = N` and `2w ≥ N` gives `u₀ ≤ 2w` ✓. `N even ≥ 4k+2`: `u₀ = N+1`; with `2w > N` and both `2w, N` even, `2w ≥ N+2 > N+1 = u₀` ✓. `N ≤ 4k`: `u₀ = 4k+1`, and `w ≥ 2k+1` gives `2w ≥ 4k+2 = u₀+1`, so `u₀ ≤ 2w−1` ✓. **All three sub-cases exact.** The two lifts: `u = u₀` odd `≤ 2w` → RAM → `{(2,2)}` ✓; `u = 2w+1 > 2w` → 2SIDED(w, w+1) → `{(1,2),(1,2)}` ✓ — **and `2w+1` is realizable at a band-zero member because the a₀ lift digits are free above N** ✓.

**DERIVATION:** verbatim, lines 1985–1999 (quoted in the source; its key steps: band-zero existence from deep0's sweep, u-geography from GENH4-7′(a) with M1's correction, the two legs from S7's RAM and 2SIDED bullets, and disc ≠ 0 at both witnesses).

**RESOLUTION TRACE:** statement lines 1957–1999. correction sites: 2033–2059 (M2 supplies (ii)'s char-odd input), 2100–2103 (R2.REM verifies (ii)'s char-2 input), 2159–2167 (MINOR-2 corrects the disc parenthetical).
**TEETH:** FR4 (24/24 band-pinned σ-constant) + FR5 at `(2,9,2)` (9/9, both sides at one band-pinned stratum with `m = 2w`) — **the machine-confirmed instance pattern is displayed at `.32`.**

---

### EFF.GENH4.s2of2.32  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.G1's consumption status). verbatim, lines 2001–2011.

> “**Consumption status (unchanged).** Clause (c)/(c′) is UNCONSUMED:
> W-12.D's supply row consumes clause (b) only (S11 firing table;
> re-verified by the annex pass's charge 4), and the reader's UND
> exit at 2w ≥ N is conservative-sound regardless — no consumer moves
> under this correction. The honest-scope sentence of R2's 2w = N leg
> (τ-degenerate members; key granularity) carries over to (c′)
> verbatim. The machine-confirmed instance pattern of (c′): at the
> two FR4 cells the {(2,2)} side is carried by the band-pinned strata
> (24/24) and the {(1,2),(1,2)} side by band-zero members of the same
> keys (6/6 at each cell); at the FR5 cell (2,9,2) both sides live at
> one band-pinned stratum with m = 2w (9/9).”

**CONDITIONALITY:** **The containment sentence: a machine-refuted annex argument moves no consumer, because the consumed clause is (b) and the refuted one was (c).** Re-verified independently by the pass's charge 4. **The “(6/6 at each cell)” figure is corrected by the post-annex-pass-2 MINOR-3 to “6/6 TOTAL, 3 per cell”** (`.43`).
**SUPERSESSION KIND:** none of its own; a status declaration. Receives a `provenance-rider` at MINOR-3.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2001–2011. correction sites: 2168–2173 (MINOR-3).
**TEETH:** FR4 + FR5.

---

### EFF.GENH4.s2of2.33  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M1 — realizability scoped). verbatim, lines 2013–2031.

> “### R2.M1 (MINOR-1): GENH4-7'(a)'s realizability parenthetical scoped to N ≥ 4k+1
>
> Quoted targets: "u_lift = N realizable (the a₀ lift digit at
> position N)" (7'(a)) and "u_lift sweeps {N, N+1, …} at a band-zero
> state" (R2). Corrected: **u_lift = N is realizable WHEN
> N ≥ 4k+1** (the a₀ lift digit at position N is then inside
> GENH4-1F's entry budget v(β₀) ≥ 4k+1); at hidden states with
> N ≤ 4k (nonempty: the UND leaves at (2,8,2)) the height-N letter is
> structurally zero — both components sit below the budgets (the a₀
> component at N < 4k+1, the a₁ component at N−k < 3k+1) — and the
> sweep starts at max(N, 4k+1). R2's u-geography sentences read
> correspondingly: {max(N, 4k+1), max(N, 4k+1)+1, …} at a band-zero
> state and {max(N, 4k+1), …, m} at a band-pinned state. The FLOOR
> half of (a) (u_lift ≥ N, every band completion, every lift) is
> untouched. **Clause (b) is unaffected**: SPLTAIL forces N ≥ 4k+3
> (2w < N with w ≥ 2k+1, S2.3), so position N is in budget throughout
> (b)'s geography — realizability there is exercised at the committed
> and annex-pass cells (u = N lifts at (2,11,2), (2,15,3), (3,11,2):
> C5/FR2A/FR2B).”

**CONDITIONALITY:** **A realizability claim scoped to the entry budget, with (b) explicitly unaffected because SPLTAIL forces a stronger floor.** The floor half of (a) — the one (b) uses — is untouched.
**SUPERSESSION KIND:** `scope-pin`.
**TARGETS:** `s2of2.04`(a), `s2of2.16`(a), `s2of2.19`.
**ARITHMETIC AUDIT:** SPLTAIL forces `2w < N` with `w ≥ 2k+1` ⟹ `N > 4k+2` ⟹ `N ≥ 4k+3 > 4k+1` ✓ — **(b)'s geography is always in budget** ✓. At `(2,8,2)`: `N = 8 ≤ 4k = 8` ✓ so the height-N letter is structurally zero ✓ (a₀ at `8 < 9` ✓, a₁ at `6 < 7` ✓) — matching `.29`'s independent derivation ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2013–2031. correction sites: none.
**TEETH:** C5, FR2A, FR2B (u = N lifts at three cells including the first `k = 3` and first odd-q `k ≥ 2` cells).

---

### EFF.GENH4.s2of2.34  [lemma]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M2 — the char-odd coset count completed). verbatim, lines 2033–2059.

> “### R2.M2 (MINOR-2): the 2w = N char-odd existence — the coset count completed
>
> Quoted target (R2, 2w = N, char odd): "if for EVERY square s and
> every d₀ the value s/4 − c·d₀ were a square, the set
> (squares ∪ {0}) of size (q²+1)/2 would be a union of full affine
> lines in direction c, each of size q — impossible since
> q ∤ (q²+1)/2." The negation of inert-existence covers only the
> cosets through the REALIZABLE s = S₁²/4 — the NONZERO squares (the
> pin letter is ≠ 0) — so the coset through 0 is not
> hypothesis-covered, and "union of FULL affine lines" of
> squares ∪ {0} has a half-step gap. Completed by the count route
> (adopted over the pass's alternative c = 1 route because it needs
> no input about the twist unit c): let Sq := the nonzero squares of
> F_{q²}, |Sq| = (q²−1)/2. Suppose no member of the key has an inert
> continuation at u = 2w: then for every S₁ ∈ F_{q²}^× and every
> d₀ ∈ F_q, S₁²/4 − c·d₀ is a square or zero. As S₁ sweeps F_{q²}^×,
> s := S₁²/4 sweeps Sq exactly (squaring is 2-to-1 onto Sq; 4 is a
> nonzero square, char odd), so every coset of the F_q-line c·F_q
> that meets Sq is contained in Sq ∪ {0} (its d₀ = 0 point is s
> itself, trivially a square). The q cosets of c·F_q partition
> F_{q²}; let U := the union of the cosets meeting Sq. Then
> Sq ⊆ U ⊆ Sq ∪ {0} and q divides |U|. If 0 ∈ U then U = Sq ∪ {0}
> and q | (q²+1)/2 ≡ 2⁻¹ (mod q) — false; if 0 ∉ U then U = Sq and
> q | (q²−1)/2 ≡ −2⁻¹ (mod q) — false. Contradiction either way:
> inert-continuation members EXIST at 2w = N, char odd — (c′)(ii)'s
> odd-characteristic input. The conclusion of the old display held;
> the quantifier now matches the negation.”

**CONDITIONALITY:** **A quantifier gap in a counting argument, closed by a cleaner count.** The old argument's conclusion held; its negation was mis-covered.
**SUPERSESSION KIND:** `replacement` (of the line-partition display by a coset count).
**ARITHMETIC AUDIT (compiler-computed):** `|Sq| = (q²−1)/2` ✓. `F_{q²}` has `q²` elements and the `F_q`-line `c·F_q` has `q` elements, so there are `q` cosets ✓, each of size `q`, and `q | |U|` ✓. If `0 ∈ U`: `|U| = |Sq| + 1 = (q²−1)/2 + 1 = (q²+1)/2` ✓, and `(q²+1)/2 ≡ (0+1)/2 = 2⁻¹ (mod q)` ✓, which is a unit mod q, so `q ∤ |U|` ✓ **contradiction**. If `0 ∉ U`: `|U| = (q²−1)/2 ≡ −2⁻¹ (mod q)` ✓, again a unit ✓ **contradiction**. **The count is exact and both branches close** ✓. Also: squaring on `F_{q²}^×` is 2-to-1 onto `Sq` in odd characteristic ✓, and 4 is a nonzero square ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2033–2059. correction sites: none.
**TEETH:** NONE — a counting proof. Disposition: **PROOF-ONLY**, feeding (c′)(ii), which is itself UNCONSUMED.

---

### EFF.GENH4.s2of2.35  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M3 — the excluded-digit clause). verbatim, lines 2061–2077.

> “### R2.M3 (MINOR-3): the N-odd dμ₁ = w branch — the excluded-digit clause
>
> Quoted target (R2, N odd, band-pinned m ≤ 2w, dμ₁ = w): "the
> residual is separable in both characteristics, and any nonzero
> digit gives a decided '11'/'2' ≠ {(2,2)}." In char 2 this is exact
> (disc-analog = S₁ ≠ 0, every nonzero digit decided). In char odd,
> disc = S₁² − 4S₀ with S₀ = c·d₀ sweeping the line: disc = 0 ⟺
> d₀ = S₁²/(4c) — AT MOST ONE digit (realizable only when that value
> lies in F_q^×), and there the read is '1sq' (refine), not decided.
> The sentence reads corrected as: "…and any nonzero digit d₀ with
> c·d₀ ≠ S₁²/4 gives a decided '11'/'2' ≠ {(2,2)}; at most one digit
> is degenerate." Pair-existence survives at every odd q: char odd
> forces q ≥ 3, so among the q−1 ≥ 2 nonzero digits at least
> q−2 ≥ 1 is non-degenerate — the branch's differing pair (RAM(N)
> {(2,2)} vs a decided read) stands. The branch's machine instance
> (FR5 at (2,9,2), char 2: RAM(9) {(2,2)} vs decided
> {(1,2),(1,2)}/{(1,4)} on 9/9) sits on the exact side of the split.”

**CONDITIONALITY:** **An over-strong “any nonzero digit” corrected to “any non-degenerate nonzero digit”, with pair-existence preserved by a counting margin.**
**SUPERSESSION KIND:** `replacement` (a quantifier narrowed, with the corrected sentence displayed).
**ARITHMETIC AUDIT:** `disc = S₁² − 4S₀ = 0 ⟺ S₀ = S₁²/4 ⟺ c·d₀ = S₁²/4` ✓ — at most one `d₀` ✓. Odd q ⟹ `q ≥ 3` ⟹ `q−1 ≥ 2` nonzero digits, at least `q−2 ≥ 1` non-degenerate ✓ — **pair-existence survives at every odd q** ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2061–2077. correction sites: none.
**TEETH:** FR5 at `(2,9,2)`, 9/9 — **char 2, i.e. the side of the split where the original sentence was exact.**

---

### EFF.GENH4.s2of2.36  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M4 — the header inventory corrected). verbatim, lines 2079–2088.

> “### R2.M4 (MINOR-4): the GENH4-7' header's inventory corrected
>
> Quoted target: "(GENH4-7 with the leaf's true floor … replaces
> GENH4-7's hypothesis sentence and clause (a)'s parenthetical,
> everything else unchanged)." The header UNDER-INVENTORIES its own
> supersession; it reads corrected as: "(… replaces GENH4-7's
> hypothesis sentence and clause (a)'s parenthetical, ADDS to (a) the
> band-nonzero cap u_lift ≤ m, and REPLACES clause (c)'s proof — the
> old two-lift witnesses withdrawn, the re-proof now (c′) in ANNEX
> R2; clause (b)'s conclusion and consumption unchanged)."

**CONDITIONALITY:** **A supersession inventory that under-counted its own changes — the exact defect class this compilation's `SUPERSESSION KIND` and `TARGETS` fields exist to prevent.** The corrected inventory lists four items where the original listed two.
**SUPERSESSION KIND:** `inventory completion`.
**TARGETS:** `s2of2.16` (the header).
**ARITHMETIC AUDIT:** original inventory: 2 items (hypothesis sentence; (a)'s parenthetical). Corrected: 4 (those two + (a)'s band cap + (c)'s proof) ✓, with (b) explicitly unchanged ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2079–2088. correction sites: none.
**TEETH:** NONE — an inventory repair.

---

### EFF.GENH4.s2of2.37  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + two bulleted remarks (R2.REM). verbatim, lines 2090–2103.

> “### R2.REM (the two pass remarks, folded)
>
> * **Remark 1 (R3's consumption-audit sentence), ridered:** "S7's
>   resolvent chain … all run in L/O_L verbatim" is loose — S7's
>   Y-trichotomy runs in the quartic root field base(θ_F), not in
>   L = Frac(R); the facts consumed there are covered by S7's own
>   displayed transport ((F) v(θ) = k, res(θπ^{−k}) a root of ψ) plus
>   the R6 rider, while the genuinely L-resident part (the norm
>   identity over the key's roots) is covered as stated. No consumer
>   moves.
> * **Remark 2 (R2's char-2 trace argument at 2w = N):** re-derived
>   SOUND by the annex pass (trace transitivity, Frobenius sweep,
>   trace-kernel count); no edit owed — recorded so that (c′)(ii) can
>   cite it as pass-verified.”

**CONDITIONALITY:** **Remark 1 riders a rider's audit sentence — a third-order correction** (R3 audits the body; R2.REM audits R3's audit). **Remark 2 is a positive verification recorded so a later clause can cite it** — the corpus's cleanest instance of a pass certifying an argument rather than finding a defect.
**SUPERSESSION KIND:** Remark 1 = `scope-pin` on `s2of2.21`'s audit sentence; Remark 2 = none (a certification).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2090–2103. correction sites: none.
**TEETH:** Remark 2 IS a tooth of the AUDIT class (`in-house hostile pass`, positive result).

---

### EFF.GENH4.s2of2.38  [changes-record] · **SERIES GENH4-BOX-1, entry 3 of 3 (post-annex-pass-1)**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 2105–2127.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09,
> post-annex-pass-1).** Continuing the record: **the first hostile
> annex pass HAS NOW RUN (GENH4_annexpass_report.md, fresh context,
> commits 6cb147b/fed3cff/a8dec16) — outcome NOT CLEAN: 0 CRITICAL +
> 1 GAP + 4 MINOR + 2 remarks; the annex-acceptance count stays 0/2
> (pass #2 attempts the first clean). GAP-1 machine-refuted R2's
> N-even band-pinned and refine-deeper legs (FR4: the 6 refine-path
> lifts at (2,10,2) read {(2,2)} 6/6 against the displayed 2SIDED′;
> the (2,8,2) u = N read structurally unrealizable); THIS ANNEX R2
> withdraws both legs and restates clause (c) as (c′) at the key
> level (band-zero witnesses; cross-stratum contrast — the form the
> pass confirmed 6/6 + 6/6 at the same keys), and lands the four
> minors (realizability scoped to N ≥ 4k+1; the coset count
> completed; the excluded-digit clause; the header inventory) plus
> the Remark-1 rider. The consumed surface was independently
> RE-DERIVED CLEAN by the pass (GENH4-7'(b) + the supersession +
> R3/R4/R5 + PE5's A2/A3); both annex machine legs re-ran isolated
> GREEN (PE5 bit-identical, R elapsed-only); the pass's fresh leg
> exercised the first k = 3 cell (2,15,3) and the first odd-q k ≥ 2
> cell (3,11,2), 48/48 + 48/48 σ with teeth 4/4 and the 54-cell grid
> tie. The frozen body's ACCEPTED 2/2 is untouched; conditionality is
> otherwise exactly the S11 stack plus the queued GENHN.A(i)
> transport erratum (R3).**”

**CONDITIONALITY:** **The consumed surface was independently RE-DERIVED CLEAN by the pass** — the single most reassuring sentence in the annex stack, and the reason the machine refutation of (c) costs nothing downstream. **The frozen body's ACCEPTED 2/2 is untouched.**
**SUPERSESSION KIND:** `counter re-reading` (the annex-stack counter stays 0/2).
**ARITHMETIC AUDIT:** two new cells at 48/48 each ✓; the “6/6 + 6/6 at the same keys” is corrected to “6/6 TOTAL, 3 per cell” by MINOR-3 (`.43`) — **so this append's own figure is one of the three the next pass corrects.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2105–2127. correction sites: 2168–2173 (MINOR-3).
**TEETH:** the pass's fresh leg (first `k = 3`, first odd-q `k ≥ 2`, 54-cell grid tie, teeth 4/4).

---

### EFF.GENH4.s2of2.39  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 3 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 2129–2140.

> “**What does not move (ANNEX R2).** Every displayed statement,
> proof, and frozen number of the accepted body, ANNEX PE5, and ANNEX
> R except the five named targets (R2's two withdrawn legs → (c′);
> 7'(a)'s realizability parenthetical + R2's two u-geography
> sentences → R2.M1; R2's char-odd line-partition display → R2.M2;
> R2's dμ₁ = w separability sentence → R2.M3; the GENH4-7' header
> inventory → R2.M4) and the one rider (R2.REM Remark 1, on R3's
> audit sentence); ANNEX-LEMMA GENH4-7' clauses (a)-floor and (b) —
> their proofs and the W-12.D supply row are untouched by every item
> here; the sealed runner and all committed artifacts and pins; every
> committed key count and the eleven densities; GENH4-BOX-2 (n = 5's
> embedded CS genres stay OPEN).”

**CONDITIONALITY:** **Five named targets, one rider, and an explicit statement that (a)-floor and (b) — the consumed clauses — are untouched by every item.**
**ARITHMETIC AUDIT:** five targets enumerated ✓ (`.31`, `.33`, `.34`, `.35`, `.36`) + one rider ✓ (`.37`) — **six items, all emitted as units here** ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2129–2140. correction sites: none.
**TEETH:** NONE.

---

### EFF.GENH4.s2of2.40  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the post-annex-pass-2 corrections' frame). verbatim, lines 2142–2150.

> “### Dated corrections (2026-08-09, post-annex-pass-2)
>
> Provenance: the three MINORs of the annex-pass-2 verdict
> (GENH4_annexpass2_report.md, commit d6a9ac8 — 0 CRITICAL + 0 GAP +
> 3 MINOR at annex-stack scope; the stack's clean count HOLDS at 1/2
> through this minors-only round, the HE7-r3 precedent). Each
> one-liner names its exact display target above; byte-freeze
> verified: the pre-annex prefix (128,564 bytes, md5 `22b766d3…`) is
> byte-identical before == after this append.”

**CONDITIONALITY:** **The terminal state of the whole note: body ACCEPTED 2/2 (annotated); annex stack at 1/2 through a minors-only round.** “the stack's clean count HOLDS at 1/2 through this minors-only round, the HE7-r3 precedent” — **a minors-only round does not break a clean count**, by corpus precedent.
**SUPERSESSION KIND:** `counter re-reading` (the annex-stack counter 0/2 → 1/2).
**SERIES:** GENH4-BOX-1's terminal state (though this record is not itself a BOX-1 append).
**ARITHMETIC AUDIT:** three MINORs, three one-liners ✓ (`.41`, `.42`, `.43`).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2142–2150. correction sites: **none — this is the note's terminal text region.**
**TEETH:** `in-house hostile pass` at annex scope, CLEAN of GAPs.
**PIN VERIFICATION:** `d6a9ac8` ✓; `lean/notes/openmath/GENH4_annexpass2_report.md` — **verified to EXIST ✓**; `verification/openmath/genh4annexpass2_fresh.*` ✓ EXIST (3 files), **and `genh4annexpass3_fresh.*` ✓ also exist** — a third annex pass's leg, **cited nowhere in the note** (recorded, §8 defect 1).

---

### EFF.GENH4.s2of2.41  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-1 — a provenance pin transcription). verbatim, lines 2152–2158.

> “* **MINOR-1 (ANNEX R2 provenance pin).** R2's fresh-leg results pin
>   "results `71535780…`" reads for `7153578c…` — the committed
>   `genh4annexpass_fresh_results.json` has md5
>   `7153578c0948d773830f58c193dcb62d`, the blob at fed3cff (the
>   commit R2 cites) == HEAD with a single-commit history
>   (re-verified before this append): a transcription slip in the
>   displayed pin; the machine record is intact.”

**CONDITIONALITY:** **A one-character md5 transcription slip** — the same defect class GENIND's shard 2 `.58` records (`e5493312` → `e549331a`). **Two independent notes in this corpus have now had a quoted md5 prefix corrupted; the artifact never moved in either case.**
**SUPERSESSION KIND:** `provenance-rider` (a pin transcription; nothing about the artifact or any claim changes).
**TARGETS:** `s2of2.28`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2152–2158. correction sites: none.
**TEETH:** `arithmetic recount` at the byte level (a commit-time md5 re-verification), plus a blob-vs-HEAD check with a single-commit history.
**PIN VERIFICATION:** `fed3cff` ✓; `genh4annexpass_fresh_results.json` ✓ EXISTS.

---

### EFF.GENH4.s2of2.42  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-2 — the (c′) disc parenthetical in equal characteristic 2). verbatim, lines 2159–2167.

> “* **MINOR-2 ((c′) proof parenthetical).** (c′)(i)'s "disc ≠ 0 is
>   automatic at both witnesses (v(4A₀) = u + 2v(2) is odd either
>   characteristic, ≠ 2w = v(A₁²), so v(disc) < ∞)" fails in EQUAL
>   characteristic 2 (4A₀ = 0, so v(4A₀) = ∞, not odd); the
>   conclusion holds by the one-line route disc = A₁² − 4A₀ = A₁²
>   with v(disc) = 2w < ∞ (A₁ ≠ 0 since dv(A₁) = w is pinned finite)
>   — machine-confirmed by the pass's FAeq equal-char leg 4/4 (exact
>   F₂[t]-gcd disc ≠ 0 + Panayi roots on the F₂[[t]] witnesses at
>   (2,7,2) and (2,12,2)).”

**CONDITIONALITY:** **A characteristic-2 degeneration in a parenthetical, with the conclusion preserved by a one-line alternative route and machine-confirmed.**
**SUPERSESSION KIND:** `replacement` (of a proof parenthetical; the clause's conclusion is unchanged).
**TARGETS:** `s2of2.31`'s proof.
**ARITHMETIC AUDIT (compiler-computed):** in equal characteristic 2, `4 = 0` so `4A₀ = 0` and `v(4A₀) = ∞` ✓ — **the original parenthetical genuinely fails** ✓. The replacement: `disc = A₁² − 4A₀ = A₁²` in char 2 ✓, and `v(A₁²) = 2·v(A₁) = 2w < ∞` since `dv(A₁) = w` is a finite pin ✓ — **so `disc ≠ 0`** ✓. **Both the failure and the repair check.**
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2159–2167. correction sites: none.
**TEETH:** the pass's FAeq equal-char leg, 4/4, with exact `F₂[t]`-gcd and Panayi root counts at two cells.

---

### EFF.GENH4.s2of2.43  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-3 — a machine-instance count). verbatim, lines 2168–2173.

> “* **MINOR-3 (ANNEX R2 machine-instance count).** The
>   consumption-status sentence's "(6/6 at each cell)" reads for
>   "6/6 TOTAL, 3 per cell" — the committed fresh leg builds 3
>   band-zero contrast pins at (2,8,2) + 3 at (2,10,2); the substance
>   is intact ((c′) needs ≥ 1 contrast member per cell, and each of
>   the two FR4 cells carries 3/3).”

**CONDITIONALITY:** **A count overstated by a factor of two, with the substance preserved because the requirement is `≥ 1` per cell.** **This is the note's last word** (line 2173 is the file's last line).
**SUPERSESSION KIND:** `counter re-reading` (a machine-instance count corrected).
**TARGETS:** `s2of2.32`, `s2of2.38`.
**ARITHMETIC AUDIT:** `3 + 3 = 6` ✓ TOTAL, against the claimed `6` per cell (which would be 12) ✓ — **a factor-2 overstatement** ✓; and `(c′)` needs `≥ 1` contrast member per cell ✓, so `3/3` at each suffices ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2168–2173. correction sites: **none — terminal.**
**TEETH:** `arithmetic recount`.

---
## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` **This shard cites very few external designations** — the annex stack is almost entirely self-referential (it repairs GENH4's own frozen text). **3 distinct designations, all count ≥ 1.**

| Target : designation | Count | Unit |
|---|---|---|
| `GENHN_PROOF_2026-08-08.md:GENHN.A(i)` | 11 | `.22` (the queued transport erratum's target) |
| `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | `.06`, `.17`, `.19`, `.32` (the σ-labelling consumer) |
| `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | `.24` (the non-law strata's tie route) |

All other citations are internal (`GENH4-2`, `GENH4-3`, `GENH4-4`, `GENH4-6`, `GENH4-CAP`, `GENH4-1F`, `S2.1`, `S6.1`, `S6.3`, `S7`, `S11`, `S2.3`), resolved to shard-1 unit IDs throughout and **not emitted as XREFs**.

### 3.2 Pin verification (rule 23)

**Commit hashes cited and `git cat-file -t`-verified — all resolve as `commit`. 12/12:** `11dbd23`, `4b0d946`, `e15308d`, `cceca77`, `e945734`, `6272cd4`, `6cb147b`, `fed3cff`, `a8dec16`, `ca3754d`, `d6a9ac8`, plus `65681144` (the note's own last-touch commit).

**Reports verified to EXIST:** `GENH4_passPE5_report.md` ✓ · `CODEX_GENH4RAT_2026-08-09.md` ✓ · `GENH4_annexpass_report.md` ✓ · `GENH4_annexpass2_report.md` ✓ — **4/4.**

**Machine legs verified to EXIST** (`verification/openmath/`): `genh4annex_supp.py` + output + results ✓ (3) · `genh4annexr_supp.py` + output + results ✓ (3) · `genh4annexpass_fresh.py` + output + results ✓ (3) · `genh4annexpass2_fresh.py` + output + results ✓ (3) — **12/12.** **Plus `genh4annexpass3_fresh.py` + output + results ✓ (3), which the note cites NOWHERE** (§8 defect 1).

**Non-commit hashes (md5s):** `09af7f78…`, `a584cb3e…`, `863c2160…`, `22b766d3…`, `713a0a3b…`, `37d0650e…`, `c1ed4a7f…`, `f26186fd…`, `f044c491…`, `bf8f94f5…`, `7153578c…` (corrected from `71535780…` at `.41`), `6c2441a1…`.

### 3.3 NEAR-MISS dispositions

| As cited | Count | Referent | Disposition |
|---|---|---|---|
| `71535780…` (`.28`) | n/a | the committed file's md5 is `7153578c…` | **The note corrects it itself** at `.41`; carried with the correction |
| internal `S2.1`, `S6.1`, `S6.3`, `S7`, `S11`, `S2.3` | n/a | self-references | Resolved to shard-1 unit IDs, not emitted as XREFs |

### 3.4 Reverse consumer edges

| Party | Direction | What crosses | Protocol |
|---|---|---|---|
| W-12 | outbound supply | GENH4-7′(b) restores the F-SPLTAIL σ_F label the σ-labelling clause consumes | Nothing appended |
| GENHN | **outbound erratum, QUEUED** | the A(i) carrier rename with witnesses (`.22`) | **Queued, not landed** — later discharged at the source (GENHN E3 `46bf675`, per GENIND shard 3) |
| Codex ratification | inbound | 5 findings, CHALLENGE | Repaired here by R1–R6 |
| annex pass #1 | inbound | 1 GAP + 4 MINOR + 2 remarks; **a machine refutation** | Repaired here by ANNEX R2 |
| annex pass #2 | inbound | 3 MINOR | Repaired here by the dated corrections |

**Zero appends are claimed landed on any supplier by this stack.**

---

## 4. NON-IMPORTS

| Fence | Material NOT claimed | Unit |
|---|---|---|
| Annex grade | “the annex text itself is a post-acceptance append and has NOT been through a hostile pass” ×3 | `.01`, `.14`, `.28` |
| Annex-stack counter | 0/2 → **1/2** through a minors-only round | `.28`, `.40` |
| Acceptance scope | “The ACCEPTED 2/2 grade stands ANNOTATED by the fold note pending Asvin's read” | `.26` |
| Clause (c)/(c′) unconsumed | “W-12.D's supply row consumes clause (b) only … no consumer moves under this correction” | `.19`, `.32` |
| Two withdrawn legs | “Both are FALSE as within-stratum claims” | `.29`, `.20` |
| No within-stratum pair | “NO within-stratum pair is claimed at band-pinned strata with m ≤ 2w” | `.31` |
| Honest scope at 2w = N | τ-degenerate members; “a finer reader … would be a menu REFINEMENT, not this note's reader” | `.19`, `.32` |
| Transport erratum queued | “QUEUED (not executed here)” | `.22` |
| n = 5 stays open | GENH4-BOX-2 re-asserted in all three what-does-not-move declarations | `.13`, `.27`, `.39` |
| Nothing above edited | three byte-freezes, four byte counts, each verified before and after | `.01`, `.14`, `.28`, `.40` |

---

## 5. Teeth inverse table

| Instrument / audit | Guarded units | Disposition |
|---|---|---|
| **`genh4annex_supp.py`** C0–C6 (GREEN after a disclosed RED-and-repair) | `.03`–`.11` | Executable regression + two fired teeth (`2w ≥ N` two-lift; the extra-token) |
| **`genh4annexr_supp.py`** C0–C7 (GREEN, 0.4 s + PARI) | `.15`–`.18` | Executable regression; **the k ≥ 2 slice's FIRST exercise**; C6 the **first char-p σ contact for F-SPLTAIL**; C7 two wrong-floor mutants FIRED 4/4 |
| **`genh4annexpass_fresh.py`** FR2A/FR2B/FR4/FR5/FAeq (GREEN) | `.19`, `.29`–`.33`, `.35`, `.38`, `.42` | **Foreign-note (verifier) evidence, including a MACHINE REFUTATION** of two displayed annex legs (FR4: 6/6 and 24/24) |
| **`genh4annexpass2_fresh.*`** | `.40`–`.43` | Foreign-note evidence for the three minors |
| **the pass's independent re-derivation of the consumed surface** | `.16`(b), `.17` | **AUDIT: `in-house hostile pass`, positive result** — GENH4-7′(b) + the supersession + R3/R4/R5 + PE5's A2/A3 all re-derived CLEAN |
| **R2.REM Remark 2** (the char-2 trace argument re-derived SOUND) | `.31`(ii), `.37` | **AUDIT: positive certification**, recorded so (c′)(ii) can cite it |
| **isolated re-runs of both annex legs** (PE5 bit-identical; R elapsed-only) | `.11`, `.18`, `.38` | Reproduction by a hostile verifier |
| **this compiler's arithmetic audits** | `.03`, `.04`, `.05`, `.06`, `.07`, `.08`, `.09`, `.10`, `.11`, `.12`, `.14`, `.15`, `.16`, `.18`, `.19`, `.20`, `.21`, `.23`, `.24`, `.29`, `.30`, `.31`, `.33`, `.34`, `.35`, `.36`, `.38`, `.39`, `.41`, `.42`, `.43` | **AUDIT: `arithmetic recount`** — **31 units re-derived; all agree with the source** |

**PROOF-ONLY rows:** `.34` (the coset count — a counting proof feeding an UNCONSUMED clause), `.31`(ii) (whose existence inputs are M2 and a pass-verified trace argument), `.21`/`.22` (frame and queued erratum).

**Both-direction audit.** Every instrument row guards at least one unit; every unit whose TEETH field names a leg appears above. **`TEETH: NONE`** units — `.13`, `.22`, `.23`, `.25`, `.27`, `.34`, `.36`, `.39` — are fences, riders, queued obligations and inventory repairs. **Zero orphans.**

**Signed vacuity / disclosure dispositions:** `.19`/`.31`/`.32` ((c′) is UNCONSUMED and its 2w = N leg rides existence arguments with an honest-scope caveat), `.22` (the erratum is queued, not executed), `.14`/`.28` (each annex layer is itself ungraded at composition). **`stale self-description`:** none uncured — **every layer's grade claim is superseded by the next layer's provenance paragraph, in order.**

---

## 6. BOUNDARY SELF-AUDIT (rider-and-repair prose, rule 9)

Zero tags. **But the boundary problem is unusually easy here and §6.3 says why: the source's own numbered sub-headings (A1–A4, R1.0–R1.2, R2–R6, R2.G1, R2.M1–M4, R2.REM, MINOR-1–3) are boundary markers the author supplied.** Every unit below corresponds to one such heading or to a distinct named object inside one.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. Each annex layer's provenance emitted as its own unit (`.01`, `.14`, `.28`, `.40`).** Test 1 and rule 21: each carries a distinct byte-freeze predicate with its own byte count, and each states its own grade. *Not arguable.*

**2. A1 split into five (`.02`–`.06`).** Test 1: a defect report, a three-rider list, a lemma with proof, a machine refutation, and a σ-labelling consequence are five different claims. *Arguable:* whether `.03` (the three riders) folds into `.02`. **Chosen split** because the three riders are the *supersession vehicle* and carry the TARGETS list; a merge needs them addressable.

**3. GENH4-7 (`.04`) and GENH4-7′ (`.16`) are SEPARATE units, not a chain in one.** **The shard's most consequential call.** *Candidate A:* one unit with a CHAIN field, since GENH4-7′ “replaces GENH4-7's hypothesis sentence … everything else unchanged”. *Candidate B (chosen):* two units. **Reason: GENH4-7 is the object the Codex ratification found gapped, and its exact displayed hypothesis is the evidence for that finding.** Collapsing it into GENH4-7′ would erase the defect's subject. **And R2.M4 (`.36`) corrects GENH4-7′'s own inventory of what it replaced — a correction that is unstatable if the two lemmas are one unit.** *Cost:* the two share most of their text; both are quoted in full, and the overlap is flagged.

**4. Clause (c) → (c′) emitted as separate units (`.04`(c) inside `.04`; `.19`'s witnesses; `.31`'s (c′)).** Test 3: three successive versions, two of them withdrawn or replaced, each with its own machine evidence. **`.19` must be addressable because two of its three bullets are WITHDRAWN and one survives.**

**5. R2's three per-stratum bullets kept in ONE unit (`.19`) with the withdrawal recorded there.** *Candidate A:* three units, since two are withdrawn and one is not. **Rejected** because R2.G1 withdraws them as a pair by name (“the N-even band-pinned leg and the refine-deeper leg”) and the surviving `2w = N` bullet's inputs are supplied by two separate later units (`.34`, `.37`) that already make it traceable. **The refine-deeper leg IS emitted separately (`.20`)** because it is a self-contained construction cited from elsewhere and is withdrawn by name.

**6. R2.M1–M4 and R2.REM → five units (`.33`–`.37`).** Test 2: each is cited by designation and each names a distinct target. **`.36` (M4) is the inventory correction and must be addressable — it is the unit that tells a merge how many things GENH4-7′ actually replaced.**

**7. The three what-does-not-move declarations → three units (`.13`, `.27`, `.39`), declared as SERIES.** *Candidate A:* one merged fence. **Rejected**: they have different exception lists (zero, four, five-plus-one), and a merge that kept only the last would lose the record that ANNEX PE5 changed nothing at all.

**8. The three GENH4-BOX-1 appends → three units (`.12`, `.26`, `.38`), declared as SERIES.** Rule 28: dated entries continuing one box across a freeze. Their order is the arc's order and must be reconstructible.

**9. The post-annex-pass-2 minors → three units (`.41`–`.43`).** Test 2 and 4: three targets, three kinds (`provenance-rider`, `replacement`, `counter re-reading`).

### 6.2 Merges deliberately NOT made

- `.02` and `.15` stay separate (PE5's defect report and the Codex finding against PE5's own repair): **the second is a finding against the first's fix**, and collapsing them would hide a two-level recursion.
- `.07` and `.23` stay separate (A2's partial units rider and R4's superseding one): **a rider superseded by a rider needs both endpoints.**
- `.29` and `.30` stay separate (the machine refutation and the transport-error diagnosis): the first is evidence, the second is the explanation, and the explanation generalizes.
- `.34` is not folded into `.31`: it is a self-contained counting proof cited by designation from (c′)(ii).

### 6.3 Format feedback

1. **Author-supplied numbered sub-headings made this the easiest shard in the queue to bound.** Every unit maps to a heading or a named object. **Recommendation: the format should note that a source which numbers its own repair items is materially cheaper to compile, and the corpus should keep doing it.**
2. **Rule 18's kinds needed the WITHDRAWAL sub-kind again** (`.19`, `.20`, `.29`) — the same recommendation GENIND shard 3 made independently. **Two shards, two queues, same gap.**
3. **A third-order rider occurred here** (`.37` Remark 1 riders `.21`'s audit sentence, which itself audits the body). **The `TARGETS` field handles it, but the CHAIN field's vocabulary assumes edits to *statements*, not to *audits of statements*.** Recommend allowing a CHAIN member to be an audit.
4. **Rule 14 fired twice** (`.10`'s mass table, `.24`'s six-key partition) and both double emissions paid: the six-key partition's arithmetic audit reproduces every one of its seven numbers, which is what makes the REFUTED-CRITICAL disposition checkable.
5. **The `AUDIT` disposition class (rule 27) needed a POSITIVE member.** `.37`'s Remark 2 and `.38`'s “the consumed surface was independently RE-DERIVED CLEAN by the pass” are hostile-pass results that *certify* rather than *find*. The current vocabulary can only record findings. **Recommend `hostile-pass certification` as an explicit disposition** — without it, the strongest evidence in this shard is unlabelled.
6. **The shard's structural finding.** **Four layers, each finding a real defect in the one before it, and the consumed surface surviving every one of them.** PE5 finds two display defects in an ACCEPTED body → Codex finds a hypothesis contradiction in PE5's own repair, on a consumed clause → annex pass #1 machine-refutes two of Codex's repair's witnesses, on an unconsumed clause → annex pass #2 finds three transcription/parenthetical defects. **The consumed clause (b) was re-derived clean at every level.** That separation — defects concentrate in the unconsumed and the display, the consumed surface holds — is this shard's calibration datum, and it is the opposite of GENIND shard 3's (where the defects landed squarely on a consumed rate).

---

## 7. SHARD NOTES

- **Cross-shard riders ISSUED by this range (eleven in-range sentences of shard 1).** ANNEX PE5 → shard 1 `.21`, `.25`, `.29`, `.30`, `.39`. ANNEX R → shard 1 `.14` (×3 sentences), `.19`, `.28`–`.32`, `.62`. **ANNEX R2 and the post-pass-2 corrections issue NO rider into shard 1** — they act on annex material only, and all three what-does-not-move declarations say so.
- **Range-edge audit.** Line 1208 is blank (the accepted body ends at 1207); line 1209 opens `## ANNEX PE5`; **line 2173 is the note's last line.** No source statement unit is cut at either edge, and the lower edge is exactly the acceptance freeze's boundary.
- **Protocol.** No append landed on any supplier; one erratum queued (and discharged at the source, per GENIND's record); one fold obligation offered in shard 1 (likewise discharged).
- **Numbering.** Temporary IDs `EFF.GENH4.s2of2.01`–`.43`.
- **MERGE HAZARDS (five).**
  1. **`.04` and `.16` share most of their text** (GENH4-7 and GENH4-7′). Do not dedupe: the first is the finding's subject.
  2. **`.19`'s three bullets have different fates** — two WITHDRAWN, one surviving with completed inputs. A merge that treats R2 as a unit will carry two false witnesses.
  3. **`.31`'s (c′) is UNCONSUMED** and its (ii) leg rides two existence arguments (M2's count; a pass-verified trace argument). Do not promote it to a load-bearing clause.
  4. **`.26`'s annotation is unresolved**: ACCEPTED 2/2 “stands ANNOTATED … pending Asvin's read” (OPEN-CALL 1).
  5. **`.40`'s terminal state is body 2/2 (annotated) + annex stack 1/2**, and a third annex pass's leg exists on disk uncited (§8 defect 1).

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the ACCEPTED 2/2 grade is ANNOTATED and the annotation is unresolved

ANNEX R's BOX-1 append (`.26`): “The ACCEPTED 2/2 grade stands **ANNOTATED** by the fold note pending Asvin's read”. Nothing later resolves it: annex pass #1 was NOT CLEAN at annex scope, annex pass #2 was minors-only, and the terminal record (`.40`) reports the annex stack at 1/2 without revisiting the annotation. **So GENH4's status is: body ACCEPTED 2/2 with an unresolved annotation; annex stack 1/2.** **Decision needed: what grade the merged spec attaches to THEOREM GENH4.A/B/C, COROLLARY GENH4.D and the eleven densities.** Raised identically at shard 1 OPEN-CALL 2; recorded at both ends because the evidence is split.

### OPEN-CALL 2 — a third annex pass's machine leg exists on disk and is cited nowhere

`verification/openmath/genh4annexpass3_fresh.py` (+ output + results) **EXIST** and the note — frozen at the post-annex-pass-2 corrections — cites them nowhere. The note cannot know its own successor. **Decision needed: whether the merged spec reads the annex-stack grade from the note (1/2) or from the repo (a third pass's verdict, unread here), and whether GENH4 owes a dated append.** **This compilation does not adjudicate it and has not read pass #3.** (The same shape as GENIND shard 3's OPEN-CALL 4 — **two notes in this queue are behind their own repos.**)

### OPEN-CALL 3 — the (c′) honest-scope caveat may be a menu refinement, and the note says so without deciding

R2's 2w = N leg (carried over to (c′)(ii) verbatim, `.32`) closes: “at τ-degenerate members every lift may read {(1,2),(1,2)}; a finer reader keyed on the pin letter's twist class could conceivably decide those members at 2w = N — that would be a menu REFINEMENT, not this note's reader, whose key granularity (letters censused into one key) is what (c) is sharp for.” **So cap-uniqueness is sharp for THIS reader's key granularity and possibly not for a finer one.** The clause is unconsumed, so nothing rests on it. **Decision needed: whether the merged spec records “the UND exit at 2w ≥ N is forced” as reader-relative** — which is what the caveat says and what a chapter cut might over-read.

### Recorded source defects (flagged, not repaired)

1. **A third annex pass's leg exists uncited** — OPEN-CALL 2.
2. **`.28`'s results pin was one character wrong** — the note corrects it itself at `.41`; recorded because it is the second md5-transcription defect in this queue (GENIND shard 2 `.58` is the first), and both were caught by commit-time re-verification rather than by any run.
3. **`.19`'s scope paragraph calls F4 “unconsumed” and the ratification graded it a GAP** — consistent (a GAP on an unconsumed clause is still a GAP), but a reader may take “unconsumed” as a downgrade. The note's own grading (`.14`: “F4 (CONFIRMED GAP, scoped to GENH4-7(c), unconsumed)”) is precise; recorded because the two words sit far apart.

### Fidelity audit

- Every CANONICAL STATEMENT is verbatim or explicitly `[ASSEMBLED]`. **No count, valuation, σ-multiset, census, md5, or quantifier was altered anywhere.** Where two units share text (`.04`/`.16`), both are quoted in full and the overlap is flagged.
- **One truncation, at `.19`**, marked `…`, taken because the three stratum bullets are carried by reference to their own targets (`.20`, `.29`, `.31`, `.34`, `.37`), each of which quotes the relevant text.
- **Two rule-14 double emissions** (`.10`, `.24`); no source Markdown table exists.
- **3 XREF designations verified (all count ≥ 1); 12 commit pins verified, 12/12; 4 reports and 12 machine-leg files verified present** (plus 3 uncited pass-3 files).
- **31 units carry compiler-computed arithmetic audits, all agreeing with the source**, including: the six-key partition's seven numbers; the wrong-cap mass conservations at three rows; the k ≥ 2 cell's HALF; the coset count's two contradiction branches; (c′)(i)'s three sub-cases; the char-2 disc failure and its repair; and the `3 + 3 = 6` recount.
- **Every layer's grade disclosure is carried at its unit**, and the terminal state (body 2/2 annotated; annex stack 1/2) is recorded at `.40` rather than inferred.
- **Honest limitation:** this shard's mathematics is thin (one new lemma family, GENH4-7/7′/(c′), plus a coset count) and its content is overwhelmingly *repair discipline*. Its value to a chapter cut is (i) the restored F-SPLTAIL supply that W-12.D consumes, and (ii) the record of what four successive decorrelated reads found in an accepted note — **including one machine refutation of a displayed argument, and the fact that the consumed surface survived all four.**

EFF-GENH4-s2of2 COMPILED: 43 statements / 3 xrefs verified / 12 commit pins + 16 artifacts verified / 2 near-misses / 3 open calls
