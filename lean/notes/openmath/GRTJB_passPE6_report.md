# GRTJB-PE6 — hostile verification pass on the post-r5 J-B tree-junction note (FOURTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD** (commit
`98c3e47`; note last touched by **r5** = `f9f104e`, 265 insertions / 31
deletions, one file — THE DISCHARGE ROUND: the u ≥ 0 four-line theorem
displayed at §5 with the honest membership-scope split at rows 4/12, plus the
F-1 surface-4 re-scope, the F-2 exit-bound-node gloss, the F-4 row-20 OUT
adjudication, the F-5 row-24(d) correction).
**Scripts re-run (all four):** `grt_jb_checks.py` (sealed) ·
`grt_jb_r1_levelcensus.py` · `grt_jb_printwalk.py` · `grt_jb_printwalk2.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-06 (wallclock). Prior reports **JB-PE1** (1C+9G), **JB-PE2**
(0C+7G), **JB-PE3** (0C+8G), **JB-PE4** (0C+8G), **JB-PE5** (0C+5G) read in
full, and the r5 diff read line by line, before this pass formed any judgment.
This is the SIXTH hostile reader and the FOURTH acceptance attempt.

---

## §0. VERDICT

**0 CRITICAL, 2 JUSTIFICATION GAPS, 1 minor.**

    GRTJB-PE6 FINDINGS: 0 critical, 2 gaps + 1 minor / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

**The r5 diff itself is CLEAN on its mathematics.** The four-line u ≥ 0
theorem at §5 re-derives exactly (all four steps verified against the r4
lattice definition and the [RMG] S2.1 constants, including the m = 1
degenerate corner γ₁ = h₀ and the two divisibility legs of step (1)); the
parity corollary excluding J-A's (e,h) = (2,3), V = 1 instance is exact; my
own independent read-only probe confirms **u ≥ 0 and the step-(2) identity on
598,500 lattice members with 0 violations of either, and 1 ∉ 𝒲₁ at (2,3)**.
The scope split is honestly drawn: §2's THEOREM JB-DEV and §3's THEOREM
JB-VTX do quantify `f ∈ O[x] nonzero` with NO degree bound (verified at both
theorem statements), the membership residue is characterized the same way at
both rows and at all 17 live carrying surfaces I swept, the frontier census
correctly stays FOUR (rows 4, 5, 12, 22), and the row-20 OUT adjudication is
sound and displayed. The §4(ii) restated gloss is now TRUE and every one of
its citations checks verbatim at [RMG] (L-CELL(i)'s degree hypothesis, the
S2.1 telescope, S2.2's "Φ_m-exit (i = m−1)" with j_{m−1} ≥ P_{m−1}, and the
structural remark's sub-cell b·∏_{l≤m−2}Φ_l^{j_l} REDUCED AT LEVEL m−1). The
strike system is balanced at **67 spans** (136 `~~` tokens − 2 backticked
literals, toggle-parse clean), exactly r5's claim.

The two gaps: **one fence one level short in a body vein no pass had
level-audited** — §3(d)'s third min tie (d3) `w_{q+1}(f) = v_{q+2}(f)` is, by
the note's own words, "JA-VAL **one level up**", i.e. JA-VAL at level q+1,
which by the note's OWN level-indexing rule (rows 17/18's "`P<q` read at
level m"; the r3/F-4 correction; J-A §1's "at level m … for all q ≤ m−1")
requires the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — while §0M row 11 and every
regenerated surface fence all three min ties at `P<q` only (F-1); and **the
r5 supporting probe is transcribed below the arc's own replayability
standard** — its enumeration (h-range, j-ranges, a-range, tuple-vs-value
counting) is not recoverable from the note, so the headline figure 5,288,324
cannot be reproduced by a fresh verifier, unlike the two r4 probes, which
PE5 replayed bit-for-bit from committed code (F-2). One minor: the scope
block's "strictly smaller MEMBERSHIP hypothesis" mischaracterizes the logical
relation (membership IMPLIES the needed u ≥ 0 instance — a sufficient route,
per-instance a STRONGER hypothesis; "smaller" is true only of the remaining
open domain) — direction conservative, no consumer is endangered (m-1).

**All four machine legs reproduce, exit 0, all four md5s intact at HEAD,
`git diff verification/` empty after the runs** — r5's "note-only, all
instruments byte-frozen" claim HOLDS.

---

## §1. MACHINE LEG (mandatory — all FOUR runners RUN, exit 0; no leg NOT-RUN)

Run from `verification/openmath/`, `python3`, no arguments, nothing edited.

| runner | md5 at HEAD | exit | reproduction |
|---|---|---|---|
| `grt_jb_checks.py` (sealed) | `55f4911eaddd8524fd91368b30ed71bd` **intact** | **0** | 18/18 families GREEN, 6,700 samples, 0 violations |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` **intact** | **0** | output **diff-identical** to committed `_output.txt` (0 lines) |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` **intact** | **0** | 5/5 GREEN; coverage 84 leg-A walks / 12 byte-unequal / 72 leg-B |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` **intact** | **0** | 3/3 GREEN, 45 xframe / 27 degen / 28 recon |

`git diff verification/` is **EMPTY** after all four runs. Figures vs the
note, all match: EXT-GATE 1 · JB-DEV 893 · JB-KEYEQ 25 · JB-SHEAR 893 ·
JB-VTX 893 · JB-ID 34 · JB-TREE 79 (125 with chambers) · JB-LINE 194 ·
JB-EPS 955 · JB-CM 28 · JB-CREAD 79 · JB-QO 5 · JB-D0 4 · TW-JB 2,480 ·
teeth 3/3/3/3 caught · censuses scored 104 | boundary 21 | v = 0: 0 |
R = 0: 0 | off-perimeter tree rows 0 · byte census identical to the note's
examples (I4A/I4B `{1:T,2:T,3:T}`; T3A/T3C/T3D/T3E `{1:T,2:F}`; I4C
`{1:T,2:F,3:F}`; three `{}`) · level census m = 1: 45/0 · m = 2: 8/10 ·
m = 3: 3/3, 0 scope-outs, totals 13 = 0/10/3.

**The r5 probe, replicated in substance (read-only, /tmp):** my own
enumerator over 1-, 2- and 3-level read chains (coprime (e, h), e ≤ 6,
h ≤ 8; W_l ∈ {0, 1, 2}; a ≤ 4; j_l ≤ 6; 900 sampled chains) checked
**598,500 lattice members: u < 0 violations 0, step-(2) identity violations
0**, and 1 ∉ 𝒲₁ at (e, h) = (2, 3) — the display's three machine claims all
CONFIRMED independently. The note's own figure 5,288,324 did NOT reproduce
under any natural parameterization I searched (see F-2): the note does not
disclose the probe's h-range, j-ranges, a-range, or counting unit.

---

## §2. FINDINGS

### F-1 — JUSTIFICATION GAP (charges 4 + 5: the one body vein no pass had level-audited). §3(d)'s third min tie consumes "JA-VAL one level up" (level q+1) but is fenced at `P<q`; by the note's own level-indexing it needs the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — the exact PE3/F-4 disease at a row the (RES) correction never swept

§3(d) (LIVE body text):

> min ordinate of H(f) = w_{q+1}(f) = v_{q+2}(f)
> (the weight recursion + **JA-VAL one level up**);

The identity `w_{q+1}(f) = v_{q+2}(f)` is the m = q+1 member of JA-VAL's
family (`w_m = v_{m+1}`). The note's OWN consumption rule for JA-VAL is
level-indexed — §0M rows 17/18 and the §4 surfaces say JA-VAL consumed at
level m holds at "**`P<q` read at level m**", i.e. keys shared strictly
below m; and J-A's §1 defines (verified at source,
`GRTJA_PROOF_2026-08-08.md` L69–70):

> **Shared-key perimeter at level m**: Φ_q^har = φ_{q+1}^cls byte-for-byte
> for all q ≤ m−1 (all operators at level m consume only keys that deep).

At m = q+1 that is agreement for j ≤ q — the BYTE-EQUAL CHAIN THROUGH q
(`P≤q`), NOT the shared-key perimeter `P<q`. This is letter-for-letter the
r3/F-4 analysis that re-fenced (RES) ("JA-RES at read level m = q+1 …
requires agreement for j ≤ q, i.e. `P≤q`, NOT `P<q`"). Yet §0M row 11
fences (d1)–(d3) at (a1) `P<q` with (a2) = `—`, and every regenerated
surface repeats it (§3 ∎ Grade line "(d1)(d2)(d3) the THREE min ties:
`P<q` + W2-C1"; the grade cap's "(d1–d3) ride `P<q` + W2-C1 only"; §7.2's
JB-VTX row; §7.3's W-3 bullet; JB-BOX-2's enumeration "ALL of JB-VTX … on
the SHARED-KEY PERIMETER `P<q`").

Three corroborations, all from the note's own material:

* **The runner itself gates the tie at the deeper fence.** In
  `grt_jb_checks.py` (`jb_shear_vtx`, L276–284), d2 (`minH == T.wlev(q+1,f)`,
  harness-internal) runs unguarded, while d1 AND d3 run only under
  `q <= L` with `L = shared_upto(T,G)` — which is exactly `P≤q`. So no
  machine leg has ever tested d3 on `P<q` \ `P≤q`; the note discloses this
  as "machine-restricted further to q ≤ shared_upto" but treats it as an
  instrument cut, not the statement's own hypothesis.
* **The representative-pin rescue is the route the note explicitly refused.**
  d3 at q = qcap could be argued via "slot q holds φ_{q+1} := Φ_q^har by the
  frame's own pin, so J-A's j = q requirement is free" — but r3/F-4 records
  for the identical question at (RES): "The alternative repair — arguing
  that the representative pin φ_{q+1} := Φ_q^har discharges J-A's j = q
  requirement — is NOT taken: it is not derived anywhere in this note." The
  same refusal must bind d3, or (RES)'s own deeper fence is unmotivated.
* **The geography is the known one.** The two fences differ exactly at
  q = qcap on the 5 roster towers with shared_upto < n (T3A, T3C, T3D, T3E,
  I4C — the r4/F-3 census); there d3 is asserted with no J-A license and no
  machine leg. d1 (`min U = v_{q+1}(f)`, print Lemma `shape` item 1 — all
  operators at level q) and d2 (harness-internal) are correctly fenced at
  `P<q`; ONLY d3 is the level-(q+1) consumption.

Classification: gap, not critical — nothing inside §4/§5 consumes d3
(JB-TREE/JB-CREAD read w_m/v_{m+1} of R and Q through their own fenced
rows), the tie is unproved-in-note at the affected levels rather than shown
false, and the repair is a strict narrowing of one clause (the same genre
PE3's F-4 was graded). But §7.3 hands "the three keyed min ties (d1)–(d3)"
to downstream units on `P<q`, so a consumer can over-consume d3 by exactly
one level on 5 of 16 roster towers. Under JB-BOX-6's standing rule the
matrix (row 11) must carry the fence first. Why five passes missed it: PE1
re-derived the shear/slope arithmetic, PE3 re-derived (a)/(b)/(c) and
transcription-checked (VAL)/(GRID)/(RES) — the level audit that produced
F-4 was run on §2(iii)'s three layers and never extended to §3(d)'s tie
list; the ties' own derivation line ("JA-VAL one level up") was never
re-derived against the level-indexed perimeter until this pass.

### F-2 — JUSTIFICATION GAP (charge 1, machine/record leg: the r5 probe is transcribed below the arc's own replayability standard). The §5 figure 5,288,324 is not reproducible from the note — the enumeration's parameters are not disclosed

The §5 display's machine bracket (the ONLY probe record; the S-STATUS and
the r5 round block point here as "transcribed at §5"):

> [Machine: read-only probe 2026-08-06 (/tmp, all four instruments
> byte-untouched): 5,288,324 enumerated lattice members over 1-, 2- and
> 3-level read chains (coprime reads e ≤ 6, weights W_l ≤ 2), u < 0
> violations **0**, step-(2) identity violations **0**; 1 ∉ 𝒲₁ at
> (e, h) = (2, 3).]

Missing from this transcription: the h-range of the coprime reads, the
j_l-ranges (and whether the P_l = e_l·g_l caps of the lattice definition
were enumerated — which would require g-data the sketch does not mention),
the a-range, and the counting unit (parameter tuples vs distinct V-values).
I attempted reproduction under a family of natural parameterizations
(h ≤ 2..15, j-caps 2..14, a-caps 1..40, W ∈ {0..2}, including
per-level j-caps proportional to e_l) and none yields 5,288,324. Contrast
the arc's own standard: both r4 probes were replayed **bit-for-bit** by PE5
precisely because their parameters were pinned by committed code (the
roster + `qcap_of`/`shared_upto`; `jb_eps`'s strided grid), and r4's
S-STATUS made "transcribed where cited" part of the instrument-hygiene
claim, as r5's does ("its one supporting probe ran read-only to /tmp and is
transcribed at §5").

Classification: gap, small, record-layer only — NOTHING mathematical rides
on the figure: u ≥ 0 on 𝒲_m is fully proved by the displayed four lines
(re-derived by this pass), and every claim the probe supports (u ≥ 0, the
step-(2) identity, the parity exclusion) is independently machine-confirmed
by this pass's own enumerator (598,500 members, 0/0 violations, 1 ∉ 𝒲₁).
The defect is that the note's number is take-my-word-for-it, in an arc
whose probes have until now been replayable exactly.

### m-1 — MINOR (charge 1, wording of the scope split). "strictly smaller MEMBERSHIP hypothesis" / "exactly the MEMBERSHIP hypothesis" mischaracterizes the logical relation between the residue and the original proviso

The §5 SCOPE block:

> stays CARRIED at the full quantifier as the **strictly smaller**
> MEMBERSHIP hypothesis w_{q+1}(f) ∈ 𝒲_{q+1}

and §0M column (b): "The carried residue at the two consuming rows (4 and
12) is **exactly** the MEMBERSHIP hypothesis". What the consumption needs
at the residual domain (deg f ≥ deg Φ_{q+1}) is u ≥ 0 at V = w_{q+1}(f);
by the r5 theorem, membership IMPLIES that — it is a SUFFICIENT route, and
per-instance a logically STRONGER hypothesis, not an equivalent or weaker
one (its satisfaction set is contained in the proviso's, with strictness
unproved either way). "Strictly smaller" is accurate only in the
obligation-domain reading (what remains open is now confined to
deg f ≥ deg Φ_{q+1} and pinned to one concrete question), and "exactly"
overstates necessity. Direction: conservative — a consumer carrying
membership carries at least what the proviso needs, so no statement is
weakened and no consumer is endangered; the row cells' operative content
("DISCHARGED for deg f < deg Φ_{q+1}; open residue = MEMBERSHIP at the
unbounded-degree quantifier") is a fair description of what the note now
carries. Minor, not a gap.

---

## §3. CHARGE-BY-CHARGE COVERAGE, AND WHAT SURVIVED

**Charge 1 (the r5 partial-discharge split).**

* **The four-line derivation — RE-DERIVED, EXACT.** Step (1): e_{m−1} | E_m
  (E_m = e₀⋯e_{m−1}) and e_{m−1} | Γ_l for l ≤ m−2 (the ∏_{l<t<m} e_t
  contains t = m−1) ✓; Γ_{m−1} = γ_m (empty product) with
  γ_m ≡ h_{m−1} (mod e_{m−1}) and γ_m ≥ h_{m−1} ≥ 1 ✓, including the m = 1
  corner (γ₁ = h₀, congruence trivial). Step (2): all terms but
  j_{m−1}Γ_{m−1} vanish mod e_{m−1}, then ℓ_{m−1}h_{m−1} ≡ 1 gives
  s_m^wt(V) = j_{m−1} mod e_{m−1} ≤ j_{m−1} ✓ (well-defined regardless of
  representation non-uniqueness, since s_m^wt is a function of V and each V
  has at least one representation). Step (3): V ≥ j_{m−1}γ_m (every
  discarded term ≥ 0, using E_m ≥ 1, Γ_l ≥ 1, a, j_l ≥ 0 — the PE5-verified
  positivity), then γ_m ≥ h_{m−1} and (2) give
  (j_{m−1} − s^wt)h_{m−1} ≥ 0 ✓. Step (4): divide by e_{m−1} ≥ 1 ✓. The
  proof nowhere needs the j_l ≤ P_l − 1 caps ✓. COROLLARY: V ≡ j_{m−1}
  (mod 2) at h = 3, so V = 1 forces j_{m−1} odd ≥ 1, whence
  V ≥ j_{m−1}γ_m ≥ γ_m ≥ 3 ✓. The display is a genuine re-derivation, not a
  copy: it adds the j_{m−1}γ_m intermediate step PE5's four-line sketch
  skipped (which the rigor actually needs) and the two divisibility legs.
* **The scope analysis — SOUND at both rows.** §2's THEOREM JB-DEV ("Level
  q ≥ 0, f ∈ O[x] nonzero") and §3's THEOREM JB-VTX ("f ∈ O[x] nonzero")
  verified to carry NO degree bound; both consumptions apply JA-GRID(a) at
  V = w_{q+1}(f) (the read grid s(λ) with λ = w_{q+1}(f)); 𝒲_{q+1} is by
  its r4 definition the value set on deg f < deg Φ_{q+1} only, so
  membership holds by definition exactly on that sub-window and is honestly
  refused off it ("nothing this note consumes establishes [it] at
  deg f ≥ deg Φ_{q+1}" — correct: the note consumes no result about weights
  of degree-≥ deg Φ polynomials). The residue is characterized identically
  at rows 4 and 12 and both cells display the same formula. The only
  wording defect is m-1.
* **Surface consistency — 17/17 live carrying sites narrowed.** I swept
  every live `u ≥ 0` site (54 mention lines; the rest are historical round
  records, struck predecessors, or superseded regions, all correctly
  banner-fenced): §0M column (b) · row 4 · row 12 · ⟨n3⟩ · summary points
  (1) and (3) · grade cap ×2 bullets (GRID and d4) · §2 ∎ Grade line ·
  §2(iii) retraction block (with the forward pointer PE5's F-3 asked for) ·
  §3 ∎ Grade line · §3 machine bracket's disclosed coincidence · §5 ·
  JB-BOX-2's G-5 bullet · §7.1's JB-SHEAR row · §7.2's JB-DEV and JB-VTX
  rows · §7.3's W-3 bullet — every one carries the narrowed form with the
  same content (PROVED at deg f < deg Φ_{q+1} / V ∈ 𝒲_{q+1}; membership
  residue at the unbounded-degree quantifier; §5 pointer). No live site
  retains the stale "not excluded" frame; both r5 strikes verified in
  place. JB-BOX-2's reach sentence ("reaches EXACTLY TWO claims: rows 4 and
  12") is status-free and stays true.
* **"§5's OWN application is unaffected either way" — TRUE**: the λ and
  γ_{m+1} memberships are derived (λ = w_m(f) with §5's own
  deg f < deg Φ_m hypothesis; γ_{m+1} = w_m(Ĉ_m) via (Ĉ-wt) with Ĉ_m ≠ 0
  via (Ĉ-read) + the class pin), as PE4/PE5 verified and I re-checked.

**Charge 2 (the §4(ii) restated gloss).** TRUE NOW, all citations verified
at `RMENGINE_2026-08-08.md`: L-CELL(i) is quantified "Every 0 ≠ x ∈ O[x]
with deg x < deg Φ_m" (L419–420) ✓; "reduced … then deg C < deg Φ_m by the
degree telescope deg Φ_{l+1} = P_l·deg Φ_l" (S2.1, L415–416) ✓; a node
taking a Φ_m-exit has i = m−1 as its lowest violating index, hence
j_{m−1} ≥ P_{m−1} (S2.2's child list, L507) and
deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m ✓; the structural remark reads verbatim
"At a Φ_m-exit the reducing level is m−1, so by priority j_l ≤ P_l − 1 for
every l ≤ m−2: the sub-cell S := b∏_{l≤m−2}Φ_l^{j_l} is REDUCED AT LEVEL
m−1" (L527–530) — exactly the r5 text's exit-bound decomposition claim, and
the E1-priority (lowest index fires first) is what licenses it ✓. The
R-leaves gloss matches row 15's machine cell (leaf reducedness is the only
reducedness `jb_tree` keys) ✓. The added scope note on the r4/F-4 bracket's
min-line parenthetical ("its bound line ≤ w_m is supplied where the reduced
decomposition exists, deg < deg Φ_m") is the correct completion of PE5's
adjacent observation ✓. "Nothing downstream consumed the struck gloss" —
re-confirmed: (i)/(iii)/(iv) consume L-EXACT/L-CANON/JA-VAL per rows
15/17/18, and PE5 re-derived (ii)'s operative content sound.

**Charge 3 (the row-20 OUT adjudication).** SOUND, and displayed where the
criterion lives (summary point (1)). The reason is coherent with the
system: row 20's (c) cell is row 21's (VD-m) context INHERITED — the
hypothesis is native to rows 21/22, where it IS counted (row 22 in the
frontier, row 21 beside its end-to-end IND leg) — and row 20's own
conditionality is column (e)'s [RMG] license riding the lemma's PROOF at
the derived membership, the same consumption-at-grade genre as the
rows-13/18 exclusions. Cross-checked against row 23 (also "inherits row
21", but carrying the MJB-CREAD IND leg — never a candidate), and against
the criterion's own words ("open proviso with NO machine leg beside it").
The census "THE FRONTIER IS ROWS 4, 5, 12, 22" is now mechanically
reproducible from the post-r5 table: I re-walked all 28 rows under the
criterion and find exactly those four IN, rows 13/18(C-W_Q)/20 OUT with
displayed reasons, and no further candidate. Row 20's cell carries the
[r5, F-4] pointer ✓.

**Charge 4 (body veins vs the five reports' re-derivation lists).** Compiled
coverage: PE1 (JB-EPS line-by-line; JB-CREAD's five lines + verbatim ε′;
the shear derived incl. slope law; JB-AFF; §3(a)'s v_{q+2} half), PE2 (F1
split from the sealed JSON; JA-GRID(c) re-derived), PE3 (JB-VTX(a)–(d) +
JB-AFF re-derived; JB-ID; the (VAL)/(GRID)/(RES) transcriptions verified
against J-A verbatim; walker2 code audit), PE4 (the (RM-m) recital 11/11
byte-compare; the §4(iii) scope dig = F-4), PE5 (§4(i)/(ii) in full; the
𝒲_m definition at source; the re-scoped per-edge laws vs S3.2). Remaining
un-re-derived veins I closed this pass: §2(i)'s uniqueness-of-division line
(sound), §1's m_{q+1}^GMN degree identity (sound — the print recursion
deg φ_{r+1} = e_r f_r·deg φ_r under the P-index dictionary telescopes to
[RMG]'s deg Φ_{l+1} = P_l·deg Φ_l), §5's v = 0 branch display (sound: v = 0
kills the B-READ step, so only the target-read vanishing survives — and the
note claims exactly that), §3(c)'s slope/length arithmetic re-checked
(exact), and **§3(d)'s tie derivations with their level bookkeeping — where
the arc's one remaining fence defect was hiding (F-1)**. After F-1 the note
has no body vein unread by the six-pass arc.

**Charge 5 (the [r1..r5] strike system + matrix-surface consistency, final
pass).** Strike census: **136 `~~` tokens − 2 backticked literals (L761,
L763) = 134 markup tokens = 67 balanced spans**; a toggle-parse of the whole
file ends balanced with no dangling opener — the 7 spans r5 added (r4
S-STATUS, §2(iii) frame sentence, §4(ii) gloss, JB-BOX-2 phrase, row 24's
(d) cell, the footer counter line, the dating-record arc line) account
exactly for 60 → 67. No live content sits under a superseded banner; the
r5 strikes all carry correction brackets in place. Matrix-vs-surfaces: the
r5-touched surfaces verified cell-for-cell (§2 above); the F-1 leftover
sweep is clean (`line(C) = w_m(C) = v_{m+1}(C)` grep: 3 hits — the r5
round-block quotation, the struck r2 block, and the r5/F-1 bracket's own
quotation of the removed text; ZERO live unfenced sites). Row 24's (d)
correction verified by my own grep of JB-BOX-2's full extent: no
W2-C1/clause-1 record; the only representative content is JA-BOX-3's
pinned-(P-ell) sentence and the W2-C1a object on the (a1) enumeration's
row-13 line — the struck cell's replacement text is accurate. Arc-status
consistency (the LIFT-PE6 genre): the [r5] S-STATUS, the r5 round block,
§7.3's live CONSUMES bullet, JB-BOX-6 and the sign-off ALL say five passes /
five rounds / counter 0/2 / JB-PE6 next — no stale pointer anywhere; the
dating record carries the full arc through PE5 (0C+5G) → r5 → PE6. The r5
round block's ledger quote verified against
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` L11167 ("LIFT r5 minimal
LANDED … JB PE5 0C/5G incl. THE u ≥ 0 GIFT"). The PE5-history account in
the S-STATUS (0C + 5G, third attempt, both r4 probes replayed bit-for-bit,
F-3 = the gift) is accurate against the PE5 report.

---

## §4. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **All five PE5 findings are genuinely discharged, each at its own
  surface**: F-1 (surface 4's (iii)/(iv) line now scoped, the unrestricted
  parenthetical gone — grep-verified no live residual), F-2 (the gloss
  struck and replaced by the source-true statement — every citation
  verified at [RMG] this pass), F-3 (the discharge displayed WITH the
  honest membership split; both stale sentences struck; forward pointer
  added; 17 carrying surfaces consistent), F-4 (row 20 OUT, reason
  displayed, census reproducible), F-5 (row 24's (d) cell struck and
  corrected to what the box actually carries — grep-verified).
* **The four-line theorem and its corollary re-derive exactly** (charge 1);
  u ≥ 0 + step-(2) + the parity exclusion independently machine-confirmed
  on 598,500 members, 0 violations.
* **The frontier stays FOUR and is now mechanically reproducible** from the
  table (charge 3; all 28 rows re-walked).
* **No §2–§5 identity moved in r5** — I read all 31 deleted lines: every
  deletion is a strike-and-replace of frame/gloss/record text or an arc
  bookkeeping line; the only §4 body movement is the false gloss's
  replacement by a strictly weaker true one.
* **The machine claims of the r5 S-STATUS hold**: md5s intact, note-only,
  `git diff verification/` empty, 4/4 runners exit 0, figures exact.
* **No gate claim, no gr/carrier claim, no density claim anywhere**; the
  counter is 0/2 at every live site; JB-PE6 named as the next attempt
  consistently.

---

## §5. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **F-1** — edit §0M row 11 FIRST (per JB-BOX-6): split the (d3) tie out
   of the `P<q` cell — "(d1)/(d2) on `P<q` + W2-C1; (d3) = JA-VAL at level
   q+1, on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`), the r3/F-4 genre; the
   exclusion bites at q = qcap on the 5 shared_upto < n towers, where the
   runner's own q ≤ shared_upto gate already sits" — then re-derive the
   five carrying surfaces (§3 body (d), §3 ∎ Grade line, grade cap, §7.2
   JB-VTX row, §7.3 W-3, JB-BOX-2's enumeration). Alternative (wider):
   derive the representative-pin discharge once and cite it at BOTH (RES)
   and (d3) — but that reverses r3/F-4's recorded refusal and is the larger
   movement.
2. **F-2** — transcribe the r5 probe's enumeration exactly (h-range,
   j-ranges and whether P_l-capped, a-range, counting unit, chain count),
   or commit the ~40-line enumerator, or replace the bare figure with a
   parameterization a verifier can replay.
3. **m-1** — replace "strictly smaller" with the accurate relation
   ("a SUFFICIENT hypothesis for the proviso at the applied V; the open
   domain shrinks to deg f ≥ deg Φ_{q+1}") and drop "exactly", one sentence
   at §5 and one at §0M column (b).

---

## §6. Divergences from PE1–PE5 (all five read before this pass)

* **All five PE5 findings discharged; none recurs as charged.** The r5 diff
  bred no defect of its own in body mathematics — like LIFT r5, the new
  prose is clean; both this pass's gaps live in what r5 did not touch.
* **F-1 here is the first BODY-FENCE finding since PE4's F-4**, and it is
  the PE3/F-4 disease (a J-A consumption fenced at the citing level instead
  of the consumed level) at the one row whose derivation line no pass had
  re-read against the level-indexed perimeter. The matrix mechanism did not
  fail — the matrix faithfully propagates row 11 everywhere — the CELL was
  filled one level short in r3 and certified by inheritance since.
* **The finding sizes continue to shrink**: PE5's five gaps were a leftover
  parenthetical, a false gloss, a stale frame, an uncounted row and a wrong
  record cell; this pass's are one fence level on one sub-clause nothing
  in-note consumes, one under-transcribed supplementary probe, and one
  wording minor. Nothing found here moves a displayed identity, a grade, a
  census count, or a machine claim.
* **New territory this pass entered** (no earlier pass touched): the §3(d)
  tie-derivation level audit (F-1); exact-reproduction attempt of the r5
  probe (F-2); the full 28-row frontier re-walk under the post-r5 criterion;
  the ledger-quote and arc-status cross-checks at all live sites.

---

## §7. Pass hygiene

Nothing was edited. All four scripts, all committed artifacts and the note
are byte-untouched; the four re-runs regenerate the three `_results.json`
artifacts with zero diff (`git diff verification/` empty). My probes ran
read-only with outputs to /tmp; only `verification/openmath/__pycache__`
was written by the interpreter. `git add` is scoped to this report file
alone; other agents' in-flight files were never touched or staged. Sources
consulted read-only: `RMENGINE_2026-08-08.md` (S2.1/S2.2/L-CELL),
`GRTJA_PROOF_2026-08-08.md` (§1 perimeter, §3.1 JA-VAL, §3.3 JA-GRID),
`grt_jb_checks.py` (jb_shear_vtx), `BRIDGE_ADJUDICATIONS_2026-07-30.md`
(ledger quote), the five PE reports, and the r5 diff.

No leg is NOT-RUN.

— GRTJB-PE6, Fable, fresh context, 2026-08-06 (campaign date 2026-08-08).
This pass returns findings, so it is **not** a clean pass: the acceptance
counter for the note remains **0/2**, and the fourth acceptance attempt has
not landed.
