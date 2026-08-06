# GRTJB-PE5 — hostile verification pass on the post-r4 J-B tree-junction note (THIRD ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD**, i.e.
r0 (5a72b62/7f6759d/f5578d0) + r1 (4c97649, 46f9452) + r2 (67bf0c4, 888e293) +
r3 (8acb2d1, 87c553d) + **r4** (`ae0acdf` = F-1..F-8 dispositions: the §4(iii)
LINE-LAW re-scope with the NOT-TAKEN route recorded, the 4-member NO-LEG
census with rows 13/18 adjudicated OUT, the qcap gloss corrected at 9 sites,
row 20 rewritten to the strided code, the §7.3 superseded-region terminator,
the row-24/JB-BOX-6 syncs, and the 𝒲_m lattice definition).
**Scripts re-run (all four):** `grt_jb_checks.py` (sealed) ·
`grt_jb_r1_levelcensus.py` · `grt_jb_printwalk.py` · `grt_jb_printwalk2.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-06 (wallclock). Prior reports **JB-PE1** (1C+9G), **JB-PE2**
(0C+7G), **JB-PE3** (0C+8G), **JB-PE4** (0C+8G) read in full, and the r4 diff
(`ae0acdf`, 372 insertions / 47 deletions, one file) read line by line, before
this pass formed any judgment. This is the FIFTH hostile reader and the THIRD
acceptance attempt.

---

## §0. VERDICT

**0 CRITICAL, 5 JUSTIFICATION GAPS.**

    GRTJB-PE5 FINDINGS: 0 critical, 5 gaps / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

**Every r4 disposition I could machine-check is exact.** The F-3 correction
reproduces bit-for-bit from the runner's own `qcap_of`/`shared_upto` (the
exclusion bites on exactly T3A/T3C/T3D/T3E/I4C, 5 of 16; the other 11
coincide over the whole range); the F-5 probe reproduces bit-for-bit (56
roster scored rows, the applied (λ, γ_{m+1}) sampled on exactly 4 — T2A and
T3D at m = 1, λ ∈ {0, 4}, γ₂ = 9 — and every m ≥ 2 row has γ_{m+1} beyond the
range bound); the F-4 NOT-TAKEN record is accurate at both anchors
(HigherNewton tex ~1012 IS the valuation proposition, and T3E's P₁ = e₁·g₁ =
1·1 = 1 realizes the interior-period degeneracy in-roster); and the **F-8
lattice definition is source-CORRECT** — I verified both descriptions of 𝒲_m
against [RMG] S2.1/S3.2 (L-CELL(i) verbatim gives the forward inclusion,
L-LINE(iv) plus π^a·∏Φ_l^{j_l} cells the converse, the S2.1 degree telescope
the class membership) and both positivity claims (E_m = e₀⋯e_{m−1} ≥ 1;
Γ_l = γ_{l+1}·∏e_t ≥ 1 via the h ≥ 1 class pin, [RMG] S4 census line), so
**𝒲_m ⊆ ℤ_{≥0} does close the quantifier's ≥ 0 half**.

The five gaps: **one leftover site of the F-4 disease inside a surface r4
itself re-scoped** (surface 4's (iii)/(iv) line still glosses the JA-VAL
consumption with the unrestricted `line(C) = w_m(C) = v_{m+1}(C)`, three
lines above its own r4 R-LEAVES-ONLY item — F-1); **one false-as-literally-
read gloss in the body vein no pass had re-derived** (§4(ii)'s "every node is
a sum of reduced cells" fails at every exit-bound node, whose degree is
≥ deg Φ_m, where L-CELL's hypothesis fails — F-2); **the new 𝒲_m definition
contradicts two retained honesty sentences** (both say J-A's (e,h) = (2,3),
V = 1 counterexample "is not excluded by anything this note says" — the r4
definition excludes it by parity, and in fact u ≥ 0 holds on ALL of 𝒲_m in
four lines from the displayed description — F-3); **the recount is silent on
row 20**, which r4's own F-5 edit turned into a candidate fifth frontier
member (F-4); and **row 24's (d) cell records a JB-BOX-2 content the box does
not carry** (F-5).

**All four machine legs reproduce bit-identically, exit 0, all four md5s
intact at HEAD, `git diff verification/` empty** — r4's "note-only, all
instruments byte-frozen" claim HOLDS. The strike system remains balanced
(60 spans post-r4, toggle-parse clean, no dangling opener).

---

## §1. MACHINE LEG (mandatory — all FOUR runners RUN, exit 0, artifacts reproduce)

Run from `verification/openmath/`, `python3`, no arguments, nothing edited.

| runner | md5 at HEAD | exit | reproduction |
|---|---|---|---|
| `grt_jb_checks.py` (sealed) | `55f4911eaddd8524fd91368b30ed71bd` **intact** | **0** | 18/18 families GREEN, 6,700 samples, 0 violations, elapsed 0.7 s |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` **intact** | **0** | output **diff-identical** to committed `_output.txt` |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` **intact** | **0** | 5/5 GREEN, coverage 84 / 12 / 72 |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` **intact** | **0** | 3/3 GREEN, 45 xframe / 27 degen / 28 recon, 0 violations |

`git diff verification/` is **EMPTY** after all four runs (0 lines). Figures
vs the note, all match: EXT-GATE 1 · JB-DEV 893 · JB-KEYEQ 25 · JB-SHEAR 893 ·
JB-VTX 893 · JB-ID 34 · JB-TREE 79 (125 with chambers) · JB-LINE 194 ·
JB-EPS 955 · JB-CM 28 · JB-CREAD 79 · JB-QO 5 · JB-D0 4 · TW-JB 2,480 · teeth
3/3/3/3 caught · censuses **scored 104 | boundary 21 | v = 0: 0 | R = 0: 0 |
off-perimeter tree rows 0** · byte census identical to the note's examples
(I4A/I4B `{1:T,2:T,3:T}`; T3A/T3C/T3D/T3E `{1:T,2:F}`; I4C `{1:T,2:F,3:F}`;
three `{}` = the T.n = 0 QO shapes) · level census m = 1: 45/0 · m = 2: 8/10 ·
m = 3: 3/3, reasons 10 R + 3 f EVAL-FALSE, 0 scope-outs.

**The two r4 probes, re-run independently by this pass (read-only, /tmp):**

* **F-3 probe — EXACT.** `qcap == shared_upto+1` on exactly {T3A, T3C, T3D,
  T3E, I4C} (all with `shared_upto < n`); on the other 11 towers (T2A–T2G,
  T3B, T3F, I4A, I4B) `qcap = n ≤ shared_upto` and the two fences coincide
  over the whole range. Every number in §0M column (a2)'s r4 bracket is right.
* **F-5 probe — EXACT.** Replaying `jb_cread`'s own scoring logic over the
  16-tower roster: **56 scored rows**; the applied instance (λ, γ_{m+1}) lies
  in `jb_eps`'s strided sample (`V ∈ Vs[::2]`, `V′ ∈ Vs[::3]`,
  `Vs = range(0, min(3eh+5, 25))`) on **exactly 4** — T2A m = 1 (λ = 0, 4) and
  T3D m = 1 (λ = 0, 4), all with γ₂ = 9 — and on **zero** of the 11 m ≥ 2
  scored rows (γ_{m+1} ≥ the range bound on every m ≥ 2 eligible (T, m)).
  Every number in §0M row 20's r4 cell is right.

No leg is NOT-RUN.

---

## §2. FINDINGS

### F-1 — JUSTIFICATION GAP (charge 1: the r4 re-scope left ONE live site carrying the unrestricted identity, inside a surface r4 itself lists as re-scoped). Surface 4's (iii)/(iv) line still writes `line(C) = w_m(C) = v_{m+1}(C)` with no reduced-cell restriction

The §4 ∎ Grade line (surface 4, LIVE r3 text, L1431–1436):

>     (iii)/(iv)    at levels **m ≤ qcap** only (`P<q` read at level m), since
>                   both consume JA-VAL (line(C) = w_m(C) = v_{m+1}(C); the
>                   v_{m+1}-values of the R and Q digits), which J-A grades
>                   "PROVED unconditionally ON THE SHARED-KEY PERIMETER"; off it
>                   the v_{m+1}-reading of the print side is a different object.

Three lines below, the same surface's new r4 item says the opposite scope:

>     (iii)         … [r4, F-4]
>                   the per-edge laws are laws of the LINE functional; the
>                   identification line = w_m = v_{m+1} is asserted at the
>                   R-LEAVES ONLY (L-LINE(iv) reduced cells + JA-VAL) …

and §0M row 17's (e) cell — the governing record — reads "L-LINE(iv)
**REDUCED CELLS ONLY** = the R-leaves **[r4, F-4]**". So within ONE
regenerated surface the identity appears once unfenced and once fenced, and
the unfenced occurrence disagrees with the table. I swept every live site of
the identity (`grep`, 12 hits): all others carry the reduced-cell/R-leaves
scope or are struck; **L1432 is the unique live leftover.** The r4 F-4
disposition claims "RE-SCOPED at §4(iii), row 17, the grade cap, the §4 ∎
Grade line, the §7.2 JB-TREE row and §7.3's W-5 bullet" — the §4 ∎ Grade line
received the new (iii) item but its (iii)/(iv) joint line was not touched.
Under JB-BOX-6's standing rule ("if a surface and the table ever disagree,
THE TABLE GOVERNS and the disagreement is a defect to report") this is a
defect the note's own rule obliges a reader to report. Classification: gap —
the correct scope is stated three lines below and in the table; a consumer of
the parenthetical alone re-imports exactly the transfer F-4 retracted.

### F-2 — JUSTIFICATION GAP (charge 4, the largest body vein no pass had re-derived: §4(i)/(ii)). §4(ii)'s closing gloss "every node is a sum of reduced cells" is FALSE at every exit-bound node, and its L-CELL citation is used beyond L-CELL's stated hypothesis

No earlier pass re-derived §4(i) or §4(ii)'s prose proofs (PE3 re-derived
JB-ID, the (ID-(i+1))-as-development sentence only; PE1 audited the machine
leg's code). I re-derived both against `RMENGINE_2026-08-08.md` S2.1/S2.2/
S0.3/S4.2. **§4(i) is SOUND** and **§4(ii)'s operative content is SOUND**
(details in §3 below). The defect is (ii)'s final sentence (L1341–1344):

> The tree is the classifier's division arithmetic made cell-local; the
> blueprint's "each cell = a set of expansion slots" is L-CELL: every node is
> a sum of reduced cells = multiadic expansion slots (iterated JB-DEV at
> levels m−1, …, 0).

[RMG] L-CELL(i) is quantified with a degree hypothesis:

> **Lemma L-CELL (cell decomposition; B-READ).** (i) Every 0 ≠ x ∈ O[x] with
> **deg x < deg Φ_m** is a finite sum of DISTINCT reduced cells …

and that hypothesis FAILS at in-tree nodes the tree necessarily contains:
a node taking a Φ_m-exit has j_{m−1} ≥ P_{m−1} (S2.2: "**Φ_m-exit**
(i = m−1)"), hence deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m by the S2.1 degree
telescope; and a sum of reduced cells has degree < deg Φ_m (S2.1: "then
deg C < deg Φ_m"), so **such a node is not a sum of reduced cells at all** —
the sentence is false as literally read, not merely uncited. (Initial cells
can violate the hypothesis too: their bound is j_l ≤ 2P_l − 2.) The
parenthetical's own weaker reading — iterated development bounds the
exponents BELOW the reducing level — is the true statement; the E1-priority
structural remark ([RMG] S2.2) supplies exactly it for exit cofactors ("the
sub-cell S := b∏_{l≤m−2}Φ_l^{j_l} is REDUCED AT LEVEL m−1").

Classification: gap, not critical, on the arc's own precedent (PE4's F-4, a
strictly stronger unlicensed transfer in the same section, was graded a gap):
nothing downstream consumes the gloss — JB-TREE(ii)'s load-bearing content is
the edge typing plus JB-ID plus L-EXACT, all of which I re-derived sound, and
`jb_tree` keys reassembly plus **leaf** reducedness only. The same
hypothesis-scope point touches, more mildly, the r4 F-4 bracket's own
parenthetical "(L-CELL(i): w_m = min line over the reduced cells of the
decomposition …)" when applied to nodes of degree ≥ deg Φ_m.

### F-3 — JUSTIFICATION GAP (charge 3's flip side: the new definition contradicts two retained sentences that argue about the same object). §2(iii) and JB-BOX-2 still say J-A's V = 1 counterexample "is not excluded by anything this note says" — the r4 definition excludes it

§2(iii)'s G2-5 retraction block (L1070–1073), retained un-annotated by r4:

> and J-A's own counterexample lives at small positive V
> ((e,h) = (2,3), V = 1 ⇒ u = −1), which nothing in this note excludes from the
> level-m weight lattice. So the proviso may well hold at every site — this note
> does not show it.

JB-BOX-2 (L1782–1783), same:

> J-A's own (e,h) = (2,3), V = 1 ⇒ u = −1 is not excluded by
> anything this note says

Both sentences were true before r4. As of r4 the level-m weight lattice is a
DEFINED object — 𝒲_m = {E_m·a + Σ_{l<m} j_l·Γ_l : a ∈ ℤ_{≥0},
0 ≤ j_l ≤ P_l − 1} — and that definition **does** exclude V = 1 at any read
with (e_{m−1}, h_{m−1}) = (2, 3): e_{m−1} divides E_m and every Γ_l with
l ≤ m−2, while Γ_{m−1} = γ_m = e_{m−1}w_{m−1}Φ_{m−1} + h_{m−1} is odd and
≥ 3, so V = 1 forces j_{m−1} odd, whence V ≥ γ_m ≥ 3 — contradiction.
(Machine-confirmed on the m = 1 instance: 𝒲₁ = {2a + 3j₀} =
{0, 2, 3, 4, 5, …}, and 1 ∉ 𝒲₁.) Stronger, and in the same four lines from
the displayed description: for EVERY V ∈ 𝒲_m one has V ≡ j_{m−1}·h_{m−1}
(mod e_{m−1}), so s_m^wt(V) = j_{m−1} mod e_{m−1} ≤ j_{m−1} and
V − s_m^wt(V)·h_{m−1} ≥ (j_{m−1} − s_m^wt(V))·h_{m−1} ≥ 0, i.e. **u ≥ 0
holds on all of 𝒲_m** (machine-confirmed: zero lattice members with u < 0).
So the "what is and is not known" frame at both sites is stale in a
machine-checkable way: the two obstacles the r2 retraction named (units;
J-A's small-V counterexample) are BOTH cleared by the r4 definition, and what
actually remains open is only the site hypothesis that JA-GRID(a)'s
quantified-window V's lie in 𝒲_m.

Classification: gap. Direction: **conservative** — the note claims LESS than
its own displayed definition supplies, and the CARRIED, DISCHARGE-OWED status
of the proviso remains defensible (the window-membership hypothesis is
genuinely not established here). But the F-8 block's own header names the
§2(iii) prose as a site that "argues about" the object, and neither sentence
was re-derived against the new definition — the round's own standing rule
(edit the record first, re-derive every touched surface) applied to the
DEFINITION only forward into §5, not sideways into the two sites that reason
about the same set. A small adjacent defect, same genre: the phrase's first
textual use (§2(iii), L1071) precedes the §5 definition with no forward
pointer.

### F-4 — JUSTIFICATION GAP (charge 2: the recount is not closed under r4's own edits). The FOUR-member frontier sentence adjudicates rows 13/18 OUT but is silent on row 20, which r4's own F-5 rewrite turned into a candidate fifth member

The r4 frontier sentence (§0M summary point (1)):

> (1) FOUR cells hold an open proviso with NO machine leg beside it —
> rows 4 …, 5 (RES), 12 (d4) and 22 (v = 0) … ADJUDICATED AND EXCLUDED, with
> the reason stated: row 13 (JB-VTX(e)) and row 18's (C-W_Q) sub-cell are
> NO-LEG cells but carry no OPEN proviso …

The rows-13/18 adjudication itself is SOUND (see §3). But in the same round,
r4's F-5 rewrote row 20's evidence cell to:

> … a SPOT-CHECK of the LEMMA, not a superset of anything. The applied
> instance: IN the sampled set on 4 of the 56 roster scored rows ONLY …
> NOT-SAMPLED on the other 52, including EVERY m ≥ 2 row … Instance-keyed
> evidence: NONE on those 52 …

while row 20's column (c) reads "inherits row 21's context" — and row 21's
(c) is "**YES — the governing fence**", the (VD-m) hypothesis, which the
note's own vocabulary classes as an open hypothesis at every m ≥ 2 (the same
class that puts row 22 IN the frontier). So under the sentence's criterion a
mechanical reader now finds a fifth candidate cell — open (inherited) proviso,
"instance-keyed evidence: NONE" on 52 of 56 rows — that is neither counted
nor adjudicated. A defensible OUT-reason exists (the license rides the
lemma's PROOF at the derived membership, as the cell itself says; and row
21's end-to-end `jb_cread` leg exercises the applied ε-collapse implicitly on
every scored row, since the five-line display passes through it), but the
note does not say it, and r4's own F-2 standard was that borderline cells get
their adjudication DISPLAYED. Classification: gap — the count "FOUR" is not
mechanically reproducible from the post-r4 table without a row-20 ruling.

### F-5 — JUSTIFICATION GAP (charge 5, residual surface-vs-table disagreement surviving the F-7 sync). Row 24's (d) cell says JB-BOX-2 "records rows 1,8–13,15" for the W2-C1 restriction; the box carries no such record

§0M row 24, column (d) (unchanged by r4):

> records rows 1,8–13,15

I grepped JB-BOX-2's full extent (L1743–1827) for `W2-C1`, `clause 1` and
`representative`: the box never mentions the W2-C1 representative
restriction — the only "representative" occurrences are JA-BOX-3's orbit
sentence ("all displays at the pinned (P-ell) representative") and the
W2-C1a object f = Φ_{q+1}^har inside the (a1) enumeration's row-13 line,
which is clause-(e)-specific. Rows 1 and 15 (JB-DEV(i), JB-TREE(i)) appear in
the box's perimeter enumeration only under "on NO key perimeter", with no
representative record. So the (d) cell asserts a record the box does not
carry; r4's F-7(a) synced (a1)/(a2)/(c) "with surface 14 and with summary
point (4)" and left (d) unexamined. Under JB-BOX-6's rule, the table governs
and the disagreement is reportable. Classification: gap (record defect; no
mathematical content moves — the W2-C1 conditionality is correctly carried at
rows 1/8–13/15 themselves and at surfaces 2/3).

---

## §3. CHARGE-BY-CHARGE COVERAGE, AND WHAT SURVIVED

**Charge 1 (the r4 edits, each verified at its own surface).**

* **F-1 (r4)** — summary point (4) now agrees with row 18, surfaces 4 and 6,
  row 24's (c) cell and JB-BOX-2's new (VD-m)-rider sentence (all five sites
  read "rows 18, 21, 22, 23"; §2–§3 clean of the level-m dictionary in the
  table ✓). Row 5's new (c) cell is faithful to JA-RES's own statement
  ("(VD-(m−1)) at every on-line digit" = the per-digit proviso, an
  evaluated-dictionary hypothesis at m−1 ≥ 2) and is consistently echoed at
  ⟨n4⟩, the §2 ∎ Grade line, §7.2's JB-DEV row and §7.3's W-3 bullet. The
  grade cap's JB-DEV bullet carries the proviso under its JA-RES name without
  the (VD-(m−1)) identification — the conditionality is carried, so I do not
  score it.
* **F-3 (r4)** — probe-verified EXACT (§1). All 9 carrying sites now state
  the shared_upto < n condition or point at column (a2); `grep` finds no
  live residual of the old gloss ("differ exactly at", "one level per tower",
  "excludes exactly the top level" — all hits struck).
* **F-4 (r4)** — the re-scope is correctly worded at §4(iii)'s body bracket,
  row 17 (both (e) and (f) cells), the grade cap, §7.2's JB-TREE row and
  §7.3's W-5 bullet; the one leftover is F-1 of this report. The re-scoped
  per-edge laws match [RMG] L-LINE cell for cell (promotion quantum
  h_{i+1}∏e_t > 0; correction-main Δline = 0; junk ≥ E_m / ≥ Γ₀; exit pays
  w_mΦ_m — all re-checked against S3.2's displays). **The NOT-TAKEN record is
  accurate**: HigherNewton tex ~1012 is the proposition "The natural
  extension of v_r to K(x)* is a discrete valuation" (multiplicativity via
  the semigroup-homomorphism composition), it is NOT among the note's header
  print anchors, and T3E realizes P₁ = e₁·g₁ = 1 in-roster (probe: e =
  [2,1,2], g = [2,1,1]). The direction claim ("[RMG] gives only
  line(C) ≤ w_m(C) off reduced cells") is right: L-MONO's edge signs are
  nonnegative, so every reduced descendant has line ≥ line(C) and the
  L-CELL(i) min is ≥ line(C). **Nothing downstream still assumes the
  internal-edge transfer**: JB-TREE(iv) and §5 consume w_m/v_{m+1} of R and Q
  through JA-VAL (a theorem for ALL nonzero polynomials on the perimeter, no
  reducedness needed), and I checked every LED-Λ/λ_E consumption site
  (JB-BOX-4, row 26, §7.3 W-5, the §4 machine bracket) — all speak of line(·)
  or of leaf readings, except the F-1 leftover.
* **F-5 (r4)** — probe-verified EXACT (§1); the §5 echo of the old "superset"
  description is struck too ✓.
* **F-6 (r4)** — the terminator closes the §7.3 superseded region, matching
  the grade cap's genre; the three live [r4, F-6] bullets in surface 13
  reproduce the content of the superseded NOT-supplied list, the r1/F1
  (C-READ) notice and the CONSUMES line, with the arc counters updated and
  nothing dropped (I compared item by item).
* **F-7 (r4)** — row 24's (a1)/(a2)/(c) now match surface 14 and summary
  point (4) exactly (I re-read all three); §7.3's W-3 bullet now names (d4)
  and (e); JB-BOX-6's inventory is narrowed to JB-BOX-2 and is now true.
  Residual: the (d) cell, F-5 of this report.
* **F-8 (r4)** — source-verified SOUND, see charge 3 below.
* **Arc honesty** — the r4 S-STATUS supersedes all three struck predecessors;
  counter 0/2 stated consistently at the S-STATUS, the r4 block tail, the
  live CONSUMES bullet, JB-BOX-6 and the sign-off; the r4 block's account of
  PE4 (0C+8G, second attempt, did not land) is accurate; "md5s re-verified
  2026-08-06 and `git diff verification/` empty" holds at my re-run; both
  probe transcriptions are bit-exact against my independent replications.

**Charge 2 (the census and the rows-13/18 adjudication).** The displayed
OUT-reason is sound and matches the table: row 13's only conditionality
columns are (a1) YES\* and (d) **YES — W2-C1a** — consumption of W-2 at its
grade, not an undischarged hypothesis; row 18's (C-W_Q) sub-cell rides (a1)
`P<q` and (e) [RMG] ACCEPTED — a perimeter plus an accepted consumption. The
IN-members all carry genuine open hypotheses (u ≥ 0 for rows 4/12; JA-RES's
per-digit proviso at m ≥ 3 for row 5; the (VD-m) hypothesis for row 22), so
the open-proviso / consumption-at-grade distinction is coherent and applied
consistently across rows 1–19 and 21–28. The one cell the distinction is NOT
applied to is row 20 (F-4 of this report). I also checked for further
candidates: row 6 (displayed fence, no proviso), row 7 (unconditional), row
15's 8-chamber-walks NONE sub-part (consumption at grade only) — all rightly
outside.

**Charge 3 (the 𝒲_m definition).** Verified against `RMENGINE_2026-08-08.md`:

* S2.1 defines cell, line(C) := E_m·w₀(b) + Σ_{l<m} j_l·Γ_l, reduced :=
  j_l ≤ P_l − 1 ∀l, and "then deg C < deg Φ_m by the degree telescope" —
  so reduced cells are in the class quantified by the first description. ✓
* Forward inclusion: L-CELL(i) verbatim — "Every 0 ≠ x ∈ O[x] with deg x <
  deg Φ_m is a finite sum of DISTINCT reduced cells …, with w_m(x) = min line
  over its cells" — so every w_m value on the class IS a reduced-cell line
  value with a = w₀(b) ∈ ℤ_{≥0}. ✓
* Converse: L-LINE(iv) verbatim ("**(iv) reduced cells:** w_m(C) = line(C)
  EXACTLY"), and every parameter tuple (a, j⃗) is realized by the reduced cell
  π^a·∏Φ_l^{j_l} (deg 0 < d₀, w₀(π^a) = a). ✓
* ≥ 0 half: E_m = e₀⋯e_{m−1} ≥ 1 ✓; Γ_l = γ_{l+1}·∏_{l<t<m}e_t with
  γ₁ = h₀ ≥ 1 and γ_{j+1} = e_jw_jΦ_j + h_j ≥ h_j ≥ 1 (h ≥ 1 is the class
  pin, cited in [RMG] S4's census: "needs only h ≥ 1, the class pin") ✓ — so
  every element is a nonnegative-integer combination and **𝒲_m ⊆ ℤ_{≥0}**,
  which does make "V, V′ ≥ 0" follow from membership. The license's two
  membership legs both check: λ = w_m(f) with §5's own deg f < deg Φ_m
  hypothesis (the r4 text now says "of the class" ✓), and γ_{m+1} = w_m(Ĉ_m)
  via (Ĉ-wt) with Ĉ_m ≠ 0 via (Ĉ-read) + the class pin (re-confirmed, as
  PE4 did). The definition's collision guard (script 𝒲 vs §1's roman
  W_m = w_mΦ_m) is stated twice. The residue is F-3 of this report — the
  definition's consequences were not propagated to the two retained sentences
  that argue about the same set.

**Charge 4 (the untouched body vein: §4(i)/(ii) re-derived in full).**

* **§4(i) — SOUND.** L-EXACT verbatim gives f·Ĉ_m = R₀ + Q·Φ_m with
  deg R₀ < deg Φ_m and (R₀, Q) = the canonical pair by L-CANON, whose three
  hypotheses (Φ_m monic; deg f < deg Φ_m; deg Ĉ_m < deg Φ_m) are all in §4's
  setting + the restored (Ĉ-deg) — row 15's (e) cell records the L-CANON
  dependence correctly. T-TERM is consumed on T-scope(m) exactly as fenced
  (the initial cells of S2.1 satisfy the window bounds j_l ≤ 2P_l − 2 (+1 at
  l = 0), so they are window cells; and the note's "W-WIN not consumed
  (window-free legs only, as in [RMG])" matches [RMG]'s own W-WIN display
  paragraph). The identification with the print's division step is exact:
  the φ_{m+1}-adic 0-th digit and once-divided cofactor of f·Ĉ_m at the
  representative φ_{m+1} = Φ_m^har ARE (R, Q) by uniqueness of division by
  the monic Φ_m, and JB-DEV(i) (quantified over all nonzero f, applied to
  the product) supplies print = harness digit-for-digit. The clause's
  PERIMETER-FREE grading is right: its only fences are W2-C1/W2-C3 and
  [RMG]'s scope, all carried in row 15.
* **§4(ii) — operative content SOUND, one false gloss (F-2).** The
  edge-typing sentence matches S2.2's child definitions one for one:
  promotion child (j_i −= P_i, j_{i+1} += 1) = the carry of the multiadic
  development (the "1 at abscissa P_i" digit of JB-ID's list); Φ_m-exit
  (i = m−1) = one quotient summand; correction children (sign −, coefficient
  b·c_d L-NORM-split, exponents j_l + a_{d,l}, j_i −= P_i − e_ik) = the
  remainder write substituting the key's lower development digits, with the
  L/π-junk/Φ₀Y-junk split as displayed in L-NORM. JB-ID's own proof stands as
  PE3 verified. The one defect is the closing L-CELL gloss (F-2).

**Charge 5 (matrix + surfaces as a system, post-r4).** Every r4-touched
surface re-checked against its rows: grade cap (rows 1–23 fences ✓), §2 ∎
Grade line (rows 1–6 ✓ incl. the r4 (RES) riders), §4 ∎ Grade line (rows
14–18 — the F-1 leftover), §7.2's JB-DEV and JB-TREE rows (✓), §7.3's W-3 /
W-5 / three new F-6 bullets (✓, and the NOT-supplied and CONSUMES contents
agree with row 28 and the header consumption list), JB-BOX-2 (✓ incl. the
new rider sentence; the (d)-column residual is F-5), JB-BOX-6 (✓ now
accurate). Summary points (1)–(4) agree with the table except the row-20
silence (F-4). Strike system: 122 `~~` tokens − 2 backticked literals = 120
markup tokens = **60 balanced spans** (48 at PE4 + 12 added by r4); a
toggle-parse of the whole file ends balanced with no dangling opener. No
superseded region is unterminated; no live content sits under a superseded
banner (the F-6 terminator sits after the old CONSUMES line, and all three
live items are regenerated above it).

---

## §4. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **All eight PE4 findings were applied, and every machine-checkable one is
  exact** (§1's two probes; the 9-site F-3 sweep; the row-24 sync at
  (a1)/(a2)/(c); the terminator; the JB-BOX-6 narrowing; the definition).
* **PE4's F-4 diagnosis is confirmed at source a second time**: L-LINE(iv) is
  the only equality clause and it is reduced-cells-only; L-LINE(i)–(iii) are
  Δline laws for every edge — the re-scoped §4(iii) now says exactly this.
* **The rows-13/18 OUT adjudication is sound** (charge 2, §3).
* **The 𝒲_m definition is sound and closes the ≥ 0 half** (charge 3, §3);
  both its positivity side-claims (E_m ≥ 1, Γ_l ≥ 1) are true at source.
* **§4(i) re-derived in full — SOUND** (charge 4, §3): the first pass in this
  arc to re-derive it.
* **§4(ii)'s edge typing re-derived in full — SOUND** except the F-2 gloss.
* **No §2–§5 identity moved in r4 except the F-4 re-scope**, which is a
  strict narrowing: I read all 47 deleted lines of the r4 diff; every
  deletion is a strike-and-replace of fence/gloss/record text, and the only
  body-proof movement is §4(iii)'s struck sentence, replaced by a weaker one.
* **The r4 S-STATUS's history and every count in it are accurate** (four
  passes 1C+9G / 0C+7G / 0C+8G / 0C+8G; four rounds; two probes; both
  transcribed exactly).
* **Every §7.1 figure and census reproduces from my own runs** (§1), and the
  four md5s are intact at HEAD.
* **No gate claim, no gr/carrier claim, no density claim anywhere**; the J-C
  germ's conditionality notice is now stated LIVE in surface 13.

---

## §5. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **F-1** — restate surface 4's (iii)/(iv) parenthetical to the scoped form:
   "(the leaf reading line = w_m = v_{m+1} for (iii), row 17; the
   v_{m+1}-values of the OUTPUT digits R and Q via JA-VAL for (iv), row 18)".
2. **F-2** — scope the gloss: "every node OF DEGREE < deg Φ_m is a sum of
   reduced cells (L-CELL); exit-bound nodes decompose below the top instead
   (the S2.2 structural remark), and the R-leaves are the expansion slots" —
   or simply state it of the R-leaves and the division output.
3. **F-3** — re-derive the two retained sentences against the r4 definition:
   either display the four-line "u ≥ 0 on 𝒲_m" consequence and restate the
   open residue as the window-membership site hypothesis alone, or at
   minimum strike "is not excluded by anything this note says" at both
   sites (it is excluded, by parity, at exactly J-A's instance). Add a
   forward pointer at §2(iii)'s first use of the phrase.
4. **F-4** — adjudicate row 20 explicitly, either direction, with the reason
   displayed (the natural OUT-reason: the (VD-m) proviso is row 21's, which
   has the end-to-end IND leg, and the license rides the lemma's proof).
5. **F-5** — either add the W2-C1 record to JB-BOX-2 (one sentence naming
   rows 1, 8–13, 15) or blank row 24's (d) cell to "—" and let rows 1/8–13/15
   carry it themselves.

---

## §6. Divergences from PE1–PE4 (all four read before this pass)

* **All eight PE4 findings are genuinely discharged**; none recurs as
  charged. The matrix mechanism continues to hold: I found NO instance of the
  original body-vs-surface disease class, and the F-1 leftover here is a
  finer grain — one cell inside an already-regenerated surface, exactly the
  "frontier moved into the record's own precision" trajectory PE4 named.
* **New territory this pass entered** (no earlier pass touched): §4(i)'s
  composition proof and §4(ii)'s edge-typing / slot gloss (F-2); the
  interaction of the r4 definition with the u ≥ 0 retraction prose (F-3);
  row 20's post-r4 status under the frontier criterion (F-4); row 24's (d)
  column (F-5).
* **The finding sizes are strictly shrinking across the arc**: PE4's
  smallest finding (F-8) became a sound definition; this pass's findings are
  one leftover parenthetical, one gloss sentence, two record cells and one
  stale honesty frame. Nothing found here moves a displayed identity, a
  fence, a grade or a machine claim.
* **PE4's observation that the composer sourced a cell from a verifier's
  paraphrase (its F-5) did not recur**: both r4 probe transcriptions were
  taken from code/probe output and reproduce exactly.

---

## §7. Pass hygiene

Nothing was edited. All four scripts, all committed artifacts and the note
are byte-untouched; the four re-runs regenerate the three `_results.json`
artifacts with **zero diff** (`git diff verification/` empty, 0 lines). My
probes ran read-only with outputs to /tmp; only
`verification/openmath/__pycache__` was written by the interpreter. `git add`
is scoped to this report file alone; `WELDMASTER_2026-08-08.md` /
`weldmaster_checks.py` (another agent's in-flight work) were never read,
touched or staged.

No leg is NOT-RUN.

— GRTJB-PE5, Fable, fresh context, 2026-08-06 (campaign date 2026-08-08).
This pass returns findings, so it is **not** a clean pass: the acceptance
counter for the note remains **0/2**, and the third acceptance attempt has
not landed.
