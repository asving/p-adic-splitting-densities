# GRTJB-PE4 — hostile verification pass on the post-r3 J-B tree-junction note (SECOND ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD**, i.e. the
r0 note (composed 5a72b62, sealed 7f6759d, verdict f5578d0) + r1 (`4c97649`,
`46f9452`) + r2 (`67bf0c4`, `888e293`) + **r3** (`8acb2d1` = §0M matrix +
surfaces 1–5 + F-5/F-2/F-3/F-4/F-6(a)/F-7; `87c553d` = surfaces 6–14 +
F-6(b) + JB-BOX-6 rule + sign-off).
**Scripts re-run (all four):** `grt_jb_checks.py` (sealed) ·
`grt_jb_r1_levelcensus.py` · `grt_jb_printwalk.py` · `grt_jb_printwalk2.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-05 (wallclock). Prior reports **JB-PE1** (1C+9G), **JB-PE2**
(0C+7G) and **JB-PE3** (0C+8G) read in full, and the r3 diffs read, before this
pass formed any judgment. This is the FOURTH hostile reader and the SECOND
acceptance attempt.

---

## §0. VERDICT

**0 CRITICAL, 8 JUSTIFICATION GAPS.**

    GRTJB-PE4 FINDINGS: 0 critical, 8 gaps / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

**The r3 mechanism works and the recurrence class is closed.** All eight PE3
findings are discharged, the 14 surfaces are genuinely regenerated, and I could
not find a fifth instance of the old "body fenced, surface not" disease that ran
PE1/G-9 → PE2/G2-1 → PE3/F-1 + F-1B. **The failure mode moved rather than
vanished:** four of my eight findings are defects of §0M ITSELF — its
derived-claims paragraph contradicts its own row 18 (F-1), its "only three
NO-LEG cells" undercounts by at least one (F-2, the answer to the fourth-cell
charge: **row 4**, the second u ≥ 0 rider), its new `P≤q` arithmetic is false on
**11 of the note's own 16 towers** (F-3), and three regenerated surfaces
disagree with the table under the note's own new governing rule (F-7). That is
one audit target instead of fourteen, which is progress, and it is why none of
these is critical.

The two findings in untouched territory are the sharper ones: **§4(iii)
transfers the per-edge λ_E line laws to v_{m+1} across every tree edge, while
its licensing identity (`line = w_m`, [RMG] L-LINE(iv)) holds only on REDUCED
cells and no internal tree node is reduced** (F-4 — the machine leg agrees with
me: `jb_line` keys the tie at leaves only); and **r3's own new evidence cell
misdescribes `jb_eps`'s quantifier** (F-5 — the code strides `[::2]`/`[::3]` and
caps at `min(3eh+5, 25)`, so "PLAIN integers 0 ≤ V,V′ < 25, a superset of the
lattice instance" is wrong twice and the applied instance is not shown to be
tested).

**All four machine legs reproduce bit-identically, exit 0, all four md5s intact
at HEAD, `git diff verification/` empty** — r3's "note-only, all instruments
byte-frozen" claim HOLDS. **The F-5 byte-compare PASSES**: the quoted (RM-m) box
is character-for-character identical to `RMENGINE_2026-08-08.md` S0.2 across all
11 lines, and the L-CANON three-hypothesis claim is faithful to the source.

---

## §1. MACHINE LEG (mandatory — all FOUR runners RUN, exit 0, artifacts reproduce)

Run from `verification/openmath/`, `python3`, no arguments, nothing edited.

| runner | md5 at HEAD | exit | reproduction |
|---|---|---|---|
| `grt_jb_checks.py` (sealed) | `55f4911eaddd8524fd91368b30ed71bd` **intact** | **0** | 18/18 families GREEN, 6,700 samples, 0 violations, elapsed 0.7 s |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` **intact** | **0** | output identical to committed `_output.txt` |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` **intact** | **0** | 5/5 GREEN, 458 samples, coverage 84/12/72 |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` **intact** | **0** | 3/3 GREEN, 45 xframe / 27 degen / 28 recon, 0 violations |

`git diff verification/` is **EMPTY** after all four runs — the three committed
`_results.json` artifacts regenerated **bit-identically**, `elapsed_s` included.
r3's claim "r3 is NOTE-ONLY and all four scripts plus every artifact are
byte-frozen" **HOLDS**: `git diff 0aa5c41 HEAD` touches
`lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` and nothing else (677 + 147
lines, one file, both commits).

**Sealed-runner figures vs §7.1 (all match):** EXT-GATE 1 · JB-DEV 893 ·
JB-KEYEQ 25 · JB-SHEAR 893 · JB-VTX 893 · JB-ID 34 · JB-TREE 79 · JB-LINE 194 ·
JB-EPS 955 · JB-CM 28 · JB-CREAD 79 · JB-QO 5 · JB-D0 4 · TW-JB 2,480 · teeth
3/3/3/3 all caught. Censuses **scored 104 | boundary 21 | v = 0: 0 | R = 0: 0 |
off-perimeter tree rows 0**.

**Level census vs §7.1/§7.4(A):** m = 1 scored 45 / boundary 0 · m = 2 scored 8 /
boundary 10 (T3A 3, T3B 3, T3C 1, T3D 3) · m = 3 scored 3 / boundary 3 (I4B) ·
reasons R EVAL-FALSE 10, f EVAL-FALSE 3, scope-outs 0 · cross-check 13 + 8 = 21.
**Byte census** identical to PE3's spot-check (I4A/I4B `{1:T,2:T,3:T}`;
T3A/T3C/T3D/T3E `{1:T,2:F}`; I4C `{1:T,2:F,3:F}`; three `{}` = the T.n = 0 QO
shapes).

No leg is NOT-RUN.

---

## §2. FINDINGS

### F-1 — JUSTIFICATION GAP (the matrix's own derived-claims paragraph is self-contradictory, and its (VD-m) column understates JA-RES). §0M's summary point (4) names a §4 row as a (VD-m) consumer and denies in the same sentence that any §2–§4 row rides (VD-m)

§0M, "What the matrix shows that no earlier surface stated", point (4) (L211–212):

> (4) The (VD-m) fence reaches exactly rows 18 (its (C-READ) leg), 21, 22 and
> 23 — nothing in §2–§4 rides it.

**Row 18 IS a §4 row.** The matrix's own row 18 reads
"**JB-TREE(iv)** (RM-m) as the transported instance" with column (c) =
"**YES for the (C-READ) leg** (it transports as §5)", and JB-TREE(iv) is
§4(iv) of this note. Surface 4 (§4's regenerated ∎ Grade line, L1224–1226) says
so explicitly:

>     (iv)          its (C-READ) leg transports as §5 and therefore rides §5's
>                   (VD-m) fence IN FULL

and surface 6 (§7.2's JB-TREE row, L1737) repeats it ("**(iv)**'s (C-READ) leg
additionally rides §5's (VD-m) fence in full"). So the table and two of its
regenerated surfaces assert exactly what the summary sentence denies. This is
the surface-vs-record divergence r3 was built to eliminate, now located inside
the record itself, four lines below the table.

**Second, independent leg: row 5's (c) cell is "—" but JA-RES's own hypothesis
is a (VD-·) hypothesis.** Row 5 (JB-DEV(iii)(RES)) has column (c) = "— ⟨n4⟩",
and ⟨n4⟩ (L191) states:

> (RES) does NOT consume (VD-m) — it is the PER-SLOT law

J-A's actual theorem (`GRTJA_PROOF_2026-08-08.md` L250–251) is:

> **THEOREM JA-RES (per-slot law).** Level m ≥ 2, shared keys below m. IF
> (VD-(m−1)) holds at every on-line digit a_i of A (the PER-DIGIT PROVISO),
> THEN for every attained abscissa i: …

So at read level m = q+1 ≥ 3, (RES) consumes **(VD-(m−1)) = (VD-q) at every
on-line digit** — an instance of column (c)'s own object ("(c) (VD-m) level
fence — J-A §3.4's EVALUATED dictionary"), at level q ≥ 2 where that column
says it is "a HYPOTHESIS". The note *does* record this, but in column (g)
("per-digit proviso at m ≥ 3 (JA-BOX-2)") rather than column (c), and the
consequence is that summary point (4)'s "nothing in §2–§4 rides it" is false a
second time: §2(iii)(RES) at q ≥ 2 rides an evaluated-dictionary hypothesis.

Classification: gap, not critical. The conditionality is on record (row 18's
(c) cell, surfaces 4 and 6, row 5's (g) cell); what is wrong is the ONE sentence
the note offers as the matrix's payload, which a consumer is invited to read as
the authoritative summary of where (VD-m) bites. Given JB-BOX-6's new standing
rule ("if a surface and the table ever disagree, THE TABLE GOVERNS and the
disagreement is a defect to report"), this is a defect the note's own rule
obliges a reader to report.

### F-2 — JUSTIFICATION GAP (charge 1: there is a FOURTH open-proviso-no-leg cell, and it is the second u ≥ 0 rider). §0M claims exactly three; row 4's (GRID) grid/attained-abscissa half is a fourth by the table's own cells

§0M (L205–208):

> **What the matrix shows that no earlier surface stated.** (1) Three cells hold
> an open proviso with NO machine leg beside it — rows 5 (RES), 12 (d4), 22
> (v = 0) — and one of them (row 12) is the u ≥ 0 rider; those three are the
> note's honest evidence frontier.

Row 4 of the same table is:

> | 4 | **JB-DEV(iii)(GRID)**, §2(iii) | **YES** | — | **YES — UNDISCHARGED** | — | YES\* | — | carry half **IND** (`jb_eps` keys JA-GRID(c)); grid/attained-abscissa half **NONE** | W2-L0 consumed |

i.e. column (b) = the UNDISCHARGED u ≥ 0 proviso and column (f) = "grid/
attained-abscissa half **NONE**". By the very criterion the sentence uses — an
open proviso with no machine leg beside it — row 4's grid half qualifies, and it
qualifies with the *strongest* class of open proviso in the note's vocabulary
(carried, discharge owed). The note cannot treat rows 4 and 12 as one cell,
because its own next sentence keeps them apart:

> (3) Exactly two rows consume the u ≥ 0 proviso (4 and 12), and every surface
> must therefore name JB-VTX(d)'s grid content as well as JB-DEV(iii)(GRID).

So "one of them (row 12) is the u ≥ 0 rider" is false as a uniqueness claim:
**both** u ≥ 0 riders have a NONE half, and the honest evidence frontier has
four members, not three. The same over-tightening propagates to §3's machine
bracket (L1103–1105), which says (d4) "is also the **only** sub-clause of
JB-VTX riding the undischarged u ≥ 0 proviso" — true within JB-VTX, but the
adjacent §0M sentence generalises it across the note, where it is not.

Two further cells satisfy the sentence's criterion under the note's own
inclusion of row 5 (whose only open proviso is a *perimeter*, `P≤q`):

* **row 13** (JB-VTX(e), the window clause): (a1) YES\*, (d) **YES — W2-C1a**,
  (f) **NONE** ("none claimed").
* **row 18's (C-W_Q) sub-cell**: (a1) YES, (e) YES, (f) "(C-W_Q) **NONE**" —
  named as no-leg at the grade cap and at §7.2, but excluded from the
  frontier count.

Classification: gap. Direction: the note UNDERSTATES its own evidence frontier
by one to three cells, in a sentence advertised as "what the matrix shows that
no earlier surface stated".

### F-3 — JUSTIFICATION GAP (charge 4: r3's one MATHEMATICAL movement is fenced correctly but DESCRIBED falsely, and the note's own runner refutes the description on 11 of its 16 towers). "`P≤q` excludes exactly the top level q = qcap = shared_upto+1" holds on only 5 roster towers

The re-fence itself is **source-correct** and I confirm it independently:
J-A's perimeter is level-indexed (`GRTJA_PROOF_2026-08-08.md` L69–70,
"Shared-key perimeter at level m: Φ_q^har = φ_{q+1}^cls byte-for-byte for all
q ≤ m−1"), JA-RES is stated at "Level m ≥ 2, shared keys below m" (L250), and
(RES) is JA-RES at m = q+1, so it needs agreement through j = q. **F-4's
disposition is right.** What is wrong is the arithmetic gloss r3 attaches to it
at every regenerated surface. §0M column (a2) (L60–64):

> **(a2) BYTE-EQUAL CHAIN THROUGH q, `P≤q`** … STRICTLY STRONGER than `P<q`;
> the two differ exactly at the top level q = qcap = shared_upto+1, where
> `P<q` holds and `P≤q` FAILS by the definition of shared_upto.

§1 defines `qcap := min(n, shared_upto + 1)`. The identification
`qcap = shared_upto+1` therefore holds only when `shared_upto + 1 ≤ n`. Read off
the note's OWN instrument (`qcap_of` and `GJA.shared_upto`, read-only probe over
`GWP.TOWERS`, the 16-tower roster this note's evidence is built on):

    tower   n  shared_upto  qcap   qcap == shared_upto+1 ?
    T2A–T2G 1      1         1      NO   (qcap = n)
    T3A     2      1         2      yes
    T3B     2      2         2      NO
    T3C     2      1         2      yes
    T3D     2      1         2      yes
    T3E     2      1         2      yes
    T3F     2      2         2      NO
    I4A     3      3         3      NO
    I4B     3      3         3      NO
    I4C     4      1         2      yes

**On 11 of the 16 towers** (T2A–T2G, T3B, T3F, I4A, I4B) `qcap = n ≤
shared_upto`, so `P≤q` holds at EVERY level of the quantified range including
q = qcap, the two perimeters coincide there, and (RES) is excluded at **no**
level. Only 5 towers (T3A, T3C, T3D, T3E, I4C) realise the described split.

The false gloss is not confined to §0M; it is in the r3 text at every site it
was regenerated into, which is what makes it a matrix-and-surfaces defect rather
than a typo:

* §1's [r3, F-4] amendment (L739–742): "The two differ exactly at the top level
  q = qcap = shared_upto+1 … so at that one level per tower r2's single fence
  over-supplied (RES) by exactly one level" — **"one level per tower" is zero
  levels on 11 towers**.
* §2(iii)'s [r3, F-4] bracket (L817–819): "**(RES) on the BYTE-EQUAL CHAIN
  THROUGH q (`P≤q`)**, which is strictly stronger and excludes exactly the top
  level q = qcap."
* ⟨n4⟩ (L189–190): "the two differ exactly at q = qcap, where `P≤q` fails by
  definition".
* Surface 1, the grade cap (L230–231): "**(RES)** on the **BYTE-EQUAL CHAIN
  THROUGH q** — `P≤q`, **one level deeper than r2's fence**".
* Surface 6, §7.2's JB-DEV row (L1734): "one level deeper than r2's fence".
* Surface 13, §7.3 (L1768): "one level deeper than r2's display said".
* Surface 14, JB-BOX-2 (L1553–1554): "`P≤q` (strictly stronger; they differ
  exactly at q = qcap)".

Direction: **conservative** — the note claims MORE conditionality than it has,
so nothing downstream is unsound. Classification: gap, not critical, on two
counts: nothing in §3–§5 consumes (RES) (the note says so and I confirm it), and
the fence `P≤q` is the correct one regardless of how many levels it removes.
But the claim is (a) false on the majority of the note's own roster, (b)
mechanically checkable against the very function the note cites as authoritative
for the other perimeter, and (c) the single new mathematical assertion of the
round, restated at seven sites.

### F-4 — JUSTIFICATION GAP (charge 5, body mathematics no pass has dug: JB-LINE). §4(iii) transfers the per-edge λ_E line laws to v_{m+1} across EVERY tree edge, but the licensing identity line = w_m = v_{m+1} is a REDUCED-CELL identity and no internal tree node is reduced

§4(iii), the whole of the LED-Λ face citation (L1164–1175):

> On reduced cells, line(C) = w_m(C) ([RMG] L-LINE(iv)) = v_{m+1}(C)
> (JA-VAL): THE LEDGER'S LINE FUNCTIONAL IS THE CLASSIFIER'S MacLANE
> ORDINATE. Hence LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the
> complete per-edge polygon bookkeeping of the division in classifier
> coordinates: **promotions raise v_{m+1} by exactly the quantum q_{i+1} > 0,
> correction-main edges are v_{m+1}-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀
> (Y), exits pay w_mΦ_m** ([LED-Λ] S1 table, λ_E column; …)

The premise is correctly restricted ("On reduced cells"); the conclusion is not.
[RMG] S2.1 defines the line as a *bound*, exact only when reduced:

> Its **line** (level-m weight lower bound, exact on reduced cells by
> L-LINE(iv)): line(C) := E_m·w₀(b) + Σ_{l<m} j_l·Γ_l.
> C is **reduced** iff j_l ≤ P_l − 1 for every l;

and [RMG] S2.2's tree makes the reduced cells exactly the LEAVES:

> **The tree.** Nodes are cells. A cell with all j_l ≤ P_l − 1 is an
> **R-leaf**. Otherwise let i := the LOWEST level with j_i ≥ P_i
> (E1-priority) and apply (ID-(i+1)) to Φ_i^{P_i} inside C:

So **every node that has an outgoing edge is by construction NOT reduced**
(it has some j_i ≥ P_i), and for such a node line(C) is only a lower bound for
w_m(C). L-LINE(i)/(ii)/(iii) are accordingly stated as `Δline` laws, never as
Δw_m laws; L-MONO is "line(child) ≥ line(parent)". The step from those to
"promotions raise **v_{m+1}** by exactly the quantum" needs
line = w_m = v_{m+1} at BOTH endpoints of the edge, which the cited lemma
supplies at neither. Nothing in this note, in [RMG] S2/S3, or in LED-Λ S3.E
supplies w_m(C) = line(C) off the reduced cells; LED-Λ's own specialisation is
carefully phrased as "λ_E·J(C) = line(C) **BY DEFINITION of the line**", i.e.
about line, not about w_m.

**The machine leg agrees with me, not with the prose.** `jb_line`
(`grt_jb_checks.py` L509–555) checks the quanta on `line(·)` alone —

    d = line(bc, jc) - line(bp, jp)
    if typ == 'P':  if d != qq[i + 1]: viol(... 'promotion quantum fails')
    …
    for sgn, b, j in leaves[:60]:
        if T.wlev(m, cp) != ln:   viol(... 'leaf line != wlev')
        elif okline and G.vgen(m + 1, cp) != ln: viol(... 'leaf line != vgen')

— and keys the `line == wlev == vgen` tie **only on leaves**, i.e. only where
L-LINE(iv) licenses it. §7.1's JB-LINE row says exactly this ("λ_E quanta per
edge + **leaf** line == wlev == vgen"), and §0M row 17's (f) cell repeats it.
So the note's own evidence surface is scoped correctly and its §4(iii) prose is
not: the machine never tests any v_{m+1} statement at a non-leaf, and cannot,
because the identity is false there in general.

Classification: gap, not critical. What §4(iii) actually establishes — and all
the machine keys — is the per-edge law for the LINE functional, plus the
identification line = w_m = v_{m+1} at the R-leaves (where the division's output
R lives). That is enough for JB-TREE's downstream role; the sentence claiming
per-edge v_{m+1} bookkeeping is an unlicensed strengthening, and §0M row 17's
(e) cell ("**YES** L-LINE(iv), S3.2") records the citation without recording
its reduced-cell restriction. §7.3's W-5 bullet inherits the wording
("the tree/division correspondence with LED-Λ as the bookkeeping").

### F-5 — JUSTIFICATION GAP (r3 introduces a NEW machine-evidence over-claim of exactly the F-2/F-3 genre it was correcting). §0M row 20's (f) cell misdescribes `jb_eps`'s quantifier twice, and the "superset of the lattice instance" claim is not established

§0M row 20 (the cell r3 added to license the JB-EPS application):

> | 20 | **JB-EPS APPLIED at (V,V′) = (λ, γ_{m+1})** (inside §5's display) | … | **IND** — the leg quantifies PLAIN integers 0 ≤ V,V′ < 25, a superset of the lattice instance | — |

repeated at §5 (L1312–1313): "`jb_eps` quantifies PLAIN integers 0 ≤ V,V′ < 25,
a superset of the lattice". The code (`grt_jb_checks.py` L634–637) is:

        Vs = list(range(0, min(3*e*h + 5, 25)))
        for V in Vs[::2]:
            for Vp in Vs[::3]:

Two divergences, both in the direction of MORE claimed coverage:

1. **The bound is `min(3·e·h + 5, 25)`, not 25.** For the many roster levels
   with small (e, h) — e.g. (e, h) = (1, 1), which occurs on T2E, T3E, T3F,
   I4A and I4B — the range is `[0, 8)`, not `[0, 25)`.
2. **The two loops STRIDE.** `Vs[::2]` tests only EVEN V; `Vs[::3]` tests only
   V′ ≡ 0 (mod 3). So V = 1, 3, 5, … are never first arguments and
   V′ = 1, 2, 4, 5, … are never second arguments. The tested set is not
   `[0,25)²` under any reading.

Consequently the cell's operative claim — that the machine leg's quantification
is "a superset of the lattice instance", i.e. contains the applied
(V, V′) = (λ, γ_{m+1}) — is **not established**: the note nowhere shows
λ = w_m(f) is even, γ_{m+1} even less that it is a multiple of 3, nor that
either is below min(3eh+5, 25). Whether the applied instance is exercised at all
is unknown from the note.

This is a gap and not worse for one reason only: **LEMMA JB-EPS has a complete
proof**, and I re-verified its two inputs independently — JA-GRID(c) is
quantified over plain `V, V′ ≥ 0` with no lattice condition
(`GRTJA_PROOF_2026-08-08.md` L216–218, "for V, V′ ≥ 0, s(V) + s(V′) − s(V + V′)
= e·δ, δ ∈ {0,1}", graded "PROVED, unconditional"), and the telescope needs only
`s^wt(β) ≡ ℓ_{m−1}β (mod e_{m−1})`. So the mathematics is fine and the machine
leg is a spot-check whose advertised scope is wrong. Classification: gap. Note
that PE3 described the same range loosely (its F-5 text says "range(0,
min(3*e*h + 5, 25)), i.e. plain integers") and r3 copied the description while
dropping the `min`, so the composer's source for the cell was a verifier's
paraphrase rather than the code — the exact failure mode JB-BOX-6's new rule
("every cell filled from the BODY PROOF") is meant to prevent, applied to a
column whose content is code.

### F-6 — JUSTIFICATION GAP (charge 6, the bracket system). §7.3's SUPERSEDED block has no terminator, so the "NOT supplied" fence list, the r1/F1 downstream notice and the CONSUMES + acceptance-counter line all sit inside a region the note declares NOT AUTHORITATIVE — and none of them is regenerated

r3 opens a superseded region at L1788–1790:

> **[r3 — SUPERSEDED r0/r2 consequence display, retained for the record. NOT
> authoritative; its defects are F-1 (the proviso attached to the expansion half
> only) and F-4 ((RES) at the wrong perimeter).]**

and never closes it. Compare the grade cap, which r3 does bound properly with an
explicit terminator at L320 ("**[r3 — end of the superseded grade cap.]**"), and
§7.2's superseded table, which is bounded by the `### 7.3` heading. Here the
next heading is `### 7.4` at L1834, so the banner covers L1792 through L1833 —
which includes three items that are NOT part of the r0/r2 consequence display
and have no replacement in surface 13:

> **NOT supplied:** W-1's uncollapsed all-orders dictionary (JA-BOX-2),
> W-2's grades (consumed), the J-C block W-6..W-9 (no gr claim;
> BLOCKED-ON-CARRIER-TIE stands), J-D counts/menus (W-10..W-12), W2-OPEN-1.
> The P0 application gate stands.

> **[r1, F1 — what the consequence display now says about (C-READ).** W-5(iii)
> is supplied WITH the corrected perimeter … Downstream units that read
> "unconditional at m ≤ 2" from r0 … must re-read this line.]**

> CONSUMES: [RMG] (ACCEPTED) · [ILN]† (accepted) · W-2 + J-A + LED-Λ at
> attempt grade … Acceptance counter 0/2.

Surface 13 (L1757–1786) regenerates only the "what J-B supplies" half. So on the
note's own reading discipline a consumer of §7.3 is told that J-B's
NOT-SUPPLIED list, its consumption list and its acceptance-counter statement are
non-authoritative record. That is plainly not intended, and it is precisely the
class of surface defect §0M exists to retire. Classification: gap (a markup /
scope defect, no mathematical content moves).

**Everything else in the bracket system CHECKS.** I counted the strike markup
mechanically: **98 `~~` tokens** in the file, of which **2 are literal
backticked mentions** inside r3's own STEP-2 bullet ("struck with `~~` …",
"`~~` cannot nest"), leaving **96 markup tokens = 48 balanced strike spans**;
no line and no span is left open. The 60 lines carrying an odd count are all
multi-line spans with their partner on another line. Every `[r1]`/`[r2]`/`[r3]`
bracket I sampled quotes the superseded text verbatim in place rather than
rewriting it, r3's "`~~` cannot nest" justification for using retained quoted
blocks (grade cap, §7.2 table, §7.3 display) is correct, and I found **no site
where superseded text is consumed as authority** other than the unterminated
region above.

### F-7 — JUSTIFICATION GAP (surface-vs-table disagreements that the note's OWN new standing rule makes reportable). Three places where a regenerated surface and §0M do not read the same

JB-BOX-6's r3 rule (L1594–1601):

> if a surface and the table ever disagree, THE TABLE GOVERNS and the
> disagreement is a defect to report.

Applying it:

**(a) Row 24's (a2) cell vs surface 14.** §0M row 24 (JB-BOX-2 as a matrix row)
records its columns as: "(a1) records rows 3,4,5,8–13,17,18 | (a2) **records
row 5** | (b) records rows 4,12 | (c) records rows 21,22 | (d) records rows
1,8–13,15". But surface 14 — which IS JB-BOX-2's regenerated enumeration
(L1553–1556) — lists **two** rows under `P≤q`:

>     on the BYTE-EQUAL CHAIN THROUGH q `P≤q` …
>         §2(ii)'s byte clause                                    [row 2]
>         §2(iii)(RES) — added in r3, F-4                         [row 5]

Row 24's (a2) cell omits row 2. Symmetrically, row 24's (a1) cell *includes*
row 5, whose own (a1) cell reads "insufficient — see (a2)" and which surface 14
places under `P≤q` only. Also, row 24's (c) cell records rows 21, 22 while
summary point (4) puts the (VD-m) fence at rows 18, 21, 22, 23 — so JB-BOX-2,
the note's carrier box for inherited conditionality, does not record row 18's
(VD-m) rider at all.

**(b) Surface 13 never states (d4)'s perimeter.** §7.3's W-3 bullet (L1761–1774)
enumerates the `P<q` set as "The polygon half (JB-VTX **(a)/(b)/(c) and the
three keyed min ties**) and the (VAL)/(GRID) layers of the expansion half"; it
later mentions (d4) twice (proviso, no leg) but never says (d4) is on `P<q`.
§0M row 12's (a1) cell is **YES**, and surface 14 does list (d4) under `P<q`.
Under "none may omit one", surface 13 omits one.

**(c) JB-BOX-6's own scope sentence over-reaches.** It tells a consumer that
"the grade cap, any ∎ Grade line, any §7.2 row, §7.3, **or any box**" is "a
REGENERATION of that table". Only ONE box (JB-BOX-2, surface 14) was
regenerated in r3; JB-BOX-1/3/4/5/6 were not. Their content is consistent with
the table as far as I checked (JB-BOX-4's fences match row 26's (g) cell;
JB-BOX-5 matches row 27), but the rule's inventory is inaccurate as written.

Classification: gap. Each of (a)–(c) is a record defect, none moves a
mathematical statement, and each is exactly the divergence class §0M was
constructed to make impossible — which is the reason to report them rather than
absorb them.

### F-8 — JUSTIFICATION GAP (charge 3: the F-5 license rests on an object this note never defines, and it addresses only half of the lemma's quantifier)

The restored clauses and the byte-compare **pass** (see §3 below). The
one-line derivation does not fully close. §5 (L1293–1306):

> **THE LICENSE (what F-5 charged). LEMMA JB-EPS below is quantified over
> V, V′ ≥ 0 IN THE LEVEL-m WEIGHT LATTICE, and THEOREM JB-CREAD's display
> applies it at (V, V′) = (λ, γ_{m+1}). Both memberships now follow in one line
> each:**
>
>     λ = w_m(f)  with f ≠ 0        ⇒  λ is the level-m weight of a NONZERO
>                                      polynomial, hence in the level-m weight
>                                      lattice (which contains every value of
>                                      w_m on nonzero polynomials).

Two defects:

1. **"the level-m weight lattice" is never defined in this note.** Grepping the
   whole file, the phrase occurs only at the JB-EPS quantifier (L1343), inside
   this derivation (L1297–1306), and in the u ≥ 0 retraction prose (L877, L892).
   The derivation's entire warrant is the parenthetical "(which contains every
   value of w_m on nonzero polynomials)" — an uncited assertion about an
   undefined set. If that parenthetical is the *definition*, the derivation is a
   tautology and the lemma's quantifier carries no content; if it is a
   *theorem*, it needs a source. Either way the reader cannot check it, and the
   note elsewhere treats the same object as substantive (the u ≥ 0 retraction
   argues about which V "the level-m weight lattice" excludes: "J-A's own
   (e,h) = (2,3), V = 1 ⇒ u = −1 is not excluded by anything this note says").
2. **Only the lattice half of the quantifier is derived.** JB-EPS says
   "V, V′ ≥ 0 in the level-m weight lattice". The display derives membership and
   says "**Both** memberships now follow" — where "both" means λ and γ_{m+1},
   not the two conditions. Neither λ ≥ 0 nor γ_{m+1} ≥ 0 is stated or cited
   anywhere in the license.

Classification: gap, and the smallest in this report — the lemma is true for all
V, V′ ∈ ℤ_{≥0} (JA-GRID(c)'s own quantifier), so the substance is safe and PE3's
alternative repair ("widen the quantifier") would have closed it outright. What
r3 chose instead is a derivation whose only load-bearing step is unanchored.

---

## §3. THE F-5 DISCHARGE (charge 3) — THE BYTE-COMPARE AND THE L-CANON CLAIM BOTH PASS

**The quoted (RM-m) box is BYTE-IDENTICAL to `RMENGINE_2026-08-08.md` §S0.2.**
Machine-compared line for line (note L1268–1278 against RMENGINE L308–318):
**11/11 lines identical, zero character differences.** The three restored clause
strings occur verbatim in the source parenthetical:

    'deg < deg Φ_m'                                            present
    'w_m = γ_{m+1}'                                            present
    'R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}c_m'          present

so the word "verbatim" is now true of §5's recital, which is what PE3's F-5
asked for, and both dropped clauses ((Ĉ-deg), (Ĉ-wt)) are back.

**The L-CANON third-hypothesis claim is FAITHFUL.** The note says (L1288–1291)
"[RMG] L-CANON's three hypotheses are Φ_m MONIC, deg f < deg Φ_m and (Ĉ-deg)".
RMENGINE S0.3's own repair record says exactly that:

> [r1, PE-n4: … and the C2 claim row now records ALL the hypotheses this lemma
> consumes — Φ_m MONIC, deg f < deg Φ_m, deg Ĉ_m < deg Φ_m — per PC-G3.]

**The lattice-membership derivation** is where the discharge is incomplete —
F-8 above. The γ_{m+1} leg's own internal chain is sound as far as it goes:
(Ĉ-wt) gives γ_{m+1} = w_m(Ĉ_m); (Ĉ-read) gives R_{m,γ_{m+1}}(Ĉ_m) = τ_m,
nonzero because c_m = ψ_{m,0} ≠ 0 (the class pin, cited in the r1 hygiene note
and consistent with `jb_cm`'s 28 rows); a nonzero read forces Ĉ_m ≠ 0. That
part I confirm.

---

## §4. CHARGE-BY-CHARGE COVERAGE, AND WHAT SURVIVED

**Charge 1 (the matrix cell by cell).** I checked every row I can key to the
body: rows 1–6 against §2(i)–(iv), rows 7–13 against §3's LEMMA JB-AFF and
clauses (a)–(e), rows 14–18 against §4(i)–(iv), rows 19–23 against §5 and
JB-BOX-1, rows 24–28 against §6's boxes. **Every consumption cell I could key
matches the body's actual consumption** except the two named in F-1 (row 5's
(c), and summary point (4)) and the F-2 count. Specific confirmations:
row 1's (d) matches §2(i)'s W-2 clause-1 sentence; row 2's (d) "—" is
*correct* (on a byte-equal chain Φ_q^har IS φ_{q+1}^cls, so no W2-C1
admissibility is needed — surface 3 says so independently); row 3's
"over 0 ≤ q ≤ qcap" is the runner's literal loop `for q in range(0,
qcap_of(T,G) + 1)`; row 11's "machine-restricted further to q ≤ shared_upto"
is the code's `if q <= L` guard; row 15's SAME sub-leg ⟨n2⟩ and row 1's SAME
sub-leg ⟨n1⟩ are both accurate to the code (I re-read `jb_dev` L216–234 and
confirm `G.P.dev` sits behind `continue`-on-disagreement with a byte-equality
guard, so its violation is unreachable); row 14's "genuinely print-side leg on
the print chain's OWN keys" is accurate (`jb_id` L586–602 runs
`fresh_dev(T.R, G.phi[r], G.phi[r-1])` and checks grid support + shear
constancy). **The three-NO-LEG claim is the answer to the "hunt for a fourth"
charge: there IS a fourth (row 4), and two more borderline (rows 13, 18) — F-2.**

**Charge 2 (surfaces vs matrix).** All 14 surfaces are present and labelled
(1 grade cap + 4 ∎ Grade lines + 7 §7.2 rows + §7.3 + JB-BOX-2 = 14 ✓), each
carries its row citations, and each superseded predecessor is retained. No
surface asserts a fence ABSENT from the table. Two surfaces OMIT a table cell
(F-7(b): §7.3 and (d4)'s perimeter) or disagree with a table cell
(F-7(a): surface 14 vs row 24), and seven surfaces carry the false
`qcap = shared_upto+1` gloss (F-3).

**Charge 4 (the (RES) re-fence).** Split verdict: the FENCE is source-correct
and consistent with J-A's JA-RES hypothesis at m = q+1 (§F-3 opening); the
DESCRIPTION of how it sits inside `qcap_of` is false on 11 of 16 towers (F-3);
and there is no inconsistency with the runner, because the runner keys (RES)
nowhere — which the note states and I confirm by grep over all four scripts
(no family computes a per-slot residual gauge `c_i = z^{−iA}·C_i`).

**Charge 5 (JB-LINE and the assembly).** The λ_E face citation carries the
defect in F-4. The rest of §4(iii) checks: `line(C) = w_m(C)` is [RMG]
L-LINE(iv) verbatim ("**(iv) reduced cells:** w_m(C) = line(C) EXACTLY"); the
four per-edge values quoted (`+q_{i+1}` promotions, `−w_mΦ_m` exits, `0`
correction-main, `≥ E_m (π) / ≥ Γ₀ (Y)` junk) match LED-Λ's S1 table λ_E row
cell for cell, and match `jb_line`'s five assertions cell for cell. The S6/§7.3
assembly of the four identities into the junction statement (W-3 = JB-DEV +
JB-VTX; W-5 = JB-TREE + JB-CREAD, with JB-EPS as the coordinate change) is
otherwise faithful: W-3's "full in CONTENT, not full in q" scoping, W-5's
"(VD-m) ∩ {v ≠ 0}" and "needed at BOTH f and R", the (C-W_Q) no-leg disclosure,
and the NOT-supplied list (modulo F-6's markup problem) all agree with the body.

**Charge 6 (brackets).** 48 balanced strike spans, no superseded text consumed
as authority, one unterminated superseded region (F-6).

---

## §5. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **All eight PE3 findings were applied, and applied honestly.** F-1/F-1B are
  killed structurally (the surfaces now carry the JB-VTX(d4) proviso and the
  JB-TREE(iii)/(iv) perimeter at the grade cap, §7.2 and JB-BOX-2 — I re-grepped
  each); F-2's SAME-COMPUTATION reclassification is accurate to the code at all
  three sites; F-3's "three keyed, (d4) unkeyed" matches `jb_shear_vtx`'s three
  assertions exactly; F-4's fence is source-correct; F-5's recital is verbatim;
  F-6(a)'s "or directly" now reads consistently at **all three** obligation
  sites (§2(iii) L885, the r2 G2-5 bullet L570–576, JB-BOX-2 L1525–1529) —
  PE3's mutual inconsistency is gone; F-6(b)'s purity softening says exactly
  what `PW2-DEGEN` certifies; F-7's `P_i := e_i·g_i` is defined at first use in
  §4(ii) and [RMG] S0.1 is added to the header consumption list.
* **r3's own honesty about r2 is exemplary.** The r2 block's false
  "already consistent" sentence is struck in place and replaced with an explicit
  admission ("THE STRUCK SENTENCE WAS FALSE WHEN WRITTEN, and it is the round's
  honesty defect, not a mere omission … 'All 8 fixed' is a count of hits found,
  not of surfaces made consistent"). No round in this arc has graded itself up.
* **No §2–§5 identity moved in r3.** The r3 diff (`0aa5c41..HEAD`, one file) is
  additive except for strike-and-replace of fence/grade/record text; not one
  displayed equation of JB-DEV, JB-AFF, JB-VTX, JB-TREE, JB-EPS or JB-CREAD is
  touched, and the sole mathematical movement (the (RES) perimeter) is toward
  MORE conditionality, as claimed.
* **JB-CREAD's five-line display re-derived a fourth time**, including the ε′
  match against the now byte-verified [RMG] box and the `w_m(R) = λ + γ_{m+1}`
  pin from (B-READ) = L-CELL(ii) + (C-W_R). Sound.
* **LEMMA JB-EPS re-derived from JA-GRID(c)**, whose statement I read at source
  (`GRTJA_PROOF` L216–226, "PROVED, unconditional") — the telescope is exact and
  the proviso-free status of (c) is correct, so §5's "u ≥ 0 NOT consumed" line
  (surface 5) is right.
* **The u ≥ 0 retraction stands intact** and is stated identically at §2(iii),
  JB-BOX-2 and the r2 block; JA-GRID(a)'s proviso is verbatim J-A's
  (`GRTJA_PROOF` L197–212, including the `(e,h) = (2,3), V = 1 ⇒ u = −1`
  counterexample the note quotes).
* **Every §7.1 figure and census reproduces** from my own runs (§1), and the
  G2-4 roster table, the G2-7 decompositions (66 = 56+2+8, 21 = 13+8,
  458 = 362+96, 45+27+12 = 84) and the walker2 verdicts are unchanged and
  correct.
* **Acceptance-counter honesty is complete and consistent**: the r3 S-STATUS
  line, the r3 block's tail, JB-BOX-6, §7.3's CONSUMES line and the sign-off all
  say 0/2 with three passes run and three repair rounds applied, and all
  correctly record that PE3 was the first acceptance attempt and did not land.
  No gate claim, no gr/carrier claim, no density claim anywhere.

---

## §6. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **F-1** — rewrite §0M summary point (4): the (VD-m) fence reaches rows 18
   (§4), 21, 22, 23 — i.e. §4 DOES ride it — and add (VD-(m−1))-at-every-
   on-line-digit to row 5's column (c) with the m ≥ 3 qualifier, or say in
   column (c)'s definition that it means the dictionary *at the row's own read
   level only*.
2. **F-2** — "FOUR cells hold an open proviso with no machine leg — rows 4
   (the (GRID) grid half), 5, 12, 22 — and TWO of them (4 and 12) are the u ≥ 0
   riders"; decide explicitly whether rows 13 and 18's (C-W_Q) are in or out and
   say which.
3. **F-3** — replace "differ exactly at q = qcap = shared_upto+1" with
   "differ at q = qcap **when qcap = shared_upto+1 < n**; when qcap = n ≤
   shared_upto the two coincide on the whole range (11 of the 16 roster towers)"
   — at all seven sites. The direction of the correction is toward LESS claimed
   conditionality, so it needs the same care as a widening.
4. **F-4** — restate §4(iii) as a LINE law: "promotions raise **line** by
   exactly q_{i+1} > 0 …", and say separately that line = w_m = v_{m+1} holds at
   the R-leaves (L-LINE(iv), JA-VAL), which is where the division's output sits
   and where `jb_line` keys the tie; or supply w_m(C) = line(C) for non-reduced
   cells and cite it.
5. **F-5** — row 20's (f) cell: "`jb_eps` tests V ∈ 2ℤ ∩ [0, min(3eh+5,25)),
   V′ ∈ 3ℤ ∩ same — a SPOT-CHECK, not a superset of the applied instance; the
   lemma's proof, not this leg, is what licenses (λ, γ_{m+1})".
6. **F-6** — add "**[r3 — end of the superseded consequence display.]**" before
   the "NOT supplied" paragraph, as the grade cap already does.
7. **F-7** — sync row 24's (a2)/(a1)/(c) cells with surface 14; add (d4)'s
   `P<q` to §7.3's W-3 bullet; narrow JB-BOX-6's "or any box" to JB-BOX-2 (or
   regenerate the other boxes).
8. **F-8** — define "the level-m weight lattice" once at first use (§1 or §5),
   with a citation, and add the ≥ 0 half — or take PE3's one-word route and
   widen JB-EPS to V, V′ ∈ ℤ_{≥0}, which JA-GRID(c) already supports.

---

## §7. Divergences from PE1/PE2/PE3 (all three read before this pass)

* **PE3's eight findings are all genuinely discharged**; none recurs. In
  particular the F-1/F-1B recurrence class is closed: r3's regeneration did
  reach the grade cap, JB-BOX-2, all seven §7.2 rows and §7.3, and I could not
  find a fifth site of the old disease. **The matrix mechanism works.**
* **But it relocated the failure mode rather than eliminating it.** Four of my
  eight findings (F-1, F-2, F-3, F-7) are defects *of the table and of its own
  summary*, i.e. the disease moved from "surfaces disagree with the body" to
  "the single record disagrees with itself and with its regenerations". This is
  a better place for it to live — one audit target instead of fourteen — and it
  is the reason none of these is critical.
* **New in this pass, in territory no earlier pass entered:** the §4(iii)
  line-vs-v_{m+1} transfer (F-4, charge 5 — PE3 explicitly listed §4's LED-Λ
  citation as unexamined), the `jb_eps` stride/bound (F-5), the numeric
  refutation of the `qcap = shared_upto+1` gloss on 11 of 16 towers (F-3), and
  the unterminated §7.3 superseded block (F-6).
* **PE3's F-5 diagnosis is confirmed and its recommended repair was NOT the one
  taken**; the taken route is sound in outline but leaves F-8.
* **Everything PE1/PE2/PE3 certified clean and that I re-tested is still
  clean** (§5).

---

## §8. Pass hygiene

Nothing was edited. All four scripts, all committed artifacts and the note are
byte-untouched; the four re-runs regenerate the three `_results.json` files with
**zero diff** (`git diff verification/` empty). Only
`verification/openmath/__pycache__` was written by the interpreter, and my
probes went to `/tmp`. `git add` was scoped to this report file alone; the
GRTJC PE2 verifier's `GRTJC_passPE2_report.md` was never read, touched or
staged.

No leg is NOT-RUN. (The Bash tool was intermittently refused on the
model-availability path during this pass; every leg was retried and completed —
all four scripts, the roster `qcap_of`/`shared_upto` probe, the strike-markup
count and the (RM-m) byte-compare all ran to completion.)

— GRTJB-PE4, Fable, fresh context, 2026-08-05. This pass returns findings, so
it is **not** a clean pass: the acceptance counter for the note remains
**0/2**, and the second acceptance attempt has not landed.
