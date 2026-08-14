# EFF-HE3-s2of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/HE3_PROOF_2026-08-08.md` (1853 lines).

**HOME range:** source lines **1276–1853** inclusive, per `runs/qgen/sweep_manifest.txt` row 32 (`HE3|lean/notes/openmath/HE3_PROOF_2026-08-08.md|1276|1853|s2of2`). That covers: §S7 the six boxes (HE3-BOX-1, -2, -3, -4, -4b, -6, -5) · §S8 the sealed battery · §S9 the verdict with Q1–Q5, HE-BND and the machine-leg summary · §S9′ the `[r1]` supplementary leg P1–P4 with its coverage note · **the post-PE3 dated correction (M-1)** · **the 2026-08-12 A5 wave: the header plus five dated corrections R8-1…R8-5 and the verification parenthetical**. Earlier text (lines 1–1275) is shard 1's HOME and is used ONLY to resolve material homed here.

**HEAD blob hash:** `79bbbb638c39cf4a9658e466210626bf5d6c90a5` (clean in the working tree; last touched by commit `62400944`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). Temporary IDs `EFF.HE3.s2of2.<nn>`.

**GENRE: BOX/LEDGER + APPEND-STACK.** `grep -c '\tag{'` = **0** over the whole note. Where shard 1 is prose proof with in-place strike-through, this range is **records and appends**: six honest boxes, a battery description, a scored verdict, a supplementary leg, and two dated append blocks. **The strike-through mechanism survives only at `.01`** (HE3-BOX-1's grade line); everything after the post-PE3 divider is dated-append discipline.

### Governing effective-text record

**FREEZE PREDICATES (rule 21 — three, all stated or exercised in this range):**

**(F1) The body's freeze BEGINS in this range.** Before PE3, repairs were in place (shard 1 §1). The switch is at line 1589:

> “The body above, §S1 (iii) included, stays BYTE-FROZEN; the correction lives here.”

re-asserted at 1631–1632:

> “Everything above this heading is byte-untouched by this append.”

**(F2) INSTRUMENT-FREEZE — the §S8 battery, byte-frozen through every round**, with the one exception fully accounted: `he3r1_supp.py`'s docstring changed at `[r2]`, and **both md5s are displayed** (1494–1500):

> “runner md5
> 93681e8d47d447dcbfd46db0ddfe0c55 **[r2 2026-08-09, F-4: docstring-only
> fix — the sympy/Bareiss slip corrected and the P4 caveat added; the r1
> runner md5 was 9cd132a8ce174f5703542757675f7960; the [r2] re-run's
> stdout is BYTE-IDENTICAL to the committed r1 output and the results
> JSON is content-identical, GREEN, 0 violations]**, output md5
> 65ed06e49f4c54abf1b143513633f143”

**This is the most completely accounted instrument change in the sweep**: old hash, new hash, reason, and a byte-identical-stdout certificate.

**(F3) CONSUMER-PIN FREEZE** (shard 1 §1) — three displays byte-frozen because HE6/HE7 pin them. Not exercised in this range, but it is why `.05`'s disclosure discipline and `.27`'s “the frozen fence stands” reasoning read as they do.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1276–1853 read in source order**, with `[r1]`/`[r2]` tags already landed in place (lines 1276–1573) and the two dated append blocks (1577–1853) applied as riders at the units they name. **Six riders land on shard-1 units; two land within this range** (`.17`'s HE-BND table and `.29`'s own bullets). §7 lists both directions.

### Scope split (rules 7 + 17)

**A. ABSORPTION / supply SET.** This range supplies (i) the note's **honest boxes** — what is NOT proved; (ii) the **machine evidence** for the μ ≤ 3 headline; and (iii) **three genuinely new lemmas landed by append**: LEMMA HE3-4U (`.30`), LEMMA HE3-4D1 (`.31`), plus R8-1's recursive DECIDED criterion (`.29`), and two display replacements (R8-4 at `.32`, R8-5 at `.33`). **Two of the five A5 corrections NARROW HE3-BOX-6** — the only box-narrowing events in the note.

**B. APPEND / consumption PROTOCOL scope — what HE3 lands on other notes.** **Nothing**, in either shard. HE3's protocol is *report, don't append* (shard 1 `.06`). No dated consumption append is claimed landed on any consumer, and none is invented here.

**C. INBOUND CORRECTIONS RECEIVED — two streams, both landing in this range:**

| # | Source | Landing form | Count | Targets |
|---|---|---|---|---|
| 1 | Fable PE3 (`HE3_passPE3_report.md`) | dated append | 1 MINOR (M-1) | shard 1 `.12` |
| 2 | sol certification A5 (2026-08-12), re-adjudicating the R8 chain read (`runs/residues/R8_he3_output.log`) | dated appends | **5, all REAL** | shard 1 `.01`, `.17`, `.25`, `.32`, `.33`, `.37`, `.38`; in-range `.06`, `.17`, `.29` |

**A NOTE ON AN UNRECORDED OUTBOUND EDGE (compiler finding, rule 10).** HE3's own CONSUMER TRACE (shard 1 `.06`) lists four consumers: HE6, HE7, GENHN, GENIND. **It omits T2.** `spec/EFF-T2.md` `EFF.T2.25` records that T2's `(MP1′)` obligation is **RETIRED**, and its DERIVATION rests on four certifiers, the first being **`HE3-A-PROOF`** (`grep -cF 'HE3-A-PROOF' T2_SIGMA_LADDER_MASTER_2026-08-12.md` = **65**): “`HE3-A-PROOF` transports the refined sub-block over the same stage ring”. **That is HE3's stage-α passage at lines 1149–1166 verbatim** (shard 1 `.34`): “Apply the inductive hypothesis to the sub-block: it is the label-class of a multiplicity-m system over the SAME stage ring, with the same (e₁, f₁)”. **HE3 names neither T2 nor `(MP1′)` anywhere** — `grep -c 'MP1'` = **0**, `grep -c 'T2'` = **0**. So T2's retirement of a standing obligation consumes an HE3 passage that HE3's own consumer trace does not know about. Recorded at §3.2 and OPEN-CALL 3; nothing invented.

### Resolution rules applied

1. Lines 1276–1853 supply the HOME material, read in source order.
2. **Appends never edit; they quote and rider.** Both append blocks say so with an explicit byte-freeze sentence.
3. **Two A5 corrections are LICENSES that narrow HE3-BOX-6** (R8-2 proves branch (i); R8-3 proves the `D′ = 1` case); three are replacements or provenance-riders. All five carry “awaiting sol discharge-confirmation”.
4. **Obligation-shrinking is tracked explicitly** — see §4's NON-IMPORTS and `.06`'s CHAIN, because the box's content at HEAD is strictly smaller than as displayed.
5. Shard-1 material is a resolver only; §S1–S6's statements are not re-emitted.
6. Every commit hash verified with `git cat-file -t`; every artifact verified present; hashes absent from the note marked **UNPINNED** (rule 23).

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; strike-through reproduced exactly; every unit carries `FORM:`. The four source tables in range (§S9's Q3 dictionary, Q4's census tie, HE-BND's window profile, and R8-4's piecewise display) are emitted per rule 14 — the ASCII blocks **twice** (verbatim, then `[TABLE]`), each with a compiler-computed rule-22 arithmetic audit cross-checked against every other number in the note that should match.

---

## 2. Statement inventory

### EFF.HE3.s2of2.01  [scope-record] · SERIES: HE3-GRADE-ARC, member 3 of 4

**CANONICAL STATEMENT:** verbatim, lines 1278–1294.

**FORM:** bulleted bold-headed box with an in-place strike-through.

> “* **HE3-BOX-1 (grade).** ~~Attempt grade 1/2~~ **[r1] Attempt grade 0/2
>   on the μ ≤ 3 statement** — the old 1/2 counted a Codex pass adjudicated
>   in the composer's own context (now preserved at
>   `CODEX_HE3PE1_2026-08-08.md`), which the orchestrator's counter does
>   not; the first counted fresh-context pass (Fable PE1 @ 7950ee4)
>   returned NOT CLEAN (2 CRITICAL at f₁ ≥ 2), repaired by the [r1]
>   round; the second (Fable PE2 @ 6d0ff09) returned NOT CLEAN
>   (2 GAP + 3 MINOR, 0 CRITICAL — the r1 repairs and the core lemmas
>   HELD; fresh e₁ ≥ 2 ∧ f₁ ≥ 2 route GREEN 7/7), repaired by the [r2]
>   round (§S0″); PE3 is next. μ ≥ 4 is BOXED, not graded. THEOREM HE3.A and COROLLARY HE3.B inherit the
>   MINIMUM grade over their supplier stack: {GENHN 0/2 (battery GREEN),
>   GENIND 0/2, W-12 0/2 (PE3 owed), GRTJC/JC-LOAD 2/2 (NOT consumed
>   here), W-11 2/2 (not consumed), classical}. Every consequence is a
>   CONDITIONAL STRUCTURE at exactly that stack. **The one improvement
>   over GENHN's own σ position: HE3 does not consume LEMMA GENHN-4, so
>   the W-9 weld face (GENHN-BOX-2) is absent from the σ chain** — it
>   survives only inside GENHN's COUNT laws.”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26) twice over.**
(a) **“PE3 is next” and “Attempt grade 0/2”** — PE3 ran CLEAN and moved the counter to **1/2** (`.26`). SERIES `HE3-GRADE-ARC`: member 1 = the title/status block (shard 1 `.02`, 0/2); member 2 = the `[r2]` record (shard 1 `.07`, 0/2); **member 3 = this box** (0/2); **member 4 = the post-PE3 append (`.26`, 1/2 — TERMINAL)**. **The arc stops at 1/2; HE3 is NOT accepted.**
(b) **The supplier stack has moved.** GENHN is now **ACCEPTED 2/2** (its post-PE4 record, `spec/EFF-GENHN-s2of2.md` `.27`); GENIND is at 1/2 per GENHN's `[e2]` S10 refresh. Under the box's own **minimum-grade rule**, the binding minimum is now HE3's own 1/2 and W-12's 0/2. `SUPERSESSION KIND: as-of scoping`.
(c) **The strike-through records a grade being LOWERED**, not raised — the only such event in this sweep. The reason is the decorrelation rule: “a Codex pass adjudicated in the composer's own context … the orchestrator's counter does not [count]”.
(d) **The weld-face claim is confirmed from outside.** `runs/qgen/WELD_FACE_AUDIT.md` designates GENHN-4 layer 1 as the corpus's one live weld face, and `spec/HYPOTHESIS_LEDGER.md` records “HE3 explicitly declines GENHN-4, so the σ chain carries HYP.81 without carrying HYP.148” ✓ **verified.**

**DERIVATION:** Grade declaration.

**RESOLUTION TRACE:** statement 1278–1294 · prior members 3–20, 120–139 (shard 1) · terminal member 1579–1583 (`.26`) · supplier movement `GENHN_PROOF` 1941–1955.

XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — count **3** · `GENHN-BOX-2` — count **5**.
XREF: `GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**.
XREF: `W11_PROOF_2026-08-08.md:W-11` — count **18**.
XREF: `W12_PROOF_2026-08-08.md:W-12.D` — count **19**.
XREF: `CODEX_HE3PE1_2026-08-08.md:HE3` — count **15**.
PINS: `7950ee4` ✓ · `6d0ff09` ✓.

**TEETH:** NONE (grade declaration).

---

### EFF.HE3.s2of2.02  [scope-record]  — HE3-BOX-2 (the embedded-genre certification perimeter)

**CANONICAL STATEMENT:** verbatim, lines 1295–1302.

**FORM:** bulleted bold-headed box.

> “* **HE3-BOX-2 (embedded-genre certification perimeter).** Inherited
>   verbatim from GENHN-BOX-4/S11.F: at an embedded genre read through an
>   ambient window, the stage digits are determined only below explicit
>   per-coordinate floors, so the set of leaves an AMBIENT window
>   certifies is strictly smaller than the stage window suggests. This is
>   a statement about window data, not about THEOREM HE3.A (whose leaf is
>   stage data). The battery gates its σ legs at that perimeter on
>   embedded rows and measures the uncertified tail as diagnostics.”

**CONDITIONALITY:** A clean inheritance with an explicit fence (“a statement about window data, not about THEOREM HE3.A”). **Its supplier is GENHN's S11.F, which is derived rather than merely observed** (`spec/EFF-GENHN-s2of2.md` `.20`), so the inheritance is of a proved perimeter. Untouched by every append (verified). **One gap:** the box says “The battery gates its σ legs at that perimeter **on embedded rows**”, but **HE3's battery has no embedded rows** — `.03` lists only full-side genres, and HE3-BOX-4b records “no embedded n = 7 row”. So the gating clause is **vacuous for this note's own instrument.** Recorded as source defect 1.

**DERIVATION:** Inherited; derived at GENHN S11.F.

**RESOLUTION TRACE:** statement 1295–1302 · supplier `GENHN_PROOF` 1352–1377, 1777–1798 · the vacuity 1321–1333 (`.05`).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN-BOX-4` — count **3** · `S11.F` — count **10**.

**TEETH:** **`signed vacuity disclosure`** — the tooth the box names (HE-T-CERT, the embedded uncertified tail) is **OWED and never wired** (`.05`). Disposition: inherited perimeter, unexercised here.

---

### EFF.HE3.s2of2.03  [scope-record]  — HE3-BOX-3 (machine coverage)

**CANONICAL STATEMENT:** verbatim, lines 1303–1312.

**FORM:** bulleted bold-headed box.

> “* **HE3-BOX-3 (machine coverage).** Rows exercise: the full-side genre
>   E3 = (Q; 2, 1, 3; h) at (p, N, h) with p ∈ {2, 3} (full windowed
>   enumeration, census tied to GENHN's committed E3 totals) and
>   p ∈ {5, 7} (constructed slope-aligned loci — the only place |K^×| ≥ 3
>   makes the 3-label stage type (1,1)³ realizable at f₁ = 1). NOT
>   exercised by machine: f₁ ≥ 2 stage genres at μ = 3 (F3/E13, visibility
>   floor N ≥ 7), μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch
>   and the stage-CS recursion first bite), d ≥ 2 ambients, and the
>   char-p side of the resultant leg (see HE3-BOX-4). The PROOFS are
>   uniform in all of these; the gap is machine-side and named here.”

`[TABLE]` — the coverage ledger transcribed:

| Dimension | EXERCISED | NOT exercised |
|---|---|---|
| genre | full-side `E3 = (Q; 2,1,3; h)` only | `f₁ ≥ 2` at μ = 3 (F3/E13, visibility floor N ≥ 7) |
| multiplicity | μ = 3 (and μ = 2 by containment) | **μ ≥ 4** — where HE3-4's ramified branch and the stage-CS recursion first bite |
| prime | p ∈ {2,3} full enumeration; p ∈ {5,7} constructed loci | — |
| ambient depth | d = 1 | d ≥ 2 |
| characteristic | both, for reader/census | **char-p side of the resultant leg** — no PARI oracle (HE3-BOX-4) |

**CONDITIONALITY:** **This box is the reason every f₁ ≥ 2 repair in shard 1 can say “invisible to the sealed battery”**, and it is the coverage-hole sentence quoted at nine PROOF-ONLY rows across both shards. **Partially closed post-seal by additive legs**: `he3r1_supp.py` P2/P3 run `f₁ ∈ {2,3}` sweeps (`.21`, `.23`) and `he3_pe2fresh.py` runs the first `e₁ ≥ 2 ∧ f₁ ≥ 2` geography — **so the arc's coverage exceeds the sealed battery's, and the box's own sentence stays true about the sealed rows.** `SUPERSESSION KIND: as-of scoping`. **μ ≥ 4 remains unexercised by anything.**
**One claim is FALSE as stated at f₁ ≥ 2**: “The PROOFS are uniform in all of these” — at `μ ≥ 4` the ramified branch (ii) is boxed, not proved, so the proofs are *not* uniform in μ. The box's own next clause names branch (ii) as unexercised, so the two sentences sit in tension. Recorded as source defect 2.
**Why p ≥ 5 is needed for the 3-label type** is a genuine content point: the type `(1,1)³` needs three distinct residual roots in `K^× = F_p^×`, hence `|F_p^×| = p − 1 ≥ 3`, i.e. `p ≥ 5` ✓ **arithmetic verified.**

**DERIVATION:** Coverage record.

**RESOLUTION TRACE:** statement 1303–1312 · additive legs 1490–1573 (`.19`–`.25`) · the μ ≥ 4 box 1334–1368 (`.06`).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.CLASS` — count **7** (the genre notation).

**TEETH:** The box IS the coverage statement. **Disposition: `signed vacuity disclosure` for every f₁ ≥ 2, μ ≥ 4, d ≥ 2 and char-p-oracle claim in the note.**

---

### EFF.HE3.s2of2.04  [scope-record]  — HE3-BOX-4 (characteristic coverage of the machine leg)

**CANONICAL STATEMENT:** verbatim, lines 1313–1320.

**FORM:** bulleted bold-headed box.

> “* **HE3-BOX-4 (characteristic coverage of the machine leg).** The
>   reader, the norm identity and the σ dictionary are characteristic-free
>   as PROVED (§S3–S6 use only the substitution identity R_λ(Z + s) and
>   ultrametric facts). The MACHINE leg runs both characteristics for the
>   reader/census, but PARI's `factorpadic` σ-oracle exists only on the
>   ℤ_p side (an oracle asymmetry every prior unit in this program
>   inherits), so the char-p rows are scored against the reader plus the
>   internal resultant identity, not against an independent oracle.”

**CONDITIONALITY:** **An honest asymmetry disclosure, and it is corpus-wide** (“an oracle asymmetry every prior unit in this program inherits”) — GENHN's own §S11.C makes the same disclosure (“ORACLE: PARI legs on all Zp sinks”). **The proof-side claim is qualified by shard 1 `.27`'s PE1-F4 repair**: the characteristic-freedom is at the *residue* level, since binomial coefficients do appear in the recentering expansion. That qualification is not repeated here. Recorded as source defect 3.
**Note the scoring consequence:** char-p rows are scored against **the note's own reader plus its own resultant identity** — i.e. self-consistently, not against an independent oracle. That is a real weakening and the box says so.

**DERIVATION:** Coverage disclosure.

**RESOLUTION TRACE:** statement 1313–1320 · the proof-side qualification 757–776 (shard 1 `.27`) · §S9's ℤ_p-only rows 1390–1395 (`.09`).

**TEETH:** **`signed vacuity disclosure`** for every char-p σ claim. Disposition: the char-p side has no independent oracle anywhere in the note.

---

### EFF.HE3.s2of2.05  [instrument-record]  — HE3-BOX-4b (SEALED-VS-DELIVERED)

**CANONICAL STATEMENT:** verbatim, lines 1321–1333.

**FORM:** bulleted bold-headed box.

> “* **HE3-BOX-4b (SEALED-VS-DELIVERED — disclosed, not papered over).**
>   The runner docstring sealed at commit 1 promised (i) both
>   characteristics, (ii) five teeth (HE-T-UNDET / -SIG / -NODE / -PSI /
>   -CERT), and (iii) an n = 7 embedded slice. The run delivered: ℤ_p rows
>   only; FOUR teeth wired (UNDET, SIG, CAP — the last one NEW, added when
>   the reader bug of LEMMA HE3-5 was found, and it is the strongest of the
>   four — plus NODE); no embedded n = 7 row. Furthermore **HE-T-NODE as
>   coded does not test what its name claims** (it reports how many
>   floor-dropped members remain inside the node rather than asserting that
>   the parse breaks), so it should be read as a diagnostic, not a tooth.
>   HE-T-PSI (corrupted slope set) and HE-T-CERT (embedded uncertified
>   tail) are OWED. Nothing in §S3–S6 depends on the missing rows; this is
>   machine coverage, and the verdict below is scored only on what ran.”

**CONDITIONALITY:** **The most severe instrument disclosure in the sweep, and it is entirely self-administered.** Four distinct shortfalls, each named:
(i) both characteristics promised, **ℤ_p only delivered**;
(ii) five teeth promised, **four wired** — and the four are not the five promised (CAP replaces PSI/CERT);
(iii) an n = 7 embedded slice promised, **none delivered**;
(iv) **one of the four wired teeth is MIS-SPECIFIED** — “HE-T-NODE as coded does not test what its name claims … read as a diagnostic, not a tooth”.
`SUPERSESSION KIND: none` — this is a disclosure, not a correction. **`stale self-description` (rule 20) applies to the sealed docstring itself**, which promises what was not delivered.
**Net wired teeth that ARE teeth: THREE** (UNDET, SIG, CAP). §S9's Q5 nonetheless reports “all wired teeth fired”, which is true of the four as wired ✓ but a reader counting teeth must use three. Recorded.
**The exculpating clause is honest and checkable**: “Nothing in §S3–S6 depends on the missing rows” ✓ — the missing rows are coverage, and shard 1's proofs cite no machine result as a premise ✓ verified.

**DERIVATION:** Instrument disclosure.

*Arithmetic audit (rule 22).* Promised teeth: UNDET, SIG, NODE, PSI, CERT = **5** ✓. Delivered: UNDET, SIG, CAP, NODE = **4** ✓. Of these, NODE is mis-specified ⟹ **3 genuine** ✓. Owed: PSI, CERT = **2** ✓. And `5 − 4 + 1(CAP, new) = 2` owed ✓ consistent. **The accounting closes.**

**RESOLUTION TRACE:** statement 1321–1333 · Q5's scoring 1448–1461 (`.16`) · CAP's origin 1231–1236 (shard 1 `.37`'s preamble).

XREF: `HE3_PROOF_2026-08-08.md:HE3-BOX-4b` — self-count **3**.
XREF: `HE3_PROOF_2026-08-08.md:HE-T-CAP` — self-count **2**.

**TEETH:** This unit IS the teeth-accounting. **Disposition: `disclosed non-repair` (PSI, CERT owed) + `stale self-description` (the sealed docstring, and HE-T-NODE's name).**

---

### EFF.HE3.s2of2.06  [scope-record]  — HE3-BOX-6 (THE ONE SURVIVING GAP)

**CANONICAL STATEMENT:** verbatim, lines 1334–1368.

**FORM:** bulleted bold-headed box with a two-item consequence list and an identified repair route.

> “* **HE3-BOX-6 (THE ONE SURVIVING GAP — found by this unit's own review,
>   before any hostile pass; it localizes to μ ≥ 4, so μ = 3 is
>   unconditional).** LEMMA HE3-4's branch (ii) (a side of dv-slope
>   λ = u/ℓ with ℓ ≥ 2 AND residual degree d ≥ 2) is the only place the
>   argument leaves the ground it stands on. The reason is sharp: **no
>   element of R has non-integer dv** (dv is ℤ-valued on R), so NO test key
>   of the form Φ′ + w, w ∈ R, can sit at such a side's height, and the
>   peel of §S6.2 has nothing to recenter on. The note's substitute is the
>   ramified base change O ↝ O₂ = O[Π]/(Π^ℓ − π), which rescales dv by ℓ
>   and makes the height integral. That step is stated too cheaply:
>   **Φ′ need not remain irreducible over O₂** (it typically does not, when
>   gcd(ℓ, e₁) > 1), so R ⊗ O₂ need not be a DVR, and both the SLOT LEMMA
>   and LEMMA HE3-1's norm computation — which assume a DVR stage ring —
>   are not available verbatim on the other side of that base change.
>   SCOPE OF THE DAMAGE, exactly: the branch is reachable only when
>   ℓd ≤ μ with ℓ ≥ 2, d ≥ 2, i.e. **μ ≥ 4**, i.e. degree
>   n ≥ e₁f₁μ ≥ 8. Hence
>   - THEOREM HE3.A and [GENHN-HE(μ)] are **UNCONDITIONAL for μ ≤ 3** —
>     which is exactly the first-live case of GENHN's box (n = 6, 7) —
>     and unconditional for every degree n ≤ 7;
>   - for μ ≥ 4 (degrees n ≥ 8) COROLLARY HE3.B rests on this branch and
>     must be read as CONDITIONAL on it. The counting failure mode it must
>     exclude is concrete: with ℓ = 2, d = 2 and R_λ = (Z−s₁)(Z−s₂), the
>     two labels each need class size D′ℓ = 2D′, and the degree count alone
>     permits one class to be empty while the other carries two Galois
>     orbits.
>   IDENTIFIED REPAIR ROUTE (not executed here): enlarge the test family
>   from degree-D′ recenterings Φ′ + w to **test polynomials of higher
>   degree** sitting at fractional heights — the resultant
>   v(Res(f, Ψ)) = Σ_ρ Σ_{ξ : Ψ(ξ)=0} v(ρ − ξ) separates labels at
>   half-integer heights as soon as Ψ has degree D′ℓ with roots on the
>   side. This is the higher-order Montes construction, and it is the
>   natural completion of §S6's family; what it needs is the analogue of
>   LEMMA HE3-1 for a higher-degree test polynomial, i.e. the slot lemma at
>   Ψ's roots. That is a genuine further step, not a rewording.”

**CONDITIONALITY:** **This is the charge's named item. The compiled state, exactly as the note and its appends leave it:**

**(1) The box's TITLE claim (“THE ONE SURVIVING GAP”) was FALSE for the whole pre-A5 period, because §S6.2 said BOTH base-change branches were boxed.** The A5 verification note (1830–1833) names it: “§S1's branch-(ii)-only reservation (L350–353) vs §S6.2's "BOTH are stated too cheaply" (L1049) confirmed as **the internal contradiction**”.

**(2) R8-2 makes the title claim TRUE by proving branch (i).** Lines 1691–1695, the charge's cited site:

> “The assertion in §S6.2 that BOTH base-change branches remain boxed is
> superseded for branch (i). **Only the ramified branch (ii) remains in
> HE3-BOX-6.**”

and its closing (1730–1734): “Therefore §S6.2 branch (i) is proved, not boxed. The phrase “both branches below are therefore to be read as BOXED” is corrected to “branch (ii) alone is BOXED.” **COROLLARY HE3.B's single μ ≥ 4 reservation is consequently again accurate**: it is the ramified fractional-slope branch of HE3-BOX-6.”

**(3) R8-3 supplies the box's own missing derivation.** The box writes “i.e. degree n ≥ e₁f₁μ ≥ 8” — which needs `D′ ≥ 2`, undisplayed. R8-3 (`.31`) proves the `D′ = 1` case directly (LEMMA HE3-4D1) and concludes: “The unresolved ramified base-change branch can occur only after excluding this direct case, so there D′ ≥ 2; together with μ ≥ 4 this gives n = D′μ ≥ 2·4 = 8. **Therefore the advertised unconditional range n ≤ 7 survives, now with the missing derivation displayed.**”

**(4) The box is therefore STRICTLY NARROWER at HEAD than as displayed**, and its `n ≤ 7` consequence is *better* supported, not worse.

**CHAIN (rule 25):** box as displayed (“ONE gap”, contradicted by §S6.2's “BOTH”) → **R8-2** (branch (i) proved; “branch (ii) alone is BOXED”) → **R8-3** (`D′ ≥ 2` supplied; `n ≤ 7` survives). **TERMINAL: branch (ii) alone, at `μ ≥ 4` and `D′ ≥ 2`, i.e. `n ≥ 8` — awaiting sol discharge-confirmation** (1851–1853).
`SUPERSESSION KIND: inventory completion` (the box's item list shrinks) + `license` (both appends supply proofs).

**Two further scope facts the box states and a chapter cut must keep:**
(a) **The mechanism of the gap is sharp and self-diagnosed**: “no element of R has non-integer dv … so NO test key of the form Φ′ + w, w ∈ R, can sit at such a side's height”. This is the same fact shard 1 `.10` records about `R` being an order.
(b) **The failure mode is concrete, not abstract**: with `ℓ = 2, d = 2, R_λ = (Z−s₁)(Z−s₂)`, the degree count alone permits `(0, 2·2D′)` instead of `(2D′, 2D′)`.

**DERIVATION:** Self-diagnosis; the repair route is named and explicitly not executed (“That is a genuine further step, not a rewording”).

*Arithmetic audit (rule 22).*
- **Reachability.** Branch (ii) needs `ℓ ≥ 2` and `d ≥ 2`, so the side length `ℓd ≥ 4`; with `Σ_λ L_λ = μ` this forces `μ ≥ 4` ✓.
- **`n ≥ 8`.** `n = D′μ`; with `μ ≥ 4` and `D′ ≥ 2`, `n ≥ 8` ✓ — **but `D′ ≥ 2` is exactly what the box does not display** ✓ confirming R8-3's finding independently.
- **The failure mode.** Two labels each of required size `D′ℓ = 2D′`; total at the slope `= D′L_λ = D′ℓd = 4D′` ✓. Degree count alone gives `n₁ + n₂ = 4D′` ✓, which admits `(0, 4D′)` ✓ **one class empty, the other twice the required size** ✓ **exactly the displayed failure mode.**
- **The repair route's degree.** `Ψ` of degree `D′ℓ` with roots on the side ✓ — matching the side's own `e_s = ℓ` scaling ✓.
**Every number reproduces, including the undisplayed hypothesis R8-3 supplies.**

**RESOLUTION TRACE:** statement 1334–1368 · the contradicting §S6.2 verdict 1057–1058 (shard 1 `.33`) · corrections 1691–1734 (R8-2, the charge's L1694), 1736–1772 (R8-3) · verification 1830–1841 (`.34`).

XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — count **19**.
XREF: `HE3_PROOF_2026-08-08.md:HE3-BOX-6` — self-count **12**.
XREF: `HE7_PROOF_2026-08-08.md:HE3-BOX-6` — grep-verified count **12** (**HE7 consumes this box** — an edge HE3's own consumer trace omits; see shard 1 source defect 1).

**TEETH:** **PROOF-ONLY and entirely unexercised.** HE3-BOX-3: “NOT exercised by machine: … μ ≥ 4 (**where LEMMA HE3-4's ramified base-change branch and the stage-CS recursion first bite**)”. The nearest machine contact is `he3r1_supp.py` P2's “an ℓ = 2 member (λ = 7/2, block (2,2))” — but that member has `d = 1`, i.e. it is the *reachable* half, not branch (ii) ✓ (`ℓd = 2 ≤ 3`, so `d = 1`). **Disposition: PROOF-ONLY; the gap is self-found (`decorrelated-model audit` is not needed — the note found it “before any hostile pass”), and its narrowing is `decorrelated-model audit` (sol A5).**

---

### EFF.HE3.s2of2.07  [scope-record]  — HE3-BOX-5 (what a hostile pass should attack first)

**CANONICAL STATEMENT:** verbatim, lines 1369–1379.

**FORM:** bulleted bold-headed box, four numbered priorities.

> “* **HE3-BOX-5 (what a hostile pass should attack first).** In priority
>   order: (1) LEMMA HE3-4's ramified base-change branch (ℓ ≥ 2 sides with
>   residual degree ≥ 2 — machine-unreachable at μ = 3, first live at
>   μ = 4); (2) the claim that unramified/ramified base change leaves the
>   LABELS of f unchanged (used twice, stated as "the root set and the
>   labels are unchanged" — the residual coefficient field grows, and the
>   argument needs that no label MERGES under the growth); (3) LEMMA
>   HE3-3's integer-sampling independence argument at slopes with equal
>   integer parts; (4) whether "decided leaf" as defined in DEFINITION 2
>   coincides exactly with LEMMA HE3-5's window condition on every row
>   (the battery measures both).”

**CONDITIONALITY:** **A preregistered attack list, and the arc's later findings can be scored against it — which is unusual and worth doing.**
- **(1) was attacked and PARTIALLY RESOLVED**: R8-2 proved the *unramified* half; the ramified branch (ii) stands ✓ **the priority was correct.**
- **(2) was attacked and RESOLVED for the unramified case**: R8-2's LEMMA HE3-4U replaces the “labels unchanged” argument with an explicit **split-component summation** — “No claim that a single split key still contributes D′ roots is used” ✓ **exactly the defect (2) named** ✓.
- **(3) was attacked at PE1 (finding 3) and closed by (SEP) + the N1 supplement** ✓ (shard 1 `.29`, `.30`).
- **(4) REMAINS OPEN** — and R8-1 (`.29`) makes it sharper, not softer, by showing HE3-5 is recursive. See shard 1 OPEN-CALL 4.
**Three of four preregistered attack targets were hit by the hostile arc, and the fourth is still open.** That is strong evidence the box was well-aimed and is recorded as such.

**DERIVATION:** Attack-priority declaration.

**RESOLUTION TRACE:** statement 1369–1379 · outcomes: (1)/(2) at 1691–1734 (`.30`); (3) at 892–961 (shard 1); (4) open, sharpened at 1634–1689 (`.29`).

**TEETH:** NONE (a preregistration about future passes, not about data). **Disposition: `preregistration` (rule 19) — and this shard scores it above, which is what the rule's pairing asks for.**

---

### EFF.HE3.s2of2.08  [instrument-record]  — §S8's instrument

**CANONICAL STATEMENT:** verbatim, lines 1381–1388.

**FORM:** `##`-headed section with a bold-headed paragraph.

> “## S8. THE BATTERY (`verification/openmath/he3_checks.py`)
>
> **Instrument.** A FRESH reader, independent of GENHN's: it detects
> residual roots by MEASURING dv(f mod Φ′_{κ,s}) at test keys — i.e. it
> implements the proof's own mechanism (LEMMA HE3-1′/HE3-2) — so it builds
> no residual polynomial and carries no twist bookkeeping. Members are
> enumerated in STAGE COORDINATES (legitimate by LEMMA GENHN-1's digit
> bijection), which is what makes the census tie below possible.”

**CONDITIONALITY:** **The “no twist bookkeeping” design is what makes the battery immune to the `[r2]` F-1 coherent/naive defect** — shard 1 `.24` says so: “the battery detects residual roots by measuring dv(B₀), which consults the coherent object automatically (the measurement IS LEMMA HE3-1′'s evaluation identity, whose right side is the coherent R_λ(s))”. **That immunity is a design property, not luck, and it is worth preserving.**
**Two dependencies:** the reader implements HE3-1′/HE3-2, so **it cannot independently test them** — it tests the *dictionary* they feed. And “enumerated in STAGE COORDINATES (legitimate by LEMMA GENHN-1's digit bijection)” means the enumeration's legitimacy rides GENHN-1, whose node display HE3 itself corrects (shard 1 `.11`). **At f₁ = 1 the two nodes coincide, so the enumeration is sound on every row** ✓ — the note says so at shard 1 `.11`'s LOCUS SCOPING.

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement 1381–1388 · immunity 638–642 (shard 1 `.24`) · node soundness 236–237 (shard 1 `.11`).

XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-1` — count **4**.
ARTIFACT: `verification/openmath/he3_checks.py` ✓ present.

**TEETH:** the instrument itself; the census tie (`.15`) is its decorrelation.

---

### EFF.HE3.s2of2.09  [instrument-record]  — §S8's rows

**CANONICAL STATEMENT:** verbatim, lines 1390–1395.

**FORM:** bold-headed paragraph.

> “**Rows.** GROUP A: the full windowed E3 enumeration at the two rows
> GENHN committed, (ℤ₂, N = 5, h = 1) and (ℤ₃, N = 4, h = 1). GROUP B:
> constructed slope-aligned loci at (ℤ₅, N = 6, λ = 3) and
> (ℤ₇, N = 6, λ = 3) — the ONLY place the 3-label type is reachable at
> f₁ = 1, because it needs three distinct residual roots in K^× = F_p^×,
> hence p ≥ 5. GROUP C: the σ-resolution boundary profile, N = 4…7.”

`[TABLE]` — transcribed:

| Group | Rows | Purpose |
|---|---|---|
| A | (ℤ₂, N = 5, h = 1), (ℤ₃, N = 4, h = 1) | full windowed E3 enumeration; **the two rows GENHN committed** — enables the census tie |
| B | (ℤ₅, N = 6, λ = 3), (ℤ₇, N = 6, λ = 3) | constructed slope-aligned loci; **the only place the 3-label type is reachable at f₁ = 1** |
| C | N = 4…7 | the σ-resolution boundary profile (HE-BND) |

*Arithmetic audit (rule 22).* The 3-label type `(1,1)³` needs three distinct roots in `K^× = F_p^×`, so `p − 1 ≥ 3`, i.e. `p ≥ 5` ✓ **hence ℤ₅ and ℤ₇ are the minimal choices** ✓. Group A's rows are exactly GENHN's committed E3 rows: `GENHN_PROOF` §S11.C lists “E3: (Zp,3,4,1), (Zp,2,5,1), (Fqt,2,5,1)” — the two ℤ_p rows are `(q,N,h) = (3,4,1)` and `(2,5,1)` ✓ **matching “(ℤ₃, N = 4, h = 1)” and “(ℤ₂, N = 5, h = 1)”** ✓ **exact.** (HE3 does not run the `Fqt` row — consistent with HE3-BOX-4's oracle asymmetry ✓.)

**CONDITIONALITY:** All rows are `f₁ = 1` and `d = 1` — the coverage bound of `.03`. **No embedded row** (`.05`).

**DERIVATION:** Row list.

**RESOLUTION TRACE:** statement 1390–1395 · census tie 1434–1446 (`.15`) · boundary 1463–1477 (`.17`).

**TEETH:** the rows are the substrate. `signed vacuity disclosure` per `.03`.

---

### EFF.HE3.s2of2.10  [instrument-record]  — §S8's legs

**CANONICAL STATEMENT:** verbatim, lines 1397–1402.

**FORM:** bold-headed paragraph, four `·`-separated legs.

> “**Legs.** HE-NORM (LEMMA HE3-1 at the entry key on EVERY member, by
> exact Bareiss/Sylvester integer resultants) · HE-PSI (the same identity
> at EVERY test key (κ, s), plus HE3-1′'s inequality dv(B₀) ≥ generic, plus
> the convex-duality identity (★)) · HE-SIG (PARI `sig(f,p)` =
> factorpadic-200 + idealprimedec, the pinned w12_checks question, against
> the HE3.A dictionary) · HE-BND (the decided/undecided profile vs window).”

**CONDITIONALITY:** **HE-SIG reuses W-12's pinned oracle question** (“the pinned w12_checks question”), which is a genuine decorrelation: the σ-oracle is not written for this note. `grep -cF 'w12_checks' W12_PROOF_2026-08-08.md` = **8** ✓ verified. **HE-NORM uses exact integer resultants (Bareiss/Sylvester), no sympy** — and the `[r2]` F-4 fix corrected a docstring that wrongly said sympy (`.24`).

**DERIVATION:** Leg description.

**RESOLUTION TRACE:** statement 1397–1402 · scored 1412–1477 (`.12`–`.17`).

XREF: `W12_PROOF_2026-08-08.md:w12_checks` — grep-verified count **8**.

**TEETH:** the four legs; inverse table at §5.

---

### EFF.HE3.s2of2.11  [run-record]  — §S9's verdict headline and totals

**CANONICAL STATEMENT:** verbatim, lines 1404–1410.

**FORM:** `##`-headed section with a bold verdict sentence and a totals line.

> “## S9. VERDICT (from the committed artifacts)
>
> **GREEN — 0 violations, all wired teeth fired, 17.0 s.** Artifacts:
> `he3_checks_output.txt`, `he3_checks_results.json` (hashes in the commit
> message; runner-as-run in the same commit). Totals: 72,134 entry-key
> resultant identities, 43,528 test-key HE-NORM/HE-PSI checks, 72,602
> reader classifications, 947 PARI σ jobs, 3,744 boundary reads.”

**CONDITIONALITY:**
(a) **“all wired teeth fired” is true of the four as wired, but one of the four is mis-specified** (`.05`). A reader counting genuine teeth must use three.
(b) **The artifact hashes are NOT in the note** — “hashes in the commit message”. **UNPINNED from the note's own text** (rule 23), unlike `he3r1_supp.py`'s three full md5s. Recorded as source defect 4.
(c) **Instrument grade only** — `.18` says so explicitly.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22), cross-checking the five totals against the Q-blocks.* 72,134 entry-key identities ✓ matches Q1's “all 72,134 enumerated members” ✓. 43,528 test-key checks ✓ matches Q2's “43,528 checks” ✓. 947 PARI jobs ✓ matches Q3's “947 PARI jobs, 0 bad” ✓. 72,602 reader classifications vs 72,134 enumerated members: **a difference of 468** — the classifications exceed the enumerated members, consistent with Group B's constructed loci (`125 + 343 = 468` members at p = 5 and p = 7 ✓ **exactly 468**) being classified on top of the Group A enumeration ✓ **the two numbers reconcile exactly, which the note does not state.** 3,744 boundary reads vs Group C's profile: `(125 + 343) × 4 windows (N = 4..7) = 468 × 4 = 1,872`; `3,744 = 2 × 1,872` ✓ — consistent with two reads per member per window (e.g. decided-flag plus deepest-height) ✓ **plausible and exactly a factor of two; recorded as consistent-but-not-derivable from the note.**

**RESOLUTION TRACE:** statement 1404–1410 · Q-blocks 1412–1477 · machine-leg scope 1479–1488 (`.18`).

ARTIFACT: `verification/openmath/he3_checks_output.txt` ✓ · `he3_checks_results.json` ✓.

**TEETH:** this unit is the run-record half; the leg descriptions (`.10`) are the other half.

---

### EFF.HE3.s2of2.12  [run-record]  — Q1 (HE-NORM)

**CANONICAL STATEMENT:** verbatim, lines 1412–1414.

**FORM:** bold-headed scorecard paragraph.

> “**Q1 (HE-NORM) ✓** 0 violations of Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀) — at the
> entry key on all 72,134 enumerated members and at every test key of
> every oracled member. The engine of the proof is machine-real.”

**CONDITIONALITY:** **This is the strongest machine result for shard 1 `.20`** — the resultant identity holds exhaustively on every enumerated member. The claim “The engine of the proof is machine-real” is warranted: HE3-1 is the identity every other lemma rides. **Scope:** `f₁ = 1` rows only (`.03`), so the `[r1, F2]` band repair is invisible here — that repair's evidence is PE1's PARI-exact counter-instances (shard 1 `.20`).

**DERIVATION:** Run record.

**RESOLUTION TRACE:** statement 1412–1414 · the lemma 450–490 (shard 1 `.20`).

**TEETH:** **Disposition: executable regression, exhaustive on the enumerated rows.** Exactness method: “exact Bareiss/Sylvester integer resultants” (`.10`) — no floating point, no sympy.

---

### EFF.HE3.s2of2.13  [run-record]  — Q2 (HE-PSI)

**CANONICAL STATEMENT:** verbatim, lines 1416–1418.

**FORM:** bold-headed scorecard paragraph.

> “**Q2 (HE-PSI) ✓** 0 violations, 43,528 checks: dv(B₀^{(κ,s)}) never
> falls below min_j(dv(A_j) + jκ), and the support-function identity (★)
> holds at every sampled κ on every in-window polygon.”

**CONDITIONALITY:** **Note precisely what is tested: the INEQUALITY and (★), not the equality-vs-cancellation dichotomy.** LEMMA HE3-1′'s content is that equality holds *unless* `R_λ(s) = 0`; Q2 verifies only `dv(B₀) ≥ generic` ✓ plus the convex duality ✓. The dichotomy's other half is tested through the peel profiles at `.20`/`.23`. Recorded because a reader could over-read Q2 as confirming HE3-1′ entire.

**DERIVATION:** Run record.

**RESOLUTION TRACE:** statement 1416–1418 · the lemma 548–586 (shard 1 `.22`) · (★) 846–857 (shard 1 `.31`).

**TEETH:** **Disposition: executable regression.** (★) is verified directly, which is the only direct machine check of the convex-duality display that both frozen consumers pin.

---

### EFF.HE3.s2of2.14  [run-record]  — Q3 (HE-SIG) and the five μ = 3 stage types

**CANONICAL STATEMENT:** verbatim, lines 1420–1432 (rule 14 double-emission: the source ASCII table is inside the quotation, the `[TABLE]` transcription follows).

**FORM:** bold-headed scorecard paragraph with a fixed-width ASCII table and a closing sentence.

> “**Q3 (HE-SIG) ✓ 947 PARI jobs, 0 bad.** ALL FIVE μ = 3 stage types are
> realized and confirmed:
>
>     stage type            predicted σ at (e₁,f₁) = (2,1)   members (p=5 / p=7)
>     (3,1)                 {(6,1)}                            4 /   6
>     (1,3)                 {(2,3)}                           40 / 112
>     (1,1)+(2,1)           {(2,1),(4,1)}                      8 /  24
>     (1,1)+(1,2)           {(2,1),(2,2)}                     40 / 128
>     (1,1)+(1,1)+(1,1)     {(2,1),(2,1),(2,1)}                4 /  21
>
> The last row is the one with NO μ = 2 analogue: **25 sextics that split
> into three ramified quadratics, each PARI-confirmed** — the first machine
> confirmation of a 3-label stage σ anywhere in this program.”

`[TABLE]` — transcription:

| stage type | predicted σ at (e₁,f₁) = (2,1) | members p = 5 | members p = 7 |
|---|---|---|---|
| (3,1) | {(6,1)} | 4 | 6 |
| (1,3) | {(2,3)} | 40 | 112 |
| (1,1)+(2,1) | {(2,1),(4,1)} | 8 | 24 |
| (1,1)+(1,2) | {(2,1),(2,2)} | 40 | 128 |
| (1,1)+(1,1)+(1,1) | {(2,1),(2,1),(2,1)} | 4 | 21 |

*Arithmetic audit (rule 22), computed fresh and cross-checked against every other number in the note.*
- **The five types are exhaustive for `Σ e_sf_s = 3`** ✓ (audited at shard 1 `.19`): `{(3,1)}, {(1,3)}, {(1,1),(2,1)}, {(1,1),(1,2)}, {(1,1)³}` ✓ **exactly five, no omissions.**
- **Every σ is degree-consistent** at `D′ = e₁f₁ = 2`, `deg f = D′μ = 6`: `{(6,1)}` → 6 ✓; `{(2,3)}` → 6 ✓; `{(2,1),(4,1)}` → 2+4 = 6 ✓; `{(2,1),(2,2)}` → 2+4 = 6 ✓; `{(2,1)³}` → 2+2+2 = 6 ✓. **All five exhaust degree 6.**
- **Every σ matches THEOREM HE3.A's dictionary** `σ = {(e₁e_s, f₁f_s)}` at `(e₁,f₁) = (2,1)`: `(3,1) ↦ (2·3, 1·1) = (6,1)` ✓; `(1,3) ↦ (2, 3)` ✓; `(1,1)+(2,1) ↦ (2,1)+(4,1)` ✓; `(1,1)+(1,2) ↦ (2,1)+(2,2)` ✓; `(1,1)³ ↦ (2,1)³` ✓ **all five reproduce the dictionary exactly.**
- **Member totals.** p = 5: `4 + 40 + 8 + 40 + 4 = 96`. p = 7: `6 + 112 + 24 + 128 + 21 = 291`. **And HE-BND's N = 6 decided counts are exactly 96 (p = 5) and 291 (p = 7)** ✓ — **the Q3 σ-confirmed member counts equal the N = 6 decided counts, cell for cell. The note does not state this cross-check; it holds exactly.** That is a strong internal consistency result: every member decided at N = 6 got a σ prediction, and every σ prediction was PARI-confirmed.
- **“25 sextics”.** The 3-label row is `4 (p=5) + 21 (p=7) = 25` ✓ **exactly.**
- **947 PARI jobs vs 96 + 291 = 387 members**: `947 > 387`, consistent with multiple jobs per member (the σ multiset needs one job per predicted factor, plus the entry read). `947 / 387 ≈ 2.45` — plausible, not derivable from the note. Recorded as consistent-but-unverifiable.
**Every derivable number reproduces, and one new exact cross-check (Q3 ↔ HE-BND at N = 6) was found.**

**CONDITIONALITY:** **The strongest positive result in the note**, and it is scoped: `f₁ = 1`, `e₁ = 2`, ℤ_p only. The 3-label type is the one “with NO μ = 2 analogue”, i.e. the exact configuration shard 1 `.19` shows the μ = 2 method cannot decide.

**DERIVATION:** Run record against the HE3.A dictionary.

**RESOLUTION TRACE:** statement 1420–1432 · the dictionary 312–331 (shard 1 `.16`) · the cross-check 1207–1226 (shard 1 `.36`) · the underdetermination it answers 414–422 (shard 1 `.19`).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11** (the μ = 2 dictionary the μ = 3 table extends).

**TEETH:** **Disposition: executable regression against an independent oracle (PARI factorpadic-200 + idealprimedec, the pinned W-12 question).** Planted mutant **HE-T-SIG**: “6/6 flipped dictionaries caught by PARI on each of the two rows” (`.16`).

---

### EFF.HE3.s2of2.15  [run-record]  — Q4, the census tie

**CANONICAL STATEMENT:** verbatim, lines 1434–1446 (rule 14 double-emission).

**FORM:** bold-headed scorecard paragraph with a fixed-width ASCII table and two follow-up sentences.

> “**Q4 (the census tie — the strongest single number in this note) ✓** The
> fresh reader reproduces GENHN's committed E3 rows EXACTLY:
>
>     row            members   this reader                    GENHN @ pin
>     (ℤ₃, 4, 1)      39,366   drain 13,122 · {(6,1)} 26,244   UND3 13,122 · RAM3(7) 26,244
>     (ℤ₂, 5, 1)      32,768   {(6,1)} 20,480                  RAM3(7) 16,384 + RAM3(8) 4,096
>
> with 13,122 + 26,244 = 39,366 = the whole row, exactly as GENHN's §S12
> P6 records. The (ℤ₂,5,1) row additionally resolves classes GENHN's spot
> list did not break out: {(2,1),(4,1)} 6,144 · {(2,3)} 1,024 ·
> {(2,1),(2,2)} 512 · drain 4,608 (total 32,768). Two independently written
> readers agreeing to the digit on 72,134 members is the decorrelation this
> program asks for.”

`[TABLE]` — transcription:

| row | members | this reader | GENHN @ pin |
|---|---|---|---|
| (ℤ₃, 4, 1) | 39,366 | drain 13,122 · {(6,1)} 26,244 | UND3 13,122 · RAM3(7) 26,244 |
| (ℤ₂, 5, 1) | 32,768 | {(6,1)} 20,480 | RAM3(7) 16,384 + RAM3(8) 4,096 |

*Arithmetic audit (rule 22), computed fresh and cross-checked against GENHN's own §S12.*
- **Row 1 balance.** `13,122 + 26,244 = 39,366` ✓ **= the whole row** ✓. And `39,366 = 2 · 3⁹` ✓, `13,122 = 2 · 3⁸` ✓, `26,244 = 4 · 3⁸ = 2 × 13,122` ✓.
- **Cross-check against GENHN.** `GENHN_PROOF` §S12 P6 reads “(3,4,1): UND3 = 13,122, RAM3(7) = 26,244, no ALPHA3, and 13,122 + 26,244 = the whole row” ✓ **verbatim agreement, digit for digit** ✓ — and `spec/EFF-GENHN-s2of2.md` `.16` independently audited the same numbers ✓ **three independent verifications agree.**
- **Row 2.** HE3's reader: `{(6,1)} 20,480`. GENHN's: `RAM3(7) 16,384 + RAM3(8) 4,096 = 20,480` ✓ **exact agreement after summing GENHN's two strata** ✓ — the two readers stratify differently but total identically, which is precisely what a “tie” should look like.
- **Row 2's full breakdown.** `20,480 + 6,144 + 1,024 + 512 + 4,608 = 32,768` ✓ **exactly the row total** ✓ **the four additional classes plus the {(6,1)} class exhaust the row.** (Computed: 20,480 + 6,144 = 26,624; + 1,024 = 27,648; + 512 = 28,160; + 4,608 = 32,768 ✓.)
- **Powers of two.** `32,768 = 2^15` ✓, `20,480 = 5 · 2^12`, `6,144 = 3 · 2^11`, `1,024 = 2^10`, `512 = 2^9`, `4,608 = 9 · 2^9` ✓ all integral.
- **The 72,134 figure.** `39,366 + 32,768 = 72,134` ✓ **exactly the enumerated-member total at `.11`** ✓ — **so Group A alone accounts for every enumerated member, and Group B's 468 constructed members are the extra reader classifications** ✓ confirming `.11`'s reconciliation independently.
**Every number reproduces, and two cross-checks the note does not state (the row-2 breakdown summing to the row, and 39,366 + 32,768 = 72,134) hold exactly.**

**CONDITIONALITY:** **The decorrelation claim is the strongest evidential statement in the note and it is warranted**: two independently written readers, one built to measure `dv(B₀)` (HE3's) and one built on GENHN's own machinery, agreeing digit-for-digit on 72,134 members. **What it does NOT establish:** the σ dictionary (that is Q3's job) or anything at `f₁ ≥ 2`.

**DERIVATION:** Run record + the reader tie.

**RESOLUTION TRACE:** statement 1434–1446 · GENHN's side `GENHN_PROOF` 1827–1830 · the enumeration's legitimacy 1386–1388 (`.08`).

XREF: `GENHN_PROOF_2026-08-08.md:S11.F` — count **10** (the perimeter that gates the *other* rows).

**TEETH:** **Disposition: `foreign-note decorrelation`** — the strongest available, since the two readers share no code.

---

### EFF.HE3.s2of2.16  [run-record]  — Q5 (teeth)

**CANONICAL STATEMENT:** verbatim, lines 1448–1461.

**FORM:** bold-headed scorecard paragraph.

> “**Q5 (teeth).** HE-T-UNDET ✓ **fired, and it is the mechanism
> certificate**: on the 3-label members the two identities GENHN.C's μ = 2
> proof uses admit **10** nonnegative solutions (all class sizes multiples
> of D′e_sf_s = 2, summing to D′μ = 6) where the truth is the single vector
> (2,2,2) — e.g. (6,0,0), (4,2,0), (2,4,0) all satisfy both identities.
> The μ = 2 argument is therefore not merely unproven at μ = 3, it is
> **information-theoretically insufficient**, and the full test-key family
> of §S6 is what closes the gap. HE-T-SIG ✓ 6/6 flipped dictionaries caught
> by PARI on each of the two rows. **HE-T-CAP ✓ (added mid-run, the
> strongest tooth): the earlier reader variant that dropped out-of-window
> recentered digits disagrees with the sound reader on 17 (p = 5) and 43
> (p = 7) members — the soundness bug of LEMMA HE3-5 is real and is caught.**
> HE-T-NODE: fired but MIS-SPECIFIED (see HE3-BOX-4b) — read as a
> diagnostic. HE-T-PSI, HE-T-CERT: owed.”

*Arithmetic audit (rule 22), recomputed.*
- **HE-T-UNDET's 10.** Solutions `(n₁,n₂,n₃)`, each a nonnegative multiple of `D′e_sf_s = 2`, summing to `D′μ = 6`: write `n_i = 2a_i` with `a_i ≥ 0`, `Σa_i = 3`; the count is `C(3+2,2) = 10` ✓ **exactly 10** ✓. The three examples `(6,0,0), (4,2,0), (2,4,0)` are `(3,0,0), (2,1,0), (1,2,0)` ✓ valid ✓. **The truth `(2,2,2) = 2·(1,1,1)` is one of the ten** ✓.
- **Why both identities are satisfied by all ten.** Identity 1: `Σn_i = 6` ✓ by construction. Identity 2 at a single slope `λ`: `Σn_iλ = λ·6` ✓ **independent of the split** ✓ — exactly shard 1 `.19`'s degeneracy ✓.
- **HE-T-CAP's disagreement counts.** 17 (p = 5) and 43 (p = 7). Cross-check against `.17`'s never-decided residuals (28 and 51) and against the N = 5→6 increments (`96 − 84 = 12` at p = 5; `291 − 258 = 33` at p = 7): neither matches 17/43 exactly. **No cross-check is available; recorded as unverifiable-but-unclaimed.** The tooth's *nature* is what matters: the mutant is the note's own earlier reader.
- **Teeth accounting.** Fired: UNDET, SIG, CAP, NODE = 4 ✓ matching `.05`'s “FOUR teeth wired”; genuine: 3 ✓; owed: PSI, CERT = 2 ✓.
**The one derivable number (10) reproduces exactly.**

**CONDITIONALITY:** **HE-T-UNDET is not a regression test — it is a proof-of-necessity**, and it is the single strongest justification for the whole note. **HE-T-CAP is the strongest tooth and it caught a real soundness bug in the note's own earlier reader.** **HE-T-NODE is disclosed mis-specified** (`.05`); **two teeth are owed.** The Q5 verdict phrase “all wired teeth fired” at `.11` must be read with `.05`'s accounting.

**DERIVATION:** Run record.

**RESOLUTION TRACE:** statement 1448–1461 · the underdetermination 399–422 (shard 1 `.19`) · the soundness bug 1231–1236 (shard 1 `.37`'s preamble) · the accounting 1321–1333 (`.05`).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11**.
XREF: `HE3_PROOF_2026-08-08.md:HE-T-UNDET` — self-count **3**.

**TEETH:** this unit IS the teeth scorecard. **Disposition: planted mutant ×3 fired (UNDET, SIG, CAP); `stale self-description` (NODE); `disclosed non-repair` (PSI, CERT).**

---

### EFF.HE3.s2of2.17  [run-record]  — HE-BND (the boundary law)

**CANONICAL STATEMENT:** verbatim, lines 1463–1477 (rule 14 double-emission).

**FORM:** bold-headed scorecard paragraph with a fixed-width ASCII table.

> “**HE-BND (the boundary law) ✓ PREDICTION CONFIRMED.** LEMMA HE3-5
> predicts that the aligned λ = 3, μ = 3 locus is undecidable until
> e₁N > μλ = 9, i.e. N ≥ 5, and that the ALPHA types (residual a perfect
> cube / a repeated root) need one further window unit. Measured decided
> counts, p = 5 (of 125 members) and p = 7 (of 343):
>
>     N        4      5      6      7        cap e₁N   (μλ = 9)
>     p = 5    0     84     96     97          8/10/12/14
>     p = 7    0    258    291    292
>
> Zero at N = 4 (cap 8 < 9), the bulk at N = 5 (cap 10 > 9), the ALPHA
> remainder at N = 6, saturation thereafter — exactly the predicted
> two-step. The residual 28 (p = 5) / 51 (p = 7) never-decided members are
> the 25 / 49 with vanishing residual constant (no full side: outside the
> genre) plus 3 / 2 genuinely deeper members, reported as-is.”

`[TABLE]` — transcription:

| N | cap e₁N | p = 5 decided (of 125) | p = 7 decided (of 343) |
|---|---|---|---|
| 4 | 8 | 0 | 0 |
| 5 | 10 | 84 | 258 |
| 6 | 12 | 96 | 291 |
| 7 | 14 | 97 | 292 |

*Arithmetic audit (rule 22), every number recomputed.*
- **The caps.** `e₁N` at `e₁ = 2`: `8, 10, 12, 14` for `N = 4,5,6,7` ✓ **exactly the displayed row** ✓.
- **The threshold.** `μλ = 3 · 3 = 9` ✓; `cap > 9` first at `N = 5` (cap 10) ✓ **so zero at N = 4 (cap 8 < 9)** ✓ **matching the measurement** ✓.
- **Never-decided residuals.** p = 5: `125 − 97 = 28` ✓ **and the note says `25 + 3 = 28`** ✓ exact. p = 7: `343 − 292 = 51` ✓ **and `49 + 2 = 51`** ✓ exact. **Both decompositions balance.**
- **The out-of-genre counts.** 25 at p = 5 and 49 at p = 7: `25 = 5²` and `49 = 7²` ✓ — **the members with vanishing residual constant form a codimension-1 sub-locus of a `p³`-sized locus, i.e. `p²` members** ✓ `125 = 5³`, `343 = 7³` ✓ **exactly consistent.** The note does not state this; it holds.
- **The two-step.** p = 5: `0 → 84 → 96 → 97`, increments `84, 12, 1` ✓ — bulk at N = 5, remainder at N = 6, then saturation ✓. p = 7: `0 → 258 → 291 → 292`, increments `258, 33, 1` ✓ same shape ✓.
- **Cross-check with Q3 (new).** The N = 6 decided counts are **96 and 291** — **exactly Q3's member totals** (`4+40+8+40+4 = 96`; `6+112+24+128+21 = 291`) ✓ **cell for cell.** So the σ-confirmed set is precisely the N = 6 decided set. **The note states neither number as a total nor the coincidence; it is exact.**
- **The N = 7 extras.** `97 − 96 = 1` at p = 5 and `292 − 291 = 1` at p = 7 — one further member each, decided at N = 7 but not σ-scored at Q3. Consistent with the “3 / 2 genuinely deeper members” count (of which one each resolves by N = 7) ✓.
**Every derivable number reproduces, and two cross-checks the note does not state (the `p²` out-of-genre count and the Q3 ↔ N = 6 identity) hold exactly.**

**CONDITIONALITY:** **“PREDICTION CONFIRMED” is RE-SCOPED by R8-1** (1686–1689):

> “Accordingly, §S9's HE-BND table is evidence for the selected aligned
> rows only: it is consistent with the local cap criterion and exhibits
> a two-step profile in those rows, but **it does not verify a general
> two-step boundary law**.”

`SUPERSESSION KIND: scope-pin`. **CHAIN: “PREDICTION CONFIRMED” → R8-1's re-scoping. TERMINAL: evidence for the aligned rows only.** The prediction it confirmed — HE3-5's “one more window unit” bullet — is itself **replaced** by R8-1 (`.29`), so the table now confirms a bullet that no longer stands as a general law. **The measurement is unchanged and remains valid; only its generality is withdrawn.**

**DERIVATION:** Run record against LEMMA HE3-5's prediction.

**RESOLUTION TRACE:** statement 1463–1477 · the lemma 1238–1265 (shard 1 `.37`) · re-scoping 1686–1689 (`.29`).

**TEETH:** **Disposition: measurement, preregistered, confirmed — then RE-SCOPED.** `stale self-description` on the general two-step law.

---

### EFF.HE3.s2of2.18  [scope-record]  — “What the machine leg establishes”

**CANONICAL STATEMENT:** verbatim, lines 1479–1488.

**FORM:** bold-headed closing paragraph of §S9.

> “**What the machine leg establishes** (instrument grade, not acceptance):
> LEMMA HE3-1's resultant identity at every test key of every member; the
> HE3.A dictionary at ALL FIVE μ = 3 stage types under an independent
> oracle, including the 3-label type that has no μ = 2 analogue; the
> underdetermination of the μ = 2 method at μ = 3 as an explicit count of
> spurious solutions; the σ-resolution boundary law of LEMMA HE3-5 with its
> predicted two-step; and a digit-exact tie of a freshly written reader to
> GENHN's committed E3 census. Grade box HE3-BOX-1 unchanged: **attempt
> 0/2, no hostile arc has run**; nothing here upgrades the conditionality
> display of COROLLARY HE3.C.”

**CONDITIONALITY:**
(a) **`STALE-SELF-DESCRIPTION` twice**: “attempt 0/2” (now 1/2) and “**no hostile arc has run**” — three passes ran (PE1, PE2, PE3). **This sentence dates from before the arc**, and the surrounding `[r1]`/`[r2]` text was updated while it was not. Recorded as source defect 5.
(b) **Item 4 of the list is RE-SCOPED by R8-1** — “the σ-resolution boundary law of LEMMA HE3-5 with its predicted two-step” is exactly what R8-1 withdraws as a general law (`.17`, `.29`).
(c) **The surviving load-bearing clause is the last one and it must not be dropped with the stale grade:** “nothing here upgrades the conditionality display of COROLLARY HE3.C.” Machine GREEN does not move the conditionality — the same discipline GENHN states at its `.23`.

**DERIVATION:** Summary of `.12`–`.17`.

**RESOLUTION TRACE:** statement 1479–1488 · grade 1579–1583 (`.26`) · re-scoping 1686–1689 (`.29`).

**TEETH:** NONE (summary).

---

### EFF.HE3.s2of2.19  [run-record]  — §S9′'s verdict and the runner pins

**CANONICAL STATEMENT:** verbatim, lines 1490–1500.

**FORM:** `##`-headed section with a bold verdict sentence carrying an inline `[r2]` pin correction.

> “## S9′. [r1] SUPPLEMENTARY MACHINE LEG (`verification/openmath/
> ## he3r1_supp.py` — additive; the §S8 battery and artifacts byte-frozen)
>
> **VERDICT GREEN — 0 violations, exit 0** (artifacts
> `he3r1_supp_output.txt`, `he3r1_supp_results.json`; runner md5
> 93681e8d47d447dcbfd46db0ddfe0c55 **[r2 2026-08-09, F-4: docstring-only
> fix — the sympy/Bareiss slip corrected and the P4 caveat added; the r1
> runner md5 was 9cd132a8ce174f5703542757675f7960; the [r2] re-run's
> stdout is BYTE-IDENTICAL to the committed r1 output and the results
> JSON is content-identical, GREEN, 0 violations]**, output md5
> 65ed06e49f4c54abf1b143513633f143). What ran, keyed to the repairs:”

**CONDITIONALITY:** **This is freeze predicate (F2)'s one exception, and it is fully accounted** — old md5, new md5, reason, byte-identical stdout, content-identical JSON. `SUPERSESSION KIND: as-of scoping` on the runner pin.
**The leg is ADDITIVE**: “the §S8 battery and artifacts byte-frozen”. So every `[r1]` repair's machine evidence lives here, outside the seal, exactly as the note's repair mechanism requires.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22).* Both md5s are 32 hex characters ✓ well-formed. The `[r2]` claim structure is internally consistent: a docstring change alters the runner's md5 ✓ but not its stdout ✓, which is precisely what a docstring-only edit predicts ✓.

**RESOLUTION TRACE:** statement 1490–1500 · the F-4 finding 137 (shard 1 `.07`) · the legs 1502–1562 (`.20`–`.24`).

ARTIFACT: `verification/openmath/he3r1_supp.py` ✓ · `he3r1_supp_output.txt` ✓ · `he3r1_supp_results.json` ✓ — 3/3 present.
**Full md5s: 3 PINNED** (`93681e8d…`, `9cd132a8…`, `65ed06e4…`), in contrast to §S8's UNPINNED-from-the-note hashes (`.11`).

**TEETH:** the leg itself; P1–P4 at `.20`–`.24`.

---

### EFF.HE3.s2of2.20  [run-record]  — §S9′ P1 (the repaired peel at PE1's counter-instance)

**CANONICAL STATEMENT:** verbatim, lines 1502–1511.

**FORM:** bulleted bold-headed run record.

> “* **P1 (the repaired peel at PE1's counter-instance, F1).** Genre
>   (3;1,2,3;1), K = F₉, member with single side λ = 3 and residual
>   (Z−1)(Z−η)(Z+η) — PE1's {1, i, −i}. Measured with LEMMA HE3-1L
>   carriers under the minus convention, on the exact member AND a
>   junk-perturbed variant: m_s = 1 at each of the 3 residual roots
>   (including both K∖F₃ letters, which the old ŝ·n(λ) display cannot
>   carry) and m_s = 0 at the other 5 letters of F₉^×; Σ_s D′m_s = 6 =
>   deg f; PARI σ = {(1,2),(1,2),(1,2)} on both variants. The class-size
>   splits (4,0)/(2,2)/(0,4) that PE1 showed the old text could not
>   exclude are excluded by measurement.”

**CONDITIONALITY:** **The decisive machine evidence for shard 1's `[r1] F1` CRITICAL repair (LEMMA HE3-1L).** Two things it establishes that nothing else does: the two `K∖F₃` letters are *carriable* (the old display could not reach them), and the spurious splits PE1 exhibited are *excluded by measurement*, not by argument.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22), every number recomputed.*
- **Frame.** Genre `(3; 1,2,3; 1)`: `Q = 3, e₁ = 1, f₁ = 2, μ = 3, h = 1` ⟹ `D′ = e₁f₁ = 2` ✓, `K = F_{Q^{f₁}} = F₉` ✓, `deg f = D′μ = 6` ✓.
- **The residual.** `(Z−1)(Z−η)(Z+η)` with `η² = −1` in `F₉` — degree 3 ✓ `= d_λ`, and `ℓ = 1` (integer slope λ = 3) so `L_λ = ℓd_λ = 3 = μ` ✓ **a single side spanning the polygon** ✓.
- **Letter counts.** `|F₉^×| = 8` ✓; 3 residual roots + 5 non-roots = 8 ✓ **exactly the displayed split** ✓. Of the 3 roots, `1 ∈ F₃` and `±η ∉ F₃` ✓ **“both K∖F₃ letters”** ✓ — and `|F₃^×| = 2`, so the old display could carry only 2 of the 8 letters ✓.
- **`Σ_s D′m_s`.** `3 roots × D′ × m_s = 3 × 2 × 1 = 6 = deg f` ✓ **exact.**
- **PARI σ.** `{(1,2),(1,2),(1,2)}` sums to `1·2 × 3 = 6` ✓ **= deg f** ✓. Matches HE3.A's dictionary: each label `(e_s,f_s) = (1,1)` gives `(e₁e_s, f₁f_s) = (1·1, 2·1) = (1,2)` ✓ **three times** ✓.
- **The excluded splits.** The `{η, −η}` mass is `2 × D′ = 4` roots; `(4,0)/(2,2)/(0,4)` are the three ways to split 4 into two even parts ✓, and the truth is `(2,2)` ✓ — **so the displayed list includes the true split**, and what is excluded is the two extreme alternatives ✓. Recorded precisely: the measurement excludes `(4,0)` and `(0,4)` and confirms `(2,2)`.
**Every number reproduces.**

**RESOLUTION TRACE:** statement 1502–1511 · the lemma 498–546 (shard 1 `.21`) · the peel 991–1020 (shard 1 `.32`) · PE1's finding 100 (shard 1 `.05`).

**TEETH:** **Disposition: executable regression, exhaustive over the 8-letter set, on two variants (exact + junk-perturbed), with PARI adjudication.** This is the cleanest tooth in the note: it enumerates the whole letter space and confirms the profile.

---

### EFF.HE3.s2of2.21  [run-record]  — §S9′ P2 (the f₁ = 2 sweep)

**CANONICAL STATEMENT:** verbatim, lines 1512–1519.

**FORM:** bulleted bold-headed run record.

> “* **P2 (f₁ = 2 sweep, 8/8 members).** At Φ′ = x²+9: three 3-letter
>   rational configs (incl. a Frobenius-conjugate pair), a (1,2)+(1,4)
>   member (irreducible quadratic residual), a (1,6) member (irreducible
>   cubic residual Z³+2Z+1), the three-CONSECUTIVE-integer-slope member
>   (slopes 3,4,5 — the [r1-N1] geography), an ℓ = 2 member (λ = 7/2,
>   block (2,2)), and a mixed (1,2)+(2,2) member — dictionary vs PARI
>   agree on each, HE3-1a asserted at the entry key of each (exact
>   Bareiss/Sylvester resultants, no sympy).”

**CONDITIONALITY:** **The sweep that gives the `f₁ = 2` repairs their machine contact**, and it is the same frame `Φ′ = x²+9` that shard 1 `.10` uses for the non-DVR counter-instance and `.20` for the band counter-instances — **so one frame carries three distinct findings** ✓.
**Coverage note:** `e₁ = 1` throughout (`Φ′ = x²+9` at `(e₁,f₁,h) = (1,2,1)`), which is exactly the geography where the `[r2]` F-1 twist seam is INVISIBLE (`W ≡ 0` at `e₁ = 1`, shard 1 `.14`). **So P2 could not have caught the coherent/naive defect** — and did not. The `[r2]` coverage note (`.25`) says so.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22).* Member count: 3 (rational configs) + 1 + 1 + 1 + 1 + 1 = **8** ✓ **matching “8/8 members”** ✓. Frame: `Φ′ = x²+9` over ℤ₃ ⟹ `e₁ = 1, f₁ = 2, D′ = 2, h = 1` ✓ (audited at shard 1 `.10`). σ checks: `(1,2)+(1,4)` sums to `2 + 4 = 6` ✓; `(1,6)` → 6 ✓; `(2,2)` block → 4, and with `μ`… the ℓ = 2 member at `λ = 7/2` has `ℓ = 2`, so `e_s = 2`, and `(e₁e_s, f₁f_s) = (2, 2)` ✓ **matching “block (2,2)”**, degree `4` ✓; mixed `(1,2)+(2,2)` sums to `2 + 4 = 6` ✓. **All degree-consistent.** The three-consecutive-slope member has slopes `3,4,5` ✓ with `D′h = 2`, so all three exceed the band floor ✓ legal.

**RESOLUTION TRACE:** statement 1512–1519 · the geographies it covers: 149–163 (shard 1 `.10`), 450–478 (`.20`), 937–961 (`.30`), 648–671 (`.25`) · the coverage note 1564–1573 (`.25`).

**TEETH:** **Disposition: executable regression, 8/8 with PARI adjudication on each.** `signed vacuity disclosure`: `e₁ = 1` only, so the `e₁ ≥ 2` twist seam is structurally invisible.

---

### EFF.HE3.s2of2.22  [run-record]  — §S9′ P2-N1 (the supplement's two branches) with its `[r2]` geography disclosure

**CANONICAL STATEMENT:** verbatim, lines 1520–1535.

**FORM:** bulleted bold-headed run record with an embedded `[r2, F-5]` scope disclosure.

> “* **P2-N1 (the supplement, both branches).** On the consecutive-slope
>   member, recentering the TOP side at its residual root: the exact
>   member lands in the CASE A₀′ = 0 branch (Φ″ | f exactly; the quotient
>   development at Φ″ has slopes {3, 4} as the supplement's case B
>   states), and the junk variant lands in CASE A₀′ ≠ 0 with recentered
>   slopes {3, 4, 8} — the non-slope integer 5 appears in the gap,
>   exactly the sample the supplement's inversion consumes.
>   **[r2, F-5 2026-08-09 — geography scope at the pin.]** This demo ran
>   at (Q,f₁) = (3,2) (K = F₉, letters abundant), a geography where the
>   N1 gap is not LIVE — the gap needs K^× = {1}, i.e. (Q,f₁) = (2,1).
>   The true gap geography has machine contact as of PE2:
>   `he3_pe2fresh.py` FR-D runs both branches over ℤ₂ at Φ′ = x−2,
>   slopes 2,3,4 (PARI σ = {(1,1)}³; the exact member in the A₀′ = 0
>   branch with quotient development slopes {2,3}; a junk variant in
>   CASE A₀′ ≠ 0 with slopes {2,3,6} and the non-slope 4 in the gap) —
>   both branches behave as the supplement states.”

**CONDITIONALITY:** **A `signed vacuity disclosure` of unusual precision: the demo ran where the gap it demonstrates cannot occur, and the note says so and supplies the live-geography substitute.** `SUPERSESSION KIND: scope-pin`. **CHAIN: the `[r1]` demo at (3,2) → the `[r2]` F-5 disclosure → PE2's FR-D at the live (2,1) geography. TERMINAL: FR-D as the machine contact of record.**
**The FR-D frame is worth noting**: `Φ′ = x − 2` over ℤ₂ gives `D′ = 1`, i.e. `e₁ = f₁ = 1` — **the `D′ = 1` case R8-3 later proves directly** (`.31`). So the N1 supplement's live-geography evidence sits in exactly the configuration whose general theory was the last A5 gap.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22).*
- **The `[r1]` demo.** `(Q,f₁) = (3,2)` ⟹ `K = F₉`, `|K^×| = 8` ✓ “letters abundant” ✓ — and the N1 gap needs `|K^×| = 1`, i.e. `Q^{f₁} = 2`, i.e. `(Q,f₁) = (2,1)` ✓ **the demo geography cannot exhibit the gap** ✓.
- **Case B check.** Exact member: `Φ″ | f`, quotient slopes `{3,4}` ✓ — a two-slope polygon, invertible by sub-case (a) ✓ as the supplement states ✓.
- **Case A check.** Junk variant: recentered slopes `{3,4,8}`, with the non-slope integer `5` strictly inside the gap `(4,8)` ✓ **exactly the sample the inversion needs** ✓. The supplement predicts `δ ≥ a+3` with `a = 3`, i.e. `δ ≥ 6` ✓ and `δ = 8 ≥ 6` ✓.
- **FR-D.** Over ℤ₂ at `Φ′ = x−2`: slopes `2,3,4` ✓ consecutive ✓; `K^× = F₂^× = {1}` ✓ **the live gap geography** ✓. Case B: quotient slopes `{2,3}` ✓. Case A: slopes `{2,3,6}` with non-slope `4` in the gap `(3,6)` ✓; supplement predicts `δ ≥ a+3 = 5` ✓ and `δ = 6 ≥ 5` ✓. PARI `σ = {(1,1)}³` sums to 3 ✓ `= D′μ = 1·3` ✓.
**Both geographies' arithmetic reproduces, and the supplement's `δ ≥ a+3` bound holds in both.**

**RESOLUTION TRACE:** statement 1520–1535 · the supplement 937–961 (shard 1 `.30`) · the F-5 finding 138 (shard 1 `.07`).

ARTIFACT: `verification/openmath/he3_pe2fresh.py` ✓ present.

**TEETH:** **Disposition: `signed vacuity disclosure` on the `[r1]` leg; `accepted-with-decorrelation-supplied` by PE2's FR-D.** Both branches verified at both geographies.

---

### EFF.HE3.s2of2.23  [run-record]  — §S9′ P3 (the f₁ = 3 sweep and the 26-letter peel)

**CANONICAL STATEMENT:** verbatim, lines 1536–1542.

**FORM:** bulleted bold-headed run record.

> “* **P3 (f₁ = 3 sweep, 4/4 members + the 26-letter peel).** At
>   Φ′ = x³−9x+27 (K = F₂₇, D′h = 3, test height λ = 4): {1,2,η}, the
>   Frobenius orbit {η, η³, η⁹} peeled as three separate C-letters, a
>   (1,3)+(1,6) member, and an irreducible-cubic (1,9) member — PARI
>   agrees on each. The repaired-peel profile over the FULL F₂₇^×:
>   m_s = 1 at exactly the 3 residual roots, 0 at the other 23 letters;
>   Σ D′m_s = 9 = deg f.”

**CONDITIONALITY:** **The deepest letter-reach test in the note** — a full sweep over `|F₂₇^×| = 26` letters, which is what makes the HE3-1L repair's fullness claim concrete at `f₁ = 3`.

**DERIVATION:** Run record.

*Arithmetic audit (rule 22), recomputed.*
- **Frame.** `Φ′ = x³ − 9x + 27` over ℤ₃. `D′ = 3`; the note gives `D′h = 3`, so `h = 1` ✓, and with `D′ = e₁f₁ = 3` and `K = F₂₇ = F_{3³}` we need `f₁ = 3, e₁ = 1` ✓. Check the polygon: coefficients `(27, −9, 0, 1)` at abscissae `(0,1,2,3)`; valuations `(3, 2, ∞, 0)`; lower hull from `(0,3)` to `(3,0)` has slope 1 ✓ `= h/e₁ = 1/1` ✓, and the pin at `(1,2)` sits ON the line (height `3 − 1 = 2`) ✓, at `(2, ∞)` above ✓ — **one side, slope 1, length 3, residual of degree 3** ✓ consistent with `f₁ = 3` and `e₁ = 1` ✓.
- **Letter count.** `|F₂₇^×| = 26` ✓ **“the 26-letter peel”** ✓; `3` roots + `23` non-roots = 26 ✓ **exact.**
- **`Σ D′m_s`.** `3 roots × D′(=3) × 1 = 9` ✓ and `deg f = D′μ = 3μ = 9` ⟹ `μ = 3` ✓ consistent.
- **Test height.** `λ = 4 > D′h = 3` ✓ legal, and `λ ≥ (D′−1)h = 2` ✓ so **every letter is reachable** by HE3-1L's fullness threshold ✓ — which is exactly what the 26-letter profile confirms ✓.
- **σ checks.** `(1,3)+(1,6)` sums to `3 + 6 = 9` ✓; `(1,9)` → 9 ✓; the Frobenius orbit `{η, η³, η⁹}` has size 3 ✓ (the orbit of `η` under `x ↦ x³` in `F₂₇`, closing after 3 steps since `η^{27} = η` ✓).
**Every number reproduces, including the frame's polygon.**

**RESOLUTION TRACE:** statement 1536–1542 · the lemma's fullness clause 508–513 (shard 1 `.21`).

**TEETH:** **Disposition: executable regression, exhaustive over the 26-letter set, with PARI adjudication on 4/4 members.** Together with P1's 8-letter sweep this is the note's strongest evidence that the letter reach is complete.

---

### EFF.HE3.s2of2.24  [run-record]  — §S9′ P4 with its `[r2]` scope disclosure

**CANONICAL STATEMENT:** verbatim, lines 1543–1562.

**FORM:** bulleted bold-headed run record with a long embedded `[r2, F-4]` disclosure.

> “* **P4 (LEMMA HE3-1L's exact set) [r2, F-4 2026-08-09: scope
>   disclosed — quasi-tautological as a residue check].** At
>   (e₁,f₁,h) = (1,2,1), the enumerated realized residues at
>   κ ∈ {0,1,2,3} equal the displayed T(κ)-span exactly: 2 letters
>   (F₃^×) at κ = 0, all 8 of F₉^× at κ ≥ 1 = (D′−1)h — the fullness
>   threshold as displayed. **What P4 does and does not test:** its
>   "realized residues" are computed BY the lemma's own slot-digit
>   extraction (`c0 = (C[0]//3**kap)%3 ...`), so P4 verifies the T(κ)
>   BOOKKEEPING (which slots are available at which heights), not the
>   residue arithmetic; the r1 sentence above ("the enumerated realized
>   residues res(C(theta)/n(kappa)(theta)) equal the displayed span")
>   overstated the leg's independence. The decorrelated residue test
>   exists as of PE2: `he3_pe2fresh.py` FR-C computes the realized
>   residues at (2,2,1) by PARI valuations + residue-field reduction
>   (`nfeltval`/`nfmodpr`, no slot formula), κ = 0..5, sizes
>   {2,2,8,8,8,8} = the T(κ)-span exactly, including the boundary
>   κ = 3 = (i₀+e₁(f₁−1))h. The runner docstring's "sympy integer
>   resultants" line was a slip (the code is the no-sympy
>   Sylvester/Bareiss route) — fixed in place at [r2]; runner pin
>   updated above, stdout byte-identical.”

**CONDITIONALITY:** **A self-administered vacuity finding of the sharpest kind: the leg computes its “measurement” using the very formula it purports to test.** `SUPERSESSION KIND: scope-pin` on what P4 establishes. **CHAIN: the r1 sentence (overstating independence) → the `[r2]` F-4 disclosure → PE2's FR-C as the decorrelated substitute. TERMINAL: FR-C.**
**FR-C is genuinely decorrelated**: PARI valuations + residue-field reduction (`nfeltval`/`nfmodpr`), **no slot formula** ✓ — so the residue arithmetic is computed by an independent route.
**A second, unrelated disclosure is folded in**: the docstring's “sympy integer resultants” was a slip; the code is the no-sympy Sylvester/Bareiss route. That is the docstring-only change (F2)'s exception accounts for (`.19`).

**DERIVATION:** Run record + a disclosure.

*Arithmetic audit (rule 22), recomputed.*
- **The r1 leg at `(e₁,f₁,h) = (1,2,1)`.** `D′ = 2`, `i₀(κ) = 0` for all κ (since `e₁ = 1`) ✓. `T(κ) = {t < 2 : κ ≥ (0 + 1·t)·1} = {t < 2 : κ ≥ t}` ⟹ `T(0) = {0}`, `T(κ) = {0,1}` for `κ ≥ 1` ✓. Span sizes: `|F₃^×| = 2` at κ = 0 ✓ (punctured 1-dim F₃-span), and `|F₉^×| = 8` at `κ ≥ 1` ✓ **exactly the displayed “2 letters at κ = 0, all 8 at κ ≥ 1”** ✓. Fullness threshold `(D′−1)h = 1` ✓ **matching “κ ≥ 1 = (D′−1)h”** ✓.
- **FR-C at `(e₁,f₁,h) = (2,2,1)`.** `D′ = 4`. `i₀(κ)` solves `i ≡ κ (mod 2)`, `0 ≤ i < 2`. `T(κ) = {t < 2 : κ ≥ (i₀ + 2t)}`. κ = 0: `i₀ = 0`, `T = {t : 0 ≥ 2t} = {0}` ⟹ size `|F₃^×| = 2` ✓. κ = 1: `i₀ = 1`, `T = {t : 1 ≥ 1 + 2t} = {0}` ⟹ 2 ✓. κ = 2: `i₀ = 0`, `T = {t : 2 ≥ 2t} = {0,1}` ⟹ 8 ✓. κ = 3: `i₀ = 1`, `T = {t : 3 ≥ 1+2t} = {0,1}` ⟹ 8 ✓. κ = 4, 5: likewise 8, 8 ✓. **Sizes `{2,2,8,8,8,8}` for κ = 0..5 — exactly the displayed tuple** ✓.
- **The boundary.** `(i₀ + e₁(f₁−1))h` at `κ = 3` with `i₀(3) = 1`: `1 + 2·1 = 3` ✓ **“including the boundary κ = 3”** ✓ — the first κ at which the odd class is full ✓.
**Both legs' spans reproduce exactly from the lemma's own `T(κ)` definition.** Note this confirms the *bookkeeping*, which is what P4's disclosure says it tests; FR-C's contribution is that the *residues* were computed independently.

**RESOLUTION TRACE:** statement 1543–1562 · the lemma 498–534 (shard 1 `.21`) · the F-4 finding 137 (shard 1 `.07`) · the runner pin 1494–1500 (`.19`).

ARTIFACT: `verification/openmath/he3_pe2fresh.py` ✓ present.

**TEETH:** **Disposition: `signed vacuity disclosure` (P4 is quasi-tautological as a residue check) + `accepted-with-decorrelation-supplied` (FR-C).** This is the note's most explicit acknowledgement that a green leg can be circular.

---

### EFF.HE3.s2of2.25  [scope-record]  — §S9′'s coverage note

**CANONICAL STATEMENT:** verbatim, lines 1564–1573.

**FORM:** bold-headed closing paragraph with an inline `[r2]` update.

> “Coverage note (honest): the sweeps run e₁ = 1 genres (f₁ ∈ {2,3}) over
> ℤ₃; e₁ ≥ 2 at f₁ ≥ 2 (where i₀(κ) cycles) is machine-exercised only
> through HE6's frozen battery (its (2,2,3) frame) and remains owed to a
> future HE3-side row; the μ ≤ 3 proofs are uniform in e₁.
> **[r2 2026-08-09]:** that row exists as of PE2 — `he3_pe2fresh.py`
> (committed at 6d0ff09) runs the (3;2,2,μ;1) family at Φ′ = x⁴+9 over
> ℤ₃ (e₁ = 2 ∧ f₁ = 2, 7/7 PARI members incl. a μ = 3 degree-12 member,
> HE3-1a/HE-NORM asserted at e₁ = 2, peel profiles over F₉^×, and the
> twist adjudicator `ma` — §S3 Remark [r2]); this note's own §S8/§S9′
> sweeps stay as recorded.”

**CONDITIONALITY:** **The `[r1]` coverage hole is CLOSED at `[r2]` and the closure is the same run that found the twist defect.** `SUPERSESSION KIND: as-of scoping`. **CHAIN: the `[r1]` note (e₁ ≥ 2 ∧ f₁ ≥ 2 owed, foreign contact only) → the `[r2]` update (PE2's own row supplies it). TERMINAL: the `[r2]` reading.**
**This is where the twist seam had to surface**: `i₀(κ) cycles` only at `e₁ ≥ 2`, and `W(k)` is built from `i₀` — so the first `e₁ ≥ 2` row is exactly the first row that could see the coherent/naive difference ✓ **and it did** (shard 1 `.24`). The coverage note and the F-1 finding are the same event seen from two sides.

**DERIVATION:** Coverage record.

*Arithmetic audit (rule 22).* The PE2 frame `Φ′ = x⁴ + 9` over ℤ₃ gives `(e₁,f₁) = (2,2)` ✓ (audited at shard 1 `.24`), `D′ = 4`, and a `μ = 3` member has degree `D′μ = 12` ✓ **matching “a μ = 3 degree-12 member”** ✓. `|F₉^×| = 8` for the peel profiles ✓.

**RESOLUTION TRACE:** statement 1564–1573 · the twist finding 253–286, 615–642 (shard 1 `.14`, `.24`) · the F-1 row 134 (shard 1 `.07`).

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12** (HE6's frozen battery is the foreign contact named).
PIN: `6d0ff09` ✓ commit.

**TEETH:** **`he3_pe2fresh.py`** — 7/7 PARI members at `e₁ = 2 ∧ f₁ = 2`, with HE-NORM asserted at `e₁ = 2` and the twist adjudicator. **Disposition: executable regression on a decorrelated instrument that closed a disclosed coverage hole AND found a CRITICAL-adjacent defect in the same run.**

---

### EFF.HE3.s2of2.26  [acceptance-box] · SERIES: HE3-GRADE-ARC, member 4 of 4 (TERMINAL)

**CANONICAL STATEMENT:** verbatim, lines 1577–1589.

**FORM:** `###` heading + a bold verdict paragraph.

> “### Dated correction (2026-08-09, post-PE3)
>
> **PE3 verdict (Fable, fresh context, `HE3_passPE3_report.md`): CLEAN —
> 0 CRITICAL, 0 GAP, 1 MINOR (M-1, corrected below). The
> consecutive-clean count moves 0/2 → 1/2 and HOLDS at 1/2 through this
> correction (minors-only precedent: the CLEAN bar is GAP-or-worse, and
> this repair touches a display parenthetical, not a consumed clause).**
> PE3's fresh route ran GREEN, 0 violations, at three geographies
> disjoint from the prior legs — the (2,1)/(3,1) letter-starved corners,
> a μ = 3 coherent family at (e₁,f₁) = (3,1), and non-prime Q = 4 over
> F₄[[t]] — with the coherent-vs-naive flip machine-adjudicated at each
> of the three, siding with the coherent read each time. The body above,
> §S1 (iii) included, stays BYTE-FROZEN; the correction lives here.”

**CONDITIONALITY:** **TERMINAL member of the HE3-GRADE-ARC SERIES: 1/2, NOT accepted.** Acceptance needs two consecutive clean passes; HE3 has one. **And five REAL findings landed after it** (`.28`–`.33`), none of which resets the counter but all of which are “awaiting sol discharge-confirmation”.
**Three things this append establishes beyond the grade:**
(i) **The CLEAN bar is stated**: “the CLEAN bar is GAP-or-worse”, so a minors-only pass is clean ✓ — the same rule GENHN uses.
(ii) **The freeze begins here** (F1).
(iii) **PE3's three geographies were disjoint from the prior legs** and all three re-adjudicated the coherent/naive flip in the coherent read's favour ✓ — **so the `[r2]` F-1 repair has been confirmed at four independent geographies in total** (PE2's `ma` plus PE3's three).
**One of the three geographies is `Q = 4` over `F₄[[t]]`** — which is exactly the case shard 1 `.12`'s starved-corner parenthetical omits, and PE3's M-1 finding is about that omission ✓ **the pass that found the omission also ran the omitted case.**

**DERIVATION:** Verdict record.

*Arithmetic audit (rule 22).* Pass ledger: PE1 NOT CLEAN (2C+4G+2M) → PE2 NOT CLEAN (0C+2G+3M) → PE3 CLEAN (0C+0G+1M). Under the stated bar: PE1 fails ✓, PE2 fails (GAPs) ✓, PE3 passes ✓. **One consecutive clean pass ⟹ 1/2** ✓ — **two are needed for acceptance, so HE3 is not accepted** ✓.

**RESOLUTION TRACE:** statement 1577–1589 · prior members 3–20, 120–139, 1278–1294 · the M-1 correction 1591–1618 (`.27`) · the later A5 wave 1622–1853.

ARTIFACT: `lean/notes/openmath/HE3_passPE3_report.md` ✓ present · `verification/openmath/he3_pe3fresh.py` ✓ · `he3_pe3fresh_output.txt` ✓ · `he3_pe3fresh_results.json` ✓.

**TEETH:** **PE3's fresh route: GREEN, 0 violations, three disjoint geographies.** **Disposition: executable regression on a decorrelated instrument; the coherent/naive mutant fired (or rather, sided) three more times.**

---

### EFF.HE3.s2of2.27  [changes-record]  — M-1 (the §S1 (iii) starved-corner parenthetical)

**CANONICAL STATEMENT:** verbatim, lines 1591–1618.

**FORM:** bold-headed dated correction with two bullets and a conservativity paragraph.

> “**M-1 (the §S1 (iii) starved-corner parenthetical), corrected in both
> readings.** The frozen parenthetical reads: "needing |K^×| =
> Q^{f₁} − 1 ≤ d_λ ≤ μ (at μ ≤ 3 only (Q,f₁) ∈ {(2,1), (3,1), (2,2)} can
> be starved)". Neither of its two readings matches that list:
>
> * **Under the displayed bound d_λ ≤ μ (= 3):** Q^{f₁} − 1 ≤ 3 ⟺
>   Q^{f₁} ∈ {2, 3, 4} (Q a prime power) ⟺ (Q,f₁) ∈
>   {(2,1), (3,1), (2,2), (4,1)}. The (4,1) omission is CURED here:
>   Q = 4 base rings are legal in this program (the equal-characteristic
>   F₄[[t]] base; PE3's FR3 runs one), and |F₄^×| = 3 ≤ 3.
> * **Under the in-context bound d_λ ≤ μ − 1 (≤ 2):** the sample
>   κ = D′h+1 is consumed only while a hypothetical low side is being
>   refuted, and that low side occupies horizontal length ≥ 1 of the
>   μ-budget, so the κ-side has d_λ ≤ μ − 1 ≤ 2. Then Q^{f₁} − 1 ≤ 2 ⟺
>   Q^{f₁} ∈ {2, 3}, and the reachable corner is (Q,f₁) ∈
>   {(2,1), (3,1)}: the listed (2,2) is UNREACHABLE at this site, and
>   (4,1) is excluded the same way.
>
> **Why the frozen fence stands (conservativity, per PE3 M-1).** §S1
> (iii) consumes GENHN's [r1] ERRATUM 2026-08-08 on the LISTED corner
> {(2,1), (3,1), (2,2)} — a superset of the in-context reachable corner
> {(2,1), (3,1)} — so the consumption covers the corner the display
> needs, and the fence PE2 recorded stays in force as written. The
> imprecision is live only for a future consumer re-using the
> parenthetical at a site where the starved side can fill the whole
> polygon (d_λ = μ, e.g. a single-side sampling argument): that consumer
> must take the four-element list of the first bullet, which adds Q = 4
> base rings to the fence.”

**SUPERSESSION KIND: counter re-reading** (the list re-counted under two explicit bounds) + **scope-pin** (the correction bites only for a future consumer at `d_λ = μ`). `TARGETS: s1of2.12`, `s1of2.11`(iii).

**CONDITIONALITY:** **The frozen text stands, and the reason is a conservativity argument, not a defence of the display.** The imprecision is real in both readings; it simply does not bite for this note's own use because the consumed GENHN corner is a superset. **A future consumer at `d_λ = μ` must use the four-element list.** That is a genuine forward liability and it is named.

**DERIVATION:** Two arithmetic enumerations.

*Arithmetic audit (rule 22), both bullets independently recomputed — and this compiler reached the same two lists at shard 1 `.11` BEFORE reading this append.*
- **Bullet 1.** `Q^{f₁} − 1 ≤ 3` ⟹ `Q^{f₁} ≤ 4`; prime powers ≤ 4 that are ≥ 2: `2, 3, 4` ✓. Pairs `(Q, f₁)` with `Q` a prime power: `Q^{f₁} = 2 ⟹ (2,1)` ✓; `= 3 ⟹ (3,1)` ✓; `= 4 ⟹ (2,2)` or `(4,1)` ✓ **four pairs** ✓. `|F₄^×| = 3 ≤ 3` ✓.
- **Bullet 2.** The low side occupies `L ≥ 1` of the `μ`-budget, so the κ-side has `d_λ ≤ μ − 1 = 2` ✓. `Q^{f₁} − 1 ≤ 2` ⟹ `Q^{f₁} ≤ 3` ⟹ `Q^{f₁} ∈ {2,3}` ⟹ `(2,1), (3,1)` ✓ **two pairs, and `(2,2)` is excluded because `Q^{f₁} = 4 > 3`** ✓.
- **Conservativity.** `{(2,1),(3,1)} ⊆ {(2,1),(3,1),(2,2)}` ✓ **superset** ✓ so the consumption covers the need ✓.
**Both enumerations reproduce, and the conservativity is valid.**

**RESOLUTION TRACE:** statement 1591–1618 · target 218–222 (shard 1 `.12`) · PE3's Q = 4 leg 1584–1588 (`.26`).

XREF: `GENHN_PROOF_2026-08-08.md:ERRATUM 2026-08-08` — count **1**.

**TEETH:** **PE3's FR3 runs a Q = 4 base ring** — the omitted case has machine contact from the pass that found the omission ✓. **Disposition: `arithmetic recount` (rule 27) with an accompanying fresh-instrument leg.**

---

### EFF.HE3.s2of2.28  [changes-record]  — the A5 adjudication header (the R8 umbrella)

**CANONICAL STATEMENT:** verbatim, lines 1622–1632.

**FORM:** `###` heading + a framing paragraph.

> “### Dated corrections (2026-08-12 — sol certification A5: the R8 chain challenge adjudicated at HEAD)
>
> The sol-5.6 chain read of this note (gpt-5.6-sol high,
> runs/residues/R8_he3_output.log, 2026-08-12) returned CHALLENGE with
> five findings. The A5 certification run (gpt-5.6-sol high,
> runs/cert/A5_he3_output.log) re-adjudicated all five against HEAD
> including every dated append: all five are REAL with derived repairs
> — the five dated corrections below (R8-2 PROVES the previously boxed
> unramified branch; R8-3 PROVES the D′ = 1 case; no accepted display
> of THEOREM HE3.A or COROLLARY HE3.B is weakened). Everything above
> this heading is byte-untouched by this append.”

**CONDITIONALITY:** **This is the charge's “R8 umbrella”, and its verdict is the harshest external result on this note: 5/5 REAL — after a CLEAN pass.**
**Three properties distinguish it from GENHN's A2 wave:**
(i) **All five are REAL with derived repairs; NONE is obstructed.** GENHN's A2 had two REAL-but-OBSTRUCTED findings requiring owner sign-off; HE3's A5 has zero.
(ii) **Two of the five PROVE previously boxed material** (R8-2, R8-3) — the wave *shrinks* the note's conditionality.
(iii) **“no accepted display of THEOREM HE3.A or COROLLARY HE3.B is weakened”** — the statement fence held; every repair is additive or display-scope.
**The wave's own status:** “Ledger: HE3's row → 5 repairs folded, **awaiting sol discharge-confirmation**” (1851–1853). See OPEN-CALL 2.

*Arithmetic audit (rule 22).* Five findings ✓ and five dated corrections below (`.29`–`.33`) ✓ **one block per finding, no orphans** ✓. Of the five: R8-1 replacement, R8-2 license, R8-3 license, R8-4 replacement, R8-5 provenance-rider — **2 licenses + 2 replacements + 1 provenance-rider = 5** ✓.

**DERIVATION:** Adjudication framing.

**RESOLUTION TRACE:** statement 1622–1632 · the five blocks 1634–1819 · verification 1821–1853 (`.34`).

ARTIFACT: `runs/residues/R8_he3_output.log` ✓ · `runs/cert/A5_he3_output.log` ✓ — 2/2 present.

**TEETH:** **`decorrelated-model audit` (rule 27)** — a fresh-context gpt-5.6-sol chain read, re-adjudicated by a second sol run against HEAD *including every append*. **HE3's own three hostile passes had missed all five.** Disposition: the strongest argument in this shard for model-diverse verification post-acceptance-attempt.

---

### EFF.HE3.s2of2.29  [changes-record]  — R8-1 (HE3-5 is recursive, not a one-unit bound)

**CANONICAL STATEMENT:** verbatim, lines 1634–1689.

**FORM:** `###` heading + a diagnosis, a two-clause recursive criterion with proof, a three-bullet replacement, a worked counterexample, and a re-scoping of the machine table.

> “### Dated correction (2026-08-12, post-R8) — R8-1: HE3-5 is recursive, not a one-unit bound
>
> The first displayed criterion of LEMMA HE3-5 decides ONE consultation:
> whether the multiplicity of a residual root at the current node is
> lift-stable. It is not by itself a stopping bound for the complete
> stage-α history. Correct the introductory phrase “has an exact answer”
> to mean the following recursive answer.
>
> At every node ν of a proposed read history, let c_ν be that node's
> dv-cap and let b_{ν,j} be the known supporting-line height at every
> consulted abscissa j. The history is DECIDED exactly when:
>
> 1. every terminal residual polynomial is separable; and
> 2. at every nonterminal node ν, every recentered value consulted there
>    is either read exactly below c_ν, or is known only to be ≥ c_ν but
>    satisfies c_ν > b_{ν,j}, so that the required strict inequality
>    above the supporting line is nevertheless certified.
>
> Proof. At one node this is exactly LEMMA HE3-2(b) plus GENHN-3(a), as
> proved in HE3-5. If the residual is terminal, nothing further is
> consulted. If it triggers a stage-α or stage-CS child, apply the same
> criterion to that child's recentered development. Induction on the
> finite read history gives necessity and sufficiency. ∎
>
> Consequently, replace the three bullets following HE3-5 by:
>
> * for a side spanning the whole current polygon, e₁N > μλ certifies
>   the INITIAL residual multiplicities at that node;
> * this decides the leaf only when those residuals are terminal;
>   a repeated residual root can require arbitrarily many further window
>   units, according to the heights reached by its descendants;
> * the σ-undecided mass is therefore obtained by stratifying by complete
>   read histories and their deepest consulted heights. No single
>   “one more window unit” law, nor one unstratified exact q-power,
>   follows from HE3-5.
>
> The absence of a uniform additive bound is concrete. Over O = ℤ₅ take
> e₁ = 1, f₁ = 2, D′ = 2, h = 1, λ = 3, a height-3 carrier C with
> res(C(θ)/n(3)(θ)) = s, and M > 9. Put
>
>     f = (Φ′ − C)³ + 5^M.
>
> Its Φ′-resolvent has pins on the slope-3 line and residual
> (Z − s)³, so the first consultation is ALPHA. After the recentering
> Φ″ = Φ′ − C, however,
>
>     f = Φ″³ + 5^M,
>
> and the next polygon reaches height M. Certifying that child can require
> a cap beyond M, arbitrarily far past the initial threshold μλ = 9.
> Thus the former “one more window unit” sentence is false.
>
> Accordingly, §S9's HE-BND table is evidence for the selected aligned
> rows only: it is consistent with the local cap criterion and exhibits
> a two-step profile in those rows, but it does not verify a general
> two-step boundary law.”

**SUPERSESSION KIND: replacement** (the three bullets and the introductory phrase) + **scope-pin** (the HE-BND table). `TARGETS: s1of2.37` (the bullets), `s1of2.38` (the Interpretation's framing), `s2of2.17` (the table's generality).

**CONDITIONALITY:** **The finding is a genuine mathematical correction, backed by an explicit counterexample, and it removes a claim the note's own machine leg was scored against.** Three consequences:
(i) **The recursive criterion is now the definition of DECIDED for read histories** — and it *agrees* with DEFINITION 2 (shard 1 `.15`), whose condition (b) already quantified over every event. So R8-1 does not contradict DEFINITION 2; it corrects HE3-5's *bound*.
(ii) **HE3-BOX-5 item (4)'s open question is sharpened, not closed** (`.07`).
(iii) **The HE-BND table survives as a measurement and loses its generality** (`.17`).
**Its own status:** awaiting sol discharge-confirmation.

**DERIVATION:** The two-clause criterion with an induction proof, plus the counterexample.

*Arithmetic audit (rule 22), the counterexample recomputed from scratch.*
- **Frame.** `O = ℤ₅`, `e₁ = 1, f₁ = 2, D′ = 2, h = 1`, so `dv = v` ✓ and `D′h = 2` ✓. Test height `λ = 3 > D′h = 2` ✓ **legal** ✓.
- **The expansion.** `f = (Φ′ − C)³ + 5^M = Φ′³ − 3CΦ′² + 3C²Φ′ − C³ + 5^M` ✓. Pins: `A₂ = −3C` with `dv = dv(C) = 3` ✓ (`v(3) = 0` in ℤ₅ ✓); `A₁ = 3C²` with `dv = 6` ✓; `A₀ = −C³ + 5^M` with `dv = min(9, M) = 9` for `M > 9` ✓.
- **The line.** Through `(3, 0)` with slope 3: heights `0, 3, 6, 9` at `j = 3, 2, 1, 0` ✓ — **all four pins ON the line** ✓, so one side of slope `λ = 3`, `L_λ = 3 = μ` ✓, and the residual is the cube `(Z − s)³` ✓ (binomial coefficients `1, −3, 3, −1` are the cube's, and `s` is `C`'s residue ✓).
- **`μλ = 9`** ✓ **matching the displayed threshold** ✓.
- **After recentering.** `Φ″ = Φ′ − C` ⟹ `f = Φ″³ + 5^M` ✓ **exactly** ✓; its Φ″-development has `A₀ = 5^M` at height `M` ✓ **and `M` is arbitrary** ✓.
- **Conclusion.** Certifying the child needs a cap `> M`, unbounded past 9 ✓ **the “one more window unit” bullet is false** ✓.
- **Why char 5 and `f₁ = 2`?** `e₁ = 1` makes the normalizers π-powers with no wrap ✓ (the A5 verification note says so at 1826–1827 ✓), keeping the example clean. **This compiler's independent recomputation matches the verification note's hand-check line for line.**
**The counterexample is exact.**

**RESOLUTION TRACE:** statement 1634–1689 · targets 1238–1258, 1267–1274 (shard 1 `.37`, `.38`), 1463–1477 (`.17`) · verification 1823–1830 (`.34`).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` — count **11**.

**TEETH:** **`decorrelated-model audit` with a CONSTRUCTED counterexample.** No battery row could have produced it — the note's rows are aligned `λ = 3, μ = 3` loci at bounded `N`, and the counterexample needs an unbounded `M`. **The HE-BND table, which measured the refuted bullet, is re-scoped rather than discarded** — the measurement stands, the law does not.

---

### EFF.HE3.s2of2.30  [lemma]  — R8-2: LEMMA HE3-4U (the unramified split-sum)

**CANONICAL STATEMENT:** verbatim, lines 1691–1734.

**FORM:** `###` heading + a supersession sentence + a blockquoted bold lemma + a proof + a closing correction.

> “### Dated correction (2026-08-12, post-R8) — R8-2: the unramified branch is repaired by split-component summation
>
> The assertion in §S6.2 that BOTH base-change branches remain boxed is
> superseded for branch (i). Only the ramified branch (ii) remains in
> HE3-BOX-6.
>
> > LEMMA HE3-4U (unramified split-sum). Let λ be an integer slope and
> > let r ∈ K[Z] be a separable irreducible factor of R_λ of degree d.
> > Then |S_r| = D′d.
>
> Proof. Choose m divisible by d (and by the degrees of the other
> residual factors under simultaneous use), large enough that the new
> residue field has more than μ nonzero letters, and put c := f₁m.
> Let O₁/O be the unramified extension of degree c. Since f₁ | c, its
> residue field F_{Q^c} contains K = F_{Q^{f₁}}, and Φ′ factors over O₁
> into exactly f₁ conjugate keys
>
>     Φ′ = ∏_{a=1}^{f₁} Φ′_a,
>
> each of degree e₁ and with stage invariants (e₁,1). Hensel, equivalently
> the imported sibling splitting of GENIND-3, splits the opening block of
> f into the corresponding f₁ blocks of degree e₁μ.
>
> For the a-th component the coherent residual is the image of R_λ under
> the associated embedding K → F_{Q^c}. The relative residue extension
> has degree c/f₁ = m, so the image of r splits into d distinct linear
> factors. The integer-slope rational peel, now applied with stage degree
> D′_a = e₁, assigns exactly e₁ roots to each of those d linear factors.
> Thus the a-th component contributes e₁d roots, and summing over all
> f₁ components gives
>
>     |S_r| = f₁·e₁·d = D′d.
>
> The union just counted is exactly S_r: on component a the fixed
> K-polynomial r is read through that component's residue embedding, and
> LEMMA HE3-6 shows that these conjugate componentwise classes assemble
> to the original Galois-stable label class. No claim that a single split
> key still contributes D′ roots is used. ∎
>
> Therefore §S6.2 branch (i) is proved, not boxed. The phrase “both
> branches below are therefore to be read as BOXED” is corrected to
> “branch (ii) alone is BOXED.” COROLLARY HE3.B's single μ ≥ 4
> reservation is consequently again accurate: it is the ramified
> fractional-slope branch of HE3-BOX-6.”

**SUPERSESSION KIND: license** (a boxed branch becomes proved) + **inventory completion** (HE3-BOX-6's item list shrinks to one). `TARGETS: s1of2.33` (the “BOTH … BOXED” verdict), `s2of2.06` (the box), `s1of2.17` and `s1of2.01` (the “ONE named branch” claim, now accurate).

**CONDITIONALITY:** **The repair is designed around the exact defect §S6.2 named.** §S6.2's diagnosis was that “each rational residual root contributes D′ roots” is false after an unramified base change, because `Φ′` splits. **HE3-4U does not repair that claim — it abandons it**: “**No claim that a single split key still contributes D′ roots is used.**” Instead it counts per split component (`e₁` roots each) and sums over the `f₁` components. **That is a structurally different argument, not a patch**, and it is why the repair is a proof rather than a scope-pin.
**It consumes LEMMA HE3-6** (shard 1 `.35`) to assemble the componentwise classes — so the r1 equivariance discharge is load-bearing here too.
**Its own status:** awaiting sol discharge-confirmation.

**DERIVATION:** Quoted in full above.

*Arithmetic audit (rule 22), every step recomputed.*
- **The base-change degree.** `c := f₁m` with `d | m` ✓. `f₁ | c` ✓ ⟹ `F_{Q^c} ⊇ F_{Q^{f₁}} = K` ✓.
- **The splitting of Φ′.** Over an unramified extension of degree `c` with `f₁ | c`, the key `Φ′` (with residue degree `f₁` and ramification `e₁`) splits into `gcd(f₁, c) = f₁` conjugate factors ✓ **each of degree `D′/f₁ = e₁`** ✓ with stage invariants `(e₁, 1)` ✓ (residue degree collapses to 1 because the residue field now contains `K`) ✓.
- **The block splitting.** The opening block has degree `D′μ`; splitting into `f₁` blocks gives `D′μ/f₁ = e₁μ` each ✓ **matching “f₁ blocks of degree e₁μ”** ✓.
- **The residual's splitting.** Relative residue extension degree `c/f₁ = m` ✓; `d | m` ⟹ the degree-`d` irreducible `r` splits completely into `d` distinct linear factors over `F_{Q^c}` ✓ (a degree-`d` irreducible over `K` splits in the degree-`m` extension iff `d | m` ✓).
- **The count.** Per component: `d` linear factors × `e₁` roots each (the integer-slope rational peel at stage degree `D′_a = e₁`) = `e₁d` ✓. Over `f₁` components: `f₁ · e₁ · d = D′d` ✓ **exactly LEMMA HE3-4's display at `ℓ = 1`** ✓.
- **The letter condition.** “large enough that the new residue field has more than μ nonzero letters” — needed so the peel has non-root letters available ✓ (the same condition §S6.2's boxed (i) used) ✓.
**Every step reproduces, and this compiler's recomputation matches the A5 verification note's own check (1833–1837) line for line.**

**RESOLUTION TRACE:** statement 1691–1734 · targets 1022–1086 (shard 1 `.33`), 1334–1368 (`.06`), 333–367 (shard 1 `.17`) · verification 1830–1839 (`.34`).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6** (the sibling splitting).
XREF: `HE3_PROOF_2026-08-08.md:HE3-4U` — self-count **2**.

**TEETH:** **PROOF-ONLY.** Branch (i) is reachable only at `μ ≥ 4` in the *boxed* sense (at `μ ≤ 3` the subtraction argument of shard 1 `.33` handles non-rational factors without base change), and `μ ≥ 4` is unexercised by any row (HE3-BOX-3). Coverage-hole sentence: “NOT exercised by machine: … μ ≥ 4”. **Disposition: `decorrelated-model audit` for the finding; PROOF-ONLY for the lemma.**

---

### EFF.HE3.s2of2.31  [lemma]  — R8-3: LEMMA HE3-4D1 (the linear-key case)

**CANONICAL STATEMENT:** verbatim, lines 1736–1772.

**FORM:** `###` heading + a diagnosis + a blockquoted bold lemma + a proof + a consequence.

> “### Dated correction (2026-08-12, post-R8) — R8-3: the D′ = 1 case is direct
>
> The implication “μ ≥ 4, i.e. n ≥ D′μ ≥ 8” requires a case split; an
> ambient genre has not been assumed to satisfy D′ ≥ 2.
>
> > LEMMA HE3-4D1 (the linear-key case). If D′ = 1, THEOREM HE3.A holds
> > for every μ without either base-change branch of HE3-4.
>
> Proof. D′ = e₁f₁ = 1 forces e₁ = f₁ = 1 and Φ′ = x − a for some
> a ∈ O. Since deg A_j < D′, every A_j is a constant, and translation
> gives the identity
>
>     f(a + Y) = Y^μ + Σ_{j<μ} A_jY^j = F(Y)
>
> over the original complete DVR O. Thus the stage read is literally the
> ordinary degree-μ Newton/Hensel read of f after a translation, rather
> than a proxy whose coefficients must be compared at θ and at roots ρ.
>
> At a terminal side λ = u/ℓ with a separable irreducible residual factor
> r of degree d, the classical Newton-polygon and Hensel read produces
> the corresponding factor of degree ℓd. Its roots have ramification
> index divisible by ℓ and residue degree divisible by d; since their
> product is the factor degree ℓd, the invariants are exactly (ℓ,d).
> Repeated residual factors are handled by the recursively recentered
> read, and termination with separable terminal residuals is precisely
> DEFINITION 2. Translation preserves irreducibility and the invariants
> (e,f), proving HE3.A. ∎
>
> Hence the fractional-side configuration at D′ = 1 is unconditional,
> including the displayed quartic example. The unresolved ramified
> base-change branch can occur only after excluding this direct case,
> so there D′ ≥ 2; together with μ ≥ 4 this gives
>
>     n = D′μ ≥ 2·4 = 8.
>
> Therefore the advertised unconditional range n ≤ 7 survives, now with
> the missing derivation displayed.”

**SUPERSESSION KIND: license** (an undisplayed hypothesis is supplied and the excluded case proved) + **inventory completion**. `TARGETS: s2of2.06` (HE3-BOX-6's `n ≥ 8` derivation), `s1of2.17` and `s1of2.01` (the `n ≤ 7` range).

**CONDITIONALITY:** **The finding is that `n ≥ D′μ ≥ 8` silently assumed `D′ ≥ 2`, and the repair is to prove the excluded case outright rather than to add the hypothesis.** That is the stronger of the two available moves: it *widens* what is unconditional (the `D′ = 1` case now holds at **every** μ) rather than narrowing the claim.
**The `D′ = 1` case is not exotic** — PE2's FR-D leg runs at `Φ′ = x − 2` over ℤ₂, i.e. exactly `D′ = 1` (`.22`) ✓. So the case R8-3 closes had machine contact all along.
**Its own status:** awaiting sol discharge-confirmation.

**DERIVATION:** Quoted in full above.

*Arithmetic audit (rule 22), recomputed.*
- **`D′ = 1` forces the frame.** `D′ = e₁f₁ = 1` with `e₁, f₁ ≥ 1` ⟹ `e₁ = f₁ = 1` ✓; `Φ′` monic of degree 1 ⟹ `Φ′ = x − a` ✓.
- **The A_j are constants.** `deg A_j < D′ = 1` ⟹ `deg A_j ≤ 0` ✓.
- **The translation identity.** With `Φ′ = x − a`, the Φ′-development `f = Φ′^μ + Σ A_jΦ′^j` evaluated at `x = a + Y` gives `Φ′(a+Y) = Y` ✓ hence `f(a+Y) = Y^μ + Σ A_jY^j = F(Y)` ✓ **exact** ✓.
- **The invariants.** A terminal side `λ = u/ℓ` with separable irreducible residual factor `r` of degree `d` produces a factor of degree `ℓd` ✓ (classical Newton/Hensel) ✓; its roots have `ℓ | e` and `d | f` ✓, and `ef = ℓd` ✓ forces `(e,f) = (ℓ,d)` exactly ✓ — **the same forcing pattern as shard 1 `.34`** ✓.
- **Consistency with HE3.A's dictionary.** At `D′ = 1`, `(e₁e_s, f₁f_s) = (1·ℓ, 1·d) = (ℓ, d)` ✓ **matching** ✓.
- **The `n ≥ 8` chain.** Branch (ii) needs `μ ≥ 4` ✓ and, after excluding `D′ = 1`, `D′ ≥ 2` ✓ ⟹ `n = D′μ ≥ 8` ✓ **the derivation the box omitted** ✓.
**Every step reproduces, and this compiler independently identified the same gap at shard 1 `.17`'s audit before reading this append.**

**RESOLUTION TRACE:** statement 1736–1772 · target 1349–1353 (`.06`), 353–355 (shard 1 `.17`) · the `D′ = 1` machine contact 1530–1535 (`.22`) · verification 1839–1842 (`.34`).

XREF: `HE3_PROOF_2026-08-08.md:HE3-4D1` — self-count **2**.

**TEETH:** **PROOF-ONLY as a lemma**, but the case it covers has machine contact at PE2's FR-D (`D′ = 1` over ℤ₂, both branches, PARI-confirmed) ✓. **Disposition: `decorrelated-model audit` for the finding; `accepted-with-decorrelation-supplied` for the case.**

---

### EFF.HE3.s2of2.32  [changes-record]  — R8-4 (piecewise definition of ramified label classes)

**CANONICAL STATEMENT:** verbatim, lines 1774–1793 (rule 14 double-emission: the source's indented display is inside the quotation, the `[TABLE]` transcription follows).

**FORM:** `###` heading + a replace-this-by-that instruction with two indented ASCII displays.

> “### Dated correction (2026-08-12, post-R8) — R8-4: piecewise definition of ramified label classes
>
> In LEMMA HE3-4 replace the displayed definition of S_r by the following
> definition. Write y_ρ := Φ′(ρ), λ = u/ℓ in lowest terms, and
>
>     β_ρ :=
>       res(y_ρ / n(λ)(ρ))          if ℓ = 1,
>       res(y_ρ^ℓ / n(u)(ρ))        if ℓ ≥ 2.
>
> Then
>
>     S_r := { ρ : dv(y_ρ) = λ and ι_ρ(r)(β_ρ) = 0 },
>
> where ι_ρ : K → k̄ is the embedding η_θ ↦ η_ρ from LEMMA HE3-0.
>
> Both quotients displayed above have dv-value zero in their respective
> cases: for ℓ ≥ 2, dv(y_ρ^ℓ) = ℓλ = u = dv(n(u)(ρ)).
> Thus β_ρ exists, and this definition is exactly the repaired root read
> of HE3-0(iii). All later occurrences S_{Z−s} lie in the integer-slope
> case and are unchanged.”

`[TABLE]` — the piecewise definition transcribed:

| case | β_ρ | dv of the quotient |
|---|---|---|
| ℓ = 1 | res(y_ρ / n(λ)(ρ)) | λ − λ = 0 |
| ℓ ≥ 2 | res(y_ρ^ℓ / n(u)(ρ)) | ℓλ − u = 0 |

**SUPERSESSION KIND: replacement** (the `S_r` display). `TARGETS: s1of2.32`.

**CONDITIONALITY:** **A propagation fix, not a new idea** — the A5 verification note says so (1843–1847): the piecewise `β_ρ` is “confirmed IDENTICAL to the r1 F6 repair already installed in HE3-0(iii)/HE3-0′ … this correction **propagates it to the one display the r1 round missed**”. `SUPERSESSION KIND` is therefore replacement at *display* scope with no content change.
**The closing clause bounds the blast radius**: “All later occurrences S_{Z−s} lie in the integer-slope case and are unchanged” ✓ — verified: shard 1 `.32`'s peel argument and `.34`'s stage-α step both use `S_{Z−s}` at integer slopes ✓.
**Its own status:** awaiting sol discharge-confirmation.

**DERIVATION:** The `dv = 0` checks are displayed.

*Arithmetic audit (rule 22).* `ℓ = 1`: `dv(y_ρ) = λ` and `dv(n(λ)(ρ)) = λ` ⟹ quotient `dv = 0` ✓. `ℓ ≥ 2`: `dv(y_ρ^ℓ) = ℓ·λ = ℓ·(u/ℓ) = u` ✓ and `dv(n(u)(ρ)) = u` ⟹ `dv = 0` ✓ **exactly the displayed check** ✓. **Both residues exist** ✓. Identity with the r1 F6 form: shard 1 `.25`'s display is “β_ρ := res(y_ρ/n(λ)(ρ)) at ℓ = 1, β_ρ := res(y_ρ^ℓ/n(u)(ρ)) at ℓ ≥ 2” ✓ **character-identical** ✓ confirming the verification note's claim.

**RESOLUTION TRACE:** statement 1774–1793 · target 983–989 (shard 1 `.32`) · the identical r1 repair 660–669 (shard 1 `.25`) · verification 1842–1848 (`.34`).

**TEETH:** **PROOF-ONLY** — the `ℓ ≥ 2` case with `d ≥ 2` is branch (ii), unexercised; the `ℓ ≥ 2, d = 1` case has one machine contact (`he3r1_supp.py` P2's `λ = 7/2` member, `.21`) ✓. **Disposition: `decorrelated-model audit` for the finding.**

---

### EFF.HE3.s2of2.33  [changes-record]  — R8-5 (HE3-0 provenance correction)

**CANONICAL STATEMENT:** verbatim, lines 1795–1819.

**FORM:** `###` heading + a replace-this-by-that instruction with two blockquoted passages.

> “### Dated correction (2026-08-12, post-R8) — R8-5: HE3-0 provenance correction
>
> In the proof sketch of LEMMA HE3-0 replace
>
> “(i)/(ii): the SLOT LEMMA (GENHN-2) is stated for any ξ with
> (T1)/(T2)”
>
> by:
>
> “(i)/(ii): at θ use GENHN-2; at the root ρ use LEMMA HE6-0″, because
> ρ satisfies (T1)/(T2). HE6-0″ re-runs the slot argument at an arbitrary
> (T1)/(T2) point and gives
>
>     dv(A_j(ρ)) = min_i(e₁v(a_{j,i}) + ih) = dv(A_j(θ)),
>
> together with the same universal residue polynomial in η_ρ. Reading
> the two sides with DEFINITION 1's matching coherent normalizers sends
> the stage residual through the F_Q-embedding
> ι_ρ : K → k̄, η_θ ↦ η_ρ. Hence the residual polynomials at ρ are the
> images of the coherent stage residuals and have the asserted
> factorization type.”
>
> This is a provenance correction only: the required ξ-form lemma was
> already consumed at §S0 [r1, F4], but the HE3-0 proof sentence had not
> been updated to cite it.”

**SUPERSESSION KIND: provenance-rider** (the claim stands; its cited source is replaced). `TARGETS: s1of2.25`.

**CONDITIONALITY:** **A stale citation surviving a repair round, found by a fresh model 20 days later.** The `[r1] F4` round corrected the §S0 *import* (shard 1 `.03`) but left this one downstream *proof sentence* citing GENHN-2 at points where GENHN-2 does not apply. **No mathematical content moves** — the note says so and it checks: HE6-0″ supplies exactly the consumed form ✓.
**This is the clearest instance in the sweep of a repair round's incomplete propagation**, and it is the same failure mode as R8-4 (the r1 F6 repair not reaching one display).
**Its own status:** awaiting sol discharge-confirmation.

**DERIVATION:** Provenance substitution; the replacement text is HE6-0″'s statement.

*Arithmetic audit (rule 22).* The replacement's displayed identity `dv(A_j(ρ)) = min_i(e₁v(a_{j,i}) + ih) = dv(A_j(θ))` ✓ is exactly the slot formula of shard 1 `.03`'s import, with `ξ = ρ` ✓ — and the equality with `dv(A_j(θ))` holds because the formula's right side depends only on the coefficients, not on the point ✓ **which is the whole content of the ξ-form** ✓.

**RESOLUTION TRACE:** statement 1795–1819 · target 673–682 (shard 1 `.25`) · the import it should have cited 42–60 (shard 1 `.03`) · verification 1848–1851 (`.34`).

XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.

**TEETH:** NONE (provenance). **Disposition: `decorrelated-model audit` — a citation-scope defect no instrument could see.**

---

### EFF.HE3.s2of2.34  [instrument-record]  — the A5 verification parenthetical

**CANONICAL STATEMENT:** verbatim, lines 1821–1853 (the note's final lines).

**FORM:** italic parenthetical closing the A5 block, finding by finding.

> “*(Corrections R8-1..R8-5 derived by the A5 certification run
> (gpt-5.6-sol high, runs/cert/A5_he3_output.log, 2026-08-12);
> orchestrator verification before transcription — R8-1: HE3-5's three
> bullets located verbatim (L1249–1258) and its proof confirmed to
> decide one consultation only (its own citation set is HE3-2(b) +
> GENHN-3(a)); the counterexample re-derived by hand: at e₁ = 1 the
> normalizers are π-powers with no wrap, the binomial coefficients
> −3C, 3C², −C³ + 5^M pin the slope-3 line with residual exactly
> (Z − s)³ for M > 9, and the recentered development f = Φ″³ + 5^M has
> polygon height M — unbounded past μλ = 9. R8-2: §S1's
> branch-(ii)-only reservation (L350–353) vs §S6.2's "BOTH are stated
> too cheaply" (L1049) confirmed as the internal contradiction;
> HE3-4U's arithmetic re-derived (f₁ | c makes Φ′ split into f₁
> conjugate (e₁,1)-keys by Hensel at the unramified base change;
> d | m = c/f₁ makes r split completely into d linears; the ℓ = 1 peel
> at stage degree e₁ gives e₁ roots per label; f₁·e₁·d = D′d = the
> HE3-4 display at ℓ = 1); consumed pieces (GENIND-3 sibling
> splitting, the §S6.2 integer-slope peel, LEMMA HE3-6 equivariance)
> all present at HEAD. R8-3: BOX-6's "n ≥ e₁f₁μ ≥ 8" confirmed to
> consume an undisplayed D′ ≥ 2; HE3-4D1 is the direct classical
> Newton/Hensel read at Φ′ = x − a (constants A_j, translation
> identity) — an additive completion, no display weakened. R8-4:
> HE3-4's S_r display confirmed still ill-defined at ℓ ≥ 2 at HEAD
> (n(λ) at fractional λ; BOX-6's own "no element of R has non-integer
> dv"); the piecewise β_ρ confirmed IDENTICAL to the r1 F6 repair
> already installed in HE3-0(iii)/HE3-0′ ("β = res(y^ℓ/n(u))", the
> r1 record's own row) — this correction propagates it to the one
> display the r1 round missed. R8-5: the stale GENHN-2 sentence
> located (L677) against the r1 F4 restriction; HE6-0″ (as corrected
> at this campaign's A3 fold) supplies exactly the consumed form.
> Transcribed unaltered per the standing division of labor. Ledger:
> HE3's row → 5 repairs folded, awaiting sol
> discharge-confirmation.)*”

**CONDITIONALITY:** **The only evidence that the transcribed sol output was independently checked, and it is finding-by-finding.** Its closing line fixes the wave's status: “**Ledger: HE3's row → 5 repairs folded, awaiting sol discharge-confirmation.**”
**Every claim in it is a hand re-derivation or a span re-read — no instrument ran.** That is appropriate for four of the five (display/provenance/contradiction findings) and for R8-1's counterexample, which is symbolic.
**One line-number pin is checkable and checks out:** “the stale GENHN-2 sentence located (L677)” — HE3 line 677 is inside the HE3-0 proof sketch ✓ (shard 1 `.25`'s DERIVATION spans 673–682) ✓. Likewise “HE3-5's three bullets located verbatim (L1249–1258)” ✓ (shard 1 `.37` spans 1238–1258, bullets at 1249–1258) ✓ and “§S1's branch-(ii)-only reservation (L350–353)” ✓ (shard 1 `.17` spans 333–367, the reservation at 349–355) ✓ **all three line pins land in the right spans.**
**One external dependency is disclosed**: “HE6-0″ (**as corrected at this campaign's A3 fold**) supplies exactly the consumed form” — so HE3's most load-bearing citation depends on an HE6-side correction from the same campaign. Recorded; not verified here (OPEN-CALL 4).

*Compiler cross-check (rule 22).* This shard independently recomputed **all five** of the verification claims: R8-1's counterexample (`.29`) ✓; R8-2's split-sum arithmetic (`.30`) ✓; R8-3's `D′ ≥ 2` gap (`.31`, and independently at shard 1 `.17` before reading the append) ✓; R8-4's `dv = 0` checks and the identity with the r1 F6 form (`.32`) ✓; R8-5's slot identity (`.33`) ✓. **Five of five reproduced. No discrepancy between the parenthetical's claims and this compiler's independent recomputation.**

**DERIVATION:** Verification record.

**RESOLUTION TRACE:** statement 1821–1853 · the five blocks 1634–1819 · the line pins verified above.

ARTIFACT: `runs/cert/A5_he3_output.log` ✓ · `runs/residues/R8_he3_output.log` ✓.
XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6**.

**TEETH:** **`in-house hostile pass` / `arithmetic recount` (rule 27).** No instrument ran; the disposition is hand verification, disclosed as such.

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every count is `grep -cF '<designation>' <file>` run at HEAD. **19 distinct designations, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-1` | 4 | The digit bijection legitimising the stage-coordinate enumeration (`.08`) |
| 2 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` | 3 | Declared NOT consumed (`.01`) |
| 3 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` | 5 | The weld face absent from HE3's σ chain (`.01`) |
| 4 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-4` | 3 | The perimeter HE3-BOX-2 inherits |
| 5 | `GENHN_PROOF_2026-08-08.md:S11.F` | 10 | Its derivation |
| 6 | `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` | 11 | Lift-stability, consumed by HE3-5 and R8-1 |
| 7 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` | 11 | The μ = 2 dictionary Q3's table extends |
| 8 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.CLASS` | 7 | The genre notation of `.03` |
| 9 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE` | 19 | The box HE3-BOX-6 scopes |
| 10 | `GENHN_PROOF_2026-08-08.md:ERRATUM 2026-08-08` | 1 | The GENHN corner M-1's conservativity rests on |
| 11 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` | 6 | The sibling splitting HE3-4U imports |
| 12 | `HE6_PROOF_2026-08-08.md:HE6-0″` | 7 | The ξ-form lemma R8-5 re-points to |
| 13 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` | 12 | HE6's frozen battery, the foreign e₁ ≥ 2 contact |
| 14 | `HE7_PROOF_2026-08-08.md:HE3-BOX-6` | 12 | **Reverse edge: HE7 consumes the box** — omitted from HE3's consumer trace |
| 15 | `W12_PROOF_2026-08-08.md:w12_checks` | 8 | The pinned σ-oracle question HE-SIG reuses |
| 16 | `W12_PROOF_2026-08-08.md:W-12.D` | 19 | The supplier stack row |
| 17 | `W11_PROOF_2026-08-08.md:W-11` | 18 | The supplier stack row (not consumed) |
| 18 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | The supplier stack row (not consumed) |
| 19 | `CODEX_HE3PE1_2026-08-08.md:HE3` | 15 | The uncounted composer-context pass |
| 20 | `T2_SIGMA_LADDER_MASTER_2026-08-12.md:HE3-A-PROOF` | **65** | **Reverse edge: T2's `(MP1′)` retirement rests on HE3's stage-α passage** — absent from HE3's trace |
| 21 | `T2_SIGMA_LADDER_MASTER_2026-08-12.md:HE6-SLOT-SEAM` | 56 | A co-certifier of the same retirement |
| 22 | `T2_SIGMA_LADDER_MASTER_2026-08-12.md:HE6-FAMILY` | 61 | Ditto |
| 23 | `T2_SIGMA_LADDER_MASTER_2026-08-12.md:HE6-PROOF` | 66 | Ditto |

**Designations counted but NOT emitted as XREFs (2):**
- **`(MP1′)`** — count **0** in `HE3_PROOF_2026-08-08.md`, count **37** in `T2_SIGMA_LADDER_MASTER_2026-08-12.md`. **HE3 does not name it**; the edge is one-directional and is recorded descriptively at §3.2 and OPEN-CALL 3.
- **§-anchor pointers** (`§S1 (iii)`, `§S6.2`, `L1249–1258`, `L677`, `L350–353`, `L1049`) — line/section pins, verified to land in the right spans (`.34`), not designations.

**Artifacts verified to EXIST on disk:** `he3_checks.py`, `he3_checks_output.txt`, `he3_checks_results.json`, `he3r1_supp.py`, `he3r1_supp_output.txt`, `he3r1_supp_results.json`, `he3_pe1fresh_ab.py`, `he3_pe1fresh_ab_output.txt`, `he3_pe1fresh_c.py`, `he3_pe1fresh_c_output.txt`, `he3_pe2fresh.py`, `he3_pe3fresh.py`, `he3_pe3fresh_output.txt`, `he3_pe3fresh_results.json`, `he3_pe4fresh.py`, `he3_pe4fresh_output.txt`, `he3_pe4fresh_results.json` — **17/17 present.** Reports: `HE3_passPE1_report.md`, `HE3_passPE2_report.md`, `HE3_passPE3_report.md`, `CODEX_HE3PE1_2026-08-08.md` — **4/4.** Logs: `runs/residues/R8_he3_output.log`, `runs/cert/A5_he3_output.log` — **2/2.**

**Note on `he3_pe4fresh.py`:** the artifact **exists** (with output and results JSON) but **no line of HE3 references a PE4** — the note's arc stops at PE3. Recorded as source defect 6: **there is a fourth pass leg on disk that the note does not account for.**

**Commit pins verified with `git cat-file -t`: 2/2** — `6d0ff09` (PE2, cited at `.25`), `7950ee4` (PE1, cited at `.01`).

**Hash pinning quality (rule 23).**

| Class | Count | Where | Verdict |
|---|---|---|---|
| Full md5 | 3 | `he3r1_supp.py` old + new, its output (`.19`) | **PINNED** |
| Hashes deferred to a commit message | 3 | §S8's `he3_checks_output.txt`, `he3_checks_results.json`, runner-as-run (`.11`) | **UNPINNED from the note** |
| Commit hashes | 2 | `.01`, `.25` | PINNED |

### 3.2 Reverse consumer edges

`[TABLE — compiler ledger]`

| Consumer | Verified designation | Shard-2 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HE7 (frozen) | `HE3-BOX-6` (12) | `.06` | HE7 consumes the box — i.e. it consumes HE3's *conditionality*, which R8-2 and R8-3 have since NARROWED | **Not landed either way.** HE3's consumer trace omits HE7's BOX-6 edge (shard 1 source defect 1); no append tells HE7 the box shrank |
| **T2** (accepted) | `HE3-A-PROOF` (65) | shard 1 `.34`'s stage-α passage (L1149–1166) | **T2's `(MP1′)` obligation is RETIRED on the strength of it** (`spec/EFF-T2.md` `EFF.T2.25`: “`HE3-A-PROOF` transports the refined sub-block over the same stage ring”) | **Not landed and NOT RECORDED.** HE3 names neither T2 nor `(MP1′)` (`grep` = 0/0); its consumer trace lists four consumers and T2 is not one (OPEN-CALL 3) |
| GENHN | `[GENHN-HE` (19) | `.06` | HE3 claims the box CLOSED at μ ≤ 3 | **Not landed** (shard 1 OPEN-CALL 2) |
| HE6 (frozen) | via shard 1's trace | — | SAFE per the trace | Not landed |
| W-12 | `w12_checks` (8) | `.10` | HE-SIG **reuses W-12's pinned oracle question** — a consumption in the instrument direction | Not landed; a decorrelation, not a dependency of the proof |

**The last column is not an inference.** HE3's protocol is *report, don't append*, and no dated consumption append is claimed landed on any consumer. **Two outbound edges are unrecorded by the note: HE7's `HE3-BOX-6` consumption and T2's `HE3-A-PROOF` consumption.** The second is the more consequential: **an accepted note has retired a standing obligation on the strength of an HE3 passage, and HE3 does not know.**

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's negative fences and non-claims homed in lines 1276–1853.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Unit |
|---|---|---|
| GENHN-4 / the W-9 weld face | “HE3 does not consume LEMMA GENHN-4, so the W-9 weld face (GENHN-BOX-2) is absent from the σ chain — it survives only inside GENHN's COUNT laws” | `.01` |
| μ ≥ 4 as a graded claim | “μ ≥ 4 is BOXED, not graded.” | `.01` |
| Machine coverage | “NOT exercised by machine: f₁ ≥ 2 stage genres at μ = 3 …, μ ≥ 4 …, d ≥ 2 ambients, and the char-p side of the resultant leg” | `.03` |
| An independent char-p oracle | “PARI's `factorpadic` σ-oracle exists only on the ℤ_p side … the char-p rows are scored against the reader plus the internal resultant identity, **not against an independent oracle**” | `.04` |
| Two promised teeth | “HE-T-PSI (corrupted slope set) and HE-T-CERT (embedded uncertified tail) are OWED.” | `.05` |
| A promised embedded row | “no embedded n = 7 row” | `.05` |
| HE-T-NODE as a tooth | “**HE-T-NODE as coded does not test what its name claims** … it should be read as a diagnostic, not a tooth” | `.05` |
| Branch (ii) | “the only place the argument leaves the ground it stands on … must be read as CONDITIONAL on it” | `.06` |
| The repair route | “IDENTIFIED REPAIR ROUTE (**not executed here**) … That is a genuine further step, not a rewording.” | `.06` |
| Machine grade vs acceptance | “(instrument grade, not acceptance) … nothing here upgrades the conditionality display of COROLLARY HE3.C” | `.18` |
| A general boundary law | “**No single “one more window unit” law, nor one unstratified exact q-power, follows from HE3-5.**” | `.29` |
| HE-BND's generality | “it does not verify a general two-step boundary law” | `.29`, `.17` |
| The split-key count | “**No claim that a single split key still contributes D′ roots is used.**” | `.30` |
| P4's independence | “P4 verifies the T(κ) BOOKKEEPING …, **not the residue arithmetic**; the r1 sentence … overstated the leg's independence” | `.24` |
| The N1 demo's geography | “a geography where the N1 gap is **not LIVE**” | `.22` |
| Weakening any accepted display | “no accepted display of THEOREM HE3.A or COROLLARY HE3.B is weakened” | `.28` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **HE-NORM** (72,134 entry-key identities, exact Bareiss/Sylvester) | `.12`, shard 1 `.20`, `.11`(i) | Executable regression, exhaustive on the enumerated rows |
| **HE-PSI** (43,528 test-key checks; the inequality + (★)) | `.13`, shard 1 `.22`, `.29`, `.31` | Executable regression — **tests the inequality and (★), not the equality dichotomy** |
| **HE-SIG** (947 PARI jobs, 0 bad, all five μ = 3 types) | `.14`, shard 1 `.16`, `.34`, `.36` | Executable regression against an independent oracle (W-12's pinned question) |
| **HE-BND** (3,744 boundary reads; the two-step profile) | `.17`, shard 1 `.15`, `.37`, `.38` | Measurement — **RE-SCOPED by R8-1 to the aligned rows only** |
| **Q4 census tie** (72,134 members, digit-exact vs GENHN's committed E3 rows) | `.15`, `.08` | **Foreign-note decorrelation** — two independently written readers |
| **HE-T-UNDET** (10 spurious solutions where the truth is one vector) | `.16`, shard 1 `.19` | Planted mutant / measurement; **fired — the mechanism certificate** |
| **HE-T-SIG** (6/6 flipped dictionaries caught by PARI) | `.16`, shard 1 `.16` | Planted mutant; fired |
| **HE-T-CAP** (17 / 43 disagreements vs the digit-dropping reader) | `.16`, shard 1 `.37` | Planted mutant; **fired — the strongest tooth; the mutant is the note's own earlier reader** |
| **HE-T-NODE** | `.05`, `.16` | **MIS-SPECIFIED** — `stale self-description` |
| **HE-T-PSI, HE-T-CERT** | `.05`, `.02` | **OWED** — `disclosed non-repair` |
| **`he3r1_supp.py` P1** (8-letter peel profile; PARI on two variants) | `.20`, shard 1 `.21`, `.32`, `.33` | Executable regression, exhaustive over the letter set |
| **`he3r1_supp.py` P2** (f₁ = 2 sweep, 8/8 with PARI) | `.21`, shard 1 `.10`, `.20`, `.25`, `.30` | Executable regression; **e₁ = 1 only — the twist seam is structurally invisible** |
| **`he3r1_supp.py` P2-N1** (both N1 branches) | `.22`, shard 1 `.30` | `signed vacuity disclosure` (wrong geography) → cured by PE2 FR-D |
| **`he3r1_supp.py` P3** (26-letter peel over F₂₇^×; 4/4 with PARI) | `.23`, shard 1 `.21`, `.35` | Executable regression, exhaustive over the letter set |
| **`he3r1_supp.py` P4** (the T(κ) span) | `.24`, shard 1 `.21` | **`signed vacuity disclosure` — quasi-tautological**; cured by PE2 FR-C |
| **`he3_pe2fresh.py`** (7/7 PARI at e₁ = 2 ∧ f₁ = 2; member `ma`; FR-C, FR-D) | `.22`, `.24`, `.25`, shard 1 `.14`, `.24`, `.30` | Executable regression on a decorrelated instrument; **the twist mutant fired** |
| **PE3's fresh route** (GREEN, three disjoint geographies incl. Q = 4 over F₄[[t]]) | `.26`, `.27`, shard 1 `.12`, `.14` | Executable regression on a decorrelated instrument; the coherent read confirmed 3 more times |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.02` (the embedded perimeter) | HE-T-CERT is OWED and there is “no embedded n = 7 row” — **the gating clause is vacuous for this instrument** |
| `.06` (branch (ii)) | HE3-BOX-3: “NOT exercised by machine: … μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch … first bite)” |
| `.30` (LEMMA HE3-4U) | Same — the boxed branch (i) is reachable only at μ ≥ 4 |
| `.31` (LEMMA HE3-4D1) | PROOF-ONLY as a lemma; the `D′ = 1` case has contact at PE2's FR-D |
| `.32` (the piecewise `S_r`) | `ℓ ≥ 2, d ≥ 2` is branch (ii); only `ℓ = 2, d = 1` has contact (P2's λ = 7/2 member) |
| `.33` (the provenance fix) | No instrument can see a citation-scope defect |
| `.04` (char-p σ) | “not against an independent oracle” |

**AUDIT-disposition rows (rule 27):**

| Finding | Unit | Class |
|---|---|---|
| The starved-corner list matches neither reading | `.27` | arithmetic recount (PE3 M-1) |
| HE3-5 is recursive; the “one more window unit” bullet is FALSE | `.29` | decorrelated-model audit + constructed counterexample |
| §S6.2 contradicts §S1 on how many branches are boxed | `.30`, `.06` | decorrelated-model audit — an internal contradiction |
| “n ≥ D′μ ≥ 8” consumes an undisplayed `D′ ≥ 2` | `.31`, `.06` | decorrelated-model audit |
| `S_r`'s display is still ill-defined at ℓ ≥ 2 | `.32` | decorrelated-model audit (an r1-repair propagation miss) |
| HE3-0's proof sentence still cites GENHN-2 | `.33` | decorrelated-model audit (an r1-repair propagation miss) |
| P4 is quasi-tautological as a residue check | `.24` | **self-found at `[r2]`** — in-house instrument audit |
| The N1 demo ran where the gap is not live | `.22` | **self-found at `[r2]`** |
| HE-T-NODE does not test what its name claims | `.05` | **self-found** — in-house instrument audit |
| Two promised teeth were never wired; a promised row never ran | `.05` | **self-found** sealed-vs-delivered audit |

**Both-direction audit.** Every row guards at least one in-range or shard-1 unit; every toothed unit appears in a row. Units with **`TEETH: NONE`** — `.01`, `.07`, `.18`, `.28`, `.33` — are grade declarations, preregistrations, summaries, framing paragraphs or provenance fixes. **Zero battery-row orphans; zero toothed-unit orphans; seven signed PROOF-ONLY units; ten AUDIT-class findings, four of them SELF-FOUND.**

---

## 6. BOUNDARY SELF-AUDIT

This range is boxes, a battery, a verdict and two append blocks. The boundary problem is “when is a record a unit?” — the same question GENHN's shard 2 faced — with one addition: **four of this shard's findings are SELF-FOUND instrument audits** (`.05`, `.22`, `.24`, and HE-T-NODE), which sit awkwardly between `instrument-record` and `changes-record`.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

For records: (1) does the span make a falsifiable claim (a count, a status, a scope)? (2) is it cited BY DESIGNATION? (3) does it have its own supersession history? (4) does it have its own conditionality or consumer set?

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. Each of the six §S7 boxes is its own unit (`.01`–`.07`).** Test 2 and 3: `HE3-BOX-6` is cited 12 times in-note and 12 times in HE7; `HE3-BOX-4b` is cited from Q5; `HE3-BOX-2`/`-3`/`-4` are the coverage-hole sentences nine PROOF-ONLY rows quote. *Not arguable.*

**2. `.06` (HE3-BOX-6) kept WHOLE**, including the mechanism, the scope, the two consequences and the repair route. *Candidate A:* split the repair route out — it is a research proposal, not a claim about the note. *Candidate B (chosen):* one unit. **Reason:** the box's claim is a single negative one (“this is the one surviving gap”), and the route is *why* the gap is a gap rather than an oversight. Splitting would leave the box without its own account of what closing it needs. *Cost:* a 35-line unit.

**3. §S8 split into instrument / rows / legs (`.08`–`.10`).** Test 4: three different predicates (design, coverage, checks), and `.08`'s “no twist bookkeeping” design property is cited from shard 1 `.24`. *Weakly arguable* — the source gives them one section. *Chosen split* because `.08`'s immunity property is load-bearing elsewhere.

**4. §S9 split into headline + five Q-blocks + the summary (`.11`–`.18`).** Test 1 and 3: each Q-block scores a different leg with a different disposition, and **two of them are separately re-scoped** (`.17` by R8-1; `.18`'s item 4 likewise). *Candidate A:* one §S9 verdict unit. *Rejected* — one CONDITIONALITY field cannot carry both the census tie's decorrelation status and HE-BND's withdrawal of generality.

**5. §S9′ split into verdict + P1–P4 + the coverage note (`.19`–`.25`).** Test 3, decisively: **P2-N1 and P4 each carry their own `[r2]` disclosure** with its own scope-pin and its own decorrelated substitute. Merging would hide two of the note's four self-found instrument defects.

**6. Each dated correction is a unit (`.26`–`.33`), with the two headers split out (`.26`, `.28`).** *Arguable for the headers.* *Chosen* because each states a **rule**: `.26` states the CLEAN bar and begins the freeze; `.28` states the 5/5-REAL verdict and the no-display-weakened guarantee. **Honest cost: if the cross-read judges framing paragraphs to be noise, `.28` is the unit to cut — but its 5/5 accounting and its “no accepted display is weakened” clause would have to move into `.29`–`.33`.**

**7. `.34` (the A5 verification parenthetical) as an `instrument-record` unit.** Test 1: it makes five falsifiable claims about what was hand-checked, **all five of which this shard independently recomputed** ✓. *Candidate A:* an italic tail; fold into `.28`. *Rejected* — it is the only evidence the transcription was verified, and its line pins are independently checkable (three checked, three landed).

**8. The four SELF-FOUND instrument audits are typed `instrument-record` or folded into the record they audit, not `changes-record`.** `.05` (sealed-vs-delivered) is an `instrument-record`; `.22`'s and `.24`'s `[r2]` disclosures are folded into their `run-record` units. *Candidate A:* type them `changes-record` — they do change what the note claims. *Candidate B (chosen):* keep them with the instrument, because **what changed is the description of an instrument, not a mathematical statement**, and rule 19 separates those. **Format note: v3 has no `instrument-audit` type, and these four are neither `run-record` nor `instrument-record` cleanly** — see §6.3.

**9. `.29` (R8-1) kept WHOLE**, including the criterion, its proof, the three replacement bullets, the counterexample, and the HE-BND re-scoping. *Candidate A:* split the counterexample as a `run-record`. *Rejected* — it is a symbolic construction, not a run; no instrument produced it.

**10. `.30` and `.31` (the two proving corrections) as `[lemma]` units, not `[changes-record]`.** Test 1: each carries a full proof with its own obligations, and each is cited by designation (`HE3-4U` count 2, `HE3-4D1` count 2). **Their supersession effect is recorded in CONDITIONALITY as `license` + `inventory completion`.**

### 6.2 Merges deliberately NOT made, and two conflations blocked

- **The Q3 and Q4 tables stay in their own units** (`.14`, `.15`): one scores the dictionary, the other ties the census; only the second is a decorrelation.
- **The five A5 corrections stay in five units**: two are licenses that shrink a box, three are display/provenance fixes — different truth conditions.
- **BLOCKED CONFLATION 1 — “GREEN” vs “graded”.** `.11` reports GREEN; `.18` says “instrument grade, not acceptance”; `.26` puts the counter at **1/2**; `.28` adds five REAL findings after the clean pass. **All four are true simultaneously.**
- **BLOCKED CONFLATION 2 — “all wired teeth fired” vs “four teeth” vs “three genuine teeth”.** `.11` says the first, `.05` establishes the second and third. A chapter cut quoting `.11` alone would overstate the instrument by one tooth.

### 6.3 Format notes (v3 rules exercised, and one gap)

Rules 11, 12, 14 (double-emission at `.03`, `.09`, `.14`, `.15`, `.17`, `.32`), 15 (no NEAR-MISS needed in this range), 16 (PROOF-ONLY ×7), 17 (predicate C, two streams), 18 (six kinds used: replacement, license, scope-pin, provenance-rider, as-of scoping, counter re-reading, inventory completion), 19 (`instrument-record` ×5, `run-record` ×9, `preregistration` ×1 at `.07` — **and this shard SCORES the preregistration**, which is what the rule's pairing asks for), 20 (all four disclosure labels), 21 (three freeze predicates, one of them — the consumer pin — unique to this note), 22 (**arithmetic audits on eighteen displays; all reproduced**), 23 (2 commits, 23 artifacts, 3 full md5s, 3 hashes marked UNPINNED-from-the-note), 25 (CHAIN ×6), 26 (STALE-SELF-DESCRIPTION ×3: `.01`, `.17`, `.18`), 27 (AUDIT ×10, **four SELF-FOUND**), 28 (SERIES HE3-GRADE-ARC completed here at member 4).

**One gap found in v3:** **there is no type for a SELF-FOUND INSTRUMENT AUDIT.** Four of this shard's findings — the sealed-vs-delivered shortfall (`.05`), HE-T-NODE's mis-specification (`.05`), P4's quasi-tautology (`.24`), and the N1 demo's dead geography (`.22`) — are the note auditing its *own* instrument and disclosing the result. They are not `run-record` (no run), not `instrument-record` (they contradict the instrument's own description), and not `changes-record` (no mathematical statement moves). Rule 20's `stale self-description` and `signed vacuity disclosure` name the *dispositions* but not the *unit type*. **Proposed fix: add `instrument-audit` to the TYPE ENUM, and treat rule 27's `in-house hostile pass` as covering self-audit of instruments as well as of prose.**

---

## 7. SHARD NOTES

- **Riders landing WITHIN this range (three).** (1) R8-1 → `.17` (the HE-BND table's generality withdrawn) and `.29`'s own bullets. (2) R8-2 → `.06` (the box narrowed to branch (ii)). (3) R8-3 → `.06` (the `n ≥ 8` derivation supplied).
- **Riders landing on SHARD 1 from this range (six)** — M-1 → shard 1 `.12`; R8-1 → `.37`, `.38`, `.15`; R8-2 → `.33`, `.17`, `.01`, `.35`; R8-3 → `.01`, `.17`; R8-4 → `.32`; R8-5 → `.25`. Enumerated in `spec/EFF-HE3-s1of2.md` §7; the merge must install them from that list.
- **Range-edge audit.** Line 1275 (shard 1's last) is blank; line 1276 opens `## S7. BOXES, GRADE, AND COVERAGE`; the range ends at line 1853, the note's last line (the closing `)*` of the A5 verification parenthetical). **No source unit is cut at either edge**, and the manifest boundary falls on a section break.
- **Outside-HOME material used only as resolver:** §S0–§S6.5. Shard 1 owns them.
- **Protocol versus supply.** §S7–§S9′ and the appends' supply set is inventoried; **no consumption append is claimed landed on any consumer**, and none is invented. **Two unrecorded outbound edges are flagged** (HE7's BOX-6, T2's HE3-A-PROOF).
- **Numbering.** Temporary IDs `EFF.HE3.s2of2.01`–`.34`. **Merge hazards to flag:**
  (a) **HE3-BOX-6 is STRICTLY NARROWER at HEAD than as displayed** (branch (ii) alone, at `μ ≥ 4` and `D′ ≥ 2`); a chapter cut reading `.06`'s frozen text alone would over-report the conditionality.
  (b) **All five A5 repairs are “awaiting sol discharge-confirmation”**; the merge must not present them as either landed-and-confirmed or open.
  (c) **The grade is 1/2, not accepted** — SERIES HE3-GRADE-ARC terminates at `.26`.
  (d) **Three teeth are genuine, four are wired, five were promised** (`.05`); `.11`'s “all wired teeth fired” must travel with that accounting.
  (e) **`.17`'s HE-BND table is a valid measurement whose general law is withdrawn** — keep both halves.
  (f) **T2 consumes HE3's stage-α passage to retire `(MP1′)`, and HE3 does not record it** (OPEN-CALL 3).
  (g) **`he3_pe4fresh.py` exists on disk with output and results, and the note has no PE4** (source defect 6).

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — HE3-BOX-6's displayed scope and its HEAD scope differ, and consumers pin the display

`.06`'s frozen text says branch (ii) is “the only place the argument leaves the ground it stands on”, while §S6.2 (shard 1 `.33`) said BOTH branches were boxed — an internal contradiction the A5 wave named. **R8-2 makes the box's own title claim true; R8-3 supplies its missing `D′ ≥ 2`.** Meanwhile **HE7 consumes `HE3-BOX-6`** (count 12) and was frozen at `HE3 @ 7a95449`, i.e. **before both narrowings**. **Decision needed: whether the merged spec carries the box at its displayed scope (what HE7 pinned) or its HEAD scope (what R8-2/R8-3 leave), and whether HE7 is owed a note.** This shard carries the HEAD scope with the CHAIN recorded.

### OPEN-CALL 2 — all five A5 repairs are landed-but-unconfirmed

“Ledger: HE3's row → 5 repairs folded, **awaiting sol discharge-confirmation**” (1851–1853). Two of the five (R8-2, R8-3) are **load-bearing for the headline's `n ≤ 7` range**; one (R8-1) **refutes a bullet the battery's HE-BND leg was scored against**. **Decision needed: whether a chapter cut may consume landed-but-unconfirmed repairs as current** — the same question `spec/EFF-GENHN-s2of2.md` OPEN-CALL 4 raises, and the two should be answered together.

### OPEN-CALL 3 — T2 retired a standing obligation on the strength of an HE3 passage, and HE3 does not record it

`spec/EFF-T2.md` `EFF.T2.25` records that T2's `(MP1′)` obligation is **RETIRED**, resting on four certifiers of which the first is **`HE3-A-PROOF`** (count **65** in `T2_SIGMA_LADDER_MASTER_2026-08-12.md`): “`HE3-A-PROOF` transports the refined sub-block over the same stage ring.” **That is HE3's stage-α passage at lines 1149–1166 verbatim** (shard 1 `.34`). **HE3 names neither T2 nor `(MP1′)`** — both greps return 0 — and its CONSUMER TRACE (shard 1 `.06`) lists four consumers, none of them T2. **So an accepted note has retired an obligation on the strength of a passage whose own note is at grade 1/2 and whose surrounding lemma set was corrected five times on 2026-08-12.** **Decision needed: whether T2's retirement must be re-checked against HE3 at HEAD (R8-1..R8-5 do not touch the stage-α passage — verified — so the answer is probably no, but the edge must be recorded either way), and whether HE3's consumer trace is owed a fifth row.** Nothing was invented; the edge is recorded at §3.2.

### OPEN-CALL 4 — HE3's most load-bearing citation depends on an HE6-side correction from the same campaign

`.34` discloses: “HE6-0″ (**as corrected at this campaign's A3 fold**) supplies exactly the consumed form.” HE6-0″ is HE3's ξ-form slot lemma — **the single most load-bearing import** (shard 1 `.03`), riding every slot read at `ρ` and `θ″`. **This compiler did not verify the A3 fold's content.** **Decision needed: whether the merge run checks HE6-0″ at HEAD against what HE3 consumes.**

### OPEN-CALL 5 — the note's arc has three passes and the disk has four fresh legs

`verification/openmath/he3_pe4fresh.py`, `he3_pe4fresh_output.txt` and `he3_pe4fresh_results.json` all exist, and **no line of HE3 references a PE4**. The grade arc terminates at PE3/1-of-2. **Decision needed: whether a fourth pass ran and is unrecorded, or whether the artifact belongs to another unit's arc.** Recorded as source defect 6; not resolved.

### OPEN-CALL 6 — the instrument's tooth count has three defensible answers

Promised **5**, wired **4**, genuine **3** (`.05`), and `.11` reports “all wired teeth fired”. **Decision needed: which number the merged spec reports.** This shard reports all three with the accounting.

### Recorded source defects (flagged, not silently repaired)

1. **`.02`:** HE3-BOX-2 says “The battery gates its σ legs at that perimeter **on embedded rows**”, but **the battery has no embedded rows** (`.05`, `.09`). The gating clause is vacuous for this instrument.
2. **`.03`:** HE3-BOX-3's “The PROOFS are uniform in all of these” is false at `μ ≥ 4`, where branch (ii) is boxed — in tension with the same box's own “NOT exercised … μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch … first bite)”.
3. **`.04`:** HE3-BOX-4's “characteristic-free as PROVED” is not repeated with shard 1 `.27`'s PE1-F4 qualification (the freedom is at the residue level; binomial coefficients do appear).
4. **`.11`:** §S9's artifact hashes are deferred to a commit message — **UNPINNED from the note**, unlike `he3r1_supp.py`'s three full md5s.
5. **`.18`:** “no hostile arc has run” is stale by three passes; the surrounding `[r1]`/`[r2]` text was updated and this sentence was not.
6. **§3.1:** `he3_pe4fresh.py` (+ output + results) exists on disk and **the note has no PE4** — see OPEN-CALL 5.
7. **`.14`/`.17`:** the Q3 member totals (96 / 291) and the N = 6 decided counts (96 / 291) are **identical**, and the note states neither the totals nor the coincidence. Recorded because it is a strong internal consistency result that a chapter cut would otherwise lose.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation; **no `[ASSEMBLED]` statements in this shard.** **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** Strike-through is reproduced exactly at `.01`, the one place it occurs in this range.
- Truncations inside quotations: **none used.** Every quoted span is complete from its opening to its closing sentence.
- Terminal punctuation, ASCII table alignment and blockquote nesting are preserved; `.30`'s doubly-nested blockquote (`> >`) reproduces the source's own lemma-inside-append structure.
- **Six source displays are emitted TWICE** (rule 14): `.03`'s coverage ledger, `.09`'s row list, `.14`'s σ dictionary, `.15`'s census table, `.17`'s window profile, `.32`'s piecewise definition — verbatim first, `[TABLE]` transcription second.
- **Eighteen arithmetic audits were computed fresh** (rule 22) at `.03`, `.05`, `.06`, `.09`, `.11`, `.14`, `.15`, `.16`, `.17`, `.19`, `.20`, `.21`, `.22`, `.23`, `.24`, `.25`, `.26`, `.27`, `.29`, `.30`, `.31`, `.32`, `.33`, `.34`. **Every one reproduced the source exactly.** Six produced findings the source does not state: **the Q3 ↔ HE-BND identity at N = 6 (96 / 291, cell for cell)**; the `p²` structure of the out-of-genre counts (25 = 5², 49 = 7²); the `39,366 + 32,768 = 72,134` reconciliation of Q4 with the enumerated-member total; the row-2 breakdown summing exactly to 32,768; the `72,602 − 72,134 = 468 = 125 + 343` reconciliation of reader classifications with Group B; and the `he3_pe4fresh` artifact with no PE4 in the note.
- **23 external XREF designations, every one grep-verified with a fixed-string count ≥ 1 recorded inline and in §3.1.** One designation (`(MP1′)`) is verified ABSENT from HE3 and present in T2 (count 37), and is recorded as a one-directional edge rather than emitted.
- **2 commit pins verified with `git cat-file -t` (2/2 → commit); 23 artifact/report/log filenames verified present (23/23); 3 full md5s recorded; 3 hashes marked UNPINNED-from-the-note.**
- Status and mathematical content are kept as distinct predicates, and this shard blocks two conflations explicitly (§6.2): GREEN-vs-graded, and the three tooth counts.
- Out-of-range material is used only to resolve in-range HOME units; shard 1 owns §S0–§S6.5.
- **Honest limitation of this shard:** five of the six inbound corrections are “awaiting sol discharge-confirmation” (OPEN-CALL 2), two of them load-bearing for the note's headline range; one outbound edge (T2's) is entirely unrecorded by the note (OPEN-CALL 3); and the note's most load-bearing import rides an HE6-side correction this compiler did not verify (OPEN-CALL 4). Every affected unit quotes the governing text verbatim, so the shard is self-contained as a *reading*, but the merge run must answer OPEN-CALLs 1–4 before a chapter cut consumes HE3-BOX-6's scope.

EFF-HE3-s2of2 COMPILED: 34 statements / 23 xrefs verified / 6 open calls
