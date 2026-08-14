# EFF-GRTJB-s2of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` (3327 lines, 240,219 bytes).

**HOME range:** source lines **1303–2457** inclusive — **§1** (setting, indexing, the two frames, the shear), **§2 THEOREM JB-DEV** (the expansion identity; W-3 first half), **§3 LEMMA JB-AFF + THEOREM JB-VTX** (the polygon identity through the displayed shear; W-3 second half), **§4 THEOREM JB-TREE + JB-ID** (the division-step correspondence; W-5), **§5 THEOREM JB-CREAD + LEMMA JB-EPS** (the (C-READ) transport and the ε-carry collapse; W-5), and **§6** the six honest boxes JB-BOX-1..6. This is the shard that carries **the mathematics**. Lines 1–1302 (shard 1) and 2458–3327 (shard 3) are used ONLY to resolve material homed here.

**HEAD blob hash:** `69e859326ca58c3f96933714f7299835867f6531` (clean in the working tree; last touched by commit `68a993fa`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (rules 1–28); temporary IDs `EFF.GRTJB.s2of3.<nn>`. Companion shards: `spec/EFF-GRTJB-s1of3.md` (COMPILED: 80 statements / 56 xrefs / 5 open calls), `spec/EFF-GRTJB-s3of3.md`.

**SHARD-COUNT RECONCILIATION.** `runs/qgen/sweep_manifest.txt` line 45 gives this exact range as `s3of4`; the Q7 charge names three shards. The reconciliation is recorded in full at `spec/EFF-GRTJB-s1of3.md` §1 (manifest rows 43+44 merged into shard 1; rows 45 and 46 unchanged as shards 2 and 3). **This shard's range is the manifest's own, unmodified.** Boundaries re-verified at HEAD: L1301 `---`, L1302 blank, L1303 `## §1.`; L2456 `---`, L2457 blank, L2458 `## §7.`.

**GENRE: TAG-SPARSE PROSE PROOF (density 0.00).** `grep -cF '\tag{'` = **0**. In THIS range the note does supply strong boundary signals the front matter lacked: bold `**THEOREM X.**` / `**LEMMA X.**` openers, bold clause labels `**(i)**`…`**(iv)**` / `**(a)**`…`**(e)**`, `*Proof.*` markers, four regenerated `∎ GRADE` blocks (surfaces 2–5 of 14), and six `* **JB-BOX-n …**` bullets. **Boundaries are therefore MUCH less arguable here than in shard 1** — the §6 boundary self-audit records the four places where they still are.

### FREEZE PREDICATES (rule 21)

All three freezes declared in shard 1 govern this range identically and are not re-derived here: **(1) INSTRUMENT FREEZE** — four byte-frozen scripts, all four md5 pins re-computed EXACT at HEAD by this compiler (`grt_jb_checks.py` `55f4911e…`, `grt_jb_printwalk.py` `f53e23e8…`, `grt_jb_printwalk2.py` `6c6318f7…`, `grt_jb_r1_levelcensus.py` `2bcb44fd…`). **(2) SURFACE-GENERATION FREEZE** — “**After r3 no grade surface in this note may carry a conditionality claim that is not a cell of this table, and none may omit one**” (L182–183), with JB-BOX-6's standing rule homed HERE at `.61`: “if a surface and the table ever disagree, **THE TABLE GOVERNS**”. **Four of the fourteen regenerated surfaces are homed in this shard** (surfaces 2, 3, 4, 5 = the four `∎ GRADE` blocks), plus **surface 14** (JB-BOX-2's perimeter enumeration). **(3) TEXT FREEZE** — the 2026-08-12 certifier annex head: “Everything above this heading is byte-untouched by this append.”

### Governing effective-text record

Identical to shard 1's, and re-stated here in the one form this range needs:

**EFFECTIVE TEXT FOR THIS SHARD = lines 1303–2457 exactly as written (all `[r1]`–`[r8]` brackets already landed in place, strike markup preserved), READ AS CORRECTED by the out-of-range dated appends wherever they name an in-range sentence, and READ AS GOVERNED by §0M's matrix (shard 1 `.20`) wherever a grade surface is in question.**

**Four out-of-range appends land inside this range, and this is the shard they hit hardest:**

| append | lines (shard 3) | in-range targets homed here |
|---|---|---|
| **FOLD ANNEX E-1** (from GRTJA PE2 F1; JA r2 `5d95805`) | 3125–3133 | every “(R-coll)” — `.13`, `.47`, `.56` |
| **FOLD ANNEX E-2** (from GRTW2 r1 `8d5e3fa`) | 3135–3142 | every W2-C3 grade citation — `.31`, `.37`, `.59` |
| **CERTIFIER ANNEX E-3** (sol E4/E3, 2026-08-12) | 3199–3245 | **§3(c) — `.23`**, and “slope/length” at `.27` |
| **CERTIFIER ANNEX E-4** (same) | 3267–3312 | **every “FALSE, not merely unproved”** — `.11`, `.16`, `.17`, `.20`, `.26`, `.27` |

**E-3 and E-4 are the only corrections in the whole GRTJB stack that touch a DISPLAYED MATHEMATICAL STATEMENT of §§1–6.** Both are applied at their units with the annex text quoted; no in-range sentence is edited.

### Scope split (rule 7 + rule 17 — three predicates)

**A. ABSORPTION / supply SET.** This shard IS the supply. Five theorems and one lemma: **JB-DEV** (§2), **JB-AFF** + **JB-VTX** (§3), **JB-TREE** + **JB-ID** (§4), **JB-CREAD** + **JB-EPS** (§5). The note's own one-line inventory of what they deliver is §7.3's consequence display (shard 3): “**W-3 = both halves of the identity (expansion + polygon, shear explicit) — full in CONTENT, not full in q**” and “**W-5 on [RMG]'s scope (T-scope(m), g_m = 1), with two further fences**”.

**B. APPEND / consumption PROTOCOL scope. NO-APPENDS DECLARATION, homed in this shard** at JB-BOX-6 (`.61`, L2439–2442):

> “No gr/carrier claim (J-C untouched;
>   BLOCKED-ON-CARRIER-TIE stands); no count/menu/density claim (J-D
>   untouched); the P0 application gate stands; acceptance counter 0/2 —
>   nothing here may be consumed at proof grade before its hostile arc.”

**Zero dated consumption appends are claimed landed on [RMG], [ILN]†, W-2, J-A or LED-Λ, and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED.** Two (E-1, E-2), both listed in the table above, plus the 2026-08-08 supplier-grade annex re-grading W-2 and J-A from ATTEMPT to **ACCEPTED at 2/2** — which touches `.31`, `.37` and `.56`'s grade riders. Direction FAVORABLE; **LED-Λ's ATTEMPT grade is NOT superseded and still rides at `.34`, `.37`, `.59`.**

### Resolution rules applied

1. Lines 1303–2457 supply the HOME material listed under HOME range.
2. `[r1]`…`[r8]` brackets inside the range are ALREADY-LANDED text applied in place; the later bracket governs the earlier text it names. Multi-layer stacks carry `CHAIN:` with TERMINAL marked (rule 25) — this shard has three (`.14`, `.34`, `.42`).
3. **`~~…~~` is supersession, never deletion.** Struck text is quoted whenever the superseding bracket cannot be read without it. **In this range the struck text is frequently a FALSE MATHEMATICAL STATEMENT the note keeps on the record** (e.g. `.33`'s “every node is a sum of reduced cells”, `.34`'s internal-edge transfer, `.25`'s window clause as literally read) — dropping the strike would erase the note's own refutations.
4. **§0M's matrix (shard 1 `.20`) GOVERNS the four `∎ GRADE` surfaces homed here** and JB-BOX-2's enumeration. Each surface unit records its generating rows.
5. Out-of-range appends (E-1, E-2, E-3, E-4, the supplier-grade annex) are applied as CONDITIONALITY at the in-range units they name, with the annex text quoted; no in-range sentence is edited.
6. Out-of-range statements are NOT emitted as units here. Shard 1 owns the front matter, §0M and the eight repair-round blocks; shard 3 owns §7, the acceptance record and all four annexes.
7. External repo records are reading notes only.
8. **CITE-SCOPE rows are compiled AS THE NOTE STATES THEM.** The `HigherNewton.tex` anchors are consumed at four sites in this range (`.06`, `.21`, `.23`, `.24`); `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-11**'s retarget is recorded once, as a READING NOTE at `.21`, and referenced from the others. **Recorded, not applied.**

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or `[ASSEMBLED]`; truncation marked `…`. **The four `∎ GRADE` blocks and §1's perimeter definitions are fixed-width ASCII inside the source; each is DOUBLE-EMITTED (rule 14)** — verbatim as the source display, then as a `[TABLE]` transcription. The `(VAL)/(GRID)/(RES)` display, the `(RM-m)` box recital, the `𝒲_m` definition, the four-line `u ≥ 0` theorem and the five-line JB-CREAD chain are reproduced with line structure intact. Compiler ledgers are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GRTJB.s2of3.01  [definition]

**CANONICAL STATEMENT:** verbatim, lines 1305–1309 (through “sealed in the probe.”).
**FORM:** inline sentence (a dictionary import).

> “Harness and P-index dictionary VERBATIM from J-A §1 (itself from W-2
> §1.1–1.2): [ILN]† S0.1 class pin; GMN level i = harness read i−1; GMN keys
> φ_i = harness Φ_{i−1}; v_i = w_{i−1} (THEOREM JA-VAL, consumed); GMN
> order-q residual R_q pairs with the harness level-q read R_q v; pins
> (P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the probe.”

**CONDITIONALITY:** A verbatim import at J-A's grade. **The index shift `GMN level i = harness read i−1` is the single most load-bearing convention in the note** — every level-slip defect in the arc (r3/F-4, r6/F-1) is a failure to instantiate a supplier's level-indexed quantifier through this dictionary. **Supplier grade updated (shard 3, L3148–3161): GRTJA is now ACCEPTED at 2/2 at `17d2a32`** (body byte-frozen, md5 `cba309ce` @ `f131c53`).

**DERIVATION:** Import, not derivation.

**RESOLUTION TRACE:** statement lines 1305–1309; consumed at `.11`, `.21`, `.24`, `.34`; supplier-grade correction 3148–3161 (shard 3).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VAL` — grep-verified count **7**.
XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — count **13**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1` — count **22** (the §1.1–1.2 source section is pinned by designation, not by §-anchor).

**TEETH:** The pins are sealed in `grt_weld_probe.py` (EXISTS at HEAD); the dictionary's own content is exercised by every IND family.

---

### EFF.GRTJB.s2of3.02  [definition]  ★ the two perimeters, defined once

**CANONICAL STATEMENT:** verbatim, lines 1309–1334 — the struck conflated line, the `[r2, G2-6]` header, and the two-condition ASCII display.
**FORM:** bracketed rider + fixed-width display.

> “~~**Shared-key
> perimeter at level q**: Φ_j^har = φ_{j+1}^cls byte-for-byte for all j ≤ q.~~
> **[r2, G2-6 — TWO DISTINCT CONDITIONS, defined once, named apart. The struck
> line conflated them and was cited (at §2(iii) and at the JB-VTX theorem) for
> the other one; the two differ by exactly the level q itself, which is the
> level the `+1` in `qcap` exists for. Both names below are used verbatim from
> here on.**
>
>     BYTE-EQUAL CHAIN THROUGH q :  Φ_j^har = φ_{j+1}^cls byte-for-byte for
>         every j ≤ q — the condition of the W-2 §3.4(3) byte law, consumed by
>         JB-DEV(ii) (it is what makes Φ_q^har the classifier's OWN key at
>         level q). This is the struck line's content, retained under its own
>         name.
>
>     SHARED-KEY PERIMETER (the runner's own `qcap_of`) :  keys shared STRICTLY
>         BELOW q, i.e. Φ_j^har = φ_{j+1}^cls byte-for-byte for every
>         1 ≤ j ≤ q−1 — NOTHING is required at j = q. Equivalently, with
>         shared_upto := max{L ≥ 0 : Φ_j^har = φ_{j+1}^cls for all 1 ≤ j ≤ L}
>         and qcap := min(n, shared_upto + 1), the perimeter is the LEVEL RANGE
>
>             0 ≤ q ≤ qcap ,      qcap = min(n, shared_upto + 1),
>
>         which is exactly `qcap_of(T, G) = min(T.n, GJA.shared_upto(T,G) + 1)`
>         with the runner's loops `for q in range(0, qcap_of(T,G) + 1)`. The top
>         level q = qcap = shared_upto + 1 IS in scope, and at it the keys need
>         NOT agree at j = q — the perimeter is a condition below q, never at q.”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| name | short | condition | equivalent form | consumers |
|---|---|---|---|---|
| **BYTE-EQUAL CHAIN THROUGH q** | `P≤q` | `Φ_j^har = φ_{j+1}^cls` for every `j ≤ q` | J-A's perimeter instantiated at level `m = q+1` | JB-DEV(ii)'s byte clause (W-2 §3.4(3)); **+ JB-DEV(iii)(RES) [r3, F-4]**; **+ JB-VTX(d3) [r6, F-1]** |
| **SHARED-KEY PERIMETER** | `P<q` | `Φ_j^har = φ_{j+1}^cls` for every `1 ≤ j ≤ q−1`; **nothing at `j = q`** | the level range `0 ≤ q ≤ qcap`, `qcap := min(n, shared_upto+1)` = the runner's `qcap_of(T,G)` | JB-DEV(iii)(VAL)/(GRID); JB-VTX(a)(b)(c)(d1)(d2)(d4)(e); JB-TREE(iii)/(iv) at level m |

**SUPERSESSION KIND:** `replacement` — one conflated definition split into two named ones.

**CONDITIONALITY:** **Unconditional as definitions, and they are the note's most-cited objects.** `P≤q` is STRICTLY STRONGER than `P<q`; the two differ at `j = q`, and as fences over the level range **the exclusion bites only where `shared_upto < n`** — 5 of the 16 roster towers (T3A/T3C/T3D/T3E/I4C), the r4/F-3 geography, master statement at §0M column (a2) (shard 1 `.13`).

**DERIVATION:** Definition; the level-range equivalence is read off `qcap := min(n, shared_upto+1)` against the runner's loop bound. **This compiler verified the runner's loop form is as quoted:** the shard-1 gate check at `grt_jb_checks.py` L283 sits under `q <= L` inside exactly this loop.

**RESOLUTION TRACE:** statement lines 1309–1334; matrix columns (a1)/(a2) at shard 1 `.12`/`.13`; correction sites 1336–1364 (`.03`) and 1365–1372 (`.04`).

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:3.4` — count **35** (§-anchor; upper bound. The byte law's designation is independently pinned by `(C-coll)`, count **27**, and `TH-BASE`, count **8**).

**TEETH:** `jb_keyeq`'s byte census keys `P≤q` at q = 1 (25 rows, 3 VACUOUS); the runner's loop bound keys `P<q`; the off-perimeter counter is **0** on the roster.

---

### EFF.GRTJB.s2of3.03  [supplier-finding]

**CANONICAL STATEMENT:** verbatim, lines 1336–1364 — the struck exhaustiveness sentence and the `[r3, F-4]` correction, with the `[r4, F-3]` arithmetic fix nested inside.
**FORM:** bracketed rider on a struck sentence.

> “~~**Every r1/r2 restatement (§2(iii), the JB-VTX theorem and grade line,
> JB-BOX-2, §7.2, §7.3) now cites the SHARED-KEY PERIMETER in this second sense,
> `j < q`, 0 ≤ q ≤ qcap, and no statement cites §1 for the through-q condition
> except JB-DEV(ii)'s byte clause, which means the first.**~~
> **[r3, F-4 — THE STRUCK SENTENCE IS FALSE IN ITS SECOND HALF, and the error is
> a level slip, not a wording slip. J-A's perimeter is LEVEL-INDEXED ("Shared-key
> perimeter at level m: Φ_q^har = φ_{q+1}^cls byte-for-byte for all q ≤ m−1"), so
> instantiating it at each layer's OWN level gives TWO different conditions
> inside §2(iii): (VAL) is JA-VAL at level q and needs j ≤ q−1 = the SHARED-KEY
> PERIMETER `P<q`; (RES) is JA-RES at read level m = q+1 and needs j ≤ m−1 = q,
> i.e. the BYTE-EQUAL CHAIN THROUGH q. So there are exactly TWO consumers of the
> through-q condition, not one: JB-DEV(ii)'s byte clause AND JB-DEV(iii)'s (RES)
> layer. CORRECTED STATEMENT, which §0M's matrix column (a2) now carries as the
> single record: every restatement of the (VAL)/(GRID) layers and of all of
> JB-VTX and JB-TREE(iii)/(iv) cites the SHARED-KEY PERIMETER `P<q`
> (0 ≤ q ≤ qcap); the (RES) layer and JB-DEV(ii)'s byte clause cite the
> BYTE-EQUAL CHAIN THROUGH q. ~~The two differ exactly at the top level
> q = qcap = shared_upto+1 … r2's single fence over-supplied (RES) by exactly one level.~~ **[r4, F-3 — the
> struck arithmetic held on only 5 of the 16 roster towers. qcap :=
> min(n, shared_upto+1), so q = qcap is a level where `P≤q` fails ONLY WHEN
> shared_upto < n (T3A, T3C, T3D, T3E, I4C); when qcap = n ≤ shared_upto the two
> fences COINCIDE on the whole range 0 ≤ q ≤ qcap and r2's fence over-supplied
> (RES) at NO level (the other 11 towers). The corrected record is §0M column
> (a2); probe-verified against the runner's own `qcap_of`/`shared_upto`,
> 2026-08-06.]** No machine leg can
> catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES)
> NOWHERE (§0M row 5, cell note ⟨n4⟩).]**”

**CHAIN (rule 25):** r2's exhaustiveness claim → **[r3, F-4]** correction (TWO consumers, not one) → **[r4, F-3]** arithmetic fix (the exclusion bites on 5/16) → **[r6, F-1]** (`.04`, a THIRD consumer). **TERMINAL = the r6 reading**, recorded at `.04`.

**SUPERSESSION KIND:** `counter re-reading` (r3, a false exhaustiveness claim) + `counter re-reading` (r4, a false arithmetic gloss).

**CONDITIONALITY:** **A strict narrowing that moves a mathematical fence.** The re-fence direction is toward MORE conditionality wherever it bites at all. **The representative-pin rescue is REFUSED** (shard 1 `.56`) and the refusal binds r6.

**DERIVATION:** Level-index arithmetic on J-A's own quoted quantifier, displayed inside the bracket: at read level `m`, J-A requires agreement for `j ≤ m−1`; (VAL) is JA-VAL at level `q` ⇒ `j ≤ q−1`; (RES) is JA-RES at read level `m = q+1` ⇒ `j ≤ q`. The r4 arithmetic: if `shared_upto < n` then `qcap = shared_upto+1` and `P≤q` fails at `q = qcap` by maximality of `shared_upto`; if `shared_upto ≥ n` then `qcap = n ≤ shared_upto` and both fences require agreement only at levels `≤ shared_upto`, so they coincide on the whole range.

**RESOLUTION TRACE:** statement lines 1336–1364; the cell note ⟨n4⟩ 370–386 (shard 1 `.24`); the disposition 914–923 (shard 1 `.56`); the r4 correction 968–978 (shard 1 `.60`); the third consumer 1365–1372.

XREF: `GRTJA_PROOF_2026-08-08.md:JA-RES` — **20** · `JA-VAL` — **7** · `shared-key perimeter` — **5**.

**TEETH:** **`NONE`, signed and quoted:** “No machine leg can catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES) NOWHERE”. Disposition: **disclosed non-repair** + **AUDIT — in-house hostile pass**.

---

### EFF.GRTJB.s2of3.04  [supplier-finding]  ★ TERMINAL of the perimeter-consumer chain

**CANONICAL STATEMENT:** verbatim, lines 1365–1372.
**FORM:** bracketed rider.

> “**[r6, F-1 — the count above is amended a second time by the SAME level-slip
> disease at a third site: JB-VTX's (d3) min tie w_{q+1}(f) = v_{q+2}(f) is
> "JA-VAL one level up" (§3(d)), i.e. JA-VAL at level q+1, so it too needs the
> BYTE-EQUAL CHAIN THROUGH q. THREE consumers of the through-q condition:
> JB-DEV(ii)'s byte clause, JB-DEV(iii)'s (RES) layer, and JB-VTX(d3) (§0M
> row 11 (a2)); "all of JB-VTX" in the corrected statement above now reads
> with (d3) excepted. Unlike (RES), (d3) HAS a machine leg on its full fence:
> the runner gates it at q ≤ shared_upto, which is exactly `P≤q`.]**”

**CHAIN:** TERMINAL member of the chain opened at `.03`. **A chapter cut must read: THREE `P≤q` consumers — JB-DEV(ii), JB-DEV(iii)(RES), JB-VTX(d3); everything else on `P<q`.**

**SUPERSESSION KIND:** `inventory completion` — a third consumer added to a list twice claimed complete.

**CONDITIONALITY:** **NO frontier change** — (d3) carries a key perimeter, not an open proviso, so the four-member NO-LEG frontier (rows 4/5/12/22) is untouched. **And no leg change** — the runner's pre-existing gate turned out to BE the corrected fence.

**DERIVATION:** Identical in form to `.03`: the note's own §3(d) derivation line (“the weight recursion + JA-VAL one level up”, L1666–1667) instantiated at the tie's own read level.

**RESOLUTION TRACE:** statement lines 1365–1372; the body (d3) bracket 1667–1675 (`.24`); the split matrix cell 305 (shard 1 `.20` row 11); the disposition 1127–1163 (shard 1 `.73`); the recount 422–428 (shard 1 `.27`).

**TEETH:** **IND on the full re-fenced range.** The gate `if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):` at `grt_jb_checks.py` **L283** was **byte-verified at HEAD by this compiler**, and the second conjunct's redundancy re-derived from `grt_weld_probe.py` L211 (`self.RANK = len(levels)`) and L456–459 (`levels = […for i in range(T.NR)]`), giving `RANK = T.NR = n+1 ≥ qcap+1`. Disposition: **executable regression, scope-matched**.

---

### EFF.GRTJB.s2of3.05  [definition]

**CANONICAL STATEMENT:** verbatim, line 1373.
**FORM:** inline sentence.

> “Read data A_m := ℓ_{m−1}g_{m−1}γ_m, W_m := w_mΦ_m as in W-2/J-A.”

**CONDITIONALITY:** Unconditional. **`A_m` is the character exponent whose triviality is JA-VDIND's hypothesis** — the object the whole (VD-m) conditionality turns on (`.13`, `.47`). **`W_m := w_mΦ_m` is the roman-W read datum that §5's `[r4, F-8]` deliberately distinguishes from the SCRIPT `𝒲_m` weight lattice** (`.40`) — a notational collision the note flags explicitly.

**DERIVATION:** Definition, imported.

**RESOLUTION TRACE:** statement line 1373; `A_m` consumed at 1478–1491 and 2192–2194; `W_m` vs `𝒲_m` disambiguated at 2033–2035.

**TEETH:** NONE (definition).

---

### EFF.GRTJB.s2of3.06  [definition]  ★ the two frames and the shear

**CANONICAL STATEMENT:** verbatim, lines 1375–1386.
**FORM:** bold-headed paragraph + fixed-width display.

> “**The two frames.** Fix a level q (0 ≤ q ≤ n) and nonzero f ∈ O[x] with
> Φ_q-development f = Σ_i A_i·Φ_q^i (iterated division by the monic Φ_q).
>
>     PRINT FRAME    U(f) := { (i, u_i) : A_i ≠ 0 },
>                    u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})
>                    — the print's own N_{q+1}-ordinates (tex ~1370).
>
>     SHEARED FRAME  H(f) := { (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }
>                    — the harness eq-(12) ordinates (the S0.2 weight
>                    recursion's arguments; the GD-2 frame normalization).
>
>     THE SHEAR      Σ_q : (i, u) ↦ (i, e_q·u + h_q·i).”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| object | definition | provenance |
|---|---|---|
| **PRINT FRAME `U(f)`** | `{ (i, u_i) : A_i ≠ 0 }`, `u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})` | the print's own `N_{q+1}`-ordinates, `HigherNewton.tex` ~1370 |
| **SHEARED FRAME `H(f)`** | `{ (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }` | the harness eq-(12) ordinates; the S0.2 weight recursion's arguments; the GD-2 frame normalization |
| **THE SHEAR `Σ_q`** | `(i, u) ↦ (i, e_q·u + h_q·i)` | a theorem clause (§3(a)), **never a silent convention** |

**CONDITIONALITY:** Unconditional as definitions. **The frame declaration is a standing discipline of the note: “every polygon statement below displays which frame it lives in, and the shear itself is a theorem clause (§3(a)), never a silent convention.”** `Σ_q` is abscissa-preserving with positive `u`-coefficient `e_q` — the two properties LEMMA JB-AFF needs (`.19`). **E-3 (shard 3) later narrows what `Σ_q` preserves: the abscissa run, NOT ambient lattice data** — see `.23`.

**DERIVATION:** Definitions. The `Φ_q`-development exists and is unique by division with remainder by a monic polynomial over any commutative ring (the same fact §2(i) uses).

**RESOLUTION TRACE:** statement lines 1375–1386; consumed at 1636–1694 (§3(a)–(e)); correction site 3199–3228 (E-3, on what the shear preserves).

XREF: `docs/references/HigherNewton.tex:phiradic` — count **2** (the `φ_r`-adic development genre). The `~1370` ordinate definition is a LINE PIN, verified present in the file; NS-11 identifies the surrounding block.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:S0.2` — count **13**.
XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — count **7**.

**TEETH:** `jb_vtx` computes **fresh lower hulls of BOTH frames** and the vertex bijection between them (IND, 893 samples).

---

### EFF.GRTJB.s2of3.07  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 1388–1396.
**FORM:** bold-headed paragraph with an `[r1, G-8]` re-attribution.

> “The names are load-bearing: ~~GD-2's T-F machine check (41,720 instances)~~
> **[r1, G-8 — instrument re-attributed]** the T-F machine check of the O1thr
> rev-3 runner (`O1thr_phaseB_verifybrief_rev3.md` §9, family T-F: 41,720
> site-instances, 0 violations of WGEO/(M6c); the runner is CITED BY GD-2/GD-3,
> it is not GD-2's own instrument) verified the polygon tie in the SHEARED frame
> and measured 7,472 violations of the unsheared identification — every polygon
> statement below displays which frame it lives in, and the shear itself is a
> theorem clause (§3(a)), never a silent convention. (Both figures were
> re-checked against that source in JB-PE1 and are current, not stale.)”

**SUPERSESSION KIND:** `provenance-rider` — the instrument is re-attributed; the figures are unchanged.

**CONDITIONALITY:** **This is the empirical ground for the whole shear discipline**: the unsheared identification is not merely unproved, it is MEASURED FALSE 7,472 times. That measurement is what makes `.22`'s “The unsheared identification … is FALSE in general” a reported fact rather than a rhetorical flourish, and it is the note's own teeth family MJB-VTX one level down.

**PIN VERIFICATION (rule 23) — the cited source re-read at HEAD by this compiler:** `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md` **EXISTS**; fixed-string counts in it — `T-F` **10**, `41,720` **8**, `7,472` **2**, `WGEO` **16**, `M6c` **32**. **All five figures/designations verified present at the cited source. The r1/G-8 re-attribution is confirmed.**

**DERIVATION:** Foreign measurement, cited.

**RESOLUTION TRACE:** statement lines 1388–1396; the disposition 691–696 (shard 1 `.47` item G-8); consumed at 1648–1650 (`.22`).

XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — **7** · `GD-3` — **5**.
XREF: `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md:T-F` — **10**.

**TEETH:** **foreign-note measurement consumed as decorrelation** — 41,720 site-instances / 0 violations in the sheared frame against 7,472 violations unsheared. Disposition: **foreign-note evidence**, re-checked by JB-PE1.

---

### EFF.GRTJB.s2of3.08  [definition]

**CANONICAL STATEMENT:** verbatim, lines 1402–1410 — the theorem head plus the `[r1, G-7]` notation definition.
**FORM:** bold-headed opener + bracketed definition.

> “**THEOREM JB-DEV.** Level q ≥ 0, f ∈ O[x] nonzero, notation §1.
>
> **[r1, G-7 — notation, defined here at first use.]** m_{q+1}^GMN := the GMN
> print's KEY DEGREE at level q+1, i.e. deg φ_{q+1} = d₀·∏_{j<q} e_j g_j
> (the print's own recursion: deg φ_1 = d₀ = deg Φ_0^har and
> deg φ_{r+1} = e_r f_r · deg φ_r with (e_r, f_r) the print's level-r
> ramification/residual pair = the harness (e_{r−1}, g_{r−1})). The identity
> deg Φ_q^har = m_{q+1}^GMN is a consequence of the P-index dictionary of §1,
> not an extra hypothesis. (The symbol was used undefined in r0.)”

**SUPERSESSION KIND:** `inventory completion` (a symbol used undefined).

**CONDITIONALITY:** The theorem head's blanket “Level q ≥ 0” is **CORRECT for clauses (i), (ii), (iv)** and is narrowed per layer inside clause (iii) (`.11`). The degree identity is explicitly **not an extra hypothesis** — it follows from `.01`'s dictionary.

**DERIVATION:** Definition + a one-line consequence. `deg φ_{r+1} = e_r f_r · deg φ_r` with `(e_r, f_r) = (e_{r−1}, g_{r−1})` harness-side telescopes to `d₀·∏_{j<q} e_j g_j`, which is `deg Φ_q^har` by the harness recursion `deg Φ_{j+1} = e_j g_j · deg Φ_j`.

**RESOLUTION TRACE:** statement lines 1402–1410; the disposition 688–690 (shard 1 `.47` item G-7); the harness degree recursion is [ILN]† S0.1's.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13**.

**TEETH:** Exercised inside `jb_dev`'s development legs (the key degree is what the division is by).

---

### EFF.GRTJB.s2of3.09  [lemma]  (JB-DEV clause (i))

**CANONICAL STATEMENT:** verbatim, lines 1412–1421.
**FORM:** bold clause label + paragraph.

> “**(i) [same division].** Φ_q^har is monic of degree m_{q+1}^GMN, and the
> print's φ_{q+1}-adic development of f AT THE REPRESENTATIVE
> φ_{q+1} := Φ_q^har is the harness Φ_q-development digit-for-digit: both
> are THE canonical division chain by the same monic polynomial (uniqueness
> of division with remainder). Under W-2 clause 1, Φ_q^har is a GMN Def-2.12
> admissible representative on W-2's perimeter (of the ξ-conjugate class at
> the pinned (P-ell) convention; of the type itself when the character is
> support-trivial; STRICT at every level of the transported chamber, W2-C3)
> — so the left side is a legitimate print development, not a harness-only
> object.”

**CONDITIONALITY:** **PERIMETER-FREE** (matrix row 1; every level `q ≥ 0`), at the W2-C1 admissible representative. **W-2 clause 1's own conditionality rides**, and **E-2 (shard 3) re-reads the W2-C3 half** at the supplier's proved-to-first-twist (38/44) / measured-above (6/44) split. **Supplier grade updated: GRTW2 ACCEPTED at 2/2 (`adc6cf3`) at that honest split.**

**DERIVATION:** Uniqueness of quotient and remainder in division by a monic polynomial over any commutative ring — “the print's development (tex `phiradic` genre) and the harness development are the same recursion”; the representative legitimacy is W-2 clause 1 consumption (proof at L1549–1552).

**RESOLUTION TRACE:** statement lines 1412–1421; proof lines 1549–1552; matrix row 1 at 295 (shard 1); correction site 3135–3142 (E-2), 3148–3161 (supplier grade).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C1` — **22** · `W2-C3` — **22**.
XREF: `docs/references/HigherNewton.tex:phiradic` — **2**.

**TEETH:** `jb_dev` — `fresh_dev` (this runner's own schoolbook division) vs `PolyO.dev`, **893 samples, IND**. Plus a **SAME** third leg, disclosed at ⟨n1⟩ (shard 1 `.21`): `G.P.dev` is the same method on the same ring object behind a guard that already forced agreement — **violation UNREACHABLE, carries no information**.

---

### EFF.GRTJB.s2of3.10  [lemma]  (JB-DEV clause (ii))

**CANONICAL STATEMENT:** verbatim, lines 1423–1428.
**FORM:** bold clause label + paragraph.

> “**(ii) [byte clause].** If the junction chain is byte-equal through q (the
> W-2 §3.4(3) byte law from read data; TH-BASE gives it always at q = 1),
> then φ_{q+1}^cls = Φ_q^har byte-for-byte and (i) is the classifier's OWN
> expansion at its own construct key. On the weld roster the byte-equal set
> is the probe's F1 verdict pattern (12 GREEN / 18 RED of 30 walked
> junctions, reproduced by W-2's CK-BYTE from read data alone — consumed).”

**CONDITIONALITY:** **`P≤q` IS its hypothesis** (matrix row 2 — the one row where the through-q condition is not a fence but the antecedent). TH-BASE makes it unconditional at `q = 1`.

**ARITHMETIC AUDIT (rule 22):** 12 GREEN + 18 RED = **30 walked junctions** ✔. **Cross-check against the coverage correction (r1/G-6, shard 1 `.47`):** `jb_keyeq` walks `q = 1..T.n` i.e. print `r = 2..n+1`, never a top junction; the two instruments **share 12 junctions** (T3× at r = 3, six rows; I4× at r = 3,4, six rows) with **EXACT agreement (6 GREEN / 6 RED)**; **16 roster F1 junctions — all the top ones, carrying 12 of the probe's 18 F1 REDs — lie outside JB-KEYEQ's range.** Recount: 6 + 6 = 12 shared ✔; 12 of 18 REDs outside range ⇒ 6 REDs inside ✔ consistent with the 6 RED shared. **The quoted “12 GREEN / 18 RED of 30” is the PROBE's own figure and is exact against its committed output; the note says so.**

**DERIVATION:** W-2 §3.4(3) byte law + TH-BASE, consumed (proof at L1552–1553).

**RESOLUTION TRACE:** statement lines 1423–1428; proof line 1552; matrix row 2 at 296 (shard 1); the coverage correction 685–687 (shard 1 `.47`).

XREF: `GRTW2_PROOF_2026-08-08.md:TH-BASE` — count **8** · `(C-coll)` — **27** · `3.4` — **35** (§-anchor, upper bound).

**TEETH:** `jb_keyeq` — byte census, **25 rows, IND**, with a **signed vacuity disclosure**: 3 of the 25 are VACUOUS (`QO:x3-3/Q3`, `QO:x4+2x2+2/Q2`, `QO:x4-2/Q2` have `T.n = 0`, so the census loop `range(1, T.n+1)` walks nothing and the TH-BASE guard is never exercised).

---

### EFF.GRTJB.s2of3.11  [scope record]  (JB-DEV clause (iii) — the perimeter, per layer)

**CANONICAL STATEMENT:** verbatim, lines 1430–1455 — the clause head, the `[r1, G-9]` restatement and the `[r3, F-4]` three-layer split with its `[r4, F-3]` correction.
**FORM:** bold clause label + two nested bracketed riders.

> “**(iii) [coefficient correspondence, three layers].** **[r1, G-9 —
> quantifier restated to the perimeter the proofs need.]** This clause is
> asserted ONLY on the SHARED-KEY PERIMETER of §1: levels q with
> Φ_j^har = φ_{j+1}^cls byte-for-byte for all j < q, i.e. q ≤ qcap :=
> min(n, shared_upto + 1) — the runner's own `qcap_of(T, G)` quantifier. Off
> that perimeter the print frame is computed with keys that differ from
> Φ_0..Φ_{q−1}, and (VAL) is then FALSE, not merely unproved (J-A grades JA-VAL
> "PROVED unconditionally ON THE SHARED-KEY PERIMETER"). r0 inherited the
> theorem's blanket "level q ≥ 0" here; the machine evidence always quantified
> the narrower statement. **[r3, F-4 — ONE PERIMETER IS NOT ENOUGH FOR THREE
> LAYERS. The sentence above is correct for (VAL) and (GRID), which are JA-VAL /
> JA-GRID at level q. It is ONE LEVEL SHORT for (RES), which is JA-RES at read
> level m := q+1 … THE FENCE, PER LAYER (§0M rows 3/4/5): (VAL)
> and (GRID) on `P<q` = the SHARED-KEY PERIMETER 0 ≤ q ≤ qcap; **(RES) on the
> BYTE-EQUAL CHAIN THROUGH q (`P≤q`)**, which is strictly stronger ~~and excludes
> exactly the top level q = qcap …~~ **[r4, F-3 — corrected: the exclusion at q = qcap bites only
> when shared_upto < n (5 of the 16 roster towers: T3A/T3C/T3D/T3E/I4C); on the
> other 11 the two fences coincide over the whole level range … The fence itself is
> unchanged and the movement is still toward MORE conditionality where it bites
> at all.]** No machine leg is affected — the runner keys (RES)
> nowhere.]** For the common digit list (A_i):”

**CONDITIONALITY:** **CORRECTED FROM SHARD 3 BY CERTIFIER ANNEX E-4.** The clause “(VAL) is then FALSE, not merely unproved” is withdrawn. E-4 (L3267–3272):

> “Every live
> sentence saying that JB-DEV(iii)(VAL) or JB-VTX(a) is “FALSE, not merely
> unproved” off the shared-key perimeter is corrected to “**NOT SUPPLIED by this
> note outside the stated perimeter**.” Byte inequality of representatives removes
> the J-A theorem instance cited by the proof, but does not by itself imply
> inequality of the induced values on every polynomial.”

and E-4's corrected scope display names this clause first: “**JB-DEV(iii)(VAL) and (GRID) are asserted on `P<q` only; outside `P<q` this note makes no claim about their truth.**” E-4's consumer sweep item 2 names “§2(iii)” explicitly as a site where the phrase is re-read. **SUPERSESSION KIND: `counter re-reading`** — an unsupported negation withdrawn; **“No perimeter is widened and no on-perimeter proof moves.”**

**E-4's own ground, quoted (the f = 1 instance):** “Its development at every monic key has the sole digit A₀ = 1; normalized valuations give `w_q(A₀) = w_q(1) = 0 = v_{q+1}(1) = v_{q+1}(A₀)`, and both point sets are the singleton {(0,0)}, fixed by Σ_q. Thus (VAL) and the pointwise shear hold for this instance independently of the bytes of all positive-level keys.”

**DERIVATION:** Per layer, by instantiating each supplier theorem at its OWN read level (see `.03`).

**RESOLUTION TRACE:** statement lines 1430–1455; the perimeter definitions 1309–1334 (`.02`); correction sites 968–978 (r4/F-3, shard 1 `.60`), 3267–3312 (E-4).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VAL` — **7** · `JA-GRID` — **11** · `JA-RES` — **20**.

**TEETH:** (VAL) **IND** over `0 ≤ q ≤ qcap`; (GRID) carry half **IND**, grid half **NONE**; (RES) **NONE** — “the runner keys (RES) nowhere”.

---

### EFF.GRTJB.s2of3.12  [TABLE]  (JB-DEV clause (iii) — the three-layer display)

**CANONICAL STATEMENT:** verbatim, lines 1457–1469 — the fixed-width `(VAL)/(GRID)/(RES)` display with its `[r3, F-4]` rider.
**FORM:** display.

>     (VAL)  w_q(A_i) = v_{q+1}(A_i) for every i           [JA-VAL, consumed]
>     (GRID) the on-line attained abscissas lie on the print's T-side grid
>            s + j·e_q, and the plain carry = the side-lattice crossing
>            indicator                                  [JA-GRID/W2-L0, consumed]
>     (RES)  at read level m := q+1 ≥ 2 the print residual coefficients obey
>            the per-slot character-gauge law c_i = z_{m−1}^{−i·A_{m−1}}·C_i
>            against the harness packed digits C_i — unconditional at m = 2,
>            per-digit proviso at m ≥ 3            [JA-RES, consumed with
>                                                   JA-BOX-1/BOX-2 verbatim]
>            **[r3, F-4] — this layer alone is asserted on the BYTE-EQUAL CHAIN
>            THROUGH q (`P≤q`, §1), i.e. J-A's perimeter at its own read level
>            m = q+1; NOT on the shared-key perimeter `P<q` the two layers above
>            it use. (RES) is also the ONE layer with no machine leg (§0M row 5).**

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| layer | statement | source | fence | evidence |
|---|---|---|---|---|
| **(VAL)** | `w_q(A_i) = v_{q+1}(A_i)` for every `i` | JA-VAL, consumed | `P<q` | **IND** — `G.vgen(q+1,A) == T.wlev(q,A)`, cross-engine, `0 ≤ q ≤ qcap` |
| **(GRID)** | the on-line attained abscissas lie on the print's T-side grid `s + j·e_q`, and the plain carry = the side-lattice crossing indicator | JA-GRID / W2-L0, consumed | `P<q` **AND** JA-GRID(a)'s `[JA-r1]` `u ≥ 0` proviso | carry half **IND** (`jb_eps` keys JA-GRID(c)); **grid half NONE** |
| **(RES)** | at read level `m := q+1 ≥ 2` the print residual coefficients obey `c_i = z_{m−1}^{−i·A_{m−1}}·C_i` against the harness packed digits `C_i` | JA-RES, consumed with JA-BOX-1/BOX-2 verbatim | **`P≤q`** (r3/F-4) **+** JA-RES's own fence: free at `m = 2`, per-digit proviso at `m ≥ 3` (= (VD-(m−1)) at every on-line digit, r4/F-1) | **NONE — no family keys (RES) anywhere** |

**CONDITIONALITY:** Per row above. **The three layers have three different perimeters and three different evidence classes — that split IS the r3 correction, and it is why one “clause (iii)” cannot be graded as one object.**

**DERIVATION:** Each layer is a consumption; the proof line is “(iii) consumption as displayed” (L1553).

**RESOLUTION TRACE:** statement lines 1457–1469; proof line 1553; matrix rows 3, 4, 5 at 297–299 (shard 1 `.20`); the fences at `.11`, `.14`; the r4/F-1 (c)-cell completion 950–958 (shard 1 `.58`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-L0` — **5**. `GRTJA_PROOF_2026-08-08.md:JA-BOX-1` — **8** · `JA-BOX-2` — **7**.

**TEETH:** as tabulated. **(RES) is one of the note's four frontier cells.**

---

### EFF.GRTJB.s2of3.13  [supplier-finding]  ★ the (VD-m) reading fence

**CANONICAL STATEMENT:** verbatim, lines 1471–1495.
**FORM:** bold-headed bracketed block.

> “**[r1, F1 — the reading fence that r0 lacked, and that §5 got wrong.]**
> (RES)'s "unconditional at m = 2" is a statement about JA-RES, the PER-SLOT
> character-gauge law on residual coefficients. It does **NOT** transfer to the
> EVALUATED dictionary (VD-m) of J-A §3.4 (the identity
> z_m^{τ_m(A)}·R_m^cls(A)(z_m) = ε_m(β)·R_m v(A) between assembled read
> values). The per-slot law implies (VD-m) only through COROLLARY JA-VDIND,
> whose hypothesis is ABSOLUTE triviality of the slot character on the attained
> abscissas (z_{m−1}^{i·A_{m−1}} = 1 for every attained i; sufficient:
> A_{m−1} = 0, i.e. e_{m−2} = 1, or ord(z_{m−1}) | A_{m−1} plus the abscissa
> condition — single-slot support alone is NOT sufficient). At m = 2 that is
> z_1^{i·A_1} = 1 with A_1 = ℓ₀g₀γ₁, ~~which FAILS on towers with e₀ ≥ 2 and a
> nontrivial z₁ — and the sealed runner exhibits ten such in-roster failures
> (§7.1, §7.4)~~ **[r2, G2-4 — the struck clause asserted a failure SET and the
> note's own roster refutes it (T3E has e₀ = 2 with a nontrivial z₁ and scores
> 6/6). What is actually available here is ONE implication, in one direction:
> e₀ = 1 ⇒ A_1 = 0 ⇒ z_1^{i·A_1} = 1 at every abscissa ⇒ (VD-2) holds (J-A's own
> displayed sufficient condition, consumed). Its contrapositive is all the
> geography this note may claim: an m = 2 failure REQUIRES e₀ ≥ 2, but e₀ ≥ 2
> does NOT predict failure, and no condition in this note separates the failing
> from the scoring e₀ ≥ 2 towers. The sealed runner exhibits ten m = 2 in-roster
> failures (§7.1, §7.4) — the DATA, not a characterisation]**. Every
> (VD-m)-consuming statement in this note is fenced accordingly; **[r2,
> hygiene]** nothing (VD-m)-DEPENDENT above m = 1 is unconditional (this
> sentence is about (VD-m) only — LEMMA JB-EPS is unconditional at every
> m ≥ 1, as its own grade line says).”

**SUPERSESSION KIND:** `replacement` (r1/F1: a false perimeter replaced) + `counter re-reading` (r2/G2-4: a mechanism claim struck and NOT replaced).

**CONDITIONALITY:** **INBOUND CORRECTION E-1 lands on the “(R-coll)” label** wherever it appears downstream of this fence (`.47`, `.56`): “Wherever this note's text says ‘(R-coll)’, read the root-inclusive form of GRTJA at HEAD (≥ 5d95805).” E-1 explicitly certifies **this note's operative fence was already correct** (“root triviality a HYPOTHESIS at every m ≥ 2 — PE2's own adjudication: uncontaminated”).

**DERIVATION:** The distinction is J-A's own: JA-RES is a per-slot law on residual coefficients; (VD-m) is an identity between **assembled read values**; the implication runs only through JA-VDIND's absolute-triviality hypothesis. The note also records what is **NOT** sufficient: “single-slot support alone is NOT sufficient”.

**RESOLUTION TRACE:** statement lines 1471–1495; the disposition 638–659 (shard 1 `.44`); the mechanism strike 792–803 (shard 1 `.51`); the consuming theorem 2186–2203 (`.47`); the census 2494–2546 (shard 3); correction site 3125–3133 (E-1).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VDIND` — **21** · `(VD-m)` — **10** · `(R-coll)` — **7** · `JA-RES` — **20**.

**TEETH:** **executable regression that disconfirmed the author** — the note's own sealed runner machine-evaluates (VD-2) FALSE on 10 of 13 roster boundary rows, and PE2 re-derived the split from the committed JSON alone without calling `vd_eval`. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJB.s2of3.14  [hypothesis]  ★ CHAIN HOME (body site) — the `u ≥ 0` proviso

**CANONICAL STATEMENT:** verbatim, lines 1497–1537 — the `[r1, G-5]` naming, the `[r2, G2-5]` retraction, and the `[r5, F-3]` narrowing.
**FORM:** bold-headed bracketed block with two nested riders.

> “**[r1, G-5 — the (GRID) layer carries an inherited PROVISO.]** JA-GRID(a) is
> graded in J-A with the `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 (the
> bare V ∈ ℤ_{≥0} quantifier was FALSE at small V); that proviso is an inline
> J-A repair, not one of JA-BOX-1..5, so JB-BOX-2's blanket "rides J-A's boxes
> verbatim" did not carry it in r0. It is now named in JB-BOX-2 ~~with its
> discharge: at every consumption site here the argument V is a level-m weight
> of a nonzero polynomial in the tower's own window, so V ≥ e_{r−1}f_{r−1}
> v_r(φ_{r−1}) — J-A's own hypothesis for u ≥ 0 — and the runner's `s_geo`
> leg recomputes s from the geometry with no ℓ at all.~~ **[r2, G2-5 — THE
> DISCHARGE IS RETRACTED. The struck text asserted an implication it never
> proved …, and the implication is not plausible as
> stated: this note's own quantifiers are "f ∈ O[x] nonzero" (§2) and
> "deg f < deg Φ_m" (§4/§5), both of which admit UNITS, whose level-m weight is
> 0, while e_{r−1}f_{r−1}v_r(φ_{r−1}) is positive at r ≥ 2. J-A grounds that
> bound in the PRINT's own hypothesis at the site where `construct` is invoked;
> J-B has no such site hypothesis and supplied no substitute. The `s_geo` remark
> was a red herring: `s_geo` recomputes s geometrically (ℓ-free), which
> certifies the s-VALUE, not the sign of u. STATUS: the proviso is CARRIED, NOT
> DISCHARGED … What a real discharge requires:
> derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) (or directly V ≥ s_m^wt(V)·h_{m−1},
> which is what u ≥ 0 says) for EVERY V in the quantified window — units
> included … Two facts frame the residual: at V = 0 one
> has s^wt = 0 and u = 0 ≥ 0, so no counterexample to the proviso is exhibited
> by units; ~~and J-A's own counterexample lives at small positive V
> ((e,h) = (2,3), V = 1 ⇒ u = −1), which nothing in this note excludes from the
> level-m weight lattice. So the proviso may well hold at every site — this note
> does not show it.~~ **[r5, F-3 — the struck frame went STALE at r4 and is
> corrected: the r4-defined level-(q+1) weight lattice 𝒲_{q+1} (§5, forward
> pointer — the object is DEFINED there) DOES exclude J-A's (e,h) = (2,3),
> V = 1 instance (by parity), and u ≥ 0 is PROVED on ALL of 𝒲_{q+1} — four
> lines from the displayed description, §5's [r5, F-3] display,
> machine-confirmed. WHAT THIS DELIVERS AT THIS LAYER: the quantifier here is
> f nonzero with NO degree bound, and JA-GRID(a) is applied at V = w_{q+1}(f);
> membership V ∈ 𝒲_{q+1} holds by definition exactly at deg f < deg Φ_{q+1} —
> THERE THE PROVISO NOW HOLDS; off that sub-window membership is not
> established by anything this note consumes, and the proviso is CARRIED as
> that membership hypothesis (§0M rows 4/12, column (b)).]**]** (JB-EPS is unaffected:
> it cites JA-GRID(c), which carries no proviso.)”

**CHAIN (rule 25) — the note's deepest, four layers.** **CHAIN HOME is §0M column (b)** (shard 1 `.14`), which carries all four members and the TERMINAL reading. This unit is the **BODY SITE** of members 1–3. `CHAIN-MEMBER: s1of3.14 positions 1–3.`
1. **r1/G-5** — the proviso named in JB-BOX-2 *with a discharge argument*.
2. **r2/G2-5** — the discharge **RETRACTED** (“it was an assertion, not a derivation”).
3. **r5/F-3** — **NARROWED**: `u ≥ 0` PROVED on all of `𝒲_m`; residue = lattice MEMBERSHIP at the unbounded-degree quantifier.
4. **r6/m-1 → r7/F-1** (shard 1 `.75`, `.77`) — **TERMINAL**: membership is SUFFICIENT; the converse is EQUIVALENT at `m = 1`, of unknown strictness at `m ≥ 2`.

**SUPERSESSION KIND:** `replacement` (r2) + `scope-pin` (r5).

**CONDITIONALITY:** **Exactly two consumers: matrix row 4 (this layer) and row 12 (JB-VTX(d4)).** Both remain frontier members after the narrowing. **JB-EPS is explicitly unaffected** — it cites JA-GRID(c), which carries no proviso — a separation the note states here and repeats at `.46` and `.52`.

**DERIVATION:** The retraction's refutation is displayed (units have level-m weight 0 while the claimed bound is positive at `r ≥ 2`; `s_geo` certifies the s-value, not the sign of `u`). The genuine equivalence `u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}` is immediate from `u := (V − s_m^wt(V)·h_{m−1})/e_{m−1}` with `e_{m−1} > 0`. **The positive discharge is `.41`'s four-line theorem.**

**RESOLUTION TRACE:** statement lines 1497–1537; **proof lines 2046–2062** (§5's four-line theorem, `.41`) and **2085–2111** (the SCOPE block, `.42`); correction sites 680–684, 804–819, 1053–1073, 1179–1190, 1218–1258 (all shard 1); the box site 2340–2373 (`.56`).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11** · `JA-BOX-1` — **8** (range endpoints JA-BOX-1..5 verified individually in shard 1 §3.1).

**TEETH:** **`NONE` on both consumers' grid halves.** The lattice theorem's corroboration is verifier-owned (PE6 598,500/0, PE7 reproducing exactly, PE8 on a wider box 340/0). Disposition: **disclosed non-repair** for the rows; **accepted-with-decorrelation-supplied** for the theorem.

---

### EFF.GRTJB.s2of3.15  [fence]  (JB-DEV clause (iv))

**CANONICAL STATEMENT:** verbatim, lines 1539–1547.
**FORM:** bold clause label + paragraph.

> “**(iv) [cross-key fence, displayed not claimed].** For a DIFFERENT strict
> representative φ′ of the same type, blanket digit equality and blanket
> operator equality are FALSE (J-A §4(i): v_{r+1}(φ − φ′) = e_r·v_r(φ) —
> the standard MacLane representative-dependence); the lawful transport
> across representatives is W-2 clause 2's covariance (slot-ratio characters)
> and clause 3's chamber re-instantiation, never a byte identity. This is
> the JuncForge parity-wall lesson honored: J-B is stated against the
> semantic development objects at a NAMED representative; no SideReads/
> TreeModel transcription is consumed.”

**CONDITIONALITY:** **PERIMETER-FREE — a displayed fence, cited, with nothing to key** (matrix row 6). **Note the asymmetry E-4 turns on:** clause (iv) says a BLANKET cross-representative identity is FALSE; E-4 says that does NOT license “every off-perimeter instance fails”. E-4 quotes exactly this: “JB-DEV(iv)'s representative-dependence warning rules out a blanket cross-representative identity, but **supplies no derivation that every off-perimeter instance fails**.” **So (iv) stands unchanged and E-4's correction at `.11`/`.20` is consistent with it.**

**DERIVATION:** Cited (J-A §4(i)'s MacLane representative-dependence identity).

**RESOLUTION TRACE:** statement lines 1539–1547; proof line 1553 (“(iv) cited”); matrix row 6 at 300 (shard 1); the E-4 consistency 3282–3286 (shard 3); the standing box 2421–2426 (`.58`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C3` — **22**. `GRTJB_PROOF_2026-08-08.md:JuncForge` — count **2** (note-local reference to a corpus lesson; no external designation claimed).

**TEETH:** **NONE** — “a displayed fence: nothing to key”. Disposition: **signed non-applicability**.

---

### EFF.GRTJB.s2of3.16  [changes-record]  (JB-DEV — the proof and the two struck grade lines)

**CANONICAL STATEMENT:** verbatim, lines 1549–1560.
**FORM:** `*Proof.*` marker + two struck grade lines.

> “*Proof.* (i) Uniqueness of quotient and remainder in division by a monic
> polynomial over any commutative ring: the print's development (tex
> `phiradic` genre) and the harness development are the same recursion; the
> representative legitimacy is W-2 clause 1 consumption. (ii) W-2 §3.4(3)
> byte law + TH-BASE, consumed. (iii) consumption as displayed. (iv) cited.
> ∎ Grade: ~~PROVED at attempt grade with the displayed consumptions; no
> clause here upgrades W-2/J-A.~~ ~~**[r2, G2-1 — the perimeter carried onto this
> grade line, where r1 left it in the body only: …]**~~”

**CONDITIONALITY:** **Both grade lines are STRUCK and superseded by surface 2** (`.17`). The PROOF itself is live and is the derivation of `.09`–`.15`. **The r2 line is struck not because it was wrong but because r3 replaced the generation mechanism** — its “only defect of substance was (iii)(RES)'s perimeter”, per surface 2's own preamble.

**DERIVATION:** This unit IS the proof. Four one-line discharges, each naming its ground; the substantive content is in the clauses.

**RESOLUTION TRACE:** statement lines 1549–1560; the superseding surface 1562–1584 (`.17`).

**TEETH:** carried by the clauses.

---

### EFF.GRTJB.s2of3.17  [TABLE]  ★ SURFACE 2 of 14 — the §2 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1562–1584.
**FORM:** bold-headed bracketed block + fixed-width per-clause display.

> “**[r3, STEP 2 — SURFACE 2 of 14, REGENERATED FROM §0M rows 1–6 (the struck
> r2 line above is superseded; its only defect of substance was (iii)(RES)'s
> perimeter). ∎ GRADE: PROVED at attempt grade with the displayed consumptions;
> no clause here upgrades W-2/J-A. PER CLAUSE:**
>
>     (i)         every level q ≥ 0; at the W2-C1 admissible representative
>                 φ_{q+1} := Φ_q^har.                              [row 1]
>     (ii)        on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`, §1); TH-BASE gives
>                 q = 1 always.                                    [row 2]
>     (iii)(VAL)  on the SHARED-KEY PERIMETER (`P<q`), 0 ≤ q ≤ qcap — off it
>                 (VAL) is FALSE, not merely unproved.             [row 3]
>     (iii)(GRID) on `P<q` AND on JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso,
>                 CARRIED AND UNDISCHARGED (r2, G2-5); narrowed r5/F-3:
>                 PROVED at deg f < deg Φ_{q+1} (V ∈ 𝒲_{q+1}, §5), membership
>                 residue at the unbounded-degree quantifier.      [row 4]
>     (iii)(RES)  on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — one level deeper
>                 than r2's fence, F-4; the exclusion bites on 5/16 roster
>                 towers only ((a2), r4/F-3) — plus JA-RES's own fence
>                 (unconditional at m = q+1 = 2, per-digit proviso at m ≥ 3 =
>                 (VD-(m−1)) at every on-line digit, JA-BOX-2; r4/F-1). NOT
>                 the evaluated dictionary (VD-m) at level m.      [row 5]
>     (iv)        a displayed fence, cited; no level condition.    [row 6]
>
> **]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating matrix row |
|---|---|---|
| **(i)** | every level `q ≥ 0`; at the W2-C1 admissible representative `φ_{q+1} := Φ_q^har` | row 1 |
| **(ii)** | on `P≤q`; TH-BASE gives `q = 1` always | row 2 |
| **(iii)(VAL)** | on `P<q`, `0 ≤ q ≤ qcap` — ~~off it (VAL) is FALSE, not merely unproved~~ **→ E-4: NOT SUPPLIED outside the stated perimeter** | row 3 |
| **(iii)(GRID)** | `P<q` **AND** JA-GRID(a)'s `u ≥ 0` proviso; narrowed r5/F-3 to PROVED at `deg f < deg Φ_{q+1}`, membership residue off it | row 4 |
| **(iii)(RES)** | `P≤q` (r3/F-4; exclusion bites on 5/16, r4/F-3) **+** JA-RES's own fence (free at `m = 2`; per-digit proviso at `m ≥ 3` = (VD-(m−1)) at every on-line digit, r4/F-1). **NOT (VD-m) at level m** | row 5 |
| **(iv)** | a displayed fence, cited; no level condition | row 6 |

**CONDITIONALITY:** **This surface is a REGENERATION of §0M rows 1–6, not an independent authority** (FREEZE PREDICATE 2). **E-4 re-reads the (VAL) row's negation clause**; E-4's consumer sweep item 2 names “§2 ∎ Grade” explicitly. Nothing else moves.

**ARITHMETIC AUDIT (rule 22):** clauses listed = 6 (i, ii, iii(VAL), iii(GRID), iii(RES), iv); generating rows cited = 1, 2, 3, 4, 5, 6 = **6, contiguous, no gaps, no repeats** ✔. Cross-check against §0M rows 1–6 (shard 1 `.20`): every fence in the surface appears as a matrix cell, and every non-blank cell in rows 1–6 appears in the surface. **The surface's bidirectional claim (“Every fence below is a cell of that table; the table carries no fence this cap omits”, applied per surface) VERIFIES for rows 1–6.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1562–1584; generating rows 295–300 (shard 1 `.20`); correction site 3301–3304 (E-4).

**TEETH:** per row; see `.12`.

---

### EFF.GRTJB.s2of3.18  [instrument-record]  (JB-DEV — the machine bracket, restated at r3/F-2)

**CANONICAL STATEMENT:** verbatim, lines 1585–1609 — the struck r0 bracket and the `[r3, F-2]` replacement.
**FORM:** struck display + bold-headed bracketed replacement.

> “~~[Machine: JB-DEV — the development recomputed
> by this runner's OWN schoolbook division (fresh leg, decorrelated from the
> shared PolyO.dev used by both engines) and compared against both engines'
> digit lists at every shared level; JB-KEYEQ — byte-equality census tied to
> the W-2 read-data byte law; teeth MJB-DEV.]~~
>
> **[r3, F-2 — MACHINE BRACKET RESTATED to exactly what the code establishes;
> the struck bracket's "both engines" is WITHDRAWN. [Machine, classified as in
> §0M column (f): JB-DEV — TWO legs carry information. (1) ONE genuine second
> implementation (IND, 893 samples): the development recomputed by this runner's
> OWN schoolbook division `fresh_dev` against the engine's `PolyO.dev` on the
> same key. (2) ONE genuine CROSS-ENGINE tie (IND): the (VAL) digit-weight
> identity `G.vgen(q+1, A) == T.wlev(q, A)`, the print engine's valuation
> recursion against the harness's, at every digit and every level 0 ≤ q ≤ qcap.
> A THIRD leg carries NO information and is disclosed as such: `G.P.dev(f,
> G.phi[q+1])` is the SAME `PolyO.dev` bound to the SAME ring object … it is guarded by
> `tuple(G.phi[q+1]) == key`, so its arguments are byte-equal, and it is reached
> only after a `continue` on `dvF != dvI` has already forced agreement. The
> violation `'fresh dev != print dev'` is therefore UNREACHABLE: SAME-COMPUTATION
> (PE3 F-2 = PE1/G-1's disease at its third site). There is ONE engine comparison
> in this family, not two. JB-KEYEQ — byte-equality census tied to the W-2
> read-data byte law (25 rows; 3 VACUOUS, T.n = 0, r1/G-3); teeth MJB-DEV
> (garbled key, 3/3 caught).]]**”

**SUPERSESSION KIND:** `counter re-reading` — an advertised second engine re-read as the same computation.

**CONDITIONALITY:** **The correction DOWNGRADES the note's own advertised evidence** and is the third site of one disease (PE1/G-1 at the tree family, PE2/G2-2 inside the repair instrument, PE3/F-2 here). **This compiler independently confirmed the construction the note cites:** `grt_weld_probe.py` L456–459 is `def gmn_from_tower(T, mut=False)` building `levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]` and returning `GmnLeg(T.R, T.d0, T.Phi[0], levels, …)` — **the ring argument is `T.R`, the tower's own ring, exactly as ⟨n1⟩ states.**

**DERIVATION:** Code reading, displayed.

**RESOLUTION TRACE:** statement lines 1585–1609; the cell note ⟨n1⟩ 326–337 (shard 1 `.21`); the disposition 898–905 (shard 1 `.55` STEP 4); the §7.1 row 2480 (shard 3).

**TEETH:** two IND legs + one **SAME** leg with an **UNREACHABLE** violation + a **signed vacuity disclosure** on JB-KEYEQ (3 of 25 rows) + planted mutant **MJB-DEV** (garbled key, 3/3 caught, fired).

---

### EFF.GRTJB.s2of3.19  [lemma]  LEMMA JB-AFF

**CANONICAL STATEMENT:** verbatim, lines 1615–1621.
**FORM:** bold-headed display with its proof inline.

> “**LEMMA JB-AFF (two lines, displayed).** Let Σ : (i, u) ↦ (i, a·u + b·i + c)
> with a > 0, b, c ∈ ℚ. Then Σ maps lower convex hulls to lower convex hulls
> and vertices to vertices, bijectively, preserving abscissas. *Proof.* Σ is
> affine and abscissa-preserving, so it maps segments to segments and
> preserves "lies strictly below the chord": a·u + b·i + c < a·u′ + b·i + c
> ⟺ u < u′ at equal i, since a > 0. Hulls, faces, and strict-vertex
> conditions are defined by these two relations. ∎”

**CONDITIONALITY:** **UNCONDITIONAL — no perimeter, no proviso, no [RMG] clause, no (VD-m)** (matrix row 7; §7.2's own row says exactly this). Two hypotheses do real work: `a > 0` (the order-preservation) and abscissa-preservation. **Note what the lemma does NOT claim, and what E-3 later needs it not to claim: it says nothing about ambient lattice data or unimodularity** — only hulls, vertices, abscissas.

**DERIVATION:** Self-contained and displayed in full above: affineness + abscissa-preservation ⇒ segments to segments; `a > 0` ⇒ the strict-below-chord relation is preserved at equal `i`; hulls, faces and strict-vertex conditions are defined by those two relations. **Two lines, no consumption.**

**RESOLUTION TRACE:** statement lines 1615–1621 (statement and proof are one span); matrix row 7 at 301 (shard 1); applied at 1645–1650 (`.22`) and 1682–1694 (`.25`).

**TEETH:** **NONE as a lemma — “its content is exercised inside rows 9/10”** (matrix row 7's own (f) cell), i.e. inside `jb_vtx`'s fresh-hull/vertex-bijection and per-side slope/length legs. Disposition: **signed non-applicability**, with the exercise site named.

---

### EFF.GRTJB.s2of3.20  [scope record]  THEOREM JB-VTX — head and perimeter

**CANONICAL STATEMENT:** verbatim, lines 1623–1634.
**FORM:** bold-headed opener with a struck quantifier and its `[r1, G-9]` replacement.

> “**THEOREM JB-VTX.** Level q with read (e_q, h_q) defined ~~(0 ≤ q ≤ n)~~
> **[r1, G-9 — PERIMETER RESTATED AT THE THEOREM: 0 ≤ q ≤ qcap, where
> qcap := min(n, shared_upto + 1) is the SHARED-KEY perimeter of §1 (keys
> shared strictly below q), the runner's own `qcap_of(T,G)`. This is not
> cosmetic: clause (a) consumes JA-VAL for the digits AND for the key
> (v_{q+1}(φ_{q+1}) = w_qΦ_q), and J-A grades JA-VAL "PROVED unconditionally
> on the shared-key perimeter"; off it the print frame U(f) is computed with
> keys ≠ Φ_0..Φ_{q−1} and clause (a) is FALSE, not merely unproved. r0's grade
> line named only W-2 clause 1, which does not carry this]**,
> f ∈ O[x] nonzero, frames as §1, all statements at the representative
> φ_{q+1} := Φ_q^har (legitimate by W-2 clause 1 on its perimeter; on
> byte-equal chains this is the classifier's own key, JB-DEV(ii)).”

**SUPERSESSION KIND:** `scope-pin`.

**CONDITIONALITY:** **CORRECTED FROM SHARD 3 BY E-4** — “clause (a) is FALSE, not merely unproved” is withdrawn. E-4's corrected scope display names this head directly:

> “**JB-VTX(a), and consequently (b)/(c)/(d1)/(d2)/(d4) at the theorem's common
> head, are asserted on `P<q` only; outside it this note makes no claim.**
> The separately deeper fences remain unchanged: JB-DEV(iii)(RES) and
> JB-VTX(d3) continue to require `P≤q`.”

and its consumer sweep item 2 lists “the JB-VTX theorem head” among the sites where the phrase is re-read. **SUPERSESSION KIND for E-4: `counter re-reading`.** Additionally **`.24`'s (d3) is EXCEPTED from this head's `P<q`** by r6/F-1 and rides `P≤q` instead.

**DERIVATION:** The perimeter is what the consumed theorem needs: clause (a) consumes JA-VAL for the digits **and for the key** (`v_{q+1}(φ_{q+1}) = w_qΦ_q`), and J-A grades JA-VAL on the shared-key perimeter.

**RESOLUTION TRACE:** statement lines 1623–1634; the perimeter definition 1323–1334 (`.02`); the (d3) exception 1665–1675 (`.24`); correction sites 697–700 (shard 1 `.46`), 3267–3312 (E-4).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VAL` — **7** · `shared-key perimeter` — **5**. `GRTW2_PROOF_2026-08-08.md:W2-C1` — **22**.

**TEETH:** the runner runs the shear/vertex/slope families over `0 ≤ q ≤ qcap_of(T,G)`; **off-perimeter counter 0 on the roster**.

---

### EFF.GRTJB.s2of3.21  [lemma]  JB-VTX (a) — the shear is exact, pointwise

**CANONICAL STATEMENT:** verbatim, lines 1636–1643.
**FORM:** bold clause label + displayed computation.

> “**(a) [the shear is exact, pointwise].** H(f) = Σ_q(U(f)) with
> Σ_q(i, u) = (i, e_q·u + h_q·i): indeed e_q·u_i + h_q·i =
> e_q·v_{q+1}(A_i) + i·(e_q·v_{q+1}(φ_{q+1}) + h_q) = e_q·w_q(A_i) + i·γ_{q+1}
> by JA-VAL and the weight recursion γ_{q+1} = e_q·w_qΦ_q + h_q (JA-PIN
> clause 7). Moreover e_q·u_i + h_q·i = v_{q+2}(A_i·Φ_q^i) (propertiesv
> item 3 at a single digit): THE SHEARED FRAME IS THE PRINT'S OWN NEXT-LEVEL
> BOOKKEEPING — the harness ordinates are the v_{q+2}-values of the
> monomials, the print ordinates their v_{q+1}-values.”

**CONDITIONALITY:** `P<q` + W2-C1 (matrix row 8). **The second sentence is the one that consumes `propertiesv` item 3 and is a CITE-SCOPE row** (see the reading note below). **E-4 withdraws the head's negation gloss** (`.20`).

**DERIVATION:** Displayed arithmetic + two consumptions, both named inline: (1) JA-VAL gives `v_{q+1}(A_i) = w_q(A_i)`; (2) JA-PIN clause 7's weight recursion `γ_{q+1} = e_q·w_qΦ_q + h_q` converts the `i`-coefficient. The identification with `v_{q+2}(A_i·Φ_q^i)` is `propertiesv` item 3 at a single digit.

**READING NOTE (external, not an edit) — the CITE-SCOPE row for the whole shard.** `runs/qgen/Q7_output.log` classifies GRTJB's GMN print anchors as **CITE-SCOPE**, naming exactly these consumption sites: *“These are load-bearing in JB-VTX(a), (c), and (d1). The pasted note gives locations and conclusions but not the publication's hypotheses on the base field. Generality to F_q((t)) therefore cannot be certified from this slice.”* `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-11** resolves it:

- **Published scope of the cited source is ℚ_p-only, confirmed at the local print:** `docs/references/HigherNewton.tex` line 401, *“We fix a finite extension $K$ of $\Q_p$ as a base field …”*.
- **Local label identification:** `\label{propertiesv}` = `HigherNewton.tex` line 1028 = GMN **Proposition 2.7**; `\label{shape}` = line 1401 = GMN **Lemma 2.17**; `\label{phir}` = line 1257 = GMN **Theorem 2.11**.
- **Retarget for `propertiesv` item 3 — verdict COVERS-ALL-O (definitional):** **[GN15] §1.2** defines the augmented valuation by exactly that formula — *“$\mu'(g)= \mathrm{Min}_{0\le s}\{\mu(a_s\phi^s)+s\nu\}$, where $\sum a_s\phi^s$ is the canonical $\phi$-expansion of $g$. We denote $\mu'=[\mu;\phi,\nu]$.”* — “i.e. at general scope the statement is the **definition** of `v_r`, which is strictly stronger than citing it as a proposition.”
- **Retarget for `shape` items 1–2 (consumed at `.24`/(d1)) — COVERS-ALL-O:** **[GN15] Lemma 1.5 + Corollary 1.14**; equivalently **[FGMN] Lemma 2.2 + Prop 5.14 / Cor 5.15**, and **[AGNPRW] Lemma 4.2**.
- **Retarget for `rescoeff` / `t(i)` — COVERS-ALL-O:** **[AGNPRW] §2.2 definition (3)** + **[GN15] Theorem 1.9**.
- **The price, quoted:** *“the general-scope sources use MacLane/graded-algebra normalizations … rather than GMN's integer-rescaled `v_r = e_{r−1}H_{r−1}∘S_{r−1}`; the re-cite therefore carries a **normalization-shear obligation** — exactly the one `GENTOW2_PROOF_2026-08-09.md` already discharges for the FGMN side … Reuse that.”*

**The note's own text is compiled as written; the retarget is RECORDED, NOT APPLIED.** See shard 1 OPEN-CALL 2 for the standing decision this leaves open.

**RESOLUTION TRACE:** statement lines 1636–1643; proof line 1696 (“(a) displayed arithmetic + consumptions”); the frames 1375–1386 (`.06`); the literature declaration 565–576 (shard 1 `.39`); correction site 3267–3312 (E-4).

XREF: `docs/references/HigherNewton.tex:propertiesv` — grep-verified count **8**.
XREF: `GRTJA_PROOF_2026-08-08.md:JA-PIN` — **15** · `JA-VAL` — **7**.

**TEETH:** `jb_vtx`/`jb_shear_vtx` — **IND, 893 samples**: print ordinates (`G.vgen`/`G.vkey`) against harness ordinates (`T.wlev`/`T.gam`), i.e. **two engines, not two code paths of one**.

---

### EFF.GRTJB.s2of3.22  [lemma]  JB-VTX (b) — vertex-for-vertex

**CANONICAL STATEMENT:** verbatim, lines 1645–1650.
**FORM:** bold clause label + paragraph.

> “**(b) [vertex-for-vertex].** By (a) and JB-AFF, the harness development
> polygon (lower hull of H(f)) equals Σ_q(N_{q+1}(f)) vertex-for-vertex,
> same abscissas; equivalently N_{q+1}(f) = Σ_q^{−1}(harness polygon). This
> is GD-2's displayed clause with the shear EXPLICIT. The unsheared
> identification (hull of {(i, w_q(A_i))} against N_{q+1}(f)) is FALSE in
> general — the T-F 7,472-violation genre; teeth family MJB-VTX.”

**CONDITIONALITY:** `P<q` + W2-C1, via (a) (matrix row 9). **The “FALSE in general” here is NOT the claim E-4 withdraws** — E-4 targets only the off-perimeter negation about (VAL)/(a); this one is a MEASURED fact about the unsheared identification, backed by 7,472 counted violations (`.07`) and by the note's own teeth family. **The two negations must not be conflated at the merge.**

**DERIVATION:** (a) + LEMMA JB-AFF, which applies because `Σ_q(i,u) = (i, e_q·u + h_q·i)` has `a = e_q > 0`, `b = h_q`, `c = 0` and is abscissa-preserving.

**RESOLUTION TRACE:** statement lines 1645–1650; proof line 1696 (“(b) JB-AFF”); the lemma 1615–1621 (`.19`); the measurement 1388–1396 (`.07`).

XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — **7**.
XREF: `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md:7,472` — count **2** (figure pin, re-verified at the source by this compiler).

**TEETH:** `jb_vtx` — **fresh lower hulls of BOTH frames + the vertex bijection (IND, 893)**; plus planted mutant **MJB-VTX** (unsheared frame, 3/3 caught, fired).

---

### EFF.GRTJB.s2of3.23  [lemma]  ★ JB-VTX (c) — slope/length translation (the E-3 target)

**CANONICAL STATEMENT:** verbatim, lines 1652–1663.
**FORM:** bold clause label + paragraph.

> “**(c) [slope/length translation].** A print side of slope σ over abscissas
> [i₀, i₁] maps to a sheared side of slope e_q·σ + h_q over the same
> [i₀, i₁]; lengths (abscissa runs) are preserved. In particular:
> the REALIZED side σ = −h_q/e_q maps to slope 0 — the sheared frame is the
> frame in which the read side is HORIZONTAL, at height
> min_i(e_q·w_q(A_i) + i·γ_{q+1}) = w_{q+1}(f) — exactly the eq-(12)
> presentation of the level-(q+1) read; a side of print slope −h/e in lowest
> terms has its lattice data preserved: degree d = (abscissa run)/e is the
> same integer in both frames (the print's d(S) = the harness grid count).
> The print principal part N^−_{q+1} (σ < 0, tex 1377) corresponds to
> sheared slopes < h_q; the weld's type-quantification consumes only the
> principal sides (JA-PIN clause 2's Hensel/L1 dispatch, displayed there).”

**CONDITIONALITY — ★ THE ONE DISPLAYED MATHEMATICAL STATEMENT OF §§1–6 THAT A LATER ANNEX WITHDRAWS IN PART.** CERTIFIER ANNEX **E-3** (shard 3, L3199–3228) supersedes the “lattice data preserved” sentence:

> “**E-3 (JB-VTX(c): abscissa run, not ambient lattice data).** The sentence in
> §3(c) saying that the shear “preserves lattice data” is WITHDRAWN. The shear
>
>     Σ_q(i,u) = (i, e_q·u + h_q·i)
>
> is not unimodular when e_q > 1. For an edge with difference vector
> (Δi, Δu), its image has difference vector
>
>     (Δi, e_q·Δu + h_q·Δi),
>
> so the abscissa run Δi is preserved and the slope transforms by
>
>     σ′ = e_q·σ + h_q,
>
> but the ambient-lattice primitive step and lattice length need not be
> preserved. For example, at (e_q,h_q) = (2,1), the edge from (0,1) to (2,0)
> maps to the horizontal edge from (0,2) to (2,2), whose ambient lattice
> contains the additional point (1,2).”

**THE CORRECTED DISPLAY, verbatim from E-3:**

> “**CORRECTED DISPLAY OF JB-VTX(c).** A print side of slope σ over
> [i₀,i₁] maps to a sheared side of slope e_q·σ+h_q over the same
> [i₀,i₁]; hence its abscissa run Δi := i₁−i₀ is preserved. If the source
> slope is −h/e in lowest terms, its PRINT-side degree remains the
> source-defined integer d := Δi/e and is recoverable from the preserved run
> together with the source slope data. This does NOT say that d is the ambient
> lattice length of the sheared edge. On the realized side, identifying d with
> a count of e_q-spaced attained-grid intervals is instead a consequence of
> JB-VTX(d4), and therefore carries row 12's full scope: the `P<q` and W2-C1
> fences, together with the narrowed lattice-membership/u ≥ 0 residue and its
> NO-MACHINE-LEG disclosure.”

**SUPERSESSION KIND:** `replacement` — a false extension removed and the display re-issued. **TARGETS (rule 24):** `s2of3.23` (this unit), `s2of3.27` (the §3 ∎ GRADE surface), `s1of3.20` row 10 (“re-read as ‘JB-VTX(c), slope/abscissa-run’”), `s1of3.32` (the grade cap's JB-VTX bullet), `s3of3` §7.2's JB-VTX row and §7.3's W-3 polygon bullet.

**★ THE LOAD-BEARING CONSEQUENCE, and the merge must carry it:** every use of an attained-slot or harness-grid COUNT is **routed to JB-VTX(d4) = matrix row 12** — which is a **frontier cell** (`NONE` evidence + the membership residue). So E-3 does not merely trim a claim; **it moves a downstream consumption onto the note's weakest row.** E-3's own consumer sweep says so: “Every use of an attained-slot or harness-grid count is routed to JB-VTX(d4), §0M row 12. Its existing membership residue and NO-LEG status therefore remain visible; the four-member frontier is unchanged.”

**What E-3 explicitly does NOT disturb (quoted):** “The §3 proof and the `hull_sides` machine leg survive unchanged: they establish slope transformation and equality of endpoint abscissas/runs, not unimodularity.” And: “No hull, vertex, slope, abscissa-run, JB-TREE or JB-CREAD identity moves. Only the false ambient-lattice extension is removed.”

**Orchestrator verification of E-3, quoted from the transcription record (L3316–3320):** “E-3's shear algebra re-derived (image difference vector (Δi, e_qΔu + h_qΔi), slope law σ′ = e_qσ + h_q, the (e_q,h_q) = (2,1) witness maps (0,1)–(2,0) to the horizontal (0,2)–(2,2) containing (1,2): abscissa run preserved, ambient lattice data not)”.

**DERIVATION (as corrected):** displayed arithmetic. From `Σ_q(i,u) = (i, e_q u + h_q i)`, an edge `(Δi, Δu)` maps to `(Δi, e_q Δu + h_q Δi)`: the abscissa run is preserved and the slope transforms as stated. The realized side `σ = −h_q/e_q` maps to slope `0`, at height `min_i(e_q w_q(A_i) + i γ_{q+1}) = w_{q+1}(f)`. **The withdrawn step was the inference from “run preserved” to “ambient lattice data preserved”, which fails at `e_q > 1` because `Σ_q` is not unimodular.**

**RESOLUTION TRACE:** statement lines 1652–1663; proof line 1696 (“(c)(d) displayed arithmetic + the cited print lemmas”); **correction site 3199–3245 (E-3)**; the routed consumer 1665–1680 (`.24`, clause (d4)).

XREF: `docs/references/HigherNewton.tex:defresidual` — **1**; the `N^−` principal-part pin (tex 1377) is a LINE PIN verified present. `GRTJA_PROOF_2026-08-08.md:JA-PIN` — **15**.

**TEETH:** `jb_vtx` — `hull_sides` per-side slope/length law (**IND, 893**). **The leg survives E-3 unchanged because it only ever measured what E-3 keeps** — a case where the instrument was scope-correct and the prose over-reached. Disposition: **executable regression, scope-matched after correction**; the correction itself is an **AUDIT — decorrelated-model audit** (a sol certification run found it).

---

### EFF.GRTJB.s2of3.24  [lemma]  JB-VTX (d) — the four min/read ties

**CANONICAL STATEMENT:** verbatim, lines 1665–1680.
**FORM:** bold clause label + paragraph with a nested `[r6, F-1]` rider.

> “**(d) [min/read ties].** min ordinate of U(f) = v_{q+1}(f) (print Lemma
> `shape` item 1, tex ~1395); min ordinate of H(f) = w_{q+1}(f) = v_{q+2}(f)
> (the weight recursion + JA-VAL one level up) **[r6, F-1 — "one level up" made
> binding: this third tie (d3) is JA-VAL AT LEVEL q+1, so by J-A's
> level-indexed perimeter it holds on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`),
> NOT on the bare shared-key perimeter `P<q` the theorem head states — one
> level deeper, exactly as (RES) (r3/F-4); the exclusion bites at q = qcap on
> the 5 shared_upto < n towers. The representative-pin rescue (arguing the
> frame's own pin φ_{q+1} := Φ_q^har discharges J-A's j = q requirement) is
> NOT taken: it is not derived anywhere in this note — the same refusal
> recorded at (RES). §0M row 11 (a2)]**; the attained abscissas on
> the realized side are the read grid s(λ) + j·e_q, and the level-(q+1)
> read is assembled exactly from the on-line digits at those slots (S0.2
> consumed; JA-GRID). So the polygon identity carries the READ data — the
> harness read of f and the print's side data (s_{q+1}(f), attained set,
> side degree) are the same integers under Σ_q.”

**`[TABLE]` — the four ties, split as the note splits them (matrix rows 11 and 12):**

| tie | statement | fence | machine leg |
|---|---|---|---|
| **(d1)** | min ordinate of `U(f) = v_{q+1}(f)` (print Lemma `shape` item 1, tex ~1395) | `P<q` + W2-C1 | **IND**, `minU == G.vgen(q+1,f)` under `q ≤ shared_upto` — **an instrument cut, not the statement's hypothesis** (r6, F-1) |
| **(d2)** | min ordinate of `H(f) = w_{q+1}(f)` | `P<q` + W2-C1 | **IND**, `minH == T.wlev(q+1,f)` (harness-internal) |
| **(d3)** | `w_{q+1}(f) = v_{q+2}(f)` — JA-VAL **at level q+1** | **`P≤q`** + W2-C1 (r6, F-1); bites at `q = qcap` on T3A/T3C/T3D/T3E/I4C | **IND**, `minH == G.vgen(q+2,f)`; the runner's `q ≤ shared_upto` gate **IS** this fence, so the leg covers the full re-fenced range |
| **(d4)** | attained abscissas on the realized side = the read grid `s(λ) + j·e_q`, and the level-(q+1) read is assembled from the on-line digits at those slots | `P<q` + W2-C1 **AND** JA-GRID(a)'s `u ≥ 0` proviso (narrowed r5/F-3) | **NONE — no leg in any family of any instrument** |

**SUPERSESSION KIND:** `scope-pin` (the r6 re-fence of (d3) alone).

**CONDITIONALITY:** **(d4) is the note's most heavily fenced sub-clause and one of its four frontier cells**: it rides the open membership residue AND has zero machine evidence, and the note discloses the coincidence explicitly. **E-3 routes every attained-slot/harness-grid COUNT here** (`.23`), which strengthens (d4)'s downstream load without strengthening its evidence. **The representative-pin rescue is refused, binding on r3/F-4's precedent.**

**DERIVATION:** (d1) is print Lemma `shape` item 1 (`min_i u_i = v_r(f)`). (d2)–(d3) are the weight recursion plus JA-VAL one level up. (d4) is S0.2's read assembly plus JA-GRID. Proof line: “(c)(d) displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is also re-verified by machine through the second development route — see runner family JB-SHEAR)”.

**RESOLUTION TRACE:** statement lines 1665–1680; proof lines 1696–1699; matrix rows 11, 12 at 305–306 (shard 1); the cell note ⟨n3⟩ 347–368 (shard 1 `.23`); the r6 disposition 1127–1163 (shard 1 `.73`); the `u ≥ 0` chain home 218–250 (shard 1 `.14`).

XREF: `docs/references/HigherNewton.tex:shape` — grep-verified count **13** (NS-11 retarget: **[GN15] Lemma 1.5 + Corollary 1.14**, COVERS-ALL-O — see `.21`).
XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.2` — **5**. `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11**.

**TEETH:** three keyed, **(d4) unkeyed**. Quoted coverage-hole sentence (from ⟨n3⟩): “Clause (d)'s FOURTH tie … **has no leg in any family**”. **PROOF-ONLY row (rule 16).** The (d3) gate was byte-verified at HEAD by this compiler (`grt_jb_checks.py` L283).

---

### EFF.GRTJB.s2of3.25  [lemma]  JB-VTX (e) — the window clause, subject corrected

**CANONICAL STATEMENT:** verbatim, lines 1682–1694.
**FORM:** bold clause label + struck sentence + `[r1, G-4]` replacement.

> “**(e) [window clause].** ~~Restricted to the junction window i ≤ e_q·g_q
> (the lift comparison window), one-sidedness holds in both frames
> simultaneously (Σ_q preserves sides)~~ **[r1, G-4 — SUBJECT CORRECTED. As
> literally read with the theorem's quantified f the struck sentence is FALSE
> (a general f's polygon restricted to i ≤ e_q g_q is not one-sided). The
> clause's subject is the KEY, and it reads: APPLIED AT f = Φ_{q+1}^har (the
> next-level lift, whose window development is the W2-C1a object), restricted
> to the junction window i ≤ e_q·g_q, one-sidedness holds in both frames
> simultaneously (Σ_q preserves sides, LEMMA JB-AFF)]**: this is W2-C1a's
> polygon leg —
> v-correct, one-sided, support {0, e_q g_q} ∪ attained grid slots — i.e.
> the "window polygon" of the blueprint IS N_{q+1}(Φ_{q+1}^har) restricted
> to its single side, vertex-for-vertex under Σ_q.”

**SUPERSESSION KIND:** `replacement` — a clause whose stated subject made it FALSE, re-issued with the true subject.

**CONDITIONALITY:** **The subject is the KEY `Φ_{q+1}^har`, NOT the theorem's quantified `f`** (matrix row 13: “subject is the KEY, not the quantified f (r1, G-4)”). Fence: `YES*` via (a) at `f = Φ_{q+1}^har`, plus **W2-C1a**. **Row 13 is a no-leg cell ADJUDICATED OUT of the frontier** (r4/F-2): no-leg but no OPEN proviso — its conditionality is consumption at grade.

**DERIVATION:** W2-C1a consumed at `f = Φ_{q+1}^har` (proof line 1699), plus `Σ_q` preserving sides by LEMMA JB-AFF.

**RESOLUTION TRACE:** statement lines 1682–1694; proof line 1699; the disposition 678–679 (shard 1 `.47` item G-4); matrix row 13 at 307 (shard 1); the frontier exclusion 959–967 (shard 1 `.59`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C1a` — **10**.

**TEETH:** **NONE (none claimed)** — matrix row 13's own (f) cell. Disposition: **signed non-applicability**, adjudicated out of the frontier with the reason displayed.

---

### EFF.GRTJB.s2of3.26  [changes-record]  (JB-VTX — the proof and the struck grade line)

**CANONICAL STATEMENT:** verbatim, lines 1696–1712.
**FORM:** `*Proof.*` marker + a struck grade line with a nested `[r2, G2-1]` re-grep rider.

> “*Proof.* (a) displayed arithmetic + consumptions; (b) JB-AFF; (c)(d)
> displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is
> also re-verified by machine through the second development route — see
> runner family JB-SHEAR); (e) W2-C1a consumed at f = Φ_{q+1}^har (r1, G-4).
> ~~∎ Grade: PROVED at attempt grade **[r1, G-9] on the shared-key perimeter
> 0 ≤ q ≤ qcap …** … **[r2, G2-1
> re-grep — one fence this line was missing: clause (d)'s read-grid/attained-
> abscissa content consumes JA-GRID, so it also rides JA-GRID(a)'s UNDISCHARGED
> `[JA-r1]` u ≥ 0 proviso (r2, G2-5; carried in JB-BOX-2). Clauses (a)/(b)/(c)
> and the min ties themselves do not.]**~~”

**CONDITIONALITY:** The grade line is **STRUCK and superseded by surface 3** (`.27`). The PROOF is live. **The r2 re-grep rider inside it is the first statement that (d4) alone rides the proviso** — a separation surface 3 then carries.

**DERIVATION:** This unit IS the proof: five one-line discharges. Note the machine cross-check embedded in it — Lemma `shape` item 1 is “re-verified by machine through the second development route”, i.e. `v_{q+1}(f)` computed BOTH as `min u_i` and by the vgen recursion.

**RESOLUTION TRACE:** statement lines 1696–1712; the superseding surface 1714–1747 (`.27`).

**TEETH:** carried by the clauses; the `shape` item 1 double-computation is `jb_shear_vtx`'s (d1) leg.

---

### EFF.GRTJB.s2of3.27  [TABLE]  ★ SURFACE 3 of 14 — the §3 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1714–1747.
**FORM:** bold-headed bracketed block + fixed-width per-clause display.

> “**[r3, STEP 2 — SURFACE 3 of 14, REGENERATED FROM §0M rows 7–13. ∎ GRADE:
> PROVED at attempt grade on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap,
> stated at the theorem), every statement at the W2-C1 admissible representative
> φ_{q+1} := Φ_q^har — W-2 clause 1's perimeter and conditionality ride, and on
> byte-equal chains no W-2 input is needed beyond TH-BASE. PER CLAUSE:**
>
>     LEMMA JB-AFF  unconditional, two lines; its content is exercised inside
>                   (b)/(c)'s machine legs.                        [row 7]
>     (a)(b)(c)     `P<q` + W2-C1 only; off `P<q` clause (a)'s JA-VAL input is
>                   unavailable and (a) is FALSE, not merely unproved.
>                                                             [rows 8–10]
>     (d1)(d2)      two of the THREE min ties: `P<q` + W2-C1; the runner
>                   restricts the print-side tie (d1) further to
>                   q ≤ `shared_upto(T,G)` — an instrument cut (r6, F-1).
>                                                         [row 11 (a1)]
>     (d3)          w_{q+1}(f) = v_{q+2}(f) = JA-VAL at level q+1: the
>                   BYTE-EQUAL CHAIN THROUGH q (`P≤q`) + W2-C1 — one level
>                   deeper than the r3 fence, the r3/F-4 genre; bites at
>                   q = qcap on the 5 shared_upto < n towers; the runner's
>                   own q ≤ `shared_upto(T,G)` gate on (d3) IS this fence
>                   (r6, F-1).                            [row 11 (a2)]
>     (d4)          attained abscissas = the read grid s(λ) + j·e_q, and the
>                   level-(q+1) read assembled from the on-line digits at those
>                   slots: `P<q` + W2-C1, **AND JA-GRID(a)'s UNDISCHARGED
>                   `[JA-r1]` u ≥ 0 proviso** (r2, G2-5; JB-BOX-2; narrowed
>                   r5/F-3: PROVED at deg f < deg Φ_{q+1}, membership residue
>                   off it — §5), **AND it has
>                   NO MACHINE LEG** (r3, F-3).                   [row 12]
>     (e)           at f = Φ_{q+1}^har, the W2-C1a window object — NOT at the
>                   theorem's quantified f (r1, G-4); no machine leg claimed.
>                                                                 [row 13]
>
> **The runner runs the shear/vertex/slope families over 0 ≤ q ≤ `qcap_of(T,G)`
> and the off-perimeter counter is 0 on the roster, so nothing was silently
> scored outside the fence.]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating row |
|---|---|---|
| **JB-AFF** | unconditional, two lines; content exercised inside (b)/(c)'s legs | row 7 |
| **(a)(b)(c)** | `P<q` + W2-C1 only — ~~off `P<q` (a) is FALSE, not merely unproved~~ **→ E-4: NOT SUPPLIED outside the stated perimeter**; **(c) → E-3: “slope/length” reads “slope/abscissa-run”** | rows 8–10 |
| **(d1)(d2)** | `P<q` + W2-C1; the runner's `q ≤ shared_upto` on (d1) is **an instrument cut** | row 11 (a1) |
| **(d3)** | **`P≤q`** + W2-C1 (r6/F-1); bites at `q = qcap` on 5 towers; the runner's gate **IS** this fence | row 11 (a2) |
| **(d4)** | `P<q` + W2-C1 **AND** the `u ≥ 0` proviso (narrowed r5/F-3) **AND NO MACHINE LEG** | row 12 |
| **(e)** | at `f = Φ_{q+1}^har`, the W2-C1a window object — NOT at the quantified `f`; no leg claimed | row 13 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 7–13** (FREEZE PREDICATE 2). **TWO shard-3 corrections land on it:** E-4 (the negation clause in the (a)(b)(c) row; its consumer sweep item 2 names “§3 ∎ Grade”) and E-3 (“The grade cap, **§3 ∎ Grade surface**, §7.2's JB-VTX row and §7.3's W-3 polygon bullet read every occurrence of ‘slope/length’ as ‘slope/abscissa-run’”).

**ARITHMETIC AUDIT (rule 22):** clause groups listed = 6; generating rows cited = 7, 8–10, 11(a1), 11(a2), 12, 13 → **rows 7,8,9,10,11,12,13 = 7 rows, contiguous, no gaps, no repeats** ✔ matches “§0M rows 7–13”. Row 11 appears twice, once per sub-column, which is exactly the r6 SPLIT ✔. **Cross-check against §0M rows 7–13: every non-blank cell appears in the surface, and every fence in the surface is a cell. VERIFIES.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1714–1747; generating rows 301–307 (shard 1 `.20`); correction sites 3199–3245 (E-3), 3267–3312 (E-4); the r6 re-fence 1127–1163 (shard 1 `.73`).

**TEETH:** per row; **(d4) is PROOF-ONLY**; row 13 no-leg by design.

---

### EFF.GRTJB.s2of3.28  [instrument-record]  (JB-VTX — the machine bracket, restated at r3/F-3)

**CANONICAL STATEMENT:** verbatim, lines 1748–1778 — the struck r0 bracket and the `[r3, F-3]` replacement with its `[r7, m-3]` and `[r5, F-3]` riders.
**FORM:** struck display + bold-headed bracketed replacement.

> “~~[Machine: JB-VTX — fresh lower hulls of both
> frames, vertex bijection, per-side slope/length translation; JB-SHEAR —
> pointwise shear + all four min/read ties …]~~
>
> **[r3, F-3 — MACHINE BRACKET RESTATED; "all four min/read ties" is WITHDRAWN.
> [Machine, classified as in §0M column (f): JB-VTX — fresh lower hulls of BOTH
> frames, vertex bijection, per-side slope/length translation (IND, 893).
> JB-SHEAR — the pointwise shear plus **THREE** of clause (d)'s four ties, not
> four: the code's assertions are `minH == T.wlev(q+1, f)` (d2) and, under
> q ≤ shared_upto, `minU == G.vgen(q+1, f)` (d1) and `minH == G.vgen(q+2, f)`
> (d3) ((d3) additionally under the code's second conjunct `q+1 <= G.RANK`, a
> vgen-domain guard, identically true on the loop domain since
> RANK = n+1 ≥ qcap+1 — verified redundant [r7, PE7 m-3, commit aa9b603];
> ⟨n3⟩) **[r6, F-1 — for (d3) that gate coincides with its own statement fence
> `P≤q` (§0M row 11 (a2)); for (d1) it remains an instrument cut]** — so
> v_{q+1}(f) IS computed both as min u_i and by the vgen recursion
> through the φ_q-development (two different developments, one value; Lemma
> `shape` item 1 machine-keyed). **THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY
> OF ANY INSTRUMENT:** `jb_dev` keys only the (VAL) weight tie, `jb_line` keys
> line == wlev == vgen on reduced cells, `jb_cread` evaluates (VD-m), and
> `jb_eps` keys JA-GRID's **carry** clause (c) — the other half of the (GRID)
> layer, and the half that carries no proviso. **Disclosed coincidence:** (d4) is
> also the only sub-clause of JB-VTX riding the undischarged u ≥ 0 proviso
> **[r5, F-3 — narrowed to the membership residue, §0M column (b) and §5]**, so
> the clause with the open inherited hypothesis is the clause with zero machine
> evidence (§0M row 12; the same disclosure genre as r1/G-3's three VACUOUS
> JB-KEYEQ rows). teeth MJB-VTX on designated rows (unsheared frame, 3/3
> caught).]]**”

**SUPERSESSION KIND:** `counter re-reading` (four ties recounted to three keyed) + `inventory completion` (r7/m-3's second conjunct disclosed).

**CONDITIONALITY:** **The exhaustiveness of the no-leg claim is what makes it strong**: the note enumerates ALL FOUR families and shows none keys (d4). **E-3 does not touch this bracket** — “the `hull_sides` machine leg survive[s] unchanged”.

**PIN VERIFICATION (rule 23) — re-verified at HEAD by this compiler, 3/3 EXACT:** `verification/openmath/grt_jb_checks.py` **L283** = `                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):` — **byte-exact**; `grt_weld_probe.py` **L211** = `        self.RANK = len(levels)`; `grt_weld_probe.py` **L456–459** = `gmn_from_tower` building `levels` over `range(T.NR)`. **So `RANK = T.NR` and the redundancy derivation is source-true.** (Source defect 5 of shard 1 stands: the note gives the two line pins without naming their file, which is `grt_weld_probe.py`.)

**DERIVATION:** Code enumeration.

**RESOLUTION TRACE:** statement lines 1748–1778; the cell note ⟨n3⟩ 347–368 (shard 1 `.23`); the disposition 905–908 (shard 1 `.55`); the m-3 sweep 1259–1271 (shard 1 `.79`); the §7.1 JB-SHEAR row 2482 (shard 3).

**TEETH:** three IND tie legs + a **PROOF-ONLY** fourth + planted mutant **MJB-VTX** (fired) + a **signed vacuity disclosure** cross-referenced to JB-KEYEQ's three vacuous rows.

---

### EFF.GRTJB.s2of3.29  [hypothesis]  §4 setting

**CANONICAL STATEMENT:** verbatim, lines 1784–1788.
**FORM:** inline paragraph.

> “Setting: reduction level m (1 ≤ m ≤ n), [RMG] T-scope(m) (its termination
> fence), g_m = 1, Ĉ_m := Φ_{m+1} − Φ_m^{e_m} (WELL-DEF g_m = 1 form,
> consumed); f ∈ O[x] nonzero, deg f < deg Φ_m. The [RMG] S2.2 objects
> (cells, (ID-(i+1)), the E1-priority tree, L-NORM splits, L-EXACT, L-CANON,
> L-LINE) are consumed as ACCEPTED displays.”

**CONDITIONALITY:** **Three standing scope fences enter here and ride every §4 clause:** `T-scope(m)` ([RMG]'s termination fence, with the d₀ ≥ 2 flat corners staying FENCED), `g_m = 1` (for the Ĉ_m instance), and `deg f < deg Φ_m`. **The degree bound is the hypothesis whose scope r5/F-2 later had to enforce** (`.33`) and whose absence off the sub-window is the `u ≥ 0` membership residue (`.14`, `.42`).

**DERIVATION:** Declaration of setting.

**RESOLUTION TRACE:** statement lines 1784–1788; the boxes 2427–2433 (`.59`); the degree-bound scope enforcement 1832–1851 (`.33`).

XREF: `RMENGINE_2026-08-08.md:T-scope` — **42** · `S2.2` — **16** · `(ID-(i+1))` — **3** · `L-NORM` — **28** · `L-EXACT` — **11** · `L-CANON` — **6** · `L-LINE` — **23** · `L-CELL` — **11**.
XREF: `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` — **32**.

**TEETH:** the scope is a filter on the roster: “I4C has NO eligible (g_m = 1 ∧ T-scope) reduction level, so its tree/cread rows are honestly absent, the §4 scope fence in action” (§7.1, shard 3).

---

### EFF.GRTJB.s2of3.30  [lemma]  THEOREM JB-TREE — head

**CANONICAL STATEMENT:** verbatim, lines 1790–1791.
**FORM:** bold-headed opener.

> “**THEOREM JB-TREE.** Under the J-A dictionary (and W-2 clause 1 for the
> representative reading; clause 3's chamber off the byte perimeter):”

**CONDITIONALITY:** **E-2 re-reads the clause-3 (W2-C3) half** at the supplier's proved-to-first-twist (38/44) / measured-above (6/44) split; the 2026-08-08 annex confirms GRTW2 ACCEPTED at 2/2 **at that honest split** — “Acceptance of W-2 accepts the honest box; it does not turn its measured-above region into a theorem” (the E3 adjudication's finding 3, shard 3).

**DERIVATION:** Head; the clauses are `.31`–`.35`.

**RESOLUTION TRACE:** statement lines 1790–1791; correction sites 3135–3142 (E-2), 3247–3261 (the E3 adjudication's RESOLVED-ALREADY item, shard 3).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C3` — **22** · `W2-OPEN-2` — **60**.

**TEETH:** per clause.

---

### EFF.GRTJB.s2of3.31  [lemma]  JB-TREE (i) — the tree computes the classifier's division

**CANONICAL STATEMENT:** verbatim, lines 1793–1801.
**FORM:** bold clause label + paragraph.

> “**(i) [the tree computes the classifier's division].** The E1-priority
> tree on the initial cells of f·Ĉ_m terminates (T-TERM, consumed) with
> Σ R-leaves = R and Σ exit cofactors = Q for THE canonical division
> f·Ĉ_m = R + Q·Φ_m (L-EXACT + L-CANON, consumed) — and by JB-DEV(i) at
> level m this IS the classifier's division step at the admissible
> representative (its own key on byte-equal chains): R = the 0-th digit and
> Q = the once-divided cofactor of the print's φ_{m+1}-adic development
> algorithm applied to f·Ĉ_m. One tree = one classifier division step,
> executed inside the expansion arithmetic.”

**CONDITIONALITY:** **PERIMETER-FREE** (matrix row 15) — “it consumes JB-DEV(i), which holds at every q”. Fences: W2-C1 representative reading, W2-C3's chamber off the byte perimeter, and [RMG]'s T-TERM + L-EXACT + L-CANON on T-scope(m), g_m = 1. **L-CANON's hypothesis `deg Ĉ_m < deg Φ_m` is one of the two clauses r3/F-5 restored to §5's recital** (`.39`) — before r3 the note cited L-CANON without displaying the hypothesis that makes the division canonical.

**DERIVATION:** Consumption chain as displayed + JB-DEV(i) (proof line 1905).

**RESOLUTION TRACE:** statement lines 1793–1801; proof line 1905; the restored L-CANON hypothesis 2015–2023 (`.39`); matrix row 15 at 309 (shard 1).

XREF: `RMENGINE_2026-08-08.md:T-TERM` — **11** · `L-EXACT` — **11** · `L-CANON` — **6**.

**TEETH:** `jb_tree` — a FRESH from-note tree walker vs `fresh_divmod` (**IND**), **plus** the post-seal walker's leg A (84 print-keyed walks, genuinely decorrelated), **plus a SAME sub-leg** (⟨n2⟩: the byteeq-gated print-key re-execution), **and 8 chamber walks NONE** (unreached by both instruments). Disposition: **accepted-with-decorrelation-supplied** on base rows; **disclosed non-repair** for the chambers.

---

### EFF.GRTJB.s2of3.32  [definition]  the period `P_i` (r3/F-7)

**CANONICAL STATEMENT:** verbatim, lines 1803–1819 (through “same sense.]**”).
**FORM:** bold clause label + bracketed definition with a fixed-width display.

> “**(ii) [each edge = one classifier division step].** **[r3, F-7 — NOTATION,
> DEFINED HERE AT FIRST USE (it was used undefined in r0–r2, and it is
> load-bearing for the digit-list claim below).**
>
>     P_i := e_i · g_i     — the level-(i+1) PERIOD: the abscissa at which the
>                            key power Φ_i^{P_i} sits in the Φ_i-adic
>                            development of Φ_{i+1}. Verbatim from [RMG] S0.1
>                            ("P_l := e_lg_l (the level-(l+1) period)"), whose
>                            scope is declared "local to this note" there and
>                            which is therefore added to this note's [RMG]
>                            consumption list in the header.
>
> **The value is what the proof of (ii) turns on: every correction abscissa
> e_i·k with k < g_i satisfies e_i·k < e_i·g_i = P_i, so the digit list below is
> supported below the key power and the Φ_i-adic development reads off
> uniquely. §7.4's PW-ID and PW-WALK rows use the same symbol (and P_l) in this
> same sense.]**”

**SUPERSESSION KIND:** `inventory completion` — a symbol consumed uncited, defined and its source added to the consumption list.

**CONDITIONALITY:** **[RMG] S0.1 scopes `P_l` “local to this note”** — so consuming it required adding S0.1 to GRTJB's consumption list, which r3/F-7 did. **`P_i` is also the object the `𝒲_m` description's index bound `0 ≤ j_l ≤ P_l − 1` uses** (`.40`) and the object the r7 m = 1 equivalence's `j := s ≤ e₀−1 ≤ P₀−1` step uses (shard 1 `.77`).

**DERIVATION:** Definition + the one-line consequence displayed: `e_i·k < e_i·g_i = P_i` for `k < g_i`, so the digit list is supported below the key power and the `Φ_i`-adic development reads off uniquely.

**RESOLUTION TRACE:** statement lines 1803–1819; the disposition 911–912 (shard 1 `.55` STEP 4); the consumption-list addition 577–581 (shard 1 `.40`); consumed at 1819–1829 (`.33`), 2031 (`.40`), and §7.4's PW-ID/PW-WALK rows (shard 3).

XREF: `RMENGINE_2026-08-08.md:S0.1` — grep-verified count **12**.

**TEETH:** exercised by `jb_id` (the digit list) and by the post-seal walker's PW-WALK row (“every R-leaf reduced (`j_l ≤ P_l − 1`)”, 84 samples GREEN).

---

### EFF.GRTJB.s2of3.33  [lemma]  JB-TREE (ii) — each edge = one division step, with the L-CELL gloss corrected

**CANONICAL STATEMENT:** verbatim, lines 1819–1851 — the (ID-(i+1)) reading, the edge typing, and the struck L-CELL gloss with its `[r5, F-2]` replacement.
**FORM:** paragraph + struck sentence + bracketed replacement.

> “The identity
> (ID-(i+1)): Φ_i^{P_i} = Φ_{i+1} − Σ_{k<g_i} C_k^{(i)}·Φ_i^{e_ik} IS the
> statement that the φ_{i+1}-adic development of the KEY φ_{i+2} = Φ_{i+1}
> has digit list {C_k^{(i)} at abscissa e_i·k (k < g_i), 1 at abscissa P_i}
> (uniqueness of division; the C_k^{(i)} are reduced, REALIZE R1). So every
> in-tree edge applies the classifier's own key-expansion relation exactly
> once: a promotion edge carries one key power up one level (the division
> algorithm's carry), a Φ_m-exit emits one quotient summand (a division
> step's quotient write), and a correction edge substitutes the key's lower
> development digits (the remainder write), L-NORM-split into its L/π-junk/
> Φ₀Y-junk children. The tree is the classifier's division arithmetic made
> cell-local; ~~the blueprint's "each cell = a set of expansion slots" is
> L-CELL: every node is a sum of reduced cells = multiadic expansion slots
> (iterated JB-DEV at levels m−1, …, 0).~~ **[r5, F-2 — the struck gloss is
> FALSE at every exit-bound node, and its citation was used beyond L-CELL's
> stated hypothesis: L-CELL(i) decomposes 0 ≠ x with deg x < deg Φ_m ONLY,
> while a node taking a Φ_m-exit has j_{m−1} ≥ P_{m−1} (S2.2, "Φ_m-exit
> (i = m−1)"), hence deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m by the S2.1 degree
> telescope — and a sum of reduced cells has deg < deg Φ_m (S2.1), so such a
> node is not a sum of reduced cells at all. THE TRUE STATEMENT: the
> blueprint's "each cell = a set of expansion slots" is L-CELL(i) ON ITS OWN
> HYPOTHESIS — every node OF DEGREE < deg Φ_m is a finite sum of distinct
> reduced cells = multiadic expansion slots (iterated JB-DEV at levels
> m−1, …, 0); an exit-bound node decomposes below the top level instead
> ([RMG] S2.2's structural remark: its sub-cell b·∏_{l≤m−2}Φ_l^{j_l} is
> REDUCED AT LEVEL m−1); and the R-LEAVES — where the division's output
> lives, and the only reducedness `jb_tree` keys — are the expansion slots in
> the blueprint's sense. The same L-CELL(i) hypothesis scope reads onto the
> r4/F-4 bracket's min-line parenthetical below (its bound line ≤ w_m is
> supplied where the reduced decomposition exists, deg < deg Φ_m). Nothing
> downstream consumed the struck gloss: (ii)'s operative content — the edge
> typing and JB-ID — was re-derived SOUND (PE5), and clauses (i)/(iii)/(iv)
> consume L-EXACT/L-CANON/JA-VAL, not this sentence.]**”

**SUPERSESSION KIND:** `scope-pin` — a citation used beyond its stated hypothesis, re-scoped to that hypothesis.

**CONDITIONALITY:** **PERIMETER-FREE** (matrix rows 14, 16) — uniqueness of division at the print's own keys. **The corrected gloss is a genuine mathematical narrowing**, and the note verifies nothing downstream consumed the false form. **The same hypothesis scope reads onto the r4/F-4 min-line parenthetical** (`.34`) — one correction, two sites.

**DERIVATION:** (a) The (ID-(i+1)) reading: “the right side of (ID-(i+1)) has every `C_k^{(i)}Φ_i^{e_ik}` of degree < deg Φ_{i+1} with the `C_k` reduced (REALIZE R1), so the digit list reads off; uniqueness of division” (proof lines 1906–1908). (b) The r5/F-2 refutation is displayed: an exit-bound node has `j_{m−1} ≥ P_{m−1}`, hence `deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m` by the S2.1 degree telescope, while a sum of reduced cells has `deg < deg Φ_m` — so it cannot be one.

**RESOLUTION TRACE:** statement lines 1819–1851; proof lines 1906–1908; the disposition 1080–1088 (shard 1 `.69`); matrix rows 14, 16 at 308, 310 (shard 1).

XREF: `RMENGINE_2026-08-08.md:(ID-(i+1))` — **3** · `L-CELL` — **11** · `L-NORM` — **28** · `S2.1` — **15** · `S2.2` — **16**.
**NEAR-MISS (rule 15) — `REALIZE R1`:** fixed-string `REALIZE R1` has count **0** in `ITERLAWN_PROOF_2026-08-08.md`; the parent designation `REALIZE` has count **17** and the law label `R1` has count **9**. The referent (REALIZE's law R1: reduced correction digits) is verified and is [ILN]† S4.1's; the note's compound spelling is note-local. **Disposition: NEAR-MISS, referent verified, carried descriptively.** Same for `REALIZE R3` (`R3` count **4**).

**TEETH:** `jb_id` — (ID-(i+1)) exact + key-dev digits + print-key grid/shear-constancy (**34 samples, IND**, “both engines”, with a genuinely print-side leg); `jb_tree` keys **R-leaf reducedness** — which is exactly the scoped statement the correction leaves standing.

---

### EFF.GRTJB.s2of3.34  [lemma]  ★ JB-TREE (iii) — the polygon bookkeeping, RE-SCOPED at r4/F-4

**CANONICAL STATEMENT:** verbatim, lines 1853–1897 — the two displayed equalities, the struck per-edge `v_{m+1}` transfer, and the `[r4, F-4]` re-scope.
**FORM:** bold clause label + struck sentence + bracketed replacement.

> “**(iii) [the polygon bookkeeping = LED-Λ's line face, one citation].**
> On reduced cells, line(C) = w_m(C) ([RMG] L-LINE(iv)) = v_{m+1}(C)
> (JA-VAL): THE LEDGER'S LINE FUNCTIONAL IS THE CLASSIFIER'S MacLANE
> ORDINATE. ~~Hence LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the
> complete per-edge polygon bookkeeping of the division in classifier
> coordinates: promotions raise v_{m+1} by exactly the quantum q_{i+1} > 0,
> correction-main edges are v_{m+1}-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀
> (Y), exits pay w_mΦ_m~~ **[r4, F-4 — RE-SCOPED. The struck sentence
> transferred the per-edge line laws to v_{m+1} across EVERY tree edge, but its
> license is a REDUCED-CELL identity and NO internal tree node is reduced ([RMG]
> S2.2's own construction: a node with an outgoing edge has some j_i ≥ P_i);
> off the reduced cells [RMG] supplies only line(C) ≤ w_m(C) (L-CELL(i): w_m =
> min line over the reduced cells of the decomposition, plus L-MONO), never
> equality. THE CLAUSE AS RE-SCOPED, stated of the right functional:
> LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the complete per-edge
> polygon bookkeeping of the division AS EXACT LAWS OF THE LINE FUNCTIONAL, on
> every edge: promotions raise line by exactly the quantum q_{i+1} > 0,
> correction-main edges are line-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀ (Y),
> exits pay w_mΦ_m in line. AT THE R-LEAVES — the reduced cells, where the
> division's output R lives — and there ONLY, the ledger reads in classifier
> coordinates: line = w_m (L-LINE(iv)) = v_{m+1} (JA-VAL). That leaf reading is
> the only v_{m+1} statement this clause asserts, and it is exactly what
> `jb_line` keys (leaf line == wlev == vgen; no v_{m+1} statement is tested at
> any non-leaf — §0M row 17). DERIVABILITY OF THE INTERNAL-EDGE TRANSFER WAS
> CHECKED BEFORE RE-SCOPING: within this note's consumption list it is NOT
> derivable (L-LINE(iv) is reduced-only; LED-Λ's own face is "λ_E·J(C) = line(C)
> BY DEFINITION of the line" — a statement about line, not w_m). A candidate
> route OUTSIDE the list exists and is recorded as NOT TAKEN: the print's
> order-(m+1) valuation is multiplicative (HigherNewton's valuation proposition,
> tex ~1012 — NOT among this note's print anchors), which with JA-VAL and the
> per-atom values v_{m+1}(b) = E_m·w₀(b), v_{m+1}(Φ_l) = Γ_l would extend
> line = v_{m+1} to every cell; but the Φ_l atom value rests on the single-digit
> weight recursion, which degenerates where deg Φ_q = deg Φ_l (interior periods
> P_t = 1 — realized on this note's own roster, e.g. T3E's P_1 = 1) and there
> needs a two-digit-development case argument consuming WELL-DEF data one level
> down, and no instrument keys any internal-node v_{m+1} statement. Honesty over
> reach: the line law is what is cited, proved and measured; the leaf reading is
> what is claimed in classifier coordinates. Nothing downstream moves —
> JB-TREE(iv) and §5 consume w_m/v_{m+1} of the OUTPUT polynomials R and Q
> through JA-VAL directly, never a per-edge internal-cell ordinate.]**
> ([LED-Λ] S1 table, λ_E column; L-MONO = the
> division never descends below the polygon — the print's
> division-stability genre read through the dictionary). Where earlier
> units re-derived these per edge, J-B cites the ledger ONCE; LED-Λ is
> consumed at ATTEMPT grade and the tie's grade rides it.”

**CHAIN (rule 25):** r0's per-edge `v_{m+1}` transfer → **r4/F-4** re-scope (line-functional laws on every edge; `line = w_m = v_{m+1}` at R-leaves only) → **r5/F-1** removal of the one live leftover at surface 4 (`.37`). **TERMINAL = the r4 re-scope as cleaned by r5/F-1.**

**SUPERSESSION KIND:** `scope-pin`.

**CONDITIONALITY:** **`P<q` read at level m** (matrix row 17), since it consumes JA-VAL; **LED-Λ at ATTEMPT grade and the tie's grade rides it** — and LED-Λ's grade is **NOT** upgraded by the 2026-08-08 supplier annex, so this rider is live at HEAD. **The NOT-TAKEN route is a NON-IMPORT with a stated reason**, and the reason is concrete: the atom value degenerates at interior periods `P_t = 1`, **realized on this note's own roster at T3E**.

**DERIVATION:** Two displayed equalities on reduced cells (`line(C) = w_m(C)` by L-LINE(iv); `= v_{m+1}(C)` by JA-VAL) + the LED-Λ citation (proof line 1908). The re-scope's own derivation: no internal tree node is reduced (a node with an outgoing edge has some `j_i ≥ P_i`, [RMG] S2.2), and off reduced cells [RMG] gives only `line(C) ≤ w_m(C)` (L-CELL(i) + L-MONO), **never equality**.

**RESOLUTION TRACE:** statement lines 1853–1897; proof line 1908; the disposition 979–998 (shard 1 `.61`); the leftover removal 1074–1079 (shard 1 `.68`); matrix row 17 at 311 (shard 1).

XREF: `LEDGERLAMBDA_2026-08-08.md:LED-Λ(A1)` — **5** · `LED-Λ(B)` — count **1** · `λ_E` — **10** · `L-MONO` — **7** · `S1` — **15** (§-anchor; upper bound, referent pinned by `λ_E`).
XREF: `RMENGINE_2026-08-08.md:L-LINE` — **23** · `L-CELL` — **11** · `S3.2` — **3**.

**CITE-SCOPE NOTE:** tex ~1012 (the print's valuation-multiplicativity proposition) is **the one HigherNewton anchor GRTJB explicitly declines to consume**. It is therefore NOT in the NS-11 retarget set and NOT a CITE-SCOPE liability — it is a NON-IMPORT. Recorded in §4.

**TEETH:** `jb_line` — λ_E quanta per edge recomputed **FRESH** on `line(·)` + **leaf** `line == wlev == vgen` (194 samples, **IND**; the vgen half gated on `qcap ≥ m`). **No internal-node `v_{m+1}` statement is keyed — or, as of r4, claimed.** Disposition: **executable regression, scope-matched to the corrected claim** — the instrument keyed leaves all along and the prose was the error. The FRESH re-verification is the decorrelation JB-BOX-4 claims against LED-Λ's attempt grade.

---

### EFF.GRTJB.s2of3.35  [lemma]  JB-TREE (iv) — (RM-m) as the transported instance

**CANONICAL STATEMENT:** verbatim, lines 1899–1903.
**FORM:** bold clause label + paragraph.

> “**(iv) [(RM-m) as the transported instance].** On this scope the four
> (RM-m) box clauses ([RMG] ACCEPTED) become classifier statements: (C-W_R)/
> (C-W_Q) are polygon statements about the classifier's R and Q digits
> (their v_{m+1}-values, via JA-VAL), and (C-READ) transports as §5. No
> clause of [RMG] is re-proved or touched.”

**CONDITIONALITY:** `P<q` read at level m (JA-VAL consumption) **AND** — for the (C-READ) leg — **§5's (VD-m) fence IN FULL** (matrix row 18, the correction r4/F-1 made to summary point (4)). **Its (C-W_Q) clause has NO machine leg** and is a no-leg cell ADJUDICATED OUT of the frontier (consumption at grade, not an open proviso).

**DERIVATION:** Composition (proof line 1908: “(iv) composition”). The transport is clause-by-clause: (C-W_R)/(C-W_Q) via JA-VAL on the output digits; (C-READ) via §5.

**RESOLUTION TRACE:** statement lines 1899–1903; proof line 1908; matrix row 18 at 312 (shard 1); the r4/F-1 correction 950–958 (shard 1 `.58`); the (C-READ) transport 2186–2242 (`.47`, `.49`).

XREF: `RMENGINE_2026-08-08.md:(RM-m)` — **11** · `(C-W_R)` — **7** · `(C-W_Q)` — **9** · `(C-READ)` — **8**.

**TEETH:** **(C-W_R) IND** (`jb_cread`'s `w_m(R) = λ+γ_{m+1}` pin); **(C-W_Q) NONE**; **(C-READ) IND on the scored stratum**. Disposition: mixed; the (C-W_Q) half is a **disclosed non-repair**.

---

### EFF.GRTJB.s2of3.36  [changes-record]  (JB-TREE — the proof and the two struck grade lines)

**CANONICAL STATEMENT:** verbatim, lines 1905–1921.
**FORM:** `*Proof.*` marker + two struck grade blocks.

> “*Proof.* (i) consumption chain as displayed + JB-DEV(i). (ii) dev of
> Φ_{i+1} by Φ_i: the right side of (ID-(i+1)) has every C_k^{(i)}Φ_i^{e_ik}
> of degree < deg Φ_{i+1} with the C_k reduced (REALIZE R1), so the digit
> list reads off; uniqueness of division. (iii) the two displayed equalities
> + LED-Λ citation. (iv) composition. ~~∎ Grade: PROVED at attempt grade on
> the displayed scope. Scope fences: T-scope(m) …~~ ~~**[r2, G2-1 re-grep — a fence r1 carried into §2/§3 and
> left out of this grade line …]**~~”

**CONDITIONALITY:** Both grade lines **STRUCK and superseded by surface 4** (`.37`). **The r2 line is the one whose ADDITION created the inconsistency r2's own certification sentence denied** — PE3's F-1B (shard 1 `.49`): “hit 7 created the inconsistency in this same round by fencing JB-TREE(iii)/(iv) at m ≤ qcap while the grade cap graded JB-TREE with no perimeter and JB-BOX-2's enumeration omitted JB-TREE entirely”. The PROOF is live.

**DERIVATION:** This unit IS the proof: four one-line discharges.

**RESOLUTION TRACE:** statement lines 1905–1921; the superseding surface 1923–1962 (`.37`); the F-1B record 751–763 (shard 1 `.49`).

**TEETH:** carried by the clauses.

---

### EFF.GRTJB.s2of3.37  [TABLE]  ★ SURFACE 4 of 14 — the §4 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1923–1962.
**FORM:** bold-headed bracketed block + fixed-width per-clause display + an `[r3, F-1B]` closing note.

> “**[r3, STEP 2 — SURFACE 4 of 14, REGENERATED FROM §0M rows 14–18. ∎ GRADE:
> PROVED at attempt grade on the displayed scope. SCOPE FENCES ON EVERY CLAUSE:**
> T-scope(m) (the [RMG] d₀ ≥ 2 flat corners stay FENCED — the weld inherits them,
> blueprint S5's cross-cutting row); g_m = 1 for the Ĉ_m instance; W-WIN not
> consumed (window-free legs only, as in [RMG]). **PER CLAUSE:**
>
>     JB-ID / (ii)  PERIMETER-FREE — uniqueness of division at the print's own
>                   keys. Consumes [RMG] S2.2 (ID-(i+1)) + L-NORM + L-CELL, and
>                   S0.1's P_i = e_i·g_i (r3, F-7).           [rows 14, 16]
>     (i)           PERIMETER-FREE (it consumes JB-DEV(i), which holds at every
>                   q); W2-C1 representative reading, W2-C3's chamber off the
>                   byte perimeter; [RMG] T-TERM + L-EXACT + L-CANON — and
>                   L-CANON's hypothesis deg Ĉ_m < deg Φ_m is one of the two
>                   [RMG] clauses restored to §5's recital in r3 (F-5).
>                                                                 [row 15]
>     (iii)/(iv)    at levels **m ≤ qcap** only (`P<q` read at level m), since
>                   both consume JA-VAL — [r5, F-1: for (iii) the LEAF reading
>                   line = w_m = v_{m+1} at the R-LEAVES only (row 17); for
>                   (iv) the v_{m+1}-values of the OUTPUT digits R and Q
>                   (row 18); the unrestricted `line(C) = w_m(C) = v_{m+1}(C)`
>                   this line carried was the ONE live leftover of the r4/F-4
>                   re-scope, three lines above the surface's own (iii) item] —
>                   which J-A grades
>                   "PROVED unconditionally ON THE SHARED-KEY PERIMETER"; off it
>                   the v_{m+1}-reading of the print side is a different object.
>                                                            [rows 17, 18]
>     (iii)         LED-Λ is consumed at ATTEMPT grade and the tie's grade rides
>                   it (the runner re-verifies the λ_E quanta FRESH). [r4, F-4]
>                   the per-edge laws are laws of the LINE functional; the
>                   identification line = w_m = v_{m+1} is asserted at the
>                   R-LEAVES ONLY (L-LINE(iv) reduced cells + JA-VAL), which is
>                   where `jb_line` keys it; no internal-node v_{m+1} statement
>                   is claimed or tested.                              [row 17]
>     (iv)          its (C-READ) leg transports as §5 and therefore rides §5's
>                   (VD-m) fence IN FULL; its (C-W_Q) clause has NO machine leg.
>                                                                 [row 18]
>
> **[r3, F-1B — the (iii)/(iv) perimeter (r2's re-grep hit 7) now ALSO reaches
> the grade cap and JB-BOX-2's enumeration. r2 introduced this fence and in the
> same round certified those two surfaces "already consistent"; that claim was
> false when written and is corrected in the r2 block above.]]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating row(s) |
|---|---|---|
| **JB-ID / (ii)** | **PERIMETER-FREE** — uniqueness of division at the print's own keys; consumes [RMG] S2.2 (ID-(i+1)) + L-NORM + L-CELL + S0.1's `P_i` | rows 14, 16 |
| **(i)** | **PERIMETER-FREE** (consumes JB-DEV(i), every `q`); W2-C1 representative reading; W2-C3's chamber off the byte perimeter; T-TERM + L-EXACT + L-CANON (the last through the restored `deg Ĉ_m < deg Φ_m`) | row 15 |
| **(iii)/(iv)** | at levels **`m ≤ qcap`** only (`P<q` read at level `m`), since both consume JA-VAL; for (iii) the **LEAF** reading, for (iv) the `v_{m+1}`-values of the **OUTPUT** digits R and Q (r5/F-1) | rows 17, 18 |
| **(iii)** | LED-Λ at **ATTEMPT** grade, the tie's grade rides it; per-edge laws are **LINE**-functional laws; `line = w_m = v_{m+1}` at **R-LEAVES ONLY** | row 17 |
| **(iv)** | its (C-READ) leg rides §5's **(VD-m)** fence IN FULL; **(C-W_Q) has NO machine leg** | row 18 |
| **standing (all clauses)** | T-scope(m) (d₀ ≥ 2 flat corners stay FENCED); `g_m = 1` for the Ĉ_m instance; **W-WIN not consumed** | rows 15, 18, 26 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 14–18.** It carries the r5/F-1 cleanup inside it (the removed leftover) and the r3/F-1B honesty note about r2's false certification.

**ARITHMETIC AUDIT (rule 22):** generating rows cited = 14, 15, 16, 17, 18 → **5 rows, contiguous, no gaps, no repeats** ✔ matches “§0M rows 14–18”. Clause entries = 5 (JB-ID/(ii), (i), (iii)/(iv), (iii), (iv)); rows 17 and 18 each appear twice, once in the joint (iii)/(iv) perimeter entry and once in their own clause-specific entry — **deliberate, and it is exactly what r5/F-1 had to disentangle** ✔. **Cross-check against §0M rows 14–18: every non-blank cell appears; every fence is a cell. VERIFIES.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1923–1962; generating rows 308–312 (shard 1 `.20`); the r5/F-1 cleanup 1074–1079 (shard 1 `.68`); the F-1B record 751–763 (shard 1 `.49`).

**TEETH:** per row; **(C-W_Q) NONE**; the 8 chamber walks NONE.

---

### EFF.GRTJB.s2of3.38  [instrument-record]  (JB-TREE — the machine bracket, with the r1/G-1 correction)

**CANONICAL STATEMENT:** verbatim, lines 1963–1980.
**FORM:** display with an embedded `[r1, G-1]` strike-and-replace.

> “[Machine: JB-TREE — a FRESH from-note tree walker
> (this unit's own implementation of S2.1/S2.2 on ITL towers: cells,
> E1-priority, L-NORM via divmod, signed reassembly) checked against (1)
> exact reassembly f·Ĉ_m = R₀ + QΦ_m, (2) ~~the canonical division by the
> harness key AND by the print-side key where byte-equal~~ **[r1, G-1 —
> CORRECTED to what the sealed runner establishes: the canonical division BY
> THE HARNESS KEY (one fresh `fresh_divmod`), plus, where the print key is
> byte-equal to it, the same division re-executed on the print key's bytes —
> a CONSISTENCY RE-CHECK, not an independent print-key reading: `fresh_divmod`
> is a pure function of (R, f, key), so on equal tuples the second call cannot
> fail unless the first does, and off the byte-equal set the sealed battery runs
> NO print-key tree check at all. The genuinely independent print-key evidence
> is the POST-SEAL walker of §7.4 (`grt_jb_printwalk.py`), which builds the
> tree from the print chain's own keys and correction digits and never calls
> `fresh_divmod`]**, (3) R-leaf
> reducedness; JB-ID — (ID-(i+1)) as the key's own development, both
> engines; JB-LINE — line(C) = wlev = vgen on reduced cells + the per-edge
> λ_E quanta recomputed fresh (LED-Λ's table row keyed); teeth MJB-TREE.]”

**SUPERSESSION KIND:** `counter re-reading` — an advertised independent print-key reading re-read as a consistency re-check.

**CONDITIONALITY:** **This is PE1/G-1, the FIRST instance of the SAME-COMPUTATION disease** that later produced the `IND/SAME/NONE` classification (`.18` / shard 1 `.18`) and recurred twice more. **The repair's own repair-instrument reproduced it** (r2/G2-2, shard 1 `.50`), which is the note's clearest bred-defect record.

**DERIVATION:** Purity of `fresh_divmod` as a function of `(R, f, key)`: on equal tuples the second call cannot fail unless the first does.

**RESOLUTION TRACE:** statement lines 1963–1980; the disposition 660–672 (shard 1 `.47` item G-1); the cell note ⟨n2⟩ 339–345 (shard 1 `.22`); the post-seal walker 2766–2846 (shard 3).

**TEETH:** `jb_tree` (79 walks, 125 with chambers, GREEN) with a **SAME** print-key sub-leg; `jb_id` (34, GREEN); `jb_line` (194, GREEN); planted mutant **MJB-TREE** (corrupted correction, 3/3 caught, fired). Post-seal: walker leg A, 84 print-keyed walks, genuinely decorrelated.

---

### EFF.GRTJB.s2of3.39  [definition]  ★ §5 setting — the (RM-m) recital RESTORED (r3/F-5)

**CANONICAL STATEMENT:** verbatim, lines 1986–2023 — the struck partial recital, the `[r3, STEP 3 = F-5]` restoration, the quoted (RM-m) box, and the completed setting.
**FORM:** struck paragraph + bold-headed bracketed block + a quoted source display + a fixed-width clause list.

> “Setting: ~~the (RM-m) box verbatim ([RMG] S0.2, ACCEPTED on its scope):
> level m, g_m = 1, Ĉ_m the canonical correction digit
> (R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m), f ≠ 0 with
> deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and the canonical division
> f·Ĉ_m = R + Q·Φ_m.~~
>
> **[r3, STEP 3 = F-5 — THE RECITAL RESTORED, and with it the citation license
> LEMMA JB-EPS's application needed. The struck recital called itself "the (RM-m)
> box verbatim" while DROPPING two of the three parenthetical clauses [RMG]
> states about Ĉ_m. Both are restored here, quoted from the source display —
> `RMENGINE_2026-08-08.md` §S0.2, "THE STATEMENT UNDER PROOF — the (RM-m) box,
> quoted verbatim (operative-site paste)", itself byte-frozen there from [ILN]†
> S4.6 — which reads:**
>
> > **(RM-m) [READ-MULT with the canonical correction, level m], 1 ≤ m.**
> > Setting: level m of a class tower with g_m = 1, Ĉ_m the canonical
> > correction digit of WELL-DEF-(n)(ii) (deg < deg Φ_m, w_m = γ_{m+1},
> > R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}c_m). Input: f ∈ O[x],
> > f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f) its read. Claim:
> > there exist R, Q ∈ O[x] with deg R < deg Φ_m, deg Q < deg Φ_m, and
> >
> >   f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},
> >   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),
> >   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m,
> >   ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋  [the level-m EPS-carry].
>
> **SO §5'S SETTING, NOW COMPLETE: level m, g_m = 1, and Ĉ_m the canonical
> correction digit of WELL-DEF-(n)(ii) with ALL THREE of its clauses —**
>
>     (Ĉ-deg)   deg Ĉ_m < deg Φ_m                      [RESTORED in r3]
>     (Ĉ-wt)    w_m(Ĉ_m) = γ_{m+1}                      [RESTORED in r3]
>     (Ĉ-read)  R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m
>
> **— together with f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and
> the canonical division f·Ĉ_m = R + Q·Φ_m. (Ĉ-deg) is not decoration: [RMG]
> L-CANON's three hypotheses are Φ_m MONIC, deg f < deg Φ_m and (Ĉ-deg), so the
> restored clause is exactly what makes "THE canonical division" canonical at
> this site.**”

**Double-emission (rule 14) — the three Ĉ_m clauses as a `[TABLE]`:**

| clause | statement | status | what consumes it |
|---|---|---|---|
| **(Ĉ-deg)** | `deg Ĉ_m < deg Φ_m` | **RESTORED in r3** | L-CANON's third hypothesis — “exactly what makes ‘THE canonical division’ canonical at this site” |
| **(Ĉ-wt)** | `w_m(Ĉ_m) = γ_{m+1}` | **RESTORED in r3** | **the clause that LICENSES the JB-EPS instance at `(V, V′) = (λ, γ_{m+1})`** (`.43`) |
| **(Ĉ-read)** | `R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m` | present in r0 | JB-CREAD's proof (`τ_m` a unit) and the `Ĉ_m ≠ 0` step of the license |

**SUPERSESSION KIND:** `inventory completion` — a recital that called itself verbatim while dropping two clauses.

**CONDITIONALITY:** [RMG] ACCEPTED on its own scope (T-scope(m), g_m = 1). **The restoration is what makes two downstream statements licensed rather than asserted** — L-CANON's canonicity at `.31` and JB-EPS's application instance at `.43`. **PE4 byte-compared the restored recital against the source: 11/11 lines identical.**

**DERIVATION:** Quotation from the source display, itself byte-frozen there from [ILN]† S4.6.

**RESOLUTION TRACE:** statement lines 1986–2023; the disposition 893–897 (shard 1 `.55` STEP 3, and `.17`); the byte comparison 938–940 (shard 1 `.57`); the licensed consumers 1793–1801 (`.31`) and 2113–2144 (`.43`); matrix row 20 at 314 (shard 1).

XREF: `RMENGINE_2026-08-08.md:S0.2` — **13** · `(RM-m)` — **11** · `L-CANON` — **6**.
XREF: `ITERLAWN_PROOF_2026-08-08.md:S4.6` — **30** · `WELL-DEF` — **32**.

**TEETH:** **AUDIT — transfer audit** (PE4's 11/11 byte comparison against the source display). No battery can key a recital's completeness.

---

### EFF.GRTJB.s2of3.40  [definition]  ★ THE LEVEL-m WEIGHT LATTICE `𝒲_m` (r4/F-8)

**CANONICAL STATEMENT:** verbatim, lines 2025–2044.
**FORM:** bold-headed bracketed block + fixed-width display.

> “**[r4, F-8 — THE OBJECT, DEFINED ONCE (the lemma quantifies over it, this
> license derives membership in it, and the u ≥ 0 retraction prose at §2(iii)
> argues about it — and no display in this note defined it).**
>
>     THE LEVEL-m WEIGHT LATTICE
>         𝒲_m := { w_m(f) : f ∈ O[x], f ≠ 0, deg f < deg Φ_m }
>              = { E_m·a + Σ_{l<m} j_l·Γ_l : a ∈ ℤ_{≥0}, 0 ≤ j_l ≤ P_l − 1 },
>
> **the VALUE SET of the level-m weight on this note's polynomial class (the
> SCRIPT letter 𝒲 deliberately — the roman W_m is already §1's read datum
> W_m := w_mΦ_m and is untouched). The
> second, explicit description is [RMG]: every such f is a finite sum of
> distinct REDUCED cells with w_m(f) = min line over them (L-CELL(i)), so every
> weight value IS a reduced-cell line value E_m·w₀(b) + Σ j_l·Γ_l with
> 0 ≤ j_l ≤ P_l − 1 and a := w₀(b) ≥ 0; conversely every reduced cell attains
> its line as its own weight (L-LINE(iv)), so every such value occurs.
> CONSEQUENCE, which closes the second half of the lemma's quantifier (PE4's
> F-8): E_m ≥ 1 and every Γ_l ≥ 1, with all coefficients ≥ 0, so 𝒲_m ⊆ ℤ_{≥0} —
> the quantifier's "V, V′ ≥ 0" half is IMPLIED by lattice membership, not a
> separate unchecked side condition.]**”

**SUPERSESSION KIND:** `inventory completion` — an object quantified over, argued about, and never defined.

**CONDITIONALITY:** **The explicit description rests on L-CELL(i)'s hypothesis `deg f < deg Φ_m`. That single hypothesis is why r5's discharge is only a SUB-WINDOW discharge and why matrix rows 4 and 12 stay on the frontier** (`.42`). **The notational separation `𝒲_m` (script) vs `W_m` (roman) is deliberate and flagged** — a collision hazard the merge must preserve.

**DERIVATION:** Both inclusions displayed. **(⊆)** every `f` in the class is a finite sum of distinct REDUCED cells with `w_m(f) = min line` over them (L-CELL(i)), so every weight value is a reduced-cell line value `E_m·w₀(b) + Σ j_l·Γ_l` with `0 ≤ j_l ≤ P_l − 1`, `a := w₀(b) ≥ 0`. **(⊇)** every reduced cell attains its line as its own weight (L-LINE(iv)), so every such value occurs. **Consequence:** `E_m ≥ 1`, every `Γ_l ≥ 1`, all coefficients `≥ 0` ⇒ `𝒲_m ⊆ ℤ_{≥0}`.

**RESOLUTION TRACE:** statement lines 2025–2044; the disposition 1021–1028 (shard 1 `.65`); consumed at 2046–2062 (`.41`), 2085–2111 (`.42`), 2113–2131 (`.43`), 1526–1536 (`.14`'s forward pointer); the `P_l` definition 1803–1819 (`.32`).

XREF: `RMENGINE_2026-08-08.md:L-CELL` — **11** · `L-LINE` — **23** · `S2.1` — **15** (the `E_m`, `Γ_l` constants).

**TEETH:** corroborated only: PE6's 598,500-member enumeration and PE7's reproduction. Disposition: **accepted-with-decorrelation-supplied**; the object itself is a definition and needs none.

---

### EFF.GRTJB.s2of3.41  [lemma]  ★ the four-line theorem: `u ≥ 0` on all of `𝒲_m` (r5/F-3)

**CANONICAL STATEMENT:** verbatim, lines 2046–2083 — the theorem, its four displayed steps, the parity corollary, and the struck/replaced machine bracket.
**FORM:** bold-headed bracketed block + fixed-width numbered derivation + bold corollary + struck machine bracket with `[r6, F-2]` replacement.

> “**[r5, F-3 — THE DISCHARGE ON THE LATTICE (PE5's finding, re-derived here):
> u ≥ 0 IS A THEOREM ON ALL OF 𝒲_m, four lines from the display above. With
> s_m^wt(V) := (ℓ_{m−1}V) mod e_{m−1} (§5's notation block below;
> ℓ_{m−1}h_{m−1} ≡ 1 mod e_{m−1}) and the [RMG] S2.1 constants E_m =
> e₀⋯e_{m−1}, Γ_l = γ_{l+1}·∏_{l<t<m} e_t:**
>
>     (1) e_{m−1} | E_m, and e_{m−1} | Γ_l for every l ≤ m−2 (the ∏ contains
>         t = m−1); while Γ_{m−1} = γ_m ≡ h_{m−1} (mod e_{m−1}) with
>         γ_m ≥ h_{m−1} ≥ 1 (γ₁ = h₀; γ_m = e_{m−1}·w_{m−1}Φ_{m−1} + h_{m−1}
>         at m ≥ 2, with w_{m−1}Φ_{m−1} ≥ 0; h ≥ 1 the class pin).
>     (2) Hence every V = E_m·a + Σ_{l<m} j_l·Γ_l ∈ 𝒲_m has
>         V ≡ j_{m−1}·h_{m−1} (mod e_{m−1}), so s_m^wt(V) = j_{m−1} mod e_{m−1}
>         ≤ j_{m−1} (multiply by ℓ_{m−1}).
>     (3) V − s_m^wt(V)·h_{m−1} ≥ j_{m−1}·γ_m − s_m^wt(V)·h_{m−1}
>         ≥ (j_{m−1} − s_m^wt(V))·h_{m−1} ≥ 0  (every discarded term is ≥ 0;
>         γ_m ≥ h_{m−1}).
>     (4) So u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 for EVERY V ∈ 𝒲_m.  ∎
>
> **COROLLARY (correcting the two retained framing sentences, §2(iii) and
> JB-BOX-2): J-A's counterexample (e_{m−1}, h_{m−1}) = (2, 3), V = 1 ⇒ u = −1
> IS excluded from 𝒲_m — by (2), V ≡ j_{m−1} (mod 2), so V = 1 forces j_{m−1}
> odd ≥ 1, whence V ≥ γ_m ≥ 3 > 1.** ~~[Machine: read-only probe 2026-08-06
> (/tmp, all four instruments byte-untouched): 5,288,324 enumerated lattice
> members …]~~ **[r6, F-2 — the struck r5 bracket's figure is
> NOT REPLAYABLE … REPLACED by the reproducible record, with
> attribution: the PE6 verifier's own independent read-only enumerator
> (`GRTJB_passPE6_report.md` §1, commit ca39044; parameters disclosed there —
> 1-, 2- and 3-level read chains, coprime (e, h) with e ≤ 6, h ≤ 8,
> W_l ∈ {0, 1, 2}, a ≤ 4, j_l ≤ 6, 900 sampled chains): **598,500 lattice
> members, u < 0 violations 0, step-(2) identity violations 0; 1 ∉ 𝒲₁ at
> (e, h) = (2, 3)**. NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the
> displayed four-line THEOREM above — re-derived exactly by PE6 — and the
> probes are corroboration only.]**”

**Double-emission (rule 14) — the four-step derivation as a `[TABLE]`:**

| step | claim | ground |
|---|---|---|
| **(1)** | `e_{m−1} \| E_m`; `e_{m−1} \| Γ_l` for `l ≤ m−2`; `Γ_{m−1} = γ_m ≡ h_{m−1} (mod e_{m−1})` with `γ_m ≥ h_{m−1} ≥ 1` | `E_m = e₀⋯e_{m−1}`; the product in `Γ_l` contains `t = m−1` for `l ≤ m−2`; `γ_m = e_{m−1}w_{m−1}Φ_{m−1} + h_{m−1}` with `w_{m−1}Φ_{m−1} ≥ 0`; `h ≥ 1` the class pin |
| **(2)** | every `V ∈ 𝒲_m` has `V ≡ j_{m−1}h_{m−1} (mod e_{m−1})`, so `s_m^wt(V) = j_{m−1} mod e_{m−1} ≤ j_{m−1}` | (1) + multiply by `ℓ_{m−1}` (`ℓ_{m−1}h_{m−1} ≡ 1 mod e_{m−1}`) |
| **(3)** | `V − s_m^wt(V)h_{m−1} ≥ j_{m−1}γ_m − s_m^wt(V)h_{m−1} ≥ (j_{m−1} − s_m^wt(V))h_{m−1} ≥ 0` | every discarded term `≥ 0`; `γ_m ≥ h_{m−1}`; (2) |
| **(4)** | `u := (V − s_m^wt(V)h_{m−1})/e_{m−1} ≥ 0` for EVERY `V ∈ 𝒲_m` ∎ | (3) divided by `e_{m−1} > 0` |
| **COROLLARY** | J-A's `(e,h) = (2,3), V = 1 ⇒ u = −1` is **excluded from `𝒲_m`** | by (2), `V ≡ j_{m−1} (mod 2)`, so `V = 1` forces `j_{m−1}` odd `≥ 1`, whence `V ≥ γ_m ≥ 3 > 1` |

**CHAIN:** member 3 of the `u ≥ 0` chain; **CHAIN HOME is §0M column (b)** (shard 1 `.14`); `CHAIN-MEMBER: s1of3.14 position 3`. **This unit is the POSITIVE content of the whole chain** — the only place the discharge is actually proved.

**SUPERSESSION KIND:** `scope-pin` (the discharge with its sub-window scope) + `replacement` (r6/F-2's swap of an UNPINNED figure for a reproducible one).

**CONDITIONALITY:** **The theorem is unconditional ON `𝒲_m`.** Everything conditional is about MEMBERSHIP in `𝒲_m` — see `.42`. **The parity corollary matters because it kills the specific counterexample the retraction (`.14`) said “nothing in this note excludes”** — so the r2 retraction's own framing went stale, and r5 says so.

**PIN VERIFICATION (rule 23):** r5's own figure (5,288,324) is **UNPINNED** — read-only to /tmp, parameters unrecorded, and the note reaches that verdict itself at r6/F-2. The replacement (598,500/0) is verifier-owned with parameters disclosed in `GRTJB_passPE6_report.md` (**file EXISTS**), commit `ca39044` (**resolves**), and was **independently REPRODUCED EXACTLY by PE7 on the first natural parameterization**.

**DERIVATION:** Fully displayed above, four lines from `.40`'s description; **re-derived from the note's own display, not copied from the verifier** (the note says so).

**RESOLUTION TRACE:** statement lines 2046–2083; the object 2025–2044 (`.40`); the scope split 2085–2111 (`.42`); the chain home 218–250 (shard 1 `.14`); dispositions 1053–1073 (r5/F-3) and 1164–1178 (r6/F-2), both shard 1.

XREF: `RMENGINE_2026-08-08.md:S2.1` — **15**.

**TEETH:** **PROOF-ONLY, and the note says so:** “NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the displayed four-line THEOREM”. Corroboration: PE6 598,500/0 (produced), PE7 reproduced exactly, PE8 wider box 340/0 on the m = 1 equivalence. Disposition: **PROOF-ONLY + accepted-with-decorrelation-supplied**.

---

### EFF.GRTJB.s2of3.42  [scope record]  ★ the SCOPE split — what the discharge does and does not cover

**CANONICAL STATEMENT:** verbatim, lines 2085–2111.
**FORM:** bold-headed paragraph with two nested riders.

> “**SCOPE — WHAT THIS DISCHARGES AND WHAT IT DOES NOT (§0M rows 4/12, column
> (b)).** The two u ≥ 0 consumers — §2(iii)(GRID) and JB-VTX(d4) — quantify
> f ∈ O[x] nonzero with NO DEGREE BOUND and apply JA-GRID(a) at
> V = w_{q+1}(f), while 𝒲_{q+1} is the weight value set ONLY on
> deg f < deg Φ_{q+1} (L-CELL(i)'s hypothesis is what the displayed
> description rests on — the same hypothesis scope as §4(ii)'s r5/F-2 note).
> So the proviso is DISCHARGED on the deg f < deg Φ_{q+1} sub-window, where
> membership holds by definition, and stays CARRIED at the full quantifier as
> the ~~strictly smaller~~ MEMBERSHIP hypothesis w_{q+1}(f) ∈ 𝒲_{q+1} **[r6,
> m-1 — the accurate relation: membership IMPLIES the u ≥ 0 instance needed at
> V = w_{q+1}(f) — a SUFFICIENT route, ~~per-instance a logically STRONGER
> hypothesis, not an equivalent or weaker one~~ **[r7, PE7 F-1 — the struck
> non-equivalence claim was derived nowhere and is FALSE at every m = 1
> (q = 0) instance, where {V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁ EXACTLY — §0M column
> (b) carries the two-direction proof (the §5 four-line theorem + the j := s
> decomposition) and PE7's machine check (96 read data, every V ∈ [0, 150),
> 0 counterexamples; `GRTJB_passPE7_report.md` §2 F-1, commit aa9b603). The
> instance-honest relation: sufficiency always — all any consumer uses; the
> converse INSTANCE-DEPENDENT — EQUIVALENT at m = 1, containment possibly
> strict at m ≥ 2, strictness UNPROVED either way in general]**; "smaller" is
> true only of the
> remaining open DOMAIN, now confined to deg f ≥ deg Φ_{q+1} and pinned to one
> concrete question]**, which
> nothing this note consumes establishes at deg f ≥ deg Φ_{q+1}. Rows 4 and 12
> therefore REMAIN frontier members with their open residue re-characterized
> (summary point (1)). **§5's OWN application is unaffected either way: its
> λ, γ_{m+1} memberships are DERIVED above (the license), not hypothesized.]**”

**CHAIN:** carries members 3→4 of the `u ≥ 0` chain in body form. **CHAIN HOME: §0M column (b)** (shard 1 `.14`); **TERMINAL reading is r7's**, quoted inside. `CHAIN-MEMBER: s1of3.14 positions 3–4 (body site B).`

**SUPERSESSION KIND:** `scope-pin` (the split) + `wording-rider` (r6) + `counter re-reading` (r7).

**CONDITIONALITY:** **This is the honest core of the whole `u ≥ 0` arc, and it is stated as a clean two-part disposition:**
- **DISCHARGED** on `deg f < deg Φ_{q+1}` (membership holds by definition).
- **CARRIED** at the full quantifier as `w_{q+1}(f) ∈ 𝒲_{q+1}` — SUFFICIENT for what the consumers need; EQUIVALENT at `m = 1`; **strictness at `m ≥ 2` UNPROVED EITHER WAY**.
- **Rows 4 and 12 REMAIN frontier members.**
- **§5's own application is unaffected** — its two memberships are DERIVED at `.43`, not hypothesized. **This last clause is what stops the open residue from contaminating JB-CREAD.**

**DERIVATION:** The split is read off `.40`'s description (which rests on L-CELL(i)'s `deg f < deg Φ_m`) against the consumers' quantifier (`f` nonzero, no degree bound). The `m = 1` equivalence's two directions are displayed at §0M column (b) (shard 1 `.14`): **(⊇)** the four-line theorem at `m = 1`; **(⊆)** `u(V) ≥ 0` means `V = s·h₀ + u·e₀` with `s := (ℓ₀V) mod e₀ ∈ [0, e₀−1]`, `u ≥ 0` — take `j := s ≤ e₀−1 ≤ P₀−1` and `a := u`.

**RESOLUTION TRACE:** statement lines 2085–2111; the theorem 2046–2062 (`.41`); the chain home 218–250 (shard 1 `.14`); dispositions 1053–1073, 1179–1190, 1218–1258 (shard 1 `.67`, `.75`, `.77`, `.78`); the third site JB-BOX-2 2362–2372 (`.56`).

**TEETH:** rows 4 and 12 are **frontier cells (`NONE` + open residue)**. The `m = 1` equivalence: PE7 96 read data / 0 counterexamples; PE8 wider box 340 / 0. Disposition: **PROOF-ONLY for the split; accepted-with-decorrelation-supplied for the equivalence**. **OPEN-CALL 3 of shard 1 is exactly this residue.**

---

### EFF.GRTJB.s2of3.43  [lemma]  THE LICENSE — the two lattice memberships derived

**CANONICAL STATEMENT:** verbatim, lines 2113–2144.
**FORM:** bold-headed block + fixed-width two-part derivation + a closing provenance paragraph with an `[r4, F-5]` correction.

> “**THE LICENSE (what F-5 charged). LEMMA JB-EPS below is quantified over
> V, V′ ≥ 0 IN THE LEVEL-m WEIGHT LATTICE (:= 𝒲_m above; the script letter — W_m stays §1's read datum w_mΦ_m), and THEOREM JB-CREAD's
> display applies it at (V, V′) = (λ, γ_{m+1}). Both LATTICE memberships now
> follow in one line each — and the ≥ 0 conditions follow from them, since
> 𝒲_m ⊆ ℤ_{≥0} (r4, F-8):**
>
>     λ = w_m(f)  with f ≠ 0        ⇒  λ is the level-m weight of a NONZERO
>                                      polynomial of the class (deg f < deg Φ_m),
>                                      hence λ ∈ 𝒲_m BY THE DEFINITION ABOVE
>                                      [r4, F-8: the old warrant "(which contains
>                                      every value of w_m on nonzero
>                                      polynomials)" is now the displayed
>                                      definition, not an uncited parenthetical].
>     γ_{m+1} = w_m(Ĉ_m) by (Ĉ-wt), and Ĉ_m ≠ 0 because its read
>     R_{m,γ_{m+1}}(Ĉ_m) = τ_m is NONZERO by (Ĉ-read) (τ_m = ε_m(γ_{m+1})^{−1}c_m
>     with c_m = ψ_{m,0} ≠ 0, the class pin)
>                                   ⇒  γ_{m+1} is likewise the level-m weight of
>                                      a nonzero polynomial, hence in the
>                                      level-m weight lattice.  ∎
>
> **Before r3 the second line was UNAVAILABLE in this note: γ_{m+1} appeared only
> as the DEFINED INTEGER γ_{m+1} := e_m·w_mΦ_m + h_m of §1's read data, and
> (Ĉ-wt) — the clause that identifies that integer as a weight — was the clause
> the recital had dropped. The lemma itself was never in danger (its proof uses
> only s^wt(β) ≡ ℓ_{m−1}β mod e_{m−1} and JA-GRID(c), ~~and `jb_eps` quantifies
> PLAIN integers 0 ≤ V,V′ < 25, a superset of the lattice~~ **[r4, F-5 — the
> struck description of the machine leg was wrong twice: `jb_eps` samples the
> STRIDED grid V ∈ 2ℤ, V′ ∈ 3ℤ inside [0, min(3·e·h + 5, 25)) — a spot-check of
> the lemma, NOT a superset of anything; the applied instance is sampled on only
> 4 of the 56 roster scored rows (§0M row 20)]**), so r3 restores the
> LICENSE rather than widening the lemma: the quantifier stands as written and the
> cited instance is now provably inside it. §0M rows 19/20.]**”

**SUPERSESSION KIND:** `inventory completion` (r3/F-5 restores the licensing clause) + `counter re-reading` (r4/F-5 corrects the machine-leg description twice over).

**CONDITIONALITY:** **The license is DERIVED, not hypothesized** — which is exactly why `.42` can say “§5's OWN application is unaffected either way”. **Its second line depends on the restored `(Ĉ-wt)`** and was literally unavailable before r3. **The r4/F-5 correction downgrades the instance's machine support to a strided spot-check on 4 of 56 rows** — so the license rests on the PROOF, not on the leg, and the note says so.

**DERIVATION:** Two one-line derivations, displayed. `λ ∈ 𝒲_m` by `.40`'s definition (λ is `w_m` of a nonzero `f` in the class). `γ_{m+1} ∈ 𝒲_m` because `(Ĉ-wt)` gives `γ_{m+1} = w_m(Ĉ_m)` and `(Ĉ-read)` gives `Ĉ_m ≠ 0` (its read `τ_m = ε_m(γ_{m+1})^{−1}c_m` is nonzero, with `c_m = ψ_{m,0} ≠ 0` the class pin). The `≥ 0` half follows from `𝒲_m ⊆ ℤ_{≥0}` (r4/F-8).

**RESOLUTION TRACE:** statement lines 2113–2144; the restored clauses 2015–2017 (`.39`); the object 2025–2044 (`.40`); matrix rows 19, 20 at 313–314 (shard 1); dispositions 893–897 (r3/F-5) and 999–1008 (r4/F-5), shard 1.

XREF: `ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13** (the class pin `ψ_j(0) ≠ 0`).

**TEETH:** matrix row 20 — a **STRIDED SPOT-CHECK**: `V` from `range(0, min(3·e·h + 5, 25))` stepped `[::2]`, `V′` same range stepped `[::3]`; the applied instance IN the sampled set on **4 of 56** roster scored rows (T2A, T3D at m = 1, λ ∈ {0,4}, γ₂ = 9) and **NOT-SAMPLED on the other 52, including EVERY m ≥ 2 row**. Disposition: **signed vacuity disclosure**; “an instance-keyed leg is a CANDIDATE for a future instrument”.

---

### EFF.GRTJB.s2of3.44  [definition]  the constant `c_m = ψ_{m,0} = −z_{m+1}`

**CANONICAL STATEMENT:** verbatim, lines 2146–2150.
**FORM:** inline paragraph + display.

> “Here c_m = ψ_{m,0}, the constant coefficient of the
> degree-1 modulus ψ_m(y) = y + ψ_{m,0} (from WELL-DEF's g_m = 1 lift form
> and REALIZE R3, consumed) — so in K_{m+1} = K_m[z_{m+1}]/(ψ_m),
>
>     c_m = ψ_{m,0} = −z_{m+1}    (the classifier's NEXT residual letter).”

**CONDITIONALITY:** Requires `g_m = 1` (so `ψ_m` is degree 1). **This identity is “the semantic germ the J-C carrier block (W-6..W-9) needs”** (`.54`) and is the one place GRTJB touches the J-C interface — under an explicit BLOCKED-ON-CARRIER-TIE fence.

**DERIVATION:** At `g_m = 1`, `ψ_m(y) = y + ψ_{m,0}`; in `K_{m+1} = K_m[y]/(ψ_m)` the class of `y` is `z_{m+1}`, so `z_{m+1} + ψ_{m,0} = 0`, i.e. `ψ_{m,0} = −z_{m+1}`.

**GENERALITY NOTE (Q7, recorded not applied).** `runs/qgen/Q7_output.log` classifies this display **BENIGN** under hazard H3: *“`c_m = ψ_{m,0} = −z_{m+1}` — **BENIGN.** Negation makes sense in every characteristic; in characteristic 2, `−z = z`. No use of `2^{−1}`, discriminant square classes, or mod-4/8 arguments occurs.”* No edit; recorded.

**RESOLUTION TRACE:** statement lines 2146–2150; consumed at 2212 (`.47`'s conclusion), 2303–2308 (`.54`); the class pin `ψ_j(0) ≠ 0` at [ILN]† S0.1.

XREF: `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` — **32** · `REALIZE` — **17** (NEAR-MISS on the compound `REALIZE R3`; law label `R3` count **4**).

**TEETH:** `jb_cm` — `c_m = ψ_{m,0}` and `embed_{K_{m+1}}(c_m) = −z_{m+1}`, **28 eligible (T, m) rows, GREEN** (§7.1, shard 3).

---

### EFF.GRTJB.s2of3.45  [definition]  the `s_m(·)` overload, declared and split (r1/G-7)

**CANONICAL STATEMENT:** verbatim, lines 2152–2169.
**FORM:** bold-headed bracketed block + fixed-width two-part definition + a closing discipline sentence.

> “**[r1, G-7 — the s_m(·) OVERLOAD, declared and split.]** r0 wrote one symbol
> s_m(·) for two different integers, undefined in-note:
>
>     s_m^wt(V) := (ℓ_{m−1}·V) mod e_{m−1}   for a level-m WEIGHT V
>                  — the eq-(12) abscissa; equivalently the least x ∈
>                  [0, e_{m−1}) with (V − x·h_{m−1}) ≡ 0 (mod e_{m−1}),
>                  which is the runner's ℓ-FREE `s_geo(V, e, h)`;
>     s_m^ini(A) := the INITIAL ATTAINED ABSCISSA of a POLYNOMIAL A on its
>                  own realized side (the print's s₀ = the least abscissa of
>                  the realized side of N_m(A)) — the integer (VD-m) and
>                  τ_m(A) are written with.
>
> They differ by a multiple of e_{m−1} in general (J-A's own
> s₀ = s_m^wt(β) + ν·e_{m−1}, ν ≥ 0 the grid offset), so the two readings are
> NOT interchangeable. From here on LEMMA JB-EPS is stated with s_m^wt ONLY
> (its arguments are weights) and (VD-m)/τ_m with s_m^ini; no step of §5 mixes
> them, and the r0 proof did not (this is a notation repair, not a
> mathematical one).”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| symbol | definition | domain | used by |
|---|---|---|---|
| **`s_m^wt(V)`** | `(ℓ_{m−1}·V) mod e_{m−1}`; equivalently the least `x ∈ [0, e_{m−1})` with `(V − x·h_{m−1}) ≡ 0 (mod e_{m−1})`; = the runner's ℓ-FREE `s_geo(V, e, h)` | a level-m **WEIGHT** `V` | **LEMMA JB-EPS only** |
| **`s_m^ini(A)`** | the INITIAL ATTAINED ABSCISSA of a **POLYNOMIAL** `A` on its own realized side (the print's `s₀`, least abscissa of the realized side of `N_m(A)`) | a polynomial `A` | **(VD-m) and `τ_m` only** |
| relation | `s₀ = s_m^wt(β) + ν·e_{m−1}`, `ν ≥ 0` the grid offset — **they differ by a multiple of `e_{m−1}` in general and are NOT interchangeable** | — | — |

**SUPERSESSION KIND:** `inventory completion` — one symbol carrying two integers, split and both defined.

**CONDITIONALITY:** **“this is a notation repair, not a mathematical one” — the note verifies the r0 proof did not mix them.** The separation is load-bearing downstream: `.46`'s lemma is stated with `s_m^wt` ONLY, `.47`'s `τ_m` with `s_m^ini` ONLY.

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies the `s_m^wt` arithmetic **BENIGN** under H1/H7: *“`t_m(β)=(ℓ_{m−1}β−s_m^{wt}(β))/e_{m−1}` — **BENIGN — integer normalization.** No `e`-th root or field division is used.”* No edit; recorded.

**DERIVATION:** Definitions + the displayed relation `s₀ = s_m^wt(β) + ν e_{m−1}`, which is J-A's own.

**RESOLUTION TRACE:** statement lines 2152–2169; the disposition 688–690 (shard 1 `.47` item G-7); consumed at 2171–2183 (`.46`) and 2205–2209 (`.47`).

**TEETH:** the runner's ℓ-free `s_geo` is the machine form of `s_m^wt` and is one of `jb_eps`'s two legs (955 samples, IND).

---

### EFF.GRTJB.s2of3.46  [lemma]  ★ LEMMA JB-EPS — the ε-cocycle collapse (the note's only unconditional statement)

**CANONICAL STATEMENT:** verbatim, lines 2171–2184.
**FORM:** bold-headed lemma + display + `*Proof.*` + machine bracket.

> “**LEMMA JB-EPS (the ε-cocycle collapse; unconditional, pure read data).**
> For every m ≥ 1 and V, V′ ≥ 0 in the level-m weight lattice, with
> t_m(β) = (ℓ_{m−1}β − s_m^wt(β))/e_{m−1} the print twist exponent (JA-EPS's
> convention) and ε′ := ⌊(s_m^wt(V) + s_m^wt(V′))/e_{m−1}⌋:
>
>     t_m(V + V′) − t_m(V) − t_m(V′) = ε′ ,   hence
>     ε_m(V+V′) · ε_m(V)^{−1} · ε_m(V′)^{−1} = z_m^{−ε′} .
>
> *Proof.* The numerator telescopes (all s's are s_m^wt): ℓ(V+V′) − s(V+V′) −
> ℓV + s(V) − ℓV′ + s(V′) = s(V) + s(V′) − s(V+V′) = e_{m−1}·ε′ by the carry
> clause (JA-GRID(c) = (C-EPS), graded in J-A PROVED and unconditional, and
> carrying no u ≥ 0 proviso); divide by e_{m−1} (legitimate: t_m(β) ∈ ℤ since
> s_m^wt(β) ≡ ℓ_{m−1}β mod e_{m−1}). The field form is JA-EPS (ε = z^{−t}). ∎
> [Machine: JB-EPS, integers + field elements, every roster level.]”

**CONDITIONALITY:** **UNCONDITIONAL at every `m ≥ 1`** (matrix row 19) — **no perimeter, no `u ≥ 0` proviso (it cites JA-GRID(c), which carries none), no (VD-m)**. This is the ONLY statement in GRTJB with that status, and the note guards it explicitly at `.13` (“this sentence is about (VD-m) only — LEMMA JB-EPS is unconditional at every m ≥ 1, as its own grade line says”). **Its APPLICATION at `(λ, γ_{m+1})` is a separate matter and is `.43`/matrix row 20.**

**DERIVATION:** Displayed in full. The numerator telescopes to `s(V) + s(V′) − s(V+V′)`, which is `e_{m−1}·ε′` **by JA-GRID(c) = (C-EPS)** — the carry clause, PROVED and unconditional in J-A and carrying no proviso. Division by `e_{m−1}` is legitimate because `t_m(β) ∈ ℤ` (since `s_m^wt(β) ≡ ℓ_{m−1}β mod e_{m−1}`). The field form is JA-EPS (`ε = z^{−t}`).

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies exactly this step **BENIGN** under H1/H7: *“‘divide by `e_{m−1}` (legitimate: `t_m(β)∈ℤ` since `s_m^{wt}(β)≡ℓ_{m−1}β (mod e_{m−1})`)’ — **BENIGN — integer divisibility.** This is division in `ℤ`, not multiplication by `e_{m−1}^{−1}` in `O` or a residue field. **It remains valid when the residue characteristic divides `e_{m−1}`.**”* No edit; recorded.

**RESOLUTION TRACE:** statement lines 2171–2184 (statement and proof one span); matrix row 19 at 313 (shard 1); the license 2113–2144 (`.43`); consumed at 2241 (`.49`'s fifth line).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11** · `JA-EPS` — **13**. `RMENGINE_2026-08-08.md:(C-EPS)` — **7**.

**TEETH:** `jb_eps` — **955 samples, IND**: an ℓ-FREE `s_geo` leg plus a fresh Bézout computation against the ℓ-form `t_m`, then the field form. **Two genuinely different computations of the same integer, plus the field check.**

---

### EFF.GRTJB.s2of3.47  [lemma]  ★ THEOREM JB-CREAD — the (C-READ) transport

**CANONICAL STATEMENT:** verbatim, lines 2186–2212 — the hypothesis with its `[r1, F1]` correction and `[r2, G2-4]` mechanism strike, the definitions, and the conclusion.
**FORM:** bold-headed theorem + nested riders + display.

> “**THEOREM JB-CREAD.** Suppose (VD-m) (J-A §3.4's evaluated dictionary)
> holds at f and at R — ~~unconditional for m ≤ 2 (VD-1 = W2-L3; m = 2 by
> JA-RES), per-digit proviso / (R-coll) at m ≥ 3 (JA-BOX-2)~~ **[r1, F1 —
> SUPERSEDED; the struck parenthetical was FALSE and the note's own sealed
> runner refutes it. THE HONEST PERIMETER: unconditional at m ≤ 1 ONLY
> ((VD-1) = W2-L3); at every m ≥ 2 the hypothesis is CONDITIONAL — it needs
> JA-VDIND's absolute character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every
> attained abscissa (sufficient: A_{m−1} = 0, i.e. e_{m−2} = 1; or
> ord(z_{m−1}) | A_{m−1} with the abscissa condition), which at m ≥ 3 is
> implied by the per-digit proviso / (R-coll) of JA-BOX-2. "m = 2 by JA-RES"
> conflated J-A's PER-SLOT law (unconditional at m = 2) with the EVALUATED
> dictionary (VD-2), which JA-RES alone does not give: on the sealed roster
> (VD-2) is machine-evaluated FALSE at 10 of 13 boundary rows
> (T3A/T3B/T3C/T3D ~~— the e₀ ≥ 2 character-visible towers~~ **[r2, G2-4 — the
> struck gloss is a MECHANISM CLAIM and the note's own roster refutes it: T3E
> also has e₀ = 2 (reads e = 2,1,2) and scores 6/6. The four towers are the
> OBSERVED failing rows, listed as data; no property in this note distinguishes
> them from the scoring e₀ ≥ 2 rows, see §7.1]**), §7.1/§7.4]** — and
> suppose v ≠ 0 (THE NON-DEGENERATE READ STRATUM; the v = 0 branch is displayed
> after the proof). Define the print's TWISTED EVALUATED READ
> ρ_m(A) := z_m^{τ_m(A)}·R_m^cls(A)(z_m) (R_m^cls the print residual
> operator at A's own realized side, τ_m(A) = (s_m^ini(A) −
> ℓ_{m−1}w_m(A))/e_{m−1} as in (VD-m), with s_m^ini the initial attained
> abscissa of §5's notation block, r1/G-7). Then w_m(R) = λ + γ_{m+1} exactly,
> and
>
>     ρ_m(R)  =  c_m · ρ_m(f)  =  ψ_{m,0} · ρ_m(f) .”

**SUPERSESSION KIND:** `replacement` (r1/F1: a false perimeter) + `counter re-reading` (r2/G2-4: a mechanism claim struck, not replaced).

**CONDITIONALITY:** **Two hypotheses, both explicit and both fenced:**
1. **(VD-m) at BOTH `f` and `R`** — unconditional at `m ≤ 1` ONLY; at every `m ≥ 2` a HYPOTHESIS (JA-VDIND's absolute character-triviality). **JB-CREAD has NO unconditional stratum above `m = 1`.** **E-1 re-reads the “(R-coll)” label** at GRTJA's root-inclusive form.
2. **`v ≠ 0`** — the non-degenerate read stratum; the `v = 0` branch is `.50`.
**No key perimeter** (⟨n5⟩: the print-side content enters only through the (VD-m) hypothesis, so the theorem is a legitimate conditional at any level).

**DERIVATION:** `.49`.

**RESOLUTION TRACE:** statement lines 2186–2212; **proof lines 2223–2242** (`.49`); the reading fence 1471–1495 (`.13`); the census 2494–2546 and 2748–2764 (shard 3); dispositions 638–659 and 792–803 (shard 1 `.44`, `.51`); correction site 3125–3133 (E-1); matrix rows 21, 22 at 315–316 (shard 1).

XREF: `GRTJA_PROOF_2026-08-08.md:(VD-m)` — **10** · `JA-VDIND` — **21** · `JA-RES` — **20** · `(R-coll)` — **7** · `JA-BOX-2` — **7**. `GRTW2_PROOF_2026-08-08.md:W2-L3` — **5**.

**TEETH:** `jb_cread` — **IND end-to-end cross-engine** (print residuals via the sealed `GmnLeg`, harness division/reads via ITL, `τ`/`ε′` fresh integers) on the SCORED stratum: **104 scored / 21 boundary disclosed**, plus teeth **MJB-CREAD** (22 samples over 14 towers). Disposition: **executable regression with the boundary census disclosed**.

---

### EFF.GRTJB.s2of3.48  [scope record]  the transport, stated in both frames

**CANONICAL STATEMENT:** verbatim, lines 2214–2221.
**FORM:** bold-headed paragraph.

> “**The transport, stated.** [RMG]'s (C-READ) — "multiplying a read digit by
> the canonical correction digit shifts the read by τ_m with the level-m
> EPS-carry z_m^{ε′}" — transports to the classifier as: THE CLASSIFIER'S
> TWISTED RESIDUAL READ SHIFTS BY THE CONSTANT c_m, WITH NO CARRY FACTOR.
> The z_m^{ε′} carry of the harness frame is EXACTLY the coordinate change
> between the print twist t_m and the harness ε-kit (LEMMA JB-EPS); it
> reappears verbatim when the identity is written in ε-coordinates — that
> form IS [RMG] (C-READ), consumed not re-proved.”

**CONDITIONALITY:** Inherits `.47`'s two hypotheses. **The two-frame statement is what JB-BOX-1 corrects in the blueprint** (`.55`): the blueprint displayed the harness-frame form as if it were the classifier-frame one.

**DERIVATION:** The carry's cancellation is LEMMA JB-EPS, applied inside `.49`'s chain; the harness-frame form is [RMG] (C-READ), **consumed not re-proved**.

**RESOLUTION TRACE:** statement lines 2214–2221; proof lines 2236–2242 (`.49`); the box 2314–2321 (`.55`).

XREF: `RMENGINE_2026-08-08.md:(C-READ)` — **8**.

**TEETH:** teeth **MJB-CREAD** — “the spurious-carry reading `ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f)` must FAIL on designated `ε′ ≥ 1` rows”, and it does on all 22. **This is the tooth that makes the carry's placement machine-load-bearing rather than a notational preference.**

---

### EFF.GRTJB.s2of3.49  [lemma]  ★ the five-line proof chain

**CANONICAL STATEMENT:** verbatim, lines 2223–2242.
**FORM:** `*Proof (displayed in full).*` + a five-line display.

> “*Proof (displayed in full).* By (VD-m) at f: ρ_m(f) = ε_m(λ)·v. Since
> v ≠ 0 and τ_m is a unit, (C-READ) gives R_{m,λ+γ_{m+1}}(R) =
> z_m^{ε′}·v·τ_m ≠ 0, so some cell of R sits on-line on-grid at
> λ + γ_{m+1} (B-READ) **[r1, G-7 — tag resolved: (B-READ) is [RMG] S2.1's
> LEMMA L-CELL clause (ii) — a nonvanishing level-m read at a weight forces an
> on-line on-grid cell at that weight — whose parent L-CELL is in this note's
> header consumption list; clause (i) (w_m = the minimum line over cells) is
> what turns that into the weight inequality. r0 used the bare tag, which is
> unresolvable from this note alone]**, forcing w_m(R) ≤ λ + γ_{m+1}; with
> (C-W_R)'s ≥
> this pins w_m(R) = λ + γ_{m+1} EXACTLY — so (VD-m) at R is an identity
> at the (C-READ) target:
>
>     ρ_m(R) = ε_m(λ+γ_{m+1}) · R_{m,λ+γ_{m+1}}(R)
>            = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · τ_m            [(C-READ)]
>            = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · ε_m(γ_{m+1})^{−1} · c_m
>            = [ε_m(λ+γ_{m+1}) ε_m(λ)^{−1} ε_m(γ_{m+1})^{−1}] · z_m^{ε′}
>              · c_m · ε_m(λ)·v
>            = z_m^{−ε′} · z_m^{ε′} · c_m · ρ_m(f)            [JB-EPS]
>            = c_m · ρ_m(f) .                                  ∎”

**CONDITIONALITY:** Inherits `.47`'s hypotheses. **Every step names its ground inline**, and the note calls the display “in full” — it is the one proof in GRTJB written as a closed chain rather than a consumption list.

**DERIVATION:** As displayed. Structure: (VD-m) at `f` gives `ρ_m(f) = ε_m(λ)v`; `v ≠ 0` + `τ_m` a unit + (C-READ) gives a nonzero target read; **(B-READ) = L-CELL(ii)** forces an on-line on-grid cell at `λ+γ_{m+1}`, hence `w_m(R) ≤ λ+γ_{m+1}`; **(C-W_R)'s `≥`** pins equality; then the five-line computation, whose only non-consumption step is **JB-EPS**, which collapses `ε_m(λ+γ_{m+1})ε_m(λ)^{−1}ε_m(γ_{m+1})^{−1} = z_m^{−ε′}` against the `(C-READ)` carry `z_m^{ε′}`.

**NEAR-MISS (rule 15) — `(B-READ)`:** fixed-string `(B-READ)` has count **0** in `RMENGINE_2026-08-08.md`. **The note itself resolves it in place** to “[RMG] S2.1's LEMMA L-CELL clause (ii)”; `L-CELL` count **11**, `S2.1` count **15**. Disposition: **NEAR-MISS — designation absent as written; verified referent `L-CELL` (count 11); the tag is GRTJB-local and r1/G-7 declares it so.** Not an OPEN-CALL.

**RESOLUTION TRACE:** statement lines 2223–2242; the hypotheses 2186–2212 (`.47`); JB-EPS 2171–2184 (`.46`); the disposition 688–690 (shard 1 `.47` item G-7).

XREF: `RMENGINE_2026-08-08.md:(C-READ)` — **8** · `(C-W_R)` — **7** · `L-CELL` — **11** · `S2.1` — **15**.

**TEETH:** the whole chain is what `jb_cread` computes end-to-end on both sides. **JB-PE1 re-derived all five displayed lines; JB-PE2 confirmed them; JB-PE3 re-matched `ε′` VERBATIM against [RMG] S0.2 a second time.** Disposition: **executable regression + three independent hostile re-derivations**.

---

### EFF.GRTJB.s2of3.50  [scope record]  the degenerate branch (`v = 0`)

**CANONICAL STATEMENT:** verbatim, lines 2244–2251.
**FORM:** bold-headed paragraph.

> “**The degenerate branch (v = 0), displayed.** There ρ_m(f) = ε_m(λ)·v = 0
> by (VD-m) at f, and (C-READ) gives only the TARGET-read vanishing
> R_{m,λ+γ_{m+1}}(R) = 0; R's OWN weight can sit strictly above λ + γ_{m+1}
> with a nonzero own-side print residual, so the ρ-form identity is NOT
> claimed at v = 0 — the transport there is the read-at-target statement
> (0 = 0) only. This stratum split is the theorem's own scope, not a gap;
> the runner scores v ≠ 0 rows and censuses the v = 0 rows (checking
> ρ_m(f) = 0 on them, which does hold).”

**CONDITIONALITY:** **The ρ-form is explicitly NOT CLAIMED at `v = 0`.** The reason is displayed and is a real mathematical obstruction: `R`'s own weight can sit strictly above `λ+γ_{m+1}` with a nonzero own-side print residual, so the pinning step of `.49` fails.

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies this branch **GOOD SEPARABILITY/DEGENERACY BOOKKEEPING** under H5: *“The drainage branch is explicitly fenced rather than silently cancelled through a possibly zero residual.”* No edit; recorded.

**DERIVATION:** Displayed: `(VD-m)` at `f` with `v = 0` gives `ρ_m(f) = 0`; `(C-READ)` gives only the target-read vanishing.

**RESOLUTION TRACE:** statement lines 2244–2251; matrix row 22 at 316 (shard 1); the census 2546–2547 (shard 3: “**v = 0 stratum: 0 occurrences; R = 0: 0**”).

**TEETH:** **`NONE` — machine UNEXERCISED (v = 0 census: 0 rows).** Disposition: **signed vacuity disclosure**. **This is one of the note's four frontier cells** — and the only one whose emptiness is a property of the roster rather than of the instruments.

---

### EFF.GRTJB.s2of3.51  [changes-record]  (JB-CREAD — the struck grade line)

**CANONICAL STATEMENT:** verbatim, lines 2253–2260.
**FORM:** struck grade line with a nested `[r1, F1]` rider.

> “~~Grade: PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0} **[r1, F1 —
> the perimeter spelled out: (VD-m) is free only at m ≤ 1; at every m ≥ 2 it is
> a HYPOTHESIS (JA-VDIND's collapse condition, ⊇ (R-coll) at m ≥ 3), so
> JB-CREAD has no unconditional stratum above m = 1. The theorem is
> hypothesis-guarded and its algebra is untouched by this correction — JB-PE1
> re-derived all five displayed lines and the verbatim ε′ match against [RMG]
> (C-READ) — what was wrong in r0 was the advertised SIZE of the perimeter]**;
> the ingredient grades ride ([RMG] ACCEPTED; J-A/W-2 attempt).~~”

**CONDITIONALITY:** **STRUCK and superseded by surface 5** (`.52`). Its content survives there. **The sentence “what was wrong in r0 was the advertised SIZE of the perimeter” is the note's own cleanest summary of the F1 defect class** and is repeated at surface 5.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2253–2260; the superseding surface 2262–2291 (`.52`).

**TEETH:** carried by `.47`.

---

### EFF.GRTJB.s2of3.52  [TABLE]  ★ SURFACE 5 of 14 — the §5 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 2262–2291.
**FORM:** bold-headed bracketed block + fixed-width per-fence display + a closing provenance paragraph.

> “**[r3, STEP 2 — SURFACE 5 of 14, REGENERATED FROM §0M rows 19–23. GRADE:
> PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0}. PER FENCE:**
>
>     (VD-m)     unconditional at m ≤ 1 ONLY ((VD-1) = W2-L3); at every m ≥ 2 a
>                HYPOTHESIS — JA-VDIND's ABSOLUTE character-triviality
>                (⊇ (R-coll)/per-digit at m ≥ 3, JA-BOX-2) — so JB-CREAD has NO
>                unconditional stratum above m = 1. Required at BOTH f and R.
>                                                                  [row 21]
>     v ≠ 0      the non-degenerate read stratum. The v = 0 branch is the
>                read-at-target statement (0 = 0) only, the ρ-form is NOT claimed
>                there, and it is machine UNEXERCISED (v = 0 census: 0 rows).
>                                                                  [row 22]
>     key perim. NONE — §5's print-side content enters ONLY through the (VD-m)
>                hypothesis, so the theorem is a legitimate conditional at any
>                level. Disclosure, not a fence: the instrument cuts reduction
>                levels at `qcap_of(T,G)` and the off-perimeter counter is 0 on
>                the roster.                                 [rows 21/22, ⟨n5⟩]
>     u ≥ 0      NOT consumed — LEMMA JB-EPS cites JA-GRID(c), which carries no
>                proviso.                                            [row 19]
>     [RMG]      (C-READ) + (C-W_R) + the COMPLETE Ĉ_m clause list (restored in
>                r3, F-5) + L-CELL(i)/(ii) = (B-READ), on [RMG]'s own scope
>                (T-scope(m), g_m = 1).                        [rows 20, 21]
>     JB-EPS     UNCONDITIONAL at every m ≥ 1; its application at (λ, γ_{m+1}) is
>                LICENSED by the restored (Ĉ-wt) (r3, F-5).    [rows 19, 20]
>
> **The ingredient grades ride ([RMG] ACCEPTED; J-A / W-2 / LED-Λ at attempt).
> The theorem is hypothesis-guarded and its algebra is untouched by every
> correction in this arc: JB-PE1 re-derived all five displayed lines, JB-PE2
> confirmed them, and JB-PE3 re-matched ε′ VERBATIM against [RMG] S0.2 a second
> time. What was wrong in r0 was the advertised SIZE of the perimeter.]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| fence | content | generating row(s) |
|---|---|---|
| **(VD-m)** | free at `m ≤ 1` ONLY; a HYPOTHESIS at every `m ≥ 2`; **NO unconditional stratum above `m = 1`**; **required at BOTH `f` and `R`** | row 21 |
| **`v ≠ 0`** | the non-degenerate read stratum; the `v = 0` branch is read-at-target only, ρ-form NOT claimed, **machine UNEXERCISED (0 rows)** | row 22 |
| **key perimeter** | **NONE** — a legitimate conditional at any level; the instrument's `qcap_of` cut is a **disclosure, not a fence**; off-perimeter counter **0** | rows 21/22, ⟨n5⟩ |
| **`u ≥ 0`** | **NOT consumed** — JB-EPS cites JA-GRID(c), which carries no proviso | row 19 |
| **[RMG]** | (C-READ) + (C-W_R) + the COMPLETE Ĉ_m clause list (restored r3/F-5) + L-CELL(i)/(ii) = (B-READ), on T-scope(m), `g_m = 1` | rows 20, 21 |
| **JB-EPS** | UNCONDITIONAL at every `m ≥ 1`; its application at `(λ, γ_{m+1})` LICENSED by the restored `(Ĉ-wt)` | rows 19, 20 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 19–23.** **E-1 re-reads the “(R-coll)” label** in the (VD-m) row. **The “J-A / W-2 … at attempt” clause is STALE** — the 2026-08-08 annex re-grades both to ACCEPTED at 2/2; **LED-Λ's attempt grade is NOT stale and still rides**.

**ARITHMETIC AUDIT (rule 22):** generating rows cited = 19, 20, 21, 22 → **4 distinct rows.** The surface header says “rows 19–23”, i.e. **5 rows** — **row 23 (JB-BOX-1) is named in the header but appears in NO fence line of the surface.** Row 23 is JB-BOX-1's own row and is graded at `.55` instead, so nothing is lost; but the header's range over-states by one. **Recorded as source defect 2 in §8 — a range-label off-by-one, no fence missing, no cell moved.** Fences listed = 6; each cites at least one row; rows 19–22 each appear at least once ✔.

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 2262–2291; generating rows 313–317 (shard 1 `.20`); correction sites 3125–3133 (E-1), 3148–3161 (supplier grades).

**TEETH:** row 21 IND (104 scored / 21 boundary); **row 22 NONE (unexercised)**; row 19 IND (955); row 20 a strided spot-check (4 of 56).

---

### EFF.GRTJB.s2of3.53  [instrument-record]  (JB-CREAD — the unit hygiene note and the machine bracket)

**CANONICAL STATEMENT:** verbatim, lines 2291–2301.
**FORM:** bracketed hygiene note + machine display.

> “**[r1,
> hygiene] τ_m is a unit because c_m = ψ_{m,0} ≠ 0 (the class pin: ψ_j monic
> irreducible with ψ_j(0) ≠ 0, [ILN]† S0.1 / J-A §1, enforced in the engine's
> ψ search) and ε_m(γ_{m+1})^{−1} is a unit — r0 asserted the unit property
> without the citation.** [Machine: JB-CREAD — both
> sides computed end-to-end (print residuals by the sealed GmnLeg
> transcription, harness division/reads by ITL, τ/ε′ by fresh integers) with
> the (VD-m) instances at f and R MACHINE-EVALUATED per row: scored where
> they hold, boundary census disclosed; JB-CM — c_m = ψ_{m,0} and
> embed_{K_{m+1}}(c_m) = −z_{m+1}; teeth MJB-CREAD — the spurious-carry
> reading ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f) must FAIL on designated ε′ ≥ 1 rows.]”

**SUPERSESSION KIND:** `inventory completion` — a unit property asserted without its citation, cited.

**CONDITIONALITY:** **`τ_m` a unit is a load-bearing step of `.49`** (it is what makes the target read nonzero), and it rests on the class pin `ψ_j(0) ≠ 0`. **The (VD-m) instances are MACHINE-EVALUATED per row** — the instrument does not assume the hypothesis, it checks it and censuses the rows where it fails. **That design is why the F1 refutation was available from the note's own runner.**

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies the class pin **BENIGN** under H1/H5: *“‘ψ_j monic irreducible with ψ_j(0) ≠ 0’ — **BENIGN.** The proof uses irreducibility to obtain a field and ψ_j(0) ≠ 0 to make the residual letter a unit. **It never invokes “irreducible implies separable”** … no step excludes inseparable polynomials such as `x^p − t` by a false characteristic-zero argument.”* No edit; recorded.

**DERIVATION:** The class pin ([ILN]† S0.1 / J-A §1) gives `ψ_j(0) ≠ 0`, hence `c_m = ψ_{m,0} ≠ 0`; `ε_m(γ_{m+1})^{−1}` is a unit by construction of the ε-kit.

**RESOLUTION TRACE:** statement lines 2291–2301; consumed at 2224–2225 (`.49`'s second step); the §7.1 rows 2489, 2488 (shard 3).

XREF: `ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13**.

**TEETH:** `jb_cread` (79 samples GREEN), `jb_cm` (28 rows GREEN), **MJB-CREAD** (planted spurious carry — 22 designated samples over 14 towers, **all caught**, fired).

---

### EFF.GRTJB.s2of3.54  [fence]  ★ the carry seed — the J-C germ, fenced

**CANONICAL STATEMENT:** verbatim, lines 2303–2308.
**FORM:** bold-headed remark.

> “**Remark (the carry seed; fence).** ρ_m(R) = −z_{m+1}·ρ_m(f) in K_{m+1}:
> on twisted residual reads, multiplication by the canonical correction
> digit IS multiplication by the negative of the classifier's next residual
> letter. This is the semantic germ the J-C carrier block (W-6..W-9) needs —
> displayed here as an identity of READ VALUES only; no graded-ring (gr)
> object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.”

**CONDITIONALITY:** **Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence in full.** §7.3's downstream notice (shard 3) says so explicitly: “the J-C germ (ρ_m(R) = −z_{m+1}·ρ_m(f), §5's remark) inherits the same conditionality above m = 1.”

**★ THE J-C INTERFACE, and the merge must carry it.** This is the ONE place GRTJB touches the J-C block, and it is fenced three ways: **(i)** the identity is of READ VALUES only; **(ii)** no gr object is constructed or claimed; **(iii)** BLOCKED-ON-CARRIER-TIE stands. **GRTJC's `(IN-4)` records the inheritance from the other side** — “§5's germ display cites J-B's JB-CREAD + JB-EPS and inherits their fences verbatim” — and GRTJC's §3.3 consumes the value law with J-B's `g_m = 1` fence honoured: “on all **27 eligible (g_m = 1) stages**, val(Ĉ_m) = −z̄ = −z_{m+1} exactly”, while **REFUTING the brief's guess that this letter is OB-3's inner factor** (H-D fails on 138/669 pairs).

**DERIVATION:** `.49`'s conclusion `ρ_m(R) = c_m·ρ_m(f)` composed with `.44`'s `c_m = ψ_{m,0} = −z_{m+1}`.

**RESOLUTION TRACE:** statement lines 2303–2308; the conclusion 2212 (`.47`); the constant 2146–2150 (`.44`); the downstream notice 2658–2665 (shard 3); the standing block 2439–2442 (`.61`).

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JB-CREAD` — grep-verified count **2** (the consumer's own citation of this note — a REVERSE edge). `GRTJC_PROOF_2026-08-08.md:JB-EPS` — count **4**. `GRTJC_PROOF_2026-08-08.md:JB-BOX-2` — count **3**. `GRTJC_PROOF_2026-08-08.md:JB-BOX-4` — count **2**.

**TEETH:** inherits `.47`/`.48`'s legs; the germ itself is not separately keyed. Disposition: **inherited**, with the gate explicitly NOT retired.

---

### EFF.GRTJB.s2of3.55  [changes-record]  JB-BOX-1 — the blueprint carry placement, corrected

**CANONICAL STATEMENT:** verbatim, lines 2314–2321.
**FORM:** bold-headed bullet.

> “* **JB-BOX-1 (blueprint correction, review-owed).** Blueprint J-B(iii)
>   displays the classifier transport WITH the carry ("shifts the
>   CLASSIFIER's residual read by τ_m with the level-m EPS-carry z_m^{ε′}").
>   CORRECTED: in the print's twisted coordinates the carry cancels
>   (THEOREM JB-CREAD); the shift constant is c_m (not τ_m), and the
>   τ_m-with-carry form is the HARNESS-frame statement ([RMG] (C-READ)).
>   The blueprint display conflated the two frames; both are displayed
>   above with the coordinate change (JB-EPS) between them.”

**TYPE JUSTIFICATION (rule 13):** in substance a `supplier-finding` — a defect report against the GRT weld blueprint, **REVIEW-OWED at the source**. Filed `[changes-record]` because the note boxes it as its own correction. **Flagged for the merge run** (same disposition as shard 1 `.36`).

**CONDITIONALITY:** Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence (matrix row 23). **Two distinct errors are named: the wrong CONSTANT (`c_m`, not `τ_m`) and the wrong FRAME (the carry-bearing form is harness-side).**

**DERIVATION:** `.49`'s chain, in which `z_m^{−ε′}·z_m^{ε′}` cancels by LEMMA JB-EPS.

**RESOLUTION TRACE:** statement lines 2314–2321; proof lines 2236–2242 (`.49`); the grade-cap bullet 510–514 (shard 1 `.36`); matrix row 23 at 317 (shard 1).

**TEETH:** **teeth MJB-CREAD — “the carry-bearing reading must FAIL, and does, on all 22 designated samples over 14 towers”.** A planted mutant that fired; the note's strongest single tooth, and the one that converts a display correction into a machine-load-bearing fact.

---

### EFF.GRTJB.s2of3.56  [fence]  ★ JB-BOX-2 — inherited conditionality, quantified (and SURFACE 14)

**CANONICAL STATEMENT:** verbatim, lines 2322–2420. Because the box spans 99 lines with five nested correction layers, it is quoted in **three contiguous blocks**, each complete and byte-verbatim; the union is the whole box minus nothing.

**FORM:** bold-headed bullet with nested `[r1]`/`[r2]`/`[r3]`/`[r5]`/`[r7]` riders and an embedded fixed-width enumeration (SURFACE 14 of 14).

**BLOCK A — the (VD-m) re-fence (lines 2322–2340):**

> “* **JB-BOX-2 (inherited conditionality, quantified).** Every print-residual
>   statement rides J-A's boxes verbatim: ~~the (VD-m)/per-digit proviso at
>   m ≥ 3 (JA-BOX-2 — (R-coll) sufficient, converse unsealed)~~ **[r1, F1 —
>   RE-FENCED, this was the mis-scoped line: the (VD-m) conditionality bites
>   from m = 2 UP, not from m = 3. Correct statement: (VD-1) = W2-L3 is free;
>   at EVERY m ≥ 2 (VD-m) is conditional on JA-VDIND's absolute
>   character-triviality on the attained abscissas; at m ≥ 3 that is the
>   per-digit proviso / (R-coll) box JA-BOX-2 ((R-coll) sufficient, converse
>   unsealed); at m = 2 it is ~~the e₀ ≥ 2 / nontrivial-z₁ boundary~~ **[r2,
>   G2-4 — RE-WORDED: JA-VDIND's absolute character-triviality condition
>   ITSELF, with no known characterisation. The only implication available is
>   e₀ = 1 ⇒ A_1 = 0 ⇒ the condition holds; e₀ ≥ 2 is therefore NECESSARY for an
>   m = 2 failure but is NOT sufficient (T3E, e₀ = 2, scores 6/6)]**, where the
>   sealed runner exhibits 10 in-roster FALSE instances of (VD-2). So the
>   boundary geography of §7.1 is the JA-VDIND collapse condition at m = 2 plus
>   JA-BOX-2's box at m = 3 — r0 attributed all of it to JA-BOX-2]**, the
>   unpinned-ℓ orbit (JA-BOX-3: all displays at the pinned (P-ell)
>   representative; §4.3-orbit transport per J-A §4(ii)), and W-2's
>   (C-coll)/recursion split for the byte law.”

**BLOCK B — the `u ≥ 0` proviso, carried and narrowed (lines 2340–2373):**

> “**[r1, G-5 — one inherited
>   proviso that is NOT one of JA-BOX-1..5 and rode in uncarried in r0:
>   JA-GRID(a)'s `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 … It is consumed by §2(iii)'s
>   (GRID) layer and is hereby CARRIED BY THIS BOX, ~~with the discharge stated
>   at §2(iii) …~~ **[r2, G2-5 — THE DISCHARGE IS
>   RETRACTED … STATUS: CARRIED,
>   DISCHARGE OWED. Every statement consuming §2(iii)(GRID) — JB-DEV(iii)'s
>   (GRID) layer and, through it, the grid/abscissa content of JB-VTX(d) — is
>   conditional on this proviso in addition to its other fences. A real discharge
>   must derive u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 — ~~equivalently~~
>   **[r3, F-6(a) — "equivalently" WITHDRAWN here as at the r2 block's G2-5
>   bullet: the genuine equivalence is u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}, while J-A's
>   print bound is SUFFICIENT only. Read: **for which it SUFFICES to derive** —]**
>   V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) in J-A's own form, for EVERY V in the
>   quantified window with units included; see the retraction block at §2(iii)
>   for what is and is not known (V = 0 gives u = 0, so units are not a
>   counterexample; ~~J-A's own (e,h) = (2,3), V = 1 ⇒ u = −1 is not excluded by
>   anything this note says~~ **[r5, F-3 — struck as STALE against r4's own
>   definition: the lattice 𝒲_m of §5 EXCLUDES J-A's instance by parity, and
>   u ≥ 0 is PROVED on ALL of 𝒲_m there (machine-confirmed). What remains open
>   at the two consuming rows (4 and 12) is ~~exactly~~ **[r7, PE7 m-2 —
>   "exactly" struck as overstating necessity, the same defect r6 struck at
>   §0M column (b): membership is the SUFFICIENT hypothesis the note CARRIES
>   (and at m = 1 it is moreover EQUIVALENT to the needed u ≥ 0 instance —
>   column (b), r7/F-1)]** lattice MEMBERSHIP at their
>   unbounded-degree quantifiers (V = w_{q+1}(f), f of any degree): it holds by
>   definition at deg f < deg Φ_{q+1} — where the proviso is DISCHARGED — and
>   is not established off it. §0M column (b)]**).]** JA-GRID(c) — the carry clause
>   LEMMA JB-EPS consumes — carries NO proviso and is unconditional.]**
>   ~~**[r1, G-9]** The (VAL)/(GRID)/(RES) layers and all of JB-VTX are
>   quantified on the SHARED-KEY perimeter q ≤ qcap …~~”

**BLOCK C — SURFACE 14 of 14, the perimeter enumeration (lines 2379–2420):**

> “  **[r3, STEP 2 — SURFACE 14 of 14: THIS BOX'S PERIMETER ENUMERATION,
>   REGENERATED FROM §0M. The struck r1/G-9 sentence had two defects PE3 named:
>   it omitted JB-TREE(iii)/(iv) (F-1B …), and it put all three
>   layers of §2(iii) on ONE perimeter (F-4). THE COMPLETE ENUMERATION, which is
>   §0M's columns (a1)/(a2) read down:**
>
>     on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap; J-A grades JA-VAL on it,
>     and off it the print frame is a different object):
>         §2(iii)(VAL) and §2(iii)(GRID)                      [rows 3, 4]
>         JB-VTX — (a), (b), (c), (d1)/(d2), (d4), and (e) through
>         (a) at f = Φ_{q+1}^har (r6, F-1: (d3) MOVED to the `P≤q` list
>         below; "ALL of JB-VTX" is no longer true of this line)
>                                                           [rows 8–13]
>         JB-TREE(iii) and JB-TREE(iv), read at level m       [rows 17, 18]
>     on the BYTE-EQUAL CHAIN THROUGH q `P≤q` (strictly stronger; the difference
>     bites at q = qcap only where shared_upto < n — 5 of the 16 roster towers;
>     on the other 11 the two fences coincide over the whole range, r4/F-3):
>         §2(ii)'s byte clause                                    [row 2]
>         §2(iii)(RES) — added in r3, F-4                         [row 5]
>         JB-VTX(d3) — JA-VAL at level q+1; added in r6, F-1
>                                                         [row 11 (a2)]
>     on NO key perimeter:
>         §2(i), §2(iv), JB-AFF, JB-ID, JB-TREE(i), JB-TREE(ii), JB-EPS,
>         JB-CREAD (a legitimate conditional at any level; its instrument's own
>         level cut is disclosed at §5 and §7.1)
>                                                 [rows 1, 6, 7, 14–16, 19–22]
>
>   **And the u ≥ 0 proviso of this box reaches EXACTLY TWO claims: §2(iii)(GRID)
>   (row 4) and JB-VTX's clause (d4) — the attained-abscissa/read-grid tie, which
>   is also the ONE sub-clause of JB-VTX with no machine leg (row 12, r3/F-3).
>   No other statement in this note consumes JA-GRID(a). And the (VD-m) fence,
>   recorded by this box [r4, F-7 — this box carried rows 21/22 only and omitted
>   row 18's rider]: it reaches EXACTLY rows 18 (JB-TREE(iv)'s (C-READ) leg,
>   which transports as §5 and rides the fence IN FULL), 21 and 22 (JB-CREAD,
>   both strata) and 23 (JB-BOX-1) — §0M row 24's (c) cell, synced with summary
>   point (4).]**
>   JB-CREAD's own stratum
>   split (v ≠ 0 scored; v = 0 = the read-at-target branch only, ρ-form
>   not claimed) is displayed at the theorem. W2-OPEN-1 (the value layer
>   on transported lifts) is consumed NOWHERE (independently re-verified in
>   JB-PE1: no §2–§5 statement touches W-2 §5.3's K5/K6/K7/K12 battery).”

**Double-emission (rule 14) — SURFACE 14's enumeration as a `[TABLE]`:**

| fence | statements | generating rows |
|---|---|---|
| **`P<q`** (SHARED-KEY PERIMETER, `0 ≤ q ≤ qcap`) | §2(iii)(VAL), §2(iii)(GRID); JB-VTX (a), (b), (c), (d1)/(d2), (d4), (e) through (a) at `f = Φ_{q+1}^har`; JB-TREE(iii), JB-TREE(iv) read at level `m` | 3, 4, 8–13, 17, 18 |
| **`P≤q`** (BYTE-EQUAL CHAIN THROUGH q; bites at `q = qcap` only where `shared_upto < n`, 5/16 towers) | §2(ii)'s byte clause; §2(iii)(RES) *(added r3/F-4)*; JB-VTX(d3) *(added r6/F-1)* | 2, 5, 11(a2) |
| **NO key perimeter** | §2(i), §2(iv), JB-AFF, JB-ID, JB-TREE(i), JB-TREE(ii), JB-EPS, JB-CREAD | 1, 6, 7, 14–16, 19–22 |
| **`u ≥ 0` proviso — EXACTLY TWO** | §2(iii)(GRID); JB-VTX(d4) | 4, 12 |
| **(VD-m) fence — EXACTLY FOUR** | JB-TREE(iv)'s (C-READ) leg; JB-CREAD `v ≠ 0`; JB-CREAD `v = 0`; JB-BOX-1 | 18, 21, 22, 23 |

**CHAIN (rule 25):** BLOCK B is body site C of the `u ≥ 0` chain; **CHAIN HOME §0M column (b)** (shard 1 `.14`); `CHAIN-MEMBER: s1of3.14 positions 1–4 (body site C — the box)`. **r7/m-2 is the THIRD site of the “exactly” overclaim**, reached only after the r6 sweep (which took a verifier's two-site quote list as its universe) missed it.

**SUPERSESSION KIND:** `replacement` (r1/F1's re-fence), `counter re-reading` (r2/G2-4's mechanism strike; r7/m-2's “exactly”), `replacement` (r2/G2-5's retraction), `wording-rider` (r3/F-6(a)), `scope-pin` (r5/F-3), `inventory completion` (r3's SURFACE 14 and r4/F-7's row-18 rider).

**ARITHMETIC AUDIT (rule 22) — computed fresh against the transcribed matrix (shard 1 `.20`):**
- **`P<q` rows** listed = 3, 4, 8, 9, 10, 11(a1), 12, 13, 17, 18 → **10 statements** ✔ matches column (a1)'s non-blank rows exactly.
- **`P≤q` rows** listed = 2, 5, 11(a2) → **3** ✔ matches column (a2) and summary point (2)'s r6 recount.
- **No-perimeter rows** listed = 1, 6, 7, 14, 15, 16, 19, 20, 21, 22 → **10** ✔ (rows 19–22 named as a range; row 20 is JB-EPS's application, correctly perimeter-free).
- **Coverage check:** 10 + 3 + 10 = **23 claim rows**, and rows 24–28 are the five RECORD rows, so **23 + 5 = 28** ✔ **the enumeration is EXHAUSTIVE over the matrix with no row counted twice** (row 11 appears once per sub-column, which is the r6 split).
- **`u ≥ 0` = EXACTLY TWO (rows 4, 12)** ✔ matches column (b).
- **(VD-m) = rows 18, 21, 22, 23** ✔ matches summary point (4) as rewritten at r4/F-1 — and carries the same row-23 classification overlap flagged as shard 1's source defect 3.

**CONDITIONALITY:** **This box is the note's single conditionality inventory for a downstream consumer, and it is SURFACE 14 of 14 — a regeneration, not an authority.** `W2-OPEN-1` consumed NOWHERE is a NON-IMPORT, independently re-verified in JB-PE1.

**DERIVATION:** Regeneration from §0M columns (a1)/(a2)/(b)/(c) read down.

**RESOLUTION TRACE:** statement lines 2322–2420; generating columns 189–276 and rows 293–322 (shard 1 `.12`–`.20`); dispositions 638–659 (r1/F1), 680–684 (r1/G-5), 792–819 (r2/G2-4, G2-5), 908–911 (r3/F-6(a)), 1015–1020 (r4/F-7), 1053–1073 (r5/F-3), 1096–1101 (r5/F-5), 1250–1258 (r7/m-2) — all shard 1.

XREF: `GRTJA_PROOF_2026-08-08.md:JA-BOX-3` — **3** · `JA-VDIND` — **21** · `JA-BOX-2` — **7** · `(R-coll)` — **7**. `GRTW2_PROOF_2026-08-08.md:(C-coll)` — **27** · `W2-OPEN-1` — **10** · `W2-L3` — **5**.

**TEETH:** the box is a record (matrix row 24, `n/a`). **r5/F-5 audited the box against its own record cell and found row 24's (d) cell asserting a W2-C1 record the box does NOT carry** — an **AUDIT: arithmetic recount** finding (“Grep-verified this round: the box's full extent has NO W2-C1 record”).

---

### EFF.GRTJB.s2of3.57  [fence]  JB-BOX-3 — the cross-key fence

**CANONICAL STATEMENT:** verbatim, lines 2421–2426.
**FORM:** bold-headed bullet.

> “* **JB-BOX-3 (cross-key fence).** No cross-representative operator or
>   byte identity is claimed anywhere (JB-DEV(iv)); transport across
>   representatives is W-2 clause 2/3 covariance only. The JuncForge
>   parity-wall lesson is honored structurally: every §2–§5 statement is
>   against the semantic development/polygon/tree/read objects; SideReads/
>   TreeModel are consumed nowhere.”

**CONDITIONALITY:** A NON-IMPORT record (matrix row 25). **Its “no byte identity is claimed anywhere” is what E-4 relies on when it separates a proof-license boundary from a semantic negation** (`.15`).

**DERIVATION:** Declaration; discharged by the note's architecture (every statement is against semantic objects at a NAMED representative).

**RESOLUTION TRACE:** statement lines 2421–2426; the clause it records 1539–1547 (`.15`); matrix row 25 at 319 (shard 1); E-4's consistency 3282–3286 (shard 3).

**TEETH:** `n/a (record)`. Disposition: **signed non-applicability**.

---

### EFF.GRTJB.s2of3.58  [fence]  JB-BOX-4 — tree scope, and the LED-Λ decorrelation

**CANONICAL STATEMENT:** verbatim, lines 2427–2433.
**FORM:** bold-headed bullet.

> “* **JB-BOX-4 (tree scope).** JB-TREE inherits [RMG]'s fences verbatim:
>   termination on T-scope(m) (d₀ = 1 ∨ non-degenerate below top; the
>   d₀ ≥ 2 flat corners stay FENCED and are quantified over nowhere here);
>   g_m = 1 for the Ĉ_m instance; W-WIN consumed by nothing. LED-Λ is
>   ATTEMPT grade (acceptance counter 0) — the §4(iii) citation's grade
>   rides it, and the runner therefore re-verifies the λ_E quanta FRESH
>   rather than trusting the ledger (decorrelation, not redundancy).”

**CONDITIONALITY:** **LED-Λ's ATTEMPT grade is LIVE at HEAD** — the 2026-08-08 supplier annex upgrades W-2 and J-A but **not** LED-Λ. So `.34`'s grade rider stands, and the box's mitigation (fresh re-verification) is the operative decorrelation. **The `d₀ ≥ 2` flat corners are quantified over NOWHERE**, and `W-WIN` is consumed by nothing — two NON-IMPORTS.

**DERIVATION:** Declaration; the decorrelation claim is discharged by `jb_line`'s FRESH per-edge λ_E recomputation.

**RESOLUTION TRACE:** statement lines 2427–2433; the citation 1853–1897 (`.34`); matrix row 26 at 320 (shard 1); the supplier annex 3148–3161 (shard 3, which does NOT name LED-Λ).

XREF: `RMENGINE_2026-08-08.md:T-scope` — **42** · `W-WIN` — count **9** (verified in RMENGINE, the note that fences it; count **0** in GRTW2 — the designation is [RMG]'s, and GRTJB cites it as such).

**TEETH:** `n/a (record)` — “the FRESH λ_E re-verification of row 17 is the decorrelation this box claims”. Disposition: **accepted-with-decorrelation-supplied** for the LED-Λ grade rider.

---

### EFF.GRTJB.s2of3.59  [fence]  JB-BOX-5 — the instance perimeter

**CANONICAL STATEMENT:** verbatim, lines 2434–2438.
**FORM:** bold-headed bullet.

> “* **JB-BOX-5 (instance perimeter).** Machine evidence = the §7 roster
>   (16 towers, reads ≤ 4 + top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀
>   leg; 5 QO shapes; 4 fresh d₀ ≥ 2 shapes); F_p[[t]] rows have no PARI
>   leg (JA-BOX-4 inherited); mixed-characteristic print, equal-char rows
>   ride construction-identity + machine only.”

**CONDITIONALITY:** **This is the proof-scope-vs-machine-scope fence**, and the F_p[[t]] clause is the one Q7 examines. **The theorems are at general `q`/`m`; the evidence is a 16-tower roster + 5 QO + 4 d₀ shapes.**

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies this row **EVIDENCE-ONLY, NOT A THEOREM RESTRICTION**: *“‘evidence caveat: `F_p[[t]]` rows have NO external (PARI) oracle leg’ — **EVIDENCE-ONLY, NOT A THEOREM RESTRICTION.** Equal-characteristic rows lack one oracle but the symbolic proof does not use that oracle.”* And under H2/H4 Q7 records **NO HIT** for the whole note: *“No occurrence of `v(p)`, an Eisenstein polynomial in `p`, Teichmüller/Witt arithmetic, or an unramified-`ℤ_p` decomposition is load-bearing.”* No edit; recorded.

**DERIVATION:** Declaration of the evidence perimeter.

**RESOLUTION TRACE:** statement lines 2434–2438; the roster 2477–2492 and 2522–2528 (shard 3); matrix row 27 at 321 (shard 1).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-BOX-4` — **4**.

**TEETH:** `n/a (record)` — **evidence caveat: F_p[[t]] rows have NO external (PARI) oracle leg** (JA-BOX-4 inherited). Disposition: **signed vacuity disclosure** on the oracle leg for equal-characteristic rows.

---

### EFF.GRTJB.s2of3.60  [fence]  ★ JB-BOX-6 — standing fences and the §0M governance rule

**CANONICAL STATEMENT:** verbatim, lines 2439–2454.
**FORM:** bold-headed bullet with an `[r3]` procedural addition and an `[r4, F-7]` narrowing.

> “* **JB-BOX-6 (standing fences).** No gr/carrier claim (J-C untouched;
>   BLOCKED-ON-CARRIER-TIE stands); no count/menu/density claim (J-D
>   untouched); the P0 application gate stands; acceptance counter 0/2 —
>   nothing here may be consumed at proof grade before its hostile arc.
>   **[r3 — and one procedural fence, added by this round: the COMPLETE
>   conditionality of every claim in this note is §0M's matrix. A consumer who
>   reads a grade surface (the grade cap, any ∎ Grade line, any §7.2 row, §7.3,
>   or ~~any box~~ **[r4, F-7 — narrowed to the inventory that is true:
>   JB-BOX-2, the ONE box regenerated from the table (surface 14); JB-BOX-1 and
>   JB-BOX-3/4/5 and this box are standing records — consistent with the table
>   as checked, but NOT regenerations of it]**) is reading a REGENERATION of
>   that table; if a surface and the
>   table ever disagree, THE TABLE GOVERNS and the disagreement is a defect to
>   report. Any future repair round that adds or moves a fence must edit §0M
>   first and re-derive the 14 surfaces from it — the per-site sweep genre that
>   produced PE1/G-9, PE2/G2-1 and PE3/F-1 + F-1B is retired.]**”

**SUPERSESSION KIND:** `scope-pin` (r4/F-7 narrows “any box” to the one box that is actually a regeneration).

**CONDITIONALITY:** **THIS UNIT IS FREEZE PREDICATE 2 IN ITS OPERATIVE FORM.** “**THE TABLE GOVERNS**” is the note's governance rule and the reason `.17`, `.27`, `.37`, `.52` and `.56` are labelled REGENERATIONS. **STALE-SELF-DESCRIPTION (rule 26) on two clauses:** “acceptance counter 0/2” and “nothing here may be consumed at proof grade before its hostile arc” are falsified by the acceptance record (ACCEPTED at 2/2, PE9 + PE10) — **and, unlike GRTJC, GRTJB has NO annex expressly superseding them** (shard 1 OPEN-CALL 4). The four negative fences (no J-C claim, no J-D claim, P0 stands, BLOCKED-ON-CARRIER-TIE stands) remain LIVE.

**DERIVATION:** Declaration + a procedural rule.

**RESOLUTION TRACE:** statement lines 2439–2454; the matrix 171–441 (shard 1 `.11`–`.29`); the 14-surface list 885–892 (shard 1 `.55`); the r4/F-7 disposition 1015–1020 (shard 1 `.64`); status superseded — **NOT** superseded; see shard 1 OPEN-CALL 4; the acceptance record 3107–3119 (shard 3).

**TEETH:** `n/a (record)`. The rule's own test is PE4's “**NO fifth instance of the old surface-divergence class**”. Disposition: **AUDIT — in-house hostile pass**.

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every count is `grep -cF '<designation>' <file>` run at HEAD. **68 distinct designations, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `GRTJA_PROOF_2026-08-08.md:JA-VAL` | 7 | (VAL); JB-VTX(a)/(d); JB-TREE(iii)/(iv); **the theorem whose LEVEL-INDEXED perimeter drives both re-fences** |
| 2 | `GRTJA_PROOF_2026-08-08.md:JA-GRID` | 11 | (a) the grid law carrying `u ≥ 0`; **(c) = (C-EPS), the proviso-free carry clause JB-EPS consumes** |
| 3 | `GRTJA_PROOF_2026-08-08.md:JA-RES` | 20 | the PER-SLOT law; `.12`'s (RES) row, re-fenced to `P≤q` |
| 4 | `GRTJA_PROOF_2026-08-08.md:JA-PIN` | 15 | clause 7's weight recursion (JB-VTX(a)); clause 2's Hensel/L1 dispatch (JB-VTX(c)) |
| 5 | `GRTJA_PROOF_2026-08-08.md:JA-EPS` | 13 | the field form `ε = z^{−t}` closing LEMMA JB-EPS |
| 6 | `GRTJA_PROOF_2026-08-08.md:JA-VDIND` | 21 | absolute character-triviality — the hypothesis making (VD-m) conditional at every `m ≥ 2` |
| 7 | `GRTJA_PROOF_2026-08-08.md:(VD-m)` | 10 | JB-CREAD's governing fence |
| 8 | `GRTJA_PROOF_2026-08-08.md:(R-coll)` | 7 | the `m ≥ 3` sufficient condition; **E-1 re-reads this label root-inclusively** |
| 9 | `GRTJA_PROOF_2026-08-08.md:JA-BOX-1` | 8 | the five J-A boxes ridden verbatim |
| 10 | `GRTJA_PROOF_2026-08-08.md:JA-BOX-2` | 7 | the per-digit proviso box at `m ≥ 3` |
| 11 | `GRTJA_PROOF_2026-08-08.md:JA-BOX-3` | 3 | the pinned-(P-ell) orbit — the only representative content JB-BOX-2 carries |
| 12 | `GRTJA_PROOF_2026-08-08.md:JA-BOX-4` | 4 | the F_p[[t]] no-PARI caveat inherited at JB-BOX-5 |
| 13 | `GRTJA_PROOF_2026-08-08.md:shared-key perimeter` | 5 | the phrase whose level-indexing is the arc's recurring defect |
| 14 | `GRTW2_PROOF_2026-08-08.md:W2-C1` | 22 | the admissible representative `φ_{q+1} := Φ_q^har` |
| 15 | `GRTW2_PROOF_2026-08-08.md:W2-C1a` | 10 | the window object — JB-VTX(e)'s true subject |
| 16 | `GRTW2_PROOF_2026-08-08.md:W2-C3` | 22 | chamber transport; **E-2 re-reads its grade at 38/44 + 6/44** |
| 17 | `GRTW2_PROOF_2026-08-08.md:W2-L0` | 5 | consumed by the (GRID) layer |
| 18 | `GRTW2_PROOF_2026-08-08.md:W2-L3` | 5 | **(VD-1) = W2-L3 — the ONLY unconditional level of the dictionary** |
| 19 | `GRTW2_PROOF_2026-08-08.md:W2-OPEN-1` | 10 | declared consumed NOWHERE (a NON-IMPORT), re-verified in JB-PE1 |
| 20 | `GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` | 60 | the box W2-C3's measured-above region rides, per E-2 |
| 21 | `GRTW2_PROOF_2026-08-08.md:(C-coll)` | 27 | the byte law's split (JB-BOX-2) |
| 22 | `GRTW2_PROOF_2026-08-08.md:TH-BASE` | 8 | gives the byte clause at `q = 1` always |
| 23 | `GRTW2_PROOF_2026-08-08.md:3.4` | 35 (§-anchor) | the §3.4(3) byte law; count is an upper bound — referent pinned by rows 21–22 |
| 24 | `RMENGINE_2026-08-08.md:(RM-m)` | 11 | the box §5 recites; quoted in full at `.39` |
| 25 | `RMENGINE_2026-08-08.md:S0.1` | 12 | `P_l := e_l·g_l`, scoped “local to this note” there — added to the consumption list at r3/F-7 |
| 26 | `RMENGINE_2026-08-08.md:S0.2` | 13 | the (RM-m) box; PE4 byte-compared 11/11 |
| 27 | `RMENGINE_2026-08-08.md:S2.1` | 15 | cells/lines; the `E_m`, `Γ_l` constants; the degree telescope |
| 28 | `RMENGINE_2026-08-08.md:S2.2` | 16 | (ID-(i+1)), the E1-priority tree, the structural remark on exit-bound nodes |
| 29 | `RMENGINE_2026-08-08.md:S3.2` | 3 | L-LINE, JB-TREE(iii) |
| 30 | `RMENGINE_2026-08-08.md:L-CELL` | 11 | **(i)** the reduced decomposition (the `𝒲_m` description's ground; the r5/F-2 scope); **(ii)** = the note's `(B-READ)` |
| 31 | `RMENGINE_2026-08-08.md:L-NORM` | 28 | the L/π-junk/Φ₀Y-junk split |
| 32 | `RMENGINE_2026-08-08.md:L-EXACT` | 11 | Σ R-leaves = R, Σ exit cofactors = Q |
| 33 | `RMENGINE_2026-08-08.md:L-CANON` | 6 | canonicity; its third hypothesis `(Ĉ-deg)` restored at r3/F-5 |
| 34 | `RMENGINE_2026-08-08.md:L-LINE` | 23 | (i)–(iii) per-edge laws; **(iv) REDUCED CELLS ONLY** — the r4/F-4 scope repair |
| 35 | `RMENGINE_2026-08-08.md:T-TERM` | 11 | tree termination on T-scope(m) |
| 36 | `RMENGINE_2026-08-08.md:T-scope` | 42 | the standing termination fence |
| 37 | `RMENGINE_2026-08-08.md:(C-READ)` | 8 | the transport JB-CREAD carries to the classifier |
| 38 | `RMENGINE_2026-08-08.md:(C-EPS)` | 7 | = JA-GRID(c); **carries no proviso — why JB-EPS is unconditional** |
| 39 | `RMENGINE_2026-08-08.md:(C-W_R)` | 7 | the `≥` half pinning `w_m(R) = λ + γ_{m+1}` |
| 40 | `RMENGINE_2026-08-08.md:(C-W_Q)` | 9 | **the clause with NO machine leg** |
| 41 | `RMENGINE_2026-08-08.md:(ID-(i+1))` | 3 | the key's own development; JB-ID |
| 42 | `RMENGINE_2026-08-08.md:W-WIN` | 9 | declared **consumed by nothing** (JB-BOX-4) |
| 43 | `ITERLAWN_PROOF_2026-08-08.md:S0.1` | 13 | the class pin `ψ_j(0) ≠ 0` — `τ_m`'s unit property |
| 44 | `ITERLAWN_PROOF_2026-08-08.md:S0.2` | 5 | the read assembly consumed by JB-VTX(d4) |
| 45 | `ITERLAWN_PROOF_2026-08-08.md:REALIZE` | 17 | R1 (reduced correction digits), R3 (the `g_m = 1` lift form) |
| 46 | `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` | 32 | the `g_m = 1` form `Φ_{m+1} = Φ_m^{e_m} + Ĉ_m`; WELL-DEF-(n)(ii) |
| 47 | `ITERLAWN_PROOF_2026-08-08.md:S4.6` | 30 | the source the (RM-m) box is byte-frozen from |
| 48 | `LEDGERLAMBDA_2026-08-08.md:LED-Λ(A1)` | 5 | the λ_E face, cited ONCE |
| 49 | `LEDGERLAMBDA_2026-08-08.md:LED-Λ(B)` | 1 | the five weight functionals |
| 50 | `LEDGERLAMBDA_2026-08-08.md:λ_E` | 10 | the S1 quantum table's column |
| 51 | `LEDGERLAMBDA_2026-08-08.md:L-MONO` | 7 | “the division never descends below the polygon” |
| 52 | `LEDGERLAMBDA_2026-08-08.md:S1` | 15 (§-anchor) | the quantum table; upper bound — referent pinned by row 50 |
| 53 | `docs/references/HigherNewton.tex:propertiesv` | 8 | **item 3, load-bearing in JB-VTX(a)** — NS-11 retarget → [GN15] §1.2 (definitional) |
| 54 | `docs/references/HigherNewton.tex:shape` | 13 | **items 1–2, load-bearing in JB-VTX(d1)** — NS-11 retarget → [GN15] Lem 1.5 + Cor 1.14 |
| 55 | `docs/references/HigherNewton.tex:phiradic` | 2 | the φ_r-adic development genre (JB-DEV(i)'s proof) |
| 56 | `docs/references/HigherNewton.tex:defresidual` | 1 | the residual-polynomial definition |
| 57 | `GD23_phaseB_attempt.md:GD-2` | 7 | the frame normalization; the displayed clause JB-VTX(b) makes explicit |
| 58 | `GD23_phaseB_attempt.md:GD-3` | 5 | co-citer of the O1thr runner |
| 59 | `O1thr_phaseB_verifybrief_rev3.md:T-F` | 10 | the family that measured the shear tie |
| 60 | `O1thr_phaseB_verifybrief_rev3.md:41,720` | 8 | site-instances, 0 violations, sheared frame |
| 61 | `O1thr_phaseB_verifybrief_rev3.md:7,472` | 2 | **violations of the UNSHEARED identification** |
| 62 | `O1thr_phaseB_verifybrief_rev3.md:WGEO` | 16 | the law the T-F family keys |
| 63 | `O1thr_phaseB_verifybrief_rev3.md:M6c` | 32 | co-keyed with WGEO |
| 64 | `GRTJC_PROOF_2026-08-08.md:JB-CREAD` | 2 | **REVERSE edge** — the J-C germ's consumer citing this note |
| 65 | `GRTJC_PROOF_2026-08-08.md:JB-EPS` | 4 | **REVERSE edge** |
| 66 | `GRTJC_PROOF_2026-08-08.md:JB-BOX-2` | 3 | **REVERSE edge** — GRTJC's `(IN-4)` inherits this box's geography verbatim |
| 67 | `GRTJC_PROOF_2026-08-08.md:JB-BOX-4` | 2 | **REVERSE edge** — the `g_m = 1` fence for the Ĉ_m instance |
| 68 | `GRTJB_PROOF_2026-08-08.md:JuncForge` | 2 | note-local reference to the corpus parity-wall lesson (no external designation claimed) |

**Designations counted but NOT emitted as XREFs (3), all NEAR-MISS (rule 15):**
- **`(B-READ)`** — count **0** in `RMENGINE_2026-08-08.md`. **The note resolves it in place** (r1/G-7) to “[RMG] S2.1's LEMMA L-CELL clause (ii)”; verified referent `L-CELL` count **11**, `S2.1` count **15**. GRTJB-local shorthand, declared as such. See `.49`.
- **`REALIZE R1`** — count **0** in `ITERLAWN_PROOF_2026-08-08.md`; parent `REALIZE` count **17**, law label `R1` count **9**. Compound spelling is note-local; referent verified. See `.33`.
- **`REALIZE R3`** — count **0**; parent `REALIZE` **17**, label `R3` count **4**. Same disposition. See `.44`.

**Code-line pins re-read at HEAD (3/3 EXACT):** `grt_jb_checks.py` **L283** = `                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):`; `grt_weld_probe.py` **L211** = `        self.RANK = len(levels)`; `grt_weld_probe.py` **L456–459** = `gmn_from_tower` building `levels` over `range(T.NR)`, returning `GmnLeg(T.R, …)`. **⇒ `RANK = T.NR`, and both the (d3) gate transcription (`.28`) and the ⟨n1⟩ ring-object argument (`.18`) are source-true.**

**md5 pins re-computed at HEAD (4/4 EXACT)** — FREEZE PREDICATE 1.

**Files verified to EXIST:** `docs/references/HigherNewton.tex`; `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md`; `lean/notes/openmath/GD23_phaseB_attempt.md`; `GRTJB_passPE1..PE8_report.md` (8/8); `verification/openmath/{grt_jb_checks.py, grt_jb_printwalk.py, grt_jb_printwalk2.py, grt_jb_r1_levelcensus.py, grt_weld_probe.py}` + their committed outputs/JSONs (12/12).

**Commits verified with `git cat-file -t` (all `commit`):** `5d95805`, `8d5e3fa`, `94534df`, `adc6cf3`, `17d2a32`, `f131c53`, `ca39044`, `aa9b603` (the ones this shard's units cite; the full 29-hash census is in shard 1 §3.1).

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer / supplier | Verified designation | Shard-2 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| **GRTJC (J-C)** | `JB-CREAD` (2), `JB-EPS` (4), `JB-BOX-2` (3), `JB-BOX-4` (2) | `.44`, `.46`, `.49`, `.54` | **The germ `ρ_m(R) = −z_{m+1}·ρ_m(f)` is supplied as an identity of READ VALUES only**; GRTJC's `(IN-4)` records it and inherits JB-BOX-2's geography verbatim. **GRTJC CONFIRMS the value law on 27 eligible g_m = 1 stages and REFUTES the brief's guess that this letter is OB-3's inner factor (H-D fails 138/669)** | **Not landed. No gate retires**: BLOCKED-ON-CARRIER-TIE stands on both sides — GRTJB `.60` and GRTJC's own §10.3 (“The tie is displayed, the gate stands”) |
| GRTJA (J-A) | `JA-VAL` (7), `JA-RES` (20), `JA-GRID` (11) | `.03`, `.04`, `.11`, `.12`, `.14`, `.21`, `.24` | GRTJB re-fenced its OWN consumption twice; **J-A's theorems untouched**. GRTJB additionally PROVES `u ≥ 0` on `𝒲_m` (`.41`), a J-A-side gain proved here | **Not landed.** GRTJB **RECEIVED** E-1 from GRTJA PE2 |
| GRTW2 (W-2) | `W2-C1` (22), `W2-C3` (22), `TH-BASE` (8) | `.09`, `.10`, `.20`, `.30` | Consumed at the source's own grade; nothing upgraded | **Not landed.** GRTJB **RECEIVED** E-2 from GRTW2 r1 |
| RMENGINE ([RMG]) | `L-LINE` (23), `L-CELL` (11), `S0.1` (12) | `.32`, `.33`, `.34`, `.39`, `.40` | **L-LINE(iv)'s reduced-cell scope RESPECTED after r4/F-4**; L-CELL(i)'s degree hypothesis respected after r5/F-2; S0.1's `P_l` cited after r3/F-7. **No [RMG] clause is re-proved or touched** (`.35`) | **Not landed** — every fix is a citation added HERE |
| LEDGERLAMBDA (LED-Λ) | `LED-Λ(A1)` (5), `λ_E` (10) | `.34`, `.58` | Cited ONCE at **ATTEMPT** grade — **not upgraded by the 2026-08-08 annex, live at HEAD**; the runner re-verifies λ_E FRESH | **Not landed** |
| GMN print | `propertiesv` (8), `shape` (13) | `.21`, `.24` | Consumed as literature through the SEALED transcription; **the tex ~1012 multiplicativity anchor is explicitly NOT TAKEN** (`.34`) | **Not landed.** The NS-11 retarget is a READING NOTE — recorded, not applied |
| O1thr rev-3 runner | `T-F` (10), `41,720` (8), `7,472` (2) | `.07`, `.22` | Foreign measurement consumed as the empirical ground for the shear discipline | **Not landed**; re-attributed at r1/G-8 (the runner is CITED BY GD-2/GD-3, not GD-2's own) |

**Zero dated consumption appends are claimed landed on any supplier by this note, and none is invented here.**

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's explicit negative-import fences homed in lines 1303–2457.

| Fence | Explicit material NOT imported or NOT proved | Unit |
|---|---|---|
| **The valuation-multiplicativity route** | “the print's order-(m+1) valuation is multiplicative (HigherNewton's valuation proposition, tex ~1012 — **NOT among this note's print anchors**) … recorded as **NOT TAKEN**: its atom value degenerates at interior periods `P_t = 1` — realized on this note's own roster, e.g. T3E's `P_1 = 1` — and no instrument keys any internal-node `v_{m+1}` statement” | `.34` |
| **Internal-node `v_{m+1}`** | “That leaf reading is the only `v_{m+1}` statement this clause asserts”; “no internal-node `v_{m+1}` statement is claimed or tested” | `.34`, `.37` |
| **The internal-edge line→`w_m` transfer** | “DERIVABILITY OF THE INTERNAL-EDGE TRANSFER WAS CHECKED BEFORE RE-SCOPING: within this note's consumption list it is **NOT derivable** (L-LINE(iv) is reduced-only; LED-Λ's own face is ‘λ_E·J(C) = line(C) BY DEFINITION of the line’ — a statement about line, not `w_m`)” | `.34` |
| **The representative-pin rescue** | “The representative-pin rescue … is **NOT taken**: it is not derived anywhere in this note — the same refusal recorded at (RES)” | `.24`, and `.03`'s r3/F-4 precedent |
| **Cross-representative identity** | JB-BOX-3: “No cross-representative operator or byte identity is claimed anywhere … SideReads/TreeModel are consumed nowhere” | `.15`, `.57` |
| **`W2-OPEN-1`** | “W2-OPEN-1 (the value layer on transported lifts) is consumed **NOWHERE** (independently re-verified in JB-PE1: no §2–§5 statement touches W-2 §5.3's K5/K6/K7/K12 battery)” | `.56` |
| **`W-WIN`** | JB-BOX-4: “**W-WIN consumed by nothing**”; surface 4: “W-WIN not consumed (window-free legs only, as in [RMG])” | `.37`, `.58` |
| **`[RMG]` d₀ ≥ 2 flat corners** | “the d₀ ≥ 2 flat corners stay **FENCED** and are quantified over nowhere here” | `.37`, `.58` |
| **No gr/carrier (J-C) object** | “no graded-ring (gr) object is constructed or claimed, and **BLOCKED-ON-CARRIER-TIE stands**”; JB-BOX-6: “No gr/carrier claim (J-C untouched)” | `.54`, `.60` |
| **No count/menu/density (J-D)** | JB-BOX-6: “no count/menu/density claim (J-D untouched)” | `.60` |
| **The ρ-form at `v = 0`** | “the ρ-form identity is **NOT claimed** at v = 0 — the transport there is the read-at-target statement (0 = 0) only” | `.50` |
| **`[RMG]` clauses not re-proved** | “**No clause of [RMG] is re-proved or touched.**” | `.35` |
| **The ambient-lattice extension** | **Withdrawn from shard 3 (E-3):** the shear “is not unimodular when e_q > 1”; “Only the false ambient-lattice extension is removed” | `.23` |
| **“Different bytes” as a negation principle** | **Withdrawn from shard 3 (E-4):** “‘Different bytes’ is henceforth used only as a proof-license boundary, **not as a semantic-negation principle**” | `.11`, `.20`, `.27` |
| **No mechanism for the (VD-2) split** | “no property in this note distinguishes them from the scoring e₀ ≥ 2 rows”; the roster is DATA with an explicit ban on predicting from it | `.13`, `.47` |
| **No supplier upgrade** | “Every consumption is at the source's own grade; nothing is upgraded here” (header, shard 1 `.40`); reasserted per clause in surfaces 2–5 | `.17`, `.27`, `.37`, `.52` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition. Vocabulary as in shard 1 §5.

| Battery row / instrument leg | Guarded unit(s) | Disposition |
|---|---|---|
| **`jb_dev`** `fresh_dev` vs `PolyO.dev`, 893 | `.09`, `.18` | Executable regression (IND) |
| **`jb_dev`** cross-engine `G.vgen(q+1,A) == T.wlev(q,A)`, `0 ≤ q ≤ qcap` | `.11`, `.12` (VAL), `.18` | Executable regression (IND — the genuine cross-engine leg) |
| **`jb_dev`** third leg `G.P.dev` | `.18` | **SAME — violation UNREACHABLE, no information.** Disposition: `stale self-description` (“both engines”) |
| **`jb_keyeq`** byte census, 25 rows | `.10`, `.02` | Executable regression **+ signed vacuity disclosure**: 3 of 25 VACUOUS (`T.n = 0`) |
| **`jb_shear_vtx`** (d1)(d2)(d3) | `.04`, `.24`, `.28` | Executable regression (IND ×3). For **(d3)** the runner's `q ≤ shared_upto` gate **IS** the statement fence after r6/F-1; for (d1) an instrument cut. Gate **byte-verified at HEAD** |
| **(d4)** | `.14`, `.24`, `.27`, `.28`, `.42` | **PROOF-ONLY (rule 16).** Note's own sentence: “**THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY OF ANY INSTRUMENT**”. Disposition: `disclosed non-repair` |
| **`jb_vtx`** fresh hulls both frames + vertex bijection + `hull_sides` slope/length, 893 | `.19`, `.22`, `.23` | Executable regression (IND). **Survives E-3 unchanged** — “they establish slope transformation and equality of endpoint abscissas/runs, not unimodularity” |
| **`jb_id`**, 34 | `.32`, `.33`, `.38` | Executable regression (IND) with a genuinely print-side leg |
| **`jb_tree`**, 79 walks (125 with chambers) | `.31`, `.33`, `.38` | Executable regression **+ SAME sub-leg** (byteeq-gated print-key re-execution) **+ 8 chamber walks NONE**. `accepted-with-decorrelation-supplied` via the post-seal walker; `disclosed non-repair` for the chambers |
| **`jb_line`** λ_E per edge FRESH + leaf `line == wlev == vgen`, 194 | `.34`, `.37`, `.58` | Executable regression, **scope-matched to r4/F-4** — the leg keyed leaves all along; the prose was the error. Also the LED-Λ **decorrelation** |
| **`jb_eps`**, 955 | `.45`, `.46` | Executable regression (IND: ℓ-free `s_geo` + fresh Bézout against the ℓ-form, then the field form) |
| **`jb_eps`** at the applied `(λ, γ_{m+1})` | `.43`, `.52` (row 20) | **Signed vacuity disclosure** — a STRIDED spot-check; the applied instance sampled on **4 of 56** roster scored rows, NOT-SAMPLED on 52 including every `m ≥ 2` row |
| **`jb_cread`**, 79 (104 scored / 21 boundary) | `.47`, `.49`, `.53` | Executable regression (IND end-to-end cross-engine) with the boundary census disclosed. **The (VD-m) instances are MACHINE-EVALUATED per row, not assumed** |
| **`jb_cread`** `v = 0` branch | `.50` | **NONE — machine UNEXERCISED (0 rows).** `signed vacuity disclosure` |
| **`jb_cm`**, 28 rows | `.44` | Executable regression (`c_m = ψ_{m,0}`, `embed(c_m) = −z_{m+1}`) |
| **(RES)** | `.03`, `.12`, `.24`(⟨n4⟩ ref) | **NONE — “no family keys (RES) anywhere”.** `disclosed non-repair` + **AUDIT: in-house hostile pass** |
| **(C-W_Q)** | `.35`, `.37` | **NONE**, adjudicated OUT of the frontier (consumption at grade). `disclosed non-repair` |
| **teeth MJB-DEV / MJB-VTX / MJB-TREE / MJB-CREAD** | `.18`, `.22`, `.38`, `.48`, `.53`, `.55` | Planted mutants, 3/3 rows each, **all caught**. **MJB-CREAD is the strongest**: the carry-bearing reading must FAIL and does on all 22 samples over 14 towers |
| **The O1thr T-F family** (foreign) — 41,720 site-instances / 0, and **7,472 violations unsheared** | `.06`, `.07`, `.22` | **Foreign-note measurement consumed as decorrelation.** Re-checked in JB-PE1; all five figures re-verified at the source by this compiler |
| **PE6/PE7/PE8 lattice + equivalence legs** (verifier-owned) | `.40`, `.41`, `.42` | `accepted-with-decorrelation-supplied`: 598,500/0 produced (PE6), **reproduced EXACTLY** (PE7), `m = 1` equivalence 96/0 (PE7) and 340/0 on a wider box (PE8) |
| **Post-seal walker leg A**, 84 print-keyed walks | `.31`, `.38` | Executable regression, genuinely decorrelated in keys, correction digits, divisor and division code |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**
1. **`.24` / `.28` — (d4).** “THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY OF ANY INSTRUMENT.”
2. **`.03` / `.12` — (RES).** “No machine leg can catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES) NOWHERE.”
3. **`.41` — the four-line `u ≥ 0` theorem.** “NOTHING RIDES ON EITHER FIGURE … the probes are corroboration only.”
4. **`.50` — the `v = 0` branch.** “machine UNEXERCISED (v = 0 census: 0 rows).”
5. **`.42` — the membership residue at `deg f ≥ deg Φ_{q+1}`.** “nothing this note consumes establishes [it] at deg f ≥ deg Φ_{q+1}.”

**AUDIT rows (rule 27) — findings no battery could have produced:**

| finding | class | the note's own “no tooth applies” sentence |
|---|---|---|
| `.03` r3/F-4 — the (RES) level slip | in-house hostile pass | “No machine leg can catch this” |
| `.04` r6/F-1 — the same slip at (d3) | in-house hostile pass | “the r3/F-4 disease at the one row that correction never swept” |
| `.13` r2/G2-4 — a mechanism claim refuted by the note's own roster | decorrelated-model audit | “this gloss entered the note from JB-PE1's own §1.3 remark — a verifier's unforced explanatory claim; r2 treats no verifier as a source” |
| `.18` r3/F-2 — an advertised second engine that is one computation | in-house hostile pass | “The violation … is therefore UNREACHABLE” |
| `.23` **E-3** — the shear is not unimodular | **decorrelated-model audit** | produced by a sol certification run, not by any battery; “the `hull_sides` machine leg survive[s] unchanged” |
| `.11`/`.20` **E-4** — “FALSE off the perimeter” withdrawn | **decorrelated-model audit** | “Byte inequality … does not by itself imply inequality of the induced values on every polynomial” |
| `.33` r5/F-2 — a citation used beyond its stated hypothesis | in-house hostile pass | “its citation was used beyond L-CELL's stated hypothesis” |
| `.34` r4/F-4 — the internal-edge transfer not derivable | in-house hostile pass | “no instrument keys any internal-node v_{m+1} statement” |
| `.39` r3/F-5 — the dropped recital clauses | transfer audit | PE4's 11/11 byte comparison against RMENGINE S0.2 |
| `.21`/`.24` — the GMN cites' published scope | **decorrelated-model audit** | Q7: “the pasted note gives locations and conclusions but not the publication's hypotheses on the base field” |
| `.56` r5/F-5 — a record cell asserting a record the box does not carry | arithmetic recount | “Grep-verified this round: the box's full extent has NO W2-C1 record” |

**Both-direction audit.** Every leg above guards at least one in-range unit; every unit whose `TEETH` field names a leg appears in some row. Units with **`TEETH: NONE`/`n/a`** — `.05`, `.15`, `.25`, `.29`, `.30`, `.36`, `.51`, `.57`, `.58`, `.59`, `.60` — are definitions, declarations, fences, proofs-as-fields or records and are outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans; five signed PROOF-ONLY units; eleven AUDIT findings.**

---

## 6. BOUNDARY SELF-AUDIT (prose genre, rule 9)

GRTJB carries **zero `\tag{`** in 3327 lines, so boundaries are chosen. **But this shard is the easy half of the note**: §§1–6 supply bold `**THEOREM X.**`/`**LEMMA X.**` openers, bold clause labels `(i)`…`(iv)` and `(a)`…`(e)`, `*Proof.*` markers, four `∎ GRADE` blocks that announce themselves as “SURFACE k of 14”, and six `* **JB-BOX-n**` bullets. **Most boundaries here are READ OFF, not chosen.** The four genuinely chosen ones are recorded below.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Same four-part test as shard 1 (proof obligation / cited by designation / own supersession history / own conditionality or consumer set). Proofs are NOT units (rule 1 makes DERIVATION a field) — **with one deliberate exception recorded at 6.1 item 4.**

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. Theorem clauses as separate units (`.09`–`.15`, `.21`–`.25`, `.31`–`.35`).** Forced by tests 3 and 4: the matrix assigns each clause its OWN row with its own fences and its own evidence class, and the four `∎ GRADE` surfaces grade them per clause. *Not arguable* — a merged “THEOREM JB-DEV” unit would have to carry six different fences and three different evidence classes in one CONDITIONALITY field, and the note's own surfaces refuse to do that.

**2. `.12` (the three-layer `(VAL)/(GRID)/(RES)` display) split from `.11` (the clause head).** Test 2 and 3: `(VAL)`, `(GRID)`, `(RES)` are cited by name from dozens of spans across all three shards, and the three carry three different perimeters, three different evidence classes and two different correction histories. *Alternative:* one clause-(iii) unit. *Rejected* — the whole r3/F-4 correction is precisely that “ONE PERIMETER IS NOT ENOUGH FOR THREE LAYERS”, so a merged unit would reproduce the defect the note repaired.

**3. `.14` and `.42` both carrying the `u ≥ 0` chain, with `.41` carrying its proof.** **Genuinely arguable.** *Candidate A:* one unit for the whole `u ≥ 0` story in this shard. *Candidate B (chosen):* three — the §2(iii) body site (`.14`), the §5 theorem (`.41`), the §5 SCOPE split (`.42`) — plus the box site (`.56` BLOCK B), with **CHAIN HOME declared at §0M column (b) in shard 1** and each body site carrying `CHAIN-MEMBER: s1of3.14 position n`. **Reason:** the four sites have different content (a retraction, a theorem, a scope split, an inventory), are cited independently, and are corrected by different rounds. *Cost:* four places; mitigated by the explicit CHAIN-MEMBER pointers, which is the fix §6.3 item 1 of shard 1 recommended and this shard applies.

**4. `.19` (LEMMA JB-AFF) emitted as ONE unit with its proof inside the CANONICAL STATEMENT.** **The shard's one deliberate exception to “proofs are not units”.** *Reason:* the source presents statement and proof as a single two-line display headed “(two lines, displayed)”, and splitting would produce a DERIVATION field longer than the statement. **Format observation: when a source displays a lemma AS a two-line object, the unit boundary should follow the display, not the template's statement/proof separation.**

**5. `.23` (JB-VTX(c)) kept as one unit though E-3 replaces half of it.** *Candidate A:* two units — the surviving slope/run content and the withdrawn ambient-lattice claim. *Candidate B (chosen):* one, with E-3's **CORRECTED DISPLAY quoted in full inside CONDITIONALITY**. **Reason:** E-3 issues a single replacement display, not two; and the load-bearing consequence (attained-grid counts route to (d4)) attaches to the clause as a whole. *Cost:* the longest CONDITIONALITY field in the shard. **Merge hazard flagged in §7 — a chapter cut must take E-3's display, never the frozen sentence.**

**6. `.56` (JB-BOX-2) kept WHOLE, including SURFACE 14.** **The shard's clearest merge decision.** *Candidate A:* split into the box (2322–2373) and surface 14 (2379–2420) — surface 14 is a REGENERATION with its own generating rows and is cited as “surface 14” from four other spans. *Candidate B (chosen):* one unit. **Reason:** surface 14 IS “this box's perimeter enumeration” — it has no existence apart from the box, and the r4/F-7 correction edits BOTH halves as one object (row 24's cells are “what JB-BOX-2 records”). Splitting would leave the box's CONDITIONALITY pointing at the surface for its own content. *Cost:* a 99-line source span quoted in three blocks. *Mitigation:* the three blocks are contiguous and their union is the whole box; the enumeration is additionally emitted as a `[TABLE]` with a full arithmetic audit.

**7. The four `∎ GRADE` surfaces as units (`.17`, `.27`, `.37`, `.52`) rather than folded into their theorems' CONDITIONALITY.** Test 1 and 2: each is a REGENERATION with a stated generating range (“§0M rows 1–6”, “7–13”, “14–18”, “19–23”), each is cited as “surface k of 14” from shard 1 and from JB-BOX-6, and each has its own arithmetic audit obligation under rule 22. *Not arguable* once the surface-generation freeze is seen as a freeze predicate.

**8. `.16`, `.26`, `.36`, `.51` (the struck grade lines) as units.** **Arguable.** *Candidate A:* not units — they are struck and superseded. *Candidate B (chosen):* units, because each also CONTAINS the live `*Proof.*` of its theorem (except `.51`), and because `.36`'s struck r2 line is the very edit that created the inconsistency PE3's F-1B names. *Honest cost:* `.51` contains no proof and is the weakest of the four; if the cross-read judges struck-only spans to be noise, `.51` is the unit to cut.

**9. `.02`–`.04` (the perimeter definitions and their two corrections) as three units.** Test 3: the definition (`.02`), the r3/F-4 correction to the consumer count (`.03`), and the r6/F-1 third consumer (`.04`) have three different rounds and are cited separately. *Alternative:* one §1-perimeter unit. *Rejected* — `.03`'s and `.04`'s content is a CHAIN whose TERMINAL a merge must be able to locate mechanically.

**10. `.54` (the carry-seed remark) as a unit.** **The most consequential small unit in the shard.** Two sentences, no proof of its own. *Kept* because it is **the entire J-C interface**, it is triple-fenced, GRTJC cites it from the other side, and §7.3's downstream notice attaches conditionality to it by name. A chapter cut that loses `.54` loses the only place the note says what it does and does not hand to the carrier block.

### 6.2 Merges deliberately NOT made

- **`.39`'s quoted (RM-m) box** stays inside the §5 setting unit rather than becoming its own “(RM-m)” unit: it is [RMG]'s statement quoted verbatim, not GRTJB's claim, and the note's own contribution is the RESTORATION of two dropped clauses.
- **`.41`'s parity corollary** stays inside the four-line theorem: it is one step of the same display and is cited only as part of it.
- **`.45`'s two `s_m` definitions** stay as one unit: they are defined as a contrasted PAIR and the load-bearing content is that they are NOT interchangeable.
- **The six JB-BOXes** are six units, not one “§6” unit: each has a different subject and three of them (BOX-2, BOX-4, BOX-6) carry live riders from different rounds.

### 6.3 Which template rules fought this note's genre (format evidence for the merge and the remaining prose shards)

1. **Rule 25's CHAIN needs a declared HOME when the chain crosses shards.** This shard applies the fix shard 1 §6.3 item 1 proposed — `CHAIN-MEMBER: <home>.<position>` at every member (`.14`, `.41`, `.42`, `.56`). **It works, and the merge should adopt it as a rule.**
2. **Rule 14's double-emission is needed far more often than the pilot expected.** This shard double-emits **nine** displays (`.02`, `.06`, `.12`, `.17`, `.24`, `.27`, `.37`, `.41`, `.45`, `.52`, `.56`) because the note's per-clause fences and per-step derivations are fixed-width ASCII that a Markdown-only transcription would silently reflow. **Fix: make double-emission the DEFAULT for any fixed-width block inside a `∎ GRADE` or derivation display, not just for tables.**
3. **A withdrawn-but-still-displayed statement has no TYPE.** `.23` is a live theorem clause **half of which is withdrawn by an annex that issues a replacement display**. It is not `superseded` (the frozen text stands), not `STALE-SELF-DESCRIPTION` (it is mathematics, not self-description), and not simply `scope-pin` (a false extension was removed, not a scope narrowed). **Fix: a `partial-withdrawal` SUPERSESSION KIND, whose field must carry the replacement display verbatim.** GRTJB has exactly one; GRTJC's Annexes #4/#5/#8 are the same shape and will need it.
4. **Rule 22's arithmetic audit found a real off-by-one in a surface's own range label** (`.52`: header says “rows 19–23”, the surface's fence lines cite only 19–22). **The rule is earning its keep on regenerated surfaces specifically** — a surface that declares its generating range invites exactly this check. **Recommend: require the audit on every unit whose statement declares a generating range.**
5. **(Confirming shard 1 §6.3 item 3.)** The `bred-defect` marker is needed here too: r2's grade-line addition at `.36` created the inconsistency PE3's F-1B names, and r4/F-4's re-scope left a leftover at surface 4 that r5/F-1 had to remove (`.37`). **Two more instances; the pattern is the arc's dominant failure mode and deserves a field.**

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (four inbound, plus one grade update).**
  (1) **E-1** → `.13`, `.47`, `.52`, `.56` (the “(R-coll)” label, root-inclusive). Provenance-rider; **E-1 certifies this note's operative fence was already correct**.
  (2) **E-2** → `.09`, `.30`, `.37`, `.56` (W2-C3's grade, at the supplier's 38/44 + 6/44 split). As-of scoping + provenance-rider.
  (3) **E-3** → **`.23`** (the corrected JB-VTX(c) display), and “slope/length” → “slope/abscissa-run” at `.27`. **Partial withdrawal with a replacement display; routes attained-grid counts onto matrix row 12, a frontier cell.**
  (4) **E-4** → `.11`, `.15`(consistency), `.17`, `.20`, `.27` (every “FALSE, not merely unproved” → “NOT SUPPLIED outside the stated perimeter”). Counter re-reading; **no matrix cell changes, no perimeter widened**.
  (5) **The 2026-08-08 supplier annex** re-grades **W-2 and J-A to ACCEPTED at 2/2**; **LED-Λ stays ATTEMPT and its rider is LIVE at `.34`/`.58`.**
- **Range-edge audit.** Head: L1301 `---`, L1302 blank, L1303 `## §1.` — the shard opens on a section header. Tail: L2454 closes JB-BOX-6 (`…is retired.]**`), L2455 blank, L2456 `---`, L2457 blank, L2458 `## §7.`. **No source statement unit is cut at either edge.** Both boundaries fall exactly on section breaks and are the manifest's own.
- **Outside-HOME material used only as resolver, never inventoried here:** the front matter and S-STATUS series; **§0M's matrix, columns, cell notes and summary points** (shard 1 `.11`–`.29` — the governing authority for `.17`, `.27`, `.37`, `.52`, `.56`); the grade cap (surface 1) and the retained superseded cap; the literature/consumption block; the eight repair-round blocks; §7.1–§7.4; the footer arc; the acceptance record; the fold annex; the supplier annex; the certifier annex.
- **Protocol versus supply.** §§1–6 ARE the supply; **no consumption append is claimed landed on any supplier, and none is invented.** Two supplier corrections were RECEIVED.
- **Numbering.** Temporary IDs `EFF.GRTJB.s2of3.01`–`.60`, to be reconciled at the merge run.
- **MERGE HAZARDS TO FLAG (six).**
  1. **`.23` MUST be read through E-3's CORRECTED DISPLAY.** The frozen sentence says the shear “preserves lattice data”; that is WITHDRAWN. **Any chapter cut quoting §3(c) from the body alone will state a false lemma.** Highest-severity hazard in this shard.
  2. **E-3 routes attained-slot/harness-grid counts to matrix row 12 (JB-VTX(d4)) — a FRONTIER cell.** The merge must carry that edge, or a downstream consumer will read a grid count as if it had (c)'s evidence rather than (d4)'s `NONE`.
  3. **The `u ≥ 0` chain spans four units here and two in shard 1**, with HOME at `s1of3.14`. The merge must install `.14`, `.41`, `.42`, `.56` → `s1of3.14` as explicit CHAIN-MEMBER edges and mark **`s1of3.77` TERMINAL**.
  4. **Surfaces 2–5 (`.17`, `.27`, `.37`, `.52`) and surface 14 (`.56`) are REGENERATIONS of `s1of3.20`.** The merge must install “§0M GOVERNS” edges from the matrix to all five, or FREEZE PREDICATE 2 is unenforceable across the cut. **Per-row sub-IDs on `s1of3.20` (shard 1's merge hazard 1) are the prerequisite.**
  5. **Two “FALSE” claims must NOT be conflated.** `.22`'s “the unsheared identification is FALSE in general” is a MEASURED fact (7,472 violations) and stands. `.11`/`.20`'s “(VAL)/(a) is FALSE off the perimeter” is WITHDRAWN by E-4. A grep for “FALSE” at the merge will collide.
  6. **`.54` is the sole J-C interface.** GRTJC's `(IN-4)`/§3.3 cite it from the other side; the gate is displayed and NOT retired on either side. The merge should install the reverse edge explicitly (`.54` ↔ GRTJC `(IN-4)`, §3.3, §10.3).

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — E-3's routing puts a downstream consumption on a frontier cell, and nothing states the consequence

E-3 withdraws JB-VTX(c)'s ambient-lattice claim and routes every attained-slot/harness-grid COUNT to JB-VTX(d4) = matrix row 12, saying “Its existing membership residue and NO-LEG status therefore remain visible; the four-member frontier is unchanged.” **The frontier count is indeed unchanged — but the LOAD on row 12 is not.** Before E-3, a consumer wanting a grid count could read it off (c), a fully IND-backed clause; after E-3 the same count carries row 12's `NONE` evidence AND the open membership residue. **No line of the note states that the evidentiary standing of grid counts DROPPED.** The compiler recorded the routing verbatim at `.23` and refused to editorialise. **Decision needed: whether the merged spec adds a consequence line — “after E-3, attained-grid counts inherit row 12's evidence class” — and whether any downstream unit (W-3's hand-off in §7.3) relies on grid counts at (c)'s old standing.**

### OPEN-CALL 2 — `.52`'s generating range says “rows 19–23”; only 19–22 appear

Surface 5's header declares “REGENERATED FROM §0M rows 19–23”, but its six fence lines cite rows 19, 20, 21, 22 only. Row 23 (JB-BOX-1) is graded separately at `.55`/shard 1 `.36`. **No fence is missing and no cell moves** — this is a range-label over-statement, not a coverage gap. But it is exactly the class of defect §0M was built to catch (a surface whose declared relation to the table is not the relation it has), and it survived eight rounds. **Decision needed: whether the merged spec corrects the range label to “19–22 (row 23 at JB-BOX-1)” or records it as a source defect only.** The compiler did the latter (source defect 2).

### OPEN-CALL 3 — the `(B-READ)` shorthand is resolved in-note but unresolvable from the DAG

`(B-READ)` has fixed-string count **0** in `RMENGINE_2026-08-08.md`; r1/G-7 resolves it in prose to “[RMG] S2.1's LEMMA L-CELL clause (ii)”. **A merge run building the DAG by designation will find no edge**, and the proof step it licenses (`.49`'s “forcing `w_m(R) ≤ λ + γ_{m+1}`”) is load-bearing for JB-CREAD's weight pin. **Decision needed: whether the merged spec emits a synthetic edge `GRTJB §5 → RMENGINE L-CELL(ii)` on the strength of the note's own resolution, or carries `(B-READ)` as an unresolved local tag.** Same question applies to `REALIZE R1`/`R3` (`.33`, `.44`). The compiler emitted NEAR-MISS dispositions and no synthetic edges.

### OPEN-CALL 4 — the internal-edge transfer is NOT derivable in-list, and the one candidate route is fenced by a roster fact

`.34` records that extending `line = v_{m+1}` to internal cells is **not derivable within this note's consumption list**, and that the one outside route (HigherNewton tex ~1012's valuation multiplicativity) is NOT TAKEN because “the Φ_l atom value rests on the single-digit weight recursion, which degenerates where `deg Φ_q = deg Φ_l` (interior periods `P_t = 1` — realized on this note's own roster, e.g. T3E's `P_1 = 1`) and there needs a two-digit-development case argument consuming WELL-DEF data one level down”. **That is a precise, self-contained statement of a missing lemma**, and the note names both the obstruction and the data a proof would need. **Decision needed at 0b/chapter time: whether to prove the two-digit-development case and take the route (which would upgrade JB-TREE(iii) from a leaf reading to a per-edge classifier reading), or to formalize the leaf-only scope as the permanent statement.** Not a claimed error; recorded because a formalization blueprint will meet the choice.

### OPEN-CALL 5 — LED-Λ's ATTEMPT grade rides at HEAD with no upgrade path recorded

`.34`, `.37` and `.58` all carry “LED-Λ is consumed at ATTEMPT grade and the tie's grade rides it”. The 2026-08-08 supplier annex upgraded W-2 and J-A to ACCEPTED at 2/2 but **says nothing about LED-Λ**, and no other append does. So **JB-TREE(iii)'s grade is capped by a supplier at attempt grade, at HEAD, on an ACCEPTED note.** The note's own mitigation is real (the runner re-verifies λ_E FRESH — “decorrelation, not redundancy”), but the grade rider is not discharged by it. **Decision needed: whether LED-Λ's arc is queued, or whether JB-TREE(iii)'s dependence should be re-expressed as a dependence on the FRESH machine re-verification plus the two displayed equalities, which is what the proof actually uses.**

### Recorded source defects (flagged, not silently repaired)

1. **`.49`, `.33`, `.44`:** three note-local compound designations with fixed-string count 0 in their targets — `(B-READ)` (referent `L-CELL` (ii), count 11), `REALIZE R1` (parent `REALIZE` 17, label `R1` 9), `REALIZE R3` (label `R3` 4). All three referents verified; NEAR-MISS dispositions emitted. See OPEN-CALL 3.
2. **`.52`:** surface 5's declared generating range “rows 19–23” over-states by one; only rows 19–22 carry fence lines. No fence missing. See OPEN-CALL 2.
3. **`.28`, `.79`(shard 1):** the note pins “GmnLeg L211 via gmn_from_tower L456–459” without naming the file; both pins are in `verification/openmath/grt_weld_probe.py`, not in `grt_jb_checks.py` named two clauses earlier. **This compiler verified both at the correct file: EXACT.** File-attribution ellipsis; referent unambiguous.
4. **`.06`, `.23`, `.24`:** the print anchors are cited by TeX LINE NUMBER (“tex ~1370”, “tex 1377”, “tex ~1395”, “tex 1431”) rather than by GMN theorem number. The labels themselves (`propertiesv`, `shape`, `rescoeff`, `defresidual`, `phiradic`) grep-verify, and NS-11 supplies the theorem numbers (Prop 2.7, Lem 2.17, Thm 2.11). **Line-number pins are fragile against any re-typesetting of the source**; recorded as a citation-robustness defect, not an error.
5. **`.22` vs `.11`/`.20`:** the note uses “FALSE” for two different things — a measured falsity (the unsheared identification, 7,472 violations) and an unsupported off-perimeter negation (withdrawn by E-4). The two are distinguishable only by context. See merge hazard 5.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or explicitly `[ASSEMBLED]`. **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** Truncations are marked `…` and are used in six long bracketed riders (`.03`, `.11`, `.28`, `.41`, `.51`, `.56`) whose omitted spans are quoted at their own units in shard 1.
- **Strike markup is preserved inside quotations.** In this range the struck text is repeatedly a FALSE MATHEMATICAL STATEMENT the note keeps on the record (`.25`'s window clause as literally read, `.33`'s “every node is a sum of reduced cells”, `.34`'s internal-edge transfer, `.47`'s “m = 2 by JA-RES”); dropping the strike would erase the note's own refutations.
- **Nine fixed-width displays are DOUBLE-EMITTED** (rule 14) — `.02`, `.06`, `.12`, `.17`, `.24`, `.27`, `.37`, `.39`, `.41`, `.45`, `.52`, `.56` — verbatim, then as `[TABLE]`. **Four regenerated surfaces carry a mandatory arithmetic audit** (rule 22); one found a real off-by-one (`.52`).
- **68 external XREF designations, every one grep-verified with a fixed-string count ≥ 1 recorded inline and in §3.1.** Three candidate designations with count 0 are explicitly NOT emitted and are recorded as source defect 1. Two §-anchor XREFs (`LEDGERLAMBDA:S1`, `GRTW2:3.4`) carry upper-bound caveats with independently pinned referents.
- **Three source-code line pins re-read at HEAD: 3/3 EXACT.** Four md5 pins re-computed: 4/4 EXACT. Eight report files and twelve battery artifacts verified to exist. **Two XREF counts asserted in an earlier draft of `.54` were WRONG and were corrected against the file before commit** (`JB-CREAD` is 2, not 4; `JB-EPS` is 4, not 3) — recorded here because the fidelity rule is that counts come from the grep, never from memory.
- **CITE-SCOPE handled per resolution rule 8:** the NS-11 retarget is recorded ONCE in full at `.21` as a READING NOTE with the ℚ_p-only source scope confirmed at `HigherNewton.tex` line 401, the three retargets quoted with their verdicts, and the normalization-shear obligation named. **Recorded, not applied.** `.24`, `.06` and `.23` reference it rather than repeating it.
- **Q7 GENERALITY NOTES recorded, not applied, at five units** (`.44`, `.45`, `.46`, `.50`, `.59`) — every one a **BENIGN** or **GOOD BOOKKEEPING** classification, quoted verbatim. **The only CITE-SCOPE hazard Q7 raises against this note is H6 at the GMN print anchors**, handled at `.21`.
- Status and mathematical content are kept as distinct predicates: the four `∎ GRADE` surfaces are REGENERATIONS of §0M, never independent authorities, and each says so.
- Out-of-range material is used only to resolve in-range HOME units; shards 1 and 3 own the front matter/§0M and §7/annexes respectively.
- **Honest limitation of this shard:** the governing matrix, all eight repair-round blocks and all four annex corrections are physically in other shards. Every affected unit quotes the governing corrective text verbatim, so shard 2 is self-contained as a *reading*, but the merge run must still install the six edges listed in §7.

EFF-GRTJB-s2of3 COMPILED: 60 statements / 68 xrefs verified / 5 open calls
