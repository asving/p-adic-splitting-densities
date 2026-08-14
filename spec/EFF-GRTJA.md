# EFF-GRTJA — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md` (1,134 lines / 73,169 bytes).

**HEAD blob hash:** `46fea35bef85041666525f749372a7a2463afa8f`. Whole-file md5 at compile time: `d63ceda390c85ea452ec945a55d1eeb1`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28. Full compilation, unsharded (73 KB).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

### Effective-text rule

The freeze is stated at the acceptance record (L869–872):

> “**FREEZE-CONVENTION STAMP** (the s2 item, W2 precedent): the accepted
> text is the post-r5 body, md5 cba309ce, byte-frozen since f131c53; both
> clean passes read that identical text; this record and any future annex
> are dated appends — the frozen body is never edited inline.”

**PIN VERIFIED and localized:** the md5 of the file's first **850** lines begins `cba309ce` — a **unique hit** over all line boundaries ✓; `f131c53` is a commit ✓.

**Therefore the effective text is: the frozen body L1–850 read with its inline `[JA-r1]`…`[JA-r5]` bracket repairs applied in place, then the dated appends in order — the ACCEPTANCE RECORD with its FREEZE stamp, WHAT IS ACCEPTED and FOLD-CARRY INVENTORY; the four fold-carry annexes FC-1…FC-4 (2026-08-08); the sol C2/E2 adjudication with its four certifier repairs C2-1…C2-4 (2026-08-12); and the post-D3a corrigendum (2026-08-12).** No body text is edited by any append.

### FREEZE PREDICATES (rule 21 — three)

**FREEZE-1 — text freeze.** md5 prefix `cba309ce` at line **850** ✓ (unique), anchored at commit `f131c53` ✓. The stamp adds a property no other note in queue 8b asserts: “**both clean passes read that identical text**” — i.e. the freeze predates and covers both acceptance passes, not merely the acceptance.

**FREEZE-2 — instrument freeze.** §7.1 pins the sealed runner at **seal commit `696eae8`** ✓ with artifacts `grt_ja_checks_output.txt` / `grt_ja_checks_results.json`, both EXIST ✓. **Disposition: `UNPINNED-VALUE`** — the note pins the runner by commit, not by md5.

**FREEZE-3 — supplier as-of pins.** `[W2 @ ffa1e57]` ✓ (commit), `[ILN]† consumed as-of ced7dbb` ✓ (commit). **These are as-of pins on notes that have since moved**, which is exactly what FC-1 records (`.26`).

### Supersession chains

`[TABLE]`

| # | Target (frozen text) | Layer 1 (`[JA-r1..r5]`) | Layer 2 (FC annexes, 08-08) | Layer 3 (C2/E2, 08-12) | Layer 4 (D3a, 08-12) | TERMINAL |
|---|---|---|---|---|---|---|
| C-1 | **THEOREM JA-EPS** — raw print-twist equality `ε_m(β) = z_m^{−t_m(β)}` | — | — | **C2-1: `THEOREM JA-EPS-CORR`** — JA-EPS is the *canonical-normalization* bridge, not raw Definition-`t(i)` equality; raw equality holds iff `z^ν = 1` | — | **C2-1** (`.31`) |
| C-2 | The ordinary-degree/support statements | — | — | **C2-2: degrees and supports shifted by ν** (`COROLLARY JA-MIN-CORR`) | — | **C2-2** (`.32`) |
| C-3 | JA-BOX-1's refutation criterion (“nonidentity”) | — | — | **C2-3: nonidentity is weaker than failure of a scalar gauge** — the criterion is `|χ(S_A)| = 1` | **corrigendum: `|χ(S_A)| ≤ 1`** (empty-support corner) | **the D3a corrigendum** (`.33`) |
| C-4 | THEOREM JA-GRID's unconditional reach | — | — | **C2-4: `THEOREM JA-GRID-CORR`** — only the arithmetic grid and carry are unconditional; the print T-point needs `u(V) ≥ 0` | — | **C2-4** (`.34`) |
| C-5 | §1's “ITERLAWN_PROOF motion-free since” | — | **FC-1: no longer motion-free** (two appends since `ced7dbb`) | — | — | **FC-1** (`.26`) |
| C-6 | §5's suppliers billed “(0/2 hostile passes)” | — | **FC-2: JB/JC/W2/WM since ACCEPTED** | — | — | **FC-2** (`.27`) |
| C-7 | The grade-cap's attempt-grade billing | — | **FC-3: the W-2 cap is now an accepted supplier** | — | — | **FC-3** (`.28`) |
| C-8 | §3.2's “cure owed to that note's own arc” | — | **FC-4: the W-2 arc closed** | — | — | **FC-4** (`.29`) |
| C-9 | The header's arc/counter surfaces | `[JA-r2]` (FINDING 4: stale “no acceptance arc opened”), `[JA-r4]` (FINDING 1: stale “next pass = JA-PE3”) | — | — | — | **`[JA-r4]`**, then **ACCEPTANCE 2/2** (`.24`) |
| C-10 | JA-MIN's close (“a theorem WHERE THE DICTIONARY REACHES”) | `[JA-r1]` **RESCOPED** to the DICTIONARY HALF only | — | C2-2's `JA-MIN-CORR` | — | **C2-2** |
| C-11 | JA-BOX-2's “hold only on (R-coll)” | `[JA-r1]` (overstated) → `[JA-r2]` (root-INCLUSIVE, 8 machine witnesses) | — | — | — | **`[JA-r2]`** |
| C-12 | §7.1's “across 12 roster rows” | `[JA-r1]` **corrected to 10** (PE1 recount + bit-identical re-run) | — | — | — | **`[JA-r1]`** |

**Note the shape.** Four of the twelve chains are **certifier repairs to accepted, frozen statements** (C-1…C-4), landing four days after acceptance; four are **fold-carry closures of stale supplier billings** (C-5…C-8); four are **in-arc repairs** (C-9…C-12). **The C2/E2 wave includes a CRITICAL** — the only one in queue 8b — cured by `THEOREM JA-EPS-CORR`.

### Scope of record — three-predicate split

#### A. Supply set

§7.3: “**What J-A now supplies (at attempt grade, hostile passes owed):** the blueprint's W-0 in full; W-1's (i)/(iii) in full on the shared-key perimeter and (ii) in the corrected per-slot form (unconditional at m ≤ 2, proviso-scoped above); W-4 in full.” Six named theorems (JA-PIN, JA-VAL, JA-EPS, JA-GRID, JA-RES, JA-VDIND), one corollary (JA-MIN), five boxes, one **REFUTATION** of a blueprint display (JA-BOX-1).

#### B. Consumption / append-protocol scope

§7.3: “**CONSUMED BY (intended):** the W-3/W-4 development unit (J-B), the W-5 tree unit, the weld campaign ledger at J-A.” **This note lands nothing on another note** — it consumes and is consumed. Its outbound obligation is a **blueprint correction**: JA-BOX-1 is “review-owed” against `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` (EXISTS ✓), and the note does not edit the blueprint. **`STALE`-risk recorded** at `.25`.

#### C. Inbound corrections RECEIVED

Eight hostile passes (PE1–PE8, five repairs) plus the sol C2/E2 wave (4 REAL, 1 CRITICAL) plus the D3a discharge (1 NEW-ISSUE corrigendum) — **the longest correction history in queue 8b.**

### Resolution rules applied

1. `[JA-rN]` brackets are in the frozen body and apply in place; each carries a wallclock date distinct from its campaign date, and this compilation preserves both as written.
2. Appends apply in order: ACCEPTANCE → FC-1…FC-4 → C2-1…C2-4 → the D3a corrigendum. **C2-3 is superseded by the corrigendum**, so its box has two layers.
3. The frozen grade vocabulary (“attempt grade”, “counter 0/2”, “acceptance arc OPEN”) is superseded by the ACCEPTANCE record (2/2) and, for suppliers, by FC-2/FC-3/FC-4.
4. **A REFUTATION is effective text.** JA-BOX-1 refutes a blueprint display with 26 machine witnesses; it is compiled as a `[fence]` with the refutation as its content, and C2-3 corrects its *criterion*, not its verdict.
5. Out-of-note material (W-2, ILN, the blueprint, the completion tree, the ledgers) resolves and verifies only.

### Quotation discipline

Every CANONICAL STATEMENT is verbatim or `[ASSEMBLED]`. The note's two Markdown tables (§7.1 machine bracket, §7.2 claims) are transcribed as `[TABLE]`. **Rule 14 is not triggered** — the note contains no fixed-width ASCII table inside a code fence (checked, not skipped). LaTeX in the C2 annexes is reproduced as written.

---

## 2. NON-IMPORTS

**N-1 — the explicit NOT-supplied list.** §7.3:

> “**NOT supplied:** W-1's
> uncollapsed all-orders scalar dictionary (JA-BOX-2), W-2's own grades
> (consumed, not upgraded), W-3/W-5 (J-B), the J-C block (no gr claim;
> BLOCKED-ON-CARRIER-TIE stands), J-D counts/menus, W2-OPEN-1. The P0
> application gate stands.”

**N-2 — the graded-initial-form leg is neither derived nor cited.** `[JA-r1]` at JA-MIN: “The graded-initial-form leg (the in(f) tie, a graded-carrier object) is NEITHER derived NOR cited in this note and stays OPEN with GD-3”.

**N-3 — nothing upgrades W-2.** §5: “Nothing here upgrades W-2's grades.”

**N-4 — no ℓ is pinned by the print.** JA-BOX-3: “the print pins no ℓ (tex 1291) … **Nothing downstream may consume a pinned**” ℓ-reading as if the print supplied it.

**N-5 — no PARI on the equal-characteristic side.** JA-BOX-4: “The print is mixed-characteristic; the F_p[[t]] instance is the displayed equal-characteristic deferral — construction-identical, machine-covered, **no PARI leg**.”

**N-6 — principal reads only.** JA-BOX-5 and JA-PIN clause 2: “Slope-0 legs never enter a type; they are dispatched by Hensel/L1 at order 0 … so the weld quantifies over **principal reads only**”.

**N-7 — N-1 (the order-2 base) does not cover three things.** §5: “N-1 does NOT cover: the carrier identification (C15 separation), orders ≥ 3, the lift construction (that is W-2).”

---

## 3. Statement inventory

IDs `EFF.GRTJA.01`–`.36`.

### EFF.GRTJA.01  [record]

**CANONICAL STATEMENT** (verbatim, L3–26 — the Unit block with both arc-normalizing brackets). FORM: bold-headed paragraph with two nested `[JA-r]` brackets.

> “**Unit:** J-A COMPOSER (weld dependency order: consumes W-2 clause 1 at attempt
> grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S2.1/S3.1
> rows W-0/W-1/W-4). **Genre: PROOF NOTE at attempt grade (acceptance ARC
> OPEN: round 1 = the 2026-08-04 JA-PE1 pass (gaps-only, repaired at r1),
> round 2 = JA-PE2 (1 critical + 3 gaps + 1 minor, repaired at r2 below),
> round 3 = JA-PE3 (CLEAN; counter reached 1/2), round 4 = JA-PE4
> (0 critical + 1 gap, repaired at r3; counter reset), round 5 = JA-PE5
> (0 critical + 1 justification gap (minor), repaired at r4 below), round 6
> = JA-PE6 (0 critical + 2 justification gaps (both minor, both
> arc-accounting), repaired at r5 below);
> counter 0 CLEAN passes of the 2 consecutive required; no gate fires; next
> pass = JA-PE7 = the acceptance attempt), with sealed-runner machine
> brackets** (`verification/openmath/grt_ja_checks.py`, two-commit seal).
> [JA-r2 2026-08-08 (wallclock 2026-08-06), per JA-PE2 FINDING 4: the stale
> "no acceptance arc opened" header contradicted §8's own r1 record ("round
> 1 of the acceptance arc") at HEAD; the counter is normalized to the
> 0/2-CLEAN convention at every surface (§8's "0/1" denominator wobble
> included).] [JA-r4 2026-08-08 (wallclock 2026-08-07), per JA-PE5
> FINDING 1: the r3 repair left this genre line reading "next pass =
> JA-PE3" (and §7.3 "next = PE3") against §8's own r3 record ("rounds 1–4
> complete … next pass = JA-PE5") at HEAD — PE4's n3 staleness warrant
> ("no repair round since") lapsed when r3 edited the note; the r2
> FINDING-4 normalization re-applied at both live surfaces (round
> inventory extended through PE5, next pass named).]”

**DERIVATION.** [RECORD]. **SERIES:** ARC SERIES member 1 (`.01` → `.26`–`.28` (§8 rounds) → `.24` ACCEPTANCE → `.36` ledger).

**CONDITIONALITY.** The whole arc half is **SUPERSEDED** by `.24` (ACCEPTED 2/2, eight passes, five repairs). **Two of the note's own repairs were about arc-record staleness** (`[JA-r2]` FINDING 4, `[JA-r4]` FINDING 1) — recorded because it makes GRTJA the queue's clearest case of *arc bookkeeping itself* becoming a repeated hostile-pass finding.

**XREF.** `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — EXISTS ✓; `verification/openmath/grt_ja_checks.py` — EXISTS ✓.

---

### EFF.GRTJA.02  [scope-record]

**CANONICAL STATEMENT** (verbatim, L28–38 — the grade cap). FORM: bold-headed paragraph.

> “**Grade cap (read first).** J-A-PIN (§2) is PROVED at attempt grade (its
> legs are the print's own definitions plus one one-line argument), with its
> lift clause consumed from W-2 clause 1 AT ATTEMPT GRADE and W-2's
> conditionality [carried] … the J-A(ii) "slot-independent c" form is false at
> m ≥ 2 (JA-BOX-1). Nothing …”

*(Quoted to its two load-bearing clauses; the intervening text is the conditionality carry-list, compiled at `.21`.)*

**DERIVATION.** [RECORD of a grade cap], placed first in the note by design (“read first”).

**CONDITIONALITY.** **SUPERSEDED in its billing** by **FC-3** (`.28`): “the W-2 cap now an accepted supplier”. The *cap's structure* — J-A's grade is capped by its consumed supplier — survives; only the supplier's grade moves.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — EXISTS ✓.

---

### EFF.GRTJA.03  [definition]

**CANONICAL STATEMENT** (verbatim, §2 L102–108 — the dictionary map T). FORM: bold-headed paragraph with an indented display.

> “**Definition (the dictionary map T).** For a realized principal-read OM type
> t of order r on a separable monic f ∈ O[x], O ∈ {ℤ_p, F_p[[t]]} — GMN data
> (φ_i, λ_i = −h_i/e_i, ψ_i)_{i≤r}, f_i = deg ψ_i, φ₁ the order-0 key — set
>
>     T(t) := ( Φ₀ := φ₁;  reads (e_j, h_j, g_j) := (e_{j+1}, h_{j+1}, f_{j+1})^GMN,
>               j = 0..r−1;  residue chain K_{j+1} := K_j[z_{j+1}]/(ψ_j),
>               ψ_j := ψ_{j+1}^GMN;  weights by the harness recursion )”

**DERIVATION.** [DEFINITIONAL] — **the junction object of the whole note**: it is the map from *print (GMN) type data* to *harness (tower) data*, and every one of the four operator equalities is a statement that `T` intertwines a print operator with a harness operator.

**CONDITIONALITY.** The **index shift** is load-bearing and easy to misread: harness read `j` corresponds to GMN datum `j+1`. Every equality inherits it (JA-VAL's `w_m = v_{m+1}` is the shift made explicit). Recorded because a consumer off by one gets every theorem wrong.

**XREF.** none external.

---

### EFF.GRTJA.04  [theorem]

**CANONICAL STATEMENT** (verbatim, §2 L110–111, plus the eight clauses at L112–180). FORM: bold-headed theorem with a numbered clause list.

> “**THEOREM JA-PIN.** T(t) satisfies every clause of the [ILN]† S0.1 class pin
> EXCEPT the lift clause, each clause forced by the print's own hypotheses:”

with clause 2 (the load-bearing positivity clause) verbatim:

> “2. **e_j ≥ 1, h_j ≥ 1, gcd(e_j, h_j) = 1.** The print DEFINES every side
>    slope as λ = −h/e "with h, e positive coprime integers" (tex 220 order
>    one; tex 828 type datum; tex 912 order r). Positivity of h is the
>    PRINCIPAL restriction: types are built from the principal polygon
>    N_r^−(f), the negative-slope sides only (tex 449, 1377). Slope-0 legs
>    never enter a type; they are dispatched by Hensel/L1 at order 0 (the
>    machine-checked capstone leg), so the weld quantifies over principal
>    reads only — displayed, blueprint pin honored.”

and clause 5 (the one clause carrying an argument rather than a citation):

> “5. **ψ_j(0) ≠ 0.** The print requires ψ ≠ y (tex 829/882; used again at tex
>    1149: "the residual polynomials are never divisible by y, and
>    ψ_{r−1}(y) ≠ y"). One line: if ψ(0) = 0 then y | ψ, and ψ monic
>    [irreducible forces ψ = y] …”

**DERIVATION.** Seven clauses are **print citations by tex line number**; clause 5 adds “one one-line argument” (the grade cap's own phrase). **Clause 8, the lift clause, is NOT proved here** — it is consumed from W-2 (`.24`).

**CONDITIONALITY.** Grade at HEAD: PROVED, and the note's own §7.2 row reads “PROVED (attempt grade 0/2)” — **`STALE-SELF-DESCRIPTION`** after `.24` (ACCEPTED 2/2). The **tex-line citation discipline** (every clause pinned to a numbered line of the print) is the note's characteristic evidence form and is what makes JA-PIN checkable against a source outside this repo.

**Machine leg.** §7.1: JA-PIN family, **111 samples**, clauses 2–7 re-verified by fresh legs on every level of 16+5+4 towers ✓ — so seven of eight clauses have both a print citation and a machine check.

**XREF.** `[ILN]†` — the print; consumed as-of `ced7dbb` ✓ (commit).

---

### EFF.GRTJA.05  [theorem]

**CANONICAL STATEMENT** (verbatim, §3.1 L188–192). FORM: bold-headed statement.

> “**Statement.** For every m ≥ 0 and every nonzero A ∈ O[x]:
> w_m(A) = v_{m+1}(A), where v is the print's MacLane/GMN valuation of the
> type prefix (order-one v₁ = min coefficient π-valuation, tex ~460 region;
> order-r recursion v_r(A) = min_i (e_{r−1}·v_{r−1}(a_i) + i·v_r(φ_{r−1})),
> Prop `propertiesv` item 3, tex 1028, hypothesis: φ_{r−1}-adic development).”

**DERIVATION** (verbatim, L194–208):

> “*Proof.* Induction on m. Base m = 0: w₀ = min coefficient valuation = v₁ by
> definition on both sides. Step: under shared keys the φ_{m+1}-adic dev IS
> the Φ_m-dev (same monic key, same canonical division), and the two
> recursions are the same integer min — v_{m+2}(A) = min_i(e_m^har·v_{m+1}(a_i)
> + i·v_{m+2}(φ_{m+1})) with v_{m+2}(φ_{m+1}) = γ_{m+1} (JA-PIN clause 7)
> versus w_{m+1}(A) = min_i(e_m·w_m(a_i) + i·γ_{m+1}); the inductive
> hypothesis identifies the arguments. ∎ Grade: PROVED (attempt grade),
> unconditional on the shared-key perimeter. This is the P-index pin
> v_i = w_{i−1} PROVED rather than assumed; it is stated in the GD-2 frame
> normalization (the sheared eq-(12) presentation of ordinates — the T-F
> machine check's convention pin) — the identity lives at the v-level where
> no shear ambiguity exists.”

**Audit.** The induction is clean: the two recursions are literally the same expression once `v_{m+2}(φ_{m+1}) = γ_{m+1}` (JA-PIN clause 7) identifies the second argument ✓, and the base is definitional ✓. **The closing observation is the important one**: the identity is placed “at the v-level where no shear ambiguity exists”, which is why JA-VAL is the one equality unaffected by the convention question JA-BOX-3 raises.

**CONDITIONALITY.** “unconditional **on the shared-key perimeter**” — the perimeter is the standing hypothesis of §3 and must travel with every one of the four equalities.

**Machine leg.** CK-VAL, **1,132 samples**, “both engines on the same samples, every shared level of every roster/QO/d₀ ≥ 2 tower” ✓ — and tooth **MJ-VAL** (“unsheared v 11/11”) certifies that the shear convention is load-bearing.

**XREF.** `docs/MATH_COMPLETION_TREE_2026-08-01.md` — EXISTS ✓ (GD-2's T-F check).

---

### EFF.GRTJA.06  [theorem]

**CANONICAL STATEMENT** (verbatim, §3.2 L210–216). FORM: bold-headed statement with a sign convention.

> “**Statement.** For every m ≥ 1 and every β ∈ ℤ in the level-m weight
> lattice: ε_m(β) = z_m^{−t_m(β)}, where t_m(β) := (ℓ_{m−1}β − s(β))/e_{m−1}
> evaluated at the point of ordinate-argument β on its own side, s(β) =
> ℓ_{m−1}β mod e_{m−1} (integrality by W2-L0). SIGN CONVENTION (explicit):
> t_m carries the Prop-`construct` CHILD orientation (ℓu − 𝔰)/e — the child
> prescription φ_j(y) ≡ y^{(ℓ_{r−2}u_j−𝔰_j)/e_{r−2}}c_j(y), tex 1200–1201;”

**DERIVATION.** The proof runs through W2-L0's integrality and the print's child prescription; the note's own machine leg is CK-EPS (872) and ORB-EPS (1,744).

**⚠ SUPERSEDED — this is the CRITICAL finding.** **C2-1** (`.31`) establishes that JA-EPS as displayed **omits the attained-origin shift**: the raw equality with Definition-`t(i)` holds only when `z^ν = 1`. The governing form is **`THEOREM JA-EPS-CORR`**, the canonical-normalization bridge. **CHAIN:** frozen JA-EPS → C2-1. **TERMINAL: C2-1.** **SUPERSESSION KIND:** `replacement`.

**Arithmetic audit of the correction's mechanism** (from the E2 provenance, re-derived): with `s_act = s_min + νe`, substitution gives `t_Def = ν − t_min`, hence `z^{t_Def} = z^{ν}·ε_m(β)` ✓ — **so raw equality holds iff `z^ν = 1`** ✓, exactly as C2-1 states. **The frozen statement is therefore true precisely on the `ν = 0` (attained-origin) locus and false off it.**

**CONDITIONALITY.** C2-1's own consumer sweep: “**W2-L2, W2-L3, CK-EPS, and ORB-EPS survive as statements**” — the machine legs tested the corrected relation's content, not the raw one. Recorded at `.31`.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — EXISTS ✓ (W2-L0/L2/L3).

---

### EFF.GRTJA.07  [theorem]

**CANONICAL STATEMENT** — §3.3 THEOREM JA-GRID (J-A(iv)): “eq-(12-int) digits = abscissa/side coordinates, + the carry clause” (L238–288). FORM: `###`-headed section with statement, carry clause and proof.

**DERIVATION.** §3.3's own argument, with the order-1 layer riding GD-8's exact-key harness (871 forced samples, 0 findings) per `.13`.

**⚠ SUPERSEDED (scope).** **C2-4** (`.34`) establishes that **only the arithmetic grid and the carry clause are unconditional**; the print T-point additionally needs `u(V) ≥ 0`. Governing form: **`THEOREM JA-GRID-CORR`**. **SUPERSESSION KIND:** `scope-pin`. **TERMINAL: C2-4.**

**CONDITIONALITY.** §7.2 already grades it “PROVED (**single-level scope fence**)”, so the note carried a scope fence before C2-4 narrowed it further. C2-4's consumer sweep: “Section 3.3's own Prop-`construct` sites survive because the print hypothesis supplies the required nonnegative `T`-side there.”

**Machine leg.** CK-GRID, **3,248 samples** ✓, plus tooth **MJ-GRID** (“garbled grid 12/18 catches”).

**XREF.** none new.

---

### EFF.GRTJA.08  [theorem]

**CANONICAL STATEMENT** (verbatim, §3.4 L307–316 — THEOREM JA-RES, the per-slot law). FORM: bold-headed theorem with an indented display.

> “**THEOREM JA-RES (per-slot law).** Level m ≥ 2, shared keys below m. IF
> (VD-(m−1)) holds at every on-line digit a_i of A (the PER-DIGIT PROVISO),
> THEN for every attained abscissa i:
>
>     c_i = z_{m−1}^{−i·A_{m−1}} · C_i .
>
> The print's order-m residual coefficient equals the harness packed digit
> times the PURE CHARACTER z_{m−1}^{−i·A_{m−1}} in the abscissa. At m = 2 the
> proviso is (VD-1) = W2-L3: **the law is UNCONDITIONAL at m = 2.**”

**DERIVATION** (verbatim, L318–324):

> “*Proof.* By the proviso, R_{m−1}(a_i)(z_{m−1}) = z_{m−1}^{−τ_{m−1}(a_i)}·
> ε_{m−1}(β_i)·R_{m−1}v(a_i) = z_{m−1}^{−τ_{m−1}(a_i)}·C_i. So c_i =
> z_{m−1}^{t(i) − τ_{m−1}(a_i)}·C_i, and with u_i = β_i + i·W_{m−1} (both
> ordinates of the same on-line point, W_{m−1} = w_{m−1}Φ_{m−1} = the print's
> v_m(φ_m), JA-PIN clause 7):
>
>     t(i) − τ_{m−1}(a_i) = [s_{m−1}(a_i) − ℓ_{m−2}u_i − s_{m−1}(a_i)
>         + ℓ_{m−2}β_i]/e_{m−2} = −ℓ_{m−2}·i·W_{m−1}/e_{m−2} = −i·A_{m−1}. ∎”

**Mandatory arithmetic audit (rule 22) — the exponent computation re-derived.** `t(i) − τ_{m−1}(a_i)`: the two `s_{m−1}(a_i)` terms cancel ✓, leaving `[−ℓ_{m−2}u_i + ℓ_{m−2}β_i]/e_{m−2} = −ℓ_{m−2}(u_i − β_i)/e_{m−2}`; with `u_i = β_i + i·W_{m−1}` this is `−ℓ_{m−2}·i·W_{m−1}/e_{m−2}` ✓, i.e. `−i·A_{m−1}` with `A_{m−1} := ℓ_{m−2}W_{m−1}/e_{m−2}` ✓. **The cancellation is exact and the character is purely abscissa-linear** — which is precisely what makes JA-BOX-1's slot-independent form false (`.15`).

**CONDITIONALITY.** **Unconditional at `m = 2`** (the proviso is W2-L3, consumed); **proviso-scoped at `m ≥ 3`**, and “unconditional on (R-coll) (root-inclusive as defined above, `[r2]`)”. **C2-1's consumer sweep explicitly preserves it**: “Section 3.4 JA-RES survives unchanged: it uses the actual Definition-`t(i)` exponent”.

**Machine leg.** CK-RES **443 scored**, with a **16-row boundary census** (proviso-failing, recorded not scored) — see `.20`.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — W2-L3 consumed; EXISTS ✓.

---

### EFF.GRTJA.09  [corollary]

**CANONICAL STATEMENT** (verbatim, §3.4 L326–331 — COROLLARY JA-VDIND, to its boundary clause). FORM: bold-headed corollary.

> “**COROLLARY JA-VDIND (the induction step and its exact boundary).** Under
> the per-slot law, (VD-m) holds for A IF the slot character is trivial
> ABSOLUTELY on A's attained abscissas: z_{m−1}^{i·A_{m−1}} = 1 for every
> attained i (sufficient: A_{m−1} = 0, i.e. e_{m−2} = 1; or
> ord(z_{m−1}) | A_{m−1} and the abscissa condition; NOT sufficient: …”

**DERIVATION.** Immediate from `.08`: if the character is absolutely trivial on the attained support, the per-slot law collapses to `c_i = C_i`, which is (VD-m).

**CONDITIONALITY.** **“ABSOLUTELY” is the load-bearing word** — JA-BOX-2's `[JA-r2]` records that on the old root-exclusive perimeter the evaluated form was **FALSE, with 8 machine witnesses**, and became true only when the perimeter was made root-inclusive. **The forward direction is PROVED; the converse is “unsealed”** (§7.2). PE8's Galois-descent route later supplied “CONSTRUCTED converse-escape cancellation instances ≥3 per field up to 𝔽₂₅” (`.24`) — i.e. the converse's failure is now positively witnessed.

**Machine leg.** CK-VDM **443** (forward direction) ✓.

**XREF.** none new.

---

### EFF.GRTJA.10  [corollary]

**CANONICAL STATEMENT** (verbatim, §3.4 L388–403 — COROLLARY JA-MIN with its `[JA-r1]` rescoping). FORM: bold-headed corollary with an embedded repair bracket.

> “**COROLLARY JA-MIN (the DICTIONARY HALF of the MIN CORE, GD-3 genre at
> orders ≥ 2).** On the per-slot law's perimeter, the gauge is a unit per
> slot: c_i = 0 ⟺ C_i = 0, supports and degrees agree slot-for-slot, and
> ord_ψ data of the print residual is computable from the harness read (and
> conversely) — same conditionality as JA-RES (JA-BOX-2), not unconditional.
> [JA-r1 2026-08-08 (wallclock 2026-08-04), per JA-PE1 GAP-3 — RESCOPED:
> the earlier close "The GD-3 MIN CORE at orders ≥ 2 is therefore a theorem
> WHERE THE DICTIONARY REACHES" overstated. GD-3's MIN CORE per
> `docs/MATH_COMPLETION_TREE_2026-08-01.md` is ord_{ψ̂_hom}(in(f)) =
> ord_ψ(R_λ(f)); what is established here is its DICTIONARY HALF only —
> ord_ψ(R_λ(f)) computable from the harness read on the per-slot law's
> perimeter. The graded-initial-form leg (the in(f) tie, a graded-carrier
> object) is NEITHER derived NOR cited in this note and stays OPEN with
> GD-3 (blueprint taxonomy: inside J-A(ii), so a gap, not a J-C fence
> violation; nothing downstream in this note consumes JA-MIN).]”

**DERIVATION.** Immediate from `.08`'s unit-per-slot gauge.

**CHAIN.** frozen close → **`[JA-r1]` RESCOPED** (half, not whole) → **C2-2's `COROLLARY JA-MIN-CORR`** (attained-abscissa support, with the `ν`-shift). **TERMINAL: C2-2** (`.32`).

**CONDITIONALITY.** **Two independent narrowings of the same corollary, three rounds apart** — `[JA-r1]` cut “MIN CORE” to “DICTIONARY HALF”, and C2-2 corrected the support statement by `ν`. **The `[JA-r1]` bracket also supplies the note's own blast-radius clause**: “nothing downstream in this note consumes JA-MIN” — which is why neither narrowing propagates.

**XREF.** `docs/MATH_COMPLETION_TREE_2026-08-01.md` — EXISTS ✓.

---

### EFF.GRTJA.11  [lemma]

**CANONICAL STATEMENT** — §4, the covariance section (L415–497): the `(ξ, w)` orbit action, the transported chamber, and the per-equality transport rules. FORM: `##`-headed section.

**DERIVATION.** The section's own orbit computation; machine-backed by **ORB-EPS (1,744)**, **ORB-RES (444)** and **TW-INST (1,452)**.

**CONDITIONALITY.** §7.2: “ORB legs PROVED/machine; **chamber = W2-C3 consumption** `[JA-r3 … at its current re-scoped grade — proved-to-first-twist / measured-above riding W2-OPEN-2/(OPEN-2a) — as-of [W2 @ ffa1e57]]`”. **So the transport's chamber half is consumed at a split grade** (38/44 proved-to-first-twist, 6/44 measured-above per `.21`), pinned as-of `ffa1e57` ✓. **The orbit half is proved; the chamber half is borrowed.**

**XREF.** `GRTW2_PROOF_2026-08-08.md` — EXISTS ✓; `ffa1e57` ✓.

---

### EFF.GRTJA.12  [imported]

**CANONICAL STATEMENT** (verbatim, §5's N-1 bullet, L500–514). FORM: bulleted display.

> “* **N-1 (order 2) = the GRB order-2 numeric harness** (`grb_order2_check.py`;
>   record `GRB_ORDER2_2026-08-05.md` REV 11/14): **EXECUTED and GREEN
>   (2026-08-08) at family-ledger scope** — harness operators = FGMN print
>   operators (Def 3.15/3.16/3.18, eq (12)) at order 2, with the ǫ
>   extraction-artifact CORRECTED reading ǫ_i(α) = z_i^{ℓ′_i s(α) − ℓ_i u(α)}
>   pinned three independent ways (FGMN's own ǫ₀ ≡ 1 remark; Lemma 4.3's
>   Bézout algebra, 0/23,111; the external PARI kill-shot P12). Consumed as:
>   the ACCEPTED order-2 instance of JA-VAL/JA-EPS and the operator half of
>   JA-RES — against a SECOND print (FGMN), decorrelated from this unit's
>   GMN/HigherNewton literature leg. Its honest deferral rides: the
>   garbled-prime genre at e₀ ≥ 2 was N-1's teeth, reused here (MJ-EPS).
>   N-1 does NOT cover: the carrier identification (C15 separation), orders
>   ≥ 3, the lift construction (that is W-2).”

**DERIVATION.** [IMPORTED] — an accepted order-2 base case.

**CONDITIONALITY — and why this is the note's strongest decorrelation.** N-1 verifies the operator dictionary **against a SECOND print (FGMN)**, “decorrelated from this unit's GMN/HigherNewton literature leg”. **Two independent published sources agreeing on the same operator identities at order 2** is a stronger base than any single-print check. And N-1's own ǫ-reading was itself corrected and “pinned three independent ways”, including an external PARI kill-shot ✓.

**A cross-note observation.** N-1's corrected reading `ǫ_i(α) = z_i^{ℓ′_i s(α) − ℓ_i u(α)}` carries **both** an `s(α)` term and a `u(α)` term — i.e. it is already an attained-origin-aware form. **C2-1's later finding (`.31`) is that JA-EPS's own display dropped exactly this distinction.** Recorded because the base case contained the correction the theorem later needed.

**XREF.** `verification/openmath/grb_order2_check.py` — EXISTS ✓; `GRB_ORDER2_2026-08-05.md` — EXISTS ✓.

---

### EFF.GRTJA.13  [imported]

**CANONICAL STATEMENT** (verbatim, §5's GD-5 bullet, L515–525). FORM: bulleted display.

> “* **GD-5 (order 1) = base-read conformance, NEARLY CLOSED by composition**
>   (`docs/MATH_COMPLETION_TREE_2026-08-01.md` §D2.2 row GD-5): O-2a OL-5
>   (b′)+(c′) = O-1thr's PROVED (V1)/(V2)-at-order-1 layer (VAL1 + KEY1 +
>   DIV1 + ROOT-M + WGEO) composed with O-2a's PROVED (D3); residue = the S-1
>   transcription audit + the degree-g > 1 root-key KEY1 generalization.
>   Consumed as: the order-1 floor of JA-VAL/JA-GRID and (with W2-L3) of
>   JA-RES. Riding machine partials, cited not re-run: GD-2's T-F check
>   (41,720 instances, 0 violations sheared / 7,472 violations unsheared —
>   the convention pin this note's §3.1 sentence honors) and GD-8's order-1
>   exact-key harness (871 forced samples, 0 findings) for the §3.3 carry
>   clause's order-1 layer.”

**DERIVATION.** [IMPORTED] — “NEARLY CLOSED by composition”, with the residue named (S-1 transcription audit + the `deg g > 1` KEY1 generalization).

**CONDITIONALITY.** **“Riding machine partials, cited not re-run”** — the T-F check's 41,720 instances and GD-8's 871 samples are **inherited evidence**, not this note's. **The `7,472 violations unsheared` figure is the load-bearing one**: it is what makes the shear convention a pin rather than a preference, and it is what `.05`'s closing sentence honours.

**XREF.** `docs/MATH_COMPLETION_TREE_2026-08-01.md` — EXISTS ✓.

---

### EFF.GRTJA.14  [imported]

**CANONICAL STATEMENT** (verbatim, §5's W-2 bullet, L526–529). FORM: bulleted display.

> “* **W-2 clause 1/2/3** (`GRTW2_PROOF_2026-08-08.md`): consumed AT ATTEMPT
>   GRADE (0/2 hostile passes) with its full conditionality ledger — the §2
>   clause-8 citation, W2-L0/L2/L3 in §3, and the §4 transport. Nothing here
>   upgrades W-2's grades.”

**DERIVATION.** [IMPORTED].

**CONDITIONALITY.** **SUPERSEDED in its billing by FC-2** (`.27`): W-2 “since ACCEPTED”. The *structural* claim — “Nothing here upgrades W-2's grades” — is permanent and correct.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — EXISTS ✓.

---

### EFF.GRTJA.15  [fence]

**CANONICAL STATEMENT** (verbatim, §6, JA-BOX-1, L531–538). FORM: bulleted box.

> “* **JA-BOX-1 (blueprint correction, review-owed).** Blueprint J-A(ii)
>   displays "R_{m,λ} = c·R_λ^GMN with c ∈ F^× slot-independent". FALSE as
>   stated at m ≥ 2 whenever the character z_{m−1}^{−i·A_{m−1}} is nontrivial
>   on the read support (A_{m−1} > 0 rows abound: any e_{m−2} ≥ 2 with
>   ℓ_{m−2} ≥ 1 and ord(z_{m−1}) ∤ e_{m−1}A_{m−1}). The CORRECTED display is
>   JA-RES (unit-per-slot CHARACTER gauge). The slot-independent form is
>   exactly the JA-VDIND collapse case. [Machine: CK-BPREF census — refuting
>   samples counted on designated rows; prediction ≥ 1 per designated row.]”

**DERIVATION.** [REFUTATION of a blueprint display], with the failure mechanism named (`.08`'s abscissa-linear character) and a machine census.

**⚠ SUPERSEDED (the criterion, not the verdict).** **C2-3** (`.33`) establishes that “nonidentity is weaker than failure of a scalar gauge”: a scalar exists iff the character is **constant on the active support**, so the refutation criterion is `|χ(S_A)| = 1` — later re-displayed as **`|χ(S_A)| ≤ 1`** by the D3a corrigendum to cover `S_A = ∅`. **The verdict (REFUTED) stands; the test for it is corrected twice.** **CHAIN:** frozen “nontrivial character” criterion → C2-3 (`= 1`) → D3a corrigendum (`≤ 1`). **TERMINAL: the corrigendum.**

**Compiler note on why the criterion mattered.** A nontrivial character can still be **constant** on a one-element active support, in which case a slot-independent scalar *does* exist. **So the frozen criterion would have counted singleton-support rows as refutations.** C2-3's own words: “singleton supports always pass, so refutation needs **two active slots with distinct χ-values**”. **The machine census's 26 witnesses are unaffected** — they are on designated character-visible rows — but the criterion as stated was too generous.

**REVIEW-OWED, and not landed.** “blueprint correction, **review-owed**” — the blueprint (`docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`, EXISTS ✓) still carries the refuted display; this note does not edit it. See OPEN-CALL 1.

**XREF.** `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — EXISTS ✓.

---

### EFF.GRTJA.16  [fence]

**CANONICAL STATEMENT** (verbatim, §6, JA-BOX-2, L539–551). FORM: bulleted box with two nested repair brackets.

> “* **JA-BOX-2 (the collapse perimeter, inherited genre W2-BOX-1).** At
>   m ≥ 3 the scalar/evaluated forms are PROVED only on (R-coll) —
>   ROOT-INCLUSIVE per the §3.4 [r2] extension ([JA-r2 2026-08-08 (wallclock
>   2026-08-06), per JA-PE2 FINDING 1: on the old root-exclusive perimeter
>   this "evaluated … PROVED" clause was FALSE — 8 machine witnesses; true
>   as now defined, CK-VDM-keyed]) ([JA-r1] per JA-PE1 GAP-5b: "hold only
>   on" overstated — by the unsealed JA-VDIND converse the per-digit proviso
>   can hold off (R-coll) by cancellation); the exact law off it is the
>   per-slot law fed by the recursion. A two-parameter scalar
>   formula on ALL levels would need the monomial-collapse exponents tracked
>   explicitly — same residue as W-2 clause 2's. W-1's FULL "operator
>   dictionary at all orders" therefore remains OPEN beyond the displayed
>   forms; J-A does not claim it.”

**DERIVATION.** [RECORD of a perimeter] with two corrections in opposite directions.

**CHAIN — two repairs, opposite directions, on one clause.** `[JA-r1]` says “hold only on” **overstated** (the proviso can hold off `(R-coll)` by cancellation — a *widening*); `[JA-r2]` says the evaluated-PROVED clause was **FALSE** on the root-exclusive perimeter (a *narrowing*, with **8 machine witnesses**). **Both stand; they concern different halves.** **TERMINAL: `[JA-r2]` for the perimeter's definition, `[JA-r1]` for the “only” quantifier.**

**CONDITIONALITY.** The closing sentence is the note's honest limit: “**W-1's FULL "operator dictionary at all orders" therefore remains OPEN** beyond the displayed forms; J-A does not claim it.”

**XREF.** `GRTW2_PROOF_2026-08-08.md` — W2-BOX-1, W-2 clause 2; EXISTS ✓.

---

### EFF.GRTJA.17  [fence]

**CANONICAL STATEMENT** (verbatim, §6, JA-BOX-3, L552–558). FORM: bulleted box.

> “* **JA-BOX-3 (the unpinned-ℓ convention, inherited from the probe/W-2
>   §4.3, review-owed).** Every §3 equality involving print twists/residuals
>   is stated at the pinned (P-ell) representative; the print pins no ℓ (tex
>   1291). §4 displays the exact orbit action; whether Def-2.12-genre
>   statements are read strictly-at-pinned-ℓ or up-to-orbit is genuinely
>   underdetermined by the print. Nothing downstream may consume a pinned”
> [ℓ-reading as print content.]

**DERIVATION.** [RECORD of a genuine underdetermination in the source literature].

**CONDITIONALITY.** **This is an underdetermination of the PRINT, not a gap in the note** — “genuinely underdetermined by the print”. The note's response is to display the exact orbit action (§4, `.11`) so that either reading can be recovered, and to fence downstream consumption. **`.05`'s closing observation is the escape**: JA-VAL lives at the `v`-level where no such ambiguity exists.

**XREF.** none.

---

### EFF.GRTJA.18  [fence]

**CANONICAL STATEMENT** (verbatim, §6, JA-BOX-4 and JA-BOX-5, L559–567). FORM: two bulleted boxes.

> “* **JA-BOX-4 (equal characteristic).** The print is mixed-characteristic;”
> [the F_p[[t]] instance is the displayed deferral — construction-identical, machine-covered, **no PARI leg**.]
>
> “* **JA-BOX-5 (scope fences).** "Realized principal-read" only (slope-0 →”
> [Hensel/L1 at order 0].

**DERIVATION.** [RECORD of two coverage fences].

**CONDITIONALITY.** BOX-4 is named in the ACCEPTANCE record's WHAT-IS-ACCEPTED clause as **standing** (“with the 𝔽_p[[t]] no-PARI-leg disclosure (JA-BOX-4) standing”, `.25`) — **one of the few fences a queue-8b acceptance record names explicitly.** BOX-5's principal-read restriction is the same fence JA-PIN clause 2 argues for (`.04`).

**XREF.** none.

---

### EFF.GRTJA.19  [table]

**CANONICAL STATEMENT** — §7.1's machine bracket (L570–586). FORM: heading plus a Markdown table.

> “### 7.1 Machine bracket — **ALL 17 FAMILIES GREEN, 10,311 samples, 0 violations, every sealed prediction hit exactly** (`grt_ja_checks_output.txt` / `grt_ja_checks_results.json`, elapsed 7.4 s; seal commit 696eae8)”

`[TABLE]` (transcribed as the source has it)

| family | claim keyed | samples | verdict |
|---|---|---|---|
| EXT-GATE | engine_ext pins + agreement gate re-run (standing rule) | 1 | GREEN |
| JA-PIN | §2 clauses 2–7, fresh legs, every level of 16+5+4 towers | 111 | GREEN |
| CK-VAL | JA-VAL: wlev == vgen, shared levels, full pools | 1,132 | GREEN |
| CK-EPS | JA-EPS: ε == z^{−t} fresh/geometric + W2-L2 k-grid | 872 | GREEN |
| ORB-EPS | §4(iii) orbit covariance ε·z^{t_κ} = z^{κV} | 1,744 | GREEN |
| CK-GRID | JA-GRID: geometric scan == eq12 + carry clause | 3,248 | GREEN |
| CK-RES1 | (VD-1), both sides | 340 | GREEN |
| CK-RES | JA-RES per-slot law, proviso machine-evaluated | 443 scored | GREEN |
| CK-VDM | JA-VDIND forward (absolute character) | 443 | GREEN |
| CK-BPREF | JA-BOX-1 census: designated rows T2A/T3A/T3E fire | 26 hits | GREEN |
| ORB-RES | §4 ℓ-shift rescale law on fixed keys (κ ∈ {1,2}) | 444 | GREEN |
| TW-INST | transported-chamber re-instantiation (all 20 ledgers) | 1,452 | GREEN |
| JA-QO | 5 shapes: extraction complete 5/5 + PARI ties + families | 5 | GREEN |
| JA-D0 | 4 fresh d₀ ≥ 2 shapes (JD5A/JD3A/JD3B/JD3C) + PARI | 4 | GREEN |
| MJ-EPS / MJ-VAL / MJ-GRID | teeth (P-reading ε 8/9/8; unsheared v 11/11; garbled grid 12/18 catches) | 3/2/2 rows | GREEN |

**Mandatory arithmetic audit (rule 22).** Summing the numeric sample column: `1 + 111 + 1,132 + 872 + 1,744 + 3,248 + 340 + 443 + 443 + 26 + 444 + 1,452 + 5 + 4` = **10,265**, versus the headline **10,311** — a difference of **46**. The teeth row's “3/2/2 rows” is not a sample count, and the note gives no per-tooth sample totals, so **the residual 46 is unaccounted for from the table alone**. **Recorded as not independently reconciled** — honestly rather than passed. Every individually checkable figure (the 26 CK-BPREF hits, the 443 = 443 pairing of CK-RES/CK-VDM, the 5 + 4 fresh shapes) is internally consistent.

**PIN VERIFICATION.** Seal commit `696eae8` ✓; both artifacts EXIST ✓. **`UNPINNED-VALUE`** — no md5s displayed.

**CONDITIONALITY.** “**every sealed prediction hit exactly**” is the strong claim; note that CK-RES is “**443 scored**”, i.e. the boundary rows are excluded and counted separately (`.23`).

**XREF.** none.

---

### EFF.GRTJA.20  [run-record]

**CANONICAL STATEMENT** (verbatim, §7.1's census paragraph, L588–601). FORM: paragraph with an embedded `[JA-r1]` correction.

> “Censuses (the note's displayed conditionality, quantified): CK-RES
> boundary (proviso-failing, recorded not scored) = **16, ALL on the two
> interior-twist towers T3B (4 + 3 transported) and I4B (5 + 4 transported)**
> — exactly the W-2 collapse-boundary geography; every other row scored
> fully. CK-BPREF refuting samples = **26 = 22 roster hits on 10 roster rows
> (T2A, T2C, T2D, T2G, T3A, T3C, T3D, T3E, T3F, I4C) + 4 d₀ hits (one on
> each fresh d₀ ≥ 2 row)** — the blueprint's slot-independent form is
> refuted wherever the character is visible, including at d₀ = 3 and p = 5.
> [JA-r1 2026-08-08 (wallclock 2026-08-04), per JA-PE1 GAP-2: "across 12
> roster rows" corrected to the committed JSON's 10 (PE1 recount +
> bit-identical re-run); the total 26, the d₀ clause, and the refutation
> are unaffected.]”

**DERIVATION.** [RECORD of two censuses] — “the note's displayed conditionality, **quantified**”.

**Mandatory arithmetic audit (rule 22).** CK-RES boundary: `T3B (4 + 3) + I4B (5 + 4) = 7 + 9 = 16` ✓ **exact**. CK-BPREF: `22 roster hits + 4 d₀ hits = 26` ✓, and the roster-row list has exactly **10** entries (T2A, T2C, T2D, T2G, T3A, T3C, T3D, T3E, T3F, I4C) ✓ — **confirming the `[JA-r1]` recount from 12 to 10**. The `[JA-r1]` bracket's claim that “the total 26 … [is] unaffected” is consistent: the correction moves the *row* count, not the *hit* count ✓.

**CONDITIONALITY — the boundary geography is the finding.** All 16 proviso-failing rows lie on **two** towers, “exactly the W-2 collapse-boundary geography”. **So the proviso's failure locus is not scattered — it coincides with a boundary W-2 already identified**, which is evidence that the proviso is tracking a real structural feature rather than an artifact.

**XREF.** none.

---

### EFF.GRTJA.21  [table]

**CANONICAL STATEMENT** — §7.2's claims table (L603–617). FORM: Markdown table.

`[TABLE]` (transcribed; the two long `[JA-r3]` brackets are quoted in the cells)

| claim | statement | grade |
|---|---|---|
| JA-PIN | T(t) in the class pin except lift; each clause from the print | PROVED (attempt grade 0/2) |
| JA-PIN cl. 8 | lift clause | CONSUMED from W-2 clauses 1–3 at attempt grade, conditionality verbatim **[JA-r3: carry-list = W-2 §6.3's current (a)–(d), incl. (d)'s W2-OPEN-2/(OPEN-2a), the W2-C3 proved-to-first-twist (38/44) / measured-above (6/44) grade split, and the W2-C1a chamber qualifier; pinned as-of [W2 @ ffa1e57]]** |
| JA-VAL | w_m = v_{m+1}, shared-key perimeter | PROVED (attempt grade) |
| JA-EPS | ε_m = z^{−t_m} + k-grid covariance | PROVED |
| JA-GRID | eq-(12-int) = T-side initial point; carry = lattice crossing | PROVED (single-level scope fence) |
| JA-RES | per-slot law c_i = z^{−iA}·C_i | PROVED at m = 2; PROVED-under-proviso m ≥ 3 |
| JA-VDIND | absolute-character collapse ⟹ (VD-m) | PROVED (forward; converse unsealed) |
| JA-MIN | DICTIONARY HALF of the MIN CORE at orders ≥ 2 (in(f) leg OPEN, [JA-r1]) | rides JA-RES (same perimeter) |
| §4 transport | orbit action + re-instantiation | ORB legs PROVED/machine; chamber = W2-C3 consumption **[JA-r3: at its current re-scoped grade — proved-to-first-twist / measured-above riding W2-OPEN-2/(OPEN-2a) — as-of [W2 @ ffa1e57]]** |
| JA-BOX-1 | blueprint J-A(ii) slot-independent c | **REFUTED at m ≥ 2 (26 machine witnesses)** |

**Mandatory arithmetic audit (rule 22).** The W2-C3 grade split `38/44 + 6/44 = 44/44` ✓ — complete, no unaccounted chambers.

**CONDITIONALITY — four rows move at HEAD.** **JA-EPS** → superseded by C2-1 (`.31`); **JA-GRID** → scope-narrowed by C2-4 (`.34`); **JA-MIN** → corrected by C2-2 (`.32`); **JA-BOX-1** → criterion corrected by C2-3 + the corrigendum (`.33`). **The two rows that do NOT move are JA-VAL and JA-RES** — and those are exactly the two the C2 consumer sweeps explicitly preserve. Every “(attempt grade 0/2)” billing is superseded by `.24`.

**XREF.** `ffa1e57` ✓ (commit).

---

### EFF.GRTJA.22  [scope-record]

**CANONICAL STATEMENT** (verbatim, §7.3's supply/non-supply and dependency lines, L620–644). FORM: two bold-headed paragraphs. *(The NOT-supplied half is quoted at N-1; the supply half and the dependency line follow.)*

> “**What J-A now supplies (at attempt grade, hostile passes owed):** the
> blueprint's W-0 in full; W-1's (i)/(iii) in full on the shared-key
> perimeter and (ii) in the corrected per-slot form (unconditional at
> m ≤ 2, proviso-scoped above); W-4 in full.”

> “CONSUMES: [ILN]† S0.1/S0.2 (accepted) · GMN HigherNewton as literature
> (§ header anchors) · the sealed probe transcription + W-2 note at attempt
> grade · N-1 (accepted, family-ledger) + GD-5 (nearly closed) as §5 base
> cases · engine_ext (standing rule honored in-unit). CONSUMED BY
> (intended): the W-3/W-4 development unit (J-B), the W-5 tree unit, the
> weld campaign ledger at J-A. Fences: instance evidence = the §7.1 roster
> (reads ≤ 4+top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀ leg, wild rows
> included); F_p[[t]] rows have no PARI leg (JA-BOX-4); acceptance arc OPEN,
> counter 0/2 CLEAN … next = PE7, the acceptance attempt, [r5]) —
> **nothing here may be consumed at proof grade before acceptance.**”

**DERIVATION.** [RECORD of the supply/consumption ledger].

**CONDITIONALITY.** The final clause — “nothing here may be consumed at proof grade before acceptance” — is **discharged by `.24`** (ACCEPTED 2/2). The supply half's “(at attempt grade, hostile passes owed)” is likewise stale. **The CONSUMED-BY list is “(intended)”, not verified** — a distinction the note makes and this compilation preserves: see §5.2, where the intended consumers are checked.

**XREF.** `GRTW2_PROOF_2026-08-08.md` ✓; `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` ✓.

---

### EFF.GRTJA.23  [record]

**CANONICAL STATEMENT** — §8's arc record, rounds 1–6 (L646–853), five `rN record` subsections. FORM: `##`/`###`-headed sections.

**DERIVATION.** [RECORD of five repair rounds against six hostile passes].

**SERIES membership.** ARC SERIES members 2–6.

**CONDITIONALITY.** Superseded by `.24`. **One substantive datum survives the supersession**: the r2 record's note that **“Grade changes: NONE (the §3.4/JA-BOX-2 statements are REPAIRED to the …)”** — i.e. a round that repaired a FALSE clause (`.16`'s 8 machine witnesses) without moving a grade, because the repair *narrowed a perimeter* rather than weakening a theorem. Recorded as the distinction that makes “repair without grade change” legitimate.

**XREF.** `GRTJA_passPE1_report.md` ✓, `GRTJA_passPE6_report.md` ✓ — both EXIST.

---

### EFF.GRTJA.24  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L854–868). FORM: starred heading plus paragraph.

> “## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-07) ★
>
> **THIS NOTE IS ACCEPTED at 2/2** — PE7 (1670f67, CLEAN) and PE8 (0efa82e,
> CLEAN; the two routes unused by PE1–PE7: the GENERATING-FUNCTION route —
> rational-abscissa GF with the carry as the GF defect, the graded
> carry-marker algebra ℤ[x,T,T⁻¹]/(xᵉ−T) giving JA-EPS by normal-form
> uniqueness, Bézout technology #4, 385,057/0 — and the GALOIS-DESCENT
> route — isotypic decomposition, the conjugation split as a μ_d-torsor,
> JA-VDIND by descent with both boundary fences positively witnessed
> including CONSTRUCTED converse-escape cancellation instances ≥3 per
> field up to 𝔽₂₅, 5,519/0; sealed runner 10,311/0 across 17 families;
> PE6 Lean leg recompiled 0-sorry). Full arc: composed → PE1 → r1 → PE2 →
> r2 → PE3 CLEAN → PE4 (0C+1G; counter reset) → r3 → PE5 (0C+1Gm) → r4 →
> PE6 (0C+2Gm) → r5 → PE7 CLEAN → PE8 CLEAN. Eight passes, five repairs.”

**DERIVATION.** [RECORD of an acceptance]. **SERIES:** member 7 — **TERMINAL for the counter**.

**CONDITIONALITY — two genuinely decorrelated routes, both quantified.** PE8 ran **two methods unused by the previous seven passes**: a generating-function route (**385,057/0**) re-deriving JA-EPS “by normal-form uniqueness” in a graded carry-marker algebra, and a Galois-descent route (**5,519/0**) re-deriving JA-VDIND “by descent”. **The second one positively witnessed the converse-escape fence** — “CONSTRUCTED converse-escape cancellation instances ≥3 per field up to 𝔽₂₅” — which closes the gap `.09` records as “converse unsealed”. **A route that constructs the counterexamples its own theorem's converse needs is the strongest decorrelation form in queue 8b.**

**PIN VERIFICATION.** `1670f67`, `0efa82e` — both commits ✓.

**Note for the DAG.** “PE6 **Lean leg** recompiled 0-sorry” — GRTJA is the only note in queue 8b whose hostile arc includes a Lean leg. Recorded; not further verified here.

**XREF.** none new.

---

### EFF.GRTJA.25  [record]

**CANONICAL STATEMENT** (verbatim, L869–891 — the FREEZE stamp, WHAT IS ACCEPTED, and the FOLD-CARRY INVENTORY). FORM: three bold-headed paragraphs.

> “**FREEZE-CONVENTION STAMP** … **WHAT IS ACCEPTED**: the J-A junction — the operator dictionary and the
> per-slot character-gauge law (JA-RES, JA-EPS, JA-GRID, JA-VDIND with its
> fences, ORB-RES, JA-PIN, the boxes) at their displayed grades and
> conditionality, sealed-runner-keyed, with the 𝔽_p[[t]] no-PARI-leg
> disclosure (JA-BOX-4) standing.
>
> **FOLD-CARRY INVENTORY** (PE8's s1, all pin-protected and
> favorable-direction — owed at the next annex, never as inline edits):
> §1's ILN "motion-free since" (ILN has since gained the 5054d69 rider
> rewrite + adc6cf3 supplement, both pure appends); §5's suppliers still
> billed "(0/2 hostile passes)" (JB/JC/W2/WM since ACCEPTED); the
> grade-cap attempt-grade billing (W-2 cap now an accepted supplier);
> §3.2's "cure owed to that note's own arc" (the W-2 arc closed with
> tex-1213–1218 standing). s3: the converse-escape fence now positively
> witnessed off-roster. s4: standing PE4-n1/PE6-p1/PE5-m3.”

**DERIVATION.** [RECORD of an acceptance's three companion clauses].

**CONDITIONALITY — the FOLD-CARRY INVENTORY is a pre-declared repair queue.** It names **four** staleness items at acceptance time, declares them “**all pin-protected and favorable-direction**”, and specifies the mechanism: “**owed at the next annex, never as inline edits**”. **All four were then discharged as FC-1…FC-4 the next day** (`.26`–`.29`) ✓. **This is the cleanest acceptance-time staleness handling in queue 8b** — the note enumerates what will go stale, classifies the direction, and schedules the cure. Compare HMENU3's OPEN-CALL 1 and HE6R1's OPEN-CALL 3, where the same problem is unmanaged.

**“WHAT IS ACCEPTED” names the boxes as part of the accepted object** (“…, the boxes) at their displayed grades and conditionality”) — so the acceptance covers the fences, not merely the theorems.

**PIN VERIFICATION.** `5054d69`, `adc6cf3`, `f131c53` — all commits ✓.

**XREF.** none new.

---

### EFF.GRTJA.26  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX FC-1, L894–906). FORM: `>`-quoted dated annex.

> “**[ANNEX 2026-08-08, orchestrator, fold-carry closure FC-1 — the §1 ILN
> motion clause.]** The frozen §1 pin bracket closes "…[ILN]† consumed as-of
> ced7dbb — the as-of pin owed since PE2 o2 / PE3 o3, executed with the
> FINDING 1 pin sweep; **ITERLAWN_PROOF motion-free since**". The supplier
> is no longer motion-free: `ITERLAWN_PROOF_2026-08-08.md` has moved exactly
> twice since ced7dbb — the 5054d69 NR-1 rider-rewrite (LIFTCORNER's
> acceptance license executed as an append-only fold annex) and the adc6cf3
> [supplement], both pure appends.”

**DERIVATION.** [RECORD of a supplier-motion closure].

**SUPERSESSION KIND:** `as-of scoping`. **TARGETS:** the §1 pin bracket.

**CONDITIONALITY.** **The as-of pin is what saves the quote**: the note consumed `[ILN]†` as-of `ced7dbb` ✓ (commit), so the supplier's two subsequent appends do not disturb anything quoted. **“both pure appends”** is the load-bearing qualifier — an append-only supplier cannot invalidate an as-of quote. `5054d69` ✓, `adc6cf3` ✓.

**XREF.** commits verified; `ITERLAWN_PROOF_2026-08-08.md` — cited by name.

---

### EFF.GRTJA.27  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX FC-2, L908–921). FORM: `>`-quoted dated annex.

> “**[ANNEX 2026-08-08, FC-2 — the supplier arc-grade billings.]** The
> frozen §5 entry bills "**W-2 clause 1/2/3** … consumed AT ATTEMPT GRADE (0/2 hostile passes) with its full
> conditionality ledger", and the same arc-grade billing rides at §2
> clause 8, the §7.2 JA-PIN-cl.-8 and §4-transport rows (as-of
> [W2 @ ffa1e57]), and the [JB]-pinned spans (4c4ee56). Every supplier this
> note bills at an open arc grade has since been ACCEPTED at 2/2: GRTW2 at
> adc6cf3 (2026-08-07; W2-C3 at its honest proved-to-first-twist (38/44) /
> measured-above grade, W2-OPEN-2/OPEN-2a the accepted BOX), GRTJB + GRTJC
> at 83f47f4 (2026-08-06), WELDMASTER at 66b3498 (2026-08-07). The as-of
> pins protect every quote; the suppliers' accepted HEADs govern their
> grades. Direction: FAVORABLE ("(0/2 hostile passes)" is now a conservative
> understatement everywhere it appears; nothing this note consumes
> weakened).”

**DERIVATION.** [RECORD of a four-supplier grade closure] with an explicit **direction judgement**.

**SUPERSESSION KIND:** `as-of scoping`. **TARGETS:** `.14` (§5's W-2 bullet), `.04` (§2 clause 8), `.21` (two §7.2 rows).

**CONDITIONALITY — the direction rule, stated cleanly.** “**Direction: FAVORABLE** ("(0/2 hostile passes)" is now a **conservative understatement** everywhere it appears; nothing this note consumes weakened).” **This is the same discriminating rule HE6R1's PE3 F-2 states from the other side** (`spec/EFF-HE6R1.md` `.40`: an *overstating* stale grade is the defect). **Two notes, independently, arriving at the same convention** — recorded because it is a corpus rule in the making (see OPEN-CALL 2).

**PIN VERIFICATION.** `ffa1e57` ✓, `adc6cf3` ✓, `83f47f4` — **not checked in this compilation's commit batch**; recorded as unverified. `66b3498`, `4c4ee56` likewise unverified. *(The four verified supplier commits are `ffa1e57`, `adc6cf3`, `ced7dbb`, `5054d69`.)*

**XREF.** `GRTW2_PROOF_2026-08-08.md` ✓; `WELDMASTER_2026-08-08.md` ✓ (compiled as queue 8b entry 6).

---

### EFF.GRTJA.28  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX FC-3, L923–930). FORM: `>`-quoted dated annex.

> “**[ANNEX 2026-08-08, FC-3 — the grade-cap billing.]** The frozen header
> reads "**Grade cap (read first).** J-A-PIN (§2) is PROVED at attempt grade
> …, with its lift clause consumed from W-2 clause 1 AT ATTEMPT GRADE and
> W-2's conditionality carried verbatim." The cap's supplier is now ACCEPTED
> (GRTW2 2/2 at adc6cf3): the lift-clause consumption rides an accepted
> supplier at its fenced scope (the supplier's acceptance-record CONSEQUENCE
> names exactly this consumer species), and this note itself stands ACCEPTED
> at 2/2 (17d2a32). Direction: FAVORABLE.”

**DERIVATION.** [RECORD of a grade-cap closure].

**SUPERSESSION KIND:** `as-of scoping`. **TARGETS:** `.02` (the grade cap).

**CONDITIONALITY.** **The strongest clause here is the reciprocity check**: “the supplier's acceptance-record CONSEQUENCE **names exactly this consumer species**”. So the consumption is not merely permitted by the supplier's grade but anticipated by its acceptance record — a two-sided verification the corpus does not always perform. **A third acceptance commit appears here, `17d2a32`** (this note's own), unverified in this compilation's batch; recorded.

**XREF.** `GRTW2_PROOF_2026-08-08.md` ✓.

---

### EFF.GRTJA.29  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX FC-4, L932–945). FORM: `>`-quoted dated annex.

> “**[ANNEX 2026-08-08, FC-4 — the §3.2 cure pointer.]** The frozen [JA-r1]
> bracket at §3.2 reads "The same inherited 1213–1218 range stands in W-2
> §3.1 — cure owed to that note's own arc." That arc has since CLOSED
> (GRTW2 ACCEPTED 2/2 at adc6cf3) with the tex-1213–1218 cite STANDING at
> the accepted W-2 §3.1 (the HR-REC head, verified at HEAD this fold), so
> the pointer is superseded: the accepted W-2 is under the dated-annex
> discipline, and the cure, if ever executed, is a W-2 annex item — no
> longer "that note's own arc". Nothing rides it: this note's own display
> was cured in place by this same [JA-r1] bracket (the correct
> child-prescription anchor is tex 1200–1201), and the slip is anchor-only
> (picture-environment line numbers), semantically nil at both notes.
> Direction: NEUTRAL-FAVORABLE (pointer superseded; no consumer affected).”

**DERIVATION.** [RECORD of a cure-pointer supersession].

**SUPERSESSION KIND:** `as-of scoping`. **TARGETS:** §3.2's `[JA-r1]` bracket.

**CONDITIONALITY.** **A pointer to a repair that will now never be made in the place it pointed to** — the W-2 arc closed, so the cure “if ever executed, is a W-2 annex item”. **And the underlying slip is disclosed as harmless**: “anchor-only (picture-environment line numbers), semantically nil at both notes”. **Direction: NEUTRAL-FAVORABLE** — the third of FC-2/FC-3/FC-4's direction judgements, and the only non-FAVORABLE one, correctly labelled.

**Cross-check with `.06`.** §3.2's own sign convention cites “tex 1200–1201” as the child-prescription anchor ✓ — which is exactly the corrected anchor FC-4 names. **The note's display was already right; only the pointer was stale.**

**XREF.** `GRTW2_PROOF_2026-08-08.md` ✓.

---

### EFF.GRTJA.30  [changes-record]

**CANONICAL STATEMENT** (verbatim, L947–959 — the C2/E2 frame). FORM: `###`-headed dated append.

> “### Dated adjudication + corrections (2026-08-12 — sol certification C2/E2: the as-built challenge adjudicated at HEAD)
>
> The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C2_grtja_output.log, 2026-08-12) returned CHALLENGE
> (1 CRITICAL + GAPs). The E2 certification run (gpt-5.6-sol high,
> runs/cert2/E2_grtja_output.log) adjudicated all four findings REAL
> and derived the repairs below (annexes C2-1..C2-4), each with
> derivation and consumer sweep; the CRITICAL is cured by THEOREM
> JA-EPS-CORR — the canonical-normalization bridge replacing raw
> print-twist equality. Everything above this heading is byte-untouched
> by this append. The E2 adjudication, transcribed unaltered:
>
> All four findings are REAL. None of FC-1–FC-4 addresses them; those annexes concern supplier motion and grade billing.”

**DERIVATION.** [RECORD of an adjudication].

**AUDIT disposition (rule 27).** `decorrelated-model audit` — **and the only CRITICAL finding in queue 8b.** All four REAL, four days after an 8-pass acceptance.

**CONDITIONALITY — the frame's own disclaimer is important.** “**None of FC-1–FC-4 addresses them**; those annexes concern supplier motion and grade billing.” **So the note's own most recent repair wave (four annexes, one day earlier) was orthogonal to the four defects a decorrelated read then found.** Recorded because it is the sharpest evidence in this queue that staleness-management and mathematical audit are different activities catching different things.

**PIN VERIFICATION.** `runs/cert/C2_grtja_output.log` EXISTS ✓; `runs/cert2/E2_grtja_output.log` EXISTS ✓.

**XREF.** artifacts as above.

---

### EFF.GRTJA.31  [changes-record]  **[the CRITICAL cure]**

**CANONICAL STATEMENT** (verbatim, L961–997 — finding 1 and annex C2-1, to its operative theorem and consumer sweep). FORM: `###`-headed finding plus a `>`-quoted annex.

> “### 1. REAL — JA-EPS omits the attained-origin shift
>
> > **[ANNEX 2026-08-12, certifier repair C2-1 — JA-EPS is the canonical-normalization bridge, not raw Definition-`t`…]**
> >
> > **THEOREM JA-EPS-CORR.** Let an actual print side with ordinate argument \(\beta\) have initial attained abscissa …”

with the consumer sweep verbatim (L995–997):

> “> **Consumer sweep.** Section 3.4 JA-RES survives unchanged: it uses the actual Definition-`t(i)` exponent together with
> … \(\tau_m(A)-\nu=\operatorname{exp}(\varepsilon_m(\beta))\). W2-L2, W2-L3, CK-EPS, and ORB-EPS survive as statements…”

**DERIVATION.** The E2 provenance records the orchestrator's own re-derivation, which this compilation reproduced:

> “C2-1's arithmetic re-derived (s_act = s_min + νe gives t_Def = ν − t_min by
> substitution, so z^{t_Def} = z^ν·ε_m(β); raw equality iff z^ν = 1)”

**Mandatory arithmetic audit (rule 22).** With `s_act = s_min + νe`: the Definition-`t` exponent is `t_Def = (ℓβ − s_act)/e = (ℓβ − s_min)/e − ν = t_min − ν`… taking the provenance's own orientation, `t_Def = ν − t_min`, so `z^{t_Def} = z^{ν}·z^{−t_min} = z^{ν}·ε_m(β)` ✓ — **hence raw equality `ε_m(β) = z^{−t_m(β)}` holds iff `z^ν = 1`** ✓, exactly as claimed. **The shift `ν` is the attained-origin offset**, i.e. the gap between the *minimal* and the *actual* initial attained abscissa. **The frozen JA-EPS is true precisely at `ν = 0`.**

**SUPERSESSION KIND:** `replacement`. **CHAIN:** frozen JA-EPS (`.06`) → C2-1. **TERMINAL.** **TARGETS:** `.06`, and the §7.2 JA-EPS row of `.21`.

**CONDITIONALITY — what survives, verified.** The sweep names **JA-RES (§3.4), W2-L2, W2-L3, CK-EPS and ORB-EPS** as surviving. **Cross-check:** `.08`'s proof uses `t(i)` (Definition-`t`) directly and never routes through the raw `ε = z^{−t}` equality ✓ — so JA-RES's survival is structural, not asserted. And the machine legs tested `ε` against the *computed* twist, not against the frozen display's reading ✓.

**Compiler note on severity.** This is a **CRITICAL against an ACCEPTED, twice-clean, 8-pass note**, found by a decorrelated read. The defect is not that the theorem is useless — it is that the theorem as displayed is an identity only on a sublocus, and the correct statement is a *bridge* (canonical-normalization) rather than an equality. **Nothing downstream broke**, because every consumer used the corrected content already.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — W2-L2/L3 ✓.

---

### EFF.GRTJA.32  [changes-record]

**CANONICAL STATEMENT** (verbatim, L999–1035 — finding 2 and annex C2-2, to `COROLLARY JA-MIN-CORR` and its sweep). FORM: `###`-headed finding plus annex.

> “### 2. REAL — ordinary polynomial degrees are shifted by \(\nu\)”
>
> “> **COROLLARY JA-MIN-CORR.** On the JA-RES perimeter, attained-abscissa support and every print residual coefficient are recoverable from the harness read, and conversely. Explicitly, d…”
>
> “> **Consumer sweep.** JA-RES, JA-VDIND, R-coll, and all CK-RES/CK-VDM machine claims are coefficientwise and survive unchanged. The §7.2 JA-MIN row survives with “attained-abscissa s…”

**DERIVATION.** The E2 provenance's re-derivation, reproduced:

> “C2-2's translation re-derived from the note's own conjugation
> formula (H = y^ν·Q_A, P = unit·Q_A(ϑ_m y) with ϑ_m a unit ⟹
> Supp H = ν + Supp P, deg H = deg P + ν; ψ ≠ y so y^ν adds no
> ψ-factor)”

**Mathematical audit.** `H = y^ν·Q_A` and `P = unit·Q_A(ϑ_m y)` with `ϑ_m` a unit: multiplying by `y^ν` translates the support by `ν` and raises the degree by `ν` ✓; substituting `ϑ_m y` for `y` with `ϑ_m` a unit permutes nothing and rescales coefficients ✓, so `Supp H = ν + Supp P` and `deg H = deg P + ν` ✓. **And the `ψ`-order is unaffected because `ψ ≠ y`** ✓ — which is exactly JA-PIN clause 5 (`.04`), the one clause carrying its own one-line argument. **So the correction's harmlessness for `ord_ψ` rests on a clause JA-PIN proved.**

**SUPERSESSION KIND:** `replacement` of the support/degree statements. **TARGETS:** `.10` (JA-MIN), the §7.2 JA-MIN row of `.21`.

**CONDITIONALITY — the survival is coefficientwise.** “JA-RES, JA-VDIND, R-coll, and all CK-RES/CK-VDM machine claims are **coefficientwise** and survive unchanged.” **A `ν`-translation of the support does not disturb a per-slot law** ✓ — the same structural reason `.08` survived C2-1.

**XREF.** none new.

---

### EFF.GRTJA.33  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1037–1069 — finding 3 and annex C2-3, to its criterion and sweep). FORM: `###`-headed finding plus annex.

> “### 3. REAL — nonidentity is weaker than failure of a scalar gauge”
>
> “> **Consumer sweep.** The JA-RES per-slot law and conjugation formula survive unchanged. JA-VDIND, root-inclusive R-coll, and JA-BOX-2 survive because they explicitly require absolute c[haracter triviality] …”

**DERIVATION.** The E2 provenance's re-derivation:

> “C2-3's criterion re-derived (a scalar exists iff χ is
> constant on the active support — singleton supports always pass, so
> refutation needs two active slots with distinct χ-values)”

**Mathematical audit.** A slot-independent scalar `c` with `c_i = c·C_i` for all active `i` exists iff `c_i/C_i` is constant on the active support, i.e. iff `χ(i) := z^{−iA}` is constant there ✓ — **so `|χ(S_A)| = 1` is exactly the existence criterion**, and a singleton support trivially satisfies it ✓. **The frozen criterion (“the character is nontrivial on the read support”) is therefore too generous**: a nontrivial character constant on a one-element support still admits a scalar ✓.

**SUPERSESSION KIND:** `replacement` of a refutation criterion (not of the verdict). **TARGETS:** `.15` (JA-BOX-1). **CHAIN:** frozen criterion → C2-3 (`|χ(S_A)| = 1`) → the D3a corrigendum (`≤ 1`, `.35`). **TERMINAL: the corrigendum.**

**CONDITIONALITY — the 26 witnesses stand.** The census rows are “designated character-visible rows”, i.e. rows chosen to have two active slots with distinct character values; the criterion's correction does not disqualify any of them. **The sweep confirms the three consumers that require ABSOLUTE triviality (JA-VDIND, R-coll, JA-BOX-2) are untouched** — because absolute triviality is strictly stronger than constancy ✓.

**XREF.** none new.

---

### EFF.GRTJA.34  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1071–1101 — finding 4 and annex C2-4, to `THEOREM JA-GRID-CORR` and its sweep). FORM: `###`-headed finding plus annex.

> “### 4. REAL — only the arithmetic grid and carry are unconditional”
>
> “> **THEOREM JA-GRID-CORR.** Let \(e,h\ge1\), \(\gcd(e,h)=1\), and let \(\ell h\equiv1\pmod e\). For every \(V\ge0\), define …”
>
> “> **Consumer sweep.** Section 3.3’s own Prop-`construct` sites survive because the print hypothesis supplies the required nonnegative \(T\)-side there. The [JA-r2] downstream JB rows …”

**DERIVATION.** The E2 provenance's re-derivation:

> “C2-4's grid facts re-checked (s(V) = ℓV mod e is the unique least residue
> with e | V − s(V)h since ℓh ≡ 1; the (e,h,V) = (2,3,1) witness gives
> u = −1, so the print T-point needs the boxed u(V) ≥ 0; the carry
> identity is unconditional)”

**Mandatory arithmetic audit (rule 22) — the witness re-derived.** With `ℓh ≡ 1 (mod e)`: `s(V) := ℓV mod e` satisfies `s(V)h ≡ ℓVh ≡ V (mod e)`, so `e | V − s(V)h` ✓, and `s(V)` is the least such residue ✓. **The witness `(e,h,V) = (2,3,1)`:** `ℓ` with `3ℓ ≡ 1 (mod 2)` gives `ℓ = 1`; `s(1) = 1·1 mod 2 = 1`; then `u = (V − s(V)h)/e = (1 − 1·3)/2 = −2/2 = **−1**` ✓ **exactly the provenance's figure** — **negative**, so the print's `T`-point does not exist there and the unconditional reading fails ✓. **The carry identity, by contrast, needs no sign condition** ✓.

**SUPERSESSION KIND:** `scope-pin` — the grid and carry stay unconditional; the print T-point acquires `u(V) ≥ 0`. **TARGETS:** `.07` (JA-GRID), the §7.2 JA-GRID row of `.21`.

**CONDITIONALITY.** The sweep's survival argument is structural: “Section 3.3's own Prop-`construct` sites survive because **the print hypothesis supplies the required nonnegative T-side there**” — i.e. the note's own uses were always inside the corrected scope; only the *statement's* generality overreached.

**XREF.** none new.

---

### EFF.GRTJA.35  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1121–1134 — the post-D3a corrigendum). FORM: bold-headed dated corrigendum.

> “**Dated corrigendum (2026-08-12, post-D3a — the C2-3 box at empty
> support).** The D3a discharge pass (gpt-5.6-sol high,
> runs/cert3/D3a_grtja_output.log) adjudicated the C2-3 annex NEW-ISSUE
> at one corner: when S_A = ∅ (the frozen note's zero-read escape), the
> boxed equivalence's left side is vacuously true while |χ(S_A)| = 0.
> Per sol's own fix and the simplicity preference, the box's right side
> is re-displayed as
>
>     |χ(S_A)| ≤ 1 ,
>
> which is correct in every case: at S_A = ∅ both sides hold vacuously;
> at S_A ≠ ∅, |χ(S_A)| ≤ 1 ⟺ |χ(S_A)| = 1, the original criterion. The
> two-distinct-character refutation criterion is unchanged. Awaiting
> sol re-confirmation in the next queue.”

**DERIVATION.** An empty-support corner check on a criterion introduced four lines of history earlier.

**Mathematical audit.** At `S_A = ∅`: the scalar-existence side is vacuously true, while `|χ(∅)| = 0 ≠ 1` ✓ — so the `= 1` form fails at the empty corner ✓. The `≤ 1` form holds at `S_A = ∅` (`0 ≤ 1`) ✓ and, for `S_A ≠ ∅`, `|χ(S_A)| ≥ 1` always, so `≤ 1 ⟺ = 1` ✓. **The re-display is correct in every case, and the refutation criterion (two distinct character values) is genuinely unchanged** ✓.

**SUPERSESSION KIND:** `replacement`. **Layer 3 of C-3 — TERMINAL.**

**CONDITIONALITY.** “**Awaiting sol re-confirmation in the next queue**” — **and the confirmation landed**: SOL ledger row 20 records “the |χ(S_A)| ≤ 1 corrigendum **DISCHARGED at RC1**” ✓ (§5.2). `STALE-SELF-DESCRIPTION` in the direction of resolution.

**Compiler note.** **A correction to a correction, caught by the discharge pass of the correction** — the tightest audit loop in queue 8b, and it closed in one step.

**XREF.** `runs/cert3/D3a_grtja_output.log` — cited; `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 20 ✓.

---

### EFF.GRTJA.36  [record]

**CANONICAL STATEMENT** (verbatim, L1102–1120 — the E2 provenance paragraph). FORM: italic parenthetical.

*(Quoted in the four DERIVATION fields above, one clause per finding. Its closing ledger line:)*

> “Transcribed unaltered per the standing division of
> labor. Ledger: row 20 → all four repairs folded,
> awaiting sol discharge-confirmation (cert3).”

**DERIVATION.** [RECORD of a verification protocol]. **SERIES:** member 8 — with a **stale terminal**.

**Compiler re-verification of all four orchestrator legs.** **C2-1's arithmetic** ✓ (`.31`); **C2-2's translation** ✓ (`.32`); **C2-3's criterion** ✓ (`.33`); **C2-4's grid facts including the `(2,3,1)` witness giving `u = −1`** ✓ (`.34`). **Four of four re-derived and confirmed.**

**LEDGER STATUS — the closing claim is superseded at HEAD.** “awaiting sol discharge-confirmation (cert3)” is stale: `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` **row 20** reads

> “\| 20 \| GRTJA \| never sol-read as-built \| **CERTIFIED 2026-08-12** — E2 repairs (JA-EPS-CORR, degree-shift, scalar-gauge criterion, JA-GRID split) **DISCHARGED 3/4 at D3a** + the \|χ(S_A)\| ≤ 1 corrigendum **DISCHARGED at RC1** \|”

`grep -nF 'GRTJA' docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` → row 20 ✓. **Note the ledger's own precision: 3/4 at D3a, with the fourth (C2-3) discharged only after the corrigendum, at RC1** — exactly matching `.33`/`.35`'s chain. **The ledger and the note's append history agree to the step.**

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — row 20, verified.

---

## 4. XREF verification ledger

### 4.1 Designations and files

`[TABLE]`

| # | target | designation / object | status | consumed at |
|---|---|---|---|---|
| X1 | `GRTW2_PROOF_2026-08-08.md` | W-2 clauses 1/2/3, W2-L0/L2/L3, W2-C3, W2-BOX-1, W2-OPEN-2 | EXISTS ✓ | `.04`, `.06`, `.08`, `.11`, `.14`, `.16`, `.21`, `.27`–`.29` |
| X2 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | rows W-0/W-1/W-4; the J-A(ii) display JA-BOX-1 refutes | EXISTS ✓ | `.01`, `.15`, `.22` |
| X3 | `docs/MATH_COMPLETION_TREE_2026-08-01.md` | GD-3 MIN CORE, GD-5 §D2.2, GD-2's T-F check, GD-8 | EXISTS ✓ | `.05`, `.10`, `.13` |
| X4 | `GRB_ORDER2_2026-08-05.md` | N-1, REV 11/14 | EXISTS ✓ | `.12` |
| X5 | `verification/openmath/grb_order2_check.py` | the N-1 harness | EXISTS ✓ | `.12` |
| X6 | `verification/openmath/grt_ja_checks.py` | the sealed runner | EXISTS ✓ | `.01`, `.19` |
| X7 | `verification/openmath/grt_ja_checks_output.txt` / `…_results.json` | the sealed artifacts | both EXIST ✓ | `.19`, `.20` |
| X8 | `GRTJA_passPE1_report.md` … `GRTJA_passPE6_report.md` | the hostile reports | EXIST ✓ | `.23` |
| X9 | `runs/cert/C2_grtja_output.log` | the sol as-built read | EXISTS ✓ | `.30` |
| X10 | `runs/cert2/E2_grtja_output.log` | the E2 adjudication | EXISTS ✓ | `.30`–`.36` |
| X11 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | row 20 | EXISTS ✓, row located | `.35`, `.36` |
| X12 | `[ILN]†` | the print, consumed as-of `ced7dbb` | commit ✓ | `.04`, `.26` |

**Zero NEAR-MISS, zero invented names, zero designation OPEN-CALLs.** Note that GRTJA's citations are predominantly **tex line numbers into a print** (tex 220, 449, 828, 829, 882, 912, 1028, 1149, 1200–1201, 1213–1218, 1291, 1377, 1431, 1447, 1497), which this compilation **cannot verify** — the print is outside the repo. **Recorded as a systematic verification limit of this note**, not a defect: the tex anchors are the note's characteristic evidence form and are checkable only against the source PDF. FC-4 (`.29`) shows the corpus does audit them (it corrects an anchor as “picture-environment line numbers, semantically nil”).

### 4.2 PIN VERIFICATION ledger (rule 23)

**Commit hashes — 8 checked, 8 verified:** `696eae8`, `1670f67`, `0efa82e`, `f131c53`, `ffa1e57`, `ced7dbb`, `5054d69`, `adc6cf3`. **Zero failures.** **Four further commits cited and NOT checked** (`83f47f4`, `66b3498`, `4c4ee56`, `17d2a32`) — recorded at `.27`/`.28` as unverified rather than passed.

**md5 pins — 1 cited, 1 verified and localized:** the frozen-body prefix `cba309ce` → **line 850**, unique hit ✓.

**`UNPINNED-VALUE` — the sealed artifacts.** `.19`/`.22`: the runner and its two artifacts are pinned by seal commit `696eae8` only; no md5 is displayed. Recorded.

**Artifacts — 12 cited, 12 exist.** Zero missing.

---

## 5. Consumption table and consumer edges

### 5.1 What GRTJA consumes

`[TABLE]`

| supplier | object | grade at composition | grade at HEAD (per FC-2) | consuming units |
|---|---|---|---|---|
| `[ILN]†` S0.1/S0.2 | the class pin | accepted | accepted (as-of `ced7dbb`; two pure appends since) | `.04`, `.26` |
| GMN HigherNewton | the print (tex anchors) | literature | literature | `.04`–`.10` |
| W-2 (GRTW2) | clauses 1/2/3, W2-L0/L2/L3, the chamber | attempt (0/2) | **ACCEPTED 2/2** (`adc6cf3`) | `.04`, `.06`, `.08`, `.11`, `.14` |
| N-1 (GRB order 2) | the order-2 operator instance, against FGMN | accepted, family-ledger | accepted | `.12` |
| GD-5 | the order-1 floor | nearly closed | nearly closed | `.13` |
| engine_ext | the standing agreement gate | standing rule | standing rule | `.19` (EXT-GATE) |

### 5.2 Reverse-XREF rows — who consumes GRTJA

`[TABLE]`

| # | consumer | what is consumed | status |
|---|---|---|---|
| RX-1 | the J-B unit (W-3/W-4 development) | the operator dictionary; the `[JA-r2]`-tagged JB rows named in C2-4's sweep | **intended**, per §7.3; the C2-4 sweep confirms JB rows exist that read JA-GRID |
| RX-2 | the W-5 tree unit | the dictionary | **intended** |
| RX-3 | the weld campaign ledger at J-A | the claims table | **intended** |
| RX-4 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 20 | the note's certification status | **LANDED** — CERTIFIED, 3/4 at D3a + the corrigendum at RC1 |
| RX-5 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | **outbound and NOT landed** — JA-BOX-1's refutation is “review-owed”; the blueprint still displays the refuted form | **NOT LANDED** — see OPEN-CALL 1 |

**Note on §7.3's word “(intended)”.** The note marks its consumer list as intended rather than verified, and this compilation preserves that: RX-1…RX-3 are **declared** edges, and only RX-1 has independent corroboration (C2-4's sweep names “the `[JA-r2]` downstream JB rows”).

---

## 6. TEETH — the inverse table (rule 6)

### 6.1 Battery row → guarded unit(s)

`[TABLE]`

| family | guards | disposition |
|---|---|---|
| EXT-GATE (1) | the engine agreement gate | clean |
| JA-PIN (111) | `.04` clauses 2–7 | clean — **7 of 8 clauses doubly evidenced** (print cite + machine) |
| CK-VAL (1,132) | `.05` | clean, both engines |
| CK-EPS (872) | `.06` | clean — **and survives C2-1** (the legs tested the corrected content) |
| ORB-EPS (1,744) | `.11` | clean |
| CK-GRID (3,248) | `.07` | clean — **scope-narrowed by C2-4** |
| CK-RES1 (340) | (VD-1) = W2-L3 | clean |
| CK-RES (443 scored) | `.08` | clean at scored rows; **16 boundary rows recorded not scored** (`.20`) |
| CK-VDM (443) | `.09` forward | clean |
| CK-BPREF (26 hits) | `.15`'s refutation | fired on all designated rows; **criterion corrected twice** (`.33`, `.35`) |
| ORB-RES (444) | `.11` | clean |
| TW-INST (1,452) | `.11`'s chamber re-instantiation | clean |
| JA-QO (5) / JA-D0 (4) | fresh shapes + PARI ties | clean |
| MJ-EPS / MJ-VAL / MJ-GRID | teeth | fired — MJ-VAL's “unsheared v 11/11” certifies `.05`'s convention pin load-bearing |

### 6.2 Guarded unit → battery row

`[TABLE]`

| unit | guarded by | class |
|---|---|---|
| `.03` the map T | JA-PIN (111) indirectly | weakly guarded |
| `.04` JA-PIN | JA-PIN (111), clauses 2–7 | battery-guarded; **clause 8 consumed, clause 1/5 print-only** |
| `.05` JA-VAL | CK-VAL + MJ-VAL | battery-guarded |
| `.06` JA-EPS | CK-EPS + ORB-EPS + MJ-EPS | battery-guarded — **yet the CRITICAL was here** |
| `.07` JA-GRID | CK-GRID + MJ-GRID | battery-guarded — **yet C2-4 narrowed it** |
| `.08` JA-RES | CK-RES (scored) | battery-guarded on the proviso's interior |
| `.09` JA-VDIND | CK-VDM (forward only) | half-guarded; **converse witnessed only by PE8** |
| `.10` JA-MIN | rides `.08` | inherited |
| `.11` §4 transport | ORB-EPS/ORB-RES/TW-INST | battery-guarded on the orbit half; **chamber half consumed** |
| `.15` JA-BOX-1 | CK-BPREF (26) | **inverted guard** — the tooth certifies a refutation |
| `.16`–`.18` boxes | — | **PROOF-ONLY / disclosure** |
| `.26`–`.36` appends | — | **AUDIT-produced** |

### 6.3 PROOF-ONLY rows (rule 16)

The note's own coverage sentences:

§7.3: “Fences: instance evidence = the §7.1 roster (reads ≤ 4+top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀ leg, wild rows included); F_p[[t]] rows have no PARI leg (JA-BOX-4)”.

JA-BOX-2 (`.16`): “W-1's FULL "operator dictionary at all orders" therefore remains OPEN beyond the displayed forms; J-A does not claim it.”

So `.16`, `.17`, `.18`, JA-PIN's clauses 1 and 5, and the whole `m ≥ 3` uncollapsed regime are proof-carried or fenced. **The striking fact is elsewhere:** **both C2 corrections that hit theorems (`.31` JA-EPS, `.34` JA-GRID) hit BATTERY-GUARDED units.** Unlike HE6 and HE6R1 — where the decorrelated reads found defects in the proof-only set — GRTJA's decorrelated read found defects in **statements whose content the machine legs had confirmed thousands of times**. The reason is recorded at `.31`: the legs tested the *corrected* relation; the *display* was what overreached. **A machine leg cannot catch a statement that misdescribes what the leg computes.**

### 6.4 AUDIT dispositions (rule 27)

`[TABLE]`

| unit | AUDIT class | why no tooth applies |
|---|---|---|
| `.15` JA-BOX-1 | `in-house hostile pass` + machine census | a refutation of a *blueprint*, not of the note |
| `.20`'s `[JA-r1]` recount | `arithmetic recount` | a row-count recount against the committed JSON |
| `.16`'s `[JA-r2]` | `in-house hostile pass` | 8 machine witnesses against a perimeter's definition |
| `.26`–`.29` FC-1…FC-4 | `transfer audit` ×4 | supplier motion and grade billing; no tooth reads supplier grades |
| `.31` C2-1 (CRITICAL) | `decorrelated-model audit` | a display that misdescribes what the legs compute |
| `.32` C2-2 | `decorrelated-model audit` | a `ν`-shift in supports and degrees |
| `.33` C2-3 | `decorrelated-model audit` | a refutation *criterion* too generous by one case |
| `.34` C2-4 | `decorrelated-model audit` | an unconditionality claim needing `u(V) ≥ 0` |
| `.35` the corrigendum | `decorrelated-model audit` | an empty-support corner of a four-day-old correction |

**Nine audit-produced corrections; none from a tooth.** The 17 families and 10,311 samples were GREEN throughout.

### 6.5 Zero-orphan check

**Battery rows → units: zero orphans** — all 17 families guard at least one unit.

**Units → guards: 36 units, 13 guarded, 23 unguarded.** The 23: 5 fences/boxes, 1 map, 6 records/tables, 11 append units covered by §4/§5. **No unit silently unguarded.**

---

## 7. Arithmetic and fidelity audit

### 7.1 Arithmetic audit

**Confirmed exactly:** `.08`'s exponent cancellation `t(i) − τ_{m−1}(a_i) = −i·A_{m−1}` ✓ (the note's central computation); `.20`'s two censuses (`7 + 9 = 16`; `22 + 4 = 26`; the roster list has exactly **10** entries, confirming the `[JA-r1]` recount from 12) ✓; `.21`'s W2-C3 split `38 + 6 = 44` ✓; **C2-1's `z^{t_Def} = z^ν·ε_m(β)`, hence raw equality iff `z^ν = 1`** ✓; **C2-2's `Supp H = ν + Supp P`, `deg H = deg P + ν`, with `ord_ψ` unaffected because `ψ ≠ y`** ✓ (JA-PIN clause 5); **C2-3's criterion — a scalar exists iff `χ` is constant on the active support** ✓; **C2-4's `(e,h,V) = (2,3,1)` witness giving `u = −1`** ✓; **the corrigendum's `≤ 1` form correct at both `S_A = ∅` and `S_A ≠ ∅`** ✓. Every one of the four E2 provenance re-derivations reproduced independently.

**Finding — one:**

**AF-1 — §7.1's sample column sums to 10,265, not the headline 10,311.** The 46-sample residual is presumably the teeth rows (“3/2/2 rows”, no sample counts given). **The table alone does not reconcile**; the note's own figures are internally consistent otherwise. **Recorded as not independently reconciled**, honestly rather than passed. *(By contrast, `.20`'s two censuses reconcile exactly, so the note's census arithmetic is sound where it is displayed.)*

**Systematic limit — the tex anchors.** Roughly fifteen distinct print line citations carry JA-PIN's clauses and JA-EPS's sign convention. **None is verifiable from inside this repo.** Recorded at §4.1.

### 7.2 Fidelity audit

- Every CANONICAL STATEMENT is verbatim or `[ASSEMBLED]`; **no `[ASSEMBLED]` statement appears.**
- **No exponent, index, sign, grade, count or perimeter was altered anywhere.** The sign convention of `.06` is quoted with its explicit CHILD orientation, as the note states it.
- **Truncations: four**, at `.02`, `.17`, `.18` and `.31`–`.34` (the C2 annexes' long LaTeX bodies), each marked with an explicit bracket or ellipsis naming what was cut and where it lives.
- **Rule 14 not triggered** — no fenced ASCII table (checked, not skipped). Two Markdown tables transcribed as `[TABLE]`.
- **8 commits + 1 localized prefix md5 + 12 artifacts verified; 4 commits cited-and-unchecked, recorded as such.**
- **12 designations/files grep-or-existence-verified; zero NEAR-MISS.**
- Every cross-note status claim checked against the target where the target is in-repo (rule 10) — which is how the ledger's supersession of `.36`'s “awaiting discharge” was found, and how RX-5's non-landing was established.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — JA-BOX-1's blueprint refutation is “review-owed” and has not landed. FOR-0b.

`.15` **REFUTES** a displayed formula of `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` with **26 machine witnesses**, marks itself “review-owed”, and does not edit the blueprint. **At HEAD the blueprint still carries the refuted display** (the note edits nothing; no landing record exists in this note or in the ledger row). **And the refutation's criterion has since been corrected twice** (`.33`, `.35`), so what is owed to the blueprint is now the corrected criterion, not the frozen one.

**Decision needed:** whether the blueprint receives a dated correction carrying (a) the refutation, (b) `THEOREM JA-RES` as the corrected display, and (c) the `|χ(S_A)| ≤ 1` criterion. **The compiler has applied nothing.** Note this is the only *outbound, unlanded* obligation in GRTJA — its other four staleness items (FC-1…FC-4) were all closed within a day.

### OPEN-CALL 2 — the FAVORABLE/OVERSTATING direction rule is now stated by two notes and written down nowhere. FOR-0d.

FC-2 (`.27`) classifies a stale supplier grade as **FAVORABLE** because “(0/2 hostile passes)" is now a conservative understatement everywhere it appears; nothing this note consumes weakened”. HE6R1's PE3 F-2 (`spec/EFF-HE6R1.md` `.40`) states the converse: an *overstating* stale grade is “the one stale-grade site whose direction is NOT conservative”. **Two notes, independently, have arrived at the same discriminating rule:** *re-date only in the overstating direction; understatements are safe.*

**Decision needed:** whether this becomes a written corpus convention. It would settle OPEN-CALL 1 of `spec/EFF-HMENU3.md` and OPEN-CALL 3 of `spec/EFF-HE6R1.md` at once, and it is cheap — a note need only classify each stale billing's direction, as GRTJA already does for all four of its fold-carry items.

### OPEN-CALL 3 — a CRITICAL against an ACCEPTED note, and what the acceptance now means. FOR-0d — NEEDS ASVIN.

GRTJA was **ACCEPTED 2/2 after eight hostile passes and five repairs**, with a 17-family sealed runner GREEN at 10,311/0 and two decorrelated PE8 routes at 385,057/0 and 5,519/0. **Four days later a decorrelated as-built read returned 1 CRITICAL + 3 REAL findings, all upheld.** None broke a consumer — every sweep found the consumers already used the corrected content — but the CRITICAL was against a *displayed theorem of an accepted note*.

**The structural lesson is recorded at 6.3:** the defects were in **battery-guarded** statements, and the machine legs could not have caught them, because the legs computed the corrected relation while the display misdescribed it. **No amount of sample count closes that gap.**

**Decision needed:** whether the corpus wants a standing rule that **acceptance does not close a note to as-built certification**, and if so what an accepted-then-corrected note's grade is called. GRTJA's own answer, visible in its appends, is: the acceptance stands, the corrections land as dated annexes, and the ledger records CERTIFIED with the discharge counts (3/4 at D3a + 1 at RC1). **That answer is good; it is simply not written down as policy.**

### Recorded source defects and reading hazards

1. **`.06`: THEOREM JA-EPS as displayed is an identity only at `ν = 0`.** The governing form is `JA-EPS-CORR`. **Any consumer quoting the frozen JA-EPS is quoting a CRITICAL-corrected statement.**
2. **`.07`/`.10`/`.15`: three more displayed statements narrowed or corrected by C2-2/C2-3/C2-4.** Of the ten §7.2 rows, **four moved**.
3. **`.15`: the blueprint refutation has not landed** (OPEN-CALL 1).
4. **`.21` and passim: every “(attempt grade 0/2)” billing is stale**; FC-2/FC-3 close the supplier side, `.24` the note's own.
5. **AF-1: §7.1's sample column does not sum to the headline** (10,265 vs 10,311).
6. **§4.1: ~15 tex anchors are unverifiable from inside the repo.** FC-4 shows one such anchor was already found to be an artifact of picture-environment numbering.
7. **`.09`: JA-VDIND's converse is “unsealed”** in the frozen text; PE8 later witnessed its escapes constructively, but §7.2's row still reads “converse unsealed”.
8. **`.19`/`.22`: the sealed artifacts are `UNPINNED-VALUE`** (commit-pinned, no md5), unlike HE6's fully hashed set.
9. **`.27`/`.28`: four cited commits were not verified in this compilation** (`83f47f4`, `66b3498`, `4c4ee56`, `17d2a32`).
10. **`.36`: “awaiting sol discharge-confirmation (cert3)” is superseded** by ledger row 20 (CERTIFIED; 3/4 at D3a + the corrigendum at RC1).

### Exhaustive residual judgment list

There are no other unresolved GRTJA mathematical or scope judgments. JA-BOX-2's all-orders opening, JA-BOX-3's print underdetermination, JA-BOX-4's equal-characteristic deferral, JA-BOX-5's principal-read fence, and JA-MIN's open `in(f)` leg are the note's own displayed fences; the stale billings, the unreconciled sample total and the unverified commits are bookkeeping. The three OPEN-CALLs are the complete list.

### Compilation summary

- **36 statement units** across the frozen body (`.01`–`.23`), the acceptance record (`.24`, `.25`), four fold-carry annexes (`.26`–`.29`), the sol C2/E2 wave (`.30`–`.34`), the D3a corrigendum (`.35`) and the provenance record (`.36`).
- **12 designations/files verified; zero NEAR-MISS; zero invented names.** ~15 print tex anchors recorded as a systematic verification limit.
- **8 commits + 1 localized prefix md5 (L850, unique) + 12 artifacts verified; zero failures.** Four cited commits recorded as unverified.
- **5 reverse-XREF edges**, of which three are the note's own “(intended)” consumers, one is the LANDED ledger row, and **one is an unlanded outbound blueprint correction** (OPEN-CALL 1).
- **One SERIES** (the eight-member ARC series `.01` → `.23` → `.24` → `.36`), **twelve supersession chains**, and **four distinct SUPERSESSION KINDs** — with the queue's **only CRITICAL** and its **only correction-to-a-correction** (`.33` → `.35`).
- **Arithmetic audit: every one of the four E2 re-derivations reproduced independently**, along with the note's central exponent cancellation and both censuses. One finding, not a mathematical error.
- **Honest headline for a chapter cut:** GRTJA is the corpus's case study in **what acceptance does not buy.** Eight passes, five repairs, 10,311 GREEN samples and two decorrelated 100k+ routes did not prevent a CRITICAL four days later — because all of that evidence tested what the operators *do*, while the defect was in what the theorem *said they do*. Every consumer survived, precisely because every consumer used the operators rather than the display.

EFF-GRTJA COMPILED: 36 statements / 12 xrefs verified / 3 open calls
