# EFF-GRTJC-s2of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` (3059 lines, 217,445 bytes).

**HOME range:** source lines **662–1937** inclusive — **§2 CLAUSE W-6** (the carry target exists: JC-DOM, JC-GAUGE, JC-PER, JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD, JC-PSIKER, and §2.10's repaired coordinate calculus JC-LOC/JC-PIINV/JC-BSURJ/(COORD-B)/(DMULT)/(MULT-B)/JC-COB/TC-3), **§3 CLAUSE W-7** (the anchor-transport isomorphism Ψ: OB-2 … OB-5, JC-CARRY-m, JC-INNER, JC-IND), **§4 CLAUSE W-8** (harness-val = TC-read, the offset-transport lemma, the residue chain), **§5 CLAUSE W-9** (cocycle semantics, FINDING JC-F1, FINDING JC-F2), **§6** the cyclic fence as LAW JC-CYC, and **§7** the case split. **This is the shard that carries the four weld faces W-6, W-7, W-8, W-9.** Lines 1–661 (shard 1) and 1938–3059 (shard 3) are used ONLY to resolve material homed here.

**HEAD blob hash:** `b07f08f52c1cf2d84af7e8167b8daf2f791a4f8c` (clean; last touched by commit `e2403a2b`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (rules 1–28); temporary IDs `EFF.GRTJC.s2of3.<nn>`. Companion shards: `spec/EFF-GRTJC-s1of3.md` (53 statements / 28 xrefs / 5 open calls), `spec/EFF-GRTJC-s3of3.md`.

**SHARD-COUNT RECONCILIATION.** `runs/qgen/sweep_manifest.txt` line 48 gives this exact range as `s2of4`; the charge names three shards. Full reconciliation at `spec/EFF-GRTJC-s1of3.md` §1 (manifest rows 49+50 merged into shard 3, so no annex is separated from what it supersedes). **This shard's range is the manifest's own, unmodified.** Boundaries re-verified at HEAD: L660 `---`, L661 blank, L662 `## §2.`; L1936 `---`, L1937 blank, L1938 `## §8.`.

**GENRE: TAG-SPARSE PROSE PROOF (density 0 in the note's own prose).** In THIS range the note supplies strong boundary signals: four blockquoted `> **THEOREM W-k.**` / `> **COROLLARY W-9.**` face boxes each ending in a `**GRADE:**` block, thirteen `**LEMMA/THEOREM/COROLLARY JC-XXX.**` openers with `*Statement.*` / `*Proof.*` / `*Machine:*` sub-fields, four named displays `(COORD-B)`, `(DMULT)`, `(MULT-B)`, `(DMULT-w)/(DMULT-s)`, two `**FINDING JC-F1/F2**` blocks, a five-part `**LAW JC-CYC**`, and two source tables. **Boundaries are mostly READ OFF; §6 records the five genuinely chosen calls.**

### ★ SPECIAL-CARE DECLARATION — W-9's supply clauses (per the Q7 charge)

**The charge directs: “W-9's exact supply clauses are consumed by the WELDZERO unit and the weld audit, so compile the W-9 statement units with special care.”** Discharged as follows, and the compiler records the verification rather than asserting it:

- **W-9's four clauses are homed at `.37`, quoted BYTE-VERBATIM and UNTRUNCATED**, each clause separately identified, with a per-clause consumer column.
- **The consuming quotation was checked against the source.** `lean/notes/openmath/WELDZERO_2026-08-14.md` L151 cites “**What W-9 supplies, clause by clause** (`GRTJC_PROOF_2026-08-08.md` **L1777–1788**)”. **This compiler re-read GRTJC L1777–1788 at HEAD: the range is EXACT — it opens at `> **COROLLARY W-9.** Given W-6, W-7, W-8: (i) …` (L1777) and closes at `> **GRADE: PROVED given W-6..W-8 (general m), S-priced as the blueprint says.**` (L1788).** The four clauses (i)–(iv) lie wholly inside it. **WELDZERO's quotation is faithful (elided with `…`, no wording altered).**
- **The weld audit's row is recorded too.** `runs/qgen/WELD_FACE_AUDIT.md` L123 classifies “**COROLLARY W-9 / `GENHN-BOX-2`** (GRTJC's twisted algebra at GENHN-4 layer 1, μ ≥ 3)” as “**R&C — the only weld face inside a count law**”, and L106 records that the one reachable GRTJC face, **COROLLARY W-9, rides the CITABLE tier `(DMULT-w)`** — not the measured `(DMULT-s)`. **Both facts are verified against `.16` and `.37` below and are consistent with the note's own text** (`GRTJC` L1985–1990: “If **(DMULT-w)** failed …, **W-8 and W-9 fail together**; if only **(DMULT-s)** failed …, **the structural clauses stand**”).
- **The WELDZERO replacement is recorded clause by clause at `.37`**, because the retirement of GENHN-BOX-2 turns on exactly which W-9 clause supplies what.

### FREEZE PREDICATES (rule 21)

All four freezes declared in shard 1 govern this range and are not re-derived: **(1) INSTRUMENT FREEZE** (three batteries + the instrument; the two pinned md5s re-computed EXACT at HEAD). **(2) LITERATURE-PIN FREEZE** (the FGMN PDF, md5 `da846c82f1fcb619cefb3feb8164191e` — **re-computed EXACT at HEAD by this compiler**). **(3) SWEEP-CENSUS FREEZE** (every sweep or diversity figure must be a scored/censused fact with its unit and committing commit). **(4) TEXT FREEZE** (post-acceptance; every Annex #1–#8 correction is an APPEND).

### Governing effective-text record

**EFFECTIVE TEXT FOR THIS SHARD = lines 662–1937 exactly as written (all `[r1]`–`[r6]` brackets already landed, strike markup preserved), READ AS CORRECTED by the out-of-range appends wherever they name an in-range sentence.**

**FIVE of the eight annexes land inside this range, and this is the shard they hit hardest:**

| annex | lines (shard 3) | in-range target homed here | severity |
|---|---|---|---|
| **#1** | 2805 | `(DMULT-s)` (`.16`), JC-COB (`.19`) — **PROVED-conditional** on the measured perimeter | upgrade |
| **#4** | 2840–2884 | **§4.1's proof (`.33`) — SUPERSEDED from “Apply ρ_{λ+N}” through “The two agree.”** | **★ a CRITICAL, cured** |
| **#5** | 2890–2911 | **W-6(iv) (`.01`), JC-LOAD(a) (`.09`) — re-displayed with the load-set qualifier** | **★ REAL** |
| **#6** | 2917–3000 | **`(DMULT-w)` (`.16`) — the “quoted FGMN identity” claim WITHDRAWN; DERIVED via LEMMA JC-RANKMULT** | **★ REAL** |
| **#8** | 3014–3037 | **JC-SCAL (`.07`), JC-BSURJ (`.14`) — quantifier narrowed to `c ∈ K^*`** | **★ REAL** |

**Annex #4 cures a CRITICAL against a live proof in this shard.** Annexes #5, #6, #8 correct three further displayed statements homed here. **No in-range sentence is edited; every correction is applied at its unit with the annex text quoted.**

### Scope split (rule 7 + rule 17)

**A. ABSORPTION / supply SET — this shard IS the supply.** Four faces: **W-6** (the carry target exists at every composite stage), **W-7** (the anchor-transport isomorphism Ψ), **W-8** (harness-val = TC-read), **W-9** (cocycle semantics, given W-6..W-8). Plus the cyclic fence as **LAW JC-CYC** and the eleven-genre case split.

**B. APPEND / consumption PROTOCOL scope. NO-APPENDS; NO GATE RETIRES.** Declared in shard 1 `.02` and restated at §10.3 (shard 3): “**The tie is displayed, the gate stands.**” **Zero dated consumption appends are claimed landed on any supplier by this note, and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED.** Five post-acceptance annexes (above), all from the decorrelated sol certifier via the orchestrator. **Plus the inherited GRTJB fences** (`(IN-4)`, shard 1 `.44`), consumed at `.26`.

### Resolution rules applied

1. Lines 662–1937 supply the HOME material listed above.
2. `[r1]`–`[r6]` brackets are ALREADY-LANDED text applied in place; the later bracket governs. Multi-layer stacks carry `CHAIN:` with TERMINAL marked (rule 25); this shard has two (`.16`'s `(DMULT)` tiers, `.11`–`.21`'s `(COORD)` → `(COORD-B)` repair).
3. `~~…~~` is supersession, never deletion. **In this range the struck text is repeatedly a FALSE MATHEMATICAL STATEMENT the note keeps on the record** (`.11`'s `(COORD)`, `.10`'s over-quantified closing sentence, `.18`'s `(MULT)`, `.29`'s honest rider, `.34`'s two identifications, `.42`'s false trigger).
4. Out-of-range appends are applied as CONDITIONALITY at the in-range units they name, with the annex text quoted; **no in-range sentence is edited.**
5. Out-of-range statements are NOT emitted as units here.
6. External repo records are reading notes only.
7. **CITE-SCOPE rows are compiled AS THE NOTE STATES THEM**; the NS-9/NS-10 resolutions are recorded once, in shard 1 `.43`, and referenced here.
8. **W-9 receives the special-care treatment declared above.**

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or `[ASSEMBLED]`; truncation marked `…`. **The four face boxes and the (DMULT) tier displays are DOUBLE-EMITTED** (rule 14) where they are fixed-width. §7's case-split table is transcribed as a `[TABLE]` with an arithmetic audit. Compiler ledgers are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GRTJC.s2of3.01  [lemma]  ★ THEOREM W-6 — the face box

**CANONICAL STATEMENT:** verbatim, lines 664–699 — the theorem box with its five clauses, the GRADE line and the `[r1]` post-repair grade.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-6.** For every tower T of the [ILN]† class and every level m with
> E > 1: (i) TC-1 and TC-2 are legitimate ring-level operations on gr(w_{m+1});
> (ii) the gauged ring A(T) := gr(w)[in(π)^{-1}]/(in(π) − 1) is **ℤ/E-graded**,
> with ~~A_ν ≅ gr_n(w)-piece for any n ≡ ν~~ **[r1, G1: corrected to JC-GAUGE's
> actual conclusion]** `A_ν ≅ B_n` **for any n ≡ ν, where
> B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE} is JC-DOM's POST-TC-1 piece** — strictly
> bigger than gr_n in general (the slot bound maxslot(n+kE) of §2.10 grows
> strictly along the ladder infinitely often, so the injective transition maps
> in(π)·gr_{n+kE} ⊆ gr_{n+(k+1)E} are not onto and B_n is the strictly larger
> colimit; PE1's C2I ladder [(0,0),(1,0),(2,1),(3,1),(4,2),…] exhibits it). The
> lemma was always right; the r0 statement quoting it was not, and the
> distinction is load-bearing: B_n, not gr_n, is where Δ ≅ K_m[y] lives (§2.10
> [r1, F1]) — and the surviving index is the
> abscissa-coset index of §1's split (LEMMA JC-FIB); (iii) the anchor map
> γ ↦ [φ_γ] is E-periodic on the nose (LEMMA JC-PER), so it is defined on ℤ/E;
> (iv) **TC-3 is load-bearing exactly on the pairs with δ ≥ g_m** (THEOREM
> JC-LOAD), and the outer factor z̄^δ of c_T is TC-3's image of the graded slot
> shift y^δ — not obtainable from TC-1/TC-2 alone; (v) TC-3 is not a relabeling:
> the level-NR read is non-injective on a graded piece, with the classifier's own
> next key Φ_{m+1} as the kernel witness (COROLLARY JC-PSIKER).
>
> **GRADE: PROVED at general m** on inputs (IN-3)(a)(b)(c)(e) + (IN-5), with the
> single located exception of the **top-flat corner e_m = 1 ∧ g_m = 1** in
> JC-LOAD's sharp form (JC-BOX-4). Attempt grade 0/2.
>
> **[r1] GRADE, post-repair (supersedes the input list only).** Still **PROVED
> at general m**, and on a SMALLER literature footprint: the coordinate calculus
> now rides `(DMULT-w)` **[r2, G-1: the citable tier; the exact tier (DMULT-s)
> is MEASURED-only and carries JC-COB's sharp form alone]** (composite-stage
> residual multiplicativity) instead of
> (IN-3)(c)-on-gr, with (IN-3)(a)(b)(e) + (IN-5) unchanged; clause (ii)'s object
> is B_n (G1); clause (v) is re-quantified (F2). Boxes: ~~JC-BOX-4 (unchanged)~~
> **[r2, G-7: the box DID change at r1 — it gained a CONDITIONAL CLOSURE on
> (DMULT) (the corner is closed for a reader who grants (DMULT-w), open for one
> who wants it FGMN-independent); see JC-BOX-4 [r1]]** and
> JC-BOX-3 **re-cut to box APPLICABILITY, not literature truth**. Attempt 0/2.”

**Double-emission (rule 14) — the five clauses as a `[TABLE]` with their status at HEAD:**

| clause | statement | proved by | status at HEAD |
|---|---|---|---|
| **(i)** | TC-1 and TC-2 are legitimate ring-level operations on `gr(w_{m+1})` | JC-DOM (`.02`), JC-GAUGE (`.03`) | **PROVED, general m** |
| **(ii)** | `A(T) := gr(w)[in(π)^{-1}]/(in(π)−1)` is **ℤ/E-graded**, with `A_ν ≅ B_n` for any `n ≡ ν` | JC-GAUGE(iii) + JC-DOM | **PROVED**; **object corrected at r1/G1 from `gr_n` to `B_n`** — “`B_n`, not `gr_n`, is where `Δ ≅ K_m[y]` lives” |
| **(iii)** | the anchor map `γ ↦ [φ_γ]` is **E-periodic on the nose**, so defined on `ℤ/E` | JC-PER (`.04`) | **PROVED**, byte-exact |
| **(iv)** | **TC-3 is load-bearing exactly on the pairs with `δ ≥ g_m`**; the outer factor `z̄^δ` is TC-3's image of `y^δ` — **“not obtainable from TC-1/TC-2 alone”** | JC-LOAD (`.09`) | **SUPERSEDED IN DISPLAY by Annex #5** — the outer factor is *always* `q(y^δ) = z̄^δ`; it is *unavailable as a pre-TC-3 scalar* **exactly when `δ ≥ g_m`** |
| **(v)** | TC-3 is not a relabeling: the level-NR read is non-injective **on a graded piece**, with `Φ_{m+1}` as the kernel witness | JC-PSIKER (`.10`) | **PROVED; the fenced wording “on a graded piece” was ALREADY CORRECT and stands unamended** — only r0's unfenced generalization was refuted (r1/F2) |

**CHAIN (rule 25) — the input list, THREE layers:** r0 “(IN-3)(a)(b)(c)(e) + (IN-5)” → **r1**: `(IN-3)(c)`-on-`gr` replaced by `(DMULT)`, **a SMALLER footprint** → **r2/G-1**: `(DMULT)` split, only `(DMULT-w)` load-bearing. **TERMINAL: `(IN-3)(a)(b)(e) + (IN-5) + (DMULT-w)`, with `(DMULT-w)` itself DERIVED post-acceptance (Annex #6).** `CHAIN HOME: s1of3.43.`

**★ CONDITIONALITY — Annex #5 re-displays clause (iv), and the correction is REAL** (shard 3, L2890–2911):

> “**[ANNEX 2026-08-12 #5, post-acceptance correction — exact scope of outer-factor non-obtainability.]** This annex supersedes W-6(iv), JC-LOAD(a), and **every unqualified occurrence of “`z̄^δ` is not obtainable from TC-1/TC-2 alone”** by the following display:
> **The outer factor is always `q(y^δ) = z̄^δ`, and it is unavailable as a pre-TC-3 scalar exactly when `δ ≥ g_m`.**
> … * if `δ < g_m`, then `y^δ` is already the canonical degree-`< g_m` representative of `z̄^δ`, so the outer factor — and, after multiplication by the inner `K_m^*`-unit, the complete scalar — **is obtainable before TC-3**;
> * if `δ ≥ g_m`, no nonzero polynomial of degree `< g_m` equals `u y^δ` with `u ∈ K_m^*`, so **TC-3 is indispensable**.”

**SUPERSESSION KIND: `partial-withdrawal`** (the enum gap the GRTJB shards identified — a display is re-issued, most of the clause survives). **Annex #5's own consumer sweep:** “JC-LOAD's iff and its sealed set identity survive unchanged. §3.2's structural outer/inner split survives … §7 genres 1–2 remain RAW-solvable and genres 3–4 retain the stated `g_m = 1` split. W-7, W-8, and W-9 consume the factor's value or shape, **not the refuted universal interpretation**, and survive.”

**Also conditional:** the **top-flat corner `e_m = 1 ∧ g_m = 1`** is the single located exception (JC-BOX-4), **CONDITIONALLY CLOSED at r1 on `(DMULT-w)`** — “closed for a reader who grants (DMULT-w), open for one who wants it FGMN-independent”. **The grade line's “Attempt grade 0/2” is EXPRESSLY superseded by Annex #7.**

**DERIVATION:** Clause by clause, `.02`–`.10`.

**RESOLUTION TRACE:** statement lines 664–699; proof lines 701–1414 (§2's lemmas); correction sites 2890–2911 (Annex #5), 3004–3008 (Annex #7), 2004–2027 (JC-BOX-4, shard 3), 1960–1992 (JC-BOX-3, shard 3).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — grep-verified count **11**.

**TEETH:** JC1–JC6 + MJ1–MJ5 (§9.2, shard 3): 8,566 samples, 0 violations, all five teeth fired.

---

### EFF.GRTJC.s2of3.02  [lemma]  LEMMA JC-DOM — TC-1 is legitimate

**CANONICAL STATEMENT:** verbatim, lines 703–716 (statement and proof).
**FORM:** bold-headed lemma with `*Statement.*` / `*Proof.*`.

> “*Statement.* gr(w) is a commutative ℤ-graded domain; in(π) is homogeneous of
> degree **E** and is a nonzerodivisor; hence the localization
> B := gr(w)[in(π)^{-1}] exists as a ℤ-graded ring, gr(w) ↪ B, and
> B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}.
>
> *Proof.* By (IN-3)(a) w is multiplicative, so for f,g ≠ 0,
> in(f)in(g) = in(fg) ≠ 0 in gr_{w(f)+w(g)}: gr(w) is a domain ((IN-3)(b), the
> same domain property the accepted GRB S6a cancellation uses). For the degree:
> w_0(π) = 1 and, since the Φ_j-development of the constant π is A_0 = π,
> w_{j+1}(π) = e_jw_j(π); hence **w(π) = e_0e_1⋯e_m = E** by induction. A
> nonzerodivisor homogeneous element of a graded domain may be inverted: the
> graded localization at the multiplicative set {in(π)^k} is a ℤ-graded ring, with
> the stated degree pieces, and the localization map is injective because gr(w) is
> a domain. ∎”

**CONDITIONALITY:** **Consumes `(IN-3)(a)` and `(IN-3)(b)` — the two clauses NEVER refuted**, and the two that r5/G-2 had to ADD to the stack displays (shard 1 `.14`). **`w(π) = E` is proved by induction here, not cited.**

**★ THE REMARK IS THE POINT** (lines 718–721): “GRW2_TIE_DESIGN's OB-1 asked for exactly this at the composite stage and recorded ‘no accepted clause supplies it’. **The supply is multiplicativity of w — which is (IN-3)(a), a literature fact for types of every order, not a last-read-layer accident.**” **So an open design-note obligation is discharged by identifying the right citation.**

**GENERALITY NOTE (Q7, recorded not applied):** *“`w_0(π)=1` … `w(π)=e_0e_1⋯e_m=E` — **BENIGN.** This uses the chosen uniformizer `π`, not the integer prime `p`, and nowhere assumes `v(p)<∞`. **In `F_q[[t]]`, take `π=t`.**”*

**DERIVATION:** Displayed in full above. Three steps: multiplicativity ⇒ domain; the induction `w_{j+1}(π) = e_j w_j(π)` from the constant's development ⇒ `w(π) = E`; graded localization at a homogeneous nonzerodivisor.

**RESOLUTION TRACE:** statement lines 703–721; consumed at `.03` (as the source of `ϑ = in(π) ∈ B_E`), `.12`, `.15`, `.20`.

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:S6a` — count **8**. `GRW2_TIE_DESIGN_2026-08-08.md` — **file EXISTS**.

**TEETH:** **JC1** — “JC-PER + `w(π) = E`: `φ_{γ+kE} == π^k φ_γ` byte-for-byte at `k = 1,2,3`; s-tuple E-periodic; `u_1 ↦ u_1+k`” — **2,594 samples, 0 violations, `w(π) = E` on all 29 rows**.

---

### EFF.GRTJC.s2of3.03  [lemma]  LEMMA JC-GAUGE — TC-2 is legitimate, and ℤ collapses to ℤ/E

**CANONICAL STATEMENT:** verbatim, lines 725–752 (statement, proof and application).
**FORM:** bold-headed lemma with a fixed-width three-part conclusion.

> “*Statement.* Let B = ⊕_{n∈ℤ}B_n be any commutative ℤ-graded ring containing a
> **unit** ϑ ∈ B_E, E ≥ 1. Put A := B/(ϑ−1)B. Then
>
>     (i)  (ϑ−1)B = ⊕_{ν∈ℤ/E} (ϑ−1)B^{(ν)},  B^{(ν)} := ⊕_{n≡ν (E)} B_n,
>     (ii) A = ⊕_{ν∈ℤ/E} A_ν  is ℤ/E-GRADED, A_ν := image of B^{(ν)},
>          A_νA_{ν′} ⊆ A_{ν+ν′},
>     (iii) for each ν and EACH n ≡ ν (mod E) the composite B_n → A_ν is an
>           isomorphism of additive groups; in particular A_0 ≅ B_0 as rings.”

**With its proof (lines 734–743) and application (745–752), the application quoted:**

> “*Application.* Take B from JC-DOM and ϑ := in(π) ∈ B_E (a unit after TC-1, of
> degree E by JC-DOM — the harness check w(π) = E the design note wanted). TC-2 is
> therefore a legitimate ring-level operation at **every** stage, its output is
> ℤ/E-graded, and the design note's C13 objection ("p ↦ 1 is not a graded
> homomorphism from TC-1's output alone") is answered in the only way it can be:
> the gauge is not a graded map but a **quotient by a non-homogeneous principal
> ideal whose ideal splits along the E residue classes**, which is exactly why the
> grading survives modulo E and not on the nose.”

**★ THE LEMMA IS STATED FOR AN ARBITRARY GRADED RING — a deliberate abstraction, and it is what makes the answer to C13 clean.** The application then instantiates it. **The C13 objection is answered structurally, not by construction: “the gauge is not a graded map but a quotient by a non-homogeneous principal ideal whose ideal splits along the E residue classes.”**

**CONDITIONALITY:** Unconditional as an abstract lemma (`B` any commutative ℤ-graded ring with a unit `ϑ ∈ B_E`, `E ≥ 1`). **Its instantiation needs TC-1 first** — `in(π)` is a unit only after localization — and the note stresses the order: “TC-1 strictly before TC-2” (PE1 verified it).

**GENERALITY NOTE (Q7, recorded not applied):** *“‘TC-1 localize `gr(w)` at `in(π)`; TC-2 gauge `π ↦ 1`’ — **BENIGN.** … not Witt-vector or unramified-ℤ_p structure.”* And: *“‘the grading collapses ℤ → ℤ/E’ — **BENIGN.** … no division by `E` in the coefficient field and no extraction of an `E`-th root.”*

**DERIVATION:** Displayed in full (lines 734–743). (i) For homogeneous `b ∈ B_n`, `(ϑ−1)b` has both terms in `B^{(n mod E)}`. (iii) is the substantive step: `σ(Σ_k b_{n+kE}) := Σ_k ϑ^{-k}b_{n+kE}` is additive, surjective, kills `(ϑ−1)B^{(ν)}`, and conversely `x ≡ σ(x)` modulo `(ϑ−1)B^{(ν)}`, so `ker σ = (ϑ−1)B^{(ν)}`.

**RESOLUTION TRACE:** statement lines 725–752; the interface correction 385–386 (r1/G1, shard 1 `.33`); consumed at `.01`(ii), `.20` (the ideal transport), `.23`, `.27`.

**TEETH:** JC1 (the periodicity half); **PE7 re-proved JC-GAUGE via coarsened grading + a fresh out-of-roster `p = 7` leg** (the acceptance record, shard 3) — **a method-diverse re-derivation.**

---

### EFF.GRTJC.s2of3.04  [lemma]  LEMMA JC-PER — the anchor system is E-periodic on the nose

**CANONICAL STATEMENT:** verbatim, lines 756–772.
**FORM:** bold-headed lemma with `*Statement.*` / `*Proof.*` / `*Machine:*`.

> “*Statement.* For every γ ∈ W and k ≥ 0: the split satisfies
> s_{j+1}(γ+kE) = s_{j+1}(γ) for all j and u_1(γ+kE) = u_1(γ) + k; hence
> **φ_{γ+kE} = π^k·φ_γ as polynomials (byte-for-byte)**, and after TC-2
> [φ_{γ+E}] = [φ_γ]. So u_γ ↦ [φ_γ] is well defined on ℤ/E, and (choosing window
> representatives) independent of the representative.”

**★ “BYTE-FOR-BYTE” IS NOT RHETORICAL — it is what the machine keys.** *Machine* (lines 770–772): “instrument **P0-OB2 = 0/285 byte-for-byte** on every anchor of every row (OB-2/COR-4 exact); this note's own battery re-tests it at `k = 1,2,3` (family JC1).”

**CONDITIONALITY:** Requires `γ ∈ W` (the window). **This is OB-2 and it is the cleanest clause in the note — PROVED at general `m`, byte-exact, double-measured.**

**DERIVATION:** Displayed (lines 762–768): induction down the split. At the top `e_m | E` gives `s_{NR}(γ+E) = s_{NR}(γ)` and `u_{NR}(γ+E) = u_{NR}(γ) + E/e_m`; the same step at each level leaves `s_j` unchanged and increases `β_{j−1}`; at the bottom `u_1(γ+E) = u_1(γ) + 1`. The anchor formula then differs by exactly one factor `π`.

**GENERALITY NOTE (Q7, recorded not applied):** *“‘`s_NR(γ+E)=s_NR(γ)`’ and ‘`u_1(γ+E)=u_1(γ)+1`’ — **BENIGN — integer congruence arithmetic.**”*

**RESOLUTION TRACE:** statement lines 756–772; consumed at `.01`(iii), `.03` (the application), `.13`, `.18` (the virtual-anchor transport), `.23`, `.38`(iv).

**TEETH:** **instrument P0-OB2 0/285 byte-for-byte** + **JC1 (2,594 samples)** + tooth **MJ2** (“mutated periodicity `φ_{γ+E} == π²φ_γ`”, **285 firings — fired on every row**). Disposition: **executable regression, double-instrumented, with a planted mutant.**

---

### EFF.GRTJC.s2of3.05  [lemma]  LEMMA JC-FIB — which ℤ/E-indexing survives

**CANONICAL STATEMENT:** verbatim, lines 776–789.
**FORM:** bold-headed lemma.

> “*Statement.* γ ↦ (s_1(γ),…,s_{NR}(γ)) ∈ ∏_{j=0}^{m}ℤ/e_j is E-periodic and
> induces a **bijection ℤ/E ≅ ∏_j ℤ/e_j**. Hence the ℤ/E-grading of JC-GAUGE is
> indexed equivalently by γ mod E and by the abscissa-coset tuple — the fibred
> ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19).”

**★ ANOTHER DESIGN-NOTE OBLIGATION DISCHARGED BY IDENTIFICATION** — “the fibred ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19)”.

**CONDITIONALITY:** Unconditional given the split's definition. **The bijection is what lets W-7's Ψ be indexed by `ℤ/E` and simultaneously by abscissa cosets** — the two indexings the design note asked to be reconciled.

**DERIVATION:** Displayed (lines 781–786). Periodicity is JC-PER. Both sides have `E` elements, so injectivity on `[0,E)` suffices: equal `s_{NR}` forces `γ ≡ γ′ (mod e_m)` (as `s_{NR} = ℓ_mγ mod e_m` with `ℓ_m` invertible); descending, equality of `s_{NR−1}` forces `(γ−γ′)/e_m ≡ 0 (mod e_{m−1})`, and so on down to `E | γ−γ′`.

**RESOLUTION TRACE:** statement lines 776–789; consumed at `.01`(ii), `.07`, `.17`, `.27`.

**TEETH:** **JC2** (“the s-tuple map is injective on `E` consecutive `γ` + periodicity”, **570 samples, 0 violations, every row**); the instrument's **P4-DEG (0/29)** is “its weaker shadow”.

---

### EFF.GRTJC.s2of3.06  [lemma]  LEMMA JC-ANCHMON — the anchor is a single Φ_m-digit

**CANONICAL STATEMENT:** verbatim, lines 793–805.
**FORM:** bold-headed lemma with a four-part conclusion.

> “*Statement.* For γ ∈ W: (a) Σ_{j<m}s_{j+1}·deg Φ_j < deg Φ_m; hence (b) the
> Φ_m-development of φ_γ has exactly one nonzero digit, at abscissa s_{NR}(γ);
> hence (c) 𝑅_γ(φ_γ) is a nonzero **constant** in K_m (slot set {0}) and
> (d) deg φ_γ < (s_{NR}(γ)+1)·deg Φ_m.”

**★ CLAUSE (c) IS THE DEFINITION OF `a_λ`, THE ANCHOR CONSTANT — the object the whole ρ-normalization is built on** (`ρ_λ := 𝑅_λ/a_λ`, `.13`). **Clause (d) is the degree bound JC-SPAN's upper end uses**, and it is exactly what makes JC-SPAN `e_m`-sensitive (JC-BOX-4's corner).

**CONDITIONALITY:** `γ ∈ W`. Unconditional otherwise — **pure digit arithmetic, and PE1 re-derived it independently and CLEARED it.**

**DERIVATION:** Displayed (lines 798–805). (a) `s_{j+1} ≤ e_j − 1` and `deg Φ_{j+1} = e_jg_j deg Φ_j ≥ e_j deg Φ_j`, so `s_{j+1}degΦ_j ≤ degΦ_{j+1} − degΦ_j`; summing telescopes to `≤ deg Φ_m − deg Φ_0 < deg Φ_m`. (b) `φ_γ = (π^{u_1}∏_{j<m}Φ_j^{s_{j+1}})·Φ_m^{s_{NR}}` with the parenthesis of degree `< deg Φ_m` by (a) — **that IS the `Φ_m`-development**. (c) the single digit sits at the line's base abscissa, so slot 0; nonzero and on the line.

**RESOLUTION TRACE:** statement lines 793–805; consumed at `.08` (both ends), `.13`(c), `.16` (the `a_γ` constants), `.19`.

**TEETH:** **JC5** (“the telescoping degree bound, the single-digit development, slot set {0}, `a_λ ≠ 0`”, **855 samples, 0 violations**).

---

### EFF.GRTJC.s2of3.07  [lemma]  LEMMA JC-SCAL — the scalar image (and the Annex #8 quantifier repair)

**CANONICAL STATEMENT:** verbatim, lines 809–825.
**FORM:** bold-headed lemma with a three-part conclusion.

> “*Statement.* For N ≡ 0 (mod E), N ≥ wΦ_{NR}, and c = Σ_{i<g_m}c_iz̄^i ∈ K
> (c_i ∈ K_m, the canonical representative): (a) s_{NR}(N) = s_{NR}(0) = 0 and
> the on-line slot set of Λ_N(c) is contained in {0,…,g_m−1}, with slot i digit
> the ε-corrected c_i; so **𝑅_N(Λ_N(c)) is the canonical degree-<g_m
> representative of c, up to one line-wise unit**; (b) 𝑅_N(X_N) is a nonzero
> CONSTANT (slot set {0}); (c) consequently the "scalar image" at line N is
> exactly 𝑅_N(X_N)·{K_m-polynomials of degree < g_m}.”

**★ CONDITIONALITY — SUPERSEDED IN QUANTIFIER BY ANNEX #8** (shard 3, L3014–3037). Two changes, both narrowing:

> “Accordingly **JC-SCAL is re-displayed with `c ∈ K^*`**. Its scalar-image conclusion is
> `𝑅_N(X_N)·{ p ∈ K_m[y] : p ≠ 0, deg p < g_m }`.”

and the ground: “**No value `Λ_N(0)` is supplied by REALIZE.** The zero polynomial represents the zero class and has zero read, but it does not have weight `N`.”

**SUPERSESSION KIND: `partial-withdrawal`** — clause (c)'s image set is re-displayed with “nonzero”; clauses (a)/(b) survive with the narrowed quantifier. **r5/m-1 (shard 1 `.15`) had already patched the §2.8 display of this same set — Annex #8 is the general repair.**

**Annex #8's consumer sweep (quoted):** “**JC-LOAD already quantifies `c ∈ K^*` and survives.** W-8's `c_{m+1}` is a unit by JC-CARRY-m, so its lift remains defined. `X_N = Λ_N(1)` is unchanged. **JC-SCAL, JC-BSURJ, COORD-B, and all downstream carrier-dimension arguments survive.** Historical JC4/R1-SURJ machine rows retain their numerical counts but **evidence only defined nonzero lifts and nonzero polynomial targets**.”

**DERIVATION:** Displayed (lines 817–822). `s_{NR}(N) = 0` because `E | N` and `s_{NR}` is E-periodic with `s_{NR}(0) = 0`. REALIZE's construction expands `τ = (c_0,…,c_{g_m−1})` as `Σ_i child_i·Φ_m^{k_i}` with `k_i = s_{NR}(N) + i·e_m`, `deg child_i < deg Φ_m` — so the abscissas are exactly `{i·e_m : c_i ≠ 0}` and the packed read is `c` by R3. For `c = 1` only `i = 0` survives.

**RESOLUTION TRACE:** statement lines 809–825; **correction site 3014–3037 (Annex #8, shard 3)**; the early symptom 256–259 (shard 1 `.15`); consumed at `.09` (the RHS of RAW), `.33` (W-8's normalization).

**TEETH:** **JC4** (443 samples: slot set `== supp(c) ⊆ {0..g_m−1}`, slot-`i` digit `== c_i`, **`𝑅_N(X_N) == 1` exactly**, every row and every `c ∈ K`); instrument shadows **P0-LIFT (0/138)**, **P0-SCAL (0/293)**; tooth **MJ3** (“mutated scalar image ‘slots ⊆ {0}’”, 4 firings — **fired on every `g_m ≥ 2` row**; “2 of the 6 opportunities are the `c`'s whose slot 1 is genuinely empty”). **Annex #8 narrows what these evidence, not their counts.**

---

### EFF.GRTJC.s2of3.08  [lemma]  ★ THEOREM JC-SPAN — the slot span is the singleton {δ}

**CANONICAL STATEMENT:** verbatim, lines 829–857.
**FORM:** bold-headed theorem with `*Statement.*` / `*Proof.*` / `*Comment.*` / `*Machine:*`.

> “*Statement.* Let γ,γ′ ∈ W with γ+γ′ ∈ W, and let δ = δ(γ,γ′) ∈ {0,1} be the top
> carry. Assume **e_m ≥ 2**. Then the on-line slot set of φ_γφ_{γ′} at its own
> weight γ+γ′ is exactly **{δ}**, i.e.
>
>     𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^{δ}  for some u ∈ K_m^*.
>
> If e_m = 1 (so δ = 0), the same argument gives slot set ⊆ {0,1} with 0 attained,
> i.e. deg 𝑅 ≤ 1.”

**★ THE COMMENT IS THE STRUCTURAL PAYLOAD** (lines 849–854):

> “*Comment.* This is the composite-stage replacement for CARRY-1
> (φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ, last-read layer, IN-2): at a composite stage the
> identity acquires **exactly one extra K_m-unit u**, and the theorem proves that
> the extra factor is a unit of K_m — a scalar that TC-3 never touches — while the
> y-degree is exactly δ. **The outer/inner split of c_T is therefore structural,
> not a coordinate choice**: outer = the slot shift y^δ; inner = u ∈ K_m^*.”

**This is the sentence that refutes the brief's guess structurally**, complementing the instrument's numerical refutation (shard 1 `.03`): the inner factor is a unit of `K_m`, and `−z_{m+1} ∉ K_m` whenever `g_m ≥ 2`.

**CONDITIONALITY:** **`e_m ≥ 2` for the sharp form.** At `e_m = 1` only `deg 𝑅 ≤ 1`, which suffices when `g_m ≥ 2` but not at `e_m = 1 ∧ g_m = 1` — **JC-BOX-4's corner, MEASURED there (C4H) and CONDITIONALLY CLOSED at r1 on `(DMULT-w)` by a second, `e_m`-blind proof.** Consumes **`(IN-3)(e)` = Cor 2.7** at the lower end — **a CITE-SCOPE row, resolved COVERS-ALL-O by NS-9** (shard 1 `.43`).

**DERIVATION:** Displayed in full (lines 838–847). **Lower end:** by `(IN-3)(e)` the minimal on-line abscissa of `φ_γφ_{γ′}` is `s_{NR}(γ)+s_{NR}(γ′)`, and the line's base abscissa at `λ = γ+γ′` is `s_{NR}(λ) = s+s′ − δe_m`; so the minimal slot is `δ`, attained. **Upper end:** by JC-ANCHMON(d), `deg(φ_γφ_{γ′}) < (s+1)degΦ_m + (s′+1)degΦ_m`, so the largest abscissa is `≤ s+s′+1`; on-line abscissas are `≡ s+s′−δe_m (mod e_m)`, so slots satisfy `k ≤ δ + 1/e_m`, i.e. **`k ≤ δ` when `e_m ≥ 2`**.

**RESOLUTION TRACE:** statement lines 829–857; consumed at `.09`, `.18` (`A` is a monomial of degree `δ`), `.19`, `.24`, `.33`; the corner box 2004–2027 (shard 3).

XREF: the `(IN-3)(e)` = **[FGMN] Cor 2.7** pin re-read at HEAD by this compiler: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` **line 525** = “Corollary 2.7. For non-zero g, h ∈ K[x], we have Sλ (gh) = Sλ (g) + Sλ (h).” — **EXACT.**

**TEETH:** **JC3 — the note's OWN NEW sharp prediction**, sealed before the run: “the on-line slot set of `φ_γφ_{γ′}` at its own weight is EXACTLY `{δ}`”. **Verdict: 2,484 samples, 0 violations, slot set == {δ} on 609/609 pairs with `e_m ≥ 2`.** Plus **JC3-FLAT** (the `e_m = 1` corner: “census: **0 of 24 pairs have a slot > 0**” — the unproved sharp form measured true on C4H) and tooth **MJ5** (“slot set == {δ+1}”, **633 firings, fired on every pair**). Disposition: **a preregistered sharp prediction, hit exactly.**

---

### EFF.GRTJC.s2of3.09  [lemma]  ★ THEOREM JC-LOAD — TC-3 is load-bearing EXACTLY at δ ≥ g_m

**CANONICAL STATEMENT:** verbatim, lines 861–924 — the statement, the three consequences with their `[r1, G5]` scoping, the proof with its `[r3, G-1]` re-route and `[r4, G-3]`/`[r5, m-1]` corrections, and the honest fence.
**FORM:** bold-headed theorem.

> “*Statement.* Fix a pair (γ,γ′) as above with e_m ≥ 2, and consider the
> **pre-TC-3** (RAW) equation in gr(w) localized and gauged but NOT quotiented by
> ψ_m: does there exist c ∈ K^* with
>
>     𝑅(φ_γφ_{γ′}·X_N) = 𝑅(Λ_N(c)·φ_{γ+γ′})   at the line γ+γ′+N ?   (RAW)
>
> Then: **(RAW) is solvable ⟺ δ < g_m.** Equivalently (δ ∈ {0,1}): the pre-TC-3
> scalar exists on every pair except those with δ = 1 ∧ g_m = 1, where the
> ψ_m-relation — i.e. TC-3 — is unavoidable. Consequently:
>
>     (a) c_T's OUTER factor z̄^δ is the image under TC-3 (y ↦ z̄) of the graded
>         slot shift y^δ; it is NOT obtainable from TC-1/TC-2 alone;
>     (b) c_T's INNER factor ∏_j z_j^{D_j} lies in K_m^* and needs no quotient;
>     (c) the sealed set identity {no pre-TC-3 scalar} = {δ ≥ g_m} of the
>         instrument (0/29 set-mismatches, 134/669 pairs) is a THEOREM, not an
>         observation.
>         [r1, G5 — SCOPED to the theorem's own fence.]  JC-LOAD is stated with
>         e_m ≥ 2, so the THEOREM covers the 28 roster rows with e_m ≥ 2; on the
>         one top-flat row (C4H, e_m = 1 …) the identity is MEASURED, not proved, and is boxed at
>         JC-BOX-4.  So: theorem where proved (28 rows), measured where measured
>         (C4H).  The instrument's 0/29 set-mismatch count is unchanged — what is
>         corrected is the r0 wording, which implied the theorem covered all 29.”

**★ THE TITLE CLAIM — “theorem, not observation” — is the note's headline, and clause (c) states exactly what was upgraded**: the instrument's sealed SET IDENTITY `{no pre-TC-3 scalar} = {δ ≥ g_m}` (0/29 set-mismatches over 134/669 pairs) is proved, on the 28 rows the theorem covers.

**★ CONDITIONALITY — Annex #5 supersedes clause (a)** (shard 3, L2890–2911), and W-6(iv) with it (`.01`). **The corrected reading:** the outer factor is **always** `q(y^δ) = z̄^δ`; it is **unavailable as a pre-TC-3 scalar exactly when `δ ≥ g_m`**. **Annex #5's own note: “JC-LOAD itself proves the counterexample supplied by the finding”** — i.e. the note's own iff already contained the correction, and only the gloss over-reached. **“JC-LOAD's iff and its sealed set identity survive unchanged.”**

**Two further in-range corrections, both quoted at the proof:**
- **`[r3, G-1]`**: the proof's transport step had cited the PE1-refuted `(IN-3)(c)`; **re-routed to §4.2 = `(MULT-B)|gr` at `δ = 0`, riding `(DMULT-w)`** — “the step actually used”.
- **`[r4, G-3]` + `[r5, m-1]`**: the multiplier is the anchor coboundary `b_× := a_{λ+N}/(a_λa_N)`, **not the exact-tier `𝑅(X_N)`**; and the RHS set is the **nonzero** polynomials of degree `< g_m`. **“the iff below is tier-blind”** — the same constant appears on both sides and cancels exactly (PE4 §A1 verified).

**DERIVATION:** Displayed (lines 885–916). Multiplying by `X_N` transports lines additively and multiplies the digit polynomial by a `K_m^*`-constant `b_×` **without changing its y-degree** (offset transport, §4.2; `s_{NR}(N) = 0` so `δ(γ+γ′,N) = 0`). By JC-SPAN the LHS has digit polynomial `b_×·u·y^δ` of exact y-degree `δ`; by JC-SCAL(a)(c) the RHS ranges over `b_×·{nonzero polynomials of degree < g_m}`. **Since `K_m[y]` is a polynomial ring, `u y^δ` (`u ≠ 0`) equals a polynomial of degree `< g_m` iff `δ < g_m`.** For (a): after TC-3 the class of `y^δ` is `z̄^δ`, and `y^δ` is not in the `K_m`-span of `{y^i}_{i<g_m}` when `δ ≥ g_m`.

**★ THE HONEST FENCE, verbatim (lines 918–924):**

> “*Honest fence.* The proof of the ⟸ direction rides the offset-transport step
> (§4.2), which rides ~~(IN-3)(c)~~ **(MULT-B)|gr and with it (DMULT-w)
> [r3, G-1 …]**; the ⟹ direction (the obstruction) rides only
> JC-SPAN + JC-SCAL. The instrument's k-distribution **{0 : 669}** says the
> π-clearing ladder is never needed on its roster: the canonical division by
> Φ_{m+1} alone discharges TC-3 there.”

**The two directions have different footprints, and the note separates them** — the obstruction direction (the one that matters for the fence) rides only in-note lemmas.

**RESOLUTION TRACE:** statement lines 861–924; §4.2 1747–1760 (`.35`); **correction sites 2890–2911 (Annex #5)**, 314–319 (r3/G-1, shard 1 `.22`), 289–296 (r4/G-3, shard 1 `.19`), 256–259 (r5/m-1, shard 1 `.15`).

**TEETH:** **MJ1** — the tooth “TC-3 is never load-bearing”: **333 tested, 103 firings, and ALL 103 lie in the `δ ≥ g_m` load set; 0 anomalies in either direction — JC-LOAD's dichotomy machine-confirmed BOTH WAYS.** Plus the instrument's own **0/29 set-mismatches over 134/669 pairs.** Disposition: **planted mutant confirming an iff in both directions** — the strongest tooth design in this note.

---

### EFF.GRTJC.s2of3.10  [lemma]  ★ COROLLARY JC-PSIKER — TC-3 is not a relabeling (and the r1/F2 re-quantification)

**CANONICAL STATEMENT:** verbatim, lines 928–990 — the witness, the struck over-quantified sentence, the `[r1, F2]` three-clause replacement, the machine record and the proof.
**FORM:** bold-headed corollary with a fixed-width three-clause conclusion.

> “*Statement.* At every stage the level-NR read is **non-injective on a graded
> piece**: with λ := wΦ_{NR} = e_mg_mγ_{m+1},
>
>     𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0   in K_m[y],  but  read(λ, Φ_{m+1}) = ψ_m(z̄) = 0,
>
> so in(Φ_{m+1}) ≠ 0 in gr_λ lies in the kernel of the read; and (when λ ∈ W, so
> that the anchor φ_λ exists — otherwise use the π-translate) Φ_{m+1} + φ_λ and
> φ_λ are two elements of gr_λ with equal reads and different classes. ~~Hence
> TC-3 has a nonzero kernel on every graded piece (namely ψ_m·Δ under the anchor
> coordinate) and **cannot be a relabeling of scalars.**~~”

**The `[r1, F2]` replacement, verbatim (lines 939–961):**

> “**[r1, F2 — CRITICAL (PE1): that closing sentence is OVER-QUANTIFIED, and is
> replaced by the exact range. The witness above is UNCHANGED and correct.]**
> PE1's finding, in one line: `𝔦 := in(Φ_{m+1})·gr(w)` is homogeneous with a
> single generator of degree wΦ_NR, so its degree-λ part is
> `𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`, and weights are ≥ 0 on O[x] — hence the
> kernel is **ZERO whenever λ < wΦ_NR**, which is the case at the window base G0
> on **29/29 roster rows** … The corrected statement, in three clauses:
>
>     (i)   [WITNESS — unchanged, PROVED] at λ = wΦ_NR the display above holds:
>           𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0 while read(λ,Φ_{m+1}) = ψ_m(z̄) = 0.
>     (ii)  [EXACT RANGE on gr] for λ ∈ W, 𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR},
>           which is ZERO for every λ < wΦ_NR and NONZERO for every
>           λ ∈ wΦ_NR + W (the anchor φ_{λ−wΦ_NR} supplies the element, and
>           gr(w) is a domain).  Under the note's standing convention that
>           gr_γ = 0 off the window (JC-BOX-7) the range is exactly
>           W ∩ (wΦ_NR + W).
>     (iii) [THE FORM §2.10 CONSUMES — PROVED] after TC-1 the kernel is nonzero on
>           EVERY graded piece: 𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR} ≅ ψ_m(y)·Δ
>           ≠ 0 for every n ∈ ℤ, because in(π) is a unit in B and hence
>           B_j ≅ B_{j+E} for all j — no piece of B is zero.  So TC-3 **cannot be
>           a relabeling of scalars** on the object TC-3 is actually applied to.”

**SUPERSESSION KIND:** `counter re-reading` — a universal generalization refuted and replaced by an exact range.

**★ WHY THE CRITICAL COST NOTHING, and the note verifies it:** “Nothing downstream used the refuted universal form on gr: §2.10 [r1, F1] now states and consumes (iii). **W-6(v)'s own wording (‘the level-NR read is non-injective on a graded piece, with the classifier's own next key Φ_{m+1} as the kernel witness’) was already correct as written and stands unamended.**”

**CONDITIONALITY:** Clause (ii)'s range uses the standing convention `gr_γ = 0` off the window (JC-BOX-7). **Clause (iii) is the form the coordinate calculus consumes and it is TRUE on `B` for a structural reason — `in(π)` is a unit, so no piece of `B` is zero.**

**DERIVATION:** Displayed (lines 975–981). `Φ_{m+1} = Φ_m^{e_mg_m} + Σ_{k<g_m}C_kΦ_m^{e_mk}` with `w(C_kΦ_m^{e_mk}) = λ` for every `k` with `ψ_{m,k} ≠ 0` (REALIZE's construction of `C_k` at weight `(g_m−k)γ_{m+1}`) — **“that is the defining property of the key polynomial: all its terms sit on the λ-line, its slot digits are the coefficients of `ψ_m`, and `w(Φ_{m+1}) = λ` exactly.”** So `𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0` while its evaluation at `z̄` is `ψ_m(z̄) = 0`.

**★ INSTRUMENT CORROBORATION FROM THE OTHER SIDE (lines 983–987):** “the build-phase disclosure that the naive class identity `[π·Λ_N(c)] = [Λ_{N+E}(c)]` is **FALSE** — two weight-`(N+E)` lifts with the same read need not be the same class — is the same phenomenon measured from the other side, and is why the instrument's offset clause (P2-OFF, 0/116) is stated on the CONSTANTS.”

**RESOLUTION TRACE:** statement lines 928–990; the disposition 378–384 (r1/F2, shard 1 `.32`); the consumed form 1354–1396 (`.20`); JC-BOX-7 2049–2056 (shard 3).

**TEETH:** **JC6** (116 samples: `w(Φ_{m+1}) == wΦ_NR`, `𝑅(Φ_{m+1}) == ψ_m` coefficientwise, `read == 0`, and the equal-read/different-class pair) + tooth **MJ4** (“the read is injective on `gr_λ`”, **29 firings — fired on every row**) + **R1-PSIK-LO** (197 window lines below `wΦ_NR`, no class certified dead — **with the certifier's one-sidedness disclosed**, JC-BOX-8(ii)) + **R1-PSIK-HI** (197 residue classes with a certified nonzero witness) + tooth **T1** (the refuted universal claim, **29/29 firings**).

---

### EFF.GRTJC.s2of3.11  [supplier-finding]  ★★ §2.10 — the struck `(COORD)` and WHY it is false

**CANONICAL STATEMENT:** verbatim, lines 992–1035 — the section head, the struck r0 display, the slot-bound refutation, and the “why the literature is NOT at fault” paragraph.
**FORM:** display (an H3 head) + a struck blockquote + two bold-headed paragraphs.

> “## 2.10 [r1, F1] What TC-3 IS in this note, and WHERE the coordinate calculus lives (the post-TC-1 pieces B_n)
>
> **[r1, F1 — CRITICAL (PE1). The r0 text stated the coordinate calculus on
> gr_λ(w), where it is FALSE; it is restated here on this note's own B_n, where it
> is proved. The struck r0 wording, verbatim:]**
>
> > ~~Two facts fix the coordinate calculus used from here on. Both are named
> > inputs, not new claims.~~
> >
> > ~~**(COORD)** For λ ∈ W the digit map 𝑅_λ : gr_λ(w) → Δ := K_m[y] is a
> > K_m-linear **isomorphism**, carrying in(φ_λ) to a nonzero constant
> > a_λ ∈ K_m^* (JC-ANCHMON(c)). Injectivity is definitional (§1: 𝑅_λ(f) = 0 ⟺
> > w(f) > λ); surjectivity/rank-one is (IN-3)(c) — FGMN Thm 4.2's freeness of
> > gr_λ over Δ on the anchor basis.~~
>
> **Why the r0 statement is false (the slot bound).** §1's ambient ring is O[x]:
> w_0 is the coefficientwise π-valuation on INTEGRAL polynomials, and the window
> W = {γ : u_1(γ) ≥ 0} together with the anchors φ_γ = π^{u_1}∏Φ_j^{s_{j+1}} exist
> precisely to keep the π-exponent ≥ 0. Hence every Φ_m-digit A_a of an f in the
> ring has w_m(A_a) ≥ 0, so an on-line abscissa at level λ satisfies
> e_m·w_m(A_a) + a·γ_{m+1} = λ with w_m(A_a) ≥ 0, i.e. a·γ_{m+1} ≤ λ. Writing
>
>     maxslot(λ) := ⌊(⌊λ/γ_{m+1}⌋ − s_NR(λ))/e_m⌋,
>
> the on-line slot set at λ is contained in {0,…,maxslot(λ)}: **gr_λ is a
> FINITE-dimensional K_m-space**, 𝑅_λ is NOT onto K_m[y], and
> gr_λ/(𝔦 ∩ gr_λ) is not a 1-dimensional K-space. At this note's own window base
> maxslot(G0) = **0 on 29/29 roster rows** (r1 family R1-BND; PE1 §CRITICAL 1
> measured the same, and sampled 3,072 integral f with w(f) = 4 on row C2I —
> m = 1, E = 4, g_m = 2, e_m = 2, γ_{m+1} = 5, wΦ_NR = 20, G0 = 4 — finding slot
> set {0} throughout and 𝔦 ∩ gr_4 = 0, so gr_4 ≅ K_m while [K:K_m] = g_m = 2).
>
> **Why the literature is NOT at fault, and where the repair lives.** FGMN's
> Δ ≅ K_m[y] is the degree-0 part of the graded algebra of a MacLane valuation on
> **K[x]** — π INVERTED — and that object is exactly what JC-DOM (§2.1) builds one
> page earlier: `B := gr(w)[in(π)^{-1}]`, `B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE}`. So
> the coordinate calculus — (COORD-B)/(MULT-B) below — and TC-3 belong strictly
> AFTER TC-1, on B **[r2, G-4: this sentence formerly named the struck
> (COORD)/(MULT) here]**. Four lemmas do it. Note
> that this makes the note's literature footprint SMALLER, not larger: the
> surjectivity half becomes a theorem of this note (JC-BSURJ, from REALIZE-(m)),
> and the only cited input left in the coordinate calculus is the multiplicativity
> (DMULT) **[r2, G-1: in its citable tier (DMULT-w); the exact tier (DMULT-s) is
> MEASURED, not cited — see the split below]**.”

**SUPERSESSION KIND:** `replacement` — a false display struck and the calculus re-based.

**★ THE THREE-PART SHAPE A CHAPTER CUT MUST CARRY, and it is unusually clean:**
1. **What is false and why:** the ambient ring is `O[x]`, so `w_0 ≥ 0`, so `a·γ_{m+1} ≤ λ` and `gr_λ` is FINITE-dimensional with the explicit bound `maxslot(λ)`. **`𝑅_λ` is NOT onto `K_m[y]`.**
2. **Why the literature is not at fault:** FGMN's `Δ ≅ K_m[y]` is about `K[x]` with `π` INVERTED — **which is exactly the object JC-DOM had already built one page earlier.** The defect was transport, not truth.
3. **The repair SHRINKS the footprint:** JC-BSURJ PROVES the surjectivity half that r0 cited, leaving `(DMULT)` as the only cited input — and even that becomes DERIVED at Annex #6.

**CONDITIONALITY:** The refutation is measured, not merely argued: **`maxslot(G0) = 0` on 29/29 roster rows**, with PE1's independent sampling on row C2I (3,072 integral `f` with `w(f) = 4`; slot set `{0}` throughout; `𝔦 ∩ gr_4 = 0`; so `gr_4 ≅ K_m` while `[K:K_m] = g_m = 2`).

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 992–1035; the four repair lemmas 1037–1172 (`.12`–`.14`); the disposition 359–377 (r1/F1, shard 1 `.31`); the object 614–619 (shard 1 `.48`).

**TEETH:** **R1-BND** — “the slot bound: `maxslot(G0) == 0`”, **29 samples, 0 violations, 0 on 29/29 rows**, with the ladder census `maxslot(G0+kE)`, `k = 0..3`, showing the growth that makes `B_n ⊋ gr_n` (e.g. C2A `[0,0,1,1]`, C2D `[0,1,1,1]`, I4C `[0,0,0,0]` — “slower but unbounded”). Plus tooth **T2** (“no k-shift needed”, **29/29 firings**). **A refutation converted into a permanent scored regression.**

---

### EFF.GRTJC.s2of3.12  [lemma]  ★ LEMMA JC-LOC — B *is* the object FGMN's theorems speak about

**CANONICAL STATEMENT:** verbatim, lines 1037–1104 — the lemma, its proof with the `[r2, G-6]` additivity supplement, and the three-step `[r2, G-6]` identification with its honest residue.
**FORM:** bold-headed lemma + a fixed-width three-step derivation.

> “**LEMMA JC-LOC [r1] (B *is* the object FGMN's theorems speak about).** Write
> gr^O(w) for §1's graded ring (built on O[x]) and gr^K(w) for the same
> construction on K[x] = O[x][π^{-1}], with w extended by w(π^{-k}g) := w(g) − kE.
> Then the degreewise map
>
>     B = gr^O(w)[in(π)^{-1}] → gr^K(w),   in(π)^{-k}·in(g) ↦ in(π^{-k}g),
>
> is an isomorphism of ℤ-graded rings. In particular B_n ≅ gr^K_n(w) for every
> n ∈ ℤ, and B_0 ≅ the degree-0 subring of gr^K(w).”

**The three-step identification, verbatim (lines 1071–1091):**

>     (G6-1) THE EXTENSION IS FORCED.  Every f ∈ K[x] is π^{-k}g with g ∈ O[x],
>            and any valuation w^K on K[x] restricting to w with w^K(π) = E
>            (JC-DOM) must satisfy w^K(π^{-k}g) = w(g) − kE.  Well-defined: if
>            π^{-k}g = π^{-k′}g′ (k′ ≥ k) then g′ = π^{k′−k}g, and w(πf) =
>            w(π) + w(f) ((IN-3)(a)) gives w(g′) − k′E = w(g) − kE.  So there is
>            exactly ONE candidate, the displayed one.
>     (G6-2) §1's MIN-FORMULA COMPUTES IT ON ALL OF K[x] … So gr^K(w) is the graded ring of the MacLane
>            min-formula valuation on K[x] — the object of FGMN's graded package
>            — not of an ad-hoc extension.
>     (G6-3) IT IS A VALUATION.  Multiplicative: … Ultrametric: …

**★ THE HONEST RESIDUE, verbatim (lines 1092–1099) — and it is the sentence that keeps the note's conditionality straight:**

> “*Honest residue of this derivation (unchanged input, not a new one).* Steps
> G6-1..3 identify the extension with **the min-formula valuation on K[x] in the
> harness normalization**. The remaining tie — that §1's recursion (the harness
> w = w_{m+1}, sheared frame) is the literature's inductive valuation v_{m+1},
> and 𝑅 its residual-polynomial operator up to the line-wise unit — is exactly
> **(IN-3)'s W-1 transport clause, already priced in §0's stack** (and the
> subject of the open dictionary TR-3′-GEN quoted at [r2, G-1] below). G-6 adds
> no new conditionality; it removes the "same construction" hand-wave.”

**SUPERSESSION KIND:** `inventory completion` (r2/G-6 supplies a derivation for a phrase that had been asserted) — **explicitly NOT a new conditionality.**

**CONDITIONALITY:** **The remaining tie is W-1 (J-A) at ATTEMPT grade**, and the note says so rather than absorbing it. **TR-3′-GEN is OPEN** — the same fact that forces the `(DMULT-w)`/`(DMULT-s)` split (`.16`).

**DERIVATION:** The isomorphism's four properties are displayed (well-defined, graded+multiplicative, surjective in degree `n`, injective), **plus the `[r2, G-6]` additivity supplement** — “previously unchecked (needed because homogeneous elements are `in(f)` or 0, and sums can drop degree)”, resolved by bringing two degree-`n` elements to a common denominator and checking the same dichotomy on both sides.

**RESOLUTION TRACE:** statement lines 1037–1104; the disposition 473–478 (r2/G-6, shard 1 `.38`); consumed at `.15`, `.16`, `.20`, `.27`; the box 1960–1992 (JC-BOX-3, shard 3).

XREF: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` — **file EXISTS**; the standing setting at **line 137** re-read EXACT (shard 1 `.43`).

**TEETH:** **PE2 re-derived JC-LOC hostilely and independently and found no false statement.** No battery keys a ring isomorphism; disposition **AUDIT — in-house hostile pass** plus the indirect evidence of every family that computes in `B`.

---

### EFF.GRTJC.s2of3.13  [lemma]  LEMMA JC-PIINV — π-equivariance, and why ρ is the right coordinate

**CANONICAL STATEMENT:** verbatim, lines 1106–1143 (lemma, proof, machine).
**FORM:** bold-headed lemma with a three-part conclusion.

> “**LEMMA JC-PIINV [r1] (the digit polynomial is π-equivariant; the colimit
> coordinate is well defined).** For every λ ∈ ℤ and every f ∈ O[x] with
> w(f) ≥ λ:
>
>     (a) the on-line abscissas and slot indices at (λ+E, πf) are exactly those
>         at (λ, f);
>     (b) there is a constant c_π ∈ K_m^*, depending only on T, with
>         𝑅_{λ+E}(π f) = c_π·𝑅_λ(f);
>     (c) hence, with ρ_λ := 𝑅_λ/a_λ and a_λ := 𝑅_λ(φ_λ) ∈ K_m^* (JC-ANCHMON(c)),
>         ρ_{λ+E}(π f) = ρ_λ(f)  EXACTLY, for λ, λ+E ∈ W.”

**★ CLAUSE (c) IS WHY THE NORMALIZATION EXISTS, and the machine proves it is not cosmetic.** *Machine* (lines 1135–1143): the measured roster value set is **`c_π ∈ {1, z̄, z̄², z̄³, z̄⁴, z̄⁶, z̄⁸}` — 1 on 9 rows, `z̄` on 9, `z̄²` on 7, and `z̄³/z̄⁴/z̄⁶/z̄⁸` on the single rows C2G/C3H/C2H/I4C** — “a nontrivial constant, which is exactly why the ρ-normalization is the one that makes the colimit well defined”. **r1's own finding 3: “`c_π ≠ 1` on 20 of 29 rows. The colimit coordinate would NOT be well defined in the un-normalized `𝑅`.”**

**CONDITIONALITY:** **The r0 text quoted a 6-row SMOKE value set `{1, z̄, z̄²}` and labelled it “across the roster”** — corrected at r2/G-3 (shard 1 `.38`) to the as-of-r1 roster value set from the committed artifact. **A stale smoke figure presented as a roster figure.**

**DERIVATION:** Displayed (lines 1117–1133). (a) `deg(πA) = deg A`, so the development of `πf` is that of `f` multiplied coefficientwise; `w_m(πA) = w_m(A) + E/e_m` and `s_NR(λ+E) = s_NR(λ)`, so the on-line condition and the slot index are unchanged. (b) only the digit VALUES move, and two inductions down the levels show both corrections are independent of the slot and of `β`, so the whole digit polynomial is multiplied by one constant `c_π := δ_m·c^{(m)}`. (c) JC-PER gives `φ_{λ+E} = π·φ_λ` byte-for-byte, so `a_{λ+E} = c_π·a_λ` and `c_π` cancels.

**RESOLUTION TRACE:** statement lines 1106–1143; the disposition 461–463 (r2/G-3, shard 1 `.38`); consumed at `.15` (well-definedness of `ρ^B`), `.17` (the `κ = 1` pinning), `.18` ((G5-ii)).

**TEETH:** **R1-PER** — “`𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f)` with ONE `c_π` per row (independent of `f`, `λ`, slot, `k`), and `ρ_{λ+kE}(π^kf) == ρ_λ(f)` EXACTLY, `k = 1,2`” — **841 samples, 0 violations, every row**; plus tooth **T5** (“mutated JC-PIINV `ρ_{λ+E}(πf) == y·ρ_λ(f)`”, **406 firings**).

---

### EFF.GRTJC.s2of3.14  [lemma]  LEMMA JC-BSURJ — the colimit coordinate is ONTO Δ (proved, not cited)

**CANONICAL STATEMENT:** verbatim, lines 1145–1172 (lemma, proof, machine).
**FORM:** bold-headed lemma.

> “**LEMMA JC-BSURJ [r1] (the colimit coordinate is ONTO Δ — proved, not cited).**
> Fix n ∈ W and p = Σ_{j≤d}c_jy^j ∈ Δ = K_m[y]. For every k with
>
>     (n + kE) − (s_NR(n) + d·e_m)·γ_{m+1}  ≥  e_m·wΦ_m
>
> there is an INTEGRAL f with w(f) = n+kE and 𝑅_{n+kE}(f) = p on the nose; only
> finitely many k are excluded. Hence ρ^B_n := colim_k ρ_{n+kE} : B_n → Δ is
> SURJECTIVE, while ρ_n itself is not (its image has degree ≤ maxslot(n), which is
> 0 at every roster row's base).”

**★ “PROVED, NOT CITED” IS THE POINT — this is the half r0 had cited from FGMN and r1 proves in-note, which is why the repair SHRINKS the literature footprint.**

**CONDITIONALITY:** **SUPERSEDED IN QUANTIFIER BY ANNEX #8** (shard 3, L3034–3035): “The same zero convention repairs JC-BSURJ: for every **nonzero** `p = Σ_{j≤d}c_jy^j`, its displayed REALIZE construction produces an integral `f` with `w(f) = n+kE` and `𝑅_{n+kE}(f) = p`. **For `p = 0`, surjectivity uses the zero element of `B_n`; no exact finite-weight representative is asserted.** Thus `ρ_n^B : B_n → Δ` **remains surjective**.” **SUPERSESSION KIND: `partial-withdrawal`** — the construction's quantifier narrows, the surjectivity conclusion survives.

**DERIVATION:** Displayed (lines 1155–1166), and it is constructive. Put `λ := n+kE`, `s := s_NR(λ) = s_NR(n)`, `a_j := s + j·e_m`, `β_j := (λ − a_jγ_{m+1})/e_m`. **Each `β_j` is an INTEGER** (shown by a congruence: `γ_{m+1} ≡ h_m` and `λ ≡ s·h_m (mod e_m)`). The displayed inequality is `β_d ≥ wΦ_m`, and `β_j` decreases in `j`, so REALIZE-(m) supplies `A_j := realize(m, ε_m(β_j)^{-1}c_j, β_j)` with `deg A_j < deg Φ_m`. Put `f := Σ_j A_jΦ_m^{a_j}` — **since `deg A_j < deg Φ_m` this IS the `Φ_m`-development**, so `w(f) = λ` and the slot-`j` digit is `c_j`.

**RESOLUTION TRACE:** statement lines 1145–1172; **correction site 3034–3035 (Annex #8, shard 3)**; consumed at `.15`, `.16`, `.29`.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:REALIZE` — count **17** · `S4.1` — count **35**.

**TEETH:** **R1-SURJ** — “for targets `p` of y-degree 0,1,2 the REALIZE construction at the predicted `k` gives integral `f` with `w(f) == n+kE` and `𝑅(f) == p` ON THE NOSE; the minimal `k` is censused” — **841 samples, 0 violations**, with the census showing **degree 0 at `k = 0` on 28 rows (`k = 2` on C4H), degree 1 at `k = 2..16`, degree 2 at `k = 5..34` — “the k-shift is structural, not a convenience”**. Plus tooth **T2** (29/29).

---

### EFF.GRTJC.s2of3.15  [definition]  ★ (COORD-B) — the repaired coordinate calculus

**CANONICAL STATEMENT:** verbatim, lines 1174–1186.
**FORM:** bold-headed named display with a fixed-width two-part conclusion.

> “**(COORD-B) [r1 — REPLACES (COORD)].** Fix ν ∈ ℤ/E and n ∈ W with n ≡ ν (mod E);
> Δ := K_m[y].
>
>     (1) [PROVED at general m, in this note]  ρ^B_n : B_n → Δ,
>         in(π)^{-k}α ↦ ρ_{n+kE}(α), is a well-defined (JC-PIINV(c)), injective
>         (§1: 𝑅_λ(f) = 0 ⟺ w(f) > λ, compatibly along the system) and surjective
>         (JC-BSURJ) K_m-linear map, with ρ^B_n(in φ_n) = 1.  Moreover in(π) is a
>         unit in B of degree E, so B_j ≅ B_{j+E} for EVERY j ∈ ℤ: after TC-1 no
>         graded piece is zero and the window restriction disappears.
>     (2) [PROVED at general m from (1) + (DMULT-w) — the CITABLE tier suffices,
>         [r2, G-1]]  B_0 ≅ Δ as K_m-ALGEBRAS via
>         ρ^B_0, and B_n is FREE OF RANK ONE over B_0 ≅ Δ on in(φ_n), with ρ^B_n
>         the coordinate of that module structure.”

**★ THE TWO CLAUSES HAVE DIFFERENT FOOTPRINTS AND THE NOTE SEPARATES THEM SHARPLY:** **(1) is PROVED IN-NOTE with no literature input at all** (JC-PIINV + §1's injectivity + JC-BSURJ); **(2) needs `(DMULT-w)` — the citable tier — and nothing more.** **“after TC-1 no graded piece is zero and the window restriction disappears”** is what makes the all-of-`ℤ` quantifiers of `.18` and `.20` possible.

**SUPERSESSION KIND:** `replacement` — it REPLACES the struck `(COORD)`.

**CONDITIONALITY:** (2) rides `(DMULT-w)`, which **Annex #6 later DERIVES rather than cites** — so at HEAD (COORD-B)(2) rests on a derivation from the PDF-verified rank-one theorem, not on a quoted product law. **Annex #6's consumer sweep says exactly this: “(COORD-B)(2) survives at every `m`, now directly from JC-RANKMULT rather than from an unquoted product law.”**

**DERIVATION:** (1) from JC-PIINV(c) (well-defined), §1's injectivity, JC-BSURJ (surjective). (2) is `.17`.

**RESOLUTION TRACE:** statement lines 1174–1186; the proof of (2) 1269–1285 (`.17`); the four supporting lemmas 1037–1172; **Annex #6 at 2917–3000 (shard 3)**.

**TEETH:** R1-SURJ, R1-INJ, R1-PER (all GREEN); the Δ-module half is measured in its equivalent digit form by **R1-DMULT** and **R1-COB**.

---

### EFF.GRTJC.s2of3.16  [hypothesis]  ★★ (DMULT) AND ITS TWO TIERS — the note's signature honesty move

**CANONICAL STATEMENT:** verbatim, lines 1188–1267 — the (DMULT) display with its `[r2, G-1]` split header, the (DMULT-w) tier with its displayed derivation, the (DMULT-s) tier with its reportable citation failure, and the consumer split.
**FORM:** bold-headed named displays.

> “**(DMULT) [r1 — the one cited input of the coordinate calculus] [r2, G-1 —
> SPLIT INTO TWO HONEST TIERS; the r1 status line is struck below].** For
> f,g ∈ O[x] with λ := w(f), μ := w(g):
>
>     𝑅_{λ+μ}(fg) = y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g),
>     δ(λ,μ) := (s_NR(λ) + s_NR(μ) − s_NR(λ+μ))/e_m ∈ {0,1}.
>
> This is the composite-stage form of (IN-2)'s (W-MULT) … and of Montes/FGMN residual-polynomial multiplicativity; via
> JC-LOC it is the content of (IN-3)(c) on the object (IN-3)(c) is about. ~~It is
> **CITED, not proved here**~~ **[r2, G-1: PE2 caught that r1 labelled the EXACT
> (multiplier-1) display "CITED" while §0's own transport statement can only
> deliver it up to a line-wise unit — and simultaneously called the exactness "a
> finding of the r1 battery". The honest form is two tiers:]**
>
> **(DMULT-w) [the citable tier — DERIVED from the citation + §0's transport].**
> There is a unit ω(λ,μ) ∈ K_m^*, independent of f and g, with
>
>     𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g).
>
> *Derivation (displayed, the step r1 skipped).* The literature identity is
> stated for the FGMN operator R^{GMN}; (IN-3)'s transport clause is
> 𝑅_λ = c_λ·R^{GMN}_λ with c_λ a LINE-WISE unit (W-1). Substituting,
>
>     𝑅_{λ+μ}(fg) = c_{λ+μ}·R^{GMN}_{λ+μ}(fg)
>                 = c_{λ+μ}·y^δ·R^{GMN}_λ(f)·R^{GMN}_μ(g)
>                 = (c_{λ+μ}/(c_λc_μ))·y^δ·𝑅_λ(f)·𝑅_μ(g),
>
> so ω(λ,μ) = c_{λ+μ}/(c_λc_μ) — the 2-coboundary of the line-wise unit system.
> That ω depends only on the lines is what the transport gives; **nothing gives
> ω ≡ 1.**
>
> **(DMULT-s) [the exact tier — MEASURED, NOT CITED].** ω(λ,μ) ≡ 1 … *Status:* **MEASURED**
> (R1-DMULT 2,784/0 with tooth T3; §9.3 finding 1 "multiplier exactly 1"; r2's
> bilinear leg R2-BIL/R2-PHI, §9.4) and **not cited**: the r2 attempt to locate
> a multiplier-1 statement for the harness 𝑅 in the sources the note names
> FAILED reportably … So no
> corpus-pinned citation delivers ω ≡ 1; proving it would mean proving the
> ε-kit's unit system multiplicative (c_{λ+μ} = c_λc_μ), which this note does
> not do. The standing printed-source Codex leg (JC-BOX-3 item 2) rides
> unchanged.”

**Double-emission (rule 14) — the two tiers as a `[TABLE]` with their status at HEAD:**

| tier | statement | status as written | who rides it | status at HEAD |
|---|---|---|---|---|
| **(DMULT-w)** | `𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ}·𝑅_λ(f)·𝑅_μ(g)`, `ω(λ,μ) ∈ K_m^*` depending only on the lines | **DERIVED** from the citation + §0's transport (derivation displayed) | **(COORD-B)(2), (MULT-B), JC-CARRY-m, W-8, JC-BOX-4's corner closure — everything load-bearing** | **DERIVED from Thm 4.2's rank-one freeness via LEMMA JC-RANKMULT (Annex #6); the “quoted product identity” claim WITHDRAWN** |
| **(DMULT-s)** | `ω ≡ 1` | **MEASURED, NOT CITED** — the citation attempt FAILED reportably | **only JC-COB's sharp `u = a_γa_{γ′}`** (and its §4.1 restatement) | **PROVED-conditional on the measured perimeter ([ILN]† scored stratum, `m ≥ 1`, `e_m ≥ 2`) by DULEMMA THEOREM DU (Annex #1); `e_m = 1` stays measured, off-stratum pairs stay open** |

**★ THE CONSUMER SPLIT, verbatim (lines 1249–1260) — the paragraph that makes the tiering load-bearing rather than decorative:**

> “**Who consumes which tier (checked by PE2, GAP 1 blast radius).** (COORD-B)(2),
> (MULT-B), JC-CARRY-m, W-8 and JC-BOX-4's [r1] corner closure need only
> **(DMULT-w)**, and the mechanism is one line: the normalized coordinate
> ρ_λ = 𝑅_λ/a_λ with a_λ = 𝑅_λ(φ_λ) is **invariant under ANY line-wise
> rescaling of 𝑅** (the unit c_λ cancels between numerator and denominator), so
> the whole ρ-calculus can be run in the R^{GMN} gauge, where the cited identity
> is exact; equivalently, ω is absorbed into the anchor cocycle A(λ,μ), and the
> monomial-shape/degree-δ statements are ω-blind. Riding **(DMULT-s)** and
> downgraded with it: COROLLARY JC-COB's sharp value u = a_γa_{γ′} FOR THE
> HARNESS constants a (and its §4.1 restatement and second half) — on (DMULT-w)
> alone it degrades to JC-SPAN's already-proved u ∈ K_m^*. **No clause GRADE
> changes between tiers.**”

**CHAIN (rule 25) — FIVE layers. `CHAIN HOME: s1of3.43`; this unit is body site B.** r0 CITED on `gr` → r1/F1 re-based on `B`, reduced to `(DMULT)` → **r2/G-1 SPLIT (this unit)** → Annex #1 `(DMULT-s)` PROVED-conditional → **Annex #6 `(DMULT-w)` WITHDRAWN-as-citation and DERIVED. TERMINAL = Annex #6 + Annex #1.**

**★ THE WELD-AUDIT ROW, verified:** `runs/qgen/WELD_FACE_AUDIT.md` L106 records that **the one reachable GRTJC weld face, COROLLARY W-9, rides the CITABLE tier**, and quotes this note's own blast-radius sentence (JC-BOX-3 item 3, shard 3): *“If **(DMULT-w)** failed at composite order, (COORD-B)(2), (MULT-B), §§2.7–3.4, **W-8 and W-9 fail together**; if only **(DMULT-s)** failed (ω ≢ 1), JC-COB's sharp values and R1-COB's exact predicate fail while **the structural clauses stand**.”* **Consistent with this unit's consumer split; verified by this compiler against both sources.**

**CONDITIONALITY:** **The citation failure is REPORTED, not hidden** — `(IN-3)`'s transport prices `𝑅 = c·R^{GMN}` at a line-wise unit, and **TR-3′-GEN is OPEN beyond its closed strata** (with its closed-scope gloss itself corrected at r3/G-6, shard 1 `.27`).

**DERIVATION:** The `(DMULT-w)` derivation is displayed in full above. **`(DMULT-s)` has no derivation in this note** — that is the whole point of the tier.

**RESOLUTION TRACE:** statement lines 1188–1267; the disposition 434–447 (r2/G-1, shard 1 `.36`); **Annex #1 at 2805, Annex #6 at 2917–3000 (shard 3)**; the box 1960–1992 (JC-BOX-3, shard 3).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:TR-3′-GEN` — count **57** · `S3.4` — count **25**. `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` — **file EXISTS**.

**TEETH:** **(DMULT-s)** is measured by **R1-DMULT** (2,784/0, exact multiplier 1) with tooth **T3** (1,392 firings), and by **R2-BIL/R2-PHI** (261 dense bilinear pairs + the r1-skipped pair on 29/29) with teeth **U1/U2** (261/261 each). **(DMULT-w)** carries no separate leg. **Disposition: the exact tier is the measured one and the citable tier is the derived one — an unusual and honest inversion.**

---

### EFF.GRTJC.s2of3.17  [lemma]  the proof of (COORD-B)(2), and the κ = 1 pinning

**CANONICAL STATEMENT:** verbatim, lines 1269–1285.
**FORM:** `*Proof of (2) …*` block.

> “*Proof of (2) from (1) + (DMULT-w) [r2, G-1 — re-run on the citable tier].*
> Represent t ∈ B_0 at a line kE (so
> s_NR(kE) = 0, JC-FIB) and β ∈ B_n at a line n+k′E. Then δ(kE, n+k′E) = 0, so
> (DMULT-w) gives 𝑅(tβ) = ω·𝑅(t)𝑅(β) with ω = ω(kE, n+k′E) depending on the
> LINES only; dividing by the anchor constants this reads
> ρ^B_n(tβ) = κ·ρ^B_0(t)·ρ^B_n(β) with κ := ω·a_{kE}a_{n+k′E}/a_{n+(k+k′)E},
> again line-dependent only. **The in-note lemmas pin κ = 1** [r2, G-1]: take
> t = in(φ_{kE}) = in(π^k) (the anchor at line kE, JC-PER); then
> ρ^B_0(t) = 1 and ρ^B_n(π^kβ) = ρ^B_n(β) EXACTLY by JC-PIINV(c) (proved, not
> cited), so κ·1·ρ^B_n(β) = ρ^B_n(β) for a β with ρ^B_n(β) ≠ 0 forces κ = 1 —
> for every representative line pair, since κ never saw t or β. Hence
> ρ^B_n(tβ) = ρ^B_0(t)·ρ^B_n(β) for the B_0-action on B_n and, at n = 0,
> multiplicativity of ρ^B_0 (using a_0 = 𝑅_0(φ_0) = 1, φ_0 = 1, 0 ∈ W). So
> ρ^B_0 : B_0 → Δ is a bijective K_m-algebra map
> (bijective by (1)), and for β ∈ B_n the element t ∈ B_0 with ρ^B_0(t) = ρ^B_n(β)
> satisfies ρ^B_n(t·in φ_n) = ρ^B_0(t)·1 = ρ^B_n(β), hence β = t·in φ_n by
> injectivity: B_n = Δ·in(φ_n), free of rank one because ρ^B_n is injective. ∎”

**★ THE `κ = 1` PINNING IS THE STEP THAT MAKES THE WEAK TIER SUFFICE**, and it is done with IN-NOTE lemmas only: `ρ^B` is invariant under any line-wise rescaling (JC-PIINV(c), **proved, not cited**), so the unknown unit `ω` is pinned away by evaluating at `t = in(π^k)`. **This is the mechanism the consumer split at `.16` refers to as “one line”.**

**CONDITIONALITY:** Rides `(DMULT-w)` only. **PE3 re-derived “the κ = 1 pinning” and found it SOUND** (shard 1 `.21`).

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 1269–1285; the statement 1174–1186 (`.15`); the tier 1203–1218 (`.16`).

**TEETH:** the module structure is measured in its digit form by R1-DMULT / R1-COB / R2-BIL.

---

### EFF.GRTJC.s2of3.18  [definition]  (MULT-B) — the anchor cocycle, and the all-of-ℤ transport

**CANONICAL STATEMENT:** verbatim, lines 1287–1333 — the struck `(MULT)`, the `(MULT-B)` replacement, the `[r2, G-5]` virtual-anchor transport, the JC-SPAN consequence, the proof, and the `[r2, G-4]` gr-level restriction.
**FORM:** struck display + bold-headed named display + a fixed-width two-part transport.

> “~~**(MULT)** in(fg) = in(f)in(g) ((IN-3)(b)) plus (COORD) give a unique **anchor
> cocycle** A(λ,μ) ∈ Δ with ρ_{λ+μ}(αβ) = A(λ,μ)·ρ_λ(α)·ρ_μ(β) … for α ∈ gr_λ,
> β ∈ gr_μ, λ,μ,λ+μ ∈ W.~~
>
> **(MULT-B) [r1 — REPLACES (MULT); the object is B, and the input is the Δ-MODULE
> half, not mere K_m-linearity].** in(fg) = in(f)in(g) ((IN-3)(b)) plus
> (COORD-B)(2) give a unique **anchor cocycle** A(λ,μ) ∈ Δ with
>
>     ρ^B_{λ+μ}(αβ) = A(λ,μ)·ρ^B_λ(α)·ρ^B_μ(β),  A(λ,μ) = ρ^B_{λ+μ}(in φ_λ·in φ_μ),
>
> for α ∈ B_λ, β ∈ B_μ and **all λ,μ ∈ ℤ**.”

**The `[r2, G-5]` transport, verbatim (lines 1299–1315):**

>     (G5-i)  VIRTUAL ANCHOR.  For λ ∈ ℤ choose k ≥ 0 with λ+kE ∈ W (all large
>             k qualify) and set  in φ_λ := in(π)^{-k}·in(φ_{λ+kE}) ∈ B_λ.
>             k-independence: for k ≤ k′ with both lines in W, JC-PER gives
>             φ_{λ+k′E} = π^{k′−k}·φ_{λ+kE} byte-for-byte, so the two candidates
>             differ by in(π)^{-(k′−k)}in(π^{k′−k}) = 1 in B.
>     (G5-ii) ρ^B OFF THE WINDOW.  ρ^B_λ := ρ^B_{λ+kE} ∘ (in π)^k (multiply into
>             a window line, read there).  k-independence is exactly
>             JC-PIINV(c): ρ is π-invariant on the nose.

**And the consequence (lines 1315–1317):** “By JC-SPAN, `A(λ,μ) = (u/a_{λ+μ})·y^{δ(λ,μ)}` with `u ∈ K_m^*`, so **A is a MONOMIAL of y-degree exactly δ** (`e_m ≥ 2`).”

**★ THE PROOF NAMES THE STEP r0 SKIPPED, and it is a real distinction** (lines 1319–1325): “**This is the step the r0 text skipped**: a K_m-linear isomorphism `gr_λ ≅ Δ` transports the multiplication to *some* K_m-bilinear map `Δ × Δ → Δ`, and **only Δ-BILINEARITY — i.e. compatibility with the degree-0 action, (COORD-B)(2) — makes that map ‘multiply and scale by A(λ,μ)’.**”

**CONDITIONALITY:** `(MULT-B)` needs the **Δ-MODULE half**, not mere `K_m`-linearity — which is why `(COORD-B)(2)`, and hence `(DMULT-w)`, is load-bearing. **The all-of-ℤ quantifier is licensed by (G5-i)/(G5-ii), “not a parenthesis”** (r2/G-5). **The `[r2, G-4]` gr-level restriction (lines 1327–1333) is recorded ONCE so the proof bodies can cite it:** for `α ∈ gr_λ ⊆ B_λ`, `β ∈ gr_μ ⊆ B_μ`, `αβ ∈ gr_{λ+μ}` and `ρ^B_λ|_{gr_λ} = ρ_λ`, so `(MULT-B)|gr` reads `ρ_{λ+μ}(αβ) = A(λ,μ)ρ_λ(α)ρ_μ(β)` — **“the identity the proofs of §3.2, §4.1, §4.2 and §5 apply at gr level”**, and every site formerly invoking the struck `(MULT)` is re-pointed here.

**DERIVATION:** Displayed. The transport steps are each k-independent, with the reasons given (JC-PER for (G5-i), JC-PIINV(c) for (G5-ii)).

**RESOLUTION TRACE:** statement lines 1287–1333; the dispositions 470–472 (r2/G-5) and 464–469 (r2/G-4), shard 1 `.38`; consumed at `.24`, `.33`, `.35`, `.38`.

**TEETH:** JC7 (the cocycle identity, 581 samples, 261 triples); the module half by R1-DMULT/R1-COB.

---

### EFF.GRTJC.s2of3.19  [lemma]  COROLLARY JC-COB — the inner factor IS the anchor coboundary

**CANONICAL STATEMENT:** verbatim, lines 1335–1352.
**FORM:** bold-headed corollary with an `[r2, G-1]` re-fence.

> “**COROLLARY JC-COB [r1] (what the slot-δ unit u actually is) [r2, G-1 —
> re-fenced onto the EXACT tier].** On ~~(DMULT)~~ **(DMULT-s)**:
> A(λ,μ) = (a_λa_μ/a_{λ+μ})·y^{δ(λ,μ)}, i.e. JC-SPAN's unit is
> **u = a_λ·a_μ** — the product of the two anchors' own digit constants. Hence the
> structure constant of §3.2 is c_{m+1}(γ,γ′) = (a_γa_{γ′}/a_{γ+γ′})·z̄^δ: the
> INNER factor is exactly the **coboundary of the anchor normalization**, and (on
> [ILN]†'s scored stratum, composing with §3.3) ∏_{j≤m}z_j^{D_j} =
> a_γa_{γ′}/a_{γ+γ′}. *Fences [r2, G-1]:* this rides **(DMULT-s), the MEASURED
> tier** — on the citable (DMULT-w) alone the sharp values here degrade to
> JC-SPAN's u ∈ K_m^* — and the second half additionally rides [ILN]†; it does
> NOT trivialize the (CYC) property … and it re-scores no measured verdict.”

**★ THE MATHEMATICAL PAYLOAD: the inner factor of the carry cocycle is a COBOUNDARY** — `∏_{j≤m}z_j^{D_j} = a_γa_{γ′}/a_{γ+γ′}` on the scored stratum. **That is a structural explanation of the instrument's measured `M1–M5` constants**, and it is the sharpest statement in the note.

**CONDITIONALITY:** **THE ONLY CLAUSE RIDING `(DMULT-s)`.** On `(DMULT-w)` alone it degrades gracefully to JC-SPAN's already-proved `u ∈ K_m^*`. **The second half additionally rides [ILN]†.** **And the note fences the obvious over-read: it does NOT trivialize (CYC)**, which is a statement about the anchor-INDEXED presentation. **Annex #1 upgrades the tier: `(DMULT-s)` is PROVED-conditional on the measured perimeter, and “COROLLARY JC-COB's sharp `u = a_γa_{γ′}` inherits (DU-COB)”.**

**DERIVATION:** From `(DMULT-s)` (ω ≡ 1) applied at the two anchors, whose digit polynomials are the constants `a_γ`, `a_{γ′}` (JC-ANCHMON(c)).

**RESOLUTION TRACE:** statement lines 1335–1352; the tier 1220–1247 (`.16`); **Annex #1 at 2805 (shard 3)**; the box 1993–2003 (JC-BOX-8(iii), shard 3: “JC-COB's second half rides [ILN]† in addition to (DMULT-s), and the identity is displayed, not consumed by any clause”).

**TEETH:** **R1-COB** — “`𝑅_{γ+γ′}(φ_γφ_{γ′}) == a_γ·a_{γ′}·y^δ` exactly on the full anchor grid of every row” — **2,607 samples, 869/869 anchor pairs, all 29 rows, 0 violations, including the `e_m = 1` row C4H**. **With a TWO-MODE falsifier annotated post-tier-split** (r3/G-7, shard 1 `.28`): a failure with the slot set still `{δ}` refutes only `(DMULT-s)`; only a SLOT-SET failure refutes `(DMULT-w)` and `(COORD-B)(2)`.

---

### EFF.GRTJC.s2of3.20  [definition]  TC-3 as the quotient by 𝔦^B, and the ℤ/E-graded target 𝒜

**CANONICAL STATEMENT:** verbatim, lines 1354–1396 — the definition, the struck r0 display, the ideal-piece computation with its `[r3, G-5]` one-liner, the K-line conclusion, and the `[r2, G-9]` ideal transport.
**FORM:** bold-headed display + struck quotation + derivations.

> “**TC-3 = the quotient by the homogeneous ideal 𝔦^B := in(Φ_{m+1})·B** (this is
> exactly what the instrument's certifier operationalizes as division by Φ_{NR}),
> taken on B, i.e. **strictly after TC-1**. ~~[r0: "𝔦 := in(Φ_{m+1})·gr(w) … Hence
> for every λ ∈ W, gr_λ/(𝔦 ∩ gr_λ) ≅ Δ/(ψ_m) = K, a ONE-dimensional K-space" …]~~
> — struck at [r1, F1] … On B, by (COORD-B)+(MULT-B),
>
>     𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR}  corresponds to  ψ_m(y)·Δ,
>
> because ρ^B(in Φ_{m+1}·β) = A·ψ_m(y)·ρ^B(β) with
> ρ^B(in Φ_{m+1}) = ψ_m(y)/a_{wΦ_NR} **[r3, G-5 — the one-liner that makes the
> display an EQUALITY of ideal pieces rather than an inclusion, previously
> unwritten: A = A(wΦ_NR, n−wΦ_NR) = (unit)·y^{δ(wΦ_NR, n−wΦ_NR)} by
> (MULT-B) + JC-SPAN, and δ(wΦ_NR, n−wΦ_NR) = 0 for EVERY n, because
> e_m | wΦ_NR (= e_m·g_m·γ_{m+1}) gives s_NR(wΦ_NR) = 0 and
> s_NR(n−wΦ_NR) = s_NR(n), so δ = (0 + s_NR(n) − s_NR(n))/e_m = 0. Hence A is
> a CONSTANT and the image is ψ_m(y)·Δ on the nose — **were δ = 1 the quotient
> B_n/(𝔦^B ∩ B_n) would strictly contain a K-line and §3.1's "each 𝒜_ν is a
> 1-dimensional K-space" would fail**]** … Hence for **every n ∈ ℤ** …
>
>     B_n/(𝔦^B ∩ B_n)  ≅  Δ/(ψ_m)  =  K_{m+1} = K       (via y ↦ z̄),
>
> a ONE-dimensional K-space with basis the image of in(φ_n). This is the precise
> sense in which TC-3 turns the Δ-coordinate into a K-scalar — and JC-PSIKER(iii)
> says its kernel ψ_m·Δ ≠ 0 on every piece of B, so no relabeling can replace it.
> Write 𝒜 := (B/(in(π)−1))/image(𝔦^B) for the TC-transported ring; it is
> ℤ/E-graded … with 𝒜_ν = A_ν/(𝔦 ∩ A_ν) ≅ K·[φ_{γ_ν}] and 𝒜_0 = K.”

**★ THE `[r3, G-5]` ONE-LINER IS LOAD-BEARING AND WAS UNWRITTEN FOR THREE ROUNDS.** It is what turns an inclusion into an EQUALITY of ideal pieces, and the note spells out the counterfactual: **“were δ = 1 the quotient would strictly contain a K-line and §3.1's ‘each 𝒜_ν is a 1-dimensional K-space' would fail”** — i.e. **W-7's entire dimension count depended on an unwritten step.** (And the divisibility it uses, `e_m | wΦ_NR`, is the one r3/G-4 had to correct elsewhere — shard 1 `.25`.)

**CONDITIONALITY:** The `[r2, G-9]` ideal transport (lines 1389–1396) supplies the other unwritten step: JC-GAUGE(iii)'s isomorphism is only ADDITIVE, so carrying `image(𝔦^B) ∩ A_ν` onto `𝔦^B ∩ B_n` needs an argument — supplied, using that `𝔦^B` is an IDEAL of `B` and `ϑ^{-k} ∈ B`.

**DERIVATION:** Displayed in full.

**RESOLUTION TRACE:** statement lines 1354–1396; the dispositions 332–333 (r3/G-5) and 483 (r2/G-9), shard 1 `.26`/`.38`; JC-PSIKER(iii) 957–961 (`.10`); consumed at `.23`, `.27`, `.39`.

**TEETH:** JC6 (the kernel witness); the certifier's own division by `Φ_{NR}` is what the instrument operationalizes.

---

### EFF.GRTJC.s2of3.21  [TABLE]  the five PE1-listed consumers, re-derived

**CANONICAL STATEMENT:** verbatim, lines 1398–1413 — the header and the five-row table.
**FORM:** bold-headed paragraph + Markdown table.

> “**[r1] THE FIVE CONSUMERS, RE-DERIVED ONE BY ONE.** PE1 listed exactly five
> places that consumed the refuted r0 form. Each is re-derived on (COORD-B); none
> needed downgrading, and one is strengthened.”

`[TABLE]` transcribed verbatim:

| consumer (PE1's list) | what it needs | r1 verdict |
|---|---|---|
| §3.1 "every A_ν is 1-dimensional over K after TC-3" | `A_ν ≅ B_n` (JC-GAUGE(iii)) + the display above | **THROUGH** — restated in §3.1 on `B_n` |
| §3.4 THEOREM JC-IND / OB-4 (independence) | ℤ/E degree separation + each `𝒜_ν` a K-line with basis `[φ_{γ_ν}] ≠ 0` | **THROUGH** — §3.4, with the base-changed module now existing (`B_n` free rank one over Δ, (COORD-B)(2)) |
| W-7's bijectivity of Ψ | injectivity = JC-IND; surjectivity = spanning | **THROUGH and STRENGTHENED**: `dim_K 𝒜 = E`, so the K-span of the anchor classes is ALL of `𝒜` — **spanning is now a theorem, not a definition** (this is also G2's repair) |
| §5 FINDING JC-F1's dimension count | `dim_K 𝒜(T) = E` | **THROUGH** — E graded K-lines |
| (MULT) for arbitrary α,β | Δ-bilinearity of the multiplication | **THROUGH** as (MULT-B), on (COORD-B)(2) = (1) + (DMULT-w) [r2, G-1] |

**And the closing sentence (lines 1410–1413):** “Nothing else in §§2–5 used the refuted form: JC-DOM, JC-GAUGE, JC-PER, JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD and JC-PSIKER's witness are statements about integral digit arithmetic and are untouched (**PE1 re-derived all of them independently and found no defect**).”

**★ THIS IS THE BLAST-RADIUS AUDIT OF A CRITICAL, DONE PROPERLY: the finder listed the consumers, the round re-derived each, and the outcome is recorded per consumer — including one STRENGTHENING.** **“spanning is now a theorem, not a definition”** is the strengthening, and it is what makes W-7's Ψ surjective onto the whole transported ring rather than onto a span by fiat.

**ARITHMETIC AUDIT (rule 22):** consumers listed = **5** ✔ matches “PE1 listed exactly five places”; verdicts = 5 THROUGH, of which 1 STRENGTHENED, **0 downgraded** ✔ matches “none needed downgrading, and one is strengthened”.

**CONDITIONALITY:** **PE2 independently re-derived all five and “found no false statement”** (shard 1 `.35`).

**DERIVATION:** Per row, at the cited section.

**RESOLUTION TRACE:** statement lines 1398–1413; the consumers at 1460–1475 (`.23`), 1550–1572 (`.27`), 1419–1458 (`.22`), 1801–1824 (`.39`), 1287–1333 (`.18`).

**TEETH:** the r1 battery's ten families (§9.3, shard 3) test the repaired statements; PE2's independent re-derivation is the AUDIT leg.

---

### EFF.GRTJC.s2of3.22  [lemma]  ★ THEOREM W-7 — the face box (the anchor-transport isomorphism Ψ)

**CANONICAL STATEMENT:** verbatim, lines 1419–1458 — the theorem box with its structure-constant display and the six per-obligation grades.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-7.** Fix T of the [ILN]† class, m with E > 1, and window
> representatives γ_0,…,γ_{E−1} ∈ W of the E classes mod E (they exist: all
> large γ lie in W). Let 𝒜(T) be the K-span of the anchor classes [φ_{γ_ν}]
> ~~in the degree-0 component of~~ **[r1, G2]** across all ℤ/E-degrees of the
> TC-transported ring (§1, §2.10 [r1]; by §2.10's consumer table this span is
> the WHOLE transported ring). Then the K-linear
> extension of u_ν ↦ [φ_{γ_ν}] is an isomorphism of K-algebras
>
>     Ψ : (⊕_{ν∈ℤ/E} K·u_ν, u_νu_{ν′} = c_{m+1}(ν,ν′)u_{ν+ν′})  ≅  𝒜(T),
>
> where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T), and the structure
> constant is
>
>     c_{m+1}(γ,γ′) = (u/a_{γ+γ′})·z̄^{δ}          [always, §3.2 EXISTENCE]
>                   = z̄^{δ}·∏_{j=1}^{m} z_j^{D_j} = c_T(γ,γ′)
>                                                  [on [ILN]†'s scored stratum]
>
> with u = the slot-δ coefficient of JC-SPAN and a_λ = 𝑅_λ(φ_λ) ∈ K_m^* the
> anchor's own digit constant.”

**Double-emission (rule 14) — the six graded obligations as a `[TABLE]`:**

| obligation | statement | grade as written | scope |
|---|---|---|---|
| **OB-2** | well-defined | **PROVED, general m** — JC-PER, **byte-exact** | — |
| **OB-3 EXISTENCE + STRUCTURE** | there is a constant, and it is `(K_m^*-unit)·z̄^δ` | **PROVED, general m, on ALL window pairs** — **no [ILN]†, no stratum fence** | sharp form needs `e_m ≥ 2` (JC-BOX-4) |
| **OB-3 VALUE** | the unit is `∏_{j≤m}z_j^{D_j}` | **PROVED, general m, on [ILN]†'s scored stratum** (D integral ∧ off DCX) | by transport through W-8 + [ILN]† ACCEPTED |
| **OB-4** | independence | **PROVED, general m** | ~~(COORD)/(IN-3)(c) base change; the Δ-rank input is literature-carried, NOT measured~~ **→ [r2, G-4]: (COORD-B)(2) base change on `B_{γ_ν}`, riding (DMULT-w); the Δ-module input IS measured in its equivalent digit form** |
| **OB-5** | tautology fence | **DISCHARGED as an architecture statement** | with the instrument's independent-code leg as its machine bracket |
| — | the whole clause | Attempt grade 0/2 (**EXPRESSLY superseded by Annex #7**); rides §0's stack | — |

**★ THE `[r2, G-4]` CORRECTION TO OB-4'S GRADE LINE IS AN HONESTY DEFECT PE2 NAMED BY THAT WORD**, and it survived a full round inside a THEOREM box (lines 1449–1455):

> “**[r2, G-4: that grade line
> survived r1 un-superseded inside this THEOREM box — it graded OB-4 on the
> input PE1 REFUTED and denied r1's own machine leg.** As §3.4 [r1] actually
> states: (COORD-B)(2) base change on B_{γ_ν}, riding (DMULT-w); the
> Δ-module input IS measured in its equivalent digit form (R1-DMULT
> 2,784/0, R1-COB 869/869; bilinear leg R2-BIL at §9.4), with the exact
> tier (DMULT-s) measured-not-cited (JC-BOX-3).]**”

**★ THE TAUTOLOGY-FENCE PHRASE IN THE BOX IS THE NOTE'S ARCHITECTURAL COMMITMENT:** “**where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T)**”. The whole point of W-7 is that the structure constant is COMPUTED on the gr side and only THEN compared with the accepted closed form — see `.30`.

**CONDITIONALITY:** **The two lines of the structure-constant display have DIFFERENT scopes and the box marks them:** the `(u/a_{γ+γ′})·z̄^δ` form holds **ALWAYS** (§3.2, every window pair); the identification with `c_T = z̄^δ∏z_j^{D_j}` holds **only on [ILN]†'s scored stratum** (§3.3). **The wider half has ZERO machine support** (JC-BOX-2: 0 DCX, 0 non-integral-D pairs on the grid). **The `𝒜(T)` definition carries FINDING JC-F2** (shard 1 `.52`), REVIEW-OWED at three upstream sources.

**DERIVATION:** `.23`–`.30`.

**RESOLUTION TRACE:** statement lines 1419–1458; proof lines 1460–1652; the disposition 464–469 (r2/G-4, shard 1 `.38`), 387–390 (r1/G2, shard 1 `.33`); correction site 3004–3008 (Annex #7).

**TEETH:** JC1/JC2 + the instrument's **P0-OB2 0/285**, **P2-REP 0/174**, **P4-DEG 0/29**; r1's R1-PER/R1-SURJ/R1-DMULT for the repaired coordinate.

---

### EFF.GRTJC.s2of3.23  [lemma]  §3.1 OB-2 — well-definedness, re-derived on the repaired object

**CANONICAL STATEMENT:** verbatim, lines 1462–1475.
**FORM:** paragraph with a struck sentence and its `[r1, F1]` replacement.

> “JC-PER gives φ_{γ+kE} = π^kφ_γ as polynomials, so [φ_{γ+kE}] = [φ_γ] after TC-2
> (JC-GAUGE gauges in(π) to 1). Hence u_ν ↦ [φ_{γ_ν}] does not depend on which
> window representative of ν is chosen, and Ψ is defined on ℤ/E. ~~Every A_ν is
> 1-dimensional over K after TC-3 (§2.10), so Ψ maps the ν-summand onto A_ν's
> K-line.~~ **[r1, F1 — RE-DERIVED on the repaired object.]** By JC-GAUGE(iii) the
> gauged piece is A_ν ≅ **B_n** for any n ≡ ν (mod E) — JC-DOM's post-TC-1 piece,
> not gr_n (G1) — and by §2.10's repaired display
> B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K with basis the image of in(φ_n). So after TC-3
> each 𝒜_ν is a 1-dimensional K-space with basis [φ_{γ_ν}], and Ψ maps the
> ν-summand ONTO it. The step is now available at every ν and every n ≡ ν, with no
> window and no attainment side-condition (COORD-B(1)). **PROVED, general m**, on
> (DMULT-w) + (IN-5) [r2, G-1].”

**★ THE REPAIR IMPROVED THE STATEMENT: “with no window and no attainment side-condition”.** The r0 version needed `λ ∈ W` and attainment; the `B`-based version needs neither, because `in(π)` is a unit after TC-1.

**CONDITIONALITY:** Rides `(DMULT-w)` + `(IN-5)`.

**DERIVATION:** JC-PER + JC-GAUGE(iii) + §2.10's repaired display (`.20`).

**RESOLUTION TRACE:** statement lines 1462–1475; JC-PER 756–772 (`.04`); the display 1354–1381 (`.20`); consumer row 1 of `.21`.

**TEETH:** JC1 (`k = 1,2,3`); the instrument's P0-OB2 0/285 and P2-REP 0/174; r1's R1-PER/R1-SURJ/R1-DMULT.

---

### EFF.GRTJC.s2of3.24  [lemma]  ★ §3.2 THEOREM JC-CARRY-m — the composite CARRY law (no [ILN]† used)

**CANONICAL STATEMENT:** verbatim, lines 1479–1508 — the theorem, its proof, and the three displayed consequences.
**FORM:** bold-headed theorem + numbered consequences.

> “**THEOREM JC-CARRY-m.** For γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:
>
>     in(φ_γ)·in(φ_{γ′}) = (u/a_{γ+γ′})·y^{δ}·in(φ_{γ+γ′})   in the ρ-coordinate,
>     u ∈ K_m^*,  δ = δ(γ,γ′) ∈ {0,1},
>
> and after TC-3 the scalar (u/a_{γ+γ′})·z̄^δ ∈ K^* is the structure constant of
> 𝒜(T) at (γ,γ′). Pre-TC-3 it is a K-scalar iff δ < g_m (JC-LOAD).
>
> *Proof.* JC-SPAN computes 𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^δ with u ∈ K_m^*; divide by
> a_{γ+γ′} to pass to ρ, which is the definition of A(γ,γ′) in ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]**. TC-3 sends y ↦ z̄ (§2.10). ∎”

**★ THE THREE CONSEQUENCES, verbatim (lines 1495–1508), because each is separately consumed:**

> “1. **The outer/inner split is structural.** Outer = y^δ (slot shift, TC-3's
>    z̄^δ); inner = a K_m^*-unit (TC-3-blind). No coordinate choice enters. In
>    particular the instrument's rival readings H-B (inner dropped) and H-C
>    (germ-signed outer) are refuted structurally as well as numerically (H-B
>    fails on exactly the 215 pairs with nontrivial inner; H-C on 73).
> 2. **Existence is unconditional in the window.** The constant exists on EVERY
>    window pair, including pairs off [ILN]†'s scored stratum (non-integral D_j,
>    DCX pairs) where the closed form c_T is not even defined. This is a STRICT
>    extension of the accepted law's scope — with **zero machine support**, since
>    the instrument's grid contained 0 DCX and 0 non-integral-D pairs (JC-BOX-2).
> 3. **δ ∈ {0,1} always**, so "TC-3 load-bearing" ⟺ δ = 1 ∧ g_m = 1: the load
>    set is a *geography*, not a growing set — it is empty on every g_m ≥ 2 stage.”

**★ CONSEQUENCE 2 IS THE NOTE'S MOST EXPOSED CLAIM AND IT SAYS SO:** a STRICT extension of the accepted law's scope, **with zero machine support**, boxed at JC-BOX-2 with the instruction “a hostile pass should attack it there first”.

**CONDITIONALITY:** **`e_m ≥ 2`** (JC-SPAN's fence). **Rides `(DMULT-w)` via `(MULT-B)`.** **This is the composite-stage generalization of CARRY-1** (`(IN-2)`, where there is NO extra factor); the whole content is that exactly one `K_m`-unit appears.

**ARITHMETIC AUDIT (rule 22):** the three rival readings fail on **138** (H-D), **215** (H-B), **73** (H-C) of 669 pairs respectively — three distinct counts from one grid ✔, and H-D's 138 is the figure the header cites (shard 1 `.03`) ✔.

**DERIVATION:** Two lines, displayed: JC-SPAN gives `u·y^δ`; divide by `a_{γ+γ′}`; TC-3 sends `y ↦ z̄`.

**RESOLUTION TRACE:** statement lines 1479–1508; JC-SPAN 829–857 (`.08`); (MULT-B) 1291–1333 (`.18`); JC-LOAD 859–924 (`.09`); the box 1946–1951 (JC-BOX-2, shard 3).

**TEETH:** JC3 (609/609); the instrument's rival-reading counts are the refutation evidence. **Consequence 2 has NONE — proof-only, disclosed.**

---

### EFF.GRTJC.s2of3.25  [lemma]  §3.3 THEOREM JC-INNER — the inner normalization is ∏ z_j^{D_j}

**CANONICAL STATEMENT:** verbatim, lines 1512–1523.
**FORM:** bold-headed theorem.

> “**THEOREM JC-INNER.** On [ILN]†'s scored stratum (all D_j integral, pair off
> DCX), for γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:
>
>     c_{m+1}(γ,γ′) = c_T(γ,γ′) = z̄^{δ}·∏_{j=1}^{m}z_j^{D_j},
>     equivalently   u = a_{γ+γ′}·∏_{j=1}^{m}z_j^{D_j}  in K_m^*.
>
> *Proof.* By THEOREM W-8 (§4, proved independently of c_T) the gr-side constant
> equals the harness ratio: c_{m+1}(γ,γ′) = c_val(γ,γ′) :=
> read(γ+γ′,φ_γφ_{γ′})/read(γ+γ′,φ_{γ+γ′}). By [ILN]† (IN-1, ACCEPTED on exactly
> this stratum) c_val = c_T. Compose. For the second form, divide by z̄^δ (a unit,
> since ψ_m(0) ≠ 0) and use that ∏z_j^{D_j} and u/a lie in K_m, on which
> y ↦ z̄ reduction is the injection K_m ↪ K. ∎”

**★ THE PROOF IS A TWO-STEP COMPOSITION AND THE ORDER MATTERS FOR THE TAUTOLOGY FENCE:** W-8 (proved **independently of `c_T`**) identifies the gr-side constant with the harness ratio; **only then** does `[ILN]†` identify that ratio with the closed form. **“Deleting §3.3 leaves §§2–3.2 and 3.4 standing”** (§3.5).

**CONDITIONALITY:** **`[ILN]†`'s scored stratum (all `D_j` integral ∧ off DCX) AND `e_m ≥ 2`.** **This is OB-3's VALUE half — the narrower of W-7's two scopes.**

**DERIVATION:** Displayed. Note the care in the second form: dividing by `z̄^δ` is legitimate because `ψ_m(0) ≠ 0` makes it a unit, and the identification lands in `K_m` where `y ↦ z̄` is injective.

**RESOLUTION TRACE:** statement lines 1512–1523; W-8 1656–1771 (`.32`–`.36`); `(IN-1)` 505–517 (shard 1 `.41`); the coboundary form 1335–1352 (`.19`).

**TEETH:** the instrument's **P5-OB6 0/669** (both sides computed independently per pair) is W-8's leg; JC7/JC8 for the constant table.

---

### EFF.GRTJC.s2of3.26  [scope record]  ★★ §3.3 — the germ, split honestly (THE J-B ↔ J-C INTERFACE)

**CANONICAL STATEMENT:** verbatim, lines 1525–1548.
**FORM:** bold-headed paragraph + two bulleted halves.

> “**The germ, split honestly (M3, and J-B's fence).** J-B's JB-CREAD gives the
> (C-READ) transport constant c_m = ψ_{m,0} = −z_{m+1} at the level-m read, with
> the ε-carry cancelling in print coordinates (LEMMA JB-EPS, unconditional). The
> instrument measured this in the carrier and split it:
>
> * **CONFIRMED as a value law**: on all **27 eligible (g_m = 1) stages**,
>   val(Ĉ_m) = −z̄ = −z_{m+1} exactly, where Ĉ_m := Φ_{m+1} − Φ_m^{e_m} is the
>   canonical correction digit (J-B's g_m = 1 well-definedness fence, JB-BOX-4);
>   and the carrier-side class constant κ of multiplication by [Ĉ_m] satisfies
>   **κ·val(φ_{e_mγ_{m+1}}) = −z_{m+1} on all 27 stages (0 violations)**, with κ
>   itself ranging over {1, z̄, z̄², z̄³, z̄⁴}. In this note's coordinates that
>   identity is the a_λ-normalization of §3.2: κ is the class constant of the
>   correction digit measured against the anchor, so the bare letter appears
>   **exactly when the anchor's own digit constant is 1**. The claim
>   "c_m = −z_{m+1}" is therefore a statement about the transport constant modulo
>   the anchor's value normalization — J-B's fence is honored, not widened (and
>   J-B's own scope fences ride: (VD-m) free only at m ≤ 1, JA-VDIND above,
>   g_m = 1 for the Ĉ_m instance).
> * **REFUTED as OB-3's inner factor**: the brief's literal hypothesis is reading
>   H-D (inner letters replaced by −z_{m+1}) and it FAILS on **138 of 669** scored
>   pairs. §3.2 explains why structurally: the inner factor is a unit of **K_m**,
>   and −z_{m+1} ∉ K_m whenever g_m ≥ 2; on g_m = 1 stages K_{m+1} = K_m and the
>   two can coincide numerically without coinciding as laws (the instrument's own
>   printer caveat, S6.2).”

**★★ THIS IS THE J-B ↔ J-C INTERFACE, AND IT IS THE MOST IMPORTANT CROSS-READ FINDING IN THE QUEUE.** The compiler verified BOTH sides:

- **GRTJB's side** (`spec/EFF-GRTJB-s2of3.md` `.54`, source L2303–2308): the germ `ρ_m(R) = −z_{m+1}·ρ_m(f)` is “the semantic germ the J-C carrier block (W-6..W-9) needs — **displayed here as an identity of READ VALUES only**; no graded-ring (gr) object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.”
- **GRTJC's side (this unit)** receives it and **splits it in two**: **CONFIRMED as a value law** on all 27 eligible `g_m = 1` stages, **REFUTED as OB-3's inner factor** on 138/669 pairs.
- **The two are CONSISTENT and the note explains why:** J-B's statement is about READ VALUES at the level-`m` read; OB-3's inner factor is a unit of `K_m`; **`−z_{m+1} ∉ K_m` whenever `g_m ≥ 2`**, and on `g_m = 1` stages `K_{m+1} = K_m` so “the two can coincide numerically without coinciding as laws”.
- **J-B's fence is HONORED, NOT WIDENED**, and GRTJC names the inherited fences explicitly: “(VD-m) free only at `m ≤ 1`, JA-VDIND above, `g_m = 1` for the `Ĉ_m` instance”.

**★ THE PRECISE MECHANISM, and it is worth a chapter cut's attention:** “κ is the class constant of the correction digit measured against the anchor, so **the bare letter appears exactly when the anchor's own digit constant is 1**.” **So the brief's guess was a coordinate artefact of the `a_λ`-normalization** — true at `a_λ = 1`, false otherwise.

**CONDITIONALITY:** **27 eligible `g_m = 1` stages** (of 29 rows; the two `g_m = 2` rows C2I, C4I are ineligible). **J-B's own scope fences ride in.** **NOTE: GRTJB has since received post-acceptance corrections E-3/E-4; neither touches JB-CREAD, JB-EPS or JB-BOX-2's enumeration** (E-4: “JB-BOX-2's perimeter enumeration survives verbatim”), **so this inheritance is unaffected — but nothing in GRTJC says so** (shard 1 OPEN-CALL 3).

**ARITHMETIC AUDIT (rule 22):** 29 rows − 2 (`g_m = 2`: C2I, C4I) = **27 eligible** ✔ matches “27 eligible (g_m = 1) stages” and §7's “the 27 g_m = 1 stages counted in rows 3/4” ✔.

**DERIVATION:** The confirmation is measured; the refutation is measured AND explained structurally by §3.2's consequence 1.

**RESOLUTION TRACE:** statement lines 1525–1548; the supplier `spec/EFF-GRTJB-s2of3.md` `.54` (GRTJB L2303–2308); `(IN-4)` 559–565 (shard 1 `.44`); the structural explanation 1497–1501 (`.24`); the instrument's refutation 12–21 (shard 1 `.03`).

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-CREAD` — grep-verified count **36** · `JB-EPS` — **30** · `JB-BOX-4` — **2** · `JB-BOX-2` — **45**.

**TEETH:** **the instrument, both ways**: 27/27 stages 0 violations for the value law; 138/669 failures for the refuted reading. Disposition: **measurement, confirming AND refuting the same object under two different readings** — the cleanest instance in the corpus of an instrument separating a true statement from a false generalization of it.

---

### EFF.GRTJC.s2of3.27  [lemma]  §3.4 THEOREM JC-IND — K-linear independence, and spanning promoted to a theorem

**CANONICAL STATEMENT:** verbatim, lines 1552–1572.
**FORM:** bold-headed theorem with a struck passage and its `[r1, F1]` replacement.

> “**THEOREM JC-IND.** The classes [φ_{γ_0}],…,[φ_{γ_{E−1}}] are K-linearly
> independent in 𝒜(T), and each spans its own ℤ/E-graded line; so Ψ is bijective.
>
> *Proof.* By JC-GAUGE the transported ring is ℤ/E-graded and [φ_{γ_ν}] ∈ 𝒜_ν
> with ν = γ_ν mod E pairwise distinct (JC-FIB); the TC-3 ideal is generated by one
> homogeneous element, so the quotient keeps the ℤ/E-grading and 𝒜_0 = K. A
> relation Σ_ν c_ν[φ_{γ_ν}] = 0 with c_ν ∈ K = 𝒜_0 therefore splits into
> c_ν[φ_{γ_ν}] = 0 in 𝒜_ν for each ν. ~~By §2.10 each A_ν (after TC-3) is a
> 1-dimensional K-space with basis [φ_{γ_ν}] — the base change of the free
> rank-one Δ-module gr_{γ_ν} along Δ ↠ Δ/(ψ_m) = K.~~ **[r1, F1 — the base-changed
> module is now the RIGHT one, and it exists:]** by (COORD-B)(2) the free rank-one
> Δ-module is **B_{γ_ν}** (gr_{γ_ν} is not free over Δ — it is a
> finite-dimensional K_m-space, §2.10), and JC-GAUGE(iii) gives A_ν ≅ B_{γ_ν}; its
> base change along Δ ↠ Δ/(ψ_m) = K is the K-line 𝒜_ν with basis the image of
> in(φ_{γ_ν}), which is NONZERO because ρ^B(in φ_{γ_ν}) = 1 ∉ (ψ_m). Hence
> c_ν = 0. **[r1, G2/F1 — spanning is no longer definitional:]** by §2.10's
> display every 𝒜_ν equals K·[φ_{γ_ν}], so the K-span of the anchor classes is the
> whole transported ring and dim_K 𝒜(T) = E. (The r0 text said "spanning is
> definitional (design note C18)"; that reading is what G2 corrects.) This is the
> composite-stage instance of FGMN Thm 4.2's rank-one freeness, applied — after
> JC-LOC — to the object Thm 4.2 is about. ∎”

**★ TWO STRENGTHENINGS IN ONE PROOF:** (i) **the base-changed module now EXISTS** (it is `B_{γ_ν}`, free rank one over Δ, whereas `gr_{γ_ν}` is not); (ii) **spanning is promoted from a definition to a theorem** — “the r0 text said ‘spanning is definitional (design note C18)'; that reading is what G2 corrects.” **So Ψ is onto the WHOLE transported ring, not onto a span by fiat.**

**CONDITIONALITY:** Rides `(COORD-B)(2)`, hence `(DMULT-w)`. **The final sentence is the note's own summary of the whole repair: “the composite-stage instance of FGMN Thm 4.2's rank-one freeness, applied — after JC-LOC — to the object Thm 4.2 is about.”**

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 1552–1572; (COORD-B)(2) 1174–1186 (`.15`); JC-LOC 1037–1062 (`.12`); the §2.10 display 1354–1381 (`.20`); consumer row 2 of `.21`.

**TEETH:** the census genres at `.28`; **JC8's unit half was VACUOUS until R1-UNIT** (869 unit / 0 zero / 0 undefined / 0 out-of-window, with tooth T4 proving the predicate can fire).

---

### EFF.GRTJC.s2of3.28  [TABLE]  §3.4 — the case split FROM the census (examples-first)

**CANONICAL STATEMENT:** verbatim, lines 1574–1581 — the header and the three-genre table.
**FORM:** bold-headed paragraph + Markdown table.

> “**The case split FROM the census (examples-first).** The instrument's OB-4
> censuses give exactly three genres, and each is now accounted for:”

`[TABLE]` transcribed (long cells condensed with `…`, every figure preserved):

| genre (instrument) | count | this note's status |
|---|---|---|
| anchor classes (P4-DEG) | **29/29 rows bijective** | never zero: `a_λ ∈ K_m^*`, coordinate a unit constant, not divisible by `ψ_m` |
| monomial perturbations (SPAN-M) | **328 certified / 0 zero-class / 0 FAILED (606 skipped for non-integrality)** — **[r1, G6]** the parenthesis is the instrument's own verdict row, **dropped in r0 and restored here** | coordinate `= (unit)·y^k` reducing into K ⟹ certifies; 0 genre rows, so ~~no case is owed~~ **[r1, G6]** no case is owed MATHEMATICALLY — (COORD-B) covers every element of `B_n`, integral or not — while as MACHINE evidence the census covers only the **328 of 934** perturbations that stayed integral. **The 606 skipped are exactly the ones that left `O[x]`; after the r1 repair they are legitimate elements of `B` … i.e. they lie in the newly covered part of the statement and have NO machine leg.** Disclosed as a resolution limit, **“it is the one place r1 leaves a measurement owed”** |
| weight-matched sums (SPAN-S, unscored) | 435 certified / **60 zero-class** / 0 unexplained | **PROVED AWAY**: a class dies in TC-3 iff its Δ-coordinate `∈ (ψ_m)` (§2.10). The 60 are exactly that kernel; they are not anchors and carry no information about OB-4 |

**★ THE SPAN-M ROW IS THE NOTE'S SHARPEST SELF-INFLICTED IRONY, and it is disclosed as such:** the r1 repair made the statement WIDER (covering non-integral elements of `B`), and **the 606 perturbations the instrument skipped for non-integrality are exactly the newly covered ones** — so the repair moved 606 samples from “out of scope” to “in scope but unmeasured”. **“the one place r1 leaves a measurement owed”** (JC-BOX-8(i)).

**ARITHMETIC AUDIT (rule 22):** 328 certified + 606 skipped = **934** ✔ matches “328 of 934”. SPAN-S: 435 + 60 = **495** with 0 unexplained ✔.

**CONDITIONALITY:** The SPAN-M measurement gap is boxed at JC-BOX-8(i) and is **untouched by every runner** (shard 3, §9.4's closing: “the non-integral residue JC-BOX-8(i) is still untouched by every runner”).

**DERIVATION:** The three genres are the instrument's censuses; the note's job is to account for each.

**RESOLUTION TRACE:** statement lines 1574–1581; the disposition 399–401 (r1/G6, shard 1 `.33`); the box 1993–2003 (JC-BOX-8, shard 3); the kernel 1354–1396 (`.20`).

**TEETH:** P4-DEG 29/29; SPAN-M 328/934 with **606 unmeasured (PROOF-ONLY)**; SPAN-S PROVED AWAY.

---

### EFF.GRTJC.s2of3.29  [scope record]  §3.4 — the honest rider, restated on the repaired footprint

**CANONICAL STATEMENT:** verbatim, lines 1583–1601.
**FORM:** bold-headed paragraph with a struck predecessor.

> “**Honest rider.** ~~The Δ-rank input (IN-3)(c) is *literature-carried*: the
> instrument explicitly did NOT measure freeness over Δ before TC-3 (only its
> degree-separation shadow and post-TC-3 spanning). If Thm 4.2's composite-order
> instance failed, (COORD) and hence §§2.7–3.4 would fail together.~~ **[r1 —
> re-stated on the repaired footprint.]** The Δ-module input is now exactly
> **(DMULT-w)** **[r2, G-1: the CITABLE tier …]** (§2.10), applied to B = gr^K(w) (JC-LOC), and it is the
> ONLY cited
> input of the coordinate calculus: the surjectivity half that r0 also cited is
> PROVED here (JC-BSURJ). PE1's observation stands and is now answered on its own
> terms — the instrument did not measure Δ-freeness, so **r1 measures its
> equivalent digit form**: family R1-DMULT (the exact-tier identity (DMULT-s),
> 𝑅_{λ+μ}(fg) = y^δ𝑅_λ(f)𝑅_μ(g) with multiplier 1) plus its sharp corollary
> R1-COB (u = a_γa_{γ′}, riding (DMULT-s)), with tooth T3, **[r2, G-2]** on
> monomial-dominated samples — the genuinely bilinear leg is r2's R2-BIL (§9.4).
> If (DMULT-w) failed at composite order,
> (COORD-B)(2), (MULT-B) and §§2.7–3.4 would fail together — JC-BOX-3, which r1
> re-cuts to box APPLICABILITY and citation precision rather than literature
> truth.”

**★ “PE1's observation stands and is now answered on its own terms”** — the finder said the instrument did not measure Δ-freeness; the round's answer is not to argue but to **measure its equivalent digit form**. **That is the note's characteristic response to a finding: build the leg.**

**CONDITIONALITY:** **The blast radius is stated: if `(DMULT-w)` failed, `(COORD-B)(2)`, `(MULT-B)` and §§2.7–3.4 fail together.** **JC-BOX-3 is re-cut to box APPLICABILITY, not literature truth** — “the danger was never ‘Thm 4.2 might be false at composite order' but that Thm 4.2 (true, and about `K[x]`) had been transported to the wrong ambient object”.

**DERIVATION:** Record + the measurement programme it announces.

**RESOLUTION TRACE:** statement lines 1583–1601; the tier 1188–1267 (`.16`); the r2 leg 485–496 (shard 1 `.39`); the box 1960–1992 (JC-BOX-3, shard 3).

**TEETH:** R1-DMULT (2,784/0, **monomial-dominated — disclosed**), R1-COB (2,607/869), R2-BIL (261 dense pairs), teeth T3/U1/U2.

---

### EFF.GRTJC.s2of3.30  [fence]  ★ §3.5 OB-5 — the tautology fence, and the fence-hygiene disclosure

**CANONICAL STATEMENT:** verbatim, lines 1605–1652 — the dependency order, the machine bracket, and the `[r1, G8]` disclosure.
**FORM:** paragraph + numbered dependency order + bold-headed disclosure.

> “The fence demands that 𝒜(T)'s multiplication be computed in gr(w) *before* c_T
> is mentioned, and only then compared. This note's chain does exactly that, and
> the dependency order is auditable:
>
> 1. **gr-side only** (no c_T, no harness read): JC-DOM, JC-GAUGE, JC-PER, JC-FIB,
>    JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD, JC-PSIKER, §2.10's ~~(COORD)/(MULT)~~
>    **[r1, F1]** (COORD-B)/(MULT-B) with JC-LOC/JC-PIINV/JC-BSURJ/JC-COB,
>    JC-CARRY-m, JC-IND. Inputs used: the corpus's definitions of w, split,
>    anchors, REALIZE, and FGMN (b)(e) + (DMULT) **[r1: (c) enters only through
>    (DMULT), on B]**. **The structure constant's existence,
>    its outer/inner shape, its y-degree, and the TC-3 load set are all fixed
>    here.**
> 2. **comparison only** (c_T enters ONCE): §3.3 evaluates the already-computed
>    constant against the accepted closed form, through W-8's read identity.
>    Deleting §3.3 leaves §§2–3.2 and 3.4 standing.”

**The machine bracket for the fence, verbatim (lines 1621–1633), quoted because it is the instrument's architectural property:**

> “the
> gr-side constant is the unique solution of a weight inequality whose decision
> procedure calls exactly four primitives — schoolbook O[x] arithmetic, the weight
> w by iterated Φ-development, the graded scalar lift REALIZE, and the classifier's
> own next key Φ_{NR} — while `Tower.constants` (c_T) and `Tower.read` (the harness
> val) are **never called inside the determination or the certification**; all 29
> rows ran EXHAUSTIVE over K (zero witness input) with per-pair uniqueness
> machine-proved; and the tautology tooth MT3 (one anchor rescaled by a nontrivial
> scalar class) was **caught on 197/206 pairs, ≥ 1 per non-skipped row (28/28)**,
> while the c_T-defined "check" reports 0 violations by construction. The 9
> escapes are disclosed (single-pair, all prime-residue-field rows |K| ∈ {3,5},
> planted rescaling coincides with a lawful constant) — they weaken the tooth's
> resolution, not the fence's architecture.”

**★ THE `[r1, G8]` FENCE-HYGIENE DISCLOSURE IS THE MODEL OF ITS GENRE** (lines 1635–1652): the paragraph above is correctly attributed to the **instrument**, whose certifier calls neither primitive. **“This note's own battery (`grt_jc_checks.py`) DOES call both, and r0 disclosed only the c_val half.”** The full disclosure follows with the non-circularity argument spelled out: (i) `T.constants(ga, gb)['delta']` supplies only the **integer δ**, computed from the SPLIT data alone — “byte-identically §1's definition” — and the closed-form value “is a different field of the same return dict, **never read by the scored predicates**”; (ii) `T.read` is called in JC6 as the *claim under test* and in JC7/JC8 to build the constant table, “which is by construction the harness ratio `c_val` — the §9.2 disclosure”. **“Nothing circular follows, but a hostile reader should not have to re-derive that: r1 states it.”**

**CONDITIONALITY:** **The MT3 tooth has 9 disclosed escapes** (single-pair, all prime-residue-field rows with `|K| ∈ {3,5}`, where the planted rescaling coincides with a lawful constant) — “they weaken the tooth's resolution, not the fence's architecture”.

**ARITHMETIC AUDIT (rule 22):** 197 caught + 9 escapes = **206 pairs** ✔; “≥ 1 per non-skipped row (28/28)” — 29 rows minus 1 skipped ✔ (C4A, `|K| = 2`, where no nontrivial scalar class exists — §7 genre 7).

**DERIVATION:** Architectural; the dependency order is auditable by construction.

**RESOLUTION TRACE:** statement lines 1605–1652; the disposition 404–405 (r1/G8, shard 1 `.33`); the instrument 12–21 (shard 1 `.03`); §9.2's disclosure 2136–2142 (shard 3).

**TEETH:** **MT3 — the tautology tooth**, 197/206 caught, ≥1 per non-skipped row; **and the contrast the note draws is the point: “the c_T-defined ‘check' reports 0 violations by construction”.** Disposition: **planted mutant with disclosed escapes, guarding an architectural property no ordinary family could test.**

---

### EFF.GRTJC.s2of3.31  [lemma]  ★ THEOREM W-8 — the face box (harness-val = TC-read)

**CANONICAL STATEMENT:** verbatim, lines 1658–1671.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-8.** For γ,γ′ ∈ W with γ+γ′ ∈ W, and N ≡ 0 (mod E), N ≥ wΦ_{NR}:
> the gr-side structure constant of §3.2 equals the harness value ratio,
>
>     c_{m+1}(γ,γ′)  =  c_val(γ,γ′) := read(γ+γ′, φ_γφ_{γ′}) / read(γ+γ′, φ_{γ+γ′}),
>
> exactly, with every line-wise normalization cancelling; and the residue chain
> K_0 ⊂ … ⊂ K_{m+1} used by both sides is one and the same tower (J-C(iii)).
> **GRADE: PROVED at general m** on inputs ~~(COORD)+(MULT)~~ **[r1, F1]**
> (COORD-B)+(MULT-B) **on B, i.e. (DMULT-w) [r2, G-1] + the in-note lemmas
> JC-LOC/JC-PIINV/JC-BSURJ** +JC-SPAN+JC-SCAL+R3
> ~~(i.e. FGMN (b)(c)(e) via W-1, ATTEMPT)~~ **[r2, G-4: (i.e. FGMN (b)(e) +
> (c)-ENTERING-ONLY-THROUGH-(DMULT-w)-on-B (§3.5), via W-1, ATTEMPT)]**.
> Attempt 0/2. Machine: the instrument's
> **P5-OB6 0/669** (both sides computed independently per pair).”

**★ W-8 IS THE HINGE OF THE TAUTOLOGY FENCE: it identifies the gr-side constant with the harness ratio, and it is “proved independently of `c_T`”** — which is what lets §3.3 compose it with `[ILN]†` without circularity.

**CONDITIONALITY:** **Rides `(DMULT-w)`** (the citable tier) plus the in-note lemmas. **Its proof was found CRITICALLY DEFECTIVE post-acceptance and REPAIRED — see `.32`, Annex #4. The CONCLUSION is unchanged.**

**DERIVATION:** `.32`.

**RESOLUTION TRACE:** statement lines 1658–1671; **correction site 2840–2884 (Annex #4, shard 3)**; the footprint correction 464–469 (r2/G-4, shard 1 `.38`).

**TEETH:** the instrument's **P5-OB6 0/669** — both sides computed independently per pair, on every scored pair of every row.

---

### EFF.GRTJC.s2of3.32  [lemma]  ★★ §4.1 — the proof, SUPERSEDED by Annex #4 (the cured CRITICAL)

**CANONICAL STATEMENT:** verbatim, lines 1673–1710 — the read identity (†), the fence-clean defining equation, the (‡) derivation, the lift normalization and the conclusion.
**FORM:** `### 4.1 Proof` + displays.

> “Both sides are computed in the ρ-coordinate of §2.10.
>
> *The read is the reduced coordinate.* By §1 (definition), read(λ,f) = 𝑅_λ(f)(z̄).
> Hence for any f with w(f) = λ,
>
>     read(λ,f) / read(λ,φ_λ) = 𝑅_λ(f)(z̄)/a_λ = ρ_λ(in f)(z̄)          (†)
>
> (a_λ ∈ K_m^* is a constant, so its reduction is itself). **No unit is
> unaccounted for: (†) is an identity of the corpus's own definitions, and the
> line-wise ε-kit lives inside 𝑅_λ on both sides of the quotient.**
>
> *The gr-side constant.* Let c := c_{m+1}(γ,γ′) be defined by the fence-clean
> equation at the offset line λ+N, λ := γ+γ′:
>
>     in(φ_γ)in(φ_{γ′})in(X_N) = in(Λ_N(c))·in(φ_λ)   in the TC-transported ring.
>
> Apply ρ_{λ+N} and ~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** to both sides.
> LHS = A(γ,γ′)·A(λ,N)·ρ_N(in X_N) and
> RHS = A(λ,N)·ρ_N(in Λ_N(c)); A(λ,N) ≠ 0 cancels (Δ is a domain), leaving
>
>     ρ_N(in Λ_N(c)) = A(γ,γ′)·ρ_N(in X_N).                              (‡)
>
> *The lift is exactly normalized.* By JC-SCAL(b), 𝑅_N(X_N) is a constant, and by
> R3 its reduction is read(N,X_N) = 1; a constant equal to 1 after the injection
> K_m ↪ K **is** 1, so 𝑅_N(X_N) = 1 and ρ_N(in X_N) = 1/a_N. By JC-SCAL(a),
> 𝑅_N(Λ_N(c)) is a polynomial of y-degree < g_m whose reduction is
> read(N,Λ_N(c)) = c (R3); the canonical degree-<g_m representative of c is unique,
> so **𝑅_N(Λ_N(c)) = c̃(y)** on the nose and ρ_N(in Λ_N(c)) = c̃(y)/a_N.
>
> *Conclusion.* (‡) becomes c̃(y) = A(γ,γ′) = (u/a_λ)y^{δ} (JC-CARRY-m). Reducing
> mod ψ_m: c = (u/a_λ)·z̄^{δ}. On the other side, by (†) with f = φ_γφ_{γ′} and
> JC-SPAN,
>
>     c_val = ρ_λ(in φ_γ·in φ_{γ′})(z̄) = ((u/a_λ)y^{δ})(z̄) = (u/a_λ)z̄^{δ}.
>
> The two agree. ∎”

**★★ CONDITIONALITY — THIS PROOF IS SUPERSEDED BY ANNEX #4, WHICH CURES A CRITICAL.** The sol certification's finding 1 was **“REAL — W-8 improperly lifts a quotient equality”**, and the annex (shard 3, L2840–2884) supersedes §4.1 **“from ‘Apply ρ_{λ+N}' through ‘The two agree.'”** — i.e. exactly the span quoted above from `Apply ρ_{λ+N}` onward. **The repaired route, verbatim:**

> “Put `q : Δ = K_m[y] ⟶ Δ/(ψ_m) = K`. The fence-clean defining equation for `c = c_{m+1}(γ,γ′)` holds in the **TC-transported ring**, hence **after TC-3**. Therefore applying the coordinate calculus gives the **congruence**
> `q(A(γ,γ′)A(λ,N)ρ_N(in X_N)) = q(A(λ,N)ρ_N(in Λ_N(c)))`, `λ := γ+γ′`,
> **not the corresponding equality in Δ.** By the offset-transport lemma, `A(λ,N) ∈ K_m^*`, so its image in `K` is nonzero and cancels. JC-SCAL and R3 give `ρ_N(in X_N) = 1/a_N`, `ρ_N(in Λ_N(c)) = c̃(y)/a_N`, `q(c̃) = c`. Cancelling `a_N ∈ K_m^*` yields exactly
> **`c = q(A(γ,γ′))`  (W8-q).**
> Independently, the same-line read identity `(†)`, applied to `f = φ_γφ_{γ′}`, gives `c_val(γ,γ′) = q(ρ_λ(in φ_γ in φ_{γ′})) = q(A(γ,γ′))`. Thus **`c_{m+1}(γ,γ′) = c_val(γ,γ′)` exactly.** …
> **The former display `c̃(y) = A(γ,γ′)` is valid only when both polynomials have degree `< g_m`, in particular when `δ < g_m`. On the load set `δ ≥ g_m`, only the congruence `c̃(y) ≡ A(γ,γ′) (mod ψ_m)` holds; this is exactly compatible with JC-LOAD's proof that RAW polynomial equality fails there.**”

**★ THE DEFECT IN ONE LINE: the proof lifted a quotient equality to `Δ`, and on the load set `δ ≥ g_m` that lift is exactly what JC-LOAD proves impossible.** So §4.1 as written **contradicted the note's own JC-LOAD** on the load set. **The repair replaces the lift by a congruence, and the conclusion survives unchanged.** **Annex #4's consumer sweep:** “**W-8 survives with conclusion unchanged by (W8-q).** JC-INNER and W-7 OB-3 VALUE consume only `c_{m+1} = c_val`, so both survive unchanged. W-9's cocycle semantics and the residue-chain statement survive. **JC-LOAD is not weakened; its load-set obstruction is now explicitly respected rather than contradicted.**”

**SUPERSESSION KIND: `partial-withdrawal`** — a proof route replaced with the conclusion preserved and the invalid step named.

**★ ORCHESTRATOR VERIFICATION, quoted (shard 3, L3041–3048):** “Annex #4's quotient route re-checked (the defining equation holds after TC-3, so only the congruence descends; `A(λ,N)` and `a_N` in `K_m^*` cancel in `K`, giving `c = q(A(γ,γ′)) = c_val` exactly, with the polynomial-equality display scoped to `δ < g_m` — **now consistent with JC-LOAD's RAW ⟺ δ < g_m rather than contradicting it**, and the C4 counter-configuration (`g_m = 1, δ = 1`: `deg A = 1` vs `deg c̃ < 1`) is resolved as a congruence, not an equality)”.

**INDEPENDENT CHECK BY THIS COMPILER:** at `g_m = 1, δ = 1`, `A(γ,γ′) = (u/a_λ)y^1` has `deg = 1`, while `c̃(y)` is the canonical representative of `c ∈ K` of degree `< g_m = 1`, i.e. **a constant**. **So `c̃ = A` is impossible as a polynomial equality while `c̃ ≡ A (mod ψ_m)` is unproblematic** — the counter-configuration is exact, and it is precisely JC-LOAD's load set. ✔

**DERIVATION:** As displayed, with the `Apply ρ_{λ+N}`-onward span replaced by Annex #4's quotient route.

**RESOLUTION TRACE:** statement lines 1673–1710; **correction site 2840–2884 (Annex #4, shard 3)**; JC-LOAD 859–924 (`.09`); the offset lemma 1747–1760 (`.35`); the verification record 3039–3059 (shard 3).

**TEETH:** **P5-OB6 0/669** — and note that the instrument computed both sides independently and agreed, **so the machine never saw the defect**: the error was in the written route, not in the identity. **Disposition: AUDIT — decorrelated-model audit; the strongest single argument in this note for rule 27.**

---

### EFF.GRTJC.s2of3.33  [changes-record]  §4.1 — the two remarks, with r1/G7's struck identifications

**CANONICAL STATEMENT:** verbatim, lines 1712–1745.
**FORM:** bold-headed remarks with a struck passage and its `[r1, G7]` replacement.

> “*Two remarks the design note asked for.* (a) ~~The a_λ's — the anchor's own digit
> constants, i.e. the ε-normalization the harness carries — **cancel** because both
> reads in c_val sit on the SAME line λ; this is why no coboundary condition is
> needed, and it is the general-m form of the ε-collapse J-B proved
> unconditionally (JB-EPS).~~ **[r1, G7 — the two identifications inside that
> sentence are STRUCK as unproved; W-8 needs neither.]** Struck: (i) the apposition
> identifying a_λ = 𝑅_λ(φ_λ) with "the ε-normalization the harness carries", and
> (ii) the claim that the cancellation is "the general-m form of" JB-EPS — JB-EPS
> is a statement about the print-twist cocycle
> (t_m(V+V′) − t_m(V) − t_m(V′) = ε′, GRTJB §5, unconditional at every m ≥ 1) and
> so about a different object; **importing J-B's authority for this step was
> unwarranted.** What is TRUE, and all W-8 uses, is: **both reads in c_val are taken
> at the SAME line λ = γ+γ′ by the definition of c_val, so the single constant a_λ
> cancels in the ratio** — definitional, hence no coboundary condition.”

**★ “IMPORTING J-B'S AUTHORITY FOR THIS STEP WAS UNWARRANTED” — a self-caught borrowed-authority defect, and the cross-read notes it.** **GRTJB's JB-EPS is about the print-twist cocycle; GRTJC's `a_λ`-cancellation is about the anchor's digit constant on one line.** Different objects. **The true reason is definitional and one line long: both reads sit on the SAME line, so the single constant cancels.** **This is the second J-B ↔ J-C interface point** (the first is `.26`), and it is a NEGATIVE one: **a place where GRTJC initially over-claimed a J-B connection and then withdrew it.**

**The sharper true statement is then recorded (lines 1726–1732):** what IS additionally proved — **conditional on `(DMULT-s)`, the MEASURED tier** — is JC-COB's statement that “the a's do not merely cancel, they ARE the inner factor”.

**Remark (b) (lines 1732–1745)** records the footprint correction: C15's separation stands; what is used is `(COORD-B)+(MULT-B)`, i.e. the carrier-level content — with the `[r2, G-4]` correction of a footprint sentence that “contradicted r1's own headline”.

**SUPERSESSION KIND:** `counter re-reading` ×2 (two unproved identifications struck) + `inventory completion` (the footprint sentence regenerated).

**CONDITIONALITY:** The sharper statement rides `(DMULT-s)` and is therefore MEASURED-tier only.

**DERIVATION:** The surviving claim is definitional.

**RESOLUTION TRACE:** statement lines 1712–1745; the disposition 402–403 (r1/G7, shard 1 `.33`) and 464–469 (r2/G-4); JC-COB 1335–1352 (`.19`); the GRTJB object `spec/EFF-GRTJB-s2of3.md` `.46`.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-EPS` — grep-verified count **30**.

**TEETH:** none of its own; R1-COB measures the sharper statement.

---

### EFF.GRTJC.s2of3.34  [lemma]  §4.2 — the offset-transport lemma

**CANONICAL STATEMENT:** verbatim, lines 1749–1760.
**FORM:** bold-headed lemma.

> “*Statement.* For λ ∈ W and N ≡ 0 (mod E), N ≥ wΦ_{NR}: s_{NR}(N) = 0,
> δ(λ,N) = 0, A(λ,N) is a **constant**, and multiplication by X_N carries ρ_λ
> isomorphically onto ρ_{λ+N} up to that constant — in particular it preserves
> y-degrees.
>
> *Proof.* s_{NR}(N) = 0 by JC-FIB (E | N); then s_{NR}(λ+N) = s_{NR}(λ)
> (JC-PER), so δ(λ,N) = 0 and JC-SPAN gives A(λ,N) constant. Apply ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]** with ρ_N(in X_N) = 1/a_N ∈ K_m^*. ∎”

**★ SMALL BUT LOAD-BEARING IN THREE PLACES: it is the step JC-LOAD's ⟸ direction rides (and the step r3/G-1 re-routed to), the step (‡) uses in W-8's proof, and the step Annex #4's repaired route uses to cancel `A(λ,N)`.** “in particular it preserves y-degrees” is what makes the JC-LOAD dichotomy a statement about `δ` alone.

**CONDITIONALITY:** Rides `(MULT-B)`, hence `(DMULT-w)`.

**DERIVATION:** Displayed; three cited steps (JC-FIB, JC-PER, JC-SPAN) plus `(MULT-B)|gr`.

**RESOLUTION TRACE:** statement lines 1749–1760; consumed at 885–889 (`.09`'s re-routed step), 1691–1695 (`.32`), and Annex #4's route (shard 3).

**TEETH:** the instrument's **P2-OFF 0/116** (constants independent of the scalar offset) and **P0-SCAL 0/293** (scalar multiplicativity in gr), plus this note's family JC4.

---

### EFF.GRTJC.s2of3.35  [lemma]  §4.3 J-C(iii) — the residue chain

**CANONICAL STATEMENT:** verbatim, lines 1764–1771.
**FORM:** paragraph.

> “The chain used on the gr side is K_0 = k_0[x]/(Φ̄_0) and K_{j+1} = K_j[y]/(ψ_j)
> (§1), which is the classifier's residual tower `ResidueTower` by construction of
> the type: ψ_j is the residual polynomial of Φ_{j+1} at level j, and TC-3's
> identification Δ/(ψ_m) ≅ K_{m+1} is (IN-3)(d). Compatibility with (i)/(ii)'s
> scalars is the statement that the K_m ⊂ K_{m+1} used by JC-CARRY-m's inner factor
> is the same inclusion — true by construction, since the inner unit is literally a
> product of the letters z_1..z_m of the same tower. **GRADE: PROVED, general m,
> by construction — no independent content beyond the identification (IN-3)(d).**”

**★ THE GRADE LINE IS UNUSUALLY HONEST: “no independent content beyond the identification (IN-3)(d)”.** The clause is true by construction; the only imported fact is Thm 4.8/Cor 4.9.

**CONDITIONALITY:** Consumes `(IN-3)(d)` — **PDF-VERIFIED as a pair-cite at Annex #3** (shard 3), with the one line-pin slip on Cor 4.9 recorded at shard 1 `.43` (note says @1153; actual @1151; **content EXACT**).

**DERIVATION:** By construction, plus `(IN-3)(d)`.

**RESOLUTION TRACE:** statement lines 1764–1771; `(IN-3)(d)` 547–548 (shard 1 `.43`); **Annex #3's verification 2809–2815 (shard 3)**.

XREF: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` **line 1136** (Thm 4.8) and **line 1151** (Cor 4.9) — **both re-read EXACT at HEAD by this compiler**; **line 862** (the §3.3 definition of `ψ_i`) — **EXACT**.

**TEETH:** JC6 indirectly; the identification is definitional.

---

### EFF.GRTJC.s2of3.36  [lemma]  ★★★ COROLLARY W-9 — THE FOUR SUPPLY CLAUSES (special-care unit)

**CANONICAL STATEMENT:** **verbatim and UNTRUNCATED**, lines 1777–1788 — the complete face box, exactly the span WELDZERO cites.
**FORM:** display (a blockquoted face box).

> “**COROLLARY W-9.** Given W-6, W-7, W-8: (i) c_{m+1} descends to a map
> ℤ/E × ℤ/E → K^* and **is a 2-cocycle**: c(a,b)c(a+b,c) = c(b,c)c(a,b+c) — this
> is [ILN]†'s COR-2, and on the gr side it is nothing but **associativity of
> gr(w)'s multiplication**; (ii) its y-degree part δ satisfies the integer
> cocycle identity δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c) (the {0,1}-valued
> carry cocycle); (iii) 𝒜(T) is the **twisted group algebra** K^{c}[ℤ/E] of the
> abscissa-coset group over the carry cocycle; (iv) COR-4's monodromy is the
> **gauge period**: φ_{γ+E} = π·φ_γ (JC-PER) is the period, in(π) is the
> gauge unit of degree E (JC-DOM), and the E-fold orbit product
> ζ_T := ∏_{k=1}^{E−1}c(1,k) is exactly the K-scalar by which the E-fold anchor
> product differs from the π-power that TC-2 sets to 1.
> **GRADE: PROVED given W-6..W-8 (general m), S-priced as the blueprint says.**”

**★★ SOURCE-RANGE VERIFICATION (the charge's special-care requirement).** `WELDZERO_2026-08-14.md` L151 cites this as “`GRTJC_PROOF_2026-08-08.md` **L1777–1788**”. **This compiler re-read GRTJC L1777–1788 at HEAD: the range opens exactly at `> **COROLLARY W-9.** Given W-6, W-7, W-8: (i) …` and closes exactly at the `> **GRADE: …**` line. The four clauses lie wholly inside. WELDZERO's citation is EXACT, and its quotation (elided with `…`) alters no wording.** ✔

**Double-emission (rule 14) — the four supply clauses as a `[TABLE]`, with per-clause consumer and replacement.** **This is the table the charge asks for.**

| clause | exact supply | proved by | what a consumer takes from it | WELDZERO's in-cone replacement (COROLLARY WZ-B) | class |
|---|---|---|---|---|---|
| **(i)** | `c_{m+1}` descends to `ℤ/E × ℤ/E → K^*` and **is a 2-cocycle**, `c(a,b)c(a+b,c) = c(b,c)c(a,b+c)`; **= [ILN]†'s COR-2**; on the gr side **nothing but associativity of gr(w)'s multiplication** | JC-PER (descent) + associativity of `gr(w)` expanded with `(MULT-B)|gr`, reduced mod `ψ_m` | “a graded ring in which the residual assembly is associative/multiplicative” | **WZ-1**: `gr(L)` is a commutative graded ring with all nonzero homogeneous elements invertible — **associativity is free**. The concrete cocycle is `τ(a,b)` with its normalized law, **WZ-2(a)** — a monomial identity | **elementary** |
| **(ii)** | the y-degree part `δ` satisfies the INTEGER cocycle identity `δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c)` — **the {0,1}-valued carry cocycle** | take y-degrees in the same Δ-identity (`deg A(a,b) = δ(a,b)` by JC-CARRY-m); **degrees add, so the identity is the additive one** | “the integer wrap bookkeeping” | **WZ-2(a)**: `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋ ∈ {0,1}` with the additive identity, from `i(a)+i(b) = i(a+b) + e₁·wrap` | **elementary** |
| **(iii)** | `𝒜(T)` is the **twisted group algebra `K^{c}[ℤ/E]`** of the abscissa-coset group over the carry cocycle | restatement of W-7's Ψ | “one K-line per dv-height”, i.e. `dim_K 𝒜(T) = E` | **WZ-1(c) + LEMMA GENHN-2**. GENHN already records the implication in this direction: “**W-9's `dim_K 𝒜(T) = E = e₁` is this statement's graded shadow (cited as frame)**” | **already in-cone** |
| **(iv)** | COR-4's monodromy is the **gauge period**: `φ_{γ+E} = π·φ_γ` is the period, `in(π)` the gauge unit of degree `E`, and `ζ_T := ∏_{k=1}^{E−1}c(1,k)` is exactly the K-scalar by which the E-fold anchor product differs from the π-power TC-2 sets to 1 | JC-PER + JC-DOM + iterating `(MULT-B)|gr` along the orbit | — | **NOT CONSUMED**: “no occurrence in S6.1. The wrap letter layer 1 actually uses is `ϑ_t`, **derived** at WZ-2(c) from the monomials” | **n/a** |

**★ THE CONSUMPTION FACTS, verified by this compiler against three sources:**
1. **WHERE W-9 is consumed:** `runs/qgen/WELD_FACE_AUDIT.md` L123 — “**COROLLARY W-9 / `GENHN-BOX-2`** (GRTJC's twisted algebra at **GENHN-4 layer 1, μ ≥ 3**) — **R&C — the only weld face inside a count law**”. **W-9 is the ONLY GRTJC face that reaches a count law**, and it does so at exactly one site.
2. **The grep footprint is one line.** WELDZERO L146–149: “`W-9` occurs in GENHN S6.1 at **exactly one line (L874)**; layers 2 and 3 (L890–904) cite no weld label. GENHN-BOX-2's own wording agrees (‘layer 1’). **So the interface to be discharged is layer 1 and nothing else.**”
3. **WHICH TIER W-9 rides:** `WELD_FACE_AUDIT.md` L106 — “The one reachable GRTJC face, **COROLLARY W-9, rides the citable tier**” `(DMULT-w)`, **not** the measured `(DMULT-s)`. **Consistent with this note's own blast radius** (JC-BOX-3 item 3, shard 3): “If **(DMULT-w)** failed …, **W-8 and W-9 fail together**; if only **(DMULT-s)** failed …, **the structural clauses stand**.” ✔
4. **WELDZERO's method note, quoted because it bounds what the replacement achieves:** “WZ-B does **not** re-derive GENHN's layer-1 *prose* from weld-free inputs — that is what SG-2 tried and found impossible. **It proves layer 1's *conclusion* from scratch.** Any unstated content hiding inside ‘the organizing frame' is therefore **bypassed**, not audited.”

**CONDITIONALITY:** **PROVED GIVEN W-6..W-8** — the corollary adds no new input; it inherits the whole stack. **“S-priced as the blueprint says”** is the blueprint's own costing. **Everything W-9 rides, W-8 and W-7 ride: `(DMULT-w)`, `[ILN]†`'s scored stratum for the VALUE half, `e_m ≥ 2` for the sharp forms, and — via W-8 — Annex #4's repaired route.** **Annex #4 explicitly preserves it: “W-9's cocycle semantics and the residue-chain statement survive.”** **Annex #5 likewise: “W-7, W-8, and W-9 consume the factor's value or shape, not the refuted universal interpretation, and survive.”** **Annex #6 likewise: “(MULT-B), JC-IND, W-7's bijectivity, and W-9 survive at every `m` by (RM).”** **Three annexes, three explicit survivals.**

**DERIVATION:** `.37`.

**RESOLUTION TRACE:** statement lines 1777–1788; proof lines 1790–1799 (`.37`); W-6 664–699 (`.01`), W-7 1419–1458 (`.22`), W-8 1658–1671 (`.31`); the consumers `lean/notes/openmath/WELDZERO_2026-08-14.md` L151–156 and L425–443, `runs/qgen/WELD_FACE_AUDIT.md` L106, L123; the annex survivals 2884, 2911, 2990 (shard 3).

XREF: `lean/notes/openmath/WELDZERO_2026-08-14.md` — **file EXISTS**; `runs/qgen/WELD_FACE_AUDIT.md` — **file EXISTS**; `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — count **11** (COR-2's home).

**TEETH:** **JC7** — “COROLLARY W-9: the mod-E 2-cocycle identity …, the integer carry identity `δ(r,s)+δ(r+s,t) = δ(s,t)+δ(r,s+t)`, and the E-fold chain `c(φ_1^E) == ∏_{k=1}^{E−1}c_val(γ_1,kγ_1)` (monodromy = gauge period, **two ways**; E ≤ 8)” — **581 samples, 0 violations; 261 triples satisfy BOTH the K^*-cocycle identity and the integer carry identity; the E-fold chain matched the orbit product on all 15 rows with E ≤ 8.** Disposition: **executable regression covering all four clauses, with clause (iv) checked two independent ways.**

---

### EFF.GRTJC.s2of3.37  [lemma]  W-9's proofs — four one-liners

**CANONICAL STATEMENT:** verbatim, lines 1790–1799.
**FORM:** `*Proofs.*` block.

> “*Proofs.* (i) Descent is JC-PER. Associativity of gr(w) gives
> (in φ_a·in φ_b)·in φ_c = in φ_a·(in φ_b·in φ_c); expanding both with ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]**
> yields A(a,b)A(a+b,c) = A(b,c)A(a,b+c) in Δ, and reducing mod ψ_m gives the
> K^*-cocycle identity. (ii) Take y-degrees in the same Δ-identity (JC-CARRY-m:
> deg A(a,b) = δ(a,b)) — degrees add, so the identity is the additive one. (iii)
> Restatement of W-7's Ψ. (iv) With the representative γ_0 = 0 ∈ W we have
> φ_0 = 1, and JC-PER gives φ_{kE} = π^k, whose gauged class is 1; iterating
> ~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** along the orbit of the class 1 gives
> [φ_1]^E = ζ_T·[φ_0] = ζ_T. ∎”

**★ THE ELEGANCE IS THE POINT, and it is what makes WELDZERO's replacement feasible:** **(i) IS associativity** — the cocycle identity is not an extra hypothesis but a consequence of the ring being a ring. **(ii) is the SAME identity read in degrees** — one Δ-identity yields both the `K^*`-cocycle law and the integer carry law. **That is why WELDZERO can replace (i) with “associativity is free” in a graded field and (ii) with a monomial wrap identity.**

**CONDITIONALITY:** All four ride `(MULT-B)|gr`, hence `(COORD-B)(2)`, hence `(DMULT-w)`. **Clause (iii) is a restatement, so it carries W-7's scopes exactly.**

**DERIVATION:** Displayed in full above; each clause one line.

**RESOLUTION TRACE:** statement lines 1790–1799; JC-PER 756–772 (`.04`); `(MULT-B)|gr` 1327–1333 (`.18`); JC-CARRY-m 1479–1489 (`.24`); W-7's Ψ 1419–1458 (`.22`).

**TEETH:** **JC7's two-way check of clause (iv)** — the E-fold chain computed both as `c(φ_1^E)` and as the orbit product `∏_{k=1}^{E−1}c_val(γ_1,kγ_1)`, matching on all 15 rows with `E ≤ 8`. **A genuinely independent second computation of the monodromy.**

---

### EFF.GRTJC.s2of3.38  [supplier-finding]  ★ FINDING JC-F1 — the blueprint's cyclic fence, corrected

**CANONICAL STATEMENT:** verbatim, lines 1801–1824.
**FORM:** bold-headed finding + display + an `[r1, F1]` dimension-count re-derivation.

> “**FINDING JC-F1 (blueprint display correction, REVIEW-OWED — read with §6).**
> (iv)'s computation has a consequence the blueprint's cyclic-fence wording does
> not survive as literally stated. Put v := [φ_{γ_1}] (the anchor class of the
> residue class 1 ∈ ℤ/E). Then v^k = β_k·[φ_{γ_k}] with β_k := ∏_{i=1}^{k−1}c(1,i)
> ∈ K^* for k = 1..E−1, so {1,v,…,v^{E−1}} is a K-basis of 𝒜(T) and v^E = ζ_T:
>
>     **𝒜(T) ≅ K[v]/(v^E − ζ_T) as a K-algebra — at EVERY composite stage.**
>
> So "𝒜(T) is NOT F′[u′]/(u′^E − ζ′)" cannot be read as an abstract-isomorphism
> claim; it is (and, in its own adjudication procedure, always was) a claim about
> the ANCHOR-INDEXED presentation — see §6. Nothing measured is re-scored by this;
> what is corrected is a display, exactly as J-B's JB-BOX-1 corrected the J-B(iii)
> display.”

**★ A CONSEQUENCE OF W-9(iv) THAT REFUTES A BLUEPRINT DISPLAY: as an ABSTRACT K-algebra, `𝒜(T)` IS cyclic at every composite stage.** So the blueprint's fence — “`𝒜(T)` is NOT `F′[u′]/(u′^E − ζ′)`” — **cannot be an abstract-isomorphism claim**; it is a claim about the anchor-INDEXED presentation. **The note's own parallel is exact: “exactly as J-B's JB-BOX-1 corrected the J-B(iii) display”** — both notes found and corrected a blueprint display, and both boxed it REVIEW-OWED.

**CONDITIONALITY:** **REVIEW-OWED** (JC-BOX-5): “it must be adjudicated before any text repeats the fence in the abstract-isomorphism wording.” **The dimension count it needs was itself repaired at r1** (lines 1815–1824): the input `dim_K 𝒜(T) = E` came from the refuted “each `A_ν` is 1-dimensional on `gr_λ`” and now comes from §2.10's repaired display. **“THROUGH, general m, on (DMULT-w) + JC-IND.”**

**DERIVATION:** Displayed: `v^k = β_k·[φ_{γ_k}]` with `β_k := ∏_{i=1}^{k−1}c(1,i) ∈ K^*`; the powers lie in pairwise distinct `ℤ/E`-degrees, hence independent; so `{1,v,…,v^{E−1}}` is a K-basis and the K-algebra map `K[v]/(v^E − ζ_T) → 𝒜(T)` is well defined, surjective, and injective by comparing dimensions `E = E`.

**RESOLUTION TRACE:** statement lines 1801–1824; W-9(iv) 1785–1788 (`.36`); §6's law 1848–1916 (`.40`, `.41`); the box 2028–2038 (JC-BOX-5, shard 3); consumer row 4 of `.21`.

**TEETH:** **JC8** (“a CYCLIC verdict ⟹ the collapse geography; every structure constant is a UNIT so JC-F1's power basis exists”) — 898 samples; **its unit half was VACUOUS as coded (r1/G3) and was replaced by R1-UNIT + tooth T4**. The E-fold chain leg (15 rows with `E ≤ 8`) is real evidence for the power basis.

---

### EFF.GRTJC.s2of3.39  [supplier-finding]  ★ FINDING JC-F2 — the inherited “degree-0 component” defect

**CANONICAL STATEMENT:** verbatim, lines 1826–1842.
**FORM:** bold-headed finding.

> “**FINDING JC-F2 [r1, G2] (blueprint display correction, REVIEW-OWED — the second
> inherited-display defect, same treatment as JC-F1).** The corpus defines the
> carry-algebra target as "the K-span of the anchor classes **in the degree-0
> component** of the TC-transported gr(w)" — verbatim in `GRW2_TIE_DESIGN` §S2.2,
> the blueprint §S2.3, the GRTJC brief, and (until r1) §1 and W-7 of this note.
> **That reading is wrong, and it contradicts this note's own OB-4 proof:** the
> anchor class of γ lives in the ℤ/E-degree γ mod E (JC-GAUGE + JC-FIB), which is
> the degree-0 component only for ν = 0; under the literal reading the entire
> degree-separation argument of §3.4 is unavailable and W-7's Ψ would map an
> E-dimensional carrier onto a single K-line (false for E > 1). r0 used the
> CORRECTED reading in its proofs while displaying the inherited one — PE1's GAP 2.
> **The correct definition** (now in §1 and W-7): 𝒜(T) := the K-span of the anchor
> classes across ALL ℤ/E-degrees of the TC-transported ring, which by §2.10 [r1] is
> the whole transported ring, of K-dimension E. Nothing measured moves; no clause's
> proof changes. **REVIEW-OWED**: the design note, the blueprint and the brief
> carry the defective display and must be corrected there before any downstream
> text repeats it (JC-BOX-5's JC-F1 rider now covers JC-F2 as well).”

**★ THE DEFECT IS INHERITED FROM THREE UPSTREAM DOCUMENTS AND IS STILL LIVE THERE AT HEAD.** All three verified to exist: `GRW2_TIE_DESIGN_2026-08-08.md`, `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`, `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`. **The blueprint is one of the three — and the chapter blueprints are about to be written from it** (shard 1 OPEN-CALL 5).

**★ THE COUNTERFACTUAL IS DECISIVE:** under the literal reading, **W-7's Ψ would map an E-dimensional carrier onto a single K-line — false for `E > 1`, which is the standing hypothesis.** So the inherited display is not merely imprecise; it is inconsistent with the theorem it defines the target of.

**CONDITIONALITY:** **“Nothing measured moves; no clause's proof changes.”** r0 used the corrected reading in its proofs while displaying the inherited one — **a display/proof divergence, caught by PE1 as GAP 2.**

**DERIVATION:** The degree-separation argument (§3.4): `[φ_{γ_ν}] ∈ 𝒜_ν` with `ν = γ_ν mod E`, pairwise distinct by JC-FIB.

**RESOLUTION TRACE:** statement lines 1826–1842; the corrected definition 644–654 (shard 1 `.52`) and 1421–1424 (`.22`); the disposition 387–390 (r1/G2, shard 1 `.33`); the box 2028–2038 (JC-BOX-5, shard 3).

XREF: `GRW2_TIE_DESIGN_2026-08-08.md` — **EXISTS** · `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — **EXISTS** · `docs/in-progress/GRTJC_BRIEF_2026-08-05.md` — **EXISTS**.

**TEETH:** none — a display defect. Disposition: **AUDIT — in-house hostile pass** (PE1 GAP 2), with a **standing REVIEW-OWED obligation at three external documents**.

---

### EFF.GRTJC.s2of3.40  [definition]  §6 — the cyclic fence and the (CYC) property

**CANONICAL STATEMENT:** verbatim, lines 1848–1863.
**FORM:** paragraph + bold-headed definition.

> “The blueprint carries the fence as LAW: *at composite stages 𝒜(T) is NOT
> F′[u′]/(u′^E − ζ′) (adjudicated NOT-CYCLIC at 22/28 towers, value set
> {z₁, z̄, z̄z₁^b}, byte-frozen); only the last-read layer is cyclic.* The
> instrument, computing the same adjudication from a completely different side
> (gr-side certification instead of the harness value cocycle), returned
> **14 NOT-CYCLIC / 6 CYCLIC / 9 UNDECIDED**, with the 6 cyclic rows
> C2A/C2E/C2G/C2J/C3A/C4A. Both records stand. Here is the law that has both as
> instances.
>
> **(CYC), the property actually adjudicated (definition, quoted from both
> runners).** The anchor-indexed presentation is *cyclic* iff
> (α) image(c) ⊆ {1, ζ′} for a single ζ′ ∈ K^*, **and** (β) there are integers
> σ_r (σ_0 = 0) with σ_r + σ_s = σ_{r+s} + E·carry(r,s) reproducing the table.
> This is the **letter-monomial** shape: the anchors are, up to ζ′-power
> normalization, the power basis of one generator — precisely the shape D-REAL
> supplies one level down (K_{m+1}[u]/(u^{e_m} − z̄), anchors = powers of u).”

**★ TWO RECORDS, TWO ROSTERS, ONE LAW — and the note reconciles them without amending either.** The byte-frozen record says 22/28 NOT-CYCLIC; the instrument, “computing the same adjudication from a completely different side”, says 14/6/9. **“Both records stand.”**

**★ THE (CYC) DEFINITION IS TWO-PART AND BOTH PARTS MATTER** — (α) a single non-1 value, AND (β) an integer relabeling reproducing the table. **r3/G-8 (shard 1 `.29`) corrected the obstruction trigger precisely because clause (β) can fail alone** (C2C, C3I).

**ARITHMETIC AUDIT (rule 22):** 14 + 6 + 9 = **29** ✔ (the instrument's roster). The 6 cyclic rows are named and counted: C2A, C2E, C2G, C2J, C3A, C4A = **6** ✔.

**CONDITIONALITY:** The two rosters are different and the note says so; it claims only that both are instances of one law.

**DERIVATION:** Definition, “quoted from both runners”.

**RESOLUTION TRACE:** statement lines 1848–1863; the law 1865–1910 (`.41`); `(IN-2)`'s D-REAL 519–526 (shard 1 `.42`); §9.2's reproduction 2134–2142 (shard 3).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:D-REAL` — count **44**.

**TEETH:** JC8 (898 samples) reproducing the instrument's split exactly — “**the same six rows, and the same 14/6/9 split, as the instrument's MT2**”, with the disclosure that this is “a *consistency* check of W-8, not a second independent measurement of the split”.

---

### EFF.GRTJC.s2of3.41  [lemma]  ★ LAW JC-CYC — five parts, each graded

**CANONICAL STATEMENT:** verbatim, lines 1865–1910 — the five clauses (a)–(e) with their grades and the `[r3, G-8]` trigger correction.
**FORM:** bold-headed law + five bulleted clauses.

**Double-emission (rule 14) — the five clauses as a `[TABLE]` with their grades:**

| clause | grade | content |
|---|---|---|
| **(a)** | **PROVED, general m** | As an abstract K-algebra `𝒜(T) ≅ K[v]/(v^E − ζ_T)` **always** (JC-F1). “Hence the fence's content is (CYC), not abstract cyclicity, and **the operative dead route is the letter-monomial one** … The design note's S4 dead end (‘one-anchor-unit normalization does not trivialize a coset progression') is exactly this, and **it stays dead**.” |
| **(b)** | **PROVED, general m — the obstruction direction** | If the measured value table has **two distinct non-1 VALUES**, (CYC) fails by (α). ~~“two multiplicatively distinct (δ, D)-words”~~ **[r3, G-8 — FALSE as stated: two multiplicatively distinct words can evaluate to {1, v}, a SINGLE non-1 value, where (α) holds with ζ′ = v and (CYC) can only fail through (β); clause (d) exhibits exactly that genre on the note's own roster (C2C, C3I)]** |
| **(c)** | **PROVED, general m — the twist-blind direction** | If `\|K\| = 2` then `K^* = {1}`, so `c ≡ 1` and (CYC) holds with `ζ′ = 1, σ ≡ 0`. Likewise if the table has at most one non-1 value AND (β) is solvable |
| **(d)** | **MEASURED, m ≤ 3 — ONE-DIRECTIONAL** | On both rosters the cyclic side is CONTAINED in the twist-blind/collapse geography: every CYCLIC row has `\|K\| = 2` (C4A), or `g_m = 1` so `K_{m+1} = K_m` and `z̄ ∈ ⟨z_1⟩` (C2A/C2E/C2G/C3A), or `e_0 = 1` (C2J) — **0 violations of “CYCLIC ⟹ collapse” on 29 rows.** **“The CONVERSE IS FALSE and this note does not claim it”**: **13 collapse-geography rows are NOT-CYCLIC** (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C), by two visible mechanisms — **≥ 2 distinct non-1 values (up to 7 on I4C)**, or **a single value whose carry pattern no integer relabeling realizes (C2C, C3I)**. **The general form of the inclusion is OPEN (JC-BOX-5), and its measured resolution is LOW: only 2 of 29 rows lie off the collapse geography** |
| **(e)** | consistency record | The 22/28 adjudication and its value set `{z₁, z̄, z̄z₁^b}` are **unamended**; no row is re-scored; the instrument's 14/6/9 “is a different roster and a different computation, and it **reproduces the same SPLIT SHAPE**”. **The fence's program consequence is unchanged: any route through a letter-monomial cyclic presentation at a composite stage is DEAD**, and (b) now says why |

**★ CLAUSE (d) IS THE MODEL OF A HONESTLY-STATED ONE-DIRECTIONAL LAW:** the inclusion is measured (0 violations on 29 rows), **the converse is explicitly FALSE with 13 named counterexamples**, the general form is OPEN, **and the measured resolution is disclosed as LOW — “only 2 of 29 rows lie off the collapse geography”, so the law “was tested against few potential counterexamples”** (§9.2's finding 2). **A law, its refuted converse, its open general form and its weak evidence, all in one clause.**

**ARITHMETIC AUDIT (rule 22):** cyclic rows accounted: C4A (`|K| = 2`) 1 + C2A/C2E/C2G/C3A (`g_m = 1`) 4 + C2J (`e_0 = 1`) 1 = **6** ✔ matches the 6 cyclic rows of `.40`. NOT-CYCLIC collapse rows named = C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C = **13** ✔. Off-collapse rows = **2** (C2I, C4I per §9.2 finding 2) ✔, and 6 + 13 + 2 = 21; the remaining 8 of 29 are UNDECIDED-and-in-collapse (9 UNDECIDED total, of which C4I is the off-collapse one) — **consistent**. ✔

**CONDITIONALITY:** **(a)(b)(c) PROVED at general m; (d) MEASURED at m ≤ 3 and ONE-DIRECTIONAL; the general inclusion OPEN (JC-BOX-5).** **The 9 UNDECIDED rows are “a compute fence on (β)'s relabeling search”, not a finding.**

**DERIVATION:** (a) from JC-F1. (b) from the (CYC) definition's clause (α). (c) from `|K| = 2 ⇒ K^* = {1}`. (d) measured. (e) record.

**RESOLUTION TRACE:** statement lines 1865–1910; JC-F1 1801–1813 (`.38`); the disposition 339–342 (r3/G-8, shard 1 `.29`); §9.2's two findings 2144–2158 (shard 3); the box 2028–2038 (shard 3).

**TEETH:** **JC8** (898 samples, 0 violations for the ONE falsifiable half — “no CYCLIC verdict off the collapse geography”, 29 rows) **+ the note's own battery-driven finding 1**, which REFUTED the converse. Disposition: **measurement, one-directional, with the converse refuted by the same battery and the resolution disclosed as low.**

---

### EFF.GRTJC.s2of3.42  [scope record]  §6 — the consequence for the case split

**CANONICAL STATEMENT:** verbatim, lines 1912–1916.
**FORM:** bold-headed paragraph.

> “**Consequence for the case split.** The genre column "cyclic / not-cyclic /
> undecided" is carried into §7, and the cyclic side is *not* only the last-read
> layer: it includes composite stages whose residual tower collapses (g_m = 1 ⟹
> K_{m+1} = K_m). That was the instrument's M5, and it is now a stated law with a
> proved obstruction direction.”

**CONDITIONALITY:** **This CORRECTS the blueprint's “only the last-read layer is cyclic”** — composite stages with a collapsing residual tower are cyclic too. **A third blueprint-display correction in this note**, after JC-F1 and JC-F2, though this one is folded into the law rather than boxed as a FINDING.

**DERIVATION:** From JC-CYC(c)(d).

**RESOLUTION TRACE:** statement lines 1912–1916; the law 1865–1910 (`.41`); §7's genre column 1920–1934 (`.43`).

**TEETH:** the instrument's M5.

---

### EFF.GRTJC.s2of3.43  [TABLE]  §7 — the eleven-genre case split

**CANONICAL STATEMENT:** verbatim, lines 1920–1934 — the header and the eleven-row table.
**FORM:** display (an H2 head) + Markdown table.

> “## §7. THE CASE SPLIT (derived FROM the instrument's genre censuses; the case list matches the observed genre list)”

`[TABLE]` transcribed (long cells condensed with `…`, every figure and every verdict preserved):

| # | genre | rows / pairs | status |
|---|---|---|---|
| 1 | `g_m ≥ 2`, `δ = 0` | ~~C2B/C2I/C3I/C4I…~~ **[r1, G4:** the runner's own per-row print contradicts that list — **the `g_m ≥ 2` rows are EXACTLY C2I (m = 1, E = 4) and C4I (m = 3, E = 16), 2 of 29**, the complement of the 27 `g_m = 1` stages (29 − 2 = 27, consistent); C2B and C3I belong to rows 3/4**]**; the majority of pairs on those two rows | JC-CARRY-m + JC-INNER; RAW-solvable; canonical outer/inner split — **PROVED** |
| 2 | `g_m ≥ 2`, `δ = 1` | the carry-boundary pairs on `g_m = 2` rows | `δ = 1 < g_m` ⟹ still RAW-solvable (**the smoke correction that sharpened the sealed identity from `{δ≥1}` to `{δ≥g_m}`**) — **PROVED** |
| 3 | `g_m = 1`, `δ = 0` | most pairs on the 27 `g_m = 1` stages | `K_{m+1} = K_m` collapse: value identity holds; the outer/inner split is canonical on the gr side (y-degree) but **NOT recoverable from the VALUE alone** — **PROVED, with the display fence** |
| 4 | **`g_m = 1`, `δ = 1` — the TC-3 load set** | **134 of 669 pairs, 0/29 set-mismatches** | THEOREM JC-LOAD: no pre-TC-3 scalar exists; the `ψ_m`-relation is unavoidable — **PROVED** (the case that makes TC-3 load-bearing) |
| 5 | top-flat stage `e_m = 1` | C4H (+ any I4x with `e_m = 1` — **[r1, G5]** the roster has **NONE**: C4H is the unique `e_m = 1` row) | `δ ≡ 0`; JC-SPAN gives `deg ρ ≤ 1` instead of the singleton; sharp form **MEASURED not proved** **[r2, G-7: and CONDITIONALLY CLOSED on (DMULT-w) since r1 — the two statuses coexist because they have different footprints]** — JC-BOX-4 |
| 6 | interior-flat legs `e_j = 1`, `j < m` | C2J, C3E, C4H | no special role; the [RMG] fenced-corner genre is inherited via J-B, not re-opened — **PROVED (no case owed)** |
| 7 | twist-blind `\|K\| = 2` | C4A | `c ≡ 1`; cyclic by JC-CYC(c); **MT3 skipped there (no nontrivial scalar class)** — **PROVED** |
| 8 | zero-class genre (SPAN-S) | 60 samples | the TC-3 kernel `ψ_m·Δ` (§2.10) — **PROVED AWAY**, not a failure genre |
| 9 | DCX / non-integral-D | **0 rows, 0 pairs observed** | existence + structure PROVED (§3.2); **the VALUE `c_T` is not claimed and has no machine support** — JC-BOX-2 |
| 10 | prime-residue-field rows (MT3's 9 escapes) | 9 rows, `\|K\| ∈ {3,5}` | a tooth-resolution artifact, not a clause genre — disclosed, JC-BOX-7 |
| 11 | UNDECIDED cyclic rows (`E > 8`) | 9 rows | compute fence on (β)'s relabeling search — **no clause depends on them** |

**★ THE SUBTITLE IS THE METHOD, and it is the “examples-first” directive applied: “derived FROM the instrument's genre censuses; the case list matches the observed genre list”.** **The cases are not invented and then checked; they are read off the measured genres and then accounted for.**

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- `g_m ≥ 2` rows = **2** (C2I, C4I); `g_m = 1` stages = **27**; **2 + 27 = 29** ✔ and the note states the check itself.
- `e_m = 1` rows = **1** (C4H, unique per the r1 census R1-CEN) ✔ — hence JC-LOAD's theorem covers **28** rows ✔ (`.09` G5).
- Load set: **134 of 669 pairs, 0/29 set-mismatches** ✔ consistent with `.09`(c).
- MT3: 9 escapes ✔ consistent with `.30`'s 197/206.
- UNDECIDED: **9** ✔ consistent with `.40`'s 14/6/9.
- Genre 9: **0 rows, 0 pairs** ✔ consistent with `(IN-1)`'s census (shard 1 `.41`) — **and this is the genre with zero machine support.**
- **Genre count = 11**, matching the header's implicit claim that the case list matches the observed genre list ✔.

**CONDITIONALITY:** **Genre 9 is the exposed one** (proof-only, JC-BOX-2). **Genre 5's two coexisting statuses (MEASURED not proved / CONDITIONALLY CLOSED on `(DMULT-w)`) are deliberate** — “the two statuses coexist because they have different footprints”. **Annex #5 confirms genres 1–4 survive its re-display: “§7 genres 1–2 remain RAW-solvable and genres 3–4 retain the stated `g_m = 1` split.”**

**DERIVATION:** Per genre, at the cited clause.

**RESOLUTION TRACE:** statement lines 1920–1934; the dispositions 395–398 (r1/G4, G5, shard 1 `.33`), 479–480 (r2/G-7, shard 1 `.38`); the boxes 1946–2056 (shard 3); **Annex #5's sweep 2911 (shard 3)**.

**TEETH:** per genre; **genre 9 has NONE and the table says so.**

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Counts are `grep -cF` at HEAD. **19 distinct designations, all count ≥ 1** (this shard's imports are concentrated in §0, homed in shard 1; what it consumes directly is the FGMN clause set, the GRB layer and the J-B interface).

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` | 11 | `c_T`'s closed form; COR-2 (= W-9(i)) |
| 2 | `ITERLAWN_PROOF_2026-08-08.md:REALIZE` | 17 | JC-BSURJ's construction; JC-SCAL; `Φ_{m+1}`'s digits |
| 3 | `ITERLAWN_PROOF_2026-08-08.md:S4.1` | 35 | REALIZE R1/R2/R3 |
| 4 | `ITERLAWN_PROOF_2026-08-08.md:S0.1` | 13 | the class pin `ψ_j(0) ≠ 0` — every letter a unit |
| 5 | `ITERLAWN_PROOF_2026-08-08.md:DCX` | 115 | the excluded stratum (genre 9) |
| 6 | `GRB_ORDER2_2026-08-05.md:D-REAL` | 44 | the letter-monomial shape one level down (§6's (CYC) definition) |
| 7 | `GRB_ORDER2_2026-08-05.md:CARRY-1` | 19 | the last-read carry law JC-CARRY-m generalizes |
| 8 | `GRB_ORDER2_2026-08-05.md:(W-MULT)` | 8 | the last-read residual multiplicativity `(DMULT)` generalizes |
| 9 | `GRB_ORDER2_2026-08-05.md:TR-3′-GEN` | 57 | **OPEN — why `(DMULT-s)` cannot be cited** |
| 10 | `GRB_ORDER2_2026-08-05.md:S3.4` | 25 | TR-3′-GEN's home |
| 11 | `GRB_ORDER2_2026-08-05.md:S6a` | 8 | the corpus's pinned FGMN quotation |
| 12 | `GRTJB_PROOF_2026-08-08.md:JB-CREAD` | 36 | **the germ's supplier theorem — the J-B interface at `.26`** |
| 13 | `GRTJB_PROOF_2026-08-08.md:JB-EPS` | 30 | cited at `.26`; **and the authority r1/G7 withdrew at `.33`** |
| 14 | `GRTJB_PROOF_2026-08-08.md:JB-BOX-4` | 2 | the `g_m = 1` fence for the `Ĉ_m` instance |
| 15 | `GRTJB_PROOF_2026-08-08.md:JB-BOX-2` | 45 | the inherited J-B geography |
| 16 | `lean/notes/openmath/WELDZERO_2026-08-14.md` | file EXISTS | **the consumer of W-9's four clauses — verified at L151–156, L425–443** |
| 17 | `runs/qgen/WELD_FACE_AUDIT.md` | file EXISTS | **the audit classifying W-9 as “the only weld face inside a count law” (L123) and recording that it rides the citable tier (L106)** |
| 18 | `GRW2_TIE_DESIGN_2026-08-08.md` | file EXISTS | OB-1's ask (discharged at `.02`); the C13/C15/C18 objections; **a JC-F2 source** |
| 19 | `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` | file EXISTS | **Cor 2.7 @525, Thm 4.2 @1028, the rank-one clause @1030, Thm 4.8 @1136, Cor 4.9 @1151, §3.3 ψ_i @862 — all re-read EXACT at HEAD** (one line-pin slip recorded at shard 1 `.43`) |

**LITERATURE PIN VERIFICATION:** the FGMN PDF md5 `da846c82f1fcb619cefb3feb8164191e` **re-computed EXACT at HEAD**. Full line-pin table at shard 1 `.43`: **10 of 11 EXACT, one NEAR-MISS (Cor 4.9 at 1151, not 1153; content exact).**

**COMMIT / md5 / ARTIFACT VERIFICATION:** as shard 1 §3.1 — **23/23 commits resolve; 2/2 md5s EXACT; 12/12 artifacts exist; 6/6 PE1–PE6 reports exist.**

**★ W-9 CONSUMPTION VERIFICATION (the special-care requirement):** `WELDZERO_2026-08-14.md` cites `GRTJC_PROOF_2026-08-08.md` **L1777–1788**; **this compiler re-read that exact range at HEAD and confirms it is precisely COROLLARY W-9's face box, opening at the `(i)` clause and closing at the GRADE line.** WELDZERO's clause-by-clause replacement table (its L433–436) maps W-9(i)→WZ-1+WZ-2(a), (ii)→WZ-2(a), (iii)→WZ-1(c)+GENHN-2, (iv)→not consumed — **all four accounted for; transcribed at `.36`.**

### 3.2 Reverse consumer edges

`[TABLE — compiler ledger]`

| Consumer / supplier | Verified designation | Shard-2 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| **WELDZERO (the weld-zero composition unit)** | `WELDZERO_2026-08-14.md` (EXISTS) | **`.36` — W-9's four clauses** | **CONSUMES W-9 at GENHN-4 layer 1, μ ≥ 3, and REPLACES it clause by clause** (WZ-1, WZ-2(a), WZ-1(c)+GENHN-2; clause (iv) not consumed). **The replacement proves layer 1's CONCLUSION from scratch, bypassing rather than auditing anything inside “the organizing frame”** | **Not landed by GRTJC.** WELDZERO is a later, separate unit; GRTJC neither knows of nor authorises the retirement |
| **The weld-face audit** | `WELD_FACE_AUDIT.md` (EXISTS) | `.36`, `.16` | Classifies **W-9 as “R&C — the only weld face inside a count law”** and records that it **rides the citable tier `(DMULT-w)`** | Audit record; nothing landed |
| **GRTJB (J-B)** | `JB-CREAD` (36), `JB-EPS` (30), `JB-BOX-2` (45), `JB-BOX-4` (2) | **`.26`, `.33`** | **`.26`: CONFIRMS J-B's value law on 27 stages; REFUTES the brief's use of it (H-D, 138/669). `.33`: WITHDRAWS an unwarranted appeal to JB-EPS's authority.** J-B's fences ride verbatim | **Not landed on GRTJB.** Neither side retires J3b |
| GRB | `TR-3′-GEN` (57), `D-REAL` (44), `CARRY-1` (19) | `.16`, `.24`, `.40` | **TR-3′-GEN's OPEN status forces the tier split**; CARRY-1 is what JC-CARRY-m generalizes | **Not landed** |
| FGMN (literature) | layout line pins | `.08`, `.11`, `.12`, `.16`, `.35` | Clause (c) refuted-as-transported, re-routed through JC-LOC; (b)(d)(e) unchanged; **(DMULT-w) DERIVED at Annex #6** | **Not landed.** NS-9/NS-10 retargets recorded at shard 1 `.43`, not applied |
| **Three upstream docs (JC-F2)** | `GRW2_TIE_DESIGN`, blueprint, brief (all EXIST) | **`.39`** | **REVIEW-OWED at the source; the defective “degree-0 component” display is still live there at HEAD** | **Not landed by this note** |
| Downstream: DITERSUP J3b, `DIterCarrier.lean` JS1/JS2, MOVES B2-DEF, (H1)(a) | — | `.36` (W-9(i)(ii) is JS1's semantic home) | display/semantic homes only | **“No Lean hypothesis is discharged by this note”**; the gate stands |

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` Negative fences homed in lines 662–1937.

| Fence | Explicit material NOT imported / NOT claimed | Unit |
|---|---|---|
| **`(IN-3)(c)` NOT on `gr_{O[x]}`** | “the transported claim is REFUTED … consumed ONLY through JC-LOC, as (DMULT-w) on `B ≅ gr_{K[x]}(w)` — **never on `gr_{O[x]}`**” | `.11`, `.16` |
| **`(DMULT-s)` NOT cited** | “the r2 attempt to locate a multiplier-1 statement … **FAILED reportably** … **nothing gives ω ≡ 1**” | `.16` |
| **Surjectivity NOT cited** | “the surjectivity half that r0 also cited is **PROVED here (JC-BSURJ)**” | `.14`, `.29` |
| **`c_T` NOT used on the gr side** | “𝒜(T)'s multiplication is **gr(w)'s OWN (never c_T)**”; the dependency order is auditable; **“Deleting §3.3 leaves §§2–3.2 and 3.4 standing”** | `.22`, `.30` |
| **No harness read inside the determination** | the instrument's certifier calls **neither `Tower.constants` nor `Tower.read`** “inside the determination or the certification” | `.30` |
| **JB-EPS's authority NOT importable here** | “**importing J-B's authority for this step was unwarranted**”; the two identifications STRUCK | `.33` |
| **The abstract-cyclicity reading NOT the fence** | “‘𝒜(T) is NOT F′[u′]/(u′^E − ζ′)' **cannot be read as an abstract-isomorphism claim**” | `.38`, `.41`(a) |
| **The converse of JC-CYC(d) NOT claimed** | “**The CONVERSE IS FALSE and this note does not claim it**” — 13 named counterexamples | `.41`(d) |
| **`c_T`'s VALUE NOT claimed off-stratum** | genre 9: “the VALUE `c_T` is not claimed and **has no machine support**” | `.24`(2), `.43` |
| **No case owed at the interior-flat legs** | genre 6: “the [RMG] fenced-corner genre is **inherited via J-B, not re-opened**” | `.43` |
| **The 606 non-integral perturbations have NO leg** | “they lie in the newly covered part of the statement and have **no machine leg** … **the one place r1 leaves a measurement owed**” | `.28` |
| **Annex #5: the universal non-obtainability** | **withdrawn from shard 3:** the outer factor is always `q(y^δ)`; only its pre-TC-3 availability is at issue | `.01`(iv), `.09`(a) |
| **Annex #4: the lift to Δ** | **withdrawn from shard 3:** only the CONGRUENCE descends; the polynomial equality is scoped to `δ < g_m` | `.32` |
| **Annex #6: the quoted product law** | **withdrawn from shard 3:** “The statement that (DMULT-w) is itself a quoted FGMN residual-product identity is **withdrawn**” | `.16` |
| **Annex #8: `Λ_N(0)`** | **withdrawn from shard 3:** “No value `Λ_N(0)` is supplied by REALIZE” | `.07`, `.14` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` Vocabulary as in the companion shards.

| Battery row / instrument leg | Guarded unit(s) | Disposition |
|---|---|---|
| **JC1** — JC-PER + `w(π) = E`, byte-for-byte at `k = 1,2,3` | `.02`, `.04`, `.23` | Executable regression, 2,594 samples; **+ instrument P0-OB2 0/285 byte-for-byte** — double-instrumented |
| **MJ2** — mutated periodicity `φ_{γ+E} == π²φ_γ` | `.04` | Planted mutant, **285 firings — every row** |
| **JC2** — JC-FIB's tuple injectivity | `.05` | Executable regression, 570 samples; instrument P4-DEG 0/29 |
| **JC5** — JC-ANCHMON | `.06` | Executable regression, 855 samples |
| **JC4** — JC-SCAL + `𝑅_N(X_N) == 1` exactly | `.07`, `.34` | Executable regression, 443 samples; instrument P0-LIFT 0/138, P0-SCAL 0/293. **Annex #8 narrows what it evidences, not its count** |
| **MJ3** — “`Λ_N` slots ⊆ {0}” | `.07` | Planted mutant, 4 firings — **every `g_m ≥ 2` row**; 2 of 6 opportunities genuinely empty |
| **JC3 / JC3-FLAT** — JC-SPAN's sharp prediction | `.08` | **A preregistered sharp prediction, hit exactly: slot set == {δ} on 609/609 `e_m ≥ 2` pairs**; the `e_m = 1` corner measured (0 of 24 pairs with a slot > 0) |
| **MJ5** — “slot set == {δ+1}” | `.08` | Planted mutant, **633 firings — every pair** |
| **MJ1** — “TC-3 never load-bearing” | `.09` | **Planted mutant confirming an IFF in both directions: 103 firings, all 103 in the `δ ≥ g_m` load set, 0 anomalies either way** |
| **JC6 / MJ4** — the ψ-kernel witness | `.10` | Executable regression (116) + planted mutant (**29 firings, every row**) |
| **R1-BND / T2** — the slot bound | `.11`, `.14` | **A refutation converted into a scored regression**: `maxslot(G0) == 0` on 29/29, with the ladder census showing `B_n ⊋ gr_n`; T2 29/29 |
| **R1-INJ** | `.15` | Executable regression, 585 samples, both directions |
| **R1-PER / T5** | `.13` | Executable regression, 841 samples; **`c_π ≠ 1` on 20 of 29 rows** — the ρ-normalization is load-bearing; T5 406 firings |
| **R1-SURJ** | `.14` | Executable regression, 841 samples, targets realized ON THE NOSE; **the k-shift is structural** (degree 2 at `k = 5..34`) |
| **R1-DMULT / T3** | `.16`, `.29` | Executable regression, 2,784/0, exact multiplier 1 — **but monomial-dominated with an undisclosed skip, disclosed at r2/G-2**; T3 1,392 firings |
| **R1-COB** | `.19` | Executable regression, 2,607 samples / 869 anchor pairs; **TWO-MODE falsifier annotated post-tier-split** |
| **R1-UNIT / T4** | `.27`, `.38` | **The vacuous-GREEN → falsifiable conversion**: 869 unit / 0 zero / 0 undefined / 0 out-of-window, with a planted zero caught on every row |
| **R1-PSIK-LO / R1-PSIK-HI / T1** | `.10` | Executable regression both directions (197 + 197), **with the certifier's one-sidedness disclosed**; T1 29/29 |
| **R2-BIL / R2-PHI / R2-MONO / U1 / U2** | `.16`, `.29` | **The bilinear content finally exercised (261 dense pairs); the skipped pair scored 29/29; the sample composition SCORED not asserted; U2's machine-proved resolution separation (261/261 vs 0)**. **Diversity overstated until r3/G-3** |
| **JC7** | **`.36`, `.37`** | **Executable regression covering ALL FOUR W-9 clauses**: 581 samples, 261 triples satisfying both the `K^*`-cocycle and the integer carry identity; **the E-fold chain matched the orbit product on all 15 rows with `E ≤ 8` — clause (iv) checked TWO independent ways** |
| **JC8** | `.38`, `.40`, `.41` | Executable regression for the ONE falsifiable half (no CYCLIC verdict off the collapse geography, 29 rows); **the unit half was VACUOUS as coded (r1/G3)**; **reproduces the instrument's 14/6/9 split exactly — disclosed as a consistency check of W-8, not a second measurement** |
| **MT3** — the tautology tooth | `.30` | **Planted mutant guarding an architectural property: 197/206 caught, ≥1 per non-skipped row (28/28), with 9 escapes disclosed** |
| **P5-OB6 0/669** — both sides independently | `.31`, `.32` | Executable regression on the identity W-8 asserts. **Note: the machine agreed on every pair, so it never saw §4.1's route defect — Annex #4 found it by reading** |
| **PE7 / PE8** | all faces | **accepted-with-decorrelation-supplied**: PE7 re-proved JC-GAUGE by coarsened grading + a fresh `p = 7` out-of-roster leg; **PE8 re-proved W-8 + JC-LOAD's iff by a double-`(DMULT-w)` + ω-symmetry route, with the FIRST `g_m = 3` instances and an order-5 (m = 4, E = 8) tower, 885/0** |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**
1. **`.24`(2) / genre 9 — the off-stratum existence claim.** “**zero machine support** … it is proof-only, and a hostile pass should attack it there first.”
2. **`.28` — the 606 non-integral SPAN-M perturbations.** “**no machine leg** … the one place r1 leaves a measurement owed.”
3. **`.41`(d) — the general form of CYCLIC ⟹ collapse.** OPEN, with “**measured resolution … low: only 2 of 29 rows lie off the collapse geography**”.
4. **`.16` — `(DMULT-w)` itself.** No separate leg; DERIVED (and, post-Annex #6, derived from the PDF-verified rank-one theorem).
5. **`.32` — §4.1's route.** The machine agreed on every pair; **the defect was in the written derivation and only a reader could find it.**

**AUDIT rows (rule 27):**

| finding | class | ground |
|---|---|---|
| `.11` r1/F1 | in-house hostile pass | an object identification; no battery keys which ring a theorem is about |
| `.10` r1/F2 | in-house hostile pass | a quantifier |
| `.16` r2/G-1 | **transfer audit** | a failed citation search, REPORTED |
| `.22` r2/G-4 | in-house hostile pass | a grade line that “graded OB-4 on the input PE1 REFUTED and denied r1's own machine leg” |
| `.28` r1/G6 | arithmetic recount | a dropped verdict-row parenthesis restored |
| `.30` r1/G8 | in-house hostile pass | the note's own battery's call sites disclosed with the non-circularity argument |
| `.33` r1/G7 | in-house hostile pass | **a borrowed-authority defect, self-caught** |
| `.38`, `.39` (JC-F1, JC-F2) | in-house hostile pass | **two inherited blueprint displays refuted by the note's own proofs; REVIEW-OWED at the source** |
| `.41`(b) r3/G-8 | measurement, refuting | a false trigger refuted by the note's own C2C/C3I rows |
| **`.32` Annex #4** | **decorrelated-model audit** | **a CRITICAL against a live proof, invisible to a machine that agreed on all 669 pairs** |
| **`.01`(iv)/`.09`(a) Annex #5** | **decorrelated-model audit** | “JC-LOAD itself proves the counterexample supplied by the finding” |
| **`.16` Annex #6** | **decorrelated-model audit** | a citation claim withdrawn and replaced by a derivation |
| **`.07`/`.14` Annex #8** | **decorrelated-model audit** | a quantifier over a value REALIZE does not supply |

**Both-direction audit.** Every leg guards at least one unit; every unit whose `TEETH` field names a leg appears. Units with **`TEETH: NONE`** — `.12`, `.21`, `.29`, `.33`, `.39`, `.42` — are records, audits or display corrections. **Zero battery-row orphans; zero toothed-unit orphans; five signed PROOF-ONLY units; thirteen AUDIT findings, four of them decorrelated-model.**

---

## 6. BOUNDARY SELF-AUDIT (prose genre, rule 9)

GRTJC carries **zero `\tag{`** in its own prose. **But this shard is the note's mathematical half and it announces its own structure**: four blockquoted face boxes each ending in a GRADE block, thirteen named `JC-XXX` lemmas with `*Statement.*`/`*Proof.*`/`*Machine:*` sub-fields, four named displays, two FINDING blocks, a five-part LAW, and two tables. **Most boundaries are READ OFF. Five calls were made.**

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Same four-part test. **One addition forced by this note's shape: a NAMED DISPLAY (`(COORD-B)`, `(DMULT)`, `(MULT-B)`) is a unit even when it is not a lemma**, because the note cites those names hundreds of times and because two of them carry multi-round correction chains.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. The four face boxes as units (`.01`, `.22`, `.31`, `.36`) separate from their proofs.** Forced by rule 1 (DERIVATION is a field) and by the note's own layout — each box ends in a GRADE block, i.e. the box IS the addressable statement. *Not arguable.*

**2. `.36` (W-9) given a special-care treatment beyond the template.** **Directed by the charge, and the compiler went further than “quote it”:** the four clauses are separately identified, the consuming range is re-read and confirmed, the consumer's clause-by-clause replacement is transcribed, and the tier the audit says W-9 rides is cross-checked against the note's own blast-radius sentence. **The extra apparatus is a per-clause consumer column in the double-emission table** — without it, a merge run could not tell which W-9 clause WELDZERO replaces with what.

**3. §2.10 split into eleven units (`.11`–`.21`) rather than one “the repair” unit.** **The shard's largest split, and the clearest.** Test 2 and 3: `(COORD-B)`, `(DMULT)`, `(MULT-B)`, JC-LOC, JC-PIINV, JC-BSURJ, JC-COB are each cited by name from §§3–5 and from shard 3's boxes; `(DMULT)` alone carries a five-layer chain. *Candidate A:* one §2.10 unit — it is one repair. *Rejected* because the CONDITIONALITY field would have to carry the `(DMULT)` tier split, the Annex #6 withdrawal, the Annex #8 quantifier repair and the `(MULT-B)` all-of-ℤ transport at once.

**4. `.16` ((DMULT) and its two tiers) kept as ONE unit.** **Genuinely arguable, and the compiler chose merge.** *Candidate A:* three units — the r1 `(DMULT)` display, `(DMULT-w)`, `(DMULT-s)`. *Candidate B (chosen):* one. **Reason:** the tiers are DEFINED BY CONTRAST — “(DMULT-s)” is “(DMULT-w) with `ω ≡ 1`” — and the consumer split (“who rides which tier”) is a statement about the PAIR. Splitting would put the consumer split in neither unit or duplicate it. *Cost:* the longest unit in the shard. **Mitigation and merge recommendation: sub-IDs `.16/w` and `.16/s`**, since Annex #1 hits only `/s` and Annex #6 only `/w`.

**5. `.32` (§4.1's proof) kept as a unit though Annex #4 supersedes most of it.** **Arguable.** *Candidate A:* emit only the surviving part (the read identity `(†)`) and treat the rest as superseded record. *Candidate B (chosen):* the whole proof as one unit, with Annex #4's replacement route quoted IN FULL in CONDITIONALITY. **Reason:** the superseded span is where a CRITICAL lived, and **a chapter cut must be able to see both the defective route and the repair** — the defect (lifting a quotient equality) is instructive and the annex's own consumer sweep refers to the original by its opening words (“from ‘Apply ρ_{λ+N}' through ‘The two agree.'”). *Cost:* a long unit carrying a mostly-superseded quotation.

**6. `.26` (the germ split) as its own unit rather than part of `.25` (JC-INNER).** Test 4, decisively: **opposite predicates.** `.25` is a theorem; `.26` is a two-sided adjudication of an inherited claim — one half CONFIRMED, one half REFUTED. **And it is the J-B ↔ J-C interface, which the charge asks to be reported on.** *Not arguable.*

**7. §6's law as two units (`.40` definition, `.41` the five graded clauses).** Test 1 and 3: the `(CYC)` definition is quoted “from both runners” and is the object both records adjudicate; the five clauses carry five different grades and one carries an r3 correction. *Weakly arguable* — they read as one section. *Chosen split* because a chapter cut needs the definition without the five gradings.

**8. `.43` (§7's case split) as ONE unit with eleven rows.** Rule 5 makes tables units. *Candidate A:* eleven units. *Rejected* — the table's claim is that **the case list MATCHES the observed genre list**, which is a property of the whole table and is what the arithmetic audit checks.

### 6.2 Merges deliberately NOT made

- **`.02`–`.10`** are nine separate lemma units, not one “W-6's lemmas” unit: each is named, cited independently, and separately re-derived by PE1.
- **`.12`–`.14`** (JC-LOC, JC-PIINV, JC-BSURJ) stay separate: they are the three lemmas the r1 repair ADDED, each with its own machine family.
- **`.38`/`.39`** (JC-F1, JC-F2) stay separate: two different defective displays, two different sets of upstream sources, though one shared REVIEW-OWED rider.
- **`.36`/`.37`** (W-9's box and its proofs) stay separate: rule 1, and the box is what WELDZERO cites.

### 6.3 Which template rules fought this note's genre

1. **★ `partial-withdrawal` is needed FOUR times in this shard alone** — Annex #4 (`.32`, a proof route replaced), Annex #5 (`.01`/`.09`, a clause re-displayed with a qualifier), Annex #8 (`.07`/`.14`, a quantifier narrowed with a replacement display), and Annex #6 (`.16`, a citation claim withdrawn and replaced by a derivation). **Combined with GRTJB's E-3, that is FIVE instances across the two notes. The enum gap is confirmed beyond doubt.**
2. **★ A face box consumed CLAUSE BY CLAUSE by a downstream unit needs a per-clause consumer field.** W-9 is quoted as four clauses and replaced as four clauses; without a per-clause column at `.36`, the WELDZERO edge is unrepresentable. **Fix: `SUPPLY-CLAUSES:` — an enumerated sub-field on any unit a downstream note consumes piecewise, with a consumer column.** This shard invents it ad hoc; it should be a rule.
3. **Rule 22's arithmetic audit is where this note beats its sibling, and the cause is structural.** Every headline in GRTJC reconstructs from its own table (`.36`'s JC7 counts, `.43`'s 2 + 27 = 29, `.41`'s 6 + 13 + 2, `.30`'s 197 + 9 = 206, `.28`'s 328 + 606 = 934). **GRTJB's §7.1 headline does not.** The difference is FREEZE PREDICATE 3 — a standing rule forced by three census failures. **Recommend the merge record it as a corpus-level lesson.**
4. **A tooth that PROVES a prior leg's blindness has no disposition name.** U2 “fired 261/261 on the dense pairs and 0 on the r1-tested pairs — **machine proof that the r1 leg had zero resolution against the cross-term class**”. That is stronger than a `signed vacuity disclosure` (which asserts vacuity) and different from a planted mutant (which tests the claim). **Fix: a `resolution-separation` disposition.**
5. **(Confirming shard 1.) The `bred-defect` marker again.** This shard homes the targets of three bred defects (`.16`'s tier split answering r1's mislabel, `.28`'s SPAN-M gap CREATED by the r1 widening, `.29`'s rider re-stated because r1's own footprint claim outran its text). **Three shards of GRTJC, four of GRTJB — the pattern is the corpus's dominant failure mode.**

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (five inbound, all from shard 3's annexes) — this is the shard the annexes hit hardest.**
  (1) **Annex #4** → **`.32` (§4.1's proof, from “Apply ρ_{λ+N}” through “The two agree.”)** and `.31`. **Cures a CRITICAL**; conclusion unchanged; **JC-LOAD's load-set obstruction now respected rather than contradicted.**
  (2) **Annex #5** → **`.01`(iv), `.09`(a)** and every unqualified “not obtainable from TC-1/TC-2 alone”. The outer factor is always `q(y^δ)`; only pre-TC-3 availability is at issue.
  (3) **Annex #6** → **`.16`, `.15`, `.18`, `.27`, `.36`**. `(DMULT-w)`'s “quoted identity” claim WITHDRAWN; DERIVED via **LEMMA JC-RANKMULT**; the boxed stack entry is the chain's TERMINAL.
  (4) **Annex #8** → **`.07`, `.14`**. `Λ_N`'s quantifier narrowed to `c ∈ K^*`; JC-BSURJ's zero-target wording repaired.
  (5) **Annex #1** → **`.16`, `.19`**. `(DMULT-s)` PROVED-conditional on the measured perimeter; JC-COB's sharp form inherits (DU-COB).
  **Plus Annex #7** (the status supersession) reaching every grade line's “Attempt 0/2”.
- **Range-edge audit.** Head: L660 `---`, L661 blank, L662 `## §2.`. Tail: L1934 closes §7's table, L1935 blank, L1936 `---`, L1937 blank, L1938 `## §8.`. **No source statement unit is cut at either edge**; both are the manifest's own and fall on section breaks.
- **Outside-HOME material used only as resolver:** the header, S-STATUS series, six repair-round blocks, §0's five inputs and the one-line stack, §1's objects (shard 1); §§8–10's boxes, machine bracket, grade box, stack and consumers, the acceptance record and Annexes #1–#8 (shard 3).
- **Protocol versus supply.** This shard IS the supply. **No consumption append is claimed landed on any supplier, and none is invented.**
- **Numbering.** Temporary IDs `EFF.GRTJC.s2of3.01`–`.43`, to be reconciled at the merge run.
- **★ MERGE HAZARDS TO FLAG (seven).**
  1. **★ `.36` (W-9) is consumed CLAUSE BY CLAUSE by WELDZERO and must carry its per-clause table into the merge.** The retirement of GENHN-BOX-2 turns on which clause supplies what: **(i)→WZ-1+WZ-2(a), (ii)→WZ-2(a), (iii)→WZ-1(c)+GENHN-2, (iv)→NOT CONSUMED.** A merge that treats W-9 as one opaque face loses the whole discharge argument.
  2. **★ `.32` MUST be read through Annex #4.** The frozen §4.1 lifts a quotient equality to `Δ`, which **contradicts JC-LOAD on the load set**. Any chapter cut quoting §4.1 from the body alone reproduces a CRITICAL.
  3. **`.16` needs sub-IDs `/w` and `/s`** — Annex #1 hits only the exact tier, Annex #6 only the weak one, and the weld audit's “W-9 rides the citable tier” cites the distinction.
  4. **`.26` is the J-B ↔ J-C interface** and must be wired to `spec/EFF-GRTJB-s2of3.md` `.54` in both directions. **The confirmation (27 stages) and the refutation (138/669) are two halves of one finding.**
  5. **`.33` records that an appeal to JB-EPS was WITHDRAWN.** A merge that greps for J-B citations in GRTJC will find JB-EPS at `.26` (valid) and at `.33` (withdrawn). **They must not be conflated.**
  6. **`.39`'s JC-F2 is REVIEW-OWED at three upstream documents, one of which is the GRT weld blueprint** the chapter blueprints will be written from.
  7. **Annex #5 supersedes “every unqualified occurrence”** of a phrase, not a named list of sites. **The merge must sweep for it** — `.01`(iv) and `.09`(a) are the two this compiler found in range.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — W-9's consumer replaces it clause by clause, but BYPASSES rather than audits the frame

`.36` records WELDZERO's clause-by-clause replacement and, crucially, WELDZERO's own **method note**: “WZ-B does **not** re-derive GENHN's layer-1 *prose* from weld-free inputs — that is what SG-2 tried and found impossible. **It proves layer 1's *conclusion* from scratch.** Any unstated content hiding inside ‘the organizing frame' is therefore **bypassed**, not audited.” **So the retirement of GENHN-BOX-2 rests on a from-scratch proof of the conclusion, not on an audit of what W-9 was actually supplying.** **That is honest and is probably the right move** — but it means **W-9's clause (i)'s content (“on the gr side it is nothing but associativity of gr(w)'s multiplication”) is never checked against what GENHN-4 layer 1 actually used.** **Decision needed: whether the weld audit wants a residual check that GENHN-4 layer 1 used nothing from W-9 beyond the four clauses WZ-B replaces** — the grep footprint is one line (GENHN S6.1 L874), which is strong evidence but is a NAME grep, and GRTJC's own r4/G-4 showed that a name grep can miss a content line (shard 1 `.20`). The compiler recorded both facts and asserted neither.

### OPEN-CALL 2 — Annex #4 cures a CRITICAL, and the acceptance predates it by six days

`.32` records that §4.1's proof **lifted a quotient equality**, and that on the load set `δ ≥ g_m` this **contradicts the note's own JC-LOAD**. The repair is exact and the conclusion survives. **But the acceptance record is dated 2026-08-06 and the certifier annex 2026-08-12** — so **GRTJC was ACCEPTED at 2/2 on a text containing a CRITICAL against a live proof of one of its four faces.** Annex #7 handles the STATUS question (the note is accepted “together with the post-acceptance corrections in Annexes #4–#8”), which is more than GRTJB does. **Decision needed: whether W-8's acceptance needs re-confirming on the post-annex text, and whether the sol discharge (the GRTJB analogue was “awaiting sol discharge (cert3)”) is a prerequisite for the chapter blueprints.** Recorded because the chronology is counter-intuitive and a reader may take the 2/2 as covering the repaired text.

### OPEN-CALL 3 — the off-stratum existence claim is the note's most exposed statement and it is signed as such

`.24`(2) claims the structure constant **exists on EVERY window pair, including pairs off `[ILN]†`'s scored stratum where the closed form `c_T` is not even defined** — “a STRICT extension of the accepted law's scope — with **zero machine support**, since the instrument's grid contained 0 DCX and 0 non-integral-D pairs”. JC-BOX-2 adds: “it is proof-only, and **a hostile pass should attack it there first**.” **Eight hostile passes did not.** **Decision needed: whether the blueprint phase wants a targeted instrument (a grid containing DCX and non-integral-D pairs), or whether the off-stratum half should be dropped from what the note supplies.** The claim is not load-bearing for anything downstream that the compiler can see — W-9's clause (iii) and the weld consumption both live on the scored stratum — **so dropping it would cost nothing and would remove the note's largest unmeasured claim.**

### OPEN-CALL 4 — JC-CYC(d)'s measured resolution is low, and the note says so

`.41`(d) records the inclusion CYCLIC ⟹ collapse as **MEASURED at `m ≤ 3`, 0 violations on 29 rows** — and immediately discloses that **only 2 of 29 rows lie OFF the collapse geography**, so “‘CYCLIC ⟹ collapse' was tested against few potential counterexamples”, with the recommendation “**A hostile pass should build `g_m ≥ 2` rows with small tables.**” **Eight hostile passes did not build them either.** **Decision needed: whether the general form (JC-BOX-5's OPEN row) is worth closing, or whether the fence's program consequence — “any route through a letter-monomial cyclic presentation at a composite stage is DEAD” — is all that is needed downstream.** The compiler notes that the program consequence rides clause (b), which is **PROVED**, not clause (d).

### OPEN-CALL 5 — three annexes each say “W-9 survives”, but none re-checks W-9's proof

Annexes #4, #5 and #6 each contain a consumer-sweep line asserting that **W-9 survives** their correction (`.36`). Each is plausible — W-9's proofs are four one-liners riding `(MULT-B)|gr`, JC-PER and JC-DOM, none of which the annexes touch. **But no annex re-derives W-9's four clauses on the corrected footing**, and W-9 is the face a downstream unit actually consumes. **Decision needed: whether a one-paragraph re-derivation of W-9 on the post-annex footing is owed** — it would be cheap (the proofs are four lines) and would close the only place in this note where a consumed face's survival is asserted three times and verified zero times. The compiler recorded the three survival claims verbatim and did not treat them as a verification.

### Recorded source defects (flagged, not silently repaired)

1. **`.01`, `.22`, `.31`, `.36`:** all four face boxes carry “Attempt grade 0/2” / “Attempt 0/2”, **EXPRESSLY superseded by Annex #7** but not edited. Tagged `superseded`, not STALE — GRTJC's status handling is correct; the reader must simply follow the annex.
2. **`.32`:** §4.1's frozen proof contains the CRITICAL Annex #4 cures. **The body text is unmarked at the defect site** — there is no inline pointer from §4.1 to Annex #4, unlike the in-round `[rk, G#]` brackets. **A reader of §4.1 alone gets no warning.** Merge hazard 2.
3. **`.09`(a), `.01`(iv):** Annex #5 supersedes “**every unqualified occurrence**” of a phrase rather than a named site list. **This compiler found two in range; the sweep is not certified complete** (the same class of limit GRTJC itself discloses for its name-pattern census at shard 1 `.20`).
4. **`.16`:** `(DMULT)`'s status changed FOUR times (CITED → split → measured-tier proved-conditional → weak-tier derived). **No single place in the note states the terminal status**; it must be assembled from §2.10, Annex #1 and Annex #6. **Annex #6's boxed stack entry is the closest thing and this shard treats it as TERMINAL.**
5. **`.28`:** the SPAN-M measurement gap (606 of 934) was CREATED by the r1 repair widening the statement, and is “the one place r1 leaves a measurement owed”. **It remains owed at HEAD** — §9.4's closing line (shard 3) confirms “the non-integral residue JC-BOX-8(i) is still untouched by every runner”.
6. **`.30`:** MT3's 9 escapes are “single-pair, all prime-residue-field rows `|K| ∈ {3,5}`, planted rescaling coincides with a lawful constant”. **The escape mechanism is understood and disclosed**, but the tooth's resolution on small residue fields is permanently limited.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or explicitly `[ASSEMBLED]`. **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** Truncations are marked `…`; they are used in `.16`, `.22`, `.24`, `.28`, `.30`, `.32`, `.41`, `.43`, and in each case the omitted span is quoted at another unit or is a repeated cross-reference.
- **★ W-9's face box (`.36`) is quoted BYTE-VERBATIM AND UNTRUNCATED**, per the charge's special-care direction, and its source range was independently re-read at HEAD to confirm WELDZERO's citation (L1777–1788) is exact.
- **Strike markup is preserved.** In this range the struck text is repeatedly a FALSE MATHEMATICAL STATEMENT the note keeps on the record: `(COORD)` (`.11`), the over-quantified kernel claim (`.10`), `(MULT)` (`.18`), the two unproved identifications (`.33`), the false (CYC) trigger (`.41`), the honest rider's predecessor (`.29`).
- **Eleven displays are DOUBLE-EMITTED** (rule 14): the W-6 clause list, the two (DMULT) tiers, the (G5-i)/(G5-ii) transport, JC-GAUGE's three-part conclusion, the W-7 obligations, **W-9's four supply clauses with a per-clause consumer column**, JC-CYC's five clauses, §7's eleven genres, §3.4's three census genres, `.21`'s five consumers, `.15`'s (COORD-B) two clauses.
- **MANDATORY ARITHMETIC AUDITS performed on ten count surfaces** (`.21`, `.24`, `.26`, `.28`, `.30`, `.36`, `.40`, `.41`, `.43`, and the JC7 counts at `.36`). **Every one is internally consistent** — 5 consumers; 138/215/73 of 669; 27 = 29 − 2; 328 + 606 = 934; 197 + 9 = 206; 14 + 6 + 9 = 29; 6 cyclic accounted 1+4+1; 13 named counterexamples; 2 off-collapse; 2 + 27 = 29. **No discrepancy found in this shard.**
- **19 external XREF designations, every one grep-verified with a count ≥ 1 recorded inline and in §3.1** (four are file-existence pins).
- **PIN VERIFICATION:** the FGMN PDF md5 **EXACT at HEAD**; six FGMN layout line pins re-read EXACT (525, 862, 1028, 1030, 1136, 1151); the commit/md5/artifact census is shard 1 §3.1 (**23/23, 2/2, 12/12, 6/6**).
- **CITE-SCOPE handled per resolution rule 8:** the two Q7 H6 rows and their NS-9/NS-10 resolutions (**both COVERS-ALL-O; NS-10 calls the flag “a pasting artefact, not a real gap”**) are recorded in full at shard 1 `.43` and referenced here at `.08` (Cor 2.7) and `.16`/`.27` (Thm 4.2). **Recorded, not applied.**
- Status and mathematical content are kept as distinct predicates: the four GRADE blocks are conditionality statements read against §0's stack; the acceptance status is Annex #7's; the mathematics is the clauses'.
- **Honest limitation of this shard:** all five annex corrections and the whole conditionality stack live in other shards. Every affected unit quotes the governing corrective text verbatim, so shard 2 is self-contained as a *reading*, but the merge run must install the seven edges listed in §7 — above all **W-9's per-clause consumer table** and **Annex #4's replacement route onto `.32`**.

EFF-GRTJC-s2of3 COMPILED: 43 statements / 19 xrefs verified / 5 open calls
