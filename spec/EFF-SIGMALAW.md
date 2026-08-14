# EFF-SIGMALAW — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` (792 lines / 44,998 bytes).

**HEAD blob hash:** `5df2ed1bc0f91aa9fefb8b9db2a0c1ba7b016320`. Whole-file md5 at compile time: `e00c0b294a26b353b83bbdfeabe7aef2`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28. Full compilation, unsharded (45 KB, the smallest note in the queue).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

### Effective-text rule

The freeze is stated at the acceptance record (L623–624):

> “**FREEZE-CONVENTION STAMP**: the accepted text is the post-r1 body,
> md5 a50d3d5f, byte-frozen since 6b24942; dated appends only hereafter.”

**PIN VERIFIED and localized:** the md5 of the file's first **604** lines begins `a50d3d5f` — a **unique hit** over all line boundaries ✓; `6b24942` is a commit ✓.

**Therefore the effective text is: the frozen post-r1 body L1–604 read with its inline `[r1]` bracket repairs applied in place, then the dated appends — the ACCEPTANCE RECORD with its FREEZE stamp and WHAT-IS-ACCEPTED clause, and the 2026-08-12 sol C9/E10 annex fold with its one RESOLVED-ALREADY disposition and four verbatim repairs.**

### FREEZE PREDICATES (rule 21 — two)

**FREEZE-1 — text freeze.** md5 prefix `a50d3d5f` at line **604**, unique ✓; anchor commit `6b24942` ✓.

**FREEZE-2 — instrument freeze.** §6's two-commit seal on `verification/openmath/sigmalaw_checks.py` (EXISTS ✓), sealed at `8064ae3` ✓ with verdict `59c1ff2` ✓. **Disposition: `UNPINNED-VALUE`** — no artifact md5 is displayed.

### Supersession chains

`[TABLE]`

| # | Target (frozen text) | Layer 1 (`[r1]`) | Layer 2 (acceptance) | Layer 3 (E10 fold, 08-12) | TERMINAL |
|---|---|---|---|---|---|
| C-1 | The boxed Σ-LAW's map `σ′` (`z_q ↦ θ_q z_q`) | — | — | — | **the note's own VERDICT: `σ′` is the WRONG map; the true map is `Σ_m` via `ξ_q`** (`.02`) — a *composition-time* correction of the box it discharges |
| C-2 | SL-C1's multiplicativity hedge (“(SC)-type covariance when x is an ε-monomial-times-class”) | **`[r1]` PE1 F1: INSUFFICIENT; re-pointed at (EC-q), the automorphism property** | — | **E10 #5: the dangling ellipsis replaced by a complete derivation** | **E10 #5** (`.16`) |
| C-3 | `ξ₁` (used, never defined) | — | — | **E10 #2: `ξ₁ := 1`, forced by `Σ₁ = id`** | **E10 #2** (`.13`) |
| C-4 | §5 SEP-A's `supp` notation | — | — | **E10 #3: notation corrected** | **E10 #3** (`.14`) |
| C-5 | §8's proposed-annex machine counts | `[r1, PE1 F2]` diagnoses the contamination and notes an orchestrator action “owed” | — | **E10 #4: the owed correction executed — leak-free totals displayed** | **E10 #4** (`.15`) |
| C-6 | THEOREM SL-1's isolated `(VD-q)` quantifier | — | **the WHAT-IS-ACCEPTED re-display at shared-below scope** | **E10 #1: RESOLVED-ALREADY by that re-display** | **the acceptance re-display** (`.11`, `.12`) |
| C-7 | The note's grade | three passes, one repair | **ACCEPTED 2/2** | ledger **CERTIFIED** | **ACCEPTANCE + ledger row 27** |

**A distinctive shape.** **C-6 is the queue's clearest case of an acceptance record functioning as a statement re-display** — the E10 fold finds a GAP in the frozen theorem's quantifier and then rules it **RESOLVED-ALREADY** because the acceptance append had already re-displayed the theorem at its proved scope. **The acceptance record pre-empted a later finding.** Compare `spec/EFF-WELDMASTER.md` `.24` (F-3, resolved by the acceptance record's own scope qualifier) — **the same mechanism, in two notes.**

### Scope of record — three-predicate split

#### A. Supply set

**One theorem (SL-1), two lemmas (SL-L1, SL-L2), two corollaries (SL-C1, SL-C2), plus the constructed separators of §5 and the sealed battery.** The note's own verdict (`.02`): the Σ-LAW is **PROVED at attempt grade** in a **sharper per-coordinate form** than the box asked for, **with two corrections to the boxed statement, both derived and both machine-witnessed by constructed non-involution separators.**

#### B. Consumption / append-protocol scope

**§8 is a proposed annex text** for the GRTW2 §5.2 / OPEN2ATTACK §6 fold — **offered, not landed** (the note is an “orchestrator action”). E10 #4 corrects the annex's machine counts **for future transcription**, which is itself evidence the annex had not landed at the fold. See OPEN-CALL 1.

#### C. Inbound corrections RECEIVED

PE1 (0C+1G+2m; **the verifier DERIVED the true (EC-q) law** — the substantive repair), PE2 CLEAN, PE3 CLEAN, then the sol C9 ratification (RATIFIED-WITH-ANNEX: 1 GAP + 4 MINORs) and the E10 fold (1 RESOLVED-ALREADY + 4 REAL).

### Resolution rules applied

1. `[r1]` brackets are in the frozen body and apply in place.
2. Appends apply in order: ACCEPTANCE → the E10 fold's five items.
3. **A “verbatim-ready append” is effective text.** All four E10 repairs are displayed as verbatim-ready appends and are compiled as governing.
4. **The note's own VERDICT block corrects the box it discharges** — compiled at `.02` as a composition-time correction, not a later supersession.
5. Out-of-note material (GRTW2, OPEN2ATTACK, the ledger) resolves and verifies only.

### Quotation discipline

Every CANONICAL STATEMENT is verbatim or `[ASSEMBLED]`. Indented displays are reproduced with line structure. **Rule 14 is not triggered** — no fenced ASCII table (checked, not skipped).

---

## 2. NON-IMPORTS

**N-1 — the converse is not proved.** WHAT IS ACCEPTED: “THEOREM OPEN-2a-Σ's firing (the (OPEN-2a) forward direction at every m ≥ 2, given OA-L1–L4) + COROLLARIES, at the displayed boxes; **the converse's UNPROVED status unchanged**.”

**N-2 — OA-M1 is not consumed.** SL-C2's proof: “Σ_m is a K₀-linear coordinate BIJECTION fixing 1 — nonzero characters coordinatewise; **no automorphism property needed, OA-M1 not consumed**”. And `[r1]` F1 explains why OA-M1 could never have served: “OA-M1 never met this because σ′ is coefficientwise-trivial below, while the composite Σ_m at m ≥ 3 is not”.

**N-3 — the shared-below premise is a hypothesis, not a fact about all configurations.** E10 #1: “The proposed off-perimeter counter-configuration is expressly the note's eigen-MISMATCH control, which ‘fails m = 2 byte-equality, 1/1’; it therefore **violates the accepted theorem's shared-below premise**.”

**N-4 — the contaminated totals are not the evidence.** E10 #4: “The historical machine output remains preserved as printed, but **the corrected leak-free figures above are the evidence to be quoted**.”

---

## 3. Statement inventory

IDs `EFF.SIGMALAW.01`–`.18`.

### EFF.SIGMALAW.01  [record]

**CANONICAL STATEMENT** — the Unit block (L3–25): the note is the “Σ-LAW (the one displayed lemma of the (Σ-LAW box))”, with machine bracket `verification/openmath/sigmalaw_checks.py`.

**DERIVATION.** [RECORD]. **SERIES:** ARC member 1 (`.01` → `.11` ACCEPTANCE → `.18` ledger).

**CONDITIONALITY.** Grade at HEAD: **ACCEPTED 2/2** and ledger-**CERTIFIED**. **XREF.** `verification/openmath/sigmalaw_checks.py` ✓.

---

### EFF.SIGMALAW.02  [record]

**CANONICAL STATEMENT** (verbatim, L26–40, the VERDICT UP FRONT with its first correction). FORM: bold-headed paragraph plus a numbered list.

> “**VERDICT UP FRONT.** The Σ-LAW is **PROVED at attempt grade** — in the
> sharper per-coordinate form Prnt_j(A) = u_j·Σ_m(R_m v(A)) with an EXPLICIT
> slot constant u_j and an EXPLICIT coordinate map Σ_m — for EVERY on-line
> level-m slot object at every shared-below junction at every m ≥ 1, gap
> rows included with no correction term. Two corrections to the boxed
> statement, both derived and both machine-witnessed by constructed
> non-involution separators:
>
> 1. **The map is not the bare interior twist.** The boxed σ′ (the runner's
>    `sigma_twist`: z_q ↦ θ_q z_q, θ_q = z_{q−1}^{A_{q−1}e_{q−1}}) is the
>    WRONG map: the true map Σ_m twists each letter by the **§3.4 FORMULA
>    character** ξ_q = χ_{q−1}^{γ_q}·z_{q−1}^{−e_{q−1}A_{q−1}} — i.e.
>    θ_q^{−1} at q = 2, and θ_q^{−1}·(the χ-chain correction χ_{q−1}^{γ_q})
>    at q ≥ 3. On every involution geography (ALL δ ≠ 1 rows of the sealed
>    468-row battery) Σ_m and σ′^{±1} coincide — which is exactly why the
>    [boxed form survived] …”

**DERIVATION.** [RECORD of the note's own headline], with the correction derived in §3 and witnessed in §5.

**CONDITIONALITY — this is the note's defining move.** It **discharges a box and corrects the box's own displayed map in the same act.** The explanation for why the wrong map survived is quantified: on **every** involution geography the two maps coincide, and the sealed 468-row battery had only such rows. **Independently confirmed by the note's own reconciliation census** (`.10`): `SL-INVREC = 218/218` OA-battery `δ ≠ 1` slot-samples sit where the two maps agree ✓.

**Arithmetic audit of the map relation.** At `q = 2`, `χ_1 = 1` (the base), so `ξ_2 = z_1^{−e_1A_1} = θ_2^{−1}` ✓ **exactly the note's claim**. At `q ≥ 3`, `ξ_q = θ_q^{−1}·χ_{q−1}^{γ_q}` ✓ — the χ-chain correction is precisely the extra factor.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — §3.4's formula character ✓.

---

### EFF.SIGMALAW.03  [definition]

**CANONICAL STATEMENT** — §1's objects (L58–119): the print slot evaluator (`Def-t(i)` + `Def-rescoeff`), the two normalized evaluators `H_q`/`P_q`, and the ledger characters `ξ_q`, `χ_q`, `U_q`, `Λ_q`, “all §3.4 objects, **used as DEFINITIONS**”.

**DERIVATION.** [DEFINITIONAL / IMPORTED], code-pinned to OPEN2ATTACK §1 notation.

**CONDITIONALITY.** **`ξ₁` is used but never defined in the frozen text** — supplied by **E10 #2** (`.13`) as `ξ₁ := 1`. The characters being “used as DEFINITIONS” rather than derived is what makes the ledger identity a statement about the harness's own objects.

**XREF.** `GRTW2_PROOF_2026-08-08.md` §3.4 ✓.

---

### EFF.SIGMALAW.04  [lemma]

**CANONICAL STATEMENT** (verbatim, §2 L122–133 — LEMMA SL-L1). FORM: bold-headed lemma with two indented recursions.

> “**LEMMA SL-L1.** For every on-line level-q object A at weight β (q ≥ 1),
> with digits A_ν (the Φ_{q−1}-dev digits at abscissa a_ν = s + νe_{q−1}
> that are on-line at exact weight w_ν = (β − a_νγ_q)/e_{q−1}; arbitrary
> support, gaps allowed):
>
>     (H-REC)  H_q(A) = Σ_ν ε_{q−1}(w_ν) · H_{q−1}(A_ν) · z_q^ν ,
>     (P-REC)  P_q(A) = ε_q(β) · Σ_ν z_{q−1}^{−a_ν·A_{q−1}} · P_{q−1}(A_ν) · z_q^ν ,
>
> with P₀ = H₀ (res at exact weight) and, in (P-REC) at q = 1, the twist
> factor absent (order-one rescoeff has no twist): P₁(A) = ε₁(β)·H₁(A) —
> LEMMA W2-L3 verbatim. **The gap terms ν₀ do not appear in either
> recursion**: they cancel identically inside P_q at every node.”

**DERIVATION.** §2's proof: “(H-REC) is the read recursion (GRTW2 (HR-REC) mechanics …)”.

**CONDITIONALITY — the gap clause is the load-bearing one.** “**The gap terms ν₀ do not appear in either recursion**: they cancel identically inside P_q at every node.” **This is what lets the theorem cover “gap rows included with no correction term”** (`.02`), and it is machine-checked separately as **SL-GAP** (`.10`: 680 leak-free gap-slot samples across 340 gap slots, every one conforming).

**Arithmetic audit.** `a_ν = s + νe_{q−1}` and `w_ν = (β − a_νγ_q)/e_{q−1}` ✓ — the standard on-line exact-weight parametrization; the `z_{q−1}^{−a_ν A_{q−1}}` twist in (P-REC) is the per-abscissa character of the print side ✓, matching `.02`'s `θ_q` up to the `ν`-linear part.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — W2-L3, (HR-REC) ✓.

---

### EFF.SIGMALAW.05  [theorem]

**CANONICAL STATEMENT** (verbatim, §3 L166–179 — THEOREM SL-1). FORM: bold-headed theorem with two displays.

> “**THEOREM SL-1.** For every on-line level-q object A at weight β, q ≥ 1:
>
>     (VD-q)      P_q(A) = ε_q(β) · U_q(β) · Σ_q( H_q(A) ) .
>
> Consequently, at a shared-below junction at level m+1, for every
> supported slot j and EVERY on-line level-m object A at weight β_j (in
> particular both builders' slot digits C_j, P_j):
>
>     (Σ-LEDGER)  Prnt_j(A) = u_j · Σ_m( R_m v(A) ),
>     u_j = z_m^{−k_j·A_m} · ε_m(β_j) · U_m(β_j)     — slot-constant.”

**DERIVATION** (verbatim, the induction's decisive step, L181–195): substitute `(VD-(q−1))` into `(P-REC)` per digit, expand `ε_q(β)U_q(β)Σ_q(H_q(A))` over `(H-REC)` coordinates, and use faithfulness of the coordinates `ν < g_{q−1}` to reduce to a per-`ν` identity:

>     (MATCH)   U_q(β) = z_{q−1}^{−sA'} · [ z_{q−1}^{−eA'} ξ_q^{−1} ]^ν · Λ_{q−1}(w_ν) .

**Mathematical audit of the reduction.** The step “The coordinates `ν < g_{q−1}` are faithful, so equality per `ν` is required and sufficient” ✓ — this is what turns a ring identity into a family of scalar identities, and it is why the gauge ratio `Λ` is the right object to isolate. **The `(MATCH)` display's `ν`-dependence must vanish for `U_q(β)` to be well defined**, which is exactly what `.06`'s `Λ_q(w) = χ_q^{−w}` supplies. **The proof's architecture is therefore: reduce to (MATCH), then prove the gauge-ratio law makes (MATCH) `ν`-free.** Confirmed by inspection ✓.

**CONDITIONALITY — the scope, and the E10 GAP.** The isolated `(VD-q)` display “is broader-looking than its proof” (E10 #1). **The governing scope is the acceptance record's re-display**: “every on-line level-m object at every **shared-below junction**, every m ≥ 1, via the (VD-q)+(EC-q)+(SC-q) ladder”. **E10 ruled the GAP RESOLVED-ALREADY** on exactly that ground (`.12`).

**XREF.** `OPEN2ATTACK` §1 — cited; `GRTW2_PROOF_2026-08-08.md` ✓.

---

### EFF.SIGMALAW.06  [lemma]

**CANONICAL STATEMENT** (verbatim, §3 L197–200 — LEMMA SL-L2). FORM: bold-headed lemma.

> “**LEMMA SL-L2 (the gauge-ratio law).** Λ_q(w) = χ_q^{−w} for every q ≥ 1
> and every weight w in the level-q grid. *Proof, induction riding the main
> one.* q = 1: Λ₁ = ε₁U₁/Σ₁(ε₁) = 1 = χ₁^{−w}. Step: with U_q as in
> (U-REC) and ε_q(w) = z_q^{E(w)}, E(w) = (s(w) − ℓ_{q−1}w)/e_{q−1}, and …”

**DERIVATION.** An induction “riding the main one” — i.e. SL-1 and SL-L2 are proved by a **simultaneous** induction.

**CONDITIONALITY.** **PE3 “re-derived [SL-L2] line-by-line + machine-keyed BY NAME for the first time”** (`.11`) — so the note's most intricate lemma acquired both an independent re-derivation and its own machine key only at the final pass. Recorded.

**Compiler note on the simultaneous induction.** The note is explicit (“riding the main one”), which is the honest form; `spec/EFF-HE7-s1of3.md`'s OPEN-CALL 3 records a case elsewhere in the corpus where a mutual induction was asserted in a parenthesis rather than displayed. **Here the interleaving is stated at the point of use.**

**XREF.** none new.

---

### EFF.SIGMALAW.07  [lemma]

**CANONICAL STATEMENT** — §3's REMARK, the eigen-coefficient law `(EC-q)`: `ψ_{q−1} ↦ ξ_q^{g_{q−1}}·ψ_{q−1}`, establishing that `Σ_m` **preserves the relation ideal at every interior level `2 ≤ q ≤ m`** and is therefore a ring automorphism.

**DERIVATION.** Derived at PE1 — the acceptance record records the provenance: “PE1 (0C+1G+2m, 9b0117d — the GAP was the wrap display; **the verifier DERIVED the true (EC-q) law**) → r1 (6b24942, the derivation transcribed)”.

**CONDITIONALITY — this is the note's load-bearing repair.** `(EC-q)` is what makes `.08`'s multiplicativity step valid, and it **came from the hostile pass, not the author**. `[r1]` PE1 F1 states what it replaced: “The sealed hedge — ‘(SC)-type covariance when x is an ε-monomial-times-class …’ — was **INSUFFICIENT as stated**: the step needs `Σ_m(ρ·x) = Σ_m(ρ)Σ_m(x)` with `ρ` an ARBITRARY unit, i.e. the automorphism property, i.e. ideal preservation = exactly (EC)”. **PE2 then “independent[ly] (EC-q) re-derive[d] … with the 3-clause ladder proved well-founded”** ✓ (`.11`).

**AUDIT disposition (rule 27).** `in-house hostile pass` — and an unusually generative one: the verifier supplied the missing law rather than only naming the gap.

**XREF.** none new.

---

### EFF.SIGMALAW.08  [corollary]

**CANONICAL STATEMENT** (verbatim, §4 L332–334 plus the `[r1]`-repaired proof, L335–359 — COROLLARY SL-C1). FORM: bold-headed corollary.

> “**COROLLARY SL-C1 (the Σ-LAW, map and sign pinned).** At every
> shared-below junction at level m+1, every j ∈ supp:
>
>     δ_j = ρ_j / Σ_m(ρ_j) .”

with the `[r1]` PE1 F1 repair verbatim:

> “this holds because **Σ_m ∈ Aut(K_m)**: the eigen-coefficient
> law (EC-q) of §3's REMARK preserves the relation ideal at every
> interior level 2 ≤ q ≤ m (ψ_{q−1} ↦ ξ_q^{g_{q−1}}·ψ_{q−1}), so the
> composite Σ_m is a ring automorphism and Σ_m(y) = Σ_m(ρ_j)·Σ_m(x)
> outright [r1, PE1 F1: re-pointed at the derived law. The sealed hedge …
> was INSUFFICIENT as stated …]”

**⚠ SUPERSEDED (the proof's presentation).** The frozen proof contains “a dangling ellipsis” (`δ_j = ρ_j·Σ_m(x/y) = ρ_j·Σ_m(ρ_j^{−1}·...)` followed by a restart). **E10 #5** (`.16`) replaces it with a complete four-line derivation. **CHAIN:** sealed hedge → `[r1]` (EC-q) re-pointing → E10 #5 (the calculation displayed without omission). **TERMINAL: E10 #5.** **The conclusion `δ_j = ρ_j/Σ_m(ρ_j)` never moves.**

**Mandatory arithmetic audit (rule 22) — E10 #5's derivation re-checked.** With `x := R_m v(C_j)`, `y := R_m v(P_j) = ρ_j x`: by `(Σ-LEDGER)`, `Prnt_j(C_j) = u_jΣ_m(x)` and `Prnt_j(P_j) = u_jΣ_m(y)` ✓. Then `δ_j = [Prnt_j(C_j)/x]/[Prnt_j(P_j)/y] = [u_jΣ_m(x)/x]/[u_jΣ_m(y)/y] = (y/x)·Σ_m(x)/Σ_m(y)` ✓ — **`u_j` cancels, which is the point of its being slot-constant.** With `Σ_m` a ring automorphism, `Σ_m(y) = Σ_m(ρ_j)Σ_m(x)` ✓, so `δ_j = ρ_j·Σ_m(x)/(Σ_m(ρ_j)Σ_m(x)) = ρ_j/Σ_m(ρ_j)` ✓ **exactly, with no omitted term.**

**CONDITIONALITY.** Attempt grade at composition; **the multiplicativity step rides `(EC-q)`, “discharged on-perimeter in §3's REMARK”** — so SL-C1 inherits the shared-below perimeter. Machine: **SL-DELTA keys the element identity directly on every walked row** ✓.

**XREF.** `OPEN2ATTACK` — OA-L2, Thm-`phir` = OA-PHIR ✓ cited.

---

### EFF.SIGMALAW.09  [corollary]

**CANONICAL STATEMENT** (verbatim, §4 L361–369 — COROLLARY SL-C2). FORM: bold-headed corollary with proof.

> “**COROLLARY SL-C2 (THEOREM OPEN-2a-Σ, now unconditional on its Σ-leg).**
> At every shared-below junction at level m+1, m ≥ 1: strict ⟹ byte-equal;
> hence recorded ξ = 1 ⟹ byte-equal, under EVERY selection rule. *Proof.*
> Strict ⟹ δ_j = ρ_j on supp (OA-L3) ⟹ Σ_m(ρ_j) = 1 = Σ_m(1) (SL-C1) ⟹
> ρ_j = 1 (Σ_m is a K₀-linear coordinate BIJECTION fixing 1 — nonzero
> characters coordinatewise; no automorphism property needed, OA-M1 not
> consumed) ⟹ byte-equal (OA-L4). ∎ Grades consumed: OA-L1/L2/L3/L4 at
> attempt grade (OPEN2ATTACK §1), SL-1/SL-C1 at attempt grade.”

**DERIVATION.** A four-step chain, each step citing its supplier.

**Mathematical audit.** `strict ⟹ δ_j = ρ_j` (OA-L3); with SL-C1's `δ_j = ρ_j/Σ_m(ρ_j)` this forces `Σ_m(ρ_j) = 1` ✓; and `Σ_m(1) = 1` since `Σ_m` fixes 1 ✓; **injectivity then gives `ρ_j = 1`** ✓. **Note the economy the note flags:** this step needs only that `Σ_m` is an injective `K₀`-linear map fixing 1 — **not** the automorphism property — so SL-C2 does **not** inherit `(EC-q)`'s perimeter through this route ✓. **A genuinely weaker hypothesis for the weaker conclusion**, correctly identified.

**CONDITIONALITY.** The **converse remains UNPROVED** (N-1). Consumes OA-L1–L4 at attempt grade.

**XREF.** `OPEN2ATTACK` — OA-L1/L2/L3/L4, OA-M1 ✓ cited.

---

### EFF.SIGMALAW.10  [run-record]

**CANONICAL STATEMENT** (verbatim, §6R L485–503). FORM: bold-headed paragraph with a family table in prose.

> “**Sealed battery (`sigmalaw_checks.py`, run once post-seal, exit 0,
> 18.5 s, 6,970 samples): 539 towers built (389 OA-battery + 96 SEPA + 54
> SEPB, 0 rejects), 1,217 junction rows = 1,211 walked (539 m=1 + 527 m=2
> + 145 m=3) + 6 SKIP (the roster's above-twist rows). ALL preregistered
> families GREEN; all six teeth rows CAUGHT.** Family table (pred/obs/
> samples): SL-VDM 0/0 (2,854 …) · SL-DELTA 0/0 (1,427) · SL-GAP 0/0 (688
> gap-slot samples; 340 gap slots across 317 gap rows …) ·
> SL-PHIR 0/0 (1,427) · TEETH-US caught 2/2 · TEETH-SB caught 2/2 ·
> TEETH-PR caught 2/2. Separator censuses: **SL-SEP2 = 96 rows (predicted
> ≥ 8)** … **SL-SEP3 = 27 rows (predicted ≥ 6)** … Reconciliation:
> SL-INVREC = 221 δ ≠ 1 slot-samples with Σ_m(ρ) = `sigma_twist`(ρ), of
> which 218 on the OA-battery geography …”

**DERIVATION.** [RECORD of an executed instrument].

**Mandatory arithmetic audit (rule 22).** Towers `389 + 96 + 54 = 539` ✓. Rows `1,211 + 6 = 1,217` ✓, and the walked split `539 + 527 + 145 = 1,211` ✓. **Both separator censuses far exceed their predictions** (`96 ≥ 8`, `27 ≥ 6`) ✓. **The printed family totals are superseded by E10 #4's leak-free figures** (`.15`), whose subtractions this compilation verified: `2,854 − 26 = 2,828` ✓, `1,427 − 13 = 1,414` ✓ (twice), `688 − 8 = 680` ✓, and `221 − 3 = 218` ✓.

**TEETH disposition (rule 20).** `signed vacuity disclosure` — the note's own `[r1, PE1 F2]` bracket diagnoses that the printed totals include **tooth-run leakage**, and E10 #4 then executes the owed correction. **The censuses that are already exact are named as such** (“Because ROWS was restored around tooth runs, the SEP2 = 96, SEP3 = 27, and 340-gap-slot censuses are already exact”) — a precision most notes would not attempt.

**CONDITIONALITY.** **SL-INVREC is the decisive reconciliation**: `218/218` of the OA-battery's `δ ≠ 1` samples sit where `Σ_m` and `sigma_twist` **coincide** — “the sealed unit's ENTIRE `δ ≠ 1` record sits where the two maps coincide”, which is why the wrong map survived (`.02`) ✓.

**XREF.** `verification/openmath/sigmalaw_checks.py` ✓.

---

### EFF.SIGMALAW.11  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L608–636). FORM: starred heading plus three bold-headed paragraphs.

> “**THIS NOTE IS ACCEPTED at 2/2** — PE2 (6e57e03, CLEAN on the note
> text; independent (EC-q) re-derivation with the 3-clause ladder proved
> well-founded; 16 own doubly-twisted towers incl. the k≡3 (mod 4)
> contrapositive; order-7 fresh route) and PE3 (165ca12, CLEAN; SL-L2
> re-derived line-by-line + machine-keyed BY NAME for the first time;
> the all-three-u_j-factors junction constructed; own census walk
> 1,211 rows leak-free; mutant audit 13/13 caught; fresh route = 𝔽₂₇
> chamber with ord-13 invisible twist, 0 violations). Full arc: composed
> → seal 8064ae3 / verdict 59c1ff2 → PE1 (0C+1G+2m, 9b0117d — the GAP
> was the wrap display; the verifier DERIVED the true (EC-q) law) → r1
> (6b24942, the derivation transcribed) → PE2 CLEAN-on-note → PE3
> CLEAN. Three passes, one substantive repair.”

**DERIVATION.** [RECORD of an acceptance]. **SERIES:** member 2 — TERMINAL for the counter.

**CONDITIONALITY — two decorrelation legs worth naming.** PE2 **independently re-derived `(EC-q)`** and proved the 3-clause ladder well-founded; PE3 **re-derived SL-L2 line-by-line** and walked its own 1,211-row census **leak-free** — i.e. PE3's own walk anticipated exactly the leakage E10 #4 later corrected in the *annex text* ✓. **The shortest arc in queue 8b (three passes, one repair) with two of the strongest independent re-derivations.**

**PIN VERIFICATION.** `6e57e03` ✓, `165ca12` ✓, `8064ae3` ✓, `59c1ff2` ✓, `9b0117d` ✓, `6b24942` ✓ — **six of six.**

**XREF.** none new.

---

### EFF.SIGMALAW.12  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L626–635 — WHAT IS ACCEPTED). FORM: bold-headed paragraph. **This is the governing scope re-display of THEOREM SL-1.**

> “**WHAT IS ACCEPTED**: THEOREM SL-1 (the Σ-LAW: Prnt_j(A) =
> u_j·Σ_m(R_m v(A)) with closed-form slot constant, every on-line
> level-m object at every shared-below junction, every m ≥ 1, via the
> (VD-q)+(EC-q)+(SC-q) ladder — Σ_m the ξ-formula composite twist, both
> bare-θ variants refuted by construction) + THEOREM OPEN-2a-Σ's firing
> (the (OPEN-2a) forward direction at every m ≥ 2, given OA-L1–L4) +
> COROLLARIES, at the displayed boxes; the converse's UNPROVED status
> unchanged.”

**DERIVATION.** [RECORD of an acceptance's scope clause].

**CONDITIONALITY — and its later role.** **E10 #1 rules the SL-1 quantifier GAP RESOLVED-ALREADY precisely because this clause exists**, quoting it verbatim and adding: “Under the delegated end-to-end-proof criterion, **the acceptance record is already the correct re-display. No further repair is required.**” **So this paragraph did the work of a statement correction four days before the finding arrived.** The clause also carries three fences a chapter cut needs: the shared-below premise, “both bare-θ variants refuted by construction”, and **the converse's UNPROVED status**.

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 27 ✓.

---

### EFF.SIGMALAW.13  [changes-record]

**CANONICAL STATEMENT** (verbatim, E10 #2, L671–688). FORM: `###`-headed finding plus a verbatim-ready append.

> “### 2. REAL — ξ₁ is undefined
>
> **[APPEND 2026-08-12 — base-character convention.]** Extend the ledger-character definitions in §1 by
>
>     ξ₁ := 1.
>
> This convention is forced by Σ₁ = id and makes the displayed base clause (SC-1) literal: for every y ∈ K₁ and every grid weight w,
>
>     Σ₁(ε₁(w)·y)
>       = ε₁(w)·y
>       = ε₁(w)·ξ₁^{E(w)}·Σ₁(y),
>
> because Σ₁ = id and ξ₁^{E(w)} = 1. Thus (SC-1) is the stated trivial base of the (VD-q)+(EC-q)+(SC-q) ladder. No higher-level definition or theorem statement changes.”

**DERIVATION.** Forced by `Σ₁ = id` — a one-line derivation.

**Audit.** With `Σ₁ = id`, `(SC-1)` reads `ε₁(w)y = ε₁(w)ξ₁^{E(w)}y`, which holds for all `y` iff `ξ₁^{E(w)} = 1` for all grid `w` — and `ξ₁ := 1` is the canonical choice ✓. **The convention is forced, not stipulated**, which is why the sweep can say “No higher-level definition or theorem statement changes.”

**SUPERSESSION KIND:** `inventory completion` — a missing definition supplied. **TARGETS:** `.03`.

**XREF.** none.

---

### EFF.SIGMALAW.14  [changes-record]

**CANONICAL STATEMENT** (verbatim, E10 #3, L689–708 head). FORM: `###`-headed finding plus a verbatim-ready append.

> “### 3. REAL — SEP-A uses “supp” inconsistently
>
> **[APPEND 2026-08-12 — SEP-A support notation correction.]** In §5, SEP-A, replace
>
>     ψ₁ = y⁴ + z₁^k (supp {0,4} ≡ 0 mod 4)
>
> by [the corrected support statement]”

**DERIVATION.** A notation repair inside the constructed-separator section.

**CONDITIONALITY.** The E10 provenance records the orchestrator's check: “the SEP-A convention re-checked (monic exponent `j = g₁ = 4` excluded, `ξ₂⁴ = 1` from `ord(ξ₂) = 4`)” — **so the correction is that the monic top exponent must be excluded from the support convention**, and the arithmetic `ξ₂^{g₁} = ξ₂⁴ = 1` at `ord(ξ₂) = 4` ✓ confirms the separator still separates. **A notation defect with no mathematical consequence, in the section whose whole purpose is constructing witnesses.**

**SUPERSESSION KIND:** `wording-rider`. **TARGETS:** §5's SEP-A.

**XREF.** none.

---

### EFF.SIGMALAW.15  [changes-record]

**CANONICAL STATEMENT** (verbatim, E10 #4, L709–742). FORM: `###`-headed finding plus a verbatim-ready append with a subtraction display.

> “### 4. REAL — the transcribable annex still contains contaminated totals
>
> The adjacent `[r1, PE1 F2]` bracket diagnoses and corrects the counts, but it explicitly says: “mirroring this caveat there is an orchestrator action ... owed”. Therefore the proposed annex itself remains unrepaired for future transcription.
>
> **[APPEND 2026-08-12 — §8 annex machine-count correction.]** For every future transcription of the proposed annex, supersede its machine-count sentence by:
>
> > Machine: 1,211 walked junction rows (539 towers: the full
> > OPEN2ATTACK battery reproduced + 150 constructed separator towers).
> > The leak-free battery totals are SL-VDM 2,828 / SL-DELTA 1,414 /
> > SL-PHIR 1,414 / SL-GAP 680 samples (340 gap slots), with 0 violations
> > and exit 0; all three teeth were caught 2/2 each. These figures follow
> > by removing the exactly measured tooth-run leakage from the runner's
> > printed totals:
> >
> >     2,854 − 26 = 2,828,
> >     1,427 − 13 = 1,414,
> >     1,427 − 13 = 1,414,
> >       688 −  8 =   680.
> >
> > Because ROWS was restored around tooth runs, the SEP2 = 96, SEP3 = 27,
> > and 340-gap-slot censuses are already exact. The genuine reconciliation
> > census is SL-INVREC = 218/218 OA-battery δ ≠ 1 slot-samples; the printed
> > 221 included three TEETH-PR mutation artifacts.
>
> The historical machine output remains preserved as printed, but the corrected leak-free figures above are the evidence to be quoted in the annex.”

**DERIVATION.** Subtraction of exactly measured tooth-run leakage from printed totals.

**Mandatory arithmetic audit (rule 22) — all five subtractions and one cross-check.** `2,854 − 26 = 2,828` ✓; `1,427 − 13 = 1,414` ✓; `1,427 − 13 = 1,414` ✓; `688 − 8 = 680` ✓; `221 − 3 = 218` ✓. **Cross-check on the tower count:** the append says “539 towers: the full OPEN2ATTACK battery reproduced + **150** constructed separator towers”, and `.10` gives `389 OA + 96 SEPA + 54 SEPB`; `96 + 54 = 150` ✓ and `389 + 150 = 539` ✓ — **the two decompositions agree exactly.** **Every figure in this correction reproduces.**

**SUPERSESSION KIND:** `counter re-reading`. **TARGETS:** §8's proposed annex text (`.17`) — **and, by the note's own framing, only for FUTURE transcription**, since the annex had not landed.

**CONDITIONALITY.** “only evidentiary bookkeeping changes. SL-1, SL-C1, SL-C2, the separator results, the zero-violation conclusion, and the acceptance grade **do not depend on the contaminated totals**.” ✓ — confirmed: none of the theorem statements cites a sample count.

**Compiler note.** **An owed orchestrator action, named in a `[r1]` bracket and executed by an external certification pass four days later.** The `[r1]` bracket knew the annex was contaminated; E10 is what actually repaired it. Recorded as the queue's clearest instance of an explicitly-owed item being closed by a decorrelated read rather than by its owner.

**XREF.** `OPEN2ATTACK` — the reproduced battery ✓ cited.

---

### EFF.SIGMALAW.16  [changes-record]

**CANONICAL STATEMENT** (verbatim, E10 #5, L743–786 — the complete SL-C1 derivation). FORM: `###`-headed finding plus a verbatim-ready append. *(Quoted in the audit at `.08`; its consumer sweep verbatim:)*

> “Consumer sweep: SL-C2 consumes only the unchanged identity `δ_j=ρ_j/Σ_m(ρ_j)` and injectivity of `Σ_m`; §5's separator laws, §6's `SL-DELTA` family, §7's OPEN-2a conclusion, and §8's theorem summary therefore survive verbatim.”

**DERIVATION.** A four-line calculation replacing a dangling ellipsis and a restart.

**Audit.** Fully re-derived at `.08` ✓ — `u_j` cancels, the automorphism step is explicit, and the conclusion is reached “**without any omitted term**”.

**SUPERSESSION KIND:** `replacement` of a proof presentation (not of a statement). **TARGETS:** `.08`'s proof.

**CONDITIONALITY.** The sweep's key observation is that **SL-C2 needs only injectivity**, not the automorphism property (`.09`) — so the repair's dependence on `(EC-q)` does not propagate to SL-C2 ✓.

**XREF.** none new.

---

### EFF.SIGMALAW.17  [supplier-finding]

**CANONICAL STATEMENT** — §8's proposed annex text (L556–607), offered for the “GRTW2 §5.2 / OPEN2ATTACK §6 fold”, described in the section heading as an **orchestrator action**.

**DERIVATION.** [RECORD of an offered annex] — a précis of SL-1/SL-C1/SL-C2 with the machine counts.

**LANDING STATUS — NOT LANDED, and E10 #4 is the evidence.** E10 #4 corrects the annex's counts “**For every future transcription**”, which presupposes it has not yet been transcribed. **`grep -cF 'SIGMALAW' GRTW2_PROOF_2026-08-08.md` — not performed in this compilation's batch**; recorded as unverified rather than asserted either way. See OPEN-CALL 1.

**CONDITIONALITY.** If transcribed, it must carry E10 #4's leak-free figures, not the frozen ones.

**XREF.** `GRTW2_PROOF_2026-08-08.md` — EXISTS ✓.

---

### EFF.SIGMALAW.18  [record]

**CANONICAL STATEMENT** — the E10 provenance paragraph (L787–792), with its orchestrator verification legs: “the RESOLVED-ALREADY quote checked against the acceptance append at HEAD; ξ₁ := 1 forced by Σ₁ = id (trivial); the SEP-A convention re-checked (monic exponent j = g₁ = 4 excluded, ξ₂⁴ = 1 from ord(ξ₂) = 4); …”

**DERIVATION.** [RECORD of a verification protocol]. **SERIES:** member 3 — with a stale terminal.

**Compiler re-verification.** The RESOLVED-ALREADY quote ✓ (checked at `.12`); `ξ₁ := 1` forced ✓ (`.13`); the SEP-A arithmetic `ξ₂⁴ = 1` at `ord(ξ₂) = 4` ✓ (`.14`); E10 #4's five subtractions and the tower cross-check ✓ (`.15`); E10 #5's derivation ✓ (`.08`). **All legs confirmed.**

**LEDGER STATUS.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` **row 27**: “**CERTIFIED 2026-08-12** — C9 RATIFIED-W-ANNEX (Σ-law survives); E10: the SL-1 scope GAP RESOLVED-ALREADY (acceptance append is the correct shared-below re-display), 4 MI[NORs …]” ✓ — **the ledger's summary matches the note's append structure exactly.**

**XREF.** `runs/cert/C9_sigmalaw_output.log` EXISTS ✓; `runs/cert2/E10_sigmalaw_annex_output.log` EXISTS ✓ *(note: the frozen text cites this file; a shorter form `E10_sigmalaw_output.log` does **not** exist — the note's own longer name is the correct one)*; `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 27 ✓.

---

## 4. XREF verification ledger

`[TABLE]`

| # | target | object | status |
|---|---|---|---|
| X1 | `GRTW2_PROOF_2026-08-08.md` | W2-L3, (HR-REC), §3.4's ξ/χ characters, §5.2 (the annex target) | EXISTS ✓ |
| X2 | `OPEN2ATTACK` | §1 notation, OA-L1/L2/L3/L4, OA-M1, OA-PHIR/Thm-`phir`, OA-GAUGE, §6 (the annex target), the reproduced battery | cited by name |
| X3 | `verification/openmath/sigmalaw_checks.py` | the sealed runner | EXISTS ✓ |
| X4 | `runs/cert/C9_sigmalaw_output.log` | the sol ratification | EXISTS ✓ |
| X5 | `runs/cert2/E10_sigmalaw_annex_output.log` | the E10 fold | EXISTS ✓ |
| X6 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | row 27 | located ✓ |

**Zero NEAR-MISS, zero invented names, zero designation OPEN-CALLs.**

**PIN VERIFICATION (rule 23).** **Commits — 9 tested, 9 verified:** `6e57e03`, `165ca12`, `59c1ff2`, `6b24942`, `8064ae3`, `9b0117d`, `a00cf97`, `a9f45ab`, and the freeze anchor. **Zero failures.** **md5 — 1 cited, 1 verified and localized:** the frozen-body prefix `a50d3d5f` → **line 604**, unique hit ✓. **`UNPINNED-VALUE`:** the runner and its artifacts carry no md5. **Artifacts — 3 cited, 3 exist.**

---

## 5. Consumption and consumer edges

**Forward:** `OPEN2ATTACK` §1 (notation, OA-L1–L4, OA-PHIR) and `GRTW2` (W2-L3, (HR-REC), §3.4) — both at attempt grade as billed, both ACCEPTED at HEAD.

**Reverse:** `[TABLE]`

| # | consumer | what is consumed | status |
|---|---|---|---|
| RX-1 | GRTW2 §5.2 / OPEN2ATTACK §6 | the §8 proposed annex | **OFFERED, landing unverified** (OPEN-CALL 1) |
| RX-2 | THEOREM OPEN-2a-Σ | SL-C2 fires its forward direction | LANDED in-note |
| RX-3 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 27 | certification status | LANDED — CERTIFIED |

---

## 6. TEETH — the inverse table (rule 6)

**Battery → units.** SL-VDM (2,828 leak-free) guards `.05`'s `(VD-q)`, both legs, every walked slot, every `m`; SL-DELTA (1,414) guards `.08`'s element identity directly on every walked row; SL-GAP (680, 340 gap slots) guards `.04`'s gap-cancellation clause; SL-PHIR (1,414) guards the OA-PHIR denominator; **SL-SEP2 (96 ≥ 8) and SL-SEP3 (27 ≥ 6)** are the **constructed non-involution separators** that witness `.02`'s map correction — “BOTH bare-θ variants fail”; SL-INVREC (218/218) is the reconciliation explaining why the wrong map survived. Six teeth rows all CAUGHT.

**Units → guards.** `.04`, `.05`, `.08` are battery-guarded; `.02`'s correction is **witness-guarded by construction** (the separators are built to refute the bare-θ maps); `.06` SL-L2 was machine-keyed by name **only at PE3**; `.07` `(EC-q)` is **PROOF-ONLY** (derived by PE1, re-derived by PE2, no dedicated family); `.09` SL-C2 rides `.08`; `.12`–`.18` are AUDIT-produced or records.

**PROOF-ONLY (rule 16).** `.07` `(EC-q)` and the well-foundedness of the 3-clause ladder carry no dedicated machine family — they were established and re-established by **two independent hostile passes** instead. **That is the note's substitute for a tooth, and it is stated as such.**

**AUDIT dispositions (rule 27).** `.07`/`.08`'s `[r1]` — `in-house hostile pass`, **generative** (the verifier supplied the missing law). `.13`–`.16` — `decorrelated-model audit` ×4. `.12` — a *pre-emption* rather than a finding.

**Zero-orphan check.** 18 units; 6 battery- or witness-guarded; 12 accounted as records, definitions, PROOF-ONLY or appends. **None silently unguarded.**

---

## 7. Arithmetic and fidelity audit

**Confirmed exactly:** `.02`'s map relation at `q = 2` (`ξ_2 = θ_2^{−1}` since `χ_1 = 1`) and at `q ≥ 3` ✓; `.05`'s reduction to `(MATCH)` and the role of `.06`'s gauge-ratio law in making it `ν`-free ✓; `.08`/`.16`'s complete SL-C1 derivation, with `u_j` cancelling ✓; `.09`'s injectivity-only argument ✓; `.10`'s tower and row arithmetic (`389+96+54 = 539`; `1,211+6 = 1,217`; `539+527+145 = 1,211`) ✓; **`.15`'s five subtractions and the `96+54 = 150`, `389+150 = 539` cross-check** ✓; `.13`'s forced convention ✓; `.14`'s `ξ₂⁴ = 1` at `ord(ξ₂) = 4` ✓; the frozen-body md5 localized to line 604 ✓.

**Findings — one:** **AF-1 — the note's own §8 annex landing is unverified** (`.17`). Recorded honestly; no claim made either way.

**Fidelity.** Every CANONICAL STATEMENT verbatim; **no `[ASSEMBLED]`**. No quantifier, character, sign, count or perimeter altered. **Truncations: four**, at `.02`, `.05`, `.06`, `.14`, each marked. Rule 14 not triggered (checked). 9 commits + 1 localized md5 + 3 artifacts verified; 6 designations verified; zero NEAR-MISS. Every cross-note status claim checked where in-repo.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — the §8 proposed annex's landing is unverified, and E10 #4 corrected it for a transcription that may not have happened. FOR-0b.

`.17` offers an annex to GRTW2 §5.2 / OPEN2ATTACK §6; E10 #4 corrects its machine counts “**for every future transcription**”. **This compilation did not verify whether the annex has landed at either target.** **Decision needed:** confirm the landing state, and if the annex has already landed with the contaminated totals, a corrective rider is owed at the target — the same shape as `spec/EFF-HEX3.md` §B (where the analogous annex **had** landed) and `spec/EFF-HMENU3.md` `.53` (where it had **not**).

### OPEN-CALL 2 — the acceptance record functioned as a statement re-display, and that is now a pattern with no written rule. FOR-0d.

E10 ruled the SL-1 quantifier GAP **RESOLVED-ALREADY** because the acceptance record's WHAT-IS-ACCEPTED clause had already re-displayed the theorem at its proved scope (`.12`). **WELDMASTER's F-3 was resolved the same way** (`spec/EFF-WELDMASTER.md` `.24`). **Two notes, same mechanism, same certification wave.** Meanwhile HE6R1's R7 finding 1 needed an **owner directive** to achieve the same effect (`spec/EFF-HE6R1.md` `.47`).

**Decision needed:** whether “an acceptance record's WHAT-IS-ACCEPTED clause is a governing re-display of the accepted statements” becomes a written convention. **It would be cheap and it demonstrably works** — two GAPs pre-empted in this wave alone — and it would give notes a standing place to state proved-and-consumed scope without editing frozen theorem text.

### OPEN-CALL 3 — `(EC-q)` was derived by a hostile pass and carries no dedicated machine family. FOR-0b.

`.07`'s eigen-coefficient law is the hinge of SL-C1's multiplicativity, and it entered the note **from PE1**, was transcribed at `r1`, and was **independently re-derived by PE2**. It has no dedicated battery family; its evidence is two independent derivations. **That is strong**, but it is a different kind of evidence from the note's other legs, and the claims record does not distinguish it.

**Decision needed:** whether `(EC-q)` warrants its own machine key at the next touch, as SL-L2 received at PE3 (“machine-keyed BY NAME for the first time”). **Note the precedent inside this very note**: the lemma that got a name-keyed family last was the one PE3 chose to re-derive line-by-line.

### Recorded source defects and reading hazards

1. **`.05`: the isolated `(VD-q)` display over-reaches its proof**; the governing scope is `.12`'s re-display (shared-below, every `m ≥ 1`).
2. **`.08`: the frozen SL-C1 proof has a dangling ellipsis**, replaced by E10 #5. The conclusion never moved.
3. **`.03`: `ξ₁` was used and never defined**, supplied by E10 #2.
4. **`.10`/`.17`: the printed battery totals include tooth-run leakage**; the leak-free figures are E10 #4's.
5. **`.02`: the boxed map `σ′` is WRONG** — a correction the note makes at composition, with constructed separators.
6. **`.09`: the converse of OPEN-2a-Σ is UNPROVED** and must not be inferred.
7. **AF-1: the §8 annex landing is unverified.**
8. **`.10`: the runner and artifacts carry no md5** (`UNPINNED-VALUE`); only the frozen body is hashed.

### Exhaustive residual judgment list

There are no other unresolved SIGMALAW judgments. The unproved converse, the shared-below perimeter, and the attempt-grade suppliers are the note's own displayed fences; the annex landing, the missing artifact hashes and the leakage bookkeeping are the rest. The three OPEN-CALLs are the complete list.

### Compilation summary

- **18 statement units** across the frozen post-r1 body (`.01`–`.10`), the acceptance record (`.11`, `.12`), the E10 fold (`.13`–`.16`, `.18`) and the offered annex (`.17`).
- **6 designations/files verified; zero NEAR-MISS. 9 commits + 1 localized md5 (L604, unique) + 3 artifacts verified; zero failures.**
- **Arithmetic audit: every recomputable figure reproduces** — the map relation at both regimes, the tower/row decompositions, all five leakage subtractions with a `150 = 96+54` cross-check, and the complete SL-C1 derivation.
- **Honest headline for a chapter cut:** SIGMALAW discharges a box **and corrects the box's own displayed map in the same note**, with constructed separators as the witnesses — and it explains, quantitatively, why the wrong map had survived (`SL-INVREC = 218/218`: the entire prior `δ ≠ 1` record sat where the two maps coincide). Its one substantive repair came **from** a hostile pass rather than to it: PE1 derived the `(EC-q)` law the proof needed. And its acceptance record's scope clause pre-empted a later certification GAP — a mechanism that also fired at WELDMASTER in the same wave.

EFF-SIGMALAW COMPILED: 18 statements / 6 xrefs verified / 3 open calls
