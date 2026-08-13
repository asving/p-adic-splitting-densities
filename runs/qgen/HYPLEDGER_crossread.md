# PHASE-0b ADJUDICATION — cross-read of `spec/HYPOTHESIS_LEDGER.md`

**Reader:** Opus spec-verification arm (did not author the ledger; the ledger was codex-drafted
under `runs/qgen/HYPLEDGER_brief.txt`). **Date:** 2026-08-13. **Mode:** read-only except this file.

**Target:** `spec/HYPOTHESIS_LEDGER.md` — 80 rows / 20 CARRY-proposed / 15 MATH / 16 open calls,
ending in the capstone-conditionality preview display.

**Internal-count check (done first).** The ledger's own tallies reproduce exactly from its rows:
CARRY = {15, 19, 21, 22, 25, 26, 27, 30, 31, 32, 33, 35, 36, 41, 42, 57, 74, 75, 76, 77} = 20;
MATH = {04–10, 67–71, 78–80} = 15; OPEN-CALL = {15, 21, 22, 57, 67–71, 74–80} = 16. **PASS** — the
document is internally arithmetically consistent. Everything below is about faithfulness to sources.

---

## CHARGE 1 — ROW VERIFICATION

### C1-A. Structural / citation defects

**COR-01 (WHERE, 12 rows, mechanical).** HYP.19–HYP.30 all cite
`lean/notes/openmath/W12_PROOF_2026-08-12.md`. **That file does not exist.** The W12 proof note is
`lean/notes/openmath/W12_PROOF_2026-08-08.md` (2453 lines; verified by `find . -name "*W12*"` —
only the `_2026-08-08` note and its `passPE1..7` reports exist). The ledger evidently pattern-matched
the T-unit `_2026-08-12` dates onto W12. Twelve of the ledger's highest-value rows — including
seven of the twenty CARRY rows — therefore carry an unresolvable source pointer.

**COR-02 (WHERE, 12 rows, cosmetic).** The census row labels are `I-1…I-5`, `S-1…S-8`, `O-1…O-16`,
`L-1…L-5` (hyphenated). The ledger writes `I1`, `I3`, `I5`, `I2`, `S4`, `S5`, `S6`, `S7`, `S8`,
`S1`, `S2`, `S3`. Harmless for a human, but 0c's DAG build will grep on these.

**NOT a defect (checked and cleared).** HYP.04–07/10's `WHERE: …N3_CHECK…, §§9–12` is **correct** —
the note does run to §12 (`## 12. STATUS AFTER UNIT N3B (supersedes §8's "NOT DONE" list)`).
Likewise the coverage statement's "PROJECT_STATE entries #32–#44" is right for drafting time:
**#45 exists but is the append that records this very ledger** (`spec/HYPOTHESIS_LEDGER.md landed
(80 rows / 20 carry / 15 MATH / 16 open calls)`), so it introduces no missed obligation. #45(4) does
record a deferred item — "the GENTOW5-W consumption check + dated append (corpus maintenance, next
cycle)" — which is the same object as HYP.63/HYP.40 and needs no new row.

### C1-B. Statement drift (adversarial spot-quotes)

**COR-03 — HYP.19 `[W12-H]` (CARRY): scope overbroad.**
Ledger: *"The W12 reduction is conditional on its five supplier clauses `[H-a]`–`[H-e]`."*
Source (W12 S4.2, L1132–1138): *"The general clause **(i) at orders ≥ 2** — shapes with repeated
residual factors of degree ≥ 2, i.e. towers whose key polynomials have degree > d — is CONDITIONAL
on the following FIVE named inputs."* And W-12.D's own grade line (L304–314): at `n = 2` *"it FIRES
UNCONDITIONALLY"*; at `n = 3` the conditionality is exactly `{(hMenu-3)} + {(hExhaust-3)}`;
*"At n ≥ 4: those plus [W12-H] at composite stages."* **[W12-H] is a hypothesis only at n ≥ 4
composite stages, not on "the W12 reduction".** As written the row (and the preview display that
inherits it) over-conditionalizes the theorem.

**COR-04 — HYP.24 `[H-e]` (NODE): the row discharges only half of the obligation.**
Source (W12 S4.2, L1153–1167): *"(H-e) … the order-≥ 2 GMN LEAF/σ-DECISION theorem … (the GMN
order-r types theorem — a statement about exact polynomials over O — **PLUS the (H-a)/(H-b)-leg
in-window pinning of the consumed read data**, the composite-stage analogue of S2.3's 'All data the
read consumes sit at heights ≤ N−1' sentence [r2, PE2 m1: **the bare GMN cite under-priced the
window-level statement**]), which is exactly (A0) well-posedness at composite stages."*
The ledger's STATEMENT names only the leaf-decision half, and its disposition ("NODE — the
cite-scope resolution assigns this to the external general leaf theorem after the all-`O` citation
swap") is precisely the "bare GMN cite" that W12's own PE2 pass **already ruled insufficient**. The
window-pinning leg is project-internal and no citation supplies it. This defect propagates to
HYP.34 (`CS-3`, "identical to `[H-e]`") and to the dedup bullet merging them.

**COR-05 — HYP.25 `A0` (CARRY): the separability fence is dropped.**
Source (W12 L270–275): *"(A0) [lift well-posedness] every window-decided member of a core family
has ALL its **disc ≠ 0** O-lifts of the read's type."* The ledger renders this as "Every classified
residue/certificate datum lifts to a well-defined polynomial event with the claimed splitting-type
label" — no `disc ≠ 0`, no "window-decided member of a core family". The fence is load-bearing: W12
L434 exhibits the concrete failure (*"it is FALSE in equal characteristic 3 at the in-window
b₁ = b₂ = 0 members of a TRP-RAM3(h) family with 3∤h, where the lift F = y³ + b₀ has F′ ≡ 0, hence
disc = 0 and no σ at all"*). Since HYP.25 is a CARRY row that becomes public capstone text, an
un-fenced `A0` is a **false** public hypothesis. HYP.72 carries the fence separately, but a reader
of the preview display does not see it.

**COR-06 — HYP.26 `A1` / the display's `σ` subscripts: wrong binder.**
Ledger: *"For fixed `n,σ`, there is a finite, disjoint, `q`-independent menu…"*, and the preview
writes `A0_{n,σ} ∧ A1_{n,σ} ∧ A2_{n,σ}`. Source (W-12.D, L267–303): *"Fix `n` and suppose, **at
every prime power q simultaneously**: (A0)…(A1)…(A2)… **THEN for every splitting type τ of degree
n:** R_τ(q) := Σ_{F: σ_F = τ} …"*. `A0`/`A1`/`A2` are **fixed-`n` only** — the σ-labels `σ_F` are
data carried *inside* `A1`'s family list, and the τ-quantifier sits in the conclusion. Subscripting
them by σ misstates the interface and would mislead the 0d signature freeze.

**COR-07 — HYP.23 `[H-d]` (NODE): the conditioning is dropped.**
Source: *"(H-d) the universal residual censuses OVER RESIDUE TOWERS … — the S2.2 censuses suffice
level by level **once (H-a)–(H-c) identify the reads**."* The ledger's NODE call is right but is a
NODE *given* (H-a)–(H-c), which the row does not say.

**COR-08 — HYP.39 `JD0-BAR`: grade mis-stated, and an owner option is suppressed.**
Ledger: *"The JD0 bar required by the capstone route needs a proof-grade rather than machine-only
coverage."* Source (census I-5): *"J-D0 (count gauge-blindness) is **PROVED grade**, machine
68,523/0, but **sub-bar**: never through the 2-clean hostile arc."* It is not machine-only; the gap
is process. More importantly the census's discharge route is *"run JD0's 2-clean hostile arc, **or
Asvin signs off the machine grade as the bar**"* — an explicit owner decision the ledger converts
into a silent NODE. **This belongs in the 0d package as a needs-Asvin item.**

**COR-09 — HYP.11 `exact cubic densities` (NODE): contradicted by its own source.**
Ledger disposition: *"NODE — the accepted informal `HMENU3`/`HEX3` laws already supply the finite
formulas; the remaining task is transcription and verification."* Source (N3_CHECK §12, "Still OPEN,
and now sharply named", item 2): *"**No exact `n = 3` density**, for the **structural reason** in
§10.3 (the peel parametrisation is resultant-weighted). The five `HMENU3` values remain bracketed,
not proved."* And §8: *"Closing them needs **both drainage AND** the deeper families of HMENU3's
menu (the `DEEP-X`, `B1/B2/B3` tiers), none of which is certified here."* Drainage is HYP.09, a
**MATH** row; the deeper menu tiers are W12-BOX-2's undischarged residue (*"The depth-≥ 1 TRP
families are not enumerated … neither species' transfer law is derived"*, W12 L1218–1224). A NODE
whose precondition is a MATH row is mis-classified.

**COR-10 — HYP.10 `exactly five cubic splitting types` (MATH): over-classified.**
Source (N3_CHECK §12 item 3): *"The `n = 3` analogue of `typeOf_two_cases` ('exactly five types in
degree 3') — needed for the converse of `drainage_three_of_triple` and for any `Σ = 1` identity at
`n = 3`."* But §8 PROVED already carries *"the five cubic types with pairwise distinctness and
degree 3"*, and `typeOf_degree` (`f.Monic → (typeOf f).degree = f.natDegree`, **all degrees**) is
**proved in general** — gate G13 in `GENUINE_DENSITY`, which the ledger itself cites at HYP.01
("Lean already proves `typeOf_degree`"). Given `typeOf_degree`, exhaustiveness in degree 3 reduces
to enumerating multisets with Σeᵢfᵢ = 3, a `decide`. This looks like a **small NODE, not MATH**
(LOW-CONFIDENCE: I did not attempt the Lean). If it is a NODE the MATH count drops to 14.

**COR-11 — HYP.02 `eq_of_add_mul_eq`: statement drift.**
Ledger: *"Solutions of the landed coprime-factor lifting equation are **unique in the relevant
congruence class**."* Source (HENSEL_FACT §6.1): *"**Uniqueness of the exact solve (S3).** The map
`(u,v) ↦ hu + gv` on `R[X]_{<deg g} × R[X]_{<deg h} → R[X]_{<deg g + deg h}` is bijective, not
merely surjective. **Injectivity** is not proved here."* It is injectivity of a degree-bounded
Bézout/interpolation map — nothing to do with congruence classes. The source also records
*"The `n = 3` consumer does not obviously need it … so it was not pursued"*, which the CONSUMED-BY
should say.

**COR-12 — HYP.14 `NS-6`: polarity ambiguity.**
Ledger: *"The descent trigger is equivalent to separability of the relevant residual polynomials."*
Source header: *"NS-6 — Descent trigger: the tower **stops** at order `r` **iff every** order-`r`
residual **is separable**."* Descent *continues* iff some residual is **in**separable; the ledger's
sentence reads as the opposite. Cheap fix, but this row is public-facing text.

**COR-13 — HYP.16 `NS-15`: an undeclared coupling to HYP.15's open call.**
The ledger proposes NODE via *"a statement edit using NS-7/F2"*. Source F-3 Option A: the weakened
bound *"finite depth, bound `≤ (1/2)v(disc f)`" … **follows from F-2's index argument***. F-2 is the
**internal re-proof** branch of HYP.15's open call. If 0d takes HYP.15's other branch (cite
[AGNPRW] Thm 5.2 — which the source itself **recommends**: *"Recommended: cite, and record
honestly"*), that theorem *"gives finiteness at general scope **with no explicit constant**"* and
the `≤ ½v(disc f)` bound in HYP.16 is **not** supplied. HYP.16's disposition is conditional on how
HYP.15 resolves; the ledger presents them as independent.

**COR-14 — HYP.18 `AX-DEFECT`: the separability fence is omitted.**
Source NS-14: the fix is to cite [Kuhl] Thm 3.3 *"with the **separability fence made explicit**"*
(only *inseparable* extensions need char K = 0; the corpus fences its uses to `disc ≠ 0`). The
ledger's row states only the discreteness correction.

**COR-15 — HYP.40 `WI-LEMMA`: CONSUMED-BY materially incomplete.**
Ledger: *"CONSUMED BY: `GENTOW5-W(i)` for i ≥ 3, T3, and T5."* Source (census I-2): *"Conditional on
it at i ≥ 3: **GENTOW5-B(a)'s ψ^{(w)} realized-residual display + the (a)-certificate legs (KP
membership, prime, non-equivalence) + (b)'s FGMN-side residual displays**; NOT conditional: σ,
values, degrees, budgets, (c)/(d)/(e)."* — plus the cone evidence *"The level-r grammar (GENTOW5-B)
is load-bearing for depth ≥ 4 towers, first live n = 32; **the theorem quantifies over ALL n**."*
The ledger's framing ("PE2 is an audit/report node") is right about the *grade*, but the row hides
that the underlying bound is in-cone and load-bearing for every deep tower.

### C1-C. Rows verified clean (verbatim-checked, no correction)

- **HYP.04 strong Hensel** — ledger text vs N3_CHECK §9.4: *"`F` monic with `v(F(x₀)) > 2·v(F′(x₀))
  = 2w`, `w ≥ 1` ⟹ `∃ r, F(r) = 0 ∧ v(r − x₀) > w`."* **Verbatim faithful.** The dedup's companion
  claim also checks out: *"`Uniformity.Hensel.exists_monic_factorization` does NOT supply it. After
  recentring, the residual factorization is `X · X²`, which is not coprime."*
- **HYP.05 / HYP.06** — N3_CHECK §9.4 table: *"needs typeOf SHIFT-invariance to use at `c ≠ 0`"*;
  *"rescale `X = π^m Y`, recurse on the residual cubic | needs typeOf SCALE-invariance"*; §12
  item 1: *"Two further prerequisites the recursion needs, neither landed: **shift-invariance** and
  **scale-invariance** of `typeOf`."* Faithful.
- **HYP.08 cubic tail recurrence** — *"`u(N) ≤ q^{−N/2} + q^{−5}·u(N − 3)` … that estimate is
  written out here so the next unit can check it against its own bookkeeping, but **it is NOT
  proved**."* Verbatim faithful; `WHERE: §9.4` exactly right.
- **HYP.03 n-fold Hensel** — HENSEL_FACT §6.2: *"A pairwise-coprime residual factorization
  `f̄ = ∏ᵢ p̄ᵢ` lifts to `f = ∏ᵢ pᵢ` … `IsCoprime.prod_right`. Not landed"*, and §7: *"Where the
  factorization form becomes *indispensable* is `n ≥ 4`."* Faithful, CONSUMED-BY correct.
- **HYP.12 ordering convention** — N3_CHECK §8: *"The `(e,f)` ordering convention … is a
  trust-boundary item flagged in §3; it is pinned by `leanfinal`'s own `ramType`/`inertType` usage
  but **deserves a human read**."* Statement faithful — but see NEEDS-ASVIN below: "deserves a human
  read" is an owner item, and 0d is the definitions checkpoint.
- **HYP.21 `[H-b]`** — W12 S4.2: *"(H-b) the JB membership faces at unbounded abscissa grids
  (JB-VTX/JB-DEV; GRTJB ACCEPTED 2/2 … with row-12's u ≥ 0 proviso membership residue OPEN)."*
  Statement faithful **as a rendering of [H-b]** — but the dedup that merges it with `JB-NOLEG` is
  wrong; see DEDUP-01.
- **HYP.27 `A2`** — *"(A2) [drainage of the rest] r(N)/q^{nN} → 0, where r(N) := q^{nN} − Σ_{F, x
  visible at N} count(F, x) — everything not in a visible core family: the σ-undecided residue AND
  any window-boundary (tail) families."* Faithful.
- **HYP.13 / HYP.15 / HYP.17** — checked against `CITE_SCOPE_RESOLUTION` §5/§3-F2/§6; faithful
  (HYP.15's "2–4 page internal NODE" matches F-2's *"~2–4 pages, MEDIUM risk"* exactly).
- **HYP.30 `DRAIN-N4`** — W12-BOX-4: *"No upper bound at any grade; lower bounds only (S3.3).
  W-12.B is a conjecture with two proved instances of its shape."* Faithful.

### C1-D. T2 rows — two CLASS refutations and two evacuated CARRY statements

**COR-16 — HYP.43 `(SEC-RANK)`: CLASS REFUTED by the acceptance record, verbatim.**
T2 record L4496: *"**`(SEC-RANK)` — a CARRIER HYPOTHESIS**, not an obligation; it fences no read."*
The ledger files it `CLASS: named-obligation`. The note's own standing counter, repeated at r7,
r8, r9, r10, r11 and r12 (L3505, 3663, 3801, 4027, 4158, 4435), reads *"**Two named obligations
remain open**, both at level one … `(LB1)` … and `(MP1)`."* T2 has **two** obligations, not four.
The statement is also wrong on content: `SEC-RANK` is the **SECONDARY RANK**, the third
lexicographic component of `(RANK)`, and its content is *"σ_𝒞: {states} → W_𝒞, W_𝒞 well-founded,
σ_𝒞(S′) < σ_𝒞(S) at every product-1 linear recentering. Nothing is required of σ_𝒞 at any other
transition"* (L2341–2353). The ledger expands "SEC" as "**section**" and renders a strict *decrease*
on a well-founded order as "has the required rank" — a static property. `grep -c "carrier theorem"`
over the master = **0**; the ledger's CONSUMED-BY names a nonexistent object.

**COR-17 — HYP.44 `(RISE)`: CLASS REFUTED, and its consumer swapped with HYP.43's.**
T2 L3357 (and 3505/3663/3801/4027/4158): *"(RISE) is a **carrier hypothesis, not a ledger
obligation**: it fences no instance read."* Record L4497: *"`(RISE)` — **STIPULATED**, on
`(SEC-RANK)`'s footing."* Content (L3329–3333): `(RISE) ≡ d(Φ_new(ρ)) > λ at every root ρ of the
class being refined`; `(HT) ≡ k = λ` is **derived** from it. The ledger's "the carrier parameter
rises strictly in each recursive transport step" attributes the rise to the wrong object (that
description fits σ_𝒞, which *decreases*) and to the wrong scope (asserted at the product-1 linear
recentering / refine step only). And **termination is `(SEC-RANK)`'s consumer, not `(RISE)`'s**
(L2391: *"Secondary rank: strictly down, by `(SEC-RANK)`. This is the only transition whose strict
decrease sits in the third component"*; S5 item 12: *"well-foundedness then proves both termination
and exhaustion"*). The ledger has the two rows' consumers **swapped**.

**COR-18 — HYP.41 `(LB1)` (CARRY): the consequent is a placeholder.**
Ledger consequent: *"the stipulated block construction has the required properties."* Source
(S1.7B effective text, L2214): *"every level-one state whose clause-4 processing demands blocks …
has the monic side and label blocks of S1.7A, with their own **full developments, single-side
hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited
continuation data**."* Six named conjuncts replaced by "the required properties". As a public
capstone hypothesis this names no proposition and cannot be discharged or checked. The trigger is
also flattened: the source pins it to the displayed disjunction *"every state with at least two
sides, and every side whose residual is mixed"*. CONSUMED-BY additionally omits **S4.1** (L3116)
and **S4.2's exclusion list** (L3115).

**COR-19 — HYP.42 `(MP1)` (CARRY): three of four conjuncts dropped; no WHERE field.**
Source S1.8A (L2432): *"at **every** level-one state whose current key is a **recentered key
dividing its represented block**, the quotient `G′` satisfies `(WINDOW)`, carries its own full
development with `(ACCOUNT)` and the S1.7 test assertions together with the occupied-height, lift,
frame, origin and residual-degree data, and that the peeled recentered key admits a certified
orbit/(e,f) decomposition — **items 2, 3, 4 and 5** of the suite."* The ledger renders MP1 as "the
level-one clause-5 peel at the recentered key is valid, including irreducibility of the recentered
Φ″" — irreducibility is a **sub-clause of item 5 only**; items 2–4 (all about the quotient `G′`)
are absent, the divisibility trigger is absent, and the universal quantifier becomes a definite
singular. The row also carries **no WHERE line of its own**; the defining site is S1.8A
(L2423–2438), not the acceptance record. Additional unlisted inheriting consumers (L3411):
*"clause 5 itself, the S1.8 induction paragraph, and `(RANK)` item 3."*

**COR-20 — HYP.45 `(GRADE)`: "0/2 or 1/2" garbles two simultaneous counters.**
Record L4503: *"**HE3 is consumed at the grade stated by its supplied HEAD, which is attempt grade
0/2 (consecutive-clean count 1/2)**."* These are not alternatives — both hold at once. The ledger's
"at 0/2 **or** 1/2-clean evidence" invites recording HE3 at 1/2. CONSUMED-BY is also the wrong half
of its own STATEMENT: the record extends the cap to *"any **level-two** chain that consumes an HE3
pin through S1.8C"*, while the row narrows to "T2's level-one branch".

**CONFIRMED — the `(MP1′)` dedup claim.** Record L4499: *"`(MP1′)` is NOT a fifth standing
conditionality: it was RETIRED at r6 repair 2 and discharged in S1.8C from `HE3-A-PROOF`,
`HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`. It denotes a consequence of the pins, not an
obligation."* The ledger's bullet is correct. **Caveat it should carry** (L3100): the retirement is
*"**relative**: … a state over Φ″ is `(LB1)`-conditional and `(MP1)`-conditional on exactly the
same triggers as a state over Φ′. What is removed is the extra frame-level obligation, not the
level-one fences."*

### C1-E. T1 rows — a nonexistent locator and one drift in the dangerous direction

**COR-21 — WHERE, 10 rows: `T1 effective hypothesis list` does not exist.**
`grep -in "hypothesis list\|effective hypoth"` over all 4416 lines of `T1_GAUGE_COCYCLE_2026-08-12.md`
returns **zero hits**. HYP.47–HYP.56 all cite it. The object that plays the role is **§5 Honesty
ledger in its effective form** — L4190: *"Effective ledger after this round: items 1–22, with item 4
in this r13 form; no renumbering, no new item, no collision."* Each obligation is stated at its own
§1.1 boxed insertion.

**COR-22 — HYP.52 `C3-read-codomain`: the drift runs in exactly the wrong direction.**
Ledger: *"Every C3 residual read lands in the asserted **graded**/residue codomain."* Source
(L3661–3670): the obligation is that the read is **scalar-valued** — `R_{i+1,β}(consumed grade-β
slice) ⊆ K_i` — and the source's own displayed defeater is precisely a graded codomain: *"the
initial-form read `g ↦ in(g) ∈ gr(µ_i)` satisfies all of them and outputs **grade-β homogeneous
elements, not K_i-scalars**."* A ledger row reading "graded/residue codomain" re-admits the mock
read that this obligation exists to exclude. Its disposition ("supplied by the accepted C3 package")
is also false at depth: L3672 — *"At i ≥ 3, (C3-read-codomain) rides the same named level-general
residual-read supplier package as (C3-ladder-nonvanishing); T1 does not infer it."*

**COR-23 — HYP.53 `(H-JA-CONJ_i)`: the disposition's supplier does not exist.**
Ledger: *"NODE — the acceptance record names the accepted JA supplier."* The T1 acceptance record's
only JA mention is *"the JA/GENHN/HETOW **supplier fences**"* (L4409) — fences audited, not a
supplier discharged. No JA note name and no md5 pin appears anywhere in T1 for `(H-JA-CONJ)_i`;
the box itself says *"This is a **site hypothesis imported from the JA supplier**, not a consequence
of the T1 carrier"* (L1411). **The NODE call is unsupported.**

**COR-24 — HYP.57 `(H-VARTHETA-RES_i)` (CARRY): wrong symbol, wrong T5 locus, overstated OPEN-CALL.**
Source (L3523–3533): the hypothesis is a **membership about ϑ (vartheta)** — `res(n̂_i(u_{i+1})^s /
n̂_i(su_{i+1})) ∈ K_i` — not "residual behavior of the varying Θ_i". T1's Θ_i is a *different*
symbol (ledger item 3 records the orientation `Θ_i(t) = ϑ_{i,f−t}^{−1}`). WHERE's T5 half is wrong:
T5's standing-conditionality line (L1499–1500) reads *"𝒲_{≤i} at i ≥ 3, OPEN-2 at i = 1, [WFRAME
OPEN-1]/[OPEN-3]"* — no `(H-VARTHETA-RES)`; in T5 it sits in honesty-ledger item 13. And the
OPEN-CALL's "**the records** explicitly decline to decide whether S11.2's monomial-quotient theorem
discharges it" is overstated: only **T5** mentions S11.2 (*"Whether S11.2's S2.1 monomial-quotient
computation discharges that hypothesis is not adjudicated here"*); `grep -n "S11.2"` in T1 = **zero
hits**, and T1's only word is *"unproved here"*. CONSUMED-BY omits the heaviest consumer (L3541):
*"the corrected composed key (C3-key) is formed — **only** at a site carrying (H-VARTHETA-RES)_i."*

**COR-25 — HYP.62 `T3-JOINT-OPEN`/`F4-JOINT`: both WHERE halves wrong.**
T3's ACCEPTANCE RECORD (T3 L1345–1368) contains **no** JOINT mention — the item is at T3 **§8.5
"Open machine-coverage item"** (L1065–1081). T1's standing-conditionality block contains no JOINT
mention either — in T1 it is §4.1 plus ledger items 13–14. The CLASS/disposition are fine (T3 L1081:
*"This machine-coverage gap is not a proof gap"*).

**COR-26 — HYP.46, HYP.48–51, HYP.54–56, HYP.58–61: statement drift, uniform pattern.**
Each substitutes an abstract gloss for a displayed formula, dropping the quantitative content that
makes the obligation checkable. Worst instances: **HYP.55** `(H-GENHN-CLEAR)` drops the hypothesis
`u₂ > e₂D′h`, the clearance bound `r(u₂ − e₂D′h)/e₁ > 0`, and the carry clause (L1559–1571);
**HYP.49** drops the two restrictions that make covariance non-vacuous (*"value-zero factor"*,
*"consumed ladder elements"*, L2432–2441); **HYP.46** reproduces a parenthetical (*"general depth
has a terminating reduction algorithm"*) that **R2-1 deleted** — the effective ledger item 1 (L1987)
now reads *"A preceding-letter monomial description **requires the named supplier hypothesis
(H-JA-CONJ)_i**."* **HYP.61** is faithful on statement but its CONSUMED-BY contradicts L4241:
*"the clause gates no (C1)–(C7) conclusion."*

### C1-F. GENIND rows — one serious inversion, and locators that resolve to nothing

**COR-27 — HYP.35 `CS-EXACT` (CARRY): the statement asserts the negation of the clause.**
Ledger: *"Every stage contributes an exact finite q-power-sum menu and an **explicitly bounded
drain**."* Source (GENIND §S7.1 L1172–1177, verified verbatim by me): *"the stage menu and stage
drain delivered by (CS-1)+(CS-2) are **EXACT**: one exact closed form per stratum — a finite sum of
q-powers …, **not asymptotic bounds**."* The note then displays why the distinction is load-bearing
(L206–212): *"without (CS-EXACT) the antecedent would admit **bound-only stage laws** under which
P(n)'s fourth member fails while (CS-1)(CS-2)(CS-3) hold, and the strong induction would not
close."* **The ledger's row is precisely the failure mode the source names.** A discharger working
from the ledger would supply a bounded drain and believe the clause closed.

**COR-28 — HYP.31–37: `GENIND hypothesis ledger` / `per-genre ledger` / `box ledger` resolve to
nothing.** No such headers exist (`grep` returns two prose hits only). Correct loci:
`[GENIND-H]` → §S1 THEOREM GENIND.B L186–227 (clauses L192–214); `CS-1` → §S7.1 L1123–1146;
`CS-2` → §S7.1 L1147–1168; `CS-3` → §S7.1 L1169–1171; `CS-EXACT` → §S7.1 L1172–1190;
`(CS-1Q)` → the dated 2026-08-12 correction §C2-G1 L3592–3722 (`(CS-1Q.a)` L3623–3626,
`(CS-1Q.b)` L3630–3635); `GENIND-BOX-2` → §S8 L1357–1360.

**COR-29 — HYP.36 `(CS-1Q)` (CARRY): only half the clause is rendered.**
`(CS-1Q)` is a **pair**. The ledger paraphrases `(CS-1Q.b)` and silently drops `(CS-1Q.a)`, the
window lower bound `M_G ≥ e(N−1−H) − Δ_G` (L3623–3626); without (a) the clause is unusable in
C2Q's exponent algebra. Also "**force the residual mass to zero**" overstates a rate bound
(L3637). The disposition itself is correct and exactly sourced (L3712: *"A universal discharge for
embedded and mixed genres remains obstructed until those affine ledgers are displayed and
checked"*).

**COR-30 — HYP.34 `CS-3`: the separability antecedent and the `disc ≠ 0` fence are dropped.**
Source L1169–1171: *"(CS-3) the σ-decision — the order-≥2 GMN leaf theorem ([W12-H](H-e)):
**separable stage residuals ⟹** σ-decided with (e·E, f·[K-ext]) read off, **for ALL disc ≠ 0
lifts** — (A0) at the stage."* The ledger keeps only the consequent. Same fence-loss as COR-05.

**COR-31 — HYP.31 `[GENIND-H]`: the n ≤ 3 vacuity and the n ≥ 8 extension are both missing.**
L221–223: *"At n ≤ 3, [GENIND-H] is **EMPTY** (S5): the theorem is unconditional there."* And
L3081–3084: *"read THIS note's conditionality at n ≥ 8 as: **[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] +
[GENHN-TOW-1]**."* Neither `[GENHN-HE(μ ≥ 3)]` nor `[GENHN-TOW-1]` appears anywhere in the ledger
(see MISS-07/08). The preview display's blanket `∀n > 0` therefore both over-conditionalizes
n ≤ 3 and under-conditionalizes n ≥ 8.

**COR-32 — HYP.63 `[GENTOW5-W(i)]`: the NODE disposition is refuted by the row's own cited source.**
Ledger: *"NODE — the later `GENTOW5_WI` certification proves it; the older Q4 'open' report is
stale."* But the **T5 ACCEPTANCE RECORD** — the row's own WHERE — closes (L1499–1500, verified
verbatim by me): *"Standing conditionalities unchanged and displayed: **𝒲_{≤i} at i ≥ 3**, OPEN-2
at i = 1, [WFRAME OPEN-1]/[OPEN-3]."* T5 L616: *"**Certification of the WI companion does not
discharge these conjuncts** from the frozen GENTOW5 statements. Both the higher-rung supplier law
and every downstream conclusion retain their explicit cumulative hypothesis."* T5 §r4 item 2
records why: GENTOW5's own S12.1 append withdrew the unconditional reading of clause (b) that the
WI proof's step (iv) consumes, so the companion survives only as the **conditional** step
`𝒲_{≤i−1} ⟹ [GENTOW5-W(i)]`, and *"the induction closing the conjuncts from the empty base …
is NOT performed by the companion as written and NOT assumed here."*
**HYP.63 is a CARRY row, not a NODE.** It is the ledger's single largest understatement of the
capstone's conditionality: it removes a live conjunct from the preview display.

**COR-33 — the "stale Q4" claim is date-inverted.** `runs/qgen/Q4_output.log` was committed
**2026-08-13**; `GENTOW5_WI_2026-08-10.md`'s last commit is **2026-08-12**. Q4 is the *newest* of
the three artifacts, and its reading (𝒲_{≤n} still standing) is the same one the T5 acceptance
record adopts. The ledger has the supersession arrow pointing backwards.

**COR-34 — HYP.40 `WI-LEMMA`: invented name + stale-in-both-directions status.**
(a) "cumulative-**window** lemma" appears nowhere in the corpus except this ledger; the corpus name
is *"the **single-w monomial form of the B″-transport** at levels i ≥ 3"* (census I-2; `GENTOW5_WI`
title line). "Window" is a live and different term of art here (certified windows, stage windows,
window truncation).
(b) "the second proof-evidence report remains pending" is **false of the arc**:
`docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 18 records *"**CERTIFIED 2026-08-12** — R10 pass
3: zero findings on all five charges, sol verdict 'CERTIFIED 2/2'"*. It is true only of the stalled
file `GENTOW5_WI_passPE2_report.md` (*"VERDICT: PENDING"*), which is not the certification of
record. The **real** surviving obligation is the S12.1 scope re-verification named under COR-32 —
which the ledger does not contain at all.

### C1-G. T3/T4/T5 rows — one box reported open that is discharged, two status inversions

**COR-35 — HYP.67–71: WHERE points at the wrong section (5 rows).** The T4 ACCEPTANCE RECORD
(L2226–2244) **lists no boxes**; its standing line is L2242–2244: *"Standing fences unchanged and
displayed: f₁ ≥ 2 (BOX-4 residue), μ₂ ≥ 3 (candidate only), the disc ≠ 0 quarantine at the σ-read
legs."* The five boxes live in **T4 §S7 "Residue home", L526–539**, and their defining text is
upstream in `GENTOW6_PROOF_2026-08-09.md` / `GENTOW3_PROOF_2026-08-09.md`.

**COR-36 — HYP.70 `GENTOW6-BOX-4`: reports a DISCHARGED box as open, and fuses two objects.**
T4 L533–535: *"`GENTOW6-BOX-4`: its stated sealed-row ask **is discharged at HEAD**, but any widening
of corrected-lift certificate coverage belongs here."* Upstream, `GENTOW6_PROOF_2026-08-09.md`
L1249–1255: *"**GENTOW6-BOX-4 … : DISCHARGED.** The box's ask — a SEALED BATTERY-grade x-ful-digit
certificate row … — has run: `gentow6_box4_row.py` … **GREEN 265/0 at FOUR x-ful rows**"* — with
sealed contact **at f₁ = 2**. The ledger's *"proved only for f₁ = 1, μ₂ = 2"* belongs to a
**different object**, the R5-63A full-exposure discharge (T4 record L2233–2235). What actually
survives is a theorem-grade residue (T4 L2105–2109: *"no (a)-grade layer classification is sealed at
f₁ ≥ 2 (GENTOW6-BOX-4 residue)"*). As written the row is false in the "sealed" direction.

**COR-37 — HYP.66 `WFRAME OPEN-3`: the epistemic status is inverted.**
Ledger: *"Exact equality among the alternative avatar bookkeeping presentations **is not proved**."*
Source (T5 L392): *"**WFRAME OPEN-3 — avatar bookkeeping.** Determine the **exact gap** between a
uniformizer avatar and the intrinsic read (WF-w). **LW3 proves the gap can be nontrivial.**"* T5
L283–286 displays the instance: `w_av = 2 ≠ w_3`, *"Thus the avatar is not substituted for (WF-w)."*
Equality is **known to fail**; the open item is to quantify the gap. "Not proved" invites a later
reader to try to prove it.

**COR-38 — HYP.65 `WFRAME OPEN-2`: invented notation, disjunction flattened, and "no capstone leg"
is false inside T5 itself.** Source (T5 L390): *"**WFRAME OPEN-2 — outer tie.** Identify S11.3's
fixed letter-power unit with the displayed `w₁`, **or retain them as distinct normalizations**."*
The ledger's `u₁ = w₁` is not the corpus's notation (`u_i` is the B-law function `u_i(β_t)`), and the
source states a **disjunction**, not an unproved equality. CONSUMED-BY *"no current capstone leg"* is
contradicted at T5 L1185–1193: OPEN-2 is the fence that keeps the **entire i = 1 stratum** out of
T5's laws (*"**i = 1: NONE.** No supplier discharges (C3-ladder-nonvanishing) at i = 1 … Its
identification with w₁ is exactly WFRAME OPEN-2; the i = 1 display stays open with it."*).

**COR-39 — HYP.72 `disc ≠ 0` fence: the consumer is exactly backwards.**
Ledger CONSUMED BY: *"T4's σ-read legs and W12's lift labeling."* Source (T4 L1827–1836): *"The
**sources** demand disc ≠ 0 on their σ-read legs, and only there … **T4 consumes none of that
σ-content**: every clause of LEMMA T4.2 is a graded-digit statement."* And the operative obligation
(L1856–1860): *"disc ≠ 0 is **NOT** part of 𝔐 and appears in **no** digit-floor clause of this note;
**any later consumer that needs a decided-leaf σ must import the source's own disc ≠ 0 hypothesis at
that consumption site, alongside — not inside — membership**."* T4 even displays a floor-domain
element with `disc = 0` (L1655–1657), so the fence *cannot* be folded into membership. Also
"separable" is not T4's word (`grep separab` in T4 = **0 hits**). The correct row: the fence is an
**import obligation on downstream consumers** (W12's lift labeling being one), stated alongside
membership.

**COR-40 — HYP.62, HYP.68, HYP.71: three further drifts.**
HYP.62 fuses two **opposite** objects: `F4-JOINT` is the frame that *does* have both axes live but is
a finite graded-carrier model (*"not a claimed explicit ℚ_p-polynomial realization"*), while
`T3-JOINT-OPEN` demands a **realized p-adic** frame. HYP.68 narrows to "partial-side" where the
source says the count is *"**open already at FULL sides** (GENTOW-1's count-law remark), not a
partial-side novelty"*, and blurs a clean split (the budget half is PROVED; only the ledger half is
BOX-2). HYP.71 drops the second conjunct of the ask: *"a genre-general non-vanishing proof, **and
battery witnesses for entry-digit-driven overflows** at genres where the key self-power stays below
D′ in x, are NOT delivered."*

**Verified negatives (silence is evidence).** T5 has **no OPEN-4 or later** (only OPEN-1/2/3 at
L388/390/392); there is **no `GENTOW6-BOX-5`** anywhere in the repo. The ledger's box *count* for
T4/T5 is right; its *coverage* of each box is not.

---

## CHARGE 2 — COMPLETENESS SWEEP (obligations the ledger MISSED)

Ranked TIER-1 (clearly live, ledger-scope by its own inclusion criteria) / TIER-2 (arguably live) /
TIER-3 (recorded for exhaustiveness).

### TIER-1

**MISS-01 — `[GENHN-HE(μ ≥ 3)]` and `[GENHN-TOW-1]`: the n ≥ 8 conjuncts.**
`GENIND_PROOF_2026-08-08.md` L3081–3084: *"read THIS note's conditionality at n ≥ 8 as:
**[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] + [GENHN-TOW-1]** — the n ≥ 8 leg rests on [GENHN-TOW-1] IN
ADDITION TO [GENHN-HE(μ ≥ 3)]."* And W12 L437 names the first independently: *"the clause at μ ≥ 3
leaves IS the named open box **[GENHN-HE(μ ≥ 3)]** ('σ-decision at stage leaves of multiplicity
μ ≥ 3, first live n = 6') … it names, at W-12.D's own hypothesis, the one thing that program already
owes."* Neither name occurs anywhere in the ledger. **The capstone quantifies over all n; the
display's conjunction is incomplete for n ≥ 6 and n ≥ 8.**

**MISS-02 — the four value-layer hypotheses `(VD-m)`, `(C-coll)`, `(R-coll)`, `PERIM-μ`.**
W12 L219–221 names the value-layer hypothesis set as *"((VD-m), (C-coll), (R-coll), (DMULT-s),
PERIM-μ …)"* — absent at the order-1 layer, live at the order-≥2 layer, i.e. inside `[H-c]`. The
ledger's `[H-c]` component list names only `DMULT-S`. `(VD-m)` is the sharpest of them:
`GRTJB_PROOF_2026-08-08.md` L~510 — *"(VD-m) is **UNCONDITIONAL AT m ≤ 1 ONLY** ((VD-1) = W2-L3); at
every m ≥ 2 it is a **HYPOTHESIS** … so **JB-CREAD has NO unconditional stratum above m = 1**: the
note's own sealed runner **machine-evaluates (VD-2) FALSE on 10 of its 13 roster boundary rows**."*

**MISS-03 — `GENIND-BOX-3`, `-4`, `-5`, `-6` and `GENIND-BOX-1`.** The ledger lists box **2 of six**
from `GENIND_PROOF` §S8 with no dedup note. The three substantive omissions:
- **BOX-3 (d ≥ 2 and prime-power coverage)** L1361–1366: *"The battery exercises d = 1 clusters at
  prime q only; general d ≥ 2 … rests on the proofs' Q-uniformity … **machine-uncorroborated here**."*
  A live generality obligation on a theorem quantifying over all prime powers.
- **BOX-4 (drainage bound at n ≥ 4)** L1367–1372 — the simple-slice β-bookkeeping compression. **Not
  the same object as HYP.30 (`W12-BOX-4`), which is a different box in a different note.**
- **BOX-5 (the grade cap)** L1373–1420, closing: *"**the clean count has NOT started** … the
  uniformity theorem at n ≥ 4 is a **CONDITIONAL STRUCTURE, displayed, not a result**."* The ledger
  carries `grade-cap` as a class but omits the grade cap on the note that supplies the whole
  general-degree layer.
- **BOX-6 (conventions)** L1421–1425: *"oracle **mixed-characteristic only**"* — directly relevant to
  the all-characteristics claim.
- **BOX-1** is coextensive with HYP.31, but the ledger never says so.
Also unnamed: `GENIND-5` + its obstruction list `(OB-a)..(OB-d)`, `ANNEX-LEMMA GENIND-C2Q`, and the
`GENIND-6` honesty box (§S4.3 L814–825, whose *"clause (d) … stage-side content is [GENIND-H]'s, not
discharged here"* is a second, distinct compression debt).

**MISS-04 — the capstone `Prop` definitions are PENDING ASVIN'S SIGN-OFF, with four displayed
questions.** `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md` **§2.5 header, verbatim: "The capstone
targets (⚠ PENDING ASVIN'S SIGN-OFF)"**, followed by *"**Four points for your sign-off.** (i) The
`∀ O` is over `Type` (universe 0) … (ii) The rational function is evaluated at `(q : ℚ)` and the
equality is read in `ℝ` via the coercion. (iii) `den.eval q ≠ 0` is demanded per-`O`, not globally …
(iv) `σ.degree = n` currently does no work."* Also `HENSEL_FACT_2026-08-13.md` §4 header: *"TRUST
BOUNDARY — faithfulness paragraphs (**FLAGGED FOR ASVIN'S REVIEW**)"*. **These are the literal
subject matter of phase 0d ("definitions + capstone signatures", PROJECT_STATE #44) and the ledger
has no row for any of them.** (Point (iv) is self-superseded: `typeOf_degree` has since landed as
gate G13.)

**MISS-05 — the Haar-measure bridge: an informal-vs-Lean interface mismatch.**
`GENUINE_DENSITY` §3B.4: *"`upperDensity = genuineDensity` … does **not**, as a Lean theorem, say
that this common value is the **Haar measure** of the type-σ locus … Formally, `genuineDensity` is
the limit of decided proportions, full stop … It is recorded as an **optional, not a blocking**,
item."* But the informal capstone claims the Haar identification outright: W-12.D's conclusion —
*"it equals the N → ∞ limit of the decided-τ window mass **AND the Haar splitting density μ_τ**"* —
and the census cone line *"Σ_τ R_τ = 1 = **the Haar density**"*. `N2_EXACT` §7 lists it as open:
*"**The Haar-measure bridge** (`leanfinal` §3B.4) is untouched."* The ledger's exclusion paragraph
does not name it, and it is not a "quadratic sharpness/rate question". This is exactly census **L-5
(DEFINITION-AUDIT)**, which the ledger also omits.

**MISS-06 — census §4's Lean-capstone rows L-3, L-4, L-5.** The ledger absorbs L-1 (`hExhaust`, via
dedup) and correctly excludes L-2 (`htameFE`, dropped from the uniformity statement by Amendment 2).
It omits the other three: **L-3** *"AX-CELLREC/AX-LEAF (faithfulness entries DRAFT, **PENDING ASVIN
REVIEW**) … They gate the LEAN capstone claim"*; **L-4** *"`RealInstanceAt.faithful` placeholder —
True-placeholder in `Stage2/UniformityTarget.lean`; theorem-strength consumption before the gates
unit is declared **ILLEGITIMATE in-file**"*; **L-5** the DEFINITION-AUDIT unit. L-3 is a
pending-Asvin item by the census's own words.

### TIER-2

**MISS-07 — cross-note frame staleness (T3 and T5 against T1).** T5's own rider m-2 records that its
frame of record is *"T1 with r1–r10"*, while `T1_GAUGE_COCYCLE_2026-08-12.md` is at **r13** — and
**T1 r12 introduced the two-clause `w_i ∈ K_i^×` gate** that T5's `(WF-w)` membership depends on.
Worse, T3 pins **no T1 revision at all** (its only frame statement: *"Revised T1 is now the frame of
record for wrap and gauge facts"*) and carries **neither** `(H-VARTHETA-RES)_i` **nor**
`(C3-ladder-nonvanishing)` (grep: 0 hits in T3 and T4), while consuming `Θ_N = ϑ_N^{-1}` and
`[GENTOW5-W(i)]` at i ≥ 3 — precisely the sites at which T5 concluded *"**EVERY** site of this note
that divides by `w_i` or substitutes it carries (C3-ladder-nonvanishing) explicitly."*
**This is the strongest un-rowed risk in the sweep: an accepted note may be consuming a fence-free
version of an obligation two of its siblings carry.**

**MISS-08 — a live self-contradiction at HEAD in T5, and it is the ledger's own failure mode.**
T5 L299 (superseded r0 text, still present): *"The certified WI note **discharges** these conjuncts
in its tower range."* vs T5 L616 (governing r1 text): *"Certification of the WI companion **does not
discharge** these conjuncts."* HYP.63's NODE disposition is exactly what reading L299 alone produces.
The corpus owes a strike/append; the ledger owes the corrected row (COR-32).

**MISS-09 — T2's HE7.A source-obligation suite.** T2 S4.1 L1167: *"The theorem assumes the explicit
quantitative consequences **`(ACCOUNT)`, `(RES-DEG)`, nonemptiness, exhaustion, and root-preserving
continuation**. These are **source obligations**, not conclusions obtained merely by naming a
carrier."* `(SEC-RANK)` and `(RISE)` are *members* of the fifth — so the ledger carries two members
of a five-member suite while dropping the suite, along with its instantiation condition (*"any
instance that cannot supply it **does not instantiate HE7.A**"*).

**MISS-10 — T2's `(MID-PEEL)` items 2–5 as a standing clause hypothesis**, discharged per-instance
but never master-proved except item 1 (L2415). And **T2 S4.2's twelve explicit non-claims**
(L1171–1184) — including *"partial-side budget or **density** laws"*, the direction a density
capstone leans hardest.

**MISS-11 — T1's effective ledger items the rows do not reach**, chiefly **item 18**
`(C3-lift-coefficient-space)`/`(C3-corrected-coefficient-bound)` (*"Every coefficient used in
(C3-key) must also satisfy `deg k̂_t < deg Φ_i`"*, a live independent site obligation with its own
battery tooth), **item 9** (*"Gauge-invariant residual factor patterns become splitting types **only
through the surrounding tower correctness theorem**"* — capstone-relevant), items 15/16 (nonzero-digit-
only exact-lift contract), item 17 (binary-carry restriction on the A2 HETOW pin), item 20 (A6
provenance).

**MISS-12 — evidence-grade caveats on the T-units.** T1's record: the 2/2 is minors-only and PASS 1's
own verdict slot reads *"NOT CLEAN on its template's strict reading"*; *"the two final riders
postdate both passes and are **unreviewed by a further hostile arm**"*; *"**PASS 2's pin audit was
note-internal** … it could not reopen the HEAD supplier files at byte level"* — which downgrades
exactly the JA/GENHN/HETOW/VARTHETA supplier fences of HYP.53–57; and battery checks 7–10 (the teeth
for MISS-11's item 18, HYP.51, HYP.52, HYP.61) were **scored for the first time** at this acceptance.
T4's: *"This note adds **no machine computation** … not fresh evidence for a stronger theorem."*

**MISS-13 — W12-BOX-5 and W12-BOX-7.** BOX-5 carries a live Lean-side item (*"The Lean `omCount`
evaluator remains order-0; growing it is **Phase-B code**"*) plus the unconsumed W-2/LIFTCORNER
lift-convention seam. BOX-7 is a σ-**convention** item (decided = certified on window digits for all
disc ≠ 0 lifts; two conventions can disagree on deep-tail TRP members) — a definitional-audit sibling
of HYP.12, on the 0d definitions checkpoint. (BOX-6 and BOX-8 are correctly excluded: census O-15
grades coverage boxes as disclosures, and BOX-8 is a non-claim.)

**MISS-14 — T4's own standing fences and non-claims**: the **μ₂ ≥ 3 "candidate only"** fence (named
in T4's standing line, *distinct* from BOX-1: *"This instance does not infer that ω_j ≠ 0, does not
assert that j is touched, and does not assert threshold attainment"*, with an explicit consumption
ban); the **T4.2(c) full-exposure premise at f₁ ≥ 2**; **T4.2(d)'s all-provenance exclusion**; the
**fail-closed pin convention** (an operative consumer obligation that has already fired once as a
CRITICAL); and **GENTOW3-BOX-2** (machine coverage: *"the five committed families sit at f1 = 1 AND
eta = 1"*), absent from both T4's residue home and the ledger.

**MISS-15 — T3's `(G5-COND)` ride list and its narrowed scope.** Eight named objects are conditional
at n ≥ 3 (key-polynomial membership, primality/irreducibility, admissibility, non-equivalence; exact
intermediate values; `P_{n+1}`-membership; clause (c); clause (e)) — HYP.63 carries the hypothesis
but nothing about what rides it. Also T3's delivered scope is **two** absorptions + one documented
non-instance, and *"GENTOW-6.4 remains additive, filtration-triangular, and **unabsorbed**"* — a
narrowing no ledger row records. And **T3's acceptance record has no standing-conditionality block at
all**, so HYP.62's WHERE sources from an empty set.

**MISS-16 — `HENSEL_FACT` §7's three named missing items for branch (ii)**: *"the residual trigger"*,
*"class-determinacy at FINITE level"* (*"if `f ≡ f'` mod `𝔪^N` then the lifted factors agree mod
`𝔪^(N−c)` for an explicit `c` … is **NOT landed**"*), and *"the counting step"*. Items 1 and 3 look
**superseded** by N3B's landing of branch (b) in full; item 2 is unclear. The ledger read §6 but not
§7, and its exclusion paragraph names none of them — a reader cannot distinguish a judged exclusion
from a miss.

### TIER-3 (correctly excluded, verified)

The ledger's exclusion of **`htameFE`** is sound (census O-8: Amendment 2 dropped palindromicity from
the uniformity statement, so it is out of this cone). The exclusion of **the quadratic STATUS opens**
is sound (`N2_EXACT` closed the three exact `n = 2` values and the split/inert symmetry — and
notably *not* by an involution, but by two independent exact censuses). **`X-LEMMA` (O-1)**,
**`TAIL-CERT` (O-10)**, **`W10-GEN` (O-11)**, **rider debt (O-14)** and the **coverage-disclosure
class (O-15)** are all correctly out — though the census itself says S-4 *"will re-check this OUT
call"* for W10-GEN, and W12-BOX-1 records *"The general W-10 … remains OPEN — W10-BOX-1 stands
untouched."*

**One chronology note the ledger owes 0d.** The census's headline verdicts — *"**No unproven
mathematical statement is consumed by the theorem at acceptance grade**"* and *"**Zero in-cone items
are unproven-and-unattempted mathematics**"* — are dated **2026-08-11** and are superseded by the
2026-08-12 GENIND `(CS-1Q)` correction and the 2026-08-13 leanfinal/leancheck notes. The ledger is
right to prefer the later records, but it never says the census verdict was overtaken, and a 0d
reader comparing the two documents will read a contradiction.

**COR-41 — HYP.73 `WELD-FACE-AUDIT`: the audit's charter is overstated by a factor of two.**
Ledger CONSUMED BY: *"disposition of HYP.67–HYP.71 **and HYP.74–HYP.80**."* Source (census S-4):
*"named at Plan revision R.4/F23-F36 … **It is the decider for S-5…S-8** and the SG-2 branch
input."* S-5…S-8 are HYP.74–77 — **four rows, not fourteen**. The census puts HYP.78/79/80 in a
*different* family (Family A, the sub-box refinement residue), whose decider is not S-4 at all:
appends #20/#23 grade those *"count-grade refinements, not correctness conditions on the tie"*, and
the census assigns each its own proof route (S-1 *"PROVE — the pending RCT unit; the 6.7E
genre-geometry pair is the constructed foothold"*; S-2 *"natural rider on S-1's unit"*; S-3
*"PROVE + machine row — extend the BOX-4 sealed battery one μ₂ up"*). The T4 boxes HYP.67–71 are not
assigned to S-4 either. **Consequence: eight rows whose dispositions read "medium **if** HYP.73 finds
a live route" are resting on an audit that was never chartered to decide them.**

---

## CHARGE 3 — DEDUPLICATION AUDIT

Fifteen dedup bullets. **6 clean · 4 correct-but-incomplete · 5 wrong or refuted.**

### CLEAN (verified against source)

- **D-09 (strong Hensel ≠ coprime-factor Hensel)** — the ledger's best call, and a *non*-merge it was
  right to resist. Verbatim source (N3_CHECK §9.4): *"`Uniformity.Hensel.exists_monic_factorization`
  does NOT supply it. After recentring, the residual factorization is `X · X²`, which is not
  coprime; and the scalings that separate the polygon sides are non-integral."*
- **D-12 (`WFRAME OPEN-1` absorbs the older "can w = 1?" question)** — correct, and it silently
  reconciles a numbering discrepancy: the census calls it **O-7 "WFRAME OPEN-4"** while T5 has only
  OPEN-1/2/3, with OPEN-1 explicitly *"including a criterion for `w_i = 1`"*.
- **D-13 (`GENTOW6-BOX-1` ∩ `COMPOUND-6.5′` on f₁ ≥ 2, μ₂ ≥ 3; `P-BINOM`/`S8.1-MEMBER` adjacent but
  not proved identical)** — correct and appropriately hedged; `GENTOW6_PROOF` L1244–1247 confirms
  BOX-1's undelivered content is exactly *"the j < j\* classification at mu2 >= 3 … and the
  f1 >= 2 x mu2 >= 3 compound (ANNEX-REMARK 6.5′ there, prose only)."*
- **D-15 (`(MP1′)` retired)** — **CONFIRMED verbatim** (T2 L4499), with the relativity caveat.
- **D-02 (the drainage chain)** and **D-10 (typeOf invariance ⊋ certificate-level shift lemmas)** —
  correct; D-10 LOW-CONFIDENCE (I did not read `RamAt_shift`'s statement).

### CORRECT BUT INCOMPLETE

- **D-01 (A0/A1/A2 = W12.D's public interface; `[W12-H]`/`[GENIND-H]` are lower suppliers)** — right
  in structure, but the preview display then violates it (see CHARGE 5).
- **D-02** — add: at n = 3 the *Lean* names are `UndecidedVanishes O 3 σ` / `drainage_three_of_triple`,
  not `hExhaust3`; and **`GENIND-BOX-4` is a distinct box from `W12-BOX-4`** (MISS-03), so the chain
  as drawn conflates two rungs.
- **D-03 (menu exactness = A1 = CS-1/CS-2/CS-EXACT = hMenu3)** — too coarse. `CS-1` is a *count-
  fibration*, `CS-2` a *bracket*, `CS-EXACT` an *exactness* clause; and **`CS-1` is dual-parented**:
  GENIND L1027–1030 routes it to **Step 4 / (A2)** as well, and L3197 makes it *"the sole hypothesis"*
  of the CS-drain rate lemma. Filing CS-1 under menu exactness alone hides its drainage role.
- **D-06 (`[H-c]` = aggregate value-side package)** — right in structure (W12 S5: *"conditional on
  exactly the union of the **six** weld notes' displayed boxes + the Σ-LAW residue"*), but the
  component list is short by four — `(VD-m)`, `(C-coll)`, `(R-coll)`, `PERIM-μ` (MISS-02) — and
  `DMULT-S` is **double-parented**: `[H-a]` cites GRTJC *"consumed as warrant, **its own
  conditionality displayed there**"*, and `DMULT-S` lives in `JC-BOX-3`.
- **D-08 (BOX-2/BOX-3 discharged by HMENU3/HEX3)** — defensible, but omits that W12-BOX-3's residue
  has three corpus names (`TAIL-CERT` = `HEX3-BOX-1` = `HM3-BOX-1`, census O-10) and that HMENU3
  carries a live `[r5]` ANNEX-2 correction for the `disc ≠ 0` over-claim.

### WRONG OR REFUTED — the expensive ones

- **D-05 — `[H-b]` ≡ `JB-NOLEG`: WRONG MERGE, and it is the exact failure the charge warns about.**
  `[W12-H](H-b)` names **one** open item: *"with **row-12's** u ≥ 0 proviso membership residue
  OPEN"* (W12 L1143–1145; restated at L219 as *"the JB **row-12** membership residue"*). `JB-NOLEG`
  is GRTJB §0M's **four-row** open-proviso frontier — `GRTJB_PROOF_2026-08-08.md` [r4, F-2],
  verbatim: *"**FOUR cells hold an open proviso with NO machine leg beside it — rows 4 (the (GRID)
  grid/attained-abscissa half …), 5 (RES), 12 (d4) and 22 (v = 0)** — and TWO of them, rows 4 and 12,
  are the u ≥ 0 riders … Those FOUR are the note's honest evidence frontier."* **The merge silently
  drops rows 4, 5 and 22.** Row 5 is `(RES)` riding JA-RES's per-digit proviso at m ≥ 3; row 22 is the
  machine-unexercised `v = 0` branch. One display conjunct is standing in for four obligations.
- **D-07 — "only its evidence-grade node remains" for `GENTOW5-W(i)`: REFUTED.** The three-way merge
  of the objects is right; the discharge claim is contradicted by the T5 acceptance record and by
  T5 L616/L926–930 (COR-32), and the "older Q4" chronology is inverted (COR-33).
- **D-11 — `T3-JOINT-OPEN` ≡ `F4-JOINT`: WRONG MERGE.** They are opposite objects: `F4-JOINT` is the
  frame that *does* have both axes live (`f₁ = 2, η = ω ≠ 1, w = ω ≠ 1`) but is *"a finite
  graded-carrier frame, **not** a claimed explicit ℚ_p-polynomial realization"*; `T3-JOINT-OPEN`
  demands precisely *"a **realized p-adic** B″ frame"*. F4-JOINT additionally *supplies* scored exact
  predictions to T1's §4.1 battery. Merging the supply-side model with the demand-side gap loses both.
- **D-04 — `[H-e]` ≡ `CS-3` ≡ "the higher-order GMN σ-decision": PARTIAL.** `(CS-3) = (H-e)` is right
  (GENIND L1338). But *"the higher-order GMN σ-decision"* is the **citable half only**; `[H-e]` =
  that theorem **plus** the in-window pinning leg (COR-04). And the dedup omits W12's own
  identification *"(H-e) … **is exactly (A0) well-posedness at composite stages**"* — which matters
  because the display carries A0 separately.
- **D-14 — "the historical `RealInstance` placeholder … and Haar/Denef bridge plans are superseded":
  PARTLY WRONG.** The `RealInstanceAt.faithful` placeholder is census **L-4**, a *named stage-two
  unit* whose theorem-strength consumption is *"declared **ILLEGITIMATE in-file**"* — not a
  superseded plan. And the **Haar bridge is live, not superseded**: `GENUINE_DENSITY` §3B.4 records
  it as an explicit (optional) open item and `N2_EXACT` §7 lists it under **NOT DONE / OPEN** dated
  2026-08-13 (MISS-05). The Denef half is fine (measure route only).

---

## CHARGE 4 — THE 16 OPEN CALLS, ADJUDICATED

**RESOLVED FROM IN-REPO EVIDENCE (5).**

- **HYP.70 `GENTOW6-BOX-4`** — resolved by COR-36: the box's stated ask is **DISCHARGED at HEAD**
  (`gentow6_box4_row.py`, GREEN 265/0 at four x-ful rows, sealed contact at f₁ = 2). Restate the row
  as the surviving theorem-grade residue (*"no (a)-grade layer classification is sealed at f₁ ≥ 2"*).
  Deciding text: `GENTOW6_PROOF_2026-08-09.md` L1249–1255 + T4 L533–535, L2105–2109.
- **HYP.78 `S8.1-MEMBER`, HYP.79 `P-BINOM`, HYP.80 `COMPOUND-6.5′`** — the census already assigns each
  a proof route and an effort size (S-1 *"PROVE — the pending RCT unit; the 6.7E genre-geometry pair
  is the constructed foothold"*, hard-unit; S-2 *"natural rider on S-1's unit"*, unit; S-3
  *"PROVE + machine row — extend the BOX-4 sealed battery one μ₂ up"*, unit), and appends #20/#23
  grade the family *"count-grade refinements, not correctness conditions on the tie"*. They are
  **named proof units, not owner decisions**. Keep MATH; drop the OPEN-CALL; drop the false
  dependency on HYP.73 (COR-41).
- **HYP.57 `(H-VARTHETA-RES)_i`** — the open call asks whether S11.2's monomial-quotient theorem
  discharges it. That is a **technical adjudication, not an owner preference**: convert to a named
  corpus unit ("adjudicate S11.2 §S2.1 ⟹ `(H-VARTHETA-RES)_i` at i ≥ 3") and **CARRY meanwhile**.
  Deciding text: T5 L1195–1203 (*"is not adjudicated here"*) — a deferral, not a question for Asvin.

**COLLAPSE INTO ONE OWNER QUESTION (10 → 1).**
HYP.21, 22, 67, 68, 69, 71, 74, 75, 76, 77 all reduce to *"is this weld face reachable from the
capstone path?"*, and the census names the single instrument that answers it: **S-4
WELD-FACE-AUDIT**, *"one session, mechanical grep + walk; each hit becomes a census row."* The owner
decision is scheduling, not mathematics. (Note COR-41: the census charters S-4 for HYP.74–77 only;
extending it to HYP.21/22/67/68/69/71 is a **scope decision** that itself needs stating.)

**GENUINELY NEEDS ASVIN, STANDALONE (1).** **HYP.15 `NS-7`** — this sets the project's trusted base
and the source itself frames it as a choice while recommending one branch (*"**Recommended: cite,
and record honestly**"*, §5 Stage 3).

**Net: 16 open calls → 2 questions** (one scheduling, one trusted-base), plus 6 further owner items
the sweep found that the ledger never surfaced (CHARGE 6).

---

## CHARGE 5 — THE PREVIEW DISPLAY, RECOMPUTED

**Row coverage: correct.** Of the 20 CARRY rows, 17 appear; the three absent are HYP.19 `[W12-H]`,
HYP.31 `[GENIND-H]` (aggregates, correctly omitted per the display's own rule) and HYP.30
`DRAIN-N4` (absorbed into A2/CS1Q by dedup D-02). **Dagger placement: internally consistent** — 7
marks for the 8 CARRY∩OPEN-CALL rows, the deficit being HYP.21 and HYP.75 merged into
`JBMembership†`. But that merge is D-05, which is wrong, so the mark stands for four obligations.

### DEF-01 — the display double-counts, by its own stated rule

Its preamble warns: *"parent boxes … must not be duplicated as additional conjuncts if their
components are expanded."* The display then carries **both**:
- `A2` **and** `CS1Q_G` — which dedup D-02 declares the same fact at two levels
  (`A2 ← W12-BOX-4/DRAIN-N4 ← GENIND-(CS-1Q)`);
- `A1` **and** `CS1_G ∧ CS2_G ∧ CSExact_G` — which dedup D-03 declares the same fact at two levels.

The ledger's closing paragraph concedes this (*"the frozen theorem should choose either the public
interface or its fully expanded supplier list, not redundantly assume both"*). **So the display is
not a conditional theorem; it is two alternative theorems superimposed.** 0d cannot sign it as
drawn. Both readings are honest — the interface reading is shorter, the expanded reading is what a
formalizer needs — but they must be written as two displays.

### DEF-02 — the MATH-exclusion rule is stated but unachievable as structured

The ledger asserts *"The fifteen MATH rows are blockers to unconditional assembly, not appropriate
hypotheses on `O`; they therefore do not appear in this display."* No MATH row appears **by name** —
but they appear **inside the aggregates**: HYP.09 (cubic triple-root drainage, MATH) is the n = 3
instance of `A2`, which is displayed; HYP.67–71 and 78–80 (MATH) are components or potential
components of `[H-c]`, and `JD1ValuePackage[…]` is displayed. An aggregate containing a MATH
component is not "a hypothesis on `O`" either — it is a blocker wearing a hypothesis's clothes. The
rule and the aggregate-carrying are incompatible; one of them must give.

### DEF-03 — the O/q binder is on the wrong side of the implication

W-12.D reads *"Fix `n` and suppose, **at every prime power q simultaneously**: (A0)(A1)(A2)."* The
display puts `∀ O a complete DVR …` only **after** the `⟹`, leaving `A0/A1/A2/CS*` unbound in `O`.
The hypotheses must be assumed uniformly over `O`; as written they are open formulas.

### DEF-04 — wrong σ-binder on A0/A1/A2 (COR-06), and `A0` is missing its `disc ≠ 0` fence (COR-05)

`A0`, `A1`, `A2` are **fixed-`n`** statements; the τ/σ quantifier belongs in the conclusion. And an
un-fenced `A0` is false — W12 exhibits the equal-characteristic-3 counterexample.

### DEF-05 — missing conjuncts (5 kinds)

1. **`[GENHN-HE(μ ≥ 3)]` and `[GENHN-TOW-1]`** at n ≥ 6 / n ≥ 8 (MISS-01). The display's `∀ n > 0`
   claims coverage it does not have.
2. **`𝒲_{≤i}` at i ≥ 3** — HYP.63, which is a CARRY row, not a NODE (COR-32); T5's accepted record
   displays it as a standing conditionality.
3. **The in-window-pinning half of `(H-e)`** (COR-04) — not dischargeable by the citation swap, so it
   survives as a conjunct.
4. **`(VD-m)`, `(C-coll)`, `(R-coll)`, `PERIM-μ`** inside the `[H-c]` expansion (MISS-02) — `(VD-m)`
   most sharply, being machine-FALSE on 10 of 13 GRTJB roster boundary rows at m = 2.
5. **JB rows 4, 5, 22** hidden inside `JBMembership†` (D-05).

### DEF-06 — the display over-conditionalizes exactly where the theorem is strongest

`∀ n > 0` puts A0–A2 and `[GENIND-H]`'s components on n = 2 and n = 3, where W-12.D *"**FIRES
UNCONDITIONALLY**"* (n = 2) and `[GENIND-H]` is *"**EMPTY**"* (n ≤ 3, GENIND L221–223). The honest
display should carry the low-degree cases as theorems and the hypotheses from n ≥ 4 (with the μ ≥ 3
and n ≥ 8 conjuncts entering at n ≥ 6 and n ≥ 8).

### DEF-07 — the conclusion silently weakens W-12.D

W-12.D concludes `R_τ ∈ ℚ(q)`, equal to the window-mass limit **and the Haar splitting density μ_τ**,
the same expression at every `q`, **and `Σ_τ R_τ(q) = 1`**. The display keeps only the rational-function
equality, drops the sum-to-one, and — per MISS-05 — the Haar identification is a **live open item** on
the Lean side while the informal side asserts it. A weaker conclusion is safe, but 0d must decide
deliberately, not inherit the weakening from a transcription.

### The corrected preview, as two displays

**Display A — the public-interface reading (shortest honest form).** For n ≥ 4; n = 2 is
W-12.D unconditional and n = 3 is conditional on `HMENU3`/`HEX3` only.

    ∀ n ≥ 4,  ∀ 𝒪 a complete DVR with finite residue field of size q:
      [  NS7(𝒪)†                                   (OM termination at all-𝒪 scope)
       ∧ LB1 ∧ MP1                                  (T2 level-one block + peel legs)
       ∧ ∀ i ≥ 3, (H-VARTHETA-RES)_i  ∧  𝒲_{≤i}     (T1/T5 higher-depth residual + window laws)
       ∧ A0_n[disc ≠ 0] ∧ A1_n ∧ A2_n               (W12.D lift / exact menu / drainage)
       ∧ JB-NOLEG(rows 4,5,12,22)†                  (⊋ [H-b])
       ∧ [H-c]† = JD1 value package
             [ (VD-m), (C-coll), (R-coll), PERIM-μ, DMULT-S†, JD0-BOX-2†, W2-VALUE† ]
       ∧ (H-e)-window-pinning                       (the half no citation supplies)
       ∧ [GENHN-HE(μ ≥ 3)]   for n ≥ 6
       ∧ [GENHN-TOW-1]       for n ≥ 8            ]
      ⟹ ∀ σ with deg σ = n, ∃ num, den ∈ ℤ[q] (independent of 𝒪):
           genuineDensity_𝒪(σ) = num(q)/den(q)      [ and Σ_σ = 1 — Q5 ]

**Display B — the expanded-supplier reading.** Identical, except `A0_n ∧ A1_n ∧ A2_n` is replaced by
`∀ G ∈ Genres(n), CS1_G ∧ CS2_G ∧ CS3_G ∧ CSExact_G ∧ CS1Q_G` — **never both** (DEF-01). Note
`CSExact_G` must read *"an **exact** finite q-power-sum menu and an **exact** stage drain — not
asymptotic bounds"* (COR-27), and `CS1_G` sits under **both** the menu and the drainage clause
(D-03).

Changes from the ledger's display: `𝒲_{≤i}` and the two GENHN conjuncts and the `(H-e)` pinning leg
are **added**; `JBMembership` is **widened** to four rows; `[H-c]`'s expansion gains **four named
value-layer hypotheses**; `A0` gains its `disc ≠ 0` fence; the σ-subscripts are **removed** from
A0–A2 and the `∀𝒪` binder moves to the **hypothesis side**; `∀ n > 0` becomes `∀ n ≥ 4` with the
low-degree cases stated as theorems.

---

## CHARGE 6 — VERDICT AND THE 0d PACKAGE

### LEDGER: **NEEDS-RECOMPILE**

**41 row corrections · 16 missed obligations · 9 deduplication defects (5 wrong merges or refuted
claims) · 7 preview-display defects.**

Recompile rather than patch, because the defects are not distributed noise — they cluster in the
places that carry the most weight:
- **Class refutations (2).** `(SEC-RANK)` and `(RISE)` are filed as named obligations; T2's
  acceptance record calls the first *"a CARRIER HYPOTHESIS, **not an obligation**"* and the body
  calls the second *"a carrier hypothesis, **not a ledger obligation**"* at every counter from r7 to
  r12. **T2 has two open obligations, not four.**
- **A disposition refuted by its own cited source (1).** HYP.63's NODE removes `𝒲_{≤i}` from the
  display; the T5 acceptance record displays it as standing. The ledger appears to have read T5's
  **superseded r0 sentence** (still present at L299) instead of the governing r1 text at L616.
- **A statement that asserts the negation of its clause (1).** `CS-EXACT` requires an *exact* drain
  *"not asymptotic bounds"*; the ledger writes *"an explicitly **bounded** drain"* — the precise
  failure mode GENIND displays as breaking the induction.
- **A discharged box reported as open (1).** `GENTOW6-BOX-4`.
- **Locators (29 rows).** 12 rows cite a nonexistent W12 file; 10 cite a nonexistent "T1 effective
  hypothesis list"; 7 cite nonexistent GENIND section names.
- **Two wrong merges** that undercount obligations (`[H-b]` ≡ `JB-NOLEG`; `T3-JOINT-OPEN` ≡
  `F4-JOINT`), and a display that double-counts by its own rule.

**What survives the recompile and should be reused:** the 80-row skeleton and its class taxonomy;
the count arithmetic (internally exact); six of fifteen dedup calls, notably the strong-Hensel
non-merge and the `(MP1′)` retirement; the verbatim-faithful low-degree rows HYP.03/04/05/06/08; the
cite-scope rows HYP.13/15/17; and the idea of the preview display, which is the right deliverable.

### THE 0d PACKAGE — eight owner questions

1. **Trusted base (HYP.15, `NS-7`).** Do we cite [AGNPRW] Thm 5.2 for OM termination over every
   complete DVR — accepting that its index step is itself discharged by citation to ℚ_p-scope
   sources, recorded honestly in `AXIOM_FAITHFULNESS.md` — or spend F-2's 2–4 pages proving
   index-descent internally on the `L4` lattice machinery? *(The source recommends citing. Coupling:
   the cite branch forfeits the `≤ ½ v(disc f)` depth bound that HYP.16 assumes — COR-13.)*
2. **Scheduling + scope (collapses 10 open calls).** Run the `WELD-FACE-AUDIT` (census S-4, one
   session) before the 0d freeze, so the weld residues are carried only if reachable — and if so, do
   we widen its charter from the four rows the census assigns it (HYP.74–77) to also cover HYP.21,
   22, 67, 68, 69, 71 (COR-41)?
3. **Capstone signature (MISS-04).** Sign off `UniformityStatement`'s three live points:
   `∀ 𝒪` over `Type` (universe 0); the rational function evaluated at `(q : ℚ)` with equality read in
   `ℝ` by coercion; `den.eval q ≠ 0` demanded per-`𝒪` rather than globally. *(The note's fourth
   point, `σ.degree = n` doing no work, is self-superseded — `typeOf_degree` landed as gate G13.)*
4. **Definitions (HYP.12, MISS-13, MISS-04).** The `(e,f)` ordering/multiset convention *"deserves a
   human read"*; `W12-BOX-7`'s σ-convention at the TRP tail (two conventions can disagree on
   deep-tail members); and `HENSEL_FACT` §4's faithfulness paragraphs, headed *"FLAGGED FOR ASVIN'S
   REVIEW"*.
5. **What the theorem claims (MISS-05, DEF-07).** Does the frozen capstone assert the **Haar
   density** — as W-12.D and the census do — or only the limit of decided proportions, which is what
   Lean's `genuineDensity` is and which `GENUINE_DENSITY` §3B.4 records the bridge to as
   unformalized? And is `Σ_σ R_σ = 1` inside the frozen statement?
6. **Grade (COR-08).** `JD0-BAR`: run JD0's 2-clean hostile arc, or sign off the 68,523/0 machine
   grade as the bar? *(The census offers both; the ledger silently chose the first.)*
7. **Axioms (MISS-06).** `AX-CELLREC`/`AX-LEAF` faithfulness entries are **DRAFT, PENDING ASVIN
   REVIEW** and the census says they *"gate the LEAN capstone claim"*. Are they on the `leanfinal`
   path at all, or is `leanfinal` Lean-core-only? Same question for census **L-4**, the
   `RealInstanceAt.faithful` placeholder.
8. **Display shape (DEF-01).** Freeze **Display A** (public interface A0–A2) or **Display B**
   (expanded CS-* supplier list) — not both.

### Two items for the corpus, not for Asvin

- **Strike or append T5 L299.** The superseded r0 sentence *"The certified WI note discharges these
  conjuncts"* still sits at HEAD, contradicting the governing r1 text at L616. It already produced
  one bad ledger row; it will produce more.
- **Audit T3 against T1 HEAD (MISS-07).** T3 pins no T1 revision, carries neither
  `(H-VARTHETA-RES)_i` nor `(C3-ladder-nonvanishing)`, and consumes `Θ_N` and `[GENTOW5-W(i)]` at
  i ≥ 3 — the exact sites where T5 concluded both fences must ride. T5's own frame of record is T1
  **r1–r10** while T1 is at **r13**, and r12 introduced the `w_i ∈ K_i^×` gate that T5's `(WF-w)`
  depends on.

---

## ADDENDUM — the generality audits' INTERFACE rows (charge-2 instrument the ledger did not use)

**MISS-17 — the ledger read one of the eight generality audits.** Its coverage statement lists only
*"the qgen Q4 audit summary in `runs/qgen/Q4_output.log`"*. `Q1, Q2, Q3, Q5, Q6, Q7, Q8` were not
read. `CITE_SCOPE_RESOLUTION_2026-08-13.md` (which the ledger *did* read) was built to close only
*"the **H6/`CITE-SCOPE`** findings of the 8-slice generality audit"* — it explicitly does not touch
the audits' **INTERFACE** rows, which are a separate and larger class.

**MISS-18 — the INTERFACE rows are named all-`O` obligations, and none is in the ledger.** Each
audit closes with a table of out-of-slice suppliers plus *"the required generality fact"*, prefaced
(Q7): *"These are out-of-slice and therefore not audited here. **Each must itself be
characteristic-general before the capstone can inherit an all-complete-DVR theorem.**"* Named there
and absent from all 80 rows:

- **`GENIND-1`** (Q1 W12-4) — *"**INTERFACE — load-bearing, unaudited**. `GENIND-1` is essential in
  W12-HT Step 3 and termination/compatibility, but its statement and proof were not pasted. Its
  generality cannot be certified here."* This is a load-bearing supplier of the history-transfer leg.
- **`[RMG]`** (RMENGINE) — *"RM-m, L-CELL, L-LINE, L-EXACT, and L-CANON must hold over arbitrary
  complete/henselian DVRs, not only ℚ_p-extensions."*
- **`[ILN]†`** — *"The standard-lift and realization machinery must exist and satisfy its laws
  equally over `F_q[[t]]`."* Consumed by both GRTJB and GRTJC.
- **`GRB`** — *"Its ladder hypotheses and last-read carry algebra must not rely on `v(p) < ∞`, `p`
  odd, or characteristic zero."*
- **`ITER-LAW`**, **`W-1`/`W-2`/`J-A`/`J-B`**, **`DU lemma`**, **`W-10`**, **`J-D0`**, **`L2core`**,
  the HUMAN_PROOF sub-proofs (`L1_proof`, `M6_lemma`, `BB3_infinity`, `L5fix_complete`), the paper's
  **local-integrals lemma** (*"stated only for unramified p-adic fields here"*) and the
  **`(CONV) = α^{-1}` monic/projective bridge**.
- **Q5's unresolved out-of-slice GENHN count interface**, which Q5 records as affecting *both*
  characteristics — i.e. a correctness interface, not only a generality one.

Some of these are covered *in substance* by the ledger's aggregates (`[H-c]` absorbs the weld
suppliers; HYP.13 absorbs the external citations), but `GENIND-1`, `[RMG]`, `[ILN]†`, `GRB`,
`ITER-LAW` and the HUMAN_PROOF sub-proofs are not, and their required generality facts are the
capstone's all-`O` claim in miniature. **A 0c DAG built from this ledger would have no node for
them.**

**Verified negatives (silence is now evidence).** `grep -rn "sorry"` over `leanfinal/Uniformity` and
`leancheck/UniformityCheck` returns **zero occurrences in code** (two hits, both inside docstrings
asserting the absence). `grep -rn "^axiom "` over both projects returns **zero declarations**. So the
`leanfinal`/`leancheck` layer is Lean-core-only with no banked `sorry` — the ledger's implicit
premise there is correct, and question 7 of the 0d package (`AX-CELLREC`/`AX-LEAF`) is about the
older `lean/` project, not the new one.
