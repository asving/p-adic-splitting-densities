# GRTJC pass PE4 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e.
after the r3 NOTE-ONLY round (commit `126c33f`: the (IN-3)(c) re-route through
§4.2/(MULT-B)|gr at δ = 0, the alias-complete census 90/23-live, GAPs 2–8
dispositions; note byte-identical `126c33f` → HEAD, verified). Runners:
`grt_jc_checks.py` (r0), `grt_jc_r1_checks.py` (r1), `grt_jc_r2_checks.py`
(r2), instrument `grt_jc_probe.py` — all in `verification/openmath/`, all
BYTE-FROZEN at r3 as claimed (md5s verified; `126c33f` touches only the note,
188 insertions / 18 deletions).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **FOURTH acceptance
attempt** (two consecutive clean passes accept; a clean pass here would start
the count).

## VERDICT

**0 CRITICAL · 4 GAPS — NOT CLEAN.** Counter stays **0/2**.

**The r3 diff itself is sound and every machine-checkable figure it added is
exact.** I re-derived the GAP-1 re-route at both §2.8 sites — (MULT-B)|gr at
δ = 0 really does deliver everything JC-LOAD's proof consumed (IN-3)(c) for
(§A1); I reproduced the alias-complete census **exactly** (90 hit-lines at
HEAD; my independent classification lands on the same 23 LIVE = 16 + 7, and
all eight spot-verified live hits cite valid inputs, §A2); the corrected
§9.5 count is right at every commit it names (37/37/24, §M); the GAP-5 δ = 0
one-liner and the GAP-8 corrected trigger re-derive cleanly, with the G-8
mechanism split machine-confirmed (C2C/C3I/C2I are single-non-1-value
(β)-kills; the other 11 decided NOT-CYCLIC rows are (α)-kills, §A3/§A4); the
[r3, G-6] quotations check verbatim against `GRB_ORDER2_2026-08-05.md` §S3.4;
the [r3, G-3] ten-plus-three row split and the [r3, G-4] divisibility data
reproduce exactly (§M(c)). All three batteries + the instrument re-run exit 0
with artifacts byte-identical; strike system balanced (96 `~~` tokens, no
odd paragraph).

What the four gaps are: **the alias species is still not extinct** — §0's own
"THE STACK, ONE LINE" display still cites the refuted-then-re-routed input as
"**FGMN (c)** … CITED" under a FOURTH alias that matches none of the sweep's
patterns, un-superseded since r0 while §10.2's stack was re-stated twice
(G1); §10.1's grade box still ends its arc "**→ JC-PE3 next**" at HEAD — r3
broke the note's own per-round convention of extending that arc, leaving two
contradictory arc displays (G2); the re-routed JC-LOAD proof retains two
**exact-tier constant displays** ("the constant 𝑅(X_N)") inside a proof whose
fence now declares the citable tier, where the multiplier is the anchor
coboundary a_{λ+N}/(a_λa_N), not 𝑅(X_N) (G3); and the census certifies §0's
(IN-3)(c) tag-line hit as "cites a currently-valid input" while the clause's
content line — the very display PE1 quoted among CRITICAL 1's offending
passages — still states freeness on the unsubscripted gr with no annotation,
and is structurally invisible to the census pattern (G4).

---

## §A WHAT I RE-DERIVED (the charges, checked to the bottom)

### A1. Charge (1): the GAP-1 re-route — SOUND at both sites; (MULT-B)|gr at δ = 0 delivers exactly what (IN-3)(c) was consumed for

What the r0 proof consumed (IN-3)(c) for, at both §2.8 sites, is one fact:
*multiplication by X_N acts on the digit polynomial at the line as a constant
multiplier, preserving y-degree.* Re-derived on the declared re-route
footprint: s_{NR}(N) = 0 (JC-FIB, E | N), so δ(γ+γ′, N) = 0 (JC-PER); by
JC-SPAN A(γ+γ′, N) is a monomial of y-degree δ = 0, i.e. a CONSTANT; and
(MULT-B)|gr — which rides (COORD-B)(2) = (1) + (DMULT-w), PE3's §A2
verification — gives 𝑅_{λ+N}(fX_N) = [A(λ,N)·a_{λ+N}/(a_λa_N)]·𝑅_λ(f): a
K_m^*-constant multiplier, y-degree preserved. That is §4.2 verbatim, and it
is all the iff consumes:

* **LHS**: exact y-degree δ (JC-SPAN + the constant multiplier) — tier-blind.
* **RHS**: as c ranges over K^*, 𝑅_N(Λ_N(c)) ranges bijectively over the
  nonzero canonical degree-<g_m representatives (JC-SCAL(a)), and the
  transported set at line γ+γ′+N is that set times a fixed K_m^*-constant —
  which is the SAME set (scaling by a unit constant is a bijection of
  {nonzero polys of degree < g_m}). Tier-blind.
* Moreover the two line-pair units are literally equal (both sites use the
  pair (γ+γ′, N) and ω(λ,μ) = c_{λ+μ}/(c_λc_μ) is symmetric), so they cancel
  exactly, not merely set-theoretically.

Hence "(RAW) solvable ⟺ δ < g_m" survives on (DMULT-w) alone, and consequence
(a)'s y^δ ∉ K_m-span{y^i}_{i<g_m} argument is untouched. **The honest fence's
new footprint statement — "(MULT-B)|gr and with it (DMULT-w)" — is the true
footprint.** The one residue is the retained constant-VALUE display inside
the proof body — **GAP 3** below.

### A2. Charge (2): the alias-complete census — REPRODUCED EXACTLY; 8 live hits spot-verified valid; the alias hunt outside the pattern found ONE surviving alias (G1) and one un-annotated display (G4)

* **Count**: `grep -c '(IN-3)\|Thm 4\.2\|(COORD)\|(MULT)'` on the note at HEAD
  returns **90** (the `-B` forms are excluded automatically by the literal
  closing paren); `Theorem 4.2` returns **0**, as the protocol discloses. ✓
* **Classification, independent (line-by-line, all 90)**: my own pass lands
  on **23 LIVE / 25 STRUCK / 42 RECORD** — the census's exact split — with
  the LIVE set = {L309, L317 (§0); L451, L452, L463 (JC-DOM); L581
  (JC-SPAN); L775, L800, L812, L822 (JC-LOC/G6); L934, L950 (the (DMULT-w)
  derivation); L1017, L1054 ((MULT-B) + its |gr display); L1492, L1496
  (§4.3)} = **16** package/transport citations, plus {L922 (the (DMULT)
  gloss), L1275 + L1296/L1297 (§3.4 title + proof), L1691, L1702 (JC-BOX-3
  [r1] items 1–2), L2230 (§10.2's r1 stack)} = **7** freeness-through-JC-LOC
  sites. **16 + 7 = 23, matching the census bucket for bucket.** The RECORD
  sub-itemization also reproduces (headers 9, R1-BND 2, §9.5's own 18 — all
  exact); 2–3 borderline lines (L631/L755 strike-and-replace bracket
  interiors, L2211 the §10.1 W-8 row with its hits inside `~~…~~`) can be
  assigned STRUCK-vs-RECORD either way under the stated conventions without
  moving totals or the LIVE set — an audit remark, not a defect.
* **Spot-verification of 8 live hits** (charge minimum): L451/L452 (JC-DOM
  consumes (a),(b) — valid, correctly used for the domain + degree
  argument); L581 ((e)/Cor 2.7 within its hypotheses — PE1 §C2 concurs);
  L775 ((b) in JC-LOC — valid); L922 ("the content of (IN-3)(c) on the
  object (IN-3)(c) is about", i.e. through JC-LOC on B — valid); L1296/97
  ("applied — after JC-LOC — to the object Thm 4.2 is about" — valid);
  L1492 ((d), the evaluation isomorphism, for TC-3's identification —
  valid); L2230 ("(DMULT) on B [= FGMN Thm 4.2's content via JC-LOC]" —
  valid). **ZERO live hits name (IN-3)(c)-on-gr, (COORD), (MULT), or the
  Thm-4.2-on-gr_{O[x]} transport — confirmed.**
* **The hunt OUTSIDE the pattern** (grep for `FGMN`, `Cor 2.7`, `Thm 4.8`,
  `Cor 4.9`, `freeness`, `free of rank`, `rank-one` on lines NOT matching
  the census pattern): every hit but two is a strike, a record, or a valid
  B-side statement (the (COORD-B)(2)/§3.4/JC-BOX-3 "free of rank one over
  B_0" displays are all on B — proved in-note). The two exceptions are
  **GAP 1** (L345, "FGMN (c)(d)(e) CITED" — a live stack display under a
  fourth alias) and **GAP 4** (L316, the §0 (c) content line, invisible to
  the pattern). The species the alias-complete sweep was built to end has
  exactly one surviving live instance, and it is in the note's most
  prominent conditionality display.

### A3. Charge (3): the GAP-8 corrected trigger — SOUND, and machine-confirmed

(α) requires image(c) ⊆ {1, ζ′}: two distinct non-1 VALUES defeat it; one
non-1 value satisfies it with ζ′ = that value, so (CYC) can then fail only
through (β). The corrected trigger ("two distinct non-1 VALUES of the
(δ, D)-word") is therefore exactly the (α)-failure condition transported
through JC-INNER's law image(c) = {values of the word} — correct, where the
old word-level trigger was refuted by the note's own C2C/C3I. Machine
(committed `grt_jc_checks_results.json`, re-read this pass): **C2C, C3I and
C2I all carry verdict "NOT-CYCLIC (single value zb^1, carry pattern not
realizable)"** — nvals = 1, the (β) mechanism, exactly the bracket's
counterexample genre (C2C/C3I are the two named collapse-geography
instances; C2I is the same genre off the collapse geography, correctly not
cited by clause (d), which is about collapse rows) — while the other **11
decided NOT-CYCLIC rows all have ≥ 2 distinct non-1 values** (C2B, C2D, C2H,
C3D, C3E, C3F, C3H, C4B, C4G, I4B, I4C; up to 7 on I4C). So the appended
"[r3, G-8: those empirics are carried by (α) AND (β) jointly]" is exact:
11 (α)-kills + 3 (β)-kills among the 14 NOT-CYCLIC. ✓

### A4. Charge (4): the GAP-5 written step — SOUND

Re-derived: wΦ_NR = e_m·g_m·γ_{m+1} (§1's weight law), so e_m | wΦ_NR;
s_{NR}(γ) = l_mγ mod e_m (JC-FIB's proof) gives s_{NR}(wΦ_NR) = 0 and
s_{NR}(n − wΦ_NR) = s_{NR}(n) for every n (s_{NR} is defined by the split
arithmetic on all of ℤ, and the "every n" quantifier correctly reads the
(G5-i)/(G5-ii) transport, as the adjacent [r2, G-5] bracket already
records); hence δ(wΦ_NR, n−wΦ_NR) = (0 + s_{NR}(n) − s_{NR}(n))/e_m = 0, A
is a constant, and the image is ψ_m(y)·Δ on the nose. The e_m = 1 corner:
the monomial-degree-δ form of A rides (DMULT-w) there (JC-BOX-4 [r1]'s
closure), which is the tier the whole display already rides — no new
conditionality. The counterfactual ("were δ = 1 … §3.1 would fail") is a
correct display of what the one-liner is load-bearing FOR. Machine:
e_m | wΦ_NR on **29/29** rows (probe, this pass). ✓

### A5. Charges (5): body veins untouched by PE1–PE3 — re-derived this pass, no defect

* **LEMMA JC-DOM's localization argument** (absent from PE1's §C list,
  claimed re-derived only in the r1 header): gr(w) is a domain — for
  homogeneous classes in(f)in(g) = class of fg, nonzero since w(fg) =
  w(f)+w(g) ((IN-3)(a)); a ℤ-graded ring with no homogeneous zero-divisors
  is a domain. w(π) = E: w₀(π) = 1 and the Φ_j-development of the constant π
  is the single digit A₀ = π, so w_{j+1}(π) = e_jw_j(π); telescoping gives E.
  Localization at a central homogeneous nonzerodivisor is ℤ-graded with
  B_n = ∪_k in(π)^{-k}gr_{n+kE}, injectively (domain). ✓
* **W-9(i)(ii) proper** (PE1 §C6 covered (iv)+JC-F1 only): ρ of anchors = 1,
  so ρ_{a+b}(φ_aφ_b) = A(a,b); associativity + (MULT-B)|gr twice gives
  A(a,b)A(a+b,c) = A(b,c)A(a,b+c) in Δ; reduction mod ψ_m is the K^*
  identity (i); y-degrees add in the domain Δ, and deg A = δ (JC-CARRY-m, on
  the (DMULT-w) footprint valid at every e_m), giving the integer identity
  (ii). ✓
* **JC-CARRY-m's one-line proof**: JC-SPAN + division by a_{γ+γ′} + the
  definition of A in (MULT-B)|gr. ✓ (And "pre-TC-3 a K-scalar iff δ < g_m"
  is JC-LOAD's iff, correctly cited.)
* **The maxslot display** (§2.10): on-line abscissa a satisfies
  e_m·w_m(A_a) + aγ_{m+1} = λ with w_m ≥ 0 ⟹ a ≤ λ/γ_{m+1} ⟹ slot
  k = (a − s_{NR})/e_m ≤ maxslot(λ). ✓
* **§7 rows 2/3/6/7/9–11** (row 1 was PE1's GAP 4; rows 4/5/8 carried by
  JC-LOAD/JC-BOX-4/§2.10): row 2 (δ = 1 < g_m ⟹ RAW-solvable) is JC-LOAD's
  iff; row 7 (C4A, |K| = 2 ⟹ c ≡ 1) matches the artifact ("CYCLIC (c == 1
  identically)", nvals = 0); rows 9–11 correctly claim nothing beyond their
  boxes. ✓
* **§6(a)(c)(e)**: (a) is JC-F1 (PE1 §C6); (c)'s |K| = 2 and
  ≤-one-non-1-value clauses re-derived (definitional); (e)'s "no row
  re-scored" confirmed against the byte-frozen record citations. ✓

### A6. Charge (6): strike system + [r1..r3] consistency

96 `~~` tokens, every paragraph even — balanced. All eight PE3 gaps carry
`[r3, G-#]` brackets at their sites (15 bracket occurrences: G-1 ×4, G-3 ×4,
G-8 ×2, G-2/4/5/6/7 ×1 each), each strike-and-replace, nothing silently
deleted; the [r3] S-STATUS block correctly supersedes [r2]'s (kept annotated
for its ARC display, with the reason stated); the ARC's commits and figures
all check against `git log` (PE1 report `1a27be3`, PE2 `4a76d52`, PE3
`e4b6fbf`, r1 `85d5811`/`54904cc` + mini-seal `f45b63c`/`66263ce`, r2
`5742e25` + mini-seal `79611a4`/`db12666` — every recorded hash verified).
The two defects found are G2 (the §10.1 arc not extended at r3) and the G1
stack display (never superseded at any round).

---

## GAP 1 — §0's "THE STACK, ONE LINE" still cites the re-routed input as "FGMN (c) … CITED": a live conditionality display under a FOURTH alias, outside the alias-complete pattern, un-superseded since r0

**Offending passage (verbatim), §0:**

> **THE STACK, ONE LINE.** Every clause of §§2–5 rides
> `[ILN]† ACCEPTED (scored stratum) + GRB/CARRY-1 ACCEPTED-conditional (§0 ladder) + FGMN (c)(d)(e) CITED + W-1/W-2/J-A/J-B ATTEMPT (0/2)`,
> and this note's own arc starts at **0/2**.

This is the r0 stack, byte-unchanged through r1/r2/r3, in the section headed
"read before any clause". Since r1, the note's own current stack (§10.2 [r1],
re-ranked [r2]) replaces the FGMN entry with "(DMULT) on B [= FGMN Thm 4.2's
content via JC-LOC]" and W-6's [r1] grade line declares the calculus rides
(DMULT-w) "instead of (IN-3)(c)-on-gr"; since r2 the entry is further split
into tiers ((DMULT-w) CITED-derived / (DMULT-s) MEASURED). §0's one-liner
carries none of that: it cites clause (c) bare, with no JC-LOC re-aim and no
tier split (and it lists (c)(d)(e) while the note also consumes (a)(b) —
JC-DOM, JC-LOC, G6 — so it is not even the right r0 list). It survived all
three sweeps because "FGMN (c)" matches none of the swept names — `(IN-3)`,
`Thm 4.2`, `(COORD)`, `(MULT)` — i.e. it is exactly the species [r3, G-1]'s
protocol was widened to end, under a fourth alias the widened pattern still
does not contain. Content-wise the citation is *recoverable* (the calculus
does still ride (c)'s content, through JC-LOC, as (DMULT-w)), so nothing
false is concluded — but the note's most prominent conditionality display
contradicts its own current stack in form, three rounds after the re-aim.
**Classification: JUSTIFICATION GAP** (stale conditionality display; the
alias census's "at fixed point under its aliases" headline is true of its
own pattern and not of the input's alias set).

## GAP 2 — §10.1's grade box still ends its arc "→ JC-PE3 next" at HEAD: r3 did not extend the arc record it was the note's own convention to extend

**Offending passage (verbatim), §10.1:**

> **[r2] Arc: composed (0/2) → JC-PE1 (2 CRITICAL + 8 gaps) → r1 (STRUCTURAL)
> → JC-PE2 (0 CRITICAL + 9 gaps; "no false statement") → r2
> (labelling/footprint/disclosure + the bilinearity machine leg, §9.4) →
> **JC-PE3 next**.** Acceptance counter **0/2** (a repair round is not a
> pass). **[r2] Grade deltas at r2: NONE …**

At HEAD, JC-PE3 has RUN (0 CRITICAL + 8 gaps, report committed `e4b6fbf` —
the top [r3] S-STATUS block records it correctly) and r3 is applied — so the
note carries two arc displays, one current (header: "JC-PE4 = the next
acceptance attempt") and one stale ("JC-PE3 next"), the stale one inside the
"read this first" grade box, un-struck and un-annotated. r2's own precedent
struck r1's arc line here and wrote the [r2] one; r3 wrote nothing, and there
is also no "[r3] Grade deltas: NONE" line, so a reader of §10.1 alone cannot
see that r3 moved no grades (true, but recorded only in the header). Same
species as LIFTCORNER PE6's status-block finding. **Classification:
JUSTIFICATION GAP** (bookkeeping; two contradictory arc records coexist at
HEAD).

## GAP 3 — the re-routed JC-LOAD proof retains two EXACT-TIER constant displays under its newly declared citable-tier footprint: "the constant 𝑅(X_N)" is a (DMULT-s) value

**Offending passages (verbatim), §2.8 (the un-struck words around the [r3,
G-1] bracket):**

> *Proof.* Multiplying by X_N transports lines additively and, by
> ~~(IN-3)(c)~~ **[r3, G-1 — …Re-routed: by §4.2]** and JC-SCAL(b),
> multiplies the digit polynomial by **the constant 𝑅(X_N)** without
> changing its y-degree …

> So by JC-SPAN the LHS has digit polynomial **𝑅(X_N)·u·y^δ**, of exact
> y-degree δ; by JC-SCAL(a)(c) the RHS ranges exactly over
> **𝑅(X_N)·{polynomials of degree < g_m}** …

On the footprint the fence now declares — (MULT-B)|gr riding (DMULT-w) — the
multiplier that multiplication by X_N applies to 𝑅 is
A(λ,N)·a_{λ+N}/(a_λa_N); with the in-note κ = 1 pinning this evaluates to
the anchor coboundary **a_{λ+N}/(a_λa_N)**, which equals 𝑅(X_N) (= 1, §4.1)
exactly when ω(λ,N) ≡ 1 — i.e. on **(DMULT-s), the MEASURED tier**. The
conclusion is unaffected: the iff consumes only "a K_m^*-constant, y-degree
preserved" (§A1 — the unit is the same on both sides and cancels), and PE1
§C3 had already graded the constant slop in this display harmless. But the
note's own r2 discipline is that every sharp-constant display carries the
(DMULT-s) fence (verified at every JC-COB site by PE3 §A2), and this proof —
the one r3 just re-fenced onto the citable tier — displays a sharp constant
with no tier flag. **Classification: JUSTIFICATION GAP** (tier-hygiene
residue of the repaired species; one bracket or a "up to the line-pair
constant" rewording discharges it).

## GAP 4 — the census certifies §0's (IN-3)(c) tag-line hit as "cites a currently-valid input" while the clause's CONTENT line — PE1's own quoted offending passage — still displays freeness on the unsubscripted gr, un-annotated and invisible to the census pattern

**Offending passages (verbatim).** §0:

>     (c) gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y] on the anchor basis
>         in(φ_γ) at attained γ  [Thm 4.2];

and §9.5 [r3, G-1]:

> The verified fixed point: **every LIVE hit cites a currently-valid input**
> — 16 are (IN-3)(a)/(b)/(d)/(e) or the (IN-3) package/transport-clause
> citations (§0, …)

The (c) display's first line matches none of the census patterns (the
`[Thm 4.2]` tag sits on the next line), so the protocol sees this clause
only through its tag — and certifies that hit valid. Read against §1's
definition of gr(w) (the note's only definition of the unsubscripted symbol:
the O[x] object) the displayed clause is the proposition PE1's CRITICAL 1
refuted on the note's own roster, and PE1 quoted exactly this §0 display
among the offending passages; r1 restated every APPLICATION on B but never
annotated the §0 display itself. The defensible reading — these are FGMN's
statements about FGMN's objects, gr = gr_K per the §S6a quotation five lines
up — is the one the note intends (JC-BOX-3 [r1]: "uses FGMN Thm 4.2 only on
B …, never on gr_{O[x]}"), but the disambiguation lives three sections away
and the clause's own line, with its window-flavored "at attained γ", never
received the one-line bracket every other formerly-misaimed display got.
**Classification: JUSTIFICATION GAP** (un-annotated object-ambiguity in the
input display; also a disclosed-protocol limit — the census counts hit-LINES
by NAME, so refuted content whose name-tag sits on an adjacent line is
outside its resolution, which §9.5 does not say).

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All
three batteries overwrite their `*_results.json` on execution; `git status`
on `verification/openmath/` after all reruns + the instrument: **clean** —
every committed JSON artifact reproduced byte-for-byte.

### (a) Seals, md5s, and the r3 commit shape — all verified

* Note **byte-identical** at `126c33f` and HEAD (`git diff` empty); r3
  touches ONLY the note (188 insertions / 18 deletions, no `verification/`
  file, no `.lean`). ✓ "batteries + instrument + artifacts BYTE-FROZEN" is
  literally true.
* md5s at HEAD, all equal to their sealed values: r0
  `adb555e1134d3ae0b0174d62e8b3446c`, r1
  `7f896bfa27d06158f95c5987c7299770`, r2
  `c02bf06029a72259512ea005bd2562fd`, instrument
  `03811b695cf7aa1bd5b52d5b0cd8bcd6`. ✓
* ARC hashes: PE1 report `1a27be3`, PE2 `4a76d52`, PE3 **`e4b6fbf`** (the
  [r3] S-STATUS records `e4b6fbf`; `git log` confirms: `e4b6fbf` "GRTJC
  passPE3 report") ✓; r2 note repairs `5742e25` + mini-seal
  `79611a4`/`db12666` ✓ all confirmed in `git log`.

### (b) The three batteries + instrument — all reproduced, exit 0

* **r0** `grt_jc_checks.py`: exit **0**, 2.0 s, 0 violations, silent teeth
  NONE; stdout vs committed `grt_jc_checks_output.txt` byte-identical except
  ONE per-row wallclock digit (C4I 1.0→0.9). Headline figures (8,566
  samples, 10 families, 1,054 tooth firings, cyclic split 6/14/9) as
  committed.
* **r1** `grt_jc_r1_checks.py`: exit **0**, 0 violations; stdout vs
  `grt_jc_r1_output.txt` byte-identical except ONE wallclock digit (C3A
  0.4→0.3). R1-COB 869/869, R1-UNIT census 869/0/0/0, PSIK 197/197 — all as
  the §9.3 cells state.
* **r2** `grt_jc_r2_checks.py`: exit **0**, 0 violations; stdout vs
  `grt_jc_r2_output.txt` **byte-identical**. 261 dense pairs, deg-3 dense
  29/29, skip census 29 with bilinear content exactly ['C2I','C4I'], U2
  fired 0 times on r1-TESTED pairs — all as the §9.4 cells state.
* **instrument** `grt_jc_probe.py`: exit **0**, 18.3 s, total violations 0.

### (c) The r3-added figures — every one verified this pass

* **[r3, G-2] the corrected count**: the recorded grep returns **37** at
  `5742e25`, **37** at the pre-r3 note state (`126c33f^`), **24** at
  `66263ce` — exactly the three figures the correction states. (At r3 close
  the old-pattern count is 42, a figure the note does not claim; its r3-close
  claim is the new census, below.)
* **[r3, G-1] the alias-complete census**: **90** hit-lines at HEAD ✓;
  `Theorem 4.2` **0** ✓; independent classification **23/25/42** with LIVE
  = 16 + 7 bucket-exact (§A2). ✓
* **[r3, G-3]**: probe re-run of the frozen `build_dense` composition — the
  ten `elems[1] == 1` rows are EXACTLY (C2A, C2B, C2E, C3A, C3D, C3E, C3I,
  C4B, C4G, I4A); the three K_m^* = {1} rows are EXACTLY (C2I, C4A, C4I);
  mix2 == ones2 **byte-identical on exactly those 13 rows**, including both
  g_m = 2 rows. ✓ (PE3 had verified byte-identity on 3 rows; this pass
  verified all 13.)
* **[r3, G-4]**: E | wΦ_NR on exactly {C2D, C2I, C2J, I4A} (4/29, false on
  25); e_m | wΦ_NR on **29/29**; C2A has E = 4, wΦ_NR = 10. ✓
* **[r3, G-6]**: all five quoted fragments verified VERBATIM against
  `GRB_ORDER2_2026-08-05.md` §S3.4 read this pass — the enlarged closed
  scope "{all order-2} ∪ {order-3 all-e_j = 1}" (second bracket), the HV3
  third bracket changing that same stratum's conditionality only, TR3-S1
  "σ₁(R^F₂(f)) = R_λ(f) EXACTLY", TR3-S3 "σ₂(R^F₃(f)) = R_λ₃(f) EXACTLY —
  discrepancy ≡ 1, per-argument units ≡ 1", and "the units-only phrasing of
  the record statement below is PERMANENTLY REFUTED on (ii)". ✓
* **[r3, G-8]**: committed r0 JSON — C2C/C3I (and C2I) = "NOT-CYCLIC
  (single value zb^1, carry pattern not realizable)", nvals 1; the other 11
  decided NOT-CYCLIC rows have 2–7 distinct non-1 values. ✓
* **Strike system**: 96 `~~` tokens, 0 paragraphs with odd count; 15
  `[r3, G-#]` brackets covering all eight gap keys. ✓
* **[r3, G-7]**: the R1-COB prereg quotation is byte-intact before the
  appended annotation (diff-verified), and the annotation's two-mode blast
  radius matches JC-COB's §2.10 display word for word in content. ✓

### (d) Read-only probes written for this pass (outside the scored surface, nothing staged)

In-terminal python probes importing the frozen `grt_jc_probe` +
`grt_jc_r2_checks` modules (computing nothing new): (i) per-row E, wΦ_NR,
divisibility — GAP/[r3, G-4]'s data; (ii) per-row nonzero-element
enumeration + `surj_build` byte-comparison — [r3, G-3]'s data; (iii) the
committed r0 JSON's per-row cyc records — [r3, G-8]'s data. Greps executed
against `git show` states, never against a working copy.

---

## §C WHAT SURVIVED THE PASS (beyond §A; re-checked, no defect found)

1. **The [r3] S-STATUS + dispositions block** — arc figures, commit hashes,
   gap keying, and the "no measured quantity moves at r3" claim all exact;
   the note-only discipline is literally verified (commit shape).
2. **The [r3, G-3] disclosure block** — every figure machine-exact (see
   §M(c)); the species record's three-recurrence history matches the
   PE2-G2 → r2 → PE3-G3 record; the candidate leg is NAMED and genuinely
   NOT built (no new script, verified); the standing rule is a fence, not a
   claim.
3. **The [r3, G-4] replacement reason** — e_m | wΦ_NR ⟹ s_{NR}(wΦ_NR) = 0
   re-derived (s_{NR} = l_mγ mod e_m) and machine-confirmed 29/29.
4. **The [r3, G-6] rewrite** — now quotation-faithful on all points PE3
   listed (one stratum; exactness where closed on (i); units-only refuted on
   (ii)); the load-bearing openness claim ("OPEN beyond that closed scope")
   correctly retained.
5. **The [r3, G-5] bracket** — sound (§A4), and correctly placed so the
   ideal-piece display is an equality with its reason attached.
6. **The [r3, G-8] brackets** — sound (§A3); clause (b)'s graded first
   sentence unchanged; the empirics-attribution appendix is the honest form.
7. **The re-routed honest fence** (§2.8) — now states the true footprint
   ((MULT-B)|gr → (DMULT-w)), matching §4.2's actual proof since r2.
8. **Header/status hygiene elsewhere** — counter 0/2 at every occurrence; no
   gate fires/retires; no density/menu/count statement; JC-BOX-2/8(i)
   residues still displayed as having no machine leg on any runner.

---

## §R RECOMMENDATION

**Not clean; 0 CRITICAL, 4 gaps; counter stays 0/2.** The r3 diff itself
introduced no defect I could find — every inserted figure, quotation, and
derivation verified — and the charges' mathematical content (the re-route,
the trigger, the δ = 0 step) is sound. All four gaps are one-to-three-line
repairs in what r3 left untouched:

1. **G1/G4 (the alias species, final instances):** supersede §0's "THE
   STACK, ONE LINE" with the current §10.2 form (or bracket it as the r0
   stack, superseded), and give §0's (c) display the one-line bracket ("an
   FGMN statement about gr_{K[x]}; applied in this note only through
   JC-LOC/(DMULT-w), §2.10") that every other formerly-misaimed display
   already carries. Widen the census protocol note to say it is
   NAME-pattern-based (content lines without name tags are outside its
   resolution).
2. **G2:** extend §10.1's arc through JC-PE3/r3 → "JC-PE4 next" and add the
   one-line "[r3] Grade deltas: NONE".
3. **G3:** re-word JC-LOAD's two constant displays to the tier-honest form
   ("by a K_m^*-constant — equal to 𝑅(X_N) on (DMULT-s)") or bracket them.
4. PE5 should re-run the widened grep (expect the count to move with the
   fixes), check the §0 stack supersession, and — if clean — start the
   acceptance count. The weakest mathematical links remain §10.2 [r2]'s
   ranking, headed by (DMULT-w) + W-1's transport; nothing found this pass
   moves that ranking.

— GRTJC pass PE4, hostile verifier unit (fresh context), fixes nothing.
