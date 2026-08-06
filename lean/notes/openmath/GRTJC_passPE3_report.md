# GRTJC pass PE3 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e. after
the r2 LABELLING+FOOTPRINT round (commits `5742e25` note repairs / `79611a4` r2
runner sealed UNRUN / `db12666` verdict + artifacts). Runners:
`grt_jc_checks.py` (r0), `grt_jc_r1_checks.py` (r1), `grt_jc_r2_checks.py` (r2),
instrument `grt_jc_probe.py` — all in `verification/openmath/`.
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **Third acceptance
attempt** (two consecutive clean passes accept; a clean pass here would start the
count).

## VERDICT

**0 CRITICAL · 8 GAPS — NOT CLEAN.** Counter stays **0/2**.

**The r2 tier split is mathematically sound and survives full hostile
re-derivation.** I re-derived from scratch: the (DMULT-w) derivation (§A1 — the
§0 transport really does deliver exactly the up-to-unit-cocycle form, with
ω = c_{λ+μ}/(c_λc_μ) forced); the κ = 1 pinning inside (COORD-B)(2)'s re-run
proof (§A2 — JC-PIINV(c) genuinely pins the combined constant without ever
touching ω, so the citable tier suffices); the full consumer split (§A2 — **no
hidden (DMULT-s) consumption found**: every load-bearing clause rides (DMULT-w),
and every site displaying JC-COB's sharp value carries the (DMULT-s) fence); the
G6 derivation including the new additivity leg (§A3 — sound, and the residual tie
really is W-1 and nothing more); JC-INNER, §4.3 and JC-CYC(b)(c), the body veins
neither PE1 nor PE2 re-derived (§A5). **Machine leg: all three batteries
reproduced exactly, exit 0, JSON artifacts byte-identical, all seals verified**
(§M).

What the eight gaps are: the r2 sweeps have **leaks of their own species** — a
THEOREM proof (JC-LOAD) still consumes the PE1-refuted `(IN-3)(c)`-on-gr by name
at two live sites, missed because the fixed-point grep covered only
`(COORD)`/`(MULT)` (G1); the §9.5 sweep record's own machine-verifiable count is
**wrong at its own commit** (the grep returns 37 hit-lines, not 22; the
"3 in this §9.5 record itself" is actually 11) though its load-bearing half
(0 live consumers) is verified TRUE (G2); the new bilinearity leg's sample
diversity is overstated — on **13 of 29 rows, including BOTH g_m = 2 rows**, the
"mix2" dense element is byte-identical to "ones2", undisclosed (G3); one §9.4
verdict cell attaches a **false justification** ("E | wΦ_NR", false on 25/29
roster rows) to a true measured fact (G4); one load-bearing one-liner
(δ(wΦ_NR, ·) = 0 in the TC-3 display) is true but unwritten (G5); the TR-3′-GEN
gloss misquotes the record's closed scope in two ways (G6); the frozen R1-COB
prereg row's blast-radius claim contradicts the post-split JC-COB fencing and
carries no [r2] annotation (G7); and JC-CYC(b)'s mechanism gloss is false as
stated, refuted by the note's own mechanism-2 rows (G8).

---

## §A WHAT I RE-DERIVED (the charges, checked to the bottom)

### A1. Charge (1): the (DMULT-w) derivation — SOUND; the transport delivers exactly this and no more

Re-derived independently. §0's (IN-3) transport clause is, verbatim, "R_{m,λ} =
c·R_λ^{GMN} with c a line-wise unit". Substituting 𝑅_λ = c_λ·R^{GMN}_λ into the
GMN-gauge identity R^{GMN}_{λ+μ}(fg) = y^δ·R^{GMN}_λ(f)·R^{GMN}_μ(g) gives

    𝑅_{λ+μ}(fg) = (c_{λ+μ}/(c_λc_μ))·y^δ·𝑅_λ(f)·𝑅_μ(g),

i.e. ω(λ,μ) = c_{λ+μ}/(c_λc_μ) — the displayed 2-coboundary, dependent on the
lines only (c is line-wise), a K_m^*-unit, with **nothing giving ω ≡ 1**. This is
exactly what the note now claims and no more. Two grounding checks:

* **The GMN-gauge exact identity is corpus-grounded at arbitrary order.** The
  mechanism is pinned in `GRB_ORDER2_2026-08-05.md` §S6a: (W-MULT) is proved
  there (at GRB's layer) from Thm 4.2 three times + the FGMN anchors being
  MONOMIALS x_r^s p_r^u (eq (16), pinned verbatim at S6.2), whose products carry
  the carry with **no unit** — which is precisely why exactness holds in the
  FGMN/GMN gauge and fails to transport: the harness anchors are integral
  polynomial lifts with digit constants a_γ ≠ 1. The numbering re-verification
  stays owed and stays boxed (JC-BOX-3 item 2, unchanged) — correctly.
* **The measured/not-cited status of (DMULT-s) is honest.** TR-3′-GEN's
  statement of record is quoted verbatim-faithfully (checked against
  `GRB_ORDER2_2026-08-05.md` §S3.4, both the REV-11 form and the acceptance-era
  record), it is stated with per-argument units, and it is OPEN at general
  order. The note's proving-ω≡1-would-mean line (c_{λ+μ} = c_λc_μ, the ε-kit's
  unit system multiplicative) is the correct characterization. The gloss on the
  record's CLOSED scope has two misquotes — see **GAP 6** — but they do not
  touch the openness claim the split rides on.

### A2. Charge (2): the consumer split — VERIFIED; no hidden (DMULT-s) consumption

* **The κ = 1 pinning re-derived** (the heart of "(COORD-B)(2) from (1) +
  (DMULT-w)"). Representing t ∈ B_0 at line kE and β ∈ B_n at line n+k′E,
  (DMULT-w) + division by anchors gives ρ^B_n(tβ) = κ·ρ^B_0(t)·ρ^B_n(β) with
  κ = ω·a_{kE}a_{n+k′E}/a_{n+(k+k′)E} line-dependent only. Taking t = in(φ_{kE})
  = in(π^k): ρ^B_0(t) = 1 (definitional) and ρ^B_n(π^kβ) = ρ^B_n(β) EXACTLY by
  JC-PIINV(c) (proved in-note), so κ = 1 for every line pair of the shape used —
  and every pair the proof needs has that shape (0 mod E × n mod E). The
  argument pins the COMBINATION κ, never ω itself, which is exactly why the
  citable tier suffices. **Sound.**
* **Consumer-by-consumer:** (COORD-B)(2) ✓ (above); (MULT-B) ✓ (only
  Δ-bilinearity = (COORD-B)(2), plus the (G5-i)/(G5-ii) transport, re-derived,
  k-independence = JC-PER + JC-PIINV(c)); JC-CARRY-m ✓ (JC-SPAN + (MULT-B)|gr);
  W-8 ✓ ((†) definitional, (‡) on (MULT-B)|gr, 𝑅_N(X_N) = 1 from R3 +
  JC-SCAL(b) + K_m ↪ K — no DMULT tier at all in that step); JC-BOX-4's corner
  closure ✓ (ω·y^δ·a_γa_{γ′} is a monomial of degree exactly δ whatever ω ∈
  K_m^*); JC-IND/§3.4 ✓; JC-F1's dimension count ✓; W-9(i)(ii)(iv) ✓
  ((MULT-B)|gr only). **Every site displaying JC-COB's sharp value carries the
  (DMULT-s) fence** (checked at: §2.10 JC-COB + its second half, the tier-split
  block's who-consumes paragraph, §4.1 remark (a) both brackets, §3.4's honest
  rider, JC-BOX-3 items 1/3, JC-BOX-4, JC-BOX-8(iii), §10.2 [r2] stack, R1-COB's
  §9.3 verdict cell). JC-INNER's u = a_{γ+γ′}∏z_j^{D_j} comes from W-8 + [ILN]†,
  not from JC-COB — no tier leak there either.
* **What the hunt DID find** is not a tier leak but a stale-citation leak of the
  G-4 species: JC-LOAD's proof body and its honest fence still consume
  `(IN-3)(c)` by name — **GAP 1** — and the frozen R1-COB prereg row still
  carries the undifferentiated blast radius — **GAP 7**.

### A3. Charge (3): the G6 derivation — SOUND; the residual really is W-1

* **G6-1 (extension forced):** any valuation on K[x] restricting to w with
  w^K(π) = E satisfies w^K(π^{-k}g) = w(g) − kE; well-definedness via w(πf) =
  w(π) + w(f) checked. ✓
* **G6-2 (the min-formula computes it):** the Φ_j-development of π^{-k}g is
  π^{-k}·(development of g) (uniqueness of the development, deg preserved under
  scaling by a constant), and the induction w_{j+1}(π^{-k}f) = w_{j+1}(f) −
  k·e_0⋯e_j closes with base w_0 dropping by exactly k; at j = m this is the
  extension formula. ✓
* **G6-3 (valuation):** multiplicativity via (IN-3)(a) on O[x] after clearing
  π-powers; ultrametric inequality from termwise addition of developments +
  min subadditive, stable under subtracting kE. ✓
* **The additivity leg of JC-LOC** (PE2 GAP 6's second half): common
  denominator, then the gr^O dichotomy (in(g)+in(g′) = in(g+g′) if weight
  attained, 0 if it drops) maps to the SAME dichotomy in gr^K via the extension
  formula. ✓ Both cases carried.
* **The residual:** G6-1..3 tie the extension to the min-formula valuation on
  K[x] in the harness normalization; what remains is harness-w = literature
  v_{m+1} + 𝑅 vs the literature operator up to line-wise unit — which is
  (IN-3)'s W-1 transport clause verbatim, already in §0's stack, and the note
  adds no new input here. **The claim "residual = W-1, already priced" is
  correct.**

### A4. Charge (4): the r2 battery — code audited in full; predicates independent; teeth genuinely separating

`grt_jc_r2_checks.py` (399 lines, read whole): R2-BIL's predicate is the SAME
frozen (DMULT) predicate PE2 audited (Rpoly/pmul/pshift/delta_of **imported**
from the byte-frozen r1 module, verified at line 121); lhs from `read_coeffs` of
the schoolbook product, rhs from the factors' reads + split-data δ, exact dict
equality; each dense element is itself verified (w = n+kE, 𝑅 = target on the
nose) before any pair is scored. The dense targets have 3–4 occupied slots with
occupied interiors on BOTH factors, so the cross-term convolution (a₁b₁ into
slot 2+δ) is genuinely exercised — the samples ARE multi-slot × multi-slot
(modulo the duplicate of **GAP 3**). U2's design claim re-derived: with ≤ 2
occupied slots every index is extremal, so `mut_pmul` = `pmul` — U2 is PROVABLY
silent on every r1-tested pair (one factor always ≤ 2-slot: ψ_m is 2-slot on the
27 g_m = 1 rows) and provably live on dense × dense (the dropped a₁b₁ ≠ 0 over a
field moves one coefficient); the machine confirms both halves (261/261 fires on
dense pairs, 0 fires replayed on r1-tested pairs, scored as R2-MONO(c)). The
R2-PHI census (skip = exactly 1 pair/row; bilinear content exactly C2I/C4I, the
two g_m = 2 rows) reproduced and verified. Family arithmetic: 1 + 696 + 87 +
2,813 + 58 = 3,655 ✓; 261 = 29 × 9 ordered dense pairs ✓; dense k-ranges 5..34
(deg 2) and 7..52 (deg 3, realized 29/29) ✓ against the committed output.

### A5. Charge (6): body veins untouched by PE1/PE2 — re-derived

* **THEOREM JC-INNER (§3.3).** c_{m+1} = c_val (W-8) = c_T ([ILN]† on exactly
  the scored stratum; the c_val ↔ [ILN]† identification is the one PE1 §C7
  verified against ITERLAWN §S0.2). Second form: divide by z̄^δ (unit, ψ_m(0) ≠
  0); both u/a_{γ+γ′} and ∏_{j≤m}z_j^{D_j} lie in K_m, and K_m ↪ K is
  injective, so the K-identity descends to K_m^*. **Sound**, with the stratum
  and e_m ≥ 2 fences carried. The germ-split bullet's arithmetic (κ ranging
  over {1,z̄,…,z̄⁴} with κ·val(φ_{e_mγ_{m+1}}) = −z_{m+1} on 27 stages) is
  instrument-carried and quoted within its J-B fences.
* **§4.3 (J-C(iii)).** The residue chain is the same tower by construction;
  TC-3's identification is (IN-3)(d); the inner unit is literally a word in
  z_1..z_m of that tower. No independent content, as graded. ✓
* **LAW JC-CYC(b)(c) (§6).** (b)'s graded first sentence is correct (two
  distinct non-1 values defeat (α) trivially); its mechanism gloss is FALSE as
  stated — **GAP 8**. (c) re-derived: |K| = 2 gives c ≡ 1, and (β) holds with
  σ ≡ 0, carry ≡ 0 (0 = 0); the "at most one non-1 value AND (β) solvable"
  clause is definitional. ✓

---

## GAP 1 — JC-LOAD's proof body and honest fence still consume the PE1-refuted `(IN-3)(c)`-on-gr BY NAME at two live sites; the r2 fixed-point sweep missed them because its grep covered only `(COORD)`/`(MULT)`

**Offending passages (verbatim), §2.8:**

> *Proof.* Multiplying by X_N transports lines additively and, by (IN-3)(c) and
> JC-SCAL(b), multiplies the digit polynomial by the constant 𝑅(X_N) without
> changing its y-degree (offset transport, §4.2; note s_{NR}(N) = 0 so
> δ(γ+γ′,N) = 0).

> *Honest fence.* The proof of the ⟸ direction rides the offset-transport step
> (§4.2), which rides (IN-3)(c);

`(IN-3)(c)` as stated in §0 is "gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y]" —
the statement PE1's CRITICAL 1 **refuted on the note's own gr** and r1 re-aimed
through JC-LOC onto B, with W-6's [r1] grade line declaring the calculus now
rides "(DMULT-w) … instead of (IN-3)(c)-on-gr". §4.2 at HEAD applies
"(MULT-B)|gr [r2, G-4]", which rides (DMULT-w) — so JC-LOAD's honest fence
misstates its own repaired footprint, and its proof body invokes the refuted
citation un-bracketed inside a THEOREM. Both sites are *recoverable* (the step
used is exactly §4.2 = (MULT-B)|gr at δ = 0), so nothing false is concluded —
but a theorem proof at HEAD names an input the note itself refuted, three
sections after striking it everywhere else. §9.5's protocol discloses honestly
that the grep pattern was `(COORD)`/`(MULT)` only; these two sites are the
pattern's blind spot. **Classification: JUSTIFICATION GAP** (recoverable stale
citation; the exact species [r2, G-4] was repairing).

## GAP 2 — §9.5's sweep record misreports its own machine-verifiable count AT ITS OWN COMMIT: the recorded grep returns 37 hit-lines, not 22, and the "3 in this §9.5 record itself" is actually 11

**Offending passage (verbatim), §9.5:**

> **Fixed-point re-grep, protocol and result:** grep for `(COORD)`/`(MULT)`
> excluding `-B` forms; … Count at r2 close: the grep returns **22 hit-lines**,
> classified: **11** inside `~~…~~` strikes or strike-and-replace brackets …,
> **4** in the r1 repair-history header …, **2** R1-BND rows …, **3** in this
> §9.5 record itself, **2** in [r2, G-4]'s own quotation brackets … = 22.
> **0 live consuming sites**

Executed at HEAD and at `5742e25` (the very commit that wrote this record):
`grep -c '(COORD)\|(MULT)'` returns **37** hit-lines both times (24 pre-r2 at
`66263ce`). Reclassified line by line this pass: **17** in strikes /
strike-and-replace brackets, **4** in the r1 repair-history header, **1** in the
r2 dispositions header (unclassified by the record), **2** R1-BND rows, **11**
in §9.5 itself, **2** in [r2, G-4]'s quotation brackets = 37. The recorded count
appears to have been taken before §9.5 itself (and some [r2] brackets) were
written, then committed unrefreshed — in a record whose whole purpose is a
fixed-point claim. **The load-bearing half survives my independent
classification: all 37 hits are strikes, quotations, repair-history narrative,
refutation citations (R1-BND), or the sweep record itself — 0 live consuming
sites, verified.** (The `(IN-3)(c)` leak of GAP 1 is outside this grep's pattern,
not a counterexample to it.) **Classification: JUSTIFICATION GAP**
(machine-record arithmetic — the same defect species as PE2's GAP 8, inside the
record that was closing PE2's GAP 4).

## GAP 3 — R2-BIL's sample diversity is overstated: on 13 of 29 rows — including BOTH g_m = 2 rows — the "mix2" dense element is BYTE-IDENTICAL to "ones2", so "9 dense pairs from THREE elements" is really 4 distinct pairs from two; undisclosed

**Offending passage (verbatim), §9.4 verdict:**

> | **R2-BIL** | **0 violations on 261 dense multi-slot × multi-slot ordered
> pairs** (9 per row: the dense set D realized THREE elements on all 29 rows —
> degree-2 "ones2"/"mix2" at k = 5..34 and, censused, the degree-3 dense "ones3"
> at k = 7..52, so every row's D is {3,3,4}-slot dense) …

**The code** (`build_dense`): `alt = elems[1] if len(elems) > 1 else elems[0]`
and mix2's target is `{0: 1, 1: alt, 2: 1}`. On 13 roster rows the field
enumeration's `elems[1]` **is** `Km.one()` (reproduced this pass: C2A, C2B, C2E,
C2I, C3A, C3D, C3E, C3I, C4A, C4B, C4G, C4I, I4A), so mix2's target equals
ones2's target, and the deterministic `surj_build` returns the **same
polynomial** (verified byte-identical on C2I, C4I, C2A this pass). On those rows
D = {f, f, f′}: the 9 ordered pairs contain only **4 distinct** pairs, and the
"mixed variant" adds zero resolution. The affected rows include **C2I and C4I —
the only two rows where ψ_m has genuine interior content**, i.e. exactly the
rows the bilinearity leg exists for. The scored content survives (ones2 × ones2,
ones2 × ones3, ones3 × ones3 are genuinely dense × dense with live cross-terms,
and U2 fires on all of them), so (DMULT-s)'s bilinear evidence is real — but
"realized THREE elements on all 29 rows" conveys a three-element diversity that
13 rows do not have, with no census of the coincidence. This is the same species
as PE2's GAP 2 (sample composition asserted, not disclosed), reintroduced in the
leg that was repairing it. **Classification: JUSTIFICATION GAP** (evidence
resolution / disclosure).

## GAP 4 — §9.4's R2-PHI cell attaches a FALSE justification to a true measured fact: "E | wΦ_NR" fails on 25 of 29 roster rows

**Offending passage (verbatim), §9.4 verdict:**

> | **R2-PHI** | **0 violations on 29/29 rows** … (δ = 0 on every row —
> E \| wΦ_NR forces s_NR(wΦ_NR) = 0).

Checked per row this pass: E | wΦ_NR holds on exactly **4 of 29** rows (C2D,
C2I, C2J, I4A) and fails on the other 25 — e.g. C2A: E = 4, wΦ_NR = 10. The
measured fact (δ(wΦ_NR, wΦ_NR) = 0 on 29/29) is true and the correct one-line
reason is **e_m | wΦ_NR** (wΦ_NR = e_m·g_m·γ_{m+1}, so s_NR(wΦ_NR) = l_m·(a
multiple of e_m) mod e_m = 0) — which holds on 29/29 (verified). A false
divisibility claim stands in a verdict cell written at r2 from the artifacts.
Nothing downstream consumes it (the cell explains a census figure).
**Classification: JUSTIFICATION GAP** (false supporting claim; conclusion
unaffected).

## GAP 5 — the TC-3 display's "corresponds to ψ_m(y)·Δ" silently needs δ(wΦ_NR, n−wΦ_NR) = 0 — true, one line, unwritten, and load-bearing for the K-line conclusion

**Offending passage (verbatim), §2.10:**

>     𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR}  corresponds to  ψ_m(y)·Δ,
>
> because ρ^B(in Φ_{m+1}·β) = A·ψ_m(y)·ρ^B(β) with
> ρ^B(in Φ_{m+1}) = ψ_m(y)/a_{wΦ_NR} …

The A here is A(wΦ_NR, n−wΦ_NR) = (unit)·y^δ ((MULT-B) + JC-SPAN). The image of
the ideal piece is therefore (unit)·y^δ·ψ_m·Δ, which equals ψ_m·Δ **iff δ = 0**
— if δ were 1 the quotient B_n/(𝔦^B ∩ B_n) would strictly contain a K-line and
the display (and §3.1's "each 𝒜_ν is a 1-dimensional K-space") would fail. The
fact IS true: s_NR(wΦ_NR) = 0 and e_m | wΦ_NR gives s_NR(n − wΦ_NR) = s_NR(n),
so δ = (0 + s_NR(n) − s_NR(n))/e_m = 0 for every n. But the note writes the
unit-and-monomial A into the display without observing that its y-degree
vanishes — the one fact that makes "corresponds to ψ_m(y)·Δ" an equality of
ideals rather than an inclusion. (PE2's A5 checked nonzero-ness of the pieces,
not this identification; R2-PHI measures the δ = 0 instance at n = wΦ_NR only.)
**Classification: JUSTIFICATION GAP** (unwritten load-bearing one-liner).

## GAP 6 — the TR-3′-GEN gloss inside [r2, G-1] misquotes the record's closed scope twice

**Offending passage (verbatim), §2.10 (DMULT-s):**

> … is stated WITH per-argument units even where closed, and is OPEN beyond
> {all order-2} ∪ {two order-3 strata}.

Against `GRB_ORDER2_2026-08-05.md` §S3.4 (read this pass): (a) the enlarged
closed scope of record is "**{all order-2} ∪ {order-3 all-e_j = 1}**" — **one**
order-3 stratum, not two (the third bracket's HV3 discharge changes the
conditionality of that same stratum, not the count). (b) "stated WITH
per-argument units even where closed" misdescribes both closed strata: on
stratum (i) the accepted closures deliver **exactness** — TR3-S1
"σ₁(R^F₂(f)) = R_λ(f) EXACTLY", TR3-S3 "discrepancy ≡ 1, per-argument units ≡ 1"
— while on stratum (ii) the first post-acceptance bracket says "the units-only
phrasing of the record statement below is PERMANENTLY REFUTED on (ii)" (the
discrepancy is an explicit slot-keyed character, not a unit system). The
openness claim the tier split rides on ("OPEN beyond" the closed scope, hence no
corpus pin for ω ≡ 1 at general order) is **correct and unaffected**; what is
wrong is the parenthetical characterization of the record — in the one passage
doing G-1's citation-honesty work. **Classification: JUSTIFICATION GAP**
(citation precision).

## GAP 7 — §9.3's frozen R1-COB prereg row still asserts the pre-split blast radius ("a failure refutes (COORD-B)(2)") with no [r2] annotation, contradicting JC-COB's corrected fencing

**Offending passage (verbatim), §9.3 prereg table:**

> | **R1-COB** | COROLLARY JC-COB: 𝑅_{γ+γ′}(φ_γφ_{γ′}) == a_γ·a_{γ′}·y^δ on the
> full anchor grid (a sharp consequence of (DMULT): a failure refutes
> (COORD-B)(2)) | **0** |

Post-split, the note's own JC-COB display states the correct two-mode blast
radius: "a failure with the slot set still {δ} would refute only the exact tier
(ω ≢ 1), while a failure of the SLOT-SET half would refute (DMULT-w),
(COORD-B)(2) and with them the repair". The prereg row (a quotation of the
sealed r1 docstring, properly byte-frozen) asserts the undifferentiated form —
under the r2 discipline it should carry a bracket, as the parallel r1 texts do
(the §9.3 verdict cell and finding 1 both received [r2, G-1] annotations; this
row did not). Two contradictory blast-radius statements coexist at HEAD.
**Classification: JUSTIFICATION GAP** (bookkeeping; the frozen quote itself must
not be edited, only annotated).

## GAP 8 — JC-CYC(b)'s mechanism gloss is false as stated, and the note's own mechanism-2 rows refute it

**Offending passage (verbatim), §6:**

> * **(b) [PROVED, general m — the obstruction direction]** If the measured
>   value table has two distinct non-1 values, (CYC) fails by (α). With
>   JC-INNER's law image(c) = {z̄^δ∏_j z_j^{D_j}}, **this happens as soon as the
>   stage realizes two multiplicatively distinct (δ, D)-words** …

The graded first sentence is correct and trivially so. The bolded gloss is
false: two multiplicatively distinct words can evaluate to {1, v} — ONE non-1
value — where (α) holds with ζ′ = v and (CYC) can only fail through (β). The
note itself exhibits exactly this genre two sections later: "**a single value
whose carry pattern is not realizable by any integer relabeling** (C2C, C3I)" —
rows realizing distinct words without two distinct non-1 values, NOT-CYCLIC by
(β) not (α). So the gloss's "this happens as soon as" needs "two distinct non-1
values of the word", and the 14/29 / 22/28 empirics it explains are actually
carried by (α) AND (β) jointly. No graded claim moves. **Classification:
JUSTIFICATION GAP** (false explanatory sentence inside a PROVED-labelled
clause).

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All three
batteries overwrite their own `*_results.json` on execution; `git status` on
`verification/openmath/` after all three reruns shows **no modification** — every
committed JSON artifact reproduced **byte-for-byte**. (The only untracked file
there is `weldmaster_checks.py`, another agent's work-in-progress — untouched
and unstaged by me.)

### (a) Seals and md5s — all verified

* r0 runner `grt_jc_checks.py` md5 **`adb555e1134d3ae0b0174d62e8b3446c`** at
  HEAD = the sealed value (identical at `79611a4`). ✓
* r1 runner `grt_jc_r1_checks.py` md5 **`7f896bfa27d06158f95c5987c7299770`** at
  HEAD = the sealed value (identical at `79611a4`). ✓
* r2 runner `grt_jc_r2_checks.py` md5 **`c02bf06029a72259512ea005bd2562fd`**
  identical at `79611a4`, `db12666` and HEAD — the sealed runner is the run
  runner. ✓
* instrument `grt_jc_probe.py` md5 `03811b695cf7aa1bd5b52d5b0cd8bcd6` unchanged
  at `79611a4` and HEAD. ✓
* **r2 mini-seal shape:** `79611a4` touches **only**
  `verification/openmath/grt_jc_r2_checks.py` (1 file, 399 insertions) — script
  only, sealed UNRUN, prereg in the docstring ✓; `db12666` touches only the note
  (39 lines) + `grt_jc_r2_output.txt` + `grt_jc_r2_results.json` — verdict FROM
  artifacts, no script ✓; `5742e25` touches only the note ✓. No `.lean` touched
  by any r2 commit ✓.

### (b) The three batteries — all reproduced, exit 0

* **r0:** `python3 grt_jc_checks.py` → exit **0**, 2.0 s, 29 rows, 0 violations,
  silent teeth NONE; stdout vs committed `grt_jc_checks_output.txt`:
  **byte-identical except two per-row wallclock digits** (C3A 0.4→0.3, C3G
  0.7→0.6). Family table identical (JC1 2,594 … MJ5 633/633; ten families sum
  8,566).
* **r1:** exit **0**, 2.6 s, 0 violations, silent teeth NONE; stdout vs
  committed `grt_jc_r1_output.txt` **byte-identical** this run. Families:
  EXT-GATE 1, R1-BND 29, R1-PER 841, R1-INJ 585, R1-SURJ 841, R1-DMULT 2,784,
  R1-COB 2,607, R1-PSIK-LO 591, R1-PSIK-HI 1,182, R1-UNIT 869 (= 10,330),
  TOOTH-ROW 145 (= 10,475 over 11 rows — the [r2, G-8] decomposition is
  correct); teeth 29/29/1,392/29/406 = 1,885.
* **r2:** exit **0**, 7.4 s, 0 violations, silent teeth NONE; stdout vs
  committed `grt_jc_r2_output.txt` **byte-identical**. Families: EXT-GATE 1 +
  R2-BIL 696 + R2-PHI 87 + R2-MONO 2,813 = 3,597 in-family + TOOTH-ROW 58 =
  **3,655** ✓; **U1 261/261, U2 261/261** ✓; R2-BIL 261 ordered dense pairs
  (9 × 29) ✓; deg-3 dense realized 29/29, k ranges 5..34 (deg 2) / 7..52
  (deg 3) ✓; R2-PHI census "skipped exactly 1 pair per row (total 29); bilinear
  content on 2 rows: ['C2I','C4I']" ✓; "U2 fired 0 times on the r1-TESTED
  pairs" ✓. Every §9.4 cell and the header headline match the artifacts.

### (c) Figure cross-checks of r2-edited quotes

* **[r2, G-3] c_π roster set:** tallied from the committed `grt_jc_r1_output.txt`
  this pass — c_π = 1 on **9** rows, z̄ on **9**, z̄² on **7**, and z̄³/z̄⁴/z̄⁶/z̄⁸
  on the single rows **C2G/C3H/C2H/I4C** — exactly the [r2, G-3] bracket. ✓
* **[r2, G-8] split:** 10,330 + 145 = 10,475 ✓ (recomputed).
* **[r2, G-7] / §7 row 5:** JC-BOX-4 carries the [r1] conditional closure and
  both "unchanged" sites now corrected ✓.
* **§9.5's count:** FAILS — see GAP 2 (37 ≠ 22 at `5742e25` and HEAD; 24
  pre-r2). Its "0 live consuming sites" claim: **verified TRUE** by independent
  classification of all 37 hits.
* **Pre-seal smoke figures** (r2 docstring: dense k = 5/5/19 deg-2, 8/8/27
  deg-3 on C2A/C2I/C4H): consistent with the full-run per-row values (C2A
  [5,5,8], C2I [5,5,8], C4H [19,19,27]). ✓

### (d) Read-only probes written for this pass (outside the scored surface, nothing staged)

In-terminal python probes (imports `grt_jc_probe` + frozen r1 helpers, computes
nothing new): (i) per-row E, wΦ_NR, E|wΦ_NR, e_m|wΦ_NR — GAP 4's data;
(ii) per-row `alt == Km.one()` + byte-comparison of the ones2/mix2 builds —
GAP 3's data (13 rows; f identical on C2I/C4I/C2A, distinct on C2C).

---

## §C WHAT SURVIVED THE PASS (beyond §A; re-checked, no defect found)

1. **The G-2 disclosure block (§9.3 [r2])** — the seven-element sample list, the
   six-single-slot count, and the skip disclosure all verified against the
   frozen r1 source; R2-MONO scores (a)(b)(c) rather than asserting them, and
   its predicates are the right ones.
2. **The G-4 headline repairs** — the W-7 THEOREM box's OB-4 grade line and
   §4.1 remark (b) are struck-and-regenerated exactly as PE2 demanded, with the
   refuted input and the denial of r1's machine leg both gone; the (MULT-B)|gr
   restriction display (recorded once, cited at sites 2–6) is correct
   (ρ^B|_{gr_λ} = ρ_λ is the k = 0 colimit term; products of gr-elements stay
   in gr by (IN-3)(b)).
3. **The G-5 transport display** — (G5-i) k-independence via JC-PER byte-equality
   and (G5-ii) via JC-PIINV(c), both re-derived; the wΦ_NR ∈ W observation for
   the anchor a_{wΦ_NR} is correct (attained by Φ_{m+1}).
4. **The G-9 ideal-transport step** — σ(𝔦^B ∩ B^{(ν)}) ⊆ 𝔦^B ∩ B_n because 𝔦^B
   is an ideal and ϑ^{-k} ∈ B, reverse inclusion at k = 0. ✓
5. **The [r2] stack re-rank (§10.2)** and the tier-aware JC-BOX-3 items 1/3 —
   consistent with the consumer split as verified in §A2; "no clause GRADE
   changes between tiers" confirmed (JC-COB is a corollary, not a graded
   clause; its sharp form's demotion to measured-tier is displayed at every
   consuming site).
6. **Header/status hygiene** — the [r2] S-STATUS supersedes the struck [r1]
   line; counter 0/2 everywhere; no gate fires/retires; no density/menu/count
   statement; JC-BOX-2/JC-BOX-8(i) residues (off-stratum existence; the 606
   non-integral perturbations) still honestly displayed as having no machine
   leg on ANY runner, including r2's.

---

## §R RECOMMENDATION

**Not clean; 0 CRITICAL, 8 gaps; counter stays 0/2.** The mathematical content
of r2 — the tier split, the κ = 1 pinning, the G6 derivation — survives hostile
re-derivation completely; every gap is a labelling, disclosure, or record
defect, and none requires new mathematics:

1. **GAPs 1, 2, 7** are the r2 sweeps' own species leaking: re-point JC-LOAD's
   two `(IN-3)(c)` sites to (MULT-B)|gr/(DMULT-w) (two brackets), regenerate
   §9.5's count from an actual grep at the committing state (and widen the
   protocol to stale input NAMES, not just `(COORD)`/`(MULT)`), and annotate the
   frozen R1-COB prereg row.
2. **GAPs 3, 4** are the new battery's disclosure debts: census the ones2/mix2
   coincidence (13 rows, both g_m = 2 rows) — or pick `alt` as a genuinely
   ≠ 1 element where one exists — and replace "E | wΦ_NR" with "e_m | wΦ_NR".
   Any new scored leg needs its own mini-seal; a census/label fix does not.
3. **GAPs 5, 6, 8** are three short prose repairs: the δ(wΦ_NR, n−wΦ_NR) = 0
   line in the TC-3 display; the TR-3′-GEN closed-scope gloss ("one order-3
   stratum"; drop "stated WITH per-argument units even where closed" for the
   record's actual per-stratum shape); JC-CYC(b)'s gloss ("two distinct non-1
   values of the word").
4. PE4 should verify the GAP 1/2 sweep repairs by re-running the widened grep
   itself, spot-check the GAP 3 census against the code, and then — if clean —
   start the acceptance count. The weakest mathematical links remain exactly
   §10.2 [r2]'s list, headed by (DMULT-w) + W-1's transport; nothing found this
   pass moves that ranking.

— GRTJC pass PE3, hostile verifier unit (fresh context), fixes nothing.
