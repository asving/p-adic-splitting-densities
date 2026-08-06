# GRTJC pass PE8 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**,
unchanged since r6 (commit `4b804b4`; `git diff 4b804b4 HEAD -- <note>` = 0
lines — no repair round followed PE7's clean pass, per the arc's
note-only-in-repair-rounds convention). Runners: `grt_jc_checks.py` (r0),
`grt_jc_r1_checks.py` (r1), `grt_jc_r2_checks.py` (r2), instrument
`grt_jc_probe.py` — all in `verification/openmath/`, all four md5s at their
sealed values (§M).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **EIGHTH acceptance
attempt — THE ACCEPTANCE PASS**: the counter stands at 1/2 after PE7's clean
pass (ledger action at commit `849cdca`); a clean pass here is the second
consecutive clean and ACCEPTS the note; any finding resets the count. The bar
is identical to every pass.

## VERDICT

**0 CRITICAL · 0 GAPS — CLEAN.** This is the arc's SECOND consecutive clean
pass; per the acceptance rule it completes the 2-clean requirement (recording
the acceptance is the orchestrator's ledger action, not this report's). The
full note was re-read top to bottom at HEAD with no diff to lean on; the
statement-level truth sweep of the W-6..W-9 clause boxes, both (DMULT) tiers,
the cyclic-fence law, the case split, and all eight honest boxes found every
graded claim true as fenced; the arc-accounting system is consistent and true
at HEAD (22 hashes, round figures, strike census, pointer semantics, union
census — all independently re-executed); the two decorrelated re-derivations —
one by a proof route no prior pass and not the note used, one on TWO
fresh-instance stages whose parameters (g_m = 3; order 5 / m = 4) lie outside
every runner's and every prior report's range — returned zero exceptions, 885
checks. Machine legs 4/4: exit 0 on all three batteries + the instrument;
r0/r1/r2 stdout **exactly byte-identical** to the committed outputs (0-line
diffs — the first pass in the arc with all three battery stdouts exact);
instrument differs on TWO per-row wallclock digits only; every committed JSON
artifact reproduced byte-for-byte (`git status verification/openmath/` clean);
all four md5s at sealed values.

---

## §A THE CHARGES, CHECKED TO THE BOTTOM

### A1. Decorrelated re-derivation, LEG A (mathematical; a route no prior pass and not the note used): THEOREM W-8 + THEOREM JC-LOAD's iff by the DOUBLE-(DMULT-w) + ω-SYMMETRY route

**Route disclosure.** The note proves W-8 via the ρ-machinery: apply
(MULT-B)|gr to the fence-clean equation, cancel the anchor cocycle A(λ,N)
(Δ a domain), pin 𝑅_N(X_N) = 1, conclude through (†)/(‡). Every prior
re-derivation followed that spine: PE3 §A2 ("(‡) on (MULT-B)|gr"), PE5 §A4
(the A(λ,N) cancellation), PE4 §A1 and PE5 §A1 (JC-LOAD via §4.2's offset
transport / the b_× = a_{λ+N}/(a_λa_N) pinning with A(λ,N) = 1). **My route
uses NO anchor cocycle, no §4.2, no A(λ,N), no b_×, and no ρ beyond its
definition**: apply (DMULT-w) directly to the two product polynomials and
cancel ω by its symmetry.

Setup: γ, γ′ ∈ W, γ+γ′ =: λ ∈ W, e_m ≥ 2; N ≡ 0 (mod E), N ≥ wΦ_NR.
Since E | N and s_NR is ℤ-linear mod e_m with e_m | E: s_NR(N) = 0,
s_NR(λ+N) = s_NR(λ), hence **δ(λ,N) = 0 = δ(N,λ)**.

* **LHS digit polynomial.** f := φ_γφ_{γ′} ∈ O[x] with w(f) = λ ((IN-3)(a));
  g := X_N with w = N (R2). (DMULT-w):
  𝑅_{λ+N}(φ_γφ_{γ′}·X_N) = ω(λ,N)·y^0·𝑅_λ(φ_γφ_{γ′})·𝑅_N(X_N)
  = ω(λ,N)·u·y^δ, using JC-SPAN (𝑅_λ(φ_γφ_{γ′}) = u y^δ, u ∈ K_m^*,
  δ = δ(γ,γ′)) and 𝑅_N(X_N) = 1 (JC-SCAL(b) + R3 + K_m ↪ K injective on
  constants — tier-blind, §4.1's own step).
* **RHS digit polynomial.** (DMULT-w) on Λ_N(c) (integral, w = N) and φ_λ:
  𝑅_{λ+N}(Λ_N(c)·φ_λ) = ω(N,λ)·y^0·𝑅_N(Λ_N(c))·a_λ = ω(λ,N)·c̃(y)·a_λ,
  using **ω symmetric** (ω(λ,μ) = c_{λ+μ}/(c_λc_μ) by the tier's own
  derivation — symmetric in (λ,μ) on the nose) and 𝑅_N(Λ_N(c)) = c̃(y), the
  canonical degree-<g_m representative (JC-SCAL(a) gives degree < g_m and R3
  gives reduction = c; a degree-<g_m polynomial reducing to c mod the
  degree-g_m ψ_m IS the canonical representative — uniqueness kills the
  line-wise-unit slack, exactly as §4.1 argues).
* **JC-LOAD's iff, at one stroke.** (RAW) is literal equality of the two
  digit polynomials; ω(λ,N) ≠ 0 cancels **because both sides sit on the same
  unordered line pair {λ, N}** — this is the mechanism that makes the iff
  tier-blind, visible here without any constant bookkeeping. So (RAW) ⟺
  ∃c ∈ K^*: c̃(y) = (u/a_λ)·y^δ. Since c ↦ c̃ is a bijection
  K^* → {nonzero polynomials of degree < g_m} and u/a_λ ∈ K_m^*: solvable ⟺
  deg(y^δ) < g_m ⟺ **δ < g_m**. Both directions, no offset-transport lemma.
* **W-8.** The fence-clean equation read in the TC-transported ring: both
  sides are gr_{λ+N}-elements, and two such have equal 𝒜-classes iff their
  ρ-coordinates agree mod ψ_m (§2.10's K-line display B_n/(𝔦^B ∩ B_n) ≅
  Δ/(ψ_m) — the one shared ingredient with the note's route, consumed as the
  TC-3 semantics it is), i.e. iff their reads agree after dividing the common
  a_{λ+N}. Reads of the two displays above: ω·u·z̄^δ vs ω·c·a_λ (c̃(z̄) = c).
  Hence c = (u/a_λ)·z̄^δ, existent and unique in K^* (u, a_λ ∈ K_m^*, z̄ a
  unit since ψ_m(0) ≠ 0). And by (†) + JC-SPAN:
  c_val = 𝑅_λ(φ_γφ_{γ′})(z̄)/a_λ = (u/a_λ)·z̄^δ. **Equal — W-8 lands, with
  every normalization cancelling for a visible reason: the ω's cancel by
  symmetry of the line pair, a_{λ+N} cancels because both reads sit at the
  same line, and the lift normalization is killed by 𝑅_N(X_N) = 1.**
* **Hypothesis audit.** e_m ≥ 2 enters ONLY through JC-SPAN's sharp singleton
  (at e_m = 1 the route still runs on JC-BOX-4 [r1]'s (DMULT-w) second proof
  — consistent with the box's two-footprint closure). The route consumes
  exactly the W-8 grade line's declared inputs ((DMULT-w) + JC-SPAN + JC-SCAL
  + R3 + the in-note TC-3 semantics) — no hidden (DMULT-s) consumption: ω is
  never evaluated, only cancelled. **CLEAN, and the note's own fences are
  re-confirmed from a second direction.**

**Bonus micro-leg (W-9(ii), a route no pass used).** The integer carry
identity needs no Δ-identity and no y-degrees: from the definition
δ(a,b) = (s(a)+s(b)−s(a+b))/e_m, both sides of
δ(a,b)+δ(a+b,c) = δ(b,c)+δ(a,b+c) telescope to the SAME symmetric expression
(s(a)+s(b)+s(c)−s(a+b+c))/e_m. One line, decorrelated from §5's proof (ii)
(which takes y-degrees in the (MULT-B)|gr cocycle identity); the two routes
agreeing is itself a consistency check of JC-CARRY-m's deg A = δ.

### A2. Decorrelated re-derivation, LEG B (machine; instances outside EVERY runner's and EVERY report's parameter range)

**Route disclosure.** PE7's fresh-instance leg varied the PRIME (p = 7, m = 1,
g_j ≤ 2). All four runners' rosters and both PE7 stages satisfy m ≤ 3 and
g_j ≤ 2 — the note's own JC-BOX-1 scope. **My leg varies the OTHER two axes**:

* **XG3** (p = 2, d0 = 1, reads (2,1,1),(2,1,3)): **g_m = 3** — the first
  g_j = 3 stage any GRTJC artifact has ever built. ψ_1 = y³+y+1 over 𝔽₂
  (irreducible, ψ(0) ≠ 0 — inside (IN-5)'s class pin, which allows g_j ≥ 1);
  K = 𝔽₈, E = 4, e_m = 2, wΦ_NR = 30. Off the collapse geography
  (|K| = 8, g_m = 3, e_0 = 2) with a decidable table (E = 4 ≤ 8) — a THIRD
  off-collapse decidable row (after C2I and PE7's X7B), the exact genre
  §9.2 finding 2 says the roster is short of.
* **X5A** (p = 3, d0 = 1, reads (2,1,1),(1,1,1),(2,1,1),(1,1,1),(2,1,1)):
  **m = 4, NR = 5 reads, order 5** — the first order-5 machine contact in the
  campaign (JC-BOX-1: machine scope was orders ≤ 4). E = 8 with interleaved
  flat legs, K = 𝔽₃, g_m = 1, wΦ_NR = 62, G0 = 48.

**Engine-guard disclosure (honest).** The frozen `iterlawn_pe_reimpl.py`
(md5 `cae45db2318b89520dd5484466ef3604`) guards ψ-irreducibility by a no-root
test coded for g = 2 only and asserts g ∈ {1,2}. My XG3 run uses a /tmp
byte-copy with ONE hunk changed: the same no-root test extended to
g ∈ {2,3} — a no-root test is a VALID irreducibility criterion for any
degree-≤ 3 polynomial over a field, so the patch widens the guard's coverage
without weakening it. Everything else byte-identical; the repo file is
untouched (md5 unchanged, §M); X5A needs no patch. Caveat carried: g = 3
exercises engine paths (3-coordinate REALIZE, deg-3 residue extension) never
validated before — so any anomaly would have needed engine-vs-note
adjudication. **There was no anomaly.**

**Results — 885 checks, 0 violations, exit 0** (script `/tmp/pe8_fresh.py`,
read-only imports of the frozen `grt_jc_probe`/`grt_jc_checks`/
`grt_jc_r1_checks`, in-memory, nothing staged):

* **w(π) = E** on both (E = 4 at NR = 2; E = 8 at NR = 5 — JC-DOM's degree
  computation at a depth never machine-touched).
* **JC-PER** φ_{γ+kE} == π^kφ_γ byte-for-byte at k = 1,2 + s-tuple
  periodicity + u₁-shift, 24 checks; **JC-FIB** tuple bijection on both
  (ℤ/8 ≅ ℤ/2×ℤ/1×ℤ/2×ℤ/1×ℤ/2 on X5A).
* **JC-ANCHMON** slot set {0} on all 12 anchors; **JC-SPAN slot set == {δ}
  on 80/80 grid pairs**, δ ∈ {0,1} everywhere; **JC-COB's sharp
  u == a_γ·a_{γ′} on 80/80** — out-of-roster (DMULT-s) evidence at g_m = 3
  and at order 5.
* **JC-SCAL at g_m = 3 — genuinely new resolution**: the 7 nonzero c ∈ 𝔽₈
  all realize with slot set == supp(c) ⊆ {0,1,2} and per-slot digits exact;
  **4 of the 7 occupy slot 2**, the first slot-2 scalar lifts ever scored
  (every prior artifact had g_m ≤ 2, slots ⊆ {0,1}); 𝑅_N(X_N) == 1 on both.
* **JC-LOAD's dichotomy, both directions, exhaustive over K**: on XG3 the
  load set is **EMPTY on all 16 pairs** (δ ≤ 1 < g_m = 3 — §3.2 consequence
  3's "empty on every g_m ≥ 2 stage" geography, machine-confirmed at a g_m
  no runner reached); on X5A **exactly the 16 δ = 1 pairs of 64 have no
  pre-TC-3 scalar** (g_m = 1), 0 anomalies either direction at order 5.
* **JC-PSIKER with a DEGREE-3 kernel witness**: w(Φ_{m+1}) = e_m g_m γ_{m+1}
  = 30; 𝑅(Φ_{m+1}) == ψ_m coefficientwise with slot set {0,1,3} (the first
  ψ-witness with an unoccupied interior slot); read == 0.
* **(DMULT-s) on bilinear pairs including (Φ_{m+1}, Φ_{m+1})** — on XG3 the
  ψ_m² convolution is a 3-slot × 3-slot product with occupied interior,
  BEYOND R2-BIL's dense diversity (whose g_m = 2 rows top out at ψ 3-slot
  vs anchor-monomials); 16 pairs exact, dict equality, multiplier 1.
* **W-9(i)(ii)** on 64 + 512 = **576 triples**: K^*-cocycle and integer-carry
  identities, 0 violations (first order-5 cocycle table).
* **JC-CYC, the adversarial extra**: XG3 (OFF-collapse, decidable) →
  **NOT-CYCLIC (single value z̄, carry pattern not realizable by any integer
  relabeling)** — the (β)-mechanism kill, exactly §6(d)'s mechanism-2 genre
  (C2C/C3I's), at a fresh geography. **JC-CYC(d)'s OPEN inclusion
  "CYCLIC ⟹ collapse geography" survives a third off-collapse instance.**
  X5A (collapse geography, g_m = 1) → CYCLIC with ζ = z̄,
  σ = (0,7,6,5,4,3,2,1) — the inclusion's allowed side, consistent.

### A3. Statement-level truth sweep — the whole note at HEAD, W-6..W-9 boxes and both (DMULT) tiers TRUE AS FENCED

* **§0/§1.** The five inputs' declarations checked against sources this pass:
  the §S6a pinned quotation present at `GRB_ORDER2_2026-08-05.md` (L956/965/
  976: "Thm 4.2 three times", "Thm 4.8 (evaluation at ȳ …)", "s(gh) =
  s(g)+s(h), Cor 2.7"); δ ∈ {0,1} re-derived (s_NR ℤ-linear mod e_m, values
  in [0,e_m)); the split/window/anchor definitions consistent with the
  engine. The completed stack one-liner (FGMN (a)(b)~~(c)~~(d)(e)) matches
  the live consumption set (§10.2 [r5, G-2], verified by PE6 at source;
  re-read).
* **W-6 box.** (i) JC-DOM re-checked (domain from (a)+(b); w(π) = E by the
  A₀ = π development — machine-confirmed at NR = 5 this pass); JC-GAUGE's σ
  proof re-checked line by line ((i) componentwise split, (iii) kernel both
  inclusions; unit needed exactly where TC-1 supplies it). (ii) A_ν ≅ B_n
  with the strictly-bigger parenthetical (maxslot unbounded along the ladder;
  R1-BND's census its shadow). (iii) JC-PER — fresh byte-exact leg at
  order 5. (iv) JC-LOAD — re-derived by the fresh route (A1) AND
  fresh-instance-tested at g_m = 3 / m = 4 (A2). (v) JC-PSIKER's three
  clauses as re-quantified at [r1, F2]; the §2.9 window-base list
  **re-computed from the frozen Stage builder this pass: C2A 4 < 10, C2I
  4 < 20, C3G 200 < 222, C4C 312 < 346, C4H 60 < 81, I4A 156 < 204 — 6/6
  MATCH**. Grade lines internally consistent ([r1] input-list supersession;
  [r2, G-7] box-change record). **TRUE AS FENCED** (JC-BOX-4 carries the
  corner, both footprints displayed).
* **W-7 box.** OB-2 (byte-exact, fresh leg); OB-3 EXISTENCE+STRUCTURE on all
  window pairs with the sharp form fenced e_m ≥ 2 → JC-BOX-4; OB-3 VALUE on
  exactly [ILN]†'s stratum — the c_val ↔ [ILN]† tie re-verified at source
  (`ITERLAWN_PROOF_2026-08-08.md` L210: "c_{n+1}(γ,γ′) := val(φ_γ·φ_{γ′}) /
  val(φ_{γ+γ′})" — the note's c_val verbatim); OB-4's regenerated grade line
  true (digit-form measurement: R1-DMULT 2,784/0 + R1-COB 869/869 + R2-BIL
  261 reproduced this pass, + my 80/80 out-of-roster COB); OB-5's
  architecture discharge with the G8 call-site disclosure (code re-read:
  `constants()['delta']` is split data; gr-side from `read_coeffs`). Germ
  split: the instrument's germ table re-run — **27 eligible stages
  (11+8+4+3+1 by κ), κ ∈ {1, z̄, z̄², z̄³, z̄⁴}, val(Ĉ) = −z̄ throughout,
  H-D REFUTED 138/669** — all as §3.3 displays, J-B fences carried (JB-EPS's
  "unconditional at every m ≥ 1" re-verified at GRTJB row 19/§5).
  **TRUE AS FENCED.**
* **W-8 box.** Re-derived by a fresh route (A1); input list consistent with
  the tier split; P5-OB6 0/669 reproduced. **TRUE.**
* **W-9 box.** (i)/(ii) fresh machine leg (576 triples) + (ii) by the direct
  integer route (A1 bonus); (iii) the twisted-group-algebra restatement;
  (iv) β_{k+1} = β_k·c(1,k), v^E = ζ_T re-checked; JC7's E-fold chain
  matched on **exactly 15 rows** in this pass's re-run (counted from
  stdout). JC-F1/JC-F2 both displayed as REVIEW-OWED (JC-BOX-5). **TRUE.**
* **Both (DMULT) tiers.** The (DMULT-w) derivation re-checked (ω =
  c_{λ+μ}/(c_λc_μ), line-only, symmetric, nothing gives ω ≡ 1) — and leg A
  CONSUMES exactly the tier's content, an independent probe that (DMULT-w)
  suffices for W-8/JC-LOAD: it does. (DMULT-s)'s measured-not-cited status:
  TR-3′-GEN's statement of record re-verified at
  `GRB_ORDER2_2026-08-05.md` §S3.4 this pass (L538-9 "level-by-level
  compatible family … together with per-argument units"; closed scope
  "{all order-2} ∪ {order-3 all-e_j = 1}" at L481; TR3-S1/TR3-S3 exactness
  and the "PERMANENTLY REFUTED on (ii)" bracket at L462/486/468 — the
  [r3, G-6]-corrected gloss is quotation-faithful). Every JC-COB sharp-value
  site re-read carries the (DMULT-s) fence; my out-of-roster 80/80 adds
  fresh evidence to the measured tier without moving its label.
  **CONSISTENT AND TRUE.**
* **§6/§7/§8.** (CYC) definition matches the frozen `adjudicate` (re-read
  this pass: (α) image ⊆ {1,ζ′}, (β) the σ-relabeling); JC-CYC(b)'s corrected
  trigger + (c)+(d) as fenced, with my XG3 instance landing in mechanism 2
  and X5A in the allowed CYCLIC side; §7's rows against the reproduced
  artifacts (134/669 load set, C2I/C4I the g_m = 2 rows, C4H unique e_m = 1);
  JC-BOX-1..8 all honest at HEAD (the 606 non-integral SPAN-M residue and
  JC-BOX-2's zero-machine-support off-stratum half still displayed as owed;
  my fresh leg does NOT touch either — XG3/X5A test integral elements on
  new geographies, not the non-integral residue).
* **§9.** Every headline cell of §9.2/9.3/9.4 checked against this pass's
  re-runs (byte-identical stdouts): 8,566/0 with 1,054 firings and the
  6/14/9 split; 10,330+145 with 1,885 firings; 3,655 rows with U1 261/261,
  U2 261/261 and U2-on-r1-pairs 0; JC3 609/609; JC3-FLAT census "24 pairs,
  0 with a slot > 0"; the instrument's TOTALS line (29 rows, 669 scored,
  DCX-censused 0, non-integral-D 0), MT3 197/206, k-distribution — summed
  from the committed JSON this pass: **{0: 669} exactly** (per-row kdist
  keys all '0', totals 112+248+201+108 = 669).

### A4. The arc-accounting system at HEAD — CONSISTENT AND TRUE

* **All 22 hashes resolve** in `git log` with matching subjects (seal/verdict
  `6ad01d1`/`8f07904`; instrument `7212e56`/`fc89b03`; PE1–PE7 reports
  `1a27be3`/`4a76d52`/`e4b6fbf`/`d5072b6`/`b38f3f4`/`66760f6`/`782000e`;
  r1 `85d5811`/`54904cc` + mini-seal `f45b63c`/`66263ce`; r2 `5742e25` +
  `79611a4`/`db12666`; r3 `126c33f`; r4 `edbb966`; r5 `3870bc8`; r6
  `4b804b4`). Round figures in the [r6] arc match all six graded reports'
  verdict lines re-read at source (2C+8G / 0C+9G / 0C+8G / 0C+4G / 0C+2G+1m /
  0C+1G).
* **Exactly two current arc displays** (header L181, §10.1 L2649), both
  ending "JC-PE7 next" — round-records of r6, correct as dated: PE7 has since
  RUN and its report (`782000e`) is CLEAN; no repair round follows a clean
  pass, so the note is unchanged and the count advance (1/2) lives in the
  orchestrator's ledger (`849cdca`), exactly as PE7's report prescribed and
  as the LIFTCORNER acceptance precedent ran (its tail record appended at
  acceptance, not per-pass). Same for the 44 "0/2" counter sites — as-of-r6
  statements under the arc's convention. Not a defect (see Observations).
* **Strike census: 116 `~~` tokens / 0 odd paragraphs** (my own
  paragraph-split count) — unchanged since r6, matching PE7.
* **Union census discipline**: my own execution of the eight-alias union grep
  at HEAD returns **177** — identical to PE7's figure, as it must be (note
  byte-identical since `4b804b4`); zero live hits state the refuted content
  (PE7's classification re-spot-checked on the five r6-added lines).
* **The r6 annotation's historical claims re-verified at both pins by my own
  greps**: round-record language ABSENT at `edbb966` (0 hits) and introduced
  at `3870bc8` (3 hits); §0's [r4, G-1] bracket **byte-identical**
  `edbb966` → `3870bc8` (the inversion was r5-bred and un-annotated until r6
  — exactly as [r6, G-1] states).
* Grade-delta lines [r2]..[r6] present; counter 0/2 at 44 sites; no gate
  fires/retires; no density/menu/count statement; no `.lean` touched by any
  arc commit.

### A5. Dangling-observation sweep (nothing silently abandoned)

* PE7's two ungraded observations re-read: (1) the [r6, G-1] parenthetical
  glosses the FGMN ENTRY of the stack (subject-scoped compression, pointer
  authoritative) — stands, not a defect; (2) W-8's grade-line per-clause
  direct-input convention ((a) entering via JC-DOM) — stands, the system
  footprint is at the stack. Neither is re-gradeable.
* PE1 §C7's cleared-but-unwritten c_val ↔ [ILN]† tie: re-verified at
  ITERLAWN L210 this pass (A3). Stands as cleared.
* R1-PSIK-HI's uncapped prereg wording vs NU_CAP = 8: disclosed in the same
  table's verdict cell + docstring. Stands as disclosed.
* JC-BOX-3 item 2 (printed-source numbering Codex leg): still owed, still
  boxed, still displayed at every FGMN citation site. A standing disclosed
  leg of the ACCEPTED-state conditionality, not a defect.

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All
runs from the working tree at HEAD. **All four legs RUN** (no NOT-RUN legs).

### (a) Seals, md5s, commit shape

* Note **byte-identical** at `4b804b4` and HEAD (`git diff` 0 lines). ✓
* md5s at HEAD, all at their sealed values: r0
  `adb555e1134d3ae0b0174d62e8b3446c`, r1
  `7f896bfa27d06158f95c5987c7299770`, r2
  `c02bf06029a72259512ea005bd2562fd`, instrument
  `03811b695cf7aa1bd5b52d5b0cd8bcd6`; engine
  `iterlawn_pe_reimpl.py` = `cae45db2318b89520dd5484466ef3604` (untouched by
  the /tmp patch of §A2, which lives entirely outside the repo). ✓

### (b) The three batteries + instrument — all reproduced, exit 0

* **r0** `grt_jc_checks.py`: exit **0**, 2.0 s, 0 violations, silent teeth
  NONE; stdout **exactly byte-identical** (0-line diff). 8,566 samples /
  10 families, teeth 103+285+4+29+633 = 1,054, JC3 609/609, JC3-FLAT 24/0,
  cyclic split 6/14/9 with C2A/C2E/C2G/C2J/C3A/C4A, E-fold chain on 15 rows.
* **r1** `grt_jc_r1_checks.py`: exit **0**, 2.6 s, 0 violations; stdout
  **exactly byte-identical** (0-line diff). R1-DMULT 2,784, R1-COB 2,607
  (869 pairs), R1-UNIT 869/0/0/0, PSIK 197/197, TOOTH-ROW 145, teeth 1,885.
* **r2** `grt_jc_r2_checks.py`: exit **0**, 7.4 s, 0 violations; stdout
  **exactly byte-identical** (0-line diff). 3,655 rows, U1 261/261, U2
  261/261, U2-on-r1-pairs 0, dense bilinear content on exactly C2I/C4I.
* **instrument** `grt_jc_probe.py`: exit **0**, 18.3 s, total violations 0;
  stdout differs on TWO per-row wallclock digits only (C3I 1.6→1.7s, C3J
  1.7→1.8s). TOTALS 29 rows / 669 scored / DCX 0 / non-integral-D 0; P1-RAW
  134 == 134; H-B 215 / H-C 73 / H-D 138; MT3 197/206; MT2 14/6/9.
* `git status verification/openmath/` after all four re-runs: **clean** —
  every committed JSON artifact reproduced byte-for-byte. ✓

### (c) Figures vs the note + the fresh legs

Every headline cell of §9.2/§9.3/§9.4, §3.3's germ figures (27 stages —
re-counted 11+8+4+3+1 from the germ table — and 138/669), §3.5's MT3
figures, §2.8's k-distribution {0: 669} (summed from the committed JSON),
and §2.9's six window-base inequalities (re-computed from the Stage builder)
all match (§A3). The fresh-instance leg (§A2) adds **885 checks at g_m = 3
and order 5 with 0 violations** — outside every committed artifact's
parameter range. Leg scripts: `/tmp/pe8_fresh.py` + the disclosed
one-hunk engine-guard copy `/tmp/itl_g3.py` (md5
`b6577ae86a339cd204fddfc00deb047d`), both outside the repo, nothing staged.

---

## OBSERVATIONS (ungraded; recorded so they do not dangle)

1. **The "JC-PE7 next" arc tails and the 44 "0/2" counter sites at HEAD
   post-date-stamp to r6**, while PE7 has run clean and the ledger stands at
   1/2. Under the arc's own convention (the note is edited only in repair
   rounds; a clean pass produces none) these are round-records, and the
   LIFTCORNER acceptance precedent resolves them at the ledger fold (its
   acceptance record was appended to the note's tail at acceptance). If this
   pass is accepted, the same tail-record action is the natural place to
   close the note's own counter displays. Convention, not defect.
2. **§1's scalar-lift line** ("Λ_N(c) := realize(NR,c,N) for c ∈ K … by
   R2/R3, w(Λ_N(c)) = N and read(N,Λ_N(c)) = c") reads, at c = 0, against
   R2's own τ ≠ 0 hypothesis ((IN-5)'s law as quoted; the runners set
   Λ_N(0) = None and the SPAN legs handle the zero class separately, as the
   instrument's c = 0 disclosure records). The natural reading scopes the
   sentence by the cited laws' own hypotheses; every consuming site
   quantifies over K^* or handles 0 separately. Sub-minor wording, stood
   through seven passes without grading; recorded, not graded.
3. My XG3 stage required the disclosed one-hunk /tmp engine-guard widening
   (§A2) — i.e. the frozen engine cannot build g_j = 3 towers as shipped.
   If the arc ever wants a COMMITTED g_m ≥ 3 leg, that guard widening (a
   no-root test is complete for degree ≤ 3) plus its own mini-seal is the
   named, not-built candidate — same status genre as [r3, G-3]'s
   alt-corrected dense variant.

---

## §R RECOMMENDATION

**CLEAN: 0 CRITICAL, 0 GAPS — the second consecutive clean pass.** Per the
acceptance rule (2 consecutive clean passes accept) this pass completes the
requirement; recording the acceptance, advancing the counter to 2/2, and
appending the note's tail record are the orchestrator's ledger actions. What
would be accepted is exactly the note's fenced content: W-6/W-7/W-8/W-9 at
their stated grades on §0's conditionality stack ([ILN]† + GRB-conditional +
FGMN (a)(b) + (DMULT-w)-on-B + Thm 4.8/Cor 4.9 + Cor 2.7 CITED with the
numbering Codex leg owed + W-1/W-2/J-A/J-B at attempt), with the honest
boxes open as displayed — headed, unchanged, by (1) (DMULT-w) at composite
order + W-1's transport (TR-3′-GEN open), (2) JC-BOX-2's off-stratum
existence half (proof-only), (3) the non-integral residue JC-BOX-8(i),
(4) (DMULT-s) measured-only under JC-COB's sharp displays, (5) the top-flat
corner (JC-BOX-4, closed only on (DMULT-w)), (6) JC-F1/JC-F2 REVIEW-OWED.
No gate fires or retires with acceptance: J3b stays BLOCKED-ON-CARRIER-TIE
until (J-C)(ii)'s consumers act on the accepted tie per DITERSUP's own
gate text.

— GRTJC pass PE8, hostile verifier unit (fresh context), fixes nothing.
