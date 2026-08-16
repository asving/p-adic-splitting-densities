# OM-3 — THE COUNT LAYER (unit note, 2026-08-16)

**Unit:** OPEN-MATH OM-3 (fable, max reasoning). **Scope:** the exact per-degree counting laws
feeding the decided-density leg (`UniformityStatementDecided`): the (CS-1)/(CS-2)/(CS-EXACT)/
(CS-1Q) clause family and the (A0)/(A1) per-degree admissibility.
**Ledger rows:** HYP.23, HYP.25, HYP.26, HYP.30, HYP.32, HYP.33, HYP.35, HYP.36, HYP.88
(exact texts read from `spec/HYPOTHESIS_LEDGER.md` before work started).
**Method (owner directive):** per row-cluster — (1) high-level outline FIRST; (2) certify each
step by exact enumeration (`verification/`, both `q = 2` and `q = 3` minimum) or constructed
counterexample; (3) prove certified steps — math at transcription grade, Lean where the landed
vocabulary makes it cheap.
**Discipline honored:** GC-5 says `hwin`/`hprice` (HYP.36's (CS-1Q.a/b)) are CARRY with NO
universal discharge anywhere — this unit does NOT attempt to discharge them; its HYP.36 work is
the count-side clause only.

---

## 0. Interface inventory (verified at HEAD before any work)

Facts re-checked in the tree, cited below by these anchors:

* **[I-1]** `leanfinal/Uniformity/ChapH/H93.lean` / `H94.lean`: `A1Cell` (WITH the σ-label field,
  W-12 r4) and `LEMMA GENIND-0`'s closure — product (`A1Cell.prod`, `prod_exp`, `prod_σ_degree`),
  union (definitional on `List`), and the δ-substitution (`A1Cell.deltaSubst`, `deltaSubst_exp`).
  H.94's own ⚠: **the dominance-region split is NOT formalized and is declared OPEN**
  (blueprint §16 item 6) — clause (iii) lands the substitution *mechanism* only.
* **[I-2]** `H63.lean` lands the union bound `prod_sub_prod_le_sum` **at every r** (GENIND-C1(ii)'s
  leg F, which the corpus battery had only at r = 2, 3); `H64` the antitone lemma; `H65`–`H69` the
  `RateSpecies` calculus (growing/bounded regimes); `H72` `rate_lossPriced` consuming
  `StageInterface.hwin`/`hprice`. Verified sorry-free; H63 footprint = Lean core (re-ran
  `lake env lean` on H63, 2026-08-16).
* **[I-3]** `H09.lean` `StageInterface` (the (CS-1Q)+(CS-2)+(CS-3)-as-fields carrier); `H09w.lean`
  exhibits the genre-E and genre-F inhabitants at `stageLoss = 0` (the `EFF.GENIND.199` exemption,
  exactly GC-5's "H owns the two standalone quartic genres").
* **[I-4]** `H21.lean` the (CS-2) numeric certificate + mass/letter reconciliation
  (`alphaBracket_audit`, `massNorm_eq_ghost_mul_letters`); `H92.lean` the (CS-2) bracket at the two
  quartic genres (`subset_sum_pow`, `bracket_telescope_E`, `macroscopic_rate`); `H18/H20`
  `alphaBracket` + closed form `alphaBracket_eq : … = (Q−1)·Q^((c+1)μ−1)`.
* **[I-5]** ChapG ground truth: `G36` (`undecidedCount_two_eq`: the EXACT n = 2 undecided law
  `q^N` at level `N`, general complete DVR), `G37` (rate `q^{−N}`), `G49`–`G51` (the five cubic
  types + `CoveringMenu O 3`), `G72` (conditional total mass at n = 3).
* **[I-6]** Blueprint interface fields and the discharge/consume table:
  `blueprint/CHAP-H_general_induction.md` §3 (H.09's SIGNATURE NOTE: `hdrain_*` replace
  (CS-EXACT) for RATE consumers only; **"a node that needs the exactness identity must return
  RE-PLAN for an `exactDrain` field, not assume it"**) and
  `blueprint/CONVENTIONS_2026-08-15.md` GC-5 (who discharges what).
* **[I-7]** Sources re-read in full: `EFF.GENIND.30` (LEMMA GENIND-0 + OPEN-CALL 3),
  `.45/.46` (the S5.2 recursion + GENIND.C), `.63`–`.67` ((CS-1)/(CS-2)/(CS-3)/(CS-EXACT) displays
  + the corpus's own supply/fence record), `.78` (GENIND-BOX-4), `.91` (ANNEX R R1.0),
  `.152`–`.154` (GENIND-C1, GENIND.C′, the install record), `.197` ((CS-1Q) display);
  `EFF-W12.md` units at L505–530 (THEOREM W-12.A + the κ(T) correction), L790–816
  (LEMMA W12-S2.1 + the κ(T) rider on `C₀(q)`).

**Collision avoidance:** the in-flight `leancheck/UniformityCheck/N3*.lean` files (another unit's
n = 3 leg, untracked at my start) are not touched, cited, or duplicated; my adds are scoped to
`verification/om3_*.py`, this note, and the new Lean witness files named below.

---

## 1. CLUSTER A — the admissibility layer (HYP.25 `A0`, HYP.26 `A1`)

### 1.1 High-level outline

The (A1) predicate (per `EFF.GENIND.30` / W-12.D) is: a finite disjoint family list whose
parameter sets are shifted products of arithmetic progressions in `ℕ^r`, exponents affine with
strictly positive integer coefficients, `q`-independent coefficients, affine visibility, and (r4)
a σ-label per family. Its closure lemma (GENIND-0) has three legs; two are landed [I-1]. The third
leg — **the dominance-region split** (`{ν₁ ≥ ν₂} ∩ (shifted product)` is a finite disjoint union
of reparameterized shifted products) — is the corpus's one-line "induct on dimension" and the Lean
development's declared-open §16 item 6. **This is the cluster's real mathematical debt, and this
note discharges it at math level**: §1.3 gives a complete elementary proof (no citation needed),
whose induction is: eliminate the last coordinate by the sign of its coefficient; the unbounded
side is solved by a mod-B sub-box split + explicit tail parameterization; the bounded side by a
second induction on the number of variables in the dominating form, with an explicit two-region
parameterization. Every piece produced is an image of `ℕ^k` under an injective ℕ-affine map that
is *monotone nondegenerate* (each parameter strictly moves some coordinate), which is exactly the
condition under which strictly-positive exponent coefficients — and the σ-label — transport.

(A0) (HYP.25: every window-decided core-family member has all `disc ≠ 0` O-lifts of the read's
type) is a per-degree admissibility clause whose n ≤ 2 content is SUBSUMED by `leanfinal`'s landed
every-lift `DecidedAt` theorems (strictly stronger than the `disc ≠ 0`-fenced form, per GC-9); its
open content is at composite stages, where it is (CS-3) = HYP.24/34 — NOT this unit's row. The
OM-3 deliverable for HYP.25 is the certification record at the first non-landed degree (n = 3,
order-1 reads, both primes) plus the residue statement.

### 1.2 Certification record (executed, all green)

* `verification/om3_dominance_split_check.py` — implements the §A decomposition ALGORITHM
  verbatim and verifies, by exact integer enumeration on truncated windows (truncation soundness
  argued from monotone nondegeneracy in the script), (i) coverage, (ii) pairwise disjointness +
  injectivity, (iii) monotone nondegeneracy of every piece, (iv) exponent-form transport
  positivity, (v) the Lemma A.1 assertions on every constructed branch.  Deterministic battery:
  `r ≤ 3`, coefficients in `[−4, 4]` (sub-boxing exercised at `B ∈ {2, 3, 4}`, bounded-fiber
  second induction at `c ∈ {2, 3}`), strides to 3, offsets, the 2SIDED instance both
  orientations, strided max-split pairs.  **RESULT: 87/87 cells green** (run 2026-08-16).
* `verification/om3_a0_oracle_check.py` — every n = 3 class mod `p^N` at
  `(p, N) ∈ {(2,2), (2,3), (3,2), (3,3)}` gets the order-1 window read (independent
  implementation of the W-12.A rules: level-0 factorization; at the repeated center, shifted
  polygon + per-side residuals incl. the slope-0 co-branch side); each DECIDED class is checked
  against an independent PARI/GP oracle (`factor` over ℚ + `nfinit`/`idealprimedec` at `p` —
  no polygon, no residual read) on the canonical lift AND a decorrelated pseudo-random
  higher-digit lift, both with `disc ≠ 0`.  **RESULT: 19,758 decided classes, 39,516 oracle
  calls, 0 mismatches** (run 2026-08-16).  Scope notes: two lifts per class sample the
  all-lifts quantifier (the every-lift statement at n ≤ 2 is a landed Lean theorem; at n = 3 the
  order-1 read's lift-independence is exactly what W-12.A asserts — this is its decisive
  instance battery, not a proof); equal characteristic not covered by this leg (PARI has no
  `F_q((t))` factorization) — the equal-char count structure is carried by legs 3–5.

### 1.3 Proof record

* §A below: the dominance-split theorem — COMPLETE elementary proof (Lemma A.1 automatic
  positivity, Lemma A.2 bounded fiber, Theorem A by induction on `r` with the mod-B sub-box
  split, Corollary A′ = the σ-strengthened A1 closure leg).  Certified before finalization
  (owner method order: certify → prove).
* Lean: `H94w.lean` (set-level 2SIDED split: regions, injective parameterizations, disjointness,
  cover, exponent transport via H.94's `deltaSubst_exp`; plus `dominance_split_dim1`, the
  `r = 1` trichotomy at GENERAL ℕ-coefficients via `Nat.find`, no division).  Homed in
  `leanfinal/Uniformity/ChapH/` as an H-adjacent witness file (H09w precedent) because the
  landed A1 interface lives there; general split stays OPEN in Lean (blueprint §16 item 6 cost
  ruling) — declared in the file header.

### 1.4 Status

* **HYP.26 (A1):** the one open closure leg (dominance split / OPEN-CALL 3's residue) now has a
  complete certified math proof (§A) + partial Lean (2SIDED set level, r = 1 general).
  Disposition stays CARRY (the row is the whole fixed-n public interface), with the closure
  lemma's math debt cleared.
* **HYP.25 (A0):** n ≤ 2 subsumed by landed every-lift `DecidedAt` theorems (GC-9, strictly
  stronger than the `disc ≠ 0`-fenced form); n = 3 order-1 instance now decisively
  instance-certified against a decorrelated oracle.  Residue at composite stages = (CS-3) =
  HYP.24/34, not this unit's row.  Disposition stays CARRY.

---

## 2. CLUSTER B — the count laws (HYP.23 `[H-d]`, HYP.32 `CS-1`, HYP.33 `CS-2`, HYP.35 `CS-EXACT`)

### 2.1 High-level outline

* **HYP.23** ([H-d] residual censuses — "universal residual-tower censuses hold level by level").
  The load-bearing census objects are W-12.A's level-0 prefactor `C₀(q)` (the undecorated census
  of level-0 configurations), the per-side residual factors `S_λ(Q)` over the residue extensions
  `Q = q^d`, and the 2026-08-12 orbit correction `κ(T) = Π_{d,m} r_{d,m}!/Π_D r_{d,m,D}!`.
  The census LAW to state and prove: for a finite field `F_Q` and a factorization pattern
  `λ = {(dᵢ, mᵢ)}`, the number of monic degree-n polynomials with pattern λ is
  `Π_d C(I(d,Q); profile)` — a product of falling-factorial/multiset-choose factors in the
  irreducible counts `I(d, Q) = (1/d)Σ_{e|d} μ(e)Q^{d/e}`; and the decorated form
  `κ(T)·C₀(q) = Π_d I!/((I−R_d)!·Π_D r_{d,m,D}!)` — i.e. the κ-corrected display is EXACTLY the
  count of decoration-assigned configurations. Proof: §B. "Level by level" = the same law with
  `q → q^d` at each residual extension; the tower conditioning ([H-a]–[H-c] identify the reads) is
  NOT this unit's to discharge — the census law itself is unconditional finite-field combinatorics
  and is what this unit proves and certifies (prime AND prime-power `Q`, per GENIND-BOX-3's
  prime-power fence).
* **HYP.32** (CS-1 count-fibration). The landed order-1 shadow is LEMMA W12-S2.1 (the level-0
  product bijection). Certify S2.1 decisively (both characteristics, both primes, n ≤ 4); the
  order-≥2 residue is the READ CORRESPONDENCE (`EFF.GENIND.67`'s fence), which is CARRY and stays
  CARRY — narrowed here by stating exactly which sub-claims are now certified vs open.
* **HYP.33** (CS-2 stage bracket). The bracket IDENTITY is fully landed ([I-4]); what no landed
  artifact guards is bracket-vs-REAL-COUNTS: that actual per-history decided masses at a stage
  follow `Π (Q−1)Q^{c·kᵢ}` (mass normalization). Certify at the m = 2 ground stage (monic
  quadratics, both characteristics, both primes): per-composition history counts vs
  `alphaBracket`'s terms.
* **HYP.35** (CS-EXACT). Two deliverables: (a) the IDENTITY-direction inclusion–exclusion law
  `Π Tᵢ − Π(Tᵢ − uᵢ) = Σ_{∅≠S}(−1)^{|S|+1}Π_S u Π_{S^c} T` — the exactness form GENIND-6(d)
  prices ("children's u's exact by (IH) member 4, stage drains exact by (CS-EXACT)") — landed in
  Lean at every r (new witness file, §2.3); H.63/H.64 landed only the bound direction. (b) exact
  q-power cross-foots at the landed strata (n = 2 menu + `q^N`; the quartic λ = (1²) stratum
  volume law `(q−1)q^{4N−5h−3}`), both primes. The RE-PLAN fence of H.09 (no `exactDrain` field)
  is respected: nothing here adds interface fields.

### 2.2 Certification record (executed, all green)

* `verification/om3_residual_census_check.py` — (B.1) necklace vs sieve, (B.2) pattern census vs
  brute factorization of ALL monics, (B.3) κ(T) vs direct enumeration of decorated
  configurations, at `Q ∈ {2, 3, 4, 5, 8, 9}` (primes AND prime powers, both residue
  characteristics), n ≤ 6 at Q ∈ {2, 3}, n ≤ 5 at {4, 5}, n ≤ 4 at {8, 9}.
  **RESULT: 92/92 cells green** (run 2026-08-16).
* `verification/om3_s21_product_check.py` — the S2.1 multiplication map checked as a bijection
  (injectivity + fiber membership + counts; |Π branches| = |fiber| holds by construction, so
  injectivity is the content) over `ℤ/p^N` (p = 2, 3, N ≤ 4) and `F_q[t]/(t^N)` (q = 2, 3, 4,
  N ≤ 3), shapes through n = 4 incl. two-same-(d,m)-branch and three-branch shapes.
  **RESULT: 32/32 cells green** (run 2026-08-16).  Scope: the count-fibration transport only;
  S2.1's σ-branchwise clause not exercised here.
* `verification/om3_bracket_history_check.py` — the conservative m = 2 reader run exhaustively:
  (C.1) per-composition real masses = `Π (Q−1)Q^{c(2)·kᵢ}` × head (the MASS-normalized bracket
  terms, ghost included, against real polynomial counts — the connection no landed artifact
  guarded); (C.2) per-κ aggregate = `alphaBracket(Q,1,κ)`·head = closed form; (C.3) telescope
  `u(N) = Q^{N−1}` + the SEMANTIC cross-check (undecided ⟺ `Δ ≡ 0 mod p^N`) at odd p;
  (C.4) the q = 3 non-degeneracy cell (18 ≠ 36).  Rings: `ℤ/p^N` p = 2 (N ≤ 7), p = 3 (N ≤ 5);
  `F_q[[t]]` q = 2, 3, 4.  **RESULT: all cells green** (run 2026-08-16).
* CS-EXACT shape certification is carried by legs 4–5 (every certified law is an exact
  census × Q-power product; the quartic (1²)-stratum volume law `(q−1)q^{4N−5h−3}` reproduced
  exactly incl. the corpus's own spot values) — the separate cross-foot script promised in the
  outline draft was folded into those legs rather than duplicated.

### 2.3 Proof/Lean record

* §B below: Theorem B (pattern census, every finite residue field) and Theorem B′ (κ(T) IS the
  decoration-orbit factor) — complete proofs; the 2026-08-12 κ(T) correction is now a proved
  theorem with a decisive prime-power battery.
* Lean: `H63w.lean` — `prod_sub_eq_signed_sum` and `prod_sub_prod_eq_signed_sum`: the
  (CS-EXACT)-side inclusion–exclusion IDENTITY at every `r` over any `CommRing` (H.63 landed
  only the bound direction; the corpus's leg F had the identity at `r = 2, 3` symbolically).
  H.09's RE-PLAN fence respected: no `exactDrain` field is added; the identity is the
  composition law, not a per-stage discharge.

### 2.4 Status

* **HYP.23 ([H-d]):** the census LAW (with κ(T)) proved and certified at prime AND prime-power
  residue fields; the [H-a]–[H-c] tower-read conditioning untouched.  Disposition stays NODE,
  with the law side no longer bare.
* **HYP.32 (CS-1):** order-1 shadow (S2.1) decisively certified both characteristics; the
  residue is EXACTLY `EFF.GENIND.67`'s fence — the step-for-step READ CORRESPONDENCE at
  composite stages (plus the m ≥ 3 child-transport fibration, see §C).  Disposition stays CARRY,
  residue narrowed and named.
* **HYP.33 (CS-2):** the bracket now has teeth AGAINST REAL COUNTS (per-composition, mass
  normalization, ghost factor observed as the actual free digits) at the m = 2 ground stage in
  both characteristics — previously the only guards were arithmetic identities (H.21/H.92).
  General-genre discharge stays with C per GC-5.  Disposition stays CARRY.
* **HYP.35 (CS-EXACT):** identity-direction composition law landed in Lean at every r (H63w);
  exact-shape instance certifications at n = 2 (leg 4), n = 4 first-read layer (leg 5).
  Per-stage exactness stays CARRY; the deliberate no-field ruling (H.09) respected.

---

## 3. CLUSTER C — the drainage side (HYP.30 `DRAIN-N4`, HYP.36 `(CS-1Q)` count-side, HYP.88 `GENIND-BOX-4`)

### 3.1 High-level outline

* **HYP.36.** GC-5: `hwin`/`hprice` CARRY, per-genre instances only; the two standalone quartic
  genres are landed ([I-3]). This unit's count-side add: the explicit per-genre (CS-1Q) affine
  LEDGER for genres E and F at general `(h, N)` — the display the corpus says is what a per-genre
  verification consists of — stated, checked by exact arithmetic at `q ∈ {2, 3}`, `h ≤ 3`, and
  recorded as the genre-E/F rows of the "verified per genre" list. Embedded/mixed genres stay
  BLOCKED: HYP.36 (no attempt, per the work order).
* **HYP.30** (DRAIN-N4). CARRY with lower supplier HYP.36 — not dischargeable here. Deliverable:
  the outline of exactly which certified pieces (GENIND.C′ unconditional simple part; C2Q
  conditional CS part) compose to it, plus the n = 4 numeric leg below (which certifies the
  simple-slice ingredients it consumes).
* **HYP.88** (GENIND-BOX-4 — class MATH: "separate bookkeeping proof" of the simple-slice β-term
  bookkeeping compression). After ANNEX R R1, the box's residue is the **per-genre prefactor
  ledgers** (R1.4: "GENIND-BOX-4's pricing of the per-genre expansion STANDS for what remains
  compressed"). This unit expands the ledger at n = 4: enumerate the simple-slice β-genres of
  degree 4 (partition + integer-slope data), display each genre's route-prefactor count law,
  PROVE the displayed laws (elementary slot counts, §C), and certify them decisively at
  `q ∈ {2, 3}`, both characteristics. The general-(m, d) ledger stays open at exactly the
  corpus's scope; the n = 4 instance converts the box's "displayed, not expanded per genre" into
  "expanded and proved at the first degree where β-genres exist".

### 3.2 Certification record (executed, all green)

* `verification/om3_beta_ledger_n4_check.py` — EVERY first-read genre of the n = 4 single-center
  branch (up to 30 genres per cell) checked at three layers: (D.2) per explicit residual tuple
  the count is exactly `Q^{Σ free digits}`; (D.3) per genre the number of residual tuples is
  exactly the product of y-excluded pattern censuses (the §B law feeding the ledger, as [H-d]
  says it should); (D.1 = D.2 × D.3) the per-genre ledger; plus the partition cross-foot, the
  deep bucket `Q^{3(N−1)}`, and the named instances (α = GENIND.A(I); CS4-E incl. the corpus's
  battery spot values 162/13122; the distinct-slope and same-slope β-genres).
  Cells: `ℤ/p^N` at (2,4), (2,5), (2,6), (3,3), (3,4); `F_q[[t]]` at (2,4), (2,5), (3,3) and
  `F_4` (prime-power residue field); same-slope two-children genre reached by the `v(a₀) = 4`
  slice at (3,5), both characteristics.  **RESULT: all cells green** (run 2026-08-16).
* (CS-1Q) genre-E/F: no new enumeration — the ledgers are the `hwin`/`hprice` proof fields of
  the landed `H09w` witnesses (machine-checked); see §C.3.

### 3.3 Proof record

§C below: Lemma C.1 (explicit-residual count) and Lemma C.2 (per-genre ledger = census ×
Q-power) — proved DEGREE-AGNOSTICALLY (not just n = 4); the n = 4 ledger table; the §C.3
(CS-1Q) record.

### 3.4 Status

* **HYP.88 (GENIND-BOX-4, class MATH):** the "per-genre prefactor ledgers" residue (R1.4) is
  now PROVED at the first-step layer at every degree (C.1 + C.2) and certified exhaustively at
  n = 4 both characteristics.  The remaining debt is the recursive child-transport
  count-isomorphism at m ≥ 3 — which is HYP.32's (CS-1) residue, not a separate bookkeeping box.
  Proposed re-disposition for the next ledger fold: MATH → partially discharged, residue
  re-pointed at HYP.32.
* **HYP.36 ((CS-1Q)):** count-side only, per the work order: the standalone-quartic (E/F) rows
  of the per-genre-verified list are recorded (they are H09w's landed proof fields, at the
  stageLoss = 0 exemption); embedded/mixed stays BLOCKED: HYP.36.  `hwin`/`hprice` NOT touched.
  Disposition stays CARRY.
* **HYP.30 (DRAIN-N4):** not dischargeable here (CARRY, lower supplier HYP.36).  What this unit
  adds to its supply chain: the simple-slice ingredients it consumes are now better-certified
  (the exact first-step per-genre ledger at n = 4; the m = 2 fibration; the union-bound identity
  side).  NOTE for composition: OM-1's `package_three` (append #67) makes `P(2)`, `P(3)` both
  unconditional, so GENIND.B's base cases are theorems; HYP.30 remains the n ≥ 4 CS-side gap.

---

## 4. PER-ROW STATUS TABLE

| row | clause | what OM-3 did | landed artifacts | disposition after |
|---|---|---|---|---|
| HYP.23 | `[H-d]` residual censuses | census law + κ(T) PROVED (§B) and certified at Q ∈ {2,3,4,5,8,9} (92 cells) | `om3_residual_census_check.py`; §B | NODE (unchanged); law side proved |
| HYP.25 | `(A0)` lift well-posedness | n=3 order-1 decisive oracle battery (19,758 classes × 2 lifts, 0 mismatches); n≤2 noted subsumed by landed every-lift theorems | `om3_a0_oracle_check.py` | CARRY (unchanged); instance-certified |
| HYP.26 | `(A1)` exact core menu | the OPEN closure leg (dominance split, §16 item 6) PROVED in math (§A), algorithm certified 87/87; 2SIDED set-level + r=1 trichotomy in Lean | `om3_dominance_split_check.py`; `H94w.lean`; §A | CARRY (unchanged); closure-lemma debt cleared at math level |
| HYP.30 | `DRAIN-N4` | supply-chain certification only (see §3.4) | — | CARRY (unchanged) |
| HYP.32 | `(CS-1)` count-fibration | S2.1 bijection certified both characteristics (32 cells); residue narrowed to the read correspondence + m≥3 child transport | `om3_s21_product_check.py` | CARRY (unchanged); residue named |
| HYP.33 | `(CS-2)` stage bracket | bracket vs REAL per-history counts, mass normalization + ghost observed, q=2/3/4 both characteristics | `om3_bracket_history_check.py` | CARRY (unchanged); first real-count teeth |
| HYP.35 | `(CS-EXACT)` | identity-direction composition law in Lean at every r; exact-shape instance batteries | `H63w.lean`; legs 4–5 | CARRY (unchanged); composition identity landed |
| HYP.36 | `(CS-1Q)` | count-side record of the E/F per-genre rows (H09w proof fields); hwin/hprice untouched per GC-5 | §C.3 | CARRY (unchanged) |
| HYP.88 | `GENIND-BOX-4` | per-genre prefactor ledger PROVED (first-step, all degrees) + n=4 exhaustive certification | `om3_beta_ledger_n4_check.py`; §C | MATH → propose: partially discharged, residue re-pointed at HYP.32 |

---

## §A. THE DOMINANCE-SPLIT THEOREM (HYP.26's residue; blueprint §16 item 6, math level)

Certified BEFORE finalization: `verification/om3_dominance_split_check.py` implements the proof's
decomposition verbatim and verifies coverage, disjointness, injectivity, nondegeneracy and
exponent transport on 87/87 exact cells (r ≤ 3, coefficients to ±4, strides to 3, offsets,
2SIDED both orientations), with the proof's Lemma A.1 assertions armed on every branch.

**Definitions.** A *monotone affine map* `φ : ℕ^k → ℕ^r` is `φ(t) = v + M·t` with `v ∈ ℕ^r`,
`M ∈ ℕ^{r×k}`, and every column of `M` nonzero (each parameter strictly moves some coordinate).
A *piece* is the image `φ(ℕ^k)` of an injective monotone affine map.

**Transport lemma.** If `ℓ(p) = e₀ + Σ eᵢpᵢ` has every `eᵢ ≥ 1` and `φ` is monotone affine, then
`ℓ∘φ` is affine with every coefficient `Σᵢ eᵢ·M[i][j] ≥ 1` (column `j` is nonzero).  Hence an
A1 exponent stays an A1 exponent on every piece, and the σ-label (constant) rides along — the
σ-strengthened predicate is preserved.

**LEMMA A.1 (automatic positivity).** If an affine `e : ℕ^k → ℤ` satisfies `e ≥ 0` on all of
`ℕ^k`, then every coefficient of `e` is ≥ 0 and `e(0) ≥ 0`.
*Proof.* `e(M·e_j) = e(0) + M·c_j ≥ 0` for every `M ∈ ℕ` forces `c_j ≥ 0`; `M = 0` gives the
constant. ∎

**LEMMA A.2 (bounded fiber).** For `g : ℕ^k → ℕ` affine with ℕ-coefficients and `m₀ ∈ ℕ`, the
set `F = {(u, x) ∈ ℕ^k × ℕ : x ≤ g(u) + m₀}` is a finite disjoint union of pieces.
*Proof.* Induction on the number of variables of `g` with nonzero coefficient.
*Base* (`g ≡ g₀` constant): `F = ⨆_{j=0}^{g₀+m₀} ℕ^k × {j}`, each summand the piece
`u ↦ (u, j)` (identity columns; the `x`-coordinate has no parameter).
*Step*: pick a variable `v` with coefficient `c ≥ 1`; write `g(u) = g₀(u′) + c·v`.
Split `F` on `x ≤ g₀(u′) + m₀`:
· *Region 1* `= {x ≤ g₀(u′) + m₀}` with `v` free: decompose the `(u′, x)`-set by the induction
  hypothesis and insert `v` as a free parameter.
· *Region 2* `= {g₀(u′) + m₀ < x ≤ g₀(u′) + m₀ + c·v}`: substitute `x = g₀(u′) + m₀ + y` with
  `1 ≤ y ≤ cv` (which forces `v ≥ 1`); write `y − 1 = c·w + j` uniquely with `0 ≤ j ≤ c − 1`;
  then `y ≤ cv ⟺ w ≤ v − 1 ⟺ v = w + 1 + z`, `z ∈ ℕ`.  Region 2 is therefore
  `⨆_{j=0}^{c−1}` (image of `(u′, w, z) ↦ (u′, v = w + 1 + z, x = g₀(u′) + m₀ + c·w + j + 1)`).
  Injective (`u′` direct; `w, j` from `x − g₀(u′) − m₀ − 1` by division by `c`; `z` from `v`);
  monotone (`w` moves `x` with coefficient `c`; `z` moves `v`); the `j`-pieces are disjoint
  (distinct residues mod `c`) and disjoint from Region 1 (`x`-comparison); the two regions
  cover `F`. ∎

**THEOREM A (dominance split).** For any affine `d : ℕ^r → ℤ`, `d(t) = C + Σ Bⱼtⱼ`
(`C, Bⱼ ∈ ℤ`), the region `{t ∈ ℕ^r : d(t) ≥ 0}` is a finite disjoint union of pieces.
*Proof.* Induction on `r`.  `r = 0`: the single point (if `C ≥ 0`) or empty.  `r ≥ 1`: write
`d = d′(t′) + B·x` with `x` the last coordinate.
· **B = 0**: decompose `{d′ ≥ 0} ⊆ ℕ^{r−1}` (IH) and give every piece a free last coordinate.
· **B > 0**: split the base into `P = {d′ ≥ 0}` and `N = {−d′ − 1 ≥ 0}` — disjoint, exhaustive,
  both of the theorem's class at dimension `r − 1` (IH ⟹ pieces `ψ`).
  Over `P`: every `x` works (`d ≥ d′ ≥ 0`): contribute `ψ ×` (free `x`).
  Over an `N`-piece `ψ : ℕ^k → ℕ^{r−1}`: set `e := −(d′∘ψ)`.  Since `ψ(ℕ^k) ⊆ N`, `e ≥ 1`
  everywhere, so by Lemma A.1 `e = e₀ + Σ cᵢtᵢ` with `cᵢ ≥ 0`, `e₀ ≥ 1`.  The fiber condition
  is `B·x ≥ e(t)`.  **Sub-box split**: for each `ρ ∈ {0..B−1}^k` substitute `tᵢ = B·sᵢ + ρᵢ`
  (the `B^k` sub-boxes partition `ℕ^k`); on the `ρ`-sub-box `e = E₀ + B·g(s)` with
  `E₀ = e₀ + Σ cᵢρᵢ` and `g(s) = Σ cᵢsᵢ`.  Then `B·x ≥ E₀ + B·g(s) ⟺ x ≥ g(s) + ⌈E₀/B⌉ =: g(s)
  + m₀ ⟺ x = g(s) + m₀ + y`, `y ∈ ℕ`: contribute the piece
  `(s, y) ↦ (ψ(B·s + ρ), g(s) + m₀ + y)` — injective (base injective; `y` from `x` given `s`),
  monotone (`sᵢ` moves the base through `B·`(nonzero column); `y` moves `x`).
· **B < 0**, `b := −B`: over `N` no point survives (`d ≤ d′ < 0`).  Over a `P`-piece `ψ`:
  `e := d′∘ψ ≥ 0` has ℕ-coefficients (Lemma A.1); sub-box mod `b` gives `e = E₀ + b·g(s)`, and
  the fiber is `x ≤ ⌊e/b⌋ = g(s) + ⌊E₀/b⌋`.  Decompose `{(s, x) : x ≤ g(s) + m₀}` by Lemma A.2
  and compose each piece with `(ψ∘subbox) × id_x`.
Disjointness at every join: `P`/`N` disjoint; IH pieces disjoint; sub-boxes partition; fibers
parameterized bijectively.  Coverage by construction.  All unions finite. ∎

**COROLLARY A′ (the A1 closure leg, σ-strengthened — `EFF.GENIND.30`'s third clause).**
For an `A1Cell` (offsets `o`, strides `s ≥ 1`, exponent `ℓ` with strictly positive coefficients,
coefficient `c`, label σ) and ℕ-affine `ν₁, ν₂`:
`{p ∈ locus : ν₁(p) ≥ ν₂(p)}` is a finite disjoint union of pieces, each the image of an
injective monotone affine parameterization carrying the transported exponent (strictly positive
coefficients, by the transport lemma), the dominating form as its (affine) visibility, the same
`c`, and the same σ.
*Proof.* Parameterize the locus by `t ↦ o + s·t` (injective, monotone); `d(t) := ν₁(o + st) −
ν₂(o + st)` is ℤ-affine; apply Theorem A in `t`-space and push each piece forward (composition
of injective monotone affine maps is one). ∎

**Remarks.** (0) *Constructed counterexample sharpening the statement* (the mandated attack on
the non-enumerable step): WITHOUT the reparameterization clause the corpus's sentence would be
false — `{p₁ ≥ p₂} ⊆ ℕ²` is NOT a finite union of unreparameterized shifted products, even
allowing degenerate (lower-dimensional) products.  Argument, piece by admissible piece: a full
2-parameter product contains `(o₁, o₂ + s₂t)` with `p₂` unbounded at fixed `p₁`, leaving the
region; a vertical line `{(c, o₂ + s₂t)}` likewise; a horizontal line `{(o₁ + s₁t, c)}` meets
the diagonal `{(n, n)}` in at most one point (`o₁ + s₁t = c`), and a single point in exactly
one.  So every piece contained in the region meets the infinite diagonal — which lies inside
the region — in at most one point, and no finite union covers.  [The finite-union half of this
argument was supplied in response to the Codex verifier's JUSTIFICATION GAP finding; see the
verification record below.]  Every piece must therefore be an affine IMAGE, exactly as Theorem
A produces.
The mixed-sign `r = 3`, large-coefficient battery cells are the adversarial instances against
the proof's case analysis (the G.23 coincidence-regime lesson transposed: sub-boxing is
invisible at `|B| = 1`, so the battery forces `B ∈ {2, 3, 4}`); all survived.
(i) The pieces have varying parameter dimensions and are given by *embeddings*, not
by cells at the ambient `r` — exactly why H.93's fixed-`r` `A1Family` cannot state the split
internally and the corpus's clause speaks of "affine re-parameterizations". (ii) The statement is
a special case of the disjoint decomposition of semilinear sets (Eilenberg–Schützenberger 1969 —
attribution from memory, flagged for lookup; nothing above rests on it: the proof is
self-contained). (iii) Lean status: the 2SIDED instance and the `r = 1` general-coefficient
trichotomy are landed (`H94w.lean`); the general split stays OPEN in Lean per the blueprint's own
cost ruling (§16 item 6), with this section as the math-level discharge and the certified
algorithm as its executable regression.

**Verification record (decorrelated adversarial pass, 2026-08-16).** This section was handed to
Codex (fresh context, quote-and-classify charge, fix-nothing) with an explicit attack list
(disjointness/coverage joins, Lemma A.1 legitimacy on piece parameter spaces, ceiling/floor
arithmetic, degenerate cases `k = 0`/`B = 1`/zero coefficients/empty regions, well-foundedness,
Corollary A′ transport).  Verdict: **no critical error; Lemmas A.1–A.2, Theorem A, Corollary A′
verified correct**, with one finding — a JUSTIFICATION GAP in the *nonessential* Remark (0)
(the counterexample argument omitted the finite-union obstruction for lower-dimensional
unreparameterized products).  The gap is closed in the remark's present form (the diagonal
argument); the proof body needed no repair.

## §B. THE RESIDUAL CENSUS LAW WITH κ(T) (HYP.23)

Certified BEFORE finalization: `verification/om3_residual_census_check.py`, 92/92 cells at
`Q ∈ {2, 3, 4, 5, 8, 9}` — primes AND prime powers in both residue characteristics, per
GENIND-BOX-3's prime-power fence.

**THEOREM B (pattern census, every finite residue field).** Let `F_Q` be the field with `Q`
elements and `I(d) = (1/d) Σ_{e|d} μ(e) Q^{d/e}` (the Gauss necklace count of monic
irreducibles — Möbius inversion of `Σ_{d|n} d·I(d) = Q^n`).  For a factorization pattern λ
assigning to each degree `d` multiplicities `m` with counts `r_{d,m}` (write `R_d = Σ_m r_{d,m}`):
```
#{monic f with pattern λ}  =  Π_d  I(d)! / ( (I(d) − R_d)! · Π_m r_{d,m}! ).
```
*Proof.* By unique factorization a monic `f` with pattern λ corresponds bijectively to a choice,
for each `d`, of `R_d` DISTINCT monic irreducibles of degree `d` with an assignment of the
multiset of multiplicities to them.  Count injections of the `R_d` slots into the `I(d)`
irreducibles and quotient by the order within identical-multiplicity groups:
`I·(I−1)⋯(I−R+1)/Π_m r_{d,m}!`.  Degrees independent. ∎

**THEOREM B′ (κ(T) is exactly the decoration-orbit factor — the 2026-08-12 W-12.A correction,
proved).** If branches within a `(d, m)` class carry decorations `D` with multiplicities
`r_{d,m,D}` (`Σ_D r_{d,m,D} = r_{d,m}`), then
```
#{decorated configurations}  =  Π_d I!/((I−R_d)!·Π_{m,D} r_{d,m,D}!)  =  κ(T) · C₀(Q),
κ(T) = Π_{d,m} r_{d,m}!/Π_D r_{d,m,D}!,
```
with `C₀(Q)` Theorem B's undecorated product.
*Proof.* The same injection count with the finer symmetry group `Π_{m,D} r_{d,m,D}!` in place of
`Π_m r_{d,m}!`; the ratio of the two counts is κ(T) termwise. ∎

**Level-by-level.** [H-d]'s "residual-tower censuses hold level by level" consumes exactly this
law over the residue extensions `F_{Q^d}` — hence the prime-power leg of the certification
(`Q = 4, 8, 9`).  The [H-a]–[H-c] conditioning (that the tower reads ARE the objects being
censused) is untouched here and stays with the row's NODE disposition; what this section
supplies is the census law itself, unconditional, with the κ(T) rider now a proved theorem
rather than a correction append.

## §C. THE SIMPLE-SLICE β-LEDGER (HYP.88) AND THE (CS-1Q) GENRE LEDGERS (HYP.36)

Certified BEFORE finalization: `verification/om3_beta_ledger_n4_check.py` — 9 full cells + 2
slice cells, every first-read genre at `(q, N) ∈ {(2,4), (2,5), (2,6), (3,3), (3,4)}` mixed
characteristic and `{(2,4), (2,5), (3,3)}_{F_q[[t]]}` + `F_4[[t]]` equal characteristic (up to 30
genres per cell), all green.

**Setting.** Per center at degree `m`: members are monic degree-`m` with reduction `x^m`
(coefficients `a_{m−1}..a₀` over `O/π^N`, `v ≥ 1` each; total `Q^{m(N−1)}`).  The *first-read
datum* (genre) of a window-solid member (`v(a₀) ≤ N−1`) is its Newton hull `H` (sides `S` of
length `L_S`, slope `num_S/den_S` in lowest terms) together with each side's residual
factorization pattern `λ_S` over `F_Q` (residuals read at the `den_S`-strided line digits and
unit-normalized).

**LEMMA C.1 (explicit-residual count).** For a window-solid hull `H` with heights `ℓ(i)` and a
prescribed residual tuple: `#members = Q^{Σ_{i<m} freeᵢ}` with `freeᵢ = N − 1 − ℓ(i)` at integer
line heights and `N − ⌈ℓ(i)⌉` at non-integer ones.
*Proof.* Digit bookkeeping per abscissa: positions below the hull line are pinned to 0 (this IS
`v(aᵢ) ≥ ℓ(i)`), the on-line digit at integer heights is the prescribed residual coefficient,
and all higher digits are free.  The polygon of every such member is exactly `H`: the residual
END coefficients are units, so the vertex valuations are exact, and `v ≥ ℓ` pointwise pins the
hull from below.  Conversely, membership in the class determines exactly these digits. ∎

**LEMMA C.2 (per-genre ledger = census × Q-power).** For a genre `g = (H, (λ_S)_S)`:
```
#members(g)  =  [ Π_S S⁰_{λ_S}(Q) ] · Q^{Σ freeᵢ},
```
where `S⁰_λ(Q)` is Theorem B's census over `F_Q` restricted to nonzero constant term — i.e. with
`I(1) → I(1) − 1` (the letters live in `F_Q^×`).
*Proof.* By C.1 it remains to count residual tuples with the given patterns.  Orient sides
right-to-left: the rightmost side's leading coefficient is the monic `1`, and each shared-vertex
digit is simultaneously the left side's leading and the right side's trailing coefficient — so
the whole tuple is determined by the list of MONIC normalizations, one per side, and conversely.
A side's monic residual is an arbitrary monic polynomial of degree `L_S/den_S` with nonzero
constant term (its constant is the left vertex's unit digit; any such polynomial arises).  Count
by Theorem B with `y` excluded from the degree-1 irreducibles. ∎

**The lemmas are degree-agnostic** — nothing in C.1/C.2 uses `m = 4`.  What the certification
instantiates at `m = 4` (the first degree with β-genres) is the full genre inventory: named rows
of the certified ledger, in the per-center measure `Q^{4(N−1)}`:

| genre (sides@slopes, residual pattern) | ledger law | certified |
|---|---|---|
| α: `[4]@k`, `(y−z)⁴` | `(Q−1)·Q^{4(N−1)−10k}` — GENIND.A(I)'s `(Q−1)Q^{−k·m(m+1)/2}` | (2,5), (2,6) |
| CS-exit E: `[4]@h/2` (h odd), `(y−z)²` | `(Q−1)·Q^{4N−5h−3}` — `EFF.GENIND.48`'s CS4-E law, incl. the corpus's own spot values 162 at (3,3) and 13122 at (3,4) | all cells |
| β distinct-slope: `[1]@2 ⊔ [3]@1`, `(y−w)`, `(y−z)³` | `(Q−1)²·Q^{4(N−1)−11}` | (2,6) |
| β same-slope two children: `[4]@k`, `(y−z₁)²(y−z₂)²` | `((Q−1)(Q−2)/2)·Q^{4(N−1)−10k}` | (3,5)-slice, both characteristics |
| deep bucket (`a₀ ≡ 0`) | `Q^{3(N−1)}` | all cells |
| … every other observed genre (up to 30 per cell) | `Π_S S⁰_{λ_S}(Q) · Q^{Σ free}` | all cells (D.2 + D.3 layers) |

**What this does and does not discharge for HYP.88.** GENIND-BOX-4's post-ANNEX-R residue is
"the per-genre prefactor ledgers" (R1.4).  C.1 + C.2 PROVE the first-step per-genre ledger at
every degree `m` — each β-genre's route prefactor is an exact census × Q-power product, not just
GENIND-C1(i)'s bound `Q^{−(D_l−1)}` — and the m = 4 instance is certified exhaustively in both
characteristics.  NOT discharged here: the recursive leg — the count-isomorphism transporting
each continuing child to its own `(μ_l, d)` system at window `M_l` (certified at `m = 2` by leg
4's per-composition fibration, `ghost = Q^{c·k}` exact; at `m ≥ 3` this is exactly HYP.32's
(CS-1) read-correspondence residue, not a separate bookkeeping box).  HYP.88's class-MATH demand
"a separate bookkeeping proof" is met at the ledger layer; the residue is re-pointed at HYP.32.

**§C.3 The (CS-1Q) standalone-quartic ledgers (HYP.36, count side).** For the two standalone
quartic genres (E and F) the corpus grants the `stageLoss = 0` exemption (`EFF.GENIND.199`), and
the affine ledger degenerates to the ZERO ledger: (CS-1Q.a) `e₁(N−1−H) ≤ stageWindow + 0` holds
at equality with `stageWindow = e₁(N−1−H)`, and (CS-1Q.b) `2f₁·0 ≤ 2·entryCodim + (S−2·keyDeg)H
+ 2·slack` holds with every term 0 at the minimal side length `S = 4 = 2·keyDeg`.  These are not
new claims of this unit: they are exactly the `hwin`/`hprice` PROOF FIELDS of the landed
`stageIfaceE`/`stageIfaceF` witnesses (`H09w.lean`), machine-checked; recorded here as the
genre-E/F rows of the "(CS-1Q) verified per genre" list.  Embedded/mixed genres: **BLOCKED:
HYP.36** — no attempt, per GC-5 and the unit work order.
