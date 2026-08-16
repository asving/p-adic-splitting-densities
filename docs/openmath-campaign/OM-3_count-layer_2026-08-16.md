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

### 1.2 Certification record

* `verification/om3_dominance_split_check.py` — implements the §1.3 decomposition ALGORITHM
  verbatim and verifies, by exact integer enumeration on truncated windows, (i) coverage,
  (ii) pairwise disjointness, (iii) monotone nondegeneracy of every piece, (iv) exponent-form
  transport positivity, on a deterministic battery of instances at `r ≤ 3` with coefficients in
  `[−4, 4]`, strides up to 3, plus the corpus's 2SIDED instance. RESULT: see §1.4.
* `verification/om3_a0_oracle_check.py` — n = 3 order-1 window reads vs PARI `factorpadic` on the
  canonical lift AND a decorrelated random higher-digit lift, `q ∈ {2, 3}`, `N ∈ {2, 3}`.
  RESULT: see §1.4.

### 1.3 The dominance-split theorem (proof at transcription grade)

STATUS: written in §A below (appendix), certified by the §1.2 script before the proof was
finalized (owner method order: certify → prove).

### 1.4 Status

FILLED AT CLOSE — see the per-row table in §4.

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

### 2.2 Certification record

* `verification/om3_residual_census_check.py` — census law + κ(T) at
  `Q ∈ {2, 3, 4, 5, 8, 9}` (primes AND prime powers), n ≤ 5 (n ≤ 4 at Q ∈ {8, 9}); κ(T)
  decorated-shape instances by direct enumeration of decoration assignments. RESULT: §2.4.
* `verification/om3_s21_product_check.py` — the S2.1 multiplication bijection over `ℤ/p^N`
  (p = 2, 3) and `F_q[t]/(t^N)` (q = 2, 3, 4), degrees ≤ 4, N ≤ 3: bijectivity checked by exact
  image enumeration (injectivity + count + range). RESULT: §2.4.
* `verification/om3_bracket_history_check.py` — m = 2 per-composition history counts vs
  `alphaBracket` terms, `q ∈ {2, 3}`, both characteristics, N ≤ 6. RESULT: §2.4.
* `verification/om3_exactness_crossfoot_check.py` — exact q-power cross-foots (n = 2 complete;
  quartic (1²) stratum), `q ∈ {2, 3}`, N ≤ 5. RESULT: §2.4.

### 2.3 Proof/Lean record

* §B: the census law with κ(T) — complete proof.
* Lean witness file(s), named and justified in §4's landing table.

### 2.4 Status

FILLED AT CLOSE — see §4.

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

### 3.2 Certification record

* `verification/om3_beta_ledger_n4_check.py` — the n = 4 simple-slice per-genre β-ledger vs exact
  enumeration, `(q, N) ∈ {(2, 4), (2, 5), (3, 3)}`, both characteristics where tractable.
  RESULT: §3.4.
* (CS-1Q) genre-E/F ledger arithmetic table — in §C.3, exact rational arithmetic (no enumeration
  needed; the quantities are defined arithmetic expressions).

### 3.3 Proof record

§C: the n = 4 β-ledger lemma (statement + proof); the (CS-1Q) genre ledgers.

### 3.4 Status

FILLED AT CLOSE — see §4.

---

## 4. PER-ROW STATUS TABLE

FILLED AT CLOSE.

---

## §A. THE DOMINANCE-SPLIT THEOREM (HYP.26's residue; blueprint §16 item 6, math level)

TO BE WRITTEN AFTER CERTIFICATION (§1.2).

## §B. THE RESIDUAL CENSUS LAW WITH κ(T) (HYP.23)

TO BE WRITTEN AFTER CERTIFICATION (§2.2).

## §C. THE n = 4 SIMPLE-SLICE β-LEDGER AND THE (CS-1Q) GENRE LEDGERS (HYP.88, HYP.36)

TO BE WRITTEN AFTER CERTIFICATION (§3.2).
