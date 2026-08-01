# HDISCHARGE_H7 — the (I-τ)/K-LOC sibling-interface pair: fine-grained discharge blueprint

**REVISION 2** (2026-08-05): the Codex adversarial review of draft 1 returned REVISE —
15 criticals + 2 justification gaps (`lean/notes/openmath/H7_bp_review.md`, verbatim
archive). ALL 17 findings folded; disposition table at §7. Headline changes: the K-LOC
statement is re-domained to the polydisc and re-shaped to exactly GMN 2.26's N_r^−/fixed-λ
form with the frame-comparison kernel (KL-0) split out as a named OPEN kernel; f₀ gets a
genuine pinned factor cell; the Lean W0–W2 layer is RE-GRADED as interface-shadow plumbing
(it discharges NOTHING semantic — the semantic rows are W3 obligations); route B gains its
missing read-fiber kernel (IT-4b, OPEN); two Lean statements repaired (`one_le_thr`,
`hm : 1 ≤ m`) and RE-PROBED green.

**Lead:** H7 discharge lead (hypothesis-discharge swarm, Asvin directive 2026-08-05,
ledger `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"ASVIN DIRECTIVE … THE
HYPOTHESIS-DISCHARGE SWARM"). **Authority for content:**
`docs/ROOT_ASSEMBLY_2026-08-02.md` (ROOT-C)(H7) + the §3.1 (I-τ)/K-LOC row (REVISION 6,
finding F-1; enumeration state REVISION 12). **Leaf sources of record:**
`lean/notes/openmath/O10_phaseB_attempt_rev2.md` (VERIFIED leaf #6 — Theorem 1 K-COUNT,
Theorem 2 adapted-(SIB), the (I-τ) display §4.3), `lean/notes/openmath/M07-sibjc_fable.md`
(OL-3 = K-LOC; the K-FACT/K-LOC/K-JAC/K-COUNT reduction; the three adversarial routes),
`lean/LeanUrat/MovesU/SibJcRouteA.lean` (the compiled route-(a) fence gate),
`lean/LeanUrat/Scaffold/ValueSide/KCount.lean` (BP_IV's landed K-units incl. `EngineSIBRow`),
`docs/GMN_citations.md` §6.0 (the Thm 2.26 verbatim pin). **Unit discipline:** this is a
BLUEPRINT-ONLY unit — no `Scaffold/HDischarge/` `.lean` file lands here; prover fan-outs
run separately. All §3 unit statements COMPILE-PROBED against the built corpus
(2026-08-05, two probe rounds; KCount olean refreshed to source REVISION 3 first — it was
stale and hid `EngineSIBRow`/`sib_product_law`/`kcount_fiber_card`; probe files deleted).

---

## 0. The hypothesis, restated exactly, and what discharge means

**(H7)** [ROOT §1, verbatim scope]: the sibling-interface engine-stratum conformance pair

> **(I-τ)** — the engine's realized site strata present as O-10's ρ-separated adapted
> cells (the adapted-cell → engine-stratum presentation Theorem 2 needs);
> **(K-LOC)** (= M07 OL-3, an exactly-stated OPEN lemma) — continuation reads of branch j
> on the stratum = OM reads of f_j up to cell-constant normalization.

**Consumption (triple-displayed):** ROOT §2 Step 15's application-to-engine-strata line;
Step 18's K1 "(I-τ)→GD" (without the pair, K1 does not receive O-10's product law at the
engine's strata); the §3.1 row's own owner column. Clauses (R) and (UB) only — (UB)
inherits the same content through the transported product-law chain at q ↦ p^δ. NOT
(0)/(SQ).

**What is already PROVED and is NOT re-proved here** (the pair's factor-coordinate side,
O-10 leaf #6, VERIFIED at scope): K-COUNT = O-10 Theorem 1 (constant fibers
p^{Σᵢ min(eᵢ, N−τ)} at every N ≥ τ, = p^ρ in the guard range); the adapted-cell (SIB)
product law = O-10 Theorem 2, UNCONDITIONAL in factor coordinates; K-JAC polydisc form =
O-10 Lemma 3; K-FACT = the pinned GMN citation set (Thms 1.15/1.19/3.1/3.7,
`docs/GMN_citations.md`). **(H7) is exactly the residue separating Theorem 2 from the
engine**: that the engine's realized strata ARE such adapted cells ((I-τ)) and that the
engine's branch continuation reads ARE the factors' OM reads up to cell-constant
normalization (K-LOC).

**Discharge =** (per ROOT §6's named unit) the K-LOC lemma (M07 OL-3) + the (I-τ)
presentation write-up, plus a Lean layer in two honestly separated tiers:
**Tier S (shadow/plumbing, W0–W2):** count-interface rows + receipt wiring into the
corpus carrier `EngineSIBRow` (whose `KLoc`/`ITau` parameters are OPAQUE Props at HEAD,
"BP_III-owned with NO landed (or even chartered) declaration anywhere in the corpus") —
Tier S proves interface FIT ONLY and must never be cited as evidence for (H7)
[review findings 13–16]. **Tier M (semantic, W3+):** the engine-tied rows
(`ITauSemantic`/`KLocSemantic`, §3.7) whose proofs ARE the discharge. Nothing in this
file discharges (H7) by fiat: every claim is graded PROVED / PROVABLE-NOW / OPEN with
owner.

**Fences honored:** `MovesT.SibJcRows`/`CellData` (`BK.sibjc`, fence event 27,
PLAUSIBLY-FALSE-AS-TYPED, PARKED item 27) are NOT touched and NOT consumed — the H7 rows
quantify over a fresh abstract `SiteDatum` record (§3), never over `CellAssign`. Parked
items 22–29 untouched. No existing statement modified.

---

## 1. Member 1: (K-LOC) — door: PROVE (core mechanism LITERATURE-RETARGET onto GMN Thm 2.26)

### 1.1 The target statement (OL-3, refined to discharge precision; REV 2 form)

Setup. Fix a realized site s of the canonical tree at level N with cell datum c (the
site's complete realized read data), continuing branch roster {ν₁, …, ν_m}, m ≥ 2, and
the K-FACT base factorization at one member: dec = f₀^{(c)}·∏_{j=1}^m f_j^{(c)}
(GMN Thms 1.15/1.19 at order 1, 3.1/3.7 at order r), with
ρ(c) := Σ_{0 ≤ i < j ≤ m} v_p(Res(f_i^{(c)}, f_j^{(c)})) — f₀ included as index 0 with
its OWN pinned factor cell C₀ (§2.1 IT-1; the `Set.univ` option removes only its EVENT,
never its cell — review finding 2). thr(c) := the cell's read threshold, ≥ 1 at every
realized site (the level-0 reduction read is always consumed). Assume the D-8 guard
N ≥ thr(c) + 2ρ(c). **Domain [REV 2 — review finding 8]: the POLYDISC, not Σ_c** — all
claims below are for any monic tuple (g₀, …, g_m) with g_i ≡ f_i^{(c)} mod p^{τ(c)}
(degrees fixed), F := ∏ g_i; Σ_c enters only through (I-τ)/IT-2.

**(KL-0) — the frame kernel [split out at REV 2 — review finding 1; OPEN].** The site's
realized key chain along branch j's type t_j (the engine's recorded lift/recentering
choices — HC-2 D.10 / `StageTransHyp` in Lean) is a valid OM frame for BOTH F and g_j,
and the branch-j reads of g_j in that chain differ from g_j's intrinsic OM reads by a
c-constant frame change. This is M07 OL-3's "statement must fix the recentering/lift
convention" clause AS AN OBLIGATION, not a convention choice: declaring both sides into
one chain does not discharge it. Owner: the D.10/`StageTransHyp` area; the
`HK25_recGate`/`HK52_stretchGate` compiled artifacts bound its order-≥ 2 behavior.

**(K-LOC) main claim** (given KL-0 at the site). There is a normalization datum
ε_j(c) — per level r of branch j's continuation, a polygon-side translation δ_{j,r}(c)
and a residual unit scalar u_{j,r}(c) ∈ 𝔽_{q_r}^× — a function of the cell datum c
ALONE, such that for every polydisc tuple (g_i), every j, and every continuation level
r of branch j with reads at depth ≤ thr(c) + ρ(c), writing λ_{j,r} for the branch's
realized slope at level r [REV 2 — the claims are per-slope and principal-polygon
(N_r^−) shaped, exactly Thm 2.26's scope — review finding 6]:

> (i) the λ_{j,r}-side of N_r^−(F) in the t_j-frame is the λ_{j,r}-side of N_r^−(g_j)
> translated by δ_{j,r}(c);
> (ii) R_{λ_{j,r}}(F) = u_{j,r}(c) · R_{λ_{j,r}}(g_j) in 𝔽_{q_r}[y].

**(K-LOC) event clause (iii′)** [REV 2 — pointwise factor-condition form, no
Corollary-1 extraction map invoked — review finding 3]: for every prescribed-finite-
subtree continuation event S_{ν_j} of branch j there is a set E_j of residue classes
mod p^{K_j}, K_j ≤ thr(c) + ρ(c), with: for every polydisc tuple, F's branch-j
continuation reads realize S_{ν_j} **iff** g_j mod p^{K_j} ∈ E_j. (iii′) follows from
(i)+(ii) TOGETHER WITH the read-decoding clause of KL-4 (reads are functions of the
per-level (N_r^−, R_λ) data to bounded depth) — it is NOT a consequence of (i)+(ii)
alone, and it consumes no (I-τ) content: the map to g_j is the polydisc coordinate
itself. (I-τ) then CONSUMES (iii′) to build its presentation; O-10 Corollary 1's
extraction ε enters only after (I-τ) stands — the dependency is now acyclic:
KL-0 → (i)/(ii) → KL-4 → (iii′) → IT-1/IT-2 → Corollary 1/Theorem 2.

### 1.2 Proof plan (kernels; each graded; REV 2 grades)

* **KL-1a (residual-separation ω-vanishing).** For i ≠ j separating from ν_j at
  distinct residual factors: ω_{t_j,r}(g_i) = 0 at branch j's levels beyond the
  separation — ψ_j ∤ R(ḡ_i) by GMN Thm 1.19's factor isolation + Lemma 2.17(2)
  (ω = ord_ψ R; pinned verbatim, `docs/GMN_citations.md` §6.1). Order r: induction
  along the shared prefix with Thms 3.1/3.7. STATUS: order ≤ 1 PROVABLE NOW at the
  divisibility face (Lean H7-C2 is that face's count shadow, NOT the whole of KL-1 —
  review finding 17); order ≥ 2 legs graded open, kin to (H1).
* **KL-1b (side-separation ω-vanishing) [REV 2 — replaces the WRONG Lemma-2.17(3)
  cite, review finding 4].** For i ≠ j separating at distinct polygon sides: the
  λ_{j,r}-side of N_r^−(g_i) has length 0, because the side-length/degree accounting
  of the stage factorization (Thms 1.15/3.1: each factor carries exactly its own
  sides' degrees) leaves g_i no λ_{j,r}-mass; Lemma 2.17(3) concerns ONLY the −∞ side
  and is NOT the citation. STATUS: expected-elementary from the pinned Prop 2.7/Lemma
  2.17 vocabulary, OPEN until written (a named sub-lemma, not a cite).
* **KL-1c (ω = 0 ⟹ one-point λ-side + constant residual) [REV 2 — promoted from
  implicit to named, review finding 5].** Definition-level unfolding of Def 1.8 /
  the R_λ operator: zero length of the λ-side of N_r^− forces R_λ(g_i) to be a
  nonzero constant. STATUS: definitional at order 1; OPEN as a written sub-lemma
  (definition conventions incl. the −∞ side must be fixed once).
* **KL-2 (per-level product transport).** Apply GMN **Thm 2.26** (verbatim pin §6.0:
  "N_r^−(fg) = N_r^−(f) + N_r^−(g), R_{λ_r}(fg) = R_{λ_r}(f)·R_{λ_r}(g)") over the
  tuple: cofactors with zero λ_{j,r}-mass (KL-1a/b/c) contribute a translation
  δ_{j,r} = Σ_{i≠j} v-data and a unit scalar u_{j,r} = ∏_{i≠j} R_{λ_{j,r}}(g_i) —
  yielding (i)/(ii) IN THE PER-SLOPE N_r^− SHAPE, which is all §1.1 now claims
  [REV 2: the former full-polygon "N_r" display exceeded the theorem — review
  finding 6]. The ℓ-shift normalization of R_λ is fixed ONCE at the KL-2 transcription
  (convention clause; any fixed choice works — the unit-scalar claim is
  normalization-covariant). STATUS: LITERATURE-RETARGET (brief §1.3) + assembly.
* **KL-3 (cell-constancy of ε_j(c)).** δ_{j,r} and u_{j,r} are functions of c alone.
  Mechanism: (a) freeze-at-separation (KL-1) — branch j's levels see g_i only through
  its λ_{j,r} v-data and constant residual; (b) congruence pinning — those are
  ℤ-polynomial/valuation expressions in g_i's coefficients, pinned mod p^{τ(c)} on
  the polydisc, with values CONJECTURED to sit at valuation < τ(c) via the
  interaction bound ≤ (separation depth) + ρ_{ij}(c), whence pinned exactly (the
  O-10 Lemma-3 congruence trick). [REV 2 — review finding 7: the interaction bound
  has NO supplied citation; the precision analysis is the kernel's actual content.]
  STATUS: OPEN at every order (order ≤ 1 expected-elementary, no longer graded
  PROVABLE-NOW); order ≥ 2 shares the `HK52_stretchGate` ν_{i+1}.e-stretch area.
* **KL-4 (read decoding + event pullback).** Branch reads are functions of the
  per-level (λ-side, R_λ) data to bounded depth; with (i)/(ii) and KL-0, F's reads =
  g_j's reads composed with the c-constant renormalization; a prescribed finite
  subtree fixes finitely many reads at depths ≤ K_j; E_j := the renormalized read
  class — giving (iii′). Well-definedness on classes mod p^{K_j}: O-10 Theorem 1(iii)
  + guard arithmetic (H7-B3). STATUS: assembly; provable at each order where
  KL-0..3 stand.

### 1.3 Faithfulness brief for the KL-2 literature core (translation risks, displayed)

Candidate published statement: **GMN (arXiv:0807.2620v2) Thm 2.26** as pinned verbatim
(§6.0 of `docs/GMN_citations.md`), with Lemma 2.17 + Prop 2.7 + Def 1.8 supplying the
ω/principal-polygon vocabulary (§6.1 pins). What must match in our language:
(a) our per-level claims are N_r^− (principal polygon) claims AT THE BRANCH'S REALIZED
SLOPE — §1.1(i)/(ii) are now stated in exactly that shape; nothing about full polygons
or slope-uniform data is consumed; (b) the engine's realized key chain must be a valid
GMN type for BOTH F and g_j — this is KL-0, an OPEN kernel, NOT covered by the
citation; (c) 2.26's R_λ normalization carries an ℓ-shift — fixed once at the KL-2
transcription, unit-scalar claim covariant; (d) scope: GMN works over a fixed finite
extension K/ℚ_p (§6.0 correction 2) — covers ℚ_p, and for clause (UB)'s transported
chain each unramified K = ℚ_{p^δ} SEPARATELY; δ-uniformity of the normalization data is
NOT claimed by the citation and rides (H4a)/(UB-X) exactly as ROOT displays. Risks
(a)–(d) are why this member is PROVE-with-citable-core, NOT a pure literature retarget:
no published statement asserts (iii′) at our tree/event vocabulary.

### 1.4 Honest open points for K-LOC (the complete list, REV 2)

1. **KL-0** — the frame kernel (§1.1): chain validity + the c-constant frame change to
   intrinsic factor reads. THE load-bearing recentering obligation; never assumable.
2. **f₀ bookkeeping** — f₀ rides with a genuine pinned cell C₀ (§2.1 IT-1) and enters
   ρ(c); the `Set.univ` option removes only its event. Consumers quantifying rosters
   without the f₀ INDEX mis-price ρ(c).
3. **KL-1b/KL-1c** — named sub-lemmas, open until written (order-1 expected-elementary).
4. **KL-3** — the precision/interaction analysis, open at every order; order ≥ 2 in the
   ν_{i+1}.e-stretch area (`HK52_stretchGate`).
5. **Order ≥ 2 legs of KL-1a** — displayed grading, kin to (H1) (disjoint seam; shared
   machinery).
6. **Reads that overshoot thr(c)** — events read at their OWN depths; the ceiling
   K_j ≤ thr(c) + ρ(c) is the (I-τ) pricing choice; deeper events are out of (H7)'s
   priced scope (display, don't absorb).

---

## 2. Member 2: (I-τ) — door: CONSTRUCTION-CONFORMANCE (Lean receipt) + PROVE (the presentation write-up)

### 2.1 The presentation write-up (IT-1 … IT-4; REV 2)

* **IT-1 (per-branch strata + the f₀ cell).** For j ≥ 1: C_j := {g ∈ A_j(N) :
  g ≡ f_j^{(c)} mod p^{τ(c)}, g's branch-frame reads match branch j's realized read
  data to its realized depth} — keyed at K_j = max(τ(c), branch-j read depth) ≤
  thr(c) + ρ(c); read well-definedness = K-LOC (iii′). **C₀ := {g ∈ A₀(N) :
  g ≡ f₀^{(c)} mod p^{τ(c)}}** — the pure pinned stratum, keyed at τ(c), NO read
  clause and NO event [REV 2 — review finding 2: the (m+1)-factor presentation needs
  an f₀ CELL, not merely a trivial event; with C₀ the O-10 carrier applies to the
  full (m+1)-tuple and ρ(c) correctly includes f₀'s cross-resultants].
* **IT-2 (product form Σ_c = μ_N(C₀ × ∏_j C_j)).** ⊆: x ∈ Σ_c ⟹ the K-FACT tuple of
  dec(x) lies in C₀ × ∏C_j — K-FACT + K-LOC (iii′) at the realized reads. ⊇ [REV 2 —
  review finding 8: the former sketch was circular]: what is needed is the
  **run-replay kernel**: if a polydisc tuple's factor reads match the site's realized
  read data (which K-LOC (iii′) makes a well-defined factor-side condition), then the
  ENGINE's run on the product F reaches this site with datum c — i.e. matching reads
  ⟹ membership. K-LOC is applied on the polydisc (its REV-2 domain), never to
  members of Σ_c being constructed; the residual obligation is run-determinism +
  reachability, the O-14a′ `RunRealizerExists` mechanism family. STATUS: ⊆ provable
  once K-LOC lands per order; ⊇ OPEN with named kernel (the sharpest (I-τ)-specific
  gap).
* **IT-3 (pricing arithmetic).** τ(c) := max(ρ(c) + 1, the site's branch-pin depth);
  upper bound τ(c) ≤ thr(c) + ρ(c) — REQUIRES thr(c) ≥ 1 [REV 2 — review finding 9:
  false at thr = 0; repaired by the SiteDatum field `one_le_thr`, semantically
  grounded: every realized site has consumed at least the level-0 reduction read].
  Guard headroom (A3): in the D-8 range every K ≤ thr + ρ clears K + e_max ≤ N
  (e_max ≤ ρ) — probe-PROVED, unit H7-B3. (SEP) τ ≥ ρ + 1: automatic at order-0
  separations (ρ = 0, τ = 1 ≤ thr + 0 given thr ≥ 1 ✓); at ρ > 0 the natural pin can
  undershoot ρ + 1 → route B.
* **IT-4 (route B: refine-and-aggregate — the (SEP)-deficiency repair; REV 2
  regraded).** Refine Σ_c by pinning factor digits to depth τ′ := ρ(c) + 1 (τ′ ≤
  thr + ρ needs thr ≥ 1 ✓): each sub-cell is a genuine adapted presentation
  (A1)–(A3); O-10 Theorem 2 gives the product law per sub-cell. The aggregation to
  the full Σ_c needs, beyond the two abstract kernels (H7-C1a uniform-mixing,
  H7-C1b uniform-words-⟹-(SIB), both statable now), a genuinely OPEN kernel:
  **IT-4b (read-fiber constancy + alphabet stability)** [REV 2 — review findings
  10/11: Theorem 2 + Corollary 1(c) do NOT deliver exact uniformity of the
  continuation-read WORD — the word map can merge unequal numbers of coefficient
  classes, and the attainable word set can vary across sub-cells]: on each sub-cell,
  every attainable branch-read word at depth ≤ K_j is realized by the same number of
  depth-K_j factor classes, and the attainable word alphabet is sub-cell-independent
  across the site's refinement. IT-4b is read-semantics content of exactly the
  GD-2/GD-5 family (where ROOT's §3.1 row already locates K-LOC's read-semantics
  content); owner: the GD dictionary campaign. STATUS: route B = two provable-now
  abstract kernels + IT-4b OPEN + re-consuming IT-1/IT-2 at the deeper pin. LABEL:
  (c) claimed-new derivation, now with its missing kernel displayed.
