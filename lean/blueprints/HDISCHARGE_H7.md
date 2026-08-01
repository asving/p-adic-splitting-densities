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

### 2.2 The construction-conformance target (which corpus carriers, what theorem)

Carriers REUSED (all in `lean/LeanUrat/Scaffold/ValueSide/KCount.lean`, rebuilt-probed):
`MulFiberData` (τ, ρ, τ_sep : ρ+1 ≤ τ, smithExp, chart), `SmithStable` (+ constructor
`smithStable_of_detDivisorRows`, gate `K9Gate.gate_smithStable`), `AdaptedCell`
(cellCount/factorCount/sM/domainCount_eq/fiber_nonempty), `sib_product_law`
(himg-scoped), `kcount_fiber_card` (hsol-scoped), and the (H7) receipt
`EngineSIBRow p n N (KLoc ITau : Prop) (stratumCount : ℕ)` — K11, authored with the
pair as OPAQUE Prop parameters.

**The receipt-plumbing lemma (H7-B1, probe-PROVED) [REV 2 — regraded per review
finding 15; formerly overtitled "THE CONFORMANCE THEOREM"]:** instantiating K11's
opaque parameters with the H7 Tier-S row shapes composes into
`EngineSIBRow p n N KLoc (ITauShadow s) s.stratumCount` with no re-key. This is an
INTERFACE-FIT check (constructor compatibility — the exact failure class that blocked
BP waves), NOT a discharge step and NOT evidence for (H7): `EngineSIBRow` itself treats
the pair as opaque, and B1 merely copies proofs into fields. The semantic content
enters only when Tier M's `ITauSemantic`/`KLocSemantic` (§3.7) instantiate the
parameters.

**FINDING H7-F1 (consumed-carrier defect — reported, NOT repaired here; review
CONFIRMED).** `AdaptedCell.domainCount_eq : Nat.card Factor = ∏ j, factorCount j` runs
its product over `j : Factor` — the domain type ITSELF — so under the intended roster
semantics (factorCount = per-branch stratum counts) the field is uninstantiable at any
genuine site (F1 shape: `Nat.card Factor` must be 5⁸ = the domain count, while the
per-branch product must be indexed by `Fin 2`; no single `Factor` serves both).
K10's conclusion `… = ∏ j, A.factorCount j` therefore carries per-branch (SIB) content
only under contrived `factorCount` choices. H7's rows route around it:
`SiteDatum.branchCount : Fin m → ℕ` carries the roster-indexed counts and `ITauShadow`
demands the domain law `Nat.card A.Factor = ∏ j, s.branchCount j` in roster indexing,
leaving `factorCount` unconsumed; the delivered product-law SHAPE (H7-B2,
probe-PROVED) is `stratumCount · p^{sM} = ∏_j branchCount j`. DESIGNER-QUEUE flag to
BP_IV (adjudication, not executed): re-index `factorCount : J → ℕ` over a roster-type
field, or document `Factor` as the domain and retire `factorCount` from the (SIB)
display.

### 2.3 Door summary for the pair (REV 2 grades)

| member | door | provable-now slice | open remainder (named) |
|---|---|---|---|
| (K-LOC) | PROVE; KL-2 core = LITERATURE-RETARGET (GMN 2.26, §1.3 brief) | KL-1a order ≤ 1 divisibility face (H7-C2 its count shadow); KL-2 assembly given KL-1a/b/c; KL-4 given KL-0..3 | KL-0 (frame kernel); KL-1b/KL-1c sub-lemmas; KL-3 (all orders — precision analysis); order ≥ 2 legs; §1.4 list |
| (I-τ) | CONSTRUCTION-CONFORMANCE (Tier-S receipt plumbing) + PROVE (write-up) | H7-B1/B2/B3 (probe-proved, interface-fit only); IT-3 arithmetic (order-0, thr ≥ 1); H7-C1a/C1b aggregation kernels | IT-2 ⊇ run-replay kernel; IT-1/IT-2 ⊆ per order = K-LOC's grading; IT-4b read-fiber constancy + alphabet stability (GD-2/GD-5 family); Tier-M semantic rows (§3.7) |

Neither member is literature-axiom-eligible as a whole (M07 §3.4 stands); only KL-2's
core is citable. Tier S alone discharges NOTHING (review findings 13–16, accepted).

---

## 3. LEAN UNIT SPECS (verbatim; probe round 2 green, 2026-08-05)

Target directory: `lean/LeanUrat/Scaffold/HDischarge/H7/`; namespace
`LeanUrat.Scaffold.HDischarge.H7`; import `LeanUrat.Scaffold.ValueSide.KCount`.
**[probe-PROVED]** = compiled WITH the displayed proof; **[probe-typed]** = statement
compiled, `sorry` body in the (deleted) probe only. Landing discipline: prover units
land sorry-free or not at all. **TIER LABELS (REV 2): every W0–W2 unit is Tier S
(interface shadow) — see §0; the docstrings below carry the warning verbatim.**

### 3.1 `H7/Rows.lean` — the Tier-S row shapes (unit H7-A; MECH)

```lean
namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

/-- H7-A1 [Tier S]: the abstract realized-site datum. Engine-side instantiation
(from `MovesT.SiteLedger` at the pinned canonical models) is Tier-M unit H7-W3a.
`one_le_thr`: every realized site has consumed at least the level-0 reduction read
(REV 2, review finding 9 — the IT-3 ceiling needs it). `branchCount` is
ROSTER-indexed, deliberately NOT `AdaptedCell.factorCount` (FINDING H7-F1). -/
structure SiteDatum (p n N : ℕ) [Fact p.Prime] where
  m : ℕ
  two_le_m : 2 ≤ m
  thr : ℕ
  one_le_thr : 1 ≤ thr
  rho : ℕ
  stratumCount : ℕ
  branchCount : Fin m → ℕ

/-- The D-8 guard at the site. -/
def InGuard {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  s.thr + 2 * s.rho ≤ N

/-- H7-A2 [Tier S — renamed from `ITauPresents` at REV 2, review finding 13]: the
COUNT-INTERFACE SHADOW of the (I-τ) row: some adapted-cell carrier with Smith
stability realizes the site's integers (ρ, a pin within the pricing, the K10b image
law, cell count = stratum count, roster-indexed domain law), with `sM` pinned to the
carrier's own Smith data (the s(M) formula — the one internal tie expressible now).
WARNING: satisfiable by synthetic carriers; NOT the semantic (I-τ), which is
`ITauSemantic` (Tier M, §3.7). Never cite this row as evidence for (H7). -/
def ITauShadow {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  ∃ A : AdaptedCell p n N,
    SmithStable A.toMulFiberData ∧
    A.toMulFiberData.ρ = s.rho ∧
    A.toMulFiberData.τ ≤ s.thr + s.rho ∧
    A.sM = ∑ i, min (A.toMulFiberData.smithExp A.toMulFiberData.base i)
      (N - A.toMulFiberData.τ) ∧
    A.cellCount * p ^ A.sM = Nat.card A.Factor ∧
    A.cellCount = s.stratumCount ∧
    Nat.card A.Factor = ∏ j, s.branchCount j

/-- H7-A3 [Tier S]: the K-LOC COUNT SHAPE over an abstract event carrier. WARNING
(REV 2, review finding 14): vacuous at `Events := Empty` and freely engineerable at
arbitrary count functions — contentful ONLY at the Tier-M instantiation (H7-W3a:
`Events` := the ContFiber families, counts := their box cardinalities). It pins the
receipt VOCABULARY for wave-0; it must never be cited as evidence of K-LOC. -/
def KLocCounts {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (Events : Type) (joint : Events → ℕ) (single : Events → Fin s.m → ℕ) : Prop :=
  ∀ E : Events, joint E * s.stratumCount ^ (s.m - 1) = ∏ j, single E j
```

### 3.2 `H7/Receipt.lean` — Tier-S plumbing (units H7-B; all [probe-PROVED], round 2)

```lean
/-- H7-B1 [Tier S; probe-PROVED]: receipt PLUMBING — the H7 row shapes compose into
K11's `EngineSIBRow` with no re-key. Interface-fit only (REV 2, review finding 15):
`EngineSIBRow` treats the pair as opaque Props; this lemma copies proofs into fields
and establishes NOTHING semantic. -/
theorem engineSIBRow_of_rows {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (KLoc : Prop) (hK : KLoc) (hI : ITauShadow s) :
    EngineSIBRow p n N KLoc (ITauShadow s) s.stratumCount := by
  obtain ⟨A, hS, -, -, -, himg, hcnt, -⟩ := id hI
  exact ⟨hK, hI, ⟨A, hS, himg, hcnt⟩⟩

/-- H7-B2 [Tier S; probe-PROVED]: the Step-15 delivery SHAPE — the stratum product
law in roster indexing, extracted from the shadow row (H7-F1 workaround). -/
theorem stratum_product_law {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hI : ITauShadow s) :
    ∃ sM : ℕ, s.stratumCount * p ^ sM = ∏ j, s.branchCount j := by
  obtain ⟨A, -, -, -, -, himg, hcnt, hdom⟩ := hI
  exact ⟨A.sM, by rw [← hcnt, himg, hdom]⟩

/-- H7-B3 [Tier S; probe-PROVED]: IT-3 pricing arithmetic — in the D-8 guard range,
any pin `τ ≤ thr + ρ` and read depth `K ≤ thr + ρ` clear the `e_max ≤ ρ` ceiling
(the (A3) headroom of O-10 §4.3(a)). -/
theorem guard_read_headroom {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hg : InGuard s) {τ K emax : ℕ}
    (hτ : τ ≤ s.thr + s.rho) (hK : K ≤ s.thr + s.rho) (he : emax ≤ s.rho) :
    τ + emax ≤ N ∧ K + emax ≤ N := by
  unfold InGuard at hg
  omega
```

### 3.3 `H7/Aggregate.lean` — the IT-4 abstract kernels (H7-C1a/C1b; [probe-typed])

```lean
open Finset in
/-- H7-C1a [MED; Tier S-abstract but genuinely mathematical]: words uniform on each
part of a partition (per-part multiplicity may vary) are uniform on the union — the
aggregation half of IT-4. Review-CONFIRMED valid as stated. Proof plan: U := Σ u_C;
count each ω-fiber by `Finset.card_biUnion` over the ∃!-disjoint parts. -/
theorem uniform_on_union {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W]
    [DecidableEq W] (P : Finset (Finset X)) (w : X → W)
    (hcover : ∀ x : X, ∃! C, C ∈ P ∧ x ∈ C)
    (hunif : ∀ C ∈ P, ∃ u : ℕ, ∀ ω : W, (C.filter (fun x => w x = ω)).card = u) :
    ∃ U : ℕ, ∀ ω : W, (univ.filter (fun x : X => w x = ω)).card = U := by
  sorry -- prover wave; statement probe-typed

open Finset in
/-- H7-C1b [MED-HARD]: exactly-uniform joint words on a product alphabet satisfy the
(SIB) count identity for componentwise events — the positive twin of
`MovesU.SibRouteA.sib_diag_break`. `hm : 1 ≤ m` REQUIRED (REV 2, review finding 12:
the m = 0 instance is FALSE — empty product 1 vs #X). Proof plan: both sides equal
U^m · (∏_j #E_j) · (∏_j #A_j)^{m−1}. -/
theorem sib_of_uniform_words {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} (hm : 1 ≤ m) {A : Fin m → Type*} [∀ j, Fintype (A j)]
    [∀ j, DecidableEq (A j)]
    (w : X → ∀ j, A j) {U : ℕ}
    (hU : ∀ ω : ∀ j, A j, (univ.filter (fun x => w x = ω)).card = U)
    (E : ∀ j, Finset (A j)) :
    (univ.filter (fun x : X => ∀ j, w x j ∈ E j)).card
        * (Fintype.card X) ^ (m - 1)
      = ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card := by
  sorry -- prover wave; statement probe-typed
```

### 3.4 `H7/ResTrans.lean` — the KL-1a order-1 count face (H7-C2; [probe-typed])

```lean
/-- H7-C2 [EASY-MED]: ω-blindness of coprime cofactors — multiplying by a ψ-coprime
cofactor changes no ψ-power divisibility read (ψ irreducible over a field). SCOPE
(REV 2, review finding 17): this is KL-1a's COUNT FACE at order 1 ONLY — it proves
none of KL-1b/1c, KL-2 transport, KL-3 constancy, KL-4 pullback, or KL-0. Proof:
ψ irreducible ⟹ prime; induct with `Prime.pow_dvd_of_dvd_mul_right`. -/
theorem pow_dvd_mul_iff_of_coprime_cofactor {F : Type*} [Field F]
    {ψ g : Polynomial F} (hψ : Irreducible ψ) (hg : ¬ ψ ∣ g)
    (f : Polynomial F) (k : ℕ) :
    ψ ^ k ∣ f * g ↔ ψ ^ k ∣ f := by
  sorry -- prover wave; statement probe-typed
```

### 3.5 `H7/Order0Gate.lean` — the interface-fit gate (H7-D1; REV 2 rescoped)

```lean
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- H7-D1a [MECH; probe-typed]: the F1-shaped order-0 site datum — p = 5, n = 4,
N = 8; two continuing branches (the sealed CASE_SIB roster), residue-split ρ = 0;
stratum 5⁸ (the 14-pin Σ*), branches 5⁴ each; thr = 3 ≥ 1.
Integers from `verification/CASE_SIB_SEALED_PREDICTIONS.md`. -/
noncomputable def f1Datum : SiteDatum 5 4 8 where
  m := 2
  two_le_m := by norm_num
  thr := 3
  one_le_thr := by norm_num
  rho := 0
  stratumCount := 5 ^ 8
  branchCount := ![5 ^ 4, 5 ^ 4]

/-- H7-D1b [MED; Tier S]: `ITauShadow f1Datum` is inhabited — the INTERFACE-FIT gate
(REV 2, review finding 16: a synthetic-carrier inhabitant certifies ONLY that the row
shape is satisfiable at real integers and that the F1 arithmetic composes — it is NOT
a non-vacuity certificate for the semantic (I-τ); THAT gate is H7-W3a's
`gate_order0_semantic`). Builder notes: `Factor := Fin 2 → Fin 625` (`Nat.card_pi`),
`sM = 0` with zero Smith exponents, designated-element `factorCount` for the carrier's
own `domainCount_eq` (H7-F1 workaround). -/
theorem gate_f1_iTauShadow : ITauShadow f1Datum := by
  sorry -- prover wave; statement probe-typed

/-- H7-D1c [probe-PROVED]: the gate site is in the D-8 guard (3 + 0 ≤ 8). -/
theorem gate_f1_guard : InGuard f1Datum := by
  unfold InGuard f1Datum
  norm_num
```

### 3.6 `H7/AxChk.lean` — census (H7-E1; MECH)

`#print axioms` for every landed H7 declaration — expected Lean core only; zero
`sorryAx` at wave close; regression = stop-the-line.

### 3.7 Tier M — the SEMANTIC units (specified, NOT scheduled; the actual discharge)

* **H7-W3a (`ITauSemantic`/`KLocSemantic` + engine instantiation)** [HARD; owner:
  MovesT/BP_III side]: the engine-tied rows — `ITauSemantic`: the site's box-level
  stratum (`Nat.card (siteCellEvent …)` at the pinned canonical models) IS presented
  by an adapted cell whose `MulFiberData` is the ACTUAL level-N multiplication chart
  on the K-FACT factor strata (C₀ × ∏C_j of §2.1), with `branchCount j` = #C_j-classes;
  `KLocSemantic`: `KLocCounts` instantiated at `Events` := the site's ContFiber
  families with box-cardinality counts. Includes `gate_order0_semantic`: the REAL
  non-vacuity gate at a `decide`-small order-0 site (p = 2, n = 2, N = 2 box
  enumeration). BLOCKED on: OL-2 (ledger inhabitation at the pinned instance) and the
  item-27 statement-repair adjudication (PARKED; not executed by H7).
* **H7-W3b (KL-0 + KL-2/KL-3 general residual transport)** [HARD; owner: the
  (GR-B)/HC2 apparatus]: the frame kernel (KL-0) in the `StageTransHyp`/D.10
  vocabulary; the per-level translation + unit-scalar laws; order ≥ 2 gated by the
  `HK52_stretchGate` ν_{i+1}.e ruling.
* **H7-W3c (IT-2 ⊇ run-replay kernel)** [HARD; owner: O-14a′ mechanism]: matching
  factor reads ⟹ site membership (run-determinism + reachability).
* **H7-W3d (IT-4b read-fiber constancy + alphabet stability)** [HARD; owner: the
  GD-2/GD-5 read-semantics family]: route B's missing kernel (§2.1).

---

## 4. WAVE PLAN (prover fan-out; per-file `lake env lean` gates)

| wave | units | files | deps | difficulty | parallel? |
|---|---|---|---|---|---|
| W0 | H7-A1/A2/A3 (+ `InGuard`) | `Rows.lean` | KCount olean (REBUILT — a stale olean hides `EngineSIBRow`) | MECH | single owner |
| W1a | H7-B1/B2/B3 | `Receipt.lean` | W0 | EASY (proofs displayed) | ∥ W1b/c/d |
| W1b | H7-C1a, H7-C1b | `Aggregate.lean` | Mathlib only | MED / MED-HARD | ∥ |
| W1c | H7-C2 | `ResTrans.lean` | Mathlib only | EASY-MED | ∥ |
| W1d | H7-D1a/b/c | `Order0Gate.lean` | W0 | MECH / MED / MECH | ∥ |
| W2 | H7-E1 | `AxChk.lean` | W1a–d | MECH | after all |
| W3+ | H7-W3a/b/c/d | Tier M (§3.7) | §3.7 blockers | HARD | not scheduled here |

Wave-close criteria: zero `sorry` in landed files; AxChk Lean-core; W1d gate inhabited
(or its failure filed as an interface finding). Tier-M units get their own blueprints
before any prover spend.

## 5. NUMERICS / FALSIFIER GATES (flags, never substitutes)

* **Standing:** `verification/o10_kcount_harness.py` 68/0 (factor side);
  `MovesU/SibJcRouteA.lean` (compiled NEGATIVE gate: unadapted correlation cells break
  (SIB) by exactly p — what (A1) excludes).
* **N-H7-1 (NEW; numerics-fleet charge):** `verification/openmath/h7_kloc_probe.py` —
  pure-Python exact integers; Hensel factor extraction (M07 Lemma A's constructive
  surjectivity) at (i) the F1 instance (p = 5, R₀ = (z−1)²(z−2)², the 5⁸ Σ*) and
  (ii) a wild ρ > 0 pair ((x²+2)(x²+2x+2) at p = 2, from the O-10 battery). Sealed
  tests: (a) K-JAC within-cell constancy; (b) THE K-LOC READ-CONFORMANCE TEST —
  depth-1/2 branch continuation digits on dec(x) equal the matching digits of the
  extracted factor after ONE cell-constant shift (§1.1 (i)/(ii) instances); a
  violation REFUTES §1.1 as drafted (stop-the-line before prover spend);
  (c) IT-4b probe [REV 2]: enumerate a refined sub-cell pair and test read-fiber
  constancy + alphabet stability DIRECTLY (route B's open kernel gets a falsifier
  before a proof); (d) route-B mini: verify the H7-C1a/b aggregation arithmetic on
  the enumerated data. cypari2 cross-check optional, env-conditional.

## 6. REUSE MAP + FENCES

REUSED (by import, never edited): `Scaffold.ValueSide.KCount` — `MulFiberData`,
`SmithStable` (+ constructor + gate), `AdaptedCell`, `sib_product_law`,
`kcount_fiber_card`, `card_domainProduct_finset`, `EngineSIBRow` ·
`MovesU/SibJcRouteA.lean` (fence-side evidence; `JointlyUniform` is the H7-C1
vocabulary precedent) · GMN pins: `docs/GMN_citations.md` §§5–6 (K-FACT set; Thm 2.26;
Lemma 2.17; Prop 2.7; Def 1.8) · O-10 leaf theorems (math source of record) ·
HC2 `StageTransHyp`/D.10 + `HK25_recGate`/`HK52_stretchGate` (KL-0's carrier + its
order-≥ 2 bounds, W3b) · `MovesT.SiteLedger`/`ContFiber` (W3a targets — read-only).

NOT TOUCHED (fences): `MovesT.SibJcRows`/`CellData` + every parked item 22–29 (esp.
item 27); `montes_uniform_n2` / `montes_unconditional` / all capstones; no new axioms;
no statement weakened. FINDING H7-F1 reported to BP_IV's designer queue, not executed.

## 7. CODEX REVIEW FOLD (disposition of all 17 findings; archive `lean/notes/openmath/H7_bp_review.md`)

Verdict on draft 1: **REVISE** (15 criticals C, 2 justification gaps G). Every finding
adjudicated; no rebuttal overrode a critical.

| # | class | finding (compressed) | disposition at REV 2 |
|---|---|---|---|
| 1 | C | frame convention assumed away OL-3's recentering comparison | ACCEPT — KL-0 split out as named OPEN kernel; §1.1 restated |
| 2 | C | f₀ had no factor cell/pin (`Set.univ` ≠ a coordinate) | ACCEPT — C₀ pinned cell added (IT-1); (m+1)-tuple presentation displayed |
| 3 | C | (iii) circular: Corollary-1 extraction presupposes (I-τ) | ACCEPT — (iii′) restated pointwise on the polydisc coordinate; dependency chain now acyclic (§1.1) |
| 4 | C | Lemma 2.17(3) misapplied (−∞ side only) | ACCEPT — cite RETRACTED; KL-1b named sub-lemma (Thm 1.15/3.1 side accounting), OPEN |
| 5 | G | ω = 0 ⟹ one-point side/constant residual under-argued | ACCEPT — KL-1c named sub-lemma, definition-level, OPEN |
| 6 | C | KL-2 target exceeded Thm 2.26 (full N_r vs N_r^−/fixed λ) | ACCEPT — (i)/(ii) re-shaped to per-slope N_r^− form; ℓ-shift convention clause |
| 7 | G | KL-3 depth bound uncited; PROVABLE-NOW overstated | ACCEPT — KL-3 downgraded OPEN at all orders; bound labeled conjectured |
| 8 | C | IT-2 ⊇ sketch applied K-LOC circularly | ACCEPT — K-LOC re-domained to the polydisc; ⊇ = run-replay kernel (W3c), open |
| 9 | C | IT-3 ceiling false at thr = 0 | ACCEPT — `one_le_thr` field (semantically grounded); re-probed green |
| 10 | C | Thm 2 + Cor 1(c) do NOT give word uniformity (route B) | ACCEPT — IT-4b (read-fiber constancy) named OPEN kernel; route B regraded |
| 11 | C | common-alphabet claim unsupported | ACCEPT — folded into IT-4b (alphabet stability clause) |
| 12 | C | `sib_of_uniform_words` false at m = 0 | ACCEPT — `hm : 1 ≤ m` added; re-probed green |
| 13 | C | `ITauPresents` a numerical shell | ACCEPT — renamed `ITauShadow`, Tier-S label + warning docstring; `sM` tied to the carrier's Smith data; semantic row = `ITauSemantic` (W3a) |
| 14 | C | `KLocCounts` vacuous/engineerable | ACCEPT — Tier-S warning docstring (vacuity displayed); contentful only at W3a instantiation |
| 15 | C | H7-B1 not a substantive conformance theorem | ACCEPT — regraded "receipt-plumbing lemma", interface-fit only |
| 16 | C | order-0 gate = junk inhabitance | ACCEPT — rescoped INTERFACE-FIT gate; real gate = `gate_order0_semantic` (W3a) |
| 17 | C | H7-C2 cannot carry the order-≤1 KL-1 grade | ACCEPT — KL-1 split a/b/c; C2 scoped to KL-1a's count face; grades adjusted |

Review-CONFIRMED positives (carried): H7-F1 correct; order-0 integers consistent
(5⁸·5⁰ = 5⁴·5⁴, ρ = 0 ⟹ s(M) = 0); H7-C1a valid as stated; for m ≥ 2 exact joint
uniformity DOES imply the componentwise (SIB) identity (finding 12's own concession).

## 8. DISPOSITION LOG

* 2026-08-05: draft 1 written; §3 statements compile-probed green (probe round 1);
  KCount olean rebuilt (stale-olean finding). Codex adversarial review: REVISE,
  15 C + 2 G. REV 2 executed same session: all 17 findings folded (§7); repaired
  statements re-probed green (probe round 2: `one_le_thr`, `sM` tie, `hm`,
  `ITauShadow` rename). Probe files deleted; nothing landed under `Scaffold/`.
  STATUS: blueprint READY for prover fan-out at Tier S (W0–W2) + numerics gate
  N-H7-1; Tier M (W3a–d) specified with owners and blockers — the semantic discharge
  work. A second Codex pass on the REV-2 text is the recommended next verification
  step before the Tier-S wave launches (this fold is same-lead work; the bar for
  DISCHARGE claims stays two clean fresh passes).
