# HDISCHARGE_H7 — the (I-τ)/K-LOC sibling-interface pair: fine-grained discharge blueprint

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
run separately. All §4 unit statements were COMPILE-PROBED against the built corpus
(2026-08-05 session; KCount olean refreshed to source REVISION 3 first — it was stale and
hid `EngineSIBRow`/`sib_product_law`/`kcount_fiber_card`; probe file deleted after green).

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

**What is already PROVED and is NOT re-proved here** (the pair's entire factor-coordinate
side, O-10 leaf #6, VERIFIED at scope): K-COUNT = O-10 Theorem 1 (constant fibers
p^{Σᵢ min(eᵢ, N−τ)} at every N ≥ τ, = p^ρ in the guard range); the adapted-cell (SIB)
product law = O-10 Theorem 2, UNCONDITIONAL in factor coordinates; K-JAC polydisc form =
O-10 Lemma 3; K-FACT = the pinned GMN citation set (Thms 1.15/1.19/3.1/3.7,
`docs/GMN_citations.md`). **(H7) is exactly the residue separating Theorem 2 from the
engine**: that the engine's realized strata ARE such adapted cells ((I-τ)) and that the
engine's branch continuation reads ARE the factors' OM reads up to cell-constant
normalization (K-LOC).

**Discharge =** (per ROOT §6's named unit) the K-LOC lemma (M07 OL-3) + the (I-τ)
presentation write-up, plus the Lean conformance layer instantiating the corpus receipt
`EngineSIBRow` (KCount.lean K11, whose `KLoc`/`ITau` parameters are OPAQUE Props at HEAD
— "BP_III-owned with NO landed (or even chartered) declaration anywhere in the corpus").
Nothing in this file discharges (H7) by fiat: every claim below is graded PROVED /
PROVABLE-NOW / OPEN with owner.

**Fences honored:** `MovesT.SibJcRows`/`CellData` (`BK.sibjc`, fence event 27,
PLAUSIBLY-FALSE-AS-TYPED, PARKED item 27) are NOT touched and NOT consumed — the H7 rows
quantify over a fresh abstract `SiteDatum` record (§4), never over `CellAssign`. Parked
items 22–29 untouched. No existing statement modified.

---

## 1. Member 1: (K-LOC) — door: PROVE (core mechanism LITERATURE-RETARGET onto GMN Thm 2.26)

### 1.1 The target statement (OL-3, refined to discharge precision)

> **(K-LOC).** Let s be a realized site of the canonical tree at level N with cell datum
> c (the site's complete realized read data), continuing branch roster {ν₁, …, ν_m},
> m ≥ 2, and let dec(x) = f₀(x)·∏_{j=1}^m f_j(x) be the K-FACT factorization on Σ_c
> (GMN Thms 1.15/1.19 at order 1, 3.1/3.7 at order r — the recorded perimeter), with
> ρ(c) := Σ_{0 ≤ i < j ≤ m} v_p(Res(f_i, f_j)) — **f₀ INCLUDED in the pair sum** — and
> thr(c) the cell's read threshold. Assume the D-8 guard N ≥ thr(c) + 2ρ(c).
> **Frame convention (the recentering/lift pin, fixed here):** branch-j continuation
> reads are the OM data of dec(x) computed in the SITE'S REALIZED KEY CHAIN along
> branch j's type t_j — the engine's own recorded lift/recentering choices (the HC-2
> D.10 / `StageTransHyp` bookkeeping in Lean); factor-side reads of f_j use the SAME
> chain. **Claim:** there is a normalization datum ε_j(c) — per-level polygon
> translations δ_{j,r}(c) and residual unit scalars u_{j,r}(c) ∈ 𝔽_{q_r}^× — a function
> of the cell datum c ALONE, such that for every x ∈ Σ_c, every j, and every
> continuation level r of branch j with reads at depth ≤ thr(c) + ρ(c):
> (i) N_r^{t_j}(dec(x)) = N_r^{t_j}(f_j(x)) translated by δ_{j,r}(c);
> (ii) R_r^{t_j}(dec(x)) = u_{j,r}(c) · R_r^{t_j}(f_j(x)) in 𝔽_{q_r}[y];
> (iii) consequently every prescribed-finite-subtree continuation event S_{ν_j} on Σ_c
> is the pullback, under the O-10 Corollary-1 factor extraction ε, of an event
> E_j ⊆ A_j(N) keyed at depth K_j ≤ thr(c) + ρ(c).

Clause (iii) is exactly the event-translation clause of the O-10 §4.3 (I-τ) display;
(i)/(ii) are its mechanism made statement-level. The depth ceiling thr(c) + ρ(c) is the
(I-τ) pricing clause; the guard supplies K_j ≤ N − e_max (probe-proved arithmetic,
unit H7-B3).

### 1.2 Proof plan (four kernels; each graded)

* **KL-1 (cofactor ω-vanishing).** For every i ≠ j (including i = 0) and every
  continuation level r of branch j beyond the separation of ν_i from ν_j:
  ω_{t_j, r}(f_i) = 0. *Mechanism at order ≤ 1:* if the siblings separate at distinct
  residual factors, ψ_j ∤ R(f̄_i) — GMN Thm 1.19's factor isolation plus Lemma 2.17(2)
  (ω = ord_ψ R; pinned verbatim in `docs/GMN_citations.md` §6.1); if at distinct polygon
  sides, the side of branch j's slope in N(f_i) has length 0 — Lemma 2.17(3) + Thm 1.15.
  *Order r:* induction along the shared type prefix, Thms 3.1/3.7 isolating the factors;
  after divergence the cofactor's residual multiplicity at branch j's ψ_r is 0.
  STATUS: order ≤ 1 PROVABLE NOW (the count-face slice is Lean unit H7-C2, probe-typed);
  order ≥ 2 inherits the project's proved-≤1/open-≥2 grading — displayed, kin to (H1),
  NOT silently absorbed.
* **KL-2 (per-level product transport).** Apply GMN **Thm 2.26** (Theorem of the product
  in order r; verbatim pin at `docs/GMN_citations.md` §6.0: "N_r^−(fg) = N_r^−(f) +
  N_r^−(g), R_{λ_r}(fg)(y) = R_{λ_r}(f)(y)·R_{λ_r}(g)(y)") over the factorization: a
  cofactor with ω_{t_j,r}(f_i) = 0 has one-point principal polygon at level r — its
  polygon summand is a pure translation by v_r(f_i) and its residual factor is the
  nonzero CONSTANT R_{λ_r}(f_i); multiplying over i ≠ j gives (i)/(ii) with
  δ_{j,r}(c) = Σ_{i≠j} v_r(f_i) and u_{j,r}(c) = ∏_{i≠j} R_{λ_r}(f_i).
  STATUS: LITERATURE-RETARGET (faithfulness brief §1.3) + elementary assembly.
* **KL-3 (cell-constancy of ε_j(c)).** δ_{j,r} and u_{j,r} are functions of c alone.
  *Mechanism:* (a) freeze-at-separation — by KL-1, from the separation level on, branch
  j's data see f_i only through v_r(f_i) and the constant R_{λ_r}(f_i), both determined
  by f_i's data at depths ≤ (separation depth) + ρ_{ij}(c) (the resultant interaction
  bound); (b) below-τ determination — those data are ℤ-polynomial/valuation expressions
  in f_i's coefficients, pinned mod p^{τ(c)} on the polydisc with values of valuation
  < τ(c), hence pinned EXACTLY (the O-10 Lemma-3 congruence trick, verbatim mechanism).
  STATUS: order ≤ 1 PROVABLE NOW; general order OPEN — the same valuation-stretch
  bookkeeping area as the compiled obstruction `HC2/HK52_stretchGate.lean` (ν_{i+1}.e
  stretch); named open point, owner = the deep-wild tower campaign.
* **KL-4 (event pullback and depth accounting).** From (i)/(ii): every continuation
  verdict/digit read of ν_j on dec(x) equals the matching read on f_j(x) composed with
  the c-constant renormalization; a prescribed finite subtree fixes finitely many reads
  at depths ≤ K_j; set E_j := the renormalized read class. Well-definedness on classes
  mod p^{K_j} is O-10 Theorem 1(iii) fiber blindness + the guard (H7-B3). STATUS:
  assembly; provable at each order where KL-1..3 stand.

### 1.3 Faithfulness brief for the KL-2 literature core (translation risks, displayed)

Candidate published statement: **GMN (arXiv:0807.2620v2) Thm 2.26** as pinned verbatim
(§6.0 of `docs/GMN_citations.md`), with Lemma 2.17 + Def 1.8 supplying the
ω/principal-polygon vocabulary (§6.1 pins). What must match in our language:
(a) our branch reads are N_r^−/R_{λ_r} data **in the same convention** (principal
polygon INCLUDING the slope-−∞ side, Def 1.8; ω_{i+1} = ord_{ψ_i}R_i, gmn.txt:1093);
(b) the engine's realized key chain must be a valid GMN type for BOTH dec(x) and f_j —
the D.10/`StageTransHyp` recentering area; if the engine recenters mid-branch, ε_j(c)
must absorb the recentering (claimed absorbable — the recentering is itself c-data —
but UNPROVEN: named open point KL-3(c)); (c) 2.26's R_λ normalization carries an
ℓ-shift — the unit-scalar claim survives any FIXED normalization, but the Lean
transcription must pick one and stick to it; (d) scope: GMN works over a fixed finite
extension K/ℚ_p (§6.0 correction 2) — covers our ℚ_p case and, for clause (UB)'s
transported chain, each unramified K = ℚ_{p^δ} SEPARATELY; the δ-uniformity of the
normalization data is NOT claimed by the citation and rides (H4a)/(UB-X) exactly as ROOT
displays. Risks (a)–(d) are why this member is PROVE-with-citable-core, NOT a pure
literature retarget: no published statement asserts (iii) at our tree/event vocabulary.

### 1.4 Honest open points for K-LOC (the complete list)

1. **f₀ bookkeeping** — the off-roster factor rides as the (m+1)-st no-prescription
   factor (O-10 Theorem 2's `Set.univ` option); ρ(c) must include its cross-resultants
   (§1.1 does). Any consumer that quantifies rosters WITHOUT f₀ mis-prices ρ(c).
2. **Order ≥ 2 legs of KL-1/KL-3** — displayed grading; kin to (H1)'s proved-≤1/open-≥2
   shape. The pair (H7) does NOT collapse into (H1): its seam (K1 product law) is
   disjoint; but its deep-wild legs share the (H1) campaign's machinery.
3. **The recentering absorption** (§1.3(b)) — KL-3(c).
4. **Reads that overshoot thr(c)** — continuation events read at their OWN depths; the
   ceiling K_j ≤ thr(c) + ρ(c) is a pricing CHOICE matching the (I-τ) display; events
   deeper than the ceiling are out of scope of (H7) as priced (they would need a larger
   guard — display, don't absorb).

---

## 2. Member 2: (I-τ) — door: CONSTRUCTION-CONFORMANCE (Lean receipt) + PROVE (the presentation write-up)

### 2.1 The presentation write-up (IT-1 … IT-4)

* **IT-1 (per-branch strata).** C_j := {g ∈ A_j(N) : g ≡ f_j^{(c)} mod p^{τ(c)}, and
  g's OM reads along t_j match branch j's realized read data to its realized depth} —
  keyed at K_j = max(τ(c), branch-j read depth) ≤ thr(c) + ρ(c). Well-defined
  factor-side reads = K-LOC(iii). STATUS: definition + K-LOC dependency.
* **IT-2 (product form Σ_c = μ_N(∏_j C_j)).** ⊆: x ∈ Σ_c ⟹ (f_j(x))_j ∈ ∏C_j — K-FACT
  + K-LOC. ⊇ (the realizer direction): for (g_j) ∈ ∏C_j, the product (with the f₀ slot)
  runs the SAME site history with datum c — K-LOC applied at the product (its K-FACT
  tuple IS (g_j) by Proposition-1 rigidity) + run-determinism; the completeness face is
  kin to O-14a′'s `RunRealizerExists` mechanism (cited as ingredient, NOT re-proved).
  STATUS: ⊆ provable once K-LOC lands; ⊇ OPEN with named ingredient (the sharpest
  (I-τ)-specific gap — everything else reduces to K-LOC + arithmetic).
* **IT-3 (pricing arithmetic).** τ(c) := max(ρ(c) + 1, the site's branch-pin depth);
  upper bound τ(c) ≤ thr(c) + ρ(c) from the site's reads pinning each factor to at most
  its realized depth ≤ thr(c) plus the Hensel ρ-loss. Guard headroom (A3): in the D-8
  range N ≥ thr + 2ρ, every K ≤ thr + ρ satisfies K ≤ N − e_max (e_max ≤ ρ) —
  probe-PROVED, unit H7-B3. (SEP) lower bound τ(c) ≥ ρ(c) + 1: AUTOMATIC at order-0
  separations (distinct residues ⟹ ρ(c) = 0); at ρ(c) > 0 the site's NATURAL pin depth
  can undershoot ρ + 1 (wild multi-root-pair sites: ρ ~ Σ_pairs d_i d_j·H can exceed
  the read depth ~ H·e) — THEN route B fires:
* **IT-4 (route B: refine-and-aggregate — the (SEP)-deficiency repair).** Refine Σ_c by
  pinning factor digits to depth τ' := ρ(c) + 1: each sub-cell is a genuine adapted
  presentation (A1)–(A3); O-10 Theorem 2 gives the product law per sub-cell; per-factor
  keyed classes have EQUAL counts within each factor stratum (O-10 Corollary 1(c)
  mechanics: each depth-K_j class contains exactly p^{(N−K_j)d_j} members), so on each
  sub-cell the joint continuation-read word is EXACTLY UNIFORM on the product alphabet,
  with the SAME alphabet across sub-cells of one site; uniform-per-part with common
  alphabet aggregates to uniform-on-the-union (unit H7-C1a), and exact joint uniformity
  implies the (SIB) count identity for componentwise events (unit H7-C1b — the positive
  twin of `SibJcRouteA.sib_diag_break`). Hence (SIB) at the FULL stratum Σ_c even where
  the natural pin violates (SEP). STATUS: the two aggregation kernels are
  PROVABLE-NOW abstract counting lemmas (probe-typed); the refinement's sub-cell
  presentations re-consume IT-1/IT-2 at the deeper pin. LABEL: (c) claimed-new
  derivation (synthesized from M07 §2.3's uniformity-mixing diagnostic) — a designated
  Codex-review attack surface.

### 2.2 The construction-conformance target (which corpus carriers, what theorem)

Carriers REUSED (all in `lean/LeanUrat/Scaffold/ValueSide/KCount.lean`, rebuilt-probed):
`MulFiberData` (τ, ρ, τ_sep : ρ+1 ≤ τ, smithExp, chart), `SmithStable` (+ constructor
`smithStable_of_detDivisorRows`, gate `K9Gate.gate_smithStable`), `AdaptedCell`
(cellCount/factorCount/sM/domainCount_eq/fiber_nonempty), `sib_product_law` (himg-scoped),
`kcount_fiber_card` (hsol-scoped), and the (H7) receipt `EngineSIBRow p n N (KLoc ITau :
Prop) (stratumCount : ℕ)` — K11, authored with the pair as OPAQUE Prop parameters.

**The conformance theorem (H7-B1, probe-PROVED):** instantiating the opaque parameters
with the H7 row bodies (`ITau := ITauPresents s`, `KLoc := ` the K-LOC row) yields
`EngineSIBRow p n N KLoc (ITauPresents s) s.stratumCount` — i.e. the H7 rows ARE
sufficient for the exact receipt K10/Step-18-K1 consumes, with no re-key of K11
(honoring its design contract "BP_III's actual rows instantiate them with no re-key";
ownership note: BP_III.md never chartered the rows — this blueprint now does, under
`Scaffold/HDischarge/H7/`).

**FINDING H7-F1 (consumed-carrier defect — reported, NOT repaired here).**
`AdaptedCell.domainCount_eq : Nat.card Factor = ∏ j, factorCount j` runs its product
over `j : Factor` — the domain type ITSELF — so under the intended roster semantics
(factorCount = per-branch stratum counts) the field is uninstantiable at any genuine
site (F1 shape: `Nat.card Factor` must be 5⁸ = the domain count, while the per-branch
product must be indexed by `Fin 2`; no single `Factor` serves both). Consequently K10's
conclusion `… = ∏ j, A.factorCount j` carries per-branch (SIB) content only under
contrived `factorCount` choices (e.g. one designated element carrying the whole count).
H7's rows ROUTE AROUND it: `SiteDatum.branchCount : Fin m → ℕ` carries the
roster-indexed counts and `ITauPresents` demands the domain law
`Nat.card A.Factor = ∏ j, s.branchCount j` in roster indexing, leaving `factorCount`
unconsumed; the delivered product law (H7-B2, probe-PROVED) is
`stratumCount · p^{sM} = ∏_j branchCount j` — the honest Step-15 delivery shape.
DESIGNER-QUEUE flag to BP_IV (adjudication, not executed): re-index
`factorCount : J → ℕ` over a roster-type field, or document `Factor` as the domain and
retire `factorCount` from the (SIB) display.

### 2.3 Door summary for the pair

| member | door | provable-now slice | open remainder (named) |
|---|---|---|---|
| (K-LOC) | PROVE; KL-2 core = LITERATURE-RETARGET (GMN 2.26, §1.3 brief) | KL-1/KL-3 order ≤ 1; KL-2 assembly; KL-4 given those; H7-C2 count-face slice | order ≥ 2 legs (KL-1/KL-3); recentering absorption KL-3(c); §1.4 list |
| (I-τ) | CONSTRUCTION-CONFORMANCE (EngineSIBRow receipt) + PROVE (write-up) | H7-B1/B2/B3 (probe-proved); IT-3 order-0; IT-4 aggregation kernels (H7-C1a/b); order-0 gate H7-D1 | IT-2 ⊇ realizer direction; IT-1/IT-2 ⊆ at each order = K-LOC's grading; (SEP) at natural pins for wild sites (route B covers, at the cost of re-running IT-1/2 at depth ρ+1) |

Neither member is literature-axiom-eligible as a whole (M07 §3.4 stands: no published
statement is quantified over our tree/event vocabulary); only KL-2's core is citable.

---

## 3. LEAN UNIT SPECS (verbatim; every statement COMPILE-PROBED green 2026-08-05)

Target directory: `lean/LeanUrat/Scaffold/HDischarge/H7/`; namespace
`LeanUrat.Scaffold.HDischarge.H7`; import `LeanUrat.Scaffold.ValueSide.KCount` (which
carries `import Mathlib`). PROBE RECORD: all statements below compiled in one probe file
against the rebuilt KCount olean — zero errors; units marked **[probe-PROVED]** compiled
WITH the displayed proof; units marked **[probe-typed]** compiled with `sorry` (statement
well-formedness only — the sorry lives in the deleted probe, never in a landed file).
Landing discipline: prover fan-out units land sorry-free or not at all.

### 3.1 `H7/Rows.lean` — the row statements (unit H7-A; MECH)

```lean
namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

/-- H7-A1: the abstract realized-site datum the (H7) rows quantify over — the
integers the engine's ledger supplies for ONE realized site stratum. Engine-side
instantiation (from `MovesT.SiteLedger` at the pinned canonical models) is the
owner unit H7-W3a, NOT this wave; H7's theorems consume ONLY this record.
`branchCount` is ROSTER-indexed (`Fin m`), deliberately NOT `AdaptedCell.factorCount`
(FINDING H7-F1). -/
structure SiteDatum (p n N : ℕ) [Fact p.Prime] where
  m : ℕ
  two_le_m : 2 ≤ m
  thr : ℕ
  rho : ℕ
  stratumCount : ℕ
  branchCount : Fin m → ℕ

/-- The D-8 guard at the site. -/
def InGuard {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  s.thr + 2 * s.rho ≤ N

/-- H7-A2: the (I-τ) row body — the site stratum presents as an O-10 adapted cell:
an `AdaptedCell` with Smith stability whose fiber data carry the site's ρ at a pin
within the (I-τ) pricing (`τ ≤ thr + ρ`; `ρ + 1 ≤ τ` is the carrier's own `τ_sep`),
satisfying the K10b image law, with cell count = the stratum's box count and domain
count = the roster-indexed per-branch product. -/
def ITauPresents {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  ∃ A : AdaptedCell p n N,
    SmithStable A.toMulFiberData ∧
    A.toMulFiberData.ρ = s.rho ∧
    A.toMulFiberData.τ ≤ s.thr + s.rho ∧
    A.cellCount * p ^ A.sM = Nat.card A.Factor ∧
    A.cellCount = s.stratumCount ∧
    Nat.card A.Factor = ∏ j, s.branchCount j

/-- H7-A3: the K-LOC row, COUNT face — over an abstract carrier of continuation-event
families (joint + per-branch counts; the engine instantiates `Events` with its
prescribed-finite-subtree families, owner unit H7-W3b), every family satisfies the
(SIB) count identity at the stratum. The full read-semantics OL-3 statement is
§1.1 of the blueprint; this is its consumed integer shadow. -/
def KLocCounts {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (Events : Type) (joint : Events → ℕ) (single : Events → Fin s.m → ℕ) : Prop :=
  ∀ E : Events, joint E * s.stratumCount ^ (s.m - 1) = ∏ j, single E j
```

### 3.2 `H7/Receipt.lean` — conformance + delivery (units H7-B; all [probe-PROVED])

```lean
/-- H7-B1 [probe-PROVED]: THE CONFORMANCE THEOREM — the H7 rows instantiate K11's
`EngineSIBRow` opaque parameters with no re-key (K11's design contract). -/
theorem engineSIBRow_of_rows {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (KLoc : Prop) (hK : KLoc) (hI : ITauPresents s) :
    EngineSIBRow p n N KLoc (ITauPresents s) s.stratumCount := by
  obtain ⟨A, hS, -, -, himg, hcnt, -⟩ := id hI
  exact ⟨hK, hI, ⟨A, hS, himg, hcnt⟩⟩

/-- H7-B2 [probe-PROVED]: the Step-15 delivery shape — the stratum product law in
roster indexing (`stratumCount · p^{sM} = ∏_j branchCount j`), extracted from the
(I-τ) row; the honest replacement for K10's `factorCount` display (H7-F1). -/
theorem stratum_product_law {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hI : ITauPresents s) :
    ∃ sM : ℕ, s.stratumCount * p ^ sM = ∏ j, s.branchCount j := by
  obtain ⟨A, -, -, -, himg, hcnt, hdom⟩ := hI
  exact ⟨A.sM, by rw [← hcnt, himg, hdom]⟩

/-- H7-B3 [probe-PROVED]: IT-3 pricing arithmetic — in the D-8 guard range, any pin
`τ ≤ thr + ρ` and any read depth `K ≤ thr + ρ` clear the `e_max ≤ ρ` ceiling with
room (`τ + e_max ≤ N`, `K + e_max ≤ N`) — the (A3) headroom of O-10 §4.3(a). -/
theorem guard_read_headroom {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (hg : InGuard s) {τ K emax : ℕ}
    (hτ : τ ≤ s.thr + s.rho) (hK : K ≤ s.thr + s.rho) (he : emax ≤ s.rho) :
    τ + emax ≤ N ∧ K + emax ≤ N := by
  unfold InGuard at hg
  omega
```

### 3.3 `H7/Aggregate.lean` — the IT-4 route-B kernels (units H7-C1a/C1b; [probe-typed])

```lean
open Finset in
/-- H7-C1a [MED]: words uniform on each part of a partition (per-part multiplicity
may vary) are uniform on the union — the aggregation half of IT-4. Proof plan:
`U := Σ_{C ∈ P} u_C`; count each ω-fiber by partitioning X along `hcover`
(`Finset.card_biUnion` over pairwise-disjoint parts from the ∃!). -/
theorem uniform_on_union {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W]
    [DecidableEq W] (P : Finset (Finset X)) (w : X → W)
    (hcover : ∀ x : X, ∃! C, C ∈ P ∧ x ∈ C)
    (hunif : ∀ C ∈ P, ∃ u : ℕ, ∀ ω : W, (C.filter (fun x => w x = ω)).card = u) :
    ∃ U : ℕ, ∀ ω : W, (univ.filter (fun x : X => w x = ω)).card = U := by
  sorry -- prover wave; statement probe-typed

open Finset in
/-- H7-C1b [MED-HARD]: exactly-uniform joint words on a product alphabet satisfy the
(SIB) count identity for componentwise events — the positive twin of
`MovesU.SibRouteA.sib_diag_break`. Proof plan: both sides equal
`U^m · (∏_j #E_j) · (∏_j #A_j)^{m−1}` — LHS: the joint fiber count is
`U · ∏_j #E_j` and `#X = U · ∏_j #A_j`; RHS: per-branch counts are
`U · #E_j · ∏_{i≠j} #A_i`; `Finset.prod` bookkeeping. -/
theorem sib_of_uniform_words {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} {A : Fin m → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (w : X → ∀ j, A j) {U : ℕ}
    (hU : ∀ ω : ∀ j, A j, (univ.filter (fun x => w x = ω)).card = U)
    (E : ∀ j, Finset (A j)) :
    (univ.filter (fun x : X => ∀ j, w x j ∈ E j)).card
        * (Fintype.card X) ^ (m - 1)
      = ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card := by
  sorry -- prover wave; statement probe-typed
```

### 3.4 `H7/ResTrans.lean` — the KL-1 order-1 count-face slice (unit H7-C2; [probe-typed])

```lean
/-- H7-C2 [EASY-MED]: ω-blindness of coprime cofactors — multiplying by a ψ-coprime
cofactor changes no ψ-power divisibility read (ψ irreducible over a field). This is
KL-1's consumed face at order 1 (ω = ord_ψ R, GMN Lemma 2.17(2)): branch-j residual
reads cannot see a separated cofactor. Proof plan: ψ irreducible in F[X] ⟹ prime;
induct on k with `Prime.dvd_of_dvd_mul_right`/`mul_dvd_mul`. -/
theorem pow_dvd_mul_iff_of_coprime_cofactor {F : Type*} [Field F]
    {ψ g : Polynomial F} (hψ : Irreducible ψ) (hg : ¬ ψ ∣ g)
    (f : Polynomial F) (k : ℕ) :
    ψ ^ k ∣ f * g ↔ ψ ^ k ∣ f := by
  sorry -- prover wave; statement probe-typed
```

### 3.5 `H7/Order0Gate.lean` — the non-vacuity gate (units H7-D1a/b/c)

```lean
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- H7-D1a [MECH; probe-typed]: the F1-shaped order-0 site datum — p = 5, n = 4,
N = 8 boxes; two continuing branches (the sealed CASE_SIB roster), residue-split so
ρ = 0; stratum count 5⁸ (the 14-pin cell Σ*), per-branch strata 5⁴ each. Integers
from `verification/CASE_SIB_SEALED_PREDICTIONS.md` via the SibJcRouteA header. -/
noncomputable def f1Datum : SiteDatum 5 4 8 where
  m := 2
  two_le_m := by norm_num
  thr := 3
  rho := 0
  stratumCount := 5 ^ 8
  branchCount := ![5 ^ 4, 5 ^ 4]

/-- H7-D1b [MED]: THE GATE — `ITauPresents f1Datum` is inhabited: a compiled
non-vacuous adapted-cell presentation at the F1 integers (ρ = 0, τ = 1, sM = 0,
`SmithStable` with all exponents 0, image law 5⁸·5⁰ = 5⁸, domain law 5⁸ = 5⁴·5⁴).
Builder notes: `MulFiberData` synthetic fields at the base point (Fiber/SolutionSet
:= `Unit`-sized charts are NOT enough — the domain law needs `Nat.card A.Factor = 5⁸`:
take `Factor := Fin 2 → Fin 625`, `Nat.card_pi` + `norm_num`; `domainCount_eq` via a
designated-element `factorCount` (H7-F1 workaround) or `Finset.prod_eq_single`).
A FAILURE to build this gate is a stop-the-line interface finding, not a prover bug. -/
theorem gate_f1_iTau : ITauPresents f1Datum := by
  sorry -- prover wave; statement probe-typed

/-- H7-D1c [probe-PROVED]: the gate site is in the D-8 guard (3 + 0 ≤ 8). -/
theorem gate_f1_guard : InGuard f1Datum := by
  unfold InGuard f1Datum
  norm_num
```

### 3.6 `H7/AxChk.lean` — census (unit H7-E1; MECH)

`#print axioms` for `engineSIBRow_of_rows`, `stratum_product_law`,
`guard_read_headroom`, `uniform_on_union`, `sib_of_uniform_words`,
`pow_dvd_mul_iff_of_coprime_cofactor`, `gate_f1_iTau` — expected Lean core only;
zero `sorryAx` at wave close; regression = stop-the-line.

### 3.7 W3+ units — SPECIFIED, NOT SCHEDULED (owner ladders; statements owed to their waves)

* **H7-W3a (engine instantiation of `SiteDatum`)** [HARD; owner: MovesT/BP_III side]:
  a builder `MovesT.SiteLedger → SiteDatum p n N` at the pinned canonical models
  (stratumCount := `Nat.card (siteCellEvent …)`, branchCount from the roster's
  per-branch strata) + `KLocCounts` instantiated at the `ContFiber` event families.
  BLOCKED on: OL-2 (CellAssign/ledger inhabitation at the pinned instance — M07's
  standing prerequisite) and the item-27 statement-repair adjudication (PARKED; H7
  does not execute it). Compile-probing deferred to its own wave by design.
* **H7-W3b (KL-2/KL-3 general residual transport)** [HARD; owner: the (GR-B)/HC2
  apparatus]: the level-r translation + unit-scalar laws in the corpus's carry-algebra
  vocabulary; the `HK52_stretchGate` ν_{i+1}.e ruling gates the order ≥ 2 legs.
* **H7-W3c (IT-2 ⊇ realizer direction)** [HARD; owner: O-14a′ mechanism]: the
  product-of-strata → stratum run-reconstruction; consumes run-determinism + the
  RunRealizerExists machinery.

---

## 4. WAVE PLAN (prover fan-out; per-file `lake env lean` gates)

| wave | units | files | deps | difficulty | parallel? |
|---|---|---|---|---|---|
| W0 | H7-A1/A2/A3 (+ `InGuard`) | `Rows.lean` | KCount olean (REBUILT — see header; a stale olean hides `EngineSIBRow`) | MECH | single owner |
| W1a | H7-B1/B2/B3 | `Receipt.lean` | W0 | EASY (proofs displayed) | ∥ W1b/c/d |
| W1b | H7-C1a, H7-C1b | `Aggregate.lean` | Mathlib only | MED / MED-HARD | ∥ |
| W1c | H7-C2 | `ResTrans.lean` | Mathlib only | EASY-MED | ∥ |
| W1d | H7-D1a/b/c | `Order0Gate.lean` | W0 | MECH / MED / MECH | ∥ |
| W2 | H7-E1 | `AxChk.lean` | W1a–d | MECH | after all |
| W3+ | H7-W3a/b/c | (their own blueprints' waves) | §3.7 blockers | HARD | not scheduled here |

Wave-close criteria: zero `sorry` in landed files; AxChk census Lean-core; the W1d gate
inhabited (or its failure filed as a stop-the-line interface finding against §2.2).

## 5. NUMERICS / FALSIFIER GATES (flags, never substitutes)

* **Standing (already run):** `verification/o10_kcount_harness.py` 68 PASS / 0 FAIL
  (factor-coordinate side); `MovesU/SibJcRouteA.lean` (the compiled NEGATIVE gate:
  unadapted correlation cells break (SIB) by exactly p — what (I-τ)'s (A1) excludes).
* **N-H7-1 (NEW; charge for the numerics fleet):** `verification/openmath/h7_kloc_probe.py`
  — pure-Python exact integers; Hensel factor extraction (M07 Lemma A's constructive
  surjectivity) at (i) the F1 instance (p = 5, R₀ = (z−1)²(z−2)², the 5⁸-member Σ*) and
  (ii) a wild ρ > 0 pair from the O-10 battery ((x²+2)(x²+2x+2) at p = 2). Tests, sealed
  before first run: (a) K-JAC within-cell constancy (M07 test-4 shape); (b) THE K-LOC
  READ-CONFORMANCE TEST — depth-1/2 branch continuation digits on dec(x) equal the
  matching OM digits of the extracted factor after one cell-constant shift (per §1.1
  (i)/(ii)); (c) route-B mini — refine a synthetic (SEP)-deficient cell, verify the
  H7-C1a/b aggregation arithmetic. A (b) violation REFUTES the K-LOC statement as
  drafted (stop-the-line for §1.1, before any prover spend). cypari2 cross-check
  (factorpadic) optional, env-conditional — the O-10 session found it absent.

## 6. REUSE MAP + FENCES

REUSED (by import, never edited): `Scaffold.ValueSide.KCount` — `MulFiberData`,
`SmithStable` (+ `smithStable_of_detDivisorRows`, `K9Gate.gate_smithStable`),
`AdaptedCell`, `sib_product_law`, `kcount_fiber_card`, `card_domainProduct_finset`,
`EngineSIBRow` (K11) · `MovesU/SibJcRouteA.lean` (fence-side evidence; its
`JointlyUniform` is the H7-C1 vocabulary precedent) · GMN pins:
`docs/GMN_citations.md` §§5–6 (K-FACT set; Thm 2.26; Lemma 2.17; Def 1.8) ·
O-10 leaf theorems (math source of record; NOT re-proved) · HC2 `StageTransHyp`/D.10
(the K-LOC frame-convention carrier, W3b) · `MovesT.SiteLedger`/`ContFiber` (W3a
instantiation targets — read-only here).

NOT TOUCHED (fences): `MovesT.SibJcRows`/`CellData` + every parked item 22–29 (esp.
item 27, the SibJcRows statement repair — M07 R1–R3 menu stays designer-queue);
`montes_uniform_n2` / `montes_unconditional` / all capstones; no new axioms; no
statement weakened. FINDING H7-F1 is REPORTED to BP_IV's designer queue, not executed.

## 7. DISPOSITION LOG

* 2026-08-05: blueprint drafted; all §3 statements compile-probed green (probe file
  deleted); KCount olean rebuilt (stale-olean finding recorded in header); Codex
  adversarial review launched — fold table appended below on return.
